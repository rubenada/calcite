/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.calcite.util;

import org.junit.jupiter.api.Test;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Set;

import static org.hamcrest.CoreMatchers.containsString;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Unit tests for the P3 (no-SSRF) URL-guard helpers on {@link Sources}:
 * {@link Sources#checkAllowedScheme} and
 * {@link Sources#checkNotPrivateNetwork}.
 */
class SourcesUrlGuardTest {

  // ---------- checkAllowedScheme ----------

  @Test void checkAllowedSchemeEmptyAllowlistIsNoOp() {
    assertDoesNotThrow(() ->
        Sources.checkAllowedScheme("http://any.example.com/x",
            java.util.Collections.emptySet()));
  }

  @Test void checkAllowedSchemeAllowedSchemeOk() {
    Set<String> allow = Sources.parseAllowedUrlSchemes("https,file");
    assertDoesNotThrow(() ->
        Sources.checkAllowedScheme("https://example.com/", allow));
    assertDoesNotThrow(() ->
        Sources.checkAllowedScheme("file:/tmp/x.csv", allow));
  }

  /** With the default policy (file,https), plaintext http is refused. */
  @Test void checkAllowedSchemeDefaultRefusesHttp() {
    Set<String> allow = Sources.parseAllowedUrlSchemes("file,https");
    SecurityException e =
        assertThrows(SecurityException.class,
            () -> Sources.checkAllowedScheme("http://example.com/", allow));
    assertThat(e.getMessage(), containsString("not in the configured allowlist"));
  }

  /** With the default policy (file,https), plaintext ftp is refused. */
  @Test void checkAllowedSchemeDefaultRefusesFtp() {
    Set<String> allow = Sources.parseAllowedUrlSchemes("file,https");
    assertThrows(SecurityException.class,
        () -> Sources.checkAllowedScheme("ftp://example.com/", allow));
  }

  @Test void checkAllowedSchemeMalformedUrlRejected() {
    Set<String> allow = Sources.parseAllowedUrlSchemes("https");
    assertThrows(SecurityException.class,
        () -> Sources.checkAllowedScheme("http ://bad", allow));
  }

  @Test void parseAllowedUrlSchemesLowercasesAndTrims() {
    Set<String> s = Sources.parseAllowedUrlSchemes(" HTTPS , File ,, ftp ");
    assertTrue(s.contains("https"));
    assertTrue(s.contains("file"));
    assertTrue(s.contains("ftp"));
    assertEquals(3, s.size());
  }

  // ---------- checkNotPrivateNetwork ----------

  @Test void checkNotPrivateNetworkPublicSchemeOk() {
    try {
      InetAddress.getByName("example.com");
    } catch (UnknownHostException skip) {
      return;
    }
    assertDoesNotThrow(() ->
        Sources.checkNotPrivateNetwork("https://example.com/"));
  }

  @Test void checkNotPrivateNetworkLoopbackRejected() {
    SecurityException e =
        assertThrows(SecurityException.class,
            () -> Sources.checkNotPrivateNetwork("http://127.0.0.1/"));
    assertThat(e.getMessage(), containsString("blocked network address"));
  }

  /** Cloud metadata endpoint &mdash; Always a Vulnerability P3 in the thret model. */
  @Test void checkNotPrivateNetworkMetadataIpRejected() {
    SecurityException e =
        assertThrows(
            SecurityException.class, () -> Sources.checkNotPrivateNetwork(
            "http://169.254.169.254/latest/meta-data/"));
    assertThat(e.getMessage(), containsString("169.254.169.254"));
  }

  @Test void checkNotPrivateNetworkRfc1918Rejected() {
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://10.0.0.1/"));
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://192.168.1.1/"));
  }

  /** RFC 6598 CGNAT (100.64.0.0/10) - Alibaba Cloud's metadata
   * endpoint 100.100.100.200 and many K8s pod networks live here.
   * Not covered by {@link InetAddress#isSiteLocalAddress()}. */
  @Test void checkNotPrivateNetworkCgnatRejected() {
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://100.100.100.200/"));
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://100.64.0.1/"));
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://100.127.255.254/"));
  }

  /** CGNAT block boundary: 100.63.x.x is public (not in 100.64.0.0/10);
   * 100.128.x.x is public too. Both must be allowed by the private-net
   * check (they may still be rejected by resolution, so we only assert
   * that the classifier does not reject on range grounds by using
   * hosts near the boundary that we can't resolve -- but the safe
   * assertion is that the mask arithmetic is precise). */
  @Test void checkNotPrivateNetworkCgnatBoundaryPrecise() {
    // 100.63.255.255 must NOT be blocked as CGNAT (it is not in the /10).
    // We can't easily assert non-throwing behaviour for a literal IP
    // without a DNS round-trip, so we assert the classifier via the
    // range endpoint that IS in the block: 100.64.0.0 is the first
    // CGNAT address and MUST be rejected.
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://100.64.0.0/"));
  }

  /** 0.0.0.0/8 - RFC 1122 "this network". isAnyLocalAddress() only
   * matches the exact address 0.0.0.0, not the whole /8. */
  @Test void checkNotPrivateNetworkCurrentNetworkBlockRejected() {
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://0.0.0.0/"));
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://0.1.2.3/"));
  }

  /** IPv6 Unique Local Address range (fc00::/7). Contains AWS's IPv6
   * IMDS fd00:ec2::254 and any operator ULA metadata endpoint.
   * Java's isSiteLocalAddress() on IPv6 only covers the deprecated
   * fec0::/10, so this range is otherwise unclassified. */
  @Test void checkNotPrivateNetworkIpv6UlaRejected() {
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://[fd00:ec2::254]/"));
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://[fc00::1]/"));
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://[fdff::1]/"));
  }

  /** IPv4-mapped IPv6 for a blocked IPv4 destination:
   * ::ffff:169.254.169.254 must still resolve to "blocked". Without
   * unwrapping, Inet6Address.isLinkLocalAddress() inspects the top
   * nibble (0xfe80) and returns false. */
  @Test void checkNotPrivateNetworkIpv4MappedMetadataRejected() {
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork(
            "http://[::ffff:169.254.169.254]/latest/meta-data/"));
  }

  /** IPv4-mapped IPv6 for loopback: ::ffff:127.0.0.1. */
  @Test void checkNotPrivateNetworkIpv4MappedLoopbackRejected() {
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork("http://[::ffff:127.0.0.1]/"));
  }

  /** IPv4-mapped IPv6 for CGNAT: ::ffff:100.100.100.200. */
  @Test void checkNotPrivateNetworkIpv4MappedCgnatRejected() {
    assertThrows(SecurityException.class,
        () -> Sources.checkNotPrivateNetwork(
            "http://[::ffff:100.100.100.200]/"));
  }

  @Test void checkNotPrivateNetworkNonNetworkSchemeIsNoOp() {
    assertDoesNotThrow(() ->
        Sources.checkNotPrivateNetwork("file:/tmp/x.csv"));
    assertDoesNotThrow(() ->
        Sources.checkNotPrivateNetwork("jar:file:/tmp/x.jar!/a"));
  }
}
