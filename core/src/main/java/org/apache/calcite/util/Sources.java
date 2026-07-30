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

import com.google.common.io.CharSource;

import org.checkerframework.checker.nullness.qual.Nullable;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.net.InetAddress;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.net.UnknownHostException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;
import java.util.zip.GZIPInputStream;

import static java.util.Objects.requireNonNull;

/**
 * Utilities for {@link Source}.
 */
public abstract class Sources {
  private Sources() {}

  public static Source of(File file) {
    return new FileSource(file);
  }

  public static Source of(URL url) {
    return new FileSource(url);
  }


  public static Source file(@Nullable File baseDirectory, String fileName) {
    final File file = new File(fileName);
    if (baseDirectory != null && !file.isAbsolute()) {
      return of(new File(baseDirectory, fileName));
    } else {
      return of(file);
    }
  }

  /** Creates a {@link Source} from a character sequence such as a
   * {@link String}. */
  public static Source of(CharSequence s) {
    return fromCharSource(CharSource.wrap(s));
  }

  /** Creates a {@link Source} from a generic text source such as string,
   * {@link java.nio.CharBuffer} or text file. Useful when data is already
   * in memory or can't be directly read from
   * a file or url.
   *
   * @param source generic "re-readable" source of characters
   * @return {@code Source} delegate for {@code CharSource} (can't be null)
   * @throws NullPointerException when {@code source} is null
   */
  public static Source fromCharSource(CharSource source) {
    return new GuavaCharSource(source);
  }

  public static Source url(String url) {
    try {
      return of(URI.create(url).toURL());
    } catch (MalformedURLException | IllegalArgumentException e) {
      throw new RuntimeException("Malformed URL: '" + url + "'", e);
    }
  }

  /**
   * Rejects a URL whose scheme is not in {@code allowedSchemes}. When
   * {@code allowedSchemes} is empty this method is a no-op (permissive
   * fallback). Scheme comparison is case-insensitive.
   *
   * <p>This helper enforces the P3 (no-SSRF) boundary of the Calcite security
   * threat model for adapters that resolve attacker-influenced URLs:
   * any URL-fetching schema operand must resolve to a scheme the
   * operator has chosen to permit.
   *
   * @throws SecurityException if the URL's scheme is not allowed, or
   *   the URL is malformed.
   */
  public static void checkAllowedScheme(String url, Set<String> allowedSchemes) {
    if (allowedSchemes.isEmpty()) {
      return;
    }
    final URI uri;
    try {
      uri = new URI(url);
    } catch (URISyntaxException e) {
      throw new SecurityException("Malformed URL: '" + url + "'", e);
    }
    final String scheme = uri.getScheme();
    if (scheme == null
        || !allowedSchemes.contains(scheme.toLowerCase(Locale.ROOT))) {
      throw new SecurityException("URL scheme '" + scheme
          + "' is not in the configured allowlist " + allowedSchemes);
    }
  }

  /**
   * Parses a comma-separated allowlist of URL schemes into a lowercased
   * set. Empty entries and whitespace are stripped.
   */
  public static Set<String> parseAllowedUrlSchemes(String raw) {
    if (raw == null || raw.isEmpty()) {
      return Collections.emptySet();
    }
    final Set<String> out = new LinkedHashSet<>();
    for (String s : raw.split(",")) {
      final String trimmed = s.trim().toLowerCase(Locale.ROOT);
      if (!trimmed.isEmpty()) {
        out.add(trimmed);
      }
    }
    return out;
  }

  /**
   * Rejects a URL whose host resolves to a loopback, link-local,
   * private (RFC-1918), CGNAT (RFC 6598), IPv6 unique-local (RFC 4193),
   * "current network" ({@code 0.0.0.0/8}), or well-known cloud metadata
   * endpoint. No-op for non-network schemes (anything other than
   * {@code http}, {@code https}, {@code ftp}).
   *
   * <p>Covers, beyond {@link InetAddress#isLoopbackAddress()} /
   * {@link InetAddress#isLinkLocalAddress()} /
   * {@link InetAddress#isSiteLocalAddress()} /
   * {@link InetAddress#isAnyLocalAddress()}:
   *
   * <ul>
   *   <li>{@code 169.254.169.254} &mdash; the AWS/GCP/Azure/OCI IPv4
   *       metadata endpoint (link-local, but checked explicitly so
   *       the error message is unambiguous);</li>
   *   <li>{@code 100.64.0.0/10} &mdash; RFC 6598 CGNAT space, which
   *       includes Alibaba Cloud's metadata endpoint
   *       {@code 100.100.100.200} and many Kubernetes pod networks
   *       and which is <em>not</em> covered by
   *       {@code isSiteLocalAddress()};</li>
   *   <li>{@code 0.0.0.0/8} &mdash; RFC 1122 "this network";
   *       {@code isAnyLocalAddress()} matches only the exact address
   *       {@code 0.0.0.0}, not the whole block;</li>
   *   <li>{@code fc00::/7} &mdash; the entire IPv6 Unique Local
   *       Address range (RFC 4193), which contains AWS's IPv6 IMDS
   *       ({@code fd00:ec2::254}) and any operator's ULA metadata
   *       scheme. {@code isSiteLocalAddress()} on IPv6 covers only
   *       the deprecated {@code fec0::/10}.</li>
   * </ul>
   *
   * <p>IPv4-mapped and IPv4-compatible IPv6 addresses are unwrapped
   * before classification: {@code ::ffff:169.254.169.254} and
   * {@code ::169.254.169.254} are treated as their IPv4 counterparts,
   * because the wrapping form's {@code Inet6Address.is*Address()}
   * methods inspect the top nibble ({@code 0xfe80} link-local,
   * {@code 0xfc/7} ULA) and do not look at the mapped payload.
   *
   * <p>Best-effort against DNS-time attacker control: a DNS-rebinding
   * adversary can still switch the resolved address between check-time
   * and connect-time. Full defense requires bind-time IP pinning
   * inside the URL-opening path.
   *
   * @throws SecurityException if the URL targets a blocked host.
   */
  public static void checkNotPrivateNetwork(String url) {
    final URI uri;
    try {
      uri = new URI(url);
    } catch (URISyntaxException e) {
      throw new SecurityException("Malformed URL: '" + url + "'", e);
    }
    final String scheme = uri.getScheme();
    if (scheme == null) {
      return;
    }
    final String s = scheme.toLowerCase(Locale.ROOT);
    if (!s.equals("http") && !s.equals("https") && !s.equals("ftp")) {
      return;
    }
    final String host = uri.getHost();
    if (host == null || host.isEmpty()) {
      throw new SecurityException("URL '" + url + "' has no valid host");
    }
    final InetAddress[] addrs;
    try {
      addrs = InetAddress.getAllByName(host);
    } catch (UnknownHostException e) {
      throw new SecurityException("Cannot resolve host '" + host + "'", e);
    }
    for (InetAddress a : addrs) {
      // Unwrap IPv4-mapped / IPv4-compatible IPv6 (e.g.
      // ::ffff:169.254.169.254 or ::169.254.169.254 -> 169.254.169.254)
      // so IPv4 range checks below see the real payload.
      final InetAddress target = unwrapIpv4InIpv6(a);
      if (target.isLoopbackAddress()
          || target.isLinkLocalAddress()
          || target.isSiteLocalAddress()
          || target.isAnyLocalAddress()
          || isReservedOrCloudMetadataIp(target)
          || isIpv6UniqueLocal(target)) {
        throw new SecurityException("URL '" + url
            + "' resolves to a blocked network address: " + a.getHostAddress());
      }
    }
  }

  /** Unwraps an IPv4-mapped ({@code ::ffff:a.b.c.d}) or IPv4-compatible
   * ({@code ::a.b.c.d}) IPv6 address to its IPv4 counterpart. Leaves
   * genuine IPv6 addresses untouched. */
  private static InetAddress unwrapIpv4InIpv6(InetAddress addr) {
    final byte[] bytes = addr.getAddress();
    if (bytes.length != 16) {
      return addr;
    }
    // First 10 bytes must be zero for both mapped and compatible forms.
    for (int i = 0; i < 10; i++) {
      if (bytes[i] != 0) {
        return addr;
      }
    }
    final int b10 = bytes[10] & 0xff;
    final int b11 = bytes[11] & 0xff;
    // IPv4-mapped: bytes 10..11 are 0xff,0xff.
    // IPv4-compatible: bytes 10..11 are 0,0 (deprecated but still parseable).
    // The all-zero compatible form must have a nonzero payload; ::0.0.0.0
    // is the unspecified address and is handled by isAnyLocalAddress().
    final boolean mapped = b10 == 0xff && b11 == 0xff;
    final boolean compatible = b10 == 0 && b11 == 0
        && (bytes[12] != 0 || bytes[13] != 0
            || bytes[14] != 0 || bytes[15] != 0);
    if (mapped || compatible) {
      try {
        return InetAddress.getByAddress(Arrays.copyOfRange(bytes, 12, 16));
      } catch (UnknownHostException ignored) {
        // Fall through and use the original address.
      }
    }
    return addr;
  }

  private static boolean isReservedOrCloudMetadataIp(InetAddress a) {
    final byte[] b = a.getAddress();
    if (b.length != 4) {
      return false;
    }
    final int b0 = b[0] & 0xff;
    final int b1 = b[1] & 0xff;
    final int b2 = b[2] & 0xff;
    final int b3 = b[3] & 0xff;

    // 169.254.169.254 - AWS/GCP/Azure/OCI IPv4 metadata endpoint.
    if (b0 == 169 && b1 == 254 && b2 == 169 && b3 == 254) {
      return true;
    }
    // 100.64.0.0/10 - RFC 6598 CGNAT space; includes Alibaba Cloud's
    // metadata endpoint 100.100.100.200 and many K8s pod networks.
    if (b0 == 100 && (b1 & 0xc0) == 64) {
      return true;
    }
    // 0.0.0.0/8 - RFC 1122 "current network". isAnyLocalAddress()
    // covers only the exact address 0.0.0.0.
    if (b0 == 0) {
      return true;
    }
    return false;
  }

  /** True if {@code a} is an IPv6 Unique Local Address (RFC 4193,
   * {@code fc00::/7}). Java's {@code isSiteLocalAddress()} on IPv6
   * covers only the deprecated {@code fec0::/10}, so ULAs -- which
   * are where every documented IPv6 cloud metadata endpoint lives --
   * are otherwise unclassified. */
  private static boolean isIpv6UniqueLocal(InetAddress a) {
    final byte[] b = a.getAddress();
    // Top 7 bits are 1111110 (i.e. first byte is 0xfc or 0xfd).
    return b.length == 16 && (b[0] & 0xfe) == 0xfc;
  }

  /** Looks for a suffix on a path and returns
   * either the path with the suffix removed
   * or null. */
  private static @Nullable String trimOrNull(String s, String suffix) {
    return s.endsWith(suffix)
        ? s.substring(0, s.length() - suffix.length())
        : null;
  }

  private static boolean isFile(Source source) {
    return source.protocol().equals("file");
  }

  /** Adapter for {@link CharSource}. */
  private static class GuavaCharSource implements Source {
    private final CharSource charSource;

    private GuavaCharSource(CharSource charSource) {
      this.charSource = requireNonNull(charSource, "charSource");
    }

    private UnsupportedOperationException unsupported() {
      return new UnsupportedOperationException(
          String.format(Locale.ROOT, "Invalid operation for '%s' protocol", protocol()));
    }

    @Override public URL url() {
      throw unsupported();
    }

    @Override public File file() {
      throw unsupported();
    }

    @Override public Optional<File> fileOpt() {
      return Optional.empty();
    }

    @Override public String path() {
      throw unsupported();
    }

    @Override public Reader reader() throws IOException {
      return charSource.openStream();
    }

    @Override public InputStream openStream() throws IOException {
      return charSource.asByteSource(StandardCharsets.UTF_8).openStream();
    }

    @Override public String protocol() {
      return "memory";
    }

    @Override public Source trim(final String suffix) {
      throw unsupported();
    }

    @Override public @Nullable Source trimOrNull(final String suffix) {
      throw unsupported();
    }

    @Override public Source append(final Source child) {
      throw unsupported();
    }

    @Override public Source relative(final Source source) {
      throw unsupported();
    }

    @Override public String toString() {
      return getClass().getSimpleName() + "{" + protocol() + "}";
    }
  }

  /** Implementation of {@link Source} on the top of a {@link File} or
   * {@link URL}. */
  private static class FileSource implements Source {
    private final @Nullable File file;
    private final URL url;

    /**
     * A flag indicating if the url is deduced from the file object.
     */
    private final boolean urlGenerated;

    private FileSource(URL url) {
      this.url = requireNonNull(url, "url");
      this.file = urlToFile(url);
      this.urlGenerated = false;
    }

    private FileSource(File file) {
      this.file = requireNonNull(file, "file");
      this.url = fileToUrl(file);
      this.urlGenerated = true;
    }

    private File fileNonNull() {
      return requireNonNull(file, "file");
    }

    private static @Nullable File urlToFile(URL url) {
      if (!"file".equals(url.getProtocol())) {
        return null;
      }
      URI uri;
      try {
        uri = url.toURI();
      } catch (URISyntaxException e) {
        throw new IllegalArgumentException("Unable to convert URL " + url + " to URI", e);
      }
      if (uri.isOpaque()) {
        // It is like file:test%20file.c++
        // getSchemeSpecificPart would return "test file.c++"
        return new File(uri.getSchemeSpecificPart());
      }
      // See https://stackoverflow.com/a/17870390/1261287
      return Paths.get(uri).toFile();
    }

    private static URL fileToUrl(File file) {
      String filePath = file.getPath();
      if (!file.isAbsolute()) {
        // convert relative file paths
        filePath = filePath.replace(File.separatorChar, '/');
        if (file.isDirectory() && !filePath.endsWith("/")) {
          filePath += "/";
        }
        try {
          // We need to encode path. For instance, " " should become "%20"
          // That is why java.net.URLEncoder.encode(java.lang.String, java.lang.String) is not
          // suitable because it replaces " " with "+".
          String encodedPath = new URI(null, null, filePath, null).getRawPath();
          return URI.create("file:" + encodedPath).toURL();
        } catch (MalformedURLException | URISyntaxException e) {
          throw new IllegalArgumentException("Unable to create URL for file " + filePath, e);
        }
      }

      URI uri = null;
      try {
        // convert absolute file paths
        uri = file.toURI();
        return uri.toURL();
      } catch (SecurityException e) {
        throw new IllegalArgumentException("No access to the underlying file " + filePath, e);
      } catch (MalformedURLException e) {
        throw new IllegalArgumentException("Unable to convert URI " + uri + " to URL", e);
      }
    }

    @Override public String toString() {
      return (urlGenerated ? fileNonNull() : url).toString();
    }

    @Override public URL url() {
      return url;
    }

    @Override public File file() {
      if (file == null) {
        throw new UnsupportedOperationException();
      }
      return file;
    }

    @Override public Optional<File> fileOpt() {
      return Optional.ofNullable(file);
    }

    @Override public String protocol() {
      return file != null ? "file" : url.getProtocol();
    }

    @Override public String path() {
      if (file != null) {
        return file.getPath();
      }
      try {
        // Decode %20 and friends
        return url.toURI().getSchemeSpecificPart();
      } catch (URISyntaxException e) {
        throw new IllegalArgumentException("Unable to convert URL " + url + " to URI", e);
      }
    }

    @Override public Reader reader() throws IOException {
      final InputStream is;
      if (path().endsWith(".gz")) {
        final InputStream fis = openStream();
        is = new GZIPInputStream(fis);
      } else {
        is = openStream();
      }
      return new InputStreamReader(is, StandardCharsets.UTF_8);
    }

    @Override public InputStream openStream() throws IOException {
      if (file != null) {
        return Files.newInputStream(file.toPath());
      } else {
        return url.openStream();
      }
    }

    @Override public Source trim(String suffix) {
      Source x = trimOrNull(suffix);
      return x == null ? this : x;
    }

    @Override public @Nullable Source trimOrNull(String suffix) {
      if (!urlGenerated) {
        final String s = Sources.trimOrNull(url.toExternalForm(), suffix);
        return s == null ? null : Sources.url(s);
      } else {
        final String s = Sources.trimOrNull(fileNonNull().getPath(), suffix);
        return s == null ? null : of(new File(s));
      }
    }

    @Override public Source append(Source child) {
      if (isFile(child)) {
        if (child.file().isAbsolute()) {
          return child;
        }
      } else {
        try {
          URI uri = child.url().toURI();
          if (!uri.isOpaque()) {
            // The URL is "absolute" (it starts with a slash)
            return child;
          }
        } catch (URISyntaxException e) {
          throw new IllegalArgumentException("Unable to convert URL " + child.url() + " to URI", e);
        }
      }
      String path = child.path();
      if (!urlGenerated) {
        String encodedPath = new File(".").toURI().relativize(new File(path).toURI())
            .getRawSchemeSpecificPart();
        return Sources.url(url + "/" + encodedPath);
      } else {
        return Sources.file(file, path);
      }
    }

    @Override public Source relative(Source parent) {
      if (isFile(parent)) {
        if (isFile(this)
            && fileNonNull().getPath().startsWith(parent.file().getPath())) {
          String rest =
              fileNonNull().getPath().substring(parent.file().getPath().length());
          if (rest.startsWith(File.separator)) {
            return Sources.file(null, rest.substring(File.separator.length()));
          }
        }
        return this;
      } else {
        if (!isFile(this)) {
          String rest =
              Sources.trimOrNull(url.toExternalForm(),
                  parent.url().toExternalForm());
          if (rest != null
              && rest.startsWith("/")) {
            return Sources.file(null, rest.substring(1));
          }
        }
        return this;
      }
    }
  }
}
