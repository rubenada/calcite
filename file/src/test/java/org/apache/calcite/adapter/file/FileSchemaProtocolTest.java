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
package org.apache.calcite.adapter.file;

import org.apache.calcite.schema.Table;
import org.apache.calcite.util.Sources;

import com.google.common.collect.ImmutableList;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static org.hamcrest.CoreMatchers.containsString;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Tests that {@link FileSchema} dereferences only {@code file} sources by
 * default, and requires an explicit operator opt-in (the
 * {@code calcite.file.remote.protocols.allowed} system property) for remote
 * URL table operands, which would otherwise let a model author direct the
 * host to fetch arbitrary URLs (SSRF, cf. CVE-2020-13955).
 */
class FileSchemaProtocolTest {

  private static Map<String, Object> table(String name, String url) {
    final Map<String, Object> tableDef = new HashMap<>();
    tableDef.put("name", name);
    tableDef.put("url", url);
    return tableDef;
  }

  @Test void testRemoteUrlRejectedByDefault() {
    final FileSchema schema =
        new FileSchema(null, "S", null,
            ImmutableList.of(table("T", "http://localhost/table.csv")));
    IllegalArgumentException e =
        assertThrows(IllegalArgumentException.class, schema::getTableMap);
    assertThat(e.getMessage(),
        containsString("Remote URL protocol 'http' is not allowed"));
    assertThat(e.getMessage(),
        containsString("calcite.file.remote.protocols.allowed"));
  }

  @Test void testFtpUrlRejectedByDefault() {
    final FileSchema schema =
        new FileSchema(null, "S", null,
            ImmutableList.of(table("T", "ftp://localhost/table.csv")));
    assertThrows(IllegalArgumentException.class, schema::getTableMap);
  }

  @Test void testFileUrlAllowedByDefault() {
    final FileSchema schema =
        new FileSchema(null, "S", null,
            ImmutableList.of(table("T", "file:foo.csv")));
    final Map<String, Table> tableMap = schema.getTableMap();
    assertThat(tableMap.containsKey("T"), is(true));
  }

  /** Exercises the check with an explicit allowlist rather than by mutating a
   * JVM-wide system property; {@link
   * org.apache.calcite.config.CalciteSystemProperty} caches at class-load, so
   * mid-run {@code System.setProperty} would not be observed by the read
   * inside {@link FileSchema#checkSourceProtocolAllowed(org.apache.calcite.util.Source)}. */
  @Test void testRemoteUrlAllowedWhenOptedIn() {
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("http://localhost/table.csv"), "http, https"));
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("https://localhost/table.csv"), "http, https"));
  }

  @Test void testExplicitAllowlistStillRejectsUnlisted() {
    IllegalArgumentException e =
        assertThrows(IllegalArgumentException.class, () ->
            FileSchema.checkSourceProtocolAllowed(
                Sources.url("ftp://localhost/table.csv"), "http, https"));
    assertThat(e.getMessage(),
        containsString("Remote URL protocol 'ftp' is not allowed"));
  }

  @Test void testHostAllowlistPermitsListedHost() {
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("https://data.example.com/table.csv"),
            "http, https", "data.example.com, ftp.example.com"));
  }

  @Test void testHostAllowlistRejectsUnlistedHost() {
    IllegalArgumentException e =
        assertThrows(IllegalArgumentException.class, () ->
            FileSchema.checkSourceProtocolAllowed(
                Sources.url("https://bad.example.com/table.csv"),
                "http, https", "data.example.com"));
    assertThat(e.getMessage(),
        containsString("Remote URL host 'bad.example.com' is not on"));
    assertThat(e.getMessage(),
        containsString("calcite.file.remote.hosts.allowed"));
  }

  @Test void testHostAllowlistIsCaseInsensitive() {
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("https://DATA.Example.COM/table.csv"),
            "https", "data.example.com"));
  }

  @Test void testHostAllowlistExactMatchOnly() {
    // A suffix must not slip through: "example.com" does not admit
    // "bad-example.com".
    IllegalArgumentException e =
        assertThrows(IllegalArgumentException.class, () ->
            FileSchema.checkSourceProtocolAllowed(
                Sources.url("https://bad-example.com/table.csv"),
                "https", "example.com"));
    assertThat(e.getMessage(),
        containsString("Remote URL host 'bad-example.com' is not on"));
  }

  @Test void testHostAllowlistIgnoredWhenEmpty() {
    // Empty host allowlist means "any host allowed".
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("https://whatever.example.com/table.csv"),
            "https", ""));
  }
}
