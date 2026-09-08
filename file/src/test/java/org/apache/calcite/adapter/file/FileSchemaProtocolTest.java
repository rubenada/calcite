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

import org.apache.calcite.config.CalciteSystemProperty;
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
 * Tests the operator-level controls over which table {@code url} operands
 * {@link FileSchema} will dereference: the
 * {@code calcite.file.remote.protocols.allowed} and
 * {@code calcite.file.remote.hosts.allowed} system properties.
 */
class FileSchemaProtocolTest {

  private static Map<String, Object> table(String name, String url) {
    final Map<String, Object> tableDef = new HashMap<>();
    tableDef.put("name", name);
    tableDef.put("url", url);
    return tableDef;
  }

  @Test void testDefaultsAreWildcards() {
    assertThat(CalciteSystemProperty.FILE_REMOTE_PROTOCOLS_ALLOWED.value(), is("*"));
    assertThat(CalciteSystemProperty.FILE_REMOTE_HOSTS_ALLOWED.value(), is("*"));
  }

  @Test void testRemoteUrlAcceptedByDefault() {
    final FileSchema schema =
        new FileSchema(null, "S", null,
            ImmutableList.of(table("T", "http://localhost/table.csv")));
    final Map<String, Table> tableMap = schema.getTableMap();
    assertThat(tableMap.containsKey("T"), is(true));
  }

  @Test void testFileUrlAccepted() {
    final FileSchema schema =
        new FileSchema(null, "S", null,
            ImmutableList.of(table("T", "file:foo.csv")));
    final Map<String, Table> tableMap = schema.getTableMap();
    assertThat(tableMap.containsKey("T"), is(true));
  }

  @Test void testWildcardAdmitsAnyProtocol() {
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("ftp://localhost/table.csv"), "*", "*"));
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("jar:http://localhost/x.jar!/table.csv"), "*", "*"));
  }

  /** The off-switch: an empty protocol list leaves only {@code file:}. */
  @Test void testEmptyProtocolListRejectsEveryRemoteProtocol() {
    for (String url : new String[] {
        "http://localhost/table.csv",
        "https://localhost/table.csv",
        "ftp://localhost/table.csv",
        "jar:http://localhost/x.jar!/table.csv"}) {
      final IllegalArgumentException e =
          assertThrows(IllegalArgumentException.class, () ->
              FileSchema.checkSourceProtocolAllowed(Sources.url(url), "", "*"));
      assertThat(e.getMessage(), containsString("is not allowed"));
      assertThat(e.getMessage(),
          containsString("calcite.file.remote.protocols.allowed"));
    }
    // ... while a file: source is still dereferenced.
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("file:foo.csv"), "", ""));
  }

  @Test void testNarrowedProtocolListAdmitsOnlyListed() {
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("http://localhost/table.csv"), "http, https", "*"));
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("https://localhost/table.csv"), "http, https", "*"));
    final IllegalArgumentException e =
        assertThrows(IllegalArgumentException.class, () ->
            FileSchema.checkSourceProtocolAllowed(
                Sources.url("ftp://localhost/table.csv"), "http, https", "*"));
    assertThat(e.getMessage(),
        containsString("Remote URL protocol 'ftp' is not allowed"));
  }

  @Test void testHostListPermitsListedHost() {
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("https://data.example.com/table.csv"),
            "http, https", "data.example.com, ftp.example.com"));
  }

  @Test void testHostListRejectsUnlistedHost() {
    final IllegalArgumentException e =
        assertThrows(IllegalArgumentException.class, () ->
            FileSchema.checkSourceProtocolAllowed(
                Sources.url("https://bad.example.com/table.csv"),
                "http, https", "data.example.com"));
    assertThat(e.getMessage(),
        containsString("Remote URL host 'bad.example.com' is not allowed"));
    assertThat(e.getMessage(),
        containsString("calcite.file.remote.hosts.allowed"));
  }

  @Test void testHostListIsCaseInsensitive() {
    assertDoesNotThrow(() ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("https://DATA.Example.COM/table.csv"),
            "https", "data.example.com"));
  }

  @Test void testHostListExactMatchOnly() {
    // A suffix must not slip through: "example.com" does not admit "bad-example.com"
    final IllegalArgumentException e =
        assertThrows(IllegalArgumentException.class, () ->
            FileSchema.checkSourceProtocolAllowed(
                Sources.url("https://bad-example.com/table.csv"),
                "https", "example.com"));
    assertThat(e.getMessage(),
        containsString("Remote URL host 'bad-example.com' is not allowed"));
  }

  /** An empty host list is the off-switch too: it admits no host, so an
   * allowed protocol on its own reaches nothing. */
  @Test void testEmptyHostListRejectsEveryHost() {
    final IllegalArgumentException e =
        assertThrows(IllegalArgumentException.class, () ->
            FileSchema.checkSourceProtocolAllowed(
                Sources.url("https://data.example.com/table.csv"), "*", ""));
    assertThat(e.getMessage(),
        containsString("calcite.file.remote.hosts.allowed"));
  }

  /** Both lists must pass: a listed host does not excuse an unlisted protocol. */
  @Test void testListsAreConjunctive() {
    assertThrows(IllegalArgumentException.class, () ->
        FileSchema.checkSourceProtocolAllowed(
            Sources.url("ftp://data.example.com/table.csv"),
            "http, https", "data.example.com"));
  }
}
