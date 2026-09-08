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
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.Table;
import org.apache.calcite.schema.impl.AbstractSchema;
import org.apache.calcite.util.Source;
import org.apache.calcite.util.Sources;
import org.apache.calcite.util.Util;

import au.com.bytecode.opencsv.CSVParser;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;

import org.checkerframework.checker.nullness.qual.Nullable;

import java.io.File;
import java.util.List;
import java.util.Map;

/**
 * Schema mapped onto a set of URLs / HTML tables. Each table in the schema
 * is an HTML table on a URL.
 *
 * <p>By default, only {@code file} sources are dereferenced. Table operands
 * naming remote URLs make the host fetch an arbitrary, model-supplied URL and
 * return the response as rows (potential server-side request forgery), so
 * remote protocols must be explicitly enabled by the operator via the
 * {@link CalciteSystemProperty#FILE_REMOTE_PROTOCOLS_ALLOWED} system property.
 */
class FileSchema extends AbstractSchema {
  private final ImmutableList<Map<String, Object>> tables;
  private final @Nullable File baseDirectory;

  /**
   * Creates an HTML tables schema.
   *
   * @param parentSchema  Parent schema
   * @param name          Schema name
   * @param baseDirectory Base directory to look for relative files, or null
   * @param tables        List containing HTML table identifiers, or null
   */
  FileSchema(SchemaPlus parentSchema, String name, @Nullable File baseDirectory,
      @Nullable List<Map<String, Object>> tables) {
    this.tables =
        tables == null ? ImmutableList.of()
            : ImmutableList.copyOf(tables);
    this.baseDirectory = baseDirectory;
  }

  /**
   * Looks for a suffix on a string and returns
   * either the string with the suffix removed
   * or the original string.
   */
  private static String trim(String s, String suffix) {
    String trimmed = trimOrNull(s, suffix);
    return trimmed != null ? trimmed : s;
  }

  /**
   * Looks for a suffix on a string and returns
   * either the string with the suffix removed
   * or null.
   */
  private static @Nullable String trimOrNull(String s, String suffix) {
    return s.endsWith(suffix)
        ? s.substring(0, s.length() - suffix.length())
        : null;
  }

  @Override protected Map<String, Table> getTableMap() {
    final ImmutableMap.Builder<String, Table> builder = ImmutableMap.builder();

    for (Map<String, Object> tableDef : this.tables) {
      addTable(builder, tableDef);
    }

    // Look for files in the directory ending in ".csv", ".csv.gz", ".json",
    // ".json.gz".
    if (baseDirectory != null) {
      final Source baseSource = Sources.of(baseDirectory);
      File[] files = baseDirectory.listFiles((dir, name) -> {
        final String nameSansGz = trim(name, ".gz");
        return nameSansGz.endsWith(".csv")
            || nameSansGz.endsWith(".json");
      });
      if (files == null) {
        System.out.println("directory " + baseDirectory + " not found");
        files = new File[0];
      }
      // Build a map from table name to table; each file becomes a table.
      for (File file : files) {
        Source source = Sources.of(file);
        Source sourceSansGz = source.trim(".gz");
        final Source sourceSansJson = sourceSansGz.trimOrNull(".json");
        if (sourceSansJson != null) {
          addTable(builder, source, sourceSansJson.relative(baseSource).path(),
              null);
        }
        final Source sourceSansCsv = sourceSansGz.trimOrNull(".csv");
        if (sourceSansCsv != null) {
          addTable(builder, source, sourceSansCsv.relative(baseSource).path(),
              null);
        }
      }
    }

    return builder.build();
  }

  /** Checks that the protocol of a model-supplied source may be dereferenced
   * by this adapter: {@code file} always, any remote protocol only when the
   * operator has listed it in
   * {@link CalciteSystemProperty#FILE_REMOTE_PROTOCOLS_ALLOWED}, and (if the
   * host allowlist {@link CalciteSystemProperty#FILE_REMOTE_HOSTS_ALLOWED} is
   * set) only when the URL's host is on that list. */
  static void checkSourceProtocolAllowed(Source source) {
    checkSourceProtocolAllowed(source,
        CalciteSystemProperty.FILE_REMOTE_PROTOCOLS_ALLOWED.value(),
        CalciteSystemProperty.FILE_REMOTE_HOSTS_ALLOWED.value());
  }

  static void checkSourceProtocolAllowed(Source source, String allowedProtocols) {
    checkSourceProtocolAllowed(source, allowedProtocols, "");
  }

  static void checkSourceProtocolAllowed(Source source, String allowedProtocols,
      String allowedHosts) {
    final String protocol = source.protocol();
    if ("file".equals(protocol)) {
      return;
    }
    boolean protocolMatch = false;
    for (String p : allowedProtocols.split(",")) {
      if (protocol.equalsIgnoreCase(p.trim())) {
        protocolMatch = true;
        break;
      }
    }
    if (!protocolMatch) {
      throw new IllegalArgumentException("Remote URL protocol '" + protocol
          + "' is not allowed in file adapter table operands (only 'file' is"
          + " allowed by default); to allow it, add it to the system property"
          + " \"calcite.file.remote.protocols.allowed\"");
    }
    if (allowedHosts.trim().isEmpty()) {
      return;
    }
    final String host = source.url().getHost();
    for (String h : allowedHosts.split(",")) {
      final String allowed = h.trim();
      if (!allowed.isEmpty() && allowed.equalsIgnoreCase(host)) {
        return;
      }
    }
    throw new IllegalArgumentException("Remote URL host '" + host
        + "' is not on the file adapter host allowlist; to allow it, add it"
        + " to the system property \"calcite.file.remote.hosts.allowed\"");
  }

  private boolean addTable(ImmutableMap.Builder<String, Table> builder,
      Map<String, Object> tableDef) {
    final String tableName = (String) tableDef.get("name");
    final String url = (String) tableDef.get("url");
    final Source source0 = Sources.url(url);
    checkSourceProtocolAllowed(source0);
    final Source source;
    if (baseDirectory == null) {
      source = source0;
    } else {
      source = Sources.of(baseDirectory).append(source0);
    }
    return addTable(builder, source, tableName, tableDef);
  }

  private static boolean addTable(ImmutableMap.Builder<String, Table> builder,
      Source source, String tableName, @Nullable Map<String, Object> tableDef) {
    final Source sourceSansGz = source.trim(".gz");
    final Source sourceSansJson = sourceSansGz.trimOrNull(".json");
    if (sourceSansJson != null) {
      final Table table = new JsonScannableTable(source);
      builder.put(Util.first(tableName, sourceSansJson.path()), table);
      return true;
    }
    final Source sourceSansCsv = sourceSansGz.trimOrNull(".csv");
    if (sourceSansCsv != null) {
      final Table table =
          new CsvTranslatableTable(source, null, CSVParser.DEFAULT_SEPARATOR);
      builder.put(Util.first(tableName, sourceSansCsv.path()), table);
      return true;
    }

    if (tableDef != null) {
      try {
        FileTable table = FileTable.create(source, tableDef);
        builder.put(Util.first(tableName, source.path()), table);
        return true;
      } catch (Exception e) {
        throw new RuntimeException("Unable to instantiate table for: "
            + tableName);
      }
    }

    return false;
  }
}
