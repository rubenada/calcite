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
import org.apache.calcite.util.Sources;

/**
 * Auxiliary class that centralizes the P3 (no-SSRF) enforcement for the
 * file adapter, so both {@link FileSchema} (at schema-construction time)
 * and {@link FileReader} (at fetch time, defense in depth) apply the same
 * policy.
 *
 * <p>Policy is driven by two system properties, both configured for a
 * secure-by-default posture per the Calcite security threat model:
 *
 * <ul>
 *   <li>{@link CalciteSystemProperty#FILE_ADAPTER_ALLOWED_URL_SCHEMES}
 *       &mdash; default {@code "file,https"}</li>
 *   <li>{@link CalciteSystemProperty#FILE_ADAPTER_BLOCK_PRIVATE_NETWORKS}
 *       &mdash; default {@code true}</li>
 * </ul>
 *
 * <p>Throws {@link SecurityException} on any violation; callers let
 * it propagate (aborting schema construction / fetch respectively).
 */
final class FileSchemaUrlGuard {
  private FileSchemaUrlGuard() {}

  /** Applies the configured scheme and private-network policy to
   * {@code url}. No-op for a {@code null} url. */
  static void check(String url) {
    if (url == null) {
      return;
    }
    Sources.checkAllowedScheme(url,
        Sources.parseAllowedUrlSchemes(
            CalciteSystemProperty.FILE_ADAPTER_ALLOWED_URL_SCHEMES.value()));
    if (CalciteSystemProperty.FILE_ADAPTER_BLOCK_PRIVATE_NETWORKS.value()) {
      Sources.checkNotPrivateNetwork(url);
    }
  }
}
