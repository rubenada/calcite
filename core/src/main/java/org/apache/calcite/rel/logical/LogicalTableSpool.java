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
package org.apache.calcite.rel.logical;

import org.apache.calcite.linq4j.function.Experimental;
import org.apache.calcite.plan.Convention;
import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelWriter;
import org.apache.calcite.rel.core.Spool;

/**
 * Spool that writes into a temporary table.
 *
 * <p>NOTE: The current API is experimental and subject to change without notice.</p>
 */
@Experimental
public class LogicalTableSpool extends Spool {

  protected final String tableName;

  //~ Constructors -----------------------------------------------------------
  public LogicalTableSpool(RelOptCluster cluster, RelTraitSet traitSet, RelNode input,
                           Type readType, Type writeType, String tableName) {
    super(cluster, traitSet, input, readType, writeType);
    this.tableName = tableName;
  }

  /** Creates a LogicalTableSpool. */
  public static LogicalTableSpool create(RelNode input, Type readType, Type writeType,
                                         String tableName) {
    RelOptCluster cluster = input.getCluster();
    RelTraitSet traitSet = cluster.traitSetOf(Convention.NONE);
    return new LogicalTableSpool(cluster, traitSet, input, readType, writeType, tableName);
  }

  //~ Methods ----------------------------------------------------------------

  @Override protected Spool copy(RelTraitSet traitSet, RelNode input,
                                 Type readType, Type writeType) {
    return new LogicalTableSpool(input.getCluster(), traitSet, input,
        readType, writeType, tableName);
  }

  public String getTableName() {
    return tableName;
  }

  @Override public RelWriter explainTerms(RelWriter pw) {
    super.explainTerms(pw);
    return pw.item("tableName", tableName);
  }
}

// End LogicalTableSpool.java
