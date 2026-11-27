DROP TABLE IF EXISTS pub_targets;
DROP TABLE IF EXISTS work_items;
DROP TABLE IF EXISTS decl_ownership;
DROP TABLE IF EXISTS claim_groundings;
DROP TABLE IF EXISTS verification_receipts;
DROP TABLE IF EXISTS symbols;
DROP TABLE IF EXISTS edges;
DROP TABLE IF EXISTS nodes;

CREATE TABLE nodes (
  id VARCHAR PRIMARY KEY,
  kind VARCHAR NOT NULL,
  title VARCHAR NOT NULL,
  chapter VARCHAR NOT NULL,
  section VARCHAR NOT NULL,
  seq_order INTEGER NOT NULL DEFAULT 1000,
  axis VARCHAR NOT NULL,
  grounding_tier VARCHAR NOT NULL,
  formal_pkg VARCHAR NOT NULL,
  stratum VARCHAR NOT NULL,
  module VARCHAR,
  decl_names_json VARCHAR NOT NULL,
  expected_axioms_json VARCHAR NOT NULL,
  cert_path VARCHAR,
  spec_hash VARCHAR NOT NULL,
  body_hash VARCHAR NOT NULL,
  grounding_hash VARCHAR NOT NULL DEFAULT '',
  taint_status VARCHAR NOT NULL,
  taint_reason VARCHAR NOT NULL,
  locked_spec_hash VARCHAR,
  locked_body_hash VARCHAR,
  locked_grounding_hash VARCHAR,
  file_path VARCHAR NOT NULL,
  raw_json VARCHAR NOT NULL
);

CREATE TABLE edges (
  src_id VARCHAR NOT NULL,
  dst_id VARCHAR NOT NULL,
  fiber VARCHAR NOT NULL,
  metadata_json VARCHAR NOT NULL
);

CREATE TABLE symbols (
  macro_key VARCHAR PRIMARY KEY,
  symbol_node_id VARCHAR NOT NULL,
  latex_macro VARCHAR NOT NULL,
  description VARCHAR NOT NULL
);

CREATE TABLE verification_receipts (
  node_id VARCHAR PRIMARY KEY,
  spec_hash VARCHAR NOT NULL,
  body_hash VARCHAR NOT NULL,
  grounding_hash VARCHAR NOT NULL DEFAULT '',
  stratum VARCHAR NOT NULL,
  actual_axioms_json VARCHAR NOT NULL,
  cert_sha256 VARCHAR,
  verified_at_utc VARCHAR NOT NULL,
  passed BOOLEAN NOT NULL
);

CREATE TABLE claim_groundings (
  node_id VARCHAR PRIMARY KEY REFERENCES nodes(id),
  cohort VARCHAR NOT NULL,
  primary_category VARCHAR NOT NULL,
  blueprint_tier VARCHAR NOT NULL,
  characterization_types_json VARCHAR NOT NULL,
  witness_scope VARCHAR NOT NULL,
  dual_pillars_json VARCHAR NOT NULL,
  grounding_hash VARCHAR NOT NULL
);

CREATE TABLE decl_ownership (
  decl_or_cert VARCHAR PRIMARY KEY,
  node_id VARCHAR NOT NULL REFERENCES nodes(id),
  ownership_kind VARCHAR NOT NULL
);

CREATE TABLE work_items (
  node_id VARCHAR PRIMARY KEY REFERENCES nodes(id),
  milestone VARCHAR NOT NULL,
  milestone_num INTEGER NOT NULL,
  slice_code VARCHAR NOT NULL,
  target_modules_json VARCHAR NOT NULL,
  deliverable_nodes_json VARCHAR NOT NULL,
  guardrails_json VARCHAR NOT NULL,
  summary VARCHAR NOT NULL,
  status VARCHAR NOT NULL,
  verified_deliverables INTEGER NOT NULL,
  total_deliverables INTEGER NOT NULL
);

CREATE TABLE pub_targets (
  node_id VARCHAR PRIMARY KEY REFERENCES nodes(id),
  channel VARCHAR NOT NULL,
  sensitivity VARCHAR NOT NULL,
  outputs_json VARCHAR NOT NULL,
  published_paths_json VARCHAR NOT NULL,
  cone_hash VARCHAR NOT NULL,
  locked_cone_hash VARCHAR,
  pub_status VARCHAR NOT NULL,
  pub_reason VARCHAR NOT NULL
);
