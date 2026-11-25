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
  taint_status VARCHAR NOT NULL,
  taint_reason VARCHAR NOT NULL,
  locked_spec_hash VARCHAR,
  locked_body_hash VARCHAR,
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
  stratum VARCHAR NOT NULL,
  actual_axioms_json VARCHAR NOT NULL,
  cert_sha256 VARCHAR,
  verified_at_utc VARCHAR NOT NULL,
  passed BOOLEAN NOT NULL
);
