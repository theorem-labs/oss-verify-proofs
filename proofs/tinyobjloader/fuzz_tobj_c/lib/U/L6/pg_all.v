From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_ex_fin.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6 Require Import S_pg S_pgB pg pg_ex pgB.

Theorem tess_polygon_U : tess_polygon_sum_stmt_U.
Proof. exact (tess_polygon_sum_U pgB_sum_U). Qed.

Theorem tess_polygon_ex_U : r2_sum_ex_stmt_U -> tess_polygon_sum_ex_stmt_U.
Proof. intros R2X. exact (tess_polygon_sum_ex_U (pgB_sum_ex_U R2X)). Qed.

Theorem tess_polygon_ex_closed_U : tess_polygon_sum_ex_stmt_U.
Proof. exact (tess_polygon_ex_U r2_sum_ex). Qed.
