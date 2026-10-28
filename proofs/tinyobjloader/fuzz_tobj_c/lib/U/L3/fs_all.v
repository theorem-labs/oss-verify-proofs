From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require aa.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require vf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L12 Require vp fsB.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3 Require fs fsT.

(* finalize_shape: head region (fs), tail from +852 (t-mal1's fsB), part from +1236 (fsT) *)
Theorem fs_sum_closed : fs_stmt_U.
Proof. exact (fs.fs_sum_U aa.aa_sum (fsB.fsB_sum_U (vf.vf_sum_U aa.aa_sum) (fsT.fsT_sum_U vp.vp_sum))). Qed.

Theorem fs_ex_closed : fs_ex_stmt_U.
Proof. exact (fs.fs_ex_U aa.aa_sum_ex (fsB.fsB_ex_U (vf.vf_ex_U aa.aa_sum_ex) (fsT.fsT_ex_U vp.vp_sum_ex))). Qed.
