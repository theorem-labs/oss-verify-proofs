(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition RSTAGE : Z := 0x66f79.
Definition RSTAGE_SZ : Z := 0x10000.

Definition PRIS : list (Z * Z) :=
[(0x10000,0x66f30); (0x66f31,0x66f79); (0x76f79,0x77b30); (0x97c08,0x97c18); (0x77b64,0x77bb0); (0x77bb8,0x77bd0);
(0x77bd8,0x77bf0); (0x77c00,0x77c10); (0x77c20,0x97c08); (0x97c40,0x97e70); (0x97e78,0x97e80); (0x97e91,0x97e98);
(0x97ec8,0x97ef8); (0x97f00,0x97f78); (0x98320,0x99000)].

Definition pris (m : mem) : Prop :=
Forall (fun iv => forall a, fst iv <= a < snd iv -> m (wa a) = None) PRIS.

Definition main_frame (usp0 : Z) : list cell :=
[C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 (usp0 + 32)); C8 (Z_to_bv 64 0x20b84);
C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 0x508ac)].
Definition MAIN_SP (usp0 : Z) : Z := usp0 - 128.
Definition MAIN_FR (usp0 : Z) : Z := usp0 - 120.

Section Iface.
Context {AMB : Amb}.

Record drv_entry (usp0 pp tid : Z) (path : list byte) (m : mem) : Prop := DE {
de_sp    : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0;
de_stk   : stk rsegs m (usp0 - 8388608) usp0;
de_frame : rw_cells rsegs m (usp0 - 120) (main_frame usp0);
de_errno : rw_cells rsegs m RERRNO [C4 (wz 0)];

de_ctx   : forall a : word, 0x97f78 <= bv_unsigned a < 0x98320 -> m a = None;
de_nl    : rw_cells rsegs m RNEED_LOCKS [C1 (Z_to_bv 8 0)];
de_ps    : rw_cells rsegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)];
de_got   : rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)];
de_guard : rw_cells rsegs m RSSP_GUARD [C8 rc_canary];
de_canary: bytes_at rsegs m (RATP - 16) (le8 rc_canary);
de_mi    : mem_inv rsegs m;
de_auxv  : rauxv_ok m usp0;

de_tid   : bytes_at rsegs m 0x77b58 (le4 (Z_to_bv 64 tid)) /\ 0 < tid < 2^22;
de_self  : bytes_at rsegs m 0x77b38 (le8 (Z_to_bv 64 0x77b38));
de_pris  : pris m;

de_stage : forall a, RSTAGE <= a < RSTAGE + RSTAGE_SZ -> m (wa a) = None;

de_path  : bytes_at rsegs m pp (path ++ [Z_to_bv 8 0]) /\ usp0 <= pp /\ pp + Z.of_nat (length path) + 9 <= usp0 + 4194304;
de_path8 : exists t8, bytes_at rsegs m (pp + Z.of_nat (length path)) t8 /\ length t8 = 8%nat;

de_loc   : bytes_at rsegs m 0x77bd0 (le8 (wz 0x97ec8));

de_ceil  : alloc_ceiling = usp0 - 8388608
}.
End Iface.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4FC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4FC.

Definition DRV_W : Z := 2^31.
Definition DRV_D : nat := 1000%nat.

Section Stmt.
Context {AMB : Amb}.

Definition read_entry_stmt (usp0 tid : Z) (ppw : word) (path : list byte)
(fds : list (word * FdEntry)) (fs : Fs.Fs) (KB : TSet) : Prop :=
forall (F : bvmap 5 word) (fc : bv 32) (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (m : mem) (md : Model),
drv_entry usp0 (bv_unsigned ppw) tid path m ->
HEAPc usp0 A0 [] m md -> BUD md DRV_W DRV_D ->
m_fds md = fds -> m_fs md = fs -> QCcH.frm0 fc ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 0x20bd8) (Z_to_bv 64 (usp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77c00)
t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7
ppw s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
F (Z_to_bv 64 0x521f4) fc None m (seg_rom rsegs)) md) KB.
End Stmt.
