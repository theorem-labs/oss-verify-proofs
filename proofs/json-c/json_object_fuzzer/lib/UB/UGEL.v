(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPZI. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ja_utf8rep : list byte := [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189].

Definition JA_UTF8REP_P : Z := 0x66a28.

Definition JA_GOT_FREE_USERDATA_P : Z := 0x658c0.

Definition TOKPARSE_STK_P : Z := 16 + 48 + 144 + 12288.

Section TokParseStmt.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Notation segs := (hl_segs L).

Record tokparse_consts := TPC {
tpc_entry : Z; tpc_stk : Z;
tpc_G : (word -> option byte) -> Prop; tpc_X : Z -> Prop;
tpc_LOCC : Z; tpc_GLOBL : Z; tpc_LOCK : Z; tpc_UTF8A : Z; tpc_GOTA : Z; tpc_GOTV : Z }.

Definition tokparse_statics (C : tokparse_consts) (m : word -> option byte) : Prop :=
rw_cells segs m (tpc_LOCC C) [C8 (Z_to_bv 64 (tpc_GLOBL C))] /\
rw_cells segs m (tpc_LOCK C) [C4 (Z_to_bv 64 0)] /\
tpc_G C m /\
bytes_at segs m (tpc_UTF8A C) ja_utf8rep /\
bytes_at segs m (tpc_GOTA C) (le8 (Z_to_bv 64 (tpc_GOTV C))).

Definition tokparse_post (C : tokparse_consts)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LBc : list blk) (lo : Z) (ms' : machine_state) (md' : Model) : Prop :=
exists (m' : word -> option byte) (A' : AS L HIx) (gp' : word) (r : Z) (errv' : word) (RBS LK : list blk),
ret_statew L ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
rw_cells segs m' (hl_tp L - 164) [C4 errv'] /\
tokparse_statics C m' /\
heap_presx L (tpc_X C) LBc (bv_unsigned sp) m m' /\
HEAP L HIx A' (RBS ++ LK ++ LBc) m' md' /\
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval segs fn s m' RBS r 1 /\ sdepth s <= 32)).

Definition tokparse_stmt (C : tokparse_consts) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LBc : list blk) (sb lo : Z) (str0 slack : list byte) (errv : word),
HEAP L HIx A LBc m md ->

bytes_at segs m sb (str0 ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str0 -> Z.of_nat (length str0) < 2^25 ->
bytes_at segs m (sb + Z.of_nat (length str0) + 1) slack ->
(- (sb + Z.of_nat (length str0) + 1)) mod 8 <= Z.of_nat (length slack) ->
bv_unsigned sp <= sb -> sb + Z.of_nat (length str0) + 1 < 2^63 ->
tokparse_statics C m ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - tpc_stk C ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top L HIx -> bv_unsigned sp <= 2^62 ->
rw_cells segs m (hl_tp L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 sb ->
(forall ms' md', tokparse_post C ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LBc lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (tpc_entry C)) fc None m (seg_rom segs)) md) T.
End TokParseStmt.

Definition ja_xloc_P (a : Z) : Prop := UC8c.Mq0.s4_volatile a \/ (QPZI.LOCCELL <= a < QPZI.LOCCELL + 8).

Definition tokparse_consts_P : tokparse_consts :=
TPC 0x21b24 TOKPARSE_STK_P UPZI.Mq0.jc_glob_P ja_xloc_P QPZI.LOCCELL QPZI.GLOBLOC QPZI.LOCALE_LOCK
JA_UTF8REP_P JA_GOT_FREE_USERDATA_P (fn_free_userdata UC8c.Mq0.S4F).

Definition tokparse_stmt_P (HIx : heap_iface UC8c.Mq0.S4L) : Prop := tokparse_stmt UC8c.Mq0.S4L HIx UC8c.Mq0.S4F tokparse_consts_P.

End RC__1.
