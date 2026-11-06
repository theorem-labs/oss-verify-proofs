(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD QXup Lib.GwApply QWxq_c1 Lib.SepCache QHnV QCcH QfLs Q0Ek Qsw7 QJjn QBpc Qhd4 Qwm6 QsKa Q2y2 QdM4 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QBpc.
Import Qhd4.
Import Qwm6.Mq0.

Import Q2y2 QdM4.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Section Ga.
Context {RC__ : Q6q3.RunConsts}.

Lemma img_c4_any : forall A m, img_rw_b A 4 = true -> 0 <= A -> A + 4 <= 2^64 -> exists v, rw_cells asegs m A [C4 v].
Proof.
intros A m Hb HA Hhi. destruct (img_rw_any A 4 m Hb HA ltac:(cbn; lia)) as (junk & RW).
destruct RW as [[WF BA] WR]. cbn in WF. destruct WF as [WF _].
exists (sext 64 (bv_extract 0 32 (le_bytes_to_word junk))). split; [split; [cbn; split; exact I|] | exact WR].
cbn [cells_bytes cbytes app] in BA |- *. rewrite (le4_lw junk WF). exact BA.
Qed.

Theorem lh_globA_of_drv : forall argv USP m, drvA_mem argv USP m -> QsKa.Mq5.lh_globA m.
Proof.
intros argv USP m D. pose proof (dm_pris _ _ _ D) as P. pris_get P 0xea500 0xea560.
split.
- refine (rw_cells_pristine_recast m QsKa.Mq5.GHASHA (le8 (Z_to_bv 64 (fn_lh_char_hash A4F))) _ _ _ _ _ _ _ _).
+ apply (pristine_sub m 0xea500 0xea560); [exact PR | unfold QsKa.Mq5.GHASHA; lia | unfold QsKa.Mq5.GHASHA; cbn; lia].
+ vm_compute. reflexivity.
+ unfold QsKa.Mq5.GHASHA. lia.
+ unfold QsKa.Mq5.GHASHA. cbn. lia.
+ cbn. tauto.
+ cbn [cells_bytes cbytes]. apply app_nil_r.
+ reflexivity.
- apply img_c4_any; [vm_compute; reflexivity | unfold QsKa.Mq5.GSEEDA; lia | unfold QsKa.Mq5.GSEEDA; lia].
Qed.

Theorem jhex_of_drv : forall argv USP m, drvA_mem argv USP m -> bytes_at asegs m 0xea520 (le8 (Z_to_bv 64 0x23320)).
Proof.
intros argv USP m D. pose proof (dm_pris _ _ _ D) as P. pris_get P 0xea500 0xea560.
assert (RW : rw_cells asegs m 0xea520 [C8 (Z_to_bv 64 0x23320)]).
{ refine (rw_cells_pristine_recast m 0xea520 (le8 (Z_to_bv 64 0x23320)) _ _ _ _ _ _ _ _).
+ apply (pristine_sub m 0xea500 0xea560); [exact PR | lia | cbn; lia].
+ vm_compute. reflexivity.
+ lia.
+ cbn. lia.
+ cbn. tauto.
+ cbn [cells_bytes cbytes]. apply app_nil_r.
+ reflexivity. }
destruct RW as [[_ BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
Qed.

Theorem utf8rep_of_drv : forall argv USP m, drvA_mem argv USP m -> bytes_at asegs m 0xea500 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189].
Proof.
intros argv USP m D. pose proof (dm_pris _ _ _ D) as P. pris_get P 0xea500 0xea560.
assert (RW : rw_cells asegs m 0xea500 [CB 3 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189]]).
{ refine (rw_cells_pristine_recast m 0xea500 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189] _ _ _ _ _ _ _ _).
+ apply (pristine_sub m 0xea500 0xea560); [exact PR | lia | cbn; lia].
+ vm_compute. reflexivity.
+ lia.
+ cbn. lia.
+ cbn. tauto.
+ cbn [cells_bytes cbytes]. apply app_nil_r.
+ reflexivity. }
destruct RW as [[_ BA] _]. cbn [cells_bytes cbytes app] in BA. exact BA.
Qed.

Theorem ga_jo_of_drv : forall argv USP m, drvA_mem argv USP m ->
QsKa.Mq5.lh_globA m /\ bytes_at asegs m 0xea520 (le8 (Z_to_bv 64 0x23320)) /\ bytes_at asegs m 0xea500 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189].
Proof. intros argv USP m D. split; [exact (lh_globA_of_drv argv USP m D) | split; [exact (jhex_of_drv argv USP m D) | exact (utf8rep_of_drv argv USP m D)]]. Qed.

End Ga.
End Mq0.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Monad Fs Specs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC QCKW QPra QsRG Qnhz QBxa QRjH QsV0 Qn1e QMz4 Q9ox QSpR Qe4Y QlKV Qw5U QpNt Q0TL Qujl QnXa Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD Qhd4 QGcC.Mq0.
Import QCKW.Mq0 QPra.Mq1.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QBxa.Mq5 QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Qw5U.Mq4 QpNt.Mq4.
Import Q0TL Qujl QnXa Qirj.Mq0 Q2y2 QdM4.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition READPT_A : Z := 0x916c4.
Definition COPY_A : Z := 0x91668.
Definition GROW_A : Z := 0x9168c.
Definition HDRPT_A : Z := 0x916f4.
Definition RDENTRY_A : Z := 0x91640.

Section DrvReadA.
Context {RC__ : Q6q3.RunConsts}.

Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation HEAPA6 := (QZsi.HEAPA A4L H6).
Notation bud6 := QZsi.bud.

Lemma hr_view : forall A LB LM FR (B : bud6) m md, HEAPA6 A LB LM FR B m md -> HEAPAx A LB LM FR (Bud 0 0 0) m md.
Proof.
intros A LB LM FR B m md HP. eapply (heapa5_enter A4L H6); [exact HP|].
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP) as (Q1 & Q2 & Q3 & Q4 & Q5).
unfold blink. cbn [bB bD bM]. lia.
Qed.
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.
Ltac d5_reenter A := lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj_evt J T c ms _); change (evt asegs (AJe A4L J A T c) ms) end.

Variable reqA : ASA A4L HIx -> Z.
Hypothesis OBL_MALLOC_N6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (n lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) ra u ->
1 <= QZsi.bN B -> acostA n <= QZsi.bB B -> uw_cost u <= QZsi.bD B -> n + 8192 <= QZsi.bQ B -> reqA A + n <= 2^31 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]) ->
HEAPA6 A' ((r, n) :: LB) LM FR (QZsi.chargeQ (QZsi.charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' md' ->
reqA A' <= reqA A + n ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_FREE_N6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (p lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
(if Z.eqb p 0 then 0 else uw_cost u) <= QZsi.bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPA6 A' (lb_remove p LB) LM FR (QZsi.charge B 0 (if Z.eqb p 0 then 0 else uw_cost u) 0) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).

Definition cs_wide (a : Z) : Prop :=
(0xea500 <= a < 0xec420)
\/ (0xec448 <= a < 0xec498) \/ (0x181998 <= a < 0x1819a8) \/ (0x612140 <= a < 0x622d90)
\/ (0x622d90 <= a < 0x644280 /\ ~ (0x622dbc <= a < 0x622dc0) /\ ~ (0x622e50 <= a < 0x622e58) /\ ~ (0x622e08 <= a < 0x622e10) /\ ~ (0x622e58 <= a < 0x622e98)
/\ ~ (0x642ea0 <= a < 0x642ea8) /\ ~ (0x6430f0 <= a < 0x643158) /\ ~ (0x6431e0 <= a < 0x643588)).
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.

Variables (argv : list (list byte)) (USP LO : Z) (path data : list byte) (fs : Fs.Fs) (LM0 : list blk).
Variables (fds0 : list (word * FdEntry)).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis FS : fs_lookup fs path = Some data.
Hypothesis LEND : Z.of_nat (length data) < 2^40.
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Definition LFDS (fds : list (word * FdEntry)) (len : Z) : Prop :=
fd_lookup fds (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 len)) /\
forall fd', fd' <> Z_to_bv 64 3 -> fd_lookup fds fd' = fd_lookup fds0 fd'.
Definition CFDS (fds : list (word * FdEntry)) : Prop :=
fd_lookup fds (Z_to_bv 64 3) = None /\ forall fd', fd' <> Z_to_bv 64 3 -> fd_lookup fds fd' = fd_lookup fds0 fd'.

Definition main_frame (j8 : list byte) (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition RD_NEED (k : nat) (cap : Z) : Z := 2^31 - 32 * cap + (10 - Z.of_nat k) * 1024.

Definition RDQ (k : nat) (cap : Z) : Z := 134217728 - 2 * cap + (10 - Z.of_nat k) * 8192.
Definition RDB (k : nat) (cap : Z) : Z := 3 * (134217728 - 2 * cap) + (10 - Z.of_nat k) * 45101.

Variables (BB_REST BD_REST : Z).
Variables (BQ_REST BN_REST : Z).
Definition rest_bud (B : bud6) : Prop :=
BQ_REST <= QZsi.bQ B /\ BB_REST <= QZsi.bB B /\ BN_REST <= QZsi.bN B /\ BD_REST <= QZsi.bD B
/\ BD_REST <= 134217728 * QZsi.bM B.
Definition rd_bud (k : nat) (cap : Z) (B : bud6) : Prop :=
RDQ k cap + BQ_REST <= QZsi.bQ B /\ RDB k cap + BB_REST <= QZsi.bB B
/\ (10 - Z.of_nat k) + BN_REST <= QZsi.bN B /\ BD_REST <= QZsi.bD B /\ BD_REST <= 134217728 * QZsi.bM B.

Record LINV (k : nat) (len cap buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) : Prop := MKL {
l_mem  : drvA_memS argv USP m;
l_heap : HEAPA6 A [(buf, cap)] LM0 [] B m md;
l_req  : reqA A <= 2^20 + 2 * cap;
l_cap  : cap = 65536 * 2 ^ Z.of_nat k /\ (k <= 10)%nat;
l_len  : 0 <= len <= cap /\ len <= Z.of_nat (length data);
l_blk  : exists junk, rw_cells asegs m buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk];
l_errno: exists errv, rw_cells asegs m (A_TP - 164) [C4 errv];
l_stk  : stk asegs m LO SP;
l_frame: exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN));
l_fds  : LFDS (m_fds (cfg_model md)) len;
l_fs   : m_fs (cfg_model md) = fs;
l_bud  : rd_bud k cap B
}.

Hypothesis OBL_CLIENT_FRAME : forall A LB LM FR B m m' md, HEAPAx A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPAx A LB LM FR B m' md.

Definition cwin (LB : list blk) (iv : Z * Z) : Prop :=
fst iv <= snd iv /\
( alloc_ceiling <= fst iv
\/ (forall a, fst iv <= a < snd iv -> cs_wide a)
\/ (exists b n, In (b, n) LB /\ b <= fst iv /\ snd iv <= b + n) ).

Hypothesis OBL_CLIENT_FRAME6 : forall A LB LM FR (B : bud6) m m' md, HEAPA6 A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPA6 A LB LM FR B m' md.
Lemma heapA_munch6 : forall A LB LM (B : bud6) m m' md W,
HEAPA6 A LB LM [] B m md -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (cwin LB) W -> HEAPA6 A LB LM [] B m' md.
Proof.
intros A LB LM B m m' md W HP MU WM MI' FW.
eapply OBL_CLIENT_FRAME6; [exact HP | | intros x Hx; apply WM; exact Hx | exact MI'].
intros a Ha NC _ _. apply MU. rewrite wa_unsigned by lia.
clear - FW NC Ha OBL_CS_WIDE. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [outside fst snd] in *. split; [| apply IH; exact FW].
intros [X1 X2]. apply NC. destruct HC as [H2 | [H2 | (b & n & HIN & H2 & H3)]].
- left. lia.
- right; left. apply OBL_CS_WIDE. apply H2. lia.
- right; right. exists (b, n). split; [apply in_or_app; left; exact HIN | cbn; lia].
Qed.

Lemma stage_shadow : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md ->
forall g, RS_GLO <= g < RS_GHI -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0].
Proof.
intros A LB LM FR B m md HP g Hg. unfold RS_GLO, RS_GHI in Hg.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ g HP ltac:(cbn; lia) ltac:(cbn; lia)) as SH.
cbn [hl_sb hl_reg_globals A4L] in SH.
rewrite (img_shadow_val_outside tokA_reg_globals 0xc2428 0xc4430 g ltac:(vm_compute; reflexivity) ltac:(lia)) in SH. exact SH.
Qed.

Lemma real_read_cell : forall m, rtc_R m -> ro_cells asegs m REAL_READ_CELL [C8 (Z_to_bv 64 READ_SYM)].
Proof. intros m P. unfold REAL_READ_CELL, READ_SYM. rtcR_cell P 0xe7c58 (le8 (Z_to_bv 64 0xe1270)).
Qed.

Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs,
bytes_at asegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at asegs m' a bs.
Proof.
intros m m' a bs (H1 & H2 & H3) E. split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold mrd in *. rewrite E by lia. apply H3. exact Hi.
Qed.

Lemma bytes_at_prefix : forall (m : word -> option byte) a bs k,
bytes_at asegs m a bs -> (k <= length bs)%nat -> bytes_at asegs m a (firstn k bs).
Proof.
intros m a bs k (H1 & H2 & H3) Hk. split; [exact H1|]. split; [rewrite length_firstn; lia|].
intros i Hi. rewrite length_firstn in Hi. rewrite (H3 i) by lia. rewrite nth_error_firstn.
replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

Definition in_pris (x : Z) : Prop := Exists (fun iv => fst iv <= x < snd iv) PRIS_A.
Definition dcell (x : Z) : Prop :=
USP <= x < USP + 2^22 \/ in_pris x \/ A_TP - 168 <= x < A_TP - 164 \/ T_LOCCELL_A <= x < T_LOCCELL_A + 8 \/ ATEXIT_A <= x < ATEXIT_A + 304
\/ ADFLAG_A <= x < ADFLAG_A + 1.

Lemma argstr_agree : forall m m' p s, argstr m USP p s -> (forall x, USP <= x < USP + 2^22 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) -> argstr m' USP p s.
Proof.
intros m m' p s (B1 & B2 & B3 & B4 & (t & B5 & B6)) EQ. pose proof B4 as [B4a B4b].
assert (LT : Z.of_nat (length t) <= 8 \/ 8 < Z.of_nat (length t)) by lia.
split; [| split; [exact B2 | split; [exact B3 | split; [exact B4 |]]]].
- eapply bytes_at_agree; [exact B1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQ; lia.
- exists (firstn 8 t). split.
+ destruct LT as [LT|LT].
* rewrite firstn_all2 by lia. eapply bytes_at_agree; [exact B5|]. intros x Hx. apply EQ; lia.
* eapply bytes_at_agree; [apply (bytes_at_prefix m _ t 8 B5); lia|]. intros x Hx. rewrite length_firstn in Hx. apply EQ; lia.
+ rewrite length_firstn. lia.
Qed.

Lemma drvA_mem_agree : forall m m', drvA_mem argv USP m ->
(forall x, 0 <= x < 2^64 -> dcell x -> m' (wa x) = m (wa x)) ->
(forall x, dcell (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None) -> mem_inv asegs m' ->
drvA_mem argv USP m'.
Proof.
intros m m' D EQ WM MI'. destruct D as [MI ARGC (p0 & A0 & S0) ARG1 PR (tid & TID & TIDR) LOC (mid & AT & MIDL)].
pose proof USPF as (U1 & U2 & U3).
assert (PH : ax_phase m' = ax_phase m) by (apply ax_phase_agree; apply EQ; [unfold ADFLAG_A; lia | unfold dcell; repeat (lazymatch goal with |- _ \/ _ => right end); unfold ADFLAG_A; lia]).
assert (EQA : forall x, USP <= x < USP + 2^22 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) by (intros; apply EQ; [lia | left; lia]).
assert (ROT : forall A cs, ro_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcell x) -> ro_cells asegs m' A cs).
{ intros A cs [WF BA] HD. split; [exact WF|]. eapply bytes_at_agree; [exact BA|]. intros x Hx.
rewrite cells_bytes_length in Hx by exact WF. destruct BA as (B0 & B1 & _). rewrite cells_bytes_length in B1 by exact WF. apply EQ; [lia | apply HD; lia]. }
assert (RWT : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcell x) -> rw_cells asegs m' A cs).
{ intros A cs [RO (W1 & W2 & W3)] HD. split; [apply ROT; assumption|]. split; [exact W1|]. split; [exact W2|]. intros i Hi.
apply WM; [| apply W3; exact Hi]. rewrite wa_unsigned by lia. apply HD. lia. }
constructor.
- exact MI'.
- exact ARGC.
- exists p0. split; [| eapply argstr_agree; [exact S0 | exact EQA]]. apply ROT; [exact A0|]. cbn. intros; left; lia.
- intros H2. destruct (ARG1 H2) as (p1 & A1 & S1). exists p1. split; [| eapply argstr_agree; [exact S1 | exact EQA]]. apply ROT; [exact A1|]. cbn. intros; left; lia.
- unfold pris_A in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PR _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0.
assert (R : 0 <= lo /\ hi <= 2^64) by (unfold PRIS_A in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN).
apply EQ; [lia|]. right; left. unfold in_pris. apply Exists_exists. exists (lo, hi). split; [exact IN | cbn; lia].
- exists tid. split; [| exact TIDR]. apply ROT; [exact TID|]. cbn. intros; right; right; left; lia.
- apply RWT; [exact LOC|]. cbn. intros; right; right; right; left; lia.
- exists mid. split; [| exact MIDL]. unfold atexit_cells in AT |- *. rewrite PH. apply RWT; [exact AT|]. rewrite (atexit_cellsK_size _ _ MIDL). unfold ATEXIT_A. intros; right; right; right; right; left; unfold ATEXIT_A; lia.
Qed.

Definition dwin (iv : Z * Z) : Prop :=
fst iv <= snd iv /\
( (LO <= fst iv /\ snd iv <= USP - 48) \/ (RSTAGE <= fst iv /\ snd iv <= RSTAGE + 65536) \/ (0x645000 <= fst iv /\ snd iv <= USP - 48) ).

Lemma dcell_cases : forall x, dcell x ->
USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x645000 /\ ~ (RSTAGE <= x < RSTAGE + 65536) /\ cs_wide x).
Proof.
intros x [H|[H|[H|[H|[H|H]]]]].
- left; exact H.
- right. unfold in_pris, PRIS_A in H. unfold cs_wide, RSTAGE.
repeat (apply Exists_cons in H; destruct H as [H|H]; [cbn [fst snd] in H; lia|]). apply Exists_nil in H. destruct H.
- right. unfold A_TP, cs_wide, RSTAGE in *. lia.
- right. unfold T_LOCCELL_A, A_TP, cs_wide, RSTAGE in *. lia.
- right. unfold ATEXIT_A, cs_wide, RSTAGE in *. lia.
- right. unfold ADFLAG_A, cs_wide, RSTAGE in *. lia.
Qed.

Lemma drvA_mem_munch : forall m m' W, drvA_mem argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall dwin W -> drvA_mem argv USP m'.
Proof.
intros m m' W D MU WM MI' FW. pose proof LOF as [L1 L2]. rc_lia_prep. unfold alloc_ceiling in L1.
eapply drvA_mem_agree; [exact D | | intros x _ Hx; apply WM; exact Hx | exact MI'].
intros x Hx HC. apply MU. rewrite wa_unsigned by lia. apply dcell_cases in HC.
clear - FW HC Hx L1 L2 H. unfold dwin, RSTAGE in *. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW].
Qed.

Lemma drvA_mem_pres : forall LBM m m',
drvA_mem argv USP m -> heap_pres A4H LBM SP m m' -> mem_inv asegs m' -> drvA_mem argv USP m'.
Proof.
intros LBM m m' D PRES MI'. pose proof LOF as [L1 L2].
assert (CL : forall x, dcell x -> client_addr A4H LBM SP x).
{ intros x HC. apply dcell_cases in HC. destruct HC as [HC|(HC1 & HC2 & HC3)]; [left; lia | right; left; apply OBL_CS_WIDE; exact HC3]. }
eapply drvA_mem_agree; [exact D | | | exact MI'].
- intros x Hx HC. apply PRES; [lia | apply CL; exact HC].
- intros x HC Hw. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
rewrite <- (Z_to_bv_bv_unsigned x) in Hw |- *. apply (proj2 (PRES (bv_unsigned x) ltac:(cbn in R; lia) (CL _ HC))). exact Hw.
Qed.

Lemma drvA_memS_munch : forall m m' W, drvA_memS argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall dwin W -> drvA_memS argv USP m'.
Proof.
intros m m' W [D S] MU WM MI' FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
split; [eapply drvA_mem_munch; eassumption|].
eapply stdio0_munch; [exact S | exact MU |]. clear - FW L1 L2 H U2 U3. unfold dwin, RSTAGE in *.
induction W as [|[lo hi] W IH]; [constructor|]. apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [fst snd] in *.
constructor; [cbn [fst snd]; lia | apply IH; exact FW].
Qed.

Lemma drvA_memS_pres : forall LBM m m',
drvA_memS argv USP m -> heap_pres A4H LBM SP m m' -> mem_inv asegs m' -> drvA_memS argv USP m'.
Proof.
intros LBM m m' [D S] PRES MI'. split; [eapply drvA_mem_pres; eassumption|].
eapply stdio0_agree; [exact S|]. intros x Hx HI. apply in_stdio0_cases in HI.
apply PRES; [lia|]. right; left. apply OBL_CS_WIDE. unfold cs_wide. lia.
Qed.

Definition LOOP_A : Z := 0x91680.

Definition readpt_stmt (k : nat) (len cap : Z) : Prop :=
forall (buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A B -> frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READPT_A) fc None m (seg_rom asegs)).

Definition loopk_stmt (k : nat) (len cap : Z) : Prop :=
forall (buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A B -> frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 LOOP_A) fc None m (seg_rom asegs)).
Definition loop_stmt : Prop := forall k len cap, loopk_stmt k len cap.

Record HINV (cap buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) : Prop := MKH {
h_mem  : drvA_memS argv USP m;
h_heap : HEAPA6 A [(buf, cap)] LM0 [] B m md;
h_req  : reqA A <= 2^20 + 2 * cap;
h_cap  : 65536 <= cap <= 2^26;
h_len  : Z.of_nat (length data) < cap;
h_blk  : exists junk, rw_cells asegs m buf [CB (length data) data; CB (Z.to_nat (cap - Z.of_nat (length data))) junk];
h_errno: exists errv, rw_cells asegs m (A_TP - 164) [C4 errv];
h_stk  : stk asegs m LO SP;
h_frame: exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN));
h_fds  : CFDS (m_fds (cfg_model md));
h_fs   : m_fs (cfg_model md) = fs;
h_bud  : rest_bud B
}.
Definition hdr_stmt : Prop :=
forall (cap buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HINV cap buf m md A B -> frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 3) (Z_to_bv 64 cap) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 HDRPT_A) fc None m (seg_rom asegs)).

Lemma cap_bounds : forall k cap, cap = 65536 * 2 ^ Z.of_nat k -> (k <= 10)%nat -> 65536 <= cap <= 2^26.
Proof.
intros k cap -> Hk. pose proof (Z.pow_le_mono_r 2 0 (Z.of_nat k) ltac:(lia) ltac:(lia)) as P1.
pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 10 ltac:(lia) ltac:(lia)) as P2. change (2^0) with 1 in P1. change (2^26) with (65536 * 2^10). nia.
Qed.

Lemma stage_rw_any : forall m, exists junk, rw_cells asegs m RSTAGE [CB (Z.to_nat 65536) junk].
Proof. intros m. apply (img_rw_any RSTAGE (Z.to_nat 65536) m); [vm_compute; reflexivity | unfold RSTAGE; lia | rewrite Z2Nat.id by lia; unfold RSTAGE; lia]. Qed.

Lemma rw_cells_app2 : forall m a c1 c2, rw_cells asegs m a [c1; c2] <-> rw_cells asegs m a [c1] /\ rw_cells asegs m (a + Z.of_nat (csize c1)) [c2].
Proof.
intros m a c1 c2. pose proof (QJjn.rw_cells_app asegs m a [c1] [c2]) as X. cbn [app cells_size Nat.add] in X. rewrite Nat.add_0_r in X. exact X.
Qed.

Lemma fd_lookup_remove_eq : forall fds fd, fd_lookup (fd_remove fds fd) fd = None.
Proof.
intros fds fd. unfold fd_remove. induction fds as [|[k e] r IH]; [reflexivity|]. simpl.
destruct (bv_eqb k fd) eqn:E; simpl; [exact IH | rewrite E; exact IH].
Qed.

Hypothesis RESTS6 : 0 <= BB_REST /\ 0 <= BD_REST /\ 0 <= BQ_REST /\ 0 <= BN_REST.
Definition READCALL_A : Z := 0x916d4.

Lemma seg_read2 : forall k len cap cnt, hdr_stmt ->
len < cap -> 1 <= cnt <= 65536 -> cnt <= cap - len ->
(forall n, 1 <= n -> len + n <= cap -> loopk_stmt k (len + n) cap) ->
forall (buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A B -> frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 (Z_to_bv 64 cnt) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READCALL_A) fc None m (seg_rom asegs)).
Proof.
intros k len cap cnt HDR LT Hcnt Hcnt2 NEXT. intros until fc. intros LI FRM.
destruct LI as [DM HP6 REQ [Hcap Hk] [Hlen Hlen2] (junk & BLK) (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) Hfds Hfs HBUD].
pose proof (hr_view _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP) as RT.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; left; reflexivity)) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.
pose proof (real_read_cell m (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP)) as RR.
pose proof (stage_shadow _ _ _ _ _ _ _ HP) as ZSH.
destruct (stage_rw_any m) as (sjunk & STG).

destruct (QJjn.rw_cells_CB_cut asegs m RSTAGE (Z.to_nat 65536) sjunk (Z.to_nat cnt) STG ltac:(lia)) as [DST STGH].

d5_enter.
unfold READCALL_A. step. step. step.
step.
apply evt_done.
eapply (aread_cps_A Jx SYS) with (lo := LO) (cnt := cnt) (p := path) (off := Z_to_bv 64 len) (data := data);
[ exact HCK | reflexivity | reflexivity | reflexivity | reflexivity
| exact (proj1 Hfds) | rewrite Hfs; exact FS | lia | exact DST
| rewrite unsigned_lit by lia; exact ST | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact RT | exact RR | exact ZSH | exact MI | rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 cf2. cbv zeta. rewrite !unsigned_lit by lia.
intros MU2 WM2 MI2 ST2 DST2 HN2 FDS2 FSE2.
rewrite (file_read_unguarded data (Z_to_bv 64 len) (Z_to_bv 64 cnt)) in *. unfold word_to_nat in *. rewrite !unsigned_lit in * by lia.
set (bs := firstn (Z.to_nat cnt) (skipn (Z.to_nat len) data)) in *.
assert (LBS : length bs = Nat.min (Z.to_nat cnt) (length data - Z.to_nat len)) by (subst bs; rewrite length_firstn, length_skipn; reflexivity).
set (nb := length bs) in *.
unfold len_word. fold nb.
replace (Z_to_bv 64 len + Z_to_bv 64 (Z.of_nat nb))%bv with (Z_to_bv 64 (len + Z.of_nat nb) : word)
by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite <- Zplus_mod; reflexivity).

replace (Z_to_bv 64 len + len_word bs)%bv with (Z_to_bv 64 (len + Z.of_nat nb) : word) in FDS2
by (unfold len_word; fold nb; apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite <- Zplus_mod; reflexivity).
assert (HP26 : HEAPA6 A [(buf, cap)] LM0 [] B m2 cf2).
{ eapply (QZsi.heapA_cfg_next A4L H6); [| exact HN2].
eapply heapA_munch6; [exact HP6 | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold cwin; cbn [fst snd].
- split; [lia | left; lia].
- split; [lia | right; left; intros a Ha; unfold cs_wide, RSTAGE in *; lia]. }
pose proof (hr_view _ _ _ _ _ _ _ HP26) as HP2.
assert (DM2 : drvA_memS argv USP m2).
{ eapply drvA_memS_munch; [exact DM | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold dwin; cbn [fst snd]; [split; [lia | left; lia] | split; [lia | right; left; lia]]. }
assert (ERR2 : rw_cells asegs m2 (A_TP - 164) [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP, RSTAGE. repeat split; lia. }
assert (FR2 : rw_cells asegs m2 SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. unfold RSTAGE. repeat split; lia. }
assert (BLK2 : rw_cells asegs m2 buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk]).
{ eapply rw_cells_transport; [exact BLK | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold RSTAGE. repeat split; lia. }
pose proof (cnext_ck _ Jx _ _ HN2) as HCK2.
clear MU2 WM2 DST ST FR BLK ERR HP HCK MI RT RR ZSH STGH DM.
d5_reenter A.
replace (ret_pc (Z_to_bv 64 595680)) with (Z_to_bv 64 595680 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
step. step.
assert (Hnb : Z.of_nat nb <= cnt /\ len + Z.of_nat nb <= Z.of_nat (length data) /\ (nb = 0%nat \/ Z.of_nat nb = cnt \/ len + Z.of_nat nb = Z.of_nat (length data))) by (subst nb; rewrite LBS; lia).
destruct (Nat.eq_dec nb 0) as [NB0|NBP].
-
if_falsex. step. step.
apply evt_done.
eapply (close_cps_A Jx SYS) with (lo := LO);
[ exact HCK2 | reflexivity | rewrite FDS2; apply Qn1e.fd_lookup_insert_eq
| rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI2
| rewrite unsigned_lit by lia; reflexivity | ].
intros b1 b2 b3 b4 b5 b6 b7 m3 cf3. rewrite !unsigned_lit by lia. intros MU3 WM3 MI3 ST3 HN3 FDS3 FSE3.
assert (LEND' : len = Z.of_nat (length data)) by lia.
unfold HDRPT_A in HDR.
replace (ret_pc (Z_to_bv 64 595700)) with (Z_to_bv 64 595700 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
subst len.
lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj5_back A4L J _ A T c ms _ _); [gp5_solve|] end.
apply (HDR cap buf m3 cf3 A B); [| exact FRM].
constructor.
+ eapply drvA_memS_munch; [exact DM2 | exact MU3 | exact WM3 | exact MI3 |]. constructor; [| constructor]. unfold dwin; cbn [fst snd]. split; [lia | left; lia].
+ eapply (QZsi.heapA_cfg_next A4L H6); [| exact HN3].
eapply heapA_munch6; [exact HP26 | exact MU3 | exact WM3 | exact MI3 |]. constructor; [| constructor]. unfold cwin; cbn [fst snd]. split; [lia | left; lia].
+ exact REQ.
+ exact CAPB.
+ lia.
+ exists junk. rewrite firstn_all2 in BLK2 by lia. rewrite Nat2Z.id in BLK2.
eapply rw_cells_transport; [exact BLK2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
+ exists errv. eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia.
+ exact ST3.
+ exists j8, x7, x6, x5, x4, x3, x2, x1, x0. eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia.
+ rewrite FDS3, FDS2. split; [apply fd_lookup_remove_eq|]. intros fd' NE. rewrite Qn1e.fd_lookup_remove_neq by exact NE. rewrite Qn1e.fd_lookup_insert_neq by exact NE. apply (proj2 Hfds). exact NE.
+ rewrite FSE3, FSE2. exact Hfs.
+ destruct HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1). unfold rest_bud. unfold RDQ in HQ1. unfold RDB in HB1. repeat split; lia.
-
if_truex.

apply rw_cells_app2 in BLK2 as [PRE REST]. cbn [csize] in REST. rewrite Z2Nat.id in REST by lia.
destruct (QJjn.rw_cells_CB_cut asegs m2 (buf + len) (Z.to_nat (cap - len)) junk nb REST ltac:(lia)) as [CDST TAIL]. clear REST.
apply rw_cells_app2 in DST2 as [SRC SREST]. cbn [csize] in SREST.
assert (SRCB : bytes_at asegs m2 RSTAGE bs) by (destruct SRC as [[_ BA] _]; cbn [cells_bytes cbytes] in BA; rewrite app_nil_r in BA; exact BA).
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ buf cap HP2 ltac:(apply in_or_app; left; left; reflexivity)) as BAPP. cbn [hl_sb A4L] in BAPP.
assert (Bhi2 : 6574080 <= buf) by lia.
step. step. step.
replace (Z_to_bv 64 buf + Z_to_bv 64 len)%bv with (Z_to_bv 64 (buf + len) : word)
by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite <- Zplus_mod; reflexivity).
step.
assert (APP : 64 < Z.of_nat nb -> app_mem (buf + len) (Z.of_nat nb) /\ app_mem RSTAGE (Z.of_nat nb)).
{ intros Hn64. unfold A_SB in BAPP. replace ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in BAPP by reflexivity.
unfold app_mem, A_SB, A_HMB, RSTAGE. split; [split; [lia|] | split; [lia | left; lia]].
destruct BAPP as [BAPP|BAPP]; [left; lia | right; lia]. }
eapply (imemcpy_sound region_is_poisoned_sound_U) with (d := buf + len) (s := RSTAGE) (n := Z.of_nat nb) (lo := LO);
[ intros _; eapply (unpoisoned_of_blk HIx); [exact HP2 | left; reflexivity | lia | lia | lia]
| intros _; eapply (unpoisoned_of_zero_shadow2 asegs m2 A_SB RSTAGE (Z.of_nat nb) RS_GLO RS_GHI);
[ exact (stage_shadow _ _ _ _ _ _ _ HP2) | unfold RS_GLO, A_SB, RSTAGE; cbn; lia | unfold RS_GHI, A_SB, RSTAGE; Z.div_mod_to_equations; lia
| lia | unfold RSTAGE; lia | unfold RS_GLO, A_SB; lia ]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP2)
| lia | lia | unfold RSTAGE; lia | unfold RSTAGE; lia
| exact APP
| lia | unfold RSTAGE; lia
| reflexivity | reflexivity | reflexivity | lia | unfold RSTAGE; lia
| rewrite Nat2Z.id; exact CDST | exact SRCB | subst nb; rewrite Nat2Z.id; reflexivity
| rewrite unsigned_lit by lia; exact ST2 | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI2 | rewrite unsigned_lit by lia; reflexivity | ].
clear APP. rewrite !unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 MU3 WM3 MI3 CDST3 SRC3 ST3. rewrite Nat2Z.id in CDST3.
assert (HP3 : HEAPA6 A [(buf, cap)] LM0 [] B m3 cf2).
{ eapply heapA_munch6; [exact HP26 | exact MU3 | exact WM3 | exact MI3 |].
constructor; [| constructor; [| constructor]]; unfold cwin; cbn [fst snd].
- split; [lia | right; right; exists buf, cap; split; [left; reflexivity | lia]].
- split; [lia | left; lia]. }
assert (DM3 : drvA_memS argv USP m3).
{ eapply drvA_memS_munch; [exact DM2 | exact MU3 | exact WM3 | exact MI3 |].
constructor; [| constructor; [| constructor]]; unfold dwin; cbn [fst snd]; [split; [lia | right; right; lia] | split; [lia | left; lia]]. }
assert (ERR3 : rw_cells asegs m3 (A_TP - 164) [C4 errv]).
{ eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia. }
assert (FR3 : rw_cells asegs m3 SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia. }
assert (PRE3 : rw_cells asegs m3 buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data)]).
{ eapply rw_cells_transport; [exact PRE | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
assert (TAIL3 : rw_cells asegs m3 (buf + len + Z.of_nat nb) [CB (Z.to_nat (cap - len) - nb) (skipn nb junk)]).
{ eapply rw_cells_transport; [exact TAIL | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }

assert (EBS : firstn (Z.to_nat len) data ++ bs = firstn (Z.to_nat len + nb) data).
{ subst nb bs. rewrite Qn1e.firstn_add. f_equal. rewrite length_firstn, <- List.firstn_firstn, List.firstn_all. reflexivity. }
assert (BLK3 : rw_cells asegs m3 buf [CB (Z.to_nat (len + Z.of_nat nb)) (firstn (Z.to_nat (len + Z.of_nat nb)) data);
CB (Z.to_nat (cap - (len + Z.of_nat nb))) (skipn nb junk)]).
{ pose proof (QJjn.rw_cells_CB_join asegs m3 buf (Z.to_nat len) nb _ bs PRE3 ltac:(rewrite Z2Nat.id by lia; exact CDST3)) as J.
rewrite EBS in J.
apply (proj2 (rw_cells_app2 m3 buf _ _)). cbn [csize]. split.
- replace (Z.to_nat (len + Z.of_nat nb)) with (Z.to_nat len + nb)%nat by lia. exact J.
- replace (buf + Z.of_nat (Z.to_nat (len + Z.of_nat nb))) with (buf + len + Z.of_nat nb) by lia.
replace (Z.to_nat (cap - (len + Z.of_nat nb))) with (Z.to_nat (cap - len) - nb)%nat by lia. exact TAIL3. }
clear PRE PRE3 TAIL TAIL3 CDST3 SRC3 MU3 WM3 SRC SREST SRCB HP2 DM2 ERR2 FR2 MI2 ST2.
replace (ret_pc (Z_to_bv 64 595576)) with (Z_to_bv 64 595576 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step.
evt_done5.
match goal with |- context [Z_to_bv 64 (Z.of_nat nb + len)] => replace (Z.of_nat nb + len) with (len + Z.of_nat nb) by lia | _ => idtac end.
try replace (Z_to_bv 64 (Z.of_nat nb) + Z_to_bv 64 len)%bv with (Z_to_bv 64 (len + Z.of_nat nb) : word)
by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite <- Zplus_mod; f_equal; lia).
apply (NEXT (Z.of_nat nb) ltac:(lia) ltac:(lia) buf m3 cf2 A B); [| exact FRM].
constructor.
+ exact DM3.
+ exact HP3.
+ exact REQ.
+ split; [exact Hcap | exact Hk].
+ lia.
+ eexists. exact BLK3.
+ exists errv. exact ERR3.
+ exact ST3.
+ exists j8, x7, x6, x5, x4, x3, x2, x1, x0. exact FR3.
+ rewrite FDS2. split; [apply Qn1e.fd_lookup_insert_eq|]. intros fd' NE. rewrite Qn1e.fd_lookup_insert_neq by exact NE. apply (proj2 Hfds). exact NE.
+ rewrite FSE2. exact Hfs.
+ exact HBUD.
Qed.

Lemma seg_read : forall k len cap, hdr_stmt -> len < cap ->
(forall n, 1 <= n -> len + n <= cap -> loopk_stmt k (len + n) cap) ->
readpt_stmt k len cap.
Proof.
intros k len cap HDR LT NEXT. unfold readpt_stmt. intros until fc. intros LI FRM.
pose proof (l_cap _ _ _ _ _ _ _ _ LI) as [Hcap Hk]. pose proof (l_len _ _ _ _ _ _ _ _ LI) as [Hlen Hlen2].
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ (hr_view _ _ _ _ _ _ _ (l_heap _ _ _ _ _ _ _ _ LI))) as HCK.
pose proof USPF as (U1 & U2 & U3).
d5_enter.
unfold READPT_A.
step. rewrite (unsigned_lit len) by lia. replace (cap + - len) with (cap - len) by lia. step. step.
rewrite (unsigned_lit cap) by lia.
destruct (Z_lt_dec (cap - len) 65536) as [SM|BG].
- if_truex. evt_done5.
eapply (seg_read2 k len cap (cap - len) HDR LT ltac:(lia) ltac:(lia) NEXT buf m md A B); [exact LI | exact FRM].
- if_falsex. step. evt_done5.
eapply (seg_read2 k len cap 65536 HDR LT ltac:(lia) ltac:(lia) NEXT buf m md A B); [exact LI | exact FRM].
Qed.

Definition REFUSED_A : Z := 0x91840.

Definition leaf_refused_stmt : Prop :=
forall (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config)
(ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
(forall fd', fd' <> Z_to_bv 64 3 -> fd_lookup (m_fds (cfg_model md)) fd' = fd_lookup fds0 fd') -> m_fs (cfg_model md) = fs -> frm0 fc ->
RZAx A md (t_die msg_refused fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 REFUSED_A) fc None m (seg_rom asegs)).
Hypothesis LREF : leaf_refused_stmt.
Hypothesis RESTS : 0 <= BB_REST /\ 0 <= BD_REST.

Lemma seg_loop : forall k len cap,
(len < cap -> readpt_stmt k len cap) ->
(len = cap -> (k < 10)%nat -> 65536 <= cap -> readpt_stmt (S k) len (2 * cap)) ->
loopk_stmt k len cap.
Proof.
intros k len cap RD GROW. unfold loopk_stmt. intros until fc. intros LI FRM.
destruct LI as [DM HP6 REQ [Hcap Hk] [Hlen Hlen2] (junk & BLK) (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) Hfds Hfs HBUD].
pose proof (hr_view _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
d5_enter.
unfold LOOP_A. step.
destruct (Z.eq_dec len cap) as [FULL|NFULL].
2:{
if_falsex. step. step. evt_done5.
apply (RD ltac:(lia) buf m md A B); [| exact FRM].
constructor; auto. exists junk; exact BLK. exists errv; exact ERR. exists j8, x7, x6, x5, x4, x3, x2, x1, x0; exact FR. }

if_truex. subst len. step. rewrite (unsigned_lit cap) by lia. rewrite Z.shiftr_div_pow2 by lia.
destruct (Nat.eq_dec k 10) as [K10|KLT].
{
assert (Hc : cap = 2^26) by (rewrite Hcap, K10; reflexivity).
replace (cap / 2 ^ 26) with 1 by (rewrite Hc; reflexivity).
step. if_truex. evt_done5.
replace (t_body data fs) with (t_die msg_refused fs).
2:{ unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with true; [reflexivity|]. symmetry. apply Z.leb_le. unfold MAX_INPUT. lia. }
pose proof LREF as LR. unfold leaf_refused_stmt, REFUSED_A in LR. eapply LR; [exact DM | exact HP | exact ST | exact (proj2 Hfds) | exact Hfs | exact FRM]. }

assert (Hc : cap <= 2^25).
{ rewrite Hcap. change (2^25) with (65536 * 2^9). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
replace (cap / 2 ^ 26) with 0 by (symmetry; apply Z.div_small; lia).
step. if_falsex. step. rewrite (unsigned_lit cap) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
step. step. evt_done5.
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (BB0 & BD0 & BN0 & BM0 & BQ0). pose proof HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1). unfold RDQ in HQ1. unfold RDB in HB1.
pose proof RESTS6 as (RSa & RSb & RSc & RSd).
assert (AC2 : acostA (cap * 2) = 3 * (cap * 2) + 45101) by (unfold acostA; destruct (Z.leb_spec (cap * 2) 64512); [lia | reflexivity]).
eapply (OBL_MALLOC_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A [(buf, cap)] LM0 [] B (cap * 2) LO errv UWptr HP6);
[ rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | lia
| cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]
| lia | rewrite AC2; lia | cbn [uw_cost]; lia | lia | lia | ].
intros ms' m' md' A' r errv' RS VM ST' PRES ERR' Hr (junk2 & BLK2) HP6' REQ'.
pose proof (hr_view _ _ _ _ _ _ _ HP6') as HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H] in ERR'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
assert (DM' : drvA_memS argv USP m') by (eapply drvA_memS_pres; [exact DM | exact PRES | exact MI']).

assert (BLK' : rw_cells asegs m' buf [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat (cap - cap)) junk]).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact BLK |]. right; right. exists (buf, cap). split; [left; reflexivity|]. cbn. lia. }
apply rw_cells_app2 in BLK' as [SRC _]. cbn [csize] in SRC.
assert (SRCB : bytes_at asegs m' buf (firstn (Z.to_nat cap) data)) by (destruct SRC as [[_ BA] _]; cbn [cells_bytes cbytes] in BA; rewrite app_nil_r in BA; exact BA).
assert (FR' : rw_cells asegs m' SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact FR |]. left. lia. }

destruct (QJjn.rw_cells_CB_cut asegs m' r (Z.to_nat (cap * 2)) junk2 (Z.to_nat cap) BLK2 ltac:(lia)) as [NB1 NB2].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r (cap * 2) buf cap HP' ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity)) as DISJ.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP') as ND. cbn [map blk_addr fst app] in ND.
assert (NE : r <> buf) by (intros E; inversion ND; subst; cbn in *; tauto).
specialize (DISJ NE).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP' ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r (cap * 2) HP' ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Rpos & Rhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP' ltac:(apply in_or_app; left; right; left; reflexivity)) as Bimg.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r (cap * 2) HP' ltac:(apply in_or_app; left; left; reflexivity)) as Rimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg, Rimg. unfold alloc_ceiling in Bhi, Rhi.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ buf cap HP' ltac:(apply in_or_app; left; right; left; reflexivity)) as BAPP.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ r (cap * 2) HP' ltac:(apply in_or_app; left; left; reflexivity)) as RAPP.
cbn [hl_sb A4L] in BAPP, RAPP. unfold A_SB in BAPP, RAPP.
replace ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in BAPP, RAPP by reflexivity.
clear BLK FR ERR ST HP HCK MI.
d5_enter.
replace (ret_pc (Z_to_bv 64 595616)) with (Z_to_bv 64 595616 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
step.
step. if_falsex.
step. step. step.
step.
change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
eapply (imemcpy_sound region_is_poisoned_sound_U) with (d := r) (s := buf) (n := cap) (lo := LO);
[ intros _; eapply (unpoisoned_of_blk HIx); [exact HP' | left; reflexivity | lia | lia | lia]
| intros _; eapply (unpoisoned_of_blk HIx); [exact HP' | right; left; reflexivity | lia | lia | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP')
| lia | lia | lia | lia
| intros _; unfold app_mem, A_SB, A_HMB; split; [split; [lia|]; destruct RAPP as [X|X]; [left; lia | right; lia] | split; [lia|]; destruct BAPP as [X|X]; [left; lia | right; lia]]
| lia | lia
| reflexivity | reflexivity | reflexivity | lia | lia
| exact NB1 | exact SRCB | rewrite length_firstn; lia
| rewrite unsigned_lit by lia; exact ST' | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI' | rewrite unsigned_lit by lia; reflexivity | ].
rewrite !unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 DST2 SRC2 ST2.
assert (HP26 : HEAPA6 A' [(r, cap * 2); (buf, cap)] LM0 [] (QZsi.chargeQ (QZsi.charge B (acostA (cap * 2)) (uw_cost UWptr) 1) (cap * 2 + 8192)) m2 md').
{ eapply heapA_munch6; [exact HP6' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold cwin; cbn [fst snd].
- split; [lia | right; right; exists r, (cap * 2); split; [left; reflexivity | lia]].
- split; [lia | left; lia]. }
assert (DM2 : drvA_memS argv USP m2).
{ eapply drvA_memS_munch; [exact DM' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold dwin; cbn [fst snd]; [split; [lia | right; right; lia] | split; [lia | left; lia]]. }
assert (NB2' : rw_cells asegs m2 (r + Z.of_nat (Z.to_nat cap)) [CB (Z.to_nat (cap * 2) - Z.to_nat cap) (skipn (Z.to_nat cap) junk2)]).
{ eapply rw_cells_transport; [exact NB2 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
assert (FR2 : rw_cells asegs m2 SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact FR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia. }
assert (ERR2 : rw_cells asegs m2 (A_TP - 164) [C4 errv']).
{ eapply rw_cells_transport; [exact ERR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia. }
pose proof (hr_view _ _ _ _ _ _ _ HP26) as HP2.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP2) as HCK2.    clear MU2 WM2 SRC SRCB NB1 NB2 ST' ERR' DM' MI' PRES FR' BLK2.
replace (ret_pc (Z_to_bv 64 595644)) with (Z_to_bv 64 595644 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step.
evt_done5.
eapply (OBL_FREE_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 md' _ A' [(r, cap * 2); (buf, cap)] LM0 [] _ buf LO errv' UWptr HP26);
[ right; exists cap; right; left; reflexivity
| rewrite unsigned_lit by lia; exact ST2 | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR2 | reflexivity | reflexivity
| split; [cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]
| replace (buf =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [uw_cost QZsi.bD QZsi.charge QZsi.chargeQ]; lia | ].
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 PRES3 ERR3 HP36 REQ3.
replace (lb_remove buf [(r, cap * 2); (buf, cap)]) with [(r, cap * 2)] in *
by (cbn [lb_remove blk_addr fst]; rewrite (proj2 (Z.eqb_neq _ _) NE), Z.eqb_refl; reflexivity).
replace (buf =? 0) with false in HP36 by (symmetry; apply Z.eqb_neq; lia). cbn [uw_cost] in HP36.
pose proof (hr_view _ _ _ _ _ _ _ HP36) as HP3.
destruct RS3 as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & ->).
rewrite unsigned_lit in ST3, PRES3 by lia. cbn [hl_tp A4H] in ERR3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3.
assert (DM3 : drvA_memS argv USP m3) by (eapply drvA_memS_pres; [exact DM2 | exact PRES3 | exact MI3]).

assert (NBLK : rw_cells asegs m2 r [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat cap) (skipn (Z.to_nat cap) junk2)]).
{ apply (proj2 (rw_cells_app2 m2 r _ _)). cbn [csize]. split; [exact DST2|].
replace (Z.to_nat (cap * 2) - Z.to_nat cap)%nat with (Z.to_nat cap) in NB2' by lia. exact NB2'. }
assert (NBLK3 : rw_cells asegs m3 r [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat cap) (skipn (Z.to_nat cap) junk2)]).
{ eapply (heap_pres_rw_cells A4H); [exact PRES3 | exact NBLK |]. right; right. exists (r, cap * 2). split; [left; reflexivity|]. cbn. lia. }
assert (FR3 : rw_cells asegs m3 SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply (heap_pres_rw_cells A4H); [exact PRES3 | exact FR2 |]. left. lia. }

replace (ret_pc (Z_to_bv 64 595652)) with (Z_to_bv 64 595652 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold readpt_stmt, READPT_A in GROW.
rewrite (Z.mul_comm cap 2) in *. change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
eapply (GROW eq_refl ltac:(lia) ltac:(lia) r m3 md3 A3); [| exact FRM].
constructor.
+ exact DM3.
+ exact HP36.
+ lia.
+ split; [| lia]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
+ lia.
+ exists (skipn (Z.to_nat cap) junk2). replace (Z.to_nat (2 * cap - cap)) with (Z.to_nat cap) by lia. exact NBLK3.
+ exists errv'. exact ERR3.
+ exact ST3.
+ exists j8, x7, x6, x5, x4, x3, x2, x1, x0. exact FR3.
+ destruct VM3 as (F1 & _). destruct VM as (F0 & _). unfold m_fds in *. rewrite F1, F0. exact Hfds.
+ destruct VM3 as (_ & _ & F1 & _). destruct VM as (_ & _ & F0 & _). unfold m_fs in *. rewrite F1, F0. exact Hfs.
+ unfold rd_bud, RDQ, RDB. cbn [QZsi.bB QZsi.bD QZsi.bN QZsi.bQ QZsi.bM QZsi.charge QZsi.chargeQ uw_cost].
rewrite AC2. rewrite Nat2Z.inj_succ. repeat split; lia.
Qed.

Lemma loop_vacuous : forall k len cap, (10 < k)%nat -> loopk_stmt k len cap.
Proof. intros k len cap Hk. unfold loopk_stmt. intros until fc. intros LI. pose proof (l_cap _ _ _ _ _ _ _ _ LI). lia. Qed.

Lemma loop_inner : hdr_stmt -> forall k cap, (forall len' cap', loopk_stmt (S k) len' cap') ->
forall n len, (Z.to_nat (cap - len) <= n)%nat -> loopk_stmt k len cap.
Proof.
intros HDR k cap QS. induction n as [|n IH]; intros len Hn.
- apply seg_loop.
+ intros LT. unfold readpt_stmt. intros until fc. intros LI. pose proof (l_len _ _ _ _ _ _ _ _ LI). lia.
+ intros -> Hk Hc. apply (seg_read (S k) cap (2 * cap) HDR ltac:(lia)). intros n _ _. apply QS.
- apply seg_loop.
+ intros LT. apply (seg_read k len cap HDR LT). intros n' H1 H2. apply IH. lia.
+ intros -> Hk Hc. apply (seg_read (S k) cap (2 * cap) HDR ltac:(lia)). intros n' _ _. apply QS.
Qed.

Lemma loop_all : hdr_stmt -> loop_stmt.
Proof.
intros HDR.
assert (DOWN : forall j k, (k = 11 - j)%nat -> (j <= 11)%nat -> forall len cap, loopk_stmt k len cap).
{ induction j as [|j IH]; intros k -> Hj len cap.
- apply loop_vacuous. lia.
- apply (loop_inner HDR (11 - S j) cap) with (n := Z.to_nat (cap - len)); [| lia].
intros len' cap'. apply (IH (S (11 - S j))); lia. }
unfold loop_stmt. intros k.
destruct (Nat.le_gt_cases k 10) as [Hk|Hk].
- exact (DOWN (11 - k)%nat k ltac:(lia) ltac:(lia)).
- intros len cap. apply loop_vacuous. exact Hk.
Qed.

Definition read_entry_stmt : Prop :=
forall (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPA6 A [] LM0 [] B m md -> reqA A <= 2^20 ->
(exists errv, rw_cells asegs m (A_TP - 164) [C4 errv]) -> stk asegs m LO SP ->
(exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))) ->
LFDS (m_fds (cfg_model md)) 0 -> m_fs (cfg_model md) = fs ->
RDQ 0 65536 + (65536 + 8192) + BQ_REST <= QZsi.bQ B -> RDB 0 65536 + (3 * 65536 + 45101) + BB_REST <= QZsi.bB B ->
11 + BN_REST <= QZsi.bN B -> BD_REST <= QZsi.bD B -> BD_REST <= 134217728 * QZsi.bM B ->
frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RDENTRY_A) fc None m (seg_rom asegs)).

Lemma read_entry_ok : hdr_stmt -> read_entry_stmt.
Proof.
intros HDR. unfold read_entry_stmt. intros until fc. intros DM HP6 REQ (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) Hfds Hfs HQ1 HB1 HN1 HB2 HM1 FRM.
pose proof (hr_view _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (BB0 & BD0 & BN0 & BM0 & BQ0). unfold RDQ in HQ1. unfold RDB in HB1.
pose proof RESTS6 as (RSa & RSb & RSc & RSd).
assert (AC2 : acostA 65536 = 3 * 65536 + 45101) by reflexivity.
d5_enter.
unfold RDENTRY_A. step. step. step.
evt_done5.
eapply (OBL_MALLOC_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A [] LM0 [] B 65536 LO errv UWptr HP6);
[ rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | lia
| cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]
| lia | rewrite AC2; lia | cbn [uw_cost]; lia | lia | lia | ].
intros ms' m' md' A' r errv' RS VM ST' PRES ERR' Hr (junk & BLK) HP6' REQ'.
pose proof (hr_view _ _ _ _ _ _ _ HP6') as HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H app] in ERR', PRES.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
assert (DM' : drvA_memS argv USP m') by (eapply drvA_memS_pres; [exact DM | exact PRES | exact MI']).
assert (FR' : rw_cells asegs m' SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact FR |]. left. lia. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 65536 HP' ltac:(left; reflexivity)) as (_ & _ & Rpos & Rhi & _).
d5_enter.
replace (ret_pc (Z_to_bv 64 0x9164c)) with (Z_to_bv 64 0x9164c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
do 4 step.
step. if_truex.
step. step.
evt_done5.
eapply (seg_read 0 0 65536 HDR ltac:(lia) (fun n H1 H2 => loop_all HDR 0%nat (0 + n) 65536) r m' md' A'); [| exact FRM].
constructor.
+ exact DM'.
+ exact HP6'.
+ lia.
+ split; [reflexivity | lia].
+ lia.
+ exists junk. replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by lia.
apply (proj2 (rw_cells_app2 m' r _ _)). cbn [csize]. change (Z.to_nat 0) with 0%nat. cbn [firstn Z.of_nat]. rewrite Z.add_0_r. split; [| exact BLK].
unfold rw_cells, ro_cells, cells_at. cbn [cells_wf cells_bytes cells_size cbytes csize app length cell_wf].
rewrite firstn_O. cbn [app length Nat.add Z.of_nat].
split; [split; [split; [reflexivity | exact I] | split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia] | split; [lia|]; split; [lia|]; intros i Hi; lia].
+ exists errv'. exact ERR'.
+ exact ST'.
+ exists j8, x7, x6, x5, x4, x3, x2, x1, x0. exact FR'.
+ destruct VM as (F0 & _). unfold m_fds in *. rewrite F0. exact Hfds.
+ destruct VM as (_ & _ & F0 & _). unfold m_fs in *. rewrite F0. exact Hfs.
+ unfold rd_bud, RDQ, RDB. cbn [QZsi.bB QZsi.bD QZsi.bN QZsi.bQ QZsi.bM QZsi.charge QZsi.chargeQ uw_cost].
rewrite AC2. change (Z.of_nat 0) with 0. repeat split; lia.
Qed.

End DrvReadA.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE QsjA QbVh QS67 QMow QoSL QJBH QCiC QdZp QmAH Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Notation asegs := Q7UD.asegs.

Lemma file_cells_rdn : forall m f flags wend wpos wbase w buf bsz fd mode lbf tail,
QmAH.DT.rw_cells asegs m f (Qu3b.Mq0.file_cells flags wend wpos wbase w buf bsz fd mode lbf tail) ->
forall k n, (k + n <= 232)%nat ->
QsjA.rdn asegs m (Z_to_bv 64 (f + Z.of_nat k)) n = Some (firstn n (skipn k (QMow.cells_bytes (Qu3b.Mq0.file_cells flags wend wpos wbase w buf bsz fd mode lbf tail)))).
Proof.
intros m f flags wend wpos wbase w buf bsz fd mode lbf tail [[WF BA] _] k n Hk.
assert (LT : length tail = 80%nat) by (unfold Qu3b.Mq0.file_cells in WF; cbn [QMow.cells_wf QMow.cell_wf] in WF; tauto).
change (QZDE.bytes_at asegs m f (QMow.cells_bytes (Qu3b.Mq0.file_cells flags wend wpos wbase w buf bsz fd mode lbf tail))) in BA.
apply (QZDE.bytes_at_rdn asegs m f _ k n BA).
unfold Qu3b.Mq0.file_cells. cbn [QMow.cells_bytes QMow.cbytes]. rewrite !length_app. cbn [length]. rewrite LT. exact Hk.
Qed.

Lemma file_cells_clean : forall m f flags wend e w buf bsz fd mode lbf tail,
QmAH.DT.rw_cells asegs m f (Qu3b.Mq0.file_cells flags wend e e w buf bsz fd mode lbf tail) ->
QS67.file_clean m f (Z_to_bv 64 e) (Z_to_bv 64 0).
Proof.
intros m f flags wend e w buf bsz fd mode lbf tail FC.
pose proof (file_cells_rdn m f _ _ _ _ _ _ _ _ _ _ _ FC) as RD. unfold QS67.file_clean.
split; [exact (RD 140%nat 4%nat ltac:(lia))|]. split; [exact (RD 40%nat 8%nat ltac:(lia))|]. split; [exact (RD 56%nat 8%nat ltac:(lia))|].
split; [exact (RD 8%nat 8%nat ltac:(lia))| exact (RD 16%nat 8%nat ltac:(lia))].
Qed.

Lemma rw_cells_eq_on : forall (m m' : word -> option byte) A cs, QmAH.DT.rw_cells asegs m A cs ->
0 <= A -> A + Z.of_nat (QMow.cells_size cs) <= 2^64 ->
(forall x, A <= x < A + Z.of_nat (QMow.cells_size cs) -> m' (QZDE.wa x) = m (QZDE.wa x)) -> QmAH.DT.rw_cells asegs m' A cs.
Proof.
intros m m' A cs RW H0 H1 E.
refine (QJBH.rw_cells_agree asegs (fun x => A <= x < A + Z.of_nat (QMow.cells_size cs)) m m' A cs _ RW (fun a Ha => Ha)).
intros a Ha Pa.
assert (Ea : m' (QCUT.wa a) = m (QCUT.wa a)) by exact (E a Pa).
split; [exact Ea|]. unfold wview. rewrite Ea. exact (fun H => H).
Qed.

Lemma stdoutw_agree : forall m m' k, QdM4.Mq0.STDOUTW_A m k ->
(forall x, (Q2y2.F_STDOUT <= x < Q2y2.F_STDOUT + 232 \/ Q2y2.STDOUT_BUF <= x < Q2y2.STDOUT_BUF + 1024) -> m' (QZDE.wa x) = m (QZDE.wa x)) -> QdM4.Mq0.STDOUTW_A m' k.
Proof.
intros m m' k (flags & mode & tail & bufbytes & FC & FL & BUF & FN & ZL & ACT) E. unfold Q2y2.F_STDOUT, Q2y2.STDOUT_BUF in E.
exists flags, mode, tail, bufbytes. split; [| split; [exact FL| split; [| split; [exact FN| split; [exact ZL| exact ACT]]]]].
- apply (rw_cells_eq_on m m' _ _ FC); [lia | unfold Qu3b.Mq0.file_cells; cbn [QMow.cells_size QMow.csize Nat.add]; lia |].
intros x Hx. apply E. left. unfold Qu3b.Mq0.file_cells in Hx. cbn [QMow.cells_size QMow.csize Nat.add] in Hx. lia.
- apply (rw_cells_eq_on m m' _ _ BUF); [lia | cbn [QMow.cells_size QMow.csize Nat.add]; lia |].
intros x Hx. apply E. right. cbn [QMow.cells_size QMow.csize Nat.add] in Hx. lia.
Qed.

Lemma to_bytes_zl : forall k, QdZp.to_bytes (QdM4.Mq0.zl k) = QBxa.Mq5.zero_lines k.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [QdM4.Mq0.zl QBxa.Mq5.zero_lines]. unfold QdZp.to_bytes in *. cbn [map]. rewrite IH. reflexivity. Qed.
Lemma zl_length : forall k, length (QdM4.Mq0.zl k) = (2 * k)%nat.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [QdM4.Mq0.zl length]. lia. Qed.

Lemma stdoutw_clean : forall m, QdM4.Mq0.STDOUTW_A m 1 -> exists wp rp, QS67.file_clean m 0xea750 wp rp.
Proof.
intros m (flags & mode & tail & bufbytes & FC & _). cbn [QdM4.Mq0.so_w Nat.pred QdM4.Mq0.zl QdZp.so_active QdZp.so_buf QdZp.so_lbf_nl QdZp.so_first] in FC.
change (QCiC.Mq1.zlength (@nil Z)) with 0 in FC. rewrite Z.add_0_r in FC.
exists (Z_to_bv 64 0x6435e8), (Z_to_bv 64 0). exact (file_cells_clean m 0xea750 _ _ _ _ _ _ _ _ _ _ FC).
Qed.

Lemma stdoutw_pending : forall m k can, (2 <= k <= 4)%nat -> QdM4.Mq0.STDOUTW_A m k -> QCKW.Mq2.ssp_cells m can ->
exists wb wp bufp bufsz rp1, QCKW.Mq2.stdout_pending m wb wp bufp bufsz rp1 can (QBxa.Mq5.zero_lines (Nat.pred k)) /\ Q2y2.STDOUT_BUF <= wb /\ wp <= Q2y2.STDOUT_BUF + 1024.
Proof.
intros m k can Hk (flags & mode & tail & bufbytes & FC & _ & BUF & FN & ZL & _) SSP.
cbn [QdM4.Mq0.so_w QdZp.so_active QdZp.so_buf QdZp.so_lbf_nl QdZp.so_first] in FC, FN, ZL.
pose proof (file_cells_rdn m 0xea750 _ _ _ _ _ _ _ _ _ _ _ FC) as RD.
pose proof (zl_length (Nat.pred k)) as LZ.
assert (ZLE : QCiC.Mq1.zlength (QdM4.Mq0.zl (Nat.pred k)) = 2 * Z.of_nat (Nat.pred k)) by (unfold QCiC.Mq1.zlength; rewrite LZ; lia).
rewrite ZLE in *.
exists 0x6435e8, (0x6435e8 + 2 * Z.of_nat (Nat.pred k)), (Z_to_bv 64 0x6435e8), (Z_to_bv 64 1024), (Z_to_bv 64 0).
unfold Q2y2.STDOUT_BUF. split; [| lia].
assert (LP : length (QBxa.Mq5.zero_lines (Nat.pred k)) = (2 * Nat.pred k)%nat) by (rewrite <- to_bytes_zl; unfold QdZp.to_bytes; rewrite length_map; exact LZ).
constructor.
- exact (RD 140%nat 4%nat ltac:(lia)).
- exact (RD 40%nat 8%nat ltac:(lia)).
- exact (RD 56%nat 8%nat ltac:(lia)).
- exact (RD 72%nat 8%nat ltac:(lia)).
- exact (RD 88%nat 8%nat ltac:(lia)).
- exact (RD 96%nat 8%nat ltac:(lia)).
- exact (RD 120%nat 4%nat ltac:(lia)).
- exact (RD 8%nat 8%nat ltac:(lia)).
- exact (RD 16%nat 8%nat ltac:(lia)).
- lia.
- rewrite LP. lia.
- rewrite LP. unfold Uaccess.rw_bytes_max. cbn. lia.
- destruct BUF as [[WF BA] _]. change (QZDE.bytes_at asegs m 0x6435e8 (QMow.cells_bytes [QMow.CB 1024 bufbytes])) in BA.
cbn [QMow.cells_bytes QMow.cbytes] in BA. rewrite app_nil_r in BA.
assert (LB : length bufbytes = 1024%nat) by (cbn [QMow.cells_wf QMow.cell_wf] in WF; tauto).
pose proof (QZDE.bytes_at_rdn asegs m 0x6435e8 bufbytes 0 (length (QBxa.Mq5.zero_lines (Nat.pred k))) BA ltac:(rewrite LB, LP; lia)) as X.
cbn [skipn Z.of_nat] in X. rewrite Z.add_0_r in X. refine (eq_trans X _). f_equal.
change (skipn 0 bufbytes) with bufbytes. rewrite LP, <- LZ, FN. apply to_bytes_zl.
- exact SSP.
Qed.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QBpc.
Import Qhd4.
Import Qwm6.Mq4.

Import QupI QdM4.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac.
Open Scope Z_scope.
Import Q6q3.

Section Ga.
Context {RC__ : Q6q3.RunConsts}.

Lemma img_c4_any : forall A m, img_rw_b A 4 = true -> 0 <= A -> A + 4 <= 2^64 -> exists v, rw_cells asegs m A [C4 v].
Proof.
intros A m Hb HA Hhi. destruct (img_rw_any A 4 m Hb HA ltac:(cbn; lia)) as (junk & RW).
destruct RW as [[WF BA] WR]. cbn in WF. destruct WF as [WF _].
exists (sext 64 (bv_extract 0 32 (le_bytes_to_word junk))). split; [split; [cbn; split; exact I|] | exact WR].
cbn [cells_bytes cbytes app] in BA |- *. rewrite (le4_lw junk WF). exact BA.
Qed.

Theorem lh_globA_of_drv : forall argv USP m, drvA_mem argv USP m -> QsKa.Mqe.lh_globA m.
Proof.
intros argv USP m D. pose proof (dm_pris _ _ _ D) as P. pris_get P 0xec920 0xec980.
split.
- refine (rw_cells_pristine_recast m QsKa.Mqe.GHASHA (le8 (Z_to_bv 64 (fn_lh_char_hash A4F))) _ _ _ _ _ _ _ _).
+ apply (pristine_sub m 0xec920 0xec980); [exact PR | unfold QsKa.Mqe.GHASHA; lia | unfold QsKa.Mqe.GHASHA; cbn; lia].
+ vm_compute. reflexivity.
+ unfold QsKa.Mqe.GHASHA. lia.
+ unfold QsKa.Mqe.GHASHA. cbn. lia.
+ cbn. tauto.
+ cbn [cells_bytes cbytes]. apply app_nil_r.
+ reflexivity.
- apply img_c4_any; [vm_compute; reflexivity | unfold QsKa.Mqe.GSEEDA; lia | unfold QsKa.Mqe.GSEEDA; lia].
Qed.

Theorem jhex_of_drv : forall argv USP m, drvA_mem argv USP m -> bytes_at asegs m 0xec940 (le8 (Z_to_bv 64 0x23380)).
Proof.
intros argv USP m D. pose proof (dm_pris _ _ _ D) as P. pris_get P 0xec920 0xec980.
assert (RW : rw_cells asegs m 0xec940 [C8 (Z_to_bv 64 0x23380)]).
{ refine (rw_cells_pristine_recast m 0xec940 (le8 (Z_to_bv 64 0x23380)) _ _ _ _ _ _ _ _).
+ apply (pristine_sub m 0xec920 0xec980); [exact PR | lia | cbn; lia].
+ vm_compute. reflexivity.
+ lia.
+ cbn. lia.
+ cbn. tauto.
+ cbn [cells_bytes cbytes]. apply app_nil_r.
+ reflexivity. }
destruct RW as [[_ BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
Qed.

Theorem utf8rep_of_drv : forall argv USP m, drvA_mem argv USP m -> bytes_at asegs m 0xec920 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189].
Proof.
intros argv USP m D. pose proof (dm_pris _ _ _ D) as P. pris_get P 0xec920 0xec980.
assert (RW : rw_cells asegs m 0xec920 [CB 3 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189]]).
{ refine (rw_cells_pristine_recast m 0xec920 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189] _ _ _ _ _ _ _ _).
+ apply (pristine_sub m 0xec920 0xec980); [exact PR | lia | cbn; lia].
+ vm_compute. reflexivity.
+ lia.
+ cbn. lia.
+ cbn. tauto.
+ cbn [cells_bytes cbytes]. apply app_nil_r.
+ reflexivity. }
destruct RW as [[_ BA] _]. cbn [cells_bytes cbytes app] in BA. exact BA.
Qed.

Theorem ga_jo_of_drv : forall argv USP m, drvA_mem argv USP m ->
QsKa.Mqe.lh_globA m /\ bytes_at asegs m 0xec940 (le8 (Z_to_bv 64 0x23380)) /\ bytes_at asegs m 0xec920 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189].
Proof. intros argv USP m D. split; [exact (lh_globA_of_drv argv USP m D) | split; [exact (jhex_of_drv argv USP m D) | exact (utf8rep_of_drv argv USP m D)]]. Qed.

End Ga.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1jK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Notation asegs := QbFI.asegs.

Lemma file_cells_rdn : forall m f flags wend wpos wbase w buf bsz fd mode lbf tail,
QmAH.DT.rw_cells asegs m f (Qu3b.Mq4.file_cells flags wend wpos wbase w buf bsz fd mode lbf tail) ->
forall k n, (k + n <= 232)%nat ->
QsjA.rdn asegs m (Z_to_bv 64 (f + Z.of_nat k)) n = Some (firstn n (skipn k (QMow.cells_bytes (Qu3b.Mq4.file_cells flags wend wpos wbase w buf bsz fd mode lbf tail)))).
Proof.
intros m f flags wend wpos wbase w buf bsz fd mode lbf tail [[WF BA] _] k n Hk.
assert (LT : length tail = 80%nat) by (unfold Qu3b.Mq4.file_cells in WF; cbn [QMow.cells_wf QMow.cell_wf] in WF; tauto).
change (QZDE.bytes_at asegs m f (QMow.cells_bytes (Qu3b.Mq4.file_cells flags wend wpos wbase w buf bsz fd mode lbf tail))) in BA.
apply (QZDE.bytes_at_rdn asegs m f _ k n BA).
unfold Qu3b.Mq4.file_cells. cbn [QMow.cells_bytes QMow.cbytes]. rewrite !length_app. cbn [length]. rewrite LT. exact Hk.
Qed.

Lemma file_cells_clean : forall m f flags wend e w buf bsz fd mode lbf tail,
QmAH.DT.rw_cells asegs m f (Qu3b.Mq4.file_cells flags wend e e w buf bsz fd mode lbf tail) ->
Q1jK.file_clean m f (Z_to_bv 64 e) (Z_to_bv 64 0).
Proof.
intros m f flags wend e w buf bsz fd mode lbf tail FC.
pose proof (file_cells_rdn m f _ _ _ _ _ _ _ _ _ _ _ FC) as RD. unfold Q1jK.file_clean.
split; [exact (RD 140%nat 4%nat ltac:(lia))|]. split; [exact (RD 40%nat 8%nat ltac:(lia))|]. split; [exact (RD 56%nat 8%nat ltac:(lia))|].
split; [exact (RD 8%nat 8%nat ltac:(lia))| exact (RD 16%nat 8%nat ltac:(lia))].
Qed.

Lemma rw_cells_eq_on : forall (m m' : word -> option byte) A cs, QmAH.DT.rw_cells asegs m A cs ->
0 <= A -> A + Z.of_nat (QMow.cells_size cs) <= 2^64 ->
(forall x, A <= x < A + Z.of_nat (QMow.cells_size cs) -> m' (QZDE.wa x) = m (QZDE.wa x)) -> QmAH.DT.rw_cells asegs m' A cs.
Proof.
intros m m' A cs RW H0 H1 E.
refine (QJBH.rw_cells_agree asegs (fun x => A <= x < A + Z.of_nat (QMow.cells_size cs)) m m' A cs _ RW (fun a Ha => Ha)).
intros a Ha Pa.
assert (Ea : m' (QCUT.wa a) = m (QCUT.wa a)) by exact (E a Pa).
split; [exact Ea|]. unfold wview. rewrite Ea. exact (fun H => H).
Qed.

Lemma stdoutw_agree : forall m m' k, QdM4.Mq3.STDOUTW_A m k ->
(forall x, (QupI.F_STDOUT <= x < QupI.F_STDOUT + 232 \/ QupI.STDOUT_BUF <= x < QupI.STDOUT_BUF + 1024) -> m' (QZDE.wa x) = m (QZDE.wa x)) -> QdM4.Mq3.STDOUTW_A m' k.
Proof.
intros m m' k (flags & mode & tail & bufbytes & FC & FL & BUF & FN & ZL & ACT) E. unfold QupI.F_STDOUT, QupI.STDOUT_BUF in E.
exists flags, mode, tail, bufbytes. split; [| split; [exact FL| split; [| split; [exact FN| split; [exact ZL| exact ACT]]]]].
- apply (rw_cells_eq_on m m' _ _ FC); [lia | unfold Qu3b.Mq4.file_cells; cbn [QMow.cells_size QMow.csize Nat.add]; lia |].
intros x Hx. apply E. left. unfold Qu3b.Mq4.file_cells in Hx. cbn [QMow.cells_size QMow.csize Nat.add] in Hx. lia.
- apply (rw_cells_eq_on m m' _ _ BUF); [lia | cbn [QMow.cells_size QMow.csize Nat.add]; lia |].
intros x Hx. apply E. right. cbn [QMow.cells_size QMow.csize Nat.add] in Hx. lia.
Qed.

Lemma to_bytes_zl : forall k, QdZp.to_bytes (QdM4.Mq3.zl k) = QBxa.Mq5.zero_lines k.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [QdM4.Mq3.zl QBxa.Mq5.zero_lines]. unfold QdZp.to_bytes in *. cbn [map]. rewrite IH. reflexivity. Qed.
Lemma zl_length : forall k, length (QdM4.Mq3.zl k) = (2 * k)%nat.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [QdM4.Mq3.zl length]. lia. Qed.

Lemma stdoutw_clean : forall m, QdM4.Mq3.STDOUTW_A m 1 -> exists wp rp, Q1jK.file_clean m 0xece30 wp rp.
Proof.
intros m (flags & mode & tail & bufbytes & FC & _). cbn [QdM4.Mq3.so_w Nat.pred QdM4.Mq3.zl QdZp.so_active QdZp.so_buf QdZp.so_lbf_nl QdZp.so_first] in FC.
change (QCiC.Mq1.zlength (@nil Z)) with 0 in FC. rewrite Z.add_0_r in FC.
exists (Z_to_bv 64 0x645ca8), (Z_to_bv 64 0). exact (file_cells_clean m 0xece30 _ _ _ _ _ _ _ _ _ _ FC).
Qed.

Lemma stdoutw_pending : forall m k can, (2 <= k <= 4)%nat -> QdM4.Mq3.STDOUTW_A m k -> QCKW.Mq7.ssp_cells m can ->
exists wb wp bufp bufsz rp1, QCKW.Mq7.stdout_pending m wb wp bufp bufsz rp1 can (QBxa.Mq5.zero_lines (Nat.pred k)) /\ QupI.STDOUT_BUF <= wb /\ wp <= QupI.STDOUT_BUF + 1024.
Proof.
intros m k can Hk (flags & mode & tail & bufbytes & FC & _ & BUF & FN & ZL & _) SSP.
cbn [QdM4.Mq3.so_w QdZp.so_active QdZp.so_buf QdZp.so_lbf_nl QdZp.so_first] in FC, FN, ZL.
pose proof (file_cells_rdn m 0xece30 _ _ _ _ _ _ _ _ _ _ _ FC) as RD.
pose proof (zl_length (Nat.pred k)) as LZ.
assert (ZLE : QCiC.Mq1.zlength (QdM4.Mq3.zl (Nat.pred k)) = 2 * Z.of_nat (Nat.pred k)) by (unfold QCiC.Mq1.zlength; rewrite LZ; lia).
rewrite ZLE in *.
exists 0x645ca8, (0x645ca8 + 2 * Z.of_nat (Nat.pred k)), (Z_to_bv 64 0x645ca8), (Z_to_bv 64 1024), (Z_to_bv 64 0).
unfold QupI.STDOUT_BUF. split; [| lia].
assert (LP : length (QBxa.Mq5.zero_lines (Nat.pred k)) = (2 * Nat.pred k)%nat) by (rewrite <- to_bytes_zl; unfold QdZp.to_bytes; rewrite length_map; exact LZ).
constructor.
- exact (RD 140%nat 4%nat ltac:(lia)).
- exact (RD 40%nat 8%nat ltac:(lia)).
- exact (RD 56%nat 8%nat ltac:(lia)).
- exact (RD 72%nat 8%nat ltac:(lia)).
- exact (RD 88%nat 8%nat ltac:(lia)).
- exact (RD 96%nat 8%nat ltac:(lia)).
- exact (RD 120%nat 4%nat ltac:(lia)).
- exact (RD 8%nat 8%nat ltac:(lia)).
- exact (RD 16%nat 8%nat ltac:(lia)).
- lia.
- rewrite LP. lia.
- rewrite LP. unfold Uaccess.rw_bytes_max. cbn. lia.
- destruct BUF as [[WF BA] _]. change (QZDE.bytes_at asegs m 0x645ca8 (QMow.cells_bytes [QMow.CB 1024 bufbytes])) in BA.
cbn [QMow.cells_bytes QMow.cbytes] in BA. rewrite app_nil_r in BA.
assert (LB : length bufbytes = 1024%nat) by (cbn [QMow.cells_wf QMow.cell_wf] in WF; tauto).
pose proof (QZDE.bytes_at_rdn asegs m 0x645ca8 bufbytes 0 (length (QBxa.Mq5.zero_lines (Nat.pred k))) BA ltac:(rewrite LB, LP; lia)) as X.
cbn [skipn Z.of_nat] in X. rewrite Z.add_0_r in X. refine (eq_trans X _). f_equal.
change (skipn 0 bufbytes) with bufbytes. rewrite LP, <- LZ, FN. apply to_bytes_zl.
- exact SSP.
Qed.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGcC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPra.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfub. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnXa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnXa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qirj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition READPT_A : Z := 0x91a9c.
Definition COPY_A : Z := 0x91a40.
Definition GROW_A : Z := 0x91a64.
Definition HDRPT_A : Z := 0x91acc.
Definition RDENTRY_A : Z := 0x91a18.

Section DrvReadA.
Context {RC__ : Q6q3.RunConsts}.

Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation HEAPA6 := (QZsi.HEAPA A4L H6).
Notation bud6 := QZsi.bud.

Lemma hr_view : forall A LB LM FR (B : bud6) m md, HEAPA6 A LB LM FR B m md -> HEAPAx A LB LM FR (Bud 0 0 0) m md.
Proof.
intros A LB LM FR B m md HP. eapply (heapa5_enter A4L H6); [exact HP|].
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP) as (Q1 & Q2 & Q3 & Q4 & Q5).
unfold blink. cbn [bB bD bM]. lia.
Qed.
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.
Ltac d5_reenter A := lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj_evt J T c ms _); change (evt asegs (AJe A4L J A T c) ms) end.

Variable reqA : ASA A4L HIx -> Z.
Hypothesis OBL_MALLOC_N6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (n lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) ra u ->
1 <= QZsi.bN B -> acostA n <= QZsi.bB B -> uw_cost u <= QZsi.bD B -> n + 8192 <= QZsi.bQ B -> reqA A + n <= 2^31 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]) ->
HEAPA6 A' ((r, n) :: LB) LM FR (QZsi.chargeQ (QZsi.charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' md' ->
reqA A' <= reqA A + n ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_FREE_N6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (p lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
(if Z.eqb p 0 then 0 else uw_cost u) <= QZsi.bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPA6 A' (lb_remove p LB) LM FR (QZsi.charge B 0 (if Z.eqb p 0 then 0 else uw_cost u) 0) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).

Definition cs_wide (a : Z) : Prop :=
(0xec920 <= a < 0xeeb00)
\/ (0xeeb08 <= a < 0xeeb58) \/ (0x184058 <= a < 0x184068) \/ (0x614800 <= a < 0x625450)
\/ (0x625450 <= a < 0x646940 /\ ~ (0x62547c <= a < 0x625480) /\ ~ (0x625510 <= a < 0x625518) /\ ~ (0x6254c8 <= a < 0x6254d0) /\ ~ (0x625518 <= a < 0x625558)
/\ ~ (0x645560 <= a < 0x645568) /\ ~ (0x6457b0 <= a < 0x645818) /\ ~ (0x6458a0 <= a < 0x645c48)).
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.

Variables (argv : list (list byte)) (USP LO : Z) (path data : list byte) (fs : Fs.Fs) (LM0 : list blk).
Variables (fds0 : list (word * FdEntry)).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis FS : fs_lookup fs path = Some data.
Hypothesis LEND : Z.of_nat (length data) < 2^40.
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Definition LFDS (fds : list (word * FdEntry)) (len : Z) : Prop :=
fd_lookup fds (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 len)) /\
forall fd', fd' <> Z_to_bv 64 3 -> fd_lookup fds fd' = fd_lookup fds0 fd'.
Definition CFDS (fds : list (word * FdEntry)) : Prop :=
fd_lookup fds (Z_to_bv 64 3) = None /\ forall fd', fd' <> Z_to_bv 64 3 -> fd_lookup fds fd' = fd_lookup fds0 fd'.

Definition main_frame (j8 : list byte) (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition RD_NEED (k : nat) (cap : Z) : Z := 2^31 - 32 * cap + (10 - Z.of_nat k) * 1024.

Definition RDQ (k : nat) (cap : Z) : Z := 134217728 - 2 * cap + (10 - Z.of_nat k) * 8192.
Definition RDB (k : nat) (cap : Z) : Z := 3 * (134217728 - 2 * cap) + (10 - Z.of_nat k) * 45101.

Variables (BB_REST BD_REST : Z).
Variables (BQ_REST BN_REST : Z).
Definition rest_bud (B : bud6) : Prop :=
BQ_REST <= QZsi.bQ B /\ BB_REST <= QZsi.bB B /\ BN_REST <= QZsi.bN B /\ BD_REST <= QZsi.bD B
/\ BD_REST <= 134217728 * QZsi.bM B.
Definition rd_bud (k : nat) (cap : Z) (B : bud6) : Prop :=
RDQ k cap + BQ_REST <= QZsi.bQ B /\ RDB k cap + BB_REST <= QZsi.bB B
/\ (10 - Z.of_nat k) + BN_REST <= QZsi.bN B /\ BD_REST <= QZsi.bD B /\ BD_REST <= 134217728 * QZsi.bM B.

Record LINV (k : nat) (len cap buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) : Prop := MKL {
l_mem  : drvA_memS argv USP m;
l_heap : HEAPA6 A [(buf, cap)] LM0 [] B m md;
l_req  : reqA A <= 2^20 + 2 * cap;
l_cap  : cap = 65536 * 2 ^ Z.of_nat k /\ (k <= 10)%nat;
l_len  : 0 <= len <= cap /\ len <= Z.of_nat (length data);
l_blk  : exists junk, rw_cells asegs m buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk];
l_errno: exists errv, rw_cells asegs m (A_TP - 164) [C4 errv];
l_stk  : stk asegs m LO SP;
l_frame: exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN));
l_fds  : LFDS (m_fds (cfg_model md)) len;
l_fs   : m_fs (cfg_model md) = fs;
l_bud  : rd_bud k cap B
}.

Hypothesis OBL_CLIENT_FRAME : forall A LB LM FR B m m' md, HEAPAx A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPAx A LB LM FR B m' md.

Definition cwin (LB : list blk) (iv : Z * Z) : Prop :=
fst iv <= snd iv /\
( alloc_ceiling <= fst iv
\/ (forall a, fst iv <= a < snd iv -> cs_wide a)
\/ (exists b n, In (b, n) LB /\ b <= fst iv /\ snd iv <= b + n) ).

Hypothesis OBL_CLIENT_FRAME6 : forall A LB LM FR (B : bud6) m m' md, HEAPA6 A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPA6 A LB LM FR B m' md.
Lemma heapA_munch6 : forall A LB LM (B : bud6) m m' md W,
HEAPA6 A LB LM [] B m md -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (cwin LB) W -> HEAPA6 A LB LM [] B m' md.
Proof.
intros A LB LM B m m' md W HP MU WM MI' FW.
eapply OBL_CLIENT_FRAME6; [exact HP | | intros x Hx; apply WM; exact Hx | exact MI'].
intros a Ha NC _ _. apply MU. rewrite wa_unsigned by lia.
clear - FW NC Ha OBL_CS_WIDE. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [outside fst snd] in *. split; [| apply IH; exact FW].
intros [X1 X2]. apply NC. destruct HC as [H2 | [H2 | (b & n & HIN & H2 & H3)]].
- left. lia.
- right; left. apply OBL_CS_WIDE. apply H2. lia.
- right; right. exists (b, n). split; [apply in_or_app; left; exact HIN | cbn; lia].
Qed.

Lemma stage_shadow : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md ->
forall g, RS_GLO <= g < RS_GHI -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0].
Proof.
intros A LB LM FR B m md HP g Hg. unfold RS_GLO, RS_GHI in Hg.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ g HP ltac:(cbn; lia) ltac:(cbn; lia)) as SH.
cbn [hl_sb hl_reg_globals A4L] in SH.
rewrite (img_shadow_val_outside tokA_reg_globals 0xc2900 0xc4908 g ltac:(vm_compute; reflexivity) ltac:(lia)) in SH. exact SH.
Qed.

Lemma real_read_cell : forall m, rtc_R m -> ro_cells asegs m REAL_READ_CELL [C8 (Z_to_bv 64 READ_SYM)].
Proof. intros m P. unfold REAL_READ_CELL, READ_SYM. rtcR_cell P 0xea078 (le8 (Z_to_bv 64 0xe3934)).
Qed.

Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs,
bytes_at asegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at asegs m' a bs.
Proof.
intros m m' a bs (H1 & H2 & H3) E. split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold mrd in *. rewrite E by lia. apply H3. exact Hi.
Qed.

Lemma bytes_at_prefix : forall (m : word -> option byte) a bs k,
bytes_at asegs m a bs -> (k <= length bs)%nat -> bytes_at asegs m a (firstn k bs).
Proof.
intros m a bs k (H1 & H2 & H3) Hk. split; [exact H1|]. split; [rewrite length_firstn; lia|].
intros i Hi. rewrite length_firstn in Hi. rewrite (H3 i) by lia. rewrite nth_error_firstn.
replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

Definition in_pris (x : Z) : Prop := Exists (fun iv => fst iv <= x < snd iv) PRIS_A.
Definition dcell (x : Z) : Prop :=
USP <= x < USP + 2^22 \/ in_pris x \/ A_TP - 168 <= x < A_TP - 164 \/ T_LOCCELL_A <= x < T_LOCCELL_A + 8 \/ ATEXIT_A <= x < ATEXIT_A + 304
\/ ADFLAG_A <= x < ADFLAG_A + 1.

Lemma argstr_agree : forall m m' p s, argstr m USP p s -> (forall x, USP <= x < USP + 2^22 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) -> argstr m' USP p s.
Proof.
intros m m' p s (B1 & B2 & B3 & B4 & (t & B5 & B6)) EQ. pose proof B4 as [B4a B4b].
assert (LT : Z.of_nat (length t) <= 8 \/ 8 < Z.of_nat (length t)) by lia.
split; [| split; [exact B2 | split; [exact B3 | split; [exact B4 |]]]].
- eapply bytes_at_agree; [exact B1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQ; lia.
- exists (firstn 8 t). split.
+ destruct LT as [LT|LT].
* rewrite firstn_all2 by lia. eapply bytes_at_agree; [exact B5|]. intros x Hx. apply EQ; lia.
* eapply bytes_at_agree; [apply (bytes_at_prefix m _ t 8 B5); lia|]. intros x Hx. rewrite length_firstn in Hx. apply EQ; lia.
+ rewrite length_firstn. lia.
Qed.

Lemma drvA_mem_agree : forall m m', drvA_mem argv USP m ->
(forall x, 0 <= x < 2^64 -> dcell x -> m' (wa x) = m (wa x)) ->
(forall x, dcell (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None) -> mem_inv asegs m' ->
drvA_mem argv USP m'.
Proof.
intros m m' D EQ WM MI'. destruct D as [MI ARGC (p0 & A0 & S0) ARG1 PR (tid & TID & TIDR) LOC (mid & AT & MIDL)].
pose proof USPF as (U1 & U2 & U3).
assert (PH : ax_phase m' = ax_phase m) by (apply ax_phase_agree; apply EQ; [unfold ADFLAG_A; lia | unfold dcell; repeat (lazymatch goal with |- _ \/ _ => right end); unfold ADFLAG_A; lia]).
assert (EQA : forall x, USP <= x < USP + 2^22 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) by (intros; apply EQ; [lia | left; lia]).
assert (ROT : forall A cs, ro_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcell x) -> ro_cells asegs m' A cs).
{ intros A cs [WF BA] HD. split; [exact WF|]. eapply bytes_at_agree; [exact BA|]. intros x Hx.
rewrite cells_bytes_length in Hx by exact WF. destruct BA as (B0 & B1 & _). rewrite cells_bytes_length in B1 by exact WF. apply EQ; [lia | apply HD; lia]. }
assert (RWT : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcell x) -> rw_cells asegs m' A cs).
{ intros A cs [RO (W1 & W2 & W3)] HD. split; [apply ROT; assumption|]. split; [exact W1|]. split; [exact W2|]. intros i Hi.
apply WM; [| apply W3; exact Hi]. rewrite wa_unsigned by lia. apply HD. lia. }
constructor.
- exact MI'.
- exact ARGC.
- exists p0. split; [| eapply argstr_agree; [exact S0 | exact EQA]]. apply ROT; [exact A0|]. cbn. intros; left; lia.
- intros H2. destruct (ARG1 H2) as (p1 & A1 & S1). exists p1. split; [| eapply argstr_agree; [exact S1 | exact EQA]]. apply ROT; [exact A1|]. cbn. intros; left; lia.
- unfold pris_A in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PR _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0.
assert (R : 0 <= lo /\ hi <= 2^64) by (unfold PRIS_A in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN).
apply EQ; [lia|]. right; left. unfold in_pris. apply Exists_exists. exists (lo, hi). split; [exact IN | cbn; lia].
- exists tid. split; [| exact TIDR]. apply ROT; [exact TID|]. cbn. intros; right; right; left; lia.
- apply RWT; [exact LOC|]. cbn. intros; right; right; right; left; lia.
- exists mid. split; [| exact MIDL]. unfold atexit_cells in AT |- *. rewrite PH. apply RWT; [exact AT|]. rewrite (atexit_cellsK_size _ _ MIDL). unfold ATEXIT_A. intros; right; right; right; right; left; unfold ATEXIT_A; lia.
Qed.

Definition dwin (iv : Z * Z) : Prop :=
fst iv <= snd iv /\
( (LO <= fst iv /\ snd iv <= USP - 48) \/ (RSTAGE <= fst iv /\ snd iv <= RSTAGE + 65536) \/ (0x647000 <= fst iv /\ snd iv <= USP - 48) ).

Lemma dcell_cases : forall x, dcell x ->
USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x647000 /\ ~ (RSTAGE <= x < RSTAGE + 65536) /\ cs_wide x).
Proof.
intros x [H|[H|[H|[H|[H|H]]]]].
- left; exact H.
- right. unfold in_pris, PRIS_A in H. unfold cs_wide, RSTAGE.
repeat (apply Exists_cons in H; destruct H as [H|H]; [cbn [fst snd] in H; lia|]). apply Exists_nil in H. destruct H.
- right. unfold A_TP, cs_wide, RSTAGE in *. lia.
- right. unfold T_LOCCELL_A, A_TP, cs_wide, RSTAGE in *. lia.
- right. unfold ATEXIT_A, cs_wide, RSTAGE in *. lia.
- right. unfold ADFLAG_A, cs_wide, RSTAGE in *. lia.
Qed.

Lemma drvA_mem_munch : forall m m' W, drvA_mem argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall dwin W -> drvA_mem argv USP m'.
Proof.
intros m m' W D MU WM MI' FW. pose proof LOF as [L1 L2]. rc_lia_prep. unfold alloc_ceiling in L1.
eapply drvA_mem_agree; [exact D | | intros x _ Hx; apply WM; exact Hx | exact MI'].
intros x Hx HC. apply MU. rewrite wa_unsigned by lia. apply dcell_cases in HC.
clear - FW HC Hx L1 L2 H. unfold dwin, RSTAGE in *. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW].
Qed.

Lemma drvA_mem_pres : forall LBM m m',
drvA_mem argv USP m -> heap_pres A4H LBM SP m m' -> mem_inv asegs m' -> drvA_mem argv USP m'.
Proof.
intros LBM m m' D PRES MI'. pose proof LOF as [L1 L2].
assert (CL : forall x, dcell x -> client_addr A4H LBM SP x).
{ intros x HC. apply dcell_cases in HC. destruct HC as [HC|(HC1 & HC2 & HC3)]; [left; lia | right; left; apply OBL_CS_WIDE; exact HC3]. }
eapply drvA_mem_agree; [exact D | | | exact MI'].
- intros x Hx HC. apply PRES; [lia | apply CL; exact HC].
- intros x HC Hw. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
rewrite <- (Z_to_bv_bv_unsigned x) in Hw |- *. apply (proj2 (PRES (bv_unsigned x) ltac:(cbn in R; lia) (CL _ HC))). exact Hw.
Qed.

Lemma drvA_memS_munch : forall m m' W, drvA_memS argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall dwin W -> drvA_memS argv USP m'.
Proof.
intros m m' W [D S] MU WM MI' FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
split; [eapply drvA_mem_munch; eassumption|].
eapply stdio0_munch; [exact S | exact MU |]. clear - FW L1 L2 H U2 U3. unfold dwin, RSTAGE in *.
induction W as [|[lo hi] W IH]; [constructor|]. apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [fst snd] in *.
constructor; [cbn [fst snd]; lia | apply IH; exact FW].
Qed.

Lemma drvA_memS_pres : forall LBM m m',
drvA_memS argv USP m -> heap_pres A4H LBM SP m m' -> mem_inv asegs m' -> drvA_memS argv USP m'.
Proof.
intros LBM m m' [D S] PRES MI'. split; [eapply drvA_mem_pres; eassumption|].
eapply stdio0_agree; [exact S|]. intros x Hx HI. apply in_stdio0_cases in HI.
apply PRES; [lia|]. right; left. apply OBL_CS_WIDE. unfold cs_wide. lia.
Qed.

Definition LOOP_A : Z := 0x91a58.

Definition readpt_stmt (k : nat) (len cap : Z) : Prop :=
forall (buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A B -> frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READPT_A) fc None m (seg_rom asegs)).

Definition loopk_stmt (k : nat) (len cap : Z) : Prop :=
forall (buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A B -> frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 LOOP_A) fc None m (seg_rom asegs)).
Definition loop_stmt : Prop := forall k len cap, loopk_stmt k len cap.

Record HINV (cap buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) : Prop := MKH {
h_mem  : drvA_memS argv USP m;
h_heap : HEAPA6 A [(buf, cap)] LM0 [] B m md;
h_req  : reqA A <= 2^20 + 2 * cap;
h_cap  : 65536 <= cap <= 2^26;
h_len  : Z.of_nat (length data) < cap;
h_blk  : exists junk, rw_cells asegs m buf [CB (length data) data; CB (Z.to_nat (cap - Z.of_nat (length data))) junk];
h_errno: exists errv, rw_cells asegs m (A_TP - 164) [C4 errv];
h_stk  : stk asegs m LO SP;
h_frame: exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN));
h_fds  : CFDS (m_fds (cfg_model md));
h_fs   : m_fs (cfg_model md) = fs;
h_bud  : rest_bud B
}.
Definition hdr_stmt : Prop :=
forall (cap buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HINV cap buf m md A B -> frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 3) (Z_to_bv 64 cap) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 HDRPT_A) fc None m (seg_rom asegs)).

Lemma cap_bounds : forall k cap, cap = 65536 * 2 ^ Z.of_nat k -> (k <= 10)%nat -> 65536 <= cap <= 2^26.
Proof.
intros k cap -> Hk. pose proof (Z.pow_le_mono_r 2 0 (Z.of_nat k) ltac:(lia) ltac:(lia)) as P1.
pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 10 ltac:(lia) ltac:(lia)) as P2. change (2^0) with 1 in P1. change (2^26) with (65536 * 2^10). nia.
Qed.

Lemma stage_rw_any : forall m, exists junk, rw_cells asegs m RSTAGE [CB (Z.to_nat 65536) junk].
Proof. intros m. apply (img_rw_any RSTAGE (Z.to_nat 65536) m); [vm_compute; reflexivity | unfold RSTAGE; lia | rewrite Z2Nat.id by lia; unfold RSTAGE; lia]. Qed.

Lemma rw_cells_app2 : forall m a c1 c2, rw_cells asegs m a [c1; c2] <-> rw_cells asegs m a [c1] /\ rw_cells asegs m (a + Z.of_nat (csize c1)) [c2].
Proof.
intros m a c1 c2. pose proof (QJjn.rw_cells_app asegs m a [c1] [c2]) as X. cbn [app cells_size Nat.add] in X. rewrite Nat.add_0_r in X. exact X.
Qed.

Lemma fd_lookup_remove_eq : forall fds fd, fd_lookup (fd_remove fds fd) fd = None.
Proof.
intros fds fd. unfold fd_remove. induction fds as [|[k e] r IH]; [reflexivity|]. simpl.
destruct (bv_eqb k fd) eqn:E; simpl; [exact IH | rewrite E; exact IH].
Qed.

Hypothesis RESTS6 : 0 <= BB_REST /\ 0 <= BD_REST /\ 0 <= BQ_REST /\ 0 <= BN_REST.
Definition READCALL_A : Z := 0x91aac.

Lemma seg_read2 : forall k len cap cnt, hdr_stmt ->
len < cap -> 1 <= cnt <= 65536 -> cnt <= cap - len ->
(forall n, 1 <= n -> len + n <= cap -> loopk_stmt k (len + n) cap) ->
forall (buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A B -> frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 (Z_to_bv 64 cnt) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READCALL_A) fc None m (seg_rom asegs)).
Proof.
intros k len cap cnt HDR LT Hcnt Hcnt2 NEXT. intros until fc. intros LI FRM.
destruct LI as [DM HP6 REQ [Hcap Hk] [Hlen Hlen2] (junk & BLK) (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) Hfds Hfs HBUD].
pose proof (hr_view _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP) as RT.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; left; reflexivity)) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.
pose proof (real_read_cell m (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP)) as RR.
pose proof (stage_shadow _ _ _ _ _ _ _ HP) as ZSH.
destruct (stage_rw_any m) as (sjunk & STG).

destruct (QJjn.rw_cells_CB_cut asegs m RSTAGE (Z.to_nat 65536) sjunk (Z.to_nat cnt) STG ltac:(lia)) as [DST STGH].

d5_enter.
unfold READCALL_A. step. step. step.
step.
apply evt_done.
eapply (aread_cps_A Jx SYS) with (lo := LO) (cnt := cnt) (p := path) (off := Z_to_bv 64 len) (data := data);
[ exact HCK | reflexivity | reflexivity | reflexivity | reflexivity
| exact (proj1 Hfds) | rewrite Hfs; exact FS | lia | exact DST
| rewrite unsigned_lit by lia; exact ST | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact RT | exact RR | exact ZSH | exact MI | rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 cf2. cbv zeta. rewrite !unsigned_lit by lia.
intros MU2 WM2 MI2 ST2 DST2 HN2 FDS2 FSE2.
rewrite (file_read_unguarded data (Z_to_bv 64 len) (Z_to_bv 64 cnt)) in *. unfold word_to_nat in *. rewrite !unsigned_lit in * by lia.
set (bs := firstn (Z.to_nat cnt) (skipn (Z.to_nat len) data)) in *.
assert (LBS : length bs = Nat.min (Z.to_nat cnt) (length data - Z.to_nat len)) by (subst bs; rewrite length_firstn, length_skipn; reflexivity).
set (nb := length bs) in *.
unfold len_word. fold nb.
replace (Z_to_bv 64 len + Z_to_bv 64 (Z.of_nat nb))%bv with (Z_to_bv 64 (len + Z.of_nat nb) : word)
by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite <- Zplus_mod; reflexivity).

replace (Z_to_bv 64 len + len_word bs)%bv with (Z_to_bv 64 (len + Z.of_nat nb) : word) in FDS2
by (unfold len_word; fold nb; apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite <- Zplus_mod; reflexivity).
assert (HP26 : HEAPA6 A [(buf, cap)] LM0 [] B m2 cf2).
{ eapply (QZsi.heapA_cfg_next A4L H6); [| exact HN2].
eapply heapA_munch6; [exact HP6 | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold cwin; cbn [fst snd].
- split; [lia | left; lia].
- split; [lia | right; left; intros a Ha; unfold cs_wide, RSTAGE in *; lia]. }
pose proof (hr_view _ _ _ _ _ _ _ HP26) as HP2.
assert (DM2 : drvA_memS argv USP m2).
{ eapply drvA_memS_munch; [exact DM | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold dwin; cbn [fst snd]; [split; [lia | left; lia] | split; [lia | right; left; lia]]. }
assert (ERR2 : rw_cells asegs m2 (A_TP - 164) [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP, RSTAGE. repeat split; lia. }
assert (FR2 : rw_cells asegs m2 SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. unfold RSTAGE. repeat split; lia. }
assert (BLK2 : rw_cells asegs m2 buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk]).
{ eapply rw_cells_transport; [exact BLK | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold RSTAGE. repeat split; lia. }
pose proof (cnext_ck _ Jx _ _ HN2) as HCK2.
clear MU2 WM2 DST ST FR BLK ERR HP HCK MI RT RR ZSH STGH DM.
d5_reenter A.
replace (ret_pc (Z_to_bv 64 596664)) with (Z_to_bv 64 596664 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
step. step.
assert (Hnb : Z.of_nat nb <= cnt /\ len + Z.of_nat nb <= Z.of_nat (length data) /\ (nb = 0%nat \/ Z.of_nat nb = cnt \/ len + Z.of_nat nb = Z.of_nat (length data))) by (subst nb; rewrite LBS; lia).
destruct (Nat.eq_dec nb 0) as [NB0|NBP].
-
if_falsex. step. step.
apply evt_done.
eapply (close_cps_A Jx SYS) with (lo := LO);
[ exact HCK2 | reflexivity | rewrite FDS2; apply Qn1e.fd_lookup_insert_eq
| rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI2
| rewrite unsigned_lit by lia; reflexivity | ].
intros b1 b2 b3 b4 b5 b6 b7 m3 cf3. rewrite !unsigned_lit by lia. intros MU3 WM3 MI3 ST3 HN3 FDS3 FSE3.
assert (LEND' : len = Z.of_nat (length data)) by lia.
unfold HDRPT_A in HDR.
replace (ret_pc (Z_to_bv 64 596684)) with (Z_to_bv 64 596684 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
subst len.
lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj5_back A4L J _ A T c ms _ _); [gp5_solve|] end.
apply (HDR cap buf m3 cf3 A B); [| exact FRM].
constructor.
+ eapply drvA_memS_munch; [exact DM2 | exact MU3 | exact WM3 | exact MI3 |]. constructor; [| constructor]. unfold dwin; cbn [fst snd]. split; [lia | left; lia].
+ eapply (QZsi.heapA_cfg_next A4L H6); [| exact HN3].
eapply heapA_munch6; [exact HP26 | exact MU3 | exact WM3 | exact MI3 |]. constructor; [| constructor]. unfold cwin; cbn [fst snd]. split; [lia | left; lia].
+ exact REQ.
+ exact CAPB.
+ lia.
+ exists junk. rewrite firstn_all2 in BLK2 by lia. rewrite Nat2Z.id in BLK2.
eapply rw_cells_transport; [exact BLK2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
+ exists errv. eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia.
+ exact ST3.
+ exists j8, x7, x6, x5, x4, x3, x2, x1, x0. eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia.
+ rewrite FDS3, FDS2. split; [apply fd_lookup_remove_eq|]. intros fd' NE. rewrite Qn1e.fd_lookup_remove_neq by exact NE. rewrite Qn1e.fd_lookup_insert_neq by exact NE. apply (proj2 Hfds). exact NE.
+ rewrite FSE3, FSE2. exact Hfs.
+ destruct HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1). unfold rest_bud. unfold RDQ in HQ1. unfold RDB in HB1. repeat split; lia.
-
if_truex.

apply rw_cells_app2 in BLK2 as [PRE REST]. cbn [csize] in REST. rewrite Z2Nat.id in REST by lia.
destruct (QJjn.rw_cells_CB_cut asegs m2 (buf + len) (Z.to_nat (cap - len)) junk nb REST ltac:(lia)) as [CDST TAIL]. clear REST.
apply rw_cells_app2 in DST2 as [SRC SREST]. cbn [csize] in SREST.
assert (SRCB : bytes_at asegs m2 RSTAGE bs) by (destruct SRC as [[_ BA] _]; cbn [cells_bytes cbytes] in BA; rewrite app_nil_r in BA; exact BA).
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ buf cap HP2 ltac:(apply in_or_app; left; left; reflexivity)) as BAPP. cbn [hl_sb A4L] in BAPP.
assert (Bhi2 : 6582272 <= buf) by lia.
step. step. step.
replace (Z_to_bv 64 buf + Z_to_bv 64 len)%bv with (Z_to_bv 64 (buf + len) : word)
by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite <- Zplus_mod; reflexivity).
step.
assert (APP : 64 < Z.of_nat nb -> app_mem (buf + len) (Z.of_nat nb) /\ app_mem RSTAGE (Z.of_nat nb)).
{ intros Hn64. unfold A_SB in BAPP. replace ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in BAPP by reflexivity.
unfold app_mem, A_SB, A_HMB, RSTAGE. split; [split; [lia|] | split; [lia | left; lia]].
destruct BAPP as [BAPP|BAPP]; [left; lia | right; lia]. }
eapply (imemcpy_sound region_is_poisoned_sound_U) with (d := buf + len) (s := RSTAGE) (n := Z.of_nat nb) (lo := LO);
[ intros _; eapply (unpoisoned_of_blk HIx); [exact HP2 | left; reflexivity | lia | lia | lia]
| intros _; eapply (unpoisoned_of_zero_shadow2 asegs m2 A_SB RSTAGE (Z.of_nat nb) RS_GLO RS_GHI);
[ exact (stage_shadow _ _ _ _ _ _ _ HP2) | unfold RS_GLO, A_SB, RSTAGE; cbn; lia | unfold RS_GHI, A_SB, RSTAGE; Z.div_mod_to_equations; lia
| lia | unfold RSTAGE; lia | unfold RS_GLO, A_SB; lia ]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP2)
| lia | lia | unfold RSTAGE; lia | unfold RSTAGE; lia
| exact APP
| lia | unfold RSTAGE; lia
| reflexivity | reflexivity | reflexivity | lia | unfold RSTAGE; lia
| rewrite Nat2Z.id; exact CDST | exact SRCB | subst nb; rewrite Nat2Z.id; reflexivity
| rewrite unsigned_lit by lia; exact ST2 | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI2 | rewrite unsigned_lit by lia; reflexivity | ].
clear APP. rewrite !unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 MU3 WM3 MI3 CDST3 SRC3 ST3. rewrite Nat2Z.id in CDST3.
assert (HP3 : HEAPA6 A [(buf, cap)] LM0 [] B m3 cf2).
{ eapply heapA_munch6; [exact HP26 | exact MU3 | exact WM3 | exact MI3 |].
constructor; [| constructor; [| constructor]]; unfold cwin; cbn [fst snd].
- split; [lia | right; right; exists buf, cap; split; [left; reflexivity | lia]].
- split; [lia | left; lia]. }
assert (DM3 : drvA_memS argv USP m3).
{ eapply drvA_memS_munch; [exact DM2 | exact MU3 | exact WM3 | exact MI3 |].
constructor; [| constructor; [| constructor]]; unfold dwin; cbn [fst snd]; [split; [lia | right; right; lia] | split; [lia | left; lia]]. }
assert (ERR3 : rw_cells asegs m3 (A_TP - 164) [C4 errv]).
{ eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia. }
assert (FR3 : rw_cells asegs m3 SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia. }
assert (PRE3 : rw_cells asegs m3 buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data)]).
{ eapply rw_cells_transport; [exact PRE | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
assert (TAIL3 : rw_cells asegs m3 (buf + len + Z.of_nat nb) [CB (Z.to_nat (cap - len) - nb) (skipn nb junk)]).
{ eapply rw_cells_transport; [exact TAIL | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }

assert (EBS : firstn (Z.to_nat len) data ++ bs = firstn (Z.to_nat len + nb) data).
{ subst nb bs. rewrite Qn1e.firstn_add. f_equal. rewrite length_firstn, <- List.firstn_firstn, List.firstn_all. reflexivity. }
assert (BLK3 : rw_cells asegs m3 buf [CB (Z.to_nat (len + Z.of_nat nb)) (firstn (Z.to_nat (len + Z.of_nat nb)) data);
CB (Z.to_nat (cap - (len + Z.of_nat nb))) (skipn nb junk)]).
{ pose proof (QJjn.rw_cells_CB_join asegs m3 buf (Z.to_nat len) nb _ bs PRE3 ltac:(rewrite Z2Nat.id by lia; exact CDST3)) as J.
rewrite EBS in J.
apply (proj2 (rw_cells_app2 m3 buf _ _)). cbn [csize]. split.
- replace (Z.to_nat (len + Z.of_nat nb)) with (Z.to_nat len + nb)%nat by lia. exact J.
- replace (buf + Z.of_nat (Z.to_nat (len + Z.of_nat nb))) with (buf + len + Z.of_nat nb) by lia.
replace (Z.to_nat (cap - (len + Z.of_nat nb))) with (Z.to_nat (cap - len) - nb)%nat by lia. exact TAIL3. }
clear PRE PRE3 TAIL TAIL3 CDST3 SRC3 MU3 WM3 SRC SREST SRCB HP2 DM2 ERR2 FR2 MI2 ST2.
replace (ret_pc (Z_to_bv 64 596560)) with (Z_to_bv 64 596560 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step.
evt_done5.
match goal with |- context [Z_to_bv 64 (Z.of_nat nb + len)] => replace (Z.of_nat nb + len) with (len + Z.of_nat nb) by lia | _ => idtac end.
try replace (Z_to_bv 64 (Z.of_nat nb) + Z_to_bv 64 len)%bv with (Z_to_bv 64 (len + Z.of_nat nb) : word)
by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap; rewrite <- Zplus_mod; f_equal; lia).
apply (NEXT (Z.of_nat nb) ltac:(lia) ltac:(lia) buf m3 cf2 A B); [| exact FRM].
constructor.
+ exact DM3.
+ exact HP3.
+ exact REQ.
+ split; [exact Hcap | exact Hk].
+ lia.
+ eexists. exact BLK3.
+ exists errv. exact ERR3.
+ exact ST3.
+ exists j8, x7, x6, x5, x4, x3, x2, x1, x0. exact FR3.
+ rewrite FDS2. split; [apply Qn1e.fd_lookup_insert_eq|]. intros fd' NE. rewrite Qn1e.fd_lookup_insert_neq by exact NE. apply (proj2 Hfds). exact NE.
+ rewrite FSE2. exact Hfs.
+ exact HBUD.
Qed.

Lemma seg_read : forall k len cap, hdr_stmt -> len < cap ->
(forall n, 1 <= n -> len + n <= cap -> loopk_stmt k (len + n) cap) ->
readpt_stmt k len cap.
Proof.
intros k len cap HDR LT NEXT. unfold readpt_stmt. intros until fc. intros LI FRM.
pose proof (l_cap _ _ _ _ _ _ _ _ LI) as [Hcap Hk]. pose proof (l_len _ _ _ _ _ _ _ _ LI) as [Hlen Hlen2].
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ (hr_view _ _ _ _ _ _ _ (l_heap _ _ _ _ _ _ _ _ LI))) as HCK.
pose proof USPF as (U1 & U2 & U3).
d5_enter.
unfold READPT_A.
step. rewrite (unsigned_lit len) by lia. replace (cap + - len) with (cap - len) by lia. step. step.
rewrite (unsigned_lit cap) by lia.
destruct (Z_lt_dec (cap - len) 65536) as [SM|BG].
- if_truex. evt_done5.
eapply (seg_read2 k len cap (cap - len) HDR LT ltac:(lia) ltac:(lia) NEXT buf m md A B); [exact LI | exact FRM].
- if_falsex. step. evt_done5.
eapply (seg_read2 k len cap 65536 HDR LT ltac:(lia) ltac:(lia) NEXT buf m md A B); [exact LI | exact FRM].
Qed.

Definition REFUSED_A : Z := 0x91c18.

Definition leaf_refused_stmt : Prop :=
forall (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config)
(ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
(forall fd', fd' <> Z_to_bv 64 3 -> fd_lookup (m_fds (cfg_model md)) fd' = fd_lookup fds0 fd') -> m_fs (cfg_model md) = fs -> frm0 fc ->
RZAx A md (t_die msg_refused fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 REFUSED_A) fc None m (seg_rom asegs)).
Hypothesis LREF : leaf_refused_stmt.
Hypothesis RESTS : 0 <= BB_REST /\ 0 <= BD_REST.

Lemma seg_loop : forall k len cap,
(len < cap -> readpt_stmt k len cap) ->
(len = cap -> (k < 10)%nat -> 65536 <= cap -> readpt_stmt (S k) len (2 * cap)) ->
loopk_stmt k len cap.
Proof.
intros k len cap RD GROW. unfold loopk_stmt. intros until fc. intros LI FRM.
destruct LI as [DM HP6 REQ [Hcap Hk] [Hlen Hlen2] (junk & BLK) (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) Hfds Hfs HBUD].
pose proof (hr_view _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
d5_enter.
unfold LOOP_A. step.
destruct (Z.eq_dec len cap) as [FULL|NFULL].
2:{
if_falsex. step. step. evt_done5.
apply (RD ltac:(lia) buf m md A B); [| exact FRM].
constructor; auto. exists junk; exact BLK. exists errv; exact ERR. exists j8, x7, x6, x5, x4, x3, x2, x1, x0; exact FR. }

if_truex. subst len. step. rewrite (unsigned_lit cap) by lia. rewrite Z.shiftr_div_pow2 by lia.
destruct (Nat.eq_dec k 10) as [K10|KLT].
{
assert (Hc : cap = 2^26) by (rewrite Hcap, K10; reflexivity).
replace (cap / 2 ^ 26) with 1 by (rewrite Hc; reflexivity).
step. if_truex. evt_done5.
replace (t_body data fs) with (t_die msg_refused fs).
2:{ unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with true; [reflexivity|]. symmetry. apply Z.leb_le. unfold MAX_INPUT. lia. }
pose proof LREF as LR. unfold leaf_refused_stmt, REFUSED_A in LR. eapply LR; [exact DM | exact HP | exact ST | exact (proj2 Hfds) | exact Hfs | exact FRM]. }

assert (Hc : cap <= 2^25).
{ rewrite Hcap. change (2^25) with (65536 * 2^9). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
replace (cap / 2 ^ 26) with 0 by (symmetry; apply Z.div_small; lia).
step. if_falsex. step. rewrite (unsigned_lit cap) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
step. step. evt_done5.
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (BB0 & BD0 & BN0 & BM0 & BQ0). pose proof HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1). unfold RDQ in HQ1. unfold RDB in HB1.
pose proof RESTS6 as (RSa & RSb & RSc & RSd).
assert (AC2 : acostA (cap * 2) = 3 * (cap * 2) + 45101) by (unfold acostA; destruct (Z.leb_spec (cap * 2) 64512); [lia | reflexivity]).
eapply (OBL_MALLOC_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A [(buf, cap)] LM0 [] B (cap * 2) LO errv UWptr HP6);
[ rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | lia
| cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]
| lia | rewrite AC2; lia | cbn [uw_cost]; lia | lia | lia | ].
intros ms' m' md' A' r errv' RS VM ST' PRES ERR' Hr (junk2 & BLK2) HP6' REQ'.
pose proof (hr_view _ _ _ _ _ _ _ HP6') as HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H] in ERR'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
assert (DM' : drvA_memS argv USP m') by (eapply drvA_memS_pres; [exact DM | exact PRES | exact MI']).

assert (BLK' : rw_cells asegs m' buf [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat (cap - cap)) junk]).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact BLK |]. right; right. exists (buf, cap). split; [left; reflexivity|]. cbn. lia. }
apply rw_cells_app2 in BLK' as [SRC _]. cbn [csize] in SRC.
assert (SRCB : bytes_at asegs m' buf (firstn (Z.to_nat cap) data)) by (destruct SRC as [[_ BA] _]; cbn [cells_bytes cbytes] in BA; rewrite app_nil_r in BA; exact BA).
assert (FR' : rw_cells asegs m' SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact FR |]. left. lia. }

destruct (QJjn.rw_cells_CB_cut asegs m' r (Z.to_nat (cap * 2)) junk2 (Z.to_nat cap) BLK2 ltac:(lia)) as [NB1 NB2].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r (cap * 2) buf cap HP' ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity)) as DISJ.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP') as ND. cbn [map blk_addr fst app] in ND.
assert (NE : r <> buf) by (intros E; inversion ND; subst; cbn in *; tauto).
specialize (DISJ NE).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP' ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r (cap * 2) HP' ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Rpos & Rhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP' ltac:(apply in_or_app; left; right; left; reflexivity)) as Bimg.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r (cap * 2) HP' ltac:(apply in_or_app; left; left; reflexivity)) as Rimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg, Rimg. unfold alloc_ceiling in Bhi, Rhi.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ buf cap HP' ltac:(apply in_or_app; left; right; left; reflexivity)) as BAPP.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ r (cap * 2) HP' ltac:(apply in_or_app; left; left; reflexivity)) as RAPP.
cbn [hl_sb A4L] in BAPP, RAPP. unfold A_SB in BAPP, RAPP.
replace ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in BAPP, RAPP by reflexivity.
clear BLK FR ERR ST HP HCK MI.
d5_enter.
replace (ret_pc (Z_to_bv 64 596600)) with (Z_to_bv 64 596600 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
step.
step. if_falsex.
step. step. step.
step.
change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
eapply (imemcpy_sound region_is_poisoned_sound_U) with (d := r) (s := buf) (n := cap) (lo := LO);
[ intros _; eapply (unpoisoned_of_blk HIx); [exact HP' | left; reflexivity | lia | lia | lia]
| intros _; eapply (unpoisoned_of_blk HIx); [exact HP' | right; left; reflexivity | lia | lia | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP')
| lia | lia | lia | lia
| intros _; unfold app_mem, A_SB, A_HMB; split; [split; [lia|]; destruct RAPP as [X|X]; [left; lia | right; lia] | split; [lia|]; destruct BAPP as [X|X]; [left; lia | right; lia]]
| lia | lia
| reflexivity | reflexivity | reflexivity | lia | lia
| exact NB1 | exact SRCB | rewrite length_firstn; lia
| rewrite unsigned_lit by lia; exact ST' | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI' | rewrite unsigned_lit by lia; reflexivity | ].
rewrite !unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 DST2 SRC2 ST2.
assert (HP26 : HEAPA6 A' [(r, cap * 2); (buf, cap)] LM0 [] (QZsi.chargeQ (QZsi.charge B (acostA (cap * 2)) (uw_cost UWptr) 1) (cap * 2 + 8192)) m2 md').
{ eapply heapA_munch6; [exact HP6' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold cwin; cbn [fst snd].
- split; [lia | right; right; exists r, (cap * 2); split; [left; reflexivity | lia]].
- split; [lia | left; lia]. }
assert (DM2 : drvA_memS argv USP m2).
{ eapply drvA_memS_munch; [exact DM' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold dwin; cbn [fst snd]; [split; [lia | right; right; lia] | split; [lia | left; lia]]. }
assert (NB2' : rw_cells asegs m2 (r + Z.of_nat (Z.to_nat cap)) [CB (Z.to_nat (cap * 2) - Z.to_nat cap) (skipn (Z.to_nat cap) junk2)]).
{ eapply rw_cells_transport; [exact NB2 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
assert (FR2 : rw_cells asegs m2 SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact FR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia. }
assert (ERR2 : rw_cells asegs m2 (A_TP - 164) [C4 errv']).
{ eapply rw_cells_transport; [exact ERR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia. }
pose proof (hr_view _ _ _ _ _ _ _ HP26) as HP2.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP2) as HCK2.    clear MU2 WM2 SRC SRCB NB1 NB2 ST' ERR' DM' MI' PRES FR' BLK2.
replace (ret_pc (Z_to_bv 64 596628)) with (Z_to_bv 64 596628 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step.
evt_done5.
eapply (OBL_FREE_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 md' _ A' [(r, cap * 2); (buf, cap)] LM0 [] _ buf LO errv' UWptr HP26);
[ right; exists cap; right; left; reflexivity
| rewrite unsigned_lit by lia; exact ST2 | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR2 | reflexivity | reflexivity
| split; [cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]
| replace (buf =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [uw_cost QZsi.bD QZsi.charge QZsi.chargeQ]; lia | ].
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 PRES3 ERR3 HP36 REQ3.
replace (lb_remove buf [(r, cap * 2); (buf, cap)]) with [(r, cap * 2)] in *
by (cbn [lb_remove blk_addr fst]; rewrite (proj2 (Z.eqb_neq _ _) NE), Z.eqb_refl; reflexivity).
replace (buf =? 0) with false in HP36 by (symmetry; apply Z.eqb_neq; lia). cbn [uw_cost] in HP36.
pose proof (hr_view _ _ _ _ _ _ _ HP36) as HP3.
destruct RS3 as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & ->).
rewrite unsigned_lit in ST3, PRES3 by lia. cbn [hl_tp A4H] in ERR3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3.
assert (DM3 : drvA_memS argv USP m3) by (eapply drvA_memS_pres; [exact DM2 | exact PRES3 | exact MI3]).

assert (NBLK : rw_cells asegs m2 r [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat cap) (skipn (Z.to_nat cap) junk2)]).
{ apply (proj2 (rw_cells_app2 m2 r _ _)). cbn [csize]. split; [exact DST2|].
replace (Z.to_nat (cap * 2) - Z.to_nat cap)%nat with (Z.to_nat cap) in NB2' by lia. exact NB2'. }
assert (NBLK3 : rw_cells asegs m3 r [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat cap) (skipn (Z.to_nat cap) junk2)]).
{ eapply (heap_pres_rw_cells A4H); [exact PRES3 | exact NBLK |]. right; right. exists (r, cap * 2). split; [left; reflexivity|]. cbn. lia. }
assert (FR3 : rw_cells asegs m3 SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply (heap_pres_rw_cells A4H); [exact PRES3 | exact FR2 |]. left. lia. }

replace (ret_pc (Z_to_bv 64 596636)) with (Z_to_bv 64 596636 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold readpt_stmt, READPT_A in GROW.
rewrite (Z.mul_comm cap 2) in *. change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
eapply (GROW eq_refl ltac:(lia) ltac:(lia) r m3 md3 A3); [| exact FRM].
constructor.
+ exact DM3.
+ exact HP36.
+ lia.
+ split; [| lia]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
+ lia.
+ exists (skipn (Z.to_nat cap) junk2). replace (Z.to_nat (2 * cap - cap)) with (Z.to_nat cap) by lia. exact NBLK3.
+ exists errv'. exact ERR3.
+ exact ST3.
+ exists j8, x7, x6, x5, x4, x3, x2, x1, x0. exact FR3.
+ destruct VM3 as (F1 & _). destruct VM as (F0 & _). unfold m_fds in *. rewrite F1, F0. exact Hfds.
+ destruct VM3 as (_ & _ & F1 & _). destruct VM as (_ & _ & F0 & _). unfold m_fs in *. rewrite F1, F0. exact Hfs.
+ unfold rd_bud, RDQ, RDB. cbn [QZsi.bB QZsi.bD QZsi.bN QZsi.bQ QZsi.bM QZsi.charge QZsi.chargeQ uw_cost].
rewrite AC2. rewrite Nat2Z.inj_succ. repeat split; lia.
Qed.

Lemma loop_vacuous : forall k len cap, (10 < k)%nat -> loopk_stmt k len cap.
Proof. intros k len cap Hk. unfold loopk_stmt. intros until fc. intros LI. pose proof (l_cap _ _ _ _ _ _ _ _ LI). lia. Qed.

Lemma loop_inner : hdr_stmt -> forall k cap, (forall len' cap', loopk_stmt (S k) len' cap') ->
forall n len, (Z.to_nat (cap - len) <= n)%nat -> loopk_stmt k len cap.
Proof.
intros HDR k cap QS. induction n as [|n IH]; intros len Hn.
- apply seg_loop.
+ intros LT. unfold readpt_stmt. intros until fc. intros LI. pose proof (l_len _ _ _ _ _ _ _ _ LI). lia.
+ intros -> Hk Hc. apply (seg_read (S k) cap (2 * cap) HDR ltac:(lia)). intros n _ _. apply QS.
- apply seg_loop.
+ intros LT. apply (seg_read k len cap HDR LT). intros n' H1 H2. apply IH. lia.
+ intros -> Hk Hc. apply (seg_read (S k) cap (2 * cap) HDR ltac:(lia)). intros n' _ _. apply QS.
Qed.

Lemma loop_all : hdr_stmt -> loop_stmt.
Proof.
intros HDR.
assert (DOWN : forall j k, (k = 11 - j)%nat -> (j <= 11)%nat -> forall len cap, loopk_stmt k len cap).
{ induction j as [|j IH]; intros k -> Hj len cap.
- apply loop_vacuous. lia.
- apply (loop_inner HDR (11 - S j) cap) with (n := Z.to_nat (cap - len)); [| lia].
intros len' cap'. apply (IH (S (11 - S j))); lia. }
unfold loop_stmt. intros k.
destruct (Nat.le_gt_cases k 10) as [Hk|Hk].
- exact (DOWN (11 - k)%nat k ltac:(lia) ltac:(lia)).
- intros len cap. apply loop_vacuous. exact Hk.
Qed.

Definition read_entry_stmt : Prop :=
forall (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPA6 A [] LM0 [] B m md -> reqA A <= 2^20 ->
(exists errv, rw_cells asegs m (A_TP - 164) [C4 errv]) -> stk asegs m LO SP ->
(exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))) ->
LFDS (m_fds (cfg_model md)) 0 -> m_fs (cfg_model md) = fs ->
RDQ 0 65536 + (65536 + 8192) + BQ_REST <= QZsi.bQ B -> RDB 0 65536 + (3 * 65536 + 45101) + BB_REST <= QZsi.bB B ->
11 + BN_REST <= QZsi.bN B -> BD_REST <= QZsi.bD B -> BD_REST <= 134217728 * QZsi.bM B ->
frm0 fc ->
RZAx A md (t_body data fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RDENTRY_A) fc None m (seg_rom asegs)).

Lemma read_entry_ok : hdr_stmt -> read_entry_stmt.
Proof.
intros HDR. unfold read_entry_stmt. intros until fc. intros DM HP6 REQ (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) Hfds Hfs HQ1 HB1 HN1 HB2 HM1 FRM.
pose proof (hr_view _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (BB0 & BD0 & BN0 & BM0 & BQ0). unfold RDQ in HQ1. unfold RDB in HB1.
pose proof RESTS6 as (RSa & RSb & RSc & RSd).
assert (AC2 : acostA 65536 = 3 * 65536 + 45101) by reflexivity.
d5_enter.
unfold RDENTRY_A. step. step. step.
evt_done5.
eapply (OBL_MALLOC_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A [] LM0 [] B 65536 LO errv UWptr HP6);
[ rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | lia
| cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]
| lia | rewrite AC2; lia | cbn [uw_cost]; lia | lia | lia | ].
intros ms' m' md' A' r errv' RS VM ST' PRES ERR' Hr (junk & BLK) HP6' REQ'.
pose proof (hr_view _ _ _ _ _ _ _ HP6') as HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H app] in ERR', PRES.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
assert (DM' : drvA_memS argv USP m') by (eapply drvA_memS_pres; [exact DM | exact PRES | exact MI']).
assert (FR' : rw_cells asegs m' SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact FR |]. left. lia. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 65536 HP' ltac:(left; reflexivity)) as (_ & _ & Rpos & Rhi & _).
d5_enter.
replace (ret_pc (Z_to_bv 64 0x91a24)) with (Z_to_bv 64 0x91a24 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
do 4 step.
step. if_truex.
step. step.
evt_done5.
eapply (seg_read 0 0 65536 HDR ltac:(lia) (fun n H1 H2 => loop_all HDR 0%nat (0 + n) 65536) r m' md' A'); [| exact FRM].
constructor.
+ exact DM'.
+ exact HP6'.
+ lia.
+ split; [reflexivity | lia].
+ lia.
+ exists junk. replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by lia.
apply (proj2 (rw_cells_app2 m' r _ _)). cbn [csize]. change (Z.to_nat 0) with 0%nat. cbn [firstn Z.of_nat]. rewrite Z.add_0_r. split; [| exact BLK].
unfold rw_cells, ro_cells, cells_at. cbn [cells_wf cells_bytes cells_size cbytes csize app length cell_wf].
rewrite firstn_O. cbn [app length Nat.add Z.of_nat].
split; [split; [split; [reflexivity | exact I] | split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia] | split; [lia|]; split; [lia|]; intros i Hi; lia].
+ exists errv'. exact ERR'.
+ exact ST'.
+ exists j8, x7, x6, x5, x4, x3, x2, x1, x0. exact FR'.
+ destruct VM as (F0 & _). unfold m_fds in *. rewrite F0. exact Hfds.
+ destruct VM as (_ & _ & F0 & _). unfold m_fs in *. rewrite F0. exact Hfs.
+ unfold rd_bud, RDQ, RDB. cbn [QZsi.bB QZsi.bD QZsi.bN QZsi.bQ QZsi.bM QZsi.charge QZsi.chargeQ uw_cost].
rewrite AC2. change (Z.of_nat 0) with 0. repeat split; lia.
Qed.

End DrvReadA.
