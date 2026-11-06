(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Qhd4 QGcC QCKW Q1jK QsRG Qnhz QBxa QRjH Q9ox QsV0 Qn1e QMz4 QSpR QXup Lib.GwApply QWxq_c1 Lib.SepCache Qe4Y QHnV QCcH QfLs Qsw7 QJjn QBpc Qwm6 QlKV QsKa Qw5U QpNt Qfub Qujl Qirj QupI QnXa QbKA QdM4 QscU QOii QtWm QaDa QSzo Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import Qhd4.
Import QGcC.
Import QCKW.Mq5 QCKW.Mq6 QCKW.Mq7 Q1jK.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH Q9ox.Mq2 QsV0 Qn1e QBxa.Mq5 QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QBpc.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg Qw5U QpNt.Mq8.
Import Qfub Qujl.Mq4 Qirj QupI.Mq1 QnXa.Mq0 QbKA.Mq3 QupI QdM4.Mq4 QdM4.Mq3 QdM4.
Import QscU QOii QtWm QaDa.Mq0 QSzo.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac ivs_lia := repeat (lazymatch goal with |- _ \/ _ => fail | |- _ => constructor end); cbn [fst snd]; lia.

Definition OPENCALL_RET_A : Z := 0x91a10.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Main.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation HEAPA6 := (QZsi.HEAPA A4L H6).
Notation bud6 := QZsi.bud.
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.
Ltac d5_reenter A := lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj_evt J T c ms _); change (evt asegs (AJe A4L J A T c) ms) end.
Ltac from5 A := lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj5_back A4L J _ A T c ms _ _); [gp5_solve|] end.
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
Hypothesis OBL_FREE_NN : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_CLIENT_FRAME : forall A LB LM FR B m m' md, HEAPAx A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPAx A LB LM FR B m' md.
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.
Hypothesis OBL_CLIENT_FRAME6 : forall A LB LM FR (B : bud6) m m' md, HEAPA6 A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPA6 A LB LM FR B m' md.

Variables (argv : list (list byte)) (USP LO : Z) (fs : Fs.Fs) (LM0 : list blk).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis VA : valid_argv argv.

Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.
Hypothesis OBL_GA_of : forall A LB LM FR B m md, drvA_mem argv USP m -> HEAPAx A LB LM FR B m md -> GA m.
Hypothesis TGTB : 0 <= TGT_STACK_A /\ LO + TGT_STACK_A <= USP - 208 /\ 0 <= TGT_BB_A /\ 0 <= TGT_BD_A.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= hiA_bot A4L HIx.
Hypothesis PF1 : emitpf1_stmt Jx PFRT PFLO.
Hypothesis PFK : emitpfk_stmt Jx PFRT PFLO.
Hypothesis FPU : fprintf_u_stmt Jx PFRT PFLO.
Hypothesis FWR : fwrite_stmt Jx PFRT PFLO.
Hypothesis FPS : fprintf_s_stmt Jx PFRT PFLO.

Definition BBR : Z := TR_BB TGT_BB_A + 512.
Definition BDR : Z := TR_BD TGT_BD_A.
Definition BQR : Z := TR_BQ TGT_BB_A.
Definition BNR : Z := TRV_BB TGT_BB_A / 512 + 2.

Hypothesis TGTB6 : TRV_BB TGT_BB_A <= 2^30.

Definition mwin (iv : Z * Z) : Prop :=
fst iv <= snd iv /\ ((LO <= fst iv /\ snd iv <= USP - 48) \/ (A_TP - 164 <= fst iv /\ snd iv <= A_TP - 160)
\/ (0x614810 <= fst iv /\ snd iv <= 0x624810) \/ (0x647000 <= fst iv /\ snd iv <= USP - 48)).

Lemma drvA_mem_munchM : forall m m' W, drvA_mem argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall mwin W -> drvA_mem argv USP m'.
Proof.
intros m m' W D MU WM MI' FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
assert (AG : forall x, 0 <= x < 2^64 -> dcellL USP x \/ (T_LOCCELL_A <= x < T_LOCCELL_A + 8) -> m' (wa x) = m (wa x)).
{ intros x Hx HC. apply MU. rewrite wa_unsigned by lia.
assert (X : USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x647000 /\ ~ (0x614810 <= x < 0x624810) /\ ~ (0x62547c <= x < 0x625480))).
{ destruct HC as [HC|HC]; [pose proof (dcellL_cases USP x HC) as [X|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8)]; [left; lia | right] |].
- split; [lia|]. split; [lia|]. unfold cs_wide in X2. lia.
- right. unfold T_LOCCELL_A, A_TP in HC. lia. }
clear - FW X Hx L1 L2 H U2 U3. unfold mwin, A_TP in FW. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW]. }
eapply (drvA_mem_agreeL argv USP LO [] USPF LOF); [exact D | intros x Hx HC; apply AG; [exact Hx | left; exact HC] | intros x _ Hw; apply WM; exact Hw | | exact MI'].
eapply rw_cells_transport; [exact (dm_loc _ _ _ D) | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. unfold T_LOCCELL_A, A_TP. clear - FW L1 L2 H U2 U3. unfold mwin, A_TP in FW.
induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [disjoint_from fst snd] in *.
split; [lia | apply IH; exact FW].
Qed.

Lemma stdio0_munchM : forall m m' W, stdio0 m -> munch W m m' -> Forall mwin W -> stdio0 m'.
Proof.
intros m m' W S MU FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
eapply stdio0_munch; [exact S | exact MU |]. clear - FW L1 L2 H U2 U3. unfold mwin, A_TP in FW.
induction W as [|[lo hi] W IH]; [constructor|]. apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [fst snd] in *.
constructor; [cbn [fst snd]; lia | apply IH; exact FW].
Qed.

Lemma heapA_munchM6 : forall A LB LM (B : bud6) m m' md W,
HEAPA6 A LB LM [] B m md -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (fun iv => fst iv <= snd iv /\ (alloc_ceiling <= fst iv \/ (A_TP - 164 <= fst iv /\ snd iv <= A_TP - 160)
\/ (forall a, fst iv <= a < snd iv -> cs_wide a)
\/ (exists b n, In (b, n) LB /\ b <= fst iv /\ snd iv <= b + n))) W ->
HEAPA6 A LB LM [] B m' md.
Proof.
intros A LB LM B m m' md W HP MU WM MI' FW.
eapply OBL_CLIENT_FRAME6; [exact HP | | intros x Hx; apply WM; exact Hx | exact MI'].
intros a Ha NC NS _. apply MU. rewrite wa_unsigned by lia.
clear - FW NC NS Ha OBL_CS_WIDE. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [outside fst snd] in *. split; [| apply IH; exact FW].
intros [X1 X2]. destruct HC as [H2 | [H2 | [H2 | (b & n & HIN & H2 & H3)]]].
- apply NC. left. lia.
- apply NS. cbn [hl_scratch A4H]. unfold A_TP in *. lia.
- apply NC. right; left. apply OBL_CS_WIDE. apply H2. lia.
- apply NC. right; right. exists (b, n). split; [apply in_or_app; left; exact HIN | cbn; lia].
Qed.

Lemma errno_rw_any : forall m, exists errv, rw_cells asegs m (A_TP - 164) [C4 errv].
Proof.
intros m. destruct (img_rw_any (A_TP - 164) 4 m ltac:(vm_compute; reflexivity) ltac:(unfold A_TP; lia) ltac:(unfold A_TP; cbn; lia)) as (junk & RW).
destruct RW as [[WF BA] WR]. cbn in WF. destruct WF as [WF _].
exists (sext 64 (bv_extract 0 32 (le_bytes_to_word junk))). split; [split; [cbn; split; exact I|] | exact WR].
cbn [cells_bytes cbytes app] in BA |- *. rewrite (le4_lw junk WF). exact BA.
Qed.
Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
induction p as [|a p IH]; intros [|b q]; cbn [list_byte_eqb]; split; intros HE; try discriminate; try reflexivity.
- apply andb_prop in HE as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b.
f_equal. apply IH. exact H2.
- injection HE as <- <-. apply andb_true_intro. split; [unfold bv_eqb; apply Z.eqb_refl| apply IH; reflexivity].
Qed.
Lemma list_byte_eqb_false : forall p q, list_byte_eqb p q = false -> p <> q.
Proof. intros p q HE E. apply (proj2 (list_byte_eqb_eq p q)) in E. rewrite E in HE. discriminate. Qed.

Lemma t_body_nil : forall data fs', t_body data fs' [].
Proof.
intros data fs'. unfold t_body, t_die. cbv zeta.
repeat (lazymatch goal with
| |- (if ?c then _ else _) [] => destruct c
| |- (match ?n with O => _ | S _ => _ end) [] => destruct n
end); apply t_emit_has_nil.
Qed.

Lemma read_entry_dir : forall (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) (p1w : word)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(2 <= length argv)%nat ->
drvA_memS argv USP m -> HEAPA6 A [] LM0 [] B m md -> reqA A <= 2^20 ->
(exists errv, rw_cells asegs m (A_TP - 164) [C4 errv]) -> stk asegs m LO SP ->
ro_cells asegs m (USP + 16) [C8 p1w] ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 3) = Some FdDir -> fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
65536 + 8192 <= QZsi.bQ B -> 3 * 65536 + 45101 <= QZsi.bB B -> 1 <= QZsi.bN B -> 0 <= QZsi.bD B -> frm0 fc ->
RZAx A md (t_die (msg_read_error (nth 1 argv [])) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7
p1w s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RDENTRY_A) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros ARGC2 [D S0] HP6 REQ (errv & ERR) ST A1 FD3 FDL2 HQ1 HB1 HN1 HB2 FRM.
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
assert (AC2 : acostA 65536 = 3 * 65536 + 45101) by reflexivity.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
d5_enter.
unfold RDENTRY_A. step. step. step. evt_done5.
eapply (OBL_MALLOC_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A [] LM0 [] B 65536 LO errv UWptr HP6);
[ rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | lia
| cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]
| lia | rewrite AC2; lia | cbn [uw_cost]; lia | lia | lia | ].
intros ms' m' md' A' r errv' RS VM ST' PRES ERR' Hr (junk & BLK) HP6' REQ'.
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6') as HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H app] in ERR', PRES.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 65536 HP' ltac:(left; reflexivity)) as (_ & _ & Rpos & Rhi & _). unfold alloc_ceiling in Rhi.
assert (D' : drvA_mem argv USP m') by (eapply (drvA_mem_presT OBL_CS_WIDE argv USP LO [] USPF LOF _ SP m m'); [exact D | exact PRES | exact MI' | lia]).
assert (S0' : stdio0 m').
{ eapply stdio0_agree; [exact S0|]. intros x Hx HI. apply in_stdio0_cases in HI. apply PRES; [lia|]. right; left. apply OBL_CS_WIDE. unfold cs_wide. lia. }
assert (A1' : ro_cells asegs m' (USP + 16) [C8 p1w]).
{ destruct A1 as [WF1 BA1]. split; [exact WF1|]. eapply (heap_pres_bytes_at A4H); [exact PRES | exact BA1 | left; lia]. }
destruct (stage_rw_any USP [] m') as (sjunk & STG).
pose proof (real_read_cell H6 USP LO USPF LOF TOPF m' (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP')) as RR.
unfold A_TP in ERR'.
d5_enter.
replace (ret_pc (Z_to_bv 64 0x91a24)) with (Z_to_bv 64 0x91a24 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
do 4 step.
step. if_truex.
step. step.
step. step. step.
if_falsex. step.
step. step. step.
step.
apply evt_done. change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP') as RT'.
pose proof (vm_only_fds _ _ VM) as FDS'. pose proof (vm_only_fs _ _ VM) as FS'.
eapply (aread_dir_cps_A Jx SYS) with (lo := LO) (cnt := 65536);
[ exact HCK' | reflexivity | reflexivity | reflexivity | reflexivity | rewrite FDS'; exact FD3 | lia
| exact STG | exact ERR'
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | exact RT' | exact RR | exact MI' | rewrite unsigned_lit by lia; reflexivity | ].
rewrite !unsigned_lit by lia. unfold RSTAGE.
intros q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 m2 cf2 MU2 WM2 MI2 ST2 ERR2 HN2 [SIO1 SIO2].
assert (D2 : drvA_mem argv USP m2).
{ eapply drvA_mem_munchM; [exact D' | exact MU2 | exact WM2 | exact MI2 |]. unfold mwin, A_TP. ivs_lia. }
assert (S2 : stdio0 m2) by (eapply stdio0_munchM; [exact S0' | exact MU2 | unfold mwin, A_TP; ivs_lia]).
assert (HP2 : HEAPAx A' [(r, 65536)] LM0 [] (Bud 0 0 0) m2 cf2).
{ eapply (hr_view H6). eapply (QZsi.heapA_cfg_next A4L H6); [| exact HN2]. eapply heapA_munchM6; [exact HP6' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; unfold alloc_ceiling, A_TP;
[ split; [lia | left; lia] | split; [lia | right; right; left; intros; unfold cs_wide; lia] | split; [lia | right; left; lia] ]. }
assert (A1'' : ro_cells asegs m2 (USP + 16) [C8 p1w]).
{ eapply ro_cells_transport; [exact A1' | exact MU2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia. }
d5_reenter A'.
replace (ret_pc (Z_to_bv 64 0x91ab8)) with (Z_to_bv 64 0x91ab8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
match goal with |- context [if ?c then _ else _] => replace c with true by reflexivity | _ => idtac end. cbv iota.
evt_done5. rewrite <- FS', <- SIO2.
eapply (leaf_readerr_ok H6 SYS OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO [] LM0 USPF LOF TOPF PFRT PFLO OBL_PFRT OBL_PFLO FPS);
[split; [exact D2 | exact S2] | exact HP2 | exact ST2 | exact ARGC2 | exact A1'' | rewrite SIO1, FDS'; exact FDL2 | exact FRM].
Qed.
Hypothesis LM0S : Z.of_nat (length LM0) < 8.

Theorem main_ok : forall (m : word -> option byte) (md : config) (A0 : ASA A4L HIx) (B0 : bud6)
(gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_pre argv USP LO m (cfg_model md) -> HEAPA6 A0 [] LM0 [] B0 m md -> reqA A0 <= 2^20 ->
RDQ 0 65536 + (65536 + 8192) + BQR <= QZsi.bQ B0 -> RDB 0 65536 + (3 * 65536 + 45101) + BBR <= QZsi.bB B0 ->
11 + BNR <= QZsi.bN B0 -> BDR <= QZsi.bD B0 -> BDR <= 134217728 * QZsi.bM B0 ->
m_fs (cfg_model md) = fs -> frm0 fc ->
RZAx A0 md (spec argv fs)
(MS (mkR (Z_to_bv 64 RA_MAIN) (Z_to_bv 64 (USP - 48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1
(Z_to_bv 64 (Z.of_nat (length argv))) (Z_to_bv 64 (USP + 8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 MAIN_A) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros PRE HP6 REQ HBQ HBB HBN HBD HBM Hfs FRM.
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
assert (BNR0 : 2 <= BNR /\ 512 + TRV_BB TGT_BB_A <= 512 * BNR) by (unfold BNR; pose proof TGTB as (_ & _ & G3' & _); unfold TRV_BB; Z.div_mod_to_equations; lia).
destruct PRE as [_ _ ST FD1' FD2' [AFD FD3] D S0].
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof TGTB as (G1 & G2 & G3 & G4).
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (dm_argc _ _ _ D) as ARGC.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (errno_rw_any m) as (errv & ERR). unfold A_TP in ERR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(USP - 128, USP - 48)] m) as MU.
d5_enter.
unfold MAIN_A. carve_frame 80%nat ST.
replace (USP + -48 + -80) with (USP + -128) in * by lia.
do 10 step.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (D1 : drvA_mem argv USP mx) by (eapply drvA_mem_munchM; [exact D | exact MU | exact WM | exact MI | unfold mwin; ivs_lia]);
assert (S1 : stdio0 mx) by (eapply stdio0_munchM; [exact S0 | exact MU | unfold mwin; ivs_lia]);
assert (HP1 : HEAPA6 A0 [] LM0 [] B0 mx md) by (eapply heapA_munchM6; [exact HP6 | exact MU | exact WM | exact MI | constructor; [cbn [fst snd]; unfold alloc_ceiling; split; [lia | left; lia] | constructor]])
end.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ (hr_view H6 _ _ _ _ _ _ _ HP1)) as HCK1.    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [ARGC2|ARGCN].
2:{
match goal with |- context [if ?c then _ else _] =>
replace c with true by (symmetry; unfold bv_eqb; cbn -[Z.eqb bv_unsigned Z_to_bv]; rewrite !unsigned_lit by lia;
apply Bool.negb_true_iff; apply Z.eqb_neq; lia) end.
cbv iota. evt_done5.
assert (SPEC : spec argv fs = t_die (msg_usage (nth 0 argv [])) fs).
{ destruct argv as [|a0s [|pth [|x r]]]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in ARGC, ARGCN; try lia; reflexivity. }
rewrite SPEC.
eapply (leaf_usage_ok H6 SYS OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO [] fs LM0 USPF LOF TOPF PFRT PFLO OBL_PFRT OBL_PFLO FPS);
[split; [exact D1 | exact S1] | exact (hr_view H6 _ _ _ _ _ _ _ HP1) | exact ST | do 9 eexists; unfold main_frame; exact FR | exact FD2' | exact Hfs | exact FRM]. }
assert (SHAPE : exists a0s path, argv = [a0s; path]).
{ destruct argv as [|a0s [|path [|x r]]]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in ARGC2; try lia. exists a0s, path. reflexivity. }
destruct SHAPE as (a0s & path & Eargv).
assert (NTH1 : nth 1 argv [] = path) by (rewrite Eargv; reflexivity).

pose proof VA as VA'. rewrite Eargv in VA'.
destruct VA' as (_ & _ & VLEN & VNUL & VTL). apply Forall_cons_iff in VNUL as [_ VNUL]. apply Forall_cons_iff in VNUL as [PNUL _].
cbn [tl] in VTL. apply Forall_cons_iff in VTL as [[PSL PDD] _].

match goal with |- context [if ?c then _ else _] =>
replace c with false by (symmetry; unfold bv_eqb; cbn -[Z.eqb bv_unsigned Z_to_bv]; rewrite !unsigned_lit by lia;
apply Bool.negb_false_iff; apply Z.eqb_eq; lia) end.
cbv iota.
destruct (dm_arg1 _ _ _ D1 ltac:(rewrite Eargv; cbn; lia)) as (p1 & A1 & STR). rewrite NTH1 in STR.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ (hr_view H6 _ _ _ _ _ _ _ HP1)) as (g & CG & CC & _). cbn [hl_got_guard hl_guard hl_tp hla_base A4L A4H] in CG, CC.
apply ro_C8_of_bytes_at in CG. apply ro_C8_of_bytes_at in CC.
step. step. step. step.
apply evt_done. change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
pose proof STR as (SB1 & SB2 & SB3 & [SB4a [SB4b SB4c]] & _).

assert (AFTER : forall m', munch [(bv_unsigned (Z_to_bv 64 SP) - 112, bv_unsigned (Z_to_bv 64 SP)); (A_TP - 164, A_TP - 160)] m0 m' ->
wmono asegs m0 m' -> mem_inv asegs m' ->
drvA_mem argv USP m' /\ stdio0 m' /\ HEAPA6 A0 [] LM0 [] B0 m' md /\ ro_cells asegs m' (USP + 16) [C8 (Z_to_bv 64 p1)]
/\ rw_cells asegs m' SP [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 (firstn 64 (firstn 72 junk)))))))));
C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)]).
{ intros m' MU' WM' MI'. rewrite unsigned_lit in MU' by lia. unfold A_TP in MU'.
split; [| split; [| split; [| split]]].
- eapply drvA_mem_munchM; [exact D1 | exact MU' | exact WM' | exact MI' | unfold mwin, A_TP; ivs_lia].
- eapply stdio0_munchM; [exact S1 | exact MU' | unfold mwin, A_TP; ivs_lia].
- eapply heapA_munchM6; [exact HP1 | exact MU' | exact WM' | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling, A_TP; [split; [lia | left; lia] | split; [lia | right; left; lia]].
- eapply ro_cells_transport; [exact A1 | exact MU' |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
- eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }

assert (KFAIL : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config) (e : Z),
munch [(bv_unsigned (Z_to_bv 64 SP) - 112, bv_unsigned (Z_to_bv 64 SP)); (A_TP - 164, A_TP - 160)] m0 m' -> wmono asegs m0 m' -> mem_inv asegs m' ->
stk asegs m' LO (bv_unsigned (Z_to_bv 64 SP)) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 e)] -> CNEXT Jx md cf' -> same_io md cf' ->
RZAx A0 cf' (t_die (msg_cannot_open path) fs)
(MS (mkR (Z_to_bv 64 OPENCALL_RET_A) (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0' t1' t2' (Z_to_bv 64 2) s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 p1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc (Z_to_bv 64 OPENCALL_RET_A)) fc None m' (seg_rom asegs))).
{ intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' e MU' WM' MI' ST' ERR' HN' [SIO1 SIO2].
destruct (AFTER m' MU' WM' MI') as (D' & S' & HP' & A1' & FR'). rewrite unsigned_lit in ST' by lia.
apply (fun HX => QZsi.heapA_cfg_next A4L H6 _ _ _ _ _ _ _ cf' HX HN') in HP'. apply (hr_view H6) in HP'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.
d5_enter.
replace (ret_pc (Z_to_bv 64 OPENCALL_RET_A)) with (Z_to_bv 64 OPENCALL_RET_A : word) by (symmetry; apply ret_pc_even; [unfold OPENCALL_RET_A; lia| reflexivity]).
unfold OPENCALL_RET_A. step.
match goal with |- context [if ?c then _ else _] => replace c with true by reflexivity end. cbv iota.
evt_done5. rewrite <- Hfs, <- SIO2, <- NTH1.
eapply (leaf_openfail_ok H6 SYS OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO [] LM0 USPF LOF TOPF PFRT PFLO OBL_PFRT OBL_PFLO FPS);
[split; [exact D' | exact S'] | exact HP' | exact ST' | rewrite Eargv; cbn; lia | exact A1' | rewrite SIO1; exact FD2' | exact FRM]. }

assert (PFX : forall k, (k <= length path)%nat -> bytes_at asegs m0 p1 (firstn k path)).
{ intros k Hk. destruct SB1 as (Q1 & Q2 & Q3). rewrite length_app in Q2. cbn [length] in Q2.
split; [exact Q1|]. split; [rewrite length_firstn; lia|].
intros i Hi. rewrite length_firstn in Hi. rewrite (Q3 i) by (rewrite length_app; cbn; lia).
rewrite nth_error_app1 by lia. rewrite nth_error_firstn. replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }

replace (spec argv fs) with (spec [a0s; path] fs) by (rewrite Eargv; reflexivity). unfold spec.
destruct (4096 <=? length path)%nat eqn:TL.
{
apply Nat.leb_le in TL.
eapply (open_toolong_cps_A Jx SYS) with (lo := LO) (pp := p1) (p := path);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| exact SB1 | exact PNUL | exact TL | exact PSL | exact PDD
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' SIO'.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }
apply Nat.leb_gt in TL.
destruct (list_byte_eqb path []) eqn:E0.
{
apply list_byte_eqb_eq in E0.
eapply (open_empty_cps_A Jx SYS) with (lo := LO) (pp := p1);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| rewrite E0 in SB1; exact SB1
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' SIO'.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }
apply list_byte_eqb_false in E0.
assert (NEQ23 : Z_to_bv 64 2 <> Z_to_bv 64 3) by exact neq23.
destruct (list_byte_eqb path dot_path) eqn:ED.
{
apply list_byte_eqb_eq in ED.
eapply (open_dot_cps_A Jx SYS) with (lo := LO) (pp := p1);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| rewrite ED in SB1; exact SB1 | exact AFD | exact FD3
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity
| apply t_emit_has_nil | apply t_emit_has_nil | | ].
{ intros e t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' INe MU' WM' MI' ST' ERR' HN' SIO'.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' FDS' FSE'.
destruct (AFTER m' MU' WM' MI') as (D' & S' & HP' & A1' & FR'). rewrite unsigned_lit in ST' by lia.
assert (HPd : HEAPA6 A0 [] LM0 [] B0 m' cf') by (eapply (QZsi.heapA_cfg_next A4L H6); [exact HP' | exact HN']).
d5_reenter A0.
replace (ret_pc (Z_to_bv 64 596496)) with (Z_to_bv 64 596496 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
match goal with |- context [if ?c then _ else _] => replace c with false by reflexivity end. cbv iota.
step. evt_done5.
unfold t_opened_dir. rewrite <- NTH1. replace fs with (m_fs (cfg_model cf')) by (rewrite FSE'; exact Hfs).
eapply read_entry_dir;
[ rewrite Eargv; cbn; lia | split; [exact D' | exact S'] | exact HPd | exact REQ | exists errv; exact ERR' | exact ST' | exact A1'
| rewrite FDS'; apply Qn1e.fd_lookup_insert_eq
| rewrite FDS', Qn1e.fd_lookup_insert_neq by exact NEQ23; exact FD2'
| unfold RDQ, BQR, TR_BQ, TRV_BB in HBQ; pose proof TGTB as (_ & _ & G3' & _); lia
| unfold RDB, BBR, TR_BB, TRV_BB in HBB; pose proof TGTB as (_ & _ & G3' & _); lia
| lia
| pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (_ & BD0 & _); lia | exact FRM ]. }
apply list_byte_eqb_false in ED.
assert (NDR : path_is_dirref path = false).
{ unfold path_is_dirref. rewrite (Qn1e.path_eqb_neq path Uapi.dot_path ED). cbn [orb]. exact PDD. }
rewrite <- Hfs. destruct (fs_lookup (m_fs (cfg_model md)) path) as [data|] eqn:FS.
2:{
eapply (open_absent_cps_A Jx SYS) with (lo := LO) (pp := p1);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| exact SB1 | exact PNUL | lia | exact E0 | exact PSL | exact NDR | exact FS
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' SIO'. rewrite Hfs.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }

eapply (open_file_cps_A Jx SYS) with (lo := LO) (pp := p1);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| exact SB1 | exact PNUL | lia | exact E0 | exact PSL | exact NDR | exact FS | exact AFD | exact FD3
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity
| apply t_emit_has_nil | unfold t_opened; apply t_body_nil | | ].
{ intros e t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' INe MU' WM' MI' ST' ERR' HN' SIO'. rewrite Hfs.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' FDS' FSE'.
destruct (AFTER m' MU' WM' MI') as (D' & S' & HP' & A1' & FR'). rewrite unsigned_lit in ST' by lia.
assert (HPd : HEAPA6 A0 [] LM0 [] B0 m' cf') by (eapply (QZsi.heapA_cfg_next A4L H6); [exact HP' | exact HN']).
d5_reenter A0.
replace (ret_pc (Z_to_bv 64 596496)) with (Z_to_bv 64 596496 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
match goal with |- context [if ?c then _ else _] => replace c with false by reflexivity end. cbv iota.
step. evt_done5.
unfold t_opened. rewrite Hfs.
assert (RESTS_T : TR_BB TGT_BB_A <= BBR /\ TR_BD TGT_BD_A <= BDR) by (unfold BBR, BDR; lia).
assert (RESTS_H : TR_BB TGT_BB_A + 512 <= BBR /\ TR_BD TGT_BD_A <= BDR /\ 0 <= TR_BB TGT_BB_A /\ 0 <= TR_BD TGT_BD_A) by (unfold BBR, BDR, TR_BB, TR_BD, TRV_BB; lia).
assert (RESTS_R : 0 <= BBR /\ 0 <= BDR) by (unfold BBR, BDR, TR_BB, TR_BD, TRV_BB; lia).
assert (RESTS6_T : TR_BQ TGT_BB_A <= BQR /\ 512 + TRV_BB TGT_BB_A <= 512 * BNR /\ TRV_BB TGT_BB_A <= 2^30) by (unfold BQR; split; [lia| split; [exact (proj2 BNR0)| exact TGTB6]]).
assert (RESTS6_H : 8192 <= BQR /\ 1 <= BNR /\ 0 <= BDR) by (unfold BQR, TR_BQ, TRV_BB, BDR, TR_BD; lia).
assert (RESTS6_R : 0 <= BBR /\ 0 <= BDR /\ 0 <= BQR /\ 0 <= BNR) by (unfold BBR, BDR, BQR, TR_BB, TR_BD, TR_BQ, TRV_BB; lia).
pose proof (trun_ok H6 reqA OBL_MALLOC_N6 OBL_FREE_NN OBL_CLIENT_FRAME OBL_CS_WIDE OBL_CLIENT_FRAME6 argv USP LO data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF FD1'
BBR BDR BQR BNR GA TGT_STACK_A TGT_BB_A TGT_BD_A TGT OBL_GA_of TGTB PFRT PFLO OBL_PFRT OBL_PFLO PF1 PFK RESTS_T RESTS6_T LM0S) as TRUN.
pose proof (leaf_hdr_ok H6 SYS reqA OBL_FREE_NN OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF FD2' PFRT PFLO OBL_PFRT OBL_PFLO FWR) as HLEAF.
pose proof (hdr_ok H6 SYS reqA OBL_FREE_NN OBL_CS_WIDE argv USP LO data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF BBR BDR (TR_BB TGT_BB_A) (TR_BD TGT_BD_A) BQR BNR
RESTS_H RESTS6_H TRUN HLEAF) as HDR.
pose proof (leaf_refused_ok H6 SYS OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF FD2' PFRT PFLO OBL_PFRT OBL_PFLO FPU) as LREF.
pose proof FS as FS0. rewrite Hfs in FS0.
pose proof (read_entry_ok H6 SYS reqA OBL_MALLOC_N6 OBL_FREE_N6 OBL_CS_WIDE argv USP LO path data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF FS0
BBR BDR BQR BNR OBL_CLIENT_FRAME6 RESTS6_R LREF RESTS_R HDR) as RD.
eapply RD;
[ split; [exact D' | exact S'] | exact HPd | exact REQ | exists errv; exact ERR' | exact ST'
| do 9 eexists; unfold main_frame; exact FR'
| unfold LFDS; rewrite FDS'; split; [apply Qn1e.fd_lookup_insert_eq | intros fd' NE; rewrite Qn1e.fd_lookup_insert_neq by exact NE; reflexivity]
| rewrite FSE'; exact Hfs
| exact HBQ | exact HBB | exact HBN | exact HBD | exact HBM
| exact FRM ].
Qed.
End Main.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGcC.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QS67.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QS67.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0TL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qirj.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnXa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnXa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbKA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QscU.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTmr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTmr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtWm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtWm.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaDa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaDa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSzo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSzo.
Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac ivs_lia := repeat (lazymatch goal with |- _ \/ _ => fail | |- _ => constructor end); cbn [fst snd]; lia.

Definition OPENCALL_RET_A : Z := 0x91638.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Main.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation HEAPA6 := (QZsi.HEAPA A4L H6).
Notation bud6 := QZsi.bud.
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.
Ltac d5_reenter A := lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj_evt J T c ms _); change (evt asegs (AJe A4L J A T c) ms) end.
Ltac from5 A := lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj5_back A4L J _ A T c ms _ _); [gp5_solve|] end.
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
Hypothesis OBL_FREE_NN : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_CLIENT_FRAME : forall A LB LM FR B m m' md, HEAPAx A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPAx A LB LM FR B m' md.
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.
Hypothesis OBL_CLIENT_FRAME6 : forall A LB LM FR (B : bud6) m m' md, HEAPA6 A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPA6 A LB LM FR B m' md.

Variables (argv : list (list byte)) (USP LO : Z) (fs : Fs.Fs) (LM0 : list blk).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis VA : valid_argv argv.

Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.
Hypothesis OBL_GA_of : forall A LB LM FR B m md, drvA_mem argv USP m -> HEAPAx A LB LM FR B m md -> GA m.
Hypothesis TGTB : 0 <= TGT_STACK_A /\ LO + TGT_STACK_A <= USP - 208 /\ 0 <= TGT_BB_A /\ 0 <= TGT_BD_A.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= hiA_bot A4L HIx.
Hypothesis PF1 : emitpf1_stmt Jx PFRT PFLO.
Hypothesis PFK : emitpfk_stmt Jx PFRT PFLO.
Hypothesis FPU : fprintf_u_stmt Jx PFRT PFLO.
Hypothesis FWR : fwrite_stmt Jx PFRT PFLO.
Hypothesis FPS : fprintf_s_stmt Jx PFRT PFLO.

Definition BBR : Z := TR_BB TGT_BB_A + 512.
Definition BDR : Z := TR_BD TGT_BD_A.
Definition BQR : Z := TR_BQ TGT_BB_A.
Definition BNR : Z := TRV_BB TGT_BB_A / 512 + 2.

Hypothesis TGTB6 : TRV_BB TGT_BB_A <= 2^30.

Definition mwin (iv : Z * Z) : Prop :=
fst iv <= snd iv /\ ((LO <= fst iv /\ snd iv <= USP - 48) \/ (A_TP - 164 <= fst iv /\ snd iv <= A_TP - 160)
\/ (0x612150 <= fst iv /\ snd iv <= 0x622150) \/ (0x645000 <= fst iv /\ snd iv <= USP - 48)).

Lemma drvA_mem_munchM : forall m m' W, drvA_mem argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall mwin W -> drvA_mem argv USP m'.
Proof.
intros m m' W D MU WM MI' FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
assert (AG : forall x, 0 <= x < 2^64 -> dcellL USP x \/ (T_LOCCELL_A <= x < T_LOCCELL_A + 8) -> m' (wa x) = m (wa x)).
{ intros x Hx HC. apply MU. rewrite wa_unsigned by lia.
assert (X : USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x645000 /\ ~ (0x612150 <= x < 0x622150) /\ ~ (0x622dbc <= x < 0x622dc0))).
{ destruct HC as [HC|HC]; [pose proof (dcellL_cases USP x HC) as [X|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8)]; [left; lia | right] |].
- split; [lia|]. split; [lia|]. unfold cs_wide in X2. lia.
- right. unfold T_LOCCELL_A, A_TP in HC. lia. }
clear - FW X Hx L1 L2 H U2 U3. unfold mwin, A_TP in FW. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW]. }
eapply (drvA_mem_agreeL argv USP LO [] USPF LOF); [exact D | intros x Hx HC; apply AG; [exact Hx | left; exact HC] | intros x _ Hw; apply WM; exact Hw | | exact MI'].
eapply rw_cells_transport; [exact (dm_loc _ _ _ D) | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. unfold T_LOCCELL_A, A_TP. clear - FW L1 L2 H U2 U3. unfold mwin, A_TP in FW.
induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [disjoint_from fst snd] in *.
split; [lia | apply IH; exact FW].
Qed.

Lemma stdio0_munchM : forall m m' W, stdio0 m -> munch W m m' -> Forall mwin W -> stdio0 m'.
Proof.
intros m m' W S MU FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
eapply stdio0_munch; [exact S | exact MU |]. clear - FW L1 L2 H U2 U3. unfold mwin, A_TP in FW.
induction W as [|[lo hi] W IH]; [constructor|]. apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [fst snd] in *.
constructor; [cbn [fst snd]; lia | apply IH; exact FW].
Qed.

Lemma heapA_munchM6 : forall A LB LM (B : bud6) m m' md W,
HEAPA6 A LB LM [] B m md -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (fun iv => fst iv <= snd iv /\ (alloc_ceiling <= fst iv \/ (A_TP - 164 <= fst iv /\ snd iv <= A_TP - 160)
\/ (forall a, fst iv <= a < snd iv -> cs_wide a)
\/ (exists b n, In (b, n) LB /\ b <= fst iv /\ snd iv <= b + n))) W ->
HEAPA6 A LB LM [] B m' md.
Proof.
intros A LB LM B m m' md W HP MU WM MI' FW.
eapply OBL_CLIENT_FRAME6; [exact HP | | intros x Hx; apply WM; exact Hx | exact MI'].
intros a Ha NC NS _. apply MU. rewrite wa_unsigned by lia.
clear - FW NC NS Ha OBL_CS_WIDE. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [outside fst snd] in *. split; [| apply IH; exact FW].
intros [X1 X2]. destruct HC as [H2 | [H2 | [H2 | (b & n & HIN & H2 & H3)]]].
- apply NC. left. lia.
- apply NS. cbn [hl_scratch A4H]. unfold A_TP in *. lia.
- apply NC. right; left. apply OBL_CS_WIDE. apply H2. lia.
- apply NC. right; right. exists (b, n). split; [apply in_or_app; left; exact HIN | cbn; lia].
Qed.

Lemma errno_rw_any : forall m, exists errv, rw_cells asegs m (A_TP - 164) [C4 errv].
Proof.
intros m. destruct (img_rw_any (A_TP - 164) 4 m ltac:(vm_compute; reflexivity) ltac:(unfold A_TP; lia) ltac:(unfold A_TP; cbn; lia)) as (junk & RW).
destruct RW as [[WF BA] WR]. cbn in WF. destruct WF as [WF _].
exists (sext 64 (bv_extract 0 32 (le_bytes_to_word junk))). split; [split; [cbn; split; exact I|] | exact WR].
cbn [cells_bytes cbytes app] in BA |- *. rewrite (le4_lw junk WF). exact BA.
Qed.
Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
induction p as [|a p IH]; intros [|b q]; cbn [list_byte_eqb]; split; intros HE; try discriminate; try reflexivity.
- apply andb_prop in HE as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b.
f_equal. apply IH. exact H2.
- injection HE as <- <-. apply andb_true_intro. split; [unfold bv_eqb; apply Z.eqb_refl| apply IH; reflexivity].
Qed.
Lemma list_byte_eqb_false : forall p q, list_byte_eqb p q = false -> p <> q.
Proof. intros p q HE E. apply (proj2 (list_byte_eqb_eq p q)) in E. rewrite E in HE. discriminate. Qed.

Lemma t_body_nil : forall data fs', t_body data fs' [].
Proof.
intros data fs'. unfold t_body, t_die. cbv zeta.
repeat (lazymatch goal with
| |- (if ?c then _ else _) [] => destruct c
| |- (match ?n with O => _ | S _ => _ end) [] => destruct n
end); apply t_emit_has_nil.
Qed.

Lemma read_entry_dir : forall (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) (p1w : word)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(2 <= length argv)%nat ->
drvA_memS argv USP m -> HEAPA6 A [] LM0 [] B m md -> reqA A <= 2^20 ->
(exists errv, rw_cells asegs m (A_TP - 164) [C4 errv]) -> stk asegs m LO SP ->
ro_cells asegs m (USP + 16) [C8 p1w] ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 3) = Some FdDir -> fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
65536 + 8192 <= QZsi.bQ B -> 3 * 65536 + 45101 <= QZsi.bB B -> 1 <= QZsi.bN B -> 0 <= QZsi.bD B -> frm0 fc ->
RZAx A md (t_die (msg_read_error (nth 1 argv [])) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7
p1w s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RDENTRY_A) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros ARGC2 [D S0] HP6 REQ (errv & ERR) ST A1 FD3 FDL2 HQ1 HB1 HN1 HB2 FRM.
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
assert (AC2 : acostA 65536 = 3 * 65536 + 45101) by reflexivity.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
d5_enter.
unfold RDENTRY_A. step. step. step. evt_done5.
eapply (OBL_MALLOC_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A [] LM0 [] B 65536 LO errv UWptr HP6);
[ rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | lia
| cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]
| lia | rewrite AC2; lia | cbn [uw_cost]; lia | lia | lia | ].
intros ms' m' md' A' r errv' RS VM ST' PRES ERR' Hr (junk & BLK) HP6' REQ'.
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6') as HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H app] in ERR', PRES.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 65536 HP' ltac:(left; reflexivity)) as (_ & _ & Rpos & Rhi & _). unfold alloc_ceiling in Rhi.
assert (D' : drvA_mem argv USP m') by (eapply (drvA_mem_presT OBL_CS_WIDE argv USP LO [] USPF LOF _ SP m m'); [exact D | exact PRES | exact MI' | lia]).
assert (S0' : stdio0 m').
{ eapply stdio0_agree; [exact S0|]. intros x Hx HI. apply in_stdio0_cases in HI. apply PRES; [lia|]. right; left. apply OBL_CS_WIDE. unfold cs_wide. lia. }
assert (A1' : ro_cells asegs m' (USP + 16) [C8 p1w]).
{ destruct A1 as [WF1 BA1]. split; [exact WF1|]. eapply (heap_pres_bytes_at A4H); [exact PRES | exact BA1 | left; lia]. }
destruct (stage_rw_any USP [] m') as (sjunk & STG).
pose proof (real_read_cell H6 USP LO USPF LOF TOPF m' (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP')) as RR.
unfold A_TP in ERR'.
d5_enter.
replace (ret_pc (Z_to_bv 64 0x9164c)) with (Z_to_bv 64 0x9164c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
do 4 step.
step. if_truex.
step. step.
step. step. step.
if_falsex. step.
step. step. step.
step.
apply evt_done. change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP') as RT'.
pose proof (vm_only_fds _ _ VM) as FDS'. pose proof (vm_only_fs _ _ VM) as FS'.
eapply (aread_dir_cps_A Jx SYS) with (lo := LO) (cnt := 65536);
[ exact HCK' | reflexivity | reflexivity | reflexivity | reflexivity | rewrite FDS'; exact FD3 | lia
| exact STG | exact ERR'
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | exact RT' | exact RR | exact MI' | rewrite unsigned_lit by lia; reflexivity | ].
rewrite !unsigned_lit by lia. unfold RSTAGE.
intros q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 m2 cf2 MU2 WM2 MI2 ST2 ERR2 HN2 [SIO1 SIO2].
assert (D2 : drvA_mem argv USP m2).
{ eapply drvA_mem_munchM; [exact D' | exact MU2 | exact WM2 | exact MI2 |]. unfold mwin, A_TP. ivs_lia. }
assert (S2 : stdio0 m2) by (eapply stdio0_munchM; [exact S0' | exact MU2 | unfold mwin, A_TP; ivs_lia]).
assert (HP2 : HEAPAx A' [(r, 65536)] LM0 [] (Bud 0 0 0) m2 cf2).
{ eapply (hr_view H6). eapply (QZsi.heapA_cfg_next A4L H6); [| exact HN2]. eapply heapA_munchM6; [exact HP6' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; unfold alloc_ceiling, A_TP;
[ split; [lia | left; lia] | split; [lia | right; right; left; intros; unfold cs_wide; lia] | split; [lia | right; left; lia] ]. }
assert (A1'' : ro_cells asegs m2 (USP + 16) [C8 p1w]).
{ eapply ro_cells_transport; [exact A1' | exact MU2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia. }
d5_reenter A'.
replace (ret_pc (Z_to_bv 64 0x916e0)) with (Z_to_bv 64 0x916e0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
match goal with |- context [if ?c then _ else _] => replace c with true by reflexivity | _ => idtac end. cbv iota.
evt_done5. rewrite <- FS', <- SIO2.
eapply (leaf_readerr_ok H6 SYS OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO [] LM0 USPF LOF TOPF PFRT PFLO OBL_PFRT OBL_PFLO FPS);
[split; [exact D2 | exact S2] | exact HP2 | exact ST2 | exact ARGC2 | exact A1'' | rewrite SIO1, FDS'; exact FDL2 | exact FRM].
Qed.
Hypothesis LM0S : Z.of_nat (length LM0) < 8.

Theorem main_ok : forall (m : word -> option byte) (md : config) (A0 : ASA A4L HIx) (B0 : bud6)
(gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_pre argv USP LO m (cfg_model md) -> HEAPA6 A0 [] LM0 [] B0 m md -> reqA A0 <= 2^20 ->
RDQ 0 65536 + (65536 + 8192) + BQR <= QZsi.bQ B0 -> RDB 0 65536 + (3 * 65536 + 45101) + BBR <= QZsi.bB B0 ->
11 + BNR <= QZsi.bN B0 -> BDR <= QZsi.bD B0 -> BDR <= 134217728 * QZsi.bM B0 ->
m_fs (cfg_model md) = fs -> frm0 fc ->
RZAx A0 md (spec argv fs)
(MS (mkR (Z_to_bv 64 RA_MAIN) (Z_to_bv 64 (USP - 48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1
(Z_to_bv 64 (Z.of_nat (length argv))) (Z_to_bv 64 (USP + 8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 MAIN_A) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros PRE HP6 REQ HBQ HBB HBN HBD HBM Hfs FRM.
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
assert (BNR0 : 2 <= BNR /\ 512 + TRV_BB TGT_BB_A <= 512 * BNR) by (unfold BNR; pose proof TGTB as (_ & _ & G3' & _); unfold TRV_BB; Z.div_mod_to_equations; lia).
destruct PRE as [_ _ ST FD1' FD2' [AFD FD3] D S0].
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof TGTB as (G1 & G2 & G3 & G4).
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (dm_argc _ _ _ D) as ARGC.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (errno_rw_any m) as (errv & ERR). unfold A_TP in ERR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(USP - 128, USP - 48)] m) as MU.
d5_enter.
unfold MAIN_A. carve_frame 80%nat ST.
replace (USP + -48 + -80) with (USP + -128) in * by lia.
do 10 step.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (D1 : drvA_mem argv USP mx) by (eapply drvA_mem_munchM; [exact D | exact MU | exact WM | exact MI | unfold mwin; ivs_lia]);
assert (S1 : stdio0 mx) by (eapply stdio0_munchM; [exact S0 | exact MU | unfold mwin; ivs_lia]);
assert (HP1 : HEAPA6 A0 [] LM0 [] B0 mx md) by (eapply heapA_munchM6; [exact HP6 | exact MU | exact WM | exact MI | constructor; [cbn [fst snd]; unfold alloc_ceiling; split; [lia | left; lia] | constructor]])
end.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ (hr_view H6 _ _ _ _ _ _ _ HP1)) as HCK1.    destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [ARGC2|ARGCN].
2:{
match goal with |- context [if ?c then _ else _] =>
replace c with true by (symmetry; unfold bv_eqb; cbn -[Z.eqb bv_unsigned Z_to_bv]; rewrite !unsigned_lit by lia;
apply Bool.negb_true_iff; apply Z.eqb_neq; lia) end.
cbv iota. evt_done5.
assert (SPEC : spec argv fs = t_die (msg_usage (nth 0 argv [])) fs).
{ destruct argv as [|a0s [|pth [|x r]]]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in ARGC, ARGCN; try lia; reflexivity. }
rewrite SPEC.
eapply (leaf_usage_ok H6 SYS OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO [] fs LM0 USPF LOF TOPF PFRT PFLO OBL_PFRT OBL_PFLO FPS);
[split; [exact D1 | exact S1] | exact (hr_view H6 _ _ _ _ _ _ _ HP1) | exact ST | do 9 eexists; unfold main_frame; exact FR | exact FD2' | exact Hfs | exact FRM]. }
assert (SHAPE : exists a0s path, argv = [a0s; path]).
{ destruct argv as [|a0s [|path [|x r]]]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in ARGC2; try lia. exists a0s, path. reflexivity. }
destruct SHAPE as (a0s & path & Eargv).
assert (NTH1 : nth 1 argv [] = path) by (rewrite Eargv; reflexivity).

pose proof VA as VA'. rewrite Eargv in VA'.
destruct VA' as (_ & _ & VLEN & VNUL & VTL). apply Forall_cons_iff in VNUL as [_ VNUL]. apply Forall_cons_iff in VNUL as [PNUL _].
cbn [tl] in VTL. apply Forall_cons_iff in VTL as [[PSL PDD] _].

match goal with |- context [if ?c then _ else _] =>
replace c with false by (symmetry; unfold bv_eqb; cbn -[Z.eqb bv_unsigned Z_to_bv]; rewrite !unsigned_lit by lia;
apply Bool.negb_false_iff; apply Z.eqb_eq; lia) end.
cbv iota.
destruct (dm_arg1 _ _ _ D1 ltac:(rewrite Eargv; cbn; lia)) as (p1 & A1 & STR). rewrite NTH1 in STR.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ (hr_view H6 _ _ _ _ _ _ _ HP1)) as (g & CG & CC & _). cbn [hl_got_guard hl_guard hl_tp hla_base A4L A4H] in CG, CC.
apply ro_C8_of_bytes_at in CG. apply ro_C8_of_bytes_at in CC.
step. step. step. step.
apply evt_done. change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
pose proof STR as (SB1 & SB2 & SB3 & [SB4a [SB4b SB4c]] & _).

assert (AFTER : forall m', munch [(bv_unsigned (Z_to_bv 64 SP) - 112, bv_unsigned (Z_to_bv 64 SP)); (A_TP - 164, A_TP - 160)] m0 m' ->
wmono asegs m0 m' -> mem_inv asegs m' ->
drvA_mem argv USP m' /\ stdio0 m' /\ HEAPA6 A0 [] LM0 [] B0 m' md /\ ro_cells asegs m' (USP + 16) [C8 (Z_to_bv 64 p1)]
/\ rw_cells asegs m' SP [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 (firstn 64 (firstn 72 junk)))))))));
C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 RA_MAIN)]).
{ intros m' MU' WM' MI'. rewrite unsigned_lit in MU' by lia. unfold A_TP in MU'.
split; [| split; [| split; [| split]]].
- eapply drvA_mem_munchM; [exact D1 | exact MU' | exact WM' | exact MI' | unfold mwin, A_TP; ivs_lia].
- eapply stdio0_munchM; [exact S1 | exact MU' | unfold mwin, A_TP; ivs_lia].
- eapply heapA_munchM6; [exact HP1 | exact MU' | exact WM' | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling, A_TP; [split; [lia | left; lia] | split; [lia | right; left; lia]].
- eapply ro_cells_transport; [exact A1 | exact MU' |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
- eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }

assert (KFAIL : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config) (e : Z),
munch [(bv_unsigned (Z_to_bv 64 SP) - 112, bv_unsigned (Z_to_bv 64 SP)); (A_TP - 164, A_TP - 160)] m0 m' -> wmono asegs m0 m' -> mem_inv asegs m' ->
stk asegs m' LO (bv_unsigned (Z_to_bv 64 SP)) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 e)] -> CNEXT Jx md cf' -> same_io md cf' ->
RZAx A0 cf' (t_die (msg_cannot_open path) fs)
(MS (mkR (Z_to_bv 64 OPENCALL_RET_A) (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0' t1' t2' (Z_to_bv 64 2) s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 p1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc (Z_to_bv 64 OPENCALL_RET_A)) fc None m' (seg_rom asegs))).
{ intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' e MU' WM' MI' ST' ERR' HN' [SIO1 SIO2].
destruct (AFTER m' MU' WM' MI') as (D' & S' & HP' & A1' & FR'). rewrite unsigned_lit in ST' by lia.
apply (fun HX => QZsi.heapA_cfg_next A4L H6 _ _ _ _ _ _ _ cf' HX HN') in HP'. apply (hr_view H6) in HP'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.
d5_enter.
replace (ret_pc (Z_to_bv 64 OPENCALL_RET_A)) with (Z_to_bv 64 OPENCALL_RET_A : word) by (symmetry; apply ret_pc_even; [unfold OPENCALL_RET_A; lia| reflexivity]).
unfold OPENCALL_RET_A. step.
match goal with |- context [if ?c then _ else _] => replace c with true by reflexivity end. cbv iota.
evt_done5. rewrite <- Hfs, <- SIO2, <- NTH1.
eapply (leaf_openfail_ok H6 SYS OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO [] LM0 USPF LOF TOPF PFRT PFLO OBL_PFRT OBL_PFLO FPS);
[split; [exact D' | exact S'] | exact HP' | exact ST' | rewrite Eargv; cbn; lia | exact A1' | rewrite SIO1; exact FD2' | exact FRM]. }

assert (PFX : forall k, (k <= length path)%nat -> bytes_at asegs m0 p1 (firstn k path)).
{ intros k Hk. destruct SB1 as (Q1 & Q2 & Q3). rewrite length_app in Q2. cbn [length] in Q2.
split; [exact Q1|]. split; [rewrite length_firstn; lia|].
intros i Hi. rewrite length_firstn in Hi. rewrite (Q3 i) by (rewrite length_app; cbn; lia).
rewrite nth_error_app1 by lia. rewrite nth_error_firstn. replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }

replace (spec argv fs) with (spec [a0s; path] fs) by (rewrite Eargv; reflexivity). unfold spec.
destruct (4096 <=? length path)%nat eqn:TL.
{
apply Nat.leb_le in TL.
eapply (open_toolong_cps_A Jx SYS) with (lo := LO) (pp := p1) (p := path);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| exact SB1 | exact PNUL | exact TL | exact PSL | exact PDD
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' SIO'.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }
apply Nat.leb_gt in TL.
destruct (list_byte_eqb path []) eqn:E0.
{
apply list_byte_eqb_eq in E0.
eapply (open_empty_cps_A Jx SYS) with (lo := LO) (pp := p1);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| rewrite E0 in SB1; exact SB1
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' SIO'.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }
apply list_byte_eqb_false in E0.
assert (NEQ23 : Z_to_bv 64 2 <> Z_to_bv 64 3) by exact neq23.
destruct (list_byte_eqb path dot_path) eqn:ED.
{
apply list_byte_eqb_eq in ED.
eapply (open_dot_cps_A Jx SYS) with (lo := LO) (pp := p1);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| rewrite ED in SB1; exact SB1 | exact AFD | exact FD3
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity
| apply t_emit_has_nil | apply t_emit_has_nil | | ].
{ intros e t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' INe MU' WM' MI' ST' ERR' HN' SIO'.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' FDS' FSE'.
destruct (AFTER m' MU' WM' MI') as (D' & S' & HP' & A1' & FR'). rewrite unsigned_lit in ST' by lia.
assert (HPd : HEAPA6 A0 [] LM0 [] B0 m' cf') by (eapply (QZsi.heapA_cfg_next A4L H6); [exact HP' | exact HN']).
d5_reenter A0.
replace (ret_pc (Z_to_bv 64 595512)) with (Z_to_bv 64 595512 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
match goal with |- context [if ?c then _ else _] => replace c with false by reflexivity end. cbv iota.
step. evt_done5.
unfold t_opened_dir. rewrite <- NTH1. replace fs with (m_fs (cfg_model cf')) by (rewrite FSE'; exact Hfs).
eapply read_entry_dir;
[ rewrite Eargv; cbn; lia | split; [exact D' | exact S'] | exact HPd | exact REQ | exists errv; exact ERR' | exact ST' | exact A1'
| rewrite FDS'; apply Qn1e.fd_lookup_insert_eq
| rewrite FDS', Qn1e.fd_lookup_insert_neq by exact NEQ23; exact FD2'
| unfold RDQ, BQR, TR_BQ, TRV_BB in HBQ; pose proof TGTB as (_ & _ & G3' & _); lia
| unfold RDB, BBR, TR_BB, TRV_BB in HBB; pose proof TGTB as (_ & _ & G3' & _); lia
| lia
| pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (_ & BD0 & _); lia | exact FRM ]. }
apply list_byte_eqb_false in ED.
assert (NDR : path_is_dirref path = false).
{ unfold path_is_dirref. rewrite (Qn1e.path_eqb_neq path Uapi.dot_path ED). cbn [orb]. exact PDD. }
rewrite <- Hfs. destruct (fs_lookup (m_fs (cfg_model md)) path) as [data|] eqn:FS.
2:{
eapply (open_absent_cps_A Jx SYS) with (lo := LO) (pp := p1);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| exact SB1 | exact PNUL | lia | exact E0 | exact PSL | exact NDR | exact FS
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' SIO'. rewrite Hfs.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }

eapply (open_file_cps_A Jx SYS) with (lo := LO) (pp := p1);
[ exact HCK1 | reflexivity | reflexivity | reflexivity
| exact SB1 | exact PNUL | lia | exact E0 | exact PSL | exact NDR | exact FS | exact AFD | exact FD3
| exact CG | exact CC | exact ERR
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia
| right; rewrite unsigned_lit by lia; lia | exact MI | unfold RA_MAIN; rewrite unsigned_lit by lia; reflexivity
| apply t_emit_has_nil | unfold t_opened; apply t_body_nil | | ].
{ intros e t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' INe MU' WM' MI' ST' ERR' HN' SIO'. rewrite Hfs.
from5 A0. eapply KFAIL; [exact MU' | exact WM' | exact MI' | exact ST' | exact ERR' | exact HN' | exact SIO']. }
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' cf' MU' WM' MI' ST' ERR' HN' FDS' FSE'.
destruct (AFTER m' MU' WM' MI') as (D' & S' & HP' & A1' & FR'). rewrite unsigned_lit in ST' by lia.
assert (HPd : HEAPA6 A0 [] LM0 [] B0 m' cf') by (eapply (QZsi.heapA_cfg_next A4L H6); [exact HP' | exact HN']).
d5_reenter A0.
replace (ret_pc (Z_to_bv 64 595512)) with (Z_to_bv 64 595512 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step.
match goal with |- context [if ?c then _ else _] => replace c with false by reflexivity end. cbv iota.
step. evt_done5.
unfold t_opened. rewrite Hfs.
assert (RESTS_T : TR_BB TGT_BB_A <= BBR /\ TR_BD TGT_BD_A <= BDR) by (unfold BBR, BDR; lia).
assert (RESTS_H : TR_BB TGT_BB_A + 512 <= BBR /\ TR_BD TGT_BD_A <= BDR /\ 0 <= TR_BB TGT_BB_A /\ 0 <= TR_BD TGT_BD_A) by (unfold BBR, BDR, TR_BB, TR_BD, TRV_BB; lia).
assert (RESTS_R : 0 <= BBR /\ 0 <= BDR) by (unfold BBR, BDR, TR_BB, TR_BD, TRV_BB; lia).
assert (RESTS6_T : TR_BQ TGT_BB_A <= BQR /\ 512 + TRV_BB TGT_BB_A <= 512 * BNR /\ TRV_BB TGT_BB_A <= 2^30) by (unfold BQR; split; [lia| split; [exact (proj2 BNR0)| exact TGTB6]]).
assert (RESTS6_H : 8192 <= BQR /\ 1 <= BNR /\ 0 <= BDR) by (unfold BQR, TR_BQ, TRV_BB, BDR, TR_BD; lia).
assert (RESTS6_R : 0 <= BBR /\ 0 <= BDR /\ 0 <= BQR /\ 0 <= BNR) by (unfold BBR, BDR, BQR, TR_BB, TR_BD, TR_BQ, TRV_BB; lia).
pose proof (trun_ok H6 reqA OBL_MALLOC_N6 OBL_FREE_NN OBL_CLIENT_FRAME OBL_CS_WIDE OBL_CLIENT_FRAME6 argv USP LO data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF FD1'
BBR BDR BQR BNR GA TGT_STACK_A TGT_BB_A TGT_BD_A TGT OBL_GA_of TGTB PFRT PFLO OBL_PFRT OBL_PFLO PF1 PFK RESTS_T RESTS6_T LM0S) as TRUN.
pose proof (leaf_hdr_ok H6 SYS reqA OBL_FREE_NN OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF FD2' PFRT PFLO OBL_PFRT OBL_PFLO FWR) as HLEAF.
pose proof (hdr_ok H6 SYS reqA OBL_FREE_NN OBL_CS_WIDE argv USP LO data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF BBR BDR (TR_BB TGT_BB_A) (TR_BD TGT_BD_A) BQR BNR
RESTS_H RESTS6_H TRUN HLEAF) as HDR.
pose proof (leaf_refused_ok H6 SYS OBL_CLIENT_FRAME OBL_CS_WIDE argv USP LO data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF FD2' PFRT PFLO OBL_PFRT OBL_PFLO FPU) as LREF.
pose proof FS as FS0. rewrite Hfs in FS0.
pose proof (read_entry_ok H6 SYS reqA OBL_MALLOC_N6 OBL_FREE_N6 OBL_CS_WIDE argv USP LO path data fs LM0 (m_fds (cfg_model md)) USPF LOF TOPF FS0
BBR BDR BQR BNR OBL_CLIENT_FRAME6 RESTS6_R LREF RESTS_R HDR) as RD.
eapply RD;
[ split; [exact D' | exact S'] | exact HPd | exact REQ | exists errv; exact ERR' | exact ST'
| do 9 eexists; unfold main_frame; exact FR'
| unfold LFDS; rewrite FDS'; split; [apply Qn1e.fd_lookup_insert_eq | intros fd' NE; rewrite Qn1e.fd_lookup_insert_neq by exact NE; reflexivity]
| rewrite FSE'; exact Hfs
| exact HBQ | exact HBB | exact HBN | exact HBD | exact HBM
| exact FRM ].
Qed.
End Main.
End RC__1.
