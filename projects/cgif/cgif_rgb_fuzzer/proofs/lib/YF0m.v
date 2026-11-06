(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF40 YF0k YF0q YF0o YF0w YF1v YF34 YF35 YF37 YF36 YF39 YF3d YF3f YF3e YF3c YF3a YF38 YF3g YF3b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFX_IMG_END, TFX_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, YF34.YFRAME, YF35.YFRAME, YF37.YFRAME, YF36.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, YF38.sp1, YF38.sp0, YF38.SY in *; numconst.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Hypothesis RCC : tfx_rchunk_spec B.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : dr_pre B ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (YF38.sp0 regs0).
Local Notation sp1 := (YF38.sp1 regs0).
Local Notation U := (as_universe B).
Local Notation zlen := (@YF38.zlen _).
Local Notation OST := (YF38.OST B ly X0 W0 regs0 mem0 md0).
Local Notation RCST := (YF38.RCST B ly X0 W0 regs0 mem0 md0).
Local Notation RST := (YF38.RST B ly X0 W0 regs0 mem0 md0).
Local Notation CDST := (YF38.CDST B ly X0 W0 regs0 mem0 md0).
Local Notation QST := (YF38.QST B ly X0 W0 regs0 mem0 md0).
Local Notation FIN := (dr_leaf B ly X0 W0 regs0 mem0 md0).
Local Notation entry_facts := (YF3g.entry_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (YF3g.sp_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation T_O := (YF3b.T_O B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation T_R := (YF3b.T_R B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation T_Q := (YF3b.T_Q B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation T_E := (YF3b.T_E B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation RC_pre := (YF3b.RC_pre B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation RC_post := (YF3b.RC_post B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation CD_pre := (YF3b.CD_pre B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation CD_post := (YF3b.CD_post B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation HTSD := (YF3b.HTSD B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Lemma ITEMS : forall b t its i fuel X W c, RCST X b t its i W c -> (length its <= fuel)%nat ->
amreal tfxsegs (recycle_items fuel its X) W c (fun r W' c' => CDST (snd r) b t W' c').
Proof.
intros b t its. induction its as [|k ks IH]; intros i fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. eapply rc_ne; [img_try (img_exact ST) | img_refl].
- destruct fuel as [|f]; [img_try (cbn in Hfuel; img_lia)|]. cbn [recycle_items].
img_apply (amreal_mbind tfxsegs (recycle_chunk k) (fun _ => recycle_items f ks) X W c (fun r W' c' => RST (snd r) b t ks (S i) W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
pose proof (RIx_head U 0 0 0 X k ks t [b_self b] ltac:(img_try (eapply rc_rix; img_exact ST))) as (WP & Hk & Hst & Hni).
img_apply (amreal_atok _ _ _ _ _ _ (recycle_chunk_ok U 0 0 0 X k true WP Hk Hst Hni)).
eapply amreal_mono; [| img_try (img_exact (RCC ly X k (sp1 + 8) W regs mem md (RC_pre X b t k ks i lz qb W regs mem md ST)))].
intros [[] X1] W' c' HL [ns' RP]. cbn [snd]. img_exact (RC_post X b t k ks i lz qb W regs mem md X1 ns' W' c' ST HL RP).
+ intros [] X1 W1 c1 ST1. destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
eapply amreal_SRr_pre; [img_try (img_exact (T_R X1 b t ks (S i) lz qb W1 regs mem md ST1))|].
intros W2 c2 _ HP. unfold YF3b.postRI in HP. destruct ks as [|k' ks'].
* destruct f; cbn [recycle_items]; img_apply amreal_ret; cbn [snd]; img_exact HP.
* img_apply (IH (S i) f X1 W2 c2 HP). cbn in Hfuel |- *. img_lia.
Qed.
Lemma LOOP : forall rest fuel X W c, OST X rest W c -> (length rest <= fuel)%nat ->
amreal tfxsegs (do_recycle fuel rest X) W c FIN.
Proof.
induction rest as [|b t IH]; intros fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. eapply o_ne; [img_try (img_exact ST) | img_refl].
- destruct fuel as [|f]; [img_try (cbn in Hfuel; img_lia)|]. cbn [do_recycle].
apply (amreal_mbind tfxsegs (recycle_items 1100 (b_items b)) (fun _ => YG00.bind (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t)) X W c
(fun r W' c' => CDST (snd r) b t W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
eapply amreal_SRr_pre; [img_try (img_exact (T_O X b t lz qb W regs mem md ST))|].
intros W1 c1 _ H1. img_apply (ITEMS b t (b_items b) 0 1100 X W1 c1 H1).
destruct H1 as (lz1 & qb1 & regs1 & mem1 & md1 & _ & ST1). assert (BL : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) by (img_try (eapply rc_blen; img_exact ST1)). unfold kBatchSlots in BL. cbn in BL. img_lia.
+ intros [] X1 W1 c1 ST1.
img_apply (amreal_mbind tfxsegs (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t) X1 W1 c1 (fun r W' c' => QST (snd r) t W' c')).
* destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
pose proof (RIx_cd_pre U 0 0 0 X1 t (b_self b) [] ltac:(img_try (eapply cd_rix; img_exact ST1))) as (WP & Z1 & Z2 & Z3 & RM).
img_apply (amreal_atok _ _ _ _ _ _ (cache_dealloc_ok U 0 0 0 X1 kBatchClass (b_self b) true WP ltac:(img_try (unfold kBatchClass; img_lia)) Z1 Z2 Z3 RM)).
eapply amreal_mono; [| img_try (img_exact (tfx_cdealloc_ok B TB ly X1 kBatchClass (b_self b) W1 regs mem md (CD_pre X1 b t lz qb W1 regs mem md ST1) HTSD))].
intros [[] X2] W' c' HL [ns' CP]. cbn [snd]. img_exact (CD_post X1 b t lz qb W1 regs mem md X2 ns' W' c' ST1 HL CP).
* intros [] X2 W2 c2 ST2. destruct ST2 as (lz & qb & regs & mem & md & -> & ST2).
eapply amreal_SRr_pre; [img_try (img_exact (T_Q X2 t lz qb W2 regs mem md ST2))|].
intros W3 c3 _ HP. unfold YF3b.postQO in HP. destruct t as [|b' t'].
-- destruct f; cbn [do_recycle]; img_apply amreal_ret; img_exact HP.
-- img_apply (IH f X2 W3 c3 HP). cbn in Hfuel |- *. img_lia.
Qed.
Theorem tfx_dorecycle_arm : amreal tfxsegs (do_recycle 100000%nat P0 X0) W0 (cfg_at tfxsegs A_DoRecycle regs0 mem0 md0) FIN.
Proof.
pose proof (seed_E B TB ly X0 P0 W0 regs0 mem0 md0 PRE) as FH.
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
assert (WALK : SRr tfxsegs W0 (cfg_at tfxsegs A_DoRecycle regs0 mem0 md0) (YF34.postE W0 ly regs0 mem0 md0 (zlen P0))).
{ unfold cfg_at. rewrite <- (wvb_self md0) at 1. img_exact (YF39.segYE W0 ly regs0 mem0 md0 (zlen P0) (m_vm_materialized md0) FH). }
unfold YF34.postE in WALK.
assert (CASES : P0 = [] \/ exists b t, P0 = b :: t) by (img_try (clear; destruct P0 as [|b t]; [img_try (left; img_refl) | img_try (right; exists b, t; img_refl)])).
destruct CASES as [EP|(b & t & EP)].
-
rewrite EP. rewrite EP, zlen_nil, Z.eqb_refl in WALK. cbn [do_recycle amreal ret].
eapply SRr_mono; [img_try (img_exact WALK)|]. intros W' c' _ HP.
destruct HP as (-> & _ & regs & mem & mat & -> & R2 & CS & MQ & PRS).
assert (WST : forall a, YF34.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (img_try (intros a Ha; unfold YF34.WIN in Ha; clear - Ha E1 E2; nsp; img_lia)).
assert (WDEC : forall a, YF34.WIN regs0 a \/ ~ YF34.WIN regs0 a) by (img_try (intros a; unfold YF34.WIN; img_apply ivl_dec)).
exists regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split.
{ unfold cfg_at, raZ. rewrite Z_to_bv_bv_unsigned || (unfold w64; rewrite Z_to_bv_bv_unsigned). img_refl. }
split.
+ split; [img_try (img_exact (AR_after_stack_write B ly X0 W0 mem0 mem md0 mat _ HAR WST WDEC MQ PRS))|].
split; [img_try (img_apply layout_le_refl)|]. split; [img_try (img_apply wle_refl)|]. split.
{ img_apply aregs_intro; first [img_exact R2 | img_apply CS; cbn; tauto]. }
split; [img_try (img_apply same_io_with_vm_backing)|]. split.
{ intros a Ha _ _ NS _. img_apply (aview_after_write (w_H W0) mem0 mem _ a MQ Ha).
intros Hw. img_apply NS. left. unfold YF34.WIN in Hw. clear - Hw. nsp. img_lia. }
intros a Ha. img_apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [img_try (clear - Ha S1 U0; nsp; img_lia)|]. img_apply HPRES. clear - Ha. nsp. img_lia.
+ intros a Ha. img_apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [img_try (clear - Ha S1 S2 U0; nsp; img_lia)|]. img_apply HPRES. clear - Ha. nsp. img_lia.
-
replace (zlen P0 =? 0) with false in WALK by (img_try (symmetry; img_apply Z.eqb_neq; rewrite EP, zlen_cons; unfold YF38.zlen; img_lia)).
eapply amreal_SRr_pre; [img_try (img_exact WALK)|]. intros W' c' _ HP.
img_apply (LOOP P0 100000%nat X0 W' c' (T_E W' c' HP)).
img_apply Nat2Z.inj_le. rewrite of_nat_100000. clear - LENP. img_lia.
Qed.
End e.
Theorem tfx_dorecycle_ok {imgk : img} : forall B, TfxSyms B -> tfx_rchunk_spec B -> tfx_dorecycle_spec B.
Proof. intros B TB RCC ly X P W regs mem md PRE. img_exact (tfx_dorecycle_arm B TB RCC ly X P W regs mem md PRE). Qed.
End d.
