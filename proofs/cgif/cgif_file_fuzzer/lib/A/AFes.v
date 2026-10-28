(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFi3 AFeq AFew AFeu AFf2 AFg0 AFh9 AFha AFhc AFhb AFhe AFhi AFhk AFhj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFhh.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhf AFhd AFhl AFhg.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, kChunkHeaderSize, AFh9.YFRAME, AFha.YFRAME, AFhc.YFRAME, AFhb.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, AFhd.sp1, AFhd.sp0, AFhd.SY in *; numconst.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis RCC : tfib_rchunk_spec B.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : dr_pre B ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (AFhd.sp0 regs0).
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation U := (as_universe B).
Local Notation zlen := (@AFhd.zlen _).
Local Notation OST := (AFhd.OST B ly X0 W0 regs0 mem0 md0).
Local Notation RCST := (AFhd.RCST B ly X0 W0 regs0 mem0 md0).
Local Notation RST := (AFhd.RST B ly X0 W0 regs0 mem0 md0).
Local Notation CDST := (AFhd.CDST B ly X0 W0 regs0 mem0 md0).
Local Notation QST := (AFhd.QST B ly X0 W0 regs0 mem0 md0).
Local Notation FIN := (dr_leaf B ly X0 W0 regs0 mem0 md0).
Local Notation entry_facts := (AFhl.entry_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (AFhl.sp_facts B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation T_O := (AFhg.T_O B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation T_R := (AFhg.T_R B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation T_Q := (AFhg.T_Q B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation T_E := (AFhg.T_E B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation RC_pre := (AFhg.RC_pre B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation RC_post := (AFhg.RC_post B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation CD_pre := (AFhg.CD_pre B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation CD_post := (AFhg.CD_post B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation HTSD := (AFhg.HTSD B TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Lemma ITEMS : forall b t its i fuel X W c, RCST X b t its i W c -> (length its <= fuel)%nat ->
amreal tfibsegs (recycle_items fuel its X) W c (fun r W' c' => CDST (snd r) b t W' c').
Proof.
intros b t its. induction its as [|k ks IH]; intros i fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. eapply rc_ne; [exact ST | reflexivity].
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [recycle_items].
apply (amreal_mbind tfibsegs (recycle_chunk k) (fun _ => recycle_items f ks) X W c (fun r W' c' => RST (snd r) b t ks (S i) W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
pose proof (RIx_head U 0 0 0 X k ks t [b_self b] ltac:(eapply rc_rix; exact ST)) as (WP & Hk & Hst & Hni).
apply (amreal_atok _ _ _ _ _ _ (recycle_chunk_ok U 0 0 0 X k true WP Hk Hst Hni)).
eapply amreal_mono; [| exact (RCC ly X k (sp1 + 8) W regs mem md (RC_pre X b t k ks i lz qb W regs mem md ST))].
intros [[] X1] W' c' HL [ns' RP]. cbn [snd]. exact (RC_post X b t k ks i lz qb W regs mem md X1 ns' W' c' ST HL RP).
+ intros [] X1 W1 c1 ST1. destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
eapply amreal_SRr_pre; [exact (T_R X1 b t ks (S i) lz qb W1 regs mem md ST1)|].
intros W2 c2 _ HP. unfold AFhg.postRI in HP. destruct ks as [|k' ks'].
* destruct f; cbn [recycle_items]; apply amreal_ret; cbn [snd]; exact HP.
* apply (IH (S i) f X1 W2 c2 HP). cbn in Hfuel |- *. lia.
Qed.
Lemma LOOP : forall rest fuel X W c, OST X rest W c -> (length rest <= fuel)%nat ->
amreal tfibsegs (do_recycle fuel rest X) W c FIN.
Proof.
induction rest as [|b t IH]; intros fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. eapply o_ne; [exact ST | reflexivity].
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [do_recycle].
apply (amreal_mbind tfibsegs (recycle_items 1100 (b_items b)) (fun _ => YG00.bind (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t)) X W c
(fun r W' c' => CDST (snd r) b t W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
eapply amreal_SRr_pre; [exact (T_O X b t lz qb W regs mem md ST)|].
intros W1 c1 _ H1. apply (ITEMS b t (b_items b) 0 1100 X W1 c1 H1).
destruct H1 as (lz1 & qb1 & regs1 & mem1 & md1 & _ & ST1). assert (BL : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) by (eapply rc_blen; exact ST1). unfold kBatchSlots in BL. cbn in BL. lia.
+ intros [] X1 W1 c1 ST1.
apply (amreal_mbind tfibsegs (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t) X1 W1 c1 (fun r W' c' => QST (snd r) t W' c')).
* destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
pose proof (RIx_cd_pre U 0 0 0 X1 t (b_self b) [] ltac:(eapply cd_rix; exact ST1)) as (WP & Z1 & Z2 & Z3 & RM).
apply (amreal_atok _ _ _ _ _ _ (cache_dealloc_ok U 0 0 0 X1 kBatchClass (b_self b) true WP ltac:(unfold kBatchClass; lia) Z1 Z2 Z3 RM)).
eapply amreal_mono; [| exact (tfib_cdealloc_ok B TB ly X1 kBatchClass (b_self b) W1 regs mem md (CD_pre X1 b t lz qb W1 regs mem md ST1) HTSD)].
intros [[] X2] W' c' HL [ns' CP]. cbn [snd]. exact (CD_post X1 b t lz qb W1 regs mem md X2 ns' W' c' ST1 HL CP).
* intros [] X2 W2 c2 ST2. destruct ST2 as (lz & qb & regs & mem & md & -> & ST2).
eapply amreal_SRr_pre; [exact (T_Q X2 t lz qb W2 regs mem md ST2)|].
intros W3 c3 _ HP. unfold AFhg.postQO in HP. destruct t as [|b' t'].
-- destruct f; cbn [do_recycle]; apply amreal_ret; exact HP.
-- apply (IH f X2 W3 c3 HP). cbn in Hfuel |- *. lia.
Qed.
Theorem tfib_dorecycle_arm : amreal tfibsegs (do_recycle 100000%nat P0 X0) W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) FIN.
Proof.
pose proof (seed_E B TB ly X0 P0 W0 regs0 mem0 md0 PRE) as FH.
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & INIT0). unfold spZ in *.
pose proof HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
assert (WALK : SRr tfibsegs W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) (AFh9.postE W0 ly regs0 mem0 md0 (zlen P0))).
{ unfold cfg_at. rewrite <- (wvb_self md0) at 1. exact (AFhe.segYE W0 ly regs0 mem0 md0 (zlen P0) (m_vm_materialized md0) FH). }
unfold AFh9.postE in WALK.
assert (CASES : P0 = [] \/ exists b t, P0 = b :: t) by (clear; destruct P0 as [|b t]; [left; reflexivity | right; exists b, t; reflexivity]).
destruct CASES as [EP|(b & t & EP)].
-
rewrite EP. rewrite EP, zlen_nil, Z.eqb_refl in WALK. cbn [do_recycle amreal ret].
eapply SRr_mono; [exact WALK|]. intros W' c' _ HP.
destruct HP as (-> & _ & regs & mem & mat & -> & R2 & CS & MQ & PRS).
assert (WST : forall a, AFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold AFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, AFh9.WIN regs0 a \/ ~ AFh9.WIN regs0 a) by (intros a; unfold AFh9.WIN; apply ivl_dec).
exists regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split.
{ unfold cfg_at, raZ. rewrite Z_to_bv_bv_unsigned || (unfold w64; rewrite Z_to_bv_bv_unsigned). reflexivity. }
split.
+ split; [exact (AR_after_stack_write B ly X0 W0 mem0 mem md0 mat _ HAR WST WDEC MQ PRS)|].
split; [apply layout_le_refl|]. split; [apply wle_refl|]. split.
{ apply aregs_intro; first [exact R2 | apply CS; cbn; tauto]. }
split; [apply same_io_with_vm_backing|]. split.
{ intros a Ha _ _ NS _. apply (aview_after_write (w_H W0) mem0 mem _ a MQ Ha).
intros Hw. apply NS. left. unfold AFh9.WIN in Hw. clear - Hw. nsp. lia. }
intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [clear - Ha S1 U0; nsp; lia|]. apply HPRES. clear - Ha. nsp. lia.
+ intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [clear - Ha S1 S2 U0; nsp; lia|]. apply HPRES. clear - Ha. nsp. lia.
-
replace (zlen P0 =? 0) with false in WALK by (symmetry; apply Z.eqb_neq; rewrite EP, zlen_cons; unfold AFhd.zlen; lia).
eapply amreal_SRr_pre; [exact WALK|]. intros W' c' _ HP.
apply (LOOP P0 100000%nat X0 W' c' (T_E W' c' HP)).
apply Nat2Z.inj_le. rewrite of_nat_100000. clear - LENP. lia.
Qed.
End e.
Theorem tfib_dorecycle_ok : forall B, TfibSyms B -> tfib_rchunk_spec B -> tfib_dorecycle_spec B.
Proof. intros B TB RCC ly X P W regs mem md PRE. exact (tfib_dorecycle_arm B TB RCC ly X P W regs mem md PRE). Qed.
End d.
