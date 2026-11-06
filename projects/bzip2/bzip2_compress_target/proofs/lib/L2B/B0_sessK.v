(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit D_clx I_read RT_liveprim L_libA R_unwind_chain. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpFsKit0 AsanKit AsanCut B0_b2c_cbV B0_b2c_hcV B0_b2c_wrV B0_b2c_wrE.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).



Lemma act_geom_sub : forall RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 live0' Wc Wc',
  act_geom RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc -> (forall e, In e live0' -> In e live0) ->
  (forall x, ~ outside Wc' x -> aclient live0' fr usp x) ->
  act_geom RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0' Wc'.
Proof.
  intros RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 live0' Wc Wc' [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 CAP _] SUB WCL'.
  constructor; try assumption. intros x Hx. apply CAP. exact (aclient_mono live0' fr usp live0 fr usp x Hx SUB (fun e H => H) (Z.le_refl _)).
Qed.
Lemma sig_ok_sub : forall RT sp0 hasf k FB fr live0 live0' Σ, sig_ok RT sp0 hasf k FB fr live0 Σ -> (forall e, In e live0' -> In e live0) ->
  sig_ok RT sp0 hasf k FB fr live0' Σ.
Proof. intros RT sp0 hasf k FB fr live0 live0' Σ (H1 & H2 & H3) SUB. split; [exact H1|]. split; [exact H2|]. intros e He. exact (H3 e (SUB e He)). Qed.
Lemma live_remove_in : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> In e l /\ fst e <> p.
Proof.
  intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He. apply stdpp.list_basics.list.list_elem_of_filter in He. destruct He as [Hp He].
  split; [apply stdpp.base.list_elem_of_In; exact He|]. intros E. rewrite E, Z.eqb_refl in Hp. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma lib_of_munch : forall W (m m' : mem), OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m -> munch W m m' -> (forall x, 857056 <= x < 860480 -> outside W x) -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m'.
Proof.
  intros W m m' H MU HO. apply (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_locA m m' H). intros a (l0 & h0 & IN & R). apply MU. apply HO.
  cbn [OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__.LIB_FP In] in IN. destruct IN as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.
Lemma lib_static : forall x, (857056 <= x < 858080) \/ (858336 <= x < 858392) \/ (858432 <= x < 860480) -> client_static x.
Proof.
  intros x Hx. split.
  - exists 0xd13c0, 0xd2ed8. split; [cbn; tauto| lia].
  - intros (l0 & h0 & IN & R). cbn [RT_STATIC In] in IN.
    destruct IN as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; lia.
Qed.
Lemma lib_of_pfp : forall live frames sp W (m m' : mem), OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m -> rt_pres_fp live frames sp W m m' -> (forall x, 857056 <= x < 860480 -> outside W x) -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m'.
Proof.
  intros live frames sp W m m' H ST HO. apply (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_locA m m' H). intros a (l0 & h0 & IN & R).
  cbn [OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__.LIB_FP In] in IN.
  apply ST; [right; left; apply lib_static; destruct IN as [E|[E|[E|[]]]]; injection E as <- <-; lia| apply HO; destruct IN as [E|[E|[E|[]]]]; injection E as <- <-; lia].
Qed.

Section SessK.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma live_other_base : forall Σ (m : mem) p1 n1 p n x, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p, n) (rt_live RT Σ) -> 0 < n1 ->
  p <= x < p + n -> ~ (p1 <= x < p1 + n1) -> p <> p1.
Proof.
  intros Σ m p1 n1 p n x ART0 H1 H N1 Hx Hnx E. subst p.
  destruct (in_split _ _ H1) as (l1 & l2 & LV). rewrite LV in H. apply in_app_or in H.
  assert (C : (p1, n) = (p1, n1) \/ In (p1, n) (l1 ++ l2)).
  { destruct H as [H|[H|H]]; [right; apply in_or_app; left; exact H| left; symmetry; exact H| right; apply in_or_app; right; exact H]. }
  destruct C as [C|C]; [injection C as ->; exact (Hnx Hx)|].
  pose proof (af_live_disj RT AF Σ m p1 n1 p1 n l1 l2 ART0 LV C) as D. lia.
Qed.

(* [comment removed for export] *)
Lemma live_reader : forall Σ (m : mem) p n W, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p mod 8 = 0 -> n mod 8 = 0 -> app_fp W -> shzW b0segs W m p (p + n).
Proof.
  intros Σ m p n W ART0 LIV P8 N8 AFW. destruct (af_acc_live RT AF Σ m p n ART0 LIV) as [_ ACC].
  pose proof (af_live_range RT AF Σ m p n ART0 LIV) as (L0 & L1 & _). pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. unfold USTACK_TOP, STACK_WIN in *.
  apply (shzW_of_acc b0segs W m p n _ _ ACC AFW); [lia| lia| lia|]. clear - P8 N8. Z.div_mod_to_equations. lia.
Qed.
Lemma live_readerp : forall Σ (m : mem) p n W, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> app_fp W -> shpW b0segs W m p (p + n).
Proof.
  intros Σ m p n W ART0 LIV AFW. destruct (af_acc_live RT AF Σ m p n ART0 LIV) as [_ ACC].
  pose proof (af_live_range RT AF Σ m p n ART0 LIV) as (L0 & L1 & _). pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. unfold USTACK_TOP, STACK_WIN in *.
  apply (shpW_of_acc b0segs W m p n ACC AFW); lia.
Qed.
End SessK.

(* [comment removed for export] *)
Lemma n_rw_CB_of_bytes' : forall (m : mem) d (bs : list byte), bytes_at b0segs m d bs -> wr_at bsegs m d (Z.of_nat (length bs)) -> rw_cells b0segs m d [CB (length bs) bs].
Proof.
  intros m d bs HB HW. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HW.
Qed.

(* [comment removed for export] *)
Lemma strm_acc : forall (m : mem) STRM SHS, sanchor STRM SHS -> 0 <= STRM -> bytes_at b0segs m SHS (repeat z8 10) -> acc bsegs m STRM 80.
Proof.
  intros m STRM SHS [S8 SE] S0 ZSH.
  pose proof (acc_of_zero_shadow bsegs m STRM SHS 0 10 S8 SE S0 ltac:(lia)) as A.
  replace (STRM + 8 * 0) with STRM in A by lia. change (8 * Z.of_nat 10) with 80 in A. apply A. replace (SHS + 0) with SHS by lia. exact ZSH.
Qed.
Lemma strm_reader : forall (m : mem) STRM SHS W, sanchor STRM SHS -> 0 <= STRM -> STRM + 80 <= 2^47 -> bytes_at b0segs m SHS (repeat z8 10) -> app_fp W ->
  shzW b0segs W m STRM (STRM + 80).
Proof.
  intros m STRM SHS W AS S0 S1 ZSH AFW. pose proof (strm_acc m STRM SHS AS S0 ZSH) as ACC. destruct AS as [S8 _].
  apply (shzW_of_acc b0segs W m STRM 80 _ _ ACC AFW); [lia| lia| lia|]. clear - S8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma in_alloc_ras : forall r, existsb (Z.eqb r) ALLOC_RAS = true -> In r ALLOC_RAS.
Proof. intros r H. apply existsb_exists in H as (x & Hx & E). apply Z.eqb_eq in E. subst x. exact Hx. Qed.
(* [comment removed for export] *)
Lemma unwind_site1 : forall (m : mem) r s0v P, In r ALLOC_RAS -> 0 <= s0v < P -> P < 2^64 -> unwind_ch m (Z_to_bv 64 r) (Z_to_bv 64 s0v) (Z_to_bv 64 P).
Proof.
  intros m r s0v P H H0 H1. apply unwind_ok_ch. split.
  - rewrite unsigned_lit; [exact H|]. unfold ALLOC_RAS in H. cbn [In] in H. repeat (destruct H as [<-|H]; [lia|]). destruct H.
  - left. rewrite !unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ActNew.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variables (lo P usp sp0 : Z) (hasf : bool) (k : nat) (FB SHF FSZ SSZ : Z) (fr : list (Z * nat)) (live0 : list (Z * Z)) (Wc : list (Z * Z)).
Hypothesis G : act_geom RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc.
Variable mi : mem.
Notation PRESI := (PRESI usp fr live0 Wc mi).
Notation SOK Σ := (sig_ok RT sp0 hasf k FB fr live0 Σ).

Lemma pres_step_new : forall Σ W (m m' : mem), SOK Σ -> PRESI m -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m' ->
  (forall x, ~ KFrame.outside W x -> ((P <= x < usp) \/ (FB <= x < FB + FSZ) \/ (SHF <= x < SHF + SSZ)) \/ ~ outside Wc x \/ ~ aclient live0 fr usp x) -> PRESI m'.
Proof.
  intros Σ W m m' S H STEP HW a [Ha Ho]. rewrite <- (H a (conj Ha Ho)). apply STEP; [exact (acl_caller G Σ _ S Ha)|].
  destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O| exfalso]. destruct (HW _ O) as [E|[E|E]]; [exact (ag_cap G _ Ha E)| exact (E Ho)| exact (E Ha)].
Qed.

Lemma after_l1_new : forall Σ W (m m' : mem), SOK Σ -> ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI m ->
  NMem.mem_inv b0segs m' -> munch W m m' -> wmono b0segs m m' ->
  (forall x, ~ KFrame.outside W x -> (P <= x < usp) \/ (FB <= x < FB + FSZ - 8) \/ (SHF <= x < SHF + SSZ) \/ ~ outside Wc x
                                     \/ ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= x < p + n) /\ ~ aclient live0 fr usp x)) ->
  ART RT Σ m' /\ KMem.mem_inv bsegs m' /\ stk bsegs m' lo P /\ PRESI m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m'.
Proof.
  intros Σ W m m' S ART0 MI0 ST0 PR NMI MU WM HW. pose proof S as (S1 & S2 & S3).
  pose proof G as [FSZE SSZE SSB AX LOW LOR PUS SPT SPA GFR GSH SP0R CAP WCL].
  assert (HA : forall x, ~ KFrame.outside W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x).
  { intros x Hx. destruct (HW x Hx) as [E|[E|[E|[E|[(p & n & IN & R) _]]]]].
    - left. lia.
    - exact (acl_frame G Σ x S E).
    - exact (acl_shadow G Σ x S E).
    - exact (acl_caller G Σ x S (WCL x E)).
    - right; right; left. exists p, n. split; [exact IN| exact R]. }
  split; [| split; [| split; [| split]]].
  - apply (art_of_munch RT AF Σ m m' W P ART0 ltac:(rewrite S2; unfold RT_STACK in *; lia) MU WM HA).
  - apply (kmem_inv_munch' bsegs W m m' MI0 MU NMI). intros x Hx. unfold KMem.UTOP. pose proof (aclient_below RT AF Σ m P x ART0 (HA x Hx)) as B.
    unfold USTACK_TOP in B. exact B.
  - apply (stk_agree_nw bsegs m m' lo P ST0). intros a Ha. cbv beta in Ha. apply MU.
    destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O| exfalso]. destruct (HW _ O) as [E|[E|[E|[E|[(p & n & IN & R) _]]]]]; [lia| lia| lia| |].
    + assert (AC : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
      { apply (aclient_mono live0 fr usp _ _ usp _ (WCL _ E)); [exact S3| intros e He; rewrite S1; apply in_or_app; right; exact He| lia]. }
      destruct (aclient_split RT AF Σ m usp _ ART0 AC) as [E1|E1]; [lia| rewrite S2 in E1; lia].
    + pose proof (af_live_range RT AF Σ m p n ART0 IN) as (_ & R1 & _). rewrite S2 in R1. lia.
  - apply (pres_step_new Σ W m m' S PR (pfp_of_nmunch _ _ _ W m m' MU)). intros x Hx. destruct (HW x Hx) as [E|[E|[E|[E|[_ E]]]]].
    + left; left; exact E.
    + left; right; left; lia.
    + left; right; right; exact E.
    + right; left; exact E.
    + right; right; exact E.
  - exact (pfp_of_nmunch _ _ _ W m m' MU).
Qed.
End ActNew.
Arguments pres_step_new {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments after_l1_new {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma uw_chain_agree : forall TOPB (m m' : mem) ras f fp, uw_chain TOPB m f fp ras -> agree_on (fun x => f <= x < TOPB) m m' -> uw_chain TOPB m' f fp ras.
Proof.
  intros TOPB m m'. induction ras as [|r ras IH]; intros f fp H AG; cbn [uw_chain] in *; [exact H|].
  destruct H as (H1 & H2 & H3 & fp' & R & C & U). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact R|]. split.
  - apply (rw_cells_agree_nw bsegs m m' _ _ C). intros a Ha. apply AG. cbn [KCells.cells_size KCells.csize Nat.add] in Ha. lia.
  - apply (IH fp fp' U). intros a Ha. apply AG. lia.
Qed.
Lemma uw_chain_lower : forall TOPB (m : mem) f f' fp r ras, uw_chain TOPB m f fp (r :: ras) -> f' <= f -> uw_chain TOPB m f' fp (r :: ras).
Proof. intros TOPB m f f' fp r ras H L. cbn [uw_chain] in *. destruct H as (H1 & H2). split; [lia| exact H2]. Qed.

(* [comment removed for export] *)
Lemma live_disj_in : forall RT (AF : art_facts RT) Σ (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> (p1, n1) <> (p2, n2) ->
  p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
  intros RT AF Σ m p1 n1 p2 n2 ART0 H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & LV). rewrite LV in H2. apply in_app_or in H2.
  apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 ART0 LV). apply in_or_app.
  destruct H2 as [H|[H|H]]; [left; exact H| exfalso; exact (NE H)| right; exact H].
Qed.

(* [comment removed for export] *)
Lemma newlive_not_caller : forall RT (AF : art_facts RT) Σ2 (m2 : mem) live0 fr usp l1 p n,
  ART RT Σ2 m2 -> rt_live RT Σ2 = l1 ++ live0 -> In (p, n) l1 -> (forall e, In e fr -> In e (rt_frames RT Σ2)) -> rt_sp0 RT Σ2 - STACK_WIN <= usp ->
  forall x, p <= x < p + n -> ~ aclient live0 fr usp x.
Proof.
  intros RT AF Σ2 m2 live0 fr usp l1 p n ART2 LV IN1 FRS SPU x Hx HA.
  assert (INL : In (p, n) (rt_live RT Σ2)) by (rewrite LV; apply in_or_app; left; exact IN1).
  pose proof (af_live_range RT AF Σ2 m2 p n ART2 INL) as (R0 & R1 & R2).
  destruct HA as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range x H) as CS. unfold SEGTOP_A in *. lia.
  - destruct H as (p' & n' & IN' & Hx'). destruct (in_split _ _ IN1) as (la & lb & E1). rewrite E1, <- app_assoc in LV. cbn [app] in LV.
    pose proof (af_live_disj RT AF Σ2 m2 p n p' n' la (lb ++ live0) ART2 LV ltac:(apply in_or_app; right; apply in_or_app; right; exact IN')) as D. lia.
  - destruct H as (f & k & INF & Hf). pose proof (af_frames_range RT AF Σ2 m2 f k ART2 (FRS _ INF)) as (_ & _ & _ & FL). destruct (FL p n INL); lia.
  - destruct H as (f & k & INF & Hf). pose proof (af_fshadow_apart RT AF Σ2 m2 f k ART2 (FRS _ INF)) as (SL & _). destruct (SL p n INL); lia.
Qed.
