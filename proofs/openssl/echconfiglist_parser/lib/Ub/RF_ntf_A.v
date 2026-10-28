(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import F_malloc_free MallocModel_B F_ntf_A F_ntf_B.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaRel.
Local Ltac lia ::=
  dle_wrap ltac:(first [ n8v_prune1p; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker   (* [comment removed for export] *)
        | n8v_prune1; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker    (* [comment removed for export] *)
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker    (* [comment removed for export] *)
        | n8v_prunep; Zify.zify; xlia zchecker                                                 (* [comment removed for export] *)
        | zify_prune; Zify.zify; xlia zchecker                                                 (* [comment removed for export] *)
        | Zify.zify; xlia zchecker ]).                                                          (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
  [CB 48 junk; C8 (wz hcanary); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

End HCW.


(* [comment removed for export] *)
Ltac rmeta_open cq MUq WMq :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
    pose proof (wmono_refl usegs mX) as WMq end.

(* [comment removed for export] *)
Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]);
    clear MUq WMq CH end.

(* [comment removed for export] *)
Ltac rmeta_chunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
  rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rntf_ret : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (raw s0o s1o s2o s3o : word) st st' (lo : Z),
  rmrep st' m -> mem_inv usegs m ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk usegs m lo (bv_unsigned sp + -96) -> hceil <= lo -> lo <= bv_unsigned sp - 96 ->
  munch ((bv_unsigned sp - 96, bv_unsigned sp) :: W) m0 m -> wmono usegs m0 m ->
  ivs_covered (rfree_fp st lo (bv_unsigned sp)) W ->
  evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st' a2 a1)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b67a4) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until lo. intros MR' MI S1 FR ST LO LOLE MU WM COV.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, RSSP_GUARD, rntf_frame in *. subst s1.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl usegs m) as WMs.
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia]) end.
  clear MR' MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|exact COV]. intros x Hx. apply rfree_fp_stack. lia. }
  finish.
Qed.

(* [comment removed for export] *)
Lemma rntf_aor : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (i lo : Z),
  rmrep st m -> mem_inv usegs m -> meta_slot st g ->
  a1 = wz (sxv (2 ^ i)) -> 0 <= i < 32 ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  0 <= m_freed (get_meta_rec st g) < 2^32 ->
  rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk usegs m lo (bv_unsigned sp + -96) -> hceil <= lo -> lo <= bv_unsigned sp - 96 ->
  evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (aor_st st g i) (wz 0) (wz 0))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b677c) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until lo. intros MR MI MSL A1 HI S1 HF FR ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
  pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & _). pose proof MSL as MS0. destruct MS0 as (ar0 & arr0 & k0 & Har0 & Hk0 & Eg0).
  destruct (rarea_conc st ar0 arr0 WF Har0) as (ra0 & Hra0 & Ca0 & Sa00 & Sa01 & SaL0 & NK0 & RB00 & RBAL0 & RBC0).
  assert (HGA : conc st g = conc st ar0 + (24 + 40 * k0)) by (rewrite Eg0, conc_aadd by (rewrite Hra0; eauto); reflexivity).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, NSLOTS in *.
  assert (GB : 0 <= conc st g /\ conc st g + 40 <= lo) by lia.
  pose proof (rmrep_meta_chunk st m g MR MSL) as MM. unfold meta_cells in MM.
  set (mr := get_meta_rec st g) in *.
  pose proof (sxv_range (2 ^ i)) as RS. pose proof (sxv_range (m_freed mr)) as RF.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (conc st g + 28)) = true).
  { apply amo_aligned_intro; [lia|]. rewrite HGA, Ca0. Z.div_mod_to_equations. (first [clear - H9 H4 H0 H RBAL0 SaL0; lia | lia]). }
  subst a1.
  st1. rewrite sx32_wz_sxv by lia. st1.
  amo_step AMO. rewrite ?sx32_wz_sxv by lia.
  st1. if_false.
  amo_step AMO.
  st1. if_false.
  st1. rewrite ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (MR' : rmrep (aor_st st g i) mX) end.
  { unfold aor_st. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
    eapply rw_cells_congr; [ | | | exact MM].
    - unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
      rewrite (Z.lor_comm (sxv (m_freed mr)) (sxv (2 ^ i))).
      rewrite (le4_lor_sxv (m_freed mr) (2 ^ i)); [reflexivity | lia |].
      split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
    - reflexivity.
    - cbn. (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto]). }
  clear MUg MM.
  (* [comment removed for export] *)
  st1. st1.
  eapply rntf_ret; [exact MR' | assumption | exact S1 | exact FR | exact ST | hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia | lia | exact MU | exact WM |].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply rfree_fp_meta; [exact MR | exact MSL | lia].
Qed.

(* [comment removed for export] *)
Lemma rntf_frame_remerge : forall m A (j0 : list byte) (z1 z2 z3 z4 z5 : word) rest,
  rw_cells usegs m A (CB 8 j0 :: C8 z1 :: C8 z2 :: C8 z3 :: C8 z4 :: C8 z5 :: rest) ->
  rw_cells usegs m A (CB 48 (j0 ++ le8 z1 ++ le8 z2 ++ le8 z3 ++ le8 z4 ++ le8 z5) :: rest).
Proof. try hcb. try hsb.
  intros m A j0 z1 z2 z3 z4 z5 rest H. pose proof H as [[WF _] _]. destruct WF as [L0 WFr]. cbn in L0.
  eapply rw_cells_congr; [| | | exact H].
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
  - reflexivity.
  - split; [| destruct WFr as (_ & _ & _ & _ & _ & X); exact X]. cbn [cell_wf]. rewrite !length_app, !length_le8, L0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rntf_fm : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (lo : Z),
  rmrep st m -> mem_inv usegs m -> meta_slot st g ->
  fm_facts st g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk usegs m lo (bv_unsigned sp + -96) -> hceil <= lo -> lo <= bv_unsigned sp - 96 ->
  evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a2 a1)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b66e0) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until lo. intros MR MI MSL FMF S1 FR ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof FR as [[[LJ _] _] _]. cbn in LJ.
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, RCTX, rntf_frame in *.
  rmeta_chunk MR MSL CH.
  (* [comment removed for export] *)
  pose proof MR as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRf : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM | intros l h [E|[]]; inversion E; subst; hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia]) end.
  clear MUs.
  (* [comment removed for export] *)
  rmeta_open (conc st g) MUg WMg.
  st1. st1. (* [comment removed for export] *)
  st1. st1. (* [comment removed for export] *)
  st1. st1. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C4 ?va; C4 ?vf; ?c5] =>
    assert (CH' : rw_cells usegs mX A [c0; c1; c2; CB 8 (le4 va ++ le4 vf); c5])
      by (eapply rw_cells_congr; [ | | | exact CH]; [cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity | reflexivity | cbn -[le4 app]; rewrite ?app_length, ?length_le4; cbn; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]);
    clear CH; rename CH' into CH
  end end.
  st1. st1. (* [comment removed for export] *)
  st1. st1. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C8 ?z; ?c5] =>
    assert (CH' : rw_cells usegs mX A [c0; c1; c2; C4 (wz 0); C4 (wz 0); c5])
      by (eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]);
    clear CH; rename CH' into CH
  end end.
  rmeta_close MRf MSL MUg WMg CH (put_meta g meta0 st) MR0.
  set (st0 := put_meta g meta0 st) in MR0.
  assert (MSL0 : meta_slot st0 g) by (apply meta_slot_put_meta; exact MSL).
  (* [comment removed for export] *)
  rmeta_chunk MR0 MSL0 CH0.
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  clear CH0 K1 K2.
  (* [comment removed for export] *)
  st1. destruct (c_free_meta_head (ctx st)) as [head|] eqn:FMH.
  - (* [comment removed for export] *)
    destruct (FMF head FMH) as (NEh & MSh & pv & Hpv & NEp & MSp).
    pose proof (rmeta_slot_bounds st m head MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
    unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    (* [comment removed for export] *)
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR0 MSL0 CH.
    st1.
    rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_next (Some head) meta0) st0) MRa.
    set (stA := put_meta g (m_set_next (Some head) meta0) st0) in MRa.
    assert (MSha : meta_slot stA head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
    assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
    assert (MSpa : meta_slot stA pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
    (* [comment removed for export] *)
    rmeta_chunk MRa MSha CHh. rewrite get_meta_rec_put_other in CHh by exact NEh.
    unfold st0 in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
    st1.
    clear CHh.
    (* [comment removed for export] *)
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MRa MSga CH.
    st1.
    rmeta_close MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) stA) MR1.
    unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga MSpa stA.
    set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) st0) in MR1.
    assert (MSh1 : meta_slot st1 head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
    assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
    assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
    (* [comment removed for export] *)
    munch_grow MU (conc st pv, conc st pv + 40). munch_grow MU (conc st head, conc st head + 40).
    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR1 MSp1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
    st1.
    rmeta_close MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2.
    set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
    assert (MSh2 : meta_slot st2 head) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
    (* [comment removed for export] *)
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    unfold st1 in CH. rewrite get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0 m_set_prev m_set_next Z.mul Z.add oconc] in CH.
    st1. clear CH.
    (* [comment removed for export] *)
    rmeta_open (conc st head) MUh WMh.
    rmeta_chunk MR2 MSh2 CH.
    st1.
    rmeta_close MR2 MSh2 MUh WMh CH (put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2) MR3.
    assert (EQ3 : fm_st st g = put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2).
    { unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_link.
      rewrite !upd_meta_put. rewrite (get_meta_rec_put_other st g meta0 head NEh), Hpv. cbn iota. rewrite !upd_meta_put.
      rewrite get_meta_rec_put_same.
      rewrite (get_meta_rec_put_other (put_meta g meta0 st) g _ pv NEp). rewrite (get_meta_rec_put_other st g meta0 pv NEp).
      reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
    eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia | lia | exact MU | exact WM |].
    cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
    + eapply rfree_fp_meta; [exact MR | exact MSh | lia].
    + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
    + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
    + apply rfree_fp_ctx. unfold RCTX. lia.
  - (* [comment removed for export] *)
    unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR0 MSL0 CH.
    st1. st1.
    rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) MRb.
    set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) in MRb.
    (* [comment removed for export] *)
    clear C1. pose proof MRb as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1. rewrite FMH in C1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
    unfold RCTX in MUc.
    st1. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (set_head LFree (Some g) stB) mX) end.
    { eapply (rmrep_ctx_frameW stB _ _ _ _ MRb MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold ctx_head_cells, RCTX. cbn [ctx set_head upd_ctx s_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        unfold pw at 4. cbn [oconc]. unfold wz at 4. exact C1.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    assert (EQ3 : fm_st st g = set_head LFree (Some g) stB).
    { unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_single. rewrite upd_meta_put. fold st0. rewrite get_meta_rec_put_same. reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
    eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia | lia | exact MU | exact WM |].
    cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
    + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
    + apply rfree_fp_ctx. unfold RCTX. lia.
Qed.

End HCW2.

