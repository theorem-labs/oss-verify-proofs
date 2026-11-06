(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA PmHeapIfaceA PmShadowW ArtMem ArtRuns ArtRunsMem Pm9ArtCls Pm9ArtCellEx Pm9ArtDepot ArtBridge Pm9ArtInv Pm9ArtInvMalloc Pm9ArtLift Pm9ArtWrapKit
     Pm9ArtFsInv Pm9ArtFsInvLaws Pm9ArtIfaceLaws Pm9ArtWrapC Pm9ArtWrapVis Pm9ArtWrapC2 Pm9ArtWrapMallocH Pm9ArtInvFrameS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma shadow_blk_w_unrestrict : forall H (M : word -> option byte) u n, shadow_blk_w (mrestrict H M) u n -> shadow_blk_w M u n.
Proof. intros H M u n. apply shadow_blk_w_tr. intros j v _ _ B. exact (art_byte_unrestrict H M _ v B). Qed.

Lemma art_client_ok_frame_s : forall rn LB FF LK A (M M1 : word -> option byte) ux nx, art_client_ok rn LB FF LK A M -> mem_grows M M1 ->
  (forall b a, In b LB -> fst b <> ux -> in_shadow_of (fst b) (snd b) a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  In (ux, nx) LB -> shadow_blk_w M1 ux nx -> art_client_ok rn LB FF LK A M1.
Proof.
  intros rn LB FF LK A M M1 ux nx (C1 & CR) GR AG HB SHW. split; [|exact CR]. pose proof CR as (ND & _).
  intros b Hb. destruct (C1 b Hb) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
  split. { intros i Hi. apply GR. exact (K7 i Hi). }
  split; [|exact K9]. destruct (Z.eq_dec (fst b) ux) as [E|N].
  - assert (Eb : b = (ux, nx)).
    { clear - ND Hb HB E. induction LB as [|x r IH]; [contradiction|]. cbn [map] in ND. apply NoDup_ListNoDup in ND. inversion ND as [|y l NI ND' Ey]; subst y l. apply NoDup_ListNoDup in ND'.
      destruct Hb as [->|Hb]; destruct HB as [HB|HB].
      - exact HB.
      - exfalso. apply NI. rewrite E. change ux with (fst (ux, nx)). apply in_map. exact HB.
      - exfalso. apply NI. rewrite HB. cbn [fst]. rewrite <- E. apply in_map. exact Hb.
      - exact (IH HB ND' Hb). }
    rewrite Eb. exact SHW.
  - apply (shadow_blk_w_frame M M1 (fst b) (snd b)); [lia | | lia | intros a Ha; exact (AG b a Hb N Ha) | exact K8].
    pose proof (Z.div_mod (fst b) 16 ltac:(lia)) as D. rewrite K3, Z.add_0_r in D. rewrite D. replace (16 * (fst b / 16)) with ((2 * (fst b / 16)) * 8) by ring. apply Z_mod_mult.
Qed.

Section Wrap2s.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Context {fx : PropExec.FPState}.

#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).

Theorem art_wrap_pure2s : forall (K : ShapeAlg.TSet) (R : bvmap 5 word) (pc0 : word) (M : word -> option byte) (model : Model)
    (G : art_gs art_fsg) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (FP : Z -> Prop) (ux nx : Z)
    (Q : PropExec.FPState -> bvmap 5 word -> word -> (word -> option byte) -> Prop),
  art_alloc_rep art_fsg rn G LB (mrestrict (bhid A model) M) -> art_fsinv rn (g_fs art_fsg G) FF LK M ->
  BI (g_log art_fsg G) A M model -> art_credit_ok art_fsg BUDGET rn G LB cr -> art_client_ok rn LB FF LK A M ->
  art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A (m_vm_lazy model) -> art_eager_ok LB A (m_vm_lazy model) ->
  In (ux, nx) LB ->
  (exists (fx' : PropExec.FPState) R' pc1 Mr', msteps ASEGS (@mkst fx R pc0 (mrestrict (bhid A model) M) (seg_rom ASEGS)) (@mkst fx' R' pc1 Mr' (seg_rom ASEGS))
                       /\ mem_grows (mrestrict (bhid A model) M) Mr' /\ (forall x : word, ~ FP (U x) -> Mr' x = mrestrict (bhid A model) M x)
                       /\ cellA Mr' (rn_tp rn + rn_loff rn) 4 0 /\ shadow_blk_w Mr' ux nx /\ Q fx' R' pc1 Mr') ->
  (forall x, FP x -> art_alloc_zone art_fsg rn G x -> in_block LB x \/ in_shadow_of ux nx x) ->
  (forall x, FP x -> fs_zone3 rn x -> in_fframe FF x) ->
  (forall x, FP x -> ~ cs_zone rn x) ->
  (forall b x, In b LB -> fst b <> ux -> in_shadow_of (fst b) (snd b) x -> ~ FP x) ->
  (forall (fx' : PropExec.FPState) R' pc1 Mr' M1 model', Q fx' R' pc1 Mr' ->
       RI LB FF LK cr A M1 (vml_of model') -> mem_grows M M1 -> (forall x : word, ~ FP (U x) -> M1 x = M x) ->
       (forall x : word, bhid A model x = false -> M1 x = Mr' x) -> (forall x : word, bhid A model' x = bhid A model x) ->
       model_rt model model' -> MInv A model' ->
       srealizes ASEGS scfg (mkCfg (@mkst fx' R' pc1 M1 (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (@mkst fx R pc0 M (seg_rom ASEGS)) model) K.
Proof.
  intros K R pc0 M model G LB FF LK cr A FP ux nx Q REPr FS B0 CRED CLI KN LZ EG HB RUN FPAZ FPFS FPCS FPSH CONT.
  destruct RUN as (fx' & R' & pc1 & Mr' & MS & GRr & FRr & LSAN & SHWr & HQ).
  apply (bridge_msteps ASEGS scfg Hwx MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log art_fsg G) A (@mkst fx R pc0 M (seg_rom ASEGS)) model
           (@mkst fx' R' pc1 Mr' (seg_rom ASEGS)) K B0).
  { rewrite restrict_mkst. exact MS. }
  intros ms' model' Est B1 RT BS. destruct (@restrict_eq_mkst fx' _ _ _ _ _ _ Est) as (Ems & EMr0). set (M1 := ms_mem ms') in *. rewrite Ems. assert (EMr : mrestrict (bhid A model') M1 = Mr') by (symmetry; exact EMr0).
  change (ms_mem (@mkst fx R pc0 M (seg_rom ASEGS))) with M in BS.
  pose proof (art_bstep_pure_frame A M M1 model model' Mr' BS EMr) as FRAME.
  pose proof (art_bstep_pure_grows A M M1 model model' Mr' BS EMr GRr) as GROW.
  pose proof (art_bstep_pure_hid A M M1 model model' BS) as HID.
  assert (FR1 : forall x : word, ~ FP (U x) -> M1 x = M x) by (intros x Hx; apply FRAME; apply FRr; exact Hx).
  pose proof CLI as (C1 & _). destruct (C1 (ux, nx) HB) as (_ & _ & U16 & Unx & _). cbn [fst snd] in U16, Unx.
  assert (U8 : ux mod 8 = 0).
  { pose proof (Z.div_mod ux 16 ltac:(lia)) as D. rewrite U16, Z.add_0_r in D. rewrite D. replace (16 * (ux / 16)) with ((2 * (ux / 16)) * 8) by ring. apply Z_mod_mult. }
  apply (CONT fx' R' pc1 Mr' M1 model' HQ); [ | exact GROW | exact FR1 | | exact HID | exact RT | exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1)].
  - exists G. cbn [vml_of fst snd].
    split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr.
             apply (art_alloc_rep_frame_s art_fsg MAPS0 RESV0 rn G LB _ Mr' ux nx REPr GRr HB U8 Unx); [|exact SHWr|exact LSAN|exact (bi_live _ _ _ _ _ _ _ _ _ _ _ B0)|exact KN].
             intros x Hz Hb Hs. apply FRr. intros HF. destruct (FPAZ _ HF Hz) as [X|X]; [exact (Hb X)|exact (Hs X)]. }
    split. { apply (art_fsinv_client_proved rn (g_fs art_fsg G) FF LK M M1 FS GROW).
             - intros x a Hz Hn. apply FR1. intros HF. apply Hn. exact (FPFS _ HF Hz).
             - intros x Hz. apply FR1. intros HF. exact (FPCS _ HF Hz). }
    split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
    split; [exact CRED|].
    split. { apply (art_client_ok_frame_s rn LB FF LK A M M1 ux nx CLI GROW); [|exact HB|].
             - intros b a Hb Nb Ha.
               pose proof CLI as (C1' & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1' b Hb) as (K1 & _ & _ & K4 & K5 & _).
               assert (Ra : 0 <= a < 2 ^ 64).
               { unfold in_shadow_of, HeapIfaceA.S in Ha. assert (0 <= fst b / 8) by (apply Z.div_pos; lia).
                 assert ((fst b + snd b - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.SB in *. lia. }
               pose proof (FR1 (Z_to_bv 64 a)) as X. rewrite art_u_lit in X by exact Ra. apply X. exact (FPSH b a Hb Nb Ha).
             - apply (shadow_blk_w_unrestrict (bhid A model') M1). rewrite EMr. exact SHWr. }
    split; [exact KN|].
    split. { apply (art_lazy_ok_shrink art_fsg rn G A (m_vm_lazy model) (m_vm_lazy model') LZ). exact (art_bstep_pure_lazy A M M1 model model' BS). }
    destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
    pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
  - intros x Hx. rewrite (art_bstep_pure_mem A M M1 model model' Mr' BS EMr). rewrite Hx. reflexivity.
Qed.
End Wrap2s.
