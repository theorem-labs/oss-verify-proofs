(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel OdModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_h_defs Atp_h_find.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_h_arith.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Od_setup_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Od_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs Od_begin.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_pro Od_pad Od_setup Od_exit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition od_iter_stmt : Prop := forall E, od_ok E -> od_oku E ->
  forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    evt usegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 (o_len E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (o_BUF E)) xs3 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 0) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom usegs)).

Lemma od_doc_bytes_ok : forall d, Forall (fun c => 0 <= c < 256) d -> bytes_ok (od_doc d).
Proof.
  intros d H. unfold od_doc. destruct (od_copied d); [| constructor].
  assert (S0 : Forall (fun c => 0 <= c < 256) (od_s0 d)).
  { destruct (OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P.Od_setup_kit.od_els_shape 0 d) as (_ & _ & _ & _ & HS0). rewrite HS0. apply Forall_firstn'. destruct d as [|b0 d']; [constructor| inversion H; assumption]. }
  unfold bytes_ok. destruct (od_s0 d) as [|c0 [|c1 [|c2 r]]] eqn:E0; try (rewrite strip_bom_short by (cbn; lia); exact S0).
  destruct (Z.eq_dec c0 239) as [->|N0]; [destruct (Z.eq_dec c1 187) as [->|N1]; [destruct (Z.eq_dec c2 191) as [->|N2]|]|].
  - rewrite strip_bom_hit. inversion S0 as [|? ? _ S1]; inversion S1 as [|? ? _ S2]; inversion S2; assumption.
  - rewrite strip_bom_miss by (intros (_ & _ & ?); congruence). exact S0.
  - rewrite strip_bom_miss by (intros (_ & ? & _); congruence). exact S0.
  - rewrite strip_bom_miss by (intros (? & _ & _); congruence). exact S0.
Qed.

Lemma od_action_range : forall d, Forall (fun c => 0 <= c < 256) d -> 0 <= od_action d <= 12.
Proof. intros [|b r] H; cbn [od_action]; [lia|]. pose proof (Z.mod_pos_bound b 13 ltac:(lia)). lia. Qed.

Lemma rw_cells_split_at1 : forall m A cs n, rw_cells usegs m A cs ->
  rw_cells usegs m A (firstn n cs) /\ rw_cells usegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply Sj_stage1_kit.rw_cells_app in H. exact H. Qed.

Lemma odinv_low : forall E v144 v176 v184 v200 v208 v216 st m1, ODINVg E v144 v176 v184 v200 v208 v216 st m1 ->
  (exists j, rw_cells usegs m1 (bv_unsigned (o_sp E) - 496) [CB 288 j])
  /\ rw_cells usegs m1 (bv_unsigned (o_sp E) - 496 + 136) [C8 (Z_to_bv 64 0)]
  /\ mem_inv usegs m1 /\ stk usegs m1 (o_lo E) (bv_unsigned (o_sp E) - 496)
  /\ munch [(o_lo E, bv_unsigned (o_sp E) - 496 + 288); (o_SB E, o_SB E + o_CAP E)] (o_m0 E) m1 /\ wmono usegs (o_m0 E) m1.
Proof.
  intros E v144 v176 v184 v200 v208 v216 st m1 INV.
  destruct INV as (FR0 & (j24 & j32 & j40 & j48 & FR24) & FR56 & (j88 & FR88) & FR96 & (j168 & FR168) & FR176
                   & (j273 & j284 & ITER) & _ & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & ST).
  unfold fr_k0 in FR0. unfold fr_k56 in FR56. unfold fr_k96 in FR96. unfold fr_k176 in FR176. unfold iter_cells in ITER. unfold od_W in MU.
  replace (bv_unsigned (o_sp E) + -496) with (bv_unsigned (o_sp E) - 496) in * by lia.
  replace (bv_unsigned (o_sp E) + -208) with (bv_unsigned (o_sp E) - 496 + 288) in MU by lia.
  remember (bv_unsigned (o_sp E) - 496) as sp0 eqn:Esp0.
  split.
  { pose proof (rw_cells_join _ _ _ _ _ FR0 FR24 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 FR56 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2.
    pose proof (rw_cells_join _ _ _ _ _ J2 FR88 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J3.
    pose proof (rw_cells_join _ _ _ _ _ J3 FR96 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J4.
    pose proof (rw_cells_join _ _ _ _ _ J4 FR168 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J5.
    pose proof (rw_cells_join _ _ _ _ _ J5 FR176 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J6.
    pose proof (rw_cells_join _ _ _ _ _ J6 ITER ltac:(cbn [app cells_size csize Nat.add]; lia)) as J7.
    cbn [app] in J7. destruct (rw_cells_forget _ _ _ _ J7) as [j J]. cbn [cells_size csize Nat.add] in J. exists j. exact J. }
  split.
  { destruct (rw_cells_split_at1 _ _ _ 5%nat FR96) as [_ R1]. cbn [firstn skipn cells_size csize Nat.add] in R1.
    destruct (rw_cells_split_at1 _ _ _ 1%nat R1) as [C136 _]. cbn [firstn skipn cells_size csize Nat.add] in C136.
    unfold Sj_stage1_kit.wz in C136.
    lazymatch type of C136 with rw_cells _ _ ?a _ => replace a with (sp0 + 136) in C136 by lia end. exact C136. }
  split; [exact MI|]. split; [exact ST|]. split; [exact MU| exact WM].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HIT : od_iter_stmt.

  Theorem rfuzz_one_of_parts : rfuzz_one_stmt.
  Proof.
    unfold rfuzz_one_stmt. intros until canary.
    intros HEAP LXS SJS SEW SSP AUX SPB B63 ST CEIL GLO LO ERR TP MI AL16 PL FRM HA0 HA1.
    unfold OdModel.fuzz_one. cbn [bind ret lib_malloc lib_free lops Target.ops cho].
    eapply (od_pro_cps HM HF); try eassumption.
    cbv beta. intros v st1 ms1 VP. unfold pro_post in VP.
    destruct VP as (x1 & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & A & cap & bv & jr
                    & j0 & j288 & jfd
                    & -> & -> & CAPB & MI1 & ST1 & ERR1 & AUX1 & FA1 & SO1 & HEAP1 & VR1 & PRES1 & SJS1 & PL1 & OUT & SCR & XFD & SAVE).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof LO as LO'. unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK in LO'.
    eapply (od_pad_cps HM) with (m0 := m) (s00 := s) (init := init) (B := B) (lo := lo);
      [exact HEAP| exact LXS| exact HEAP1| exact AUX1| lia| exact B63| exact ST1| exact CEIL| exact GLO| unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK; lia
      | exact ERR1| exact MI1| replace (bv_unsigned sp - 496 + 496) with (bv_unsigned sp) by lia; exact AL16| exact FA1| exact SO1
      | exact VR1| exact CAPB| exact PRES1| exact SJS1| exact PL1| exact OUT| exact SCR| exact XFD| exact SAVE|].
    cbv beta. intros cpo st2 ms2 PD. unfold pad_post in PD.
    destruct PD as (y1 & yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & ys3 & yt3 & yt4 & yt5 & yt6 & m2 & errv2 & COPY & BUF & jl & j305
                    & -> & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & HEAP2 & PRES2 & LXS2 & SJS2 & PL2 & VR2 & DOC2 & LOW2 & PA2 & XFD2 & SAVE2).
    pose proof (od_doc_len d) as (DCL0 & DCL & DCD & DCP). unfold SJ_PADMAX in DCP.
    pose proof PL as (_ & PRNG & _).
    pose proof (od_doc_bytes_ok d PRNG) as BOK.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL'; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    remember (bv_unsigned sp - 496) as sp0 eqn:Esp0.
    remember (zlength (od_s0 d)) as len0 eqn:Elen0.
    set (LBC := cblocks cpo COPY (len0 + 64) ++ (bv, A, 16 * cap) :: LB) in *.
    assert (BUFR : 0 <= BUF < 2^63).
    { destruct cpo as [pcp|]; [| destruct DOC2 as (_ & -> & _); lia]. destruct DOC2 as (_ & C1 & C2 & (C0 & _ & _ & CC & _)).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CC. lia. }
    assert (DOCS : od_doc d = [] \/ (bytes_at usegs m2 BUF (padded_bytes (od_doc d)) /\ 0 < BUF
                                     /\ exists b, In b LBC /\ blk_addr b <= BUF /\ BUF + blen (od_doc d) + 64 <= blk_addr b + blk_size b)).
    { destruct cpo as [pcp|]; [right| left; destruct DOC2 as (_ & _ & E); exact E]. destruct DOC2 as (BB & C1 & C2 & (CP0' & _)).
      split; [exact BB|]. split; [lia|]. exists (pcp, COPY, len0 + 64). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. unfold blen, zlength in *. lia. }
    eapply (od_setup_cps HM) with (LBC := LBC) (B := B) (lo := lo) (init := init) (bs := od_doc d) (BUF := BUF) (COPY := COPY);
      [exact HEAP2| exact AUX2| lia| exact B63| exact ST2| exact CEIL| exact GLO| unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK; lia
      | exact ERR2| exact MI2| exact LXS2| exact SJS2| exact BOK| unfold blen, zlength in *; lia| exact BUFR| exact DOCS| exact LOW2| exact PA2|].
    cbv beta. intros psb pim pix poc pia st3 ms3 SP. unfold setup_post in SP.
    destruct SP as (z1 & zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & m3 & errv3 & SB & IMPL & IDX & OC & IA & code & idxs & ws
                    & jl3 & j305' & p12 & p28 & p50 & nxt & docv
                    & -> & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & HEAP3 & PRES3 & LXS3 & SJS3 & LOW3 & PA3 & THIS3 & ARR3 & LWS3 & FIRSTN3 & WRSB3
                    & BRSB & BRIM & BRIX & CR & S1OK).
    remember (blen (od_doc d)) as L eqn:EL.
    assert (L0 : 0 <= L) by (subst L; unfold blen; lia).
    assert (LMAX : L <= 1048512) by (subst L; unfold blen, zlength in *; lia).
    unfold GLOBALS_TOP in GLO.
    assert (LO0 : 0 <= lo) by (destruct ST3 as [? _]; assumption).
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
    assert (INLB : forall b, In b LB -> In b LBC) by (intros b Hb; unfold LBC; apply in_or_app; right; right; exact Hb).
    assert (BLKCL : forall b a, In b LBC -> blk_addr b <= a < blk_addr b + blk_size b -> lx_client LBC (sp0 + 344) [LXW_SJ] a).
    { intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
      pose proof (LH_block_range _ _ _ _ HEAP2 Hb) as (_ & _ & _ & _ & BS). unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha BS. lia. }
    assert (FRCL : forall a, sp0 + 344 <= a -> lx_client LBC (sp0 + 344) [LXW_SJ] a).
    { intros a Ha. split; [| left; exact Ha]. unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha GLO LO' Esp0. lia. }
    assert (PRES3' : lx_pres LB (sp0 + 496) [LXW_SJ] m m3).
    { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_weaken; [exact PRES3| lia| exact INLB| auto]. }
    assert (PL3 : payload_ok m3 LB D d).
    { eapply payload_ok_agree; [exact AG3| exact PL2|]. intros b a Hb Ha. apply (BLKCL b a (INLB b Hb) Ha). }
    assert (VR3 : vrep m3 (sp0 + 344) A (cap, Z.of_nat (od_P d), Some bv) (od_els D d) jr).
    { eapply vrep_agree; [exact AG3| | | exact VR2].
      - intros a Ha. apply FRCL. lia.
      - intros a _ Ha. apply (BLKCL (bv, A, 16 * cap)); [unfold LBC; apply in_or_app; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG3) in XFD2; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in SAVE2; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    pose proof (rw_cells_merge usegs m3 (sp0 + 288) [] [C1 (Z_to_bv 8 0); CB 7 j305'] _ PA3) as PA3'.
    cbn [app cells_size csize cells_bytes cbytes Nat.add] in PA3'.
    assert (XI3 : exit_inv sp0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m s LB lo B D d bv A cap (Z.of_nat (od_P d)) (od_els D d) psb pim pix poc pia SB (OD_SBUF L)
                           (match cpo with Some p => [(p, COPY, len0 + 64)] | None => [] end) m3 st3).
    { unfold exit_inv. exists IMPL, IDX, OC, IA, (OD_IDX L), errv3, jr, jl3. do 2 eexists. do 4 eexists. do 12 eexists.
      split; [exact HEAP3|]. split; [exact AUX3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [congruence|]. split; [congruence|].
      split; [exact PRES3'|]. split; [exact SJS3|]. split; [exact PL3|]. split; [exact VR3|]. split; [exact LOW3|]. split; [exact PA3'|].
      split; [exact THIS3|]. split; [exact XFD2| exact SAVE2]. }
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    assert (TPE : tp = Z_to_bv 64 RATP) by exact TP.
    unfold implM. iprefix.

    step.
    destruct (Z.eq_dec code 0) as [C0|CN].
    -
      subst code. if_true.
      destruct (S1OK eq_refl) as (S1O & BUFB3).
      pose proof (S1OUT_length_le _ _ S1O) as NLE. pose proof (S1OUT_length_pos _ _ S1O) as NPOS. rewrite <- EL in NLE.

      destruct cpo as [pcp|]; [| exfalso; destruct DOC2 as (_ & _ & E0); rewrite E0 in EL; unfold blen in EL; cbn [length] in EL; clear - EL NLE NPOS; lia].
      destruct DOC2 as (_ & CB1 & CB2 & BRC). cbn [cblocks app] in LBC.
      pose proof BRC as (CP0 & _ & _ & CPC & _). pose proof BRSB as (SB0 & _ & SBN & SBC & SBS). pose proof BRIM as (IM0 & _ & _ & IMC & _). pose proof BRIX as (IX0 & _ & _ & IXC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CPC, SBC, IMC, IXC. unfold OD_IDX in IXC.
      pose proof (OD_SBUF_room L L0) as SBROOM.
      assert (RUL : L <= roundup64 L) by apply roundup64_ge.
      assert (LWS' : Z.of_nat (length ws) = roundup64 L + 9) by (rewrite LWS3; lia).

      pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, OD_IDX L); (pim, IMPL, 96)] _ _ _ HEAP3) as HEAPSB. cbn [app] in HEAPSB.
      pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPSB ltac:(do 2 right; left; reflexivity)) as D_SB_IX.
      pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPSB ltac:(do 3 right; left; reflexivity)) as D_SB_IM.
      pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAPSB ltac:(do 4 right; left; reflexivity)) as D_SB_CP.
      unfold OD_IDX in D_SB_IX.

      pose proof THIS3 as THISC. unfold impl_cells16 in THISC.
      set (mid1 := [CB 4 p28; C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 p50; C8 (Z_to_bv 64 OC); C8 (Z_to_bv 64 IA)]).
      assert (WF1 : cells_wf mid1).
      { destruct THISC as [[Hwf _] _]. cbn [cells_wf] in Hwf. subst mid1. cbn [cells_wf].
        destruct Hwf as (_ & _ & _ & _ & _ & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & _). repeat split; assumption. }
      pose proof (rw_cells_merge usegs m3 IMPL [C8 (Z_to_bv 64 SJ_DPI_VPTR); C4 (Z_to_bv 64 (Z.of_nat (length idxs))); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt] mid1
                    [C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 L); C8 docv] THISC) as TH1.
      pose proof (rw_cells_merge usegs m3 IMPL ([C8 (Z_to_bv 64 SJ_DPI_VPTR); C4 (Z_to_bv 64 (Z.of_nat (length idxs))); CB 4 p12; C8 (Z_to_bv 64 IDX); C4 nxt] ++ [CB (cells_size mid1) (cells_bytes mid1); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 L)])
                    [C8 docv] [] TH1) as TH2.
      clear TH1 THISC. cbn [app] in TH2. change (cells_size mid1) with 44%nat in TH2. change (cells_size [C8 docv]) with 8%nat in TH2.

      pose proof VR3 as (_ & _ & SV3 & _).
      pose proof (rw_cells_join _ _ _ _ _ SV3 XFD2 ltac:(cbn [cells_size csize Nat.add]; lia)) as HJ1.
      pose proof (rw_cells_join _ _ _ _ _ HJ1 SAVE2 ltac:(cbn [app cells_size csize Nat.add]; lia)) as HI3. cbn [app] in HI3. clear HJ1 SV3.
      lazymatch type of HI3 with rw_cells _ _ _ ?hi =>
      set (E := mkOdEnv ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo BUF SB (OD_SBUF L) IMPL IDX (length ws) COPY (od_action d) (od_doc d) idxs
                        (Z_to_bv 64 SJ_DPI_VPTR) p12 nxt (cells_bytes mid1) (cells_bytes [C8 docv]) (cells_bytes [C1 (Z_to_bv 8 0); CB 7 j305'])
                        (Z_to_bv 64 L) (Z_to_bv 64 4294967295) (Z_to_bv 64 1024) (Z_to_bv 64 L) hi m3) end.
      pose proof BRC as (_ & CP16 & _). pose proof BRSB as (_ & SB16 & _). pose proof BRIM as (_ & IM16 & _). pose proof BRIX as (_ & IX16 & _).
      assert (OKU : od_oku E).
      { unfold E. constructor; cbn [o_sp o_BUF o_COPY o_SB o_IDX o_IMPL].
        - exact AL16.
        - clear - CP0 CB1. lia.
        - clear - CP0 CPC CEIL_RANGE__ Elen0. unfold zlength in *. lia.
        - exact SB0.
        - clear - IX0 IX16. pose proof (Z.mod_divide IDX 16 ltac:(lia)) as [H _]. destruct (H IX16) as [q Hq]. split; [lia|]. rewrite Hq. replace (q * 16) with (4 * q * 4) by lia. apply Z.mod_mul. lia.
        - clear - IM0 IM16. pose proof (Z.mod_divide IMPL 16 ltac:(lia)) as [H _]. destruct (H IM16) as [q Hq]. split; [lia|]. rewrite Hq. replace (q * 16) with (2 * q * 8) by lia. apply Z.mod_mul. lia. }
      assert (OK : od_ok E).
      { unfold E. constructor; cbn [o_bs o_idxs o_lo o_sp o_BUF o_SB o_CAP o_IMPL o_IDX o_icap o_act o_vptr]; unfold S1_LEN_MAX, OD_FRAME, OD_NEED, OD_GTOP, OD_DPI_VPTR, tokn;
          rewrite <- ?EL.
        - exact BOK.
        - exact S1O.
        - exact LMAX.
        - exact GLO.
        - clear - LO'. lia.
        - clear - SPB B63. lia.
        - clear - BUFR CB1 CB2 CPC CEIL' EL Elen0. unfold blen, zlength in *. lia.
        - clear - SB0 SBC CEIL'. lia.
        - exact SBROOM.
        - exact SBS.
        - clear - IM0 IMC CEIL'. lia.
        - rewrite LWS'. clear - IX0 IXC CEIL'. lia.
        - rewrite LWS'. clear - NLE RUL. lia.
        - apply od_action_range. exact PRNG.
        - reflexivity.
        - clear - D_SB_CP CB1 CB2 EL Elen0. unfold blen, zlength in *. lia.
        - rewrite LWS'. clear - D_SB_IX. lia.
        - clear - D_SB_IM. lia. }
      assert (PRE : OD_PRE E m3).
      { unfold OD_PRE, E, od_parser_cells, dpi_cells, idx_ok, od_vt_cells, OD_DPI_VPTR, OD_GOT_TABS, OD_PSTR, tokn, Sj_stage1_kit.wz.
        cbn [o_bs o_idxs o_lo o_sp o_BUF o_SB o_CAP o_IMPL o_IDX o_icap o_act o_vptr o_p12 o_nxt o_mid o_docj o_j304 o_w320 o_w328 o_w336 o_w344 o_hi o_m0 o_COPY].
        rewrite <- ?EL.
        replace (bv_unsigned sp + -496) with sp0 by lia. replace (bv_unsigned sp + -208) with (sp0 + 288) by lia. replace (bv_unsigned sp + -152) with (sp0 + 344) by lia.
        pose proof LXS3 as (_ & _ & _ & _ & VTD & GTAB).
        split; [exists jl3; exact LOW3|]. split; [exact PA3'|]. split; [exact HI3|]. split; [exact TH2|].
        split. { exists ws. split; [exact ARR3|]. split; [reflexivity| exact FIRSTN3]. }
        split; [exact BUFB3|]. split; [exact WRSB3|].
        split. { do 9 eexists. exact VTD. }
        split; [exact GTAB|]. split; [exact MI3| exact ST3]. }
      rewrite Esp0, EL.
      eapply evt_eq; [| eapply (HIT E OK OKU) with (m1 := m3); [exact PRE| exact FRM| reflexivity|]].
      { cbv delta [mkR E o_sp o_gp o_tp o_BUF o_bs o_act o_COPY OD_ITER]. reflexivity. }
      unfold od_exit_k. intros st v144 v176 v184 v200 v208 v216 qra qt0 qt1 qt2 qs1 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 qs2 qs3 qs5 qs6 qs7 qs8 qs9 qs10 qs11 qt3 qt4 qt5 qt6 qF qfc mq FRM1 INV.
      destruct (odinv_low _ _ _ _ _ _ _ _ _ INV) as ((j & LOWq) & C176 & MIq & STq & MUq & WMq).
      unfold E in LOWq, C176, STq, MUq, WMq. cbn [o_sp o_lo o_SB o_CAP o_m0 o_COPY] in LOWq, C176, STq, MUq, WMq.
      unfold E. cbn [o_sp o_gp o_tp o_act]. unfold OD_EXIT.
      replace (bv_unsigned sp + -496) with (bv_unsigned sp - 496) by lia.
      ihere. cbv beta. to_implM. rewrite <- TPE.
      eapply (od_exit_it HF ra sp) with (B := B) (lo := lo) (canary := canary) (m0 := m) (ncp := len0 + 64) (pcp := pcp) (COPY := COPY);
        [exact HEAP| exact LXS| exact SEW| exact SSP| exact SPB| exact B63| exact CEIL| exact GLO| exact LO| exact TP| exact AL16| exact CAPB| exact FRM1| exact C176|].
      rewrite <- Esp0 in *.
      eapply exit_inv_munch with (m3 := m3) (m1 := mq) (j := j);
        [exact HEAP| exact CEIL| exact GLO| clear - LO' Esp0; lia| clear - SPB Esp0; lia| exact XI3| exact MUq| exact WMq| exact MIq| exact STq| exact LOWq].
    -
      if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
      ihere. to_implM. rewrite Esp0. rewrite <- TPE.
      eapply (od_exit_err HF ra sp) with (B := B) (lo := lo) (canary := canary) (m0 := m) (ncp := len0 + 64) (cpo := cpo);
        [exact HEAP| exact LXS| exact SEW| exact SSP| exact SPB| exact B63| exact CEIL| exact GLO| exact LO| exact TP| exact AL16| exact CAPB| exact FRM| |].
      + intros ->. destruct DOC2 as (E & _). exact E.
      + rewrite <- Esp0. exact XI3.
  Qed.
End Proofs.
End WithCeiling0.
