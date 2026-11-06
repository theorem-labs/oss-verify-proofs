(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase ABytes AModelFacts ASecFacts ARep ALayout AHeapP ARepKit ARepFrame ARepExt AFreeGeo AFreeRep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeRead. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.AFreeRead. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AC6U.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Definition ov_set (ov : annOV) (p : aptr) (bs : list byte) : annOV :=
  mkAnnOV (fun q => if N.eqb q p then Some bs else @ann_ov ov q) (@ann_ovs ov).

Definition ov_agree (ov ov' : annOV) (X : aconc) : Prop :=
  forall b p, In b (x_busy X) -> xb_st b = BLive p -> @live_bytes ov' p (xb_n b) = @live_bytes ov p (xb_n b).

Lemma slot_bytes_agree : forall ov ov' X S c k, ov_agree ov ov' X ->
  @slot_shadow_bytes ov' S (busy_of X c k) = @slot_shadow_bytes ov S (busy_of X c k).
Proof.
  intros ov ov' X S c k AG. destruct (busy_of X c k) as [b|] eqn:EB; [| reflexivity].
  pose proof EB as EB'. unfold busy_of in EB'. apply find_some in EB'. destruct EB' as [HIn _].
  unfold slot_shadow_bytes. destruct (xb_st b) as [p| |] eqn:ES; try reflexivity.
  rewrite (AG b p HIn ES). reflexivity.
Qed.

Lemma aslot_shadow_agree : forall ov ov' L st X m c, ov_agree ov ov' X ->
  @aslot_shadow ov L st X m c -> @aslot_shadow ov' L st X m c.
Proof.
  intros ov ov' L st X m c AG [SL UND]. split; [| exact UND].
  intros k Hk. rewrite (slot_bytes_agree ov ov' X _ c k AG). exact (SL k Hk).
Qed.

Theorem AREP_ov_agree : forall ov ov' H L st X m, ov_agree ov ov' X ->
  @AREP rc ov H L st X m -> @AREP rc ov' H L st X m.
Proof.
  intros ov ov' H L st X m AG AR.
  destruct AR as (WF & RT & INST & THR & CLS & REST).
  split; [exact WF|]. split; [exact RT|]. split; [exact INST|]. split; [exact THR|]. split; [| exact REST].
  intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
  split; [exact REG|]. split; [exact FARR|]. split; [exact SLOTS|]. exact (aslot_shadow_agree ov ov' L st X m c AG SHADOW).
Qed.

Theorem AHEAP_P_ov_agree : forall ov ov' H L RNG st LB m,
  (forall p ch, (a_live st) !! p = Some ch -> @ann_ov ov' p = @ann_ov ov p) ->
  @AHEAP_P rc ov H L RNG st LB m -> @AHEAP_P rc ov' H L RNG st LB m.
Proof.
  intros ov ov' H L RNG st LB m AG (ALO & ARNG & [X [AR BL]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL]. eapply (AREP_ov_agree ov ov'); [| exact AR].
  intros b p Hb ES. destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY b Hb) as [_ M]. rewrite ES in M. destruct M as (_ & _ & _ & _ & _ & LV). unfold live_bytes. rewrite (AG p _ LV). reflexivity.
Qed.

Definition ov_clear_from (ov : annOV) (p0 : aptr) : annOV :=
  mkAnnOV (fun q => if N.ltb q p0 then @ann_ov ov q else None) (@ann_ovs ov).
Lemma ov_clear_from_fresh : forall ov p0, @ann_ov (ov_clear_from ov p0) p0 = None.
Proof. intros ov p0. cbn. rewrite N.ltb_irrefl. reflexivity. Qed.
Theorem AHEAP_P_clear_fresh : forall ov H L RNG st LB m,
  @AHEAP_P rc ov H L RNG st LB m -> @AHEAP_P rc (ov_clear_from ov (a_next st)) H L RNG st LB m.
Proof.
  intros ov H L RNG st LB m AH. eapply AHEAP_P_ov_agree; [| exact AH].
  intros p ch LV. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  pose proof (FRESH p ch LV) as LT. cbn. apply N.ltb_lt in LT. rewrite LT. reflexivity.
Qed.

Lemma ov_read : forall (m : amem) A n, 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> m (wa (A + i)) <> None) -> exists bs, length bs = n /\ bytes_at asegs m A bs.
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A A0 A1 PR.
  - exists []. split; [reflexivity|]. split; [exact A0|]. split; [cbn in *; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (IH (A + 1)) as (bs & LB & (B0 & B1 & BR)); [lia | lia | |].
    { intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply PR. lia. }
    pose proof (PR 0 ltac:(lia)) as P0. rewrite Z.add_0_r in P0.
    destruct (m (wa A)) as [b0|] eqn:E; [| congruence].
    exists (b0 :: bs). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; [cbn; rewrite Z.add_0_r; unfold mrd; rewrite E; reflexivity|].
    cbn [nth_error]. rewrite <- (BR i ltac:(cbn in Hi; lia)). f_equal. f_equal. lia.
Qed.

Section Remark.
Variable ov : annOV.
Variable H : aholes.
Hypothesis HL : ahole_laws H.
Variables (L : alayout) (st : astate) (X : aconc) (m m' : amem) (p : aptr) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Hypothesis ALO : alayout_ok L.
Hypothesis AR : @AREP rc ov H L st X m.
Hypothesis XB : x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let g := granules n.
Let W := [(shad UB, shad UB + g)].
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis RDM : forall i, 0 <= i < g -> m' (wa (shad UB + i)) <> None.

Lemma Ksh : forall A k', (A + k' <= shad UB \/ shad UB + g <= A) -> disjoint_from W A k'.
Proof. intros A k' D. unfold W. cbn [disjoint_from]. split; [exact D| exact I]. Qed.

Lemma slot_bytes_set_other : forall bs c' k', (c' <> c \/ k' <> k) ->
  @slot_shadow_bytes (ov_set ov p bs) (size_of_class c') (busy_of X c' k') = @slot_shadow_bytes ov (size_of_class c') (busy_of X c' k').
Proof.
  intros bs c' k' NE. destruct (busy_of X c' k') as [b|] eqn:EB; [| reflexivity].
  pose proof EB as EB'. unfold busy_of in EB'. apply find_some in EB'. destruct EB' as [HIn HP].
  apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
  unfold slot_shadow_bytes. destruct (xb_st b) as [q| |] eqn:ES; try reflexivity.
  unfold live_bytes, ov_set. cbn [ann_ov]. destruct (N.eqb_spec q p) as [->|NQ]; [| reflexivity].
  exfalso. destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNIQ).
  assert (HF : In (bfreed p c k n b1 ctx) (x_busy X)) by (rewrite XB; apply in_app_iff; right; left; reflexivity).
  pose proof (UNIQ b (bfreed p c k n b1 ctx) HIn HF ltac:(rewrite ES; reflexivity) ltac:(exists p; exact ES)) as EQ.
  subst b. cbn [xb_class xb_slot bfreed] in HP1, HP2. destruct NE as [NE|NE]; [apply NE; symmetry; exact HP1| apply NE; symmetry; exact HP2].
Qed.

Theorem AREP_remark1 :
  exists bs, length bs = Z.to_nat g /\ bytes_at asegs m' (shad UB) bs /\ @AREP rc (ov_set ov p bs) H L st X m'.
Proof.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE0 & N0 & FIT0 & B10 & AT0 & CTX0).
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (CG1 & CG2 & CG3 & CG4 & CG5 & CG6 & CG7 & CG8 & CG9 & CG10 & CG11 & CG12 & CG13 & CG14).
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GF & GLO & GHI & GRL & GRH).
  pose proof (slot_geo L st X c k ALO WF HC KR) as (SG1 & SG2 & SGAL & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9 & SG10 & SG11 & SG12).
  fold S AB UB in CG1, CG2, CG3, CG4, CG5, CG6, CG7, CG8, CG11, CG14, SE, GF, GLO, GHI, GRL, GRH, SG1, SG2, SGAL, SG3, SG4, SG7, SG8, SG9, SG10.
  fold g in GE, GF.
  assert (G0' : 0 <= g) by (rewrite <- GE; exact G0).

  assert (WB : 0x2008fff7000 <= shad UB /\ shad UB + g <= 0x10007fff8000 /\ shad AB <= shad UB /\ shad UB + g <= shad AB + shlen S).
  { rewrite SE. lia. }
  destruct WB as (WB1 & WB2 & WB3 & WB4).

  destruct (CLS c HC) as (REGc & FARRc & SLOTSc & SHADOWc).
  destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj SLOTSc SHADOWc)) as (_ & _ & _ & _ & SHA & SHU & SHR).
  fold S AB UB in SHA, SHU, SHR. rewrite GE in SHU, SHR.

  assert (WRU : wr_at asegs m' (shad UB) (Z.of_nat (Z.to_nat g))).
  { destruct SHU as [_ (W0 & W1 & WR)]. cbn [cells_size csize] in W1, WR. rewrite Nat.add_0_r in W1, WR.
    split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM. apply WR. exact Hi. }
  destruct (ov_read m' (shad UB) (Z.to_nat g) ltac:(clear -WB1; lia) ltac:(clear -WB2 G0'; lia)
              ltac:(intros i Hi; apply RDM; clear -Hi G0'; lia)) as (bs & LBS & BAT).
  exists bs. split; [exact LBS|]. split; [exact BAT|].
  assert (SHU' : rw_cells asegs m' (shad UB) [CB (Z.to_nat g) bs]).
  { split; [split|].
    - cbn. split; [exact LBS| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BAT.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WRU. }
  assert (SHA' : rw_cells asegs m' (shad AB) [CB (Z.to_nat (shlen (rz_size n))) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (rz_size n))))]).
  { eapply cells_frame; [exact SHA | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    apply Ksh. left. rewrite SE. lia. }
  assert (SHR' : rw_cells asegs m' (shad UB + g) [CB (Z.to_nat (shlen S - shlen (rz_size n) - g))
                                                    (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen (rz_size n) - g)))]).
  { eapply cells_frame; [exact SHR | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    apply Ksh. right. lia. }
  assert (NEWCELL : rw_cells asegs m' (shad AB) [CB (Z.to_nat (shlen S)) (@slot_shadow_bytes (ov_set ov p bs) S (busy_of X c k))]).
  { rewrite (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF).
    unfold slot_shadow_bytes. cbn [xb_n xb_st bfreed]. unfold live_bytes, ov_set. cbn [ann_ov]. rewrite N.eqb_refl.
    fold g. rewrite LBS, PeanoNat.Nat.eqb_refl.
    replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SHU', SHR' by (rewrite SE; lia).
    replace (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + g) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat g)) in SHR' by lia.
    pose proof (cb_app m' _ _ _ _ _ SHA' (cb_app m' _ _ _ _ _ SHU' SHR')) as FIN.
    replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat g + Z.to_nat (shlen S - shlen (rz_size n) - g)))%nat with (Z.to_nat (shlen S)) in FIN by lia.
    exact FIN. }

  pose proof atop_range as ATR.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_fake L ALO) as FK.
  unfold aobj, sclr, KLS in OT, OC, ORS, ON, OS, FK. pose proof (ao_space L ALO) as RSP.

  assert (Kout : forall A k', (A + k' <= 2147450880 \/ 17594333495296 <= A) -> disjoint_from W A k').
  { intros A k' HB. apply Ksh. clear -HB WB1 WB2. lia. }
  assert (Kimg : forall A k', 0 <= A -> 0 <= k' -> A + k' <= AIMG_HI -> disjoint_from W A k').
  { intros A k' H1 H2 H3. apply Kout. unfold AIMG_HI in H3. left. lia. }
  assert (Kres : forall A k', al_res L <= A -> 0 <= k' -> A + k' <= al_res L + 137439023104 -> disjoint_from W A k').
  { intros A k' H1 H2 H3. apply Kout. clear -H1 H2 H3 ORS ORH. lia. }
  assert (Kt : forall A k', al_t L <= A -> 0 <= k' -> A + k' <= al_t L + 4096 -> disjoint_from W A k').
  { intros A k' H1 H2 H3. apply Kout. clear -H1 H2 H3 OT. lia. }
  assert (Kctx : forall A k', al_ctx L <= A -> 0 <= k' -> A + k' <= al_ctx L + 65536 -> disjoint_from W A k').
  { intros A k' H1 H2 H3. apply Kout. clear -H1 H2 H3 OC. lia. }

  assert (RGC : forall c', 1 <= c' < K_NUM_CLASSES -> c' <> c ->
            forall A k', shad (aregion L c') <= A -> A + k' <= shad (aregion L c') + 536870912 -> disjoint_from W A k').
  { intros c' Hc' NE A k' H1 H2. apply Ksh.
    pose proof (aregion_mod L c' SAL) as RM'. pose proof (aregion_mod L c SAL) as RMc.
    assert (E29 : forall a, a mod 8 = 0 -> shad (a + K_REGION) = shad a + 536870912).
    { intros a Ha. rewrite shad_add_shlen by (clear -Ha; Z.div_mod_to_equations; lia). unfold K_REGION. rewrite shlen_div. reflexivity. }
    assert (INR : shad (aregion L c) <= shad UB /\ shad UB + g <= shad (aregion L c) + 536870912).
    { split; [lia|]. eapply Z.le_trans; [exact WB4|]. eapply Z.le_trans; [exact GRH|].
      rewrite <- (E29 (aregion L c)) by (clear -RMc; Z.div_mod_to_equations; lia).
      rewrite <- shad_add_shlen by (clear -RMc; Z.div_mod_to_equations; lia). apply shad_mono. unfold K_REGION, K_FREEARR_OFF in *. clear -SG6. lia. }
    destruct (Z.lt_ge_cases c' c) as [LT|GEc].
    - left. pose proof (regions_sep L c' c LT) as RS. apply shad_mono in RS. rewrite (E29 (aregion L c')) in RS by (clear -RM'; Z.div_mod_to_equations; lia).
      clear -H2 RS INR. lia.
    - right. pose proof (regions_sep L c c' ltac:(clear -GEc NE; lia)) as RS. apply shad_mono in RS. rewrite (E29 (aregion L c)) in RS by (clear -RMc; Z.div_mod_to_equations; lia).
      clear -H1 RS INR. lia. }

  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c0 Hc0. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c0 Hc0) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc0. apply Kt; clear -Hc0; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
  split.
  { intros c0 Hc0. destruct (CLS c0 Hc0) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c0 Hc0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c0 Hc0) as [QS QS16]. pose proof (aregion_mod L c0 SAL) as RM. pose proof Hc0 as Hc0'. unfold K_NUM_CLASSES in Hc0.
    assert (RI : al_res L <= aregion L c0 /\ aregion L c0 + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc0 RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.

    assert (KSH : forall o d, 0 <= o -> 0 <= d -> o mod 8 = 0 -> o + d <= K_REGION -> (c0 = c -> AB + S <= aregion L c + o) ->
                   disjoint_from W (shad (aregion L c0 + o)) (shlen d)).
    { intros o d Ho Hd Mo OD AFTER. destruct (Z.eq_dec c0 c) as [->|NEc].
      - apply Ksh. right. eapply Z.le_trans; [exact WB4|]. apply shad_sep; [exact (AFTER eq_refl)| clear -SGAL; Z.div_mod_to_equations; lia].
      - apply (RGC c0 Hc0' NEc).
        + apply shad_mono. clear -Ho. lia.
        + rewrite <- shad_add_shlen by (clear -RM Mo; Z.div_mod_to_equations; lia).
          replace 536870912 with (shlen K_REGION) by (unfold K_REGION; rewrite shlen_div; reflexivity).
          rewrite <- shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). apply shad_mono. clear -OD. lia. }
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc0 RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + unfold afreearr. apply KSH; [unfold K_FREEARR_OFF; clear; lia | clear -Q5 Q6; lia | unfold K_FREEARR_OFF; reflexivity
                                    | unfold K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; clear -Q6; lia |].
        intros ->. unfold K_FREEARR_OFF in *. clear -SG4 SG5 SG6. lia.
    - eapply (aslots_update L W m m' MU WM st st X X c0 (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k0 Hk0 _. pose proof (slot_in_region L st c0 k0 ltac:(clear -QS; lia) (proj1 Q1) Hk0) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    -
      destruct SHADOW as [SL UND]. split.
      + intros k0 Hk0. destruct (Z.eq_dec c0 c) as [EC|NEc]; [destruct (Z.eq_dec k0 k) as [EK|NEk]|].
        * subst c0 k0. exact NEWCELL.
        * subst c0. rewrite (slot_bytes_set_other bs c k0 (or_intror NEk)).
          eapply cells_frame; [exact (SL k0 Hk0) | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply shlen_nonneg; clear -QS; lia).
          apply Ksh. pose proof (slot_aligned L c k0 SAL Hc0') as AL0.
          destruct (slots_disjoint L c k0 k ltac:(clear -Hk0; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; fold S AB in D.
          -- left. eapply Z.le_trans; [| exact WB3]. apply shad_sep; [exact D| clear -AL0; Z.div_mod_to_equations; lia].
          -- right. eapply Z.le_trans; [exact WB4|]. apply shad_sep; [exact D| clear -SGAL; Z.div_mod_to_equations; lia].
        * rewrite (slot_bytes_set_other bs c0 k0 (or_introl NEc)).
          eapply cells_frame; [exact (SL k0 Hk0) | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply shlen_nonneg; clear -QS; lia).
          pose proof (slot_in_region L st c0 k0 ltac:(clear -QS; lia) (proj1 Q1) Hk0) as (P5 & P4 & P0).
          pose proof (slot_aligned L c0 k0 SAL Hc0') as AL0.
          apply (RGC c0 Hc0' NEc); [apply shad_mono; exact P5|].
          rewrite <- shad_add_shlen by (clear -AL0; Z.div_mod_to_equations; lia).
          replace 536870912 with (shlen K_REGION) by (unfold K_REGION; rewrite shlen_div; reflexivity).
          rewrite <- shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
          unfold K_REGION, K_FREEARR_OFF in *. clear -P4 Q1 Q2. lia.
      + eapply fill_frame; [exact UND | exact MU | exact WM |]. intros POS.
        pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM.
        apply KSH; [clear -Q1; lia | clear -Q1; lia | clear -AM; Z.div_mod_to_equations; lia | unfold K_REGION, K_FREEARR_OFF in *; clear -Q1 Q2; lia |].
        intros ->. clear -SG4. lia. }

  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  split.
  { eapply (hq_frame _ HL L st st X X m m' W); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched, W. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold AINSTANCE in *.
      split; [clear -WB1 WB2 OT; lia|].
      split; [clear -WB1; lia|].
      split; [clear -WB1; lia|].
      split; [clear -WB1; lia|].
      intros b Hb. destruct (BB b Hb) as [B1 B2]. destruct (xb_st b); [exact I| |]; clear -WB1 WB2 B1 B2 ORS ORH; lia.
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { assert (INS : shad (al_space_beg L) + 536870912 <= shad UB /\ shad UB + g <= shad (al_space_beg L) + 17179869696).
    { pose proof (aregion_mod L c SAL) as RMc.
      assert (SB8 : al_space_beg L mod 8 = 0) by (unfold K_ALIGN in SAL; clear -SAL; Z.div_mod_to_equations; lia).
      split.
      - eapply Z.le_trans; [| exact WB3]. eapply Z.le_trans; [| exact GRL].
        replace 536870912 with (shlen K_REGION) by (unfold K_REGION; rewrite shlen_div; reflexivity).
        rewrite <- shad_add_shlen by exact SB8. apply shad_mono. unfold aregion, K_REGION, K_NUM_CLASSES in *. clear -HC. lia.
      - eapply Z.le_trans; [exact WB4|]. eapply Z.le_trans; [exact GRH|].
        rewrite <- shad_add_shlen by (clear -RMc; Z.div_mod_to_equations; lia).
        replace 17179869696 with (shlen (K_SPACE_SIZE + 4096)) by (unfold K_SPACE_SIZE; rewrite shlen_div; reflexivity).
        rewrite <- shad_add_shlen by exact SB8. apply shad_mono. unfold aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_NUM_CLASSES in *.
        change (2^37) with 137438953472. clear -HC SG6. lia. }
    eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | | | apply sec_same_refl].
    - unfold sec_untouched, aknown, W. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. right. left. clear -INS Ha. lia.
    -
      unfold W. apply AC6U.c6u_cons; [| apply AC6U.c6u_nil]. cbn [fst snd]. apply (AC6U.c6p_std L _ _ ALO). intros _. do 4 right. left.
      assert (SHBx : 0x7fff7000 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869696 <= 0x10007fff8000).
      { rewrite !shad_div. unfold ASHOFF. pose proof atop_range as ATRx. pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_res_hi L ALO) as ORHx.
        pose proof (ao_space L ALO) as RSPx. clear -RSPx ORSx ORHx ATRx. Z.div_mod_to_equations. lia. }
      clear -INS SHBx. lia. }
  split.
  { eapply (hd_frame _ HL L m m' W); [exact HD | exact MU | exact WM |].
    unfold W. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha.
    clear -Ha WB1 WB2 ON OS. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
  intros c0 Hc0. destruct (PERC c0 Hc0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof Hc0 as Hc0'. unfold K_NUM_CLASSES in Hc0.
  pose proof (aregion_mod L c0 SAL) as RM.
  assert (KSH : forall o d, 0 <= o -> 0 <= d -> o mod 8 = 0 -> o + d <= K_REGION -> (c0 = c -> AB + S <= aregion L c + o) ->
                 disjoint_from W (shad (aregion L c0 + o)) (shlen d)).
  { intros o d Ho Hd Mo OD AFTER. destruct (Z.eq_dec c0 c) as [->|NEc].
    - apply Ksh. right. eapply Z.le_trans; [exact WB4|]. apply shad_sep; [exact (AFTER eq_refl)| clear -SGAL; Z.div_mod_to_equations; lia].
    - apply (RGC c0 Hc0' NEc).
      + apply shad_mono. clear -Ho. lia.
      + rewrite <- shad_add_shlen by (clear -RM Mo; Z.div_mod_to_equations; lia).
        replace 536870912 with (shlen K_REGION) by (unfold K_REGION; rewrite shlen_div; reflexivity).
        rewrite <- shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). apply shad_mono. clear -OD. lia. }
  eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c0 Hc0') | reflexivity | reflexivity | |].
  - intros POS. apply KSH; [clear -Q1; lia | unfold K_FREEARR_OFF in *; clear -Q2; lia | unfold K_USER_MAP in Q4; clear -Q4; Z.div_mod_to_equations; lia
                           | unfold K_FREEARR_OFF, K_REGION; clear -Q1 Q2; lia |].
    intros ->. clear -SG4 SG5. lia.
  - intros POS. unfold afreearr. rewrite <- Z.add_assoc.
    apply KSH; [unfold K_FREEARR_OFF; clear -Q5 Q6; lia | unfold K_FREEARR_MAX in *; clear -Q6; lia
               | unfold K_FREEARR_OFF, K_FREEARR_MAP in *; clear -Q7; Z.div_mod_to_equations; lia
               | unfold K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; clear -Q5 Q6; lia |].
    intros ->. unfold K_FREEARR_OFF in *. clear -SG4 SG5 SG6 Q5 Q6. lia.
Qed.

Lemma remark_geo : 0x2008fff7000 <= shad UB /\ shad UB + g <= 0x10007fff8000
  /\ shad (al_res L) <= shad UB /\ shad UB + g <= shad (al_res L + 137439023104).
Proof.
  pose proof AR as AR0. destruct AR0 as (WF & _).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE0 & N0 & FIT0 & B10 & AT0 & CTX0).
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GF & GLO & GHI & GRL & GRH).
  pose proof (slot_geo L st X c k ALO WF HC KR) as (SG1 & SG2 & SGAL & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9 & SG10 & SG11 & SG12).
  fold S AB UB in SE, GF, GLO, GHI, GRL, GRH, SG1, SG2, SGAL, SG3, SG4, SG7, SG8, SG9, SG10. fold g in GE, GF.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  split; [rewrite SE; lia|]. split; [rewrite SE; lia|].
  split. { eapply Z.le_trans; [| rewrite SE; instantiate (1 := shad AB); lia]. apply shad_mono. clear -SG7 RSP. lia. }
  eapply Z.le_trans; [instantiate (1 := shad AB + shlen S); rewrite SE; lia|].
  apply shad_sep; [| clear -SGAL; Z.div_mod_to_equations; lia]. unfold K_SPACE_SIZE in SG8. change (2^37) with 137438953472 in SG8. clear -SG8 RSP. lia.
Qed.

Lemma remark_fake : disjoint_from W (al_t L + 72) 8 /\ fake_untouched L W.
Proof.
  destruct remark_geo as (WB1 & WB2 & WR1 & WR2).
  pose proof (ao_t L ALO) as OT. pose proof (ao_fake L ALO) as FK. pose proof (ao_dtls L ALO) as OD. pose proof (ao_res L ALO) as ORS.
  pose proof (ad_fake_res L ALO) as DFR. unfold adisj in DFR.
  unfold aobj, sclr, KLS in OT, FK, OD, ORS.
  split. { apply Ksh. clear -WB1 WB2 OT. lia. }
  unfold fake_untouched, W. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
  assert (SHR : shad (al_res L + 137439023104) <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad (al_res L)).
  { destruct DFR as [D|D]; [right | left].
    - apply shad_sep; [exact D | clear -FK; Z.div_mod_to_equations; lia].
    - apply shad_mono. exact D. }
  split; [clear -WB1 WB2 FK; lia|].
  split; [clear -WR1 WR2 SHR; lia|].
  split; [clear -WB1 WB2 OD; lia|].
  repeat split; clear -WB1; lia.
Qed.
End Remark.

Theorem AHEAP_P_remark1 : forall (ov : annOV) H (HL : ahole_laws H) L RNG st LB m m' p A n,
  @AHEAP_P rc ov H L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  munch [(shad A, shad A + granules n)] m m' -> wmono asegs m m' ->
  (forall i, 0 <= i < granules n -> m' (wa (shad A + i)) <> None) ->
  exists bs, length bs = Z.to_nat (granules n) /\ bytes_at asegs m' (shad A) bs /\ @AHEAP_P rc (ov_set ov p bs) H L RNG st LB m'.
Proof.
  intros ov H HL L RNG st LB m m' p A n (ALO & ARNG & [X [AR BL]] & HFK) Hin PRIM MU WM RDM.
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & _ & NP & _). congruence. }
  destruct b as [c k n' s0 b1 ctx]. cbn [xb_st xb_n] in Sb, Nb. subst s0 n'.
  unfold xb_user, xb_alloc in Ub. cbn [xb_class xb_slot xb_n] in Ub.
  destruct (in_split _ _ Hb) as (l1 & l2 & XB). change (mkXBusy c k n (BLive p) b1 ctx) with (bfreed p c k n b1 ctx) in XB.
  rewrite <- Ub in MU, RDM |- *.
  destruct (AREP_remark1 ov H HL L st X m m' p c k n b1 ctx l1 l2 ALO AR XB MU WM RDM) as (bs & LBS & BAT & AR').
  destruct (remark_fake ov H L st X m p c k n b1 ctx l1 l2 ALO AR XB) as [DT FU].
  exists bs. split; [exact LBS|]. split; [exact BAT|].
  split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
  eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM | exact DT | exact FU].
Qed.

Lemma AHEAP_P_live_cell : forall (ov : annOV) H L RNG st LB m p A n,
  @AHEAP_P rc ov H L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) (@live_bytes ov p n)]
  /\ 0x2008fff7000 <= shad A /\ shad A + granules n <= 0x10007fff8000.
Proof.
  intros ov H L RNG st LB m p A n (ALO & ARNG & [X [AR BL]] & HFK) Hin PRIM.
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & _ & NP & _). congruence. }
  destruct b as [c k n' s0 b1 ctx]. cbn [xb_st xb_n] in Sb, Nb. subst s0 n'.
  unfold xb_user, xb_alloc in Ub. cbn [xb_class xb_slot xb_n] in Ub.
  destruct (in_split _ _ Hb) as (l1 & l2 & XB). change (mkXBusy c k n (BLive p) b1 ctx) with (bfreed p c k n b1 ctx) in XB.
  rewrite <- Ub.
  destruct (remark_geo ov H L st X m p c k n b1 ctx l1 l2 ALO AR XB) as (WB1 & WB2 & _ & _).
  split; [| split; [exact WB1| exact WB2]].
  pose proof AR as (WF & _ & _ & _ & CLS & _).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE0 & N0 & FIT0 & _).
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & GE & _).
  destruct (CLS c HC) as (_ & _ & SLOTSc & SHADOWc).
  destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj SLOTSc SHADOWc)) as (_ & _ & _ & _ & _ & SHU & _).
  rewrite GE in SHU. exact SHU.
Qed.

Lemma hb_ids_inj : forall (LB : list ablock) p A n A' n', List.NoDup (hb_ids LB) -> In (HB p A n) LB -> In (HB p A' n') LB -> HB p A n = HB p A' n'.
Proof.
  intros LB p A n A' n' ND. induction LB as [|x l IH]; intros Hb Hb'; [destruct Hb|]. cbn [hb_ids flat_map] in ND.
  assert (INID : forall A0 n0, In (HB p A0 n0) l -> In p (hb_ids l)).
  { intros A0 n0 Hy. unfold hb_ids. apply in_flat_map. exists (HB p A0 n0). split; [exact Hy| left; reflexivity]. }
  destruct Hb as [E0|Hb]; destruct Hb' as [E|Hb'].
  - rewrite <- E0. exact E.
  - exfalso. subst x. cbn [ab_kind app] in ND. apply NoDup_cons_iff in ND as [NI _]. exact (NI (INID _ _ Hb')).
  - exfalso. subst x. cbn [ab_kind app] in ND. apply NoDup_cons_iff in ND as [NI _]. exact (NI (INID _ _ Hb)).
  - apply IH; [| exact Hb| exact Hb']. destruct (ab_kind x); cbn [app] in ND; [apply NoDup_cons_iff in ND as [_ ND]; exact ND| exact ND].
Qed.

Lemma cb_overlay : forall (m : amem) A g bs i, rw_cells asegs m A [CB g bs] -> 0x62f000 <= A -> 0 <= i < Z.of_nat (length bs) ->
  m (wa (A + i)) = nth_error bs (Z.to_nat i).
Proof.
  intros m A g bs i [[_ (B0 & B1 & BR)] _] LO Hi. cbn [cells_bytes cbytes] in B1, BR. rewrite app_nil_r in B1, BR.
  specialize (BR (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in BR by lia.
  rewrite <- BR. symmetry. apply (mrd_no_image asegs m 0x62f000 (2^64)); [apply no_image_asan; lia| lia| lia| lia].
Qed.

Theorem AHEAP_P_mark_all : forall H (HL : ahole_laws H) L RNG st LB m (l : list ablock) (ov : annOV),
  @AHEAP_P rc ov H L RNG st LB m -> (forall b, In b l -> In b LB) ->
  exists ov' : annOV, @AHEAP_P rc ov' H L RNG st LB m
    /\ (forall p A n, In (HB p A n) l -> is_primary n = true -> exists bs, @ann_ov ov' p = Some bs /\ length bs = Z.to_nat (granules n))
    /\ (forall q, @ann_ov ov' q <> None -> @ann_ov ov q <> None \/ exists A n, In (HB q A n) l).
Proof.
  intros H HL L RNG st LB m l. induction l as [|b l IH]; intros ov AH SUB.
  - exists ov. split; [exact AH|]. split; [intros p A n []| intros q Hq; left; exact Hq].
  - destruct (IH ov AH ltac:(intros x Hx; apply SUB; right; exact Hx)) as (ov1 & AH1 & MK1 & SP1).
    destruct b as [[p|cls] A n].
    2: { exists ov1. split; [exact AH1|]. split.
         - intros p' A' n' [E|Hin] PR; [discriminate E| exact (MK1 p' A' n' Hin PR)].
         - intros q Hq. destruct (SP1 q Hq) as [S|(A' & n' & Hin)]; [left; exact S| right; exists A', n'; right; exact Hin]. }
    destruct (is_primary n) eqn:PRIM.
    2: { exists ov1. split; [exact AH1|]. split.
         - intros p' A' n' [E|Hin] PR; [injection E as <- <- <-; congruence| exact (MK1 p' A' n' Hin PR)].
         - intros q Hq. destruct (SP1 q Hq) as [S|(A' & n' & Hin)]; [left; exact S| right; exists A', n'; right; exact Hin]. }
    assert (HinLB : In (HB p A n) LB) by (apply SUB; left; reflexivity).
    destruct (AHEAP_P_live_cell ov1 H L RNG st LB m p A n AH1 HinLB PRIM) as (CELL & LO1 & HI1).
    pose proof CELL as [[[LEN _] _] _]. cbn in LEN.
    destruct (AHEAP_P_remark1 ov1 H HL L RNG st LB m m p A n AH1 HinLB PRIM (munch_refl _ _) (wmono_refl _ _)) as (bs & LBS & BAT & AH2).
    { intros i Hi. rewrite (cb_overlay m (shad A) _ _ i CELL ltac:(lia) ltac:(rewrite LEN; unfold granules in *; lia)).
      intros E. apply nth_error_None in E. rewrite LEN in E. unfold granules in *. lia. }
    exists (ov_set ov1 p bs). split; [exact AH2|]. split.
    + intros p' A' n' [E|Hin] PR.
      * injection E as <- <- <-. exists bs. split; [| exact LBS]. unfold ov_set. cbn [ann_ov]. rewrite N.eqb_refl. reflexivity.
      * destruct (MK1 p' A' n' Hin PR) as (bs' & E1 & L1). unfold ov_set. cbn [ann_ov].
        destruct (N.eqb_spec p' p) as [->|NE]; [| exists bs'; split; assumption].

        exists bs. split; [reflexivity|].
        destruct AH1 as (_ & _ & [X1 [_ BL1]] & _). destruct BL1 as (_ & _ & NDI & _).
        assert (EQ : HB p A' n' = HB p A n).
        { apply (hb_ids_inj LB); [exact NDI| apply SUB; right; exact Hin| exact HinLB]. }
        injection EQ as _ <-. exact LBS.
    + intros q Hq. destruct (N.eq_dec q p) as [EQ|NE].
      * right. exists A, n. left. rewrite EQ. reflexivity.
      * unfold ov_set in Hq. cbn [ann_ov] in Hq. apply N.eqb_neq in NE. rewrite NE in Hq.
        destruct (SP1 q Hq) as [S|(A' & n' & Hin)]; [left; exact S| right; exists A', n'; right; exact Hin].
Qed.

Theorem twin_bytes_eq : forall (ov : annOV) H H' L RNG RNG' st st' LB LB' m m' p A n bs,
  @AHEAP_P rc ov H L RNG st LB m -> @AHEAP_P rc ov H' L RNG' st' LB' m' -> In (HB p A n) LB -> In (HB p A n) LB' -> is_primary n = true ->
  @ann_ov ov p = Some bs -> length bs = Z.to_nat (granules n) ->
  forall i, 0 <= i < granules n -> m' (wa (shad A + i)) = m (wa (shad A + i)).
Proof.
  intros ov H H' L RNG RNG' st st' LB LB' m m' p A n bs AH AH' Hin Hin' PRIM E LBS i Hi.
  destruct (AHEAP_P_live_cell ov H L RNG st LB m p A n AH Hin PRIM) as (C1 & LO1 & _).
  destruct (AHEAP_P_live_cell ov H' L RNG' st' LB' m' p A n AH' Hin' PRIM) as (C2 & _ & _).
  assert (LV : @live_bytes ov p n = bs) by (unfold live_bytes; rewrite E, LBS, PeanoNat.Nat.eqb_refl; reflexivity).
  rewrite LV in C1, C2.
  rewrite (cb_overlay m (shad A) _ _ i C1 ltac:(lia) ltac:(rewrite LBS; lia)).
  rewrite (cb_overlay m' (shad A) _ _ i C2 ltac:(lia) ltac:(rewrite LBS; lia)). reflexivity.
Qed.

Lemma AHEAP_P_hb_lt : forall (ov : annOV) H L RNG st LB m p A n,
  @AHEAP_P rc ov H L RNG st LB m -> In (HB p A n) LB -> (p < a_next st)%N.
Proof.
  intros ov H L RNG st LB m p A n (_ & _ & [X [AR BL]] & _) Hin.
  destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & _)|(mb & ms & Lp & _)].
  - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & LV). exact (FRESH p _ LV).
  - exact (FRESH p _ Lp).
Qed.

Definition ov_unset (ov : annOV) (p : aptr) : annOV :=
  mkAnnOV (fun q => if N.eqb q p then None else @ann_ov ov q) (@ann_ovs ov).

Lemma nth_block_shadow_bytes : forall n i, 0 < n -> 0 <= i < granules n ->
  nth_error (block_shadow_bytes n) (Z.to_nat i) = Some (Z_to_bv 8 (if 8 * i + 8 <=? n then 0 else n - 8 * i)).
Proof.
  intros n i Hn Hi. unfold block_shadow_bytes. unfold granules in Hi. rewrite !shlen_div in *.
  destruct (Z.leb_spec (8 * i + 8) n) as [LE|GT].
  - rewrite nth_error_app1 by (rewrite repeat_length; Z.div_mod_to_equations; lia).
    apply nth_error_repeat. Z.div_mod_to_equations; lia.
  - assert (EI : i = n / 8) by (Z.div_mod_to_equations; lia).
    rewrite nth_error_app2 by (rewrite repeat_length; Z.div_mod_to_equations; lia).
    rewrite repeat_length. replace (Z.to_nat i - Z.to_nat (n / 8))%nat with 0%nat by lia.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; [exfalso; Z.div_mod_to_equations; lia|].
    cbn [nth_error]. f_equal. f_equal. Z.div_mod_to_equations; lia.
Qed.

Lemma cb_canon_bytes : forall (m : amem) A n bs, 0 < n -> 0x62f000 <= shad A ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) bs] -> ablock_shadow m A n -> bs = block_shadow_bytes n.
Proof.
  intros m A n bs Hn LO CELL CAN.
  pose proof CELL as [[[LEN _] _] _]. cbn in LEN.
  assert (G0 : 0 <= granules n) by (unfold granules; apply shlen_nonneg; lia).
  apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (Z.to_nat (granules n))) as [LT|GE].
  - rewrite <- (Nat2Z.id k). rewrite (nth_block_shadow_bytes n (Z.of_nat k) Hn ltac:(lia)).
    rewrite <- (cb_overlay m (shad A) _ _ (Z.of_nat k) CELL LO ltac:(rewrite LEN; lia)).
    apply CAN; [lia|]. unfold granules in LT. rewrite shlen_div in LT. Z.div_mod_to_equations. lia.
  - rewrite (proj2 (nth_error_None bs k)) by (rewrite LEN; exact GE).
    symmetry. apply nth_error_None. rewrite length_block_shadow_bytes by lia. exact GE.
Qed.

Theorem AHEAP_P_unmark : forall (ov : annOV) H L RNG st LB m p A n,
  @AHEAP_P rc ov H L RNG st LB m -> In (HB p A n) LB -> is_primary n = true -> ablock_shadow m A n ->
  @AHEAP_P rc (ov_unset ov p) H L RNG st LB m.
Proof.
  intros ov H L RNG st LB m p A n AH Hin PRIM CAN.
  destruct (AHEAP_P_live_cell ov H L RNG st LB m p A n AH Hin PRIM) as (CELL & LO1 & _).
  pose proof AH as (ALO & ARNG & [X [AR BL]] & HFK).
  assert (N1 : 0 < n).
  { destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & _ & Nb)|(mb & ms & Lp & EA & G)].
    - destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
      destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (M1 & _). rewrite Nb in M1. lia.
    - cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & G5 & _). lia. }
  pose proof (cb_canon_bytes m A n _ N1 ltac:(lia) CELL CAN) as EQB.
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL]. eapply (AREP_ov_agree ov (ov_unset ov p)); [| exact AR].
  intros b q Hb ES. unfold live_bytes at 1. unfold ov_unset. cbn [ann_ov].
  destruct (N.eqb_spec q p) as [->|NE]; [| reflexivity].

  destruct (proj1 BL p A n Hin) as [(b' & Hb' & Sb' & _ & Nb')|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & _ & NP & _). congruence. }
  destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNIQ).
  pose proof (UNIQ b b' Hb Hb' ltac:(rewrite ES, Sb'; reflexivity) ltac:(exists p; exact ES)) as EB. subst b'.
  rewrite Nb'. symmetry. exact EQB.
Qed.

Theorem AHEAP_P_unset_nonprim : forall (ov : annOV) H L RNG st LB m p,
  @AHEAP_P rc ov H L RNG st LB m -> (forall c n, (a_live st) !! p <> Some (CPrim c n)) ->
  @AHEAP_P rc (ov_unset ov p) H L RNG st LB m.
Proof.
  intros ov H L RNG st LB m p (ALO & ARNG & [X [AR BL]] & HFK) NP.
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL]. eapply (AREP_ov_agree ov (ov_unset ov p)); [| exact AR].
  intros b q Hb ES. unfold live_bytes at 1. unfold ov_unset. cbn [ann_ov].
  destruct (N.eqb_spec q p) as [->|NE]; [| reflexivity]. exfalso.
  destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY b Hb) as [_ M]. rewrite ES in M. destruct M as (_ & _ & _ & _ & _ & LV). exact (NP _ _ LV).
Qed.

End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import ABase.TwinB ABytes.TwinB AModelFacts.TwinB ASecFacts.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB ARepKit.TwinB ARepFrame.TwinB ARepExt.TwinB AFreeGeo.TwinB AFreeRep.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.TwinB.AFreeRead. Import RtCells.TwinB.
Import AC6U.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Definition ov_set (ov : annOV) (p : aptr) (bs : list byte) : annOV :=
  mkAnnOV (fun q => if N.eqb q p then Some bs else @ann_ov ov q) (@ann_ovs ov).

Definition ov_agree (ov ov' : annOV) (X : aconc) : Prop :=
  forall b p, In b (x_busy X) -> xb_st b = BLive p -> @live_bytes ov' p (xb_n b) = @live_bytes ov p (xb_n b).

Lemma slot_bytes_agree : forall ov ov' X S c k, ov_agree ov ov' X ->
  @slot_shadow_bytes ov' S (busy_of X c k) = @slot_shadow_bytes ov S (busy_of X c k).
Proof.
  intros ov ov' X S c k AG. destruct (busy_of X c k) as [b|] eqn:EB; [| reflexivity].
  pose proof EB as EB'. unfold busy_of in EB'. apply find_some in EB'. destruct EB' as [HIn _].
  unfold slot_shadow_bytes. destruct (xb_st b) as [p| |] eqn:ES; try reflexivity.
  rewrite (AG b p HIn ES). reflexivity.
Qed.

Lemma aslot_shadow_agree : forall ov ov' L st X m c, ov_agree ov ov' X ->
  @aslot_shadow ov L st X m c -> @aslot_shadow ov' L st X m c.
Proof.
  intros ov ov' L st X m c AG [SL UND]. split; [| exact UND].
  intros k Hk. rewrite (slot_bytes_agree ov ov' X _ c k AG). exact (SL k Hk).
Qed.

Theorem AREP_ov_agree : forall ov ov' H L st X m, ov_agree ov ov' X ->
  @AREP rc ov H L st X m -> @AREP rc ov' H L st X m.
Proof.
  intros ov ov' H L st X m AG AR.
  destruct AR as (WF & RT & INST & THR & CLS & REST).
  split; [exact WF|]. split; [exact RT|]. split; [exact INST|]. split; [exact THR|]. split; [| exact REST].
  intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
  split; [exact REG|]. split; [exact FARR|]. split; [exact SLOTS|]. exact (aslot_shadow_agree ov ov' L st X m c AG SHADOW).
Qed.

Theorem AHEAP_P_ov_agree : forall ov ov' H L RNG st LB m,
  (forall p ch, (a_live st) !! p = Some ch -> @ann_ov ov' p = @ann_ov ov p) ->
  @AHEAP_P rc ov H L RNG st LB m -> @AHEAP_P rc ov' H L RNG st LB m.
Proof.
  intros ov ov' H L RNG st LB m AG (ALO & ARNG & [X [AR BL]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL]. eapply (AREP_ov_agree ov ov'); [| exact AR].
  intros b p Hb ES. destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY b Hb) as [_ M]. rewrite ES in M. destruct M as (_ & _ & _ & _ & _ & LV). unfold live_bytes. rewrite (AG p _ LV). reflexivity.
Qed.

Definition ov_clear_from (ov : annOV) (p0 : aptr) : annOV :=
  mkAnnOV (fun q => if N.ltb q p0 then @ann_ov ov q else None) (@ann_ovs ov).
Lemma ov_clear_from_fresh : forall ov p0, @ann_ov (ov_clear_from ov p0) p0 = None.
Proof. intros ov p0. cbn. rewrite N.ltb_irrefl. reflexivity. Qed.
Theorem AHEAP_P_clear_fresh : forall ov H L RNG st LB m,
  @AHEAP_P rc ov H L RNG st LB m -> @AHEAP_P rc (ov_clear_from ov (a_next st)) H L RNG st LB m.
Proof.
  intros ov H L RNG st LB m AH. eapply AHEAP_P_ov_agree; [| exact AH].
  intros p ch LV. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  pose proof (FRESH p ch LV) as LT. cbn. apply N.ltb_lt in LT. rewrite LT. reflexivity.
Qed.

Lemma ov_read : forall (m : amem) A n, 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> m (wa (A + i)) <> None) -> exists bs, length bs = n /\ bytes_at bsegs m A bs.
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A A0 A1 PR.
  - exists []. split; [reflexivity|]. split; [exact A0|]. split; [cbn in *; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (IH (A + 1)) as (bs & LB & (B0 & B1 & BR)); [lia | lia | |].
    { intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply PR. lia. }
    pose proof (PR 0 ltac:(lia)) as P0. rewrite Z.add_0_r in P0.
    destruct (m (wa A)) as [b0|] eqn:E; [| congruence].
    exists (b0 :: bs). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; [cbn; rewrite Z.add_0_r; unfold mrd; rewrite E; reflexivity|].
    cbn [nth_error]. rewrite <- (BR i ltac:(cbn in Hi; lia)). f_equal. f_equal. lia.
Qed.

Section Remark.
Variable ov : annOV.
Variable H : aholes.
Hypothesis HL : ahole_laws H.
Variables (L : alayout) (st : astate) (X : aconc) (m m' : amem) (p : aptr) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Hypothesis ALO : alayout_ok L.
Hypothesis AR : @AREP rc ov H L st X m.
Hypothesis XB : x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let g := granules n.
Let W := [(shad UB, shad UB + g)].
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis RDM : forall i, 0 <= i < g -> m' (wa (shad UB + i)) <> None.

Lemma Ksh : forall A k', (A + k' <= shad UB \/ shad UB + g <= A) -> disjoint_from W A k'.
Proof. intros A k' D. unfold W. cbn [disjoint_from]. split; [exact D| exact I]. Qed.

Lemma slot_bytes_set_other : forall bs c' k', (c' <> c \/ k' <> k) ->
  @slot_shadow_bytes (ov_set ov p bs) (size_of_class c') (busy_of X c' k') = @slot_shadow_bytes ov (size_of_class c') (busy_of X c' k').
Proof.
  intros bs c' k' NE. destruct (busy_of X c' k') as [b|] eqn:EB; [| reflexivity].
  pose proof EB as EB'. unfold busy_of in EB'. apply find_some in EB'. destruct EB' as [HIn HP].
  apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
  unfold slot_shadow_bytes. destruct (xb_st b) as [q| |] eqn:ES; try reflexivity.
  unfold live_bytes, ov_set. cbn [ann_ov]. destruct (N.eqb_spec q p) as [->|NQ]; [| reflexivity].
  exfalso. destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNIQ).
  assert (HF : In (bfreed p c k n b1 ctx) (x_busy X)) by (rewrite XB; apply in_app_iff; right; left; reflexivity).
  pose proof (UNIQ b (bfreed p c k n b1 ctx) HIn HF ltac:(rewrite ES; reflexivity) ltac:(exists p; exact ES)) as EQ.
  subst b. cbn [xb_class xb_slot bfreed] in HP1, HP2. destruct NE as [NE|NE]; [apply NE; symmetry; exact HP1| apply NE; symmetry; exact HP2].
Qed.

Theorem AREP_remark1 :
  exists bs, length bs = Z.to_nat g /\ bytes_at bsegs m' (shad UB) bs /\ @AREP rc (ov_set ov p bs) H L st X m'.
Proof.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE0 & N0 & FIT0 & B10 & AT0 & CTX0).
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (CG1 & CG2 & CG3 & CG4 & CG5 & CG6 & CG7 & CG8 & CG9 & CG10 & CG11 & CG12 & CG13 & CG14).
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GF & GLO & GHI & GRL & GRH).
  pose proof (slot_geo L st X c k ALO WF HC KR) as (SG1 & SG2 & SGAL & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9 & SG10 & SG11 & SG12).
  fold S AB UB in CG1, CG2, CG3, CG4, CG5, CG6, CG7, CG8, CG11, CG14, SE, GF, GLO, GHI, GRL, GRH, SG1, SG2, SGAL, SG3, SG4, SG7, SG8, SG9, SG10.
  fold g in GE, GF.
  assert (G0' : 0 <= g) by (rewrite <- GE; exact G0).

  assert (WB : 0x2008fff7000 <= shad UB /\ shad UB + g <= 0x10007fff8000 /\ shad AB <= shad UB /\ shad UB + g <= shad AB + shlen S).
  { rewrite SE. lia. }
  destruct WB as (WB1 & WB2 & WB3 & WB4).

  destruct (CLS c HC) as (REGc & FARRc & SLOTSc & SHADOWc).
  destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj SLOTSc SHADOWc)) as (_ & _ & _ & _ & SHA & SHU & SHR).
  fold S AB UB in SHA, SHU, SHR. rewrite GE in SHU, SHR.

  assert (WRU : wr_at bsegs m' (shad UB) (Z.of_nat (Z.to_nat g))).
  { destruct SHU as [_ (W0 & W1 & WR)]. cbn [cells_size csize] in W1, WR. rewrite Nat.add_0_r in W1, WR.
    split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM. apply WR. exact Hi. }
  destruct (ov_read m' (shad UB) (Z.to_nat g) ltac:(clear -WB1; lia) ltac:(clear -WB2 G0'; lia)
              ltac:(intros i Hi; apply RDM; clear -Hi G0'; lia)) as (bs & LBS & BAT).
  exists bs. split; [exact LBS|]. split; [exact BAT|].
  assert (SHU' : rw_cells bsegs m' (shad UB) [CB (Z.to_nat g) bs]).
  { split; [split|].
    - cbn. split; [exact LBS| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BAT.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WRU. }
  assert (SHA' : rw_cells bsegs m' (shad AB) [CB (Z.to_nat (shlen (rz_size n))) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (rz_size n))))]).
  { eapply cells_frame; [exact SHA | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    apply Ksh. left. rewrite SE. lia. }
  assert (SHR' : rw_cells bsegs m' (shad UB + g) [CB (Z.to_nat (shlen S - shlen (rz_size n) - g))
                                                    (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen (rz_size n) - g)))]).
  { eapply cells_frame; [exact SHR | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    apply Ksh. right. lia. }
  assert (NEWCELL : rw_cells bsegs m' (shad AB) [CB (Z.to_nat (shlen S)) (@slot_shadow_bytes (ov_set ov p bs) S (busy_of X c k))]).
  { rewrite (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF).
    unfold slot_shadow_bytes. cbn [xb_n xb_st bfreed]. unfold live_bytes, ov_set. cbn [ann_ov]. rewrite N.eqb_refl.
    fold g. rewrite LBS, PeanoNat.Nat.eqb_refl.
    replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SHU', SHR' by (rewrite SE; lia).
    replace (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + g) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat g)) in SHR' by lia.
    pose proof (cb_app m' _ _ _ _ _ SHA' (cb_app m' _ _ _ _ _ SHU' SHR')) as FIN.
    replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat g + Z.to_nat (shlen S - shlen (rz_size n) - g)))%nat with (Z.to_nat (shlen S)) in FIN by lia.
    exact FIN. }

  pose proof atop_range as ATR.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_fake L ALO) as FK.
  unfold aobj, sclr, KLS in OT, OC, ORS, ON, OS, FK. pose proof (ao_space L ALO) as RSP.

  assert (Kout : forall A k', (A + k' <= 2147450880 \/ 17594333495296 <= A) -> disjoint_from W A k').
  { intros A k' HB. apply Ksh. clear -HB WB1 WB2. lia. }
  assert (Kimg : forall A k', 0 <= A -> 0 <= k' -> A + k' <= AIMG_HI -> disjoint_from W A k').
  { intros A k' H1 H2 H3. apply Kout. unfold AIMG_HI in H3. left. lia. }
  assert (Kres : forall A k', al_res L <= A -> 0 <= k' -> A + k' <= al_res L + 137439023104 -> disjoint_from W A k').
  { intros A k' H1 H2 H3. apply Kout. clear -H1 H2 H3 ORS ORH. lia. }
  assert (Kt : forall A k', al_t L <= A -> 0 <= k' -> A + k' <= al_t L + 4096 -> disjoint_from W A k').
  { intros A k' H1 H2 H3. apply Kout. clear -H1 H2 H3 OT. lia. }
  assert (Kctx : forall A k', al_ctx L <= A -> 0 <= k' -> A + k' <= al_ctx L + 65536 -> disjoint_from W A k').
  { intros A k' H1 H2 H3. apply Kout. clear -H1 H2 H3 OC. lia. }

  assert (RGC : forall c', 1 <= c' < K_NUM_CLASSES -> c' <> c ->
            forall A k', shad (aregion L c') <= A -> A + k' <= shad (aregion L c') + 536870912 -> disjoint_from W A k').
  { intros c' Hc' NE A k' H1 H2. apply Ksh.
    pose proof (aregion_mod L c' SAL) as RM'. pose proof (aregion_mod L c SAL) as RMc.
    assert (E29 : forall a, a mod 8 = 0 -> shad (a + K_REGION) = shad a + 536870912).
    { intros a Ha. rewrite shad_add_shlen by (clear -Ha; Z.div_mod_to_equations; lia). unfold K_REGION. rewrite shlen_div. reflexivity. }
    assert (INR : shad (aregion L c) <= shad UB /\ shad UB + g <= shad (aregion L c) + 536870912).
    { split; [lia|]. eapply Z.le_trans; [exact WB4|]. eapply Z.le_trans; [exact GRH|].
      rewrite <- (E29 (aregion L c)) by (clear -RMc; Z.div_mod_to_equations; lia).
      rewrite <- shad_add_shlen by (clear -RMc; Z.div_mod_to_equations; lia). apply shad_mono. unfold K_REGION, K_FREEARR_OFF in *. clear -SG6. lia. }
    destruct (Z.lt_ge_cases c' c) as [LT|GEc].
    - left. pose proof (regions_sep L c' c LT) as RS. apply shad_mono in RS. rewrite (E29 (aregion L c')) in RS by (clear -RM'; Z.div_mod_to_equations; lia).
      clear -H2 RS INR. lia.
    - right. pose proof (regions_sep L c c' ltac:(clear -GEc NE; lia)) as RS. apply shad_mono in RS. rewrite (E29 (aregion L c)) in RS by (clear -RMc; Z.div_mod_to_equations; lia).
      clear -H1 RS INR. lia. }

  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c0 Hc0. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c0 Hc0) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc0. apply Kt; clear -Hc0; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
  split.
  { intros c0 Hc0. destruct (CLS c0 Hc0) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c0 Hc0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c0 Hc0) as [QS QS16]. pose proof (aregion_mod L c0 SAL) as RM. pose proof Hc0 as Hc0'. unfold K_NUM_CLASSES in Hc0.
    assert (RI : al_res L <= aregion L c0 /\ aregion L c0 + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc0 RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.

    assert (KSH : forall o d, 0 <= o -> 0 <= d -> o mod 8 = 0 -> o + d <= K_REGION -> (c0 = c -> AB + S <= aregion L c + o) ->
                   disjoint_from W (shad (aregion L c0 + o)) (shlen d)).
    { intros o d Ho Hd Mo OD AFTER. destruct (Z.eq_dec c0 c) as [->|NEc].
      - apply Ksh. right. eapply Z.le_trans; [exact WB4|]. apply shad_sep; [exact (AFTER eq_refl)| clear -SGAL; Z.div_mod_to_equations; lia].
      - apply (RGC c0 Hc0' NEc).
        + apply shad_mono. clear -Ho. lia.
        + rewrite <- shad_add_shlen by (clear -RM Mo; Z.div_mod_to_equations; lia).
          replace 536870912 with (shlen K_REGION) by (unfold K_REGION; rewrite shlen_div; reflexivity).
          rewrite <- shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). apply shad_mono. clear -OD. lia. }
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc0 RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + unfold afreearr. apply KSH; [unfold K_FREEARR_OFF; clear; lia | clear -Q5 Q6; lia | unfold K_FREEARR_OFF; reflexivity
                                    | unfold K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; clear -Q6; lia |].
        intros ->. unfold K_FREEARR_OFF in *. clear -SG4 SG5 SG6. lia.
    - eapply (aslots_update L W m m' MU WM st st X X c0 (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k0 Hk0 _. pose proof (slot_in_region L st c0 k0 ltac:(clear -QS; lia) (proj1 Q1) Hk0) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    -
      destruct SHADOW as [SL UND]. split.
      + intros k0 Hk0. destruct (Z.eq_dec c0 c) as [EC|NEc]; [destruct (Z.eq_dec k0 k) as [EK|NEk]|].
        * subst c0 k0. exact NEWCELL.
        * subst c0. rewrite (slot_bytes_set_other bs c k0 (or_intror NEk)).
          eapply cells_frame; [exact (SL k0 Hk0) | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply shlen_nonneg; clear -QS; lia).
          apply Ksh. pose proof (slot_aligned L c k0 SAL Hc0') as AL0.
          destruct (slots_disjoint L c k0 k ltac:(clear -Hk0; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; fold S AB in D.
          -- left. eapply Z.le_trans; [| exact WB3]. apply shad_sep; [exact D| clear -AL0; Z.div_mod_to_equations; lia].
          -- right. eapply Z.le_trans; [exact WB4|]. apply shad_sep; [exact D| clear -SGAL; Z.div_mod_to_equations; lia].
        * rewrite (slot_bytes_set_other bs c0 k0 (or_introl NEc)).
          eapply cells_frame; [exact (SL k0 Hk0) | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply shlen_nonneg; clear -QS; lia).
          pose proof (slot_in_region L st c0 k0 ltac:(clear -QS; lia) (proj1 Q1) Hk0) as (P5 & P4 & P0).
          pose proof (slot_aligned L c0 k0 SAL Hc0') as AL0.
          apply (RGC c0 Hc0' NEc); [apply shad_mono; exact P5|].
          rewrite <- shad_add_shlen by (clear -AL0; Z.div_mod_to_equations; lia).
          replace 536870912 with (shlen K_REGION) by (unfold K_REGION; rewrite shlen_div; reflexivity).
          rewrite <- shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
          unfold K_REGION, K_FREEARR_OFF in *. clear -P4 Q1 Q2. lia.
      + eapply fill_frame; [exact UND | exact MU | exact WM |]. intros POS.
        pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM.
        apply KSH; [clear -Q1; lia | clear -Q1; lia | clear -AM; Z.div_mod_to_equations; lia | unfold K_REGION, K_FREEARR_OFF in *; clear -Q1 Q2; lia |].
        intros ->. clear -SG4. lia. }

  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  split.
  { eapply (hq_frame _ HL L st st X X m m' W); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched, W. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold AINSTANCE in *.
      split; [clear -WB1 WB2 OT; lia|].
      split; [clear -WB1; lia|].
      split; [clear -WB1; lia|].
      split; [clear -WB1; lia|].
      intros b Hb. destruct (BB b Hb) as [B1 B2]. destruct (xb_st b); [exact I| |]; clear -WB1 WB2 B1 B2 ORS ORH; lia.
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { assert (INS : shad (al_space_beg L) + 536870912 <= shad UB /\ shad UB + g <= shad (al_space_beg L) + 17179869696).
    { pose proof (aregion_mod L c SAL) as RMc.
      assert (SB8 : al_space_beg L mod 8 = 0) by (unfold K_ALIGN in SAL; clear -SAL; Z.div_mod_to_equations; lia).
      split.
      - eapply Z.le_trans; [| exact WB3]. eapply Z.le_trans; [| exact GRL].
        replace 536870912 with (shlen K_REGION) by (unfold K_REGION; rewrite shlen_div; reflexivity).
        rewrite <- shad_add_shlen by exact SB8. apply shad_mono. unfold aregion, K_REGION, K_NUM_CLASSES in *. clear -HC. lia.
      - eapply Z.le_trans; [exact WB4|]. eapply Z.le_trans; [exact GRH|].
        rewrite <- shad_add_shlen by (clear -RMc; Z.div_mod_to_equations; lia).
        replace 17179869696 with (shlen (K_SPACE_SIZE + 4096)) by (unfold K_SPACE_SIZE; rewrite shlen_div; reflexivity).
        rewrite <- shad_add_shlen by exact SB8. apply shad_mono. unfold aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_NUM_CLASSES in *.
        change (2^37) with 137438953472. clear -HC SG6. lia. }
    eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | | | apply sec_same_refl].
    - unfold sec_untouched, aknown, W. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. right. left. clear -INS Ha. lia.
    -
      unfold W. apply AC6U.TwinB.c6u_cons; [| apply AC6U.TwinB.c6u_nil]. cbn [fst snd]. apply (AC6U.TwinB.c6p_std L _ _ ALO). intros _. do 4 right. left.
      assert (SHBx : 0x7fff7000 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869696 <= 0x10007fff8000).
      { rewrite !shad_div. unfold ASHOFF. pose proof atop_range as ATRx. pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_res_hi L ALO) as ORHx.
        pose proof (ao_space L ALO) as RSPx. clear -RSPx ORSx ORHx ATRx. Z.div_mod_to_equations. lia. }
      clear -INS SHBx. lia. }
  split.
  { eapply (hd_frame _ HL L m m' W); [exact HD | exact MU | exact WM |].
    unfold W. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha.
    clear -Ha WB1 WB2 ON OS. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
  intros c0 Hc0. destruct (PERC c0 Hc0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof Hc0 as Hc0'. unfold K_NUM_CLASSES in Hc0.
  pose proof (aregion_mod L c0 SAL) as RM.
  assert (KSH : forall o d, 0 <= o -> 0 <= d -> o mod 8 = 0 -> o + d <= K_REGION -> (c0 = c -> AB + S <= aregion L c + o) ->
                 disjoint_from W (shad (aregion L c0 + o)) (shlen d)).
  { intros o d Ho Hd Mo OD AFTER. destruct (Z.eq_dec c0 c) as [->|NEc].
    - apply Ksh. right. eapply Z.le_trans; [exact WB4|]. apply shad_sep; [exact (AFTER eq_refl)| clear -SGAL; Z.div_mod_to_equations; lia].
    - apply (RGC c0 Hc0' NEc).
      + apply shad_mono. clear -Ho. lia.
      + rewrite <- shad_add_shlen by (clear -RM Mo; Z.div_mod_to_equations; lia).
        replace 536870912 with (shlen K_REGION) by (unfold K_REGION; rewrite shlen_div; reflexivity).
        rewrite <- shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). apply shad_mono. clear -OD. lia. }
  eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c0 Hc0') | reflexivity | reflexivity | |].
  - intros POS. apply KSH; [clear -Q1; lia | unfold K_FREEARR_OFF in *; clear -Q2; lia | unfold K_USER_MAP in Q4; clear -Q4; Z.div_mod_to_equations; lia
                           | unfold K_FREEARR_OFF, K_REGION; clear -Q1 Q2; lia |].
    intros ->. clear -SG4 SG5. lia.
  - intros POS. unfold afreearr. rewrite <- Z.add_assoc.
    apply KSH; [unfold K_FREEARR_OFF; clear -Q5 Q6; lia | unfold K_FREEARR_MAX in *; clear -Q6; lia
               | unfold K_FREEARR_OFF, K_FREEARR_MAP in *; clear -Q7; Z.div_mod_to_equations; lia
               | unfold K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; clear -Q5 Q6; lia |].
    intros ->. unfold K_FREEARR_OFF in *. clear -SG4 SG5 SG6 Q5 Q6. lia.
Qed.

Lemma remark_geo : 0x2008fff7000 <= shad UB /\ shad UB + g <= 0x10007fff8000
  /\ shad (al_res L) <= shad UB /\ shad UB + g <= shad (al_res L + 137439023104).
Proof.
  pose proof AR as AR0. destruct AR0 as (WF & _).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE0 & N0 & FIT0 & B10 & AT0 & CTX0).
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GF & GLO & GHI & GRL & GRH).
  pose proof (slot_geo L st X c k ALO WF HC KR) as (SG1 & SG2 & SGAL & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9 & SG10 & SG11 & SG12).
  fold S AB UB in SE, GF, GLO, GHI, GRL, GRH, SG1, SG2, SGAL, SG3, SG4, SG7, SG8, SG9, SG10. fold g in GE, GF.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  split; [rewrite SE; lia|]. split; [rewrite SE; lia|].
  split. { eapply Z.le_trans; [| rewrite SE; instantiate (1 := shad AB); lia]. apply shad_mono. clear -SG7 RSP. lia. }
  eapply Z.le_trans; [instantiate (1 := shad AB + shlen S); rewrite SE; lia|].
  apply shad_sep; [| clear -SGAL; Z.div_mod_to_equations; lia]. unfold K_SPACE_SIZE in SG8. change (2^37) with 137438953472 in SG8. clear -SG8 RSP. lia.
Qed.

Lemma remark_fake : disjoint_from W (al_t L + 72) 8 /\ fake_untouched L W.
Proof.
  destruct remark_geo as (WB1 & WB2 & WR1 & WR2).
  pose proof (ao_t L ALO) as OT. pose proof (ao_fake L ALO) as FK. pose proof (ao_dtls L ALO) as OD. pose proof (ao_res L ALO) as ORS.
  pose proof (ad_fake_res L ALO) as DFR. unfold adisj in DFR.
  unfold aobj, sclr, KLS in OT, FK, OD, ORS.
  split. { apply Ksh. clear -WB1 WB2 OT. lia. }
  unfold fake_untouched, W. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
  assert (SHR : shad (al_res L + 137439023104) <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad (al_res L)).
  { destruct DFR as [D|D]; [right | left].
    - apply shad_sep; [exact D | clear -FK; Z.div_mod_to_equations; lia].
    - apply shad_mono. exact D. }
  split; [clear -WB1 WB2 FK; lia|].
  split; [clear -WR1 WR2 SHR; lia|].
  split; [clear -WB1 WB2 OD; lia|].
  repeat split; clear -WB1; lia.
Qed.
End Remark.

Theorem AHEAP_P_remark1 : forall (ov : annOV) H (HL : ahole_laws H) L RNG st LB m m' p A n,
  @AHEAP_P rc ov H L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  munch [(shad A, shad A + granules n)] m m' -> wmono bsegs m m' ->
  (forall i, 0 <= i < granules n -> m' (wa (shad A + i)) <> None) ->
  exists bs, length bs = Z.to_nat (granules n) /\ bytes_at bsegs m' (shad A) bs /\ @AHEAP_P rc (ov_set ov p bs) H L RNG st LB m'.
Proof.
  intros ov H HL L RNG st LB m m' p A n (ALO & ARNG & [X [AR BL]] & HFK) Hin PRIM MU WM RDM.
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & _ & NP & _). congruence. }
  destruct b as [c k n' s0 b1 ctx]. cbn [xb_st xb_n] in Sb, Nb. subst s0 n'.
  unfold xb_user, xb_alloc in Ub. cbn [xb_class xb_slot xb_n] in Ub.
  destruct (in_split _ _ Hb) as (l1 & l2 & XB). change (mkXBusy c k n (BLive p) b1 ctx) with (bfreed p c k n b1 ctx) in XB.
  rewrite <- Ub in MU, RDM |- *.
  destruct (AREP_remark1 ov H HL L st X m m' p c k n b1 ctx l1 l2 ALO AR XB MU WM RDM) as (bs & LBS & BAT & AR').
  destruct (remark_fake ov H L st X m p c k n b1 ctx l1 l2 ALO AR XB) as [DT FU].
  exists bs. split; [exact LBS|]. split; [exact BAT|].
  split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
  eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM | exact DT | exact FU].
Qed.

Lemma AHEAP_P_live_cell : forall (ov : annOV) H L RNG st LB m p A n,
  @AHEAP_P rc ov H L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (granules n)) (@live_bytes ov p n)]
  /\ 0x2008fff7000 <= shad A /\ shad A + granules n <= 0x10007fff8000.
Proof.
  intros ov H L RNG st LB m p A n (ALO & ARNG & [X [AR BL]] & HFK) Hin PRIM.
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & _ & NP & _). congruence. }
  destruct b as [c k n' s0 b1 ctx]. cbn [xb_st xb_n] in Sb, Nb. subst s0 n'.
  unfold xb_user, xb_alloc in Ub. cbn [xb_class xb_slot xb_n] in Ub.
  destruct (in_split _ _ Hb) as (l1 & l2 & XB). change (mkXBusy c k n (BLive p) b1 ctx) with (bfreed p c k n b1 ctx) in XB.
  rewrite <- Ub.
  destruct (remark_geo ov H L st X m p c k n b1 ctx l1 l2 ALO AR XB) as (WB1 & WB2 & _ & _).
  split; [| split; [exact WB1| exact WB2]].
  pose proof AR as (WF & _ & _ & _ & CLS & _).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE0 & N0 & FIT0 & _).
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & GE & _).
  destruct (CLS c HC) as (_ & _ & SLOTSc & SHADOWc).
  destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj SLOTSc SHADOWc)) as (_ & _ & _ & _ & _ & SHU & _).
  rewrite GE in SHU. exact SHU.
Qed.

Lemma hb_ids_inj : forall (LB : list ablock) p A n A' n', List.NoDup (hb_ids LB) -> In (HB p A n) LB -> In (HB p A' n') LB -> HB p A n = HB p A' n'.
Proof.
  intros LB p A n A' n' ND. induction LB as [|x l IH]; intros Hb Hb'; [destruct Hb|]. cbn [hb_ids flat_map] in ND.
  assert (INID : forall A0 n0, In (HB p A0 n0) l -> In p (hb_ids l)).
  { intros A0 n0 Hy. unfold hb_ids. apply in_flat_map. exists (HB p A0 n0). split; [exact Hy| left; reflexivity]. }
  destruct Hb as [E0|Hb]; destruct Hb' as [E|Hb'].
  - rewrite <- E0. exact E.
  - exfalso. subst x. cbn [ab_kind app] in ND. apply NoDup_cons_iff in ND as [NI _]. exact (NI (INID _ _ Hb')).
  - exfalso. subst x. cbn [ab_kind app] in ND. apply NoDup_cons_iff in ND as [NI _]. exact (NI (INID _ _ Hb)).
  - apply IH; [| exact Hb| exact Hb']. destruct (ab_kind x); cbn [app] in ND; [apply NoDup_cons_iff in ND as [_ ND]; exact ND| exact ND].
Qed.

Lemma cb_overlay : forall (m : amem) A g bs i, rw_cells bsegs m A [CB g bs] -> 0x631000 <= A -> 0 <= i < Z.of_nat (length bs) ->
  m (wa (A + i)) = nth_error bs (Z.to_nat i).
Proof.
  intros m A g bs i [[_ (B0 & B1 & BR)] _] LO Hi. cbn [cells_bytes cbytes] in B1, BR. rewrite app_nil_r in B1, BR.
  specialize (BR (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in BR by lia.
  rewrite <- BR. symmetry. apply (mrd_no_image bsegs m 0x631000 (2^64)); [apply no_image_asan; lia| lia| lia| lia].
Qed.

Theorem AHEAP_P_mark_all : forall H (HL : ahole_laws H) L RNG st LB m (l : list ablock) (ov : annOV),
  @AHEAP_P rc ov H L RNG st LB m -> (forall b, In b l -> In b LB) ->
  exists ov' : annOV, @AHEAP_P rc ov' H L RNG st LB m
    /\ (forall p A n, In (HB p A n) l -> is_primary n = true -> exists bs, @ann_ov ov' p = Some bs /\ length bs = Z.to_nat (granules n))
    /\ (forall q, @ann_ov ov' q <> None -> @ann_ov ov q <> None \/ exists A n, In (HB q A n) l).
Proof.
  intros H HL L RNG st LB m l. induction l as [|b l IH]; intros ov AH SUB.
  - exists ov. split; [exact AH|]. split; [intros p A n []| intros q Hq; left; exact Hq].
  - destruct (IH ov AH ltac:(intros x Hx; apply SUB; right; exact Hx)) as (ov1 & AH1 & MK1 & SP1).
    destruct b as [[p|cls] A n].
    2: { exists ov1. split; [exact AH1|]. split.
         - intros p' A' n' [E|Hin] PR; [discriminate E| exact (MK1 p' A' n' Hin PR)].
         - intros q Hq. destruct (SP1 q Hq) as [S|(A' & n' & Hin)]; [left; exact S| right; exists A', n'; right; exact Hin]. }
    destruct (is_primary n) eqn:PRIM.
    2: { exists ov1. split; [exact AH1|]. split.
         - intros p' A' n' [E|Hin] PR; [injection E as <- <- <-; congruence| exact (MK1 p' A' n' Hin PR)].
         - intros q Hq. destruct (SP1 q Hq) as [S|(A' & n' & Hin)]; [left; exact S| right; exists A', n'; right; exact Hin]. }
    assert (HinLB : In (HB p A n) LB) by (apply SUB; left; reflexivity).
    destruct (AHEAP_P_live_cell ov1 H L RNG st LB m p A n AH1 HinLB PRIM) as (CELL & LO1 & HI1).
    pose proof CELL as [[[LEN _] _] _]. cbn in LEN.
    destruct (AHEAP_P_remark1 ov1 H HL L RNG st LB m m p A n AH1 HinLB PRIM (munch_refl _ _) (wmono_refl _ _)) as (bs & LBS & BAT & AH2).
    { intros i Hi. rewrite (cb_overlay m (shad A) _ _ i CELL ltac:(lia) ltac:(rewrite LEN; unfold granules in *; lia)).
      intros E. apply nth_error_None in E. rewrite LEN in E. unfold granules in *. lia. }
    exists (ov_set ov1 p bs). split; [exact AH2|]. split.
    + intros p' A' n' [E|Hin] PR.
      * injection E as <- <- <-. exists bs. split; [| exact LBS]. unfold ov_set. cbn [ann_ov]. rewrite N.eqb_refl. reflexivity.
      * destruct (MK1 p' A' n' Hin PR) as (bs' & E1 & L1). unfold ov_set. cbn [ann_ov].
        destruct (N.eqb_spec p' p) as [->|NE]; [| exists bs'; split; assumption].

        exists bs. split; [reflexivity|].
        destruct AH1 as (_ & _ & [X1 [_ BL1]] & _). destruct BL1 as (_ & _ & NDI & _).
        assert (EQ : HB p A' n' = HB p A n).
        { apply (hb_ids_inj LB); [exact NDI| apply SUB; right; exact Hin| exact HinLB]. }
        injection EQ as _ <-. exact LBS.
    + intros q Hq. destruct (N.eq_dec q p) as [EQ|NE].
      * right. exists A, n. left. rewrite EQ. reflexivity.
      * unfold ov_set in Hq. cbn [ann_ov] in Hq. apply N.eqb_neq in NE. rewrite NE in Hq.
        destruct (SP1 q Hq) as [S|(A' & n' & Hin)]; [left; exact S| right; exists A', n'; right; exact Hin].
Qed.

Theorem twin_bytes_eq : forall (ov : annOV) H H' L RNG RNG' st st' LB LB' m m' p A n bs,
  @AHEAP_P rc ov H L RNG st LB m -> @AHEAP_P rc ov H' L RNG' st' LB' m' -> In (HB p A n) LB -> In (HB p A n) LB' -> is_primary n = true ->
  @ann_ov ov p = Some bs -> length bs = Z.to_nat (granules n) ->
  forall i, 0 <= i < granules n -> m' (wa (shad A + i)) = m (wa (shad A + i)).
Proof.
  intros ov H H' L RNG RNG' st st' LB LB' m m' p A n bs AH AH' Hin Hin' PRIM E LBS i Hi.
  destruct (AHEAP_P_live_cell ov H L RNG st LB m p A n AH Hin PRIM) as (C1 & LO1 & _).
  destruct (AHEAP_P_live_cell ov H' L RNG' st' LB' m' p A n AH' Hin' PRIM) as (C2 & _ & _).
  assert (LV : @live_bytes ov p n = bs) by (unfold live_bytes; rewrite E, LBS, PeanoNat.Nat.eqb_refl; reflexivity).
  rewrite LV in C1, C2.
  rewrite (cb_overlay m (shad A) _ _ i C1 ltac:(lia) ltac:(rewrite LBS; lia)).
  rewrite (cb_overlay m' (shad A) _ _ i C2 ltac:(lia) ltac:(rewrite LBS; lia)). reflexivity.
Qed.

Lemma AHEAP_P_hb_lt : forall (ov : annOV) H L RNG st LB m p A n,
  @AHEAP_P rc ov H L RNG st LB m -> In (HB p A n) LB -> (p < a_next st)%N.
Proof.
  intros ov H L RNG st LB m p A n (_ & _ & [X [AR BL]] & _) Hin.
  destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & _)|(mb & ms & Lp & _)].
  - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & LV). exact (FRESH p _ LV).
  - exact (FRESH p _ Lp).
Qed.

Definition ov_unset (ov : annOV) (p : aptr) : annOV :=
  mkAnnOV (fun q => if N.eqb q p then None else @ann_ov ov q) (@ann_ovs ov).

Lemma nth_block_shadow_bytes : forall n i, 0 < n -> 0 <= i < granules n ->
  nth_error (block_shadow_bytes n) (Z.to_nat i) = Some (Z_to_bv 8 (if 8 * i + 8 <=? n then 0 else n - 8 * i)).
Proof.
  intros n i Hn Hi. unfold block_shadow_bytes. unfold granules in Hi. rewrite !shlen_div in *.
  destruct (Z.leb_spec (8 * i + 8) n) as [LE|GT].
  - rewrite nth_error_app1 by (rewrite repeat_length; Z.div_mod_to_equations; lia).
    apply nth_error_repeat. Z.div_mod_to_equations; lia.
  - assert (EI : i = n / 8) by (Z.div_mod_to_equations; lia).
    rewrite nth_error_app2 by (rewrite repeat_length; Z.div_mod_to_equations; lia).
    rewrite repeat_length. replace (Z.to_nat i - Z.to_nat (n / 8))%nat with 0%nat by lia.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; [exfalso; Z.div_mod_to_equations; lia|].
    cbn [nth_error]. f_equal. f_equal. Z.div_mod_to_equations; lia.
Qed.

Lemma cb_canon_bytes : forall (m : amem) A n bs, 0 < n -> 0x631000 <= shad A ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (granules n)) bs] -> ablock_shadow m A n -> bs = block_shadow_bytes n.
Proof.
  intros m A n bs Hn LO CELL CAN.
  pose proof CELL as [[[LEN _] _] _]. cbn in LEN.
  assert (G0 : 0 <= granules n) by (unfold granules; apply shlen_nonneg; lia).
  apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (Z.to_nat (granules n))) as [LT|GE].
  - rewrite <- (Nat2Z.id k). rewrite (nth_block_shadow_bytes n (Z.of_nat k) Hn ltac:(lia)).
    rewrite <- (cb_overlay m (shad A) _ _ (Z.of_nat k) CELL LO ltac:(rewrite LEN; lia)).
    apply CAN; [lia|]. unfold granules in LT. rewrite shlen_div in LT. Z.div_mod_to_equations. lia.
  - rewrite (proj2 (nth_error_None bs k)) by (rewrite LEN; exact GE).
    symmetry. apply nth_error_None. rewrite length_block_shadow_bytes by lia. exact GE.
Qed.

Theorem AHEAP_P_unmark : forall (ov : annOV) H L RNG st LB m p A n,
  @AHEAP_P rc ov H L RNG st LB m -> In (HB p A n) LB -> is_primary n = true -> ablock_shadow m A n ->
  @AHEAP_P rc (ov_unset ov p) H L RNG st LB m.
Proof.
  intros ov H L RNG st LB m p A n AH Hin PRIM CAN.
  destruct (AHEAP_P_live_cell ov H L RNG st LB m p A n AH Hin PRIM) as (CELL & LO1 & _).
  pose proof AH as (ALO & ARNG & [X [AR BL]] & HFK).
  assert (N1 : 0 < n).
  { destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & _ & Nb)|(mb & ms & Lp & EA & G)].
    - destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
      destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (M1 & _). rewrite Nb in M1. lia.
    - cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & G5 & _). lia. }
  pose proof (cb_canon_bytes m A n _ N1 ltac:(lia) CELL CAN) as EQB.
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL]. eapply (AREP_ov_agree ov (ov_unset ov p)); [| exact AR].
  intros b q Hb ES. unfold live_bytes at 1. unfold ov_unset. cbn [ann_ov].
  destruct (N.eqb_spec q p) as [->|NE]; [| reflexivity].

  destruct (proj1 BL p A n Hin) as [(b' & Hb' & Sb' & _ & Nb')|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & _ & NP & _). congruence. }
  destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNIQ).
  pose proof (UNIQ b b' Hb Hb' ltac:(rewrite ES, Sb'; reflexivity) ltac:(exists p; exact ES)) as EB. subst b'.
  rewrite Nb'. symmetry. exact EQB.
Qed.

Theorem AHEAP_P_unset_nonprim : forall (ov : annOV) H L RNG st LB m p,
  @AHEAP_P rc ov H L RNG st LB m -> (forall c n, (a_live st) !! p <> Some (CPrim c n)) ->
  @AHEAP_P rc (ov_unset ov p) H L RNG st LB m.
Proof.
  intros ov H L RNG st LB m p (ALO & ARNG & [X [AR BL]] & HFK) NP.
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL]. eapply (AREP_ov_agree ov (ov_unset ov p)); [| exact AR].
  intros b q Hb ES. unfold live_bytes at 1. unfold ov_unset. cbn [ann_ov].
  destruct (N.eqb_spec q p) as [->|NE]; [| reflexivity]. exfalso.
  destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY b Hb) as [_ M]. rewrite ES in M. destruct M as (_ & _ & _ & _ & _ & LV). exact (NP _ _ LV).
Qed.

End CANSEC1.
End TwinB.
