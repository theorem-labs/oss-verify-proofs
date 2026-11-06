(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* rp_uci_int_cgW: the proof of lib/A/Prog/rp_uci_int_cg.v's frozen uci_rp_uci_int_holds_stmt, for every float
   state, run ceiling and record B. The walk is the cgif-form walk of libreac/fuzz_decode's released
   lib/A/Prog/crtA_walk.v (origin/ossv/recipes 88154566652a): the function's own code runs as footprint runs
   (lib/A/Prog/rp_uci_int_cgW_runs.v), each carried into SRr by the leaf kit's bridge (lib/A/Prog/LeafCgFacts.v
   bridge_evtF_stmt_YA0n) after the state transport of lib/A/Prog/LeafCgGlue.v; the one call, memchr (0x7ff30), is
   cut by the statement's memchr premise (lib/A/Rt/MemchrDef.v amemchr_realizesM at c = '\n').
   - n = 0: rui_seg_zero runs to the return.
   - n > 0: rui_seg_call runs to the memchr trampoline; its frame write keeps AR (rui_mem_post: the frame is in the
     stack, so no owned byte, and present, so no hidden byte); memchr's premises are the statement's, read through the
     frame write (the reply, its shadow and musl memchr's constant window all lie outside the frame); memchr's post
     keeps every byte outside its ESTACK window, so the frame, the reply and its shadow keep their bytes; rui_seg_ret
     runs from the return address 0x7ff34 to the return.
   The footprint of every run is LeafCgKit.v RNG_W W (the visible bytes); each byte a run reads is visible: the frame
   by the stack premise, the runtime cells and the reply by their views, the shadow bytes by range_addressable. The
   four __asan_report_load1 branches are refuted inside the runs by the reply's shadow bytes (range_addressable). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import MState Mem Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Regs6ss ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00 YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI5b YI5c YK1b YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciPSyms UciPAddr UciCg rp_uci_int_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require LeafCgKit LeafCgFacts LeafCgGlue.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require rp_uci_int_cgW_runs.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_uci_int_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module LK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgFacts.
Module LG := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgGlue.
Module RR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_uci_int_cgW_runs.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_uci_int_c.
Module UC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.AsanCells.
Module I0 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Img0.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- facts of the walk that name no state of this function ---- *)

(* The reply's shadow bytes lie below kHighMemBeg (0x10007fff8000), so below every stack address (layout_ok
   lo_top). *)
Lemma rui_shadow_low : forall r n x, amem_range r n -> 0 <= r -> r <= x < r + n ->
  0 <= shadow_of_addr SHADOW_OFF x < 0x10007fff8000.
Proof.
  intros r n x HA H0 Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA.
  unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

Lemma rui_hull_low : forall r n s, amem_range r n -> 0 <= r -> 0 < n ->
  shadow_addr r / 8 * 8 <= s < shadow_addr (r + n - 1) / 8 * 8 + 8 -> 0 <= s < 0x10007fff8000.
Proof.
  intros r n s HA H0 Hn Hs. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HA.
  unfold shadow_addr, SHADOW_OFF in Hs. Z.div_mod_to_equations. lia.
Qed.

Lemma rui_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128. Z.div_mod_to_equations. lia.
Qed.

(* the first LF of the reply, as find_byte reads it *)
Lemma rui_find_lf : forall (bs : list byte) n k,
  Z.of_nat (length bs) = n -> 0 <= k <= n ->
  (forall i, 0 <= i < k -> bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)) <> 10) ->
  (k < n -> bv_unsigned (nth (Z.to_nat k) bs (Z_to_bv 8 0)) = 10) ->
  find_byte 10 bs = (if k <? n then Some (Z.to_nat k) else None).
Proof.
  intros bs n k HL Hk Hlt Hat.
  destruct (Z.ltb_spec k n) as [Hkn|Hkn].
  - apply (find_byte_charact 10 bs (Z.to_nat k) (nth (Z.to_nat k) bs (Z_to_bv 8 0))).
    + apply nth_error_nth'. lia.
    + exact (Hat Hkn).
    + intros j b' Hj Hn.
      assert (E : nth j bs (Z_to_bv 8 0) = b') by (apply nth_error_nth; exact Hn).
      rewrite <- E. replace j with (Z.to_nat (Z.of_nat j)) by lia. apply Hlt. lia.
  - destruct (find_byte 10 bs) as [i|] eqn:F; [|reflexivity]. exfalso.
    destruct (find_byte_Some _ _ _ F) as (Hi & (b & Hn & Hb) & _).
    apply (Hlt (Z.of_nat i)); [lia|]. rewrite Nat2Z.id.
    assert (E : nth i bs (Z_to_bv 8 0) = b) by (apply nth_error_nth; exact Hn).
    rewrite E. exact Hb.
Qed.

(* rw_cells is a property of the bytes of its range only (crtA_w_head.v crtA_rw_cells_eq) *)
Lemma rui_rw_cells_eq : forall (m m' : word -> option byte) A cs,
  rw_cells I0.rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (A + i)) = m (wa (A + i))) ->
  rw_cells I0.rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf [H0 [H1 Hb]]] [W0 [W1 Hw]]] E.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite <- (Hb i Hi). unfold mrd. rewrite (E (Z.of_nat i)); [reflexivity|]. rewrite L in Hi. lia.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    unfold wview. rewrite (E i Hi). exact (Hw i Hi).
Qed.

Section Glue.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.

(* Hidden bytes are off the image (YA0n.v w_Hoff), so a byte with a view is not hidden. *)
Lemma rui_vis : forall (W : world segs) mem x, aview segs (w_H W) mem x <> None -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W mem x H. destruct (w_H W (Z_to_bv 64 x)) eqn:E; [|reflexivity]. exfalso. apply H.
  assert (R : YK11.seg_rom segs (Z_to_bv 64 x) = None).
  { pose proof (w_Hoff W _ E) as Hf. unfold YK11.seg_rom, memory_read.
    rewrite (Hf : find_segment segs (bv_unsigned (Z_to_bv 64 x)) (Z.of_N 1) = None). reflexivity. }
  unfold aview, YP09.mbyte, mrestrict. rewrite E. cbv beta iota. rewrite R. reflexivity.
Qed.

(* A byte with a view is read by the machine at its value. *)
Lemma rui_mrd : forall (W : world segs) mem x v, aview segs (w_H W) mem x = Some v ->
  exists b, mrd I0.rsegs mem (wa x) = Some b /\ bv_unsigned b = v.
Proof.
  intros W mem x v H.
  assert (E : w_H W (Z_to_bv 64 x) = false) by (apply (rui_vis W mem x); rewrite H; discriminate).
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H. cbv beta iota in H.
  unfold mrd, wa. revert H.
  destruct (mem (Z_to_bv 64 x)) as [b|] eqn:Hm; intros H.
  - cbn in H. injection H as <-. exists b. split; reflexivity.
  - revert H. destruct (YK11.seg_rom segs (Z_to_bv 64 x)) as [b|] eqn:Hs; intros H; cbn in H; [|discriminate].
    injection H as <-. exists b. split; [exact Hs | reflexivity].
Qed.

(* Two present bytes with the same view are the same byte (crtA_w_head.v crtA_byte_eq). *)
Lemma rui_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  apresent H m a -> apresent H' m' a -> aview segs H' m' a = aview segs H m a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, YP09.mbyte, mrestrict in E. rewrite Hh, Hh', Hb, Hb' in E. cbn in E. injection E as E.
  rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

(* A range of visible bytes is in the walk's footprint (crtA_w_head.v crtA_rng_vis). *)
Lemma rui_rng_vis : forall (W : world segs) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  ExecF.rng (LK.RNG_W (world segs) (@w_H segs) W) a n.
Proof.
  intros W a n H0 H1 Hv. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hj. unfold LK.RNG_W, LK.range_avoids. intros kk Hk. unfold LK.woff.
  assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  rewrite Ub. replace (b + Z.of_nat kk) with (a + (b + Z.of_nat kk - a)) by lia. apply Hv. lia.
Qed.

(* An 8-byte constant cell of the record, read through its view, is the machine's le8 bytes. *)
Lemma rui_cell8 : forall (W : world segs) mem a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall k, (k < 8)%nat -> aview segs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v 8 k)) ->
  (forall k, (k < 8)%nat -> exists b, nth_error (le8 (wa v)) k = Some b /\ bv_unsigned b = le_byte v 8 k) ->
  bytes_at I0.rsegs mem a (le8 (wa v)).
Proof.
  intros W mem a v H0 H8 HV HN. split; [lia|]. split; [rewrite length_le8; cbn; lia|].
  intros i Hi. rewrite length_le8 in Hi. destruct (HN i Hi) as (b0 & Hb0 & Hu0). rewrite Hb0.
  destruct (rui_mrd W mem (a + Z.of_nat i) _ (HV i Hi)) as (b & Hb & Hu).
  rewrite Hb. f_equal. apply bv_eq. rewrite Hu, Hu0. reflexivity.
Qed.

(* The reply byte j, from garr8, read through its view. *)
Lemma rui_reply_view : forall (W : world segs) mem r (bs : list byte) j,
  garr8 segs (mrestrict (w_H W) mem) r (map (fun b : byte => bv_unsigned b) bs) -> (j < length bs)%nat ->
  aview segs (w_H W) mem (r + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
  intros W mem r bs j HG Hj.
  assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hj).
  assert (Em : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0))).
  { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hj'.
    exact (map_nth (fun b : byte => bv_unsigned b) bs (Z_to_bv 8 0) j). }
  destruct (HG j Hj') as (HV & HR). specialize (HV 0%nat ltac:(lia)).
  change (Z.of_nat 0) with 0 in HV. rewrite Z.add_0_r in HV.
  unfold aview. rewrite HV. cbn [option_map]. f_equal. rewrite <- Em.
  assert (S0 : forall z, Z.shiftr z (8 * Z.of_nat 0) = z) by (intros z; reflexivity).
  rewrite le_byte_small by (cbn; lia). rewrite S0.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

(* The frame write of a run keeps AR: the frame [lo, hi) is in the stack (no owned byte, AR_stack_law) and present
   (no hidden byte); every byte outside it keeps its view. (LeafCgGlue.v dleaf_mem_post, at a window of the caller's
   stack.) *)
Lemma rui_mem_post : forall B ly S (W : world segs) mem md mem' md' lo hi,
  @AR rc segs B ly S W mem md -> ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
  YK1b.mem_grows mem mem' -> munch [(lo, hi)] mem mem' -> same_but_materialized md md' ->
  @AR rc segs B ly S W mem' md' /\
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview segs (w_H W) mem' x = aview segs (w_H W) mem x) /\
  (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x).
Proof.
  intros B ly S W mem md mem' md' lo hi HAR Hlo Hhi HP HG HM HS.
  assert (HVIS : forall x, lo <= x < hi -> w_H W (Z_to_bv 64 x) = false) by (intros x Hx; exact (proj1 (HP x Hx))).
  assert (HPR : forall x, lo <= x < hi -> mem' (Z_to_bv 64 x) <> None).
  { intros x Hx. destruct (HP x Hx) as (_ & b & Hb). apply HG. rewrite Hb. discriminate. }
  assert (OUT : forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x).
  { intros x Hx. apply HM. cbn [outside]. split; [exact Hx | exact I]. }
  split; [|split].
  - apply (LF.AR_sbm_stmt_YG0q segs B ly S W mem' md md'); [|exact HS].
    apply (LF.AR_frame_stmt_YG0q segs B ly S W mem md mem' HAR).
    + intros a Ha Hown. apply (LF.aview_ext_stmt_YG0n segs). apply OUT. rewrite unsigned_lit by lia.
      intros Hin. exact (LF.AR_stack_stmt_YG0s segs B ly S W mem md a HAR ltac:(lia) Hown).
    + intros a Hv.
      destruct (Z_le_gt_dec lo (bv_unsigned (Z_to_bv 64 a))) as [H1|H1];
        [destruct (Z_lt_ge_dec (bv_unsigned (Z_to_bv 64 a)) hi) as [H2|H2]|].
      * apply (LF.aview_some_stmt_YG0n segs).
        -- rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 a)). apply HVIS. lia.
        -- rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 a)). apply HPR. lia.
      * rewrite (LF.aview_ext_stmt_YG0n segs (w_H W) mem mem' a); [exact Hv|]. apply OUT. lia.
      * rewrite (LF.aview_ext_stmt_YG0n segs (w_H W) mem mem' a); [exact Hv|]. apply OUT. lia.
    + intros a Ha. apply OUT. intros Hin.
      pose proof (HVIS _ Hin) as Hf. rewrite Z_to_bv_bv_unsigned in Hf. congruence.
  - intros x Hx Hn. apply (LF.aview_ext_stmt_YG0n segs). apply OUT. rewrite unsigned_lit by exact Hx. exact Hn.
  - intros x (HxH & b & Hb). split; [exact HxH|].
    destruct (mem' (Z_to_bv 64 x)) as [b'|] eqn:Hb'; [exists b'; reflexivity|].
    exfalso. refine (HG (Z_to_bv 64 x) _ Hb'). rewrite Hb. discriminate.
Qed.

(* A footprint run from cgif's configuration at pc, carried into SRr (crtA_walk.v crtA_run). *)
Lemma rui_run : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (pc : Z)
    (P : machine_state -> Prop) (Q : world segs -> config -> Prop),
  ExecF.evtF I0.rsegs (LK.RNG_W (world segs) (@w_H segs) W) P (@LK.ms_of_regs fx pc regs mem) ->
  (forall ms' md', (exists ms1, P ms1 /\ Regs6ss.ms_eqv ms1 ms' /\ YK1b.mem_grows mem (ms_mem ms1)) ->
     same_but_materialized md md' -> SRr segs W (mkCfg ms' md') Q) ->
  SRr segs W (@cfg_at fx segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc P Q HR K.
  pose proof (LG.evtF_eqv I0.rsegs _ P _ _ HR (LG.ms_of_regs_eqv pc regs mem)) as HR'.
  assert (FPA : LK.fp_avoids (w_H W) (LK.RNG_W (world segs) (@w_H segs) W)).
  { intros a n Ha. unfold LK.RNG_W in Ha. rewrite Z_to_bv_bv_unsigned in Ha. exact Ha. }
  exact (LF.bridge_evtF_stmt_YA0n W _ md _ _ Q HR' FPA K).
Qed.

End Glue.

(* ---- the walk ---- *)

Section Main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

Lemma uci_rp_uci_int_holds_at : @uci_rp_uci_int_holds_stmt fx rc B.
Proof.
  intros HCELLS LAWS HNOE HMC.
  unfold uci_rp_uci_int_cg.
  intros ly S W regs mem md r n cur bs HPRE HSTK HPRES Hr Hn Hcur Hnr Hlen Hcr Hr0 Hrn HG HVIS HAMR HRAD HSHV HCV.
  pose proof HPRE as (HAR & HRET & HAL & HLO & HHI & HSTKE & HGP & HTP).
  assert (HRET' : YK0s.ret_ok (YK11.getr regs (Z_to_bv 5 1))) by exact HRET.
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (LT1 & LT2 & LT3 & LT4 & LT5 & LT6 & LT7).
  unfold RUI_STK, RUI_FRAME, REPLY_MAX, ESTACK in *.
  unfold kHighMemBeg, kHighMemEnd in LT4, LT7.
  set (RNG := LK.RNG_W (world segs) (@w_H segs) W).
  (* the caller's stack below sp, the frame and its footprint *)
  assert (STK : stk I0.rsegs mem (spZ regs - (48 + 4096)) (spZ regs)).
  { split; [lia|]. split; [lia|].
    intros a Ha. destruct (HPRES a Ha) as [_ [b Hb]]. unfold wa. split.
    - unfold wview. rewrite Hb. discriminate.
    - exists b. unfold mrd. rewrite Hb. reflexivity. }
  assert (RFR : ExecF.rng RNG (spZ regs + -48) 48).
  { apply rui_rng_vis; [lia | lia |]. intros i Hi. exact (proj1 (HPRES (spZ regs + -48 + i) ltac:(lia))). }
  (* the runtime cells: the shadow base and its GOT word *)
  destruct (HCELLS ly) as (C1 & C2 & _).
  pose proof (am_const _ _ _ _ (proj1 HAR)) as HCo. rewrite Forall_forall in HCo.
  pose proof (HCo _ C1) as K1. pose proof (HCo _ C2) as K2.
  unfold z8, c8, cell_holds in K1, K2. cbn [c_at c_val c_w aeval] in K1, K2.
  assert (BCK : bytes_at I0.rsegs mem UC.CELL_K (le8 (wa UC.ASAN_K))).
  { apply (rui_cell8 W mem); [unfold UC.CELL_K; lia | unfold UC.CELL_K; lia | exact K1 |].
    intros k Hk. do 8 (destruct k as [|k]; [eexists; split; [reflexivity | vm_compute; reflexivity]|]). lia. }
  assert (BGCK : bytes_at I0.rsegs mem UC.GOT_CELL_K (le8 (wa UC.CELL_K))).
  { apply (rui_cell8 W mem); [unfold UC.GOT_CELL_K; lia | unfold UC.GOT_CELL_K; lia | exact K2 |].
    intros k Hk. do 8 (destruct k as [|k]; [eexists; split; [reflexivity | vm_compute; reflexivity]|]). lia. }
  assert (RCK : ExecF.rng RNG UC.CELL_K 8).
  { apply rui_rng_vis; [unfold UC.CELL_K; lia | unfold UC.CELL_K; lia |]. intros i Hi.
    apply (rui_vis W mem). replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite K1 by lia. discriminate. }
  assert (RGCK : ExecF.rng RNG UC.GOT_CELL_K 8).
  { apply rui_rng_vis; [unfold UC.GOT_CELL_K; lia | unfold UC.GOT_CELL_K; lia |]. intros i Hi.
    apply (rui_vis W mem). replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite K2 by lia. discriminate. }
  (* the reply and its shadow bytes are in the footprint *)
  assert (RD : forall x, r <= x < r + n -> ExecF.rng RNG x 1).
  { intros x Hx. apply rui_rng_vis; [lia | lia |]. intros i Hi. replace (x + i) with x by lia.
    apply (rui_vis W mem). exact (proj1 (HVIS x Hx)). }
  assert (RS : forall x, r <= x < r + n -> ExecF.rng RNG (x / 8 + UC.ASAN_K) 1).
  { intros x Hx. destruct (HRAD x Hx) as (s & Hs & _).
    pose proof (rui_shadow_low r n x HAMR ltac:(lia) Hx) as Lx. unfold shadow_of_addr, SHADOW_OFF in Lx, Hs.
    apply rui_rng_vis; [unfold UC.ASAN_K; lia | unfold UC.ASAN_K; lia |]. intros i Hi.
    replace (x / 8 + UC.ASAN_K + i) with (2147450880 + x / 8) by (unfold UC.ASAN_K; lia).
    apply (rui_vis W mem). rewrite Hs. discriminate. }
  destruct (Z.eq_dec n 0) as [Hn0|Hn0].
  - (* n = 0: rui_seg_zero to the return *)
    assert (Hb0 : bs = []) by (destruct bs; [reflexivity | cbn in Hlen; lia]). subst bs. subst n.
    assert (G12 : YK11.getr regs (Z_to_bv 5 12) = Z_to_bv 64 cur) by exact Hcur.
    assert (A1 : bv_unsigned (YK11.getr regs (Z_to_bv 5 11)) = 0)
      by (rewrite (Hn : YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 0); reflexivity).
    eapply rui_run.
    { unfold LK.ms_of_regs. rewrite G12. change (LK.w64 (uci_sigma US_rp_uci_int)) with (Z_to_bv 64 0x7fef0).
      eapply (RR.rui_seg_zero RNG).
      - exact STK.
      - change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs). lia.
      - exact RFR.
      - exact A1.
      - exact Hcr. }
    intros ms' md' (ms1 & (m1 & -> & MU) & HE & HGR) HS.
    destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE) as (R2 & -> & HX).
    cbn [ms_mem] in HGR.
    destruct (rui_mem_post B ly S W mem md m1 md' (spZ regs + -48) (spZ regs) HAR ltac:(lia) ltac:(lia)
                ltac:(intros a Ha; apply HPRES; lia) HGR MU HS) as (HAR1 & HV1 & HP1).
    apply SRr_ret. split; [reflexivity|]. exists R2, m1, md'.
    split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned, (LF.ret_ok_stmt_YK0s _ HRET'); reflexivity|].
    split; [exact HAR1|].
    split.
    { intros q Hq. rewrite (LG.getr_xeqv _ _ HX). unfold acallee_saved in Hq.
      assert (Hq' : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/
                    q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
      repeat (destruct Hq' as [->|Hq']; [reflexivity|]). subst q. reflexivity. }
    split; [exact HS|].
    split; [rewrite (LG.getr_xeqv _ _ HX); reflexivity|].
    split; [intros x Hx Hnx; apply HV1; [exact Hx | lia] | exact HP1].
  - (* n > 0: rui_seg_call to memchr, memchr, rui_seg_ret to the return *)
    assert (A1 : bv_unsigned (YK11.getr regs (Z_to_bv 5 11)) <> 0)
      by (rewrite (Hn : YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 n); rewrite unsigned_lit by lia; lia).
    eapply rui_run.
    { unfold LK.ms_of_regs. change (LK.w64 (uci_sigma US_rp_uci_int)) with (Z_to_bv 64 0x7fef0).
      eapply (RR.rui_seg_call RNG).
      - exact STK.
      - change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs). lia.
      - exact BGCK.
      - exact BCK.
      - change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs). unfold UC.CELL_K. lia.
      - exact RFR.
      - exact RGCK.
      - exact RCK.
      - exact A1. }
    intros ms' md1 (ms1 & (m1 & junk & -> & MU & FR1) & HE & HGR) HS1.
    destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE) as (R1 & -> & HX1).
    cbn [ms_mem] in HGR.
    destruct (rui_mem_post B ly S W mem md m1 md1 (spZ regs + -48) (spZ regs) HAR ltac:(lia) ltac:(lia)
                ltac:(intros a Ha; apply HPRES; lia) HGR MU HS1) as (HAR1 & HV1 & HP1).
    (* the registers at the call *)
    assert (R1_1 : YK11.getr R1 (Z_to_bv 5 1) = Z_to_bv 64 0x7ff34) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_2 : YK11.getr R1 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -48))
      by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_3 : YK11.getr R1 (Z_to_bv 5 3) = YK11.getr regs (Z_to_bv 5 3))
      by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_4 : YK11.getr R1 (Z_to_bv 5 4) = YK11.getr regs (Z_to_bv 5 4))
      by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_8 : YK11.getr R1 (Z_to_bv 5 8) = Z_to_bv 64 cur) by (rewrite (LG.getr_xeqv _ _ HX1); exact Hcur).
    assert (R1_9 : YK11.getr R1 (Z_to_bv 5 9) = Z_to_bv 64 r) by (rewrite (LG.getr_xeqv _ _ HX1); exact Hr).
    assert (R1_10 : YK11.getr R1 (Z_to_bv 5 10) = Z_to_bv 64 r) by (rewrite (LG.getr_xeqv _ _ HX1); exact Hr).
    assert (R1_11 : YK11.getr R1 (Z_to_bv 5 11) = Z_to_bv 64 10) by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (R1_12 : YK11.getr R1 (Z_to_bv 5 12) = Z_to_bv 64 n) by (rewrite (LG.getr_xeqv _ _ HX1); exact Hn).
    assert (R1_18 : YK11.getr R1 (Z_to_bv 5 18) = Z_to_bv 64 n) by (rewrite (LG.getr_xeqv _ _ HX1); exact Hn).
    assert (R1_19 : YK11.getr R1 (Z_to_bv 5 19) = Z_to_bv 64 UC.ASAN_K)
      by (rewrite (LG.getr_xeqv _ _ HX1); reflexivity).
    assert (SP1 : spZ R1 = spZ regs - 48).
    { change (spZ R1) with (bv_unsigned (YK11.getr R1 (Z_to_bv 5 2))). rewrite R1_2. apply unsigned_lit. lia. }
    assert (RA1 : raZ R1 = 0x7ff34).
    { change (raZ R1) with (bv_unsigned (YK11.getr R1 (Z_to_bv 5 1))). rewrite R1_1. reflexivity. }
    (* memchr (r, '\n', n) *)
    assert (PRE1 : ecall_pre segs B ly S W R1 m1 md1).
    { split; [exact HAR1|].
      split; [assert (Hra1 : YK0s.ret_ok (YK11.getr R1 (Z_to_bv 5 1)))
                by (rewrite R1_1; apply ret_ok_even; vm_compute; reflexivity); exact Hra1|].
      split; [rewrite SP1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z.mod_add by lia;
              exact HAL|].
      split; [rewrite SP1; unfold ESTACK; lia|]. split; [rewrite SP1; lia|].
      split; [intros a Ha; rewrite SP1 in Ha; unfold ESTACK in Ha; apply HP1; apply HPRES; lia|].
      split; [assert (Hg1 : YK11.getr R1 (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite R1_3; exact HGP); exact Hg1
             |assert (Ht1 : YK11.getr R1 (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite R1_4; exact HTP); exact Ht1]. }
    eapply SRr_bind.
    { exact (HMC fx ly S W R1 m1 md1 r 10 n PRE1 R1_10 R1_11 R1_12 ltac:(lia) ltac:(lia) Hr0 Hrn
        ltac:(intros a Ha; rewrite SP1; unfold ESTACK; destruct (HVIS a Ha) as [Hv Hw];
              split; [rewrite HV1; [exact Hv | lia | lia] | lia])
        HAMR
        ltac:(intros x Hx; destruct (HRAD x Hx) as (s & Hs & Hok); exists s; split; [|exact Hok];
              pose proof (rui_shadow_low r n x HAMR ltac:(lia) Hx); rewrite HV1; [exact Hs | lia | lia])
        ltac:(intros Hn' s Hs; pose proof (rui_hull_low r n s HAMR ltac:(lia) Hn' Hs);
              rewrite HV1; [exact (HSHV Hn' s Hs) | lia | lia])
        ltac:(intros a Ha; unfold UCI_MC_LO, UCI_MC_HI in Ha; rewrite HV1; [exact (HCV a Ha) | lia | lia])). }
    intros W' c' _ (-> & regs2 & m2 & md2 & -> & HAR2 & HAP2 & HS2 & (k & HFB & G10) & HV2 & HP2).
    rewrite RA1. unfold ESTACK in HV2.
    destruct HFB as (Hk & Hbef & Hat).
    (* what memchr keeps *)
    assert (TV : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - (48 + 4096) <= x < spZ regs) ->
                 aview segs (w_H W) m2 x = aview segs (w_H W) mem x).
    { intros x Hx Hnx. rewrite HV2; [| exact Hx | rewrite SP1; lia]. apply HV1; [exact Hx | lia]. }
    assert (G2 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) + -48))
      by (rewrite (HAP2 2 ltac:(unfold acallee_saved; lia)); exact R1_2).
    assert (G8 : YK11.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 cur)
      by (rewrite (HAP2 8 ltac:(unfold acallee_saved; lia)); exact R1_8).
    assert (G9 : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 r)
      by (rewrite (HAP2 9 ltac:(unfold acallee_saved; lia)); exact R1_9).
    assert (G18 : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 n)
      by (rewrite (HAP2 18 ltac:(unfold acallee_saved; lia)); exact R1_18).
    assert (G19 : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 UC.ASAN_K)
      by (rewrite (HAP2 19 ltac:(unfold acallee_saved; lia)); exact R1_19).
    assert (A0 : bv_unsigned (YK11.getr regs2 (Z_to_bv 5 10)) = (if k <? n then r + k else 0)).
    { rewrite (G10 : YK11.getr regs2 (Z_to_bv 5 10) = _). destruct (k <? n); apply unsigned_lit; lia. }
    (* the reply at memchr's call, its first LF, and the reply and its shadow after memchr *)
    assert (V1 : forall i, 0 <= i < n ->
                 aview segs (w_H W) m1 (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))).
    { intros i Hi. pose proof (proj2 (HVIS (r + i) ltac:(lia))) as Hw.
      rewrite HV1; [| lia | lia].
      replace (r + i) with (r + Z.of_nat (Z.to_nat i)) by lia. apply rui_reply_view; [exact HG | lia]. }
    assert (FB : find_byte 10 bs = (if k <? n then Some (Z.to_nat k) else None)).
    { apply rui_find_lf; [exact Hlen | exact Hk | |].
      - intros i Hi. destruct (Hbef i Hi) as (b & Hb & Hne). rewrite V1 in Hb by lia. injection Hb as <-. exact Hne.
      - intros Hkn. pose proof (Hat Hkn) as Ha. rewrite V1 in Ha by lia. injection Ha as Ha. exact Ha. }
    assert (BR : bytes_at I0.rsegs m2 r bs).
    { split; [lia|]. split; [lia|]. intros i Hi.
      assert (Hv : aview segs (w_H W) m2 (r + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))).
      { rewrite TV; [exact (rui_reply_view W mem r bs i HG Hi) | lia | exact (proj2 (HVIS (r + Z.of_nat i) ltac:(lia)))]. }
      destruct (rui_mrd W m2 _ _ Hv) as (b & Hb & Hu). rewrite Hb.
      rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. exact Hu. }
    assert (SH : forall x, r <= x < r + n ->
                 exists kb : byte, mrd I0.rsegs m2 (wa (x / 8 + UC.ASAN_K)) = Some kb /\
                                   (bv_signed kb = 0 \/ x mod 8 < bv_signed kb)).
    { intros x Hx. destruct (HRAD x Hx) as (s & Hs & Hok).
      pose proof (rui_shadow_low r n x HAMR ltac:(lia) Hx) as Lx.
      assert (Hs2 : aview segs (w_H W) m2 (shadow_of_addr SHADOW_OFF x) = Some s) by (rewrite TV; [exact Hs | lia | lia]).
      destruct (rui_mrd W m2 _ _ Hs2) as (kb & Hkb & Hu).
      exists kb. replace (x / 8 + UC.ASAN_K) with (shadow_of_addr SHADOW_OFF x)
        by (unfold shadow_of_addr, SHADOW_OFF, UC.ASAN_K; lia).
      split; [exact Hkb|]. unfold saddr_ok in Hok. rewrite rui_signed_small by lia. rewrite Hu. lia. }
    (* the frame keeps its bytes across memchr: it lies above memchr's window *)
    pose proof (rui_rw_cells_eq m1 m2 _ _ FR1
      ltac:(intros i Hi; cbn [cells_size csize Nat.add] in Hi;
            change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs); unfold wa;
            apply (rui_byte_eq (w_H W) (w_H W) m1 m2);
            [ apply HP1; apply HPRES; lia | apply HP2; apply HP1; apply HPRES; lia
            | rewrite HV2; [reflexivity | lia | rewrite SP1; lia] ])) as FR2.
    (* rui_seg_ret from 0x7ff34 *)
    eapply rui_run.
    { unfold LK.ms_of_regs. rewrite G2, G8, G9, G18, G19. change (LK.w64 0x7ff34) with (Z_to_bv 64 0x7ff34).
      eapply (RR.rui_seg_ret RNG) with (k := k) (r := r) (n := n) (bs := bs) (cur := cur).
      - exact FR2.
      - change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs). lia.
      - exact RFR.
      - exact BR.
      - exact Hlen.
      - lia.
      - exact Hr0.
      - exact Hrn.
      - exact SH.
      - exact RD.
      - exact RS.
      - exact Hk.
      - exact FB.
      - exact A0.
      - exact Hcr. }
    intros ms' md3 (ms3 & (y5 & y6 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & ->) & HE3 & _) HS3.
    destruct (LG.eqv_MS_mkst _ _ _ _ _ _ _ HE3) as (R3 & -> & HX3).
    apply SRr_ret. split; [reflexivity|]. exists R3, m2, md3.
    split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned, (LF.ret_ok_stmt_YK0s _ HRET'); reflexivity|].
    split; [exact (LF.AR_sbm_stmt_YG0q segs B ly S W m2 md2 md3 HAR2 HS3)|].
    split.
    { intros q Hq. rewrite (LG.getr_xeqv _ _ HX3). unfold acallee_saved in Hq.
      assert (Hq' : q = 2 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 3 \/ q = 4 \/ q = 20 \/ q = 21 \/ q = 22 \/
                    q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
      destruct Hq' as [->|[->|[->|[->|[->|Hq']]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|].
      assert (KQ : YK11.getr R1 (Z_to_bv 5 q) = YK11.getr regs (Z_to_bv 5 q)).
      { rewrite (LG.getr_xeqv _ _ HX1).
        repeat (destruct Hq' as [->|Hq']; [reflexivity|]). subst q. reflexivity. }
      rewrite <- KQ, <- (HAP2 q ltac:(unfold acallee_saved; lia)).
      repeat (destruct Hq' as [->|Hq']; [reflexivity|]). subst q. reflexivity. }
    split; [exact (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ HS1 HS2) HS3)|].
    split; [rewrite (LG.getr_xeqv _ _ HX3); reflexivity|].
    split; [intros x Hx Hnx; exact (TV x Hx Hnx) | intros x Hx; exact (HP2 x (HP1 x Hx))].
Qed.

End Main.

(* The frozen statement, at every float state, run ceiling and record. *)
Theorem uci_rp_uci_int_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (B : asyms),
  @uci_rp_uci_int_holds_stmt fx rc B.
Proof. intros fx rc B. exact (@uci_rp_uci_int_holds_at fx rc B). Qed.
