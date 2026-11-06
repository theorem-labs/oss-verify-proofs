(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names, addresses and numbers changed; 598 of its 699 lines of code are new or changed and 1401 lines of the source are left out. *)
(* The shared tail of the image-A segments R11 and R12 of fuzz_ctrl LLVMFuzzerTestOneInput (asan): the three
   argument loads and the call of reac_identity_ingest at 0x81714 .. 0x81730, and the continuation from there to the
   official cut Inv_A81734_at (R13's entry; aslot push 13 carries PRO, RXS and X81734 there).

   0x81714 ld a0,88(s1) ; 0x81718 lhu a1,0(a0) ; 0x8171c ld a0,80(s1) ; 0x81720 ld a2,0(a0) ;
   0x81724 ld a0,72(s1) ; 0x81728 ld a3,0(a0) ; 0x8172c mv a0,s5 ; 0x81730 jal reac_identity_ingest.
   The three spills [A + 88] / [A + 80] / [A + 72] are the frame pointers fr + 2448 / fr + 2464 / fr + 2496 that
   A4 stores at 0x814d8 / 0x814d4 / 0x814d0; the reply (R10, b = 3, 4) and the fragment close (R10, b = 6) left the
   address, the payload pointer and the payload length in those three cells. The identity record id = s5 = fr + 2176
   is the ingest's first argument and its only write outside its own 32 stack bytes.
   None of the eight instructions is instrumented (no shadow check in the listing), so the run is the plain Lib-level
   `step`s plus the callee contract.

   rn_ing_cont rebuilds the cut at 0x81734: FRA across the write set W = [sp - 32, sp) U [fr + 2176, fr + 2214) by
   B3FrCl.b3_fr_cl (AH by rn_ah: real arm a_laws_store, side arm a_laws_fs_store), ENT by Tac_slot.ent_store, the
   loop-body spills and the four record cells by position (all at [A + ...] with sp <= A, or inside the frame above
   fr + 2214), OUTA / HB / the two addressable ranges by Tac_slot.sl_addr_keep (W is app memory), PRO (push 13B) by
   RcPro.rc_pro_keep (the ingest window is at or above the slot window's base, the id record is frame body: both
   rc_away), and X81734 from the ingest post: a0 = fst (ING idb ad pb) = 1 (the caller's premise), s8 = phi
   (callee-saved) and the records of turn S b (the identity record is the one ingest wrote,
   snd (ING idb ad pb) = RID (S b)). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel RcFrag RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3FrCl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import RcPro.
Import ListNotations.
(* Qualified, as in R15.v: `Require ... BzBridge KindBGlue` loads the image-independent lib/Reusable/YK11, whose
   getr / mkst / FPState are NOT the ones the cuts are built over. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module ACi := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFi := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module YKi := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

(* ---- small helpers (ports of the ubsan Tac_u2m lemmas of the same shape) ---- *)

Lemma rn_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zx16. rewrite MState.unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma rn_ovr : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as E.
  rewrite Z.add_0_r, skipn_O, firstn_all in E. exact E.
Qed.

(* A byte at [A0, A0 + 312) with Z_to_bv 64 A0 = Z_to_bv 64 A lies outside any [lo, hi) with 0 <= lo and
   hi <= A (R17.v's r17_wrap_out, with the lower offset the spills [A + 0] / [A + 8] need). *)
Lemma rn_wrap_out : forall A A0 lo hi x, Z_to_bv 64 A = Z_to_bv 64 A0 -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  0 <= lo -> hi <= A -> A0 <= x < A0 + 312 -> ~ (lo <= x < hi).
Proof.
  intros A A0 lo hi x E H0 H1 Hlo Hhi Hx.
  assert (Ew : A mod 2 ^ 64 = A0 mod 2 ^ 64).
  { apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. exact E. }
  rewrite (Z.mod_small A (2 ^ 64)) in Ew by lia.
  pose proof (Z.div_mod A0 (2 ^ 64) ltac:(lia)) as Hdm. rewrite <- Ew in Hdm.
  remember (A0 / 2 ^ 64) as q eqn:Eq. clear Eq.
  change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.

Lemma rn_bv_mod : forall a a' d, Z_to_bv 64 a = Z_to_bv 64 a' -> Z_to_bv 64 (a + d) = Z_to_bv 64 (a' + d).
Proof.
  intros a a' d H. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap in *.
  rewrite (Zplus_mod a d), (Zplus_mod a' d), H. reflexivity.
Qed.

Lemma rn_bytes_cong : forall m a a' bs,
  Z_to_bv 64 a = Z_to_bv 64 a' -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m a' bs -> bytes_at rsegs m a bs.
Proof.
  intros m a a' bs Hcong Ha0 Hal (Ha'0 & Ha'l & Hr). split; [exact Ha0|]. split; [exact Hal|].
  intros i Hi.
  assert (Heq : wa (a + Z.of_nat i) = wa (a' + Z.of_nat i)).
  { unfold wa. apply rn_bv_mod. exact Hcong. }
  rewrite Heq. exact (Hr i Hi).
Qed.

(* A spill word read at the FRA base A (R17.v's r17_spill_ro, as an ov_read_bytes fact). *)
Lemma rn_spill_ov : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  ov_read_bytes rsegs m (wa (A + off)) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros regs m off v A (A1 & Hr9' & Hq) Hr9 HA0 HAb Hoff.
  unfold rg in Hr9'. assert (Hcong : Z_to_bv 64 A = Z_to_bv 64 A1) by (rewrite <- Hr9; exact Hr9').
  unfold q64 in Hq.
  assert (Hb : bytes_at rsegs m (A + off) (le8 (Z_to_bv 64 v))).
  { eapply rn_bytes_cong; [ apply rn_bv_mod; exact Hcong | lia | rewrite length_le8; lia | exact Hq ]. }
  pose proof (rn_ovr m (A + off) _ Hb) as E. rewrite length_le8 in E. exact E.
Qed.

(* A spill transported across a run whose write set W avoids its 8 bytes (R17.v's r17_spill_keep). *)
Lemma rn_spill_keep : forall (regs regs'' : bvmap 5 word) m m' off v A W,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> getr regs'' 9 = getr regs 9 ->
  0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  Frame.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> Frame.outside W x) ->
  spill regs'' m' off v.
Proof.
  intros regs regs'' m m' off v A W (A1 & Hr9' & Hq) Hr9 K9 HA0 HAb Hoff MU Hout.
  unfold rg in Hr9'. assert (Hcong : Z_to_bv 64 A = Z_to_bv 64 A1) by (rewrite <- Hr9; exact Hr9').
  assert (Hq2 : q64 m (A + off) v).
  { unfold q64 in *. eapply rn_bytes_cong; [ apply rn_bv_mod; exact Hcong | lia | rewrite length_le8; lia | exact Hq ]. }
  exists A. split; [unfold rg; transitivity (getr regs 9); [exact K9 | exact Hr9]|].
  unfold q64 in *. eapply fl_bytes; [exact Hq2 | exact MU |]. rewrite length_le8. exact Hout.
Qed.

(* One CB cell transported across a run whose write set W avoids its bytes (R17.v's r17_rwcb_keep). *)
Lemma rn_rwcb_keep : forall W (m m' : word -> option byte) a n bs,
  Frame.munch W m m' -> Frame.wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat n -> Frame.outside W x) ->
  rw_cells rsegs m a [CB n bs] -> rw_cells rsegs m' a [CB n bs].
Proof.
  intros W m m' a n bs MU WM HO ((Hwf & Hb) & Hw).
  assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
  split; [split; [exact Hwf|]|].
  - apply (a_keep W m m' a _ MU); [|exact Hb]. intros x Hx.
    cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hlen in Hx. exact (HO x Hx).
  - destruct Hw as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
    intros i Hi. exact (WM _ (Hw i Hi)).
Qed.

(* bytes_at + writability of the range as a CB cell. *)
Lemma rn_rwcb_of : forall (m : word -> option byte) a bs,
  bytes_at rsegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> writable_at rsegs m x) ->
  rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m a bs HB HW. pose proof HB as (Ha0 & Hal & _).
  split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - split; [exact Ha0|]. cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|].
    intros i Hi. exact (HW (a + i) ltac:(lia)).
Qed.

(* Lengths of the round-trip records (R15.v's r15_fg_st_len / r15_RS_len, a Theorem Labs lane). *)
Lemma rn_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, fg_class.
  change ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) with false. cbv iota.
  destruct (fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in Efr. rewrite !andb_true_iff in Efr. destruct Efr as [[[_ H1] H2] _].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  assert (Hb : forall bs i, 0 <= bat bs i).
  { intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. }
  assert (Hbody : length (fg_body g) = Z.to_nat (fg_n g)).
  { unfold fg_body, bsl. rewrite length_firstn, length_skipn, Hg. lia. }
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. unfold fg_first. rewrite !length_app, Hbody, length_skipn, Hs. cbn [length].
    unfold bsl. rewrite length_firstn, length_skipn, Hg. lia.
  - destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|cbn [fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hs; cbn [length]; lia].
    assert (HT : fg_T st g <= 64).
    { unfold fg_keep in Ek. rewrite !andb_true_iff in Ek. destruct Ek as [_ H]. apply Z.leb_le in H. exact H. }
    assert (Hj : length (fg_join st g) = 72%nat).
    { unfold fg_join. unfold fg_T, fg_lf in HT. pose proof (Hb st 7).
      rewrite !length_app, Hbody, length_firstn, length_skipn, Hs. unfold fg_T, fg_lf. lia. }
    destruct (fg_close st g); cbn [negb fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hj; cbn [length]; lia.
Qed.

Lemma rn_RS_len : forall inp b, length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RID, RFG. induction b as [|b [IH1 IH2]]; [split; reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact (conj IH1 IH2)|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - split; [|exact IH2]. unfold rp_id. destruct (RcReply.ir _ _); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact (conj IH1 IH2)].
    split.
    + unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
    + apply rn_fg_st_len; [exact IH2 | apply fr50_length].
Qed.

(* Slices of a byte range (the ubsan Tac_u2m u2_at_slice / u2_bsl_at / u2_bsl_len / u2_fr50_at). *)
Lemma rn_at_slice : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma rn_bsl_at : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> 0 <= n ->
  k + n <= Z.of_nat (length bs) -> bytes_at rsegs m (a + k) (RcFrag.bsl bs k n).
Proof.
  intros m a bs k n H Hk Hn L. unfold RcFrag.bsl.
  pose proof (rn_at_slice m a bs (Z.to_nat k) (Z.to_nat n) H ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma rn_bsl_len : forall bs k n, 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  length (RcFrag.bsl bs k n) = Z.to_nat n.
Proof. intros bs k n Hk Hn L. unfold RcFrag.bsl. rewrite length_firstn, length_skipn. lia. Qed.

Lemma rn_fr50_at : forall m a bs, bytes_at rsegs m a bs -> (50 <= length bs)%nat ->
  bytes_at rsegs m a (fr50 bs).
Proof.
  intros m a bs H L. unfold fr50.
  rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  pose proof (rn_at_slice m a bs 0%nat 50%nat H ltac:(lia)) as E.
  rewrite skipn_O in E. change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E. exact E.
Qed.

Lemma rn_hull : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 6283264.
Proof.
  assert (H : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  intros s Hin. apply Z.leb_le. rewrite forallb_forall in H. exact (H s Hin).
Qed.

Lemma rn_ro_lt : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 6283264.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  pose proof (YK1j.find_segment_in rsegs (bv_unsigned a) 1 s E) as Hin.
  pose proof (YK1j.find_segment_range rsegs (bv_unsigned a) 1 s E) as (_ & Hhi).
  pose proof (rn_hull s Hin) as Hb. lia.
Qed.

Lemma rn_ro_keep : forall (mem mem' : word -> option byte) (W : list Frame.ivl),
  ro_agree rsegs mem -> Frame.munch W mem mem' ->
  (forall a : word, ro_addr rsegs a = true -> Frame.outside W (bv_unsigned a)) ->
  ro_agree rsegs mem'.
Proof.
  intros mem mem' W HRO MU Hout a Hro. unfold mrd. rewrite (MU a (Hout a Hro)). exact (HRO a Hro).
Qed.

(* ---- The Lib-level run 0x81714 .. 0x81734 with the reac_identity_ingest contract ---- *)
Lemma rn_ing_evt : reac_identity_ingest_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A id pa pp pn ad p len lo : Z) (idb pb : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 id ->
    0 <= spv < 2 ^ 64 -> spv mod 16 = 0 ->
    0 < id < 2 ^ 64 -> id mod 2 = 0 -> 0 <= ad < 65536 -> 0 < p < 2 ^ 64 -> 0 < len < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 88)) 8 = Some (le8 (Z_to_bv 64 pa)) ->
    ov_read_bytes rsegs m (wa (A + 80)) 8 = Some (le8 (Z_to_bv 64 pp)) ->
    ov_read_bytes rsegs m (wa (A + 72)) 8 = Some (le8 (Z_to_bv 64 pn)) ->
    ov_read_bytes rsegs m (wa pa) 2 = Some (le2 (Z_to_bv 64 ad)) ->
    ov_read_bytes rsegs m (wa pp) 8 = Some (le8 (Z_to_bv 64 p)) ->
    ov_read_bytes rsegs m (wa pn) 8 = Some (le8 (Z_to_bv 64 len)) ->
    rw_cells rsegs m id [CB 38 idb] ->
    length pb = Z.to_nat len -> bytes_at rsegs m p pb ->
    p + len <= id \/ id + 38 <= p ->
    stk rsegs m lo spv -> lo + 32 <= spv ->
    (id + 38 <= spv - 32 \/ spv <= id) -> (p + len <= spv - 32 \/ spv <= p) ->
    asan_cells m -> shadow_rw m -> addressable m id 38 -> addressable m p len ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       Frame.outside [(spv - 32, spv); (id, id + 38)] x) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81734) sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (fst (RcIdentModel.ING idb ad pb)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x81734) fc None m' (seg_rom rsegs) /\
         Frame.munch [(spv - 32, spv); (id, id + 38)] m m' /\ Frame.wmono rsegs m m' /\
         stk rsegs m' lo spv /\
         rw_cells rsegs m' id [CB 38 (snd (RcIdentModel.ING idb ad pb))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81714) fc None m (seg_rom rsegs)).
Proof.
  intros INGC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A id pa pp pn ad p len lo idb pb -> -> -> Hspv H16 Hid Hidm Had Hp Hlen
    R88 R80 R72 RPA RPP RPN HI Hpblen HPB HD ST Hlo32 Hidsp Hpsp HAC HSW HAid HAp HOut.
  assert (NR : ingest_refused id p len = false).
  { unfold ingest_refused.
    replace (id =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite andb_false_r. reflexivity. }
  step. step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply INGC with (id := id) (ad := ad) (p := p) (len := len) (idb := idb) (pb := pb) (lo := lo).
    - reflexivity.
    - apply rn_zx16. lia.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros _. split; [exact Hidm | exact HI].
    - exact Hpblen.
    - intros _ _. exact HPB.
    - intros _ _ _. exact HD.
    - rewrite MState.unsigned_lit by lia. exact ST.
    - rewrite MState.unsigned_lit by lia. unfold REAC_IDENTITY_INGEST_FRAME. lia.
    - intros _. rewrite MState.unsigned_lit by lia. unfold REAC_IDENTITY_INGEST_FRAME. exact Hidsp.
    - intros _ _. rewrite MState.unsigned_lit by lia. unfold REAC_IDENTITY_INGEST_FRAME. exact Hpsp.
    - exact HAC.
    - exact HSW.
    - intros _. exact HAid.
    - intros _ _. exact HAp.
    - unfold reac_identity_ingest_W, REAC_IDENTITY_INGEST_FRAME.
      rewrite MState.unsigned_lit by lia. exact HOut. }
  intros ms' PO. unfold reac_identity_ingest_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI & STc & _ & HZ).
  subst ms'. specialize (HZ NR).
  unfold ingest_ret. rewrite NR.
  unfold reac_identity_ingest_W, REAC_IDENTITY_INGEST_FRAME in MU.
  rewrite MState.unsigned_lit in MU, STc by lia.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact STc | exact HZ].
Qed.

Section RNIngW.
Context {fx : YKi.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACi.AsanAllocAPI ACi.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis INGC : reac_identity_ingest_contract.

(* AH after the ingest store W = [sp - 32, sp) U [fr + 2176, fr + 2214): real arm by a_laws_store, side arm by
   a_laws_fs_store (the identity record lies inside the FakeStack frame, above its metadata). *)
Lemma rn_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch [(ACi.aspZ regs - 32, ACi.aspZ regs); (fr + 2176, fr + 2176 + 38)] mem mem' ->
  Frame.wmono rsegs mem mem' -> rd_mono mem mem' ->
  ACi.aa_AH ACi.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, ACi.a_in_img a ->
     ACi.aa_owned ACi.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     ACi.aa_owned ACi.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) /\
  ACi.aa_stklo ACi.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACi.aa_stklo ACi.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  ACi.aa_stkhi ACi.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACi.aa_stkhi ACi.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md HFRA MU WM HRDM.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlowin & Hstkwin).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in MU, Hlowin.
  assert (HSS : AFi.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : ACi.FS_SIZE = 11571200) by reflexivity.
  unfold FN_STACK in Hlowin.
  pose proof (ACi.a_laws_stack_high ACi.ASYMS _ _ _ _ (ACi.aa_laws ACi.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH) as Hhigh.
  unfold stk in Hwin. destruct Hwin as (Hwlo & Hwhi & _).
  assert (HWR : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
  { intros a _ Ha. exact (WM (Z_to_bv 64 a) Ha). }
  destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & HfsbS & Hfs & _)].
  - assert (Hunch : forall a, 0 <= a < 2 ^ 64 ->
      ~ ACi.a_store_ok (hb ++ g_H g) (ACi.aa_stklo ACi.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
      split; [|split; [|exact I]]; intro Hin.
      - apply Hns. unfold ACi.a_store_ok. right; left. split; lia.
      - apply Hns. unfold ACi.a_store_ok. right; left. exact (Hreal a ltac:(lia)). }
    destruct (ACi.a_laws_store ACi.ASYMS _ _ _ _ (ACi.aa_laws ACi.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem mem' md HAH Hunch HWR) as (HAH' & HOWN' & HSTK' & HSHI').
    split; [exact HAH'|]. split; [intros a _ Ha; exact (proj2 (HOWN' a) Ha)|].
    split; [exact HSTK' | exact HSHI'].
  - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSb0 & HwFSb & HFSbr).
    pose proof (HfsbS FSb HwFSb HFSb0) as HfrGE.
    pose proof (ACi.a_laws_fs_place ACi.ASYMS _ _ _ _ (ACi.aa_laws ACi.ASYMS AsanRTInv.RT (APIf rc))
                  (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0) as (HGTfs & HFSstk & _ & _).
    assert (HFSz : FSb + ACi.FS_SIZE <= 2 ^ 64) by lia.
    pose proof (proj1 (ACi.a_laws_fs_state ACi.ASYMS _ _ _ _ (ACi.aa_laws ACi.ASYMS AsanRTInv.RT (APIf rc))
                  (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0)) as Hfsok.
    assert (HPres : forall q0, 0 <= q0 < 2 ^ 64 -> (exists b, mbyte rsegs mem q0 = Some b) ->
                    (exists b, mbyte rsegs mem' q0 = Some b)).
    { intros q0 Hq0 Hpr. apply (HRDM (wa q0)). exact Hpr. }
    assert (Hfsok' : ACi.a_fs_ok mem' FSb).
    { apply (a_fs_ok_pres [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] mem mem' FSb Hfsok MU HWR HPres).
      - intros q0 Hmeta. pose proof (fs_meta_below FSb q0 Hmeta) as Hbelow.
        cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hin; lia.
      - lia.
      - exact HFSz. }
    assert (Hunch : forall a, 0 <= a < 2 ^ 64 ->
      ~ ACi.a_store_ok (hb ++ g_H g) (ACi.aa_stklo ACi.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FSb <= a < FSb + ACi.FS_SIZE) ->
      ~ (exists bb, FSb <= bb < FSb + ACi.FS_SIZE /\ a = shadow_addr bb) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns HnFS Hnsh. apply MU. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
      split; [|split; [|exact I]]; intro Hin.
      - apply Hns. unfold ACi.a_store_ok. right; left. split; lia.
      - apply HnFS. split; lia. }
    destruct (ACi.a_laws_fs_store ACi.ASYMS _ _ _ _ (ACi.aa_laws ACi.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem mem' md FSb HAH HwFSb HFSb0 Hunch HWR Hfsok')
      as (HAH' & HOWN' & HSTK' & HSHI').
    split; [exact HAH'|]. split; [intros a _ Ha; exact (proj2 (HOWN' a) Ha)|].
    split; [exact HSTK' | exact HSHI'].
Qed.

(* The continuation from 0x81714 to the official Inv_A81734_at (R13's entry). The caller (R11 / R12) supplies the
   turn-b facts the three argument cells hold and the two model facts of the ingest result. *)
Lemma rn_ing_cont : forall b : nat,
  Hat B APIf ra (Inv_A81734_at (fx := fx) B APIf ra) b ->
  forall g regs mem md fr phi ad p len (pb : list byte),
    FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md ->
    ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem md ->
    (* the official push-9 body at the entry *)
    g_n g < 2 ^ 26 -> (b <= 6)%nat -> HB mem phi (rnb g b) -> rg regs 23 (Z.of_nat b) ->
    OURb g fr mem -> OUTA fr mem -> CUR g 7 regs ->
    spill regs mem 112 (mrow (g_in g)) -> spill regs mem 128 (fr + 544) -> PRO g fr regs mem ->
    spill regs mem 104 0x21140 -> spill regs mem 96 0x1234 -> spill regs mem 64 0xe38f0000 ->
    spill regs mem 144 (fr + 2688) -> spill regs mem 192 (fr + 2768) ->
    (exists idb0, rw_cells rsegs mem (fr + 2688) [CB 38 idb0]) ->
    (exists junk, rw_cells rsegs mem (fr + 2768) [CB 72 junk]) ->
    spill regs mem 280 (fr + 3040) -> spill regs mem 240 (fr + 3056) ->
    (exists jy, rw_cells rsegs mem (fr + 3040) [CB 1 jy]) ->
    (exists junk, rw_cells rsegs mem (fr + 3056) [CB 32 junk]) ->
    spill regs mem 152 (Sfr fr + 68) -> rg regs 21 (fr + 2176) ->
    addressable mem (fr + 2176) 38 ->
    (* the ingest arguments *)
    rg regs 24 phi ->
    IDBr g fr (RID (g_in g) b) mem -> FGBr g fr (RFG (g_in g) (S b)) mem ->
    RXS g fr regs mem ->
    bytes_at rsegs mem (fr + 2448) (le2 (Z_to_bv 64 ad)) ->
    bytes_at rsegs mem (fr + 2464) (le8 (Z_to_bv 64 p)) ->
    bytes_at rsegs mem (fr + 2496) (le8 (Z_to_bv 64 len)) ->
    0 <= ad < 65536 -> 0 < len -> length pb = Z.to_nat len ->
    bytes_at rsegs mem p pb -> addressable mem p len ->
    ((phi <= p /\ p + len <= phi + rnb g b) \/ (fr + 2214 <= p /\ p + len <= fr + FRAME_BYTES)) ->
    (* the two model facts of the ingest result *)
    fst (RcIdentModel.ING (RID (g_in g) b) ad pb) = 1 ->
    snd (RcIdentModel.ING (RID (g_in g) b) ad pb) = RID (g_in g) (S b) ->
    rnb g b <> 0 ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x81714) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b Hexit g regs mem md fr phi ad p len pb HFRA HENT
    Hgn Hb6 HHB Hr23 HOUR HOUTA HCUR
    Hs112 Hs128 HPRO Hs104 Hs96 Hs64 Hs144 Hs208 HRWid HRWjk Hs280 Hs240 HRWjy HRWj32 Hs152 Hr21 HAD38
    Hr24 HIDB HFGB HRXS HBa HBp HBn Had Hlen0 Hpblen HPB HAp Hploc HING1 HINGs Hnz.
  destruct (a_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnbrng & _).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hnbrng.
  pose proof HRXS as (Hs48 & Hs56 & Hs88 & Hs80 & Hs72 & Hs16 & Hs8 & Hs192 & Hs216 & HAD72).
  pose proof (proj1 FF) as SEGS.
  (* names from FRA *)
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5v & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hlowin & Hstkwin).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hfrpl & Hfr9 & Hfspl & Hfrwr).
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGTfr & Hframeapp).
  pose proof (sl_frame_apart_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as Hapart.
  rewrite Haspz in Hlowin, Hstkwin, Hapart.
  assert (HSS : AFi.SLOT_STACK = 1048576) by reflexivity.
  unfold FN_STACK in Hlowin, Hstkwin.
  pose proof (ACi.a_laws_stack_high ACi.ASYMS _ _ _ _ (ACi.aa_laws ACi.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (rnb g b) ++ g_H g) mem md HAH) as Hhigh.
  assert (HSPstrong : 17594334539776 <= sp) by (unfold HIGHMEM_BEG, FN_STACK in *; lia).
  destruct HRT as (HAC & HSW & HasO & HCF & HasR & HREAL & HasRest).
  pose proof (a_hb B APIf ra g fr phi (rnb g b) regs mem md HFRA) as (Hphi0' & Hphi4096 & Hphistk & Hein & Hphibytes).
  assert (HA0 : 0 <= A) by (unfold stk in Hwin; lia).
  assert (HSle : g_S g <= 2 ^ 64) by (unfold stk in Hwin; lia).
  assert (HA312 : A + 312 <= 2 ^ 64) by lia.
  assert (Hspapp : forall x, sp - 32 <= x < sp -> app_mem x).
  { intros x Hx. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hframe8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  unfold ACi.GT in HGTfr.
  (* the identity record cell *)
  assert (HRWidr : rw_cells rsegs mem (fr + 2176) [CB 38 (RID (g_in g) b)]).
  { pose proof (rn_RS_len (g_in g) b) as (LID & _).
    pose proof (rn_rwcb_of mem (fr + 2176) (RID (g_in g) b) HIDB
                 ltac:(rewrite LID; intros x Hx; apply (Hfrwr x); lia)) as Hc.
    rewrite LID in Hc. exact Hc. }
  (* the three argument cells read as ov *)
  assert (R88 : ov_read_bytes rsegs mem (wa (A + 88)) 8 = Some (le8 (Z_to_bv 64 (fr + 2448))))
    by exact (rn_spill_ov regs mem 88 _ A Hs88 Hr9 HA0 ltac:(lia) ltac:(lia)).
  assert (R80 : ov_read_bytes rsegs mem (wa (A + 80)) 8 = Some (le8 (Z_to_bv 64 (fr + 2464))))
    by exact (rn_spill_ov regs mem 80 _ A Hs80 Hr9 HA0 ltac:(lia) ltac:(lia)).
  assert (R72 : ov_read_bytes rsegs mem (wa (A + 72)) 8 = Some (le8 (Z_to_bv 64 (fr + 2496))))
    by exact (rn_spill_ov regs mem 72 _ A Hs72 Hr9 HA0 ltac:(lia) ltac:(lia)).
  assert (RPA : ov_read_bytes rsegs mem (wa (fr + 2448)) 2 = Some (le2 (Z_to_bv 64 ad))).
  { pose proof (rn_ovr mem (fr + 2448) _ HBa) as E. rewrite length_le2 in E. exact E. }
  assert (RPP : ov_read_bytes rsegs mem (wa (fr + 2464)) 8 = Some (le8 (Z_to_bv 64 p))).
  { pose proof (rn_ovr mem (fr + 2464) _ HBp) as E. rewrite length_le8 in E. exact E. }
  assert (RPN : ov_read_bytes rsegs mem (wa (fr + 2496)) 8 = Some (le8 (Z_to_bv 64 len))).
  { pose proof (rn_ovr mem (fr + 2496) _ HBn) as E. rewrite length_le8 in E. exact E. }
  (* payload bounds and placement *)
  assert (Hlenb : len < 2 ^ 64) by (pose proof HAp as (_ & _ & Hple & _); unfold APPMEM_END in *; lia).
  assert (Hp0 : 0 < p).
  { destruct Hploc as [(H1 & H2)|(H1 & H2)]; lia. }
  assert (Hpb64 : p + len <= 2 ^ 64) by (pose proof HAp as (_ & _ & Hple & _); unfold APPMEM_END in *; lia).
  (* the heap block and the frame are disjoint (R17.v's Hblkfr) *)
  assert (Hblkfr : fr + FRAME_BYTES <= phi \/ phi + rnb g b <= fr).
  { destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
    - right. lia.
    - destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [Hle|Hgt]; [left; exact Hle|].
      destruct (Z_le_gt_dec (phi + rnb g b) fr) as [Hle2|Hgt2]; [right; exact Hle2|].
      exfalso.
      pose proof (ACi.a_laws_blocks ACi.ASYMS _ _ _ _ (ACi.aa_laws ACi.ASYMS AsanRTInv.RT (APIf rc))
                    (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH
                    ltac:(unfold hb1; apply in_or_app; left; apply in_eq)) as (_ & _ & _ & _ & Hbb).
      destruct (Hbb (Z.max phi fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
      exact (Hnfs (Hfs (Z.max phi fr) ltac:(lia))). }
  assert (HD : p + len <= fr + 2176 \/ fr + 2176 + 38 <= p).
  { destruct Hploc as [(H1 & H2)|(H1 & H2)]; [destruct Hblkfr as [Hc|Hc]; [right | left] | right]; lia. }
  assert (Hfrsp : fr + FRAME_BYTES <= sp - 32 \/ sp <= fr).
  { destruct (Hfrpl 32 ltac:(unfold FN_STACK; lia)) as [Hc|Hc]; rewrite Haspz in Hc; [left; lia | right; lia]. }
  assert (Hidsp : fr + 2176 + 38 <= sp - 32 \/ sp <= fr + 2176) by (destruct Hfrsp as [Hc|Hc]; [left | right]; lia).
  assert (Hpsp : p + len <= sp - 32 \/ sp <= p).
  { destruct Hploc as [(H1 & H2)|(H1 & H2)]; [left; lia | destruct Hfrsp as [Hc|Hc]; [left | right]; lia]. }
  assert (Happp : forall x, p <= x < p + len -> app_mem x) by exact (addressable_app mem p len HAp).
  (* the outside premise of the contract *)
  assert (HOut : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            Frame.outside [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hin.
    - destruct Hx as [HG|[HC|HSh]].
      + unfold GOT_CELL_K, HIGHMEM_BEG in *; lia.
      + unfold CELL_K, HIGHMEM_BEG in *; lia.
      + unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia.
    - destruct Hx as [HG|[HC|HSh]].
      + unfold GOT_CELL_K in *; lia.
      + unfold CELL_K in *; lia.
      + pose proof (Hframeapp x ltac:(lia)) as Happx.
        unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *; lia. }
  (* run *)
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81714) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81734 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 10 = Z_to_bv 64 1 /\
       Frame.munch [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)] mem mem' /\ Frame.wmono rsegs mem mem' /\
       stk rsegs mem' (sp - (AFi.SLOT_STACK - 4096)) sp /\
       rw_cells rsegs mem' (fr + 2176) [CB 38 (RID (g_in g) (S b))])
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg in Hr21, Hr9.
    eapply evt_mono.
    + apply (rn_ing_evt INGC) with (spv := sp) (A := A) (id := fr + 2176) (pa := fr + 2448) (pp := fr + 2464)
        (pn := fr + 2496) (ad := ad) (p := p) (len := len) (lo := sp - (AFi.SLOT_STACK - 4096))
        (idb := RID (g_in g) b) (pb := pb).
      all: try assumption.
      all: try (Z.div_mod_to_equations; lia).
    + intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Hms & MUq & WMq & STq & HIq).
      subst ms'. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|].
      do 12 (split; [reflexivity|]).
      split; [cbn; rewrite HING1; reflexivity|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|].
      rewrite HINGs in HIq. exact HIq.
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K10 &
       MU & WM & STk & HIc) Hreg Hmat.
    subst pc'.
    set (W := [(sp - 32, sp); (fr + 2176, fr + 2176 + 38)]).
    (* read-monotonicity across the write set *)
    assert (HRDM : rd_mono mem mem').
    { apply (rd_mono_list W mem mem' MU).
      constructor; [|constructor; [|constructor]].
      - cbn [fst snd]. intros y Hy. exact (rd_of_stk mem' (sp - (AFi.SLOT_STACK - 4096)) sp STk y ltac:(lia)).
      - cbn [fst snd]. intros y Hy.
        destruct HIc as ((_ & Hbb) & _). destruct Hbb as (_ & _ & Hbr).
        cbn [cells_bytes cbytes] in Hbr. rewrite app_nil_r in Hbr.
        pose proof (rn_RS_len (g_in g) (S b)) as (LID' & _).
        pose proof (Hbr (Z.to_nat (y - (fr + 2176))) ltac:(rewrite LID'; lia)) as Hb.
        replace (fr + 2176 + Z.of_nat (Z.to_nat (y - (fr + 2176)))) with y in Hb by lia.
        destruct (nth_error (RID (g_in g) (S b)) (Z.to_nat (y - (fr + 2176)))) as [bb|] eqn:E;
          [exists bb; rewrite Hb; first [exact E | reflexivity]|].
        apply nth_error_None in E. rewrite LID' in E. lia. }
    assert (MUa : Frame.munch [(ACi.aspZ regs - 32, ACi.aspZ regs); (fr + 2176, fr + 2176 + 38)] mem mem').
    { rewrite Haspz. exact MU. }
    pose proof (rn_ah g fr (hb1 phi (rnb g b)) regs mem mem' md HFRA MUa WM HRDM)
      as (HAH' & HOWN' & HSTK' & HSHI').
    assert (HAW : all_app W).
    { unfold W. cbn [all_app app_ivl]. split; [|split; [|exact I]].
      - intros a Ha. exact (Hspapp a Ha).
      - intros a Ha. exact (Hframeapp a ltac:(lia)). }
    assert (HDJ : rt_disjoint W).
    { unfold W, rt_disjoint; cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
        RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN in *.
      repeat split; left; lia. }
    assert (HWlo : forall x, 0 <= x < 6283264 -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (HWhdr : forall x, fr <= x < fr + 24 -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - intro Hc. apply (Hapart x ltac:(lia)); lia.
      - lia. }
    assert (HWspill : forall A0, getr regs 9 = Z_to_bv 64 A0 -> forall x, A0 + 304 <= x < A0 + 312 -> Frame.outside W x).
    { intros A0 E x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - apply (rn_wrap_out A A0 (sp - 32) sp x ltac:(rewrite <- Hr9; exact E)); lia.
      - apply (rn_wrap_out A A0 (fr + 2176) (fr + 2176 + 38) x ltac:(rewrite <- Hr9; exact E)); lia. }
    assert (HWsel : forall A0, getr regs 9 = Z_to_bv 64 A0 -> forall x, A0 + 16 <= x < A0 + 32 -> Frame.outside W x).
    { intros A0 E x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - apply (rn_wrap_out A A0 (sp - 32) sp x ltac:(rewrite <- Hr9; exact E)); lia.
      - apply (rn_wrap_out A A0 (fr + 2176) (fr + 2176 + 38) x ltac:(rewrite <- Hr9; exact E)); lia. }
    assert (HWsaved : forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (HWsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x).
    { intros x Hx.
      assert (Hin : in_shadow x).
      { assert (Ex : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
          by (rewrite (sh_add8 fr (x - Sfr fr) Hframe8); unfold Sfr; lia).
        rewrite <- Ex. apply AsanRTFacts.shadow_of_app. apply Hframeapp. unfold Sfr in *. lia. }
      unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hc.
      - exact (AsanRTFacts.app_not_shadow x (Hspapp x Hc) Hin).
      - exact (AsanRTFacts.app_not_shadow x (Hframeapp x ltac:(lia)) Hin). }
    assert (Hrokeep : ro_agree rsegs mem').
    { apply (rn_ro_keep mem mem' W Hro MU). intros a Hroa.
      pose proof (rn_ro_lt a Hroa) as Hlt. unfold W. cbn [Frame.outside].
      split; [|split; [|exact I]]; lia. }
    assert (HWfs : forall FS x, word_mem rsegs mem (ACi.as_tp ACi.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
      FS <= x < FS + ACi.FS_SIZE -> ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x).
    { intros FS x Hwtp HFS Hx Hnbody.
      pose proof (ACi.a_laws_fs_place ACi.ASYMS _ _ _ _ (ACi.aa_laws ACi.ASYMS AsanRTInv.RT (APIf rc))
                    (hb1 phi (rnb g b) ++ g_H g) mem md FS HAH Hwtp HFS) as (_ & HFSstk & _ & _).
      unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (HWcase : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/
      (g_S g - AFi.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx.
      destruct (Z_le_gt_dec (sp - 32) x) as [A1|A1]; destruct (Z_lt_ge_dec x sp) as [A2|A2];
        destruct (Z_le_gt_dec (fr + 2176) x) as [B1|B1];
        destruct (Z_lt_ge_dec x (fr + 2176 + 38)) as [B2|B2];
        first [ right; left; lia
              | right; right; left; lia
              | left; unfold W; cbn [Frame.outside]; split; [lia | split; [lia | exact I]] ]. }
    assert (HENT' : ENT APIf g (hb1 phi (rnb g b)) mem' md).
    { eapply ent_store;
        [ exact HENT | exact HFRA | exact MU | exact HWcase | exact HSTK' | exact HSHI' | exact HOWN' ]. }
    assert (HFRAmd : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md).
    { apply (B3FrCl.b3_fr_cl B APIf ra empty FF g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md W HFRA MU WM
        Hrokeep HAW HDJ HAH' HSTK' HWlo HWhdr (fun A0 E _ => HWspill A0 E) (fun A0 E _ => HWsel A0 E)
        HWsaved HWsh HWfs HRDM);
        (rewrite Hreg; assumption). }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAmd);
        try reflexivity. exact Hmat. }
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g b)) mem' md').
    { eapply ent_mat; [exact HENT' | exact Hmat]. }
    (* the frame bytes above the identity record are kept *)
    assert (Hapartfr : forall x, fr <= x < fr + 2176 \/ fr + 2214 <= x < fr + FRAME_BYTES -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - intro Hc. apply (Hapart x ltac:(lia)); lia.
      - lia. }
    assert (K9' : getr regs'' 9 = getr regs 9).
    { transitivity (getr R 9); [lazymatch goal with |- _ = getr _ ?r => exact (Hreg r) end | exact K9]. }
    assert (KSP : forall off w, 0 <= off <= 304 -> spill regs mem off w -> spill regs'' mem' off w).
    { intros off w Hoff Hsp.
      apply (rn_spill_keep regs regs'' mem mem' off w A W Hsp Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - apply (rn_wrap_out A A (sp - 32) sp x eq_refl); lia.
      - apply (rn_wrap_out A A (fr + 2176) (fr + 2176 + 38) x eq_refl); lia. }
    assert (KRW : forall a n bs, (fr + 2214 <= a /\ a + Z.of_nat n <= fr + FRAME_BYTES) ->
                    rw_cells rsegs mem a [CB n bs] -> rw_cells rsegs mem' a [CB n bs]).
    { intros a n bs Hr HRW. apply (rn_rwcb_keep W mem mem' a n bs MU WM); [|exact HRW].
      intros x Hx. apply Hapartfr. lia. }
    (* the cut facts at 0x81734 *)
    assert (Hsz : ACi.a_size (rnb g b) = rnb g b).
    { unfold ACi.a_size. destruct HHB as (_ & HAphi0). pose proof HAphi0 as (_ & Hn0 & _). lia. }
    destruct HHB as (Hphinz & HAphi). rewrite Hsz in HAphi.
    assert (HHB' : HB mem' phi (rnb g b)).
    { split; [exact Hphinz|]. rewrite Hsz. exact (sl_addr_keep mem mem' W phi (rnb g b) HAphi MU HAW). }
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *. apply (a_keep W mem mem' (fr + 2624) (OUR (g_in g)) MU);
        [rewrite OUR_length; intros x Hx; apply Hapartfr; lia | exact HOUR]. }
    assert (HOUTA' : OUTA fr mem') by exact (outa_run fr mem mem' W HOUTA MU HAW).
    assert (Hr23' : rg regs'' 23 (Z.of_nat b))
      by (unfold rg in *; transitivity (getr R 23);
          [exact (Hreg _) | transitivity (getr regs 23); [exact K23 | exact Hr23]]).
    assert (Hr24' : rg regs'' 24 phi)
      by (unfold rg in *; transitivity (getr R 24);
          [exact (Hreg _) | transitivity (getr regs 24); [exact K24 | exact Hr24]]).
    assert (Hr21' : rg regs'' 21 (fr + 2176))
      by (unfold rg in *; transitivity (getr R 21);
          [exact (Hreg _) | transitivity (getr regs 21); [exact K21 | exact Hr21]]).
    assert (HCUR' : CUR g 7 regs'').
    { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split;
        [ transitivity (getr R 22); [exact (Hreg _) | transitivity (getr regs 22); [exact K22 | exact Hc22]]
        | transitivity (getr R 25); [exact (Hreg _) | transitivity (getr regs 25); [exact K25 | exact Hc25]] ]. }
    assert (Ha0' : a0v regs'' 1).
    { unfold a0v, rg. transitivity (getr R 10); [exact (Hreg _) | exact K10]. }
    assert (HIDB' : IDBr g fr (RID (g_in g) (S b)) mem').
    { unfold IDBr. destruct HIc as ((_ & Hbb) & _). cbn [cells_bytes cbytes] in Hbb.
      rewrite app_nil_r in Hbb. exact Hbb. }
    assert (HFGB' : FGBr g fr (RFG (g_in g) (S b)) mem').
    { unfold FGBr in *. pose proof (rn_RS_len (g_in g) (S b)) as (_ & LFG).
      apply (a_keep W mem mem' (fr + 2256) (RFG (g_in g) (S b)) MU);
        [rewrite LFG; intros x Hx; apply Hapartfr; lia | exact HFGB]. }
    assert (HAD38' : addressable mem' (fr + 2176) 38)
      by exact (sl_addr_keep mem mem' W (fr + 2176) 38 HAD38 MU HAW).
    (* PRO (push 13B): the PRO spills are at [A + 32, A + 280) with sp <= A, our[]'s shadow is no app byte, and
       the write set is at or above the slot window's base (the ingest window) or frame body (the id record) *)
    assert (HPRO' : PRO g fr regs'' mem').
    { apply (rc_pro_keep B APIf ra g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md W A HFRA HPRO MU Hr9 HA0
               ltac:(lia) K9').
      - intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
        + apply (rn_wrap_out A A (sp - 32) sp x eq_refl); lia.
        + apply (rn_wrap_out A A (fr + 2176) (fr + 2176 + 38) x eq_refl); lia.
      - intros i Hi.
        pose proof (AsanRTFacts.shadow_of_app _ (Hframeapp (fr + 2624 + i) ltac:(lia))) as Hshq.
        unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hc.
        + exact (AsanRTFacts.app_not_shadow _ (Hspapp _ Hc) Hshq).
        + exact (AsanRTFacts.app_not_shadow _ (Hframeapp (shadow_addr (fr + 2624 + i)) ltac:(lia)) Hshq).
      - intros x Hx.
        assert (Hx' : sp - 32 <= x < sp \/ fr + 2176 <= x < fr + 2176 + 38).
        { destruct (Z_le_gt_dec (sp - 32) x) as [A1|A1]; destruct (Z_lt_ge_dec x sp) as [A2|A2];
            destruct (Z_le_gt_dec (fr + 2176) x) as [B1|B1];
            destruct (Z_lt_ge_dec x (fr + 2176 + 38)) as [B2|B2];
            first [ left; lia | right; lia
                  | exfalso; apply Hx; unfold W; cbn [Frame.outside]; split; [lia | split; [lia | exact I]] ]. }
        destruct Hx' as [Hx'|Hx'].
        + apply (rc_away_hi B APIf ra g fr (hb1 phi (rnb g b)) regs mem md x HFRA). lia.
        + apply (rc_away_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md x HFRA). lia. }
    (* rebuild the strengthened exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHB'|]. split; [exact Hr23'|].
      split; [exact HOUR'|]. split; [exact HOUTA'|]. split; [exact HCUR'|].
      split; [exact (KSP 112 _ ltac:(lia) Hs112)|].
      split; [exact (KSP 128 _ ltac:(lia) Hs128)|].
      split; [exact HPRO'|].
      split; [exact (KSP 104 _ ltac:(lia) Hs104)|].
      split; [exact (KSP 96 _ ltac:(lia) Hs96)|].
      split; [exact (KSP 64 _ ltac:(lia) Hs64)|].
      split; [exact (KSP 144 _ ltac:(lia) Hs144)|].
      split; [exact (KSP 192 _ ltac:(lia) Hs208)|].
      split; [destruct HRWid as (idb0 & Hx); exists idb0;
              exact (KRW (fr + 2688) 38%nat idb0 ltac:(cbn [Z.of_nat]; lia) Hx)|].
      split; [destruct HRWjk as (junk & Hx); exists junk;
              exact (KRW (fr + 2768) 72%nat junk ltac:(cbn [Z.of_nat]; lia) Hx)|].
      split; [exact (KSP 280 _ ltac:(lia) Hs280)|].
      split; [exact (KSP 240 _ ltac:(lia) Hs240)|].
      split; [destruct HRWjy as (jy & Hx); exists jy;
              exact (KRW (fr + 3040) 1%nat jy ltac:(cbn [Z.of_nat]; lia) Hx)|].
      split; [destruct HRWj32 as (junk & Hx); exists junk;
              exact (KRW (fr + 3056) 32%nat junk ltac:(cbn [Z.of_nat]; lia) Hx)|].
      split; [exact (KSP 152 _ ltac:(lia) Hs152)|].
      split; [exact Hr21'|].
    split; [exact HAD38'|].
    (* RXS: the nine [A + off] spills keep by position; the fragment record's 72 bytes keep their shadow *)
    split.
    { unfold RXS.
      split; [exact (KSP 48 _ ltac:(lia) Hs48)|].
      split; [exact (KSP 56 _ ltac:(lia) Hs56)|].
      split; [exact (KSP 88 _ ltac:(lia) Hs88)|].
      split; [exact (KSP 80 _ ltac:(lia) Hs80)|].
      split; [exact (KSP 72 _ ltac:(lia) Hs72)|].
      split; [exact (KSP 8 _ ltac:(lia) Hs16)|].
      split; [exact (KSP 0 _ ltac:(lia) Hs8)|].
      split; [exact (KSP 200 _ ltac:(lia) Hs192)|].
      split; [exact (KSP 216 _ ltac:(lia) Hs216)|].
      exact (sl_addr_keep mem mem' W (fr + 2256) 72 HAD72 MU HAW). }
    (* X81734 (push 11): the ingest result, s8 = Phi_r and the turn-(S b) records *)
    unfold X81734.
    split; [exact Ha0'|]. split; [exact Hr24'|].
    split; [exact Hb6|]. split; [exact HCUR'|]. split; [exact HOUR'|]. split; [exact Hr23'|].
    split; [exact HIDB' | exact HFGB'].
Qed.

End RNIngW.
