(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 877 of its 987 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R8.v, with its module paths, module names and numbers changed; 691 of its 803 lines of code are new or changed and 875 lines of the source are left out. *)
(* Shared memory / transport helpers of the image-B round-trip segments R17-R21 (asan-ubsan, fuzz_ctrl
   LLVMFuzzerTestOneInput, libreac v1.9.0). rule 24: no function proved (slot segments).

   Three groups:
   - byte, cell and stack helpers of the Lib engine (the copies lib/B/Prog/Seg/F13.v and R4.v use, renamed rh_):
     a byte run as a read, a sub-run, a spill word, a stack window across a run, the normalized-memory transfers
     (the cuts carry ro_agree, the callee contracts ask for mem_inv, so a run goes through MemNorm.evt_normalize);
   - the round-trip bundles across a run (RB / RFb / RBE);
   - FRA / ENT across the two write shapes these segments make: the frame's own shadow bytes
     [Sfr fr, Sfr fr + FRAME_SHADOW) (the `sb` poison stores; FRAME_SHADOW = 392 in v1.9.0) and a callee's stack
     window [sp - K, sp) together with the frame cells it writes. The heap invariant AH moves across both by rh_ah,
     on the real arm through AC.a_laws_store and on the side arm through AC.a_laws_fs_store. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcFrag RcSynth RcBox.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs RtmB.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module ACh := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AFh := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module MNh := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.

(* ---- byte, cell and stack helpers (the F13 / R4 copies) ---- *)

Lemma rh_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [|left; split; [lia | exact H]].
  destruct (Z_lt_ge_dec x hi) as [H2|H2]; [right; tauto | left; split; [lia | exact H]].
Qed.

Lemma rh_out1 : forall lo hi x, (x < lo \/ hi <= x) -> outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn [outside]. split; [lia | exact I]. Qed.

Lemma rh_mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof. intros m a. unfold mbyte, mrd, wa. destruct (m (Z_to_bv 64 a)); reflexivity. Qed.

Lemma rh_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (HA & HL & H) Hx.
  assert (Hi : (Z.to_nat (x - A) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - A)) Hi) as HH. rewrite Z2Nat.id in HH by lia.
  replace (A + (x - A)) with x in HH by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E; [exists b; exact HH|].
  exfalso. apply nth_error_None in E. lia.
Qed.

Lemma rh_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma rh_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.

Lemma rh_rdn : forall m a bs (n : nat), bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H Hn.
  pose proof (bytes_at_ov_read rsegs m a bs 0 n H ltac:(lia)) as HR.
  replace (a + Z.of_nat 0) with a in HR by lia.
  rewrite skipn_O, firstn_all2 in HR by lia. exact HR.
Qed.

Lemma rh_stk_keep : forall W m m' lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HR.
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  split; [apply WM; exact Hv|].
  destruct (rh_out_dec W a) as [Ho|Ho].
  - exists b. unfold mrd in *. rewrite (MU (wa a)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
  - exact (HR a Ha Ho).
Qed.

Lemma rh_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma rh_rwc_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma rh_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma rh_munch_self : forall W (m : word -> option byte), munch W m m.
Proof. intros W m a _. reflexivity. Qed.

(* ---- the read-only image and the normalized memory ---- *)

Definition rh_segs_below (sgs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sgs.

Lemma rh_find_below : forall sgs top x n s,
  rh_segs_below sgs top = true -> find_segment sgs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sgs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold rh_segs_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma rh_below_GT : rh_segs_below rsegs ACh.GT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rh_ro_hi : forall a, ACh.GT <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha.
  assert (Hu : bv_unsigned (wa a) = a) by (rewrite wa_unsigned by (unfold ACh.GT in Ha; lia); reflexivity).
  unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso.
  destruct (rh_find_below rsegs ACh.GT (bv_unsigned (wa a)) 1 s rh_below_GT E ltac:(lia)) as [L|L];
    [rewrite Hu in L; unfold ACh.GT in *; lia | lia].
Qed.

Lemma rh_ro_lt : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < ACh.GT.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (rh_find_below rsegs ACh.GT (bv_unsigned a) 1 s rh_below_GT E ltac:(lia)) as [L|L]; [exact L | lia].
Qed.

Definition rh_not_ro (A n : Z) : Prop := forall i, 0 <= i < n -> ro_addr rsegs (wa (A + i)) = false.

Lemma rh_not_ro_hi : forall A n, ACh.GT <= A -> A + n <= 2 ^ 64 -> rh_not_ro A n.
Proof. intros A n H1 H2 i Hi. apply rh_ro_hi. lia. Qed.

Lemma rh_ro_keep : forall (mem mem' : word -> option byte) (W : list ivl),
  MNh.ro_agree rsegs mem -> munch W mem mem' ->
  (forall a : word, ro_addr rsegs a = true -> outside W (bv_unsigned a)) ->
  MNh.ro_agree rsegs mem'.
Proof.
  intros mem mem' W HRO MU Hout a Hro. unfold mrd. rewrite (MU a (Hout a Hro)). exact (HRO a Hro).
Qed.

Lemma rh_ba_back : forall m m0 a bs, MNh.mem_rel rsegs m m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs.
Proof. intros m m0 a bs R H. exact (proj2 (MNh.bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma rh_rwc_norm : forall m a cs, MNh.ro_agree rsegs m -> rw_cells rsegs m a cs ->
  rh_not_ro a (Z.of_nat (cells_size cs)) -> rw_cells rsegs (MNh.normalize rsegs m) a cs.
Proof.
  intros m a cs HR ((Hwf & Hb) & Hw) Hn. split; [split; [exact Hwf|]|].
  - apply MNh.bytes_at_normalize; assumption.
  - eapply MNh.wr_at_norm; [apply MNh.mem_rel_normalize; exact HR | exact Hw | exact Hn].
Qed.

Lemma rh_rwc_back : forall m m0 a cs, MNh.mem_rel rsegs m m0 -> ACh.GT <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs REL Hlo Hhi ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (rh_ba_back m m0 a _ REL Hb).
  - destruct Hw as (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi.
    rewrite <- (MNh.wview_rel_rw rsegs m m0 (wa (a + i)) REL (rh_ro_hi (a + i) ltac:(lia))). exact (H i Hi).
Qed.

Lemma rh_stk_norm : forall m lo hi, MNh.ro_agree rsegs m -> stk rsegs m lo hi -> rh_not_ro lo (hi - lo) ->
  stk rsegs (MNh.normalize rsegs m) lo hi.
Proof.
  intros m lo hi HR (H1 & H2 & H) Hn.
  pose proof (MNh.mem_rel_normalize rsegs m HR) as REL.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  assert (RO : ro_addr rsegs (wa a) = false)
    by (specialize (Hn (a - lo) ltac:(lia)); replace (lo + (a - lo)) with a in Hn by lia; exact Hn).
  split.
  - rewrite (MNh.wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (MNh.mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma rh_stk_back : forall m m0 lo hi, MNh.mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb).
  pose proof (MNh.ro_false_of_wview rsegs m m0 (wa a) REL Hv) as RO. split.
  - rewrite <- (MNh.wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (MNh.mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma rh_addr_rel : forall m m0 p n, MNh.mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (MNh.mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma rh_shadow_gt : forall a, in_shadow a -> ACh.GT <= a < 2 ^ 64.
Proof.
  intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  unfold ACh.GT. lia.
Qed.

Lemma rh_shrw_rel : forall m m0, MNh.mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha.
  pose proof (rh_ro_hi a (rh_shadow_gt a Ha)) as RO.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (MNh.wview_rel_rw rsegs m m0 _ HR RO). exact Hw.
  - exists b. rewrite <- (MNh.mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma rh_shrw_back : forall m m0, MNh.mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha.
  pose proof (rh_ro_hi a (rh_shadow_gt a Ha)) as RO.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (MNh.wview_rel_rw rsegs m m0 _ HR RO). exact Hw.
  - exists b. rewrite (MNh.mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma rh_acells_rel : forall m m0, MNh.mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs =>
      exact (proj1 (MNh.bytes_at_rel rsegs m m0 a bs R) ltac:(assumption)) end.
Qed.

Lemma rh_acells_back : forall m m0, MNh.mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (rh_ba_back m m0 a bs R ltac:(assumption)) end.
Qed.

(* ---- spills of the 448-byte save area ---- *)

Lemma rh_rg9_eq : forall (regs : bvmap 5 word) (A A' : Z),
  rg regs 9 A -> rg regs 9 A' -> 0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A' = A.
Proof.
  intros regs A A' H H' HA HA'. pose proof (rg_eq64 regs 9 A' A H' H) as Hm.
  rewrite !Z.mod_small in Hm by lia. exact Hm.
Qed.

Lemma rh_spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) (A off v : Z),
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  q64 m (A + off) v.
Proof.
  intros regs m A off v (A' & H9' & Hq) H9 HA0 HA1 Ho0 Ho1.
  assert (EA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    pose proof Hq as Hq'. unfold q64, bytes_at in Hq'. rewrite length_le8 in Hq'.
    destruct Hq' as (Hb1 & Hb2 & _).
    revert Hm Hb1 Hb2 HA0 HA1 Ho0 Ho1. change (2 ^ 64) with 18446744073709551616. intros.
    Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

Lemma rh_spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list ivl) (A off v : Z),
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  getr regs' 9 = getr regs 9 -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v Hs H9 HA0 HA1 Ho0 Ho1 E9 MU Hout.
  pose proof (rh_spill_at regs m A off v Hs H9 HA0 HA1 Ho0 Ho1) as Hq.
  exists A. split; [unfold rg in *; exact (eq_trans E9 H9)|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8. exact Hout.
Qed.

(* ---- the round-trip bundles across a run ---- *)

Lemma rh_keep : forall W m m' a bs, munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof. intros W m m' a bs MU HO H. exact (fl_bytes W m m' a bs H MU HO). Qed.

(* RB across a run that keeps the frame records [fr + 2176, fr + 2630) and the registers s6 (22, the turn index),
   s7 (23) and s9 (25) (the input cursor CUR; v1.9.0 keeps n - c in s9, the patched image in s8). *)
Lemma rh_RB_keep : forall g fr b idb fgb regs regs' W m m',
  munch W m m' -> length idb = 38%nat -> length fgb = 72%nat ->
  (forall x, fr + 2176 <= x < fr + 2630 -> outside W x) ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  RB g fr b idb fgb regs m -> RB g fr b idb fgb regs' m'.
Proof.
  intros g fr b idb fgb regs regs' W m m' MU L1 L2 HD E22 E23 E25
    (Hb & (Hc & H23 & H25) & HO & H22 & HI & HF).
  unfold RB, CUR, OURb, IDBr, FGBr, rg in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; [rewrite E23; exact H23 | rewrite E25; exact H25]|].
  split.
  { apply (rh_keep W m m' (fr + 2624) (OUR (g_in g)) MU); [|exact HO].
    rewrite OUR_length. intros x Hx. apply HD. lia. }
  split; [rewrite E22; exact H22|].
  split.
  { apply (rh_keep W m m' (fr + 2176) idb MU); [|exact HI]. rewrite L1. intros x Hx. apply HD. lia. }
  { apply (rh_keep W m m' (fr + 2256) fgb MU); [|exact HF]. rewrite L2. intros x Hx. apply HD. lia. }
Qed.

(* RFb adds the block [phi, phi + n_b) and the register s4 (20, Phi_r). *)
Lemma rh_RFb_keep : forall g fr b idb fgb phi regs regs' W m m',
  munch W m m' -> length idb = 38%nat -> length fgb = 72%nat ->
  0 <= rnb g b -> length (rt_F (g_in g) (Z.of_nat b)) = Z.to_nat (rnb g b) ->
  (forall x, fr + 2176 <= x < fr + 2630 -> outside W x) ->
  (forall x, phi <= x < phi + rnb g b -> outside W x) ->
  getr regs' 20 = getr regs 20 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 25 = getr regs 25 ->
  RFb g fr b idb fgb phi regs m -> RFb g fr b idb fgb phi regs' m'.
Proof.
  intros g fr b idb fgb phi regs regs' W m m' MU L1 L2 Hn0 HLF HD HDp E20 E22 E23 E25 (HRB & Hnz & H20 & HF).
  unfold RFb, rg in *. rewrite E20.
  split; [exact (rh_RB_keep g fr b idb fgb regs regs' W m m' MU L1 L2 HD E22 E23 E25 HRB)|].
  split; [exact Hnz|]. split; [exact H20|].
  apply (rh_keep W m m' phi (rt_F (g_in g) (Z.of_nat b)) MU); [|exact HF].
  rewrite HLF. intros x Hx. apply HDp. rewrite Z2Nat.id in Hx by lia. exact Hx.
Qed.

(* The same keeps with the three record ranges named one by one (identity record fr + 2176 .. + 2214, fragment
   record fr + 2256 .. + 2328, our[] fr + 2624 .. + 2630), for a run that writes other frame cells between them
   (the ports words fr + 2528 .. + 2540, the declaration slot fr + 2560 .. + 2592). *)
Lemma rh_RB_keep3 : forall g fr b idb fgb regs regs' W m m',
  munch W m m' -> length idb = 38%nat -> length fgb = 72%nat ->
  (forall x, fr + 2176 <= x < fr + 2214 -> outside W x) ->
  (forall x, fr + 2256 <= x < fr + 2328 -> outside W x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> outside W x) ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  RB g fr b idb fgb regs m -> RB g fr b idb fgb regs' m'.
Proof.
  intros g fr b idb fgb regs regs' W m m' MU L1 L2 HD1 HD2 HD3 E22 E23 E25
    (Hb & (Hc & H23 & H25) & HO & H22 & HI & HF).
  unfold RB, CUR, OURb, IDBr, FGBr, rg in *.
  split; [exact Hb|].
  split; [split; [exact Hc|]; split; [rewrite E23; exact H23 | rewrite E25; exact H25]|].
  split.
  { apply (rh_keep W m m' (fr + 2624) (OUR (g_in g)) MU); [|exact HO].
    rewrite OUR_length. intros x Hx. apply HD3. lia. }
  split; [rewrite E22; exact H22|].
  split.
  { apply (rh_keep W m m' (fr + 2176) idb MU); [|exact HI]. rewrite L1. intros x Hx. apply HD1. lia. }
  { apply (rh_keep W m m' (fr + 2256) fgb MU); [|exact HF]. rewrite L2. intros x Hx. apply HD2. lia. }
Qed.

Lemma rh_RFb_keep3 : forall g fr b idb fgb phi regs regs' W m m',
  munch W m m' -> length idb = 38%nat -> length fgb = 72%nat ->
  0 <= rnb g b -> length (rt_F (g_in g) (Z.of_nat b)) = Z.to_nat (rnb g b) ->
  (forall x, fr + 2176 <= x < fr + 2214 -> outside W x) ->
  (forall x, fr + 2256 <= x < fr + 2328 -> outside W x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> outside W x) ->
  (forall x, phi <= x < phi + rnb g b -> outside W x) ->
  getr regs' 20 = getr regs 20 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 25 = getr regs 25 ->
  RFb g fr b idb fgb phi regs m -> RFb g fr b idb fgb phi regs' m'.
Proof.
  intros g fr b idb fgb phi regs regs' W m m' MU L1 L2 Hn0 HLF HD1 HD2 HD3 HDp E20 E22 E23 E25
    (HRB & Hnz & H20 & HF).
  unfold RFb, rg in *. rewrite E20.
  split; [exact (rh_RB_keep3 g fr b idb fgb regs regs' W m m' MU L1 L2 HD1 HD2 HD3 E22 E23 E25 HRB)|].
  split; [exact Hnz|]. split; [exact H20|].
  apply (rh_keep W m m' phi (rt_F (g_in g) (Z.of_nat b)) MU); [|exact HF].
  rewrite HLF. intros x Hx. apply HDp. rewrite Z2Nat.id in Hx by lia. exact Hx.
Qed.

(* ---- RBE across a run (v1.9.0 RBE, 33 conjuncts): the spills stay (the save area [A, A + 448) is outside W:
   the 21 leading spills, PRA's eleven, [A+152], [A+112] and the appended [A+160]), the addressability of out[],
   our[], the identity record, the row name and (adopt 10) the fragment record [fr + 2256, fr + 2328) stays (W is
   app memory, so no shadow byte changes), and the image bytes (the row table at BA_FR + 72, the box bytes at BOXA,
   the catalogue row at mrow, the row name) stay (below GT, which W misses). ---- *)
Lemma rh_RBE_keep : forall g fr regs regs' W m m' A,
  RBE g fr regs m -> munch W m m' -> all_app W ->
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  (forall x, A <= x < A + 448 -> outside W x) ->
  (forall x, 0 <= x < ACh.GT -> outside W x) ->
  RBE g fr regs' m'.
Proof.
  intros g fr regs regs' W m m' A H MU HAW H9 HA0 HA1 E9 HWA HWlo.
  destruct H as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUT & HA2176 & HNM & HOUR & HTBL & HBOX & HMROW &
    HPRA & S152 & S112 & HA2256 & S160).
  unfold PRA in HPRA.
  destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
  assert (K : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    exact (rh_spill_keep regs regs' m m' W A off v Hs H9 HA0 HA1 Ho0 Ho1 E9 MU (fun x Hx => HWA x ltac:(lia))). }
  assert (KB : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= ACh.GT ->
            bytes_at rsegs m a bs -> bytes_at rsegs m' a bs).
  { intros a bs H0 H1 Hb. apply (rh_keep W m m' a bs MU); [intros x Hx; apply HWlo; lia | exact Hb]. }
  pose proof (rb_mrow_range (g_in g)) as (Hmr0 & Hmr1 & _).
  unfold RBE.
  do 21 (split; [apply K; [lia | lia | assumption]|]).
  split; [unfold OUTA in *; exact (sl_addr_keep m m' W (fr + 544) 1492 HOUT MU HAW)|].
  split; [exact (sl_addr_keep m m' W (fr + 2176) 38 HA2176 MU HAW)|].
  split.
  { intros Hc. destruct (HNM Hc) as (Hok & Hbytes & Haddr & Hpos & Hhi).
    split; [exact Hok|]. split; [apply KB; [lia | lia | exact Hbytes]|].
    split; [exact (sl_addr_keep m m' W _ _ Haddr MU HAW)|]. split; [exact Hpos | exact Hhi]. }
  split; [exact (sl_addr_keep m m' W (fr + 2624) 6 HOUR MU HAW)|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HTBL]|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HBOX]|].
  split; [apply KB; [unfold CAT in Hmr0; lia | rewrite rb_mb_len; unfold CAT in Hmr1; unfold ACh.GT; lia
                    | exact HMROW]|].
  split; [unfold PRA; do 10 (split; [apply K; [lia | lia | assumption]|]); apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | assumption]|].
  split; [exact (sl_addr_keep m m' W (fr + 2256) 72 HA2256 MU HAW)|].
  apply K; [lia | lia | assumption].
Qed.

(* ---- shadow-byte helpers (the A R18 copies, renamed rh_) ---- *)

(* n present bytes form a byte run. *)
Lemma rh_bytes_of_present : forall (n : nat) (m : word -> option byte) a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat k)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros m a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). replace (a + Z.of_nat 0) with a in Hb by lia.
    destruct (IH m (a + 1) ltac:(lia) ltac:(lia)) as (bs & HBs & HL).
    { intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. apply H. lia. }
    exists (b :: bs). split; [|cbn [length]; lia].
    change (b :: bs) with ([b] ++ bs).
    apply (proj2 (bytes_at_app rsegs m a [b] bs)). split.
    + split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
      intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
      replace (a + Z.of_nat 0) with a by lia. cbn [nth_error]. exact Hb.
    + cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact HBs.
Qed.

(* Addressability across a run whose write set misses the shadow bytes of the range. *)
Lemma rh_addr_keep_rng : forall m m' W p n,
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' W p n HA MU HO. pose proof HA as (H1 & H2 & H3 & H).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (shadow_of_app (p + i) Ha) as IS. pose proof (in_shadow_range _ IS) as IR.
  unfold mrd in Hb |- *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. exact (HO i Hi).
Qed.

(* A present, writable byte run gives store_ok for each of its bytes. *)
Lemma rh_stk_store_ok : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 1 <= hi ->
  store_ok rsegs m (wa a) 1%nat = true.
Proof.
  intros m lo hi a (H1 & H2 & H) Hlo Hhi.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. assert (Ei : i = 0) by lia. subst i.
    rewrite Z.add_0_r. exact (proj1 (H a ltac:(lia))). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* n addressable bytes from n single addressable bytes. *)
Lemma rh_addr_join : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> addressable m (p + i) 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn Hend H. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hend|].
  intros i Hi. destruct (H i Hi) as (_ & _ & _ & Hb). pose proof (Hb 0 ltac:(lia)) as Hb0.
  rewrite Z.add_0_r in Hb0. exact Hb0.
Qed.

(* An aligned addressable granule has shadow byte 0, read by the instrumented check of any of its 8 bytes. *)
Lemma rh_meta0 : forall m p q, addressable m p 8 -> p mod 8 = 0 -> p <= q < p + 8 ->
  ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m p q HA Hal Hq.
  assert (Hp0 : 0 <= p) by (destruct HA as (H & _); exact H).
  assert (E : Z.shiftr q 3 = Z.shiftr p 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. revert Hal Hq Hp0. Z.div_mod_to_equations. lia. }
  rewrite E.
  destruct (meta8 m p HA) as (RC & _). destruct RC as (_ & HB).
  cbn [cells_bytes cbytes app] in HB.
  exact (rh_rdn m _ _ 1%nat HB eq_refl).
Qed.

(* A byte whose shadow byte is one of the frame's [Sfr fr + k1, Sfr fr + k2) is a frame byte of
   [fr + 8 k1, fr + 8 k2). *)
Lemma rh_sh_inv : forall fr x k1 k2, fr mod 8 = 0 -> 0 <= fr -> 0 <= x ->
  Sfr fr + k1 <= shadow_addr x < Sfr fr + k2 -> fr + 8 * k1 <= x < fr + 8 * k2.
Proof.
  intros fr x k1 k2 H8 H0 Hx. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* RBE across a run that writes only frame shadow bytes in [Sfr fr + 291, Sfr fr + 328) (the shadow of the frame
   bytes [fr + 2328, fr + 2624); the v1.9.0 round-trip loop 0x816ec-0x81ac8 stores to 296..300 / 306 / 308 / 312 /
   316 / 317 / 320..323(s3) only, s3 = S(fr)): no spill, no image byte and no shadow byte of out[] (Sfr fr + 68 ..
   254), the identity record [fr + 2176, fr + 2214) (272 .. 276), the fragment record [fr + 2256, fr + 2328) (adopt
   10; 282 .. 290), our[] (328) or the row name is among them. *)
Lemma rh_RBE_keep_sh : forall g fr regs regs' W m m' A,
  RBE g fr regs m -> munch W m m' -> fr mod 8 = 0 -> ACh.GT <= fr ->
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  (forall x, A <= x < A + 448 -> outside W x) ->
  (forall x, ~ outside W x -> Sfr fr + 291 <= x < Sfr fr + 328) ->
  RBE g fr regs' m'.
Proof.
  intros g fr regs regs' W m m' A H MU H8 HGT H9 HA0 HA1 E9 HWA HW.
  assert (HWo : forall x, (x < Sfr fr + 291 \/ Sfr fr + 328 <= x) -> outside W x).
  { intros x Hx. destruct (rh_out_dec W x) as [Ho|Ho]; [exact Ho|]. pose proof (HW x Ho). lia. }
  assert (HSfr : ACh.GT < Sfr fr) by (unfold Sfr, shadow_addr, ASAN_K, ACh.GT in *; Z.div_mod_to_equations; lia).
  destruct H as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUT & HA2176 & HNM & HOUR & HTBL & HBOX & HMROW &
    HPRA & S152 & S112 & HA2256 & S160).
  unfold PRA in HPRA.
  destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
  assert (K : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    exact (rh_spill_keep regs regs' m m' W A off v Hs H9 HA0 HA1 Ho0 Ho1 E9 MU (fun x Hx => HWA x ltac:(lia))). }
  assert (KB : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= ACh.GT ->
            bytes_at rsegs m a bs -> bytes_at rsegs m' a bs).
  { intros a bs H0 H1 Hb. apply (rh_keep W m m' a bs MU); [intros x Hx; apply HWo; lia | exact Hb]. }
  assert (KA : forall p n, addressable m p n ->
            (forall i, 0 <= i < n -> shadow_addr (p + i) < Sfr fr + 291 \/ Sfr fr + 328 <= shadow_addr (p + i)) ->
            addressable m' p n).
  { intros p n Hp Hs. apply (rh_addr_keep_rng m m' W p n Hp MU). intros i Hi. apply HWo. exact (Hs i Hi). }
  pose proof (rb_mrow_range (g_in g)) as (Hmr0 & Hmr1 & _).
  unfold RBE.
  do 21 (split; [apply K; [lia | lia | assumption]|]).
  split.
  { unfold OUTA in *. apply (KA _ _ HOUT). intros i Hi. left.
    unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  split.
  { apply (KA _ _ HA2176). intros i Hi. left. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  split.
  { intros Hc. destruct (HNM Hc) as (Hok & Hbytes & Haddr & Hpos & Hhi).
    split; [exact Hok|]. split; [apply KB; [lia | lia | exact Hbytes]|].
    split; [|split; [exact Hpos | exact Hhi]].
    apply (KA _ _ Haddr). intros i Hi. left.
    unfold Sfr, shadow_addr, ASAN_K, ACh.GT in *. Z.div_mod_to_equations. lia. }
  split.
  { apply (KA _ _ HOUR). intros i Hi. right. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HTBL]|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HBOX]|].
  split; [apply KB; [unfold CAT in Hmr0; lia | rewrite rb_mb_len; unfold CAT in Hmr1; unfold ACh.GT; lia
                    | exact HMROW]|].
  split; [unfold PRA; do 10 (split; [apply K; [lia | lia | assumption]|]); apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | assumption]|].
  split; [apply (KA _ _ HA2256); intros i Hi; left; unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia|].
  apply K; [lia | lia | assumption].
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864). *)
Lemma rh_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACh.a_fs_hint in Hr. assert (0 <= Z.of_nat c) by lia. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* ---- Contract.v laws and definitions taken apart ONCE each in this file (a Theorem Labs lane via a Theorem Labs lane 15:32Z: a later
   generation appends conjuncts / disjuncts at any nesting level, so each inner list is destructured in exactly
   one place below and every site uses these lemmas). ---- *)

(* a_store_ok (Contract.v:103): the real-stack disjunct and the real-stack shadow disjunct. *)
Lemma rh_sok_rng : forall H lo a, lo <= a < APPMEM_END -> ACh.a_store_ok H lo a.
Proof. intros H lo a Ha. unfold ACh.a_store_ok. right; left. exact Ha. Qed.

Lemma rh_sok_sh : forall H lo a b, a = shadow_addr b -> lo <= b < APPMEM_END -> ACh.a_store_ok H lo a.
Proof.
  intros H lo a b Eb Hb. unfold ACh.a_store_ok. right; right; right. exists b. split; [exact Eb|].
  right; left. exact Hb.
Qed.

(* a_fs_ok (Contract.v:122): every side-stack byte is present. *)
Lemma rh_fs_ok_rd : forall mem FS a, ACh.a_fs_ok mem FS -> FS <= a < FS + ACh.FS_SIZE ->
  exists b, mbyte rsegs mem a = Some b.
Proof. intros mem FS a (Hb & _) Ha. exact (proj2 (Hb a Ha)). Qed.

(* a_in_fs (Contract.v:109): the side-stack base FS (the word at tp) and the byte's place in [FS, FS + FS_SIZE). *)
Lemma rh_in_fs : forall mem a, ACh.a_in_fs ACh.ASYMS mem a ->
  exists FS, 0 <= FS < 2 ^ 64 /\ word_mem rsegs mem (ACh.as_tp ACh.ASYMS) FS /\ FS <= a < FS + ACh.FS_SIZE.
Proof. intros mem a (FS & H0 & H1 & H2). exists FS. split; [exact H0|]. split; [exact H1 | exact H2]. Qed.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACh.AsanAllocAPI ACh.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* a_laws_blocks: a live block lies at or above 4096, below stklo, ends in application memory, and each of its
   bytes is application memory, writable and outside the side stack. *)
Lemma rh_blocks : forall H mem md p n,
  ACh.aa_AH ACh.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  4096 <= p /\ p + n <= ACh.aa_stklo ACh.ASYMS AsanRTInv.RT (APIf rc) mem md /\ end_in_app p n /\
  (forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ ACh.a_in_fs ACh.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  pose proof (ACh.a_laws_blocks ACh.ASYMS _ _ _ _ (ACh.aa_laws ACh.ASYMS AsanRTInv.RT (APIf rc))
                H mem md p n HAH Hin) as L.
  (* each conjunct picked by its statement, never by position (a Theorem Labs lane 15:18Z) *)
  decompose [and] L. split; [assumption|]. split; [assumption|]. split; [assumption|].
  intros a Ha.
  match goal with Hb : forall a, p <= a < p + n -> _ |- _ => pose proof (Hb a Ha) as La end.
  decompose [and] La. split; [assumption|]. split; assumption.
Qed.

(* a_laws_fs_place: the side stack FS (the word at tp) is above GT, wholly below stklo, application memory. *)
Lemma rh_fs_place : forall H mem md FS,
  ACh.aa_AH ACh.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (ACh.as_tp ACh.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  ACh.GT <= FS /\ FS + ACh.FS_SIZE <= ACh.aa_stklo ACh.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, FS <= a < FS + ACh.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Htp HFS.
  pose proof (ACh.a_laws_fs_place _ _ _ _ _ (ACh.aa_laws ACh.ASYMS AsanRTInv.RT (APIf rc))
                H mem md FS HAH Htp HFS) as L.
  decompose [and] L. split; [assumption|]. split; assumption.
Qed.

(* a_laws_fs_state: the side stack's runtime state a_fs_ok. *)
Lemma rh_fs_state : forall H mem md FS,
  ACh.aa_AH ACh.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (ACh.as_tp ACh.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> ACh.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Htp HFS.
  decompose [and ex] (ACh.a_laws_fs_state _ _ _ _ _ (ACh.aa_laws ACh.ASYMS AsanRTInv.RT (APIf rc))
                        H mem md FS HAH Htp HFS).
  assumption.
Qed.

(* The single live harness block (phi, n) of FRA's heap list is placed, aligned low, below the real stack, in
   application memory and writable (Contract.a_laws_blocks). *)
Lemma rh_hb : forall g fr phi n regs mem md,
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  phi <> 0 /\ 4096 <= phi /\ phi + n <= ACh.aa_stklo ACh.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  end_in_app phi n /\ (forall a, phi <= a < phi + n -> app_mem a /\ writable_at rsegs mem a).
Proof.
  intros g fr phi n regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & _ & HAH & _).
  destruct (rh_blocks (hb1 phi n ++ g_H g) mem md phi n HAH
              ltac:(unfold hb1; apply in_or_app; left; apply in_eq)) as (Hlo & Hhi & Hein & Hbytes).
  split; [lia|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hein|].
  intros a Ha. destruct (Hbytes a Ha) as (Hap & Hwr & _). split; [exact Hap | exact Hwr].
Qed.

(* The harness block (phi, n) and the FRAME_BYTES-byte frame (3136 in v1.9.0) are disjoint: on the real arm the
   block is below stklo <= fr; on the side arm the frame is in the side stack and no block byte is
   (a_laws_blocks). *)
Lemma rh_blk_fr : forall g fr phi n regs mem md,
  FRA B APIf ra g fr (hb1 phi n) regs mem md -> 0 < n -> fr + FRAME_BYTES <= phi \/ phi + n <= fr.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr phi n regs mem md HFRA Hn.
  pose proof (rh_hb g fr phi n regs mem md HFRA) as (_ & _ & Hphistk & _ & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & _).
  destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & HfsbS & Hfs & _)].
  - right. pose proof (Hreal fr ltac:(lia)) as (Hlo & _). lia.
  - destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [Hle|Hgt]; [left; exact Hle|].
    destruct (Z_le_gt_dec (phi + n) fr) as [Hle2|Hgt2]; [right; exact Hle2|].
    exfalso.
    destruct (rh_blocks (hb1 phi n ++ g_H g) mem md phi n HAH
                ltac:(unfold hb1; apply in_or_app; left; apply in_eq)) as (_ & _ & _ & Hbb).
    destruct (Hbb (Z.max phi fr) ltac:(lia)) as (_ & _ & Hnfs).
    exact (Hnfs (Hfs (Z.max phi fr) ltac:(lia))).
Qed.

(* The frame's shadow byte at offset k is the shadow of the frame byte at offset 8 k. *)
Lemma rh_sh_off : forall fr k, 0 <= k -> shadow_addr (fr + k * 8) = Sfr fr + k.
Proof.
  intros fr k Hk. unfold Sfr, shadow_addr. rewrite Z.div_add by lia. lia.
Qed.

(* Every byte of the frame's FRAME_SHADOW shadow bytes (392 in v1.9.0) is a shadow byte of the frame body. *)
Lemma rh_sh_in : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW ->
    in_shadow x /\ exists b, fr <= b < fr + FRAME_BYTES /\ x = shadow_addr b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA x Hx.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  assert (Ex : shadow_addr (fr + (x - Sfr fr) * 8) = x) by (rewrite rh_sh_off by lia; unfold Sfr; lia).
  split.
  - rewrite <- Ex. apply shadow_of_app. apply Happ. lia.
  - exists (fr + (x - Sfr fr) * 8). split; [lia | symmetry; exact Ex].
Qed.

(* ---- AH, ownership and the stack bounds across a write confined to the slot window, the frame body and the
   frame's shadow bytes. Real arm: every such byte is a_store_ok (the window and the frame are in
   [stklo, APPMEM_END), the shadow bytes are the shadow of the frame). Side arm: the frame is the FakeStack's,
   so the write goes through AC.a_laws_fs_store (Tac_fs.a_fs_ok_pres keeps a_fs_ok), whose metadata cells lie
   below FS + 36864 <= fr and are outside the write set. ---- *)
Lemma rh_ah : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall x, ~ outside W x ->
     (g_S g - AFh.SLOT_STACK <= x < g_S g) \/ (fr + 24 <= x < fr + FRAME_BYTES) \/
     (Sfr fr <= x < Sfr fr + FRAME_SHADOW)) ->
  (forall x, 0 <= x < 2 ^ 64 -> (exists b, mbyte rsegs mem x = Some b) -> exists b, mbyte rsegs mem' x = Some b) ->
  ACh.aa_AH ACh.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, ACh.aa_owned ACh.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
             ACh.aa_owned ACh.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
  ACh.aa_stklo ACh.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACh.aa_stklo ACh.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  ACh.aa_stkhi ACh.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACh.aa_stkhi ACh.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md W HFRA MU WM HW HPres.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Happ).
  pose proof (rh_sh_in g fr hb regs mem md HFRA) as Hshin.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACh.aa_laws ACh.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (ACh.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AFh.SLOT_STACK = 1048576) by reflexivity.
  assert (HWR : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Ha; exact (WM (Z_to_bv 64 a) Ha)).
  destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & HfsbS & Hfs & HFSREC)].
  - (* real arm *)
    assert (Hunch : forall a, 0 <= a < 2 ^ 64 ->
      ~ ACh.a_store_ok (hb ++ g_H g) (ACh.aa_stklo ACh.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns.
      destruct (rh_out_dec W a) as [Ho|Ho];
        [apply MU; rewrite MState.unsigned_lit by lia; exact Ho|].
      exfalso. apply Hns.
      destruct (HW a Ho) as [Hc|[Hc|Hc]].
      - apply rh_sok_rng. unfold APPMEM_END in *. lia.
      - apply rh_sok_rng. exact (Hreal a ltac:(lia)).
      - destruct (Hshin a Hc) as (_ & (bb & Hbb & Eb)).
        exact (rh_sok_sh _ _ a bb Eb (Hreal bb Hbb)). }
    destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH Hunch HWR) as [HAH' HOWN' HSTK' HSHI'].
    split; [exact HAH'|]. split; [exact HOWN'|]. split; [exact HSTK' | exact HSHI'].
  - (* side arm: the frame is in the FakeStack *)
    destruct (rh_in_fs mem (fr + FRAME_BYTES - 1) (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)))
      as (FSb & HFSb0 & HwFSb & HFSbr).
    pose proof (HfsbS FSb HwFSb HFSb0) as HfrGE.
    pose proof (rh_fs_place (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0) as (HGTfs & HFSstk & HFSapp).
    assert (HFSz : FSb + ACh.FS_SIZE <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
    assert (HFSsz : ACh.FS_SIZE = 11571200) by reflexivity.
    pose proof (rh_fs_state (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0) as Hfsok.
    assert (Hmeta : forall q, fs_meta FSb q -> outside W q).
    { intros q Hq.
      pose proof (rh_fs_meta_range FSb q Hq) as (Hq0 & Hq1).
      destruct (rh_out_dec W q) as [Ho|Ho]; [exact Ho|].
      exfalso. destruct (HW q Ho) as [Hc|[Hc|Hc]].
      - (* a metadata cell is inside the FakeStack, which is below stklo <= S - SLOT_STACK *)
        lia.
      - lia.
      - destruct (Hshin q Hc) as (Hsh' & _).
        pose proof (HFSapp q ltac:(lia)) as Happq.
        exact (app_not_shadow q Happq Hsh'). }
    assert (Hfsok' : ACh.a_fs_ok mem' FSb).
    { apply (a_fs_ok_pres W mem mem' FSb Hfsok MU HWR HPres Hmeta ltac:(lia) HFSz). }
    assert (Hunch : forall a, 0 <= a < 2 ^ 64 ->
      ~ ACh.a_store_ok (hb ++ g_H g) (ACh.aa_stklo ACh.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FSb <= a < FSb + ACh.FS_SIZE) ->
      ~ (exists bb, FSb <= bb < FSb + ACh.FS_SIZE /\ a = shadow_addr bb) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns HnFS Hnsh.
      destruct (rh_out_dec W a) as [Ho|Ho];
        [apply MU; rewrite MState.unsigned_lit by lia; exact Ho|].
      exfalso. destruct (HW a Ho) as [Hc|[Hc|Hc]].
      - apply Hns. apply rh_sok_rng. unfold APPMEM_END in *. lia.
      - apply HnFS. lia.
      - destruct (Hshin a Hc) as (_ & (bb & Hbb & Eb)).
        apply Hnsh. exists bb. split; [lia | exact Eb]. }
    destruct (lw_fs_store (APIf rc) (hb ++ g_H g) mem mem' md FSb HAH HwFSb HFSb0 Hunch HWR Hfsok')
      as [HAH' HOWN' HSTK' HSHI'].
    split; [exact HAH'|]. split; [exact HOWN'|]. split; [exact HSTK' | exact HSHI'].
Qed.

(* Every frame byte is present: on the real arm the frame is inside the entry-anchored slot window, on the side
   arm it is inside the side stack, whose bytes a_fs_ok keeps mapped. *)
Lemma rh_frame_rd : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  forall a, fr <= a < fr + FRAME_BYTES -> exists b, mbyte rsegs mem a = Some b.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr hb regs mem md HFRA a Ha.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AFh.SLOT_STACK = 1048576) by reflexivity.
  destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & HfsbS & Hfs & _)].
  - pose proof Hwin as Hw. destruct Hw as (_ & _ & Hwv).
    destruct (Hwv a ltac:(lia)) as (_ & bb & Hbb). exists bb. rewrite rh_mbyte_mrd. exact Hbb.
  - destruct (rh_in_fs mem a (Hfs a Ha)) as (bb & Hb0 & Hwtp & Hbr).
    exact (rh_fs_ok_rd mem bb a (rh_fs_state (hb ++ g_H g) mem md bb HAH Hwtp Hb0) Hbr).
Qed.

(* The catalogue (v1.9.0 BOX_CATALOGUE, frame_AG's (0x9f620, 3256)) is one of the registered globals, so each of
   its bytes is addressable. *)
Lemma rh_cat_addr : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md -> forall a, CAT <= a < CAT + 3256 -> addressable mem a 1.
Proof.
  intros g fr hb regs mem md HFRA a Ha.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  apply HAG. exists 0x9f620, 3256. split; [|unfold CAT in Ha; lia].
  unfold AFh.frame_AG. cbn [In]. repeat (first [ left; reflexivity | right ]).
Qed.

(* FRA and ENT across stores into the frame's own shadow bytes [Sfr fr + lo, Sfr fr + hi) (the `sb` poison /
   unpoison runs; hi <= FRAME_SHADOW = 392 in v1.9.0): sl_fr_meta with AH from rh_ah, ENT by ent_store. *)
Lemma rh_sh_move : forall g fr hb regs regs' mem mem' md lo hi,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  0 <= lo -> lo <= hi -> hi <= FRAME_SHADOW ->
  munch [(Sfr fr + lo, Sfr fr + hi)] mem mem' -> wmono rsegs mem mem' ->
  (forall qq, Sfr fr + lo <= qq < Sfr fr + hi -> exists b, mrd rsegs mem' (wa qq) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md lo hi HFRA HENT Hlo Hlh Hhi MU WM HPres E2 E3 E4 E8 E9 E19 E26.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof (rh_sh_in g fr hb regs mem md HFRA) as Hshin.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACh.a_laws_stack_high _ _ _ _ _ (ACh.aa_laws ACh.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AFh.SLOT_STACK = 1048576) by reflexivity.
  assert (HGT' : ACh.GT <= fr) by exact HGT.
  unfold ACh.GT in HGT.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia).
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (Hshin (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as (IS & _).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); unfold APPMEM_END in *; lia).
  set (W := [(Sfr fr + lo, Sfr fr + hi)]).
  assert (HoutW : forall x, (x < Sfr fr + lo \/ Sfr fr + hi <= x) -> outside W x)
    by (intros x Hx; unfold W; cbn [outside]; split; [lia | exact I]).
  assert (HW3 : forall x, ~ outside W x ->
     (g_S g - AFh.SLOT_STACK <= x < g_S g) \/ (fr + 24 <= x < fr + FRAME_BYTES) \/
     (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
  { intros x Hx. right; right. unfold W in Hx. cbn [outside] in Hx. lia. }
  assert (Hpres : forall x, 0 <= x < 2 ^ 64 -> (exists b, mbyte rsegs mem x = Some b) ->
            exists b, mbyte rsegs mem' x = Some b).
  { intros x Hx Hb. destruct (rh_out_dec W x) as [Ho|Ho].
    - rewrite !rh_mbyte_mrd in Hb |- *. unfold mrd in *.
      rewrite (MU (wa x)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
    - unfold W in Ho. cbn [outside] in Ho. rewrite rh_mbyte_mrd. apply HPres. lia. }
  destruct (rh_ah g fr hb regs mem mem' md W HFRA MU WM HW3 Hpres) as (HAH' & HOWN' & HSTK' & HSHI').
  assert (Hsh' : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { destruct Hsh as (sh0 & Hb0 & HL0).
    change (Z.to_nat FRAME_SHADOW) with 392%nat in HL0 |- *.
    assert (HSfr0 : 0 <= Sfr fr) by (unfold ASAN_K in HSfrlo; lia).
    unfold HIGHMEM_BEG in HSfrhi.
    apply (rh_bytes_of_present 392%nat mem' (Sfr fr)); [lia | lia |].
    intros k Hk. rewrite <- rh_mbyte_mrd. apply Hpres; [lia|].
    pose proof (proj2 (proj2 Hb0) k ltac:(lia)) as Hb0k.
    destruct (nth_error sh0 k) as [b|] eqn:Ek; [|exfalso; apply nth_error_None in Ek; lia].
    exists b. rewrite rh_mbyte_mrd. exact Hb0k. }
  assert (HA9 : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 -> A0 = A)
    by (intros A0 HA0r HA0b; exact (rh_rg9_eq regs A A0 Hr9 HA0r HA64 HA0b)).
  assert (Hrokeep : ro_agree rsegs mem').
  { apply (rh_ro_keep mem mem' W Hro MU). intros x Hx.
    pose proof (rh_ro_lt x Hx) as Hlt. unfold ACh.GT in Hlt. apply HoutW. left. unfold ASAN_K in HSfrlo. lia. }
  assert (HDJ : rt_disjoint W).
  { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
      RT_AGLOB, RT_AGLOB_LEN.
    unfold W. cbn [disjoint_from]. unfold ASAN_K in HSfrlo.
    repeat split; first [left; lia | right; lia | exact I]. }
  assert (HWkept : forall x, 0 <= x < 2 ^ 64 -> ~ (fr + 24 <= x < fr + FRAME_BYTES) ->
            ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> outside W x).
  { intros x Hx Hnb Hnsh. apply HoutW. lia. }
  assert (HWspill : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
            forall x, A0 + 336 <= x < A0 + 344 -> outside W x).
  { intros A0 HA0r HA0b x Hx. rewrite (HA9 A0 HA0r HA0b) in Hx. apply HoutW. right.
    unfold HIGHMEM_BEG in *. lia. }
  assert (HWsaved : forall x, g_S g - 104 <= x < g_S g -> outside W x)
    by (intros x Hx; apply HoutW; right; unfold HIGHMEM_BEG in *; lia).
  assert (HWsel : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
            forall x, A0 + 40 <= x < A0 + 56 -> outside W x).
  { intros A0 HA0r HA0b x Hx. rewrite (HA9 A0 HA0r HA0b) in Hx. apply HoutW. right.
    unfold HIGHMEM_BEG in *. lia. }
  assert (HWwin : forall x, g_S g - AFh.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mem' (wa x) = Some b)
    by (intros x Hx; left; apply HoutW; right; unfold HIGHMEM_BEG in *; lia).
  assert (HAG' : forall a, in_globals AFh.frame_AG a -> addressable mem' a 1).
  { intros a Hin. apply (addr1_munch W mem mem' a MU); [|exact (HAG a Hin)].
    apply HoutW. left.
    destruct Hin as (lo0 & len0 & Hinl & Hr).
    assert (HAGb : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? ACh.GT)) AFh.frame_AG = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in HAGb. specialize (HAGb (lo0, len0) Hinl). cbn [fst snd] in HAGb.
    apply andb_true_iff in HAGb as (Hg0 & Hg1). apply Z.leb_le in Hg0, Hg1. unfold ACh.GT in Hg1.
    unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  split.
  - exact (sl_fr_meta B APIf ra empty FF g fr hb regs regs' mem mem' md W HFRA MU WM Hrokeep HDJ HAH' HSTK'
             Happ HGT' Hsh' HWkept HWspill HWsaved HWsel HWwin HAG' E2 E3 E4 E8 E9 E19 E26).
  - apply (ent_store B APIf ra g fr hb regs mem mem' md W HENT HFRA MU); [| exact HSTK' | exact HSHI' |].
    + intros x Hx. destruct (rh_out_dec W x) as [Ho|Ho]; [left; exact Ho|].
      right; right; right. unfold W in Ho. cbn [outside] in Ho. lia.
    + intros a Himg Ho. exact (proj2 (HOWN' a) Ho).
Qed.

End S.
