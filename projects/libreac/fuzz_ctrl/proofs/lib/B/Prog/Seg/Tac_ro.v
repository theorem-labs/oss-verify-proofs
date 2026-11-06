(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 485 of its 520 lines of code are new or changed and 361 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F8.v; 211 of its 266 lines of code are new or changed and 465 lines of the source are left out. *)
(* Normalized-memory transfer helpers for the fuzz_ctrl LLVMFuzzerTestOneInput slot proof (asan-ubsan, image B).

   Push 5c took mem_inv out of FRA and out of the segment cuts: a cut now carries ro_agree alone. A callee
   contract that asks for mem_inv is reached through MemNorm.evt_normalize instead: the segment runs its body on
   the normalized memory `normalize rsegs m` (which has mem_inv by mem_inv_normalize), and evt_normalize carries
   the run back to the real memory m, leaving `mem_rel rsegs m (normalize rsegs m)` and `ro_same` to move the
   facts across. The lemmas here are that move, in both directions:

   - ro_hi: above the image there is no read-only byte, so normalizing changes nothing at or above LOWMEM_END
     (the shadow map's first byte). Every address a segment of this file speaks of -- a shadow byte
     (in_shadow a: LOWMEM_END <= a) and the whole slot stack window (HIGHMEM_BEG <= a) -- is at or above it.
   - wview_hi: hence writability is the same on both memories there;
   - stk_rel / stk_rel_back, shadow_rw_rel: the stack window and the shadow map, out and back;
   - ba_rel, addressable_rel, asan_cells_rel: the read-side facts a run premise needs, out.

   The image-A twin of these lemmas is lib/A/Prog/Seg/F18.v (ro_addr_hi .. asan_cells_rel). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require BzBridge.
(* The fragment-record model (fg_next / fg_class and the rf_* length facts) for the record lengths below, imported
   before SlotModel / SlotInv as lib/B/Prog/Seg/F8.v does. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
Import ListNotations.
Local Open Scope Z_scope.

Module BZB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzBridge.

(* Every segment of image B ends below the shadow map's first byte. *)
Lemma segs_below_low : BZB.seg_tops_below rsegs LOWMEM_END = true.
Proof. vm_compute. reflexivity. Qed.

(* Above the image there is no read-only byte, so normalizing changes nothing there. *)
Lemma ro_hi : forall a, LOWMEM_END <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold LOWMEM_END in Ha. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  destruct (BZB.find_segment_below rsegs LOWMEM_END (bv_unsigned (wa a)) 1 s segs_below_low E ltac:(lia))
    as [L|L]; [exfalso; rewrite MState.unsigned_lit in L by lia; unfold LOWMEM_END in L; lia | cbn in L; lia].
Qed.

Lemma wview_hi : forall m m0 a, mem_rel rsegs m m0 -> LOWMEM_END <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (ro_hi a Ha)). split; auto.
Qed.

Lemma stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> LOWMEM_END <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma stk_rel_back : forall m m0 lo hi, mem_rel rsegs m m0 -> LOWMEM_END <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (wview_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma shadow_rw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_hi m m0 a HR ltac:(unfold LOWMEM_END; lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma addressable_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma ba_rel : forall m m0 a bs, mem_rel rsegs m m0 -> bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs.
Proof. intros m m0 a bs R H. exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma asan_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (ba_rel m m0 a bs R ltac:(assumption)) end.
Qed.

(* The frame-loop set FLI (SlotInv.v, v1.9.0: 28 positions) is s11 = -8, the spills of the spill base A = reg 9
   (positions 2-22, plus the appended 27 = [A+168] = fr + 2880 again and 28 = [A+88] = fr + 2885), our[]'s six
   bytes addressable, the frame body's stack facts stk fr (fr + FRAME_BYTES), RAD (the identity record
   [fr + 2688, fr + 2726), the fragment record [fragb fr, fragb fr + 72) and the local `first` [fr + 2880,
   fr + 2920) addressable) and KNT (the kind-name table's bytes and their addressability, 112 bytes at
   KNC.KIND_NAME). A segment that keeps reg 9 and reg 27, that carries its own spill transporter (memory kept, or
   kept outside the spill window) and that gives the six memory facts on its new memory carries FLI, and with the
   our[] bytes also LK. Every frame-loop cut holds LK, so each of this unit's segments needs the pair; they live
   here rather than in each file. KNT speaks of the new memory, so it is a premise like the other five; the
   addressability of `first` (RAD's third range) is the last premise of the six. knt_munch proves KNT for a run
   whose write list misses the table: the table is image data, and the runs of the frame loop write the spill
   window, the frame, the frame's shadow, the turn's heap block and their callees' stack windows. *)
Lemma knt_munch : forall W (m m' : word -> option byte), KNT m -> munch W m m' -> meta_kept m m' ->
  (forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 -> outside W x) -> KNT m'.
Proof.
  intros W m m' (Hb & Hadr) MU MK HO.
  assert (HL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
  split.
  - apply (fl_bytes W m m' KNC.KIND_NAME KNC.kind_name_bytes Hb MU).
    rewrite HL. intros x Hx. apply HO. lia.
  - exact (addressable_kept m m' KNC.KIND_NAME 112 Hadr MK).
Qed.

Lemma fli_keep : forall g fr (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  FLI g fr regs m -> rg regs' 27 (-8) ->
  addressable m' (fr + 2624) 6 -> stk rsegs m' fr (fr + FRAME_BYTES) ->
  addressable m' (fr + 2688) 38 -> addressable m' (fragb fr) 72 -> KNT m' ->
  addressable m' (fr + 2880) 40 ->
  (forall off v, 0 <= off <= 336 -> spill regs m off v -> spill regs' m' off v) ->
  FLI g fr regs' m'.
Proof.
  intros g fr regs regs' m m' H H27 Had Hstk Hid Hfg HKNT Hfst K. unfold FLI, RAD in H |- *.
  destruct H as (_ & H168 & H96 & H112 & H120 & H128 & H136 & H144 & H152 & H280 & H160 & H176 & H192 & H200 &
    H216 & H208 & H104 & H256 & H264 & H288 & H296 & H304 & _ & _ & _ & _ & H168b & H88).
  repeat match goal with |- _ /\ _ => split end;
    solve [ exact H27 | exact Had | exact Hstk | exact Hid | exact Hfg | exact HKNT | exact Hfst
          | apply K; [lia | assumption] ].
Qed.

(* The six memory facts of FLI, by name (a segment moves them to its new memory itself): our[]'s six bytes
   addressable, the frame's stk, RAD's first two record ranges addressable, KNT's kind-name table, and (appended
   last, v1.9.0) RAD's third range, the local `first` addressable. *)
Lemma fli_mem : forall g fr (regs : bvmap 5 word) (m : word -> option byte),
  FLI g fr regs m -> addressable m (fr + 2624) 6 /\ stk rsegs m fr (fr + FRAME_BYTES) /\
    addressable m (fr + 2688) 38 /\ addressable m (fragb fr) 72 /\ KNT m /\ addressable m (fr + 2880) 40.
Proof.
  intros g fr regs m H. unfold FLI, RAD in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Had & Hstk &
    (Hid & Hfg & Hfst) & HKNT & _ & _).
  split; [exact Had|]. split; [exact Hstk|]. split; [exact Hid|]. split; [exact Hfg|]. split; [exact HKNT | exact Hfst].
Qed.

Lemma lk_keep : forall g fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  LK g fr j regs m -> rg regs' 27 (-8) ->
  addressable m' (fr + 2624) 6 -> stk rsegs m' fr (fr + FRAME_BYTES) ->
  addressable m' (fr + 2688) 38 -> addressable m' (fragb fr) 72 -> KNT m' -> addressable m' (fr + 2880) 40 ->
  OURb g fr m' ->
  (forall off v, 0 <= off <= 336 -> spill regs m off v -> spill regs' m' off v) ->
  LK g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' H H27 Had Hstk Hid Hfg HKNT Hfst HOUR K.
  destruct H as (Hj & H240 & _ & HFLI).
  split; [exact Hj|]. split; [apply K; [lia | exact H240]|]. split; [exact HOUR|].
  exact (fli_keep g fr regs regs' m m' HFLI H27 Had Hstk Hid Hfg HKNT Hfst K).
Qed.

(* Adopt 6 added three per-turn bundles to the frame-loop cuts: FTURN (the cursor spills [A+224] / [A+232] and the
   frame's bytes at Phi), the record pair FREC (REC0 / RECR / RECF / RECS: the identity record at fr + 2688 and the
   fragment record at fr + 2768) and IFS (both records and the first-fragment state FSj). FTURN's parts are spills
   over reg 9 and a byte list at Phi; FREC's and FSj's are byte lists at fixed frame addresses (v1.9.0: FSj is the
   frame local `first`, have / n / body at fr + 2880 / 2884 / 2885 and its 40 bytes addressable). So a segment
   moves a bundle with its own spill transporter and its own byte transport at those addresses. *)
Lemma spill_reg9 : forall (regs regs' : bvmap 5 word) m off v,
  getr regs' 9 = getr regs 9 -> spill regs m off v -> spill regs' m off v.
Proof. intros regs regs' m off v E (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E; exact HA | exact Hq]. Qed.

Lemma turn_keep : forall g j phi (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  FTURN g j phi regs m ->
  (forall off v, 0 <= off <= 336 -> spill regs m off v -> spill regs' m' off v) ->
  (bytes_at rsegs m phi (t_phi (g_in g) j) -> bytes_at rsegs m' phi (t_phi (g_in g) j)) ->
  FTURN g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' (H224 & H232 & Hphi & Hlen) K KB.
  split; [apply K; [lia | exact H224]|]. split; [apply K; [lia | exact H232]|].
  split; [exact (KB Hphi) | exact Hlen].
Qed.

Lemma turn_reg : forall g j phi (regs regs' : bvmap 5 word) m,
  getr regs' 9 = getr regs 9 -> FTURN g j phi regs m -> FTURN g j phi regs' m.
Proof.
  intros g j phi regs regs' m E H. apply (turn_keep g j phi regs regs' m m H); [|exact (fun X => X)].
  intros off v _ Hs. exact (spill_reg9 regs regs' m off v E Hs).
Qed.

Lemma frec_keep : forall g fr idb st (m m' : word -> option byte),
  FREC g fr idb st m ->
  (bytes_at rsegs m (fr + 2688) idb -> bytes_at rsegs m' (fr + 2688) idb) ->
  (bytes_at rsegs m (fr + 2768) st -> bytes_at rsegs m' (fr + 2768) st) ->
  FREC g fr idb st m'.
Proof.
  intros g fr idb st m m' ((Hid & Hidok) & (Hfg & Hfgok)) KI KF.
  split; split; [exact (KI Hid) | exact Hidok | exact (KF Hfg) | exact Hfgok].
Qed.

(* The body of the first-fragment state is at most 23 bytes: the bytes after position 27 of the 50-byte frame
   prefix t_g (fs0's body is empty, and a turn either keeps the body or takes firstn _ (skipn 27 g)). So the three
   facts of FSb lie inside `first`, [fr + 2880, fr + 2920). *)
Lemma tr_body_length : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn. lia.
  - rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

Lemma fsj_keep : forall g fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  FSj g fr j regs m ->
  (forall a bs, fr + 2880 <= a -> a + Z.of_nat (length bs) <= fr + 2920 ->
     bytes_at rsegs m a bs -> bytes_at rsegs m' a bs) ->
  addressable m' (fr + 2880) 40 ->
  FSj g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' H KB Hfst. unfold FSj, FSb, u32, b8 in *.
  destruct H as (Hh & Hn & Hb & _ & HFI).
  pose proof (tr_body_length (g_in g) j) as Hbl.
  split; [apply KB; [lia | rewrite length_le4; lia | exact Hh]|].
  split; [apply KB; [lia | cbn [length]; lia | exact Hn]|].
  split; [apply KB; [lia | lia | exact Hb]|].
  split; [exact Hfst | exact HFI].
Qed.

Lemma ifs_keep : forall g fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  IFS g fr j regs m ->
  (bytes_at rsegs m (fr + 2688) (t_ID (g_in g) j) -> bytes_at rsegs m' (fr + 2688) (t_ID (g_in g) j)) ->
  (bytes_at rsegs m (fr + 2768) (t_FG (g_in g) j) -> bytes_at rsegs m' (fr + 2768) (t_FG (g_in g) j)) ->
  (forall a bs, fr + 2880 <= a -> a + Z.of_nat (length bs) <= fr + 2920 ->
     bytes_at rsegs m a bs -> bytes_at rsegs m' a bs) ->
  addressable m' (fr + 2880) 40 ->
  IFS g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' ((Hid & Hidok) & (Hfg & Hfgok) & HFS) KI KF KB Hfst.
  split; [split; [exact (KI Hid) | exact Hidok]|].
  split; [split; [exact (KF Hfg) | exact Hfgok]|].
  exact (fsj_keep g fr j regs regs' m m' HFS KB Hfst).
Qed.

(* FSb names no register (its regs argument keeps image A's form), so IFS moves to any register file. *)
Lemma ifs_reg : forall g fr j (regs regs' : bvmap 5 word) m,
  getr regs' 9 = getr regs 9 -> IFS g fr j regs m -> IFS g fr j regs' m.
Proof.
  intros g fr j regs regs' m _ H. pose proof H as (_ & _ & _ & _ & _ & Hfst & _).
  exact (ifs_keep g fr j regs regs' m m H (fun X => X) (fun X => X) (fun a bs _ _ X => X) Hfst).
Qed.

(* The turn's two frame records keep their lengths: the identity record 38 bytes (the ingest keeps it,
   RcIdentModel.ING_length) and the fragment record 72 bytes (fg_next keeps it in every class). The proofs of
   lib/B/Prog/Seg/F8.v (f8_t_FG_length / f8_t_ID_length), which the segments of this unit do not import. With them a
   segment shows that a record lies inside the frame body [fr, fr + FRAME_BYTES). *)
Lemma tr_first_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold fg_first, fg_body.
  rewrite !length_app, length_skipn, (rf_bsl_length g 6 6), (rf_bsl_length g 27 (fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma tr_fr_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.

Lemma tr_keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.

Lemma tr_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply tr_first_length; [exact HL | exact HG | apply (tr_fr_fg_n len); exact FR].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply rf_clear_length, rf_fg_join_length;
      solve [exact HL | exact HG | apply (tr_fr_fg_n len); exact FR | apply tr_keep_T; exact KEEP].
Qed.

Lemma tr_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (tr_next_length 1 1 1 1 1); solve [exact IH | unfold t_g; apply fr50_length].
Qed.

Lemma tr_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn.
    assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact IH | exact IH]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; unfold fg_id;
      (match goal with |- context [if ?c then _ else _] => destruct c end;
       [apply RcIdentModel.ING_length; exact Hr | exact Hr]).
Qed.

Lemma tr_IDr_length : forall inp j, length (t_IDr inp j) = 38%nat.
Proof.
  intros inp j. unfold t_IDr, rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply RcIdentModel.ING_length; apply tr_ID_length | apply tr_ID_length].
Qed.

(* A run whose write list W misses the frame body [fr, fr + FRAME_BYTES) keeps both records: they are 38 and 72
   bytes at fr + 2688 and fr + 2768. *)
Lemma frec_munch : forall g fr idb st W (m m' : word -> option byte),
  FREC g fr idb st m -> length idb = 38%nat -> length st = 72%nat -> munch W m m' ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x) -> FREC g fr idb st m'.
Proof.
  intros g fr idb st W m m' H Li Ls MU HO. rewrite FRAME_BYTES_val in HO. apply (frec_keep g fr idb st m m' H).
  - intros Hb. apply (fl_bytes W m m' (fr + 2688) idb Hb MU). rewrite Li. intros x Hx. apply HO. lia.
  - intros Hb. apply (fl_bytes W m m' (fr + 2768) st Hb MU). rewrite Ls. intros x Hx. apply HO. lia.
Qed.

(* ... and the local `first` [fr + 2880, fr + 2920) with it, so IFS; the run's post memory gives `first`'s
   addressability (FLI's RAD, third range). *)
Lemma ifs_munch : forall g fr j (regs regs' : bvmap 5 word) W (m m' : word -> option byte),
  IFS g fr j regs m -> munch W m m' -> (forall x, fr <= x < fr + FRAME_BYTES -> outside W x) ->
  addressable m' (fr + 2880) 40 -> IFS g fr j regs' m'.
Proof.
  intros g fr j regs regs' W m m' H MU HO Hfst. rewrite FRAME_BYTES_val in HO.
  apply (ifs_keep g fr j regs regs' m m' H); [| | | exact Hfst].
  - intros Hb. apply (fl_bytes W m m' (fr + 2688) _ Hb MU). rewrite tr_ID_length. intros x Hx. apply HO. lia.
  - intros Hb. apply (fl_bytes W m m' (fr + 2768) _ Hb MU). rewrite tr_FG_length. intros x Hx. apply HO. lia.
  - intros a bs Ha Hab Hb. apply (fl_bytes W m m' a bs Hb MU). intros x Hx. apply HO. lia.
Qed.

(* FTURN across a run whose write list misses Phi's len bytes. *)
Lemma turn_munch : forall g j phi (regs regs' : bvmap 5 word) W (m m' : word -> option byte),
  FTURN g j phi regs m ->
  (forall off v, 0 <= off <= 336 -> spill regs m off v -> spill regs' m' off v) ->
  munch W m m' -> (forall x, phi <= x < phi + t_len (g_in g) j -> outside W x) -> FTURN g j phi regs' m'.
Proof.
  intros g j phi regs regs' W m m' H K MU HO. pose proof H as (_ & _ & _ & Hlen).
  apply (turn_keep g j phi regs regs' m m' H K).
  intros Hb. apply (fl_bytes W m m' phi _ Hb MU). intros x Hx. apply HO. lia.
Qed.
