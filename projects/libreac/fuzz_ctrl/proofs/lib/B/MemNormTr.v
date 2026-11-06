(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fuzz_ctrl image B, the twin of lib/A/MemNormTr.v (same lemma names, on B's Img0 / AsanRT / MemNorm / ImgBounds;
   no BzBridge, see rsegs_below_img): the caller-side transports of the MemNorm route. A caller holds `ro_agree rsegs m` (each
   read-only byte that m holds equals the rom byte, lib/B/MemNorm.v); a callee contract takes `mem_inv rsegs m`, which
   only `normalize rsegs m` has (MemNorm.mem_inv_normalize). The callee runs on `normalize rsegs m`;
   MemNormF.evtF_normalize_ro moves that run to m, and the run's post comes back to the real memory through
   MemNorm.ms_rel. This file moves the callee's premises forward to `normalize rsegs m` and the post's facts back.

   Forward, with nothing more than ro_agree: asan_cells_normalize and addressable_normalize (both read memory only
   through mrd, which normalize keeps under ro_agree: MemNorm.mrd_rel), and shadow_rw_normalize (every shadow address
   lies above every segment of rsegs, so it is not read-only). bytes_at moves by MemNorm.bytes_at_normalize.
   A WRITABILITY fact (wview <> None: stk, wr_at, rw_cells) does not move in general. RiscvSemantics.wview m a is
   `Some b` whenever `m a = Some b`, also at a read-only address, and normalize drops that byte; see
   stk_normalize_ro_unguarded_false. Such a fact moves when its range is not read-only: stk_normalize_ro takes
   `ImgBounds.IMG_HI <= lo`, stk_normalize_below_img takes `hi <= ImgBounds.IMG_LO`, rw_cells_normalize takes the R8F
   not-read-only premise (ro_addr_above_img_range gives it for a range at or above IMG_HI), wr_at moves by
   MemNorm.wr_at_norm.
   Back, with no extra premise: stk_of_rel, addressable_of_rel, rw_cells_of_rel, asan_cells_of_rel, shadow_rw_of_rel
   (MemNorm has bytes_at_rel, wr_at_rel, munch_rel, wmono_rel, ro_agree_of_mem_rel), and ms_rel_MS (a state that
   ms_rel relates to an MS state is that MS state with its own memory). At the end: the side-stack forms (fp_* and
   the tls forms) for the B callee lanes. rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
Import ListNotations.
Open Scope Z_scope.

(* ---- No address at or above IMG_HI is read-only: every segment of rsegs ends at or below IMG_HI = 0x5fe000 (B's
   lib/B/Prog/ImgBounds.v). seg_ends_below / find_segment_end_below are BzBridge's seg_tops_below /
   find_segment_below, stated here so that this file does not Require lib/B/BzBridge.v: through it the closure of
   every file that Requires MemNormTr reached lib/B/Bz/Lib/{Mem,MState,Step,Cells}.v beside lib/Lib's copies, and
   a Theorem Labs lane's ctrlgate DUP gate then fails each bare use of a lib/Lib name. *)
Definition seg_ends_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma find_segment_end_below : forall segs top x n s,
  seg_ends_below segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_ends_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma rsegs_below_img : seg_ends_below rsegs ImgBounds.IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ro_addr_above_img : forall a, ImgBounds.IMG_HI <= a < 2 ^ 64 -> lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa a) = false.
Proof.
  intros a Ha. unfold lib.Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned (lib.Lib.Mem.wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. rewrite (lib.Lib.Mem.wa_unsigned a ltac:(unfold ImgBounds.IMG_HI in Ha; lia)) in E.
  destruct (find_segment_end_below rsegs ImgBounds.IMG_HI a 1 s rsegs_below_img E ltac:(lia)) as [L|L]; lia.
Qed.

(* The R8F not-read-only premise of the ProgLift lifts, `forall i, 0 <= i < n -> ro_addr rsegs (wa (x + i)) = false`,
   for a range [x, x + n) at or above IMG_HI. AsanRT.app_mem does not give it: app_mem's low branch [0, LOWMEM_END)
   contains the image. *)
Lemma ro_addr_above_img_range : forall x n, ImgBounds.IMG_HI <= x -> x + n <= 2 ^ 64 ->
  forall i, 0 <= i < n -> lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa (x + i)) = false.
Proof. intros x n Hlo Hhi i Hi. apply ro_addr_above_img. lia. Qed.

(* ---- No address below IMG_LO is read-only: every segment of rsegs starts at or above IMG_LO = 0x10000 (B's
   lib/B/Prog/ImgBounds.v). *)
Definition seg_bases_above (segs : list Segment) (lo : Z) : bool :=
  forallb (fun s => lo <=? Z.of_N (seg_base s)) segs.

Lemma rsegs_above_img_lo : seg_bases_above rsegs ImgBounds.IMG_LO = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_above : forall segs lo x n s,
  seg_bases_above segs lo = true -> find_segment segs x n = Some s -> lo <= x.
Proof.
  induction segs as [|s0 r IH]; intros lo x n s Hb H; cbn in H; [discriminate H|].
  unfold seg_bases_above in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [E _]. apply Z.leb_le in E. lia.
  - exact (IH lo x n s Hr H).
Qed.

Lemma ro_addr_below_img : forall a, 0 <= a < ImgBounds.IMG_LO -> lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa a) = false.
Proof.
  intros a Ha. unfold lib.Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned (lib.Lib.Mem.wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. rewrite (lib.Lib.Mem.wa_unsigned a ltac:(unfold ImgBounds.IMG_LO in Ha; lia)) in E.
  pose proof (find_segment_above rsegs ImgBounds.IMG_LO a 1 s rsegs_above_img_lo E). lia.
Qed.

(* ---- Forward: a callee premise on m holds on normalize m. *)
Lemma asan_cells_normalize : forall m, ro_agree rsegs m -> asan_cells m -> asan_cells (normalize rsegs m).
Proof.
  intros m RO H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end.
  all: apply (bytes_at_normalize rsegs m _ _ RO); assumption.
Qed.

Lemma addressable_normalize : forall m p n, ro_agree rsegs m -> addressable m p n ->
  addressable (normalize rsegs m) p n.
Proof.
  intros m p n RO (H0 & H1 & H2 & H). pose proof (mem_rel_normalize rsegs m RO) as REL.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|].
  exists b. split; [|exact Hok]. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ REL). exact Hb.
Qed.

Lemma shadow_rw_normalize : forall m, ro_agree rsegs m -> shadow_rw m -> shadow_rw (normalize rsegs m).
Proof.
  intros m RO H a Ha. pose proof (mem_rel_normalize rsegs m RO) as REL.
  destruct (H a Ha) as [Hv [b Hb]].
  assert (E : lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa a) = false).
  { apply ro_addr_above_img.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
    unfold ImgBounds.IMG_HI. lia. }
  split; [rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ REL E); exact Hv|].
  exists b. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ REL). exact Hb.
Qed.

(* The premise `ImgBounds.IMG_HI <= lo` is not a weakening at any call site of the ProgLift lifts: each caller stack
   window there already carries `HIGHMEM_BEG <= lo`, and HIGHMEM_BEG = 0x10007fff8000 is far above
   IMG_HI = 0x5fe000. Without some such premise the statement is false (stk_normalize_ro_unguarded_false). *)
Lemma stk_normalize_ro : forall m lo hi, ro_agree rsegs m -> ImgBounds.IMG_HI <= lo -> lib.Lib.Frame.stk rsegs m lo hi ->
  lib.Lib.Frame.stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RO Hlo (H0 & H1 & H). pose proof (mem_rel_normalize rsegs m RO) as REL.
  split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  assert (E : lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa a) = false) by (apply ro_addr_above_img; lia).
  split; [rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ REL E); exact Hv|].
  exists b. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ REL). exact Hb.
Qed.

(* The unguarded form is false. Counter-model: m := seg_rom rsegs (the rom itself as memory) agrees with the rom, and
   the one-byte window [0x10000, 0x10001) of the read-only first segment is a stk window of m (wview reads the byte
   that m holds), but normalize drops that byte and the segment is not writable, so wview of the normalized memory
   there is None. Do not restate stk_normalize_ro without a not-read-only premise. *)
Lemma stk_normalize_ro_unguarded_false :
  ~ (forall m lo hi, ro_agree rsegs m -> lib.Lib.Frame.stk rsegs m lo hi -> lib.Lib.Frame.stk rsegs (normalize rsegs m) lo hi).
Proof.
  intros H.
  assert (RO : ro_agree rsegs (lib.Lib.PropExec.seg_rom rsegs)).
  { intros a _. unfold lib.Lib.Mem.mrd. destruct (lib.Lib.PropExec.seg_rom rsegs a); reflexivity. }
  assert (Hb : exists b, lib.Lib.PropExec.seg_rom rsegs (lib.Lib.Mem.wa 0x10000) = Some b).
  { destruct (lib.Lib.PropExec.seg_rom rsegs (lib.Lib.Mem.wa 0x10000)) as [b|] eqn:E; [exists b; reflexivity|].
    vm_compute in E. discriminate E. }
  destruct Hb as [b Hb].
  assert (ST : lib.Lib.Frame.stk rsegs (lib.Lib.PropExec.seg_rom rsegs) 0x10000 0x10001).
  { split; [lia|]. split; [lia|]. intros a Ha. assert (Ea : a = 0x10000) by lia. subst a.
    unfold wview, lib.Lib.Mem.mrd. rewrite Hb. cbv beta iota.
    split; [intros E; discriminate E | exists b; reflexivity]. }
  destruct (H _ _ _ RO ST) as (_ & _ & H2). destruct (H2 0x10000 ltac:(lia)) as [Hv _].
  apply Hv. vm_compute. reflexivity.
Qed.

(* The twin of stk_normalize_ro for a window BELOW the image (the frame / flag byte of a caller whose fake-stack frame
   lies under IMG_LO): no byte there is read-only (ro_addr_below_img). *)
Lemma stk_normalize_below_img : forall (mm : word -> option byte) lo hi, ro_agree rsegs mm ->
  0 <= lo -> hi <= ImgBounds.IMG_LO -> lib.Lib.Frame.stk rsegs mm lo hi -> lib.Lib.Frame.stk rsegs (normalize rsegs mm) lo hi.
Proof.
  intros mm lo hi RO Hlo Hhi (H0 & H1 & H). pose proof (mem_rel_normalize rsegs mm RO) as REL.
  split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  assert (E : lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa a) = false) by (apply ro_addr_below_img; lia).
  split; [rewrite (wview_rel_rw rsegs mm (normalize rsegs mm) _ REL E); exact Hv|].
  exists b. rewrite <- (mrd_rel rsegs mm (normalize rsegs mm) _ REL). exact Hb.
Qed.

Lemma rw_cells_normalize : forall m p cs, ro_agree rsegs m ->
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) -> lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa (p + i)) = false) ->
  lib.Lib.Step.rw_cells rsegs m p cs -> lib.Lib.Step.rw_cells rsegs (normalize rsegs m) p cs.
Proof.
  intros m p cs RO Hn [[Hwf Hb] Hw]. pose proof (mem_rel_normalize rsegs m RO) as REL.
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m p _ RO Hb)]|].
  exact (wr_at_norm rsegs m (normalize rsegs m) p _ REL Hw Hn).
Qed.

(* ---- Back: a fact of the normalized post holds of the real memory that mem_rel relates to it. *)
Lemma stk_of_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> lib.Lib.Frame.stk rsegs m0 lo hi -> lib.Lib.Frame.stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb]]. pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as E.
  split; [rewrite <- (wview_rel_rw rsegs m m0 _ REL E); exact Hv|].
  exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

(* addressable reads memory only through mrd, which mem_rel keeps (MemNorm.mrd_rel): the twin of stk_of_rel. *)
Lemma addressable_of_rel : forall (mm mm0 : word -> option byte) p k, mem_rel rsegs mm mm0 ->
  addressable mm0 p k -> addressable mm p k.
Proof.
  intros mm mm0 p k REL (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|].
  exists b. split; [|exact Hok]. rewrite (mrd_rel rsegs mm mm0 _ REL). exact Hb.
Qed.

Lemma rw_cells_of_rel : forall m m0 p cs, mem_rel rsegs m m0 -> lib.Lib.Step.rw_cells rsegs m0 p cs -> lib.Lib.Step.rw_cells rsegs m p cs.
Proof.
  intros m m0 p cs REL [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m m0 p _ REL) Hb)]|].
  exact (wr_at_rel rsegs m m0 p _ REL Hw).
Qed.

Lemma asan_cells_of_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 REL H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end.
  all: apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

Lemma shadow_rw_of_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL H a Ha. destruct (H a Ha) as [Hv [b Hb]].
  pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as E.
  split; [rewrite <- (wview_rel_rw rsegs m m0 _ REL E); exact Hv|].
  exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma ms_rel_MS : forall s R F pc fc rv m0 ro, ms_rel rsegs s (lib.Lib.MState.MS R F pc fc rv m0 ro) ->
  s = lib.Lib.MState.MS R F pc fc rv (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros s R F pc fc rv m0 ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8). split; [|exact E8].
  destruct s as [x1 x2 x3 x4 x5 x6 x7 x8]. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
Qed.

(* ---- The side-stack premise packs of the asan callees (lib/B/Prog/RcAsanFP.v fp, lib/B/Prog/asan_stack_malloc_c.v
   asan_tls_cells and fs_place) on normalize m, and the tls disjointness every B <fn>_tls premise is. Generic forms for
   the B callee lanes; fp_transport and asan_tls_cells_transport are a Theorem Labs lane's cmRB_fp_tr / cmRB_tls_tr
   (lib/B/Prog/C_reac_box_catalogue_matchLib.v (a version not in this delivery; written on a working branch c48dda1461f)) with
   the proofs copied; cmRB_fs_above_img becomes fp_FS_above_img. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c RcAsanFP.

(* fp's side stack lies above the image: fp's fs_place conjunct carries ASAN_GT <= FS (asan_stack_malloc_c.v:35), and
   ASAN_GT = 0x5fe000 (lib/B/Prog/asan_stack_malloc_c.v:14) = ImgBounds.IMG_HI (lib/B/Prog/ImgBounds.v:9). It is the
   guard stk_normalize_ro needs for fp's side-stack stk. *)
Lemma fp_FS_above_img : forall cs m TP FS lo hi W D, fp cs m TP FS lo hi W D -> ImgBounds.IMG_HI <= FS.
Proof.
  intros cs m TP FS lo hi W D (DT & TS & C & T & DB & k & _ & _ & (_ & _ & HG & _) & _).
  unfold ASAN_GT in HG. unfold ImgBounds.IMG_HI. lia.
Qed.

Lemma asan_tls_cells_transport : forall (m m' : word -> option byte) TP DT TS C T DB k,
  (forall a bs, lib.Lib.Mem.bytes_at rsegs m a bs -> lib.Lib.Mem.bytes_at rsegs m' a bs) ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m' TP DT TS C T DB k.
Proof.
  intros m m' TP DT TS C T DB k E
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19).
  split; [exact (E _ _ H1)|]. split; [exact (E _ _ H2)|]. split; [exact (E _ _ H3)|]. split; [exact (E _ _ H4)|].
  split; [exact (E _ _ H5)|]. split; [exact H6|]. split; [exact (E _ _ H7)|]. split; [exact (E _ _ H8)|].
  split; [exact (E _ _ H9)|]. split; [exact (E _ _ H10)|]. split; [exists tb, te; exact (E _ _ H11)|].
  split; [exact (E _ _ H12)|]. split; [exact (E _ _ H13)|]. split; [exact (E _ _ H14)|].
  split; [exact (E _ _ H15)|]. split; [exact (E _ _ H16)|]. split; [exact (E _ _ H17)|].
  split; [exact H18 | exact (E _ _ H19)].
Qed.

(* fp moves with its bytes and its side-stack stk; the stk move takes the IMG_HI guard, from fp_FS_above_img. *)
Lemma fp_transport : forall (m m' : word -> option byte) cs TP FS lo hi W D,
  (forall a bs, lib.Lib.Mem.bytes_at rsegs m a bs -> lib.Lib.Mem.bytes_at rsegs m' a bs) ->
  (forall lo' hi', ImgBounds.IMG_HI <= lo' -> lib.Lib.Frame.stk rsegs m lo' hi' -> lib.Lib.Frame.stk rsegs m' lo' hi') ->
  fp cs m TP FS lo hi W D -> fp cs m' TP FS lo hi W D.
Proof.
  intros m m' cs TP FS lo hi W D EB ES H.
  pose proof (fp_FS_above_img cs m TP FS lo hi W D H) as HG.
  destruct H as (DT & TS & C & T & DB & k & TL & HTP & (P1 & P2 & P3 & P4 & PS) & H88 & H96 & HC & HLO & HAPP & DJW &
                 DJD).
  exists DT, TS, C, T, DB, k.
  split; [exact (asan_tls_cells_transport m m' TP DT TS C T DB k EB TL)|].
  split; [exact (EB _ _ HTP)|].
  split; [split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4|]; exact (ES _ _ HG PS)|].
  split; [exact (EB _ _ H88)|]. split; [exact (EB _ _ H96)|].
  split; [|split; [exact HLO|]; split; [exact HAPP|]; split; [exact DJW | exact DJD]].
  eapply Forall_impl; [|exact HC]. intros c (Hc & h & flags & Hh & Hf & Hl & Hb).
  split; [exact Hc|]. exists h, flags. split; [exact (EB _ _ Hh)|]. split; [exact (EB _ _ Hf)|].
  split; [exact Hl | exact Hb].
Qed.

Lemma fp_normalize : forall cs m TP FS lo hi W D, MemNorm.ro_agree rsegs m -> fp cs m TP FS lo hi W D ->
  fp cs (MemNorm.normalize rsegs m) TP FS lo hi W D.
Proof.
  intros cs m TP FS lo hi W D RO. apply fp_transport.
  - intros a bs H. exact (bytes_at_normalize rsegs m a bs RO H).
  - intros lo' hi' Hlo H. exact (stk_normalize_ro m lo' hi' RO Hlo H).
Qed.

Lemma asan_tls_cells_normalize : forall m TP DT TS C T DB k, MemNorm.ro_agree rsegs m ->
  (asan_tls_cells (MemNorm.normalize rsegs m) TP DT TS C T DB k <-> asan_tls_cells m TP DT TS C T DB k).
Proof.
  intros m TP DT TS C T DB k RO. pose proof (mem_rel_normalize rsegs m RO) as REL. split.
  - apply asan_tls_cells_transport. intros a bs H. exact (proj2 (bytes_at_rel rsegs _ _ a bs REL) H).
  - apply asan_tls_cells_transport. intros a bs H. exact (proj1 (bytes_at_rel rsegs _ _ a bs REL) H).
Qed.

Lemma tls_pred_normalize : forall (P : word -> word -> word -> word -> word -> Z -> Prop) m TP,
  MemNorm.ro_agree rsegs m ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> P DT TS C T DB k) ->
  forall DT TS C T DB k, asan_tls_cells (MemNorm.normalize rsegs m) TP DT TS C T DB k -> P DT TS C T DB k.
Proof.
  intros P m TP RO H DT TS C T DB k HN.
  exact (H DT TS C T DB k (proj1 (asan_tls_cells_normalize m TP DT TS C T DB k RO) HN)).
Qed.

(* The tls disjointness of a callee: every B <fn>_tls (reac_ctrl_parse_tls, reac_box_model_block_tls, ...) is
   tls_dj m TP (fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)]) up to unfolding. *)
Definition tls_dj (m : word -> option byte) (TP : Z) (X : list lib.Lib.Frame.ivl) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X.

(* No guard: m occurs only in the antecedent, which comes back from normalize m (asan_tls_cells_normalize). *)
Lemma tls_dj_normalize : forall m TP X, MemNorm.ro_agree rsegs m -> tls_dj m TP X ->
  tls_dj (MemNorm.normalize rsegs m) TP X.
Proof.
  intros m TP X RO H. exact (tls_pred_normalize (fun DT TS C T DB k => fp_dj (fp_tls TP DT TS C T DB k) X) m TP RO H).
Qed.
