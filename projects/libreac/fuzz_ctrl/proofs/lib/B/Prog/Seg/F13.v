(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths, module names and numbers changed; 1595 of its 1770 lines of code are new or changed and 2382 lines of the source are left out. *)
(* Segment F13 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B), libreac v1.9.0: 0x82340-0x82358, the
   call of reac_ctrl_identity_fragment (0x859e4) at 0x82358; no trap row, no shadow row.  The frame-loop body
   sets up the six arguments of the call (a0 = s5, a1 = s2, a2 = s4, a3 = [s1+288], a4 = [s1+304],
   a5 = [s1+296]) and calls it; the segment runs from the pre-call cut 0x82340 through the call and lands at the
   return cut 0x8235c (the entry of F14) with a0 = the fragment result.  (v1.8: 0x822d0-0x822e8, a0 = s7,
   a3 = [s1+280]; the code is otherwise the same.)

   The record f = fragb fr = fr + 2768 (s5; spilled at [s1+208], set 0x81508) and the three output cells
   pa = fr + 256 ([s1+288]), pp = fr + 272 ([s1+304]) and pn = fr + 304 ([s1+296]) all lie inside the 3136-byte
   frame body; the record buffer is phi = s2 (the frame loop's heap block Phi) and its length len = s4.  The callee's
   write set is fg_fp K f pa pp pn sp c: those cells plus the callee stack window [sp - K, sp).  Every placement fact
   is read off FRA: fra_frame (the frame apart from the callee window on both arms, fr + 3136 <= s1, the side stack's
   metadata below fr), fra_win (the sp-anchored window), and the frame-location disjunction (the frame in AppMem at
   or above GT).  FRA moves across the call's memory change with fra_mem_call (its write set may cover the callee's
   window below sp, which Tac_slot's sl_fr_run excludes) and across the register change and the page
   materialization with Tac_slot.sl_fra_move; ENT moves with Tac_slot.ent_store / ent_mat.  The runtime cells the
   callee reads come from FRA's runtime invariant (rt_cells).  The three argument spills, the record pointer spill
   [s1+208] and the before-call copy pointer [s1+200] are the frame-loop bundle FLI that LK carries; the sum flag
   s9 is FM's, the spill [s1+248] = 1 - sum_ok is FS9's.

   Push 5c keeps mem_inv out of FRA and out of the cuts: the cut carries ro_agree, and the callee contract, which
   asks for mem_inv, is reached on the normalized memory through MemNorm.evt_normalize (f13_evt below wraps
   f13_evt_n, which is the run against the contract as stated).  The run lifts through AsanLift.evt_SR_canon_lazy
   (sl_run_lib). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.


(* ---- fragment-class helper facts (lengths of the record's post bytes, footprint shape). ---- *)

Lemma rf_first_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold fg_first, fg_body.
  rewrite !length_app, length_skipn, (rf_bsl_length g 6 6), (rf_bsl_length g 27 (fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma fr_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.

Lemma keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.

Lemma fg_case_eq_dec : forall c d : fg_case, {c = d} + {c <> d}.
Proof. decide equality. Qed.

(* The record's post bytes have the same length in every class. *)
Lemma fg_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply rf_first_length; [exact HL | exact HG | apply (fr_fg_n len); exact FR].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply rf_clear_length, rf_fg_join_length;
      solve [exact HL | exact HG | apply (fr_fg_n len); exact FR | apply keep_T; exact KEEP].
Qed.

Lemma t_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

Lemma t_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (fg_next_length 1 1 1 1 1); solve [exact IH | apply t_g_length].
Qed.

(* The declared length of a frame is a two-byte field, so it is far below 2^64. *)
Lemma inb_range : forall inp j, 0 <= inb inp j < 256.
Proof.
  intros inp j. unfold inb, RIM.bz.
  pose proof (bv_unsigned_in_range 8 (RIM.nthb inp (Z.to_nat j))) as H.
  unfold bv_modulus in H. cbn in H. lia.
Qed.

Lemma flen_small : forall inp j, t_len inp j <= 65535.
Proof.
  intros inp j. unfold t_len, f_len.
  pose proof (Z.le_min_l (f_L inp (fc inp j)) (f_left inp (fc inp j) - f_h inp (fc inp j))) as Hm.
  assert (HL : f_L inp (fc inp j) <= 65535).
  { unfold f_L. pose proof (inb_range inp (fc inp j)) as H1.
    pose proof (inb_range inp (fc inp j + 1)) as H2.
    destruct (2 <=? f_left inp (fc inp j)); lia. }
  lia.
Qed.

(* ---- the fragment footprint. ---- *)

Lemma all_app_fp : forall K f pa pp pn S c,
  app_ivl f (f + 72) -> app_ivl pa (pa + 2) -> app_ivl pp (pp + 8) -> app_ivl pn (pn + 8) ->
  app_ivl (S - K) S -> all_app (fg_fp K f pa pp pn S c).
Proof. intros K f pa pp pn S c H1 H2 H3 H4 H5. destruct c; cbn [fg_fp all_app]; tauto. Qed.

(* Every address the callee may write lies in one of the five FgClose intervals. *)
Lemma fp_in : forall K f pa pp pn S c x,
  ~ outside (fg_fp K f pa pp pn S c) x ->
  (f <= x < f + 72) \/ (pa <= x < pa + 2) \/ (pp <= x < pp + 8) \/ (pn <= x < pn + 8) \/ (S - K <= x < S).
Proof. intros K f pa pp pn S c x H. destruct c; cbn [fg_fp outside] in H; tauto. Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn [outside]; intros x; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [right; intros (C & _); lia | left; split; [lia | exact H]].
Qed.

Lemma fp_outside_of : forall K f pa pp pn S c x,
  ((f <= x < f + 72) \/ (pa <= x < pa + 2) \/ (pp <= x < pp + 8) \/ (pn <= x < pn + 8) \/ (S - K <= x < S) ->
     False) ->
  outside (fg_fp K f pa pp pn S c) x.
Proof.
  intros K f pa pp pn S c x H.
  destruct (outside_dec (fg_fp K f pa pp pn S c) x) as [Ho|Ho]; [exact Ho|].
  exfalso. exact (H (fp_in K f pa pp pn S c x Ho)).
Qed.

Lemma ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (HA & HL & H) Hx.
  assert (Hi : (Z.to_nat (x - A) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - A)) Hi) as HH. rewrite Z2Nat.id in HH by lia.
  replace (A + (x - A)) with x in HH by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E; [exists b; exact HH|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* A stack window survives a run with write set W: outside W the bytes are unchanged, inside W the caller shows
   the post memory is readable. *)
Lemma stk_keep : forall W m m' lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HR.
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  split; [apply WM; exact Hv|].
  destruct (outside_dec W a) as [Ho|Ho].
  - exists b. unfold mrd in *. rewrite (MU (wa a)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
  - exact (HR a Ha Ho).
Qed.

(* One spilled 8-byte word of the save area, as the single-cell rw_cells the load tactic consumes. *)
Lemma rwc_of_q64 : forall m a v, q64 m a v -> wr_at rsegs m a 8 -> rw_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v Hq Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hq.
  - cbn [cells_size csize]. exact Hw.
Qed.

(* ---- The record's post bytes (SlotInv's frrec, at the class frcl of this call site's pointers). ---- *)
Lemma frrec_length : forall g j fr phi, length (frrec g j fr phi) = 72%nat.
Proof.
  intros g j fr phi. unfold frrec, frcl.
  apply fg_next_length; [apply t_FG_length | apply t_g_length].
Qed.

(* Every runtime cell lies below AC.GT = 0x5fe000, so a footprint above it is rt_disjoint. *)
Lemma rt_dj_fp : forall K f pa pp pn S c,
  6283264 <= f -> 6283264 <= pa -> 6283264 <= pp -> 6283264 <= pn -> 6283264 <= S - K ->
  rt_disjoint (fg_fp K f pa pp pn S c).
Proof.
  intros K f pa pp pn S c H1 H2 H3 H4 H5.
  unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN.
  destruct c; cbn [fg_fp disjoint_from]; repeat split; first [left; lia | exact I].
Qed.

(* bytes_at sub-range (as lib/B/Prog/Seg/F18.v ba_sub). *)
Lemma ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite firstn_length, skipn_length; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* The runtime cells the fragment call reads (its __asan_memcpy and bcmp-wrapper callees), from the runtime
   invariant RT that FRA carries (as lib/B/Prog/Seg/F18.v bcmp_cells). *)
Lemma rt_cells : forall sp mem md, AsanRTInv.RT sp mem md ->
  asan_cells mem /\ shadow_rw mem /\
  bytes_at rsegs mem REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mem REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mem GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp mem md HRT.
  destruct HRT as (HAC0 & HSW0 & _ & HCF0 & _ & HREAL0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  split; [exact HAC0|]. split; [exact HSW0|].
  split; [apply (real_cell_of mem REAL_BCMP BCMP HREAL0); vm_compute; reflexivity|].
  split; [apply (real_cell_of mem REAL_MEMCMP MEMCMP HREAL0); vm_compute; reflexivity|].
  split; [exact HGOTCF|].
  split.
  { pose proof (ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240
                  ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 14 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  { pose proof (ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240
                  ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 15 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
Qed.

(* ---- Normalized-memory transfer.  Push 5c took mem_inv out of FRA and out of the cuts: a cut carries ro_agree
   alone, and a callee contract that asks for mem_inv is reached through MemNorm.evt_normalize, which runs the
   body on `normalize rsegs m` and carries the run back to m, leaving `mem_rel` and `ro_same` to move the facts
   across.  Above the image there is no read-only byte, and every address this segment stores to is at or above
   AC.GT; the image-A twin of these lemmas is lib/A/Prog/Seg/F18.v (ro_addr_hi .. asan_cells_rel). ---- *)

(* Every loaded segment of this image ends at or below AC.GT (the top of the runtime's own cells). *)
Definition seg_tops_below (sgs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sgs.

Lemma find_segment_below : forall sgs top x n s,
  seg_tops_below sgs top = true -> find_segment sgs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sgs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma segs_below_GT : seg_tops_below rsegs AC.GT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ro_hi : forall a, AC.GT <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha.
  assert (Hu : bv_unsigned (wa a) = a)
    by (rewrite wa_unsigned by (unfold AC.GT in Ha; lia); reflexivity).
  unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso.
  destruct (find_segment_below rsegs AC.GT (bv_unsigned (wa a)) 1 s segs_below_GT E ltac:(lia))
    as [L|L]; [rewrite Hu in L; unfold AC.GT in *; lia | lia].
Qed.

Definition not_ro (A n : Z) : Prop := forall i, 0 <= i < n -> ro_addr rsegs (wa (A + i)) = false.

Lemma not_ro_hi : forall A n, AC.GT <= A -> A + n <= 2 ^ 64 -> not_ro A n.
Proof. intros A n H1 H2 i Hi. apply ro_hi. lia. Qed.

Lemma ba_back : forall m m0 a bs, MN.mem_rel rsegs m m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs.
Proof. intros m m0 a bs R H. exact (proj2 (MN.bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma rwc_norm : forall m a cs, MN.ro_agree rsegs m -> rw_cells rsegs m a cs ->
  not_ro a (Z.of_nat (cells_size cs)) -> rw_cells rsegs (MN.normalize rsegs m) a cs.
Proof.
  intros m a cs HR ((Hwf & Hb) & Hw) Hn. split; [split; [exact Hwf|]|].
  - apply MN.bytes_at_normalize; assumption.
  - eapply MN.wr_at_norm; [apply MN.mem_rel_normalize; exact HR | exact Hw | exact Hn].
Qed.

Lemma wr_norm : forall m a n, MN.ro_agree rsegs m -> wr_at rsegs m a n -> not_ro a n ->
  wr_at rsegs (MN.normalize rsegs m) a n.
Proof.
  intros m a n HR Hw Hn.
  eapply MN.wr_at_norm; [apply MN.mem_rel_normalize; exact HR | exact Hw | exact Hn].
Qed.

Lemma stk_norm : forall m lo hi, MN.ro_agree rsegs m -> stk rsegs m lo hi -> not_ro lo (hi - lo) ->
  stk rsegs (MN.normalize rsegs m) lo hi.
Proof.
  intros m lo hi HR (H1 & H2 & H) Hn.
  pose proof (MN.mem_rel_normalize rsegs m HR) as REL.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  assert (RO : ro_addr rsegs (wa a) = false)
    by (specialize (Hn (a - lo) ltac:(lia)); replace (lo + (a - lo)) with a in Hn by lia; exact Hn).
  split.
  - rewrite (MN.wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (MN.mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma stk_back : forall m m0 lo hi, MN.mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb).
  pose proof (MN.ro_false_of_wview rsegs m m0 (wa a) REL Hv) as RO. split.
  - rewrite <- (MN.wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (MN.mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma addr_rel : forall m m0 p n, MN.mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (MN.mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma shrw_rel : forall m m0, MN.mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha.
  assert (RO : ro_addr rsegs (wa a) = false).
  { apply ro_hi. pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    unfold AC.GT. lia. }
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (MN.wview_rel_rw rsegs m m0 _ HR RO). exact Hw.
  - exists b. rewrite <- (MN.mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma shrw_back : forall m m0, MN.mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha.
  assert (RO : ro_addr rsegs (wa a) = false).
  { apply ro_hi. pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    unfold AC.GT. lia. }
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (MN.wview_rel_rw rsegs m m0 _ HR RO). exact Hw.
  - exists b. rewrite (MN.mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma acells_rel : forall m m0, MN.mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs =>
      exact (proj1 (MN.bytes_at_rel rsegs m m0 a bs R) ltac:(assumption)) end.
Qed.

Lemma acells_back : forall m m0, MN.mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (ba_back m m0 a bs R ltac:(assumption)) end.
Qed.

Lemma fgmem_back : forall m m0 f pa pp pn st g c, MN.mem_rel rsegs m m0 ->
  fg_mem f pa pp pn st g c m0 -> fg_mem f pa pp pn st g c m.
Proof.
  intros m m0 f pa pp pn st g c R H.
  assert (BB : forall a bs, bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs)
    by (intros a bs Hb; exact (ba_back m m0 a bs R Hb)).
  destruct c; cbn [fg_mem] in H |- *; try exact I; try (apply BB; exact H).
  destruct H as (H1 & H2 & H3 & H4).
  split; [apply BB; exact H1|]. split; [apply BB; exact H2|].
  split; [apply BB; exact H3 | apply BB; exact H4].
Qed.

(* ---- Spills of the 448-byte save area across a run that keeps s1 and misses the area. ---- *)

(* Two readings of s1 that both lie below 2 ^ 64 are the same spill base. *)
Lemma rg9_eq : forall (regs : bvmap 5 word) (A A' : Z),
  rg regs 9 A -> rg regs 9 A' -> 0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A' = A.
Proof.
  intros regs A A' H H' HA HA'. pose proof (rg_eq64 regs 9 A' A H' H) as Hm.
  rewrite !Z.mod_small in Hm by lia. exact Hm.
Qed.

(* A spill names its own base; it is s1, so the word sits at A + off. *)
Lemma spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) (A off v : Z),
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

Lemma spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z)) (A off v : Z),
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 448 ->
  getr regs' 9 = getr regs 9 -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v Hs H9 HA0 HA1 Ho0 Ho1 E9 MU Hout.
  pose proof (spill_at regs m A off v Hs H9 HA0 HA1 Ho0 Ho1) as Hq.
  exists A. split; [unfold rg in *; exact (eq_trans E9 H9)|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8. exact Hout.
Qed.

(* FLI across a run that keeps s1 and s11 and misses the save area: the spills by spill_keep, our[]'s six
   addressable bytes and RAD's three records by sl_addr_keep (the write set is app memory), the frame body's stk
   by stk_keep (a frame byte the run writes is readable afterwards), KNT (image bytes below GT) by fl_bytes. *)
Lemma fli_keep : forall g fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z)) (A : Z),
  FLI g fr regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  munch W m m' -> wmono rsegs m m' -> all_app W -> (forall x, A <= x < A + 448 -> outside W x) ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  FLI g fr regs' m'.
Proof.
  intros g fr regs regs' m m' W A HFLI H9 HA0 HA1 E9 E27 MU WM HAW Hout Hlow Hrd.
  assert (K : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    eapply spill_keep;
      [exact Hs | exact H9 | exact HA0 | exact HA1 | exact Ho0 | exact Ho1 | exact E9 | exact MU |].
    intros x Hx. apply Hout. lia. }
  destruct HFLI as (H27 & S168 & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 &
    S192 & S200 & S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & Had & Hstk &
    (Hrad1 & Hrad2 & Hrad3) & (Hknt1 & Hknt2) & S168b & S88).
  split; [unfold rg in *; exact (eq_trans E27 H27)|].
  split; [apply K; [lia | lia | exact S168]|].
  split; [apply K; [lia | lia | exact S96]|].
  split; [apply K; [lia | lia | exact S112]|].
  split; [apply K; [lia | lia | exact S120]|].
  split; [apply K; [lia | lia | exact S128]|].
  split; [apply K; [lia | lia | exact S136]|].
  split; [apply K; [lia | lia | exact S144]|].
  split; [apply K; [lia | lia | exact S152]|].
  split; [apply K; [lia | lia | exact S280]|].
  split; [apply K; [lia | lia | exact S160]|].
  split; [apply K; [lia | lia | exact S176]|].
  split; [apply K; [lia | lia | exact S192]|].
  split; [apply K; [lia | lia | exact S200]|].
  split; [apply K; [lia | lia | exact S216]|].
  split; [apply K; [lia | lia | exact S208]|].
  split; [apply K; [lia | lia | exact S104]|].
  split; [apply K; [lia | lia | exact S256]|].
  split; [apply K; [lia | lia | exact S264]|].
  split; [apply K; [lia | lia | exact S288]|].
  split; [apply K; [lia | lia | exact S296]|].
  split; [apply K; [lia | lia | exact S304]|].
  split; [exact (Tac_slot.sl_addr_keep m m' W (fr + 2624) 6 Had MU HAW)|].
  split; [exact (stk_keep W m m' fr (fr + FRAME_BYTES) Hstk MU WM Hrd)|].
  (* RAD: the three frame records stay marked usable (the write set is app memory) *)
  split; [split; [exact (Tac_slot.sl_addr_keep m m' W (fr + 2688) 38 Hrad1 MU HAW)|
                  split; [exact (Tac_slot.sl_addr_keep m m' W (fragb fr) 72 Hrad2 MU HAW)
                         | exact (Tac_slot.sl_addr_keep m m' W (fr + 2880) 40 Hrad3 MU HAW)]]|].
  (* KNT: the kind-name table is image memory below GT, which the write set misses *)
  split.
  { split.
    - assert (HKL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
      eapply fl_bytes; [exact Hknt1 | exact MU |].
      rewrite HKL. intros x Hx. apply Hlow. unfold KNC.KIND_NAME, AC.GT in *. lia.
    - exact (Tac_slot.sl_addr_keep m m' W KNC.KIND_NAME 112 Hknt2 MU HAW). }
  split; [apply K; [lia | lia | exact S168b] | apply K; [lia | lia | exact S88]].
Qed.

Lemma lk_keep : forall g fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z)) (A : Z),
  LK g fr j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  munch W m m' -> wmono rsegs m m' -> all_app W -> (forall x, A <= x < A + 448 -> outside W x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> outside W x) ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  LK g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W A (Hj & H240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 MU WM HAW Hout Hour Hlow Hrd.
  split; [exact Hj|].
  split.
  { eapply spill_keep; [exact H240 | exact H9 | exact HA0 | exact HA1 | lia | lia | exact E9 | exact MU |].
    intros x Hx. apply Hout. lia. }
  split.
  { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
    rewrite OUR_length. intros x Hx. apply Hour. lia. }
  eapply fli_keep; [exact HFLI | exact H9 | exact HA0 | exact HA1 | exact E9 | exact E27 | exact MU | exact WM
                    | exact HAW | exact Hout | exact Hlow | exact Hrd].
Qed.

(* FM (v1.9.0): the fill flag [A+184], k = s8, s6 = 1, the sum flag s9 and the block [A+312]. *)
Lemma fm_keep : forall g j phi fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z))
    (A : Z),
  FM g j phi fr regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 ->
  munch W m m' -> (forall x, A <= x < A + 448 -> outside W x) -> FM g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W A (S184 & H24 & H22 & H25 & S312) H9 HA0 HA1 E9 E22 E24 E25 MU Hout.
  split.
  { eapply spill_keep; [exact S184 | exact H9 | exact HA0 | exact HA1 | lia | lia | exact E9 | exact MU |].
    intros x Hx. apply Hout. lia. }
  split; [unfold rg in *; exact (eq_trans E24 H24)|].
  split; [unfold rg in *; exact (eq_trans E22 H22)|].
  split; [unfold rg in *; exact (eq_trans E25 H25)|].
  eapply spill_keep; [exact S312 | exact H9 | exact HA0 | exact HA1 | lia | lia | exact E9 | exact MU |].
  intros x Hx. apply Hout. lia.
Qed.

(* FS9 (v1.9.0): the spill [A+248] = 1 - sum_ok. *)
Lemma fs9_keep : forall g j (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z)) (A : Z),
  FS9 g j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W m m' -> (forall x, A <= x < A + 448 -> outside W x) ->
  FS9 g j regs' m'.
Proof.
  intros g j regs regs' m m' W A S248 H9 HA0 HA1 E9 MU Hout. unfold FS9 in *.
  eapply spill_keep; [exact S248 | exact H9 | exact HA0 | exact HA1 | lia | lia | exact E9 | exact MU |].
  intros x Hx. apply Hout. lia.
Qed.

(* The body of the first-fragment state is at most 23 bytes (frame bytes 27 .. 50). *)
Lemma fst_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn, t_g_length. lia.
Qed.

(* FSj (v1.9.0): the local `first` at fr + 2880 (have, n, the body from fr + 2885, its 40 usable bytes) and FI,
   across a write set of app memory that misses [fr + 2880, fr + 2920). *)
Lemma fsj_keep : forall g fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z)),
  FSj g fr j regs m -> munch W m m' -> all_app W ->
  (forall x, fr + 2880 <= x < fr + 2920 -> outside W x) ->
  FSj g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W (Hhave & Hn & Hbody & Had & HFI) MU HAW Hout.
  pose proof (fst_body_len (g_in g) j) as HBL.
  split; [unfold u32 in *; eapply fl_bytes; [exact Hhave | exact MU |];
          rewrite length_le4; intros x Hx; apply Hout; lia|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hn | exact MU |]; cbn [length]; intros x Hx; apply Hout; lia|].
  split; [eapply fl_bytes; [exact Hbody | exact MU |]; intros x Hx; apply Hout; lia|].
  split; [exact (Tac_slot.sl_addr_keep m m' W (fr + 2880) 40 Had MU HAW) | exact HFI].
Qed.

(* Fold the engine-form stack pointer `bv_unsigned (reg_get regs 2)` (from Regs6ss.mkR_of) back to AC.aspZ regs. *)
Ltac fold_sp regs :=
  match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) end.

(* ===== The byte-range and fragment-model facts the exit bundles RECF / FRBA / FRX read (adopt 6 / 7). The
   fragment model is image-independent: the same copies are in Seg/F15.v and Seg/F16.v. ===== *)

Lemma ba_nth_err_firstn : forall (n i : nat) (l : list byte), (i < n)%nat ->
  nth_error (firstn n l) i = nth_error l i.
Proof.
  induction n as [|n IH]; intros [|i] [|a l] H; cbn; try lia; try reflexivity.
  apply IH. lia.
Qed.
Lemma ba_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H2). split; [exact H0|].
  split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite ba_nth_err_firstn by lia. apply H2. lia.
Qed.
Lemma ba_skipn : forall m a bs (k : nat), (k <= length bs)%nat ->
  bytes_at rsegs m a bs -> bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k Hk HB. rewrite <- (firstn_skipn k bs) in HB.
  apply bytes_at_app in HB. destruct HB as (_ & HB).
  rewrite length_firstn, Nat.min_l in HB by exact Hk. exact HB.
Qed.
Lemma ba_b8 : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i -> (Z.to_nat i < length bs)%nat ->
  b8 m (a + i) (bat bs i).
Proof.
  intros m a bs i (H0 & H1 & H2) Hi0 Hi.
  unfold b8, bytes_at. cbn [length].
  split; [lia|]. split; [lia|].
  intros i' Hi'. destruct i' as [|i']; [|cbn in Hi'; lia]. cbn [nth_error].
  change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_r.
  unfold bat. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
  pose proof (H2 (Z.to_nat i) Hi) as HH. rewrite Z2Nat.id in HH by lia. rewrite HH.
  apply nth_error_nth'. exact Hi.
Qed.
Lemma ba_det : forall m a bs cs, bytes_at rsegs m a bs -> bytes_at rsegs m a cs ->
  length bs = length cs -> bs = cs.
Proof.
  intros m a bs cs (_ & _ & Hb) (_ & _ & Hc) HL.
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (Hb i Hi), <- (Hc i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi), (proj2 (nth_error_None cs i) ltac:(lia)). reflexivity.
Qed.
(* Two words read at one address are the same value (the spill base pins the cut's L / L2 to FLI's). *)
Lemma q64_det : forall m a v1 v2, q64 m a v1 -> q64 m a v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 Hb1 Hb2.
  assert (E : le8 (Z_to_bv 64 v1) = le8 (Z_to_bv 64 v2))
    by (apply (ba_det m a); [exact H1 | exact H2 | rewrite !length_le8; reflexivity]).
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.
Lemma bat_nonneg : forall bs i, 0 <= bat bs i.
Proof. intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. Qed.
Lemma bat_lt : forall bs i, bat bs i < 256.
Proof.
  intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

(* The class of the call at this site, and what a closing turn tells about the record. *)
Lemma ret1_close : forall c, fg_ret c = 1 -> c = FgClose.
Proof. intros c H. destruct c; cbn [fg_ret] in H; try discriminate; reflexivity. Qed.
Lemma frcl_fcls : forall g j fr phi, fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  frcl g j fr phi = fcls (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j).
Proof.
  intros g j fr phi H1 H2 H3 H4 H5. unfold frcl, fcls.
  rewrite (rf_class_nn (fragb fr) phi (fr + 256) (fr + 272) (fr + 304)) by assumption.
  rewrite (rf_class_nn 1 1 1 1 1) by lia. reflexivity.
Qed.
Lemma trf_of_frcl : forall g j fr phi, fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  t_rf (g_in g) j = fg_ret (frcl g j fr phi).
Proof.
  intros g j fr phi H1 H2 H3 H4 H5. unfold t_rf, fg_rf.
  rewrite (frcl_fcls g j fr phi) by assumption. unfold flen. reflexivity.
Qed.
Lemma trf1_cls : forall inp j, t_rf inp j = 1 -> fcls (t_len inp j) (t_FG inp j) (t_g inp j) = FgClose.
Proof. intros inp j H. unfold t_rf, fg_rf in H. apply ret1_close. exact H. Qed.
Lemma cls_close_inv : forall len st g,
  fcls len st g = FgClose -> fg_fr len g = true /\ fg_keep st g = true /\ fg_close st g = true /\ bat g 19 <> 1.
Proof.
  intros len st g H. unfold fcls, fg_class in H.
  destruct (negb (fg_fr len g)) eqn:Efr; [cbn in H; discriminate|].
  destruct (bat g 19 =? 1) eqn:E19; [cbn in H; discriminate|].
  destruct (negb (fg_keep st g)) eqn:Ek; [cbn in H; discriminate|].
  destruct (negb (fg_close st g)) eqn:Ec; [cbn in H; discriminate|].
  apply Bool.negb_false_iff in Efr, Ek, Ec. apply Z.eqb_neq in E19. repeat split; try assumption.
Qed.
Lemma keep_hf : forall st g, fg_keep st g = true -> fg_hf st <> 0.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H. destruct H as ((H & _) & _).
  apply Bool.negb_true_iff, Z.eqb_neq in H. exact H.
Qed.
Lemma fi_nb : forall st s, FI st s -> bat st 6 = 1 -> fs_have s = 1 /\ fs_n s = bat st 7.
Proof. intros st s H H6. destruct (H H6) as (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
Lemma tFGf_close : forall inp j, t_rf inp j = 1 ->
  t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j)).
Proof. intros inp j H. unfold t_FGf, fg_st. rewrite (trf1_cls inp j H). reflexivity. Qed.
Lemma t_FGf_length : forall inp j, length (t_FGf inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FGf, fg_st, fcls.
  apply (fg_next_length 1 1 1 1 1); [apply t_FG_length | apply t_g_length].
Qed.

(* self-contained nth helpers, for the record's bytes 17 / 18 *)
Lemma nthfn : forall (i n : nat) (l : list byte), (i < n)%nat ->
  nth i (firstn n l) (Z_to_bv 8 0) = nth i l (Z_to_bv 8 0).
Proof.
  intros i n l. revert i l. induction n as [|n IH]; intros i l Hi; [lia|].
  destruct l as [|a l]; cbn [firstn]; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [nth]; [reflexivity|]. apply IH. lia.
Qed.
Lemma nth_sk : forall (m i : nat) (l : list byte), nth i (skipn m l) (Z_to_bv 8 0) = nth (m + i) l (Z_to_bv 8 0).
Proof.
  induction m as [|m IH]; intros i l.
  - reflexivity.
  - destruct l as [|a l].
    + cbn [skipn]. rewrite !nth_overflow by (cbn; lia). reflexivity.
    + cbn [skipn plus nth]. apply IH.
Qed.
Lemma nth_clear_hi : forall (j : nat) (st : list byte), (7 <= j)%nat -> (6 <= length st)%nat ->
  nth j (fg_clear st) (Z_to_bv 8 0) = nth j st (Z_to_bv 8 0).
Proof.
  intros j st Hj HL. unfold fg_clear.
  rewrite app_nth2; rewrite length_firstn; [|rewrite Nat.min_l by lia; lia].
  rewrite Nat.min_l by lia.
  rewrite app_nth2; cbn [length]; [|lia].
  rewrite nth_sk. f_equal. lia.
Qed.
Lemma bat_clear_hi : forall st i, 7 <= i -> (6 <= length st)%nat -> bat (fg_clear st) i = bat st i.
Proof. intros st i Hi HL. unfold bat. f_equal. apply nth_clear_hi; [lia | exact HL]. Qed.
Lemma bat_join_lo : forall st g i, 0 <= i -> i < 8 + fg_lf st -> (Z.to_nat i < length st)%nat ->
  bat (fg_join st g) i = bat st i.
Proof.
  intros st g i H0 Hlf HL. unfold bat, fg_join.
  assert (Hlen : (Z.to_nat i < length (firstn (Z.to_nat (8 + fg_lf st)) st))%nat).
  { rewrite length_firstn. apply Nat.min_glb_lt; [|exact HL]. apply Z2Nat.inj_lt; lia. }
  rewrite app_nth1 by exact Hlen. rewrite nthfn; [reflexivity| apply Z2Nat.inj_lt; lia].
Qed.
(* The joined record's bytes past the FIRST part are the LAST frame's body bytes from frame byte 27. *)
Lemma bat_join_mid : forall st g i, 8 + fg_lf st <= i -> i < 8 + fg_T st g ->
  0 <= fg_lf st -> (Z.to_nat (8 + fg_lf st) <= length st)%nat -> 27 + fg_n g <= Z.of_nat (length g) ->
  bat (fg_join st g) i = bat g (27 + (i - 8 - fg_lf st)).
Proof.
  intros st g i H1 H2 H0 HL HG. unfold fg_T in H2. unfold bat, fg_join, fg_body, bsl. f_equal.
  rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn, Nat.min_l by exact HL.
  rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia).
  rewrite nthfn by lia. rewrite nth_sk. f_equal. lia.
Qed.
(* A byte of a slice firstn n (skipn k l) is the list's byte k + i. *)
Lemma bat_firstn_skipn : forall (l : list byte) n (k : nat) i, 0 <= i -> i < n ->
  bat (firstn (Z.to_nat n) (skipn k l)) i = bat l (Z.of_nat k + i).
Proof. intros l n k i H0 H1. unfold bat. f_equal. rewrite nthfn by lia. rewrite nth_sk. f_equal. lia. Qed.
(* On a closing turn (fg_T >= 14) the record's address bytes 17 / 18 are joined_byte 9 / 10 of the FIRST state
   that FI names (fuzz_ctrl.c v1.9.0:251-254 against RcFrag.fg_join). *)
Lemma joined_close : forall st g s, length st = 72%nat -> length g = 50%nat -> frag_ok st -> FI st s ->
  bat st 6 = 1 -> 1 <= fg_n g <= 22 -> 14 <= fg_T st g ->
  bat (fg_join st g) 17 = joined_byte s g 9 /\ bat (fg_join st g) 18 = joined_byte s g 10.
Proof.
  intros st g s HL HG (_ & Hok) HFI H6 Hn HT.
  destruct (HFI H6) as (_ & En & Eb). pose proof (Hok H6) as Hlf.
  assert (K : forall i, 9 <= i <= 10 -> bat (fg_join st g) (8 + i) = joined_byte s g i).
  { intros i Hi. unfold joined_byte. rewrite En, Eb.
    destruct (Z.ltb_spec i (bat st 7)) as [Hlt|Hge].
    - rewrite bat_join_lo by (unfold fg_lf; rewrite ?HL; lia).
      rewrite (bat_firstn_skipn st (bat st 7) 8 i) by lia. reflexivity.
    - rewrite bat_join_mid by (unfold fg_T, fg_lf in *; rewrite ?HL, ?HG; lia).
      unfold fg_lf. f_equal. lia. }
  split; [exact (K 9 ltac:(lia)) | exact (K 10 ltac:(lia))].
Qed.
Lemma f13_split16 : forall v, 0 <= v < 65536 ->
  v mod 256 + 256 * (v / 256) = v /\ 0 <= v mod 256 < 256 /\ 0 <= v / 256 < 256.
Proof.
  intros v Hv. pose proof (Z.div_mod v 256 ltac:(lia)). pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  split; [lia|]. split; [lia|].
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma f13_hi_lo : forall hi lo, 0 <= hi < 256 -> 0 <= lo < 256 ->
  (256 * hi + lo) / 256 = hi /\ (256 * hi + lo) mod 256 = lo.
Proof.
  intros hi lo Hhi Hlo. split.
  - rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.mul_comm, Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma fst_bounds : forall inp j,
  (fs_have (fst_at inp j) = 0 \/ fs_have (fst_at inp j) = 1) /\ 0 <= fs_n (fst_at inp j) < 256.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_have fs_n]. lia.
  - rewrite fst_at_S. unfold turn. cbv zeta.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_have fs_n].
    + pose proof (bat_nonneg (t_g inp j) 26). pose proof (bat_lt (t_g inp j) 26). lia.
    + exact IH.
Qed.

(* ---- The turn's records as the model keeps them (the exit's RECF bundle). ---- *)
Lemma t_FG_S : forall inp j, t_FG inp (S j) = t_FGf inp j.
Proof.
  intros inp j. unfold t_FG, t_FGf. rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.
Lemma t_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold t_ID in *. rewrite fst_at_S. unfold turn. cbv zeta.
  assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
  { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply RIM.ING_length; exact IH | exact IH]. }
  assert (Hf : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                         (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat).
  { unfold fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply RIM.ING_length; exact Hr | exact Hr]. }
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; exact Hf.
Qed.
Lemma t_IDr_length : forall inp j, length (t_IDr inp j) = 38%nat.
Proof.
  intros inp j. unfold t_IDr, rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply RIM.ING_length; apply t_ID_length | apply t_ID_length].
Qed.

(* frag_ok holds of every turn's record: the zero record has flag 0; each writing class keeps the invariant. *)
Lemma bat_clear6 : forall x, (6 <= length x)%nat -> bat (fg_clear x) 6 = 0.
Proof.
  intros x Hx. unfold bat, fg_clear. change (Z.to_nat 6) with 6%nat.
  rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (6 - Init.Nat.min 6 (length x))%nat with 0%nat by lia.
  cbn [app nth]. reflexivity.
Qed.
Lemma fok_clear : forall x, (6 <= length x)%nat -> frag_ok (fg_clear x).
Proof.
  intros x Hx. split; [left; apply bat_clear6; exact Hx|].
  rewrite (bat_clear6 x Hx). intros H. discriminate H.
Qed.
Lemma fok_first : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  frag_ok (fg_first st g).
Proof.
  intros st g HL HG Hn.
  assert (HB : length (bsl g 6 6) = 6%nat) by (rewrite (rf_bsl_length g 6 6) by lia; reflexivity).
  assert (E6 : bat (fg_first st g) 6 = 1).
  { unfold bat, fg_first. change (Z.to_nat 6) with 6%nat.
    rewrite app_nth2 by lia. rewrite HB.
    replace (6 - 6)%nat with 0%nat by lia. cbn [app nth]. reflexivity. }
  assert (E7 : bat (fg_first st g) 7 = fg_n g).
  { unfold bat, fg_first, fg_n. change (Z.to_nat 7) with 7%nat.
    rewrite app_nth2 by lia. rewrite HB.
    replace (7 - 6)%nat with 1%nat by lia. cbn [app nth]. change (Z.to_nat 26) with 26%nat. reflexivity. }
  split; [right; exact E6|]. rewrite E7. intros _. exact Hn.
Qed.
Lemma fok_next : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat -> frag_ok st ->
  frag_ok (fg_next st g (fg_class f fr pa pp pn len st g)).
Proof.
  intros f fr pa pp pn len st g HL HG Hok. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact Hok|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact Hok].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply fok_first; [exact HL | exact HG | exact (fr_fg_n len g FR)].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply fok_clear; lia].
    destruct (fg_close st g); cbn [negb fg_next]; apply fok_clear;
      rewrite (rf_fg_join_length st g HL HG (fr_fg_n len g FR) (keep_T st g KEEP)); lia.
Qed.
Lemma fok_FG : forall inp j, frag_ok (t_FG inp j).
Proof.
  intros inp j. induction j as [|j IH].
  - assert (E : bat (t_FG inp 0) 6 = 0) by reflexivity.
    split; [left; exact E|]. rewrite E. intros H. discriminate H.
  - rewrite t_FG_S. unfold t_FGf, fg_st, fcls.
    apply (fok_next 1 1 1 1 1); [apply t_FG_length | apply t_g_length | exact IH].
Qed.
(* The record invariant across a write set that misses Phi, the spills [A+288, A+320), the record pointer's
   halfword and the shadow map (the copy of Seg/F16.v's f16_rec_inv_keep). *)
Lemma bsl_len_le : forall bs k n, (length (bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold bsl. rewrite length_firstn. apply Nat.le_min_l. Qed.
Lemma rec_inv_keep : forall g j phi A kp m m' W,
  rec_inv g j phi A kp m -> munch W m m' ->
  (forall x, phi <= x < phi + 50 -> outside W x) ->
  (forall x, A + 248 <= x < A + 320 -> outside W x) ->
  (forall x, in_shadow x -> outside W x) ->
  (forall x, kp + 20 <= x < kp + 22 -> outside W x) ->
  rec_inv g j phi A kp m'.
Proof.
  intros g j phi A kp m m' W (Hp0 & Hp50 & Hfl & Htk & Hpap & H312 & H18 & H34 &
     field16 & v14 & v15 & v16 & v17 & H248 & Hf16 & Hkpub & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2)
    MU OWphi OWspill OWsh OWkp.
  assert (SH : forall t, 14 <= t <= 17 -> outside W (Z.shiftr (phi + t) 3 + ASAN_K)).
  { intros t Ht. apply OWsh.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (shadow_of_app (phi + t) (Hpap (phi + t) ltac:(lia))) as His.
    unfold shadow_addr, ASAN_K in *. exact His. }
  unfold rec_inv.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [unfold q64 in *; eapply fl_bytes; [exact H312 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [eapply fl_bytes; [exact H18 | exact MU | intros x Hx; apply OWphi; unfold t_blk in Hx;
            pose proof (bsl_len_le (t_g (g_in g) j) 18 32) as BL; change (Z.to_nat 32) with 32%nat in BL; lia]|].
  split; [eapply fl_bytes; [exact H34 | exact MU | intros x Hx; apply OWphi;
            pose proof (bsl_len_le (t_g (g_in g) j) 34 6) as BL; change (Z.to_nat 6) with 6%nat in BL; lia]|].
  exists field16, v14, v15, v16, v17.
  split; [unfold q64 in *; eapply fl_bytes; [exact H248 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [unfold u16 in *; eapply fl_bytes; [exact Hf16 | exact MU | rewrite length_le2; intros x Hx; apply OWkp; lia]|].
  split; [exact Hkpub|]. split; [exact Hkp0|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb14 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb15 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb16 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb17 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs14 | exact MU | cbn [length]; intros x Hx;
            replace x with (Z.shiftr (phi + 14) 3 + ASAN_K) by lia; apply (SH 14); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs15 | exact MU | cbn [length]; intros x Hx;
            replace x with (Z.shiftr (phi + 15) 3 + ASAN_K) by lia; apply (SH 15); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs16 | exact MU | cbn [length]; intros x Hx;
            replace x with (Z.shiftr (phi + 16) 3 + ASAN_K) by lia; apply (SH 16); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs17 | exact MU | cbn [length]; intros x Hx;
            replace x with (Z.shiftr (phi + 17) 3 + ASAN_K) by lia; apply (SH 17); lia]|].
  split; [exact Heq1|]. exact Heq2.
Qed.


Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract (lib/B/Prog/reac_ctrl_identity_fragment_c.v), taken as a Section Hypothesis. *)
Hypothesis HFRAG : reac_ctrl_identity_fragment_contract.

(* The allocator laws are read once per law in this file, in the three lemmas below (a Theorem Labs lane 15:32Z); every other
   site reads these lemmas. The block law goes through SlotInv's named fields (lw_blocks, lwb_end,
   lwb_byte_not_fs). *)
Lemma f13_blk : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  pose proof (lw_blocks (APIf rc) H mem md p n HAH Hin) as HB.
  split; [exact (lwb_end _ _ _ _ _ _ HB) | exact (lwb_byte_not_fs (APIf rc) H mem md p n HB)].
Qed.

Lemma f13_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hw.
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hw)
    as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma f13_fs_place : forall H mem md b,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) b ->
  0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hb.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md b HAH Hw Hb)
    as (H1 & H2 & _ & H4).
  split; [exact H1|]. split; [exact H2 | exact H4].
Qed.

(* ---- The Lib-level run lemma: the ONE place of this file that uses the lazy-model lemma
   AsanLift.evt_SR_canon_lazy.  It is used once, by seg_F13, for the run from the F13 entry cut through the call of
   reac_ctrl_identity_fragment to the F14 entry cut (f13_evt).  That run reads the spills [s1+280, s1+288) and
   [s1+296, s1+312) of the entry function's save area; the call reads the record buffer [phi, phi + 50), the record
   [fr + 2768, fr + 2840), the runtime cells REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254 / CF + 255 (their v1.9 values
   are the constants of the callee _c.v files, not written here), the runtime's own cells (asan_cells) and the shadow
   bytes (a >> 3) + 0x7fff8000 of the ranges its checks cover; it writes only its footprint fg_fp: [fr + 2768, fr + 2840),
   [fr + 256, fr + 258), [fr + 272, fr + 280), [fr + 304, fr + 312) and its own stack window [sp - 4672, sp). *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF' & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF', Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* FRA transports across a callee run's memory change (mem -> mem'), at a fixed md and fixed registers: the run
   writes only W, and W misses the frame header [fr, fr + 24), the whole 448-byte save area [A, A + 448) (which
   holds the frame spill s1+336, the selector s1+48 and the fr reload s1+40), the saved registers [S - 104, S),
   the 392 frame shadow bytes and the whole low image [0, AC.GT) (so the sink words, the RELRO bytes and the
   thread pointer survive).  Unlike Tac_slot's sl_fr_run, W may also cover the callee's own stack window below sp,
   which on the real arm lies below the frame.  RT survives by RT_store; the heap invariant, the stklo equality,
   the entry-anchored stack window and ro_agree come from the caller.  The side arm's FakeStack frame record
   FSREC moves by Tac_slot.fsrec_munch_lo: W writes nothing below stklo outside the frame body [fr + 24, fr + 3136)
   (the callee window lies above stklo by fra_win). *)
Lemma fra_mem_call : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  all_app W -> rt_disjoint W -> MN.ro_agree rsegs mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall A, 0 <= A < 2 ^ 64 -> getr regs 9 = Z_to_bv 64 A ->
     forall x, A <= x < A + 448 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + 392 -> outside W x) ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md -> ~ (fr + 24 <= x < fr + 3136) ->
     outside W x) ->
  FRA B APIf ra g fr hb regs mem' md.
Proof.
  intros g fr hb regs mem mem' md W HFRA MU WM HAW HD HRO' HAH' HSTK HWIN'
    HWhdr HWsave HWsaved HWshadow HWlow HWfs.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (Hsave : forall x, A <= x < A + 448 -> outside W x) by (apply HWsave; [exact HA64 | exact Hr9]).
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold AC.GT in *; lia).
      apply HWlow. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md W HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO'|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [exact Hr2|].
  split; [exact Hspm|].
  split; [exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [exact Hr4|].
  split; [exact Hr8|].
  split; [exact Hr9|].
  split; [exact Hr3|].
  split; [exact Hr19|].
  split; [exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply Hsave. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply Hsave. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. apply Hsave. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [|exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * eapply Tac_slot.fsrec_munch_lo with (W := W); [exact Hrec | exact HAH | exact MU | exact HWfs]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen, FRAME_SHADOW_val.
    intros x Hx. exact (HWshadow x ltac:(lia)). }
  split; [exact HWIN'|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (Tac_slot.sl_addr_keep mem mem' W a 1 (HAG a Hin) MU HAW)|].
  split; [intros a Ha Hb; exact (Tac_slot.sl_addr_keep mem mem' W a 1 (HWA a Ha Hb) MU HAW)|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* the input block: below stklo and apart from the frame (fra_in_apart), so outside W by HWfs *)
  apply (Tac_slot.fra_in_keep g mem mem' W Hinb Hinblk MU HAW).
  intros x Hx. destruct (Hinap x Hx) as (_ & Hxlo & Hxf & _). unfold FRAME_BYTES in Hxf.
  apply HWfs; [exact Hxlo | lia].
Qed.

(* ---- The run 0x82340 -> 0x82358 (the call) -> 0x8235c, against the callee contract as stated (mem_inv): three
   register moves (a0 = s5, a1 = s2, a2 = s4), three spill loads (a3 = [s1+288], a4 = [s1+304], a5 = [s1+296])
   and the jal; the contract's post lands at the return pc with a0 = fg_ret of the class and every other
   callee-saved register unchanged. ---- *)
Lemma f13_evt_n :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    s1v = Z_to_bv 64 A -> s5 = Z_to_bv 64 f -> s2v = Z_to_bv 64 frg -> s4v = Z_to_bv 64 len ->
    0 <= f < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    rw_cells rsegs m (A + 288) [C8 (Z_to_bv 64 pa)] ->
    rw_cells rsegs m (A + 296) [C8 (Z_to_bv 64 pn)] ->
    rw_cells rsegs m (A + 304) [C8 (Z_to_bv 64 pp)] ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length gfrag = 50%nat -> length st = 72%nat ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m frg gfrag) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1v
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8235c) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82340) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag -> -> -> -> Hfb Hfrgb Hlenb Hpab Hppb Hpnb
    Hc280 Hc296 Hc304 Hsp16 Hstk Lg Lst Hfrg Hcond MI AC0 SW HHM HAE Haddrfrg Hcond2 HB1 HB2 HB3 HB4 HB5.
  pose proof HFRAG as HF.
  do 7 step.
  eapply evt_cut.
  { unfold reac_ctrl_identity_fragment_contract, REAC_CTRL_IDENTITY_FRAGMENT in HF.
    eapply HF with (f := f) (fr := frg) (len := len) (pa := pa) (pp := pp) (pn := pn) (st := st) (g := gfrag).
    all: try assumption.
    all: try reflexivity. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI' & ST' & FGM & AC' & SW').
  subst ms2.
  replace (ret_pc (Z_to_bv 64 533340)) with (Z_to_bv 64 533340)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exists (Z_to_bv 64 533340), a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact FGM|]. split; [exact AC' | exact SW'].
Qed.

(* ---- The same run from a cut that carries ro_agree instead of mem_inv: the body runs on the normalized memory
   (mem_inv_normalize) and MemNorm.evt_normalize carries it back to m, with mem_rel / ro_same moving the read
   facts out and the post facts back. ---- *)
Lemma f13_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    s1v = Z_to_bv 64 A -> s5 = Z_to_bv 64 f -> s2v = Z_to_bv 64 frg -> s4v = Z_to_bv 64 len ->
    0 <= f < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    AC.GT <= A -> A + 448 <= 2 ^ 64 ->
    AC.GT <= f -> AC.GT <= pa -> AC.GT <= pp -> AC.GT <= pn ->
    rw_cells rsegs m (A + 288) [C8 (Z_to_bv 64 pa)] ->
    rw_cells rsegs m (A + 296) [C8 (Z_to_bv 64 pn)] ->
    rw_cells rsegs m (A + 304) [C8 (Z_to_bv 64 pp)] ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length gfrag = 50%nat -> length st = 72%nat ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m frg gfrag) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    MN.ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1v
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8235c) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ MN.ro_agree rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82340) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4v s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag EA Ef Efrg Elen Hfb Hfrgb Hlenb Hpab Hppb Hpnb
    HGTA HAhi HGTf HGTpa HGTpp HGTpn
    Hc280 Hc296 Hc304 Hsp16 Hstk Lg Lst Hfrg Hcond HRO AC0 SW HHM HAE Haddrfrg Hcond2 HB1 HB2 HB3 HB4 HB5.
  pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
  assert (HGThi : AC.GT <= HIGHMEM_BEG) by (unfold AC.GT, HIGHMEM_BEG; lia).
  assert (HAPPb : APPMEM_END <= 2 ^ 64) by (unfold APPMEM_END; lia).
  eapply evt_mono.
  { eapply MN.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    eapply f13_evt_n with (A := A) (f := f) (frg := frg) (len := len) (pa := pa) (pp := pp) (pn := pn)
      (st := st) (gfrag := gfrag).
    - exact EA.
    - exact Ef.
    - exact Efrg.
    - exact Elen.
    - exact Hfb.
    - exact Hfrgb.
    - exact Hlenb.
    - exact Hpab.
    - exact Hppb.
    - exact Hpnb.
    - apply rwc_norm; [exact HRO | exact Hc280 | apply not_ro_hi; [lia | cbn [cells_size csize]; lia]].
    - apply rwc_norm; [exact HRO | exact Hc296 | apply not_ro_hi; [lia | cbn [cells_size csize]; lia]].
    - apply rwc_norm; [exact HRO | exact Hc304 | apply not_ro_hi; [lia | cbn [cells_size csize]; lia]].
    - exact Hsp16.
    - apply stk_norm; [exact HRO | exact Hstk | apply not_ro_hi; lia].
    - exact Lg.
    - exact Lst.
    - intros H1 H2 H3 H4 H5 H6.
      apply MN.bytes_at_normalize; [exact HRO | exact (Hfrg H1 H2 H3 H4 H5 H6)].
    - intros H1 H2 H3 H4 H5.
      destruct (Hcond H1 H2 H3 H4 H5) as (Hrw & Hpa2 & Hpp8 & Hpn8 & Wpa & Wpp & Wpn & Hdj).
      destruct (Hcond2 H1 H2 H3 H4 H5) as (Af & Apa & App & Apn & Happ78 & Hdjrt).
      destruct Af as (_ & _ & Afhi & _). destruct Apa as (_ & _ & Apahi & _).
      destruct App as (_ & _ & Apphi & _). destruct Apn as (_ & _ & Apnhi & _).
      unfold APPMEM_END in Afhi, Apahi, Apphi, Apnhi.
      split; [apply rwc_norm; [exact HRO | exact Hrw | apply not_ro_hi; [lia | cbn [cells_size csize]; lia]]|].
      split; [exact Hpa2|]. split; [exact Hpp8|]. split; [exact Hpn8|].
      split; [apply wr_norm; [exact HRO | exact Wpa | apply not_ro_hi; lia]|].
      split; [apply wr_norm; [exact HRO | exact Wpp | apply not_ro_hi; lia]|].
      split; [apply wr_norm; [exact HRO | exact Wpn | apply not_ro_hi; lia]|].
      exact Hdj.
    - apply MN.mem_inv_normalize.
    - exact (acells_rel m _ REL AC0).
    - exact (shrw_rel m _ REL SW).
    - exact HHM.
    - exact HAE.
    - intros H1 H2 H3 H4 H5 H6. exact (addr_rel m _ frg 50 REL (Haddrfrg H1 H2 H3 H4 H5 H6)).
    - intros H1 H2 H3 H4 H5.
      destruct (Hcond2 H1 H2 H3 H4 H5) as (Af & Apa & App & Apn & Happ78 & Hdjrt).
      split; [exact (addr_rel m _ f 72 REL Af)|].
      split; [exact (addr_rel m _ pa 2 REL Apa)|].
      split; [exact (addr_rel m _ pp 8 REL App)|].
      split; [exact (addr_rel m _ pn 8 REL Apn)|].
      split; [exact Happ78 | exact Hdjrt].
    - apply MN.bytes_at_normalize; [exact HRO | exact HB1].
    - apply MN.bytes_at_normalize; [exact HRO | exact HB2].
    - apply MN.bytes_at_normalize; [exact HRO | exact HB3].
    - apply MN.bytes_at_normalize; [exact HRO | exact HB4].
    - apply MN.bytes_at_normalize; [exact HRO | exact HB5]. }
  intros msx (msx0 & Pn & MR & RS).
  destruct Pn as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
                 & E & MU & WM & MI' & ST' & FGM & AC' & SW').
  subst msx0.
  destruct msx as [regs1 fregs1 pcv1 svc1 resv1 fcsr1 mem1 rom1].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', mem1.
  split; [unfold MS; subst; reflexivity|].
  split; [exact (MN.munch_rel rsegs _ m _ mem1 m0' REL Hmem RS MU)|].
  split; [exact (MN.wmono_rel rsegs m _ mem1 m0' REL Hmem RS WM)|].
  split; [exact (MN.ro_agree_same rsegs m mem1 HRO RS)|].
  split; [exact (stk_back mem1 m0' _ _ Hmem ST')|].
  split; [exact (fgmem_back mem1 m0' f pa pp pn st gfrag _ Hmem FGM)|].
  split; [exact (acells_back mem1 m0' Hmem AC') | exact (shrw_back mem1 m0' Hmem SW')].
Qed.

(* ---- seg_F13: from the pre-call cut 0x822d0 (the exit of F12; SlotInv's Inv_B82340_at: LK, the before-call copy
   of the record at fr + 336, FM and FSj, plus what the call needs: s7 = the record, the record's and Phi's bytes,
   the addressability of Phi, the record, the copy and the three output cells, and the placement of Phi against the
   frame and against the callee's stack window) through the call to the return cut 0x822ec (the entry of F14;
   SlotInv's Inv_B8235c_at: a0 = the fragment result, the two bcmp operands of F14, Phi, and the fragment's post
   memory fg_mem).  The three argument spills [s1+280] / [s1+296] / [s1+304], the record pointer [s1+240] and the
   copy pointer [s1+200] are FLI's (carried by LK); the reply flag [s1+288] is FM's.  The window, the writability of
   the frame cells and the runtime cells the callee reads come from FRA (fra_frame / fra_win / fra_app / the
   frame-location disjunction / RT / ro_agree). ---- *)
Lemma seg_F13 : forall j : nat,
  Hat B APIf ra (Inv_B8235c_at B APIf ra) j -> Hat B APIf ra (Inv_B82340_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & H18 & H20 & Hturn &
    (HLK & HbL & HFM & HFS) &
    H23 & Hlong & Hfgb & Haf & HaL & Hapa & Happ8 & Hapn & HRECR & HFRBA & HFS9).
  subst c. rewrite SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (Hplace & HfrA & Hfsmeta & Hfrwr).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillq & Hselq & Hfr56q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (rt_cells sp mem md HRT) as (HAC0 & HSW0 & HB1 & HB2 & HB3 & HB4 & HB5).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HAb : 0 <= A < 2 ^ 64) by lia.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)).
  (* placement of the frame against the callee's stack window, and of the spill area *)
  assert (HK : 0 <= REAC_CTRL_IDENTITY_FRAGMENT_K <= FN_STACK)
    by (unfold REAC_CTRL_IDENTITY_FRAGMENT_K; lia).
  pose proof (Hplace REAC_CTRL_IDENTITY_FRAGMENT_K HK) as Hfrsep.
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HfrA.
  assert (HaspH : HIGHMEM_BEG <= AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K)
    by (unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia).
  assert (HaspE : AC.aspZ regs <= APPMEM_END) by lia.
  (* the frame body is app memory above AC.GT, on both arms *)
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Happ).
  rewrite ?FRAME_SHADOW_val in *. unfold FRAME_BYTES in *.
  assert (Hfrb : 0 <= fr /\ fr + 3136 < 2 ^ 64).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1, H2. lia. }
  (* the callee's stack window, carved out of the FRA window *)
  assert (Hstkcall : stk rsegs mem (AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs)).
  { destruct (stk_split rsegs mem (AC.aspZ regs - FN_STACK)
                (AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs) Hwstk
                ltac:(unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia)) as (_ & Hs2). exact Hs2. }
  (* the frame pointers: non-zero, in range, aligned and writable *)
  assert (Hfb : 0 <= fragb fr < 2 ^ 64).
  { assert (Ha : app_mem (fr + 2768)) by (apply Happ; lia).
    unfold fragb, app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG, AC.GT in *. lia. }
  assert (Hfnz : fragb fr <> 0) by (unfold fragb, AC.GT in *; lia).
  assert (Hphinz : phi <> 0) by (destruct HHB as (HH & _); exact HH).
  assert (Hphib : 0 <= phi < 2 ^ 64)
    by (destruct HHB as (_ & Hadd); destruct Hadd as (H1 & H2 & H3 & _); unfold APPMEM_END in *; lia).
  assert (Hlenb : 0 <= flen g j < 2 ^ 64)
    by (destruct Hturn as (_ & _ & _ & Tlen); unfold flen in *; pose proof (flen_small (g_in g) j); lia).
  (* The record block's placement, which the cut now states only on a long frame: it follows from the heap
     list's block law and the frame's location, as image A's seg_F13 derives it (both arms). *)
  destruct (f13_blk (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi (AC.a_size (flen g j)) HAH
              ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity))
    as (Hblkend & Hblk).
  assert (Hasz : flen g j <= AC.a_size (flen g j) /\ 1 <= AC.a_size (flen g j))
    by (unfold AC.a_size; lia).
  assert (Hphifr : phi + 50 <= fr \/ fr + 3136 <= phi).
  { destruct Hloc as [[_ [Hspfr _]]|[_ [Hfsgap [Hfs _]]]].
    - left. lia.
    - destruct (Hfs (fr + 3135) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
      pose proof (Hfsgap FSc HwFSc HFScr) as Hgap.
      destruct (Z_lt_le_dec phi FSc) as [Hlt|Hge].
      + left. destruct (Z_lt_le_dec FSc (phi + AC.a_size (flen g j))) as [Hov|Hov]; [|lia].
        exfalso. apply (Hblk FSc ltac:(lia)). unfold AC.a_in_fs. exists FSc.
        split; [exact HFScr|]. split; [exact HwFSc | unfold AC.FS_SIZE in *; lia].
      + destruct (Z_lt_le_dec phi (FSc + AC.FS_SIZE)) as [Hin|Hout]; [|right; lia].
        exfalso. apply (Hblk phi ltac:(lia)). unfold AC.a_in_fs. exists FSc.
        split; [exact HFScr|]. split; [exact HwFSc | lia]. }
  assert (Hphisep : phi + 50 <= AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= phi)
    by (left; unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia).
  (* and the whole block [phi, phi + a_size len) against the frame (FTURN's Phi bytes are len long) *)
  assert (Hphiblk : phi + AC.a_size (flen g j) <= fr \/ fr + 3136 <= phi).
  { destruct Hloc as [[_ [Hspfr _]]|[_ [Hfsgap [Hfs _]]]].
    - left. lia.
    - destruct (Hfs (fr + 3135) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
      pose proof (Hfsgap FSc HwFSc HFScr) as Hgap.
      destruct (Z_lt_le_dec phi FSc) as [Hlt|Hge].
      + left. destruct (Z_lt_le_dec FSc (phi + AC.a_size (flen g j))) as [Hov|Hov]; [|lia].
        exfalso. apply (Hblk FSc ltac:(lia)). unfold AC.a_in_fs. exists FSc.
        split; [exact HFScr|]. split; [exact HwFSc | unfold AC.FS_SIZE in *; lia].
      + destruct (Z_lt_le_dec phi (FSc + AC.FS_SIZE)) as [Hin|Hout']; [|right; lia].
        exfalso. apply (Hblk phi ltac:(lia)). unfold AC.a_in_fs. exists FSc.
        split; [exact HFScr|]. split; [exact HwFSc | lia]. }
  assert (Hphig : 50 <= flen g j -> bytes_at rsegs mem phi (t_g (g_in g) j))
    by (intros Hl; destruct (Hlong Hl) as (_ & _ & Hg & _); exact Hg).
  assert (Haphi : 50 <= flen g j -> addressable mem phi 50)
    by (intros Hl; destruct (Hlong Hl) as (_ & _ & _ & Ha); exact Ha).
  assert (Hwr : forall a n, fr <= a -> a + n <= fr + 3136 -> 0 <= n -> wr_at rsegs mem a n).
  { intros a n Ha Hn Hn0. split; [unfold AC.GT in *; lia|].
    split; [pose proof (Happ (fr + 3135) ltac:(lia)) as Hap;
            unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; lia|].
    intros i Hi. exact (Hfrwr (a + i) ltac:(lia)). }
  assert (Hrwf : rw_cells rsegs mem (fragb fr) [CB 72 (t_FG (g_in g) j)]).
  { split; [split|].
    - cbn [cells_wf cell_wf]. split; [apply t_FG_length | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hfgb.
    - cbn [cells_size csize]. apply (Hwr (fragb fr) 72); unfold fragb; lia. }
  (* the save area [A, A + 448) lies inside the slot window, so each of its words is writable *)
  assert (HwrA : forall a, A <= a -> a + 8 <= A + 448 -> wr_at rsegs mem a 8).
  { intros a Ha Hn. destruct Hwin as (HW0 & HW1 & HW).
    split; [lia|]. split; [lia|].
    intros i Hi. destruct (HW (a + i) ltac:(lia)) as (Hv & _). exact Hv. }
  pose proof HLK as HLK2. destruct HLK2 as (_ & _ & _ & HFLI).
  destruct HFLI as (F27 & F168 & F96 & F112 & F120 & F128 & F136 & F144 & F152 & F280 & F160 & F176 &
    F192 & F200 & F216 & F208 & F104 & F256 & F264 & F288 & F296 & F304 & F2624 & Ffrstk &
    (Frad1 & Frad2 & Frad3) & (Fknt1 & Fknt2) & F168b & F88).
  assert (HFLIq : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs mem off v -> q64 mem (A + off) v).
  { intros off v Ho0 Ho1 Hs.
    exact (spill_at regs mem A off v Hs Hr9 ltac:(lia) ltac:(unfold APPMEM_END in *; lia) Ho0 Ho1). }
  assert (Hc280 : rw_cells rsegs mem (A + 288) [C8 (Z_to_bv 64 (fr + 256))])
    by (apply rwc_of_q64; [apply HFLIq; [lia | lia | exact F288] | apply HwrA; lia]).
  assert (Hc296 : rw_cells rsegs mem (A + 296) [C8 (Z_to_bv 64 (fr + 304))])
    by (apply rwc_of_q64; [apply HFLIq; [lia | lia | exact F296] | apply HwrA; lia]).
  assert (Hc304 : rw_cells rsegs mem (A + 304) [C8 (Z_to_bv 64 (fr + 272))])
    by (apply rwc_of_q64; [apply HFLIq; [lia | lia | exact F304] | apply HwrA; lia]).
  (* run the segment *)
  apply (sl_run_lib regs (Z_to_bv 64 0x82340) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x8235c /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\
       getr R0 26 = getr regs 26 /\
       getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 (fg_ret (frcl g j fr phi)) /\
       munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                (AC.aspZ regs) (frcl g j fr phi)) mem mem' /\
       wmono rsegs mem mem' /\ MN.ro_agree rsegs mem' /\
       stk rsegs mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs) /\
       fg_mem (fragb fr) (fr + 256) (fr + 272) (fr + 304) (t_FG (g_in g) j) (t_g (g_in g) j)
         (frcl g j fr phi) mem' /\
       asan_cells mem' /\ shadow_rw mem')
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f13_evt with (A := A) (f := fragb fr) (frg := phi) (len := flen g j)
        (pa := fr + 256) (pp := fr + 272) (pn := fr + 304)
        (st := t_FG (g_in g) j) (gfrag := t_g (g_in g) j).
      - unfold rg in Hr9; exact Hr9.
      - unfold rg in H23; exact H23.
      - unfold rg in H18; exact H18.
      - unfold rg in H20; exact H20.
      - exact Hfb.
      - exact Hphib.
      - exact Hlenb.
      - lia.
      - lia.
      - lia.
      - unfold AC.GT in *; lia.
      - lia.
      - unfold fragb, AC.GT in *; lia.
      - unfold AC.GT in *; lia.
      - unfold AC.GT in *; lia.
      - unfold AC.GT in *; lia.
      - exact Hc280.
      - exact Hc296.
      - exact Hc304.
      - fold_sp regs. rewrite Haspz. exact Hspm.
      - fold_sp regs. exact Hstkcall.
      - apply t_g_length.
      - apply t_FG_length.
      - intros _ _ _ _ _ Hl. exact (Hphig Hl).
      - intros _ _ _ _ _. split; [exact Hrwf|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split; [apply (Hwr (fr + 256) 2); lia|].
        split; [apply (Hwr (fr + 272) 8); lia|].
        split; [apply (Hwr (fr + 304) 8); lia|].
        fold_sp regs. unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *.
        cbn [all_dj dj_from]. repeat split; lia.
      - exact Hro.
      - exact HAC0.
      - exact HSW0.
      - fold_sp regs. exact HaspH.
      - fold_sp regs. exact HaspE.
      - intros _ _ _ _ _ Hl. exact (Haphi Hl).
      - intros _ _ _ _ _. split; [exact Haf|]. split; [exact Hapa|]. split; [exact Happ8|].
        split; [exact Hapn|].
        split; [apply Happ; unfold fragb in *; lia|].
        unfold RT_LO, RT_HI, fragb, AC.GT in *. cbn [dj_from]. repeat split; try lia; exact I.
      - exact HB1.
      - exact HB2.
      - exact HB3.
      - exact HB4.
      - exact HB5. }
    { intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                  & E & MU & WM & HRO' & ST' & FGM & AC' & SW').
      eexists _, (Z_to_bv 64 0x8235c), m'. split; [exact E|].
      split; [reflexivity|].
      do 14 (split; [reflexivity|]).
      split; [unfold frcl; reflexivity|].
      match type of ST' with context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST' end.
      split; [unfold frcl; exact MU|]. split; [exact WM|]. split; [exact HRO'|]. split; [exact ST'|].
      split; [unfold frcl; exact FGM|]. split; [exact AC' | exact SW']. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 & Er24 &
      Er25 & Er26 & Er27 & Er10 &
      MU & WM & HROM & ST' & FGM & AC' & SW') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (fg_ret (frcl g j fr phi))) by (rewrite Hreg; exact Er10).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* the write set: app memory, clear of the runtime's cells *)
    assert (Hallapp : all_app (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                                 (AC.aspZ regs) (frcl g j fr phi))).
    { apply all_app_fp.
      - intros a Ha. apply Happ. unfold fragb in Ha. lia.
      - intros a Ha. apply Happ. lia.
      - intros a Ha. apply Happ. lia.
      - intros a Ha. apply Happ. lia.
      - intros a Ha. unfold app_mem. right.
        unfold APPMEM_END, HIGHMEM_BEG, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia. }
    assert (Hrtdj : rt_disjoint (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                                   (AC.aspZ regs) (frcl g j fr phi))).
    { apply rt_dj_fp; unfold fragb, AC.GT, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *; lia. }
    (* the record's post bytes *)
    assert (Hrec : bytes_at rsegs mem' (fragb fr) (frrec g j fr phi)).
    { unfold frrec, frcl in *.
      rewrite (rf_class_nn (fragb fr) phi (fr + 256) (fr + 272) (fr + 304) (flen g j)
                 (t_FG (g_in g) j) (t_g (g_in g) j)) in *
        by (unfold fragb, AC.GT in *; lia).
      destruct (fg_fr (flen g j) (t_g (g_in g) j)) eqn:FR; cbn [negb] in *.
      - destruct (bat (t_g (g_in g) j) 19 =? 1); cbn [fg_mem fg_next] in *; [exact FGM|].
        destruct (fg_keep (t_FG (g_in g) j) (t_g (g_in g) j)); cbn [negb] in *;
          [|cbn [fg_mem fg_next] in *; exact FGM].
        destruct (fg_close (t_FG (g_in g) j) (t_g (g_in g) j)); cbn [negb fg_mem fg_next] in *;
          [exact (proj1 FGM) | exact FGM].
      - cbn [fg_mem fg_next] in *.
        eapply fl_bytes; [exact Hfgb | exact MU |].
        rewrite t_FG_length. intros x' Hx'. cbn [fg_fp outside].
        split; [unfold REAC_CTRL_IDENTITY_FRAGMENT_K, fragb in *; lia | exact I]. }
    (* every byte the call wrote is readable afterwards *)
    assert (Hrdpost : forall x,
              ~ outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                           (AC.aspZ regs) (frcl g j fr phi)) x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. destruct (fp_in _ _ _ _ _ _ (frcl g j fr phi) x Hx) as [Hf|[Hpa|[Hpp|[Hpn|Hstk]]]].
      - apply (ba_rd mem' (fragb fr) (frrec g j fr phi) x Hrec). rewrite frrec_length. lia.
      - destruct (fg_case_eq_dec (frcl g j fr phi) FgClose) as [HC|HC].
        + rewrite HC in FGM. cbn [fg_mem] in FGM. destruct FGM as (_ & Hpa2 & _ & _).
          apply (ba_rd mem' (fr + 256) _ x Hpa2). rewrite length_le2. lia.
        + exfalso. apply Hx. destruct (frcl g j fr phi) eqn:EC; try (exfalso; apply HC; reflexivity);
            cbn [fg_fp outside]; repeat split; unfold REAC_CTRL_IDENTITY_FRAGMENT_K, fragb in *;
            try lia; exact I.
      - destruct (fg_case_eq_dec (frcl g j fr phi) FgClose) as [HC|HC].
        + rewrite HC in FGM. cbn [fg_mem] in FGM. destruct FGM as (_ & _ & Hpp2 & _).
          apply (ba_rd mem' (fr + 272) _ x Hpp2). rewrite length_le8. lia.
        + exfalso. apply Hx. destruct (frcl g j fr phi) eqn:EC; try (exfalso; apply HC; reflexivity);
            cbn [fg_fp outside]; repeat split; unfold REAC_CTRL_IDENTITY_FRAGMENT_K, fragb in *;
            try lia; exact I.
      - destruct (fg_case_eq_dec (frcl g j fr phi) FgClose) as [HC|HC].
        + rewrite HC in FGM. cbn [fg_mem] in FGM. destruct FGM as (_ & _ & _ & Hpn2).
          apply (ba_rd mem' (fr + 304) _ x Hpn2). rewrite length_le8. lia.
        + exfalso. apply Hx. destruct (frcl g j fr phi) eqn:EC; try (exfalso; apply HC; reflexivity);
            cbn [fg_fp outside]; repeat split; unfold REAC_CTRL_IDENTITY_FRAGMENT_K, fragb in *;
            try lia; exact I.
      - destruct ST' as (_ & _ & HS). destruct (HS x ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
    (* AH, ownership and the stack bounds across the call's store, by arm *)
    assert (Hwmon : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
      by (intros q Hq Hw; exact (WM (Z_to_bv 64 q) Hw)).
    assert (HAHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md /\
                     (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)
                                  (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md q <->
                                AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)
                                  (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md q) /\
                     AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                       = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                     AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                       = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs _]]]].
      - (* real arm: the frame body and the callee window both lie in [stklo, APPMEM_END) *)
        assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns. apply MU. rewrite MState.unsigned_lit by exact Hq.
          apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin. apply Hns. right. left.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]].
          - specialize (Hreal q ltac:(unfold fragb in *; lia)). lia.
          - specialize (Hreal q ltac:(lia)). lia.
          - specialize (Hreal q ltac:(lia)). lia.
          - specialize (Hreal q ltac:(lia)). lia.
          - unfold APPMEM_END, REAC_CTRL_IDENTITY_FRAGMENT_K, FN_STACK in *. lia. }
        destruct (f13_store (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md
                    HAH Hmc Hwmon) as (HAH2 & Hown2 & Hstk2 & Hhi2).
        split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2].
      - (* side arm: the frame body is inside the side stack, the callee window is a_store_ok *)
        destruct (Hfs (fr + 3135) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
        destruct (f13_fs_place (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSc
                    HAH HwFSc HFScr) as (HFSgt & HFSend & HFSapp).
        pose proof (Hfsmeta FSc HwFSc HFScr) as HFSmeta.
        assert (Hstore : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FSc <= q < FSc + AC.FS_SIZE) ->
                  ~ (exists b, FSc <= b < FSc + AC.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns Hnfs _Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
          apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]].
          - apply Hnfs. unfold fragb in *. lia.
          - apply Hnfs. lia.
          - apply Hnfs. lia.
          - apply Hnfs. lia.
          - apply Hns. right. left.
            unfold APPMEM_END, REAC_CTRL_IDENTITY_FRAGMENT_K, FN_STACK in *. lia. }
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  (exists b, mbyte rsegs mem' q = Some b)).
        { intros q Hq Hb.
          destruct (outside_dec (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272)
                                   (fr + 304) (AC.aspZ regs) (frcl g j fr phi)) q) as [Ho|Ho].
          - unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - destruct (Hrdpost q Ho) as (b & Hb2). unfold mrd, mbyte, wa in *.
            destruct (mem' (Z_to_bv 64 q)) as [b'|] eqn:Em; [exists b'; reflexivity|].
            exists b. exact Hb2. }
        destruct (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _
                    (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                       (AC.aspZ regs) (frcl g j fr phi))
                    (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md FSc
                    LAWS HAH HwFSc HFScr ltac:(unfold APPMEM_END in *; lia) MU Hwmon Hpres
                    ltac:(intros q Hq; pose proof (Tac_fs.fs_meta_below FSc q Hq) as HB';
                          apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)); intros Hin;
                          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
                          unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K, FN_STACK, AC.FS_SIZE in *; lia)
                    Hstore)
          as (HAH2 & Hown2 & Hstk2 & Hhi2).
        split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2]. }
    destruct HAHSTK as (HAH' & Hown' & HSTK' & HSTKH').
    (* the frame's 392 shadow bytes are shadow addresses, so the (app) write set misses them *)
    assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
    { intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
      pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
      replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
      unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
    assert (Hshout : forall x, in_shadow x ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
      destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]].
      - exact (app_not_shadow x (Happ x ltac:(unfold fragb in *; lia)) Hx).
      - exact (app_not_shadow x (Happ x ltac:(lia)) Hx).
      - exact (app_not_shadow x (Happ x ltac:(lia)) Hx).
      - exact (app_not_shadow x (Happ x ltac:(lia)) Hx).
      - apply (app_not_shadow x); [|exact Hx]. unfold app_mem. right.
        unfold APPMEM_END, REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia. }
    (* "outside the write set" for the data above / below the frame *)
    assert (Hout : forall x, (x < fr \/ fr + 3136 <= x) ->
              (x < AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= x) ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros x H1 H2. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
      destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb in *; lia. }
    (* every cell of the save area at or above s1 = A is above the frame and above sp *)
    assert (HoutA : forall x, A <= x ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros x Hx. apply Hout; [right; lia | right; lia]. }
    (* rebuild FRA at mem', then move it to regs' / md' *)
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem' md).
    { apply (fra_mem_call g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem' md _
               HFRA MU WM Hallapp Hrtdj HROM HAH' HSTK').
      - apply (stk_keep (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                           (AC.aspZ regs) (frcl g j fr phi)) mem mem' (g_S g - AF.SLOT_STACK) (g_S g));
          [exact Hwin | exact MU | exact WM |].
        intros x Hx Ho. exact (Hrdpost x Ho).
      - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia.
      - intros A' HA'b HA' x Hx. apply HoutA.
        assert (EA' : A' = A) by (exact (rg9_eq regs A A' Hr9 HA' HAb HA'b)).
        lia.
      - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia.
      - intros x Hx. apply Hshout, HshIS, Hx.
      - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, AC.GT, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *; lia.
      - (* FSREC: the footprint below stklo is empty outside the frame body (the callee window is above stklo) *)
        intros x Hxlo Hxfr. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem' md md' HFRA');
        [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
    (* ENT: the call wrote only cells of the frame and its own stack window inside the slot window, so no byte
       the entry relation speaks of changed; then the model step of sl_run_lib. *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x \/
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + 3136) \/
              (Sfr fr <= x < Sfr fr + 392)).
    { intros x Hx.
      destruct (outside_dec (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                               (AC.aspZ regs) (frcl g j fr phi)) x) as [Ho|Ho]; [left; exact Ho|].
      destruct (fp_in _ _ _ _ _ _ (frcl g j fr phi) x Ho) as [Hf|[Hpa|[Hpp|[Hpn|Hstk2]]]].
      - right; right; left. unfold fragb in *. lia.
      - right; right; left. lia.
      - right; right; left. lia.
      - right; right; left. lia.
      - right; left. unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *. lia. }
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md).
    { apply (Tac_slot.ent_store B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem' md _
               HENT HFRA MU HWcases HSTK' HSTKH').
      intros a Hia Ho. exact (proj2 (Hown' a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem' md md' HENT' Hmat). }
    assert (Hmeta : meta_kept mem mem') by (apply (munch_meta _ mem mem' MU Hallapp)).
    assert (HoutA' : forall x, A <= x < A + 448 ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x)
      by (intros x Hx; apply HoutA; lia).
    (* the frame cells the call did not write (everything in the frame outside its four output ranges) *)
    assert (Hfrout : forall x, fr <= x < fr + 3136 ->
              (x < fragb fr \/ fragb fr + 72 <= x) ->
              (x < fr + 256 \/ fr + 258 <= x) -> (x < fr + 272 \/ fr + 280 <= x) ->
              (x < fr + 304 \/ fr + 312 <= x) ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros x Hx H1 H2 H3 H4. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
      destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
        unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
    (* the record block misses the call's footprint: apart from the frame, and far below the callee window *)
    assert (HOphi : forall x, phi <= x < phi + AC.a_size (flen g j) ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros x Hx. apply Hout;
        [destruct Hphiblk as [Hd|Hd]; [left | right]; lia
        | left; unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia]. }
    assert (HOphi50 : forall x, phi <= x < phi + 50 ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros x Hx. apply Hout;
        [destruct Hphifr as [Hd|Hd]; [left | right]; lia
        | left; unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia]. }
    (* the record's post bytes are turn j + 1's record *)
    assert (EFR : frrec g j fr phi = t_FG (g_in g) (S j)).
    { unfold frrec. rewrite t_FG_S. unfold t_FGf, fg_st. f_equal.
      rewrite (frcl_fcls g j fr phi Hfnz Hphinz ltac:(unfold AC.GT in *; lia) ltac:(unfold AC.GT in *; lia)
                 ltac:(unfold AC.GT in *; lia)). unfold flen. reflexivity. }
    assert (HIexit : Inv_B8235c_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x8235c) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hj|].
      split.
      { destruct HHB as (Hphinz2 & Hphiad). split; [exact Hphinz2|].
        eapply Tac_slot.sl_addr_keep; [exact Hphiad | exact MU | exact Hallapp]. }
      split; [unfold rg in H18 |- *; rewrite Fr18; exact H18|].
      split; [unfold rg in H20 |- *; rewrite Fr20; exact H20|].
      (* FTURN: the turn's two cursor spills and Phi's frame bytes *)
      split.
      { destruct Hturn as (T216 & T224 & Tphi & Tlen).
        split.
        { eapply spill_keep; [exact T216 | exact Hr9 | lia | lia | lia | lia | exact Fr9 | exact MU |].
          intros x Hx. apply HoutA. lia. }
        split.
        { eapply spill_keep; [exact T224 | exact Hr9 | lia | lia | lia | lia | exact Fr9 | exact MU |].
          intros x Hx. apply HoutA. lia. }
        split; [|exact Tlen].
        eapply fl_bytes; [exact Tphi | exact MU |].
        intros x Hx. apply HOphi. unfold flen in *. lia. }
      split.
      { split.
        { eapply lk_keep; [exact HLK | exact Hr9 | lia | lia | exact Fr9 | exact Fr27 | exact MU | exact WM
                           | exact Hallapp | exact HoutA' | | |].
          - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
            destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb in *; lia.
          - intros x Hx. apply Hout; [left; unfold AC.GT in *; lia | left; unfold AC.GT, HIGHMEM_BEG in *; lia].
          - intros x _ Ho. exact (Hrdpost x Ho). }
        split.
        { eapply fm_keep; [exact HFM | exact Hr9 | lia | lia | exact Fr9 | exact Fr22 | exact Fr24
                           | exact Fr25 | exact MU | exact HoutA']. }
        eapply fsj_keep; [exact HFS | exact MU | exact Hallapp |].
        intros x Hx. apply Hfrout; unfold fragb in *; lia. }
      split; [unfold rg; exact Fr10|].
      (* the record block's facts, on a long frame *)
      split.
      { intros Hl. split; [exact Hphifr|]. split; [rewrite HaspEq; exact Hphisep|].
        split.
        { eapply fl_bytes; [exact (Hphig Hl) | exact MU |].
          rewrite t_g_length. intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb in *; lia. }
        eapply addressable_kept; [exact (Haphi Hl) | exact Hmeta]. }
      split.
      { eapply fl_bytes; [exact HbL | exact MU |].
        rewrite t_FG_length. intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb in *; lia. }
      split; [eapply addressable_kept; [exact HaL | exact Hmeta]|].
      split; [exact Hrec|].
      split; [eapply addressable_kept; [exact Haf | exact Hmeta]|].
      split; [exact FGM|].
      (* RECF: the identity record is untouched, the fragment record is turn j + 1's *)
      split.
      { split.
        - split.
          + unfold IDBe. eapply fl_bytes; [exact (proj1 (proj1 HRECR)) | exact MU |].
            rewrite t_IDr_length. intros x Hx. apply Hfrout; unfold fragb in *; lia.
          + exact (proj2 (proj1 HRECR)).
        - split.
          + unfold FGBe. rewrite <- EFR. exact Hrec.
          + apply fok_FG. }
      (* FRBA: the spill base, the [A+272] word and, on a parsed header, the record invariant and the two
         6-byte compare operands at the FLI spills [A+88] / [A+80] = fr + 186 / fr + 180 *)
      split.
      { destruct HFRBA as (A0 & H9b & HA0b & HFRB).
        assert (EA0 : A0 = A) by (exact (rg9_eq regs A A0 Hr9 H9b HAb HA0b)).
        subst A0.
        destruct HFRB as (Hw112 & (w272 & Hq272 & Hw272b & Hw272t & Hw272f) & Hkp112 & HkpBC & Hkp2688 &
          HphiG & H8819).
        exists A. split; [unfold rg in *; rewrite Fr9; exact Hr9|]. split; [exact HAb|].
        split; [exact Hw112|].
        split.
        { exists w272.
          split.
          { unfold q64 in *. eapply fl_bytes; [exact Hq272 | exact MU |].
            rewrite length_le8. intros x Hx. apply HoutA. lia. }
          split; [exact Hw272b|]. split; [exact Hw272t | exact Hw272f]. }
        split; [exact Hkp112|].
        split; [rewrite HaspEq; exact HkpBC|].
        split; [exact Hkp2688|].
        split.
        { intros Hl. destruct (HphiG Hl) as (HpA & HpBC). split; [exact HpA | rewrite HaspEq; exact HpBC]. }
        intros H8.
        destruct (H8819 H8) as (HRI &
          (L & ls & rs & QL & HBL1 & HLl & HBR1 & HLr & Hmm1 & HAL1 & Hap6 & Hap7 & HLBC & HLA & HL2688) &
          (L2 & ls2 & rs2 & QL2 & HBL2 & HLl2 & HBR2 & HLr2 & Hmm2 & HAL2 & Hap62 & Hap72 & HL2BC & HL2A &
           HL22688)).
        assert (EL : L = fr + 186).
        { apply (q64_det mem (A + 112) L (fr + 186) QL (HFLIq 112 _ ltac:(lia) ltac:(lia) F112));
            [destruct HAL1 as (HL0 & _ & HLe & _); unfold APPMEM_END in *; lia
            | unfold AC.GT, APPMEM_END in *; lia]. }
        assert (EL2 : L2 = fr + 180).
        { apply (q64_det mem (A + 96) L2 (fr + 180) QL2 (HFLIq 96 _ ltac:(lia) ltac:(lia) F96));
            [destruct HAL2 as (HL0 & _ & HLe & _); unfold APPMEM_END in *; lia
            | unfold AC.GT, APPMEM_END in *; lia]. }
        subst L L2.
        split.
        { apply (rec_inv_keep g j phi A (fr + 176) mem mem'
                   (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                      (AC.aspZ regs) (frcl g j fr phi)) HRI MU).
          - intros x Hx. apply HOphi50. lia.
          - intros x Hx. apply HoutA. lia.
          - intros x Hx. apply Hshout. exact Hx.
          - intros x Hx. apply Hfrout; unfold fragb in *; lia. }
        split.
        { exists (fr + 186), ls, rs.
          split.
          { unfold q64 in *. eapply fl_bytes; [exact QL | exact MU |].
            rewrite length_le8. intros x Hx. apply HoutA. lia. }
          split.
          { eapply fl_bytes; [exact HBL1 | exact MU |]. rewrite HLl.
            intros x Hx. apply Hfrout; unfold fragb in *; lia. }
          split; [exact HLl|].
          split.
          { eapply fl_bytes; [exact HBR1 | exact MU |]. rewrite HLr.
            intros x Hx. apply HOphi50. lia. }
          split; [exact HLr|].
          split; [exact Hmm1|].
          split; [eapply addressable_kept; [exact HAL1 | exact Hmeta]|].
          split; [exact Hap6|]. split; [exact Hap7|].
          split; [rewrite HaspEq; exact HLBC|]. split; [exact HLA | exact HL2688]. }
        { exists (fr + 180), ls2, rs2.
          split.
          { unfold q64 in *. eapply fl_bytes; [exact QL2 | exact MU |].
            rewrite length_le8. intros x Hx. apply HoutA. lia. }
          split.
          { eapply fl_bytes; [exact HBL2 | exact MU |]. rewrite HLl2.
            intros x Hx. apply Hfrout; unfold fragb in *; lia. }
          split; [exact HLl2|].
          split.
          { eapply fl_bytes; [exact HBR2 | exact MU |]. rewrite HLr2.
            intros x Hx. apply HOphi50. lia. }
          split; [exact HLr2|].
          split; [exact Hmm2|].
          split; [eapply addressable_kept; [exact HAL2 | exact Hmeta]|].
          split; [exact Hap62|]. split; [exact Hap72|].
          split; [rewrite HaspEq; exact HL2BC|]. split; [exact HL2A | exact HL22688]. } }
      (* FRX: the record bytes, the fragment and identity records, and (on the arm that closes a record) the
         first-fragment values with the address cell the call wrote *)
      split.
      { split.
      { intros Hl. split.
        { eapply fl_bytes; [exact (Hphig Hl) | exact MU |].
          rewrite t_g_length. intros x Hx. apply HOphi50. lia. }
        split; [eapply addressable_kept; [exact (Haphi Hl) | exact Hmeta] | exact Hphifr]. }
      split; [exact Hrec|].
      split; [eapply addressable_kept; [exact Haf | exact Hmeta]|].
      split.
      { exists (t_IDr (g_in g) j). split; [apply t_IDr_length|].
        split; [split|].
        - cbn [cells_wf cell_wf]. split; [apply t_IDr_length | exact I].
        - cbn [cells_bytes cbytes]. rewrite app_nil_r.
          eapply fl_bytes; [exact (proj1 (proj1 HRECR)) | exact MU |].
          rewrite t_IDr_length. intros x Hx. apply Hfrout; unfold fragb in *; lia.
        - cbn [cells_size csize]. split; [unfold AC.GT in *; lia|].
          split; [pose proof (Happ (fr + 3135) ltac:(lia)) as Hap;
                  unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; lia|].
          intros i Hi. apply (Hwmon (fr + 2688 + i)); [unfold APPMEM_END, AC.GT in *; lia|].
          exact (Hfrwr (fr + 2688 + i) ltac:(lia)). }
      split; [eapply addressable_kept; [exact Frad1 | exact Hmeta]|].
      intros Hrf1.
      pose proof (trf1_cls (g_in g) j Hrf1) as Hcls.
      assert (HCfrcl : frcl g j fr phi = FgClose).
      { rewrite (frcl_fcls g j fr phi Hfnz Hphinz ltac:(unfold AC.GT in *; lia)
                   ltac:(unfold AC.GT in *; lia) ltac:(unfold AC.GT in *; lia)).
        unfold flen. exact Hcls. }
      destruct (cls_close_inv _ _ _ Hcls) as (Hfr' & Hkeep & Hclose & _).
      pose proof (t_FG_length (g_in g) j) as HLst. pose proof (t_g_length (g_in g) j) as HLg.
      pose proof (fr_fg_n _ _ Hfr') as Hnn.
      destruct (fst_bounds (g_in g) j) as (Hhave01 & Hnb).
      assert (Hbat6 : bat (t_FG (g_in g) j) 6 = 1).
      { pose proof (keep_hf _ _ Hkeep) as Hhf. unfold fg_hf in Hhf.
        destruct (fok_FG (g_in g) j) as ([H0|H1] & _); [exfalso; apply Hhf; exact H0 | exact H1]. }
      destruct HFS as (_ & _ & _ & _ & HFI).
      destruct (fi_nb _ _ HFI Hbat6) as (Hhave1 & Hnbeq).
      (* the closing test fg_close starts with 14 <= fg_T *)
      assert (HT14 : 14 <= fg_T (t_FG (g_in g) j) (t_g (g_in g) j)).
      { unfold fg_close in Hclose.
        repeat (apply andb_prop in Hclose; destruct Hclose as [Hclose _]).
        apply Z.leb_le. exact Hclose. }
      destruct (joined_close _ _ _ HLst HLg (fok_FG (g_in g) j) HFI Hbat6 Hnn HT14) as (E17 & E18).
      assert (HU : u16 mem' (fr + 256) (fg_addr (t_FG (g_in g) j) (t_g (g_in g) j))).
      { pose proof FGM as FGM'. rewrite HCfrcl in FGM'. cbn [fg_mem] in FGM'.
        destruct FGM' as (_ & Hpa & _ & _). unfold u16. exact Hpa. }
      assert (HADb : 0 <= fg_addr (t_FG (g_in g) j) (t_g (g_in g) j) < 65536).
      { unfold fg_addr.
        pose proof (bat_nonneg (fg_join (t_FG (g_in g) j) (t_g (g_in g) j)) 17).
        pose proof (bat_lt (fg_join (t_FG (g_in g) j) (t_g (g_in g) j)) 17).
        pose proof (bat_nonneg (fg_join (t_FG (g_in g) j) (t_g (g_in g) j)) 18).
        pose proof (bat_lt (fg_join (t_FG (g_in g) j) (t_g (g_in g) j)) 18). lia. }
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [rewrite <- E17; split; [apply bat_nonneg | apply bat_lt]|].
      split; [rewrite <- E18; split; [apply bat_nonneg | apply bat_lt]|].
      exists (fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)).
      split; [exact HU|]. split; [exact HADb|].
      unfold fg_addr, joined_addr. rewrite E17, E18. reflexivity. }
      (* FS9: the spill [A+248] = 1 - sum_ok is above sp and the frame, outside the call's footprint *)
      eapply fs9_keep; [exact HFS9 | exact Hr9 | lia | lia | exact Fr9 | exact MU | exact HoutA']. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
