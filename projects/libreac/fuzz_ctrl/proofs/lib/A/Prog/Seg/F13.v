(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths, module names and numbers changed; 1284 of its 1418 lines of code are new or changed and 2423 lines of the source are left out. *)
(* Segment F13 (plan-asan 2 / section 2 row F13 = 0x82138-0x82150, call FRAG@0x82150), in the slot framework
   (CUTST / FRA / LK), against the push-5 cut set.  The reply-arm frame-loop body sets up the six arguments of
   reac_ctrl_identity_fragment (a0=s9, a1=s7, a2=s2, a3=[s1+256], a4=[s1+272], a5=[s1+264]) and calls it at
   0x82150; the segment runs from the pre-call cut 0x82138 through the call and lands at the return cut 0x82154
   with a0 = the fragment result.

   The five pointers the callee gets all sit INSIDE the 3136-byte frame body: the record f = fragb fr = fr + 2768
   ([s1+208], set 0x813c4), pa = fr + 256 ([s1+256], 0x81348), pp = fr + 272 ([s1+272], 0x81350) and
   pn = fr + 304 ([s1+264], 0x81358); the sixth argument is the record pointer phi = s7.  The callee's write set
   is fg_fp K f pa pp pn S c: those cells plus the callee stack window [S - K, S).  Every placement fact the
   proof needs is arm-neutral and read off FRA by fra_frame (frame apart from the callee window on both arms,
   fr + 3136 <= s1, the FakeStack metadata below fr) and fra_win (the sp-anchored window); the cut itself carries
   only the register / memory data of the call.  The callee contract reac_ctrl_identity_fragment_contract is a
   Section Hypothesis (plan-asan 8.1); the run lifts through AsanLift.evt_SR_canon_lazy (sl_run_lib). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.

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

(* The length is never negative: the declared length is a sum of two bytes and the bytes left are max (left - 2, 0). *)
Lemma flen_nonneg : forall inp j, 0 <= t_len inp j.
Proof.
  intros inp j. unfold t_len, f_len, f_h.
  assert (HL : 0 <= f_L inp (fc inp j)).
  { unfold f_L. pose proof (inb_range inp (fc inp j)) as H1.
    pose proof (inb_range inp (fc inp j + 1)) as H2.
    destruct (2 <=? f_left inp (fc inp j)); lia. }
  lia.
Qed.

(* ---- the fragment footprint. ---- *)

Lemma fg_fp_dj : forall K f pa pp pn S c a n,
  disjoint_from (fg_fp K f pa pp pn S FgClose) a n ->
  disjoint_from (fg_fp K f pa pp pn S c) a n.
Proof. intros K f pa pp pn S c a n H. destruct c; cbn [fg_fp disjoint_from] in *; tauto. Qed.

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

(* ---- The fragment class frcl and the record's post bytes frrec at this call site's pointers are SlotInv's
   (aslot push 11B). ---- *)

Lemma frrec_length : forall g j fr phi, length (frrec g j fr phi) = 72%nat.
Proof.
  intros g j fr phi. unfold frrec, frcl.
  apply fg_next_length; [apply t_FG_length | apply t_g_length].
Qed.

(* At this call site the class is the model's class of the turn: the five pointers are non-zero, and past the
   refusal test the class reads only len / st / g. So the record the call leaves is the model's t_FGf j on every
   arm (moved here from F14.v / F15.v for push 12: F13 now names the turn S j fragment record). *)
Lemma frcl_fcls : forall g j fr phi, fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  frcl g j fr phi = fcls (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j).
Proof.
  intros g j fr phi H1 H2 H3 H4 H5. unfold frcl, fcls.
  rewrite (rf_class_nn (fragb fr) phi (fr + 256) (fr + 272) (fr + 304)) by assumption.
  rewrite (rf_class_nn 1 1 1 1 1) by lia. reflexivity.
Qed.

Lemma frrec_FGf : forall g j fr phi, fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  frrec g j fr phi = t_FGf (g_in g) j.
Proof.
  intros g j fr phi H1 H2 H3 H4 H5. unfold frrec, t_FGf, fg_st.
  rewrite (frcl_fcls g j fr phi) by assumption. unfold flen. reflexivity.
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

(* Fold the engine-form stack pointer `bv_unsigned (reg_get regs 2)` (from Regs6ss.mkR_of) back to AC.aspZ regs. *)
Ltac fold_sp regs :=
  match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) end.

(* ---- The carried bundles F17CARRY / F16CARRY (the fields of the F16 entry cut 0x821d0 and of the official F17
   entries Inv_A8229c_at / Inv_A822a0_at that F13, F14 and F15 neither compute nor read) are SlotInv's (aslot
   push 11B).  They are set before 0x82138 (the F12 exit must produce F16CARRY there) and pass unchanged through
   the fragment call, the bcmp and F15: the cells are spills in [A+32, A+312), frame bytes at fr + 176 .. fr + 200
   and fr + 2688 .. fr + 2726, the record block [phi, phi + len) and shadow bytes, all outside both callees' write
   sets; registers s2, s6, s7, s8 and s1 are callee-saved. *)
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Local Abbreviation memcmp_model := StrFun.memcmp_model.

(* A carried 8-byte cell in the form the load tactic consumes. *)
Lemma f13_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* Two 8-byte values read at one address agree. *)
Lemma q64_same : forall m a v w, q64 m a v -> q64 m a w -> Z_to_bv 64 v = Z_to_bv 64 w.
Proof.
  intros m a v w Hv Hw. unfold q64 in *.
  pose proof (f13_rd8 m a _ Hv (length_le8 _)) as E1.
  pose proof (f13_rd8 m a _ Hw (length_le8 _)) as E2.
  assert (E : le8 (Z_to_bv 64 v) = le8 (Z_to_bv 64 w)) by congruence.
  transitivity (bv_extract 0 64 (le_bytes_to_word (le8 (Z_to_bv 64 v)))); [symmetry; apply load_u64|].
  rewrite E. apply load_u64.
Qed.

Lemma q64_eq : forall m a v w, q64 m a v -> q64 m a w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
  intros m a v w Hv Hw Hvb Hwb. pose proof (q64_same m a v w Hv Hw) as E.
  apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

(* A spill cell survives a run that keeps s1 and misses the cell. *)
Lemma spill_keep : forall regs regs' m m' W A off v,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  getr regs' 9 = getr regs 9 -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v (A' & H9' & Hq) H9 HA0 HA1 Ho0 Ho1 E9 MU Hout.
  assert (EA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    pose proof Hq as Hq'. unfold q64, bytes_at in Hq'. rewrite length_le8 in Hq'.
    destruct Hq' as (Hb1 & Hb2 & _).
    revert Hm Hb1 Hb2 HA0 HA1 Ho0 Ho1. change (2 ^ 64) with 18446744073709551616. intros.
    Z.div_mod_to_equations. lia. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8. exact Hout.
Qed.

Lemma bytes_at_firstn : forall m a bs n, bytes_at rsegs m a bs -> (n <= length bs)%nat ->
  bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n H Hn. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(* A write set in app memory misses every shadow byte. *)
Lemma shadow_outside : forall W x, all_app W -> in_shadow x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x HA Hs; cbn [outside all_app] in *; [exact I|].
  destruct HA as (H1 & H2). split; [|apply IH; assumption].
  intros Hx. exact (app_not_shadow x (H1 x Hx) Hs).
Qed.

Lemma b8_shadow_keep : forall m m' W p v, munch W m m' -> all_app W -> app_mem p ->
  b8 m (Z.shiftr p 3 + ASAN_K) v -> b8 m' (Z.shiftr p 3 + ASAN_K) v.
Proof.
  intros m m' W p v MU AW Hp H. unfold b8 in *. eapply fl_bytes; [exact H | exact MU |].
  cbn [length]. intros x Hx. apply shadow_outside; [exact AW|].
  rewrite Z.shiftr_div_pow2 in Hx by lia. change (2 ^ 3) with 8 in Hx.
  replace x with (shadow_addr p) by (unfold shadow_addr; lia).
  apply shadow_of_app. exact Hp.
Qed.

Lemma t_blk_length : forall inp j, length (t_blk inp j) = 32%nat.
Proof.
  intros inp j. unfold t_blk. rewrite rf_bsl_length; [reflexivity | lia | lia |].
  rewrite t_g_length. lia.
Qed.

Lemma bsl34_length : forall inp j, length (RF.bsl (t_g inp j) 34 6) = 6%nat.
Proof. intros inp j. rewrite rf_bsl_length; [reflexivity | lia | lia |]. rewrite t_g_length. lia. Qed.

(* The compare model reads only the first n bytes of each list, so cutting the lists at k >= n keeps its value.
   The carried compare operands are 6 bytes long at most for the transports below, which need their exact span. *)
Lemma memcmp_firstn : forall n k (l r : list byte), (n <= k)%nat ->
  memcmp_model (firstn k l) (firstn k r) n = memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros k l r Hk; [reflexivity|].
  destruct k as [|k]; [lia|].
  destruct l as [|a l]; destruct r as [|b r]; cbn [firstn memcmp_model]; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH; lia | reflexivity].
Qed.

(* The 8819 arm is a long frame: t_8819 is a conjunction whose first factor is t_big = (50 <=? len). *)
Lemma t8819_big : forall g j, t_8819 (g_in g) j = true -> 50 <= flen g j.
Proof.
  intros g j H. unfold t_8819 in H. rewrite !andb_true_iff in H.
  destruct H as ((Hb & _) & _). unfold t_big in Hb. apply Z.leb_le in Hb. unfold flen. exact Hb.
Qed.

(* The frame body the memcpy copies to phi is at most len bytes long. *)
Lemma t_phi_len : forall g j, Z.of_nat (length (t_phi (g_in g) j)) <= flen g j.
Proof.
  intros g j. unfold flen, t_phi, f_phi. rewrite length_firstn.
  pose proof (flen_nonneg (g_in g) j) as H. unfold t_len in *. lia.
Qed.

(* v1.9: the harness's FIRST state FSb is the spills [A + 104] (have) and [A + 112] (n), and the body bytes with
   their shadow at fr + 2880 (first.sroa.7, 35 bytes).  The body is block[9 ..] of a 50-byte frame cut to n bytes,
   so it is at most 23 bytes long. *)
Lemma fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn, t_g_length. lia.
Qed.

Lemma fsj_keep : forall g fr j A regs regs' m m' W, FSj g fr j regs m ->
  rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 -> munch W m m' -> meta_kept m m' ->
  (forall x, A + 104 <= x < A + 120 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x) -> FSj g fr j regs' m'.
Proof.
  intros g fr j A regs regs' m m' W HFS H9 HA0 HA E9 MU MK Ho Hob. unfold FSj, FSb in *.
  destruct HFS as (S104 & S112 & Hbody & Hadd & HFI).
  split; [eapply spill_keep; [exact S104 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply Ho; lia|].
  split; [eapply spill_keep; [exact S112 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply Ho; lia|].
  split.
  { eapply fl_bytes; [exact Hbody | exact MU |].
    pose proof (fs_body_len (g_in g) j) as Hl. intros x Hx. apply Hob. lia. }
  split; [eapply addressable_kept; [exact Hadd | exact MK] | exact HFI].
Qed.

(* F16CARRY survives a run with write set W (app memory) that keeps s1, s2, s4, s6, s7 and s8 and misses the spills
   [A+32, A+312), the record block [phi, phi + len) on a long frame and the frame bytes [fr + 176, fr + 200),
   [fr + 2688, fr + 2726) and (v1.9) the FIRST body [fr + 2880, fr + 2915).  Every record fact is guarded by
   50 <= len (the 8819 arm is one of those), so the short arm needs no record-byte premise. *)
Lemma f16carry_keep : forall g j fr phi A regs regs' m m' W,
  F16CARRY g j fr phi A regs m ->
  munch W m m' -> all_app W ->
  rg regs 9 A -> 0 <= fr -> fr + FRAME_BYTES <= A -> A + 416 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 20 = getr regs 20 ->
  getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  (forall x, A + 32 <= x < A + 312 -> outside W x) ->
  (50 <= flen g j -> forall x, phi <= x < phi + flen g j -> outside W x) ->
  (forall x, fr + 176 <= x < fr + 200 -> outside W x) ->
  (forall x, fr + 2688 <= x < fr + 2726 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x) ->
  F16CARRY g j fr phi A regs' m'.
Proof.
  intros g j fr phi A regs regs' m m' W HC MU AW H9 Hfr0 HfrA HA E9 E18 E20 E22 E23 E24 HoA Hophi Hofr Hoid Hobody.
  pose proof FRAME_BYTES_val as HFBv.
  assert (MK : meta_kept m m') by (apply (munch_meta W m m' MU AW)).
  unfold F16CARRY, F17CARRY in *.
  destruct HC as (Hfok & HFS & (idb & Hidb & Lidb) & Haid & H144 &
    H23 & H22 & H24 & H18 & H20 & H232 & H192u & H136 & H120 & H176 & H152 & Hw & H50 & H88).
  assert (HA0 : 0 <= A) by lia.
  assert (HqA : forall off v, 32 <= off -> off + 8 <= 312 -> q64 m (A + off) v -> q64 m' (A + off) v).
  { intros off v Ho1 Ho2 Hq. unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
    rewrite length_le8. intros x Hx. apply HoA. lia. }
  assert (Hph : 50 <= flen g j -> forall k bs, 0 <= k -> k + Z.of_nat (length bs) <= flen g j ->
            bytes_at rsegs m (phi + k) bs -> bytes_at rsegs m' (phi + k) bs).
  { intros Hl k bs Hk Hkl Hb. eapply fl_bytes; [exact Hb | exact MU |].
    intros x Hx. apply (Hophi Hl). lia. }
  assert (Hfrb : forall k bs, 176 <= k -> k + Z.of_nat (length bs) <= 200 ->
            bytes_at rsegs m (fr + k) bs -> bytes_at rsegs m' (fr + k) bs).
  { intros k bs Hk Hkl Hb. eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply Hofr. lia. }
  split; [exact Hfok|].
  split.
  { eapply fsj_keep; [exact HFS | exact H9 | lia | lia | exact E9 | exact MU | exact MK | |].
    - intros x Hx. apply HoA. lia.
    - exact Hobody. }
  split.
  { exists idb. split; [|exact Lidb]. eapply fl_bytes; [exact Hidb | exact MU |].
    rewrite Lidb. intros x Hx. apply Hoid. lia. }
  split; [eapply addressable_kept; [exact Haid | exact MK]|].
  split; [apply HqA; [lia | lia | exact H144]|].
  split; [unfold rg in *; rewrite E23; exact H23|].
  split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E24; exact H24|].
  split; [unfold rg in *; rewrite E18; exact H18|].
  split; [unfold rg in *; rewrite E20; exact H20|].
  split; [apply HqA; [lia | lia | exact H232]|].
  split; [apply HqA; [lia | lia | exact H192u]|].
  split; [apply HqA; [lia | lia | exact H136]|].
  split; [apply HqA; [lia | lia | exact H120]|].
  split; [apply HqA; [lia | lia | exact H176]|].
  split; [eapply spill_keep; [exact H152 | exact H9 | lia | lia | lia | lia | exact E9 | exact MU |];
          intros x Hx; apply HoA; lia|].
  split.
  { destruct Hw as (w240 & H240 & Hwb & Hwt & Hwf).
    exists w240. split; [apply HqA; [lia | lia | exact H240]|].
    split; [exact Hwb|]. split; [exact Hwt | exact Hwf]. }
  split.
  { intros Hl. destruct (H50 Hl) as ((rb & Hrb & Lrb) & Hgb & Hpb & HRI).
    pose proof (t_phi_len g j) as Hpl.
    split.
    { exists (firstn 38 rb). rewrite length_firstn. split; [|lia].
      rewrite <- (Z.add_0_r phi). apply (Hph Hl); [lia | rewrite length_firstn; lia |].
      rewrite Z.add_0_r. apply bytes_at_firstn; [exact Hrb | lia]. }
    split.
    { rewrite <- (Z.add_0_r phi). apply (Hph Hl);
        [lia | rewrite t_g_length; lia | rewrite Z.add_0_r; exact Hgb]. }
    split.
    { rewrite <- (Z.add_0_r phi). apply (Hph Hl);
        [lia | lia | rewrite Z.add_0_r; exact Hpb]. }
    unfold rec_inv0 in *.
    destruct HRI as (Hp0 & Hp50 & Hfl & Htk & Happ & H192 & Hblk & H34 & Hkp & H280).
    split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|].
    split; [exact Happ|].
    split; [apply HqA; [lia | lia | exact H192]|].
    split; [apply (Hph Hl); [lia | rewrite t_blk_length; lia | exact Hblk]|].
    split; [apply (Hph Hl); [lia | rewrite bsl34_length; lia | exact H34]|].
    split; [apply HqA; [lia | lia | exact Hkp] | apply HqA; [lia | lia | exact H280]]. }
  (* the two compare operands, cut to the 6 bytes the compare reads: the transport needs their exact span *)
  intros Ht. pose proof (t8819_big g j Ht) as Hl50.
  assert (Happ : forall a, phi <= a < phi + 50 -> app_mem a)
    by (destruct (H50 Hl50) as (_ & _ & _ & (_ & _ & _ & _ & Happ & _)); exact Happ).
  destruct (H88 Ht) as (HRP & (ls & rs & H56 & Hls & Lls & Hrs & Lrs & Hmm & Ha186) &
    (ls2 & rs2 & H48 & Hls2 & Lls2 & Hrs2 & Lrs2 & Hmm2 & Ha180)).
  (* push 15: the parse-made part of rec_inv (rec_parse), on the 8819 arm (a long frame) *)
  split.
  { unfold rec_parse in *.
    destruct HRP as (f16 & v14 & v15 & v16 & v17 & Hu16 & B14 & B15 & B16 & B17 &
      R14 & R15 & R16 & R17 & S14 & S15 & S16 & S17 & Ef16 & Eif).
    exists f16, v14, v15, v16, v17.
    split; [unfold u16 in *; replace (fr + 176 + 20) with (fr + 196) in * by lia;
            apply Hfrb; [lia | rewrite length_le2; lia | exact Hu16]|].
    unfold b8 in B14, B15, B16, B17.
    split; [unfold b8; apply (Hph Hl50); [lia | cbn [length]; lia | exact B14]|].
    split; [unfold b8; apply (Hph Hl50); [lia | cbn [length]; lia | exact B15]|].
    split; [unfold b8; apply (Hph Hl50); [lia | cbn [length]; lia | exact B16]|].
    split; [unfold b8; apply (Hph Hl50); [lia | cbn [length]; lia | exact B17]|].
    split; [exact R14|]. split; [exact R15|]. split; [exact R16|]. split; [exact R17|].
    split; [apply (b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S14]|].
    split; [apply (b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S15]|].
    split; [apply (b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S16]|].
    split; [apply (b8_shadow_keep m m' W); [exact MU | exact AW | apply Happ; lia | exact S17]|].
    split; [exact Ef16 | exact Eif]. }
  assert (Lf : forall bs : list byte, (6 <= length bs)%nat -> length (firstn 6 bs) = 6%nat)
    by (intros bs Hb; rewrite length_firstn; lia).
  split.
  { exists (firstn 6 ls), (firstn 6 rs).
    split; [apply HqA; [lia | lia | exact H56]|].
    split; [apply Hfrb; [lia | rewrite (Lf ls Lls); lia | apply bytes_at_firstn; [exact Hls | lia]]|].
    split; [rewrite (Lf ls Lls); lia|].
    split; [rewrite <- (Z.add_0_r phi); apply (Hph Hl50);
            [lia | rewrite (Lf rs Lrs); lia | rewrite Z.add_0_r; apply bytes_at_firstn; [exact Hrs | lia]]|].
    split; [rewrite (Lf rs Lrs); lia|].
    split; [rewrite memcmp_firstn by lia; exact Hmm|].
    eapply addressable_kept; [exact Ha186 | exact MK]. }
  exists (firstn 6 ls2), (firstn 6 rs2).
  split; [apply HqA; [lia | lia | exact H48]|].
  split; [apply Hfrb; [lia | rewrite (Lf ls2 Lls2); lia | apply bytes_at_firstn; [exact Hls2 | lia]]|].
  split; [rewrite (Lf ls2 Lls2); lia|].
  split; [apply (Hph Hl50); [lia | rewrite (Lf rs2 Lrs2); lia | apply bytes_at_firstn; [exact Hrs2 | lia]]|].
  split; [rewrite (Lf rs2 Lrs2); lia|].
  split; [rewrite memcmp_firstn by lia; exact Hmm2|].
  eapply addressable_kept; [exact Ha180 | exact MK].
Qed.

(* ---- Push 12 (a Theorem Labs lane's ifs-design.md (a working note, not in this delivery)): the stage bundles IFS1 / IFS2 / IFS3 of SlotInv.v. The model step of
   turn j (SlotModel turn): the fragment record of turn S j is t_FGf j, the identity of turn S j is fg_id of the
   half-way identity ID1 g j, and the two records keep their lengths (72 and 38 bytes). ---- *)
Lemma t_FG_S : forall inp j, t_FG inp (S j) = t_FGf inp j.
Proof.
  intros inp j. unfold t_FG, t_FGf. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

Lemma t_ID_S1 : forall g j,
  t_ID (g_in g) (S j) = fg_id (ID1 g j) (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j).
Proof.
  intros g j. unfold ID1, flen, t_ID, t_FG. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len (g_in g) j) (t_g (g_in g) j)); reflexivity.
Qed.

(* On the edge that skips the fragment ingest (t_rf j <> 1) the identity of turn S j is ID1 g j. *)
Lemma t_ID_S_skip : forall g j, t_rf (g_in g) j <> 1 -> t_ID (g_in g) (S j) = ID1 g j.
Proof.
  intros g j H. rewrite t_ID_S1. unfold fg_id.
  replace (fg_rf (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j) =? 1) with false; [reflexivity|].
  symmetry. apply Z.eqb_neq. exact H.
Qed.

Lemma rp_id_length : forall idb len g, length idb = RIM.ID_SIZE -> length (rp_id idb len g) = RIM.ID_SIZE.
Proof.
  intros idb len g H. unfold rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply RIM.ING_length; exact H | exact H].
Qed.

Lemma fg_id_length : forall idb len st g, length idb = RIM.ID_SIZE ->
  length (fg_id idb len st g) = RIM.ID_SIZE.
Proof.
  intros idb len st g H. unfold fg_id.
  destruct (fg_rf len st g =? 1); [apply RIM.ING_length; exact H | exact H].
Qed.

Lemma t_ID_length : forall inp j, length (t_ID inp j) = RIM.ID_SIZE.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold t_ID in *. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; apply fg_id_length, rp_id_length, IH.
Qed.

Lemma ID1_length : forall g j, length (ID1 g j) = 38%nat.
Proof. intros g j. change 38%nat with RIM.ID_SIZE. unfold ID1. apply rp_id_length, t_ID_length. Qed.

(* frag_ok after the fragment call: FgRefuse / FgNone keep the record, FgFirst writes byte 6 = 1 and byte 7 =
   fg_n g (1 .. 22 by fg_fr), FgDrop / FgJoin / FgClose end in fg_clear, whose byte 6 is 0. *)
Lemma frag_ok_clear : forall l, (6 <= length l)%nat -> frag_ok (fg_clear l).
Proof.
  intros l Hl. assert (E : bat (fg_clear l) 6 = 0).
  { unfold bat, fg_clear. change (Z.to_nat 6) with 6%nat.
    rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (6 - Nat.min 6 (length l))%nat with 0%nat by lia. reflexivity. }
  unfold frag_ok. rewrite E. split; [left; reflexivity | intros H; discriminate H].
Qed.

Lemma frag_ok_first : forall st g, length g = 50%nat -> 1 <= fg_n g <= 22 -> frag_ok (fg_first st g).
Proof.
  intros st g HG Hn.
  assert (L6 : length (bsl g 6 6) = 6%nat)
    by (rewrite rf_bsl_length; [reflexivity | lia | lia | rewrite HG; lia]).
  assert (E6 : bat (fg_first st g) 6 = 1).
  { unfold bat, fg_first. change (Z.to_nat 6) with 6%nat.
    rewrite app_nth2 by lia. rewrite L6. reflexivity. }
  assert (E7 : bat (fg_first st g) 7 = fg_n g).
  { unfold bat, fg_first, fg_n. change (Z.to_nat 7) with 7%nat.
    rewrite app_nth2 by lia. rewrite L6. reflexivity. }
  unfold frag_ok. rewrite E6, E7. split; [right; reflexivity | intros _; exact Hn].
Qed.

Lemma frag_ok_fg_st : forall len st g, frag_ok st -> length st = 72%nat -> length g = 50%nat ->
  frag_ok (fg_st len st g).
Proof.
  intros len st g HOK HL HG. unfold fg_st, fcls.
  rewrite (rf_class_nn 1 1 1 1 1) by lia.
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HOK].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply frag_ok_first; [exact HG | apply (fr_fg_n len); exact FR].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply frag_ok_clear; lia].
    destruct (fg_close st g); cbn [negb fg_next]; apply frag_ok_clear;
      rewrite (rf_fg_join_length st g HL HG (fr_fg_n len g FR) (keep_T st g KEEP)); lia.
Qed.

(* The three parts of a stage bundle cross a run that misses their bytes (and keeps s1). *)
Lemma idbe_keep : forall g fr idb m m' W, IDBe g fr idb m -> length idb = 38%nat -> munch W m m' ->
  (forall x, fr + 2688 <= x < fr + 2726 -> outside W x) -> IDBe g fr idb m'.
Proof.
  intros g fr idb m m' W H L MU Ho. unfold IDBe in *. eapply fl_bytes; [exact H | exact MU |].
  rewrite L. intros x Hx. apply Ho. lia.
Qed.

Lemma fgbe_keep : forall g fr st m m' W, FGBe g fr st m -> length st = 72%nat -> munch W m m' ->
  (forall x, fr + 2768 <= x < fr + 2840 -> outside W x) -> FGBe g fr st m'.
Proof.
  intros g fr st m m' W H L MU Ho. unfold FGBe in *. eapply fl_bytes; [exact H | exact MU |].
  rewrite L. intros x Hx. apply Ho. lia.
Qed.

Lemma fsj_regs : forall g fr j regs regs' m, FSj g fr j regs m -> getr regs' 9 = getr regs 9 ->
  FSj g fr j regs' m.
Proof.
  intros g fr j regs regs' m HFS E9. unfold FSj, FSb, spill in *.
  destruct HFS as (S104 & S112 & Hbody & Hadd & HFI).
  assert (K : forall off v, (exists A, rg regs 9 A /\ q64 m (A + off) v) ->
                exists A, rg regs' 9 A /\ q64 m (A + off) v)
    by (intros off v (A & HA & Hq); exists A; split; [unfold rg in *; rewrite E9; exact HA | exact Hq]).
  exact (conj (K _ _ S104) (conj (K _ _ S112) (conj Hbody (conj Hadd HFI)))).
Qed.

Lemma ifs2_regs : forall g fr j regs regs' m, IFS2 g fr j regs m -> getr regs' 9 = getr regs 9 ->
  IFS2 g fr j regs' m.
Proof.
  intros g fr j regs regs' m H E9. unfold IFS2 in *. destruct H as (HI & HG & HS).
  split; [exact HI|]. split; [exact HG|]. exact (fsj_regs g fr j regs regs' m HS E9).
Qed.

Lemma ifs2_keep : forall g fr j A regs regs' m m' W, IFS2 g fr j regs m ->
  rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 -> munch W m m' -> meta_kept m m' ->
  (forall x, fr + 2688 <= x < fr + 2840 -> outside W x) ->
  (forall x, A + 104 <= x < A + 120 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x) ->
  IFS2 g fr j regs' m'.
Proof.
  intros g fr j A regs regs' m m' W H H9 HA0 HA E9 MU MK Hofr HoA Hob. unfold IFS2, IDb1, FGj, FGb in *.
  destruct H as ((HI & HIok) & (HG & HGok) & HS).
  split; [split; [|exact HIok]|].
  { eapply idbe_keep; [exact HI | apply ID1_length | exact MU |]. intros x Hx. apply Hofr. lia. }
  split; [split; [|exact HGok]|].
  { eapply fgbe_keep; [exact HG | apply t_FG_length | exact MU |]. intros x Hx. apply Hofr. lia. }
  eapply fsj_keep; [exact HS | exact H9 | exact HA0 | exact HA | exact E9 | exact MU | exact MK | exact HoA | exact Hob].
Qed.

(* PRO (push 13 group B, FLSH's prologue part; push 14D adds [A+184 / 256 / 264 / 272]; v1.9 adds [A + 32] =
   fr + 2880) crosses a run that keeps s1, misses the thirteen prologue spills [A+32, A+280), keeps the shadow map
   and misses the input block. *)
Lemma pro_keep : forall g fr A regs regs' m m' W, PRO g fr regs m ->
  rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 -> munch W m m' -> meta_kept m m' ->
  (forall x, A + 32 <= x < A + 280 -> outside W x) ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g -> outside W x) ->
  PRO g fr regs' m'.
Proof.
  intros g fr A regs regs' m m' W HP H9 HA0 HA E9 MU MK HoA HoIn. unfold PRO in *.
  destruct HP as (S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248 & Hour & Hin & Hg &
    S184 & S256 & S264 & S272 & S32).
  assert (K : forall off v, 32 <= off -> off + 8 <= 280 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    eapply spill_keep; [exact Hs | exact H9 | exact HA0 | exact HA | lia | lia | exact E9 | exact MU |].
    intros x Hx. apply HoA. lia. }
  split; [apply K; [lia | lia | exact S40]|].
  split; [apply K; [lia | lia | exact S120]|].
  split; [apply K; [lia | lia | exact S136]|].
  split; [apply K; [lia | lia | exact S160]|].
  split; [apply K; [lia | lia | exact S168]|].
  split; [apply K; [lia | lia | exact S176]|].
  split; [apply K; [lia | lia | exact S208]|].
  split; [apply K; [lia | lia | exact S248]|].
  split; [eapply addressable_kept; [exact Hour | exact MK]|].
  split.
  { eapply fl_bytes; [exact Hin | exact MU |]. intros x Hx. apply HoIn; unfold g_n, nlen in *; lia. }
  split.
  { intros Hn. destruct (Hg Hn) as (HIn & Had).
    split; [exact HIn | eapply addressable_kept; [exact Had | exact MK]]. }
  split; [apply K; [lia | lia | exact S184]|].
  split; [apply K; [lia | lia | exact S256]|].
  split; [apply K; [lia | lia | exact S264]|].
  split; [apply K; [lia | lia | exact S272]|].
  apply K; [lia | lia | exact S32].
Qed.

(* A spill names memory and register 9 only, so it moves with s1. *)
Lemma spill_r9 : forall regs regs' m off v,
  spill regs m off v -> getr regs' 9 = getr regs 9 -> spill regs' m off v.
Proof.
  intros regs regs' m off v (A & H9 & Hq) E9. exists A. split; [unfold rg in *; rewrite E9; exact H9 | exact Hq].
Qed.

Lemma pro_regs : forall g fr regs regs' m, PRO g fr regs m -> getr regs' 9 = getr regs 9 -> PRO g fr regs' m.
Proof.
  intros g fr regs regs' m HP E9. unfold PRO in *.
  destruct HP as (S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248 & Hour & Hin & Hg &
    S184 & S256 & S264 & S272 & S32).
  repeat (split; [eapply spill_r9; eassumption|]).
  split; [exact Hour|]. split; [exact Hin|]. split; [exact Hg|].
  repeat (split; [eapply spill_r9; eassumption|]).
  eapply spill_r9; eassumption.
Qed.

(* FLC (push 14D / 14E, in FLSI; v1.9 adds [A + 56] = fr + 2889 and [A + 48] = fr + 2890): the twelve
   loop-invariant spills [A+48, A+280) and the two record ranges (addressable, so decided by the shadow map) cross
   a run that keeps s1, misses those spills and keeps the shadow map. *)
Lemma flc_keep : forall fr A regs regs' m m' W, FLC fr regs m ->
  rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 -> munch W m m' -> meta_kept m m' ->
  (forall x, A + 48 <= x < A + 280 -> outside W x) ->
  FLC fr regs' m'.
Proof.
  intros fr A regs regs' m m' W HF H9 HA0 HA E9 MU MK HoA. unfold FLC in *.
  destruct HF as (S256 & S184 & S192 & S80 & S88 & S96 & S272 & S264 & Hfa & Hid & S72 & S64 & S56 & S48).
  assert (K : forall off v, 48 <= off -> off + 8 <= 280 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho0 Ho1 Hs.
    eapply spill_keep; [exact Hs | exact H9 | exact HA0 | exact HA | lia | lia | exact E9 | exact MU |].
    intros x Hx. apply HoA. lia. }
  split; [apply K; [lia | lia | exact S256]|].
  split; [apply K; [lia | lia | exact S184]|].
  split; [apply K; [lia | lia | exact S192]|].
  split; [apply K; [lia | lia | exact S80]|].
  split; [apply K; [lia | lia | exact S88]|].
  split; [apply K; [lia | lia | exact S96]|].
  split; [apply K; [lia | lia | exact S272]|].
  split; [apply K; [lia | lia | exact S264]|].
  split; [eapply addressable_kept; [exact Hfa | exact MK]|].
  split; [eapply addressable_kept; [exact Hid | exact MK]|].
  split; [apply K; [lia | lia | exact S72]|].
  split; [apply K; [lia | lia | exact S64]|].
  split; [apply K; [lia | lia | exact S56] | apply K; [lia | lia | exact S48]].
Qed.

Lemma flc_regs : forall fr regs regs' m, FLC fr regs m -> getr regs' 9 = getr regs 9 -> FLC fr regs' m.
Proof.
  intros fr regs regs' m HF E9. unfold FLC in *.
  destruct HF as (S256 & S184 & S192 & S80 & S88 & S96 & S272 & S264 & Hfa & Hid & S72 & S64 & S56 & S48).
  repeat (split; [eapply spill_r9; eassumption|]).
  split; [exact Hfa|]. split; [exact Hid|].
  repeat (split; [eapply spill_r9; eassumption|]).
  eapply spill_r9; eassumption.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ---- The Lib-level run lemma: the asan evt of the slot segment starts at the CUTST config (regs via mkR_of) and
   runs the Lib engine's step/call to a landing state satisfying K, lifting to SR Post through evt_SR_canon_lazy. *)
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

(* ---- The run 0x82138 -> 0x82150 (the call) -> 0x82154: three register moves, three spill loads and the jal;
   the callee contract's post lands at the return pc with a0 = fg_ret of the class. ---- *)
Lemma f13_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    reac_ctrl_identity_fragment_contract ->
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 f -> s7v = Z_to_bv 64 frg -> s2v = Z_to_bv 64 len ->
    0 <= f < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    rw_cells rsegs m (A + 256) [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)] ->
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
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7v s8 (Z_to_bv 64 f) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82154) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82138) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag HFRAG -> -> -> -> Hfb Hfrgb Hlenb Hpab Hppb Hpnb
    Hc256 Hsp16 Hstk Lg Lst Hfrg Hcond MI AC0 SW HHM HAE Haddrfrg Hcond2 HB1 HB2 HB3 HB4 HB5.
  do 7 step.
  eapply evt_cut.
  { unfold reac_ctrl_identity_fragment_contract, REAC_CTRL_IDENTITY_FRAGMENT in HFRAG.
    eapply HFRAG with (f := f) (fr := frg) (len := len) (pa := pa) (pp := pp) (pn := pn) (st := st) (g := gfrag).
    all: try assumption.
    all: try reflexivity. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI' & ST' & FGM & AC' & SW').
  subst ms2.
  replace (ret_pc (Z_to_bv 64 532820)) with (Z_to_bv 64 532820)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exists (Z_to_bv 64 532820), a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact FGM|]. split; [exact AC' | exact SW'].
Qed.

(* fg_mem is a conjunction of bytes_at, so it crosses MemNorm.mem_rel in both directions. *)
Lemma fg_mem_back : forall f pa pp pn st g c m m0, mem_rel rsegs m m0 ->
  fg_mem f pa pp pn st g c m0 -> fg_mem f pa pp pn st g c m.
Proof.
  intros f pa pp pn st g c m m0 REL H. destruct c; cbn [fg_mem] in H |- *; try exact I;
    try (exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) H)).
  destruct H as (H1 & H2 & H3 & H4).
  split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) H1)|].
  split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) H2)|].
  split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) H3)
        | exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) H4)].
Qed.

(* The same run on the memory the cut carries: FRA holds ro_agree, not mem_inv (push 5b), and every premise of
   f13_evt is a bytes_at / addressable / stk / rw_cells / wr_at fact that crosses MemNorm.mem_rel to the
   normalized memory (which has mem_inv by construction); the post comes back across mem_rel / ro_same.  The
   five pointers and the callee's window lie above 6283264, so no address the run writes or reads is read-only. *)
Lemma f13_evt_ro :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    reac_ctrl_identity_fragment_contract ->
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 f -> s7v = Z_to_bv 64 frg -> s2v = Z_to_bv 64 len ->
    6283264 <= f -> f + 72 < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    6283264 <= pa -> pa + 2 < 2 ^ 64 -> 6283264 <= pp -> pp + 8 < 2 ^ 64 ->
    6283264 <= pn -> pn + 8 < 2 ^ 64 -> 6283264 <= A -> A + 312 <= 2 ^ 64 ->
    rw_cells rsegs m (A + 256) [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)] ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length gfrag = 50%nat -> length st = 72%nat ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m frg gfrag) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
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
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7v s8 (Z_to_bv 64 f) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82154) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82138) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2 Hflo Hfhi Hfrgb Hlenb Hpalo Hpahi Hpplo Hpphi
    Hpnlo Hpnhi HAlo HAhi Hc256 Hsp16 Hstk Lg Lst Hfrg Hcond HRO AC0 SW HHM HAE Haddrfrg Hcond2
    HB1 HB2 HB3 HB4 HB5.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hsplo : 6283264 <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K)
    by (unfold HIGHMEM_BEG in HHM; lia).
  assert (Hsphi : bv_unsigned sp <= 2 ^ 64) by (unfold APPMEM_END in HAE; lia).
  assert (Hro256 : forall i, 0 <= i < Z.of_nat (cells_size
              [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)]) ->
            ro_addr rsegs (wa (A + 256 + i)) = false).
  { intros i Hi.
    change (Z.of_nat (cells_size [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)]))
      with 24 in Hi.
    apply RoAdapt.ro_addr_false_hi. lia. }
  assert (Hrof72 : forall i, 0 <= i < Z.of_nat (cells_size [CB 72 st]) ->
            ro_addr rsegs (wa (f + i)) = false).
  { intros i Hi. change (Z.of_nat (cells_size [CB 72 st])) with 72 in Hi.
    apply RoAdapt.ro_addr_false_hi. lia. }
  assert (Hrostk : forall x, bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K <= x < bv_unsigned sp ->
            ro_addr rsegs (wa x) = false)
    by (intros x Hx; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropa : forall i, 0 <= i < 2 -> ro_addr rsegs (wa (pa + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropp : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (pp + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropn : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (pn + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  pose proof (f13_evt ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11
    t3 t4 t5 t6 Fr fc (normalize rsegs m) A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2
    ltac:(lia) Hfrgb Hlenb ltac:(lia) ltac:(lia) ltac:(lia)
    (RoAdapt.rel_rw_norm m _ (A + 256) _ REL Hro256 Hc256)
    Hsp16
    (RoAdapt.rel_stk_norm m _ _ _ REL Hrostk Hstk)
    Lg Lst
    ltac:(intros H1 H2 H3 H4 H5 H6; exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) (Hfrg H1 H2 H3 H4 H5 H6)))
    ltac:(intros H1 H2 H3 H4 H5;
          destruct (Hcond H1 H2 H3 H4 H5) as (Hrw & Ha2 & Ha8 & Ha8' & Hw2 & Hw8 & Hw8' & Hdj);
          split; [exact (RoAdapt.rel_rw_norm m _ f _ REL Hrof72 Hrw)|];
          split; [exact Ha2|]; split; [exact Ha8|]; split; [exact Ha8'|];
          split; [exact (wr_at_norm rsegs m _ pa 2 REL Hw2 Hropa)|];
          split; [exact (wr_at_norm rsegs m _ pp 8 REL Hw8 Hropp)|];
          split; [exact (wr_at_norm rsegs m _ pn 8 REL Hw8' Hropn)|];
          exact Hdj)
    (mem_inv_normalize rsegs m) (RoAdapt.rel_ac_norm m _ REL AC0) (RoAdapt.rel_sw_norm m _ REL SW)
    HHM HAE
    ltac:(intros H1 H2 H3 H4 H5 H6; exact (RoAdapt.rel_addr_norm m _ _ _ REL (Haddrfrg H1 H2 H3 H4 H5 H6)))
    ltac:(intros H1 H2 H3 H4 H5; destruct (Hcond2 H1 H2 H3 H4 H5) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6);
          split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q1)|];
          split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q2)|];
          split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q3)|];
          split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q4)|];
          split; [exact Q5 | exact Q6])
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB1) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB2)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB3) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB4)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB5)) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply evt_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & FGM & AC' & SW') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact (RoAdapt.rel_stk_back memX m0' _ _ Hmr ST')|].
  split; [exact (fg_mem_back f pa pp pn st gfrag _ memX m0' Hmr FGM)|].
  split; [exact (RoAdapt.rel_ac_back memX m0' Hmr AC') | exact (RoAdapt.rel_sw_back memX m0' Hmr SW')].
Qed.

(* ---- seg_F13 : the entry cut Inv_A82138_at (0x82138, pre-call) to the exit cut Inv_A82154_at (0x82154,
   post-call), both SlotInv's (aslot push 11B). ---- *)
Lemma seg_F13 : reac_ctrl_identity_fragment_contract ->
  forall j : nat, Hat B APIf ra (Inv_A82154_at B APIf ra) j -> Hat B APIf ra (Inv_A82138_at B APIf ra) j.
Proof.
  intros HFRAG j Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK &
    A & v280 & H9 & H25 & HAb & Hv280b & Hv280s &
    Hc256 & Hrwf & Haf & Hapa & Happ8 & Hapn & HAC0 & HSW0 &
    HB1 & HB2 & HB3 & HB4 & HB5 &
    H184 & H208 & H280 & HbL & HaL & H64 & H72 & H80 & H272 & H264 & HCAR & HIFS1).
  pose proof HCAR as HCAR0. unfold F16CARRY, F17CARRY in HCAR0.
  destruct HCAR0 as (_ & _ & _ & _ & _ & H23 & _ & _ & H18 & _ & _ & _ & _ & _ & _ & _ & _ & HC50 & _).
  assert (Hlong : 50 <= flen g j -> bytes_at rsegs mem phi (t_g (g_in g) j))
    by (intros Hl; destruct (HC50 Hl) as (_ & Hgb & _); exact Hgb).
  subst c. rewrite SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (Hplace & HfrA & Hfsmeta & Hfrwr).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hselq & Hfr24q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HA2b : 0 <= A2 < 2 ^ 64) by lia.
  assert (HA2 : A2 = A).
  { assert (E : Z_to_bv 64 A2 = Z_to_bv 64 A) by (unfold rg in *; rewrite <- Hr9; exact H9).
    apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !MState.unsigned_lit in E by lia. exact E. }
  subst A2.
  assert (HSPu : bv_unsigned (getr regs 2) = AC.aspZ regs) by (unfold AC.aspZ; reflexivity).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)).
  (* placement of the frame against the callee's stack window, and of the spill area *)
  assert (HK : 0 <= REAC_CTRL_IDENTITY_FRAGMENT_K <= FN_STACK)
    by (unfold REAC_CTRL_IDENTITY_FRAGMENT_K; lia).
  pose proof (Hplace REAC_CTRL_IDENTITY_FRAGMENT_K HK) as Hfrsep.
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in H9; rewrite H9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HfrA.
  assert (HaspH : HIGHMEM_BEG <= AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K)
    by (unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia).
  assert (HaspE : AC.aspZ regs <= APPMEM_END) by lia.
  (* the frame body is app memory above AC.GT, on both arms *)
  assert (Hframe : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - intros a Ha. destruct (Hreal a Ha) as (Hlo2 & Hhi2).
      split; [right; unfold APPMEM_END, HIGHMEM_BEG in *; lia | unfold AC.GT, HIGHMEM_BEG in *; lia].
    - intros a Ha. destruct (Hfs a Ha) as (FSa & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (lw_fs_place (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSa HAH Hw
                  HFSr) as LWr1.
      pose proof (lwf_gt _ _ _ _ LWr1) as HG.
      pose proof (lwf_end _ _ _ _ LWr1) as Hend.
      pose proof (lwf_app _ _ _ _ LWr1) as Happ2.
      split; [exact (Happ2 a ltac:(lia)) | lia]. }
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; apply (Hframe a Ha)).
  assert (HGT : AC.GT <= fr) by (apply (Hframe fr ltac:(lia))).
  assert (Hfrb : 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
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
    by (destruct HHB as (_ & H1 & _ & H3 & _); unfold AC.a_size, APPMEM_END in *; lia).
  assert (Hlenb : 0 <= flen g j < 2 ^ 64)
    by (unfold flen in *; pose proof (flen_small (g_in g) j); pose proof (flen_nonneg (g_in g) j); lia).
  (* the record block [phi, phi + a_size len) lies below stklo and outside the side stack (the block law of the
     heap list), so [phi, phi + 50) is apart from the frame (real arm: sp = fr, a megabyte above stklo; side arm:
     fr is 36864 bytes into FS and phi is not in FS) and from the callee's window (above S - 4096 - K). *)
  pose proof (lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH
              ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity)) as LWr2.
  pose proof (lwb_end _ _ _ _ _ _ LWr2) as Hblkend.
  pose proof (lwb_byte_not_fs _ _ _ _ _ _ LWr2) as Hblk.
  assert (Hasz : 1 <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hphifr : phi + 50 <= fr \/ fr + FRAME_BYTES <= phi).
  { destruct Hloc as [[_ [Hspfr _]]|[_ [Hfsgap [Hfs _]]]].
    - left. lia.
    - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
      pose proof (Hfsgap FSc HwFSc HFScr) as Hgap.
      destruct (Z_lt_le_dec phi FSc) as [Hlt|Hge]; [left; lia|].
      destruct (Z_lt_le_dec phi (FSc + AC.FS_SIZE)) as [Hin|Hout]; [|right; lia].
      exfalso. pose proof (Hblk phi ltac:(lia)) as Hnfs.
      apply Hnfs. unfold AC.a_in_fs. exists FSc. split; [exact HFScr|]. split; [exact HwFSc | lia]. }
  assert (Hphisep : phi + 50 <= AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= phi)
    by (left; unfold REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia).
  assert (Haphi : 50 <= flen g j -> addressable mem phi 50).
  { intros Hl. destruct HHB as (_ & Hadd). rewrite <- (Z.add_0_r phi).
    eapply addressable_sub; [exact Hadd | lia | lia | unfold AC.a_size; lia]. }
  assert (Hwr : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> 0 <= n -> wr_at rsegs mem a n).
  { intros a n Ha Hn Hn0. split; [unfold AC.GT in *; lia|].
    split; [pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Hap;
            unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; lia|].
    intros i Hi. exact (Hfrwr (a + i) ltac:(lia)). }
  (* run the segment *)
  apply (sl_run_lib regs (Z_to_bv 64 0x82138) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82154 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 20 = getr regs 20 /\
       getr R0 10 = Z_to_bv 64 (fg_ret (frcl g j fr phi)) /\
       munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                (AC.aspZ regs) (frcl g j fr phi)) mem mem' /\
       wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K) (AC.aspZ regs) /\
       fg_mem (fragb fr) (fr + 256) (fr + 272) (fr + 304) (t_FG (g_in g) j) (t_g (g_in g) j)
         (frcl g j fr phi) mem' /\
       asan_cells mem' /\ shadow_rw mem')
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f13_evt_ro with (A := A) (f := fragb fr) (frg := phi) (len := flen g j)
        (pa := fr + 256) (pp := fr + 272) (pn := fr + 304)
        (st := t_FG (g_in g) j) (gfrag := t_g (g_in g) j).
      - exact HFRAG.
      - unfold rg in H9; exact H9.
      - unfold rg in H25; exact H25.
      - unfold rg in H23; exact H23.
      - unfold rg in H18; exact H18.
      - unfold fragb, AC.GT in *; lia.
      - unfold fragb in *; lia.
      - exact Hphib.
      - exact Hlenb.
      - unfold AC.GT in *; lia.
      - lia.
      - unfold AC.GT in *; lia.
      - lia.
      - unfold AC.GT in *; lia.
      - lia.
      - unfold AC.GT in *; lia.
      - unfold APPMEM_END in *; lia.
      - exact Hc256.
      - fold_sp regs. rewrite Haspz. exact Hspm.
      - fold_sp regs. exact Hstkcall.
      - apply t_g_length.
      - apply t_FG_length.
      - intros _ _ _ _ _ Hl. exact (Hlong Hl).
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
                  & E & MU & WM & RO' & ST' & FGM & AC' & SW').
      eexists _, (Z_to_bv 64 0x82154), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [unfold rg in H9; rewrite H9; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [unfold frcl; reflexivity|].
      match type of ST' with context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST' end.
      split; [unfold frcl; exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST'|].
      split; [unfold frcl; exact FGM|]. split; [exact AC' | exact SW']. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er18 & Er22 & Er23 &
      Er24 & Er20 & Er10 &
      MU & WM & HroM & ST' & FGM & AC' & SW') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
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
        destruct Hrwf as ((_wff & Hbf) & _wrf).
        cbn [cells_bytes cbytes] in Hbf. rewrite app_nil_r in Hbf.
        eapply fl_bytes; [exact Hbf | exact MU |].
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
    (* AH and stklo across the call's store, by arm *)
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
    { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs HFSREC]]]].
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
        pose proof (lw_store (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH Hmc
                    Hwmon) as LWr3.
        pose proof (lws_ah _ _ _ _ _ LWr3) as HAH2.
        pose proof (lws_own _ _ _ _ _ LWr3) as Hown2.
        pose proof (lws_lo _ _ _ _ _ LWr3) as Hstk2.
        pose proof (lws_hi _ _ _ _ _ LWr3) as Hhi2.
        split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2].
      - (* side arm: the frame body is inside the FakeStack, the callee window is a_store_ok *)
        destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
        pose proof (lw_fs_place (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSc HAH
                    HwFSc HFScr) as LWr4.
        pose proof (lwf_gt _ _ _ _ LWr4) as HFSgt.
        pose proof (lwf_end _ _ _ _ LWr4) as HFSend.
        pose proof (lwf_app _ _ _ _ LWr4) as HFSapp.
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
    assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
    { intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
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
    (* rebuild FRA at mem' (Tac_slot.sl_fr_cl), then move it to regs' / md' *)
    assert (HSTKW : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (stk_keep (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) mem mem' (g_S g - AF.SLOT_STACK) (g_S g));
        [exact Hwin | exact MU | exact WM |].
      intros x Hx Ho. exact (Hrdpost x Ho). }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem' md).
    { apply (Tac_slot.sl_fr_cl B APIf ra empty FF g fr (hb1 phi (AC.a_size (flen g j))) regs regs mem mem' md _
               HFRA MU WM HroM Hallapp Hrtdj HAH' HSTK'); try reflexivity.
      - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, AC.GT, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *; lia.
      - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia.
      - intros A' HA' HA'b x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        assert (EA' : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in H9; rewrite <- HA'; exact H9).
          apply (f_equal (bv_unsigned (n := 64))) in E.
          rewrite !MState.unsigned_lit in E by lia. exact E. }
        subst A'.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia.
      - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia.
      - intros x Hx. apply Hshout, HshIS, Hx.
      - intros A' HA' HA'b x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        assert (EA' : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in H9; rewrite <- HA'; exact H9).
          apply (f_equal (bv_unsigned (n := 64))) in E.
          rewrite !MState.unsigned_lit in E by lia. exact E. }
        subst A'.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia.
      - exact HSTKW.
      - intros HR. eapply Tac_slot.fsrec_munch_lo; [exact HR | exact HAH | exact MU | |].
        + intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
            unfold fragb, AC.GT, REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG in *; lia.
        + intros x Hxa Hxf Hxs. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
            unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K, AC.aspZ in *; lia. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem' md md' HFRA');
        [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
    (* ENT: the fragment call wrote only cells of the frame and its own stack window inside the slot window, so
       no byte the entry relation speaks of changed; then the model step of sl_run_lib. *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x \/
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/
              (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
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
    { apply (Tac_slot.ent_store B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem' md _ HENT HFRA MU
               HWcases
               HSTK' HSTKH').
      intros a Hia Ho. exact (proj2 (Hown' a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem' md md' HENT' Hmat). }
    assert (Hmeta : meta_kept mem mem') by (apply (munch_meta _ mem mem' MU Hallapp)).
    (* "outside the write set" for the data above / below the frame *)
    assert (Hout : forall x, (x < fr \/ fr + FRAME_BYTES <= x) ->
              (x < AC.aspZ regs - REAC_CTRL_IDENTITY_FRAGMENT_K \/ AC.aspZ regs <= x) ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros x H1 H2. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
      destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb in *; lia. }
    assert (HoutA : forall x, A + 32 <= x < A + 312 ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros x Hx. apply Hout; [right; lia | right; unfold AC.aspZ in *; lia]. }
    (* a live block of the heap list ends below stklo and is off the side stack, so it is clear of the write
       set: on the real arm the frame starts at stklo or above (sp = fr), on the side arm the frame is in FS;
       and the callee's window is above S - 8752, a megabyte above stklo. *)
    assert (Hblkout : forall q n x, In (q, n) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) -> q <= x < q + n ->
              outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                         (AC.aspZ regs) (frcl g j fr phi)) x).
    { intros q n x Hin Hx.
      pose proof (lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md q n HAH Hin) as LWr5.
      pose proof (lwb_end _ _ _ _ _ _ LWr5) as Hend.
      pose proof (lwb_byte_not_fs _ _ _ _ _ _ LWr5) as Hb.
      apply Hout.
      - destruct Hloc as [[_ [Hspfr Hreal]]|[_ [Hfsgap [Hfs _]]]].
        + pose proof (Hreal fr ltac:(lia)) as (Hs1 & _). left. lia.
        + destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
          pose proof (Hfsgap FSc HwFSc HFScr) as Hgap.
          destruct (Z_lt_le_dec x FSc) as [Hlt|Hge]; [left; lia|].
          destruct (Z_lt_le_dec x (FSc + AC.FS_SIZE)) as [Hin2|Hout2]; [|right; lia].
          exfalso. pose proof (Hb x ltac:(lia)) as Hnfs.
          apply Hnfs. unfold AC.a_in_fs. exists FSc. split; [exact HFScr|]. split; [exact HwFSc | lia].
      - left. unfold REAC_CTRL_IDENTITY_FRAGMENT_K, AC.aspZ in *. lia. }
    assert (HIexit : Inv_A82154_at B APIf ra g j (mkCfg (mkst regs' (Z_to_bv 64 0x82154) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hj|].
      split.
      { destruct HHB as (Hphinz2 & Hphiad). split; [exact Hphinz2|].
        eapply Tac_slot.sl_addr_keep; [exact Hphiad | exact MU | exact Hallapp]. }
      split.
      { destruct HFLSI as ((HPRO & F128 & Fstk & F144 & Fid17) & F216 & F224 & F248 & (Fin1 & Fin2 & Fin3) &
          HFLC).
        assert (Hsp : forall off v, 32 <= off -> off + 8 <= 312 -> spill regs mem off v ->
                  spill regs' mem' off v).
        { intros off v Ho1 Ho2 Hs. eapply spill_keep;
            [exact Hs | exact H9 | lia | unfold APPMEM_END in *; lia | lia | lia | exact Fr9 | exact MU |].
          intros x Hx. apply HoutA. lia. }
        split.
        { split.
          { eapply pro_keep; [exact HPRO | exact H9 | lia | unfold APPMEM_END in *; lia | exact Fr9 | exact MU
                             | exact Hmeta | |].
            - intros x Hx. apply HoutA. lia.
            - intros Hn x Hx. apply (Hblkout (g_p g) (g_n g) x); [|exact Hx].
              apply in_or_app. right. apply Fin1. exact Hn. }
          split; [apply Hsp; [lia | lia | exact F128]|].
          split.
          { apply (stk_keep (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fragb fr) (fr + 256) (fr + 272) (fr + 304)
                               (AC.aspZ regs) (frcl g j fr phi)) mem mem' fr (fr + FRAME_BYTES));
              [exact Fstk | exact MU | exact WM |].
            intros x Hx Ho. exact (Hrdpost x Ho). }
          split; [apply Hsp; [lia | lia | exact F144]|].
          eapply addressable_kept; [exact Fid17 | exact Hmeta]. }
        split; [apply Hsp; [lia | lia | exact F216]|].
        split; [apply Hsp; [lia | lia | exact F224]|].
        split; [apply Hsp; [lia | lia | exact F248]|].
        split.
        { split; [exact Fin1|].
          split; [eapply addressable_kept; [exact Fin2 | exact Hmeta]|].
          eapply fl_bytes; [exact Fin3 | exact MU |].
          intros x Hx. apply (Hblkout (g_p g) (g_n g) x); [|unfold g_n, nlen; lia].
          apply in_or_app. right. apply Fin1. unfold g_n, nlen in *. lia. }
        (* push 14D / 14E: FLC *)
        eapply flc_keep; [exact HFLC | exact H9 | lia | unfold APPMEM_END in *; lia | exact Fr9 | exact MU
                         | exact Hmeta |].
        intros x Hx. apply HoutA. lia. }
      split.
      { destruct HLK as (Hj' & Hs5j & HOURb). split; [exact Hj'|]. split.
        - unfold rg in *. rewrite Fr21. exact Hs5j.
        - unfold OURb in *. eapply fl_bytes; [exact HOURb | exact MU |].
          rewrite OUR_length. intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb in *; lia. }
      exists A, v280.
      split; [unfold rg; rewrite Fr9; unfold rg in H9; exact H9|].
      split; [unfold rg; exact Fr10|].
      split; [exact HAb|].
      split; [exact Hv280b|].
      split; [exact Hv280s|].
      split; [exact Hphifr|].
      split; [rewrite HaspEq; exact Hphisep|].
      split.
      { unfold q64 in *. eapply fl_bytes; [exact H184 | exact MU |].
        rewrite length_le8. intros x Hx. apply HoutA. lia. }
      split.
      { unfold q64 in *. eapply fl_bytes; [exact H208 | exact MU |].
        rewrite length_le8. intros x Hx. apply HoutA. lia. }
      split.
      { unfold q64 in *. eapply fl_bytes; [exact H280 | exact MU |].
        rewrite length_le8. intros x Hx. apply HoutA. lia. }
      split.
      { eapply fl_bytes; [exact HbL | exact MU |].
        rewrite t_FG_length. intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb in *; lia. }
      split; [eapply addressable_kept; [exact HaL | exact Hmeta]|].
      split; [exact Hrec|].
      split; [eapply addressable_kept; [exact Haf | exact Hmeta]|].
      split.
      { eapply fl_bytes; [exact HB1 | exact MU |]. rewrite length_le8. intros x Hx.
        apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAL_BCMP, AC.GT, HIGHMEM_BEG, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
      split.
      { eapply fl_bytes; [exact HB2 | exact MU |]. rewrite length_le8. intros x Hx.
        apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, REAL_MEMCMP, AC.GT, HIGHMEM_BEG, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
      split.
      { eapply fl_bytes; [exact HB3 | exact MU |]. rewrite length_le8. intros x Hx.
        apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, GOT_CF, AC.GT, HIGHMEM_BEG, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
      split.
      { eapply fl_bytes; [exact HB4 | exact MU |]. cbn [length]. intros x Hx.
        apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, CF, AC.GT, HIGHMEM_BEG, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
      split.
      { eapply fl_bytes; [exact HB5 | exact MU |]. cbn [length]. intros x Hx.
        apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]];
          unfold fragb, CF, AC.GT, HIGHMEM_BEG, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
      split; [exact AC'|].
      split; [exact SW'|].
      split.
      { eapply rw_cells_transport; [exact Hc256 | exact MU | exact WM |].
        change (Z.of_nat (cells_size [C8 (Z_to_bv 64 (fr + 256)); C8 (Z_to_bv 64 (fr + 304));
                                      C8 (Z_to_bv 64 (fr + 272))])) with 24.
        unfold fragb, AC.aspZ in *.
        destruct (frcl g j fr phi); cbn [fg_fp disjoint_from]; repeat split; first [right; lia | exact I]. }
      split.
      { unfold q64 in *. eapply fl_bytes; [exact H64 | exact MU |].
        rewrite length_le8. intros x Hx. apply HoutA. lia. }
      split.
      { unfold q64 in *. eapply fl_bytes; [exact H72 | exact MU |].
        rewrite length_le8. intros x Hx. apply HoutA. lia. }
      split.
      { unfold q64 in *. eapply fl_bytes; [exact H80 | exact MU |].
        rewrite length_le8. intros x Hx. apply HoutA. lia. }
      split.
      { unfold q64 in *. eapply fl_bytes; [exact H272 | exact MU |].
        rewrite length_le8. intros x Hx. apply HoutA. lia. }
      split.
      { unfold q64 in *. eapply fl_bytes; [exact H264 | exact MU |].
        rewrite length_le8. intros x Hx. apply HoutA. lia. }
      split; [exact FGM|].
      split.
      { eapply f16carry_keep; [exact HCAR | exact MU | exact Hallapp | exact H9 | lia | lia
                               | unfold APPMEM_END in *; lia
                               | exact Fr9 | exact Fr18 | exact Fr20 | exact Fr22 | exact Fr23 | exact Fr24
                               | exact HoutA | | | |].
        - intros Hl x Hx. apply (Hblkout phi (AC.a_size (flen g j)) x);
            [apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity | unfold AC.a_size; lia].
        - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia.
        - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia.
        - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
          destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
      (* push 12: IFS2 at 0x82154. The identity record (ID1 g j) and the first-fragment state (v1.9: the spills
         [A+104 / 112] and the body at fr + 2880) lie outside the call's write set; the fragment record is the
         call's post bytes frrec, which are t_FGf j = t_FG (S j) on every arm (frcl = fcls), and frag_ok moves to
         t_FG (S j) by frag_ok_fg_st. *)
      unfold IFS1, IDb1, FGj, FGb in HIFS1.
      destruct HIFS1 as ((HId1 & HidOK) & (_ & HfOK) & HFSj).
      unfold IFS2, IDb1, FGj, FGb.
      split; [split; [|exact HidOK]|].
      { eapply idbe_keep; [exact HId1 | apply ID1_length | exact MU |].
        intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
      rewrite t_FG_S.
      split; [split|].
      { unfold FGBe. rewrite <- (frrec_FGf g j fr phi)
          by solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia].
        exact Hrec. }
      { unfold t_FGf. apply frag_ok_fg_st; [exact HfOK | apply t_FG_length | apply t_g_length]. }
      eapply fsj_keep; [exact HFSj | exact H9 | lia | unfold APPMEM_END in *; lia | exact Fr9 | exact MU
                       | exact Hmeta | |].
      - intros x Hx. apply HoutA. lia.
      - intros x Hx. apply (fp_outside_of _ _ _ _ _ _ (frcl g j fr phi)). intros Hin.
        destruct Hin as [Hf|[Hpa2|[Hpp2|[Hpn2|Hstk2]]]]; unfold fragb, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
