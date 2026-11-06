(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): the memory kit of its inner
   walk (Prog/Seg/M02D.v). The pieces carry one fact about memory from call to call, M02_inv S m0 m (written only
   inside M02_W S since m0, writability kept, mem_inv, MemNorm.task_mem); these lemmas step it across a callee's
   post (m02_inv_step) and read every fact of M02_mem back at m: the two blocks' states (c and m lie below the
   window), the stack-protector cells and the cap cell (outside M02_W), the stack window (present: it lies above
   Tac_slot.SL_TOP, where a writable byte is present), the callee stack regions (stack_ok) and free cells of main's
   frame (rw_cells).
   Part of the proof of LLVMFuzzerTestOneInput: a kit of segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (segment lemma). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot M02D.
Import ListNotations.
Open Scope Z_scope.

Lemma m02_TASK_SIZE : TASK_SIZE = 2 ^ 47.
Proof. reflexivity. Qed.

Lemma m02_inv_refl : forall S c mm cap rc mc m0, M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m0.
Proof.
  intros S c mm cap rc mc m0 (HMI & HTM & _).
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HMI | exact HTM].
Qed.

(* A callee's post: it wrote only inside W, which lies inside M02_W S and below TASK_SIZE. *)
Lemma m02_inv_step : forall S m0 m m' W, M02_inv S m0 m -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  sub_fp W (M02_W S) -> (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> x < 2 ^ 47) -> M02_inv S m0 m'.
Proof.
  intros S m0 m m' W (MU & WM & _ & HTM) MU' WM' HMI' Hsub Hlow.
  split; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ Hsub MU'))|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact HMI'|].
  intros a b E.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra.
  destruct (sl_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU' a O) in E. exact (HTM a b E).
  - right. rewrite m02_TASK_SIZE. exact (Hlow _ Ra O).
Qed.

(* The same, for a post that gives MemNorm.task_mem itself (snprintf's printf_post). *)
Lemma m02_inv_step_tm : forall S m0 m m' W, M02_inv S m0 m -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  MemNorm.task_mem rsegs m' -> sub_fp W (M02_W S) -> M02_inv S m0 m'.
Proof.
  intros S m0 m m' W (MU & WM & _ & _) MU' WM' HMI' HTM' Hsub.
  split; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ Hsub MU'))|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact HMI' | exact HTM'].
Qed.

(* A callee's post that wrote its frames [sp - d, sp), sp = S - 208. *)
Lemma m02_inv_call : forall S m0 m m' d (wsp : word),
  munch [(bv_unsigned wsp - d, bv_unsigned wsp)] m m' -> M02_inv S m0 m -> wsp = Z_to_bv 64 (S - 208) ->
  wmono rsegs m m' -> mem_inv rsegs m' -> 0 <= d <= 65536 - 208 -> 0x60000 <= S - 65536 -> S <= 2 ^ 47 ->
  M02_inv S m0 m'.
Proof.
  intros S m0 m m' d wsp MU HI -> WM MI Hd HT H47.
  rewrite unsigned_lit in MU by lia.
  apply (m02_inv_step S m0 m m' _ HI MU WM MI).
  - intros x Hx. unfold M02_W, M02_FRAME in Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & X2 & _).
    split; [lia | exact I].
  - intros x Rx O. cbn [outside] in O. apply Z.nle_gt. intros C. apply O. split; [lia | exact I].
Qed.

(* A callee's post that wrote nothing. *)
Lemma m02_inv_nil : forall S m0 m m', munch [] m m' -> M02_inv S m0 m -> wmono rsegs m m' -> mem_inv rsegs m' ->
  M02_inv S m0 m'.
Proof.
  intros S m0 m m' MU HI WM MI. apply (m02_inv_step S m0 m m' [] HI MU WM MI).
  - intros x _. exact I.
  - intros x _ O. exfalso. apply O. exact I.
Qed.

(* `blt` / `bge` of two values in [0, 2^63): the signed compare is the compare of the values. *)
Lemma m02_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed. rewrite !unsigned_lit by lia.
  destruct (Z.ltb_spec x (2 ^ 63)); [|lia]. destruct (Z.ltb_spec y (2 ^ 63)); [|lia]. reflexivity.
Qed.

(* A load of the bytes at a, whole, as 4 or as 8 bytes. *)
Lemma m02_rd : forall segs m a bs, bytes_at segs m a bs -> ov_read_bytes segs m (wa a) (length bs) = Some bs.
Proof.
  intros segs m a bs H.
  pose proof (bytes_at_ov_read segs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [Z.of_nat skipn] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma m02_rd4 : forall segs m a v, bytes_at segs m a (le4 v) -> ov_read_bytes segs m (wa a) 4 = Some (le4 v).
Proof. intros segs m a v H. pose proof (m02_rd segs m a _ H) as R. rewrite length_le4 in R. exact R. Qed.

Lemma m02_rd8 : forall segs m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (wa a) 8 = Some (le8 v).
Proof. intros segs m a v H. pose proof (m02_rd segs m a _ H) as R. rewrite length_le8 in R. exact R. Qed.

Section K.
Variables (S c mm cap : Z) (rc : rconf) (mc : mconf) (m0 m : word -> option byte).
Hypothesis HM : M02_mem S c mm cap rc mc m0.
Hypothesis HI : M02_inv S m0 m.

Lemma m02_mem_inv : mem_inv rsegs m.
Proof. exact (proj1 (proj2 (proj2 HI))). Qed.

Lemma m02_task_mem : MemNorm.task_mem rsegs m.
Proof. exact (proj2 (proj2 (proj2 HI))). Qed.

Lemma m02_bnds : S mod 16 = 0 /\ 0x60000 <= S - 65536 /\ S <= 2 ^ 47 /\
  0 < c /\ c mod 16 = 0 /\ c + SEG_C_SIZE <= S - 65536 /\ 0 < mm /\ mm mod 16 = 0 /\ mm + SEG_M_SIZE <= S - 65536.
Proof.
  destruct HM as (_ & _ & _ & H16 & HT & H47 & _ & _ & _ & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm & _).
  repeat split; assumption.
Qed.

Lemma m02_rom : forall a, S - 65536 <= a < S -> seg_rom rsegs (wa a) = None.
Proof. destruct HM as (_ & _ & _ & _ & _ & _ & _ & HR & _). exact HR. Qed.

(* A fact of m0 on bytes outside M02_W S holds at m. *)
Lemma m02_keep : forall a bs, bytes_at rsegs m0 a bs -> disjoint_from (M02_W S) a (Z.of_nat (length bs)) ->
  bytes_at rsegs m a bs.
Proof. intros a bs H Hd. exact (bytes_at_transport rsegs _ _ _ _ _ H (proj1 HI) Hd). Qed.

Lemma m02_rconf : rconf_at rsegs m c rc.
Proof.
  pose proof m02_bnds as (_ & _ & _ & Hc0 & _ & Hc & _).
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (bs & HB & HE) & _).
  exists bs. split; [|exact HE]. apply m02_keep; [exact HB|].
  rewrite (proj1 HE). unfold M02_W, M02_FRAME, SEG_C_SIZE in *. cbn [disjoint_from]. repeat split; lia.
Qed.

Lemma m02_mconf : mconf_at rsegs m mm mc.
Proof.
  pose proof m02_bnds as (_ & _ & _ & _ & _ & _ & Hm0 & _ & Hm).
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (bs & HB & HE)).
  exists bs. split; [|exact HE]. apply m02_keep; [exact HB|].
  rewrite (proj1 HE). unfold M02_W, M02_FRAME, SEG_M_SIZE in *. cbn [disjoint_from]. repeat split; lia.
Qed.

Lemma m02_ssp : ssp_ok m.
Proof.
  pose proof m02_bnds as (_ & HT & _).
  destruct HM as (_ & _ & (HG & g & HGd) & _).
  split; [|exists g]; apply m02_keep; try assumption; rewrite length_le8; unfold M02_W, M02_FRAME;
    cbn [disjoint_from sa_got_guard sa_guard SA SEG_PLAIN]; repeat split; lia.
Qed.

Lemma m02_cap : bytes_at rsegs m (S - M02_FRAME + 0x18) (le8 (Z_to_bv 64 cap)).
Proof.
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & HC & _).
  apply m02_keep; [exact HC|]. rewrite length_le8. unfold M02_W, M02_FRAME. cbn [disjoint_from]. repeat split; lia.
Qed.

(* The stack window stays present: it lies above SL_TOP, where every writable byte is present. *)
Lemma m02_stk : stk rsegs m (S - 65536) S.
Proof.
  pose proof m02_bnds as (_ & HT & H47 & _).
  destruct HM as (_ & _ & _ & _ & _ & _ & (_ & _ & HST) & _).
  apply sl_stk_of_writable; [unfold SL_TOP; lia | lia |].
  intros a Ha. unfold writable_at. apply (proj1 (proj2 HI)). exact (proj1 (HST a Ha)).
Qed.

(* The stack region a callee of main (sp = S - 208) uses. *)
Lemma m02_stack_ok : forall depth, 0 <= depth <= 65536 - M02_FRAME ->
  stack_ok rsegs m (S - 65536) (S - M02_FRAME) depth.
Proof.
  intros depth Hd. pose proof m02_bnds as (H16 & _).
  split; [exact (proj1 (stk_split rsegs m _ (S - M02_FRAME) _ m02_stk ltac:(unfold M02_FRAME; lia)))|].
  split; [unfold M02_FRAME in *; lia|]. split; [unfold M02_FRAME; Z.div_mod_to_equations; lia|].
  intros a Ha. apply m02_rom. unfold M02_FRAME in *. lia.
Qed.

(* Cells of main's own frame (or of the window) the walk stores to or reads. *)
Lemma m02_cells : forall a n, S - 65536 <= a -> a + Z.of_nat n <= S -> exists bs, rw_cells rsegs m a [CB n bs].
Proof. intros a n H1 H2. exact (sl_rw_of_stk m _ _ a n m02_stk H1 H2). Qed.

Lemma m02_bytes : forall a n, S - 65536 <= a -> a + Z.of_nat n <= S ->
  exists bs, length bs = n /\ bytes_at rsegs m a bs.
Proof.
  intros a n H1 H2. destruct (m02_cells a n H1 H2) as (bs & HC).
  pose proof HC as [[Hwf _] _]. cbn [cells_wf] in Hwf.
  exists bs. split; [exact (proj1 Hwf) | exact (sl_rw_bytes m a n bs HC)].
Qed.

End K.

(* sub_fp of a callee's write set inside M02_W S, and its addresses below 2^47: unfold and lia. *)
Ltac m02_subfp :=
  unfold sub_fp, M02_W, M02_FRAME; intros ?x ?Hx; cbn [outside] in *; repeat split; lia.
Ltac m02_low :=
  intros ?x ?Hx ?O; cbn [outside] in O; unfold M02_FRAME in *; lia.
