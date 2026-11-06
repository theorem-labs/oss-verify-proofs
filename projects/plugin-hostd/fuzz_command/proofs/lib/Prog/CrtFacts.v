From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0x YO0u.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP
  VerbsB CommandB.
Import ListNotations.
Local Open Scope Z_scope.

Definition zz_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma pw_count : forall (R : Z * Z -> Z * Z -> Prop) l x,
  pairwise R l -> ~ R x x -> (count_occ (zz_dec) l x <= 1)%nat.
Proof.
  intros R l x. induction l as [|y l IH]; intros HP NR; cbn; [lia|].
  destruct HP as [H1 H2]. destruct (zz_dec y x) as [->|NE].
  - assert (C : count_occ (zz_dec) l x = 0%nat).
    { apply count_occ_not_In. intros Hin. exact (NR (H1 x Hin)). }
    lia.
  - exact (IH H2 NR).
Qed.

Lemma rd_irrefl : forall x, 0 < snd x -> ~ ranges_disjoint x x.
Proof. intros [a n] H. unfold ranges_disjoint. cbn in *. lia. Qed.

Lemma pw_perm_two : forall l l1 l2 x, pairwise ranges_disjoint l -> Permutation l (l1 ++ l2) ->
  In x l1 -> In x l2 -> 0 < snd x -> False.
Proof.
  intros l l1 l2 x HP HPm H1 H2 Hx.
  pose proof (pw_count _ l x HP (rd_irrefl x Hx)) as C.
  rewrite (proj1 (Permutation_count_occ zz_dec _ _) HPm x), count_occ_app in C.
  apply (count_occ_In (zz_dec)) in H1. apply (count_occ_In (zz_dec)) in H2.
  lia.
Qed.

Lemma pw_mid_notin : forall b1 x b2, pairwise ranges_disjoint (b1 ++ x :: b2) -> 0 < snd x -> ~ In x (b1 ++ b2).
Proof.
  intros b1 x b2 HP Hx Hin.
  apply (pw_perm_two (b1 ++ x :: b2) [x] (b1 ++ b2) x HP); [| left; reflexivity | exact Hin | exact Hx].
  apply Permutation_sym. exact (Permutation_middle b1 b2 x).
Qed.

Lemma pw_in_disjoint : forall l x y, pairwise ranges_disjoint l -> In x l -> In y l -> x <> y ->
  ranges_disjoint x y.
Proof.
  induction l as [|z l IH]; intros x y HP Hx Hy Hne; [destruct Hx|].
  destruct HP as [H1 H2]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - congruence.
  - exact (H1 y Hy).
  - unfold ranges_disjoint in *. pose proof (H1 x Hx). lia.
  - exact (IH x y H2 Hx Hy Hne).
Qed.

Section B.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis CTXO : ctx_owned B API.
Hypothesis AX : AllocExtra B MR.

Lemma le_at_bytes : forall mem a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  le_at B mem a bs -> bytes_at rsegs mem a bs.
Proof using SEGS.
  intros mem a bs H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (H (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id, SEGS in E. exact E.
Qed.

Lemma bytes_le_at : forall mem a bs, bytes_at rsegs mem a bs -> le_at B mem a bs.
Proof using SEGS.
  intros mem a bs (H0 & H1 & H) i Hi. rewrite SEGS.
  pose proof (H (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E.
Qed.

Lemma stk_of_writable : forall mem lo hi, 2 ^ 20 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs mem a) -> stk rsegs mem lo hi.
Proof.
  intros mem lo hi Hlo Hhi H. split; [lia|]. split; [exact Hhi|]. intros a Ha.
  assert (W : writable_at rsegs mem a) by (apply H; lia).
  split; [exact W|].
  destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity.
Qed.

Lemma not_owned_any : forall L A mem md L1 A1 mem1 md1 a,
  MR L A mem md -> MR L1 A1 mem1 md1 -> (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
  ~ owned B L A a -> ~ owned B L1 A1 a.
Proof using CTXO AX.
  intros L A mem md L1 A1 mem1 md1 a HM HM1 Ha NO [Ho|Hs].
  - destruct Ha as [Ha|Ha].
    + pose proof (mr_owned_low B MR (aa_laws API) L1 A1 mem1 md1 a HM1 (or_introl Ho)). lia.
    + pose proof (ax_img AX L1 A1 mem1 md1 a HM1 Ha Ho) as Hc. exact (NO (CTXO L A mem md a HM Hc)).
  - exact (NO (or_intror Hs)).
Qed.

End B.
