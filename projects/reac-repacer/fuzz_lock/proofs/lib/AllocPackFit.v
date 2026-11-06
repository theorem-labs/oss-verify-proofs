From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO0d YO0j.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import AllocPack AllocPackRoom AllocPackGSF.
Import ListNotations.
Local Open Scope Z_scope.

(* Linear bounds of the cut-free room in the caps, for the per-unit fit checks: a unit with caps CS proves
   LIVE2c CS bytes + NONHEAP_CF <= lim from LIVE2c_lin and a linear bound of its CS. *)

Definition MWf (k : Z) : Z :=
  zsumZ (fun c => if nestF c then 0 else GLEN c * znth k (pk_row pk_A c)) (zseq 0 48) +
  (if k =? 48 then pk_D * (3 * PGSZ) else 0).

Definition MW0 : Z := zsumZ (fun c => if nestF c then 0 else GLEN c * (znth c pk_B + pk_D * RED)) (zseq 0 48).

Lemma pk_lin_wsum (p : Z -> bool) (w : Z -> Z) (R : Z -> list Z) caps l :
  zsumZ (fun c => if p c then w c * pk_lin (R c) caps else 0) l =
  zsumZ (fun k => zsumZ (fun c => if p c then w c * znth k (R c) else 0) l * znth k caps) (zseq 0 49).
Proof.
  induction l as [|c l IH].
  - change (0 = zsumZ (fun k => 0 * znth k caps) (zseq 0 49)). symmetry. apply zsumZ_zero. intros; reflexivity.
  - rewrite zsumZ_cons, IH. cbv beta.
    transitivity (zsumZ (fun k => (if p c then w c * znth k (R c) * znth k caps else 0) +
      zsumZ (fun c0 => if p c0 then w c0 * znth k (R c0) else 0) l * znth k caps) (zseq 0 49)).
    + rewrite zsumZ_add. apply (f_equal2 Z.add); [|reflexivity].
      destruct (p c); [|symmetry; apply zsumZ_zero; intros; reflexivity].
      unfold pk_lin. rewrite <- zsumZ_mul_l. apply zsumZ_ext. intros k _. ring.
    + apply zsumZ_ext. intros k _. cbv beta. rewrite zsumZ_cons. cbv beta. destruct (p c); ring.
Qed.

Lemma GLEN_nonneg c : 0 <= c < 48 -> 0 <= GLEN c.
Proof.
  intros Hc. assert (T : forallb (fun c => 0 <=? GLEN c) (zseq 0 48) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in T. apply Z.leb_le. apply T. apply In_zseq. lia.
Qed.

Theorem MAPB_lin : forall caps, (forall k, 0 <= k < 49 -> 0 <= znth k caps) ->
  pk_D * MAPB caps <= zsumZ (fun k => MWf k * znth k caps) (zseq 0 49) + MW0.
Proof.
  intros caps Hc. unfold MAPB.
  assert (H1 : pk_D * zsumZ (fun c => if nestF c then 0 else (znth c (NF caps) + RED) * GLEN c) (zseq 0 48) <=
     zsumZ (fun c => if negb (nestF c) then GLEN c * pk_lin (pk_row pk_A c) caps else 0) (zseq 0 48) + MW0).
  { unfold MW0. rewrite <- zsumZ_mul_l, <- zsumZ_add. apply zsumZ_le. intros c Hc'. apply In_zseq in Hc'. cbv beta.
    destruct (nestF c); cbn [negb]; [lia|]. pose proof (pk_class caps Hc c ltac:(lia)) as P.
    pose proof (GLEN_nonneg c Hc') as G. unfold pk_D in *. nia. }
  rewrite (pk_lin_wsum (fun c => negb (nestF c)) GLEN (pk_row pk_A) caps (zseq 0 48)) in H1. cbv beta in H1.
  pose proof (zsumZ_single (fun k => pk_D * (3 * PGSZ) * znth k caps) 48 (zseq 0 49) (zseq_NoDup 0 49)
    (proj2 (In_zseq 0 49 48) ltac:(lia))) as E2. cbv beta in E2.
  assert (E3 : zsumZ (fun k => MWf k * znth k caps) (zseq 0 49) =
     zsumZ (fun k => zsumZ (fun c => if negb (nestF c) then GLEN c * znth k (pk_row pk_A c) else 0) (zseq 0 48) * znth k caps) (zseq 0 49) +
     zsumZ (fun k => if k =? 48 then pk_D * (3 * PGSZ) * znth k caps else 0) (zseq 0 49)).
  { rewrite <- zsumZ_add. apply zsumZ_ext. intros k _. unfold MWf.
    assert (Ez : zsumZ (fun c => if nestF c then 0 else GLEN c * znth k (pk_row pk_A c)) (zseq 0 48) =
      zsumZ (fun c => if negb (nestF c) then GLEN c * znth k (pk_row pk_A c) else 0) (zseq 0 48)).
    { apply zsumZ_ext. intros c _. destruct (nestF c); reflexivity. }
    rewrite Ez. destruct (k =? 48); ring. }
  rewrite E3, E2. lia.
Qed.

Theorem LIVE2c_lin : forall caps bytes, length caps = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k caps) ->
  METAS_PER_AREA * pk_D * LIVE2c caps bytes <=
  zsumZ (fun k => (METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA) * znth k caps) (zseq 0 49) +
  METAS_PER_AREA * MW0 + 3 * PGSZ * pk_G0 + METAS_PER_AREA * pk_D * (bytes + 84 * PGSZ).
Proof.
  intros caps bytes Hl Hc.
  pose proof (MAPB_lin caps Hc) as HM. pose proof (GALL_lin caps Hl Hc) as HG.
  assert (H0 : 0 <= GALL caps).
  { unfold GALL. pose proof (Hc 48 ltac:(lia)). enough (0 <= zsumZ (fun c => znth c (NF caps) + RED) (zseq 0 48)) by lia.
    apply zsumZ_nonneg. intros c _. pose proof (NF_nonneg caps c (fun j Hj => Hc j ltac:(lia))). unfold RED. lia. }
  pose proof (Z.mul_div_le (GALL caps) METAS_PER_AREA ltac:(unfold METAS_PER_AREA; lia)) as DV.
  assert (E : zsumZ (fun k => (METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA) * znth k caps) (zseq 0 49) =
     METAS_PER_AREA * zsumZ (fun k => MWf k * znth k caps) (zseq 0 49) +
     3 * PGSZ * zsumZ (fun k => znth k pk_BETA * znth k caps) (zseq 0 49)).
  { rewrite <- !zsumZ_mul_l, <- zsumZ_add. apply zsumZ_ext. intros k _. ring. }
  rewrite E. unfold LIVE2c, NA2, AREA2. unfold pk_D, PGSZ, METAS_PER_AREA in *. nia.
Qed.
