(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). Closed check, a Theorem Labs lane's condition (b) on the lib_const_addr
   --patch (a Theorem Labs lane): the patched range [0x9c388, 0x9c390) (scene_obj 4, a .got word) is disjoint from every Tfib_owned_static row and from
   the errno cell, so ACeg's tl_lib_consts holds at scene's B and TfibLib is satisfiable. proves no function (kind: start-up facts). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AF0m.
Import ListNotations. Open Scope Z_scope.
Lemma lib_const_owned_chk :
  forallb (fun r => (fst r + snd r <=? 0x9c388) || (0x9c390 <=? fst r)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lib_const_errno_chk : (TFIB_ERRNO + 4 <=? 0x9c388) || (0x9c390 <=? TFIB_ERRNO) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lib_const_scene_ok : forall a, 0x9c388 <= a < 0x9c390 ->
  ~ Exists (in_zr a) Tfib_owned_static /\ ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4).
Proof.
  intros a Ha. split.
  - intros HE. apply Exists_exists in HE as (r & Hr & Hin). unfold in_zr in Hin.
    pose proof (proj1 (forallb_forall _ _) lib_const_owned_chk r Hr) as Hc. cbn beta in Hc.
    apply orb_true_iff in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
  - pose proof lib_const_errno_chk as Hc. apply orb_true_iff in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
Qed.
