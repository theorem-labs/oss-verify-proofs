From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import reac_scene_struct SceneTac SceneRun.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneE00 SceneE01 SceneE02 SceneE03 SceneE04 SceneE05
  SceneE06 SceneE07 SceneE08 SceneE09 SceneE10 SceneE11.
Import ListNotations.
Open Scope Z_scope.

Section E.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).

Lemma scene_entry_x : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m lo p data,
  entry_stmt ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m lo p data.
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m lo p data.
  assert (H : (length data = 0 \/ length data = 1 \/ length data = 2 \/ length data = 3 \/ length data = 4 \/
               length data = 5 \/ length data = 6 \/ length data = 7 \/ length data = 8 \/ length data = 9 \/
               length data = 10 \/ 11 <= length data)%nat) by lia.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
    first [ (eapply scene_entry_l0; exact H)
          | (eapply scene_entry_l1; exact H)
          | (eapply scene_entry_l2; exact H)
          | (eapply scene_entry_l3; exact H)
          | (eapply scene_entry_l4; exact H)
          | (eapply scene_entry_l5; exact H)
          | (eapply scene_entry_l6; exact H)
          | (eapply scene_entry_l7; exact H)
          | (eapply scene_entry_l8; exact H)
          | (eapply scene_entry_l9; exact H)
          | (eapply scene_entry_l10; exact H)
          | (eapply scene_entry_l11; exact H) ].
Qed.

End E.
