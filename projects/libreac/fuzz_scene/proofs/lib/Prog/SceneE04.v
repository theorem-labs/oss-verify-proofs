From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import reac_scene_struct SceneTac SceneRun.
Import ListNotations.
Open Scope Z_scope.

Section E.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).

Lemma scene_entry_l4 : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m lo p data, length data = 4%nat ->
  entry_stmt ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m lo p data.
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m lo p data HL. entry_cases HL.
  entry_run sp. all: entry_vals sp.
Qed.

End E.
