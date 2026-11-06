From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

(* the program-written image cells, from the generated LedgerCells.v (twin .symtab, keyed by symbol), in the order the
   proofs need: the four ledger words over Ledger.v's names, then g_ran_out (entry 5, as before #102), then the #102
   cells g_most (entry 6) and g_own_ran_out (entry 7). Each cell is one object and the alignment padding after it. *)
Definition omx_G : list (Z * Z) := Eval cbv beta delta [GL_cells_over] in GL_cells_over G_LIVE G_PEAK G_COUNT G_FAIL.

Lemma omx_G_cells : omx_G = GL_cells.
Proof. reflexivity. Qed.

Section GInit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.

Lemma omx_GI_init : forall mem,
  ms_segs B = rsegs ->
  (forall a, in_globals omx_G a -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a)) ->
  omx_GI B 0 mem.
Proof.
  intros mem HS H. exists 0, 0.
  assert (W : forall g v, In (g, 8) omx_G ->
            (forall k, (k < 8)%nat -> seg_rom rsegs (Z_to_bv 64 (g + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v 8 k))) ->
            word_mem (ms_segs B) mem g v).
  { intros g v Hin Hk k Hk8. rewrite H.
    - rewrite HS. apply Hk. exact Hk8.
    - exists g, 8. split; [exact Hin|]. lia. }
  split; [|split; [lia|split; lia]].
  unfold alloc_words. repeat split; apply W;
    try (cbn [omx_G In]; tauto);
    intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.

End GInit.
