From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Definition omx_G : list (Z * Z) := [(G_LIVE, 8); (G_PEAK, 8); (G_COUNT, 8); (G_FAIL, 8)].

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
