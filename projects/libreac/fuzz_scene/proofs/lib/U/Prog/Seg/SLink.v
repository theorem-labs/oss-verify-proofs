From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv STac SSlot.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require FrameProof.
From OSSVerify.libreac.fuzz_scene Require Statements.
Import ListNotations.
Open Scope Z_scope.

Theorem ubsan_halts_of_entry :
  (forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
          (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
     frame_facts B APIf LS SH SK ra empty -> malloc_contract B (APIf rc) -> free_contract B (APIf rc) ->
     Hcut B APIf ra (Inv_ENTRY B APIf ra empty)) ->
  scene_early -> OSSVerify.libreac.fuzz_scene.Statements.ubsan_halts.
Proof.
  intros HENTRY HEARLY.
  destruct (frame_ubsan_split FrameProof.frame_ubsan_holds) as (B & API & LS & SH & SK & ra & empty & HF & HLAST).
  destruct HF as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & HROOM & HALLOC).
  assert (FF : frame_facts B API LS SH SK ra empty)
    by (unfold frame_facts; repeat (split; [assumption|]); assumption).
  apply (HLAST [] (fun _ _ => True)).
  - intros a (lo & len & Hin & _). destruct Hin.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j _.
    destruct (HALLOC rc fx) as (HMAL & HFREE & _).
    apply (slot_lib B API ra empty FF HEARLY);
      [intros b0 n0 Hb; destruct (HROOM b0 n0 Hb) as (R1 & R2 & R3); unfold slot_room; rewrite R3; unfold CAPMAX; lia|].
    exact (HENTRY fx rc B API LS SH SK ra empty FF HMAL HFREE).
Qed.
