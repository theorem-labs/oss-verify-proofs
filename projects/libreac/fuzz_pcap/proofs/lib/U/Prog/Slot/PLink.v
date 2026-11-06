From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PSlot.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require FrameProof.
From OSSVerify.libreac.fuzz_pcap Require Statements.
Import ListNotations.
Open Scope Z_scope.

(* The plain theorem from the slot's run, cut at its entry: for an output function f that is [] on payloads of
   2^26 bytes or more, the run from Inv_ENTRY outputs f of the payload and returns with Post_o. *)
Theorem ubsan_halts_of_entry_o : forall f : list byte -> list byte,
  (forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
          (SH : sink_head) (SK : sink_syms) (ra empty : Z),
     frame_facts B APIf SH SK ra empty -> malloc_contract B (APIf rc) -> free_contract B (APIf rc) ->
     Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => f (g_in g))) ->
  (forall pl, 2 ^ 26 <= Z.of_nat (length pl) -> f pl = []) ->
  OSSVerify.libreac.fuzz_pcap.Statements.ubsan_halts.
Proof.
  intros f HENTRY HBIG.
  destruct FrameProof.frame_ubsan_holds as (B & API & LS & SH & SK & ra & empty & H1 & H2 & H3 & H4 & H5 & H6 & H7 &
    H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
    H27 & H28 & H29 & HALLOC & HLAST).
  assert (FF : frame_facts B API SH SK ra empty)
    by (unfold frame_facts; repeat (split; [assumption|]); assumption).
  apply (HLAST f frame_G GI).
  - intros a H. exact H.
  - exact (GI_local B H1).
  - intros mem Hm. exact (GI_img B mem H1 Hm).
  - intros rc fx j _.
    destruct (HALLOC rc fx) as (HMAL & HFREE & _).
    apply (slot_contract_o B API ra empty FF f); [|exact HBIG].
    exact (HENTRY fx rc B API SH SK ra empty FF HMAL HFREE).
Qed.
