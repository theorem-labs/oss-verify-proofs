(* ubsan_halts of reac-pw/fuzz_rate from the UBSan frame and the slot of LLVMFuzzerTestOneInput: reac-pw/fuzz_role's
   U/Prog/RoleEnd.v (the plain lib/Prog/RoleEnd.v in reac-pw/fuzz_pin's
   U/Prog/PinEnd.v form: libreac/fuzz_ctrl's released U/Prog/Seg/Segs.v + SlotLink.v, origin/ossv/recipes
   25e3d17bdb50) on rate's UBSan build's files, for its five segments.
   - The segment lemmas, each as its segment file states it once its Section closes (Section hypotheses:
     U/FrameAPI.frame_facts_ubsan, then the one contract the segment takes): seg_E01_stmt (U/Prog/Seg/E01.v: the
     prologue, the header reads and malloc(pp)), seg_M01_stmt (U/Prog/Seg/M01.v: rate_build_contract and
     malloc(pod)), seg_M02_stmt (U/Prog/Seg/M02.v: rate_check_contract), seg_M03_stmt (U/Prog/Seg/M03.v: malloc(buf)
     and rate_csv_contract) and seg_X01_stmt (U/Prog/Seg/X01.v: the three frees and the epilogue, free_contract).
   - segs_holds: U LLVMFuzzerTestOneInput_c.seg_lemmas for every instance that satisfies frame_facts_ubsan, from the
     five segment lemmas and the three evt contracts (free_contract from frame_facts_ubsan's frame_allocator).
   - ubsan_halts_of_callees: Statements.ubsan_halts from U/FrameProof.frame_ubsan_holds through
     U/Prog/RateSlot.ubsan_halts_of_frame, with the five segment lemmas and the three evt contracts as its premises.
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the composition of
   the segment lemmas with the slot); LLVMFuzzerTestOneInput's walk is closed here modulo the five segment lemmas
   and the three evt contracts. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require FrameProof.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require RateSlot.
From OSSVerify.reac_pw.fuzz_rate Require Statements.

(* The segment lemmas, as the segment files state them once their Sections close. *)
Definition seg_E01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> S_E01 B APIf ra empty.

Definition seg_M01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> rate_build_contract -> S_M01 B APIf ra empty.

Definition seg_M02_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> rate_check_contract -> S_M02 B APIf ra empty.

Definition seg_M03_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> rate_csv_contract -> S_M03 B APIf ra empty.

Definition seg_X01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> free_contract B (APIf rc) -> S_X01 B APIf ra empty.

Theorem segs_holds : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_X01_stmt ->
  rate_build_contract -> rate_check_contract -> rate_csv_contract ->
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros E01 M01 M02 M03 X01 BUILD CHECK CSV fx rc B APIf LS SH SK ra empty FF.
  assert (FREE : free_contract B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_ubsan in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [exact (E01 fx rc B APIf LS SH SK ra empty FF)|].
  split; [exact (M01 fx rc B APIf LS SH SK ra empty FF BUILD)|].
  split; [exact (M02 fx rc B APIf LS SH SK ra empty FF CHECK)|].
  split; [exact (M03 fx rc B APIf LS SH SK ra empty FF CSV)|].
  exact (X01 fx rc B APIf LS SH SK ra empty FF FREE).
Qed.

Theorem ubsan_halts_of_callees : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_X01_stmt ->
  rate_build_contract -> rate_check_contract -> rate_csv_contract -> Statements.ubsan_halts.
Proof.
  intros E01 M01 M02 M03 X01 BUILD CHECK CSV.
  exact (RateSlot.ubsan_halts_of_frame (segs_holds E01 M01 M02 M03 X01 BUILD CHECK CSV)
           FrameProof.frame_ubsan_holds).
Qed.
