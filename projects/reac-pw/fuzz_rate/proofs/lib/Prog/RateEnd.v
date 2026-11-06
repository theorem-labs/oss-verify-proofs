(* plain_halts of reac-pw/fuzz_rate from the frame and the slot of LLVMFuzzerTestOneInput: reac-pw/fuzz_role's
   Prog/RoleEnd.v (itself reac-pw/fuzz_pin's Prog/PinEnd.v,
   libreac/fuzz_ctrl's released Prog/Seg/Segs.v + Prog/Seg/SlotLink.v, origin/ossv/recipes 25e3d17bdb50) for rate's
   five segments.
   - The segment lemmas, each as its segment file states it once its Section closes (Section hypotheses:
     FrameAPI.frame_facts_plain, then the one contract the segment takes): seg_E01_stmt (Seg/E01.v: the prologue,
     the seven header reads and malloc(pp), malloc from frame_allocator inside frame_facts_plain), seg_M01_stmt
     (Seg/M01.v: rate_build_contract, the builder evt, and malloc(pod)), seg_M02_stmt (Seg/M02.v:
     rate_check_contract, the checking evt), seg_M03_stmt (Seg/M03.v: malloc(buf) and rate_csv_contract, the csv
     evt) and seg_X01_stmt (Seg/X01.v: free(buf), free(pod), free(pp) and the epilogue, free_contract).
   - segs_holds: LLVMFuzzerTestOneInput_c.seg_lemmas for every instance that satisfies frame_facts_plain, from the
     five segment lemmas and the three evt contracts (free_contract from frame_facts_plain's frame_allocator).
   - plain_halts_of_callees: Statements.plain_halts from FrameProof.frame_plain_holds through
     RateSlot.plain_halts_of_frame, with the five segment lemmas and the three evt contracts as its premises (the
     builder's walk discharges rate_build_contract from the leaves memset, memcpy and strlen; the checking walk
     discharges rate_check_contract from the contracts of rate's own callees; the csv walk discharges
     rate_csv_contract from those of reac_rate_drivable_csv and check_csv).
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the composition of
   the segment lemmas with the slot); LLVMFuzzerTestOneInput's walk is closed here modulo the five segment lemmas
   and the three evt contracts. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require FrameProof.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require RateSlot.
From OSSVerify.reac_pw.fuzz_rate Require Statements.

(* The segment lemmas, as the segment files state them once their Sections close. *)
Definition seg_E01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> S_E01 B APIf ra empty.

Definition seg_M01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> rate_build_contract -> S_M01 B APIf ra empty.

Definition seg_M02_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> rate_check_contract -> S_M02 B APIf ra empty.

Definition seg_M03_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> rate_csv_contract -> S_M03 B APIf ra empty.

Definition seg_X01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> free_contract B (APIf rc) -> S_X01 B APIf ra empty.

Theorem segs_holds : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_X01_stmt ->
  rate_build_contract -> rate_check_contract -> rate_csv_contract ->
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros E01 M01 M02 M03 X01 BUILD CHECK CSV fx rc B APIf LS SH SK ra empty FF.
  assert (FREE : free_contract B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_plain in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [exact (E01 fx rc B APIf LS SH SK ra empty FF)|].
  split; [exact (M01 fx rc B APIf LS SH SK ra empty FF BUILD)|].
  split; [exact (M02 fx rc B APIf LS SH SK ra empty FF CHECK)|].
  split; [exact (M03 fx rc B APIf LS SH SK ra empty FF CSV)|].
  exact (X01 fx rc B APIf LS SH SK ra empty FF FREE).
Qed.

Theorem plain_halts_of_callees : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_X01_stmt ->
  rate_build_contract -> rate_check_contract -> rate_csv_contract -> Statements.plain_halts.
Proof.
  intros E01 M01 M02 M03 X01 BUILD CHECK CSV.
  exact (RateSlot.plain_halts_of_frame (segs_holds E01 M01 M02 M03 X01 BUILD CHECK CSV)
           FrameProof.frame_plain_holds).
Qed.
