(* plain_halts of reac-pw/fuzz_headamp from the frame and the slot of LLVMFuzzerTestOneInput: reac-pw/fuzz_role's
   Prog/RoleEnd.v (itself reac-pw/fuzz_pin's Prog/PinEnd.v and libreac/fuzz_ctrl's released Prog/Seg/Segs.v +
   Prog/Seg/SlotLink.v) for headamp's six segments.
   - The segment lemmas, each as its segment file states it once its Section closes (Section hypotheses:
     FrameAPI.frame_facts_plain, then the contracts the segment takes, in this order): seg_E01_stmt (Seg/E01.v: the
     prologue and malloc(pp)), seg_M01_stmt (Seg/M01.v: headamp_build_contract, the builder evt, and malloc(pod)),
     seg_M02_stmt (Seg/M02.v: headamp_dup_pod_contract and malloc(out)), seg_M03_stmt (Seg/M03.v:
     headamp_check_contract, the checking evt, and malloc(first)), seg_M04_stmt (Seg/M04.v:
     headamp_dup_first_contract, then headamp_plain_contract) and seg_X01_stmt (Seg/X01.v: the four frees and the
     epilogue, free_contract). malloc and free come from frame_allocator inside frame_facts_plain.
   - segs_holds: LLVMFuzzerTestOneInput_c.seg_lemmas for every instance that satisfies frame_facts_plain, from the
     six segment lemmas and the five evt contracts (free_contract from frame_facts_plain's frame_allocator).
   - plain_halts_of_callees: Statements.plain_halts from FrameProof.frame_plain_holds through
     HeadSlot.plain_halts_of_frame, with the six segment lemmas, the five middle evt contracts and the n >= 2^26
     run's headamp_early_contract as its premises; plain_halts_of_segs: the same with headamp_early_contract
     discharged by Prog/headamp_early.v's headamp_early_holds.
   - seg_E01_holds .. seg_X01_holds: the six segment statements from the segment files Seg/E01.v .. Seg/X01.v.
   - plain_halts_of_evts: Statements.plain_halts with the segment lemmas and the n >= 2^26 run discharged (premises:
     the five middle evt contracts); plain_halts_of_leaves: also dup_pod, dup_first and plain discharged by their
     walks (Prog/headamp_dup_pod.v, headamp_dup_first.v, headamp_plain.v; premises: the builder and checking evts
     and the leaf contracts memcpy, memset, the parse and check_plain); plain_halts_of_contracts: also the builder
     (Prog/headamp_build.v's headamp_build_holds) and memset, memcpy, strlen (Prog/memset.v, memcpy.v, strlen.v)
     discharged; its premises are the contracts whose walks are written elsewhere: headamp_check_contract (the
     checking evt), reac_headamp_prop_parse_contract and check_plain_contract.
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the composition of
   the segment lemmas with the slot); LLVMFuzzerTestOneInput's walk is closed here modulo the checking evt
   headamp_check_contract and the two callee contracts of the plain evt. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require FrameProof.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require HeadSlot headamp_early.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require headamp_build headamp_dup_pod headamp_dup_first
  headamp_plain memset memcpy strlen memset_c memcpy_c strlen_c reac_headamp_prop_parse_c check_plain_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require E01 M01 M02 M03 M04 X01.
From OSSVerify.reac_pw.fuzz_headamp Require Statements.

(* The segment lemmas, as the segment files state them once their Sections close. *)
Definition seg_E01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> S_E01 B APIf ra empty.

Definition seg_M01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> headamp_build_contract -> S_M01 B APIf ra empty.

Definition seg_M02_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> headamp_dup_pod_contract -> S_M02 B APIf ra empty.

Definition seg_M03_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> headamp_check_contract -> S_M03 B APIf ra empty.

Definition seg_M04_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> headamp_dup_first_contract -> headamp_plain_contract ->
  S_M04 B APIf ra empty.

Definition seg_X01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> free_contract B (APIf rc) -> S_X01 B APIf ra empty.

Theorem segs_holds : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_M04_stmt -> seg_X01_stmt ->
  headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract -> headamp_dup_first_contract ->
  headamp_plain_contract ->
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros E01 M01 M02 M03 M04 X01 BUILD DUPP CHECK DUPF PLAIN fx rc B APIf LS SH SK ra empty FF.
  assert (FREE : free_contract B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_plain in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [exact (E01 fx rc B APIf LS SH SK ra empty FF)|].
  split; [exact (M01 fx rc B APIf LS SH SK ra empty FF BUILD)|].
  split; [exact (M02 fx rc B APIf LS SH SK ra empty FF DUPP)|].
  split; [exact (M03 fx rc B APIf LS SH SK ra empty FF CHECK)|].
  split; [exact (M04 fx rc B APIf LS SH SK ra empty FF DUPF PLAIN)|].
  exact (X01 fx rc B APIf LS SH SK ra empty FF FREE).
Qed.

Theorem plain_halts_of_callees : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_M04_stmt ->
  seg_X01_stmt ->
  headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract -> headamp_dup_first_contract ->
  headamp_plain_contract -> headamp_early_contract -> Statements.plain_halts.
Proof.
  intros E01 M01 M02 M03 M04 X01 BUILD DUPP CHECK DUPF PLAIN EARLY.
  exact (HeadSlot.plain_halts_of_frame EARLY (segs_holds E01 M01 M02 M03 M04 X01 BUILD DUPP CHECK DUPF PLAIN)
           FrameProof.frame_plain_holds).
Qed.

(* The n >= 2^26 run discharged by its walk. *)
Theorem plain_halts_of_segs : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_M04_stmt ->
  seg_X01_stmt ->
  headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract -> headamp_dup_first_contract ->
  headamp_plain_contract -> Statements.plain_halts.
Proof.
  intros E01 M01 M02 M03 M04 X01 BUILD DUPP CHECK DUPF PLAIN.
  exact (plain_halts_of_callees E01 M01 M02 M03 M04 X01 BUILD DUPP CHECK DUPF PLAIN
           headamp_early.headamp_early_holds).
Qed.

(* ---- The segment lemmas, from the segment files ---- *)
Theorem seg_E01_holds : seg_E01_stmt.
Proof. intros fx rc B APIf LS SH SK ra empty FF. exact (@E01.seg_E01 fx rc B APIf LS SH SK ra empty FF). Qed.

Theorem seg_M01_holds : seg_M01_stmt.
Proof. intros fx rc B APIf LS SH SK ra empty FF H. exact (@M01.seg_M01 fx rc B APIf LS SH SK ra empty FF H). Qed.

Theorem seg_M02_holds : seg_M02_stmt.
Proof. intros fx rc B APIf LS SH SK ra empty FF H. exact (@M02.seg_M02 fx rc B APIf LS SH SK ra empty FF H). Qed.

Theorem seg_M03_holds : seg_M03_stmt.
Proof. intros fx rc B APIf LS SH SK ra empty FF H. exact (@M03.seg_M03 fx rc B APIf LS SH SK ra empty FF H). Qed.

Theorem seg_X01_holds : seg_X01_stmt.
Proof. intros fx rc B APIf LS SH SK ra empty FF H. exact (@X01.seg_X01 fx rc B APIf LS SH SK ra empty FF H). Qed.

Theorem seg_M04_holds : seg_M04_stmt.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF H1 H2. exact (@M04.seg_M04 fx rc B APIf LS SH SK ra empty FF H1 H2).
Qed.

(* ---- LLVMFuzzerTestOneInput's walk with the segment lemmas and the n >= 2^26 run discharged ---- *)
Theorem plain_halts_of_evts : headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract ->
  headamp_dup_first_contract -> headamp_plain_contract -> Statements.plain_halts.
Proof.
  exact (plain_halts_of_segs seg_E01_holds seg_M01_holds seg_M02_holds seg_M03_holds seg_M04_holds seg_X01_holds).
Qed.

(* ... and the small evts dup_pod, dup_first and plain discharged by their walks. *)
Theorem plain_halts_of_leaves : headamp_build_contract -> headamp_check_contract -> memcpy_c.memcpy_contract ->
  memset_c.memset_contract -> reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract ->
  check_plain_c.check_plain_contract -> Statements.plain_halts.
Proof.
  intros BUILD CHECK MCPY MSET PARSE CPLAIN.
  exact (plain_halts_of_evts BUILD (headamp_dup_pod.headamp_dup_pod_holds MCPY) CHECK
           (headamp_dup_first.headamp_dup_first_holds MCPY) (headamp_plain.headamp_plain_holds MSET PARSE CPLAIN)).
Qed.

(* ... and the builder, memcpy, memset and strlen discharged by their walks: modulo the checking evt and the plain
   evt's two callees. *)
Theorem plain_halts_of_contracts : headamp_check_contract ->
  reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract -> check_plain_c.check_plain_contract ->
  Statements.plain_halts.
Proof.
  intros CHECK PARSE CPLAIN.
  exact (plain_halts_of_leaves
           (headamp_build.headamp_build_holds memset.memset_holds memcpy.memcpy_holds strlen.strlen_holds)
           CHECK memcpy.memcpy_holds memset.memset_holds PARSE CPLAIN).
Qed.
