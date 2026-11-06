(* ubsan_halts of reac-pw/fuzz_headamp from the UBSan frame and the slot of LLVMFuzzerTestOneInput: reac-pw/fuzz_role's
   U/Prog/RoleEnd.v (reac-pw/fuzz_pin's U/Prog/PinEnd.v form: libreac/fuzz_ctrl's released U/Prog/Seg/Segs.v +
   SlotLink.v, origin/ossv/recipes 25e3d17bdb50) on headamp's six segments.
   - The segment lemmas, each as its segment file states it once its Section closes (Section hypotheses:
     U/FrameAPI.frame_facts_ubsan, then the contracts the segment takes): seg_E01_stmt (U/Prog/Seg/E01.v: the
     prologue and malloc(pp)), seg_M01_stmt (U/Prog/Seg/M01.v: headamp_build_contract and malloc(pod)), seg_M02_stmt
     (U/Prog/Seg/M02.v: headamp_dup_pod_contract and malloc(out)), seg_M03_stmt (U/Prog/Seg/M03.v:
     headamp_check_contract and malloc(first)), seg_M04_stmt (U/Prog/Seg/M04.v: headamp_dup_first_contract, then
     headamp_plain_contract) and seg_X01_stmt (U/Prog/Seg/X01.v: the four frees and the epilogue, free_contract).
   - segs_holds: U LLVMFuzzerTestOneInput_c.seg_lemmas for every instance that satisfies frame_facts_ubsan, from the
     six segment lemmas and the five evt contracts (free_contract from frame_facts_ubsan's frame_allocator).
   - ubsan_halts_of_callees: Statements.ubsan_halts from U/FrameProof.frame_ubsan_holds through
     U/Prog/HeadSlot.ubsan_halts_of_frame, with the six segment lemmas, the five evt contracts of the segments and
     headamp_early_contract (the n >= 2^26 run) as its premises; ubsan_halts_of_segs, the same with
     headamp_early_contract discharged by U/Prog/headamp_early.headamp_early_holds.
   - seg_*_holds: the six segment statements, by the segment files (U/Prog/Seg/E01.v .. X01.v).
   - ubsan_halts_of_evts: Statements.ubsan_halts from the five evt contracts of the segments alone;
     ubsan_halts_of_leaves: the same with the three small evts discharged (U/Prog/headamp_dup_pod.v,
     headamp_dup_first.v, headamp_plain.v), from headamp_build_contract, headamp_check_contract and the leaf contracts
     memcpy, memset, reac_headamp_prop_parse, check_plain; ubsan_halts_of_contracts: the same with the builder
     (U/Prog/headamp_build.v) and memcpy, memset, strlen, pod_write_ent discharged, from headamp_check_contract,
     reac_headamp_prop_parse_contract and check_plain_contract.
   rule 24: proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's walk: the composition of
   the segment lemmas with the slot); LLVMFuzzerTestOneInput's UBSan walk is closed here modulo
   headamp_check_contract, reac_headamp_prop_parse_contract and check_plain_contract (ubsan_halts_of_contracts). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require FrameProof.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require HeadSlot headamp_early.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require headamp_dup_pod headamp_dup_first headamp_plain
  headamp_build memcpy memset strlen pod_write_ent memcpy_c memset_c reac_headamp_prop_parse_c check_plain_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.Seg Require E01 M01 M02 M03 M04 X01.
From OSSVerify.reac_pw.fuzz_headamp Require Statements.

(* The segment lemmas, as the segment files state them once their Sections close. *)
Definition seg_E01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> S_E01 B APIf ra empty.

Definition seg_M01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> headamp_build_contract -> S_M01 B APIf ra empty.

Definition seg_M02_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> headamp_dup_pod_contract -> S_M02 B APIf ra empty.

Definition seg_M03_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> headamp_check_contract -> S_M03 B APIf ra empty.

Definition seg_M04_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> headamp_dup_first_contract -> headamp_plain_contract ->
  S_M04 B APIf ra empty.

Definition seg_X01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> free_contract B (APIf rc) -> S_X01 B APIf ra empty.

Theorem segs_holds : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_M04_stmt -> seg_X01_stmt ->
  headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract -> headamp_dup_first_contract ->
  headamp_plain_contract ->
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> seg_lemmas B APIf ra empty.
Proof.
  intros E01 M01 M02 M03 M04 X01 BUILD DUPPOD CHECK DUPFIRST PLAIN fx rc B APIf LS SH SK ra empty FF.
  assert (FREE : free_contract B (APIf rc)).
  { pose proof FF as H. unfold frame_facts_ubsan in H. repeat apply proj2 in H.
    destruct (H rc fx) as (_ & FRE & _). exact FRE. }
  unfold seg_lemmas.
  split; [exact (E01 fx rc B APIf LS SH SK ra empty FF)|].
  split; [exact (M01 fx rc B APIf LS SH SK ra empty FF BUILD)|].
  split; [exact (M02 fx rc B APIf LS SH SK ra empty FF DUPPOD)|].
  split; [exact (M03 fx rc B APIf LS SH SK ra empty FF CHECK)|].
  split; [exact (M04 fx rc B APIf LS SH SK ra empty FF DUPFIRST PLAIN)|].
  exact (X01 fx rc B APIf LS SH SK ra empty FF FREE).
Qed.

Theorem ubsan_halts_of_callees : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_M04_stmt ->
  seg_X01_stmt -> headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract ->
  headamp_dup_first_contract -> headamp_plain_contract -> headamp_early_contract -> Statements.ubsan_halts.
Proof.
  intros E01 M01 M02 M03 M04 X01 BUILD DUPPOD CHECK DUPFIRST PLAIN EARLY.
  exact (HeadSlot.ubsan_halts_of_frame (segs_holds E01 M01 M02 M03 M04 X01 BUILD DUPPOD CHECK DUPFIRST PLAIN) EARLY
           FrameProof.frame_ubsan_holds).
Qed.

(* The same with the n >= 2^26 run discharged by U/Prog/headamp_early.headamp_early_holds. *)
Theorem ubsan_halts_of_segs : seg_E01_stmt -> seg_M01_stmt -> seg_M02_stmt -> seg_M03_stmt -> seg_M04_stmt ->
  seg_X01_stmt -> headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract ->
  headamp_dup_first_contract -> headamp_plain_contract -> Statements.ubsan_halts.
Proof.
  intros E01 M01 M02 M03 M04 X01 BUILD DUPPOD CHECK DUPFIRST PLAIN.
  exact (ubsan_halts_of_callees E01 M01 M02 M03 M04 X01 BUILD DUPPOD CHECK DUPFIRST PLAIN
           headamp_early.headamp_early_holds).
Qed.

(* The six segment lemmas, as their files prove them. *)
Lemma seg_E01_holds : seg_E01_stmt.
Proof. intros fx rc B APIf LS SH SK ra empty FF. exact (@E01.seg_E01 fx rc B APIf LS SH SK ra empty FF). Qed.

Lemma seg_M01_holds : seg_M01_stmt.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF BUILD. exact (@M01.seg_M01 fx rc B APIf LS SH SK ra empty FF BUILD).
Qed.

Lemma seg_M02_holds : seg_M02_stmt.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF DUPPOD. exact (@M02.seg_M02 fx rc B APIf LS SH SK ra empty FF DUPPOD).
Qed.

Lemma seg_M03_holds : seg_M03_stmt.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF CHECK. exact (@M03.seg_M03 fx rc B APIf LS SH SK ra empty FF CHECK).
Qed.

Lemma seg_M04_holds : seg_M04_stmt.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF DUPFIRST PLAIN.
  exact (@M04.seg_M04 fx rc B APIf LS SH SK ra empty FF DUPFIRST PLAIN).
Qed.

Lemma seg_X01_holds : seg_X01_stmt.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF FREE. exact (@X01.seg_X01 fx rc B APIf LS SH SK ra empty FF FREE).
Qed.

(* ubsan_halts from the five evt contracts of the segments (the segment lemmas and the n >= 2^26 run discharged). *)
Theorem ubsan_halts_of_evts : headamp_build_contract -> headamp_dup_pod_contract -> headamp_check_contract ->
  headamp_dup_first_contract -> headamp_plain_contract -> Statements.ubsan_halts.
Proof.
  intros BUILD DUPPOD CHECK DUPFIRST PLAIN.
  exact (ubsan_halts_of_segs seg_E01_holds seg_M01_holds seg_M02_holds seg_M03_holds seg_M04_holds seg_X01_holds
           BUILD DUPPOD CHECK DUPFIRST PLAIN).
Qed.

(* The same with the three small evts discharged by their walks (U/Prog/headamp_dup_pod.v, headamp_dup_first.v,
   headamp_plain.v): what remains is the builder's and the check's evt contracts and the leaf callee contracts. *)
Theorem ubsan_halts_of_leaves : headamp_build_contract -> headamp_check_contract -> memcpy_c.memcpy_contract ->
  memset_c.memset_contract -> reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract ->
  check_plain_c.check_plain_contract -> Statements.ubsan_halts.
Proof.
  intros BUILD CHECK MCPY MSET PARSE CKP.
  exact (ubsan_halts_of_evts BUILD (headamp_dup_pod.headamp_dup_pod_holds MCPY) CHECK
           (headamp_dup_first.headamp_dup_first_holds MCPY) (headamp_plain.headamp_plain_holds MSET PARSE CKP)).
Qed.

(* The same with the builder discharged by U/Prog/headamp_build.headamp_build_holds and the leaf string routines by
   their walks (U/Prog/memcpy.v, memset.v, strlen.v, pod_write_ent.v): what remains is the check segment's evt
   contract and the plain parse's and check_plain's contracts. *)
Theorem ubsan_halts_of_contracts : headamp_check_contract ->
  reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract -> check_plain_c.check_plain_contract ->
  Statements.ubsan_halts.
Proof.
  intros CHECK PARSE CKP.
  pose proof memcpy.memcpy_holds as MCPY. pose proof memset.memset_holds as MSET.
  pose proof strlen.strlen_holds as STRL.
  pose proof (pod_write_ent.pod_write_ent_holds MCPY MSET) as PWE.
  exact (ubsan_halts_of_leaves (headamp_build.headamp_build_holds MSET MCPY STRL PWE) CHECK MCPY MSET PARSE CKP).
Qed.
