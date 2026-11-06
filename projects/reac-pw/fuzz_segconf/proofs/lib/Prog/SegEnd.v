(* plain_halts of reac-pw/fuzz_segconf from the frame and the slot of LLVMFuzzerTestOneInput: reac-pw/fuzz_role's
   Prog/RoleEnd.v (commit 52bb2f1ed35d; reac-pw/fuzz_pin's Prog/PinEnd.v, libreac/fuzz_ctrl's
   released Prog/Seg/Segs.v + Prog/Seg/SlotLink.v, commit 25e3d17bdb50) for segconf's eight segments.
   - The segment lemmas, each as its segment file states it once its Section closes (Section hypotheses:
     FrameAPI.frame_facts_plain, then the contracts the segment consumes). The callee contracts of a segment's evt
     body are its premise K_<seg> (a Prop the walk states over the callees' contracts, instance-free as
     reac-pw/fuzz_role's role_build_contract is); the allocator steps use the frame's malloc_contract and
     free_contract (inside frame_facts_plain's frame_allocator) and CallocBigC.calloc_contract_big at the
     instance (E01: calloc(m); M02: calloc(tab), calloc(mt)):
       seg_E01_stmt: calloc_contract_big; seg_M01_stmt: K_M01 (reac_segconf_init); seg_L01_stmt: K_L01 (memchr);
       seg_L02_stmt: K_L02 (memcpy, snprintf, memset, m_file, reac_segconf_parse_file, m_refuse,
       reac_segconf_parse); seg_L03_stmt: none (free); seg_M02_stmt: K_M02 (check_segments, the reader's queries
       and the check_* of the segment, refusal and probe loops, snprintf, strlen, m_find, check_absent) and
       calloc_contract_big at every FP state (its cut K13ae0 holds some FP state of its own, and snprintf's post may
       change fcsr and fa0 before the two callocs); seg_V01_stmt: K_V01 (memset, memcpy, strrchr, strcmp, reac_segconf_declared,
       check_declared); seg_X01_stmt: none (free).
   - segs_holds: SegSlot's segment lemmas at the frame's concrete instance (src0_msyms, zlib_API, checksum_shape,
     src0_sink_head, src0_sink, RA_LIB, EMPTY: SegSlot.frame_facts_concrete), for every RunCeil and FP state, from
     the eight segment statements, the five evt contracts and calloc_contract_big at that instance
     (CallocHolds.calloc_holds proves it there).
   - plain_halts_of_callees: Statements.plain_halts from SegSlot.plain_halts_of_slot with these premises.
   Proves no function by itself (segment lemma of LLVMFuzzerTestOneInput's walk: the composition of
   the segment lemmas with the slot); LLVMFuzzerTestOneInput's walk is closed here modulo the eight segment lemmas,
   the five evt contracts, the calloc contract and the cut predicates CP. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YH02 YI5b YI5c YL0s YN2b.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Contract Img0 FrameAPI ZAllocator ZTraceSpec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require CallocBigC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require SegSlot.
From OSSVerify.reac_pw.fuzz_segconf Require Statements.

Section Ends.
Variable CP : cut_preds.
Variables K_M01 K_L01 K_L02 K_M02 K_V01 : Prop.

(* The segment lemmas, as the segment files state them once their Sections close. *)
Definition seg_E01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> CallocBigC.calloc_contract_big B (APIf rc) CallocBigC.CALLOC_PC ->
  S_E01 B APIf ra empty CP.

Definition seg_M01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> K_M01 -> S_M01 B APIf ra empty CP.

Definition seg_L01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> K_L01 -> S_L01 B APIf ra empty CP.

Definition seg_L02_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> K_L02 -> S_L02 B APIf ra empty CP.

Definition seg_L03_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> S_L03 B APIf ra empty CP.

Definition seg_M02_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> K_M02 ->
  (forall fx' : FPState, CallocBigC.calloc_contract_big (fx:=fx') B (APIf rc) CallocBigC.CALLOC_PC) ->
  S_M02 B APIf ra empty CP.

Definition seg_V01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> K_V01 -> S_V01 B APIf ra empty CP.

Definition seg_X01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_plain B APIf LS SH SK ra empty -> S_X01 B APIf ra empty CP.

(* calloc_contract_big at the concrete instance, for every RunCeil and FP state:
   CallocHolds.calloc_holds. *)
Definition calloc_concrete : Prop :=
  forall (fx : FPState) (rc : RunCeil),
    CallocBigC.calloc_contract_big (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc) CallocBigC.CALLOC_PC.

Theorem segs_holds : seg_E01_stmt -> seg_M01_stmt -> seg_L01_stmt -> seg_L02_stmt -> seg_L03_stmt ->
  seg_M02_stmt -> seg_V01_stmt -> seg_X01_stmt ->
  K_M01 -> K_L01 -> K_L02 -> K_M02 -> K_V01 -> calloc_concrete ->
  forall (fx : FPState) (rc : RunCeil), seg_lemmas src0_msyms (@zlib_API) RA_LIB EMPTY CP.
Proof.
  intros E01 M01 L01 L02 L03 M02 V01 X01 KM01 KL01 KL02 KM02 KV01 CAL fx rc.
  pose proof SegSlot.frame_facts_concrete as FF.
  unfold seg_lemmas.
  split; [exact (E01 fx rc _ _ _ _ _ _ _ FF (CAL fx rc))|].
  split; [exact (M01 fx rc _ _ _ _ _ _ _ FF KM01)|].
  split; [exact (L01 fx rc _ _ _ _ _ _ _ FF KL01)|].
  split; [exact (L02 fx rc _ _ _ _ _ _ _ FF KL02)|].
  split; [exact (L03 fx rc _ _ _ _ _ _ _ FF)|].
  split; [exact (M02 fx rc _ _ _ _ _ _ _ FF KM02 (fun fx' => CAL fx' rc))|].
  split; [exact (V01 fx rc _ _ _ _ _ _ _ FF KV01)|].
  exact (X01 fx rc _ _ _ _ _ _ _ FF).
Qed.

Theorem plain_halts_of_callees : seg_E01_stmt -> seg_M01_stmt -> seg_L01_stmt -> seg_L02_stmt -> seg_L03_stmt ->
  seg_M02_stmt -> seg_V01_stmt -> seg_X01_stmt ->
  K_M01 -> K_L01 -> K_L02 -> K_M02 -> K_V01 -> calloc_concrete -> Statements.plain_halts.
Proof.
  intros E01 M01 L01 L02 L03 M02 V01 X01 KM01 KL01 KL02 KM02 KV01 CAL.
  exact (SegSlot.plain_halts_of_slot CP (segs_holds E01 M01 L01 L02 L03 M02 V01 X01 KM01 KL01 KL02 KM02 KV01 CAL)).
Qed.

End Ends.
