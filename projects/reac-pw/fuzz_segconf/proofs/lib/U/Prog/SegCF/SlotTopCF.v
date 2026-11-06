(* The cut-free (agreement) slot of reac-pw/fuzz_segconf's UBSan build: lib_contract_cg for every j < 4 at the
   frame's concrete instance (src0_msyms, zlib_API, src0_sink_head, src0_sink, RA_LIB, EMPTY) and any shape LS with
   SlotInvCF.frame_facts_cf, from the cut-free copy of the slot proof (U/Prog/SlotInvCF.v, SegCF/*.v), in the form
   of reac-pw/fuzz_pin's U/Prog/SegCF/SlotTopCF.v (commit a2a7540da98), for segconf's eight
   segments:
   - the CF segment statements of the five allocator-step segments, each as its CF walk file states it once its
     Section closes (SlotInvCF.frame_facts_cf, then the contracts the segment consumes: E01 calloc_contract_cfg at
     CALLOC_PC (calloc(m)); L01 K_L01 (memchr); L03 none (free, inside frame_facts_cf); M02 K_M02 and
     calloc_contract_cfg at every FP state (calloc(tab), calloc(mt)); X01 none (free)): seg_E01_cf_stmt,
     seg_L01_cf_stmt, seg_L03_cf_stmt, seg_M02_cf_stmt, seg_X01_cf_stmt. Their proofs are the CF copies of the U
     walks U/Prog/Seg/{E01,L01,L03,M02,X01}.v (SegCF/{E01,L01,L03,M02,X01}.v);
   - the evt statements of the three evt-only segments M01, L02, V01, as the U walks prove them (U/Prog/SegEvt.v:
     frame_facts_ubsan -> K_<seg> -> evt_<seg>): evt_M01_stmt, evt_L02_stmt, evt_V01_stmt, taken at the concrete
     instance and the halts shape checksum_shape (U/Prog/SegSlot.frame_facts_concrete) and lifted to the CF segment
     statements by SegEvtCF (the evt statements do not mention the shape);
   - calloc_cf_concrete: calloc_contract_cfg at the concrete instance for every RunCeil and FP state (AgreeSeg.v
     derives it from CallocHolds.calloc_cf_holds and the zlib run-limit law);
   - segs_cf: StmtsCF.seg_lemmas at the concrete instance from these; segconf_ubsan_slot_cg:
     SegSlotCF.slot_of_lemmas with segs_cf.
   Proves no function by itself (kind: segment lemma of LLVMFuzzerTestOneInput's agreement walk: the composition of
   the cut-free segment lemmas with the cut-free slot). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YH02 YI5b YI5c YL0s YN2b.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI ZAllocator ZTraceSpec SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require CallocBigC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv SegEvt SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require SegSlot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require Import StmtsCF SegEvtCF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require SegSlotCF.
Import ListNotations.
Open Scope Z_scope.

Section EndsCF.
Variable CP : cut_preds.
Variables K_M01 K_L01 K_L02 K_M02 K_V01 : Prop.

(* The CF segment statements of the allocator-step segments. *)
Definition seg_E01_cf_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> calloc_contract_cfg B (APIf rc) CallocBigC.CALLOC_PC ->
  S_E01 B APIf ra empty CP.

Definition seg_L01_cf_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> K_L01 -> S_L01 B APIf ra empty CP.

Definition seg_L03_cf_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> S_L03 B APIf ra empty CP.

Definition seg_M02_cf_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> K_M02 ->
  (forall fx' : FPState, calloc_contract_cfg (fx:=fx') B (APIf rc) CallocBigC.CALLOC_PC) ->
  S_M02 B APIf ra empty CP.

Definition seg_X01_cf_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_cf B APIf LS SH SK ra empty -> S_X01 B APIf ra empty CP.

(* The evt statements of the evt-only segments, as the U walks prove them (U/Prog/SegEvt.v). *)
Definition evt_M01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> K_M01 -> evt_M01 B APIf ra empty CP.

Definition evt_L02_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> K_L02 -> evt_L02 B APIf ra empty CP.

Definition evt_V01_stmt : Prop :=
  forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts_ubsan B APIf LS SH SK ra empty -> K_V01 -> evt_V01 B APIf ra empty CP.

(* calloc in its CF slot form at the concrete instance, for every RunCeil and FP state. *)
Definition calloc_cf_concrete : Prop :=
  forall (fx : FPState) (rc : RunCeil),
    calloc_contract_cfg (fx:=fx) (rc:=rc) src0_msyms (@zlib_API rc) CallocBigC.CALLOC_PC.

Theorem segs_cf : seg_E01_cf_stmt -> evt_M01_stmt -> seg_L01_cf_stmt -> evt_L02_stmt -> seg_L03_cf_stmt ->
  seg_M02_cf_stmt -> evt_V01_stmt -> seg_X01_cf_stmt ->
  K_M01 -> K_L01 -> K_L02 -> K_M02 -> K_V01 -> calloc_cf_concrete ->
  forall (fx : FPState) (rc : RunCeil) (LS : lib_shape),
  frame_facts_cf src0_msyms (@zlib_API) LS src0_sink_head src0_sink RA_LIB EMPTY ->
  StmtsCF.seg_lemmas src0_msyms (@zlib_API) RA_LIB EMPTY CP.
Proof.
  intros E01 M01 L01 L02 L03 M02 V01 X01 KM01 KL01 KL02 KM02 KV01 CAL fx rc LS FF.
  pose proof U.Prog.SegSlot.frame_facts_concrete as FFu.
  unfold StmtsCF.seg_lemmas.
  split; [exact (E01 fx rc _ _ _ _ _ _ _ FF (CAL fx rc))|].
  split; [exact (S_M01_cf_of_evt src0_msyms (@zlib_API) RA_LIB EMPTY CP FF
                   (fun fx' => M01 fx' rc _ _ _ _ _ _ _ FFu KM01))|].
  split; [exact (L01 fx rc _ _ _ _ _ _ _ FF KL01)|].
  split; [exact (S_L02_cf_of_evt src0_msyms (@zlib_API) RA_LIB EMPTY CP FF
                   (fun fx' => L02 fx' rc _ _ _ _ _ _ _ FFu KL02))|].
  split; [exact (L03 fx rc _ _ _ _ _ _ _ FF)|].
  split; [exact (M02 fx rc _ _ _ _ _ _ _ FF KM02 (fun fx' => CAL fx' rc))|].
  split; [exact (S_V01_cf_of_evt src0_msyms (@zlib_API) RA_LIB EMPTY CP FF
                   (fun fx' => V01 fx' rc _ _ _ _ _ _ _ FFu KV01))|].
  exact (X01 fx rc _ _ _ _ _ _ _ FF).
Qed.

Theorem segconf_ubsan_slot_cg : seg_E01_cf_stmt -> evt_M01_stmt -> seg_L01_cf_stmt -> evt_L02_stmt ->
  seg_L03_cf_stmt -> seg_M02_cf_stmt -> evt_V01_stmt -> seg_X01_cf_stmt ->
  K_M01 -> K_L01 -> K_L02 -> K_M02 -> K_V01 -> calloc_cf_concrete ->
  forall (fx : FPState) (rc : RunCeil) (LS : lib_shape),
  frame_facts_cf src0_msyms (@zlib_API) LS src0_sink_head src0_sink RA_LIB EMPTY ->
  forall j, (j < 4)%nat ->
    lib_contract_cg (LS := LS) src0_msyms (@zlib_API rc) frame_G frame_RELRO (GI_SLOT (ms_segs src0_msyms)) j
      ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros E01 M01 L01 L02 L03 M02 V01 X01 KM01 KL01 KL02 KM02 KV01 CAL fx rc LS FF j Hj.
  exact (SegSlotCF.slot_of_lemmas src0_msyms (@zlib_API) RA_LIB EMPTY CP FF
           (segs_cf E01 M01 L01 L02 L03 M02 V01 X01 KM01 KL01 KL02 KM02 KV01 CAL fx rc LS FF) j Hj).
Qed.

End EndsCF.
