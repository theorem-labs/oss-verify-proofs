(* Footprint (_F) form of reac_box_model_block_c.v at a working branch d69f7c708f6 (proved v1.9 run of
   record): definitions only, as the plain file is, so no proof script is re-run here.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes: none read (this file holds definitions only; the image
   literals it names, JOIN_0013 = 0x21a20 and JOIN_0014 = 0x21a60, come from reac_box_model_block_c.v and are
   checked in the files whose runs read them). *)

(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery), a Theorem Labs lane's rewalk-F-policy.md (a working note, not in this delivery) canonical shape): the same run as
   an ExecF.evtF under a universally quantified footprint RNG, with the premises of reac_box_model_block_contract
   unchanged and one rng premise per region the run reads or writes (instruction fetch is not an access).  The
   regions come from the steps of the run (lib/A/Prog/reac_box_model_block.v) and from the contracts of the
   callees __asan_stack_malloc_0, __asan_memset, __asan_memcpy and build_dt1_single:

     image (code, GOT, runtime words)            [0x10000, 0x5fe000)                 read
     memory-checking runtime words               [RT_LO, RT_HI)                      read/write
     own window (frame, spills, probe, callees)  [S - K, S)                          read/write
     window shadow (frame words, memset/memcpy)  8-aligned cover of its shadow       read/write, checked
     thread pointer words                        [TP - 88, TP - 80), [TP - 8, TP+16) read
     the thread cells asan_tls_cells names       reac_box_model_block_tls_rng        read
     side-stack header (hints, flags, words)     [FS, fs_frame FS 0 0)               read/write
     class-0 hint, flags, frames, frame shadow   fp_w [0] FS                         read/write
     the row (p <> 0)                            [p + 16, p + 291)                   read, checked
     the out block (p <> 0, o <> 0)              [o, o + 32)                         read/write, checked
     JOIN_0014 (b = 1) / JOIN_0013 (b = 2)       [JOIN, JOIN + 32)                   read, checked
     the name (b = 5, 6, has row, rname row)     [rname row, + length nb)            read, checked

   Each checked region also carries the 8-ALIGNED shadow word cover (sh_cover) its instrumented checks load: the
   check of a field is a load of the shadow byte at (a >> 3) + ASAN_K and a compare, and __asan_memcpy's and
   __asan_memset's quick check loads aligned shadow words.

   The side stack is NOT one region [FS, FS + FS_SIZE) (11571200 bytes; the v1.8 text of 66990ce635c had it): the
   run takes the class-0 frame only (fp [0%nat]), so it reads and writes the header [FS, fs_frame FS 0 0) (the hint
   word at FS, the words at FS + 88 and FS + 96, the class-0 flag bytes fs_flag FS 0 j) and the class-0 area
   fp_w [0%nat] FS (the hint word, the flag bytes, the frames fs_frame FS 0 j and their shadow), nothing of the
   classes 1 .. 10.  __asan_stack_malloc_0's narrow footprint form (a Theorem Labs lane) asks for the same two pieces.  The
   class-0 frame shadow premise is the fourth range of fp_w [0%nat] FS, kept in its v1.8 text. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_box_model_block_c asan_memcpy_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_classify_box_frame_c.
Import ListNotations.
Open Scope Z_scope.

(* The 8-aligned shadow word cover of [a, a + n) with n > 0 (a Theorem Labs lane's canonical form). *)
Definition sh_cover (RNG : ExecF.footprint) (a n : Z) : Prop :=
  ExecF.rng RNG (shadow_addr a / 8 * 8) (shadow_addr (a + n - 1) / 8 * 8 + 8 - shadow_addr a / 8 * 8).

(* Every byte of every range of l is in RNG.  ONE text, the auditor-signed one: this unit's shared definition at
   lib/A/Prog/reac_ctrl_classify_box_frame_c.v:116 (a contract-only file; its closure is contract files and
   lib/Lib, no frame-route and no cut-free file).  Required, not Imported, so that file's other names stay out of
   this scope; the name rng_ivls is kept for every caller. *)
Module CBF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.
Notation rng_ivls := CBF.rng_ivls.

(* The thread cells that __asan_stack_malloc_0 reads through the thread pointer.  asan_tls_cells pins each of
   DT, TS, C, T, DB and k from the bytes of m, so the premise at every witness is the premise at the witnesses of
   the run. *)
Definition reac_box_model_block_tls_rng (RNG : ExecF.footprint) (m : word -> option byte) (TP : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    ExecF.rng RNG (bv_unsigned DT + 8) 8 /\ ExecF.rng RNG (bv_unsigned TS + 8 * k) 8 /\
    ExecF.rng RNG (bv_unsigned C + 152) 8 /\ ExecF.rng RNG (bv_unsigned T + 48) 16 /\
    ExecF.rng RNG (bv_unsigned DB + 24) 8.

(* The footprint twin of reac_box_model_block_contract: the same premises, plus RNG and the nine footprint
   premises, and ExecF.evtF in place of evt. *)
Definition reac_box_model_block_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p b o FS : Z) (row nb ob : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 o ->
    0 <= p < 2^64 -> 0 <= b < 2^64 -> 0 <= o < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
               (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               name_ok nb /\ bytes_at rsegs m (rname row) nb /\
               (bv_unsigned sp <= rname row \/
                rname row + Z.of_nat (length nb) <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
    (o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
               (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    (p <> 0 -> addressable m p 296) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               addressable m (rname row) (Z.of_nat (length nb))) ->
    (o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)) ->
    reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (* the regions the run reads or writes *)
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG RT_LO (RT_HI - RT_LO) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    ExecF.rng RNG (bv_unsigned tp - 88) 8 -> ExecF.rng RNG (bv_unsigned tp - 8) 24 ->
    reac_box_model_block_tls_rng RNG m (bv_unsigned tp) ->
    ExecF.rng RNG FS (fs_frame FS 0%nat 0 - FS) -> rng_ivls RNG (fp_w [0%nat] FS) ->
    ExecF.rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8) ->
    rng_bytes RNG ->
    sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    (p <> 0 -> ExecF.rng RNG p 296) -> (p <> 0 -> sh_cover RNG p 296) ->
    (o <> 0 -> ExecF.rng RNG o 32) -> (o <> 0 -> sh_cover RNG o 32) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               ExecF.rng RNG (rname row) (Z.of_nat (length nb))) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               sh_cover RNG (rname row) (Z.of_nat (length nb))) ->
    (b = 2 -> sh_cover RNG JOIN_0013 32) ->
    (b = 1 -> sh_cover RNG JOIN_0014 32) ->
    ExecF.evtF rsegs RNG
      (reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m (seg_rom rsegs)).
(* Audit rebuild 2026-10-29 (evidence rule, the coordinating lane 04:39Z). *)
