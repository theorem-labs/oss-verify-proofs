(* fuzz_state image A: the instance of a Theorem Labs lane's realloc composition (lib/Reusable/RGtop.v, relocated byte-identically
   from proofs/cgif/cgif_file_fuzzer/lib/RGtop.v @ 2bd8ae006ef, a Theorem Labs lane's c5), the invariants K1 / K2 / K3 the segment
   walks prove against, and the two non-segment obligations that are not walks: [rmodel_ok] (image-free, proved in
   lib/A/FSRealloc_rmodel.v, Required and exported here) and the copy contract [amemcpy_realizes] for musl memcpy.

   Rule 24 (released-proof lookup): a Theorem Labs lane (internal path; ossv proof
   index v5, 2026-10-28T21:58:24Z, ossv/recipes@566eb6ffa5df) answered CONFIRM for the realloc chain: no released
   ASan-image proof of any fuzz_state function.  The donor is cgif_rgb's released lib/YF78.v:553 (with YF6s-YF6u,
   YF67, YF63, YF68, YF6o, YF6p); the owner ruling (a Theorem Labs lane, 2026-10-28 23:20-23:23Z) is that fuzz_state
   walks a Theorem Labs lane's shared thin segments directly on its own images, one text.  This file is that text's instance.

   INSTANTIATION (RGtop.v Section b, in its order; A = fuzz_state.asan, sha256 64b53ff86172bb07...).
     segs  := tfibsegs                         (A/AB1v.v: Asan.M.loaded_segments of the pinned A image)
     B     := Section variable [B] (fs's symbols; every fs contract takes it)
     U     := FS_U B: `In tr (as_universe B) \/ st_nev S < EV_MAX`, fs's C5 trace premise, at the Allocate and the
              Deallocate calls (FSRealloc_rmodel.v; as YG0d.amalloc_realizes and FSupoisonU's contracts state it)
     mt    := YG00.malloc,  ft := YG00.free    (the realloc tree of A/FSH_ReallocModel.v, the model of record on S0:
                                                free PNull ;; malloc n ;; free p)
     ARX   := fun inst ly S W mem md => inst = TFIB_INST /\ FSupoison.ARU tfibsegs B ly S Up W mem md
              (the any-user-poison invariant; the poison set [Up] is a Section variable, the same set before and after
              the call)
     AOX   := aowned B
     rpre  := FS_rpre B (FSRealloc_rmodel.v): Wf Un S /\ qmeter S /\ aregime3 S n (FSH_ReallocModel.arealloc_realizes_all's
              premises acall_pre (whose AR gives Wf and which carries qmeter) and aregime3)
     nmax  := MALLOC_MAX, lmax := LIVE_MAX, lpost := qtight   (FSH_ReallocModel.arealloc_realizes_all / arealloc_leaf)
     fpre  := FS_fpre: no range of Up meets the released old block (the range premise of FSupoisonU.afree_realizesU;
              at fs's call site FSupoisonU.ARU_free_outside gives it, since fuzz_realloc unpoisons the head first)
     rU    := FS_rU B: `In tr (as_universe B) \/ (length tr <= kUnwindMax /\ st_nev S + 2 < EV_MAX)` (realloc's entry
              premise; FSupoisonRealloc.arealloc_realizesU's trace premise gives it with call_trace_len)
     RSTACK := FS_RFRAME = 0x8a0  (realloc's own frames down to Reallocate's sp, below; Allocate's alloc_pre asks
              `ly_bot ly < spZ regsA` at spZ regsA = spZ regs - FS_RFRAME)
     rpreA := FS_rpreA (FSRealloc_rmodel.v): aregime S /\ qmeter S        (Allocate's premise; = AllocGcgif.rpre_cgif)
     rpreD := FS_rpreD (FSRealloc_rmodel.v): aregime S /\ qmeter S /\ st_internal_inited S = true   (Deallocate's)
     pcR   := FS_AREALLOC_PC_A   = 0x53078  __wrap_realloc, `j 0x53474` (3fc0006f)
     pc0   := FS_AREALLOC_IPC_A  = 0x535b0  return pc of the SECOND `jal StackTrace::GetCurrentPc` 0x535ac (314200ef
              jal 0x20314 -> 0x738c0), the long branch taken with malloc_context_size = 30 (`addi a1, zero, 2` 0x53574,
              `bltu a1, a0` 0x53578); the short-branch call 0x53590 returns to 0x53594, which the originals never record
     inst  := TFIB_INST          = 0xa48d8  asan_realloc: `auipc a0, 0x72` 0x32904 + `addi a0, a0, -0x2c` 0x32908
              (also 0x328d4 + `addi a0, a0, 4` 0x328e0 and 0x328a8 + `addi a0, a0, 0x30` 0x328ac)
     oomb  := TFIB_OOM           = 0x12a1a0 Allocate's `jal 0x5edf8` at 0x32264; 0x5edf8 `auipc a0, 0xcb` (=0x129df8),
              `addi a1, zero, 1`, `sb a1, 0x3a8(a0)` (0x129df8 + 0x3a8)
     pcM   := tfib_A_memcpy = 0x98a20  REAL(memcpy): Reallocate `auipc a0, 0x6d` 0x329d4 + `ld a0, -0x2bc(a0)`
              (GOT 0x9f718 = tfib_D_REAL_memcpy's slot) -> `ld a3, 0(a0)` (cell 0xa1568 = tfib_D_REAL_memcpy, holding
              0x98a20) -> `jalr a3` 0x32a08
     pcA   := tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb   = 0x31ef4  (Reallocate `jal -0xa9c` 0x32990)
     pcD   := tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE = 0x31be0  (Reallocate `jal -0xe44` 0x32a24)

   fuzz_state never calls realloc with p = NULL (fuzz_realloc routes NULL to fuzz_malloc, a Theorem Labs lane), so
   [rg_realloc_null], its invariant Kn and its segments S5 / S6 are NOT needed for fs's arealloc_realizes_all; this
   file defines no Kn.  [fs_rg_realloc_all] below is rg_realloc_all at this instance with its non-segment obligations
   discharged: fs_rmodel_ok (FSRealloc_rmodel.v), fs_amemcpy_realizes (below) and the errno tie
   `as_errno B = as_tp B - 0xa4` (fs_errno_tp, from TfibSyms: ts_errno 0x5dae8c = ts_tp 0x5daf30 - 0xa4).  What remains is
   the Allocate contract (AllocG.aalloc_realizes) and the RAW Deallocate contract (DeallocG.adealloc_realizes_raw, c5's
   DPOST := dealloc_post_raw; fs supplies a Theorem Labs lane's DIfaceR beside DIface for it), a Theorem Labs lane's AG* / DG* walks, and the five
   segments S1, S2a, S2b, S3, S4 (lib/A/FSRealloc_S*.v; composed in lib/A/FSRealloc_top.v).

   THE SEGMENT TARGETS ON A (capstone over the pinned A image; RV64, no compressed instructions).
     S1  seg_pre K1:     start cfg_at 0x53078 (__wrap_realloc `j 0x53474`) -> __interceptor_realloc 0x53474 (frame
                         0x7f0 + 0x70) -> `jal 0x738c0` 0x535ac (pc0 = 0x535b0) -> `jal 0x5ae10` (UnwindImpl) 0x53608,
                         return 0x5360c -> `jal asan_realloc` 0x5361c -> asan_realloc 0x3287c (frame 0x10; `beqz a0`
                         0x3288c and `bnez a3` 0x32894 -> 0x32904) -> `jal Reallocate` 0x32914 -> Reallocate 0x32928
                         (frame 0x30; CHECKs `beqz a1` 0x32944, `beqz a2` 0x3294c; `jal 0x5ba44` 0x3295c, thread stats
                         0x32960-0x32974).  End: Reallocate's `jal Allocate` 0x32990, i.e. cfg_at 0x31ef4 with
                         ra = 0x32994, a0 = inst, a1 = n, a2 = 8, a3 = so, a4 = a5 = 1.
     S2a seg_mid_a K1 K2: start cfg_at 0x32994 (Allocate's return; `mv s4, a0`, `beqz a0` 0x32998 not taken), the
                         chunk-state check `lb a0, -0x10(s1)` 0x3299c (= 2, CHUNK_ALLOCATED), REAL(memcpy) load 0x329d4-
                         0x329dc (`beqz a3` 0x329e0 not taken), UsedSize `lhu -0xe(s1)` / `lwu -0xc(s1)` 0x329e4-0x329f0,
                         min 0x329f4-0x329f8.  End: `jalr a3` 0x32a08, i.e. cfg_at 0x98a20 with ra = 0x32a0c,
                         a0 = q, a1 = p, a2 = min(UsedSize, n).
     (copy) amemcpy_realizes: 0x98a20 -> 0x32a0c (proved below).
     S2b seg_mid_b K2 K3: start cfg_at 0x32a0c (`addi a5, zero, 1`).  End: `jal Deallocate` 0x32a24, i.e. cfg_at 0x31be0
                         with ra = 0x32a28, a0 = inst, a1 = p, a2 = a3 = 0, a4 = so, a5 = 1.
     S3  seg_ret K3:     start cfg_at 0x32a28 (`mv a0, s4`), Reallocate's epilogue to `ret` 0x32a48 -> asan_realloc
                         0x32918 (`beqz a0` not taken) ret 0x32924 -> interceptor 0x53620 epilogue, `ret` 0x53648.
                         End: cfg_at (raZ regs) with a0 = q.
     S4  seg_nret K1:    start cfg_at 0x32994 with a0 = 0 (`beqz a0` 0x32998 taken -> 0x32a28), Reallocate's epilogue
                         -> asan_realloc 0x32918 `beqz a0` taken -> 0x328f8 `jal 0x6ccd4` (errno := 12: `jal 0x8c744`,
                         `addi a1, zero, 0xc`, `sw a1, 0(a0)`) -> `j 0x328c4` (`mv a0, zero`), ret 0x328d0 -> interceptor
                         0x53620 epilogue, `ret` 0x53648.  End: cfg_at (raZ regs) with a0 = 0.
     S5 / S6: not needed for fs (realloc(NULL, n) never happens).

   No Axiom, no Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG03 YG06 YG07 YG08 YG0k YG0l.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x AE2y AE3c FSupoison FSH_ReallocModel.
(* the image-free instance values (FS_U, FS_rpre, FS_rpreA, FS_rpreD) and fs_rmodel_ok, shared with image B *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Export FSRealloc_rmodel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSH_ReallocModel.
(* realloc's entry pc and trace pc on A, by fs's names (A/FSH_ReallocModel.v:33-34). *)
Abbreviation FS_AREALLOC_PC_A := FSR.FS_AREALLOC_PC_A.
Abbreviation FS_AREALLOC_IPC_A := FSR.FS_AREALLOC_IPC_A.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The return pcs and frame offsets of the realloc chain on A (new literals; each checked by disassembly).          *)

(* Reallocate 0x32990 `jal -0xa9c` (d64ff0ef) -> Allocate 0x31ef4; the next instruction 0x32994 is `mv s4, a0`. *)
Definition FS_RA_ALLOC : Z := 0x32994.
(* Reallocate 0x32a08 `jalr a3` (000680e7) -> REAL(memcpy); the next instruction 0x32a0c is `addi a5, zero, 1`. *)
Definition FS_RA_COPY : Z := 0x32a0c.
(* Reallocate 0x32a24 `jal -0xe44` (9bcff0ef) -> Deallocate 0x31be0; the next instruction 0x32a28 is `mv a0, s4`. *)
Definition FS_RA_DEALLOC : Z := 0x32a28.
(* asan_realloc 0x32914 `jal 0x14` (014000ef) -> Reallocate 0x32928; the next instruction 0x32918 is `beqz a0, -0x20`. *)
Definition FS_RA_REALLOCATE : Z := 0x32918.
(* __interceptor_realloc 0x5361c `jal -0x20da0` (a60df0ef) -> asan_realloc 0x3287c; the next instruction 0x53620 is
   `addi sp, sp, 0x70`. *)
Definition FS_RA_ASAN_REALLOC : Z := 0x53620.
(* Reallocate's sp below realloc's entry sp: __interceptor_realloc 0x53474 `addi sp, sp, -0x7f0` and 0x5349c
   `addi sp, sp, -0x70`, asan_realloc 0x3287c `addi sp, sp, -0x10`, Reallocate 0x32928 `addi sp, sp, -0x30`. *)
Definition FS_RFRAME : Z := 0x8a0.
(* The interceptor's BufferedStackTrace object, below the entry sp: 0x53498 `addi s0, sp, 0x7f0` (s0 = entry sp),
   0x53548 `addi s5, s0, -0x800`, 0x5354c `addi s5, s5, -0x58`; asan_realloc / Reallocate pass it on as a3 (0x5360c /
   0x53610 `addi a2, s0, -0x800; addi a2, a2, -0x58`, 0x32884 `mv a6, a2`, 0x32910 `mv a3, a6`, 0x32950 `mv s0, a3`,
   0x3298c `mv a3, s0`).  Its trace buffer is at so + 0x10: 0x53550 / 0x53554 `addi a0, s0, -0x800; addi a0, a0, -0x48`,
   0x53568 `sd a0, 0(s5)`. *)
Definition FS_SO : Z := 0x858.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* The user-poison set: unchanged across the call (fuzz_realloc removes the old block's head before the call). *)
Variable Up : list (Z * Z).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The instance.                                                                                                     *)

Definition FS_ARX (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model)
  : Prop := inst = TFIB_INST /\ FSP.ARU tfibsegs B ly S Up W mem md.
Definition FS_fpre (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte) (p : sptr) (n : Z)
  : Prop := forall r, In r Up -> fst r + snd r <= sptr_addr B ly p \/ sptr_addr B ly p + req_size n <= fst r.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The invariants.                                                                                                   *)

(* The words realloc's frames hold below the entry sp [spZ regs] (regs = realloc's entry registers), read back by the
   epilogues of S3 / S4:
   - Reallocate's saved ra: 0x3292c `sd ra, 0x28(sp)` (ra = 0x32918), reloaded by 0x32a2c `ld ra, 0x28(sp)`;
   - asan_realloc's saved ra: 0x32880 `sd ra, 8(sp)` (ra = 0x53620; sp = Reallocate's sp + 0x30), reloaded by
     0x3291c / 0x328c8 `ld ra, 8(sp)`;
   - the interceptor's saves of the entry ra, s0-s6: 0x53478 `sd ra, 0x7e8(sp)`, 0x5347c `sd s0, 0x7e0(sp)`, 0x53480
     `sd s1, 0x7d8(sp)`, 0x53484 `sd s2, 0x7d0(sp)`, 0x53488 `sd s3, 0x7c8(sp)`, 0x5348c `sd s4, 0x7c0(sp)`, 0x53490
     `sd s5, 0x7b8(sp)`, 0x53494 `sd s6, 0x7b0(sp)` (sp = entry sp - 0x7f0), reloaded by 0x53624-0x53640 after
     0x53620 `addi sp, sp, 0x70`. *)
Definition fs_rframe (regs : bvmap 5 word) (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - FS_RFRAME + 0x28) 8 FS_RA_REALLOCATE /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - FS_RFRAME + 0x38) 8 FS_RA_ASAN_REALLOC /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - 8) 8 (raZ regs) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)).

(* The interceptor's stack object [so] = entry sp - FS_SO and its trace buffer so + 16 hold the trace [tr], in the
   form alloc_pre / dealloc_pre ask (AllocG.v:79-85, DeallocG.v:87-92): 0x53568 `sd a0, 0(s5)` (trace pointer),
   0x5356c `sd zero, 8(s5)` and the unwinder's size word, the frames written by UnwindImpl (0x53608). *)
Definition fs_trobj (regs : bvmap 5 word) (tr : list Z) (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  (1 <= length tr <= 30)%nat /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - FS_SO) 8 (spZ regs - FS_SO + 16) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - FS_SO + 8) 8 (Z.of_nat (length tr)) /\
  (forall i, (i < length tr)%nat ->
     val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs - FS_SO + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)).

(* K1: at Reallocate's `jal Allocate` 0x32990 (Allocate's entry, regsA / memA / W1).  What S2a (from Allocate's
   return with a block) and S4 (from its return with NULL) need beyond Allocate's own pre / post. *)
Definition K1_fs : K1_t tfibsegs :=
  fun ly S W regs mem md p n_old n ch S1 W1 regsA memA mdA =>
  (* the `jal` at 0x32990 sets ra = 0x32994: the pc where S2a / S4 start *)
  (* S1 = realloc_s1 S (fs_free_null) keeps the sections: layout_le over S1's sections weakens to S's (from a Theorem Labs lane).
     The old block's liveness at Allocate's entry, `In (p, n_old) (blocks S1)`, is c5's seg_mid_a / seg_nret premise
     (RGtop.v:269 / :330), so K1 does not carry it. *)
  (length (st_secs S) <= length (st_secs S1))%nat /\
  raZ regsA = FS_RA_ALLOC /\
  (* sp moved only by the four frame allocations (0x53474, 0x5349c, 0x3287c, 0x32928) *)
  spZ regsA = spZ regs - FS_RFRAME /\
  (* s0 = so: 0x32950 `mv s0, a3`; Allocate (aregs_preserved) keeps it for S2b's `mv a4, s0` 0x32a20 *)
  getr regsA 8 = w64 (spZ regs - FS_SO) /\
  (* s1 = p: 0x32890 `mv a1, a0` (asan_realloc), 0x32954 `mv s1, a1`; S2a reads the header at s1 - 0x10 / - 0xe /
     - 0xc and passes s1 as memcpy's a1 (0x32a00) *)
  getr regsA 9 = w64 (sptr_addr B ly p) /\
  (* s2 = inst: 0x32904 / 0x32908 `auipc a0, 0x72; addi a0, a0, -0x2c`, 0x32958 `mv s2, a0`; S2b's `mv a0, s2` 0x32a10 *)
  getr regsA 18 = w64 TFIB_INST /\
  (* s3 = n: 0x32888 `mv a3, a1`, 0x3290c `mv a2, a3`, 0x32948 `mv s3, a2`; S2a's min with UsedSize 0x329f4 *)
  getr regsA 19 = w64 n /\
  (* s7-s11: no instruction of the interceptor, asan_realloc or Reallocate writes them *)
  (forall r, 23 <= r <= 27 -> getr regsA (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  (* the saved words of the three frames, for the epilogues *)
  fs_rframe regs W1 memA /\
  (* the stack object holds the trace, for S2b's Deallocate pre-state *)
  fs_trobj regs (call_trace ly FS_AREALLOC_IPC_A regs ch) W1 memA /\
  (* realloc's 16384-byte window is present (rwin), for S4's post and the later windows *)
  rwin tfibsegs regs W1 memA /\
  (* the old block's bytes are the entry bytes (the prefix writes only stack, errno and owned bytes), for S2a's
     source-bytes clause *)
  (forall i, 0 <= i < req_size n_old ->
     aview tfibsegs (w_H W1) memA (sptr_addr B ly p + i) = aview tfibsegs (w_H W) mem (sptr_addr B ly p + i)).

(* K2: at Reallocate's `jalr a3` 0x32a08 (REAL(memcpy)'s entry, regsM / memM / W3, the state after the inner malloc
   ly2 / S2).  What S2b needs to reach Deallocate's pre-state. *)
Definition K2_fs : K2_t tfibsegs :=
  fun ly S W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM =>
  (* the `jalr a3` at 0x32a08 sets ra = 0x32a0c: the pc where S2b starts after the copy returns *)
  (* q is a real block: S3's `beqz a0` at asan_realloc 0x32918 must fall through (sptr_addr PNull = 0, YG0f.v:120);
     S2a gets it from seg_mid_a's premise `q <> PNull`, S2b carries it to K3_fs (a Theorem Labs lane, from a Theorem Labs lane) *)
  q <> PNull /\
  (* gp / tp unchanged since entry (Allocate's aregs_preserved): Deallocate's pre-state (DeallocG.v:83) needs them;
     donor YF78.v:252 mid_regs carries [3; 4; 23..27] (from a Theorem Labs lane) *)
  getr regsM 3 = w64 (as_gp B) /\ getr regsM 4 = w64 (as_tp B) /\
  (* q's block is live after the inner malloc (seg_mid_a's premise): with ARU's AR_blocks_law it puts the copy's
     window [q, q + min ..) off the stack and off owned bytes, which S2b's frame needs (donor YF78.v:187 HBQ2) *)
  In (q, n) (blocks S2) /\
  raZ regsM = FS_RA_COPY /\
  spZ regsM = spZ regs - FS_RFRAME /\
  (* s0 = so (kept by Allocate), for 0x32a20 `mv a4, s0` *)
  getr regsM 8 = w64 (spZ regs - FS_SO) /\
  (* s1 = p, for 0x32a14 `mv a1, s1` *)
  getr regsM 9 = w64 (sptr_addr B ly p) /\
  (* s2 = inst, for 0x32a10 `mv a0, s2` *)
  getr regsM 18 = w64 TFIB_INST /\
  (* s4 = q: 0x32994 `mv s4, a0` (Allocate's result), for S3's `mv a0, s4` 0x32a28 *)
  getr regsM 20 = w64 (sptr_addr B ly2 q) /\
  (forall r, 23 <= r <= 27 -> getr regsM (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  fs_rframe regs W3 memM /\
  fs_trobj regs (call_trace ly FS_AREALLOC_IPC_A regs ch) W3 memM /\
  rwin tfibsegs regs W3 memM /\
  (* the allocator relation after the inner malloc (Allocate's post), for Deallocate's pre-state *)
  FS_ARX TFIB_INST ly2 S2 W3 memM mdM /\
  (* the layout only grew, and p's address is the same under ly2 (Deallocate's a1 is p under ly2; fpre moves) *)
  layout_le (length (st_secs S)) ly ly2 /\ sptr_addr B ly2 p = sptr_addr B ly p.

(* K3: at Reallocate's `jal Deallocate` 0x32a24 (Deallocate's entry, regsD / memD / W4).  What S3 needs to return. *)
Definition K3_fs : K2_t tfibsegs :=
  fun ly S W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD =>
  (* the `jal` at 0x32a24 sets ra = 0x32a28: the pc where S3 starts *)
  (* q <> PNull: carried from K2_fs for S3's `beqz a0` at 0x32918 (see K2_fs) *)
  q <> PNull /\
  (* carried from K2_fs for S3 (from a Theorem Labs lane): q's block live (with ARX's AR_blocks_law, 4096 <= addr q, which decides
     the `beqz a0` at 0x32918 even when ly2 maps a PPrim q to an arbitrary address), and the layout growth (DPOST's
     frame needs realloc's stack window inside ly2's stack) *)
  In (q, n) (blocks S2) /\ layout_le (length (st_secs S)) ly ly2 /\
  raZ regsD = FS_RA_DEALLOC /\
  spZ regsD = spZ regs - FS_RFRAME /\
  (* s4 = q, for 0x32a28 `mv a0, s4` *)
  getr regsD 20 = w64 (sptr_addr B ly2 q) /\
  (forall r, 23 <= r <= 27 -> getr regsD (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  fs_rframe regs W4 memD /\
  rwin tfibsegs regs W4 memD.

(* The segment hypotheses at this instance: the targets of the segment lanes (pcs in the header). *)
Definition FS_seg_pre : Prop :=
  seg_pre tfibsegs B (FS_U B) YG00.free FS_ARX (aowned B) (FS_rpre B) MALLOC_MAX LIVE_MAX FS_fpre (FS_rU B) FS_RFRAME
    FS_rpreA FS_AREALLOC_PC_A FS_AREALLOC_IPC_A TFIB_INST tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb K1_fs.
Definition FS_seg_mid_a : Prop :=
  seg_mid_a tfibsegs B (FS_U B) FS_ARX (aowned B) (FS_rpre B) MALLOC_MAX LIVE_MAX qtight FS_fpre (FS_rU B) FS_RFRAME
    FS_rpreA FS_rpreD FS_AREALLOC_IPC_A TFIB_INST tfib_A_memcpy K1_fs K2_fs.
Definition FS_seg_mid_b : Prop :=
  seg_mid_b tfibsegs B (FS_U B) FS_ARX (FS_rpre B) MALLOC_MAX LIVE_MAX FS_fpre (FS_rU B) FS_RFRAME FS_rpreD
    FS_AREALLOC_IPC_A TFIB_INST tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE K2_fs K3_fs.
Definition FS_seg_ret : Prop :=
  seg_ret tfibsegs B (FS_U B) FS_ARX (aowned B) (FS_rpre B) MALLOC_MAX LIVE_MAX qtight FS_fpre (FS_rU B) FS_RFRAME
    FS_rpreD FS_AREALLOC_IPC_A TFIB_INST K3_fs.
Definition FS_seg_nret : Prop :=
  seg_nret tfibsegs B (FS_U B) FS_ARX (aowned B) (FS_rpre B) MALLOC_MAX LIVE_MAX qtight FS_fpre (FS_rU B) FS_RFRAME
    FS_rpreA FS_AREALLOC_IPC_A TFIB_INST TFIB_OOM K1_fs.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The copy contract: REAL(memcpy) = musl memcpy 0x98a20, from the in-tree leaf A/AE3c.v (tfib_memcpy, the machine run
   AE30.v's __asan_memcpy walk uses at MC_REAL = 0x98a20), lifted to SRr as AE30.v:842 (mc_tail) does.               *)

Theorem fs_amemcpy_realizes : amemcpy_realizes tfibsegs tfib_A_memcpy.
Proof.
intros W regs mem md d x n (RA & G10 & G11 & G12 & Hn0 & Hd0 & Hdn & Hx0 & Hxn & HDISJ & HWR & HRD).
set (H := w_H W) in *.
assert (Hnb : n < 2 ^ 64) by lia.
assert (DW : forall a, d <= a < d + n -> H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (H (Z_to_bv 64 a)) eqn:Hh; [|reflexivity]. exfalso.
  exact (AE2y.hidden_not_writable W mem a ltac:(lia) Hh (HWR a Ha)). }
destruct (AE2y.rdn_of_vis (mrestrict H mem) x (Z.to_nat n) Hx0 ltac:(lia)) as (bs & RDN & LEN & BS).
{ intros i Hi. apply (proj1 (AF0x.aview_vis H mem (x + i))). apply HRD. lia. }
assert (LENZ : Z.of_nat (length bs) = n) by lia.
(* the words' values: exact when the range is not empty, and in range in any case *)
assert (WD : bv_unsigned (w64 d) + n <= 2 ^ 64 /\ (0 < n -> bv_unsigned (w64 d) = d)).
{ destruct (Z.eq_dec n 0) as [N0|N0]; [pose proof (u64_range (w64 d)); split; lia|].
  unfold w64. rewrite unsigned_lit_small by lia. split; lia. }
assert (WX : bv_unsigned (w64 x) + n <= 2 ^ 64 /\ (0 < n -> bv_unsigned (w64 x) = x)).
{ destruct (Z.eq_dec n 0) as [N0|N0]; [pose proof (u64_range (w64 x)); split; lia|].
  unfold w64. rewrite unsigned_lit_small by lia. split; lia. }
assert (WDISJ : bv_unsigned (w64 d) + Z.of_nat (length bs) <= bv_unsigned (w64 x) \/
                bv_unsigned (w64 x) + Z.of_nat (length bs) <= bv_unsigned (w64 d)).
{ rewrite LENZ. destruct (Z.eq_dec n 0) as [N0|N0]; [subst n; lia|].
  rewrite (proj2 WD), (proj2 WX) by lia. exact HDISJ. }
assert (SOK : store_ok tfibsegs (mrestrict H mem) (w64 d) (length bs) = true).
{ apply store_ok_of_all; [rewrite LENZ; exact (proj1 WD)|].
  intros z Hz. rewrite LENZ in Hz. destruct (Z.eq_dec n 0) as [N0|N0]; [lia|].
  rewrite (proj2 WD) in Hz by lia.
  pose proof (HWR (bv_unsigned z) ltac:(lia)) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (AE3c.tfib_memcpy bs (w64 d) (w64 x) (w64 n) (mrestrict H mem) (seg_rom tfibsegs) regs G10 G11 G12
  ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) ltac:(rewrite LEN; exact RDN) SOK
  ltac:(rewrite LENZ; exact (proj1 WD)) ltac:(rewrite LENZ; exact (proj1 WX)) WDISJ)
  as (regs2 & Hms & _ & Hkeep).
set (mem2 := munrestrict H mem (wbytes (mrestrict H mem) (w64 d) bs)).
assert (M2out : forall z : word, ~ (d <= bv_unsigned z < d + n) -> mem2 z = mem z).
{ intros z Hz. unfold mem2, munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
  destruct (Z.eq_dec n 0) as [N0|N0].
  - assert (E0 : bs = []) by (destruct bs; [reflexivity | cbn in LENZ; lia]). subst bs. cbn [wbytes].
    unfold mrestrict. rewrite Hh. reflexivity.
  - pose proof (proj2 WD ltac:(lia)) as Ed. pose proof (u64_range z).
    destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L].
    + rewrite wbytes_below; [unfold mrestrict; rewrite Hh; reflexivity | rewrite LENZ; exact (proj1 WD) | lia].
    + rewrite wbytes_above; [unfold mrestrict; rewrite Hh; reflexivity | rewrite LENZ; lia]. }
assert (M2in : forall z : word, d <= bv_unsigned z < d + n -> mem2 z = Some (nth (Z.to_nat (bv_unsigned z - d)) bs 0%bv)).
{ intros z Hz. pose proof (proj2 WD ltac:(lia)) as Ed. unfold mem2, munrestrict.
  rewrite <- (Z_to_bv_bv_unsigned 64 z), (DW (bv_unsigned z) Hz), Z_to_bv_bv_unsigned.
  rewrite (AE2y.wbytes_inside bs (mrestrict H mem) (w64 d) z); rewrite ?LENZ, ?Ed; [|lia | lia].
  apply nth_error_nth'. lia. }
unfold cfg_at.
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. apply SRr_ret. split; [reflexivity|].
exists regs2, mem2, model'.
split.
{ replace (w64 (raZ regs)) with (v_jalr (getr regs 1) 0) by (rewrite RA; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  reflexivity. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
  apply Hkeep; intros E; apply (f_equal (@bv_unsigned 5)) in E; vm_compute in E; discriminate E. }
split; [exact Hsbm|].
split.
{ intros i Hi. unfold aview.
  assert (Ed : bv_unsigned (w64 d) = d) by exact (proj2 WD ltac:(lia)).
  replace (mbyte tfibsegs (mrestrict H mem2) (d + i)) with (Some (nth (Z.to_nat i) bs 0%bv)).
  2:{ unfold mbyte, mrestrict. rewrite (DW (d + i) ltac:(lia)).
      rewrite (M2in (Z_to_bv 64 (d + i))); rewrite unsigned_lit_small by lia; [|lia].
      replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia. reflexivity. }
  replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. rewrite (BS (Z.to_nat i) ltac:(lia)). reflexivity. }
(* the frame on the raw memory (c5's amemcpy_realizes, ReallocG.v:250): M2out *)
split; [exact M2out|].
intros a (Hh & b & Hb). split; [exact Hh|].
destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 a)) d) as [L1|L1];
[|destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 a)) (d + n)) as [L2|L2]].
- exists b. rewrite M2out by lia. exact Hb.
- eexists. apply M2in. lia.
- exists b. rewrite M2out by lia. exact Hb.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* RGtop's rg_realloc_all at this instance, with rmodel_ok, the copy contract and the errno tie discharged: what
   remains is the Allocate contract and the raw Deallocate contract (a Theorem Labs lane's AG* / DG* walks at fs's ARX) and the
   five segments S1-S4 (discharged in lib/A/FSRealloc_top.v).                                                       *)

(* errno is the musl thread slot at tp - 0xa4 (RGtop's seg_nret / rg_realloc_all premise): ts_errno 0x5dae8c,
   ts_tp 0x5daf30 (A/AF0m.v) *)
Lemma fs_errno_tp : TfibSyms B -> as_errno B = as_tp B - 0xa4.
Proof. intros TB. rewrite (ts_errno B TB), (ts_tp B TB). unfold TFIB_ERRNO, TFIB_TP. lia. Qed.

Theorem fs_rg_realloc_all : TfibSyms B ->
  aalloc_realizes tfibsegs B (FS_U B) YG00.malloc FS_ARX (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb TFIB_OOM 8 1 1 ->
  adealloc_realizes_raw tfibsegs B (FS_U B) YG00.free FS_ARX (aowned B) FS_rpreD qtight FS_fpre
    tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE 1 ->
  FS_seg_pre -> FS_seg_mid_a -> FS_seg_mid_b -> FS_seg_ret -> FS_seg_nret ->
  arealloc_realizes_all tfibsegs B YG00.malloc YG00.free FS_ARX (aowned B) (FS_rpre B) MALLOC_MAX LIVE_MAX qtight
    FS_fpre (FS_rU B) FS_RFRAME FS_AREALLOC_PC_A FS_AREALLOC_IPC_A TFIB_INST TFIB_OOM.
Proof.
intros TB HA HD S1 S2a S2b S3 S4.
exact (rg_realloc_all tfibsegs B (FS_U B) YG00.malloc YG00.free FS_ARX (aowned B) (FS_rpre B) MALLOC_MAX LIVE_MAX qtight
  FS_fpre (FS_rU B) FS_RFRAME FS_rpreA FS_rpreD FS_AREALLOC_PC_A FS_AREALLOC_IPC_A TFIB_INST TFIB_OOM tfib_A_memcpy
  tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE K1_fs K2_fs K3_fs (fs_errno_tp TB) HA HD fs_amemcpy_realizes
  (fs_rmodel_ok B (ts_universe B TB)) S1 S2a S2b S3 S4).
Qed.

End i.
