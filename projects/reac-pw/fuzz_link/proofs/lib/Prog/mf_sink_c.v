(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_printf_core_common.v, with its module paths and module names changed; 89 of its 124 lines of code are new or changed and 2249 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: the FILE sink for CJ's printf_core on link's memory FILE, and the
   CJ-level statement of vfprintf on that FILE.

   1. `printf_core_stmt_heap`: CJ's `printf_core_stmt` (lib/CJ/RL/GX/G_printf_core_common.v :305-330),
      word for word, with one last disjunct added to each of the two premises that place the FILE (:320)
      and its buffer (:321): the FILE and the buffer may also lie below the caller's frame (`<= lo`), in
      the first 64 KiB with the format in .rodata, or above the image's writable segments (GLOBALS_TOP).
      link's FILE is a malloc block (fmemopen), so it takes that arm. The destination premise (:324-325)
      carries the libc walk's 4th window (GOT_GUARD_SLOT + 8 <= RE /\
      RE + RES <= STACK_GUARD; those names are only-parsing notations for sym 0x22e18 / sym 0x34288,
      written out here). The printf walk proves this generalized statement in place;
      `printf_core_heap_all` has the form of G_printf_core.v `printf_core_proof_c` with it.
   2. `SINK_mf`: the sink. St = the text printed so far (o). The FILE is at f, its 1024-byte buffer at
      f + 280 (fmemopen: buf = f + 280, buf_size = 1024); the window is active (wbase = buf,
      wend = buf + 1024) and the buffer holds the k bytes pending before the call, then o.
      `wfile` (lib/CJ/RL/G/G_fwritex.v) is the FILE as __fwritex reads it (its first 148 bytes); the
      84 bytes after them are kept as they are. OUT is CJ's `OUT_snf OM`: a piece that does not fit OM
      is the model's unreachable arm; `k + OM <= 1024` makes every piece that fits OM fit the buffer,
      so __fwritex copies it and does not call f->write.
   3. `mf_file`, `vfprintf_mf_stmt`: the 232-byte FILE as vfprintf reads and writes it, and vfprintf
      (plain 0x19ff4 = sym 0x7f000400) on it, in CJ's vocabulary: pass 1, the lock skipped (lock = -1),
      F_ERR cleared, the buffered arm (buf_size = 1024), __towrite when wend = 0, pass 2 into SINK_mf,
      no flush (saved_buf = 0), F_ERR put back, the canary. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import SFModel Arr ITree Nodes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Img.
  Context {IMG : RImg}.

(* ==========================================================================
   1. printf_core with the FILE and its buffer allowed on the heap
   ========================================================================== *)

Section Heap.
  Context {St : Type}.
  Variables (Fp B BS RC RCS RE RES : Z).
  Variable SINK : mem -> St -> Prop.
  Variable TOPOK : Z -> Prop.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

  Definition printf_core_stmt_heap : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
           (fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
      SINK m st ->
      bytes_at img_segs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
      a0 = Z_to_bv 64 Fp ->
      rw_cells img_segs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
      va_area m VA slots -> 0 <= i ->
      args_ok Fp B BS RC RCS RE RES m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
      Forall (fpcall_stmt Fp B BS RC RCS RE RES SINK TOPOK OUTFP) (fp_calls (length fmt) fmt args) ->
      stk img_segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
      (bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> (0 <= BS) ->
      (((sym 0x22e18 + 8) <= Fp /\ Fp + 232 <= (sym 0x34288)) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)
       \/ (0 < Fp /\ Fp + 232 <= lo /\ ((Fp + 232 <= 65536 /\ 65536 <= bv_unsigned a1) \/ GLOBALS_TOP <= Fp))) ->
      ((bv_unsigned a2 + 8 <= B /\ B + BS <= VA)
       \/ (0 < B /\ B + BS <= lo /\ ((B + BS <= 65536 /\ 65536 <= bv_unsigned a1) \/ GLOBALS_TOP <= B))) ->
      (0 <= RCS) -> (0 <= RES) ->
      (bv_unsigned a2 + 8 <= RC /\ RC + RCS <= VA) ->
      (((sym 0x34288 + 8) <= RE /\ RE + RES <= lo) \/ (VA <= RE /\ VA + 8 * zlength slots <= RE /\ RE + RES <= 2^64)
       \/ (0 < RE /\ RE + RES <= 65536 /\ 65536 <= bv_unsigned a1) \/ (sym 0x22e18 + 8 <= RE /\ RE + RES <= sym 0x34288)) ->
      (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      implM img_segs (printf_model OUT OUTFP fmt args) st
            (printf_core_post Fp B BS RC RCS RE RES SINK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
                              (bv_unsigned a2) lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (sym 0x18704)) fc None m (seg_rom img_segs)).
End Heap.

Definition printf_core_heap_all : Prop :=
  forall (St : Type) (Fp B BS RC RCS RE RES : Z) (SINK : mem -> St -> Prop) (TOPOK : Z -> Prop)
         (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
    sink_frame_stmt Fp B BS RC RCS RE RES SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK ->
    out_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT ->
    printf_core_stmt_heap Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP.

(* ==========================================================================
   2. The sink
   ========================================================================== *)

Section MfSink.
  Variables (f k OM : Z) (pb : list byte) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (jx : list byte).

  Definition SINK_mf (m : mem) (o : list Z) : Prop :=
    exists bjunk : list byte,
      wfile m f fl0 j1 j2 lbfw (f + 280) (pb ++ zb o) bjunk
      /\ rw_cells img_segs m (f + 148) [CB 84 jx]
      /\ Z.of_nat (length pb) = k /\ k + zlength o + zlength bjunk = 1024
      /\ zlength o <= OM /\ k + OM <= 1024
      /\ 0 < f /\ f + 1304 < 2^63 /\ (f + 1304 <= 65536 \/ GLOBALS_TOP <= f).
End MfSink.

Definition TOPOK_mf (sp : Z) : Prop := True.

(* ==========================================================================
   3. vfprintf on the memory FILE
   ========================================================================== *)

(* the FILE: flags +0, rpos +8 and rend +16 (0), wend +32, wpos +40, wbase +56, buf +88, buf_size +96
   (1024), mode +136, lock +140 (-1), lbf +144, then 84 bytes; the other bytes as they are *)
Definition mf_file (fl : word) (jp jc : list byte) (we wp : word) (j48 : list byte) (wb : word) (j64 : list byte)
    (buf : Z) (j104 : list byte) (mode lbf : word) (jx : list byte) : list cell :=
  [C4 fl; CB 4 jp; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 8 jc; C8 we; C8 wp; CB 8 j48; C8 wb; CB 24 j64;
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 1024); CB 32 j104; C4 mode; C4 (Z_to_bv 64 (-1)); C4 lbf; CB 84 jx].

Definition vfprintf_mf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (f k : Z) (fl : word) (jp jc : list byte) (we : word) (j48 j64 j104 : list byte) (mode lbf : word)
    (jx pb : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (bj : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(lo, bv_unsigned sp); (f, f + 232); (f + 280, f + 1304)] m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ (forall rk : reg, bv_unsigned rk <> 10 -> reg_get Ft rk = reg_get F rk)
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells img_segs m' f
         (mf_file fl jp jc (Z_to_bv 64 (f + 1304)) (Z_to_bv 64 (f + 280 + k + zlength o)) j48 (Z_to_bv 64 (f + 280))
                  j64 (f + 280) j104 (if bv_unsigned we =? 0 then Z_to_bv 64 4294967295 else mode) lbf jx)
    /\ rw_cells img_segs m' (f + 280) [CB (length (pb ++ zb o)) (pb ++ zb o); CB (length bj) bj]
    /\ 0 <= r <= INT_MAX.

Definition vfprintf_mf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (f k : Z) (fl : word) (jp jc : list byte) (we wp : word) (j48 : list byte) (wb : word) (j64 j104 : list byte)
         (mode lbf : word) (jx pb bjunk : list byte)
         (A VA OM : Z) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells img_segs m f (mf_file fl jp jc we wp j48 wb j64 (f + 280) j104 mode lbf jx) ->
    rw_cells img_segs m (f + 280) [CB (length pb) pb; CB (length bjunk) bjunk] ->
    Z.of_nat (length pb) = k -> Z.of_nat (length pb) + Z.of_nat (length bjunk) = 1024 ->
    ((bv_unsigned we = 0 /\ k = 0) \/
     (bv_unsigned we = f + 1304 /\ bv_unsigned wp = f + 280 + k /\ bv_unsigned wb = f + 280)) ->
    Z.land (bv_unsigned fl) 8 = 0 ->
    (bv_unsigned mode = 0 \/ bv_unsigned mode = 4294967295) ->
    (2147483648 <= bv_unsigned lbf mod 4294967296) ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> args_ok f (f + 280) 1024 lo 0 1 0 m lo q lo slots args ->
    printf_model (OUT_snf OM) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    0 <= OM -> k + OM <= 1024 ->
    stk img_segs m lo q -> lo <= q - VF_DEPTH -> GLOBALS_TOP <= lo -> q < 2^63 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    A + zlength fmt <= STATIC_SPLIT -> 65536 <= A ->
    q <= VA -> VA + 8 * zlength slots <= 2^64 ->
    0 < f -> f + 1304 <= lo -> (f + 1304 <= 65536 \/ GLOBALS_TOP <= f) ->
    evt img_segs (vfprintf_mf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F f k fl jp jc we j48 j64 j104
                                   mode lbf jx pb r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x7f000400)) fc None m (seg_rom img_segs)).

End Img.
