(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/ProgAt3.v, with its module paths, module names and numbers changed; 588 of its 649 lines of code are new or changed and 7120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/CJ/RL/GX/G_vfprintf_snf.v, with its module paths and module names changed; 16 of its 47 lines of code are new or changed and 618 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied unchanged from plugin-hostd/fuzz_reply lib/CJ/RL/GXA at 568db058c1d; only the module path prefix is rewritten to this harness. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require Import Printf_model G_printf_core_common G_vfprintf_snf.
Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Import PropExec MState Mem Exec Frame Cells Step ITree.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Import FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
Import ITree.Exc.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA Require Import SetCall.
Import ListNotations.
Open Scope Z_scope.

Definition vf_guard := mem -> Z -> Z -> Z -> Z -> Z -> nat -> Z -> Z -> Z -> Z -> list Z -> list word -> list parg -> Prop.

Section Img.
Context {IMG : RImg}.
Variable vf_ready : vf_guard.

Definition vfprintf_guarded_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (Fp CK D N OM bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells img_segs m Fp (snf_file bufp CK) ->
    rw_cells img_segs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 N)] ->
    rw_cells img_segs m D [CB dn (Z_to_bv 8 0 :: skipn 1 junkd)] -> length junkd = dn ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> args_ok Fp lo 0 CK 16 D (Z.of_nat dn) m lo q lo slots args ->
    printf_model (OUT_snf OM) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    0 <= N < 2^63 -> 0 <= OM -> Z.min N OM < Z.of_nat dn -> 0 < bufp < 2^64 ->
    stk img_segs m lo q -> lo <= q - (48 + VF_DEPTH) -> GLOBALS_TOP <= lo -> q < 2^63 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    vf_ready m q lo Fp CK D dn N bufp A VA fmt slots args ->
    A + zlength fmt <= GLOBALS_TOP -> 65536 <= A ->
    q <= Fp -> Fp + 232 <= CK -> CK + 16 <= VA -> CK + 16 < 2^63 -> VA + 8 * zlength slots <= 2^64 ->
    0 < D -> D + Z.of_nat dn < 2^63 ->
    (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt img_segs (vfprintf_snf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x7f000400)) fc None m (seg_rom img_segs)).

Definition vsnprintf_ready (set_ready : mem -> Z -> Z -> Z -> Prop)
    (m : mem) (q lo D n A VA : Z) (dn : nat) (fmt : list Z) (slots : list word) (args : list parg) : Prop :=
  forall m', munch [(lo, q); (D, D + Z.of_nat dn)] m m' -> wmono img_segs m m' ->
    set_ready m' (q - 304) (q - 304) 232 /\
    vf_ready m' (q - 304) lo (q - 304) (q - 72) D dn (n - 1) (q - 49) A VA fmt slots args.

End Img.
