(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/F_vsnprintf.v, with its module paths and module names changed; 94 of its 114 lines of code are new or changed and 2120 lines of the source are left out. *)
(* Image B twin of lib/A/RT_pf_stmt.v at d49bd1db505: module paths lib.A -> lib.B; 26 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) (* fuzz_reply.asan-ubsan's snprintf interceptor chain: the STATEMENTS (evt level, GXA's form), at RT_IImgA.v's instance A_img.

   The chain (no musl snprintf frame in the ASan image; addresses and measurements in RT_pf_Tbl.v):
     __wrap_snprintf 0x42234 -> ___interceptor_snprintf 0x46928 -> ___interceptor_vsnprintf 0x46538
       -> REAL(vsnprintf) cell 0x9fcf0 -> musl vsnprintf 0x963b4
       -> __wrap_vfprintf 0x42228 -> ___interceptor_vfprintf 0x46484 + printf_common 0x459bc
       -> REAL(vfprintf) cell 0x9fce8 -> musl vfprintf 0x93288.

   THE FORM.  Every statement here has GXA's post, G_vsnprintf.v:146-156 vsnprintf_x_post: the destination holds
   zb (firstn (n - 1) o) ++ [0] (= FMsnprintfShared.v sn_bytes (n - 1) T), a0 = r, nothing outside [lo, sp) and
   [D, D + dn) changed, and every destination premise is over the written part dn = min (|o|, n - 1) + 1
   (= sn_len (n - 1) T).  This is the evt layer under a Theorem Labs lane's SRr-level contracts (a working branch
   FMsnprintfShared.v sh_asnprintf_realizesU, sh_avsnprintf_icpt_realizesU, sh_avfprintf_icpt_realizesU,
   sh_apcommon_realizesU): those are bridge (this layer) at fuzz_reply's record, with the K values below.
   The REAL(vsnprintf) call is a hypothesis in exactly GXA's statement (G_vsnprintf.v:158 vsnprintf_x_stmt, at the
   second instance A_img_vsn), so GXA's vsnprintf_x_proof plugs in there (RT_pf_vf.v snprintf_chain_ok does it).

   THE WINDOWS K (bytes below the entry sp a call may use; every value MEASURED from fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) - each
   frame from the function's own `addi sp,sp,-N` lines, each callee window from the Bz walk that charges it, which
   checks the instructions; see RT_pf_Tbl.v for the per-instruction record):
     printf_common 0x459bc           K = 2320 = frame 2032 + 208 + 80 for its callees (I_vprintfw.v PCOM_DEPTH)
     ___interceptor_vfprintf 0x42228 K = 5648 = frame 48 + max (16 TryAsanInitFromRtl, 2320 printf_common,
                                               48 + VF_DEPTH 5552 for REAL(vfprintf) = GXA's guarded body)
     ___interceptor_vsnprintf 0x4222c K = 8064 = frame 2160 + max (16, 2320, 80 output check, VSN_DEPTH 5904);
                                               8112 once the vfprintf glue is in (304 + 5648 = 5952 > 5904)
     ___interceptor_snprintf 0x42234  K = 8160 = frame 96 + 16 / + 8064;  8208 once the vfprintf glue is in
   The statements carry 8064 / 8160 (VSNI_DEPTH / SNI_DEPTH); the extra 48 is vf_ready_icpt's own premise, so it
   reaches a caller only through the vf_ready it must supply.

   THE va_start SPILL (measured, RT_pf_Tbl.v): ___interceptor_snprintf stores a3..a7 at [q-40, q) (pcs 0x4694c,
   0x46950, 0x46954, 0x46958, 0x46948) and passes va_list = q - 40, so the 6th, 7th, ... variadic words are the
   caller's stack words at [q, q + 8k).  Its geometry is fuzz_disco a Theorem Labs lane's `asan_snprintf_spill`
   (vs_off 40, vs_regs [3;4;5;6;7], vs_off = frame 0x60 - spill_post 0x38), measured identical on our image.
   HERE it is the NAMED premise snf_spill_ok (below), because this layer is CJ evt over the PLAIN BYTE MODEL
   (m : word -> option byte), where the slot predicate is forced to be GXA's own va_area (G_pop_arg.v:456), that
   being the premise of vsnprintf_x_stmt (G_vsnprintf.v:167).  A Theorem Labs lane's va_spill_words is the same fact one
   layer up, over a reader rd = aview segs (w_H W) mem (FMsnprintfShared.v:36-39, reader at YG0f.v:265).
   THE PAIRING, for the bridge owner (a Theorem Labs lane's FMgxa_bridge.v, a working branch efa2842e125 - the one place the
   two views meet):
     va_area m VA slots  <->  words_at rd (S - vs_off g) ws
     u64s slots          <->  ws = map (argZ regs) (map Z.of_nat (vs_regs g)) ++ xs  (a3..a7, then the caller's
                              stack words)
     VA                  <->  S - 40,  S = spZ regs at the snprintf entry
   WHO DISCHARGES IT: THIS FILE, for every xs - snf_spill_ok_all (below, Qed), in this layer's own model: the five
   spilled cells are bytes_at VA (u64s [a3..a7]), the caller's words are bytes_at (VA + 40) (u64s xs), and an
   append of the two at VA + 8 * 5 = VA + PF_SPILL is the va_list area.  So nobody above the bridge owes a premise
   here; snf_spill_ok stays a named premise of snprintf_icpt_stmt only so that the seam is visible, and every
   caller discharges it with snf_spill_ok_all.  The ASan-side twin of the same fact, over the reader, is
   FMsnprintfVa.v va_spill_words on a working branch 5724ded508c: ONE geometry across the units
   (a Theorem Labs lane's asan_snprintf_spill), one text per model, no gap.

   What a caller supplies besides GXA's own premises: the runtime cells (RT_pf_bz.v sni_cells, vfi_cells),
   printf_common's start premise (RT_pf_bz.v pcom_pre) at the memories the interceptors reach it in, and icpt_ready
   (GXA's vsnprintf_ready at musl vsnprintf's sp, plus the two ASan facts the output check after REAL(vsnprintf)
   reads), each over every memory the call can leave inside its window. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Import G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require Import SetCall VfprintfCall G_vsnprintf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_IImgA RT_pf_Tbl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_bz.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module BzM2 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Module BzQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Module PB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_bz.

#[local] Existing Instance A_img.

Definition VSNI_DEPTH : Z := PF_VSN_FRAME + VSN_DEPTH.                  (* 8064 *)
Definition SNI_DEPTH : Z := PF_SNF_FRAME + PF_VSN_FRAME + VSN_DEPTH.    (* 8160 *)
Definition VFI_DEPTH : Z := PF_VF_FRAME + 48 + VF_DEPTH.                (* 5648 *)

(* ---- what both interceptors ask of the memories below their window: GXA's vsnprintf_ready AT MUSL VSNPRINTF'S sp
   qv (VfprintfCall.v:46-50, at the second instance, which is where GXA's vsnprintf_x reads it), plus the two ASan
   facts the output's write check needs after REAL(vsnprintf) returns (R_m2s.v m2s_cells, and I_qck.v chk_ok over
   [D, D + min (n, r + 1)), which is ASan's WRITE_RANGE (str, min (size, res + 1))).
   It hands vsnprintf_ready ITSELF rather than its two conjuncts: an earlier form inlined the conjuncts at m', and
   then a caller had to rebuild the quantifier - one munch composition whose cost did not finish in 13 minutes in
   any of three forms, while the proof around it compiled in 18 s.  Handing the predicate removes that step. ---- *)
Definition icpt_ready (set_ready : mem -> Z -> Z -> Z -> Prop) (vf_ready : vf_guard)
    (m : mem) (q lo qv D n A VA : Z) (dn : nat) (fmt : list Z) (slots : list word) (args : list parg) (r : Z) : Prop :=
  forall m', munch [(lo, q); (D, D + Z.of_nat dn)] m m' -> wmono img_segs m m' ->
    @vsnprintf_ready A_img_vsn vf_ready set_ready m' qv lo D n A VA dn fmt slots args
    /\ BzM2.m2s_cells m' /\ BzQ.chk_ok m' D (Z.min n (r + 1)).

(* ---- the va_start spill, a NAMED premise: the spilled a3..a7 at VA and the caller's stack words xs right above
   them form the va_list area GXA reads.  Discharged for every xs by snf_spill_ok_all below. ---- *)
Definition snf_spill_ok (xs : list word) : Prop :=
  forall (m : mem) (VA : Z) (a3 a4 a5 a6 a7 : word),
    rw_cells img_segs m VA [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
    bytes_at img_segs m (VA + PF_SPILL) (u64s xs) ->
    va_area m VA ([a3; a4; a5; a6; a7] ++ xs).

(* the spill, for any number of caller stack words (a Theorem Labs lane's outline, in the plain byte model) *)
Lemma snf_spill_ok_all : forall xs, snf_spill_ok xs.
Proof.
  intros xs m VA a3 a4 a5 a6 a7 [[_ B] _] HX. unfold va_area.
  rewrite u64s_app. apply (proj2 (bytes_at_app img_segs m VA (u64s [a3; a4; a5; a6; a7]) (u64s xs))).
  split.
  - cbn [cells_bytes cbytes u64s] in B |- *. rewrite ?app_nil_r in B |- *. exact B.
  - rewrite u64s_length. cbn [length].
    replace (VA + Z.of_nat (8 * 5)) with (VA + PF_SPILL) by (unfold PF_SPILL; lia). exact HX.
Qed.

(* fuzz_reply's own sites: no stack word *)
Lemma snf_spill_ok_nil : snf_spill_ok [].
Proof. exact (snf_spill_ok_all []). Qed.

(* ---- ___interceptor_vsnprintf, entered at `entry` (__wrap_vsnprintf 0x4222c, or its body 0x46538, where
   ___interceptor_snprintf calls it) ---- *)
Definition vsnprintf_icpt_stmt (set_ready : mem -> Z -> Z -> Z -> Prop) (vf_ready : vf_guard) (entry : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells img_segs m D [CB dn junkd] -> Z.of_nat dn = Z.min (zlength o) (n - 1) + 1 ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> args_ok lo lo 0 lo 0 D (Z.of_nat dn) m lo q lo slots args ->
    printf_model (OUT_snf (zlength o)) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    0 <= r -> r + 1 < 2^31 -> 1 <= n < 2^31 ->
    stk img_segs m lo q -> lo <= q - VSNI_DEPTH -> GLOBALS_TOP <= lo -> BzM2.kHighShadowEnd + 8 <= lo ->
    q <= 2^47 -> q mod 16 = 0 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    A + zlength fmt <= GLOBALS_TOP -> 65536 <= A ->
    q <= VA -> VA + 8 * zlength slots <= 2^64 ->
    0 < D -> D + Z.of_nat dn < 2^63 -> D + Z.min n (r + 1) <= 2^47 ->
    (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    PB.sni_cells m ->
    (forall m', munch [(q - (PF_VSN_FRAME + PF_TRYINIT), q)] m m' -> wmono img_segs m m' -> mem_inv img_segs m' ->
       va_area m' VA slots -> PB.pcom_pre A VA (q - PF_VSN_FRAME) m') ->
    icpt_ready set_ready vf_ready m q lo (q - PF_VSN_FRAME) D n A VA dn fmt slots args r ->
    (* entry = the BODY 0x46538 is reached from the trampoline 0x4222c in ONE step, and that step forward needs the
       post not to hold at the trampoline state, i.e. the caller's return address is not the trampoline.  For
       entry = the trampoline this premise is unused. *)
    ret_pc ra <> Z_to_bv 64 PF_WRAP_VSNPRINTF ->
    evt img_segs (vsnprintf_x_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn
                    (zb (firstn (Z.to_nat (n - 1)) o) ++ [Z_to_bv 8 0]) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 entry) fc None m (seg_rom img_segs)).

(* ---- snprintf at __wrap_snprintf 0x42234: GX's plain snprintf_x_stmt (GX/G_snprintf.v:106-127, the variadic words
   a3..a7 then the caller's stack words xs at sp) with ASan's extra premises ---- *)
Definition snprintf_icpt_stmt (set_ready : mem -> Z -> Z -> Z -> Prop) (vf_ready : vf_guard) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (xs : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
    rw_cells img_segs m D [CB dn junkd] -> Z.of_nat dn = Z.min (zlength o) (n - 1) + 1 ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    bytes_at img_segs m q (u64s xs) -> q + 8 * zlength xs <= 2^64 -> snf_spill_ok xs ->
    args_ok lo lo 0 lo 0 D (Z.of_nat dn) m lo q lo ([a3; a4; a5; a6; a7] ++ xs) args ->
    printf_model (OUT_snf (zlength o)) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    0 <= r -> r + 1 < 2^31 -> 1 <= n < 2^31 ->
    stk img_segs m lo q -> lo <= q - SNI_DEPTH -> GLOBALS_TOP <= lo -> BzM2.kHighShadowEnd + 8 <= lo ->
    q <= 2^47 -> q mod 16 = 0 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    A + zlength fmt <= GLOBALS_TOP -> 65536 <= A ->
    0 < D -> D + Z.of_nat dn < 2^63 -> D + Z.min n (r + 1) <= 2^47 ->
    (D + Z.of_nat dn <= lo \/ q + 8 * zlength xs <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    PB.sni_cells m ->
    (forall m', munch [(q - (PF_SNF_FRAME + PF_VSN_FRAME + PF_TRYINIT), q)] m m' -> wmono img_segs m m' ->
       mem_inv img_segs m' -> va_area m' (q - PF_SPILL) ([a3; a4; a5; a6; a7] ++ xs) ->
       PB.pcom_pre A (q - PF_SPILL) (q - PF_SNF_FRAME - PF_VSN_FRAME) m') ->
    icpt_ready set_ready vf_ready m q lo (q - PF_SNF_FRAME - PF_VSN_FRAME) D n A (q - PF_SPILL) dn fmt
      ([a3; a4; a5; a6; a7] ++ xs) args r ->
    evt img_segs (vsnprintf_x_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn
                    (zb (firstn (Z.to_nat (n - 1)) o) ++ [Z_to_bv 8 0]) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_WRAP_SNPRINTF) fc None m (seg_rom img_segs)).

(* ---- ___interceptor_vfprintf as musl vsnprintf's vfprintf (G_vsnprintf.v:144's VF at A_img_vsn, whose call target
   `sym 0x7f000400` is __wrap_vfprintf 0x42228), from GXA's guarded vfprintf body at A_img (musl vfprintf 0x93288,
   G_vfprintf_snf_closed.v:117 vfprintf_snf_a_guarded_closed).  The guard adds what the interceptor needs: its
   window (VFI_DEPTH), its cells, printf_common's start premise, and the body's guard after the interceptor's front
   ([q - 2368, q) changed). ---- *)
Definition vf_ready_icpt (vfb : vf_guard) : vf_guard :=
  fun m q lo Fp CK D dn N bufp A VA fmt slots args =>
    lo <= q - VFI_DEPTH /\ BzM2.kHighShadowEnd + 8 <= lo /\ q <= 2^47 /\ q mod 16 = 0
    /\ PB.vfi_cells m
    /\ (forall m', munch [(q - (PF_VF_FRAME + PF_TRYINIT), q)] m m' -> wmono img_segs m m' -> mem_inv img_segs m' ->
          va_area m' VA slots -> PB.pcom_pre A VA (q - PF_VF_FRAME) m')
    /\ (forall m', munch [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m' -> wmono img_segs m m' ->
          vfb m' (q - PF_VF_FRAME) lo Fp CK D dn N bufp A VA fmt slots args).

Definition vf_icpt_stmt : Prop :=
  forall vfb : vf_guard, @vfprintf_guarded_stmt A_img vfb -> @vfprintf_guarded_stmt A_img_vsn (vf_ready_icpt vfb).
