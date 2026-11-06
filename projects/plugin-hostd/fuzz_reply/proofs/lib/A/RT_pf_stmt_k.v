(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/F_vsnprintf.v, with its module paths and module names changed; 91 of its 113 lines of code are new or changed and 2118 lines of the source are left out. *)
(* fuzz_reply.asan's snprintf interceptor chain, KEEP-FX statements: RT_pf_stmt.v's vsnprintf_icpt_stmt /
   snprintf_icpt_stmt with the floating-point state KEPT and no rounding-mode premise.

   Why (SNP-ROUTE.md (sha256 5a5fabe9f628; internal record) section 7.5, the ruling): the integrated W_sites.v asnprintf_realizes returns at the same FP
   state (cfg_at at the Section's fx) and takes no frm0 premise.  GXA's released posts (G_vsnprintf.v:146-156
   vsnprintf_x_post) only say `exists Ft fc', frm0 fc' /\ Ft k = F k for k <> 10`, which is slack: under the snprintf
   model the float arm never runs (OUTFP_snf := Ret Unr, GX/G_printf_core_common.v:392) and pop_arg keeps F for
   every non-DBL type (G/G_pop_arg.v:559-573).  The chain is proved keep-fx from the scripted GXA keep-fx twin;
   this file only states it.

   Every premise is RT_pf_stmt.v's (at the same position) except `frm0 fc`, which is dropped; every post is
   vsnprintf_k_post: the caller's FP registers F and fcsr fc unchanged.  The vocabulary is the released GXA one
   (vf_guard, vsnprintf_ready, args_ok, printf_model) so that the seam's readiness lemmas, stated over it, apply. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_IImgA RT_pf_Tbl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_bz.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module BzM2 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Module PB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_bz.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.

#[local] Existing Instance A_img.

(* GXA's vsnprintf_x_post (G_vsnprintf.v:146-156) with Ft := F and fc' := fc: the FP state is the caller's. *)
Definition vsnprintf_k_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (dn : nat) (txt : list byte) (r : Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells img_segs m' D [CB dn txt].

(* the keep-fx post gives GXA's post whenever the entry rounding mode is 0 *)
Lemma vsnprintf_k_post_x : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dn txt r lo canary m ms,
  frm0 fc ->
  vsnprintf_k_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dn txt r lo canary m ms ->
  @vsnprintf_x_post A_img ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn txt r lo canary m ms.
Proof.
  intros until ms. intros FR (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & H).
  unfold vsnprintf_x_post.
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m'.
  destruct H as (MU & WM & MI & ST & SSP & DST).
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|].
  split; [intros k _; reflexivity|]. split; [exact ST|]. split; [exact SSP|]. exact DST.
Qed.

(* ---- ___interceptor_vsnprintf at `entry`: RT_pf_stmt.v:124-154 without frm0, keep-fx post ---- *)
Definition vsnprintf_icpt_stmt_k (set_ready : mem -> Z -> Z -> Z -> Prop) (vf_ready : vf_guard) (entry : Z) : Prop :=
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
    stk img_segs m lo q -> lo <= q - PS.VSNI_DEPTH -> GLOBALS_TOP <= lo -> BzM2.kHighShadowEnd + 8 <= lo ->
    q <= 2^47 -> q mod 16 = 0 ->
    ssp_cells m canary -> mem_inv img_segs m ->
    A + zlength fmt <= GLOBALS_TOP -> 65536 <= A ->
    q <= VA -> VA + 8 * zlength slots <= 2^64 ->
    0 < D -> D + Z.of_nat dn < 2^63 -> D + Z.min n (r + 1) <= 2^47 ->
    (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    PB.sni_cells m ->
    (forall m', munch [(q - (PF_VSN_FRAME + PF_TRYINIT), q)] m m' -> wmono img_segs m m' -> mem_inv img_segs m' ->
       va_area m' VA slots -> PB.pcom_pre A VA (q - PF_VSN_FRAME) m') ->
    PS.icpt_ready set_ready vf_ready m q lo (q - PF_VSN_FRAME) D n A VA dn fmt slots args r ->
    ret_pc ra <> Z_to_bv 64 PF_WRAP_VSNPRINTF ->
    evt img_segs (vsnprintf_k_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dn
                    (zb (firstn (Z.to_nat (n - 1)) o) ++ [Z_to_bv 8 0]) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 entry) fc None m (seg_rom img_segs)).

(* ---- snprintf at __wrap_snprintf 0x421dc: RT_pf_stmt.v:158-186 without frm0, keep-fx post ---- *)
Definition snprintf_icpt_stmt_k (set_ready : mem -> Z -> Z -> Z -> Prop) (vf_ready : vf_guard) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (xs : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
    rw_cells img_segs m D [CB dn junkd] -> Z.of_nat dn = Z.min (zlength o) (n - 1) + 1 ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    bytes_at img_segs m q (u64s xs) -> q + 8 * zlength xs <= 2^64 -> PS.snf_spill_ok xs ->
    args_ok lo lo 0 lo 0 D (Z.of_nat dn) m lo q lo ([a3; a4; a5; a6; a7] ++ xs) args ->
    printf_model (OUT_snf (zlength o)) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    0 <= r -> r + 1 < 2^31 -> 1 <= n < 2^31 ->
    stk img_segs m lo q -> lo <= q - PS.SNI_DEPTH -> GLOBALS_TOP <= lo -> BzM2.kHighShadowEnd + 8 <= lo ->
    q <= 2^47 -> q mod 16 = 0 ->
    ssp_cells m canary -> mem_inv img_segs m ->
    A + zlength fmt <= GLOBALS_TOP -> 65536 <= A ->
    0 < D -> D + Z.of_nat dn < 2^63 -> D + Z.min n (r + 1) <= 2^47 ->
    (D + Z.of_nat dn <= lo \/ q + 8 * zlength xs <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    PB.sni_cells m ->
    (forall m', munch [(q - (PF_SNF_FRAME + PF_VSN_FRAME + PF_TRYINIT), q)] m m' -> wmono img_segs m m' ->
       mem_inv img_segs m' -> va_area m' (q - PF_SPILL) ([a3; a4; a5; a6; a7] ++ xs) ->
       PB.pcom_pre A (q - PF_SPILL) (q - PF_SNF_FRAME - PF_VSN_FRAME) m') ->
    PS.icpt_ready set_ready vf_ready m q lo (q - PF_SNF_FRAME - PF_VSN_FRAME) D n A (q - PF_SPILL) dn fmt
      ([a3; a4; a5; a6; a7] ++ xs) args r ->
    evt img_segs (vsnprintf_k_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dn
                    (zb (firstn (Z.to_nat (n - 1)) o) ++ [Z_to_bv 8 0]) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_WRAP_SNPRINTF) fc None m (seg_rom img_segs)).

(* the keep-fx statement gives RT_pf_stmt.v's (a sanity check that it is the stronger text) *)
Lemma snprintf_icpt_stmt_k_x : forall set_ready vf_ready,
  snprintf_icpt_stmt_k set_ready vf_ready -> PS.snprintf_icpt_stmt set_ready vf_ready.
Proof.
  intros set_ready vf_ready K. unfold PS.snprintf_icpt_stmt. intros until o. cbv zeta.
  intros E0 E1 E2 DST HDN BY HF P1 XS XH SP AOK MOD R0 R31 Hn ST LO GLO LOLO QHI Q16 SSP MI FRM HA HA0 D0 DHI DMH
    DD1 DD2 CELLS PCOM READY.
  eapply evt_mono.
  - exact (K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             D n A dn junkd fmt xs args lo canary r o E0 E1 E2 DST HDN BY HF P1 XS XH SP AOK MOD R0 R31 Hn ST LO GLO
             LOLO QHI Q16 SSP MI HA HA0 D0 DHI DMH DD1 DD2 CELLS PCOM READY).
  - intros ms H. exact (vsnprintf_k_post_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRM H).
Qed.
