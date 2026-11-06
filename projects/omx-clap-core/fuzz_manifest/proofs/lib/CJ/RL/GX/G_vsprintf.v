(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/P/F_vsnprintf.v, with its module paths, module names and numbers changed; 66 of its 99 lines of code are new or changed and 1368 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Import SFModel Arr ITree Nodes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.GX Require Import G_vfprintf_snf G_vsnprintf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Import StoreCache.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition vsprintf_prog (B B_vsnprintf : Z) : RStep.ptree :=
  PLeaf
      (PJ_OpImm_ALU_ADD_nnn 0 13 12 0 4
      (PJ_OpImm_ALU_ADD_nnn 4 12 11 0 4
      (PJ_Lui_nn 8 11 524288 4
      (PJ_OpImm32_nnn 12 11 11 4095 4
      (PJ_Jal_nt 16 0 (jimm21 (B_vsnprintf - (B + 16))) 4 nil))))).
Definition vsprintf_size : Z := 20.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PROGAT_CODE_vsprintf (IMG : RImg) := vsprintf_prog (sym 0x7f000600) (sym 0x7f000200).

Section Img.
  Context {IMG : RImg}.
  Context {CODE_vsprintf : CodeAtT img_segs (sym 0x7f000600) (PROGAT_CODE_vsprintf IMG)}.
  Context {RB_vsprintf : RelCode (sym 0x7f000600) 20}.
  Context {RN_vsnprintf : RelNear (sym 0x7f000600) (sym 0x7f000200)}.
  Context (VSN : vsnprintf_x_stmt).

Definition vsprintf_x_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells img_segs m D [CB dn junkd] -> Z.of_nat dn = zlength o + 1 ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> args_ok lo lo 0 lo 0 D (Z.of_nat dn) m lo q lo slots args ->
    printf_model (OUT_snf (zlength o)) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    zlength o < 2^31 - 1 ->
    stk img_segs m lo q -> lo <= q - VSN_DEPTH -> GLOBALS_TOP <= lo -> q < 2^63 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    A + zlength fmt <= STATIC_SPLIT -> 65536 <= A ->
    q <= VA -> VA + 8 * zlength slots <= 2^64 ->
    0 < D -> D + Z.of_nat dn < 2^63 ->
    (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt img_segs (vsnprintf_x_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn (zb o ++ [Z_to_bv 8 0]) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x7f000600)) fc None m (seg_rom img_segs)).

Theorem vsprintf_x_proof : vsprintf_x_stmt.
Proof.
  unfold vsprintf_x_stmt. intros until o. cbv zeta.
  intros -> -> -> DST HDN BY HF P1 VAA AOK MODEL Ho ST LO GLO QHI SSP MI FRM HA HA0 QVA VAHI D0 DHI DD1 DD2.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  do 5 zs.
  pose proof VSN as V. unfold vsnprintf_x_stmt in V. cbv zeta in V.
  eapply evt_mono.
  { eapply V with (n := 2147483647) (D := D) (A := A) (VA := VA) (dn := dn) (junkd := junkd) (fmt := fmt)
                  (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      clear V; first [ reflexivity | eassumption | (unfold zlength in *; lia) ]. }
  intros ms' P.
  replace (firstn (Z.to_nat (2147483647 - 1)) o) with o in P
    by (symmetry; apply firstn_all2; unfold zlength in Ho; lia).
  exact P.
Qed.

End Img.
