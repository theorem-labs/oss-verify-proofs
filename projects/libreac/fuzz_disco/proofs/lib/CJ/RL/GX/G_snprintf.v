(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_syscalls.v, with its module paths, module names, addresses and numbers changed; 148 of its 186 lines of code are new or changed and 492 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import SFModel Arr ITree Nodes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Import G_vfprintf_snf G_vsnprintf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import StoreCache.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition snprintf_prog (B got_ssp B_vsnprintf B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 40%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4016 4
        (PJ_Store_SZ8_nnn 4 2 1 24 4
        (PJ_Store_SZ8_nnn 8 2 8 16 4
        (PJ_Store_SZ8_nnn 12 2 17 72 4
        (PJ_Auipc_nt 16 17 (hi20 (got_ssp - (B + 16))) 4
        (PJ_Load_SZ8_true_nnt 20 8 17 (lo12 (got_ssp - (B + 16))) 4
        (PJ_Store_SZ8_nnn 24 2 13 40 4
        (PJ_Store_SZ8_nnn 28 2 14 48 4
        (PJ_Store_SZ8_nnn 32 2 15 56 4
        (PJ_Store_SZ8_nnn 36 2 16 64 4 nil)))))))))))
    (PNode 80%Z
      (PLeaf
          (PJ_Load_SZ8_true_nnn 40 13 8 0 4
          (PJ_OpImm_ALU_ADD_nnn 44 14 2 40 4
          (PJ_Store_SZ8_nnn 48 2 13 8 4
          (PJ_Store_SZ8_nnn 52 2 14 0 4
          (PJ_OpImm_ALU_ADD_nnn 56 13 2 40 4
          (PJ_Jal_nt 60 1 (jimm21 (B_vsnprintf - (B + 60))) 4
          (PJ_Load_SZ8_true_nnn 64 11 8 0 4
          (PJ_Load_SZ8_true_nnn 68 12 2 8 4
          (PJ_Branch_BC_NE_nnn 72 11 12 20 4
          (PJ_Load_SZ8_true_nnn 76 1 2 24 4 nil)))))))))))
      (PLeaf
          (PJ_Load_SZ8_true_nnn 80 8 2 16 4
          (PJ_OpImm_ALU_ADD_nnn 84 2 2 80 4
          (PJ_Jalr_nnn 88 0 1 0 4
          (PJ_Jal_nt 92 1 (jimm21 (B_stack_chk_fail - (B + 92))) 4 nil)))))).
Definition snprintf_size : Z := 96.

Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PROGAT_CODE_snprintf (IMG : RImg) :=
  snprintf_prog (sym 0x7f000100) (sym 0x22e18) (sym 0x7f000200) (sym 0x15f04).

Definition SNPRINTF_DEPTH : Z := 5936.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_snprintf : CodeAtT img_segs (sym 0x7f000100) (PROGAT_CODE_snprintf IMG)}.
  Context {RB_snprintf : RelCode (sym 0x7f000100) 96}.
  Context {RN_vsnprintf : RelNear (sym 0x7f000100) (sym 0x7f000200)}.
  Context {RN_stack_chk_fail : RelNear (sym 0x7f000100) (sym 0x15f04)}.
  Context {RS_got_ssp : RelSym (sym 0x22e18)}.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Context {RS_35000 : RelSym (sym 0x35000)}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)}.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)}.
  Context {RQ_22e18 : ZFact (0x14000 <= sym 0x22e18)}.
  Let rp_22e18 : 0 <= sym 0x22e18 < 2^30 := @rel_sym_pf _ RS_got_ssp.
  Let rp_34288 : 0 <= sym 0x34288 < 2^30 := @rel_sym_pf _ RS_34288.
  Let rp_35000 : 0 <= sym 0x35000 < 2^30 := @rel_sym_pf _ RS_35000.
  Let rl0_0 : sym 0x22e18 + 8 <= sym 0x34288 := @zfact_pf _ RL0_0.
  Let rl0_1 : sym 0x34288 + 8 <= sym 0x35000 := @zfact_pf _ RL0_1.
  Let rq_22e18 : 0x14000 <= sym 0x22e18 := @zfact_pf _ RQ_22e18.
  Context (VSN : vsnprintf_x_stmt).

Definition snprintf_x_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (xs : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
    rw_cells img_segs m D [CB dn junkd] -> Z.of_nat dn = Z.min (zlength o) (n - 1) + 1 ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    bytes_at img_segs m q (u64s xs) -> q + 8 * zlength xs <= 2^64 ->
    args_ok lo lo 0 lo 0 D (Z.of_nat dn) m lo q lo ([a3; a4; a5; a6; a7] ++ xs) args ->
    printf_model (OUT_snf (zlength o)) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    1 <= n < 2^31 ->
    stk img_segs m lo q -> lo <= q - SNPRINTF_DEPTH -> GLOBALS_TOP <= lo -> q < 2^63 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    A + zlength fmt <= STATIC_SPLIT -> 65536 <= A ->
    0 < D -> D + Z.of_nat dn < 2^63 ->
    (D + Z.of_nat dn <= lo \/ q + 8 * zlength xs <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt img_segs (vsnprintf_x_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn
                    (zb (firstn (Z.to_nat (n - 1)) o) ++ [Z_to_bv 8 0]) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x7f000100)) fc None m (seg_rom img_segs)).

Theorem snprintf_x_proof : snprintf_x_stmt.
Proof.
  unfold snprintf_x_stmt. intros until o. cbv zeta.
  intros -> -> -> DST HDN BY HF P1 XS XHI AOK MODEL Hn ST LO GLO QHI SSP MI FRM HA HA0 D0 DHI DD1 DD2.
  unfold SNPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. unfold zb in AB. rewrite length_map in AB.
  pose proof (u64s_length xs) as LX. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof rp_22e18. pose proof rp_34288. pose proof rp_35000. pose proof rl0_0. pose proof rl0_1. pose proof rq_22e18.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU2.
  stash BY. stash XS. stash AOK. stash MODEL. stash DST.
  carve_frame 80%nat ST.
  do 15 zs. zs.
  apply (proj1 (rw_cells_app img_segs _ _ [_; _; _; _; _] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
  replace (bv_unsigned sp + -80 + Z.of_nat 40) with (bv_unsigned sp + -40) in VAC by lia.
  unfold hideP in BY, XS, AOK, MODEL, DST.
  assert (XS1 : bytes_at img_segs m0 (bv_unsigned sp) (u64s xs)).
  { eapply bytes_at_transport; [exact XS | exact MU2 |]. cbn [disjoint_from]. rewrite LX. lia. }
  assert (VAA : va_area m0 (bv_unsigned sp + -40) ([a3; a4; a5; a6; a7] ++ xs)).
  { destruct VAC as [[_ VB] _]. unfold va_area. rewrite u64s_app. apply (proj2 (bytes_at_app img_segs _ _ _ _)). split.
    - cbn [cells_bytes cbytes] in VB. exact VB.
    - rewrite u64s_length. cbn [length]. replace (bv_unsigned sp + -40 + Z.of_nat (8 * 5)) with (bv_unsigned sp) by lia.
      exact XS1. }
  assert (BY1 : bytes_at img_segs m0 A (zb fmt)).
  { eapply bytes_at_transport; [exact BY | exact MU2 |]. cbn [disjoint_from]. unfold zb. rewrite length_map. lia. }
  assert (DST1 : rw_cells img_segs m0 D [CB dn junkd]).
  { eapply rw_cells_transport; [exact DST | exact MU2 | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (AOK1 : args_ok lo lo 0 lo 0 D (Z.of_nat dn) m0 lo (bv_unsigned sp + -80) lo ([a3; a4; a5; a6; a7] ++ xs) args).
  { eapply args_ok_rebase; [exact AOK | | | | | |].
    - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros; lia.
    - lia.
    - right; reflexivity.
    - right; split; reflexivity.
    - right; split; reflexivity.
    - right; reflexivity. }
  clear MU2 BY XS XS1 AOK DST.
  pose proof VSN as V. unfold vsnprintf_x_stmt in V. cbv zeta in V.
  eapply evt_cut.
  { eapply V with (D := D) (n := n) (A := A) (VA := bv_unsigned sp + -40) (dn := dn) (junkd := junkd) (fmt := fmt)
                  (slots := [a3; a4; a5; a6; a7] ++ xs) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      clear V; rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength in *;
      first [ reflexivity | exact DST1 | exact BY1 | exact HF | exact P1 | exact VAA | exact AOK1 | exact MODEL | exact ST
            | (split; [exact SSP1 | exact SSP2]) | assumption | exact FRM | (rewrite ?length_app; cbn [length]; lia) | lia ]. }
  clear V.
  cbv beta. intros ms' P. unfold vsnprintf_x_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 26%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' m3 -> MUc WMc MI3 FRM' FOK ST3 SSP3 DST3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m3 MUc WMc; clear MUc WMc end.
  aret_pc.
  destruct SSP3 as [SSP4 SSP5]. unfold got_ssp, ssp_guard in SSP4, SSP5.
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  do 4 zs.
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80) ?c1, VAC : rw_cells _ ?mm (bv_unsigned sp + -40) ?c2 |- _ =>
    assert (FALL : rw_cells img_segs mm (bv_unsigned sp + -80) (c1 ++ c2)) by
      (apply (proj2 (rw_cells_app img_segs _ _ _ _)); split; [exact FR | eapply rwc_eq; [exact VAC | cbn; lia]]);
    clear FR VAC end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold vsnprintf_x_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|].
  split; [exact FOK|]. split; [exact ST3|]. split; [split; [exact SSP4 | exact SSP5]|]. exact DST3.
Qed.

End Img.
