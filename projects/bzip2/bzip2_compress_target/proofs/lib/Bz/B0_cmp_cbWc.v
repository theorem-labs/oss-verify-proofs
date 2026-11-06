(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 DecTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCSortM BzArrD CmpMem CmpCut BzCNumZ CmpLaws CmpCutCB CmpArith CmpSdTac BzSepTac BzCLemmas1 BzLemmasMtf BzLemmasT CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV CmpSmKit CmpHmKit B0_cmp_bsw B0_cmp_bsx B0_cmp_cbV.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section B0CBW.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y.
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation nblock := (e_nblock e).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.

  (* [comment removed for export] *)
  Definition cbW_W : list (Z * Z) := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P - 48, P)]%Z.
  (* [comment removed for export] *)
  Definition cbF_W : list (Z * Z) := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE)]%Z.

  (* [comment removed for export] *)
  Definition EH1b (m : word -> option byte) (b : bw) : Prop := rw_cells b0segs m E (EHEAD1 cx g (est_set_bw e b)).
  Definition EH2b (m : word -> option byte) (b : bw) : Prop := rw_cells b0segs m (E + 640) (EHEAD2 cx g (est_set_bw e b)).
  Definition AR2b (m : word -> option byte) (b : bw) : Prop := u8arr b0segs m A2 (zb8 (zbl (e_arr2 e) nblock b) ARR2_SIZE).

  (* [comment removed for export] *)
  Notation RW ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma B0_bsw8_call : forall (b : bw) (v : Z) (m : word -> option byte)
      (ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= v < 256)%Z -> bw_ok b -> (nblock + bw_numZ b + 4 <= ARR2_SIZE)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv b0segs m -> stk b0segs m lo P ->
    aconsts B0C m -> cctx_sh b0segs cx cbW_W m ->
    (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        let b' := bsW b 8 v in
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv b0segs m' -> stk b0segs m' lo P -> munch cbW_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (RW ra t0' t1' t2' s0 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra t0 t1 t2 s0 (Z_to_bv 64 E) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x8b19c) fc None m (seg_rom b0segs)).
  Proof.
    intros b v m ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hv OK ROOM EH1 EH2 AR2 MI ST AC CSH K.
    unfold EH1b, EH2b, AR2b in *.
    cbenv_open XOK. acenv_open YOK. cb_ranges CX.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    assert (HP : (0 <= P < 18446744073709551616)%Z) by lia.
    pose proof (B0_cmp_bsw.B0_bsW8 ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 E) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g (est_set_bw e b) v lo) as BSW.
    cbv zeta in BSW. cbn [aci_segs aci_c ci_segs B0C ci_bsW8] in BSW. unfold bsW8_post in BSW.
    rewrite (unsigned_lit P) in BSW by lia.
    eapply evt_cut.
    { eapply BSW; [reflexivity| reflexivity| exact Hv| exact EH1| exact EH2| cbn_est; exact AR2| exact MI| exact ST| lia| unfold CEIL; lia| exact CX| exact SEP| exact Gbs
        | cbn_est; exact Gzb| cbn_est; exact OK| cbn_est; exact Hnb| cbn_est; exact ROOM| exact AC|].
      eapply (cctx_sh_sub b0segs cx cbW_W _ m m CSH (munch_refl _ _)).
      unfold bsW8_W, cbW_W. cbn_est. cbn [app]. cps_pose OK as (? & ? & ?). bz_params. a_sub_fp. }
    clear EH1 EH2 AR2 MI ST BSW. cbn_est.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI2 [ST2 [EH1 [EH2 AR2]]]]]]]; subst ms'.
    lazymatch type of MUc with munch _ m ?m' =>
      assert (MU' : munch cbW_W m m');
      [ eapply munch_weaken; [| exact MUc];
        unfold bsW8_W, cbW_W; cbn_est; cbn [app]; cps_pose OK as (? & ? & ?); bz_params; a_sub_fp
      | ] end.
    eapply K; [exact EH1| exact EH2| exact AR2| exact MI2| exact ST2| exact MU'| exact WMc].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bsput32_call : forall (b : bw) (u : Z) (m : word -> option byte)
      (ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= u < 4294967296)%Z -> bw_ok b -> (nblock + bw_numZ b + 16 <= ARR2_SIZE)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv b0segs m -> stk b0segs m lo P ->
    aconsts B0C m -> cctx_sh b0segs cx cbW_W m ->
    (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        let b' := bsPutUInt32 b u in
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv b0segs m' -> stk b0segs m' lo P -> munch cbW_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (RW ra t0' t1' t2' s0 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra t0 t1 t2 s0 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x8b418) fc None m (seg_rom b0segs)).
  Proof.
    intros b u m ra t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hu OK ROOM EH1 EH2 AR2 MI ST AC CSH K.
    unfold EH1b, EH2b, AR2b in *.
    cbenv_open XOK. acenv_open YOK. cb_ranges CX.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    assert (HP : (0 <= P < 18446744073709551616)%Z) by lia.
    pose proof (B0_cmp_bsx.B0_bsPutUInt32S ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g (est_set_bw e b) u lo) as BSP.
    cbv zeta in BSP. cbn [aci_segs aci_c ci_segs B0C ci_bsPutUInt32] in BSP. unfold bsPutUInt32_post in BSP.
    rewrite (unsigned_lit P) in BSP by lia.
    eapply evt_cut.
    { eapply BSP; [reflexivity| reflexivity| exact Hu| exact EH1| exact EH2| cbn_est; exact AR2| exact MI| exact ST| lia| unfold CEIL; lia| exact CX| exact SEP| exact Gbs
        | cbn_est; exact Gzb| cbn_est; exact OK| cbn_est; exact Hnb| cbn_est; exact ROOM| exact AC|].
      eapply (cctx_sh_sub b0segs cx cbW_W _ m m CSH (munch_refl _ _)).
      unfold bsPutUInt32_W, cbW_W. cbn_est. cbn [app]. cps_pose OK as (? & ? & ?). bz_params. a_sub_fp. }
    clear EH1 EH2 AR2 MI ST BSP. cbn_est.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI2 [ST2 [EH1 [EH2 AR2]]]]]]]; subst ms'.
    lazymatch type of MUc with munch _ m ?m' =>
      assert (MU' : munch cbW_W m m');
      [ eapply munch_weaken; [| exact MUc];
        unfold bsPutUInt32_W, cbW_W; cbn_est; cbn [app]; cps_pose OK as (? & ? & ?); bz_params; a_sub_fp
      | ] end.
    eapply K; [exact EH1| exact EH2| exact AR2| exact MI2| exact ST2| exact MU'| exact WMc].
  Qed.
End B0CBW.
End ACeilS1.
