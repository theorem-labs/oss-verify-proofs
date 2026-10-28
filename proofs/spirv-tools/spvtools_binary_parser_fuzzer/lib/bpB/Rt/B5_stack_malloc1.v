(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel BSysStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk BakeStackRep B5_tls B5_smkit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import B8Store.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LOOP1.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t1 t2 s0 s1 a1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (FB : Z) (FV : Z -> Z).
  Hypothesis FL : forall pos, 0 <= pos < 8192 -> rw_cells asegs m (FB + pos) [C1 (b8 (FV pos))].
  Hypothesis FV01 : forall pos, FV pos = 0 \/ FV pos = 1.

  Definition loop1_post : machine_state -> Prop :=
    fun ms' => exists (cur' t0 : word) (c' p : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c') a1 cur' (Z_to_bv 64 FB) (Z_to_bv 64 8191) (Z_to_bv 64 (FB + p)) a6 (Z_to_bv 64 p)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x9dd64) fc None m (seg_rom asegs)
      /\ 0 <= p < 8192 /\ p = bv_unsigned cur' mod 8192 /\ FV p = 0 /\ 1 <= c' <= 8192.

  Lemma sm1_loop : forall (n : nat) (cur a5 a7 t0 : word) (c : Z),
    c = Z.of_nat n -> 1 <= c <= 8192 ->
    (exists j, 0 <= j < c /\ FV ((bv_unsigned cur + j) mod 8192) = 0) ->
    evt asegs loop1_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 cur (Z_to_bv 64 FB) (Z_to_bv 64 8191) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9dcec) fc None m (seg_rom asegs)).
  Proof.
    induction n as [|n IH]; intros cur a5 a7 t0 c Hc HC EXJ; [lia|].
    pose proof (bv_unsigned_in_range 64 cur) as CR. unfold bv_modulus in CR. change (2 ^ Z.of_N 64) with (2^64) in CR.
    set (p := bv_unsigned cur mod 8192).
    assert (HP : 0 <= p < 8192) by (subst p; Z.div_mod_to_equations; lia).
    remember (FB + p) as FP eqn:HFP.
    pose proof (FL p HP) as CELL. rewrite <- HFP in CELL.

    zstep. rewrite land_8191. fold p. zstep. rewrite <- HFP.

    destruct (FV01 p) as [Z0|Z1].
    - rewrite Z0 in CELL. st1.
      zstep. if_cases K; [| exfalso; revert K; vm_compute; discriminate].
      apply evt_done. unfold loop1_post. subst FP. eexists _, _, c, p. split; [reflexivity|]. repeat split; lia.
    - rewrite Z1 in CELL. st1.
      zstep. if_cases K; [exfalso; revert K; vm_compute; discriminate|].

      destruct EXJ as (j & J0 & JF).
      assert (JNZ : j <> 0). { intros ->. rewrite Z.add_0_r in JF. fold p in JF. lia. }

      zstep. rewrite swrap32_small by lia. zstep.
      zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
      apply (IH (Z_to_bv 64 (bv_unsigned cur + 1)) _ _ _ (c - 1)); [lia| lia|].
      exists (j - 1). split; [lia|]. rewrite <- Zplus_mod_idemp_l, wrap_mod_8192, Zplus_mod_idemp_l.
      replace (bv_unsigned cur + 1 + (j - 1)) with (bv_unsigned cur + j) by lia. exact JF.
  Qed.
End LOOP1.

Section FOUND1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m m2 : mem) (LF : list fframe) (lo p c' : Z) (rax t0 t1 t2 cur a6 t3 t4 t5 t6 : word).
  Hypothesis FR : rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis ST0 : stk asegs m2 lo (bv_unsigned sp + -32).
  Hypothesis LO : aceil <= lo.
  Hypothesis LOSP : lo <= bv_unsigned sp - 1024.
  Hypothesis MI : mem_inv asegs m2.
  Hypothesis AC : ACONST m2.
  Hypothesis R : RFSI (as_FSB H) LF m2.
  Hypothesis HP : 0 <= p < 8192.
  Hypothesis FREE : flagv LF (flag_addr (as_FSB H) 1 p) = 0.
  Hypothesis MU0 : munch [(bv_unsigned sp - 1024, bv_unsigned sp)] m m2.
  Hypothesis WM0 : wmono asegs m m2.

  Lemma sm1_found :
    evt asegs (stack_malloc_post H 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 (as_FSB H))
               (Z_to_bv 64 c') (Z_to_bv 64 (as_FSB H + 4096)) cur (Z_to_bv 64 (as_FSB H + 20480)) (Z_to_bv 64 8191) (Z_to_bv 64 (as_FSB H + 20480 + p)) a6 (Z_to_bv 64 p)
               (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9dd64) fc None m2 (seg_rom asegs)).
  Proof.
    remember (as_FSB H) as fsb eqn:Hfsb.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    acb; unfold AFS_STACK in *.
    pose proof R as ((G1 & G2 & G3 & G4) & TLS & (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR) & SL & ND & FL & STF & STS).
    acb; unfold AIMG_TOP, AFS_SIZE, AFS_HDR in G1, G2, STF, STS. unfold hdr in HDR.
    assert (SOK : slot_ok 1 p) by (split; [unfold KMAX; lia| unfold NF; cbn; lia]).

    remember (fsb + 20480 + p) as FP eqn:HFP.
    assert (EFP : flag_addr fsb 1 p = FP) by (unfold flag_addr, AFS_HDR; cbn; lia).
    pose proof (FL 1 p SOK) as CFP. rewrite FREE in CFP. rewrite EFP in CFP.

    remember (fsb + 1085440 + 128 * p) as FF eqn:HFF.
    assert (EFF : frame_addr fsb 1 p = FF) by (unfold frame_addr, AFS_HDR, fsz; cbn; lia).
    destruct (stk_split asegs m2 _ (FF + 128) _ STF ltac:(lia)) as [STa STc].
    destruct (stk_carve asegs m2 _ _ 128 STa ltac:(lia)) as [STa' [fjunk FRM]].
    replace (FF + 128 - Z.of_nat 128) with FF in STa', FRM by lia. clear STa.

    remember (sh FF) as SF eqn:HSF.
    assert (SFR : 2148356096 <= SF /\ SF + 16 <= 17594333495296 /\ sh fsb <= SF /\ SF + 16 <= sh (fsb + 11571200)).
    { subst SF. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    assert (SEP : fsb + 11571200 <= 2147446784 \/ 17594333495296 <= fsb)
      by (clear - G4; destruct G4 as [[X1 X2]|[X1 X2]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AFS_SIZE in X1, X2; lia).
    destruct (stk_split asegs m2 _ (SF + 16) _ STS ltac:(lia)) as [SSa SSc].
    destruct (stk_carve asegs m2 _ _ 16 SSa ltac:(lia)) as [SSa' [sjunk SRM]].
    replace (SF + 16 - Z.of_nat 16) with SF in SSa', SRM by lia. clear SSa SSc STc.

    pose proof (ACONST_mts m2 AC) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_MIDBEG, AMIDBEG_CELL, AGOT_MIDEND, AMIDEND_CELL, AGOT_HIEND, AHIEND_CELL, wz in Q1, Q2, Q3, Q4, Q5, Q6.
    unfold ATP, wz in TLS.

    pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (fsb, fsb + 4096); (FP, FP + 1); (FF, FF + 128); (SF, SF + 16)] m2) as MU2.
    assert (MU : munch [(bv_unsigned sp - 1024, bv_unsigned sp); (fsb, fsb + 4096); (FP, FP + 1); (FF, FF + 128); (SF, SF + 16)] m m2).
    { eapply munch_weaken; [| exact MU0]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    pose proof WM0 as WM. pose proof (wmono_refl asegs m2) as WM2. clear MU0 WM0 STF STS FL.

    zstep. zstep. zstep. zstep.
    st1. st1.

    zstep. zstep. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 7) with 128. zstep.
    match goal with |- context [Z_to_bv 64 (fsb + 36864 + ?e)] => replace (fsb + 36864 + e) with FF by lia end.

    st1. st1. zstep. zstep.
    call_pure mts_spec; try reflexivity; try eassumption;
      [clear - G4 HFF HP; destruct G4 as [[G4a G4b]|[G4a G4b]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, AFS_SIZE in *; [left | right]; acb; lia|].
    rewrite <- HSF.

    zstep. zstep. zstep. st1. st1.

    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST0 (bv_unsigned sp).
    assert (FF8 : 0 <= FF /\ FF mod 8 = 0) by (subst FF; Z.div_mod_to_equations; lia).
    subst fsb SF. unfold stack_malloc_post. finish_nm.
    all: lazymatch goal with
         | |- munch _ _ _ => exact MU
         | |- rw_cells _ _ _ [CB _ _; _; _; _] => exact FRM
         | |- rw_cells _ _ _ [C1 _] => exact CFP
         | |- SHAD _ _ _ => apply shad16_of_words; [lia| lia| exact SRM]
         | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU2| exact WM2|];
                          repeat apply Forall_cons; [| | | | |apply Forall_nil]; aconst5 G1 G4
         | |- as_RFS _ _ _ => apply RFS_is; eapply (RFSI_alloc _ LF m2 m1 1 p);
              [exact R| exact SOK| exact FREE| symmetry; exact EFF| symmetry; exact EFP| exact MU2| exact WM2| acb; lia| exact TLS| | exact CFP];
              do 11 eexists; exact HDR
         end.
  Qed.
End FOUND1.

Section SM1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.

  Lemma stack_malloc_1_ok : stack_malloc_1_stmt H.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LF lo.
    intros RFS LEN ST0 LO LOSP MI Htp AC ATH. subst tp.
    pose proof (proj1 (RFS_is LF m) RFS) as R. clear RFS.
    remember (as_FSB H) as fsb eqn:Hfsb.
    pose proof (RFSI_geom _ _ _ R) as (G1 & G2 & G3 & G4).
    acb; unfold AFS_STACK, AFS_MALLOC_1, AFS_SIZE in *. unfold AIMG_TOP in G1.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    destruct ATH as (ctx & T & D & tb & te & A1 & A2 & A3 & A4 & A5 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    acb; unfold ATSD0, ATP, wz in A1, A2, A3, A4, A5, B3, B6, B9. change (7100504 + 8) with 7100512 in A4.
    pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ST0 as ST. carve_frame 32%nat ST.

    zstep. st1. st1. st1. st1. zstep. zstep. zstep. zstep.
    call2 tls_icpt_spec.
    all: lazymatch goal with
         | |- mem_inv _ _ => eassumption
         | |- Z_to_bv _ _ = Z_to_bv _ _ => reflexivity
         | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU| exact WM|]; apply Forall_cons; [|apply Forall_nil]; aconst5 G1 G4
         | |- athr_cells _ => exists ctx, T, D, tb, te;
              split; [exact A1|]; split; [exact A2|]; split; [exact A3|]; split; [exact A4|]; split; [exact A5|]; acb; repeat split; lia
         | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
         | |- _ <= _ => rewrite ?unsigned_lit by lia; acb; lia
         | |- evt _ _ _ => idtac
         end.
    rewrite ?unsigned_lit in * by lia.
    match goal with Hst : stk asegs ?mx lo (bv_unsigned sp + -32), Hac : ACONST ?mx |- _ => rename Hst into ST; rename Hac into AC2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (R2 : RFSI fsb LF mx) by (eapply RFSI_stack_frame; [exact R| exact MU| exact WM| acb; lia]) end.
    pose proof (RFSI_tls _ _ _ R2) as TLS. pose proof (RFSI_hdr _ _ _ R2) as (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR).
    unfold ATP, wz in TLS |- *. unfold hdr, wz, b8 in HDR.

    zstep. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
    st1. zstep. unfold wz. zstep. if_true.

    zstep. zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3; [exfalso; revert K3; vm_compute; lia|].

    do 15 zstep.

    pose proof R2 as (_ & _ & _ & _ & _ & FL & _).
    eapply evt_cut.
    { eapply sm1_loop with (FV := fun pos => flagv LF (flag_addr fsb 1 pos)) (n := 8192%nat).
      - intros pos Hpos. cbn beta. replace (fsb + 20480 + pos) with (flag_addr fsb 1 pos) by (unfold flag_addr, AFS_HDR; cbn; lia).
        apply FL. split; [unfold KMAX; lia| unfold NF; cbn; lia].
      - intros pos. apply flagv_01.
      - reflexivity.
      - lia.
      - destruct (RFSI_free_slot fsb LF _ 1 (bv_unsigned h1) R2 ltac:(lia) LEN) as (j & J1 & J2). exists j.
        change (NF 1) with 8192 in J1, J2. exact (conj J1 J2). }
    intros ms' PO. destruct PO as (cur' & t0' & c' & p & -> & HP & HPM & FV0 & HC').
    subst fsb. eapply (sm1_found H RFS_is); eassumption.
  Qed.
End SM1.

