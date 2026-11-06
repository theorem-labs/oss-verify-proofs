(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface I_asan_memset AU_rt AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_kit4 APC_docalloc APC_setcap APC_setdepth APC_active APC_create APC_dtor APC_memcmp APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_pid0 APC_pid_t1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_mpres.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac tlia ::= tlia_u.
Local Ltac lia3 ::= lia3_u.
Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.

Section Proof.
  Hypothesis ONTA : opnew_nt_stmtA AI.
  Hypothesis ODA : opdelete_arr_stmtA AI.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis PARSE : parse_stmtA AI rng_fs.
  Hypothesis RFSM : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.

  Theorem apid_proof : apid_stmt AI rng_fs.
  Proof using All.
    unfold apid_stmt. intros until trR.
    intros AH LBK PAY DAT DB D16 DL CI0 CSH CST PIM PDOC PMAX PCP PR FK RP R8 P8 SHP SHR RPR RSHR RPP RSHP RSPR RHI
      ST LOA LOS RCL RCL1 RCL2 RCL3 RRNG STOP SP16 MI FZ TP HUL UCR TRR RSTK RI RISH RFS AOK AFR DKW A0 A1 A2 A3 A4 A5.
    pose proof PR as PRO.
    pose proof (client_img_x _ CI0) as (RMC & FMIN & BOMS & CTS).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold APID_STACK, APARSE_STACK, STAGE2_STACK_A in LOS. atop_facts.
    destruct FK as (fcls & FA & FN & INF & FKH & FK2 & FKB). assert (FK1 : FA <= R) by lia.
    pose proof (ablk_lin _ _ FKB) as (FKB1 & FKB2 & FKB3 & FKB4). unfold AIMG_HI in FKB1. band_ind FKB bF.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & RIC & REAL & SHB & SUA & INI & LAY).
    set (len := zlength data) in *.
    assert (LEN0 : 0 <= len) by (unfold len, zlength; lia).
    assert (CAPR : 32 <= CAP len < 2^26 + 32) by (unfold CAP; lia).
    (* [comment removed for export] *)
    unfold shx, ASHOFF in SHP, SHR, RSHR, RSHP.
    assert (R47 : R + 24 <= 2 ^ 47) by (destruct RCL as [(_ & _ & _ & AB) _]; unfold app_blk, KLOW, KHIGH, KEND in AB; lia).
    pose proof (bv_unsigned_in_range 64 sp) as _.
    assert (PR0 : 0 <= R) by (pose proof (ablk_lin _ _ FKB); lia).
    Local Ltac shc1 H X k j := let C := fresh "SC" in
      pose proof (shadow_cell_of_run _ X k j ltac:(assumption) ltac:(lia) ltac:(lia) H) as C;
      match type of C with rw_cells _ _ (Z.shiftr (?Y + 8 * ?jj) 3 + _) _ =>
        let v := eval vm_compute in (8 * jj) in change (8 * jj) with v in C end.
    shc1 SHP P 10 1. shc1 SHP P 10 3. shc1 SHP P 10 4. shc1 SHP P 10 5. shc1 SHP P 10 6. shc1 SHP P 10 7. shc1 SHP P 10 8. shc1 SHP P 10 9.
    shc1 SHR R 3 0. shc1 SHR R 3 1. shc1 SHR R 3 2.
    replace (R + 0) with R in SC7 by lia.
    clear SHP SHR.
    pose proof (ablk_lin _ _ FKB) as (FKB5 & FKB6 & FKB7 & FKB8).
    Local Ltac shb X := let B := fresh "SB" in pose proof (blk_shx_bounds X ltac:(lia) ltac:(lia)) as B.
    shb (P + 8). shb (P + 24). shb (P + 32). shb (P + 40). shb (P + 48). shb (P + 56). shb (P + 64). shb (P + 72).
    shb R. shb (R + 8). shb (R + 16).
    (* [comment removed for export] *)
    Local Ltac rsh RG H X := let Hr := fresh "RS" in
      assert (Hr : rng RG (Z.shiftr X 3 + 2147450880) 1)
        by (eapply rng_sub'; [exact H| rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    rsh RNG RSHP (P + 8). rsh RNG RSHP (P + 24). rsh RNG RSHP (P + 32). rsh RNG RSHP (P + 40). rsh RNG RSHP (P + 48).
    rsh RNG RSHP (P + 56). rsh RNG RSHP (P + 64). rsh RNG RSHP (P + 72).
    rsh RNG RSHR R. rsh RNG RSHR (R + 8). rsh RNG RSHR (R + 16).
    (* [comment removed for export] *)
    boxm PAY. boxm LBK. boxm CST. boxm HUL. boxm UCR. boxm PRO.
    unfold HarnessP.parse_into_doc. fold len.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 80); (R, R + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl bsegs m) as WM0.
    park_memA m.
    boxm SB. boxm SB0. boxm SB1. boxm SB2. boxm SB3. boxm SB4. boxm SB5. boxm SB6. boxm SB7. boxm SB8. boxm SB9.
    (* [comment removed for export] *)
    boxm RS. boxm RS0. boxm RS1. boxm RS2. boxm RS3. boxm RS4. boxm RS5. boxm RS6. boxm RS7. boxm RS8. boxm RS9.
    boxm RPR. boxm RPP. boxm RSHR. boxm RSHP. boxm RRNG. boxm RI. boxm RISH.
    carve_frame 112%nat ST.
    subst a0 a1 a2 a3 a4 a5. unfold APID in *.
    do 14 zstep.
    unparkA.
    unfold boxed in SB, SB0, SB1, SB2, SB3, SB4, SB5, SB6, SB7, SB8, SB9.
    trmB MU0 WM0. clear MU0 WM0.
    (* [comment removed for export] *)
    parkA RIC. parkA REAL. parkA SUA. parkA INI. parkA LAY. parkA FMIN. parkA PCP. parkA PR. parkA DAT.
    parkA SC0. parkA SC1. parkA SC4. parkA SC5. parkA SC6. parkA SC7. parkA SC8. parkA SC9.
    unbox RI. unbox RPR. unbox RPP. unbox RS. unbox RS2. unbox RS3.
    steps_to 0x95b84.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (evtF_cut bsegs RNG (fun x => x = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1
          (Z_to_bv 64 32) (Z_to_bv 64 P) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 D) (Z_to_bv 64 len) (Z_to_bv 64 1) a6 a7 (Z_to_bv 64 len)
          (Z_to_bv 64 D) s4 (Z_to_bv 64 P) (Z_to_bv 64 1) s7 (Z_to_bv 64 (CAP len)) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) s11
          t3 t4 t5 t6) F (Z_to_bv 64 0x95b8c) fc None mm (seg_rom bsegs)))
    end.
    { zstep. if_cases K0; zify_cond K0.
      - apply evtF_done. unfold CAP. rewrite Z.max_l by lia. reflexivity.
      - zstep. apply evtF_done. unfold CAP. rewrite Z.max_r by lia. reflexivity. }
    intros ms0 ->.
    steps_to 0x95c80.
    zstep. if_cases K1; zify_cond K1; [| exfalso; lia].
    steps_to 0x95ca4.
    zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    steps_to 0x96154.
    apply evtF_done.
    (* [comment removed for export] *)
    unparkA. unbox RS0. unbox RS1. unbox RS2. unbox HUL.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
        by (eapply (AI_frame AI); [exact AH| exact MU| exact WM|];
            apply Forall_cons; [left; left; cbn; lia|];
            apply Forall_cons; [right; left; exists (mkABlock (ABFake fcls) FA FN); split; [exact INF| cbn; lia]|];
            apply Forall_cons; [left; left; cbn; lia| apply Forall_nil])
    end.
    eapply implMA_bind.
    { eapply implMA_leaves; [| exact (doc_allocate_dk len s)].
      pose proof (adocalloc_proof AI ONTA) as DA. unfold adocalloc_stmt in DA.
      eapply DA with (lo := lo) (DOC := P + 24) (c0 := Z_to_bv 64 0) (len := len); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact AH1 | exact TP | (unfold ADOCALLOC_STACK, OPNEW_NT_STACK_A, OPNEW_STACK_A, AMALLOC_STACK; lia)
              | (exists fcls, FA, FN; split; [exact INF| split; [lia| split; [lia| exact FKB]]])
              | (unfold shc, shx, ASHOFF; replace (P + 24 + 8) with (P + 32) by lia; eassumption)
              | (unfold shc, shx, ASHOFF; replace (P + 24 + 16) with (P + 40) by lia; eassumption)
              | (unfold shc, shx, ASHOFF; eassumption)
              | (unfold shx, ASHOFF; replace (P + 24 + 8) with (P + 32) by lia; eassumption)
              | (unfold shx, ASHOFF; replace (P + 24 + 16) with (P + 40) by lia; eassumption)
              | (unfold shx, ASHOFF; eassumption)
              | eassumption
              | (eapply rng_sub'; [exact RPR| lia]) | (eapply rng_sub'; [exact RPP| lia]) | (eapply (HU_in _ _ HUL); unfold HU_TRACES; repeat (first [left; reflexivity | right])) | lia]. }
    cbv beta. intros [psb ptp] s1' RNG1 ms1 [(FPL1 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2 & -> & MI2 & ST2 & HPX1 & ARS1
                                            & (SBA & TPA & jsb & jtp & BRS & BRT & AH2 & BLKS & BLKT & DOC2)) DKS1].
    destruct DKS1 as (DF1 & _ & _). destruct (DF1 AFR) as [AFR1 DKB1]. assert (DK1 : dk (aps_m s1') < DWMAX) by (clear - DKW DKB1; lia). clear DF1 DKB1.
    cbn [fst snd] in AH2. rewrite ?unsigned_lit in ST2, HPX1 by lia. retlit.
    clear GOT RIC REAL SHB SUA INI LAY.
    trxA HPX1 INF IMG_CI.
    (* [comment removed for export] *)
    assert (FW0 : Forall wfar [(lo, bv_unsigned sp); (P, P + 80); (R, R + 24)]).
    { apply Forall_cons; [apply wfar_high; lia|]. apply Forall_cons; [eapply wfar_ablk; [exact FKB| lia| lia]|].
      apply Forall_cons; [apply wfar_high; lia| apply Forall_nil]. }
    pose proof (client_static_munch32 _ _ _ _ _ ltac:(unbox CST; exact CST) MU WM FW0) as CST0.
    pose proof (client_static_pres_x AI IMG_CI _ _ _ _ _ _ _ _ HPX1 ltac:(eapply wfar_ablk; [exact FKB| lia| lia]) CST0) as CST2.
    clear CST CST0 FW0.
    assert (PW2 : aheap_pres_W CI LB (bv_unsigned sp) (apid_W P R) m m2).
    { eapply aheap_pres_W_trans.
      - eapply aheap_pres_W_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx. unfold apid_W in Hx. cbn [app outside] in Hx |- *.
        pose proof (aclient_lo_or_sp AI _ _ _ _ _ _ _ a AH (fun b Hb => Hb) Hc) as Ha'. lia.
      - eapply pres_W_of_x; [exact HPX1| lia| intros b Hb; exact Hb|]. intros a Hc Ho Hx. unfold apid_W in Ho. cbn [app outside] in Ho. lia. }
    clear AH AH1 MU WM HPX1 RMC BOMS CTS FMIN MI ST PDOC.
    exact (apid_t1 AI rng_fs ONTA ODA IMG_CI PARSE RFSM L RNG ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo rstk data D P R jr trR LBK PAY DAT DB
       D16 DL CI0 CSH fcls FA FN INF FKH FK2 FKB RP R8 P8 RPR RSHR RPP RSHP RSPR RHI LOA LOS RCL RCL1 RCL2 RCL3 RRNG STOP SP16 m0 FZ TP HUL UCR TRR RSTK
       RI RISH RFS AOK AFR DKW PRO RSP H FK1 FKB1 FKB2 FKB3 FKB4 bF bFr bFhi bFlo LY1 LY2 LY3 LEN0 CAPR R47 PR0 FKB5 FKB6 FKB7 FKB8 SB SB0 SB1 SB2 SB3 SB4
       SB5 SB6 SB7 SB8 SB9 RS RS0 RS1 RS2 RS3 RS4 RS5 RS6 RS7 RS8 RS9 junk K1 K2 psb ptp s1' RNG1 FPL1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m2
       MI2 ST2 ARS1 SBA TPA jsb jtp BRS BRT AH2 BLKS BLKT DOC2 AFR1 DK1 PIM PMAX PCP PR SC SC0 SC1 SC2 SC3 SC4 SC5 SC6 SC7 SC8 SC9 FR CST2 PW2).
  Qed.
End Proof.
End S.
End CANSEC1.
