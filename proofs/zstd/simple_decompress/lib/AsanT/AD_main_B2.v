(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 ATP).



Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells bsegs m A [CB 0%nat []].
Proof.
  intros m A H. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact H.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
  rw_cells bsegs m A [CB n1 b1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells bsegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  assert (H : rw_cells bsegs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2. }
  destruct H as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  split; [split|].
  - cbn. rewrite length_app. split; [lia| exact I].
  - cbn [cells_bytes cbytes app] in HB |- *. rewrite !app_nil_r in HB |- *. exact HB.
  - replace (Z.of_nat (cells_size [CB (n1 + n2)%nat (b1 ++ b2)])) with (Z.of_nat (cells_size ([CB n1 b1] ++ [CB n2 b2]))) by (cbn; lia). exact HW.
Qed.

(* [comment removed for export] *)
Lemma implMA_msys : forall {A} RNG n (dec : resp -> option A) (s : APS) (Q' : A -> footprint -> machine_state -> Prop) ms,
  implA bsegs RNG (enode n dec) (epostF Q') ms ->
  implMA RNG (msys n dec) s (fun a s' RNG' ms' => s' = s /\ Q' a RNG' ms') ms.
Proof.
  intros A RNG n dec s Q' ms H. apply implA_implS in H. unfold implMA, msys, enode in *. cbn [implF] in H |- *.
  eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp RNG' HF. specialize (Hk rsp RNG' HF). destruct (dec rsp) as [a|]; cbn [implF epostF] in Hk |- *.
  - eapply evtF_mono; [exact Hk|]. cbv beta. intros ms' HQ. split; [reflexivity| exact HQ].
  - exact Hk.
Qed.

(* [comment removed for export] *)
Section B2.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variables (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word) (L : alayout).
  Hypothesis RSTK_lo : r_lo RSTK <= ALO usp.
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis SPG : usp = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= ALO usp.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (argv : list (list byte)) (P0 P1 : Z) (slack0 slack1 : list byte) (RA0 RA1 : region).
  Hypothesis VARGV : valid_argv argv.
  Notation argc := (Z.of_nat (length argv)).
  Notation arg0 := (map bv_unsigned (nth 0 argv [])).
  Notation arg1 := (map bv_unsigned (nth 1 argv [])).
  (* [comment removed for export] *)
  Variable J8 : list byte.
  Notation ABASE' := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK canary).
  Notation AMFRAME' := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 J8).
  Notation LO := (ALO usp).
  Notation RNGS' := (RNGS rng_fs usp RSTK L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation AARGV' := (AARGV usp argv P0 P1 slack0 slack1 RA0 RA1).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.
  Let geoA' := geoA usp USP16 USPLO USPHI.
  (* [comment removed for export] *)
  Hypothesis UM_e48 : In [AMALLOC_PC; 0x825dc] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0x82630] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0x82654] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0x82784] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0x828bc] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0x82950] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)

  Notation ioS := (ioA AAllocAsan).
  Notation BUF' := (BUF AI L).
  Notation RDINV' := (RDINV AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation RDBRK' := (RDBRK AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation POSTBODY' := (POSTBODY AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).
  Hypothesis ARGC2 : argc = 2.

  (* [comment removed for export] *)
  Lemma rd_read_core : forall (fd : Z) (st1 : rd_st) (s : APS) RNG x1 t0 t1 t2 a1 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : amem) (A CNT : Z) (DATA junk sj : list byte),
    3 <= fd < 2^32 ->
    rd_content st1 = map bv_unsigned DATA -> BUF' mm s RNG (rd_buf st1) A (rd_cap st1) DATA junk -> STAGE mm sj -> Z.of_nat (length DATA) < rd_cap st1 ->
    CNT = (if 65536 <? rd_cap st1 - Z.of_nat (length DATA) then 65536 else rd_cap st1 - Z.of_nat (length DATA)) ->
    ABASE' stdout_init mm -> AARGV' mm -> RNGS' RNG -> frm0 fc ->
    implMA RNG (rd_read_part fd arg1 st1) s (POSTBODY' fd)
      (GST 0x82664 x1 t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 65536) a1 (Z_to_bv 64 CNT) a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 (Z.of_nat (length DATA))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until sj. intros FD HC BU SJ LT ECNT0 BA ARG RG FRM.
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *. atop_facts.
    destruct BU as (P0h & SO0 & RK & HA & BLK & [CAPR CAPK] & LENR & BR & RGA & RGAS). pose proof BR as (BR1 & BR2 & BR3 & BR4).
    pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & RGa0 & RRa0 & RG1).
    assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    unfold MAX_INPUT in CAPR.
    assert (CNTR : 1 <= CNT <= 65536 /\ CNT <= rd_cap st1 - Z.of_nat (length DATA)).
    { rewrite ECNT0. destruct (Z.ltb_spec0 65536 (rd_cap st1 - Z.of_nat (length DATA))); lia. }
    (* [comment removed for export] *)
    pose proof ASTAGE_LEN_Z as STGZ.
    (* [comment removed for export] *)
    pose proof (ASHENV _ _ _ _ _ P0h) as ENV. pose proof ENV as (Hgot & Hric & Hshb & Hini & Hlay & Hrmem & Hrpf & Hrwcs & Hrread & _).
    pose proof RSG as [(SUNP & SHUL & SWR & SAPP) _]. unfold RSTG in SUNP, SHUL, SWR, SAPP. cbn [r_lo r_hi r_rlo r_rhi] in SUNP, SHUL, SWR, SAPP.
    unfold rd_read_part. cbv zeta. rewrite LENZ, <- ECNT0.
    unfold AMFRAME in FR. rewrite errno_addr_ATP in ERR. unfold STAGE, ASTAGE in SJ.
    apply implMA_from_evtF.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [Z.to_nat CNT; (ASTAGE_LEN - Z.to_nat CNT)%nat]) in SJ; [| cbn; lia].
    cbn [mk_CB_cells app] in SJ.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in SJ. destruct SJ as [SJ1 SJ2]. cbn [cells_size csize Nat.add] in SJ2.
    apply evtF_done.
    set (LEN := Z.of_nat (length DATA)) in *.
    assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. clearbody LEN. assert (LEN0 : 0 <= LEN) by lia.
    eapply implMA_bind.
    { set (w1 := Z_to_bv 64 ASTAGE). unfold ASTAGE in w1.
      replace ASTAGE with (bv_unsigned w1) by (subst w1; unfold ASTAGE; rewrite unsigned_lit; lia).
      eapply implMA_msys.
      eapply (read_i_spec RNG) with (lo := LO) (junk := firstn (Z.to_nat CNT) sj) (errv := errv) (RLO2 := 0x5f2340) (RHI2 := 0x602380); subst w1;
        rewrite ?(unsigned_lit (usp + -128)) by lia; rewrite ?(unsigned_lit 6234960) by lia; rewrite ?errno_addr_ATP; unfold ATP; rewrite ?unsigned_lit by lia;
        try reflexivity;
        first [ exact MI | exact ST | exact Hgot | exact Hshb | exact Hini | exact Hlay | exact Hrread | exact SJ1 | exact ERR | exact SWR | exact RGimg
              | idtac ].
      all: first [ lia
                 | unfold KHIGH; lia
                 | unfold app_blk, KLOW, KHIGH, KEND; lia
                 | eapply unpoisoned_sub; [exact SUNP| lia| lia]
                 | unfold KEND; repeat match goal with |- _ /\ _ => split end; lia
                 | replace (shad 0x5f2340) with 0x800b6468 by reflexivity; replace (shad 0x602380) with 0x800b8470 by reflexivity;
                   first [ exact SWR | eapply rng_sub'; [exact RGimsh| lia] ]
                 | eapply rng_sub'; [exact RGstk| lia]
                 | eapply rng_sub'; [exact RGimg| lia] ]. }
    cbv beta. intros a s' RNG' ms' [-> [-> PO]].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
    unfold ATP in MUc, RES. rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in RES by lia.
    change (6302896 + -164) with 6302732 in MUc, RES.
    transport_after_call bsegs mm m2 MUc WMc.
    fix_ret.
    rename ST2 into ST2'.
    assert (WOKW : Forall (WOK usp) [(usp + -128 - 2208, usp + -128); (6234960, 6234960 + Z.of_nat (Z.to_nat CNT)); (6302732, 6302732 + 4)]).
    { unfold WOK, WOKb, ALO, ASTAGE, ablk, AIMG_HI, KLS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    assert (P2 : AHEAP AI L RNG (aps_m s) [HB (rd_buf st1) A (rd_cap st1)] m2).
    { eapply (AI_frame AI); [exact P0h| exact MUc| exact WMc|].
      pose proof (AI_layout AI _ _ _ _ _ P0h) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
      constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
      - left. left. lia.
      - left. right; left. exists (0x5f2340, 0x602380). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia].
      - left. right; left. exists (0x602c08, 0x602c10). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
    assert (ERR2 : exists errv', rw_cells bsegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv']).
    { rewrite errno_addr_ATP. destruct a as [e|bs]; destruct RES as (_ & X & _); eexists; exact X. }
    assert (BA2 : ABASE' stdout_init m2).
    { eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| exact ST2'| | exact ERR2].
      destruct SE as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
      eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact Hc|]. intros a' Ha'. cbn in Ha' |- *. lia. }
    assert (ARG2 : AARGV' m2) by (eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKW| exact MUc| exact WMc| exact ARG]).
    (* [comment removed for export] *)
    remember (firstn (ASTAGE_LEN - Z.to_nat CNT) (skipn (Z.to_nat CNT) sj)) as JR eqn:EJR. clear EJR.
    pose proof (rng_fp_le _ _ _ _ (fp_le_refl RNG) RGA) as RGA2.
    clear MUc WMc WOKW.
    destruct a as [e|bs]; cbn [read_ret] in *.
    - (* [comment removed for export] *)
      destruct RES as (SJ1' & ERRe & He).
      pose proof BA2 as (ST3 & MI3 & _). pose proof (drv_got_of_aheap AI _ _ _ _ _ P2) as (GSE & PSE & _). unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
      destruct ARG2 as (_ & _ & A1f). destruct (A1f ltac:(lia)) as [B1 A1]. pose proof (astring_facts usp _ _ _ _ _ A1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
      apply implMA_from_evtF.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
      cbn [io_diag ioA io_S].
      eapply afprintf_exit with (LB := [HB (rd_buf st1) A (rd_cap st1)]) (d := DReadError arg1);
        lazymatch goal with
        | |- adiag_args _ _ _ _ _ _ _ => idtac
        | |- forall ms'', aat_exit _ _ _ ms'' -> _ => intros ms'' AE; apply implMA_ret; apply evtF_done; exact AE
        | |- _ => eassumption
        end.
      cbn [adiag_args]. split; [reflexivity|]. exists slack1, RA1. destruct A1 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
      rewrite ?unsigned_lit by lia. unfold GLOBALS_TOP, FmtFp.INT_MAX. destruct (RG1 ltac:(lia)) as [RGa1 RRa1].
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    - destruct RES as (SJ1' & ERRe & Hbs).
      pose proof (bytes_at_bound _ _ _ _ (proj2 (proj1 SJ1'))) as BB. cbn [cells_bytes cbytes app] in BB. rewrite !length_app, length_skipn in BB.
      apply implMA_from_evtF.
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 CNTR LENR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        pose proof BA2 as (ST3 & MI3 & FR3 & AS3 & SE3 & GU3 & TR3 & HI3 & ROD3 & RCS3 & RCB3 & RSG3 & [errv3 ERR3] & SOF3).
        rewrite errno_addr_ATP in ERR3.
        pose proof RSG3 as [(SUNP3 & _ & SWR3 & _) _]. unfold RSTG in SUNP3, SWR3. cbn [r_lo r_hi r_rlo r_rhi] in SUNP3, SWR3.
        pose proof (ASHENV _ _ _ _ _ P2) as ENV2. pose proof ENV2 as (Hgot2 & Hric2 & Hshb2 & Hini2 & Hlay2 & Hrmem2 & _).
        (* [comment removed for export] *)
        pose proof (AI_block AI _ _ _ _ _ (rd_buf st1) A (rd_cap st1) P2 ltac:(left; reflexivity)) as (_ & _ & _ & _ & SHA2 & WRA2 & _ & (RLO' & RHI' & Ar1' & Ar2' & Ar3' & Ar4' & ARR' & ARW')).
        (* [comment removed for export] *)
        apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in SJ1'. destruct SJ1' as [SJa SJb]. cbn [cells_size csize Nat.add] in SJb.
        pose proof (rw_cells_bytes_at _ _ _ _ SJa) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
        (* [comment removed for export] *)
        pose proof BLK as BLK2. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLK2. destruct BLK2 as [BLK1 BLK2].
        cbn [cells_size csize Nat.add] in BLK2. replace (length DATA + 0)%nat with (length DATA) in BLK2 by lia.
        apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [length bs; (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat]) in BLK2; [| cbn; lia].
        cbn [mk_CB_cells app] in BLK2.
        apply (proj1 (rw_cells_app _ _ _ [_] _)) in BLK2. destruct BLK2 as [BLK2 BLK3]. cbn [cells_size csize Nat.add] in BLK3.
        (* [comment removed for export] *)
        pose proof (block_hull RNG m2 (A + LEN) (Z.of_nat (length bs)) RLO' RHI' ltac:(lia) Ar1' Ar2' ltac:(lia) ltac:(lia) ltac:(lia) ARR' ARW') as (HR & HW & Hh1 & Hh2 & Hh3 & Hh4 & Hh5 & Hh6).
        pose proof (hull_props (A + LEN) (Z.of_nat (length bs)) ltac:(lia)) as (_ & _ & _ & _ & Hp5 & Hp6).
        assert (UPD : unpoisoned m2 (A + LEN) (A + LEN + Z.of_nat (length bs))).
        { eapply unpoisoned_sub; [apply (ablock_unpoisoned m2 A (rd_cap st1) SHA2); first [lia | clear -BR4; Z.div_mod_to_equations; lia] | lia | lia]. }
        assert (UPS : unpoisoned m2 6234960 (6234960 + Z.of_nat (length bs))) by (eapply unpoisoned_sub; [exact SUNP3| lia| lia]).
        unfold ASTAGE.
        zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep.
        eapply evtF_cut.
        { eapply (memcpy_i_spec RNG) with (lo := LO) (src := bs) (junk := firstn (length bs) junk)
                                           (RLO1 := 0x5f2340) (RHI1 := 0x602380) (RLO2 := hull_lo (A + LEN)) (RHI2 := hull_hi (A + LEN) (Z.of_nat (length bs)));
            rewrite ?unsigned_lit by lia;
            lazymatch goal with
            | |- mem_inv _ _ => exact MI3
            | |- stk _ _ _ _ => exact ST3
            | |- bytes_at _ _ _ _ => exact SRCB
            | |- rw_cells _ _ _ [CB _ _] => replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; exact BLK2
            | |- rw_cells _ _ _ _ => assumption
            | |- length _ = _ => lia
            | |- app_blk _ _ => first [ eapply ablk_app_blk; [eapply ablk_sub; [exact BR1| lia| lia]| lia] | unfold app_blk, KLOW, KHIGH, KEND in *; lia ]
            | |- unpoisoned _ _ _ => assumption
            | |- wr_at _ _ (shad 0x5f2340) _ => exact SWR3
            | |- wr_at _ _ _ _ => assumption
            | |- rng_aimg _ => exact RGimg
            | |- rng _ (shad 0x5f2340) _ => replace (shad 0x5f2340) with 0x800b6468 by reflexivity; replace (shad 0x602380) with 0x800b8470 by reflexivity;
                                            eapply rng_sub'; [exact RGimsh| lia]
            | |- rng _ (shad _) _ => assumption
            | |- rng _ LO _ => eapply rng_sub'; [exact RGstk| lia]
            | |- rng _ 6234960 _ => eapply rng_sub'; [exact RGimg| lia]
            | |- rng _ (A + LEN) _ => eapply rng_sub'; [exact RGA2| lia]
            | |- _ /\ _ => unfold KEND in *; repeat match goal with |- _ /\ _ => split end; lia
            | |- _ => unfold KHIGH in *; lia
            end. }
        cbv beta. intros ms'' PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUd & WMd & MI4 & ST4 & NB & _).
        rewrite !(unsigned_lit (A + LEN)) in MUd, NB by lia. rewrite !(unsigned_lit (Z.of_nat (length bs))) in MUd, NB by lia.
        rewrite ?(unsigned_lit (usp + -128)) in MUd, ST4 by lia.
        transport_after_call bsegs m2 m3 MUd WMd.
        fix_ret.
        assert (WOKD : Forall (WOK usp) [(usp + -128 - 2240, usp + -128); (A + LEN, A + LEN + Z.of_nat (length bs))]).
        { unfold WOK, WOKb, ALO. constructor; [cbn [fst snd]; lia| constructor; [| constructor]].
          cbn [fst snd]. right; right; right; left. eapply ablk_sub; [exact BR1| lia| lia]. }
        assert (P3 : AHEAP AI L RNG (aps_m s) [HB (rd_buf st1) A (rd_cap st1)] m3).
        { eapply (AI_frame AI); [exact P2| exact MUd| exact WMd|].
          pose proof (AI_layout AI _ _ _ _ _ P2) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
          constructor; [| constructor; [| constructor]]; cbn [fst snd].
          - left. left. lia.
          - right; left. exists (HB (rd_buf st1) A (rd_cap st1)). split; [left; reflexivity| cbn; lia]. }
        assert (BA3 : ABASE' stdout_init m3).
        { eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA2| exact WOKD| exact MUd| exact WMd| exact MI4| exact ST4| |].
          - destruct SE3 as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
            eapply rw_cells_magree; [eapply magree_of_munch; [exact MUd| exact WMd]| exact Hc|]. intros a' Ha'. cbn in Ha' |- *. lia.
          - exists errv3. rewrite errno_addr_ATP.
            first [ exact ERR3 | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUd| exact WMd]| exact ERR3|]; intros a' Ha'; cbn in Ha' |- *; lia ]. }
        assert (ARG3 : AARGV' m3) by (eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKD| exact MUd| exact WMd| exact ARG2]).
        clear MUd WMd WOKD.
        (* [comment removed for export] *)
        zstep. zstep.
        apply evtF_done.
        replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; intros E; rewrite E in K1; apply K1; reflexivity).
        apply implMA_ret. apply evtF_done. cbn [POSTBODY]. unfold RDINV. cbn [rd_content rd_cap rd_buf].
        assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
        rewrite LEN'.
        (* [comment removed for export] *)
        pose proof (rw_cells_CB_join _ _ _ _ _ _ BLK1 ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) by lia; exact NB)) as BLK1'.
        replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) in BLK1' by lia.
        assert (BLK' : rw_cells bsegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (firstn (Z.to_nat (rd_cap st1 - LEN) - length bs) (skipn (length bs) junk))]).
        { apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split; [exact BLK1'|]. cbn [cells_size csize Nat.add].
          replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + Z.of_nat (length DATA) + Z.of_nat (length bs + 0)) by lia.
          replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + length bs))) with (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat by lia. exact BLK3. }
        (* [comment removed for export] *)
        pose proof (rw_cells_CB_join _ _ _ _ _ _ SJb ltac:(replace (6234960 + Z.of_nat (length bs + 0) + Z.of_nat (Z.to_nat CNT - length bs)) with (6234960 + Z.of_nat (Z.to_nat CNT + 0)) by lia; exact SJ2)) as SJc.
        pose proof (rw_cells_CB_join _ _ _ _ _ _ SJa ltac:(replace (6234960 + Z.of_nat (length bs)) with (6234960 + Z.of_nat (length bs + 0)) by lia; exact SJc)) as SJ'.
        do 17 eexists. exists F, fc, m3, A, (DATA ++ bs), (firstn (Z.to_nat (rd_cap st1 - LEN) - length bs) (skipn (length bs) junk)).
        exists (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) sj) ++ JR)), 0x82610.
        split; [replace (Z.of_nat (length bs) + LEN) with (LEN + Z.of_nat (length bs)) by lia; reflexivity|].
        split; [left; split; reflexivity|].
        split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
        split; [| split; [| split; [exact BA3| split; [exact ARG3| split; [exact RG| exact FRM]]]]].
        { split; [exact P3|]. split; [exact SO0|]. split; [exact RK|]. split; [exact HA|]. split; [exact BLK'|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|].
          split; [rewrite length_app; lia|]. split; [exact BR|]. split; [exact RGA2| exact RGAS]. }
        { unfold STAGE, ASTAGE. replace ASTAGE_LEN with (length bs + (Z.to_nat CNT - length bs + (ASTAGE_LEN - Z.to_nat CNT)))%nat at 1 by lia. exact SJ'. }
      + (* [comment removed for export] *)
        assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
        cbn [length Nat.eqb]. apply evtF_done.
        apply implMA_ret. apply evtF_done.
        cbn [POSTBODY]. unfold RDBRK.
        do 17 eexists. exists F, fc, m2, A, (rd_cap st1), DATA, junk.
        split; [rewrite LENZ; cbn [Z.of_nat]; reflexivity|].
        split; [exact HC|]. split; [| split; [exact BA2| split; [exact ARG2| split; [exact RG| exact FRM]]]].
        split; [exact P2|]. split; [exact SO0|]. split; [exact RK|]. split; [exact HA|]. split; [rewrite <- ELEN; exact BLK|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|].
        split; [lia|]. split; [exact BR|]. split; [exact RGA2| exact RGAS].
  Qed.

  (* [comment removed for export] *)
  Lemma rd_read : forall (fd : Z) (st1 : rd_st) (s : APS) RNG x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : amem) (A : Z) (DATA junk sj : list byte),
    3 <= fd < 2^32 ->
    rd_content st1 = map bv_unsigned DATA -> BUF' mm s RNG (rd_buf st1) A (rd_cap st1) DATA junk -> STAGE mm sj -> Z.of_nat (length DATA) < rd_cap st1 ->
    ABASE' stdout_init mm -> AARGV' mm -> RNGS' RNG -> frm0 fc ->
    implMA RNG (rd_read_part fd arg1 st1) s (POSTBODY' fd)
      (GST 0x82654 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 (zlength (rd_content st1))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until sj. intros FD HC BU SJ LT BA ARG RG FRM.
    pose proof BU as (_ & _ & _ & _ & _ & [CAPR CAPK] & LENR & _). unfold MAX_INPUT in CAPR.
    pose proof BA as (_ & MI & _).
    assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    rewrite LENZ.
    apply implMA_from_evtF.
    zstep. zstep. zstep. if_cases KW; zify_cond KW.
    - (* [comment removed for export] *)
      apply evtF_done.
      replace (Z_to_bv 64 (rd_cap st1 + - Z.of_nat (length DATA))) with (Z_to_bv 64 (rd_cap st1 - Z.of_nat (length DATA))) by (f_equal; lia).
      eapply (rd_read_core fd st1 s); try eassumption.
      replace (65536 <? rd_cap st1 - Z.of_nat (length DATA)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      zstep. apply evtF_done.
      eapply (rd_read_core fd st1 s); try eassumption.
      destruct (Z.ltb_spec0 65536 (rd_cap st1 - Z.of_nat (length DATA))); [reflexivity| lia].
  Qed.
End B2.
End CANSEC1.
