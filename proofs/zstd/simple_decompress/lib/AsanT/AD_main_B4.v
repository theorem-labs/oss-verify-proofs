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
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2 AD_main_B3.
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





(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section B4.
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
  Notation POSTLOOP' := (POSTLOOP AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation AP1' := (AP1 AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).
  Hypothesis ARGC2 : argc = 2.

  (* [comment removed for export] *)
  Definition RDONE (bufp : AsanCtrl.aptr) (content : list Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem)
           (A cap fd : Z) (DATA junk : list byte),
      ms = RST 0x82684 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF' mm s RNG bufp A cap DATA junk
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  Definition POSTB (r : rd_result) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    match r with
    | RdExit => aat_exit 2 s RNG ms
    | RdDone b c => RDONE b c s RNG ms
    end.

  (* [comment removed for export] *)
  Lemma amain_read_all : forall RNG st (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : amem),
    ABASE' stdout_init mm -> aps_so st = stdout_init -> aps_ok L st -> AHEAP AI L RNG (aps_m st) [] mm -> AARGV' mm -> RNGS' RNG ->
    bytes_at bsegs mm (usp + -8) (le8 (wz 0)) -> frm0 fc -> ASTG mm ->
    implMA RNG (read_all ioS amalloc_M afree_M ASTAGE arg1) st POSTB
      (MS (mkR (wz ASTAGE2_RET) (wz (usp + -128)) gpv tpv t0 t1 t2 (wz 2) S1 (wz 2) (wz (usp + 8)) a2 a3 a4 a5 a6 a7
               S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          bvmap_empty (wz 0x825b8) fc None mm (seg_rom bsegs)).
  Proof.
    intros until mm. intros BA SOI RK AH ARG RG U8 FRM [sj SJ].
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *. atop_facts.
    pose proof ASTAGE_LEN_Z as STGZ. unfold ASTAGE in SJ.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR. rewrite errno_addr_ATP in ERR.
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & RGa0 & RRa0 & RG1). destruct (RG1 ltac:(lia)) as [RGa1 RRa1].
    pose proof ARG as (B0 & A0 & A1f). destruct (A1f ltac:(lia)) as [B1 A1]. pose proof (astring_facts usp _ _ _ _ _ A1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    destruct A1 as (BY1 & HF1 & SL1 & LEN1 & LO1 & RC1 & IR1 & RLO1).
    destruct (drv_got_of_aheap AI _ _ _ _ _ AH) as (_ & _ & _ & GSSP).
    pose proof VARGV as (_ & _ & _ & NONUL & NOSL). pose proof (proj1 (Forall_forall _ _) NONUL _ (nth_In (n:=1%nat) argv [] ltac:(lia))) as A1NN. cbv beta in A1NN.
    assert (A1NOSL : path_has_slash (nth 1 argv []) = false).
    { destruct argv as [|a0' [|a1' l']]; cbn in ARGC2; try lia. cbn [tl] in NOSL. inversion NOSL as [|? ? [X _]]. exact X. }
    assert (STR1' : bytes_at bsegs mm P1 (nth 1 argv [] ++ [Z_to_bv 8 0])).
    { pose proof BY1 as X. unfold zb in X. change (fun z : Z => Z_to_bv 8 z) with (Z_to_bv 8) in X.
      rewrite (zbytes_map_unsigned' (nth 1 argv [])) in X || idtac.
      change (?p ++ Z_to_bv 8 0 :: slack1) with (p ++ ([Z_to_bv 8 0] ++ slack1)) in X. rewrite app_assoc in X. apply bytes_at_app in X. destruct X as [X _]. exact X. }
    unfold read_all. apply implMA_from_evtF.
    pose proof (u64ro_read bsegs mm (usp + 16) [wz P1] 0 (wz P1) (wz (usp + 16)) B1 eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.
    remember READ_FUEL as rf eqn:Erf. clear Erf.
    apply evtF_done.
    replace (map (Z_to_bv 8) arg1) with (nth 1 argv []) by (symmetry; apply zbytes_map_unsigned').
    eapply implMA_bind.
    { eapply implMA_msys.
      eapply (open_spec RNG) with (lo := LO) (errv := errv) (canary := canary);
        rewrite ?(unsigned_lit (usp + -128)) by lia; rewrite ?(unsigned_lit P1) by lia; rewrite ?errno_addr_ATP; unfold ATP; rewrite ?unsigned_lit by lia;
        first [ exact ST | exact STR1' | exact ERR | exact GSSP | exact GU | exact MI | reflexivity | exact A1NN | exact A1NOSL | exact RGimg | idtac ].
      all: unfold got_ssp, ssp_guard, zlength in *; rewrite ?length_map in RGa1;
           first [ lia | eapply rng_sub'; [exact RGstk| lia] | eapply rng_sub'; [exact RGimg| lia] | eapply rng_sub'; [exact RGa1| lia] ]. }
    cbv beta. intros r s' RNG' ms' [-> [-> PO]].
    destruct PO as (u0 & u1 & u2 & b1' & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & FDR).
    unfold ATP in MUc, ERR1. rewrite ?unsigned_lit in MUc by lia. rewrite ?(unsigned_lit (usp + -128)) in ST1 by lia. change (6302896 + -164) with 6302732 in MUc, ERR1.
    transport_after_call bsegs mm m1 MUc WMc.
    fix_ret.
    assert (WOKW : Forall (WOK usp) [(usp + -128 - 112, usp + -128); (6302732, 6302732 + 4)]).
    { unfold WOK, WOKb, ALO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (AH1 : AHEAP AI L RNG (aps_m st) [] m1).
    { eapply (AI_frame AI); [exact AH| exact MUc| exact WMc|]. pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - left. left. lia.
      - left. right; left. exists (0x602c08, 0x602c10). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
    assert (BA1 : ABASE' stdout_init m1).
    { eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| exact ST1| |].
      - destruct SE as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
        first [ exact Hc | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact Hc|]; intros a' Ha'; cbn in Ha' |- *; lia ].
      - eexists. rewrite errno_addr_ATP. exact ERR1. }
    assert (ARG1m : AARGV' m1).
    { eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKW| exact MUc| exact WMc| exact ARG]. }
    clear MUc WMc WOKW.
    pose proof BA1 as (ST1' & _ & FR1 & AS1 & SE1 & GU1 & TR1 & HI1 & ROD1 & RCS1 & RCB1 & RSG1 & _ & SOF1). unfold AMFRAME in FR1.
    apply implMA_from_evtF.
    destruct r as [e|fd]; cbn [open_ret open_errno] in *.
    - (* [comment removed for export] *)
      pose proof (drv_got_of_aheap AI _ _ _ _ _ AH1) as (GSE & PSE & _). unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
      cbn [io_diag ioA io_S].
      eapply afprintf_exit with (LB := []) (d := DCannotOpen arg1);
        lazymatch goal with
        | |- adiag_args _ _ _ _ _ _ _ => idtac
        | |- forall ms'', aat_exit _ _ _ ms'' -> _ => intros ms'' AE; apply implMA_ret; apply evtF_done; exact AE
        | |- _ => eassumption
        end.
      destruct ARG1m as (_ & _ & A1f'). destruct (A1f' ltac:(lia)) as [_ A1']. destruct A1' as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
      cbn [adiag_args]. split; [reflexivity|]. exists slack1, RA1.
      rewrite ?unsigned_lit by lia. unfold GLOBALS_TOP, FmtFp.INT_MAX.
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    - (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. zstep. zstep. apply evtF_done.
      eapply implMA_bind.
      { eapply (dmalloc_M AI DMALLOC L RNG) with (lo := LO); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
          first [ exact AH1 | exact MI1 | exact ST1' | exact BOT | unfold AMALLOC_STACK; lia | unfold AREQMAX; lia | exact UM_e48 | exact UM0 | exact RGtop | exact RK | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
        all: rewrite ?unsigned_lit by lia; unfold AMALLOC_PC; lia. }
      cbv beta. intros r s1 RNG1 ms1 [SOE PO].
      destruct PO as (LE1 & v0 & v1 & v2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MI2 & ST2 & HPR & HSP & RR).
      rewrite ?(unsigned_lit (usp + -128)) in ST2, HPR, HSP by lia.
      fix_ret. cbn [aps_m aset_m fst snd] in RR.
      destruct r as [buf|]; [| destruct RR].
      destruct RR as (A & junk & -> & BR & HEAP2 & BLK & RGN & RGNS & HEXP).
      specialize (HEXP (is_primary_big 65536 ltac:(lia))).
      assert (RG1' : RNGS' RNG1) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE1| exact RG]).
      assert (BA2 : ABASE' stdout_init m2).
      { eapply (ABASE_after_dpost AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI canary);
          [exact HPR| exact HSP| exact HEAP2| exact MI2| exact ST2| exact BA1]. }
      assert (ARG2 : AARGV' m2) by (eapply (AARGV_after_dpost AI usp USP16 USPLO USPHI); [exact HPR| exact HSP| exact ARG1m]).
      assert (SJ2 : STAGE m2 sj).
      { eapply (dpost_stage AI usp DRV_CI); [exact HPR| exact HSP|]. unfold STAGE, ASTAGE. exact SJ. }
      pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
      apply implMA_from_evtF.
      zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. apply evtF_done.
      eapply (implMA_bind RNG1 _ _ s1 (POSTLOOP' fd)).
      { eapply rd_loop; lazymatch goal with |- RDINV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- _ => first [eassumption | lia] end.
        unfold RDINV. cbn [rd_content rd_cap rd_buf zlength length Z.of_nat].
        do 17 eexists. exists bvmap_empty, fc, m2, A, [], junk, sj, 0x825f0.
        split; [reflexivity|]. split; [right; split; reflexivity|]. split; [reflexivity|].
        split; [| split; [exact SJ2| split; [exact BA2| split; [exact ARG2| split; [exact RG1'| exact FRM]]]]].
        split; [exact HEAP2|]. split; [rewrite (aps_so_of_rest _ _ SOE); exact SOI|]. split; [eapply aps_ok_rest; [exact SOE| exact RK]|]. split; [exact HEXP|]. cbn [length Z.of_nat Z.sub].
        split; [replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity; apply (proj2 (rw_cells_app _ _ _ [CB 0%nat []] _)); split; [| cbn [cells_size csize Nat.add]; rewrite Z.add_0_r; exact BLK] |].
        - apply rw_cells_CB0. lia.
        - unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia|]. split; [exact BR|]. split; [exact RGN| exact RGNS]. }
      cbv beta. intros res s2 RNG2 ms2 PO.
      destruct res as [|b c]; cbn [POSTLOOP] in PO.
      { apply implMA_ret. apply evtF_done. exact PO. }
      (* [comment removed for export] *)
      clear dependent m2.
      destruct PO as (x1 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & x23 & Fv2 & fc2 & m3 & A3 & cap3 & DATA3 & junk3
                      & -> & HC3 & BU3 & BA3 & ARG3 & RG3 & FRM3).
      pose proof BA3 as (ST3 & MI3 & FR3 & AS3 & SE3 & GU3 & TR3 & HI3 & ROD3 & RCS3 & RCB3 & RSG3 & [errv3 ERR3] & SOF3). unfold AMFRAME in FR3. rewrite errno_addr_ATP in ERR3.
      pose proof RG3 as (RGstk3 & RGtop3 & RGimg3 & _).
      pose proof BU3 as (P3 & SO3 & RK3 & HA3 & BLK3 & CAP3 & LEN3 & BRR3 & RGA3 & RGAS3).
      pose proof BRR3 as (BQ1 & BQ2 & BQ3 & BQ4). pose proof (ablk_lin _ _ BQ1) as (BM1 & BM2 & BM3 & BM4). unfold AIMG_HI in BM1.
      apply implMA_from_evtF. zstep. zstep. apply evtF_done.
      eapply implMA_bind.
      { eapply implMA_msys.
        eapply (close_spec RNG2) with (lo := LO) (errv := errv3); try reflexivity; rewrite ?errno_addr_ATP; unfold ATP; rewrite ?unsigned_lit by lia;
          first [ exact ST3 | exact ERR3 | exact MI3 | lia | eapply rng_sub'; [exact RGstk3| lia] | eapply rng_sub'; [exact RGimg3| lia] ]. }
      cbv beta. intros r3 s3 RNG3' ms3 [-> [-> PO]].
      destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & -> & MUc & WMc & MI4 & ST4 & ERR4).
      unfold ATP in MUc, ERR4. rewrite ?unsigned_lit in MUc by lia. rewrite ?(unsigned_lit (usp + -128)) in ST4 by lia. change (6302896 + -164) with 6302732 in MUc, ERR4.
      transport_after_call bsegs m3 m4 MUc WMc.
      fix_ret.
      assert (WOKW : Forall (WOK usp) [(usp + -128 - 32, usp + -128); (6302732, 6302732 + 4)]).
      { unfold WOK, WOKb, ALO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      assert (P4 : AHEAP AI L RNG2 (aps_m s2) [HB b A3 cap3] m4).
      { eapply (AI_frame AI); [exact P3| exact MUc| exact WMc|]. pose proof (AI_layout AI _ _ _ _ _ P3) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
        constructor; [| constructor; [| constructor]]; cbn [fst snd].
        - left. left. lia.
        - left. right; left. exists (0x602c08, 0x602c10). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
      assert (BA4 : ABASE' stdout_init m4).
      { eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA3| exact WOKW| exact MUc| exact WMc| exact MI4| exact ST4| |].
        - destruct SE3 as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
          first [ exact Hc | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact Hc|]; intros a' Ha'; cbn in Ha' |- *; lia ].
        - eexists. rewrite errno_addr_ATP. exact ERR4. }
      assert (ARG4 : AARGV' m4) by (eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKW| exact MUc| exact WMc| exact ARG3]).
      assert (BLK4 : rw_cells bsegs m4 A3 [CB (length DATA3) DATA3; CB (Z.to_nat (cap3 - Z.of_nat (length DATA3))) junk3]).
      { first [ exact BLK3 | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact BLK3|]; intros a' Ha'; cbn in Ha' |- *; lia ]. }
      apply implMA_ret. apply evtF_done. cbn [POSTB]. unfold RDONE.
      do 17 eexists. exists Fv2, fc2, m4, A3, cap3, fd, DATA3. exists junk3.
      split; [reflexivity|]. split; [exact HC3|]. split; [| split; [exact BA4| split; [exact ARG4| split; [exact RG3| exact FRM3]]]].
      split; [exact P4|]. split; [exact SO3|]. split; [exact RK3|]. split; [exact HA3|]. split; [exact BLK4|]. split; [exact CAP3|]. split; [exact LEN3|]. split; [exact BRR3|]. split; [exact RGA3| exact RGAS3].
  Qed.
End B4.
End CANSEC1.
