(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AU_kit AU_iface AHarnessU_iface AU_fuzz_kit F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2 AD_main_B3 AD_main_B4 AD_main_C AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Set Keyed Unification.   (* [comment removed for export] *)
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

Section CANSEC1. Context {rc : runConstT} {XP : ExitParams}.
Lemma implMA_retb : forall {X Y} RNG (a : X) (f : X -> @Monad.M APS Y) (s : APS) Q ms,
  implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
Proof. intros X Y RNG a f s Q ms H. exact H. Qed.

(* [comment removed for export] *)
Section D.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variables (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word) (L : alayout).
  Hypothesis RSTK_lo : r_lo RSTK <= ALO usp.
  Hypothesis RSTK_hi : usp + -112 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis URI_CI : forall iv, In iv uri_img_ranges -> In iv CI.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis SPG : usp = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= ALO usp.
  (* [comment removed for export] *)
  Hypothesis XSLO : xp_SLO <= ALO usp.
  Hypothesis XSHI : usp <= xp_SHI.
  Hypothesis HUXL : HUX L.
  Hypothesis SPTOP : In [AFREE_PC] (al_U L).        (* [comment removed for export] *)
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneU_stmt AI rng_fs.
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
  Hypothesis UM_e48 : In [AMALLOC_PC; 0x95410] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0x95464] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0x95488] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0x955b8] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0x956f0] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0x95784] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  (* [comment removed for export] *)

  Notation ioS := (ioA AAllocAsan).
  Notation BUF' := (BUF AI L).
  Notation RUN0' := (RUN0 AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  (* [comment removed for export] *)
  Hypothesis HUL : HU L.
  Hypothesis TRUN : atarget_run_stmtA AI rng_fs.

  (* [comment removed for export] *)
  Notation GST8 pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ABASE2 (tbl : list (Z * Z)) (mm : amem) : Prop :=
    stk asegs mm LO (usp + -128) /\ mem_inv asegs mm /\ AMFRAME' mm /\ ASTAT TID tbl mm /\ stderr_wfile0 mm
    /\ rw_cells asegs mm ssp_guard [C8 canary]
    /\ harness_invA mm /\ rclean mm RSTK.          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma dpost_adrv : forall LB SP m m', aheap_pres CI LB SP m m' -> astk_shadow_pres SP m m' -> adrv_pres AI LB SP m m'.
  Proof.
    intros LB SP m m' HP HS a Ha Hc _. exact (magree_of_dpost _ _ _ _ _ HP HS a Ha Hc).
  Qed.

  Lemma adrv_magree : forall LB SP m m', adrv_pres AI LB SP m m' ->
    magree asegs (fun a => dcli CI LB SP a /\ ~ rin_ivs atrun_ivs a) m m'.
  Proof. intros LB SP m m' H a Ha [Hc Hn]. exact (H a Ha Hc Hn). Qed.

  Local Ltac not_ivs := unfold atrun_ivs, rin_ivs, AINIT_FLAG, ANEWH; cbn [fst snd]; lia.

  Lemma ABASE2_after_adrv : forall LB LB' RNG st RNG0 st0 LB0 m m' tbl tbl',
    adrv_pres AI LB (usp + -128) m m' -> AHEAP AI L RNG st LB' m' -> stk asegs m' LO (usp + -128) -> mem_inv asegs m' -> harness_invA m' ->
    AMFRAME' m -> ASTAT TID tbl m -> stderr_wfile0 m -> rw_cells asegs m ssp_guard [C8 canary] -> rclean m RSTK ->
    AHEAP AI L RNG0 st0 LB0 m (* [comment removed for export] *) -> ATXS tbl' m' ->
    ABASE2 tbl' m'.
  Proof.
    pose proof HT as HTkeep.
    intros LB LB' RNG st RNG0 st0 LB0 m m' tbl tbl' HPR AH' ST' MI' HINV' FR AS SE GU RCS AHOLD TX'.
    pose proof (adrv_magree _ _ _ _ HPR) as AG.
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
    split; [exact ST'|]. split; [exact MI'|].
    split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR|]. intros a Ha. cbn in Ha.
             split; [apply (stack_dcli AI usp); lia| not_ivs]. }
    split. { eapply ASTAT_after_adrv with (LB := LB) (m := m);
               first [ exact HPR | exact AH' | exact MI' | exact AS | exact TX' | exact USP16 | exact USPLO | exact USPHI | exact DRV_CI | exact URI_CI | exact RSTK_rlo | exact RSTK_lo | exact RSTK_hi | exact XSLO | exact XSHI | exact AHOLD | idtac ]. }
    split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
             eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. cbn in Ha.
             split; [apply (ci_drv AI usp DRV_CI LB RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| lia] | not_ivs]. }
    split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. unfold ssp_guard in Ha. cbn in Ha.
             split; [apply (ci_drv AI usp DRV_CI LB 0x662eb0 0x662eb8); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| unfold ssp_guard; lia] | not_ivs]. }
    split; [exact HINV'|].
    eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. pose proof RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
    split; [eapply stack_sh_dcli with (RLO := r_rlo RSTK) (RHI := r_rhi RSTK); first [exact USP16 | exact USPLO | exact USPHI | exact Ha | (atop_facts; lia) | lia]|].
    rewrite !shad_div in Ha. unfold ASHOFF in Ha. not_ivs.
  Qed.

  Lemma ABASE2_of_ABASE : forall so mm, ABASE' so mm -> ABASE2 TBL_MAIN mm.
  Proof. intros so mm (ST & MI & FR & AS & SE & GU & _ & HI & _ & RCS & _). repeat (split; [assumption|]). split; [exact (proj1 HI)| exact RCS]. Qed.

  (* [comment removed for export] *)
  Lemma client_static_cl : forall s s' LB m, aps_cl s' = aps_cl s -> client_static s LB m -> client_static s' LB m.
  Proof. intros s s' LB m E [CL CS]. split; [rewrite E; exact CL| exact CS]. Qed.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma client_static_drop_buf : forall s LBc bufp A cap m, 8 < cap ->
    client_static s (LBc ++ [HB bufp A cap]) m -> client_static s LBc m.
  Proof.
    intros s LBc bufp A cap m HC H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma free_return : forall (code : Z) (s : APS) RNG (bufp : AsanCtrl.aptr) (A cap : Z) (LBc : list ablock)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    0 <= code <= COUNT_MAX ->
    AHEAP AI L RNG (aps_m s) (LBc ++ [HB bufp A cap]) mm -> (LBc = [] \/ exists pc V, LBc = [HB pc V 8]) -> 8 < cap ->
    client_static s (LBc ++ [HB bufp A cap]) mm ->
    ABASE2 TBL_REG mm -> stdout_file mm (aps_so s) -> RNGS' RNG -> aps_ok L s -> frm0 fc ->
    implMA RNG (afree_M bufp ;;; mret code) s (RQEXIT AI)
      (GST8 0x955b0 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros CR HP1 HLBc HCAP CS1 B2 SOF RG RK FRM.
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH, COUNT_MAX in *.
    pose proof B2 as (ST1 & MI1 & FR1 & AS1 & SE1 & GU1 & HINV1 & RCS1).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
    (* [comment removed for export] *)
    apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (dfree_M AI DFREE L RNG) with (lo := LO) (p := bufp) (A := A) (n := cap); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
        first [ exact HP1 | (apply in_or_app; right; left; reflexivity) | exact MI1 | exact ST1 | exact BOT | unfold AFREE_STACK; lia | exact UF_ff0 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | exact RK | idtac ].
      all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
    cbv beta. intros [] s2 RNG2 ms3 [SOE3 PO].
    destruct PO as (LE2 & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
    rewrite ?(unsigned_lit (usp + -128)) in ST3, HPR3, HSP3 by lia.
    fix_ret. cbn [aps_m aset_m fst snd] in HEAP3.
    pose proof (AI_hb_ids AI _ _ _ _ _ HP1) as ND.
    assert (ELB : lb_remove bufp (LBc ++ [HB bufp A cap]) = LBc).
    { destruct HLBc as [-> | (pc & V & ->)]; cbn [app] in ND |- *; [apply (lb_remove_headA bufp A cap [] ND) | apply (lb_remove_secondA bufp A cap (HB pc V 8) [] ND)]. }
    rewrite ELB in HPR3, HEAP3.
    assert (HINV3 : harness_invA m3).
    { destruct HINV1 as [IG SH]. split; [eapply (client_img_pres AI URI_CI); [exact IG| exact HPR3| exact HEAP3| exact MI3] | eapply (client_sh_pres AI URI_CI); [exact HPR3| exact SH]]. }
    assert (TX3 : ATXS TBL_REG m3).
    { pose proof AS1 as (_ & _ & _ & TX1). eapply ATXS_magree; [exact TX1| exact (magree_of_dpost _ _ _ _ _ HPR3 HSP3)|].
      intros a [Ha|Ha].
      - apply (ci_drv AI usp DRV_CI LBc 0x662ec0 0x6630e0); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| lia].
      - unfold aincb_addr in Ha. apply (ci_drv AI usp DRV_CI LBc 0x642150 0x642338); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| lia]. }
    assert (BA3 : ABASE2 TBL_REG m3).
    { eapply (ABASE2_after_adrv LBc); [apply dpost_adrv; [exact HPR3| exact HSP3]| exact HEAP3| exact ST3| exact MI3| exact HINV3| exact FR1| exact AS1| exact SE1| exact GU1| exact RCS1| eassumption| exact TX3]. }
    assert (CS3 : client_static s2 LBc m3).
    { eapply client_static_cl; [exact (aps_cl_ofU _ _ SOE3)|]. eapply (client_static_pres AI URI_CI); [exact HPR3|].
      eapply client_static_drop_buf; [exact HCAP| exact CS1]. }
    pose proof BA3 as (_ & _ & FR3 & AS3 & SE3 & GU3 & _ & RCS3).
    assert (RG2' : RNGS' RNG2) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE2| exact RG]).
    pose proof RG2' as (RGstk2 & RGtop2 & RGimg2 & RGimsh2 & _ & RRS2 & _ & _ & RG02 & _ & _ & _ & RGX2).
    apply implMA_ret. unfold RQEXIT.
    eapply (amain_return AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK RSTK_lo RSTK_hi RSTK_rlo USP16 USPLO USPHI canary XSLO XSHI) with (L := L) (LB := LBc);
      first [exact FR3 | exact ST3 | exact AS3 | exact HEAP3 | exact MI3 | exact HT | exact RGimg2 | exact RGimsh2 | exact RG02 | exact GU3
            | exact HINV3 | exact CS3 | (eapply aps_ok_restU; [exact SOE3| exact RK]) | exact FRM | exact RCS3 | exact RRS2 | exact HUXL | exact RGtop2 | exact RGX2 | exact SPTOP
            | idtac].
    - rewrite (aps_so_of_restU _ _ SOE3). eapply stdout_file_magree; [eapply magree_of_dpost; [exact HPR3| exact HSP3]| | exact SOF].
      intros a [Ha|Ha].
      + apply (ci_drv AI usp DRV_CI _ RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| exact Ha].
      + apply (ci_drv AI usp DRV_CI _ 0x663560 0x663980); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| cbn in Ha |- *; lia].
    - apply stderr_wfile0_file. exact SE3.
    - eapply rng_sub'; [exact RGstk2| lia].
    - destruct HLBc as [-> | (pc & V & ->)]; intros b Hb; cbn [In] in Hb; [destruct Hb| destruct Hb as [<-|[]]; do 3 eexists; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma phaseDE : forall bufp A cap DATA cw Lc cfg sc s RNG ms,
    RUN0' bufp A cap DATA cw Lc cfg sc s RNG ms ->
    dk (aps_m s) <= 16 ->     (* [comment removed for export] *)
    implMA RNG (main_tail bufp cw cfg (skipn (Z.to_nat (6 + Lc)) (map bv_unsigned DATA))) s (RQEXIT AI) ms.
  Proof.
    intros bufp A cap DATA cw Lc cfg sc s RNG ms R0 DK16.
    destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & junk
                    & -> & HD & BU & BA & ARG & RG & FRM).
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR.
    pose proof BU as (P0h & SO0 & RK & HA & BLK & [CAPR CAPK] & LENR & BR & RGA & RGAS). unfold MAX_INPUT in CAPR.
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
    destruct HD as (LEN6 & LENC & CAPM & _ & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB). unfold MAX_INPUT in CAPM.
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    destruct (drv_got_of_aheap AI _ _ _ _ _ P0h) as (_ & _ & _ & GSSP).
    pose proof AS as (ASc0 & _ & _ & TX0). destruct ASc0 as (_ & _ & (cdt & thr & sec & tm1 & LIBC) & _).
    (* [comment removed for export] *)
    assert (WRM : wr_at asegs mm (usp + -128) (al_top L - (usp + -128))).
    { pose proof ARG as (_ & _ & _ & AD).
      pose proof (rw_cells_wr_at asegs _ _ _ 80 FR ltac:(cbn; lia)) as WF.
      assert (TOPB : usp - 160 <= al_top L <= usp / 4096 * 4096 + 4096).
      { unfold al_top. rewrite <- SPG. unfold page_round_up_Z, page_size. clear - G4 G5. Z.div_mod_to_equations. lia. }
      destruct (Z_le_dec (al_top L) (usp + -48)) as [TL|TL].
      - apply (wr_at_le_dkm _ _ 80); [exact WF| lia].
      - replace (al_top L - (usp + -128)) with (80 + (al_top L - (usp + -48))) by lia.
        apply wr_at_join_dkm; [exact WF| | lia| lia].
        replace (usp + -128 + 80) with (usp + -48) by lia.
        apply wr_at_of_view_dkm; [lia| lia|]. intros x Hx. apply AD. lia. }
    unfold main_tail. rewrite ECFG.
    (* [comment removed for export] *)
    apply implMA_from_evtF. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (TRUN L RNG RSTK) with (lo := LO) (p := bufp) (cap := cap) (LB := [HB bufp A cap]) (canary := canary);
        rewrite ?(unsigned_lit (usp + -128)) by lia;
        first [ exact P0h | exact DK16 | exact WRM | left; reflexivity | exact TR | exact (proj1 HI) | exact (proj2 HI _ _ (proj2 SO0)) | exact TX0 | exact LIBC | exact ST | exact BOT | exact MI | exact FRM | exact RCS | exact ROD | exact RCB
              | exact HUL | exact UM_14c | exact UF_1a0 | exact UM0 | exact UF0 | exact RGtop | exact RGimg | exact RGimsh | exact RGfs
              | exact RRS | exact RRF | exact RRB | reflexivity | idtac ].
      all: try (unfold zlength; rewrite ?length_map; unfold ATARGET_RUN_STACK, AHARNESS_STACK; lia).
      all: first [ intros b [<-|[]]; do 3 eexists; reflexivity
                 | rewrite zbytes_map_unsigned'; exact BLKB
                 | apply map_unsigned_range
                 | rewrite (proj1 SO0); exact SOF
                 | split; [exact GSSP| exact GU]
                 | clear -G5; Z.div_mod_to_equations; lia
                 | unfold zlength; rewrite length_map; f_equal; lia
                 | eapply rng_sub'; [exact RGstk| lia]
                 | exact RK
                 | atop_facts; lia ]. }
    cbv beta. intros r s1 RNG1 ms1 [LE1 PO].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & LB1
                    & -> & RR & MI1 & FRM1 & ST1 & DP & HP1 & HINV1 & CS1 & LBC & SOF1 & SSP1 & RK1 & TX1).
    rewrite ?(unsigned_lit (usp + -128)) in ST1, DP by lia.
    fix_ret.
    assert (BA2 : ABASE2 TBL_REG m1).
    { eapply (ABASE2_after_adrv [HB bufp A cap]); [exact DP| exact HP1| exact ST1| exact MI1| exact HINV1| unfold AMFRAME; exact FR| exact AS| exact SE| exact GU| exact RCS| eassumption| exact TX1]. }
    (* [comment removed for export] *)
    assert (ELB1 : exists LBc, LB1 = LBc ++ [HB bufp A cap] /\ (LBc = [] \/ exists pc V, LBc = [HB pc V 8])).
    { destruct LBC as [-> _]. exists []. split; [reflexivity| left; reflexivity]. }
    destruct ELB1 as (LBc & -> & HLBc). clear LBC.
    assert (HCAP8 : 8 < cap) by (clear - CAPR; lia).
    assert (RG1' : RNGS' RNG1) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE1| exact RG]).
    clear DP.
    rewrite TB.
    destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
    - (* [comment removed for export] *)
      replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
      apply implMA_from_evtF. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
      zstep. apply evtF_done.
      apply implMA_bind_assoc. eapply implMA_bind; [apply atarget_alloc_count_spec|].
      cbv beta. intros n s2 RNG2 ms2 (-> & -> & -> & ->). apply implMA_retb.
      fix_ret.
      unfold COUNT_MAX. change (if 0 <? 251 then 0 else 251) with 0.
      apply implMA_from_evtF. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
      apply evtF_done.
      eapply free_return; [unfold COUNT_MAX; lia| exact HP1| exact HLBc| exact HCAP8| exact CS1| exact BA2| exact SOF1| exact RG1'| exact RK1| exact FRM1].
    - (* [comment removed for export] *)
      replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      apply implMA_retb.
      apply implMA_from_evtF. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
      zstep. zstep. apply evtF_done.
      eapply free_return; [unfold COUNT_MAX; lia| exact HP1| exact HLBc| exact HCAP8| exact CS1| exact BA2| exact SOF1| exact RG1'| exact RK1| exact FRM1].
  Qed.
End D.
End CANSEC1.
