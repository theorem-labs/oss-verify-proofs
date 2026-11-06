(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy AF_atexit ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2 AD_main_B3 AD_main_B4 AD_main_C.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Set Keyed Unification.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

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
#[using="Type"] Lemma implMA_retb : forall {X Y} RNG (a : X) (f : X -> @Monad.M APS Y) (s : APS) Q ms,
implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
Proof. intros X Y RNG a f s Q ms H. exact H. Qed.
Section D.
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
Variable J8 : list byte.
Notation AMFRAME' := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 J8).
Notation LO := (ALO usp).
Notation RNGS' := (RNGS rng_fs usp RSTK L argv P0 P1 slack0 slack1 RA0 RA1).
Let WOKo := WOK_outside usp USP16 USPLO USPHI.
Let geoA' := geoA usp USP16 USPLO USPHI.
Hypothesis UM_e48 : In [AMALLOC_PC; 0x809e8] (al_U L).
Hypothesis UM_e9c : In [AMALLOC_PC; 0x80a3c] (al_U L).
Hypothesis UF_ec0 : In [AFREE_PC; 0x80a60] (al_U L).
Hypothesis UF_ff0 : In [AFREE_PC; 0x80b90] (al_U L).
Hypothesis UM_14c : In [AMALLOC_PC; 0x80cc8] (al_U L).
Hypothesis UF_1a0 : In [AFREE_PC; 0x80d5c] (al_U L).
Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
Hypothesis UF0 : In [AFREE_PC] (al_U L).
Notation RUN0' := (RUN0 AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
Hypothesis HUL : HU L.
Hypothesis TRUN : atarget_run_stmtA AI rng_fs.
Notation GST8 pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
Definition ABASE2 (mm : amem) : Prop :=
stk asegs mm LO (usp + -128) /\ mem_inv asegs mm /\ AMFRAME' mm /\ ASTAT TID mm /\ stderr_wfile0 mm
/\ rw_cells asegs mm ssp_guard [C8 canary].
#[using="Type"] Lemma dpost_adrv : forall LB SP m m', aheap_pres CI LB SP m m' -> astk_shadow_pres SP m m' -> adrv_pres AI LB SP m m'.
Proof.
intros LB SP m m' HP HS a Ha Hc _. exact (magree_of_dpost _ _ _ _ _ HP HS a Ha Hc).
Qed.
#[using="Type"] Lemma adrv_magree : forall LB SP m m', adrv_pres AI LB SP m m' ->
magree asegs (fun a => dcli CI LB SP a /\ ~ rin_ivs atrun_ivs a) m m'.
Proof. intros LB SP m m' H a Ha [Hc Hn]. exact (H a Ha Hc Hn). Qed.
Local Ltac not_ivs := unfold atrun_ivs, rin_ivs, AINIT_FLAG; cbn [fst snd]; lia.
#[using="RSTK RSTK_rlo USP16 USPLO USPHI DRV_CI HT BOT geoA'"] Lemma ABASE2_after_adrv : forall LB m m',
adrv_pres AI LB (usp + -128) m m' -> stk asegs m' LO (usp + -128) -> mem_inv asegs m' ->
AMFRAME' m -> ASTAT TID m -> stderr_wfile0 m -> rw_cells asegs m ssp_guard [C8 canary] ->
ASTATX m' ->
ABASE2 m'.
Proof.
intros LB m m' HPR ST' MI' FR AS SE GU AXX.
pose proof (adrv_magree _ _ _ _ HPR) as AG.
pose proof geoA' as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
split; [exact ST'|]. split; [exact MI'|].
split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR|]. intros a Ha. cbn in Ha.
Local Ltac2 Set LiaHints.tbl := fun () => "00E0?11333410480.10313131997936.10314514651888.10316774681328.10319518594416.10325187914480.1032603224944.103 33442538224.10336644959344.10341036490713.87 50231667440.10354721685382.10354721685382.81 54721685382.87 55181160242.81 5715385072.81  5721498072.103 62208600816.10366750907120.10367190418080.1039662484592.103 00000400800<00@00D00H00L00P00T00X00\00`00m01101801<01L01P01T01X01\S2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS3BOT2G21H2HaS2HaS2G42HaS2HaS3BOT2G22G51H2HaS2HaS2HaS2HaS2Ha".
split; [apply (stack_dcli AI usp); lia| not_ivs]. }
split. {
destruct AS as (A1 & A2 & (cdt & thr & sec & tm1 & A3) & _ & A5 & [dso A6] & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & GD & [j1 SH1] & [j2 SH2]).
Ltac tryr2 lo hi := exists (lo, hi); split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto | cbn; lia].
Ltac trc AG lo hi H := eapply rw_cells_magree; [exact AG| exact H| intros a Ha; cbn in Ha; unfold AExit.RSTDIN in Ha; split; [left; right; left; tryr2 lo hi| not_ivs]].
unfold ASTAT.
split; [trc AG 0x5d5368 0x5d5370 A1|]. split; [trc AG 0x5f5680 0x5f5688 A2|].
split; [exists cdt, thr, sec, tm1; trc AG 0x5f56a0 0x5f56b0 A3|].
split; [exact AXX|].
split; [trc AG 0x9ee10 0x9ee11 A5|]. split; [exists dso; trc AG 0x9b480 0x9b488 A6|].
split; [trc AG 0x5f5b00 0x5f5f40 A7|]. split; [trc AG 0x9e000 0x9e008 A8|]. split; [trc AG 0x9df18 0x9dfa8 A9|].
split; [trc AG 0x9df10 0x9df18 A10|]. split; [trc AG 0x9de20 0x9de28 A11|].
split; [trc AG 0x9fc90 0x9fc94 A12|]. split; [trc AG 0x9edc0 0x9edc8 A13|]. split; [trc AG 0x9fd30 0x9fd38 A14|].
split. { eapply gdescs_magree; [exact AG| | exact GD]. intros a Ha. rewrite F_module_dtor.AGLOBALS_length in Ha. split; [| not_ivs].
left. right; left. tryr2 0x9e030 0x9edb0. }
split. { exists j1. eapply rw_cells_magree; [exact AG| exact SH1|]. intros a Ha. cbn in Ha. split; [| rewrite ?shad_div in Ha; unfold ASHOFF in Ha; not_ivs].
apply (ci_drv_sh' AI usp DRV_CI LB 0x20e20 0x22140); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]. }
exists j2. eapply rw_cells_magree; [exact AG| exact SH2|]. intros a Ha. cbn in Ha. split; [| rewrite ?shad_div in Ha; unfold ASHOFF in Ha; not_ivs].
apply (ci_drv_sh' AI usp DRV_CI LB 0x9e030 0x9edb0); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]. }
split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. cbn in Ha.
split; [apply (ci_drv AI usp DRV_CI LB RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; tauto| lia] | not_ivs]. }
eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. unfold ssp_guard in Ha. cbn in Ha.
split; [apply (ci_drv AI usp DRV_CI LB 0x5f5450 0x5f5458); [unfold drv_img_ranges; cbn; tauto| unfold ssp_guard; lia] | not_ivs].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rng_fs_mono RSTK_rlo USP16 USPLO USPHI DRV_CI HT BOT DFREE geoA' UF_ff0 UF0"] Lemma free_return : forall (code : Z) (s : APS) RNG (bufp : AsanCtrl.aptr) (A cap : Z)
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
0 <= code <= COUNT_MAX ->
AHEAP AI L RNG (aps_m s) [HB bufp A cap] mm -> ABASE2 mm -> stdout_file mm (aps_so s) -> RNGS' RNG -> aps_ok L s ->
implMA RNG (afree_M bufp ;;; mret code) s RQEXIT
(GST8 0x80b88 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until mm. intros CR HP1 B2 SOF RG RK.
pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH, COUNT_MAX in *.
pose proof B2 as (ST1 & MI1 & FR1 & AS1 & SE1 & GU1).
pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
apply implMA_from_evtF. zstep. zstep. apply evtF_done.
eapply implMA_bind.
{ Local Ltac2 Set LiaHints.tbl := fun () => "00K0?11083647278.11811402446986.11811402446986.14315344696443.15417282764447.11817383257931.14720893753140.11822030612026.11824510417566.11825686194360.1182896334970.118 30529052096.11831189481627.1473378770747.118 34700506614.11835419511931.11836647051675.15642567031726.11843185561405.11846511830492.11848533638054.11856840016110.11856840016110.1435817865883.147 59315816095.11867935671451.1479215361074.118 00000100200300400500900:00;00H00I00J00K00O00P00W00X00\00`00a00b00o01?01O01S01T01X01YFSSSFS2HaSSS3BOT2G22G51HSFSS2HaFS5USPHIFS2HaS2CRFFS3BOT2CR2G21HS5USPHI3BOT2G21HS5USPHI3BOT2G21HS2HaFS2HaS".
eapply (dfree_M AI DFREE L RNG) with (lo := LO) (p := bufp) (A := A) (n := cap); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
first [ exact HP1 | left; reflexivity | exact MI1 | exact ST1 | exact BOT | unfold AFREE_STACK; lia | exact UF_ff0 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | exact RK | idtac ].
all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
cbv beta. intros [] s2 RNG2 ms3 [SOE3 PO].
destruct PO as (LE2 & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
rewrite ?(unsigned_lit (usp + -128)) in ST3, HPR3, HSP3 by lia.
fix_ret. cbn [aps_m aset_m fst snd] in HEAP3.
pose proof (AI_hb_ids AI _ _ _ _ _ HP1) as ND.
rewrite (lb_remove_headA bufp A cap [] ND) in HPR3, HEAP3.
assert (BA3 : ABASE2 m3).
{ eapply (ABASE2_after_adrv []); [apply dpost_adrv; [exact HPR3| exact HSP3]| exact ST3| exact MI3| exact FR1| exact AS1| exact SE1| exact GU1|].
destruct AS1 as (_ & _ & _ & [reg AXr] & _). exists reg.
eapply atx_stateA_agree; [eapply magree_of_dpost; [exact HPR3| exact HSP3]| | exact AXr].
intros a Ha. unfold atx_state_addrA, atx_addrA in Ha.
repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
first [ apply (ci_drv AI usp DRV_CI _ 0x5f5460 0x5f5490); [unfold drv_img_ranges; cbn; tauto| lia]
| apply (ci_drv AI usp DRV_CI _ 0x5f5580 0x5f5590); [unfold drv_img_ranges; cbn; tauto| lia]
| apply (ci_drv AI usp DRV_CI _ 0x5d4ad0 0x5d4b00); [unfold drv_img_ranges; cbn; tauto| lia]
| apply (ci_drv AI usp DRV_CI _ 0x134320 0x134321); [unfold drv_img_ranges; cbn; tauto| lia] ]. }
pose proof BA3 as (_ & _ & FR3 & AS3 & SE3 & GU3).
assert (RG2' : RNGS' RNG2) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE2| exact RG]).
pose proof RG2' as (RGstk2 & _ & RGimg2 & RGimsh2 & _ & _ & _ & _ & RG02 & _).
apply implMA_ret. unfold RQEXIT.
eapply (amain_return AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 USP16 USPLO USPHI canary);
first [exact FR3 | exact ST3 | exact AS3 | exact HEAP3 | exact MI3 | exact HT | exact RGimg2 | exact RGimsh2 | exact RG02 | exact GU3 | idtac].
- rewrite (aps_so_of_rest _ _ SOE3). eapply stdout_file_magree; [eapply magree_of_dpost; [exact HPR3| exact HSP3]| | exact SOF].
intros a [Ha|Ha].
+ apply (ci_drv AI usp DRV_CI _ RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; tauto| exact Ha].
+ apply (ci_drv AI usp DRV_CI _ 0x5f5b00 0x5f5f40); [unfold drv_img_ranges; cbn; tauto| cbn in Ha |- *; lia].
- apply stderr_wfile0_file. exact SE3.
- eapply rng_sub'; [exact RGstk2| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rng_fs_mono RSTK_lo RSTK_hi RSTK_rlo USP16 USPLO USPHI DRV_CI HT SPG BOT DFREE geoA' UF_ff0 UM_14c UF_1a0 UM0 UF0 HUL TRUN"] Lemma phaseDE : forall bufp A cap DATA cw Lc cfg sc s RNG ms,
RUN0' bufp A cap DATA cw Lc cfg sc s RNG ms ->
implMA RNG (main_tail bufp cw cfg (skipn (Z.to_nat (6 + Lc)) (map bv_unsigned DATA))) s RQEXIT ms.
Proof.
intros bufp A cap DATA cw Lc cfg sc s RNG ms R0.
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
unfold main_tail. rewrite ECFG.
apply implMA_from_evtF. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
eapply implMA_bind.
{ Local Ltac2 Set LiaHints.tbl := fun () => "00T0?10244523423.18411607912823.1841263775811.151 15344696443.15115782763483.15116817863562.1851742630693.151 17605903091.18517794525788.1512058332056.151 24510417566.15127281337226.18228283831542.15133372620191.15133532748151.15134700506614.15134868664067.18640887782655.18441951713402.15142659979371.15143185561405.15143191853440.12 43841896255.15143843977602.11 45264780135.15152854593275.15153012982625.18456840016110.15156840016110.18257750742653.10 57752836288.15159314873579.18559314873579.18668658771084.1517447421819.184 9992210261.151 00000600700=00>00?00@00F00J00S00]00j00k01901=01>01E01F01P01Q01R01S01T01U01V01_01`01f02602F02G02H02O02S02T02^02dS4SPOSSS4LENCSFSS4LEN6S2RRS7RSTK_hiS8RSTK_rloS3BOT2G22G51HSS3SPG3BOT2G21HS2LRFS5USPHISS3SCR4SNEGFFFFFFS7RSTK_loSS4SNEGS5USPHI3BOT2G21HS5USPHI3BOT2G21HFFS3SCR1KS2K2FS3SCR4SPOSS4CAPM".
eapply (TRUN L RNG RSTK) with (lo := LO) (p := bufp) (cap := cap) (LB := [HB bufp A cap]) (canary := canary);
rewrite ?(unsigned_lit (usp + -128)) by lia;
first [ exact P0h | left; reflexivity | exact TR | exact HI | exact (proj1 (proj2 (proj2 AS))) | exact ST | exact BOT | exact MI | exact FRM | exact RCS | exact ROD | exact RCB
| exact HUL | exact UM_14c | exact UF_1a0 | exact UM0 | exact UF0 | exact RGtop | exact RGimg | exact RGimsh | exact RGfs
| exact RRS | exact RRF | exact RRB | reflexivity | idtac ].
all: try (unfold zlength; rewrite ?length_map; unfold ATARGET_RUN_STACK, AHARNESS_STACK; lia).
all: first [ intros b [<-|[]]; do 3 eexists; reflexivity
| rewrite zbytes_map_unsigned'; exact BLKB
| apply map_unsigned_range
| rewrite SO0; exact SOF
| split; [exact GSSP| exact GU]
| clear -G5; Z.div_mod_to_equations; lia
| unfold zlength; rewrite length_map; f_equal; lia
| eapply rng_sub'; [exact RGstk| lia]
| exact RK
| atop_facts; lia ]. }
cbv beta. intros r s1 RNG1 ms1 [LE1 PO].
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1
& -> & RR & MI1 & FRM1 & ST1 & DP & HP1 & SOF1 & SSP1 & AX1 & RK1).
rewrite ?(unsigned_lit (usp + -128)) in ST1, DP by lia.
fix_ret.
assert (BA2 : ABASE2 m1).
{ eapply (ABASE2_after_adrv [HB bufp A cap]); [exact DP| exact ST1| exact MI1| unfold AMFRAME; exact FR| exact AS| exact SE| exact GU| exists true; exact AX1]. }
assert (RG1' : RNGS' RNG1) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE1| exact RG]).
clear DP.
rewrite TB.
destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
-
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
eapply free_return; [unfold COUNT_MAX; lia| exact HP1| exact BA2| exact SOF1| exact RG1'| exact RK1].
-
replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
apply implMA_retb.
apply implMA_from_evtF. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
zstep. zstep. apply evtF_done.
eapply free_return; [unfold COUNT_MAX; lia| exact HP1| exact BA2| exact SOF1| exact RG1'| exact RK1].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End D.
End CANSEC1.
