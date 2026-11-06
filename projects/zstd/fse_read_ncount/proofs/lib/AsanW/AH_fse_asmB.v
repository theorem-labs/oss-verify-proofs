(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface
AFake5_iface AH_fse_kit AF_fse_iface AF_fse_rd_iface AH_fse_malloc AH_fse_pro AH_fse_B1 AH_fse_fill AH_fse_B2a AH_fse_B2
AH_fse_Hiface AH_fse_Biface AF_fse_rd_asm.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Open Scope mspec_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac cl := repeat match goal with H : _ |- _ => clear H end.
Ltac h_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [cl; lia| reflexivity]) end.
Section CANSEC1. Context {rc : runConstT}.
Section AsmB.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis MONO : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
Hypothesis SM5 : stack_malloc_5_stmt AI fflag rng_fs.
Hypothesis U32R : prod_u32r_stmtA.
Hypothesis I32R : prod_i32r_stmtA.
Hypothesis WBOUND : fse_wbound_stmtA.
Hypothesis WRITE : fse_write_stmtA.
Hypothesis ISERR : fse_iserror_stmtA.
Variables (L : alayout) (RNG0 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(FR : bvmap 5 word) (fc : bv 32) (s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem).
Notation SP := (bv_unsigned sp).
Hypothesis AH0 : AHEAP AI L RNG0 (aps_m s) LB m0.
Hypothesis HLB : forall b, In b LB -> exists p A n, b = HB p A n.
Hypothesis PAY : AHarness_iface.payload_atA LB D pl.
Hypothesis PAYB : bytes_at asegs m0 D (map (Z_to_bv 8) pl).
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis D16 : D mod 16 = 0.
Hypothesis SZ : zlength pl < 2^26.
Hypothesis ST0 : stk asegs m0 lo SP.
Hypothesis BOT : ATOP + 4096 <= lo.
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis SPG : SP + ATRUN_DEPTH = al_sp0 L.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis MI0 : mem_inv asegs m0.
Hypothesis TP : tp = Z_to_bv 64 ATP.
Hypothesis HUL : HU L.
Hypothesis RSTK0 : rng RNG0 lo (al_top L - lo).
Hypothesis RI0 : rng_aimg RNG0.
Hypothesis RFS0 : rng_fs L RNG0.
Hypothesis AOK : aps_ok L s.
Hypothesis S0E : s0 = Z_to_bv 64 (zlength pl).
Hypothesis FRM : frm0 fc.
Hypothesis RAE : ra = Z_to_bv 64 ATRUN_RET.
Hypothesis RISH0 : rng_aimg_sh RNG0.
Let SPA : Z := (SP - 192) - (SP - 192) mod 32.
#[using="AI RNG0 s LB D lo m0 AH0 BOT LOS SPG SP16"] Lemma geomB : 0 <= SP /\ SP + 16 <= al_top L /\ SP < 2^64 /\ al_top L <= 2^47
/\ SP - 208 <= SPA <= SP - 192 /\ SPA mod 32 = 0 /\ SPA + 88 <= SP - 104 /\ ATOP + 4096 + 16384 <= SP.
Proof.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>10223185404.7222437156941.7233909198460.7234947189069.7240874367307.7243786047718.7247706333551.725777501044.72 691677035.63  691677035.72  00000600:00@00_00d00i00o01I01N01SS4SPABS2T1S4SPABS3BOT3LOS3RSP2T23LY13LY44SPAB1HS3LY3S3RSPS4SPABS3BOT3LOS3RSP4SPAB5SPA321HS3RSPS3RSP".
pose proof (harness_topF L SP SPG ltac:(lia)) as [T1 T2].
pose proof (AI_layout AI _ _ _ _ _ AH0) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. fold SPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
unfold AHARNESS_STACK in LOS. repeat split; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="RNG0 s D m0 AH0 HLB BOT LOS SPG SP16 SPA"] Lemma pag_outsideB : forall RNGx st LBF mx F a,
AHEAP AI L RNGx st LBF mx -> In (FB5 F) LBF -> (forall b, In b LB -> In b LBF) -> ablk F (F + 2048) ->
aclient_addr CI LB SP a ->
(a < lo \/ SP <= a) /\ ~ (F <= a < F + 2048) /\ ~ (SHF F <= a < SHF F + 256).
Proof.
intros RNGx st LBF mx F a AHx HF INCL FH Ha. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof geomB as (G1 & G2 & G3 & G4 & _). pose proof atop_range as ATR. unfold AHARNESS_STACK in LOS.
pose proof (ablk_disj_band _ _ FH) as FB. unfold KLS in FB.
Local Ltac2 Set LiaHints.tbl := fun () => "0090>20598018897.1529784366060.8234301889471.2243731946175.1453410728957.8355348168258.1955348168387.2155348168387.279298445489.87 00000@00D00\00n01D01\02402Z036S2FB3A471H2H02H4S2G1S3FH13FH33A471H2H02H42H5S3BOT3ATR3A471H2H0S3BOT3LOS1X3FH22G13ATRS3BOT2Hr3FH13ATR1H2H02H1S3BOT3LOS1X3FH33ATR1H2H0S3BOT2Hr3FH23FH33ATR2FB2DJ3R1c2RB1H2H0S3BOT3LOS2Hr3FH22G13ATR1H2H0".
assert (SB : SHF F = F / 8 + ASHOFF) by (unfold SHF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
rewrite SB. unfold ASHOFF.
destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- clear - X FH2 FH3 FH4 FB ATR BOT LOS G1. Z.div_mod_to_equations. lia.
- pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. cbn in Hr. clear - H Hr FH1 FB ATR BOT. Z.div_mod_to_equations. lia.
- destruct (HLB _ Hb) as (p & A & N & ->). cbn in Hr.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx (INCL _ Hb) HF ltac:(discriminate)) as DJ. cbn [ab_addr ab_size] in DJ.
destruct (AI_block AI _ _ _ _ _ _ _ _ AHx (INCL _ Hb)) as (_ & (R1 & R2 & R3 & R4) & _).
pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a.
pose proof (ablk_disj_band _ _ R1) as RB. unfold KLS in RB.
clear - Hr DJ R1a R1b R1c R2 R3 RB FB FH2 FH3 ATR BOT. Z.div_mod_to_equations. lia.
- assert (A47 : 0 <= a' < 2^47 /\ (ATOP <= a' \/ a' < AIMG_HI)).
{ destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; cbn in Hr; lia|].
destruct (HLB _ Hb') as (p & A & N & E'). discriminate. }
rewrite shad_div. unfold ASHOFF. unfold AIMG_HI in A47.
split; [| split].
+ clear - A47 ATR BOT. Z.div_mod_to_equations. lia.
+ clear - A47 FB FH2 FH3. Z.div_mod_to_equations. lia.
+ clear - A47 FH1 FH2 FH3 ATR. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="L RNG0 s D m0 AH0 HLB BOT LOS SPG SP16 SPA"] Lemma pag_stack0 : forall a, aclient_addr CI LB SP a -> a < lo \/ SP <= a.
Proof.
intros a Ha. pose proof geomB as (G1 & G2 & G3 & G4 & _). pose proof atop_range as ATR. unfold AHARNESS_STACK in LOS.
destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "0060>40463674142.7240465652028.6846168014848.1352620336196.686495059616.71 6496992170.71 00000H00Z00l01201H01]S3BOT3LOS2Hr2G13ATR1H2H0S3BOT3LOS1X2G13ATRS3BOT3ATR3A471H2H0S1X2G1S3BOT3LOS2Hr2G13ATR2BBS3BOT3LOS2Hr2G13ATR1H".
right; lia.
- pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. cbn in Hr. left; lia.
- pose proof (AI_block_bounds AI _ _ _ _ _ _ AH0 Hb) as BB. cbn in Hr. left; lia.
- assert (A47 : 0 <= a' < 2^47).
{ destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; cbn in Hr; lia|].
destruct (HLB _ Hb') as (p & A & N & E'). discriminate. }
left. rewrite shad_div. unfold ASHOFF. clear - A47 ATR BOT. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition pro_post (ms : machine_state) : Prop :=
exists (F : Z) (m : amem) (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (jb jc jd junk : list byte),
ms = MS (mkR (Z_to_bv 64 0x80fdc) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 D) (Z_to_bv 64 (zlength pl)) y12 y13 y14 y15 y16 y17
(Z_to_bv 64 18446744073709551602) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (F + 608))
(Z_to_bv 64 (SHF F + 76)) s7 (Z_to_bv 64 (zlength pl)) (Z_to_bv 64 D) s10 (Z_to_bv 64 (SHF F))
y28 y29 y30 y31)
FR (Z_to_bv 64 0x82564) fc None m (seg_rom asegs)
/\ AHEAP AI L RNG0 (aps_m s) (FB5 F :: LB) m
/\ magree asegs (aclient_addr CI LB SP) m0 m
/\ F mod 2048 = 0 /\ ablk F (F + 2048) /\ F + 2048 <= ATOP /\ rng RNG0 F 2048 /\ rng RNG0 (shad F) 256
/\ mem_inv asegs m /\ stk asegs m lo SPA /\ stk asegs m (SPA + 88) (SP + -104)
/\ rw_cells asegs m (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
/\ rw_cells asegs m SPA [CB 16 jb; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148)); CB 16 jc; C8 (Z_to_bv 64 F); CB 24 jd; C8 (Z_to_bv 64 F)]
/\ rw_cells asegs m F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x15f28); C8 (Z_to_bv 64 0x80e34); CB 2016 junk;
C8 (Z_to_bv 64 (fflag L 5 F))]
/\ rw_cells asegs m (SHF F) (FSH F8S F8S F8S BF8 BF8).
#[using="rng_fs SM5 AH0 HLB ST0 BOT LOS SPG SP16 MI0 TP RSTK0 RI0 RFS0"] Lemma asmB_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
evtF asegs RNG0 pro_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (zlength pl)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom asegs)).
Proof.
intros.
pose proof geomB as (G1 & G2 & G3 & G4 & SPAB & SPA32 & SPA88 & G5).
pose proof atop_range as ATR. pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (fse_rt_of_aheap AI _ _ _ _ _ AH0) as (GOT0 & RIC0 & REAL0 & SHB0 & SUA0 & INI0 & LAY0).
pose proof (fse_got_of_aheap AI _ _ _ _ _ AH0) as (GSU0 & GOTM0).
Local Ltac2 Set LiaHints.tbl := fun () => "00N0?12417112204.7  1511645200.12  15669621851.7  17722280074.13 17986879152.4  18227142408.16419180283614.16428215712174.7  29771511728.7  29786644187.16131573439875.3  33978120264.4  33998759772.7  35419500961.0  37786476787.7  40003881692.16440179956481.12 50152101189.12 50943924590.4  51184631297.3  52107990421.9  56043687309.10 56174447011.8  59111659615.16462708484519.10 64531730152.3  66151427842.16 66272038326.16467040404205.1647381584737.14  00000=00P00T00h00m01501=01D01M01U01V01]01h01i02502A02N02_02f02j03203@03D03L03b03h04704?04G04\S2G22G45SPA88S4SPAB2G54LOS'2O11HS2G5S3BOT2G53ATR3FH33BSFS3BOTS2G13FH2S2G13FH2S2G22G4S2G24SPABS2G13FH2SS2G22G4S4SPAB4LOS'SS2G22G44SPABS2G13FH13FH2S2G22G45SPA88S3BOT4SPAB4LOS'1HS2G22G4S2O2S4LOS'1OS3FH13FH41H2H0S2G2S2G13FH2S3BOT2G34SPAB3ATR4LOS'S4SPABS5F20481H2H02H4S2G13FH2S2G13FH2S4SPAB2G53ATR3FH33BSF".
assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; clear - SPAB G1 G3 LOS' BOT ATR; lia).
assert (ESPA : SPA = (SP - 192) - (SP - 192) mod 32) by reflexivity.
assert (RSTKS : rng RNG0 lo (SP - lo)) by (eapply rng_sub'; [exact RSTK0| clear - G2 LOS' BOT; lia]).
eapply evtF_cut.
{ eapply (@f_pro rc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc D (zlength pl) lo SPA LOS ltac:(clear - BOT; lia)
ltac:(clear - G2 G4; lia) SP16 ESPA RNG0 RSTKS RI0); first [exact ST0| exact MI0| exact GOT0| exact SHB0| exact GSU0| exact SUA0]. }
cbv beta. intros ms1 (m1 & ja & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
assert (NOF5 : forall F' n', ~ In (mkABlock (ABFake 5) F' n') LB) by (intros F' n' Hin; destruct (HLB _ Hin) as (p' & A' & n'' & E'); discriminate).
assert (AH1 : AHEAP AI L RNG0 (aps_m s) LB m1).
{ eapply (AI_frame AI); [exact AH0| exact MU1| exact WM1|]. constructor; [| constructor]. cbn [fst snd].
apply cr_stack; clear - G5 G4 G2; lia. }
assert (AG1 : magree asegs (aclient_addr CI LB SP) m0 m1).
{ eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn [outside].
destruct (pag_stack0 a Ha) as [O|O]; (split; [clear - O LOS' BOT G5; lia| exact I]). }
clear MU1 WM1.
eapply evtF_cut.
{ eapply SM5; first [exact AH1| exact NOF5| exact MI1| exact BOT| exact TP| exact RSTK0| exact RI0| exact RFS0
| rewrite USPA; first [exact STL1| unfold SM5_STACK; clear - SPAB LOS' G2; lia| clear - SPAB G2; lia]]. }
cbv beta. intros ms2 PO.
destruct PO as (F & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & j0 & j1 & j2 & junk
& -> & MI2 & ST2 & HPR2 & AH2 & F2048 & FH & FC & FFC & SHW & RF & RSF).
rewrite USPA in ST2, HPR2. h_retlit.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
assert (INCL2 : forall b, In b LB -> In b (FB5 F :: LB)) by (intros b Hb; right; exact Hb).
assert (INF2 : In (FB5 F) (FB5 F :: LB)) by (left; reflexivity).
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; rewrite FZRB13_size; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SPA88 SPAB G2 G4; lia)) as FRB2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SPA88 SPAB G2 G4; lia)) as FRA2.
pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(clear - SPA88; lia) ltac:(clear - G2 G4; lia)) as STG2.
assert (AG2 : magree asegs (aclient_addr CI LB SP) m0 m2).
{ eapply magree_trans; [exact AG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply aca_monoA; [exact Ha| exact (fun b Hb => Hb)| clear - SPAB; lia]. }
clear AG1 FRB1 FRA1 STG1 STL1 MI1 AH1 HPR2.
pose proof (fse_got_of_aheap AI _ _ _ _ _ AH2) as (_ & GOTM2).
pose proof (fse_rt_of_aheap AI _ _ _ _ _ AH2) as (_ & _ & REAL2 & _).
eapply evtF_cut.
{ eapply (@f_hdr rc sp gp tp s2 s4 s5 s6 s7 s10 s11 FR fc D (zlength pl) lo SPA LOS ltac:(clear - BOT; lia) SP16 ESPA RNG0 RSTKS RI0);
first [exact FRA2| exact FFC| apply fsh0_of_words; exact SHW| exact MI2| exact GOTM2| exact REAL2| exact FH| exact FC| exact F2048| exact RF| exact RSF]. }
cbv beta. intros ms3 (m3 & y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & jb & jc & jd & -> & MU3 & WM3 & MI3 & FRA3 & FFC3 & SH3).
clear FRA2 FFC SHW.
assert (SBF : SHF F = F / 8 + ASHOFF) by (unfold SHF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (BSF : 2147450880 <= SHF F /\ SHF F + 256 <= 17594333495296) by (rewrite SBF; unfold ASHOFF; clear - FH1 FH4; Z.div_mod_to_equations; lia).
pose proof (ablk_disj_band _ _ FH) as FBD. unfold KLS in FBD.
apply (rw_cells_transport asegs [(SPA, SPA + 88); (F, F + 24); (SHF F, SHF F + 256)] m2 m3 (SP + -104) _) in FRB2;
[| exact MU3| exact WM3| rewrite FZRB13_size; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SPA88 BSF FH3 ATR BOT LOS' G5 SPAB FBD; lia].
apply (stk_transport_disjoint asegs [(SPA, SPA + 88); (F, F + 24); (SHF F, SHF F + 256)] m2 m3 (SPA + 88) (SP + -104)) in STG2;
[| exact MU3| exact WM3| cbn [disjoint_from]; clear - SPA88 BSF FH3 ATR BOT LOS' G5 SPAB FBD; lia].
apply (stk_transport_disjoint asegs [(SPA, SPA + 88); (F, F + 24); (SHF F, SHF F + 256)] m2 m3 lo SPA) in ST2;
[| exact MU3| exact WM3| cbn [disjoint_from]; clear - BSF FH3 ATR BOT LOS' G5 SPAB FBD; lia].
assert (AH3 : AHEAP AI L RNG0 (aps_m s) (FB5 F :: LB) m3).
{ eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
- apply cr_stack; clear - SPAB SPA88 G2 G4 BOT LOS'; lia.
- eapply cr_block; [exact INF2| cbn; lia| cbn; lia].
- eapply cr_fshadow; [exact INF2| clear - F2048; Z.div_mod_to_equations; lia| lia| lia| lia| lia]. }
assert (AG3 : magree asegs (aclient_addr CI LB SP) m0 m3).
{ eapply magree_trans; [exact AG2|]. eapply magree_mono; [eapply magree_of_munch; [exact MU3| exact WM3]|]. intros a Ha. cbn [outside].
destruct (pag_outsideB _ _ _ _ F a AH2 INF2 INCL2 FH Ha) as (O1 & O2 & O3).
split; [clear - O1 SPAB SPA88 BOT LOS' G5; lia|]. split; [clear - O2; lia|]. split; [exact O3| exact I]. }
clear AH2 AG2 MU3 WM3 MI2.
apply evtF_done. unfold pro_post.
exists F, m3, y5, y6, y7, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, jb, jc, jd, junk.
split; [reflexivity|]. split; [exact AH3|]. split; [exact AG3|].
split; [exact F2048|]. split; [exact FH|]. split; [exact FC|]. split; [exact RF|]. split; [exact RSF|].
split; [exact MI3|]. split; [exact ST2|]. split; [exact STG2|]. split; [exact FRB2|]. split; [exact FRA3|].
split; [exact FFC3| exact SH3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="AH0 BOT LOS SPG SP16 TP HUL RSTK0 RI0 AOK"] Lemma asmB_create : forall ms1, pro_post ms1 ->
implMA RNG0 (Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) PRODUCER_SIZE) s
(fun r s1' RNG1 ms => exists pP, r = Some pP
/\ fzC_state AI fflag L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms) ms1.
Proof.
intros ms1 PRO.
destruct PRO as (F & m & y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & jb & jc & jd & junk
& -> & AH & AG & F2048 & FH & FC & RF & RSF & MI & ST & STG & FRB & FRA & FFC & SH).
pose proof geomB as (G1 & G2 & G3 & G4 & SPAB & SPA32 & SPA88 & G5).
pose proof atop_range as ATR. pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
Local Ltac2 Set LiaHints.tbl := fun () => "00A0?12417112204.7  17002669873.5  18229238975.14927507234005.5  29771365531.5  29771511728.6  31573439875.3  37786476787.7  40005978475.14941976525601.0  50943924590.4  62708484519.10 62830969335.14964480833740.14964531730152.3  66151427842.16 7443812940.148 00000=00H00P00Q00Z00[00\00h01401501<01R01Z01b01h02702?S2G22G45SPA88S4SPAB4LOS'S2G13FH2SS2G24SPABFSS2G22G44SPABS2G13FH13FH2SS2G22G4S3BOT2G34SPAB3ATR4LOS'S2G13FH2S2G13FH2S4SPABS5F20481H2H02H4S2G13FH2".
assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; clear - SPAB G1 G3 LOS' BOT ATR; lia).
pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
eapply implMA_post_evtF.
{ eapply (prod_create_proofA AI (fuzz_malloc_proofA AI) L RNG0); rewrite ?USPA;
first [ exact AH | exact MI | exact ST | exact BOT | exact TP | exact HU1 | exact RSTK0 | exact RI0 | exact AOK
| (unfold PROD_CREATE_STACK_A, FUZZ_MALLOC_STACK_A, AMALLOC_STACK; clear - LOS' SPAB; lia)
| (clear - SPAB G2; lia) | (clear - SPA32; Z.div_mod_to_equations; lia) ]. }
cbv beta. intros r s1' RNG1 ms2 PO.
destruct PO as (FLE1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & p & P
& -> & -> & MI1 & ST1 & HPR1 & REST1 & BR & AH1 & PCELL & RP & RPS).
rewrite USPA in ST1, HPR1. apply evtF_done.
exists p. split; [reflexivity|].
set (LB1 := FB5 F :: LB) in *.
assert (INF1 : In (FB5 F) LB1) by (left; reflexivity).
Local Ltac xsz := cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length FZRB13].
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR1 FRA ltac:(left; left; xsz; clear - SPAB SPA88 G2 G4; lia)) as FRA1.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR1 FRB ltac:(left; left; xsz; clear - SPAB SPA88 G2 G4; lia)) as FRB1.
pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR1 STG ltac:(clear - SPA88; lia) ltac:(clear - G2 G4; lia)) as STG1.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR1 FFC ltac:(right; left; exists (FB5 F); split; [exact INF1| cbn; lia])) as FFC1.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR1 SH
ltac:(eapply cr_fshadow; [exact INF1| clear - F2048; Z.div_mod_to_equations; lia| lia| lia| rewrite FSH_size; cbn; lia| lia])) as SH1.
assert (AG1 : magree asegs (aclient_addr CI LB SP) m0 m1).
{ eapply magree_trans; [exact AG|]. eapply magree_mono; [exact HPR1|]. intros a Ha.
eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| clear - SPAB; lia]. }
exists P, F, SPA, m1, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, jb, jc, jd, junk.
split; [reflexivity|].
split; [h_retlit; reflexivity|].
split; [exact AH1|]. split; [exact REST1|]. split; [exact FLE1|]. split; [exact AG1|].
split; [exact BR|]. split; [exact RP|]. split; [exact RPS|]. split; [exact PCELL|].
split; [exact F2048|]. split; [exact FH|]. split; [exact FC|].
split; [exact (rng_fp_le _ _ _ _ FLE1 RF)|]. split; [exact (rng_fp_le _ _ _ _ FLE1 RSF)|].
split; [exact FFC1|]. split; [exact SH1|]. split; [exact ST1|]. split; [exact FRA1|].
split; [exact STG1|]. split; [exact FRB1| exact MI1].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Hypothesis SF5 : stack_free_5_stmt AI fflag rng_fs.
Hypothesis READ : fse_read_stmtA AI rng_fs.
Hypothesis FZBB : fzBB_stmt AI fflag.
Hypothesis FZD : fzD_stmt AI fflag rng_fs.
#[using="fflag rng_fs MONO SM5 U32R I32R WBOUND WRITE ISERR AH0 HLB PAY PAYB PLB D16 SZ ST0 BOT LOS SPG SP16 MI0 TP HUL RSTK0 RI0 RFS0 AOK S0E FRM RAE RISH0 SPA SF5 READ FZBB FZD"] Theorem fz_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
implMA RNG0 (fuzz_oneA AAllocAsan pl) s (fuzz_oneA_post AI L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m0)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (zlength pl)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m0 (seg_rom asegs)).
Proof.
intros. rewrite fuzz_oneA_split_fse.
eapply implMA_evtF; [apply asmB_pro|]. intros ms1 PRO.
eapply (implMA_bind _ _ _ _ (fun r s1' RNG1 ms => exists pP, r = Some pP
/\ fzB_state AI fflag L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms)).
{ eapply implMA_post_evtF; [exact (asmB_create ms1 PRO)|].
cbv beta. intros r s1' RNG1 ms2 (pP & -> & FZC).
eapply evtF_mono; [eapply (FZBB U32R I32R WBOUND WRITE ISERR L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0
pP s1' RNG1 ms2 HLB PAY PAYB PLB D16 SZ BOT LOS SPG SP16 TP RSTK0 RI0 RISH0 FZC)|].
cbv beta. intros ms3 FZB. exists pP. split; [reflexivity| exact FZB]. }
cbv beta. intros r s1' RNG1 ms3 (pP & -> & FZB).
exact (FZD MONO SF5 READ L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms3
HLB PAY PLB D16 SZ BOT LOS SPG SP16 S0E FRM TP RAE HUL RSTK0 RI0 RISH0 RFS0 AOK FZB).
Qed.
End AsmB.
#[using="Type"] Theorem fuzz_oneA_of_halves : forall (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop),
(forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R') ->
stack_malloc_5_stmt AI fflag rng_fs -> stack_free_5_stmt AI fflag rng_fs -> fse_read_stmtA AI rng_fs ->
prod_u32r_stmtA -> prod_i32r_stmtA -> fse_wbound_stmtA -> fse_write_stmtA -> fse_iserror_stmtA ->
fzBB_stmt AI fflag -> fzD_stmt AI fflag rng_fs ->
fuzz_oneA_stmt AI rng_fs.
Proof.
intros AI fflag rng_fs MONO SM5 SF5 READ U32R I32R WBOUND WRITE ISERR FZBB FZD. unfold fuzz_oneA_stmt.
intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB D payload lo rstk
AH HLB PAY PAYB PLB D16 SZ HINV ST BOT LOS SPG SP16 RC RLO RHI RRLO S0E MI FRM TP A0E A1E RAE HUL RSTK RI RISH RFS RR AOK.
subst a0 a1.
exact (fz_main AI fflag rng_fs MONO SM5 U32R I32R WBOUND WRITE ISERR L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB D payload lo m
AH HLB PAY PAYB PLB D16 SZ ST BOT LOS SPG SP16 MI TP HUL RSTK RI RFS AOK S0E FRM RAE RISH SF5 READ FZBB FZD
t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Qed.
End CANSEC1.
