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
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface
AFake5_iface AH_fse_kit AF_fse_iface AF_fse_rd_iface AF_fse_prod AH_fse_malloc AH_fse_Eiface AH_fse_E1 AH_fse_E2
AH_fse_Diface AH_fse_D2 AH_fse_Hiface AF_fse_rd_asm AF_fse_leaf AH_fse_D1.
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
Section AsmD.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis MONO : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
Hypothesis SF5 : stack_free_5_stmt AI fflag rng_fs.
Hypothesis READ : fse_read_stmtA AI rng_fs.
Variables (L : alayout) (RNG0 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(FR : bvmap 5 word) (fc : bv 32) (s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem).
Notation SP := (bv_unsigned sp).
Hypothesis HLB : forall b, In b LB -> exists p A n, b = HB p A n.
Hypothesis PAY : AHarness_iface.payload_atA LB D pl.
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis D16 : D mod 16 = 0.
Hypothesis SZ : zlength pl < 2^26.
Hypothesis BOT : ATOP + 4096 <= lo.
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis SPG : SP + ATRUN_DEPTH = al_sp0 L.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis S0E : s0 = Z_to_bv 64 (zlength pl).
Hypothesis FRM : frm0 fc.
Hypothesis TP : tp = Z_to_bv 64 ATP.
Hypothesis RAE : ra = Z_to_bv 64 ATRUN_RET.
Hypothesis HUL : HU L.
Hypothesis RSTK0 : rng RNG0 lo (al_top L - lo).
Hypothesis RI0 : rng_aimg RNG0.
Hypothesis RISH0 : rng_aimg_sh RNG0.
Hypothesis RFS0 : rng_fs L RNG0.
Hypothesis AOK : aps_ok L s.
Notation POST := (fuzz_oneA_post AI L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m0).
#[using="rc D SPG"] Lemma geomD : 0 <= SP /\ SP + 16 <= al_top L /\ SP < 2^64.
Proof.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>22437156941.5643786047718.56691677035.54  691677035.56  00000400900>00CS2T1S3RSPS3RSPS3RSP".
pose proof (harness_topF L SP SPG ltac:(lia)) as [T1 T2].
split; [lia|]. split; [lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="D SPG"] Lemma astk_of_magree : forall m', al_top L <= 2^47 -> magree bsegs (aclient_addr CI LB SP) m0 m' -> astk_shadow_pres SP m0 m'.
Proof.
intros m' G3 MG a Ha. pose proof geomD as (G1 & G2 & G4). pose proof atop_range as ATR. pose proof ATOP_al16 as A16.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>29784546157.6329786415960.6256765676086.228117701232.30 00000400800Q00mS2G1S2G1S2G32Ha2G23ATR1H2H02H42H5S2G32Ha2G23A161H2H02H42H52H9".
assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (SS : shad SP = ASHOFF + SP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
rewrite SA, SS in Ha. unfold ASHOFF in Ha.
destruct (MG a ltac:(clear - Ha ATR G2 G3; Z.div_mod_to_equations; lia)) as [E _]; [| exact E].
replace a with (shad (8 * (a - ASHOFF))) by (apply shad_unshad). apply cl_shadow. left.
unfold ASHOFF. clear - Ha ATR A16 G2 G3. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Frame.
Variables (F P SPA tl msv dsz : Z) (j0 j1 j2 : word).
Hypothesis ESPA : SPA = (SP - 224) - (SP - 224) mod 32.
Hypothesis F2048 : F mod 2048 = 0.
Hypothesis FH : ablk F (F + 2048).
Hypothesis FC : F + 2048 <= ATOP.
Definition D2P (LBx : list ablock) (a : Z) : Prop :=
aclient_addr CI LBx SPA a /\ ~ (F + 1184 <= a < F + 1696) /\ ~ (F + 1760 <= a < F + 1764) /\ ~ (F + 1776 <= a < F + 1780).
#[using="FH"] Lemma d2p_stack : forall LBx a, SPA <= a < 2^47 -> ATOP <= SPA -> D2P LBx a.
Proof. intros LBx a Ha HS. pose proof (ablk_lin _ _ FH) as (_ & _ & F3 & _). split; [left; exact Ha|]. clear - Ha HS F3 FC. Local Ltac2 Set LiaHints.tbl := fun () => "0010=67469470029.900000:S2Ha2HS2F3".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="sp D"] Lemma d2p_frame : forall LBx a, In (FB5 F) LBx -> (F <= a < F + 1184 \/ F + 1780 <= a < F + 2048) -> D2P LBx a.
Proof.
intros LBx a Hin Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>39558551158.7067469470029.70000004008S2HaS2Ha".
split; [apply (cl_block CI LBx SPA (FB5 F) a Hin); cbn; lia|]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="sp D F2048 FH"] Lemma d2p_shadow : forall LBx a, In (FB5 F) LBx -> SHF F <= a < SHF F + 256 -> D2P LBx a.
Proof.
intros LBx a Hin Ha. pose proof (ablk_lin _ _ FH) as (F1 & F2 & F3 & F4). pose proof (ablk_disj_band _ _ FH) as FB. unfold KLS, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>29782367974.7529782367974.7651669538374.1956043687309.1067462802503.5 00000400800J00V00`S2F2S2F2S5F20482Ha1H2H02H4S2F12F41H2H0S2Ha2FB2SB".
assert (SB : 2147450880 <= SHF F /\ SHF F + 256 <= 17594333495296)
by (unfold SHF, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; clear - F1 F4; Z.div_mod_to_equations; lia).
split.
- replace a with (shad (8 * (a - ASHOFF))) by (apply shad_unshad). apply cl_shadow. right; right.
exists 5, F, 2048. split; [exact Hin|]. unfold SHF in Ha. rewrite Z.shiftr_div_pow2 in Ha by lia. unfold ASHOFF in *.
clear - Ha F2048 F2. Z.div_mod_to_equations. lia.
- clear - Ha SB FB. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rng_fs MONO SF5 D HLB BOT LOS SPG SP16 FRM TP RSTK0 RI0 RFS0 ESPA F2048 FH FC"] Lemma asmD_E2 : forall (m4 : amem) (q4 : APS) (R4 : footprint) (k0 j16 : list byte)
(x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word),
AHEAP AI L R4 (aps_m q4) (FB5 F :: LB) m4 ->
magree bsegs (aclient_addr CI LB SP) m0 m4 ->
aps_rest q4 = aps_rest s -> fp_le RNG0 R4 ->
stk bsegs m4 lo SPA ->
rw_cells bsegs m4 SPA (FRA_E F tl msv dsz k0 j16) ->
stk bsegs m4 (SPA + 120) (SP + -104) ->
rw_cells bsegs m4 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells bsegs m4 F [C8 j0; C8 j1; C8 j2] ->
rw_cells bsegs m4 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
rw_cells bsegs m4 (SHF F) (FSH Z64 Z64 F8S BF8 BF8) ->
mem_inv bsegs m4 ->
rng R4 F 2048 -> rng R4 (shad F) 256 ->
implMA R4 (mret 0) q4 POST
(MS (mkR (Z_to_bv 64 0x81268) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 P) x24 x25 (Z_to_bv 64 (SHF F)) x27 x28 x29 x30 x31)
FR (Z_to_bv 64 0x81268) fc None m4 (seg_rom bsegs)).
Proof.
intros m4 q4 R4 k0 j16 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31
AH4 MG4 REST4 FLE4 ST4 FRA4 STG4 FRB4 HDR4 FLP4 SH4 MI4 RF4 RSF4.
pose proof (AI_layout AI _ _ _ _ _ AH4) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof geomD as (G1 & G2 & G4).
apply implMA_ret.
eapply evtF_mono.
{ exact (pE2_proof AI fflag rng_fs L R4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc
x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31
m4 (aps_m q4) LB SPA lo F P tl msv dsz j0 j1 j2 k0 j16
AH4 HLB SP16 ESPA ST4 BOT LOS G2 TP FRA4 STG4 FRB4 F2048 FH FC HDR4 FLP4 SH4 MI4
(rng_fp_le _ _ _ _ FLE4 RSTK0) (rng_fp_le _ _ _ _ FLE4 RI0) (MONO _ _ _ FLE4 RFS0) RF4 RSF4 SF5). }
cbv beta. intros ms' PO.
destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m5 & -> & MI5 & ST5 & HPR5 & AH5).
assert (MG5 : magree bsegs (aclient_addr CI LB SP) m0 m5) by (eapply magree_trans; [exact MG4| exact HPR5]).
unfold fuzz_oneA_post. split; [exact FLE4|].
exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, FR, fc, m5.
split; [reflexivity|]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38691415991.0000001S".
split; [cl; lia|]. split; [exact MI5|]. split; [exact FRM|]. split; [exact ST5|].
split; [exact MG5|]. split; [exact (astk_of_magree m5 LY3 MG5)|]. split; [exact AH5|]. split; [exact I| exact REST4].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HLB"] Lemma lb_ablk : forall R q m LB', AHEAP AI L R q LB' m -> (forall b, In b LB -> In b LB') ->
forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
Proof.
intros R q m LB' AH INCL b Hb. destruct (HLB b Hb) as (p & A & n & ->).
destruct (AI_block AI _ _ _ _ _ _ _ _ AH (INCL _ Hb)) as (_ & (R1 & _) & _). exact R1.
Qed.
#[using="Type"] Lemma frame_vs_lb : forall R q m LBX, AHEAP AI L R q (LBX ++ FB5 F :: LB) m ->
forall b, In b LB -> F + 2048 <= ab_addr b \/ ab_addr b + ab_size b <= F.
Proof.
intros R q m LBX AH b Hb. pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND.
apply NoDup_app_remove_l in ND. inversion ND as [|x l NI _]; subst.
assert (NE : FB5 F <> b) by (intros E; apply NI; rewrite E; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH ltac:(apply in_or_app; right; left; reflexivity)
ltac:(apply in_or_app; right; right; exact Hb) NE) as Dj. cbn in Dj. exact Dj.
Qed.
#[using="rng_fs MONO SF5 D pl HLB SZ BOT LOS SPG SP16 S0E FRM TP RAE HUL RSTK0 RI0 RFS0 AOK ESPA F2048 FH FC"] Lemma asmD_E1 : forall (m3 : amem) (q3 : APS) (R3 : footprint) (pP : AsanCtrl.aptr) (k0 j16 : list byte)
(x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 y2 y3 y4 y5 y6 y8 y9 y11 : word),
AHEAP AI L R3 (aps_m q3) (HB pP P PRODUCER_SIZE :: FB5 F :: LB) m3 ->
magree bsegs (aclient_addr CI LB SP) m0 m3 ->
aps_rest q3 = aps_rest s -> fp_le RNG0 R3 ->
stk bsegs m3 lo SPA ->
rw_cells bsegs m3 SPA (FRA_E F tl msv dsz k0 j16) ->
stk bsegs m3 (SPA + 120) (SP + -104) ->
rw_cells bsegs m3 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells bsegs m3 F [C8 j0; C8 j1; C8 j2] ->
rw_cells bsegs m3 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
rw_cells bsegs m3 (SHF F) (FSH Z64 Z64 Z64 B04 B04) ->
mem_inv bsegs m3 ->
rng R3 F 2048 -> rng R3 (shad F) 256 ->
implMA R3 (Harness.free_opt afree_M (Some pP) ;;; mret 0) q3 POST
(MS (mkR (Z_to_bv 64 0x81248) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
y2 y3 y4 y5 y6 (Z_to_bv 64 P) y8 y9 (Z_to_bv 64 (SHF F)) y11 x28 x29 x30 x31)
FR (Z_to_bv 64 0x81248) fc None m3 (seg_rom bsegs)).
Proof.
intros m3 q3 R3 pP k0 j16 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 y2 y3 y4 y5 y6 y8 y9 y11
AH3 MG3 REST3 FLE3 ST3 FRA3 STG3 FRB3 HDR3 FLP3 SH3 MI3 RF3 RSF3.
pose proof (AI_layout AI _ _ _ _ _ AH3) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof geomD as (G1 & G2 & G4). pose proof atop_range as ATR.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
unfold AHARNESS_STACK in LOS.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof (ablk_disj_band _ _ FH) as FBD. unfold KLS in FBD.
assert (RSTK3 : rng R3 lo (al_top L - lo)) by exact (rng_fp_le _ _ _ _ FLE3 RSTK0).
assert (RI3 : rng_aimg R3) by exact (rng_fp_le _ _ _ _ FLE3 RI0).
Local Ltac2 Set LiaHints.tbl := fun () => "00V0?12419209398.7  13512676932.3  22706556809.12 22706556809.9  27504727679.1  27506827262.3  27506827262.5  28619479699.3  29788558042.20129788740073.12829788741703.14931706468408.17 33998777463.5  35560168644.15936796291674.20037784379593.6  3832670709.7   38953363535.8  41860230027.8  46995087395.0  4733863666.5   50943924840.4  51926799720.3  51926799720.5  53024297377.0  5375601226.21  55648365497.3  55748950874.7  56043687309.10 57229088363.4  58577612600.5  60681875877.8  62708007564.9  64531730152.3  66151427842.16 7443503051.199 966462368.5    966462368.6    00000=00F00_00o01001101201;01G01O01W01f02002802D02Q02^03003B03C03I03Q03R03S03T03e03f03o04=04F04G04W04l05205F05R05[05\S3LY32G24SPABS3FBD3BSFS3BOT3LOS3ATR4SPAB3BSF2HxS3BOT3ATR3BSF2HxFFFS3FBD3BSFS2G13FH23LTRS2G13FH2S2G13FH2S5F20481H2H02H4S3LOS4SPABS2G13FH2S2G13FH23LTRS3LY32G24SPABS3LOS2G24SPABS3BOT3LOS3ATR4SPABS3BOT3LOS3ATR4SPABSS4SPABS3LY32G2FFSS3BOT3LOS3ATR3BSFSS3BOT3LOSS3FH13FH41H2H0S2G44SPABSS2SZ3BOT3LOS3ATRS3BOT3LOS2G43ATR4SPABS4SPABS4SP161H2H02H45SPA32S2G13FH23LTRS2G24SPABF".
assert (RFRA : rng R3 SPA 120) by (eapply rng_sub'; [exact RSTK3| clear - LOS SPAB G2; lia]).
assert (SHFE : SHF F = shad F) by apply SHF_shad.
assert (BSF : 2147450880 <= SHF F /\ SHF F + 256 <= 17594333495296)
by (unfold SHF, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; clear - FH1 FH4; unfold AIMG_HI in *; Z.div_mod_to_equations; lia).
eapply implMA_evtF.
{ exact (pE1_proof R3 gp tp sp y2 y3 y4 y5 y6 y8 y9 y11 FR fc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
m3 SPA F P tl msv dsz k0 j16 ltac:(clear - SPAB LOS BOT ATR; lia) ltac:(clear - SPAB G4; lia) ltac:(unfold KHIGH; clear - SPAB LOS BOT ATR; lia)
F2048 FH FC FRA3 SH3 MI3 (fse_rtall_of_aheap AI _ _ _ _ _ AH3) RFRA RSF3 RI3). }
cbv beta. intros ms' PO.
destruct PO as (m3' & z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & MU & WM & MI3' & FRA3' & SH3').
assert (AH3' : AHEAP AI L R3 (aps_m q3) (HB pP P PRODUCER_SIZE :: FB5 F :: LB) m3').
{ eapply (AI_frame AI); [exact AH3| exact MU| exact WM|].
constructor; [| constructor]. cbn [fst snd]. right; right. right; right. exists 5, F, 2048. split; [right; left; reflexivity|].
unfold SHF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. clear - F2048 FH2. Z.div_mod_to_equations. lia. }
pose proof (lb_ablk _ _ _ _ AH3 ltac:(intros b Hb; right; right; exact Hb)) as LBH.
pose proof (frame_vs_lb _ _ _ [HB pP P PRODUCER_SIZE] AH3) as FVL.
assert (MG3' : magree bsegs (aclient_addr CI LB SP) m0 m3').
{ eapply magree_munch_step; [exact MG3| exact MU| exact WM|]. intros a Ha. cbn. split; [| exact I].
intros Hr. refine (shadow_not_client2048 CI LB SP F a (AI_aci_img AI) (AI_aci_lo AI) FH F2048 ltac:(clear - LOS BOT G1 ATR; lia) LBH FVL _ Ha).
rewrite <- SHFE. exact Hr. }
pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU WM ltac:(cbn [disjoint_from]; clear - BSF ATR BOT LOS; split; [lia| exact I])) as FRB3'.
pose proof (rw_cells_transport _ _ _ _ _ _ HDR3 MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - BSF FBD; split; [lia| exact I])) as HDR3'.
pose proof (rw_cells_transport _ _ _ _ _ _ FLP3 MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear - BSF FBD; split; [lia| exact I])) as FLP3'.
assert (STG3' : stk bsegs m3' (SPA + 120) (SP + -104))
by (eapply stk_transport; [exact STG3| exact MU| exact WM| intros x Hx; left; cbn; clear - Hx BSF ATR BOT LOS SPAB; lia]).
assert (ST3' : stk bsegs m3' lo SPA) by (eapply stk_transport; [exact ST3| exact MU| exact WM| intros x Hx; left; cbn; clear - Hx BSF ATR BOT; lia]).
clear MU WM.
cbn [Harness.free_opt].
destruct (fzrb13_saved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRB3') as [B16 B8]. rewrite S0E in B16. rewrite RAE in B8.
assert (ZL : 0 <= zlength pl < SP) by (unfold zlength in *; clear - SZ LOS BOT ATR; lia).
destruct (harness_uchainF m3' (al_top L) AFREE_PC SP SPA (zlength pl) B16 B8 ZL ltac:(clear - SP16; Z.div_mod_to_equations; lia)
ltac:(clear - SPAB; lia) ltac:(unfold AFREE_PC, ATRUN_RET; lia) G2) as (tr & UC & TR).
destruct HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
destruct (harness_trace_inF _ _ _ _ HU4 HU5 TR) as [HIN LTR].
assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; clear - SPAB G4 LOS BOT ATR; lia).
assert (URA : bv_unsigned (Z_to_bv 64 0x81268) = 0x81268) by (apply unsigned_lit; cl; lia).
eapply implMA_bind.
{ eapply (prod_free_proofA AI L R3 (Z_to_bv 64 0x81268) (Z_to_bv 64 SPA) gp tp z5 z6 z7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P)
z11 z12 z13 z14 z15 z16 z17 y2 y3 y4 y5 y6 (Z_to_bv 64 P) y8 y9 (Z_to_bv 64 (SHF F)) y11 z28 z29 z30 z31
FR fc m3' q3 (HB pP P PRODUCER_SIZE :: FB5 F :: LB) pP P PRODUCER_SIZE lo tr);
rewrite ?USPA, ?URA;
first [exact AH3' | exact (or_introl eq_refl) | exact MI3' | exact ST3' | exact BOT | exact TP | reflexivity | exact UC
| exact HIN | exact LTR | exact RSTK3 | exact (aps_ok_rest L q3 s REST3 AOK)
| unfold AFREE_STACK; clear - LOS SPAB; lia | clear - SPAB G2; lia | clear - SPAB; lia | unfold AFREE_PC; cl; lia
| clear - SPA32; Z.div_mod_to_equations; lia]. }
cbv beta. intros [] q4 R4 ms4 [REST4 PO4]. unfold afree_post in PO4.
destruct PO4 as (FLE4 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m4 & -> & MI4 & ST4 & HPR4 & AH4).
rewrite USPA in ST4, HPR4.
rewrite (lb_remove_headA pP P PRODUCER_SIZE (FB5 F :: LB) (AI_hb_ids AI _ _ _ _ _ AH3')) in HPR4, AH4.
h_retlit.
assert (INF : In (FB5 F) (FB5 F :: LB)) by (left; reflexivity).
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR4 FRA3' ltac:(left; left; cbn; clear - SPAB G4 G2 LY3; unfold FRA_E; cbn; lia)) as FRA4.
pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR4 STG3' ltac:(clear - SPAB; lia) ltac:(clear - G2 LY3; lia)) as STG4.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR4 FRB3' ltac:(left; left; cbn; clear - SPAB G2 LY3; unfold FZRB13; cbn; lia)) as FRB4.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR4 HDR3' ltac:(right; left; exists (FB5 F); split; [exact INF| cbn; lia])) as HDR4.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR4 FLP3' ltac:(right; left; exists (FB5 F); split; [exact INF| cbn; lia])) as FLP4.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR4 SH3'
ltac:(right; right; right; right; exists 5, F, 2048; split; [exact INF|]; rewrite FSH_size;
unfold SHF, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
clear - F2048 FH2; Z.div_mod_to_equations; lia)) as SH4.
assert (MG4 : magree bsegs (aclient_addr CI LB SP) m0 m4).
{ eapply magree_trans; [exact MG3'|]. eapply magree_mono; [exact HPR4|]. intros a Ha.
eapply aca_monoA; [exact Ha| intros b Hb; right; exact Hb| clear - SPAB; lia]. }
assert (FLE04 : fp_le RNG0 R4) by (intros b j Hb; apply FLE4, FLE3, Hb).
eapply (asmD_E2 m4 q4 R4 k0 j16); first [exact AH4| exact MG4| exact REST4 || (rewrite REST4; exact REST3) | exact FLE04 | exact ST4 | exact FRA4
| exact STG4 | exact FRB4 | exact HDR4 | exact FLP4 | exact SH4 | exact MI4 | exact (rng_fp_le _ _ _ _ FLE4 RF3)
| exact (rng_fp_le _ _ _ _ FLE4 RSF3)].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rng_fs MONO SF5 READ HLB PAY PLB D16 SZ BOT LOS SPG SP16 S0E FRM TP RAE HUL RSTK0 RI0 RISH0 RFS0 AOK ESPA F2048 FH FC"] Lemma asmD_D : forall (m2 : amem) (q2 : APS) (R2 : footprint) (pP pB : AsanCtrl.aptr) (B : Z) (jB : list byte)
(bsz rem : Z) (nc data buf' : list Z) (jb jc jd : list byte)
(x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem) ->
AHEAP AI L R2 (aps_m q2) (HB pB B bsz :: HB pP P PRODUCER_SIZE :: FB5 F :: LB) m2 ->
magree bsegs (aclient_addr CI LB SP) m0 m2 ->
aps_rest q2 = aps_rest s -> fp_le RNG0 R2 ->
ablock_range B bsz -> rw_cells bsegs m2 B [CB (Z.to_nat bsz) jB] -> rng R2 B bsz -> rng R2 (shad B) (shlen (bsz + 7)) ->
ablk P (P + 16) -> P mod 16 = 0 -> rng R2 P 16 -> rng R2 (shad P) 2 -> prod_atA m2 P D rem -> unpoisoned m2 P (P + 16) ->
rng R2 F 2048 -> rng R2 (shad F) 256 -> wr_at bsegs m2 F 2048 ->
rw_cells bsegs m2 F [C8 j0; C8 j1; C8 j2] ->
rw_cells bsegs m2 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))] ->
u8arr bsegs m2 (F + 32) (map (Z_to_bv 8) buf') -> length buf' = 512%nat -> firstn (Z.to_nat dsz) buf' = data ->
u8arr bsegs m2 (F + 608) (u16s (map (Z_to_bv 64) nc)) ->
rw_cells bsegs m2 (F + 1760) [C4 (Z_to_bv 64 255)] ->
rw_cells bsegs m2 (SHF F) (FSH Z64 Z64 Z64 B04 B04) ->
stk bsegs m2 lo SPA ->
rw_cells bsegs m2 SPA [CB 24 jb; C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F);
C8 (Z_to_bv 64 (F + 1760)); CB 8 jc; C8 (Z_to_bv 64 (SHF F + 148)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F);
C8 (Z_to_bv 64 msv); CB 16 jd; C8 (Z_to_bv 64 F)] ->
stk bsegs m2 (SPA + 120) (SP + -104) ->
rw_cells bsegs m2 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
mem_inv bsegs m2 ->
bytes_at bsegs m2 D (map (Z_to_bv 8) pl) -> unpoisoned m2 D (D + zlen pl) ->
implMA R2 (Harness.free_opt afree_M (Some pB) ;;; (Harness.free_opt afree_M (Some pP) ;;; mret 0)) q2 POST
(MS (mkR (Z_to_bv 64 0x810c4) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 B) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 dsz) (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 1760)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 bsz)
(Z_to_bv 64 P) (Z_to_bv 64 (F + 608)) x25 (Z_to_bv 64 (SHF F)) x27 x28 x29 x30 x31)
FR (Z_to_bv 64 0x810c4) fc None m2 (seg_rom bsegs)).
Proof.
intros m2 q2 R2 pP pB B jB bsz rem nc data buf' jb jc jd x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31
EA AH2 MG2 REST2 FLE2 BRG BCELL RB RBS PBLK P16 RP RPS PROD UP RF RSF WRF HDR FLP DATAA LB' FBUF NCA MSVC SH ST FRA STG FRB MI
PAYB UD.
pose proof (AI_layout AI _ _ _ _ _ AH2) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof geomD as (G1 & G2 & G4). pose proof atop_range as ATR.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof (ablk_disj_band _ _ FH) as FBD. unfold KLS in FBD.
pose proof (ablk_lin _ _ PBLK) as (PB1 & PB2 & PB3 & PB4). unfold AIMG_HI in PB1.
destruct BRG as (BR1 & BR2 & BR3 & BR4).
pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
assert (RSTK2 : rng R2 lo (al_top L - lo)) by exact (rng_fp_le _ _ _ _ FLE2 RSTK0).
assert (RI2 : rng_aimg R2) by exact (rng_fp_le _ _ _ _ FLE2 RI0).
assert (RISH2 : rng_aimg_sh R2) by exact (rng_fp_le _ _ _ _ FLE2 RISH0).
assert (RFS2 : rng_fs L R2) by exact (MONO _ _ _ FLE2 RFS0).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
Local Ltac2 Set LiaHints.tbl := fun () => "0140?12133286072.1  12292813217.0  12419209398.6  15605126675.5  17614587087.1  19473350319.3  23135524303.1  23490941431.1  24194177746.0  24978311096.3  26492564390.15 26492567317.13 26492662054.15 27504727679.1  27506827262.3  27507234005.5  28573892092.15 29293664164.2  29788558041.32730971753928.3  31012612437.0  31706468408.17 33392934435.2  33978121038.4  33998759772.5  34940283379.8  35560168644.28436796291673.32637775326631.14 37784379593.6  37920233300.15 38332514468.2  39188636933.0  39268637205.0  39556451084.3  39698210859.1  40380733653.4  41514713972.8  44813643624.3  44813919299.5  46059971268.4  4734242265.5   50943924840.4  52898775745.5  55074836728.2  55340206399.3  55648365497.3  55734320097.9  56043687309.10 56172344473.4  5865821488.3   59848598574.2  60174819656.8  60666982686.8  62708484519.9  63020948409.5  63182574115.0  64022352745.3  64531730152.3  64962341151.11 65685863065.4  66151427842.16 66595827586.3  7340735339.1   7443503048.325 765563767.4    8383862316.2   966462368.5    00000100200?00@00A00E00F00G00H00M00l01C01^01_01`01a02;02@02[02_02`02o03003803C03R03i04D04S04`05;05@05A05B05F05G05L05\05]05^05f05l06406906>06C06D06N06\06`06e06j07907J07`07i07j07o08508K08P08l09009109L09T09Y09bSSS3LY32G24SPABSSS2HaSSSS3BL4S3BOT3ATR4SPAB4LOS'3PBD3BBD3BSFS3BOT4SPAB4LOS'3PB33BL3S3BOT4SPAB4LOS'3FH33DBF3DPFFFFS3BOT4SPAB4LOS'3PB33BL32HxS3FH1S3LB'2G13FH23PB23BL22Q43LTRS2HrSS5F20481H2H02H4SS3LY32G2S4SPAB4LOS'S3BOT4SPAB4LOS'S3LB'2G13FH23PB23BL22Q4S3LB'2G13FH23PB23BL22Q43LTRS1H2H02H42H52H8S3LY32G24SPABS3BOT4SPAB4LOS'3FH33DBF3DPFS3FH1SSS2HrSS3D3jS3LY32G24SPAB2HaFFS2Q63Q11S4SPABS3LY32G2S3D1jS3PB1S3Q12SS3BOT4LOS'S3FH13FH41H2H0S2G2S3BL1S3BL2S3BOT4SPAB4LOS'S2SZ3BOT3ATR4LOS'S3BOT2G43ATR4SPAB4LOS'S4SPAB2HrSS3Q11S4SPABS3BOT3LY32G24SPAB4LOS'S3D2jS3BR41H2H02H43D164SP165SPA32S2HaSS3LB'2G13FH23PB23BL22Q43LTRS2Q63Q11S3FH1S2G24SPAB".
pose proof (fseA_facts pl (zlen pl) AB ltac:(cl; lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (Q1 & Q2 & V & Q4 & _ & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
set (LB2 := HB pB B bsz :: HB pP P PRODUCER_SIZE :: FB5 F :: LB) in *.
pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as ND2.
assert (DBP : B + bsz <= P \/ P + 16 <= B).
{ assert (NE : HB pB B bsz <> HB pP P PRODUCER_SIZE) by (intros E; inversion ND2 as [|x l NI _]; apply NI; rewrite E; left; reflexivity).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) NE) as Dj. cbn in Dj. exact Dj. }
assert (DBF : B + bsz <= F \/ F + 2048 <= B).
{ assert (NE : HB pB B bsz <> FB5 F) by discriminate.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) NE) as Dj. cbn in Dj. exact Dj. }
assert (DPF : P + 16 <= F \/ F + 2048 <= P).
{ assert (NE : HB pP P PRODUCER_SIZE <> FB5 F) by discriminate.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) NE) as Dj. cbn in Dj. exact Dj. }
assert (NIB : ~ In (HB pB B bsz) LB) by (intros Hb; inversion ND2 as [|x l NI _]; apply NI; right; right; exact Hb).
assert (NIP : ~ In (HB pP P PRODUCER_SIZE) LB).
{ intros Hb. inversion ND2 as [|x l _ ND3]. inversion ND3 as [|x' l' NI _]. apply NI. right. exact Hb. }
assert (DFACTS : ((pl = [] /\ D = AEMPTY) \/ ablk D (D + zlen pl)) /\ rng R2 D (zlen pl) /\ rng R2 (shad D) (nshad (zlen pl))
/\ (D + zlen pl <= P \/ P + 16 <= D) /\ (D + zlen pl <= F \/ F + 2048 <= D) /\ (B + bsz <= D \/ D + zlen pl <= B)).
{ destruct PAY as [(pD & HinD & NZ)|(-> & ->)].
- unfold zlength in HinD, NZ.
assert (IN2 : In (HB pD D (zlen pl)) LB2) by (right; right; right; exact HinD).
destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 IN2) as (_ & (DR1 & DR2 & DR3 & DR4) & RDx & RDSx & _).
assert (NE1 : HB pB B bsz <> HB pD D (zlen pl)) by (intros E; apply NIB; rewrite E; exact HinD).
assert (NE2 : HB pP P PRODUCER_SIZE <> HB pD D (zlen pl)) by (intros E; apply NIP; rewrite E; exact HinD).
assert (NE3 : FB5 F <> HB pD D (zlen pl)) by discriminate.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) IN2 NE1) as D1j.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(right; left; reflexivity) IN2 NE2) as D2j.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(right; right; left; reflexivity) IN2 NE3) as D3j.
cbn [ab_addr ab_size] in D1j, D2j, D3j. unfold PRODUCER_SIZE in D2j.
split; [right; exact DR1|]. split; [exact RDx|]. split; [exact RDSx|].
split; [clear - D2j; lia|]. split; [clear - D3j; lia| clear - D1j; lia].
- cbn [length Z.of_nat]. unfold AEMPTY.
split; [left; split; reflexivity|].
split; [eapply rng_sub'; [exact RI2| cl; lia]|].
split; [eapply rng_sub'; [exact RISH2| rewrite shad_div, nshad_div; unfold ASHOFF; cbn [Z.of_nat]; cl; Z.div_mod_to_equations; lia]|].
split; [clear - PB1; lia|]. split; [clear - FH1; lia| clear - BL1; lia]. }
destruct DFACTS as (DLOC & RD & RDS & DP & DF & BD).
destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity))
as (_ & _ & _ & _ & SHBB & _ & _ & (RLOB & RHIB & RL1 & RL2 & RL3 & RL4 & RLR & RLW)).
assert (UB : unpoisoned m2 B (B + bsz))
by (apply ablock_unpoisonedR; [exact SHBB| clear - BR4; Z.div_mod_to_equations; lia| clear - BL2; lia| clear - Q6 Q11; lia| clear - BL4; lia]).
assert (SPT' : SP + 16 <= 2^47) by (clear - G2 LY3; lia).
assert (RSTKs : rng R2 lo (SP - lo)) by (eapply rng_sub'; [exact RSTK2| clear - G2; lia]).
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
assert (SZ26 : zlen pl < 2^26) by (unfold zlength in SZ; exact SZ).
apply implMA_from_evtF.
eapply (pD1 prod_u32r_proofA gp tp sp FR fc SPA lo F P D B pl R2 LOS BOT SPT' SP16 ESPA RSTKs RI2 FH F2048 RF RSF PBLK P16 RP RPS
DLOC D8 RD RDS DP DF PLB SZ26 bsz RLOB RHIB BR1 BR4 ltac:(clear - Q6 Q11; lia) RB RBS DBP BD DBF
(conj RL1 (conj RL2 (conj RL3 (conj RL4 RLR))))
x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 m2 _ tl msv dsz rem nc data buf' jB jb jc jd
EA FRA DATAA LB' FBUF BCELL PROD SH ST MI (fse_rtall_of_aheap AI _ _ _ _ _ AH2) PAYB UP UD UB RLW).
intros m3 junkF remF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y25 y28 y29 y30 y31
FT BA3 PR3 FRA3 ST3 MU3 WM3 MI3.
unfold W_D in MU3.
pose proof (fseB_tail_spec pl rem dsz bsz AB ltac:(clear - Q12; lia) ltac:(clear - Q11; lia)) as TS. rewrite FT in TS.
destruct TS as (JL & JB & _). unfold FseNCount.Zlength in JL. apply all_bytes_Forall in JB.
pose proof (lb_ablk _ _ _ _ AH2 ltac:(intros b Hb; right; right; right; exact Hb)) as LBH.
pose proof (frame_vs_lb _ _ _ [HB pB B bsz; HB pP P PRODUCER_SIZE] AH2) as FVL.
assert (PVL : forall b, In b LB -> P + 16 <= ab_addr b \/ ab_addr b + ab_size b <= P).
{ intros b Hb. assert (NE : HB pP P PRODUCER_SIZE <> b) by (intros E; apply NIP; rewrite E; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(right; left; reflexivity) ltac:(right; right; right; exact Hb) NE) as Dj.
cbn in Dj. unfold PRODUCER_SIZE in Dj. exact Dj. }
assert (BVL : forall b, In b LB -> B + bsz <= ab_addr b \/ ab_addr b + ab_size b <= B).
{ intros b Hb. assert (NE : HB pB B bsz <> b) by (intros E; apply NIB; rewrite E; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; right; right; exact Hb) NE) as Dj.
cbn in Dj. exact Dj. }
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
pose proof (ablk_disj_band _ _ PBLK) as PBD. pose proof (ablk_disj_band _ _ BR1) as BBD. unfold KLS in PBD, BBD.
assert (BSF : 2147450880 <= SHF F /\ SHF F + 256 <= 17594333495296)
by (unfold SHF, ASHOFF; rewrite Z.shiftr_div_pow2 by (cl; lia); clear - FH1 FH4; Z.div_mod_to_equations; lia).
assert (MG3 : magree bsegs (aclient_addr CI LB SP) m0 m3).
{ eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a Ha. cbn.
split; [intros Hr; exact (app_not_client CI LB SP P 16 a HCI HCI0 PBLK ltac:(clear - LOS' BOT SPAB ATR G1; lia) LBH PVL ltac:(clear - Hr; lia) Ha)|].
split; [intros Hr; exact (app_not_client CI LB SP B bsz a HCI HCI0 BR1 ltac:(clear - LOS' BOT SPAB ATR G1; lia) LBH BVL Hr Ha)|].
split; [intros Hr; exact (stack_not_client CI LB SP (SPA - 2224) a HCI HCI0 LBH ltac:(clear - LOS' BOT SPAB ATR; lia) ltac:(clear - Hr SPAB; lia) Ha)| exact I]. }
assert (AH3 : AHEAP AI L R2 (aps_m q2) LB2 m3).
{ eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
constructor; [cbn; right; left; exists (HB pP P PRODUCER_SIZE); split; [right; left; reflexivity| cbn; unfold PRODUCER_SIZE; cl; lia]|].
constructor; [cbn; right; left; exists (HB pB B bsz); split; [left; reflexivity| cbn; cl; lia]|].
constructor; [cbn; left; left; clear - LOS' BOT SPAB G2 LY3 ATR; lia| constructor]. }
Local Ltac xd := cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length FRA_E FZRB13].
assert (NCA3 : u8arr bsegs m3 (F + 608) (u16s (map (Z_to_bv 64) nc))).
{ eapply u8arr_transport; [exact NCA| exact MU3| exact WM3|]. rewrite u16s_length, length_map, Q4. xd.
clear - DPF DBF FH3 LOS' BOT SPAB ATR. lia. }
pose proof (rw_cells_transport _ _ _ _ _ _ MSVC MU3 WM3 ltac:(xd; clear - DPF DBF FH3 LOS' BOT SPAB ATR; lia)) as MSVC3.
pose proof (rw_cells_transport _ _ _ _ _ _ HDR MU3 WM3 ltac:(xd; clear - DPF DBF FH3 LOS' BOT SPAB ATR; lia)) as HDR3.
pose proof (rw_cells_transport _ _ _ _ _ _ FLP MU3 WM3 ltac:(xd; clear - DPF DBF FH3 LOS' BOT SPAB ATR; lia)) as FLP3.
pose proof (rw_cells_transport _ _ _ _ _ _ SH MU3 WM3 ltac:(rewrite FSH_size; xd; clear - BSF PBD BBD LOS' BOT SPAB ATR; lia)) as SH3.
pose proof (rw_cells_transport _ _ _ _ _ _ FRB MU3 WM3 ltac:(xd; unfold FZRB13; xd; clear - PB3 BL3 SPAB ATR BOT LOS'; lia)) as FRB3.
assert (STG3 : stk bsegs m3 (SPA + 120) (SP + -104))
by (eapply stk_transport; [exact STG| exact MU3| exact WM3| intros x Hx; left; cbn; clear - Hx PB3 BL3 SPAB ATR BOT LOS'; lia]).
pose proof (wr_at_transport _ _ _ _ _ WRF WM3) as WRF3.
destruct (rw_cells_of_wr_at _ m3 (F + 1184) 512 ltac:(eapply wr_at_sub; [exact WRF3| cl; lia| cl; lia])
(no_image_asan (F + 1184) (F + 1184 + 512) ltac:(clear - FH1; lia)) ltac:(cl; lia)) as (jrt & _ & RTC3).
destruct (rw_cells_of_wr_at _ m3 (F + 1776) 4 ltac:(eapply wr_at_sub; [exact WRF3| cl; lia| cl; lia])
(no_image_asan (F + 1776) (F + 1776 + 4) ltac:(clear - FH1; lia)) ltac:(cl; lia)) as (jtl & _ & TLC3).
change (Z.to_nat 512) with 512%nat in RTC3. change (Z.to_nat 4) with 4%nat in TLC3.
assert (NOF2 : forall F' k, ~ In (mkABlock (ABFake 0) F' k) LB2).
{ intros F' k [E|[E|[E|Hin]]]; try discriminate. destruct (HLB _ Hin) as (p' & A' & n' & E'). discriminate. }
assert (LBH2 : forall b, In b LB2 -> ablk (ab_addr b) (ab_addr b + ab_size b)).
{ intros b [<-|[<-|[<-|Hb]]]; [exact BR1| exact PBLK| exact FH| exact (LBH b Hb)]. }
eapply evtF_cut.
{ exact (pD2_proof AI rng_fs READ fse_iserror_proofA L R2 gp tp sp FR fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y25 y28 y29 y30 y31
m3 (aps_m q2) LB2 SPA lo F P B pB pl tl msv dsz bsz rem nc data junkF jb jd jrt jtl
EA PLB SZ26 JB JL AH3 NOF2 LBH2 (or_intror (or_intror (or_introl eq_refl))) (or_introl eq_refl) SP16 ESPA ST3 BOT LOS G2 TP
F2048 FH FC FRA3 NCA3 RTC3 MSVC3 TLC3 BA3 SH3 MI3 RSTK2 RI2 RFS2 RF RSF). }
cbv beta. intros ms' PO.
destruct PO as (z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z18 & z19 & z20 & z21 & z22 & z24 & z25 & z28 & z29 & z30 & z31 & m4
& -> & MI4 & ST4 & MG4' & AH4).
change (magree bsegs (D2P LB2) m3 m4) in MG4'.
assert (ASP : ATOP <= SPA) by (clear - LOS' BOT SPAB ATR; lia).
assert (INF2 : In (FB5 F) LB2) by (right; right; left; reflexivity).
assert (FRA4 : rw_cells bsegs m4 SPA (FRA_E F tl msv dsz jb jd)).
{ eapply rw_cells_magree; [exact MG4'| exact FRA3|]. xd. intros a Ha. apply d2p_stack; [clear - Ha G2 LY3 SPAB; lia| exact ASP]. }
assert (STG4 : stk bsegs m4 (SPA + 120) (SP + -104)).
{ eapply stk_magree; [exact MG4'| exact STG3|]. intros a Ha. apply d2p_stack; [clear - Ha G2 LY3 SPAB; lia| exact ASP]. }
assert (FRB4 : rw_cells bsegs m4 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
{ eapply rw_cells_magree; [exact MG4'| exact FRB3|]. unfold FZRB13; xd. intros a Ha. apply d2p_stack; [clear - Ha G2 LY3 SPAB; lia| exact ASP]. }
assert (HDR4 : rw_cells bsegs m4 F [C8 j0; C8 j1; C8 j2]).
{ eapply rw_cells_magree; [exact MG4'| exact HDR3|]. xd. intros a Ha. apply d2p_frame; [exact INF2| clear - Ha; lia]. }
assert (FLP4 : rw_cells bsegs m4 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))]).
{ eapply rw_cells_magree; [exact MG4'| exact FLP3|]. xd. intros a Ha. apply d2p_frame; [exact INF2| clear - Ha; lia]. }
assert (SH4 : rw_cells bsegs m4 (SHF F) (FSH Z64 Z64 Z64 B04 B04)).
{ eapply rw_cells_magree; [exact MG4'| exact SH3|]. rewrite FSH_size. xd. intros a Ha. apply d2p_shadow; [exact INF2| clear - Ha; lia]. }
assert (MG4 : magree bsegs (aclient_addr CI LB SP) m0 m4).
{ eapply magree_trans; [exact MG3|]. eapply magree_mono; [exact MG4'|]. intros a Ha.
assert (NF : ~ (F <= a < F + 2048)) by (intros Hr; exact (app_not_client CI LB SP F 2048 a HCI HCI0 FH ltac:(clear - LOS' BOT SPAB ATR G1; lia) LBH FVL Hr Ha)).
split; [eapply aca_monoA; [exact Ha| intros b Hb; right; right; right; exact Hb| clear - SPAB; lia]|].
split; [intros Hr; apply NF; clear - Hr; lia|]. split; intros Hr; apply NF; clear - Hr; lia. }
clear MG4' MG3 FRA3 STG3 FRB3 HDR3 FLP3 SH3 NCA3 MSVC3 RTC3 TLC3 BA3 PR3.
zstep. zstep.
apply evtF_done.
cbn [Harness.free_opt].
destruct (fzrb13_saved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRB4) as [B16 B8]. rewrite S0E in B16. rewrite RAE in B8.
assert (ZL : 0 <= zlength pl < SP) by (unfold zlength in *; clear - SZ LOS' BOT ATR; lia).
destruct (harness_uchainF m4 (al_top L) AFREE_PC SP SPA (zlength pl) B16 B8 ZL ltac:(clear - SP16; Z.div_mod_to_equations; lia)
ltac:(clear - SPAB; lia) ltac:(unfold AFREE_PC, ATRUN_RET; lia) G2) as (tr & UC & TR).
pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
destruct (harness_trace_inF _ _ _ _ HU2 HU3 TR) as [HIN LTR].
assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; clear - SPAB G4 LOS' BOT ATR; lia).
assert (URA : bv_unsigned (Z_to_bv 64 0x81248) = 0x81248) by (apply unsigned_lit; cl; lia).
eapply implMA_bind.
{ eapply (implMA_afree_call AI L R2); rewrite ?USPA, ?URA;
first [exact AH4 | exact (or_introl eq_refl) | exact MI4 | exact ST4 | exact BOT | exact TP | reflexivity | exact RSTK2
| exact (aps_ok_rest L q2 s REST2 AOK)
| (apply aunw_chain; rewrite ?USPA, ?URA; [clear - SPAB G2; lia| exact UC| exact LTR| exact HIN])
| unfold AFREE_STACK; clear - LOS' SPAB; lia | clear - SPAB; lia | unfold AFREE_PC; cl; lia
| clear - SPA32; Z.div_mod_to_equations; lia]. }
cbv beta. intros [] q3 R3 ms3 [REST3 PO3]. unfold afree_post in PO3.
destruct PO3 as (FLE3 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m5 & -> & MI5 & ST5 & HPR5 & AH5).
rewrite USPA in ST5, HPR5.
pose proof (AI_hb_ids AI _ _ _ _ _ AH4) as NDH4. unfold LB2 in HPR5, AH5, NDH4.
rewrite (lb_remove_headA pB B bsz (HB pP P PRODUCER_SIZE :: FB5 F :: LB) NDH4) in HPR5, AH5.
h_retlit.
assert (INF3 : In (FB5 F) (HB pP P PRODUCER_SIZE :: FB5 F :: LB)) by (right; left; reflexivity).
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR5 FRA4 ltac:(left; left; unfold FRA_E; xd; clear - SPAB G2 LY3; lia)) as FRA5.
pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR5 STG4 ltac:(clear - SPAB; lia) ltac:(clear - G2 LY3; lia)) as STG5.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR5 FRB4 ltac:(left; left; unfold FZRB13; xd; clear - SPAB G2 LY3; lia)) as FRB5.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR5 HDR4 ltac:(right; left; exists (FB5 F); split; [exact INF3| cbn; lia])) as HDR5.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR5 FLP4 ltac:(right; left; exists (FB5 F); split; [exact INF3| cbn; lia])) as FLP5.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR5 SH4
ltac:(right; right; right; right; exists 5, F, 2048; split; [exact INF3|]; rewrite FSH_size;
unfold SHF, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
clear - F2048 FH2; Z.div_mod_to_equations; lia)) as SH5.
assert (MG5 : magree bsegs (aclient_addr CI LB SP) m0 m5).
{ eapply magree_trans; [exact MG4|]. eapply magree_mono; [exact HPR5|]. intros a Ha.
eapply aca_monoA; [exact Ha| intros b Hb; right; right; exact Hb| clear - SPAB; lia]. }
assert (FLE03 : fp_le RNG0 R3) by (intros b j Hb; apply FLE3, FLE2, Hb).
eapply (asmD_E1 m5 q3 R3 pP jb jd); first [exact AH5| exact MG5| exact FLE03 | exact ST5 | exact FRA5 | exact STG5 | exact FRB5
| exact HDR5 | exact FLP5 | exact SH5 | exact MI5 | exact (rng_fp_le _ _ _ _ FLE3 RF) | exact (rng_fp_le _ _ _ _ FLE3 RSF)
| (rewrite REST3; exact REST2)].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Frame.
#[using="rng_fs MONO SF5 READ HLB PAY PLB D16 SZ BOT LOS SPG SP16 S0E FRM TP RAE HUL RSTK0 RI0 RISH0 RFS0 AOK"] Lemma fz_D_main : forall (pP : AsanCtrl.aptr) (s1' : APS) (RNG1 : footprint) (ms : machine_state),
fzB_state AI fflag L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms ->
implMA RNG1 (fz_restA pl (Some pP)) s1' POST ms.
Proof.
intros pP s1' RNG1 ms FZB.
destruct FZB as (P & F & SPA & tl & msv & nc & data & dsz & bsz & rem & buf' & jb & jc & jd & j0 & j1 & j2
& t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x25 & x27 & t3 & t4 & t5 & t6 & m
& ESPA & EA & -> & AH1 & REST1 & FLE1 & MG1 & P16 & PBLK & RP & RPS & PROD & UP
& F2048 & FH & FC & RF & RSF & WRF & HDR & FLP & DATAA & LB' & FBUF & NCA & MSVC & SH
& ST & FRA & STG & FRB & MI & PAYB & UD).
pose proof (AI_layout AI _ _ _ _ _ AH1) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof geomD as (G1 & G2 & G4). pose proof atop_range as ATR.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
Local Ltac2 Set LiaHints.tbl := fun () => "00U0?12419209398.6  14582370140.19914999122649.0  1952185540.2   23490941431.1  25993235953.5  26912666961.19927241613824.2  27506827262.5  27507234005.5  29757353573.0  29771365531.5  29771511728.6  29790884444.1953070773431.196 31706468795.19 35220631260.19336796291676.19237784379593.6  38123278910.3  38948636245.0  40345616860.19845194705697.0  45336307852.6  45336683431.6  45340432528.10 48717033957.21250943924840.4  51966051415.4  55648365497.3  58148693845.0  62708484519.9  64531730152.3  66151427842.16 68210343370.2  7443503053.191 9004980597.194 00000=00H00I00N00O00Z00h00m00n00o01001901:01E01P01_01j02502B02G02H02S02T02U02V02W02f02n03603703803N03T03k04004;04FS3LY32G24SPABS3LB'2G12Q4SS3PL2SS4SPAB4LOS'S3LB'2G12Q42HiS3DL2FFSS2G24SPABFS3LB'2G12Q4S3LB'2G12Q4S5F20481H2H02H4S3LB'2G12Q4S3LB'2G12Q4S3LY32G24SPABS3DL4SS3LB'2G12Q4SFFFS3LB'2G12Q43DL2S3LY32G2S2Q63Q11SSS3BOT2G43ATR4SPAB4LOS'S4SPABS5SPA321H2H02H43DR43PR4S3PL4S3LB'2G12Q4S3LB'2G12Q4".
pose proof (fseA_facts pl (zlen pl) AB ltac:(cl; lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (Q1 & Q2 & V & Q4 & _ & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
assert (BSZE : buff_size pl = bsz) by (unfold buff_size, fse_bsz, FseNCount.Zlength; rewrite EA; reflexivity).
assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; clear - SPAB G4 LOS' BOT ATR; lia).
assert (RSTK1 : rng RNG1 lo (al_top L - lo)) by exact (rng_fp_le _ _ _ _ FLE1 RSTK0).
assert (RI1 : rng_aimg RNG1) by exact (rng_fp_le _ _ _ _ FLE1 RI0).
pose proof HUL as (HU1 & HU2 & HU3 & HU4 & HU5).
unfold fz_restA. rewrite BSZE.
eapply implMA_bind.
{ eapply (fuzz_malloc_proofA AI L RNG1); rewrite ?USPA;
first [exact AH1 | exact MI | exact ST | exact BOT | exact TP | reflexivity | exact HU1 | exact RSTK1 | exact RI1
| exact (aps_ok_rest L s1' s REST1 AOK)
| unfold FUZZ_MALLOC_STACK_A, AMALLOC_STACK; clear - LOS' SPAB; lia | clear - SPAB G2; lia
| clear - SPA32; Z.div_mod_to_equations; lia | unfold AREQMAX; clear - Q6 Q11; lia]. }
cbv beta. intros r q2 R2 ms2 PO.
destruct PO as (FLE2 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & pB & B & jB
& -> & -> & MI2 & ST2 & HPR2 & REST2 & BRG & AH2 & BCELL & RB & RBS).
rewrite USPA in ST2, HPR2. h_retlit. cbv beta.
set (LB1 := HB pP P PRODUCER_SIZE :: FB5 F :: LB) in *.
assert (INF1 : In (FB5 F) LB1) by (right; left; reflexivity).
assert (INP1 : In (HB pP P PRODUCER_SIZE) LB1) by (left; reflexivity).
Local Ltac xd1 := cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length FZRB13].
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA ltac:(left; left; xd1; clear - SPAB G2 LY3; lia)) as FRA2.
pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG ltac:(clear - SPAB; lia) ltac:(clear - G2 LY3; lia)) as STG2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB ltac:(left; left; xd1; clear - SPAB G2 LY3; lia)) as FRB2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 HDR ltac:(right; left; exists (FB5 F); split; [exact INF1| cbn; lia])) as HDR2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FLP ltac:(right; left; exists (FB5 F); split; [exact INF1| cbn; lia])) as FLP2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 MSVC ltac:(right; left; exists (FB5 F); split; [exact INF1| cbn; lia])) as MSVC2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 PROD ltac:(right; left; exists (HB pP P PRODUCER_SIZE); split; [exact INP1| cbn; unfold PRODUCER_SIZE; lia])) as PROD2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 SH
ltac:(right; right; right; right; exists 5, F, 2048; split; [exact INF1|]; rewrite FSH_size;
unfold SHF, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
clear - F2048 FH; apply ablk_lin in FH; Z.div_mod_to_equations; lia)) as SH2.
pose proof (aheap_pres_wr_at _ _ _ _ _ _ _ HPR2 WRF ltac:(right; left; exists (FB5 F); split; [exact INF1| cbn; lia])) as WRF2.
assert (DATAA2 : u8arr bsegs m2 (F + 32) (map (Z_to_bv 8) buf')).
{ destruct DATAA as [DB DW]. split.
- eapply aheap_pres_bytes_at; [exact HPR2| exact DB|]. rewrite length_map, LB'. right; left. exists (FB5 F). split; [exact INF1| cbn; lia].
- eapply aheap_pres_wr_at; [exact HPR2| exact DW|]. rewrite length_map, LB'. right; left. exists (FB5 F). split; [exact INF1| cbn; lia]. }
assert (NCA2 : u8arr bsegs m2 (F + 608) (u16s (map (Z_to_bv 64) nc))).
{ destruct NCA as [NB NW]. split.
- eapply aheap_pres_bytes_at; [exact HPR2| exact NB|]. rewrite u16s_length, length_map, Q4. right; left. exists (FB5 F). split; [exact INF1| cbn; lia].
- eapply aheap_pres_wr_at; [exact HPR2| exact NW|]. rewrite u16s_length, length_map, Q4. right; left. exists (FB5 F). split; [exact INF1| cbn; lia]. }
assert (PAY2 : bytes_at bsegs m2 D (map (Z_to_bv 8) pl) /\ unpoisoned m2 D (D + zlen pl)).
{ destruct PAY as [(pD & HinD & NZ)|(-> & ->)].
- unfold zlength in HinD, NZ.
assert (IN2 : In (HB pD D (zlen pl)) (HB pB B bsz :: LB1)) by (right; right; right; exact HinD).
destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 IN2) as (_ & (DR1 & DR2 & DR3 & DR4) & _ & _ & SHD & _).
pose proof (ablk_lin _ _ DR1) as (DL1 & DL2 & DL3 & DL4).
split.
+ eapply aheap_pres_bytes_at; [exact HPR2| exact PAYB|]. rewrite length_map. right; left. exists (HB pD D (zlen pl)).
split; [right; right; exact HinD| cbn; lia].
+ apply ablock_unpoisonedR; [exact SHD| clear - DR4; Z.div_mod_to_equations; lia| clear - DL2; lia| cl; lia| clear - DL4; lia].
- unfold AEMPTY. split.
+ unfold bytes_at. cbn [map length Z.of_nat]. split; [cl; lia|]. split; [cl; lia|]. intros i Hi. lia.
+ cbn [length Z.of_nat]. apply unpoisoned_nil. cl; lia. }
destruct PAY2 as [PAYB2 UD2].
assert (UP2 : unpoisoned m2 P (P + 16)).
{ destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_intror INP1)) as (_ & (PR1 & PR2 & PR3 & PR4) & _ & _ & SHP & _).
pose proof (ablk_lin _ _ PR1) as (PL1 & PL2 & PL3 & PL4).
replace (P + 16) with (P + PRODUCER_SIZE) by reflexivity.
apply ablock_unpoisonedR; [exact SHP| clear - PR4; Z.div_mod_to_equations; lia| clear - PL2; lia| unfold PRODUCER_SIZE; cl; lia| clear - PL4; lia]. }
assert (MG2 : magree bsegs (aclient_addr CI LB SP) m0 m2).
{ eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha.
eapply aca_monoA; [exact Ha| intros b Hb; right; right; exact Hb| clear - SPAB; lia]. }
assert (FLE02 : fp_le RNG0 R2) by (intros b0 j Hb; apply FLE2, FLE1, Hb).
eapply (asmD_D F P SPA tl msv dsz j0 j1 j2 ESPA F2048 FH FC m2 q2 R2 pP pB B jB bsz rem nc data buf' jb jc jd);
first [exact EA | exact AH2 | exact MG2 | (rewrite REST2; exact REST1) | exact FLE02 | exact BRG | exact BCELL | exact RB | exact RBS
| exact PBLK | exact P16 | exact (rng_fp_le _ _ _ _ FLE2 RP) | exact (rng_fp_le _ _ _ _ FLE2 RPS) | exact PROD2 | exact UP2
| exact (rng_fp_le _ _ _ _ FLE2 RF) | exact (rng_fp_le _ _ _ _ FLE2 RSF) | exact WRF2 | exact HDR2 | exact FLP2 | exact DATAA2
| exact LB' | exact FBUF | exact NCA2 | exact MSVC2 | exact SH2 | exact ST2 | exact FRA2 | exact STG2 | exact FRB2 | exact MI2
| exact PAYB2 | exact UD2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End AsmD.
#[using="Type"] Theorem fz_D_proof : forall (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop),
fzD_stmt AI fflag rng_fs.
Proof.
intros AI fflag rng_fs. unfold fzD_stmt.
intros MONO SF5 READ L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms
HLB PAY PLB D16 SZ BOT LOS SPG SP16 S0E FRM TP RAE HUL RSTK0 RI0 RISH0 RFS0 AOK FZB.
eapply fz_D_main; eassumption.
Qed.
End CANSEC1.
