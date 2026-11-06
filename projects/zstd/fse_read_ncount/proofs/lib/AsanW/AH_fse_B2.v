(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells ABytes AF_fse_iface AHarness_iface AKit FsKit AH_fse_kit AH_fse_pure AH_fse_calls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_h_model.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
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

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Ltac callt tac := lazymatch goal with
| |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ tac | post_call segs m ];
try (lazymatch goal with |- rng _ _ _ => solve_rng end)
end.
Ltac callpt tac := eapply evtF_cut; [ tac | call_pure_postF ].
Ltac rt_now RTWB := match goal with
| RT : fse_rt ?mr, MU : munch _ ?mr ?mc, WM : wmono _ ?mr ?mc |- _ =>
let H := fresh "RTN" in pose proof (RTWB _ _ RT MU WM) as H; unfold fse_rt in H;
destruct H as (? & ? & ? & ? & ? & ? & ?); assumption
end.
Section CANSEC1. Context {rc : runConstT}.
Section B2.
Hypothesis U32R : prod_u32r_stmtA.
Hypothesis WBOUND : fse_wbound_stmtA.
Hypothesis WRITE : fse_write_stmtA.
Hypothesis ISERR : fse_iserror_stmtA.
Variables (gp tp sp : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (SPA lo F P D : Z) (pl : list Z) (RNG : footprint).
Notation SP := (bv_unsigned sp).
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis SPT : SP + 16 <= 2^47.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis ESPA : SPA = (SP - 192) - (SP - 192) mod 32.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RI : rng_aimg RNG.
Hypothesis FH : ablk F (F + 2048).
Hypothesis FC : F + 2048 <= ATOP.
Hypothesis F2048 : F mod 2048 = 0.
Hypothesis RF : rng RNG F 2048.
Hypothesis RSF : rng RNG (shad F) 256.
Hypothesis BLKP : ablk P (P + 16).
Hypothesis P16 : P mod 16 = 0.
Hypothesis RP : rng RNG P 16.
Hypothesis RPS : rng RNG (shad P) 2.
Hypothesis PF : P + 16 <= F \/ F + 2048 <= P.
Hypothesis DLOC : (pl = [] /\ D = AEMPTY) \/ ablk D (D + zlen pl).
Hypothesis D8 : D mod 8 = 0.
Hypothesis RD : rng RNG D (zlen pl).
Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis DF : D + zlen pl <= F \/ F + 2048 <= D.
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis SZ26 : zlen pl < 2^26.
Definition W_B : list (Z * Z) := [(P + 8, P + 16); (SPA - 2224, SPA + 88); (F + 32, F + 1780); (SHF F, SHF F + 256)].
Definition phaseB_postA (mr : amem) : machine_state -> Prop :=
fun ms' => exists tl msv nc data dsz bsz rem buf' (jd : list byte)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word) (m' : amem),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem)
/\ ms' = MS (mkR (Z_to_bv 64 0x811a4) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 bsz) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 1760)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dsz) (Z_to_bv 64 (F + 608)) (Z_to_bv 64 (F + 32))
(Z_to_bv 64 bsz) (Z_to_bv 64 P) (Z_to_bv 64 msv) s10 (Z_to_bv 64 (SHF F)) t3 t4 t5 t6)
FR (Z_to_bv 64 0x827d8) fc None m' (seg_rom asegs)
/\ munch W_B mr m' /\ wmono asegs mr m' /\ mem_inv asegs m'
/\ stk asegs m' lo SPA
/\ prod_atA m' P D rem
/\ bytes_at asegs m' D (map (Z_to_bv 8) pl)
/\ rw_cells asegs m' SPA [C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148));
C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); CB 24 jd; C8 (Z_to_bv 64 F)]
/\ u8arr asegs m' (F + 608) (u16s (map (Z_to_bv 64) nc))
/\ u8arr asegs m' (F + 32) (map (Z_to_bv 8) buf') /\ length buf' = 512%nat /\ firstn (Z.to_nat dsz) buf' = data
/\ rw_cells asegs m' (F + 1760) [C4 (Z_to_bv 64 255)]
/\ rw_cells asegs m' (SHF F) (FSH Z64 Z64 Z64 B04 B04).
Section WB.
Let geom : SPA + 88 <= SP - 104 /\ SP - 208 <= SPA /\ lo + 16384 <= SP /\ 0 <= SP < 2^64.
Proof.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold AHARNESS_STACK in LOS. lia.
Qed.
#[using="rc sp lo D pl LOS LOC SPT SP16 ESPA FH BLKP geom"] Lemma WB_above : above AIMG_HI W_B.
Proof.
pose proof (ablk_lin _ _ FH) as (FH1 & _). pose proof (ablk_lin _ _ BLKP) as (PL1 & _). pose proof geom.
unfold W_B, SHF, AIMG_HI in *. cbn [above]. Local Ltac2 Set LiaHints.tbl := fun () => "0050>1272948352.47 28144053094.4728576693309.4729784466142.4755877092263.4700000>00U00Z00[00`S4geom3FH13PL1S3LOC4geom3FH13PL11H2H0S3PL1SS3FH1".
rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8.
repeat split; try lia; Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc sp lo D pl LOS LOC SPT SP16 ESPA FH BLKP geom"] Lemma rt_WB : forall mr mc, fse_rt mr -> munch W_B mr mc -> wmono asegs mr mc -> fse_rt mc.
Proof. intros mr mc R M W. eapply fse_rt_munch; [exact R| exact M| exact W| exact WB_above]. Qed.
#[using="rc sp lo D pl LOS LOC SPT SP16 ESPA FH F2048 BLKP P16 PF geom"] Lemma unp_P_WB : forall mr mc, unpoisoned mr P (P + 16) -> munch W_B mr mc -> unpoisoned mc P (P + 16).
Proof.
intros mr mc U MU. pose proof geom as G. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4).
pose proof (ablk_disj_band _ _ BLKP) as DBP. pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS, AIMG_HI in *. unfold AHARNESS_STACK in LOS.
eapply unpoisoned_munch; [exact U| exact MU|]. unfold W_B, SHF. Local Ltac2 Set LiaHints.tbl := fun () => "0050>29782367974.5932815121182.1743699756742.2261632444545.2566135216254.4000000900I00e01901aS3FH23PL2S3DBP1H2H02H42H5S3PL13PL43DBP3DBF1H2H02H42H5S3LOC1G3PL32H42H52H9S5F20483P162PF1H2H02H42H52H93H103H143H19".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. cbn [disjoint_from]. change (2^3) with 8.
split; [clear - DBP PL1; Z.div_mod_to_equations; lia|]. split; [clear - DBP G LOS LOC PL3; Z.div_mod_to_equations; lia|].
split; [clear - DBP DBF PL1 PL4 FH1 FH4; Z.div_mod_to_equations; lia|]. split; [clear - PF P16 F2048; Z.div_mod_to_equations; lia| exact I].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc sp lo RNG LOS LOC SPT SP16 ESPA FH FC F2048 BLKP PF DLOC D8 RD RDS DP DF PLB SZ26 geom"] Lemma unp_D_WB : forall mr mc, unpoisoned mr D (D + zlen pl) -> munch W_B mr mc -> unpoisoned mc D (D + zlen pl).
Proof.
intros mr mc U MU. Local Ltac2 Set LiaHints.tbl := fun () => "0070>29782367974.6632815121182.2342819610273.4843699756742.2361632444545.2666135216371.358555112874.50 00000=00Y00]01901M02002KS3FH23PL23DL2S3DL13DL43DBP3DBD1H2H02H42H5S2N0S3DL13DL43DBF3DBD1H2H02H42H5S3LOC1G3DL32H42H52H9S5F20482D82DF2N01H2H42H52H93H103H14S3LOC2FC2PF4geom2U12U22E01H".
destruct (Z.eq_dec (zlen pl) 0) as [E0|N0]; [rewrite E0, Z.add_0_r; apply unpoisoned_nil; destruct U as (U1 & U2 & _); lia|].
destruct DLOC as [[E _]|BLKD]; [subst pl; cbn in N0; lia|].
pose proof geom as G. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4).
pose proof (ablk_lin _ _ BLKD) as (DL1 & DL2 & DL3 & DL4).
pose proof (ablk_disj_band _ _ BLKP) as DBP. pose proof (ablk_disj_band _ _ FH) as DBF. pose proof (ablk_disj_band _ _ BLKD) as DBD.
unfold KLS, AIMG_HI in *. unfold AHARNESS_STACK in LOS.
eapply unpoisoned_munch; [exact U| exact MU|]. unfold W_B, SHF. rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. cbn [disjoint_from]. change (2^3) with 8.
split; [clear - DBD DBP PL1 PL4 DL1 DL4; Z.div_mod_to_equations; lia|]. split; [clear - DBD G LOS LOC DL3; Z.div_mod_to_equations; lia|].
split; [clear - DBD DBF DL1 DL4 FH1 FH4; Z.div_mod_to_equations; lia|]. split; [clear - DF D8 F2048 N0; Z.div_mod_to_equations; lia| exact I].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc sp lo RNG LOS LOC SPT SP16 ESPA FH F2048 BLKP PF DLOC D8 RD RDS DP DF PLB SZ26 geom"] Lemma pay_WB : forall mr mc, bytes_at asegs mr D (map (Z_to_bv 8) pl) -> munch W_B mr mc -> bytes_at asegs mc D (map (Z_to_bv 8) pl).
Proof.
intros mr mc B MU. eapply bytes_at_transport; [exact B| exact MU|]. rewrite length_map.
pose proof geom as G. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4).
assert (DT : D + zlen pl <= ATOP /\ 0 <= D).
{ Local Ltac2 Set LiaHints.tbl := fun () => "00:0?21180882330.10125155314953.55 25328592274.98 29782367974.56 29782367974.59 33013726929.59 40295300192.59 4072646780.59  55904264338.59 58467359828.59 00000]00h01@01I01R01]02A02M02Z02fS2FH5F20482PF2DP2DF3FH33PL34BLKD1H2H03H143H29S3FH23PL21HS5F20483FH23PL21H2H03H14S3FH23PL2S3FH23PL2S3FH23PL21HS3LOC2PF4geom1G3FH23FH33PL23PL32DT1HS2DP3FH23PL2S3FH23PL23DSHS2DF3FH23PL2".
destruct DLOC as [[-> ->]|BLKD]; [unfold AEMPTY; cbn; lia| pose proof (ablk_lin _ _ BLKD); unfold AIMG_HI in *; lia]. }
assert (DSH : D + zlen pl <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= D).
{ destruct DLOC as [[-> ->]|BLKD]; [unfold AEMPTY; cbn; rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia|].
unfold ablk, AIMG_HI, KLS in BLKD, FH. rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. Z.div_mod_to_equations. lia. }
unfold W_B, SHF, AIMG_HI in *. unfold AHARNESS_STACK in LOS. cbn [disjoint_from].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WB.
#[using="rc U32R WBOUND WRITE ISERR LOS LOC SPT SP16 ESPA RSTK RI FH FC F2048 RF RSF BLKP P16 RP RPS PF DLOC D8 RD RDS DP DF PLB SZ26"] Lemma pB3 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2v s4v s6v s10v x28 x29 x30 x31 : word) (mr m : amem)
(tl msv r4 bsz r5 : Z) (nc : list Z) (j8 j24 jdata jmsv : list byte),
uint32Range pl r4 (hdrSize nc msv tl) 512 = (bsz, r5) ->
fseA pl (zlen pl) = (tl, msv, nc, fse_data nc msv tl, hdrSize nc msv tl, bsz, r5) ->
0 <= r4 <= zlen pl ->
u8arr asegs m (F + 608) (u16s (map (Z_to_bv 64) nc)) ->
rw_cells asegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 r4)] ->
rw_cells asegs m SPA [C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148));
CB 8 j8; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); CB 24 j24; C8 (Z_to_bv 64 F)] ->
rw_cells asegs m (F + 32) [CB 512 jdata] ->
rw_cells asegs m (F + 1760) [CB 4 jmsv] ->
rw_cells asegs m (SHF F) (FSH Z64 Z64 F8S BF8 BF8) ->
stk asegs m lo SPA -> mem_inv asegs m ->
fse_rt mr -> bytes_at asegs mr D (map (Z_to_bv 8) pl) -> unpoisoned mr P (P + 16) -> unpoisoned mr D (D + zlen pl) ->
munch W_B mr m -> wmono asegs mr m ->
evtF asegs RNG (phaseB_postA mr)
(MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
s2v (Z_to_bv 64 2147450880) s4v (Z_to_bv 64 (F + 608)) s6v (Z_to_bv 64 tl) (Z_to_bv 64 P) (Z_to_bv 64 msv)
s10v (Z_to_bv 64 (SHF F)) x28 x29 x30 x31)
FR (Z_to_bv 64 0x8111c) fc None m (seg_rom asegs)).
Proof.
intros until jmsv. intros EB EA R4 NCA PR FRA DATAC MSVC SH ST MI RT PAY0 UNP0 UND0 MU WM.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
Local Ltac2 Set LiaHints.tbl := fun () => "01o0?11162769258.1261336903991.164 1370123474.186 13850550541.20214588363872.14516606911310.17817836644758.19118021301317.18618168056401.1871948122878.178 19588257050.14619948704282.16219962924074.18520607886280.146206360778.146  22239675741.17622613889322.14623028554134.17723298330693.10723452717618.17623492641683.11523492641683.13224384752563.14625223861242.12625349552462.10625848168853.2302597469152.202 26166611579.12827340939573.23027355377050.14628381206279.15628555306882.12729536659395.19229782367974.10629782367974.10729782367974.18830674972759.14430674972759.14531527715857.14433719989128.10033719989128.10133847513439.16334527391847.16435495549846.16435968369417.17836149813952.10 36151909501.17837450429268.14637646139802.14638794494980.16139665081360.17239679368394.14639867114339.14639999590352.10039999590352.10139999590352.14439999590352.14540335050848.14541624233714.18642146777215.14642146777215.17843500747729.14443527720977.14543879067011.14644021460374.14444373816778.1764462652304.186 45114998679.16445179768224.1274573555649.146 46415344733.23047792948487.14648083926839.10 48090202506.14648653510305.10850692615968.11150753098807.10 50759395978.14650814299972.16251350355627.18751357505765.14651357505765.17851409014211.10 51411121022.17852106616342.16052544056194.17852739448746.1465377903808.178 55038163706.11055259630626.20355904264338.11356041590156.15556170415909.14556170444361.17756296082090.12657197585530.17758731071363.10 58733181246.17859314873579.12959314873579.16360502248570.17860592901373.17860912249238.14560942366563.14661035741573.11461664466437.14662644608289.2306267520963.176 6267520963.178 62697932550.14662697932550.17862841936062.12 62844036611.17862905321347.14662926649111.14663202992012.16464284474433.23066149329409.18666149329409.18766151427842.16 66560187536.13866775607233.14667294985855.1146854930828.164 755822847.202  85789009.145   8803805885.230 00000?00@00j00k01_02L03603`04J05805n06[07H07I07J08708808b08m09W09`0:70;60;B0;K0;L0<60<I0<J0=Q0=d0>30?O0?X0?a0@K0@L0@M0AC0AP0A]0BG0BH0C20DO0DP0DQ0EG0FN0G80Gb0Gc0HL0HY0Hf0IO0J80Ja0KK0LA0MA0Mf0N\0N]0OB0Oo0PY0QG0QV0R;0R<0Re0Rf0Rg0S30Sd0Se0Sf0TS0U=0U>0U?0U@0UA0Uf0W60W^0Xl0Y90ZS0[U0\B0\l0][0]j0^T0^U0^V0^g0_S0`=0a=0ab0bK0b]0cW0cX0dE0e20f70gF0gG0gH0h10hZ0iD0iE0j50je0k40k@0ke0lD0m20nH0nm0nnS3FH23PL22F22F4FS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFFS3LOS3LOC3FH23PL23RSP2D02F42DB3LJD3LD03WN24LMNC4LNC2S3FH23PL22F42F62DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL13PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3LOS3LOC3FH23PL23RSP2D02F42DB3LJD3LD03WN24LMNC4LNC21HS3FH23PL22F42F62DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42F62DB3LJD3LD03WN24LMNC4LNC24LBUFFFS3FH23PL22F42F62DB3LJD3LD03WN24LMNC4LNC24LBUFFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL21HS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL2S3FH23PL22F42DB3LJD3LD0S3LOS3LOC3FH23PL23RSP4SPAB2D02F42DB3LJD3LD03WN24LMNC3FWS4LNC21HS3FH23PL22F4S3FH23PL2FS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42F73WB0FS3LOS3LOC3FH23FH33PL23PL33RSP4SPAB2D02F42DB3LJD3LD03WN24LMNC3FWS4LNC21HS2FH5F20481H2H03H19S3FH23PL22F12F4S3LOS3LOC2PF2DP2DF3FH23PL23RSP4SPAB2D02F42F63F113F122DB3LJD3LD03WN24LMNC4LNC24LBUF3S5a3S5b1HS3FH23PL2S3FH23PL2S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFFFS3LOS3LOC3FH23PL23RSP2D02F42DB3LJD3LD03WN24LMNC4LNC21HS3FH23FH43PL2S3FH23FH43PL2S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3LOS3LOC4SP163P162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D04LENP2F42DB3LJD3LD03WN24LMNC4LNC24LBUF1HFFS3LOS3LOC3FH23PL23RSP2D02F42DB3LJD3LD03WN24LMNC4LNC21HS3LOS3LOC3FH23FH33PL23PL33RSP4SPAB2D02F42DB3LJD3LD03WN24LMNC3FWS4LNC21HS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFFS3FH13FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S3FH13FH23PL2S3FH13FH23PL2S3FH13FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S3FH13FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC23ZD0S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3LOS3LOC3FH23PL23RSP2D02F42DB3LJD3LD03WN24LMNC4LNC21HS3LOS3LOC3FH23PL23RSP4SPAB2D02F42DB3LJD3LD03WN24LMNC4LNC24LBUF1HS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S3LOS3LOC3FH23PL23RSP2D02F42DB3LJD3LD03WN24LMNC4LNC21HFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S2R43FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL23BSF2F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F22F4S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2FS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC23ZD0FFS3FH23PL22H0S3LOS3LOC4BLKP2PF2DP2DF3FH23PL23RSP4SPAB3BSF2D01HFFS3FH23PL22F42F62DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFFFFFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S3LOS3LOC3FH23FH33PL23PL33RSP4SPAB2D02F43F122DB3LJD3LD03WN24LMNC4LNC24LBUF3S5b1HS3FH23PL22F12F42DB3LJD3LD03WN24LMNC4LNC2S3LOS3LOC2PF3FH23FH33PL23PL33RSP4SPAB2D02DT2F42DB3LJD3LD03WN24LMNC4LNC24LBUF1HS3FH23PL23BSFS3LOS3LOC2PF2DP2DF3FH23PL23RSP4SPAB2D02F42F63F113F122DB3LJD3LD03WN24LMNC4LNC24LBUF3S5a3S5bS3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA323BSF4SHDJ2D03PSH1B1HS5F20482PF2DP2DF3FH13FH33PL13PL31H2H03H193H34S3FH23PL24SPAB2F42DB3LJD3LD03WN24LMNC4LNC2S3FH23PL24SPAB2F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F12F4S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFFFS3FH23PL22F42F71KS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUF1KS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3LOS3LOC3FH23PL23RSP4SPAB2D02F42DB3LJD3LD03WN24LMNC4LNC24LBUF1HS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S3FH13FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S3FH23PL22B12B22B3S3LOS3LOC3FH23PL23RSP2D02F42DB3LJD3LD03WN24LMNC4LNC23ZD01HFS3FH23PL22F42F62DB3LJD3LD03WN24LMNC4LNC24LBUFS3FH23PL22F42F62DB3LJD3LD03WN24LMNC4LNC24LBUFS3LOS3LOC3SPT3FH23PL23RSP4SPAB5SPA882D02F42DB3LJD3LD03WN24LMNC4LNC21HS3LOS3LOC3SPT4ESPA3FH23PL23RSP4SPAB5SPA882D02F42DB3LJD3LD03WN24LMNC4LNC24LBUF1HFFS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC23ZD0S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC23ZD0S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC24LBUFFS5F20482PF2DP2DF2F43F122DB3LJD3LD03WN24LMNC4LNC2S5F20482PF2DP2DF2F43F122DB3LJD3LD03WN24LMNC4LNC2S5F20481H2H02H4S3FH23PL22F4S3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2S3LOS3LOC3FH23PL23RSP4SPAB2D01HS3FH23PL23BSF2F42DB3LJD3LD03WN24LMNC4LNC24LBUFS3LOS3LOC2PF2DP2DF3FH23PL23RSP4SPAB2D02F42F63F122DB3LJD3LD03WN24LMNC4LNC24LBUF3S5a3S5bS3FH23PL22F42DB3LJD3LD03WN24LMNC4LNC2F".
pose proof (fsh_unp_data m F F2048 ltac:(lia) ltac:(unfold KEND; lia) _ _ _ _ SH) as UDA.
pose proof (fsh_unp_nc m F F2048 ltac:(lia) ltac:(unfold KEND; lia) _ _ _ _ SH) as UNA.
unfold W_B in *. unfold SHF, FSH, AHARNESS_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND, KHIGH in *.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
replace (shad F) with (Z.shiftr F 3 + ASHOFF) in RSF by (unfold shad; lia).
assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 256 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
assert (SHDJ : F + 2048 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= F).
{ rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. unfold ablk, AIMG_HI, KLS in FH. Z.div_mod_to_equations. lia. }
assert (BLKD : 0 < zlen pl -> ablk D (D + zlen pl)).
{ intros H0. destruct DLOC as [[-> _]|B]; [cbn in H0; lia| exact B]. }
assert (D0 : 0 < D /\ D + zlen pl <= ATOP).
{ destruct DLOC as [[-> ->]|B]; [unfold AEMPTY; cbn; lia| pose proof (ablk_lin _ _ B) as (B1 & B2 & B3 & B4); unfold AIMG_HI in B1; lia]. }
destruct D0 as [D0 DT].
assert (PSH : P + 16 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= P).
{ unfold ablk, AIMG_HI, KLS in BLKP. lia. }
assert (DSH : D + zlen pl <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= D).
{ destruct DLOC as [[-> ->]|B]; [unfold AEMPTY; cbn; lia| unfold ablk, AIMG_HI, KLS in B; lia]. }
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (RFRA : rng RNG SPA 88) by (eapply rng_sub'; [exact RSTK| lia]).
clear DSH. change (sf_hide (D + zlen pl <= P \/ P + 16 <= D)) in DP. change (sf_hide (D + zlen pl <= F \/ F + 2048 <= D)) in DF.
change (sf_hide ((pl = [] /\ D = AEMPTY) \/ ablk D (D + zlen pl))) in DLOC. change (sf_hide (0 < zlen pl -> ablk D (D + zlen pl))) in BLKD.
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & _ & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
set (dsz := hdrSize nc msv tl) in *.
repeat match goal with H : ?T |- _ => lazymatch T with sf_hide _ => fail | context [Z.modulo _ _] => change T with (sf_hide T) in H | context [Z.div _ _] => change T with (sf_hide T) in H end end.
zstep. zstep. zstep.
unfold fse_wbound_stmtA, AFSE_WBOUND in WBOUND.
callpt ltac:(eapply WBOUND with (msv := msv) (tl := tl)); [lia| lia| reflexivity| reflexivity|].
pose proof (write_bound_nonneg msv tl ltac:(lia) ltac:(lia)) as WB0.
zstep. zstep.
if_cases K; zify_cond K; [exfalso; lia|]. clear K.
do 8 zstep.
pose proof (rw_cells_bound _ _ _ _ DATAC) as DB. cbn [cells_size csize Nat.add] in DB.
assert (LJD : length jdata = 512%nat) by (destruct DATAC as [[[Hn _] _] _]; exact Hn).
apply u8arr_of_rw_cells in DATAC. rewrite <- (bytes_of_unsigned jdata) in DATAC.
set (data0 := map bv_unsigned jdata) in *.
assert (LD0 : length data0 = 512%nat) by (subst data0; rewrite length_map; exact LJD).
pose proof (fseA_write_ncount pl (zlen pl) data0 AB ltac:(lia) LD0) as WN. rewrite EA in WN.
destruct WN as (buf' & WN1 & WN2 & WN3 & WN4 & WN5). fold dsz in WN1, WN3, WN4, WN5.
pose proof (valid_ncount_short _ _ _ V) as NCS.
assert (LMNC : length (map (Z_to_bv 64) nc) = 256%nat) by (rewrite length_map; exact F4).
assert (FWS : FSE_WRITE_STACK_A = 96) by reflexivity.
assert (LNC2 : length (u16s (map (Z_to_bv 64) nc)) = 512%nat) by (rewrite u16s_length, LMNC; reflexivity).
assert (ZD0 : zlen data0 = 512) by (rewrite LD0; reflexivity).
assert (ZNC : zlen nc = 256) by (rewrite F4; reflexivity).
assert (RSD : rng RNG (shad (F + 32)) (nshad (zlen data0))).
{ rewrite ZD0, shad_frame_off by (first [lia | unfold KEND; lia | unfold sf_hide in *; Z.div_mod_to_equations; lia]). unfold SHF. change (32 / 8) with 4. change (nshad 512) with 64.
eapply rng_sub'; [exact RSF| lia]. }
assert (RSN : rng RNG (shad (F + 608)) (nshad (2 * zlen nc))).
{ rewrite ZNC, shad_frame_off by (first [lia | unfold KEND; lia | unfold sf_hide in *; Z.div_mod_to_equations; lia]). unfold SHF. change (608 / 8) with 76. change (nshad (2 * 256)) with 64.
eapply rng_sub'; [exact RSF| lia]. }
replace (F + 544) with (F + 32 + zlen data0) in UDA by lia.
replace (F + 1120) with (F + 608 + 2 * zlen nc) in UNA by lia.
unfold fse_write_stmtA, AFSE_WRITE in WRITE.
callt ltac:(eapply WRITE with (SPV := SPA) (BUF := F + 32) (NC := F + 608) (buf0 := data0) (buf' := buf') (nc := nc) (msv := msv) (tl := tl) (n := dsz) (lo := lo));
[ first [ exact (proj1 NCA) | assumption | subst data0; apply bytes_unsigned_range | reflexivity | (rewrite ZD0; reflexivity) | lia | (unfold KHIGH; lia)
| (eapply ablk_sub; [exact FH| lia| lia]) | (clear - F2048; unfold sf_hide in *; Z.div_mod_to_equations; lia) | rt_now rt_WB ] .. | ].
rename POST into DATAA. rename PC into ST. rename MI0 into MI.
assert (LBUF : length (map (Z_to_bv 8) buf') = 512%nat) by (rewrite length_map; exact WN2).
zstep. zstep.
unfold fse_iserror_stmtA, AFSE_ISERROR in ISERR.
callpt ltac:(eapply ISERR with (c := dsz)); [lia| reflexivity|].
replace (2^64 - 119 <=? dsz) with false by (symmetry; apply Z.leb_gt; lia). cbn [Z.b2z].
zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
zstep. zstep. zstep. zstep.
lazymatch goal with SH : rw_cells asegs _ (Z.shiftr F 3 + ASHOFF) _ |- _ => rw_split SH 22%nat SHa SHr end.
rw_split SHr 1%nat SHb SHc.
call (ss_00_z RNG); [ first [ exact SHb | eassumption | lia | rt_now rt_WB ] .. | ].
change (Z.to_nat 64) with 64%nat in POST. rw_join SHa POST SH1. rw_join SH1 SHc SH. cbn [app] in SH.
do 6 zstep.
zstep. rewrite FseWalkKit.swrap32_small by lia.
zstep. zstep. zstep.
pose proof (uint32Range_spec pl r4 dsz 512 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S5.
rewrite EB in S5. destruct S5 as (S5a & S5b & _).
unfold prod_u32r_stmtA, APROD_U32R in U32R.
callt ltac:(eapply U32R with (SPV := SPA) (P := P) (D := D) (pl := pl) (size := r4) (mn := dsz) (mx := 512) (lo := lo));
[ first [ reflexivity | assumption | (split; [eapply pay_WB; eassumption| exact PLB]) | lia | (unfold KHIGH; lia) | (clear - P16; unfold sf_hide in *; Z.div_mod_to_equations; lia)
| (eapply unp_P_WB; eassumption) | (eapply unp_D_WB; eassumption) | rt_now rt_WB
| (unfold sf_hide in DP, DF, DLOC, BLKD; first [ exact DP | exact BLKD | lia ]) ] .. | ].
rewrite EB in *. cbn [fst snd] in *.
rename POST into PR. rename PC into ST. try rename MI0 into MI1.
zstep. zstep. rewrite land_ones32A by lia. zstep. zstep.
apply evtF_done. unfold phaseB_postA. unfold W_B. unfold SHF, FSH.
exists tl, msv, nc, (fse_data nc msv tl), dsz, bsz, r5, buf', j24.
do 16 eexists.
split; [exact EA|]. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact PR|].
split; [eapply pay_WB; eassumption|]. split; [exact FRA|]. split; [exact NCA|]. split; [exact DATAA|]. split; [exact WN2|]. split; [exact WN3|].
split; [exact MSVC| exact SH].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End B2.
End CANSEC1.
