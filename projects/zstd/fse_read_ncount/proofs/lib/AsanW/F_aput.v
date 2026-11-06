(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 AKitQ.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition putA_post (sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
(t hm n lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
(Z_to_bv 64 0x9f0f0) (Z_to_bv 64 (t + 80))
(Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (rup n 8)) (Z_to_bv 64 253) (Z_to_bv 64 0) a4 a5 a6 a7
(Z_to_bv 64 n) a3 a2 (Z_to_bv 64 hm) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36724) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -80)
/\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
#[using="Type"] Lemma putA_spec : forall (t hm n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo stb b1 ctx : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 80 ->
mem_inv asegs m ->
a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
rw_cells asegs m 0x99778 [C8 (Z_to_bv 64 AFLAGS)] ->
rw_cells asegs m 0x9fca4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
rw_cells asegs m hm [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
0 <= n <= Q_MAX -> AIMG_HI <= hm -> hm + 16 <= ATOP ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG hm 16 ->
evtF asegs RNG (putA_post sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 F fc t hm n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3659c) fc None m (seg_rom asegs)).
Proof.
intros until ctx. intros ST CEIL LO MI -> -> -> -> QK GF FL HD N H0 H1 RIMG RSTK RH.
unfold AIMG_HI, AQUAR_Q, AQ_MAX, AFLAGS, Q_MAX, Q_MIN, Q_CACHE in *.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "01\0>11472836995.6711601497306.681162083374.67 11805467289.6511805467289.6611805467289.6711805467289.6813629548202.6114598424174.6715702970684.6817212185306.6817449403630.6717776320431.6618261894510.6618321827310.6520758753646.6820937541742.672130161072.67 21713897404.6621840295918.6822163107130.6522226183811.6723064840430.6823589365338.6624630998586.6825420113390.6625878270255.6627723960707.6630008181843.6130196181434.673051486595.67 31407249106.6732651489978.6733146554862.6833680001082.6734131883738.6534457081818.6834737286766.6735909988007.6635916187738.6736115622446.6736560264302.673662364220.68 36646331050.6137436222938.6739411241710.6739713958766.6739771606844.6540091925679.6640374333670.5842200251523.6842589983314.6742720579438.6842831019478.6743061431595.5643656575204.7143802119662.6843987951406.6744168122222.6744977136295.6845221239098.6845799194044.6746878522350.6746887021955.6747663274663.6748307028028.6748907072110.6749834049331.6749870597903.6750354202374.6750628941955.6851678667183.6651978274254.6151989355505.6752493847790.6852664346990.6653767577775.6654317840060.6755958408871.6756185989799.68563227834.67  56559481326.6556699110510.685736209134.67 57745675194.665896867971.65 59314873579.6159522377383.6760345424700.6861122376686.6861214533978.6761482382924.6161646795623.7061917199020.6561929812114.6061937685145.7161994440323.6862602652498.6762670790311.6863235321900.6463798011630.6764352634714.6766934446833.7567965490855.657993003374.65 8583720762.68 894743207.67  9675386044.67 00000100=00A00B00C00D00E00F00O00S00_00h00l01501>01G01P01T01X01a01f01g02002<02A02J02N02O02P02U02V02_02d02m03203>03J03S03T03`03d03m04104404@04I04R04V04Z04[04\04e04n05305705805A05E05N05O05T05X05a05b05c05g06006106206>06?06C06F06I06R06[06_06c06d06e06j07307<07E07J07K07Q07R07V07_07k07l07m08108408708808A08B08F08O08[08g08h09109609709;SS4CEIL2LO2H1S2LOSSSSSS4CEIL2LOS2HBS4CEIL2LO2H1S4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS2HBS4CEIL2LOS3SPRSS4CEIL2LOS4CEIL2LO2H1S3SPRS4CEIL2LOS2LOSSS3SPRSS4CEIL2LOS3SPRS4CEIL2LOS3SPRS4CEIL2LO2H1S4CEIL2LO2H1S4CEIL2LOSS4CEIL2LO2H1S2LOS4CEIL2LOS2HBS1NS4CEIL2LO2H1S4CEIL2LOS4CEIL2LOS2HBS2LOSSS4CEIL2LOS4CEIL2LOS3SPRS2LOSS4CEIL2LOS2LOS4CEIL2LOSS3SPRS2HBS4CEIL2LOSSS2HBS4CEIL2LOSSS4CEIL2LO2H1SS2LOS1NS1NS4CEIL2LOS4CEIL2LOS2LOS2HBSSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRSS1N2K0SS2HBS4CEIL2LOS4CEIL2LO2H1SSS2LOS1NS1NSS4CEIL2LOSS2LOS4CEIL2LOS4CEIL2LO2H1S1H2H22H62H7SS4CEIL2LOS3SPRSS2HB".
carve_frame 80%nat ST.
do 9 step.
step. step. step.
step. step. step. if_lit.
step. step. if_cases K0; zify_cond K0; [|exfalso; lia].
step. step. step.
step. step. lstep. step. if_lit.
lstep. lstep. zstep. zstep. zstep.
rewrite Z.lor_0_l.
zstep. zstep.
change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia.
setreg 11%Z (Z_to_bv 64 (rup n 8)) ltac:(f_equal; unfold rup; Z.div_mod_to_equations; lia).
step. step.
unfold putA_post. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
