(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 AKitQ.
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
(Z_to_bv 64 0x9f1b0) (Z_to_bv 64 (t + 80))
(Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (rup n 8)) (Z_to_bv 64 253) (Z_to_bv 64 0) a4 a5 a6 a7
(Z_to_bv 64 n) a3 a2 (Z_to_bv 64 hm) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36610) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp + -80)
/\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
#[using="Type"] Lemma putA_spec : forall (t hm n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo stb b1 ctx : Z),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 80 ->
mem_inv bsegs m ->
a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
rw_cells bsegs m 0x99908 [C8 (Z_to_bv 64 AFLAGS)] ->
rw_cells bsegs m 0x9fd64 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
rw_cells bsegs m hm [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
0 <= n <= Q_MAX -> AIMG_HI <= hm -> hm + 16 <= ATOP ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG hm 16 ->
evtF bsegs RNG (putA_post sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 F fc t hm n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36488) fc None m (seg_rom bsegs)).
Proof.
intros until ctx. intros ST CEIL LO MI -> -> -> -> QK GF FL HD N H0 H1 RIMG RSTK RH.
unfold AIMG_HI, AQUAR_Q, AQ_MAX, AFLAGS, Q_MAX, Q_MIN, Q_CACHE in *.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
word_range sp SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "01\0>11472836995.6711601497306.681162083374.67 11805467289.6511805467289.6611805467289.6711805467289.6811989311342.6813629548202.6115696294482.6715702970684.6816157723630.6717212185306.6817776320431.6618565840494.671901476206.67 19737586030.6620555087086.682130161072.67 21713897404.6621750412114.6722163107130.6522226183811.6723589365338.6623847006446.6724181503982.6524630998586.6825620414830.6825878270255.6625984619630.6827723960707.6630008181843.6130196181434.673051486595.67 30718442606.6731546410990.6832651489978.673355483630.68 33680001082.6734131883738.6534457081818.6835909988007.6635916187738.6736115622446.673662364220.68 36646331050.6136936768494.6837164696046.6537436222938.6737855536750.6739771606844.6540091925679.6640374333670.5842200251523.6842831019478.6743061431595.5643656575204.7143987951406.6744977136295.6845221239098.6845799194044.6746887021955.6746998556014.6547663274663.6748307028028.6748804778094.6749834049331.6749870597903.6749884718574.6650354202374.6750628941955.6851678667183.6651978274254.6151989355505.6753767577775.6654317840060.6754452579182.6755958408871.6756185989799.68563227834.67  56461247726.6757745675194.665896867971.65 59314873579.6159522377383.6760345424700.6861096069870.6761214533978.6761482382924.6161646795623.7061917199020.6561929812114.6061937685145.7161994440323.6862670790311.6863235321900.6463863132910.6764352634714.6764588566254.6866934446833.7567965490855.65692741842.67  7720336238.66 8054831726.67 8583720762.68 894743207.67  8967238126.68 9675386044.67 00000100=00A00B00C00D00E00N00O00X00\00e01101501>01G01P01Y01]01a01j01o02002<02E02N02S02\02`02i02j02k03003103:03C03H03Q03V03b03n03o04;04?04C04F04O04X04d04m05105505605705<05@05A05E05F05K05O05P05Y05Z05^05g05h05i06206>06?06C06F06I06M06Q06Z06[06\06a06j06o07007607707;07D07P07Q07R07V07Y07\07]07^07b07k08708@08L08M08V08_08h08m08n09709;SS4CEIL2LO2H1S2LOSSSSS4CEIL2LOSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LO2H1S2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS2HBS4CEIL2LOS3SPRSS4CEIL2LO2H1S4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS2LOS4CEIL2LOSSS3SPRSS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS3SPRS4CEIL2LO2H1S4CEIL2LO2H1SS4CEIL2LO2H1S2LOS2HBS1NS4CEIL2LOS4CEIL2LOS4CEIL2LO2H1S4CEIL2LOS2HBS2LOSSS3SPRS2LOSS2LOSS3SPRS2HBSS4CEIL2LOSS2HBS4CEIL2LOSSS4CEIL2LOS4CEIL2LO2H1SS2LOS1NS1NS2LOS2HBS4CEIL2LOSSS3SPRS4CEIL2LOS3SPRSS1N2K0SS2HBS4CEIL2LOS4CEIL2LO2H1SSS2LOS1NS1NSSS2LOS4CEIL2LOS4CEIL2LO2H1S4CEIL2LOS1H2H22H62H7SS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRSS4CEIL2LOS2HB".
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
