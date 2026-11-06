(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AKitQ.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition putA_post (sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
                  (Z_to_bv 64 0x9dcb0) (Z_to_bv 64 (t + 80))
                  (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (rup n 8)) (Z_to_bv 64 253) (Z_to_bv 64 0) a4 a5 a6 a7
                  (Z_to_bv 64 n) a3 a2 (Z_to_bv 64 hm) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x354b8) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma putA_spec : forall (t hm n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo stb b1 ctx : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 80 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0x99008 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0x9e864 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= n <= Q_MAX -> AIMG_HI <= hm -> hm + 16 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG hm 16 ->
  evtF bsegs RNG (putA_post sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35330) fc None m (seg_rom bsegs)).
Proof.
  intros until ctx. intros ST CEIL LO MI -> -> -> -> QK GF FL HD N H0 H1 RIMG RSTK RH.
  unfold AIMG_HI, AQUAR_Q, AQ_MAX, AFLAGS, Q_MAX, Q_MIN, Q_CACHE in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "01\0>11391583470.6711472836995.6711601497306.681162083374.67 11805467289.6511805467289.6611805467289.6711805467289.6811903774446.6713629548202.6115702970684.6815776184302.6817040090734.6717212185306.6817776320431.6618848698606.682003044974.67 2130161072.67 2148553070.68 21713897404.6622163107130.6522226183811.6723589365338.6624630998586.6825878270255.6626757167854.6727723960707.6627730847314.6728679466606.6730008181843.6130196181434.673051486595.67 32651489978.6733351324398.6733647749998.6733680001082.6733885744366.6834131883738.6534457081818.6835153358318.6535909988007.6635916187738.6736115622446.673662364220.68 36646331050.6137436222938.6737738008046.6839771606844.6540069102958.6640091925679.6640374333670.5840814410734.6742200251523.6842744733806.6742831019478.6743061431595.5643656575204.7143987951406.6744977136295.6845221239098.6845799194044.6746441072110.6646600235374.6646887021955.6747663274663.6748307028028.6749834049331.6749870597903.6749978085870.6850354202374.6750491175406.6550628941955.6850634998894.6851678667183.6651978274254.6151989355505.6752436596434.6753767577775.6654317840060.6755958408871.6756185989799.68563227834.67  56912526318.6857338214255.6057581223022.6757745675194.6658102279534.655896867971.65 59314873579.6159522377383.6760345424700.6861214533978.6761482382924.6161646795623.7061917199020.6561929812114.6061937685145.7161994440323.6862670790311.6863235321900.6463617233490.6763728955246.6864352634714.6765977411438.6767965490855.658583720762.68 894743207.67  9675386044.67 00000900:00F00J00K00L00M00N00W00X00\00e00n01:01>01G01P01T01]01a01f01g02302802<02E02F02O02X02Y02^02_02d02m03603;03D03P03\03e03f04204604:04=04I04R04V04_04c04d04m04n05705<05@05A05E05F05K05O05X05a05b05c05g05h05i06206>06G06H06Q06U06X06[06d06h06l06m06n07307<07=07F07K07T07U07[07\07`07l07m07n08208508808908:08>08G08P08\08e08f08k08l090S4CEIL2LOSS4CEIL2LO2H1S2LOSSSSS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LO2H1S2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS2HBS3SPRSS4CEIL2LO2H1S3SPRS2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOSS3SPRSS3SPRS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LO2H1S4CEIL2LO2H1S4CEIL2LOSS4CEIL2LO2H1S2LOS2HBS1NS4CEIL2LO2H1S4CEIL2LOS2HBS4CEIL2LOS2LOSS4CEIL2LOSS4CEIL2LOS3SPRS2LOSS2LOSS3SPRS2HBS4CEIL2LOS4CEIL2LOSSS2HBSSS4CEIL2LOS4CEIL2LO2H1S4CEIL2LOSS4CEIL2LOS2LOS1NS1NS4CEIL2LOS2LOS2HBSSS3SPRS4CEIL2LOSS4CEIL2LOS3SPRS4CEIL2LOSS1N2K0SS2HBS4CEIL2LO2H1SSS2LOS1NS1NSSS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2H1S4CEIL2LOSS3SPRSS2HB".
carve_frame 80%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. step. if_lit.                    (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [|exfalso; lia].   (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  step. step. lstep. step. if_lit.             (* [comment removed for export] *)
  lstep. lstep. zstep. zstep. zstep.           (* [comment removed for export] *)
  rewrite Z.lor_0_l.
  zstep. zstep.                                (* [comment removed for export] *)
  change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia.
  setreg 11%Z (Z_to_bv 64 (rup n 8)) ltac:(f_equal; unfold rup; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. step.                                  (* [comment removed for export] *)
  unfold putA_post. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
