(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AKitQ.
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
                  (Z_to_bv 64 0x9daf0) (Z_to_bv 64 (t + 80))
                  (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (rup n 8)) (Z_to_bv 64 253) (Z_to_bv 64 0) a4 a5 a6 a7
                  (Z_to_bv 64 n) a3 a2 (Z_to_bv 64 hm) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x354b4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma putA_spec : forall (t hm n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo stb b1 ctx : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 80 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0x98e30 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0x9e6a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= n <= Q_MAX -> AIMG_HI <= hm -> hm + 16 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG hm 16 ->
  evtF asegs RNG (putA_post sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3532c) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros ST CEIL LO MI -> -> -> -> QK GF FL HD N H0 H1 RIMG RSTK RH.
  unfold AIMG_HI, AQUAR_Q, AQ_MAX, AFLAGS, Q_MAX, Q_MIN, Q_CACHE in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "01\0>10197707630.6711472836995.6711601497306.681162083374.67 11805467289.6511805467289.6611805467289.6711805467289.6813629548202.6115702970684.6817212185306.6817362271214.6717776320431.662130161072.67 21713897404.6621760655342.6522163107130.6522226183811.6723513515246.6723589365338.6624630998586.6825878270255.6627723960707.6627908601838.6829456923118.6830008181843.6130196181434.673051486595.67 31466597614.6832651489978.6733680001082.6734131883738.6534253562734.6634457081818.6835310472686.6835909988007.6635916187738.6736033452270.6736115622446.6736585497582.683662364220.68 36646331050.6137436222938.6738889585390.6739771606844.6540091925679.6640374333670.5840805592686.6740830091886.6741966671698.6742200251523.6842831019478.6743061431595.5643656575204.7143987951406.6744977136295.6845221239098.6845799194044.6746887021955.6747619645806.6747663274663.6748076354030.6548224240750.6848307028028.6749834049331.6749870597903.6750354202374.6750628941955.6851678667183.6651978274254.6151989355505.6753767577775.6654317840060.6755687327086.6555958408871.6756185989799.68563227834.67  57338214255.6057745675194.6657995278062.6858571392494.6658732652910.665896867971.65 59314873579.6159522377383.6760345424700.6861214533978.6761482382924.6161646795623.7061917199020.6561929812114.6061937685145.7161994440323.6862309656174.6762670790311.6862802417774.6763235321900.6464352634714.6764560625362.6767965490855.6568459368814.687021785682.67 7152381806.68 8583720762.68 894743207.67  9675386044.67 9882407662.67 992066670.67  00000900:00F00J00K00L00M00N00O00S00_00h00l01001401=01B01C01L01X01]01a01b01k02402502:02;02D02I02N02Z02c02o03803903E03N03R03[03_03b03n04704;04?04@04I04R04[04\04a04e04f04j04k05005405505>05?05H05Q05U05V05W05c05d05h05k05n06206606?06@06A06F06G06L06U06^06g06h06n06o07307?07@07A07E07H07K07L07U07V07_07c07o08808908B08K08T08Y08Z08^08g090S4CEIL2LOSS4CEIL2LO2H1S2LOSSSSSS2HBS4CEIL2LO2H1S4CEIL2LOS2LOS2HBS2HBS4CEIL2LOS3SPRSS4CEIL2LOS4CEIL2LO2H1S3SPRS2LOSS4CEIL2LOS4CEIL2LOSS3SPRSS4CEIL2LOS3SPRS3SPRS4CEIL2LO2H1S4CEIL2LOS4CEIL2LO2H1S4CEIL2LOSS4CEIL2LO2H1S4CEIL2LOS2LOS4CEIL2LOS2HBS1NS4CEIL2LO2H1S4CEIL2LOS2HBS2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3SPRS2LOSS2LOSS3SPRS2HBSS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBSSS4CEIL2LO2H1SS2LOS1NS1NS2LOS2HBS4CEIL2LOSSS3SPRSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOSS1N2K0SS2HBS4CEIL2LO2H1SSS2LOS1NS1NSS4CEIL2LOSS4CEIL2LOS2LOS4CEIL2LO2H1S4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRSS2HBS4CEIL2LOS4CEIL2LO".
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
