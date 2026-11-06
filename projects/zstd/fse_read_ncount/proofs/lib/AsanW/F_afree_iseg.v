(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 AKitQ F_aintal.
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
Definition ficptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(p lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
ms' = MS (mkR (Z_to_bv 64 0x53424) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
sp (Z_to_bv 64 p)
(Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x53410) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
(Z_to_bv 64 0x53410) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53468) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 2176, bv_unsigned sp); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -2128)
/\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
/\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
/\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m' 0x131f08 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ stk asegs m' 0xa3680 (0xa3680 + 0x81030)
/\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))).
#[using="Type"] Lemma ficptA_spec : forall (p : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
mem_inv asegs m ->
a0 = Z_to_bv 64 p -> 0 <= p < 2^47 ->
rw_cells asegs m 0xa317c [C4 (Z_to_bv 64 30)] ->
rw_cells asegs m 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)] ->
rw_cells asegs m 0x133fca [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m 0x99760 [C8 (Z_to_bv 64 0x131f20)] -> rw_cells asegs m 0x131f20 [C8 (Z_to_bv 64 4096)] ->
rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
(ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (ficptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> PR MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RSTK.
unfold AFREE_SYM, AFREE_PC, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z m) as MU0.
step.
Local Ltac2 Set LiaHints.tbl := fun () => "0340>11575978478.701162083360.89 1162083374.86 11658450183.8111805467289.6811805467289.6911805467289.7011805467289.7111805467289.8711805467289.8811805467289.9011903774446.6911944803374.8712844508569.7013219133678.6913390583683.6813993462363.8114010572455.8814118943342.7014253206403.7014491644918.8514698211132.7014782759150.6915025058286.701530906322.87 1530906322.90 15510396114.8715510396114.9015819558015.8115835617411.881595966771.87 1595966771.90 17292611950.6817508180239.8717508180239.9017776320431.6918112172441.6918295418137.7018677176814.7018848698606.7019003817779.902003044974.71 20633589486.7020725798332.7021176846097.8222570153326.7022700267513.6822700267513.8422976515865.6823488737418.8023562950937.7024245873445.6224630998586.7024689793902.7025835920692.8725878270255.6926291562981.8126494647592.6826494647592.6926494647592.7026494647592.7126494647592.8726494647592.8826494647592.9026507015092.822665991228.71 26734508604.7027377293550.7027730847314.8727730847314.9027810329426.8727810329426.9027813070503.7028064746879.6128575982988.8128809381244.8129022465774.7029496748159.6229782367974.8129915095918.7130196181434.6831156070897.9031158168048.813150149308.82 32651489978.7132762210492.6932965887298.9233680001082.6933893304857.8834197713817.7034233151718.5934563363993.7034643237692.8835042269550.683537628943.90 35973081767.6836115622447.6937844949358.683787933806.71 38687199342.7138748835203.7138773857693.8738773857693.9039268020206.6939631846169.7139782355367.7039833108633.6940005884953.7040069102958.7040871484270.7041535431150.7042267177992.8042744733806.7042831019478.8742831019478.9043000880110.8843061792393.5743268403504.8743268403504.9043987951406.7044021460374.7844534072174.6944697468441.6845141028272.9045221239098.8845273532441.704642516355.69 47169169795.7047469105018.7849360766237.9049432389714.6049878323996.8049921929014.6549978085870.8850492992828.8152024118390.8552074235540.9352118790567.6952364071662.8853223703150.7053746530983.7053767577775.6954452518048.8954465538982.7854844324854.8554862598254.7155530626798.7055916683929.7055972696470.7956170558594.61563227834.70  56721401731.7056912526318.7057000382702.6957745675194.7058512233326.7059349051708.6860492827805.8760492827805.9060857959228.8161359073817.7161917199020.6862236679847.7163235321900.6763267093326.9363398219886.686405779422.93 64163977966.6864219115431.706466066542.88 64932245891.7065088762478.7065175745553.8065434813422.7165573453422.7065792509166.7065977411438.6866000180723.8566067451964.8166209555097.8866260016006.6866260016006.8466377468316.816642473454.70 66656729710.7066747928658.8766747928658.9067290543932.8067943285742.8868309604434.8768309604434.90802261998.88  8583720762.70 8676799164.70 9111996248.82 9941623150.70 00000900=00A00B00C00D00E00F00G00H00I00R00V00W00`00a00b00c00l00m00n01201;01D01M01V01_01h01i01j01k01l02502602702;02<02=02F02O02P02Y02b02f03303<03M03_03`03a03b03f03k04404504904:04;04<04=04>04?04@04A04N04R04V04_04h05105:05C05D05E05T05a05j05k05l06506:06>06B06C06H06L06P06U06V06W06X06Y06]06f06g06h06l07507>07G07H07I07J07S07T07U07V07W07`07i08208708@08E08J08S08W08[08_08c08d08m08n09209709809909:09>09?09@09A09P09Y09f09g09h09i0:20:;0:<0:@0:D0:E0:F0:O0:X0:Y0:Z0:[0:`0:a0:j0;30;80;A0;E0;F0;G0;T0;U0;Y0;Z0;^0;b0;k0;l0<50<60<?0<@0<I0<V0<_0<h0=10=:0=C0=P0=Q0=X0=`0=m0>60>?0>H0>Q0>R0>[0>d0>m0?60?;0??0?@0?IS4CEIL2LOS2LOS2LOFSSSSSSSS4CEIL2LOS2LOSS4CEIL2LOSSSS4CEIL2LOSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOSSS2LOSSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LO3HspS4CEIL2LOS4CEIL2LO2Hj2Hi1HS4CEIL2LO3Hj02Hi1HSSSS2LOS3SPRS4CEIL2LOSS2LOFSSSSSSSS4CEIL2LO3HspS2HBS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LO3Hsp1HS4CEIL2LO3HspS4CEIL2LOSSS4CEIL2LOS3SPRS2PRS2PRFS3SPRS2HBS2JRS3SPRSSSSS2HBS4CEIL2LOSSS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS3SPRS3SPRS4CEIL2LOS2LOS2HBS2HBS2LOSS4CEIL2LOSS2HBS3SPRSSSS2PRSSSS4CEIL2LO3SPR1HS4CEIL2LOS4CEIL2LO3HspSFSS4CEIL2LOS4CEIL2LOSS2LOS2LOSSS4CEIL2LOS4CEIL2LOSSSS3SPRSS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS2HBSSS4CEIL2LO3HspSS2LOSS2LOS2JRS4CEIL2LOFS4CEIL2LOSS4CEIL2LOSS4CEIL2LOS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2PR1H2H0S4CEIL2LO3HspSS2Hj2HiS3Hj02HiS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOFS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS2HBSS4CEIL2LO".
carve_frame 2128%nat ST.
cb_split3 FR 16%nat 2040%nat 72%nat. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
do 8 step.
zstep. zstep. step. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs mm (669320 + 8 * j) (le8 (Z_to_bv 64 0)))
by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
clear Z2 MU0.
step. call_sp internal_allocator_spec;
[exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
try rename MI0 into MI. clear Z2'.
match goal with H : stk asegs ?mm lo _ |- _ => rename H into ST end.
match goal with H : stk asegs ?mm 669312 _ |- _ => rename H into IA' end.
match goal with H : rw_cells asegs ?mm 1253128 _ |- _ => rename H into FL' end.
match goal with H : forall j, _ -> bytes_at asegs _ _ _ |- _ => rename H into MAP end.
snapshot [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z MU1 WM1.
zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
step. if_lit.
zstep.
remember (Z.shiftr p 32) as j eqn:Hj.
assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.
pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
replace (669320 + 8 * j) with (669312 + j * 8 + 8) in RD by lia.
step. clear RD.
step. step. if_lit.
clear Hj JR.
zstep. zstep. zstep. zstep. zstep.
step. sstep. step.
step. step. lstep. step. step.
step. step. if_lit.
step. step. step.
step. step. lstep. step.
step. step. lstep. step. step.
step. zstep. zstep. zstep. step.
change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
sstep.
step. if_lit.
zstep. zstep. step. step. step. step.
rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
apply evtF_done. unfold ficptA_post. do 10 eexists. exists (firstn 2040 (skipn 16 junk)). eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ficptD_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(rav s0v s1v s2v s3v s4v s5v spv : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 : list byte),
stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 ->
mem_inv asegs m ->
(exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
(exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
rw_cells asegs m (bv_unsigned sp + -72) [C8 spv; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (fun ms' =>
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom asegs)
/\ stk asegs m lo (bv_unsigned sp))
(MS (mkR (Z_to_bv 64 0x53480) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53480) fc None m (seg_rom asegs)).
Proof.
intros until junk2. intros ST CEIL LO MI [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
word_range sp SPR.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00D0>13390583683.6814253206403.6817776320429.6718156171132.6220070138776.6125878270252.6830415381124.6236115622444.6838748835203.7043987951407.694642516355.68 47169169795.6949473387449.6353767577772.6856721401731.6958955648508.6261492862777.6361917199021.6763235321901.6764932245891.6900000100200600700800<00@00D00E00I00J00K00O00S00T00U00Y00]00a00bSSS2LOSSS2LOS2LOS2LOSS2LOSSS2LOS2LOSSS2LOS2LOS2LOS".
do 7 step. zstep. step.
pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
release_frame FRA' ST (bv_unsigned sp + -2112).
pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
release_frame FRT' ST (bv_unsigned sp + -72).
release_frame FRS ST (bv_unsigned sp).
apply evtF_done. split; [|exact ST].
reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
