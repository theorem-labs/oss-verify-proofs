(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 AKitQ F_aintal.
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
ms' = MS (mkR (Z_to_bv 64 0x53310) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
sp (Z_to_bv 64 p)
(Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x532fc) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
(Z_to_bv 64 0x532fc) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53354) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 2176, bv_unsigned sp); (0xa3740, 0xa3740 + 0x81030); (0x131fc8, 0x131fc8 + 4)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp + -2128)
/\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
/\ rw_cells bsegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
/\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells bsegs m' 0x131fc8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ stk bsegs m' 0xa3740 (0xa3740 + 0x81030)
/\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xa3748 + 8 * j) (le8 (Z_to_bv 64 0))).
#[using="Type"] Lemma ficptA_spec : forall (p : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
mem_inv bsegs m ->
a0 = Z_to_bv 64 p -> 0 <= p < 2^47 ->
rw_cells bsegs m 0xa323c [C4 (Z_to_bv 64 30)] ->
rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)] ->
rw_cells bsegs m 0x13408a [C1 (Z_to_bv 8 1)] ->
rw_cells bsegs m 0x998f0 [C8 (Z_to_bv 64 0x131fe0)] -> rw_cells bsegs m 0x131fe0 [C8 (Z_to_bv 64 4096)] ->
rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
stk bsegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
(ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF bsegs RNG (ficptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> PR MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RSTK.
unfold AFREE_SYM, AFREE_PC, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp); (0xa3740, 0xa3740 + 0x81030); (0x131fc8, 0x131fc8 + 4)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z m) as MU0.
step.
Local Ltac2 Set LiaHints.tbl := fun () => "0340>10177642990.7010500596124.8110512138478.6911230823790.7011232843474.8711232843474.901162083360.89 1162083374.86 11658450183.8111805467289.6811805467289.6911805467289.7011805467289.7111805467289.8711805467289.8811805467289.9011944803374.8712685940462.7012844508569.7013390583683.6813993462363.8114010572455.8814253206403.7014698211132.7015819558015.8115835617411.881595966771.87 1595966771.90 1629019516.81 16824022294.7917424134738.8717424134738.9017508180239.8717508180239.9017776320431.6918112172441.6918295418137.701892362350.71 19003817779.9019130765422.6819622476014.6919861076086.8520566891510.8520725798332.7020861669742.7021459134830.7021916162286.6922652873582.6822700267513.6822700267513.8422976515865.6823291651388.8123488737418.8023562950937.7023900099601.8024245873445.6224630998586.70249852526.70  25025521262.7125792608750.7025835920692.8725878270255.6926291562981.8126494647592.6826494647592.6926494647592.7026494647592.7126494647592.8726494647592.8826494647592.9026507015092.822665991228.71 26734508604.7027813070503.7028064746879.6128535651182.7028575982988.8128857563758.7029322360558.7029496748159.6229531591534.7029782367974.8129870281326.7030196181434.6831156070897.9031158168048.8131521058898.8731521058898.9032440122478.7032503858158.7132651489978.7132716547054.8832762210492.6932965887298.9233680001082.6933893304857.8834197713817.7034233151718.5934563363993.7034643237692.8835012330478.883537628943.90 35973081767.6836087104750.7036115622447.6938166047726.8838748835203.7138773857693.8738773857693.9039208223342.7039530135918.6839631846169.7139782355367.7039833108633.6939955995858.8739955995858.9040005884953.704085338990.69 42267177992.8042426800622.7042548949842.8742548949842.9042831019478.8742831019478.9043061792393.5743268403504.8743268403504.9043741526382.6843987951406.7044021460374.7844690296508.8244697468441.6844752146798.6845141028272.9045221239098.8845273532441.704642516355.69 46610241646.7147169169795.7047469105018.7849272000060.8149360766237.9049432389714.6049878323996.8049921929014.6550569079278.7050621823214.7050808556270.685087518190.88 51262103278.7052074235540.9352118790567.6953746530983.7053767577775.6954444793660.8154452518048.8954465538982.7854465698286.7055419944174.7055916683929.7056170558594.61563227834.70  56721401731.7057745675194.7058248097398.8559349051708.6859714667374.7060492827805.8760492827805.9060551939928.8261359073817.7161826058350.8861892124754.8761892124754.9061917199020.6861925142126.7062236679847.7162826138350.6963235321900.6763267093326.9363722139630.696405779422.93 64219115431.7064932245891.7066000180723.8566209555097.8866260016006.6866260016006.8466400913390.7068202125073.827708480366.71 8109200110.88 8583720762.70 8676799164.70 888033390.71  99807036.80   00000900F00O00X00a00j00n01201301401501601701801901:01>01G01H01I01J01K01L01P01Q01R01S01T01a01b01k02402502602:02;02<02E02F02O02X02Y02Z02^02g03003903B03S03e03f04304404504B04F04K04T04]04f04g04k04l04m04n04o05005105205305@05D05H05I05J05S05b05k06406506>06?06H06M06Q06U06^06g07007907>07G07K07O07T07U07V07W07X07\07e07f07g08008408=08>08?08@08I08R08S08T08U08^08g08h09109609?09H09Q09V09[09_09c09g0:00:40:50:60:70:@0:D0:I0:J0:K0:T0:U0:Y0:f0:g0:h0:i0;80;A0;J0;S0;\0;e0;f0;g0;h0;l0<90<=0<>0<G0<P0<Q0<R0<W0<X0<]0<^0<b0<k0<l0<m0<n0<o0=80=A0=J0=N0=W0=X0=a0=e0=i0>20>30>40>50>>0>?0>F0>N0>W0>d0>m0?60?;0??0?H0?IS4CEIL2LOS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOFSSSSSSSS2LOS4CEIL2LOSSSSSS2HBSSSSS4CEIL2LO3HspSS4CEIL2LOS4CEIL2LOSSS2LOSSS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2Hj2Hi1HS4CEIL2LO3Hj02Hi1HSS4CEIL2LO3HspSSS4CEIL2LO3HspS2LOS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOSS2LOFSSSSSSSS4CEIL2LO3HspS2HBS2HBSSS4CEIL2LOS4CEIL2LO3Hsp1HS4CEIL2LOS4CEIL2LOSS4CEIL2LOSS4CEIL2LOS3SPRS2PRS2PRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS2HBS2JRS3SPRSSSSS2HBS4CEIL2LOSSS4CEIL2LOS2LOS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS3SPRS2LOS2HBS2HBS4CEIL2LOS2LOSFSS4CEIL2LOS2HBS3SPRSSS4CEIL2LOSS2PRS4CEIL2LO3HspSSSS4CEIL2LO3SPR1HS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOFSSS2LOS4CEIL2LO3HspS2LOSS4CEIL2LOS4CEIL2LOSSS3SPRSS3SPRSS2HBS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOSS4CEIL2LOS2LOS2JRS4CEIL2LOFSSS2PR1H2H0SS2Hj2HiS3Hj02HiS4CEIL2LOS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS3SPRS2HBS4CEIL2LOF".
carve_frame 2128%nat ST.
cb_split3 FR 16%nat 2040%nat 72%nat. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
do 8 step.
zstep. zstep. step. step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs mm (669512 + 8 * j) (le8 (Z_to_bv 64 0)))
by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
clear Z2 MU0.
step. call_sp internal_allocator_spec;
[exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
try rename MI0 into MI. clear Z2'.
match goal with H : stk bsegs ?mm lo _ |- _ => rename H into ST end.
match goal with H : stk bsegs ?mm 669504 _ |- _ => rename H into IA' end.
match goal with H : rw_cells bsegs ?mm 1253320 _ |- _ => rename H into FL' end.
match goal with H : forall j, _ -> bytes_at bsegs _ _ _ |- _ => rename H into MAP end.
snapshot [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z MU1 WM1.
zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
step. if_lit.
zstep.
remember (Z.shiftr p 32) as j eqn:Hj.
assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.
pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
replace (669512 + 8 * j) with (669504 + j * 8 + 8) in RD by lia.
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
stk bsegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 ->
mem_inv bsegs m ->
(exists csA, rw_cells bsegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
(exists csT, rw_cells bsegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
rw_cells bsegs m (bv_unsigned sp + -72) [C8 spv; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF bsegs RNG (fun ms' =>
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom bsegs)
/\ stk bsegs m lo (bv_unsigned sp))
(MS (mkR (Z_to_bv 64 0x5336c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5336c) fc None m (seg_rom bsegs)).
Proof.
intros until junk2. intros ST CEIL LO MI [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
word_range sp SPR.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00D0>13390583683.6814253206403.6817776320429.6718156171132.6220070138776.6125878270252.6830415381124.6236115622444.6838748835203.7043987951407.694642516355.68 47169169795.6949473387449.6353767577772.6856721401731.6958955648508.6261492862777.6361917199021.6763235321901.6764932245891.6900000100200600700800<00@00D00E00I00J00K00O00S00T00U00Y00]00a00bSSS2LOSSS2LOS2LOS2LOSS2LOSSS2LOS2LOSSS2LOS2LOS2LOS".
do 7 step. zstep. step.
pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
release_frame FRA' ST (bv_unsigned sp + -2112).
pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
release_frame FRT' ST (bv_unsigned sp + -72).
release_frame FRS ST (bv_unsigned sp).
apply evtF_done. split; [|exact ST].
reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
