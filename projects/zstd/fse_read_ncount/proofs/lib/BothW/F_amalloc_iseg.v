(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase ABytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2.
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
Definition icptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(n lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
ms' = MS (mkR (Z_to_bv 64 0x53470) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
sp (Z_to_bv 64 n)
(Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x5345c) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
(Z_to_bv 64 0x5345c) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x534b4) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp + -2128)
/\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
/\ rw_cells bsegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
/\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
#[using="Type"] Lemma icptA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n lo : Z),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 - 16 ->
mem_inv bsegs m ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
rw_cells bsegs m 0xa3218 [C1 (Z_to_bv 8 1)] ->
rw_cells bsegs m 0xa323c [C4 (Z_to_bv 64 30)] ->
rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)] ->
rw_cells bsegs m 0x13408a [C1 (Z_to_bv 8 1)] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF bsegs RNG (icptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x531c0) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> NR INI MCS GOT CF34 RIMG RSTK. atop_facts.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 2128 - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
step.
Local Ltac2 Set LiaHints.tbl := fun () => "02O0>10894115438.6611230823790.6511232843474.6611232843474.6711232843474.681162083361.67 1162083375.65 11805467289.6311805467289.6411805467289.6511805467289.6611805467289.6711805467289.6811944803375.6512685940462.6512844508569.6513390583683.6313997492006.5914010572455.6614253206403.6514262234230.6414698211132.6515815196930.5915835617411.661595966771.66 1595966771.68 16856728066.5917508180239.6617508180239.6817721832112.6717776320431.6418112172441.6418295418137.6518500769902.6518736735982.641892362350.66 19003817779.6819130765422.6319622476014.6420725798332.6520861669742.6521875103086.6522976515865.6323492967905.5823562950937.6524630998586.65249852526.65  25792608750.6525835920692.6625878270255.642665991228.66 26734508604.6527813070503.6528060516446.5528496379187.6729501105410.5629531591534.6529717588462.6629870281326.6530196181434.6331521058898.6631521058898.6731521058898.6832503858158.6632651489978.6632716547054.6632762210492.6433680001082.6433893304857.6634197713817.6534233151718.5434563363993.6534643237692.663517109230.65 3537628943.68 35973081767.63360322319.67  36087104750.6536115622447.6438748835203.6638773857693.6638773857693.6738773857693.6839631846169.6639782355367.6539833108633.6439955995858.6639955995858.6739955995858.6840005884953.654085338990.64 41317949302.6542263017827.5842831019478.6642831019478.6742831019478.6842976005733.5943059266230.5243268403504.6643268403504.6843987951406.6544490584985.6644697468441.6344752146798.6345141028272.6845221239098.6645273532441.654569555623.66 4642516355.64 47169169795.6547933512623.6649360766237.6749360766237.6849426064712.5449874034295.5850569079278.6550621823214.6550808556270.6351818863747.6652074235540.7252118790567.6452174953590.6453719345964.6553746530983.6553767577775.6454277570414.6354452518049.6754465698286.6555916683929.65563227834.65  56721401731.6557745675194.6558879845244.5859349051708.6359426343926.6460165880658.6660165880658.6760165880658.6860492827805.6660492827805.6760492827805.6860616668387.5761257697518.6561359073817.6661826058350.6661917199020.6361925142126.6562236679847.6663235321900.6263722139630.6464219115431.6564932245891.6565263019168.5966209555097.667219832892.66 7708480366.66 8109200110.66 8583720762.65 8676799164.65 00000;00F00Q00\00g00k00o01001101201301401501901D01E01F01G01H01I01J01N01O01P01Q01R01V01W01X01\01`01a01b01m02802C02D02O02Z02^02i03403503603703<03G03R03S03W03[03_03`03a03b03c03n04904D04I04T04_04j05505:05E05I05N05O05P05Q05R05V05a05b05c05d05o06306406506606706806906:06E06P06[06\06g06h06m07207707<07=07A07E07I07M07N07O07Z07^07c07d07e07f07g07k07l07m07n07o08:08E08P08Q08R08S08T08X08Y08]08h08l09709809=09>09C09D09H09I09T09_09j09k09l09m0:10:<0:=0:H0:L0:W0:X0:\0:g0:h0:i0:j0:k0:o0;:0;E0;J0;NS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2LOS2LOSSSSSSS2LOS4CEIL2LO1HSSSSSSS2HBSSSSS2LOSSS2HBS2LOSSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS2HBS4CEIL2LO1HS4CEIL2LO1HSSSS3SPRS4CEIL2LO1HS4CEIL2LO1HSS2LOS2HBS2HBSSSSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SPRS4CEIL2LO1HS2HBS3SPRSSSSS2HBS4CEIL2LO1HSSSS4CEIL2LO1HS2LOSSSSSSSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HSS3SPRS3SPRS3SPRS3SPRSS2LOS2HBS2HBS2LOSSS4CEIL2LO1HS2HBS3SPRSSSSS2LOSSSSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSFSSS2LOSS2LOS4CEIL2LO1HS2LOS4CEIL2LO1HSS3SPRSS3SPRSS2HBSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSSS2LOS4CEIL2LO1HSS4CEIL2LO1HS2LOS4CEIL2LO1HSS2LOS4CEIL2LO1HSSSSS2HBS4CEIL2LO1HS4CEIL2LO1HS3SPRS2HB".
carve_frame 2128%nat ST.
cb_split3 FR 16%nat 2040%nat 72%nat. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
do 8 step.
zstep. zstep. step. step.
step. carve_frame 16%nat ST.
do 5 step. lstep. step. step. step. if_lit.
do 4 step. release_frame FR ST (bv_unsigned sp + -2128).
step. if_lit.
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
apply evtF_done. unfold icptA_post. do 10 eexists. exists (firstn 2040 (skipn 16 junk)). eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition icptB_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0v : word) (F : bvmap 5 word) (fc : bv 32)
(n lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
fun ms' => exists m',
ms' = MS (mkR (Z_to_bv 64 0x534c8) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
s0v s1
(Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32354) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp + -2144)
/\ rw_cells bsegs m' (bv_unsigned sp + -2144) [C8 s0v; C8 (Z_to_bv 64 0x534c8)].
#[using="Type"] Lemma icptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n lo : Z),
stk bsegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
mem_inv bsegs m ->
s1 = Z_to_bv 64 n ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF bsegs RNG (icptB_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x534b8) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
zstep. zstep. step. step.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>11805467289.5511805467289.5717721832112.5728496379187.57360322319.57  42831019478.5742976005733.4845221239098.554569555623.55 47933512623.5651818863747.5553719345964.5460619012633.467219832892.55 00000100200600700800=00>00C00D00H00I00M00Q00USSS2HBSSS3SPRSS3SPRSS2LOSS2LOS2LOS2HB".
carve_frame 16%nat ST.
do 3 step.
do 7 step.
apply evtF_done. unfold icptB_post, AINSTANCE. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma icptC_spec : forall RNG sp gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(rav s0v s1v s2v s3v s4v s5v s0i : word) (F : bvmap 5 word) fc (m : amem) (UB lo : Z) (junk2 : list byte),
stk bsegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
mem_inv bsegs m ->
0 < UB < 2^64 ->
rw_cells bsegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x534c8)] ->
(exists csA, rw_cells bsegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
(exists csT, rw_cells bsegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
rw_cells bsegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF bsegs RNG (fun ms' => exists m',
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom bsegs)
/\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp))
(MS (mkR (Z_to_bv 64 0x32358) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32358) fc None m (seg_rom bsegs)).
Proof.
intros until junk2. intros ST CEIL LO MI UBR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
word_range sp SPR.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
step. Local Ltac2 Set LiaHints.tbl := fun () => "00M0>13390583683.7114253206403.7216856789792.6517776320428.7118156171132.6420070138776.6325878270252.7126397653890.6530415381124.64360322319.72  36115622444.7138350421878.7038748835203.7343987951407.724642516355.71 47169169795.7247933512620.7149473387449.6551818863747.7153719345965.7053767577772.7156721401731.7258879845244.6458955648508.6459308628179.6561492862777.6561917199021.7063235321901.7064932245891.7200000100200600:00;00<00@00E00I00J00N00O00P00T00U00V00Z00^00_00c00g00h00i00j01201601:01>01?SSS2LOS2LOSSS2LOS3UBRS2LOSS2LOSSS2LOSSS2LOS2LOSS2LOS2LOSSSS3UBR2K0S2LOS2LOS2LOS".
if_cases K0; zify_cond K0. { exfalso. lia. }
do 4 step.
zstep. do 7 step. zstep. step.
release_frame FR16 ST (bv_unsigned sp + -2128).
pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
release_frame FRA' ST (bv_unsigned sp + -2112).
pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
release_frame FRT' ST (bv_unsigned sp + -72).
release_frame FRS ST (bv_unsigned sp).
apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
