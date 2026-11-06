(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase ABytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2.
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
ms' = MS (mkR (Z_to_bv 64 0x53584) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
sp (Z_to_bv 64 n)
(Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x53570) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
(Z_to_bv 64 0x53570) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x535c8) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -2128)
/\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
/\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
/\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
#[using="Type"] Lemma icptA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 - 16 ->
mem_inv asegs m ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
rw_cells asegs m 0xa3158 [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m 0xa317c [C4 (Z_to_bv 64 30)] ->
rw_cells asegs m 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)] ->
rw_cells asegs m 0x133fca [C1 (Z_to_bv 8 1)] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (icptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x532d4) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> NR INI MCS GOT CF34 RIMG RSTK. atop_facts.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 2128 - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
step.
Local Ltac2 Set LiaHints.tbl := fun () => "02O0>11575978478.651162083361.67 1162083375.65 11805467289.6311805467289.6411805467289.6511805467289.6611805467289.6711805467289.6811903774446.6411944803375.6512844508569.6513390583683.6313997492006.5914010572455.6614253206403.6514698211132.651530906322.66 1530906322.67 1530906322.68 15510396114.6615510396114.6715510396114.6815815196930.5915835617411.661595966771.66 1595966771.68 16856728066.5917508180239.6617508180239.6817721832112.6717776320431.6418112172441.6418295418137.6518677176814.6518848698606.6519003817779.682003044974.66 20725798332.6520970059894.6422570153326.6522976515865.6323492967905.5823562950937.6524630998586.6525483987182.6525835920692.6625878270255.642665991228.66 26734508604.6527377293550.6527730847314.6627730847314.6727730847314.6827813070503.6528060516446.5528290880502.6428496379187.6729501105410.5629915095918.6630196181434.6332651489978.6632762210492.6433680001082.6433893304857.6634197713817.6534233151718.5434563363993.6534643237692.663537628943.68 35561507310.6635973081767.63360322319.67  36115622447.6438748835203.6638773857693.6638773857693.6738773857693.6839268020206.6439631846169.6639782355367.6539833108633.6440005884953.6540069102958.6542263017827.5842744733806.6542831019478.6642831019478.6742831019478.6842976005733.5943059266230.5243268403504.6643268403504.6843987951406.6544490584985.6644534072174.6444697468441.6345141028272.6845221239098.6645273532441.654569555623.66 4642516355.64 46595657582.6347169169795.6547933512623.6648989959150.6549360766237.6749360766237.6849426064712.5449874034295.5849978085870.6650470234962.6650470234962.6750470234962.6851322024558.6651665594094.6451818863747.6652074235540.7252118790567.6452364071662.6653223703150.6553719345964.6553746530983.6553767577775.6454452518049.6755916683929.65563227834.65  56721401731.6556912526318.6557745675194.6558879845244.5859349051708.6360357415926.6560492827805.6660492827805.6760492827805.6860616668387.576129476974.65 61359073817.6661917199020.6362236679847.6663235321900.6263398219886.6364163977966.6364219115431.656466066542.66 64932245891.6565263019168.5965434813422.6665573453422.6565792509166.6565977411438.6366209555097.6668030567414.647219832892.66 8583720762.65 8676799164.65 8805124206.65 9941623150.65 00000;00?00C00D00E00F00G00H00I00T00X00Y00Z00[00\00]00a00l01701B01M01X01c01d01e01f01g01k01l01m02102502602702B02M02N02Y02]02^02i02j02k02l03103<03=03A03E03I03T03_03j04504604704804904:04E04J04O04S04X04Y04Z04[04\04`04a04l04m04n05205305405505605A05B05C05D05E05P05U05`05e05j05o06006406806<06@06A06L06M06Q06V06W06X06Y06d06e06i07407507607707807C07N07Y07d07o08:08;08<08=08H08S08W08X08\08`08a08f08g09209709809<09=09>09?09@09D09O09P09T09U09Y09d09o0:00:;0:<0:=0:H0:S0:^0:i0:j0:k0:o0;40;80;C0;NS4CEIL2LO1HS2LOS2LOSSSSSSS4CEIL2LO1HS2LOSSSSSS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSSSS2LOSSS2HBS2LOSSS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS2HBSS4CEIL2LO1HSSSS3SPRS4CEIL2LO1HSS2LOS2HBS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSSSSS4CEIL2LO1HS3SPRS3SPRS2HBS3SPRSSSSS2HBSS4CEIL2LO1HSSS2LOSSSSS4CEIL2LO1HSSSSS4CEIL2LO1HS3SPRS4CEIL2LO1HS3SPRS3SPRS3SPRSS2LOS2HBS2HBS2LOSS4CEIL2LO1HSS2HBS3SPRSSSS4CEIL2LO1HSS2LOS4CEIL2LO1HSSSSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSFSS4CEIL2LO1HS4CEIL2LO1HS2LOSS2LOS2LOSS3SPRSS4CEIL2LO1HS3SPRSS2HBSSSSS2LOS4CEIL2LO1HSS2LOSS2LOS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HSSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSS2HBS3SPRS2HBS4CEIL2LO1HS4CEIL2LO1H".
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
ms' = MS (mkR (Z_to_bv 64 0x535dc) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
s0v s1
(Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32468) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -2144)
/\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0v; C8 (Z_to_bv 64 0x535dc)].
#[using="Type"] Lemma icptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n lo : Z),
stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
mem_inv asegs m ->
s1 = Z_to_bv 64 n ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (icptB_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x535cc) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
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
stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
mem_inv asegs m ->
0 < UB < 2^64 ->
rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x535dc)] ->
(exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
(exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (fun ms' => exists m',
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom asegs)
/\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR (Z_to_bv 64 0x3246c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3246c) fc None m (seg_rom asegs)).
Proof.
intros until junk2. intros ST CEIL LO MI UBR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
word_range sp SPR.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
step. Local Ltac2 Set LiaHints.tbl := fun () => "00M0>13390583683.7114253206403.7216856789792.6517776320428.7118156171132.6420070138776.6325878270252.7126397653890.6530415381124.64360322319.72  36115622444.7138748835203.7343987951407.724642516355.71 47169169795.7247933512620.7149473387449.6551818863747.7153719345965.7053767577772.715624042486.70 56721401731.7258879845244.6458955648508.6459308628179.6561492862777.6561917199021.7063235321901.7064932245891.7200000100200600:00;00<00@00E00I00J00N00O00S00T00U00Y00]00^00b00f00g00h00i00j01201601:01>01?SSS2LOS2LOSSS2LOS3UBRS2LOSS2LOSS2LOSSS2LOS2LOSS2LOS2LOSSSSS3UBR2K0S2LOS2LOS2LOS".
if_cases K0; zify_cond K0. { exfalso. lia. }
do 4 step.
zstep. do 7 step. zstep. step.
release_frame FR16 ST (bv_unsigned sp + -2128).
pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
release_frame FRA' ST (bv_unsigned sp + -2112).
pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
release_frame FRT' ST (bv_unsigned sp + -72).
release_frame FRS ST (bv_unsigned sp).
apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
