(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AHarness_iface AKit FsKit AH_fse_kit F_memset F_asetshadow AFake5_iface AH_fse_calls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
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

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Ltac bcase K := if_cases K; zify_cond K.
Section CANSEC1. Context {rc : runConstT}.
Section S.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (D SZ : Z) (lo : Z) (SPA : Z).
Notation SP := (bv_unsigned sp).
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis LOC : ATOP <= lo.
Hypothesis SPT : SP + 16 <= 2^47.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis ESPA : SPA = (SP - 192) - (SP - 192) mod 32.
Variable RNG : footprint.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RI : rng_aimg RNG.
#[using="rc SP16 ESPA"] Lemma spa_props : SP - 208 <= SPA <= SP - 192 /\ SPA mod 32 = 0 /\ (SP + -192) - (SP + -192) mod 32 = SPA.
Proof. rewrite ESPA. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>53663102416.6000000LS4SP161H2H02H42H52H93H103H14".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc LOS LOC SPT SP16 ESPA RSTK RI"] Lemma f_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
stk asegs m lo SP -> mem_inv asegs m ->
rt_got m -> rt_shbase m -> rw_cells asegs m 0x997d8 [C8 (Z_to_bv 64 0xa2480)] -> rw_cells asegs m 0xa2480 [C4 (Z_to_bv 64 1)] ->
evtF asegs RNG (fun ms' => exists m' ja,
ms' = MS (mkR (Z_to_bv 64 0x80ea8) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 1792) (Z_to_bv 64 0xa2478) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 ASHOFF) s4 s5 s6 s7 (Z_to_bv 64 SZ) (Z_to_bv 64 D) s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 ASM5_ENTRY) fc None m' (seg_rom asegs)
/\ munch [(SP - 192, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\ rw_cells asegs m' SPA [CB 88 ja]
/\ stk asegs m' lo SPA /\ stk asegs m' (SPA + 88) (SP + -104))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST MI GOT SHB GSU SUA. unfold AFUZZ_ENTRY, ASM5_ENTRY, AHARNESS_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
pose proof spa_props as (SPAB & SPA32 & ESPA').
assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
pose proof (munch_refl [(SP - 192, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
zstep.
Local Ltac2 Set LiaHints.tbl := fun () => "00k0>1162083372.70 1237157135.72 12472314755.7014878889284.6315555790503.7117776320428.7019347287719.7119575182557.7019576181958.6623787153319.7124559885228.7025825925031.7125878270252.7026498395174.6126966040451.7126994131331.7127408782895.7127528277671.7028360455555.722986933752.64 30898146691.7133890036524.7034103486887.7136115622447.7136960603523.7138205351847.7039101079207.7240091925677.6940131048926.7340623765930.6743059266230.5943987951407.714609047859.68 48039688188.634805334695.72 49801938227.7251370739587.7051678667181.6953012503774.7353186721695.7253767577772.7054933170051.7157081557379.7058528444687.6859230329255.7059308628179.656144403652.61 61917199021.6963152402819.7063235321901.6964318223524.6465598123907.7166240597415.7066964538243.7267859076775.7168155467983.637316916790.64 7326914868.68 8847963168.64 00000500600700800900>00?00@00A00B00G00H00M00R00S00T00Y00Z00[00o01001501601;01<01=01>01C01D01I01N01S01T01U01V01W01X01]01^01_01d01e01f01g01h01l01m02202302802902:02;02<02=02Q02d03703<S3LOSSSSSS3LOSSSSSS3LOSSS3LOSS3LOSSSS3LOSSSS3LOS3LOC3RSP1H4SPABSS3LOSSS3LOSSSSS3LOSSS3LOSS3LOSS3LOSSSSSSS3LOSSSS3LOSSSSSS2K0SS3LOSSS3LOSSSSSSS3LOS3LOC3RSP1H4SPABS3LOS3LOC3SPT3RSP1HS3LOS3LOC3SPT3RSP1HS3LOS".
carve_frame 104%nat ST. carve_frame 88%nat ST.
zstep.
do 13 zstep.
zstep.
zstep.
rewrite land_m32F by lia. rewrite ESPA'.
release_frame FR1 ST (SP + -104).
destruct (stk_split asegs _ lo (SPA + 88) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
destruct (stk_carve asegs _ lo (SPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA0]]. clear ST1.
change (Z.of_nat 88) with 88 in STL, FRA0. replace (SPA + 88 - 88) with SPA in STL, FRA0 by lia.
zstep. zstep.
zstep. zstep. zstep. zstep.
clear GOT GSU.
zstep. rewrite (sx32_lit 1) by lia. zstep.
zstep.
zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
zstep. zstep.
apply evtF_done. change (Z_to_bv 64 2147450880) with (Z_to_bv 64 ASHOFF).
eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
split; [exact FR0|]. split; [exact FRA0|]. split; [exact STL| exact STG].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="lo LOS LOC SP16 ESPA RSTK RI"] Lemma f_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m (F : Z) (j0 j1 j2 : word) (junk ja : list byte) (FLG : Z),
rw_cells asegs m SPA [CB 88 ja] -> rw_cells asegs m F [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 FLG)] ->
rw_cells asegs m (SHF F) FSH0 -> mem_inv asegs m ->
rw_cells asegs m 0x997a0 [C8 (Z_to_bv 64 0x9b5e8)] -> rt_real_mem m ->
ablk F (F + 2048) -> F + 2048 <= ATOP -> F mod 2048 = 0 ->
rng RNG F 2048 -> rng RNG (shad F) 256 ->
evtF asegs RNG (fun ms' => exists m' (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (jb jc jd : list byte),
ms' = MS (mkR (Z_to_bv 64 0x80fdc) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 D) (Z_to_bv 64 SZ) y12 y13 y14 y15 y16 y17
(Z_to_bv 64 18446744073709551602) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (F + 608))
(Z_to_bv 64 (SHF F + 76)) s7 (Z_to_bv 64 SZ) (Z_to_bv 64 D) s10 (Z_to_bv 64 (SHF F)) y28 y29 y30 y31)
FR (Z_to_bv 64 0x82564) fc None m' (seg_rom asegs)
/\ munch [(SPA, SPA + 88); (F, F + 24); (SHF F, SHF F + 256)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' SPA [CB 16 jb; C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148)); CB 16 jc; C8 (Z_to_bv 64 F); CB 24 jd; C8 (Z_to_bv 64 F)]
/\ rw_cells asegs m' F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x15f28); C8 (Z_to_bv 64 0x80e34); CB 2016 junk; C8 (Z_to_bv 64 FLG)]
/\ rw_cells asegs m' (SHF F) (FSH F8S F8S F8S BF8 BF8))
(MS (mkR (Z_to_bv 64 0x80ea8) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 F) x11 x12 x13 x14 x15 x16 x17
s2 (Z_to_bv 64 ASHOFF) s4 s5 s6 s7 (Z_to_bv 64 SZ) (Z_to_bv 64 D) s10 s11 x28 x29 x30 x31)
FR (Z_to_bv 64 0x80ea8) fc None m (seg_rom asegs)).
Proof.
intros until FLG. intros FRA FFC SH0 MI GOTM REALM FH FC F2048 RF RSF. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
unfold SHF, FSH0, FSH, AHARNESS_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND, KHIGH in *.
pose proof spa_props as (SPAB & SPA32 & _).
Local Ltac2 Set LiaHints.tbl := fun () => "01;0?1370123485.127 14549903879.87 14723231628.82 16707650838.12320572578561.11720674773441.11721316803553.13122004642705.11722683272097.11723568199473.13124522298490.96 25059262615.82 25349552462.72 25675713676.96 26918830103.96 28381205639.10829782367974.72 29782367974.73 30400065313.13132618034033.1313287162942.89  33849775066.10934957802305.13135226064150.10935495549846.11035495549846.82 35495549846.96 35594558818.90 35945580172.82 36282397969.13137648604625.1173851966096.87  3873683841.103 39665081360.11841349132957.86 41427975703.90 41624233725.12743496930236.81 4398706810.109 44032511105.13145114998679.11045362379089.13149236341442.90 49877423329.10350565131410.90 5169965649.103 52124489777.10353005185538.13253794353558.95 54353223320.90 55119024802.13256041590284.10757197585530.12358504925061.89 58952161313.10359314873579.79 60502248570.12461170003057.10362376611962.11062536353548.96 63202992012.11063513965633.10364843933201.10366560187549.86 66811069213.90 67294985855.74 6854930828.110 7038263393.117 7673273466.95  7676635532.91  851547.87      8854610.78     89901372.95    9183238129.117 9293723057.117 00000500:00?00D00I00N00S00X00]00b00g01001501:01C01U01Z01_01d01i01n02302802=02B02G02L02Q02Z02_02d02i02n03303803=03B03G03L03Q03Z03_03d03i03n04304804=04B04G04L04g04l05105605B05G05L05Q05Z05_05d05i05n06306K06T06Y06^06c07007=07B07G07LS3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH23BSFS2FH5F20481H2H02H9S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S5F20483FH13FH31H2H02H93H24S3FH2S3FH2S3FH2S3FH13FH22K0S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH2S3FH2S3FH2S3LOS3LOC3FH23RSP4SPAB1HS3FH23BSFS3FH2S3FH2S3FH2S3FH13FH23FH4S3FH13FH23FH4S3FH2S3FH2S3FH2".
replace (shad F) with (Z.shiftr F 3 + ASHOFF) in RSF by (unfold shad; lia).
assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 256 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
assert (SHDJ : F + 2048 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= F).
{ rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. unfold ablk, AIMG_HI, KLS in FH. Z.div_mod_to_equations. lia. }
assert (RFRA : rng RNG SPA 88) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof (munch_refl [(SPA, SPA + 88); (F, F + 24); (Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 256)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
zstep.
zstep.
zstep.
zstep. bcase K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia).
zstep.
zstep.
do 7 zstep.
zstep. zstep.
zstep.
zstep.
zstep.
zstep.
replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SH : rw_cells asegs mx (Z.shiftr F 3 + ASHOFF) _ |- _ =>
pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
zstep. clear SOK. zstep. zstep. zstep.
zstep. zstep. zstep.
zstep.
lazymatch goal with SH : rw_cells asegs _ (Z.shiftr F 3 + ASHOFF) _ |- _ => rw_split SH 4%nat SHa SHr end.
rw_split SHr 1%nat SHb SHc.
call (ss_f8_z RNG); [ first [ exact SHb | exact GOTM | exact REALM | eassumption | lia ] .. | ].
change (Z.to_nat 64) with 64%nat in POST. rw_join SHa POST SH1. rw_join SH1 SHc SH. cbn [app] in SH.
zstep.
replace (Z_to_bv 64 (-14)) with (Z_to_bv 64 18446744073709551602) by (apply Z_to_bv_eqm; reflexivity).
do 8 zstep.
zstep. zstep. zstep.
zstep.
rw_split SH 13%nat SHa SHr. rw_split SHr 1%nat SHb SHc.
call (ss_f8_z RNG); [ first [ exact SHb | exact GOTM | exact REALM | eassumption | lia ] .. | ].
change (Z.to_nat 64) with 64%nat in POST. rw_join SHa POST SH1. rw_join SH1 SHc SH. cbn [app] in SH.
do 8 zstep.
zstep. zstep. zstep.
zstep.
rw_split SH 22%nat SHa SHr. rw_split SHr 1%nat SHb SHc.
call (ss_f8_z RNG); [ first [ exact SHb | exact GOTM | exact REALM | eassumption | lia ] .. | ].
change (Z.to_nat 64) with 64%nat in POST. rw_join SHa POST SH1. rw_join SH1 SHc SH. cbn [app] in SH.
do 8 zstep.
zstep. zstep.
replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
do 4 zstep.
zstep. zstep. zstep.
apply evtF_done.
do 14 eexists. eexists _, _, _.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|].
split; [exact FRA|]. split; [exact FFC| exact SH].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
