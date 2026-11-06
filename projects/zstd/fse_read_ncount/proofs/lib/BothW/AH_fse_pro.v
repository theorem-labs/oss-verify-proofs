(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AHarness_iface AKit FsKit AH_fse_kit F_memset F_asetshadow AFake5_iface AH_fse_calls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import ShadowTac.
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
Hypothesis ESPA : SPA = (SP - 224) - (SP - 224) mod 32.
Variable RNG : footprint.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RI : rng_aimg RNG.
#[using="rc SP16 ESPA"] Lemma spa_props : SP - 240 <= SPA <= SP - 224 /\ SPA mod 32 = 0 /\ (SP + -224) - (SP + -224) mod 32 = SPA.
Proof. rewrite ESPA. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>53663102416.6000000LS4SP161H2H02H42H52H93H103H14".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc LOS LOC SPT SP16 ESPA RSTK RI"] Lemma f_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
stk bsegs m lo SP -> mem_inv bsegs m ->
rt_got m -> rt_shbase m -> rw_cells bsegs m 0x99968 [C8 (Z_to_bv 64 0xa2540)] -> rw_cells bsegs m 0xa2540 [C4 (Z_to_bv 64 1)] ->
evtF bsegs RNG (fun ms' => exists m' ja,
ms' = MS (mkR (Z_to_bv 64 0x80d94) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 1792) (Z_to_bv 64 0xa2538) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 ASHOFF) s4 s5 s6 (Z_to_bv 64 SZ) (Z_to_bv 64 D) s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 ASM5_ENTRY) fc None m' (seg_rom bsegs)
/\ munch [(SP - 224, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\ rw_cells bsegs m' SPA [CB 120 ja]
/\ stk bsegs m' lo SPA /\ stk bsegs m' (SPA + 120) (SP + -104))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST MI GOT SHB GSU SUA. unfold AFUZZ_ENTRY, ASM5_ENTRY, AHARNESS_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
pose proof spa_props as (SPAB & SPA32 & ESPA').
assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
pose proof (munch_refl [(SP - 224, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
zstep.
Local Ltac2 Set LiaHints.tbl := fun () => "00k0>1162083372.70 1237157135.72 12472314755.7015555790503.7115799534863.6817776320428.7019347287719.7123787153319.7124559885228.7025825925031.7125878270252.7026498395174.6126966040451.7126994131331.7127408782895.7127528277671.7028360455555.7230898146691.7132922925600.6433890036524.7034103486887.7136115622447.7136960603523.7138205351847.7039101079207.723972147407.63 40091925677.6943059266230.5943621323318.6443631247668.6843987951407.714805334695.72 48634128287.7248773092266.6749801938227.7250498707654.6651370739587.7051398917112.6451678667181.6953695823155.6853767577772.7054264048862.7354933170051.7156963072324.6357081557379.7057307948253.7059230329255.7059308628179.656144403652.61 61917199021.6962839777246.7363152402819.7063235321901.6964318223524.6465598123907.7166240597415.7066964538243.7267859076775.7168343892476.6300000500600700800900>00?00@00E00F00K00P00Q00R00W00X00Y00Z00_00d00e00j00k00l00m01A01F01K01^02102602702802=02>02?02@02T02Y02Z02_02`02a02b02c02d02e02i02j02o03003103603703803903:03;03<S3LOSSSSSS3LOSSSS3LOSSS3LOSS3LOSSSS3LOSSSSS3LOSS3LOSSS3LOSSSSS3LOS3LOC3RSP1H4SPABS3LOSS3LOSS3LOS3LOC3SPT3RSP1HS3LOS3LOC3SPT3RSP1HS3LOSSSS3LOSSSSS3LOS3LOC3RSP1H4SPABS3LOSSS3LOSSSSSSSS2K0SS3LOSSSS3LOSSSSSSS".
carve_frame 104%nat ST. carve_frame 120%nat ST.
zstep.
do 13 zstep.
zstep.
zstep.
rewrite land_m32F by lia. rewrite ESPA'.
release_frame FR1 ST (SP + -104).
destruct (stk_split bsegs _ lo (SPA + 120) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
destruct (stk_carve bsegs _ lo (SPA + 120) 120 ST1 ltac:(cbn; lia)) as [STL [jA FRA0]]. clear ST1.
change (Z.of_nat 120) with 120 in STL, FRA0. replace (SPA + 120 - 120) with SPA in STL, FRA0 by lia.
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
rw_cells bsegs m SPA [CB 120 ja] -> rw_cells bsegs m F [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 FLG)] ->
rw_cells bsegs m (SHF F) FSH0 -> mem_inv bsegs m ->
rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)] -> rt_real_mem m ->
ablk F (F + 2048) -> F + 2048 <= ATOP -> F mod 2048 = 0 ->
rng RNG F 2048 -> rng RNG (shad F) 256 ->
evtF bsegs RNG (fun ms' => exists m' (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (jb jc jd : list byte),
ms' = MS (mkR (Z_to_bv 64 0x80ec0) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 D) (Z_to_bv 64 SZ) y12 y13 y14 y15 y16 y17
(Z_to_bv 64 18446744073709551602) (Z_to_bv 64 ASHOFF) s4 s5 (Z_to_bv 64 F)
(Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (SHF F)) (Z_to_bv 64 (SHF F + 76)) y28 y29 y30 y31)
FR (Z_to_bv 64 0x8269c) fc None m' (seg_rom bsegs)
/\ munch [(SPA, SPA + 120); (F, F + 24); (SHF F, SHF F + 256)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' SPA [CB 40 jb; C8 (Z_to_bv 64 F); CB 16 jc; C8 (Z_to_bv 64 (SHF F + 148)); CB 40 jd; C8 (Z_to_bv 64 F)]
/\ rw_cells bsegs m' F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x15f28); C8 (Z_to_bv 64 0x80d20); CB 2016 junk; C8 (Z_to_bv 64 FLG)]
/\ rw_cells bsegs m' (SHF F) (FSH F8S F8S F8S BF8 BF8))
(MS (mkR (Z_to_bv 64 0x80d94) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 F) x11 x12 x13 x14 x15 x16 x17
s2 (Z_to_bv 64 ASHOFF) s4 s5 s6 (Z_to_bv 64 SZ) (Z_to_bv 64 D) s9 s10 s11 x28 x29 x30 x31)
FR (Z_to_bv 64 0x80d94) fc None m (seg_rom bsegs)).
Proof.
intros until FLG. intros FRA FFC SH0 MI GOTM REALM FH FC F2048 RF RSF. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
unfold SHF, FSH0, FSH, AHARNESS_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND, KHIGH in *.
pose proof spa_props as (SPAB & SPA32 & _).
Local Ltac2 Set LiaHints.tbl := fun () => "01:0?1370123474.132 14549903878.88 14723231628.82 15926818576.87 19440193171.88 20572578573.11320674773453.11321316803565.12722004642717.11322683272109.11323568199473.13124522298490.96 25059262615.82 25349552462.72 25675713676.96 26918830103.96 28381205639.10829782367974.72 29782367974.73 30400065325.12732618034045.1273287162930.85  33849775066.10934957802317.12735495549846.11035495549846.82 35495549846.96 35594558829.85 35945580172.82 36282397981.12737622031638.95 37648604637.1133839306879.74  3873683853.99  41427975703.86 41624233714.13243496930236.81 4398706810.109 44032511117.12745114998679.11045362379101.12745386592662.12349236341453.85 49877423341.99 50565131421.85 50972187030.1095169965661.99  52124489789.99 53005185549.12754353223319.85 55119024813.12756041590284.10757197585530.12358504925064.86 58952161325.99 59314873579.79 60502248570.12460540020624.11861170003069.99 62376611962.11062536353548.96 63202992012.11063513965645.99 64843933213.99 66811069213.86 6854930828.110 7038263405.113 7673273466.95  7676635532.86  851546.88      8854610.78     89901372.95    9183238141.113 9293723057.117 00000500:00?00D00I00N00S00X00]00b00g00l01501:01?01H01Z01_01d01i01n02302802=02B02G02L02Q02Z02_02d02i03A03F03K03P03U03Z03_03h03m04204704<04A04F04K04P04U04Z04_05:05?05D05I05U05Z05_05d05i06206706<06A06F06O06T06Y06^06k07807=07B07GS3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH23BSFS2FH5F20481H2H02H9S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH2S3LOS3LOC3FH23RSP4SPAB1HS3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S3FH2S5F20483FH13FH31H2H02H93H24S3FH2S3FH2S3FH2S3FH13FH22K0S3FH2S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH2S3FH2S3FH23BSFS3FH2S3FH2S3FH2S3FH13FH23FH4S3FH13FH23FH4S3FH2S3FH2S3FH2".
replace (shad F) with (Z.shiftr F 3 + ASHOFF) in RSF by (unfold shad; lia).
assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 256 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
assert (SHDJ : F + 2048 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= F).
{ rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. unfold ablk, AIMG_HI, KLS in FH. Z.div_mod_to_equations. lia. }
assert (RFRA : rng RNG SPA 120) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof (munch_refl [(SPA, SPA + 120); (F, F + 24); (Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 256)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
zstep.
zstep.
zstep.
zstep. bcase K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia).
zstep.
do 7 zstep.
zstep. zstep. zstep.
zstep.
zstep.
replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr F 3 + ASHOFF) _ |- _ =>
pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
zstep. clear SOK. zstep. zstep. zstep.
zstep. zstep. zstep.
zstep.
lazymatch goal with SH : rw_cells bsegs _ (Z.shiftr F 3 + ASHOFF) _ |- _ => rw_split SH 4%nat SHa SHr end.
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
