(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AModelFacts APrimFacts ASecFacts F_aunwind F_aalloc_s F_acache F_aalloc1 F_aalloc1b.
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
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Section CANSEC1. Context {rc : runConstT}.
Definition allocA_pre_postS (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(n S t lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x3273c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 n)
(Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
(Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
t3 t4 t5 t6)
F (Z_to_bv 64 0x36930) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp - 128)
/\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
[CB 8 j0 ; C8 (Z_to_bv 64 1) ; C8 (Z_to_bv 64 16) ;
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
#[using="Type"] Lemma allocA_pre_spec_sec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
1 <= n <= AREQMAX -> is_primary n = false -> 0 < S < 2^64 ->
allocA_cells m ctx t ->
AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
(ctx + 4096 <= t \/ t + 4096 <= ctx) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
evtF asegs RNG (allocA_pre_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RSTK RCTX RT. band_lin.
destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, AREQMAX, allocate_entry in *.
Local Ltac2 Set LiaHints.tbl := fun () => "04I0?100583406.87   10345787758.91 1046777916.88  10475939182.87 10631675007.85 11077664131.87 1162083375.86  11801586693.10211801586693.93 11801586693.97 11805467289.85 11805467289.86 11805467289.87 11805467289.88 11805467289.91 11805467289.92 12279985372.86 12546622119.88 12691105774.88 12894873556.91 13078997820.85 13340275967.87 1351984962.90  14086840430.87 14377326446.87 14453557927.87 14869079534.91 14916922350.88 1533820803.87  1579170362.85  15813913888.90 16518423935.88 16598865212.88 16643491566.88 16872280319.87 17776320431.86 18748206397.10218748206397.93 18748206397.97 18821093870.87 19106585020.87 19491992743.88 20029295994.90 20092993006.85 20313996398.92 20805333024.82 20805333024.86 20805333024.94 21155567546.87 21456922734.87 21514303854.87 22163107130.88 22284289799.10222284289799.93 22284289799.97 22439364775.86 22607575996.92 22632813821.10222632813821.93 22632813821.97 22675801219.88 22700267513.10322700267513.94 22700267513.98 2327176814.87  24266362535.91 24336903790.88 24559885231.86 2458073255.87  24630998586.87 24794926247.88 24972240369.89 24982576641.90 25029166211.87 25067826030.87 25117511228.88 25348482085.82 25348482085.86 25348482085.94 25397754094.87 25483987182.87 25787632170.81 25787632170.90 25878270254.87 25898482559.88 26278908583.87 26669522158.88 26868428163.86 27408782894.87 27453056622.86 27507444718.88 27624344046.88 28355653425.91 28355726446.87 29076633087.87 29193796462.87 29782367974.91 29965292900.91 30196181434.87 30475395182.85 30518562691.87 31033748334.88 3106004334.87  31143001276.87 31298910190.88 3169312110.87  31694218478.85 32307613550.87 32431485806.87 32651489978.86 32799626990.91 33416350702.87 33532905180.82 33680001082.88 33890036527.86 34083973870.88 34173489134.88 34775537831.92 35101720189.10235101720189.93 35101720189.97 35270809255.87 35289778563.92 35492836974.87 35561507310.91 36115622446.87 36358165526.97 36367760551.87 36505554542.87 36635094629.95 37114577220.91 37153923388.88 37317216127.91 37612374638.88 38621033363.86 3888239342.88  38915808562.10238915808567.10538996969702.78 3936067822.85  39371731990.88 39813362070.92 39932040893.92 39938772488.10239938772490.10340091925676.85 40655079551.87 41788515822.88 42277915246.87 43061431595.76 43102492671.87 43183609788.87 43188973678.86 43987951406.87 44030539416.62 44158664835.88 44484923210.10244484923210.93 44484923210.97 44524995199.88 44833359747.87 45221239098.91 4560351804.91  46134254574.91 46232973498.87 46298727534.87 46481665774.87 46556098215.88 46595657582.87 47399076078.87 47813310082.10248057003647.88 48196668649.95 48989959150.87 49194402876.87 49425192486.94 49724318719.86 50317564526.92 50487304575.87 50584888647.82 50647975150.87 50693720814.88 51322024558.86 51323987107.73 51458250794.99 51469190682.90 51665594094.88 51678667183.86 52076332701.10052076332702.10052700297966.85 53262831086.88 53767577775.86 54261855034.88 54722921710.92 55222119100.87 55378305518.87 55442533998.86 56172400559.93 56172529599.85 56175235539.81 563227834.92   5662520302.88  56755583453.10256755583453.93 56755583453.97 5684463747.91  57144050542.86 57293592682.89 57508831501.91 57522549927.85 57745675194.87 57839090926.87 57884226286.88 58655119491.88 59314873579.81 59314873579.92 59314873579.93 59314873579.94 59314873579.96 5953130734.88  59576986246.93 59839360238.88 59907387523.88 60015718766.87 60468873383.87 60634079619.87 60686216330.80 60997568167.87 61230833468.87 6129476974.87  61628829678.87 61674577390.91 61889459015.86 61917199023.86 61929802144.91 61929802406.93 61939782290.10262691353710.87 62704248302.87 63045513727.92 63235321900.84 63401142510.85 63478620285.10263478620285.93 63478620285.97 63720710766.87 641441518.87   64302930659.80 64469993326.87 65518452462.88 65630542730.80 65805175866.88 65983638659.87 66028155702.85 66028155702.89 66028155702.97 66330498723.91 66423386478.87 67215858474.91 67258535356.86 68034022143.87 68096078318.87 68214575726.87 7057573564.87  7779942894.88  7848643581.102 7848643581.93  7848643581.97  7963185902.86  8179223683.85  8583720762.87  8595948976.103 8595948983.105 8684881006.92  8805124206.92  9074023790.88  9333008750.87  9381636462.92  9610135226.87  9745841262.87  00000900B00F00O00[00\00`01001@01P01Q01R01S01T01U01V01W01X01a01f01j02602702@02I02J02S02\02]02b02f03203603?03K03O03\03i04604?04C04D04E04N04W04X04Y04Z04_04h05105605705805905:05>05K05X05e05f06K07007U07^07_07h07l07m08208308408508608?08C08G08K08O08X08a08d08g08k09709809A09B09F09O09X09a09b09k0:70:@0:A0:D0:I0:R0:S0:\0:e0:i0;20;;0;D0;M0;V0;[0;d0;m0;n0<30<70<@0<I0<J0<W0<d0=10=20=30=<0=E0=I0=J0=K0=T0=g0=k0=o0>;0>D0>E0>N0>O0>P0>Q0>Z0>[0>\0>n0?80?F0?J0?V0?_0?h0?l0@80@<0@E0@I0@L0@M0@N0@O0@P0@\0@]0@b0@f0@o0A40A=0AF0AG0AP0AY0Ag0B30B40B=0BA0BE0BQ0BZ0Bf0Bg0C00C90CB0CC0CI0CO0CX0C\0C]0C^0Cg0D00D40D90DB0DF0DO0DX0DY0DZ0D[0D`0Di0E60EC0EP0EQ0EZ0E[0Ec0Ed0Ei0F20F;0F<0FC0FI0F_0Fe0G20G;0G<0GE0GF0GO0GP0GQ0GR0GS0GW0G`0Gi0H20H30H70H:0H=0H@0HI0HR0H^0Hb0Hk0I80IE0IR0I[0Id0Ih0J10J:0J;0J@0JA0JP0J_0Jn0K20K;0K<0K@0KL0KU0K^0Kb0Kk0L80LE0LR0L[0L\0La0Lb0Lc0Ll0M50M>0MG0MP0MU0M^S4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LO2C1SS2LOS3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1SSSSSSSSS4CEIL2LOS3NSES2HBS4CEIL2LO2C1SS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOSS3SPRS2LOS4CEIL2LO2C1S2HBS4CEIL2LOS4CEIL2LO2C1S2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS2HBSFS4CEIL2LOS4CEIL2LOFFFS3SPRS4CEIL2LOS4CEIL2LOS3SPRFFFSS2HBS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS4CEIL2LOSS4CEIL2LOS2LOSS3SPRSSSSS4CEIL2LOS2HBS2LOS2LOS2LOS4CEIL2LOS4CEIL2LOS1NS1NS2LOS4CEIL2LO2C1SS4CEIL2LOSS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOSS1NS3SPRS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSS3SPRS2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSSS4CEIL2LOS4CEIL2LOS2LOSSS4CEIL2LOS1N2HS2T02T13MSB2KSS2RZS2HBS4CEIL2LO2C1S4CEIL2LOFS4CEIL2LOSSSS4CEIL2LOSSS1N2NB3RSE3RSR3NSES3RL74RLR0S1N2NB3RSE3RSRS2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2LOS4CEIL2LO2C1S2HBS4CEIL2LOS2LOS1NSFFFS4CEIL2LO2C1SS3SPRS2HBS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS1N2NB3RSE3RSRS4CEIL2LO2C1FS4CEIL2LOS2HBS2C0S4CEIL2LO2C1S4CEIL2LOS4CEIL2LO2C1FS4CEIL2LOS4CEIL2LOS4CEIL2LOSS1N2NBS1N2NBS4CEIL2LOS2LOFFS4CEIL2LOS4CEIL2LOS2LOS3SPRS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSSS3SPRS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS4CEIL2LOSS2NB3RSRSS3SPRS4CEIL2LOS4CEIL2LOSS2HS2KSS1N2KBS1N3RSE3RSR3NSE3MSB2KCS1N2KDS2HS2T02KS2KES4CEIL2LOSS4CEIL2LOSS4CEIL2LOSSSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOFS2LOS1NS1NS1NS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1S2LOS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS2HSS4CEIL2LOS4CEIL2LOSS3SPRSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LOS4CEIL2LOSS2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOSS3SPRSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LO".
pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM0) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
pose proof (rz_log_big n NB) as RL7. assert (RLR0 : 0 <= rz_log n <= 7) by (rewrite RL7; lia).
pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
carve_frame 128%nat ST.
do 14 step.
do 6 step.
step. callp asan_inited_spec; [exact INI|]. step. if_lit.
step. callp rss_spec; [exact RSS|]. step. if_lit.
step. if_cases KS; zify_cond KS. { exfalso. lia. }
step. step. if_lit.
step. step. step. if_lit.
zstep. zstep. step. if_lit.
step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.
lstep. zstep. zstep. zstep.
step. step. if_lit.
step. zstep. zstep. step. if_lit.
step. zstep. step. step.
callp rz_ladder_spec; [lia|].
lstep. step. step. zstep. zstep.
step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
rename POST into ST.
step. lstep. step. zstep.
step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
rename POST into ST.
callp rz_clamp_spec; [lia| exact RLR0 |].
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
rewrite land_align8 by lia.
setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }
step. zstep.
replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
zstep. zstep.
first [rewrite (sllw_rz_gen2 n) | rewrite (sllw_rz_gen n)].
step. zstep.
zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].
zstep.
rewrite RZ.
zstep. zstep. zstep. zstep. step. zstep.
replace (rounded_size n + 2048 <? 65537) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
change (Z.land 1 0) with 0. change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
change (Z.land 18446744073709551615 2048) with 2048.
setreg 19 (Z_to_bv 64 (needed_size n)) ltac:(f_equal; lia). setreg 20 (Z_to_bv 64 (rz_size n)) ltac:(f_equal; lia).
step. if_cases KB; zify_cond KB. { exfalso. lia. }
step. if_cases KC; zify_cond KC. { exfalso. lia. }
step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }
box RT.
step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
unbox RT. rename POST into ST.
step. step. if_cases KE; zify_cond KE. { exfalso. lia. }
zstep. step. step. step.
step.
apply evtF_done. unfold allocA_pre_postS. do 12 eexists. split; [reflexivity|].
repeat lazymatch goal with |- _ /\ _ => split end.
all: try assumption. all: eexists; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
