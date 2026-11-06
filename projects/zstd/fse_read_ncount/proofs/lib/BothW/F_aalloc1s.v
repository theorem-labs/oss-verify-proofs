(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AModelFacts APrimFacts ASecFacts F_aunwind F_aalloc_s F_acache F_aalloc1 F_aalloc1b.
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
ms' = MS (mkR (Z_to_bv 64 0x32628) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 n)
(Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
(Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
t3 t4 t5 t6)
F (Z_to_bv 64 0x3681c) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp - 128)
/\ (exists j0, rw_cells bsegs m' (bv_unsigned sp - 128)
[CB 8 j0 ; C8 (Z_to_bv 64 1) ; C8 (Z_to_bv 64 16) ;
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
#[using="Type"] Lemma allocA_pre_spec_sec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n S ctx t lo : Z),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
mem_inv bsegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
1 <= n <= AREQMAX -> is_primary n = false -> 0 < S < 2^64 ->
allocA_cells m ctx t ->
AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
(ctx + 4096 <= t \/ t + 4096 <= ctx) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
evtF bsegs RNG (allocA_pre_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros ST CEIL LO MI TP -> -> -> -> -> -> N PRIM0 HS AC C0 C1 T0 T1 TAL CT2 RIMG RSTK RCTX RT. band_lin.
destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, AREQMAX, allocate_entry in *.
Local Ltac2 Set LiaHints.tbl := fun () => "04I0?10444057070.88 1046777916.88  10631675007.85 10894115438.86 11077664131.87 11118462589.10211118462589.93 11118462589.97 11277016046.88 1162083375.86  11801586693.10211801586693.93 11801586693.97 11805467289.85 11805467289.86 11805467289.87 11805467289.88 11805467289.91 11805467289.92 12279346798.87 12279985372.86 12546622119.88 12894873556.91 13078997820.85 13340275967.87 13464694894.86 1351984962.90  14453557927.87 14855983342.85 14884341230.88 15125481454.88 15258029550.85 1533820803.87  15348102510.87 15582139502.87 1579170362.85  15813913888.90 1586831214.87  16518423935.88 16598865212.88 16716288878.86 16872280319.87 17110785646.87 17242938350.87 17316385814.92 17506121710.87 17776320431.86 1845947246.87  18500769902.92 18691469806.88 18736735982.88 19106585020.87 19491992743.88 19596407918.92 19693800558.87 20805333024.82 20805333024.86 20805333024.94 20921468142.87 21064248558.87 21155567546.87 21834689774.88 21875103086.87 22163107130.88 22257987310.88 22284289799.10222284289799.93 22284289799.97 22375190282.80 22439364775.86 22548340206.88 22607575996.92 22675801219.88 22700267513.10322700267513.94 22700267513.98 22749971310.87 24118290798.92 24266362535.91 24559885231.86 2458073255.87  24630998586.87 24649134574.87 24794926247.88 24972240369.89 24982576641.90 25029166211.87 25117511228.88 25348482085.82 25348482085.86 25348482085.94 25787632170.81 25787632170.90 2582348142.87  25878270254.87 25898482559.88 26278908583.87 26868428163.86 27408782894.87 27948459987.86 28091621742.87 28344324846.88 28355653425.91 28487105262.88 29076633087.87 29124869358.88 29717588462.91 29782367974.91 29950340078.91 29965292900.91 30196181434.87 3042055150.88  30518562691.87 31143001276.87 31225663726.87 32651489978.86 33227529838.86 33532905180.82 33680001082.88 33693509870.85 33890036527.86 33951461782.88 34775537831.92 3517109230.87  35270809255.87 35289778563.92 36115622446.87 36367760551.87 36526869230.85 36635094629.95 3676042350.87  36814730237.10236814730237.93 36814730237.97 37114577220.91 37153923388.88 37317216127.91 37364793838.87 37833896558.87 38644313838.87 3875130862.91  38915808562.10238915808567.10538943022446.87 38996969702.78 3903501038.88  39482238446.87 39932040893.92 399383918.88   39938772488.10239938772490.10340091925676.85 40655079551.87 41099708142.88 41509391145.95 43061431595.76 43102492671.87 43183609788.87 433314286.87   43941322990.88 43987951406.87 44030539416.62 44158664835.88 44484923210.10244484923210.93 44484923210.97 44524995199.88 44833359747.87 45221239098.91 45519551598.87 4560351804.91  45999555182.87 46058767598.92 46082213742.87 46232973498.87 46432969966.85 46556098215.88 47747814717.10247747814717.93 47747814717.97 47813310082.10247916200342.97 48057003647.88 48330303854.87 49194402876.87 49425192486.94 49724318719.86 50487304575.87 50584888647.82 51323987107.73 51359989486.87 51394908602.90 51458250794.99 51469190682.90 51633495293.10251633495293.93 51633495293.97 51678667183.86 51905078894.86 52076332701.10052076332702.10052658742894.87 53405636718.87 53460783854.86 53767577775.86 54247907805.10254247907805.93 54247907805.97 5424914542.87  54261855034.88 54277570414.87 55222119100.87 55489964910.88 55786576878.88 56172400559.93 56172529599.85 56175235539.81 563227834.92   5684463747.91  5702686574.87  57293592682.89 57411727342.88 57508831501.91 57522549927.85 57745675194.87 58655119491.88 58995781614.87 59311160430.92 59314873579.81 59314873579.92 59314873579.93 59314873579.94 59314873579.96 59576986246.93 59907387523.88 60468873383.87 6062692974.92  60634079619.87 60997568167.87 61230833468.87 61257697518.87 61889459015.86 61917199023.86 61929802144.91 61929802406.93 61939782290.10262013585390.88 62066494062.88 62363106030.88 62891835758.91 63045513727.92 63163424110.87 63235321900.84 64302930659.80 65805175866.88 65983638659.87 66028155702.85 66028155702.89 66028155702.97 66330498723.91 66410366446.91 66729806446.87 67003513198.87 67215858474.91 67258535356.86 68034022143.87 68048062218.80 68205640558.87 68590114542.91 7009843438.87  7057573564.87  748888174.85   7987546237.102 7987546237.93  7987546237.97  8163491438.88  8179223683.85  8583720762.87  8595948976.103 8595948983.105 9610135226.87  00000900=00I00R00S00`00m01:01C01G01W01g02702802902:02;02<02=02F02G02H02M02Q02]02f02g02h03103:03C03L03M03V03_03d03h04104=04A04J04V04_04h04i05205605?05H05Q05Z05^05_05h06106206306406=06F06K06T06]06b06k06l06m06n06o07007907=07>07c08H08m09609?09@09D09E09J09S09T09U09V09W09[09_09c09g09j09m0:60::0:F0:G0:H0:L0:M0:V0:_0:`0:i0;50;>0;G0;H0;Q0;T0;Y0;b0;c0;g0<00<50<>0<?0<D0<M0<Q0<R0<S0<\0<]0<^0<b0<c0<l0=?0=H0=U0=b0=o0>30>70>C0>L0>U0>^0>g0>h0>i0?20?30?<0?E0?W0?`0?j0@80@<0@H0@Q0@R0@V0@b0@f0@o0A80A<0A?0A@0AA0AB0AC0AO0AP0AU0A^0Ab0Ak0B40B=0BB0BK0BL0BY0Bf0C30CA0CB0CN0CW0C[0C_0Ck0D70D80D90DB0DC0DI0DO0D\0Di0E60E:0EC0ED0EE0EN0EW0E`0Ed0F10F>0FK0FT0FY0Fb0Ff0Fo0G80G90G:0G;0G@0GA0GJ0GK0GT0G\0G]0Gb0Gc0Gl0H50H<0HB0HX0H^0Hk0Hl0Hm0Hn0I70I80I90I=0IF0IG0IK0IN0IQ0IT0I]0If0Io0J80JD0JM0JQ0JU0JZ0J[0Jj0K90KH0KL0KU0K^0Kg0Kh0Kl0L80L90LB0LK0LT0LX0La0Ln0M;0MH0MQ0MR0MW0MX0MY0M^S4CEIL2LOS2HBS4CEIL2LO2C1S4CEIL2LOSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS2LOS3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1S3Hsp4CEIL2LO2C1SSSSSSS4CEIL2LOSSS3NSES2HBS4CEIL2LO2C1S4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS3SPRS2LOS4CEIL2LOS4CEIL2LO2C1S2HBS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOSS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBSS4CEIL2LOS4CEIL2LOFFFS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOFFFSSS4CEIL2LOS2HBSS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS1N2HS2C02T03RSE3NSE3MSE3MSB2KS3Hsp1HS4CEIL2LOS4CEIL2LOSS2LOSS3SPRS4CEIL2LOSSSSS2HBS2LOS2LOS2LOS1NS1NS4CEIL2LOS2LOS4CEIL2LO2C1SSS2LOFS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOSS4CEIL2LOS1NS3SPRS4CEIL2LOSS2HBS4CEIL2LOS3SPRS4CEIL2LOSS3SPRS4CEIL2LOS2LOSSS4CEIL2LOSSS2LOSS4CEIL2LOS1N2HS2T02T13MSB2KSS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2RZS2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LOSS4CEIL2LOS4CEIL2LOS1N2NB3RSE3RSR3NSES4CEIL2LOS3RL74RLR0S1N2NB3RSE3RSRS2LOS4CEIL2LO2C1S4CEIL2LOFS2LOS4CEIL2LO2C1S2HBS4CEIL2LOS4CEIL2LOS2LOS1NSFFFS4CEIL2LO2C1SS3SPRS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS1N2NB3RSE3RSRSS4CEIL2LO2C1S4CEIL2LOS2HBS2C0S4CEIL2LO2C1S4CEIL2LO2C1FSS4CEIL2LOFS1N2NBS1N2NBS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2LOS4CEIL2LOFFS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS3SPRS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSSS3SPRSS4CEIL2LOSS4CEIL2LOS2NB3RSRSS3SPRSS4CEIL2LOS4CEIL2LOS2HS2KSS1N2KBS1N3RSE3RSR3NSE3MSB2KCS1N2KDS2HS2T02KS2KESSSS4CEIL2LOSSS2HBS4CEIL2LOFS2LOS1NS1NS1NS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS2LOS2HSS3SPRSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS2HBS4CEIL2LO2C1SS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOSS3SPRSSS3SPR".
pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM0) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
pose proof (rz_log_big n NB) as RL7. assert (RLR0 : 0 <= rz_log n <= 7) by (rewrite RL7; lia).
pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
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
