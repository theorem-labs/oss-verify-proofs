(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 AKitQ F_afree_s F_aalloc3.
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
Local Ltac aload ST8 i AEXPR :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let RD := fresh "RD" in
pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
step; clear RD
end.
Local Ltac astore ST8 i :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let SOK := fresh "SOK" in
pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
step;
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
let S2 := fresh "STATS" in
pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
replace (A + 8 * i)%Z with E in S2 by lia;
clear ST8; store_done; try clear SOK; rename S2 into ST8
end
end.
Section CANSEC1. Context {rc : runConstT}.
Definition dealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t hm n S b1 actx lo : Z) (sj : list word) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x9eed8) (Z_to_bv 64 hm) (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 S)
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36310) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
/\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 18446744069414584320)]
/\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat.
#[using="Type"] Lemma dealloc_spec : forall (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n b1 actx ctx lo : Z) (uw : word) (sj : list word),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
mem_inv bsegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 (hm + 16) -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 1 ->
rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
AIMG_HI <= hm -> hm + 24 <= ATOP ->
rw_cells bsegs m AFHOOK [C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
(hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
evtF bsegs RNG (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S b1 actx lo sj m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3204c) fc None m (seg_rom bsegs)).
Proof.
intros until sj. intros ST CEIL LO MI TP -> -> -> HD UW B1 B13 N AL H0 H1 HK TI TK T88 TSD CT CX0 C0 C1 T0 T1 STATS LSJ DHT DHC CT2 RIMG RSTK RCTX RT RH. band_lin.
unfold AIMG_HI, AINSTANCE, ATSDI, ATSDK, ATP88, ATSD, AFHOOK in *.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
word_range sp SPR.
do 4 step. zstep. do 5 step.
Local Ltac2 Set LiaHints.tbl := fun () => "04>0?10829118253.87 11118462589.92 11118462589.94 11601497306.92 11801586693.92 11801586693.94 11912744615.91 12367362435.91 12367362435.94 12596293756.99 12596293757.98 12596293758.97 12598390902.95 12614152141.87 12876582062.91 13021749692.91 13205419683.91 13205419683.93 13464694894.91 13596006226.91 13596006226.93 13629548202.87 13696072622.91 14308723042.87 15060057555.85 15151140912.87 1527479463.89  15321391905.86 15321888238.94 15323985382.96 15328766942.85 15582139502.89 15835335440.86 1586831214.92  16209163890.87 16307494931.91 16856831405.87 16872280319.91 17212185306.92 17506121710.92 17646078182.82 17755388179.93 17776320431.90 17776320431.93 18074052718.91 18376621181.87 18944006493.96 19049469500.92 19596407918.91 19750732782.92 19825051012.89 19882618009.86 19939579681.86 20851542163.89 20921468142.89 21064248558.89 21918414723.91 21918414723.94 21969407398.86 22001867636.99 22700267513.93 22700267513.95 22981277779.86 23206405539.87 23371224676.85 23480589001.86 23589365338.91 23718989810.87 24232371904.87 24254708740.97 24630998586.89 25314760359.92 25380058738.87 2582348142.91  25878270254.91 25878270254.94 26073886434.87 26274742996.99 27576757255.92 27576757255.94 27841752864.87 27923971379.91 28260465738.86 28344324846.92 28487105262.92 28754851922.91 28754851922.93 29510632509.87 29545175216.91 29782367974.85 29782367974.87 29950340078.92 301132402.87   30299521578.85 30597119136.87 30717345253.93 30985181748.88 30985181748.89 31076427667.92 31081687356.92 31310932627.92 31423336146.91 31423336146.93 32186460580.85 32651489978.91 32805605483.10233039531175.92 33227529838.91 33680001082.92 34293603954.87 34356250836.89 34457081818.89 35340120754.97 35693303086.89 36115622446.91 36115622446.94 36436153477.86 36646331050.87 36814730237.92 36814730237.94 36829960868.86 36993589379.92 36993589379.95 37107179452.91 37317216127.92 37364793838.92 37436222938.92 3807747055.98  38211171107.87 38590847986.87 3875130862.92  39235284912.87 3945979267.91  3945979267.94  39482238446.91 40472941298.87 40655079551.89 40778537633.86 40818989526.87 41809558659.89 41809558659.93 42160315412.10642831019478.91 42831019478.93 43060403331.92 43060403331.95 43061431595.80 43495041504.98 43495041505.97 43495041510.1004367084307.91  43941322990.92 43987951406.91 43987951406.94 44305789522.91 44305789522.93 44308094241.86 44484923210.92 44484923210.94 45065545733.87 45065545733.88 45221239098.92 45672096911.91 45672096911.93 45713281902.91 46051971694.91 46058767598.91 47402546926.89 47595661179.97 47747814717.92 47747814717.94 48057003647.92 48330303854.91 49097393336.86 49345641752.85 49425192486.86 49671508435.85 49671508435.86 49724318719.91 4972971506.87  50131772669.87 50354202374.91 50354202374.93 50487304575.92 50655895377.86 5092088214.89  51159913016.86 51359989486.89 51425718543.91 51425718543.94 51481786499.92 51481786499.95 51633495293.92 51633495293.94 51678667183.90 51678667183.93 51877860133.85 51877860133.86 51905078894.91 52230632470.87 52567164907.86 52567164907.89 52567164907.91 52567164907.92 52567164907.93 52575291859.87 52931696866.84 53460783854.91 53634055457.86 53767577775.90 53767577775.93 55031195310.91 55602792399.85 55602792399.86 55707291962.95 56062130284.85 56172410267.84 56172560690.85 56187338226.87 56228262055.91 563227834.91   56323790752.92 56323790752.94 56324080430.92 56729251374.92 57068160275.91 57745675194.91 58995781614.92 59134147250.91 59285968488.92 59311160430.91 59314873579.85 59743357778.91 59743357778.93 60025031335.92 60223348125.93 60492306926.92 60530428530.87 6062692974.91  60708418864.87 60723900404.10061214533978.91 61415267707.10061454936069.87 61454936069.88 61534126184.92 61669289758.97 61917199023.90 61917199023.93 61939782290.98 62575797294.92 62891835758.92 63045513727.91 63235321900.88 63235321900.92 63694018620.92 64352634714.91 65016030589.92 65016030589.94 66149329545.99 66410366446.92 6652598510.92  67800801447.91 68205640558.91 7010956092.89  7754842205.93  8163491438.92  8583720762.92  9151284627.92  985337532.91   00000800E00R00^01801R01S01T01U01Y01]01a01e01j02602:02F02O02X02a02e02f03203;03<03@03A03E03L03S03\03e03i04204:04J04R04^04j05305405505905=05F05R05W05[05d05m05n05o06306C06L06U06V06W06[07@08108b08c08l08m09109=09E09F09G09L09M09U09^09b09f09o0:40:50:60:?0:@0:D0:M0:V0:_0:c0:h0:l0:m0:n0;70;?0;@0;I0;J0;Y0;h0<80<<0<L0<U0<Y0<Z0<_0<`0<a0<j0<o0=70=80=D0=E0=Q0=U0=Y0=]0=`0=m0>:0>C0>D0>E0>I0>U0>^0>j0>k0?40?<0?E0?I0?J0?K0?T0?\0?h0?l0?m0?n0?o0@X0@]0@a0@b0@c0@g0@h0@i0@j0A:0AC0AG0AK0AT0AX0A\0A]0A^0Ac0Ah0Am0B=0BW0B`0Bi0C20C;0C@0CM0CZ0Cf0Co0D;0D<0DA0DB0DC0DO0DW0Dc0Do0E00E<0E@0EA0E[0Ed0Ee0Ef0Eg0Eh0F50FB0FF0FJ0FN0FR0F[0F\0F]0F^0F_0F`0Fa0Fb0Fi0G20G60G:0G>0GJ0GN0GR0GS0GT0GU0GV0G^0G_0Gd0H40HD0HP0H\0Hl0I10I:0IF0IG0IP0IW0I`0Id0Ie0J10J:0JB0JK0JL0JM0JY0J^0Jc0Jh0Ji0Jm0K10K50K80KD0KM0KY0K]0Ka0Ke0L10L>0LK0M00M90MB0MC0ML0MP0MT0M]0Mb0N20N6S2T03LSJS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2H1S3Hsp4CEIL2LO2C12H12T13LSJS4CEIL2LO2H13Hsp2C12T13LSJSSSS2B1S2B1S2B1S2B1S3LSJS4CEIL2LO2H1S2HBS4CEIL2LO2C1S3LSJ3DHCS4CEIL2LOS4CEIL2LOS2H0SS4CEIL2LO2H1S3LSJ3DHTSS2T1SS2H0S2H02H1S2H02H1S2H02H11HS4CEIL2LOS2B1S4CEIL2LOS2T03LSJS4CEIL2LO2T13LSJS2T03LSJS4CEIL2LO2C1S4CEIL2LO2H1S4CEIL2LOSSS2LOS2LOS4CEIL2LOS4CEIL2LO2T1S3LSJS2HBS4CEIL2LOS4CEIL2LOSSS2H0S4CEIL2LO2T13LSJS4CEIL2LOS4CEIL2LOSSS2B1S2AL2H02C03LSJ3DHT3DHC3CT22K01H2H22H6S4CEIL2LO2H02H12C02C12T13LSJ3DHT3DHC3CT22K03Hsp1HS4CEIL2LO2H02H12C02C12T13LSJ3DHT3DHC3CT22K03Hsp1HSS3LSJ3CT2SS2HBS4CEIL2LO2H1S2T03LSJSSS3SPRSS2T03LSJS4CEIL2LOS2LOS2LOS3LSJ3DHTS3LSJFFS3LSJ3DHTSS2H0S4CEIL2LOS4CEIL2LOS4CEIL2LOS2H0S3LSJS2HBSSS4CEIL2LOS2T03LSJSS3LSJ3DHTSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO2T13LSJS2HBS4CEIL2LO2T13LSJS4CEIL2LOS2H0SS3SPRSSS4CEIL2LOS3SPRS2T03LSJSS4CEIL2LO2H1SS4CEIL2LO2H1S2LOS2LOS2LOS1NS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ3DHCSSS2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LO2H1SS3LSJ3CT2S2T03LSJS4CEIL2LOS2T1SSS4CEIL2LOS2T03LSJS4CEIL2LO2C1S2H0SSSS2AL2H02C03LSJ3DHT3DHC3CT22K01H2H22H63H11S3SPRS2HBSSS2LOFFFS4CEIL2LO2T13LSJS4CEIL2LOS2LOS2LOS4CEIL2LOS2H0S2H0FFS3LSJS3LSJS3SPRS4CEIL2LO2T13LSJS2H02C03LSJ3DHT3DHC3CT22K0S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3LSJS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2C1S4CEIL2LOS4CEIL2LO2H1SS3CX0SSS4CEIL2LO2C1S2T03LSJS4CEIL2LO2T1S4CEIL2LO2H1SS4CEIL2LO2C1S2B1SS2H02C03LSJ3DHT3DHC3CT22K0S4CEIL2LOSSSSS4CEIL2LO3HspS4CEIL2LO3HspS2LOS2LOS2LOS2LOS4CEIL2LOSSSSSSSS2H02H1S4CEIL2LOS2H0S2LOS2LOS4CEIL2LO2H1S2B1S2B1SSSSS2T03LSJSS3SPRS4CEIL2LO2H13HspS4CEIL2LO2H13HspS4CEIL2LO2H1S4CEIL2LO2H1S4CEIL2LO2T13LSJS3SPRS4CEIL2LOS4CEIL2LO2H1SS4CEIL2LOS2H02K0S4CEIL2LOS2H0SS4CEIL2LO2H1S4CEIL2LOS2T03LSJS4CEIL2LOSSS4CEIL2LO2H1S3LSJS3LSJS3LSJSS2B1S2LOS2LOS1NS4CEIL2LO2H1S4CEIL2LOS4CEIL2LO2C1S2LOS2LOS2HBS4CEIL2LO2H1S4CEIL2LO3HspS4CEIL2LO3HspS2AL2H02C03LSJ3DHT3DHC3CT22K01H2H22H6S4CEIL2LOS4CEIL2LOSS4CEIL2LOS2HBS2H0S4CEIL2LOS3SPRS4CEIL2LO2T13LSJS2HB".
carve_frame 64%nat ST.
do 9 step.
step. if_cases K0; zify_cond K0; [exfalso; lia|].
do 6 step. zstep. step.
replace (hm + 16 + -16) with hm by lia.
box RT. box RCTX. box RH.
step. call_sp run_free_hooks_spec; [exact ST| exact CEIL| lia| exact MI| exact HK| solve_rng|].
unbox RT. unbox RCTX. unbox RH. rename POST into ST. try rename MI0 into MI.
step. if_lit.
zstep. zstep. step. step. step.
change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by lia.
replace (hm - hm mod 2 ^ 2) with hm by (Z.div_mod_to_equations; lia).
zstep. zstep. zstep.
replace ((Z.shiftl hm 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3. change (bv_swrap 32 (Z.shiftl 2 0)) with 2.
apply (rw_hdr_to_C4 _ _ 2 b1 _ ltac:(lia) ltac:(lia)) in HD.
assert (AMO : amo_aligned AW (Z_to_bv 64 hm) = true) by (apply amo_alignedW_intro; [lia| Z.div_mod_to_equations; lia]).
amo_stepA AMO. rewrite sx32_lit by lia.
zstep. rewrite (byte0_of_word 2 b1) by lia.
step. if_lit.
zstep. zstep. zstep.
rewrite (byte0_cas 2 3 b1) by lia.
amo_stepA AMO.
step. if_lit.
apply (rw_C4_to_hdr _ _ 3 b1 _ ltac:(lia) ltac:(lia)) in HD.
step. zstep. step.
lstep. zstep. rewrite B13.
step. if_lit.
zstep. step. step. if_lit.
box RT. box RH.
step. call_sp thread_stats_spec;
[exact ST| exact CEIL| lia| exact MI| exact TP| exact TI| exact TK| exact T88| exact TSD| exact CT| lia| exact C1| exact T0| exact T1| solve_rng|].
unbox RT. unbox RH. rename POST into ST. try rename MI0 into MI.
lstep. lstep.
aload STATS 4 (t + 2800 + 32).
aload STATS 3 (t + 2800 + 24).
zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.
astore STATS 3.
astore STATS 4.
step. step. step. step.
do 10 step.
release_frame FR ST (bv_unsigned sp).
unfold dealloc_post. finish.
- exact STATS.
- rewrite !upd_length. exact LSJ.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
