(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 ABytes AModelFacts APrimFacts ASecFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2 F_aalloc3g.
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
pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
step; clear RD
end.
Local Ltac astore ST8 i :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let SOK := fresh "SOK" in
pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
step;
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
let S2 := fresh "STATS" in
pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
replace (A + 8 * i)%Z with E in S2 by lia;
clear ST8; store_done; try clear SOK; rename S2 into ST8
end
end.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma allocD_sec : forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
(n t AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
(fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0x s6x s9x t3 t4 t5 t6 : word),
stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
1 <= n <= AREQMAX -> is_primary n = false ->
UB = AB + rz_size n -> ablk AB (UB + n) -> UB + n <= ATOP -> AB mod 16 = 0 ->
(t + 4096 <= AB \/ UB + n <= t) ->
rw_cells asegs m (bv_unsigned sp + -128)
[CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
rw_cells asegs m 0xa1ce0 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xa1ce4 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
rw_cells asegs m 0x9fca4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
rw_cells asegs m 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)] ->
rw_cells asegs m 0x997a0 [C8 (Z_to_bv 64 0x9b5e8)] ->
rw_cells asegs m 0x9b5e0 [C8 (Z_to_bv 64 0x92ab0); C8 (Z_to_bv 64 0x92eb4)] ->
rw_cells asegs m 0x9a3d8 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x5d5420 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m 0x133f40 [C8 (Z_to_bv 64 0)] ->
rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
0 <= b1m < 256 -> 0 < id < 2^31 ->
(16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
evtF asegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
(MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
s0x (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
(Z_to_bv 64 S) (Z_to_bv 64 0) s9x (Z_to_bv 64 t) (Z_to_bv 64 1)
t3 t4 t5 t6)
F (Z_to_bv 64 0x329e8) fc None m (seg_rom asegs)).
Proof.
intros until t6.
intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.
pose proof (ablk_lin _ _ ABLO) as (AL1 & AL2 & AL3 & AL4).
unfold AIMG_HI, ATP88, ATSD, AREQMAX in *.
Local Ltac2 Set LiaHints.tbl := fun () => "04i0?10028172029.12510028172029.14710167497279.14710456434697.1501047820382.117 10587903613.11810640816421.11910640816421.12010911084698.13711077664131.14711462352626.1181162083375.146 11801586693.12511801586693.14712308886460.14512341586989.11812373220886.14212406238321.14612560013042.11812571053298.11913086827028.13113118011600.1181324746171.148 13496907890.119137287794.119  13982882546.11914208485765.11814208485765.1191428302706.118 14335039570.1461454307978.137 1503082802.148 15043033658.11915051124456.15015077021426.1181533820803.147 15588165249.12115588165249.1381561637052.145 15636037571.14015813913903.12515924740850.11816200246386.11916210300264.15016263107213.14516398988797.11916482458097.13716703780397.1191740683122.118 17776320431.14617986879152.11717986879152.13818048262588.14518504928616.15018748206397.12518748206397.14719123199200.14719125296363.1481937063194.117 19372886979.14020609531986.14620880379370.14621250035837.12521250035837.14721355937650.1182150086885.146 2172922258.145 21857976067.14021873284733.12521873284733.14721924557829.11821924557829.11922026868477.12522026868477.14722632813821.12522632813821.14722675801219.14822700267513.12622700267513.14222700267513.1482310074925.119 23586406368.12124132108530.11924205896189.12524205896189.14724559885231.14624904914272.11824924589988.13124984467862.1212499582526.137 25029166211.14725065190167.12025071629079.13725071629079.14625080282415.11825080282415.11925162821874.11925195294056.1502521654632.150 25787632170.12125878270254.14726494647592.13726494647592.14526494647592.14626494647592.15026496924968.14026734967870.13726778510268.14526868428163.14626879533652.13026879533652.13126915800965.11926915800965.12027188338533.12127251872635.13227408782894.14727576757255.12527576757255.14727726645424.11927730847314.14628738030430.13728767007858.11929983937266.1183017725367.150 30233406450.11830507153671.13630518562691.14630719730331.12230719730331.13730876703602.11831218985776.11831407249106.14631498151784.15032377474162.11832460888562.1193289508284.145 33333358812.12933542888562.11933558212378.14633722085182.13733765134616.13833890036527.14634170950174.13735101720189.12535101720189.14735148913011.15035933558651.13236033352946.11836115622446.14736254216601.14836254216601.14937031786322.14637283284082.11937386977061.11737386977061.13837429491794.14637585159586.14537763307450.14937774388668.14538074103656.15038163290814.13738168113982.1373894281273.119 39407463154.13739771339708.14539932046344.11839938772490.13240091925676.14540326235777.12040978330866.11941422282358.11942389998958.15042445826608.11842445826608.1194258490819.140 42817532658.11842831019478.14642967766376.15043059454659.14043082390590.13743987951406.14743995329413.14544030539416.10244158664835.14844311304733.11944395637586.14644484923210.12544484923210.14744602107843.14044767421808.14544824048191.14744833359747.14745288596498.12245299829152.11945331600228.13245451326843.13245666356082.11845944259164.11945962238104.13046019491907.14046501843261.12546501843261.14746625963587.14047089684979.14047089684979.14147557849085.1184798910125.118 48616173652.13149294572020.1204936038867.141 49433673850.13749433673979.13649578074883.14049793197630.13749801462716.14550362574674.14650457931440.11850461111123.12250582100210.11850689918696.15050750500979.11950893982834.11951237798386.11951518379250.11951678667180.1455173701827.140 51816630506.13751868145084.14552357022834.11852567164907.13752567164907.14552567164907.14652567164907.15052575291859.11852575291859.11952586760667.14552682867945.13752987902756.1205300105810.146 53442040214.13753532296636.14553693616498.11853767577775.14653938471742.13754078910070.13054129336050.11854636957394.14654753862002.11854761860978.11854969794426.11755110451570.11855460634391.14556091204670.13756170256219.11956172415395.1375684463747.126 5691754054.119 56993309444.13957196545107.12257751108064.14457785628402.11957821142078.13758505212776.15058655119491.14859276314076.12159308628566.6  59308628695.6  59314873579.11959887912515.14059907387523.1486010284381.119 60235800116.12160634079619.14660666532082.11961597347058.11961694112329.14161875611762.11861917199020.14561939782288.13262976134100.13062976134100.1316313882541.118 6313882541.119 63235321900.14563670697722.14463745434493.11863974833010.11865485175549.12565485175549.14765797088788.12265983638659.14766028155702.12066028155702.14166357861087.1466653728088.140 66701037743.1306758013062.119 68049033064.15068309604434.1467070580924.145 7628953458.118 7780899791.145 7848643581.125 7848643581.147 7882758244.150 8179223683.146 8664102002.118 896064190.137  908653554.118  917434854.146  9196977948.123 9666466205.146 9729791282.137 00000=00M00i00m01201>01C01H01I01J01V01Z02202F02K02W02X02Y02e03103203303403@03L03X03]03b03n04>04?04@04A04F04R04S05E05]05b06206606B06N06S06W06c06i06n07:07>07D07J07O07T07a08108408708;08K08[08\08i09909E09F09I09Y09f0:60:;0:@0:M0:]0:j0;:0;;0<60<m0=m0>90>:0>F0>S0>c0>g0>h0>i0>j0?:0?;0@50@80@;0@<0@=0@I0@N0@S0@V0@Z0@]0@^0@a0@b0Ae0B50B:0B;0B<0BA0BF0BK0BO0BT0BX0BY0BZ0B^0Bn0C30C?0CK0CP0C\0D00D10D50D90DE0DI0DY0D^0Dj0E60E;0E@0EL0EP0E`0Ea0Ee0Ei0F60FF0F^0Fc0Fo0G30G40G50GE0GQ0GU0GY0Gi0Gm0Gn0H30H80HH0HX0H]0I10I60IH0IZ0I^0J[0Jg0Jh0Jl0K00K40KD0KP0KT0KY0Ki0L90L=0L>0LA0LB0LG0LW0LX0LY0Li0Lm0MC0MD0MH0MI0MJ0MO0M[0M\0M]0Mm0N:0NJ0NZ0Nj0Nk0O70OC0OH0OI0OJ0O^0P20PB0PR0PW0Pg0Pk0Q50QA0QF0QG0QS0Q_0Qk0Qo0R?0RC0RH0RT0RW0RX0R[0R\0R]0R^0Rc0S30S40SD0SE0SJ0SV0SZ0Sj0Sk0T70TG0TS0T_0Td0U00UH0UX0U]0U^0U_0U`0Ud0Ue0Uj0V60VF0VK0VL0VM0VY0Ve0W40WD0WE0WJ0WK0WL0WX0Wd0We0X10X50X80X90X>0XJ0XV0XZ0X[0Xg0Y30Y@0YP0Y]0Y^0Ym0Z?0Z@0ZM0ZR0ZS0ZX0Zh0Zm0[90[:0[G0[W0[[0[\0[h0\80\D0\E0\F0\V0\WS4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO3HUB3AL32NB3RZ23HspS2K4S3CX1S4CEIL2LO2T1S3LSJS3LSJSSS3LSJ2T03AL2S2LOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO3AL32NB3HspS3AL1S3LSJ2T03AL2SSS3LSJ2T03AL2S3LSJ2T03AL2SSSS3LSJ2T03AL2S3LSJ2T03AL2S3LSJ2T03AL2S3LSJS3LSJS3LSJ2T03AL2S3HUB3AL12NB3RZ2SSSS3AL1S3LSJ2T03AL2SS4CEIL2LO1N3HUB3LSJ3AL13AL23AL32NB3RZ23MSB2K02DX1HS4CEIL2LO3HUB3AL32NB3RZ2S3AL1S3HUB3AL12NB3RZ2S2LOS3LSJ2T03AL2S3LSJ2T03AL2S3AL1S2K4S4CEIL2LO2T1S1N2NBS3LSJS3LSJ2T03AL2S2LOS4CEILS4CEILS3AL1S3AL1S4CEIL2LO3HspS4CEIL2LO2NB3HspS1NS1NS2T1S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2SS4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2SS1NS3HUB3AL12NB3RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJS3LSJS4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO3HspS4CEIL2LO2NB3HspSS4CEIL2LO1N3LSJ2T13AL23RSE3NSE3MSE3MSB3Hsp1H3HUB3AL32NB3RZ2S4CEIL2LO1N3LSJ3AL23AL32NB3RSE3NSE3MSB2K01H3HUB3RZ23AL1S4CEIL2LO1N3HUB3LSJ3AL23AL32NB3RZ23RSE3NSE3MSB2K02K32K43Hsp1H2T1S3LSJ2T03AL2SS3LSJ2T03AL2S4CEIL2LO3HspS4CEIL2LO2NB3HspS2LOSSSS3HUB3AL12NB3RZ2SS4CEIL2LO1N3HUB3LSJ3AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02DX1HS1NS1NSSS3LSJ2T03AL2S3AL1S3AL1S1NS2LOS1NSS1NSS4CEIL2LO1N3HUB3LSJ2T13AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02K32K42DX1HS3HUB3AL12NB3RZ2S3AL1SSS3LSJS3LSJS3LSJS2NBS3LSJS2LOFFS2T1S3HUB3AL12NB3RZ2S3B1MS3LSJ2T03AL2S3LSJ2T03AL2S3AL1S3LSJ2T03AL2S3HUB3AL13AL32NB3RZ2SS2NBS2NBS3LSJ2T03AL2S2T1S3HUB3AL12NB3RZ2S3AL1S3LSJ2T03AL2S3LSJ2T03AL2S3AL1S3LSJS3LSJ2T03AL2S2HBS3HUB3AL12NB3RZ2SS2LOS2HBS4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO3HUB3AL32NB3RZ2S3LSJS3LSJ2T03AL2S2LOSSS3HUB3AL12NB3RZ2S3LSJ2T03AL2S2LOS2LOS3HUB3AL12NB3RZ2S2HBSS3AL1S3AL1S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S3LSJS3HUB3AL13AL32NB3RZ2S3AL1S1N2NB3RSE3RSR3NSES1N2NB3RSE3RSR3NSES2LOS4CEIL2LO1N3HUB3LSJ2T13AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02DX1HS3LSJ2T03AL2SS2HBS2T1S2T1S3HUB3AL12NB3RZ2S3LSJ2T03AL2S2HBS3AL1S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S2LOSS1NSS3LSJS3HUB3AL12NB3RZ2FFS3HUB3AL12NB3RZ2S2K4S4CEIL2LO1N3AL32NB3HspSS2NBSSS3LSJS3LSJ2T03AL2SSS3HUB3AL12NB3RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspS3HUB3AL12NB3RZ2S4CEIL2LO3AL32NBSS4CEIL2LO2T1S3LSJ2T03AL2S3LSJSFS3HUB3AL13AL32NB3RZ2S3HUB3AL13AL32NB3RZ2S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S3AL1S3HUB3AL12NB3RZ2S2T1S3AL32NB1HS3LSJ2T03AL2S3AL1FS3LSJ2T03AL2S3LSJ2T03AL2S3LSJ2T03AL2S2LOS3HUB3AL12NB3RZ2S2HBS3AL1S3LSJ2T03AL2S1NSS1NSSSS3AL1S4CEIL2LO3AL32NBSS3HUB3AL12NB3RZ2SS3AL1S3LSJ2T03AL2S2LOS3HUB3AL12NB3RZ2SS3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJ2T03AL2S3LSJ2T03AL2S3CX0S3LSJ2T03AL2S4CEIL2LO3HUB3AL32NB3RZ2S3HUB3AL12NB3RZ2S3HspSSSS2LOSS3B1MS3LSJ2T03AL2S3HUB3AL12NB3RZ2S3AL1SSS3HUB3RZ22K3S3HUB3RZ22K4S2NB3RSR3NSE2K0S3HUB3AL12NB3RZ2SS3LSJSSS3LSJ2T03AL2S3LSJ2T03AL2FS3LSJ2T03AL2S2LOS1NSS3LSJS3LSJ2T03AL2S3LSJ2T03AL2S2LOSS4CEIL2LO2T1S3LSJ2T03AL2S4CEIL2LO3HspS4CEIL2LO2NB3HspS3HUB3AL13RZ2SS4CEIL2LO3SPR1HS4CEIL2LO2NB3SPR1HSS4CEIL3AL32NBS3LSJSS3AL1S3HUB3AL12NB3RZ2S3AL1S3LSJ2T03AL2SS4CEIL2LO3HspS4CEIL2LO2NB3HspS2K4SS3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJ2T03AL2SSS4CEIL2LO3AL32NBS".
pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM) as (NB & RZ2 & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
box DJT. box LH.
snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
box UJ. box HDR.
step. call_sp (thread_stats_spec RNG (al_ctx L) t lo).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ _ _ => assumption
end.
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- rng _ _ _ => solve_rng
| |- _ => unfold AIMG_HI; lia
end.
rename POST into ST.
aload STATS 2 (t + 2800 + 16).
aload STATS 0 (t + 2800 + 0).
aload STATS 1 (t + 2800 + 8).
zstep. zstep. step. zstep. zstep. zstep.
astore STATS 0.
astore STATS 1.
astore STATS 2.
step. if_cases K0; zify_cond K0. { exfalso. lia. }
aload STATS 13 (t + 2800 + 104).
zstep.
astore STATS 13.
step. step. if_lit.
carry UJ MUs WMs ltac:(with_box DJT lia). carry HDR MUs WMs ltac:(with_box DJT lia).
unbox LH.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (LH' : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
{ intros RZ. specialize (LH RZ). box LH. carry LH MUs WMs ltac:(with_box DJT lia). exact LH. }
clear LH MUs WMs. box LH'. box STATS.
snapshot [(UB - 16, UB + n); (AB, AB + 16); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUc WMc.
snapshot [(UB - 16, UB + n); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUl WMl.
step. step. lstep. step. if_lit.
eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG] |]. cbv beta. intros msF ->.
set (fl := Z.min n 4096) in *.
destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
step. step. step. lstep. step.
step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- mem_inv _ _ => assumption
| |- @eq word _ _ => reflexivity
| |- rw_cells _ _ _ [CB _ _] => exact UJ1
| |- rng _ _ _ => eapply rng_sub'; [exact RU|]; subst fl; lia
| |- _ => subst fl; atop_facts; lia
end.
rename POST into UF1.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (UF : rw_cells asegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
{ replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
clear UF1 UJ2.
step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
lstep. zstep. zstep. zstep. zstep. step.
sstep. step. step.
unbox LH'.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (LH : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
{ intros RZ. specialize (LH' RZ). box LH'. carry LH' MUl WMl ltac:(lia). exact LH'. }
clear LH' MUl WMl.
pose proof (rz_size_cases n) as RZC. box RZC.
step. if_cases K3; zify_cond K3. { exfalso. clear -K3 RZ2 HUB; lia. }
-
specialize (LH ltac:(rewrite RZ2; lia)).
zstep. step. if_cases K4; zify_cond K4. { exfalso. clear -K4 RZ2 HUB; lia. }
step. step.
step. step. step.
step. step. step. call_sp (run_malloc_hooks_spec RNG).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- rw_cells _ _ _ _ => exact HK
| |- rng _ _ _ => solve_rng
| |- _ => atop_facts; lia
end.
rename POST into ST.
do 16 step.
release_frame FR ST (bv_unsigned sp).
carry STATS MUc WMc ltac:(with_box DJT lia).
apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
intros _. exact LH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
