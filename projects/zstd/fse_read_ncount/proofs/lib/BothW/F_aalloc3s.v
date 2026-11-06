(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 ABytes AModelFacts APrimFacts ASecFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2 F_aalloc3g.
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
#[using="Type"] Lemma allocD_sec : forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
(n t AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
(fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0x s6x s9x t3 t4 t5 t6 : word),
stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
mem_inv bsegs m ->
tp = Z_to_bv 64 ATP ->
1 <= n <= AREQMAX -> is_primary n = false ->
UB = AB + rz_size n -> ablk AB (UB + n) -> UB + n <= ATOP -> AB mod 16 = 0 ->
(t + 4096 <= AB \/ UB + n <= t) ->
rw_cells bsegs m (bv_unsigned sp + -128)
[CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
rw_cells bsegs m 0xa1da0 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xa1da4 [C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
rw_cells bsegs m 0x9fd64 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)] ->
rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)] ->
rw_cells bsegs m 0x9b770 [C8 (Z_to_bv 64 0x92c40); C8 (Z_to_bv 64 0x93044)] ->
rw_cells bsegs m 0x9a568 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x5d54e0 [C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m 0x134000 [C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
0 <= b1m < 256 -> 0 < id < 2^31 ->
(16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
evtF bsegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
(MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
s0x (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
(Z_to_bv 64 S) (Z_to_bv 64 0) s9x (Z_to_bv 64 t) (Z_to_bv 64 1)
t3 t4 t5 t6)
F (Z_to_bv 64 0x328d4) fc None m (seg_rom bsegs)).
Proof.
intros until t6.
intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.
pose proof (ablk_lin _ _ ABLO) as (AL1 & AL2 & AL3 & AL4).
unfold AIMG_HI, ATP88, ATSD, AREQMAX in *.
Local Ltac2 Set LiaHints.tbl := fun () => "04i0?10028172029.12510028172029.14710167497279.14710456434697.1501047820382.117 10587903613.11810640816421.11910640816421.12010900051222.12110911084698.13711077664131.14711118462589.12511118462589.14711462352626.1181162083375.146 11765624680.15011801586693.12511801586693.14712308886460.14512341586989.11812406238321.14613086827028.13113118011600.11813166236520.1501324746171.148 13303947452.14513596006226.14614208485765.11814208485765.11914335039570.1461503082802.148 15043033658.1191533820803.147 15588165249.12115588165249.13815813913903.12515995719016.15016263107213.14516398988797.11916482458097.13716703780397.11916865227715.1401750798787.140 17776320431.14617967033458.11817986879152.11717986879152.13818436191427.14018803398514.11819123199200.14719125296363.14819350300419.1401937063194.117 20880379370.14620970059894.13021077578749.12521077578749.14721282393832.15021490588786.1192150086885.146 2172922258.145 21924557829.11821924557829.11922182730578.14622675801219.14822700267513.12622700267513.14222700267513.1482310074925.119 23182051176.15023586406368.12124559885231.14624904914272.11824924589988.13125029166211.14725065190167.12025071629079.13725071629079.14625080282415.11825080282415.11925708897522.11925787632170.12125878270254.1472589182834.118 26170477810.11826494647592.13726494647592.14526494647592.14626494647592.15026496924968.14026868428163.14626879533652.13026879533652.13126915800965.11926915800965.1202699564227.140 27171665174.13727188338533.12127251872635.13227408782894.14727576757255.12527576757255.14727726645424.11928360709362.11828738030430.13728754851922.14628767007858.11928832574270.13729877002610.1183017725367.150 30420195523.14030507153671.13630518562691.14630608897138.11930719730331.12230719730331.13730876703602.11831218985776.11831423336146.14631521058898.14632162886226.14632418465650.11833333358812.12933558212378.14633765134616.13833890036527.14634022839870.13734170950174.13734811111154.11834977462002.11935148913011.15035376095986.11835437277426.11935587884146.11835933558651.13236115622446.14736254216601.14836254216601.14936302465522.11936814730237.12536814730237.14737386977061.11737386977061.13837585159586.14537763307450.14938074103656.15038465254514.1183894281273.119 39407463154.13739932046344.11839938772490.13240091925676.14540326235777.12040458636732.14541422282358.1194158230386.118 42389998958.15042445826608.11842445826608.11942831019478.14643041729214.13743372435176.15043509719107.14043987951406.14743995329413.14544030539416.10244158664835.14844305789522.14644311304733.11944484923210.12544484923210.14744602107843.14044631646014.13744767421808.14544824048191.14744833359747.14745201937650.11845288596498.12245299829152.11945331600228.13245451326843.13245944259164.11945962238104.13046148965950.13746368229782.14246562743228.14547089684979.14047089684979.14147103961859.14047420759102.13747557849085.11847747814717.12547747814717.1474798910125.118 48616173652.13149294572020.1204936038867.141 49433673850.13749433673979.13649890836722.11850457931440.11850461111123.12250750500979.11950993995517.12550993995517.14751074090738.11951136181618.11851191184446.13751515740530.11851633495293.12551633495293.14751678667180.14551816630506.13751822753522.11952297866226.11852458472562.11952567164907.13752567164907.14552567164907.14652567164907.15052575291859.11852575291859.11952586760667.14552682867945.13752987902756.12053276606962.11953442112190.13753767577775.14653826772850.11854833884274.11954969794426.11755044677874.11955415250674.11955460634391.14555860948746.13756170256219.11956172415395.13756590202216.1505684463747.126 5691754054.119 56993309444.13957033123058.11957054875198.13757196545107.12257378147907.14057708384067.14057751108064.14457821142078.13757866941884.14558023386994.118586216434.118  58655119491.14858910293436.14558956747506.11859192378728.15059276314076.12159308628566.6  59308628695.6  59314873579.11959442793916.14559907387523.1486010284381.119 60235800116.1216055995506.119 60634079619.14660685297596.14561597347058.11961694112329.14161917199020.14561939782288.1326293724274.119 62976134100.13062976134100.1316313882541.118 6313882541.119 63143451580.14563235321900.14563620834110.13763670697722.14463745434493.11863923647848.1506398474066.146 64393308029.12564393308029.14764548988925.12564548988925.14765644234482.11865797088788.12265952741501.12565952741501.14765983638659.14766028155702.12066028155702.14166357861087.1466653728088.140 66701037743.1306748444989.125 6748444989.147 6758013062.119 692741842.146  7021785682.146 7780899791.145 7795003580.145 7882758244.150 8179223683.146 8601557106.118 917434854.146  9196977948.123 9457190248.150 9522874812.145 9632634738.118 9666466205.146 9729791282.137 00000=00M00i00m01201>01C01H01I01J01K01X01h02402802=02U02i02n03:03;03<03=03B03C03H03X03]03b04204304404504g05?05C05H05L05X05^05c06306C06G06S06Y06_06o07;07>07A07Q07U07V07W07d08408908E08F08I08N08S08c08d09_0:V0;V0;b0;g0;h0;l0;m0;n0;o0<i0<l0<o0=00=10==0=@0=D0=P0=\0=_0=`0=c0=d0>g0>h0>i0>n0?30?80?H0?I0?M0?R0?V0?W0?X0?\0?h0?m0@=0@I0@Y0@e0@j0A:0AN0AO0A[0A_0Ac0Ao0B30BC0BS0Bc0Bo0C40C80C90C=0CM0CQ0C]0Ci0DA0DM0DY0De0Dj0Dn0Do0E00E<0EI0EY0E]0Ea0Ee0Ef0Ek0F70F<0FP0Fb0G40G80H50H:0H;0HG0HK0HO0HS0HW0Hg0Hl0I<0I@0IA0ID0IE0IU0IZ0I[0I\0Il0J<0J@0JV0JW0Jc0Jg0Jh0Ji0Jn0Jo0K00K@0KA0KF0KV0KW0Kg0L70LC0LP0L`0Ll0M10M20M30MG0M[0Mg0Mk0N50N60NC0NS0N_0Nk0O;0OG0OT0Od0Oh0Ol0P80PD0PP0PS0PT0PW0PX0PY0PZ0P_0Po0Q00Q<0QL0QP0Q\0Qh0Qm0R90RE0R]0R^0Rc0Rd0Ri0Rj0Rk0Ro0S;0SK0SL0S\0Sl0T10TA0TF0TR0T^0T_0Td0U00U50U60UB0UN0U]0Ub0Uc0Uh0Ui0V50V60V;0VG0VH0VL0VO0V[0V\0Va0Vm0W90W>0WB0WR0WS0W_0Wd0X40XA0XQ0X^0Xn0Y:0YG0YT0Yd0Ye0Z40ZF0ZG0ZT0ZY0Zf0[60[70[G0[W0[X0[]0[a0[b0[n0[o0\00\50\:0\F0\V0\WS4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO3HUB3AL32NB3RZ23HspS2K4S3CX1S4CEIL2LO2T1S3LSJS3LSJSSSS4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2S2LOS3AL1S4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO3AL32NB3HspS3AL1S3LSJ2T03AL2SSSS3AL1SS3AL1S3HUB3AL12NB3RZ2S3LSJS3LSJS3HUB3AL12NB3RZ2SSSS4CEIL2LO1N3HUB3LSJ3AL13AL23AL32NB3RZ23MSB2K02DX1HS4CEIL2LO3HUB3AL32NB3RZ2S2LOS3AL1S2K4S4CEIL2LO2T1S1N2NBS3LSJS3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S2LOS3LSJ2T03AL2S4CEILS4CEILS3HUB3AL12NB3RZ2S3LSJ2T03AL2S1NS1NS3HUB3AL12NB3RZ2S2T1SSS4CEIL2LO3HspS4CEIL2LO2NB3HspS3AL1S3LSJ2T03AL2SS1NS3LSJS3LSJS3HUB3AL12NB3RZ2SS4CEIL2LO1N3LSJ2T13AL23RSE3NSE3MSE3MSB3Hsp1H3HUB3AL32NB3RZ2S4CEIL2LO1N3LSJ3AL23AL32NB3RSE3NSE3MSB2K01H3HUB3RZ23AL1S4CEIL2LO1N3HUB3LSJ3AL23AL32NB3RZ23RSE3NSE3MSB2K02K32K43Hsp1H2T1S3LSJ2T03AL2S3AL1SS2LOSSSS4CEIL2LO1N3HUB3LSJ3AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02DX1HS1NS1NSSS3LSJ2T03AL2S1NS2LOS3LSJ2T03AL2S3LSJ2T03AL2S1NSS1NSS4CEIL2LO1N3HUB3LSJ2T13AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02K32K42DX1HSSS3LSJS3LSJS3LSJS3HUB3AL12NB3RZ2SS2NBS3LSJS2LOFFS2T1S3LSJ2T03AL2S3B1MS3HUB3AL12NB3RZ2S3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJ2T03AL2S3AL1S3HUB3AL12NB3RZ2S3HUB3AL13AL32NB3RZ2SS3LSJ2T03AL2S2NBS2NBS3LSJ2T03AL2S2T1S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S3LSJ2T03AL2S3LSJS2HBSS2LOS3HUB3AL12NB3RZ2S2HBS3LSJ2T03AL2S3LSJ2T03AL2S4CEIL2LO3HUB3AL32NB3RZ2S3LSJ2T03AL2S3LSJ2T03AL2S3LSJ2T03AL2S3LSJS2LOSSS3LSJ2T03AL2S4CEIL2LO3HspS4CEIL2LO2NB3HspS2LOS2LOS2HBSS3AL1S3LSJ2T03AL2S3LSJS3HUB3AL13AL32NB3RZ2S1N2NB3RSE3RSR3NSES1N2NB3RSE3RSR3NSES2LOS4CEIL2LO1N3HUB3LSJ2T13AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02DX1HS3AL1SS3LSJ2T03AL2S2HBS2T1S2T1S2HBS3HUB3AL12NB3RZ2S3AL1S3HUB3AL12NB3RZ2S2LOSS1NSS3HUB3AL12NB3RZ2S3LSJFFS3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S2K4S4CEIL2LO1N3AL32NB3HspSS3LSJ2T03AL2S2NBSSS3LSJSSS3HUB3AL12NB3RZ2SS3AL1S4CEIL2LO3AL32NBSS3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S4CEIL2LO2T1S4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2S3LSJSFS3HUB3AL13AL32NB3RZ2S3HUB3AL13AL32NB3RZ2S3LSJ2T03AL2S2T1S3AL32NB1HFS4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2S3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJ2T03AL2S4CEIL2LO3HspS4CEIL2LO2NB3HspS2LOS2HBS3LSJ2T03AL2S3LSJ2T03AL2S3LSJ2T03AL2S1NSS1NSSSS3AL1S4CEIL2LO3AL32NBSS3LSJ2T03AL2S3HUB3AL12NB3RZ2S2LOS3LSJ2T03AL2S3LSJ2T03AL2S3CX0S3LSJ2T03AL2S3LSJ2T03AL2S4CEIL2LO3HUB3AL32NB3RZ2SS3HspSS3AL1SSS2LOS3LSJ2T03AL2S3HUB3AL12NB3RZ2SS3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S3B1MS3HUB3AL12NB3RZ2S3AL1S3LSJ2T03AL2S3LSJ2T03AL2SS3AL1S3LSJ2T03AL2S3AL1SS3HUB3RZ22K3S3HUB3RZ22K4S2NB3RSR3NSE2K0S3AL1SS3LSJSS3LSJ2T03AL2SS3AL1S3LSJ2T03AL2FS2LOS1NS3LSJ2T03AL2SS3LSJS3LSJ2T03AL2S3LSJ2T03AL2S3AL1S2LOS3HUB3AL12NB3RZ2SS4CEIL2LO2T1S3AL1S3HUB3AL12NB3RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2S3HUB3AL13RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspSS4CEIL2LO3SPR1HS4CEIL2LO2NB3SPR1HSS4CEIL3AL32NBS3LSJS4CEIL2LO3HspS4CEIL2LO2NB3HspSS3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2SS3AL1S2K4SS3LSJ2T03AL2SSS3AL1S3AL1S3LSJ2T03AL2S4CEIL2LO3AL32NBS".
pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM) as (NB & RZ2 & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
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
assert (LH' : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
assert (UF : rw_cells bsegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
{ replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
clear UF1 UJ2.
step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
lstep. zstep. zstep. zstep. zstep. step.
sstep. step. step.
unbox LH'.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (LH : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
