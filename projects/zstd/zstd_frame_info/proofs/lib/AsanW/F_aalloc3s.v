(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 ABytes AModelFacts APrimFacts ASecFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2 F_aalloc3g.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m 0xa06e0 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xa06e4 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
  rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
  0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x9e6a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                             C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)] ->
  rw_cells asegs m 0x98e58 [C8 (Z_to_bv 64 0x9acc0)] ->
  rw_cells asegs m 0x9acb8 [C8 (Z_to_bv 64 0x92164); C8 (Z_to_bv 64 0x92568)] ->
  rw_cells asegs m 0x99a90 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x5d3e20 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x132940 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 <= b1m < 256 -> 0 < id < 2^31 ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
  evtF asegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              s0x (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) s9x (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x31778) fc None m (seg_rom asegs)).
Proof.
  intros until t6.
  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  pose proof (ablk_lin _ _ ABLO) as (AL1 & AL2 & AL3 & AL4).   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD, AREQMAX in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "04i0?10167497279.14710397311164.14510456434697.1501047820382.117 10587903613.11810640816421.11910640816421.12010911084698.13711077664131.14711167982066.1191162083375.146 11801586693.12511801586693.14711956477810.11812341586989.11812406238321.14613086827028.13113118011600.1181324746171.148 13329794408.15014208485765.11814208485765.11914484648690.11814684412918.1301503082802.148 15043033658.1191533820803.147 15588165249.12115588165249.13815813913903.12515845511538.11815969700978.11916263107213.14516398988797.11916482458097.13716622434386.14616703780397.11917028749810.11917487950275.14017658312259.14017776320431.14617986879152.11717986879152.13818260229182.1371838634856.150 18392534760.15019123199200.14719125296363.14819155925874.11819241987666.1461937063194.117 19591727510.12120010950973.12520010950973.14720880379370.1462150086885.146 21597125182.1372172922258.145 21924557829.11821924557829.11922675801219.14822700267513.12622700267513.14222700267513.14822737361138.1182310074925.119 23586406368.12124411702716.14524559885231.14624885861438.13724904914272.11824924589988.13125029166211.14725065190167.12025071629079.13725071629079.14625080282415.11825080282415.11925787632170.12125878270254.14726310013116.14526494647592.13726494647592.14526494647592.14626494647592.15026496924968.14026649897404.14526775167848.15026868428163.14626879533652.13026879533652.13126915800965.11926915800965.12027188338533.12127251872635.13227408782894.14727576757255.12527576757255.14727726645424.11928176765800.15028586104050.11928738030430.13728941393650.1183017725367.150 30475885500.14530507153671.13630518562691.14630719730331.12230719730331.13730750431683.14031042920131.14031218985776.11831665118403.14033333358812.12933558212378.14633761420530.11933765134616.13833890036527.14634170950174.13734357674738.11834509983550.13734601944178.11835065878258.11935148913011.15035895327997.12535895327997.14735933558651.13236033352946.11836115622446.14736254216601.14836254216601.14936268652402.11836911535464.15037179231090.11837386977061.11737386977061.13837585159586.14537763307450.14937774388668.1453789875267.140 38769580476.1453894281273.119 39146469490.11939203822524.14539407463154.13739779905342.13739932046344.11839938772490.13240091925676.14540226033084.14540326235777.12040462318706.11941422282358.11941836358898.11942389998958.15042445826608.11842445826608.11942831019478.14642967766376.15043186039794.11843472444776.15043493603410.14643987951406.14743995329413.14544030539416.10244158664835.14844225934142.13744227402430.13744311304733.11944484923210.12544484923210.14744610219890.11844767421808.14544824048191.14744833359747.14745288596498.12245299829152.11945331600228.13245354402162.11845451326843.13245944259164.11945962238104.13046162087634.14647089684979.14047089684979.14147353497150.1374738246770.118 47406429554.11847557849085.11847843767026.1194798910125.118 48348884739.14048616173652.1314881215427.140 48841878642.11949294572020.1204936038867.141 49433673850.13749433673979.13649793197630.13750077211645.12550077211645.14750457931440.11850461111123.12250470234962.14650750500979.11951548755826.11851678667180.1455173701827.140 51816630506.13751902411762.1185234660466.118 52567164907.13752567164907.14552567164907.14652567164907.15052575291859.11852575291859.11952586760667.14552682867945.13752987902756.12052994560594.1465300105810.146 53767577775.14654124535740.14554761860978.11854969794426.11755460634391.14556170256219.11956172415395.13756375967986.11956426686290.1465684463747.126 5691754054.119 56993309444.13957196545107.12257751108064.14457785628402.11957945953128.15058147165938.11858331630915.14058343875516.14558655119491.14859276314076.12159308628566.6  59308628695.6  59314873579.1195932235838.137 59681117426.11859743357778.14659784840306.11959907387523.14859961997718.1376010284381.119 60235800116.12160634079619.14660976774461.12560976774461.14761694112329.14161917199020.14561939782288.13262073164018.11962976134100.13062976134100.1316313882541.118 6313882541.119 63235321900.14563297025046.14263478620285.12563478620285.14763670697722.14463745434493.11864227055474.11864349369458.11964560625362.14664666605650.14664794176872.15064862446845.12564862446845.14765016030589.12565016030589.14765188488701.12565188488701.14765683728114.11865797088788.12265983638659.14766028155702.12066028155702.14166357861087.1466653728088.140 66701037743.1306698781810.118 6718686952.150 6758013062.119 6955981502.137 6967372938.137 7349490435.140 7518407421.125 7518407421.147 7780899791.145 7848643581.125 7848643581.147 7882758244.150 8179223683.146 8610795133.125 8610795133.147 8664102002.119 880821490.118  9118104306.119 917434854.146  9196977948.123 9666466205.146 9729791282.137 00000L00Q00U00Z00f00k01001101201>01B01Z01n02:02F02G02H02I02J02O02T02Y02e02f02g02h02i03[04304704C04O04S04_04e05505:05F05V05f05j06006606F06K06P06S06V06b07207607707D07T07U07V07f07i07n08308408o09f0:f0;20;>0;?0;D0;H0;X0;Y0;Z0;[0<U0<X0<[0<\0<]0<`0<d0<i0<l0<m0=00=10>40>90>>0>?0>@0>E0>J0>O0>S0>X0>\0>]0>^0>b0>g0?30?80?D0?I0?N0?b0?c0?g0?k0@;0@K0@O0@_0@d0@h0A40A50A90A=0AI0AY0Ae0B10BI0BV0Bf0Bk0C70C;0C<0C=0CI0CN0CZ0C^0Cb0Cf0Cg0Cl0D<0DA0DF0DR0DW0Dk0E;0EM0E_0Ec0Eh0Fe0G10G20G>0GB0GF0GJ0GN0GS0G_0Gd0H40H80H90H<0H=0HM0H]0Hb0Hc0Hd0I00I40IJ0IK0IO0IP0IQ0I]0Ib0Ic0Id0J40JD0JE0JU0Ja0Jm0K90KE0KQ0Ka0Kf0L60LB0LC0LD0LX0Ll0M<0MI0MY0M]0Mg0N70N80ND0NH0NX0N\0Nh0O40O70O80O;0O<0O=0O>0OC0OS0OT0Od0P40P80P=0PI0PN0Pf0Pk0Pl0Q80QH0QI0QJ0QN0QO0QT0Q`0Qe0R10RA0RF0RG0RH0RT0R`0Ro0S?0SK0S[0Sg0Sh0Si0Sn0So0T00T=0TM0TN0TR0TU0Ta0Tb0Tg0U30U?0UC0UD0UQ0Ua0Ub0Un0V:0VF0VV0Vf0Vk0W80WH0WU0We0X20XB0XN0X[0X\0Xk0Y=0Y>0YK0YP0Y\0Ya0Yb0Z20Z30ZC0ZP0Z`0Za0Zn0[>0[B0[C0[P0[`0[l0\80\D0\E0\F0\V0\WS4CEIL2LO3HUB3AL32NB3RZ23HspS3AL1S2K4S3CX1S4CEIL2LO2T1S3LSJS3LSJSSS3LSJ2T03AL2S2LOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO3AL32NB3HspS3LSJ2T03AL2S3LSJ2T03AL2SSSSS3AL1S3LSJS3LSJS3LSJ2T03AL2SSSSS4CEIL2LO1N3HUB3LSJ3AL13AL23AL32NB3RZ23MSB2K02DX1HS4CEIL2LO3HUB3AL32NB3RZ2S2LOS3LSJ2T03AL2S3LSJ2T03AL2S2K4S4CEIL2LO2T1S1N2NBS3HUB3AL12NB3RZ2S3LSJS3LSJ2T03AL2S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S2LOS4CEILS4CEILS3HUB3AL12NB3RZ2S3AL1S3AL1S1NS1NS3LSJ2T03AL2S3HUB3AL12NB3RZ2S2T1SS4CEIL2LO3HspS4CEIL2LO2NB3HspSSS3HUB3AL12NB3RZ2S1NS3LSJS3LSJSS4CEIL2LO1N3LSJ2T13AL23RSE3NSE3MSE3MSB3Hsp1H3HUB3AL32NB3RZ2S4CEIL2LO1N3LSJ3AL23AL32NB3RSE3NSE3MSB2K01H3HUB3RZ23AL1S4CEIL2LO1N3HUB3LSJ3AL23AL32NB3RZ23RSE3NSE3MSB2K02K32K43Hsp1H2T1S3LSJ2T03AL2S3LSJ2T03AL2SS3AL1S2LOS3HUB3AL12NB3RZ2SSSS4CEIL2LO1N3HUB3LSJ3AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02DX1HS1NS1NSSS1NS2LOS3AL1S1NSS1NSS4CEIL2LO1N3HUB3LSJ2T13AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02K32K42DX1HS3AL1S3AL1SSS3LSJS3LSJS3LSJS2NBS3LSJS2LOFFS2T1S3AL1S3LSJ2T03AL2S3B1MS3LSJ2T03AL2S3AL1S3AL1S3HUB3AL13AL32NB3RZ2SS2NBS2NBS3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S2T1S3HUB3AL12NB3RZ2S3LSJS2HBS3LSJ2T03AL2SS2LOS2HBS3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJ2T03AL2S3LSJ2T03AL2S4CEIL2LO3HUB3AL32NB3RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJS3LSJ2T03AL2S2LOSSS3LSJ2T03AL2S3AL1S3LSJ2T03AL2S2LOS2LOS2HBSS3AL1S3HUB3AL12NB3RZ2S3AL1S3LSJS3LSJ2T03AL2S3AL1S3HUB3AL13AL32NB3RZ2S3HUB3AL12NB3RZ2S1N2NB3RSE3RSR3NSES1N2NB3RSE3RSR3NSES2LOS3AL1S4CEIL2LO1N3HUB3LSJ2T13AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02DX1HS3LSJ2T03AL2SS3LSJ2T03AL2S2HBS2T1S2T1S2HBS3AL1S3LSJ2T03AL2S3AL1S3HUB3AL12NB3RZ2S2LOSS1NSS3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S3LSJFFS3LSJ2T03AL2S2K4S4CEIL2LO1N3AL32NB3HspSS2NBSSS3LSJ2T03AL2S3LSJSSS3HUB3AL12NB3RZ2S4CEIL2LO3AL32NBSS3HUB3AL12NB3RZ2S3LSJ2T03AL2S3LSJ2T03AL2S4CEIL2LO2T1S3LSJ2T03AL2S3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJS3HUB3AL12NB3RZ2S3LSJ2T03AL2SFS3HUB3AL13AL32NB3RZ2S3HUB3AL13AL32NB3RZ2S3HUB3AL12NB3RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspS2T1S3AL32NB1HS3HUB3AL12NB3RZ2FS3LSJ2T03AL2S2LOS3HUB3AL12NB3RZ2S2HBS3LSJ2T03AL2S3LSJ2T03AL2S1NSS1NSSSS3AL1S4CEIL2LO3AL32NBSS3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S2LOS3AL1S3LSJ2T03AL2S3CX0S4CEIL2LO3HUB3AL32NB3RZ2S3HspSS3LSJ2T03AL2S3HUB3AL12NB3RZ2SSS2LOSS3B1MS3LSJ2T03AL2S3AL1S3LSJ2T03AL2S3HUB3AL12NB3RZ2S3AL1SSS3HUB3RZ22K3S3HUB3RZ22K4S2NB3RSR3NSE2K0S3HUB3AL12NB3RZ2S3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJ2T03AL2SSS3LSJSSS4CEIL2LO3HspS4CEIL2LO2NB3HspFS2LOS1NS3LSJ2T03AL2SS3LSJS3LSJ2T03AL2S3LSJ2T03AL2S2LOSS4CEIL2LO3HspS4CEIL2LO2NB3HspSS4CEIL2LO2T1S3LSJ2T03AL2S3LSJ2T03AL2S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S3AL1S4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2S3HUB3AL13RZ2SS4CEIL2LO3SPR1HS4CEIL2LO2NB3SPR1HSS4CEIL3AL32NBS3LSJS3LSJ2T03AL2S3AL1SS3HUB3AL12NB3RZ2SS3HUB3AL12NB3RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspSS4CEIL2LO3HspS4CEIL2LO2NB3HspS2K4SS4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2S3LSJ2T03AL2S3LSJ2T03AL2SSS4CEIL2LO3AL32NBS".
pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM) as (NB & RZ2 & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  step. call_sp (thread_stats_spec RNG (al_ctx L) t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  rename POST into ST.
  aload STATS 2 (t + 2800 + 16).                                 (* [comment removed for export] *)
  aload STATS 0 (t + 2800 + 0).                                  (* [comment removed for export] *)
  aload STATS 1 (t + 2800 + 8).                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep. zstep. zstep.                       (* [comment removed for export] *)
  astore STATS 0.                                                (* [comment removed for export] *)
  astore STATS 1.                                                (* [comment removed for export] *)
  astore STATS 2.                                                (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  aload STATS 13 (t + 2800 + 104).                               (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  astore STATS 13.                                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  carry UJ MUs WMs ltac:(with_box DJT lia). carry HDR MUs WMs ltac:(with_box DJT lia).
  unbox LH.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH' : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH RZ). box LH. carry LH MUs WMs ltac:(with_box DJT lia). exact LH. }
  clear LH MUs WMs. box LH'. box STATS.
  snapshot [(UB - 16, UB + n); (AB, AB + 16); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUc WMc.
  snapshot [(UB - 16, UB + n); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUl WMl.
  (* [comment removed for export] *)
  step. step. lstep. step. if_lit.                               (* [comment removed for export] *)
  eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG] |]. cbv beta. intros msF ->.   (* [comment removed for export] *)
  set (fl := Z.min n 4096) in *.
  destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
  step. step. step. lstep. step.                                 (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => exact UJ1
       | |- rng _ _ _ => eapply rng_sub'; [exact RU|]; subst fl; lia
       | |- _ => subst fl; atop_facts; lia
       end.
  rename POST into UF1.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (UF : rw_cells asegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
  { replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
    apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
  clear UF1 UJ2.
  (* [comment removed for export] *)
  step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
  lstep. zstep. zstep. zstep. zstep. step.                       (* [comment removed for export] *)
  sstep. step. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  unbox LH'.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH' RZ). box LH'. carry LH' MUl WMl ltac:(lia). exact LH'. }
  clear LH' MUl WMl.
  pose proof (rz_size_cases n) as RZC. box RZC.
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 RZ2 HUB; lia. }   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    specialize (LH ltac:(rewrite RZ2; lia)).
    zstep. step. if_cases K4; zify_cond K4. { exfalso. clear -K4 RZ2 HUB; lia. }   (* [comment removed for export] *)
    step. step.                                                  (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
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
(* [comment removed for export] *)
