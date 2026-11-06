(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 ABytes AModelFacts APrimFacts ASecFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2 F_aalloc3g.
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
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m 0xa08a0 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xa08a4 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
  rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
  0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0x9e864 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                             C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)] ->
  rw_cells bsegs m 0x99030 [C8 (Z_to_bv 64 0x9ae98)] ->
  rw_cells bsegs m 0x9ae90 [C8 (Z_to_bv 64 0x92340); C8 (Z_to_bv 64 0x92744)] ->
  rw_cells bsegs m 0x99c68 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x5d3fe0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x132b00 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 <= b1m < 256 -> 0 < id < 2^31 ->
  (16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
  evtF bsegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              s0x (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) s9x (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x3177c) fc None m (seg_rom bsegs)).
Proof.
  intros until t6.
  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  pose proof (ablk_lin _ _ ABLO) as (AL1 & AL2 & AL3 & AL4).   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD, AREQMAX in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "04i0?10167497279.14710456434697.1501047820382.117 10486456818.11910495213693.12510495213693.14710587903613.11810640816421.11910640816421.12010768192754.11910911084698.13711077664131.14711480366910.1371162083375.146 11801586693.12511801586693.14712115366258.11812270362430.13712341586989.11812406238321.14613086827028.13113118011600.1181324746171.148 137680626.119  14208485765.11814208485765.1191503082802.148 15043033658.1191533820803.147 15578933362.11815588165249.12115588165249.13815696294482.14615813913903.12515928523971.14016263107213.14516398988797.11916482458097.13716703780397.11917018810435.14017086648040.15017776320431.14617986879152.11717986879152.13818365406014.13719123199200.14719125296363.1481921160771.140 1937063194.117 20501024188.14520670856254.13720880379370.14621006689010.1182150086885.146 2172922258.145 21905638514.11921924557829.11821924557829.1192267550066.118 22675801219.14822700267513.12622700267513.14222700267513.1482310074925.119 23100797699.14023257131773.12523257131773.14723586406368.12123724173437.12523724173437.14724346898045.12524346898045.14724492166258.11824559885231.14624904914272.11824924589988.13125029166211.14725065190167.12025071629079.13725071629079.14625080282415.11825080282415.11925765569650.11925787632170.12125845764028.14525878270254.14726494647592.13726494647592.14526494647592.14626494647592.15026496924968.14026858971378.11926868428163.14626879533652.13026879533652.13126915800965.11926915800965.12027188338533.12127251872635.13227408782894.14727576757255.12527576757255.14727726645424.11928738030430.13728862602600.15029331998019.1403017725367.150 30240964978.11830507153671.13630518562691.14630719730331.12230719730331.13731218985776.11831361185874.14632094984894.13732096683286.12132346218354.11832598658622.13732927862979.14033333358812.12933525351794.11833558212378.14633753433366.13733765134616.13833890036527.14633953449074.11834170950174.13735148913011.15035376310130.1183542266866.118 35568762877.12535568762877.14735933558651.13236053481878.14236115622446.14736147869116.14536254216601.14836254216601.14936822615400.15037018278974.13737369278270.13737386977061.11737386977061.13837585159586.14537728604022.13037763307450.1493894281273.119 39025939570.11839119749992.15039295571186.11839407463154.13739932046344.11839938772490.13240091925676.14540326235777.12040730098802.11941266725106.11941279206130.11841422282358.1194165013746.119 42078147432.15042389998958.15042445826608.11842445826608.1194272226621.125 4272226621.147 42770728680.15042831019478.14642886996547.14043360954812.14543609253714.14643987951406.14743995329413.14544030539416.10244158664835.14844311304733.11944398238652.14544484923210.12544484923210.14744551111922.11844702716274.11844767421808.14544824048191.14744833359747.14745238050109.12545238050109.14745288596498.12245299829152.11945331600228.13245451326843.13245464690442.13745944259164.11945962238104.13046486534595.1404664361714.118 47037521138.11847089684979.14047089684979.14147557849085.11847917573052.1454798910125.118 48577040082.14648616173652.13149123722493.12549123722493.14749294572020.1204936038867.141 49433673850.13749433673979.13650457931440.11850461111123.12250575413842.14650750500979.11951678667180.14551787079037.12551787079037.14751816630506.13751956423154.11952436596434.14652567164907.13752567164907.14552567164907.14652567164907.15052575291859.11852575291859.11952586760667.14552666310076.14552682867945.13752766889320.15052987902756.12053735224680.15053767577775.14654011733842.14654876624626.11854969794426.11755460634391.14555724282098.11956170256219.11956172415395.13756358351678.13756630081394.11856772200515.1405684463747.126 5691754054.119 56993309444.13957196545107.12257750928210.14657751108064.14457864589251.14058129263858.11958241330536.15058439414514.11858536729426.14658655119491.148587405170.118  59276314076.12159308628566.6  59308628695.6  59314873579.11959475428926.13759783765746.11859907387523.1486010284381.119 60129843048.15060235800116.12160406065266.11960634079619.14661038846706.11961694112329.14161917199020.14561939782288.13262251784274.14662368215228.14562602652498.14662976134100.13062976134100.1316313882541.118 6313882541.119 63188354408.15063235321900.14563551429310.13763581023218.11863670697722.14463745434493.11864083382019.14065346271869.12565346271869.14765419448050.11965526597052.14565797088788.12265811741693.12565811741693.14765983638659.14766028155702.12066028155702.14166357861087.1466653728088.140 66701037743.1306671039602.119 67138201714.1196758013062.119 68021603186.11868043442620.1457780899791.145 7882758244.150 8179223683.146 9087230140.145 917434854.146  9196977948.123 9494050930.119 9666466205.146 9674157938.118 9729791282.137 00000L00P00U00a00n01>01J01O01T01`01a01b02202602N02b02n03>03J03K03L03M03N03Z03_03d03e03f03g04304e05=05M05Q05a05e06106706<06L06Q06U06[06a07107407707G07K07P07`07a07m07n08108=08B08G08S08T09O0:F0;F0;R0;b0;o0<?0<@0<M0<]0<j0=:0=F0=J0=K0=L0=M0>G0>J0>M0>N0>O0>[0>^0>c0>g0>j0>k0>n0>o0@20@>0@?0@@0@E0@J0@O0@S0@X0@\0@]0@^0@b0@g0@l0A<0AA0AM0Aa0Ab0Af0Aj0An0B>0BN0BO0B[0Bk0C;0C@0CL0CP0CQ0CR0CV0Cb0Cf0D>0DJ0DV0Dc0E30E80E90E=0EB0EC0ED0EI0EY0Ei0Em0F10F50F60F70F<0FH0FM0FY0Fm0G?0GQ0GU0HR0H^0Hj0I60I70IC0IH0IL0IP0IT0Ia0J10J60J:0JJ0JO0J_0Jc0Jd0Jg0Jh0Jm0K20K30K40K@0KL0KP0Kf0Kg0L40LD0LH0LI0LJ0LO0LP0LQ0LR0Lb0Ln0M:0MJ0MK0MW0M\0Mh0N80N=0NJ0NZ0N[0N\0O00OD0OH0OR0Ob0Oc0Og0P40PD0PH0PT0Pd0Pg0Ph0Pk0Pl0Pm0Pn0Q30Q80QH0QM0QN0QS0QW0Qg0R30R80RP0R\0Ra0Rb0S20S>0SN0SO0SP0ST0SU0Se0Sj0T:0TF0TK0TW0Tg0Th0U40U50UA0UM0U\0Ul0V80V90V>0VC0VD0VP0VQ0V]0V^0Vb0Ve0W50W:0WJ0WK0WP0W\0Wh0Wm0X10XA0XM0XN0XZ0Xj0Y70YG0YS0YX0Ye0Z20ZB0ZC0ZR0Zd0Ze0[20[70[C0[O0[P0[\0[a0[b0[f0[g0[l0[m0[n0\:0\J0\V0\WS4CEIL2LO3HUB3AL32NB3RZ23HspS2K4S3CX1S3LSJ2T03AL2S4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO2T1S3LSJS3LSJS3LSJ2T03AL2SSS3HUB3AL12NB3RZ2S2LOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO3AL32NB3HspS3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJ2T03AL2SSSSS3LSJ2T03AL2S3LSJS3LSJSSSS3LSJ2T03AL2S4CEIL2LO1N3HUB3LSJ3AL13AL23AL32NB3RZ23MSB2K02DX1HS4CEIL2LO3HUB3AL32NB3RZ2S3HUB3AL12NB3RZ2S2LOS3HUB3AL12NB3RZ2S2K4S4CEIL2LO2T1S1N2NBS3LSJS3HUB3AL12NB3RZ2S3AL1S2LOS4CEILS4CEILS3HUB3AL12NB3RZ2S1NS1NS3HUB3AL12NB3RZ2S2T1S3AL1S3HUB3AL12NB3RZ2SS3LSJ2T03AL2SS1NS3LSJ2T03AL2S3LSJS3LSJS3LSJ2T03AL2SS4CEIL2LO1N3LSJ2T13AL23RSE3NSE3MSE3MSB3Hsp1H3HUB3AL32NB3RZ2S4CEIL2LO1N3LSJ3AL23AL32NB3RSE3NSE3MSB2K01H3HUB3RZ23AL1S4CEIL2LO1N3HUB3LSJ3AL23AL32NB3RZ23RSE3NSE3MSB2K02K32K43Hsp1H2T1S3LSJ2T03AL2S3HUB3AL12NB3RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspSS4CEIL2LO3HspS4CEIL2LO2NB3HspS4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2S2LOSSSS4CEIL2LO1N3HUB3LSJ3AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02DX1HS1NS1NSSS3LSJ2T03AL2S1NS3AL1S2LOS1NSS1NSS4CEIL2LO1N3HUB3LSJ2T13AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02K32K42DX1HS3LSJ2T03AL2SSS3LSJS3LSJS3LSJS2NBS3LSJS2LOFFS2T1S3B1MS3AL1S3HUB3AL12NB3RZ2S3AL1S3LSJ2T03AL2S3HUB3AL13AL32NB3RZ2SS2NBS2NBS2T1S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2SS3LSJ2T03AL2S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S3LSJS3LSJ2T03AL2S2HBSSS2LOS3LSJ2T03AL2S2HBS4CEIL2LO3HUB3AL32NB3RZ2S3LSJ2T03AL2S3LSJ2T03AL2S4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJSS2LOS3AL1SSS3AL1S3HUB3AL12NB3RZ2S3HUB3AL12NB3RZ2S2LOS2LOS2HBSSS3LSJS3LSJ2T03AL2S3AL1S3LSJ2T03AL2S3HUB3AL13AL32NB3RZ2S1N2NB3RSE3RSR3NSES1N2NB3RSE3RSR3NSES2LOS4CEIL2LO1N3HUB3LSJ2T13AL13AL23AL32NB3RZ23RSE3NSE3MSB2K02DX1HS3LSJ2T03AL2S3LSJ2T03AL2S3LSJ2T03AL2SS3LSJ2T03AL2S3AL1S2HBS2T1S2T1S4CEIL2LO3HspS4CEIL2LO2NB3HspS3AL1S2HBS3HUB3AL12NB3RZ2S3AL1S3HUB3AL12NB3RZ2S2LOSS1NSS3LSJS3AL1FFS3LSJ2T03AL2S3LSJ2T03AL2S2K4S4CEIL2LO1N3AL32NB3HspSS4CEIL2LO3HspS4CEIL2LO2NB3HspS2NBSSS3LSJSSSS3HUB3AL12NB3RZ2S3LSJ2T03AL2S3LSJ2T03AL2S4CEIL2LO3AL32NBSS4CEIL2LO2T1S3AL1S3LSJ2T03AL2S3HUB3AL12NB3RZ2S3LSJS4CEIL2LO3HspS4CEIL2LO2NB3HspSFS3HUB3AL13AL32NB3RZ2S3HUB3AL13AL32NB3RZ2S2T1S3AL32NB1HS3HUB3AL12NB3RZ2FS2LOS4CEIL2LO3HspS4CEIL2LO2NB3HspS2HBS3LSJ2T03AL2S3HUB3AL12NB3RZ2S1NSS1NSSSS3AL1S3AL1S4CEIL2LO3AL32NBS3AL1SS3AL1S2LOS3HUB3AL12NB3RZ2S3LSJ2T03AL2S3CX0S4CEIL2LO3HUB3AL32NB3RZ2S3LSJ2T03AL2S3HspSS3HUB3AL12NB3RZ2S3LSJ2T03AL2S3HUB3AL12NB3RZ2SSS2LOSS3HUB3AL12NB3RZ2S3B1MS3HUB3AL12NB3RZ2S3LSJ2T03AL2S3AL1S3LSJ2T03AL2S3HUB3AL12NB3RZ2SS3LSJ2T03AL2SS3HUB3RZ22K3S3HUB3RZ22K4S2NB3RSR3NSE2K0S3HUB3AL12NB3RZ2S3LSJ2T03AL2SS3LSJS3AL1SS3LSJ2T03AL2SS3LSJ2T03AL2FS2LOS1NS3HUB3AL12NB3RZ2S3AL1S3HUB3AL12NB3RZ2SS3LSJS3LSJ2T03AL2S3LSJ2T03AL2S3AL1S2LOS3HUB3AL12NB3RZ2S3LSJ2T03AL2SS4CEIL2LO2T1S3HUB3AL12NB3RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspS3LSJ2T03AL2S3AL1S3HUB3AL13RZ2S4CEIL2LO3HspS4CEIL2LO2NB3HspSS4CEIL2LO3SPR1HS4CEIL2LO2NB3SPR1HSS4CEIL3AL32NBS3LSJS3LSJ2T03AL2S3LSJ2T03AL2SS3LSJ2T03AL2S3AL1SS2K4SS3AL1SSS3LSJ2T03AL2S4CEIL2LO3AL32NBS3LSJ2T03AL2S".
pose proof (sec_facts n ltac:(unfold AREQMAX; lia) PRIM) as (NB & RZ2 & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
    assert (LH' : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
    assert (UF : rw_cells bsegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
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
    assert (LH : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
