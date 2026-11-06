(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AKitQ.
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
Notation acache24 t := (t + 2128) (only parsing).       (* [comment removed for export] *)
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition enq_new_post (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt24 b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells bsegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt24 - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells bsegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr bsegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells bsegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells bsegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

#[using="Type"] Lemma enqueue_new_spec : forall (full : bool) (t lst b : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt24 spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0x9d9f8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (acache24 t) [C4 (Z_to_bv 64 cnt24); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt24 <= 16 -> nth_error chunks (Z.to_nat (cnt24 - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF bsegs RNG (enq_new_post full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt24 b lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x354e0) fc None m (seg_rom bsegs)).
Proof.
  intros until chunks. intros ST CEIL LO MI -> -> -> -> QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RSTK RT RB RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. Local Ltac2 Set LiaHints.tbl := fun () => "07a0?10082350123.10110082350123.10610082350123.11310082350123.11910422297078.11210422297078.11811213771118.10511213771118.99 11775166127.10311775166127.10811775166127.11311775166127.11911912744615.10211912744615.10712282866549.11212282866549.11812367362435.10112367362435.10612367362435.10912367362435.11512431607254.10312431607254.10812431607254.11312505512393.10412505512393.11012506424771.10312506424771.97 13019652484.10213019652484.1071320589867.102 1320589867.107 13415235858.10313415235858.10413415235858.10913415235858.11014081336602.10414081336602.11114081336602.11814191121987.10814191121987.11414763672662.10114763672662.10614763672662.11314763672662.11915219254896.11215219254896.1181527479463.100 1527479463.105 15721548975.10515721548975.11115867407727.11015867407727.11616553534906.10816553534906.11417071004203.10217071004203.1071752374022.103 1752374022.97  17646078182.94 17776320431.10117776320431.10617776320431.10817776320431.11417886707500.10217886707500.96 18323497078.10718718229056.11818729902251.10318729902251.10818781667829.11018781667829.11618867207222.10318867207222.97 18930958230.94 19047372292.10319047372292.10819118515698.11319118515698.11919358200107.10219358200107.10719515728436.10319515728436.97 19728240785.11119728240785.11719967583878.11319967583878.11920854954799.10220854954799.1072120151001.110 2120151001.116 2132821131.119 21615035051.10021615035051.10521638840877.11021638840877.11321638840877.11821638840877.11921651633935.10321651633935.97 21878215663.11221878215663.11821918414723.10221918414723.10721918414723.10921918414723.11522161629359.10022161629359.10524633095682.10024633095682.10525098853573.10825098853573.11425281518355.11925314760359.10325314760359.10825661013931.10325661013931.10825878270254.10225878270254.10725878270254.10925878270254.11525993202438.11325993202438.11926081728704.11826083973675.10226083973675.10726944398891.11226944398891.11827233233268.1192724243422.112 2724243422.118 27345537325.11327609489678.10627609489678.11228546751915.10328546751915.10828751896950.10729389398518.10829518211028.10429518211028.98 30842648281.11030842648281.11630863979691.10330863979691.10831083784452.10331083784452.10831286525686.10831286525686.11932004012422.11332138622763.11032138622763.11632473033413.10832473033413.11432649392770.10232649392770.10733039531175.10333039531175.10833677903874.10333677903874.10833677903874.11333677903874.11933725004155.11333725004155.11934482413739.10334482413739.10834482413739.11334482413739.11935212070530.10835212070530.11435268010949.10835268010949.11435764571985.10635764571985.11035764571985.11135764571985.11235764571985.11635764571985.1183591008555.102 3591008555.107 36115622446.10236115622446.10736115622446.10936115622446.11536425635733.10136425635733.10736716916907.11236716916907.11836836562166.10536993589379.10336993589379.10836993589379.11036993589379.11637109276548.10137109276548.10637478275932.11037868945378.11837951031538.11338150590251.10138150590251.10638150590251.11338150590251.1193830991471.112 3830991471.118 3832027923.119 38327491723.10338327491723.97 38650006390.10638650006390.11938860591861.11238860591861.1183945979267.102 3945979267.107 3945979267.109 3945979267.115 39565726113.11339565726113.11940605904854.10340605904854.10840818989526.10440818989526.98 41809558659.10041809558659.10541809558659.10841809558659.11441956975377.11141956975377.11742240553391.10342240553391.10842240553391.11342333175588.10842333175588.11442828922350.10442828922350.10542828922350.11142828922350.11242828922350.11842828922350.98 43059283003.92 43060403331.10343060403331.10843060403331.11043060403331.11643151507489.10143151507489.10743987951406.10243987951406.10743987951406.10943987951406.11544021460374.10344021460374.97 4474788558.119 44757967521.11345219141890.10345219141890.10845219141890.11345412913494.10245412913494.10747489664620.10247489664620.10847650684435.11948185458843.10448185458843.10548185458843.11148185458843.11248185458843.11848185458843.98 48445925628.10148445925628.10748480135152.11248480135152.11848722578991.10148722578991.10648722578991.11348722578991.11948843461303.10448843461303.11248843461303.11848843461303.98 48930319418.10748930319418.11349141338643.10949141338643.11549242818135.10349242818135.97 49345641752.10049345641752.10649388040153.11049388040153.11649996111275.10349996111275.10849996111275.11350295509468.11750295509469.10950295509471.11250295509471.11850526502779.11350669429877.10350669429877.97 50915327839.11250915327839.11851000560815.11251000560815.11851007082073.11251007082073.11851246144882.11251246144882.11851345202948.10451345202948.11051356649574.10351356649574.97 51481786499.10351481786499.10851481786499.11051481786499.11651747557201.10451747557201.10551747557201.11051747557201.1115244888359.105 5244888359.111 52565067731.10052565067731.10152565067731.10252565067731.10352565067731.10452565067731.10552565067731.10652565067731.10752565067731.10852565067731.11052565067731.11152565067731.11252565067731.11352565067731.11452565067731.11652565067731.11852565067731.11952565067731.98 52624921519.10352624921519.10852793185963.10352793185963.10852793185963.11353289372016.11053289372016.11653767577775.10153767577775.10653767577775.10853767577775.11455643443280.10255645540427.96 55887383951.10855887383951.11455989853626.10255989853626.96 56216855090.11956228262055.10156228262055.10656428783466.10456428783466.10556428783466.11156428783466.11256428783466.11856428783466.98 56439567680.116565324930.101  565324930.106  565324930.113  565324930.119  56714183894.10056714183894.10556717501381.10856717501381.11457080844137.11957165168630.10857743577986.10257743577986.10758273841247.1125847843499.100 5847843499.105 58528603905.10858528603905.11458804815878.10158804815878.10758804816386.10058804816386.95 58899268058.10458899268058.11058931693703.10458933790875.98 59109042223.10259109042223.10759314873579.10159314873579.10259314873579.10359314873579.10559314873579.10859314873579.96 59314873579.97 59314873579.99 59395809188.11459483211481.11259483211481.11859536183085.11359536183085.11959584255094.11259584255094.11859585269547.10159585269547.10660025031335.10360025031335.10860225445285.10460225445285.10560225445285.11160225445285.11260225445285.11860225445285.98 60554839223.11961521325654.10261521325654.10761523295858.10461523295858.98 61542199749.11961917199020.10061917199020.10561917199023.10861917199023.11462099560040.10362099560040.97 63235321900.10463235321900.10763235321900.11363235321900.99 63314293035.10263314293035.10763418925148.10663418925148.11263691921412.10363691921412.10864593875639.10464593875639.10564593875639.11164593875639.98 6514018009.112 6514018009.118 65276466908.11165276466908.11765276466911.10565276466911.10965276466911.11065276466911.11566397384571.11366397384571.11966541015119.10866541015119.11466759593561.11266759593561.11867388853175.10567388853175.11167388853175.11267388853175.11867600552182.11067600552182.11667800801447.10267800801447.10767841563051.10067841563051.1057008858884.100 7008858884.105 7793793313.113 7793793313.119 8233180530.105 8233180530.111 835094361.112  835094361.118  8581623554.103 8581623554.108 8879850866.113 8879850866.119 9311109081.112 9311109081.118 9552935473.119 9581476779.103 9581476779.108 9581476779.113 9581476779.119 983240324.102  983240324.107  9869190602.103 9869190602.97  9910599595.103 9910599595.108 9954448086.103 9954448086.108 9954448086.113 9954448086.119 998721837.107  998721837.113  00000@00P00U00Z00c00l01101601F01V01[01`01a01f02T03I03J03O03P03U03^03g04004904B04K04T04Y04^04n05>05C05H05M05R05^05j06606>06F06O06X06a06j07207:07;07@07E07J07R07Z07c07l08<08L08Q08V08[08c08k09309;09D09M09]09i0:90:I0;70;l0<10<60<;0<@0<E0<N0<W0<g0=70=<0=A0=F0=K0=T0=]0=m0>=0>F0>O0>T0>d0?40?90?>0?C0?H0?Q0?Z0?b0?j0?k0@00@10@60@F0@V0@[0@`0@e0@j0A60A70A<0AL0A\0Ad0Al0B40B<0BE0BN0BZ0Bj0C:0CJ0CZ0Cc0Cl0D50D:0DC0DL0D\0Dl0E<0EL0EQ0EV0E_0Eh0F80FH0FM0FR0Fb0Fn0G70GG0GW0G`0Gi0Gn0H30H40H90H>0HC0HL0HU0HZ0H_0Ho0I?0ID0II0IJ0IK0IT0I]0Ib0Ig0Il0J10J60J;0JK0J[0Jc0Jk0K30K;0KC0KK0K[0Kk0L;0L<0LA0LB0LG0LL0LQ0LV0L[0Ld0M40MD0MI0MN0MV0M^0Mj0N30N<0NL0NX0OF0P;0P<0PA0PB0PG0PW0Pg0Q00Q90Q>0QC0QD0QI0QJ0QO0QT0QY0Qi0R90R>0RF0RN0RW0R`0Ri0S20S;0SD0SL0SM0SR0SS0SX0S]0Sb0Sj0T20T:0TB0TG0TL0TT0Td0Ti0Tn0U70U@0UI0UN0US0U_0Ud0Ui0Un0V30V80V=0VB0VG0VO0VW0Vg0W70W<0WA0WF0WK0WP0WU0WZ0W_0Wd0Wi0Wn0X30X40X90XB0XK0X[0Xk0Y00Y50Y:0Y?0YD0YI0YN0YS0YX0Y]0Yb0Yg0Z00Z90ZB0ZK0ZP0ZU0[60[O0[P0[U0[V0[[0[`0[e0[j0[o0\40\90\>0\C0\H0\M0\R0\W0\\0\a0\f0\k0]00]50]:0]?0]D0]I0]N0]S0]c0^30^C0^S0^X0^`0^h0_00_80_@0_H0_Q0_Z0_j0`:0`j0aR0a^0a_0ad0am0b60b?0bH0bQ0bZ0bf0bk0c00c90cB0cK0cT0c]0cf0d60dF0dK0dP0dU0de0e50ec0fX0f\0f`0fd0fh0fm0g20g=0gH0gX0gh0h40hU0ha0hl0i80iG0iT0i`0il0j50j>0jC0jH0jQ0jZ0jj0k:0k;0k@0kP0k`0l00l@0lP0l`0mX0ma0mj0n30n<0nA0nI0nQ0nY0na0nf0nk0o30o;0oC0oK0o[0ok10010510:10?10D10I10N10S10\10e10j10o11411911>11C11H11M11R11W11`11i11n12312812=12F12O12P12U12e13513:13?13O13_13h14114:14C14H14M14V14_14h15115:15J15Z15_15d15i15n16316816H16X16a16j17317<17A17FS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3LCH3HB0S3LCH3HB0S3LCHS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHSS3LCHS3LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR3K2'3K3'S2NB2L03LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR2K02K22K3SS3LCHSS3LCHS4CEIL2LOS4CEIL2LOS3LCH3TALS3LCH3CNTS3LCH3CNTS3LCH3CNTS3LCH3CNTS3HB0S3HB0S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3LCHS3LCHS2L03LCH3DTLS2L03LCH3DTLS2L03LCH3DTLS3LCH2B0S3LCH2B0S4CEIL2LOS4CEIL2LOS3LCH3TALS3LCH3TALS3LCH2B0S3LCH2B0SS3LCHS3LCHS3LCHS3LCH2B0S3LCH2B0S3LCH3HB0S3LCH3HB0S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3LCH3CNTS3LCH3CNTS4CEIL2LO2L13LCHS2L03LCH3DBLS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR3K2'3K3'S2NB2L03LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR2K02K22K3S3LCHS3LCHS3LCHS3HB0S3HB0S3LCH3DTBS3LCH3DTBS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3LCHS3LCHS3LCH3HB0S3LCH3HB0S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCH3DTBS3LCH3DTBS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3LCHS3LCHS3LCH3IXSS3LCH3IXSS3LCH2B0S3LCH2B0SS3LCHSS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3SPRS3SPRS3LCHS3LCHS2L03LCH3DTLSS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3LCH3HB0S3LCH3HB0S2L03LCH3DBLS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2B1S4CEIL2LO3LCH2B1S3LCH3HB0S3LCH3DTBS3LCH3DTBS3LCHS3LCH3CNTS3LCH3CNTS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO2L13LCHS4CEIL2LO2L13LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3HB0S3HB0S4CEIL2LO2L13LCHS2L03LCH3DTLS3LCH3HB0S4CEIL2LO3LCH2B1S4CEIL2LO3LCH2B1S3LCH3DTBS3LCH3DTBS3SPRS3SPRSS3LCHS3SPRS3SPRS3LCH3HB0S3LCH3HB0S3LCHS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHFFS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS4CEIL2LO3LCH2B1S4CEIL2LO3LCH2B1S4CEIL2LO2L13LCHSS3LCHSS3LCHS3HB0S3HB0S3LCHS3LCHS3LCH3DTBS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3LCH2B0S3LCH2B0S2L03LCH3DTLS3LCH3CNTS3LCH3CNTS4CEIL2LO2L13LCHS2L03LCH3DTLS3LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR3K2'3K3'S2NB2L03LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR2K02K22K3SS3LCHSS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LOS4CEIL2LOS3LCHS3LCHSS3LCHSS3LCHS3LCHS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCH2B0S3LCH2B0S3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCH3HB0S2LO3LCHSS3LCHSS3LCHS3LCHS3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3LCHS3LCHS2L03LCHS4CEIL2LO3LCH2T1S3SPRS3SPRS3LCH3HB0S4CEIL2LOS4CEIL2LOS3LCHS3LCHS2L03LCH3DTLS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH2B0S3LCH2B0S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHSS3LCHS3LCH3DTBS3LCH3DTBS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS3LCH3HB0S3LCH3HB0S3LCHS3LCHS2NB2L03LCH3CNT2T02T13TAL2K02K21HS3LCH3CNT2T02T13TAL3K2'1HSS3LCHSS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCH2B0S3LCH2B0S2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3LCH3CNTS3LCH3CNTS4CEIL2LO3LCH2B1S4CEIL2LO3LCH2B1S2NB2L03LCH3CNT2HB3TAL3SBP3DTB3DTL3DBL3IXR2K02K2S3LCH3CNT2HB3TAL3SBP3DTB3DTL3DBL3IXR3K2'S2L03LCH3DBLSS3LCHS3LCH3TALS3LCH3TALS3LCH3TALS3LCH3TALS3LCH3TALS3LCH3TALS2L03LCH3DBLS3SPRS3SPRS3LCH3HB0S3LCH3HB0S4CEIL2LOS4CEIL2LOS3LCH3DTBS3LCH3DTBS4CEIL2LO2L13LCHS4CEIL2LO2L13LCHS3SPRS3SPRS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR3K2'3K3'S2NB2L03LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR2K02K22K3S2NBS2NBS2NBS2NBS3LCHS3LCHS3LCH2B02B1S3LCH2B02B1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3NB13LCH2K0S3LCH2K12NB3CNT2B03NB03K2'3K3'2K4S3LCH3CNT2K2S3LCH2B02K3S3NB13LCH2K4S2NB3LCH3NB02K0S3LCH3CNT3K2'S3LCH2B03K3'S2L03LCH3DBLS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCH3HB0S3LCH3HB0S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1SS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S2NB2L03LCH3CNT2HB2T03SBP2B03DTB3DTL3DBL3IXR2K02K22K32K4S4CEIL2LOS4CEIL2LOS3LCH3HB0S3LCH3HB0S3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS3LCHS3LCHS2LO3LCHS2LO3LCHS2LO3LCHS2LO3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3HB0S3HB0S3LCHS3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCH3HB0S3LCH3HB0SS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3HB0S3HB0S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCH3HB0S3LCH3HB0S3LCH3DTBS3LCH3DTBS3SPRS3SPRS3LCH3DTBS3LCH3DTBS3LCH3DTBS3LCH3DTBS3LST3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCHS3LCHS3HB0S3HB0S3LCHS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LOS4CEIL2LOS3LCH3TALS3LCH3TALS3LCHS3LCH".
pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  carve_frame 64%nat ST.
  destruct full.
  - (* [comment removed for export] *)
    destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1).
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read bsegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep. step.                   (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [|exfalso; lia].        (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2'; zify_cond K2'; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt24 + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt24 + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read bsegs _ _ chunks (cnt24 + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt24 + -1))) CH ltac:(replace (cnt24 + -1) with (cnt24 - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [|exfalso; lia].        (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_new_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition enq_append_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C nb fst lst qb hm n nx bsz cnt lo : Z) (hs : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 (qb + n))]
    /\ rw_cells bsegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (bsz + n)); C8 (Z_to_bv 64 (cnt + 1))]
    /\ u64arr bsegs m' (lst + 24) (hs ++ [Z_to_bv 64 hm])
    /\ (exists bs, rw_cells bsegs m' (lst + 24 + 8 * (cnt + 1)) [CB (Z.to_nat (8192 - 24 - 8 * (cnt + 1))) bs]).

#[using="Type"] Lemma enqueue_append_spec : forall (C lst cnt : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (hs : list word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 C -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells bsegs m C [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> qb + n < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 ->
  rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 cnt)] ->
  0 <= cnt < Q_BATCH -> 0 <= bsz -> bsz + n < 2^63 -> 0 <= nx < 2^64 ->
  u64arr bsegs m (lst + 24) hs -> length hs = Z.to_nat cnt ->
  (exists bs, rw_cells bsegs m (lst + 24 + 8 * cnt) [CB (Z.to_nat (Q_BATCH_BYTES - 24 - 8 * cnt)) bs]) ->
  iclr C 32 -> C + 32 <= ATOP -> AIMG_HI <= lst -> lst + Q_BATCH_BYTES <= ATOP ->        (* [comment removed for export] *)
  (C + 32 <= lst \/ lst + Q_BATCH_BYTES <= C) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG C 32 -> rng RNG lst Q_BATCH_BYTES ->
  evtF bsegs RNG (enq_append_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C nb fst lst qb hm n nx bsz cnt lo hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x354e0) fc None m (seg_rom bsegs)).
Proof.
  intros until hs. intros ST CEIL LO MI -> -> -> QC NB QB QBN N HM FST LB CNT BSZ BSZN NX LA LEN LJ C0 C1 L0 L1 DJ RIMG RSTK RC RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (C + 24, C + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  destruct LJ as [junkt LJ]. Local Ltac2 Set LiaHints.tbl := fun () => "0220>10667183810.9010690961731.9611421678270.8811912744615.8711985132563.8712367362435.8612367362435.9213021749692.8713583744403.8814083433762.9614362685148.9214961824965.931527479463.85 17646078182.7817776320431.8617776320431.9117854195977.9118321399886.8718902906886.9619049469500.8821364814270.8521602767192.9621790604032.9621918414723.8721918414723.9222293241861.952269199934.87 23339081790.8624630998586.8525314760359.8825878270254.8725878270254.9226915970366.8728219042696.9328749799758.8729387301326.8829414284450.9629782367974.8331081687356.8731288622798.8731684263567.9632226578647.9332651489978.8733039531175.8733680001082.8734996152007.8535012019028.9636115622446.9236115622447.8636425635733.8436834464974.8536993589379.8736993589379.9337107179452.8637478275932.9037478275932.9237946111907.8338359781566.8838647909198.863945979267.87 3945979267.92 41344151001.9341352056401.8141352056528.824149174280.93 41809558659.8541809558659.9142027557555.9642430520254.8742831019478.9643059281971.7643060403331.8843060403331.9343917156458.9643987951406.8743987951406.9245221239098.8845734062492.8946474658803.8347342046573.8548022902103.9348726100883.8849092975902.9549345641752.8350242165840.9350337295123.8651481786499.8851481786499.9351909237829.9352567164907.8552567164907.8652567164907.8752567164907.8852567164907.9352567164907.9653078479214.9653767577775.8653767577775.9154118660373.9355104599699.8756228262055.86563227834.86  57167265742.8857745675194.8758804816386.8059314873579.8159314873579.8259314873579.8359449959825.8660025031335.8860144267157.9360223348125.966045625691.84 61663376548.9661917199020.8561917199023.9162513103751.7863205012378.8663235321900.8463235321900.9063694018620.8864744575251.8765736585424.936724373651.85 67800801447.877010956092.85 8583720762.88 8820792025.84 985337532.87  9972342994.85 00000100500A00B00V00W00\00`01401=01B01N01O01P01T01\01]01i02D02H02T02X02]02^02c02o03;03G03L03M03Q03Y03e03i04504A04\04]04a04m05605;05@05A05F05K05f05n06206:06F06G06L06P06Q06V06^06j07607707<07E07N07W07[07\07a07i08508=08A08B08G08S08W08_08d08e08j08o09409H09M09R09Z09n09o0:40:@0:E0:J0:O0:T0:Y0:^0:f0:j0;20;60;J0;K0;P0;\0;a0;e0<00<<0<H0<M0<N0<R0<e0<n0=30=70=?0=H0=M0=Q0=Y0=]0>10>90>M0>N0>R0>W0>_0>c0>hSS2HBS4CEIL2LO2C1SS4CEIL2LO3CNT3LEN2L1SS3LENS2HBS4CEIL2LO3CNT3LEN2L1S3CNT3LENS3LENS4CEIL2LO2L1SSS2LOS2LO3LENSS4CEIL2LO2L1S2NB3CNT3LEN2L02DJ2K02K12K2S2HBS4CEIL2LO2C1S2HBS3LENSS3LENS3CNT3LEN2K2S4CEIL2LO2C1S4CEIL2LO2C1S3SPRSS2LOS2LO3LENS4CEIL2LO2C1S2HBS4CEIL2LO2L1S4CEIL2LO2L1S2NB3CNT3LEN2L02DJ2K02K12K2SS2HBS4CEIL2LO2L1S3CNT3LENS3LENS3SPRSS3SPRS3LENS2NB3CNT3LEN2L02DJ2K02K12K2S2LO3LENS2LOS2LO3LENS4CEIL2LO2L1SS3LENS2HBSS3LENS3LEN2K2S4CEIL2LO2C1S4CEIL2LO2L1SS3LENS3CNT3LENS3CNT3LENS3CNT3LENS2HBSS3LENS3LEN2DJS4CEIL2LO2C1S3LEN2HBS2LOSS3LENS4CEIL2LO2C1S2LOS2LO3LENS3SPRSS3LENS3LENS3LENS4CEIL2LO3CNT3LEN2L1S3LENS3LENS3LEN2DJS4CEIL2LO3CNT3LEN2L1SS3LENS4CEIL2LO2L1S3LENS3LENS3LENS3LENS3LENS3LENS3LEN2HBS2LOS2LO3LENS2L0S4CEIL2LO3CNT3LEN2L1SS3SPRS4CEIL2LO2L1S3SPRS2NBS2NB3LEN2K0S3CNT3LEN2K1S3CNT3LEN2K2S3LENSS2L0S4CEIL2LO3LEN2L12K2S3CNT3LENS3LENS2LOS2LO3LENS3CNT3LENS3LENS2LOS2LO3LENS2HBS4CEIL2LO3CNT3LEN2L1S3LEN2DJS4CEIL2LO3CNT3LEN2L1SS2HBS3SPRS3LEN2K2S2HBS3LEN".
pose proof (stk_of_cb _ _ _ _ LJ ltac:(lia)) as TJ. clear LJ junkt.
  carve_frame 64%nat ST.
  do 8 step.                                   (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
  step. step. step. step. if_cases K1; zify_cond K1; [|exfalso; lia].   (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; [exfalso; lia|].          (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  replace (Z.shiftl cnt 3) with (8 * cnt) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. zstep.                         (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (stk_split bsegs mm (lst + 24 + 8 * cnt) (lst + 24 + 8 * cnt + 8) _ TJ ltac:(lia)) as [TJ0 TJ1];
    destruct (stk_cb mm _ _ TJ0 ltac:(lia)) as [junk8 E8] end.
  clear TJ TJ0. replace (Z.to_nat (lst + 24 + 8 * cnt + 8 - (lst + 24 + 8 * cnt))) with 8%nat in E8 by lia.
  replace (lst + 24 + 8 * cnt) with (lst + 8 * cnt + 24) in E8 by lia.
  step.                                        (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. zstep. step.                           (* [comment removed for export] *)
  do 9 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold enq_append_post. finish.
  - eapply u64arr_snoc; [exact LA|]. rewrite LEN. replace (lst + 24 + 8 * Z.of_nat (Z.to_nat cnt)) with (lst + 8 * cnt + 24) by lia. exact E8.
  - lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TJ1 ltac:(lia)) as [bs Hbs] end.
    exists bs. replace (lst + 24 + 8 * cnt + (8192 - 24 - 8 * cnt) - (lst + 24 + 8 * cnt + 8)) with (8192 - 24 - 8 * (cnt + 1)) in Hbs by lia.
    replace (lst + 24 + 8 * cnt + 8) with (lst + 24 + 8 * (cnt + 1)) in Hbs by lia. exact Hbs.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
