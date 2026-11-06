(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
AKit AKit2 AModelFacts ASecFacts ASec ASecFrame AFreeModel AFreeRep AFreeGeo AFreeRead F_afree_tail F_afree_icpt F_afree_icptR F_afree_arep F_afree_arepR AFreeStoreK AFreeStore
AFrameD ASF_kit ASF_read ASF_fast ASF_store ASF_refill.
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
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
exists k, 0 <= k <= 1 /\ 6254592 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
6254592 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25807118408.1036002021247.103826536157.10 48752954456.1000000600:00D00MS2H21HS2H3S2H22H52HnS2H31H2H0".
split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
4096 <= a /\ a + 4096 <= ATOP
/\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
/\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6254592 * j <= a).
Proof.
intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
Local Ltac2 Set LiaHints.tbl := fun () => "0040=25807118408.836072040845.83826536157.8 48752954456.800000900=00A00MS2H21H2H5S2H3S2H2S2H31H2H02H5".
split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
/\ (snd iv <= 0x9f1b0 \/ 0x9f270 <= fst iv)
/\ (snd iv <= 0xa3740 \/ 0x124770 <= fst iv)
/\ (snd iv <= 0x131fc8 \/ 0x131fcc <= fst iv)) CI.
#[using="HL CI_OK"] Theorem mid_kitS : mid_stmtS DI AFK CI.
Proof.
unfold mid_stmtS. intros L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 ctx A lo lst nx bsz hs tr.
cbv zeta. intros ALO ARNG AR AQ BL HFK LIVE HIN NQM HDR B1 B13 CTX CEIL LO ms1 PM. unfold AFREE_STACK in LO.
set (ch := CSec mb ms n) in *.
set (st1 := set_live (delete p (a_live st)) st) in *.
set (QM := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)) in *.
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EAu & _ & WFch).
destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).
pose proof SCL as (SC_t & SC_c & SC_r & SC_p & SC_n & SC_st & SC_f & SC_d).
pose proof HS as HS0. destruct HS0 as (WFS & _ & SINST & PZ & SHZ).
pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
destruct (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE)
as (order & i & b1r & cxr & uw & PO & NTH & IL & LENO & WF1o & WDo & U64 & JK & PER & CH & H1 & H5 & _ & _ & _ & HUW & UJ & S1 & S2 & S3).
cbv zeta in H5, HUW, UJ, S2, S3.
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
pose proof (aobj4_int _ OT) as (_ & _ & [kT TBND] & [jT TIMG]).
Local Ltac2 Set LiaHints.tbl := fun () => "08O0>10026630731.1 10196145140.4 10313546700.2 10317707088.1 10395164824.3510395164824.4110450661196.0 10780660995.1110793671910.2110794062471.3510794062471.4110998108614.211126616693.0  11484570712.1111624421952.5 11790930421.0 11909393000.6 12028886269.4 12097687285.0 12464417781.0 12612293896.6512861923704.1312866091207.8 12877090629.1 12978782934.2113097809467.1 13247393063.2 13296790518.1913296790518.2413296790518.2813296790518.2913310964772.2513338703576.3513338703576.4113387026774.2113432448837.8 13440155621.7 13519333479.2 13797909889.1814001734711.2 14010618241.1414010618241.2514043501308.5 14128416780.2 14470160884.2 15211289497.9 1522106012.1  15259511169.1 15339307381.0 15453126219.1 15518689194.2115518689194.2515522672629.0 15628063534.6 15628696790.2115630524557.5 15637857749.1 15646064245.0 15653624221.5 15769036414.1015835817897.0 15870411829.2816470472636.4 16475459476.2516534157257.1 16656649474.4 16789719553.3 1685717371.0  16884868271.2 17114841083.2517114851612.2 17195587061.0 17376957532.1817520992186.2 17569436502.2117876585497.9 18063706004.251809120150.21 18108944683.1418214196981.0 18777878251.4 19103934226.7 19190814485.1 19533222981.0 19661371593.1 1976232904.3  20055855553.3 20132172469.0 20253841909.0 20324533793.1420324533793.2520780272588.0 21045873636.2521198318055.3121198318055.3221200416232.1821200416232.2121201691374.9 21517512885.0 21549609119.2 21757214722.1921842373400.5 21927406558.9 22014172427.5 22171511443.8 22651993467.2522660696137.4 22876177764.2522947759178.7 23219059796.2523539635759.4 23556526996.2523888351508.2524097474916.142424857170.2  24386447584.112451983477.0  24522399417.2624960430335.1 25027101548.1 25161805257.6525440935497.5 2594861318.21 25982480559.4 26009289556.2526017132307.1026186986357.0 26238245128.0 26306678284.4 26310377973.0 26554307614.6 26800500085.0 26831418963.5 27136281110.2127594215439.5 27594218767.5 27594218895.5 27594219277.5 27893500283.2527945449407.2 28043266037.0 28233644939.3 2833535172.8  28453283427.5 28849653061.1 28865040722.6 29161774014.3529161774014.4129279152639.4 29293492283.5 29858754933.0 29938794873.2630089315520.3430122402196.2530213944567.2 30423646092.2530463451465.0 30515072832.3430591451849.0 30908703488.3 30975407276.1 31012612437.0 31404605725.8 3161907580.4  31836704053.0 31854741868.3431899909673.5 31953063638.2132351896522.1232395334108.6 326098708.25  32776955779.4 32837901993.263286806506.21 3286806506.25 32921143846.2133209929600.7 33566802644.4 33671115282.5 33802113362.2 33807609477.0 33814714644.2533896070369.2 34133706697.7 34438901183.5 34521219823.7 34589924213.0 34737456555.5 34773289461.0 34811499015.9 34877400823.2 35133727527.2 35295170995.3535295170995.413547638373.7  35544842516.2535658482041.263567119949.23 35694103779.2 36107973012.2536127204876.253617535950.9  36313061991.1 36386552263.5 36386552283.5 36386552285.5 36388649437.5 36714295519.2 36732773230.1 36958550341.1 37158056949.0 37284170245.1 37558919954.2 37648179061.0 37932502460.4 38436634709.0 38692635477.0 38948636245.0 39012636437.0 39076636629.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39332637397.0 39349303700.2539396637589.0 39412637669.0 39716638549.0 39807547359.2540038943072.1140192835119.2 40438228290.3 40561793063.9 40794405779.1841023691513.2641107849968.3 4184269202.2  419436314.7   419517597.6   42031591399.1 42063720630.5 4233523261.2  42362891158.2142379348341.0 42411609006.0 42703802337.1442703802337.2542989238132.2 43195871047.2543268453396.4 43332231982.1 43487657398.2143583853560.6 43593744991.2 43701890370.1943760733614.1 43903962786.1 44064759366.2144180196223.3 44985545750.5 44985546260.5 44985546388.5 44985547540.5 45161700303.6 45161700303.7 45164012108.6 45420083828.3 4576132444.16 45800157388.2545858738389.0 4588927050.2  45923156329.2645966287030.2146111090549.0 46133628016.3446178793218.2 46182202218.2146182202218.2546384744827.2546490978145.1446490978145.254650569643.5  46544065309.1446544065309.2546653515486.1 4678526621.14 46968447212.5 47007070456.3 47010513865.0 47262857684.6547482395858.3747491873821.7 47872845720.3 47993005860.2548182876821.1 4822555979.25 48238116919.2 48324593020.5 48418518089.0 48674518857.0 48683248534.2149135537766.8 49314520777.0 49655347078.3549655347078.4149785575052.9 49826522313.0 5004942408.3  50203955267.1 50210523465.0 50338523849.0 50410131434.7 50535502965.0 50713924820.2550718868213.0 50850525385.0 50930202724.2551106526153.0 5143745345.3  51607519243.2 51746528073.0 51793199619.1451946534344.3 52036015637.0 52036032852.2552058772710.2152169594139.5 52194529417.0 52324826299.2552368270964.2 52386529993.0 52392875668.5 52555466551.4 52569147371.1952569147371.2152569147371.2352569147371.2452569147371.2552569147371.2752569147371.2852569147371.2952722334054.2152895507081.4 53025787526.2153045873664.5 53226283926.2153238998938.2 53330317708.2553341058949.5 53387318241.1053410533065.0 53543486193.1 53777123061.0 53881886761.5 53900514677.0 54175347796.2554178535369.0 54275345606.1954758580605.2054758580605.2254758580605.2454758580605.2654758582002.1154765217882.2154765217882.2555112225729.3 55162509369.7 5517988864.34 55186704028.1 55221209172.4 55330538825.0 55450037493.0 55458539209.0 55458692139.4 55588686165.0 55610495036.4 55842540361.0 55983921528.1156237613590.2156350333127.4 56354541897.0 56435648472.1156468647413.0 56482821952.3456701989985.3 56775404277.0 56866543433.0 56938635019.3556938635019.415695761684.25 56994543817.0 57035045711.2 57378544969.0 57433925909.1857442545161.0 57506545353.0 57570545545.0 57574598994.1957717400998.8 57762546121.0 57826546313.0 57859594769.1457859594769.2557890546505.0 58002546937.0 58066547129.0 58107925871.1958107925871.2158107925871.2558107925871.2658107925871.3458146547273.0 58370997033.0 58466548233.0 58530548425.0 58658548809.0 58706241669.65588087689.1   58809045462.1 58914549577.0 58969035956.2 59234401204.6559382964098.1959554551497.0 5960416717.3  59793447252.1059810552265.0 59905684263.1 60051611180.1 60066553033.0 60186513396.2 60198051703.2 6031146182.21 60322553801.0 60406657558.2160412371595.6 60538605798.2160699326563.3560699326563.4160726687833.8 60752849319.2 6091747063.15 60989765334.2161090556105.0 61097659196.5 61116988062.1161251344357.3061346556873.0 61497988483.9 61552696794.8 61689938805.0 61807763572.4 61934999861.0 62008754397.8 62015290976.3562015290976.4162103679700.2562118365109.0 62202748743.1862208013214.5962242559561.0 62274559721.0 62315020900.2562370559945.0 62498560329.0 62754561097.0 6281292339.19 6281292339.21 6281292339.25 6281292339.26 6281292339.34 62842451974.2163114028116.2563292970900.25636494581.0   63662649864.1963662649864.2363662649864.2763662649864.2863662649864.3463745937942.2163991198558.6 63991199562.6 63991200330.6 63991200458.6 63997075330.1964192377451.4 64363103972.2564748193653.0 64763960740.4 64931558901.0 65054950517.0 65250602667.3 65253966880.1 65325072520.3 65403404180.2565447104936.8 65580437378.1965905589530.9 66048936517.1 66149329551.2666151427713.2166151427842.1666151427842.1766151427842.1866263364923.1 66459511919.2 66604473333.0 66985451747.8 67762809634.1 67934911766.2168022559995.4 68179776204.0 68223262561.1468223262561.257043641721.26 7177947379.35 7177947379.41 7215606014.6  7366518005.0  7673274869.0  7722623749.1  7739443299.8  7807322142.4  8038629874.9  8090163211.2  8196913479.8  8306928481.14 8306928481.25 8311111488.34 8480082788.25 8570339392.26 8570341198.11 8590582695.2  8592593028.2  8936802302.2  8938650181.21 8938650181.25 8938650181.26 9161320822.3  9505972408.1  9933288150.3  00000100800=00>00J00N00O00^00d01401<01L01M01]01b01c01m02702802902F02X02f02g02m02n02o03>03?03@03A03B03N03R03X03c03k03l04:04;04A04G04H04I04J04V04W04X04Y04Z04b04c04d04i04o05:05;05<05A05H05I05d05e05f05g05h05i05j05k06606706806B06H06N06Z06[06a06b06c06d06n06o07007107207307407507607707807>07^08B08U08g09209309409909:09C09H09S09^09h09i0:00:10:20:30:40:C0:G0:S0:T0:[0:\0:]0;60;70;=0;>0;?0;J0;K0;L0;M0;N0;O0;P0;W0;]0;j0<70<D0<Q0<\0<]0<^0<c0=60=70=80=@0=P0=^0=_0=`0=a0=h0=m0=n0=o0>90>:0>?0>@0>G0>H0>I0>Q0>R0>S0?10?20?80?G0?H0?I0?S0?h0@00@10@70@C0@D0@E0@F0@G0@H0@I0@U0@Z0@f0@g0@h0@i0A50A60A70A;0AG0AO0AP0AW0Ao0B00B10B;0BK0BL0BW0Bb0Bm0C90C:0C;0C<0C=0C>0C?0C@0CA0CB0CC0CD0CE0CF0CG0CH0CI0CJ0CK0CL0CM0CN0CO0Cg0D30D40D90DH0DI0DP0DW0DX0Dc0Dk0Dl0Dm0E10E70E80E90E:0E;0E@0EP0EQ0ER0EX0Ee0Ef0Ek0El0Em0F30F40FA0FN0F[0Fh0G40G<0GE0GJ0G]0Gg0Gh0Gi0H00H@0HA0HF0HG0HO0HP0H[0H\0H]0H^0Hg0I00I10I70I80I90I:0ID0Ic0Ij0Io0J50J60JA0JB0JC0JD0JE0JK0JW0JX0Jh0K00K?0K@0KA0KB0KC0KD0KP0KQ0KR0KS0KT0KZ0K[0K\0K`0Ka0Kn0Ko0L00L10L70L?0L@0LK0LL0LM0LN0LO0LP0LQ0LR0LS0LT0LU0LV0LW0L]0La0M10M80M>0MC0MM0MU0M_0M`0Me0Mf0Mg0Mh0Mi0Mj0N00N>0NS0Nl0O=0OF0ON0OO0OP0O\0Oa0Ob0Oc0Od0Oe0Of0Og0Oh0Oi0Oj0P:0P@0PI0PJ0PZ0P[0P`0Pd0Pe0Pf0QD0QQ0QR0QS0QT0QU0QZ0Q[0Q\0Q]0Qb0Qm0Qn0Qo0R00R10R20R30R40R50R60R70R80R90R:0R;0R<0R=0R>0R?0R@0RA0RB0RC0RD0RI0RJ0RN0RV0RW0RX0RY0RZ0R[0R\0Rb0Rc0Ri0S20S80S<0SH0SW0SX0S]0Sc0Sd0Se0T10TP0TQ0T\0Tg0Th0U20U30UO0U`0Uj0Uk0Ul0V=0WI0WJ0WK0WQ0WR0WS0WT0WU0WV0WW0WX0WY0Wi0Wj0Wk0Wl0Wm0Wn0Wo0X00XN0XT0X_0Xj0Y50Y@0YE0YF0YG0YH0YI0YJ0YK0YL0YM0YN0YO0Yg0Yl0Z70Z80ZR0Z_0[70[E0[S0[T0[U0[V0[c0[d0[j0[k0[l0[m0[n0\50\A0\E0\J0\K0\L0\M0\Z0\_0\i0\m0];0]<0]=0]B0]C0]W0]d0]i0]m0^10^20^30^B0^I0^J0^KSS2Q52Q6S3RSPSS4TIMG2Y12Y2S2Y2SS2WR2WB3OPi3OPsS4TIMGS3MSB4SC_t2Y12Y2S3KBM2Y2S4TBND4SHF24SHF3SS3RHI3RSP3FIT2P5S3MSBSS3JCE4JMSBS3RSP4Hc''SSS3SHE3SHL3EGQS4JMSB3JL13KEJ3KCJS3RHI3RSP4Hc''SS4TIMGFFS4FBND3SHB4DBNDFFFSS4TIMG2Y12Y2S2Y2S4TIMGS3SHL2HH2MMS3RHI2F3FS3SHE3SHP4SHLOSS4SHF2S4SHF2FFFS3RHI3RSP2P5SSSSS3DTF2D1FSS3MSBS4TIMGS2NB3NMS2N6SSS3MSBS2WR2OPSS3FKO3FKi3AR81H2H02H42H52H9FSSFFSFS4CEIL2LO1HFSS3SHE4SHHIS4Hc''S4TIMGS3RHI3RSP2P5SS4TIMGSSFS1D3RI32P6SSSFFSSSSSS4SHF2S3RES3RI23RI33FA21H2H02H42H53H14S3RES3RI23RI33U0'1H2H02H42H53H143FA2S3SP21H2H02H42H52H9S2P81H2H02H42H52H9S1D3RI23RI3SFS3SHBSS2Hj1H2H0S3MSBS3SHL2Z12HHS4CEIL2LO1HS3RSP4Hc''SS1D3RSPSFSSS3MSB4SHHI1H2H0S2NBS3RHI2Q13RI4SS2Ni2SiSFS3H243H183H223H123H163H28FS4TIMGFSS3SHL2HH2MMSSFSSSS2Q52Q6S4TIMGS2WR2WB5D_n_pS2WR2WB5D_t_pS2WR2WB5D_s_pS2WR2WB5D_p_rS4CEIL2LO1HSSS3POSS3SHE3SHL4SHLO4SHHISFS3Ha'2K1S4CEIL2LO3TL22Y2S4CEIL2LO2Y21HFSSS2Ni2SiS3KBMSFS3FKi4DIMGSS3KBMSS5POS''FSS3JCE2Z3FSS2NB3KEM3KCM3RUP3UBS4SHF24SHF3SS4TIMGS2WR2WB3OPi3OPsSSS3RSP4Hc''S4NBND4SHF24SHF34SBNDS3DTF2D1FS4TIMGS4SC_p2WR2WBFSFSSFS4SC_p2WR2WBS3MSBS2Q23RI23RI3SSSS3Gs33Gs42SFFFS2Y2S4TIMG2Y12Y2S3RHI2F3SS2Ni2SiS3JCE4JAL82Z31H2H42H52H9FSS3FKi4DIMGS3Gs23Gs43Gs52SFFS4JMSB4JC_nS4JMSB4JC_rS4JMSB4JC_tS4JMSB5JC_stFSSSFFSFSSSSSSSSSSSSSSS4CEIL2LO3RES2OT3FKO3DTOS3RHI2Q13RI4FS3Hc'S1D3RI23RI33FA2SS2Ni2SiS5POS''FS3SHL2HH2MMS3SHL2HHFSS2Z2S4TIMGSSSSS3Gs5S4CEIL2LO4SHF31HFSS4TIMGS3RI23RI33FA2FS3SHBSSS4TIMGFS2WR2WB5D_p_rS2WR2WB5D_t_pS2WR2WB5D_s_pS2WR2WB5D_n_pS3RI42U03RI1S2Q13RI4S3RI13FA1S3Hc'S3KBJ3KEJ3KCJ2Z12Z3S3FKi4DIMGSSS2Ni2SiS4TBND4SHF24SHF3SS3KBMFS3DTF2D1FS4CEIL2LO1HSSSS3FKi3DTOS3FKi3DTOSS4SHLOFFSS3UBS2H11HS4MAL83SHL2NX2GE1H2H42H52H93H10S2Z32HHS3FITS4SHF2SS4CEIL2LO1HFFSSS4TIMGS4SC_f2K12K3SS3MSB4SC_t2Y12Y2S3KBM2Y2S1D3RI23RI33U0'SFSSSS3RSP3FIT2P5SSSSS4SHF2SFS2NBSS3JL12Z11H2H0FSSS4TIMGS3RSP2P5SS4CEIL2LO1HFSSSFFFFFFFFS4TIMGS2Q6S4TBND4SHF24SHF3S2Q12Q2S4TIMGS3Gs5S3FKi4DIMGS3RSP2P6S2WR2WB2OPSS3POSSSSSSS4SHF1S3RHI3RSP1H2H0S3RHI3RI13FA11H2H02P7S3RHI3RI42U01H2H03RI13FA1S3FKi3Ha'2K11H2H0S2Hx1H2H0S3DTF2D1FFS3RSP3FIT2P6S3KBMSFSSSFSFSS3FKi4FBND2K12K3S4TIMGS3RI13FA1SS3RHI3RSP3FIT2P5SS3KBMS2Q6SSS4TBND3SHE3SHL4SHLO4SHHI2Y12Y2S3SHE4SHLO2Y2SSSSS3SHLSSSS3SHBS2P52P63RSPSSSSSSSFFFFFSSSSSSSSSFSS3SHBSS2F3S3FKO2K3SFFSFFS4TIMGSS4TIMGS4JMSB2DcS4TIMGS2Y2S4TIMG2Y12Y2S1D3RI23RI33FA2FS3SHES4TIMGSFS2Hx1H2H02H4S3Ha'2K34FAL82HH1H2H02H42H93H10SS3Gs42Dc2SFS3SHL2HH2MMSS3RSP4Hc''SS4JC_t2Z12Z34JC_r4JC_n5JC_stS3MSB2Y12Y22X72X8S2Ni2Y22SiSSS4MAL82LT1H2H02H4S3MAL2NB4MSAL3NMS3ML13ML33RUP4RUP83RS13NSE3AR81H2H02H42H52H93H143H153H193H24SSS4SHF2SSSFFFFFS4TBND4SHF24SHF3SSSFFFFS2NB4SC_f3RUP3UBS3FKO3DTO4SC_dS4TIMGS2K12K33DFRS2K12K33DNFS2K12K33DTFS2K12K33DSFS3SHBFSSFSSSSFSS3Gs43Gs52Ct2SF2Cr2Cn2CsS3SHBS3SHL2HH2MMSS4RM''2AM1H2H02H42H92Q42Q7S3FKO1H2H02H4S3MAL1H2H02H43JAL3SP32F8S4RM''1H2H02H4S4AL''1H2H02H4FFSS3RHI3RI43FA1SS4TIMGFSSSS2Ni2SiS4TIMG2Y12Y2S2Y2S3EUBSSSS3RHI3RI43FA1S3SHPS2Dc2Z32Z1S2WBS3RHI3RSP4Hc''SSS3KBMSS3FKO3Ha'2K31H2H02H9S2Hx3AR81H2H0S3T16S2QSS2X1FFS3DNF2D33DSF2D4S5POS''FS".
pose proof (aobj_int _ _ OC ltac:(clear; lia)) as (Ci & _ & [kC CBND]). pose proof (aobj_int _ _ ON ltac:(clear; lia)) as (Ni & _ & [kN NBND]).
pose proof (aobj_int _ _ OS ltac:(clear; lia)) as (Si & _ & [kS SBND]). pose proof (ao_res_hi L ALO) as RHI.
unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
word_range sp SPR.
set (UB := mb + 6144) in *.
assert (EUB : UB = mb + 6144) by reflexivity.
assert (EHM : mb + 6128 = UB - 16) by (subst UB; clear; lia).
assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; Z.div_mod_to_equations; lia).
assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
rewrite EHM in PM, HDR.
pose proof (rup8_facts n ltac:(clear -NB; lia)) as (RUP & RUP8 & RUPS).
assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
/\ 0x800b6e00 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).
{ subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as (_ & _ & _ & RS1 & _ & NSE & _).
unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
destruct SHGEO as (SHE & SHL & SHP & UBS & SHLO & SHHI).
pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
pose proof NUM as NUM0. destruct NUM0 as (NB1 & NB2 & NF & NC & NM).
pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BSI & _).
unfold free_to_refill_post in PM.
destruct PM as (id & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj' & tb' & junk2 & j0
& -> & MU & WM & MI' & ST' & IDR & HDR' & FC' & SH' & STATS' & LSJ' & UW' & FL' & IAS' & IAM' & SS' & TB' & LTB' & FRS' & FRP' & FRE' & LBS' & DEP').
cbn [ms_mem MS].
replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
set (gq := shlen (rup n 8)) in *. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) m m').
{ eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo 0 0 0).
{ unfold kfactsS. unfold K_HIGH_MEM in *.
assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ. clear. intros.
rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *. rewrite ?qsz_0.
repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia]. }
pose proof (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
pose proof (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
pose proof (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
pose proof (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
pose proof (KS_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s) SC_c) as Kctx.
pose proof (KS_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
pose proof (KS_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
pose proof (KS_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
pose proof (KS_chunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kchunk.
lazymatch type of MU with munch ?W0 _ _ =>
assert (KtO : forall Ad kk, al_t L + 80 <= Ad -> Ad + kk <= al_t L + 2800 -> 0 <= kk -> disjoint_from W0 Ad kk);
[ intros Ad kk Y1 Y2 Y3; pose proof DL7 as X7; unbox X7; pose proof DL8 as X8; unbox X8;
cbn [disjoint_from]; unfold K_HIGH_MEM in *; clear -Y1 Y2 Y3 TL1 TL2 TBND TIMG LO CEIL X7 X8 SC_t MSB EUB UBS NB RUP SHLO SHHI SHE SHL; repeat (split; [lia|]); exact I |];
assert (KgO : forall Ad kk, 0x9f1b0 <= Ad -> Ad + kk <= 0x9f270 -> 0 <= kk -> disjoint_from W0 Ad kk);
[ intros Ad kk Y1 Y2 Y3; cbn [disjoint_from]; unfold K_HIGH_MEM in *; clear -Y1 Y2 Y3 TL1 TBND TIMG LO CEIL MLO ML1 ML3 KAM KBM KEM KCM KDM EUB DL1 DL4 Ni Si NBND SBND SHLO SHE; repeat (split; [lia|]); exact I |]
end.
assert (ELIVE : a_live st1 = delete p (a_live st)) by reflexivity.
assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
assert (WF' : awf L st1 X) by (apply (awf_delete_sec L st X p mb ms n st1 WF LIVE); reflexivity).
assert (RT' : arep_rt L m').
{ eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
assert (INST' : ainstance L st1 m').
{ eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
assert (THR' : athread L st1 X m').
{ unfold athread. split; [| split; [| split; [| split; [| split]]]].
- eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
- eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
- intros c' Hc'. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply KtO; clear -Hc'; lia.
- eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply KtO; clear; lia].
- exists sj'. split; [exact STATS' | exact LSJ'].
- exact UW'. }
assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
aregion_cells L st1 m' c'' /\ afreearray L st1 X m' c'' /\ aslots L st1 X m' c'' /\ aslot_shadow L st1 X m' c'').
{ intros c'' Hc''. destruct (CLS c'' Hc'') as (REG & FARR & SLOTS & SHADOW).
pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
pose proof (aregion_mod L c'' SAL) as RM''.
unfold K_NUM_CLASSES in Hc''.
assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
/\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
destruct RI as (RI1 & RI2 & RI3 & RI4).
split; [| split; [| split]].
- eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
apply Kres; try (clear -Hc'' RSP; lia); right; clear -Hc'' RSP RES RHI; lia.
- eapply afreearray_frame; [exact MUn | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
+ assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
{ unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
destruct FA1 as [FA1 FA2].
apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |]; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia.
+ assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
{ unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
destruct FA1 as [FA1 FA2].
apply Kshad.
* rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
* rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
* apply shlen_nonneg. clear -Q5 Q6. lia.
* assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
rewrite SHE. destruct SC_r as [D|D].
-- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
-- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
-
eapply (aslots_update_gen L _ m m' MUn WM st st1 X X c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
+ intros k'' Hk''. left.
pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
split; [reflexivity|]. split.
* apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | | |]; right; clear -P5 RSP RES RHI; lia.
* intros b Hb. destruct (busy_of_Some_facts X c'' k'' b Hb) as (IB & CB' & KB'). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
+ intros POS''.
set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |]; right; clear -RI4 Q1 U0 RES RHI; lia.
-
eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
+ intros k'' Hk''. left.
pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
split; [reflexivity|].
pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
apply Kshad.
* rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
* rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
* apply shlen_nonneg. clear -T16; lia.
* rewrite SHE. destruct SC_r as [D|D].
-- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
-- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; Z.div_mod_to_equations; lia] | clear; lia].
+ intros POS''.
set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
apply Kshad.
* rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
* rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
* clear -POS''; lia.
* rewrite SHE. destruct SC_r as [D|D].
-- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
-- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
}
assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st1 m' c'').
{ intros c'' Hc''. pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof (aregion_mod L c'' SAL) as RM''.
unfold K_NUM_CLASSES in Hc''.
assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
destruct RI as (RI1 & RI2 & RI3).
eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | reflexivity | reflexivity | |].
- intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
apply Kshad.
+ rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
+ rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
+ clear -POS''; lia.
+ rewrite SHE. destruct SC_r as [D|D].
* right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
* left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
- intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
{ subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
destruct FA as [FA1 FA2].
assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
apply Kshad.
+ rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
+ rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
+ clear -POS''; lia.
+ rewrite SHE. destruct SC_r as [D|D].
* right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
* left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
assert (NOTL : ~ sec_live st1 ch) by (apply (sec_not_live_after L st _ p mb ms n st1 WFS (Permutation_refl _) LIVE ELIVE)).
assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st1 c <-> sec_live st c)).
{ intros j c Hj NEj. apply (sec_live_other st p mb ms n st1 c LIVE ELIVE).
intros E. apply NEj. destruct WDo as [ND _].
apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
pose proof (ao_ptr L ALO) as OP. pose proof (aobj_int _ _ OP ltac:(clear; lia)) as (OPi & OPa & [kP OPs]). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.
assert (HS' : ASECc (sec_chunks_of st) L st1 X m').
{ unfold ASECc.
pose proof HS as HS1. destruct HS1 as (_ & _ & _ & _ & SHZ0).
split; [| split; [| split; [| split]]].
- exact WFS.
- exists order. change (a_nres st1) with (a_nres st). change (a_nsec st1) with (a_nsec st).
split; [exact PO|].
unfold K_HIGH_MEM in *.
split; [| split].
+ eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
+ eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
+ intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
*
rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL Hl)]|].
unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
destruct CH0 as (G1 & G2 & G3 & G4 & _ & _ & _ & _ & _). unfold SEC_UOFF in *. rewrite <- ?EUB in *.
replace (UB - 16 + 16) with UB in FC' by (clear; lia).
split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
- pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
- eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
replace (mb + 6128 + 24) with (UB + 8) in UJ by (rewrite EUB; clear; lia). exact UJ. }
split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia]|].
rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
replace (mb + 6128 + 16) with UB in S3 by (rewrite EUB; clear; lia).
eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia].
*
destruct (PER j c Hj) as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
assert (INj : In c order) by (eapply nth_error_In; exact Hj).
pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
destruct (sec_wf1_facts' L mb' ms' n' Wc) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & (JC_t & _ & JC_r & _ & JC_n & JC_st & _) & _).
assert (NEc : CSec mb' ms' n' <> ch).
{ intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
destruct WDo as [_ DJ]. assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
all: unfold K_HIGH_MEM in JLO, JCE.
all: pose proof (ablk_lin _ _ JLO) as (JL1 & JL2 & JL3 & JL4); unfold AIMG_HI in JL1; pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).
all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
-- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
-- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
- destruct SINST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
- unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
apply Kshad.
+ rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. Z.div_mod_to_equations. lia.
+ rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia.
+ clear -POS; lia.
+ rewrite SHE. destruct SC_r as [D|D].
* right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
* left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; Z.div_mod_to_equations; lia] | clear; lia].
- intros x Hx HFh HC.
pose proof HC as HC0.
assert (INst : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.
assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; clear -Hx; Z.div_mod_to_equations; lia).
rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; Z.div_mod_to_equations; lia| clear; lia|].
rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
+ left. rewrite !shad_div. clear -LT MAL8. Z.div_mod_to_equations. lia.
+ right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. Z.div_mod_to_equations. lia. }
assert (BL' : ablocks L st1 X (lb_remove p LB)).
{ eapply (ablocks_free_sec L st X LB p mb ms n st1 X LIVE WF ELIVE); [| exact BL]. intros y Hy. exact Hy. }
assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & FKa & [kF FBND]). unfold aobj in FKO.
pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
assert (SHB : 0x800b6e00 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).
assert (HFK' : AFK L (lb_remove p LB) m').
{ eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
- pose proof (ao_dtls L ALO) as DTO. pose proof (aobj4_int _ DTO) as (_ & _ & [kD DBND] & [jD DIMG]). unfold aobj in DTO.
pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
unfold adisj in D1, D2, D3, D4.
unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
/\ 0x800b6e00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).
{ split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
rewrite SHE. destruct SC_f as [D|D].
- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; Z.div_mod_to_equations; lia] | clear; lia]. }
destruct SHF as (SHF1 & SHF2 & SHF3).
pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
do 16 (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [lia|]); lia]
| solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
| match goal with |- ?G => idtac "FAKELEFT" G end ] |]).
apply Forall_nil.
- intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
assert (BGEOq : forall q, In q (q_loc Q ++ q_glob Q) ->
al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
{ intros q Hq. pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as (_ & _ & _ & P1 & P2 & P3 & P4 & P5 & P6 & _).
rewrite size_of_class_24 in P2, P6. unfold abatch_addr. unfold K_SPACE_SIZE in P6. change (2^37) with 137438953472 in P6.
generalize P1 P2 P5 P6 RSP; clear; intros. lia. }
assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (abatch_addr L (qb_slot q)) 8192).
{ intros q Hq. destruct (BGEOq q Hq) as [F3 F4]. apply Kres; [clear -F3; lia| exact F4| clear; lia| | |]; right; clear -F3 RES RHI; lia. }
assert (HQ' : AQUAR_at L st1 X QM m').
{ subst QM. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
change (a_qloc st1) with (a_qloc st). change (a_qglob st1) with (a_qglob st). change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
split; [| split; [| split; [| split; [| split]]]].
- split; [eapply cells_frame; [exact QK| exact MUn| exact WM| cbn [cells_size csize Nat.add]; apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia]|].
eapply cells_frame; [exact MX| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply KgO; clear; unfold AQ_MUTEX; lia].
- split; [eapply cells_frame; [exact QC| exact MU| exact WM| cbn [cells_size csize Nat.add]; unfold aq_tcache; apply KtO; clear; lia]|].
eapply (abatches_frame L _ m m' MUn WM); [exact ABL|]. intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. left. exact Hq.
- split; [eapply cells_frame; [exact GCQ| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply KgO; clear; unfold AQ_GCACHE; lia]|].
eapply (abatches_frame L _ m m' MUn WM); [exact ABG|]. intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. right. exact Hq.
- split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. Z.div_mod_to_equations. lia.
- exact CP.
- exact NUM. }
assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (ab_addr blk) (ab_size blk)).
{ intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
- destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb' & msz' & Lp & EUA & Gs)].
+ destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
unfold xb_user, xb_alloc in Ub. subst A' n'.
set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
{ intros q' Hq'. destruct (bslot_busy L st X Q CP q' Hq') as (yq & Hyq & Syq & Cyq & Kyq).
assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
{ destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia | | |]; right; clear -FIT P5 RSP RES RHI; lia.
+
assert (NEq : q <> p) by (intros ->; apply NEp; reflexivity).
assert (NEc : CSec mb' msz' n' <> ch).
{ intros E. apply NOTL. exists q. rewrite ELIVE, lookup_delete_ne by (intros E'; exact (NEq (eq_sym E'))). rewrite <- E. exact Lp. }
assert (INc : In (CSec mb' msz' n') (sec_chunks_of st)) by (eapply live_sec_in; exact Lp).
assert (INs : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
all: cbn [sec_wf1] in Gs; destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
all: unfold ablk, KLS, AIMG_HI in Gs2.
all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
- destruct (FKD cls A' n' Hin) as (K1 & K2 & K3). unfold K_HIGH_MEM in *.
pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
| clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (shad a') 1).
{ intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). unfold K_HIGH_MEM in *.
assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
| rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
rewrite SHE. destruct SC_f as [D|D].
- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
- left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
clear -HH Ha' K3 FAL8. Z.div_mod_to_equations. lia. }
split; [| split; [exact BL'| split; [exact HFK'|]]].
- split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
- eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
