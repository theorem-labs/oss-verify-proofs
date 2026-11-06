(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts ASecFacts ASec ASecFrame AFreeModel AFreeRep AFreeGeo AFreeRead F_afree_tail F_afree_icpt F_afree_icptR F_afree_arep F_afree_arepR AFreeStoreK AFreeStore
     AFrameD ASF_kit ASF_read ASF_fast ASF_store ASF_refill.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6250496 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6250496 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>25807118408.1036002021247.103826536157.10 48752954456.1000000600:00D00MS2H21HS2H3S2H22H52HnS2H31H2H0".
split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6250496 * j <= a).
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
                                  /\ (snd iv <= 0x9daf0 \/ 0x9dbb0 <= fst iv)
                                  /\ (snd iv <= 0xa2080 \/ 0x1230b0 <= fst iv)
                                  /\ (snd iv <= 0x130908 \/ 0x13090c <= fst iv)) CI.

#[using="HL CI_OK"] Theorem mid_kitS : mid_stmtS DI AFK CI.
Proof.
  unfold mid_stmtS. intros L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 ctx A lo lst nx bsz hs tr.
  cbv zeta. intros ALO ARNG AR AQ BL HFK LIVE HIN NQM HDR B1 B13 CTX CEIL LO ms1 PM. unfold AFREE_STACK in LO.
  set (ch := CSec mb ms n) in *.
  set (st1 := set_live (delete p (a_live st)) st) in *.
  set (QM := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
  destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EAu & _ & WFch).
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).   (* [comment removed for export] *)
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
  pose proof (aobj4_int _ OT) as (_ & _ & [kT TBND] & [jT TIMG]).   (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "08U0>10026630731.1 10196145140.4 10313546700.2 10317707088.1 10357162313.0 10485162697.0 10570200823.2 10707908469.0 10780660995.1110794062471.3510794062471.4110998108614.2111190051350.2111484570712.1111624421952.5 11773154516.2511909393000.6 1196071673.26 12021105364.2512028886269.4 12257431285.0 12417695618.1912612293896.6512861923704.1312866091207.8 12877090629.1 13097809467.1 13296790518.1913296790518.2413296790518.2813296790518.2913341084364.0 13432448837.8 13440155621.7 13563704212.2513795940257.1113849226562.1914001734711.2 14010618241.1414010618241.2514043501308.5 14128416780.2 14248615048.1014248862995.1014248862995.9 14250793113.6 14639337364.2515132320885.0 15211289497.9 1522106012.1  15259511169.1 15439077749.0 15453126219.1 15503147087.5 15515497321.5 15518689194.2115518689194.2515628063534.6 15630524557.5 15637857749.1 15653624221.5 15754900564.2515769036414.1015913113386.2 16020704486.2116534157257.1 16641052917.0 16656649474.4 16801639638.211685717371.0  16884868271.2 17114851612.2 1719372884.25 17240050198.2117330577750.2117374471804.1117520992186.2 17734834689.3 17876585497.9 18113523605.7 181632187.25  18326180244.251840862455.2  18587749582.3 1861022073.26 18680697845.0 18777878251.4 19074402919.1 19103934226.7 19190814485.1 19231870649.2619506922580.2519661371593.1 19710847493.1 1990627212.25 20162786534.2120228488911.2 20517235800.11205688706.19  21048865186.9 21127161141.0 21201691374.9 21549609119.2 21553614380.1 21603401536.3421742752948.2 21842373400.5 21862344309.0 21886510158.9 21888851405.9 21927396353.2 22014172427.5 22068247393.1422068247393.2522171511443.8 22208142071.7 22483864548.2522660696137.4 22941351991.2 22947759178.7 23539635759.4 24101828570.7 2424857170.2  24386447584.1124496633676.0 2460702823.2  24831184865.1424831184865.252484947455.7  2486760693.7  2487091158.5  24960430335.1 25161805257.6525440935497.5 25502561157.1125504546824.4 25982480559.4 26017132307.102611727477.0  26225946432.3426238245128.0 26306678284.4 26307031873.3 26554307614.6 2672118728.3  26831418963.5 26960244085.0 2735119093.0  27594215439.5 27594218767.5 27594218895.5 27594219277.5 27895037940.2 27945449407.2 27948118412.2528233644939.3 2833535172.8  28453283427.5 28478945574.1128865040722.6 29038208332.4 29161774014.3529161774014.4129168411648.3429279152639.4 29293492283.5 29528376821.0 29742208628.2 30280507544.3530280507544.4130289609511.1 30370828283.2530805913020.4 30908703488.3 31012612437.0 31228234864.3431404605725.8 3150388519.2  31607341260.2531760437524.2531809637600.2 31812090093.2 31824659409.6 31854741868.3431899909673.5 32351896522.1232395334108.6 32567013239.2 32648327477.0 32650118316.1 32776955779.4 32831692725.0 32837901993.263286806506.21 3286806506.25 33209929600.7 33441520534.2133566802644.4 33664443848.3 33671115282.5 33802113362.2 33896070369.2 34133706697.7 34197850293.0 34438901183.5 34521219823.7 34566302965.0 34737456555.5 34749668213.0 34811499015.9 34991432652.0 35093294278.2135295170995.3535295170995.413547638373.7  35655074153.263566823747.8  35694103779.2 3617535950.9  36386552263.5 36386552283.5 36386552285.5 36388649437.5 36548533320.3 36714295519.2 36732773230.1 36877341398.2136958550341.1 37238859556.2537317800949.0 37519011252.1737558919954.2 37807923061.0 37991288309.0 38436634709.0 38479020294.2138536497531.2538692635477.0 38948636245.0 39012636437.0 39076636629.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39282819476.2539332637397.0 39348314248.3 39349763510.2139396637589.0 39412637669.0 39484780757.0 39607582561.1439607582561.2539716638549.0 3977885045.0  39807547359.2540038943072.1140082674198.2140192835119.2 4027300116.25 40438228290.3 40499447413.0 40561793063.9 40682812661.0 40796883379.1140989569525.0 41107849968.3 4184269202.2  419436314.7   419517597.6   42010739649.3 42063720630.5 4233523261.2  42411609006.0 42489549249.3 42539092341.0 42556365140.2542989238132.2 43059711526.2 43195871047.2543268453396.4 43332231982.1 43583853560.6 43593744991.2 43672874517.0 43760733614.1 43903962786.1 44084246420.2544087822040.3544087822040.4144180196223.3 44901734804.2544985545750.5 44985546260.5 44985546388.5 44985547540.5 45161700303.6 45161700303.7 45164012108.6 4520937093.0  4536697209.26 45420083828.3 45492474916.2545727962468.254576132444.16 4588927050.2  45966287030.2145980186556.4 46178793218.2 46182202218.2146182202218.254650569643.5  46544065309.1446544065309.2546653515486.1 4665792547.7  46889859881.0 46968447212.5 47007070456.3 47106079221.0 47262857684.6547298079993.9 47397410518.2147491873821.7 47650515785.0 47803412682.3 47824300411.2547828869500.4 47872845720.3 47906516553.0 47938516713.0 48034516937.0 48162517321.0 48182876821.1 48324593020.5 48582343014.2148778993653.0 48942484859.2549125353229.3 49135537766.8 49145724149.0 49186520393.0 49314520777.0 49570521545.0 49655347078.3549655347078.4149698521929.0 49785575052.9 50203955267.1 50210523465.0 50338523849.0 50410131434.7 50555785828.2550722525001.0 50850525385.0 51362526921.0 51607519243.2 51792904453.7 51874528457.0 51973644052.2551974741890.195198996308.25 52130529225.0 52158892582.2152169594139.5 52368717924.2552386529993.0 52392875668.5 5241886528.34 52555466551.4 52569147371.1952569147371.2152569147371.2352569147371.2452569147371.2552569147371.2752569147371.2852569147371.2952594096041.0 52770531145.0 52895507081.4 53025787526.215303251829.0  53037570577.1453037570577.2553045873664.5 53154532297.0 53238998938.2 53341058949.5 53387318241.1053410533065.0 53543486193.1 53666533833.0 53881886761.5 53922534601.0 54275345606.1954376399078.2154424782016.3454765217882.2154765217882.2555078868597.0 55162509369.7 55186704028.1 55221209172.4 55330538825.0 55376578060.2555458692139.4 55588686165.0 55714539977.0 55857651414.2155983921528.1156098541129.0 5626182550.21 56350333127.4 56435648472.1156445026165.0 56610542665.0 56628391413.0 56701989985.3 56935148277.0 56938635019.3556938635019.4157035045711.2 57717400998.8 58052068246.2158107925871.1958107925871.2158107925871.2558107925871.2658107925871.345836997957.1  58391484257.1458391484257.2558658548809.0 58706241669.6558786549193.0 588087689.1   58809045462.1 58914549577.0 58966027333.0 59042549961.0 59051497895.2 59060038550.2159136172532.2 59186120947.3559186120947.4159234401204.6559490551305.0 59504205884.4 59554551497.0 59564976821.0 5960416717.3  59618551689.0 59793447252.1059874552457.0 59938552649.0 59993403125.0 60050553081.0 60114553273.0 60194553417.0 6020956344.1  60412371595.6 60514554377.0 60578554569.0 60699326563.3560699326563.4160726687833.8 6104698953.8  61097659196.5 61181322092.1 61346556873.0 61497988483.9 61552696794.8 61807763572.4 61849682805.0 61986558793.0 62008754397.8 62015290976.3562015290976.4162434560137.0 62626560713.0 6281292339.19 6281292339.21 6281292339.25 6281292339.26 6281292339.34 62842451974.2163262921558.2163662649864.1963662649864.2363662649864.2763662649864.2863662649864.3463991198558.6 63991199562.6 63991200330.6 63991200458.6 64192377451.4 64763960740.4 65031329269.0 65250602667.3 65253966880.1 65447104936.8 65455420215.3 65645737505.1465645737505.2565905589530.9 66048936517.1 66263364923.1 66282876930.1966459511919.2 66714332438.2166899560164.2566922131348.2566985451747.8 67421407124.2567719891812.2567728023110.2167762809634.1 67966192501.0 68022559995.4 68089584117.0 68316589387.257159531509.0  7214490407.2  7215606014.6  7363940729.26 7722623749.1  7739443299.8  7807322142.4  7833018869.0  8038629874.9  8090163211.2  8125337575.1  8196913479.8  8265560598.21 8278630676.25 8344820050.19 8376585492.25 8590582695.2  8592593028.2  8914958284.4  8936802302.2  8938650181.21 8938650181.25 8938650181.26 9161320822.3  9933288150.3  00000100800=00>00?00@00A00B00Q00a00i01901?01O01T01U01_01f01g02102202702D02V02d02e02f03503603703803903D03L03M03[03`03a03g03m03n03o04@04Q04b04f04g04h05405505605705805D05M05U05V05[05f05g05l05m06406906?06@06A06B06H06I06J06K06L06R06X06b06h06i07507607A07B07C07G07N07O07P07Q07[07\07c07d07e07f08008608;08G08L08\08]08h08i08j08o09009109209?09O09S09X09Y09Z09e0:20:80:B0:C0:J0:K0:U0:Y0:e0:f0:g0:h0:i0:m0;:0;C0;D0;]0;^0;j0<20<30<>0<?0<D0<E0<F0<G0<H0<I0<P0<Q0<R0<_0<l0=90=F0=G0=H0=R0=W0=j0=k0>00>80>A0>Q0>_0>d0>e0>f0>g0>h0?40?80?90?D0?E0?L0?M0?R0?Z0?[0?e0?f0?k0?o0@40@R0@S0@b0@c0@d0@e0@f0A00A10AF0AN0AO0A[0Aa0Ab0Ac0Ad0Ae0Af0B20B30B80BD0BE0BF0BG0BS0BT0BZ0B^0Bj0C20C90CF0CG0CW0Cb0Cm0D80DD0DE0DF0DG0DM0DN0DT0DU0EC0ED0EE0EF0EG0EM0EX0EY0EZ0E[0E\0E]0E^0E_0E`0Ea0Eb0Ec0Ei0Ej0Ek0El0Em0En0Eo0F00FH0FT0FZ0F[0F\0Fa0Fb0G10G20G30G40G;0G<0GG0GO0GP0GQ0GU0GV0GW0GX0GY0G^0Gc0H30H40H50HB0HC0HD0HE0HF0HG0HS0HW0HX0HY0Hf0I30I@0IM0IY0Ia0Ij0Ik0J20J70J80J90JL0JM0J]0J^0J_0Jg0Jh0Ji0K20K;0K<0KB0KC0KD0KE0KF0KP0K`0Kf0Km0Kn0L20L=0L>0LC0LD0LE0LF0LG0LH0LI0LO0LP0L[0L`0Ll0Lm0Ln0Lo0M00M@0MH0MI0MX0MY0MZ0M[0Mg0Mm0Mn0Mo0N00N40N<0N=0N>0NC0ND0NE0NK0NS0NY0NZ0N[0N`0Na0Nb0Nc0Nd0Ne0Nf0Ng0Nh0Ni0Nj0Nk0No0O?0O@0OA0OB0OI0OJ0OO0OW0Oa0Ob0Og0Oh0Oi0Oj0P00P60P;0PC0PD0PE0PQ0PR0PS0PT0P^0P_0P`0Pa0Pg0Q70Q80Q>0QG0QW0QX0QY0QZ0Q^0Q_0R=0RJ0RK0RV0R\0R]0R^0R_0R`0Ra0Rb0Rc0Rd0Re0Rf0Rg0Rh0Ri0Rj0Rk0Rl0Rm0S30S40S@0SD0SE0SF0SG0SH0SI0SM0SN0SV0SW0SX0SY0SZ0S[0S\0S]0Sf0Sg0Sh0Sl0T80TG0TL0TM0TN0TO0TZ0Te0To0U00U10UM0U^0Uh0Ui0Uj0Uk0Ul0Um0Un0Uo0V?0VE0VF0VG0VH0VI0Vg0W20W=0WH0WS0WT0WU0WV0WW0WX0X00X60X70X80XC0XD0XE0XJ0XK0XQ0XR0XS0X`0Xa0Xb0Xh0Xi0Xj0Xk0Xl0Y70Y80Y90Y>0YE0YF0YS0YX0YY0Yc0Yg0Yh0Z60Z<0Z=0ZB0ZC0ZH0ZL0ZR0ZV0ZW0ZX0Zg0Zn0ZoSS2Q52Q6S3RSPSSSFSS2WR2WB3OPi3OPsS3MSB4SC_t2Y12Y2S3KBM2Y2S4TBND4SHF24SHF3S4TIMGS3RHI3RSP3FIT2P5S3MSBSS3JCE4JMSBS2Ni2SiSS3RSP4Hc''SS3SHBS3SHE3SHL3EGQS4JMSB3JL13KEJ3KCJS3RHI3RSP4Hc''SFS4FBND3SHB4DBNDFFFSS3SHL2HH2MMS3RHI2F3SS3SHE3SHP4SHLOS3SHBSS4SHF2S4SHF2FFS3RES3RI23RI33U0'S3RES3RI23RI33FA2S3RES3RI23RI33FA2S2P8SSS3RHI3RSP2P5SSSSS2Q44RM''2Q7S4RM''2AMS3DTF2D1FS3MSBS2NB3NMS2N6SS3MSBSS2WR2OPS3MALS4TIMGSSFS4TIMGSFFSS4TIMGS4TIMGS3SHE4SHHIS4Hc''FS3RHI3RSP2P5SS4CEIL2LO1HSFS2HxS2Ni2SiSFFS1D3RI32P6SS2Ni2SiSSFS3FKi4DIMGS4TIMGS3MALS3FKi3Ha'2K1S3SHBS4MAL83SHL2NX2GESS1D3RI23RI3FFS3KBMFSSS3RHI3RI13FA1S3RHI3RI42U03RI1S2HjS3MSBSSS3SHL2Z12HHS3FKO3FKi3AR8S4SHF2S3RSP4Hc''FS1D3RSPFS3MSB4SHHIS2NBS3RHI2Q13RI4SFSSS2P7S3RHI3RI13FA1S3RHI3RSPSS3H243H183H223H123H163H28FS3FKO3Ha'2K3S2Hx3AR8FS3SHL2HH2MMSS3KBMSFFSFS2Q52Q6SSS2WR2WB5D_n_pS2WR2WB5D_t_pS2WR2WB5D_s_pS2WR2WB5D_p_rFSS3FKi4DIMGS3POSS3SHE3SHL4SHLO4SHHISS3SHLS3Ha'2K1S4MAL82LTS4CEIL2LO3TL22Y2S4CEIL2LO2Y21HS3KBMFSSFS4TIMG2Y12Y2S2Y2FS4CEIL2LO1HFS5POS''SS3KBMS3JCE2Z3FS3FKi4DIMGSS3SP3S2F8S3FKOS2NB3KEM3KCM3RUP3UBS4SHF24SHF3SS2WR2WB3OPi3OPsSFSFS3RSP4Hc''SS4NBND4SHF24SHF34SBNDS3DTF2D1FS4SC_p2WR2WBS4TIMGFFSFFS4SC_p2WR2WBSS3MSBS2Q23RI23RI3SSSS3Gs33Gs42SFSS4TIMGS2Y2S4TIMG2Y12Y2S3RHI2F3S2Ni2SiS3JCE4JAL82Z3FS3Gs23Gs43Gs52SFS4JMSB4JC_nS4JMSB4JC_rS4JMSB4JC_tS4JMSB5JC_stFFSS4TIMGSS4SHF2SS3MAL2NB4MSAL3NMS3ML13ML33RUP4RUP83RS13NSE3AR8FSSSS4TIMGS4CEIL2LO1HSSSSSSSSSSFS4TIMGSSSSSSSS4CEIL2LO3RES2OT3FKO3DTOS3RHI2Q13RI4S4TIMGFSS3Hc'SS1D3RI23RI33FA2SSSS5POS''FS3SHL2HH2MMS3SHL2HHFSS2Z2SFSSS3Gs5S3JALS4CEIL2LO4SHF31HFSS3RI23RI33FA2FSSSSS4TIMG2Y12Y2S2Y2FSS2WR2WB5D_p_rS2WR2WB5D_t_pS2WR2WB5D_s_pS2WR2WB5D_n_pS3RI42U03RI1S2Q13RI4S3RI13FA1SS2Ni2SiS3Hc'SSS3KBJ3KEJ3KCJ2Z12Z3SS4TBND4SHF24SHF3FFS3DTF2D1FSS3FKi3DTOS3FKi3DTOSS4SHLOSFFSS3UBS2H11HS3Ha'2K34FAL82HHS4TIMGS2Z32HHSS2HxS4CEIL2LO1HFS3FITSSSSSFS4TIMGSS4CEIL2LO1HS3SP2S4SC_f2K12K3SSSSS3MSB4SC_t2Y12Y2S3KBM2Y2SS1D3RI23RI33U0'SSSS3RSP3FIT2P5S4SHF2SSSS2NBS3JL12Z1SSS3SHBSSS4TIMGS3RSP2P5S4SHF2SSS3KBMSFFFFFFFFSSS2Q6S4TBND4SHF24SHF3SSSS2Q12Q2SS3Gs5S3RSP2P6S2WR2WB2OPSS3POSSSSS4SHF1S4TIMGS3KBMS3DTF2D1FSS3RSP3FIT2P6SFSS3FKi4DIMGFSSS4TIMGS3FKi4FBND2K12K3SS4TIMGS3RI13FA1S3RHI3RSP3FIT2P5SSSS2Q6SS4TBND3SHE3SHL4SHLO4SHHI2Y12Y2S3SHE4SHLO2Y2SS2P52P63RSPS4TIMGFFFFFFSSSSSSSSSSFS4TIMGFS4TIMG2Y12Y2S2Y2SSFSSS2F3SS3FKO2K3SSSSSSFS4JMSB2DcSSS2Y2S4TIMG2Y12Y2S1D3RI23RI33FA2S3SHEFFSS3Gs42Dc2SFS3SHL2HH2MMS3RSP4Hc''SSS4JC_t2Z12Z34JC_r4JC_n5JC_stS3MSB2Y12Y22X72X8S2Ni2Y22SiSSFFFFFS4TBND4SHF24SHF3S4TIMGFFFFS2NB4SC_f3RUP3UBS3FKO3DTO4SC_dS2K12K33DFRS2K12K33DNFS2K12K33DTFS2K12K33DSFFFSSSS3Gs43Gs52Ct2SF2Cr2Cn2CsS4RM''SSS3SHL2HH2MMSFS3SHBFS4TIMGSSS3RHI3RI43FA1SSS4TIMGSSFSS4CEIL2LO1HSFS3EUBS2Ni2SiSS3RHI3RI43FA1S3SHPSS2Dc2Z32Z1S2WBFS3RHI3RSP4Hc''S4TIMGSS3SHBSS3T16S2QSS4AL''S2X1FFS3DNF2D33DSF2D4S5POS''S".
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
  assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  rewrite EHM in PM, HDR.
  pose proof (rup8_facts n ltac:(clear -NB; lia)) as (RUP & RUP8 & RUPS).
  assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
                  /\ 2148232192 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as (_ & _ & _ & RS1 & _ & NSE & _).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHGEO as (SHE & SHL & SHP & UBS & SHLO & SHHI).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  pose proof NUM as NUM0. destruct NUM0 as (NB1 & NB2 & NF & NC & NM).
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BSI & _).
  (* [comment removed for export] *)
  unfold free_to_refill_post in PM.
  destruct PM as (id & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj' & tb' & junk2 & j0
                  & -> & MU & WM & MI' & ST' & IDR & HDR' & FC' & SH' & STATS' & LSJ' & UW' & FL' & IAS' & IAM' & SS' & TB' & LTB' & FRS' & FRP' & FRE' & LBS' & DEP').
  cbn [ms_mem MS].
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  set (gq := shlen (rup n 8)) in *. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
  (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo 0 0 0).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *. rewrite ?qsz_0.   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  lazymatch type of MU with munch ?W0 _ _ =>
    assert (KtO : forall Ad kk, al_t L + 80 <= Ad -> Ad + kk <= al_t L + 2800 -> 0 <= kk -> disjoint_from W0 Ad kk);
    [ intros Ad kk Y1 Y2 Y3; pose proof DL7 as X7; unbox X7; pose proof DL8 as X8; unbox X8;
      cbn [disjoint_from]; unfold K_HIGH_MEM in *; clear -Y1 Y2 Y3 TL1 TL2 TBND TIMG LO CEIL X7 X8 SC_t MSB EUB UBS NB RUP SHLO SHHI SHE SHL; repeat (split; [lia|]); exact I |];   (* [comment removed for export] *)
    assert (KgO : forall Ad kk, 0x9daf0 <= Ad -> Ad + kk <= 0x9dbb0 -> 0 <= kk -> disjoint_from W0 Ad kk);
    [ intros Ad kk Y1 Y2 Y3; cbn [disjoint_from]; unfold K_HIGH_MEM in *; clear -Y1 Y2 Y3 TL1 TBND TIMG LO CEIL MLO ML1 ML3 KAM KBM KEM KCM KDM EUB DL1 DL4 Ni Si NBND SBND SHLO SHE; repeat (split; [lia|]); exact I |]   (* [comment removed for export] *)
  end.
  (* [comment removed for export] *)
  assert (ELIVE : a_live st1 = delete p (a_live st)) by reflexivity.
  assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
  assert (WF' : awf L st1 X) by (apply (awf_delete_sec L st X p mb ms n st1 WF LIVE); reflexivity).
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st1 m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st1 X m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
      unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply KtO; clear -Hc'; lia.
    - eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply KtO; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
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
        * rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
          rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
    - (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        split; [reflexivity|].
        pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * apply shlen_nonneg. clear -T16; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia] | clear; lia].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * clear -POS''; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
  }
  (* [comment removed for export] *)
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
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
  (* [comment removed for export] *)
  assert (NOTL : ~ sec_live st1 ch) by (apply (sec_not_live_after L st _ p mb ms n st1 WFS (Permutation_refl _) LIVE ELIVE)).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st1 c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st1 c LIVE ELIVE).
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. pose proof (aobj_int _ _ OP ltac:(clear; lia)) as (OPi & OPa & [kP OPs]). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASECc (sec_chunks_of st) L st1 X m').
  { unfold ASECc.
    pose proof HS as HS1. destruct HS1 as (_ & _ & _ & _ & SHZ0).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) exact WFS.
    - (* [comment removed for export] *) exists order. change (a_nres st1) with (a_nres st). change (a_nsec st1) with (a_nsec st).
      split; [exact PO|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
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
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          replace (mb + 6128 + 16) with UB in S3 by (rewrite EUB; clear; lia).
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
        * (* [comment removed for export] *)
          destruct (PER j c Hj) as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          destruct (sec_wf1_facts' L mb' ms' n' Wc) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & (JC_t & _ & JC_r & _ & JC_n & JC_st & _) & _).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ]. assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
          destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
          all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
          all: unfold K_HIGH_MEM in JLO, JCE.
          all: pose proof (ablk_lin _ _ JLO) as (JL1 & JL2 & JL3 & JL4); unfold AIMG_HI in JL1; pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).   (* [comment removed for export] *)
          all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
          all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
          all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
                    eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| clear -Z2; lia|].
             left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| clear -Z2; lia|].
             right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
    - (* [comment removed for export] *) destruct SINST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
      split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
    - (* [comment removed for export] *) unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + clear -POS; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia] | clear; lia].
    - (* [comment removed for export] *) intros x Hx HFh HC.
      pose proof HC as HC0.
      assert (INst : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; clear -Hx; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| clear; lia|].
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (BL' : ablocks L st1 X (lb_remove p LB)).
  { eapply (ablocks_free_sec L st X LB p mb ms n st1 X LIVE WF ELIVE); [| exact BL]. intros y Hy. exact Hy. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & FKa & [kF FBND]). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148232192 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. pose proof (aobj4_int _ DTO) as (_ & _ & [kD DBND] & [jD DIMG]). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148232192 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
        rewrite SHE. destruct SC_f as [D|D].
        - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
        - left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia] | clear; lia]. }
      destruct SHF as (SHF1 & SHF2 & SHF3).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      do 16 (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [lia|]); lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [rewrite ?qsz_0; clear -FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]   (* [comment removed for export] *)
              | match goal with |- ?G => idtac "FAKELEFT" G end ] |]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  (* [comment removed for export] *)
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
    - split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - exact CP.
    - exact NUM. }
  (* [comment removed for export] *)
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
      + (* [comment removed for export] *)
        assert (NEq : q <> p) by (intros ->; apply NEp; reflexivity).
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite ELIVE, lookup_delete_ne by (intros E'; exact (NEq (eq_sym E'))). rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') (sec_chunks_of st)) by (eapply live_sec_in; exact Lp).
        assert (INs : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - destruct (FKD cls A' n' Hin) as (K1 & K2 & K3). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) 0 0 0) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). unfold K_HIGH_MEM in *.
    assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | clear; lia |].
    rewrite SHE. destruct SC_f as [D|D].
    - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
      pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
    - left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
      clear -HH Ha' K3 FAL8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  split; [| split; [exact BL'| split; [exact HFK'|]]].
  - split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
  - eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
