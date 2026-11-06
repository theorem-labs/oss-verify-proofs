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
     AKit AKit2 AModelFacts ASecFacts ASec ASecFrame AFreeModel AFreeRep AFreeGeo AFreeRead F_afree_tail F_afree_icpt F_afree_arep F_afree_arepR AFreeStoreK AFreeStore AFreeStoreR
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

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & LJ & L0 & L1 & DTL & DHL & CR' & STS' & RL). exact L0.
  - destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & BJ & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB). exact B0.
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0x9daf0 \/ 0x9dbb0 <= fst iv)
                                  /\ (snd iv <= 0xa2080 \/ 0x1230b0 <= fst iv)
                                  /\ (snd iv <= 0x130908 \/ 0x13090c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

#[using="HL CI_OK"] Theorem store_freeRS : store_freeRS_stmt DI AFK CI.
Proof.
  unfold store_freeRS_stmt. intros L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q cs mb ms n b1 ctx lo k24 stj chunks.
  cbv zeta. intros ALO ARNG AR BL HFK PCS RSCS NOTL NQM B1 B13 CTX EAF NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0 NOREC EK DK CEIL LO ms' PM. unfold AFREE_STACK in LO.
  assert (NEWF : enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; repeat (split; [assumption|]); exact POS0).
  clear NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0.
  set (ch := CSec mb ms n) in *.
  set (st2 := st_enq st ch) in *.
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHSm] in HQ, HS, HD. rename HQ into AQ.
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
  pose proof HS as HS0. destruct HS0 as (WFS & ARR0 & SINST & PZ & SHZ).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  assert (INcs : In ch cs) by (eapply Permutation_in; [apply Permutation_sym; exact PCS| left; reflexivity]).
  pose proof (proj1 (Forall_forall _ _) WF1 ch INcs) as WFch.
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).   (* [comment removed for export] *)
  pose proof SCL as (SC_t & SC_c & SC_r & SC_p & SC_n & SC_st & SC_f & SC_d).
  (* [comment removed for export] *)
  destruct ARR0 as (order & PO & U64 & JK & PER).
  assert (INo : In ch order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INcs]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  assert (LENO : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  destruct (PER i _ NTH) as (lv0 & LV0 & CH).
  assert (Elv : lv0 = false) by (destruct lv0; [exfalso; apply NOTL; apply (proj1 LV0); reflexivity| reflexivity]). subst lv0.
  pose proof CH as CH0. unfold ch in CH0. cbn [asec_chunk] in CH0.
  destruct CH0 as (H1 & _ & _ & _ & _ & H6 & S1 & _ & S3). unfold SEC_UOFF in H6, S3.
  Local Ltac2 Set LiaHints.tbl := fun () => "0;k0?10129480930.14610196145140.4  10313546700.2  10317707088.1  10570200823.2  10645443711.20 10645443711.22 10645443711.26 10645443711.27 10645443711.35 10707908469.0  10780660995.11 10788002338.3  10924510459.20 10998108614.21 11097776055.20 1111870547.5   11190051350.21 11202920.2     11624421952.5  11773154516.25 11888782229.1  11892977425.4  11909393000.6  1196071673.26  12021105364.25 12028886269.4  12038807697.4  12043002901.1  12257431285.0  12417695618.19 12612293892.83 12612294022.89 12612294026.86 12861923704.13 12866091207.8  12877090629.1  12877527575.11 12920915338.52 12920915338.7  12971281919.20 13097809467.1  13296790518.19 13296790518.24 13296790518.28 13296790518.29 13341084364.0  13432448837.8  13544598300.2  13563704212.25 13795940257.11 13849226562.19 14003737881.3  14043501308.5  14128416780.2  14248615048.10 14248862995.10 14248862995.9  14250793113.6  14281919934.2  14297405530.8  14299800674.2  14551660263.2  14639337364.25 14860407635.1  15061026666.5  15132320885.0  15259511169.1  15439077749.0  15453126219.1  15503147087.5  15515497321.5  15518689194.21 15518689194.25 15628063534.6  15630524557.5  15632654259.14615637857749.1  15653624221.5  15714467111.13 15754900564.25 15769036414.10 15913113386.2  15985097707.20 16020704486.21 16056761287.33916114808228.1  16119001376.4  1634525507.7   16368862892.33916432229618.6  16534157257.1  16641052917.0  16644899888.3  16656649474.4  16779702664.14 16801639638.21 1685717371.0   16884868271.2  17026234542.8  17114851612.2  1719372884.25  17240050198.21 17330577750.21 17374471804.11 17520992186.2  17617125066.34217734834689.3  18101162640.2  18113523605.7  181632187.25   18326180244.25 1840862455.2   18583273217.4  18587466629.1  18587749582.3  1861022073.26  18680697845.0  18703868551.34318777878251.4  18930958230.14 18930958230.24818930958230.33818930958230.34219074402919.1  19103934226.7  19190814485.1  19231870649.26 19506922580.25 19553720766.0  19710847493.1  19759569631.2  1990627212.25  2009547599.5   20096121660.15 20162786534.21 20228488911.2  20344620357.1  20415666024.14 20517235800.11 205688706.19   20905091944.2  20907259734.4  21048865186.9  21127161141.0  21201691374.9  21549609119.2  21553614380.1  21603401536.34 21742752948.2  21842373400.5  21862344309.0  21886510158.9  21888851405.9  21896799131.1  21927396353.2  21962168434.3  22014172427.5  22078411937.22 22171511443.8  22208142071.7  22483864548.25 22660696137.4  22809127129.6  22812861017.83 22812861143.86 22812861147.89 22941351991.2  22947759178.7  23023850886.4  2356004018.1   23574709585.22 23860662149.4  23873330652.3  24101828570.7  2424857170.2   24386447584.11 24496633676.0  2460702823.2   24721163744.20 24721163744.22 2484947455.7   2486760693.7   2487091158.5   24960430335.1  25105977745.22 25151768127.20 25161805127.89 25161805131.86 25161805253.83 25232370983.2  25440935497.5  25502561157.11 25504546824.4  25745894988.0  26003370052.7  26017132307.10 2611727477.0   26134337999.20 26152634640.2  26225946432.34 26238245128.0  26306678284.4  26307031873.3  26492213457.4  26496408661.1  26537571606.7  26554307614.6  26717002278.5  2672118728.3   26808141859.5  26810173397.5  26826558778.5  26831418963.5  26960244085.0  27032899823.3  2735119093.0   27594215439.5  27594218767.5  27594218895.5  27594219277.5  27895037940.2  27945449407.2  27948118412.25 28233644939.3  2833535172.8   28453283427.5  28478945574.11 28865040722.6  29038208332.4  29168411648.34 29279152639.4  29293492283.5  29323123732.13 29451311717.7  29528376821.0  29717986733.20 29717986733.21 29717986733.22 29717986733.26 29717986733.27 29717986733.35 29742208628.2  30289609511.1  30370828283.25 30465278057.0  3065012820.4   30805913020.4  30873323561.0  30908703488.3  31012612437.0  31191852883.1  31228234864.34 31292898136.3  31404605725.8  3150388519.2   31529209730.1  31607341260.25 31760437524.25 31809637600.2  31812090093.2  31824659409.6  31854741868.34 31899909673.5  3212155662.0   32351896522.12 32395334108.6  3256203307.2   32567013239.2  32648327477.0  32650118316.1  32776955779.4  32831692725.0  32837901993.26 32840080802.2  3286806506.21  3286806506.25  33034530043.20 33214062194.7  33441520534.21 33566802644.4  33664443848.3  33671115282.5  33703808519.3  33802113362.2  33836477841.3  33896070369.2  34129450555.7  34197850293.0  34259051234.2  34372620418.1  34438901183.5  34521219823.7  34566302965.0  34737456555.5  34749668213.0  34811499015.9  34991432652.0  35092724124.2  35093294278.21 35094583552.20 35094583552.22 35150722036.38035157163477.3  35655074153.26 3566823747.8   35694103779.2  35760294982.4  35815230055.2  35878629777.22 3617535950.9   36272315026.2  36386552263.5  36386552283.5  36386552285.5  36388649437.5  36449675461.1  36548533320.3  36586368003.5  36714295519.2  36732773230.1  36877341398.21 36917578143.14 36958550341.1  37023218382.0  37027469036.20 37027469036.22 37090334480.2  37238859556.25 37317800949.0  37384834303.4  37519011252.17 37558919954.2  37582747071.20 37630783035.20 37807923061.0  37991288309.0  38205014962.3  38211521123.1  38436634709.0  38464322519.2  384657662.3    38479020294.21 38529617698.2  38536497531.25 38639113934.3  38692635477.0  38763541244.13 38776846099.20 38776846099.22 38776846099.26 38776846099.27 38776846099.35 38948636245.0  39012636437.0  39076636629.0  39172636981.0  39188636933.0  39220637093.0  39268637205.0  39282819476.25 39332637397.0  39348314248.3  39349763510.21 39396637589.0  39412637669.0  39484780757.0  39491769071.4  39716638549.0  3977885045.0   39802033959.2  39807547359.25 40038943072.11 40082674198.21 40192835119.2  4027300116.25  40313319482.3  40499447413.0  40561793063.9  40569190201.7  40682812661.0  40796883379.11 40847487953.5  40989569525.0  4109668801.5   41107849968.3  41175950771.3  4184269202.2   41891655969.3  419436314.7    419517597.6    42010739649.3  42063720630.5  42080551597.4  4231187719.20  4231187719.22  4233523261.2   42411609006.0  42455853923.1  42469039429.1  42489549249.3  42539092341.0  42556365140.25 42600816231.2  42989238132.2  43059711526.2  43195871047.25 43268453396.4  43332231982.1  43583853560.6  43593744991.2  43669979263.20 43672874517.0  43760733614.1  43899182423.13 4392527934.3   44084246420.25 44180196223.3  44901734804.25 44985545750.5  44985546260.5  44985546388.5  44985547540.5  45031825642.5  45161700303.6  45161700303.7  45164012108.6  4520937093.0   4536697209.26  45492474916.25 45686027211.12 45727962468.25 45738895041.7  4576132444.16  4588927050.2   45966287030.21 45980186556.4  46100613962.3  46178793218.2  46182202218.21 46182202218.25 4650569643.5   46653515486.1  4665792547.7   46780644473.5  46968447212.5  46990720185.2  47007070456.3  47102472806.44747102472806.45147106079221.0  47262857558.86 47262857562.89 47262857688.83 47298079993.9  47397410518.21 47478229362.89 47478229374.86 47478229488.83 47491873821.7  47650515785.0  47657442670.4  47717757129.1  47803412682.3  47824300411.25 47828869500.4  47872845720.3  47906516553.0  47938516713.0  47959972135.2  47995172967.2  48034516937.0  48122452579.4  48162517321.0  48172209967.3  48182876821.1  48324593020.5  48582343014.21 48742894451.13 48778993653.0  48863027762.3  48942484859.25 49047162874.3  49125353229.3  49135537766.8  49145724149.0  49186520393.0  4928185745.22  49314520777.0  49570521545.0  49698521929.0  49785575052.9  49828668885.0  50053598883.1  50203955267.1  50210523465.0  50338523849.0  50410131434.7  50555785828.25 50722525001.0  50830581883.20 50850525385.0  50913014806.13 51161183847.0  51362526921.0  51463334873.6  51607519243.2  51792904453.7  51874528457.0  51939553624.83 51939553750.86 51973644052.25 51974741890.19 5198996308.25  52130529225.0  52158892582.21 52169594139.5  52368717924.25 52386529993.0  52392875668.5  5241886528.34  52555466551.4  52569147371.19 52569147371.21 52569147371.23 52569147371.24 52569147371.25 52569147371.27 52569147371.28 52569147371.29 52770531145.0  52895507081.4  53025787526.21 5303251829.0   53045873664.5  53154532297.0  53238998938.2  53341058949.5  53387318241.10 53410533065.0  53543486193.1  53625821697.22 53666533833.0  53841042975.2  53881886761.5  53922534601.0  54275345606.19 54376399078.21 54424782016.34 54545594495.20 54747134349.5  54765217882.21 54765217882.25 54850238520.13 55078868597.0  55162509369.7  55221209172.4  55330538825.0  55376578060.25 55413433640.3  55458692139.4  55714539977.0  55839719569.2  55857651414.21 55983921528.11 56017846568.2  56023436187.1  56078624876.1  56098541129.0  56137362799.8  56143417687.2  5626182550.21  56350333127.4  56445026165.0  56548018252.1  56552213704.4  56610542665.0  56628391413.0  56701989985.3  56935148277.0  57035045711.2  57306259454.3  57342651816.15 57798265135.5  5782921199.20  5782921199.22  58052068246.21 5836997957.1   58577517210.8  58658548809.0  58742649983.20 58786549193.0  588087689.1    58914549577.0  58966027333.0  59042549961.0  59051497895.2  59060038550.21 59136172532.2  59213864045.4  59314873579.10 59314873579.52 59314873579.8  59321247737.3  59490551305.0  59504205884.4  59554551497.0  59564976821.0  5958468464.14  59618551689.0  59668206885.5  5967452503.13  59793447252.10 59874552457.0  59938552649.0  59993403125.0  60050553081.0  60070176529.20 60070176529.21 60070176529.22 60070176529.26 60070176529.27 60070176529.35 60114553273.0  60194553417.0  6020956344.1   60412371595.6  60514554377.0  60578554569.0  60618587276.14 60649290018.2  60726687833.8  6104698953.8   61097659196.5  61181322092.1  6130166021.1   61346556873.0  61444424438.2  61469804199.2  61497988483.9  61510416471.4  61552696794.8  61602034000.2  61807763572.4  61849682805.0  61986558793.0  62008754397.8  62291000355.1  62305507400.2  62434560137.0  62541394087.2  62626560713.0  62842451974.21 6292008538.4   63179173420.1  63262921558.21 63374621462.14663489174179.1  6364460655.5   63662649864.19 63662649864.23 63662649864.27 63662649864.28 63662649864.34 63991198558.6  63991199562.6  63991200330.6  63991200458.6  64026752006.4  64143574904.3  64190421863.3  64192377451.4  64630052639.2  64763960740.4  64929301227.3  65031329269.0  65194392751.3  65210676195.5  65250602667.3  65253966880.1  65447104936.8  65455420215.3  65840305187.1  65862411281.22 65905589530.9  66048936517.1  66263364923.1  66282876930.19 6628837655.20  6628837655.21  6628837655.22  6628837655.26  6628837655.27  6628837655.35  66459511919.2  6654053634.3   66617857959.2  66714332438.21 66899560164.25 66922131348.25 66967764310.86 66967764314.89 66985451747.8  67065851623.2  67301438931.20 67301438931.21 67301438931.22 67301438931.26 67301438931.27 67301438931.35 67377962076.2  67421407124.25 67678377324.20 67678377324.22 67714728187.20 67719891812.25 67728023110.21 67762809634.1  67838892206.1  678721768.2    67966192501.0  68022559995.4  68089584117.0  6825780775.2   68316589387.25 68595398618.1  68597495712.1  68692784329.1  7159531509.0   7214490407.2   7215606014.6   7242528488.3   7358704019.253 7363940729.26  7497496250.3   7722623749.1   7739443299.8   7807322142.4   7833018869.0   7895480116.4   789940584.3    8038629874.9   8090163211.2   8125337575.1   8196673018.3   8196913479.8   8265560598.21  8278630676.25  8344820050.19  8376585492.25  8590582695.2   8592593028.2   8880602072.13  8914958284.4   8936802302.2   8938650181.21  8938650181.25  8938650181.26  9059237865.0   9161320822.3   9686710118.2   9696982132.52  9933288150.3   00000800?00D00E00F00G00H00I00J00K00L00[00\01201B01b01c01i01j01o02002102602@02G02H02R02W02X02Y02^02k03803E03W03e03f04;04C04K04T04U04d04e04f04g04h05305405505C05H05I05J05K05\05m06>06B06C06M06Q06R06S06T06W06X06Y06Z06[06g07007807907>07I07U07V07[07_07`07g07l08B08H08e08f08k09309P09Q09R09S09X09Y09h09n09o0:00:A0:B0:C0:I0:O0:Y0:_0;=0;>0;?0;@0;K0;L0;M0;R0;S0;W0;^0;_0<<0<=0<>0<N0<i0=D0=E0=O0=P0=W0=X0=Y0=Z0=[0=e0=f0>@0>F0>K0>L0>^0>j0>o0?00?50?E0?F0?Q0?R0?S0?X0?Y0?Z0?[0?h0@80@90@=0@>0@C0@h0A30A@0AF0AP0AS0A^0B20B90B:0BA0BF0BG0Bb0Bf0Bl0C60C:0CF0CG0CH0CP0CX0C\0Ci0D20D30DN0DW0E00EI0Eb0Ec0Ed0F00F80F90FF0FQ0FR0F[0F\0Fa0Fb0Fc0Fd0Fi0Fj0G70G80G;0G<0G=0GE0GJ0GQ0GR0GS0GT0Ga0Gn0H;0HH0HI0HJ0HT0HY0Hl0Hm0I20I:0IC0IH0II0IJ0I`0Im0In0Io0J00JV0JW0JX0JY0JZ0J[0Jf0Jg0Jh0Ji0Jj0K10K20K30K80K=0KE0KF0KG0KQ0KR0KW0K[0K`0L>0L?0L@0LO0LP0LQ0LR0LS0LT0L^0L_0M40M50M=0M>0MT0M`0Mf0Mg0Mh0Mi0Mj0Mk0Ml0Mm0N90N:0N;0N<0NA0NM0NN0NO0NP0N\0N]0N^0Nd0O90ON0Oi0Oo0P60PC0PD0PH0PI0Pd0Q40Q80QC0QN0QY0Qe0Qf0Qg0Qj0Qk0Ql0R20R60R70R80RP0Rb0Rc0Ri0Rj0Rm0S[0S\0Sj0T@0TA0TB0TC0TD0TE0TF0TL0TR0TS0T^0T_0T`0U70UX0UY0UZ0U[0U\0U]0U^0U_0U`0Ua0Ub0Uc0Ud0Ue0Uf0Ul0Um0Un0Uo0V20V30V40V50VM0VY0V_0V`0Va0Vb0Vc0W20W60W70W80W;0W<0WA0WH0WI0WJ0WK0WV0W^0W_0W`0We0Wj0Wo0X30X40X50X60X70X80X90X:0X?0XD0XT0XU0XV0Xc0Xd0Xm0Xn0Xo0YI0YJ0YK0YL0YM0YZ0Yg0Z40ZA0ZD0ZP0ZX0Za0Zb0Zi0Zj0[D0[E0[F0[Y0[Z0[j0[k0[l0[m0\50\60\70\80\>0\?0\@0\A0\B0\h0]`0]a0]l0^90^D0^T0^Z0^a0^n0_50_<0_=0_>0_?0_C0_N0_O0_T0_U0_V0_W0_X0_Y0_Z0_[0_`0_a0_b0_h0`B0`C0`D0`O0`P0`U0`a0`b0`c0a>0a?0a@0aA0aP0aQ0aR0aS0aT0aU0aa0ag0ah0b>0b?0b@0bA0bB0bF0bJ0bR0bS0bW0b[0b\0ba0bb0bc0bi0c10c70c80c90c>0c?0c@0cA0cB0cC0cD0cE0cF0cG0cH0cL0c\0c]0cd0ce0cj0d20d<0d=0dB0d]0d^0d_0d`0da0dg0dm0e20e;0eC0eK0eL0e_0e`0el0em0en0f80f90f:0f;0f<0fB0fR0fS0fT0fU0fV0f^0fb0fh0g10g20g30g80g90g:0g>0g?0g@0gA0g[0g\0gc0gj0h00h10hB0hC0hL0hM0hN0hO0hP0hQ0hR0hX0hY0h_0hl0i50iC0iL0iM0iN0iO0iP0iT0iU0iV0iZ0ib0ic0id0ie0if0ig0ih0ii0ij0ik0il0im0in0io0j80j90j:0jL0jM0j\0ja0jb0jc0jd0je0ji0jj0k50k:0kE0kF0kP0kQ0kR0kn0ko0l00l10l20l30lC0lH0lI0lO0lW0lX0lY0lZ0l[0l\0l]0m;0mF0mQ0m\0mg0ml0mm0mn0mo0n00n10n20n30n40n<0n=0n>0nV0n\0n]0o80oC0oD0oE0oJ0oK0oL0oM0oN0oO0oP0oQ0oR0oS0oY0oZ0o[0ob0oj10710810P10Q10R10S10T10U10V10W10^10e11;11<11B11C11D11E11F11G11H11I11T11X11]11^11_11`11e11f12W12^12_12`12m13213313413513?13C13D13H13V13\13]13b13c13h13l13m14314714814914H14I14P14V14\14]S3ML22ILS2Q52Q6S3RSPSFFFFFFSS2WR2WB3OPi3OPsSS3RES3RHI3FKO3DTO4LSTRS4TBND4SHF24SHF3S3RES3RHI3FKO3DTO4SHF24SHF34LSTRFS4TIMGFS3MSBSSS3LCHS3JCE4JMSBS2Ni2SiSS3RSP4Hc''S3LCHSSS3SHBS3SHE3SHL3EGQS3SHE3SHL3EGQS3SHE3SHL3EGQS4JMSB3JL13KEJ3KCJS3RHI3RSP4Hc''SS3RES3RHI3RSP2P54DW13S3RHI2FFS3RHI2F3S3RHI3EBRFS4FBND3SHB4DBNDFFFSS3SHL2HH2MMFSS3SHE3SHP4SHLOS3SHBSFFS3RES3RI23RI33U0'S3RES3RI23RI33FA2S3RES3RI23RI33FA2S2P8SS3RES2F41HS2Z0FSSS1ESSSSS2Q44RM''2Q7S4RM''2AMS3DTF2D1FS3MSBS2NB3NMS2N6S3MSB3ML22ILSS3MSBS2F3SS2WR2OPS3MALS3RES3RHI3FKO3DTO4LSTRS4TIMGS4LSJ'3ML22IL3LN13LN25ENEXT1HSS3LCHS3RHI2F3S4LSJ'3ML22IL3LN13LN25ENEXT1HSSSS3LCHFS3RES3RHI2F32DLS4TIMGSFS2Q12Q22Q52Q63RSPFSS4TIMGS4TIMGS3SHE4SHHIS4Hc''S4LSJ'3ML22IL3LN13LN25ENEXT2KKFFSS4CEIL2LO1HSFS3LCHSS2HxS2Ni2SiSS4LSJ'3ML22IL3LN13LN25ENEXT1HFSS3ML22IL3LN13LN2S4LSJ'3ML22IL3LN13LN25ENEXTS4LSJ'3ML22IL3LN13LN25ENEXTFS1D3RI32P6SS2Ni2SiSSFFS3FKi4DIMGFS3RES3RHI3RSP3FIT2P52DL2DGS4TIMGS3MALFS3RES3RHI2F32DL2DGS3FKi3Ha'2K1S3SHBFS3Hc'S4MAL83SHL2NX2GESS1D3RI23RI3FFS3KBMFSSS3RHI3RI13FA1S3RHI3RI42U03RI1SS2HjFS3MSBS3RES3RHI3FKO3DTO4SHF24SHF34LSTR4GLRRS3SHL2Z12HHS3FKO3FKi3AR8S4SHF2S3RSP4Hc''S1DS3RHI2Z02Z2S2H12H23RHI2H52H62Z2S2H12H2FS1D3RSPS3Hc'SS3RES3RHI3FKO3DTO4LSTR4GLRRS2HpS4CNT'S3MSB4SHHIS2NBS3RHI2Q13RI4SFS3GLS2HAS3GLS2HAS2P7S3RHI3RI13FA1S3RHI3RSPSS3RES3RHI3FKO3DTO4LSTR4GLRRS3RHI3EBRS3H363H303H343H243H283H40S3H323H263H303H203H243H36S3H283H223H263H163H203H32FFS3FKO3Ha'2K3S2Hx3AR8SS3A242F24Hc''S3SHL2HH2MMSS3RHI3EBRFS3KBMSFFS3LCHSS3A242F24Hc''SS1EFFS3A242F2S3LN2S2Q52Q6SSSS2WR2WB5D_n_pS2WR2WB5D_t_pS2WR2WB5D_s_pS2WR2WB5D_p_rFSS3FKi4DIMGS3POSS3SHE3SHL4SHLO4SHHISS3SHLS3Ha'2K1S4MAL82LTS3KBMFSS3RES3RHI2F33GNZ2DL2DES3A244Hc''2F2SFFS3RES3RHI3FKO3FKi3DTO3DFR4LSTR4GLRR2D2FFFFFS4CEIL2LO1HSFFSS5POS''SSS3KBMS3LCHS3JCE2Z3FSS3FKi4DIMGSS3SP3S2F8S3FKOS2NB3KEM3KCM3RUP3UBS4SHF24SHF3SSS2WR2WB3OPi3OPsSFFSFS3RSP4Hc''SS4NBND4SHF24SHF34SBNDFS3DTF2D1FS3RES3RHI3FKO3DTO4LSTRS2WR2WB4SC_pS4TIMGFFSFFSFS2WR2WB4SC_pSFSS3MSBS2Q23RI23RI3SSSS3Gs33Gs42SFSFS4TIMGS3RES3RHI2F32DL2HA2HKS3RES3RHI2F32DL2HA2HKS4LSJ'3ML22IL3LN13LN25ENEXTS4CNT'S2Ni2SiS3JCE4JAL82Z3FS2NEFS3RES3RHI3FKO3DTO4LSTR4GLRRS3Gs23Gs43Gs52SFS2NBS4JMSB4JC_nS4JMSB4JC_rS4JMSB4JC_tS4JMSB5JC_stSFS1DFSS4TIMGS2F4SSS3RES3RHI2F32DL2DE2HA2HKS3RES3EEB2DE2HA2HKFS4SHF2SS1ES3MAL2NB4MSAL3NMS3ML13ML33RUP4RUP83RS13NSE3AR8FS3RHI4SHF33EBRS3RES3RHI3FKO3DTO4LSTRSSFSSSS4CNT'S4TIMGFS4CEIL2LO1HSSS3RES3RHI3RSP3FIT2P52DLS3RES3RHI3FKO3FKi3DTO3DFR4LSTR2D2FFFFSSSSSSSSSFS4TIMGSSSS1ESSFS4CEIL2LO3RES2OT3FKO3DTOS3RHI2Q13RI4S4TIMGFSFSS1D3RI23RI33FA2S2Y6SSS1ESS3LN1S5POS''FFFS3SHL2HH2MMS3SHL2HHFSS3Hc'S3KK0S3KK0S2Z2SSSFSSFS3Gs5S3JALS4CEIL2LO4SHF31HFSS3RI23RI33FA2FS3RHI3EBRSSS3RES3RHI3RSP2P54DW134DW15SSFSS2WR2WB5D_p_rS2WR2WB5D_t_pS2WR2WB5D_s_pS2WR2WB5D_n_pS1ES3RI42U03RI1S2Q13RI4S3RI13FA1SS2Ni2SiSS3MSB4SC_r3RSP2Q12Q22P52P4SSS3KBJ3KEJ3KCJ2Z12Z3SS4TBND4SHF24SHF3FFFS3DTF2D1FSSS4SHLOFFFFS4LSJ'3ML22IL2Y53LN13LN25ENEXT3LQg3LNgS3EAF3LEN4LSJ'3ML22IL2Z52Y53LN13LN25ENEXT2LQ3LNl3LQg3LNgSS3UBS2H92H7S3UBS3H133H11S3UBS2H52H3S3Ha'2K34FAL82HHS4TIMGS2H52H6S2H52H62H12H2S2H12H2S2Z32HHSFSS2HxS4CEIL2LO1HFS3FITSSFFSSSS3LCHSFS4TIMGS3RES3RHI3RSP2P54DW134DW14SFS4CEIL2LO1HFS3SP2S4SC_f2K12K3SSS3RES3RHI3FKO3DTO4LSTR4GLRRSSSS1D3RI23RI33U0'SSSSSS3RSP3FIT2P5S4SHF2SS3RES3RHI3FKO3DTO4LSTRSSSSS2Y6S2NBS3JL12Z1SS2Z0S2Z0SS3SHBSSS4TIMGS3RSP2P5S4SHF2SSS3KBMSFFFFFFFFSS2Q6S4TBND4SHF24SHF3SS2Q12Q2SS3Gs5S3RSP2P6S2WR2WB2OPSS3POSS3RES3RHI3FKO3DTO4LSTR4GLRRSFSSS4SHF1S4TIMGS3KBMS3RHI3EBRS3A242F2S3DTF2D1FS3RES3RHI2F33GNZ2DLSS3RSP3FIT2P6FSS3FKi4DIMGFFSFS4TIMGS3FKi4FBND2K12K3FSSSS3RHI2F3S2Z0S4TIMGS3RI13FA1SSS3LCHSSS2Q6SSSS3RES3RHI3RSP3FIT2P52DL2DEFS2F42HKS2F42HKS4TIMGFS2Q12Q22Q52Q63RSPSS3RHI3EBRSSSSSFS4TIMGFS4CNT'S3RHI2Z01E2F3S2Z14EBNZS3RHI2Z02B32NES2Z04EBNZSFSSS2F3SSS2F4S3FKO2K3SSSSFFFFFFSSFS4JMSB2DcSSS3RES3RHI2F32DL2DEFS1D3RI23RI33FA2S3SHEFFFSS2NBFS3Gs42Dc2SFS3EQAS3SHL2HH2MMFS3RSP4Hc''SSS4JC_t2Z12Z34JC_r4JC_n5JC_stSSSFSS4TBND4SHF24SHF3S3Hc'SS4TIMGS3ML22ILSFFFFFS2NB4SC_f3RUP3UBS3FKO3DTO4SC_dS2K12K33DFRS2K12K33DNFS2K12K33DTFS2K12K33DSFS3Hc'FFFFFFSFS3A242F2SSS3Gs43Gs52Ct2SF2Cr2Cn2CsS4RM''SS3RES3RHI3FKO3DTO4LSTR4GLRRS3SHL2HH2MMSFS3SHBFFFFFFFFFS4TIMGSSS2H52H6S2H93H10S3RHI3RI43FA1FS3RES3FKO3DTO3DFR3EBR2D2FFFFFFSS2F32HAS2F32HAS3RES3RHI3FKO3DTO4LSTRSS4TIMGSSFSFSFS4CEIL2LO1HS2LQS3LQgSSFS3EUBFS2WR2NB3MSB3ML23KBM2IL3SP14TIMG3RUP3LN13LN22Q12Q2S2Ni2SiFSS3RHI3RI43FA1S3SHPSFFS2Dc2Z32Z1S2WBFS2Y6S3RHI3RSP4Hc''S4TIMGSS3SHBSS3T16S2QSSS4AL''S2X1FFS3DNF2D33DSF2D4SS5POS''S4EBNZS4EBNZS".
destruct (junk_split m _ 8 (ms - 6144 - 8) ltac:(replace (8 + (ms - 6144 - 8)) with (ms - 6144) by lia; exact H6) ltac:(lia) ltac:(lia)) as [_ UJ].
  rewrite (granules_rup n) in S3 by (clear -NB; lia).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (aobj4_int _ OT) as (_ & _ & [kT TBND] & [jT TIMG]).   (* [comment removed for export] *)
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
  rewrite EHM in PM, EK, DK.
  replace (mb + 6144) with UB in UJ, S3 by reflexivity.
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
  assert (CNT : enq_app st ch = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF EAF))))))))).
  assert (EAPP0 : enq_app st ch = None).
  { destruct (enq_app st ch) as [sx|] eqn:EAPP; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st ch)); eexists; exact EAPP). congruence. }
  assert (SB : a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st).
  { subst st2 ek. unfold st_enq, ek_of. rewrite EAPP0, EAF. cbn [ek_delta]. pose proof (enq_new_core ch st) as (_ & G1' & G2' & _ & _ & L2' & _).
    rewrite G1', G2', L2'. unfold ch. cbn [chunk_size]. unfold Q_BATCH_BYTES. repeat split; try reflexivity. clear; lia. }
  destruct SB as (SB1 & SB2 & SB3).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; clear -NB; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EAx; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EAx E]]; [left; exact E| right; exists k24]. destruct (NEWF EAx) as (NK & NBk & KK & NIB & _). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> UB - 16 + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= UB - 16).
  { intros kk KK. pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _).
    destruct (PERC K_BATCH_CLASS (K24)) as (Q1 & Q2 & _).
    pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as (P5 & P4 & _).
    rewrite size_of_class_24 in P4. subst UB. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_r MSB. lia. }
  destruct (read_dkS (AHSm DI AFK cs Q) L st X Q m RNG (UB - 16) ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek
              (proj1 ED0) EBB ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) as (_ & _ & GL & GLST).
  fold g in GL, GLST.
  set (lst := qlast L (q_loc Q)) in *. set (eb := ek_b ek lst) in *. set (gl := dk_glst g lst) in *. set (gq := shlen (rup n 8)) in *.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as (_ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (Q1 & Q2 & _). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EAx E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. destruct (NEWF EAx) as (_ & _ & KK & _). pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as (_ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  destruct PM as (id & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj'
                  & -> & MU & WM & MI' & ST' & IDR & HDR' & FC' & SH' & QC' & EKP & DKP & STATS' & LSJ' & UW' & FL' & IAS' & IAM' & DEP').
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  replace (eb + 8192) with (eb + qsz eb) in MU by (rewrite (qsz_pos eb) by (clear -EBNZ; lia); reflexivity).   (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo lst eb gl).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ LSTF EBF GLF EBNZ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); rewrite (qsz_pos eb) by (atop_facts; lia); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
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
  assert (SC : same_core st (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = a_live st /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. destruct (enq_app st ch) as [sx|] eqn:EAPP.
      - destruct (enq_app_Some st _ sx EAPP) as (l & bl & QL & NFz & ->). split; [repeat split; intros; reflexivity|].
        split; [intros _; reflexivity|]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st ch)); eexists; exact EAPP).
        congruence.
      - pose proof (enq_new_core ch st) as (C1 & _ & _ & _ & _ & _ & C7). split; [exact C1|].
        split; [| intros _; exact C7]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st = true) by exact EAx. destruct (proj1 (enq_is_app_spec st ch) EA1) as [s Hs]. congruence. }
    destruct SC1 as (SC1 & CLa & CLb). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. destruct SC0 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EAx; rewrite CL2'; exact (CLa EAx)| intros EAx; rewrite CL2'; exact (CLb EAx)]. }
  destruct SC as (SC & ECIN & ELIVE & ENEXT & ESB & EPA & CLa & CLb).
  pose proof SC as SC0. destruct SC0 as (_ & _ & _ & _ & _ & ENRES & ENSEC & GCo & M24a & M24b & M24c & M24d).
  set (st' := st_after st2) in *.
  set (X' := xfreeS X (enq_is_app st) k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. destruct (enq_is_app st) eqn:EAx; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF' : awf L st' X').
  { subst X'. unfold xfreeS. destruct (enq_is_app st) eqn:EAx.
    - exfalso. clear -EAF EAx. congruence.
    - destruct (NEWF eq_refl) as (NK & NBk & KK & NIB & JKb & FSH & CIN & POS).
      apply (awf_xbatch L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK).
      + exact ESB. + exact EPA. + exact ECIN. + exact ELIVE. + exact ENEXT.
      + intros c' NE. rewrite (GCo' c' NE). reflexivity.
      + rewrite GC24. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CHc & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN. subst X'. rewrite xfreeS_cache, Z.eqb_refl, andb_true_r.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CHc |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EAx; cbn [ek_post negb] in EKP |- *.
        * destruct EKP as (_ & _ & _ & CR' & _). exists tail. split; [exact CR'|]. split; [| exact LCH].
          eapply u32arr_frame; [exact CHc | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
        * destruct EKP as (CR' & _). destruct (NEWF eq_refl) as (NK & NBk & KK & NIB & JKb & FSH & CIN & POS).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CHc. cbn [map] in CHc. rewrite <- app_assoc in CHc. cbn [app] in CHc. exact CHc.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xfreeS_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
            - destruct EKP as (_ & _ & _ & _ & STS'). exists stj. exact STS'.
            - destruct EKP as (_ & STS' & _). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 Hq1 Hq2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 Hq1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 Hq2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EAx. destruct (NEWF EAx) as (NK & NBk & KK & NIB & _).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. destruct (CLS c'' Hc'') as (REG & FARR & SLOTS & SHADOW).
    pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3 & RI4).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xfreeS_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
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
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
          by (destruct (enq_is_app st); clear; lia).
        destruct D2 as [(EAx & E24 & EK24)|NE2].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 K_BATCH_CLASS k24), EAx. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
          subst ek. unfold ek_of in EKP. rewrite EAx in EKP. cbn [ek_post] in EKP. destruct EKP as (_ & _ & BC & BA & [bsb BJ] & _).
          fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
          replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
          apply junk_merge; [| | clear; lia| cbn; clear; lia].
          -- pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
          -- apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
             cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
        * assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
          { destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
            destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
            destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
          assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
          { subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k''), T1. reflexivity. }
          (* [comment removed for export] *)
          assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
              exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                         /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
          { intros q Hq -> EQA. destruct (bslot_busy L st X Q CP q Hq) as (yq & Hyq & Syq & Cyq & Kyq).
            assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
            exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
            split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
            destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
            unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
          assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
          destruct D3 as [(E24 & LNZ & EL)|NE3].
          -- (* [comment removed for export] *)
             right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
             destruct (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) as (yq & BY & Syq & Cyq & Kyq & JQ & EKQ).
             rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
             assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
             subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EAx; cbn [ek_post ek_pre] in EKP, EK.
             ** destruct EKP as (LB' & LA' & [bs LJ'] & _). destruct EK as (_ & _ & CNT' & _ & _ & _ & _ & LEN & _).
                rewrite ELST in LB', LA', LJ' |- *.
                set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
                replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
                  by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
                apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
                +++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
                +++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
                    rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
             ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                destruct EKP as (_ & _ & _ & _ & _ & [LB' LA']). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                rewrite ELST in LB', LA' |- *.
                replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                  by (rewrite LEN0; clear; lia).
                apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
          -- assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                        \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
             destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
             ** (* [comment removed for export] *)
                right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                destruct (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) as (yq & BY & Syq & Cyq & Kyq & JQ & EKQ).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                assert (GNE : a_qglob st <> []) by (intros QG0; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                unfold dk_post in DKP. rewrite GD in DKP. destruct DKP as (_ & _ & GLN).
                assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                rewrite GF, GL, <- GQL in GLN.
                replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                    eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                    assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                      destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                      exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                    assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EAx). }
                    apply Kres; clear -F3 F4 RES RHI GNZ DL DE; lia.
             ** (* [comment removed for export] *)
                left. split; [exact BX|]. split.
                +++ assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                        aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                    { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                    (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                 intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                      destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                      rewrite Eql in Z0. destruct (BGEO ql ltac:(apply in_or_app; left; exact Hql)) as (_ & _ & B3 & _). clear -Z0 B3 RES RHI. lia. }
                    assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. destruct (NEWF EAx) as (_ & _ & KK & _).
                      pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                    ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EAx in NE; discriminate| left; exact NE| right; exact NE])) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                    { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                      rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                      destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                      - exfalso. rewrite Eq in NE. destruct (BGEO q ltac:(apply in_or_app; right; exact Hq)) as (_ & _ & B3 & _). clear -NE B3 RES RHI. lia.
                      - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                        rewrite Eq in Z0. destruct (BGEO q ltac:(apply in_or_app; right; exact Hq)) as (_ & _ & B3 & _). clear -Z0 B3 RES RHI. lia. }
                    apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia
                                | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                +++ intros b Hb. destruct (busy_of_Some_facts X c'' k'' b Hb) as (IB & CB' & KB'). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        split.
        -- subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k'').
           destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
           destruct (enq_is_app st) eqn:EAx; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
           destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
           destruct (NEWF eq_refl) as (_ & NBk & _). rewrite NBk. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
           reflexivity.
        -- pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
           apply Kshad.
           ++ rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
           ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
           ++ apply shlen_nonneg. clear -T16; lia.
           ++ rewrite SHE. destruct SC_r as [D|D].
              ** right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
                 pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
              ** left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia] | clear; lia].
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
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
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
  assert (PD : Permutation (sec_chunks_of st') cs).
  { eapply Permutation_trans; [| apply Permutation_sym; exact PCS]. apply (sec_chunks_of_quar_sec st st' mb ms n ELIVE). exact (st_after_enq_qfilt_sec st ch eq_refl). }
  assert (NOTL' : ~ sec_live st' ch) by (unfold sec_live; rewrite ELIVE; exact NOTL).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)) by (intros; unfold sec_live; rewrite ELIVE; reflexivity).
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. pose proof (aobj_int _ _ OP ltac:(clear; lia)) as (OPi & OPa & [kP OPs]). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { unfold ASEC_of, ASECc.
    pose proof HS as HS1. destruct HS1 as (_ & _ & _ & _ & SHZ0).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) unfold asec_wf. rewrite EPA, WP, ENRES, ENSEC.
      split; [exact ALO|]. split; [reflexivity|]. split; [exact WR|]. split; [rewrite (Permutation_length PD); exact WL|]. split; [exact WB|].
      split; [rewrite Forall_forall in WF1 |- *; intros c Hc; apply WF1; eapply Permutation_in; [exact PD| exact Hc]|].
      eapply sec_disjoint_perm; [apply Permutation_sym; exact PD| exact WD].
    - (* [comment removed for export] *) exists order. rewrite ?ENRES, ?ENSEC.
      split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
          rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL' Hl)]|].
          unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
          pose proof CH as CH1. unfold ch in CH1. cbn [asec_chunk] in CH1. destruct CH1 as (G1 & G2 & G3 & G4 & _). unfold SEC_UOFF in G1, G2, G3, G4 |- *. rewrite <- ?EUB in *.
          replace (UB - 16 + 16) with UB in FC' by (clear; lia).
          split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
          split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
                   - pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
                   - eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
                     exact UJ. }
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
        * (* [comment removed for export] *)
          destruct (PER j c Hj) as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          destruct (sec_wf1_facts' L mb' ms' n' Wc) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & (JC_t & _ & JC_r & _ & JC_n & JC_st & _) & _).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ].
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
      assert (HC0 : Forall (fun c => ~ (sec_mb c <= x < sec_mb c + sec_ms c)) cs).
      { rewrite Forall_forall in HC |- *. intros c Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PD| exact Hin]. }
      pose proof INcs as INst.
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; clear -Hx; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| clear; lia|].
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (BL' : ablocks L st' X' LB).
  { eapply ablocks_mono; [exact BL| intros y q Hy _; subst X'; apply In_xfreeS; exact Hy| intros q mb' ms' n' Hl; rewrite ELIVE; exact Hl]. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & FKa & [kF FBND]). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148232192 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L LB m').
  { eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |].
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
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104 /\ qsz eb = 8192) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; [assumption| split; [assumption| apply qsz_pos; clear -EBNZ; lia]]]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      do 16 (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [lia|]); lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR; repeat (split; [lia|]); lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR; repeat (split; [lia|]); lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR; repeat (split; [lia|]); lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] |]).
      apply Forall_nil. }
  assert (QH : qhdr L ch 0 = UB - 16) by (unfold ch; cbn [qhdr]; unfold PG; rewrite RZ, EUB; clear; lia).
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  destruct DKP as [MX' DKP'].
  pose proof (qnum_freeR st ch NUM ltac:(unfold ch; cbn [chunk_size]; clear -NB; lia) NOREC) as (NUM' & NB2a & NB2b & NB2c & NF2).
  fold st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QK' : aquar_glob_const m').
  { split; [| exact MX']. eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. destruct (BGEO q Hq) as (_ & _ & F3 & F4). pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI DL DE DG; lia. }
  assert (HQ' : AQUAR L st' X' m').
  { subst ek. unfold ek_of in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      destruct EKP as (LB' & LA' & [bs LJ'] & _). destruct EK as (_ & _ & CNT' & _ & _ & _ & _ & LEN & _).
      (* [comment removed for export] *)
      pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
      assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
      destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
      set (l := rev rl) in *. set (bl := blr) in *.
      assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
      assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
      set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
      assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
      assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
      assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
      set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)) in *.
      set (qz' := mkQB (qb_slot qz) (0 :: qb_ks qz)) in *.
      assert (EAPP : enq_app st ch = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st + n) st)).
      { unfold enq_app. rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
        subst bl'. reflexivity. }
      assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. cbn. repeat split; reflexivity. }
      destruct Q2 as (QL2 & QB2 & QG2 & QGB2).
      (* [comment removed for export] *)
      unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
      cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
      assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
      { cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
        intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
        assert (NEq : abatch_addr L (qb_slot q) <> lst).
        { rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
          apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
          unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
        apply BFR; [exact INq | exact NEq |].
        destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; destruct (BGEO q INq) as (_ & _ & F3 & _); clear -F3 RES RHI; lia|].
        rewrite Eqg. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl). apply in_split in Hqg. destruct Hqg as (gs1 & gs2 & EQg).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
        pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
        unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      assert (ABz' : abatch_cells L m' bl' qz' 0).
      { unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite QH.
        split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
        exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
      assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
      { apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
      { subst X'. unfold xfreeS. apply (qcoupled_app_sec L st X Q mb ms n CP st2 l bl ql qz true 0 QL QQ QL2 QG2). }
      subst qz'.
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        destruct (DRN DR) as (QL3 & QB3 & QG3 & QGB3).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
             replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
             assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                       rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
                       apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                       pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                       unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
                       { rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                         pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
                       destruct (BGEO qgz INgz) as (_ & _ & F3 & F4). pose proof (BLST qgz INgz NGL) as DL.
                       assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
                       { destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST. 
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app, qfirst_reslot, qlast_reslot, <- QQ, <- ELST. cbn [length].
          replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity). exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          assert (NEq : abatch_addr L (qb_slot q) <> lst).
          { rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
            apply (bslots_nodup_split L st X Q CP ql qz gs1 q gs2); [rewrite QQ, EQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
          apply BFR; [exact INq | exact NEq | rewrite EGL; unfold dk_glst; rewrite GD; exact NEq].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'.
    - (* [comment removed for export] *)
      destruct (NEWF eq_refl) as (NK24 & NB24 & KK24 & NIB & JK24 & FK & CIN & POS).
      destruct EKP as (C24' & [stj' SJ'] & NBc & NAc & [bs NJc] & OLDc).
      pose proof EAPP0 as EAPP.
      set (nbt := mkABatch 1 (n + 8192) [ch]) in *.
      set (qn := mkQB k24 [0]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. pose proof (enq_new_core ch st) as (_ & E1 & E2 & _ & E3 & E4 & _).
        rewrite E1, E2, E3, E4. subst nbt. unfold ch. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. fold ch. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      destruct Q2 as (QL2 & QB2 & QG2 & QGB2).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite FSTE in QC'. rewrite FSTE in DKP'.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - destruct (BGEO q INq) as (_ & _ & F3 & _). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg). apply in_split in Hq'. destruct Hq' as (qs1 & qs2 & EQl).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; destruct (BGEO q INq) as (_ & _ & F3 & _); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl). apply in_split in Hqg. destruct Hqg as (gs1 & gs2 & EQg).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite QH.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
      { subst X' qn nbt. rewrite ?EA. unfold xfreeS. cbv iota beta.
        apply (qcoupled_new_sec L st X Q mb ms n WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true 0 eq_refl POS NK24 QL2 QG2). }
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        destruct (DRN DR) as (QL3 & QB3 & QG3 & QGB3).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       destruct (BGEO qgz INgz) as (_ & _ & F3 & F4). pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz eq_refl) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE EEB GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST.
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite QLST'. exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          apply BFR; [exact INq | exact (GNL q Hq) | rewrite EGL; unfold dk_glst; rewrite GD; exact (GNL q Hq)].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'. }
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk LB -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size].
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
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EAx. destruct (NEWF EAx) as (_ & NBk & KK & _).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NBk. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. exact (DK24 EAx). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') cs) by (eapply Permutation_in; [apply Permutation_sym; exact PCS| right; eapply live_sec_in; exact Lp]).
        pose proof INcs as INs.
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - destruct (FKD cls A' n' Hin) as (K1 & K2 & K3). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'.
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
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS]. }
  split; [exact ALO|].
  split. { pose proof ARNG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RCl & RPA & RSC & RPSH).
           unfold arng. repeat (split; [assumption|]). split; [| split; [rewrite ENRES; exact RPA| split; [eapply RSEC_perm; [apply Permutation_sym; exact PD| exact RSCS]| exact RPSH]]].
           intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24a, M24d; exact (RCl K_BATCH_CLASS Hc')| rewrite (GCo' c' NE); exact (RCl c' Hc')]. }
  split; [| exact HFK'].
  exists X'. split; [| exact BL'].
  split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
  split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
