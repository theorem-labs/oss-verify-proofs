(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import ASecFacts BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
AKit AKit2 AModelFacts F_aalloc_s F_aalloc1 F_aunwind F_afree_iseg F_afree_null F_afree_arep.
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
Section CANSEC1. Context {rc : runConstT}.
Definition q_set_ia (Q : qconc) : qconc := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q).
#[using="Type"] Lemma AQUAR_null : forall L st X Q m m' W,
AQUAR_at L st X Q m -> munch W m m' -> wmono bsegs m m' ->
Forall (fun iv => (snd iv <= al_t L + 80 \/ al_t L + 208 <= fst iv)
/\ (snd iv <= AINSTANCE + 728 \/ AINSTANCE + 984 <= fst iv)
/\ (forall b, In b (x_busy X) -> match xb_st b with BLive _ => True | _ =>
snd iv <= xb_alloc L b \/ xb_alloc L b + size_of_class (xb_class b) <= fst iv end)) W ->
aintal true m' ->
AQUAR_at L st X (q_set_ia Q) m'.
Proof.
intros L st X Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT IA'.
unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend q_set_ia].
assert (DT : disjoint_from W (aq_tcache L) 32).
{ apply ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. Local Ltac2 Set LiaHints.tbl := fun () => "0040>15132752779.2116515709918.2021144446923.2124957545227.2100000300600900<S1AS1AS1AS1A".
lia. }
assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
{ unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
repeat split; apply ARepQP.disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
destruct DG as (DG1 & DG2 & DG3).
assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
{ intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
apply ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & A).
specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
split; [| split; [| split; [| split; [exact IA'| split; [| exact NUM]]]]].
- eapply aquar_glob_const_frame; eassumption.
- eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
- eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
-
destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
unfold qcoupled. cbn [q_loc q_glob q_pend]. cbv zeta.
split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
split; [exact BS|]. split; [exact PS| exact NN].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition Wnull (SP t : Z) : list (Z * Z) :=
[(SP - 4096, SP); (0xa3740, 0xa3740 + 0x81030); (0x131fc8, 0x131fc8 + 4); (t + 3168, t + 3169)]%Z.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
/\ (snd iv <= 0x9f1b0 \/ 0x9f270 <= fst iv)
/\ (snd iv <= 0xa3740 \/ 0x124770 <= fst iv)
/\ (snd iv <= 0x131fc8 \/ 0x131fcc <= fst iv)) CI.
#[using="HL"] Lemma AREP_null : forall L st X Q m m' SP,
alayout_ok L -> AREP (AHQ DI ASEC AFK) L st X m -> AQUAR_at L st X Q m ->
munch (Wnull SP (al_t L)) m m' -> wmono bsegs m m' -> ATOP + 4096 <= SP ->
rw_cells bsegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] -> aintal true m' ->
AREP (AHQ DI ASEC AFK) L st X m' /\ AQUAR_at L st X (q_set_ia Q) m'.
Proof.
intros L st X Q m m' SP ALO AR AQ MU WM HSP UNW' IA'.
set (W := Wnull SP (al_t L)) in *.
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON.
pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
unfold aobj in OT, OC, ORS, ON, OS, OFK, ODT. pose proof (ao_space L ALO) as RSP.
pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS, OFK, ODT.
pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. pose proof (ad_t_nodes L ALO) as D_t_n.
pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
unfold adisj in D_t_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_d.
assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
/\ shad (al_res L + 137439023104) <= 17594332446720).
{ rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0480>10317707088.1 10450661196.0 10833985377.0 11316741985.0 1174635441.0  11932486566.0 12011399388.1112011399388.1312074188401.0 12424292897.0 12466250849.0 12693510042.0 12877090629.1 12884907546.0 13097809467.1 13284001889.0 13668301562.0 14003831931.2 14015374737.0 14156105569.0 14843047521.0 1489739297.0  15702755169.0 16075693601.0 16534157257.1 16744448026.0 16776985498.0 16819224858.0 1685717371.0  16872684250.0 17142656993.0 17182596419.4 17516952106.0 18106462146.4 19033280097.0 19326977656.2 19825578598.0 20228638561.0 20780272588.0 21938576305.0 22380900506.0 22452704993.0 22749869729.0 22753993626.0 23454356593.0 23683026033.0 24990232882.6 25096308066.5 2552580386.1  2579967585.0  25927571866.0 25936419883.0 25942124698.0 26238245128.0 26752806805.0 27791511834.0 2791086392.3  28739967409.0 29455943531.0 29789203969.0 30349224161.0 30912897340.3 31102089014.6 31933984517.3 31974293055.6 32148301793.0 32201349065.1 32583808113.0 32917795153.6 33054871194.0 33945872673.0 34081784602.0 34521219823.7 34605942042.0 34767466017.0 34808658458.0 3493811297.0  35608742817.0 3578486597.0  36087876001.0 36449675461.1 36478104782.2 36782690527.2 36958550341.1 38167166234.0 38436634709.0 38692635477.0 38907343899.9 38948636245.0 38976513754.0 39012636437.0 39076636629.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39332637397.0 39396637589.0 39412637669.0 39716638549.0 40063858913.0 4016855089.0  40463950405.0 40550412698.0 40555353201.0 40582950170.0 40653080609.0 40682004513.0 40771319841.0 40916976638.6 41120432332.3 41163234465.0 41331042586.0 41604975041.0 41621129249.0 41746907126.6 41772873761.0 42101483546.0 42197754993.0 4234258273.0  42411609006.0 42509970977.0 42582682593.0 43394716785.0 43498236257.0 43554307580.3 43556650069.0 43781106499.3 45279912730.0 45368611111.1145834946401.0 4585549409.0  47010513865.0 47164711649.0 47225255969.0 47262993329.0 47298263521.0 47364842906.0 47446352417.0 47742405329.0 48252416741.3348569374753.0 48629766177.0 48880235586.7 50210523465.0 50338523849.0 5079207062.11 50850525385.0 51209830554.0 51228748878.1151746528073.0 51970569626.0 52194529417.0 52298115873.0 52376922934.0 52386529993.0 52489829152.4 52551278971.4 52775454234.0 5287053885.2  53148547354.0 53161170186.0 53410533065.0 53441943969.0 54178535369.0 54180105358.1154567155105.0 54620176929.0 54953652027.5 55117453473.0 55267958817.0 55330538825.0 55458539209.0 55531793818.0 5559110211.1  55842540361.0 56062205002.0 56104427370.0 56305755233.0 56354541897.0 56866543433.0 56994543817.0 57170013745.0 57378544969.0 57442545161.0 57484626142.6 57506545353.0 57570545545.0 57762546121.0 57826546313.0 57890546505.0 57966782994.6 58066547129.0 58146547273.0 58424040929.0 58466548233.0 58530548425.0 58658548809.0 588087689.1   58867622849.9 58914549577.0 59235419057.0 59308586510.3 59452556646.0 59466111130.0 59554551497.0 59810552265.0 59900823562.0 6000075077.6  6002171134.4  60066553033.0 60322553801.0 60524831429.1 60946143649.0 61090556105.0 61346556873.0 61820339768.4 62005321761.0 62242559561.0 62274559721.0 62370559945.0 62381190561.0 62487006817.0 62498560329.0 62754561097.0 63030103191.6 63739442122.0 63766807670.0 63993005153.0 64191649598.6 64348587873.0 64418702959.1064420796626.6 64532545057.0 64823954913.0 65179852321.0 66048936517.1 66062975450.0 66149329551.2666151427842.1766151427842.1866205764506.0 66263364923.1 66615748641.0 66863253345.0 67028052790.6 67240953178.0 67469470029.1267573762977.0 67723395739.5 68179776204.0 68331430219.0 6859089733.7  68678800481.0 7454607049.1  7457518318.6  7489863818.0  7623454362.0  8446217697.0  8459899809.0  8488167450.0  8849157729.0  9173904202.3  9925009062.0  00000100200300400500600I00_00`00a00b00c00d00e00f00g00h00i00j00k00l00m00n00o01001101201301401501601>01?01G01H01L01M01N01O01P01Q01R01S01T01U01V01^01f01g01h01i01j01k01l01m01n02202302402502602;02E02I02M02N02O02P02[02\02]02^02j02k02l02m02n02o03003103203603:03;03<03=03>03P03Q03R03S03T03U03V03W03X03Y03Z03[03\03]03^03_03`03a03b03c03d03e03i03n03o04004104204304404504604704804904:04;04<04A04B04F04G04]04^04_04`04a04b04c04d04e04f04g05J05K05L05]05^05_06006106206E06F06G06H06I06J06K06R06S06T06X06Y06Z06[06\06]07007107207:07;07<07=07>07?07@07A07B07C07D07E07F07G07H07I07J07N07O07P07Q07R07S07Z07[07\07]07^07_07`07a08608708808<08=08>08?08@08A08L08T08U08V08W08X08Y08Z08b08c08d08e08f08g08h08i08j08k08l08m08n09209309E09Z09[09\09]09^09_0:70:C0:O0:P0:Q0:R0:S0:T0:U0;40;50;=0;>0;?0;H0;I0;J0;V0;W0;X0;Y0;Z0;[0;\0;a0;bSSSSSSS3HSP2H12H32H42OT1HS3HSP2OT2H12H32H42H51HSSSSSSFSSSSSSSSSSSSSSSSS3RSP2HcSS3RSP2HcSS2QSSSSSSSSSSSS3HSP2HaS2Q13RI1SSSSSSSSS2HcSSSSS3POSS3HSP2OT1HS2Q6S2OTSSSS2Q52Q63RI1SSSS2Q23RI23RI3SSSSSSSSS2HcS2QSSSSSS2Q12Q23RI23RI32P4SSSSSSSSSSSSSSSSSSSSSS2OTS3POSSSSSSSSSSSSSSSS3RI1SS2HcSS2OT3ORS7D_t_res2B12B2SSSSSSSSSSS3ORS3RHI1H2H02H42H52H93H103H143H19SSS3ORS2H33SR31H2OCSSS3HSP2OT3ORS2B21HSSS2OT3ORS7D_t_res2B1SSSSSSS2Q52Q6SSS2HaSSSSSS2OT3ORS7D_t_res2B1SSS3RI12P5SSSSSSSSSSSSSSSSS2HaSSSSSS3HSP1HSSSSSSSS3RSP3CLB2Q12Q22P52P4SSS2HkSSSSSS3ORS2H12OCS3SR12H1SSSSSSS3RSP2HcSSSSSSSSSSSSS2OTSS2OT3SR13SR32H12H3S7D_t_res2H12H35D_t_cSSSSSS2RM2AM1H2H02H42H92Q42Q7S2RM1H2H02H4S2AL1H2H02H4SFSSSSS3HSP2OT2ON2OS5D_t_n5D_t_s2Ha1HSS2Q13RI1SSS3RI23RI3SSS2Q63RI23RI3SSSSSSS3POSS".
lia. }
destruct SHRES as (SR1 & SR2 & SR3).
assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI ->
(A + k <= 0xa3740 \/ 0x124770 <= A) -> (A + k <= 0x131fc8 \/ 0x131fcc <= A) -> disjoint_from W A k).
{ intros A k H1 H2 H3 H4 H5. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 H5 HSP OT. lia. }
assert (Kobj : forall A k, AIMG_HI <= A -> 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) -> disjoint_from W A k).
{ intros A k H1 H2 H3 H4. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 HSP. lia. }
assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W A k).
{ intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 ORS; lia | exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k).
{ intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 SR1; lia | exact H2 | clear -H3 SR3; lia | clear -H1 H3 SR1 SR3 OT; lia]. }
assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 3168 -> disjoint_from W A k).
{ intros A k H1 H2 H3. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT. lia. }
assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k).
{ intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 OC; lia | exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
{ intros b Hb. destruct (BUSY b Hb) as [CLB _].
destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
{ apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
assert (AQ' : AQUAR_at L st X (q_set_ia Q) m').
{ eapply AQUAR_null; [exact AQ | exact MU | exact WM | | exact IA'].
unfold W, Wnull. unfold AINSTANCE, AIMG_HI in *.
repeat (apply Forall_cons; [cbn [fst snd]; split; [clear -OT HSP; lia|]; split; [clear -OT HSP; lia|];
intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |]; clear -B1 B2 ORS OT HSP D_t_res; lia |]).
apply Forall_nil. }
split; [| exact AQ'].
split; [exact WF|].
split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
split.
{ destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW). unfold athread.
split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
exact UNW'. }
split.
{ intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
/\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
split; [| split; [| split]].
- eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
- eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
+ apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
+ apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
- eapply (aslots_update L W m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
+ intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
split; [reflexivity|]. split.
* apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
* intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
+ intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
- eapply (aslot_shadow_update L W m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
+ intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
+ intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
split; [exists (q_set_ia Q); exact AQ'|].
split.
{ cbn [ah_sec AHQ]. cbn [ah_sec AHQ] in HS.
eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | |].
- unfold sec_untouched, aknown, W, Wnull. unfold AINSTANCE, AIMG_HI in *.
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha HSP; lia|].
do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; clear -Ha; lia|]).
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT; lia|].
apply Forall_nil.
- apply sec_same_refl. }
split.
{ cbn [ah_depot AHQ]. cbn [ah_depot AHQ] in HD.
eapply (hd_frame _ HL L m m' W); [exact HD | exact MU | exact WM |].
unfold W, Wnull. unfold AIMG_HI in *.
repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha OT ON OS HSP D_t_n D_t_s; lia|]). apply Forall_nil. }
split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil].
intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
/\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
- intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
- intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HL CI_OK"] Theorem afree_nullP : afree_null_stmt CI (AHEAP_P (AHQ DI ASEC AFK)).
Proof.
unfold afree_null_stmt. intros until tr. intros AH MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
{ destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
destruct UNWX as (trt & FUNW & TRU).
destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
cbn [ah_quar ah_sec ah_depot ah_fake AHQ] in HQ, HS, HD, HFK. destruct HQ as [Q AQ].
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.
pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
unfold aobj in OT, ORS, OFK, ODT. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, ORS, OFK, ODT.
pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
unfold adisj in D_t_res, D_t_f, D_t_d.
pose proof RT as RT0.
destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
& PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
pose proof AQ as AQ0. destruct AQ0 as (_ & _ & _ & (FL & IAS & IAM) & CP & _).
unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM.
unfold AIMG_HI, AFREE_STACK, UDEPTH in *.
box CL5.
eapply evtF_mono.
{ eapply (free_null_spec (q_ia Q) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
(al_t L) (al_ctx L) lo (al_top L) (al_bot L) trt).
all: try lazymatch goal with
| |- stk _ _ _ _ => first [exact ST | exact IAS]
| |- mem_inv _ _ => exact MI
| |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
| |- afree_unw _ _ _ _ _ _ => exact FUNW
| |- _ = true -> _ => exact IAM
end.
Local Ltac2 Set LiaHints.tbl := fun () => "00H0?10317641044.17210317641044.21 1047820382.21  15870411829.25 17986879152.21 19033156465.21 24215381656.17231220694215.8  35005089235.14 36782690527.2  40461571878.10 40461571878.6  40463821211.5  52569147371.14 53238998938.2  54969794426.21 6027852627.14  6507725776.21  8800126135.12  8800126135.16  8800126135.17  8800126135.19  8800126135.21  8806431371.18  00000500;00@00W00\00i00n01601B01F01U01[01d02H02M02U02a03303D03a04=04_05M05fS3LSJS4STK1S3CL2S3OFK3AR81H2H02H42H52H9S3BOTS2LO3BOT4STK3S3LSJS3BOT2LOS3OFK3ODT2SFS2QSS3OFK1R2K12K31HS2SK1HS1R2Q12Q3S3BOT2LO2OT3OFK3ODT5D_t_f5D_t_d2SF1HS3Gs5S4STK31HS3OFK3ODT2SFS4STK14STK24STK31HS3BOT2LO3TL22SK1HS3BOT2LO4TL4u1R2Q12Q32Q52Q61HS3BOT2LO3OFK5D_t_f1R2K12K31HS3BOT2LO1R3Gs23Gs33Gs43Gs52Ct2SF1HS3BOT2LO3ORS3RSP7D_t_res1R3CLB2P12P22P52P43FITS3BOT2LO4TL1u3A471H2H02H4".
all: try lazymatch goal with
| |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact T0
| |- rw_cells _ _ _ _ => assumption
| |- @eq word _ _ => first [exact TP | exact Ha0 | reflexivity]
| |- _ \/ _ => first [unboxed CL5 | pose proof CL5 as Y; unbox Y; lia]
| |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
end.
all: try assumption.
all: unfold AIMG_HI, UDEPTH in *.
all: try (generalize LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 RA4; clear; intros; lia).
all: match goal with |- ?G => idtac "REMF" G end. }
cbv beta. intros ms' PM.
destruct PM as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & UNW' & FL' & IAS' & IAM').
change (munch (Wnull (bv_unsigned sp) (al_t L)) m m') in MU.
assert (IA' : aintal true m').
{ unfold aintal, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN. split; [exact FL'|]. split; [exact IAS'|]. intros _. exact IAM'. }
destruct (AREP_null L st X Q m m' (bv_unsigned sp) ALO AR AQ MU WM ltac:(atop_facts; clear -LO BOT STK3; lia) UNW' IA') as [AR' AQ'].
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
{
intros a Ha CLA. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Ha.
word_range sp SPR.
unfold Wnull. cbn [outside].
destruct CLA as [SK | [CIa | [BLK | SH]]].
- clear -SK Ha LO BOT STK3 TL2. lia.
- destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbn [fst snd] in *.
unfold AIMG_HI in *. clear -R Q1 Q3 Q5 Q6 LO BOT STK3 TL4u. lia.
- destruct BLK as ([[q|cls] A' n'] & Hin & R); cbn [ab_addr ab_size] in R.
+ destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
* destruct (BUSY b Hb) as [CLB _].
destruct (PERC (xb_class b) CLB) as (P1 & P2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR).
pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
{ apply PR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 P1) KB) as (P5 & P4 & P0).
pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
subst A' n'. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
clear -R P5 P4 P1 P2 CLB RSP FIT ORS D_t_res LO BOT STK3. lia.
*
cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
unfold ablk, KLS, AIMG_HI in Gs2.
clear -R Gs2 Gs3 Gs4 Gs5 SF Ct LO BOT STK3. lia.
+ destruct (proj1 (proj2 BL) cls A' n' Hin) as (K1 & K2 & K3).
clear -R K1 K2 K3 OFK D_t_f LO BOT STK3. lia.
- destruct SH as (a' & Ha' & ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
assert (A47 : 0 <= a' < 2^47).
{ destruct Ha' as [SK | [CIa | FK]].
- atop_facts. clear -SK SPR. lia.
- destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
unfold AIMG_HI in *. clear -R Q1 Q3. lia.
- destruct FK as (cls & FA & sz & Hin & R). destruct (proj1 (proj2 BL) cls FA sz Hin) as (K1 & K2 & K3). clear -R K1 K3 OFK. lia. }
clear -A47 LO BOT STK3 TL1u. Z.div_mod_to_equations. lia. }
split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
cbn [ah_fake AHQ].
assert (SF : 0x800b6e00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
{ rewrite shad_div, shlen_div. unfold ASHOFF in *. pose proof atop_range as AR8. clear -OFK AR8. Z.div_mod_to_equations. lia. }
eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |].
unfold fake_untouched, Wnull.
repeat (apply Forall_cons; [cbn [fst snd]; clear -OFK ODT OT SF D_t_f D_t_d LO BOT STK3; lia|]). apply Forall_nil.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
