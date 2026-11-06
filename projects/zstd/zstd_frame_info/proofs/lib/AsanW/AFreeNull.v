(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import ASecFacts AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts F_aalloc_s F_aalloc1 F_aunwind F_afree_iseg F_afree_null F_afree_arep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition q_set_ia (Q : qconc) : qconc := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q).

(* [comment removed for export] *)
#[using="Type"] Lemma AQUAR_null : forall L st X Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> wmono asegs m m' ->
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
  { apply ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. Local Ltac2 Set LiaHints.tbl := fun () => "0040>16515709918.2059579628427.216043359179.21 61230484235.2100000300600900<S1AS1AS1AS1A".
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
  - (* [comment removed for export] *)
    destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
    unfold qcoupled. cbn [q_loc q_glob q_pend]. cbv zeta.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wnull (SP t : Z) : list (Z * Z) :=
  [(SP - 4096, SP); (0xa2080, 0xa2080 + 0x81030); (0x130908, 0x130908 + 4); (t + 3168, t + 3169)]%Z.

Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0x9daf0 \/ 0x9dbb0 <= fst iv)
                                  /\ (snd iv <= 0xa2080 \/ 0x1230b0 <= fst iv)
                                  /\ (snd iv <= 0x130908 \/ 0x13090c <= fst iv)) CI.

#[using="HL"] Lemma AREP_null : forall L st X Q m m' SP,
  alayout_ok L -> AREP (AHQ DI ASEC AFK) L st X m -> AQUAR_at L st X Q m ->
  munch (Wnull SP (al_t L)) m m' -> wmono asegs m m' -> ATOP + 4096 <= SP ->
  rw_cells asegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] -> aintal true m' ->
  AREP (AHQ DI ASEC AFK) L st X m' /\ AQUAR_at L st X (q_set_ia Q) m'.
Proof.
  intros L st X Q m m' SP ALO AR AQ MU WM HSP UNW' IA'.
  set (W := Wnull SP (al_t L)) in *.
  (* [comment removed for export] *)
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON.
  pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, ODT. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. pose proof (ad_t_nodes L ALO) as D_t_n.
  pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_d.
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= 17594332446720).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Local Ltac2 Set LiaHints.tbl := fun () => "0490>10317707088.1 10589696033.0 1093161894.0  11128200705.0 11896768362.0 11994843857.0 12011399388.1112011399388.1312076917681.0 12467668890.0 12698334129.0 12877090629.1 13097809467.1 13341084364.0 1364358257.0  13645646618.0 13673902049.0 14003831931.2 1420605082.0  14974688666.0 15315244314.0 15509219169.0 15515497321.5 15515743081.5 15705326390.0 15886608609.0 1611527265.0  16138165857.0 16352056433.0 16434477089.0 1646164001.0  16534157257.1 1685717371.0  17182596419.4 17269308897.0 17538574561.0 18058937242.0 18106462146.4 18165372769.0 18794319457.0 18819676314.0 19046035041.0 19326977656.2 19997301913.4 20019976641.0 20273424225.0 21860639857.0 21882970224.4 22611539617.0 23071010401.0 23072338465.0 23781981302.0 24140679201.0 24427938890.0 24496633676.0 24990232882.6 25096308066.5 2552580386.1  25777298977.0 25825504026.0 26238245128.0 26315217818.0 27519611425.0 2791086392.3  28266557450.0 29185706913.0 29814163489.0 29910885658.0 30527187937.0 30720233178.0 30912897340.3 31102089014.6 3134486341.0  31933984517.3 32201349065.1 32439215969.0 32917795153.6 33397679505.0 33660189286.0 34521219823.7 34991432652.0 35000780641.0 36449675461.1 36478104782.2 36622244257.0 36782690527.2 36958550341.1 37529178593.0 37603466657.0 37991092769.0 38167166234.0 38183653409.0 38436634709.0 38471736266.0 38654162795.0 38692635477.0 38845773921.0 38907343899.9 38948636245.0 38968368703.6 39012636437.0 39076636629.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39332637397.0 39396637589.0 39412637669.0 39716638549.0 40019950149.0 4073600417.0  41120432332.3 41331042586.0 41973247322.0 42363246641.0 42411609006.0 42590784625.0 43129210721.0 43554307580.3 43556650069.0 43714289050.0 43781106499.3 44162190961.0 4418943009.0  44396039246.1144517398945.0 44519173658.0 44708664986.0 44817489946.0 44892266778.0 45149336689.0 45368611111.114567690598.0  45916044833.0 46353558945.0 46431726513.0 47650515785.0 47906516553.0 47938516713.0 47991068186.0 48034516937.0 48162517321.0 48231386721.0 48880235586.7 49108017185.0 49186520393.0 49214230042.0 49314520777.0 49570521545.0 49698521929.0 50210523465.0 50338523849.0 50339438177.0 50392742049.0 50453942426.0 50734796790.6 5079207062.11 5081201441.0  50850525385.0 51209830554.0 51257640801.0 51362526921.0 51585869630.6 52130529225.0 52386529993.0 52489829152.4 52551278971.4 52770531145.0 5287053885.2  53154532297.0 53339102113.0 53410533065.0 53666533833.0 53922534601.0 54374850081.0 54387727403.0 54560037217.0 54629052321.0 54953652027.5 55330538825.0 55566237466.0 5559110211.1  55714539977.0 55889437793.0 56098541129.0 56145280922.0 56336678426.0 56378177377.0 56610542665.0 5674528305.0  56918404257.0 5704536858.0  57120072442.0 57123395617.0 57484626142.6 57588988434.6 57806694874.0 57949483930.0 58786549193.0 588087689.1   58867622849.9 58914549577.0 59042549961.0 59304377889.0 59308586510.3 59342457121.0 59466111130.0 59490551305.0 59554551497.0 59618551689.0 59874552457.0 59938552649.0 6000075077.6  6002171134.4  60114553273.0 60194553417.0 60228756378.0 60514554377.0 60524831429.1 60578554569.0 60661562634.0 60968722986.0 61438389046.6 61820339768.4 61986558793.0 62172904993.0 62202573921.0 62256894362.0 62434560137.0 62626560713.0 62920058721.0 63014898609.0 63030103191.6 63064052449.0 64418702959.1064420796626.6 65198948833.0 65238063537.0 65459601425.3 66048936517.1 66263364923.1 66496141345.0 66723112033.0 67469470029.1267723395739.5 67805161126.0 67953059978.0 68218897406.6 68305811425.0 68331430219.0 68536850325.0 6859089733.7  6922614497.0  6945320078.11 7007477217.0  7454607049.1  7457518318.6  7541892193.0  7883819041.0  8616403674.0  9173904202.3  9315624049.0  9540952602.0  9983539745.0  00000100200300400500600I00_00`00a00b00c00d00e00f00g00h00i00j00k00l00m01401>01?01@01A01B01C01D01E01F01G01O01P01Q01R01Z01[01\01]01^01b01f01g01h01i02202302402502602702802902A02I02J02K02L02M02N02O02S02T02U02V02W02X02Y02^02h02i02m02n02o03:03;03<03H03I03J03K03O03P03T03U03V03W03X03Y03Z03[03\03]03^03_04104204604704804904:04;04<04=04>04?04@04A04B04G04H04I04J04K04L04M04R04S04T04X04Y04Z04m04n04o05005105205305I05J05K05L05M05N05O05P05Q05R05S05T05e05f05g05h05i05j05k05l05m05n05o06006106B06C06D06E06F06G06K06L06M06T06U06V06Z06[06\06]06^06_06`06a06b06c06k06l06m06n06o07007107207307407507607707807907:07>07E07F07G07H07I07^07_07`07a07e07f07g07h07i07j07k07l08708?08@08A08B08C08D08E08F08G08H08P08Q08R08S08T08U08V08W08X08Y08Z08l09A09B09C09G09H09I09J09K09j0:20:30:40:80:90::0:;0:D0:E0:X0:Y0:Z0:f0:g0:h0:i0:n0:o0;00;1SSSSSSS3HSP2H12H32H42OT1HS3HSP2OT2H12H32H42H51HSSSSFSSSSSSSSSS2RM2AMS2Q42RM2Q7SSSSSSSSSS3RSP2HcSSSS3RSP2HcSSSSS2QSS2ALSSSS3ORS3RHISSSSSSSS3HSP2HaS2Q13RI1SSSSSSS2HcSSSSSSS3POSS3HSP2OT1HSS2Q6SSS2Q52Q63RI1SSS2Q23RI23RI3SSSS2HcSS2QSSSSSSSSSSSSS2Q12Q23RI23RI32P4SS2OTSSSSSSSSSSSSS3POSSSSSSSS3RI1SSS2HcSSS2OT3ORS7D_t_res2B1SSSSSSS2OT3ORS7D_t_res2B12B2SSSSSSSSSSSS3ORS2H33SR31H2OCSSSSSSSSSSSSS3HSP2OT3ORS2B21HSSSSSS2OTSSS2Q52Q6SSS2HaSSSSSSSSSS3RI12P5SSSSSSSSSSSSSSSS2HaS3HSP1HSSSSS3RSP3CLB2Q12Q22P52P4SSSS2HkSSSSSSSS3ORS2H12OCS3SR12H1SSSSSSSSSS3RSP2HcSSSSSSSSSSS2OT3SR13SR32H12H3S7D_t_res2H12H35D_t_cSSS2RMSFSSS3HSP2OT2ON2OS5D_t_n5D_t_s2Ha1HS2Q13RI1SSS2OTSSSS3RI23RI3SS2OT3ORS7D_t_res2B1SSS2Q63RI23RI3SSSS3POSSSS".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHRES as (SR1 & SR2 & SR3).
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
            (A + k <= 0xa2080 \/ 0x1230b0 <= A) -> (A + k <= 0x130908 \/ 0x13090c <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4 H5. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 H5 HSP OT. lia. }
  assert (Kobj : forall A k, AIMG_HI <= A -> 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 HSP. lia. }
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 ORS; lia | exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 SR1; lia | exact H2 | clear -H3 SR3; lia | clear -H1 H3 SR1 SR3 OT; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 3168 -> disjoint_from W A k).
  { intros A k H1 H2 H3. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT. lia. }   (* [comment removed for export] *)
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 OC; lia | exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  (* [comment removed for export] *)
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
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). apply shad_mono.
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
        rewrite <- shad_add_shlen by (clear -AL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split; [exists (q_set_ia Q); exact AQ'|].
  split.
  { cbn [ah_sec AHQ]. cbn [ah_sec AHQ] in HS.
    eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown, W, Wnull. unfold AINSTANCE, AIMG_HI in *.
      (* [comment removed for export] *)
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
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, ORS, OFK, ODT. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, ORS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_f, D_t_d.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof AQ as AQ0. destruct AQ0 as (_ & _ & _ & (FL & IAS & IAM) & CP & _).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM.
  (* [comment removed for export] *)
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
    Local Ltac2 Set LiaHints.tbl := fun () => "00H0?10317641044.17210317641044.21 1047820382.21  17986879152.21 19033156465.21 22208142071.4  24215381656.17231220694215.8  36782690527.2  3787906515.14  40461571878.10 40461571878.6  40463821211.5  52569147371.14 53238998938.2  54969794426.21 56134185811.14 6507725776.21  8800126135.12  8800126135.16  8800126135.17  8800126135.19  8800126135.21  8804186758.10  00000500;00@00E00R00[00`00h00l01801G01M01V02:02?02G02S02e03603S03o04Q05?05PS3LSJS4STK1S3CL2S3BOTS2LO3BOT4STK3S3OFK3AR8S3LSJS3BOT2LOS2QSS3OFK3ODT2SFS3OFK1R2K12K31HS2SK1HS1R2Q12Q3S3BOT2LO2OT3OFK3ODT5D_t_f5D_t_d2SF1HS3Gs5S4STK31HS3OFK3ODT2SFS4STK14STK24STK31HS3BOT2LO3TL22SK1HS3BOT2LO4TL4u1R2Q12Q32Q52Q61HS3BOT2LO3OFK5D_t_f1R2K12K31HS3BOT2LO1R3Gs23Gs33Gs43Gs52Ct2SF1HS3BOT2LO3ORS3RSP7D_t_res1R3CLB2P12P22P52P43FITS3BOT2LO4TL1u3A47".
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
  (* [comment removed for export] *)
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { (* [comment removed for export] *)
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
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
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
      clear -A47 LO BOT STK3 TL1u. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
  (* [comment removed for export] *)
  cbn [ah_fake AHQ].
  assert (SF : 2148232192 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).   (* [comment removed for export] *)
  { rewrite shad_div, shlen_div. unfold ASHOFF in *. pose proof atop_range as AR8. clear -OFK AR8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |].
  unfold fake_untouched, Wnull.
  repeat (apply Forall_cons; [cbn [fst snd]; clear -OFK ODT OT SF D_t_f D_t_d LO BOT STK3; lia|]). apply Forall_nil.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
