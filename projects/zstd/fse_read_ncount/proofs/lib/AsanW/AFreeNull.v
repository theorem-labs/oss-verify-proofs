(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ASecFacts AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
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
{ apply ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. Local Ltac2 Set LiaHints.tbl := fun () => "0040>12584343499.2113888109451.2116133204747.2116515709918.2000000300600900<S1AS1AS1AS1A".
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
[(SP - 4096, SP); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4); (t + 3168, t + 3169)]%Z.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
/\ (snd iv <= 0x9f0f0 \/ 0x9f1b0 <= fst iv)
/\ (snd iv <= 0xa3680 \/ 0x1246b0 <= fst iv)
/\ (snd iv <= 0x131f08 \/ 0x131f0c <= fst iv)) CI.
#[using="HL"] Lemma AREP_null : forall L st X Q m m' SP,
alayout_ok L -> AREP (AHQ DI ASEC AFK) L st X m -> AQUAR_at L st X Q m ->
munch (Wnull SP (al_t L)) m m' -> wmono asegs m m' -> ATOP + 4096 <= SP ->
rw_cells asegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] -> aintal true m' ->
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
{ rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "03j0>10038099361.0 10317707088.1 10524228385.0 10954123084.0 11173954657.0 11274536766.6 11279297649.0 11354115190.0 11706929818.0 12011399388.1112011399388.1312168326222.1112231087258.0 12408284273.0 12610434122.0 12877090629.1 128948940.0   13097809467.1 14003831931.2 14103899297.0 14281758753.0 14303234273.0 14885359002.0 15643153306.0 16063336730.0 16075959562.0 16449052682.0 16534157257.1 1685717371.0  17182596419.4 17452631905.0 18106462146.4 18355890465.0 18359420769.0 1891303130.0  19019216746.0 19326977656.2 2025471457.0  20424888353.0 21448922060.0 21686312481.0 22238414741.0 22260686433.0 22380900506.0 22753993626.0 2314513377.0  23641242049.0 23880252385.0 24344347553.0 24990232882.6 25096308066.5 2552580386.1  25734436897.0 25773232682.0 26215040401.0 26238245128.0 26654231498.0 27330188401.0 2791086392.3  28260313910.6 28481059233.0 28977764826.0 29037308625.0 29322385062.0 30155742554.0 3045711206.0  30912897340.3 3103093281.0  31102089014.6 31836835377.0 31933984517.3 32201349065.1 32891160218.0 32917795153.6 33585235809.0 33970357169.0 34034574433.0 34081784602.0 34521219823.7 34739060257.0 3497739546.0  35249961889.0 36449675461.1 36478104782.2 36782690527.2 36815802337.0 36937208945.0 36958550341.1 37013199265.0 37740761825.0 37779520282.0 38333028321.0 38436634709.0 38664710177.0 38692635477.0 38907343899.9 38948636245.0 39012636437.0 39055692913.0 39076636629.0 39124129930.0 39172636981.0 39188636933.0 39220637093.0 39262210993.0 39268637205.0 39332637397.0 39396637589.0 39412637669.0 39447935009.0 39716638549.0 39838320481.0 40016178785.0 40377912241.0 4088600427.0  41120432332.3 41604406177.0 41764935073.0 42004161649.0 42411609006.0 43096011873.0 43487844001.0 43525804065.0 43554307580.3 43556650069.0 43781106499.3 44327776154.0 44395746225.0 45302567674.0 45368611111.1145815388193.0 46626512713.0 46670265919.6 46754513097.0 46882513481.0 4698531873.0  47138514249.0 47202514441.0 47266514633.0 47330514825.0 47586515593.0 47648606362.0 47650515785.0 47692412961.0 47826516409.0 47878439009.0 48226517513.0 48252416741.3348290517705.0 48453490970.0 48506950362.0 48880235586.7 49214230042.0 49698521929.0 50082523081.0 50146523273.0 50338523849.0 50531121377.0 5053188710.0  50577811489.0 5079207062.11 50850525385.0 51209830554.0 51234526537.0 51648059441.0 51970836321.0 52002528841.0 52034529001.0 52130529225.0 52258529609.0 52489829152.4 52551278971.4 52560693089.0 5287053885.2  53282532681.0 53410533065.0 53794534217.0 54169770337.0 54306535753.0 54393503265.0 54953652027.5 5559110211.1  55818384481.0 56074431045.0 56098541129.0 56482542281.0 56866543433.0 56881710945.0 57482380286.6 57484626142.6 57506545353.0 57762546121.0 58018546889.0 58322577050.0 58414883750.0 58420510305.0 588087689.1   58867622849.9 59063834785.0 5915703137.0  59308586510.3 59500554778.0 6000075077.6  6002171134.4  60066553033.0 60490127890.6 60524831429.1 60554890382.1161090556105.0 61820339768.4 62663473585.0 62718896225.0 63030103191.6 63434872090.0 63586393633.0 64371284065.0 64418702959.1064420796626.6 65368870513.0 65445025434.0 65716050714.0 65907119841.0 65917933665.0 66048936517.1 66149329551.2666151427842.1766151427842.1866263364923.1 66442924570.0 66578857626.0 66996096282.0 6725672449.0  67469470029.1267574755318.6 67669765089.0 67693676357.0 67723395739.5 68331430219.0 6859089733.7  7384966554.0  7454607049.1  7457518318.6  7460700193.0  8043637786.0  868163105.0   891212598.0   9129824289.0  9173904202.3  9237232683.0  9323683354.0  00000100200300400500900:00;00<00O00e01801901:01;01<01=01>01?01@01A01B01C01D01E01F01G01H01I01Q01R01Z01[01\01]01^01b01c01d01e01f01g01h01i01j01k01l01m01n02602>02?02@02A02B02C02D02E02I02J02K02L02M02N02O02P02U02V02`02a02e02f02g03203303403503603B03C03D03E03F03J03N03O03P03Q03R03S03T03U03V03W03X03j03k03l03m03n03o04004104204304404504604704804904:04;04<04=04B04C04D04E04F04G04H04I04N04O04S04T04U04V04l04m04n05205305405505605705805905:05;05<05=05>05?05@05c05d05e05f06706806906:06;06<06=06>06?06P06Q06R06S06T06U06V06W06X06Y06`06a06b06f06g06h06i06j06k06l07407507607707807907:07;07?07C07D07E07F07G07H07I07J07_07`07a07e07f08108908:08A08B08U08V08^08_08`08a08b08c08d09609K09L09M09N09O09P09Q09i0:50:A0:B0:C0:D0:E0:F0:e0:f0:g0:h0;00;10;:0;;0;<0;H0;I0;J0;K0;L0;M0;R0;S0;TSSSSSS2OTSSSS3HSP2H12H32H42OT1HS3HSP2OT2H12H32H42H51HS2OT3ORS7D_t_res2B1SSSSSFSSSSSSSSSSSS3RSP2HcSS3RSP2HcSSSSS2QSSSSSSSSSSSSSS3HSP2HaS2Q13RI1SSSSSSSS2HcSSSSSSSS3POSSS3HSP2OT1HSS2Q6SSS2Q52Q63RI1SSSSS2Q23RI23RI3SSSSS2HcS2QSSSSSSSSSSSS2Q12Q23RI23RI32P4SSSSSSSSSSSSSSSSSSSS3POSSSSSSSSS3RI1SS2HcSSSS2OT3ORS7D_t_res2B12B2SSS2OTSSSSSSSSSSSSSSS3ORS3RHI1H2H02H42H52H93H103H143H19SSSS3ORS2H33SR31H2OCSSSSSSSSS3HSP2OT3ORS2B21HSSSSSSSSSS2Q52Q6SSS2HaSSSSSSS3RI12P5SSSSSSSS2OTS2HaSSSSSSSS3RSP3CLB2Q12Q22P52P4SSS2HkSS3ORS2H12OCS3SR12H1SS3HSP1HSS2OT3ORS7D_t_res2B1SS3RSP2HcSSSSSSS2OT3SR13SR32H12H3S7D_t_res2H12H35D_t_cSSSSSSS2RM2AM1H2H02H42H92Q42Q7S2RM1H2H02H4S2AL1H2H02H4FSSSSS3HSP2OT2ON2OS5D_t_n5D_t_s2Ha1HSSSS2Q13RI1SS3RI23RI3SSS2Q63RI23RI3SSSSSS3POSSS".
lia. }
destruct SHRES as (SR1 & SR2 & SR3).
assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI ->
(A + k <= 0xa3680 \/ 0x1246b0 <= A) -> (A + k <= 0x131f08 \/ 0x131f0c <= A) -> disjoint_from W A k).
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
Local Ltac2 Set LiaHints.tbl := fun () => "00H0?10317641044.17210317641044.21 1047820382.21  17986879152.21 19033156465.21 24215381656.17231220694215.8  36782690527.2  37245297491.14 40461571878.10 40461571878.6  40463821211.5  52569147371.14 53238998938.2  53618232787.14 54969794426.21 6507725776.21  67244368949.25 8800126135.12  8800126135.16  8800126135.17  8800126135.19  8800126135.21  8806431371.18  00000500;00@00E00R00W00_00c00o01>01D01M02102602B02J02\03303D03a04=04_05M05fS3LSJS4STK1S3CL2S3BOTS2LO3BOT4STK3S3LSJS3BOT2LOS2QSS3OFK3ODT2SFS3OFK1R2K12K31HS2SK1HS1R2Q12Q3S3BOT2LO2OT3OFK3ODT5D_t_f5D_t_d2SF1HS3Gs5S3OFK3ODT2SFS4STK31HS4STK14STK24STK31HS3OFK3AR81H2H02H42H52H9S3BOT2LO3TL22SK1HS3BOT2LO4TL4u1R2Q12Q32Q52Q61HS3BOT2LO3OFK5D_t_f1R2K12K31HS3BOT2LO1R3Gs23Gs33Gs43Gs52Ct2SF1HS3BOT2LO3ORS3RSP7D_t_res1R3CLB2P12P22P52P43FITS3BOT2LO4TL1u3A471H2H02H4".
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
assert (SF : 2148232704 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
{ rewrite shad_div, shlen_div. unfold ASHOFF in *. pose proof atop_range as AR8. clear -OFK AR8. Z.div_mod_to_equations. lia. }
eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |].
unfold fake_untouched, Wnull.
repeat (apply Forall_cons; [cbn [fst snd]; clear -OFK ODT OT SF D_t_f D_t_d LO BOT STK3; lia|]). apply Forall_nil.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
