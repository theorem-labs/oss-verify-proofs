(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase ABytes AModelFacts ARep ALayout AHeapP ARepKit ARepFrame ARepExt.
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
Definition apre (L : alayout) (iv : Z * Z) : Prop :=
fst iv < snd iv -> ATOP <= fst iv \/ (fst iv = al_t L + 3168 /\ snd iv = al_t L + 3169).
#[using="Type"] Lemma pre_clear : forall L W A k,
Forall (apre L) W -> 0 <= k ->
A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) ->
disjoint_from (List.filter nonempty W) A k.
Proof.
intros L W A k EXT Hk D1 D2. apply disjoint_from_Forall.
induction W as [|[lo hi] W IH]; [constructor|].
inversion EXT as [| x l E1 E2]; subst.
rewrite filter_cons_eq. unfold nonempty at 1. cbn [fst snd].
destruct (Z.ltb_spec lo hi) as [LT|GE]; [| apply IH; exact E2].
constructor; [| apply IH; exact E2]. cbn [fst snd].
unfold apre in E1. cbn [fst snd] in E1. specialize (E1 LT).
clear IH E2 EXT. Local Ltac2 Set LiaHints.tbl := fun () => "0010>30294239397.1300000:S2D12D22E1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Ext2.
Variable H : aholes.
Hypothesis HL : ahole_laws H.
#[using="HL"] Theorem AREP_frame_pre : forall L st X m m' W,
alayout_ok L -> AREP H L st X m -> munch W m m' -> wmono bsegs m m' ->
Forall (apre L) W ->
rw_cells bsegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] ->
AREP H L st X m'.
Proof.
intros L st X m m' W ALO AR MU0 WM EXT UNW'.
pose proof (munch_filter_nonempty W m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty W) in *.
pose proof (ao_fake L ALO) as FK. Local Ltac2 Set LiaHints.tbl := fun () => "02V0>10317707088.1 10450661196.0 12693510042.0 12877090629.1 12884907546.0 13097809467.1 13668301562.0 14003831931.2 16534157257.1 16744448026.0 16776985498.0 16819224858.0 16822287510.7 1685717371.0  16872684250.0 17032418858.4017182596419.4 17516952106.0 18106462146.4 18464866142.7 19326977656.2 20780272588.0 22380900506.0 22753993626.0 24990447293.9 25096308066.5 2552580386.1  25927571866.0 25942124698.0 26149833681.7 26238245128.0 26752806805.0 27791511834.0 2791086392.3  30912897340.3 31933984517.3 32201349065.1 32832863258.9 32917795153.6 33054871194.0 34081784602.0 34521219823.7 34605942042.0 34808658458.0 34922986513.7 3578486597.0  36449675461.1 36478104782.2 36782690527.2 36958550341.1 37936500651.1138167166234.0 38436634709.0 38692635477.0 38907343899.9 38948636245.0 38976513754.0 39012636437.0 39076636629.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39332637397.0 39396637589.0 39412637669.0 39716638549.0 40463950405.0 40550412698.0 40582950170.0 41120432332.3 41331042586.0 42101483546.0 42411609006.0 43554307580.3 43556650069.0 43781106499.3 45279912730.0 47010513865.0 47364842906.0 48873933567.5 48873933567.8 48880235586.7 50210523465.0 50338523849.0 50850525385.0 51209830554.0 51746528073.0 51853062327.1751970569626.0 52194529417.0 52386529993.0 52489829152.4 52551278971.4 52775454234.0 53148547354.0 53161170186.0 53410533065.0 54178535369.0 54953652027.5 55330538825.0 55458539209.0 55531793818.0 5559110211.1  55842540361.0 56062205002.0 56104427370.0 56354541897.0 56866543433.0 56994543817.0 57378544969.0 57442545161.0 57482589668.1057506545353.0 57570545545.0 57762546121.0 57826546313.0 57890546505.0 58066547129.0 58146547273.0 58466548233.0 58524927621.4 58530548425.0 58658548809.0 588087689.1   58867622849.9 58914549577.0 59308586510.3 59466111130.0 59554551497.0 59810552265.0 59900823562.0 60066553033.0 60322553801.0 60524831429.1 61090556105.0 61346556873.0 61820339768.4 62242559561.0 62274559721.0 62370559945.0 62498560329.0 62754561097.0 63739442122.0 64418702959.1164418702959.8 64420796626.6 66048936517.1 66062975450.0 66149329551.2666151427842.1766151427842.1866205764506.0 66263364923.1 67240953178.0 67477796656.1367723395739.5 68179776204.0 68331430219.0 6859089733.7  7454607049.1  7457518318.6  7489863818.0  7623454362.0  8488167450.0  9173904202.3  00000100200300400500600700800900:00;00<00F00G00H00o01701801@01J01N01O01P01Q01W01_01`01a01b01l01m01n01o02302802<02=02G02R02S02T02`02a02b02l02m02n03203603703L03M03N03O03a03b03c03d03e03f03g03h03i03j03k03l03m03n03o04004504604704804=04>04B04C04D04E04M04]04m04n04o05005105205305405505605=05>05?05@05A05B05C05K05L05M05N05O05P05Q05R05S05T05U05V05W05a05b05c05d05e05f05g05h05i05m05n05o06006E06F06J06K06L06M06N06O06P06Q06R06S06[06\06]06^06_06`06a07707A07V07W07X08008<08H08I08J08K08j09209309409=09>09J09K09L09M09RSSSSSFSSSSSSS3ATR2OT1ESSS3ORS3ORH1H2H02H42H52H93H103H143H153H19S3RSP2HcSS3RSP2HcS3ATR2OT1ES2QSSSSS2Ha1ES2Q13RI1SSSS3ATR2OT1ESSSS2HcS3POSS2Q6SS3ATR1H2H0S2Q52Q63RI1SSS2Q23RI23RI3SSS3ATR2OT1ESSS2HcS2QSSS3ORS7D_t_res1E2B12B2SSSS2Q12Q23RI23RI32P4SSSSSSSSSSSSSSSS3POSSSSS3RI1SS2HcSSSS3ATR2H3S3ATR3SAT3SR32H3S3ORS2H32OT1H2OCSSSSSSSSSS2Q52Q6SSSSSSS3RI12P5SSSSSSSSSSSSS2Ha2E12E2SSSSSSSSS2HaSSSS3RSP3CLB2Q12Q22P52P4SS2HkSSSSSSSSSS3RSP2HcSSSSSSS2OT3SAT3SR13SR32H12H3S2OT2H12H3S7D_t_res2H12H35D_t_cSSS2RM2AM1H2H02H42H92Q42Q7S2RM1H2H02H4S2AL1H2H02H4SFSS3ATR2OT2ON2OS2Ha1E5D_t_n5D_t_sS2Q13RI1SSS3RI23RI3SS2Q63RI23RI3SSSS3POS".
pose proof (aobj_img _ _ FK ltac:(lia)) as FKI. unfold aobj in FK. destruct FK as (FK3 & FK1 & FK2 & FKS & _).
unfold sclr, KLS in FKS. unfold AIMG_HI in FKI. pose proof atop_range as ATR. pose proof ATOP_al16 as ATA.
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
pose proof (ao_res_hi L ALO) as ORH.
unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS. pose proof (ao_space L ALO) as RSP.
pose proof (fun A k => pre_clear L W A k EXT) as KX. cbn beta in KX. fold W' in KX.
pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_fake_res L ALO) as D_f_res.
pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
unfold adisj in D_t_f, D_c_f, D_f_res, D_n_f, D_s_f.
assert (SAT : 0x10006fef8000 <= shad ATOP <= 0x10007fef8000) by (rewrite shad_div; unfold ASHOFF; clear -ATR; Z.div_mod_to_equations; lia).
assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
/\ shad (al_res L + 137439023104) <= shad ATOP).
{ rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS ORH. Z.div_mod_to_equations. lia. }
destruct SHRES as (SR1 & SR2 & SR3).
pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_res, D_t_c.
assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI -> disjoint_from W' A k).
{ intros A k H1 H2 H3. unfold AIMG_HI in H3. apply KX; [exact H2| clear -H3 ATR; lia| clear -H1 H3 OT; lia]. }
assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k).
{ intros A k H1 H2 H3. apply KX; [exact H2| clear -H3 SR3 SAT ATR; lia| clear -H1 H3 SR1 SR3 SAT OT; lia]. }
assert (Kobj : forall A k, 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) -> disjoint_from W' A k).
{ intros A k H2 H3 H4. apply KX; [exact H2| exact H3| exact H4]. }
clear KX.
assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k).
{ intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 3168 -> disjoint_from W' A k).
{ intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OT; lia | left; exact H3]. }
assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k).
{ intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
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
- eapply (aslots_update L W' m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
+ intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
split; [reflexivity|]. split.
* apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
* intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
+ intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
- eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
+ intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
+ intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
{ intros b Hb. destruct (BUSY b Hb) as [CLB _].
destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
{ apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
split.
{ eapply (hq_frame _ HL L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
- unfold quar_untouched. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE]. unfold nonempty in NE. cbn [fst snd] in NE. apply Z.ltb_lt in NE.
pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold apre in E. cbn [fst snd] in E. specialize (E NE).
unfold AINSTANCE in *.
split; [clear -E OT ATR; lia|]. split; [clear -E OT ATR; lia|]. split; [clear -E OT ATR; lia|]. split; [clear -E OT ATR; lia|].
intros b Hb. destruct (BB b Hb) as [B1 B2]. destruct (xb_st b); [exact I| |]; clear -E B1 B2 ORS D_t_res ATR; lia.
- unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
split.
{ eapply (hs_frame _ HL L st st X X m m' W'); [exact HS | exact MU | exact WM | |].
- unfold sec_untouched, aknown. apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold apre in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)).
clear -E Ha OT ATR. destruct E as [E|[E1 E2]]; [do 4 right; left; lia| do 5 right; left; lia].
- apply sec_same_refl. }
split.
{ eapply (hd_frame _ HL L m m' W'); [exact HD | exact MU | exact WM |].
apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold apre in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)).
pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s. unfold adisj in D_t_n, D_t_s.
clear -E Ha OT ON OS D_t_n D_t_s ATR. lia. }
split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
/\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
- intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
- intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Ext2.
End CANSEC1.
