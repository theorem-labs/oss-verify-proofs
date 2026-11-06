(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase ABytes AModelFacts ASecFacts ARep ALayout AHeapP ARepKit ARepFrame.
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
Definition aext (L : alayout) (iv : Z * Z) : Prop :=
fst iv < snd iv ->
(al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
\/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
\/ ATOP <= fst iv
\/ (shad ATOP <= fst iv /\ snd iv <= shad (2^47)).
Definition nonempty (iv : Z * Z) : bool := fst iv <? snd iv.
#[using="Type"] Lemma sub_fp_filter_nonempty : forall W, sub_fp W (List.filter nonempty W).
Proof.
unfold sub_fp. induction W as [|[lo hi] W IH]; intros x Hx; cbn in *; [exact I|].
unfold nonempty in Hx. cbn [fst snd] in Hx. destruct (Z.ltb_spec lo hi).
- cbn in Hx. destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
- Local Ltac2 Set LiaHints.tbl := fun () => "0010=56461269045.8000003S1H".
split; [lia| apply IH; exact Hx].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma munch_filter_nonempty : forall W m m', munch W m m' -> munch (List.filter nonempty W) m m'.
Proof. intros W m m' MU. eapply munch_weaken; [apply sub_fp_filter_nonempty | exact MU]. Qed.
#[using="Type"] Lemma filter_cons_eq : forall {A} (f : A -> bool) x l, List.filter f (x :: l) = if f x then x :: List.filter f l else List.filter f l.
Proof. reflexivity. Qed.
#[using="Type"] Lemma disjoint_from_Forall : forall W A k,
Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W -> disjoint_from W A k.
Proof.
induction W as [|[lo hi] W IH]; intros A k HF; cbn; [exact I|].
inversion HF as [| x l H1 H2]; subst. cbn [fst snd] in H1. split; [exact H1| apply IH; exact H2].
Qed.
#[using="Type"] Lemma ext_clear : forall L W A k,
Forall (aext L) W -> 0 <= k ->
(A + k <= al_fake L \/ al_fake L + 11571200 <= A) ->
(A + k <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= A) ->
A + k <= ATOP ->
(A + k <= shad ATOP \/ shad (2^47) <= A) ->
disjoint_from (List.filter nonempty W) A k.
Proof.
intros L W A k EXT Hk D1 D2 D3 D4. apply disjoint_from_Forall.
induction W as [|[lo hi] W IH]; [constructor|].
inversion EXT as [| x l E1 E2]; subst.
rewrite filter_cons_eq. unfold nonempty at 1. cbn [fst snd].
destruct (Z.ltb_spec lo hi) as [LT|GE]; [| apply IH; exact E2].
constructor; [| apply IH; exact E2]. cbn [fst snd].
unfold aext in E1. cbn [fst snd] in E1. specialize (E1 LT).
clear IH E2 EXT. Local Ltac2 Set LiaHints.tbl := fun () => "0010>30294239397.1500000@S2D12D22D32D42E1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Ext.
Variable H : aholes.
Hypothesis HL : ahole_laws H.
#[using="HL"] Theorem AREP_frame_ext : forall L st X m m' W,
alayout_ok L -> AREP H L st X m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => fst iv < snd iv ->
(al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
\/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
\/ ATOP <= fst iv
\/ (shad ATOP <= fst iv /\ snd iv <= shad (2^47))) W ->
AREP H L st X m'.
Proof.
intros L st X m m' W ALO AR MU0 WM EXT.
change (Forall (aext L) W) in EXT.
pose proof (munch_filter_nonempty W m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty W) in *.
pose proof (ao_fake L ALO) as FK. Local Ltac2 Set LiaHints.tbl := fun () => "02^0>10317707088.1 10346402168.5 10348506307.8 11706929818.0 12231087258.0 12610434122.0 12877090629.1 14003831931.2 1470656533.33 14885359002.0 15643153306.0 15680996183.1 16063336730.0 16075959562.0 16449052682.0 16534157257.1 1685717371.0  17032418858.4017182596419.4 18106462146.4 18464651473.121891303130.0  19019216746.0 19062377098.1119326977656.2 22238414741.0 22380900506.0 22753993626.0 24990232882.1025096308066.5 25773232682.0 26238245128.0 26654231498.0 28977764826.0 29831068689.9 30155742554.0 30912897340.3 31536066761.1 31933984517.3 32832863258.9 32891160218.0 32917795153.6 34081784602.0 34521219823.7 3497739546.0  36449675461.1 36478104782.2 36782690527.2 36958550341.1 37765601928.0 37779520282.0 37938770577.1538436634709.0 38692635477.0 38907343899.9 38948636245.0 39012636437.0 39076636629.0 39124129930.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39332637397.0 39396637589.0 39412637669.0 39716638549.0 40171130513.2 41120432332.3 42411609006.0 43554307580.3 43556650069.0 43781106499.3 44161593864.0 44327776154.0 44771398743.1 45302567674.0 45348655445.0 4704857041.9  47648606362.0 48260400904.0 48420664661.0 48453490970.0 48506950362.0 48809933974.9 48873933567.5 48873933567.7 48880235586.7 48932666197.0 48989652933.1 49214230042.0 49316667349.0 49503560163.7 49503560163.9 49949808190.1149949814153.5 49949814153.8 50203955267.1 50212670037.0 50468670805.0 51209830554.0 51853062327.1652004675413.0 52489829152.4 52551278971.4 52644677333.0 52900678101.0 53028678485.0 53924681173.0 54436682709.0 54948684245.0 54949005805.1154953652027.5 55588686165.0 55844686933.0 55972687317.0 56074431045.0 56708689589.0 56740689621.0 57484626142.1157892693077.0 58084693653.0 58148693845.0 58322577050.0 58524927621.4 58532694997.0 588087689.1   58867622849.9 59044696533.0 59172696917.0 59236697109.0 59308586510.3 59364697493.0 59500554778.0 59556698069.0 59684698453.0 59757943557.1059757943557.5 59757943557.6 59812698837.0 60196699989.0 60260700181.0 60524831429.1 60545795320.8 60580701141.0 60644701333.0 60916702181.0 6094198434.1  61820339768.4 6292111160.3  63434872090.0 65445025434.0 65716050714.0 66048936517.1 66149329551.2666151427713.1866151427842.1666151427842.1766151427842.1866442924570.0 66578857626.0 66996096282.0 67469389506.1767693676357.0 67723395739.5 67762809634.1 68331430219.0 6859089733.7  7384966554.0  7457518318.6  8043637786.0  8126717385.1  9173904202.3  9323683354.0  00000100900F00G00H00I00J00K01201301401501601701801901:01a01i02102K02L02M02W02[02\02]02^02e02m02n02o03003103D03E03J03K03O03Y03Z03e03f04204304404804<04=04>04?04`04a04b05405505605705805905:05;05<05=05>05?05@05E05J05K05P05Q05U05V05W05X05Y05Z05m05n05o06006106206E06M06Y06i06j06k06l06m07507E07U07]07l07m07n07o08008108208908:08;08<08=08>08?08@08J08R08S08T08U08V08W08X08b08c08d08e08f08j08k08l09A09B09C09D09H09I09J09K09L09c09k0:F0:G0:H0:I0:J0:V0:W0:X0:Y0:Z0:b0:f0:g0:h0:i0:j0;B0;O0;\0;h0<40<50<60<70<c0<d0<l0<m0<n0=70=80=D0=E0=F0=K0=LSS3ORH2H1S2OT2H12H32OCSSSSSS3FK23FKI3ATR1H2H02H42H52H93H103H143H15SSFSSSSSS3ORS3ORH1H2H02H42H52H93H103H143H153H19S3RSP2HcS3RSP2HcS2OT5D_t_f3SF13SF23SAT1E1HSSS2Ha2E12E2S2QSSSSS2Ha2E1S2Q13RI1SSSSS3FKI3ATR3SF13SAT1ESS3POSSS2Q6S3ATR1H2H0SS2Q52Q63RI1SS2Q23RI23RI3SSS2HcS2QSSSSS3ORS3ORH7D_f_res3SF23SAT1E2B12B2SSS2Q12Q23RI23RI32P4SSSSSSSSSSSSS3FKSS3POSSS3RI1SS2HcSSFSSS3FKI3ATR3SF13SAT1ESSSSSS3FKI3ATR3SF13SAT1ES3ATR2H3S3ATR3SR32H3S3ORS2H32OT1H2OCSSSSS3SR32H3S3SF13SF23SF02H3S3ATR3SF13SF22HBS3SF12H3S3SHR3SR22H12H3SSSSSSS2Q52Q6SSSSSSSS2Ha2E12E2S3RI12P5SSSSSSS2Ha2E12E2SSSSS2HaSSS3RSP3CLB2Q12Q22P52P4SSSS2HkSSSSS3ATR3SR13SR33FKB2H12H3S3FKI2H3S7D_f_res2H12H35D_t_f5D_c_fSSSSS3ATR3SF42HBSSSSS3RSP2HcS2HcSSSSS2RM2AM1H2H02H42H92Q42Q7S3ORS1H2H02H4S3FK31H2H02H4S2RM1H2H02H4S2AL1H2H02H4SSSS3FKI3ATR2ON2OS5D_n_f5D_s_f3SF13SF23SAT2Ha1ESS2Q13RI1SSS3RI23RI3SS2Q63RI23RI3SSS3POSS".
pose proof (aobj_img _ _ FK ltac:(lia)) as FKI. unfold aobj in FK. destruct FK as (FK3 & FK1 & FK2 & FKS & _).
unfold sclr, KLS in FKS. unfold AIMG_HI in FKI. pose proof atop_range as ATR.
pose proof (fun A k => ext_clear L W A k EXT) as KX. cbn beta in KX. fold W' in KX.
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
pose proof (ao_res_hi L ALO) as ORH.
unfold aobj, sclr, KLS in OT, OC, ORS, ON, OS. pose proof (ao_space L ALO) as RSP.
pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_fake_res L ALO) as D_f_res.
pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
unfold adisj in D_t_f, D_c_f, D_f_res, D_n_f, D_s_f.
assert (SHF : 2147450880 + 781824 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= shad ATOP
/\ shad ATOP + 1048576 <= shad (2^47) /\ shad (2^47) = 17594333495296).
{ rewrite !shad_div, shlen_div. change (2^47) with 140737488355328. unfold ASHOFF in *. clear -FKI FK2 ATR. Z.div_mod_to_equations. lia. }
destruct SHF as (SF1 & SF2 & SF3 & SF4).
assert (SF0 : shlen 11571200 = 1446400) by (rewrite shlen_div; reflexivity).
assert (SAT : 0x10006fef8000 <= shad ATOP <= 0x10007fef8000) by (rewrite shad_div; unfold ASHOFF; clear -ATR; Z.div_mod_to_equations; lia).
assert (SHR : shad (al_res L) + shlen 137439023104 <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad (al_res L)).
{ destruct D_f_res as [D|D]; [right | left]; apply shad_sep; [exact D | clear -FK3 | exact D | clear -ORS]; Z.div_mod_to_equations; lia. }
assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
/\ shad (al_res L + 137439023104) <= shad ATOP).
{ rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS ORH. Z.div_mod_to_equations. lia. }
destruct SHRES as (SR1 & SR2 & SR3).
assert (FKB : al_fake L + 11571200 <= 2147450880 \/ 17594333495296 <= al_fake L) by (clear -FKS; lia).
assert (Kimg : forall A k, 0 <= A -> 0 <= k -> A + k <= AIMG_HI -> disjoint_from W' A k).
{ intros A k H1 H2 H3. unfold AIMG_HI in H3. apply KX; [exact H2| clear -H3 FKI; lia| clear -H3 SF1; lia| clear -H3 ATR; lia| clear -H3 SF0 SF1 SF2; lia]. }
assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k).
{ intros A k H1 H2 H3. apply KX; [exact H2| | clear -H1 H2 H3 SHR SR2; lia| clear -H3 SR3 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia| clear -H3 SR3; lia].
clear -H1 H3 SR1 SR3 FKB ATR. rewrite (shad_div ATOP) in *. unfold ASHOFF in *. lia. }
assert (Kobj : forall A k, 0 <= k -> A + k <= ATOP -> (A + k <= 2147450880 \/ 17594333495296 <= A) ->
(A + k <= al_fake L \/ al_fake L + 11571200 <= A) -> disjoint_from W' A k).
{ intros A k H2 H3 HB H4. apply KX; [exact H2| exact H4| clear -HB SF0 SF1 SF2 SF3 SF4 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia| exact H3| clear -HB H3 SF3 SF4 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia]. }
clear KX.
assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k).
{ intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 ORS; lia | clear -H1 ORH; lia | clear -H1 H3 D_f_res; lia]. }
assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W' A k).
{ intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OT; lia | clear -H1 H3 OT; lia | clear -H1 H3 D_t_f; lia]. }
assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k).
{ intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OC; lia | clear -H1 H3 OC; lia | clear -H1 H3 D_c_f; lia]. }
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
eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
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
pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E NE). change (2^47)%Z with 140737488355328%Z in E.
unfold AINSTANCE in *. change (shad 140737488355328) with 17594333495296%Z in E.
split; [clear -E OT D_t_f SF0 SF1 SF2 SAT; lia|].
split; [clear -E FKI SF1 SAT ATR; lia|].
split; [clear -E FKI SF1 SAT ATR; lia|].
split; [clear -E FKI SF1 SAT ATR; lia|].
intros b Hb. destruct (BB b Hb) as [B1 B2]. destruct (xb_st b); [exact I| |];
clear -E B1 B2 ORS ORH D_f_res SF0 SF2 SAT; lia.
- unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
split.
{ eapply (hs_frame _ HL L st st X X m m' W'); [exact HS | exact MU | exact WM | |].
- unfold sec_untouched, aknown. apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)). change (2^47)%Z with 140737488355328%Z in E.
atop_facts. clear -E Ha FK1 FK2.
destruct E as [[E1 E2]|[[E1 E2]|[E1|[E1 E2]]]].
+ do 10 right. left. lia.
+ do 2 right. left. rewrite shlen_div in E2. lia.
+ do 4 right. left. lia.
+ do 3 right. left. rewrite (shad_div 140737488355328) in E2. change (140737488355328 / 8)%Z with 17592186044416%Z in E2. unfold ASHOFF in E2. lia.
- apply sec_same_refl. }
split.
{ eapply (hd_frame _ HL L m m' W'); [exact HD | exact MU | exact WM |].
apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)). change (2^47)%Z with 140737488355328%Z in E.
change (shad 140737488355328) with 17594333495296%Z in E.
clear -E Ha FKI SF0 SF1 SF2 SAT ON OS D_n_f D_s_f ATR. lia. }
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
End Ext.
#[using="Type"] Lemma AHEAP_P_hb_fake : forall H L RNG st LB m p A n,
AHEAP_P H L RNG st LB m -> In (HB p A n) LB -> A + n <= al_fake L \/ al_fake L + 11571200 <= A.
Proof.
intros H L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
destruct AR as (WF & _). pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
2: { cbn [sec_wf1] in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7). destruct G7 as (_ & _ & _ & _ & _ & _ & CF & _).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>36782690527.2 44992127358.1451607632185.3863137523960.1100000400U00Y00fS2QSS3CLB3FIT2Q12Q22P52P41D3RSP2RG2RZS2G5S2G42G52CF2SF".
pose proof (sec_facts n ltac:(lia) G6) as SF. subst A. unfold SEC_UOFF. clear -G3 G4 G5 CF SF. lia. }
destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. destruct M as (N0 & FIT & _).
destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
{ apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
pose proof (ad_fake_res L ALO) as D. pose proof (ao_space L ALO) as RSP. unfold adisj in D.
pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
subst A n. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP D N0 FIT RG RZ. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma AREP_relro : forall H L st X m, AREP H L st X m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros H L st X m AR. destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _). exact HRO. Qed.
#[using="Type"] Lemma AHEAP_P_relro : forall H L RNG st LB m, AHEAP_P H L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros H L RNG st LB m (_ & _ & [X [AR _]] & _). exact (AREP_relro H L st X m AR). Qed.
#[using="Type"] Lemma AHEAP_P_hb_range : forall H L RNG st LB m p A n,
AHEAP_P H L RNG st LB m -> In (HB p A n) LB -> ablock_range A n.
Proof.
intros H L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
destruct AR as (WF & _). pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
2: { cbn [sec_wf1] in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
Local Ltac2 Set LiaHints.tbl := fun () => "00D0>15045117442.502431248216.11 29317564158.5029784466142.5034741471777.1136782690527.2 40825284078.5041415991886.5044134344200.1145355278736.5146282098069.1047870876220.2 51607632185.3852329333790.5055257122349.115819200041.13 63967151502.5066149329409.5366149329551.256755919038.50 00000100500600700800<00=00>00E00F00Y00]00a00b00l01I01J01W01k01lSS2G5SSSS2QSSSS2G42SFSS3CLB2P53RSP3ORH2RZS2N0S2G5SS2G32G42SFS3CLB3FIT2Q12Q22P43RSP3ORS2RGSS2G11H2H03H24S2AL4RZ161H2H02H42H9S".
pose proof (sec_facts n ltac:(lia) G6) as SF. subst A. unfold ablock_range, SEC_UOFF in *. clear -G1 G2 G3 G4 G5 SF.
split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. destruct M as (N0 & FIT & _).
destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
{ apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
pose proof (slot_aligned L (xb_class b) (xb_slot b) SAL CLB) as AL.
pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_res_hi L ALO) as ORH.
pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ. pose proof (rz_size_eq (xb_n b)) as RZE.
assert (RZ16 : rz_size (xb_n b) mod 16 = 0).
{ rewrite RZE. assert (0 <= rz_log (xb_n b)) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
replace (2 ^ rz_log (xb_n b)) with (2 ^ (rz_log (xb_n b) - 0)) by (f_equal; lia).
rewrite Z.mul_comm. apply Z_mod_mult. }
subst A n. unfold ablock_range, xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
split; [right; split; [clear -P5 RSP ORS ORH CLB RZ; lia| clear -P4 Q1 Q2 CLB RSP ORS FIT RG; lia]|]. split; [clear -N0; lia|].
split; [clear -P4 Q1 Q2 CLB RSP ORS FIT RG; lia|].
clear -AL RZ16. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
