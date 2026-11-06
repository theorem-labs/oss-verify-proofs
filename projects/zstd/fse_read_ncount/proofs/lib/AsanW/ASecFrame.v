(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase ARep ARepFrame ALayout AHeapP ASecFacts ASec ARepExt.
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
#[using="Type"] Lemma su_disjoint : forall L W A k,
sec_untouched L W -> Forall (fun iv => fst iv < snd iv) W -> 0 < k ->
(forall a, A <= a < A + k -> aknown L a -> False) ->
disjoint_from W A k.
Proof.
intros L W A k SU NE Hk CL. induction W as [|[lo hi] W IH]; cbn; [exact I|].
inversion SU as [|x l Hx Hl]; subst. inversion NE as [|x' l' Hn Hnl]; subst. split; [| apply IH; [exact Hl| exact Hnl]].
cbn [fst snd] in Hx, Hn.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>16805405549.1833362669339.1838630918765.1750965389882.1800000700>00B00FS2Hk2L1S2Hn2L2S2L1S2L2".
destruct (Z_lt_le_dec lo (A + k)) as [L1|L1]; [| left; lia].
destruct (Z_lt_le_dec A hi) as [L2|L2]; [| right; lia].
exfalso. apply (CL (Z.max A lo)); [lia|]. apply Hx. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sec_untouched_filter : forall L W, sec_untouched L W -> sec_untouched L (List.filter nonempty W).
Proof. intros L W SU. unfold sec_untouched in *. rewrite Forall_forall in SU |- *. intros iv Hin. apply SU. apply List.filter_In in Hin. tauto. Qed.
#[using="Type"] Lemma nonempty_filter : forall W, Forall (fun iv : Z * Z => fst iv < snd iv) (List.filter nonempty W).
Proof. intros W. rewrite Forall_forall. intros [lo hi] Hin. apply List.filter_In in Hin. destruct Hin as [_ NE]. unfold nonempty in NE. cbn [fst snd] in *. apply Z.ltb_lt. exact NE. Qed.
Section Geo.
Variable L : alayout.
Hypothesis ALO : alayout_ok L.
Local Ltac layout :=
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & _); pose proof (ao_space L ALO) as RSP; pose proof (ao_res_hi L ALO) as ORH;
pose proof (ao_t L ALO) as (_ & OT1 & OT2 & OTs & OTi);
let OC := fresh in pose proof (ao_ctx L ALO) as OC; pose proof (aobj_img _ _ OC ltac:(lia)) as OCI; destruct OC as (_ & OC1 & OC2 & OCs & _);
pose proof (ao_res L ALO) as (_ & OR1 & OR2 & _ & _);
let ON := fresh in pose proof (ao_nodes L ALO) as ON; pose proof (aobj_img _ _ ON ltac:(lia)) as ONI; destruct ON as (_ & ON1 & ON2 & ONs & _);
let OS := fresh in pose proof (ao_store L ALO) as OS; pose proof (aobj_img _ _ OS ltac:(lia)) as OSI; destruct OS as (_ & OS1 & OS2 & OSs & _);
let OFK := fresh in pose proof (ao_fake L ALO) as OFK; pose proof (aobj_img _ _ OFK ltac:(lia)) as OFI; destruct OFK as (OF0 & OF1 & OF2 & OFs & _);
pose proof (ao_dtls L ALO) as (_ & OD1 & OD2 & ODs & ODi);
let OP := fresh in pose proof (ao_ptr L ALO) as OP; pose proof (aobj_img _ _ OP ltac:(lia)) as OPI; destruct OP as (_ & OP1 & OP2 & OPs & _);
pose proof atop_range as ATR; pose proof ATOP_al16 as ATA;
unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in SP2, SP3; change (2^37) with 137438953472 in SP2;
unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *.
#[using="ALO"] Lemma clear_inst : forall a, AINSTANCE + 72 <= a < AINSTANCE + 728 -> aknown L a -> False.
Proof.
intros a Ha K. Local Ltac2 Set LiaHints.tbl := fun () => "0090>51852955146.1751855061554.2351855061554.2751855061554.3151855061554.4059308580059.2359308580059.2459310676310.3059310828256.1700000100200300400500O00^00j01PSSSSSS2Ha1K3SP11H2H03ATR3ATA2H4S2Ha1K3OF11H2H0S2Ha1K2H42H5S2Ha1K3ORH3OTi3OCI3ONI3OSI3OFI3ODi3ATR".
layout.
unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE in *. rewrite !shad_div in K. unfold ASHOFF in K.
destruct K as [K|[K|[K|[K|K]]]].
- clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha OF1 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Ha OTi OCI OR1 ORH ONI OSI OFI ODi ATR ATA SP1 SP2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ALO"] Lemma clear_ptr : forall a, al_ptr_array L <= a < al_ptr_array L + 8388608 -> aknown L a -> False.
Proof.
intros a Ha K. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>51852955146.1751855061554.2351855061554.2751855061554.3151855061554.4059308579414.1759308580059.2559308580059.2659308842074.1859310676310.3200000100200300400500P00j01E02002ISSSSSS2Ha1K3SP13SP23OPs3ATR1H2H0S2Ha1K3OPs3ATR3ATA1H2H02H4S2Ha1K3OF13OF23OPs3ATR1H2H0S2Ha1K3SP23RSP3OP23ATR2X12X22X32X42X52X62X7S2Ha1K3OPs3OPI1H2H02H42H5".
layout.
pose proof (ad_t_ptr L ALO) as X1. pose proof (ad_ctx_ptr L ALO) as X2. pose proof (ad_ptr_res L ALO) as X3. pose proof (ad_nodes_ptr L ALO) as X4.
pose proof (ad_store_ptr L ALO) as X5. pose proof (ad_fake_ptr L ALO) as X6. pose proof (ad_dtls_ptr L ALO) as X7.
unfold adisj, aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in K. unfold ASHOFF in K.
destruct K as [K|[K|[K|[K|K]]]].
- clear -K Ha OPI OPs SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha SP1 OPs OP2 ATR SP2. Z.div_mod_to_equations. lia.
-
clear -K Ha OF1 OF2 OPs ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Ha OPs OP2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Ha OP2 X1 X2 X3 X4 X5 X6 X7 RSP SP1 SP2 ATR ATA. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ALO"] Lemma clear_chunk : forall mb ms n a, sec_wf1 L (CSec mb ms n) -> mb <= a < mb + ms -> aknown L a -> False.
Proof.
intros mb ms n a WF1 Ha K. cbn [sec_wf1] in WF1. destruct WF1 as (G1 & G2 & G3 & G4 & G5 & G6 & (Qt & Qc & Qr & Qp & Qn & Qs & Qf & Qd)).
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>51852955146.3451855061554.4051855061554.4451855061554.4851855061554.5759308579414.1959308580059.2759308580059.2959310676310.3359310828256.2000000100200300400500O00h01B01V02@SSSSSS2G22Ha1K3SP13SP23ATR1H2H0S2G22Ha1K3ATR3ATA1H2H02H4S2G22Ha1K3OF13OF23ATR1H2H0S2G22Ha1K1H2H02H42H5S2G32Qt2Qc2Qr2Qn2Qs2Qf2Qd2Ha1K3SP23RSP3ATR".
layout. unfold ablk in G2.
unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in K. unfold ASHOFF in K.
destruct K as [K|[K|[K|[K|K]]]].
- clear -K Ha G2 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha SP1 G2 G3 ATR SP2. Z.div_mod_to_equations. lia.
- clear -K Ha OF1 OF2 G2 G3 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Ha G2 G3 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Ha G3 Qt Qc Qr Qn Qs Qf Qd RSP SP1 SP2 ATR ATA. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ALO"] Lemma clear_chunk_shadow : forall mb ms n a, sec_wf1 L (CSec mb ms n) -> shad mb <= a < shad mb + ms / 8 -> aknown L a -> False.
Proof.
intros mb ms n a WF1 Ha K. cbn [sec_wf1] in WF1. destruct WF1 as (G1 & G2 & G3 & G4 & G5 & G6 & (Qt & Qc & Qr & Qp & Qn & Qs & Qf & Qd)).
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>51613910273.2451852955146.3651855061554.4251855061554.4651855061554.5051855061554.5959308580059.4359310676315.4359310676438.4959310676438.5159310676438.5566151427842.1600000400500600700800901201V02902]03M03]S2G5SSSSSS2G22G32Ha1K3ORH3OTs3OCs3ONs3OSs3OFs3ODs3ATR3MB83MS81H2H4S2G32Ha1K3ATA3MB83MS81H2H02H42H93H14S2G22Ha1K1H2H02H42H52H93H103H143H15S2Qf2Ha1K3OF03MB83MS81H2H02H42H93H19S2Qr2Ha1K3MSB3SP33RSP3ORH3MB83MS81H2H02H42H93H19S2G11H2H02H43MSM".
pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & MSM & MSB). rewrite <- G4 in MSM, MSB.
layout. unfold ablk in G2.
assert (MB8 : mb mod 8 = 0) by (clear -G1; Z.div_mod_to_equations; lia).
assert (MS8 : ms mod 8 = 0) by (clear -MSM; Z.div_mod_to_equations; lia).
unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. rewrite !shad_div in K. rewrite !shad_div in Ha. unfold ASHOFF in K, Ha.
destruct K as [K|[K|[K|[K|K]]]].
-
clear -K Ha G2 G3 MSB ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
-
clear -K Ha MB8 MS8 MSB Qr RSP SP3 OR1 ORH G2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Ha MB8 MS8 MSB Qf OF0 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha MB8 MS8 MSB G3 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
-
clear -K Ha G2 G3 MSB MB8 MS8 ATR OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 SP1 SP2. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ALO"] Lemma clear_prim0 : forall a, shad (al_space_beg L) <= a < shad (al_space_beg L) + shlen K_REGION -> aknown L a -> False.
Proof.
intros a Ha K. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>51852955146.1751855061554.2351855061554.2751855061554.3151855061554.4059310676310.3059310676310.4459310676315.3759310676438.4459310676443.5700000100200300400500A01:01^02402dSSSSSS2Ha1K2H42H5S2Ha1K3SP13SP23ORH3OTs3OCs3ONs3OSs3OFs3ODs3ATR1H2H02H42H5S2Ha1K3SP23ATA1H2H02H42H52H93H103H14S2Ha1K3SP11H2H02H93H10S2Ha1K3SP33RSP3OF03DFR1H2H02H42H52H93H103H193H24".
layout. pose proof (ad_fake_res L ALO) as DFR.
unfold adisj, aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_REGION in *. change (2^32) with 4294967296 in Ha.
rewrite !shad_div, shlen_div in Ha. rewrite !shad_div in K. unfold ASHOFF in K, Ha.
destruct K as [K|[K|[K|[K|K]]]].
- clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha DFR RSP OF0 SP3 OR1 ORH SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha SP2 SP1 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Ha SP1 SP2 OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 ATR ATA. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ALO"] Lemma clear_free_shadow : forall x,
(AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
aknown L (shad x) -> False.
Proof.
intros x Hx HF K. unfold astartup_hulls in HF.
repeat (apply Forall_cons_iff in HF; destruct HF as [?H HF]). cbn [fst snd] in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>51850858376.3751850858376.4151850858376.4551850858376.5451850858383.3159308580059.3759310676310.3059310676312.3959310676312.4259310676315.3700000100200300400500`01<01U02602NSSSSSS2Hx1K3ORH3OTs3OCs3ONs3OSs3OFs3ODs3ATR1H2H0S2Hx1K3ATR3ATA1H2H02H42H52H9S2H31K3OF01H2H02H52H63H15S2H81K3SP33RSP3ORH1H2H02H42H53H15S2Hx1K1H2H02H42H52H93H10".
layout. unfold K_HIGH_MEM in Hx.
unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. rewrite !shad_div in K. unfold ASHOFF in K.
destruct K as [K|[K|[K|[K|K]]]].
- clear -K Hx ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Hx H8 RSP SP3 OR1 ORH ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Hx H3 OF0 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
- clear -K Hx ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
- clear -K Hx OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Geo.
Section Frame.
Variables (L : alayout) (W0 : list (Z * Z)) (m m' : amem).
Hypothesis MU0 : munch W0 m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis SU0 : sec_untouched L W0.
Let W := List.filter nonempty W0.
Let MU : munch W m m' := munch_filter_nonempty W0 m m' MU0.
Let SU : sec_untouched L W := sec_untouched_filter L W0 SU0.
Let NE : Forall (fun iv => fst iv < snd iv) W := nonempty_filter W0.
Section WithLayout.
Hypothesis ALO : alayout_ok L.
#[using="rc L SU0 SU NE ALO"] Lemma D_inst : forall A k, AINSTANCE + 72 <= A -> A + k <= AINSTANCE + 728 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_inst L ALO). Local Ltac2 Set LiaHints.tbl := fun () => "0010>35408005380.2000000:S2H12H22Ha".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc SU0 SU NE ALO"] Lemma D_ptr : forall A k, al_ptr_array L <= A -> A + k <= al_ptr_array L + 8388608 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_ptr L ALO). Local Ltac2 Set LiaHints.tbl := fun () => "0010>57482534197.2000000:S2H12H22Ha".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SU0 SU NE ALO"] Lemma D_chunk : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k.
Proof. intros mb ms n A k WF1 H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56207311688.2400000:S2H12H22Ha".
apply (clear_chunk L ALO mb ms n); [exact WF1| lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SU0 SU NE ALO"] Lemma D_shadow : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k.
Proof. intros mb ms n A k WF1 H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59956046619.2400000:S2H12H22Ha".
apply (clear_chunk_shadow L ALO mb ms n); [exact WF1| lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="W0 MU0 WM SU0 W MU SU NE ALO"] Lemma asec_chunk_frame : forall mb ms n idx lv,
sec_wf1 L (CSec mb ms n) -> asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
intros mb ms n idx lv WF1 CH. pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00I0>11624291152.8 15653492877.8 1785468914.7  18107032235.4 21842504200.8 22014303259.8 22096821547.5 24963147917.6 28989849047.5 29293361451.7 33671246594.7 34438769839.8 34737325243.8 35864023691.6 39170548780.9 40397452967.6 41213433359.514650438331.8  48175602055.6 51613910273.2752392744836.8 59335169898.8 66028962729.8 6644414584.5  66500705481.5 00000@00P00`00a00b01201;01<01A01B01C01S01T01U01^01c02\02]02b02f02g02h03803=03>S2G53RSR3NSE3MSRS2G53RSR3NSE3MSRS2G53RSR3NSE3MSRSSS2G53RSR3NSE3MSRS3GR13GR3SS3POSSSS2G53RSR3NSE3MSRSSS2G51H2H0S3GR1S2G12G53RSR3NSE3MSR3MSM1H2H02H42H52H93H103H143H153H193H24SS3GR3S2G5SSS2G53RSR3NSE3MSRS3GRPS".
pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
{ unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
destruct GR as (GR1 & GR2 & GR3).
cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
unfold SEC_UOFF in *.
split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
eapply cells_frame; [exact H5| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]. }
split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1; lia]|].
assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1 GRP; lia]|].
eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1 POS; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithLayout.
#[using="W0 MU0 WM SU0 W MU SU NE"] Theorem asec_frame : forall st st' X X',
ASEC_of L st X m -> sec_same st st' -> ASEC_of L st' X' m'.
Proof.
intros st st' X X' (WFS & ARR & INST & PZ & SHZ) (EN & ER & EP & EL & PERM).
unfold ASEC_of, ASECc.
pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
assert (ALLSEC : forall ch, In ch (sec_chunks_of st) -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
{ intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
exists mb, ms, n. split; [reflexivity| exact W1]. }
split; [| split; [| split; [| split]]].
-
unfold asec_wf. rewrite EP, ER, EN. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [| split; [exact WB| split]].
+ rewrite (Permutation_length PERM). exact WL.
+ rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [exact PERM| exact Hin].
+ eapply sec_disjoint_perm; [apply Permutation_sym; exact PERM| exact WD].
-
destruct ARR as (order & PO & U64 & JK & PER). exists order.
assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PERM]|].
split; [| split].
+ destruct order as [|o0 order'].
* destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. Local Ltac2 Set LiaHints.tbl := fun () => "00M0>10313511634.6 11787385189.4016240810784.4017320376170.4017943859483.4018697145376.4020740072765.4323019067284.5 2413154794.40 28233644939.4 30298271984.4033660695317.4035419219100.3 3626455729.5  39220637093.0 44006662939.4045375072234.4047845853802.4049861985765.4057865613797.4057926322917.5 59936118426.4061116987935.1161590143977.6 64711478890.4065253966880.1 65510701083.4068050567342.4068692504503.4300000500600700800900:00=00B00C00H00I00J00N00R00S00T00U00V00W00X00\00]00j01501601701801901<S3LENSSSSSS1HS3LENSS3POSSSS2HaS2WBSSSSSSS2WRSS2Hx3ATR1H2H0S2WR2WB3LENSSSSS1H".
split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
* eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply (D_ptr ALO); cbn [length] in LEN |- *; clear -LEN WB WR; lia.
+ rewrite EN, ER. eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply (D_ptr ALO); clear -POS WB WR; lia.
+ intros i ch Hi. destruct (PER i ch Hi) as (lv & LV & CH).
assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
destruct (ALLSEC ch Hin) as (mb & ms & n & -> & W1).
exists lv. split; [| eapply asec_chunk_frame; [exact ALO| exact W1| exact CH]].
rewrite LV. unfold sec_live. split; intros [p Hp]; exists p; [apply (proj2 (EL p mb ms n)); exact Hp| apply (proj1 (EL p mb ms n)); exact Hp].
-
destruct INST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia]|].
split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia]|].
split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
eapply junk_frame; [exact I6| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia].
-
unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
apply (su_disjoint L); [exact SU| exact NE| exact POS|]. intros a Ha. apply (clear_prim0 L ALO). exact Ha.
-
intros x Hx HF HC.
assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; pose proof atop_range as ATR; clear -Hx ATR; Z.div_mod_to_equations; lia).
assert (HC0 : Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) (sec_chunks_of st)).
{ rewrite Forall_forall in HC |- *. intros ch Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]. }
rewrite <- (SHZ x Hx HF HC0). apply MU. rewrite wa_unsigned by exact SX.
eapply (disjoint_outside W (shad x) 1); [| clear; lia].
apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Frame.
#[using="Type"] Theorem asec_hs_frame : forall L st st' X X' m m' W,
ASEC_of L st X m -> munch W m m' -> wmono asegs m m' -> sec_untouched L W -> sec_same st st' -> ASEC_of L st' X' m'.
Proof. intros L st st' X X' m m' W HS MU WM SU SS. eapply (asec_frame L W m m' MU WM SU); [exact HS| exact SS]. Qed.
End CANSEC1.
