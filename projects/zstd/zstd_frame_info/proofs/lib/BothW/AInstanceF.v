(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase ABytes ACanary ARep ARepKit ARepFrame ALayout AHeapP ARepExt
     AMalloc_iface ADepot_iface APoisonR_iface AQConst ARepQ ARepQP ASec ASecFacts ASecFrame ASecStore FsKit
     F_adepot AFake_iface AFake_arep AInstance AFreeGeo AFreeRead ADriver_iface F_afree_arep AFreeNull F_apoison_remap AMalloc AInstanceM.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition aci_clear (A k : Z) : Prop := Forall (fun iv => A + k <= fst iv \/ snd iv <= A) aci_I.
End CANSEC1.
Ltac aci_clear_tac := unfold aci_clear, aci_I, drv_img_ranges, cli_img_ranges, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI, AIMG_HI;
  repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

Section CANSEC2. Context {rc : runConstT}.
Lemma achunk_eq_dec' : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* [comment removed for export] *)
#[using="Type"] Lemma junk_any : forall m m' A n, junk_at m A n -> wmono bsegs m m' -> 0x5f6000 <= A -> junk_at m' A n.
Proof. intros m m' A n H WM HA. exact (dc_at_any m m' A n H WM HA). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aobj_sub_sclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> sclr A k.
Proof. intros a n A k (_ & _ & _ & HS & _) H1 H2. unfold sclr in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=43703479539.800000:S2HS2H12H2".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma aobj_sub_iclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> iclr A k.
Proof. intros a n A k (_ & HG & _ & _ & HI) H1 H2. unfold iclr in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=64849419538.900000:S2HI2H12H2".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section ClientW.
Variables (L : alayout) (st : astate) (X : aconc) (LB : list ablock) (m m' : amem) (W : list (Z * Z)).
Hypothesis ALO : alayout_ok L.
Hypothesis AR : AREP AHI L st X m.
Hypothesis BL : ablocks L st X LB.
Hypothesis HFK : AFAKE L LB m.
Hypothesis MU0 : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis CW : Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W.
Let W' := List.filter nonempty W.
Let MU : munch W' m m' := munch_filter_nonempty W m m' MU0.

(* [comment removed for export] *)
#[using="X m ALO AR BL"] Lemma hb_where : forall p B n, In (HB p B n) LB ->
  (exists c, 1 <= c < K_NUM_CLASSES /\ aregion L c <= B /\ B + n <= aregion L c + c_allocated_user (get_cls st c)
             /\ c_allocated_user (get_cls st c) <= K_FREEARR_OFF /\ 1 <= n)
  \/ (exists mb ms, B = mb + 6144 /\ 1 <= n /\ n + 6144 <= ms /\ sec_wf1 L (CSec mb ms n)).
Proof.
  intros p B n Hin.
  destruct (hb_cases L st X LB m p B n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - left. exists (xb_class b). destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). destruct (PERC _ CLB) as (A1 & A2 & _).
    pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user in *.
    split; [exact CLB|]. Local Ltac2 Set LiaHints.tbl := fun () => "0070=10207120786.510916645978.229971573467.239170297337.451607648958.264980214825.467373203911.600000=00A00E00L00P00W00bS3RSR3NSE3MSRS2NBS2G5S2A12A2S2G5S2P52RZS3FIT2P42RG".
split; [clear -P5 RZ; lia|]. split; [clear -P4 FIT RG; lia|]. split; [unfold K_FREEARR_OFF in *; clear -A1 A2; lia| clear -NB; lia].
  - right. exists mb, ms. pose proof G as G0. cbn [sec_wf1] in G0. destruct G0 as (_ & _ & _ & G4 & G5 & G6 & _).
    pose proof (sec_facts n ltac:(clear -G5; lia) G6) as (_ & _ & _ & RSR & _ & NSE & _ & MSR & _). rewrite <- G4 in MSR.
    split; [exact EA|]. split; [clear -G5; lia|]. split; [clear -RSR NSE MSR; lia| exact G].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc L st X LB m ALO AR BL HFK CW"] Lemma P_img : forall A k, 0 <= k -> A + k <= 0x5f6000 -> aci_clear A k -> disjoint_from W' A k.
Proof.
  intros A k Hk HA CLR. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. Local Ltac2 Set LiaHints.tbl := fun () => "0070>50850525385.0 54652817777.1054658902853.9 54659099977.1154659099977.1454659099977.1654659099977.9 00000100;00D00M00W00i012SS2HA2I12I0S2I12I21DS2HA2K11HS2HA2B12G2S2HA2F14OFKI2K52B1S2HA2K51H".
pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.   (* [comment removed for export] *)
  pose proof (ao_stack L ALO) as (_ & _ & _ & SB). unfold aobj in *.
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 SB NEV HA. lia.
  - pose proof (proj1 (Forall_forall _ _) CLR iv Hiv) as D. cbn beta in D. clear -D I1 I2 NEV. lia.
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & _). clear -K5 F1 F2 OFK OFKI HA NEV. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (alayout_space L ALO) as (SP1 & _). unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Q1 B1 B2 NEV HA SP1 Hc. nia.
      * cbn [sec_wf1] in Q3. destruct Q3 as (_ & G2 & _). apply ablk_lin in G2. unfold AIMG_HI in G2. clear -G2 B1 B2 NEV HA. lia.   (* [comment removed for export] *)
    + destruct (afake_lb L LB m cls B n' HFK Hb) as (_ & _ & _ & _ & K5 & _). clear -K5 B1 B2 OFK OFKI HA NEV. lia.
  - clear -K5 NEV HA. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 _]. unfold ASHOFF in *. clear -I0 I1 I2 NEV HA. lia.
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & _). unfold ASHOFF in *. clear -K5 F1 F2 OFK OFKI HA NEV. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="m ALO HFK CW"] Lemma P_obj : forall A k, sclr A k -> iclr A k -> 0 <= k -> A + k <= ATOP ->
  (A + k <= al_fake L \/ al_fake L + 11571200 <= A) ->
  (forall p B n, In (HB p B n) LB -> A + k <= B \/ B + n <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k HS HI Hk HC HF HB. unfold sclr, KLS in HS. unfold iclr, AIMG_LO, AIMG_HI in HI. destruct HI as [HA HI].
  subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. Local Ltac2 Set LiaHints.tbl := fun () => "0080>50850525385.0 54652785271.1454652818420.1154652818420.1254658902853.1154659099977.1054659099977.1954659099977.9 00000100G00W00g01001901Z01aSS2HF2F12F22K52K62B12B2S2HI2I12I22I02I3S2HS2I12I22I02I3S2B12B21DS2HS2K51HS2HS2F12F24OFKI2K52K64OFK34OFKS1HS2HC2K1".
pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
  pose proof (ao_stack L ALO) as (_ & _ & S47 & SB). unfold aobj in *.
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 NEV HC. lia.
  - pose proof (proj1 (Forall_forall _ _) aci_ok iv Hiv) as (I0 & _ & I3). unfold AIMG_HI in I3. clear -I0 I1 I2 I3 NEV HI. lia.
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & K6 & _). unfold FAKESZ in K6. clear -K5 K6 F1 F2 HF NEV Hk. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + pose proof (HB q B n' Hb) as D. clear -D B1 B2 NEV Hk. lia.
    + destruct (afake_lb L LB m cls B n' HFK Hb) as (_ & _ & _ & _ & K5 & K6 & _). unfold FAKESZ in K6. clear -K5 K6 B1 B2 HF NEV Hk. lia.
  - clear -K5 NEV HS Hk. lia.
  - pose proof (proj1 (Forall_forall _ _) aci_ok iv Hiv) as (I0 & _ & I3). unfold AIMG_HI, ASHOFF in *. clear -I0 I1 I2 I3 NEV HS Hk. lia.
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & K6 & _). pose proof OFK as (_ & _ & OFK3 & OFKS & _). unfold sclr, KLS in OFKS.
    unfold FAKESZ, ASHOFF in *. clear -K5 K6 F1 F2 OFK3 OFKS OFKI NEV HS Hk. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="st X LB m ALO AR BL HFK CW"] Lemma P_sh : forall A k, 2148232192 <= A -> 0 <= k -> A + k <= shad ATOP ->
  (A + k <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k HA Hk HC HF.
  assert (HC2 : A + k <= 17594332446720 /\ 8 * (A + k) <= ATOP + 8 * ASHOFF).
  { rewrite shad_div in HC. pose proof ATOP_al16 as A16. unfold ASHOFF in *. clear -HC A16. Local Ltac2 Set LiaHints.tbl := fun () => "0090>12559806498.3 2283971744.5  50850525385.0 54652785271.1654652818420.1054652818420.1154659099977.1654659099977.1854659099977.9 00000500=00>00V00`00j01@01e022S3OFKS2HC3A16SS2HF2F12F23SF13SF22K52K6S2HA2I22I3S2HA2I22I3S2HA3HC22B22B12Q22G21HS2HA3HC22F12F23OFK4OFKS2K52K61H2B12B2S3HC22K11H2K5".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  clear HC. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
  pose proof OFK as (_ & _ & _ & OFKS & _). unfold sclr, KLS in OFKS.
  pose proof (ao_stack L ALO) as (_ & _ & S47 & SB). unfold aobj in *.
  assert (SF : shad (al_fake L) = al_fake L / 8 + ASHOFF /\ shad (al_fake L + 11571200) = al_fake L / 8 + 1446400 + ASHOFF).
  { rewrite !shad_div. clear -OFK. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SF as [SF1 SF2]. unfold ASHOFF in *.
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 NEV HC2. lia.
  - destruct (aci_ok1 iv Hiv) as [_ I3]. unfold AIMG_HI in I3. clear -I1 I2 I3 NEV HA. lia.
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & K6 & _). unfold FAKESZ in K6. clear -K5 K6 F1 F2 OFK OFKS NEV HC2 HA. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (alayout_space L ALO) as (SP1 & _). unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Q1 B1 B2 NEV HC2 SP1 Hc. nia.
      * cbn [sec_wf1] in Q3. destruct Q3 as (_ & G2 & _). unfold ablk, KLS, AIMG_HI in G2. clear -G2 Q2 B1 B2 NEV HC2 HA. lia.   (* [comment removed for export] *)
    + destruct (afake_lb L LB m cls B n' HFK Hb) as (_ & _ & _ & _ & K5 & K6 & _). unfold FAKESZ in K6. clear -K5 K6 B1 B2 OFK OFKS HC2 HA NEV. lia.
  - clear -K5 NEV HC2. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 I3]. unfold AIMG_HI in *. clear -I0 I1 I2 I3 NEV HA. lia.
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & K6 & _). unfold FAKESZ in K6. clear -K5 K6 F1 F2 SF1 SF2 HF NEV Hk. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc X m AR"] Lemma hb_prim_span : forall p B n c,
  In (HB p B n) LB -> 1 <= c < K_NUM_CLASSES -> aregion L c <= B -> B + n <= aregion L c + c_allocated_user (get_cls st c) ->
  al_space_beg L + K_REGION <= B /\ B + n <= al_space_beg L + K_SPACE_SIZE /\ B + n <= aregion L c + K_FREEARR_OFF.
Proof.
  intros p B n c Hin Hc Q1 Q2. destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). destruct (PERC c Hc) as (A1 & A2 & _).
  unfold aregion, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. change (2^37) with 137438953472. clear -Hc Q1 Q2 A1 A2. nia.
Qed.

(* [comment removed for export] *)
#[using="rc st X m ALO AR BL"] Lemma hb_clear_obj : forall A k,
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_space_beg L + K_SPACE_SIZE <= A /\ A + k <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA)
   \/ (al_res L <= A /\ A + k <= al_space_beg L + K_REGION)) ->
  forall p B n, In (HB p B n) LB -> A + k <= B \/ B + n <= A.
Proof.
  intros A k HR p B n Hin.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res.
  pose proof (ad_store_res L ALO) as D_s_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  unfold adisj, aobj in *.
  destruct (hb_where p B n Hin) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - pose proof (hb_prim_span p B n c Hin Hc Q1 Q2) as (S1 & S2 & S3).
    unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    clear -HR S1 S2 D_t_res D_c_res D_n_res D_s_res D_p_res RSP ORS. Local Ltac2 Set LiaHints.tbl := fun () => "0020>19457650551.1837541430130.1700000Q01KS2HR3RSP3ORS2Q22Ct2Cc2Cr2Cp2Cn2CsS2HR7D_t_res7D_c_res7D_n_res7D_s_res7D_p_res3RSP3ORS2S12S2".
lia.
  - cbn [sec_wf1] in Q3. destruct Q3 as (_ & _ & _ & _ & _ & _ & (Ct & Cc & Cr & Cp & Cn & Cs & _)).
    unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    clear -HR Ct Cc Cr Cp Cn Cs RSP ORS Q2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc ALO"] Lemma hb_clear_fake_obj : forall A k,
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_res L <= A /\ A + k <= al_res L + 137439023104)) ->
  A + k <= al_fake L \/ al_fake L + 11571200 <= A.
Proof.
  intros A k HR.
  pose proof (ad_t_fake L ALO) as D1. pose proof (ad_ctx_fake L ALO) as D2. pose proof (ad_nodes_fake L ALO) as D3.
  pose proof (ad_store_fake L ALO) as D4. pose proof (ad_fake_ptr L ALO) as D5. pose proof (ad_fake_res L ALO) as D6. unfold adisj in *.
  clear -HR D1 D2 D3 D4 D5 D6. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59758008966.1000000FS2HR2D12D22D32D42D52D6".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc st X LB m ALO AR BL HFK CW"] Lemma P_rt : forall A k, 0 <= k ->
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_space_beg L + K_SPACE_SIZE <= A /\ A + k <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA)
   \/ (al_res L <= A /\ A + k <= al_space_beg L + K_REGION)) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk HR.
  pose proof (ao_space L ALO) as RSP.
  (* [comment removed for export] *)
  assert (SUB : exists a n, aobj a n /\ a <= A /\ A + k <= a + n).
  { unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION in HR. change (2^37) with 137438953472 in HR.
    Local Ltac2 Set LiaHints.tbl := fun () => "0030=35989341342.539607437916.548880235586.800000700?00FS1H3RSPS2HR3RSPS2S22O3".
destruct HR as [H|[H|[H|[H|[H|[H|H]]]]]];
      [ exists (al_t L), 4096 | exists (al_ctx L), 65536 | exists (al_nodes L), 1048576 | exists (al_store L), 8388608
      | exists (al_ptr_array L), 8388608 | exists (al_res L), 137439023104 | exists (al_res L), 137439023104 ];
      (split; [first [exact (ao_t L ALO) | exact (ao_ctx L ALO) | exact (ao_nodes L ALO) | exact (ao_store L ALO) | exact (ao_ptr L ALO) | exact (ao_res L ALO)] |]);
      clear -H RSP; lia. }
  destruct SUB as (a & n & OA & S1 & S2).
  apply P_obj; [exact (aobj_sub_sclr a n A k OA S1 S2) | exact (aobj_sub_iclr a n A k OA S1 S2) | exact Hk | | |].
  - pose proof OA as (_ & _ & O3 & _). clear -O3 S2. lia.
  - apply hb_clear_fake_obj. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION in HR. change (2^37) with 137438953472 in HR. clear -HR RSP. lia.
  - exact (hb_clear_obj A k HR).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc X LB m ALO AR BL HFK CW"] Lemma P_reg_hi : forall c A k, 1 <= c < K_NUM_CLASSES -> 0 <= k ->
  aregion L c + c_allocated_user (get_cls st c) <= A -> A + k <= aregion L c + K_REGION -> disjoint_from W' A k.
Proof.
  intros c A k Hc Hk H1 H2.
  pose proof (ao_res L ALO) as ORS. pose proof (ao_space L ALO) as RSP. unfold aobj in *.
  destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). destruct (PERC c Hc) as (A1 & A2 & _).
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104).
  { unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Hc RSP. nia. }
  destruct RI as [RI1 RI2]. unfold K_REGION in *. pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0080>19455734285.1537543394888.9 39607436670.1046907966564.9 48880235586.9 52188409247.4 6004629830.8  61527815965.1200000H00O00a00k01701>01M01]S2H12H22A13RI13RI22Q22CrS2H12Q2S2H12H22A13RI13RI2S2H22Q12RSS2H23ORS3RI2S2NE2GES2H12A13RI13RHIS2H12A12Q22Q32RS".
apply P_obj; [unfold sclr; right; clear -H1 RI1 RHI A1; lia| unfold iclr, AIMG_HI; split; [clear -H1 RI1 RHI A1; lia| right; clear -H1 RI1 RHI A1; lia]
               | exact Hk| atop_facts; clear -H2 RI2 ORS; lia| apply hb_clear_fake_obj; clear -H1 H2 RI1 RI2 A1; lia|].
  intros p B n Hin. destruct (hb_where p B n Hin) as [(c' & Hc' & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - destruct (Z.eq_dec c' c) as [->|NE]; [clear -Q2 H1; lia|].
    destruct (Z.lt_ge_cases c' c) as [LT|GE].
    + right. pose proof (regions_sep L c' c LT) as RS. unfold K_REGION, K_FREEARR_OFF in *. clear -RS Q2 Q3 H1 A1. lia.
    + left. pose proof (regions_sep L c c' ltac:(clear -GE NE; lia)) as RS. unfold K_REGION in *. clear -RS Q1 H2. lia.
  - cbn [sec_wf1] in Q3. destruct Q3 as (_ & _ & _ & _ & _ & _ & (_ & _ & Cr & _)). clear -Cr RI1 RI2 H1 H2 Q2 A1. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc m ALO AR BL"] Lemma slot_vs_blocks : forall c k p B n, 1 <= c < K_NUM_CLASSES -> 0 <= k < ndist st c -> In (HB p B n) LB ->
  (exists b, busy_of X c k = Some b /\ xb_st b = BLive p /\ B = xb_user L b /\ n = xb_n b)
  \/ (B + n <= aslot_addr L c k \/ aslot_addr L c k + size_of_class c <= B).
Proof.
  intros c k p B n Hc Hk Hin.
  pose proof AR as (WF & _). pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  pose proof (size_of_class_facts c Hc) as [QS _]. destruct (PERC c Hc) as (A1 & A2 & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "0090>10403830041.8 19326977656.2 32432421927.1736176004835.1347870829326.3 51607648958.2 51794599906.4 895072720.11  9210411702.4  00000>00B00a01:01>01B01F01Y01`S3FIT2SD2RZ2RGS2QSS2A12A22P52P42Cr3RSR3NSE3MSR2RIS2P53FIT2Q42RG3B1'3B2'2RSS2KBS2G5S2HkS2A12A22P42Q52RZ2RSS2NC2GE".
pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 A1) Hk) as (P5 & P4 & P0).
  destruct (hb_cases L st X LB m p B n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & Q5 & Q4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    + destruct (Z.eq_dec (xb_slot b) k) as [EK|NK].
      * left. exists b. rewrite <- EC, <- EK. split; [exact (busy_of_of_In L st X b WF Hb)|]. split; [exact Sb|]. split; [symmetry; exact Ub| symmetry; exact Nb].
      * right. pose proof (slots_disjoint L c (xb_slot b) k ltac:(clear -KB; lia) ltac:(clear -Hk; lia) NK ltac:(clear -QS; lia)) as SD.
        pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user, xb_alloc in *. rewrite EC in *.
        clear -SD FIT RG RZ. lia.
    + right. pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user, xb_alloc in *.
      destruct (PERC (xb_class b) CLB) as (B1' & B2' & _). unfold K_FREEARR_OFF in *.
      destruct (Z.lt_ge_cases (xb_class b) c) as [LT|GE].
      * left. pose proof (regions_sep L (xb_class b) c LT) as RS. unfold K_REGION in RS. clear -RS Q4 P5 FIT RG RZ B1' B2'. lia.
      * right. pose proof (regions_sep L c (xb_class b) ltac:(clear -GE NC; lia)) as RS. unfold K_REGION in RS. clear -RS Q5 P4 A1 A2 RZ. lia.
  - right. cbn [sec_wf1] in G. destruct G as (_ & _ & _ & G4 & G5 & G6 & (_ & _ & Cr & _)). subst B. unfold SEC_UOFF.
    pose proof (sec_facts n ltac:(clear -G5; lia) G6) as (_ & _ & _ & RSR & _ & NSE & _ & MSR & _). rewrite <- G4 in MSR.
    pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_NUM_CLASSES, K_REGION in *; clear -Hc RSP; nia).
    unfold K_REGION, K_FREEARR_OFF in *. clear -Cr RI P5 P4 A1 A2 G5 RSR NSE MSR. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc"] Lemma disjoint_from_In : forall (Wx : list (Z * Z)) A k iv, disjoint_from Wx A k -> In iv Wx -> A + k <= fst iv \/ snd iv <= A.
Proof.
  intros Wx A k iv. induction Wx as [|[lo hi] Wx IH]; intros D Hin; [destruct Hin|].
  cbn in D. destruct D as [D1 D2]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>30294239397.26000004S2D1".
destruct Hin as [<-|Hin]; [cbn; lia| apply IH; assumption].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc st X LB m ALO AR BL HFK CW"] Lemma P_sh_res : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof.
  intros A k H1 Hk H2. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ad_fake_res L ALO) as D. pose proof (ao_res_hi L ALO) as RHI. unfold aobj, adisj in *.
  assert (SR : 2148232192 <= shad (al_res L) /\ shad (al_res L + 137439023104) <= shad ATOP   (* [comment removed for export] *)
               /\ (shad (al_res L + 137439023104) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad (al_res L))).
  { rewrite !shad_div. unfold ASHOFF. clear -ORS OFK D RHI. Local Ltac2 Set LiaHints.tbl := fun () => "0050=11446827096.949503560163.951796692231.959867800729.66000075077.9 00000700A00E00T00[S2H22SRS2H12H22SRS2HkS3ORS3OFK1D3RHIS2H12SR".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  apply P_sh; clear -SR H1 Hk H2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc st X LB m ALO AR BL HFK CW"] Lemma P_dtls : forall A k, al_dtls L <= A -> 0 <= k -> A + k <= al_dtls L + 4096 -> disjoint_from W' A k.
Proof.
  intros A k H1 Hk H2.
  pose proof (ao_dtls L ALO) as OD. pose proof (ad_fake_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  unfold aobj, adisj in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>19455736091.1037541430130.1448880235586.7 59758008323.6 00000=00U00\00fS2H12H22Q22CdS2H12H22D23RSP3ORS2S12S2S2H22ODS2H12H22D1".
apply P_obj; [exact (aobj_sub_sclr _ _ A k (ao_dtls L ALO) H1 H2)| exact (aobj_sub_iclr _ _ A k (ao_dtls L ALO) H1 H2)| exact Hk| clear -H2 OD; lia| clear -H1 H2 D1; lia|].   (* [comment removed for export] *)
  intros p B n Hin. destruct (hb_where p B n Hin) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - pose proof (hb_prim_span p B n c Hin Hc Q1 Q2) as (S1 & S2 & S3). unfold K_REGION, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    clear -H1 H2 S1 S2 D2 RSP ORS. lia.
  - cbn [sec_wf1] in Q3. destruct Q3 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Cd)). clear -H1 H2 Cd Q2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc st X LB m ALO AR BL HFK CW"] Lemma P_fakehdr : disjoint_from W' (al_fake L) 36864.
Proof.
  subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. Local Ltac2 Set LiaHints.tbl := fun () => "0070>19211233412.1119211354197.9 19217711082.1219217711082.1419217711082.1519217711082.9 50850525385.0 00000=00G00S01501L01^01_S2B22B12Q22CfS2F12K52B1S2I24OFKI2I3S2I12I23OFK4OFKS2I02I32F12F22K52K6S2B12B22S12S21D3RSP3ORSS2K13OFK2K54OFKS1HS".
pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.   (* [comment removed for export] *)
  pose proof OFK as (_ & _ & _ & OFKS & _). unfold sclr, KLS in OFKS.
  pose proof (ao_stack L ALO) as (_ & _ & S47 & SB). unfold aobj in *.
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 SB NEV OFK. lia.
  - destruct (aci_ok1 iv Hiv) as [_ I3]. unfold AIMG_HI in I3. clear -I1 I2 I3 NEV OFK OFKI. lia.
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & _). clear -K5 F1 F2 NEV. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + pose proof (hb_clear_fake_obj) as _. destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (hb_prim_span q B n' c Hb Hc Q1 Q2) as (S1 & S2 & _). pose proof (ad_fake_res L ALO) as D. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
        unfold adisj, aobj, K_REGION, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *. clear -S1 S2 D RSP ORS B1 B2 NEV. lia.
      * cbn [sec_wf1] in Q3. destruct Q3 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & Cf & _)). clear -Cf B1 B2 NEV Q2. lia.
    + destruct (afake_lb L LB m cls B n' HFK Hb) as (_ & _ & _ & _ & K5 & _). clear -K5 B1 B2 NEV. lia.
  - clear -K5 NEV OFK OFKS. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 I3]. unfold AIMG_HI in *. clear -I0 I1 I2 I3 NEV OFK OFKS OFKI. lia.
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & K6 & _). unfold FAKESZ in *.
    clear -K5 K6 F1 F2 OFK OFKS NEV. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc LB W ALO AR BL HFK MU0 WM CW W' MU"] Lemma aslot_client : forall c k, 1 <= c < K_NUM_CLASSES -> 0 <= k < ndist st c ->
  match busy_of X c k with None => junk_at m (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m b end ->
  match busy_of X c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end.
Proof.
  intros c k Hc Hk SL.
  pose proof AR as (WF & _). pose proof (size_of_class_facts c Hc) as [QS _].
  pose proof WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC c Hc) as (A1 & A2 & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "00B0>1685717371.0  19326977656.2 20119998637.8 28006451339.5 34419814823.2 36782708560.2 37707887324.3 39145840517.3 39609893326.144146706116.5  41688916150.4 43470275966.1050732020802.1454330615135.8 6002173134.8  63468094640.5 64167879746.4 67528538155.3 00000100500=00B00F00J00K00L00g00k00l01501J01Y01h01i01j01kSS2QSS2N03FITS3H16S2HpS2RZSSS2A12A22P52P43RI13RI22HA2HBS2RZSS2HA2HB1DS2A12A22P43ORS3RI22HBS2P53RI13RHI2RZS2P53RI13RHI2HASSS".
pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 A1) Hk) as (P5 & P4 & P0).
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_NUM_CLASSES, K_REGION in *; clear -Hc RSP; nia).
  destruct RI as [RI1 RI2]. unfold K_REGION, K_FREEARR_OFF in *. pose proof (ao_res_hi L ALO) as RHI.
  (* [comment removed for export] *)
  assert (PSUB : forall A kk, aslot_addr L c k <= A -> 0 <= kk -> A + kk <= aslot_addr L c k + size_of_class c ->
      (forall b, busy_of X c k = Some b -> match xb_st b with BLive _ => A + kk <= xb_user L b \/ xb_user L b + xb_n b <= A | _ => True end) ->
      disjoint_from W' A kk).
  { intros A kk HA Hkk HB OWN.
    apply P_obj; [unfold sclr; right; clear -HA P5 RI1 RHI; lia| unfold iclr, AIMG_HI; split; [clear -HA P5 RI1 RHI; lia| right; clear -HA P5 RI1 RHI; lia]
                 | exact Hkk| atop_facts; clear -HB P4 A1 A2 RI2 ORS; lia
                 | apply hb_clear_fake_obj; clear -HA HB P5 P4 A1 A2 RI1 RI2; lia|].   (* [comment removed for export] *)
    intros p B n Hin. destruct (slot_vs_blocks c k p B n Hc Hk Hin) as [(b & EB & Sb & -> & ->)|D]; [| clear -D HA HB; lia].
    specialize (OWN b EB). rewrite Sb in OWN. exact OWN. }
  destruct (busy_of X c k) as [b|] eqn:EB.
  - destruct (busy_of_Some_facts X c k b EB) as (Hb & Cb & Kb). pose proof (awf_fits L st X b WF Hb) as FIT.
    destruct (xb_st b) as [q| |] eqn:Sb.
    + (* [comment removed for export] *)
      unfold aslot_busy in SL |- *. cbv zeta in SL |- *. rewrite Sb in SL |- *. unfold xb_fits in FIT. rewrite Sb in FIT. destruct FIT as (N0 & RZ & FIT).
      unfold xb_user, xb_alloc in *. rewrite Cb, Kb in *. destruct SL as (LH & [stb [E HDR]] & UJ).
      assert (D : disjoint_from W' (aslot_addr L c k) (rz_size (xb_n b))).
      { apply PSUB; [clear; lia| clear -RZ; lia| clear -FIT RZ N0; pose proof (rounded_size_ge (xb_n b)); lia|].
        intros b' EB'. injection EB' as <-. rewrite Sb. unfold xb_user, xb_alloc. rewrite Cb, Kb. left. clear; lia. }
      split; [| split].
      * intros H16. destruct (LH H16) as [LC J]. split.
        -- eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | clear; lia | clear -H16; lia | clear; lia].
        -- eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | clear; lia | clear -Hp; lia | clear -Hp; lia].
      * exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
        eapply disjoint_from_sub; [exact D | clear -RZ; lia | clear; lia | clear; lia].
      * eapply junk_any; [exact UJ| exact WM| clear -P5 RI1 RHI RZ; lia].   (* [comment removed for export] *)
    + eapply (aslot_busy_frame L W' m m' MU WM); [exact SL| exact FIT|]. unfold xb_alloc. rewrite Cb, Kb.
      apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. injection EB' as <-. rewrite Sb. exact I.
    + eapply (aslot_busy_frame L W' m m' MU WM); [exact SL| exact FIT|]. unfold xb_alloc. rewrite Cb, Kb.
      apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. injection EB' as <-. rewrite Sb. exact I.
  - eapply junk_frame; [exact SL | exact MU | exact WM |]. intros _. apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. discriminate EB'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="X LB W ALO AR BL HFK MU0 WM CW W' MU"] Lemma asec_chunk_client : forall mb ms n idx lv,
  In (CSec mb ms n) (sec_chunks_of st) -> sec_wf1 L (CSec mb ms n) ->
  (lv = true <-> sec_live st (CSec mb ms n)) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros mb ms n idx lv INC WF1 LVE CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & GC). pose proof GC as (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd).
  Local Ltac2 Set LiaHints.tbl := fun () => "00T0>10065782946.1910348506307.1411446827096.131149840136.0  1685717371.0  18107032235.4 18266057370.1 18392029611.1 21839884792.1 22096821547.5 22731753056.1 24963147917.6 27146320176.4 28989849047.5 29180318668.1 34739953483.1 35864023691.6 40397452967.6 40799456635.2 4643500219.16 4648867147.1  48175602055.6 48880235586.1349503560163.1351607648958.2 51796692231.1352394314868.1 52784342954.2053238990468.2 55607616718.1 57938841640.1459757942914.136000075077.13 6644414584.5  66500705481.5 9993908144.2  00000W01001801901:01;01<01=01>01G01H01I01M01R01S01T01U01Z01^02C02D02I02_02m03103503603_03d03e03l04E04M04R04S04XS2G53RSR3NSE3MSR2H12H21D4RSR'4NSE'4MSR'S2G22G53RSR3NSE3MSR2H12H2S3GR52H2SSSSSSS3GR13GR3SSS2H2S3GR3SSSS3GR1S2G5S2G12G32G52Cf3RSR3NSE3MSR3MSM3OFK3G2aSS3GR3S2G32G53RSR3NSE3MSR2H2S3GR62H12Hk2H2S2G5S2HkSS2G52Cr3RSR3NSE3MSR2H12H23FIT2R12R22RZ2RGS3G5'SS2G22H1S2G52Cf3RSR3NSE3MSR2H12H2S3GR42H1S3GR1SS3G2a".
pose proof (sec_facts n ltac:(clear -G5; lia) G6) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- G4 in MSR, MSM, MSB.
  pose proof AR as (WF & _ & _ & _ & _ & _ & HS & _). cbn [AHI ah_sec] in HS. unfold ASEC_of in HS. pose proof HS as ((_ & _ & _ & _ & _ & WFA & [ND PW]) & _).
  pose proof (ao_fake L ALO) as OFK. unfold aobj in OFK. unfold K_HIGH_MEM in *.
  pose proof (ablk_lin _ _ G2) as (G2a & G2b & _ & _).   (* [comment removed for export] *)
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8 /\ 2148232192 <= shad mb /\ shad mb + ms / 8 <= shad ATOP
               /\ (shad mb + ms / 8 <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad mb)).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. unfold ASHOFF, AIMG_HI in *. clear -G1 G2a G2b G3 G5 RSR NSE MSR MSM Cf OFK. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct GR as (GR1 & GR2 & GR3 & GR4 & GR5 & GR6).
  (* [comment removed for export] *)
  assert (DLO : forall A k, mb <= A -> 0 <= k -> A + k <= mb + 6144 -> disjoint_from W' A k).
  { intros A k H1 Hk H2.
    apply P_obj; [clear -H1 H2 G2 MSR NSE RSR G5; unfold ablk, sclr, KLS, AIMG_HI in *; lia| clear -H1 H2 G2 MSR NSE RSR G5; unfold ablk, iclr, AIMG_LO, AIMG_HI, KLS in *; lia
                 | exact Hk| atop_facts; clear -H2 G3 MSR NSE RSR G5; lia| clear -H1 H2 Cf MSR NSE RSR G5; lia|].
    intros p B n' Hin. destruct (hb_cases L st X LB m p B n' ALO AR BL Hin) as [(b & _ & _ & Ub & Nb & _ & NB' & FIT & _ & _ & _ & _ & _ & R1 & R2)|(mb' & ms' & Lp & -> & G' & _ & INC')].
    - pose proof (rz_size_ge16 (xb_n b)) as RZ. pose proof (rounded_size_ge n') as RG. unfold xb_user in *. subst B n'. clear -R1 R2 Cr H1 H2 MSR NSE RSR RZ G5 FIT RG NB'. lia.
    - unfold SEC_UOFF. destruct (achunk_eq_dec' (CSec mb' ms' n') (CSec mb ms n)) as [E|NE].
      + injection E as -> -> ->. left. clear -H2; lia.
      + pose proof (PW _ _ INC' INC NE) as D. cbn [sec_mb sec_ms] in D.
        cbn [sec_wf1] in G'. destruct G' as (_ & _ & _ & G4' & G5' & G6' & _). pose proof (sec_facts n' ltac:(clear -G5'; lia) G6') as (_ & _ & _ & RSR' & _ & NSE' & _ & MSR' & _). rewrite <- G4' in MSR'.
        clear -D H1 H2 MSR' NSE' RSR' G5' MSR NSE RSR G5. lia. }
  assert (DSH : forall A k, shad mb <= A -> 0 <= k -> A + k <= shad mb + ms / 8 -> disjoint_from W' A k).
  { intros A k H1 Hk H2. apply P_sh; clear -H1 Hk H2 GR4 GR5 GR6; lia. }
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DLO; clear; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DLO; clear; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DLO; clear; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DLO; clear; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DLO; clear; lia]. }
  split; [eapply junk_any; [exact H6| exact WM| clear -G2a; unfold AIMG_HI in *; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DSH; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DSH; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DSH; clear -GR3 GR1 POS; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="st X m W ALO AR BL HFK MU0 WM CW W' MU"] Lemma afake_client : AFAKE L LB m'.
Proof.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *.
  pose proof (ablk_lin _ _ G2) as (G2a & G2b & G2c & G2d). unfold AIMG_HI in G2a.   (* [comment removed for export] *)
  pose proof P_fakehdr as DF.
  split; [exact G|].
  split.
  { destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold afake_cells.
    Local Ltac2 Set LiaHints.tbl := fun () => "02U0>10068349625.0 10317707088.1 10557452072.5410774136387.5410899766051.5411977215400.541247274280.54 15502358050.1 15533891240.5415617278696.5415716413480.5415793936552.5416014294056.541641167784.54 16597149864.5416597860308.2 16769637416.541685717371.0  18308001464.5419851325864.5420107690920.5421013273897.0 21122236456.5421425112872.542154467240.54 22021355048.5422147171880.5422922120872.5423747685160.542376824232.54 23820843304.5424107459496.5424147866296.5424542813936.9 2486733860.3  24922284613.1 2534225704.54 25625578664.5425900733864.5426075826344.5426090158760.5426495985848.5427389166120.5428215388904.5428271849128.5428473696040.542886830632.54 29267119784.5429408471592.5430461437096.5430771397288.5431357097512.5431607872168.5431654361320.5432189500200.5432431168552.5433131529000.5433635548200.5434481174696.5434530535208.5435016495016.5435099851176.5436038506792.5436042036898.1 36121963048.5436388299843.5436685980840.5436987499432.5438401289144.5438458152360.5438999270568.5439403510440.5439547748904.5439693465128.5440436634536.544049924008.54 40715026243.5441795581736.54418199080.54  42271358275.5442411609006.0 42462908329.0 4255502882.1  43141873960.5443297428264.5443840340648.5443900587688.5444076889640.5445485555269.1 45811447720.5446222758824.544633620136.54 46414973992.5446800828856.5446994666152.5447939710376.5448085547944.5448270900904.5448294403395.5448352115512.544835283270.2  48620072515.5448980212003.5449097857960.5449966170856.5450093813800.5450203955267.1 50861320610.4 50976977577.0 51887209064.545201587128.54 52485517224.5452666326440.5452933799491.5453650965800.5453802289448.545420080195.54 54525220392.5454849894184.5455040009128.5455113082408.5457294370088.5457445693736.5458102276776.545822019496.54 58336488360.5459139159848.5459293085224.5459500846120.5459699735720.5460641099587.5460705889448.5460834414120.5460889500344.5460956300472.5461081823544.5461620741288.5462250917608.5462674464041.0 62850999976.5462951054248.5463394883880.5463541315525.1 64189583144.5464345074216.5464738207016.5464815926952.5465078255272.5466759694776.5466789914536.546774249000.54 68207423657.0 68653792936.546880638648.54 759157544.54  7745082152.54 829216296.54  8503663528.54 8592745896.54 8849362728.54 8934092200.54 8971102376.54 9065430952.54 9164489512.54 9926424131.54 00000100200700<00A00F00K00L00Q00V00[00`00e00j00o01401901:01?01D01I01J01O01T01Y01^01c01h01m02202702<02A02O02T02U02Z02_02d02i02n03303803=03B03G03L03Q03V03[03`03e03j03o04404904>04C04H04M04R04W04\04]04b04g04l05105605;05@05E05J05O05T05Y05^05c05h05m05n05o06006506:06?06D06I06J06O06T06Y06^06c06h06m07207707<07A07F07K07P07U07Z07_07`07d07e07j07o08408908>08C08H08M08R08W08\08a08f08k09009509:09?09D09I09N09S09X09]09b09g09l0:10:60:70:<0:A0:F0:G0:L0:Q0:V0:[0:`0:e0:j0:o0;00;50;:0;?0;D0;I0;N0;S0;X0;]0;b0;g0;l0<1SSS3G2bS3G2bS3G2bS3G2bS3G2bSS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2aS3G2bSS3G2bS3G2bS3G2bSS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2a3G2c2FR1HS3G2aSS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bSS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bSSSS3G2bS3G2bS3G2bS3G2bS3G2bSS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G7iS3G2bS3G2bS3G2bS3G2bS3G2bSS2FRSS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bSS3G2bS3G2bS3G2bSS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bSS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2bS3G2b".
split; [eapply cells_frame; [exact C1| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac]]|].
    split; [eapply cells_frame; [exact C2| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac]]|].
    split; [eapply cells_frame; [exact C3| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac]]|].
    split; [eapply cells_frame; [exact C4| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac]]|].
    split; [eapply cells_frame; [exact C5| exact MU| exact WM| cbn; apply P_dtls; clear; lia]|].
    split; [eapply cells_frame; [exact C6| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac]]|].
    split; [eapply cells_frame; [exact C7| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac]]|].
    eapply dc_at_any2; [exact C8| exact WM| destruct G7 as (_ & G7i & _); unfold iclr, AIMG_LO, AIMG_HI in G7i; clear -G7i; lia]. }   (* [comment removed for export] *)
  split. { exists h0, h1, h2, hs. eapply cells_frame; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]. }
  split; [eapply cells_frame; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]|].
  split; [eapply cells_frame; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| clear -G2a; lia]|].
  split. { eapply dc_at_any; [exact DC2| exact WM|]. rewrite shad_div. unfold ASHOFF. clear -G2a G2b. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    rewrite (munch_outside_range W' m m' (al_fake L) 36864) in Hb; [eapply FL; eauto| exact MU| exact DF| clear -FR; lia| clear -FR G2a G2c G3; lia].
  - intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    rewrite (munch_outside_range W' m m' (al_fake L) 36864); [exact Hb| exact MU| exact DF| clear -FR; lia| clear -FR G2a G2c G3; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="LB m W ALO AR BL HFK MU0 WM CW W' MU"] Theorem AREP_client : AREP AHI L st X m'.
Proof.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_ptr L ALO) as OP.
  pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  unfold aobj in ORS, OT, OC, ON, OS, OP.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  Local Ltac2 Set LiaHints.tbl := fun () => "0F?0>10029160762.5510107077370.0 10107239162.5510231081425.5510255999338.5510271909450.5510277245339.5510285913640.7210302292593.551030542033.55 10313546700.2 10317707088.1 10421904849.5510433566795.5810467573899.5510616215994.5510680827978.5510717266635.5510738284746.5510741179338.5510890948810.5510926224033.5510940882522.5510944979658.721097043194.72 1098044107.58 10998753738.5511027883594.5511057141146.5511170297290.5511303811210.5511318206353.551132753482.55 11391016650.5511647093066.5911731368347.5511861689418.5511878961930.5511931363386.5511947901370.5512009374747.5512079622090.5512097820777.4 12105266250.551226957514.55 12343656570.5512398789322.5512413710154.5512483347274.5512490728250.5512508314122.6012555400762.551265059162.55 12655224669.3 12670689610.5512703043995.5512782386922.551278342858.55 12800699176.5512869106890.5512877090629.1 12884104010.7212909124922.551291099082.55 1291602554.55 13097184323.5513107291210.5513137870266.5513138726090.5513249168296.7213258726602.7213369749578.5513374621338.0 13385627722.721339885882.55 13407141002.551342024906.55 13497591498.5513521431626.5913522945169.5513620014090.5513654388618.5513669596042.6013684015178.5513757352330.5513876186954.5513915842122.5513933274449.5514003831931.2 14022507448.7214059076730.5514063577546.5514196308042.5514364434362.5514503842153.5 14585595850.5514650434298.7214715794698.5514889626042.5514910319434.5514942251130.5515032888890.5515197586506.5515253396042.5515314273098.5515412202378.551542040650.55 15435108986.5515464065546.5515470528209.5515502962378.5515515497321.5 15515743081.5 1552851402.55 15542321866.5515550008778.5515600913946.0 15641247130.0 15710667850.5515717872074.5515744126026.5515768478922.7215800899146.5515956337448.5516001494410.5516051983946.7216121585114.5516227733313.551622934737.55 16253427402.5516401498443.5516477159530.5516534157257.1 16633400922.5516728304506.5516819224858.0 1685717371.0  16871165050.5516878402442.5516891439114.5516945038410.5517003715786.5517007846490.5517132899112.5517135113850.551713555531.58 17139675239.5 17170994216.7217179434234.5517272559313.5517302944067.7217310089290.5517370792970.5517375901514.5517411908474.5517483785144.721755741642.55 17561198376.5517629121448.7217683448330.6017712515082.5517736881738.5517756435146.5517762375226.5517813711963.5817847570442.5517868871115.58179463882.55  17965623498.5517980045770.5517989502888.7218042295498.5518047479498.5918051070410.551805167953.72 18106462146.4 18112593354.5518137898826.5518211243130.5518230906523.5518250325834.5518258467240.5518284800458.5518288861642.5518289475658.5518295038282.5518316524559.6 18351021736.7218382873018.551847755083.58 18540717450.5518641476776.7218665387046.4 18681837642.5518697860490.5518761899338.7218813810698.5518819676314.0 18851113722.5518919672650.5519030579274.5519085345754.5519094587914.5519133075274.5519209897994.5519264880650.5519326977656.2 19352225226.5519447490762.721944815482.55 19459245642.5519475394762.5519498476235.5519537214538.5519582371368.7219624560922.0 19678020314.0 19683274746.5519694156729.0 19766667978.5519773457866.5519806780682.5519811583451.5519826928074.5519904425419.5819990846666.5519997301913.4 20023201866.5520080622869.0 20110758939.5520156035240.7220188687016.7220288397258.552053774538.55 20538944250.5520542421137.5520664887370.5520742166789.7520754335185.5520819884874.5520846705355.5820891379240.7220930921866.5520959376970.552104345850.55 21059035130.5521068041418.5521102394408.7221120998858.7221246808227.2 21273044938.5521451327946.5521534780346.5521608397050.7221650694474.5521659053386.5521664629370.5521817517258.5521849567402.5521929847720.5521950459770.5521976227786.5521995317258.5522044666314.5522096176970.5522204201290.552220810602.55 22226767178.7222238627530.5522252709002.5522323215690.5522323418954.7222323474897.5522350708346.552237012090.55 22380900506.0 22393918107.5522394738506.5522406064586.5522412312680.7222564825546.5522609964072.7222775718602.5522829853736.7223000344906.5523019168074.5523029073843.2 23033955850.5523063708106.5523098688138.5523103835722.5523170023562.5523211359306.5523212012938.6023240051002.5523282302120.5523352297162.5523376378442.5523482468746.5523554543691.5523622683978.5523655811354.0 23665833674.552368639434.55 23777717578.5523853158410.552395697162.55 23993645818.5524092187803.552418908490.55 24200206794.5524202925642.5524258464586.5524360064970.5524368225754.0 24374851722.5524393655114.5524405196129.5524409920586.5524456572426.5524520651722.5524523042250.5524531394122.552456861514.55 24688751418.5524706005002.6024709513658.5524729491914.5524738880074.5524765837370.5524874488826.5524930878154.5525008256266.5525018059850.5525042526218.5525049514442.7225096308066.5 25172563658.5525207650856.7225289147850.5925297850058.5525308170314.5525320480842.5525326120250.5525332579450.5525364850337.5525376202346.5525438091466.5525509362763.5525519295451.5525608871738.5525642288570.5525775307978.5525778920586.6025927571866.0 2598582810.0  26031588938.5526038753850.5526042701002.5526100196753.5526182298961.7226199814033.5526201687869.2 26204124712.7226207294714.5526238245128.0 2632833082.55 263539770.55  26393329226.5526436243227.5526453448603.5526562318522.552656244177.55 26638945738.5526745688138.552678019985.55 26825243466.5526829423882.5526833884315.5526861080394.5526926157786.5526939583034.55269559498.55  27044402746.5527070384266.6027132606474.5527359879626.7227360918865.5527384519610.5527468586698.5527529842378.5527548629195.5827574161466.6027685195082.5527758980170.5527829223562.6027829530698.7228011160209.5528040546250.5528058537681.5528192728292.5528233225098.5528233644939.2 28335848058.5528341441418.5528411409850.5528458131624.5528483242890.5528497821706.5528580371658.5528592627018.5528595841994.5528640081729.5528659064721.6028728630090.5528729174346.5528751486970.7228824701595.5528829632394.602893949992.72 28947054330.5529019651914.5529047565242.5529136806986.5529171850395.5529216634324.5529244703178.5529500132042.5529527434442.5929552035322.5929570950184.7229581962058.5529602336859.5829661505994.5529698756298.5529825899748.5529876442010.0 298791802.55  29911413418.5529918680010.5530003076564.5530018805770.5530133104970.5530146455080.7230174801866.5530211331642.5530217663482.5530292578763.5530321418049.5530357100571.5530467059018.5530544539466.5530548528451.7230579940426.5530584017738.5530616980170.5530643284298.5530653669946.5530701606858.5530713594570.5530725485642.5530764188106.5530778141786.5530793728552.7230912897340.3 30917072202.5530925151272.7230967927114.5530970707978.5530987552266.5531002039354.5531012612437.0 31020431290.5531033177547.5831049232330.5531069527498.5531080832913.5531100152906.5531111232970.5531113866826.5531134391114.5531218872876.1 31228516683.5531250500251.5531257498506.5531257895626.5531280564234.6031313271323.5531320653002.553134620730.55 31364819258.5531487749450.5531513065722.5531536066761.1 31555695057.5531588007835.5531642085818.5531667613898.5531671261690.5531762336714.5531810591178.5531822058426.5531885326801.5531895395146.5531905450570.7231933984517.3 32084248360.5532168012234.5532212267082.5532260802826.553228216138.59 32313738954.5532326847912.5532359461416.7232360178618.5532460182986.5532476013770.5532478399306.55325369354.55  3254517450.55 3256364107.55 32586941962.6032628713256.5532641671306.5532649116618.5532663722826.5532673876538.5532827535818.5532830096394.5532851034954.5532895681066.0 32908269578.5532917795153.6 3292555281.55 33147530705.5533267473866.5533288030714.5933300441034.5533320865994.5533397919562.5533482846650.5533502832762.5533547280138.5533568965322.5533593921642.55336472488.55  3367763275.55 33691177098.5533844315466.5533909356490.5534016808266.5534021835274.5534066164682.5534110987786.5534126296266.5534193706042.553425474634.59 3433171290.55 34361639306.6034393597352.7234442346826.5534521219823.7 34543604874.553459169226.55 34605723338.5534605942042.0 34620182666.5534699874378.5534715413066.7234794294696.7234800268682.5534809045002.5534842649354.553484735306.55 34895125898.553489956346.55 34911824778.5534951772072.7235050868042.5535094149770.5535148327370.5535155193162.5935193749578.5535241523594.5935243510922.5535294050977.5535354339274.7235373261450.7235413567242.5535446285386.5535494572874.7235531918666.5535547787729.5535549190586.5535549308346.5535636776570.5535655459275.5835657400906.5535659378634.5535958398666.5536008840603.5536080434977.5536256435018.5536351245480.5536449675461.1 36453235786.5536511893962.5536630721146.5536655927930.5536667146139.55366882472.72  3670961098.55 36720576138.6036751843019.5836771247882.5536782969055.2 36788830650.553679144906.55 3687442890.55 36874520826.5536882131914.7236887120666.0 36958550341.1 36979591608.7236994610762.5537009599562.5537111629192.0 3715518730.55 37156630869.0 37171104936.7237251647050.7237252942090.5537256876874.5537263272529.5537305821674.5537394822602.553740608522.55 37428213067.5837439197594.553747231818.55 37552863434.7237564336869.5 3756518122.55 37613994522.0 37662783306.55376942090.55  37776478730.5537887850570.5537891631690.5537907511962.4 37915580426.5537917019857.553794258762.59 37972133002.5537999485770.5538025458234.553803306826.72 38038005705.1 38041098058.5538041363914.5538148514426.5538227139658.7238250767016.7238292895637.0 382942026.55  38312722243.723833130346.55 38400602890.5538419834792.7238436634709.0 38585452090.5538599636554.5538692635477.0 38698219210.5538727965498.5538907343899.9 3892805288.72 38948636245.0 39005197274.5539012636437.0 39043066442.5539076636629.0 39172636981.0 39186074449.7239188636933.0 39190855882.5539212212026.5539220637093.0 39268637205.0 39277432826.553930602954.55 39332637397.0 39396637589.0 39412351690.5539412637669.0 39431622865.5539433675706.5539483188490.5539609907710.5 39658513705.0 3967024330.72 39675183226.5539716638549.0 39721604933.0 39765893050.5539880018058.0 39883378570.5539905552202.7239993244363.5540016182266.5540077043514.5540077524922.5540079502538.5540113780106.5540177615818.5540206491882.5540254995658.5540328258123.5540388345546.7240404985594.7240426703306.5540510704842.5540594118602.554060032650.55 4062230170.0  4062335434.55 40684766376.7240720421178.5540761583460.5840796015946.5540836470794.5540877660266.5540890963153.5540974333258.5540975759802.5541028595995.5541094240378.5541097264273.5541100048714.7241120432332.3 4117304522.72 41200903633.5541204698954.7241235895690.5541264243432.7241378375930.5541380430282.5541395498058.554139684362.55 41443187624.7241447663258.0 41448258170.5541485553546.5541497511114.5941521482682.554153087899.55 41569698257.5541588188106.554174012874.55 41749118154.5541781849818.0 41869563514.5541916243898.5541977840876.1 41990853258.5542043850.55   42149215178.7242190131530.5542239952714.554235483146.55 42380900426.5542411609006.0 42426141136.5 42495314442.604253627674.0  42583125531.5542597921786.7242599652106.5542615043658.5542671814730.5542726987850.5542749264330.7242785789962.6042806652474.5542837413194.5542902703306.5542963821339.5542964298570.5543078345658.5543158474954.5543204299770.5543240308746.5543242622347.5543268985066.5543298987530.5543300649301.0 43315687370.5543328099914.5543393123082.5543394350554.5543508283553.5543554307580.3 43556650069.0 43569923658.5543685420106.5543690850234.5543732592186.5543749601674.5543781106499.3 43849082186.5543902928714.724390613706.55 43929167434.5544023486026.5544147680168.7244160404970.5544168529553.5544172790696.7244211631441.5544236693962.5944392184906.5544511319121.5544554089204.5 44599708794.5544637014410.5544701224522.5544702250065.5944707000778.5944773074250.5544886403914.7244987209594.5545083664282.0 45104009146.5545193711242.55452488266.59  45318467450.5545348132874.554535093690.55 45376282961.554541912219.55 45445587658.5545447087818.5545459604954.554549001546.55 45513099857.5545519367626.5545629989450.7245699700106.5545769612362.7245779442378.55457794600.72  45784065594.5545863075921.5545873544826.5545886108712.7245890039802.5545908924600.5545917667898.554593664074.59 45976200232.7246035800858.0 46180643834.5546284514186.5546302591441.5546521121866.5546534515914.5546554246218.7246696603210.5546707566666.5546819049000.7246833245002.7246836000186.5546890356474.5546929524026.5547008985546.5547044402058.554704467978.55 47083209162.5547115551674.5547120670632.7247209608138.554721820810.55 4724261322.55 47315824801.554737642186.55 47411770506.5547486235770.5547539820618.554755498424.72 47593277514.5547648606362.0 47688768330.5547689959626.5547691985482.5547719144104.7247881625745.5547889842890.5547933390666.5547972561930.5547989254858.5547994101834.5548034511114.5548036252314.0 48161399882.5548184667338.5548206349002.5548304689994.5548313939658.5548466331083.5548503958602.5548512773066.5548538556298.5548552444968.7248554821898.5548642739530.5548670577210.5548755859066.5548940112074.5548969949818.5548989652933.1 49001420618.5549002600650.5549051031162.5549134831178.5549153563089.5549167139738.0 49214230042.0 49239202234.5549259096603.5549264257034.5549316297882.0 4932792603.55 49401267786.5549437954250.5549495465354.5549587534545.5549655214154.5549693515322.5549711883850.5549713781962.5549807010856.7249809940090.5549814129902.3 49913317946.5549987370032.1050054432698.5550132099466.5550203955267.1 50252617978.5550359020682.5550401410506.5550453223754.7250477360465.725049006522.55 50533444538.5550546226698.5550632536010.5550681474698.5550833989834.5550868073755.5550882520202.5550916693578.5550946873354.5550951098577.555096742730.55 50985958154.5551079193128.7251087337226.5551172248650.5551172607569.5951174427722.5551229137866.7251348193786.5551374530106.5551504537797.1 51563090378.5551619947944.7251654378938.5551664324682.555168148362.55 517997450.55  51862747473.5551950623400.7252189502794.5552206509690.5552240849226.5552267253386.5552319664842.5552325775050.7252331808395.5552360333434.5552380576138.5552474011098.5552489829152.4 52497090698.5552500980810.0 52564788817.9 52569081327.1 525698122.55  52573909818.5552577184458.5552602288587.585265572154.55 52788980106.5552789879114.5552792543578.5552856441274.5552890622522.5553014694026.5553043406842.5553060565194.5553106653352.725322146426.55 5335113354.55 53408537610.5553473848506.5553543486193.1 53594422427.555368093066.60 53810630696.7253933181770.5553944526346.5553985294858.5554069469642.5554109131476.555417563066.55 54179566794.5554312155688.725432121115.55 54404297233.555451627850.55 54547776330.555460335818.55 5462387802.55 54671842890.5554806945995.5854820683861.0 54846581944.5554856171322.5554895966282.5554901278090.5554953652027.5 55081680074.5955125618122.5555153932456.5555383186344.5555398531706.5555504948426.5555547229658.5555556589882.5555588686165.0 55632877066.555574371594.55 55769527690.5555884343505.5555910302794.6055933763082.5555949009226.5555952403066.5555966506250.0 55980145105.5555983294586.5556009508426.7256247734155.5556268009162.5556297408040.7256307887306.5556309276362.5556339599370.0 56434651850.5556449076945.5556527591754.7256608547658.555662539386.55 567167690.55  56718339530.5556746703434.5556778579082.5556824444362.555687446650.55 56909037706.7256974949963.5857029649338.5557047738170.5557066166202.5557109580282.5557119183179.5857266689098.555731836618.55 57397274792.5557457222723.5557473277050.5557502987978.5557645791259.5557658670026.5557752725514.6057825712138.5557922769402.5557954013002.5558058257098.7258137162554.5558321875082.5558328473530.5558354060090.5558413136730.55584624586.72  58478411914.5558487887627.5858664798410.7258683209802.5558729889994.5558753507146.5558794811304.72588087689.1   5887318330.55 58903174154.5558909763434.0 58930744042.5558972524753.5558972818506.7258973270346.5559015431754.555906612938.55 5911485514.55 59196396945.6059199794810.5559207471818.5559219106417.55592843210.55  59308586510.3 59704198602.5559787699274.555994289115.55 59977530394.0 60037360977.5560138476554.5560140784762.5560178217930.0 6029180577.55 60295670794.5560329404746.5960339840833.5560427044938.5560524831429.1 60527058826.5560587370890.7260643924200.7260700386088.5560740881673.5 60764258746.5560768212427.55607723130.55  60784864587.5560841594330.5560885859880.7260901543201.556094198434.1  60996855480.3 61008345034.5561088112539.5561115019338.5561157059210.5561169858506.556122552138.55 61285215697.5561296820874.5561317526922.5561332759050.5561439025546.5561539141841.5561556476618.5561585580154.5561598784970.5961631315306.5561693206218.5561715131594.5561721504314.6061741641530.5561798075850.556186067235.72 61941724362.5561952008986.5561953691786.5561979270794.5561993523658.7262020642826.5562040120266.556209603018.55 62109015370.5562195531210.5562271447194.0 62380671515.5562471492961.5562492771786.5562501751258.0 62588838906.5562590291018.7262631172299.5562670323537.7262743460298.5562752524426.5562756865738.7262780155722.5562780218068.55627994746.55  62853855818.7262869422154.556292111160.3  62951441691.5562972222548.2 62989686811.5562994636683.5563077731786.556309246522.55 63170311451.5563180274122.5563226286010.556333672360.72 63340648074.556336712504.72 6338859370.55 63473328618.5563543593914.5563570827729.5563612347722.5563658740170.5563661904202.5563679728986.0 63859466570.5563906527690.5563985325514.5564027646154.5564088336155.5564090870538.5564151313532.2 64177132618.5564267809738.5564285633082.5564356218378.5564383460810.5564401791434.556448635402.55 64540476874.5564599314641.5564626135754.5564666842314.5564693584970.5564740224506.5564795567690.5564854294858.5565040231114.5565197674186.556520379274.55 65220417034.5565226928970.5565253966880.1 65286644874.6065293332970.5565377850442.5565436776074.5565445025434.0 65459601425.3 6550464744.55 6560463562.55 65645221578.5565647853412.5865680081738.5565683608273.5565690740234.556569359691.55 65769234378.5565818118554.0 65820089658.5565831196049.5565879196107.5565887410250.5565919499914.5565920036682.5565986926058.5566048936517.1 66050705482.5966057856202.556614915082.55 66240208154.0 66310891432.7266320765386.5566339334474.5566374531274.7266378384506.5566405897738.5566438914385.7266512830538.5566526401320.5566596209786.556660151242.72 66628951115.0 66662654410.5566861025306.0 66927376122.5566984683633.3 67049299978.6067101353512.7267190219978.5567203619450.5567221969210.5567241252426.7267251849674.5567270680232.7267305312586.5567326385162.5567385796666.5567463092208.7 67493044218.5567529477962.5567549066314.5567550360890.5567638791633.5567679874570.5567722120778.5567723395739.5 6775360970.55 67762809634.1 68004553169.5568027593658.5568078634554.5568192306507.5868210850890.5568271676113.5568283253289.0 68308865307.5568331430219.0 68355418826.5568432782666.5568524803530.5568535946442.5568569628986.556857551754.55 68581723594.556859089733.7  6859347530.55 68666825169.5568686205839.756870967107.72 6936641354.55 6976049226.55 699209034.55  7029766554.0  7030402618.55 7081865674.72 7163289210.55 7226262840.72 7237743562.55 72999546.55   7320803146.55 7359305050.55 7363115722.55 7379737418.55 7444958074.55 7457518318.6  75824762.55   7586814027.58 7668815882.55 7708772131.72 775242570.72  775481866.55  7807800138.55 7808783387.55 7887592005.0  794320714.55  794967882.55  7973222568.72 8020698186.55 8062822202.55 8100535178.55 8126717385.1  8152897704.72 8169778378.72 8211641034.55 8248294090.55 8256016033.55 8323275466.55 8367321914.55 8380583370.59 8472218634.55 8494923722.55 8514014538.55 8546587979.58 8562921937.55 8640788170.55 869218058.55  8742985530.55 881560394.55  8817041226.55 8859966666.55 8867429160.55 8873125498.55 8886032842.55 8897836362.55 8901768865.55 8950590234.0  8981824458.55 8987588746.55 9027348938.55 9045003594.55 9128038026.55 9146936539.55 9147231434.72 9162993361.55 9173904202.3  9199932618.55 9229883210.55 9237344084.2  9305581050.55 9319311818.55 93304458.55   9364473482.55 9513666762.55 9521956426.55 9697632843.55 979419722.55  9899303354.55 9920086826.55 9952532939.55 00000100200300400500600700800900:00?00@00A00B00C00D00E00F00G00H00I00J00K00L00M00N00O00P00Q00R00S00T00U00V00W00X00Y00Z00[00\00]00^00f00g00h00i00j00k00l00m00n00o01001101201301401501601701801901:01;01<01=01>01?01@01A01B01C01D01E01F01G01H01I01J01K01L01M01N01O01P01Q01R01S01T01U01V01W01X01Y01\01]01^01_01`01a01b01c01d01e01f01g01h01i01j01k01l02302=02>02?02@02A02B02C02D02E02F02G02H02I02J02K02L02M02N02O02P02Q02R02S02T02U02V02W02X02Y02Z02[02\02]02^02f02g02h02i02j02k02l02m02n02o03003103203303403503603703803903:03;03<03=03>03?03@03A03B03J03K03L03M03N03O03P03Q03R03S03T03`03a03b03c03d03e03i03j03k03l03m03n03o04004104204304404504604:04;04<04=04>04?04@04A04B04C04D04E04F04G04H04I04J04K04L04M04Q04R04S04T04U04V04W04X04Y04Z04[04^04_04`04a04b04c04d04e04f04g04h04i04m04n04o05005105205305405505605705805905:05;05<05=05>05?05@05A05B05C05D05E05F05G05H05I05J05K05L05M05N05O05P05Q05R05S05T05U05V05W05X05Y05Z05[05\05]05^05_05`05a05b05c05d05e05f05g05h05i05j05k05l05m05n05o06006106206306406506606706806906:06;06<06=06>06?06@06A06B06C06K06L06M06N06O06P06Q06R06S06T06U06V06W06X06Y06Z06[06\06]06^06_06`06a06b06c06d06h06i06j06k06l06m06n06o07007107207307407507607707807907:07;07<07=07>07?07@07A07B07C07D07E07F07G07H07I07J07K07L07M07N07O07T07U07V07W07X07Y07Z07[07\07]07^07_07`07a07b07c07d07e07f07g07h07i07j07k07l07m07n07o08008108208308408508608708808908:08;08<08=08>08?08@08A08B08C08D08E08F08G08H08I08J08K08L08M08N08O08P08Q08V08W08X08Y08Z08[08\08]08^08_08`08a08b08c08d08e08f08g08h08i08j08k08l08m08n08o09009109209309409509609709809909:09;09<09=09>09B09C09D09E09F09G09H09I09J09K09L09M09N09O09P09Q09R09S09T09U09V09W09X09Y09Z09[09\09g09h09i09j09k09l09m09n09o0:00:10:20:30:40:50:60:70:80:90::0:;0:<0:=0:>0:?0:@0:A0:B0:C0:O0:P0:Q0:R0:S0:T0:U0:V0:W0:X0:Y0:Z0:[0:\0:]0:^0:_0:`0:a0:b0:c0:d0:e0:f0:g0:h0:i0:j0:k0:l0:m0:n0:o0;00;10;20;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;H0;I0;J0;K0;L0;M0;N0;O0;P0;Q0;R0;S0;T0;U0;V0;W0;X0;Y0;Z0;[0;\0;]0;^0;_0;`0;a0;e0;f0;g0;h0;i0;j0;k0;l0<00<10<20<30<40<50<60<70<80<90<:0<;0<<0<=0<>0<?0<@0<A0<B0<C0<D0<E0<F0<G0<H0<I0<[0<\0<]0<^0<_0<`0<a0<b0<c0<d0<e0<f0<g0<h0<i0<j0<k0<l0<m0<n0<o0=00=10=80=90=:0=;0=<0==0=>0=?0=@0=A0=B0=C0=D0=E0=F0=G0=H0=I0=J0=K0=L0=M0=N0=O0=P0=Q0=R0=S0=T0=U0=V0=W0=X0=Y0=Z0=[0=\0=]0=^0=_0=`0=e0=f0=g0=h0=i0=j0=k0=l0=m0=n0=o0>00>10>20>30>40>50>60>70>80>90>:0>;0><0>=0>>0>?0>@0>A0>B0>C0>D0>E0>L0>M0>N0>O0>P0>Q0>R0>S0>T0>U0>V0>W0>X0>Y0>Z0>[0>\0>]0>^0>_0>`0>a0>b0>c0>d0>e0>f0>g0>h0>m0>n0>o0?00?10?20?30?70?80?90?:0?;0?<0?=0?>0??0?@0?A0?B0?C0?D0?L0?M0?N0?O0?P0?Q0?R0?S0?T0?U0?V0?W0?X0?Y0?Z0?[0?\0?]0?^0?_0?`0?a0?b0?c0?d0?e0?f0?g0?h0?i0?j0?k0?l0?m0?n0?o0@00@10@20@30@40@50@60@70@80@90@:0@;0@<0@=0@>0@?0@@0@A0@B0@C0@D0@E0@F0@G0@H0@I0@J0@K0@L0@M0@N0@O0@P0@Q0@R0@S0@T0@U0@V0@W0@X0@Y0@Z0@[0@\0@]0@^0@_0@`0@a0@b0@c0@d0@e0@f0@g0@h0@i0@j0@k0@l0@m0@n0@o0A00A10A20A30A40A50A60A70A80A90A:0A;0A<0A=0A>0A?0A@0AA0AB0AC0AG0AH0A\0A]0A^0A_0A`0Aa0Ab0Ac0Ad0Ae0Af0Ag0Ah0Ai0Aj0Ak0Al0Am0An0Ao0B00B10B20B30B40B50B60B70B80B90B:0B;0B<0B=0B>0B?0B@0BA0BB0BC0BD0BE0BF0BG0BH0BI0BJ0BK0BL0BS0BT0BU0Bl0Bm0Bn0Bo0C00C10C20C30C40C50C60C70C80C90C:0C;0C<0C=0C>0C?0CD0CE0CF0CG0CH0CI0CJ0CK0CL0CM0CN0CO0CP0CQ0CR0CS0CT0CU0CV0CW0CX0CY0CZ0C[0C\0Cd0Ce0Cf0Cg0Ch0Ci0Cj0Ck0Cl0Cm0Cn0Co0D00D10D20D30D40D50D60D70D80D90D:0D;0D<0D=0D>0D?0D@0DA0DB0DC0DD0DE0DF0DG0DH0DI0DJ0DK0DL0DM0DN0DO0DP0DQ0DR0DS0DT0DU0DV0DW0DX0DY0DZ0D[0D\0D]0D^0D_0D`0Da0Db0Dc0Dd0De0Df0Dg0Dh0Di0Dj0Dk0Dl0Dm0Dn0Do0E00E10E20E30E40E50E60E70E80E90E:0E;0E?0E@0EA0EB0EC0ED0EE0EF0EG0EH0EI0EJ0EK0EL0EM0EN0EO0EP0EQ0E]0E^0E_0E`0Ea0Eb0Ec0Ed0Ee0Ei0Ej0Ek0El0Em0En0Eo0F00F10F20F30F40F50F60F70F80F90F:0F;0F<0F=0F>0F?0F@0FA0FB0FC0FD0FE0FF0FG0FH0FI0FJ0FK0FL0FM0FN0FO0FP0FQ0FR0FS0FT0FU0FV0FW0FX0FY0FZ0F^0F_0Fc0Fd0Fe0Ff0Fg0Fh0Fi0Fj0Fk0Fl0Fm0Fn0Fo0G00G10G20G30G40G50G60G70G80G90G:0G;0G?0G@0GA0GB0GC0GD0GE0GF0GG0GH0GI0GJ0GK0GL0GM0GN0GO0GP0GQ0GR0GS0GT0GU0GV0GW0GX0GY0G]0G^0G_0G`0Ga0Gb0Gc0Gd0Ge0Gf0Gg0Gh0Gi0Gj0Gk0Gl0Gm0Gn0Go0H00H10H20H30H40H50H60H70H80H90H:0H;0H<0H=0H>0H?0H@0HA0HB0HF0HG0HH0HI0HJ0HK0HL0HM0HN0HO0HP0HQ0H^0H_0H`0Ha0Hb0Hc0Hd0He0Hm0Hn0Ho0I00I10I20I30I40I50I60I70I80I90I:0I;0I<0I=0I>0I?0IH0II0IJ0IM0IN0IO0IP0IQ0IR0IS0IT0IU0IV0IW0IX0IY0IZ0I[0I\0I]0Ii0Ij0Ik0Il0Im0In0Io0J00J10J20J30J40J50J60J70J80J90J:0J;0J<0J=0J>0J?0J@0JA0JB0JC0JD0JE0JF0JG0JH0JI0JJ0JK0JL0JM0JN0JO0JP0JQ0JR0JS0JT0JU0JV0JW0JX0JY0JZ0J_0J`0Ja0Jf0Jg0Jh0Ji0Jj0Jk0Jl0Jm0Jn0Jo0K00K1SSSSSSSSSSS3RSPSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS2Hx3A16SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS1DSSSSSSSSSSSSSSSSS2RM2AMS2Q42RM2Q7SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS3WRB2WBSSSSSSSSSSSSSSSSSSSSSSSSSSSSS3RSP2HcSSSSSSSSSSS3WRB2WB3LENSSSSSS2E5SSSSSSSSSSSSSS2QSSSSSSSSSSSSSSSSSSSSS2ALSSSSSSSSSSS1HSSSSSSSSSSSS2E2SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS2Q13RI1SSSSSSSSSSSSSSSSSSSSSSSSSS2E3SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS3POSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS3POSSSSSSSSSSSSSSSSSFSSSSSSSSSSSSSSSSSSSSSSSS2Q6SSSSSSSSSSSSSSSSSSSSSSSSSSS2Q52Q63RI1SSSSSSSSSSSSSSSSSSSSSSSSSSSSS2Q23RI23RI3SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS2BSSSSSSSSSSSSSSSSSSSSSSSSSSS2Q2SSSSSSSS2Q6SSSSSSSSSSSSSSSSSSSSSSSSSS2Q12Q23RI23RI32P4SSSSSSSSSSSSSSSSSSSSSSS2H12H2SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS3POSSSSSSSSSSSSSSSSSSSSSSSSFSSSSSSSSS2Q12Q2SSSSSSSSSSSSSSSSSSSSSSSSSSSSS3RI1SSSSSSS2HcSSSSSSSSSSSSSS2XF3OFKSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS2E1SS3ORS3B1'3B2'2P43RI2SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS2Q52Q6SSS3B1'3B2'2P52P43RI13RI2SSSSSSSSSSSSSSSSSSSS3POSSSSSSSSSSSSSSSSSSSSSSSSSS3RI12P5SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS2HkSSSSSSSSSSSSSSSSSSS3RHI2P53RI1SSSSSSSSS2HcSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS2HcSS2X2SSSSSSSSSSSSSSSSSSSSSSSSS2E4SSSSSSSSSSSSSSSSSSSSSSSSSSS2RMSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS2H3SSSSSSSSSSSS2Ha2E12E22E3SSSSSSSS2Q13RI1SSSSSSSSSSSSSSSSSSS3RI23RI3SSS1HSSSSSSSSSSSSSSSSS2Q63RI23RI3SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS3POSSSS3RSPSSSSSSSSSSS".
assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W' A k) by (intros A k H1 Hk H2; apply P_rt; [exact Hk| clear -H1 H2; lia]).
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k) by (intros A k H1 Hk H2; apply P_rt; [exact Hk| clear -H1 H2; lia]).
  Local Ltac kimg := apply P_img; [clear; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia| clear; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia| aci_clear_tac].
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [kimg | apply Kctx; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; kimg. }
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
  { intros c Hc. destruct (CLS c Hc) as (REG & FARR & [SLOTS SUND] & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply P_rt; [clear; lia|]. do 5 right. left. unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; clear -Hc; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply (P_reg_hi c); [exact HcK| clear -Q5 Q6; lia| unfold afreearr, K_FREEARR_OFF in *; clear -Q1 Q2; lia| unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; clear -Q6; lia].
      + apply P_sh_res; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - split; [intros k Hk; apply (aslot_client c k HcK Hk); exact (SLOTS k Hk)|].
      eapply junk_frame; [exact SUND | exact MU | exact WM |]. intros POS. apply (P_reg_hi c); [exact HcK| clear -POS; lia| clear; lia| unfold K_FREEARR_OFF, K_REGION in *; clear -Q1 Q2; lia].
    - eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c k SAL HcK) as AL.
        split; [reflexivity|]. apply P_sh_res; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply P_sh_res; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split.
  { (* [comment removed for export] *)
    eapply (hq_frame _ AHI_laws L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched. apply Forall_forall. intros iv Hin.
      assert (D1 : disjoint_from W' (al_t L + 80) 128) by (apply Kt; clear; lia).
      assert (D2 : disjoint_from W' (AINSTANCE + 728) 256) by kimg.
      assert (D3 : disjoint_from W' 0xa2240 0x81030) by kimg.
      assert (D4 : disjoint_from W' 0x130ac8 4) by kimg.
      pose proof (disjoint_from_In _ _ _ _ D1 Hin) as E1. pose proof (disjoint_from_In _ _ _ _ D2 Hin) as E2.
      pose proof (disjoint_from_In _ _ _ _ D3 Hin) as E3. pose proof (disjoint_from_In _ _ _ _ D4 Hin) as E4.
      split; [clear -E1; lia|]. split; [clear -E2; lia|]. split; [clear -E3; lia|]. split; [clear -E4; lia|].
      intros b Hb. destruct (xb_st b) as [q| |] eqn:Sb; [exact I| |].
      all: destruct (BUSY b Hb) as [CLB _]; pose proof CLB as CLBK; unfold K_NUM_CLASSES in CLB;
           destruct (PERC (xb_class b) CLBK) as (B1' & B2' & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR);
           pose proof (size_of_class_facts (xb_class b) CLBK) as [BS _];
           assert (KB : 0 <= xb_slot b < ndist st (xb_class b)) by
             (apply BR; apply in_app_iff; right; apply in_app_iff; right; unfold busy_slots; apply in_map_iff; exists b; split; [reflexivity|];
              apply filter_In; split; [exact Hb| apply Z.eqb_refl]);
           assert (D5 : disjoint_from W' (xb_alloc L b) (size_of_class (xb_class b)));
           [ pose proof (aslot_client) as _;
             pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -BS; lia) (proj1 B1') KB) as (P5 & P4 & P0);
             assert (RI : al_res L <= aregion L (xb_class b) /\ aregion L (xb_class b) + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_REGION in *; clear -CLB RSP; nia);
             destruct RI as [RI1 RI2]; unfold K_REGION, K_FREEARR_OFF, xb_alloc in *;
             apply P_obj; [unfold sclr; right; clear -P5 RI1 RHI; lia| unfold iclr, AIMG_HI; split; [clear -P5 RI1 RHI; lia| right; clear -P5 RI1 RHI; lia]
                          | clear -BS; lia| atop_facts; clear -P4 B1' B2' RI2 ORS; lia| apply hb_clear_fake_obj; clear -P5 P4 B1' B2' RI1 RI2; lia|];
             intros p B n Hin'; destruct (slot_vs_blocks (xb_class b) (xb_slot b) p B n CLBK KB Hin') as [(b' & EB & Sb' & _)|D]; [| clear -D; lia];
             rewrite (busy_of_of_In L st X b WF Hb) in EB; injection EB as <-; rewrite Sb in Sb'; discriminate
           | pose proof (disjoint_from_In _ _ _ _ D5 Hin) as E5; clear -E5; lia ].
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { (* [comment removed for export] *)
    cbn [AHI ah_sec] in HS |- *. unfold ASEC_of in *. pose proof HS as (WFS & ARR & INST2 & PZ & SHZ).
    pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
    split; [exact WFS|]. split; [| split; [| split]].
    - destruct ARR as (order & PO & U64 & JK & PER). exists order. split; [exact PO|].
      assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL). destruct WR as [_ WRB].
      split; [| split].
      + destruct order as [|o0 order'].
        * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
        * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply P_rt; [clear; cbn; lia|]. do 4 right. left. cbn [length] in LEN |- *. clear -LEN WB WRB; lia.
      + eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply P_rt; [clear -POS; lia|]. do 4 right. left. clear -POS WB WRB; lia.
      + intros i ch Hi. destruct (PER i ch Hi) as (lv & LV2 & CH).
        assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        destruct (asec_wf_all L st _ ch WFS Hin) as (mb & ms & n0 & -> & W1).
        exists lv. split; [exact LV2|]. eapply asec_chunk_client; [exact Hin| exact W1| exact LV2| exact CH].
    - destruct INST2 as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; kimg]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; kimg]|].
      split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; kimg]|].
      split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; kimg]|].
      split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; kimg]|].
      eapply junk_frame; [exact I6| exact MU| exact WM| intros _; kimg].
    - unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
      apply P_sh_res; [apply shad_mono; clear -RSP; lia| clear -POS; lia|].
      replace (shlen K_REGION) with 536870912 by reflexivity. rewrite !shad_div. clear -RSP. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - intros x Hx HF HC. unfold K_HIGH_MEM in Hx.
      assert (SX : 0 <= shad x < 2^64 /\ 2148232192 <= shad x /\ shad x + 1 <= shad ATOP).   (* [comment removed for export] *)
      { rewrite !shad_div. pose proof ATOP_al16 as A16. unfold ASHOFF, AIMG_HI, KLS in *. clear -Hx A16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      destruct SX as (SX & SX1 & SX2).
      assert (XF : x < al_fake L \/ al_fake L + 11571200 <= x).
      { unfold astartup_hulls in HF. repeat lazymatch type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF; destruct HF as [? HF] | _ => idtac end.
        cbn [fst snd] in *. clear -H3. lia. }
      rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside W' (shad x) 1); [| clear; lia]. apply P_sh; [exact SX1| clear; lia| exact SX2|].
      pose proof (ao_fake L ALO) as OFK. unfold aobj in OFK. rewrite !shad_div. clear -XF OFK. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  split.
  { cbn [AHI ah_depot]. eapply (adi_frame adepot_iface); [exact HD | exact MU | exact WM |].
    assert (DD : disjoint_from W' 0x172f08 (0x5c2f50 - 0x172f08)).
    { apply P_img; [clear; lia| clear; lia|]. unfold aci_clear. eapply Forall_impl; [| exact aci_ok]. cbv beta. intros iv (_ & X2 & _). clear -X2. lia. }
    assert (DN : disjoint_from W' (al_nodes L) 1048576) by (apply P_rt; [clear; lia| clear; lia]).
    assert (DS : disjoint_from W' (al_store L) 8388608) by (apply P_rt; [clear; lia| clear; lia]).
    apply Forall_forall. intros iv Hin a Ha.
    pose proof (disjoint_from_In _ _ _ _ DD Hin) as E1. pose proof (disjoint_from_In _ _ _ _ DN Hin) as E2. pose proof (disjoint_from_In _ _ _ _ DS Hin) as E3.
    clear -E1 E2 E3 Ha. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | kimg]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; kimg|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; kimg |]); apply Forall_nil].
  intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c HcK) | reflexivity | reflexivity | |].
  - intros POS. apply P_sh_res; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply P_sh_res; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ClientW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem AHI_frame : forall L RNG st LB m m' (W : list ivl),
  AHEAP_I L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
  AHEAP_I L RNG st LB m'.
Proof.
  intros L RNG st LB m m' W (ALO & ARNG & [X [AR BL]] & HFK) MU WM CW. cbn [AHI ah_fake] in HFK.
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [eapply AREP_client; eauto| exact BL].
  - cbn [AHI ah_fake]. eapply afake_client; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma aci_okQ : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                           /\ (snd iv <= 0x9dcb0 \/ 0x9dd70 <= fst iv)
                           /\ (snd iv <= 0xa2240 \/ 0x123270 <= fst iv)
                           /\ (snd iv <= 0x130ac8 \/ 0x130acc <= fst iv)) aci_I.
Proof. unfold aci_I, drv_img_ranges, cli_img_ranges, AIMG_HI. Local Ltac2 Set LiaHints.tbl := fun () => "00D0=14698236380.115316680540.117138709468.118366944988.119890978524.127524125148.131505310684.132717293276.133945626076.135157215452.135776052828.139138400988.142488592220.144933232988.145543190236.153492943580.157457349852.162646322652.167530846684.17985197276.1 00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00DSSSSSSSSSSSSSSSSSSSS".
repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Theorem AHI_malloc : amalloc_stmt aci_I AHEAP_I.
Proof. exact (amalloc_all adepot_iface AQUAR AFAKE AH_laws poison_remap_proof aci_I aci_ok aci_ok2). Qed.

#[using="Type"] Theorem AHI_free_null : afree_null_stmt aci_I AHEAP_I.
Proof. exact (afree_nullP adepot_iface ASEC_of AFAKE AH_laws aci_I aci_okQ). Qed.

Definition AI_of (FREE : afree_stmt aci_I AHEAP_I) : AMallocIface :=
  {| aci := aci_I;
     AHEAP := AHEAP_I;
     AI_aci_img := aci_img;
     AI_aci_lo := aci_lo;
     AI_rng_mono := AHI_rng_mono;
     AI_perm := AHI_perm;
     AI_frame := AHI_frame;
     AI_block := AHI_block;
     AI_block_bounds := AHI_block_bounds;
     AI_blocks_disjoint := AHI_blocks_disjoint;
     AI_blocks_nodup := AHI_blocks_nodup;
     AI_hb_ids := AHI_hb_ids;
     AI_layout := AHI_layout;
     AI_relro := AHI_relro;
     AI_rtcells := AHI_rtcells;
     AI_malloc := AHI_malloc;
     AI_free := FREE;
     AI_free_null := AHI_free_null |}.

(* [comment removed for export] *)
#[using="Type"] Lemma AI_of_E : forall FREE, AHEAP (AI_of FREE) = AHEAP_P AHI.
Proof. reflexivity. Qed.
#[using="Type"] Lemma AI_of_CI_OK : forall FREE iv, In iv (aci (AI_of FREE)) -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Proof. intros FREE iv H. exact (aci_ok1 iv H). Qed.
#[using="Type"] Lemma AI_of_DRV_CI : forall FREE iv, In iv drv_img_ranges -> In iv (aci (AI_of FREE)).
Proof. intros FREE iv H. exact (drv_aci iv H). Qed.
#[using="Type"] Lemma AI_of_CLI_CI : forall FREE iv, In iv cli_img_ranges -> In iv (aci (AI_of FREE)).
Proof. intros FREE iv H. exact (uri_aci iv H). Qed.
#[using="Type"] Lemma AI_of_chunk : forall FREE L RNG st LB m p A n, AHEAP (AI_of FREE) L RNG st LB m -> In (HB p A n) LB ->
  exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
Proof. intros FREE. exact AHI_chunk. Qed.
#[using="Type"] Lemma AI_of_premap : forall FREE L RNG st LB m, AHEAP (AI_of FREE) L RNG st LB m -> premap_cells m.
Proof. intros FREE. exact AHI_premap. Qed.
End CANSEC2.
