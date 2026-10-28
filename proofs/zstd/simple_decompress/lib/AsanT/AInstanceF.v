(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes ACanary ARep ARepKit ARepFrame ALayout AHeapP ARepExt
     AMalloc_iface ADepot_iface APoisonR_iface AQConst ARepQ ARepQP ASec ASecFacts ASecFrame ASecStore FsKit
     F_adepot AFake_iface AFake_arep AInstance AFreeGeo AFreeRead ADriver_iface F_afree_arep AFreeNull F_apoison_remap AMalloc AInstanceM.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
Lemma junk_any : forall m m' A n, junk_at m A n -> wmono bsegs m m' -> 0x625000 <= A -> junk_at m' A n.
Proof. intros m m' A n H WM HA. exact (dc_at_any m m' A n H WM HA). Qed.

(* [comment removed for export] *)
Lemma aobj_sub_sclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> sclr A k.
Proof. intros a n A k (_ & _ & _ & HS & _) H1 H2. unfold sclr in *. lia. Qed.
Lemma aobj_sub_iclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> iclr A k.
Proof. intros a n A k (_ & HG & _ & _ & HI) H1 H2. unfold iclr in *. lia. Qed.

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
Lemma hb_where : forall p B n, In (HB p B n) LB ->
  (exists c, 1 <= c < K_NUM_CLASSES /\ aregion L c <= B /\ B + n <= aregion L c + c_allocated_user (get_cls st c)
             /\ c_allocated_user (get_cls st c) <= K_FREEARR_OFF /\ 1 <= n)
  \/ (exists mb ms, B = mb + 6144 /\ 1 <= n /\ n + 6144 <= ms /\ sec_wf1 L (CSec mb ms n)).
Proof.
  intros p B n Hin.
  destruct (hb_cases L st X LB m p B n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - left. exists (xb_class b). destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). destruct (PERC _ CLB) as (A1 & A2 & _).
    pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user in *.
    split; [exact CLB|]. split; [clear -P5 RZ; lia|]. split; [clear -P4 FIT RG; lia|]. split; [unfold K_FREEARR_OFF in *; clear -A1 A2; lia| clear -NB; lia].
  - right. exists mb, ms. pose proof G as G0. cbn [sec_wf1] in G0. destruct G0 as (_ & _ & _ & G4 & G5 & G6 & _).
    pose proof (sec_facts n ltac:(clear -G5; lia) G6) as (_ & _ & _ & RSR & _ & NSE & _ & MSR & _). rewrite <- G4 in MSR.
    split; [exact EA|]. split; [clear -G5; lia|]. split; [clear -RSR NSE MSR; lia| exact G].
Qed.

(* [comment removed for export] *)
Lemma P_img : forall A k, 0 <= k -> A + k <= 0x625000 -> aci_clear A k -> disjoint_from W' A k.
Proof.
  intros A k Hk HA CLR. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.   (* [comment removed for export] *)
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
Qed.

(* [comment removed for export] *)
Lemma P_obj : forall A k, sclr A k -> iclr A k -> 0 <= k -> A + k <= ATOP ->
  (A + k <= al_fake L \/ al_fake L + 11571200 <= A) ->
  (forall p B n, In (HB p B n) LB -> A + k <= B \/ B + n <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k HS HI Hk HC HF HB. unfold sclr, KLS in HS. unfold iclr, AIMG_LO, AIMG_HI in HI. destruct HI as [HA HI].
  subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
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
Qed.

(* [comment removed for export] *)
Lemma P_sh : forall A k, 2148256256 <= A -> 0 <= k -> A + k <= shad ATOP ->
  (A + k <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k HA Hk HC HF.
  assert (HC2 : A + k <= 17594332446720 /\ 8 * (A + k) <= ATOP + 8 * ASHOFF).
  { rewrite shad_div in HC. pose proof ATOP_al16 as A16. unfold ASHOFF in *. clear -HC A16. Z.div_mod_to_equations. lia. }
  clear HC. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
  pose proof OFK as (_ & _ & _ & OFKS & _). unfold sclr, KLS in OFKS.
  pose proof (ao_stack L ALO) as (_ & _ & S47 & SB). unfold aobj in *.
  assert (SF : shad (al_fake L) = al_fake L / 8 + ASHOFF /\ shad (al_fake L + 11571200) = al_fake L / 8 + 1446400 + ASHOFF).
  { rewrite !shad_div. clear -OFK. Z.div_mod_to_equations. lia. }
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
  - destruct (afake_lb L LB m cls FA fn HFK Hf) as (_ & _ & _ & _ & K5 & K6 & _). unfold FAKESZ in K6. clear -K5 K6 F1 F2 SF1 SF2 HF NEV Hk. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma hb_prim_span : forall p B n c,
  In (HB p B n) LB -> 1 <= c < K_NUM_CLASSES -> aregion L c <= B -> B + n <= aregion L c + c_allocated_user (get_cls st c) ->
  al_space_beg L + K_REGION <= B /\ B + n <= al_space_beg L + K_SPACE_SIZE /\ B + n <= aregion L c + K_FREEARR_OFF.
Proof.
  intros p B n c Hin Hc Q1 Q2. destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). destruct (PERC c Hc) as (A1 & A2 & _).
  unfold aregion, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. change (2^37) with 137438953472. clear -Hc Q1 Q2 A1 A2. nia.
Qed.

(* [comment removed for export] *)
Lemma hb_clear_obj : forall A k,
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
    clear -HR S1 S2 D_t_res D_c_res D_n_res D_s_res D_p_res RSP ORS. lia.
  - cbn [sec_wf1] in Q3. destruct Q3 as (_ & _ & _ & _ & _ & _ & (Ct & Cc & Cr & Cp & Cn & Cs & _)).
    unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    clear -HR Ct Cc Cr Cp Cn Cs RSP ORS Q2. lia.
Qed.

Lemma hb_clear_fake_obj : forall A k,
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_res L <= A /\ A + k <= al_res L + 137439023104)) ->
  A + k <= al_fake L \/ al_fake L + 11571200 <= A.
Proof.
  intros A k HR.
  pose proof (ad_t_fake L ALO) as D1. pose proof (ad_ctx_fake L ALO) as D2. pose proof (ad_nodes_fake L ALO) as D3.
  pose proof (ad_store_fake L ALO) as D4. pose proof (ad_fake_ptr L ALO) as D5. pose proof (ad_fake_res L ALO) as D6. unfold adisj in *.
  clear -HR D1 D2 D3 D4 D5 D6. lia.
Qed.

(* [comment removed for export] *)
Lemma P_rt : forall A k, 0 <= k ->
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
Qed.

(* [comment removed for export] *)
Lemma P_reg_hi : forall c A k, 1 <= c < K_NUM_CLASSES -> 0 <= k ->
  aregion L c + c_allocated_user (get_cls st c) <= A -> A + k <= aregion L c + K_REGION -> disjoint_from W' A k.
Proof.
  intros c A k Hc Hk H1 H2.
  pose proof (ao_res L ALO) as ORS. pose proof (ao_space L ALO) as RSP. unfold aobj in *.
  destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). destruct (PERC c Hc) as (A1 & A2 & _).
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104).
  { unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Hc RSP. nia. }
  destruct RI as [RI1 RI2]. unfold K_REGION in *. pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  apply P_obj; [unfold sclr; right; clear -H1 RI1 RHI A1; lia| unfold iclr, AIMG_HI; split; [clear -H1 RI1 RHI A1; lia| right; clear -H1 RI1 RHI A1; lia]
               | exact Hk| atop_facts; clear -H2 RI2 ORS; lia| apply hb_clear_fake_obj; clear -H1 H2 RI1 RI2 A1; lia|].
  intros p B n Hin. destruct (hb_where p B n Hin) as [(c' & Hc' & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - destruct (Z.eq_dec c' c) as [->|NE]; [clear -Q2 H1; lia|].
    destruct (Z.lt_ge_cases c' c) as [LT|GE].
    + right. pose proof (regions_sep L c' c LT) as RS. unfold K_REGION, K_FREEARR_OFF in *. clear -RS Q2 Q3 H1 A1. lia.
    + left. pose proof (regions_sep L c c' ltac:(clear -GE NE; lia)) as RS. unfold K_REGION in *. clear -RS Q1 H2. lia.
  - cbn [sec_wf1] in Q3. destruct Q3 as (_ & _ & _ & _ & _ & _ & (_ & _ & Cr & _)). clear -Cr RI1 RI2 H1 H2 Q2 A1. lia.
Qed.

(* [comment removed for export] *)
Lemma slot_vs_blocks : forall c k p B n, 1 <= c < K_NUM_CLASSES -> 0 <= k < ndist st c -> In (HB p B n) LB ->
  (exists b, busy_of X c k = Some b /\ xb_st b = BLive p /\ B = xb_user L b /\ n = xb_n b)
  \/ (B + n <= aslot_addr L c k \/ aslot_addr L c k + size_of_class c <= B).
Proof.
  intros c k p B n Hc Hk Hin.
  pose proof AR as (WF & _). pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  pose proof (size_of_class_facts c Hc) as [QS _]. destruct (PERC c Hc) as (A1 & A2 & _).
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
Qed.

(* [comment removed for export] *)
Lemma disjoint_from_In : forall (Wx : list (Z * Z)) A k iv, disjoint_from Wx A k -> In iv Wx -> A + k <= fst iv \/ snd iv <= A.
Proof.
  intros Wx A k iv. induction Wx as [|[lo hi] Wx IH]; intros D Hin; [destruct Hin|].
  cbn in D. destruct D as [D1 D2]. destruct Hin as [<-|Hin]; [cbn; lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma P_sh_res : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof.
  intros A k H1 Hk H2. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ad_fake_res L ALO) as D. pose proof (ao_res_hi L ALO) as RHI. unfold aobj, adisj in *.
  assert (SR : 2148256256 <= shad (al_res L) /\ shad (al_res L + 137439023104) <= shad ATOP   (* [comment removed for export] *)
               /\ (shad (al_res L + 137439023104) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad (al_res L))).
  { rewrite !shad_div. unfold ASHOFF. clear -ORS OFK D RHI. Z.div_mod_to_equations. lia. }
  apply P_sh; clear -SR H1 Hk H2; lia.
Qed.

Lemma P_dtls : forall A k, al_dtls L <= A -> 0 <= k -> A + k <= al_dtls L + 4096 -> disjoint_from W' A k.
Proof.
  intros A k H1 Hk H2.
  pose proof (ao_dtls L ALO) as OD. pose proof (ad_fake_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  unfold aobj, adisj in *.
  apply P_obj; [exact (aobj_sub_sclr _ _ A k (ao_dtls L ALO) H1 H2)| exact (aobj_sub_iclr _ _ A k (ao_dtls L ALO) H1 H2)| exact Hk| clear -H2 OD; lia| clear -H1 H2 D1; lia|].   (* [comment removed for export] *)
  intros p B n Hin. destruct (hb_where p B n Hin) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - pose proof (hb_prim_span p B n c Hin Hc Q1 Q2) as (S1 & S2 & S3). unfold K_REGION, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    clear -H1 H2 S1 S2 D2 RSP ORS. lia.
  - cbn [sec_wf1] in Q3. destruct Q3 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Cd)). clear -H1 H2 Cd Q2. lia.
Qed.

(* [comment removed for export] *)
Lemma P_fakehdr : disjoint_from W' (al_fake L) 36864.
Proof.
  subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.   (* [comment removed for export] *)
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
Qed.

(* [comment removed for export] *)
Lemma aslot_client : forall c k, 1 <= c < K_NUM_CLASSES -> 0 <= k < ndist st c ->
  match busy_of X c k with None => junk_at m (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m b end ->
  match busy_of X c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end.
Proof.
  intros c k Hc Hk SL.
  pose proof AR as (WF & _). pose proof (size_of_class_facts c Hc) as [QS _].
  pose proof WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC c Hc) as (A1 & A2 & _).
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
Qed.

(* [comment removed for export] *)
Lemma asec_chunk_client : forall mb ms n idx lv,
  In (CSec mb ms n) (sec_chunks_of st) -> sec_wf1 L (CSec mb ms n) ->
  (lv = true <-> sec_live st (CSec mb ms n)) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros mb ms n idx lv INC WF1 LVE CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & GC). pose proof GC as (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd).
  pose proof (sec_facts n ltac:(clear -G5; lia) G6) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- G4 in MSR, MSM, MSB.
  pose proof AR as (WF & _ & _ & _ & _ & _ & HS & _). cbn [AHI ah_sec] in HS. unfold ASEC_of in HS. pose proof HS as ((_ & _ & _ & _ & _ & WFA & [ND PW]) & _).
  pose proof (ao_fake L ALO) as OFK. unfold aobj in OFK. unfold K_HIGH_MEM in *.
  pose proof (ablk_lin _ _ G2) as (G2a & G2b & _ & _).   (* [comment removed for export] *)
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8 /\ 2148256256 <= shad mb /\ shad mb + ms / 8 <= shad ATOP
               /\ (shad mb + ms / 8 <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad mb)).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. unfold ASHOFF, AIMG_HI in *. clear -G1 G2a G2b G3 G5 RSR NSE MSR MSM Cf OFK. Z.div_mod_to_equations. lia. }
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
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DSH; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DSH; clear -GR3 GR1 POS; lia].
Qed.

(* [comment removed for export] *)
Lemma afake_client : AFAKE L LB m'.
Proof.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *.
  pose proof (ablk_lin _ _ G2) as (G2a & G2b & G2c & G2d). unfold AIMG_HI in G2a.   (* [comment removed for export] *)
  pose proof P_fakehdr as DF.
  split; [exact G|].
  split.
  { destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold afake_cells.
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
  split. { eapply dc_at_any; [exact DC2| exact WM|]. rewrite shad_div. unfold ASHOFF. clear -G2a G2b. Z.div_mod_to_equations; lia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    rewrite (munch_outside_range W' m m' (al_fake L) 36864) in Hb; [eapply FL; eauto| exact MU| exact DF| clear -FR; lia| clear -FR G2a G2c G3; lia].
  - intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    rewrite (munch_outside_range W' m m' (al_fake L) 36864); [exact Hb| exact MU| exact DF| clear -FR; lia| clear -FR G2a G2c G3; lia].
Qed.

(* [comment removed for export] *)
Theorem AREP_client : AREP AHI L st X m'.
Proof.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_ptr L ALO) as OP.
  pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  unfold aobj in ORS, OT, OC, ON, OS, OP.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
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
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - split; [intros k Hk; apply (aslot_client c k HcK Hk); exact (SLOTS k Hk)|].
      eapply junk_frame; [exact SUND | exact MU | exact WM |]. intros POS. apply (P_reg_hi c); [exact HcK| clear -POS; lia| clear; lia| unfold K_FREEARR_OFF, K_REGION in *; clear -Q1 Q2; lia].
    - eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c k SAL HcK) as AL.
        split; [reflexivity|]. apply P_sh_res; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply P_sh_res; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split.
  { (* [comment removed for export] *)
    eapply (hq_frame _ AHI_laws L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched. apply Forall_forall. intros iv Hin.
      assert (D1 : disjoint_from W' (al_t L + 80) 128) by (apply Kt; clear; lia).
      assert (D2 : disjoint_from W' (AINSTANCE + 728) 256) by kimg.
      assert (D3 : disjoint_from W' 0xd0f00 0x81030) by kimg.
      assert (D4 : disjoint_from W' 0x15f788 4) by kimg.
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
      replace (shlen K_REGION) with 536870912 by reflexivity. rewrite !shad_div. clear -RSP. Z.div_mod_to_equations. lia.
    - intros x Hx HF HC. unfold K_HIGH_MEM in Hx.
      assert (SX : 0 <= shad x < 2^64 /\ 2148256256 <= shad x /\ shad x + 1 <= shad ATOP).   (* [comment removed for export] *)
      { rewrite !shad_div. pose proof ATOP_al16 as A16. unfold ASHOFF, AIMG_HI, KLS in *. clear -Hx A16. Z.div_mod_to_equations. lia. }
      destruct SX as (SX & SX1 & SX2).
      assert (XF : x < al_fake L \/ al_fake L + 11571200 <= x).
      { unfold astartup_hulls in HF. repeat lazymatch type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF; destruct HF as [? HF] | _ => idtac end.
        cbn [fst snd] in *. clear -H3. lia. }
      rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside W' (shad x) 1); [| clear; lia]. apply P_sh; [exact SX1| clear; lia| exact SX2|].
      pose proof (ao_fake L ALO) as OFK. unfold aobj in OFK. rewrite !shad_div. clear -XF OFK. Z.div_mod_to_equations. lia. }
  split.
  { cbn [AHI ah_depot]. eapply (adi_frame adepot_iface); [exact HD | exact MU | exact WM |].
    assert (DD : disjoint_from W' 0x1a1bc8 (0x5f1c10 - 0x1a1bc8)).
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
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply P_sh_res; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End ClientW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem AHI_frame : forall L RNG st LB m m' (W : list ivl),
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
Lemma aci_okQ : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                           /\ (snd iv <= 0xcc970 \/ 0xcca30 <= fst iv)
                           /\ (snd iv <= 0xd0f00 \/ 0x151f30 <= fst iv)
                           /\ (snd iv <= 0x15f788 \/ 0x15f78c <= fst iv)) aci_I.
Proof. unfold aci_I, drv_img_ranges, cli_img_ranges, AIMG_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

Theorem AHI_malloc : amalloc_stmt aci_I AHEAP_I.
Proof. exact (amalloc_all adepot_iface AQUAR AFAKE AH_laws poison_remap_proof aci_I aci_ok aci_ok2). Qed.

Theorem AHI_free_null : afree_null_stmt aci_I AHEAP_I.
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
Lemma AI_of_E : forall FREE, AHEAP (AI_of FREE) = AHEAP_P AHI.
Proof. reflexivity. Qed.
Lemma AI_of_CI_OK : forall FREE iv, In iv (aci (AI_of FREE)) -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Proof. intros FREE iv H. exact (aci_ok1 iv H). Qed.
Lemma AI_of_DRV_CI : forall FREE iv, In iv drv_img_ranges -> In iv (aci (AI_of FREE)).
Proof. intros FREE iv H. exact (drv_aci iv H). Qed.
Lemma AI_of_CLI_CI : forall FREE iv, In iv cli_img_ranges -> In iv (aci (AI_of FREE)).
Proof. intros FREE iv H. exact (uri_aci iv H). Qed.
Lemma AI_of_chunk : forall FREE L RNG st LB m p A n, AHEAP (AI_of FREE) L RNG st LB m -> In (HB p A n) LB ->
  exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
Proof. intros FREE. exact AHI_chunk. Qed.
Lemma AI_of_premap : forall FREE L RNG st LB m, AHEAP (AI_of FREE) L RNG st LB m -> premap_cells m.
Proof. intros FREE. exact AHI_premap. Qed.
End CANSEC2.
