(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg AProto ABase ABytes ARep ARepKit ARepFrame ALayout AHeapP ARepQ ARepQP
     ASec ASecFacts ASecFrame ADepot ADepot_iface F_adepot AFake_iface AFake_arep AInstance AFreeGeo AMalloc_iface ALoose ALooseInst.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition upd_pat (pat : aptr -> option (list byte)) (p : aptr) (e : option (list byte)) : aptr -> option (list byte) :=
  fun q => if N.eqb q p then e else pat q.
Definition upd_spat (spat : Z -> option (list byte)) (mb : Z) (e : option (list byte)) : Z -> option (list byte) :=
  fun x => if Z.eqb x mb then e else spat x.
Lemma upd_pat_eq : forall pat p e, upd_pat pat p e p = e.
Proof. intros. unfold upd_pat. rewrite N.eqb_refl. reflexivity. Qed.
Lemma upd_pat_ne : forall pat p e q, q <> p -> upd_pat pat p e q = pat q.
Proof. intros pat p e q NE. unfold upd_pat. destruct (N.eqb_spec q p); [contradiction| reflexivity]. Qed.
Lemma upd_spat_eq : forall spat mb e, upd_spat spat mb e mb = e.
Proof. intros. unfold upd_spat. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma upd_spat_ne : forall spat mb e x, x <> mb -> upd_spat spat mb e x = spat x.
Proof. intros spat mb e x NE. unfold upd_spat. destruct (Z.eqb_spec x mb); [contradiction| reflexivity]. Qed.

(* [comment removed for export] *)
Definition set_pat1 (L : alayout) (p : aptr) (e : option (list byte)) : alayout := remapL L (upd_pat (al_pat L) p e) (al_spat L).
Definition set_spat1 (L : alayout) (mb : Z) (e : option (list byte)) : alayout := remapL L (al_pat L) (upd_spat (al_spat L) mb e).
(* [comment removed for export] *)
Definition set_blk (L : alayout) (p : aptr) (A n : Z) (e : option (list byte)) : alayout :=
  if is_primary n then set_pat1 L p e else set_spat1 L (A - SEC_UOFF) e.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_CB_iff : forall m A n bs,
  rw_cells asegs m A [CB n bs] <-> (length bs = n /\ bytes_at asegs m A bs /\ wr_at asegs m A (Z.of_nat n)).
Proof.
  intros. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma nth_error_patch : forall {T} (bs bs2 : list T) k i,
  (k + length bs2 <= length bs)%nat ->
  nth_error (firstn k bs ++ bs2 ++ skipn (k + length bs2) bs) i =
    if (i <? k)%nat then nth_error bs i else if (i <? k + length bs2)%nat then nth_error bs2 (i - k) else nth_error bs i.
Proof.
  intros T bs bs2 k i LE.
  assert (LF : length (firstn k bs) = k) by (rewrite length_firstn; lia).
  destruct (Nat.ltb_spec i k) as [H1|H1].
  - rewrite nth_error_app1 by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec i k); [reflexivity| lia].
  - rewrite nth_error_app2 by lia. rewrite LF. destruct (Nat.ltb_spec i (k + length bs2)) as [H2|H2].
    + rewrite nth_error_app1 by lia. reflexivity.
    + rewrite nth_error_app2 by lia. rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma length_patch : forall {T} (bs bs2 : list T) k,
  (k + length bs2 <= length bs)%nat -> length (firstn k bs ++ bs2 ++ skipn (k + length bs2) bs) = length bs.
Proof. intros T bs bs2 k LE. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

(* [comment removed for export] *)
Lemma rw_cells_patch : forall (W : list (Z * Z)) m m' A n bs A2 bs2,
  rw_cells asegs m A [CB n bs] ->
  munch W m m' -> wmono asegs m m' ->
  (forall x, A <= x < A + Z.of_nat n -> ~ (A2 <= x < A2 + Z.of_nat (length bs2)) -> outside W x) ->
  rw_cells asegs m' A2 [CB (length bs2) bs2] ->
  A <= A2 -> A2 + Z.of_nat (length bs2) <= A + Z.of_nat n ->
  rw_cells asegs m' A [CB n (firstn (Z.to_nat (A2 - A)) bs ++ bs2 ++ skipn (Z.to_nat (A2 - A) + length bs2) bs)].
Proof.
  intros W m m' A n bs A2 bs2 OLD MU WM OUT NEW H1 H2.
  apply rw_cells_CB_iff in OLD. apply rw_cells_CB_iff in NEW. destruct OLD as (LO & (B0 & B1 & BR) & WO). destruct NEW as (_ & (N0 & N1 & NR) & _).
  apply rw_cells_CB_iff. set (k := Z.to_nat (A2 - A)).
  assert (LE : (k + length bs2 <= length bs)%nat) by (subst k; lia).
  split; [rewrite (length_patch bs bs2 k LE); exact LO|]. split; [| eapply wr_at_transport; [exact WO| exact WM]].
  unfold bytes_at. rewrite (length_patch bs bs2 k LE). split; [exact B0|]. split; [exact B1|].
  intros i Hi. rewrite (nth_error_patch bs bs2 k i LE).
  destruct (Nat.ltb_spec i k) as [I1|I1]; [| destruct (Nat.ltb_spec i (k + length bs2)) as [I2|I2]].
  - rewrite <- (BR i Hi). unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. apply OUT; subst k; lia.
  - replace (A + Z.of_nat i) with (A2 + Z.of_nat (i - k)) by (subst k; lia). apply NR. lia.
  - rewrite <- (BR i Hi). unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. apply OUT; subst k; lia.
Qed.

Lemma fit_pat_exact : forall g bs, length bs = g -> fit_pat g bs = bs.
Proof. intros g bs E. unfold fit_pat. rewrite firstn_app, <- E, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

(* [comment removed for export] *)
Lemma ssb_upd_other : forall pat p e S ob,
  (forall b, ob = Some b -> xb_st b <> BLive p) ->
  slot_shadow_bytes (upd_pat pat p e) S ob = slot_shadow_bytes pat S ob.
Proof.
  intros pat p e S [b|] H; [| reflexivity]. specialize (H b eq_refl). unfold slot_shadow_bytes.
  destruct (xb_st b) as [q| |] eqn:E; [| reflexivity| reflexivity].
  rewrite upd_pat_ne; [reflexivity|]. intros ->. exact (H eq_refl).
Qed.

(* [comment removed for export] *)
Lemma shad_apart : forall UB g A k, UB mod 8 = 0 -> A mod 8 = 0 -> 0 <= A -> 0 <= UB -> 0 <= k -> 0 <= g ->
  (A + k <= UB \/ UB + 8 * g <= A) -> shad A + shlen k <= shad UB \/ shad UB + g <= shad A.
Proof.
  intros UB g A k U8 A8 A0 U0 K0 G0 [H|H].
  - left. apply shad_sep; assumption.
  - right. rewrite !shad_div. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

Lemma quar_same_refl : forall st X, quar_same st st X X.
Proof.
  intros st X. unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb].
Qed.

Lemma l_nodup_map_inj : forall {A B} (f : A -> B) (l : list A) x y,
  List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | |].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma l_busy_of_of_In : forall L st X b, awf L st X -> In b (x_busy X) -> busy_of X (xb_class b) (xb_slot b) = Some b.
Proof.
  intros L st X b WF Hb. pose proof WF as (_ & _ & _ & _ & _ & PERC & _ & BUSY & _).
  destruct (BUSY b Hb) as [CLB _]. destruct (PERC (xb_class b) CLB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
  apply List.NoDup_app_remove_l in ND. apply List.NoDup_app_remove_l in ND. unfold busy_slots in ND.
  unfold busy_of. destruct (List.find (fun b0 => (xb_class b0 =? xb_class b) && (xb_slot b0 =? xb_slot b)) (x_busy X)) as [b'|] eqn:E.
  - apply find_some in E. destruct E as [HIn HP]. apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
    f_equal. apply (l_nodup_map_inj xb_slot (List.filter (fun x => xb_class x =? xb_class b) (x_busy X)) b' b ND).
    + apply List.filter_In. split; [exact HIn| rewrite HP1; apply Z.eqb_refl].
    + apply List.filter_In. split; [exact Hb| apply Z.eqb_refl].
    + exact HP2.
  - exfalso. pose proof (find_none _ _ E b Hb) as F. cbn beta in F. rewrite !Z.eqb_refl in F. discriminate.
Qed.

Section PrimSet.
Variables (L : alayout) (st : astate) (X : aconc) (m m' : amem) (b0 : xbusy) (p : aptr) (e : option (list byte)).
Hypothesis ALO : alayout_ok L.
Hypothesis AR : AREP AHL L st X m.
Hypothesis Hb0 : In b0 (x_busy X).
Hypothesis Sb0 : xb_st b0 = BLive p.
Local Notation c0 := (xb_class b0).
Local Notation k0 := (xb_slot b0).
Local Notation n0 := (xb_n b0).
Local Notation AB := (xb_alloc L b0).
Local Notation UB := (xb_user L b0).
Local Notation g := (granules (xb_n b0)).
Local Notation W := [(shad (xb_user L b0), shad (xb_user L b0) + granules (xb_n b0))].
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis NEW : rw_cells asegs m' (shad UB) [CB (Z.to_nat g) (live_pat e n0)].
Local Notation L' := (set_pat1 L p e).

(* [comment removed for export] *)
Lemma L'_aslot_addr : forall c k, aslot_addr L' c k = aslot_addr L c k. Proof. reflexivity. Qed.
Lemma L'_aregion : forall c, aregion L' c = aregion L c. Proof. reflexivity. Qed.
Lemma L'_afreearr : forall c, afreearr L' c = afreearr L c. Proof. reflexivity. Qed.
Lemma L'_aregion_info : forall c, aregion_info L' c = aregion_info L c. Proof. reflexivity. Qed.
Lemma L'_acache_addr : forall c, acache_addr L' c = acache_addr L c. Proof. reflexivity. Qed.
Lemma L'_xb_alloc : forall b, xb_alloc L' b = xb_alloc L b. Proof. reflexivity. Qed.
Lemma L'_xb_user : forall b, xb_user L' b = xb_user L b. Proof. reflexivity. Qed.
Lemma L'_awf : forall s Y, awf L' s Y = awf L s Y. Proof. reflexivity. Qed.
Lemma L'_arep_rt : forall mx, arep_rt L' mx = arep_rt L mx. Proof. reflexivity. Qed.
Lemma L'_ainstance : forall s mx, ainstance L' s mx = ainstance L s mx. Proof. reflexivity. Qed.
Lemma L'_athread : forall s Y mx, athread L' s Y mx = athread L s Y mx. Proof. reflexivity. Qed.
Lemma L'_aregion_cells : forall s mx c, aregion_cells L' s mx c = aregion_cells L s mx c. Proof. reflexivity. Qed.
Lemma L'_afreearray : forall s Y mx c, afreearray L' s Y mx c = afreearray L s Y mx c. Proof. reflexivity. Qed.
Lemma L'_aslots : forall s Y mx c, aslots L' s Y mx c = aslots L s Y mx c. Proof. reflexivity. Qed.
Lemma L'_ashadow_avail : forall s mx c, ashadow_avail L' s mx c = ashadow_avail L s mx c. Proof. reflexivity. Qed.
Lemma L'_ADEPOTi : forall mx, ADEPOTi L' mx = ADEPOTi L mx. Proof. reflexivity. Qed.
Lemma L'_AFAKE : forall B mx, AFAKE L' B mx = AFAKE L B mx. Proof. reflexivity. Qed.
Lemma L'_arng : forall R s, arng L' R s = arng L R s. Proof. reflexivity. Qed.
Lemma L'_ablocks : forall s Y B, ablocks L' s Y B = ablocks L s Y B. Proof. reflexivity. Qed.
Lemma L'_ok : alayout_ok L' <-> alayout_ok L. Proof. apply remapL_ok. Qed.
Lemma L'_AQUAR : forall s Y mx, AQUAR L' s Y mx <-> AQUAR L s Y mx. Proof. intros. apply remapL_AQUAR. Qed.
Lemma L'_ASEC_of : forall s Y mx, ASEC_of L' s Y mx <-> ASEC_of L s Y mx. Proof. intros. apply remapL_ASEC_of_prim. Qed.
Lemma l_aobj_sclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> sclr A k.
Proof. intros a n A k (_ & _ & _ & HS & _) H1 H2. unfold sclr in *. lia. Qed.

(* [comment removed for export] *)
Lemma prim_geo :
  1 <= c0 < K_NUM_CLASSES /\ 1 <= n0 <= AREQMAX /\ rounded_size n0 + rz_size n0 <= size_of_class c0
  /\ 0 <= k0 < ndist st c0 /\ busy_of X c0 k0 = Some b0
  /\ aregion L c0 <= AB /\ AB + size_of_class c0 <= aregion L c0 + c_allocated_user (get_cls st c0)
  /\ 0 <= c_allocated_user (get_cls st c0) <= K_FREEARR_OFF
  /\ AB mod 16 = 0 /\ UB = AB + rz_size n0 /\ 16 <= rz_size n0 <= 2048 /\ rz_size n0 mod 16 = 0
  /\ 0 < g /\ UB + 8 * g <= AB + size_of_class c0
  /\ al_res L <= aregion L c0 /\ aregion L c0 + K_REGION <= al_space_beg L + K_SPACE_SIZE
  /\ al_space_beg L + K_REGION <= aregion L c0
  /\ 0x10007fff8000 <= al_res L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP.
Proof.
  pose proof AR as (WF & _). pose proof WF as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (BUSY b0 Hb0) as [CLB M]. rewrite Sb0 in M. destruct M as (N0 & FIT & _ & _ & _ & LV).
  destruct (PERC (xb_class b0) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
  pose proof (size_of_class_facts (xb_class b0) CLB) as [QS QS16].
  assert (KB : 0 <= xb_slot b0 < ndist st (xb_class b0)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b0. split; [reflexivity|].
    apply filter_In. split; [exact Hb0| apply Z.eqb_refl]. }
  pose proof (slot_in_region L st (xb_class b0) (xb_slot b0) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
  pose proof (slot_aligned L (xb_class b0) (xb_slot b0) SAL CLB) as AL.
  pose proof (rz_size_facts (xb_n b0) ltac:(lia)) as RZ. pose proof (rounded_size_facts (xb_n b0) ltac:(lia)) as RS.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI.
  split; [exact CLB|]. split; [exact N0|]. split; [exact FIT|]. split; [exact KB|]. split; [exact (l_busy_of_of_In L st X b0 WF Hb0)|].
  split; [exact P5|]. split; [exact P4|]. split; [unfold K_FREEARR_OFF in *; clear -Q1 Q2; lia|]. split; [exact AL|].
  split; [reflexivity|]. split; [clear -RZ; lia|]. split; [clear -RZ; lia|].
  assert (GR : 0 < granules (xb_n b0) /\ 8 * granules (xb_n b0) <= rounded_size (xb_n b0)).
  { unfold granules, rup in *. rewrite shlen_div. destruct RS as (RS1 & RS2 & RS3 & RS4 & _). clear -N0 RS1 RS2 RS3 RS4. Z.div_mod_to_equations. lia. }
  split; [exact (proj1 GR)|]. split; [unfold xb_user, xb_alloc in *; clear -GR FIT; lia|].
  unfold aregion, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
  split; [clear -RSP CLB; lia|]. split; [clear -CLB; nia|]. split; [clear -CLB; nia|]. split; [exact RHI| exact SHI].
Qed.

(* [comment removed for export] *)
Lemma prim_W_range : shad (al_space_beg L) + 536870912 <= shad UB /\ shad UB + g <= shad (al_space_beg L) + 17179869184
  /\ 0x02008fff7000 <= shad UB /\ shad UB + g <= 0x10007fff8000.
Proof.
  pose proof prim_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
  pose proof (ao_space L ALO) as RSP. atop_facts.
  unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *.
  assert (U8 : UB mod 8 = 0) by (rewrite G10; clear -G9 G12; Z.div_mod_to_equations; lia).
  assert (SG : shad UB + g = shad (UB + 8 * g)) by (rewrite (shad_add_shlen _ _ U8), shlen_mul8; reflexivity).
  rewrite SG. rewrite !shad_div. unfold ASHOFF. clear -G6 G7 G8 G10 G11 G13 G14 G15 G16 G17 G18 G19 RSP H U8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma PW_gen : forall A k, 0 <= k -> (A + k <= shad UB \/ shad UB + g <= A) -> disjoint_from W A k.
Proof. intros A k Hk H. cbn. split; [lia| exact I]. Qed.
Lemma PW_app : forall A k, 0 <= k -> sclr A k -> disjoint_from W A k.
Proof. intros A k Hk HS. pose proof prim_W_range as (_ & _ & R1 & R2). apply PW_gen; [exact Hk|]. unfold sclr, KLS in HS. lia. Qed.
Lemma PW_img : forall A k, 0 <= k -> A + k <= AIMG_HI -> disjoint_from W A k.
Proof. intros A k Hk H. apply PW_app; [exact Hk|]. unfold sclr, KLS, AIMG_HI in *. lia. Qed.
Lemma PW_sh : forall A k, A mod 8 = 0 -> 0 <= A -> 0 <= k -> (A + k <= UB \/ UB + 8 * g <= A) -> disjoint_from W (shad A) (shlen k).
Proof.
  intros A k A8 A0 Hk H.
  pose proof prim_geo as (_ & _ & _ & _ & _ & G6 & _ & _ & G9 & G10 & G11 & G12 & G13 & _ & G15 & _ & _ & G18 & _).
  assert (U8 : UB mod 8 = 0) by (rewrite G10; clear -G9 G12; Z.div_mod_to_equations; lia).
  apply PW_gen; [apply shlen_nonneg; exact Hk|].
  apply (shad_apart UB g A k U8 A8 A0); [clear -G6 G10 G11 G15 G18; unfold aregion in *; lia| exact Hk| lia| exact H].
Qed.

(* [comment removed for export] *)
Lemma ssb_L' : forall c k, busy_of X c k <> Some b0 ->
  slot_shadow_bytes (al_pat L') (size_of_class c) (busy_of X c k) = slot_shadow_bytes (al_pat L) (size_of_class c) (busy_of X c k).
Proof.
  intros c k NE. apply ssb_upd_other. intros b EB SB.
  pose proof AR as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNIQ) & _).
  destruct (busy_of_Some_facts X c k b EB) as (Hb & _ & _).
  assert (b = b0) by (apply UNIQ; [exact Hb| exact Hb0| rewrite SB, Sb0; reflexivity| exists p; exact SB]). subst b. exact (NE EB).
Qed.

(* [comment removed for export] *)
Lemma aslot_shadow_set : forall c, 1 <= c < K_NUM_CLASSES -> aslot_shadow L st X m c -> aslot_shadow L' st X m' c.
Proof.
  intros c Hc [SL UND].
  pose proof prim_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
  pose proof AR as ((_ & _ & SAL & _ & _ & PERC & _) & _). destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & _).
  pose proof (size_of_class_facts c Hc) as [QS QS16].
  assert (RG : forall c', 1 <= c' < K_NUM_CLASSES -> aregion L c' + K_REGION <= aregion L c0 \/ aregion L c0 + K_REGION <= aregion L c' \/ c' = c0).
  { intros c' Hc'. destruct (Z.lt_total c' c0) as [LT|[EQ|GT]].
    - left. apply regions_sep. exact LT. - right. right. exact EQ. - right. left. apply regions_sep. exact GT. }
  unfold aslot_shadow. cbv zeta. split.
  - intros k Hk. rewrite !L'_aslot_addr. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
    pose proof (slot_aligned L c k SAL Hc) as ALk.
    destruct (Z.eq_dec c c0) as [->|NEc]; [destruct (Z.eq_dec k k0) as [->|NEk]|].
    + (* [comment removed for export] *)
      specialize (SL k0 Hk). rewrite G5 in SL |- *.
      assert (E1 : slot_shadow_bytes (al_pat L) (size_of_class c0) (Some b0)
                   = repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (rz_size n0))) ++ live_pat (al_pat L p) n0
                     ++ repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (size_of_class c0) - shlen (rz_size n0) - granules n0))).
      { unfold slot_shadow_bytes. rewrite Sb0. reflexivity. }
      assert (E2 : slot_shadow_bytes (al_pat L') (size_of_class c0) (Some b0)
                   = repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (rz_size n0))) ++ live_pat e n0
                     ++ repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (size_of_class c0) - shlen (rz_size n0) - granules n0))).
      { unfold slot_shadow_bytes. rewrite Sb0. unfold set_pat1, remapL. cbn [al_pat]. rewrite upd_pat_eq. reflexivity. }
      rewrite E1 in SL. rewrite E2.
      assert (LP : forall x, length (live_pat x n0) = Z.to_nat g) by (intros x; apply live_pat_length; lia).
      assert (SHU : shad UB = shad (aslot_addr L c0 k0) + shlen (rz_size n0)).
      { rewrite G10. apply shad_add_shlen. unfold xb_alloc in G9. clear -G9; Z.div_mod_to_equations; lia. }
      assert (SR : shlen (rz_size n0) + g <= shlen (size_of_class c0)).
      { rewrite !shlen_div. rewrite G10 in G14. clear -G14 G12 G11 QS16 G9. Z.div_mod_to_equations. lia. }
      pose proof (rw_cells_patch W m m' _ _ _ (shad UB) (live_pat e n0) SL MU WM) as P.
      rewrite LP in P. specialize (P ltac:(intros x Hx1 Hx2; cbn [outside]; split; [clear -Hx2 G13; lia| exact I]) NEW).
      assert (SLN : 0 <= shlen (rz_size n0)) by (apply shlen_nonneg; lia).
      specialize (P ltac:(rewrite SHU; lia)).
      assert (LEN1 : length (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (rz_size n0))) ++ live_pat (al_pat L p) n0
                     ++ repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (size_of_class c0) - shlen (rz_size n0) - granules n0))) = Z.to_nat (shlen (size_of_class c0))).
      { rewrite !length_app, !repeat_length, LP. clear -SR SLN G13. lia. }
      specialize (P ltac:(rewrite SHU; clear -SR SLN G13; lia)).
      replace (Z.to_nat (shad UB - shad (aslot_addr L c0 k0))) with (Z.to_nat (shlen (rz_size n0))) in P by (rewrite SHU; f_equal; lia).
      rewrite firstn_app, repeat_length, Nat.sub_diag in P. rewrite firstn_all2 in P by (rewrite repeat_length; lia). cbn [firstn] in P. rewrite app_nil_r in P.
      rewrite skipn_app, repeat_length in P. replace (Z.to_nat (shlen (rz_size n0)) + Z.to_nat g - Z.to_nat (shlen (rz_size n0)))%nat with (Z.to_nat g) in P by lia.
      rewrite skipn_all2 in P by (rewrite repeat_length; lia). cbn [app] in P.
      rewrite skipn_app, LP, Nat.sub_diag in P. cbn [skipn] in P.
      replace (Z.to_nat g - Z.to_nat g)%nat with 0%nat in P by lia.
      rewrite skipn_all2 in P by (rewrite LP; lia). cbn [app] in P. exact P.
    + (* [comment removed for export] *)
      rewrite (ssb_L' c0 k) by (intros EB; destruct (busy_of_Some_facts X c0 k b0 EB) as (_ & _ & K); apply NEk; rewrite <- K; reflexivity).
      eapply cells_frame; [exact (SL k Hk)| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply shlen_nonneg; lia).
      apply PW_sh; [clear -ALk; Z.div_mod_to_equations; lia| clear -P5 G15 G18; unfold aregion in *; lia| lia|].
      assert (D : aslot_addr L c0 k + size_of_class c0 <= AB \/ AB + size_of_class c0 <= aslot_addr L c0 k).
      { unfold xb_alloc. destruct (Z.lt_total k k0) as [LT|[EQ|GT]]; [left| exfalso; exact (NEk EQ)| right];
          [apply (slots_sep L c0 k k0)| apply (slots_sep L c0 k0 k)]; lia. }
      clear -D G10 G11 G14. lia.
    + (* [comment removed for export] *)
      rewrite (ssb_L' c k) by (intros EB; destruct (busy_of_Some_facts X c k b0 EB) as (_ & C & _); apply NEc; rewrite <- C; reflexivity).
      eapply cells_frame; [exact (SL k Hk)| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply shlen_nonneg; lia).
      apply PW_sh; [clear -ALk; Z.div_mod_to_equations; lia| pose proof (ao_space L ALO) as RSP'; unfold aregion, K_REGION in *; clear -P5 RSP' G18 Hc; lia| lia|].
      destruct (RG c Hc) as [D|[D|D]]; [| | exfalso; exact (NEc D)]; unfold K_REGION, K_FREEARR_OFF in *; clear -D P5 P4 Q1 Q2 G6 G7 G10 G11 G14 G8; lia.
  - rewrite !L'_aregion. eapply fill_frame; [exact UND| exact MU| exact WM|]. intros POS.
    pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM. pose proof (aregion_mod L c SAL) as RM.
    apply PW_sh; [clear -AM RM; Z.div_mod_to_equations; lia| pose proof (ao_space L ALO) as RSP'; unfold aregion, K_REGION in *; clear -Q1 RSP' G18 Hc; lia| lia|].
    destruct (Z.eq_dec c c0) as [->|NEc].
    + right. clear -G7 G10 G11 G14. lia.
    + destruct (RG c Hc) as [D|[D|D]]; [| | exfalso; exact (NEc D)]; unfold K_REGION, K_FREEARR_OFF in *; clear -D Q1 Q2 G6 G7 G10 G11 G14 G8; lia.
Qed.

(* [comment removed for export] *)
Theorem AREP_set_prim : AREP AHL L' st X m'.
Proof.
  pose proof prim_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
  pose proof prim_W_range as (HW1 & HW2 & HW3 & HW4).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof AR as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  assert (U8 : UB mod 8 = 0) by (rewrite G10; clear -G9 G12; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (Kobj : forall a n A k, aobj a n -> a <= A -> 0 <= k -> A + k <= a + n -> disjoint_from W A k).
  { intros a n A k OB H1 Hk H2. apply PW_app; [exact Hk| exact (l_aobj_sclr a n A k OB H1 H2)]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W A k) by (intros A k H1 Hk H2; exact (Kobj _ _ A k (ao_t L ALO) H1 Hk H2)).
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k) by (intros A k H1 Hk H2; exact (Kobj _ _ A k (ao_ctx L ALO) H1 Hk H2)).
  assert (Kxr : forall A k, al_xr L <= A -> 0 <= k -> A + k <= al_xr L + 3727360 -> disjoint_from W A k) by (intros A k H1 Hk H2; exact (Kobj _ _ A k (ao_xr L ALO) H1 Hk H2)).
  assert (Ksp : forall A k, al_space_beg L <= A -> 0 <= k -> disjoint_from W A k).
  { intros A k H1 Hk. apply PW_app; [exact Hk|]. unfold sclr. right. clear -H1 SP1. lia. }
  Local Ltac kimg := apply PW_img; clear; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia.
  split; [rewrite L'_awf; exact WF|].
  split. { rewrite L'_arep_rt. eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [kimg | apply Kctx; clear; lia | apply Kxr; clear; lia] |]). apply Forall_nil. }
  split. { rewrite L'_ainstance. eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; kimg. }
  split.
  { rewrite L'_athread. destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW). unfold athread.
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
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
    assert (RC : al_space_beg L <= aregion L c) by (unfold aregion, K_REGION; clear -Hc; lia).
    assert (RG : aregion L c + K_REGION <= aregion L c0 \/ aregion L c0 + K_REGION <= aregion L c \/ c = c0).
    { destruct (Z.lt_total c c0) as [LT|[EQ|GT]]; [left; apply regions_sep; exact LT| right; right; exact EQ| right; left; apply regions_sep; exact GT]. }
    split; [| split; [| split]].
    - rewrite L'_aregion_cells. eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Ksp; [| clear; lia]. unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. clear -Hc. lia.
    - rewrite L'_afreearray. eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Ksp; [unfold afreearr, K_FREEARR_OFF; clear -RC; lia| clear -Q5 Q6; lia].
      + apply PW_sh; [unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia| unfold afreearr, K_FREEARR_OFF; clear -RC SP1; lia| clear -Q5 Q6; lia|].
        (* [comment removed for export] *)
        unfold afreearr. unfold K_REGION, K_FREEARR_OFF, K_FREEARR_MAX in *. change (2^32) with 4294967296 in *.
        destruct RG as [D|[D|D]]; [left; clear -D G6 G7 G8 G10 G11 G14 Q6; lia| right; clear -D G6 G7 G8 G10 G11 G14 Q6; lia| right; subst c; clear -G6 G7 G8 G10 G11 G14 Q6; lia].
    - rewrite L'_aslots. destruct SLOTS as [SL SUND]. split.
      + intros k Hk. specialize (SL k Hk). pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        destruct (busy_of X c k) as [b|] eqn:EB.
        * destruct (busy_of_Some_facts X c k b EB) as (HbIn & Cb & Kb).
          eapply aslot_busy_frame; [exact MU| exact WM| exact SL| eapply awf_fits; [exact WF| exact HbIn]|].
          unfold xb_alloc. rewrite Cb, Kb. apply Ksp; [clear -P5 RC; lia| clear -QS; lia].
        * eapply junk_frame; [exact SL | exact MU | exact WM |]. intros _. apply Ksp; [clear -P5 RC; lia| clear -QS; lia].
      + eapply junk_frame; [exact SUND | exact MU | exact WM |]. intros POS. apply Ksp; [clear -RC Q1; lia| clear -POS; lia].
    - exact (aslot_shadow_set c HcK SHADOW). }
  split.
  { (* [comment removed for export] *)
    cbn [AHL ah_quar]. apply L'_AQUAR. eapply (hq_frame _ AHL_laws L st st X X m m' W); [exact HQ | exact MU | exact WM | | apply quar_same_refl].
    unfold quar_untouched. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
    pose proof (ao_t L ALO) as OT. unfold aobj, sclr, KLS in OT. unfold AINSTANCE.
    split; [clear -OT HW3 HW4; lia|]. split; [clear -HW3; lia|]. split; [clear -HW3; lia|]. split; [clear -HW3; lia|].
    intros b Hb. destruct (xb_st b) as [q| |] eqn:Sb; [exact I| |].
    all: destruct (BUSY b Hb) as [CLB _]; destruct (PERC (xb_class b) CLB) as (B1' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR);
         pose proof (size_of_class_facts (xb_class b) CLB) as [BS _];
         assert (KB : 0 <= xb_slot b < ndist st (xb_class b)) by
           (apply BR; apply in_app_iff; right; apply in_app_iff; right; unfold busy_slots; apply in_map_iff; exists b; split; [reflexivity|];
            apply filter_In; split; [exact Hb| apply Z.eqb_refl]);
         pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -BS; lia) (proj1 B1') KB) as (P5' & _ & _);
         left; unfold xb_alloc, aregion, K_REGION in *; change (2^32) with 4294967296 in *; clear -P5' CLB HW4 SP1; lia. }
  split.
  { (* [comment removed for export] *)
    cbn [AHL ah_sec]. apply L'_ASEC_of. eapply (hs_frame _ AHL_laws L st st X X m m' W); [exact HS | exact MU | exact WM | | apply sec_same_refl].
    unfold sec_untouched. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. unfold aknown. right. left. clear -Ha HW1 HW2. lia. }
  split.
  { (* [comment removed for export] *)
    cbn [AHL ah_depot ADEPOT adepot_iface_raw]. rewrite L'_ADEPOTi. cbn [AHL ah_depot ADEPOT adepot_iface_raw] in HD.
    eapply adepot_frame; [exact HD | exact MU | exact WM |].
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha.
    pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. unfold aobj, sclr, KLS in ON, OS.
    split; [clear -Ha HW3; lia|]. split; [clear -Ha ON HW3 HW4; lia| clear -Ha OS HW3 HW4; lia]. }
  split; [eapply arelro_frame; [exact MU | exact HRO | kimg]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; kimg|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; kimg |]); apply Forall_nil].
  (* [comment removed for export] *)
  intros c Hc. rewrite L'_ashadow_avail. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
  pose proof (size_of_class_facts c HcK) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM.
  assert (RC : al_space_beg L <= aregion L c) by (unfold aregion, K_REGION; clear -Hc; lia).
  assert (RG : aregion L c + K_REGION <= aregion L c0 \/ aregion L c0 + K_REGION <= aregion L c \/ c = c0).
  { destruct (Z.lt_total c c0) as [LT|[EQ|GT]]; [left; apply regions_sep; exact LT| right; right; exact EQ| right; left; apply regions_sep; exact GT]. }
  eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c HcK) | reflexivity | reflexivity | |].
  - intros POS. apply PW_sh; [clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia| clear -RC SP1 Q1; lia| clear -Q2; unfold K_FREEARR_OFF in *; lia|].
    unfold K_REGION, K_FREEARR_OFF, K_FREEARR_MAX in *. change (2^32) with 4294967296 in *.
    destruct RG as [D|[D|D]]; [left; clear -D G6 G7 G8 G10 G11 G14 Q1 Q2; lia| right; clear -D G6 G7 G8 G10 G11 G14 Q1 Q2; lia| right; subst c; clear -G6 G7 G8 G10 G11 G14 Q1 Q2; lia].
  - intros POS. apply PW_sh; [unfold afreearr; clear -RM Q7; unfold K_FREEARR_MAP, K_FREEARR_OFF in *; Z.div_mod_to_equations; lia| unfold afreearr, K_FREEARR_OFF; clear -RC SP1 Q5 Q6; lia| clear -Q6; unfold K_FREEARR_MAX in *; lia|].
    unfold afreearr. unfold K_REGION, K_FREEARR_OFF, K_FREEARR_MAX in *. change (2^32) with 4294967296 in *.
    destruct RG as [D|[D|D]]; [left; clear -D G6 G7 G8 G10 G11 G14 Q5 Q6; lia| right; clear -D G6 G7 G8 G10 G11 G14 Q5 Q6; lia| right; subst c; clear -G6 G7 G8 G10 G11 G14 Q5 Q6; lia].
Qed.

(* [comment removed for export] *)
Lemma AFAKE_set_prim : forall LB, AFAKE L LB m -> AFAKE L' LB m'.
Proof.
  intros LB HF. rewrite L'_AFAKE. eapply afake_frame; [exact HF| exact MU| exact WM|].
  pose proof prim_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
  pose proof prim_W_range as (HW1 & HW2 & HW3 & HW4). pose proof (ao_space L ALO) as RSP.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. pose proof (ad_fake_res L ALO) as DFR. unfold aobj, sclr, KLS, adisj in OF, OD, DFR.
  assert (U8 : UB mod 8 = 0) by (rewrite G10; clear -G9 G12; Z.div_mod_to_equations; lia).
  assert (SF : disjoint_from W (shad (al_fake L)) (shlen 11571200)).
  { apply PW_sh; [clear -OF; Z.div_mod_to_equations; lia| clear -OF; lia| clear; lia|].
    unfold K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
    clear -DFR G6 G7 G8 G10 G11 G14 G15 G16 RSP. lia. }
  cbn [disjoint_from] in SF. destruct SF as [SF _].
  unfold afake_untouched, fake_untouched. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
  split; [clear -OF HW3 HW4; lia|]. split; [clear -SF; lia|]. split; [clear -OD HW3 HW4; lia|].
  clear -HW3. repeat split; lia.
Qed.
End PrimSet.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_casesH : forall H L st X LB m p A n,
  alayout_ok L -> AREP H L st X m -> ablocks L st X LB -> In (HB p A n) LB ->
  (exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_user L b = A /\ xb_n b = n /\ is_primary n = true)
  \/ (exists mb ms, (a_live st) !! p = Some (CSec mb ms n) /\ A = mb + SEC_UOFF /\ sec_wf1 L (CSec mb ms n) /\ is_primary n = false
      /\ In (CSec mb ms n) (sec_chunks_of st)).
Proof.
  intros H L st X LB m p A n ALO AR BL Hin.
  pose proof AR as (WF & _). pose proof WF as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  - left. exists b. destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. destruct M as (N0 & FIT & _).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _]. subst n.
    repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try reflexivity.
    unfold is_primary, needed0, K_MAX_SIZE. apply Z.leb_le. clear -FIT QS. lia.
  - right. exists mb, ms. pose proof G as G0. cbn [sec_wf1] in G0. destruct G0 as (_ & _ & _ & _ & _ & G6 & _).
    repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
    apply in_map_iff. exists (p, CSec mb ms n). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp.
Qed.

Theorem AHEAP_set_prim : forall L RNG st LB m m' p A n e,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
  munch [(shad A, shad A + granules n)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (shad A) [CB (Z.to_nat (granules n)) (live_pat e n)] ->
  AHEAP_L (set_pat1 L p e) RNG st LB m'.
Proof.
  intros L RNG st LB m m' p A n e (ALO & ARNG & [X [AR BL]] & HFK) Hin PRIM MU WM NEW. cbn [AHL ah_fake] in HFK.
  destruct (hb_casesH AHL L st X LB m p A n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & _)|(mb & ms & _ & _ & _ & NP & _)]; [| rewrite PRIM in NP; discriminate].
  subst A n.
  split; [apply L'_ok; exact ALO|]. split; [rewrite L'_arng; exact ARNG|]. split.
  - exists X. split; [| rewrite L'_ablocks; exact BL]. eapply AREP_set_prim; eassumption.
  - cbn [AHL ah_fake]. eapply AFAKE_set_prim; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma l_achunk_eq_dec : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; apply Z.eq_dec. Defined.

Section SecSet.
Variables (L : alayout) (st : astate) (X : aconc) (m m' : amem) (mb ms n0 : Z) (e : option (list byte)).
Hypothesis ALO : alayout_ok L.
Hypothesis AR : AREP AHL L st X m.
Hypothesis INC : In (CSec mb ms n0) (sec_chunks_of st).
Hypothesis LVC : sec_live st (CSec mb ms n0).
Local Notation UBs := (mb + SEC_UOFF).
Local Notation g := (granules n0).
Local Notation W := [(shad (mb + SEC_UOFF), shad (mb + SEC_UOFF) + granules n0)].
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis NEW : rw_cells asegs m' (shad UBs) [CB (Z.to_nat g) (live_pat e n0)].
Local Notation L' := (set_spat1 L mb e).

(* [comment removed for export] *)
Lemma M'_aslot_addr : forall c k, aslot_addr L' c k = aslot_addr L c k. Proof. reflexivity. Qed.
Lemma M'_aregion : forall c, aregion L' c = aregion L c. Proof. reflexivity. Qed.
Lemma M'_afreearr : forall c, afreearr L' c = afreearr L c. Proof. reflexivity. Qed.
Lemma M'_awf : forall s Y, awf L' s Y = awf L s Y. Proof. reflexivity. Qed.
Lemma M'_arep_rt : forall mx, arep_rt L' mx = arep_rt L mx. Proof. reflexivity. Qed.
Lemma M'_ainstance : forall s mx, ainstance L' s mx = ainstance L s mx. Proof. reflexivity. Qed.
Lemma M'_athread : forall s Y mx, athread L' s Y mx = athread L s Y mx. Proof. reflexivity. Qed.
Lemma M'_aregion_cells : forall s mx c, aregion_cells L' s mx c = aregion_cells L s mx c. Proof. reflexivity. Qed.
Lemma M'_afreearray : forall s Y mx c, afreearray L' s Y mx c = afreearray L s Y mx c. Proof. reflexivity. Qed.
Lemma M'_aslots : forall s Y mx c, aslots L' s Y mx c = aslots L s Y mx c. Proof. reflexivity. Qed.
Lemma M'_aslot_shadow : forall s Y mx c, aslot_shadow L' s Y mx c = aslot_shadow L s Y mx c. Proof. reflexivity. Qed.
Lemma M'_ashadow_avail : forall s mx c, ashadow_avail L' s mx c = ashadow_avail L s mx c. Proof. reflexivity. Qed.
Lemma M'_ADEPOTi : forall mx, ADEPOTi L' mx = ADEPOTi L mx. Proof. reflexivity. Qed.
Lemma M'_AFAKE : forall B mx, AFAKE L' B mx = AFAKE L B mx. Proof. reflexivity. Qed.
Lemma M'_arng : forall R s, arng L' R s = arng L R s. Proof. reflexivity. Qed.
Lemma M'_ablocks : forall s Y B, ablocks L' s Y B = ablocks L s Y B. Proof. reflexivity. Qed.
Lemma M'_asec_inst : forall mx, asec_inst L' mx = asec_inst L mx. Proof. reflexivity. Qed.
Lemma M'_aprim0 : forall mx, aprim0 L' mx = aprim0 L mx. Proof. reflexivity. Qed.
Lemma M'_ashz : forall cs mx, ashz L' cs mx = ashz L cs mx. Proof. reflexivity. Qed.
Lemma M'_ok : alayout_ok L' <-> alayout_ok L. Proof. apply remapL_ok. Qed.
Lemma M'_AQUAR : forall s Y mx, AQUAR L' s Y mx <-> AQUAR L s Y mx. Proof. intros. apply remapL_AQUAR. Qed.
Lemma M'_asec_wf : forall s cs, asec_wf L' s cs <-> asec_wf L s cs. Proof. intros. apply remapL_asec_wf. Qed.

(* [comment removed for export] *)
Lemma sec_geo :
  mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ 64512 < n0 <= AREQMAX /\ sec_clear L mb ms
  /\ 0 < g /\ shad UBs = shad mb + 768 /\ 768 + g <= ms / 8 /\ UBs + 8 * g <= mb + ms
  /\ 2148339200 <= shad mb /\ shad mb + ms / 8 <= shad ATOP /\ shad ATOP + 1 <= 0x10007fff8000 /\ AIMG_HI <= mb /\ 0 <= ms.
Proof.
  pose proof AR as (_ & _ & _ & _ & _ & _ & HS & _). cbn [AHL ah_sec] in HS. unfold ASEC_of in HS. pose proof HS as (WFS & _).
  pose proof WFS as (_ & _ & _ & _ & _ & WF1 & _). pose proof (proj1 (Forall_forall _ _) WF1 _ INC) as W1.
  pose proof W1 as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
  pose proof (sec_facts n0 ltac:(clear -G5; lia) G6) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- G4 in MSR, MSM, MSB.
  pose proof (ablk_lin _ _ G2) as (G2a & G2b & G2c & G2d). atop_facts.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G5|]. split; [exact GC|].
  unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. unfold ASHOFF, AIMG_HI in *.
  clear -G1 G2a G2b G2c G2d G3 G5 RSR NSE MSR MSM H. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma SW_gen : forall A k, 0 <= k -> (A + k <= shad UBs \/ shad UBs + g <= A) -> disjoint_from W A k.
Proof. intros A k Hk H. cbn. split; [lia| exact I]. Qed.
Lemma SW_app : forall A k, 0 <= k -> sclr A k -> disjoint_from W A k.
Proof.
  intros A k Hk HS. pose proof sec_geo as (_ & _ & _ & _ & _ & G6 & G7 & G8 & _ & G10 & G11 & G12 & _).
  apply SW_gen; [exact Hk|]. unfold sclr, KLS in HS. clear -HS G6 G7 G8 G10 G11 G12 Hk. lia.
Qed.
Lemma SW_img : forall A k, 0 <= k -> A + k <= AIMG_HI -> disjoint_from W A k.
Proof. intros A k Hk H. apply SW_app; [exact Hk|]. unfold sclr, KLS, AIMG_HI in *. lia. Qed.
Lemma SW_sh : forall A k, A mod 8 = 0 -> 0 <= A -> 0 <= k -> (A + k <= UBs \/ UBs + 8 * g <= A) -> disjoint_from W (shad A) (shlen k).
Proof.
  intros A k A8 A0 Hk H. pose proof sec_geo as (G1 & _ & _ & _ & _ & G6 & _ & _ & _ & _ & _ & _ & G13 & _).
  assert (U8 : UBs mod 8 = 0) by (unfold SEC_UOFF; clear -G1; Z.div_mod_to_equations; lia).
  apply SW_gen; [apply shlen_nonneg; exact Hk|].
  apply (shad_apart UBs g A k U8 A8 A0); [unfold SEC_UOFF, AIMG_HI in *; clear -G13; lia| exact Hk| clear -G6; lia| exact H].
Qed.
(* [comment removed for export] *)
Lemma res_apart : forall A k, al_res L <= A -> A + k <= al_res L + 137439023104 -> A + k <= UBs \/ UBs + 8 * g <= A.
Proof.
  intros A k H1 H2. pose proof sec_geo as (_ & _ & _ & _ & (_ & _ & Cr & _) & _ & _ & _ & G9 & _).
  unfold SEC_UOFF in *. clear -H1 H2 Cr G9. lia.
Qed.

Theorem AREP_set_sec : AREP AHL L' st X m'.
Proof.
pose proof sec_geo as (G1 & G2 & G3 & G5 & GC & GR1 & GR2 & GR3 & GR4 & GR5 & GR6 & GR7 & GR8 & GR9).
pose proof GC as (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd & Cx).
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ao_space L ALO) as RSP.
pose proof AR as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
pose proof WF as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
assert (Kobj : forall a n A k, aobj a n -> a <= A -> 0 <= k -> A + k <= a + n -> disjoint_from W A k).
{
intros a n A k OB H1 Hk H2.
apply SW_app; [exact Hk| exact (l_aobj_sclr a n A k OB H1 H2)].
}
assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W A k) by (intros A k H1 Hk H2; exact (Kobj _ _ A k (ao_t L ALO) H1 Hk H2)).
assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k) by (intros A k H1 Hk H2; exact (Kobj _ _ A k (ao_ctx L ALO) H1 Hk H2)).
assert (Kxr : forall A k, al_xr L <= A -> 0 <= k -> A + k <= al_xr L + 3727360 -> disjoint_from W A k) by (intros A k H1 Hk H2; exact (Kobj _ _ A k (ao_xr L ALO) H1 Hk H2)).
assert (Ksp : forall A k, al_space_beg L <= A -> 0 <= k -> disjoint_from W A k).
{
intros A k H1 Hk.
apply SW_app; [exact Hk|].
unfold sclr.
right.
clear -H1 SP1.
lia.
}
assert (Kpsh : forall A k, A mod 8 = 0 -> al_space_beg L <= A -> 0 <= k -> A + k <= al_space_beg L + K_SPACE_SIZE -> disjoint_from W (shad A) (shlen k)).
{
intros A k A8 H1 Hk H2.
apply SW_sh; [exact A8| clear -H1 SP1; lia| exact Hk|].
apply res_apart; [clear -H1 RSP; lia|].
unfold K_SPACE_SIZE in H2.
change (2^37) with 137438953472 in H2.
clear -H2 RSP.
lia.
}
Local Ltac kimgS := apply SW_img; clear; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia.
split; [rewrite M'_awf; exact WF|].
split.
{
rewrite M'_arep_rt.
eapply arep_rt_frame; [exact MU | exact WM | exact RT |].
unfold rt_hulls, ATP88, ATSD.
repeat (apply Forall_cons; [cbn [fst snd]; first [kimgS | apply Kctx; clear; lia | apply Kxr; clear; lia] |]).
apply Forall_nil.
}
split.
{
rewrite M'_ainstance.
eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; kimgS.
}
split.
{
rewrite M'_athread.
destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
unfold athread.
split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
split.
{
intros c Hc.
eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
unfold acache_addr.
unfold K_NUM_CLASSES in Hc.
apply Kt; clear -Hc; lia.
}
split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia].
}
split.
{
intros c Hc.
destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
pose proof (size_of_class_facts c Hc) as [QS QS16].
pose proof (aregion_mod L c SAL) as RM.
pose proof Hc as HcK.
unfold K_NUM_CLASSES in Hc.
assert (RC : al_space_beg L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE).
{
unfold aregion, K_REGION, K_SPACE_SIZE.
change (2^37) with 137438953472.
clear -Hc.
lia.
}
destruct RC as [RC RC2].
unfold K_REGION in RC2.
split; [| split; [| split]].
-
rewrite M'_aregion_cells.
eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
apply Ksp; [| clear; lia].
unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE.
change (2^37) with 137438953472.
clear -Hc.
lia.
-
rewrite M'_afreearray.
eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
+
apply Ksp; [unfold afreearr, K_FREEARR_OFF; clear -RC; lia| clear -Q5 Q6; lia].
+
apply Kpsh; [unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia| unfold afreearr, K_FREEARR_OFF; clear -RC; lia| clear -Q5 Q6; lia|].
unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *.
change (2^32) with 4294967296 in *.
clear -RC2 Q6.
lia.
-
rewrite M'_aslots.
destruct SLOTS as [SL SUND].
split.
+
intros k Hk.
specialize (SL k Hk).
pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
destruct (busy_of X c k) as [b|] eqn:EB.
*
destruct (busy_of_Some_facts X c k b EB) as (HbIn & Cb & Kb).
eapply aslot_busy_frame; [exact MU| exact WM| exact SL| eapply awf_fits; [exact WF| exact HbIn]|].
unfold xb_alloc.
rewrite Cb, Kb.
apply Ksp; [clear -P5 RC; lia| clear -QS; lia].
*
eapply junk_frame; [exact SL | exact MU | exact WM |].
intros _.
apply Ksp; [clear -P5 RC; lia| clear -QS; lia].
+
eapply junk_frame; [exact SUND | exact MU | exact WM |].
intros POS.
apply Ksp; [clear -RC Q1; lia| clear -POS; lia].
-
rewrite M'_aslot_shadow.
eapply (aslot_shadow_update L W m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
+
intros k Hk _.
pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
pose proof (slot_aligned L c k SAL HcK) as AL.
split; [reflexivity|].
apply Kpsh; [clear -AL; Z.div_mod_to_equations; lia| clear -P5 RC; lia| clear -QS; lia|].
unfold K_FREEARR_OFF in *.
change (2^32) with 4294967296 in *.
clear -P4 Q1 Q2 RC2.
lia.
+
intros POS.
apply Kpsh; [pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia| clear -Q1 RC; lia| clear -Q1; lia|].
unfold K_FREEARR_OFF in *.
change (2^32) with 4294967296 in *.
clear -Q1 Q2 RC2.
lia.
}
split.
{
cbn [AHL ah_quar].
apply M'_AQUAR.
eapply (hq_frame _ AHL_laws L st st X X m m' W); [exact HQ | exact MU | exact WM | | apply quar_same_refl].
unfold quar_untouched.
apply Forall_cons; [| apply Forall_nil].
cbn [fst snd].
pose proof (ao_t L ALO) as OT.
unfold aobj, sclr, KLS in OT.
unfold AINSTANCE.
split; [clear -OT GR2 GR5 GR6 GR7 GR1 GR3; lia|].
split; [clear -GR2 GR5; lia|].
split; [clear -GR2 GR5; lia|].
split; [clear -GR2 GR5; lia|].
intros b Hb.
destruct (xb_st b) as [q| |] eqn:Sb; [exact I| |].
all: destruct (BUSY b Hb) as [CLB _]; destruct (PERC (xb_class b) CLB) as (B1' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR);
         pose proof (size_of_class_facts (xb_class b) CLB) as [BS _];
         assert (KB : 0 <= xb_slot b < ndist st (xb_class b)) by
           (apply BR; apply in_app_iff; right; apply in_app_iff; right; unfold busy_slots; apply in_map_iff; exists b; split; [reflexivity|];
            apply filter_In; split; [exact Hb| apply Z.eqb_refl]);
         pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -BS; lia) (proj1 B1') KB) as (P5' & _ & _);
         left; unfold xb_alloc, aregion, K_REGION in *; change (2^32) with 4294967296 in *; clear -P5' CLB GR2 GR3 GR6 GR7 GR1 SP1; lia.
}
split.
{
cbn [AHL ah_sec] in HS |- *.
unfold ASEC_of in *.
pose proof HS as (WFS & ARR & INST2 & PZ & SHZ).
pose proof WFS as (_ & WP & WR & WL & WB & WF1 & [ND PW]).
split; [apply M'_asec_wf; exact WFS|].
split; [| split; [| split]].
-
destruct ARR as (order & PO & U64 & JK & PER).
exists order.
split; [exact PO|].
assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
destruct WR as [_ WRB].
change (al_ptr_array L') with (al_ptr_array L).
split; [| split].
+
destruct order as [|o0 order'].
*
destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]].
split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
*
eapply u64arr_frame; [exact U64| exact MU| exact WM|].
rewrite length_map.
eapply Kobj; [exact (ao_ptr L ALO)| clear; lia| clear; cbn; lia| cbn [length] in LEN |- *; clear -LEN WB WRB; lia].
+
eapply junk_frame; [exact JK| exact MU| exact WM|].
intros POS.
eapply Kobj; [exact (ao_ptr L ALO)| clear -POS WB WRB; lia| clear -POS; lia| clear -POS WB WRB; lia].
+
intros i ch Hi.
destruct (PER i ch Hi) as (lv & LV2 & CH).
assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
pose proof (proj1 (Forall_forall _ _) WF1 _ Hin) as W1'.
destruct ch as [c' n'|mb' ms' n']; [destruct W1'|].
exists lv.
split; [exact LV2|].
        pose proof W1' as W0'. cbn [sec_wf1] in W0'. destruct W0' as (G1' & G2' & G3' & G4' & G5' & G6' & GC').
        pose proof (sec_facts n' ltac:(clear -G5'; lia) G6') as (NB' & _ & RSE' & RSR' & _ & NSE' & _ & MSR' & MSM' & MSB'). rewrite <- G4' in MSR', MSM', MSB'.
        pose proof (ablk_lin _ _ G2') as (G2a' & G2b' & _ & _).
        assert (GR' : 0 <= granules n' /\ shad (mb' + SEC_UOFF) = shad mb' + 768 /\ 768 + granules n' <= ms' / 8 /\ 0 <= ms' /\ 0 < granules n').
        { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -G1' G5' RSR' NSE' MSR' MSM'. Z.div_mod_to_equations. lia. }
        destruct GR' as (GR1' & GR2' & GR3' & GR4' & GR5').
        assert (DLO : forall A k, mb' <= A -> 0 <= k -> A + k <= mb' + ms' -> disjoint_from W A k).
        { intros A k H1 Hk H2. apply SW_app; [exact Hk|]. unfold ablk, sclr, KLS, AIMG_HI in *. clear -H1 H2 G2'. lia. }
        cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3). unfold SEC_UOFF in *.
        split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DLO; clear -MSR' NSE' RSR' G5'; lia]|].
        split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DLO; clear -MSR' NSE' RSR' G5'; lia]|].
        split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DLO; clear -MSR' NSE' RSR' G5'; lia]|].
        split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DLO; clear -MSR' NSE' RSR' G5'; lia]|].
        split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
                 eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DLO; clear -MSR' NSE' RSR' G5'; lia]. }
        split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; apply DLO; clear -MSR' NSE' RSR' G5'; lia]|].
        destruct (l_achunk_eq_dec (CSec mb' ms' n') (CSec mb ms n0)) as [E|NE].
        * (* [comment removed for export] *)
          injection E as -> -> ->.
          split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply SW_gen; unfold SEC_UOFF; [clear; lia| left; rewrite GR2; clear; lia]]|].
          split.
          { assert (LVT : lv = true) by (apply LV2; exact LVC). subst lv.
            unfold set_spat1. rewrite remapL_spat, upd_spat_eq. unfold sec_user_shadow. exact NEW. }
          eapply fill_frame; [exact S3| exact MU| exact WM| intros _; apply SW_gen; unfold SEC_UOFF; [clear -GR3 GR1; lia| right; clear; lia]].
        * (* [comment removed for export] *)
          pose proof (PW _ _ Hin INC NE) as D. cbn [sec_mb sec_ms] in D.
          assert (NEB : mb' <> mb) by (intros ->; clear -D GR4' GR8 GR3' GR5' GR3 GR1 ; lia).
          assert (DSH : disjoint_from W (shad mb') (shlen ms')).
          { apply SW_sh; unfold SEC_UOFF; [clear -G1'; Z.div_mod_to_equations; lia| exact G2b'| exact GR4'|]. clear -D GR4. lia. }
          rewrite shlen_div in DSH.
          split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; eapply disjoint_from_sub; [exact DSH| clear; lia| clear -GR3' GR1'; lia| clear; lia]]|].
          split.
          { unfold set_spat1. rewrite remapL_spat, (upd_spat_ne _ _ _ _ NEB).
            eapply cells_frame; [exact S2| exact MU| exact WM| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by exact GR1'; rewrite GR2'].
            eapply disjoint_from_sub; [exact DSH| clear; lia| clear -GR3' GR1'; lia| exact GR1']. }
          eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2'; eapply disjoint_from_sub; [exact DSH| clear -GR1'; lia| clear -GR3' GR1'; lia| clear -POS; lia]].

-
rewrite M'_asec_inst.
destruct INST2 as (I1 & [srt I2] & I3 & I4 & I5 & I6).
unfold asec_inst.
split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; kimgS]|].
split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; kimgS]|].
split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; kimgS]|].
split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; kimgS]|].
split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; kimgS]|].
eapply junk_frame; [exact I6| exact MU| exact WM| intros _; kimgS].
-
rewrite M'_aprim0.
unfold aprim0 in *.
eapply azero_frame; [exact PZ| exact MU| exact WM|].
intros POS.
apply Kpsh; [clear -SAL; unfold K_ALIGN in *; Z.div_mod_to_equations; lia| clear; lia| clear; unfold K_REGION; lia| unfold K_REGION, K_SPACE_SIZE; clear; lia].
-
rewrite M'_ashz.
intros x Hx HF HC.
rewrite <- (SHZ x Hx HF HC).
apply MU.
assert (SX : 0 <= shad x < 2^64) by (rewrite !shad_div; atop_facts; unfold ASHOFF, AIMG_HI, KLS, K_HIGH_MEM in *; clear -Hx H; Z.div_mod_to_equations; lia).
rewrite wa_unsigned by exact SX.
pose proof (proj1 (Forall_forall _ _) HC _ INC) as NX.
cbn [sec_mb sec_ms] in NX.
cbn [outside].
split; [| exact I].
rewrite GR2.
rewrite !shad_div in *.
unfold SEC_UOFF in *.
clear -NX GR3 GR4 G1.
Z.div_mod_to_equations.
lia.
  }
  split.
  { (* [comment removed for export] *)
    cbn [AHL ah_depot ADEPOT adepot_iface_raw]. rewrite M'_ADEPOTi. cbn [AHL ah_depot ADEPOT adepot_iface_raw] in HD.
    eapply adepot_frame; [exact HD | exact MU | exact WM |].
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. unfold SEC_UOFF in *.
    pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. unfold aobj, sclr, KLS in ON, OS.
    split; [clear -Ha GR2 GR5; lia|]. split; [clear -Ha ON GR2 GR3 GR5 GR6 GR7; lia| clear -Ha OS GR2 GR3 GR5 GR6 GR7; lia]. }
  split; [eapply arelro_frame; [exact MU | exact HRO | kimgS]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; kimgS|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; kimgS |]); apply Forall_nil].
  (* [comment removed for export] *)
  intros c Hc. rewrite M'_ashadow_avail. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
  pose proof (size_of_class_facts c HcK) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM.
  assert (RC : al_space_beg L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc. lia. }
  destruct RC as [RC RC2]. unfold K_REGION in RC2.
  eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c HcK) | reflexivity | reflexivity | |].
  - intros POS. apply Kpsh; [clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia| clear -RC Q1; lia| clear -Q2; unfold K_FREEARR_OFF in *; lia|].
    unfold K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. clear -RC2 Q1 Q2. lia.
  - intros POS. apply Kpsh; [unfold afreearr; clear -RM Q7; unfold K_FREEARR_MAP, K_FREEARR_OFF in *; Z.div_mod_to_equations; lia| unfold afreearr, K_FREEARR_OFF; clear -RC Q5 Q6; lia| clear -Q6; unfold K_FREEARR_MAX in *; lia|].
    unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. change (2^32) with 4294967296 in *. clear -RC2 Q5 Q6. lia.
Qed.

Lemma AFAKE_set_sec : forall LB, AFAKE L LB m -> AFAKE L' LB m'.
Proof.
  intros LB HF. rewrite M'_AFAKE. eapply afake_frame; [exact HF| exact MU| exact WM|].
  pose proof sec_geo as (G1 & G2 & G3 & G5 & GC & GR1 & GR2 & GR3 & GR4 & GR5 & GR6 & GR7 & GR8 & GR9).
  pose proof GC as (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd & Cx).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. unfold aobj, sclr, KLS in OF, OD.
  assert (SF : disjoint_from W (shad (al_fake L)) (shlen 11571200)).
  { apply SW_sh; [clear -OF; Z.div_mod_to_equations; lia| clear -OF; lia| clear; lia|]. unfold SEC_UOFF in *. clear -Cf GR4. lia. }
  cbn [disjoint_from] in SF. destruct SF as [SF _].
  unfold afake_untouched, fake_untouched. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold SEC_UOFF in *.
  split; [clear -OF GR2 GR3 GR5 GR6 GR7; lia|]. split; [clear -SF; lia|]. split; [clear -OD GR2 GR3 GR5 GR6 GR7; lia|].
  clear -GR2 GR5. repeat split; lia.
Qed.
End SecSet.

Theorem AHEAP_set_sec : forall L RNG st LB m m' p A n e,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB -> is_primary n = false ->
  munch [(shad A, shad A + granules n)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (shad A) [CB (Z.to_nat (granules n)) (live_pat e n)] ->
  AHEAP_L (set_spat1 L (A - SEC_UOFF) e) RNG st LB m'.
Proof.
  intros L RNG st LB m m' p A n e (ALO & ARNG & [X [AR BL]] & HFK) Hin NPRIM MU WM NEW. cbn [AHL ah_fake] in HFK.
  destruct (hb_casesH AHL L st X LB m p A n ALO AR BL Hin) as [(b & _ & _ & _ & _ & PR)|(mb & ms & Lp & EA & G & _ & INC)]; [rewrite NPRIM in PR; discriminate|].
  subst A. replace (mb + SEC_UOFF - SEC_UOFF) with mb by lia.
  assert (LVC : sec_live st (CSec mb ms n)) by (exists p; exact Lp).
  split; [apply M'_ok; exact ALO|]. split; [rewrite M'_arng; exact ARNG|]. split.
  - exists X. split; [| rewrite M'_ablocks; exact BL]. eapply AREP_set_sec; eassumption.
  - cbn [AHL ah_fake]. eapply AFAKE_set_sec; eassumption.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition blk_entry (L : alayout) (p : aptr) (A n : Z) : option (list byte) :=
  if is_primary n then al_pat L p else al_spat L (A - SEC_UOFF).

Lemma upd_pat_upd_pat : forall pat p e e', upd_pat (upd_pat pat p e) p e' = upd_pat pat p e'.
Proof. intros. apply functional_extensionality. intros q. unfold upd_pat. destruct (N.eqb q p); reflexivity. Qed.
Lemma upd_pat_same : forall pat p e, pat p = e -> upd_pat pat p e = pat.
Proof. intros pat p e H. apply functional_extensionality. intros q. unfold upd_pat. destruct (N.eqb_spec q p) as [->|]; [symmetry; exact H| reflexivity]. Qed.
Lemma upd_spat_upd_spat : forall spat mb e e', upd_spat (upd_spat spat mb e) mb e' = upd_spat spat mb e'.
Proof. intros. apply functional_extensionality. intros q. unfold upd_spat. destruct (Z.eqb q mb); reflexivity. Qed.
Lemma upd_spat_same : forall spat mb e, spat mb = e -> upd_spat spat mb e = spat.
Proof. intros spat mb e H. apply functional_extensionality. intros q. unfold upd_spat. destruct (Z.eqb_spec q mb) as [->|]; [symmetry; exact H| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma set_blk_remapL : forall L p A n e,
  set_blk L p A n e = remapL L (if is_primary n then upd_pat (al_pat L) p e else al_pat L)
                               (if is_primary n then al_spat L else upd_spat (al_spat L) (A - SEC_UOFF) e).
Proof. intros. unfold set_blk, set_pat1, set_spat1. destruct (is_primary n); reflexivity. Qed.

(* [comment removed for export] *)
Lemma set_blk_set_blk : forall L p A n e e', set_blk (set_blk L p A n e) p A n e' = set_blk L p A n e'.
Proof.
  intros. unfold set_blk, set_pat1, set_spat1, remapL. destruct (is_primary n); cbn [al_V al_w al_U al_pat al_spat];
    [rewrite upd_pat_upd_pat| rewrite upd_spat_upd_spat]; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma set_blk_same : forall L p A n e, blk_entry L p A n = e -> set_blk L p A n e = L.
Proof.
  intros [V w U f g] p A n e H. unfold set_blk, set_pat1, set_spat1, remapL, blk_entry in *. cbn [al_V al_w al_U al_pat al_spat] in *.
  destruct (is_primary n); [rewrite (upd_pat_same _ _ _ H)| rewrite (upd_spat_same _ _ _ H)]; reflexivity.
Qed.
Lemma blk_entry_set_blk : forall L p A n e, blk_entry (set_blk L p A n e) p A n = e.
Proof.
  intros. unfold blk_entry, set_blk, set_pat1, set_spat1, remapL. destruct (is_primary n); cbn [al_pat al_spat]; [apply upd_pat_eq| apply upd_spat_eq].
Qed.
Lemma blk_entry_tight : forall L p A n, al_tight L -> blk_entry L p A n = None.
Proof. intros L p A n [H1 H2]. unfold blk_entry. rewrite H1, H2. destruct (is_primary n); reflexivity. Qed.
Corollary set_blk_tight : forall L p A n, al_tight L -> set_blk L p A n None = L.
Proof. intros. apply set_blk_same. apply blk_entry_tight. assumption. Qed.
Corollary set_blk_restore : forall L p A n e, al_tight L -> set_blk (set_blk L p A n e) p A n None = L.
Proof. intros. rewrite set_blk_set_blk. apply set_blk_tight. assumption. Qed.

(* [comment removed for export] *)
Section BlkInv.
Variables (L : alayout) (p : aptr) (A n : Z) (e : option (list byte)).
Local Notation L' := (set_blk L p A n e).
Lemma set_blk_V : al_V L' = al_V L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_w : al_w L' = al_w L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_U : al_U L' = al_U L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_sp0 : al_sp0 L' = al_sp0 L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_top : al_top L' = al_top L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_bot : al_bot L' = al_bot L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_t : al_t L' = al_t L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_ctx : al_ctx L' = al_ctx L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_space_beg : al_space_beg L' = al_space_beg L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_ptr_array : al_ptr_array L' = al_ptr_array L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_nodes : al_nodes L' = al_nodes L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_store : al_store L' = al_store L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_fake : al_fake L' = al_fake L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_res : al_res L' = al_res L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_dtls : al_dtls L' = al_dtls L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_xr : al_xr L' = al_xr L. Proof. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_ok : alayout_ok L' <-> alayout_ok L. Proof. rewrite set_blk_remapL. apply remapL_ok. Qed.
Lemma set_blk_aunw : forall mx RNG lo PC sp s0 ra tr, aunw mx L' RNG lo PC sp s0 ra tr <-> aunw mx L RNG lo PC sp s0 ra tr.
Proof. intros. unfold aunw. rewrite set_blk_top, set_blk_U. tauto. Qed.
Lemma set_blk_aresv_ok : forall RESV, aresv_ok L' RESV <-> aresv_ok L RESV.
Proof. intros. rewrite set_blk_remapL. unfold aresv_ok. cbn [al_V remapL al_ptr_array al_t al_ctx al_nodes al_store al_fake]. tauto. Qed.
(* [comment removed for export] *)
Lemma blk_entry_set_blk_other : forall q B k, is_primary k = is_primary n -> (if is_primary n then q <> p else B <> A) ->
  blk_entry L' q B k = blk_entry L q B k.
Proof.
  intros q B k EK NE. unfold blk_entry, set_blk, set_pat1, set_spat1, remapL. rewrite EK. destruct (is_primary n); cbn [al_pat al_spat].
  - apply upd_pat_ne. exact NE.
  - apply upd_spat_ne. intros E. apply NE. lia.
Qed.
End BlkInv.

(* [comment removed for export] *)
Theorem AHEAP_L_set1 : forall L RNG st LB m m' p A n e,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB ->
  munch [(shad A, shad A + granules n)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (shad A) [CB (Z.to_nat (granules n)) (live_pat e n)] ->
  AHEAP_L (set_blk L p A n e) RNG st LB m'.
Proof.
  intros L RNG st LB m m' p A n e AH Hin MU WM NEW. unfold set_blk.
  destruct (is_primary n) eqn:P; [eapply AHEAP_set_prim| eapply AHEAP_set_sec]; eassumption.
Qed.
End CANSEC1.
