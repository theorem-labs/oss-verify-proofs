(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums DepotInv.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module DIN.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import APSX.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section WithFP1. Context {FP : PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.
Variables dD dS : Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kreadE (k : list kentry) (b : expr) (off : Z) (n : nat) : option expr :=
  match know_lookup segs k b off n false [] [] with
  | LHit e sc _ => match sc with [] => Some e | _ => None end
  | _ => None
  end.
Definition kcellZ (k : list kentry) (a : Z) (n : nat) : option Z := kreadZ segs k (ELit 0) a n.

(* [comment removed for export] *)
Fixpoint insert_iv (x : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => [x]
  | y :: r => if Z.leb (fst x) (fst y) then x :: l else y :: insert_iv x r
  end.
Fixpoint sort_ivs (l : list (Z * Z)) : list (Z * Z) :=
  match l with [] => [] | x :: r => insert_iv x (sort_ivs r) end.
Definition kimg_ivs (k : list kentry) (lo hi : Z) : list (Z * Z) :=
  sort_ivs (fold_right (fun K acc => match K with
                                    | KImg a b => if (Z.ltb a hi && Z.ltb lo b && Z.ltb a b)%bool then (Z.max a lo, Z.min b hi) :: acc else acc
                                    | _ => acc end) [] k).
Fixpoint cells_ok (k : list kentry) (a : Z) (n : nat) (vmax : Z) : bool :=
  match n with
  | O => true
  | S n' => match kcellZ k a 4 with Some v => Z.leb v vmax | None => false end && cells_ok k (a + 4) n' vmax
  end%bool.
(* [comment removed for export] *)
Definition gap_ok (k : list kentry) (dD g0 g1 vmax : Z) : bool :=
  if (Z.leb g0 g1 && Z.eqb ((g0 - dD) mod 4) 0 && Z.eqb ((g1 - dD) mod 4) 0 && Z.leb (g1 - g0) 64)%bool
  then cells_ok k g0 (Z.to_nat ((g1 - g0) / 4)) vmax else false.   (* [comment removed for export] *)
Fixpoint tab_sweep (k : list kentry) (dD : Z) (cur : Z) (ivs : list (Z * Z)) (hi : Z) (vmax : Z) : bool :=
  match ivs with
  | [] => gap_ok k dD cur hi vmax
  | (a, b) :: r => (if Z.leb a cur then true else gap_ok k dD cur a vmax) && tab_sweep k dD (Z.max cur b) r hi vmax
  end%bool.
Definition tab_cov (k : list kentry) (dD vmax : Z) : bool :=
  let hi := dD + 4194304 in tab_sweep k dD dD (kimg_ivs k dD hi) hi vmax.

(* [comment removed for export] *)
Definition block_ok (k : list kentry) (e : expr) (size : Z) : bool :=
  match elo k e, ehi k e with
  | Some lo, Some hi => (Z.leb IMGHI lo && Z.leb (hi + size) VATOP && Z.leb 12 (ealign k e))%bool
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition depot_intro_chk (K : Z) (k : list kentry) : bool :=
      match kcellZ k (dD + 0x400000) 4, kreadE k (ELit 0) (dD + 0x400010) 8, kcellZ k dS 8, kreadE k (ELit 0) (dS + 16) 8, kcellZ k (dS + 24) 4 with
      | Some n1, Some e17, Some t, Some e18, Some c =>
          (Z.eqb n1 1 && Z.eqb c t && Z.leb 0 t && Z.leb 0 K && Z.leb (t + 5 * K) 512 && Z.ltb (1 + K) 65535
           && match kreadZ segs k e17 24 4 with Some l => Z.eqb l 0 | None => false end
           && block_ok k e17 (2 ^ 20) && block_ok k e18 (2 ^ 23)
           && ranges_apart_x k e17 0 (ELit (2 ^ 20)) e18 0 (ELit 4096)
           && kwritable k k e17 0 (2 ^ 20) && kwritable k k e18 0 4096
           && Z.leb 65536 dS && Z.leb (dS + 32) dD && Z.leb (dD + 0x400018) IMGHI
           && Z.eqb (dD mod 8) 0 && Z.eqb (dS mod 8) 0
           && tab_cov k dD 1)%bool
      | _, _, _, _, _ => false
      end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.

Definition img_byte_ok (x : Z) : Prop :=
  exists seg b, find_segment segs x 1 = Some seg /\ seg_writable seg = true /\ seg_readable seg = true
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (x - Z.of_N (seg_base seg))) = Some b /\ bv_unsigned b = 0.

(* [comment removed for export] *)
Lemma img_ok_wr : forall M lo len, 0 <= lo -> lo + len < 2 ^ 64 ->
  (forall x, lo <= x < lo + len -> img_byte_ok x) -> wr_ok segs M lo len.
Proof.
  intros M lo len Hlo Hhi H d m Hd Hdm.
  apply store_ok_seg_writable; rewrite u64_lit by lia; [lia|].
  intros x Hx. destruct (H (bv_unsigned x) ltac:(lia)) as (seg & b & F1 & F2 & F3 & F4 & F5).
  exists seg. split; [exact F1|]. split; [exact F2|]. rewrite F4. discriminate.
Qed.

Lemma img_ok_rom : forall x, 0 <= x < 2 ^ 64 -> img_byte_ok x -> seg_rom segs (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof.
  intros x Hx (seg & b & F1 & F2 & F3 & F4 & F5). unfold seg_rom, memory_read.
  rewrite u64_lit by lia. change (Z.of_N 1) with 1. rewrite F1, F3.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite F4. f_equal. apply bv_eq. rewrite F5. reflexivity.
Qed.

Lemma img_ok_rdn : forall M n a, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> img_byte_ok x /\ M (Z_to_bv 64 x) = None) ->
  rdn segs M (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros M n. induction n as [|n IH]; intros a Ha Hn H; [reflexivity|].
  cbn [rdn repeat]. destruct (H a ltac:(lia)) as [Hb Hm]. rewrite Hm, (img_ok_rom a ltac:(lia) Hb).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  - rewrite (IH (a + 1)); [reflexivity | lia | lia |]. intros x Hx. apply H. lia.
  - apply bv_eq. rewrite bv_add_unsigned, !u64_lit by lia. change (bv_unsigned (1%bv : bv 64)) with 1.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kreadZ_kreadE : forall k b off n z, kreadZ segs k b off n = Some z ->
  exists z0, kreadE k b off n = Some (ELit z0) /\ z = z0 mod two64.
Proof.
  intros k b off n z H. unfold kreadZ in H. unfold kreadE.
  destruct (know_lookup segs k b off n false [] []) as [v sc hs|sc hs|]; try discriminate.
  destruct v; try discriminate. destruct sc; [|discriminate]. injection H as <-. eexists. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kreadE_rdn0 : forall E M k b off n v,
  know_ok segs E M k -> kreadE k b off n = Some v -> (1 <= n)%nat -> (n <= 8)%nat -> flat E (SA b off) (Z.of_nat n) ->
  rdn segs M (adenot E (SA b off)) n = Some (word_to_le_bytes n (edenot E v)).
Proof.
  intros E M k b off n v HK H Hn1 Hn8 Hfl. unfold kreadE in H.
  pose proof (know_lookup_sound segs E M k b off n false [] [] HK Hn1 Hn8) as X.
  destruct (know_lookup segs k b off n false [] []) as [v' sc hs|sc hs|]; try discriminate.
  destruct sc; [|discriminate]. injection H as ->.
  destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  rewrite Hrd. f_equal. rewrite <- Hv. unfold extz. symmetry. apply word_to_le_bytes_of_bytes_n; assumption.
Qed.

Lemma Z2bv_mod64 : forall z, Z_to_bv 64 (z mod two64) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, two64. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.

Lemma kcellZ_rdw : forall E M k a n z,
  know_ok segs E M k -> kcellZ k a n = Some z -> (1 <= n <= 8)%nat -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdw segs M a n z /\ 0 <= z < 2 ^ 64.
Proof.
  intros E M k a n z HK H Hn Ha Han. unfold kcellZ in H.
  destruct (kreadZ_kreadE k (ELit 0) a n z H) as (z0 & He & ->).
  assert (Hfl : flat E (SA (ELit 0) a) (Z.of_nat n)).
  { unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. }
  pose proof (kreadE_rdn0 E M k (ELit 0) a n (ELit z0) HK He ltac:(lia) ltac:(lia) Hfl) as R.
  unfold adenot, v_addi in R. cbn [a_base a_off edenot] in R. rewrite u64_lit in R by lia. rewrite Z.add_0_l in R.
  split; [| unfold two64; apply Z.mod_pos_bound; lia].
  unfold rdw. rewrite R, <- Z2bv_mod64. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kreadZ_at_rdw : forall E M k e off n z base,
  know_ok segs E M k -> kreadZ segs k e off n = Some z -> (1 <= n <= 8)%nat ->
  bv_unsigned (edenot E e) = base -> 0 <= base + off -> base + off + Z.of_nat n <= 2 ^ 64 ->
  rdw segs M (base + off) n z /\ 0 <= z < 2 ^ 64.
Proof.
  intros E M k e off n z base HK H Hn Hb H0 Hhi.
  destruct (kreadZ_kreadE k e off n z H) as (z0 & He & ->).
  assert (Hfl : flat E (SA e off) (Z.of_nat n)) by (unfold flat, estart; cbn [a_base a_off]; rewrite Hb; lia).
  pose proof (kreadE_rdn0 E M k e off n (ELit z0) HK He ltac:(lia) ltac:(lia) Hfl) as R.
  unfold adenot, v_addi in R. cbn [a_base a_off edenot] in R. rewrite Hb in R.
  split; [| unfold two64; apply Z.mod_pos_bound; lia].
  unfold rdw. rewrite R, <- Z2bv_mod64. reflexivity.
Qed.

Lemma block_ok_sound : forall E M k e size,
  know_ok segs E M k -> block_ok k e size = true ->
  IMGHI <= bv_unsigned (edenot E e) /\ bv_unsigned (edenot E e) + size <= VATOP
  /\ bv_unsigned (edenot E e) mod 4096 = 0.
Proof.
  intros E M k e size HK H. unfold block_ok in H.
  destruct (elo k e) as [lo|] eqn:Hlo; [|discriminate]. destruct (ehi k e) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H Hal]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in Hal.
  pose proof (xlo_sound segs E M k e lo HK Hlo) as B1. pose proof (xhi_sound segs E M k e hi HK Hhi) as B2.
  split; [lia|]. split; [lia|].
  pose proof (ealign_sound segs E M k e HK) as [Hrg [q Hq]]. rewrite Hq. apply Z.mod_divide; [lia|].
  exists (q * 2 ^ (ealign k e - 12)). rewrite <- Z.mul_assoc. f_equal.
  change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma kwritable_wr : forall E M k e n base,
  know_ok segs E M k -> kwritable k k e 0 n = true -> 0 <= n -> bv_unsigned (edenot E e) = base ->
  base + n < 2 ^ 64 -> wr_ok segs M base n.
Proof.
  intros E M k e n base HK H Hn Hb Hhi.
  destruct (kwritable_sound segs E M k k e 0 n HK HK H Hn) as (ST & _ & _). unfold estart in ST. cbn [a_base a_off] in ST. rewrite Hb, Z.add_0_r in ST.
  pose proof (u64_range (edenot E e)) as Hr.
  intros d m Hd Hdm. apply (StoreOk.store_ok_sub segs M (Z_to_bv 64 base) _ (Z.to_nat n) m); rewrite ?u64_lit; try lia. exact ST.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_ok_sound : forall k n g0 vmax, cells_ok k g0 n vmax = true ->
  forall j, 0 <= j < Z.of_nat n -> exists v, kcellZ k (g0 + 4 * j) 4 = Some v /\ v <= vmax.
Proof.
  intros k n. induction n as [|n IH]; intros g0 vmax H j Hj; [lia|].
  cbn [cells_ok] in H. apply andb_prop in H as [H1 H2].
  destruct (kcellZ k g0 4) as [v|] eqn:Hv; [|discriminate]. apply Z.leb_le in H1.
  destruct (Z.eq_dec j 0) as [-> | Hne].
  - exists v. rewrite Z.mul_0_r, Z.add_0_r. split; [exact Hv | exact H1].
  - destruct (IH (g0 + 4) vmax H2 (j - 1) ltac:(lia)) as (v' & Hv' & B'). exists v'.
    replace (g0 + 4 * j) with (g0 + 4 + 4 * (j - 1)) by lia. split; assumption.
Qed.

Section Sweep.
  Variables (k : list kentry) (dB vmax : Z) (ivs0 : list (Z * Z)).

  Definition in_ivs (y : Z) : Prop := exists a b, In (a, b) ivs0 /\ a <= y < b.
  Definition cell_of (y : Z) : Z := dB + 4 * ((y - dB) / 4).
  Definition cell_chk (c : Z) : Prop := exists v, kcellZ k c 4 = Some v /\ v <= vmax.
  Definition okb (y : Z) : Prop := in_ivs y \/ cell_chk (cell_of y).

  Lemma cell_of_range : forall y, dB <= y -> cell_of y <= y < cell_of y + 4 /\ (cell_of y - dB) mod 4 = 0.
  Proof.
    intros y Hy. unfold cell_of.
    pose proof (Z.div_mod (y - dB) 4 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (y - dB) 4 ltac:(lia)) as B1.
    split; [lia|]. replace (dB + 4 * ((y - dB) / 4) - dB) with (((y - dB) / 4) * 4) by lia. apply Z_mod_mult.
  Qed.

  Lemma cell_of_aligned : forall c j, (c - dB) mod 4 = 0 -> 0 <= j < 4 -> cell_of (c + j) = c.
  Proof.
    intros c j Hc Hj. unfold cell_of.
    pose proof (Z.div_mod (c - dB) 4 ltac:(lia)) as E1. rewrite Hc, Z.add_0_r in E1.
    replace (c + j - dB) with (j + ((c - dB) / 4) * 4) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia.
  Qed.

  Lemma gap_ok_sound : forall g0 g1, gap_ok k dB g0 g1 vmax = true -> forall y, g0 <= y < g1 -> okb y.
  Proof.
    intros g0 g1 H y Hy. unfold gap_ok in H.
    match type of H with (if ?c then _ else _) = true => destruct c eqn:Hg; [|discriminate] end.
    rename H into Hc. pose proof Hg as H. clear Hg.
    apply andb_prop in H as [H H64]. apply andb_prop in H as [H Hm1].
    apply andb_prop in H as [Hle Hm0].
    apply Z.leb_le in Hle. apply Z.eqb_eq in Hm0. apply Z.eqb_eq in Hm1. apply Z.leb_le in H64.
    right.
    pose proof (Z.div_mod (g0 - dB) 4 ltac:(lia)) as E0. rewrite Hm0, Z.add_0_r in E0.
    pose proof (Z.div_mod (g1 - dB) 4 ltac:(lia)) as E1. rewrite Hm1, Z.add_0_r in E1.
    set (j := (y - g0) / 4).
    pose proof (Z.div_mod (y - g0) 4 ltac:(lia)) as Ey. pose proof (Z.mod_pos_bound (y - g0) 4 ltac:(lia)) as By. fold j in Ey.
    assert (Hcell : cell_of y = g0 + 4 * j).
    { replace y with ((g0 + 4 * j) + (y - g0) mod 4) at 1 by lia. apply cell_of_aligned; [|lia].
      replace (g0 + 4 * j - dB) with ((j + (g0 - dB) / 4) * 4) by lia. apply Z_mod_mult. }
    rewrite Hcell. unfold cell_chk.
    apply (cells_ok_sound k _ g0 vmax Hc j).
    assert (Hdiv : (g1 - g0) / 4 * 4 = g1 - g0).
    { pose proof (Z.div_mod (g1 - g0) 4 ltac:(lia)) as E2.
      assert (Hm : (g1 - g0) mod 4 = 0).
      { replace (g1 - g0) with ((g1 - dB) - (g0 - dB)) by lia. rewrite Zminus_mod, Hm0, Hm1. reflexivity. }
      lia. }
    rewrite Z2Nat.id by (apply Z.div_pos; lia). nia.
  Qed.

  Lemma sweep_sound : forall ivs cur hi,
    tab_sweep k dB cur ivs hi vmax = true -> incl ivs ivs0 ->
    (forall y, dB <= y < cur -> okb y) -> dB <= cur ->
    forall y, dB <= y < hi -> okb y.
  Proof.
    induction ivs as [|[a b] r IH]; intros cur hi H Hincl Hcur Hdc y Hy.
    - cbn [tab_sweep] in H. destruct (Z_lt_le_dec y cur) as [Hl|Hg]; [apply Hcur; lia|].
      apply (gap_ok_sound cur hi H). lia.
    - cbn [tab_sweep] in H. apply andb_prop in H as [H1 H2].
      apply (IH (Z.max cur b) hi H2); [intros iv Hiv; apply Hincl; right; exact Hiv | | lia | exact Hy].
      intros y' Hy'. destruct (Z_lt_le_dec y' cur) as [Hl|Hg]; [apply Hcur; lia|].
      destruct (Z.leb_spec a cur).
      + left. exists a, b. split; [apply Hincl; left; reflexivity | lia].
      + destruct (Z_lt_le_dec y' a) as [Hl'|Hg'].
        * apply (gap_ok_sound cur a H1). lia.
        * left. exists a, b. split; [apply Hincl; left; reflexivity | lia].
  Qed.
End Sweep.

Lemma insert_iv_incl : forall x l y, In y (insert_iv x l) -> y = x \/ In y l.
Proof.
  induction l as [|z l IH]; intros y H; cbn [insert_iv] in H.
  - destruct H as [<-|[]]. left; reflexivity.
  - destruct (Z.leb (fst x) (fst z)).
    + destruct H as [<-|H]; [left; reflexivity | right; exact H].
    + destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH y H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.

Lemma sort_ivs_incl : forall l y, In y (sort_ivs l) -> In y l.
Proof.
  induction l as [|x l IH]; intros y H; cbn [sort_ivs] in H; [exact H|].
  destruct (insert_iv_incl x (sort_ivs l) y H) as [->|H']; [left; reflexivity | right; apply IH; exact H'].
Qed.

(* [comment removed for export] *)
Lemma kimg_ivs_sound : forall E M k lo hi a b, know_ok segs E M k -> In (a, b) (kimg_ivs k lo hi) ->
  forall y, a <= y < b -> lo <= y < hi /\ M (Z_to_bv 64 y) = None.
Proof.
  intros E M k lo hi a b HK Hin y Hy. unfold kimg_ivs in Hin. apply sort_ivs_incl in Hin.
  induction k as [|K r IH]; [destruct Hin|].
  apply Forall_cons_iff in HK as [HKK Hr]. cbn [fold_right] in Hin.
  assert (REST : In (a, b) (fold_right (fun K acc => match K with
                                     | KImg a0 b0 => if (Z.ltb a0 hi && Z.ltb lo b0 && Z.ltb a0 b0)%bool then (Z.max a0 lo, Z.min b0 hi) :: acc else acc
                                     | _ => acc end) [] r) -> lo <= y < hi /\ M (Z_to_bv 64 y) = None) by (intros H; exact (IH Hr H)).
  destruct K as [| | |ilo ihi| | | | | | |kid kargs]; try (apply REST; exact Hin).
  destruct (Z.ltb ilo hi && Z.ltb lo ihi && Z.ltb ilo ihi)%bool eqn:Hc; [|apply REST; exact Hin].
  destruct Hin as [Heq|Hin]; [|apply REST; exact Hin].
  injection Heq as <- <-. cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & HN).
  split; [lia|]. apply HN. lia.
Qed.

Theorem tab_cov_sound : forall E M k dB vmax,
  know_ok segs E M k -> tab_cov k dB vmax = true -> 0 <= vmax ->
  0 <= dB -> dB + 4194304 < 2 ^ 64 ->
  (forall x, dB <= x < dB + 4194304 -> img_byte_ok x) ->
  forall bi, 0 <= bi < 2 ^ 20 -> exists v, rdw segs M (dB + 4 * bi) 4 v /\ 0 <= v <= vmax.
Proof.
  intros E M k dB vmax HK H Hvmax HdD Hhi Himg bi Hbi. unfold tab_cov in H.
  set (hi := dB + 4194304) in *. set (ivs := kimg_ivs k dB hi) in *.
  pose proof (sweep_sound k dB vmax ivs ivs dB hi H ltac:(intros iv Hiv; exact Hiv) ltac:(intros; lia) ltac:(lia)) as SW.
  set (c := dB + 4 * bi).
  assert (Hcd : (c - dB) mod 4 = 0) by (subst c; replace (dB + 4 * bi - dB) with (bi * 4) by lia; apply Z_mod_mult).
  (* [comment removed for export] *)
  assert (ALT : (exists v, kcellZ k c 4 = Some v /\ v <= vmax) \/ (forall j, 0 <= j < 4 -> in_ivs ivs (c + j))).
  { destruct (SW c ltac:(subst c hi; lia)) as [I0|C0].
    - destruct (kcellZ k c 4) as [v|] eqn:Hcell.
      + destruct (Z_le_gt_dec v vmax) as [Hle|Hgt]; [left; exists v; split; [reflexivity | exact Hle] | right].
        intros j Hj. destruct (SW (c + j) ltac:(subst c hi; lia)) as [I|C]; [exact I|].
        exfalso. rewrite (cell_of_aligned dB c j Hcd Hj) in C. destruct C as (v' & E' & B'). rewrite Hcell in E'. injection E' as <-. lia.
      + right. intros j Hj. destruct (SW (c + j) ltac:(subst c hi; lia)) as [I|C]; [exact I|].
        exfalso. rewrite (cell_of_aligned dB c j Hcd Hj) in C. destruct C as (v' & E' & _). rewrite Hcell in E'. discriminate.
    - left. rewrite (cell_of_aligned dB c 0 Hcd ltac:(lia)) in C0 || (replace (cell_of dB c) with c in C0 by (symmetry; rewrite <- (Z.add_0_r c) at 1; apply (cell_of_aligned dB c 0 Hcd); lia)).
      exact C0. }
  destruct ALT as [(v & Hcell & Hle) | Hall].
  - destruct (kcellZ_rdw E M k c 4 v HK Hcell ltac:(lia) ltac:(lia) ltac:(subst c hi; cbn [Z.of_nat]; lia)) as [R B].
    exists v. split; [exact R | lia].
  - exists 0. split; [|lia]. unfold rdw. rewrite (img_ok_rdn M 4 c); [reflexivity | lia | subst c hi; cbn [Z.of_nat]; lia |].
    intros x Hx. destruct (Hall (x - c) ltac:(cbn [Z.of_nat] in Hx; lia)) as (a & b & Hin & Hab). replace (c + (x - c)) with x in Hab by lia.
    destruct (kimg_ivs_sound E M k dB hi a b HK Hin x Hab) as [Hr Hn]. split; [apply Himg; subst hi; lia | exact Hn].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac band H a b := apply andb_prop in H as [a b].

Theorem depot_intro_sound : forall E M k K e17 e18,
  (forall x, dD <= x < dD + 0x400018 -> img_byte_ok x) -> (forall x, dS <= x < dS + 32 -> img_byte_ok x) ->
  know_ok segs E M k -> depot_intro_chk K k = true ->
  kreadE k (ELit 0) (dD + 0x400010) 8 = Some e17 -> kreadE k (ELit 0) (dS + 16) 8 = Some e18 ->
  0 <= K /\ DepotInv segs dD dS K (bv_unsigned (edenot E e17)) (bv_unsigned (edenot E e18)) M.
Proof.
  intros E M k K e17 e18 ZD ZS HK H He17 He18. unfold depot_intro_chk in H.
  destruct (kcellZ k (dD + 0x400000) 4) as [n1|] eqn:HN; [|discriminate].
  rewrite He17 in H.
  destruct (kcellZ k dS 8) as [t|] eqn:HT; [|discriminate].
  rewrite He18 in H.
  destruct (kcellZ k (dS + 24) 4) as [c|] eqn:HC; [|discriminate].
  band H H Htab. band H H Hm2. band H H Hm1.
  band H H L3. band H H L2. band H H L1.
  band H H W18. band H H W17. band H H Hap. band H H B18. band H H B17. band H H Hlk.
  band H H HK65. band H H HTK. band H H HK0. band H H Ht0. band H Hn1 Hct.
  apply Z.eqb_eq in Hn1. apply Z.eqb_eq in Hct. apply Z.leb_le in Ht0. apply Z.leb_le in HK0. apply Z.leb_le in HTK. apply Z.ltb_lt in HK65.
  apply Z.leb_le in L1. apply Z.leb_le in L2. apply Z.leb_le in L3. apply Z.eqb_eq in Hm1. apply Z.eqb_eq in Hm2. subst n1 c.
  destruct (kreadZ segs k e17 24 4) as [lk|] eqn:Hlk'; [|discriminate]. apply Z.eqb_eq in Hlk. subst lk.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (block_ok_sound E M k e17 (2 ^ 20) HK B17) as (B17a & B17b & B17c).
  destruct (block_ok_sound E M k e18 (2 ^ 23) HK B18) as (B18a & B18b & B18c).
  unfold IMGHI, VATOP in B17a, B17b, B18a, B18b, L3.
  set (b17 := bv_unsigned (edenot E e17)) in *. set (b18 := bv_unsigned (edenot E e18)) in *.
  pose proof (u64_range (edenot E e17)) as R17r. pose proof (u64_range (edenot E e18)) as R18r. fold b17 in R17r. fold b18 in R18r.
  (* [comment removed for export] *)
  destruct (kcellZ_rdw E M k (dD + 0x400000) 4 1 HK HN ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as [RN _].
  destruct (kcellZ_rdw E M k dS 8 t HK HT ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as [RT Rt].
  destruct (kcellZ_rdw E M k (dS + 24) 4 t HK HC ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as [RC _].
  assert (R17 : rdw segs M (dD + 0x400010) 8 b17).
  { assert (Hfl : flat E (SA (ELit 0) (dD + 0x400010)) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
    pose proof (kreadE_rdn0 E M k (ELit 0) (dD + 0x400010) 8 e17 HK He17 ltac:(lia) ltac:(lia) Hfl) as R.
    unfold adenot, v_addi in R. cbn [a_base a_off edenot] in R. rewrite u64_lit in R by lia. rewrite Z.add_0_l in R.
    unfold rdw. rewrite R. subst b17. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R18 : rdw segs M (dS + 16) 8 b18).
  { assert (Hfl : flat E (SA (ELit 0) (dS + 16)) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
    pose proof (kreadE_rdn0 E M k (ELit 0) (dS + 16) 8 e18 HK He18 ltac:(lia) ltac:(lia) Hfl) as R.
    unfold adenot, v_addi in R. cbn [a_base a_off edenot] in R. rewrite u64_lit in R by lia. rewrite Z.add_0_l in R.
    unfold rdw. rewrite R. subst b18. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  destruct (kreadZ_at_rdw E M k e17 24 4 0 b17 HK Hlk' ltac:(lia) eq_refl ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as [RL _].
  (* [comment removed for export] *)
  pose proof (ranges_apart_x_sound segs E M k e17 0 (ELit (2 ^ 20)) e18 0 (ELit 4096) HK Hap) as DJ.
  unfold estart, elenZ in DJ. cbn [a_base a_off edenot] in DJ. rewrite !u64_lit in DJ by lia. fold b17 b18 in DJ.
  split; [exact HK0|]. exists (DST 1 t). unfold DepotInvS. cbn [d_N d_T]. unfold TCAP, IMGHI, VATOP in *.
  repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  - apply img_ok_wr; [lia | lia |]. intros x Hx. apply ZD. lia.
  - apply img_ok_wr; [lia | lia |]. intros x Hx. apply ZS. lia.
  - eapply kwritable_wr; [exact HK | exact W17 | lia | reflexivity | lia].
  - eapply kwritable_wr; [exact HK | exact W18 | lia | reflexivity | lia].
  - apply (tab_cov_sound E M k dD 1 HK Htab); [lia | lia | lia |]. intros x Hx. apply ZD. lia.
  - intros i Hi. exists 0. replace i with 1 by lia. replace (b17 + 16 * 1 + 8) with (b17 + 24) by lia. split; [exact RL | lia].
Qed.


End Sound.
End WithSegs.
End WithFP1.

End DIN.
