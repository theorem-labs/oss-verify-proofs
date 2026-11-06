(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac flia := solve [ repeat match goal with x := _ |- _ => clearbody x end; lia ].
Ltac fnia := solve [ repeat match goal with x := _ |- _ => clearbody x end; nia ]. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zin_rangeb (z : Z) (r : word * word) : bool :=
  ((bv_unsigned (fst r) <=? z) && (z <? bv_unsigned (fst r) + bv_unsigned (snd r)))%Z.

Definition in_rangesb (a : word) (rs : list (word * word)) : bool :=
  existsb (zin_rangeb (bv_unsigned a)) rs.

(* [comment removed for export] *)
Definition hiddenb (L S : list (word * word)) (a : word) : bool :=
  in_rangesb a L && negb (in_rangesb a S).

(* [comment removed for export] *)
Definition restrict_mem_by (hid : word -> bool) (m : word -> option byte)
    : word -> option byte :=
  fun a => if hid a then None else m a.

Definition unrestrict_mem_by (hid : word -> bool) (mF m1 : word -> option byte)
    : word -> option byte :=
  fun a => if hid a then mF a else m1 a.

Definition with_mem (ms : machine_state) (m : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := m; ms_rom := ms_rom ms |}.

Definition restrict_by (hid : word -> bool) (ms : machine_state) : machine_state :=
  with_mem ms (restrict_mem_by hid (ms_mem ms)).

Definition unrestrict_by (hid : word -> bool) (msF ms1 : machine_state) : machine_state :=
  with_mem ms1 (unrestrict_mem_by hid (ms_mem msF) (ms_mem ms1)).

Definition restrict_mem (L S : list (word * word)) := restrict_mem_by (hiddenb L S).
Definition restrict (L S : list (word * word)) := restrict_by (hiddenb L S).
Definition unrestrict_to (L S : list (word * word)) := unrestrict_by (hiddenb L S).

(* [comment removed for export] *)
Definition range_visible (hid : word -> bool) (a : word) (n : nat) : Prop :=
  forall i, (i < n)%nat -> hid (a + Z_to_bv 64 (Z.of_nat i)) = false.

Definition ranges_visible (hid : word -> bool) (rs : list memory_access) : Prop :=
  forall a n, In (a, n) rs -> range_visible hid a n.

(* [comment removed for export] *)
Definition seg_covers (seg : Segment) (z : Z) : Prop :=
  (Z.of_N (seg_base seg) <= z < Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.

Definition hid_avoids_segs (segs : list Segment) (hid : word -> bool) : Prop :=
  (forall a seg, In seg segs -> seg_covers seg (bv_unsigned a) -> hid a = false)
  /\ (forall seg, In seg segs ->
        (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_add_nat_S : forall (a : word) i,
  a + Z_to_bv 64 (Z.of_nat (S i)) = (a + 1) + Z_to_bv 64 (Z.of_nat i).
Proof.
  intros a i. apply bv_eq.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  unfold bv_wrap. rewrite Nat2Z.inj_succ.
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_r, Zplus_mod_idemp_l.
  f_equal. lia.
Qed.

Lemma bv_add_nat_0 : forall (a : word), a + Z_to_bv 64 (Z.of_nat 0) = a.
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 (Z.of_nat 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma bv_unsigned_add_small : forall (a : word) (i : Z),
  (0 <= i)%Z -> (bv_unsigned a + i < 2 ^ 64)%Z ->
  bv_unsigned (a + Z_to_bv 64 i) = (bv_unsigned a + i)%Z.
Proof.
  intros a i Hi Hlt.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  change (bv_modulus 64) with (2^64)%Z in Ha.
  rewrite bv_add_unsigned, Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 i) by (change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma range_visible_S : forall hid a n,
  range_visible hid a (S n) <-> hid a = false /\ range_visible hid (a + 1) n.
Proof.
  intros hid a n. unfold range_visible. split.
  - intros H. split.
    + rewrite <- (bv_add_nat_0 a). apply H. lia.
    + intros i Hi. rewrite <- bv_add_nat_S. apply H. lia.
  - intros [H0 HS] i Hi. destruct i as [|i].
    + rewrite bv_add_nat_0. exact H0.
    + rewrite bv_add_nat_S. apply HS. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HidSem.
Variable segs : list Segment.
Variable hid : word -> bool.
Hypothesis Hhs : hid_avoids_segs segs hid.

Let rmem := restrict_mem_by hid.

Lemma find_segment_spec : forall ss z n seg,
  find_segment ss z n = Some seg ->
  In seg ss /\ (Z.of_N (seg_base seg) <= z)%Z
  /\ (z + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction ss as [|s ss IH]; cbn; intros z n seg H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s)) z && Z.leb (z + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - inversion H; subst. apply andb_true_iff in E. destruct E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2. auto.
  - destruct (IH z n seg H) as (Hin & H1 & H2). auto.
Qed.

(* [comment removed for export] *)
Lemma find_segment_visible : forall a n seg,
  find_segment segs (bv_unsigned a) (Z.of_nat n) = Some seg ->
  range_visible hid a n.
Proof.
  intros a n seg Hf i Hi.
  destruct (find_segment_spec _ _ _ _ Hf) as (Hin & Hlo & Hhi).
  destruct Hhs as [Hcov Hnw].
  pose proof (Hnw seg Hin) as Hseg.
  apply (Hcov _ seg Hin). unfold seg_covers.
  rewrite bv_unsigned_add_small by lia. lia.
Qed.

Lemma find_segment_visible1 : forall a seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> hid a = false.
Proof.
  intros a seg Hf.
  rewrite <- (bv_add_nat_0 a).
  apply (find_segment_visible a 1 seg); [exact Hf | lia].
Qed.

(* [comment removed for export] *)

Lemma wview_restrict : forall m a,
  wview segs (rmem m) a = if hid a then None else wview segs m a.
Proof.
  intros m a. unfold wview, rmem, restrict_mem_by.
  destruct (hid a) eqn:Eh; [|reflexivity].
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Ef; [|reflexivity].
  pose proof (find_segment_visible1 a seg Ef). congruence.
Qed.

Lemma memory_read1_hidden : forall a,
  hid a = true ->
  match memory_read segs a 1 with Some (b :: _) => Some b | _ => None end = None.
Proof.
  intros a Ha. unfold memory_read. change (Z.of_N 1) with 1%Z.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Ef; [|reflexivity].
  pose proof (find_segment_visible1 a seg Ef). congruence.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ov_byte (m : word -> option byte) (a : word) : option byte :=
  match m a with
  | Some b => Some b
  | None => match memory_read segs a 1 with
            | Some (b :: _) => Some b
            | _ => None
            end
  end.

Lemma ov_byte_restrict : forall m a,
  ov_byte (rmem m) a = if hid a then None else ov_byte m a.
Proof.
  intros m a. unfold ov_byte, rmem, restrict_mem_by.
  destruct (hid a) eqn:Eh; [|reflexivity].
  exact (memory_read1_hidden a Eh).
Qed.

Lemma ov_read_bytes_unfold : forall m a n,
  ov_read_bytes segs m a (S n) =
  match ov_byte m a with
  | Some b => match ov_read_bytes segs m (a + 1) n with
              | Some rest => Some (b :: rest) | None => None end
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma ov_read_bytes_restrict : forall n m a bs,
  ov_read_bytes segs (rmem m) a n = Some bs ->
  ov_read_bytes segs m a n = Some bs /\ range_visible hid a n.
Proof.
  induction n as [|n IH]; intros m a bs H.
  - cbn in H |- *. split; [exact H|]. intros i Hi. lia.
  - rewrite ov_read_bytes_unfold in H |- *. rewrite ov_byte_restrict in H.
    destruct (hid a) eqn:Eh; [discriminate|].
    destruct (ov_byte m a) as [b|]; [|discriminate].
    destruct (ov_read_bytes segs (rmem m) (a + 1) n) as [rest|] eqn:Er; [|discriminate].
    destruct (IH m (a + 1) rest Er) as [-> Hvis].
    split; [exact H|].
    apply range_visible_S. split; [exact Eh | exact Hvis].
Qed.

(* [comment removed for export] *)

Lemma store_ok_restrict : forall n m a,
  store_ok segs (rmem m) a n = true ->
  store_ok segs m a n = true /\ range_visible hid a n.
Proof.
  induction n as [|n IH]; intros m a H.
  - split; [reflexivity|]. intros i Hi. lia.
  - cbn [store_ok] in H |- *. rewrite wview_restrict in H.
    destruct (hid a) eqn:Eh; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) H) as [-> Hvis].
    split; [reflexivity|].
    apply range_visible_S. split; [exact Eh | exact Hvis].
Qed.

Lemma write_to_mem_restrict : forall data m a,
  range_visible hid a (length data) ->
  write_to_mem (rmem m) a data = rmem (write_to_mem m a data).
Proof.
  induction data as [|b data IH]; intros m a Hvis; cbn [write_to_mem length] in *.
  - reflexivity.
  - apply range_visible_S in Hvis. destruct Hvis as [Ha Hvis].
    rewrite <- (IH _ (a + 1) Hvis). f_equal.
    apply functional_extensionality. intros x.
    unfold rmem, restrict_mem_by.
    destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
    unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
    rewrite Ha. reflexivity.
Qed.

Lemma write_to_mem_hidden : forall data m a x,
  range_visible hid a (length data) ->
  hid x = true ->
  write_to_mem m a data x = m x.
Proof.
  induction data as [|b data IH]; intros m a x Hvis Hx; cbn [write_to_mem length] in *.
  - reflexivity.
  - apply range_visible_S in Hvis. destruct Hvis as [Ha Hvis].
    rewrite (IH _ (a + 1) x Hvis Hx).
    destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
    unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x. congruence.
Qed.

(* [comment removed for export] *)

Lemma interp_eff_accesses_restrict : forall t m c m1 rs,
  interp_eff_accesses segs t (rmem m) = MachineOk (@mkAccessReport _ (c, m1) rs) ->
  exists m',
    interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, m') rs)
    /\ m1 = rmem m'
    /\ (forall x, hid x = true -> m' x = m x)
    /\ ranges_visible hid rs.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c m1 rs H; cbn [interp_eff_accesses] in H |- *.
  - inversion H; subst. exists m. repeat split; auto.
    intros a' n' Hin. destruct Hin.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (ov_read_bytes segs (rmem m) a (width_bytes n)) as [bs|] eqn:Er; [|discriminate].
    destruct (ov_read_bytes_restrict _ _ _ _ Er) as [-> Hvis].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (rmem m))
      as [[[c' m''] rs']| |] eqn:Ek; [|discriminate|discriminate].
    cbn in H. inversion H; subst.
    destruct (IH _ _ _ _ _ Ek) as (m' & Hk & -> & Hhid & Hrs).
    rewrite Hk. cbn. exists m'. repeat split; auto.
    intros a' n' [Hin|Hin]; [|exact (Hrs a' n' Hin)].
    inversion Hin; subst. exact Hvis.
  - destruct (store_ok segs (rmem m) a (width_bytes n)) eqn:Es; [|discriminate].
    destruct (store_ok_restrict _ _ _ Es) as [-> Hvis].
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict _ m a) in H by (rewrite Hlen; exact Hvis).
    destruct (interp_eff_accesses segs k
                (rmem (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c' m''] rs']| |] eqn:Ek; [|discriminate|discriminate].
    cbn in H. inversion H; subst.
    destruct (IH _ _ _ _ Ek) as (m' & Hk & -> & Hhid & Hrs).
    rewrite Hk. cbn. exists m'. repeat split; auto.
    + intros x Hx. rewrite (Hhid x Hx). apply write_to_mem_hidden; [rewrite Hlen; exact Hvis | exact Hx].
    + intros a' n' [Hin|Hin]; [|exact (Hrs a' n' Hin)].
      inversion Hin; subst. exact Hvis.
Qed.

(* [comment removed for export] *)

Lemma seg_ov_read_bytes_restrict : forall n m seg a,
  range_visible hid a n ->
  seg_ov_read_bytes (rmem m) seg a n = seg_ov_read_bytes m seg a n.
Proof.
  induction n as [|n IH]; intros m seg a Hvis; [reflexivity|].
  cbn [seg_ov_read_bytes].
  apply range_visible_S in Hvis. destruct Hvis as [Ha Hvis].
  unfold rmem at 1, restrict_mem_by. rewrite Ha. fold rmem.
  rewrite (IH m seg (a + 1) Hvis). reflexivity.
Qed.

Lemma code_read_ov_restrict : forall m a n,
  code_read_ov segs (rmem m) a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Ef; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg); [|reflexivity].
  apply seg_ov_read_bytes_restrict.
  apply (find_segment_visible a (N.to_nat n) seg).
  rewrite N_nat_Z. exact Ef.
Qed.

Lemma fetch_word_ov_restrict : forall m a,
  fetch_word_ov segs (rmem m) a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_ov_restrict : forall m a,
  fetch_half_ov segs (rmem m) a = fetch_half_ov segs m a.
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_any_restrict : forall m a,
  fetch_half_any segs (rmem m) a = fetch_half_any segs m a.
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

Lemma fetch_tail_any_restrict : forall m a,
  fetch_tail_any segs (rmem m) a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

Lemma fetch_failure_restrict : forall m a,
  fetch_failure segs (rmem m) a = fetch_failure segs m a.
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lifts_to (msF : machine_state) (rep1 : access_report machine_state)
    (res : machine_result (access_report machine_state)) : Prop :=
  exists rep,
    res = MachineOk rep
    /\ accessed_ranges _ rep = accessed_ranges _ rep1
    /\ access_value _ rep = unrestrict_by hid msF (access_value _ rep1)
    /\ ranges_visible hid (accessed_ranges _ rep1)
    /\ (forall x, hid x = true -> ms_mem (access_value _ rep1) x = None)
    /\ (forall x, hid x = true -> ms_mem (access_value _ rep) x = ms_mem msF x).

Lemma decode_exec_accesses_restrict : forall msF w rep1,
  decode_exec_accesses segs (restrict_by hid msF) w = MachineOk rep1 ->
  lifts_to msF rep1 (decode_exec_accesses segs msF w).
Proof.
  intros msF w rep1 H. unfold decode_exec_accesses in H |- *.
  destruct (is_ecall w).
  - inversion H; subst; clear H. eexists. split; [reflexivity|].
    cbn. split; [reflexivity|]. split; [|split; [|split]].
    + unfold unrestrict_by, with_mem. cbn. f_equal.
      apply functional_extensionality. intros x.
      unfold unrestrict_mem_by, restrict_mem_by. destruct (hid x); reflexivity.
    + intros a n [].
    + intros x Hx. unfold restrict_mem_by. rewrite Hx. reflexivity.
    + intros x Hx. reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [restrict_by with_mem ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom] in H.
    destruct (interp_eff_accesses segs (exec (Z_to_bv 64 isz) i
                {| c_regs := ms_regs msF; c_fregs := ms_fregs msF; c_pc := ms_pc_val msF;
                   c_fcsr := ms_fcsr msF; c_resv := ms_resv msF |})
                (restrict_mem_by hid (ms_mem msF)))
      as [[[c m1] rs]| |] eqn:Ei; [|discriminate|discriminate].
    cbn in H. inversion H; subst; clear H.
    destruct (interp_eff_accesses_restrict _ _ _ _ _ Ei) as (m' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn. eexists. split; [reflexivity|].
    cbn. split; [reflexivity|]. split; [|split; [|split]].
    + unfold unrestrict_by, with_mem. cbn. f_equal.
      apply functional_extensionality. intros x.
      unfold unrestrict_mem_by, restrict_mem_by.
      unfold rmem, restrict_mem_by.
      destruct (hid x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + exact Hrs.
    + intros x Hx. unfold rmem, restrict_mem_by. rewrite Hx. reflexivity.
    + exact Hhid.
Qed.

Lemma step_accesses_restrict : forall msF rep1,
  step_accesses segs (restrict_by hid msF) = MachineOk rep1 ->
  lifts_to msF rep1 (step_accesses segs msF).
Proof.
  intros msF rep1 H. unfold step_accesses in H |- *.
  change (ms_pc (restrict_by hid msF)) with (ms_pc msF) in H.
  change (ms_mem (restrict_by hid msF)) with (rmem (ms_mem msF)) in H.
  destruct (fetch_word segs (ms_pc msF)) as [w|].
  { exact (decode_exec_accesses_restrict _ _ _ H). }
  rewrite fetch_word_ov_restrict in H.
  destruct (fetch_word_ov segs (ms_mem msF) (ms_pc msF)) as [w|].
  { exact (decode_exec_accesses_restrict _ _ _ H). }
  rewrite fetch_tail_any_restrict in H.
  destruct (fetch_tail_any segs (ms_mem msF) (ms_pc msF)) as [w|].
  { exact (decode_exec_accesses_restrict _ _ _ H). }
  rewrite fetch_failure_restrict in H.
  unfold fetch_failure in H |- *.
  destruct (negb (bv_unsigned (ms_pc msF) `mod` 2 =? 0)%Z); [discriminate|].
  match type of H with (match (if ?c then _ else _) with _ => _ end = _) =>
    destruct c; discriminate end.
Qed.

(* [comment removed for export] *)
Theorem step_restrict_by : forall msF ms1,
  RiscvSemantics.step segs (restrict_by hid msF) = MachineOk ms1 ->
  exists rep,
    step_accesses segs msF = MachineOk rep
    /\ access_value _ rep = unrestrict_by hid msF ms1
    /\ ranges_visible hid (accessed_ranges _ rep)
    /\ (forall x, hid x = true -> ms_mem ms1 x = None)
    /\ (forall x, hid x = true -> ms_mem (access_value _ rep) x = ms_mem msF x).
Proof.
  intros msF ms1 H.
  rewrite <- drop_step_accesses in H.
  destruct (step_accesses segs (restrict_by hid msF)) as [rep1| |] eqn:E1;
    cbn in H; [|discriminate|discriminate].
  inversion H; subst; clear H.
  destruct (step_accesses_restrict _ _ E1) as (rep & -> & Hrs & Hval & Hvis & Hnone & Hhid).
  exists rep. split; [reflexivity|]. split; [exact Hval|].
  split; [rewrite Hrs; exact Hvis|]. split; [exact Hnone | exact Hhid].
Qed.

(* [comment removed for export] *)
Corollary step_restrict_by_step : forall msF ms1,
  RiscvSemantics.step segs (restrict_by hid msF) = MachineOk ms1 ->
  RiscvSemantics.step segs msF = MachineOk (unrestrict_by hid msF ms1).
Proof.
  intros msF ms1 H.
  destruct (step_restrict_by _ _ H) as (rep & Hsa & Hval & _).
  rewrite <- drop_step_accesses, Hsa. cbn. f_equal. exact Hval.
Qed.

(* [comment removed for export] *)

Lemma restrict_unrestrict_by : forall msF ms1,
  (forall x, hid x = true -> ms_mem ms1 x = None) ->
  restrict_by hid (unrestrict_by hid msF ms1) = ms1.
Proof.
  intros msF [regs fregs pc svc resv fcsr m rom] Hnone.
  unfold restrict_by, unrestrict_by, with_mem. cbn. f_equal.
  apply functional_extensionality. intros x.
  unfold restrict_mem_by, unrestrict_mem_by. cbn in Hnone.
  destruct (hid x) eqn:Hx; [symmetry; exact (Hnone x Hx) | reflexivity].
Qed.

Lemma unrestrict_by_hidden : forall msF ms1 x,
  hid x = true -> ms_mem (unrestrict_by hid msF ms1) x = ms_mem msF x.
Proof.
  intros msF ms1 x Hx. unfold unrestrict_by, with_mem, unrestrict_mem_by. cbn.
  rewrite Hx. reflexivity.
Qed.

Lemma unrestrict_by_visible : forall msF ms1 x,
  hid x = false -> ms_mem (unrestrict_by hid msF ms1) x = ms_mem ms1 x.
Proof.
  intros msF ms1 x Hx. unfold unrestrict_by, with_mem, unrestrict_mem_by. cbn.
  rewrite Hx. reflexivity.
Qed.

Lemma unrestrict_by_idem : forall msF ms1 ms2,
  unrestrict_by hid (unrestrict_by hid msF ms1) ms2 = unrestrict_by hid msF ms2.
Proof.
  intros msF ms1 ms2. unfold unrestrict_by, with_mem. cbn. f_equal.
  apply functional_extensionality. intros x. unfold unrestrict_mem_by.
  destruct (hid x); reflexivity.
Qed.

Lemma restrict_by_mem_visible : forall ms x,
  hid x = false -> ms_mem (restrict_by hid ms) x = ms_mem ms x.
Proof.
  intros ms x Hx. unfold restrict_by, with_mem, restrict_mem_by. cbn. rewrite Hx. reflexivity.
Qed.

Lemma restrict_by_mem_hidden : forall ms x,
  hid x = true -> ms_mem (restrict_by hid ms) x = None.
Proof.
  intros ms x Hx. unfold restrict_by, with_mem, restrict_mem_by. cbn. rewrite Hx. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma restrict_by_regs : forall ms, ms_regs (restrict_by hid ms) = ms_regs ms.
Proof. reflexivity. Qed.
Lemma restrict_by_pc : forall ms, ms_pc (restrict_by hid ms) = ms_pc ms.
Proof. reflexivity. Qed.
Lemma restrict_by_svc : forall ms, ms_svc_pending (restrict_by hid ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma restrict_by_rom : forall ms, ms_rom (restrict_by hid ms) = ms_rom ms.
Proof. reflexivity. Qed.
Lemma unrestrict_by_regs : forall msF ms, ms_regs (unrestrict_by hid msF ms) = ms_regs ms.
Proof. reflexivity. Qed.
Lemma unrestrict_by_pc : forall msF ms, ms_pc (unrestrict_by hid msF ms) = ms_pc ms.
Proof. reflexivity. Qed.
Lemma unrestrict_by_svc : forall msF ms, ms_svc_pending (unrestrict_by hid msF ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma unrestrict_by_rom : forall msF ms, ms_rom (unrestrict_by hid msF ms) = ms_rom ms.
Proof. reflexivity. Qed.

End HidSem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition seg_disjoint_rangeb (seg : Segment) (r : word * word) : bool :=
  let sb := Z.of_N (seg_base seg) in
  let se := (sb + Z.of_N (seg_size seg))%Z in
  let lo := bv_unsigned (fst r) in
  let hi := (lo + bv_unsigned (snd r))%Z in
  ((se <=? lo) || (hi <=? sb))%Z.

Definition segs_nowrapb (segs : list Segment) : bool :=
  forallb (fun seg => (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 2 ^ 64)%Z) segs.

Definition range_nowrapb (r : word * word) : bool :=
  (bv_unsigned (fst r) + bv_unsigned (snd r) <=? 2 ^ 64)%Z.

Definition lazy_range_okb (segs : list Segment) (r : word * word) : bool :=
  range_nowrapb r && forallb (fun seg => seg_disjoint_rangeb seg r) segs.

Definition lazy_ranges_okb (segs : list Segment) (L : list (word * word)) : bool :=
  segs_nowrapb segs && forallb (lazy_range_okb segs) L.

Lemma lazy_ranges_okb_nil : forall segs, lazy_ranges_okb segs [] = segs_nowrapb segs.
Proof. intros segs. unfold lazy_ranges_okb. cbn. apply andb_true_r. Qed.

Lemma lazy_ranges_okb_cons : forall segs r L,
  lazy_ranges_okb segs (r :: L) = true <->
  lazy_range_okb segs r = true /\ lazy_ranges_okb segs L = true.
Proof.
  intros segs r L. unfold lazy_ranges_okb. cbn [forallb].
  rewrite !andb_true_iff. tauto.
Qed.

Lemma lazy_ranges_okb_app : forall segs L1 L2,
  lazy_ranges_okb segs (L1 ++ L2) = true <->
  lazy_ranges_okb segs L1 = true /\ lazy_ranges_okb segs L2 = true.
Proof.
  intros segs L1 L2. unfold lazy_ranges_okb. rewrite forallb_app, !andb_true_iff. tauto.
Qed.

Lemma lazy_ranges_okb_In : forall segs L r,
  lazy_ranges_okb segs L = true -> In r L -> lazy_range_okb segs r = true.
Proof.
  intros segs L r H Hin. unfold lazy_ranges_okb in H. apply andb_true_iff in H.
  destruct H as [_ H]. rewrite forallb_forall in H. exact (H r Hin).
Qed.

(* [comment removed for export] *)
Lemma lazy_range_okb_intro : forall segs lo sz,
  (bv_unsigned lo + bv_unsigned sz <= 2 ^ 64)%Z ->
  (forall seg, In seg segs ->
     (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= bv_unsigned lo)%Z
     \/ (bv_unsigned lo + bv_unsigned sz <= Z.of_N (seg_base seg))%Z) ->
  lazy_range_okb segs (lo, sz) = true.
Proof.
  intros segs lo sz Hnw Hdis. unfold lazy_range_okb, range_nowrapb. cbn [fst snd].
  apply andb_true_iff. split; [apply Z.leb_le; exact Hnw|].
  apply forallb_forall. intros seg Hin. unfold seg_disjoint_rangeb. cbn [fst snd].
  apply orb_true_iff. destruct (Hdis seg Hin) as [H|H]; [left|right]; apply Z.leb_le; exact H.
Qed.

(* [comment removed for export] *)
Lemma lazy_range_okb_above : forall segs lo sz top,
  (forall seg, In seg segs -> (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= top)%Z) ->
  (top <= bv_unsigned lo)%Z ->
  (bv_unsigned lo + bv_unsigned sz <= 2 ^ 64)%Z ->
  lazy_range_okb segs (lo, sz) = true.
Proof.
  intros segs lo sz top Hsegs Htop Hnw. apply lazy_range_okb_intro; [exact Hnw|].
  intros seg Hin. left. pose proof (Hsegs seg Hin). lia.
Qed.

Lemma in_rangesb_true : forall a rs,
  in_rangesb a rs = true <->
  exists lo sz, In (lo, sz) rs
    /\ (bv_unsigned lo <= bv_unsigned a < bv_unsigned lo + bv_unsigned sz)%Z.
Proof.
  intros a rs. unfold in_rangesb. rewrite existsb_exists. split.
  - intros ([lo sz] & Hin & Hr). unfold zin_rangeb in Hr. cbn [fst snd] in Hr.
    apply andb_true_iff in Hr. destruct Hr as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists lo, sz. auto.
  - intros (lo & sz & Hin & Hr). exists (lo, sz). split; [exact Hin|].
    unfold zin_rangeb. cbn [fst snd]. apply andb_true_iff. split;
      [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_rangesb_false : forall a rs,
  in_rangesb a rs = false <->
  forall lo sz, In (lo, sz) rs ->
    ~ (bv_unsigned lo <= bv_unsigned a < bv_unsigned lo + bv_unsigned sz)%Z.
Proof.
  intros a rs. split.
  - intros Hf lo sz Hin Hr.
    assert (Ht : in_rangesb a rs = true) by (apply in_rangesb_true; eauto).
    congruence.
  - intros H. destruct (in_rangesb a rs) eqn:E; [|reflexivity].
    apply in_rangesb_true in E. destruct E as (lo & sz & Hin & Hr).
    exfalso. exact (H lo sz Hin Hr).
Qed.

Lemma lazy_ranges_ok_avoids : forall segs L S,
  lazy_ranges_okb segs L = true -> hid_avoids_segs segs (hiddenb L S).
Proof.
  intros segs L S Hok. unfold lazy_ranges_okb in Hok. apply andb_true_iff in Hok.
  destruct Hok as [Hnw HL]. unfold segs_nowrapb in Hnw.
  rewrite forallb_forall in Hnw. rewrite forallb_forall in HL.
  split.
  - intros a seg Hin Hcov.
    unfold hiddenb. destruct (in_rangesb a L) eqn:EL; [|reflexivity].
    apply in_rangesb_true in EL. destruct EL as (lo & sz & HinL & Hr).
    specialize (HL (lo, sz) HinL). unfold lazy_range_okb in HL.
    apply andb_true_iff in HL. destruct HL as [_ HL]. rewrite forallb_forall in HL.
    specialize (HL seg Hin). unfold seg_disjoint_rangeb in HL. cbn [fst snd] in HL.
    unfold seg_covers in Hcov. apply orb_true_iff in HL.
    destruct HL as [Hd|Hd]; apply Z.leb_le in Hd; exfalso; lia.
  - intros seg Hin. specialize (Hnw seg Hin). apply Z.leb_le in Hnw. exact Hnw.
Qed.

(* [comment removed for export] *)
Lemma hiddenb_visible_S : forall L S a,
  in_rangesb a S = true -> hiddenb L S a = false.
Proof. intros L S a H. unfold hiddenb. rewrite H. apply andb_false_r. Qed.

Lemma hiddenb_outside_L : forall L S a,
  in_rangesb a L = false -> hiddenb L S a = false.
Proof. intros L S a H. unfold hiddenb. rewrite H. reflexivity. Qed.

Lemma hiddenb_true_iff : forall L S a,
  hiddenb L S a = true <-> in_rangesb a L = true /\ in_rangesb a S = false.
Proof.
  intros L S a. unfold hiddenb. rewrite andb_true_iff, negb_true_iff. tauto.
Qed.

Lemma restrict_mem_in_window : forall L S m a,
  in_rangesb a S = true -> restrict_mem L S m a = m a.
Proof.
  intros L S m a H. unfold restrict_mem, restrict_mem_by. rewrite (hiddenb_visible_S L S a H). reflexivity.
Qed.

Lemma restrict_mem_outside_lazy : forall L S m a,
  in_rangesb a L = false -> restrict_mem L S m a = m a.
Proof.
  intros L S m a H. unfold restrict_mem, restrict_mem_by. rewrite (hiddenb_outside_L L S a H). reflexivity.
Qed.

Lemma restrict_mem_hidden : forall L S m a,
  hiddenb L S a = true -> restrict_mem L S m a = None.
Proof. intros L S m a H. unfold restrict_mem, restrict_mem_by. rewrite H. reflexivity. Qed.

Lemma ms_mem_restrict : forall L S ms,
  ms_mem (restrict L S ms) = restrict_mem L S (ms_mem ms).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem step_restrict : forall segs L S msF ms1,
  lazy_ranges_okb segs L = true ->
  RiscvSemantics.step segs (restrict L S msF) = MachineOk ms1 ->
  exists rep,
    step_accesses segs msF = MachineOk rep
    /\ access_value _ rep = unrestrict_to L S msF ms1
    /\ ranges_visible (hiddenb L S) (accessed_ranges _ rep)
    /\ (forall a, hiddenb L S a = true -> ms_mem ms1 a = None)
    /\ (forall a, hiddenb L S a = true -> ms_mem (access_value _ rep) a = ms_mem msF a).
Proof.
  intros segs L S msF ms1 Hok Hstep.
  exact (step_restrict_by segs (hiddenb L S) (lazy_ranges_ok_avoids segs L S Hok) msF ms1 Hstep).
Qed.

Corollary step_restrict_step : forall segs L S msF ms1,
  lazy_ranges_okb segs L = true ->
  RiscvSemantics.step segs (restrict L S msF) = MachineOk ms1 ->
  RiscvSemantics.step segs msF = MachineOk (unrestrict_to L S msF ms1).
Proof.
  intros segs L S msF ms1 Hok Hstep.
  exact (step_restrict_by_step segs (hiddenb L S) (lazy_ranges_ok_avoids segs L S Hok) msF ms1 Hstep).
Qed.

Lemma restrict_unrestrict_to : forall L S msF ms1,
  (forall a, hiddenb L S a = true -> ms_mem ms1 a = None) ->
  restrict L S (unrestrict_to L S msF ms1) = ms1.
Proof. intros L S. exact (restrict_unrestrict_by (hiddenb L S)). Qed.

Lemma unrestrict_to_idem : forall L S msF ms1 ms2,
  unrestrict_to L S (unrestrict_to L S msF ms1) ms2 = unrestrict_to L S msF ms2.
Proof. intros L S. exact (unrestrict_by_idem (hiddenb L S)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_alignedb (r : word * word) : bool :=
  ((bv_unsigned (fst r) mod page_size =? 0) && (bv_unsigned (snd r) mod page_size =? 0))%Z.

Definition windows_okb (S : list (word * word)) : bool := forallb page_alignedb S.

(* [comment removed for export] *)
Definition cl_lo (r : word * word) : Z := (bv_unsigned (fst r) / page_size * page_size)%Z.
Definition cl_hi (r : word * word) : Z :=
  ((bv_unsigned (fst r) + bv_unsigned (snd r) + page_size - 1) / page_size * page_size)%Z.
Definition win_npagesZ (r : word * word) : Z := ((cl_hi r - cl_lo r) / page_size)%Z.

Lemma cl_bounds : forall r,
  (0 <= cl_lo r <= bv_unsigned (fst r))%Z
  /\ (bv_unsigned (fst r) + bv_unsigned (snd r) <= cl_hi r < bv_unsigned (fst r) + bv_unsigned (snd r) + page_size)%Z
  /\ (cl_lo r mod page_size = 0)%Z /\ (cl_hi r mod page_size = 0)%Z
  /\ (0 <= win_npagesZ r <= bv_unsigned (snd r) / page_size + 2)%Z
  /\ (win_npagesZ r * page_size = cl_hi r - cl_lo r)%Z.
Proof.
  intros [b n]. unfold win_npagesZ, cl_lo, cl_hi. cbn [fst snd].
  pose proof (bv_unsigned_in_range 64 b) as Hb. pose proof (bv_unsigned_in_range 64 n) as Hn.
  set (lo := bv_unsigned b) in *. set (sz := bv_unsigned n) in *.
  pose proof (Z.div_mod lo page_size ltac:(unfold page_size; lia)) as D1.
  pose proof (Z.mod_pos_bound lo page_size ltac:(unfold page_size; lia)) as M1.
  pose proof (Z.div_mod (lo + sz + page_size - 1) page_size ltac:(unfold page_size; lia)) as D2.
  pose proof (Z.mod_pos_bound (lo + sz + page_size - 1) page_size ltac:(unfold page_size; lia)) as M2.
  pose proof (Z.div_mod sz page_size ltac:(unfold page_size; lia)) as D3.
  pose proof (Z.mod_pos_bound sz page_size ltac:(unfold page_size; lia)) as M3.
  set (q1 := (lo / page_size)%Z) in *. set (q2 := ((lo + sz + page_size - 1) / page_size)%Z) in *.
  set (q3 := (sz / page_size)%Z) in *.
  replace (q2 * page_size - q1 * page_size)%Z with ((q2 - q1) * page_size)%Z by lia.
  rewrite Z.div_mul by (unfold page_size; lia).
  unfold page_size in *.
  repeat split; first [apply Z_mod_mult | lia].
Qed.

(* [comment removed for export] *)
Definition win_npages (r : word * word) : nat := Z.to_nat (win_npagesZ r).

Definition win_page (r : word * word) (i : nat) : word :=
  Z_to_bv 64 (cl_lo r + page_size * Z.of_nat i).

Definition win_pages (r : word * word) : list word :=
  map (win_page r) (seq 0 (win_npages r)).

Fixpoint all_pages (S : list (word * word)) : list word :=
  match S with
  | [] => []
  | r :: S' => win_pages r ++ all_pages S'
  end.

(* [comment removed for export] *)
Fixpoint pages_total (S : list (word * word)) : Z :=
  match S with
  | [] => 0
  | r :: S' => win_npagesZ r + pages_total S'
  end%Z.

Fixpoint wbudget (S : list (word * word)) : Z :=
  match S with
  | [] => 0
  | r :: S' => bv_unsigned (snd r) / page_size + 2 + wbudget S'
  end%Z.

Lemma pages_total_nonneg : forall S, (0 <= pages_total S)%Z.
Proof.
  induction S as [|r S IH]; cbn [pages_total]; [lia|].
  destruct (cl_bounds r) as (_ & _ & _ & _ & Hn & _). lia.
Qed.

Lemma pages_total_le_wbudget : forall S, (pages_total S <= wbudget S)%Z.
Proof.
  induction S as [|r S IH]; cbn [pages_total wbudget]; [lia|].
  destruct (cl_bounds r) as (_ & _ & _ & _ & Hn & _). lia.
Qed.

Lemma all_pages_length : forall S,
  Z.of_nat (length (all_pages S)) = pages_total S.
Proof.
  induction S as [|r S IH]; cbn [all_pages pages_total length]; [reflexivity|].
  rewrite length_app, Nat2Z.inj_add, IH. unfold win_pages.
  rewrite length_map, length_seq. unfold win_npages.
  pose proof (cl_bounds r). rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma all_pages_app : forall S1 S2, all_pages (S1 ++ S2) = all_pages S1 ++ all_pages S2.
Proof.
  induction S1 as [|r S1 IH]; intros S2; cbn [all_pages app]; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m
  = (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record lazy_inv (L S : list (word * word)) (m : Model) : Prop := {
  li_lazy   : m_vm_lazy m = L;
  li_nodup  : List.NoDup (m_vm_materialized m);
  li_incl   : incl (m_vm_materialized m) (all_pages S);
  li_budget : (eager_used m + pages_total S * page_size <= vm_limit (m_vmmaps m))%Z
}.

(* [comment removed for export] *)
Definition same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_materialized_refl : forall m, same_but_materialized m m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : forall m1 m2 m3,
  same_but_materialized m1 m2 -> same_but_materialized m2 m3 -> same_but_materialized m1 m3.
Proof.
  unfold same_but_materialized.
  intros [fd [maps lazy mat] io fs proc lim tm] m2 m3 -> ->. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_but_materialized_fields : forall m m',
  same_but_materialized m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m.
Proof.
  intros [fd [maps lazy mat] io fs proc lim tm] m' ->. cbn. repeat split; reflexivity.
Qed.

Lemma same_but_materialized_halted : forall m m',
  same_but_materialized m m' -> m_halted m' = m_halted m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_fs : forall m m',
  same_but_materialized m m' -> m_fs m' = m_fs m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_fds : forall m m',
  same_but_materialized m m' -> m_fds m' = m_fds m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_vmmaps : forall m m',
  same_but_materialized m m' -> m_vmmaps m' = m_vmmaps m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_lazy : forall m m',
  same_but_materialized m m' -> m_vm_lazy m' = m_vm_lazy m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_eager : forall m m',
  same_but_materialized m m' -> eager_used m' = eager_used m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_with_vm_backing : forall m pages,
  same_but_materialized m (with_vm_backing (m_vm_lazy m) pages m).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] pages. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_unsigned_add_Z_to_bv : forall (a : word) z,
  bv_unsigned (a + Z_to_bv 64 z) = ((bv_unsigned a + z) mod 2 ^ 64)%Z.
Proof.
  intros a z. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64)%Z. apply Zplus_mod_idemp_r.
Qed.

(* [comment removed for export] *)
Lemma page_base_of_unsigned : forall z,
  (0 <= z)%Z ->
  bv_unsigned (page_base_of z) = (((z mod 2 ^ 64) / page_size) * page_size)%Z.
Proof.
  intros z Hz. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64)%Z.
  set (M := (2 ^ 64)%Z). set (ps := page_size).
  assert (HM : M = (ps * 2 ^ 52)%Z) by reflexivity.
  assert (Hps : (0 < ps)%Z) by (unfold ps, page_size; lia).
  set (q := (z / M)%Z). set (r := (z mod M)%Z).
  assert (Hzqr : z = (M * q + r)%Z) by (unfold q, r; apply Z.div_mod; unfold M; lia).
  assert (Hr : (0 <= r < M)%Z) by (unfold r; apply Z.mod_pos_bound; unfold M; lia).
  assert (Hdiv : (z / ps = 2 ^ 52 * q + r / ps)%Z).
  { rewrite Hzqr, HM. replace (ps * 2 ^ 52 * q + r)%Z with ((2 ^ 52 * q) * ps + r)%Z by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  rewrite Hdiv.
  replace ((2 ^ 52 * q + r / ps) * ps)%Z with (r / ps * ps + q * M)%Z by flia.
  rewrite Z.mod_add by (unfold M; lia).
  apply Z.mod_small.
  pose proof (Z.mul_div_le r ps Hps) as H1.
  assert (0 <= r / ps)%Z by (apply Z.div_pos; lia).
  flia.
Qed.

(* [comment removed for export] *)
Lemma page_of_access_byte : forall (a : word) (k : nat),
  let x := bv_unsigned (a + Z_to_bv 64 (Z.of_nat k)) in
  let p := bv_unsigned (page_base_of (bv_unsigned a + Z.of_nat k)) in
  p = ((x / page_size) * page_size)%Z /\ (p <= x < p + page_size)%Z.
Proof.
  intros a k. cbn zeta.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  rewrite page_base_of_unsigned by lia.
  rewrite <- bv_unsigned_add_Z_to_bv.
  set (x := bv_unsigned (a + Z_to_bv 64 (Z.of_nat k))).
  pose proof (bv_unsigned_in_range 64 (a + Z_to_bv 64 (Z.of_nat k))) as Hx. fold x in Hx.
  split; [reflexivity|].
  pose proof (Z.div_mod x page_size ltac:(unfold page_size; lia)).
  pose proof (Z.mod_pos_bound x page_size ltac:(unfold page_size; lia)).
  unfold page_size in *. lia.
Qed.

(* [comment removed for export] *)
Lemma window_page_in_all_pages : forall S (x : word) (p : word),
  in_rangesb x S = true ->
  bv_unsigned p = ((bv_unsigned x / page_size) * page_size)%Z ->
  In p (all_pages S).
Proof.
  induction S as [|r S IH]; intros x p Hin Hp.
  - cbn in Hin. discriminate.
  - cbn [all_pages]. apply in_app_iff.
    unfold in_rangesb in Hin. cbn [existsb] in Hin. apply orb_true_iff in Hin.
    destruct Hin as [Hin | Hin]; [left | right; apply (IH x p); [exact Hin | exact Hp]].
    clear IH.
    pose proof (cl_bounds r) as (C1 & C2 & C3 & C4 & C5 & C6).
    destruct r as [b n]. unfold zin_rangeb in Hin. cbn [fst snd] in Hin, C1, C2.
    unfold cl_lo, cl_hi, win_npagesZ in *. cbn [fst snd] in *.
    apply andb_true_iff in Hin. destruct Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (bv_unsigned_in_range 64 x) as Hx.
    set (ux := bv_unsigned x) in *. set (lo := bv_unsigned b) in *. set (sz := bv_unsigned n) in *.
    assert (Hlo : (lo / page_size <= ux / page_size)%Z) by (apply Z.div_le_mono; unfold page_size; lia).
    assert (Hhi : (ux / page_size + 1 <= (lo + sz + page_size - 1) / page_size)%Z).
    { replace (ux / page_size + 1)%Z with ((ux + 1 * page_size) / page_size)%Z
        by (rewrite Z.div_add by (unfold page_size; lia); reflexivity).
      apply Z.div_le_mono; unfold page_size; lia. }
    unfold win_pages. apply in_map_iff. exists (Z.to_nat (ux / page_size - lo / page_size))%Z. split.
    + unfold win_page, cl_lo. cbn [fst]. apply bv_eq. rewrite Z_to_bv_unsigned.
      rewrite Z2Nat.id by lia. fold lo.
      replace (lo / page_size * page_size + page_size * (ux / page_size - lo / page_size))%Z
        with (ux / page_size * page_size)%Z by lia.
      rewrite <- Hp. apply bv_wrap_small. apply bv_unsigned_in_range.
    + apply in_seq. unfold win_npages, win_npagesZ, cl_lo, cl_hi. cbn [fst snd]. fold lo sz.
      replace ((lo + sz + page_size - 1) / page_size * page_size - lo / page_size * page_size)%Z
        with (((lo + sz + page_size - 1) / page_size - lo / page_size) * page_size)%Z by lia.
      rewrite Z.div_mul by (unfold page_size; lia).
      clear - Hlo Hhi. generalize dependent (ux / page_size)%Z. generalize dependent (lo / page_size)%Z.
      generalize dependent ((lo + sz + page_size - 1) / page_size)%Z. intros q1 q2 q3 Hlo Hhi. lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_addr : forall L (p x : word),
  page_in_ranges p L = true ->
  (bv_unsigned p <= bv_unsigned x < bv_unsigned p + page_size)%Z ->
  in_rangesb x L = true.
Proof.
  intros L p x Hp Hx. unfold page_in_ranges in Hp. apply existsb_exists in Hp.
  destruct Hp as ([lo sz] & Hin & Ht). cbn [fst snd] in Ht.
  apply andb_true_iff in Ht. destruct Ht as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply in_rangesb_true. exists lo, sz. split; [exact Hin | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_mem_In : forall p pages, page_mem p pages = true <-> In p pages.
Proof.
  intros p pages. unfold page_mem. rewrite existsb_exists. split.
  - intros (q & Hin & He). unfold bv_eqb in He. apply Z.eqb_eq in He. apply bv_eq in He. subst; exact Hin.
  - intros Hin. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

Lemma NoDup_page_insert : forall q pages, List.NoDup pages -> List.NoDup (page_insert q pages).
Proof.
  intros q pages H. unfold page_insert. destruct (page_mem q pages) eqn:E; [exact H|].
  constructor; [|exact H]. intros Hin. apply page_mem_In in Hin. congruence.
Qed.

Lemma NoDup_access_pages_acc : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages H; [exact H|].
  apply IH. apply NoDup_page_insert. exact H.
Qed.

Lemma NoDup_accesses_pages : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages H; [exact H|].
  apply IH. apply NoDup_access_pages_acc. exact H.
Qed.

(* [comment removed for export] *)
Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages];
    intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
        as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k.
      split; [right; exact Hin | split; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma newly_materialized_pages_visible : forall L S mat rs,
  ranges_visible (hiddenb L S) rs ->
  let new := newly_materialized_pages L mat rs in
  List.NoDup new
  /\ (forall p, In p new -> ~ In p mat)
  /\ incl new (all_pages S).
Proof.
  intros L S mat rs Hvis. cbn zeta.
  unfold newly_materialized_pages. split; [|split].
  - apply NoDup_filter. apply NoDup_accesses_pages. constructor.
  - intros p Hp Hin. apply filter_In in Hp. destruct Hp as [_ Hp].
    apply andb_true_iff in Hp. destruct Hp as [_ Hm].
    apply page_mem_In in Hin. rewrite Hin in Hm. discriminate.
  - intros p Hp. apply filter_In in Hp. destruct Hp as [Hacc Hp].
    apply andb_true_iff in Hp. destruct Hp as [HpL _].
    destruct (accesses_pages_in rs [] p Hacc) as [[] | (a & n & k & Hin & Hk & ->)].
    pose proof (Hvis a n Hin k Hk) as Hhid.
    destruct (page_of_access_byte a k) as [Hpx Hbr].
    set (x := a + Z_to_bv 64 (Z.of_nat k)) in *.
    unfold hiddenb in Hhid.
    destruct (in_rangesb x S) eqn:ES.
    + exact (window_page_in_all_pages S x _ ES Hpx).
    + rewrite (page_in_ranges_addr L _ x HpL Hbr) in Hhid. discriminate.
Qed.

Theorem materialize_restrict : forall L S m rs,
  lazy_inv L S m ->
  ranges_visible (hiddenb L S) rs ->
  exists pages,
    materialize_model_accesses m rs = Some (with_vm_backing (m_vm_lazy m) pages m)
    /\ lazy_inv L S (with_vm_backing (m_vm_lazy m) pages m).
Proof.
  intros L S m rs Hinv Hvis.
  destruct Hinv as [Hlazy Hnd Hincl Hbud].
  pose proof (newly_materialized_pages_visible L S (m_vm_materialized m) rs Hvis) as Hnew.
  cbn zeta in Hnew. destruct Hnew as (Hnnd & Hfresh & Hnincl).
  set (new := newly_materialized_pages L (m_vm_materialized m) rs) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m))
    by (apply NoDup_app; assumption).
  assert (Happ_incl : incl (new ++ m_vm_materialized m) (all_pages S))
    by (apply incl_app; assumption).
  assert (Hlen : (Z.of_nat (length (new ++ m_vm_materialized m)) <= pages_total S)%Z).
  { rewrite <- all_pages_length. apply Nat2Z.inj_le. apply NoDup_incl_length; assumption. }
  assert (Hgoal : forall pages,
            (pages = m_vm_materialized m \/ pages = new ++ m_vm_materialized m) ->
            lazy_inv L S (with_vm_backing (m_vm_lazy m) pages m)).
  { intros pages Hp.
    destruct m as [fd [maps lazy mat] io fs proc lim tm]. cbn in *. subst lazy.
    split; cbn.
    - reflexivity.
    - destruct Hp as [-> | ->]; assumption.
    - destruct Hp as [-> | ->]; assumption.
    - exact Hbud. }
  unfold materialize_model_accesses, materialize_accesses.
  replace (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) rs) with new
    by (unfold new; rewrite Hlazy; reflexivity).
  destruct new as [|p new'] eqn:En.
  - exists (m_vm_materialized m). split; [reflexivity|]. apply Hgoal. left; reflexivity.
  - rewrite vm_backing_used_split.
    rewrite length_app, Nat2Z.inj_add in Hlen.
    match goal with |- context [if ?c then _ else _] => replace c with true end.
    + exists ((p :: new') ++ m_vm_materialized m). split; [reflexivity|].
      apply Hgoal. right; reflexivity.
    + symmetry. apply Z.leb_le. clear - Hlen Hbud. unfold page_size in *. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HiddenInv.
Variables L S : list (word * word).

(* [comment removed for export] *)
Definition hidden_inv (P : option byte -> Prop) (msF : machine_state) : Prop :=
  forall a, hiddenb L S a = true -> P (ms_mem msF a).

Definition hidden_const : machine_state -> Prop :=
  hidden_inv (fun o => exists b, o = Some b).

Definition hidden_zero : machine_state -> Prop :=
  hidden_inv (fun o => o = Some (Z_to_bv 8 0)).

Lemma hidden_inv_unrestrict : forall P msF ms1,
  hidden_inv P msF -> hidden_inv P (unrestrict_to L S msF ms1).
Proof.
  intros P msF ms1 H a Ha. unfold unrestrict_to.
  rewrite (unrestrict_by_hidden (hiddenb L S) msF ms1 a Ha). exact (H a Ha).
Qed.

(* [comment removed for export] *)
Lemma hidden_inv_frame : forall P msF msF',
  hidden_inv P msF ->
  (forall a, hiddenb L S a = true -> ms_mem msF' a = ms_mem msF a) ->
  hidden_inv P msF'.
Proof. intros P msF msF' H Hf a Ha. rewrite (Hf a Ha). exact (H a Ha). Qed.

Lemma hidden_inv_weaken : forall (P Q : option byte -> Prop) msF,
  (forall o, P o -> Q o) -> hidden_inv P msF -> hidden_inv Q msF.
Proof. intros P Q msF HPQ H a Ha. apply HPQ. exact (H a Ha). Qed.

Lemma hidden_zero_const : forall msF, hidden_zero msF -> hidden_const msF.
Proof. intros msF. apply hidden_inv_weaken. intros o ->. eexists; reflexivity. Qed.

Lemma unrestrict_restrict_self : forall msF,
  unrestrict_to L S msF (restrict L S msF) = msF.
Proof.
  intros [regs fregs pc svc resv fcsr m rom].
  unfold unrestrict_to, restrict, unrestrict_by, restrict_by, with_mem. cbn. f_equal.
  apply functional_extensionality. intros x.
  unfold unrestrict_mem_by, restrict_mem_by. destruct (hiddenb L S x); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma restrict_mem_le : forall m a b,
  restrict_mem L S m a = Some b -> m a = Some b.
Proof.
  intros m a b. unfold restrict_mem, restrict_mem_by. destruct (hiddenb L S a); [discriminate | auto].
Qed.

End HiddenInv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Windows.
Variable L : list (word * word).

(* [comment removed for export] *)

Lemma lazy_inv_intro : forall S m,
  m_vm_lazy m = L ->
  m_vm_materialized m = [] ->
  (eager_used m + pages_total S * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv L S m.
Proof.
  intros S m Hl Hm Hb. split; try assumption.
  - rewrite Hm. constructor.
  - rewrite Hm. intros p [].
Qed.

(* [comment removed for export] *)
Lemma lazy_inv_windows_mono : forall S S' m,
  lazy_inv L S m ->
  incl (all_pages S) (all_pages S') ->
  (eager_used m + pages_total S' * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv L S' m.
Proof.
  intros S S' m [Hl Hnd Hincl Hb] Hsub Hb'. split; try assumption.
  eapply incl_tran; eassumption.
Qed.

Lemma windows_okb_cons : forall W S,
  windows_okb (W :: S) = page_alignedb W && windows_okb S.
Proof. reflexivity. Qed.

Lemma pages_total_cons : forall W S,
  pages_total (W :: S) = (win_npagesZ W + pages_total S)%Z.
Proof. reflexivity. Qed.

Lemma wbudget_cons : forall W S,
  wbudget (W :: S) = (bv_unsigned (snd W) / page_size + 2 + wbudget S)%Z.
Proof. reflexivity. Qed.

Lemma pages_total_app : forall S1 S2,
  pages_total (S1 ++ S2) = (pages_total S1 + pages_total S2)%Z.
Proof. induction S1 as [|r S1 IH]; intros S2; cbn [pages_total app]; [lia | rewrite IH; lia]. Qed.

Lemma wbudget_app : forall S1 S2,
  wbudget (S1 ++ S2) = (wbudget S1 + wbudget S2)%Z.
Proof. induction S1 as [|r S1 IH]; intros S2; cbn [wbudget app]; [lia | rewrite IH; lia]. Qed.

(* [comment removed for export] *)
Lemma lazy_inv_open_window : forall W S m,
  lazy_inv L S m ->
  (eager_used m + pages_total (W :: S) * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv L (W :: S) m.
Proof.
  intros W S m Hinv Hb. eapply lazy_inv_windows_mono; [exact Hinv | | exact Hb].
  cbn [all_pages]. apply incl_appr. apply incl_refl.
Qed.

(* [comment removed for export] *)
Lemma lazy_inv_open_window_wb : forall W S m,
  lazy_inv L S m ->
  (eager_used m + (bv_unsigned (snd W) / page_size + 2 + pages_total S) * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv L (W :: S) m.
Proof.
  intros W S m Hinv Hb. apply lazy_inv_open_window; [exact Hinv|].
  rewrite pages_total_cons. pose proof (cl_bounds W). unfold page_size in *. nia.
Qed.

Lemma lazy_inv_open_windows_app : forall S1 S m,
  lazy_inv L S m ->
  (eager_used m + pages_total (S1 ++ S) * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv L (S1 ++ S) m.
Proof.
  intros S1 S m Hinv Hb. eapply lazy_inv_windows_mono; [exact Hinv | | exact Hb].
  rewrite all_pages_app. apply incl_appr. apply incl_refl.
Qed.

(* [comment removed for export] *)
Lemma lazy_inv_budget : forall S m,
  lazy_inv L S m ->
  (eager_used m + pages_total S * page_size <= vm_limit (m_vmmaps m))%Z.
Proof. intros S m H. exact (li_budget _ _ _ H). Qed.

(* [comment removed for export] *)

Lemma in_rangesb_cons : forall a W S,
  in_rangesb a (W :: S) = zin_rangeb (bv_unsigned a) W || in_rangesb a S.
Proof. reflexivity. Qed.

Lemma in_rangesb_app : forall a S1 S2,
  in_rangesb a (S1 ++ S2) = in_rangesb a S1 || in_rangesb a S2.
Proof. intros a S1 S2. unfold in_rangesb. apply existsb_app. Qed.

Lemma hiddenb_cons_window : forall W S a,
  hiddenb L (W :: S) a = hiddenb L S a && negb (zin_rangeb (bv_unsigned a) W).
Proof.
  intros W S a. unfold hiddenb. rewrite in_rangesb_cons.
  destruct (in_rangesb a L), (zin_rangeb (bv_unsigned a) W), (in_rangesb a S); reflexivity.
Qed.

Lemma hiddenb_app_windows : forall S1 S a,
  hiddenb L (S1 ++ S) a = hiddenb L S a && negb (in_rangesb a S1).
Proof.
  intros S1 S a. unfold hiddenb. rewrite in_rangesb_app.
  destruct (in_rangesb a L), (in_rangesb a S1), (in_rangesb a S); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hiddenb_mono_cons : forall W S a,
  hiddenb L (W :: S) a = true -> hiddenb L S a = true.
Proof.
  intros W S a H. rewrite hiddenb_cons_window in H. apply andb_true_iff in H. tauto.
Qed.

Lemma hiddenb_mono_app : forall S1 S a,
  hiddenb L (S1 ++ S) a = true -> hiddenb L S a = true.
Proof.
  intros S1 S a H. rewrite hiddenb_app_windows in H. apply andb_true_iff in H. tauto.
Qed.

(* [comment removed for export] *)
Lemma hidden_inv_open_window : forall P W S msF,
  hidden_inv L S P msF -> hidden_inv L (W :: S) P msF.
Proof. intros P W S msF H a Ha. apply H. eapply hiddenb_mono_cons; exact Ha. Qed.

Lemma hidden_inv_open_windows_app : forall P S1 S msF,
  hidden_inv L S P msF -> hidden_inv L (S1 ++ S) P msF.
Proof. intros P S1 S msF H a Ha. apply H. eapply hiddenb_mono_app; exact Ha. Qed.

(* [comment removed for export] *)
Lemma restrict_mem_open_window : forall W S m a,
  restrict_mem L (W :: S) m a
  = if zin_rangeb (bv_unsigned a) W then m a else restrict_mem L S m a.
Proof.
  intros W S m a. unfold restrict_mem, restrict_mem_by. rewrite hiddenb_cons_window.
  destruct (zin_rangeb (bv_unsigned a) W), (hiddenb L S a); reflexivity.
Qed.

Lemma restrict_mem_open_windows_app : forall S1 S m a,
  restrict_mem L (S1 ++ S) m a
  = if in_rangesb a S1 then m a else restrict_mem L S m a.
Proof.
  intros S1 S m a. unfold restrict_mem, restrict_mem_by. rewrite hiddenb_app_windows.
  destruct (in_rangesb a S1), (hiddenb L S a); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma restrict_mem_open_window_inv : forall P W S msF a,
  hidden_inv L S P msF ->
  (zin_rangeb (bv_unsigned a) W = true /\ hiddenb L S a = true
     /\ P (ms_mem (restrict L (W :: S) msF) a))
  \/ ms_mem (restrict L (W :: S) msF) a = ms_mem (restrict L S msF) a.
Proof.
  intros P W S msF a HP. rewrite !ms_mem_restrict, restrict_mem_open_window.
  destruct (zin_rangeb (bv_unsigned a) W) eqn:EW; [|right; reflexivity].
  destruct (hiddenb L S a) eqn:Eh.
  - left. repeat split. exact (HP a Eh).
  - right. unfold restrict_mem, restrict_mem_by. rewrite Eh. reflexivity.
Qed.

Lemma restrict_open_window_zero : forall W S msF a,
  hidden_zero L S msF ->
  ms_mem (restrict L (W :: S) msF) a
  = if zin_rangeb (bv_unsigned a) W && hiddenb L S a
    then Some (Z_to_bv 8 0)
    else ms_mem (restrict L S msF) a.
Proof.
  intros W S msF a HZ. rewrite !ms_mem_restrict, restrict_mem_open_window.
  unfold restrict_mem, restrict_mem_by.
  destruct (zin_rangeb (bv_unsigned a) W) eqn:EW; cbn [andb]; [|reflexivity].
  destruct (hiddenb L S a) eqn:Eh; [exact (HZ a Eh) | reflexivity].
Qed.

Lemma restrict_open_windows_app_zero : forall S1 S msF a,
  hidden_zero L S msF ->
  ms_mem (restrict L (S1 ++ S) msF) a
  = if in_rangesb a S1 && hiddenb L S a
    then Some (Z_to_bv 8 0)
    else ms_mem (restrict L S msF) a.
Proof.
  intros S1 S msF a HZ. rewrite !ms_mem_restrict, restrict_mem_open_windows_app.
  unfold restrict_mem, restrict_mem_by.
  destruct (in_rangesb a S1) eqn:EW; cbn [andb]; [|reflexivity].
  destruct (hiddenb L S a) eqn:Eh; [exact (HZ a Eh) | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma restrict_open_window_eq : forall W S msF,
  restrict L (W :: S) msF
  = with_mem (restrict L S msF)
      (fun a => if zin_rangeb (bv_unsigned a) W then ms_mem msF a
                else ms_mem (restrict L S msF) a).
Proof.
  intros W S msF. unfold restrict, restrict_by, with_mem. cbn. f_equal.
  apply functional_extensionality. intros a. apply restrict_mem_open_window.
Qed.

(* [comment removed for export] *)

Lemma lazy_inv_vm_frame : forall S m m',
  m_vm m' = m_vm m -> lazy_inv L S m -> lazy_inv L S m'.
Proof.
  intros S [fd vm io fs proc lim tm] [fd' vm' io' fs' proc' lim' tm'] E H.
  cbn in E. subst vm'. destruct H as [Hl Hnd Hincl Hb]. split; assumption.
Qed.

Lemma lazy_inv_with_fds : forall S fds m, lazy_inv L S m -> lazy_inv L S (with_fds fds m).
Proof. intros S fds m. apply lazy_inv_vm_frame. reflexivity. Qed.
Lemma lazy_inv_with_pipes : forall S ps m, lazy_inv L S m -> lazy_inv L S (with_pipes ps m).
Proof. intros S ps m. apply lazy_inv_vm_frame. reflexivity. Qed.
Lemma lazy_inv_with_stdin : forall S x m, lazy_inv L S m -> lazy_inv L S (with_stdin x m).
Proof. intros S x m. apply lazy_inv_vm_frame. reflexivity. Qed.
Lemma lazy_inv_with_fs : forall S x m, lazy_inv L S m -> lazy_inv L S (with_fs x m).
Proof. intros S x m. apply lazy_inv_vm_frame. reflexivity. Qed.
Lemma lazy_inv_with_halted : forall S x m, lazy_inv L S m -> lazy_inv L S (with_halted x m).
Proof. intros S x m. apply lazy_inv_vm_frame. reflexivity. Qed.
Lemma lazy_inv_with_tid : forall S x m, lazy_inv L S m -> lazy_inv L S (with_tid x m).
Proof. intros S x m. apply lazy_inv_vm_frame. reflexivity. Qed.
Lemma lazy_inv_with_rlimit_core : forall S x m, lazy_inv L S m -> lazy_inv L S (with_rlimit_core x m).
Proof. intros S x m. apply lazy_inv_vm_frame. reflexivity. Qed.
Lemma lazy_inv_with_clock : forall S x m, lazy_inv L S m -> lazy_inv L S (with_clock x m).
Proof. intros S x m. apply lazy_inv_vm_frame. reflexivity. Qed.
Lemma lazy_inv_with_sigmask : forall S x m, lazy_inv L S m -> lazy_inv L S (with_sigmask x m).
Proof. intros S x m. apply lazy_inv_vm_frame. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lazy_inv_with_vmmaps : forall S h m,
  lazy_inv L S m ->
  (eager_used (with_vmmaps h m) + pages_total S * page_size <= vm_limit h)%Z ->
  lazy_inv L S (with_vmmaps h m).
Proof.
  intros S h [fd [maps lazy mat] io fs proc lim tm] [Hl Hnd Hincl Hb] Hb'.
  cbn in *. split; cbn; assumption.
Qed.

Lemma eager_used_with_vmmaps : forall h m,
  eager_used (with_vmmaps h m) = live_bytes (maps_subtract_all (vm_backed_maps h) (m_vm_lazy m)).
Proof. intros h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lazy_inv_fields_frame : forall S m m',
  m_vmmaps m' = m_vmmaps m ->
  m_vm_lazy m' = m_vm_lazy m ->
  m_vm_materialized m' = m_vm_materialized m ->
  lazy_inv L S m -> lazy_inv L S m'.
Proof.
  intros S m m' E1 E2 E3 [Hl Hnd Hincl Hb]. split.
  - rewrite E2. exact Hl.
  - rewrite E3. exact Hnd.
  - rewrite E3. exact Hincl.
  - unfold eager_used in *. rewrite E1, E2. exact Hb.
Qed.

End Windows.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section LazyLedger.

(* [comment removed for export] *)

Lemma hiddenb_cons_lazy : forall r L S a,
  hiddenb (r :: L) S a
  = (zin_rangeb (bv_unsigned a) r && negb (in_rangesb a S)) || hiddenb L S a.
Proof.
  intros r L S a. unfold hiddenb. rewrite in_rangesb_cons.
  destruct (zin_rangeb (bv_unsigned a) r), (in_rangesb a L), (in_rangesb a S); reflexivity.
Qed.

Lemma hiddenb_app_lazy : forall R L S a,
  hiddenb (R ++ L) S a
  = (in_rangesb a R && negb (in_rangesb a S)) || hiddenb L S a.
Proof.
  intros R L S a. unfold hiddenb. rewrite in_rangesb_app.
  destruct (in_rangesb a R), (in_rangesb a L), (in_rangesb a S); reflexivity.
Qed.

Lemma hiddenb_lazy_mono_app : forall R L S a,
  hiddenb L S a = true -> hiddenb (R ++ L) S a = true.
Proof. intros R L S a H. rewrite hiddenb_app_lazy, H. apply orb_true_r. Qed.

Lemma restrict_mem_app_lazy : forall R L S m a,
  restrict_mem (R ++ L) S m a
  = if in_rangesb a R && negb (in_rangesb a S) then None else restrict_mem L S m a.
Proof.
  intros R L S m a. unfold restrict_mem, restrict_mem_by. rewrite hiddenb_app_lazy.
  destruct (in_rangesb a R && negb (in_rangesb a S)); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma restrict_mem_app_lazy_fresh : forall R L S (m m' : word -> option byte),
  (forall a, in_rangesb a R = true -> in_rangesb a S = false) ->
  (forall a, in_rangesb a R = true -> m a = None) ->
  (forall a, in_rangesb a R = false -> m' a = m a) ->
  forall a, restrict_mem (R ++ L) S m' a = restrict_mem L S m a.
Proof.
  intros R L S m m' HRS Hfree Hframe a. rewrite restrict_mem_app_lazy.
  destruct (in_rangesb a R) eqn:ER.
  - rewrite (HRS a ER). cbn. unfold restrict_mem, restrict_mem_by.
    destruct (hiddenb L S a); [reflexivity|]. symmetry. exact (Hfree a ER).
  - cbn. unfold restrict_mem, restrict_mem_by. rewrite (Hframe a ER). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hidden_zero_app_lazy : forall R L S msF msF',
  hidden_zero L S msF ->
  (forall a, in_rangesb a R = true -> ms_mem msF' a = Some (Z_to_bv 8 0)) ->
  (forall a, in_rangesb a R = false -> ms_mem msF' a = ms_mem msF a) ->
  hidden_zero (R ++ L) S msF'.
Proof.
  intros R L S msF msF' HZ Hnew Hframe a Ha. rewrite hiddenb_app_lazy in Ha.
  destruct (in_rangesb a R) eqn:ER.
  - exact (Hnew a ER).
  - cbn in Ha. rewrite (Hframe a ER). exact (HZ a Ha).
Qed.

(* [comment removed for export] *)

Lemma m_vm_lazy_vm_add_lazy : forall a n m,
  m_vm_lazy (vm_add_lazy a n m) = lazy_interior a n ++ m_vm_lazy m.
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_materialized_vm_add_lazy : forall a n m,
  m_vm_materialized (vm_add_lazy a n m) = m_vm_materialized m.
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vmmaps_vm_add_lazy : forall a n m,
  m_vmmaps (vm_add_lazy a n m) = m_vmmaps m.
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_lazy_vm_forget_range : forall lo hi m,
  m_vm_lazy (vm_forget_range lo hi m) = maps_subtract (m_vm_lazy m) lo hi.
Proof. intros lo hi [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_materialized_vm_forget_range : forall lo hi m,
  m_vm_materialized (vm_forget_range lo hi m)
  = List.filter (page_outside_range lo hi) (m_vm_materialized m).
Proof. intros lo hi [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi m,
  m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. intros lo hi [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_lazy_with_vmmaps : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_materialized_with_vmmaps : forall h m,
  m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. intros h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vmmaps_with_vmmaps : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. intros h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lazy_interior_aligned : forall a n,
  (bv_unsigned a mod page_size = 0)%Z ->
  (bv_unsigned n mod page_size = 0)%Z ->
  (0 < bv_unsigned n)%Z ->
  lazy_interior a n = [(a, n)].
Proof.
  intros a n Ha Hn Hpos. unfold lazy_interior.
  pose proof (bv_unsigned_in_range 64 a) as Har. pose proof (bv_unsigned_in_range 64 n) as Hnr.
  set (lo := bv_unsigned a) in *. set (sz := bv_unsigned n) in *.
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  pose proof (Z.div_mod lo page_size ltac:(lia)) as Hlo.
  pose proof (Z.div_mod (lo + sz) page_size ltac:(lia)) as Hhi.
  pose proof (Z.div_mod (lo + page_size - 1) page_size ltac:(lia)) as Hlo'.
  pose proof (Z.mod_pos_bound (lo + page_size - 1) page_size ltac:(lia)) as Hm'.
  assert (Hsum : ((lo + sz) mod page_size = 0)%Z).
  { rewrite Z.add_mod, Ha, Hn by lia. reflexivity. }
  assert (E1 : ((lo + page_size - 1) / page_size * page_size = lo)%Z).
  { replace (lo + page_size - 1)%Z with (lo / page_size * page_size + (page_size - 1))%Z in * by lia.
    rewrite Z.div_add_l in * by lia.
    rewrite (Z.div_small (page_size - 1) page_size) by lia. lia. }
  assert (E2 : ((lo + sz) / page_size * page_size = lo + sz)%Z) by lia.
  rewrite E1, E2.
  destruct (lo <? lo + sz)%Z eqn:E; [|apply Z.ltb_ge in E; lia].
  f_equal. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Har.
  - apply bv_eq. rewrite Z_to_bv_unsigned. replace (lo + sz - lo)%Z with sz by lia.
    apply bv_wrap_small. exact Hnr.
Qed.

Lemma lazy_inv_vm_add_lazy : forall L S a n m,
  lazy_inv L S m ->
  (eager_used (vm_add_lazy a n m) + pages_total S * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv (lazy_interior a n ++ L) S (vm_add_lazy a n m).
Proof.
  intros L S a n m [Hl Hnd Hincl Hb] Hb'. split.
  - rewrite m_vm_lazy_vm_add_lazy, Hl. reflexivity.
  - rewrite m_vm_materialized_vm_add_lazy. exact Hnd.
  - rewrite m_vm_materialized_vm_add_lazy. exact Hincl.
  - rewrite m_vmmaps_vm_add_lazy. exact Hb'.
Qed.

Lemma lazy_inv_vm_forget_range : forall L S lo hi m,
  lazy_inv L S m ->
  (eager_used (vm_forget_range lo hi m) + pages_total S * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv (maps_subtract L lo hi) S (vm_forget_range lo hi m).
Proof.
  intros L S lo hi m [Hl Hnd Hincl Hb] Hb'. split.
  - rewrite m_vm_lazy_vm_forget_range, Hl. reflexivity.
  - rewrite m_vm_materialized_vm_forget_range. apply NoDup_filter. exact Hnd.
  - rewrite m_vm_materialized_vm_forget_range. intros p Hp. apply filter_In in Hp.
    apply Hincl. tauto.
  - rewrite m_vmmaps_vm_forget_range. exact Hb'.
Qed.

(* [comment removed for export] *)

Lemma iv_subtract_within : forall a sz lo hi b m,
  (bv_unsigned a + bv_unsigned sz <= 2 ^ 64)%Z ->
  (hi <= 2 ^ 64)%Z ->
  In (b, m) (iv_subtract a sz lo hi) ->
  (bv_unsigned a <= bv_unsigned b)%Z
  /\ (bv_unsigned b + bv_unsigned m <= bv_unsigned a + bv_unsigned sz)%Z.
Proof.
  intros a sz lo hi b m Hnw Hhi Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a) as Har. pose proof (bv_unsigned_in_range 64 sz) as Hszr.
  change (bv_modulus 64) with (2^64)%Z in Har, Hszr.
  apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo)%Z eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [Hin|[]]. inversion Hin; subst.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2^64)%Z; lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz)%Z eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [Hin|[]]. inversion Hin; subst.
    pose proof (Z.le_max_l (bv_unsigned a) hi). pose proof (Z.le_max_r (bv_unsigned a) hi).
    assert (Z.max (bv_unsigned a) hi < 2 ^ 64)%Z by lia.
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2^64)%Z; lia). lia.
Qed.

Lemma lazy_range_okb_within : forall segs a sz b m,
  lazy_range_okb segs (a, sz) = true ->
  (bv_unsigned a <= bv_unsigned b)%Z ->
  (bv_unsigned b + bv_unsigned m <= bv_unsigned a + bv_unsigned sz)%Z ->
  lazy_range_okb segs (b, m) = true.
Proof.
  intros segs a sz b m H Hlo Hhi. unfold lazy_range_okb, range_nowrapb in *. cbn [fst snd] in *.
  apply andb_true_iff in H. destruct H as [Hnw Hd]. apply Z.leb_le in Hnw.
  apply andb_true_iff. split; [apply Z.leb_le; lia|].
  rewrite forallb_forall in Hd |- *. intros seg Hin. specialize (Hd seg Hin).
  unfold seg_disjoint_rangeb in *. cbn [fst snd] in *.
  rewrite orb_true_iff in Hd |- *. rewrite !Z.leb_le in Hd |- *. lia.
Qed.

Lemma lazy_ranges_okb_maps_subtract : forall segs L lo hi,
  (hi <= 2 ^ 64)%Z ->
  lazy_ranges_okb segs L = true ->
  lazy_ranges_okb segs (maps_subtract L lo hi) = true.
Proof.
  intros segs L lo hi Hhi H. induction L as [|[a sz] L IH].
  - cbn [maps_subtract]. rewrite lazy_ranges_okb_nil.
    unfold lazy_ranges_okb in H. apply andb_true_iff in H. tauto.
  - apply lazy_ranges_okb_cons in H. destruct H as [Hr HL].
    cbn [maps_subtract]. apply lazy_ranges_okb_app. split; [|exact (IH HL)].
    unfold lazy_ranges_okb. apply andb_true_iff. split.
    + unfold lazy_ranges_okb in HL. apply andb_true_iff in HL. tauto.
    + apply forallb_forall. intros [b m] Hin.
      assert (Hnw : (bv_unsigned a + bv_unsigned sz <= 2 ^ 64)%Z).
      { unfold lazy_range_okb, range_nowrapb in Hr. cbn [fst snd] in Hr.
        apply andb_true_iff in Hr. destruct Hr as [Hr _]. apply Z.leb_le in Hr. exact Hr. }
      destruct (iv_subtract_within a sz lo hi b m Hnw Hhi Hin) as [H1 H2].
      exact (lazy_range_okb_within segs a sz b m Hr H1 H2).
Qed.

Lemma lazy_ranges_okb_vm_add : forall segs L a n,
  lazy_ranges_okb segs L = true ->
  lazy_range_okb segs (a, n) = true ->
  lazy_ranges_okb segs (lazy_interior a n ++ L) = true.
Proof.
  intros segs L a n HL Hr. apply lazy_ranges_okb_app. split; [|exact HL].
  unfold lazy_ranges_okb. apply andb_true_iff. split.
  { unfold lazy_ranges_okb in HL. apply andb_true_iff in HL. tauto. }
  apply forallb_forall. intros [b m] Hin.
  unfold lazy_interior in Hin.
  pose proof (bv_unsigned_in_range 64 a) as Har. pose proof (bv_unsigned_in_range 64 n) as Hnr.
  change (bv_modulus 64) with (2^64)%Z in Har, Hnr.
  assert (Hnw : (bv_unsigned a + bv_unsigned n <= 2 ^ 64)%Z).
  { unfold lazy_range_okb, range_nowrapb in Hr. cbn [fst snd] in Hr.
    apply andb_true_iff in Hr. destruct Hr as [Hr' _]. apply Z.leb_le in Hr'. exact Hr'. }
  set (lo := bv_unsigned a) in *. set (sz := bv_unsigned n) in *.
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  pose proof (Z.div_mod (lo + page_size - 1) page_size ltac:(lia)) as Hlo'.
  pose proof (Z.mod_pos_bound (lo + page_size - 1) page_size ltac:(lia)) as Hm'.
  pose proof (Z.div_mod (lo + sz) page_size ltac:(lia)) as Hhi'.
  pose proof (Z.mod_pos_bound (lo + sz) page_size ltac:(lia)) as Hm''.
  set (lo' := ((lo + page_size - 1) / page_size * page_size)%Z) in *.
  set (hi' := ((lo + sz) / page_size * page_size)%Z) in *.
  destruct (lo' <? hi')%Z eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
  destruct Hin as [Hin|[]]. inversion Hin; subst.
  apply (lazy_range_okb_within segs a n); [exact Hr| |];
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2^64)%Z; lia); lia.
Qed.

End LazyLedger.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Clients.
Variables L S : list (word * word).

(* [comment removed for export] *)
Lemma restrict_open_window_state : forall W msF1 ms1,
  hidden_zero L S msF1 ->
  restrict L S msF1 = ms1 ->
  restrict L (W :: S) msF1
  = with_mem ms1 (fun a => if zin_rangeb (bv_unsigned a) W && hiddenb L S a
                          then Some (Z_to_bv 8 0) else ms_mem ms1 a).
Proof.
  intros W msF1 ms1 HZ <-. rewrite (restrict_open_window_eq L W S msF1). f_equal.
  apply functional_extensionality. intros a.
  destruct (zin_rangeb (bv_unsigned a) W); cbn [andb]; [|reflexivity].
  destruct (hiddenb L S a) eqn:Eh; [exact (HZ a Eh)|].
  rewrite ms_mem_restrict. unfold restrict_mem, restrict_mem_by. rewrite Eh. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma restrict_open_hidden_window_state : forall W msF1 ms1,
  hidden_zero L S msF1 ->
  restrict L S msF1 = ms1 ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> hiddenb L S a = true) ->
  restrict L (W :: S) msF1
  = with_mem ms1 (fun a => if zin_rangeb (bv_unsigned a) W
                          then Some (Z_to_bv 8 0) else ms_mem ms1 a).
Proof.
  intros W msF1 ms1 HZ Hr HW. rewrite (restrict_open_window_state W msF1 ms1 HZ Hr). f_equal.
  apply functional_extensionality. intros a.
  destruct (zin_rangeb (bv_unsigned a) W) eqn:E; [|reflexivity].
  rewrite (HW a E). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma window_hidden_intro : forall (wlo wsz : word),
  (exists lo sz, In (lo, sz) L /\ bv_unsigned lo <= bv_unsigned wlo
                 /\ bv_unsigned wlo + bv_unsigned wsz <= bv_unsigned lo + bv_unsigned sz)%Z ->
  (forall lo sz, In (lo, sz) S ->
     (bv_unsigned lo + bv_unsigned sz <= bv_unsigned wlo
      \/ bv_unsigned wlo + bv_unsigned wsz <= bv_unsigned lo)%Z) ->
  forall a, zin_rangeb (bv_unsigned a) (wlo, wsz) = true -> hiddenb L S a = true.
Proof.
  intros wlo wsz (lo & sz & HinL & Hlo & Hhi) HS a Ha.
  unfold zin_rangeb in Ha. cbn [fst snd] in Ha. apply andb_true_iff in Ha.
  destruct Ha as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  apply hiddenb_true_iff. split.
  - apply in_rangesb_true. exists lo, sz. split; [exact HinL | lia].
  - apply in_rangesb_false. intros lo' sz' Hin' Hr. destruct (HS lo' sz' Hin'); lia.
Qed.

(* [comment removed for export] *)
Lemma ms_read_byte_unrestrict_visible : forall msF ms1 a,
  hiddenb L S a = false ->
  ms_read_byte (unrestrict_to L S msF ms1) a = ms_read_byte ms1 a.
Proof.
  intros msF ms1 a Ha. unfold ms_read_byte, unrestrict_to.
  rewrite (unrestrict_by_visible (hiddenb L S) msF ms1 a Ha). reflexivity.
Qed.

Lemma ms_read_bytes_aux_unrestrict_visible : forall n msF ms1 a,
  range_visible (hiddenb L S) a n ->
  ms_read_bytes_aux (unrestrict_to L S msF ms1) a n = ms_read_bytes_aux ms1 a n.
Proof.
  induction n as [|n IH]; intros msF ms1 a Hvis; [reflexivity|].
  cbn [ms_read_bytes_aux]. apply range_visible_S in Hvis. destruct Hvis as [Ha Hvis].
  rewrite (ms_read_byte_unrestrict_visible msF ms1 a Ha), (IH msF ms1 (a + 1) Hvis). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wview_unrestrict_visible : forall segs msF ms1 a,
  hiddenb L S a = false ->
  wview segs (ms_mem (unrestrict_to L S msF ms1)) a = wview segs (ms_mem ms1) a.
Proof.
  intros segs msF ms1 a Ha. unfold wview, unrestrict_to.
  rewrite (unrestrict_by_visible (hiddenb L S) msF ms1 a Ha). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma range_visible_outside_lazy : forall (a : word) (n : nat),
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall lo sz, In (lo, sz) L ->
     (bv_unsigned lo + bv_unsigned sz <= bv_unsigned a
      \/ bv_unsigned a + Z.of_nat n <= bv_unsigned lo)%Z) ->
  range_visible (hiddenb L S) a n.
Proof.
  intros a n Hnw HL i Hi. apply hiddenb_outside_L. apply in_rangesb_false.
  intros lo sz Hin Hr. rewrite bv_unsigned_add_small in Hr by lia.
  destruct (HL lo sz Hin); lia.
Qed.

(* [comment removed for export] *)
Lemma range_visible_in_window : forall (a : word) (n : nat) wlo wsz,
  In (wlo, wsz) S ->
  (bv_unsigned wlo <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned wlo + bv_unsigned wsz)%Z ->
  (bv_unsigned wlo + bv_unsigned wsz <= 2 ^ 64)%Z ->
  range_visible (hiddenb L S) a n.
Proof.
  intros a n wlo wsz Hin Hlo Hhi Hnw i Hi. apply hiddenb_visible_S. apply in_rangesb_true.
  exists wlo, wsz. split; [exact Hin|]. rewrite bv_unsigned_add_small by lia. lia.
Qed.

End Clients.
