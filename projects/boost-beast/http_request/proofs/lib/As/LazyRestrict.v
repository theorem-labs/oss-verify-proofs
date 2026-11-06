(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

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
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma cl_bounds : forall r,
  (0 <= cl_lo r <= bv_unsigned (fst r))%Z
  /\ (bv_unsigned (fst r) + bv_unsigned (snd r) <= cl_hi r < bv_unsigned (fst r) + bv_unsigned (snd r) + page_size)%Z
  /\ (cl_lo r mod page_size = 0)%Z /\ (cl_hi r mod page_size = 0)%Z
  /\ (0 <= win_npagesZ r <= bv_unsigned (snd r) / page_size + 2)%Z
  /\ (win_npagesZ r * page_size = cl_hi r - cl_lo r)%Z.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@kc__1); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_lo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_hi); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_npagesZ); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__2); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.ZArith.Zdiv.Z_mod_mult); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.ZArith.BinInt.Z.div_mul); constr:(@Corelib.Init.Datatypes.pair); constr:(@kc__1 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))))|] [|@p; @__ff; @__varmap; @__wit; @__arith; @H2; @H1; @H0; @H; @heq_lo; @heq_sz; @__sat3; @__sat2; @H7; @H6; @H5; @H4; @r; @q; @H3; @H9; @H8; @__sat4; @H14; @H13; @H12; @H11; @H10; @r0; @q0; @__sat5; @__sat6; @H16; @H15; @__sat8; @H21; @H20; @H19; @H18; @H17; @r1; @q1; @__sat7; @__sat9; @__x1; @__x2; @__x3; @H23; @H22; @q4; @heq_q1; @heq_q2; @heq_q3; @z; @__x4; @__p1; @__x5; @__x6; @__p2; @__x7; @__x8; @__p3; @q3; @q2; @M3; @D3; @M2; @D2; @M1; @D1; @sz; @lo; @Hn; @Hb; @n; @b|] "#@##h$f#}#{#s$6#$##$7$5#%$<#'#-#)#(#&#*#+#.#,#h#:#<$`#/#2#6#9#A#J#M#8#@#C#S#G$;#4#7#?#O#[#0#1#5#;#>#E#3#D#R#_#`#F#=#B#N#^$/#I#K#f#g#o#H#Q#V$^$J#U#L#Z#]#W#c#Y#e#t#v#x#y$#$-$?$@#P#T#X#a$W$[$e$*$D#m#l#k$($)$.$0$1$2$4$3$=$A$B$>$C#\$]$\$U$a$g$f$h$R$Q$i#p#r#w#z#q#|#~$'$&$$$,$_$9$8$+#u$G$H$I$E$F$Y$K$d#n$O$M$V$Z$b$S$L$N$c$X$T$:$P$%N$@%$A%$B%$C%$D&$E%$F%$G%$H%$I($J+$K'$L*$M%$N%#~%$#%$O%$P%$Q%$R%$S%$T&$U'$V&$W$$X%$Y&$Z%$[$$\*$]'$^%$_&$`)$a%$b&$c%$d$$e$#~&$#&#(,<SQ<#<#<#<#<#USp#USq#VSr##US_H#E#WS`&&H1(##&#&&#WSa**H1,#$'#USbH#$#$%D%%#&%#(0D'C#E()D'C#EUScH#E#+/DJ@$$##'#&'#*)D)3<'C$#&&#&.#&1#&4#&=#j#$s#$#VSss#'G1s#(G#E#USts#*%%#&%#1s#-Q1s#.M0C#'CH$m#$#1s#2O0C#'CK$m#$##EK%K/&$#<s#:<#<#<#<#<#J#'C#EUSd#j##,#%Q;#EM%P=#ER%R?&$#j###*%S#B#ES%%Ns#$USuSLUSvSLUSwCUSxCUSyCHC5HCE.C$S6#/&JFFI#LZSz'JFFI#VS{(I0SeSfVS|HK'Se#Sfm$%#WS}CEGXS~HK$#l#%*)#l#&21#l#'54#k##s##T#l#($#Hj#)9#j#*;#V#GHj##>#j##s###,s#$s##A#S%j#+s#&#j#,s#(#V#GHj##s#+#j##s#9#,s#:s#9s#.#Ml#-s#<s#=#l#.s#As#B#'CDEUSd#m#%#KGD#+GD*D#(GD$$#'CG#1s#zP0C#'CG$m#$#1s#~R0C#'CQ$m#$#7MD#ED(OD#E#k##%#k##s#E#8PD#EP+RD#E#k##+#k##&#2OD*D'(RD$$#'CR#k##s###3RD%ED(S#D#E#%$D&$#k##'#4S#D%DE(S%D%D##$E&$#k##'#5S%D+ND'C#Ek##s#6#6ND(S$D'C#S$k##s#:#+S$D(S*D#ES*%S*s$)&$#%Es#rj##$#%S<s$-#ES=%S+s$/#ES7%S7s$1&$#j###*%S>s$4#ES,%S8s$6US+G#ENk##s#<#US7K.Cs#nSVs#o/s#qJFFI#Ll#%#s#ls#fl#&s#us#t#l#'s#xs#w#l#(#7Hl#/)*#l#0-+#j#1/#j#21#V#GHj##4#j##9#,:97#S,j#3<#j#4>#V#GHj##A#j##s#'#,s#(s#'s#$#S=l#5s#*C#l#6s#,C#l#7s#1s#.#l#)s#6s#3#l#*s#>s#8#l#+s#Fs#@#l#,s#Ms#H#l#0s#Ts#O#l#/s#[s#V#l#-s#]s#^#l#.s#bs#c#m##s#KLKD#(KD#E#%$D&$#$QK$#DJSQ)$#1s%0S#0C#'CM$m#$#7PD#Es#_k##s#m#k##s#h#8OD#EO+S#D#E#k##s#s#k##&#2RD*D'$#s#d'CS##k##s$.#3S#D#Es#a%s#bD&$#k##s#l#4S%D(ND%D##$E&$#k##s#k#5ND'Cs#_Ek##s$=#6S$D'Cs#aS*k##s$@#+S*D(S<D#EH%HD&$#j###s$v%GD%QDj##s#`s$y#ES-%S-s%6&$#j###s$}%S's%9#ES?%S(s%;US,Gk##s$@s#mUS1Kl#/#$s$cl#0&%#j#8(#j#9*#V#GHj##-#j##2#,320#S?j#1s#o#j#2s#q#V#GHj##s#t#j##s#y#,s#zs#y:#S,j#3<#j#4s%B#V#GHj##@#j##s#%#,s#&s#%s###S$l#5s#(C#l#6s#*C#l#7s#.s#,#l#)s#2s#0#l#*s#9s#4#l#+s#?s#;#l#,s#Es#A#l#0s#Ls#G#l#/s#Qs#N#l#-s#Ss#T#l#.s%Rs%S#m##s$rKs#ZD#+s#[D*D#(s#]D$$#'Cs#_#$MQ$#D)#s#c1s&4S%0C#'CP$m#$#$OP$#D)#s#j7#D#E$$S#R$#D)#s#o(#D#E#k##s$y#k##)#$RO$#D)#s#v8#D#E$$S%S#$#D)#s#{+#D#E#k##s%)#k##)#7S#D#ES##Es#gk##s%.#k##%#8S%D#Es$fk##s%2#k##s%k#2ND*Ds$j$#s$n'CS$#k##s%I#3S$D#Es$n%s$oD&$#k##s%+#4S*D%Ds#m#s#nE&$#k##s%)#5S<D+S=D'C#Ek##s%X#6S=D(S+D'C#S+k##s%\#+S+D(SBD$S7SB$#D)#s$H2#D$S>S7$#D)#s$L+#D*D#(%D$$#'C'#k##s%j#3)D$S,S>$#D)#s$V(#D#E#%$D&$#k##s%P#4(D$S8S,$#D)#s$_(#D%D##$E&$#k##s%R#5(D$S1S8$#D)#s$h+#D'C#Ek##s&(#6&D$S-S1$#D)#s$o(#D'C#$k##s&/#+&D$S'S-$#D)#s$v(#D%RD&s&a#j###s%U%S#D%ND#ES@%S@s'&&$#j###s%[%S9s')#ES2%S.s'+#ES3%S3s'-&$#j###s%b%SCs'0#ESA%SGs'2USHG#ES1k##s&8#US9Kl#:#$s%Ul#/'%#j#;)#j#<+#V#GHj##.#j##3#,431#SAj#=6#j#>8#V#GHj##;#j##@#,A@>#S2j#?s###j#8s'%#V#GHj##s#'#j##s'-#,s'.s#,s#*#S1l#@s#.C#l#As#3C#l#9s#;s#5#l#1s#Cs#=#l#2s#Ms#E#l#3s#Ws#O#l#4s#bs#Y#l#5s#gC#l#6s#iC#l#7s#ns#k#l#)s#ss#p#l#*s#ys#u#l#+s$#s#{#l#,s$)s$%#l#/s$.s$+#l#:s$4s$0#l#Bs$>s$6#l#Cs$Ks$C#l#-s$Ps$Q#l#.s&cs&d#m##s&PLs$WD#(s$XD#E#%$D&$#1s(1N0C#'CO$m#$#7s$MD(s$ID#E#k##s&o#k##s$O#8s$YD#Es$Z$NS%$#D)#s%n+#D#E#k##s&x#k##)#7S%D#Es&Wk##s&|#k##s'Y#8ND#Es%Rk##s'$#k##s&H#2S$D*Ds%V$#s&\'CS*#k##s';#3S*D#Es%Z%s%[D&$#k##s&y#4S<D(S=D%D##$E&$#k##s&x#5S=D'Cs$JEk##s'J#6S+D'Cs$LSBk##s'M#+SBD(S7D2s$ID+s$@D*D#$#s$A'Cs$C#k##s'T#3s$ED#Es$<%s$=D&$#k##s'6#4s$AD(s$9D%D##$E&$#k##s'5#5s$>D'Cs$4Ek##s'c#6s$:D'Cs$3s$4k##s'f#+s$6D$S?S'$#D)#s&Q(#D#ES$%S$D&$#j###s(C%S*D#ES<%S=Dj##s$2s(G#ESR%SRs(`&$#j###s(K%SMs(c#ES/%SNs(eUS.G#ES(k##s'k#US3Kl#:#$s(2l#/'%#j#D)#j#E+#V#GHj##.#j##3#,431#S/j#;s$B#j#<s$D#V#GHj##s$G#j##s$L#,s$Ms$L;#SAj#==#j#>?#V#GHj##B#j##s#'#,s#(s#'s#%#SHj#?s&M#j#8s(s#V#GHj##s&Q#j##s&V#,s&Ws&Vs&T#S8l#@s#0C#l#As#5C#l#9s#9s#7#l#1s#=s#;#l#2s#Ds#?#l#3s#Js#F#l#4s#Qs#L#l#5s#SC#l#6s#UC#l#7s#Ys#W#l#)s#]s#[#l#*s#ds#_#l#+s#js#f#l#,s#ps#l#l#/s#us#r#l#:s#zs#w#l#Bs$(s#|#l#Cs$.s$*#l#-s$0s$1#l#.s'2s'3#m##s(PKMD#+MD*D#(MD$$#'CM#1s)kS$0C#'CR$m#$#7s&2D(s$4D#E#k##s(M#k##s$:#8s$8D#Es$9$S*S$$#D)#s'L+#D#E#k##s(V#k##)#7S*D#Es$*k##s(Z#k##s(2#8S<D#Es%pk##s(^#k##s#^#2S=D*Ds%t$#s%x'CS+#k##s(u#3S+D#Es%x%s%yD&$#k##s(W#4SBD%Ds$0#s$1E&$#k##s(U#5S7D+S>D'C#Ek##s)(#6S>D(S,D'C#S,k##s),#+S,D(S8D2S8D+S1D*D#(S1D$$#'CS1#k##s)4#3S1D(S-D#E#%$D&$#k##s(s#4S-D(S'D%D##$E&$#k##s(r#5S'D+S?D'C#Ek##s)E#6S?D(S(D'C#S(k##s)I#+S(D(SHD$S9S@$#D)#s(52#D$S2S9$#D)#s(9+#D*D#(%D$$#'C'#k##s)W#3)D$S.S2$#D)#s(C(#D#E#%$D&$#k##s)=#4(D$SIS.$#D)#s(L(#D%D##$E&$#k##s)?#5(D$S3SI$#D)#s(U+#D'C#Ek##s)q#6&D$SCS3$#D)#s(\(#D'C#$k##s)x#+&D$SASC$#D)#s(c(#Dj##s(;s)@#ES>%S>D&$#j###s)D%S,D#ES8%S1D#ES0%S0s*r&$#j###s)K%SJs*u#ES:%Sgs*w#ESD%SDs*y&$#j###s)R%S4s*|#ESh%SWs*~US/PUS0OUS/Qk##s*)s&SUSXMl#B#$s)Fl#:&%#l#F(s$|#l#C*s$}#j#G,#j#H.#V#GHj##1#j##6#,764#Shj#I9#j#J;#V#GHj##>#j##s###,s#$s##A#S:j#Ks#&#j#Ds#(#V#GHj##s#+#j##s#0#,s#1s#0s#.#S5j#Es(i#j#;s+3#V#GHj##s(m#j##s(r#,s(ss(rs#8#S.l#Ls#:C#l#Ms#?C#l#<s#Gs#A#l#=s#Os#I#l#>s#Ys#Q#l#?s#cs#[#l#8s#ns#e#l#@s#sC#l#As#uC#l#9s#zs#w#l#1s$#s#|#l#2s$*s$%#l#3s$1s$,#l#4s$9s$3#l#5s$;C#l#6s$=C#l#7s$Bs$?#l#)s$Gs$D#l#*s$Ms$I#l#+s$Ss$O#l#,s$Ys$U#l#:s$^s$[#l#Bs$cs$`#l#Cs&>s&;#l#Ns$ns$f#l#Fs(7s(3#l#Os$us$q#l#-s$ws$x#l#.s(Ss(T#m##s*RLPD#(PD#E#%$D&$#+s(RD+S%D0C#'CH$m#$#$S$N$#D)#s)j+#D0C#'CK$m#$#0Cs)I'CMs)Jm#$#1s,BSB0C#'CS*$m#$#1s,FS>0C#'CS=$m#$#$S+S=$#D)#s)|7#D#E$(s(9D#E#k##s+,#k##&#7S+D#ES+#Es&Qk##s+1#k##%#8s(BD#Es(C#Es&Tk##s+6#k##%#8S7D#Es$|k##s+:#k##s*f#7S,D#Es${k##s+>#k##s*e#8S8D+S-D#E#k##s+C#k##s$0#2S1D*D'$#s%$'CS-#k##s+Z#3S-D#Es$~%s%#D&$#k##s+<#4S'D(S?D%D##$E&$#k##s+;#5S?D'Cs$|Ek##s+i#6S(D'Cs$~SHk##s+l#+SHD(S@D2S@D+S9D*D#(S9D$$#'CS9#k##s+t#3S9D(S2D#E#%$D&$#k##s+W#4S2D(S.D%D##$E&$#k##s+V#5S.D+SID'C#Ek##s,)#6SID(S3D'C#S3k##s,-#+S3D(SCD$SGSA$#D)#s*u2#D$S5SG$#D)#s*y+#D*D#(%D$$#'C'#k##s,;#3)D$SRS5$#D)#s+'(#D#E#%$D&$#k##s+}#4(D$SMSR$#D)#s+0(#D%D##$E&$#k##s,##5(D$S/SM$#D)#s+9+#D'C#Ek##s,U#6&D$SNS/$#D)#s+@(#D'C#$k##s,\#+&D$SXSN$#D)#s+G(#D)SASG*#D*SAD*SGD)$#'C&#j##s)4#%MD&s-;#)SMS/*#D*SMD*S/D)$#'C&#j##)#%PD%S-D&s+,#)S0SJ*#D*S0D*SJD)$#'C&#j##)#%S'D%S(D#ESi%Sis-j&$#)SSSD*#D*SSD*SDD)$#'C&#j##)#%S]s-s#ESY%S;s-u#ESZ%SZs-w&$#)SWST*#D*SWD*STD)$#'C&#j##)#%SKs.$#ESE%SFs.&USJPk##s-+s)\USSOUSJQ#ESMk##s-/#USgMCCKCCQ:C$G#=CSQ=Cs.`DC$#ISQ=C#>C%#>C($>C(%DC$#.C&S6#/s-pJFFI#Ll#%#s-ks-el#&/s-s#l#'s-ws-v#j#PC#j#QC#j#RC#)HG*#K*HK*GK)$#'C&#k#PC#k#QC#k#RC#WHDSKSZl#(-$#l#BBs###l#:s#&s#$#l#Fs#(s#)#l#Cs#+s#*#j#Ss#-#j#Ts#/#V#GHj##s#2#j##s#=#,s#>s#=s#5#SEj#Gs#@#j#Hs#B#V#GHj##s#E#j##s#P#,s#Qs#Ps#H#SYj#Is#S#j#Js,&#V#GHj##s#W#j##s,.#,s,/s#bs#Z#SDj#Ks*E#j#Ds,U#V#GHj##s#g#j##s.M#,s.Ns#rs#j#SXj#Es*G#j#;s.I#V#GHj##s*K#j##s.Q#,s.Rs*Ps#y#SGl#Ls$%C#l#Us$*C#l#<s$2s$,#l#=s$:s$4#l#>s$Ds$<#l#?s$Ns$F#l#8s$Ys$P#l#@s$^C#l#As$`C#l#9s$es$b#l#1s$js$g#l#2s$qs$l#l#3s$xs$s#l#4s%$s$z#l#5s%&C#l#6s%(C#l#7s%,s%*#l#)s%0s%.#l#*s%7s%2#l#+s%=s%9#l#,s%Cs%?#l#:s%Is%E#l#Bs%Ns%K#l#Cs%Ss%P#l#Ns%Ys%U#l#Fs%_s%[#l#Os%fs%a#l#-s%ks%l#l#.s%ps%q#l#Vs%us%v#l#Ws%ys%z#l#Xs&%s&&#)GK*#D*GD*KD)$#'C&#)KQ*#D*MD#E##$S*&$#*QD#s(P#%$s(P&$#(*D'C#E((D'C#E+HD#E#$Ks/Y#%#&%#*'D'C#H&%#&+#&.#&1#&6#j#YC##H-&s-)#*HD)QM*#D'C%#&'#&7#&:#&=#&B#j#YC#*Qs/K#E##$S$&$#*Ks/O#s&W#$s&Xs/Q%%#&%#(+s/T'C#E()s/V'C#E#Es#6$Gs/~#s#8#&%#*s#:s/\'C##&%#&*#&-#&0#+Ns/b0C#'CG$m#$#$s)/s/f)#s-x+#s/h0C#'CQ$m#$#+S<s/l0C#'CP$m#$#1s0QS70C#'CS<$m#$#1s0US,0C#'CS+$m#$#7S+s/x#Es/y(S7s/z#E#k##%#k##s&h#$s,Ks/~)#s.48#s0$#E$$s,As0&)#s.8+#s0(#E#k##/#k##(#8S7s0,+S,s0-#E#k##4#k##s.s#7S,s01(S1s02#E#k##9#k##s.s#8S8s06+S-s07#E#k##>#k##s(>#$s,Ds0;)#s.M7#s0=#E$$s,:s0?)#s.Q(#s0A#E#k##s#(#k##(#2S-s0E+S's0F*s0G#(S's0H$$#'CS'#k##s0I#3S's0L(S?s0M#E#%$s0O&$#k##s/=#4S?s0R%s0SE(S(s0T%s0U##$E&$#k##'#5S(s0Y+SHs0Z'C#Ek##s0[#6SHs0](S@s0^'C#S@k##s0_#+S@s0a(S9s0b2S9s0c+S2s0d*s0e#(S2s0f$$#'CS2#k##s0g#3S2s0j(S.s0k#E#%$s0m&$#k##s/[#4S.s0p(SIs0q%s0r##$E&$#k##s#$#5SIs0v+S3s0w'C#Ek##s0x#6S3s0z(SCs0{'C#SCk##s0|#+SCs0~(SAs1#$s&xs1$)#s/62#s1&$s&qs1')#s/9+#s1)*s1*#(%s1+$$#'C'#k##s1,#3)s1/$s&qs10)#s/B(#s12#E#%$s14&$#k##s/~#4(s17$s&ps18)#s/J(#s1:%s1;##$E&$#k##s#I#5(s1?$s&qs1@)#s/R+#s1B'C#Ek##s1C#6&s1E$s&ps1F)#s/X(#s1H'C#$k##s1I#+&s1K$S0SX$#s1M)#s/_(#s1O%Rs1P&s1J#*S5s1R#E#j##%#%S#s1U%Ns1V%Ms1W&s1S#*SNs1Y#E#j##%#%Ps1\%S-s1]&s/@#*S:s1_#E#j##%#%S's1b%S(s1c#ES]&#s&e*S4s1f#E#j##%#%SYs1~#ES;%T$s2$#ESK&#s&`*S[s1n#E#j##%#%SEs2*#ESF%Sjs2,US:Pk##s$Zs-bUSDOUS:Qk##s$]s&dUSSM?CSk@Sk@#@#@#@#?C#UT%SQVT&C#?C'WSlC$#9C'#9C.#F#SUVT'0#GSL#s1{CCM:Cs1{Q#:C#Ks1|:C#Gs1}.Cs1zS)s1{/s1}JFFI#LUT(F<s&t<#=C#.Cs2$S)#/s2'JFFI#L-s2(JFFI)(#.Cs&}S6&/s2*JFFI#L=Cs3#.Cs2*S)#/s2-JFFI#L.Cs2,S)s'%/s2/JFFI#L>Cs'(s2/.Cs2/S)#/s22JFFI#L-s23JFFI&3#-s24JFFI)4#-s25JFFI-5#-s26JFFI06#l#%#s21s2+l#&;s29#l#'@s2<#j#PC#j#QC#j#RC#j#ZC#k##s%5s2K'CGM*Ms2R#E#k##s2O#k##s2P#k##'#k##)#k#PC#k#QC#k#RC#k#ZC#\HSNSOSPSEKS]NOl#(0$#l#Cs#Cs#D#l#Bs#Fs#E#l#Os#Hs#I#l#Ns#Ks#J#j#Ss#M#j#Ts#O#V#GHj##s#R#j##s#X#,s#Ys'Zs#U#SFj#Gs#[#j#Hs#]#V#GHj##s#`#j##s#f#,s#gs'ms#c#S;j#Is#i#j#Js0L#V#GHj##s#m#j##s0T#,s0Us#ts#p#S4j#Ks$&#j#Ds0{#V#GHj##s#y#j##s2s#,s2ts$$s#|#S0j#Es$&#j#;s2o#V#GHj##s$*#j##s2w#,s2xs$1s$-#S5l#Ls$3C#l#Us$8C#l#<s$?s$:#l#=s$Fs$A#l#>s$Os$H#l#?s$Xs$Q#l#8s$bs$Z#l#@s$fC#l#As$hC#l#9s$ms$j#l#1s$rs$o#l#2s$ys$t#l#3s%$s${#l#4s%,s%&#l#5s%.C#l#6s%0C#l#7s%5s%2#l#)s%:s%7#l#*s%Bs%<#l#+s%Is%D#l#,s%Qs%K#l#:s%Zs%S#l#Bs%bs%^#l#Cs%hs%d#l#Ns%ns%j#l#Fs%ws%p#l#Os&$s%{#l#-s&&s&'#l#.s&+s&,#l#Vs&0s&1#l#Ws&5s&6#l#Xs&<s&=##s$PS:j##s$R##s$KS4j##s$M##s$GS[j##s$I##s$BS;j##s$D##s$<SEj##s$>#?Cs$/WSlCs$+#9C#s$49Cs$,#F#SUGSL#s3E:Cs(<Ks3D:Cs$)Ms3E:C$G#Is4>=C#.Cs3ES)#/s3HJFFI#LEs3IJFFIOAs3JJFFI$#-s3KJFFIs28s$+#>Cs3Ks(D;C#).Cs(ES6#/s3OJFFI#L.Cs#~S)s(G/s3QJFFI#L-s3RJFFIs$%s$2#-s3SJFFIs$(s$3#-s3TJFFI's$4#-s3UJFFI,s$5#l#%#s3Ps3Jl#&5s3X#l#'9s3[#j#PC#j#QC#j#RC#j#ZC#j#[S&#&s3kPk##s2]#*s3rG$#M'CK##s$%Pk##s3q#k##s3r#k##&#k##*#k#PC#k#QC#k#RC#k#ZC#k#[S&#%S/s4#M#S/SOSPSES:S^NOl#(4%#l#Cs$gs$h#l#Bs$js$i#l#Os$ls$m#l#Ns$os$n#j#Ss$q#j#Ts$s#V#GHj##s$v#j##s$|#,s$}s(~s#@#SFj#Gs%##j#Hs%%#V#GHj##s%(#j##s%.#,s%/s)5s#H#S;j#Is%1#j#Js1p#V#GHj##s%5#j##s1x#,s1ys%<s#P#S4j#Ks%J#j#Ds2C#V#GHj##s%A#j##s4;#,s4<s%Hs#X#S0j#Es%J#j#;s47#V#GHj##s%N#j##s4?#,s4@s%Us#`#S5l#Ls%WC#l#Us%\C#l#<s%cs%^#l#=s%js%e#l#>s%ss%l#l#?s%|s%u#l#8s&*s%~#l#@s&.C#l#As&0C#l#9s&5s&2#l#1s&:s&7#l#2s&As&<#l#3s&Hs&C#l#4s&Ps&J#l#5s&RC#l#6s&TC#l#7s&Ys&V#l#)s&^s&[#l#*s&fs&`#l#+s&ms&h#l#,s&us&o#l#:s&~s&w#l#Bs'*s'&#l#Cs'0s',#l#Ns'6s'2#l#Fs'?s'8#l#Os'Hs'C#l#-s'Js'K#l#.s'Os'P#l#Vs'Ts'U#l#Ws'Ys'Z#l#Xs'`s'a#Bs'zs'ys$'#$S:SJ*SGs4j#$#j##s%y#$S4SD*S/s4n#$#j##s%v#$S[ST*SJs4r#$#j##s%t#$S;SY*SDs4v#$#j##s%q#$SESK*STs4z#$#j##s%m#9Cs$1s%a9Cs%Y#F#SUGSL#s4r:Cs)jGs%TIs)e=C#.C#SVs4q/s4sJFFI#LAs4tJFFIs$-#-s4uJFFIs3bs%U#;Cs)ns)m;C#s4vHCs3?DC$#>Cs4ys)n;C#,.C%S6#/s4}JFFI#L.Cs4|S)s)v/s5#JFFI#L>Cs)ts5#.C-S)#/s5&JFFI#L-s5'JFFI&s%c#-s5(JFFIs%Ws%d#-s5)JFFI*s%e#-s5*JFFI3s%f#l#%#s5%s4{l#&;s5-#l#'=s50#j#PC#j#QC#j#RC#j#ZC#j#[S&#&Ps&Lk##s42#$GK$#s5H)#s3Z*s5JQ$#M'C%##EQ$MP*Os5O#$#k##&#k##'#k##)#k##0#k#PC#k#QC#k#RC#k#ZC#k#[S&#Ms/fS(SKSOSPS.S\NOl#(9$#l#Cs&As&B#l#Bs&Ds&C#l#Os&Fs&G#l#Ns&Is&H#j#Ss&K#j#Ts&M#V#GHj##s&P#j##s&V#,s&Ws*Xs#G#SFj#Gs&Y#j#Hs&[#V#GHj##s&^#j##s&d#,s&es*ks#Q#S;j#Is&g#j#Js3J#V#GHj##s&k#j##s3R#,s3Ss&rs#[#S4j#Ks'$#j#Ds3y#V#GHj##s&w#j##s5q#,s5rs&~s#e#S0j#Es'$#j#;s5m#V#GHj##s'(#j##s5u#,s5vs'/s#o#S5l#Ls'1C#l#Us'6C#l#<s'=s'8#l#=s'Ds'?#l#>s'Ms'F#l#?s'Vs'O#l#8s'`s'X#l#@s'dC#l#As'fC#l#9s'ks'h#l#1s'ps'm#l#2s'ws'r#l#3s'~s'y#l#4s(*s($#l#5s(,C#l#6s(.C#l#7s(3s(0#l#)s(8s(5#l#*s(@s(:#l#+s(Gs(B#l#,s(Os(I#l#:s(Xs(Q#l#Bs(`s(\#l#Cs(fs(b#l#Ns(ls(h#l#Fs(us(n#l#Os(~s(y#l#-s)$s)%#l#.s))s)*#l#Vs).s)/#l#Ws)3s)4#l#Xs):s);#$s$7s6B%s$7#j##s'Q#$s$6s6E%s$6#j##s'M#$s$5s6H%s$5#j##s'J#$s$4s6K%s$4#j##s'F#$s$3s6N%s$3#j##s'A#.Cs6=S)s$,/s6@JFFI#LAs6AJFFI#s%V-s6BJFFIs5/s&~#;Cs+:s+7;C#s6CDC#s$+;Cs%Xs$3.C$S6#/s6HJFFI#L.Cs6GS)s+=/s6JJFFI#L.Cs&ySV)/s6LJFFI#L-s6MJFFIs&|s'-#-s6NJFFI&s'.#-s6OJFFI)s'/#-s6PJFFI0s'0#l#%#s6Ks6El#&s$As6S#l#'s%ps6V#j#PC#j#QC#j#RC#j#ZC#j#[S&#$KQ$#s6l)#s4~'C#s%Y$PO$#s6p%s&}#k##s6m#k##s6n#k##(#k##s%b#k#PC#k#QC#k#RC#k#ZC#k#[S&#Ms'vS(SOSPSKS.S\NOl#(4$#l#Cs'bs'c#l#Bs'es'd#l#Os'gs'h#l#Ns'js'i#j#Ss'l#j#Ts'n#V#GHj##s'q#j##s'w#,s'xs+ys#8#SFj#Gs'z#j#Hs'|#V#GHj##s(##j##s()#,s(*s,0s#A#S;j#Is(,#j#Js4k#V#GHj##s(0#j##s4s#,s4ts(7s#J#S4j#Ks(E#j#Ds5>#V#GHj##s(<#j##s76#,s77s(Cs#S#S0j#Es(E#j#;s72#V#GHj##s(I#j##s7:#,s7;s(Ps#\#S5l#Ls(RC#l#Us(WC#l#<s(^s(Y#l#=s(es(`#l#>s(ns(g#l#?s(ws(p#l#8s)%s(y#l#@s))C#l#As)+C#l#9s)0s)-#l#1s)5s)2#l#2s)<s)7#l#3s)Cs)>#l#4s)Ks)E#l#5s)MC#l#6s)OC#l#7s)Ts)Q#l#)s)Ys)V#l#*s)as)[#l#+s)hs)c#l#,s)ps)j#l#:s)ys)r#l#Bs*%s)}#l#Cs*+s*'#l#Ns*1s*-#l#Fs*:s*3#l#Os*Cs*>#l#-s*Es*F#l#.s*Js*K#l#Vs*Os*P#l#Ws*Ts*U#l#Xs*[s*\#Bs*qs*os$$#VSmQs7dVSmKs7e)SGS5#E#j##s(u#)S/SN#E#j##s(q#)SJS:#E#j##s(n#)SDS4#E#j##s(j#)STS[#E#j##s(e#@s(T?C#?Cs(YVT)Cs7xWT*C#s(]9C%#9Cs'.#9Cs(W#9Cs([#9C*#F#SUGSL#s7rCCP:Cs7rK#CCO:Cs(XQ#:C%G#Es7tJFFIS#As7uJFFI#s%`-s7vJFFIs6cs(V#=Cs(V.Cs7vS)#/s7yJFFI#LEs7zJFFIS%As7{JFFI$#-s7|JFFIs6is(\#;Cs,qs'9;C#s7}DC#s%e.C#S6s$</s8%JFFI#L>Cs8%s,y;C#..Cs,xS6#/s8)JFFI#L.Cs8(S)s,|/s8+JFFI#L-s8,JFFIs$@s(h#-s8-JFFIs'Cs(i#-s8.JFFI's(j#-s8/JFFI,s(k#-s80JFFI2s(l#-s81JFFI9s(m#l#%#s8,s8&l#&>s84#l#'s#$s87#j#PC#j#QC#j#RC#j#ZC#j#\C#j#]C#j#[S&#j#^S&#%Os8O&R#k##s7=#&s6XS%k##s7?#$s%ds8T)#s6f*s8VK$#R'C%#*s8YM$#R'CP#)OR#E#k##s8W#k##s8X#k##'#k##+#k##1#k##4#k#PC#k#QC#k#RC#k#ZC#k#\C#k#]C#k#[S&#k#^S&#bHs'Ks2xS(S/SOSPSESKS.S:S\S^NOl#(A$#l#Cs)Ss)T#l#Bs)Vs)U#l#Os)Xs)Y#l#Ns)[s)Z#j#Ss)]#j#Ts)_#V#GHj##s)b#j##s)h#,s)is-js#a#SFj#Gs)k#j#Hs)m#V#GHj##s)p#j##s)v#,s)ws-}s#j#S;j#Is)y#j#Js6\#V#GHj##s)}#j##s6d#,s6es*(s#s#S4j#Ks*6#j#Ds7/#V#GHj##s*-#j##s9'#,s9(s*4s#|#S0j#Es*6#j#;s9##V#GHj##s*:#j##s9+#,s9,s*As$)#S5l#Ls*CC#l#Us*HC#l#<s*Os*J#l#=s*Vs*Q#l#>s*_s*X#l#?s*hs*a#l#8s*rs*j#l#@s*vC#l#As*xC#l#9s*}s*z#l#1s+&s+##l#2s+-s+(#l#3s+4s+/#l#4s+<s+6#l#5s+>C#l#6s+@C#l#7s+Es+B#l#)s+Js+G#l#*s+Rs+L#l#+s+Ys+T#l#,s+as+[#l#:s+js+c#l#Bs+rs+n#l#Cs+xs+t#l#Ns+~s+z#l#Fs,+s,$#l#Os,4s,/#l#-s,6s,7#l#.s,;s,<#l#Vs,@s,A#l#Ws,Es,F#l#Xs,Ls,M#$SAs9y#s$M#j##s*c#$SMs9|#s$M#j##s*_#$S0s:##s$M#j##s*\#$SSs:&#s$M#j##s*X#$SWs:)#s$M#j##s*S#@s$L@#?C#?C%9Cs(ws$L9Cs*B#9Cs*G#9Cs$R#9C'#9C)#F#SUGSL#s9`CCR:C#Ms9`:C#Ks$NCCS#:C#S#s9c:C#Qs$O:C&G#=Cs:[.Cs9cS)#/s9fJFFI#LEs9gJFFINAs9hJFFI$#-s9iJFFIs8Vs*I#Es9jJFFIS$Is:c=C#.C#SVs9l/s9nJFFI#LAs9oJFFI'#-s9pJFFIs8]s*P#Es9qJFFIS*As9rJFFI#s']-s9sJFFIs8`s*S#;Cs'X*.Cs$\S6#/s9vJFFI#L;Cs*Ns$^;C#s9wDC#s'_;Cs)08.C$S6#/s9|JFFI#L;Cs$Ys'j.Cs*US6#/s:#JFFI#LHCs:[;Cs.u#.Cs.xS)#/s:'JFFI#L-s:(JFFIs*Ys*d#-s:)JFFIs$js*e#-s:*JFFI)s*f#-s:+JFFI-s*g#-s:,JFFI4s*h#-s:-JFFI8s*i#-s:.JFFI<s*j#-s:/JFFIs#$s*k#l#%#s:*s:$l#&s#,s:2#l#'s#4s:5#j#PC#j#QC#j#RC#j#ZC#j#\C#j#]C#j#_C#j#`C#j#[S&#j#^S&#j#aS&#&s:IS%k##s9=#%S%s:R&S$#k##s9@#&S<s+^k##s9B#*s:WP$#N'CR#$RS#$#s:[)#s8m$s$bN'C$#*s:_O$#N'CS##)S#S%$Ns;,#$#k##s9D#k##s9E#k##(#k##,#k##2#k##6#k##9#k##=#k#PC#k#QC#k#RC#k#ZC#k#\C#k#]C#k#_C#k#`C#k#[S&#k#^S&#k#aS&#gHs5+s6cs+sS3S(S/SOSPSZSESKS.SRS:SjS\S^NOl#(s#,$#l#Cs+_s+`#l#Bs+bs+a#l#Os+ds+e#l#Ns+gs+f#j#Ss+i#j#Ts+k#V#GHj##s+n#j##s+t#,s+us/vs$##SFj#Gs+w#j#Hs+y#V#GHj##s+|#j##s,&#,s,'s0-s$,#S;j#Is,)#j#Js8h#V#GHj##s,-#j##s8p#,s8qs,4s$5#S4j#Ks,B#j#Ds9;#V#GHj##s,9#j##s;3#,s;4s,@s$>#S0j#Es,B#j#;s;/#V#GHj##s,F#j##s;7#,s;8s,Ms$G#S5l#Ls,OC#l#Us,TC#l#<s,[s,V#l#=s,bs,]#l#>s,ks,d#l#?s,ts,m#l#8s,~s,v#l#@s-&C#l#As-(C#l#9s--s-*#l#1s-2s-/#l#2s-9s-4#l#3s-@s-;#l#4s-Hs-B#l#5s-JC#l#6s-LC#l#7s-Qs-N#l#)s-Vs-S#l#*s-^s-X#l#+s-es-`#l#,s-ms-g#l#:s-vs-o#l#Bs-~s-z#l#Cs.(s.$#l#Ns..s.*#l#Fs.7s.0#l#Os.@s.;#l#-s.Bs.C#l#.s.Gs.H#l#Vs.Ls.M#l#Ws.Qs.R#l#Xs.Xs.Y#Bs.fs.ds$k#0Cs.cBs.es.c$#Bs.js.cs&\#Bs.ms.cs&^#Bs.ps.cs&`#Bs.vs.cs)\##Es/?#s/@S$&$##s2qs/K%s/Ls2q&$#(s/ND'C#E'Cs/Ls/L&s.s#&%#&s/C#&)#&-#m#1#+s/SD0Cs:o'CGs:pm#$#0Cs5@'CQs5Am#$#+S<D0C#'CP$m#$#$SBS+$#D)#s:87#D#E$#Es8Jk##s;C#k##%#7SBD#ESB(S>D#E#k##s;I#k##&#8s8VD#Es8W+s8ED#E#k##s;O#k##&#8S>D+S8D#E#k##s;T#k##s4F#7S8Dk##s;Ws53k##s4D#8S1D+S'D#E#k##s;\#k##s8(#2S-D*D'$#s57'CS'#k##s;s#3S'D#Es2r%s2sD&$#k##s;U#4S?D%Ds56#s57E&$#k##s;S#5S(D'Cs2qEk##s<%#6SHD'Cs2sS@k##s<(#+S@D2S9D+S2D*D#$#s2p'CS2#k##s<.#3S2D#Es2n%s2oD&$#k##s;l#4S.D(SID%D##$E&$#k##s;k#5SID'Cs2lEk##s<=#6S3D'Cs2nSCk##s<@#+SCD(SAD2s2kD+s2bD*D#$#s2c'Cs2e#k##s<G#3s2gD#Es2^%s2_D&$#k##s<)#4s2cD(s2[D%D##$E&$#k##s<(#5s2`D'Cs2VEk##s<V#6s2\D'Cs2Us2Vk##s<Y#+s2XD$s.CD)#s;C(#Dj##s9*s=2j##s2Ss=3j##s2Js=4j##s.0s=5j##s.)s=6l#Bs2#s2$s<rl#:s2's2%#l#Fs2)s2*#l#Cs2,s2+#j#Ss.(#j#Ts.*#V#GHj##s.-#j##s.3#,s.4s25,#SFj#Gs.6#j#Hs.8#V#GHj##s.;#j##s.A#,s.Bs2H3#S;j#Is2T#j#Js;'#V#GHj##s2X#j##s;/#,s;0s2c:#S4j#Ks9F#j#Ds;V#V#GHj##s2h#j##s=N#,s=Os2sA#S0j#Es9H#j#;s=J#V#GHj##s9L#j##s=R#,s=Ss9Qs#(#S5l#Ls#*C#l#Us#.C#l#<s#2s#0#l#=s#6s#4#l#>s#=s#8#l#?s#Cs#?#l#8s#Js#E#l#@s#LC#l#As#NC#l#9s#Rs#P#l#1s#Vs#T#l#2s#]s#X#l#3s#cs#_#l#4s#js#e#l#5s4#C#l#6s#mC#l#7s#qs#o#l#)s#us#s#l#*s#{s#w#l#+s$%s#}#l#,s$+s$'#l#:s$1s$-#l#Bs$5s$3#l#Cs$;s$7#l#Ns$Bs$=#l#Fs$Is$D#l#Os$Os$K#l#-s0]s0^#l#.s0bs0c#l#Vs$Vs$W#l#Ws$[s$\#l#Xs$_s$`#m##s=HWT+s1ZD#ZT,Cs1[s15s$fs$e#)s1_s1VZT-Cs1\s1C$#Hl#,s1es1_#l#bs<*C#l#cs52C#l#Ms=8C#l#ds59s55#l#es7_s7Z#l#fs9=s99#l#gs;?s;:#l#hs<Ds<@#l#is=Ts=O#l#js>@C#l#ks>AC#l#ls>Hs>C#l#ms>Is>D#XT.s>ns>nGHWS`s>os>o#1s>q#+#D*#D#E##$&&$#WSas>vs>v*1s>x#$*#$#D)#s<O+#D*#D#'#%$'&$#(0D'C#E((D'C#E)*4+#D#E#+2D$#s>q#&#&&#*(D'C#*&%#&-#&0#&3#&>#m#s#'#US_s#'#E##$s#'&$#USbs#+#B#%$B&$#(*D'C#E((D'C#EUScs#3#E##$;&$#*&D)/3'C$#&&#&+#&.#&1#&6#m#;#j#ns?P#j#os?Q#V#GHj#os?S#j#os?T#YT/s?Us?Us?2#Hj#5s?U##"). Qed.

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
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.pages_total); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_bounds); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_lo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_hi); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_npagesZ); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.EnvRing.Pinj); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PX); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Logic.False)|] [|@S; @__ff; @__varmap; @__wit; @__arith; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @__x9; @__x10; @__x11; @__x12; @__x13; @__p1; @__p2; @__p3; @__p4; @__p5; @r2; @q1; @H14; @H13; @H12; @H11; @H10; @r1; @q0; @H9; @H8; @H7; @H6; @H5; @r0; @q; @H4; @H3; @H2; @H1; @H0; @__sat0; @__sat1; @__sat2; @H; @IH; @r|] "#3##D$;#R#T#Y#Z#X#p#O#^$,$6#%#4#D#]#2#5$8#3#8#+#6#7###$#,#-#.#/#0#L#)#*#1#:#?#(#;#<#&#'$?#G#Q#b#c#k#r#v#w#9#=$($*#J#I#H#S#U#W#\#_#a#e#f#`#g#t#x#z$+$.$1$/$7$;$>#C#>#M$#$%#d#N$4#[#V#h$$$'#o#q$&$9#l$5#j#i#n#s#m#K#u$-$2$0$3$<$)$:#P$=#y#{#|#}#~H#r&#s&#t&#u%#v+#w'#x*#y%#z%#{$#|%#}%#~%$#*$$%$%%$&%$'$$($$)%$*&$+$$,%$-&$.'$/$$0%$1&$2&$3)$4$$5&$6%$7%$8%$9%$:%8S08#8#8#8#8#USH#USI#VSJ##US<#AS)&I#j#$%#US=CUS<CUSKDUSLDUSMDVSNDI(D#P#)%GEEF#JVSO&FVSPS>S?VSQS)M%S>#S?m$%#WSRDIS*XSSS)M$#l#%*)#l#&0/#l#'32#&IIl#($#S)US=;A#&I#m#&#USTM4M&I#WS@s##s##M3s#%#&&#*&#7s#'s#'M3s#)#1'#5M&$#1%H-%#*%#.0H%D#I.)H%D#IUSAM&I#6/HUSUs#=1$#&'#*'#9)HVSB3<%D$#*&#*.#*1#*4#*=#5S9VSC#H&I$&IH5S6.#H&I#k##&#k##(#7s#Ks#KS:3s#M#VSV#H&I$7s#Os#OS13s#Q#6#H&I#k##0#k##(#4S6VSC#H&I$4S2.#H&I#k##8#k##'#C/H%DHIUSW#7s#`s#`S23s#b#6#H9H#.%H1$#%D'#k##*#D)H-IH7s#js#jS&3s#l#.#H&I#-$H*$#k##)#E(H-HI7s#ss#sS+3s#u#.#H-H#&$I*$#k##)#F(H7s#{s#{S,3s#}#6#H%D#Ik##s###G&H7s$%s$%S-3s$'#.#H%D#$k##s#)#6&H7s$+s$+S.3s$-#.#H4S/C#H4S36#H9H#.%H1$#%D'#k##s#5#D)H4Q.#H&I#-$H*$#k##s#2#E(H4S$.#H-H#&$I*$#k##s#0#F(H4N6#H%D#Ik##s#I#G&H4R.#H%D#$k##s#N#6&H4S'.#H5S(C#H5S%6#H9H#.%H1$#%D'#k##s#Y#D)H5SD.#H&I#-$H*$#k##s#V#E(H5S4.#H-H#&$I*$#k##s#T#F(H5S76#H%D#Ik##s#m#G&H5S8.#H%D#$k##s#r#6&H5SE.#H,SF,#,#,#,#,#,#,#,#,#,#,#,#,#/D#USXS0VSGD#/D*?D$#$D'#+#K,*,#/D#?D*#$D-#+#K/D($D#&+#K$D%.+#K,,,#,#/D#$D#4+#K$D%0+#K,(,#/D#?D=#$D@#+#K$D-%+#K$D7'+#K/D,$D#s##+#K$D%,+#K$D'A+#K,2,#,#/D#$D#s#-+#K$D%s#)+#K$D'8+#K/Ds#C:Ds#8#/Ds#;/Ds#AVSYDs%-/Ds#D:D$#/Ds#G/Ds#L?Ds#>#$D,#$D&#$D(#$D,#$D.#$Ds#9#$D1#+#K:Ds#44$D#&+#K:Ds#?7<S08#VSGDIXSZDs#NS0#WS[D%#?D#s#R$Ds#O1$D=#$D%#$D,#+#K/Ds#[$D?=$D$#$Ds#$#+#K:Ds#/s#($D#:+#K:Ds#<s#+$D#=+#K,s#6/D#$D#s#a+#K$D%s#]+#K:D's#4$D#s#&+#K$D*s#O+#K/Ds#|/DSF$D$#$Ds#<#+#K#C#s&7#C$##C%##C&##C'##C(##C)##C*##C+##C,##C-##C.##C/##C0##C1##C2##C3##C4##C5##C6##C7##C8##C9##C:##C;##C<##C=##C>##C?##C@##CA##CB##Cs#9##Cs#:##Cs#;##Cs#<##Cs#=##Cs#>##Cs#?##Cs#@##Cs#A##Cs#B##Cs#C##Cs#D##Cs#E##Cs#F##Cs#G##Cs#H##Cs#I##Cs#J##Cs#K##Cs#L##Cs#M##Cs#N##Cs#O##Cs#P##Cs#Q##Cs#R##Cs#S##Cs#T##Cs#U##Cs#V##Cs#W##Cs#X##Cs#Y##Cs#Z##Cs#[##Cs#\##Cs#]##Cs#^##Cs#_##Cs#`##Cs#a##Cs#b##Cs#c##Cs#d##Cs#e##Cs#f##Cs#g##Cs#h##Cs#i##Cs#j##Cs#k##Cs#l##Cs#m##Cs#n##Cs#o##Cs#p##Cs#q##Cs#r##Cs#s##Cs#t##Cs#u##Cs#v##Cs#w##Cs#x##Cs#y##Cs#z##Cs#{##Cs#|##Cs#}##Cs#~##Cs$###Cs$$##Cs$%##Cs$&##Cs$'##Cs$(##Cs$)##Cs$*##Cs$+##Cs$,##Cs$-##Cs$.##Cs$/##Cs$0##Cs$1##Cs$2##Cs$3##Cs$4##Cs$5##Cs$6##Cs$7##Cs$8##Cs$9##Cs$:##Cs$;##Cs$<##Cs$=##Cs$>##Cs$?##Cs$@##Cs$A##Cs$B##Cs$C##Cs$D##Cs$E##Cs$F##Cs$G##Cs$H##Cs$I##Cs$J##Cs$K##Cs$L##Cs$M##Cs$N##Cs$O##Cs$P##Cs$Q##Cs$R##Cs$S##Cs$T##Cs$U##Cs$V##Cs$W##Cs$X##Cs$Y##Cs$Z##Cs$[##Cs$\##Cs$G##Cs$H##Cs$I##Cs$J##Cs$a##Cs$b##Cs$M##Cs$N##Cs$O##Cs$P##Cs$Q##Cs$R##Cs$S##Cs$T##Cs$k##Cs$l##Cs$m##Cs$n##Cs$Y##Cs$Z##Cs$[##Cs$\##Cs$]##Cs$^##Cs$_##Cs$`##Cs$w##Cs$x##Cs$y##Cs$z##Cs$e##Cs$f##Cs$g##Cs$h##Cs$i##Cs$j##Cs$k##Cs$l##Cs$m##Cs$n##Cs%)##Cs%*##Cs$q##Cs$r##Cs$s##Cs$t##Cs$u##Cs$v##Cs$w##Cs$x##Cs$y##Cs%4##Cs%5##Cs$|##Cs$}##Cs$~##Cs%###Cs%$##Cs%%##Cs%&##Cs%'##Cs%>##Cs%?##Cs%@##Cs%A##Cs%,##Cs%-##Cs%.##Cs%/##Cs%0##Cs%1##Cs%2##Cs%3##Cs%J##Cs%K##Cs%L##Cs%M##Cs%8##Cs%9##Cs%:##Cs%;##Cs%<##Cs%=##Cs%>##Cs%?##Cs%V##Cs%W##Cs%X##Cs%Y##Cs%D##Cs%E##Cs%F##Cs%G##Cs%H##Cs%I##Cs%J##Cs%K##Cs%b##Cs%c##Cs%d##Cs%e##Cs%P##Cs%Q##Cs%R##Cs%S##Cs%T##Cs%U##Cs%V##Cs%W##Cs%n##Cs%o##Cs%p##Cs%q##Cs%\##Cs%]##Cs%^##Cs%_##Cs%`##Cs%a##Cs%b##Cs%c##Cs%z##Cs%{##Cs%|##Cs%}##Cs%h##Cs%i##Cs%j##Cs%k##Cs%l##Cs%m##Cs%n##Cs%o##Cs&*##Cs&+##Cs&,##Cs&-##Cs%t##Cs%u##Cs%v##Cs%w##Cs%x##Cs%y##Cs%z##Cs%{##Cs&6##Cs&7##Cs&8##Cs&9##Cs&$##Cs&%##Cs&&##Cs&'##Cs&(##Cs&)##Cs&*##Cs&+##Cs&B##Cs&C##Cs&D##Cs&E##Cs&F##Cs&G##Cs&H##Cs&I##Cs&J##Cs&K##Cs&L##Cs&M##Cs&N##Cs&O##Cs&P##Cs&Q##Cs&R##Cs&S##Cs&T##Cs&U##Cs&V##Cs&W##Cs&X##Cs&Y##Cs&Z##Cs&[##Cs&\##Cs&]##Cs&^##Cs&_##Cs&`##Cs&a##Cs&b##Cs&c##Cs&d##Cs&e##Cs&f##Cs&g##Cs&h##Cs&i##Cs&T##Cs&U##Cs&V##Cs&W##Cs&n##Cs&o##Cs&p##Cs&q##Cs&\##Cs&]##Cs&^##Cs&_##Cs&v##Cs&w##Cs&x##Cs&y##Cs&z##Cs&{##Cs&|##Cs&}##Cs&h##Cs&i##Cs&j##Cs&k##Cs&l##Cs&m##Cs&n##Cs&o##Cs'*##Cs'+##Cs',##Cs'-##Cs&t##Cs&u##Cs&v##Cs&w##Cs&x##Cs&y##Cs&z##Cs&{##Cs'6##Cs'7##Cs'8##Cs'9##Cs':##Cs';##Cs'<##Cs'=##Cs'>##Cs'?##Cs'@##Cs'A##Cs'B##Cs'C##Cs'D##Cs'E##Cs'F##Cs'G##Cs'H##Cs'I##Cs'J##Cs'K##Cs'L##Cs'M##Cs'N##Cs'O##Cs'P##Cs'Q##Cs'R##Cs'S##Cs'T##Cs'U##Cs'V##Cs'W##Cs'X##Cs'Y##Cs'D##Cs'E##Cs'F##Cs'G##Cs'H##Cs'I##Cs'J##Cs'K##Cs'b##Cs'c##Cs'd##Cs'e##Cs'P##Cs'Q##Cs'R##Cs'S##Cs'T##Cs'U##Cs'V##Cs'W##Cs'n##Cs'o##Cs'p##Cs'q##Cs'r##Cs's##Cs't##Cs'u##Cs'`##Cs'a##Cs'b##Cs'c##Cs'z##Cs'{##Cs'|##Cs'}##Cs'h##Cs'i##Cs'j##Cs'k##Cs(&##Cs('##Cs((##Cs()##Cs(*##Cs(+##Cs(,##Cs(-##Cs(.##Cs(/##Cs(0##Cs(1##Cs(2##Cs(3##Cs(4##Cs(5##Cs(6##Cs(7##Cs(8##Cs(9##Cs(:##Cs(;##Cs(<##Cs(=##Cs(>##Cs(?##Cs(@##Cs(A##Cs(B##Cs(C##Cs(D##Cs(E##Cs(F##Cs(G##Cs(H##Cs(I##Cs(J##Cs(K##Cs(6##Cs(7##Cs(8##Cs(9##Cs(:##Cs(;##Cs(<##Cs(=##Cs(>##Cs(?##Cs(@##Cs(A##Cs(B##Cs(C##Cs(D##Cs(E##Cs)T##Cs)O##Cs)M##Cs)L##Cs)G##Cs)F##Cs)T##Cs)[##Cs)\##Cs)D##Cs)C##Cs)N##Cs)U##Cs)D##Cs)I##Cs)c##Cs)d##Cs)L##Cs)I##Cs)\##Cs)H##Cs)G##Cs)Q##Cs)k##Cs)l##Cs)g##Cs)J##Cs)O##Cs)e##Cs)h##Cs)l##Cs)s##Cs)t##Cs)o##Cs)m##Cs)l##Cs(v##Cs(u##Cs)t##Cs){##Cs)|##Cs)d##Cs(u##Cs(}##Cs)u##Cs)d##Cs)i##Cs*'##Cs*(##Cs)l##Cs)i##Cs)|##Cs)w##Cs)n##Cs)q##Cs*/##Cs*0##Cs*+##Cs){##Cs)~##Cs*)##Cs*,##Cs*0##Cs*7##Cs*8##Cs*3##Cs*1##Cs*0##Cs*+##Cs**##Cs*8##Cs*?##Cs*@##Cs)]##Cs)[##Cs*2##Cs*9##Cs)R##Cs)N##Cs*G##Cs*H##Cs)Q##Cs)W##Cs*@##Cs)J##Cs)F##Cs)j##Cs*O##Cs*P##Cs*K##Cs)N##Cs)Q##Cs*I##Cs*L##Cs*P##Cs*W##Cs*X##Cs*S##Cs*Q##Cs*P##Cs*<##Cs*9##Cs*X##Cs*_##Cs*`##Cs)}##Cs)d##Cs*C##Cs*Y##Cs)r##Cs)n##Cs*g##Cs*h##Cs)q##Cs)w##Cs*`##Cs*[##Cs**##Cs*.##Cs*o##Cs*p##Cs*k##Cs*_##Cs*b##Cs*i##Cs*l##Cs*p##Cs*w##Cs*x##Cs*s##Cs*q##Cs*p##Cs*k##Cs*j##Cs*x##Cs+###Cs+$##Cs*A##Cs*?##Cs*r##Cs*y##Cs*6##Cs*2##Cs++##Cs+,##Cs*5##Cs*;##Cs+$##Cs*l##Cs*3##Cs*N##Cs+3##Cs+4##Cs+/##Cs*n##Cs*s##Cs+-##Cs+0##Cs+4##Cs+;##Cs+<##Cs+7##Cs+5##Cs+4##Cs*r##Cs*q##Cs+<##Cs+C##Cs+D##Cs*a##Cs*K##Cs*y##Cs+=##Cs*V##Cs*R##Cs+K##Cs+L##Cs*U##Cs*[##Cs+D##Cs+?##Cs*j##Cs*n##Cs+S##Cs+T##Cs+O##Cs+C##Cs+F##Cs+M##Cs+P##Cs+T##Cs+[##Cs+\##Cs+W##Cs+U##Cs+T##Cs+O##Cs+N##Cs+\##Cs+c##Cs+d##Cs+L##Cs+K##Cs+V##Cs+]##Cs+L##Cs+Q##Cs+k##Cs+l##Cs+T##Cs+Q##Cs+d##Cs+F##Cs+C##Cs+Y##Cs+s##Cs+t##Cs+o##Cs+J##Cs+M##Cs+m##Cs+p##Cs+t##Cs+{##Cs+|##Cs+w##Cs+u##Cs+t##Cs+`##Cs+]##Cs+|##Cs,'##Cs,(##Cs+l##Cs+d##Cs+g##Cs+}##Cs+l##Cs+q##Cs,/##Cs,0##Cs+t##Cs+q##Cs,(##Cs,###Cs+v##Cs+y##Cs,7##Cs,8##Cs,3##Cs,'##Cs,*##Cs,1##Cs,4##Cs,8##Cs,?#=DS&=DS.;D$S:#=DS,;D#S1s.h;D%M#=DS+=DS/;D$S6#=DS-;D#S2s.n;D%S9#;D)S*#<s+d2D#(D#Ls.p)s.rGEEF#JUS\E<s/(2D#2Ds+j(D$L#)s.xGEEF#J's.yGEEF)(#<s+n2D#(D#Ls.{)s.}GEEF#J's.~GEEF.-#(D1S#s.~)s/$GEEF#J(D3S#.)s/&GEEF#J@s/'GEEFQ0s/(GEEF$#'s/)GEEF'4#(Ds/)S#8)s/+GEEF#J@s/,GEEFS$(D6S#;)s/.GEEF#J0s//GEEF%#'s/0GEEF';#ZS]s/1GEEF=BD@5>D#<(D<L#)s/5GEEF#J's/6GEEF'A#2Ds/F2Ds,-(D$L#)s/:GEEF#J's/;GEEFs#'s#&#8s,02D#(D#Ls/=)s/?GEEF#J's/@GEEFs#,s#+#(Ds#/S#,)s/BGEEF#J@s/CGEEFN0s/DGEEF$#'s/EGEEFs##s#0#@s/FGEEFR(D2S#s#5)s/HGEEF#J0s/IGEEF%#'s/JGEEFAs#5#BDs#90>D#7(D7L#)s/NGEEF#J's/OGEEF@s#:#<s/a<#2D#2D%(D$L#)s/UGEEF#J's/VGEEFs#Bs#A#8)2D#(D#Ls/X)s/ZGEEF#J's/[GEEFs#Gs#F#(Ds#JS#,)s/]GEEF#J(D.Ps/])s/_GEEF#J0s/`GEEF%#'s/aGEEFs#?s#L#(Ds/aP2)s/cGEEF#J(D4S#s#R)s/eGEEF#J0s/fGEEF%#'s/gGEEFs#>s#R#BDs#V2>D#9(D9L#)s/kGEEF#J's/lGEEFs#=s#W#(Ds/lPs#7)s/nGEEF#J2Ds0#(Ds#:P#)s/qGEEF#J0s/rGEEF&#>D&B(D#Ps#\)s/uGEEF#J>D%s#d(Ds#_S##)s/xGEEF#J0s/yGEEF&#(Ds#ELs/y)s/{GEEF#J(Ds#eLs/{)s/}GEEF#J2DS0(Ds/~P#)s0$GEEF#J@s0%GEEFS'0s0&GEEF$#BD's#qWS^Ds#ls#N(D$L#)s0*GEEF#J0s0+GEEF'#0s0,GEEF-#0s0-GEEF0#0s0.GEEF3#0s0/GEEF;#2Ds0A(Ds00P#)s02GEEF#J>D3%(Ds03P#)s05GEEF#J's06GEEF&s#}#'s07GEEF*s#~#'s08GEEFs#*s$##'s09GEEFs#0s$$#'s0:GEEFs#7s$%#'s0;GEEFs#>s$&#'s0<GEEFs#Ds$'#'s0=GEEFs#Ls$(#'s0>GEEFs#Rs$)#'s0?GEEFs#Xs$*#'s0@GEEFs#^s$+#'s0AGEEFs#ds$,#'s0BGEEFs#js$-#'s0CGEEFs#qs$.#'s0DGEEFs#ys$/#'s0EGEEFs$%s$0#'s0FGEEFs$+s$1#l#%#s0Cs0=l#&s$8s0I#l#'s$Fs0L#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#j#0D#j#1D#j#2D#j#3D#j#4D#j#5D#j#6O#j#7O#j#8O#j#9O#j#:O#%DS1I%DS+S1k##$#%DS2I%DS3Ik##$#-S&I-S+S-*#S$k##%#-IS+-S.S,*R#k##%#%DS,Ik###S;9S-N1#S/%DS,#k##&#%DS-I%DS/S&k##$#%DS.I%DRIk##$#-S/I-S3Q*#S4k##%#-IS3-S$Q*S8#k##%#%DQIk###S;9S$S%1#N%DS.#k##&#%DS$I%DS%Qk##$#%DNI%DS%Ik##$#-RI-S'S4&S4I*$#k##&#-IS'&IS7-S7S(*$#k##&#%DS(Ik###S;9S%S71#S8%DS'#k##&#&IN&NR*$#1RS'&#S(1$S%-S(#*%#%DSDI%DS4I&IQ*#S_9QS%VSBS(N%D$#*&#*)#*+#*-#*3#1NR&I#k##8#k##&#k##;#k##B#k##s#(#k##s#.#k##s#2#k##s#6#k##s#=#k##s#B#k##s#G#k##s#K#k##s#O#k##s#V#k##s#[#k##s#`#k##s#d#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#k#0D#k#1D#k#2D#k#3D#k#4D#k#5D#k#6O#k#7O#k#8O#k#9O#k#:O#USAS51S$s1N&$#&IS&&S&I&IS*&S*I5S57s2-s2-S53s2/#WS@s2/s2/S53s21#4S5AS`i#FS).-,+*MS+QS$S*S&H)'%$#0S9S:S6S1S2S,S-S.S/S3NRS'S(S%S8SEl#(s$-2#l#;s/zD#l#<s/}D#l#=s0's0##l#>s0-s0)#l#?s05s0/#l#@s0=s07#l#As0Fs0?#l#Bs0ID#l#Cs0LD#l#Ds0Rs0N#l#Es0Xs0T#l#Fs0`s0Z#l#Gs0hs0b#l#Hs0qs0j#l#Is0tD#l#Js0xD#l#Ks1#s0z#l#Ls1*s1%#l#Ms14s1,#l#Ns1>s16#l#Os1Js1@#l#Ps1Rs1L#l#Qs1\s1U#l#Rs1gs1`#l#Ss2/s1j##s2MMS*A#&I#m#&#j#Ts2N#j#$s2Q#j#Us2S#YSas2Ts2Ps28#S)j#$s2T##"). Qed.

Lemma pages_total_le_wbudget : forall S, (pages_total S <= wbudget S)%Z.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.pages_total); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.wbudget); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_bounds); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_lo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_hi); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_npagesZ); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.EnvRing.Pinj); constr:(@Stdlib.micromega.EnvRing.PX); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Logic.False)|] [|@S; @__ff; @__varmap; @__wit; @__arith; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @__x9; @__x10; @__x11; @__x12; @__x13; @__x14; @__p1; @__p2; @__p3; @__p4; @r2; @q1; @H14; @H13; @H12; @H11; @H10; @r1; @q0; @H9; @H8; @H7; @H6; @H5; @r0; @q; @H4; @H3; @H2; @H1; @H0; @__sat0; @__sat1; @__sat2; @H; @IH; @r|] "#31#@$;#N#P#U#V#T#m#Y#[$)$3#4#%#6#Z#2$5#5#9#@###+#$#.#/#0#1#7#8#H#-#3#;#<#?#(#*#,#:#=#&#'#)$<#C#M#X#_#`#h#o#s#t$%$'#>#F#E#D#O#Q#S#\#^#b#c#]#d#q#u#w$($+$-$,$4$8$;#I#|#~#J#a#W#R$0#e$$#}#l#n$##i$1$6#g#f#k#p#G#j#r$9$*$/$.$2$&#K#L$7$:#v#x#y#z#{I#q&#r&#s%#t&#u'#v*#w+#x%#y$#z%#{%#|%#}%#~%$#%$$*$%%$&$$'$$(%$)$$*&$+%$,&$-&$.%$/'$0$$1&$2$$3$$4)$5&$6%$7%$8%$9%$:%7S/7#7#7#7#7#USJ#USK#VSL##US>#@S&AS&%$#j#$&#US?CUS>CUSMDUSNDUSODVS@DI'D#P#(%GEEF#JVSP&FVSQSASBVSRS&N&SA#SBm$%#WSSDIS(XSTS&N$#l#%*)#l#&0/#l#'32#%IIl#($#S&US?<@#A$%$#m#'#USUN4N%I#WSCs#%s#%N3s#'#%&#*&#8s#)s#)N3s#+#0'#5N%$#0%H-%#*%#.0H&D#I.)H&D#IUSDN%I#6/HUSVs#?0$#%'#*'#9)HVSE3<&D$#*&#*.#*1#*4#*=#5S:VSF#H%I$%IH5S5.#H%I#k##&#k##(#8s#Ms#MS;3s#O#VSW#H%I$8s#Qs#QS<3s#S#6#H%I#k##0#k##(#4S5VSF#H%I$4S6.#H%I#k##8#k##'#D/H&DHIUSX#8s#bs#bS63s#d#6#H9H#.%H0$#&D'#k##*#E)H-IH8s#ls#lS'3s#n#.#H%I#-$H*$#k##)#F(H-HI8s#us#uS73s#w#.#H-H#%$I*$#k##)#G(H8s#}s#}S03s$##6#H&D#Ik##s###H&H8s$'s$'S)3s$)#.#H&D#$k##s#)#6&H8s$-s$-S*3s$/#.#H4S+D#H4S,6#H9H#.%H0$#&D'#k##s#5#E)H4Q.#H%I#-$H*$#k##s#2#F(H4S1.#H-H#%$I*$#k##s#0#G(H4M6#H&D#Ik##s#I#H&H4S#.#H&D#$k##s#N#6&H4O.#H5S-D#H5S.6#H9H#.%H0$#&D'#k##s#Y#E)H5S$.#H%I#-$H*$#k##s#V#F(H5S8.#H-H#%$I*$#k##s#T#G(H5S26#H&D#Ik##s#m#H&H5S3.#H&D#$k##s#r#6&H5S9.#H+SG+#+#+#+#+#+#+#+#+#+#+#+#+#+#/D#USYS/VSHD#/D*?D$#$D'#,#K+*+#/D#?D*#$D-#,#K/D($D#&,#K$D%.,#K+,+#+#/D#$D#4,#K$D%0,#K+(+#/D#?D=#$D@#,#K$D-%,#K$D7',#K/D,$D#s##,#K$D%,,#K$D'A,#K+2+#+#/D#$D#s#-,#K$D%s#),#K$D'8,#K/Ds#C;Ds#8#/Ds#;/Ds#AVSZDs%./Ds#D;D$#/Ds#G/Ds#M?Ds#>#$D,#$D&#$D(#$D,#$D.#$Ds#9#$D1#,#K;Ds#44$D#&,#K;Ds#?7VSHDIXS[Ds#LS/#WS\Ds%}#?D#s#P$Ds#M/$D;#$D%#$D*#,#K/Ds#Y$D=;$D$#$DB#,#K;Ds#-s#&$D#8,#K;Ds#:s#)$D#;,#K+s#4/D#$D#s#_,#K$D%s#[,#K;D's#2$D#s#$,#K$D*s#M,#K/Ds#y/Ds#|/DSG$D$#$D&#,#K#C#s&8#C$##C%##C&##C'##C(##C)##C*##C+##C,##C-##C.##C/##C0##C1##C2##C3##C4##C5##C6##C7##C8##C9##C:##C;##C<##C=##C>##C?##C@##CA##CB##Cs#:##Cs#;##Cs#<##Cs#=##Cs#>##Cs#?##Cs#@##Cs#A##Cs#B##Cs#C##Cs#D##Cs#E##Cs#F##Cs#G##Cs#H##Cs#I##Cs#J##Cs#K##Cs#L##Cs#M##Cs#N##Cs#O##Cs#P##Cs#Q##Cs#R##Cs#S##Cs#T##Cs#U##Cs#V##Cs#W##Cs#X##Cs#Y##Cs#Z##Cs#[##Cs#\##Cs#]##Cs#^##Cs#_##Cs#`##Cs#a##Cs#b##Cs#c##Cs#d##Cs#e##Cs#f##Cs#g##Cs#h##Cs#i##Cs#j##Cs#k##Cs#l##Cs#m##Cs#n##Cs#o##Cs#p##Cs#q##Cs#r##Cs#s##Cs#t##Cs#u##Cs#v##Cs#w##Cs#x##Cs#y##Cs#z##Cs#{##Cs#|##Cs#}##Cs#~##Cs$###Cs$$##Cs$%##Cs$&##Cs$'##Cs$(##Cs$)##Cs$*##Cs$+##Cs$,##Cs$-##Cs$.##Cs$/##Cs$0##Cs$1##Cs$2##Cs$3##Cs$4##Cs$5##Cs$6##Cs$7##Cs$8##Cs$9##Cs$:##Cs$;##Cs$<##Cs$=##Cs$>##Cs$?##Cs$@##Cs$A##Cs$B##Cs$C##Cs$D##Cs$E##Cs$F##Cs$G##Cs$H##Cs$I##Cs$J##Cs$K##Cs$L##Cs$M##Cs$N##Cs$O##Cs$P##Cs$Q##Cs$R##Cs$S##Cs$T##Cs$U##Cs$V##Cs$W##Cs$X##Cs$Y##Cs$Z##Cs$[##Cs$\##Cs$]##Cs$G##Cs$H##Cs$I##Cs$J##Cs$b##Cs$c##Cs$M##Cs$N##Cs$O##Cs$P##Cs$Q##Cs$R##Cs$S##Cs$T##Cs$l##Cs$m##Cs$n##Cs$o##Cs$Y##Cs$Z##Cs$[##Cs$\##Cs$]##Cs$^##Cs$_##Cs$`##Cs$x##Cs$y##Cs$z##Cs${##Cs$e##Cs$f##Cs$g##Cs$h##Cs$i##Cs$j##Cs$k##Cs$l##Cs$m##Cs$n##Cs%*##Cs%+##Cs$q##Cs$r##Cs$s##Cs$t##Cs$u##Cs$v##Cs$w##Cs$x##Cs$y##Cs%5##Cs%6##Cs$|##Cs$}##Cs$~##Cs%###Cs%$##Cs%%##Cs%&##Cs%'##Cs%?##Cs%@##Cs%A##Cs%B##Cs%,##Cs%-##Cs%.##Cs%/##Cs%0##Cs%1##Cs%2##Cs%3##Cs%K##Cs%L##Cs%M##Cs%N##Cs%8##Cs%9##Cs%:##Cs%;##Cs%<##Cs%=##Cs%>##Cs%?##Cs%W##Cs%X##Cs%Y##Cs%Z##Cs%D##Cs%E##Cs%F##Cs%G##Cs%H##Cs%I##Cs%J##Cs%K##Cs%c##Cs%d##Cs%e##Cs%f##Cs%P##Cs%Q##Cs%R##Cs%S##Cs%T##Cs%U##Cs%V##Cs%W##Cs%o##Cs%p##Cs%q##Cs%r##Cs%\##Cs%]##Cs%^##Cs%_##Cs%`##Cs%a##Cs%b##Cs%c##Cs%{##Cs%|##Cs%}##Cs%~##Cs%h##Cs%i##Cs%j##Cs%k##Cs%l##Cs%m##Cs%n##Cs%o##Cs&+##Cs&,##Cs&-##Cs&.##Cs%t##Cs%u##Cs%v##Cs%w##Cs%x##Cs%y##Cs%z##Cs%{##Cs&7##Cs&8##Cs&9##Cs&:##Cs&$##Cs&%##Cs&&##Cs&'##Cs&(##Cs&)##Cs&*##Cs&+##Cs&C##Cs&D##Cs&E##Cs&F##Cs&G##Cs&H##Cs&I##Cs&J##Cs&K##Cs&L##Cs&M##Cs&N##Cs&O##Cs&P##Cs&Q##Cs&R##Cs&S##Cs&T##Cs&U##Cs&V##Cs&W##Cs&X##Cs&Y##Cs&Z##Cs&[##Cs&\##Cs&]##Cs&^##Cs&_##Cs&`##Cs&a##Cs&b##Cs&c##Cs&d##Cs&e##Cs&f##Cs&g##Cs&h##Cs&i##Cs&j##Cs&T##Cs&U##Cs&V##Cs&W##Cs&o##Cs&p##Cs&q##Cs&r##Cs&\##Cs&]##Cs&^##Cs&_##Cs&w##Cs&x##Cs&y##Cs&z##Cs&{##Cs&|##Cs&}##Cs&~##Cs&h##Cs&i##Cs&j##Cs&k##Cs&l##Cs&m##Cs&n##Cs&o##Cs'+##Cs',##Cs'-##Cs'.##Cs&t##Cs&u##Cs&v##Cs&w##Cs&x##Cs&y##Cs&z##Cs&{##Cs'7##Cs'8##Cs'9##Cs':##Cs';##Cs'<##Cs'=##Cs'>##Cs'?##Cs'@##Cs'A##Cs'B##Cs'C##Cs'D##Cs'E##Cs'F##Cs'G##Cs'H##Cs'I##Cs'J##Cs'K##Cs'L##Cs'M##Cs'N##Cs'O##Cs'P##Cs'Q##Cs'R##Cs'S##Cs'T##Cs'U##Cs'V##Cs'W##Cs'X##Cs'Y##Cs'Z##Cs'D##Cs'E##Cs'F##Cs'G##Cs'H##Cs'I##Cs'J##Cs'K##Cs'c##Cs'd##Cs'e##Cs'f##Cs'P##Cs'Q##Cs'R##Cs'S##Cs'T##Cs'U##Cs'V##Cs'W##Cs'o##Cs'p##Cs'q##Cs'r##Cs's##Cs't##Cs'u##Cs'v##Cs'`##Cs'a##Cs'b##Cs'c##Cs'{##Cs'|##Cs'}##Cs'~##Cs'h##Cs'i##Cs'j##Cs'k##Cs('##Cs((##Cs()##Cs(*##Cs(+##Cs(,##Cs(-##Cs(.##Cs(/##Cs(0##Cs(1##Cs(2##Cs(3##Cs(4##Cs(5##Cs(6##Cs(7##Cs(8##Cs(9##Cs(:##Cs(;##Cs(<##Cs(=##Cs(>##Cs(?##Cs(@##Cs(A##Cs(B##Cs(C##Cs(D##Cs(E##Cs(F##Cs(G##Cs(H##Cs(I##Cs(J##Cs(K##Cs(L##Cs(6##Cs(7##Cs(8##Cs(9##Cs(:##Cs(;##Cs(<##Cs(=##Cs(>##Cs(?##Cs(@##Cs(A##Cs(B##Cs(C##Cs(D##Cs(E##Cs)S##Cs)N##Cs)L##Cs)K##Cs)F##Cs)E##Cs)S##Cs)Z##Cs)[##Cs)C##Cs)B##Cs)M##Cs)T##Cs)C##Cs)H##Cs)b##Cs)c##Cs)K##Cs)H##Cs)[##Cs)G##Cs)F##Cs)P##Cs)j##Cs)k##Cs)f##Cs)I##Cs)N##Cs)d##Cs)g##Cs)k##Cs)r##Cs)s##Cs)n##Cs)l##Cs)k##Cs(w##Cs(v##Cs)s##Cs)z##Cs){##Cs)c##Cs(v##Cs(~##Cs)t##Cs)c##Cs)h##Cs*&##Cs*'##Cs)k##Cs)h##Cs){##Cs)v##Cs)m##Cs)p##Cs*.##Cs*/##Cs**##Cs)z##Cs)}##Cs*(##Cs*+##Cs*/##Cs*6##Cs*7##Cs*2##Cs*0##Cs*/##Cs**##Cs*)##Cs*7##Cs*>##Cs*?##Cs)\##Cs)Z##Cs*1##Cs*8##Cs)S##Cs)O##Cs*F##Cs*G##Cs)R##Cs)X##Cs*?##Cs)K##Cs)G##Cs)i##Cs*N##Cs*O##Cs*J##Cs)O##Cs)R##Cs*H##Cs*K##Cs*O##Cs*V##Cs*W##Cs*R##Cs*P##Cs*O##Cs*;##Cs*8##Cs*W##Cs*^##Cs*_##Cs)|##Cs)e##Cs*B##Cs*X##Cs)s##Cs)o##Cs*f##Cs*g##Cs)r##Cs)x##Cs*_##Cs*Z##Cs*)##Cs*-##Cs*n##Cs*o##Cs*j##Cs*^##Cs*a##Cs*h##Cs*k##Cs*o##Cs*v##Cs*w##Cs*r##Cs*p##Cs*o##Cs*j##Cs*i##Cs*w##Cs*~##Cs+###Cs*@##Cs*>##Cs*q##Cs*x##Cs*7##Cs*3##Cs+*##Cs++##Cs*6##Cs*<##Cs+###Cs*k##Cs*4##Cs*M##Cs+2##Cs+3##Cs+.##Cs*m##Cs*r##Cs+,##Cs+/##Cs+3##Cs+:##Cs+;##Cs+6##Cs+4##Cs+3##Cs*q##Cs*p##Cs+;##Cs+B##Cs+C##Cs*`##Cs*L##Cs*x##Cs+<##Cs*W##Cs*S##Cs+J##Cs+K##Cs*V##Cs*\##Cs+C##Cs+>##Cs*i##Cs*m##Cs+R##Cs+S##Cs+N##Cs+B##Cs+E##Cs+L##Cs+O##Cs+S##Cs+Z##Cs+[##Cs+V##Cs+T##Cs+S##Cs+N##Cs+M##Cs+[##Cs+b##Cs+c##Cs+K##Cs+J##Cs+U##Cs+\##Cs+K##Cs+P##Cs+j##Cs+k##Cs+S##Cs+P##Cs+c##Cs+E##Cs+B##Cs+X##Cs+r##Cs+s##Cs+n##Cs+I##Cs+L##Cs+l##Cs+o##Cs+s##Cs+z##Cs+{##Cs+v##Cs+t##Cs+s##Cs+_##Cs+\##Cs+{##Cs,&##Cs,'##Cs+k##Cs+c##Cs+f##Cs+|##Cs+k##Cs+p##Cs,.##Cs,/##Cs+s##Cs+p##Cs,'##Cs+~##Cs+u##Cs+x##Cs,6##Cs,7##Cs,2##Cs,&##Cs,)##Cs,0##Cs,3##Cs,7##Cs,>#<DS'<DS*=D$S;#<DS0<DS,=D$S<#=D&N#<DS7<DS+=D$S5#<DS)=D#S6s.p=D%S:#=D)S(#>s/&1D#'D#Ls.r(s.tGEEF#JUS]E>s/,>#1D#1Ds/-'D$L#(s.{GEEF#J)s.|GEEF*)#>S/>#7#1D#'D#Ls/$(s/&GEEF#J)s/'GEEF10#'D4Rs/'(s/)GEEF#J'D6R0(s/+GEEF#JBs/,GEEFS12s/-GEEF$#)s/.GEEF'7#'Ds/.R;(s/0GEEF#JBs/1GEEFM'D8R>(s/3GEEF#J2s/4GEEF%#)s/5GEEF'>#ZS^s/6GEEF@CDs##5:D#>'D>L#(s/:GEEF#J)s/;GEEF's#$#7s#$1D#1Ds#&'D$L#(s/@GEEF#J)s/AGEEFs#+s#*#7s##>#1D#'D#Ls/D(s/FGEEF#J)s/GGEEFs#1s#0#'Ds#4R-(s/IGEEF#JBs/JGEEFS#2s/KGEEF$#)s/LGEEFs#%s#5#Bs/MGEEFO'D3Rs#:(s/OGEEF#J2s/PGEEF%#)s/QGEEFs##s#:#CDs#>0:D#8'D8L#(s/UGEEF#J)s/VGEEFBs#?#771D#1Ds#9'D$L#(s/[GEEF#J)s/\GEEFs#Fs#E#1Ds#>'D#Ls/](s/_GEEF#J)s/`GEEFs#Js#I#'Ds#MR+(s/bGEEF#J'D-Ps/b(s/dGEEF#J2s/eGEEF%#)s/fGEEFs#?s#O#'Ds/fP1(s/hGEEF#J'D3Rs#U(s/jGEEF#J2s/kGEEF%#)s/lGEEFs#>s#U#CDs#Y2:D#8'D8L#(s/pGEEF#J)s/qGEEFs#=s#Z#'Ds/qPs#6(s/sGEEF#J1Ds#4'Ds#9P#(s/vGEEF#J2s/wGEEF&#:D&A'D#Ps#^(s/zGEEF#J:D%s#g'Ds#aR#(s/}GEEF#J2s/~GEEF&#'Ds#DLs/~(s0$GEEF#J'Ds#gLs0$(s0&GEEF#J1DS/'Ds0'P#(s0)GEEF#JVS@Ds/[:Ds#,#'D'P#(s0-GEEF#J2s0.GEEF'#CD*s#wWS_Ds#qs#P'D$L#(s02GEEF#J2s03GEEF'#2s04GEEF0#2s05GEEF3#2s06GEEF6#2s07GEEF>#1Ds0J1Ds0J'D$P#(s0;GEEF#J:D7&:D4&'D$P#(s0?GEEF#J)s0@GEEF's$)#)s0AGEEF,s$*#)s0BGEEFs#/s$+#)s0CGEEFs#5s$,#)s0DGEEFs#<s$-#)s0EGEEFs#Cs$.#)s0FGEEFs#Hs$/#)s0GGEEFs#Os$0#)s0HGEEFs#Us$1#)s0IGEEFs#[s$2#)s0JGEEFs#as$3#)s0KGEEFs#hs$4#)s0LGEEFs#os$5#)s0MGEEFs#vs$6#)s0NGEEFs#~s$7#)s0OGEEFs$*s$8#)s0PGEEFs$2s$9#l#%#s0Ms0Gl#&s$@s0S#l#'s$Os0V#j#)D#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#j#0D#j#1D#j#2D#j#3D#j#4D#j#5D#j#6D#j#7S%#j#8S%#j#9S%#j#:S%#&DS'I&DS)S'k##$#&DS7I&DQIk##$#-S0I-S)S+*#Mk##%#-IS)-S,S**O#k##%#&DS*Ik###S=9S+S#0#Q&DS*#k##&#&DS+I&DQS0k##$#&DS,I&DOIk##$#-QI-S1M*#S2k##%#-IS1-S#M*S9#k##%#&DMIk###S=9S#S$0#O&DS,#k##&#&DS#I&DS$Mk##$#k##56-S-I-S.S2%S2I*$#k##&#-IS.%IS3-S3S$*$#k##&#&DS$Ik###S=9S8M0#S9&DS.#k##&#%IO%OS-*$#0S-S.%#S$0$S8-S$#*%#&DS2I&DS3I%IQ0Ms1&%Q#*%#9QS8VSES$O&D$#*&#*+#*-#*/#*5#%MO0MS#0Os130#S-%%#k##'#k##)#k##@#k##s#'#k##s#-#k##s#3#k##s#5#k##s#9#k##s#@#k##s#E#k##s#J#k##s#N#k##s#R#k##s#Y#k##s#^#k##s#c#k##s#g#k#)D#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#k#0D#k#1D#k#2D#k#3D#k#4D#k#5D#k#6D#k#7S%#k#8S%#k#9S%#k#:S%#%IS'%S'I%IS(%S(I5S48s28s28S43s2:#WSCs2:s2:S43s2<#4S4ASI@SIUSDS4i#FS&/.-,NS7QS(S'H+)'&%S1$#S:S;S5S<S6S0S)S*S+S,MS#OS-S.S3S9l#(s$/1#l#;s0)D#l#<s0,D#l#=s02s0.#l#>s08s04#l#?s0@s0:#l#@s0Hs0B#l#As0Qs0J#l#Bs0TD#l#Cs0WD#l#Ds0]s0Y#l#Es0cs0_#l#Fs0ks0e#l#Gs0ss0m#l#Hs0|s0u#l#Is1#D#l#Js1'D#l#Ks1.s1)#l#Ls15s10#l#Ms1?s17#l#Ns1Is1A#l#Os1Us1K#l#Ps1]s1W#l#Qs1gs1`#l#Rs1rs1k#l#Ss2:s1u##s2ZNS(@#A$%$#m#'#j#Ts2[#j#$s2_#j#Us2a#YS`s2bs2]s2D#S&j#$s2b##"). Qed.

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
  ltac2:(KReplay.runc [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@kc__2); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.div_add_l); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.EnvRing.Pinj); constr:(@Stdlib.micromega.EnvRing.PX); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.ZArith.BinInt.Z.mod_small); constr:(@Stdlib.ZArith.BinInt.Z.mul_div_le); constr:(@Stdlib.ZArith.BinInt.Z.div_pos); constr:(@Stdlib.ZArith.BinInt.Z.mod_add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_base_of)|] [|@z; @Ha; @__ff; @__varmap; @__wit; @__arith; @__sat0; @__sat1; @__sat2; @__sat3; @heq_M; @heq_ps; @r0; @q0; @H3; @H2; @H1; @H0; @H; @__sat4; @__sat5; @heq_q; @heq_r; @M; @__x1; @__x2; @__x3; @H5; @H4; @__x4; @__x5; @__x6; @__x7; @__x8; @__x9; @__p1; @H10; @H15; @H14; @r2; @q2; @H13; @H12; @H11; @H9; @r1; @q1; @H8; @H7; @H6; @__sat6; @__sat7; @H16; @__sat8; @__sat9; @__x10; @__x11; @__x12; @H17; @Hdiv; @Hr; @Hzqr; @r; @q; @Hps; @HM; @ps; @Hz|] "#:5#b$a#e$&#g$'$%#{#$##$+#6#7#5#8#:#*#4#;#9#<#+#3#?#($>#,#>#H#)#G#0#-#@#I#o#'#=#l#&#2#A#%#B#E#F#J$*#.#K#L#/#C#D$U#1#P#M#O#Q#R#S#W#N#T#Y$Z$?#U#V#X#[#Z#x#b#\#j#r#v#y$.$/$=$2$7$F$Q$[#^#]$`$4#i#z#|#}#~$$$,$0$1$-$I$G$]$^#a#_$\$_$a$b$c#p#w#k#f#m#n$8#q$J$6$H$($#$L$R#t$5$W$@$9$:$;$P$A$D$O$M$E$S$K$X#s$B$C$3#u#h$T$Y$<$V$)$NT$6&$7%$8$$9%$:%$;%$<%$=%$>&$?%$@+$A'$B*$C&$D&$E%$F$$G&$H(#t%#u%$I%$J%$K%$L$$M'$N&$O%$P&#|&$Q%$R%$S%$T'$U$$V%$W&$X&$Y$$Z)$[$$\*$])#|%#A$$^%$_%#*%$`%&EJ%S7%#%#%#%#%#US]#(IS4'#S4VSm%#E,E(VS^$#*S;#(#S4'#S4#CJ#j#$C#IS7%#I#%#%#E#VS^0#'J#2C##CI$2CS4#CIS4m#$#2C5#CS86m#$#VS_:-$E;&E/$E/k##$#k##&#&E@WS`A4Ij##SZ#j#%%#&E6k##SZ#k#%(#VS_s#'s#&&Es#'$Es#'k##$#k##2#WS`s#,s#+Ij##SZ#j#%0#&Es#-k##SZ#k#%3#USnHUSoHUSpCUSqCUSrCQCE%s#=%#%#%#%#%#E#QC#.C+S@#/-GDDF#KVSs.F2SaSbVStJS;#Sa#Sbm$%#WSuCEIXSvJS;$#l#&*)#l#'87#l#(;:#$E0l#)$#Jl#*B?#l#+s#*s#&#l#,s#/s#,#l#-s#9s#4#l#.s#;s#<#l#/s#?s#@#$EIm#$#(S)S8*S.S5*QS)2C##CJ$m#$#(S&S.2C##CS;$m#$##CS.S4m#s#O##CS&s#`m#s#N#HS9S0SH&ES0*S'SH&E#k##%#@S'SHS9&ESH(RS9&E#k##%#6RS9#CS9E3#(NS''S'#*NS',$##CN#k##(#7NS'$ES'*LR&E#$$R)$#k##'#8LR$RE*MN$N#&$E)$#k##'#9MN#CNE(OL#C#Ek##%#:OL#CLE*S$M#C#S$k##%#(S$M*POQCs$5WScC#s$:.C#S*s#^/s#`GDDF#KMs#aGDDF#l#&#s#Vs#Pl#'s#es#d#l#(s#hs#g##Cs$;Ek###STl#)%#Jl#0.C#l#10C#l#262#l#3<8#l#4s#$>#l#5s#,s#&#l#6s#6s#.#l#*s#<s#8#l#+s#Bs#>#l#,s#ys#v#l#-s$%s#}#l#7s$*s$'#l#8s$4s$/#l#.s#Hs#I#l#/s#Ks#L#l#9s#Ns#O#l#:s#Ss#T##CS)E3#m#%#WSdQS)#'S)I,#J#CQ#m#&#*S&S.2C##CI$m#$#(S+Q2C##CS8$m#$##CQS4m#s$P##CS+s$am#s$O#HS'SHS9*RS9&E#k##s#\#@RS9S'&ES9&Es#Xk##$#6NS'#CS'E3#(LR'R#,#s#W#CL#k##'#7LR$ER&Es#U$s#VN)$#k##&#8MN$NE*OL$L#&$E)$#k##'#9OL#Cs#REk##s#W#:S$M#CME#Cs#UPk##$#(PO*S#S$.Cs$VS@s#W/s$XGDDF#Kl#&#s$Ms$Gl#'s$\s$[#l#(s$_s$^#l#)#s$iJl#0)C#l#1+C#l#20-#l#342#l#4<6#l#5s##>#l#6s#,s#%#l#*s#1s#.#l#+s#6s#3#l#,s$ns$k#l#-s$vs$r#l#7s${s$x#l#8s%)s%$#l#.s#<s#=#l#/s#?s#@#l#9s#Bs#C#l#:s#Gs#H#$ES.m#$#WSeS&S.#&EI$IS.)$#m#&#'QS8,#S;(JQ's%BS5(S8Q,$##C&#j#$C#'S.s%G'JS5,#S8(#Q#C#)j#;C#*S+Q2C##CS;$m#$#(S1S&2C##CS5$m#$##CS&S4m#s%R##CS1s%cm#s%Q#HRS9S'&Es$Sk##s#]#@NS'R&ES'&Es#Zk##$#6LR#CRE3#(MN'N#,#s$Q#CM#k##'#7MN$EN&Es#Y$s#ZL)$#k##&#8OL$LE$Ms$P&s$QE)$#k##&#9S$M#Cs#XEk##s#\#:PO#COE#Cs#[S#k##$#(S#S$*S%P&EL$LS#)$#'s&$O'#S#,#M'S#s&''#O,#M#C&#j##*#$MS%&EO$S$S,FCS;FCS8<C$I#US]s&4WScCs$j#ACS7=C$#ACs&N=C$#ACs&>GC$#=C&)=C#)GC#&.C&S*#/s%tGDDF#Kl#&#s%is%cl#'1s%w#l#(s%{s%z#j#<C#j#=C#j#>C#'s&EJ'#I,#S;'Is&H'#J,#S;#C&#k#<C#k#=C#k#>C#WJS#S(S%l#).$#j#?s#%#j#@s#'#V#IJj##s#*#j##s#6#5s#7s#6s#-#Rl#0s#9C#l#1s#;C#l#2s#@s#=#l#3s#Ds#B#l#4s#Ks#F#l#5s#Rs#M#l#6s#[s#T#l#*s#`s#]#l#+s#ds#b#l#,s&Bs&?#l#-s&Js&F#l#7s&Os&L#l#8s&Ys&T#l#.s#js#k#l#/s#ms#n#l#9s#ps#q#l#:s#us#v#'s&hS8'#S.,#S;'s$&S8,#S;#C%#'s$.Q,#S8(JS&'s&qS)(S5S&,$##C&#j#$C##CJ%j#$C#2Cs$6(,Q*S1S&2C##CS8$m#$#(SAS+2C##CS)$m#$##CS+S4m#s'###CSAs'4m#s&~#HNS'Rk##s$,s%y@LRN&ER&Es$)k##$#6MN3s%s'Ls%s,#s$~#CO#k##&#7OL$EL&Es%t$s%uM)$#k##&#8S$M$ME$Os%v&s%wE)$#k##&#9PO#Cs$&Ek##s$*#:S#S$#CS$E#Cs$)S%k##$#(S%P*S6S#&EM)#s#~#CS%E3#j##%#$OS6&ES$$PS(FCI.Cs'-S@s#~/s'/GDDF#KUSwD.Cs$%S*s'0/s'2GDDF#KMs'3GDDF#-s'4GDDF'&#l#&#s')s'#l#'+s'7#l#(s';s':#j#<C#$EJ#CIEk###STk##%#k#<C#RS2S,l#))$#j#?6#j#@8#V#IJj##;#j##A#5Bs$A>#Nl#0s#$C#l#1s#&C#l#2s#+s#(#l#3s#/s#-#l#4s#6s#1#l#5s#=s#8#l#6s#Ds#?#l#*s#Is#F#l#+s#Ls#K#l#,s'Ws'T#l#-s'_s'[#l#7s'ds'a#l#8s'ns'i#l#.s#Rs#S#l#/s#Us#V#l#9s#Xs#Y#l#:s#]s#^#XSxs%=QS8#JCs%<s#es#ds#c#'Qs(#'#S5,#S8ZSfCs#qs#k&#Jl#6s#zs#t#JCs%?s%:#QS)JCs%Gs%A#S+I(S+S.(S;S.,s#~##C%#'JS&*#S+'s#xS&#C$#j#$C#@NS9R(LS'&E#k##s&8#HLRNk##s#is&-NS0R&EN(S9L&E#k##%#k##s'E#@OLM&Es&yk##s$~#6S9L3s'$(S'M'M#*S'M,$##CS'#k##(#7S'M$EM*RO&E#$$O)$#k##'#8RO$OE*NS$$S$#&$E)$#k##'#9NS$(LP#C#Ek##s#s#:LP#CPE*MS##C#Mk##%#(MS#*OS%6S2S,#CS,E3#(S:S('S(#*S:S(,$##CS:#k##(#7S:S($ES(*S<S2&E#$$S2)$#k##'#8S<S2$S2E*SES:$S:#&$E)$#k##'#9SES:#CS:E(SFS<#C#Ek##%#:SFS<#CS<E*S=SE#C#S=k##%#(S=SE*S>SF6S/SF#CSFE3#(S-S='S=#*S-S=,$##CS-#k##(#7S-S=$ES=*S3S>&E#$$S>)$#k##'#8S3S>$S>E*S?S/$S/#&$E)$#k##'#9S?S/#CS/E(SBS-#C#Ek##%#:SBS-#CS-E*SCS3#C#SCk##%#(SCS3*SJS?&ES/$S/SC)$#'S'SC'S3SJ,$#'s)SS3,#S''#SC#C&#j##*#$S-SJ&ES3$S?SKUS6I&ESKk###s$pOSP&ES)$S)SI)$#US%SK$MSL)s$w#&EQ$QSM)$#'PSN'SISQ,$#'s)kSI,#P'#SN#C&#j##*#$S&SN&ES+$S1SU&ES%$S%SV)$#'S,SO'SQSW,$#'s)ySQ,#S,'#SO#C&#j##*#$S6SO&ES,$S(SR%s)T%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#E#SC#;Sg;#;#;#;#;#;#;#;#;#>C#?C.#>C&?C0#K3BC#>C,1C$#0C'#0C*#C#SGKS7BC#BCEDC$S7#4Cs+$#1C#,BC?DC#S7'4Cs+(#>C;1C$#Is+*%s#&%#%#%#%#%#%#%#%#%#%#%#K#BC#DC6S7#4C2#>Cs#/1C$#>CSg0C$#0C8#0C>#E-SC#?C#(BCs*[DCs#'S7#4C>#;s#6;#>C#1C&#Is+:4C#)DC#S7s#.4Cs+O#>Cs#@1C$#%=%#%#%#%#%#%#%#%#%#%#%#E#BC#DCs#)S7#4Cs#8#1C#s#;1C>s#)>Cs#X1C@#0C%#0C'#0C9#0C@#0Cs#(#C#SGPs#-#ES7BC#DC#S7s#O4Cs+p#1C#s#XDCs#ZS7s#R4Cs+s#1C#s#MBCs#5DCs#^S7#4Cs#N#1C#s#>0C#s#=0C(#0C,#Ks+7BC#DC2S7#4Cs#V#1C#s#84Cs#7%DC#S7s#b4Cs,'#1C#s#6Ks#*BC#DC4S7#4Cs#_#1C#s#b1C-s#P1C.s#)0C$#0C&#0C,#0C1#0Cs#N#C#SGP9#?Cs$/s#W4Cs,6s#'1C#s#G4Cs,8s#&1C#s#~4Cs,:s#w>Cs$31C$#0C&#0C)#0C,#C#SGPs#`#1C*s#R4Cs,Cs#|1C#s$-1C1,0C$#0C'#0C5#C#SGPs#/#1Cs#ps$:0C#s#kC#SG1Cs#7s$=0C#s#4C#SG+H#s+u+H'#+H+#+H5#+Hs$:#+Hs$;#+Hs#%#+Hs#L#+Hs#M#+Hs#(#+Hs$@#+Hs$A#+Hs#+#+Hs#R#+Hs$D#+Hs$E#+Hs$F#+Hs$G#FCQ<C#S5s,*FCS+<C#S.s,,<C%S;#FCS&<C#S)s,/<C#S8s,0<C&I#ACs,m.C#S*s,0/s,2GDDF#KACs,oIs,rAC#.C%S*#/s,7GDDF#K-s,8GDDF(s'f#ACs$N.C#S*s,9/s,;GDDF#K-s,<GDDF,s'j#.C/S@s,</s,>GDDF#K.C1S@./s,@GDDF#K.C0SSs,@/s,BGDDF#KLs,CGDDF%#-s,DGDDF(s'r#.Cs,DS@7/s,FGDDF#KZShs,GGDDFSA.C7S@:/s,IGDDF#KLs,JGDDF%#-s,KGDDF's'y#.C>S*s+L/s,MGDDF#K%<AC#.Cs)BS*#/s,QGDDF#K.Cs)BS*;/s,SGDDF#KACs-#.C#S*s#$/s,VGDDF#K=Cs#)s)GGC#&.Cs#&S*#/s,ZGDDF#K.Cs,ZS@s)M/s,\GDDF#K.Cs#/S*s)K/s,^GDDF#K=Cs)Ss)Q=Cs)Ps#2GC$#=Cs)Ws)RGC#s)W=C#s)V.C&S*#/s,fGDDF#K-s,gGDDF+s(9#-s,hGDDF.s(:#-s,iGDDF1s(;#-s,jGDDF6s(<#-s,kGDDF:s(=#-s,lGDDF=s(>#-s,mGDDFBs(?#-s,nGDDFs#%s(@#-s,oGDDFs#-s(A#-s,pGDDFs#6s(B#-s,qGDDFs#;s(C#l#&#s,fs,`l#'s#Fs,t#l#(s#Ps,w#j#<C#j#=C#j#>C#j#AC#j#BC#j#CC#j#DC#j#EC#j#FC#j#GS[##CS8E#CQS)k##$##CS5E#CS+Ek##$#$S)E$S.S+&S+E)$#k##&#$S1Q)S0#k##s*|##CQs-c#CS.S0#CS&S0#CSDS0'SAS1,#S0#CSD#$ES1'SAs-_#CS0#'SASD'S0SH,$#'s-dS0,#SA'#SD#C&#k##*#k##-#k##/#k##3#k##5#k##7#k##9#k##;#k##?#k##s#%#k##s#)#k#<C#k#=C#k#>C#k#AC#k#BC#k#CC#k#DC#k#EC#k#FC#k#GS[#&EPi#8J#S4S#PSOSiS\SWSXS<S%S6S,S(SISLSMSNSVSRSYl#)s#9%#j#2s&^#j#5s&`#V#IJj##s&c#j##s&o#5s&ps&os&f#S5j#3s&r#j#4s&t#V#IJj##s&w#j##s''#5s'(s''s&z#Il#5s',s'*#l#Hs'1s'.#l#+s'5s'3#j#Is'7#j#Js'9#V#IJj##s'<#j##s'H#5s'Is'Hs'?#S=l#Ks'KC#l#Ls'MC#l#Ms'Ss'O#l#Ns'Ys'U#l#Os'as'[#l#Hs'is'c#l#Ps'ss'k#l#Qs'uC#l#Rs'wC#l#Ss'}s'y#l#Ts('s(##l#Us(/s()#l#?s(7s(1#l#@s(As(9#l#0s(CC#l#1s(EC#l#2s(Ks(G#l#3s(Ps(M#l#4s(Xs(R#l#5s(`s(Z#l#6s(is(b#l#*s(ms(k#l#+s(ts(o#l#,s(ws(v#l#-s(|s(y#l#7s.4s.1#l#8s.<s.8#l#Vs.As.>#l#Ws.Ks.F#l#.s*/s*0#l#/s*2s*3#l#9s*5s*6#l#:s*:s*;#'s+uQ'S5S&,$#'s+wQ#C$#'S)S+,s)2#*JS1(S)S+'#S+#C%#j#$C#*s)8S+#CJ&j#$C#WSyS5S&S.'S&s*V&#S5*SDS12C##CS)$m#$#(S0SA2C##CQ$m#$##CSAS4m#s.q##CS0s/&m#s.p#@MRL(ON&E#k##s*P#HOLMk##s+^s*GNS9L(RO&E#k##s*8#k##s-(#@POS$&Es+gk##s+Z#6S#S$3s*C'Ps*A,#s+k#CS%#k##&#7S%P$EP&Es*F$s*GS#)$#k##&#8S6S#$S#E*S,S%$S%#&$E)$#k##'#9S,S%(S(S6#C#Ek##s*Q#:S(S6#CS6E*S2S,#C#S2k##%#(S2S,6S#S(#CS(E3#(S%S2'S2#*S%S2,$##CS%#k##(#7S%S2$ES2*S6S:&E#$$S:)$#k##'#8S6S:$S:E*S,S<$S<#&$E)$#k##'#9S,S<(S(SE#C#Ek##s)?#:S(SE#CSEE*S2SF#C#S2k##%#(S2SF*S:S=6S3S>#CS>E3#(S?S/'S/#,#s)4#CS?#k##'#7S?S/$ES/*SBS-&E#$$S-)$#k##'#8SBS-$S-E$S3s)4&s)5E)$#k##&#9SCS3#CS3E(SJS?#C#Ek##%#:SJS?#CS?E*SPSB#C#SPk##%#(SPSB*SKSC$S3SP)s)4#&ES?j##$#&ESB$SCSL&ESLk###s/<OSI$S)SM)s)7#UNSL$S0SN)s/B#$QSQ)s)6#j###,$S&SU$S1SO$NSW)s*f#&ESUj##$#$LSR$OSX.Cs/|SSs,q/s/~GDDF#K-s0#GDDF#s+Q#l#&#s/ts/nl#'s+Vs0&#l#(s0*s0)#j#<C#k##s0gs-qk#<C#RSRS0l#)&$#j#P.#j#Us+f#V#IJj##2#j##s*z#5s*{85#S5j#S:#j#Ts)F#V#IJj##>#j##s)U#5s)Vs##A#Il#Us#'s#%#l#Os#+s#)#l#-s)cs#-#j#Xs#0#j#Is#2#V#IJj##s)h#j##s)j#5s)ks#:s#7#S/l#Ks#<C#l#Ls#>C#l#Js#Ds#@#l#Ms#Js#F#l#Ns#Qs#L#l#Os#Ys#S#l#Hs#bs#[#l#Qs#dC#l#Rs#fC#l#Ps#ls#h#l#Ss#qs#n#l#Ts#ys#s#l#Us$%s#{#l#?s$/s$'#l#0s*kC#l#1s$2C#l#@s$8s$4#l#2s$=s$:#l#3s$Es$?#l#5s$Ls$G#l#6s$Ss$N#l#,s$Ws$U#l#-s$]s$Y#l#7s$`s$_#l#8s$es$b#l#Vs0bs0_#l#Ws0js0f#l#Ys0os0l#l#Zs0ys0t#l#.s$ks$l#l#/s$ns$o#l#9s$qs$r#l#:s$vs$w#$ESPj##s#\#$ESUj##s#P#$ESRj##s#M#-s0hGDDFs,;s,:s,;l#&#s0]s0Wl#'s,?s0k#l#(s0os0n#j#<C#k##s,6s0Ok#<C#RSjSXl#)&$#j#Ps#S#j#Us,O#V#IJj##s#W#j##s+c#5s+ds#]1#S5j#Ss#_#j#Ts*/#V#IJj##s#c#j##s*>#5s*?s#h9#Il#Us#ls#j#l#Os#ps#n#l#-s*Ls#r#j#Xs#u#j#Is#w#V#IJj##s*Q#j##s*S#5s*Ts$#s#$#S/l#Ks$%C#l#Ls$'C#l#Js$-s$)#l#Ms$3s$/#l#Ns$:s$5#l#Os$Bs$<#l#Hs$Ks$D#l#Qs$MC#l#Rs$OC#l#Ps$Us$Q#l#Ss$Zs$W#l#Ts$bs$\#l#Us$js$d#l#?s$ts$l#l#0s+TC#l#1s$wC#l#@s$}s$y#l#2s%&s%##l#3s%.s%(#l#5s%5s%0#l#6s%<s%7#l#,s%@s%>#l#-s%Fs%B#l#7s%Is%H#l#8s%Ns%K#l#Vs1Ks1H#l#Ws1Ss1O#l#Ys1Xs1U#l#Zs1bs1]#l#.s%Ts%U#l#/s%Ws%X#l#9s%Zs%[#l#:s%_s%`#XSzS)S+s#H#&Es%n*S0SA2C##CS.$m#$#(SHSD2C##CS&$m#$##CSDS4m#s1x##CSHs2-m#s1w#@ONM(S$L&E#k##s,J#HS$MO&Es0`k##s-<#NS'M(NS$&E#k##s.^#k##s//#@S#S$P&Es-Ek##s->#6NS$'Ps,8*LP,$##CL#k##s%j#7LP&Es,9$s,:S#)$#k##s%i#8MS#$S%s,:&s,;E)$#k##s%h#9OS%(S$S6#C#Ek##s-V#:S$S6*PS,#C#Pk##s%e#(PS,*S#S(6SES:3s,0'S<s,0*SFS<,$##CSF#k##'#7SFS<$ES<&Es,2$s,3SE)$#k##&#8S=SE$SEE$SFs,4&s,5E)$#k##&#9S>SF(S/S=#C#Ek##s,9#:S/S=#CS=E*S-S>#C#S-k##%#(S-S>*S3S/6S?S/3s,+'S-s,+,#s%X#CSB#k##&#7SBS-$ES-&Es,,$s,-S3)$#k##&#8SCS3$S3E$S?s,.&s,/E)$#k##&#9SJS?#Cs%SEk##s%X#:SPSB#CSBE#Cs%VSKk##$#(SKSC*SISJ)s%Ws,-'S'SK&E#$$SI)$#j##'#$SBSI&ESC$SJSM&ESMk###s.FOSL$S)SN)s,5#US%SM$MSQ)s.L#$QSU)s,4#'PSV&E#$$SO)$#j##'#$S&SV$S1SW$S%SR)s,/#'S,SY&E#$$SX)$#j##'#$S6SY$S(S\%s*e%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#E#SC#;s+G>C#?C%#?C&s+~K)BC#1C#s,#?C*s+3?C+s+Z0C$#0C&#0C*#0C,#C#SG?Cs+Ns*a?C2#?C3s+P0C#+0C%#C#SG1Cs,'s,-0Cs+[#C#SG;9;#>C#?Cs,D#>C&?Cs,F#0C#s,50C&#C#SG0CA.C#SG+H.s3v+H/#+H'#+H(#+H)#+H*#+H4#+H5#+H9#+H@#+H8#+H9#+H1#+H2#+H1#+H@#+H>#+H?#+H@#+HA#+Hs#%#+Hs#,#+H;#+H<#+Hs#&#+Hs#'#+Hs#+#+Hs#2#+Hs#-#+Hs#4#FCSD<Cs*gS5#FCS1<C#S.s49<C%S;#<Cs*nS)s4;FCSA<C#Qs4=<C%S8#<C'I#%s4iAC#.Cs4?SS#/s4AGDDF#K.Cs14S*s4A/s4CGDDF#KMs4DGDDF#ACs,9=Cs18#GC#*.Cs*vS*#/s4IGDDF#K-s4JGDDF(s/x#.Cs1;S*s4J/s4LGDDF#K.Cs*xS*s*{/s4NGDDF#K-s4OGDDF%s/}#-s4PGDDF&s/~s*s.Cs1AS@s4P/s4RGDDF#K.Cs1CS@s*~/s4TGDDF#KLs4UGDDF#s*q-s4VGDDF&s0(#.Cs4VS@s1G/s4XGDDF#KZShs4YGDDFSH.Cs+)S@s1J/s4[GDDF#KLs4\GDDF%#-s4]GDDF's0/#Ms4^GDDF4=Cs1Os+(GC#s+/.Cs+3S*#/s4bGDDF#K-s4cGDDF's05#Is+2AC#.C#S@s1X/s4gGDDF#K.Cs4gSS%/s4iGDDF#K=Cs1\s1^GC#(.Cs*vS*#/s4mGDDF#K-s4nGDDFs#,s0@#.Cs4nSSs1a/s4pGDDF#K-s4qGDDF#s0Cs'Q.Cs1bS*s3r/s4sGDDF#K.Cs+AS*s+=/s4uGDDF#K=Cs1ks+CGC#s1k.Cs#5S*#/s4yGDDF#K.Cs1jS*s1h/s4{GDDF#K.Cs4{SSs*{/s4}GDDF#K.Cs*}S@s1n/s5#GDDF#KLs5$GDDF%#-s5%GDDF(s0S#-s5&GDDFs+(s0T#-s5'GDDF,s0U#-s5(GDDFs+0s0V#-s5)GDDF2s0W#-s5*GDDFs+7s0X#-s5+GDDF6s0Y#-s5,GDDF9s0Z#-s5-GDDF=s0[#-s5.GDDFs##s0\#-s5/GDDFs#&s0]#-s50GDDFs#+s0^#-s51GDDFs#2s0_#-s52GDDFs#:s0`#-s53GDDFs#As0a#-s54GDDFs#Cs0b#-s55GDDFs#Is0c#-s56GDDFs#Ss0d#l#&#s5+s5%l#'s#Ys59#l#(s#ds5<#j#<C#j#=C#j#>C#j#AC#j#BC#j#CC#j#DC#j#EC#j#FC#j#[C#j#\C#j#]C#j#GS[#&ESA#CS;Ek###ST'S8S&,#S0#CS)#k##&##CS1S.k##s++##CSDEk##s46#$S.E$QSD&SDE)$#k##&#$EQ$S0S&)N#k##%##CS&Ek###ST'S+S9,#SH#CS1#k##&#$RS&#CS1Ek###ST,s+1M#CS9#k##%#k##BB#CS0O#CRO#CLO's65L,#S9#CO#'Ns68#CL#'NL&E#$$M)$#k##'#k##s45#k##+#k##/#k##1#k##3#k##s*,#k##6#k##8#k##s0k#k##?#k##A#k##s#(#k##s#-#k##s#3#k##s#6#k##s#9#k##s#@#k#<C#k#=C#k#>C#k#AC#k#BC#k#CC#k#DC#k#EC#k#FC#k#[C#k#\C#k#]C#k#GS[#i#BJs+>S'S:S4S#PRSYSXS{S|SiS<S.S$S%S6S,S(S2IS;S/SASISLSMSNSOS\Sjl#)s#P$#j#?s%r#j#3s/?#V#IJj##s%v#j##s/N#5s/Os&#s%y#S5j#@s&%#j#2s/S#V#IJj##s&)#j##s/b#5s/cs&2s&,#Il#3s&6s&4#l#Ns&:s&8#l#-s/ps&<#j#^s&?#j#Xs&A#V#IJj##s&D#j##s)D#5s)Es/ws&G#S-l#Ks&NC#l#Ls&PC#l#Is&Us&R#l#Js&Ys&W#l#Ms&`s&[#l#Ns&gs&b#l#Os&ns&i#l#Qs&pC#l#Rs&rC#l#Hs&xs&t#l#Ps&}s&z#l#Ss'(s'##l#Ts'/s'*#l#Us'7s'1#l#0s'9C#l#1s';C#l#?s'@s'=#l#@s'Es'B#l#2s'Ks'G#l#3s'Qs'M#l#5s'Xs'S#l#,s'\s'Z#l#-s'bs'^#l#7s'fs'd#l#8s'ks'h#l#Vs6os6l#l#Ws6ws6s#l#Ys6|s6y#l#Zs7*s7%#l#.s'qs'r#l#/s'ts'u#l#9s'ws'x#l#:s'|s'}#l#6s(&s(%#l#4s+/s+-#WS}s1iS+#*s+:S+*SAS+2C##CS5$m#$#(SDS12C##CS.$m#$##CS1S4m#s7B##CSDs7Sm#s7A#@LS'N(MR&E#k##s4M#HMNLk##s1rs4BNSHN&Es1jk##s42#k##s6T#@S$MO&Es57k##s2h#6PO3s4='S$s4;,#s5;#CS##k##&#7S#S$$ES$&Es4@$s4AP)$#k##&#8S%P$PE$S#s2x&s2yE)$#k##&#9S6S##CS#E(S,S%#C#Ek##%#:S,S%*S(S6#C#S(k##s3%#6PS,(S#S('S(#,#s(+#CS##k##s1o#7S#S(&Es+.$s+/S2)$#k##s1l#8S%S2$S:s+-&s+.E)$#k##s1j#9S6S:(S,S<#C#Ek##s1g#:S,S<*S(SE#C#S(k##s1f#6S-S=3s(((S3S>'S>#,#s1Z#CS3#k##'#7S3S>$ES>&Es1X$s1YS/)$#k##&#8S?S/$S/E$S-s+'&s+(E)$#k##&#9SBS-#Cs1TEk##s1Y#:SCS3#Cs1VSJk##s+$#&ES-)#s1M3s6wj##$#&ESIk###s7ROSK$S)SL)s1M#UNSI$S0SM)s7X#$QSN)s1L#j###.$S&SQ$S1SV$NSO)s2|#j###3$LSW$OSYj#S#s7-j#?s3p#V#IJj##'#j##s3(#5s3),*#S5j#T.#j#Us1P#V#IJj##2#j##s1_#5s1`75#Il#?;9#l#H?=#l#+s1mA#j#Is(>#j#Js+>#V#IJj##s+B#j##s#+#5s#,s1vs#)#S>l#Ks+JC#l#Ls+PC#l#Ms#2s#0#l#Ns#6s#4#l#Os#=s#8#l#Hs#Ds#?#l#Ps#Ls#F#l#Qs+rC#l#Rs+xC#l#Ss#Ss#P#l#Ts#Xs#U#l#Us#^s#Z#l#?s#ds#`#l#@s#ks#f#l#0s,>C#l#1s,DC#l#2s#rs#o#l#3s#xs#t#l#4s$#s#z#l#5s$*s$%#l#6s$1s$,#l#*s$5s$3#l#+s$:s$7#l#,s$=s$<#l#-s$Bs$?#l#7s8ls8i#l#8s8ts8p#l#Vs8ys8v#l#Ws9's8~#l#.s$Hs$I#l#/s$Ks$L#l#9s$Ns$O#l#:s$Ss$T#3s.Gm#$#XS~s3fS)S+#JCs-1s-/s$\s$[#'s5%S&ZSfCs-9s-4$#Jl#6s-As-<#(S1QJCs6Xs3j$#Jl#_s3ts3p#l#`s6`s6a#l#as7Us7V#l#bs8WC#l#cs8YC#l#ds8[s8\#l#es9Cs9B#l#fS4C#l#;s9SC#*Is9T(#S4'#S4#Cs9Z#m#'#VT#s9_s9]VSks9`#VT$s9as9_JCs9_s9W&$#UT%IVSks9d##C#+m#&#j#gs9n#j#$C##"). Qed.

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
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.

(* [comment removed for export] *)
Lemma window_page_in_all_pages : forall S (x : word) (p : word),
  in_rangesb x S = true ->
  bv_unsigned p = ((bv_unsigned x / page_size) * page_size)%Z ->
  In p (all_pages S).
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.all_pages); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Datatypes.cons); (KReplay.sort_at constr:(@Stdlib.Lists.List.hd_error_nil) [0]); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.in_app_iff); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_pages); constr:(@Corelib.Init.Datatypes.orb); constr:(@Stdlib.Bool.Bool.orb_true_iff); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.zin_rangeb); constr:(@Stdlib.Lists.List.existsb); constr:(@kc__3); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_bounds); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_lo); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_hi); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_npagesZ); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Stdlib.ZArith.BinInt.Z.div_le_mono); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.ZArith.BinInt.Z.eq_decidable); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.div_add); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); (KReplay.sort_at constr:(@Stdlib.Lists.List.count_occ_map) [0]); (KReplay.sort_at constr:(@Stdlib.Lists.List.count_occ_map) [1; 0]); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Init.Logic.ex); constr:(@Stdlib.Lists.List.in_map_iff); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_page); constr:(@Corelib.Lists.ListDef.seq); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_npages); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Numbers.BinNums.N); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@stdpp.bitvector.definitions.bv_wrap_small); constr:(@Stdlib.ZArith.Znat.Z2Nat.id); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Nat.add); constr:(@Stdlib.Lists.List.in_seq); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.ZArith.BinInt.Z.div_mul); constr:(@Corelib.Init.Logic.or_intror)|] [|@p; @x; @S; @b; @e; @H; @Hp; @Hin; @a; @l'; @l; @A; @b2; @b1; @C6; @C5; @C4; @C3; @C2; @C1; @m; @n; @__ff; @__varmap; @__wit; @__arith; @H39; @H38; @__sat13; @H37; @H36; @r5; @q5; @H35; @H34; @H33; @H32; @H31; @r4; @q4; @H30; @H29; @H28; @H27; @H26; @r3; @q3; @H25; @H24; @H23; @H22; @H21; @r2; @q2; @H20; @H19; @H18; @H17; @H16; @r1; @q1; @H15; @H14; @H13; @H12; @H11; @r0; @q0; @H10; @H9; @H8; @H7; @H6; @r; @q; @H5; @H4; @H3; @H0; @__sat7; @__sat8; @__sat9; @__sat10; @__sat11; @__sat12; @heq_ux; @heq_lo; @heq_sz; @__x1; @__x2; @z; @__x3; @y; @f; @B; @start; @len; @__x4; @__x5; @__p1; @__p2; @__p3; @z5; @z4; @Hhi; @Hlo; @sz; @lo; @ux; @Hx; @H2; @H1; @IH|] "#GY#m%N$##{$=###$#%$c#&#x#z$d$b#'#(#)%$#*$h#+#8#<#,#7#;%'#.#4#:#/#0#>#G#M#-#6#H#L#O#E#3#?#D#2#=#C#F#I#K$]#J#5#9#B#P%/$7#1#N$q#m#@#U#V#Q#S#A#R#T#[#a$v#e%4#u#c$m$p%&%G%D%H%M#`#b$\$g$n$s%0#y$)$0$5$8$F$J$f#h#g#\$}%%#Z#f%*%N$&$.$P#^#l$R#d#]$x#i$~$|${%(%,%.#W#X#Y%=%>%;$<$@%5$C%C%I%L#s#q$*$($+$,$3$6$;$K$N$O$Q$^$_$a$i$k$l$j$r$u$t#j%#%-#_%1%2%3%7%<%@%A%B%?%:%K%J%8%O%+%)$H$:%P$9#v#w$2#~$D#}$G#|$>$B$$$I$V$X$Y$Z$[$/$A$E$S$T$e$`$1$?#t$4%E$-$U%6$M$o$y#r$%$L$W$w$z%9%F#p$'U$~&$G%$H%%#%%$%%%%%&%%'%$J%%(%%)$%*$%+&%,'%-%%.%%/%%0%%1%%2(%3&%4$%5%%6%%7'%8*%9%%:&%;$%<$%=&%>&%?%$/$#&&%@%$I%%A%%B+%C&%D$%E$%F%%G$%H&%I&%J%%K%%L$%M)?S\?#?#?#?#?#UT>#K#VT?##S#VSlGH#K#L,(G,)H'#C)#C#D&#LO/-H#k##%#k##+#k#$0#k#%1#j#&0#US}2VSlG##K#LnK#$#'SNF#%#Sm#T@j#(K#TKTA#TBLGL(/:J#VTC#Fl#)&Sm#j#*4#j#++#j#$?#j#%@#B@OJVSlG##K#LSFSGWSnJHG/JF#/OGJ/OGH=$#k##&#/JFH/JFG=$#WSnOJH/OG#k##%#&)#WSnPOJ/PH#k##-#j##&#j##$Fj##/#XTDJHGF61+&$#j#,H#j#-9#j#.;#j#/S~#k#,H0k#-=#k#.?#k#/S~#@S#LQVSoGF#K#L#KHL#KGL=$#k##&##KFL=&#VSoHG#K#Lk##%#&(##KJL=#-k##'#j##&#VSoJH#K#Lk##0#j###Gj##1#VTEGF63.)$#j#0K#j#1K#k#0K6k#1K#,s#aPVSJ#S%USJ$WSps#b#S#E%#J#K&L#K%L=$#,s#iQVSJ#S(#K#LUSJ%WSps#k#S%#K#L=&#@S4/s#pQ#LS(/s#rQ#=%#j##(#,s#vS#VSJ#S4#K#L@S,/s#yS##LS4/s#{S##UTFS,-S,$E#>s$#s$#S,,s$%#$&#&&#7s$'s$'S,,s$)#%'#.S,$$#%%C+%#&%#(0C#D#E()C#D#E8S,$E#'/CUSqs$=%$#$'#&'#))C*3<#D$#&&#&.#&1#&4#&=#-S/$E#>s$Ds$DS/,s$F#$&#&&#7s$Hs$HS/,s$J#%'#.S/$$#%%C+%#&%#(0C#D#E()C#D#E8S/$E#'/C%#s##$&#&&#)(C*2;#D$#&&#&-#&0#&3#&<#@S0/s$cS(#j##%#>s$es$eS0,s$g#7s$gs$gS0,s$i#%%#.S0$$#%%C+%#&%#-S0(#C#D#E(*C#D#E8S0$E#'0C%#s#C$&#&&#)(C*3.#D$#&&#&-#&0#&4#-SK$E#>s%'s%'SK,s%)#$&#&&#>s%+s%+S=,s%-#7s%-s%-S=,s%/#%%#.S=$$#%%C+%#&%#-S=(#C#D#E(*C#D#E8S=$E#'0C%#s#e$&#&&#)(C*3.#D$#&&#&-#&0#&4#>s%Gs%GS:,s%I#7s%Is%IS:,s%K#%%#.S:$$#%%C+%#&%#-S:(#C#D#E(*C#D#E8S:$E#'0C%#s$%$&#&&#)(C*3.#D$#&&#&-#&0#&4#@S-/s%dS0#j##%#-S-(#C#D#E.S-(#C#D#E8S-$E#7s%ns%nS-,s%p#'#C%#s$=$(#&(#)*C*.1#D$#&&#&/#&3#>s%zs%zSE,s%|#7s%|s%|SE,s%~#%%#.SE$$#%%C+%#&%#-S5(#C#D#E.S5(#C#D#E8S5$E#7s&0s&0S5,s&2#'#C%#s$[$(#&(#)*C*.1#D$#&&#&/#&3#-S)(#C#D#E.S)(#C#D#E8S)$E#7s&Ds&DS),s&F#'#C%#s$o$(#&(#)*C*.1#D$#&&#&/#&3#@S&/s&QS-#j##%#.S&(#C#D#E8S&$E#7s&Xs&XS&,s&Z#'#C%#s%'$(#&(#)*C-S&*/##D%#&'#&0#-SF(#C#D#E.S.(#C#D#E8S.$E#7s&ls&lS.,s&n#'#C%#s%;$(#&(#)*C-S.*/##D%#&'#&0#.S*(#C#D#E8S*$E#7s&}s&}S*,s'##'#C%#s%L$(#&(#)*C-S**/##D%#&'#&0#@S'/s'.S&#j##%#8S'$E#7s'2s'2S',s'4#'#C%#s%]$(#&(#)*C.S'-S'*$##D&#&(#.S>(#C#D#E8S1$E#7s'Cs'CS1,s'E#'#C%#s%n$(#&(#)*C.S1-S1*$##D&#&(#8S;$E#7s'Qs'QS;,s'S#'#C%#s%|$(#&(#)*C.S;-S;*$##D&#&(#@SO/s'^S'#j##%#8SO)#C.SO-SO*$##D&#8ST$E#7s'hs'hST,s'j#'#C%#s&7$(#&(#8SG)#C.SG-SG*$##D&#,s'uSTVSJ#F#K#L-G$E#>s'ys'yG,s'{#$&#&&#>s'}s'}H,s(##7s(#s(#H,s(%#%%#.H$$#%%C+%#&%#-J(#C#D#E.O(#C#D#E8P$E#7s(3s(3P,s(5#'#C%#s&^$(#&(#8Q)#C.Q-Q*$##D&#/s(?S2s'Zk#2$#k#3+#k#44#k#58#k#6<#k#7s#'#k#+s#.#j#$s(F#,s(IS<0s(Is(IGFVSJ$##K#L0s(Ls(LHG-#$E#>s(Os(O%,s(Q#$&#&&#0s(Ss(SJH>s(Ts(T#,s(V#7s(Vs(V%,s(X#%%#.($$#%%C+%#&%#0s(^s(^OJ-#(#C#D#E0s(bs(bPO.#(#C#D#E0s(fs(fQP8#$E#7s(is(i%,s(k#'#C%#s'8$(#&(#0s(os(oS#Q8#)#C.%-&*$##D&#VSrGF#K#L&s(3s(2k##$#&s(4s(1VSrHG#K#Lk##%#&'#&s(0s(:k##&#j##%#VSrJH#K#Lk##.#j###Gj##/#VTGGF61-)$#j#0K#j#1K#k#0K4k#1K#,s)2S(,s)3S7M$#,s)5S%%&#H&#E&#S##K'L#K%L&$#,s)<S4,s)=S3M$##K#L%&0H&##K#L&&#0s)Cs)CS,S4@#/s)ES3#j##&#,s)HSL,s)IS,%#0H%##K#L,s)MS/,s)NS8M$##K#L,s)QSH,s)RS0%#(H%##K#LMGF#K#L$HGk##$#$GFMHG#K#Lk##%#&'#$JHk##&#j##%#MJH#K#Lk##.#j###Gj##/#VTHGF61-)$#j#8D#j#9D#k#8D4k#9D#,s)mS=,s)nSUE$#H$%$HGF#K#L+HGk##$#+GFHHG#K#Lk##%#&'#+JHk##&#j##%#HJH#K#Lk##.#j###Gj##/#VTIGF61-)$#j#8D#j#9D#k#8D4k#9D#,s*,SV,s*-S-,s*.S:%$#E&#J+'$VT#s*2SP,s*3SP$E#UTJs*5+%#&%#,s*8SQ,s*9S),s*:S&9D##DF$m#$#,s*>S.9D##DH$m#$#,s*BSW9D##DO$m#$#:PC$EP$EC'S#C$E#k##%#k##'#%PO%#CUSqS\*$#:#C$E$%S#Q%#C*#('#C$E#k##2#k##)#)&CC#C$E$%S(S%%#C*#2'#C)#C(#C$E#k##>#k##+#:S%C$ES%'S4C$E#k##s#$#k##&#'S(C)#CC#C$E$'S,C)#C(#C$E#k##s#.#k##(#0s*us*uSGST.#-$*$#:#C$E$0s*{s*{S<S?.#-$*$#'#C$E#k##s#<#k##*#0s+'s+'S?SG.#-$*$#1#C#DCEN#)C-(/C%$##D1#k##'#23C+EC0s+5s+5S9S<.#-$*$#(#C$E#+$C&$#k##+#3(C+CE0s+@s+@S@S9.#-$*$#(#C+C#$$E&$#k##+#4(C0s+Js+JS2S@.#-$*$#'#C#D#Ek##s#&#5&C0s+Rs+RS6S2.#-$*$#(#C#D#$k##s#.#'&C0s+Zs+ZSAS6.#-$*$#(#C1SEC'S5C)C#(S5C%$##DS5#k##s#:#2S5C(S)C$E#+$C&$#k##s#9#3S)C(S&C+C#$$E&$#k##s#4#4S&C'SFC#D#Ek##s#K#5SFC(S.C#D#S.k##s#O#'S.C(S*C%S'S*%#C*#s$21#C%S>S'%#C*#s$6'#C)C#(%C%$##D'#k##s#]#2)C%S1S>%#C*#s$@(#C$E#+$C&$#k##s#_#3(C%S;S1%#C*#s$I(#C+C#$$E&$#k##s#]#4(C%SOS;%#C*#s$R'#C#D#Ek##s#w#5&C%STSO%#C*#s$Y(#C#D#$k##s#~#'&C%SGST%#C*#s$`(#C1SGC'S?C)C#(S?C%$##DS?#k##s$-#2S?C(S<C$E#+$C&$#k##s$,#3S<C(S9C+C#$$E&$#k##s$'#4S9C'S@C#D#Ek##s$>#5S@C(S2C#D#S2k##s$B#'S2C(S6C1SBC'S7C)C#(S7C%$##DS7#k##s$J#2S7C(S3C$E#+$C&$#k##s$I#3S3C(SLC+C#$$E&$#k##s$D#4SLC'S8C#D#Ek##s$[#5S8C(SHC#D#SHk##s$_#'SHC(SRC)SFC1#C)S.C'#C)C#(%C%$##D'#k##s$i#2)C)S*C(#C$E#+$C&$#k##s$i#3(C)S'C(#C+C#$$E&$#k##s$e#4(C)S>C'#C#D#Ek##s$}#5&C)S1C(#C#D#$k##s%&#'&C)S;C(#C$ESe+Ses&#&$#?s-Y?#?#?#?#?#USq#+E#j##+#+SXs&.$ESf+S]s&0UT$G$ES)k##s%|#VSgS9Q#DS9QN#=$#m#&#VSgS3SK#DS3SKN#=$#m#&#US}SCSSCUTKDUTLDUTMDVSsDEVSsD;;D$Sh#<&NIIM#S$VTN'M9KLVTOFH#K#Lm$%#WTPDEGXTQFH$#l#:*)#l#;10#l#<43#l#=#s#'Fl#>78#l#?=>#l#@s#%s###j#As#'#j#Bs#)#V#GFj##s#,#j##s#9#6s#:s#9s#/#SXl#Cs#<D#l#Ds#?D#l#Es#Es#A#l#Fs#Ks#G#l#Gs#Ss#M#l#Hs#[s#U#l#Is#ds#]#l#Js#CD#l#Ks#FD#l#Ls#Ls#H#l#Ms#Rs#N#l#Ns#Zs#T#l#Os#bs#\#l#Ps#ks#d#l#Qs#nD#l#Rs#pD#l#Ss#us#r#l#Ts#zs#w#l#Us$%s#|#l#Vs$,s$'#l#Ws$4s$.#l#Xs$6D#l#Ys$8D#l#Zs$=s$:#l#[s$Bs$?#l#\s$Is$D#l#]s$Ps$K#l#^s$Xs$R#l#_s$ZD#l#`s$_D#l#as$gs$a#l#bs$os$i#l#cs$ys$q#l#ds%'s${#l#es%2s%)#l#fs%7D#l#gs%9D#l#hs%>s%;#l#is%Cs%@#l#js%Js%E#l#ks%Qs%L#l#ls%Ys%S#l#ms%[D#l#ns%aD#l#os%js%c#l#ps%ss%l#l#qs&#s%u#l#rs&/s&%#l#)s&8s&1#l#ss&Gs&>#l#ts&Ts&M#l#us&]s&X#l#vs&is&_#l#ws'#s&y#l#xs&us&m#l#@s'%s&{#l#ys''s'(#l#zs',s'-#l#{s'1s'2#m##s&:$SeSXj##s#v#VSiDHXS^D#Gs#\VS_DS\VS_Ds.y;D$SM#<s#^NIIM#S$UTRIIs#`NIIM$#$l#:#s#\s#Vl#;*s#c#l#<s#gs#f#j#|D#j#}D#$FG$GHk##$#k#|D#k#}D#EStSuT%l#=)$#l#>s#rs#s#l#?s#xs#y#l#@s$$s#~#j#As$&#j#Bs$(#V#GFj##s$+#j##s$8#6s$9s$8?#SXl#Cs$;D#l#Ds$>D#l#Es$Ds$@#l#Fs$Js$F#l#Gs$Rs$L#l#Hs$Zs$T#l#Is$cs$\#l#Js$BD#l#Ks$ED#l#Ls$Ks$G#l#Ms$Qs$M#l#Ns$Ys$S#l#Os$as$[#l#Ps$js$c#l#Qs$mD#l#Rs$oD#l#Ss$ts$q#l#Ts$ys$v#l#Us%$s${#l#Vs%+s%&#l#Ws%3s%-#l#Xs%5D#l#Ys%7D#l#Zs%<s%9#l#[s%As%>#l#\s%Hs%C#l#]s%Os%J#l#^s%Ws%Q#l#_s%YD#l#`s%^D#l#as%fs%`#l#bs%ns%h#l#cs%xs%p#l#ds&&s%z#l#es&1s&(#l#fs&6D#l#gs&8D#l#hs&=s&:#l#is&Bs&?#l#js&Is&D#l#ks&Ps&K#l#ls&Xs&R#l#ms&ZD#l#ns&`D#l#os&is&b#l#ps&rs&k#l#qs&~s&t#l#rs'.s'$#l#)s'7s'0#l#ss'Fs'=#l#ts'Ss'L#l#us'\s'W#l#vs'hs'^#l#ws'~s'x#l#xs'ts'l#l#@s($s'z#l#ys(&s('#l#zs(+s(,#l#{s(0s(1#m##s#LYT&GHCs#^#'GC'HC$$#'JC%#s(%'OC%#s('#DF#j#~D#9D')s(+C%J#'#C,s/{SF9D##DG$m#$#,s0#S*9D##DJ$m#$#,s0'Sv9D##DP$m#$#:QC$EQ'S%C$E#k##s(E#k##&#%QP%#C*#s(B:#C$E$%S%S#%#C*#s(G'#C$E#k##s(Q#k##)#)&CC#C$E$%S4S(%#C*#s(Q'#C)#C(#C$E#k##s(]#k##+#:S(C$ES($Es(9k##s(b#k##%#)s(DCC#C$E$'S/C)#C(#C$E#k##s(k#k##(#:s(.C$Es(/'s'~C$E#k##s(q#k##&#1s(<C)C'%#s('#Ds()#k##s(5#2s(+C$Es'|+s'}C&$#k##s(3#3s(%C(s'xC+C#$$E&$#k##s(.#4s'}C#Ds'rEk##s(D#5s'xC#Ds'ps'qk##s(G#'s'sC0s0ss0sSDSA.#-$*$#(#C1S5C'S)C)C#%#s'r#DS)#k##s(R#2S)C$Es'p+s'qC&$#k##s(P#3S&C(SFC+C#$$E&$#k##s(K#4SFC#Ds'nEk##s(a#5S.C#Ds'pS*k##s(d#'S*C(S'C1s'mC's'dC)C#%#s'e#Ds'g#k##s(k#2s'iC$Es'`+s'aC&$#k##s(i#3s'eC(s']C+C#$$E&$#k##s(d#4s'bC#Ds'XEk##s(z#5s'^C#Ds'Ws'Xk##s(}#'s'ZC%S?SG%#C*#s)_(#C1S?C'S<C)C#%#s'X#DS<#k##s)+#2S<C$Es'V+s'WC&$#k##s))#3S9C(S@C+C#$$E&$#k##s)$#4S@C#Ds'TEk##s):#5S2C#Ds'VS6k##s)=#'S6C(SAC1S7C'S3C)C#%#s'T#DS3#k##s)D#2S3C$Es'R+s'SC&$#k##s)B#3SLC(S8C+C#$$E&$#k##s)=#4S8C#Ds'PEk##s)S#5SHC#Ds'RSRk##s)V#'SRC(SUC$ESX&#s'&#Ds'*EN#j##%#+Sfs*V$ES]+T's*X;Ds&sSYs&t<s&vNIIM#S$ZTSs&wNIIM#l#:#s&ss&ml#;s&{s&z#l#<s&~s&}#k##.Sml#=$#Fl#>s'&s''#l#?s',s'-#l#@s'4s'2#j#A.#j#B0#V#GFj##3#j##9#6:s'=6#Sfl#Cs'KD#l#Ds'ND#l#Es'Ts'P#l#Fs'Zs'V#l#Gs'bs'\#l#Hs'js'd#l#Is'ss'l#l#Js'RD#l#Ks'UD#l#Ls'[s'W#l#Ms'as']#l#Ns'is'c#l#Os'qs'k#l#Ps'zs's#l#Qs#*D#l#Rs#,D#l#Ss#0s#.#l#Ts#4s#2#l#Us#;s#6#l#Vs#As#=#l#Ws#Hs#C#l#Xs#JD#l#Ys#LD#l#Zs#Ps#N#l#[s#Ts#R#l#\s#[s#V#l#]s#as#]#l#^s#hs#c#l#_s#jD#l#`s#oD#l#as#ss#q#l#bs#ws#u#l#cs#~s#y#l#ds$(s$$#l#es$/s$*#l#fs$1D#l#gs$3D#l#hs$7s$5#l#is$;s$9#l#js$Bs$=#l#ks$Hs$D#l#ls$Os$J#l#ms$QD#l#ns$WD#l#os$[s$Y#l#ps$_s$]#l#qs$fs$a#l#rs$ls$h#l#)s$rs$n#l#ss$ys$t#l#ts%&s${#l#us%-s%)#l#vs%9s%/#l#ws%Ms%H#l#xs%Es%=#l#@s%Os%J#l#ys%Qs%R#l#zs%Vs%W#l#{s%[s%\#m##s*PXTTJs+0C#ZSjDs%js%fs%es%b##Ds%cs%k%Os%f'#C%OJ%#C*#s+7'#C$F#j#~D#%JH%#C*#s+=,s3/S'9D##DO$m#$#,s33T(9D##DQ$m#$#:S#C$ES#$Es++k##s+P#k##%#:s+EC$Es+F$Es+<k##s+U#k##%#Cs+>C$Es+?%S,S4%#C*#s+T'#C)#C(#C$E#k##s+`#k##+#:S4C$ES4$Es%[k##s+e#k##%#Cs+>C$Es+?'S0C)#C(#C$E#k##s+m#k##(#:s+8C$Es+9's*uC$E#k##s+s#k##&#1s+(C)C'%#s*z#Ds*|#k##s+7#2s*~C$Es%[+s%\C&$#k##s+5#3s*yC+Cs*q$s*rE&$#k##s+/#4s*vC#Ds%ZEk##s+E#5s*qC#Ds%Xs%Yk##s+H#'s%[C0s3ts3tSBSD.#-$*$#(#C1S)C'S&C)C#%#s*m#DS&#k##s+S#2S&C$Es%Z+s%[C&$#k##s+Q#3SFC+Cs*l$s*mE&$#k##s+K#4S.C#Ds%YEk##s+a#5S*C#Ds%[S'k##s+d#'S'C(S>C1s*cC's*[C)C#%#s*\#Ds*^#k##s+k#2s*`C$Es%Y+s%ZC&$#k##s+i#3s*\C+Cs*U$s*VE&$#k##s+c#4s*ZC#Ds%XEk##s+y#5s*VC#Ds%Ws%Xk##s+|#'s%ZC%S<S?%#C*#s,^(#C1S<C'S9C)C#%#s*Q#DS9#k##s,*#2S9C$Es%X+s%YC&$#k##s,(#3S@C+Cs*P$s*QE&$#k##s+~#4S2C#Ds%WEk##s,8#5S6C#Ds%YSAk##s,;#'SAC(SDC1S3C'SLC)C#%#s*L#DSL#k##s,B#2SLC$Es%W+s%XC&$#k##s,@#3S8C+Cs*K$s*LE&$#k##s,:#4SHC#Ds%VEk##s,P#5SRC#Ds%XSUk##s,S#'SUC(SSC&s)}s%Vj###s*%$ET'+SZs-Qj#A#s)\j#B%#V#GFj##s*'#j##s*)#6s**s%_*#S]l#Cs*9D#l#Ds*<D#l#Es*Bs*>#l#Fs*Hs*D#l#Gs*Ps*J#l#Hs*Xs*R#l#Is*as*Z#l#Js*@D#l#Ks*CD#l#Ls*Is*E#l#Ms*Os*K#l#Ns*Ws*Q#l#Os*_s*Y#l#Ps*hs*a#l#Q;D#l#R=D#l#SA?#l#Ts#%s###l#Us#+s#'#l#Vs#1s#-#l#Ws#8s#3#l#Xs#:D#l#Ys#<D#l#Zs#@s#>#l#[s#Ds#B#l#\s#Js#F#l#]s#Ps#L#l#^s#Ws#R#l#_s#YD#l#`s#^D#l#as#bs#`#l#bs#fs#d#l#cs#ls#h#l#ds#rs#n#l#es#ys#t#l#fs#{D#l#gs#}D#l#hs$%s$##l#is$)s$'#l#js$/s$+#l#ks$5s$1#l#ls$<s$7#l#ms$>D#l#ns$DD#l#os$Hs$F#l#ps$Ls$J#l#qs$Rs$N#l#rs$Xs$T#l#)s$^s$Z#l#ss$es$`#l#ts$ns$g#l#us$ts$p#l#vs%$s$v#l#ws%/s%+#l#xs%+s%'#l#@s%1s%-#l#ys%3s%4#l#zs%8s%9#l#{s.*s.+#m##s-7)s-zs*k%S]#%SfSX%#s*n*#s-~$&#j##s#N#VSiDJXS^Ds)aG#UT)S\VS_D#ODs)a#;Ds)cSh#<s*aNIIM#S$VSsDs.,JD#s*aODs)g#OD(s*cPD#&;D%SM#<s*hNIIM#S$Is*iNIIM*s)h#l#:#s*es*_l#;1s*l#l#<s*ps*o#j#|D#j#}D#j$#D#%GH+F#%G@%HJ%#s+/*#s.?$&#k##(#k#|D#k#}D#k$#D#XFStT*TUT%l#=/$#l#>s+&s+'#l#?s+,s+-#l#@s+4s+2#j#As#q#j#Bs#s#V#GFj##s+9#j##s+;#6s+<s&qs#-#S]l#Cs+KD#l#Ds+ND#l#Es+Ts+P#l#Fs+Zs+V#l#Gs+bs+\#l#Hs+js+d#l#Is+ss+l#l#Js+RD#l#Ks+UD#l#Ls+[s+W#l#Ms+as+]#l#Ns+is+c#l#Os+qs+k#l#Ps+zs+s#l#Qs$-D#l#Rs$/D#l#Ss$3s$1#l#Ts$7s$5#l#Us$=s$9#l#Vs$Cs$?#l#Ws$Js$E#l#Xs$LD#l#Ys$ND#l#Zs$Rs$P#l#[s$Vs$T#l#\s$\s$X#l#]s$bs$^#l#^s$is$d#l#_s$kD#l#`s$pD#l#as$ts$r#l#bs$xs$v#l#cs$~s$z#l#ds%(s%$#l#es%/s%*#l#fs%1D#l#gs%3D#l#hs%7s%5#l#is%;s%9#l#js%As%=#l#ks%Gs%C#l#ls%Ns%I#l#ms%PD#l#ns%VD#l#os%Zs%X#l#ps%^s%\#l#qs%ds%`#l#rs%js%f#l#)s%ps%l#l#ss%ws%r#l#ts&$s%y#l#us&*s&&#l#vs&6s&,#l#ws&As&=#l#xs&=s&9#l#@s&Cs&?#l#ys&Es&F#l#zs&Js&K#l#{s/<s/=#$s&Zs&Pm#$#YT&s&\s&RCs#r#TDs&\s&V#s)iFl#)s&`s&_#%HG%#C*#s/6'#C$s)q#k##GGSHXSwOJHG/JF#UOF#P#H/QFJ&$#j#%P#VT+P#k##)#UJF#O#G/PFH&$#j#%O#VT+O#XSwPOJH/OG#k##%#&,#XSwQPOJ/PH#k##0#j##&#j##$Fj##2#YTVOJHGF64+&$#j$$H#j#.?#j$%A#j$&T,#j#/T-#k$$H1k#.s#$#k$%s#&#k$&T,#k#/T-#0s7Ps7PS'S*USx#UT.$VS`S+#0s7Ts7TS>S'VSx#F#s7V#SvUT.%VS`S+#/RF#&&#j#%R#'PC*#s*ID#VSx1##s7`#SW/R%0KFKGKH##GF,JH,JG#D$#k##&#,HG,HF#D$#KJ##HGk##%#&)#KO##JHk##-#j##&#j##$Fj##/#WTWHGF61+&$#j#08#j#1:#j#9T/#k#0;/k#1=#k#9T/#,s8$S>'#C)#C'QC*#s#)D#USI#)C#%(#VT0s8-#VSks8.$#DFs'Zj#~D#,s81S1'#C)#C)CF%$#VSks86##D#s'bj#~D#9D*#DQ+m#$#,s8<TX9D##DS%$m#$#:s0?C$Es0@$Es'Zk##s0Y#k##%#Cs'\C$Es']%S0S/%#C*#s0X'#C)#C(#C$E#k##s0d#k##+#:S/C$ES/'SKC$E#k##s0j#k##&#Cs'`C$Es'a'S=C)#C(#C$E#k##s0r#k##(#:s/xC$Es/y$Es/dk##s0w#k##%#1S:C'S-C)C#(S-C%$##DS-#k##s0=#2S-C(SEC$E#+$C&$#k##s0<#3SEC+Cs/l$s/mE&$#k##s06#4S5C#Ds*ZEk##s0L#5S)C#Ds/iS&k##s0O#1SFC)Cs/_%#s/c#DS.#k##s0S#2S.C$Es/c+s/dC&$#k##s0Q#3S*C+Cs*S$s*TE&$#k##s0K#4S'C'S>C#D#Ek##s0b#5S>C(S1C#D#S1k##s0f#'S1C(S;C0s97s97SPSV.#-$*$#1#C0s9<s9<SQSP.#-$*$#'#C)C#(%C%$##D'#k##s0v#2)C0s9Gs9GT1SQ.#-$*$#(#C$E#+$C&$#k##s0y#3(C0s9Qs9QT2T1.#-$*$#(#C+C#$$E&$#k##s0x#4(C0s9[s9[T3T2.#-$*$#'#C#D#Ek##s17#5&C0s9cs9cSyT3.#-$*$#(#C#D#$k##s1?#'&C0s9ks9kSWSy.#-$*$#(#C%S2S@%#C*#s2&1#C%S6S2%#C*#s2*'#C)C#(%C%$##D'#k##s1Q#2)C%SAS6%#C*#s24(#C$E#+$C&$#k##s1S#3(C%SDSA%#C*#s2=(#C+C#$$E&$#k##s1Q#4(C%SBSD%#C*#s2F'#C#D#Ek##s1k#5&C%S7SB%#C*#s2M(#C#D#$k##s1r#'&C%S3S7%#C*#s2T(#C)S=C1#C)S:C'#C)C#(%C%$##D'#k##s2##2)C)S-C(#C$E#+$C&$#k##s2##3(C)SEC(#C+C#$$E&$#k##s1{#4(C)S5C'#C#D#Ek##s27#5&C)S)C(#C#D#$k##s2<#'&C)S&C(#C&s(Fs+>)S8C)S6C*S8S6)C#%%##D'#j##)#$ESz+Sus3A$ESSk##s30#VSgS1Q#DS1QN#=$#m#&#JDs.hs.gJDs'fs.hPDs.js'gJDs.j#OD%#;D'SY#<s/kNIIM#S$l#:#s/gs/al#;s'os/n#l#<s/rs/q#j#|D#j#}D#j$#D#)FG)HG*FH)G#%%##D'#k#|D#k#}D#k$#D#ES8CSQl#=-$#l#>s0&s0'#l#?<=#l#@s04B#j#As#%#j#Bs#'#V#GFj##s(t#j##s(v#6s(ws+os#,#SZl#Cs#5D#l#Ds#8D#l#Es#>s#:#l#Fs#Ds#@#l#Gs#Ls#F#l#Hs#Ts#N#l#Is#]s#V#l#Js0RD#l#Ks0UD#l#Ls0[s0W#l#Ms0as0]#l#Ns0is0c#l#Os0qs0k#l#Ps0zs0s#l#Qs)-D#l#Rs)/D#l#Ss)3s)1#l#Ts)7s)5#l#Us)=s)9#l#Vs)Cs)?#l#Ws)Js)E#l#Xs#nD#l#Ys#sD#l#Zs#{s#u#l#[s$'s#}#l#\s$1s$)#l#]s$;s$3#l#^s$Fs$=#l#_s$KD#l#`s$QD#l#as$Zs$S#l#bs$cs$\#l#cs$ns$e#l#ds$ys$p#l#es%)s${#l#fs%/D#l#gs%1D#l#hs%6s%3#l#is%;s%8#l#js%As%=#l#ks%Gs%C#l#ls%Ms%I#l#ms-DD#l#ns*OD#l#os%Ss%Q#l#ps%Ws%U#l#qs%]s%Y#l#rs%ds%_#l#)s%ls%f#l#ss%rs%n#l#ts%{s%t#l#us&&s%}#l#vs&2s&(#l#ws./s.+#l#xs&9s&5#l#@s.1s.-#l#ys&<s&=#l#zs&As&B#l#{s+Ks+L#)s&WC)s&~C)Cs&X%$##D&#)s4:CVSks<&F,s<'T$#D$#j#~D#VT#s<*T(WTYs<+s+V#TDs+W%#)SW*s4Bs&d)C#%1#TD-)&#Fl#)4/#%s&j2VSks<3##D#s.km#&#$Es$&j##s$*#;Ds0#SMs0$<s0~NIIM#S$PDs0&s0%;Ds1#SM#<s1%NIIM#S$Is1&NIIM&s0%#l#:#s0~s0xl#;s0,s1)#l#<s1-s1,#j#|D#j#}D#*GH$E#k##s5I#k#|D#k#}D#ES8SQT*l#=)$#l#>s18s19#l#?s$.s$/#l#@s1Fs$4#j#As$7#j#Bs$9#V#GFj##s**#j##s*,#6s*-s-%=#SZl#Cs$GD#l#Ds$JD#l#Es$Ps$L#l#Fs$Vs$R#l#Gs$^s$X#l#Hs$fs$`#l#Is$os$h#l#Js1dD#l#Ks1gD#l#Ls1ms1i#l#Ms1ss1o#l#Ns1{s1u#l#Os2's1}#l#Ps20s2)#l#Qs*?D#l#Rs*AD#l#Ss*Es*C#l#Ts*Is*G#l#Us*Os*K#l#Vs*Us*Q#l#Ws*\s*W#l#Xs%$D#l#Ys%)D#l#Zs%1s%+#l#[s%9s%3#l#\s%Cs%;#l#]s%Ms%E#l#^s%Xs%O#l#_s%]D#l#`s%cD#l#as%ls%e#l#bs%us%n#l#cs&$s%w#l#ds&/s&&#l#es&;s&1#l#fs&AD#l#gs&CD#l#hs&Hs&E#l#is&Ms&J#l#js&Ss&O#l#ks&Ys&U#l#ls&_s&[#l#ms.VD#l#ns+aD#l#os&es&c#l#ps&is&g#l#qs&os&k#l#rs&vs&q#l#)s&~s&x#l#ss'(s'$#l#ts'1s'*#l#us'8s'3#l#vs'Ds':#l#ws/As/=#l#xs'Ks'G#l#@s/Cs/?#l#ys'Ns'O#l#zs'Ss'T#l#{s,]s,^#VTZs'h#ZSjDs'is'Ys#\s'g#,s=4s'eVT[s=5s'gZSjDs'fs'd%$#XFs=7s'hSv#l#)s'vs's#>s=8s=8s(F,s=:#'#C)#CUSIs(<)C#%%#VT0s=@##s=@#SWm#,#m##s(@VS`GH/RF#VS[HGFHJGG#&%#k##'#VS[GFFGHGF#&%#VS`HJ/RG#k##%#&*#VS`JO/RH#k##.#j##&#j##$Fj##0#WT\HGF62+&$#j#9R#j$'R#j$(R#k#9R/k$'R#k$(R#%S=SK%#C*#s5r1#C%S:S=%#C*#s5v'#C)C#(%C%$##D'#k##s5A#2)C%S-S:%#C*#s6$(#C$E#+$C&$#k##s5C#3(C%SES-%#C*#s6-(#C+C#$$E&$#k##s5A#4(C%S5SE%#C*#s66'#C#D#Ek##s5[#5&C%S)S5%#C*#s6=(#C#D#$k##s5b#'&C%S&S)%#C*#s6D(#C1S@C)Cs4(%#s4,#DS2#k##s5k#2S2C$Es4,+s4-C&$#k##s5i#3S6C+Cs/6$s/7E&$#k##s5c#4SAC'SDC#D#Ek##s5z#5SDC(SBC#D#SBk##s5~#'SBC1S8C)Cs4#%#s4'#DSH#k##s6'#2SHC$Es4'+s4(C&$#k##s6%#3SRC+Cs/5$s/6E&$#k##s5{#4SUC'SSC#D#Ek##s66#5SSC(SVC#D#SVk##s6:#'SVC(SPC)S2C1#C's&[C)C#(s&]C%$##Ds&_#k##s6C#2s&aC)SAC(#C$E#+$C&$#k##s6C#3(C)SDC(#C+C#$$E&$#k##s6?#4(C)SBC'#C#D#Ek##s6W#5&C)S7C(#C#D#$k##s6\#'&C)S3C(#C)s&{C*s&~s&}#D$#j##s'%#VSgSSQ#DSSQN#=$#m#&#JDs%\s+}JDs3%s+~JDs3%s,#PD$#;D&SY#<s4&NIIM#S$l#:#s3~s3xl#;s,*s4)#l#<s4-s4,#j#|D#j#}D#j$#D#*FG)#H)FH)GH*$##D&#k#|D#k#}D#k$#D#ECS8SQl#=-$#l#>s4=s4>#l#?;<#l#@s4Ks4I#j#As'<#j#Bs'>#V#GFj##s-/#j##s-1#6s-2s0*s#'#SZl#Cs#,D#l#Ds#/D#l#Es#5s#1#l#Fs#;s#7#l#Gs#Cs#=#l#Hs#Ks#E#l#Is#Ss#M#l#Js4iD#l#Ks4lD#l#Ls4rs4n#l#Ms4xs4t#l#Ns5$s4z#l#Os5,s5&#l#Ps55s5.#l#Qs#]D#l#Rs#_D#l#Ss#ds#a#l#Ts#is#f#l#Us#os#k#l#Vs#us#q#l#Ws#{s#w#l#Xs5XD#l#Ys#~D#l#Zs$'s$$#l#[s$,s$)#l#\s$2s$.#l#]s$8s$4#l#^s$>s$:#l#_s(bD#l#`s(hD#l#as(qs(j#l#bs(zs(s#l#cs))s(|#l#ds)4s)+#l#es)@s)6#l#fs)FD#l#gs)HD#l#hs)Ms)J#l#is)Rs)O#l#js)Xs)T#l#ks)^s)Z#l#ls)ds)`#l#ms$ND#l#ns$SD#l#os$[s$U#l#ps$cs$]#l#qs$ms$e#l#rs$ws$o#l#)s%&s$y#l#ss*-s*)#l#ts*6s*/#l#us*=s*8#l#vs*Is*?#l#ws2Fs2B#l#xs*Ps*L#l#@s2Hs2D#l#ys*Ss*T#l#zs*Xs*Y#l#{s/bs/c#'s8EC*#s+9)#C)%C*#s&x#D%#'s2hC*#s*u)#C*s2qs8UD#VS[S+#'FCD#FS+#G'#&'#j#~D#DFFS+#G,#&,#j#~D#%Gs8]$#J,s@PSG9D##DS4$m#$#9Ds:i#DS/s:jm#$#,s@WSZ9D##DSK$m#$#*PQD#VS[S+#*S#QD#FS+#G'#&'#QE*$E#QE)%E#+&#&&#9DEj#%DFQEFj#%D#9D4`T4DRDDS{&SI$T555#`T6RDS[SIT7T]S+E(5.#9D4`T4DRDDS{)SI'T555#fT^RRRDDDT_SISISIT8T`S+E+5/#`T6RDT9SIT:Ta92'5/#ZTb952/'#VT;E9+E:#D4;&$#$=E#D7E&$#=&#*S%S#QE#*S#S%VT;E#+E$QE%#D#&&%#$(E#D&E&$#=&#*S%S(QE#USaS+USa#USa#RD#RD%RD'AD$#AD&#VSb#ScUSa)RD#UTcS\VTdD#WT<D#,RDS+AD,#AD.#AD&#AD*#VSb#ScWT<D*,AD#)VSb#ScUSa0RD#AD#&VSb#ScAD9/AD1#AD5#VSb#ScBSC9s6;BSC:#BSC%#BSC*#BSC/#BSC3#BSC?#BSC@#VSiDOXS^D#Hs6BVSiDPXS^D#Js6DXS^D%G#VS_DsA`PD#s.E;Ds6ESh#<s6GNIIM#S$;Ds5KSY%<s6INIIM#S$[Sds6JNIIM%#ZS|s6KNIIMS#;Ds5OSYs6K<s6MNIIM#S$[Sds6NNIIM%#[T=s6ONIIM'#ZS|s6PNIIMS%UT)sAnVS_D#PD#s.S;Ds5VSY#<s6UNIIM#S$[Sds6VNIIM(#;D&SMs6V<s6XNIIM#S$ZS|s6YNIIMS([Sds6ZNIIM$#[T=s6[NIIM'#OD:s.X;D#SM-<s6^NIIM#S$;Ds._SM=<s6`NIIM#S$;Ds6`SMs5d<s6bNIIM#S$ODs6bs5e;Ds5gSh#<s6eNIIM#S$[Sds6fNIIM&#Is6gNIIM)s5f#Is6hNIIM,s5g#Is6iNIIM0s5h#Is6jNIIM=s5i#l#:#s6fs6`l#;s#+s6m#l#<s#1s6p#j#|D#j#}D#j$#D#j$)D#j$*D#j$+SN#j$,SN#j$-SN#*JH+E##DF$&$##DFE&P#=%#*PJ#DH#&S##$%E&#S%=%#%Ps:M$#Q$PQ$EO%EP+O#&%#k##'#k##)#k##,#k##3#k#|D#k#}D#k$#D#k$)D#k$*D#k$+SN#k$,SN#k$-SN##DJE*S/S,+E#*S4S,$#E`F'%#S/S4S,JGHOS%S(l#=s#))#l$.s$,D#l#os$7s$/#l$/s$:D#l#ps$Ds$=#XTes$Xs$Rs$F#l#ys$as$b#l#zs$fs$g#l#{s$js$k#j$0s$o#j$1s;e#j#RD#j#YD#j#`D#Y#s%*s-@s:zOJ's%)C9Ds-E#DPs-Fm#$#,sBjS;9D##DS#$m#$#,sBnSe9D##DS($m#$#:s52C$Es53%S/S,%#C*#s;)'#C$E#k##s;3#k##)#)&CC#C$E$%SKS0%#C*#s;3'#C)#C(#C$E#k##s;?#k##+#:S0C$ES0$Es-3k##s;D#k##%#)s-<CC#C$E$'S:C)#C(#C$E#k##s;M#k##(#:s:IC$Es:J$Es5&k##s;R#k##%#1s:FC)Cs5*%#s:?#Ds:A#k##s:r#2s:CC$Es5*+s5+C&$#k##s:p#3s5/C+Cs2.$s2/E&$#k##s:j#4s23C0sCMsCMS7SB.#-$*$#'#C#D#Ek##s;)#5&C0sCUsCUS3S7.#-$*$#(#C#D#$k##s;1#'&C0sC]sC]SLS3.#-$*$#(#C1S.C)Cs52%#s:G#DS*#k##s;;#2S*C$Es56+s57C&$#k##s;9#3S'C+Cs2;$s2<E&$#k##s;3#4S>C#Ds-?Ek##s;I#5S1C#Ds-AS;k##s;L#'S;C(SOC1s:2C)Cs50%#s:,#Ds:.#k##s;R#2s:0C$Es51+s52C&$#k##s;P#3s56C+Cs27$s28E&$#k##s;J#4s2<C%S9S<%#C*#s<?'#C#D#Ek##s;d#5&C%S@S9%#C*#s<F(#C#D#$k##s;k#'&C(s-'C1S2C)Cs53%#s:.#DS6#k##s;q#2S6C$Es57+s58C&$#k##s;o#3SAC+Cs2>$s2?E&$#k##s;i#4SDC#Ds(]Ek##s<##5SBC#Ds:;S7k##s<&#1SHC)Cs5/%#s:&#DSR#k##s<*#2SRC$Es53+s54C&$#k##s<(#3SUC+Cs2;$s2<E&$#k##s;~#4SSC#Ds(ZEk##s<8#5SVC#Ds(\SPk##s<;#'SPC(SQC$ESZ&#s2Dj###s5B+Szs=9$ESu+Sts=;j#A#s57j#B%#V#GFj##(#j##,#6-s2N+#Szl#Cs:#D#l#Ds:&D#l#Es:,s:(#l#Fs:2s:.#l#Gs::s:4#l#Hs:Bs:<#l#Is:Ks:D#l#Js:*D#l#Ks:-D#l#Ls:3s:/#l#Ms:9s:5#l#Ns:As:;#l#Os:Is:C#l#Ps:Rs:K#l#Q=D#l#R?D#l#Ss##A#l#Ts#'s#%#l#Us#-s#)#l#Vs#3s#/#l#Ws#9s#5#l#Xs:pD#l#Ys:xD#l#Zs#?s#=#l#[s#Cs#A#l#\s#Is#E#l#]s#Os#K#l#^s#Us#Q#l#_s#WD#l#`s#YD#l#as#as#[#l#bs#is#c#l#cs#os#k#l#ds#us#q#l#es#{s#w#l#fs#}D#l#gs$#D#l#hs$'s$%#l#is$+s$)#l#js$1s$-#l#ks$7s$3#l#ls$=s$9#l#ms$?D#l#ns$ED#l#os$Ns$G#l#ps$Ws$P#l#qs$]s$Y#l#rs$cs$_#l#)s$is$e#l#ss$os$k#l#ts$xs$q#l#us%#s${#l#vs%/s%%#l#ws4`s4\#l#xs%;s%3#l#@s4bs4^#l#ys%>s%?#l#zs%Cs%D#l#{s%Hs%I#m##s=(WTfs'uC#ZSjDs'vs'gs%Os%N#)s'xC*#s,:TDs'xs'o%#Fl#)s(&s'|#VS[S+s04%s0:s5/%#C*#s=m'#C)#C*#s0='#CD#FS+#Gs0>#&-#m#/#>sEgsEgs0q,sEi#7sEisEis0s,sEk#%%#%#C*#s=}'#C)#C'*C)#C*%#'#CD#FS+#Gs0P#&?#m#4#FS+s1$Gs0T#&s###m#&#XFs1(S+s0W#l#)s+$s*}#XTgs0}s0|s+?#XThRs1's1$#ZFRsF%s12s10SW#l#)s1:s15#0sF'sF'S*S.@#/sF)Sy#m#&#l$0s1fs1a#l$1s8zs8w#l$2s>SD#l$3s>TD#l$4s>VD#l$5s>]s>X#l$6s>`s>_#l#)s>hs>f#l$7s?#s>~#l#)s?)s?'#j$6s??#j$7s?E#V#GFj##s?K#j##s?Y#6s?Zs?Ws?R#Fl#+s?bs?_#l#)s?ls?j#0sF=sF=S%S#@#/sF?SD#m#&#m##$j#2s@+#j#3s@3#j#4s@=#j#5s@B#j#6s@G#j#7s@S#j#+s@[#j#9sFI#j#'sFJ#V#GFj#'sFL#j#'sFM#YTisFNsFNs@e#S?[#S&S-S0S(PGFj#2sA;#j#3sAB#V#GFj##sAL#j##sA\#6sA]sAXsAT#Fj#)sAf#j#4sAu#V#GFj##sAz#j##sB>#6sB?sB2sB.#Fj#)sBC#j#5sBU#V#GFj##sBZ#j##sC$#6sC%sBqsBm#Fj#)sC)#j#6sC>#V#GFj##sCJ#j##sCt#6sCusCdsC`#Fj#)sD$#j#7sDA#V#GFj##sDI#j##sE'#6sE(sDksDg#Fl#)sEPsE/#WTjsETsER#j#+sEW#U#Fj##sEf#USJsE\WSpsFs#S(#K#LXS(S%S#FPWTksE\sEZ#j#+%#U#Fj##sEk#ZTlsEosElsEe+#Fl#+sEvsEs#l#)sE~sE|#YFsF~sF=sF<J#l#)sFCsF?#BsG#QPL#/sG&H#m#&#j#*sF{#j#+sFd#j#$sG*#j#%sG+#j$8sFy#j#&sG+#j#msG-#YTmsG.sF{sFm#Fj#&sG.##"). Qed.

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
Scheme kc__4 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

(* [comment removed for export] *)
Lemma lazy_interior_aligned : forall a n,
  (bv_unsigned a mod page_size = 0)%Z ->
  (bv_unsigned n mod page_size = 0)%Z ->
  (0 < bv_unsigned n)%Z ->
  lazy_interior a n = [(a, n)].
Proof.
  ltac2:(KReplay.runc [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@kc__2); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.add_mod); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.div_add_l); constr:(@Stdlib.ZArith.BinInt.Z.eq_decidable); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.ZArith.BinInt.Z.div_small); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Corelib.Init.Datatypes.prod); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.pair); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@kc__4); constr:(@stdpp.tactics.f_equal_help); constr:(@Corelib.Numbers.BinNums.N); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@stdpp.bitvector.definitions.bv_wrap_small); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@Stdlib.micromega.Tauto.X); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.lazy_interior)|] [|@__ff; @__varmap; @__wit; @__arith; @__sat0; @__sat1; @H12; @H11; @H10; @H9; @r0; @q0; @H8; @H7; @H6; @H5; @H4; @r; @q; @H3; @H2; @H1; @H0; @H; @heq_lo; @heq_sz; @__x1; @__sat2; @__sat3; @__sat4; @H17; @H16; @H15; @H14; @r1; @q1; @H13; @__sat5; @__sat6; @H22; @H21; @H20; @H19; @r2; @q2; @H18; @z; @H24; @H23; @__x2; @__x3; @__x4; @__x5; @H29; @H28; @H27; @H26; @H25; @r3; @q3; @Hlo'; @Hm'; @__sat7; @__sat8; @E; @b; @b2; @b1; @n; @__sat9; @y; @x; @__p1; @E2; @E1; @Hsum; @Hhi; @Hlo; @Hps; @sz; @lo; @Hnr; @Har; @Hpos; @Hn; @Ha; @a|] "#J6$.%-$9$6$:###$$U$V$T#%#/#,#*#)#0#'#2#-#6#($Z#&#+#.#3#4#1#5#7#8#@#:$]#>#S#?#I#<#J#A#B#H#=#C#G#U#Z#]#9#D#Q#T#Y#;$f#M#E#K#O#F#\#L#N#V#[$N#R#P#X#_#W#c$Y#p$r#b#^#d#a$4#t#`#e#h#o#q%##l$l%(%1$^#k#g$y#s#x${#f#i#m%.#u#y$L$M$O$e$G$q$w$}$~$&%,%0#}$.$B$2$<$?$P$Q$S$[$_$`$\$d$g$k$u$t$|#w#{$#$'$(#j$+$-%%%$#r%&%-%/%2#|%3$%$$#z%*%4$5$>$D$;$=$7$E$F$K$i$H$I$J$A$h$8$@$W$R$b$3$j$n$v%'$x%)$1$c$m$a$p$o$s$z%+$C$XU$c&$d%$e%$f%$g%$h%$i%$j%$k($l%$<%$2%$m%$n%$o%$p%$q%$r%$s%$t'$u*#z&$v+#{'$w$$x)$y&$z'#G$${%#&%$|&$}%#;$#S$#_$$~$%#%%$%%%%%&$%'%#0$#?$%(&%)&%*+%+$%,%$<&;Sa;#;#;#;#;#UT-#G#4$G(#C#D#E4'K&E#VT.)Q4*Q$E#UT/,&%#'%#4/O40N5D##DF$m#$#44M5D##DK$m#$#2KC$EK$EC(QC$E#k##%#k##'#2QC$EQ(OC$E#k##+#k##&#-S%C#DCER#*OC)C#%#+#DO#k##'#.OC&EC(NC$E#&$C'$#k##'#/NC&CE(S(C&C#$$E'$#k##'#0S(C*MC#D#Ek##:#1MC(S#C#D#S#k##>#*S#C(S)C-S)C*LC)C#(LC%$##DL#k##s#&#.LC(PC$E#&$C'$#k##s#%#/PC(S,C&C#$$E'$#k##s#$#0S,C*RC#D#Ek##s#7#1RC(S*C#D#S*k##s#;#*S*C(S+C$ES-&S-s#Y'$#;s#f;#;#;#;#;#USz#&E#j##+#&S$s#d$ES.&S/s#f$ES1&S1s#h'$#j###*&SGs#k$ES7&S<s#mUS1S%$EMk##s#b#US1K$ES+k##s#e#US{SSUS|SSUT0DUT1DUT2DSDESD;6D$SZ#7&JHHI#S&VT3'I5S2SmVT4FK#S2#Smm$%#WT5DEGXT6FK$#l#$*)#l#%10#l#&43#l#'#s#'Fl#(97#l#)=;#j#*?#j#+A#V#GFj##s#$#j##s#)#+s#*s#)s#'#S7j#,s#,#j#-s#.#V#GFj##s#1#j##s#>#+s#?s#>s#4#S.l#.s#AD#l#/s#CD#l#0s#Hs#E#l#1s#Ms#J#l#2s#Ts#O#l#3s#[s#V#l#4s#cs#]#l#5s#eD#l#6s#gD#l#7s#ls#i#l#8s#qs#n#l#9s#ys#s#l#:s$%s#{#l#;s$.s$'#l#(s$5s$0#l#)s$=s$7#l#<s$?s$@#l#=s$Ds$E#m##s$*4s$WS(5D##DG$m#$#4s$[S#5D##DS'$m#$#2S'C$ES'(S%C$E#k##s$K#k##&#2S%C$ES%k##s$Os$9k##$#-OC*NC)C#%#s$?#DN#k##s$I#.NC$Es$<&s$=C'$#k##s$G#/S(C(MC&C#$$E'$#k##s$F#0MC#Ds$:Ek##s$X#1S#C#Ds$<S)k##s$[#*S)C-LC*PC)C#%#s$9#DP#k##s$a#.PC$Es$7&s$8C'$#k##s$_#/S,C(RC&C#$$E'$#k##s$^#0RC#Ds$5Ek##s$p#1S*C#Ds$7S+k##s$s#*S+C(S-C$ES$'#s$/j###s$w&S.s%7$ES/&SBs%9$ESG'#s$.j###s$}&S7s%=$ES<&S3s%?MS<$ES(&S(C'$#NS3$ES*&S*C'$#?N$ES)k##s%<#?Qk##s%>:$EL&LC'$#j###s%5&PC$ES,&RC&S1C's$L#j###s%;&SGC&S<CJDGHDSa6Ds$@SZ#7s$BJHHI#S&UT7H6D&SHs$C7s$EJHHI#S&ZS}s$FJHHI#9s$GJHHI'&#l#$#s$Cs$=l#%,s$J#l#&s$Ns$M#j#>D#&EF#DGEk###T8k##%#k#>D#ACS8l#')$#j#77#j#:s$`#V#GFj##;#j##s$h#+s$i@>#Oj#8B#j#9s#$#V#GFj##s#'#j##s#,#+s#-s#,s#*#S'l#(s#0s#/#l#)s#4s#2#l#:s#9s#6#l#3s#>s#;#j#*s#@#j#+s#B#V#GFj##s#E#j##s#I#+s#Js$us#H#S<j#,s#L#j#-s#N#V#GFj##s#Q#j##s#U#+s#Vs%&s#T#S/l#.s#XD#l#/s#ZD#l#0s#^s#\#l#1s#bs#`#l#2s#is#d#l#3s#os#k#l#4s#vs#q#l#5s%TD#l#6s#yD#l#7s#}s#{#l#8s$%s$##l#9s$,s$'#l#:s$2s$.#l#;s$9s$4#l#(s$>s$;#l#)s$Es$@#l#<s$Gs$H#l#=s$Ls$M#TKC#*KC)C#(KC%$##DK#%S'K4s&PS)5D##DQ$m#$#2OC$EOk##s&>s$Dk##$#3NC$EN$Es%|k##s&C#k##%#-S(C)Cs&$%#s$H#DM#k##s&<#.MC$Es&%&s&&C'$#k##s&:#/S#C&Cs&&$s&'E'$#k##s&8#0S)C#Ds&)Ek##s&J#1LC#Ds&%Pk##s&M#-S,C)Cs%x%#s$E#DR#k##s&Q#.RC$Es%y&s%zC'$#k##s&O#/S*C&Cs%z$s%{E'$#k##s&M#0S+C*S-C#D#Ek##s&`#1S-C(S$C#D#S$k##s&d#*S$C(S.C's$Ks%yj###s&g's$Gs%tj###s&i$ES5&S0s'*MS5NS0US<Nk##s&|s&'US3S%$EP'#s$>j###s&s&S,C$ER's$Ys$<j###s&w&S7C&S3CACSIl#'s$3s$.#j#7%#j#:s$\#V#GFj##)#j##s$c#+s$ds$G,#Nj#8s$Y#j#90#V#GFj##3#j##7#+8s$S6#Ql#):;#l#(s$[<#l#?>s$]#l#:@s$a#l#3Bs$f#j#*s#$#j#+s#&#V#GFj##s$n#j##s$p#+s$qs&Bs#+#S5j#,s&E#j#-s&J#V#GFj##s$z#j##s$|#+s$}s&Os#3#S1l#.s#6D#l#/s#8D#l#0s#=s#:#l#1s#Bs#?#l#2s#Hs#D#l#3s#Ns#J#l#4s#Ts#P#l#5s&tD#l#6s%FD#l#7s#Zs#X#l#8s#^s#\#l#9s#ds#`#l#:s#js#f#l#;s#ps#l#l#(s#vs#r#l#)s#{s#x#l#?s'Us'P#l#<s#~s$##l#=s'_s'`#Ts$(C#*s$)C)C#(s$+C%$##Ds$-#%QCUSzSa,$#4s'~L5D##DS%$m#$#2NC$Es%lk##s'l#k##s$.#3S(C$Es'Fk##s'p#k##s%@#%MS(2#C$E$%S)S#(#C$E#k##s'x#k##'#%S#M3#C$E$%LS)*#C$E#k##s($#k##'#-/C)C'()C%$##D+#k##s'z#.-C%PL(#C$E#&$C'$#k##s'z#/(C%S,P(#C&C#$$E'$#k##s'z#0(C%RS,*#C#D#Ek##s(2#1&C%S*R(#C#D#$k##s(7#*&C%S+S*(#C-S-C)Cs$5%#s$9#DS$#k##s(>#.S$C$Es$9&s$:C'$#k##s(<#/S.C(S/C&C#$$E'$#k##s(;#0S/C*SBC#D#Ek##s(N#1SBC(S1C#D#S1k##s(R#*S1C(SGC-SGC*S7C)C#(S7C%$##DS7#k##s(Z#.S7C(S<C$E#&$C'$#k##s(Y#/S<C(S3C&C#$$E'$#k##s(X#0S3C*S5C#D#Ek##s(k#1S5C(S0C#D#S0k##s(o#*S0C(S9C$ES:&S:s)1'$#j###s(t&S=s)4$ESC&SJs)6$ES>&S>s)8'$#j###s({&S;s);$ES6&S8s)=MS6NS8US0SKUS>S(k##s)4s&SUSMS%k##s)6s&jUS;O's&Rs$qj###s),&S+C's(;s$pj###s)/$ES3&S5C&S>C'9#j###s)4&S;C&S8CACSNl#'s&Ls&G#j#2%#j#:;#V#GFj##)#j##s###+s#$.,#S)j#30#j#72#V#GFj##s&c#j##s(P#+s(Qs%*7#S(j#8:#j#9s&z#V#GFj##s&n#j##s&p#+s&qs%4@#S%l#@s##s#$#l#?s#&s#%#l#As#)s#(#l#:s#+s%6#l#3s#-s'%#l#,s#/s'*#j#Bs#1#j#Cs#3#V#GFj##s#6#j##s#;#+s#<s#;s#9#S6j#Ds#>#j#Es#@#V#GFj##s#C#j##s#H#+s#Is#Hs#F#SCl#Fs#KD#l#Gs#MD#l#Hs#Rs#O#l#*s#Ws#T#l#+s#^s#Y#l#,s#es#`#l#-s#ms#g#l#.s#oD#l#/s#qD#l#0s#vs#s#l#1s#{s#x#l#2s$&s#}#l#3s$,s$(#l#4s$2s$.#l#5s$4D#l#6s$7D#l#7s$=s$9#l#8s$Cs$?#l#9s$Ks$E#l#:s$Ss$M#l#;s$Zs$U#l#(s$bs$\#l#)s$ks$e#l#?s$qs$n#l#@s$vs$s#l#As(8s(5#l#<s$ys$z#l#=s(As(B#Ts%#C#*s%$C)C#(s%&C%$##Ds%(#%S%C,#s%+4s*JP5D##DO$m#$#2S(Ck##s*7s&Jk##s'c#3MC$Es(0k##s*;#k##s)9#2s$}C$Es$tk##s*?#k##s$~#%S)C,#s%<2#C$E$%PC,#s%@(#C$E#k##s*I#k##(#3s%,C$Es%-*s$wC$E#k##s*O#k##&#3-C$E.%RC,#s%N*#C$E#k##s*W#k##(#%S,C,#s%T-#C)C)(+C%$##D-#k##s*S#./C%S*C,#s%](#C$E#&$C'$#k##s*T#/(C%S+C,#s%e(#C&C#$$E'$#k##s*U#0(C%S-C,#s%m*#C#D#Ek##s*j#1&C%S$C,#s%s(#C#D#$k##s*p#*&C%S.C,#s%y(#C%S/S.-#C%SBS/*#C)C#(%C%$##D'#k##s*|#.)C%S1SB(#C$E#&$C'$#k##s*|#/(C%SGS1(#C&C#$$E'$#k##s*|#0(C%S7SG*#C#D#Ek##s+4#1&C%S<S7(#C#D#$k##s+9#*&C%S3S<(#C-S5C)Cs%,%#s%0#DS0#k##s+@#.S0C$Es%0&s%1C'$#k##s+>#/S9C(S:C&C#$$E'$#k##s+=#0S:C*S=C#D#Ek##s+P#1S=C(SCC#D#SCk##s+T#*SCC(SJC-SJC*SMC)C#(SMC%$##DSM#k##s+\#.SMC(S>C$E#&$C'$#k##s+[#/S>C(S;C&C#$$E'$#k##s+Z#0S;C*S6C#D#Ek##s+m#1S6C(S8C#D#S8k##s+q#*S8C(SKC$ESO&SOs,3'$#j###s+o&SIs,6$ESP&SLs,8$ESD&SDs,:'$#j###s+v&STs,=$ES4&SEs,?MS4NSEUS0S?US;SQ$ES=&S=C'$#USDMk##s,:s'vUSUO$ESBk##s,=#USTN's'ws)Xj###s,,&S-C's)ps)Vj###s,/&S0C$ES;'#s%bj###s,3&S6C$ES8&SKC&S4C'>#j###s,9&SEC$ES?&SQC9s+EJHHIs)as)`s)al#$#s+As+;l#%s)fs+H#l#&s+Ls+K#j#>D#&EGk##s)]#k#>D#ACSnl#''$#j#0-#j#:/#V#GFj##2#j##s#1#+s#275#Rj#19#j#3;#V#GFj##>#j##B#+s##s&&A#Lj#2s#%#j#7s(O#V#GFj##s(B#j##s*=#+s*>s*$s#+#Mj#8s#.#j#9s+h#V#GFj##s*:#j##s(M#+s(Ns*/s#4#Ol#Is#7s#8#l#As#;s#9#l#Js#>s#=#l#:s#Cs#@#l#3s#Es(R#l#,s#Gs*A#l#Ds#Is*F#j#Ks#K#j#Ls#M#V#GFj##s#P#j##s#U#+s#Vs#Us#S#S4j#Ms#X#j#Ns#Z#V#GFj##s#]#j##s#b#+s#cs#bs#`#SPl#Os#eD#l#Ps#gD#l#Qs#ls#i#l#Bs#qs#n#l#Cs#xs#s#l#Ds$#s#z#l#Es$+s$%#l#Fs$-D#l#Gs$/D#l#Hs$4s$1#l#*s$9s$6#l#+s$@s$;#l#,s$Fs$B#l#-s$Ls$H#l#.s$ND#l#/s$QD#l#0s$Ws$S#l#1s$]s$Y#l#2s$es$_#l#3s$ms$g#l#4s$vs$o#l#5s$yD#l#6s$}D#l#7s%(s%##l#8s%/s%*#l#9s%8s%1#l#:s%As%:#l#;s%Hs%C#l#(s%Ss%L#l#)s%Zs%U#l#?s%cs%\#l#@s%js%g#l#As%os%l#l#Is%ss%q#l#Js)ns)k#l#<s%vs%w#l#=s)qs)r#WS~s%|C#(s%}C$E#&$C'$#%s-Ms+i(#C#DFEj#RD#%Fs-Q(#C#D#Ej#RD#%EF(#C#D#Ej#RD#5DE<DE$#s+vS#<DE)#s-[S)%OS%(#C4s-}S,5D##DN$m#$#2MC$Es-@k##s-k#k##s,i#3S#C$ES#$Es-Ck##s-p#k##%#2s([C$Es(\k##s-ts(Gk##$#%LC,#s(q2#C$E$(s%~C$E#k##s-|#k##&#3s(SC$Es(T$Es(Fk##s.%#k##%#3s&+C$Es&,*s&$C$E#k##s.+#k##&#-s&7C)C'%#s&)#Ds&+#k##s.$#.s&-C$Es&%&s&&C'$#k##s-~#/s&*C(s&#C&C#$$E'$#k##s-}#0s&(C#Ds%{Ek##s.3#1s&%C#Ds%{s%|k##s.6#*s%~C%S/C,#s)?(#C-s%~C*s%wC)C#%#s%x#Ds%z#k##s.?#.s%|C$Es%u&s%vC'$#k##s.=#/s%zC(s%tC&C#$$E'$#k##s.<#0s%yC#Ds%qEk##s.N#1s%wC#Ds%rs%sk##s.Q#*s%uC%S5S3(#C-S0C*S9C)C#%#s(E#DS9#k##s.Y#.S9C$Es%r&s%sC'$#k##s.W#/S:C(S=C&C#$$E'$#k##s.V#0S=C#Ds%pEk##s.h#1SCC#Ds%rSJk##s.k#*SJC-SMC*S>C)C#%#s%o#DS>#k##s.q#.S>C$Es%m&s%nC'$#k##s.o#/S;C(S6C&C#$$E'$#k##s.n#0S6C#Ds%kEk##s/$#1S8C#Ds%mSKk##s/'#*SKC(SOC&S/C's,k#j###s/+&SBCj##s%ks/-$ESQ&SQs/J'$#j###s/1&SXs/M$ESV&SFs/ODSV?SF&S.C's.L#ES@'s+.s(gFSRUS?MUSEOk##s/Ks,yUSQN&S$C's-*#j###s/B$ES9&S9C'$#j###s/F&S:C&SCC&SOC's&5#j###s/K&SIC&SLC$ESX&SXC'$#j###s/Q&SVC$ESF&S@CACS[l#'s,js,e#j#0%#j#:'#V#GFj##*#j##/#+0/-#Rj#12#j#3s&D#V#GFj##6#j##s&L#+s&M;9#Lj#2=#j#7s&=#V#GFj##A#j##s#&#+s#'s#&s#$#Mj#8s#?#j#9s-O#V#GFj##s#7#j##s-V#+s-Ws#0s#.#Ol#Is#2s#3#l#As#5s#4#l#Js#7s.w#l#:s#9s)A#l#3s#<s#;#l#,s#@s#>#l#Ds#Bs-C#j#Ss#D#j#Ts#F#V#GFj##s#I#j##s#N#+s#Os#Ns#L#SVj#Ks&Z#j#Ls&\#V#GFj##s&_#j##s&d#+s&es&ds#V#S4j#Ms-H#j#Ns/9#V#GFj##s#[#j##s-k#+s-ls#`s#^#S;l#Os#bD#l#Ps#dD#l#Qs#hs#f#l#Bs#ls#j#l#Cs#ss#n#l#Ds#ys#u#l#Es$$s#{#l#Fs'8D#l#Gs$'D#l#Hs$+s$)#l#*s$/s$-#l#+s$6s$1#l#,s$<s$8#l#-s$Cs$>#l#.s$ED#l#/s$HD#l#0s$Ls$J#l#1s$Ps$N#l#2s$Ws$R#l#3s$]s$Y#l#4s$ds$_#l#5s$fD#l#6s$jD#l#7s$ns$l#l#8s$rs$p#l#9s$ys$t#l#:s%#s${#l#;s%)s%%#l#(s%0s%+#l#)s%6s%2#l#?s%=s%8#l#@s%Ds%A#l#As%Js%F#l#Is%Os%L#l#Js+Os+L#l#<s%Rs%S#l#=s+Rs+S#XT9OS%C#<Ds%hs%fs%[s%Y##Ds%ZE4s0yR5D##DS($m#$#2S#C$Es08k##s0g#k##s%X#3S)C$Es.^k##s0k#k##s.3#2s+NC$Es+;k##s0o#k##s)&#2s)-C$Es(sk##s0s#k##s)$#3s+CC$Es+D$Es+5k##s0x#k##%#3s)(C$Es))*s(oC$E#k##s0~#k##&#-S*C)Cs._%#s0;#DS+#k##s0w#.S+C$Es.c&s.dC'$#k##s0u#/S-C&Cs,{$s,|E'$#k##s0s#0S$C*S.C#D#Ek##s1*#1S.C#Ds+DS/k##s1-#*S/C(SBC%S1C,#s,7-#C%SGC,#s,:*#C)C#(%C%$##D'#k##s19#.)C%S7C,#s,C(#C$E#&$C'$#k##s1:#/(C%S<C,#s,K(#C&C#$$E'$#k##s1;#0(C%S3C,#s,S*#C#D#Ek##s1P#1&C%S5C,#s,Y(#C#D#$k##s1V#*&C%S0C,#s,_(#C%S9S0-#C%S:S9*#C)C#(%C%$##D'#k##s1b#.)C%S=S:(#C$E#&$C'$#k##s1b#/(C%SCS=(#C&C#$$E'$#k##s1b#0(C%SJSC*#C#D#Ek##s1v#1&C%SMSJ(#C#D#$k##s1{#*&C%S>SM(#C-S>C*S;C)C#%#s({#DS;#k##s2'#.S;C$Es%k&s%lC'$#k##s2%#/S6C&Cs(z$s({E'$#k##s2##0S8C#Ds%jEk##s25#1SKC#Ds%lSOk##s28#*SOC(SIC)S1C,Cs-B%$#%SUC,#s-E#D%#j##s+s#$EST'#s(~)S3C%#+%SEC,#s-M#D%#j##(#&S4s2d$ESE&S?s2f's%\s%x)S:C%#5%SVC,#s-W#D%#j##(#&SVs2n&S@s2oDSF?S@ESRFSN$ESKk##s2g#)SIC%#s##%SYC,#s-e#D%#j##s%}#)SDC%#s#)%SoC,#s-k#D%#j##s&##)S?C%#s#/%SnC,#s-q#D%#j##s&$#)SFC%#s#5%SfC,#s-w#D%#j##s&$#KT#K#K#LD#LD&LDT#=D$#=D&#I#S\UT:SaVT;D#OD#*OD$*=D#*=D%#I#S\8SS#s2,8SS+#JDQ>D#Ks2-JDS'>D$G#HDs3X6D#SHs2.7s20JHHI#S&ZS}s21JHHI#UT$SaHD#WSpD(s0RHDs3^BD$#6D&SH#7s28JHHI#S&9s29JHHI*s0T#6Ds29SZ.7s2;JHHI#S&6D)SHs2;7s2=JHHI#S&WSpDs0\2SDs.EPD4#BD%#BD16PD#&6D%SH#7s2EJHHI#S&9s2FJHHI+s0a#9s2GJHHI.s0b#9s2HJHHI1s0c#l#$#s2Ds2>l#%?s2K#l#&s#$s2N#j#>D#j#UD#j#VD#j#WD#)KG%#Q#DS'#k##s0c#&EK#DS%E)S'Q,Qs.]%$#%S%Q,#s.`#D%#k##)#k##+#k##-#k#>D#k#UD#k#VD#k#WD#[FSNSqCSAS]SgSrl#'7$#j#0s&n#j#:s&p#V#GFj##s&s#j##s&x#+s&ys&xs#U#Rj#1s&{#j#3s*Q#V#GFj##s'##j##s*Y#+s*Zs'(s#a#Lj#2s'*#j#7s*J#V#GFj##s'.#j##s'3#+s'4s'3s#m#Mj#8s'L#j#9s1\#V#GFj##s'D#j##s1c#+s1ds'=s#y#Ol#Is'?s$$#l#As'Bs$%#l#Js'Ds3(#l#:s$)s-N#l#3s$+s'H#l#,s$-s'K#l#Ds$/s1P#j#Ss$1#j#Ts'3#V#GFj##s$5#j##s';#+s'<s'Xs$8#SFj#Ks$@#j#Ls$B#V#GFj##s$E#j##s$N#+s$Os*ns$H#SEj#Ms-d#j#Ns1h#V#GFj##s1\#j##s1^#+s1_s/~s$V#S6l#Os$^D#l#Ps$`D#l#Qs$ds$b#l#Bs$hs$f#l#Cs$ns$j#l#Ds$ts$p#l#Es${s$v#l#Fs$}D#l#Gs%$D#l#Hs%*s%&#l#*s%0s%,#l#+s%8s%2#l#,s%@s%:#l#-s%Is%B#l#.s%LD#l#/s%PD#l#0s%Ws%R#l#1s%^s%Y#l#2s%gs%`#l#3s%ps%i#l#4s%zs%r#l#5s%~D#l#6s&$D#l#7s&(s&&#l#8s&-s&*#l#9s&3s&/#l#:s&9s&5#l#;s&?s&;#l#(s&Fs&A#l#)s&Ls&H#l#?s&Qs&N#l#@s&Vs&S#l#As&[s&X#l#Is&`s&]#l#Js-4s-2#l#<s&cs&d#l#=s-7s-8#)s2wC%#s%&%NC,#s/h#D%#*S(C)#C%#s%,*FC)#C#D#Mj#RD#%S(C,#s/r(FC$E#&$C'$#j#RD#<D(#K.F(/C$E#&$C'$#%MC,#s/~)C4%#/#DF#j#RD#)s4gC%#s%D<D)%Q#G*$C)C#(&C%$##D(#*s%KC%s4i#)FC#D#S)j#RD#)s4mC%#s%Q*#C)s33C%#s%T)CF($C%$##D&#j#RD#4s5\S*5D##DM$m#$#4s5`S-5D##DS)$m#$#2S)Ck##s5Ms4uk##s2q#2PC$Es39k##s5Q#k##s12#3S,C$Es4jk##s5U#k##s2p#2s/zC$Es/{$Es/qk##s5Z#k##%#)s4rC%#s%s2#C$E$)s1TC%#s%w(#C$E#k##s5d#k##(#)s3DC%#s%}3#C$E$)s1WC%#s&%*#C$E#k##s5n#k##(#%S-S+3#C$E$%S.S$*#C$E#k##s5v#k##'#%S$S--#C)C((*C%$##D,#k##s5q#..C(s-]C$E#&$C'$#k##s5p#/s-bC&Cs-^$s-_E'$#k##s5n#0s-eC#Ds*EEk##s6$#1s-`C#Ds-Ys-Zk##s6'#*s-\C-S<C*S3C)C#%#s0'#DS3#k##s6-#.S3C(S5C$E#&$C'$#k##s6,#/S5C&Cs0'$s0(E'$#k##s6*#0S0C#Ds*CEk##s6<#1S9C#Ds-TS:k##s6?#*S:C)GC%#s&d-#C)KC%#s&g*#C)C#(%C%$##D'#k##s6J#.)C)S'C%#s&p(#C$E#&$C'$#k##s6K#/(C)QC%#s&x(#C&C#$$E'$#k##s6L#0(C)S%C%#s'$*#C#D#Ek##s6a#1&C)OC%#s'*(#C#D#$k##s6g#*&C)NC%#s'0(#C-S8C)Cs*G%#s-Y#DSK#k##s6o#.SKC$Es*K&s*LC'$#k##s6m#/SOC&Cs'?$s'@E'$#k##s6k#0SIC*SPC#D#Ek##s6~#1SPC(SLC#D#SLk##s7&#*SLC(SUC&NC's3S#j###s7*&S#C's-Hs'?j###s7-$ES@'#s'9j###s70&SRs7L$ESN&SAs7NDSN?SAES^FSWk##s7Es0|ACSbl#'s4Ns4I#j#0s*E#j#:s*G#V#GFj##s*J#j##s*O#+s*Ps*Os*M#Rj#1s*R#j#3s.(#V#GFj##s*V#j##s.0#+s.1s*[s*Y#Lj#2s*]#j#7s-}#V#GFj##s*a#j##s*f#+s*gs*fs*d#Mj#8s+##j#9s53#V#GFj##s*w#j##s5:#+s5;s*ps*n#Ol#Is*r=#l#As*u>#l#Js*ws6[#l#:As1%#l#3s##s*{#l#,s#%s*~#l#Ds#'s5'#j#Ss#)#j#Ts#+#V#GFj##s#.#j##s#2#+s#3s'is#1#SNj#Ks'k#j#Ls*q#V#GFj##s+6#j##s.$#+s.%s'xs#:#SXj#Ms#=#j#Ns6q#V#GFj##s5D#j##s48#+s49s#Es#C#S6l#Os#GD#l#Ps#ID#l#Qs#Ns#K#l#Bs#Ss#P#l#Cs#Ys#U#l#Ds#_s#[#l#Es#es#a#l#Fs#gD#l#Gs#kD#l#Hs#rs#m#l#*s#ys#t#l#+s$&s#{#l#,s$/s$(#l#-s$9s$1#l#.s+xD#l#/s$>D#l#0s$Bs$@#l#1s$Fs$D#l#2s$Ls$H#l#3s$Ss$N#l#4s$Zs$U#l#5s,=D#l#6s$]D#l#7s$as$_#l#8s$es$c#l#9s$ks$g#l#:s$rs$m#l#;s$ys$t#l#(s%&s$|#l#)s%0s%)#l#?s%;s%4#l#@s%Cs%?#l#As%Hs%E#l#Is%Ms%J#l#Js%Qs%O#l#<s%Ss%T#l#=s%Xs%Y#XT<s7uCs(X#ZSsDs%es%^Fs%k#)Cs%l(s%hC%$##Ds%j#%s7xF)#C#D#Lj#RD#4s8dS+5D##DS#$m#$#4s8hS$5D##DL$m#$#2LCk##s8Us6Ck##s5u#3s(mC$Es(n$Es&&k##s8Z#k##%#2RC$Es7rk##s8^#k##s4;#3S*C$Es4Uk##s8b#k##s6.#2s2}C$Es2~(s%LC$E#k##s8h#k##&#2s%gC$Es%h)s*:C%#s)'(#C$E#k##s8p#k##(#3s%XC$Es%Y*s0QC$E#k##s8v#k##&#-S.C)Cs*A%#s3*#DS/#k##s8o#.S/C$Es*E&s*FC'$#k##s8m#/SBC&Cs3)$s3*E'$#k##s8k#0S1C*SGC#D#Ek##s8~#1SGC#Ds3*S7k##s9%#-s0IC*s-2C)C#%#s-3#Ds-5#k##s9*#.s-7C%S0S5(#C$E#&$C'$#k##s9*#/(C(s*7C&C#$$E'$#k##s9)#0s*<C#Ds*:Ek##s9;#1s*=C#Ds*5s*6k##s9>#*s*8C-s)bC)Cs&v(s)dC%$##Ds)f#k##s9D#.s)hC$E'&(C'$#k##s9B#/s)mC&C,$-E'$#k##s9@#0s)rC#Ds'*Ek##s9R#1s)uC#D4s)vk##s9U#)RC%#s)y-#C)S*C%#s)|*#C)C#(%C%$##D'#k##s9_#.)C)S+C%#s*)(#C$E#&$C'$#k##s9`#/(C)S-C%#s*1(#C&C#$$E'$#k##s9a#0(C)S$C%#s*9*#C#D#Ek##s9v#1&C)S.C%#s*?(#C#D#$k##s9|#*&C)S/C%#s*E(#C-STC*S4C)C#(S4C%$##DS4#k##s:*#.S4C(SEC$E#&$C'$#k##s:)#/SEC(S?C&C#$$E'$#k##s:(#0S?C*SQC#D#Ek##s:;#1SQC(SXC#D#SXk##s:?#*SXC(SVC%S9E)#C#D#SRj##s%y#$ESA'#s%q%SJE)#C#D#SWj##&#&S^s:f$ESW&Scs:h$ES]&S]s:j'$#%S6E)#C#D#SYj##&#&SYs:p$ES_&Sds:rDS_?SdEStFSoUSESe$ESL'#s-oUSAS#k##s:ms:%USRNk##s:os1AUSAS(%S?E)#C#D#Sfj##s.1#'s4Us.#%SFE)#C#D#Sqj##&#&SJC$ESI'#s.%%SAE)#C#D#T=j##&#&SPC&SUC's.Es.&%S`E)#C#D#T>j##&#&SFC&SRC$ESY&SYC'$#%SdE)#C#D#T?j##&#&S_C$ESd&StC%SeS@VT%#S4#D$S4R#VT&$#m#&#Ks*vK#LD#ODs*q#=D#s*oI#S\=D&s*xI#S\8SS#s:>8SS&#JDS%>Ds*qK#>D#Gs*p6Ds:>Shs*o7s:@JHHI#S&6Ds:@Shs8_7s:BJHHI#S&9s:CJHHI%s8^#;s*pHD#6Ds:ESZ#7s:GJHHI#S&BDs8fs:GWSpD#s*y6D#SHs*u7s:KJHHI#S&9s:LJHHIs*ms8g#9s:MJHHI(s8h#9s:NJHHIs*qs8i#9s:OJHHI.s8j#9s:PJHHIs*us8k#l#$#s:Ls:Fl#%6s:S#l#&:s:V#j#>D#j#UD#j#VD#j#WD#j#XD#k##s;fs;f&ES'&EN#DNE%S%E)#O#D#Nk##&#k##(#k##*#k##,#k##s*o#k#>D#k#UD#k#VD#k#WD#k#XD#^FT@SuTACTBSfS1T'TCTDl#'5$#l#*s#=s#>#j#+s#D#j#:s#F#V#GFj##s#I#j##s#Q#+s#Rs#Qs#L#S$j#,s#T#j#3s'G#V#GFj##s#X#j##s/E#+s/Fs/'s#[#S*j#0s#a#j#1s#z#V#GFj##s#e#j##s#l#+s#ms/3s#h#Pj#2s#o#j#7s5g#V#GFj##s2Y#j##s5o#+s5ps/>s#u#S#j#8s9M#j#9s2X#V#GFj##s/`#j##s;@#+s;As/Ts$$#Nl#As$)s$*#l#@s$,s$+#l#Js$/s$.#l#:s$3s$1#l#3s$5s5]#l#,s$7s/W#l#Ds$9s/Z#l#Ms$;s9_#j#Ys$=#j#Zs$?#V#GFj##s$B#j##s$J#+s$Ks$Js$E#S_j#[s$M#j#\s$O#V#GFj##s$R#j##s$Y#+s$Zs'ls$U#SWj#]s'u#j#Ss;M#V#GFj##s9|#j##s8p#+s8qs'}s$a#SDl#^s$fD#l#_s$hD#l#Ts$ms$j#l#Ks$rs$o#l#Ls$ys$t#l#Ms%$s${#l#Ns%,s%&#l#Os%.D#l#Ps%2D#l#Qs%9s%4#l#Bs%@s%;#l#Cs%Is%B#l#Ds%Rs%K#l#Es%\s%T#l#Fs%sD#l#Gs*1D#l#Hs%ds%b#l#*s%hs%f#l#+s%ns%j#l#,s%ts%p#l#-s%{s%v#l#.s-OD#l#/s%~D#l#0s&&s&$#l#1s&*s&(#l#2s&1s&,#l#3s&9s&3#l#4s&@s&;#l#5s6fD#l#6s6nD#l#7s&Fs&D#l#8s&Ks&H#l#9s&Qs&M#l#:s&Ws&S#l#;s&]s&Y#l#(s&ds&_#l#)s&ms&f#l#?s&ts&o#l#@s&ys&v#l#As&~s&{#l#Is'(s'$#l#Js',s'*#l#<s'.s'/#l#=s'3s'4#-s)lC)Cs&l%#s)a#Ds4a#k##s<x#.s4cC$Es4_&s4`C'$#k##s<v#/s4fC&Cs4^$s4_E'$#k##s<t#0s4cC#Ds)_Ek##s=*#1s4_C#Ds1Cs4Yk##s=-#-S3C)Cs7$%#s)^#DS5#k##s=1#.S5C$Es7%&s7&C'$#k##s=/#/S0C&Cs7&$s7'E'$#k##s=-#0S9C#Ds)\Ek##s=?#1S:C#Ds1>S=k##s=B#)S(C%#s-f-#C)MC%#s-i*#C)C#(%C%$##D'#k##s=L#.)C)S#C%#s-r(#C$E#&$C'$#k##s=M#/(C)S)C%#s-z(#C&C#$$E'$#k##s=N#0(C)LC%#s.&*#C#D#Ek##s=c#1&C)PC%#s.,(#C#D#$k##s=i#*&C)S,C%#s.2(#C&s.4C's(%#j##s)H#j##s&,$j##s&#%k##s>#s4]j##s1='j##s%j(j##s%d)j##s%^*j##s%V+%S`S@VT%#S4#D$S4R#VT&$#m#&#PDs;As-B6Ds=#Sh#7s=%JHHI#S&6D%SZs;D7s='JHHI#S&[TEs=(JHHI%#9s=)JHHIs;Es;D#l#$#s=%s<{l#%s;Js=,#l#&s=0s=/#j#>D#,Gs94$E#&$G'$#k##s;D#k#>D#ACT'l#'*$#l#*67#j#+s%j#j#:s%l#V#GFj##s%o#j##s%w#+s%xs%wB#S$j#,s%z#j#3s)m#V#GFj##s%~#j##s1k#+s1ls1Ms#)#S*j#0s&+#j#1s&D#V#GFj##s&/#j##s&6#+s&7s1Ys#0#Pj#2s&9#j#7s81#V#GFj##s5##j##s89#+s8:s1ds#7#S#j#8s;s#j#9s4~#V#GFj##s2*#j##s=f#+s=gs1zs#>#Nl#As&Os#@#l#@s&Rs#A#l#Js&Us&T#l#:s&Ys&W#l#3s&[s8'#l#,s&]s1}#l#Ds&_s2$#l#Ms&as<)#j#Ys&c#j#Zs&e#V#GFj##s&h#j##s&p#+s&qs&ps#N#S_j#[s&s#j#\s&u#V#GFj##s&x#j##s'##+s'$s*6s#U#SWj#]s*?#j#Ss=s#V#GFj##s<F#j##s;:#+s;;s*Gs#\#SDl#^s'0D#l#_s'2D#l#Ts'7s'4#l#Ks'<s'9#l#Ls'Cs'>#l#Ms'Js'E#l#Ns'Rs'L#l#Os#gD#l#Ps#kD#l#Qs#rs#m#l#Bs#ys#t#l#Cs$&s#{#l#Ds$/s$(#l#Es$9s$1#l#Fs(=D#l#Gs,WD#l#Hs(.s(,#l#*s(2s(0#l#+s(8s(4#l#,s(>s(:#l#-s(Es(@#l#.s64D#l#/s69D#l#0s$Hs$F#l#1s$Ls$J#l#2s$Rs$N#l#3s$Xs$T#l#4s$^s$Z#l#5s6VD#l#6s6\D#l#7s$ds$b#l#8s$hs$f#l#9s$ns$j#l#:s$ts$p#l#;s$zs$v#l#(s).s))#l#)s)7s)0#l#?s)>s)9#l#@s)Cs)@#l#As)Hs)E#l#Is)Ns)J#l#Js)Rs)P#l#<s)Ts)U#l#=s)Ys)Z#WTFs/aC#<DEs)_s%*s,u#l#`s)hs)d#<Ds,vs,s#s,ps)jl#`s,~s,y#l#as-0s-,#ZSsDs-=s-9#s-7Fl#;s-Fs-A#*s-CC)#C#D#N3LC*S,C$E#k##s?Y#k##s<y#2s:0C(s:#C$E#k##s?^#k##s4>#2s7dCk##s?as7Zk##s4<#3s:*C*s9}C$E#k##s?f#k##s,m#3s7cC$Es7d$Es7Tk##s?k#k##%#-s:*C*s,\C)C#(s,^C%$##Ds,`#k##s?f#.s,bC&s)mC's)m#k##s?c#/s,^C&Cs,\$s,]E'$#k##s?a#0s,hC#Ds)hEk##s?s#1s7]C#Ds7Ys7\k##s?v#-s1EC*s1=C)C#%#s1>#Ds1@#k##s?{#.s1BC$Es1:&s1;C'$#k##s?y#/s1?C(s18C&C#$$E'$#k##s?x#0s1=C#Ds14Ek##s@.#1s1:C#Ds14s15k##s@1#*s17C%S9C,#s;:(#C-S:C)Cs7G%#s45#DS=#k##s@9#.S=C$Es7H&s7IC'$#k##s@7#/SCC&Cs7I$s7JE'$#k##s@5#0SJC#Ds7LEk##s@G#1SMC#Ds7HS>k##s@J#-S;C)Cs7?%#s42#DS6#k##s@N#.S6C$Es7@&s7AC'$#k##s@L#/S8C&Cs7A$s7BE'$#k##s@J#0SKC#Ds1$Ek##s@\#1SOC#Ds1&SIk##s@_#*SIC(SPC%SDSU#Ds1*#j##s::#'s7Cs0y%S?SE#Ds1%#j##%#'s47s0s%SFSV#Ds0{#j##%#DS@?SRESNFSA%S_SY#Ds0t#j##s43#%SeSo#Ds0q#j##s42#%SiSn#Ds0n#j##s40#%S[Sf#Ds0k#j##s4-#LDs0fODs0^#=D#s0d=Ds0_#I#S\=D's0g=Ds0j#I#S\8SS#s@-8SS'#>Ds(MS%s@->D#S's@.>Ds0`G#UT$sAWHD#6D#SHs@/7s@1JHHI#S&BDs0]s0[BDs0]&6D$SH#7s@5JHHI#S&6Ds0VSH&7s@7JHHI#S&9s@8JHHIs0[s>S#9s@9JHHI&s>T#9s@:JHHI+s>U#l#$#s@6s@0l#%1s@=#l#&5s@@#j#>D#j#UD#j#VD#j#WD#j#XD##DQE%S'Q%s0SS%#D$#%S%O#Ds0P#k##s(M#k##&#k##*#k#>D#k#UD#k#VD#k#WD#k#XD#\FSNSqSbCSASvS[TGl#'2$#j#0s4\#j#:s4^#V#GFj##s4a#j##s4f#+s4gs4fs#:#Rj#1s4i#j#3s8?#V#GFj##s4m#j##s8G#+s8Hs4rs#C#Lj#2s4t#j#7s88#V#GFj##s4x#j##s4}#+s4~s4}s#L#Mj#8s5:#j#9s?J#V#GFj##s52#j##s?Q#+s?Rs5+s#U#Ol#bs5-s5.#l#Js50s5/#l#cs52s@r#l#:s#\s;<#l#3s#^s56#l#,s#`s59#l#Ds#bs?>#j#Ss-B#j#Ts-F#V#GFj##s5B#j##s5D#+s5Es2%s#i#S@j#Ks5J#j#Ls88#V#GFj##s8X#j##s8Z#+s8[s25s#s#S?j#Ms;R#j#Ns?V#V#GFj##s?J#j##s?L#+s?Ms=ls#}#S8l#Os$%D#l#Ps$'D#l#Qs$+s$)#l#Bs$/s$-#l#Cs$5s$1#l#Ds$;s$7#l#Es$As$=#l#Fs9(D#l#Gs5|D#l#Hs$Gs$E#l#*s$Ks$I#l#+s$Qs$M#l#,s$Ws$S#l#-s$]s$Y#l#.s$_D#l#/s$cD#l#0s$gs$e#l#1s$ks$i#l#2s$rs$m#l#3s$xs$t#l#4s%#s$z#l#5s9wD#l#6s:$D#l#7s%)s%'#l#8s%-s%+#l#9s%3s%/#l#:s%8s%5#l#;s%@s%:#l#?s%Fs%B#l#@s%Ls%H#l#As%Ps%N#l#Is%Vs%R#l#Js%\s%X#l#bs/gs/e#l#cs7Ks7H#l#<s/ns/o#l#=s7Ns7O#%S(N*#C)#C#D#%VTHsBtsBtUS|#*s=CC)#C@F#CsBzF,%FCsB|#:sB|sB|%#US{+8,$#nS2#$##,)#%###$:sC$sC$S+S*8/#&#/%#j#RD#@S#FCsC*S#,FS#CsC,#:sC,sC,%#87#.nS2#$##7(#%###/#8#,j#RD#@Ms=b5S2F@S#s=\#S2#F@Ls=[#S2#FCsC8P,s=RPCsC:#:sC:sC:%#8s#%#<nS2#$##s#%G#%###=:sC=sC=S.S$8s#(#?#s#(%#k#d,#j#eS2#@S)s=p#S2#SmCsCEL,s=kLCsCG#:sCGsCG%#VSjs#2#:sCIsCIS$S-VSjs#4#k##s#4s#4USjs#6k##s#7$5#$WSksCOsCO-WSksCPsCPS$k##sCQs#;VSksCRsCRk##sCS$5#$GFGGGK##GF4S'K4S'G#D$#k##&#4KG4KF#D$#GS'##KGk##%#')#GQ##S'Kk##-#j##&#j##$Fj##/#WTIKGF+1+&$#j#f8#j#g:#j#hT(#k#f;/k#g=#k#hT(#VSwsCsP4sCtS/#DF#j#RD#4sCwS.WTJsCx#R4sCys#CVT)sCzP<D*'%$#XFsC|s#FS.#l#;0-#QsC}s#.s#-s#-s#;S$s#+#VSwsD#s#H#DF+j#RD#5D0#DS,1m#$#2S,Ck##sCns?lk##sA-#2S*Ck##sCqs5Ik##sA=#3S+C$Es?ak##sCu#k##sBp#2s0eC$Es0[k##sCy#k##s0f#2s;`C$Es;a$Es89k##sC~#k##%#3s0kC$Es0l$Es;\k##sD'#k##%#3s8BC$Es8C*s5LC$E#k##sD-#k##&#%SBC,#s?*-#C)C)(s5TC%$##Ds5V#k##sD)#.s5XC$Es5S&s5TC'$#k##sD'#/s5ZC&Cs5Q$s5RE'$#k##sD%#0s5VC*s5OC#D#Ek##sD8#1s5RC#Ds&qs5Kk##sD;#-s-mC*s5@C)C#%#s-i#Ds5C#k##sD@#.s5EC$Es5A&s5BC'$#k##sD>#/s5HC&Cs5@$s5AE'$#k##sD<#0s5EC*s5?C#D#Ek##sDO#1s5BC(s5<C#D#s5=k##sDS#-SIC)Cs07%#s&S#DSP#k##sDW#.SPC$Es08&s09C'$#k##sDU#/SLC&Cs09$s0:E'$#k##sDS#0SUC*SDC#D#Ek##sDf#1SDC(STC#D#STk##sDj#*STC%SQS?,#SQ#DS?#j##s8F#%S@SF,#S@#DSF#j##s&h#%S^SA,#S^#DSA#j##s-2#DSW?ScES`FS]%SuSe,#Su#DSe#j##s8?#%SvSi,#Sv#DSi#j##s8?#%SgS[,#Sg#DS[#j##s8>#%SxSb,#Sx#DSb#j##s8<#JDK>D#GsD3BDs4bsBPPD#s4c6DsBRSH#7sD5JHHI#S&l#$#sD1sD+l#%(sD8#l#&sD<sD;#j#>D#j#UD#%GF,#G#DF#k#>D#k#UD#ASySrl#')$#j#0s8K#j#:s8M#V#GFj##s8P#j##s8U#+s8Vs8U:#Rj#1s8X#j#3s<.#V#GFj##s8\#j##s<6#+s<7s8as#$#Lj#2s8c#j#7s<'#V#GFj##s8g#j##s8l#+s8ms8ls#.#Mj#8s9)#j#9sC9#V#GFj##s8}#j##sC@#+sCAs8vs#8#Ol#cs8xs8y#l#bs8{s8z#l#is8}sDa#l#:s#@s?+#l#3s#Bs9%#l#,s#Ds9(#l#Ds#FsC-#j#Ss-q#j#Ts-s#V#GFj##s-v#j##s-}#+s-~s14s#M#SWj#Ks17#j#Ls1;#V#GFj##s97#j##s99#+s9:s5vs#W#S@j#MsC2#j#NsE##V#GFj##s9E#j##sCU#+sCVs9Js#a#SLl#Os.MD#l#Ps#gD#l#Qs#ls#i#l#Bs#qs#n#l#Cs#ws#s#l#Ds#}s#y#l#Es$'s$##l#Fs6BD#l#Gs6DD#l#Hs6Hs6F#l#*s6Ls6J#l#+s6Rs6N#l#,s6Xs6T#l#-s6_s6Z#l#.s6fD#l#/s6lD#l#0s$5s$2#l#1s$:s$7#l#2s$@s$<#l#3s$Fs$B#l#4s$Ms$H#l#5s76D#l#6s7=D#l#7s$Ss$Q#l#8s$Xs$U#l#9s$^s$Z#l#:s$ds$`#l#;s$ks$f#l#@s$ts$o#l#As$zs$v#l#Is%$s$|#l#Js%)s%&#l#bs%.s%+#l#cs%2s%0#l#is%6s%4#l#<s%8s%9#l#=s0Rs0S##DLs&)VSwsFaF#D#s%Lj#RD#,s@vS,ZSsDP$s%K#Fl#;)(#4sFgs&/VT)sFhs&1<Ds%Hs%F%$#XFsFjs&2S$#l#;s%Zs%W#QsFks&Us%zs%ys&'S-s%L#Qs&Vs&#s%~s%~s&'s&%s%|#5s&Vs&NQs&Ws&Ws&(s&&s&Os&O$#j#ds&.##S2s&0Sl@GF#S2#Sl$GKk##$#$FG@KG#S2#Slk##%#''#$KS'k##&#j##%#@S'K#S2#Slk##.#j###Gj##/#VTKGF+1-)$#j#jD#j#kD#k#jD4k#kD#WFPsAFG$sAGP5Ds%r#DPs%sm#$#4sG2SB5D##DR$m#$#2S+C$EsBkk##sF|#k##sEw#3S-C$Es8Mk##sG$#k##sF9#2s3hCk##sG's3`k##s0o#2s>dC$Es>e(s%YC$E#k##sG-#k##&#3s>hC$Es>i$Es;Gk##sG2#k##%#3s%bC$Es%c$Es8Sk##sG7#k##%#-SPC)Cs2e%#s2i#DSL#k##sG0#.SLC$Es2i&s2jC'$#k##sG.#/SUC(SDC&C#$$E'$#k##sG-#0SDC#Ds%1Ek##sG?#1STC#Ds/wS4k##sGB#:sGfsGfS^SA8s'Q#s'H#s'Qs'I#j##s:y#'s:Qs:p:sGksGkS]S`8s'V#s'M#s'Vs'N#j##&#$ESR&SNsGg$ES^'#s/a:sGssGsStSd8s'^#s'U#s'^s'V#j##&#&SWsGn$ESc&S`sGpDSc?S`ES]FSY:sG~sG~SgS[8s'i#s'`#s'is'a#j##s:z#:sH&sH&SxSb8s'm#s'd#s'ms'e#j##s:z#:sH*sH*SySr8s'q#s'h#s'qs'i#j##s:y#:sH.sH.T*TL8s'u#s'l#s'us'm#j##s:w#>Ds%=KsFm>D#KsE/BDs7:s7<6D#Shs7;7sFoJHHI#S&6DsFoSZs7?7sFqJHHI#S&ZTMsFrJHHIQ9sFsJHHI$sE2#9sFtJHHI'sE3#l#$#sFpsFjl#%,sFw#l#&sF{sFz#j#>D#j#UD#j#lT+#$s%BGk##s>4Qk##$#k#>D#k#UD#k#lT+#:sHHsHHTNTO8s(3#s(*#s(3s(+#YF#TPSySiT*l#'-'#j#0s;3#j#:s;5#V#GFj##s;8#j##s;=#+s;>s;=s###Rj#1s;@#j#3s>r#V#GFj##s;D#j##s>z#+s>{s;Is#-#Lj#2s;K#j#7s>k#V#GFj##s;O#j##s;T#+s;Us;Ts#7#Mj#8s;m#j#9sE}#V#GFj##s;e#j##sF(#+sF)s;^s#A#Ol#cs;`s;a#l#bs;cs;b#l#is;esGI#l#:s#IsAo#l#3s#Ks;i#l#,s#Ms;l#l#Ds#OsEq#j#Ss#Q#j#Ts#S#V#GFj##s#V#j##s#]#+s#^s0`s#Y#Scj#Ks#`#j#Ls#b#V#GFj##s8[#j##s;]#+s;^s;}s#g#SRj#MsEv#j#NsGg#V#GFj##s<-#j##sF=#+sF>s<2s#r#SUl#Os10D#l#Ps18D#l#Qs#{s#y#l#Bs$#s#}#l#Cs$*s$%#l#Ds$0s$,#l#Es$6s$2#l#Fs*_D#l#Gs*aD#l#Hs*es*c#l#*s*is*g#l#+s*os*k#l#,s*us*q#l#-s*{s*w#l#.s9ID#l#/s9LD#l#0s9Rs9N#l#1s9Xs9T#l#2s9`s9Z#l#3s9hs9b#l#4s9qs9j#l#5s9tD#l#6s9xD#l#7s:#s9z#l#8s:*s:%#l#9s:3s:,#l#:s:<s:5#l#;s:Fs:>#l#@s$Qs$M#l#As$Ws$S#l#Is$^s$Y#l#Js$bs$`#l#bs$gs$d#l#cs$ls$i#l#is3/s3,#l#<s$os$p#l#=s$ts$u#l#ds$ys$x#l#;s$}s${#j#ds%7#XTQs(gs%9#GU#Fl#ds(xs(v#l#es(zS2#*sD#C)#C<DsD%s(~%#F*s6pC)#C<DMs).%#Gl#ms)Cs)?#l#ns,Js,G#l#os;>s;=#l#as>Os>K#l#`sAusAp#l#psDCsD>#l#qsEpsEk#l#rsGdsI0#l#ssIPD#l#tsIQD#l#usIXsIS#l#vsIYsIT#VTRQS':sIasIaQS'8s)L#s)C#s)L%#m#'#j#wsI`#j#xsIc#j#ysId#j#hsIh#j#zsIi##"). Qed.

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
Scheme kc__5 := Elimination for Corelib.Init.Logic.False Sort Prop.

Lemma lazy_ranges_okb_vm_add : forall segs L a n,
  lazy_ranges_okb segs L = true ->
  lazy_range_okb segs (a, n) = true ->
  lazy_ranges_okb segs (lazy_interior a n ++ L) = true.
Proof.
  ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.lazy_ranges_okb); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.lazy_range_okb); constr:(@Corelib.Init.Datatypes.pair); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.lazy_ranges_okb_app); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.lazy_interior); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.segs_nowrapb); constr:(@Stdlib.Lists.List.forallb); constr:(@Corelib.Init.Logic.and_ind); (KReplay.sort_at constr:(@Stdlib.Lists.List.partition) [0]); constr:(@Stdlib.Lists.List.In); constr:(@Stdlib.Lists.List.forallb_forall); constr:(@kc__1); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.seg_disjoint_rangeb); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@kc__4); constr:(@Corelib.Init.Datatypes.cons); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@kc__3); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.LazyLedger.lazy_range_okb_within); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@stdpp.bitvector.definitions.bv_wrap_small); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.AND); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@kc__5); constr:(@Corelib.Init.Datatypes.false)|] [|@L2; @L1; @segs; @b2; @b1; @H0; @H; @HL; @x; @l; @f; @A; @p; @seg; @m; @n; @Hr'; @_H; @Hr; @Ha; @__ff; @__varmap; @__wit; @__arith; @H12; @H11; @H10; @H9; @r0; @q0; @H8; @H7; @H6; @H5; @H4; @r; @q; @H3; @H2; @H1; @__sat0; @__sat1; @heq_lo; @heq_sz; @__x1; @__sat3; @__sat2; @H14; @H13; @__sat5; @__sat4; @Hin; @E; @b; @e; @z; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @H16; @H15; @heq_lo'; @heq_hi'; @__x8; @__x9; @__x10; @b0; @hi'; @lo'; @Hm''; @Hhi'; @Hm'; @Hlo'; @Hps; @sz; @lo; @Hnw; @Hnr; @Har; @a; @L|] "#<G$&%.$P$X$h$G##$i$g#$$1$3#%$m#(#&#)#+#,#*#'#-#6$w#.#/%9#4#5#7#O#8#0$l#3#<$b#@#2#1#>#F$*#:#9#A#G#S#?#U#;#=#D#M$x#B#L#E#N#f#d%3$/#I#H#j#W#_#[#b#c#q$v${#P%*%6#p#o#i#V%'$+$7$<$>$V$]#C#Q#J#T#R#a#e$A$T$a%&#\#r%/%=%:%>$0%?$;$4$-$,$9$=$@$C$E$J$M$Q$S$U$Y$c$d$f$n$p$q$o$u%#%%#K#n#]#^#y#}%2%1$%%;%<#m#Z#x#|$$%(%$%@$|$D$F$I$L$8$6$W$s$j$e$\$[$H$5$Z$~%,$.$R%4%-$^$_$`%.$?$t$}$2$B%7%8$r$K$y$z%0%+%)$:%5$)$N$O$kU$.&$^%$_%$`%$a%$b($c%$d+$e'$f*$g%$h%$i%$j'$k%$l%$m&$n$$o%$p'$q%#w%#x%$r%$s%$t%$u$$1%$v&$w%$x&$y%$z&${&$|&$}%$~%%#%%$%%%&%&%%')%(%#'&%)$%*$$1$%+$%,%%-%PS;4SO4#4#4#4#4#US~#UT##VSc##P#BPM#K#L0''MJ>S%##K#LWSd)JGBM##K#LBPJ#K#L'+#k##&#BMJ#K#LBMG#K#L'%#WSd5MJBP##K#Lk##&#',#WSd:PMBS%##K#Lk##1#j##'#j##$Gj##3#WT$MJG(5,&$#j#$B#j#%s###j#&s#.#k#$s#%0k#%s#&#k#&s#1#MS%PBQ##K#LBQO#K#LVSeJG#K#L#KML#KJL'$#k##&##KGL'&#VSeMJ#K#Lk##%#'(#VSePM#K#Lk##,#j##&#j##$Gj##.#VT%JG(0+&$#j#'K#j#(K#k#'K.k#(K#USfS$QS$MOS%?s#I$##K&L#K$L#KPL'#?k##9#j##8#j##6Jj##@#(A<%#4j#'K#j#(K#k#'Ks#$k#(K#USfRQR?s#Y#S$N%#S%#K&L#K%L'$#USfS##K#LQS#?s#a#R#K#LQS&?s#d#S##K#Lj#)#Jj#**#YT&+(+#Gl#+1.#l#*86#k##GKPJ?MJG#K#LCS%GMUS%J#K#Lk##%#k#,P#k##(#CPGJUPJ#K#Lk##%#k#,M#?PMJ#K#Lk##%#'+#?S%PM#K#Lk##/#j##&#j##$Gj##1#WT'MJG(3+&$#j#-<#j#.>#j#/Sp#k#-?/k#.A#k#/Sp#MQOMRS$Cs$2G#>S)J#K#Lk##%#j#0s$6#0s$8s$8JGMS)S&Cs$9$#VT(s$<S*/s$=S*$F#UT)s$?%%#'%#/s$BS7/s$CS8&$#Rs$KRs$GVT*$#G&#0s$Hs$HS3S7SG#j#1S;#?S;#S,N'#S*#K(L#K%L'$#/s$QS3&#2G#.#K#L0s$Ts$TS,S3SG#j#1S;#?S;#S-#K#L'(#/s$[S,&#-$#8j##&#0s$^s$^S-S,SG#j#1S;#?S;#S'#K#L/s$dS-&#,G#A#K#L0s$gs$gS.S'SG#j#1S;#?S;#S0#K#LGJG#K#L$MJk##$#$JGGMJ#K#Lk##%#''#$PMk##&#j##%#GPM#K#Lk##.#j###Jj##/#VT+JG(1-)$#j#2C#j#3C#k#2C4k#3C#/s%(S0/s%)S.&$#N#s#BM$$s#Cl#4$#Gl#*+)#j#5A#j#4s#'#V#JGj##s#-#j##s#=#(s#>s#9s#4#Gl#6s#Fs#C#l#*s$>s$<#/s%7S1&s#S#$#s#P5Cs#G#CGs#Hm#$#5Cs#7#CMs#8m#$#VT,s#Ys#X%Fs#Z$Fs#Z%Fs#Zk##$#k##&#$Fs#_WT-s#`s#_Jj##Sq#j#7%#$Fs#ak##Sq#k#7(#&ODRSO)$#8#D#CDFUT.#&QD)#(.#D1D#-%D&$##C'#k##*#9)D%FD&S$D)#2-#D$F#%$D'$#k##)#:(D%DF&RD)#;-#D%D#$$F'$#k##)#;(D&S#D)#s##.#D#C#Fk##s###<&D&S&D)#s#)-#D#C#$k##s#)#.&D&S)D)#s#/-#D&S*S)8#D&S1S*.#D1D#-%D&$##C'#k##s#5#9)D&S8S1-#D$F#%$D'$#k##s#2#:(D&S7S8-#D%D#$$F'$#k##s#0#;(D&S3S7.#D#C#Fk##s#I#<&D&S,S3-#D#C#$k##s#N#.&D&S-S,-#D$FS-%S-s$]'$#4s&I4#4#4#4#4#R#%F#j##+#%S's$h$FS.%S0s$j$FS<%S<s$l'$#j###*%SCs$o$FS4%SDs$qUSrS5PS5UT/CUT0CUT1CTCFTC5+C$S2#,&IEEH#NVT2'H5KLVT3GM#K#Lm$%#WT4CFJXT5GM$#l#8*)#l#910#l#:43#l#;#AGj#<7#j#=9#V#JGj##<#j##A#(BA?#SDj#>s#$#j#?s#&#V#JGj##s#)#j##s#6#(s#7s#6s#,#S0l#@s#9C#l#As#<C#l#Bs#Bs#>#l#Cs#Hs#D#l#Ds#Ps#J#l#Es#Xs#R#l#Fs#as#Z#l#Gs#dC#l#Hs#hC#l#Is#os#j#l#Js#vs#q#l#Ks$$s#x#l#)s$.s$&#l#*s$:s$0#l#Ls$Bs$?#l#Ms$Ls$G#l#Ns$Ns$O#l#Os$Rs$S#m##s$3&MD)#s$C5Cs%7#CJs%8m#$#/s'7S'5C##CP$m#$#8s$ED.s$<D1D#&#s$=#Cs$?#k##s$L#9s$AD$Fs$8%s$9D'$#k##s$G#:s$=D-s$6D%D#$$F'$#k##s$D#;s$;D#Cs$2Fk##s$[#<s$8D#Cs$2s$3k##s$^#.s$5D&S*D)#s$d-#D8s$5D.s$.D1D#&#s$/#Cs$1#k##s$g#9s$3D$Fs$,%s$-D'$#k##s$b#:s$1D-s$+D%D#$$F'$#k##s$_#;s$0D#Cs$(Fk##s$v#<s$.D#Cs$)s$*k##s$y#.s$,D&S'S--#D$FS''#s#~j###s$~%S.s&.$FS0%S=s&0$FSC'#s#}j###s%(%S4s&4$FSD%S9s&6US1SD$FR%RD'$#US0S9$FS3%S3D'$#US4SA$FS)%S)D'$#j###s%8%S*D$FS1%S8D$FS=%S=D'$#j###s%?%S<D%S4DFCJ@CSO+Cs$6S2#,s$8IEEH#NUT6E+C&S(s$9,s$;IEEH#NZSYs$<IEEH#*s$=IEEH'&#l#8#s$9s$3l#9,s$@#l#:s$Ds$C#j#PC#%FG#CJFk###SGk##%#k#PC#VGDSPl#;)$#j#I7#j#)s#3#V#JGj##;#j##@#(A@>#Oj#Js###j#Ks#%#V#JGj##s#(#j##s#-#(s#.s#-s#+#Ml#Ms#0s%p#l#)s#5s#2#l#Es#:s#7#j#<s#<#j#=s#>#V#JGj##s#A#j##s#E#(s#Fs$ds#D#S9j#>s#H#j#?s#J#V#JGj##s#M#j##s#Q#(s#Rs$qs#P#S=l#@s#TC#l#As#WC#l#Bs#[s#Y#l#Cs#_s#]#l#Ds#fs#a#l#Es#ls#h#l#Fs#ss#n#l#Gs#uC#l#Hs#yC#l#Is#}s#{#l#Js$%s$##l#Ks$,s$'#l#)s$2s$.#l#*s$9s$4#l#Ls&,s&)#l#Ms&6s&1#l#Ns$=s$>#l#Os$Bs$C#WSgs$FD#.s$GD1D#-s$ID&$##Cs$K#&PD)#s&25Cs&X#CS%s&Ym#$#Hs&&D$Fs&'$FD$Fs$@k##$#k##&#Is&#D$Fs&$$Fs%ok##)#k##%#8s%|D1Ds%s&#s%w#Cs%y#k##s&A#9s%{D$Fs%u%s%vD'$#k##s&<#:s%zD%Ds$E$s$FF'$#k##s&8#;s$JD&S1D)#s&R.#D#C#Fk##s&R#<&D&S8D)#s&X-#D#C#$k##s&X#.&D&S7D)#s&^-#D8s%uD1Ds%m&#s%q#Cs%s#k##s&`#9s%uD$Fs%p%s%qD'$#k##s&[#:s%uD%Ds$J$s$KF'$#k##s&W#;s$OD&S.S'.#D#C#Fk##s&p#<&D&S0S.-#D#C#$k##s&u#.&D&S=S0-#D's$>s$Uj###s&o$FS9'#s$Rj###s&r%SAs(,$FS6%S>s(.US1S6US0S>US9SHj##s$Ns&yj##s$Hs&z*s%xIEEHs$Bs$As$Bl#8#s%ts%nl#9s$Gs%{#l#:s&#s%~#j#PC#%FJk##s$>#k#PC#VGDSIl#;'$#j#Is$P#j#)s$l#V#JGj##s$T#j##s$Y#(s$Zs$Y2#Oj#Js$\#j#Ks$^#V#JGj##s$a#j##s$f#(s$gs$f9#Ml#Q;s'M#l#)=s$k#l#E?s$p#j#<A#j#=s###V#JGj##s#&#j##s#*#(s#+s$zs#)#S>j#>s$}#j#?s%%#V#JGj##s&H#j##s$n#(s$os%*s#2#S4l#@s#5C#l#As#8C#l#Bs#>s#:#l#Cs#Ds#@#l#Ds#Js#F#l#Es#Ps#L#l#Fs#Vs#R#l#Gs#XC#l#Hs#\C#l#Is#cs#^#l#Js#js#e#l#Ks#ps#l#l#)s#vs#r#l#*s#|s#x#l#Ls$&s#~#l#Ms$-s$(#l#Rs'gs'd#l#Qs'qs'l#l#Ns$1s$2#l#Os'ts'u#WShs$6D#-s$7D$F#%$D'$#&S%P5Cs(6#COs(7m#$#Hs'VD$Fs'Hk##s$;#k##s$7#Is'RD$Fs'S$Fs%qk##s$@#k##%#8s'QD1Ds%u&#s'L#Cs'N#k##s'x#9s'PD$Fs%w%s%xD'$#k##s's#:s%|D-s$3D%D#$$F'$#k##s'p#;s$8D#Cs$/Fk##s(+#<s$5D#Cs$/s$0k##s(.#.s$2D&S3D)#s(4-#D8s'FD1Ds%t&#s'B#Cs'D#k##s(6#9s'FD$Fs%w%s%xD'$#k##s(1#:s%|D-s$/D%D#$$F'$#k##s(.#;s$4D#Cs$,Fk##s(E#<s$2D#Cs$-s$.k##s(H#.s$0D&S<S=-#D$FS$%S$D'$#j###s(N$FS#%S&Dj##s$4s(Q$FSi%Sis)^'$#j###s(U%SEs)a$FSJ%S:s)cUS,SJ$FS*'#s&$US4S:%S.D's'^#USHS?$FS7%S7D'$#j###s(c$FS,%S-D%SDD's&?#j###s(h%S9D$FSA%S6DVGDSjl#;s%}s%x#j#I%#j#)'#V#JGj##*#j##s&J#(s&K/-#Oj#J1#j#K3#V#JGj##s&G#j##:#(;:8#Ml#Q=s),#l#)A?#l#Es#%s###j#Ss#'#j#Ts#)#V#JGj##s#,#j##s#1#(s#2s#1s#/#S:j#<s$b#j#=s$d#V#JGj##s$g#j##s$k#(s$ls&_s#9#S>j#>s#;#j#?s#=#V#JGj##s&`#j##s#D#(s#Es#Ds#B#S.l#@s#GC#l#As#JC#l#Bs#Ns#L#l#Cs#Rs#P#l#Ds#Ys#T#l#Es#_s#[#l#Fs#es#a#l#Gs#gC#l#Hs#kC#l#Is#os#m#l#Js#ss#q#l#Ks#zs#u#l#)s$$s#|#l#*s$*s$&#l#Ls$0s$,#l#Ms$5s$2#l#Rs)Ls)I#l#Qs)Vs)Q#l#Ns$9s$:#l#Os'^s'_#WSgs$>D#.s$?D1D#-s$AD&$##Cs$C#&OS%/s,BS=5C##CQ$m#$#&S#RH#D$F$&S)S&-#D$F#k##s&&#k##'#Hs)7D$Fs)8k##s&*s$@k##$#I+D$F,$Fs)2k##s&/#k##%#Is'aD$Fs'b$Fs%kk##s&4#k##%#8s%xD1Ds%o&#s%s#Cs%u#k##s)l#9s%wD$Fs%q%s%rD'$#k##s)g#:s%vD%Ds$D$s$EF'$#k##s)c#;s$ID&S,D)#s)}.#D#C#Fk##s)}#<&D&S-D)#s*'-#D#C#$k##s*'#.&D&S'D)#s*--#D8s%yD1Ds%q&#s%u#Cs%w#k##s*/#9s%yD$Fs%t%s%uD'$#k##s**#:s%yD%Ds$J$s$KF'$#k##s*&#;s$OD&SCS<.#D#C#Fk##s*?#<&D&S4SC-#D#C#$k##s*D#.&D&SDS4-#Dj##s$Xs*=$FS>'#s&(j###s*@%SHs+V$FS:'#s$Sj###s*D%S?s+Z$FSQ%SPs+\US,SQUS4SPUSESkj##s$Qs*Kj##s$Ms*LVGDSll#;s&-s&*#j#Is$L#j#)s$N#V#JGj##s$Q#j##s(5#(s(6s$V*#Oj#Js$X#j#Ks$Z#V#JGj##s(2#j##s$a#(s$bs$a1#Ml#U3s*s#l#)5s$f#l#E7s$j#j#S9#j#T;#V#JGj##>#j##B#(s##s$sA#SPj#<s$v#j#=s${#V#JGj##s#(#j##s#,#(s#-s&Rs#+#SEj#>s%&#j#?s%(#V#JGj##s(K#j##s%/#(s%0s%/s#4#S<l#@s#6C#l#As#9C#l#Bs#?s#;#l#Cs#Es#A#l#Ds#Ks#G#l#Es#Qs#M#l#Fs#Ws#S#l#Gs#YC#l#Hs#]C#l#Is#ds#_#l#Js#ks#f#l#Ks#qs#m#l#)s#ws#s#l#*s#}s#y#l#Ls$'s$##l#Ms$-s$)#l#Rs$2s$/#l#Qs$:s$4#l#Vs+9s+6#l#Us+Cs+>#l#Ns$?s$@#l#Os'`s'a#WShs$ED#-s$FD$F#%$D'$#1s+6D&S$Q.#D1#DVSZJG5KGVSZMJ#K#GVSZS%P#K#G2s.7O)S%O2s.9#0s.9s.9%#USrs.9As.:$#nK#$##s.:J#%###$Cs.<s,=#0s.>s.>S'S->SH##K#Lk#W&#k#X/#j#YK#VSZPM#K#L2s.GS%)PS%2s.I#0s.Is.I%#As.I#2Cs.Js,U##K>L%MJk##$#%JG#K@Lk##$#'&#%PMk##&#j##%#k##+3j###Jj##,#VT7JG(.+'$#j#2C#j#3C#k#2C1k#3C#NQOM%QO2s.bS$)QS$2s.d#0s.ds.d%##s.d#s,\Cs.es,]s#.VT8$#0s.hs.hS0S.>SE##K#Lj##&#2s.mR)S$R2s.o#0s.os.o%##s.o#*2s.rS#)RS#2s.t#0s.ts.t%#0s.us.uSCS<#s.uJ#0s.ws.wS4SC>SQ##K#Lk##&#0s.{s.{S=S0#s.{*#2s.~S&)S#S&2s/$#0s/$s/$%#0s/%s/%S<S=#s/%$#nSc%s/'s/'$#0s/'G#$%#Y#YGj#Zs/'#2s/*S))S&S)2s/,#0s/,s/,%#ZSss/,s/-'#6G#s/.%S<nSc%s//s//$#0s//G#$%#Y#YJj#Zs//#2s/2S*)S)S*2s/4#0s/4s/4%#ZSss/4s/5'#<J#s/6'S42s/8S1#s/8#SD2s/:S8#s/:#S92s/<S7)S7S32s/>##s/>#SA0s/?s/?JS6>SF##K#Lk##&#j#Ys/C#)S8S72s/F##s/F#S9)S3S,2s/I#2s/JS-0s/Js/J#G>SK##K#Lj#Ys/M#2s/OS,)S,S-2s/Q#0s/Qs/Q*#0s/Rs/RGS>#s/R$#2s/US')S-S'2s/W#0s/Ws/W%#>S/##K#Lk#W)#j#Ys/[#0s/\s/\060s/]s/]1S6#s/]$#0s/_s/_-G#s/_+#2s/bS.)S'S.2s/d#0s/ds/d%#>S[##K#Lk#W)#j#2s/h##s/h::VS\s/kS'/s/lSK$#Gj#[C#.s%8D1#D5C##CS-$m#$#&S9D)#s-).#D1#D5C##CS.$m#$#5C1#CS92m#$#/s/~S[5C##CS6$m#$#&SiSHH#D$F$&SJSE-#D$F#k##s)b#k##'#&SED)#s-?H#D$F$&S:D)#s-C-#D$F#k##s)l#k##(#I1D$F2&S?S:.#D$F#k##s)s#k##'#I.D$F/&SQD)#s-R.#D$F#k##s){#k##(#&S?D)#s-X8#D1D)-+D&$##C-#k##s-Z#9/D&SPD)#s-a-#D$F#%$D'$#k##s-X#:(D&SkD)#s-i-#D%D#$$F'$#k##s-W#;(D&T9D)#s-q.#D#C#Fk##s-q#<&D&SID)#s-w-#D#C#$k##s-w#.&D&SFD)#s-}-#D&SKSF8#D&S/SK.#D1D#-%D&$##C'#k##s.'#9)D&S[S/-#D$F#%$D'$#k##s.$#:(D&SjS[-#D%D#$$F'$#k##s-~#;(D&SmSj.#D#C#Fk##s.;#<&D&S@Sm-#D#C#$k##s.@#.&D&SlS@-#D$FG%GD'$#/s1:SL$#S/j##%#%JD$FM%PD/s1@SR$#S@j##s+u#$FSt%Sts/['$#/s1FT:$#SSj##%#%T;s/`$FT<%STs/b$FSn%Sns/d'$#/s1OSu$#SUj##%#%SVs/i$FSW%SMs/kUS0SWUS6SM%SCD's,@#USQSo%S'D's,I#/s1\T=$#SVj##%#%S>D's'&#/s1aT>$#SLj##%#%SHD%SED=Sv=#=#=#=#=#=#=#7C#7C%UT?SOVT@C#7C*JC$#7C-JC&#7CSv3C$#3C'#3C,#3C.#K#SNAS5#s.#AS5$#FCS$6C#Ps.$FCO6C$M#FCS%FCQ6C$S$#6C&J#@Cs2.OSO4#@C#+C&S2#,s..IEEH#N+C%S(s..,s.0IEEH#NZSYs.1IEEH#@Cs28DC#)TCs/EWS]C$#O.@C#EC.#DC#2+C'S(#,s.;IEEH#N*s.<IEEH-s,a#+Cs.<S+*,s.>IEEH#N+Cs.>S+5,s.@IEEH#N+Cs.@S+,,s.BIEEH#N*s.CIEEH%s,h#*s.DIEEH(s,i#+C5S(s,m,s.FIEEH#N@Cs2NEC3>+C$S(#,s.JIEEH#N+Cs.JS2A,s.LIEEH#NOs2T@C#+Cs.NS+#,s.PIEEH#N+Cs.PS+A,s.RIEEH#N+Cs,{S+.,s.TIEEH#N*s.UIEEH%s,z#*s.VIEEH(s,{#*s.WIEEH-s,|#*s.XIEEH0s,}#*s.YIEEH5s,~#*s.ZIEEH8s-##*s.[IEEHAs-$#*s.\IEEHs#0s-%#l#8#s.Xs.Rl#9s#8s._#l#:s#As.b#j#PC#j#\C#j#]C#j#^C#j#_C#j#`C#j#aC#%QS%#COFk###SG&S%Q)#s/|1QS$&#R#C%#k##(#$F'k##s*5s*1k##$##COP1S#R#CO#%FS#$RS#k##s*8#k##s*9#k##&#k##(#k##+#k##-#k##1#k##:#k#PC#k#\C#k#]C#k#^C#k#_C#k#`C#k#aC#/s3,TAcGS:S?DS^SXSR#JSISFS@SBS_S,S1l#;s#%%#j#Is$(#j#)s*H#V#JGj##s$,#j##s(U#(s(Vs$3s$/#Oj#Js-b#j#Ks-|#V#JGj##s*E#j##s.'#(s.(s$>s$:#Ml#Us$@s0U#l#)s$Ds$B#l#Es$Fs-t#j#bs$H#j#cs$J#V#JGj##s$M#j##s$T#(s$Us$Ts$P#SMj#Ss$W#j#Ts$Y#V#JGj##s$\#j##s$c#(s$ds$cs$_#STj#<s-y#j#=s-{#V#JGj##s-~#j##s.'#(s.(s.'s$k#SBj#>s$o#j#?s$q#V#JGj##s$t#j##s${#(s$|s${s$w#S/l#@s$~C#l#As%%C#l#Bs%+s%'#l#Cs%1s%-#l#Ds%9s%3#l#Es%As%;#l#Fs%Js%C#l#Gs%MC#l#Hs%QC#l#Is%Xs%S#l#Js%_s%Z#l#Ks%hs%a#l#)s%qs%j#l#*s%xs%s#l#Ls&'s%|#l#Ms&/s&)#l#Rs&8s&1#l#Qs&Bs&<#l#Vs0}s0z#l#Us1+s1&#l#Ns&Gs&H#l#Os&Ls&M#l#ds&Ps&Q#l#es&Xs&Y#$FS/%S/s2*'$#j##s%:#$FS@%S@s2.'$#j##s.L#$FSS%SSs22'$#j##s%6#$FSU%SUs26'$#j##s%1#$FSV'#s%/j##s%'#$FSL%SLs2='$#j##s%&#7Cs$|3Cs$p#3Cs$v#K#SN=s$z=#=#=#7C#7C%JCs$|#7Cs%*7Cs%-3C#s$z3C%#3Cs%$#3C(#3C+#K#SNWTBCs%+s%&7Cs%0JCs%+#3C#s%'3Cs%/#3C'#K#SNAS5*s0FAS5$#AS5,#AS5<#FCR6C#S%s0I6C#Ms%$FCS#6C#Os0L6C#Ps%,6C&J#Os4S@C#+Cs0NS+#,s0PIEEH#N+Cs$aS(s0P,s0RIEEH#NZSYs0SIEEH#@Cs%,DC#s%%ECs$fs%/DC#++C%S(#,s0YIEEH#N*s0ZIEEH)s/##+Cs%&S2s$k,s0\IEEH#NDC+s$mWS]C#s%,ECs$os%5DC#s%++C%S(#,s0bIEEH#N*s0cIEEH2s/,#+Cs0cS+(,s0eIEEH#N*s0fIEEHs$ts//s%(*s0gIEEH$s/0#ECs%>s$x+Cs/5S(#,s0jIEEH#NECs%Ds${+Cs%'S(#,s0mIEEH#N+Cs0mS2s$~,s0oIEEH#NTCs3.WTCC#s4r+C?S+#,s0sIEEH#N+Cs0sS+B,s0uIEEH#N+Cs/BS2s%1,s0wIEEH#N+Cs0wS+s/D,s0yIEEH#N+Cs/FS2+,s0{IEEH#N[Sws0|IEEH%#*s0}IEEH(s/F#*s0~IEEH+s/G#*s1#IEEH.s/H#*s1$IEEH3s/I#*s1%IEEH6s/J#*s1&IEEH:s/K#*s1'IEEH>s/L#*s1(IEEHs##s/M#*s1)IEEHs%Es/N#*s1*IEEHs#,s/O#*s1+IEEHs#/s/P#*s1,IEEHs#:s/Q#l#8#s1(s0~l#9s#@s1/#l#:s#Hs12#j#PC#j#\C#j#]C#j#^C#j#_C#j#`C#j#aC#j#fC#j#gC#&S%O1QS#&#S&#C%#k##s%2#%RQ#CRFk###SG&S$S#)#s2S1S#S&&#S)#C%#k##(#$F'$FS&k###s,Zk##%#1S)S&#CQ#1S8S)#CR#%FS*&S)S*$#s3i%S)S*%S*s3k's,e#k##%#k##s,g#k##(#k##+#k##-#k##0#k##3#k##8#k##s,y#k##B#k##s#$#k##s0B#k#PC#k#\C#k#]C#k#^C#k#_C#k#`C#k#aC#k#fC#k#gC#i#8GSAS6S:S?DS^SXS`SRQSJJMSISFSBSaS_SuS1SWl#;s#5$#j#Is&f#j#)s-*#V#JGj##s&j#j##s+7#(s+8s&qs$L#Oj#Js0D#j#Ks0^#V#JGj##s-'#j##s0e#(s0fs&|s$V#Ml#Us&~s37#l#)s'&s'$#l#Es'(s0V#j#bs'*#j#cs',#V#JGj##s'/#j##s'6#(s'7s'6s$b#SMj#Ss'9#j#Ts';#V#JGj##s'>#j##s'E#(s'Fs'Es$l#STj#<s0[#j#=s0]#V#JGj##s0`#j##s0e#(s0fs0es$v#SBj#>s'Q#j#?s'S#V#JGj##s'V#j##s']#(s'^s']s%$#S/l#@s'`C#l#As'cC#l#Bs'is'e#l#Cs'os'k#l#Ds'ws'q#l#Es(#s'y#l#Fs(,s(%#l#Gs(/C#l#Hs(3C#l#Is(:s(5#l#Js(As(<#l#Ks(Js(C#l#)s(Ss(L#l#*s(Zs(U#l#Ls(es(^#l#Ms(ms(g#l#Rs(vs(o#l#Qs)$s(z#l#Vs3_s3\#l#Us3is3d#l#Ns))s)*#l#Os).s)/#l#ds)2s)3#l#es):s);#WSxs6PS'#LCS's)As%Bs)D#/s6Rs)[VSys6SS'LCs)Gs)D%$#/s6Us)O&G#/s6WSF&s)J#$%#j#[C#VS\s6[s)cVS\s6\S.&#G$#(j#[C#VS\s6`s)[&G#$#,j#[C#&S.G$#/j#[C#)SKS/&S/#/s6iSo&s(2#$%#j##s(5#)SmS@&S@#/s6oS`&s(2#$%#j##s1I#)SaSS&SS#/s6uTD&s(2#$%#j##s(5#)TESU&SU#/s6{SX&s(/#$%#j##s(2#)SnSV&SV#/s7%TF&s((#$%#j##s(+#)SoSL&SL#/s7+TG&s()#$%#j##s(,#7Cs%`JCs'ys'|3Cs%[s'u3Cs'z#3Cs%T#3C&#3C(#K#SNAS5#s3:AS5$#6Cs%MQs3:6Cs%PM#FCS&6C#S$s3=6Cs'wP#6C&J#Os'O@C#+Cs3?S+#,s3AIEEH#N+Cs'iS(s3A,s3CIEEH#NZSYs3DIEEH#DCs'Us'w4s'W@C#ECs'o#DC#,+C'S(#,s3KIEEH#N*s3LIEEH*s1q#+Cs3LS+*,s3NIEEH#N+Cs3NS+*,s3PIEEH#N*s3QIEEHs'ms1v#*s3RIEEH&s1w#+Cs'cS(s%],s3TIEEH#N+Cs(+S(s(%,s3VIEEH#NECs(0s'~+Cs2$S(#,s3YIEEH#NEC5s(%+Cs'rS(#,s3\IEEH#N+Cs3\S2s((,s3^IEEH#NWS]Cs'vs2+DCs2,#+C#S+s%j,s3bIEEH#N*s3cIEEHs%Js2,#*s3dIEEH(s2-#*s3eIEEH+s2.#*s3fIEEH/s2/#*s3gIEEH3s20#*s3hIEEH6s21#*s3iIEEH9s22#*s3jIEEH@s23#*s3kIEEHs#,s24#l#8#s3gs3al#9s#2s3n#l#:s#9s3q#j#PC#j#\C#j#]C#j#^C#j#_C#j#`C#j#aC#j#fC#j#gC#j#hC##CS$Fk###SG&QS$1RS&&#S)#C%#k##'#$F'k##s/As/6k##$##CS$O#CS#S$1S*S)#CO#1S8S*#CS$#%FS1%RS#)S&S#&S##$#s%?k##&#k##(#k##*#k##-#k##0#k##2#k##4#k##8#k##s/V#k#PC#k#\C#k#]C#k#^C#k#_C#k#`C#k#aC#k#fC#k#gC#k#hC#/s8FTHgGSAS6S?DS^SX#s'yS`SRQSJSKS@SlSBSaS_SWl#;s#-%#j#Is)B#j#)s/b#V#JGj##s)F#j##s-o#(s-ps)Ms#~#Oj#Js2|#j#Ks3:#V#JGj##s/_#j##s3A#(s3Bs)Xs$.#Ml#Us)Zs5o#l#)s)^s)\#l#Es)`s32#j#bs)b#j#cs)d#V#JGj##s)g#j##s)n#(s)os)ns$=#SMj#Ss)q#j#Ts)s#V#JGj##s)v#j##s)}#(s)~s)}s$I#STj#<s37#j#=s39#V#JGj##s3<#j##s3A#(s3Bs3As$U#SBj#>s*-#j#?s*/#V#JGj##s*2#j##s*9#(s*:s*9s$a#S/l#@s*<C#l#As*?C#l#Bs*Es*A#l#Cs*Ks*G#l#Ds*Ss*M#l#Es*[s*U#l#Fs*ds*]#l#Gs*gC#l#Hs*kC#l#Is*rs*m#l#Js*ys*t#l#Ks+&s*{#l#)s+/s+(#l#*s+6s+1#l#Ls+As+:#l#Ms+Is+C#l#Rs+Rs+K#l#Qs+\s+V#l#Vs6;s68#l#Us6Es6@#l#Ns+as+b#l#Os+fs+g#l#ds+js+k#l#es+rs+s#$Fs%#%s%$s7D'$#j##s*T#$Fs$}%s$~s7H'$#j##s3f#$Fs${%s$|s7L'$#j##s*P#$Fs$y%s$zs7P'$#j##s*K#$Fs$w%s$xs7T'$#j##s*B#$Fs$u%s$vs7X'$#j##s*A#7Cs'tJCs*2s$t3Cs'fs$r3Cs*6#3Cs*8#3C&#3C(#K#SNAS5#s5O+Cs)cS(s'B,s5MIEEH#N+Cs3vS(s'A,s5OIEEH#N+Cs)|S2s'=,s5QIEEH#N+Cs)iS2s3z,s5SIEEH#NWS]Cs3|s)k+Cs5TS+#,s5VIEEH#N+C%S2s'D,s5XIEEH#N[Sws5YIEEH%#*s5ZIEEH)s4##*s5[IEEHs'Ds4$#*s5\IEEH-s4%#*s5]IEEHs'Ls4&#*s5^IEEH1s4'#*s5_IEEH4s4(#*s5`IEEHs'[s4)#*s5aIEEHs'cs4*#*s5bIEEHs'fs4+#*s5cIEEHs'qs4,#l#8#s5_s5Yl#9s'ws5f#l#:=s5i#j#PC#j#\C#j#]C#j#^C#j#_C#j#`C#j#aC#j#fC#j#gC#&QR)#s7&1RS#&#S&#C%#k##s$Y#1S*S##CO#%FS&%S&s85%S&S#$Fs-S%s-Ts88'$#k##&#k##s'9#k##)#k##+#k##-#k##s)l#k##1#k##s'I#k##s'K#k##s4i#k#PC#k#\C#k#]C#k#^C#k#_C#k#`C#k#aC#k#fC#k#gC#gGSAS6S:S?DS^SXSRS`QSJJSISBSaS_S3S1SWl#;s#%$#j#Is+1#j#)s1Q#V#JGj##s+5#j##s/^#(s/_s+<s#X#Oj#Js4k#j#Ks5)#V#JGj##s1N#j##s50#(s51s+Gs#b#Ml#Us+Is7^#l#)s+Ms+K#l#Es+Os4}#j#bs+Q#j#cs+S#V#JGj##s+V#j##s+]#(s+^s+]s#o#SMj#Ss+`#j#Ts+b#V#JGj##s+e#j##s+l#(s+ms+ls#y#STj#<s5&#j#=s5(#V#JGj##s5+#j##s50#(s51s50s$'#SBj#>s+x#j#?s+z#V#JGj##s+}#j##s,(#(s,)s,(s$1#S/l#@s,+C#l#As,.C#l#Bs,4s,0#l#Cs,:s,6#l#Ds,Bs,<#l#Es,Js,D#l#Fs,Ss,L#l#Gs,VC#l#Hs,ZC#l#Is,as,\#l#Js,hs,c#l#Ks,qs,j#l#)s,zs,s#l#*s-%s,|#l#Ls-0s-)#l#Ms-8s-2#l#Rs-As-:#l#Qs-Ks-E#l#Vs8*s8'#l#Us84s8/#l#Ns-Ps-Q#l#Os-Us-V#l#ds-Ys-Z#l#es-as-b#WSxs:ws.##LCs.$s&ps$Os&{#LCS's&t#s-ls'+/s:zs.%VSys:{s.'LCs'#s&{%$#LCs-ps'%#s'-s',\TIS/SFSIs.+s.)Sks',#j#Ws-s#[Sbs;#s.1s-u#S>MGj#Ws.$#[Sbs;%s.5s.(#S>PRZSbs;&s.<s.7#S6Gl#JGs.G#j#Ks.@#ZSbs;)s.Ls.D#SAGl#KGs.N#j#)s.Q#U#Gl#)s.Vs.U#U#Gl#)s.`s._#j#*s.h#U#Gj#*s.p#nSz%s;2s.y%#0##s.sG#$###s;3Gs.m>S?s.z#K#Lk##%#j#0s;7#U#s.x5s;9s.sUG#l#*+%#j#Ws/+#U#Gj##s/8#Cs;?s/6s/d>S:s.z#K#Lj##SG#VS{#Gj#*'#U#Gj##s/?#ZTJs/As/@s/;+#Ml#Xs/Hs/G#l#*s/Ls/J#j#Ws/^#j#Xs/e##Ks/gTKCs;Ms9Xs/rj##SGs/mVS{#Gj#W%#j#X'#XTLs/n)#JV#GS8l#Xs0&s0$#l#is0(K#l#js0*C#l#ks0.C#l#ls04s00#l#ms1~s1y#l#ns3ds3`#l#os5Ds5?#l#ps7/s8`#l#qs9{C#l#rs9|C#l#ss9-s9*#l#ts:(s:##l#us:)s:$#j#Ws:+#j#2s;d#j#Ys;e#V#JGj#Ys;g#j#Ys;h#YTMs;is;is:4#Gj#,s;i#XGs;js:ps:<#l#*s:As:>#XS|s;$s;#s:`#Ns;)s;&#l#*s;-s;+#m##s;FXS|s;Gs;E#MXGQs;JO#l#*s;Os;L#j#6s;m#j#+s;q#j#3s;v#j#vs;w#j#ws;v#j#&s<%##"). Qed.

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
