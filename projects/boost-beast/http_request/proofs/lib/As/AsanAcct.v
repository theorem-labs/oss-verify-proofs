(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg CatSim PropExec.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrestrict (H : word -> bool) (m : word -> option byte)
    : word -> option byte :=
  fun a => if H a then None else m a.

(* [comment removed for export] *)
Definition munrestrict (H : word -> bool) (full m' : word -> option byte)
    : word -> option byte :=
  fun a => if H a then full a else m' a.

Definition restrict (H : word -> bool) (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := mrestrict H (ms_mem ms);
     ms_rom := ms_rom ms |}.

Definition unrestrict (H : word -> bool) (full : word -> option byte)
    (ms' : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms'; ms_fregs := ms_fregs ms';
     ms_pc_val := ms_pc_val ms';
     ms_svc_pending := ms_svc_pending ms';
     ms_resv := ms_resv ms'; ms_fcsr := ms_fcsr ms';
     ms_mem := munrestrict H full (ms_mem ms');
     ms_rom := ms_rom ms' |}.

(* [comment removed for export] *)
Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop :=
  forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = None.

(* [comment removed for export] *)
Definition wx_segs_nowrap (segs : list Segment) : Prop :=
  forall seg, In seg segs ->
    seg_executable seg && seg_writable seg = true ->
    (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z.

(* [comment removed for export] *)
Definition woff (a : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned a + Z.of_nat k).

Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
  forall k, (k < n)%nat -> H (woff a k) = false.

Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop :=
  forall a n, In (a, n) l -> range_avoids H a n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma woff_0 : forall a, woff a 0 = a.
Proof.
  intros a. unfold woff. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma woff_succ : forall a k, woff (a + 1) k = woff a (S k).
Proof.
  intros a k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma range_avoids_hd : forall H a n,
  range_avoids H a (S n) -> H a = false.
Proof.
  intros H a n Hr. rewrite <- (woff_0 a). apply Hr. lia.
Qed.

Lemma range_avoids_tl : forall H a n,
  range_avoids H a (S n) -> range_avoids H (a + 1) n.
Proof.
  intros H a n Hr k Hk. rewrite woff_succ. apply Hr. lia.
Qed.

Lemma range_avoids_cons : forall H a n,
  H a = false -> range_avoids H (a + 1) n -> range_avoids H a (S n).
Proof.
  intros H a n H0 Hr k Hk. destruct k as [|k].
  - rewrite woff_0. exact H0.
  - rewrite <- woff_succ. apply Hr. lia.
Qed.

Lemma ranges_avoid_nil : forall H, ranges_avoid H [].
Proof. intros H a n Hin. destruct Hin. Qed.

Lemma ranges_avoid_cons : forall H a n l,
  range_avoids H a n -> ranges_avoid H l -> ranges_avoid H ((a, n) :: l).
Proof.
  intros H a n l Ha Hl a' n' [Heq | Hin].
  - injection Heq as <- <-. exact Ha.
  - exact (Hl a' n' Hin).
Qed.

Lemma ranges_avoid_app : forall H l1 l2,
  ranges_avoid H l1 -> ranges_avoid H l2 -> ranges_avoid H (l1 ++ l2).
Proof.
  intros H l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin | Hin];
    [exact (H1 a n Hin) | exact (H2 a n Hin)].
Qed.

(* [comment removed for export] *)
Lemma restrict_svc_pending : forall H ms,
  ms_svc_pending (restrict H ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma restrict_pc : forall H ms, ms_pc (restrict H ms) = ms_pc ms.
Proof. reflexivity. Qed.
Lemma restrict_regs : forall H ms, ms_regs (restrict H ms) = ms_regs ms.
Proof. reflexivity. Qed.
Lemma restrict_reg : forall H ms r, ms_reg (restrict H ms) r = ms_reg ms r.
Proof. reflexivity. Qed.
Lemma restrict_rom : forall H ms, ms_rom (restrict H ms) = ms_rom ms.
Proof. reflexivity. Qed.
Lemma restrict_mem : forall H ms, ms_mem (restrict H ms) = mrestrict H (ms_mem ms).
Proof. reflexivity. Qed.
Lemma unrestrict_svc_pending : forall H full ms,
  ms_svc_pending (unrestrict H full ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma unrestrict_mem : forall H full ms,
  ms_mem (unrestrict H full ms) = munrestrict H full (ms_mem ms).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma restrict_mkst : forall H regs pc mem rom,
  restrict H (mkst regs pc mem rom) = mkst regs pc (mrestrict H mem) rom.
Proof. reflexivity. Qed.

Lemma mrestrict_idem : forall H m, mrestrict H (mrestrict H m) = mrestrict H m.
Proof.
  intros H m. apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a); reflexivity.
Qed.

Lemma munrestrict_mrestrict : forall H m,
  munrestrict H m (mrestrict H m) = m.
Proof.
  intros H m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma mrestrict_munrestrict : forall H full m,
  mrestrict H (munrestrict H full m) = mrestrict H m.
Proof.
  intros H full m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma unrestrict_restrict : forall H ms,
  unrestrict H (ms_mem ms) (restrict H ms) = ms.
Proof.
  intros H ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite munrestrict_mrestrict. reflexivity.
Qed.

Lemma restrict_unrestrict : forall H full ms,
  restrict H (unrestrict H full ms) = restrict H ms.
Proof.
  intros H full ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite mrestrict_munrestrict. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hclean (H : word -> bool) (ms : machine_state) : Prop :=
  forall a, H a = true -> ms_mem ms a = None.

Lemma restrict_hclean : forall H ms, hclean H (restrict H ms).
Proof.
  intros H ms a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
Qed.

Lemma hclean_restrict_id : forall H ms, hclean H ms -> restrict H ms = ms.
Proof.
  intros H ms Hc. destruct ms. unfold restrict. cbn. f_equal.
  apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma restrict_unrestrict_clean : forall H full ms,
  hclean H ms -> restrict H (unrestrict H full ms) = ms.
Proof.
  intros H full ms Hc. rewrite restrict_unrestrict. apply hclean_restrict_id. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Lemma memory_read1_hidden : forall a, H a = true -> memory_read segs a 1 = None.
Proof.
  intros a Ha. unfold memory_read. cbn [Z.of_N]. rewrite (HH a Ha). reflexivity.
Qed.

Lemma ov_read_bytes_restrict : forall n m a bs,
  ov_read_bytes segs (mrestrict H m) a n = Some bs ->
  ov_read_bytes segs m a n = Some bs /\ range_avoids H a n.
Proof.
  induction n as [|n IH]; intros m a bs Hr.
  - cbn in Hr |- *. split; [exact Hr | intros k Hk; lia].
  - cbn [ov_read_bytes] in Hr |- *.
    unfold mrestrict in Hr at 1.
    destruct (H a) eqn:Ha.
    + rewrite (memory_read1_hidden a Ha) in Hr. discriminate.
    + destruct (match m a with
                | Some b => Some b
                | None => match memory_read segs a 1 with
                          | Some (b :: _) => Some b | _ => None end
                end) as [b|]; [|discriminate].
      destruct (ov_read_bytes segs (mrestrict H m) (a + 1) n) as [rest|] eqn:Hrest;
        [|discriminate].
      destruct (IH m (a + 1) rest Hrest) as [Hfull Hav].
      rewrite Hfull. split; [exact Hr|].
      apply range_avoids_cons; assumption.
Qed.

Lemma wview_restrict : forall m a,
  wview segs (mrestrict H m) a =
    if H a then None else wview segs m a.
Proof.
  intros m a. unfold wview, mrestrict. destruct (H a) eqn:Ha; [|reflexivity].
  rewrite (HH a Ha). reflexivity.
Qed.

Lemma store_ok_restrict : forall n m a,
  store_ok segs (mrestrict H m) a n = true ->
  store_ok segs m a n = true /\ range_avoids H a n.
Proof.
  induction n as [|n IH]; intros m a Hs.
  - split; [reflexivity | intros k Hk; lia].
  - cbn [store_ok] in Hs |- *. rewrite wview_restrict in Hs.
    destruct (H a) eqn:Ha; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) Hs) as [Hfull Hav].
    split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.

(* [comment removed for export] *)
Lemma write_to_mem_restrict : forall bs m a,
  range_avoids H a (length bs) ->
  write_to_mem (mrestrict H m) a bs = mrestrict H (write_to_mem m a bs).
Proof.
  induction bs as [|b bs IH]; intros m a Hav; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite <- (IH _ (a + 1) Htl). f_equal.
  apply functional_extensionality. intro x. unfold mrestrict.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha. reflexivity.
Qed.

Lemma write_to_mem_hidden : forall bs m a x,
  range_avoids H a (length bs) -> H x = true ->
  write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hav Hx; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite (IH _ (a + 1) x Htl Hx). cbv beta.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha in Hx. discriminate.
Qed.

(* [comment removed for export] *)
Lemma mrestrict_visible : forall (H0 : word -> bool) m a,
  H0 a = false -> mrestrict H0 m a = m a.
Proof. intros H0 m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.

Lemma ov_read_bytes_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  ov_read_bytes segs (mrestrict H0 m) a n = ov_read_bytes segs m a n.
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [ov_read_bytes]. unfold mrestrict at 1. rewrite (range_avoids_hd H0 a n Hav).
  rewrite (IH m (a + 1) (range_avoids_tl H0 a n Hav)). reflexivity.
Qed.

Lemma rdn_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  rdn segs (mrestrict H0 m) a n = rdn segs m a n.
Proof.
  intros H0 n m a Hav. rewrite <- !ov_rdn. apply ov_read_bytes_mrestrict_eq. exact Hav.
Qed.

Lemma wview_mrestrict_eq : forall (H0 : word -> bool) m a,
  H0 a = false -> wview segs (mrestrict H0 m) a = wview segs m a.
Proof. intros H0 m a Ha. unfold wview, mrestrict. rewrite Ha. reflexivity. Qed.

Lemma store_ok_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  store_ok segs (mrestrict H0 m) a n = store_ok segs m a n.
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [store_ok]. rewrite (wview_mrestrict_eq H0 m a (range_avoids_hd H0 a n Hav)).
  destruct (wview segs m a); [|reflexivity].
  exact (IH m (a + 1) (range_avoids_tl H0 a n Hav)).
Qed.

(* [comment removed for export] *)

Lemma find_segment_some_spec : forall l addr n seg,
  find_segment l addr n = Some seg ->
  In seg l /\ (Z.of_N (seg_base seg) <= addr)%Z
  /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - injection Hf as ->. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | split; assumption].
  - destruct (IH addr n seg Hf) as (Hin & H1 & H2).
    split; [right; exact Hin | split; assumption].
Qed.

Lemma find_segment_none_spec : forall l addr n,
  find_segment l addr n = None ->
  forall seg, In seg l ->
    ~ ((Z.of_N (seg_base seg) <= addr)%Z
       /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z).
Proof.
  induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
    [discriminate|].
  destruct Hin as [<- | Hin].
  - intros [H1 H2]. apply andb_false_iff in E as [E | E].
    + apply Z.leb_gt in E. lia.
    + apply Z.leb_gt in E. lia.
  - exact (IH addr n Hf seg Hin).
Qed.

(* [comment removed for export] *)
Lemma in_segment_not_hidden : forall (x : word) seg,
  In seg segs ->
  (Z.of_N (seg_base seg) <= bv_unsigned x)%Z ->
  (bv_unsigned x + 1 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  H x = false.
Proof.
  intros x seg Hin H1 H2. destruct (H x) eqn:Hx; [|reflexivity].
  exfalso. exact (find_segment_none_spec segs (bv_unsigned x) 1 (HH x Hx) seg Hin (conj H1 H2)).
Qed.

Lemma seg_ov_read_bytes_restrict : forall n m seg a,
  In seg segs ->
  (Z.of_N (seg_base seg) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z ->
  seg_ov_read_bytes (mrestrict H m) seg a n = seg_ov_read_bytes m seg a n.
Proof.
  induction n as [|n IH]; intros m seg a Hin Hlo Hhi Htop; [reflexivity|].
  cbn [seg_ov_read_bytes].
  assert (Ha : H a = false) by (apply (in_segment_not_hidden a seg Hin); lia).
  unfold mrestrict at 1. rewrite Ha.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z).
    { rewrite bv_add_unsigned.
      assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (bv_unsigned_in_range 64 a). lia. }
    rewrite (IH m seg (a + 1) Hin) by lia. reflexivity.
Qed.

Lemma code_read_ov_restrict : forall m a n,
  code_read_ov segs (mrestrict H m) a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg) eqn:Ewx; [|reflexivity].
  destruct (find_segment_some_spec segs _ _ seg Hf) as (Hin & H1 & H2).
  apply seg_ov_read_bytes_restrict; [exact Hin | exact H1 | | exact (Hwx seg Hin Ewx)].
  rewrite N_nat_Z. exact H2.
Qed.

Lemma fetch_word_ov_restrict : forall m a,
  fetch_word_ov segs (mrestrict H m) a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_ov_restrict : forall m a,
  fetch_half_ov segs (mrestrict H m) a = fetch_half_ov segs m a.
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_any_restrict : forall m a,
  fetch_half_any segs (mrestrict H m) a = fetch_half_any segs m a.
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

Lemma fetch_tail_any_restrict : forall m a,
  fetch_tail_any segs (mrestrict H m) a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

Lemma fetch_failure_restrict : forall m a,
  fetch_failure segs (mrestrict H m) a = fetch_failure segs m a.
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

(* [comment removed for export] *)
Lemma interp_eff_accesses_restrict : forall t m c mr' rs,
  interp_eff_accesses segs t (mrestrict H m)
    = MachineOk (@mkAccessReport _ (c, mr') rs) ->
  exists mf',
    interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs)
    /\ mr' = mrestrict H mf'
    /\ (forall x, H x = true -> mf' x = m x)
    /\ ranges_avoid H rs.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH]; (* [comment removed for export] *)
    intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  - (* [comment removed for export] *)
    injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    apply ranges_avoid_nil.
  - (* [comment removed for export] *)
    destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
      [|discriminate].
    destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
    rewrite Hfull.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
    apply ranges_avoid_cons; assumption.
  - (* [comment removed for export] *)
    destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
    + intros x Hx. rewrite (Hhid x Hx).
      apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
    + apply ranges_avoid_cons; assumption.
Qed.

(* [comment removed for export] *)
Lemma decode_exec_accesses_restrict : forall ms w msr' rs',
  decode_exec_accesses segs (restrict H ms) w
    = MachineOk (@mkAccessReport _ msr' rs') ->
  decode_exec_accesses segs ms w
    = MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
  /\ ranges_avoid H rs'
  /\ hclean H msr'.
Proof.
  intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-.
    split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
    unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
    rewrite munrestrict_mrestrict. destruct ms; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
    destruct (interp_eff_accesses segs
                (exec (Z_to_bv 64 isz) i
                   {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
                      c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
                      c_resv := ms_resv ms |})
                (mrestrict H (ms_mem ms)))
      as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
      as (mf' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn [access_value accessed_ranges].
    split; [|split; [exact Hrs|]].
    + unfold unrestrict. cbn.
      replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
      apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
      destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

Theorem step_accesses_restrict : forall ms msr' rs',
  step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ msr' rs') ->
  step_accesses segs ms
    = MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
  /\ ranges_avoid H rs'
  /\ hclean H msr'.
Proof.
  intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

(* [comment removed for export] *)
Theorem step_restrict_sound : forall ms msr',
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists rep,
    step_accesses segs ms = MachineOk rep
    /\ access_value _ rep = unrestrict H (ms_mem ms) msr'
    /\ ranges_avoid H (accessed_ranges _ rep)
    /\ hclean H msr'
    /\ restrict H (unrestrict H (ms_mem ms) msr') = msr'.
Proof.
  intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as ->.
  destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
  exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
  split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
  apply restrict_unrestrict_clean. exact Hcl.
Qed.

(* [comment removed for export] *)
Corollary step_restrict_step : forall ms msr',
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  RiscvSemantics.step segs ms = MachineOk (unrestrict H (ms_mem ms) msr').
Proof.
  intros ms msr' Hs.
  destruct (step_restrict_sound ms msr' Hs) as (rep & Hsa & Hv & _).
  unfold RiscvSemantics.step, drop_access_report. rewrite Hsa, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_accesses_ecall_shape : forall ms msr' rs',
  step_accesses segs ms = MachineOk (@mkAccessReport _ msr' rs') ->
  ms_svc_pending msr' <> None ->
  rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
  /\ ms_svc_pending msr' = Some (ms_reg ms 17).
Proof.
  intros ms msr' rs' Hs Hsvc.
  assert (Hdec : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ msr' rs') ->
            rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
            /\ ms_svc_pending msr' = Some (ms_reg ms 17)).
  { intros w Hd. unfold decode_exec_accesses in Hd.
    destruct (is_ecall w).
    - injection Hd as <- <-. cbn. repeat split; reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses segs _ _) as [[[c1 m1] rs1]| |]; try discriminate.
      cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn in Hsvc.
      exfalso. apply Hsvc. reflexivity. }
  unfold step_accesses in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Hf; try discriminate.
  unfold fetch_failure in Hf.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

End ISA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_allowedb (A : list (Z * Z)) (p : word) : bool :=
  existsb (fun iv => (fst iv <=? bv_unsigned p)%Z
                     && (bv_unsigned p + page_size <=? snd iv)%Z) A.

(* [comment removed for export] *)
Definition A_wf (A : list (Z * Z)) : Prop :=
  Forall (fun iv => (fst iv <= snd iv)%Z /\ (fst iv) mod page_size = 0
                    /\ (snd iv) mod page_size = 0)%Z A.

(* [comment removed for export] *)
Fixpoint A_bytes (A : list (Z * Z)) : Z :=
  match A with
  | [] => 0
  | iv :: r => (snd iv - fst iv) + A_bytes r
  end%Z.

(* [comment removed for export] *)
Definition lazy_cover (H : word -> bool) (lazy : list (word * word))
    (A : list (Z * Z)) : Prop :=
  forall w : word,
    page_in_ranges (page_base w) lazy = true -> H w = false ->
    page_allowedb A (page_base w) = true.

(* [comment removed for export] *)
Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m
  = (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
  minv_nodup    : List.NoDup (m_vm_materialized m);
  minv_aligned  : forall p, In p (m_vm_materialized m) ->
                    (bv_unsigned p mod page_size = 0)%Z;
  minv_allowed  : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
  minv_lazy     : forall p, In p (m_vm_materialized m) ->
                    page_in_ranges p (m_vm_lazy m) = true;
  minv_budget   : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.

(* [comment removed for export] *)
Definition same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_materialized_refl : forall m, same_but_materialized m m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : forall m1 m2 m3,
  same_but_materialized m1 m2 -> same_but_materialized m2 m3 ->
  same_but_materialized m1 m3.
Proof.
  unfold same_but_materialized. intros m1 m2 m3 -> ->.
  destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma with_vm_backing_same : forall m mat',
  same_but_materialized m (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros [fd [maps lazy mat] io fs proc lim tm] mat'. reflexivity.
Qed.
Scheme kc__1 := Elimination for LinuxProcessSemantics.LinuxProcessSem.State.Model Sort Prop.
Scheme kc__2 := Elimination for LinuxProcessSemantics.LinuxProcessSem.State.VmState Sort Prop.

(* [comment removed for export] *)
Lemma same_but_materialized_frame : forall m m',
  same_but_materialized m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m  (* [comment removed for export] *)
  /\ m_fds m' = m_fds m /\ m_pipes m' = m_pipes m /\ m_stdin m' = m_stdin m
  /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\ m_tid m' = m_tid m
  /\ m_rlimit_core m' = m_rlimit_core m /\ m_clock m' = m_clock m
  /\ eager_used m' = eager_used m.
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.same_but_materialized); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.with_vm_backing); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.FdState); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_fd); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.IoState); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_io); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.FsState); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_fsys); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.ProcState); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_proc); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.LimState); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_lim); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.TimeState); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_time); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_fds); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.PipeBuf); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_pipes); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.InputStream); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_stdin); constr:(@LinuxProcessSemantics.LinuxProcessSem.Fs.Fs); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_fs); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_halted); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_tid); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_rlimit_core); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_clock); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.eager_used); constr:(@kc__1); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmState); constr:(@kc__2); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkModelOf); constr:(@Corelib.Init.Logic.conj); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkVmState); constr:(@Corelib.Init.Logic.eq_refl)|] [|@m'; @m; @m_time; @m_lim; @m_proc; @m_fsys; @m_io; @v; @tm; @lim; @proc; @fs; @io; @mat; @lazy; @maps; @vmst_materialized; @vmst_lazy; @vmst_maps; @m_vm; @fd; @m_fd; @H|] "#&o#9#`###&#%#N#P#R#T#V#$#D#F#\#^#e#<#(#'#h#K#J#`#j#*#)#=#M#X#Z#3#l#/#8#i#g#>#C#B#m#k#@#E#G#O#Q#S#U#W#Y#[#]#_#a#b#c#d#f#L#H#A#?#I=#F&#G%#H%#I'#J$#K$#L$#M$#N$#O$#P$#Q$#R$#S$#T$#U$#V$#W$#X$#Y$#Z$#[$#\$#]$#^&#_%VS+KC'E:K;$#E(C(D#L$#)C)D#M$#8S,8#8#8#8#8#US%#US&#<##9#'C'D#%$#*C*D#F$#+C+D#G$#,C,D#H$#-C-D#I$#.C.D#J$#<7S-9#/C/D#%$#<<S.9#0C0D#%$#1C1D#N$#2C2D#O$#US's#'3C3D#%$#4C4D#($#US%s#3US&#9#US'#5C5D#%$#6C6D#s#7$#7C7D#P$#$&#$*#$2#$6#$;#$?#$s###$s#)#$s#/#$s#3#$s#7#$s#;#$s#?#$s#C#$s#Q#$s#U#j#$Q#:E;s#J#C(##L#s#\)%#M#s#[''#s#Q#s#P*)#F#s#O++#G#s#N,-#H#s#M-/#I#s#L.1#J#s#K/3#s#I#s#H05#s#F#s#E17#N#s#D29#O#s#C3;#s#B#s#A4=#s#D#s#@5?#s#<#s#;6A#s#m#s#:7s###P#s#9$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/#$s#2#j#%Q#[S(S)RS#DEKC'#:S/;$#%(#('#L$#)&)*#M$#')#s$.#,*+*/#F$#+.+2#G$#,1,5#H$#-4-8#I$#.7.;#J$#/:/>#s$,$#0=0A#s$*$#1@1s#$#N$#2s##2s#'#O$#3s#&3s#*#s$)$#4s#)4s#-#s$,$#5s#,5s#0#s$%$#6s#/6s#3#s$W$#7s#27s#6#P$#$&#$*#$.#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#$s#2#$s#6#$s#:#$s#=#$s#A#k#&J#k#'I#k#(H#k#)G#k#*F#j#+S$#9s$qWS0S)S*R[S(S1#S#DEKC'#:S2;$#%(#('#L$#)&)*#M$#')#s$|#,*+*/#F$#+.+2#G$#,1,5#H$#-4-8#I$#.7.;#J$#/:/>#s$z$#0=0A#s$x$#1@1s#$#N$#2s##2s#'#O$#3s#&3s#*#s$w$#4s#)4s#-#s$z$#5s#,5s#0#s$s$#6s#/6s#3#s%I$#7s#27s#6#P$#$&#$*#$.#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#$s#2#$s#6#$s#:#$s#=#%Ls#B%Ms#@%s%\s#H%Fs#=%Gs#;%Hs#9%Is#7%Js#5%s%Ns#3%s%Js#1%Ns#/%Os#-%s%Cs#+%s%Ds#)%s%;s#'%s%ks#%%Ps##&s#&s##$#&s#*s##&#&s#.s##(#&s#2s##*#&s#6s##,#&s#:s##.#&s#>s##0#&s#Bs##2#&s#Fs##4#&s#Js##6#&s#Ns##8#&s#Rs##:#&s#Vs##<#&s#Zs##>#&s#]s##@#&s#as##B#j#,J#j#-I#j#.H#j#/G#j#0F#j#1s#o#j#2s&%#j#3M#W#EKCj#4s#s#j#5s&)#j#6M#WS3s#w#Cj#7S$#j#8L#[#S*RS#DEKCj#&J#j#'I#j#(H#j#)G#j#*F#j#7S$#j#9L#WS4s$r#EZS5Qs&Gs%L#KCj#:s&K#j#$Q#j#%Q##"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint A_pages (A : list (Z * Z)) : list Z :=
  match A with
  | [] => []
  | iv :: r =>
      map (fun i => (fst iv + page_size * Z.of_nat i)%Z)
          (seq 0 (Z.to_nat ((snd iv - fst iv) / page_size)))
      ++ A_pages r
  end.

Lemma Zmod0_multiple : forall a, (a mod page_size = 0)%Z -> exists q, a = (page_size * q)%Z.
Proof.
  intros a Ha. exists (a / page_size)%Z.
  pose proof (Z.div_mod a page_size ltac:(unfold page_size; lia)) as Hdm.
  rewrite Ha, Z.add_0_r in Hdm. exact Hdm.
Qed.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Logic.ex Sort Prop.

Lemma A_pages_length : forall A,
  A_wf A -> (Z.of_nat (length (A_pages A)) * page_size = A_bytes A)%Z.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.A_wf); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.A_pages); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.A_bytes); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__3); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Lists.ListDef.seq); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@kc__4); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Nat.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.Zmod0_multiple); constr:(@Corelib.Init.Logic.ex); constr:(@kc__5); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.ZArith.BinInt.Z.eq_decidable); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.Znat.Z2Nat.id); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.ZArith.BinInt.Z.div_mul); constr:(@Stdlib.ZArith.BinInt.Z.mul_add_distr_r); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.Lists.List.length_seq); constr:(@Stdlib.Lists.List.length_map); constr:(@Stdlib.Lists.List.length_app); constr:(@kc__3 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)); constr:(@kc__5 (@Corelib.Numbers.BinNums.Z))|] [|@A; @Hwf; @l; @p; @iv; @i; @e; @H0; @H; @Hwf'; @Hhi; @Hlo; @Hle; @n; @z; @q; @lo; @hi; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @H10; @H9; @IH; @r0; @q0; @H8; @H7; @H6; @H5; @H4; @r; @H3; @H2; @H1; @__sat0; @__sat1; @cstr; @__x4; @__x5; @__x6; @__x7; @__p1; @__p2; @__p3; @__p4; @qhi; @x; @qlo; @a|] "#9H#d$f$C#i#q$J#}$K$I###$#%$T$$#'#/#&#*#(#)$S#0#1#+#-#,$'#d#.#3#2$-#4#;#D#A#B$j#g#8#:#<#@#E#6#7#9#=#C#5#?#G#H#K#b$P$3#s$+$2#>$5#F#J#L#R#O$8$N$W$X#c$^$f$i$m$n$7$0$1#h$,$.$/#I#M#N#P#Q#a$F$H$U$Y$Z$V#S$b$a$`$]$\$c$d$h$[$o$p$q$r$s$t#u#j#v#l#m#|$%#y#n$e$)#w#x$L$G$*$=#o#r#p#{$($Q#z$M#k$O$&$##~$B$E$D$;#t$6$9$:$<$>$?$@$A$g$l$k$4$R$_T$7&$8&$9%$:%$;%$<%$=$$>+$?%$@'$A%$B'$C*$D%$E%$F%$G$$H$$I&$J$$K$$L&#Y)$M&$N$$O%$P%$Q'$R&#p&$S%$T%$U'$V$$W%$X%$Y%$Z%$[%$\%$]%$^%$_%$`)$a)$b*$c%$d$$e$VSaDDUS7#;J4K2D#)#%#E3K$D$#k##)#j#$+#USJ-;#3$ED#j#%%##2LK;##4QL4#2D#)#%#E3'$D$#k##*#k##3#k#&<#j#'>#,DDQL#@#K;#8DDJ5DDJ($#&%E$D#G&&E$D#G-%#-(#j#(s#+#,DDS$S##s#-#O$s#-K#)J%E#'S(#j#)N#0S$R+#E6#=S+#>ND'#4S#?D$#2D#)#%#E3S#'-#$D%#k##4#,DDOQ#s#B#L$s#Bs#8#,DDS#O#s#E#Q$s#Es#;#nS7$s#G$#&S,J#%#Sb%####S0j#*s#G#ZSKs#Hs#>#Sc>JVSd-Jl#+$S0#j#,(#U#Jj#,-#8DDK5DDK($#&%E$D#G&&E$D#G-%#-(#8DDL5DDL($#&%E$D#G&&E$D#G-%#-(#@s#as#8L#s#bOQ,DDS&P#s#d#S-$s#d%#'S/s#8j#)N#0S&S'+#E6#=S+#>ND'#4P?D$#2D#)#%#E3P'-#$D%#k##2#k##7#j##9#8DDQ&#E$D#G5DDQ&#E$D#G-&#8DDO5DDO($#8DDS#&#E$D#G5DDS#&#E$D#G-&#8DDS$&#E$D#G5DDS$&#E$D#G-&#@s$4s#gS$#s$5S(R,DDS1S.#s$7#S/$s$7%#'S=s#gj#)N#0S1SB+#E6#=S+#>ND'#4S.?D$#2D#)#%#E3S.'-#$D%#k##2#k##7#j##9#5DDR&#E$D#G8DDS(&#E$D#G5DDS*&#E$D#G@s$Ts$+S*#s$US-S),DDS>S=#s$W#SB$s$W%##s$YPS-,DDS8S>#s$[#S=$s$[%#nS7$s$]$#&s$\J#%#S&%#'#&Jj#*s$]##s$_S&P,DDS?S8#s$a#S>ZSLs$as$a&%#J$s$bPS>nS7$s$d$#&s$dJ#%#S/%#'#&Kj#*s$d##s$fS'S&,DDS9S?#s$h#S8ZSLs$hs$i&%#K$s$jS'%,DDS2S9$s$lS/#,DDS:S2$s$nS.#,DDS@S:$s$oS1S:@s$qs$HS8'S3s$Dj#)N#0S5SA+#E6#=S+#>ND'#4S4?D$#2D#)#%#E3S4'-#$D%#k#-2#k#.s#c#k#/s$)#k#0s$5#k##7#j#'s%*#$s%*S.S2,DDS;SC8DD#5DD$($#,DDS4S;8DD#&#E$D#G,DDS5S45DD#&#E$D#G@s%8s$kQ'S<s$gj#)N#0SAS3+#E6#=S+#>ND'#4S5?D$#2D#)#%#E3S5'-#$D%#k#-2#k#.4#k#/9#k#0>#j#&s%K#,DDSCSM8DD#5DD$($#&s#&E$D#G5DDs#%&#E$D#G@s%Vs%-S;2Ds#=2Ds#=Q$#%s%-E$D#7j#1N#2Ns#D2D@QJ#)#%#E$D#>j#1N#)s#L)/'$#%JE$D#s#$j#2D#%(E%(E'$#$DJs#)j#2D#)s#4%#E'#J$D#s#.j#2D#VSNSAL%EJ$DS3#j#3D#FD#$DS<&j#3D#FD#0S3S<+#E6#)#%#E3SA'$#')$$D$#j##,#$DSO3j#3D#U#J$DSD6%EK,DDJSE#s&0#SD;#(KSe&LE$D#G0SFQ+#E6#)#%#E3SP'$#')$$D$#k#/,#k#0/#k#%1#j#4D#,DD6SD#s&C#SO;#%EL(#SE%EQ&#E$D#GVSNSPS*$DSFs#4j#3D#FD#$DSQs#7j#3D#FD#%ES$0SQ#+#E6#)#%#E3SF'$#')$$D$#j##-#$DSfs#Ej#3D#U#J$DSgs#H%ES)(#J%ES-,DD#K#s&d#Sh;#%ES&0Q#+#E6#)#%#E3SR'$#')$$D$#k#.s#>#k#%.#k#03#j#5D#%ES*(#s#I,DD8s#3#s&w#SS;#4Si2D#UST#)$(G#G:E(G;(GE%ES/&#E(G#k##&#k##(#Gs#7E(Gs#8%ES(&#E(G#k##-#k##'#%ERH#E$DEGD#++E%E#'#,$D.#k##'#I0E1GE&s#&E(G#1$E-$#k##'#Js#+E1EG&s#AE1E#($G-$#k##'#Ks#FE+s#EE$D#Gk##:#Ls#HE%EP&#E$D#$k##?#+&E&s#JE%ES?H#E%ES9+#E%E#&%E'$#$D'#k##s#)#I)E%ES2&#E(G#1$E-$#k##s#)#J(E%ES:&#E1E#($G-$#k##s#)#K(E%ES@+#E$D#Gk##s#=#L&E%ESM&#E$D#$k##s#B#+&E%ESC&#EUSjS34SG2D#)#%#E3SG$D$#MS4L$DS4LD#A$#m#&#MS9S)$DS9S)D#A$#m#&#USJCUS7CBDLBDQCD$K#USkDUSlD<DSH7SH<D#WSUD%#RSH<D#:D%#:D$):D%(WSUD$#.D&S%#/.IFFH#MVSm/HESVSWVSnJL$SV#SWm$%#WSoDGKXSpJL$#l#6*)#l#798#l#8>=#j#9D#j#:D#j#;D#0JK%#L%LJ%LK0$#$D&#k#9D#k#:D#k#;D#WJES3S:l#<-$#l#=s#.s#/#l#>s#4s#5#l#?s#@s#:#l#@s#BD#l#As#ED#l#Bs#Ks#G#l#Cs#Qs#M#l#Ds#Ys#S#l#Es#as#[#l#Fs#js#c#l#Gs#mD#l#3s#oD#l#Hs#us#q#l#Is#zs#w#l#Js$&s#|#l#+s$.s$(#l#,s$7s$0#l#Ks$@s$:#l#Ls$Is$B#l#Ms$Ms$K#0OP%#E%EO0#s$#$D%#0S#S&%#E+JE6#)#%#E3Sq'$#'J$$D$#j#2D#6J)#%#E'#*0S$S'%#E'#-$D&#j#2D#'s%{0$D#&j#2D#'8s$yED#6;)#4SR2D#UST#)$(G#%ES'G#E(G$%ES.&#E(G#k##s$t#k##'#Gs$iE(Gs$jk##s$xs$_k##$#Hs$rE+s%+E%E#'#s$e$Ds%.#k##s$o#Is%0E(Gs$b1s$cE-$#k##s$m#Js%IE&s%HE1E#($G-$#k##s$l#Ks%ME$Ds$_Gk##s$~#Ls$eE$Ds$as%Mk##s%%#+s%OE&s#&EHs$bE+s$[E%E#'#s$\$Ds$^#k##s%,#Is$`E(Gs$Y1s$ZE-$#k##s%*#Js$^E&s$XE1E#($G-$#k##s%)#Ks$]E$Ds$UGk##s%;#Ls$[E$Ds$Vs$Wk##s%>#+s$YE%ES;&#EUSGS<4SX2D#)#%#E3SX$D$#MS5L$DS5LD#A$#m#&#MS2S)$DS2S)D#A$#m#&#SS+S#S#VSYD#7s$V7#7#7#7#7#7#7#7#7#7#USr#VSsD#VSYDS+WStD$#WSuD2#VSv#Sw#C#s$o#C$##C%##C&##C'##C(##C)##C*##C+##C,##C-##C.##C/##C0##C1##C2##C3##C4##C5##C6##C7##C8##C9##C:##C;##C<##C=##C>##C?##C@##CA##CB##Cs####Cs#$##Cs#%##Cs#&##Cs#'##Cs#(##Cs#)##Cs#*##Cs#+##Cs#,##Cs#-##Cs#.##Cs#/##Cs#0##Cs#1##Cs#2##Cs#3##Cs#4##Cs#5##Cs#6##Cs#7##Cs#8##Cs#9##Cs#:##Cs#;##Cs#<##Cs#=##Cs#>##Cs#?##Cs#@##Cs#A##Cs#B##Cs#C##Cs#D##Cs#E##Cs#F##Cs#G##Cs#H##Cs#I##Cs#J##Cs#K##Cs#L##Cs#M##Cs#N##Cs#O##Cs#P##Cs#Q##Cs#R##Cs#S##Cs#T##Cs#U##Cs#V##Cs#W##Cs#X##Cs#Y##Cs#Z##Cs#[##Cs#\##Cs#]##Cs#^##Cs#_##Cs#`##Cs#a##Cs#b##Cs#c##Cs#d##Cs#e##Cs#f##Cs#g##Cs#h##Cs#i##Cs#j##Cs#k##Cs#l##Cs#m##Cs#n##Cs#o##Cs#p##Cs#q##Cs#r##Cs#s##Cs#t##Cs#u##Cs#v##Cs#w##Cs#x##Cs#y##Cs#z##Cs#{##Cs#|##Cs#}##Cs#~##Cs$###Cs$$##Cs$%##Cs$&##Cs$'##Cs$(##Cs$)##Cs$*##Cs$+##Cs$,##Cs$-##Cs$.##Cs$/##Cs$0##Cs$1##Cs$2##Cs$3##Cs$4##Cs$5##Cs$6##Cs$7##Cs$8##Cs$9##Cs$:##Cs$;##Cs$<##Cs$=##Cs$>##Cs$?##Cs$@##Cs$A##Cs$B##Cs$C##Cs$D##Cs$E##Cs$F##Cs$G##Cs$H##Cs$I##Cs$J##Cs$K##Cs$L##Cs$M##Cs$N##Cs$O##Cs$P##Cs$Q##Cs$R##Cs$S##Cs$T##Cs$U##Cs$V##Cs$W##Cs$X##Cs$Y##Cs$Z##Cs$[##Cs$\##Cs$]##Cs$^##Cs$_##Cs$`##Cs$a##Cs$b##Cs$c##Cs$d##Cs$e##Cs$f##Cs$g##Cs$h##Cs$i##Cs$j##Cs$k##Cs$l##Cs$m##Cs$n##Cs$o##Cs$p##Cs$q##Cs$r##Cs$s##Cs$t##Cs$u##Cs$v##Cs$w##Cs$x##Cs$y##Cs$z##Cs${##Cs$|##Cs$}##Cs$~##Cs%###Cs%$##Cs%%##Cs%&##Cs%'##Cs%(##Cs%)##Cs%*##Cs%+##Cs%,##Cs%-##Cs%.##Cs%/##Cs%0##Cs%1##Cs%2##Cs%3##Cs%4##Cs%5##Cs%6##Cs%7##Cs%8##Cs%9##Cs%:##Cs%;##Cs%<##Cs%=##Cs%>##Cs%?##Cs%@##Cs%A##Cs%B##Cs%C##Cs%D##Cs%E##Cs%F##Cs%G##Cs%H##Cs%I##Cs%J##Cs%K##Cs%L##Cs%M##Cs%N##Cs%O##Cs%P##Cs%Q##Cs%R##Cs%S##Cs%T##Cs%U##Cs%V##Cs%W##Cs%X##Cs%Y##Cs%Z##Cs%[##Cs%\##Cs%]##Cs%^##Cs%_##Cs%`##Cs%a##Cs%b##Cs%c##Cs%d##Cs%e##Cs%f##Cs%g##Cs%h##Cs%i##Cs%j##Cs%k##Cs%l##Cs%m##Cs%n##Cs%o##Cs%p##Cs%q##Cs%r##Cs%s##Cs%t##Cs%u##Cs%v##Cs%w##Cs%x##Cs%y##Cs%z##Cs%{##Cs%|##Cs%}##Cs%~##Cs&###Cs&$##Cs&%##Cs&&##Cs&'##Cs&(##Cs&)##Cs&*##Cs&+##Cs&,##Cs&-##Cs&.##Cs&/##Cs&0##Cs&1##Cs&2##Cs&3##Cs&4##Cs&5##Cs&6##Cs&7##Cs&8##Cs&9##Cs&:##Cs&;##Cs&<##Cs&=##Cs&>##Cs&?##Cs&@##Cs&A##Cs&B##Cs&C##Cs&D##Cs&E##Cs&F##Cs&G##Cs&H##Cs&I##Cs&J##Cs&K##Cs&L##Cs&M##Cs&N##Cs&O##Cs&P##Cs&Q##Cs&R##Cs&S##Cs&T##Cs&U##Cs&V##Cs&W##Cs&X##Cs&Y##Cs&Z##Cs&[##Cs&\##Cs&]##Cs&^##Cs&_##Cs&`##Cs&a##Cs&b##Cs&c##Cs&d##Cs&e##Cs&f##Cs&g##Cs&h##Cs&i##Cs&j##Cs&k##Cs&l##Cs&m##Cs&n##Cs&o##Cs&p##Cs&q##Cs&r##Cs&s##Cs&t##Cs&u##Cs&v##Cs&w##Cs&x##Cs&y##Cs&z##Cs&{##Cs&|##Cs&}##Cs&~##Cs'###Cs'$##Cs'%##Cs'&##Cs''##Cs'(##Cs')##Cs'*##Cs'+##Cs',##Cs'-##Cs'.##Cs'/##Cs'0##Cs'1##Cs'2##Cs'3##Cs'4##Cs'5##Cs'6##Cs'7##Cs'8##Cs'9##Cs':##Cs';##Cs'<##Cs'=##Cs'>##Cs'?##Cs'@##Cs'A##Cs'B##Cs'C##Cs'D##Cs'E##Cs'F##Cs'G##Cs'H##Cs'I##Cs'J##Cs'K##Cs'L##Cs'M##Cs'N##Cs'O##Cs'P##Cs'Q##Cs'R##Cs'S##Cs'T##Cs'U##Cs'V##Cs'W##Cs'X##Cs'Y##Cs'Z##Cs'[##Cs'\##Cs']##Cs'^##Cs'_##Cs'`##Cs'a##Cs'b##Cs'c##Cs'd##Cs'e##Cs'f##Cs'g##Cs'h##Cs'i##Cs'j##Cs'k##Cs'l##Cs'm##Cs'n##Cs'o##Cs'p##Cs'q##Cs'r##Cs's##Cs't##Cs'u##Cs'v##Cs'w##Cs'x##Cs'y##Cs'z##Cs'{##Cs'|##Cs'}##Cs'~##Cs(###Cs($##Cs(%##Cs(&##Cs('##Cs((##Cs()##Cs(*##Cs(+##Cs(,##Cs(-##Cs(.##Cs(/##Cs(0##Cs(1##Cs(2##Cs(3##Cs(4##Cs(5##Cs(6##Cs(7##Cs(8##Cs(9##Cs(:##Cs(;##Cs(<##Cs(=##Cs(>##Cs(?##Cs(@##Cs(A##Cs(B##Cs(C##Cs(D##Cs(E##Cs(F##Cs(G##Cs(H##Cs(I##Cs(J##Cs(K##Cs(L##Cs(M##Cs(N##Cs(O##Cs(P##Cs(Q##Cs(R##Cs(S##Cs(T##Cs(U##Cs(V##Cs(W##Cs(X##Cs(Y##Cs(Z##Cs([##Cs(\##Cs(]##Cs(^##Cs(_##Cs(`##Cs(a##Cs(b##Cs(c##Cs(d##Cs(e##Cs(f##Cs(g##Cs(h##Cs(i##Cs(j##Cs(k##Cs(l##Cs(m##Cs(n##Cs(o##Cs(p##Cs(q##Cs(r##Cs(s##Cs(t##Cs(u##Cs(v##Cs(w##Cs(x##Cs(y##Cs(z##Cs({##Cs(|##Cs(}##Cs(~##Cs)###Cs)$##Cs)%##Cs)&##Cs)'##Cs)(##Cs))##Cs)*##Cs)+##Cs),##Cs)-##Cs).##Cs)/##Cs)0##Cs)1##Cs)2##Cs)3##Cs)4##Cs)5##Cs)6##Cs)7##Cs)8##Cs)9##Cs):##Cs);##Cs)<##Cs)=##Cs)>##Cs)?##Cs)@##Cs)A##Cs)B##Cs)C##Cs)D##Cs)E##Cs)F##Cs)G##Cs)H##Cs)I##Cs)J##Cs)K##Cs)L##Cs)M##Cs)N##Cs)O##Cs)P##Cs)Q##Cs)R##Cs)S##Cs)T##Cs)U##Cs)V##Cs)W##Cs)X##Cs)Y##Cs)Z##Cs)[##Cs)\##Cs)]##Cs)^##Cs)_##Cs)`##Cs)a##Cs)b##Cs)c##Cs)d##Cs)e##Cs)f##Cs)g##Cs)h##Cs)i##Cs)j##Cs)k##Cs)l##Cs)m##Cs)n##Cs)o##Cs)p##Cs)q##Cs)r##Cs)s##Cs)t##Cs)u##Cs)v##Cs)w##Cs)x##Cs)y##Cs)z##Cs){##Cs)|##Cs)}##Cs)~##Cs*###Cs*$##Cs*%##Cs*&##Cs*'##Cs*(##Cs*)##Cs**##Cs*+##Cs*,##Cs*-##Cs*.##Cs*/##Cs*0##Cs*1##Cs*2##Cs*3##Cs*4##Cs*5##Cs*6##Cs*7##Cs*8##Cs*9##Cs*:##Cs*;##Cs*<##Cs*=##Cs*>##Cs*?##Cs*@##Cs*A##Cs*B##Cs*C##Cs*D##Cs*E##Cs*F##Cs*G##Cs*H##Cs*I##Cs*J##Cs*K##Cs*L##Cs*M##Cs*N##Cs*O##Cs*P##Cs*Q##Cs*R##Cs*S##Cs*T##Cs*U##Cs*V##Cs*W##Cs*X##Cs*Y##Cs*Z##Cs*[##Cs*\##Cs*]##Cs*^##Cs*_##Cs*`##Cs*a##Cs*b##Cs*c##Cs*d##Cs*e##Cs*f##Cs*g##Cs*h##Cs*i##Cs*j##Cs*k##Cs*l##Cs*m##Cs*n##Cs*o##Cs*p##Cs*q##Cs*r##Cs*s##Cs*t##Cs*u##Cs*v##Cs*w##Cs*x##Cs*y##Cs*z##Cs*{##Cs*|##Cs*}##Cs*~##Cs+###Cs+$##Cs+%##Cs+&##Cs+'##Cs+(##Cs+)##Cs+*##Cs++##Cs+,##Cs+-##Cs+.##Cs+/##Cs+0##Cs+1##Cs+2##Cs+3##Cs+4##Cs+5##Cs+6##Cs+7##Cs+8##Cs+9##Cs+:##Cs+;##Cs+<##Cs+=##Cs+>##Cs+?##Cs+@##Cs+A##Cs+B##Cs+C##Cs+D##Cs+E##Cs+F##Cs+G##Cs+H##Cs+I##Cs+J##Cs+K##Cs+L##Cs+M##Cs+N##Cs+O##Cs+P##Cs+Q##Cs+R##Cs+S##Cs+T##Cs+U##Cs+V##Cs+W##Cs+X##Cs+Y##Cs+Z##Cs+[##Cs+\##Cs+]##Cs+^##Cs+_##Cs+`##Cs+a##Cs+b##Cs+c##Cs+d##Cs+e##Cs+f##Cs+g##Cs+h##Cs+i##Cs+j##Cs+k##Cs+l##Cs+m##Cs+n##Cs+o##Cs+p##Cs+q##Cs+r##Cs+s##Cs+t##Cs+u##Cs+v##Cs+w##Cs+x##Cs+y##Cs+z##Cs+{##Cs+|##Cs+}##Cs+~##Cs,###Cs,$##Cs,%##Cs,&##Cs,'##Cs,(##Cs,)##Cs,*##Cs,+##Cs,,##Cs,-##Cs,.##Cs,/##Cs,0##Cs,1##Cs,2##Cs,3##Cs,4##Cs,5##Cs,6##Cs,7##Cs,8##Cs,9##Cs,:##Cs,;##Cs,<##Cs,=##Cs,>##Cs,?##Cs,@##Cs,A##Cs,B##Cs,C##Cs,D##Cs,E##Cs,F##Cs,G##Cs,H##Cs,I##Cs,J##Cs,K##Cs,L##Cs,M##Cs,N##Cs,O##Cs,P##Cs,Q##Cs,R##Cs,S##Cs,T##Cs,U##Cs,V##Cs,W##Cs,X##Cs,Y##Cs,Z##Cs,[##Cs,\##Cs,]##Cs,^##Cs,_##Cs,`##Cs,a##Cs,b##Cs,c##Cs,d##Cs,e##Cs,f##Cs,g##Cs,h##Cs,i##Cs,j##Cs,k##Cs,l##Cs,m##Cs,n##Cs,o##Cs,p##Cs,q##Cs,r##Cs,s##Cs,t##Cs,u##Cs,v##Cs,w##Cs,x##Cs,y##Cs,z##Cs,{##Cs,|##Cs,}##Cs,~##Cs-###Cs-$##Cs-%##Cs-&##Cs-'##Cs-(##Cs-)##Cs-*##Cs-+##Cs-,##Cs--##Cs-.##Cs-/##Cs-0##Cs-1##Cs-2##Cs-3##Cs-4##Cs-5##Cs-6##Cs-7##Cs-8##Cs-9##Cs-:##Cs-;##Cs-<##Cs-=##Cs->##Cs-?##Cs-@##Cs-A##Cs-B##Cs-C##Cs-D##Cs-E##Cs-F##Cs-G##Cs-H##Cs-I##Cs-J##Cs-K##Cs-L##Cs-M##Cs-N##Cs-O##Cs-P##Cs-Q#BDS$USxDCD$Q#BDOCD$L#BDRCD#R'BDS#CD$R#CD'K#<Ds-k.Ds/fS%#/s/hIFFH#MNs/iIFFH#[SZs/jIFFH$#USyFRs-r<D#.Ds/kS%#/s/oIFFH#MNs/pIFFH#[SZs/qIFFH$#<Ds-xVS[DG.D$S%#/s/uIFFH#M7s/q<D#:D(s/u.D$S%#/s/zIFFH#M*s/{IFFH(2#.D1S%+/s/}IFFH#M*s/~IFFH+5#.D/S6./s0$IFFH#M.D1S6,/s0&IFFH#MOs0'IFFHS*Ps0(IFFH$#*s0)IFFH'<#.D5S66/s0+IFFH#MOs0,IFFHS).D4S69/s0.IFFH#MPs0/IFFH%#*s00IFFH's###Ns01IFFH::D>s##WS\D#:.D:S%#/s05IFFH#M*s06IFFH's#)#Rs02<D#:Ds#%s08.D$S%#/s0;IFFH#M*s0<IFFHs#%s#/#.Ds#5S%s#(/s0>IFFH#M*s0?IFFHs#(s#2#.Ds#,S6*/s0AIFFH#MOs0BIFFHS-Ps0CIFFH$#*s0DIFFHBs#7#Os0EIFFHP.D0S6s#2/s0GIFFH#MPs0HIFFH%#*s0IIFFH@s#<#:Ds#6s#BWS\D#5.D5S%#/s0MIFFH#M*s0NIFFH?s#A#VS[Ds.J:D#s0M:D$s0P.D$S]#/s0SIFFH#M.D>S%s#?/s0UIFFH#M.Ds#=S%s#A/s0WIFFH#M.Ds#CS]s0T/s0YIFFH#M*s0ZIFFH%s#M#*s0[IFFH(s#N#*s0\IFFH+s#O#*s0]IFFH1s#P#*s0^IFFH7s#Q#*s0_IFFH=s#R#*s0`IFFHs##s#S#*s0aIFFHs#'s#T#*s0bIFFHs#.s#U#*s0cIFFHs#5s#V#*s0dIFFHs#=s#W#*s0eIFFHs#Es#X#*s0fIFFHs#Is#Y#*s0gIFFHs#Ts#Z#*s0hIFFHs#\s#[#l#6#s0\s0Vl#7s#cs0k#l#8s#ns0p#j#9D#j#:D#j#;D#j#ND#j#OD#j#PD#j#QD#j#RS,#j#SS,#j#TS,#j#US,#$DJS#k###S0A$#$DLRk###S0A$#$DOG%S#O$DS$#k##%#$DS#G$DS)Gk##$#1S$G1RS(-#Pk##%#1GR1S*S(-S'#k##%#$DS(Gk###S0%S*S(%S*S&'#S)$D%#k##'#$DS*G%S)S($DP#k##%#$DS'Gk##8#1S-G1PS'-#S=k##%#1GP1S/S&-S8#k##%#$DS&Gk###S0%S'P%S'S1'#S.$D%#k##'#%s/GS&%s/HP($#$DS1G0S/S.(G#k##%#k##&#k##(#k##,#k##4#k##9#k##>#k##A#k##s#&#k##s#.#k##s#3#k##s#8#k##s#<#k##s#A#k##s#E#k#9D#k#:D#k#;D#k#ND#k#OD#k#PD#k#QD#k#RS,#k#SS,#k#TS,#k#US,#(GS-(S-G(GO(OGi#=J&%$#S#PS-OES<S@KLS$RS(S*S)S&S'S/S.S1S2S?S4l#<s#Y(#l#=s/}s/~#l#>s0's0(#l#?s03s0-#l#@s05D#l#As08D#l#Bs0<s0:#l#Cs0@s0>#l#Ds0Gs0B#l#Es0Ms0I#l#Fs0Ts0O#l#Gs0VD#l#3s0XD#l#Hs0\s0Z#l#Is0`s0^#l#Js0gs0b#l#+s0ms0i#l#,s0ts0o#l#Ks0ys0v#l#Ls1%s0{#l#Ms1*s1(#VSzs1H#9Ds1Is13s11s1/#+s1IE.Ds$<S%s$t/s2.IFFH#MNs2/IFFH#l#6#s2#s1yl#7s%2s22#l#8s28s27#$Ds0.Gk###S0l#<%#Jm##s34WS{s1UE#9Ds1Vs1C/.#%ES#0#s3bZSKDs1Xs1O%#Jl#,s1`s1[#j#.s4&#j#%s3T#j#0s3X#]SIDs4Ds3[#SSJS$RS'j#,s3p#j#VD#V#KJj##s3t#j#WD#YS^Ds4)s3y#Jl#*s4/s4,#j#/s41#j#0s45#j#%s48#]SIDs4Os4<#SEJS3S(Rj#,s4Q#j#XD#V#KJj##s4U#j#WD#YS^Ds4es4Z#Jl#*s4ls4h#US;J9Ds5ds4o$s4w#%s4}EWS|s5$s5#E9Ds4ys4w%$#Qs5ps52)#VS}s5rs549Ds5's5$&$#VS~s5tS+9Ns5us5,$s52#XT#NDs5ys5u9Ns54s5.$s5:#WT$Ds5vs5u9Ns5:s57$s5t#m##s5pj#-s5?#j#.s5A#j#/s5E#j#0s5H#9s8:S@s5M#SBJl#JJs6*#j#+s5p#9s8>s6-s5r#S1Jl#+Js6/#j#,s62#U#Jl#+s67s66#U#Jl#+s6@s6?#j#,s6G#Y#JRQLKj#,s6M#j#-s6R#j#.s6T#j#/s6X#V#KJj##s6]#j##s6|#YS_s6}s6zs6b#Jj#,s7%#j#0s7-#V#KJj##s72#j##s7W#YS_s7Xs7Ss7;#Jj#,s7\#j#&s8U#j#Ws8W#X#QLKJnS`%s8Ys80%#&##s7wJ#%#s7i'#W#&#####$s8YJs7s'Rs8-j#)N#0S#S$+#E6#=S+#>ND'#4O?D$#2D#)#%#E3O'-#$D%#k##2#j#&s8j#U#s8,Es8ls8*UJ#l#,8%#4s802D#)#%#E3s84$D$#m#)#j#%s8X#j#?s8o#j#$s8x#j#5D#j#4D#V#KJj#2D#j#2D#YT%DDs8c#Jj#Ys9$#YT&s9%s8ws8r#Jj#$s9%##"). Qed.
Scheme kc__6 := Elimination for Corelib.Init.Logic.or Sort Prop.

Lemma A_pages_in : forall A p,
  A_wf A ->
  (bv_unsigned p mod page_size = 0)%Z ->
  page_allowedb A p = true ->
  In (bv_unsigned p) (A_pages A).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.A_wf); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.page_allowedb); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.A_pages); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@kc__3); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@kc__4); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.Lists.List.in_or_app); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Lists.ListDef.seq); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.Bool.Bool.orb_true_iff); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.Lists.List.existsb); constr:(@kc__6); constr:(@Corelib.Init.Logic.or_introl); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.Zmod0_multiple); constr:(@Corelib.Init.Logic.ex); constr:(@kc__5); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.ZArith.BinInt.Z.eq_decidable); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); (KReplay.sort_at constr:(@Stdlib.Lists.List.count_occ_map) [0]); (KReplay.sort_at constr:(@Stdlib.Lists.List.count_occ_map) [1; 0]); constr:(@Stdlib.Lists.List.in_map_iff); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.ZArith.Znat.Z2Nat.id); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Nat.add); constr:(@Stdlib.Lists.List.in_seq); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.ZArith.BinInt.Z.div_mul); constr:(@Corelib.Init.Logic.or_intror)|] [|@p; @A; @b; @e; @H; @Hpa; @Hal; @Hwf; @l; @iv; @H0; @Hwf'; @Hhi; @Hlo; @Hle; @i; @b2; @b1; @m; @n; @q; @z; @lo; @hi; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @H18; @H17; @H16; @r1; @q1; @H15; @H14; @H13; @H12; @H11; @r0; @q0; @H10; @H9; @H8; @H7; @H6; @r; @H5; @H4; @H3; @__sat3; @__sat4; @__sat5; @x; @y; @f; @B; @__x4; @__x5; @__x6; @__x7; @__x8; @__x9; @start; @len; @__x10; @__x11; @__p1; @__p2; @H20; @H19; @__sat6; @__sat7; @z4; @z3; @H2; @H1; @Eqp; @qp; @Eqhi; @qhi; @Eqlo; @qlo; @IH; @a|] "#6y#m%>#r#|$`#}###$$a$_#%$:#~#&$$#'$h#($?$g#4#)#,#*#+$Y#2#1#G#-#0#.#/#;#F$=#H#3#5#E#D#N#:#?#J#M#R#W#p#m#7#6#8#<#>#I#K#U$~%&$)#9#=#@#B#C#L#Q#O#X#\#P$d$f$k$|$z%;#w#A#f#i%'%($C$H$M#V#Z#[#_#d#g#h$s#S%)$@%7%<$O$'$*$+$,$6#T#a#`#e#c#k#l$o$n$v${%0%1%.$1$;$T%6%9%8%=%:$5#q#u#t$E$K$L#Y#]#^#b#j$\$^$i$l$m$j$p$t%$%%$w%*%/%3%4%5%2%-%+$r$q%>$J%?$I$8$-#s#y$<#z$0#v$.$A$%#{$B$/$b$]%#$G$D$>$9$($Z$c$3$e$&$2$R$y$F$P$Q$S$U$V$W$X$u#x$4$N$[$}$7$x%,$#U$m&$n%$=%$o%$p%$>%$q$$r&$s%$t&$u%$v%$?%$w'$x'$y*$z+${%$|%$}%$&$$~'%#)%$'%%&%&&%'%%($%)&%*$%+&%,%%-%%.%%/%%0%%1%%2%%3%%4&%5$%6(%7%%8%%9$%:)$E&%;%%<%%=%VT6CCUSA#)S_)#)#)#)#)#UT7#UT8#KH-%H&#D#C#FTNK#M#O-*N>P,C$#k##&#k##)#k##-#k#$/#j#%8#USv:K#T$K#M#OT&NnM#$#&SBG#%#SM#Swj#'M#9M%#SxOG-:P>+,C$#VSy#Gl#('SM#j#),#j#*;#j#+0#j#$A#*s#+NKK#*s#-RPT#K#M#O*s#0S&R>#,CB#k##&#k##s#'#k##+#k#$s#-#k##A#k#,s#7#j#$s#9#0CCPN*s#;#KK#0CCS&R*s#>#PT#K#M#O?CCG<CCG%$#&%D#C#F&&D#C#F'%#'(#j#-s#J#0CCS'S)*s#L#S(#s#LH#-s#FS&0CCS.S'*s#P#S)>#,C&#k##(#0CCS(S&*s#U#R#s#Us#>#0CCS)S(*s#X#S&#s#Xs#A#nSA$s#Z$#,SBG#%#Sw%####SMj#'s#Z#9s#[s#D#Sx2GVSy-Gl#.$SM#j#((#U#Gj#(-#?CCH<CCH%$#&%D#C#F&&D#C#F'%#'(#?CCK<CCK%$#&%D#C#F&&D#C#F'%#'(#Qs#ts#,K*s#uPN0CCS6S+*s#w#S,#s#w%#-s#qS/0CCS%S6*s#{#S+>#,C&#k##(#k##-#j##/#?CCN&#D#C#F<CCN&#D#C#F'&#?CCP<CCP%$#?CCR&#D#C#F<CCR&#D#C#F'&#?CCS&&#D#C#F<CCS&&#D#C#F'&#Qs$=s#QS&*s$>S)S(0CCSCSD*s$@#S7#s$@%#-s$:S%0CCSESC*s$D#SD>#,C&#k##(#k##-#j##/#<CCS(&#D#C#F?CCS)&#D#C#F<CCS'&#D#C#FQs$Ss#gS'*s$TS0S.0CCS;SN*s$V#SE#s$V%#*s$XS1S00CCS2S;*s$Z#SN#s$Z%#nSA$s$\$#,s$[G#%#S/%#$#,Gj#'s$\#*s$^S/S10CCSFS2*s$`#S;ZSzs$`s$`&%#G#s$aS1S;nSA$s$c$#,s$cG#%#S+%#$#,Hj#'s$c#*s$eS,S/0CCSOSF*s$g#S2ZSzs$gs$h&%#H#s$iS,%0CCSGSO#s$kS+#0CCS<SG#s$mS6#0CCSPS<#s$nS%S<Qs$ps$(SE-s$iSQ0CCS3S8*s$s#S9>#,C&#k#/(#k#0s#O#k#1s#g#k#2s#s#k##-#j#$s${##s${S6SG0CCSRSQ?CC#<CC$%$#0CCS9SR?CC#&#D#C#F0CCS8S9<CC#&#D#C#FQs%-s$AN-s%&SR0CCS-S3*s%0#S8>#,C&#k#/(#k#0*#k#1/#k#24#j#,s%6#0CCSQS`?CC#<CC$%$#&<D#C#F<CC;&#D#C#FQs%As$USRUS4G$D#(S-#j#3L#.S8S3+#D7#6S##8LC'#>S9VSeHG#M#O#MKO#MHO5$#k##&##MGO5&#VSeKH#M#Ok##%#'(##MNO5#-k##'#j##&#VSeNK#M#Ok##0#j###Hj##1#VT9HGL3.)$#j#4M#j#5M#k#4M6k#5M#4S-s#;(s#<D4#S3B%#-s%cS94s%-#($D4#s%.B%#j#-s%p#WSfs%q#S8WG*#SP#M+O#M%O5$#4S5-4,S-B$##M#O-s%rS84s%<#($D4#s%=B%#j#-s&##WSfs&$#S3#M#O5+#(S=s#Bj#3L#.S5SH+#D7#6S##8LC'#,C2#>S-,C4#5%#j##.#4SH746S5B$##M#O-s&/S3(SIs#Sj#3L#.SHS=+#D7#6S##8LC'#,C*#>S5,C,#BHG#M#O's#Ts#Sk##$#'s#Us#RBKH#M#Ok##%#''#'s#Qs#[k##&#j##%#BNK#M#Ok##.#j###Hj##/#VT:HGL1-)$#j#4M#j#5M#k#4M4k#5M#-s&QS-4SI#($D4#S=WG%#H#M&O#M%O'$#-s&YS54SS##M#O(%D4#SI#M#O'&#-s&`SH(S:s$(j#3L#.SSS>+#D7#6S##8LC'#,C*#j##,#(,D4#SS#M#O-s&mS=4S:##M#O-s&pSI(#D4#S:#M#O4HG#M#O%KHk##$#%HG4KH#M#Ok##%#''#%NKk##&#j##%#4NK#M#Ok##.#j###Hj##/#VT;HGL1-)$#j#6C#j#7C#k#6C4k#7C#-s'/S>WGST#K%ST$-s'2SU(#DWG#S?N%$S?VSgS{S6$DG#CSJ#j#8C#MC##CSh&j#8C#MC#-s'>S?(S@s$bj#3L#.SJSh+#D7#6S##8LC'#,C*#j##,##CS@3j#8C#U#G#CSV6VSgSVSC#CT<8j#8C#MC##CSi;j#8C#MC#-s'SS@(SWs$wj#3L#.SiSj+#D7#6S##8LC'#,C*#j##,##CSjs#(j#8C#U#G#CSWs#+-s'aSiVSg#SV-s'cSj#C#s#/j#8C#MC#-s'gSW#C#s#3j#8C#MC#(S|s%2j#3L#.SkS}+#D7#6S##8LC'#,C-#j##+#-s'tT=#C#s#@j#8C#U#G-s'xT>#C#s#D$DH(S~s%Bj#3L#.T#Sl+#D7#6S##8LC'#,CG#j#9C#-s((Sk(GD%#T#j#9C#9C&#S+0G(1D%#T?-s(/S}%S~Gj#9C#$DK9C&$S7#H%Sl$-s(5S|&GD#C#Fj#9C#$DN9C'$Sk#K&$D#C#F$DS,$DR(Hs%bj#3L#.SaG+#D7#6S##8LC'#,C*#j#:C#j#:C39CSa#S8.S/&/D#C#F%GSmj#:C#$DS+9CSm$S-#S,%$Sa$DS(%G#j#:C#$DS69CSn$N#S+$DS&%%#0CCGSb*s(a#SnK#j#:C#$DS%9CSb$Sl#S60CC$Sn*s(g#SmK#$DS/$DS'$DSC(#s&+j#3L#$DSD.G#+#D7#6S##8LC(#,C,#j#;C#j#;Cs#99CSb#S50S1&1D#C#F%1Gj#;C#9CT@#Ns#9S/%1s#:$DS0(#D%#Gj#;C#9CT$#S)s#.S,$DS.(#D%#s#1$DSN0CC#G*s),#T%K#j#;C#9CT%#Ns#1S+$DSE0CC#s#3*s)2#T$K#C,D%F-%FD$DS2&#D%F#k##&#k##(#Cs#1D%Fs#2&s#FD%F#k##,#k##&#Cs#2D%Fs#3&6D%F#k##2#k##&#Ds#;D#CDF@#+=D$D#(#+#C@#k##'#EBD/FD&s#*D%F#/$D'$#k##'#Fs#/D/DF$DS;&#D/D#%$F'$#k##(#G(D+s#+D#C#Fk##;#Hs#.D$DSF&#D#C#$k##@#+&D$DSO&#DDs#CD+5D$D#(#6#C8#k##s#(#E:D/s#<D's#<#k##s#%#Fs#@D/D3%4F'$#k##s###G8D+4D#C#Fk##s#6#H7D$DSG&#D#C#$k##s#;#+&D$DS<&#D$DS=D#D$DSI+#D$D#&%D($##C'#k##s#F#E)D$DSS&#D%F#/$D'$#k##s#F#F(D$DS>&#D/D#%$F'$#k##s#F#G(D$DS:+#D#C#Fk##s#Z#H&D$DSU&#D#C#$k##s#_#+&D$DSX&#DISTH#CSTH@#5$#m#&#IS5S'#CS5S'@#5$#m#&#IS:S%#CS:S%@#5$#m#&#USvS*USAS*NCKNCN:C$H#UTACUTBC=CS_=Cs*cWSYC$#USZS_=C#;C%#;C$(;C%(WSYC$#1C&S$#2-JEEI#QVTC.IVS[MOVTDGK#M#Om$%#WTECFHXTFGK$#l#<*)#l#=87#l#>=<#j#?C#j#@C#j#AC#.GH$#K$KG$KH.$##C&#k#?C#k#@C#k#AC#WGDSJSXl#B-$#l#Cs#-s#.#l#Ds#3s#4#l#Es#9s#:#l#Fs#?C#l#Gs#BC#l#Hs#Hs#D#l#Is#Ns#J#l#Js#Vs#P#l#Ks#^s#X#l#Ls#gs#`#l#Ms#jC#l#Ns#mC#l#Os#ss#o#l#Ps#xs#u#l#Qs#~s#z#l#Rs$'s$$#l#Ss$.s$)#l#Ts$0C#l#8s$3C#l#Us$9s$5#l#Vs$>s$;#l#Ws$Gs$@#l#.s$Os$I#l#(s$Xs$Q#l#Xs$_s$Z#l#Ys$fs$a#l#Zs$os$h#.S%SN$#D.s%Bs$|#C$#.S7S;$#D(s$Fs(gj#3L#+GD7#6S##8LC&#,Cs%k#j#9C#7G6S##8LC+#,Cs%p#j#9C#k##HHUSAK8PNKH,NG#UPG#R#K,S&GN'$#j#[R#MR#k##)#UNG#P#H,RGK'$#j#[P#MP#8RPNK,PH#k##%#',#8S&RPN,RK#k##0#j##&#j##$Gj##2#YTGPNKHGL4+&$#j#\K#j#,?#j#]A#j#^T&#j#%T'#k#\K1k#,s#$#k#]s#&#k#^T&#k#%T'#.SDS27#6S###Cs#9s&/.SCSF7#6S##,LG#''#j#[L#.S,S27#)s,))#)#)#)#)#USo#$#S2US4+$%#(%#$'S,#C$#,L09$*SF$+G($#$-S+#C$#j#9C#C/0%F0%F2$3SO&#4%F#k##&#k##(#C-8%F.$:S%&#;%F#k##-#k##'#$?SEC#@%F$$BS;&#s##%F#k##5#k##'#$s#'SND#s#(#Cs#)F@#++s#+$s#,#(#,#C.#k##'#E0s#0/Fs#1&s#1s#2%F#/$s#4'$#k##'#Fs#6s#7/s#8F&s#1s#9/s#:#%$F'$#k##'#Gs#6s#>+s#.s#?#C#Fk##:#Hs#1s#B$s#CSG&#s#D#C#$k##?#+&s#G$s#HS<&#s#IDs#Is#J+s#Cs#K$s#L#(#6#Cs#F#k##s#'#Es#Hs#P/s#?s#Q's#?#k##s#$#Fs#Cs#T/s#U3%4F'$#k##B#G8s#Y+4s#Z#C#Fk##s#5#H7s#]$s#^SP&#s#_#C#$k##s#:#+&s#b$s#cS`&#s#d$s#eSSD#s#f$s#gS>+#s#h$s#i#&%s#j($##C'#k##s#E#E)s#n$s#oS:&#s#p%F#/$s#r'$#k##s#E#F(s#u$s#vSU&#s#w/s#x#%$F'$#k##s#E#G(s#|$s#}SX+#s#~#C#Fk##s#Y#H&s$%$s$&ST&#s$'#C#$k##s#^#+&s$*$s$+S?&#s$,ISpH#CSpH@#5$#m#&#IS=S'#CS=S'@#5$#m#&#ISXS%#CSXS%@#5$#m#&#UTHC:Cs%pH#VT(Cs$>;C#s%mWSYCs%ms%n;C%#JC%#;C's%p1C$S$#2s%tJEEI#Ql#<#s%is%cl#=,s%w#l#>s%}s%|#j#?C#j#@C#.HG$s$L#(s$D#$s$NH#C$#k#?C#k#@C#VGS>S@l#B+$#l#C;<#l#DAB#l#Es#'s#(#l#Fs#-C#l#Gs#0C#l#Hs#6s#2#l#Is#<s#8#l#Js#Ds#>#l#Ks#Ls#F#l#Ls#Us#N#l#Ms#XC#l#Ns#[C#l#Os#as#]#l#Ps#fs#c#l#Qs#ls#h#l#Rs#qs#n#l#Ss#xs#s#l#Ts#zC#l#8s#}C#l#Us$'s$##l#Vs$,s$)#l#Ws$4s$.#l#.s$<s$6#l#(s$Es$>#l#Xs$Ns$H#l#Ys$Ws$Q#l#Zs$`s$Y#)s$p)#)#)#)#)#)#)#)#)#)#)#USo#VT)C#OS#O#VS\C#WS]C&#)))#)#)#)#)#)#)#)#)#)#)#USo#VT)C#VS\CS#WS]C$#AC3#R#SK*S*#s&lNCS':Cs#[P#NCS(:C#S&s#]:C%K#NCRNCS):C#S's#a:C%N#:C'H#VT(CF1Cs#cS$#2s&sJEEI#QZTIs&tJEEI#UTJE)s&r)#=C#;Cs#j#USZs.}=C#JC%#1Cs#iS$#2s&~JEEI#Q3s'#JEEI-,#USZ(=C#;Cs#s#JC#s&~1Cs#tS$#2s')JEEI#Q3s'*JEEI43#=Cs/-;Cs#y#)1=C#;Cs#|#=C8JC$#1C(S$#2s'3JEEI#Q3s'4JEEI>=#1C'S$B2s'6JEEI#Q1C:S$s#$2s'8JEEI#Q1Cs$%SLs$)2s':JEEI#Q1Cs'6S$s#(2s'<JEEI#Q1Cs#*SLs':2s'>JEEI#Q3s'?JEEI%s#(#3s'@JEEI(s#)#3s'AJEEI+s#*#3s'BJEEI.s#+#3s'CJEEI1s#,#3s'DJEEI<s#-#3s'EJEEIs#$s#.#l#<#s':s'4l#=s#5s'H#l#>s#@s'M#j#?C#j#@C#j#AC#j#_C#j#`C#j#aC#j#bC#j#cC#j#dC#k##s%XSM$s&$K$s&%S'(#R#C%#k##'#(&P#C(#k##*#$s&,S&(*S)#C$#k##.##CS)F$s&1R%(#.S(S)%F#k##'#k##&#k##)#k##*#k##,#k##1#k##5#k#?C#k#@C#k#AC#k#_C#k#`C#k#aC#k#bC#k#cC#k#dC#dGRS1SDS7PS?S0S@S>S.S%S2S9S5S3SHl#Bs#&$#l#Cs$js$k#l#Ds$ps$q#l#Es$vs$w#l#Fs$|C#l#Gs%#C#l#Hs%)s%%#l#Is%/s%+#l#Js%7s%1#l#Ks%?s%9#l#Ls%Hs%A#l#Ms%KC#l#Ns%NC#l#Os%Ts%P#l#Ps%Ys%V#l#Qs%_s%[#l#Rs%ds%a#l#Ss%ks%f#l#Ts%mC#l#8s%pC#l#Us%vs%r#l#Vs%{s%x#l#Ws&'s%}#l#.s&/s&)#l#(s&8s&1#l#Xs&As&;#l#Ys&Js&D#l#Zs&Ss&L#VTKs&j#PCs&ks&Vs$Ss&a#6HK,LG#VScKHVSqKNVSdH#'%#k##'#VScHGVSqHKVSdG#'%#6KN,LH#k##%#'*#6NP,LK#k##.#j##&#j##$Gj##0#WTLKHGL2+&$#j#7L#j#eL#j#fL#k#7L/k#eL#k#fL#.S+SF7#VScS##VSqS#s'5VSd%#'%#SF(%F#SFs';(F#/&#'&#VS[CFj#[CGSFGj#[C#VS[C2`T*CLCCSr&S4$T+33#`T,LCScS4T-TMS#F(3.#VS[Cs'F`T*CLCCSr)S4'T+s'Gs'G#fTNLLLCCCTOS4S4S4T.TPS#F+s'G/#`T,LCSdS4T/TQ72'5/#ZTR752/'#VT0Fs'K/Fs'L#C4s'M'$#%s'OF#C7F'$#5&#.SESOSF#.S%SGVT0F#/F$SF%#C#&'%#%(F#C&F'$#5&#.S7S<SF#Cs&Ss'S%Fs&T$s'USQ&#s'V%F#k##s'H#k##'#$s'ZSCC#s'[%F$&s'8s']%F#k##s'O#k##&#Cs'Ps'a%Fs'Q%Fs&xk##s'T#k##%#Ds'%s'f$s'gs&k(#s&}#Cs'##k##s'B#Es'%s'k%Fs&k/s&ls'm'$#k##s'@#Fs&ps'p/s'qs&k%s&lF'$#k##s'>#Gs&ps'u+s##s'v#C#Fk##s'Q#Hs#&s'y$s'zSR&#s'{#C#$k##s'V#+&s'~$s(#S9&#s($Ds'%s(%+s&}s(&$s('#(#s&~#Cs'$#k##s'^#Es'&s(+/s#4s(,'s#4#k##s'[#Fs#8s(//s(03%4F'$#k##s'Y#G8s(4+4s(5#C#Fk##s'l#H7s(8$s(9S8&#s(:#C#$k##s'q#+&s(=$s(>S3&#s(?Ds&xs(@+s&ts(A$s(B#(#s&u#Cs&w#k##s'y#Es&ys(F$s(GSp&#s(H%F#/$s(J'$#k##s'y#F(s(M$s(NS{&#s(O/s(P#%$F'$#k##s'y#G(s(T$s(USJ+#s(V#C#Fk##s(1#H&s(Y$s(ZSh&#s([#C#$k##s(6#+&s(^$s(_S@&#s(`ISVH#CSVH@#5$#m#&#ISUS'#CSUS'@#5$#m#&#ISJS%#CSJS%@#5$#m#&#Os&PO#O#O#VS\C#WS]Cs&E#VS\C(WS]Cs&Y#AC#s&VAC&#R#SKUT1s&MVT2C#O,O#VS\C#WSsC&#AC#s&NR#SKWS]Cs&S&WSsC*2AC0s&SAC$#AC&#R#SKAC4s&VAC(#AC*#R#SKUT1S_VT2C#WSsC#2AC#s&_R#SK*S*:s*k*S*;#*S*%#*S*+#*S*0#*S*7#*S*@#*S*A#:Cs&^Ps&dNCS0:Cs'bS&#:C%K#NCS.:Cs'eR#:C#Ns&h:C&H#USZs*q)#=C#;Cs'i#=C&JC$#1Cs&QS$#2s*|JEEI#Q3s*}JEEIs&gs&f#;Cs'os&aUSZs&g=C#;Cs'r#JC#s*}1C'S$#2s+(JEEI#Q3s+)JEEIs&os&n#;Cs'ws&X=Cs3,JCs&m#1C%S$#2s+.JEEI#Q3s+/JEEIs&us&t#WSYCs&os&c1Cs&zSt#2s+2JEEI#Q1Cs+2S$%2s+4JEEI#Q[S^s+5JEEI%#ZT3s+6JEEIS/1Cs+6S$s'$2s+8JEEI#Q[S^s+9JEEI%#[T4s+:JEEI'#WSYCs&is&n1Cs')St#2s+=JEEI#Q1Cs+<S$%2s+?JEEI#Q[S^s+@JEEI%#1C(SLs'.2s+BJEEI#QZT3s+CJEEIS,[S^s+DJEEI$#[T4s+EJEEI'#1C=S$s'32s+GJEEI#Q1Cs#-S$s'52s+IJEEI#QJCs#*s(;1C#SLs##2s+LJEEI#Q1Cs'#SLs#-2s+NJEEI#Q1Cs'<SLs+N2s+PJEEI#QJCs'>s+O1Cs+QSt#2s+SJEEI#Q[S^s+TJEEI&#3s+UJEEIs&ws'>#3s+VJEEI*s'?#3s+WJEEI-s'@#3s+XJEEI1s'A#3s+YJEEI4s'B#3s+ZJEEI7s'C#3s+[JEEIs##s'D#3s+\JEEIs#/s'E#3s+]JEEIs#6s'F#3s+^JEEIs#?s'G#l#<#s+Ss+Ml#=s#Js+a#l#>s#Ss+f#j#?C#j#@C#j#AC#j#_C#j#`C#j#aC#j#bC#j#cC#j#dC#j#gC#j#hC#j#iSB#j#jSB#$s*@P$s*AS0(#S(#C%#k##s'##(&P#Cs&x#k##s'&#$s*HS)(*S.#C$#k##s'*#.S(S&/F##CN$'$##CNF'S,#5%#.S'S(/F##CR$'$#%&F'#S65%##CS1F(<s*[$s*\S1%$#%?$#CS0F%FS.(FS0/S.#'%#k##'#k##)#k##+#k##/#k##0#k##2#k##:#k##B#k##s#'#k##s#+#k#?C#k#@C#k#AC#k#_C#k#`C#k#aC#k#bC#k#cC#k#dC#k#gC#k#hC#k#iSB#k#jSB##CS`F.S?SW%#Fi#:G%#RS1SDS7PS@S?SWS0S`S<S.S%S2SPSQSHS>S-SIS:l#Bs#B'#l#ks$os$p#l#ls$us$v#l#Cs${s$|#l#Fs%%C#l#Gs%(C#l#Ds%.s%*#l#Es%4s%0#l#Hs%<s%6#l#Is%Ds%>#l#Js%Ks%F#l#Ms%MC#l#Ns%PC#l#Ks%Vs%R#l#Ls%[s%X#l#Os%as%]#l#Ps%fs%c#l#Qs%ms%h#l#Ts%oC#l#8s%rC#l#Rs%xs%t#l#Ss%}s%z#l#Us&'s&##l#.s&-s&)#l#(s&3s&/#l#Zs&9s&5#l#ms&@s&;#l#ns&Is&C#l#os&KC#l#Vs&Vs&N#l#ps&YC#l#Ws&cs&\#XTSs&ws&qs&e#XGs+QS#s&|#l#(s'&s'##XTTs+@s+?s'A#$Ds+E(s.G##C#s/:'#s+Cm#'#XTULs+Us+S#ZGLCs,6s+]s/>#l#(s+fs+a#+s,:Dl#<s(is,ss,ml#=s)ss-%#l#>s-+s-*#l#B#s(2Gm##s.@WTVs,AD#PCs,Bs,4*)#$DS7.#s.59Cs,Ds,<%#Gl#(s,Ks,G#l#+s.bs.^#l#qs.ls.i#l#2s.ss.r#l#0s.ys.w#PCs/,s.|#SbS1l#+s/1s/.#l#rs/:s/8#l#2s/As/@#l#1s/Hs/F#PCs/Us/K#SaS/l#*s/Ys/W#l#rs/as/`#l#qs/is/g#PCs/xs/o#s/nGj#ss/z#j#tC#V#HGj##s0##j#[C#YSuCs03s0)#Gl#'s0;s07#j#us0>#j#vC#V#HGj##s0B#j#[C#YSuCs0Rs0G#Gl#'s0Xs0U#j#ws0Z#j#xC#V#HGj##s0^#j#[C#YSuCs0ns0c#Gl#'s0us0q#l#qs0xs0w#l#(s1%s1##l#rs0~s0}#l#(s1's1%#j#qs1=#j#rs1B#V#HGj##s1G#j##s1Y#Ls1Zs1Ws1L#Gl#)s1as1^#l#(s1is1g#WTWs2%s2##j#)s2/#U#Gj##s2J#4s5's21(s22D4#s5(B%#j#-s5j#WSfs5k#S-#M#OXS-S3PS9GWTXs21s2/#j#)%#U#Gj##s2N#ZTYs2Ws2Os2B/#Gl#)s2_s2\#l#(s2ns2l#YTZCs3-s3,s3b#m##s3_m##s3`j#/s39#j#0s3;#j#1s3?#j#2s3B#Ps5{SPs3G#S7Gl#rGs3l#j#.s3`#Ps6#s3os3b#S%Gl#.Gs3q#j#(s3t#U#Gl#.s3ys3x#U#Gl#.s4&s4%#j#(s4-#Y#GS(NKHj#(s43#j#/s48#j#0s4:#j#1s4>#V#HGj##s4C#j##s4X#Ls4Ys4Vs4H#Gj#(s4]#j#2s4e#V#HGj##s4j#j##s5)#Ls5*s5%s4s#Gj#(s5.#j#,s6:#j#[s6<#X#NKHGnT5%s6>s5R%#,##s5IK#%#s5;'#[#,######s6>Gs5E-s68R>s5S,C$#k##&#j#,s6C#U#s5NVS[s6Es5LUG#l#(,%#j#)s5g#j#*s6=#j#+s5m#j#$s6C#j#ys67#j#%s6M#j#;C#j#:C#V#HGj#9C#j#9C#YT[CCs5y#Gj#zs6U#YT\s6Vs6?s6.#Gj#%s6V##"). Qed.

Lemma NoDup_map_bv_unsigned : forall (l : list word),
  List.NoDup l -> List.NoDup (map bv_unsigned l).
Proof.
  intros l Hnd. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
  apply bv_eq in Hy. subst y. exact (Hx Hiny).
Qed.

Theorem allowed_pages_bound : forall A (pages : list word),
  A_wf A ->
  List.NoDup pages ->
  (forall p, In p pages -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p pages -> page_allowedb A p = true) ->
  (Z.of_nat (length pages) * page_size <= A_bytes A)%Z.
Proof.
  intros A pages Hwf Hnd Hal Hpa.
  rewrite <- (A_pages_length A Hwf).
  assert (Hlen : (length pages <= length (A_pages A))%nat).
  { rewrite <- (length_map bv_unsigned pages).
    apply NoDup_incl_length.
    - apply NoDup_map_bv_unsigned. exact Hnd.
    - intros z Hz. apply in_map_iff in Hz as (p & <- & Hp).
      apply A_pages_in; [exact Hwf | exact (Hal p Hp) | exact (Hpa p Hp)]. }
  unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_as_pages : (2 ^ 64 = page_size * 2 ^ 52)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_woff : forall a k,
  page_base (woff a k) = page_base_of (bv_unsigned a + Z.of_nat k).
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@kc__4); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.N); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.eq_Transitive); constr:(@Stdlib.setoid_ring.Ncring.ring_mult_comp); constr:(@Corelib.BinNums.PosDef.Pos.mul); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.opp); constr:(@Stdlib.setoid_ring.Ncring_initial.Zops); constr:(@Stdlib.setoid_ring.Ncring_initial.Zr); constr:(@Corelib.Classes.Morphisms.reflexive_proper); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_eq_dom_reflexive); constr:(@Corelib.Classes.RelationClasses.eq_Reflexive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.div_add); constr:(@Stdlib.ZArith.Zdiv.Z_mod_plus_full); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.two64_as_pages); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAcct.woff); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_base_of)|] [|@__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @H0; @H; @cstr; @heq_z; @b2; @b1; @n; @z; @Ha; @__p1; @H6; @__sat2; @H5; @H4; @r0; @q; @H3; @H2; @H1; @__sat0; @__sat1; @heq_r; @y; @y'; @x; @x'; @b; @a; @lemma; @__x3; @__sat3; @q0; @heq_q; @__sat4; @H10; @H9; @r1; @q1; @H8; @H7; @__sat5; @H15; @H14; @r2; @q2; @H13; @H12; @H11; @Hfl; @Hdm; @Hps; @r; @Hz; @k|] "#/{#Y$d#d$9#h##$$#$#%$%$##&#2#3#/#4$+#1#'#6#+#.#7#5#<#(#,#D#8#9#)#*#-#0#=#A#;#@#?#G#C$@$R#_#p#>#L$)$c#E#F#B#H#I#]#t#u#q#v#o$0$1$4$>$<$C$F#:$Q#Y$S$A#l$^$`$b$8#a#K$d#P#T#e#j#w#x#{#|#~$,$.$2$3$/$5$B$D$L$K$N$P$O$U$W$X$a$_$]$V$Y$Z$[$\$T$e#M#N#O#J#X$f$g$j$i$k#`$7#i#g#^$?#f#b#n$'$&#k$M#c$G$H$I$J$-#}$;$=$:#\$E#m#y$*$6#s#r#z$($hK$C%#i&$D%$E%$F$#n%$G%#m%$H%$I%$J($K'$L*$M%$N&$O$#h%$P%$Q%$R%$S%$T&$U+$V%$W$$X)$Y$$Z&#;$#Q&$[$$\'$]%$^%$_%$`&$a%$b%#&&$c%'S<'#'#'#'#'#USG#=#,$H2F($#VSc'I,(I&E#USd*%%#+%#,-L2I($#0C#$CH$m#$#AL2L&E#,6S*&E#%$0+$#,:S/2S*($#&E#j##'#%'7,@S0&E#,BS%%#;USHSIUSH#EC#EC%ECSIFC$#FC&#VSJ#SKUSeS=WSLS=$#USfS=GCIUSgCBC$H#UShCUSiCHCECCs#;.C$S@#/&KGGJ#QUSjGCCS<.C(S@#/*KGGJ#Q8C%).C+S@#/-KGGJ#Q9.KGGJ&)#9/KGGJ+*#VSk0J0SMSNVSlFI$SM#SNm$%#WSmCEHXSnFI$#l#$*)#l#%:9#l#&?>#j#'C#j#(C#&EH(IL&E#k##%#k##&#k#'C#k#(C#2S+,s#US1XF$#S*Il#)-&#j#*s#7#j#+s#:#V#HFj##s#>#j##s#G#-s#Hs#Gs#A#Il#,s#Ms#K#l#-s#Os#P#m##5=F=H=I$#HF,LI,LH$C$#k##&#,IH,IF$C$#=L$#IHk##%#+)#=S#$#LIk##-#j##&#j##$Fj##/#WSoIHF-1+&$#j#.8#j#/:#j#0SO#k#.;/k#/=#k#0SO#Ds#~L,s$##*#D##DDs$&#*LD##DDs$)#:s$*'*S#D##DDs$-#,s$.#$CF#j#1C#:s$1L*FD##D:s$4#$C#)j#1C#:s$71:s$8S#*#D##D:s$;#$C#Fj#1C#;s$DUSPS<'#USP#'#'#;#VSQ)##D#)S#F*#D##D)#F)AF$C$#j#1C#)L*'s$P'#'#'#'#'#;#HC#.Cs$%S:#/s$'KGGJ#Ql#$#s#vs#pl#%s$,s$*#l#&s$1s$/#%E)l#)$#F%EDm#$#)S*<0C#$CH$m#$#2S0(s$E#0C#$CS/$m#$#AS%2S%&E#VSps#0s#*%Es#1&Es#,%Es#,k##$#k##&#&Es#6WSqs#7s#1Hj##SR#j#2%#&Es#3k##SR#k#2(#>S1s#5S%&Es#6)S&s#7&E#k##%#3S&s#:$Cs#;EUSS#*Os#=#s#>#)Os#?($#$CO#k##(#4Os#C%Es#D)S2s#E&E#%$s#G+$#k##'#5S2s#J%s#KE)Rs#L%s#M#&$E+$#k##'#6Rs#Q*Ms#R$C#Ek##;#7Ms#U)Ns#V$C#Nk##?#*Ns#Y)Ps#Z,s%CS'&E#%$s%=+$#j###s#%,s%HS-%#s%A,s%JS.&E#,s%LST%#s%E?P&ES#%S#s#h+$#URS(&ES/%S/s#l+$#j###s#4%S0s#o&ES%%S+s#q's#d'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#;#VSrC#WSsC#s%_FC#s%_VSJ#SKWSLS=#s%]BCs%ZIs%[BC#Hs%[HCs$NUSGs$JWStC$#1Cs%V#.C#S:s%\/s%^KGGJ#QCCs$R.C&S:#/s%aKGGJ#QZSus%bKGGJS#[Svs%cKGGJ$#9s%dKGGJ(s%_#.C(S:+/s%fKGGJ#Q.Cs%fS:s%a/s%hKGGJ#Q.C/S;s%h/s%jKGGJ#QZSUs%kKGGJ#9s%lKGGJ&s%g#9s%mKGGJ)s%h#9s%nKGGJ,s%i#l#$#s%as%[l#%:s%q#l#&=s%v#j#'C#j#(C#j#3SV##Fs$c%#E#Hs$e%#I+#Lk##&#%I&%EI#Ls$k$C#Ek###SWk##&#k##(#k##*#k#'C#k#(C#k#3SV#&S&EZF#S&DMHS5l#)6%#j#4s#c#j#*s#e#V#HFj##s#h#j##s#m#-s#ns#ms#k#Hl#5s#ps$R#l#*s#us#r#j#6s#w#j#7s#z#V#HFj##s#~#j##s$(#-s$)s$(s$&#Pl#8s$,C#l#9s$.C#l#:s$3s$0#l#;s$8s$5#l#<s$@s$:#l#*s$Hs$B#l#+s$Rs$J#l#=s$Xs$T#l#>s$]s$Z#l#5s$gs$b#l#,s$ks$i#l#-s$ms$n#l#?s$ss$t#WSXS*s%5#*S*s%6#s%7#(#s$z$CS*#*S/s%:#s%;F(#L$CS0#USYCUSwC*S%D##D#s%BH(#S#*#D##D;S<VSxHF;#USy$nC#$#@CH#&#E$#A$$#A#nC#$#@CH#&#E$#A$$#A%nC#$#BCH#&#E$#C$$#C#j#@C#j#BC#k#DCCk#EC#XSZCC55XSZC%6#USzCXS[CC8#XS[C(&#WS{(&#VS\CD^S|*($S]S%7FDD#dS}CE5S^-S~T#=T$T%;7#DD$(:s%tVS\C#]T&C@?=9%$$#j#FB#*S0s%^0C#$CF$m#$#)S%s%b0C#$CS#$m#$#,s'NS&2S1($#0C#$CS+$m#$#AS&2S&&E#>S2s%oS&&Es%&k##s%=#@Rs%rO&Es%#k##s%@#3Ms%u#s%vs${(#s%#$CN#k##s%?#4Ns%z&Es%#%s%$s%|+$#k##s%<#5Ps&#)S(s&$%s&%#&$E+$#k##s%;#6S(s&)*S$s&*$C#Ek##s%O#7S$s&-)S's&.$C#S'k##s%S#*S's&1)S-s&2,s'wS5&E#%$s'q+$##s&8N##D(S$##s&:N(#S$$C%#j##)#,s(&S)%#s'{,s((S3&E#,s(*S>%#s(#?S-UMS.#s&GS.##D(S)##s&IS.(#S)$C%#j##s%=#GCLBCs'eH#1Cs$es'`CCs&W1C$#8Cs'_#1C%s$i1C#s'e8C#s'b.C&S;#/s'jKGGJ#Ql#$#s']s'Wl#%-s'm#l#&s'ts'r#j#'C#j#(C#j#GC##s&_H##I(F##Is&b##H(#F$C&#k#'C#k#(C#k#GC#IDS3S6l#).$#j#4s%W#j#*s%Y#V#HFj##s%\#j##s%a#-s%bs%as#%#Hl#Hs#-s&F#l#*s#/s%f#j#6s#1#j#7s#4#V#HFj##s#8#j##s#D#-s#Es#Ds#<#S-l#8s#HC#l#Is#JC#l#:s#Os#L#l#;s#Ts#Q#l#<s#[s#V#l#*s#as#]#l#+s#gs#c#l#=s#ks#i#l#>s#os#m#l#5s&Rs&O#l#Hs&\s&W#l#,s#us#s#l#-s#ws#x#l#?s#~s$##l#Js$'s$(##s',F##D(L#$C#s$P#s#/D(S###s'1I*S*D##D(%#$Cs'H#j#1C#(s'Rs#7#FD$C#'j#1C#*S%s';0C#$CH$m#$#)S+s'?0C#$CS*$m#$#,s)+O(#s$50C#$CS1$m#$#AO2O&E#VSAS1D&ES1&ED*OD&E#k##%#k##'#>Ms'RS2&Es&[k##s&|#@Ns'UR*Ps'V&E#k##s'$#3S2D$CDEUSS#*RD#D#)RD($#$CR#k##(#4RD)MD&E#%$D+$#k##s'O#5MD%DE)ND%D#&$E+$#k##'#6ND*PD$C#Ek##:#7PD)S(D$C#S(k##>#*S(D)S$D3S5s'y*S)s'z#s'{#)S)s'|($#$CS)#k##s'E#4S)s($)S3s(%&E#%$s('+$#k##s'C#5S3s(*)S>s(+%s(,#&$E+$#k##s'B#6S>s(0*S7s(1$C#Ek##s'V#7S7s(4)S6s(5$C#S6k##s'Z#*S6s(8)S4s(9,s)~S,&E#%$s)x+$##s(?S)(S+###D#s(AS)#S+D($#$C&#j##*#,s*.SB%#s*',s*0SC&E#,s*2S8%#s*+?S4UPSD&EO%OD+$#US5S9&ES0+#s'B#s(US9(N###D#s(WS9#ND($#$C&#j##*#%S%s(\&ES+%S1s(^&ES(%S(D+$##s(cS8(S'###D#s(eS8#S'D($#$C&#j##*#%S$D&ES'%S-D8Cs)zs$|1C#s$|1Cs)|s$}8Cs$z#.C%S;#/s*)KGGJ#Ql#$#s)xs)rl#%s%(s*,#l#&s*3s*1#j#'C#j#(C#j#GC#(Fs$y##I#FI(s$x#$C%#k#'C#k#(C#k#GC#IDS_S5l#),$#j#:9#j#*;#V#HFj##>#j##s#*#-s#+s#*A#S*j#;s#-#j#<s#/#V#HFj##s#2#j##s#=#-s#>s'}s#5#Il#Ks#@s(e#l#*s#Es#B#l#6s#Gs(*#j#Ls#I#j#Ms#L#V#HFj##s#P#j##s#]#-s#^s#]s#T#S4l#Ns#aC#l#Os#cC#l#Ps#hs#e#l#Qs#ms#j#l#4s#ts#o#l#6s#{s#v#l#7s$'s#}#l#8s$)C#l#Is$+C#l#:s$0s$-#l#;s$5s$2#l#<s$=s$7#l#*s$Ds$?#l#+s$Ns$F#l#=s$Ss$P#l#>s$Ws$U#l#5s$_s$Y#l#Hs(zs(w#l#Ks)(s)##l#,s$es$c#l#-s$gs$h#l#?s$ms$n#l#Js$rs$s#*s%%D>Rs)TO)Ms)U&E#k##s)##@Ms)XS2&Es(^k##s)&#3Ns)[#s)\s$d(#s(a$CP#k##s)%#4Ps)`&Es&?%s&@s)b+$#k##s(~#5S(s)e)S$s)f%s)g#&$E+$#k##s(}#6S$s)k$Cs&=Ek##s)4#7S's)n$Cs&?S-k##s)7#*S-s)q)S.s)r&Es&7+#s&7j###s$x%s&8s+V&Es&7,s+`S7%#s+Y?S.UMSTj##s(ms%#GCH.Cs+/S;s+4/s+6KGGJ#QZSUs+7KGGJ#9s+8KGGJs(.s+3#l#$#s++s+%l#%(s+;#l#&s+Bs+@#j#'C#%EF$CHEk###SWk##%#k#'C#VFDS6l#))$#j#4s(z#j#*s(|#V#HFj##s)##j##s)(#-s))s)(8#Hl#H:s)i#l#*<s)-#j#6>#j#7A#V#HFj##s#$#j##s#(#-s#)s&]s#'#S.l#8s#+C#l#Is#-C#l#:s#1s#/#l#;s#5s#3#l#<s#<s#7#l#*s#Bs#>#l#+s#Hs#D#l#=s#Ls#J#l#>s#Qs#N#l#5s)us)r#l#Hs*#s)z#l#,s%`s%^#l#-s%bs%c#l#?s%hs%i#l#Js%ms%n#XT'S#s&ND#<Cs%vs%ss#[s#Z#ZS`Cs%~s%x#s'kFl#+s&)s&%#Vs'SH#*S0D##D(s'xs*s$C$#)s&&s*W)Fs*X$C$#j#1C#@RDO*MD&E#k##s%o#VSAS&D&ES&*S2D&E#k##s%t#k##&#>Ns*eRk##s*2s'I@Ps*gM*S(s*h&E#k##s*6#3RD#D2(#s%h$CM#k##s%r#4MD&Es%e%s%fD+$#k##s*\#5ND)PD%D#&$E+$#k##s%o#6PD$Cs%cEk##s&%#7S(D$Cs%eS$k##s&(#*S$D)S'D3S)s+'*S3s+(#s+)#(#s%c$CS3#k##s*N#4S3s+-&Es%a%s%bs+/+$#k##s*K#5S>s+2)S7s+3%s+4#&$E+$#k##s*J#6S7s+8$Cs%_Ek##s*]#7S6s+;$Cs%aS4k##s*`#*S4s+>)SDs+?3S9D*S,D#D#)S,D($#$CS,#k##s&I#4S,D)SBD&E#%$D+$#k##s+4#5SBD)SCD%D#&$E+$#k##s&G#6SCD*S8D$C#Ek##s&Z#7S8D)SED$C#SEk##s&^#*SED)SFD,s-ES?&E#%$s-?+$##S,s+a(s%h##s+cS,(#s%j$C%#j##(#,s-OT(%#s-H,s-QT)&E#,s-ST*%#s-L?SF%S#D+s*f#UPT+%Os+q+s&&#US)S_%S'D+s%h#US,S?%S%D+s*f##S5D#S?s+z($##s+|S?(#&$C%#j##)#%S+D%S&D&ES$%S$s,'+$##S7D#Sas,*($##s,,Sa(#&$C%#j##)#%S's,0&ES-%S.s,2&ES4%S4D+$##S9D#Sbs,7($##s,9Sb(#&$C%#j##)#%SDD&ES9%S,D1Cs-Ms-Q1Cs-Rs*W1Cs(P#8C%#1C%s(R8C#'.C%S;#/s-ZKGGJ#Ql#$#s-Ms-Gl#%s(Ys-]#l#&s-ds-b#j#'C#j#(C#j#GC##FH#Is*I($##s*KI(#&$C%#k#'C#k#(C#k#GC#IT,DS8l#)-$#j#L<#j#*>#V#HFj##A#j##s#,#-s#-s#,s#$#S+j#6s#/#j#:s#1#V#HFj##s#4#j##s#?#-s#@s#?s#7#S/j#;s#B#j#<s'x#V#HFj##s#F#j##s+W#-s+Xs#Qs#I#Ll#Rs#Ss,A#l#*s#Ws#U#l#6s#[s#Y#l#Ls#_s#]#j#Ss#a#j#Ts#d#V#HFj##s#h#j##s#s#-s#ts#ss#l#SFl#Us#wC#l#Vs#yC#l#Ws#~s#{#l#Xs$'s$$#l#Ys$.s$)#l#Ls$5s$0#l#Ms$=s$7#l#Ns$?C#l#Os$AC#l#Ps$Es$C#l#Qs$Is$G#l#4s$Ps$K#l#6s$Vs$R#l#7s$]s$X#l#8s$_C#l#Is$aC#l#:s$es$c#l#;s$is$g#l#<s$ps$k#l#*s$vs$r#l#+s$|s$x#l#=s%%s$~#l#>s%(s%'#l#5s%/s%*#l#Hs%4s%1#l#Ks,_s,\#l#Rs,is,d#l#,s(Js(H#l#-s(Ls(M#l#?s(Rs(S#l#Js(Ws(X##Hs-8(s-S#$C#s*>#Is-;(s(g#*S/D##D)#s-?$C#s%Fj#1C#$C%Fj#1C#0Cs%K)+s-EWT-s(qIs-F<Cs%N&%$#ZS`C.)#s(rFl#+41#<Cs*Ns%N#s*gFl#Zs%Ws%S#l#9s*pC#l#[s*vs*r#l#\s-5s-6#l#]s-GC#;s/9VSQs-Y#<Cs-Rs-K%#T.*s-hD##D:s/=#$C#s-em#'#,s/@s-uJs/As-w<Cs-is-c%$#Js/CL<Cs-qs-l$s.##,s/Es-}Js/Fs.#<Cs-{s-u%$#XFs/Hs.$s-}#l#+s.-s.*#l#^s.Hs.[#l#2s/Fs/A#l#1s/HC#VT/HFUT0#UT1s/K$s/O$#m#'#j#_T2#j#Es/R##"). Qed.

Lemma page_base_of_aligned : forall z,
  (bv_unsigned (page_base_of z) mod page_size = 0)%Z.
Proof.
  intros z. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite two64_as_pages.
  rewrite (Z.mul_comm (z / page_size) page_size).
  rewrite Zmult_mod_distr_l.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma page_insert_nodup : forall p pages,
  List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
  intros p pages Hnd. unfold page_insert.
  destruct (page_mem p pages) eqn:Hm; [exact Hnd|].
  constructor; [|exact Hnd].
  intros Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma page_mem_false_not_in : forall p pages,
  page_mem p pages = false -> ~ In p pages.
Proof.
  intros p pages Hm Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma access_pages_acc_nodup : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
  apply IH. apply page_insert_nodup. exact Hnd.
Qed.

Lemma accesses_pages_nodup : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
  apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages Hin. unfold page_insert in Hin.
  destruct (page_mem q pages); [right; exact Hin|].
  destruct Hin as [Hqp | Hin]; [left; symmetry; exact Hqp | right; exact Hin].
Qed.

Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p Hin.
  - left; exact Hin.
  - destruct (IH (base + 1)%Z _ p Hin) as [Hin' | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin') as [-> | Hin''].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin''.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p Hin.
  - left; exact Hin.
  - destruct (IH _ p Hin) as [Hin' | (a' & n' & k & Hin' & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin') as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin' | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma new_pages_props : forall H A lazy mat ranges,
  lazy_cover H lazy A ->
  ranges_avoid H ranges ->
  let new := newly_materialized_pages lazy mat ranges in
  List.NoDup new
  /\ (forall p, In p new -> ~ In p mat)
  /\ (forall p, In p new -> (bv_unsigned p mod page_size = 0)%Z)
  /\ (forall p, In p new -> page_in_ranges p lazy = true)
  /\ (forall p, In p new -> page_allowedb A p = true).
Proof.
  intros H A lazy mat ranges Hcov Hav new.
  assert (Hchar : forall p, In p new ->
            page_in_ranges p lazy = true /\ page_mem p mat = false
            /\ exists a n k, In (a, n) ranges /\ (k < n)%nat
                             /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z).
  { intros p Hin. unfold new, newly_materialized_pages in Hin.
    apply filter_In in Hin as [Hin Hf]. apply andb_true_iff in Hf as [Hl Hm].
    split; [exact Hl|]. split; [destruct (page_mem p mat); [discriminate | reflexivity]|].
    destruct (accesses_pages_in ranges [] p Hin) as [[] | Hex]. exact Hex. }
  split; [|split; [|split; [|split]]].
  - unfold new, newly_materialized_pages. apply NoDup_filter.
    apply accesses_pages_nodup. constructor.
  - intros p Hp. destruct (Hchar p Hp) as (_ & Hm & _). apply page_mem_false_not_in. exact Hm.
  - intros p Hp. destruct (Hchar p Hp) as (_ & _ & a & n & k & _ & _ & ->).
    apply page_base_of_aligned.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _). exact Hl.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _ & a & n & k & Hin & Hk & Ep).
    pose proof (Hav a n Hin k Hk) as Hw.
    rewrite <- page_base_woff in Ep. rewrite Ep in Hl |- *.
    exact (Hcov (woff a k) Hl Hw).
Qed.

(* [comment removed for export] *)
Lemma m_vm_materialized_wvb : forall l X m,
  m_vm_materialized (with_vm_backing l X m) = X.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : forall l X m, m_vm_lazy (with_vm_backing l X m) = l.
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : forall l X m, m_vmmaps (with_vm_backing l X m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_halted_wvb : forall l X m, m_halted (with_vm_backing l X m) = m_halted m.
Proof. reflexivity. Qed.
Lemma eager_used_wvb : forall X m,
  eager_used (with_vm_backing (m_vm_lazy m) X m) = eager_used m.
Proof. reflexivity. Qed.

Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma MInv_wvb : forall A m X,
  List.NoDup X ->
  (forall p, In p X -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p X -> page_allowedb A p = true) ->
  (forall p, In p X -> page_in_ranges p (m_vm_lazy m) = true) ->
  (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z ->
  MInv A (with_vm_backing (m_vm_lazy m) X m).
Proof.
  intros A m X H1 H2 H3 H4 H5. constructor;
    rewrite ?m_vm_materialized_wvb, ?m_vm_lazy_wvb, ?m_vmmaps_wvb, ?eager_used_wvb;
    assumption.
Qed.

(* [comment removed for export] *)
Theorem materialize_restricted : forall H A m ranges,
  lazy_cover H (m_vm_lazy m) A ->
  A_wf A ->
  MInv A m ->
  ranges_avoid H ranges ->
  exists mat',
    materialize_model_accesses m ranges
      = Some (with_vm_backing (m_vm_lazy m) mat' m)
    /\ MInv A (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros H A m ranges Hcov Hwf [Hnd Hal Hpa Hlz Hbud] Hav.
  destruct (new_pages_props H A (m_vm_lazy m) (m_vm_materialized m) ranges Hcov Hav)
    as (Nnd & Nfresh & Nal & Nlz & Npa).
  unfold materialize_model_accesses, materialize_accesses.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app; [exact Nnd | exact Hnd | exact Nfresh]. }
  assert (Happ_al : forall p, In p (new ++ m_vm_materialized m) ->
                      (bv_unsigned p mod page_size = 0)%Z).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nal p Hp) | exact (Hal p Hp)]. }
  assert (Happ_pa : forall p, In p (new ++ m_vm_materialized m) -> page_allowedb A p = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Npa p Hp) | exact (Hpa p Hp)]. }
  assert (Happ_lz : forall p, In p (new ++ m_vm_materialized m) ->
                      page_in_ranges p (m_vm_lazy m) = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nlz p Hp) | exact (Hlz p Hp)]. }
  pose proof (allowed_pages_bound A (new ++ m_vm_materialized m) Hwf Happ_nd Happ_al Happ_pa)
    as Hbound.
  rewrite length_app, Nat2Z.inj_add in Hbound.
  destruct new as [|p0 new'] eqn:Enew.
  - exists (m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
  - rewrite vm_backing_used_split.
    replace (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size
             + Z.of_nat (length (p0 :: new')) * page_size
             <=? vm_limit (m_vmmaps m))%Z with true.
    2:{ symmetry. apply Z.leb_le. unfold page_size in *. lia. }
    exists ((p0 :: new') ++ m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.
Context {SC : StepCfg}.   (* [comment removed for export] *)
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs the_scfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs the_scfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Theorem mi_account_step_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists mat',
    mi_account_step segs ms model
      = MachineOk (unrestrict H (ms_mem ms) msr',
                   with_vm_backing (m_vm_lazy model) mat' model)
    /\ MInv A (with_vm_backing (m_vm_lazy model) mat' model)
    /\ hclean H msr'.
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hs.
  destruct (step_restrict_sound segs H HH Hwx ms msr' Hs) as (rep & Hsa & Hv & Hrs & Hcl & _).
  destruct (materialize_restricted H A model (accessed_ranges _ rep) Hcov Hwf Hinv Hrs)
    as (mat' & Hmat & Hinv').
  exists mat'. unfold mi_account_step. rewrite Hsa, Hmat, Hv.
  split; [reflexivity | split; [exact Hinv' | exact Hcl]].
Qed.

(* [comment removed for export] *)
Lemma sstep_instr_det : forall ms model ms1 model1 e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms1, model1) ->
  sstep_cfg segs the_scfg (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms1 model1).
Proof.
  intros ms model ms1 model1 e st Hsvc Hacc Hss. apply sstep_cfg_sub in Hss.
  inversion Hss; subst;
    match goal with
    | Hp : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in Hp; discriminate
    | Ha : mi_account_step segs ms model = _ |- _ =>
        rewrite Hacc in Ha; try discriminate; injection Ha as <- <-; split; reflexivity
    end.
Qed.

(* [comment removed for export] *)
Theorem node_instr_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists model',
    MInv A model' /\ same_but_materialized model model'
    /\ hclean H msr'
    /\ mi_account_step segs ms model
         = MachineOk (unrestrict H (ms_mem ms) msr', model')
    /\ node_ok (mkCfg ms model) unit (fun _ => [])
               (fun _ => mkCfg (unrestrict H (ms_mem ms) msr') model').
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs.
  destruct (mi_account_step_restricted A ms msr' model Hcov Hwf Hinv Hs)
    as (mat' & Hacc & Hinv' & Hcl).
  exists (with_vm_backing (m_vm_lazy model) mat' model).
  split; [exact Hinv'|]. split; [apply with_vm_backing_same|]. split; [exact Hcl|].
  split; [exact Hacc|].
  split.
  - intros []. apply sstep_cfg_instr; [exact Hh | exact Hsvc | exact Hacc].
  - intros e st Hss. exists tt.
    exact (sstep_instr_det ms model _ _ e st Hsvc Hacc Hss).
Qed.

(* [comment removed for export] *)
Lemma step_hclean : forall ms ms',
  hclean H ms ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  hclean H ms'.
Proof.
  intros ms ms' Hc Hs. rewrite <- (hclean_restrict_id H ms Hc) in Hs.
  destruct (step_restrict_sound segs H HH Hwx ms ms' Hs) as (rep & _ & _ & _ & Hcl & _).
  exact Hcl.
Qed.

Lemma msteps_hclean : forall ms ms',
  msteps segs ms ms' -> hclean H ms -> hclean H ms'.
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; intros Hc.
  - exact Hc.
  - apply IH. exact (step_hclean ms ms1 Hc Hstep).
Qed.

Lemma unrestrict_munrestrict : forall f g ms',
  unrestrict H (munrestrict H f g) ms' = unrestrict H f ms'.
Proof.
  intros f g ms'. unfold unrestrict. f_equal.
  apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x); reflexivity.
Qed.

(* [comment removed for export] *)
Variable P : config -> Prop.
Hypothesis P_silent1 : forall c c',
  node_ok c unit (fun _ => []) (fun _ => c') -> P c' -> P c.

Theorem rz_step_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs Hk.
  destruct (node_instr_restricted A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & _ & _ & Hnode).
  exact (P_silent1 _ _ Hnode (Hk model' Hinv' Hsame)).
Qed.

Theorem rz_msteps_restricted : forall A msr0 msr',
  msteps segs msr0 msr' ->
  forall ms model,
  msr0 = restrict H ms ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH];
    intros ms model -> Hcov Hwf Hinv Hh Hk.
  - specialize (Hk model Hinv (same_but_materialized_refl model)).
    rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_restricted A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
      as (model1 & Hinv1 & Hsame1 & Hcl1 & _ & Hnode).
    apply (P_silent1 _ _ Hnode).
    pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
    apply (IH (unrestrict H (ms_mem ms) msr1) model1).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
    + exact Hwf.
    + exact Hinv1.
    + replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
    + intros model' Hinv' Hsame'.
      rewrite unrestrict_mem, unrestrict_munrestrict.
      apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame')].
Qed.
(* [comment removed for export] *)
Theorem rz_msteps_restricted' : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hms Hk.
  pose proof (msteps_hclean _ _ Hms (restrict_hclean H ms)) as Hcl.
  apply (rz_msteps_restricted A (restrict H ms) msr' Hms ms model eq_refl Hcov Hwf Hinv Hh).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' Hcl).
Qed.

End Nodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses.
  unfold newly_materialized_pages. cbn [accesses_pages List.filter].
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Definition materialized_succ (m : Model) (accs : list (word * nat)) : Model :=
  match materialize_model_accesses m accs with
  | Some m' => m'
  | None => m
  end.

Section SyscallNode.
Variable segs : list Segment.
Context {SC : StepCfg}.
Variable H : word -> bool.

(* [comment removed for export] *)
Theorem node_syscall_restricted :
  forall A ms model x8 (I : Type)
         (eff : I -> SyscallEffect) (mdl : I -> Model) (evs : I -> list event),
  A_wf A ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (eff i) (mdl i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (eff i)) ->
  (* [comment removed for export] *)
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff' m' evs', syscall_spec (sys_input segs ms x8) model (Ok eff' m' evs') -> m_halted m' = None) ->
  (forall eff' m' evs', syscall_spec (sys_input segs ms x8) model (Ok eff' m' evs') ->
             ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff' ->
             exists i, Ok eff' m' evs' = Ok (eff i) (mdl i) (evs i)) ->
  (forall i, m_halted (mdl i) = None) ->
  (forall i, lazy_cover H (m_vm_lazy (mdl i)) A) ->
  (forall i, MInv A (mdl i)) ->
  (forall i, ranges_avoid H (syscall_effect_accesses (eff i))) ->
  (forall i, MInv A (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))
             /\ same_but_materialized (mdl i)
                  (materialized_succ (mdl i) (syscall_effect_accesses (eff i))))
  /\ node_ok segs (mkCfg ms model) I evs
       (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i)))
                       (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))).
Proof.
  intros A ms model x8 I eff mdl evs Hwf Hh Hsvc Hsound Hnsp Hunm Hnoh Hcompl Hnh Hcov Hinv Hav.
  assert (Hmat : forall i, exists mat',
            materialize_model_accesses (mdl i) (syscall_effect_accesses (eff i))
              = Some (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))
            /\ MInv A (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))).
  { intros i. exact (materialize_restricted H A (mdl i) _ (Hcov i) Hwf (Hinv i) (Hav i)). }
  split.
  - intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
    unfold materialized_succ. rewrite Hm. split; [exact Hinv' | apply with_vm_backing_same].
  - split.
    + intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
      unfold materialized_succ. rewrite Hm.
      eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | exact (Hsound i) | exact (Hnsp i) | exact (Hnh i) | exact Hm].
    + intros e st Hss. inversion Hss; subst;
        match goal with
        | Hp : ms_svc_pending ms = None |- _ => rewrite Hsvc in Hp; discriminate
        | Hp : ms_svc_pending ms = Some ?x |- _ =>
            rewrite Hsvc in Hp; injection Hp as <-
        end;
        match goal with
        | Hsp : syscall_spec _ _ Unmodeled |- _ => exfalso; exact (Hunm Hsp)
        | _ => idtac
        end.
      * (* [comment removed for export] *)
        match goal with
        | Hsp : syscall_spec _ _ (Ok ?ef ?m ?ev), Hns : ~ spurious_refusal_cfg _ _ _ ?ef |- _ =>
            destruct (Hcompl _ _ _ Hsp Hns) as [i Ei]; injection Ei as -> -> ->
        end.
        exists i. split; [reflexivity|].
        unfold materialized_succ.
        match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite Hm end.
        reflexivity.
      * (* [comment removed for export] *)
        match goal with
        | Hsp : syscall_spec _ _ (Ok ?ef ?m ?ev), Hns : ~ spurious_refusal_cfg _ _ _ ?ef |- _ =>
            destruct (Hcompl _ _ _ Hsp Hns) as [i Ei]; injection Ei as -> -> ->
        end.
        destruct (Hmat i) as (mat' & Hm & _).
        match goal with Hn : materialize_model_accesses _ _ = None |- _ => rewrite Hm in Hn; discriminate end.
      * (* [comment removed for export] *)
        match goal with Hsp : syscall_spec _ _ (Ok ?ef ?m ?ev), Hc : m_halted ?m = Some _ |- _ =>
          rewrite (Hnoh _ _ _ Hsp) in Hc; discriminate end.
      * (* [comment removed for export] *)
        match goal with Hsp : syscall_spec _ _ (Ok ?ef ?m ?ev), Hk : m_killed ?m = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnoh _ _ _ Hsp)) in Hk; discriminate end.
Qed.
End SyscallNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkH (L : list (word * word)) (A : list (Z * Z)) : word -> bool :=
  fun a => page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a)).

Lemma page_in_ranges_incl : forall p l L,
  incl l L -> page_in_ranges p l = true -> page_in_ranges p L = true.
Proof.
  intros p l L Hincl Hp. unfold page_in_ranges in *.
  apply existsb_exists in Hp as (r & Hin & Hr).
  apply existsb_exists. exists r. split; [exact (Hincl r Hin) | exact Hr].
Qed.

Lemma lazy_cover_mkH : forall L A lazy,
  incl lazy L -> lazy_cover (mkH L A) lazy A.
Proof.
  intros L A lazy Hincl w Hl Hw. unfold mkH in Hw.
  rewrite (page_in_ranges_incl _ _ _ Hincl Hl) in Hw. cbn in Hw.
  destruct (page_allowedb A (page_base w)); [reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
Definition seg_top (seg : Segment) : Z :=
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.

Definition wx_segs_nowrap_b (segs : list Segment) : bool :=
  forallb (fun seg => negb (seg_executable seg && seg_writable seg)
                      || (seg_top seg <=? 2 ^ 64)%Z) segs.

Lemma wx_segs_nowrap_of_b : forall segs,
  wx_segs_nowrap_b segs = true -> wx_segs_nowrap segs.
Proof.
  intros segs Hb seg Hin Hwx. unfold wx_segs_nowrap_b in Hb.
  rewrite forallb_forall in Hb. specialize (Hb seg Hin). rewrite Hwx in Hb. cbn in Hb.
  apply Z.leb_le in Hb. exact Hb.
Qed.

Definition segs_below_b (segs : list Segment) (top : Z) : bool :=
  forallb (fun seg => (seg_top seg <=? top)%Z) segs.

Lemma find_segment1_none_above : forall segs top x,
  segs_below_b segs top = true -> (top <= x)%Z -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros top x Hb Hx; [reflexivity|].
  cbn [segs_below_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply Z.leb_le in Hs. unfold seg_top in Hs.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z
    with false.
  - exact (IH top x Hl Hx).
  - symmetry. apply andb_false_iff. right. apply Z.leb_gt. lia.
Qed.

(* [comment removed for export] *)
Lemma H_off_segments_above : forall segs (H : word -> bool) top,
  segs_below_b segs top = true ->
  (forall a, H a = true -> (top <= bv_unsigned a)%Z) ->
  H_off_segments segs H.
Proof.
  intros segs H top Hb Ha a HHa. exact (find_segment1_none_above segs top _ Hb (Ha a HHa)).
Qed.

(* [comment removed for export] *)
Definition ranges_from_b (L : list (word * word)) (top : Z) : bool :=
  forallb (fun r => (top <=? bv_unsigned (fst r))%Z) L.

Lemma page_base_le : forall a, (bv_unsigned (page_base a) <= bv_unsigned a)%Z.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.ZArith.BinInt.Z.div_pos); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@kc__4); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@stdpp.bitvector.definitions.bv_wrap_small); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_base)|] [|@z; @__ff; @__varmap; @__wit; @__arith; @__x1; @__sat1; @__sat0; @H7; @H6; @H5; @H4; @r; @q; @H3; @H2; @H1; @H0; @H; @Ha; @__x2; @__x3; @__p1; @__sat3; @__sat2; @q0; @heq_q; @__x4; @Hq; @Hmb; @Hdm; @a|] "#(C#@$9#H#]#Q#^#\###$#M#d#%#&#(#|#V#'#F#.#4#@#c#T#r#q#3#2#:#1$0#g#h#i#n#t#u#)#v#w#,#x#-#0#6$%#/#9$,$4$6#=#7#G#D#C#O#S#U#W#X#Y#[#Z#e#k#l#f#m#*#+#5#~#s$#$$$&#8#;$/$.$3$5#?$8$9$7$:$;$<#N#L#R#P#j#E#J#`#_#p#K#{$)#y#o$+$*#z#}#I#b#a$-$($'$1$2>#z%#{%#|%#}%#~&$#$$$%$%'$&*$'%$(%$)+$*&$+($,%$-$$.%$/%$0%$1%$2$$3%$4&$5%$6&$7'$8*(R(#(#(#(#(#USF#USG#$$H-#J)#J6'#$(I#H#j#$C#VSH+H#E*USI-%,#&%#USJPUSKPUSLCUSMCUSNC(6(#(#(#(#(#7#8C#8CE*C$S&#+-GDDF#KZSO.GDDF#VSP/FVS/S0S1VSQHL'S0#S1m$%#WSRCEIXSSHL$#l#%*)#l#&98#l#'<;#'C2Ek###STl#(%#H'CJEUS2#m#%#WS's#+J#-s#,J)J#,s#.J1$#'Cs#0#$s#7L*C=S(>+s#'GDDF#Kl#%#;5l#&s#+s#*#l#'s#.s#-#%Es#$l#($#H%EJm#$#WS),J#,-J#E#%$J&$#$s#FMVS3#s#.#E$#Es#0$s#JN,#s#2#E#k##&#k##(#$s#OQVS4#s#7#E$$s#RS5-#s#:#E#k##.#k##'#VS'/s#>US2s#/)s#@(,*s#A1$#'C,#k##'#VS).s#E$s#_SU,#s#G#E#%$s#I&$#k##s#)#VS6(s#L%s#ME$s#gSV,#s#O%s#P##$E&$#k##(#VS7(s#T$s#nS8-#s#V'C#Ek##s#H#VS9&s#Y$s#sS:,#s#['C#$k##s#M#-&s#^$s#xS#,#s#`#EH%Hs#b&$#$s#}S;#E#j##%#%Is#g#EL%Ms#i$s$'S*#E#%$s#z&$#$s$+S$#E#j##%#%%s$#$s$/SW#E#$s$1S<%#s$'US+I#ES:k##s#J#US$L4CI5CR*Cs#zO#+s$(GDDF#KUSXD.s$*GDDF$#$l#%#s#zs#tl#&)s$-#l#'s$1s$0#j#)C##EIk##s#&#k#)C#$s$DS,VH#Ql#((%#l#*34#l#+75#j#,9#j#-<#V#IHj##@#j##s#'#0s#(s#'s###S+j#.s#+#j#/s#-#V#IHj##s#0#j##s#7#0s#8s#7s#3#S8l#0s#:C#l#1s#=C#l#2s#Cs#?#l#3s#Is#E#l#4s#Rs#K#l#5s#Zs#T#l#6s#bs#\#l#+s#js#d#l#*s#ts#m#m##s#tXSYs#wJ#s#}-s#xJ#E#-s#qJ)Hs$J#Hs#pj#$C#-s#zs$MVS/C#'CH$m#$#VS3s#vs$Q#Es#w#Es#bk##s$&#k##%#VS4s#ns$V#Es#o#Es#`k##s$+#k##%#7s$z7s$vVSZ$#%E%#E%VS['&%E#k##%#k##'##E+WS\,+Ij##S=#j#7%##E*k##S=#k#7(#VS's#os$k-s#ks$l)s$m#1#s#l'Cs#n#k##s$3#VS)s#ps$q$s%/S>,#s$s#E#%$s$u&$#k##s$U#VS6(s$x,s#ss$y%s$z##$E&$#k##s$2#VS7s#xs$~$s%<S--#s%$'C#Ek##s$r#VS9&s%'$s%AS+,#s%)'C#$k##s$w#-&s%,,s#}s%-)S;s%.##s#wj##s$+#$s%JS]#E#%$s#1&$#)S$s%5$s%OS?#$#j##&#%%s#7#Es#m$s%TS^%#s#:US$IUS<L2S@2#3C#US_RVS`C#3C'9C$#3CS@/C$#/C)#:#S.;P#s%U4CL4CM<C$I#USaR5C#*Cs%NO#+s%XGDDF#KZSAs%YGDDFN=s%ZGDDF$#.s%[GDDFs%6s$4#5Cs%tWSBCs%Us$9WSbC#**C%S&#+s%`GDDF#KWSBCs$=s%Y*C#O(+s%cGDDF#K.s%dGDDF&s$=#.s%eGDDF,s$>#l#%#s%Ys%Sl#&5s%h#l#'9s%k#j#)C#j#8C#j#9C#j#:S%##EM&#Qk##s%F#)s%iI1#M'CL#)Ls%l##Mk##%#k##)#k#)C#k#8C#k#9C#k#:S%#%S#s%t$s&2ScZH$S##S,S*SCl#(4&#l#;s#<s$^#l#<s#>s$_#j#,s#@#j#-s#C#V#IHj##s#F#j##s#N#0s#Os#Ns#I#SDj#.s$u#j#/s$w#V#IHj##s$z#j##s%%#0s%&s%%s#W#S-l#0s#[C#l#=s#]C#l#2s#cs#_#l#3s#is#e#l#4s#ps#k#l#5s#xs#r#l#6s$#s#z#l#+s$(s$%#l#*s$3s$-#l#<s$;s$7#l#;s$As$=#l#>s$Cs$D#6s&Os$J#Es#g%s#hs$6&$#j##s%5##Es#d%s#es$:&$#j##s#h#2s#]2#2#3C#9Cs#^s#`/Cs#^s#\/C$#/C&#:#S.3C*9Cs#d#/C*#/Cs#c#:#S.VSds#e#;P#s&Y;P*#4CQ<C#Ls&Z<C#Is#dZSAs&ZGDDFS5=s&[GDDFs#a#.s&\GDDFs&7s%5#*Cs&TOs&U+s&^GDDF#K5Cs&v*Cs&WO#+s&aGDDF#K.s&bGDDF&s%;#*Cs%?S&&+s&dGDDF#K8Cs$aWSeC#s&x*Cs#iS(#+s&hGDDF#K*Cs&`Os#f+s&jGDDF#K*Cs#hS('+s&lGDDF#K=s&mGDDF%#.s&nGDDF(s%G#.s&oGDDFs#ms%H#.s&pGDDF.s%I#.s&qGDDF1s%J#.s&rGDDF8s%K#l#%#s&fs&`l#&=s&u#l#'As&x#j#)C#j#8C#j#9C#j#?C#j#:S%#&s#lNk##s&S##ENk##s&I#'CLN)s&yM1#N'CQ#%Ns$z)Ns&}#E#%$s$}&$#k##'#k##)#k##-#k##/#k##2#k#)C#k#8C#k#9C#k#?C#k#:S%#^Hs#uS>S#s#tS,S*LS?SCMl#(;$#l#;s$Qs%s#l#<s$Ss%t#j#,s$U#j#-s$X#V#IHj##s$[#j##s$c#0s$ds$cs#X#SDj#.s&.#j#/s&0#V#IHj##s&3#j##s&:#0s&;s&:s#b#S-l#0s$pC#l#=s$rC#l#2s$xs$t#l#3s$~s$z#l#4s%)s%$#l#5s%1s%+#l#6s%8s%3#l#+s%=s%:#l#*s%Hs%B#l#<s%Ps%L#l#;s%Vs%R#l#>s%Xs%Y#WSfs'ds%_#ZSECs%`s%^s#us#t#)HJ6s'g###s&|m#&#l#1s%fC#l#@s%js%h#l#As'-s')#l#Bs'>s'9#l#7s'es'a#VSgs'os'k$s'p#VShs'qs'mZSECs'ms'j&$#USiH$s't###s'sm#&#j#Cs'v##"). Qed.

Lemma mkH_above : forall L A top a,
  ranges_from_b L top = true -> mkH L A a = true -> (top <= bv_unsigned a)%Z.
Proof.
  intros L A top a Hb Ha. unfold mkH in Ha. apply andb_true_iff in Ha as [Hp _].
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as ([lo sz] & Hin & Hr).
  cbn [fst snd] in Hr. apply andb_true_iff in Hr as [H1 _]. apply Z.leb_le in H1.
  unfold ranges_from_b in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Hin).
  cbn [fst] in Hb. apply Z.leb_le in Hb.
  pose proof (page_base_le a). lia.
Qed.

Corollary H_off_segments_mkH : forall segs L A top,
  segs_below_b segs top = true -> ranges_from_b L top = true ->
  H_off_segments segs (mkH L A).
Proof.
  intros segs L A top Hs HL.
  apply (H_off_segments_above segs (mkH L A) top Hs).
  intros a Ha. exact (mkH_above L A top a HL Ha).
Qed.

(* [comment removed for export] *)
Lemma MInv_intro_empty : forall A m,
  m_vm_materialized m = [] ->
  (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z ->
  MInv A m.
Proof.
  intros A m He Hb. constructor; rewrite ?He;
    [constructor | intros p Hp; destruct Hp | intros p Hp; destruct Hp
    | intros p Hp; destruct Hp | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma MInv_transport : forall A m m',
  MInv A m ->
  m_vm_materialized m' = m_vm_materialized m ->
  m_vm_lazy m' = m_vm_lazy m ->
  (eager_used m' + A_bytes A <= vm_limit (m_vmmaps m'))%Z ->
  MInv A m'.
Proof.
  intros A m m' [H1 H2 H3 H4 H5] Hm Hl Hb. constructor; rewrite ?Hm, ?Hl; assumption.
Qed.

