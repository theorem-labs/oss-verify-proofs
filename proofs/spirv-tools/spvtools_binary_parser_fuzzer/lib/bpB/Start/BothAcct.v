(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BCatSim BPropExec.

Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition mrestrict (H : word -> bool) (m : word -> option byte)
    : word -> option byte :=
  fun a => if H a then None else m a.

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

Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop :=
  forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = None.

Definition wx_segs_nowrap (segs : list Segment) : Prop :=
  forall seg, In seg segs ->
    seg_executable seg && seg_writable seg = true ->
    (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z.

Definition woff (a : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned a + Z.of_nat k).

Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
  forall k, (k < n)%nat -> H (woff a k) = false.

Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop :=
  forall a n, In (a, n) l -> range_avoids H a n.

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

Lemma restrict_svc_pending : forall H ms,
  ms_svc_pending (restrict H ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma restrict_pc : forall H ms, ms_pc (restrict H ms) = ms_pc ms.
Proof. reflexivity. Qed.

Lemma restrict_mem : forall H ms, ms_mem (restrict H ms) = mrestrict H (ms_mem ms).
Proof. reflexivity. Qed.

Lemma unrestrict_mem : forall H full ms,
  ms_mem (unrestrict H full ms) = munrestrict H full (ms_mem ms).
Proof. reflexivity. Qed.

Lemma restrict_mkst : forall H regs pc mem rom,
  restrict H (mkst regs pc mem rom) = mkst regs pc (mrestrict H mem) rom.
Proof. reflexivity. Qed.

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

Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

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

Lemma interp_eff_accesses_restrict : forall t m c mr' rs,
  interp_eff_accesses segs t (mrestrict H m)
    = MachineOk (@mkAccessReport _ (c, mr') rs) ->
  exists mf',
    interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs)
    /\ mr' = mrestrict H mf'
    /\ (forall x, H x = true -> mf' x = m x)
    /\ ranges_avoid H rs.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  -
    injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    apply ranges_avoid_nil.
  -
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
  -
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

End ISA.

Definition page_allowedb (A : list (Z * Z)) (p : word) : bool :=
  existsb (fun iv => (fst iv <=? bv_unsigned p)%Z
                     && (bv_unsigned p + page_size <=? snd iv)%Z) A.

Definition A_wf (A : list (Z * Z)) : Prop :=
  Forall (fun iv => (fst iv <= snd iv)%Z /\ (fst iv) mod page_size = 0
                    /\ (snd iv) mod page_size = 0)%Z A.

Fixpoint A_bytes (A : list (Z * Z)) : Z :=
  match A with
  | [] => 0
  | iv :: r => (snd iv - fst iv) + A_bytes r
  end%Z.

Definition lazy_cover (H : word -> bool) (lazy : list (word * word))
    (A : list (Z * Z)) : Prop :=
  forall w : word,
    page_in_ranges (page_base w) lazy = true -> H w = false ->
    page_allowedb A (page_base w) = true.

Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m
  = (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size)%Z.
Proof. reflexivity. Qed.

Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
  minv_nodup    : List.NoDup (m_vm_materialized m);
  minv_aligned  : forall p, In p (m_vm_materialized m) ->
                    (bv_unsigned p mod page_size = 0)%Z;
  minv_allowed  : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
  minv_lazy     : forall p, In p (m_vm_materialized m) ->
                    page_in_ranges p (m_vm_lazy m) = true;
  minv_budget   : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.

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

Lemma same_but_materialized_frame : forall m m',
  same_but_materialized m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m
  /\ m_fds m' = m_fds m /\ m_pipes m' = m_pipes m /\ m_stdin m' = m_stdin m
  /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\ m_tid m' = m_tid m
  /\ m_rlimit_core m' = m_rlimit_core m /\ m_clock m' = m_clock m
  /\ eager_used m' = eager_used m.
Proof.
  intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm].
  repeat split; reflexivity.
Qed.

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

Lemma A_pages_length : forall A,
  A_wf A -> (Z.of_nat (length (A_pages A)) * page_size = A_bytes A)%Z.
Proof.
  induction A as [|[lo hi] A IH]; intros Hwf; [reflexivity|].
  cbn [A_pages A_bytes fst snd]. inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst.
  cbn [fst snd] in *.
  rewrite length_app, length_map, length_seq, Nat2Z.inj_add, Z.mul_add_distr_r.
  rewrite (IH Hwf').
  destruct (Zmod0_multiple lo Hlo) as [qlo ->].
  destruct (Zmod0_multiple hi Hhi) as [qhi ->].
  replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
  rewrite Z.div_mul by (unfold page_size; lia).
  rewrite Z2Nat.id by (unfold page_size in Hle; lia).
  reflexivity.
Qed.

Lemma A_pages_in : forall A p,
  A_wf A ->
  (bv_unsigned p mod page_size = 0)%Z ->
  page_allowedb A p = true ->
  In (bv_unsigned p) (A_pages A).
Proof.
  induction A as [|[lo hi] A IH]; intros p Hwf Hal Hpa; [discriminate|].
  inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst. cbn [fst snd] in *.
  cbn [A_pages fst snd]. apply in_or_app.
  unfold page_allowedb in Hpa. cbn [existsb fst snd] in Hpa.
  apply orb_true_iff in Hpa as [Hpa | Hpa].
  - left. apply andb_true_iff in Hpa as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (Zmod0_multiple lo Hlo) as [qlo Eqlo].
    destruct (Zmod0_multiple hi Hhi) as [qhi Eqhi].
    destruct (Zmod0_multiple (bv_unsigned p) Hal) as [qp Eqp].
    rewrite Eqp in *. rewrite Eqlo, Eqhi in *.
    replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
    rewrite Z.div_mul by (unfold page_size; lia).
    apply in_map_iff. exists (Z.to_nat (qp - qlo)).
    unfold page_size in *.
    split.
    + rewrite Z2Nat.id by lia. lia.
    + apply in_seq. lia.
  - right. apply IH; [exact Hwf' | exact Hal | exact Hpa].
Qed.

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

Lemma two64_as_pages : (2 ^ 64 = page_size * 2 ^ 52)%Z.
Proof. reflexivity. Qed.

Lemma page_base_woff : forall a k,
  page_base (woff a k) = page_base_of (bv_unsigned a + Z.of_nat k).
Proof.
  intros a k. unfold page_base, woff, page_base_of.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  assert (Hz : (0 <= z)%Z) by (unfold z; lia).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite !two64_as_pages.
  set (r := (z mod (page_size * 2 ^ 52))%Z).
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).

  pose proof (Z.div_mod z (page_size * 2 ^ 52) ltac:(lia)) as Hdm.
  fold r in Hdm.
  set (q := (z / (page_size * 2 ^ 52))%Z) in Hdm.
  assert (Hfl : (z / page_size * page_size = page_size * 2 ^ 52 * q + r / page_size * page_size)%Z).
  { rewrite Hdm at 1.
    replace (page_size * 2 ^ 52 * q + r)%Z with (r + (2 ^ 52 * q) * page_size)%Z by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite Hfl.
  replace (page_size * 2 ^ 52 * q + r / page_size * page_size)%Z
    with (r / page_size * page_size + q * (page_size * 2 ^ 52))%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

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

Lemma m_vm_materialized_wvb : forall l X m,
  m_vm_materialized (with_vm_backing l X m) = X.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : forall l X m, m_vm_lazy (with_vm_backing l X m) = l.
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : forall l X m, m_vmmaps (with_vm_backing l X m) = m_vmmaps m.
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

Section Nodes.
Variable segs : list Segment.
Context {SC : StepCfg}.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs the_scfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs the_scfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

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

Variable P : config -> Prop.
Hypothesis P_silent1 : forall c c',
  node_ok c unit (fun _ => []) (fun _ => c') -> P c' -> P c.

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

Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses.
  unfold newly_materialized_pages. cbn [accesses_pages List.filter].
  rewrite with_vm_backing_id. reflexivity.
Qed.

Definition materialized_succ (m : Model) (accs : list (word * nat)) : Model :=
  match materialize_model_accesses m accs with
  | Some m' => m'
  | None => m
  end.

Section SyscallNode.
Variable segs : list Segment.
Context {SC : StepCfg}.
Variable H : word -> bool.

End SyscallNode.

Definition mkH (L : list (word * word)) (A : list (Z * Z)) : word -> bool :=
  fun a => page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a)).

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

Definition ranges_from_b (L : list (word * word)) (top : Z) : bool :=
  forallb (fun r => (top <=? bv_unsigned (fst r))%Z) L.

Lemma page_base_le : forall a, (bv_unsigned (page_base a) <= bv_unsigned a)%Z.
Proof.
  intros a. unfold page_base, page_base_of. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hmb.
  assert (Hq : (0 <= bv_unsigned a / page_size)%Z)
    by (apply Z.div_pos; unfold page_size in *; lia).
  set (q := (bv_unsigned a / page_size)%Z) in *.
  change (bv_modulus 64) with (2 ^ 64)%Z in *. unfold page_size in *.
  rewrite bv_wrap_small; [lia|].
  change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.

Lemma MInv_transport : forall A m m',
  MInv A m ->
  m_vm_materialized m' = m_vm_materialized m ->
  m_vm_lazy m' = m_vm_lazy m ->
  (eager_used m' + A_bytes A <= vm_limit (m_vmmaps m'))%Z ->
  MInv A m'.
Proof.
  intros A m m' [H1 H2 H3 H4 H5] Hm Hl Hb. constructor; rewrite ?Hm, ?Hl; assumption.
Qed.

