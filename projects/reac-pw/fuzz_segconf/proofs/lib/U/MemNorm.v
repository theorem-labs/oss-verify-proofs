From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require YK1j YO0d YP09 YL0g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma wa_shift : forall (a : word) (i : nat),
  wa (bv_unsigned (a + 1) + Z.of_nat i) = wa (bv_unsigned a + Z.of_nat (S i)).
Proof.
  intros a i. unfold wa. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  change (bv_unsigned (1:word)) with 1%Z.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma seg_ov_read_ext : forall n m m0 s a,
  (forall i, (i < n)%nat -> m (wa (bv_unsigned a + Z.of_nat i)) = m0 (wa (bv_unsigned a + Z.of_nat i))) ->
  seg_ov_read_bytes m s a n = seg_ov_read_bytes m0 s a n.
Proof.
  induction n as [|n IH]; intros m m0 s a H; [reflexivity|].
  cbn [seg_ov_read_bytes].
  assert (H0 : m a = m0 a).
  { pose proof (H 0%nat ltac:(lia)) as E. cbn [Z.of_nat] in E. unfold wa in E.
    rewrite Z_to_bv_plus0 in E. exact E. }
  rewrite H0, (IH m m0 s); [reflexivity|].
  intros i Hi. rewrite !wa_shift. apply H. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition normalize (m : word -> option byte) : word -> option byte :=
  fun a => if ro_addr segs a then None else m a.

Definition mem_rel (m m0 : word -> option byte) : Prop :=
  (forall a, m0 a = normalize m a) /\
  (forall a b, ro_addr segs a = true -> m a = Some b -> seg_rom segs a = Some b).

Definition ro_agree (m : word -> option byte) : Prop :=
  forall a, ro_addr segs a = true -> mrd segs m a = seg_rom segs a.

Definition ro_same (m m' : word -> option byte) : Prop :=
  forall a, ro_addr segs a = true -> m' a = m a.

Definition ms_rel (s s0 : machine_state) : Prop :=
  ms_regs s = ms_regs s0 /\ ms_fregs s = ms_fregs s0 /\ ms_pc_val s = ms_pc_val s0 /\
  ms_svc_pending s = ms_svc_pending s0 /\ ms_resv s = ms_resv s0 /\ ms_fcsr s = ms_fcsr s0 /\
  ms_rom s = ms_rom s0 /\ mem_rel (ms_mem s) (ms_mem s0).

Definition wx_apart : bool :=
  forallb (fun s =>
    orb (negb (andb (seg_executable s) (seg_writable s)))
        (andb (Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z (2 ^ 64)%Z)
              (forallb (fun s' =>
                 orb (orb (seg_writable s')
                          (Z.leb (Z.of_N (seg_base s') + Z.of_N (seg_size s'))%Z (Z.of_N (seg_base s))))
                     (Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z (Z.of_N (seg_base s')))) segs))) segs.

Lemma mem_inv_normalize : forall m, mem_inv segs (normalize m).
Proof.
  intros m a b H. unfold normalize in H. revert H.
  destruct (ro_addr segs a); intros H; cbv beta iota in H; [discriminate H | reflexivity].
Qed.

Lemma mem_rel_normalize : forall m, ro_agree m -> mem_rel m (normalize m).
Proof.
  intros m H. split; [intros a; reflexivity|].
  intros a b Hro Hm. rewrite <- (H a Hro). unfold mrd. rewrite Hm. reflexivity.
Qed.

Lemma ro_agree_of_mem_rel : forall m m0, mem_rel m m0 -> ro_agree m.
Proof.
  intros m m0 [_ H] a Hro. unfold mrd. destruct (m a) as [b|] eqn:E; [|reflexivity].
  symmetry. exact (H a b Hro E).
Qed.

Lemma mem_rel_rw : forall m m0 a, mem_rel m m0 -> ro_addr segs a = false -> m0 a = m a.
Proof. intros m m0 a [H _] E. rewrite H. unfold normalize. rewrite E. reflexivity. Qed.

Lemma mem_rel_ro : forall m m0 a, mem_rel m m0 -> ro_addr segs a = true -> m0 a = None.
Proof. intros m m0 a [H _] E. rewrite H. unfold normalize. rewrite E. reflexivity. Qed.

Lemma mrd_rel : forall m m0 a, mem_rel m m0 -> mrd segs m a = mrd segs m0 a.
Proof.
  intros m m0 a HR. destruct (ro_addr segs a) eqn:E.
  - rewrite (ro_agree_of_mem_rel m m0 HR a E). unfold mrd. rewrite (mem_rel_ro m m0 a HR E). reflexivity.
  - unfold mrd. rewrite (mem_rel_rw m m0 a HR E). reflexivity.
Qed.

Lemma rdn_S : forall m a n, rdn segs m a (S n) =
  match mrd segs m a with
  | Some b => match rdn segs m (a + 1) n with Some r => Some (b :: r) | None => None end
  | None => None
  end.
Proof. intros. reflexivity. Qed.

Lemma rdn_rel : forall m m0 n a, mem_rel m m0 -> rdn segs m a n = rdn segs m0 a n.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR; [reflexivity|].
  rewrite !rdn_S, (mrd_rel m m0 a HR), IH by exact HR. reflexivity.
Qed.

Lemma ov_read_rel : forall m m0 a n, mem_rel m m0 -> ov_read_bytes segs m a n = ov_read_bytes segs m0 a n.
Proof. intros m m0 a n HR. rewrite !ov_rdn. apply rdn_rel. exact HR. Qed.

Lemma wview_rel_rw : forall m m0 a, mem_rel m m0 -> ro_addr segs a = false -> wview segs m0 a = wview segs m a.
Proof. intros m m0 a HR E. unfold wview. rewrite (mem_rel_rw m m0 a HR E). reflexivity. Qed.

Lemma ro_false_of_wview : forall m m0 a, mem_rel m m0 -> wview segs m0 a <> None -> ro_addr segs a = false.
Proof.
  intros m m0 a HR Hw. destruct (ro_addr segs a) eqn:E; [|reflexivity].
  exfalso. apply Hw. unfold wview. rewrite (mem_rel_ro m m0 a HR E).
  revert E. unfold ro_addr.
  destruct (find_segment segs (bv_unsigned a) 1) as [s|]; intros E; cbv beta iota in E |- *; [|discriminate E].
  apply negb_true_iff in E. rewrite E. reflexivity.
Qed.

Lemma store_ok_rel : forall m m0 n a, mem_rel m m0 -> store_ok segs m0 a n = true -> store_ok segs m a n = true.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR Hs; [reflexivity|].
  cbn [store_ok] in Hs |- *. revert Hs.
  destruct (wview segs m0 a) eqn:E; intros Hs; cbv beta iota in Hs; [|discriminate Hs].
  rewrite <- (wview_rel_rw m m0 a HR (ro_false_of_wview m m0 a HR ltac:(rewrite E; discriminate))).
  rewrite E. exact (IH _ HR Hs).
Qed.

Fixpoint all_rw (a : word) (n : nat) : Prop :=
  match n with
  | O => True
  | S n' => ro_addr segs a = false /\ all_rw (a + 1) n'
  end.

Lemma store_ok_all_rw : forall m m0 n a, mem_rel m m0 -> store_ok segs m0 a n = true -> all_rw a n.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR Hs; [exact I|].
  cbn [store_ok] in Hs. revert Hs.
  destruct (wview segs m0 a) eqn:E; intros Hs; cbv beta iota in Hs; [|discriminate Hs].
  split.
  - apply (ro_false_of_wview m m0 a HR). rewrite E. discriminate.
  - exact (IH _ HR Hs).
Qed.

Lemma write_rw : forall bs m m0 a, (forall x, m0 x = normalize m x) -> all_rw a (length bs) ->
  forall x, write_to_mem m0 a bs x = normalize (write_to_mem m a bs) x.
Proof.
  induction bs as [|b bs IH]; intros m m0 a H Hw x; [apply H|].
  destruct Hw as [Ha Hw]. cbn [write_to_mem]. apply IH; [|exact Hw].
  intros y. unfold normalize. cbv beta. destruct (bv_eqb y a) eqn:E.
  - unfold bv_eqb in E. apply Z.eqb_eq in E. assert (y = a) as -> by (apply bv_eq; exact E).
    rewrite Ha. reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma write_ro_same : forall bs m a x, all_rw a (length bs) -> ro_addr segs x = true -> write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hw Hx; [reflexivity|].
  destruct Hw as [Ha Hw]. cbn [write_to_mem]. rewrite (IH _ _ x Hw Hx). cbv beta.
  destruct (bv_eqb x a) eqn:E; [|reflexivity].
  unfold bv_eqb in E. apply Z.eqb_eq in E. assert (x = a) as -> by (apply bv_eq; exact E).
  congruence.
Qed.

Lemma interp_rel : forall t m m0 r0, mem_rel m m0 ->
  interp_eff_accesses segs t m0 = MachineOk r0 ->
  exists r, interp_eff_accesses segs t m = MachineOk r /\
    fst (@access_value _ r) = fst (@access_value _ r0) /\
    mem_rel (snd (@access_value _ r)) (snd (@access_value _ r0)) /\
    ro_same m (snd (@access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m m0 r0 HR H;
    cbn [interp_eff_accesses] in H |- *; try discriminate H.
  - injection H as <-. eexists. split; [reflexivity|]. cbn [access_value fst snd].
    split; [reflexivity|]. split; [exact HR|]. intros x _. reflexivity.
  - rewrite (ov_read_rel m m0 a _ HR). revert H.
    destruct (ov_read_bytes segs m0 a (width_bytes n)) as [bs|]; intros H; cbn beta iota in H |- *;
      [|discriminate H].
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses segs ?t m0] => destruct (interp_eff_accesses segs t m0) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ m m0 r1 HR E1) as (r & Er & Ef & Erel & Ero). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value].
    split; [exact Ef|]. split; [exact Erel|]. exact Ero.
  - revert H. destruct (store_ok segs m0 a (width_bytes n)) eqn:Es; intros H; cbn beta iota in H;
      [|discriminate H].
    rewrite (store_ok_rel m m0 _ a HR Es). cbn beta iota.
    pose proof (store_ok_all_rw m m0 _ a HR Es) as Hw.
    rewrite <- (length_Z_to_le_bytes (width_bytes n) (bv_unsigned v)) in Hw.
    assert (HR' : mem_rel (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
                          (write_to_mem m0 a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    { split.
      - exact (write_rw _ m m0 a (proj1 HR) Hw).
      - intros x b Hx Hb. rewrite (write_ro_same _ m a x Hw Hx) in Hb. exact (proj2 HR x b Hx Hb). }
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses segs k (write_to_mem m0 ?x ?y)] =>
        destruct (interp_eff_accesses segs k (write_to_mem m0 x y)) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ _ r1 HR' E1) as (r & Er & Ef & Erel & Ero). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value].
    split; [exact Ef|]. split; [exact Erel|].
    intros x Hx. rewrite (Ero x Hx). exact (write_ro_same _ m a x Hw Hx).
Qed.

Lemma decode_rel : forall s s0 w s0', ms_rel s s0 ->
  drop_access_report (decode_exec_accesses segs s0 w) = MachineOk s0' ->
  exists s', drop_access_report (decode_exec_accesses segs s w) = MachineOk s' /\
    ms_rel s' s0' /\ ro_same (ms_mem s) (ms_mem s').
Proof.
  intros [R F pc svc rv fc m ro] [R0 F0 pc0 svc0 rv0 fc0 m0 ro0] w s0' Hrel.
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in *.
  subst R0 F0 pc0 svc0 rv0 fc0 ro0.
  unfold decode_exec_accesses, ms_reg.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem].
  destruct (is_ecall w).
  - intros H. cbn [drop_access_report access_value] in H. injection H as <-.
    eexists. split; [reflexivity|]. split.
    + refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
      exact HR.
    + intros a _. reflexivity.
  - destruct (decode_any w) as [[i isz]|].
    + lazymatch goal with
      | |- context [interp_eff_accesses segs ?t m0] =>
          destruct (interp_eff_accesses segs t m0) as [r0| |] eqn:E
      end; intros H; cbn [drop_access_report] in H; try discriminate H.
      destruct (interp_rel _ m m0 r0 HR E) as (r & Er & Ef & Erel & Ero). rewrite Er.
      destruct r0 as [[c0 m0'] acc0], r as [[c m'] acc].
      cbn [drop_access_report access_value fst snd] in *. subst c0. injection H as <-.
      eexists. split; [reflexivity|]. split; [|exact Ero].
      refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
      exact Erel.
    + destruct (is_defined_illegal w); intros H; cbn [drop_access_report] in H; discriminate H.
Qed.

Lemma wx_apart_sound : wx_apart = true -> forall s, In s segs ->
  andb (seg_executable s) (seg_writable s) = true ->
  (Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 2 ^ 64)%Z /\
  forall s', In s' segs -> seg_writable s' = false ->
    (Z.of_N (seg_base s') + Z.of_N (seg_size s') <= Z.of_N (seg_base s))%Z \/
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <= Z.of_N (seg_base s'))%Z.
Proof.
  intros H s Hs Hxw. unfold wx_apart in H. rewrite forallb_forall in H.
  specialize (H s Hs). cbv beta in H. rewrite Hxw in H. cbn [negb orb] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].
  intros s' Hs' Hw'. rewrite forallb_forall in H2. specialize (H2 s' Hs'). cbv beta in H2.
  rewrite Hw' in H2. cbn [orb] in H2.
  apply orb_prop in H2 as [H2|H2]; apply Z.leb_le in H2; [left|right]; exact H2.
Qed.

Lemma ro_addr_false_of_wx : wx_apart = true -> forall s x, In s segs ->
  andb (seg_executable s) (seg_writable s) = true ->
  (Z.of_N (seg_base s) <= bv_unsigned x < Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z ->
  ro_addr segs x = false.
Proof.
  intros Hwx s x Hin Hxw Hx. unfold ro_addr.
  destruct (find_segment segs (bv_unsigned x) 1) as [s'|] eqn:Hf; cbv beta iota; [|reflexivity].
  destruct (seg_writable s') eqn:Hw; [reflexivity|]. exfalso.
  pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [H1 H2].
  pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin'.
  destruct (wx_apart_sound Hwx s Hin Hxw) as [_ Hsep].
  destruct (Hsep s' Hin' Hw); lia.
Qed.

Lemma code_read_ov_rel : forall m m0, wx_apart = true -> mem_rel m m0 ->
  forall addr n, code_read_ov segs m addr n = code_read_ov segs m0 addr n.
Proof.
  intros m m0 Hwx HR addr n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned addr) (Z.of_N n)) as [s|] eqn:Hf; cbv beta iota; [|reflexivity].
  destruct (andb (seg_executable s) (seg_writable s)) eqn:Hxw; cbv beta iota; [|reflexivity].
  apply seg_ov_read_ext. intros i Hi.
  pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [H1 H2].
  pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin.
  pose proof (u64_range addr) as Ha.
  assert (Hi' : (Z.of_nat i < Z.of_N n)%Z) by (pose proof (N_nat_Z n); lia).
  destruct (wx_apart_sound Hwx s Hin Hxw) as [Htop _].
  symmetry. apply (mem_rel_rw m m0 _ HR).
  apply (ro_addr_false_of_wx Hwx s); [exact Hin | exact Hxw |].
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma fetch_word_ov_rel : forall m m0, wx_apart = true -> mem_rel m m0 ->
  forall pc, fetch_word_ov segs m pc = fetch_word_ov segs m0 pc.
Proof. intros m m0 Hwx HR pc. unfold fetch_word_ov. rewrite (code_read_ov_rel m m0 Hwx HR). reflexivity. Qed.

Lemma fetch_half_any_rel : forall m m0, wx_apart = true -> mem_rel m m0 ->
  forall pc, fetch_half_any segs m pc = fetch_half_any segs m0 pc.
Proof.
  intros m m0 Hwx HR pc. unfold fetch_half_any, fetch_half_ov.
  rewrite (code_read_ov_rel m m0 Hwx HR). reflexivity.
Qed.

Lemma fetch_tail_any_rel : forall m m0, wx_apart = true -> mem_rel m m0 ->
  forall pc, fetch_tail_any segs m pc = fetch_tail_any segs m0 pc.
Proof.
  intros m m0 Hwx HR pc. unfold fetch_tail_any.
  rewrite !(fetch_half_any_rel m m0 Hwx HR). reflexivity.
Qed.

Lemma fetch_failure_not_ok : forall m a st, fetch_failure segs m a <> MachineOk st.
Proof.
  intros m a st. unfold fetch_failure.
  match goal with |- (if ?c then _ else _) <> _ => destruct c end; cbv beta iota zeta; [discriminate|].
  match goal with |- (if ?c then _ else _) <> _ => destruct c end; cbv beta iota; discriminate.
Qed.

Lemma step_rel : forall s s0 s0', wx_apart = true -> ms_rel s s0 ->
  RiscvSemantics.step segs s0 = MachineOk s0' ->
  exists s', RiscvSemantics.step segs s = MachineOk s' /\ ms_rel s' s0' /\ ro_same (ms_mem s) (ms_mem s').
Proof.
  intros s s0 s0' Hwx Hrel H. pose proof Hrel as (_ & _ & Ep & _ & _ & _ & _ & HR).
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses, ms_pc in H |- *.
  rewrite Ep, (fetch_word_ov_rel _ _ Hwx HR), (fetch_tail_any_rel _ _ Hwx HR).
  revert H.
  destruct (fetch_word segs (ms_pc_val s0)) as [w|]; [intros H; exact (decode_rel s s0 w s0' Hrel H)|].
  destruct (fetch_word_ov segs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (decode_rel s s0 w s0' Hrel H)|].
  destruct (fetch_tail_any segs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (decode_rel s s0 w s0' Hrel H)|].
  destruct (fetch_failure segs (ms_mem s0) (ms_pc_val s0)) as [st| |] eqn:Ef.
  - exfalso. exact (fetch_failure_not_ok _ _ _ Ef).
  - intros H. cbn [drop_access_report] in H. discriminate H.
  - intros H. cbn [drop_access_report] in H. discriminate H.
Qed.

Lemma msteps_rel : wx_apart = true -> forall s0 s0', msteps segs s0 s0' ->
  forall s, ms_rel s s0 -> exists s', msteps segs s s' /\ ms_rel s' s0' /\ ro_same (ms_mem s) (ms_mem s').
Proof.
  intros Hwx s0 s0' H. induction H as [x|x y z [Hsvc Hst] HT IH]; intros s Hrel.
  - exists s. split; [apply msteps_refl|]. split; [exact Hrel|]. intros a _. reflexivity.
  - destruct (step_rel s x y Hwx Hrel Hst) as (t & Et & Rt & Ot).
    destruct (IH t Rt) as (s' & Es' & Rs' & Os').
    exists s'. split; [|split; [exact Rs'|]].
    + apply (msteps_cons segs s t s'); [|exact Es']. split; [|exact Et].
      destruct Hrel as (_ & _ & _ & Esvc & _). rewrite Esvc. exact Hsvc.
    + intros a Ha. rewrite (Os' a Ha). exact (Ot a Ha).
Qed.

Theorem evt_rel : forall (Q : machine_state -> Prop) s s0, wx_apart = true -> ms_rel s s0 ->
  evt segs Q s0 ->
  evt segs (fun s' => exists s0', Q s0' /\ ms_rel s' s0' /\ ro_same (ms_mem s) (ms_mem s')) s.
Proof.
  intros Q s s0 Hwx Hrel (s0' & Hs & HQ).
  destruct (msteps_rel Hwx s0 s0' Hs s Hrel) as (s' & Hs' & Hr & Ho).
  exists s'. split; [exact Hs'|]. exists s0'. split; [exact HQ|]. split; [exact Hr | exact Ho].
Qed.

Theorem evt_rel_MS : forall (Q : machine_state -> Prop) R F pc fc rv m m0 ro,
  wx_apart = true -> mem_rel m m0 ->
  evt segs Q (MS R F pc fc rv m0 ro) ->
  evt segs (fun s => exists s0, Q s0 /\ ms_rel s s0 /\ ro_same m (ms_mem s)) (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m m0 ro Hwx HR H.
  exact (evt_rel Q (MS R F pc fc rv m ro) (MS R F pc fc rv m0 ro) Hwx
    (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl HR))))))) H).
Qed.

Theorem evt_normalize : forall (Q : machine_state -> Prop) R F pc fc rv m ro,
  wx_apart = true -> ro_agree m ->
  evt segs Q (MS R F pc fc rv (normalize m) ro) ->
  evt segs (fun s => exists s0, Q s0 /\ ms_rel s s0 /\ ro_same m (ms_mem s)) (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m ro Hwx Hro H.
  exact (evt_rel_MS Q R F pc fc rv m (normalize m) ro Hwx (mem_rel_normalize m Hro) H).
Qed.

Lemma bytes_at_rel : forall m m0 a bs, mem_rel m m0 -> bytes_at segs m a bs <-> bytes_at segs m0 a bs.
Proof.
  intros m m0 a bs HR. unfold bytes_at.
  split; intros (H1 & H2 & H3); (split; [exact H1|]); (split; [exact H2|]); intros i Hi.
  - rewrite <- (mrd_rel m m0 _ HR). exact (H3 i Hi).
  - rewrite (mrd_rel m m0 _ HR). exact (H3 i Hi).
Qed.

Lemma bytes_at_normalize : forall m a bs, ro_agree m -> bytes_at segs m a bs -> bytes_at segs (normalize m) a bs.
Proof. intros m a bs Hro H. exact (proj1 (bytes_at_rel m (normalize m) a bs (mem_rel_normalize m Hro)) H). Qed.

Lemma wr_at_rel : forall m m0 a n, mem_rel m m0 -> wr_at segs m0 a n -> wr_at segs m a n.
Proof.
  intros m m0 a n HR (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  pose proof (H3 i Hi) as W.
  rewrite <- (wview_rel_rw m m0 _ HR (ro_false_of_wview m m0 _ HR W)). exact W.
Qed.

Lemma wr_at_norm : forall m m0 a n, mem_rel m m0 -> wr_at segs m a n ->
  (forall i, (0 <= i < n)%Z -> ro_addr segs (wa (a + i)) = false) -> wr_at segs m0 a n.
Proof.
  intros m m0 a n HR (H1 & H2 & H3) Hro. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite (wview_rel_rw m m0 _ HR (Hro i Hi)). exact (H3 i Hi).
Qed.

Lemma munch_rel : forall W m m0 m' m0', mem_rel m m0 -> mem_rel m' m0' -> ro_same m m' ->
  munch W m0 m0' -> munch W m m'.
Proof.
  intros W m m0 m' m0' HR HR' Ho H x Hx. destruct (ro_addr segs x) eqn:E.
  - exact (Ho x E).
  - rewrite <- (mem_rel_rw m' m0' x HR' E), <- (mem_rel_rw m m0 x HR E). exact (H x Hx).
Qed.

Lemma wmono_rel : forall m m0 m' m0', mem_rel m m0 -> mem_rel m' m0' -> ro_same m m' ->
  wmono segs m0 m0' -> wmono segs m m'.
Proof.
  intros m m0 m' m0' HR HR' Ho H x Hx. destruct (ro_addr segs x) eqn:E.
  - unfold wview in Hx |- *. rewrite (Ho x E). exact Hx.
  - rewrite <- (wview_rel_rw m' m0' x HR' E). apply H.
    rewrite (wview_rel_rw m m0 x HR E). exact Hx.
Qed.

Lemma mem_unchanged_rel : forall m m0 m' m0', mem_rel m m0 -> mem_rel m' m0' -> ro_same m m' ->
  (forall x, m0' x = m0 x) -> forall x, m' x = m x.
Proof.
  intros m m0 m' m0' HR HR' Ho H x.
  exact (munch_rel nil m m0 m' m0' HR HR' Ho (fun y _ => H y) x I).
Qed.

Lemma ro_agree_same : forall m m', ro_agree m -> ro_same m m' -> ro_agree m'.
Proof. intros m m' H Ho a E. unfold mrd. rewrite (Ho a E). exact (H a E). Qed.

Lemma mbyte_rel : forall m m0 a, mem_rel m m0 -> YP09.mbyte segs m a = YP09.mbyte segs m0 a.
Proof. intros m m0 a HR. unfold YP09.mbyte. exact (mrd_rel m m0 (Z_to_bv 64 a) HR). Qed.

Lemma writable_at_rel : forall m m0 a, mem_rel m m0 -> YP09.writable_at segs m0 a -> YP09.writable_at segs m a.
Proof.
  intros m m0 a HR H. unfold YP09.writable_at in *.
  rewrite <- (wview_rel_rw m m0 _ HR (ro_false_of_wview m m0 _ HR H)). exact H.
Qed.

Lemma mbyte_munch : forall W m m' a, munch W m m' -> (0 <= a < 2 ^ 64)%Z -> outside W a ->
  YP09.mbyte segs m' a = YP09.mbyte segs m a.
Proof.
  intros W m m' a H Ha Ho. unfold YP09.mbyte. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit by exact Ha. exact Ho.
Qed.

End WithSegs.

Lemma so_dle : forall x y : Z, (x <= y)%Z \/ ~ (x <= y)%Z.
Proof. intros. lia. Qed.
Lemma so_dlt : forall x y : Z, (x < y)%Z \/ ~ (x < y)%Z.
Proof. intros. lia. Qed.
Lemma so_deq : forall x y : Z, x = y \/ x <> y.
Proof. intros. lia. Qed.
Lemma so_dand : forall A B : Prop, A \/ ~ A -> B \/ ~ B -> (A /\ B) \/ ~ (A /\ B).
Proof. tauto. Qed.
Lemma so_dor : forall A B : Prop, A \/ ~ A -> B \/ ~ B -> (A \/ B) \/ ~ (A \/ B).
Proof. tauto. Qed.

Lemma static_owned_dec : forall (B : YO0d.malloc_syms) a, YO0d.static_owned B a \/ ~ YO0d.static_owned B a.
Proof.
  intros B a. unfold YO0d.static_owned.
  repeat first [ apply so_dor | apply so_dand | apply so_dle | apply so_dlt | apply so_deq ].
Qed.

Lemma ro_agree_of_rodata_ok : forall (B : YO0d.malloc_syms) m,
  YL0g.rodata_ok B m ->
  (forall a, YO0d.static_owned B a -> (0 <= a < 2 ^ 64)%Z ->
     ro_addr (YO0d.ms_segs B) (Z_to_bv 64 a) = true ->
     YP09.mbyte (YO0d.ms_segs B) m a = seg_rom (YO0d.ms_segs B) (Z_to_bv 64 a)) ->
  ro_agree (YO0d.ms_segs B) m.
Proof.
  intros B m Hro Hst x Hx.
  pose proof (Z_to_bv_bv_unsigned x) as Ex.
  assert (K : YP09.mbyte (YO0d.ms_segs B) m (bv_unsigned x) =
              seg_rom (YO0d.ms_segs B) (Z_to_bv 64 (bv_unsigned x))).
  { destruct (static_owned_dec B (bv_unsigned x)) as [Hs|Hs].
    - apply Hst; [exact Hs | exact (u64_range x) |]. rewrite Ex. exact Hx.
    - assert (Hin : YL0g.in_ro_img B (bv_unsigned x)).
      { split; [|exact Hs]. revert Hx. unfold ro_addr.
        destruct (find_segment (YO0d.ms_segs B) (bv_unsigned x) 1) as [s|] eqn:Hf; intros Hx;
          cbv beta iota in Hx; [|discriminate Hx].
        apply negb_true_iff in Hx.
        pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [H1 H2].
        exists s. split; [exact (YK1j.find_segment_in _ _ _ _ Hf)|]. split; [exact Hx|]. lia. }
      exact (Hro _ Hin). }
  unfold YP09.mbyte in K. rewrite Ex in K. exact K.
Qed.

Theorem evt_rodata : forall (B : YO0d.malloc_syms) (Q : machine_state -> Prop) R F pc fc rv m ro,
  wx_apart (YO0d.ms_segs B) = true ->
  YL0g.rodata_ok B m ->
  (forall a, YO0d.static_owned B a -> (0 <= a < 2 ^ 64)%Z ->
     ro_addr (YO0d.ms_segs B) (Z_to_bv 64 a) = true ->
     YP09.mbyte (YO0d.ms_segs B) m a = seg_rom (YO0d.ms_segs B) (Z_to_bv 64 a)) ->
  evt (YO0d.ms_segs B) Q (MS R F pc fc rv (normalize (YO0d.ms_segs B) m) ro) ->
  evt (YO0d.ms_segs B)
    (fun s => exists s0, Q s0 /\ ms_rel (YO0d.ms_segs B) s s0 /\ ro_same (YO0d.ms_segs B) m (ms_mem s))
    (MS R F pc fc rv m ro).
Proof.
  intros B Q R F pc fc rv m ro Hwx Hro Hst H.
  exact (evt_normalize _ Q R F pc fc rv m ro Hwx (ro_agree_of_rodata_ok B m Hro Hst) H).
Qed.

Section TaskMem.
Local Open Scope Z_scope.

Definition task_mem (segs : list Segment) (m : word -> option byte) : Prop :=
  forall a b, m a = Some b -> find_segment segs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE.

Definition mem_inv_cj (segs : list Segment) (m : word -> option byte) : Prop :=
  forall a b, m a = Some b ->
    Mem.ro_addr segs a = false /\ (find_segment segs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE).

Lemma mem_inv_cj_inv : forall segs m, mem_inv_cj segs m -> Mem.mem_inv segs m.
Proof. intros segs m H a b E. exact (proj1 (H a b E)). Qed.

Lemma mem_inv_cj_task : forall segs m, mem_inv_cj segs m -> task_mem segs m.
Proof. intros segs m H a b E. exact (proj2 (H a b E)). Qed.

End TaskMem.

Lemma find_segment_some : forall (l : list Segment) s (x n : Z), In s l ->
  (Z.of_N (seg_base s) <= x)%Z -> (x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z ->
  find_segment l x n <> None.
Proof.
  induction l as [|s0 rest IH]; intros s x n Hin H1 H2; [destruct Hin|].
  cbn [find_segment].
  match goal with |- (if ?c then _ else _) <> None => destruct c eqn:E end; [discriminate|].
  destruct Hin as [<-|Hin]; [|exact (IH s x n Hin H1 H2)].
  exfalso. apply andb_false_iff in E as [E|E]; apply Z.leb_gt in E; lia.
Qed.

Section WithSegsCJ.
Variable segs : list Segment.

Definition cj_drop (a : word) : bool :=
  orb (ro_addr segs a)
      (match find_segment segs (bv_unsigned a) 1 with
       | Some _ => false
       | None => Z.leb TASK_SIZE (bv_unsigned a)
       end).

Definition normalize_cj (m : word -> option byte) : word -> option byte :=
  fun a => if cj_drop a then None else m a.

Definition mem_rel_cj (m m0 : word -> option byte) : Prop :=
  (forall a, m0 a = normalize_cj m a) /\
  (forall a b, cj_drop a = true -> seg_rom segs a = Some b -> mrd segs m a = Some b).

Definition cj_same (m m' : word -> option byte) : Prop :=
  forall a, cj_drop a = true -> m' a = m a.

Definition ms_rel_cj (s s0 : machine_state) : Prop :=
  ms_regs s = ms_regs s0 /\ ms_fregs s = ms_fregs s0 /\ ms_pc_val s = ms_pc_val s0 /\
  ms_svc_pending s = ms_svc_pending s0 /\ ms_resv s = ms_resv s0 /\ ms_fcsr s = ms_fcsr s0 /\
  ms_rom s = ms_rom s0 /\ mem_rel_cj (ms_mem s) (ms_mem s0).

Lemma cj_drop_true : forall a, cj_drop a = true ->
  ro_addr segs a = true \/ (find_segment segs (bv_unsigned a) 1 = None /\ (TASK_SIZE <= bv_unsigned a)%Z).
Proof.
  intros a H. unfold cj_drop in H. apply orb_true_iff in H as [H|H]; [left; exact H|right].
  revert H. destruct (find_segment segs (bv_unsigned a) 1) eqn:E; intros H; cbv beta iota in H;
    [discriminate H|].
  split; [reflexivity|]. apply Z.leb_le. exact H.
Qed.

Lemma cj_drop_false : forall a, cj_drop a = false ->
  ro_addr segs a = false /\ (find_segment segs (bv_unsigned a) 1 <> None \/ (bv_unsigned a < TASK_SIZE)%Z).
Proof.
  intros a H. unfold cj_drop in H. apply orb_false_iff in H as [H1 H2]. split; [exact H1|].
  revert H2. destruct (find_segment segs (bv_unsigned a) 1) eqn:E; intros H2; cbv beta iota in H2;
    [left; discriminate|right].
  apply Z.leb_gt. exact H2.
Qed.

Lemma cj_drop_false_intro : forall a, ro_addr segs a = false ->
  find_segment segs (bv_unsigned a) 1 <> None \/ (bv_unsigned a < TASK_SIZE)%Z -> cj_drop a = false.
Proof.
  intros a H1 H2. unfold cj_drop. rewrite H1. cbn [orb].
  destruct (find_segment segs (bv_unsigned a) 1) eqn:E; cbv beta iota; [reflexivity|].
  destruct H2 as [H2|H2]; [exfalso; apply H2; first [exact E | reflexivity]|].
  apply Z.leb_gt. exact H2.
Qed.

Lemma cj_drop_ro : forall a, ro_addr segs a = true -> cj_drop a = true.
Proof. intros a H. unfold cj_drop. rewrite H. reflexivity. Qed.

Lemma seg_rom_unmapped : forall a, find_segment segs (bv_unsigned a) 1 = None -> seg_rom segs a = None.
Proof.
  intros a H. unfold seg_rom, memory_read.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N 1)) as [s|] eqn:E; [|reflexivity].
  exfalso. assert (E' : find_segment segs (bv_unsigned a) 1 = Some s) by exact E. congruence.
Qed.

Lemma mem_inv_cj_normalize : forall m, mem_inv_cj segs (normalize_cj m).
Proof.
  intros m a b H. unfold normalize_cj in H. revert H.
  destruct (cj_drop a) eqn:E; intros H; cbv beta iota in H; [discriminate H|].
  exact (cj_drop_false a E).
Qed.

Lemma mem_rel_cj_keep : forall m m0 a, mem_rel_cj m m0 -> cj_drop a = false -> m0 a = m a.
Proof. intros m m0 a [H _] E. rewrite H. unfold normalize_cj. rewrite E. reflexivity. Qed.

Lemma mem_rel_cj_drop : forall m m0 a, mem_rel_cj m m0 -> cj_drop a = true -> m0 a = None.
Proof. intros m m0 a [H _] E. rewrite H. unfold normalize_cj. rewrite E. reflexivity. Qed.

Lemma mem_rel_cj_normalize : forall m, ro_agree segs m -> mem_rel_cj m (normalize_cj m).
Proof.
  intros m H. split; [intros a; reflexivity|].
  intros a b E Hb. destruct (cj_drop_true a E) as [Er | [Ef _]].
  - rewrite (H a Er). exact Hb.
  - rewrite (seg_rom_unmapped a Ef) in Hb. discriminate Hb.
Qed.

Lemma mrd_rel_cj : forall m m0 a b, mem_rel_cj m m0 -> mrd segs m0 a = Some b -> mrd segs m a = Some b.
Proof.
  intros m m0 a b HR H. destruct (cj_drop a) eqn:E.
  - apply (proj2 HR a b E). unfold mrd in H. rewrite (mem_rel_cj_drop m m0 a HR E) in H. exact H.
  - unfold mrd in H |- *. rewrite (mem_rel_cj_keep m m0 a HR E) in H. exact H.
Qed.

Lemma rdn_rel_cj : forall m m0 n a bs, mem_rel_cj m m0 -> rdn segs m0 a n = Some bs -> rdn segs m a n = Some bs.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a bs HR H; [exact H|].
  rewrite rdn_S in H |- *. revert H.
  destruct (mrd segs m0 a) as [b|] eqn:E1; intros H; cbv beta iota in H; [|discriminate H].
  rewrite (mrd_rel_cj m m0 a b HR E1). revert H.
  destruct (rdn segs m0 (a + 1) n) as [r|] eqn:E2; intros H; cbv beta iota in H; [|discriminate H].
  rewrite (IH (a + 1) r HR E2). exact H.
Qed.

Lemma ov_read_rel_cj : forall m m0 a n bs, mem_rel_cj m m0 ->
  ov_read_bytes segs m0 a n = Some bs -> ov_read_bytes segs m a n = Some bs.
Proof. intros m m0 a n bs HR H. rewrite ov_rdn in H |- *. exact (rdn_rel_cj m m0 n a bs HR H). Qed.

Lemma wview_cj_drop : forall m a, cj_drop a = true -> m a = None -> wview segs m a = None.
Proof.
  intros m a E Hm. unfold wview. rewrite Hm.
  destruct (cj_drop_true a E) as [Er | [Ef _]].
  - revert Er. unfold ro_addr.
    destruct (find_segment segs (bv_unsigned a) 1) as [s|]; intros Er; cbv beta iota in Er |- *; [|reflexivity].
    apply negb_true_iff in Er. rewrite Er. reflexivity.
  - rewrite Ef. reflexivity.
Qed.

Lemma keep_of_wview_cj : forall m m0 a, mem_rel_cj m m0 -> wview segs m0 a <> None -> cj_drop a = false.
Proof.
  intros m m0 a HR Hw. destruct (cj_drop a) eqn:E; [|reflexivity].
  exfalso. apply Hw. exact (wview_cj_drop m0 a E (mem_rel_cj_drop m m0 a HR E)).
Qed.

Lemma wview_rel_cj : forall m m0 a, mem_rel_cj m m0 -> cj_drop a = false -> wview segs m0 a = wview segs m a.
Proof. intros m m0 a HR E. unfold wview. rewrite (mem_rel_cj_keep m m0 a HR E). reflexivity. Qed.

Lemma store_ok_rel_cj : forall m m0 n a, mem_rel_cj m m0 -> store_ok segs m0 a n = true -> store_ok segs m a n = true.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR Hs; [reflexivity|].
  cbn [store_ok] in Hs |- *. revert Hs.
  destruct (wview segs m0 a) eqn:E; intros Hs; cbv beta iota in Hs; [|discriminate Hs].
  rewrite <- (wview_rel_cj m m0 a HR (keep_of_wview_cj m m0 a HR ltac:(rewrite E; discriminate))).
  rewrite E. exact (IH _ HR Hs).
Qed.

Fixpoint all_keep (a : word) (n : nat) : Prop :=
  match n with
  | O => True
  | S n' => cj_drop a = false /\ all_keep (a + 1) n'
  end.

Lemma store_ok_all_keep : forall m m0 n a, mem_rel_cj m m0 -> store_ok segs m0 a n = true -> all_keep a n.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR Hs; [exact I|].
  cbn [store_ok] in Hs. revert Hs.
  destruct (wview segs m0 a) eqn:E; intros Hs; cbv beta iota in Hs; [|discriminate Hs].
  split.
  - apply (keep_of_wview_cj m m0 a HR). rewrite E. discriminate.
  - exact (IH _ HR Hs).
Qed.

Lemma write_keep : forall bs m m0 a, (forall x, m0 x = normalize_cj m x) -> all_keep a (length bs) ->
  forall x, write_to_mem m0 a bs x = normalize_cj (write_to_mem m a bs) x.
Proof.
  induction bs as [|b bs IH]; intros m m0 a H Hw x; [apply H|].
  destruct Hw as [Ha Hw]. cbn [write_to_mem]. apply IH; [|exact Hw].
  intros y. unfold normalize_cj. cbv beta. destruct (bv_eqb y a) eqn:E.
  - unfold bv_eqb in E. apply Z.eqb_eq in E. assert (y = a) as -> by (apply bv_eq; exact E).
    rewrite Ha. reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma write_cj_same : forall bs m a x, all_keep a (length bs) -> cj_drop x = true -> write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hw Hx; [reflexivity|].
  destruct Hw as [Ha Hw]. cbn [write_to_mem]. rewrite (IH _ _ x Hw Hx). cbv beta.
  destruct (bv_eqb x a) eqn:E; [|reflexivity].
  unfold bv_eqb in E. apply Z.eqb_eq in E. assert (x = a) as -> by (apply bv_eq; exact E).
  congruence.
Qed.

Lemma interp_rel_cj : forall t m m0 r0, mem_rel_cj m m0 ->
  interp_eff_accesses segs t m0 = MachineOk r0 ->
  exists r, interp_eff_accesses segs t m = MachineOk r /\
    fst (@access_value _ r) = fst (@access_value _ r0) /\
    mem_rel_cj (snd (@access_value _ r)) (snd (@access_value _ r0)) /\
    cj_same m (snd (@access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m m0 r0 HR H;
    cbn [interp_eff_accesses] in H |- *; try discriminate H.
  - injection H as <-. eexists. split; [reflexivity|]. cbn [access_value fst snd].
    split; [reflexivity|]. split; [exact HR|]. intros x _. reflexivity.
  - revert H. destruct (ov_read_bytes segs m0 a (width_bytes n)) as [bs|] eqn:Eo; intros H;
      cbn beta iota in H; [|discriminate H].
    rewrite (ov_read_rel_cj m m0 a _ bs HR Eo). cbn beta iota.
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses segs ?t m0] => destruct (interp_eff_accesses segs t m0) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ m m0 r1 HR E1) as (r & Er & Ef & Erel & Ero). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value].
    split; [exact Ef|]. split; [exact Erel|]. exact Ero.
  - revert H. destruct (store_ok segs m0 a (width_bytes n)) eqn:Es; intros H; cbn beta iota in H;
      [|discriminate H].
    rewrite (store_ok_rel_cj m m0 _ a HR Es). cbn beta iota.
    pose proof (store_ok_all_keep m m0 _ a HR Es) as Hw.
    rewrite <- (length_Z_to_le_bytes (width_bytes n) (bv_unsigned v)) in Hw.
    assert (HR' : mem_rel_cj (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
                             (write_to_mem m0 a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    { split.
      - exact (write_keep _ m m0 a (proj1 HR) Hw).
      - intros x b Hx Hb. unfold mrd. rewrite (write_cj_same _ m a x Hw Hx). exact (proj2 HR x b Hx Hb). }
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses segs k (write_to_mem m0 ?x ?y)] =>
        destruct (interp_eff_accesses segs k (write_to_mem m0 x y)) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ _ r1 HR' E1) as (r & Er & Ef & Erel & Ero). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value].
    split; [exact Ef|]. split; [exact Erel|].
    intros x Hx. rewrite (Ero x Hx). exact (write_cj_same _ m a x Hw Hx).
Qed.

Lemma decode_rel_cj : forall s s0 w s0', ms_rel_cj s s0 ->
  drop_access_report (decode_exec_accesses segs s0 w) = MachineOk s0' ->
  exists s', drop_access_report (decode_exec_accesses segs s w) = MachineOk s' /\
    ms_rel_cj s' s0' /\ cj_same (ms_mem s) (ms_mem s').
Proof.
  intros [R F pc svc rv fc m ro] [R0 F0 pc0 svc0 rv0 fc0 m0 ro0] w s0' Hrel.
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in *.
  subst R0 F0 pc0 svc0 rv0 fc0 ro0.
  unfold decode_exec_accesses, ms_reg.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem].
  destruct (is_ecall w).
  - intros H. cbn [drop_access_report access_value] in H. injection H as <-.
    eexists. split; [reflexivity|]. split.
    + refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
      exact HR.
    + intros a _. reflexivity.
  - destruct (decode_any w) as [[i isz]|].
    + lazymatch goal with
      | |- context [interp_eff_accesses segs ?t m0] =>
          destruct (interp_eff_accesses segs t m0) as [r0| |] eqn:E
      end; intros H; cbn [drop_access_report] in H; try discriminate H.
      destruct (interp_rel_cj _ m m0 r0 HR E) as (r & Er & Ef & Erel & Ero). rewrite Er.
      destruct r0 as [[c0 m0'] acc0], r as [[c m'] acc].
      cbn [drop_access_report access_value fst snd] in *. subst c0. injection H as <-.
      eexists. split; [reflexivity|]. split; [|exact Ero].
      refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
      exact Erel.
    + destruct (is_defined_illegal w); intros H; cbn [drop_access_report] in H; discriminate H.
Qed.

Lemma cj_keep_of_wx : wx_apart segs = true -> forall s x, In s segs ->
  andb (seg_executable s) (seg_writable s) = true ->
  (Z.of_N (seg_base s) <= bv_unsigned x < Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z ->
  cj_drop x = false.
Proof.
  intros Hwx s x Hin Hxw Hx. apply cj_drop_false_intro.
  - exact (ro_addr_false_of_wx segs Hwx s x Hin Hxw Hx).
  - left. apply (find_segment_some segs s); [exact Hin | lia | lia].
Qed.

Lemma code_read_ov_rel_cj : forall m m0, wx_apart segs = true -> mem_rel_cj m m0 ->
  forall addr n, code_read_ov segs m addr n = code_read_ov segs m0 addr n.
Proof.
  intros m m0 Hwx HR addr n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned addr) (Z.of_N n)) as [s|] eqn:Hf; cbv beta iota; [|reflexivity].
  destruct (andb (seg_executable s) (seg_writable s)) eqn:Hxw; cbv beta iota; [|reflexivity].
  apply seg_ov_read_ext. intros i Hi.
  pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [H1 H2].
  pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin.
  pose proof (u64_range addr) as Ha.
  assert (Hi' : (Z.of_nat i < Z.of_N n)%Z) by (pose proof (N_nat_Z n); lia).
  destruct (wx_apart_sound segs Hwx s Hin Hxw) as [Htop _].
  symmetry. apply (mem_rel_cj_keep m m0 _ HR).
  apply (cj_keep_of_wx Hwx s); [exact Hin | exact Hxw |].
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma fetch_word_ov_rel_cj : forall m m0, wx_apart segs = true -> mem_rel_cj m m0 ->
  forall pc, fetch_word_ov segs m pc = fetch_word_ov segs m0 pc.
Proof. intros m m0 Hwx HR pc. unfold fetch_word_ov. rewrite (code_read_ov_rel_cj m m0 Hwx HR). reflexivity. Qed.

Lemma fetch_half_any_rel_cj : forall m m0, wx_apart segs = true -> mem_rel_cj m m0 ->
  forall pc, fetch_half_any segs m pc = fetch_half_any segs m0 pc.
Proof.
  intros m m0 Hwx HR pc. unfold fetch_half_any, fetch_half_ov.
  rewrite (code_read_ov_rel_cj m m0 Hwx HR). reflexivity.
Qed.

Lemma fetch_tail_any_rel_cj : forall m m0, wx_apart segs = true -> mem_rel_cj m m0 ->
  forall pc, fetch_tail_any segs m pc = fetch_tail_any segs m0 pc.
Proof.
  intros m m0 Hwx HR pc. unfold fetch_tail_any.
  rewrite !(fetch_half_any_rel_cj m m0 Hwx HR). reflexivity.
Qed.

Lemma step_rel_cj : forall s s0 s0', wx_apart segs = true -> ms_rel_cj s s0 ->
  RiscvSemantics.step segs s0 = MachineOk s0' ->
  exists s', RiscvSemantics.step segs s = MachineOk s' /\ ms_rel_cj s' s0' /\ cj_same (ms_mem s) (ms_mem s').
Proof.
  intros s s0 s0' Hwx Hrel H. pose proof Hrel as (_ & _ & Ep & _ & _ & _ & _ & HR).
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses, ms_pc in H |- *.
  rewrite Ep, (fetch_word_ov_rel_cj _ _ Hwx HR), (fetch_tail_any_rel_cj _ _ Hwx HR).
  revert H.
  destruct (fetch_word segs (ms_pc_val s0)) as [w|]; [intros H; exact (decode_rel_cj s s0 w s0' Hrel H)|].
  destruct (fetch_word_ov segs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (decode_rel_cj s s0 w s0' Hrel H)|].
  destruct (fetch_tail_any segs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (decode_rel_cj s s0 w s0' Hrel H)|].
  destruct (fetch_failure segs (ms_mem s0) (ms_pc_val s0)) as [st| |] eqn:Ef.
  - exfalso. exact (fetch_failure_not_ok segs _ _ _ Ef).
  - intros H. cbn [drop_access_report] in H. discriminate H.
  - intros H. cbn [drop_access_report] in H. discriminate H.
Qed.

Lemma msteps_rel_cj : wx_apart segs = true -> forall s0 s0', msteps segs s0 s0' ->
  forall s, ms_rel_cj s s0 -> exists s', msteps segs s s' /\ ms_rel_cj s' s0' /\ cj_same (ms_mem s) (ms_mem s').
Proof.
  intros Hwx s0 s0' H. induction H as [x|x y z [Hsvc Hst] HT IH]; intros s Hrel.
  - exists s. split; [apply msteps_refl|]. split; [exact Hrel|]. intros a _. reflexivity.
  - destruct (step_rel_cj s x y Hwx Hrel Hst) as (t & Et & Rt & Ot).
    destruct (IH t Rt) as (s' & Es' & Rs' & Os').
    exists s'. split; [|split; [exact Rs'|]].
    + apply (msteps_cons segs s t s'); [|exact Es']. split; [|exact Et].
      destruct Hrel as (_ & _ & _ & Esvc & _). rewrite Esvc. exact Hsvc.
    + intros a Ha. rewrite (Os' a Ha). exact (Ot a Ha).
Qed.

Theorem evt_rel_cj : forall (Q : machine_state -> Prop) s s0, wx_apart segs = true -> ms_rel_cj s s0 ->
  evt segs Q s0 ->
  evt segs (fun s' => exists s0', Q s0' /\ ms_rel_cj s' s0' /\ cj_same (ms_mem s) (ms_mem s')) s.
Proof.
  intros Q s s0 Hwx Hrel (s0' & Hs & HQ).
  destruct (msteps_rel_cj Hwx s0 s0' Hs s Hrel) as (s' & Hs' & Hr & Ho).
  exists s'. split; [exact Hs'|]. exists s0'. split; [exact HQ|]. split; [exact Hr | exact Ho].
Qed.

Theorem evt_rel_MS_cj : forall (Q : machine_state -> Prop) R F pc fc rv m m0 ro,
  wx_apart segs = true -> mem_rel_cj m m0 ->
  evt segs Q (MS R F pc fc rv m0 ro) ->
  evt segs (fun s => exists s0, Q s0 /\ ms_rel_cj s s0 /\ cj_same m (ms_mem s)) (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m m0 ro Hwx HR H.
  exact (evt_rel_cj Q (MS R F pc fc rv m ro) (MS R F pc fc rv m0 ro) Hwx
    (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl HR))))))) H).
Qed.

Theorem evt_normalize_cj : forall (Q : machine_state -> Prop) R F pc fc rv m ro,
  wx_apart segs = true -> ro_agree segs m ->
  evt segs Q (MS R F pc fc rv (normalize_cj m) ro) ->
  evt segs (fun s => exists s0, Q s0 /\ ms_rel_cj s s0 /\ cj_same m (ms_mem s)) (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m ro Hwx Hro H.
  exact (evt_rel_MS_cj Q R F pc fc rv m (normalize_cj m) ro Hwx (mem_rel_cj_normalize m Hro) H).
Qed.

Lemma bytes_at_rel_cj : forall m m0 a bs, mem_rel_cj m m0 -> bytes_at segs m0 a bs -> bytes_at segs m a bs.
Proof.
  intros m m0 a bs HR (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E.
  - apply (mrd_rel_cj m m0 _ b HR). rewrite (H3 i Hi). exact E.
  - apply nth_error_None in E. lia.
Qed.

Lemma mrd_normalize_cj : forall m x, ro_agree segs m ->
  m x = None \/ find_segment segs (bv_unsigned x) 1 <> None \/ (bv_unsigned x < TASK_SIZE)%Z ->
  mrd segs (normalize_cj m) x = mrd segs m x.
Proof.
  intros m x Hro Hx. unfold mrd at 1. unfold normalize_cj.
  destruct (cj_drop x) eqn:E; [|reflexivity].
  destruct (cj_drop_true x E) as [Er | [Ef Et]].
  - rewrite (Hro x Er). reflexivity.
  - destruct Hx as [Hn | [Hf | Hl]].
    + unfold mrd. rewrite Hn. reflexivity.
    + exfalso. exact (Hf Ef).
    + exfalso. lia.
Qed.

Lemma bytes_at_normalize_cj : forall m a bs, ro_agree segs m -> task_mem segs m ->
  bytes_at segs m a bs -> bytes_at segs (normalize_cj m) a bs.
Proof.
  intros m a bs Hro Ht (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite mrd_normalize_cj; [exact (H3 i Hi) | exact Hro |].
  destruct (m (wa (a + Z.of_nat i))) as [b|] eqn:E; [right; exact (Ht _ b E) | left; reflexivity].
Qed.

Lemma bytes_at_normalize_cj_low : forall m a bs, ro_agree segs m ->
  (a + Z.of_nat (length bs) <= TASK_SIZE)%Z ->
  bytes_at segs m a bs -> bytes_at segs (normalize_cj m) a bs.
Proof.
  intros m a bs Hro Hl (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite mrd_normalize_cj; [exact (H3 i Hi) | exact Hro |].
  right. right. rewrite wa_unsigned by lia. lia.
Qed.

Lemma wr_at_rel_cj : forall m m0 a n, mem_rel_cj m m0 -> wr_at segs m0 a n -> wr_at segs m a n.
Proof.
  intros m m0 a n HR (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  pose proof (H3 i Hi) as W.
  rewrite <- (wview_rel_cj m m0 _ HR (keep_of_wview_cj m m0 _ HR W)). exact W.
Qed.

Lemma wr_at_norm_cj : forall m m0 a n, mem_rel_cj m m0 -> wr_at segs m a n ->
  (forall i, (0 <= i < n)%Z -> cj_drop (wa (a + i)) = false) -> wr_at segs m0 a n.
Proof.
  intros m m0 a n HR (H1 & H2 & H3) Hk. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite (wview_rel_cj m m0 _ HR (Hk i Hi)). exact (H3 i Hi).
Qed.

Lemma munch_rel_cj : forall W m m0 m' m0', mem_rel_cj m m0 -> mem_rel_cj m' m0' -> cj_same m m' ->
  munch W m0 m0' -> munch W m m'.
Proof.
  intros W m m0 m' m0' HR HR' Ho H x Hx. destruct (cj_drop x) eqn:E.
  - exact (Ho x E).
  - rewrite <- (mem_rel_cj_keep m' m0' x HR' E), <- (mem_rel_cj_keep m m0 x HR E). exact (H x Hx).
Qed.

Lemma wmono_rel_cj : forall m m0 m' m0', mem_rel_cj m m0 -> mem_rel_cj m' m0' -> cj_same m m' ->
  wmono segs m0 m0' -> wmono segs m m'.
Proof.
  intros m m0 m' m0' HR HR' Ho H x Hx. destruct (cj_drop x) eqn:E.
  - unfold wview in Hx |- *. rewrite (Ho x E). exact Hx.
  - rewrite <- (wview_rel_cj m' m0' x HR' E). apply H.
    rewrite (wview_rel_cj m m0 x HR E). exact Hx.
Qed.

Lemma mem_unchanged_rel_cj : forall m m0 m' m0', mem_rel_cj m m0 -> mem_rel_cj m' m0' -> cj_same m m' ->
  (forall x, m0' x = m0 x) -> forall x, m' x = m x.
Proof.
  intros m m0 m' m0' HR HR' Ho H x.
  exact (munch_rel_cj nil m m0 m' m0' HR HR' Ho (fun y _ => H y) x I).
Qed.

Lemma ro_agree_same_cj : forall m m', ro_agree segs m -> cj_same m m' -> ro_agree segs m'.
Proof. intros m m' H Ho a E. unfold mrd. rewrite (Ho a (cj_drop_ro a E)). exact (H a E). Qed.

Lemma task_mem_same_cj : forall m m', task_mem segs m -> cj_same m m' -> task_mem segs m'.
Proof.
  intros m m' H Ho a b E. destruct (cj_drop a) eqn:D.
  - rewrite (Ho a D) in E. exact (H a b E).
  - exact (proj2 (cj_drop_false a D)).
Qed.

Lemma mbyte_rel_cj : forall m m0 a b, mem_rel_cj m m0 ->
  YP09.mbyte segs m0 a = Some b -> YP09.mbyte segs m a = Some b.
Proof. intros m m0 a b HR H. unfold YP09.mbyte in *. exact (mrd_rel_cj m m0 (Z_to_bv 64 a) b HR H). Qed.

Lemma writable_at_rel_cj : forall m m0 a, mem_rel_cj m m0 -> YP09.writable_at segs m0 a -> YP09.writable_at segs m a.
Proof.
  intros m m0 a HR H. unfold YP09.writable_at in *.
  rewrite <- (wview_rel_cj m m0 _ HR (keep_of_wview_cj m m0 _ HR H)). exact H.
Qed.

End WithSegsCJ.

Theorem evt_rodata_cj : forall (B : YO0d.malloc_syms) (Q : machine_state -> Prop) R F pc fc rv m ro,
  wx_apart (YO0d.ms_segs B) = true ->
  YL0g.rodata_ok B m ->
  (forall a, YO0d.static_owned B a -> (0 <= a < 2 ^ 64)%Z ->
     ro_addr (YO0d.ms_segs B) (Z_to_bv 64 a) = true ->
     YP09.mbyte (YO0d.ms_segs B) m a = seg_rom (YO0d.ms_segs B) (Z_to_bv 64 a)) ->
  evt (YO0d.ms_segs B) Q (MS R F pc fc rv (normalize_cj (YO0d.ms_segs B) m) ro) ->
  evt (YO0d.ms_segs B)
    (fun s => exists s0, Q s0 /\ ms_rel_cj (YO0d.ms_segs B) s s0 /\ cj_same (YO0d.ms_segs B) m (ms_mem s))
    (MS R F pc fc rv m ro).
Proof.
  intros B Q R F pc fc rv m ro Hwx Hro Hst H.
  exact (evt_normalize_cj _ Q R F pc fc rv m ro Hwx (ro_agree_of_rodata_ok B m Hro Hst) H).
Qed.
