From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify Require Import Proofs.libreac.fuzz_ctrl.lib.MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK1j YP09.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* Footprint of a run from a memory restriction.  normalize_P m keeps a byte only when normalize_cj keeps it AND
   it lies in a loaded segment or satisfies P.  A load reads the overlay or a readable segment; a store needs the
   overlay or a writable segment (RiscvSemantics.ov_read_bytes, store_ok).  So a step that succeeds on
   normalize_P m accesses only bytes that satisfy P or lie in a segment, and the same step on m does the same
   thing with the same reported ranges.  An evt run on normalize_P m therefore gives an ExecF.evtF run on m whose
   footprint is RNG_P. *)

(* rng_bytes and fp_ok_rng_bytes now live in lib/Lib/RngBytes.v (one definition for the whole unit; a `_c.v`
   statement file imports THAT, never this file, which pulls in lib/Reusable). *)

Section WithSegsP.
Variable segs : list Segment.

Definition in_seg (a : word) : bool :=
  match find_segment segs (bv_unsigned a) 1 with Some _ => true | None => false end.

Lemma in_seg_false : forall a, in_seg a = false -> find_segment segs (bv_unsigned a) 1 = None.
Proof. intros a. unfold in_seg. destruct (find_segment segs (bv_unsigned a) 1); [discriminate|reflexivity]. Qed.

Lemma in_seg_true : forall a, find_segment segs (bv_unsigned a) 1 <> None -> in_seg a = true.
Proof. intros a H. unfold in_seg. destruct (find_segment segs (bv_unsigned a) 1); [reflexivity|]. exfalso; apply H; reflexivity. Qed.

Variable P : word -> bool.

Definition keepP (a : word) : bool := negb (cj_drop segs a) && (P a || in_seg a).

Definition normalize_P (m : word -> option byte) : word -> option byte :=
  fun a => if keepP a then m a else None.

Definition mem_rel_P (m m0 : word -> option byte) : Prop :=
  (forall a, m0 a = normalize_P m a) /\
  (forall a b, cj_drop segs a = true -> seg_rom segs a = Some b -> mrd segs m a = Some b).

(* The bytes of m that the restricted run cannot see stay unchanged on the full run. *)
Definition same_P (m m' : word -> option byte) : Prop :=
  forall a, keepP a = false -> m' a = m a.

Definition ms_rel_P (s s0 : machine_state) : Prop :=
  ms_regs s = ms_regs s0 /\ ms_fregs s = ms_fregs s0 /\ ms_pc_val s = ms_pc_val s0 /\
  ms_svc_pending s = ms_svc_pending s0 /\ ms_resv s = ms_resv s0 /\ ms_fcsr s = ms_fcsr s0 /\
  ms_rom s = ms_rom s0 /\ mem_rel_P (ms_mem s) (ms_mem s0).

(* Every byte of an access satisfies P or lies in a loaded segment. *)
Definition RNG_P : ExecF.footprint :=
  fun b j => forall k : nat, (k < j)%nat ->
    P (wa (b + Z.of_nat k)) = true \/ in_seg (wa (b + Z.of_nat k)) = true.

Lemma keepP_cj : forall a, keepP a = true -> cj_drop segs a = false.
Proof. intros a H. unfold keepP in H. apply andb_true_iff in H as [H _]. apply negb_true_iff in H. exact H. Qed.

Lemma keepP_P : forall a, keepP a = true -> P a = true \/ in_seg a = true.
Proof. intros a H. unfold keepP in H. apply andb_true_iff in H as [_ H]. apply orb_true_iff in H. exact H. Qed.

Lemma keepP_intro : forall a, cj_drop segs a = false -> P a = true \/ in_seg a = true -> keepP a = true.
Proof. intros a H1 H2. unfold keepP. rewrite H1. cbn [negb andb]. apply orb_true_iff. exact H2. Qed.

Lemma keepP_noseg : forall a, keepP a = false -> cj_drop segs a = false -> in_seg a = false.
Proof.
  intros a H E. unfold keepP in H. rewrite E in H. cbn [negb andb] in H.
  apply orb_false_iff in H as [_ H]. exact H.
Qed.

Lemma mem_rel_P_keep : forall m m0 a, mem_rel_P m m0 -> keepP a = true -> m0 a = m a.
Proof. intros m m0 a [H _] E. rewrite H. unfold normalize_P. rewrite E. reflexivity. Qed.

Lemma mem_rel_P_drop : forall m m0 a, mem_rel_P m m0 -> keepP a = false -> m0 a = None.
Proof. intros m m0 a [H _] E. rewrite H. unfold normalize_P. rewrite E. reflexivity. Qed.

Lemma mem_rel_P_normalize : forall m, ro_agree segs m -> mem_rel_P m (normalize_P m).
Proof.
  intros m H. split; [intros a; reflexivity|].
  intros a b E Hb. destruct (cj_drop_true segs a E) as [Er | [Ef _]].
  - rewrite (H a Er). exact Hb.
  - rewrite (seg_rom_unmapped segs a Ef) in Hb. discriminate Hb.
Qed.

(* A byte that the restricted memory serves (overlay or segment) satisfies P or lies in a segment. *)
Lemma mrd_P_present : forall m m0 a b, mem_rel_P m m0 -> mrd segs m0 a = Some b ->
  P a = true \/ in_seg a = true.
Proof.
  intros m m0 a b HR H. destruct (keepP a) eqn:K; [exact (keepP_P a K)|].
  right. unfold mrd in H. rewrite (mem_rel_P_drop m m0 a HR K) in H. cbv beta iota in H.
  destruct (in_seg a) eqn:S; [reflexivity|].
  rewrite (seg_rom_unmapped segs a (in_seg_false a S)) in H. discriminate H.
Qed.

Lemma mrd_rel_P : forall m m0 a b, mem_rel_P m m0 -> mrd segs m0 a = Some b -> mrd segs m a = Some b.
Proof.
  intros m m0 a b HR H. destruct (keepP a) eqn:K.
  - unfold mrd in H |- *. rewrite (mem_rel_P_keep m m0 a HR K) in H. exact H.
  - unfold mrd in H. rewrite (mem_rel_P_drop m m0 a HR K) in H. cbv beta iota in H.
    destruct (cj_drop segs a) eqn:E; [exact (proj2 HR a b E H)|].
    rewrite (seg_rom_unmapped segs a (in_seg_false a (keepP_noseg a K E))) in H. discriminate H.
Qed.

Lemma rdn_rel_P : forall m m0 n a bs, mem_rel_P m m0 -> rdn segs m0 a n = Some bs -> rdn segs m a n = Some bs.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a bs HR H; [exact H|].
  rewrite rdn_S in H |- *. revert H.
  destruct (mrd segs m0 a) as [b|] eqn:E1; intros H; cbv beta iota in H; [|discriminate H].
  rewrite (mrd_rel_P m m0 a b HR E1). revert H.
  destruct (rdn segs m0 (a + 1) n) as [r|] eqn:E2; intros H; cbv beta iota in H; [|discriminate H].
  rewrite (IH (a + 1) r HR E2). exact H.
Qed.

Lemma wa_unsigned_0 : forall a : word, wa (bv_unsigned a + Z.of_nat 0) = a.
Proof. intros a. unfold wa. change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma rdn_RNG_P : forall m m0 n a bs, mem_rel_P m m0 -> rdn segs m0 a n = Some bs -> RNG_P (bv_unsigned a) n.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a bs HR H k Hk; [lia|].
  rewrite rdn_S in H. revert H.
  destruct (mrd segs m0 a) as [b|] eqn:E1; intros H; cbv beta iota in H; [|discriminate H].
  revert H. destruct (rdn segs m0 (a + 1) n) as [r|] eqn:E2; intros H; cbv beta iota in H; [|discriminate H].
  destruct k as [|k].
  - rewrite wa_unsigned_0. exact (mrd_P_present m m0 a b HR E1).
  - rewrite <- wa_shift. exact (IH (a + 1) r HR E2 k ltac:(lia)).
Qed.

Lemma ov_read_rel_P : forall m m0 a n bs, mem_rel_P m m0 ->
  ov_read_bytes segs m0 a n = Some bs -> ov_read_bytes segs m a n = Some bs.
Proof. intros m m0 a n bs HR H. rewrite ov_rdn in H |- *. exact (rdn_rel_P m m0 n a bs HR H). Qed.

Lemma ov_read_RNG_P : forall m m0 a n bs, mem_rel_P m m0 ->
  ov_read_bytes segs m0 a n = Some bs -> RNG_P (bv_unsigned a) n.
Proof. intros m m0 a n bs HR H. rewrite ov_rdn in H. exact (rdn_RNG_P m m0 n a bs HR H). Qed.

Lemma wview_P_drop : forall m a, keepP a = false -> m a = None -> wview segs m a = None.
Proof.
  intros m a K Hm. destruct (cj_drop segs a) eqn:E; [exact (wview_cj_drop segs m a E Hm)|].
  unfold wview. rewrite Hm. rewrite (in_seg_false a (keepP_noseg a K E)). reflexivity.
Qed.

Lemma keep_of_wview_P : forall m m0 a, mem_rel_P m m0 -> wview segs m0 a <> None -> keepP a = true.
Proof.
  intros m m0 a HR Hw. destruct (keepP a) eqn:K; [reflexivity|].
  exfalso. apply Hw. exact (wview_P_drop m0 a K (mem_rel_P_drop m m0 a HR K)).
Qed.

Lemma wview_rel_P : forall m m0 a, mem_rel_P m m0 -> keepP a = true -> wview segs m0 a = wview segs m a.
Proof. intros m m0 a HR E. unfold wview. rewrite (mem_rel_P_keep m m0 a HR E). reflexivity. Qed.

Lemma store_ok_rel_P : forall m m0 n a, mem_rel_P m m0 -> store_ok segs m0 a n = true -> store_ok segs m a n = true.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR Hs; [reflexivity|].
  cbn [store_ok] in Hs |- *. revert Hs.
  destruct (wview segs m0 a) eqn:E; intros Hs; cbv beta iota in Hs; [|discriminate Hs].
  rewrite <- (wview_rel_P m m0 a HR (keep_of_wview_P m m0 a HR ltac:(rewrite E; discriminate))).
  rewrite E. exact (IH _ HR Hs).
Qed.

Fixpoint all_keepP (a : word) (n : nat) : Prop :=
  match n with
  | O => True
  | S n' => keepP a = true /\ all_keepP (a + 1) n'
  end.

Lemma store_ok_all_keepP : forall m m0 n a, mem_rel_P m m0 -> store_ok segs m0 a n = true -> all_keepP a n.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR Hs; [exact I|].
  cbn [store_ok] in Hs. revert Hs.
  destruct (wview segs m0 a) eqn:E; intros Hs; cbv beta iota in Hs; [|discriminate Hs].
  split.
  - apply (keep_of_wview_P m m0 a HR). rewrite E. discriminate.
  - exact (IH _ HR Hs).
Qed.

Lemma all_keepP_RNG_P : forall n a, all_keepP a n -> RNG_P (bv_unsigned a) n.
Proof.
  induction n as [|n IH]; intros a H k Hk; [lia|].
  destruct H as [Ha H]. destruct k as [|k].
  - rewrite wa_unsigned_0. exact (keepP_P a Ha).
  - rewrite <- wa_shift. exact (IH (a + 1) H k ltac:(lia)).
Qed.

Lemma write_keepP : forall bs m m0 a, (forall x, m0 x = normalize_P m x) -> all_keepP a (length bs) ->
  forall x, write_to_mem m0 a bs x = normalize_P (write_to_mem m a bs) x.
Proof.
  induction bs as [|b bs IH]; intros m m0 a H Hw x; [apply H|].
  destruct Hw as [Ha Hw]. cbn [write_to_mem]. apply IH; [|exact Hw].
  intros y. unfold normalize_P. cbv beta. destruct (bv_eqb y a) eqn:E.
  - unfold bv_eqb in E. apply Z.eqb_eq in E. assert (y = a) as -> by (apply bv_eq; exact E).
    rewrite Ha. reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma write_P_same : forall bs m a x, all_keepP a (length bs) -> keepP x = false -> write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hw Hx; [reflexivity|].
  destruct Hw as [Ha Hw]. cbn [write_to_mem]. rewrite (IH _ _ x Hw Hx). cbv beta.
  destruct (bv_eqb x a) eqn:E; [|reflexivity].
  unfold bv_eqb in E. apply Z.eqb_eq in E. assert (x = a) as -> by (apply bv_eq; exact E).
  congruence.
Qed.

Lemma write_P_cj : forall bs m a x, all_keepP a (length bs) -> cj_drop segs x = true -> write_to_mem m a bs x = m x.
Proof.
  intros bs m a x Hw Hx. apply (write_P_same bs m a x Hw).
  destruct (keepP x) eqn:K; [|reflexivity]. rewrite (keepP_cj x K) in Hx. discriminate Hx.
Qed.

Lemma interp_rel_P : forall t m m0 r0, mem_rel_P m m0 ->
  interp_eff_accesses segs t m0 = MachineOk r0 ->
  exists r, interp_eff_accesses segs t m = MachineOk r /\
    fst (@access_value _ r) = fst (@access_value _ r0) /\
    mem_rel_P (snd (@access_value _ r)) (snd (@access_value _ r0)) /\
    same_P m (snd (@access_value _ r)) /\
    @accessed_ranges _ r = @accessed_ranges _ r0 /\
    Forall (ExecF.acc_in RNG_P) (@accessed_ranges _ r0).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m m0 r0 HR H;
    cbn [interp_eff_accesses] in H |- *; try discriminate H.
  - injection H as <-. eexists. split; [reflexivity|]. cbn [access_value accessed_ranges fst snd].
    split; [reflexivity|]. split; [exact HR|]. split; [intros x _; reflexivity|]. split; [reflexivity|].
    constructor.
  - revert H. destruct (ov_read_bytes segs m0 a (width_bytes n)) as [bs|] eqn:Eo; intros H;
      cbn beta iota in H; [|discriminate H].
    rewrite (ov_read_rel_P m m0 a _ bs HR Eo). cbn beta iota.
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses segs ?t m0] => destruct (interp_eff_accesses segs t m0) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ m m0 r1 HR E1) as (r & Er & Ef & Erel & Ero & Eacc & Fa). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value accessed_ranges].
    split; [exact Ef|]. split; [exact Erel|]. split; [exact Ero|]. split; [rewrite Eacc; reflexivity|].
    constructor; [|exact Fa]. unfold ExecF.acc_in. cbn [fst snd]. exact (ov_read_RNG_P m m0 a _ bs HR Eo).
  - revert H. destruct (store_ok segs m0 a (width_bytes n)) eqn:Es; intros H; cbn beta iota in H;
      [|discriminate H].
    rewrite (store_ok_rel_P m m0 _ a HR Es). cbn beta iota.
    pose proof (store_ok_all_keepP m m0 _ a HR Es) as Hw0.
    pose proof Hw0 as Hw. rewrite <- (length_Z_to_le_bytes (width_bytes n) (bv_unsigned v)) in Hw.
    assert (HR' : mem_rel_P (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
                            (write_to_mem m0 a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    { split.
      - exact (write_keepP _ m m0 a (proj1 HR) Hw).
      - intros x b Hx Hb. unfold mrd. rewrite (write_P_cj _ m a x Hw Hx). exact (proj2 HR x b Hx Hb). }
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses segs k (write_to_mem m0 ?x ?y)] =>
        destruct (interp_eff_accesses segs k (write_to_mem m0 x y)) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ _ r1 HR' E1) as (r & Er & Ef & Erel & Ero & Eacc & Fa). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value accessed_ranges].
    split; [exact Ef|]. split; [exact Erel|].
    split; [intros x Hx; rewrite (Ero x Hx); exact (write_P_same _ m a x Hw Hx)|].
    split; [rewrite Eacc; reflexivity|].
    constructor; [|exact Fa]. unfold ExecF.acc_in. cbn [fst snd]. exact (all_keepP_RNG_P _ a Hw0).
Qed.

Lemma decode_rel_P : forall s s0 w s0' accs, ms_rel_P s s0 ->
  decode_exec_accesses segs s0 w = MachineOk (@mkAccessReport machine_state s0' accs) ->
  exists s', decode_exec_accesses segs s w = MachineOk (@mkAccessReport machine_state s' accs) /\
    ms_rel_P s' s0' /\ same_P (ms_mem s) (ms_mem s') /\ Forall (ExecF.acc_in RNG_P) accs.
Proof.
  intros [R F pc svc rv fc m ro] [R0 F0 pc0 svc0 rv0 fc0 m0 ro0] w s0' accs Hrel.
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in *.
  subst R0 F0 pc0 svc0 rv0 fc0 ro0.
  unfold decode_exec_accesses, ms_reg.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem].
  destruct (is_ecall w).
  - intros H. injection H as <- <-.
    eexists. split; [reflexivity|]. split; [|split; [intros a _; reflexivity | constructor]].
    refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
    exact HR.
  - destruct (decode_any w) as [[i isz]|].
    + lazymatch goal with
      | |- context [interp_eff_accesses segs ?t m0] =>
          destruct (interp_eff_accesses segs t m0) as [r0| |] eqn:E
      end; intros H; try discriminate H.
      destruct (interp_rel_P _ m m0 r0 HR E) as (r & Er & Ef & Erel & Ero & Eacc & Fa). rewrite Er.
      destruct r0 as [[c0 m0'] acc0], r as [[c m'] acc].
      cbn [access_value accessed_ranges fst snd] in *. subst c0 acc. injection H as <- <-.
      eexists. split; [reflexivity|]. split; [|split; [exact Ero | exact Fa]].
      refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
      exact Erel.
    + destruct (is_defined_illegal w); intros H; discriminate H.
Qed.

Lemma keepP_of_wx : wx_apart segs = true -> forall s x, In s segs ->
  andb (seg_executable s) (seg_writable s) = true ->
  (Z.of_N (seg_base s) <= bv_unsigned x < Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z ->
  keepP x = true.
Proof.
  intros Hwx s x Hin Hxw Hx. apply keepP_intro; [exact (cj_keep_of_wx segs Hwx s x Hin Hxw Hx)|].
  right. apply in_seg_true. apply (find_segment_some segs s); [exact Hin | lia | lia].
Qed.

Lemma code_read_ov_rel_P : forall m m0, wx_apart segs = true -> mem_rel_P m m0 ->
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
  symmetry. apply (mem_rel_P_keep m m0 _ HR).
  apply (keepP_of_wx Hwx s); [exact Hin | exact Hxw |].
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma fetch_word_ov_rel_P : forall m m0, wx_apart segs = true -> mem_rel_P m m0 ->
  forall pc, fetch_word_ov segs m pc = fetch_word_ov segs m0 pc.
Proof. intros m m0 Hwx HR pc. unfold fetch_word_ov. rewrite (code_read_ov_rel_P m m0 Hwx HR). reflexivity. Qed.

Lemma fetch_half_any_rel_P : forall m m0, wx_apart segs = true -> mem_rel_P m m0 ->
  forall pc, fetch_half_any segs m pc = fetch_half_any segs m0 pc.
Proof.
  intros m m0 Hwx HR pc. unfold fetch_half_any, fetch_half_ov.
  rewrite (code_read_ov_rel_P m m0 Hwx HR). reflexivity.
Qed.

Lemma fetch_tail_any_rel_P : forall m m0, wx_apart segs = true -> mem_rel_P m m0 ->
  forall pc, fetch_tail_any segs m pc = fetch_tail_any segs m0 pc.
Proof.
  intros m m0 Hwx HR pc. unfold fetch_tail_any.
  rewrite !(fetch_half_any_rel_P m m0 Hwx HR). reflexivity.
Qed.

Lemma step_accesses_rel_P : forall s s0 s0' accs, wx_apart segs = true -> ms_rel_P s s0 ->
  RiscvSemantics.step_accesses segs s0 = MachineOk (@mkAccessReport machine_state s0' accs) ->
  exists s', RiscvSemantics.step_accesses segs s = MachineOk (@mkAccessReport machine_state s' accs) /\
    ms_rel_P s' s0' /\ same_P (ms_mem s) (ms_mem s') /\ Forall (ExecF.acc_in RNG_P) accs.
Proof.
  intros s s0 s0' accs Hwx Hrel H. pose proof Hrel as (_ & _ & Ep & _ & _ & _ & _ & HR).
  unfold RiscvSemantics.step_accesses, ms_pc in H |- *.
  rewrite Ep, (fetch_word_ov_rel_P _ _ Hwx HR), (fetch_tail_any_rel_P _ _ Hwx HR).
  revert H.
  destruct (fetch_word segs (ms_pc_val s0)) as [w|]; [intros H; exact (decode_rel_P s s0 w s0' accs Hrel H)|].
  destruct (fetch_word_ov segs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (decode_rel_P s s0 w s0' accs Hrel H)|].
  destruct (fetch_tail_any segs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (decode_rel_P s s0 w s0' accs Hrel H)|].
  destruct (fetch_failure segs (ms_mem s0) (ms_pc_val s0)) as [st| |] eqn:Ef.
  - exfalso. exact (fetch_failure_not_ok segs _ _ _ Ef).
  - intros H. discriminate H.
  - intros H. discriminate H.
Qed.

Lemma step_accesses_of_step : forall s s', RiscvSemantics.step segs s = MachineOk s' ->
  exists accs, RiscvSemantics.step_accesses segs s = MachineOk (@mkAccessReport machine_state s' accs).
Proof.
  intros s s' H. unfold RiscvSemantics.step, drop_access_report in H.
  destruct (RiscvSemantics.step_accesses segs s) as [[x accs]| |]; try discriminate H.
  cbn [access_value] in H. injection H as ->. exists accs. reflexivity.
Qed.

Lemma msteps_rel_P : wx_apart segs = true -> forall s0 s0', msteps segs s0 s0' ->
  forall s, ms_rel_P s s0 ->
  exists s', ExecF.mstepsF segs RNG_P s s' /\ ms_rel_P s' s0' /\ same_P (ms_mem s) (ms_mem s').
Proof.
  intros Hwx s0 s0' H. induction H as [x|x y z [Hsvc Hst] HT IH]; intros s Hrel.
  - exists s. split; [apply ExecF.mstepsF_refl|]. split; [exact Hrel|]. intros a _. reflexivity.
  - destruct (step_accesses_of_step x y Hst) as (accs & Ea).
    destruct (step_accesses_rel_P s x y accs Hwx Hrel Ea) as (t & Et & Rt & Ot & Fa).
    destruct (IH t Rt) as (s' & Es' & Rs' & Os').
    exists s'. split; [|split; [exact Rs'|]].
    + apply (ExecF.mstepsF_cons segs RNG_P s t s'); [|exact Es']. split.
      * destruct Hrel as (_ & _ & _ & Esvc & _). rewrite Esvc. exact Hsvc.
      * exists accs. split; [exact Et | exact Fa].
    + intros a Ha. rewrite (Os' a Ha). exact (Ot a Ha).
Qed.

Theorem evtF_rel_P : forall (Q : machine_state -> Prop) s s0, wx_apart segs = true -> ms_rel_P s s0 ->
  evt segs Q s0 ->
  ExecF.evtF segs RNG_P (fun s' => exists s0', Q s0' /\ ms_rel_P s' s0' /\ same_P (ms_mem s) (ms_mem s')) s.
Proof.
  intros Q s s0 Hwx Hrel (s0' & Hs & HQ).
  destruct (msteps_rel_P Hwx s0 s0' Hs s Hrel) as (s' & Hs' & Hr & Ho).
  exists s'. split; [exact Hs'|]. exists s0'. split; [exact HQ|]. split; [exact Hr | exact Ho].
Qed.

Theorem evtF_normalize_P : forall (Q : machine_state -> Prop) R F pc fc rv m ro,
  wx_apart segs = true -> ro_agree segs m ->
  evt segs Q (MS R F pc fc rv (normalize_P m) ro) ->
  ExecF.evtF segs RNG_P (fun s => exists s0, Q s0 /\ ms_rel_P s s0 /\ same_P m (ms_mem s)) (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m ro Hwx Hro H.
  exact (evtF_rel_P Q (MS R F pc fc rv m ro) (MS R F pc fc rv (normalize_P m) ro) Hwx
    (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
      (mem_rel_P_normalize m Hro)))))))) H).
Qed.

(* Weaken RNG_P to any byte-wise footprint RNG that holds on every P or segment byte.  Byte 0 is in neither, so
   no access in RNG_P wraps past 2^64. *)
Lemma wa_modulus : wa (2^64) = wa 0.
Proof. unfold wa. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. Qed.

Lemma acc_in_RNG_P_weaken : forall RNG, rng_bytes RNG -> P (wa 0) = false -> in_seg (wa 0) = false ->
  (forall x, (0 <= x < 2^64)%Z -> P (wa x) = true \/ in_seg (wa x) = true -> RNG x 1%nat) ->
  forall acc, ExecF.acc_in RNG_P acc -> ExecF.acc_in RNG acc.
Proof.
  intros RNG RB P0 S0 HB [a n] H. unfold ExecF.acc_in in H |- *. cbn [fst snd] in H |- *.
  assert (Ra : (0 <= bv_unsigned a < 2^64)%Z) by apply bv_unsigned_in_range.
  assert (Hend : (bv_unsigned a + Z.of_nat n <= 2^64)%Z).
  { destruct (Z_le_gt_dec (bv_unsigned a + Z.of_nat n) (2^64)) as [L|L]; [exact L|]. exfalso.
    assert (E0 : (bv_unsigned a + Z.of_nat (Z.to_nat (2^64 - bv_unsigned a)) = 2^64)%Z)
      by (rewrite Z2Nat.id; lia).
    assert (K0 : (Z.to_nat (2^64 - bv_unsigned a) < n)%nat) by lia.
    destruct (H _ K0) as [X|X]; rewrite E0, wa_modulus in X; congruence. }
  apply RB; [lia | exact Hend |]. intros k Hk. apply HB; [lia|]. exact (H k Hk).
Qed.

Lemma evtF_RNG_P_weaken : forall RNG, rng_bytes RNG -> P (wa 0) = false -> in_seg (wa 0) = false ->
  (forall x, (0 <= x < 2^64)%Z -> P (wa x) = true \/ in_seg (wa x) = true -> RNG x 1%nat) ->
  forall Q ms, ExecF.evtF segs RNG_P Q ms -> ExecF.evtF segs RNG Q ms.
Proof.
  intros RNG RB P0 S0 HB Q ms (ms' & Hs & HQ). exists ms'. split; [|exact HQ]. clear HQ.
  induction Hs as [x|x y z [Hsvc (accs & E & Fa)] _ IH]; [apply ExecF.mstepsF_refl|].
  apply (ExecF.mstepsF_cons segs RNG x y z); [|exact IH]. split; [exact Hsvc|].
  exists accs. split; [exact E|]. eapply Forall_impl; [|exact Fa].
  exact (acc_in_RNG_P_weaken RNG RB P0 S0 HB).
Qed.

(* The same weakening with the TOP byte excluded instead of byte 0 (two Theorem Labs lanes, 10:19Z): a wrapping
   access would have to admit the byte at 2^64 - 1, so excluding that one is enough.  Use this form when P may
   hold byte 0 (a contract that allows a buffer at address 0, as asan_memset_contract_F does). *)
Lemma acc_in_RNG_P_weaken_top : forall RNG, rng_bytes RNG ->
  P (wa (2^64 - 1)) = false -> in_seg (wa (2^64 - 1)) = false ->
  (forall x, (0 <= x < 2^64)%Z -> P (wa x) = true \/ in_seg (wa x) = true -> RNG x 1%nat) ->
  forall acc, ExecF.acc_in RNG_P acc -> ExecF.acc_in RNG acc.
Proof.
  intros RNG RB P0 S0 HB [a n] H. unfold ExecF.acc_in in H |- *. cbn [fst snd] in H |- *.
  assert (Ra : (0 <= bv_unsigned a < 2^64)%Z) by apply bv_unsigned_in_range.
  assert (Hend : (bv_unsigned a + Z.of_nat n <= 2^64)%Z).
  { destruct (Z_le_gt_dec (bv_unsigned a + Z.of_nat n) (2^64)) as [L|L]; [exact L|]. exfalso.
    assert (E0 : (bv_unsigned a + Z.of_nat (Z.to_nat (2^64 - 1 - bv_unsigned a)) = 2^64 - 1)%Z)
      by (rewrite Z2Nat.id; lia).
    assert (K0 : (Z.to_nat (2^64 - 1 - bv_unsigned a) < n)%nat) by lia.
    destruct (H _ K0) as [X|X]; rewrite E0 in X; congruence. }
  apply RB; [lia | exact Hend |]. intros k Hk. apply HB; [lia|]. exact (H k Hk).
Qed.

Lemma evtF_RNG_P_weaken_top : forall RNG, rng_bytes RNG ->
  P (wa (2^64 - 1)) = false -> in_seg (wa (2^64 - 1)) = false ->
  (forall x, (0 <= x < 2^64)%Z -> P (wa x) = true \/ in_seg (wa x) = true -> RNG x 1%nat) ->
  forall Q ms, ExecF.evtF segs RNG_P Q ms -> ExecF.evtF segs RNG Q ms.
Proof.
  intros RNG RB P0 S0 HB Q ms (ms' & Hs & HQ). exists ms'. split; [|exact HQ]. clear HQ.
  induction Hs as [x|x y z [Hsvc (accs & E & Fa)] _ IH]; [apply ExecF.mstepsF_refl|].
  apply (ExecF.mstepsF_cons segs RNG x y z); [|exact IH]. split; [exact Hsvc|].
  exists accs. split; [exact E|]. eapply Forall_impl; [|exact Fa].
  exact (acc_in_RNG_P_weaken_top RNG RB P0 S0 HB).
Qed.

(* Transfer into the restricted memory: normalize_P agrees with normalize_cj on every byte that satisfies P or
   lies in a segment. *)
Lemma normalize_P_cj : forall m x, P x = true \/ in_seg x = true -> normalize_P m x = normalize_cj segs m x.
Proof.
  intros m x H. unfold normalize_P, normalize_cj. destruct (cj_drop segs x) eqn:E.
  - destruct (keepP x) eqn:K; [rewrite (keepP_cj x K) in E; discriminate E | reflexivity].
  - rewrite (keepP_intro x E H). reflexivity.
Qed.

Lemma mrd_normalize_P_cj : forall m x, P x = true \/ in_seg x = true ->
  mrd segs (normalize_P m) x = mrd segs (normalize_cj segs m) x.
Proof. intros m x H. unfold mrd. rewrite (normalize_P_cj m x H). reflexivity. Qed.

Lemma wview_normalize_P_cj : forall m x, P x = true \/ in_seg x = true ->
  wview segs (normalize_P m) x = wview segs (normalize_cj segs m) x.
Proof. intros m x H. unfold wview. rewrite (normalize_P_cj m x H). reflexivity. Qed.

Lemma bytes_at_P_of_cj : forall m a bs,
  (forall i, (i < length bs)%nat -> P (wa (a + Z.of_nat i)) = true \/ in_seg (wa (a + Z.of_nat i)) = true) ->
  bytes_at segs (normalize_cj segs m) a bs -> bytes_at segs (normalize_P m) a bs.
Proof.
  intros m a bs HP (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite (mrd_normalize_P_cj m _ (HP i Hi)). exact (H3 i Hi).
Qed.

Lemma stk_P_of_cj : forall m lo hi,
  (forall a, (lo <= a < hi)%Z -> P (wa a) = true \/ in_seg (wa a) = true) ->
  stk segs (normalize_cj segs m) lo hi -> stk segs (normalize_P m) lo hi.
Proof.
  intros m lo hi HP (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  rewrite (wview_normalize_P_cj m _ (HP a Ha)), (mrd_normalize_P_cj m _ (HP a Ha)). exact (H3 a Ha).
Qed.

Lemma mem_inv_normalize_P : forall m, mem_inv segs (normalize_cj segs m) -> mem_inv segs (normalize_P m).
Proof.
  intros m H a b E. unfold normalize_P in E. destruct (keepP a) eqn:K; [|discriminate E].
  apply (H a b). unfold normalize_cj. rewrite (keepP_cj a K). exact E.
Qed.

(* Transfer back to the full memory, as MemNorm's _cj lemmas. *)
Lemma bytes_at_rel_P : forall m m0 a bs, mem_rel_P m m0 -> bytes_at segs m0 a bs -> bytes_at segs m a bs.
Proof.
  intros m m0 a bs HR (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E.
  - apply (mrd_rel_P m m0 _ b HR). rewrite (H3 i Hi). exact E.
  - apply nth_error_None in E. lia.
Qed.

Lemma wr_at_rel_P : forall m m0 a n, mem_rel_P m m0 -> wr_at segs m0 a n -> wr_at segs m a n.
Proof.
  intros m m0 a n HR (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  pose proof (H3 i Hi) as W.
  rewrite <- (wview_rel_P m m0 _ HR (keep_of_wview_P m m0 _ HR W)). exact W.
Qed.

Lemma munch_rel_P : forall W m m0 m' m0', mem_rel_P m m0 -> mem_rel_P m' m0' -> same_P m m' ->
  munch W m0 m0' -> munch W m m'.
Proof.
  intros W m m0 m' m0' HR HR' Ho H x Hx. destruct (keepP x) eqn:E.
  - rewrite <- (mem_rel_P_keep m' m0' x HR' E), <- (mem_rel_P_keep m m0 x HR E). exact (H x Hx).
  - exact (Ho x E).
Qed.

Lemma wmono_rel_P : forall m m0 m' m0', mem_rel_P m m0 -> mem_rel_P m' m0' -> same_P m m' ->
  wmono segs m0 m0' -> wmono segs m m'.
Proof.
  intros m m0 m' m0' HR HR' Ho H x Hx. destruct (keepP x) eqn:E.
  - rewrite <- (wview_rel_P m' m0' x HR' E). apply H.
    rewrite (wview_rel_P m m0 x HR E). exact Hx.
  - unfold wview in Hx |- *. rewrite (Ho x E). exact Hx.
Qed.

Lemma mem_unchanged_rel_P : forall m m0 m' m0', mem_rel_P m m0 -> mem_rel_P m' m0' -> same_P m m' ->
  (forall x, m0' x = m0 x) -> forall x, m' x = m x.
Proof.
  intros m m0 m' m0' HR HR' Ho H x.
  exact (munch_rel_P nil m m0 m' m0' HR HR' Ho (fun y _ => H y) x I).
Qed.

Lemma ro_agree_same_P : forall m m', ro_agree segs m -> same_P m m' -> ro_agree segs m'.
Proof.
  intros m m' H Ho a E. unfold mrd. rewrite (Ho a); [exact (H a E)|].
  unfold keepP. rewrite (cj_drop_ro segs a E). reflexivity.
Qed.

Lemma mbyte_rel_P : forall m m0 a b, mem_rel_P m m0 ->
  YP09.mbyte segs m0 a = Some b -> YP09.mbyte segs m a = Some b.
Proof. intros m m0 a b HR H. unfold YP09.mbyte in *. exact (mrd_rel_P m m0 (Z_to_bv 64 a) b HR H). Qed.

Lemma writable_at_rel_P : forall m m0 a, mem_rel_P m m0 -> YP09.writable_at segs m0 a -> YP09.writable_at segs m a.
Proof.
  intros m m0 a HR H. unfold YP09.writable_at in *.
  rewrite <- (wview_rel_P m m0 _ HR (keep_of_wview_P m m0 _ HR H)). exact H.
Qed.

End WithSegsP.
