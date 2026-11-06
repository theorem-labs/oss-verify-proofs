(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeamNormG.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg lib/A/Rt (image-neutral: nothing here names an image): module paths changed; 0 address numerals relocated (port_addr_check 0767e70e074a predict mode: the file holds no address numeral). New file. *)
(* Modified by Theorem Labs, 2026-10: drop set parametrised. *)
(* lib/MemNorm.v's normalization simulation (its section WithSegsCJ, :524-967) with the drop set a
   PARAMETER `drop` instead of MemNorm.cj_drop (:527).  The statements and proofs are MemNorm's with
   cj_drop replaced by `drop`; names carry a g: gdrop_normalize (normalize_cj :534), gmem_rel
   (mem_rel_cj :537), gcj_same (cj_same :541), gms_rel (ms_rel_cj :544), gmsteps_rel, gevt_rel
   (evt_rel_cj :842), ...

   THE ONE HYPOTHESIS on the drop set (gdrop_ok): a dropped address is read-only in the image or lies
   outside every segment.  Equivalently, the drop set keeps every byte of every writable segment, so
   it keeps every byte of a segment the run can write or fetch from a writable segment.  Nothing
   else about the drop set is used: soundness does not depend on which addresses an instance names.
   Where MemNorm's proof used a property of cj_drop, this file uses gdrop_ok:
   - a dropped address with no stored byte has no write view (gwview_drop): MemNorm's
     wview_cj_drop, :628;
   - a dropped address that the image maps gets the image's byte from the read agreement
     (gmem_rel_normalize): MemNorm's mem_rel_cj_normalize, :599;
   - a byte of a writable executable segment is kept (gkeep_of_wx): MemNorm's cj_keep_of_wx, :765.
   The store invariant of the normalized store (MemNorm.mem_inv_cj, :501) needs cj_drop's bytes to be
   dropped too; gmem_inv_cj_normalize takes that as its premise.  The read agreement (MemNorm.ro_agree,
   :41) and W^X apartness (MemNorm.wx_apart, :52) are MemNorm's, unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YK1j.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require MemNorm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module MN := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.MemNorm.

Section WithDrop.
Variable segs : list Segment.
Variable drop : word -> bool.

(* the drop set keeps every byte of every writable segment *)
Hypothesis gdrop_ok : forall a, drop a = true ->
  ro_addr segs a = true \/ find_segment segs (bv_unsigned a) 1 = None.

Definition gdrop_normalize (m : word -> option byte) : word -> option byte :=
  fun a => if drop a then None else m a.

Definition gmem_rel (m m0 : word -> option byte) : Prop :=
  (forall a, m0 a = gdrop_normalize m a) /\
  (forall a b, drop a = true -> seg_rom segs a = Some b -> mrd segs m a = Some b).

Definition gcj_same (m m' : word -> option byte) : Prop :=
  forall a, drop a = true -> m' a = m a.

Definition gms_rel (s s0 : machine_state) : Prop :=
  ms_regs s = ms_regs s0 /\ ms_fregs s = ms_fregs s0 /\ ms_pc_val s = ms_pc_val s0 /\
  ms_svc_pending s = ms_svc_pending s0 /\ ms_resv s = ms_resv s0 /\ ms_fcsr s = ms_fcsr s0 /\
  ms_rom s = ms_rom s0 /\ gmem_rel (ms_mem s) (ms_mem s0).

(* the normalized store satisfies MemNorm's store invariant when cj_drop's bytes are dropped too *)
Lemma gmem_inv_cj_normalize : (forall a, MN.cj_drop segs a = true -> drop a = true) ->
  forall m, MN.mem_inv_cj segs (gdrop_normalize m).
Proof.
  intros Hsub m a b H. unfold gdrop_normalize in H. revert H.
  destruct (drop a) eqn:E; intros H; cbv beta iota in H; [discriminate H|].
  destruct (MN.cj_drop segs a) eqn:Ec; [rewrite (Hsub a Ec) in E; discriminate E|].
  exact (MN.cj_drop_false segs a Ec).
Qed.

Lemma gmem_rel_keep : forall m m0 a, gmem_rel m m0 -> drop a = false -> m0 a = m a.
Proof. intros m m0 a [H _] E. rewrite H. unfold gdrop_normalize. rewrite E. reflexivity. Qed.

Lemma gmem_rel_drop : forall m m0 a, gmem_rel m m0 -> drop a = true -> m0 a = None.
Proof. intros m m0 a [H _] E. rewrite H. unfold gdrop_normalize. rewrite E. reflexivity. Qed.

Lemma gmem_rel_normalize : forall m, MN.ro_agree segs m -> gmem_rel m (gdrop_normalize m).
Proof.
  intros m H. split; [intros a; reflexivity|].
  intros a b E Hb. destruct (gdrop_ok a E) as [Er | Ef].
  - rewrite (H a Er). exact Hb.
  - rewrite (MN.seg_rom_unmapped segs a Ef) in Hb. discriminate Hb.
Qed.

Lemma gmrd_rel : forall m m0 a b, gmem_rel m m0 -> mrd segs m0 a = Some b -> mrd segs m a = Some b.
Proof.
  intros m m0 a b HR H. destruct (drop a) eqn:E.
  - apply (proj2 HR a b E). unfold mrd in H. rewrite (gmem_rel_drop m m0 a HR E) in H. exact H.
  - unfold mrd in H |- *. rewrite (gmem_rel_keep m m0 a HR E) in H. exact H.
Qed.

Lemma grdn_rel : forall m m0 n a bs, gmem_rel m m0 -> rdn segs m0 a n = Some bs -> rdn segs m a n = Some bs.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a bs HR H; [exact H|].
  rewrite MN.rdn_S in H |- *. revert H.
  destruct (mrd segs m0 a) as [b|] eqn:E1; intros H; cbv beta iota in H; [|discriminate H].
  rewrite (gmrd_rel m m0 a b HR E1). revert H.
  destruct (rdn segs m0 (a + 1) n) as [r|] eqn:E2; intros H; cbv beta iota in H; [|discriminate H].
  rewrite (IH (a + 1) r HR E2). exact H.
Qed.

Lemma gov_read_rel : forall m m0 a n bs, gmem_rel m m0 ->
  ov_read_bytes segs m0 a n = Some bs -> ov_read_bytes segs m a n = Some bs.
Proof. intros m m0 a n bs HR H. rewrite ov_rdn in H |- *. exact (grdn_rel m m0 n a bs HR H). Qed.

Lemma gwview_drop : forall m a, drop a = true -> m a = None -> wview segs m a = None.
Proof.
  intros m a E Hm. unfold wview. rewrite Hm.
  destruct (gdrop_ok a E) as [Er | Ef].
  - revert Er. unfold ro_addr.
    destruct (find_segment segs (bv_unsigned a) 1) as [s|]; intros Er; cbv beta iota in Er |- *; [|reflexivity].
    apply negb_true_iff in Er. rewrite Er. reflexivity.
  - rewrite Ef. reflexivity.
Qed.

Lemma gkeep_of_wview : forall m m0 a, gmem_rel m m0 -> wview segs m0 a <> None -> drop a = false.
Proof.
  intros m m0 a HR Hw. destruct (drop a) eqn:E; [|reflexivity].
  exfalso. apply Hw. exact (gwview_drop m0 a E (gmem_rel_drop m m0 a HR E)).
Qed.

Lemma gwview_rel : forall m m0 a, gmem_rel m m0 -> drop a = false -> wview segs m0 a = wview segs m a.
Proof. intros m m0 a HR E. unfold wview. rewrite (gmem_rel_keep m m0 a HR E). reflexivity. Qed.

Lemma gstore_ok_rel : forall m m0 n a, gmem_rel m m0 -> store_ok segs m0 a n = true -> store_ok segs m a n = true.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR Hs; [reflexivity|].
  cbn [store_ok] in Hs |- *. revert Hs.
  destruct (wview segs m0 a) eqn:E; intros Hs; cbv beta iota in Hs; [|discriminate Hs].
  rewrite <- (gwview_rel m m0 a HR (gkeep_of_wview m m0 a HR ltac:(rewrite E; discriminate))).
  rewrite E. exact (IH _ HR Hs).
Qed.

Fixpoint gall_keep (a : word) (n : nat) : Prop :=
  match n with
  | O => True
  | S n' => drop a = false /\ gall_keep (a + 1) n'
  end.

Lemma gstore_ok_all_keep : forall m m0 n a, gmem_rel m m0 -> store_ok segs m0 a n = true -> gall_keep a n.
Proof.
  intros m m0 n. induction n as [|n IH]; intros a HR Hs; [exact I|].
  cbn [store_ok] in Hs. revert Hs.
  destruct (wview segs m0 a) eqn:E; intros Hs; cbv beta iota in Hs; [|discriminate Hs].
  split.
  - apply (gkeep_of_wview m m0 a HR). rewrite E. discriminate.
  - exact (IH _ HR Hs).
Qed.

Lemma gwrite_keep : forall bs m m0 a, (forall x, m0 x = gdrop_normalize m x) -> gall_keep a (length bs) ->
  forall x, write_to_mem m0 a bs x = gdrop_normalize (write_to_mem m a bs) x.
Proof.
  induction bs as [|b bs IH]; intros m m0 a H Hw x; [apply H|].
  destruct Hw as [Ha Hw]. cbn [write_to_mem]. apply IH; [|exact Hw].
  intros y. unfold gdrop_normalize. cbv beta. destruct (bv_eqb y a) eqn:E.
  - unfold bv_eqb in E. apply Z.eqb_eq in E. assert (y = a) as -> by (apply bv_eq; exact E).
    rewrite Ha. reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma gwrite_same : forall bs m a x, gall_keep a (length bs) -> drop x = true -> write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hw Hx; [reflexivity|].
  destruct Hw as [Ha Hw]. cbn [write_to_mem]. rewrite (IH _ _ x Hw Hx). cbv beta.
  destruct (bv_eqb x a) eqn:E; [|reflexivity].
  unfold bv_eqb in E. apply Z.eqb_eq in E. assert (x = a) as -> by (apply bv_eq; exact E).
  congruence.
Qed.

Lemma ginterp_rel : forall t m m0 r0, gmem_rel m m0 ->
  interp_eff_accesses segs t m0 = MachineOk r0 ->
  exists r, interp_eff_accesses segs t m = MachineOk r /\
    fst (@access_value _ r) = fst (@access_value _ r0) /\
    gmem_rel (snd (@access_value _ r)) (snd (@access_value _ r0)) /\
    gcj_same m (snd (@access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m m0 r0 HR H;
    cbn [interp_eff_accesses] in H |- *; try discriminate H.
  - injection H as <-. eexists. split; [reflexivity|]. cbn [access_value fst snd].
    split; [reflexivity|]. split; [exact HR|]. intros x _. reflexivity.
  - revert H. destruct (ov_read_bytes segs m0 a (width_bytes n)) as [bs|] eqn:Eo; intros H;
      cbn beta iota in H; [|discriminate H].
    rewrite (gov_read_rel m m0 a _ bs HR Eo). cbn beta iota.
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses segs ?t m0] => destruct (interp_eff_accesses segs t m0) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ m m0 r1 HR E1) as (r & Er & Ef & Erel & Ero). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value].
    split; [exact Ef|]. split; [exact Erel|]. exact Ero.
  - revert H. destruct (store_ok segs m0 a (width_bytes n)) eqn:Es; intros H; cbn beta iota in H;
      [|discriminate H].
    rewrite (gstore_ok_rel m m0 _ a HR Es). cbn beta iota.
    pose proof (gstore_ok_all_keep m m0 _ a HR Es) as Hw.
    rewrite <- (length_Z_to_le_bytes (width_bytes n) (bv_unsigned v)) in Hw.
    assert (HR' : gmem_rel (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
                           (write_to_mem m0 a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    { split.
      - exact (gwrite_keep _ m m0 a (proj1 HR) Hw).
      - intros x b Hx Hb. unfold mrd. rewrite (gwrite_same _ m a x Hw Hx). exact (proj2 HR x b Hx Hb). }
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses segs k (write_to_mem m0 ?x ?y)] =>
        destruct (interp_eff_accesses segs k (write_to_mem m0 x y)) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ _ r1 HR' E1) as (r & Er & Ef & Erel & Ero). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value].
    split; [exact Ef|]. split; [exact Erel|].
    intros x Hx. rewrite (Ero x Hx). exact (gwrite_same _ m a x Hw Hx).
Qed.

Lemma gdecode_rel : forall s s0 w s0', gms_rel s s0 ->
  drop_access_report (decode_exec_accesses segs s0 w) = MachineOk s0' ->
  exists s', drop_access_report (decode_exec_accesses segs s w) = MachineOk s' /\
    gms_rel s' s0' /\ gcj_same (ms_mem s) (ms_mem s').
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
      destruct (ginterp_rel _ m m0 r0 HR E) as (r & Er & Ef & Erel & Ero). rewrite Er.
      destruct r0 as [[c0 m0'] acc0], r as [[c m'] acc].
      cbn [drop_access_report access_value fst snd] in *. subst c0. injection H as <-.
      eexists. split; [reflexivity|]. split; [|exact Ero].
      refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
      exact Erel.
    + destruct (is_defined_illegal w); intros H; cbn [drop_access_report] in H; discriminate H.
Qed.

Lemma gkeep_of_wx : MN.wx_apart segs = true -> forall s x, In s segs ->
  andb (seg_executable s) (seg_writable s) = true ->
  (Z.of_N (seg_base s) <= bv_unsigned x < Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z ->
  drop x = false.
Proof.
  intros Hwx s x Hin Hxw Hx. destruct (drop x) eqn:E; [|reflexivity].
  destruct (gdrop_ok x E) as [Er | Ef].
  - rewrite (MN.ro_addr_false_of_wx segs Hwx s x Hin Hxw Hx) in Er. discriminate Er.
  - exfalso. exact (MN.find_segment_some segs s (bv_unsigned x) 1 Hin ltac:(lia) ltac:(lia) Ef).
Qed.

Lemma gcode_read_ov_rel : forall m m0, MN.wx_apart segs = true -> gmem_rel m m0 ->
  forall addr n, code_read_ov segs m addr n = code_read_ov segs m0 addr n.
Proof.
  intros m m0 Hwx HR addr n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned addr) (Z.of_N n)) as [s|] eqn:Hf; cbv beta iota; [|reflexivity].
  destruct (andb (seg_executable s) (seg_writable s)) eqn:Hxw; cbv beta iota; [|reflexivity].
  apply MN.seg_ov_read_ext. intros i Hi.
  pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [H1 H2].
  pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin.
  pose proof (u64_range addr) as Ha.
  assert (Hi' : (Z.of_nat i < Z.of_N n)%Z) by (pose proof (N_nat_Z n); lia).
  destruct (MN.wx_apart_sound segs Hwx s Hin Hxw) as [Htop _].
  symmetry. apply (gmem_rel_keep m m0 _ HR).
  apply (gkeep_of_wx Hwx s); [exact Hin | exact Hxw |].
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma gfetch_word_ov_rel : forall m m0, MN.wx_apart segs = true -> gmem_rel m m0 ->
  forall pc, fetch_word_ov segs m pc = fetch_word_ov segs m0 pc.
Proof. intros m m0 Hwx HR pc. unfold fetch_word_ov. rewrite (gcode_read_ov_rel m m0 Hwx HR). reflexivity. Qed.

Lemma gfetch_half_any_rel : forall m m0, MN.wx_apart segs = true -> gmem_rel m m0 ->
  forall pc, fetch_half_any segs m pc = fetch_half_any segs m0 pc.
Proof.
  intros m m0 Hwx HR pc. unfold fetch_half_any, fetch_half_ov.
  rewrite (gcode_read_ov_rel m m0 Hwx HR). reflexivity.
Qed.

Lemma gfetch_tail_any_rel : forall m m0, MN.wx_apart segs = true -> gmem_rel m m0 ->
  forall pc, fetch_tail_any segs m pc = fetch_tail_any segs m0 pc.
Proof.
  intros m m0 Hwx HR pc. unfold fetch_tail_any.
  rewrite !(gfetch_half_any_rel m m0 Hwx HR). reflexivity.
Qed.

Lemma gstep_rel : forall s s0 s0', MN.wx_apart segs = true -> gms_rel s s0 ->
  RiscvSemantics.step segs s0 = MachineOk s0' ->
  exists s', RiscvSemantics.step segs s = MachineOk s' /\ gms_rel s' s0' /\ gcj_same (ms_mem s) (ms_mem s').
Proof.
  intros s s0 s0' Hwx Hrel H. pose proof Hrel as (_ & _ & Ep & _ & _ & _ & _ & HR).
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses, ms_pc in H |- *.
  rewrite Ep, (gfetch_word_ov_rel _ _ Hwx HR), (gfetch_tail_any_rel _ _ Hwx HR).
  revert H.
  destruct (fetch_word segs (ms_pc_val s0)) as [w|]; [intros H; exact (gdecode_rel s s0 w s0' Hrel H)|].
  destruct (fetch_word_ov segs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (gdecode_rel s s0 w s0' Hrel H)|].
  destruct (fetch_tail_any segs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (gdecode_rel s s0 w s0' Hrel H)|].
  destruct (fetch_failure segs (ms_mem s0) (ms_pc_val s0)) as [st| |] eqn:Ef.
  - exfalso. exact (MN.fetch_failure_not_ok segs _ _ _ Ef).
  - intros H. cbn [drop_access_report] in H. discriminate H.
  - intros H. cbn [drop_access_report] in H. discriminate H.
Qed.

Lemma gmsteps_rel : MN.wx_apart segs = true -> forall s0 s0', msteps segs s0 s0' ->
  forall s, gms_rel s s0 -> exists s', msteps segs s s' /\ gms_rel s' s0' /\ gcj_same (ms_mem s) (ms_mem s').
Proof.
  intros Hwx s0 s0' H. induction H as [x|x y z [Hsvc Hst] HT IH]; intros s Hrel.
  - exists s. split; [apply msteps_refl|]. split; [exact Hrel|]. intros a _. reflexivity.
  - destruct (gstep_rel s x y Hwx Hrel Hst) as (t & Et & Rt & Ot).
    destruct (IH t Rt) as (s' & Es' & Rs' & Os').
    exists s'. split; [|split; [exact Rs'|]].
    + apply (msteps_cons segs s t s'); [|exact Es']. split; [|exact Et].
      destruct Hrel as (_ & _ & _ & Esvc & _). rewrite Esvc. exact Hsvc.
    + intros a Ha. rewrite (Os' a Ha). exact (Ot a Ha).
Qed.

Theorem gevt_rel : forall (Q : machine_state -> Prop) s s0, MN.wx_apart segs = true -> gms_rel s s0 ->
  evt segs Q s0 ->
  evt segs (fun s' => exists s0', Q s0' /\ gms_rel s' s0' /\ gcj_same (ms_mem s) (ms_mem s')) s.
Proof.
  intros Q s s0 Hwx Hrel (s0' & Hs & HQ).
  destruct (gmsteps_rel Hwx s0 s0' Hs s Hrel) as (s' & Hs' & Hr & Ho).
  exists s'. split; [exact Hs'|]. exists s0'. split; [exact HQ|]. split; [exact Hr | exact Ho].
Qed.

Theorem gevt_rel_MS : forall (Q : machine_state -> Prop) R F pc fc rv m m0 ro,
  MN.wx_apart segs = true -> gmem_rel m m0 ->
  evt segs Q (MS R F pc fc rv m0 ro) ->
  evt segs (fun s => exists s0, Q s0 /\ gms_rel s s0 /\ gcj_same m (ms_mem s)) (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m m0 ro Hwx HR H.
  exact (gevt_rel Q (MS R F pc fc rv m ro) (MS R F pc fc rv m0 ro) Hwx
    (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl HR))))))) H).
Qed.

Theorem gevt_normalize : forall (Q : machine_state -> Prop) R F pc fc rv m ro,
  MN.wx_apart segs = true -> MN.ro_agree segs m ->
  evt segs Q (MS R F pc fc rv (gdrop_normalize m) ro) ->
  evt segs (fun s => exists s0, Q s0 /\ gms_rel s s0 /\ gcj_same m (ms_mem s)) (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m ro Hwx Hro H.
  exact (gevt_rel_MS Q R F pc fc rv m (gdrop_normalize m) ro Hwx (gmem_rel_normalize m Hro) H).
Qed.

(* ---- the final stores: what the related store m (the harness's) shows of m0 (the walk's) ---- *)
Lemma gbytes_at_rel : forall m m0 a bs, gmem_rel m m0 -> bytes_at segs m0 a bs -> bytes_at segs m a bs.
Proof.
  intros m m0 a bs HR (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E.
  - apply (gmrd_rel m m0 _ b HR). rewrite (H3 i Hi). exact E.
  - apply nth_error_None in E. lia.
Qed.

(* MemNorm.mrd_normalize_cj (:878) with cj_drop's cases replaced by the one fact a read needs *)
Lemma gmrd_normalize : forall m x, MN.ro_agree segs m ->
  (drop x = true -> ro_addr segs x = false -> m x = None) ->
  mrd segs (gdrop_normalize m) x = mrd segs m x.
Proof.
  intros m x Hro Hx. unfold mrd at 1. unfold gdrop_normalize.
  destruct (drop x) eqn:E; [|reflexivity].
  destruct (ro_addr segs x) eqn:Er.
  - rewrite (Hro x Er). reflexivity.
  - unfold mrd. rewrite (Hx eq_refl eq_refl). reflexivity.
Qed.

Lemma gwr_at_rel : forall m m0 a n, gmem_rel m m0 -> wr_at segs m0 a n -> wr_at segs m a n.
Proof.
  intros m m0 a n HR (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  pose proof (H3 i Hi) as W.
  rewrite <- (gwview_rel m m0 _ HR (gkeep_of_wview m m0 _ HR W)). exact W.
Qed.

Lemma gwr_at_norm : forall m m0 a n, gmem_rel m m0 -> wr_at segs m a n ->
  (forall i, (0 <= i < n)%Z -> drop (wa (a + i)) = false) -> wr_at segs m0 a n.
Proof.
  intros m m0 a n HR (H1 & H2 & H3) Hk. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite (gwview_rel m m0 _ HR (Hk i Hi)). exact (H3 i Hi).
Qed.

Lemma gmunch_rel : forall W m m0 m' m0', gmem_rel m m0 -> gmem_rel m' m0' -> gcj_same m m' ->
  munch W m0 m0' -> munch W m m'.
Proof.
  intros W m m0 m' m0' HR HR' Ho H x Hx. destruct (drop x) eqn:E.
  - exact (Ho x E).
  - rewrite <- (gmem_rel_keep m' m0' x HR' E), <- (gmem_rel_keep m m0 x HR E). exact (H x Hx).
Qed.

Lemma gwmono_rel : forall m m0 m' m0', gmem_rel m m0 -> gmem_rel m' m0' -> gcj_same m m' ->
  wmono segs m0 m0' -> wmono segs m m'.
Proof.
  intros m m0 m' m0' HR HR' Ho H x Hx. destruct (drop x) eqn:E.
  - unfold wview in Hx |- *. rewrite (Ho x E). exact Hx.
  - rewrite <- (gwview_rel m' m0' x HR' E). apply H.
    rewrite (gwview_rel m m0 x HR E). exact Hx.
Qed.

Lemma gmem_unchanged_rel : forall m m0 m' m0', gmem_rel m m0 -> gmem_rel m' m0' -> gcj_same m m' ->
  (forall x, m0' x = m0 x) -> forall x, m' x = m x.
Proof.
  intros m m0 m' m0' HR HR' Ho H x.
  exact (gmunch_rel nil m m0 m' m0' HR HR' Ho (fun y _ => H y) x I).
Qed.

End WithDrop.
