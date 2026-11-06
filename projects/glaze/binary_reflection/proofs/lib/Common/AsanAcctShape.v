(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.PrimString LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DivergeSim.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.PrimString.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac div_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP1.
Context {fx : FPState}.


Lemma is_prefix_app_mono {A} : forall (e a b : list A),
  is_prefix a b -> is_prefix (e ++ a) (e ++ b).
Proof. induction e; cbn; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim].
  unfold materialize_model_accesses; cbn.
  unfold materialize_accesses, newly_materialized_pages; cbn.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_of_accesses : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  mi_account_step segs ms model =
    match materialize_model_accesses model ranges with
    | Some model' => MachineOk (ms', model')
    | None => MachineFault
    end.
Proof.
  intros segs ms model ms' ranges Hstep.
  unfold mi_account_step. rewrite Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_no_access : forall segs ms model ms',
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros segs ms model ms' Hstep.
  rewrite (mi_account_step_of_accesses segs ms model ms' [] Hstep).
  rewrite materialize_model_accesses_nil. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_addi_0 : forall a : word, v_addi a 0 = a.
Proof.
  intro a. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma self_jump_step_accesses : forall segs ms w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms []).
Proof.
  intros segs ms w rd imm sz Hsvc Hfetch Hecall Hdecode Hx0 Himm.
  unfold RiscvSemantics.step_accesses.
  rewrite Hfetch.
  unfold RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  rewrite Hdecode. cbv beta iota.
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses Sem.exec
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
  rewrite Hx0. cbv beta iota.
  rewrite b_addsext, Himm, v_addi_0.
  destruct ms; cbn in Hsvc; subst; reflexivity.
Qed.



Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition silent_loop (P : config -> Prop) : Prop :=
  forall c, P c ->
    m_halted (cfg_model c) = None /\
    ms_svc_pending (cfg_ms c) = None /\
    exists ms' model',
      mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
      P (mkCfg ms' model').










(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_spin : machine_state -> Model -> Prop :=
| ts_spin : forall ms model,
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms, model) ->
    to_spin ms model
| ts_step : forall ms model ms' model',
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    to_spin ms' model' ->
    to_spin ms model.

(* [comment removed for export] *)

Lemma ts_spin_no_access : forall ms model,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms []) ->
  to_spin ms model.
Proof.
  intros ms model Hsvc Hstep.
  apply ts_spin; [exact Hsvc | exact (mi_account_step_no_access segs ms model ms Hstep)].
Qed.




(* [comment removed for export] *)
Lemma ts_spin_of_step_j : forall ms model w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  to_spin ms model.
Proof.
  intros. eapply ts_spin_no_access; [assumption|].
  eapply self_jump_step_accesses; eassumption.
Qed.

(* [comment removed for export] *)
Definition spinning (c : config) : Prop :=
  to_spin (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None.










(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_self_jump (ms : machine_state) : bool :=
  match ms_svc_pending ms with
  | Some _ => false
  | None =>
    match fetch_word segs (ms_pc ms) with
    | Some w =>
      if is_ecall w then false else
      match decode_any w with
      | Some (Jal rd imm, _) => is_x0 rd && (bv_signed imm =? 0)%Z
      | _ => false
      end
    | None => false
    end
  end.

Lemma is_self_jump_to_spin : forall ms model,
  is_self_jump ms = true -> to_spin ms model.
Proof.
  intros ms model H. unfold is_self_jump in H.
  destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
  destruct (fetch_word segs (ms_pc ms)) as [w|] eqn:Hfetch; [|discriminate].
  destruct (is_ecall w) eqn:Hecall; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hdecode; [|discriminate].
  destruct i; try discriminate.
  apply andb_prop in H as [Hx0 Himm].
  apply Z.eqb_eq in Himm.
  eapply ts_spin_of_step_j; eassumption.
Qed.

(* [comment removed for export] *)
Fixpoint spin_c (fuel : nat) (ms : machine_state) (model : Model) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if is_self_jump ms then true
    else
      match ms_svc_pending ms with
      | Some _ => false
      | None =>
        match mi_account_step segs ms model with
        | MachineOk (ms', model') => spin_c fuel' ms' model'
        | _ => false
        end
      end
  end.

Lemma spin_c_to_spin : forall fuel ms model,
  spin_c fuel ms model = true -> to_spin ms model.
Proof.
  induction fuel as [|fuel IH]; intros ms model H; cbn in H;
    [discriminate|].
  destruct (is_self_jump ms) eqn:Hj;
    [exact (is_self_jump_to_spin ms model Hj)|].
  destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
  destruct (mi_account_step segs ms model) as [[ms' model']| |] eqn:Hacc;
    try discriminate.
  exact (ts_step ms model ms' model' Hsvc Hacc (IH ms' model' H)).
Qed.

End WithSegs.

(* [comment removed for export] *)
End WithFP1.
Ltac prove_to_spin fuel :=
  apply (spin_c_to_spin _ fuel);
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Section WithFP2.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section TwoBranchToy.
Variable segs : list Segment.
Variable c0 : config.
Variable evs_g : list event.
Variable c_g c_r : config.
Variable T : list event.
Variable P : config -> Prop.

Hypothesis Hsplit : forall evs to, sstep segs c0 evs to ->
  (evs = evs_g /\ to = SNext c_g) \/ (evs = [] /\ to = SNext c_r).
Hypothesis Hstep_g : sstep segs c0 evs_g (SNext c_g).
Hypothesis Hg_obs : forall tr, obs_trace segs c_g tr <-> is_prefix tr T.
Hypothesis Hg_noerr : ~ reaches_error segs c_g.
Hypothesis Hloop : silent_loop segs P.
Hypothesis HP_r : P c_r.



End TwoBranchToy.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.
Module SelfJumpImage.










End SelfJumpImage.
End DivergeSim.
Module LazyFrame.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import DivergeSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop :=
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z /\
  (bv_unsigned a + Z.of_nat n <= bv_unsigned lo
   \/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned a)%Z.

(* [comment removed for export] *)
Definition accesses_outside_lazy
    (accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
  forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
    access_outside_range a n lo sz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_all_false {A} : forall (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
  intros f l H; induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim tm]. reflexivity.
Qed.

Lemma materialize_accesses_no_new : forall lazy materialized used limit accs,
  newly_materialized_pages lazy materialized accs = [] ->
  materialize_accesses lazy materialized used limit accs = Some materialized.
Proof.
  intros lazy materialized used limit accs Hnew.
  unfold materialize_accesses. rewrite Hnew. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
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
Lemma page_in_ranges_outside : forall lazy (a : word) (n k : nat),
  (k < n)%nat ->
  (forall lo sz, In (lo, sz) lazy -> access_outside_range a n lo sz) ->
  page_in_ranges (page_base_of (bv_unsigned a + Z.of_nat k)) lazy = false.
Proof.
  intros lazy a n k Hk Hout.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  apply Bool.not_true_is_false. intro Htrue.
  unfold page_in_ranges in Htrue.
  apply existsb_exists in Htrue.
  destruct Htrue as ([lo sz] & Hin & Htest).
  cbn [fst snd] in Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (Hout lo sz Hin) as [Hnw Hdisj].
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (bv_unsigned_in_range 64 lo) as Hlo_rg.
  pose proof (bv_unsigned_in_range 64 sz) as Hsz_rg.
  assert (Hz0 : (0 <= z)%Z) by (unfold z; lia).
  (* [comment removed for export] *)
  assert (Hq0 : (0 <= z / page_size)%Z)
    by (apply Z.div_pos; [exact Hz0 | unfold page_size; lia]).
  pose proof (Z.div_mod z page_size
                ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound z page_size
                ltac:(unfold page_size; lia)) as Hmb.
  assert (Hpb : bv_unsigned (page_base_of z)
                = ((z / page_size) * page_size)%Z).
  { unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64)%Z.
    unfold page_size in *. unfold z in *. lia. }
  rewrite Hpb in Hlo, Hhi.
  (* [comment removed for export] *)
  unfold page_size in *. unfold z in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem materialize_model_accesses_disjoint : forall m accs,
  accesses_outside_lazy accs (m_vm_lazy m) ->
  materialize_model_accesses m accs = Some m.
Proof.
  intros m accs Hout.
  assert (Hnew : newly_materialized_pages
                   (m_vm_lazy m) (m_vm_materialized m) accs = []).
  { unfold newly_materialized_pages. apply filter_all_false.
    intros p Hp.
    destruct (accesses_pages_in accs [] p Hp)
      as [[] | (a & n & k & Hin & Hk & ->)].
    rewrite (page_in_ranges_outside (m_vm_lazy m) a n k Hk).
    - reflexivity.
    - intros lo sz Hlz. exact (Hout a n lo sz Hin Hlz). }
  unfold materialize_model_accesses.
  rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m)
             (vm_backing_used m) (vm_limit (m_vmmaps m)) accs Hnew).
  cbv iota beta.
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_disjoint : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros segs ms model ms' ranges Hstep Hout.
  rewrite (mi_account_step_of_accesses segs ms model ms' ranges Hstep).
  rewrite (materialize_model_accesses_disjoint model ranges Hout).
  reflexivity.
Qed.


End LazyFrame.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module SymTac.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.WallSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.DrainSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.Footprint OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sr_pins (ps : list (reg * expr)) (sr : list expr) : list expr :=
  match ps with
  | [] => sr
  | (r, e) :: rest => sr_pins rest (sr_upd sr (ridx r) e)
  end.

(* [comment removed for export] *)
Definition pins_ok (E : env) (regs : bvmap 5 word) (ps : list (reg * expr))
  : Prop :=
  Forall (fun p => getr regs (fst p) = edenot E (snd p)) ps.

Lemma regs_ok_pins : forall E ps sr regs,
  regs_ok E sr regs -> pins_ok E regs ps -> regs_ok E (sr_pins ps sr) regs.
Proof.
  intros E ps. induction ps as [|[r e] rest IH]; intros sr regs Hr Hp;
    [exact Hr|].
  unfold pins_ok in Hp. inversion Hp as [|p ps' Hh Ht Heq]; subst.
  cbn [fst snd] in Hh. cbn [sr_pins].
  apply IH; [apply regs_ok_pin; [exact Hr | exact Hh] | exact Ht].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alu64_add_0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
  intro x. rewrite alu_add. change (v_add x (Z_to_bv 64 0)) with (v_addi x 0).
  apply v_addi_0.
Qed.

(* [comment removed for export] *)
Lemma aluw_add_0 : forall x : word,
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 0))) = v_lw x.
Proof.
  intro x. rewrite low32_lit.
  change (Z_to_bv 32 0) with (@Z_to_bv 32 0).
  rewrite alu32_add_0. apply b_lw_val.
Qed.

(* [comment removed for export] *)
Lemma aluw_addi_lit : forall (a : word) (k : Z),
  sext 64 (alu32 ALU_ADD (low32 a) (low32 (Z_to_bv 64 k))) = v_addiw a k.
Proof.
  intros a k. apply bv_eq. unfold v_addiw.
  rewrite sext32_unsigned, !Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_ADD (low32 a) (low32 (Z_to_bv 64 k)))
    with (low32 a + low32 (Z_to_bv 64 k)).
  rewrite bv_add_unsigned, !low32_unsigned, Z_to_bv_unsigned.
  rewrite bv_swrap_wrap', bv_swrap_add_idemp_l.
  rewrite (bv_wrap_bv_wrap 32 64 k) by lia.
  rewrite bv_swrap_add_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bdenot_var : forall E n, bdenot E (SBVar n) = E n.
Proof. reflexivity. Qed.

Lemma bdenot_lit : forall E, bdenot E SBLit = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma edenot_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

Lemma edenot_var : forall E n, edenot E (EVar n) = E n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_addi_Z : forall (x : word) (i : Z),
  v_addi x i = Z_to_bv 64 (bv_unsigned x + i).
Proof. reflexivity. Qed.

Lemma adenot_var : forall E n k,
  adenot E (SA (SBVar n) k) = Z_to_bv 64 (bv_unsigned (E n) + k).
Proof. reflexivity. Qed.

Lemma adenot_lit : forall E k, adenot E (SA SBLit k) = Z_to_bv 64 k.
Proof.
  intros E k. unfold adenot. cbn [a_base a_off bdenot].
  rewrite v_addi_Z, u_Z_to_bv64_0; f_equal; lia.
Qed.

(* [comment removed for export] *)
End WithFP1.
Ltac sym_env_cbn :=
  cbn [Eplus Nat.ltb Nat.leb Nat.sub Nat.add Z.of_nat nth app fst snd
       a_base a_off e_addr e_width e_val].

Ltac sym_env_norm :=
  sym_env_cbn;
  rewrite ?adenot_var, ?adenot_lit, ?bdenot_var, ?bdenot_lit,
          ?edenot_lit, ?edenot_var, ?u_Z_to_bv64_0;
  sym_env_cbn;
  repeat match goal with
  | |- context [getr ?rs (Z_to_bv 5 ?z)] =>
      let u := eval vm_compute in z in
      let l := constr:(@BV 5 u ltac:(vm_compute; exact I)) in
      replace (Z_to_bv 5 z) with l by (apply bv_eq; vm_compute; reflexivity)
  end.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP3.
Ltac sym_z_lit k :=
  lazymatch k with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac sym_z_norm :=
  repeat match goal with
  (* [comment removed for export] *)
  | |- context [Z_to_bv 64 (0 + ?k)] =>
      sym_z_lit k; replace (0 + k)%Z with k by lia
  | |- context [Z_to_bv 64 (?a - ?k1 + ?k2)] =>
      sym_z_lit k1; sym_z_lit k2;
      let v := eval vm_compute in (k1 - k2)%Z in
      replace (a - k1 + k2)%Z with (a - v)%Z by lia
  | |- context [Z_to_bv 64 (?a + ?k1 + ?k2)] =>
      sym_z_lit k1; sym_z_lit k2;
      let v := eval vm_compute in (k1 + k2)%Z in
      replace (a + k1 + k2)%Z with (a + v)%Z by lia
  | |- context [Z_to_bv 64 (?a + Zneg ?p)] =>
      replace (a + Zneg p)%Z with (a - Zpos p)%Z by lia
  end.

Ltac sym_addr_norm :=
  imm_norm; rewrite ?v_addi_Z; sym_env_norm; u_norm; sym_z_norm.

Section WithFP6.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP6.
Ltac sym_lit_norm :=
  repeat match goal with
  (* [comment removed for export] *)
  | |- context [wbytes ?m (Z_to_bv 64 ?z) ?bs] =>
      lazymatch z with
      | Zpos _ =>
          let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
          replace (Z_to_bv 64 z) with l by bveq
      end
  | |- context [word_to_le_bytes ?n (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | Zpos _ =>
          let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
          replace (Z_to_bv 64 z) with l by bveq
      end
  end.

Section WithFP7.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP7.
Ltac sym_norm :=
  cbn [edenot sr_get nth ridx s_regs s_pc s_log s_next branch_taken];
  rewrite ?alu64_add_0, ?aluw_add_0;
  rewrite ?aluw_addi_lit;
  rewrite ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slt, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra;
  rewrite ?v_add_lit, ?v_sub_lit;
  sym_addr_norm.

Section WithFP8.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP8.
Ltac sym_mem_norm :=
  cbn [mem_denot e_addr e_width e_val];
  sym_norm; sym_lit_norm.

Section WithFP9.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msteps_to_exit : forall segs code ms ms',
  msteps segs ms ms' -> to_exit segs code ms' -> to_exit segs code ms.
Proof.
  intros segs code ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH]; [auto|].
  intro He. eapply te_step; eauto.
Qed.

Lemma msteps_to_wr : forall segs LH bs ms ms',
  msteps segs ms ms' ->
  AllocSim.StreamSim.to_wr segs LH bs ms' -> AllocSim.StreamSim.to_wr segs LH bs ms.
Proof.
  intros segs LH bs ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH];
    [auto|].
  intro Hw. eapply AllocSim.StreamSim.twr_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma msteps_lh_next : forall segs LH ms ms',
  msteps segs ms ms' ->
  AllocSim.StreamSim.lh_next segs LH ms' -> AllocSim.StreamSim.lh_next segs LH ms.
Proof.
  intros segs LH ms ms' H (m & Hm & HL). exists m. split; [|exact HL].
  eapply msteps_trans; eauto.
Qed.

(* [comment removed for export] *)
End WithFP9.
Ltac sym_halted :=
  solve [ reflexivity
        | eassumption
        | (rewrite ?MmapSim.mmap_model_halted, ?MmapSim.munmap_model_halted;
           solve [ reflexivity | eassumption ])
        | (cbn [cfg_model m_halted]; autorewrite with model; solve [ reflexivity | eassumption ]) ].

Ltac sym_no_lazy :=
  cbn [cfg_model];
  repeat first
    [ rewrite MmapSim.mmap_model_lazy
    | apply MmapSim.munmap_model_no_lazy ];
  solve [ reflexivity | eassumption ].

Section WithFP10.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP10.
Ltac chain_mst :=
  first [ eapply CatExec.CatSim.msteps_to_wexit
        | eapply MmapSim.msteps_twm
        | eapply MmapSim.msteps_twm_tail
        | eapply MmapSim.msteps_tmw
        | eapply AllocSim.StreamSim.msteps_to_rd
        | eapply msteps_to_wr
        | eapply AllocSim.WallSim.msteps_to_wall_tail
        | eapply AllocSim.WallSim.msteps_to_wallexit
        | eapply Mh32.DrainSim.msteps_to_rd
        | eapply Mh32.DrainSim.msteps_to_out
        | eapply msteps_to_exit
        | eapply msteps_lh_next
        | (eapply StoreOk.ShapeAlg.rz_msteps; [ sym_halted | sym_no_lazy | | ])
        | eapply msteps_trans ].

Section WithFP11.
Context {fx : FPState}.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP11.
Ltac sym_close :=
  first [ reflexivity
        | (f_equal; lia)
        | (apply bv_eq; u_norm; lia)
        | bveq ].

Ltac sym_regs H :=
  getr_resolve; regupd_resolve;
  rewrite <- ?getr_nz by reg_neq_tac;
  rewrite ?(H _);
  repeat match goal with
  | |- context [sr_get ?a ?b] =>
      let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v
  end;
  sym_norm.

Section WithFP13.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP13.
Ltac sym_reg H R r v tac :=
  assert (getr R r = v) by (sym_regs H; tac).

Section WithFP14.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP14.
Ltac list_len l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | @cons _ _ ?t => let n := list_len t in constr:(S n)
  end.

Section WithFP15.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP15.
Ltac sym_pc_Z :=
  lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] =>
      lazymatch p with
      | Z_to_bv 64 _ => idtac
      | _ => check_closed_term p;
             let u := vm_eval (bv_unsigned p) in
             replace p with (Z_to_bv 64 u) by bveq
      end
  end.

Section WithFP16.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP16.
Ltac sym_pc_lit :=
  try lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] => wlit p
  end.

Section WithFP17.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP17.
Ltac sym_sc_auto :=
  first [ reflexivity | (repeat split; lia) ].

Section WithFP18.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP18.
Ltac sym_pin_auto :=
  first
  [ reflexivity
  | multimatch goal with
    | H : regs_ok _ _ _ |- _ =>
        sym_regs H; first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia) ]
    end ].

Section WithFP19.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP19.
Ltac sym_block segs fuel dirs rds ps pvals rvals R H :=
  sym_pc_Z;
  lazymatch goal with
  | |- context [ mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom ] =>
    let k := list_len pvals in
    let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
    let EE := constr:(Eplus regs (pvals ++ rvals)) in
    let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
    let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
    let Hsc := fresh "Hsc" in
    let Hst := fresh "Hst" in
    let Hms := fresh "Hms" in
    let Heq := fresh "Heq" in
    let Hlf := fresh "Hlf" in
    let msx := fresh "msx" in
    assert (Hsc : scs_denot segs mem EE scs);
    [ unfold scs_denot;
      repeat first [ apply Forall_nil | apply Forall_cons ];
      cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
      try sym_norm; try sym_sc_auto
    | assert (Hst : st_ok EE mem rom ss0 (mkst regs (Z_to_bv 64 pc) mem rom));
      [ exists regs; split;
        [ reflexivity
        | split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
        unfold pins_ok;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
      | destruct (sym_exec_sound segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
                    ltac:(vm_compute; reflexivity) Hsc Hst)
          as (msx & Hms & (R & Heq & H & Hlf));
        clear Hsc Hst;
        chain_mst; [ exact Hms | ];
        rewrite Heq; clear Heq Hms msx;
        cbn [s_pc s_log]; try sym_mem_norm;
        norm_pc; sym_pc_lit ] ]
  end.

Section WithFP20.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP20.
Ltac sym_block_ex segs ms fuel dirs rds ps pvals rvals R H Hms :=
  lazymatch ms with
  | mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom =>
    let k := list_len pvals in
    let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
    let EE := constr:(Eplus regs (pvals ++ rvals)) in
    let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
    let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
    let Hsc := fresh "Hsc" in
    let Hst := fresh "Hst" in
    assert (Hsc : scs_denot segs mem EE scs);
    [ unfold scs_denot;
      repeat first [ apply Forall_nil | apply Forall_cons ];
      cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
      try sym_norm; try sym_sc_auto
    | assert (Hst : st_ok EE mem rom ss0 ms);
      [ exists regs; split;
        [ reflexivity
        | split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
        unfold pins_ok;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
      | destruct (sym_exec_ex segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
                    ltac:(vm_compute; reflexivity) Hsc Hst)
          as (R & H & Hms);
        clear Hsc Hst;
        cbn [s_pc s_regs s_log mem_denot] in Hms ] ]
  end.

Section WithFP21.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP21.
Ltac sym_chain Hms :=
  sym_pc_Z; chain_mst; [ exact Hms | ]; norm_pc; sym_pc_lit.
End SymTac.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module SpinAlg.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg DivergeSim LazyFrame SymTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
| srz_spin : forall c,
    to_spin segs (cfg_ms c) (cfg_model c) ->
    m_halted (cfg_model c) = None ->
    srealizes c t_nil
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.



(* [comment removed for export] *)

Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c Hspin Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
Qed.









(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.



(* [comment removed for export] *)
Lemma srz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma srz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma node_instr_disjoint : forall ms model ms' ranges,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' ranges Hh Hsvc Hstep Hout.
  pose proof (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
    as Hacc.
  apply node_ok_of_u; [CfgStep.kit_pending_on |].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model); assumption.
  - intros e st Hss.
    inversion Hss; subst; try congruence.
    match goal with
    | H : mi_account_step _ _ _ = MachineOk _ |- _ =>
        rewrite Hacc in H; injection H; intros; subst
    end.
    exists tt. split; reflexivity.
Qed.





(* [comment removed for export] *)
Lemma node_munmap : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                  model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
  apply node_ok_of_u; [exact (CfgStep.kit_pending_on_sysno segs ms model x8 215 Hsvc Hno eq_refl) |]. split.
  - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.




(* [comment removed for export] *)
Lemma node_mmap_grant : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  node_ok segs (mkCfg ms model)
    {a : word | grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
    (fun _ => [])
    (fun i => match i with
       | exist _ a _ =>
           mkCfg (advance_past_svc
                    (apply_effect ms
                       (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                 (mmap_model a (page_round_up (ms_gpr ms 1)) model)
       end).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Hnf.
  set (n := page_round_up (ms_gpr ms 1)).
  split.
  - intros [a Ha]; cbn.
    apply (sstep_cfg_syscall segs CfgStep.kit_cfg ms model x8 (mkEffect a [] [(a, n)])
             (mmap_model a n model) (mmap_model a n model) []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_succ_ok; assumption.
    + exact (grant_not_spurious segs ms x8 model a (mkEffect a [] [(a, n)]) Hno Ha eq_refl).
    + rewrite mmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
  - intros e st Hss.
    destruct (sstep_mmap_inv_grant segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hnf Hss)
      as [-> (a & Ha & ->)].
    exists (exist _ a Ha). split; reflexivity.
Qed.



End WithSegs.


(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chain_mst_sp :=
  first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
        | chain_mst ].




(* [comment removed for export] *)

(* [comment removed for export] *)
Section SpinBranchReal.
Variable segs : list Segment.
Variables (ms : machine_state) (model : Model) (x8 : word).
Variables (bs : list (list byte)) (cs : word).

Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd : fd1chan model.
Hypothesis Hsvc : ms_svc_pending ms = Some x8.
Hypothesis Hno : bv_unsigned x8 = 222%Z.
Hypothesis Hargs : mmap_args_ok ms.
(* [comment removed for export] *)
Hypothesis Hrefuse : forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model.
(* [comment removed for export] *)
Hypothesis Hgrant : forall a,
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  MmapSim.twm segs
    (advance_past_svc
       (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
    (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs.
Hypothesis Hex : exists a,
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true.
Hypothesis Hbs : bufs_modeled bs.




End SpinBranchReal.
End SpinAlg.
Require LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module NoReserve.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg DivergeSim LazyFrame SymTac SpinAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_syscall_effect_nil :
  forall (m : Model) (r : word) (zs us : list (word * word)),
  materialize_model_accesses m
    (syscall_effect_accesses (mkEffectU r [] zs us [] []))
  = Some m.
Proof. intros m r zs us. exact (materialize_model_accesses_nil m). Qed.


(* [comment removed for export] *)
Lemma materialize_munmap_eff_nil : forall (m : Model) (ms : machine_state),
  materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms))
  = Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.






(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
  vm_add_lazy a n (mmap_model a n m).

Lemma mmap_model_noreserve_halted : forall a n m,
  m_halted (mmap_model_noreserve a n m) = m_halted m.
Proof. reflexivity. Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_args_ok_noreserve (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 16418 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
Lemma mmap_args_ok_noreserve_gates : forall ms,
  mmap_args_ok_noreserve ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\
  mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
  = true.
Proof.
  intros ms (H1 & H2 & H3 & H4 & H5).
  split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
  split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noreserve_b_flags : mmap_noreserve_b (Z_to_bv 64 16418) = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

Lemma grant_ok_nr_unpack : forall hint m a n,
  grant_ok_nr hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_nr in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  auto 6.
Qed.

(* [comment removed for export] *)
Lemma grant_nr_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_nr hint model a n = true ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg.
  destruct (grant_ok_nr_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_nr_not_errno_when : forall b hint model a n,
  (0 <= n)%Z -> grant_ok_nr hint model a n = true ->
  errno_ret_in (mmap_errnos_when b) a = false.
Proof.
  intros [|] hint model a n Hn Hg; [exact (grant_nr_not_errno hint model a n Hn Hg) | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma grant_ok_nr_not_refusable : forall hint model a n,
  grant_ok_nr hint model a n = true ->
  mmap_grant_refusable (Z_to_bv 64 16418) model n = false.
Proof.
  intros hint model a n Hg. unfold mmap_grant_refusable, mmap_noreserve_backed_ok.
  rewrite mmap_noreserve_b_flags. cbn [negb orb].
  rewrite (vm_find_base_complete (m_vmmaps model) n a); [reflexivity|]. exact Hg.
Qed.



(* [comment removed for export] *)
Lemma mmap_succ_ok_noreserve : forall segs ms x8 model a,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model a Hno Ha Hg.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite (grant_nr_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  unfold grant_ok_nr in Hg. rewrite !andb_true_iff in Hg.
  destruct Hg as [[[H1 H2] H3] H4].
  rewrite Hflags.
  unfold mmap_noreserve_backed_ok, with_mmap_backing.
  rewrite mmap_noreserve_b_flags.
  rewrite H1, H2, H3, H4. cbn [andb].
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_ok_inv_noreserve : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
      /\ model' = model) \/
   (exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
      /\ model' = mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hflags in Hspec.
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite mmap_noreserve_b_flags in Hspec.
  destruct eff as [r ws zs us cs copyins].
  cbv beta iota zeta in Hspec.
  destruct ws as [|w ws]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  match type of Hspec with context [errno_ret_in ?es r] => destruct (errno_ret_in es r) eqn:Herr end;
    rewrite ?Herr in Hspec; cbv beta iota in Hspec.
  - destruct zs as [|z zs]; [|discriminate].
    inversion Hspec; subst.
    split; [reflexivity|]. left.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    exists e. auto.
  - rewrite andb_true_r in Hspec.
    destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
              && (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
              && region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))) eqn:Hcond;
      rewrite ?Hcond in Hspec.
    2:{ rewrite andb_false_l in Hspec. discriminate. }
    destruct (listNN_eqb zs
                [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
      rewrite ?Hzs in Hspec.
    2:{ rewrite andb_false_r in Hspec. discriminate. }
    cbn [andb] in Hspec.
    apply listNN_eqb_eq in Hzs. subst zs.
    inversion Hspec; subst.
    split; [reflexivity|]. right.
    exists r. split; [|split].
    + unfold grant_ok_nr. exact Hcond.
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_ok_inv_noreserve_grant : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  ~ spurious_refusal_cfg CfgStep.kit_cfg (sys_input segs ms x8) model eff ->
  evs = [] /\
  (exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
      /\ model' = mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hnf Hspec Hns.
  destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs Hno Ha Hspec) as [Hevs [(e & He & -> & ->) | Hg]];
    [|split; assumption].
  exfalso. apply Hns.
  assert (Hg : exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true).
  { pose proof Ha as (_ & _ & Hflags & _ & _).
    rewrite Hflags in Hnf. unfold mmap_grant_refusable, mmap_noreserve_backed_ok in Hnf.
    rewrite mmap_noreserve_b_flags in Hnf. cbn [negb orb] in Hnf. apply negb_false_iff in Hnf.
    destruct (vm_gap_available_find _ _ Hnf) as (a & Hf).
    exists a. unfold grant_ok_nr.
    unfold vm_find_base in Hf. apply List.find_some in Hf as [_ Hok].
    unfold vm_base_ok in Hok. exact Hok. }
  destruct Hg as (a & Hg).
  split; [| split].
  - rewrite (CfgStep.injected_family_off_alloc_only CfgStep.kit_cfg _ CfgStep.kit_cfg_alloc_only).
    cbn [sys_input in_sysno]. rewrite Hno. reflexivity.
  - apply CfgStep.refusal_b_mmap_errno; [exact Hno | exact He].
  - exists (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]),
      (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model), [].
    split; [exact (mmap_succ_ok_noreserve segs ms x8 model a Hno Ha Hg) |].
    change (eff_ret (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])) with a.
    rewrite (CfgStep.refusal_b_mmap (sys_input segs ms x8) _ _ Hno).
    apply (grant_nr_not_errno (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
      [apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia | exact Hg].
Qed.

Lemma mmap_ok_halted_noreserve : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = m_halted model.
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_ok_inv_noreserve segs ms x8 model eff model' evs Hno Ha Hspec)
    as [_ [(e & _ & _ & ->) | (a & _ & _ & ->)]]; [reflexivity | apply mmap_model_noreserve_halted].
Qed.

Lemma grant_nr_not_spurious : forall segs ms x8 model a eff,
  bv_unsigned x8 = 222%Z ->
  grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  eff_ret eff = a ->
  ~ spurious_refusal_cfg CfgStep.kit_cfg (sys_input segs ms x8) model eff.
Proof.
  intros segs ms x8 model a eff Hno Hg Hr. apply spurious_refusal_not_refusal. rewrite Hr.
  rewrite (CfgStep.refusal_b_mmap (sys_input segs ms x8) _ _ Hno).
  apply (grant_nr_not_errno (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia | exact Hg].
Qed.

Lemma mmap_no_unmodeled_noreserve : forall segs ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  cbv beta iota zeta in Hspec.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  rewrite E in Hspec. cbv beta iota in Hspec.
  match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    discriminate.
Qed.

Section WithSegs.
Variable segs : list Segment.



(* [comment removed for export] *)
Lemma sstep_mmap_inv_noreserve_grant : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sstep_cfg segs CfgStep.kit_cfg (mkCfg ms model) evs st ->
  evs = [] /\
   (exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hnf Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hns : ~ spurious_refusal_cfg _ (sys_input segs ms ?x) model ?eff |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve_grant segs ms x8 model eff model' evs0 Hno Hargs Hnf H3 Hns)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as (a & Hg & -> & ->).
    match goal with
    | Hmat : materialize_model_accesses (mmap_model_noreserve a _ model) _ = Some _ |- _ =>
      rewrite materialize_syscall_effect_nil in Hmat;
      inversion Hmat; subst
    end.
    exists a. auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hns : ~ spurious_refusal_cfg _ (sys_input segs ms ?x) model ?eff,
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_noreserve_grant segs ms x8 model eff model' evs0 Hno Hargs Hnf H3 Hns)
        as (_ & Hcase);
      destruct Hcase as (? & ? & ? & Hm); subst eff model';
      rewrite materialize_syscall_effect_nil in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      rewrite (mmap_ok_halted_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3), Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      assert (Hhn : m_halted model' = None)
          by (rewrite (mmap_ok_halted_noreserve segs ms x8 model eff model' evs0 Hno Hargs H3); exact Hh);
      rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled_noreserve segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
Lemma node_mmap_noreserve_grant : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok_noreserve ms ->
  mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  node_ok segs (mkCfg ms model)
    {a : word | grant_ok_nr (ms_gpr ms 0) model a
                  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
    (fun _ => [])
    (fun i => match i with
       | exist _ a _ =>
           mkCfg (advance_past_svc
                    (apply_effect ms
                       (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                 (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)
       end).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs Hnf.
  set (n := page_round_up (ms_gpr ms 1)).
  split.
  - intros [a Ha]; cbn.
    apply (sstep_cfg_syscall segs CfgStep.kit_cfg ms model x8 (mkEffect a [] [(a, n)])
             (mmap_model_noreserve a n model) (mmap_model_noreserve a n model) []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_succ_ok_noreserve; assumption.
    + exact (grant_nr_not_spurious segs ms x8 model a (mkEffect a [] [(a, n)]) Hno Ha eq_refl).
    + rewrite mmap_model_noreserve_halted; exact Hh.
    + apply materialize_syscall_effect_nil.
  - intros e st Hss.
    destruct (sstep_mmap_inv_noreserve_grant ms model x8 e st Hh Hsvc Hno Hargs Hnf Hss)
      as [-> (a & Ha & ->)].
    exists (exist _ a Ha). split; reflexivity.
Qed.




(* [comment removed for export] *)
Lemma sstep_mmap_inv_lazy_grant : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  sstep_cfg segs CfgStep.kit_cfg (mkCfg ms model) evs st ->
  evs = [] /\
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hnf Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hns : ~ spurious_refusal_cfg _ (sys_input segs ms ?x) model ?eff |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_grant segs ms x8 model eff model' evs0 Hno Hargs Hnf H3 Hns) as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as (a & Hg & -> & ->).
    match goal with
    | Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
      rewrite materialize_syscall_effect_nil in Hmat;
      inversion Hmat; subst
    end.
    exists a. auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hns : ~ spurious_refusal_cfg _ (sys_input segs ms ?x) model ?eff,
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv_grant segs ms x8 model eff model' evs0 Hno Hargs Hnf H3 Hns)
        as (_ & Hcase);
      destruct Hcase as (? & ? & ? & Hm); subst eff model';
      rewrite materialize_syscall_effect_nil in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      rewrite (mmap_ok_halted segs ms x8 model eff model' evs0 Hno Hargs H3), Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      assert (Hhn : m_halted model' = None)
          by (rewrite (mmap_ok_halted segs ms x8 model eff model' evs0 Hno Hargs H3); exact Hh);
      rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
Lemma node_mmap_lazy_grant : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  node_ok segs (mkCfg ms model)
    {a : word | grant_ok (ms_gpr ms 0) model a
                  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
    (fun _ => [])
    (fun i => match i with
       | exist _ a _ =>
           mkCfg (advance_past_svc
                    (apply_effect ms
                       (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                 (mmap_model a (page_round_up (ms_gpr ms 1)) model)
       end).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs Hnf.
  set (n := page_round_up (ms_gpr ms 1)).
  split.
  - intros [a Ha]; cbn.
    apply (sstep_cfg_syscall segs CfgStep.kit_cfg ms model x8 (mkEffect a [] [(a, n)])
             (mmap_model a n model) (mmap_model a n model) []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_succ_ok; assumption.
    + exact (grant_not_spurious segs ms x8 model a (mkEffect a [] [(a, n)]) Hno Ha eq_refl).
    + rewrite mmap_model_halted; exact Hh.
    + apply materialize_syscall_effect_nil.
  - intros e st Hss.
    destruct (sstep_mmap_inv_lazy_grant ms model x8 e st Hh Hsvc Hno Hargs Hnf Hss)
      as [-> (a & Ha & ->)].
    exists (exist _ a Ha). split; reflexivity.
Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_munmap_inv_lazy : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
      subst eff model' evs0
    end.
    match goal with
    | Hmat : materialize_model_accesses
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
      rewrite materialize_munmap_eff_nil in Hmat;
      inversion Hmat; subst
    end.
    split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Heff & Hm & Hevs); subst eff model' evs0;
      rewrite materialize_munmap_eff_nil in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model'; rewrite munmap_model_halted, Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model'; rewrite m_killed_of_m_halted_none in H6;
        [ discriminate | rewrite munmap_model_halted; exact Hh ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

Lemma node_munmap_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                  model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs.
  apply node_ok_of_u; [exact (CfgStep.kit_pending_on_sysno segs ms model x8 215 Hsvc Hno eq_refl) |]. split.
  - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_munmap_eff_nil.
  - intros e st Hss.
    destruct (sstep_munmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.






(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive msteps_acc
    : machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step_accesses segs ms
      = MachineOk (@mkAccessReport machine_state ms1 ranges) ->
    msteps_acc ms1 ms2 accs ->
    msteps_acc ms ms2 (ranges ++ accs).






End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End WithFP1.
Ltac stepacc_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.
Section WithFP2.
Context {fx : FPState}.























(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AsanInitReal.
Variable segs : list Segment.

(* [comment removed for export] *)
Variables (ms1 : machine_state) (model : Model) (x8a : word).
Hypothesis Hh : m_halted model = None.
Hypothesis Hfd : fd1chan model.
Hypothesis Hsvc1 : ms_svc_pending ms1 = Some x8a.
Hypothesis Hno1 : bv_unsigned x8a = 222%Z.
Hypothesis Hargs1 : mmap_args_ok_noreserve ms1.

Let nZ1 : Z := page_round_up_Z (bv_unsigned (ms_gpr ms1 1)).
Let n1 : word := page_round_up (ms_gpr ms1 1).
Let model1 (a1 : word) : Model := mmap_model_noreserve a1 n1 model.
Let post1 (a1 : word) : machine_state :=
  advance_past_svc (apply_effect ms1 (mkEffect a1 [] [(a1, n1)])).

(* [comment removed for export] *)
Hypothesis Hrefuse1 : forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 ms1 (errno_ret e))) model.
Hypothesis Hex1 : exists a, grant_ok_nr (ms_gpr ms1 0) model a nZ1 = true.

(* [comment removed for export] *)
Variable ms2 : word -> machine_state.
Variable accs1 : word -> list (word * nat).
Hypothesis Hwalk1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  msteps_acc segs (post1 a1) (ms2 a1) (accs1 a1).
Hypothesis Hout1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  accesses_outside_lazy (accs1 a1) (m_vm_lazy (model1 a1)).

(* [comment removed for export] *)
Variable x8b : word.
Hypothesis Hno2 : bv_unsigned x8b = 222%Z.
Hypothesis Hsvc2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  ms_svc_pending (ms2 a1) = Some x8b.
Hypothesis Hargs2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  mmap_args_ok (ms2 a1).

Let nZ2 (a1 : word) : Z := page_round_up_Z (bv_unsigned (ms_gpr (ms2 a1) 1)).
Let n2 (a1 : word) : word := page_round_up (ms_gpr (ms2 a1) 1).
Let model2 (a1 a2 : word) : Model := mmap_model a2 (n2 a1) (model1 a1).
Let post2 (a1 a2 : word) : machine_state :=
  advance_past_svc (apply_effect (ms2 a1) (mkEffect a2 [] [(a2, n2 a1)])).

(* [comment removed for export] *)
Hypothesis Hrefuse2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  forall e, In e mmap_errnos ->
  to_spin segs (advance_past_svc (set_gpr0 (ms2 a1) (errno_ret e))) (model1 a1).
Hypothesis Hex2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  exists a2, grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true.

(* [comment removed for export] *)
Variable ms3 : word -> word -> machine_state.
Variable accs2 : word -> word -> list (word * nat).
Hypothesis Hwalk2 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  msteps_acc segs (post2 a1 a2) (ms3 a1 a2) (accs2 a1 a2).
Hypothesis Hout2 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  accesses_outside_lazy (accs2 a1 a2) (m_vm_lazy (model2 a1 a2)).

(* [comment removed for export] *)
Variable buf : list byte.
Hypothesis Hbufnb : (1 <= length buf)%nat.
Hypothesis Hbufmod : buf_modeled buf.
Variable x8c : word.
Hypothesis Hno3 : bv_unsigned x8c = 64%Z.
Hypothesis Hw_svc : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_svc_pending (ms3 a1 a2) = Some x8c.
Hypothesis Hw_fd1 : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_gpr (ms3 a1 a2) 0 = Z_to_bv 64 1.
Hypothesis Hw_read : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  ms_read_bytes (ms3 a1 a2) (ms_gpr (ms3 a1 a2) 1) (ms_gpr (ms3 a1 a2) 2) = Some buf.
Hypothesis Hw_out : forall a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  accesses_outside_lazy [(ms_gpr (ms3 a1 a2) 1, length buf)]
    (m_vm_lazy (model2 a1 a2)).

(* [comment removed for export] *)
Variable msE : word -> word -> nat -> machine_state.
Variable accs3 : word -> word -> nat -> list (word * nat).
Hypothesis Hwalk3 : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  msteps_acc segs
    (advance_past_svc (set_gpr0 (ms3 a1 a2) (len_word (firstn n buf))))
    (msE a1 a2 n) (accs3 a1 a2 n).
Hypothesis Hout3 : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  accesses_outside_lazy (accs3 a1 a2 n) (m_vm_lazy (model2 a1 a2)).

(* [comment removed for export] *)
Variables (x8d : word) (cs : word).
Hypothesis HE_no : is_exit_no x8d.
Hypothesis HE_svc : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  ms_svc_pending (msE a1 a2 n) = Some x8d.
Hypothesis HE_code : forall a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
  grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  bv_and (ms_gpr (msE a1 a2 n) 0) (Z_to_bv 64 255) = cs.




End AsanInitReal.
End WithFP2.
End NoReserve.
Module ShapeRetry.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg DivergeSim SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition silent_into (X : config -> Prop) (c : config) : Prop :=
  (exists e st, sstep_cfg segs CfgStep.kit_cfg c e st)
  /\ (forall e st, sstep_cfg segs CfgStep.kit_cfg c e st -> e = [] /\ exists c', st = SNext c' /\ X c').



(* [comment removed for export] *)
Definition trap (R : config -> Prop) : Prop := forall c, R c -> silent_into R c.



Lemma trap_star : forall R, trap R -> forall c tr c', star_cfg segs CfgStep.kit_cfg c tr c' -> R c -> tr = [] /\ R c'.
Proof.
  intros R HR c tr c' Hstar.
  induction Hstar as [c | c evs c2 tr c3 Hstep Hstar IH]; intros Hc.
  - auto.
  - destruct (proj2 (HR c Hc) evs _ Hstep) as (-> & c2' & Heq & Hc2). injection Heq as <-.
    destruct (IH Hc2) as (-> & Hc3). auto.
Qed.

(* [comment removed for export] *)
Inductive prog (P Q : config -> Prop) : bool -> config -> Prop :=
| pg_done : forall c, Q c -> prog P Q true c
| pg_step : forall c,
    (exists e st, sstep_cfg segs CfgStep.kit_cfg c e st) ->
    (forall e st, sstep_cfg segs CfgStep.kit_cfg c e st -> e = [] /\ st <> SError) ->
    (forall e c', sstep_cfg segs CfgStep.kit_cfg c e (SNext c') -> prog P Q false c') ->
    prog P Q true c
| pg_head : forall c, P c -> prog P Q false c
| pg_lift : forall c, prog P Q true c -> prog P Q false c.

Definition progress (P Q : config -> Prop) : config -> Prop := prog P Q true.
Definition progress_or (P Q : config -> Prop) : config -> Prop := prog P Q false.






Lemma progress_cases : forall (P Q : config -> Prop) c,
  progress P Q c -> Q c \/ silent_into (progress_or P Q) c.
Proof.
  intros P Q c H. unfold progress in H.
  remember true as b eqn:Eb. destruct H as [c Hq | c Hex Hall Hnx | c Hp | c H']; try discriminate Eb.
  - left. exact Hq.
  - right. split; [exact Hex|]. intros e st Hss. destruct (Hall e st Hss) as [-> Hne].
    split; [reflexivity|]. destruct st as [c'|]; [| exfalso; apply Hne; reflexivity].
    exists c'. split; [reflexivity | exact (Hnx _ c' Hss)].
Qed.




(* [comment removed for export] *)
Lemma progress_of_or : forall (P Q : config -> Prop),
  (forall d, P d -> progress P Q d) ->
  forall c, progress_or P Q c -> progress P Q c.
Proof.
  intros P Q HP c H. unfold progress_or in H.
  remember false as b eqn:Eb. destruct H as [c Hq | c Hex Hall Hnx | c Hp | c H']; try discriminate Eb.
  - apply HP. exact Hp.
  - exact H'.
Qed.



(* [comment removed for export] *)
Definition reaches (Q : config -> Prop) (c : config) : Prop :=
  exists c', star_cfg segs CfgStep.kit_cfg c [] c' /\ Q c'.











(* [comment removed for export] *)

Inductive rrealizes : config -> TSet -> Prop :=
| rrz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (forall i, rrealizes (nx i) (T i)) ->
    rrealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rrz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rrealizes c t_nil
| rrz_diverge : forall (R : config -> Prop) c,
    trap R -> R c ->
    rrealizes c t_nil
| rrz_retry : forall (P Q : config -> Prop) c T,
    progress P Q c ->
    (forall d, P d -> progress P Q d) ->
    reaches Q c ->
    (forall d, Q d -> rrealizes d T) ->
    rrealizes c T
| rrz_conseq : forall c T T',
    rrealizes c T -> t_eq T T' -> rrealizes c T'.

(* [comment removed for export] *)

Lemma rrealizes_of_realizes : forall c T, realizes segs c T -> rrealizes c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (rrz_node c I evs nx T i0 Hnode IH).
  - exact (rrz_halt c Hh).
  - exact (rrz_conseq c T T' IH Heq).
Qed.






(* [comment removed for export] *)

Lemma rrealizes_nonempty : forall c T, rrealizes c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | R c HR Hc
                   | P Q c T Hpg HP Hlive HQ IH | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - destruct Hlive as (d & _ & Hd). exact (IH d Hd).
  - apply Heq. exact IH.
Qed.

Lemma rrealizes_pclosed : forall c T, rrealizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | R c HR Hc
                   | P Q c T Hpg HP Hlive HQ IH | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - destruct Hlive as (d & _ & Hd). eapply (IH d Hd); eassumption.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

Lemma rrealizes_star_only : forall c T, rrealizes c T ->
  forall tr c', star_cfg segs CfgStep.kit_cfg c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | R c HR Hc
                   | P Q c T Hpg HP Hlive HQ IH | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2.
      split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct (trap_star R HR c tr c' Hstar Hc) as [-> _]. reflexivity.
  - (* [comment removed for export] *)
    assert (HT0 : T []).
    { destruct Hlive as (d & _ & Hd). eapply rrealizes_nonempty. exact (HQ d Hd). }
    clear Hlive. revert Hpg. induction Hstar as [c0 | c0 e c2 tr2 c3 Hss Hstar2 IH2]; intros Hpg.
    + exact HT0.
    + destruct (progress_cases P Q c0 Hpg) as [Hq | [_ Hall]].
      * eapply (IH c0 Hq). eapply star_cfg_step; eassumption.
      * destruct (Hall e (SNext c2) Hss) as (-> & c2' & Heq & Hc2). injection Heq as <-.
        cbn [app]. apply IH2. eapply progress_of_or; [exact HP | exact Hc2].
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs CfgStep.kit_cfg c1 t1 c2 -> star_cfg segs CfgStep.kit_cfg c2 t2 c3 -> star_cfg segs CfgStep.kit_cfg c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1; revert t2 c3.
  induction H1 as [c | c1 evs c2 tr c3 Hs Hst IH]; intros t2 c4 H2; [exact H2 |].
  rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | apply IH; exact H2].
Qed.

Lemma obs_trace_after_silent : forall c c' tr,
  star_cfg segs CfgStep.kit_cfg c [] c' -> obs_trace_cfg segs CfgStep.kit_cfg c' tr -> obs_trace_cfg segs CfgStep.kit_cfg c tr.
Proof.
  intros c c' tr Hstar (tr' & c'' & Hstar' & Hp).
  exists tr', c''. split; [| exact Hp].
  change tr' with ([] ++ tr'). eapply star_cfg_trans; eassumption.
Qed.

Lemma rrealizes_admits : forall c T, rrealizes c T ->
  forall tr, T tr -> obs_trace_cfg segs CfgStep.kit_cfg c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | R c HR Hc
                   | P Q c T Hpg HP Hlive HQ IH | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - destruct Hlive as (d & Hstar & Hd).
    eapply obs_trace_after_silent; [exact Hstar | apply (IH d Hd); exact HT].
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem rrealizes_obs_iff : forall c T, rrealizes c T ->
  forall tr, obs_trace_cfg segs CfgStep.kit_cfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply rrealizes_pclosed; [exact H | eapply rrealizes_star_only; eauto | exact Hp].
  - apply rrealizes_admits; exact H.
Qed.


(* [comment removed for export] *)
Lemma rrealizes_star_no_sserror : forall c T, rrealizes c T ->
  forall tr c' e, star_cfg segs CfgStep.kit_cfg c tr c' -> ~ sstep_cfg segs CfgStep.kit_cfg c' e SError.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | R c HR Hc
                   | P Q c T Hpg HP Hlive HQ IH | c T T' H IH Heq];
    intros tr c' e' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + intros Hss. destruct Hnode as [_ Hsound].
      destruct (Hsound e' SError Hss) as (i & _ & Hbad). discriminate.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2. eapply IH. exact Hstar2.
  - destruct (star_cfg_halted_nil segs c tr c' Hh Hstar) as [-> ->].
    intros Hss. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - destruct (trap_star R HR c tr c' Hstar Hc) as [_ Hc'].
    intros Hss. destruct (proj2 (HR c' Hc') e' SError Hss) as (_ & d & Hbad & _). discriminate.
  - clear Hlive. revert Hpg. induction Hstar as [c0 | c0 e c2 tr2 c3 Hss Hstar2 IH2]; intros Hpg.
    + destruct (progress_cases P Q c0 Hpg) as [Hq | [_ Hall]].
      * apply (IH c0 Hq [] c0 e'). apply star_cfg_refl.
      * intros Hss. destruct (Hall e' SError Hss) as (_ & d & Hbad & _). discriminate.
    + destruct (progress_cases P Q c0 Hpg) as [Hq | [_ Hall]].
      * apply (IH c0 Hq (e ++ tr2) c3 e'). eapply star_cfg_step; eassumption.
      * destruct (Hall e (SNext c2) Hss) as (-> & c2' & Heq & Hc2). injection Heq as <-.
        apply IH2. eapply progress_of_or; [exact HP | exact Hc2].
  - eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)
Theorem rrealizes_no_error : forall c T,
  rrealizes c T -> ~ reaches_error_cfg segs CfgStep.kit_cfg c.
Proof.
  intros c T H (tr & c' & e & Hstar & Hss).
  exact (rrealizes_star_no_sserror c T H tr c' e Hstar Hss).
Qed.














End WithSegs.


(* [comment removed for export] *)
Theorem shape_strong_equiv_rr :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  rrealizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  rrealizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg CfgStep.kit_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg CfgStep.kit_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg CfgStep.kit_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg CfgStep.kit_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split; [| split].
  - cbn. eapply rrealizes_no_error; exact Hsource.
  - cbn. eapply rrealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (rrealizes_obs_iff source_segs _ T Hsource tr).
    rewrite (rrealizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
Qed.


(* [comment removed for export] *)
Lemma rrealizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  rrealizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg CfgStep.kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply rrealizes_no_error; eassumption. Qed.

Lemma rrealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  rrealizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg CfgStep.kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply rrealizes_obs_iff. assumption. Qed.







End ShapeRetry.
Module ShapeRel.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg DivergeSim SpinAlg ShapeRetry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Record shape_rel := SR {
  sr_rel :> config -> TSet -> Prop;
  sr_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
      node_ok segs c I evs nx -> (forall i, sr_rel (nx i) (T i)) ->
      sr_rel c (t_alt (fun i => t_emit (evs i) (T i)));
  sr_halt : forall c, m_halted (cfg_model c) <> None -> sr_rel c t_nil;
  sr_conseq : forall c T T', sr_rel c T -> t_eq T T' -> sr_rel c T';
  sr_nonempty : forall c T, sr_rel c T -> T [];
  sr_embed : forall c T, realizes segs c T -> sr_rel c T
}.

(* [comment removed for export] *)
Definition SR_realizes : shape_rel :=
  SR (realizes segs) (rz_node segs) (rz_halt segs) (rz_conseq segs) (realizes_nonempty segs) (fun c T H => H).



(* [comment removed for export] *)
Variable R : shape_rel.

Lemma sr_silent_node : forall c (I : Type) (i0 : I) (nx : I -> config) T,
  node_ok segs c I (fun _ => []) nx ->
  (forall i, R (nx i) T) -> R c T.
Proof.
  intros c I i0 nx T Hnode Hc.
  apply (sr_conseq R c (t_alt (fun _ : I => t_emit [] T))).
  - apply (sr_node R c I (fun _ => []) nx (fun _ => T) i0 Hnode Hc).
  - assert (HT : T []) by (eapply (sr_nonempty R); exact (Hc i0)).
    intros tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT tr) Hi).
    + intros Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT tr) Htr).
Qed.

Lemma sr_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') -> R c' T -> R c T.
Proof. intros c c' T Hnode Hc. apply (sr_silent_node c unit tt (fun _ => c') T Hnode). intros []; exact Hc. Qed.


Lemma sr_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, R (nx i) (T i)) -> R c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (sr_conseq R c (t_alt (fun i => t_emit [] (T i)))).
  - apply (sr_node R c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i. exact (proj1 (t_emit_nil_eq (T i) (sr_nonempty R _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i. exact (proj2 (t_emit_nil_eq (T i) (sr_nonempty R _ _ (Hc i)) tr) Hi).
Qed.

Lemma sr_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet) (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, R (nx (inl i)) A) -> (forall i, R (nx (inr i)) B) ->
  R c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  apply (sr_conseq R c (t_alt (fun i : IA + IB => match i with inl _ => A | inr _ => B end))).
  - apply (sr_cases c (IA + IB) nx _ (inl a0) Hnode). intros [i|i]; [apply HA | apply HB].
  - intros tr. unfold t_alt2, t_alt. split.
    + intros [[i|i] H]; [left | right]; exact H.
    + intros [H | H]; [exists (inl a0) | exists (inr b0)]; exact H.
Qed.

Lemma sr_step : forall ms model ms' T,
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  R (mkCfg ms' model) T -> R (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply sr_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma sr_msteps : forall ms ms' model T,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  R (mkCfg ms' model) T -> R (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
  eapply sr_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

Lemma sr_exit : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  R (mkCfg ms model) (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros. apply (sr_embed R). eapply rz_exit; eassumption. Qed.

Lemma sr_of_realizes : forall c T, realizes segs c T -> R c T.
Proof. exact (sr_embed R). Qed.


End WithSegs.
End ShapeRel.
Module ShapeRoot.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg DivergeSim SpinAlg ShapeRetry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition valid_input_core (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_va_size inp = Sv48.

Lemma valid_input_core_of_valid_input : forall inp,
  valid_input inp -> valid_input_core inp.
Proof. intros inp H. unfold valid_input in H. unfold valid_input_core. tauto. Qed.

Lemma valid_input_core_of_valid_input_abort : forall inp,
  valid_input_abort inp -> valid_input_core inp.
Proof. intros inp H. unfold valid_input_abort in H. unfold valid_input_core. tauto. Qed.

Lemma valid_input_core_va_size : forall inp,
  valid_input_core inp -> in_va_size inp = Sv48.
Proof. intros inp H. unfold valid_input_core in H. tauto. Qed.


(* [comment removed for export] *)
Definition root_obligation_core (img : Image) (lim : Z) (S : ProcInput -> TSet) : Prop :=
  forall sp brk0 mb rnd inp,
    valid_entry img (mkEntry sp brk0 mb rnd) inp ->
    valid_input_core inp ->
    rrealizes (img_segments img)
      (init_config (img_segments img) (img_init_pc img) (img_phdrs img) sp brk0 mb rnd lim inp)
      (S inp).



Lemma root_obligation_core_of_realizes : forall img lim S,
  (forall sp brk0 mb rnd inp,
     valid_entry img (mkEntry sp brk0 mb rnd) inp -> valid_input_core inp ->
     realizes (img_segments img)
       (init_config (img_segments img) (img_init_pc img) (img_phdrs img) sp brk0 mb rnd lim inp)
       (S inp)) ->
  root_obligation_core img lim S.
Proof. intros img lim S H sp brk0 mb rnd inp He Hi. apply rrealizes_of_realizes. apply H; assumption. Qed.


(* [comment removed for export] *)
Definition kill_free (S : ProcInput -> TSet) : Prop :=
  forall inp tr sig fs, valid_input_core inp -> S inp tr -> ~ In (KillEv sig fs) tr.

Lemma rrealizes_not_dies : forall ssegs spc sph sp brk0 mb rnd lim inp (T : TSet),
  rrealizes ssegs (init_config ssegs spc sph sp brk0 mb rnd lim inp) T ->
  (forall tr sig fs, T tr -> ~ In (KillEv sig fs) tr) ->
  ~ dies_by_signal (run_scfg CfgStep.kit_cfg (mkImage ssegs spc sph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros ssegs spc sph sp brk0 mb rnd lim inp T Hrz Hkf (tr & sig & fs & Htr & Hin).
  cbn in Htr. rewrite (rrealizes_obs_iff ssegs _ T Hrz tr) in Htr.
  exact (Hkf tr sig fs Htr Hin).
Qed.

(* [comment removed for export] *)
Theorem rrealizes_universal_ef_budgets_abort :
  forall (lim_s lim_t : Z) (src tgt : Image) (S : ProcInput -> TSet),
  root_obligation_core src lim_s S ->
  root_obligation_core tgt lim_t S ->
  kill_free S ->
  strong_universal_error_free_T_scfg_budgets_abort CfgStep.kit_cfg lim_s lim_t src tgt.
Proof.
  intros lim_s lim_t [ssegs spc sph] [tsegs tpc tph] S Hsrc Htgt Hkf.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hve_s Hve_t Hvi _.
  pose proof (valid_input_core_of_valid_input_abort _ Hvi) as Hci.
  pose proof (Hsrc rsp rbrk rmb rrnd inp Hve_s Hci) as RS.
  pose proof (Htgt asp abrk amb arnd inp Hve_t Hci) as RT.
  destruct (shape_strong_equiv_rr ssegs spc sph rsp rbrk rmb rrnd lim_s
              tsegs tpc tph asp abrk amb arnd lim_t (S inp) inp RS RT) as (EFs & EFt & TE).
  unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled.
  repeat split.
  - exact EFs.
  - eapply rrealizes_not_dies; [exact RS | intros tr sig fs; apply (Hkf inp); exact Hci].
  - exact EFt.
  - eapply rrealizes_not_dies; [exact RT | intros tr sig fs; apply (Hkf inp); exact Hci].
  - apply TE.
  - apply TE.
Qed.

End ShapeRoot.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit LinuxProcessSemantics.EquivalenceDefinition.FinInput LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module ShapeRows.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.MustExit LinuxProcessSemantics.EquivalenceDefinition.FinInput LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg DivergeSim SpinAlg ShapeRetry ShapeRoot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

Section OneImage.
Variables (X : Image) (lim : Z) (S : ProcInput -> TSet).
Hypothesis HX : root_obligation_core X lim S.

(* [comment removed for export] *)
Lemma root_traces_iff : forall en inp tr,
  valid_input_core inp -> valid_entry X en inp ->
  (bh_traces (run_scfg CfgStep.kit_cfg X lim en inp) tr <-> S inp tr).
Proof.
  destruct X as [segs pc ph]. intros [sp brk0 mb rnd] inp tr Hci Hen.
  apply rrealizes_traces_iff. exact (HX sp brk0 mb rnd inp Hen Hci).
Qed.

Lemma root_error_free : forall en inp,
  valid_input_core inp -> valid_entry X en inp -> error_free (run_scfg CfgStep.kit_cfg X lim en inp).
Proof.
  destruct X as [segs pc ph]. intros [sp brk0 mb rnd] inp Hci Hen.
  eapply rrealizes_error_free. exact (HX sp brk0 mb rnd inp Hen Hci).
Qed.

Lemma root_no_errors : forall inp, valid_input_core inp ->
  ~ (exists en, valid_entry X en inp /\ bh_errors (run_scfg CfgStep.kit_cfg X lim en inp)).
Proof. intros inp Hci (en & Hen & He). exact (root_error_free en inp Hci Hen He). Qed.

Lemma root_no_all_errors : forall inp, valid_input_core inp ->
  ~ (exists en, valid_entry X en inp /\ bh_all_errors (run_scfg CfgStep.kit_cfg X lim en inp)).
Proof.
  intros inp Hci (en & Hen & He).
  exact (root_error_free en inp Hci Hen (run_scfg_all_errors_errors _ _ _ _ _ He)).
Qed.

Lemma root_no_unmodeled : forall inp, valid_input_core inp ->
  ~ (exists en, valid_entry X en inp /\ bh_unmodeled (run_scfg CfgStep.kit_cfg X lim en inp)).
Proof.
  intros inp Hci (en & Hen & He).
  exact (root_error_free en inp Hci Hen (run_scfg_unmodeled_errors _ _ _ _ _ He)).
Qed.

End OneImage.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma root_trace_equiv : forall (X Y : Image) (limX limY : Z) (S : ProcInput -> TSet),
  root_obligation_core X limX S -> root_obligation_core Y limY S ->
  forall inp enX enY, valid_input_core inp ->
    valid_entry X enX inp -> valid_entry Y enY inp ->
    trace_equiv (bh_traces (run_scfg CfgStep.kit_cfg X limX enX inp)) (bh_traces (run_scfg CfgStep.kit_cfg Y limY enY inp)).
Proof.
  intros X Y limX limY S HX HY inp enX enY Hci HenX HenY tr.
  rewrite (root_traces_iff X limX S HX enX inp tr Hci HenX).
  rewrite (root_traces_iff Y limY S HY enY inp tr Hci HenY).
  reflexivity.
Qed.

(* [comment removed for export] *)
Theorem root_agree_core : forall (X Y : Image) (lim : Z) (S : ProcInput -> TSet),
  root_obligation_core X lim S -> root_obligation_core Y lim S ->
  forall inp, valid_input_core inp -> agree_s CfgStep.kit_cfg X Y lim inp.
Proof.
  intros X Y lim S HX HY inp Hci. unfold agree_s.
  split; [| split; [| split]].
  - intros enX enY HenX HenY. exact (root_trace_equiv X Y lim lim S HX HY inp enX enY Hci HenX HenY).
  - split; intros H; exfalso;
      [exact (root_no_errors X lim S HX inp Hci H) | exact (root_no_errors Y lim S HY inp Hci H)].
  - split; intros H; exfalso;
      [exact (root_no_all_errors X lim S HX inp Hci H) | exact (root_no_all_errors Y lim S HY inp Hci H)].
  - split; intros H; exfalso;
      [exact (root_no_unmodeled X lim S HX inp Hci H) | exact (root_no_unmodeled Y lim S HY inp Hci H)].
Qed.

Theorem root_agree : forall (X Y : Image) (lim : Z) (S : ProcInput -> TSet),
  root_obligation_core X lim S -> root_obligation_core Y lim S ->
  forall inp, valid_input inp -> agree_s CfgStep.kit_cfg X Y lim inp.
Proof.
  intros X Y lim S HX HY inp Hi.
  exact (root_agree_core X Y lim S HX HY inp (valid_input_core_of_valid_input _ Hi)).
Qed.


(* [comment removed for export] *)
Theorem root_good_input_core : forall (O1 O2 : Image) (S : ProcInput -> TSet),
  root_obligation_core O1 source_alloc_limit S ->
  root_obligation_core O2 target_alloc_limit S ->
  forall inp, valid_input_core inp -> good_input_s CfgStep.kit_cfg O1 O2 inp.
Proof.
  intros O1 O2 S H1 H2 inp Hci en1 en2 Hen1 Hen2.
  unfold strong_equiv_error_free_scfg. split; [| split].
  - exact (root_error_free O1 _ S H1 en1 inp Hci Hen1).
  - exact (root_error_free O2 _ S H2 en2 inp Hci Hen2).
  - exact (root_trace_equiv O1 O2 _ _ S H1 H2 inp en1 en2 Hci Hen1 Hen2).
Qed.

Theorem root_good_input : forall (O1 O2 : Image) (S : ProcInput -> TSet),
  root_obligation_core O1 source_alloc_limit S ->
  root_obligation_core O2 target_alloc_limit S ->
  forall inp, valid_input inp -> good_input_s CfgStep.kit_cfg O1 O2 inp.
Proof.
  intros O1 O2 S H1 H2 inp Hi.
  exact (root_good_input_core O1 O2 S H1 H2 inp (valid_input_core_of_valid_input _ Hi)).
Qed.

(* [comment removed for export] *)
Corollary root_agree_s : forall (X Y : Image) (lim : Z) (S : ProcInput -> TSet),
  root_obligation_core X lim S -> root_obligation_core Y lim S ->
  forall inp, valid_input inp -> agree_s CfgStep.kit_cfg X Y lim inp.
Proof.
  intros X Y lim S HX HY inp Hi.
  exact (root_agree X Y lim S HX HY inp Hi).
Qed.

Corollary root_good_input_s : forall (O1 O2 : Image) (S : ProcInput -> TSet),
  root_obligation_core O1 source_alloc_limit S ->
  root_obligation_core O2 target_alloc_limit S ->
  forall inp, valid_input inp -> good_input_s CfgStep.kit_cfg O1 O2 inp.
Proof.
  intros O1 O2 S H1 H2 inp Hi.
  exact (root_good_input O1 O2 S H1 H2 inp Hi).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition accepts_all (C : Image) : Prop :=
  forall f : FinProcInput, valid_fin_input f ->
  forall en, valid_entry C en (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f).


Lemma decides_fo_accept_all : forall (C : Image) (spec : ProcInput -> Prop),
  accepts_all C ->
  (forall f : FinProcInput, valid_fin_input f -> spec (to_proc_input f)) ->
  decides_fo C spec.
Proof.
  intros C spec Hacc Hspec f Hf en Hen.
  pose proof (Hacc f Hf en Hen) as Ha. pose proof (Hspec f Hf) as Hs.
  split; [split; intros _; assumption | left; exact Ha].
Qed.

(* [comment removed for export] *)
Lemma accepts_all_of_must_exit : forall segs pc ph,
  (forall inp sp brk mbase rdraw,
     valid_input inp -> valid_entry (mkImage segs pc ph) (mkEntry sp brk mbase rdraw) inp ->
     must_exit_at_cfg forced_only_cfg segs verdict_accept
       (init_config segs pc ph sp brk mbase rdraw classifier_alloc_limit inp)) ->
  accepts_all (mkImage segs pc ph).
Proof.
  intros segs pc ph H f Hf [sp brk mbase rdraw] Hen.
  cbn [must_exit_with_scfg]. apply H; [exact Hf | exact Hen].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem rows_ca_iff : forall (O1 O2 C : Image) (S : ProcInput -> TSet),
  root_obligation_core O1 source_alloc_limit S ->
  root_obligation_core O2 target_alloc_limit S ->
  accepts_all C ->
  classifies_good_inputs_T_s CfgStep.kit_cfg O1 O2 C.
Proof.
  intros O1 O2 C S H1 H2 Hacc. unfold classifies_good_inputs_T_s.
  apply decides_fo_accept_all; [exact Hacc |].
  intros f Hf. exact (root_good_input_s O1 O2 S H1 H2 (to_proc_input f) Hf).
Qed.

(* [comment removed for export] *)
Theorem rows_cb_iff : forall (O1 P1 O2 P2 C : Image) (S : ProcInput -> TSet),
  root_obligation_core O1 source_alloc_limit S ->
  root_obligation_core P1 source_alloc_limit S ->
  root_obligation_core O2 target_alloc_limit S ->
  root_obligation_core P2 target_alloc_limit S ->
  accepts_all C ->
  classifies_patch_diff_T_s CfgStep.kit_cfg O1 P1 O2 P2 C.
Proof.
  intros O1 P1 O2 P2 C S HO1 HP1 HO2 HP2 Hacc. unfold classifies_patch_diff_T_s.
  apply decides_fo_accept_all; [exact Hacc |].
  intros f Hf. split.
  - exact (root_agree_s O1 P1 _ S HO1 HP1 (to_proc_input f) Hf).
  - exact (root_agree_s O2 P2 _ S HO2 HP2 (to_proc_input f) Hf).
Qed.
End ShapeRows.
Module GlzArith.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.Lists.List.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma magic_div_floor : forall x d m S e,
  0 < d -> 0 <= x -> 0 <= S ->
  m * d = 2 ^ S + e -> 0 <= e -> x * e < 2 ^ S ->
  (x * m) / 2 ^ S = x / d.
Proof.
  intros x d m S e Hd Hx HS Hm He Hxe.
  set (P := 2 ^ S) in *.
  assert (HP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; lia).
  set (q0 := x / d). set (r0 := x mod d).
  assert (Hxd : x = d * q0 + r0) by (subst q0 r0; apply Z.div_mod; lia).
  assert (Hr0 : 0 <= r0 < d) by (subst r0; apply Z.mod_pos_bound; lia).
  assert (Hq0 : 0 <= q0) by (subst q0; apply Z.div_pos; lia).
  (* [comment removed for export] *)
  assert (Hdecomp : x * m = q0 * P + (q0 * e + r0 * m)) by nia.
  assert (Hm0 : 0 <= m) by nia.
  assert (Hlow : 0 <= q0 * e + r0 * m) by nia.
  assert (Hhigh : q0 * e + r0 * m < P).
  { (* [comment removed for export] *)
    assert (Hmul : d * (q0 * e + r0 * m) = e * x + r0 * P) by nia.
    assert (Hlt : d * (q0 * e + r0 * m) < d * P) by nia.
    nia. }
  rewrite Hdecomp. rewrite Z.add_comm, Z.mul_comm. rewrite Z.div_add; [|lia].
  rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma div_bounds : forall x lo hi d, 0 < d -> lo <= x <= hi -> lo / d <= x / d <= hi / d.
Proof. intros x lo hi d Hd [H1 H2]. split; apply Z.div_le_mono; lia. Qed.

(* [comment removed for export] *)
Lemma rem_bounds : forall x d, 0 < d -> 0 <= x - d * (x / d) <= d - 1.
Proof.
  intros x d Hd. pose proof (Z.div_mod x d ltac:(lia)) as H. pose proof (Z.mod_pos_bound x d Hd). lia.
Qed.

(* [comment removed for export] *)
Lemma magic_div_facts : forall x d m S e lo hi Q,
  0 < d -> 0 <= lo -> lo <= x <= hi -> 0 <= S ->
  m * d = 2 ^ S + e -> 0 <= e -> hi * e < 2 ^ S ->
  Q = (x * m) / 2 ^ S ->
  Q = x / d /\ lo / d <= Q <= hi / d /\ 0 <= x - d * Q <= d - 1.
Proof.
  intros x d m S e lo hi Q Hd Hlo Hx HS Hm He Hhe HQ.
  assert (HQ' : Q = x / d).
  { rewrite HQ. apply (magic_div_floor x d m S e); try lia. nia. }
  split; [exact HQ'|]. rewrite HQ'. split; [apply div_bounds; lia | apply rem_bounds; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint enum_mm (f : Z -> option Z) (k : Z) (cnt : nat) (mn mx : Z) {struct cnt} : option (Z * Z) :=
  match cnt with
  | O => Some (mn, mx)
  | S c =>
      match f k with
      | Some v => enum_mm f (k + 1) c (Z.min mn v) (Z.max mx v)
      | None => None
      end
  end.

Lemma enum_mm_acc : forall f cnt k mn mx mn' mx',
  enum_mm f k cnt mn mx = Some (mn', mx') -> mn' <= mn /\ mx <= mx'.
Proof.
  intros f cnt. induction cnt as [|c IH]; intros k mn mx mn' mx' H; cbn [enum_mm] in H.
  - injection H as <- <-. lia.
  - destruct (f k) as [v|]; [|discriminate].
    destruct (IH _ _ _ _ _ H) as [A B]. lia.
Qed.

(* [comment removed for export] *)
Lemma enum_mm_spec : forall f cnt k mn mx mn' mx',
  enum_mm f k cnt mn mx = Some (mn', mx') ->
  forall j, k <= j < k + Z.of_nat cnt -> exists v, f j = Some v /\ mn' <= v <= mx'.
Proof.
  intros f cnt. induction cnt as [|c IH]; intros k mn mx mn' mx' H j Hj; cbn [enum_mm] in H.
  - exfalso. cbn in Hj. lia.
  - destruct (f k) as [v|] eqn:Hf; [|discriminate].
    destruct (Z.eq_dec j k) as [->|Hne].
    + exists v. split; [exact Hf|]. destruct (enum_mm_acc _ _ _ _ _ _ _ H). lia.
    + apply (IH (k + 1) (Z.min mn v) (Z.max mx v) mn' mx' H). rewrite Nat2Z.inj_succ in Hj. lia.
Qed.

(* [comment removed for export] *)
Definition enum_minmax (f : Z -> option Z) (lo hi : Z) : option (Z * Z) :=
  if Z.ltb hi lo then None else
  match f lo with
  | Some v0 => enum_mm f (lo + 1) (Z.to_nat (hi - lo)) v0 v0
  | None => None
  end.

Lemma enum_minmax_spec : forall f lo hi mn mx,
  enum_minmax f lo hi = Some (mn, mx) ->
  forall j, lo <= j <= hi -> exists v, f j = Some v /\ mn <= v <= mx.
Proof.
  intros f lo hi mn mx H j Hj. unfold enum_minmax in H.
  destruct (Z.ltb hi lo) eqn:Hlt; [discriminate|]. apply Z.ltb_ge in Hlt.
  destruct (f lo) as [v0|] eqn:Hf0; [|discriminate].
  destruct (Z.eq_dec j lo) as [->|Hne].
  - exists v0. split; [exact Hf0|]. destruct (enum_mm_acc _ _ _ _ _ _ _ H). lia.
  - apply (enum_mm_spec f _ _ _ _ _ _ H). rewrite Z2Nat.id by lia. lia.
Qed.
End GlzArith.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Spec4KF.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg ShapeRetry ShapeRoot OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition kf (T : TSet) : Prop := forall tr sig fs, T tr -> ~ In (KillEv sig fs) tr.

Lemma is_prefix_In {A} : forall (l m : list A) x, is_prefix l m -> In x l -> In x m.
Proof.
  induction l as [|a l IH]; intros m x Hp Hin; [destruct Hin|].
  destruct m as [|b m]; [destruct Hp|]. destruct Hp as [-> Hp].
  destruct Hin as [-> | Hin]; [left; reflexivity | right; eapply IH; eauto].
Qed.

Lemma kf_nil : kf t_nil.
Proof. intros tr sig fs H. unfold t_nil in H. subst tr. intros []. Qed.

Lemma kf_emit : forall evs T,
  (forall sig fs, ~ In (KillEv sig fs) evs) -> kf T -> kf (t_emit evs T).
Proof.
  intros evs T Hevs HT tr sig fs [Hp | (tr' & -> & Htr')] Hin.
  - exact (Hevs sig fs (is_prefix_In _ _ _ Hp Hin)).
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [exact (Hevs sig fs Hin) | exact (HT _ _ _ Htr' Hin)].
Qed.

Lemma kf_alt2 : forall A B, kf A -> kf B -> kf (t_alt2 A B).
Proof. intros A B HA HB tr sig fs [H|H]; [eapply HA | eapply HB]; eauto. Qed.

Lemma W_no_kill : forall ch s sig fs, ~ In (KillEv sig fs) (W ch s).
Proof.
  intros ch s sig fs Hin. unfold W in Hin. apply in_map_iff in Hin.
  destruct Hin as (b & Hb & _). discriminate Hb.
Qed.

Lemma kf_exit : forall code fs, kf (t_exit code fs).
Proof.
  intros code fs. unfold t_exit. apply kf_emit; [| exact kf_nil].
  intros sig fs' [H | []]. discriminate H.
Qed.

Lemma kf_die : forall msg fs, kf (t_die msg fs).
Proof. intros. unfold t_die. apply kf_emit; [apply W_no_kill | apply kf_exit]. Qed.

Lemma kf_success : forall calls fs, kf (t_success calls fs).
Proof. intros. unfold t_success. apply kf_emit; [apply W_no_kill | apply kf_exit]. Qed.

Lemma kf_payload : forall cm pl calls fs, kf (t_payload cm pl calls fs).
Proof. intros. unfold t_payload. apply kf_success. Qed.

Lemma kf_body : forall data fs, kf (t_body data fs).
Proof.
  intros. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply kf_die|].
  destruct (Z.of_nat (length data) <? 6)%Z; [apply kf_die|].
  destruct (Z.of_nat (length data) <? 6 + hdr_cfglen data)%Z; [apply kf_die|].
  apply kf_payload.
Qed.

Lemma kf_opened : forall data fs, kf (t_opened data fs).
Proof. intros. unfold t_opened. apply kf_body. Qed.

Lemma kf_opened_dir : forall path fs, kf (t_opened_dir path fs).
Proof. intros. unfold t_opened_dir. apply kf_die. Qed.

Lemma kf_spec : forall argv fs0, kf (spec argv fs0).
Proof.
  intros argv fs0. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply kf_die.
  destruct (4096 <=? length path)%nat; [apply kf_die|].
  destruct (path_eqb path []); [apply kf_die|].
  destruct (path_is_dirref path); [apply kf_alt2; [apply kf_die | apply kf_opened_dir]|].
  destruct (fs_lookup fs0 path); [apply kf_alt2; [apply kf_die | apply kf_opened] | apply kf_die].
Qed.

Theorem spec_of_kill_free : kill_free spec_of.
Proof. intros inp tr sig fs _ H. exact (kf_spec _ _ _ _ _ H). Qed.
End Spec4KF.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg. (* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma node_ok_same : AsVocab.AsanAcct.node_ok segs = StoreOk.ShapeAlg.node_ok segs.
Proof. reflexivity. Qed.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
    AsVocab.AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hr => rz_silent1 segs c c' T Hn Hr.


(* [comment removed for export] *)
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    AsVocab.AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hn Hr => srz_silent1 segs c c' T Hn Hr.


Theorem srz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros A ms msr' model T.
  exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.
