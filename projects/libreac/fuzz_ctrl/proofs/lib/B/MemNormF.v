(* fuzz_ctrl image B: the twin of lib/A/MemNormF.v (same lemma names, on B's Img0 / YK11 / MemNorm), for the
   image-B ProgLift lifts whose callee writes through __asan_memcpy / __asan_memset (decisions.md item 30).
   evtF form of MemNorm.evt_normalize (lib/B/MemNorm.v): a footprint run on the normalized memory moves to the
   memory it normalizes, keeping the caller's footprint RNG and every step's access list. It is not a kit
   transport: the canonical one is the route-2 kit file lib/MemNormCj.v (not in this delivery), evt_rel_MS_cj_F (over
   normalize_cj; a Theorem Labs lane, 2026-10-28). New runs should use that; cite this file only where a run is already
   lifted through evt_normalize and switching it is more than a few lines. It is also not the route-1 lemma
   MemNormP.evtF_normalize_P (plain evt on normalize_P m -> footprint RNG_P). rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

(* ---- A footprint run moves from the normalized memory to the memory it normalizes.

   MemNorm proves this for Lib.Exec.evt (evt_normalize); evtF also carries each step's access list, so the
   transfer has to keep it. It does: the accesses a step reports are computed from the registers and the
   instruction, and both memories serve every byte a load actually reads (mem_rel), so a step on m reports
   exactly the accesses the step on normalize m reports. interp_rel_acc / decode_rel_acc / step_rel_acc are
   MemNorm's interp_rel / decode_rel / step_rel with the access report kept instead of dropped. *)
Lemma wx_ok : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma interp_rel_acc : forall t m m0 r0, mem_rel rsegs m m0 ->
  interp_eff_accesses rsegs t m0 = MachineOk r0 ->
  exists r, interp_eff_accesses rsegs t m = MachineOk r /\
    fst (@access_value _ r) = fst (@access_value _ r0) /\
    mem_rel rsegs (snd (@access_value _ r)) (snd (@access_value _ r0)) /\
    ro_same rsegs m (snd (@access_value _ r)) /\
    @accessed_ranges _ r = @accessed_ranges _ r0.
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m m0 r0 HR H;
    cbn [interp_eff_accesses] in H |- *; try discriminate H.
  - injection H as <-. eexists. split; [reflexivity|]. cbn [access_value accessed_ranges fst snd].
    split; [reflexivity|]. split; [exact HR|]. split; [intros x _; reflexivity|]. reflexivity.
  - rewrite (ov_read_rel rsegs m m0 a (width_bytes n) HR). revert H.
    destruct (ov_read_bytes rsegs m0 a (width_bytes n)) as [bs|]; intros H; cbn beta iota in H |- *;
      [|discriminate H].
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses rsegs ?t m0] => destruct (interp_eff_accesses rsegs t m0) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ m m0 r1 HR E1) as (r & Er & Ef & Erel & Ero & Eacc). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value accessed_ranges].
    split; [exact Ef|]. split; [exact Erel|]. split; [exact Ero|]. rewrite Eacc. reflexivity.
  - revert H. destruct (store_ok rsegs m0 a (width_bytes n)) eqn:Es; intros H; cbn beta iota in H;
      [|discriminate H].
    rewrite (store_ok_rel rsegs m m0 _ a HR Es). cbn beta iota.
    pose proof (store_ok_all_rw rsegs m m0 _ a HR Es) as Hw.
    rewrite <- (length_Z_to_le_bytes (width_bytes n) (bv_unsigned v)) in Hw.
    assert (HR' : mem_rel rsegs (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
                          (write_to_mem m0 a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    { split.
      - exact (write_rw rsegs _ m m0 a (proj1 HR) Hw).
      - intros x b Hx Hb. rewrite (write_ro_same rsegs _ m a x Hw Hx) in Hb. exact (proj2 HR x b Hx Hb). }
    revert H.
    lazymatch goal with
    | |- context [interp_eff_accesses rsegs k (write_to_mem m0 ?x ?y)] =>
        destruct (interp_eff_accesses rsegs k (write_to_mem m0 x y)) as [r1| |] eqn:E1
    end; intros H; cbn beta iota in H; try discriminate H.
    injection H as <-. destruct (IH _ _ r1 HR' E1) as (r & Er & Ef & Erel & Ero & Eacc). rewrite Er.
    eexists. split; [reflexivity|]. cbn [access_value accessed_ranges].
    split; [exact Ef|]. split; [exact Erel|].
    split; [intros x Hx; rewrite (Ero x Hx); exact (write_ro_same rsegs _ m a x Hw Hx)|].
    rewrite Eacc. reflexivity.
Qed.

Lemma decode_rel_acc : forall s s0 w s0' accs, ms_rel rsegs s s0 ->
  decode_exec_accesses rsegs s0 w = MachineOk (@mkAccessReport machine_state s0' accs) ->
  exists s', decode_exec_accesses rsegs s w = MachineOk (@mkAccessReport machine_state s' accs) /\
    ms_rel rsegs s' s0' /\ ro_same rsegs (ms_mem s) (ms_mem s').
Proof.
  intros [R F pc svc rv fc m ro] [R0 F0 pc0 svc0 rv0 fc0 m0 ro0] w s0' accs Hrel.
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in *.
  subst R0 F0 pc0 svc0 rv0 fc0 ro0.
  unfold decode_exec_accesses, ms_reg.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem].
  destruct (is_ecall w).
  - intros H. injection H as <- <-.
    eexists. split; [reflexivity|]. split; [|intros a _; reflexivity].
    refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
    exact HR.
  - destruct (DecodeC.decode_any w) as [[i isz]|].
    + lazymatch goal with
      | |- context [interp_eff_accesses rsegs ?t m0] =>
          destruct (interp_eff_accesses rsegs t m0) as [r0| |] eqn:E
      end; intros H; try discriminate H.
      destruct (interp_rel_acc _ m m0 r0 HR E) as (r & Er & Ef & Erel & Ero & Eacc). rewrite Er.
      destruct r0 as [[c0 m0'] acc0], r as [[c m'] acc].
      cbn [access_value accessed_ranges fst snd] in *. subst c0 acc. injection H as <- <-.
      eexists. split; [reflexivity|]. split; [|exact Ero].
      refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
      exact Erel.
    + destruct (DecodeC.is_defined_illegal w); intros H; discriminate H.
Qed.

Lemma step_rel_acc : forall s s0 s0' accs, ms_rel rsegs s s0 ->
  step_accesses rsegs s0 = MachineOk (@mkAccessReport machine_state s0' accs) ->
  exists s', step_accesses rsegs s = MachineOk (@mkAccessReport machine_state s' accs) /\
    ms_rel rsegs s' s0' /\ ro_same rsegs (ms_mem s) (ms_mem s').
Proof.
  intros s s0 s0' accs Hrel H. pose proof Hrel as (_ & _ & Ep & _ & _ & _ & _ & HR).
  unfold step_accesses, ms_pc in H |- *.
  rewrite Ep, (fetch_word_ov_rel rsegs _ _ wx_ok HR), (fetch_tail_any_rel rsegs _ _ wx_ok HR).
  revert H.
  destruct (fetch_word rsegs (ms_pc_val s0)) as [w|]; [intros H; exact (decode_rel_acc s s0 w s0' accs Hrel H)|].
  destruct (fetch_word_ov rsegs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (decode_rel_acc s s0 w s0' accs Hrel H)|].
  destruct (fetch_tail_any rsegs (ms_mem s0) (ms_pc_val s0)) as [w|];
    [intros H; exact (decode_rel_acc s s0 w s0' accs Hrel H)|].
  destruct (fetch_failure rsegs (ms_mem s0) (ms_pc_val s0)) as [st| |] eqn:Ef.
  - exfalso. exact (fetch_failure_not_ok rsegs _ _ _ Ef).
  - intros H. discriminate H.
  - intros H. discriminate H.
Qed.

Lemma mstepsF_rel_ro : forall (RNG : ExecF.footprint) s0 s0', ExecF.mstepsF rsegs RNG s0 s0' ->
  forall s, ms_rel rsegs s s0 ->
  exists s', ExecF.mstepsF rsegs RNG s s' /\ ms_rel rsegs s' s0' /\ ro_same rsegs (ms_mem s) (ms_mem s').
Proof.
  intros RNG s0 s0' H. induction H as [x|x y z [Hsvc (accs & Ea & Fa)] HT IH]; intros s Hrel.
  - exists s. split; [apply ExecF.mstepsF_refl|]. split; [exact Hrel|]. intros a _. reflexivity.
  - destruct (step_rel_acc s x y accs Hrel Ea) as (t & Et & Rt & Ot).
    destruct (IH t Rt) as (s' & Es' & Rs' & Os').
    exists s'. split; [|split; [exact Rs'|]].
    + apply (ExecF.mstepsF_cons rsegs RNG s t s'); [|exact Es']. split.
      * destruct Hrel as (_ & _ & _ & Esvc & _). rewrite Esvc. exact Hsvc.
      * exists accs. split; [exact Et | exact Fa].
    + intros a Ha. rewrite (Os' a Ha). exact (Ot a Ha).
Qed.

Lemma evtF_rel_ro : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop) s s0, ms_rel rsegs s s0 ->
  ExecF.evtF rsegs RNG Q s0 ->
  ExecF.evtF rsegs RNG (fun s' => exists s0', Q s0' /\ ms_rel rsegs s' s0' /\ ro_same rsegs (ms_mem s) (ms_mem s')) s.
Proof.
  intros RNG Q s s0 Hrel (s0' & Hs & HQ).
  destruct (mstepsF_rel_ro RNG s0 s0' Hs s Hrel) as (s' & Hs' & Hr & Ho).
  exists s'. split; [exact Hs'|]. exists s0'. split; [exact HQ|]. split; [exact Hr | exact Ho].
Qed.

Lemma evtF_normalize_ro : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop) R F pc fc rv m ro,
  ro_agree rsegs m ->
  ExecF.evtF rsegs RNG Q (MS R F pc fc rv (normalize rsegs m) ro) ->
  ExecF.evtF rsegs RNG (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs m (ms_mem s))
    (MS R F pc fc rv m ro).
Proof.
  intros RNG Q R F pc fc rv m ro Hro H.
  exact (evtF_rel_ro RNG Q (MS R F pc fc rv m ro) (MS R F pc fc rv (normalize rsegs m) ro)
    (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
      (mem_rel_normalize rsegs m Hro)))))))) H).
Qed.
