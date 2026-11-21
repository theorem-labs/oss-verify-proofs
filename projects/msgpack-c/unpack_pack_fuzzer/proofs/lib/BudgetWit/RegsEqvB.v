(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Br/StateGlue.v and Br/RegsEqv.v: evt_realizes and the register-equivalence transport restated over BudgetWit.Rzb.rzb, with the budget check carried across the equivalence *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (interp_eff_accesses_eqv takes the vvar branch of the read arm; step_accesses_eqv closes fetch_failure's new cascade by shape; sstep_eqv is Br.RegsEqv's, which covers the vDSO step cases; sys_rob_eqv carries RomBase.sys_rob across the equivalence, for rzb_node's new premise in rzb_cfg_eqv; imports RomBase). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Exec NodesM Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require RomBase.
Import ListNotations.
Open Scope bv_scope.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.

Section EvtB.
Variable segs : list Segment.

Lemma evt_rzb : forall (Q : machine_state -> Prop) ms mo (K : TSet),
  evt segs Q ms ->
  m_halted mo = None -> m_vm_lazy mo = [] ->
  (forall ms', Q ms' -> rzb segs (mkCfg ms' mo) K) ->
  rzb segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo K (ms' & Hrun & HQ) Hh Hlz HK.
  eapply rzb_msteps; [exact Hh | exact Hlz | apply msteps_C2S; exact Hrun | apply HK; exact HQ].
Qed.
End EvtB.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_eqv : forall t t', eff_eqv t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk a, MachineOk b =>
      core_eqv (fst (@access_value _ a)) (fst (@access_value _ b)) /\ snd (@access_value _ a) = snd (@access_value _ b)
      /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros t t' H. induction H; intros m; cbn [interp_eff_accesses fst snd access_value accessed_ranges]; auto.
  (* LPS: [interp_eff_accesses]'s read arm gained a [range_meets_vvar] branch on
     the None side.  This is the same hunk the g58 port already made in
     [FX/Acc.v:47]; this file is main-only and never saw it. *)
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|];
      [|destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [[[c1 m1] l1]| |];
    destruct (interp_eff_accesses segs (k' _) m) as [[[c1' m1'] l1']| |]; cbn in *; try exact H0; try contradiction.
    destruct H0 as (Hc & Hm & ->). split; [exact Hc|]. split; [exact Hm|reflexivity].
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [[[c1 m1] l1]| |];
    destruct (interp_eff_accesses segs k' _) as [[[c1' m1'] l1']| |]; cbn in *; try exact IHeff_eqv; try contradiction.
    destruct IHeff_eqv as (Hc & Hm & ->). split; [exact Hc|]. split; [exact Hm|reflexivity].
Qed.

Lemma ms_reg_eqv : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof. intros ms ms' r (HR & _). exact (HR r). Qed.

Lemma decode_exec_accesses_eqv : forall ms ms' w, ms_eqv ms ms' ->
  ares_eqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - cbn. rewrite H17. split; [|reflexivity]. repeat split; assumption.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom].
    pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HR HF) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc' fc' rv')) m') as [[[c m1] l]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] l']| |];
    cbn in *; try exact K; try contradiction.
    destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). split; [|reflexivity]. repeat split; cbn; auto.
Qed.

Lemma step_accesses_eqv : forall ms ms', ms_eqv ms ms' ->
  ares_eqv (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  (* [fetch_failure]'s boolean cascade changed shape at the revision and this
     file is main-only, so it never saw the port.  Every leaf is [True], so
     close them by SHAPE rather than by naming two. *)
  unfold fetch_failure.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact I.
Qed.

Lemma step_eqv : forall ms ms', ms_eqv ms ms' ->
  res_eqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof. intros ms ms' H. unfold RiscvSemantics.step. apply ares_res_eqv, step_accesses_eqv, H. Qed.

Lemma syscall_args_eqv : forall ms ms', ms_eqv ms ms' -> syscall_args ms = syscall_args ms'.
Proof.
  intros ms ms' (HR & _). unfold syscall_args, ms_gpr. cbn [Z.of_nat Z.add Pos.of_succ_nat Pos.add Pos.succ].
  rewrite !(regs_eqv_reg_get _ _ _ HR) by reflexivity. reflexivity.
Qed.

Lemma sys_input_eqv : forall ms ms' x8, ms_eqv ms ms' -> sys_input segs ms x8 = sys_input segs ms' x8.
Proof.
  intros ms ms' x8 Heqv. pose proof (syscall_args_eqv ms ms' Heqv) as Ha.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold sys_input. rewrite Ha. reflexivity.
Qed.

Lemma apply_effect_eqv : forall ms ms' eff, ms_eqv ms ms' ->
  ms_eqv (apply_effect ms eff) (apply_effect ms' eff).
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] eff
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold apply_effect, set_reg; simpl. split; [apply regs_eqv_set; exact HR|]. repeat split; auto.
Qed.

Lemma advance_past_svc_eqv : forall ms ms', ms_eqv ms ms' ->
  ms_eqv (advance_past_svc ms) (advance_past_svc ms').
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold advance_past_svc, ms_pc; simpl. repeat split; auto.
Qed.

Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros c. split; [apply ms_eqv_refl | reflexivity]. Qed.
Lemma cfg_eqv_sym : forall c c', cfg_eqv c c' -> cfg_eqv c' c.
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1 | congruence]. Qed.

Lemma mi_account_step_eqv : forall ms ms' mo, ms_eqv ms ms' ->
  match mi_account_step segs ms mo, mi_account_step segs ms' mo with
  | MachineOk (a, moa), MachineOk (b, mob) => ms_eqv a b /\ moa = mob
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros ms ms' mo Heqv. pose proof (step_accesses_eqv ms ms' Heqv) as H.
  unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [[a la]| |];
  destruct (RiscvSemantics.step_accesses segs ms') as [[b lb]| |]; cbn in H |- *; try exact H; try contradiction.
  destruct H as [Hab <-]. destruct (materialize_model_accesses mo la); [split; [exact Hab | reflexivity] | exact I].
Qed.

Lemma sstep_eqv : forall ms ms' mo evs X, ms_eqv ms ms' ->
  sstep_cfg segs fcfg (mkCfg ms mo) evs X ->
  exists X', sstep_cfg segs fcfg (mkCfg ms' mo) evs X' /\ to_eqv X X'.
(* The step relation gained the revision's vDSO constructors and
   [sstep_cfg_instr_unmodeled] a fourth premise; the g58-ported
   [Br/RegsEqv.v] [sstep_eqv] has this statement word for word and covers
   every constructor, so the transport is that lemma's. *)
Proof. exact (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv.sstep_eqv segs). Qed.

Lemma sstep_cfg_eqv : forall c c' evs X, cfg_eqv c c' ->
  sstep_cfg segs fcfg c evs X -> exists X', sstep_cfg segs fcfg c' evs X' /\ to_eqv X X'.
Proof.
  intros [ms mo] [ms' mo'] evs X [Hms Hmo] Hst; simpl in Hms, Hmo; subst.
  apply (sstep_eqv ms ms'); assumption.
Qed.

(** The budget check reads the configuration only through its pending
    syscall and that syscall's input, which register equivalence keeps. *)
Lemma budget_ok_eqv : forall c c', cfg_eqv c c' -> budget_ok segs c -> budget_ok segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] [Hg Hn]; simpl in Hms, Hmo; subst mo'.
  pose proof Hms as (_ & _ & _ & Hsvc & _ & _ & _ & _).
  split.
  - intros x8 Hx. cbn [cfg_ms cfg_model] in *. rewrite <- (sys_input_eqv ms ms' x8 Hms).
    apply (Hg x8). cbn [cfg_ms]. congruence.
  - intros x8 eff m' evs Hx Hs. cbn [cfg_ms cfg_model] in *.
    rewrite <- (sys_input_eqv ms ms' x8 Hms) in Hs |- *.
    apply (Hn x8 eff m' evs); [cbn [cfg_ms]; congruence | exact Hs].
Qed.

(** [RomBase.sys_rob] reads the configuration through its pending syscall, the
    input of that syscall and the read-only backing, which register equivalence
    keeps; the larger backing's input keeps it the same way. *)
Lemma sys_rob_eqv : forall c c', cfg_eqv c c' -> RomBase.sys_rob segs c -> RomBase.sys_rob segs c'.
Proof.
  intros [ms mo] [ms' mo'] [Hms Hmo] Hrob r x8 Hr Hx o; simpl in Hms, Hmo; subst mo'.
  cbn [cfg_ms cfg_model] in *.
  pose proof Hms as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  assert (Hw : ms_eqv (RomBase.wrom ms r) (RomBase.wrom ms' r)).
  { split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. reflexivity. }
  rewrite <- (sys_input_eqv _ _ x8 Hw), <- (sys_input_eqv ms ms' x8 Hms).
  assert (Hr' : RomBase.rom_ext (ms_rom ms) r) by (rewrite H8; exact Hr).
  assert (Hx' : ms_svc_pending ms = Some x8) by congruence.
  exact (Hrob r x8 Hr' Hx' o).
Qed.

Theorem rzb_cfg_eqv : forall c T, rzb segs c T ->
  forall c', cfg_eqv c c' -> rzb segs c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 [Hok1 Hok2] Hrob Hb Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
  -
    pose (I' := { x : I * config | sstep_cfg segs fcfg c' (evs (fst x)) (SNext (snd x)) /\ cfg_eqv (nx (fst x)) (snd x) }).
    assert (Hx0 : exists c0', sstep_cfg segs fcfg c' (evs i0) (SNext c0') /\ cfg_eqv (nx i0) c0').
    { destruct (sstep_cfg_eqv c c' (evs i0) (SNext (nx i0)) Heqv (Hok1 i0)) as (X' & Hs' & HX).
      destruct X' as [c0'|]; cbn in HX; [| contradiction]. exists c0'. split; assumption. }
    destruct Hx0 as (c0' & Hs0 & He0).
    apply (rzb_conseq segs c' (ShapeAlg.t_alt (fun x : I' => ShapeAlg.t_emit (evs (fst (proj1_sig x))) (T (fst (proj1_sig x)))))).
    + apply (rzb_node segs c' I' (fun x => evs (fst (proj1_sig x))) (fun x => snd (proj1_sig x))
               (fun x => T (fst (proj1_sig x))) (exist _ (i0, c0') (conj Hs0 He0))).
      * split.
        -- intros [[i ci] [Hs He]]; cbn. exact Hs.
        -- intros e st Hst'.
           destruct (sstep_cfg_eqv c' c e st (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hs & HX).
           destruct (Hok2 e X Hs) as (i & -> & ->).
           destruct st as [ci|]; cbn in HX; [| contradiction].
           exists (exist _ (i, ci) (conj Hst' (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
      * exact (sys_rob_eqv c c' Heqv Hrob).
      * exact (budget_ok_eqv c c' Heqv Hb).
      * intros [[i ci] [Hs He]]; cbn. apply (IH i). exact He.
    + intros tr. split.
      * intros [[[i ci] [Hs He]] Htr]; cbn in Htr. exists i. exact Htr.
      * intros [i Htr].
        destruct (sstep_cfg_eqv c c' (evs i) (SNext (nx i)) Heqv (Hok1 i)) as (X' & Hs' & HX).
        destruct X' as [ci|]; cbn in HX; [| contradiction].
        exists (exist _ (i, ci) (conj Hs' HX)). cbn. exact Htr.
  - apply rzb_halt. destruct Heqv as [_ <-]. exact Hh.
  - eapply rzb_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

Theorem rzb_eqv : forall ms ms' mo T, ms_eqv ms ms' ->
  rzb segs (mkCfg ms mo) T -> rzb segs (mkCfg ms' mo) T.
Proof.
  intros ms ms' mo T Heqv H. apply (rzb_cfg_eqv _ T H). split; [exact Heqv | reflexivity].
Qed.

End WithSegs.
Corollary rzb_to_mkR : forall segs R F pc fc m ro mo T,
  rzb segs (mkCfg (MS (mkR_of R) F pc fc None m ro) mo) T ->
  rzb segs (mkCfg (MS R F pc fc None m ro) mo) T.
Proof. intros segs R F pc fc m ro mo T H. eapply rzb_eqv; [apply MS_mkR_of_eqv | exact H]. Qed.

Corollary rzb_of_mkR : forall segs R F pc fc m ro mo T,
  rzb segs (mkCfg (MS R F pc fc None m ro) mo) T ->
  rzb segs (mkCfg (MS (mkR_of R) F pc fc None m ro) mo) T.
Proof. intros segs R F pc fc m ro mo T H. eapply rzb_eqv; [apply ms_eqv_sym, MS_mkR_of_eqv | exact H]. Qed.
