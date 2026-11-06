(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector bitvector.tactics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxMemSound FxValSound FxStepSound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition regop_of (fi : finstr) : option (aluop * int) :=
  match fi with
  | FOp op rd _ _ | FOpImm op rd _ _ => Some (op, rd)
  | _ => None
  end.
Definition mval (ms : machine_state) (r : int) : word := Sem.rget (core_of ms) (Z_to_bv 5 (to_Z r)).
Definition regop_opnds (ms : machine_state) (fi : finstr) : option (word * word) :=
  match fi with
  | FOp _ _ rs1 rs2 => Some (mval ms rs1, mval ms rs2)
  | FOpImm _ _ rs1 imm => Some (mval ms rs1, wbv imm)
  | _ => None
  end.

Section StepMain.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.

Local Abbreviation Rr := (R segs IM rho).
Local Abbreviation dvr := (dv rho).

(* [comment removed for export] *)
Lemma code_entry : forall F ms fi,
  Rr F ms -> iget (f_pc F) code = Some fi ->
  to_Z (f_pc F) < pc_bound - 4 /\
  exists w, fetch_word segs (ms_pc ms) = Some w /\
    ((is_ecall w = true /\ fi = FEcall) \/
     (is_ecall w = false /\ exists i, decode_any w = Some (i, 4) /\ compile (to_Z (f_pc F)) i = Some fi)).
Proof.
  intros F ms fi HR Hi. pose proof (Hcode _ _ Hi) as Hb. unfold build_entry in Hb.
  destruct ((to_Z (f_pc F) <? pc_bound - 4) && (0 <=? to_Z (f_pc F))) eqn:Hrng; [|discriminate].
  apply andb_true_iff in Hrng as [Hlt _]. apply Z.ltb_lt in Hlt. split; [exact Hlt|].
  unfold ms_pc. rewrite (R_pc _ _ _ _ _ HR).
  destruct (fetch_word segs (Z_to_bv 64 (to_Z (f_pc F)))) as [w|]; [|discriminate].
  exists w. split; [reflexivity|].
  destruct (is_ecall w) eqn:Ee.
  - left. split; [reflexivity|]. apply some_inj in Hb. subst fi. reflexivity.
  - right. split; [reflexivity|]. destruct (decode_any w) as [[i sz]|]; [|discriminate].
    exists i. destruct sz as [|p|p]; try discriminate.
    do 3 (destruct p as [p|p|]; try discriminate). split; [reflexivity | exact Hb].
Qed.

Theorem fx_step_ecall : forall F ms,
  Rr F ms -> fx_step IM code F = FEcallAt -> step segs ms = MachineOk (ms_pend ms).
Proof.
  intros F ms HR H. unfold fx_step in H.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct (code_entry F ms fi HR Hi) as (_ & w & Hf & [[He _] | (He & i & Hd & Hc)]).
  - exact (step_ecall segs ms w Hf He).
  - exfalso. destruct i; cbn [compile] in Hc; try discriminate;
      repeat match type of Hc with
             | context [match ?x with _ => _ end] => destruct x; try discriminate
             end;
      apply some_inj in Hc; subst fi; cbn in H;
      repeat match type of H with
             | context [match ?x with _ => _ end] => destruct x; try discriminate
             | context [if ?x then _ else _] => destruct x; try discriminate
             end; discriminate.
Qed.

Lemma c_pc_rset : forall rd v c, c_pc (Sem.rset rd v c) = c_pc c.
Proof. intros rd v c. unfold Sem.rset. destruct (is_x0 rd); reflexivity. Qed.
Lemma c_resv_rset : forall rd v c, c_resv (Sem.rset rd v c) = c_resv c.
Proof. intros rd v c. unfold Sem.rset. destruct (is_x0 rd); reflexivity. Qed.

(* [comment removed for export] *)
Lemma R_after_reg : forall F ms rd w v npc,
  Rr F ms -> dvr v = w ->
  Rr (FxState.rset F (ireg rd) v npc)
     (ms_of ms (Sem.rset rd w (with_pc (Z_to_bv 64 (to_Z npc)) (core_of ms))) (ms_mem ms)).
Proof.
  intros F ms rd w v npc HR Hv. apply R_intro_step.
  - rewrite c_pc_rset. reflexivity.
  - apply (regs_after_rset segs IM rho Hrho0 F ms); [exact HR | exact Hv | reflexivity].
  - rewrite c_resv_rset. cbn [with_pc c_resv core_of]. exact (R_resv _ _ _ _ _ HR).
  - exact (R_mem _ _ _ _ _ HR).
Qed.

Lemma R_after_pc : forall F ms npc,
  Rr F ms ->
  Rr (set_pc F npc) (ms_of ms (with_pc (Z_to_bv 64 (to_Z npc)) (core_of ms)) (ms_mem ms)).
Proof.
  intros F ms npc HR. apply R_intro_step.
  - reflexivity.
  - intros r. cbn [with_pc]. exact (R_regs _ _ _ _ _ HR r).
  - exact (R_resv _ _ _ _ _ HR).
  - exact (R_mem _ _ _ _ _ HR).
Qed.

Lemma interp_load_val : forall sz sgn a k m bs,
  ov_read_bytes segs m a (msz_nat sz) = Some bs ->
  interp_eff segs (load_val sz sgn a k) m = interp_eff segs (k (load_result sz sgn bs)) m.
Proof.
  intros sz sgn a k m bs H. destruct sz; unfold load_val.
  - rewrite (interp_load segs 8 a _ m bs H). reflexivity.
  - rewrite (interp_load segs 16 a _ m bs H). reflexivity.
  - rewrite (interp_load segs 32 a _ m bs H). reflexivity.
  - rewrite (interp_load segs 64 a _ m bs H). reflexivity.
Qed.

Lemma interp_store_val : forall sz a v k m,
  store_ok segs m a (msz_nat sz) = true ->
  interp_eff segs (store_val sz a v k) m = interp_eff segs k (write_to_mem m a (store_bytes_of sz v)).
Proof.
  intros sz a v k m H. destruct sz; unfold store_val.
  - rewrite (interp_store segs 8 a _ k m H). reflexivity.
  - rewrite (interp_store segs 16 a _ k m H). reflexivity.
  - rewrite (interp_store segs 32 a _ k m H). reflexivity.
  - rewrite (interp_store segs 64 a _ k m H). reflexivity.
Qed.

Lemma inval_resv_facts : forall a c,
  c_pc (inval_resv a c) = c_pc c
  /\ (forall r, Sem.rget (inval_resv a c) r = Sem.rget c r)
  /\ c_resv (inval_resv a c) = (if resv_hit (c_resv c) a then None else c_resv c).
Proof.
  intros a c. unfold inval_resv, resv_hit. destruct (c_resv c) as [r|] eqn:E.
  - destruct (bv_unsigned r =? bv_unsigned a); cbn [with_resv c_pc c_resv]; rewrite ?E; repeat split; reflexivity.
  - rewrite E. repeat split; reflexivity.
Qed.

Lemma sext32_id : forall b : bv 32, sext 32 b = b.
Proof. intros b. unfold sext. apply bv_sign_extend_idemp. Qed.

(* [comment removed for export] *)
Lemma R_after_lr : forall F ms rd w v npc a,
  Rr F ms -> dvr v = w ->
  Rr (FS npc (f_regs (FxState.rset F (ireg rd) v npc)) (f_mem F) (Some a))
     (ms_of ms (with_resv (Some (dvr a)) (Sem.rset rd w (with_pc (Z_to_bv 64 (to_Z npc)) (core_of ms)))) (ms_mem ms)).
Proof.
  intros F ms rd w v npc a HR Hv. apply R_intro_step; cbn [f_pc f_regs f_mem f_resv].
  - cbn [with_resv c_pc]. rewrite c_pc_rset. reflexivity.
  - intros r. rewrite sem_rget_with_resv.
    rewrite (regs_after_rset segs IM rho Hrho0 F ms rd w v npc (with_pc (Z_to_bv 64 (to_Z npc)) (core_of ms)) HR Hv (fun _ => eq_refl)). reflexivity.
  - reflexivity.
  - exact (R_mem _ _ _ _ _ HR).
Qed.

(* [comment removed for export] *)
Lemma R_after_sc : forall F ms rd w v npc M' m' r' c,
  Rr F ms -> dvr v = w ->
  c_pc c = Z_to_bv 64 (to_Z npc) ->
  (forall r, Sem.rget c r = Sem.rget (core_of ms) r) ->
  c_resv c = option_map dvr r' ->
  mem_ok segs IM rho M' m' ->
  Rr (FS npc (f_regs (FxState.rset F (ireg rd) v npc)) M' r') (ms_of ms (Sem.rset rd w c) m').
Proof.
  intros F ms rd w v npc M' m' r' c HR Hv Hpc Hc Hres Hm. apply R_intro_step; cbn [f_pc f_regs f_mem f_resv].
  - rewrite c_pc_rset. exact Hpc.
  - intros r. rewrite (regs_after_rset segs IM rho Hrho0 F ms rd w v npc c HR Hv Hc). reflexivity.
  - rewrite c_resv_rset. exact Hres.
  - exact Hm.
Qed.

(* [comment removed for export] *)
Definition step_post (F : fstate) (ms : machine_state) (F' : fstate) (ms' : machine_state) : Prop :=
  Rr F' ms'
  /\ (forall x, ~ claimed_wr IM rho (f_mem F) x -> ms_mem ms' x = ms_mem ms x)
  /\ (forall x, claimed_wr IM rho (f_mem F') x -> claimed_wr IM rho (f_mem F) x)
  /\ ms_rom ms' = ms_rom ms
  /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms.   (* [comment removed for export] *)

Lemma post_same : forall F ms F' ms',
  f_mem F' = f_mem F -> ms_mem ms' = ms_mem ms -> ms_rom ms' = ms_rom ms ->
  ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms ->
  Rr F' ms' -> step_post F ms F' ms'.
Proof.
  intros F ms F' ms' HM Hm Hrom Hfr Hfc HR. split; [exact HR|]. split; [|split; [|split; [|split]]].
  - intros x _. rewrite Hm. reflexivity.
  - intros x Hx. rewrite <- HM. exact Hx.
  - exact Hrom.
  - exact Hfr.
  - exact Hfc.
Qed.

Lemma post_store : forall F ms F' ms' a sz v M',
  Rr F ms ->
  fm_store IM (f_mem F) a sz v = Some M' ->
  f_mem F' = M' ->
  ms_mem ms' = write_to_mem (ms_mem ms) (dvr a) (store_bytes_of sz (dvr v)) ->
  ms_rom ms' = ms_rom ms ->
  ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms ->
  Rr F' ms' -> step_post F ms F' ms'.
Proof.
  intros F ms F' ms' a sz v M' HR0 Hst HM' Hm Hrom Hfr Hfc HR. subst M'. split; [exact HR|].
  split; [|split; [|split; [|split]]].
  - intros x Hx. rewrite Hm.
    exact (fm_store_frame segs IM rho _ _ _ _ _ _ (R_mem _ _ _ _ _ HR0) Hst x Hx).
  - intros x Hx. exact (fm_store_wr_mono IM rho _ _ _ _ _ Hst x Hx).
  - exact Hrom.
  - exact Hfr.
  - exact Hfc.
Qed.

(* [comment removed for export] *)
Lemma sem_rset_fregs : forall rd v c, c_fregs (Sem.rset rd v c) = c_fregs c.
Proof. intros rd v c. unfold Sem.rset. destruct (is_x0 rd); reflexivity. Qed.
Lemma sem_rset_fcsr : forall rd v c, c_fcsr (Sem.rset rd v c) = c_fcsr c.
Proof. intros rd v c. unfold Sem.rset. destruct (is_x0 rd); reflexivity. Qed.
Lemma inval_resv_fregs : forall a c, c_fregs (inval_resv a c) = c_fregs c.
Proof. intros a c. unfold inval_resv. destruct (c_resv c) as [r|]; [|reflexivity].
  destruct (bv_unsigned r =? bv_unsigned a)%Z; reflexivity. Qed.
Lemma inval_resv_fcsr : forall a c, c_fcsr (inval_resv a c) = c_fcsr c.
Proof. intros a c. unfold inval_resv. destruct (c_resv c) as [r|]; [|reflexivity].
  destruct (bv_unsigned r =? bv_unsigned a)%Z; reflexivity. Qed.
Ltac shape_tac :=
  cbn [ms_fregs ms_fcsr ms_of];
  repeat (progress (cbn [c_fregs c_fcsr with_resv with_pc core_of];
                    rewrite ?sem_rset_fregs, ?sem_rset_fcsr, ?inval_resv_fregs, ?inval_resv_fcsr));
  reflexivity.

(* [comment removed for export] *)
Theorem fx_step_sound_full : forall F ms F',
  Rr F ms -> fx_step IM code F = FNext F' ->
  exists ms', step segs ms = MachineOk ms' /\ step_post F ms F' ms'.
Proof.
  intros F ms F' HR H.
  unfold fx_step in H.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct (code_entry F ms fi HR Hi) as (Hpc & w & Hf & [[He ->] | (He & i & Hd & Hc)]); [discriminate|].
  rewrite (step_decode segs ms w i Hf He Hd).
  pose proof (R_regs_ok segs IM rho F ms HR) as HM.
  pose proof (R_pc _ _ _ _ _ HR) as Epc.
  pose proof (pc_plus4 _ Hpc) as Enpc.
  pose proof (R_regs _ _ _ _ _ HR) as Hregs.
  destruct i; cbn [compile] in Hc; try discriminate.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H. injection H as <-.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR|]. rewrite (dv_conc rho Hrho0), wbv_w_of_bv. reflexivity.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H. injection H as <-.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR|]. rewrite (dv_conc rho Hrho0), wbv_w_of_bv. reflexivity.
  - (* [comment removed for export] *)
    destruct (pc_of_word (Z_to_bv 64 (to_Z (f_pc F)) + sext 64 imm)) as [t|] eqn:Et; [|discriminate].
    apply some_inj in Hc. subst fi. cbv beta iota in H. injection H as <-.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. apply pc_of_word_sound in Et. rewrite <- Et.
    eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR|]. rewrite (dv_conc rho Hrho0), wbv_w_of_bv. first [reflexivity | exact Enpc].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_jalr (FxState.rget F (ireg rs1)) (w_of_bv (sext 64 imm))) as [tpc|] eqn:Ej; [|discriminate].
    injection H as <-. apply (fv_jalr_sound rho Hrho0) in Ej as [Ej _]. rewrite wbv_w_of_bv, <- Hregs in Ej.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. cbn zeta. rewrite Ej.
    eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR|]. rewrite (dv_conc rho Hrho0), wbv_w_of_bv. first [reflexivity | exact Enpc].
  - (* [comment removed for export] *)
    destruct (pc_of_word (Z_to_bv 64 (to_Z (f_pc F)) + sext 64 imm)) as [t|] eqn:Et; [|discriminate].
    destruct (pc_of_word (Z_to_bv 64 (to_Z (f_pc F)) + Z_to_bv 64 4)) as [n|] eqn:En; [|discriminate].
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_branch (f_mem F) c (FxState.rget F (ireg rs1)) (FxState.rget F (ireg rs2))) as [bb|] eqn:Eb; [|discriminate].
    injection H as <-. apply (fv_branch_sound rho Hrho0 _ _ _ _ _ HM (proj2 (R_mem _ _ _ _ _ HR))) in Eb. rewrite <- !Hregs in Eb.
    unfold exec. cbn [core_of c_pc]. rewrite Epc. rewrite Eb.
    apply pc_of_word_sound in Et, En. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    destruct bb; [rewrite <- Et | rewrite <- En]; apply R_after_pc; exact HR.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) ALU_ADD (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (sext 64 imm)))) as [a|] eqn:Ea; [|discriminate].
    destruct (fm_load_abs IM (f_mem F) a sz signed) as [v|] eqn:El0; [|discriminate].
    destruct (fm_load_abs_inv rho Hrho0 IM _ _ _ _ _ HM El0) as (a' & Ea' & El). clear El0.
    injection H as <-.
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    unfold alu64, alu in Ea. rewrite <- Ea' in Ea. clear Ea'. revert El Ea. generalize a'. clear a. intros a El Ea.
    destruct (fm_load_sound segs IM rho Hrho0 _ _ _ _ _ _ (R_mem _ _ _ _ _ HR) El) as (bs & Hbs & Hres).
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. rewrite <- Ea.
    rewrite (interp_load_val _ _ _ _ _ bs Hbs). eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | symmetry; exact Hres].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) ALU_ADD (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (sext 64 imm)))) as [a|] eqn:Ea; [|discriminate].
    destruct (fm_store_abs IM (f_mem F) a sz (FxState.rget F (ireg rs2))) as [M'|] eqn:Es0; [|discriminate].
    destruct (fm_store_abs_inv rho Hrho0 IM _ _ _ _ _ HM Es0) as (a' & Ea' & Es). clear Es0.
    destruct (resv_after_store (f_resv F) a) as [r'|] eqn:Er; [|discriminate].
    injection H as <-.
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    unfold alu64, alu in Ea.
    apply (resv_after_store_sound rho) in Er. rewrite <- (R_resv _ _ _ _ _ HR) in Er.
    rewrite <- Ea' in Ea, Er. clear Ea'. revert Es Ea Er. generalize a'. clear a. intros a Es Ea Er.
    destruct (fm_store_sound segs IM rho Hrho0 _ _ _ _ _ _ (R_mem _ _ _ _ _ HR) Es) as (Hok & Hm').
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. cbn zeta. rewrite <- Ea.
    rewrite (interp_store_val _ _ _ _ _ Hok). eexists. split; [reflexivity|]. apply (post_store F ms _ _ a sz (FxState.rget F (ireg rs2)) M' HR Es); [reflexivity | cbn [ms_mem ms_of]; rewrite !Hregs; reflexivity | reflexivity | shape_tac | shape_tac |].
    destruct (inval_resv_facts (dvr a) (with_pc (Z_to_bv 64 (to_Z (f_pc F + 4)%uint63)) (core_of ms))) as (I1 & I2 & I3).
    apply R_intro_step; cbn [f_pc f_regs f_mem f_resv].
    + rewrite I1. reflexivity.
    + intros r. rewrite I2. cbn [with_pc]. exact (Hregs r).
    + rewrite I3. cbn [with_pc c_resv core_of]. symmetry. exact Er.
    + rewrite <- Hregs in Hm'. exact Hm'.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) op (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (sext 64 imm)))) as [v|] eqn:Ea; [|discriminate].
    injection H as <-.
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | exact Ea].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) op (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (zext 64 shamt)))) as [v|] eqn:Ea; [|discriminate].
    injection H as <-.
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite (dv_conc rho Hrho0), wbv_w_of_bv, <- Hregs in Ea.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | exact Ea].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu (f_mem F) op (FxState.rget F (ireg rs1)) (FxState.rget F (ireg rs2))) as [v|] eqn:Ea; [|discriminate].
    injection H as <-.
    apply (fv_alu_sound rho Hrho0 _ _ _ _ _ HM) in Ea. rewrite <- !Hregs in Ea.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | exact Ea].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu32 ALU_ADD (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (sext 64 imm)))) as [v|] eqn:Ea; [|discriminate].
    injection H as <-.
    apply (fv_alu32_sound rho Hrho0) in Ea.
    rewrite (dv_conc rho Hrho0), wbv_w_of_bv, low32_sext64, <- Hregs in Ea.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | exact Ea].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_alu32 op (FxState.rget F (ireg rs1)) (FV 0 (w_of_bv (zext 64 shamt)))) as [v|] eqn:Ea; [|discriminate].
    injection H as <-.
    apply (fv_alu32_sound rho Hrho0) in Ea.
    rewrite (dv_conc rho Hrho0), wbv_w_of_bv, low32_zext64, <- Hregs in Ea.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | exact Ea].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    assert (Ea : exists v, F' = FxState.rset F (ireg rd) v (f_pc F + 4)%uint63
                /\ dv rho v = sext 64 (alu32 op (low32 (dv rho (FxState.rget F (ireg rs1)))) (low32 (dv rho (FxState.rget F (ireg rs2)))))).
    { destruct (fv_alu32 op (FxState.rget F (ireg rs1)) (FxState.rget F (ireg rs2))) as [v|] eqn:Ea.
      - injection H as <-. exists v. split; [reflexivity|]. exact (fv_alu32_sound rho Hrho0 _ _ _ _ Ea).
      - destruct (fv_sh32 (f_mem F) op (FxState.rget F (ireg rs1)) (FxState.rget F (ireg rs2))) as [v|] eqn:Es; [|discriminate].
        injection H as <-. exists v. split; [reflexivity|].
        exact (fv_sh32_sound rho Hrho0 _ _ _ _ _ (R_regs_ok _ _ _ _ _ HR) Es). }
    destruct Ea as (v & -> & Ea).
    rewrite <- !Hregs in Ea.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | exact Ea].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H. injection H as <-.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |]. apply R_after_pc. exact HR.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H. injection H as <-.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |]. apply R_after_pc. exact HR.
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_conc2 (w_muldiv op) (FxState.rget F (ireg rs1)) (FxState.rget F (ireg rs2))) as [v|] eqn:Ea; [|discriminate].
    injection H as <-.
    apply (fv_conc2_sound rho Hrho0 _ (mul_div op)) in Ea; [|intros; apply w_muldiv_spec].
    rewrite <- !Hregs in Ea.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | exact Ea].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota in H.
    destruct (fv_conc2 (w_muldiv32 op) (FxState.rget F (ireg rs1)) (FxState.rget F (ireg rs2))) as [v|] eqn:Ea; [|discriminate].
    injection H as <-.
    apply (fv_conc2_sound rho Hrho0 _ (fun x y => sext 64 (mul_div op (low32 x) (low32 y)))) in Ea; [|intros; apply w_muldiv32_spec].
    rewrite <- !Hregs in Ea.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
    apply R_after_reg; [exact HR | exact Ea].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    destruct (fm_load_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) true) as [v|] eqn:El0; [|discriminate].
    destruct (fm_load_abs_inv rho Hrho0 IM _ _ _ _ _ HM El0) as (a' & Ea' & El). clear El0.
    injection H as <-.
    apply (aligned_for_sound rho Hrho0 _ _ _ HM) in Eal. rewrite <- Hregs in Eal.
    destruct (fm_load_sound segs IM rho Hrho0 _ _ _ _ _ _ (R_mem _ _ _ _ _ HR) El) as (bs & Hbs & Hres).
    rewrite Ea', <- Hregs in Hbs.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. cbn zeta. rewrite Eal. cbn [negb].
    destruct w0; cbn [awidth_sz msz_nat] in Hbs.
    + rewrite (interp_load segs 32 _ _ _ bs Hbs). eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
      rewrite (Hregs rs1). apply R_after_lr; [exact HR | symmetry; exact Hres].
    + rewrite (interp_load segs 64 _ _ _ bs Hbs). eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
      rewrite (Hregs rs1). apply R_after_lr; [exact HR | symmetry; exact Hres].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    apply (aligned_for_sound rho Hrho0 _ _ _ HM) in Eal. rewrite <- Hregs in Eal.
    destruct (resv_eqb (f_resv F) (FxState.rget F (ireg rs1))) as [hit|] eqn:Ehit; [|discriminate].
    apply (resv_eqb_sound rho) in Ehit. rewrite <- (R_resv _ _ _ _ _ HR), <- Hregs in Ehit.
    unfold exec. cbn [core_of c_pc c_resv]. rewrite Epc, Enpc. cbn zeta. rewrite Eal. cbn [negb].
    unfold resv_hit in Ehit. rewrite Ehit.
    destruct hit.
    + destruct (fm_store_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) (FxState.rget F (ireg rs2))) as [M'|] eqn:Es0; [|discriminate].
      destruct (fm_store_abs_inv rho Hrho0 IM _ _ _ _ _ HM Es0) as (a' & Ea' & Es). clear Es0.
      injection H as <-.
      destruct (fm_store_sound segs IM rho Hrho0 _ _ _ _ _ _ (R_mem _ _ _ _ _ HR) Es) as (Hok & Hm').
      rewrite Ea' in Hok, Hm'.
      destruct w0; cbn [awidth_sz msz_nat store_bytes_of] in Hok, Hm';
        repeat rewrite <- Hregs in Hok; repeat rewrite <- Hregs in Hm'.
      * rewrite (interp_store segs 32 _ _ _ _ Hok). eexists. split; [reflexivity|]. apply (post_store F ms _ _ a' SZ4 (FxState.rget F (ireg rs2)) M' HR Es); [reflexivity | cbn [ms_mem ms_of]; rewrite Ea', !Hregs; reflexivity | reflexivity | shape_tac | shape_tac |].
        apply R_after_sc; try reflexivity; [exact HR | rewrite (dv_conc rho Hrho0); apply wbv_w_zero | exact Hm'].
      * rewrite (interp_store segs 64 _ _ _ _ Hok). eexists. split; [reflexivity|]. apply (post_store F ms _ _ a' SZ8 (FxState.rget F (ireg rs2)) M' HR Es); [reflexivity | cbn [ms_mem ms_of]; rewrite Ea', !Hregs; reflexivity | reflexivity | shape_tac | shape_tac |].
        apply R_after_sc; try reflexivity; [exact HR | rewrite (dv_conc rho Hrho0); apply wbv_w_zero | exact Hm'].
    + injection H as <-. eexists. split; [reflexivity|]. apply post_same; [reflexivity | reflexivity | reflexivity | shape_tac | shape_tac |].
      apply R_after_sc; try reflexivity; [exact HR | rewrite (dv_conc rho Hrho0); apply wbv_w_one | exact (R_mem _ _ _ _ _ HR)].
  - (* [comment removed for export] *)
    apply some_inj in Hc. subst fi. cbv beta iota zeta in H.
    destruct (aligned_for w0 (FxState.rget F (ireg rs1)) (f_mem F)) eqn:Eal; cbn [negb] in H; [|discriminate].
    apply (aligned_for_sound rho Hrho0 _ _ _ HM) in Eal. rewrite <- Hregs in Eal.
    destruct (fm_load_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) true) as [old|] eqn:El0; [|discriminate].
    destruct (fm_load_abs_inv rho Hrho0 IM _ _ _ _ _ HM El0) as (al & Eal' & El). clear El0.
    destruct (fm_load_sound segs IM rho Hrho0 _ _ _ _ _ _ (R_mem _ _ _ _ _ HR) El) as (bs & Hbs & Hres).
    rewrite Eal' in Hbs.
    set (src := FxState.rget F (ireg rs2)) in *.
    set (nvo := if (vtag old =? 0)%uint63 && (vtag src =? 0)%uint63
                then Some (FV 0 (match w0 with AD => w_amo op (vw old) (vw src) | AW => w_amo32 op (vw old) (vw src) end))
                else match op with AMO_SWAP => Some src | _ => None end) in *.
    destruct nvo as [nv|] eqn:Env; [|discriminate].
    destruct (resv_after_store (f_resv F) (FxState.rget F (ireg rs1))) as [r'|] eqn:Er; [|discriminate].
    destruct (fm_store_abs IM (f_mem F) (FxState.rget F (ireg rs1)) (awidth_sz w0) nv) as [M'|] eqn:Es0; [|discriminate].
    destruct (fm_store_abs_inv rho Hrho0 IM _ _ _ _ _ HM Es0) as (a' & Ea' & Es). clear Es0.
    injection H as <-.
    destruct (fm_store_sound segs IM rho Hrho0 _ _ _ _ _ _ (R_mem _ _ _ _ _ HR) Es) as (Hok & Hm').
    rewrite Ea' in Hok, Hm'.
    apply (resv_after_store_sound rho) in Er. rewrite <- (R_resv _ _ _ _ _ HR) in Er.
    (* [comment removed for export] *)
    assert (Hnv : match w0 with
                  | AW => low32 (dvr nv) = amo_val op (low32 (dvr old)) (low32 (dvr src))
                  | AD => dvr nv = amo_val op (dvr old) (dvr src)
                  end).
    { subst nvo. destruct ((vtag old =? 0)%uint63 && (vtag src =? 0)%uint63) eqn:Ec.
      - apply andb_true_iff in Ec as [Eo Esrc]. apply some_inj in Env. subst nv.
        rewrite (dv_conc rho Hrho0), (dv_tag0 rho Hrho0 _ Eo), (dv_tag0 rho Hrho0 _ Esrc).
        destruct w0; [apply w_amo32_spec | apply w_amo_spec].
      - destruct op; try discriminate. apply some_inj in Env. subst nv. destruct w0; reflexivity. }
    destruct (inval_resv_facts (Sem.rget (core_of ms) rs1) (with_pc (Z_to_bv 64 (to_Z (f_pc F + 4)%uint63)) (core_of ms))) as (I1 & I2 & I3).
    repeat rewrite <- Hregs in Hbs. repeat rewrite <- Hregs in Hok. repeat rewrite <- Hregs in Hm'. repeat rewrite <- Hregs in Er.
    unfold src in Hnv. rewrite <- Hregs in Hnv.
    unfold exec. cbn [core_of c_pc]. rewrite Epc, Enpc. cbn zeta. rewrite Eal. cbn [negb].
    destruct w0; cbn [awidth_sz msz_nat store_bytes_of load_result] in Hbs, Hok, Hm', Hres.
    + rewrite (interp_load segs 32 _ _ _ bs Hbs).
      assert (Eold : low32 (dvr old) = bv_extract 0 32 (le_bytes_to_word bs)).
      { rewrite <- Hres. rewrite low32_sext64. apply sext32_id. }
      rewrite Eold in Hnv. rewrite Hnv in Hm'.
      rewrite (interp_store segs 32 _ _ _ _ Hok). eexists. split; [reflexivity|]. apply (post_store F ms _ _ a' SZ4 nv M' HR Es); [reflexivity | cbn [ms_mem ms_of store_bytes_of]; rewrite Hnv, Ea', !Hregs; reflexivity | reflexivity | shape_tac | shape_tac |].
      apply R_after_sc; [exact HR | symmetry; exact Hres | exact I1 | exact I2 | rewrite I3; symmetry; exact Er | exact Hm'].
    + rewrite (interp_load segs 64 _ _ _ bs Hbs).
      rewrite <- Hres in Hnv. rewrite Hnv in Hm'.
      rewrite (interp_store segs 64 _ _ _ _ Hok). eexists. split; [reflexivity|]. apply (post_store F ms _ _ a' SZ8 nv M' HR Es); [reflexivity | cbn [ms_mem ms_of store_bytes_of]; rewrite Hnv, Ea', !Hregs; reflexivity | reflexivity | shape_tac | shape_tac |].
      apply R_after_sc; [exact HR | symmetry; exact Hres | exact I1 | exact I2 | rewrite I3; symmetry; exact Er | exact Hm'].
Qed.

Theorem fx_step_sound_frame : forall F ms F',
  Rr F ms -> fx_step IM code F = FNext F' ->
  exists ms', step segs ms = MachineOk ms'
    /\ Rr F' ms'
    /\ (forall x, ~ claimed_wr IM rho (f_mem F) x -> ms_mem ms' x = ms_mem ms x)
    /\ (forall x, claimed_wr IM rho (f_mem F') x -> claimed_wr IM rho (f_mem F) x)
    /\ ms_rom ms' = ms_rom ms.
Proof.
  intros F ms F' HR H.
  destruct (fx_step_sound_full F ms F' HR H) as (ms' & Hs & HR' & Hfr & Hmono & Hrom & _).
  exists ms'. split; [exact Hs|]. split; [exact HR'|]. split; [exact Hfr|]. split; [exact Hmono | exact Hrom].
Qed.

(* [comment removed for export] *)
Corollary fx_step_sound_shape : forall F ms F' ms',
  Rr F ms -> fx_step IM code F = FNext F' -> step segs ms = MachineOk ms' ->
  ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms.
Proof.
  intros F ms F' ms' HR H Hs.
  destruct (fx_step_sound_full F ms F' HR H) as (ms'' & Hs' & _ & _ & _ & _ & Hfr & Hfc).
  rewrite Hs in Hs'. injection Hs' as <-. split; assumption.
Qed.

(* [comment removed for export] *)
Corollary fx_step_sound : forall F ms F',
  Rr F ms -> fx_step IM code F = FNext F' ->
  exists ms', step segs ms = MachineOk ms' /\ Rr F' ms'.
Proof.
  intros F ms F' HR H.
  destruct (fx_step_sound_frame F ms F' HR H) as (ms' & Hs & HR' & _).
  exists ms'. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma fm_store_abs_store : forall M a sz v M',
  fm_store_abs IM M a sz v = Some M' -> exists a', fm_store IM M a' sz v = Some M'.
Proof.
  intros M a sz v M' H. unfold fm_store_abs in H.
  destruct (fm_store IM M a sz v) as [M0|] eqn:E.
  - exists a. rewrite E. exact H.
  - destruct (vtag a =? 0)%uint63; [|discriminate]. eexists. exact H.
Qed.

(* [comment removed for export] *)
Lemma fx_step_mem : forall F F',
  fx_step IM code F = FNext F' ->
  f_mem F' = f_mem F \/ exists a sz v, fm_store IM (f_mem F) a sz v = Some (f_mem F').
Proof.
  intros F F' H. unfold fx_step in H.
  destruct (iget (f_pc F) code) as [fi|]; [|discriminate].
  destruct fi; cbv zeta in H;
    repeat match type of H with
           | context [match ?x with _ => _ end] => destruct x eqn:?; try discriminate
           | context [if ?x then _ else _] => destruct x eqn:?; try discriminate
           end;
    try discriminate;
    injection H as <-; cbn [f_mem FxState.rset set_pc];
    first [left; reflexivity
          | right;
            match goal with
            | Hs : fm_store_abs IM _ _ _ _ = Some _ |- _ =>
                destruct (fm_store_abs_store _ _ _ _ _ Hs) as [a' Hs']; exists a'; do 2 eexists; exact Hs'
            end].
Qed.

Lemma fx_step_wr_mono : forall F F',
  fx_step IM code F = FNext F' ->
  forall x, claimed_wr IM rho (f_mem F') x -> claimed_wr IM rho (f_mem F) x.
Proof.
  intros F F' H x Hx. destruct (fx_step_mem F F' H) as [E | (a & sz & v & Hst)].
  - rewrite <- E. exact Hx.
  - exact (fm_store_wr_mono IM rho _ _ _ _ _ Hst x Hx).
Qed.
(* [comment removed for export] *)
Lemma fx_step_regop : forall F ms fi op rd wa wb,
  Rr F ms -> iget (f_pc F) code = Some fi ->
  regop_of fi = Some (op, rd) -> regop_opnds ms fi = Some (wa, wb) ->
  exists ms', step segs ms = MachineOk ms'
    /\ ms_mem ms' = ms_mem ms /\ ms_rom ms' = ms_rom ms /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms
    /\ forall v, dvr v = alu64 op wa wb -> Rr (FxState.rset F rd v (f_pc F + 4)%uint63) ms'.
Proof.
  intros F ms fi op rd wa wb HR Hi Hro Hopn.
  destruct (code_entry F ms fi HR Hi) as (Hpc & w & Hf & [[He ->] | (He & i & Hd & Hc)]); [discriminate Hro|].
  rewrite (step_decode segs ms w i Hf He Hd).
  pose proof (R_pc _ _ _ _ _ HR) as Epc.
  pose proof (pc_plus4 _ Hpc) as Enpc.
  assert (Hmv : forall r : reg, mval ms (ireg r) = Sem.rget (core_of ms) r).
  { intros r. unfold mval. rewrite ireg_to_Z, Z_to_bv_bv_unsigned. reflexivity. }
  destruct i; cbn [compile] in Hc; try discriminate;
    try (destruct (pc_of_word _); try discriminate; try (destruct (pc_of_word _); try discriminate));
    apply some_inj in Hc; subst fi; cbn [regop_of regop_opnds] in Hro, Hopn; try discriminate Hro;
    injection Hro as <- <-; injection Hopn as <- <-; rewrite ?Hmv, ?wbv_w_of_bv;
    unfold exec; cbn [core_of c_pc]; rewrite Epc, Enpc; eexists; (split; [reflexivity|]);
    (split; [reflexivity|]); (split; [reflexivity|]); (split; [shape_tac|]); (split; [shape_tac|]);
    intros v Hv; (apply R_after_reg; [exact HR | exact Hv]).
Qed.

(* [comment removed for export] *)
Lemma fx_step_branch : forall F ms c rs1 rs2 tgt npc,
  Rr F ms -> iget (f_pc F) code = Some (FBranch c rs1 rs2 tgt npc) ->
  exists ms', step segs ms = MachineOk ms'
    /\ ms_mem ms' = ms_mem ms /\ ms_rom ms' = ms_rom ms /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms
    /\ Rr (set_pc F (if branch_taken c (mval ms rs1) (mval ms rs2) then tgt else npc)) ms'
    /\ mval ms rs1 = dvr (FxState.rget F rs1) /\ mval ms rs2 = dvr (FxState.rget F rs2).
Proof.
  intros F ms c rs1 rs2 tgt npc HR Hi.
  destruct (code_entry F ms _ HR Hi) as (Hpc & w & Hf & [[He Hfi] | (He & i & Hd & Hc)]); [discriminate Hfi|].
  rewrite (step_decode segs ms w i Hf He Hd).
  pose proof (R_pc _ _ _ _ _ HR) as Epc.
  assert (Hmv : forall r : reg, mval ms (ireg r) = Sem.rget (core_of ms) r).
  { intros r. unfold mval. rewrite ireg_to_Z, Z_to_bv_bv_unsigned. reflexivity. }
  destruct i; cbn [compile] in Hc; try discriminate Hc; try (destruct (pc_of_word _); discriminate Hc).
  destruct (pc_of_word (Z_to_bv 64 (to_Z (f_pc F)) + sext 64 imm)) as [t|] eqn:Et; [|discriminate].
  destruct (pc_of_word (Z_to_bv 64 (to_Z (f_pc F)) + Z_to_bv 64 4)) as [n|] eqn:En; [|discriminate].
  apply some_inj in Hc. injection Hc as -> -> -> -> ->. rewrite !Hmv.
  unfold exec. cbn [core_of c_pc]. rewrite Epc.
  apply pc_of_word_sound in Et, En. eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [shape_tac|]. split; [shape_tac|].
  split; [|split; apply (R_regs _ _ _ _ _ HR)].
  match goal with |- context [branch_taken ?c' ?a' ?b'] => destruct (branch_taken c' a' b') end;
    [rewrite <- Et | rewrite <- En]; apply R_after_pc; exact HR.
Qed.

End StepMain.
