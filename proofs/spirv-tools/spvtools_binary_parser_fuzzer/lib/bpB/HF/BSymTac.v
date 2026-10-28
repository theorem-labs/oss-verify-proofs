(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BExitSim BPropExec BCatExec BCatSim BSeqExec BStreamExec BMmapSim BWallSim BStreamSim BDrainSim BStoreOk BFootprint BSymExec BStepTac BShapeAlg.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : DFP}.

Fixpoint sr_pins (ps : list (reg * expr)) (sr : list expr) : list expr :=
  match ps with
  | [] => sr
  | (r, e) :: rest => sr_pins rest (sr_upd sr (ridx r) e)
  end.

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

Lemma alu64_add_0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
  intro x. rewrite alu_add. change (v_add x (Z_to_bv 64 0)) with (v_addi x 0).
  apply v_addi_0.
Qed.

Lemma aluw_add_0 : forall x : word,
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 0))) = v_lw x.
Proof.
  intro x. rewrite low32_lit.
  change (Z_to_bv 32 0) with (@Z_to_bv 32 0).
  rewrite alu32_add_0. apply b_lw_val.
Qed.

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

Lemma bdenot_var : forall E n, bdenot E (SBVar n) = E n.
Proof. reflexivity. Qed.

Lemma bdenot_lit : forall E, bdenot E SBLit = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma edenot_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

Lemma edenot_var : forall E n, edenot E (EVar n) = E n.
Proof. reflexivity. Qed.

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
Context {fx : DFP}.

End WithFP3.
Ltac sym_z_lit k :=
  lazymatch k with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac sym_z_norm :=
  repeat match goal with

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
Context {fx : DFP}.

End WithFP6.
Ltac sym_lit_norm :=
  repeat match goal with

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
Context {fx : DFP}.

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
Context {fx : DFP}.

End WithFP8.
Ltac sym_mem_norm :=
  cbn [mem_denot e_addr e_width e_val];
  sym_norm; sym_lit_norm.

Section WithFP9.
Context {fx : DFP}.

Lemma msteps_to_exit : forall segs code ms ms',
  msteps segs ms ms' -> to_exit segs code ms' -> to_exit segs code ms.
Proof.
  intros segs code ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH]; [auto|].
  intro He. eapply te_step; eauto.
Qed.

Lemma msteps_to_wr : forall segs LH bs ms ms',
  msteps segs ms ms' ->
  BStreamSim.to_wr segs LH bs ms' -> BStreamSim.to_wr segs LH bs ms.
Proof.
  intros segs LH bs ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH];
    [auto|].
  intro Hw. eapply BStreamSim.twr_step; eauto.
Qed.

Lemma msteps_lh_next : forall segs LH ms ms',
  msteps segs ms ms' ->
  BStreamSim.lh_next segs LH ms' -> BStreamSim.lh_next segs LH ms.
Proof.
  intros segs LH ms ms' H (m & Hm & HL). exists m. split; [|exact HL].
  eapply msteps_trans; eauto.
Qed.

End WithFP9.
Ltac sym_halted :=
  solve [ reflexivity
        | eassumption
        | (rewrite ?BMmapSim.mmap_model_halted, ?BMmapSim.munmap_model_halted;
           solve [ reflexivity | eassumption ])
        | (cbn [cfg_model m_halted]; autorewrite with model; solve [ reflexivity | eassumption ]) ].

Ltac sym_no_lazy :=
  cbn [cfg_model];
  repeat first
    [ rewrite BMmapSim.mmap_model_lazy
    | apply BMmapSim.munmap_model_no_lazy ];
  solve [ reflexivity | eassumption ].

Section WithFP10.
Context {fx : DFP}.

End WithFP10.
Ltac chain_mst :=
  first [ eapply BCatSim.msteps_to_wexit
        | eapply BMmapSim.msteps_twm
        | eapply BMmapSim.msteps_twm_tail
        | eapply BMmapSim.msteps_tmw
        | eapply BStreamSim.msteps_to_rd
        | eapply msteps_to_wr
        | eapply BWallSim.msteps_to_wall_tail
        | eapply BWallSim.msteps_to_wallexit
        | eapply BDrainSim.msteps_to_rd
        | eapply BDrainSim.msteps_to_out
        | eapply msteps_to_exit
        | eapply msteps_lh_next
        | (eapply BShapeAlg.rz_msteps; [ sym_halted | sym_no_lazy | | ])
        | eapply msteps_trans ].

Section WithFP11.
Context {fx : DFP}.

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
Context {fx : DFP}.

End WithFP13.
Ltac sym_reg H R r v tac :=
  assert (getr R r = v) by (sym_regs H; tac).

Section WithFP14.
Context {fx : DFP}.

End WithFP14.
Ltac list_len l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | @cons _ _ ?t => let n := list_len t in constr:(S n)
  end.

Section WithFP15.
Context {fx : DFP}.

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
Context {fx : DFP}.

End WithFP16.
Ltac sym_pc_lit :=
  try lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] => wlit p
  end.

Section WithFP17.
Context {fx : DFP}.

End WithFP17.
Ltac sym_sc_auto :=
  first [ reflexivity | (repeat split; lia) ].

Section WithFP18.
Context {fx : DFP}.

End WithFP18.
Ltac sym_pin_auto :=
  first
  [ reflexivity
  | multimatch goal with
    | H : regs_ok _ _ _ |- _ =>
        sym_regs H; first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia) ]
    end ].

Section WithFP19.
Context {fx : DFP}.

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
Context {fx : DFP}.

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
Context {fx : DFP}.

End WithFP21.
Ltac sym_chain Hms :=
  sym_pc_Z; chain_mst; [ exact Hms | ]; norm_pc; sym_pc_lit.
