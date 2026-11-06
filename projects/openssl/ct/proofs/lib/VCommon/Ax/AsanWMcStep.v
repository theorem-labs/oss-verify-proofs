(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section XS.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable model : Model.

(* [comment removed for export] *)
Lemma xs_reg : forall S rd v v' p' r m T,
  m_halted model = None -> ms_svc_pending S = None ->
  step_accesses segs S =
    MachineOk (@mkAccessReport machine_state (setx S rd v (ms_pc_val S + Z_to_bv 64 4) (ms_resv S) (ms_mem S)) []) ->
  v = v' -> ms_pc_val S + Z_to_bv 64 4 = p' -> ms_resv S = r -> ms_mem S = m ->
  realizes_cfg segs cfg (mkCfg (setx S rd v' p' r m) model) T ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros S rd v v' p' r m T Hh Hsvc Hs <- <- <- <- Hc.
  eapply rzc_acc; [exact Hh | exact Hsvc | exact Hs | apply acc_ok_nil | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma xs_ld : forall S w sz sg rd rs1 (imm : bv 12) x a bs' p' r m T,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, 4%Z) ->
  rg S rs1 = x -> x + sext 64 imm = a -> ms_mem S = m ->
  rdn segs m a (msz_n sz) = Some bs' -> acc_ok model [(a, msz_n sz)] ->
  ms_pc_val S + Z_to_bv 64 4 = p' -> ms_resv S = r ->
  realizes_cfg segs cfg (mkCfg (setx S rd (load_word sz sg bs') p' r m) model) T ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros S w sz sg rd rs1 imm x a bs' p' r m T Hh Hsvc HF HE HD Hx Ha Hm Hrd Hacc Hp Hr Hc.
  subst x a m p' r.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Load; [exact HF | exact HE | exact HD | exact Hrd] | exact Hacc | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma xs_st : forall S w sz rs1 rs2 (imm : bv 12) x y a p' r m T,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  rg S rs1 = x -> x + sext 64 imm = a -> rg S rs2 = y -> ms_mem S = m ->
  store_ok segs m a (msz_n sz) = true -> acc_ok model [(a, msz_n sz)] ->
  ms_pc_val S + Z_to_bv 64 4 = p' -> ms_resv S = r ->
  realizes_cfg segs cfg (mkCfg (setx S 0 w0 p' (inval a r) (write_to_mem m a (store_bytes sz y))) model) T ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros S w sz rs1 rs2 imm x y a p' r m T Hh Hsvc HF HE HD Hx Ha Hy Hm Hok Hacc Hp Hr Hc.
  subst x a y m p' r.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Store; [exact HF | exact HE | exact HD | exact Hok] | exact Hacc | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma xs_br : forall S w bc rs1 rs2 (imm : bv 13) x y p0 r m T,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch bc rs1 rs2 imm, 4%Z) ->
  rg S rs1 = x -> rg S rs2 = y -> ms_pc_val S = p0 -> ms_resv S = r -> ms_mem S = m ->
  realizes_cfg segs cfg (mkCfg (setx S 0 w0 (if branch_taken bc x y then p0 + sext 64 imm else p0 + Z_to_bv 64 4) r m) model) T ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros S w bc rs1 rs2 imm x y p0 r m T Hh Hsvc HF HE HD Hx Hy Hp Hr Hm Hc.
  subst x y p0 r m.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Branch; [exact HF | exact HE | exact HD] | apply acc_ok_nil | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma xs_br2 : forall S w bc rs1 rs2 (imm : bv 13) x y pt pn r m T,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch bc rs1 rs2 imm, 4%Z) ->
  rg S rs1 = x -> rg S rs2 = y -> ms_pc_val S + sext 64 imm = pt -> ms_pc_val S + Z_to_bv 64 4 = pn ->
  ms_resv S = r -> ms_mem S = m ->
  (branch_taken bc x y = true -> realizes_cfg segs cfg (mkCfg (setx S 0 w0 pt r m) model) T) ->
  (branch_taken bc x y = false -> realizes_cfg segs cfg (mkCfg (setx S 0 w0 pn r m) model) T) ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros S w bc rs1 rs2 imm x y pt pn r m T Hh Hsvc HF HE HD Hx Hy Ht Hn Hr Hm H1 H2.
  eapply xs_br; [exact Hh | exact Hsvc | exact HF | exact HE | exact HD | exact Hx | exact Hy | reflexivity | exact Hr | exact Hm |].
  destruct (branch_taken bc x y) eqn:E; [rewrite Ht; exact (H1 eq_refl) | rewrite Hn; exact (H2 eq_refl)].
Qed.

(* [comment removed for export] *)
Lemma xs_jal0 : forall S w (imm : bv 21) p' r m T,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal 0 imm, 4%Z) ->
  ms_pc_val S + sext 64 imm = p' -> ms_resv S = r -> ms_mem S = m ->
  realizes_cfg segs cfg (mkCfg (setx S 0 w0 p' r m) model) T ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros S w imm p' r m T Hh Hsvc HF HE HD Hp Hr Hm Hc.
  subst p' r m.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Jal; [exact HF | exact HE | exact HD] | apply acc_ok_nil | exact Hc].
Qed.

End XS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XJ.
Variable segs : list Segment.
Variable model : Model.
Variable J : machine_state -> Prop.
Hypothesis J_acc : forall ms ms' acc, ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) -> acc_ok model acc -> J ms' -> J ms.

Lemma xj_acc : forall ms ms' acc, m_halted model = None -> ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) -> acc_ok model acc -> J ms' -> J ms.
Proof. intros ms ms' acc _. apply J_acc. Qed.

Lemma xj_reg : forall S rd v v' p' r m,
  m_halted model = None -> ms_svc_pending S = None ->
  step_accesses segs S =
    MachineOk (@mkAccessReport machine_state (setx S rd v (ms_pc_val S + Z_to_bv 64 4) (ms_resv S) (ms_mem S)) []) ->
  v = v' -> ms_pc_val S + Z_to_bv 64 4 = p' -> ms_resv S = r -> ms_mem S = m ->
  J (setx S rd v' p' r m) -> J S.
Proof.
  intros S rd v v' p' r m Hh Hsvc Hs <- <- <- <- Hc.
  eapply xj_acc; [exact Hh | exact Hsvc | exact Hs | apply acc_ok_nil | exact Hc].
Qed.

Lemma xj_ld : forall S w sz sg rd rs1 (imm : bv 12) x a bs' p' r m,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, 4%Z) ->
  rg S rs1 = x -> x + sext 64 imm = a -> ms_mem S = m ->
  rdn segs m a (msz_n sz) = Some bs' -> acc_ok model [(a, msz_n sz)] ->
  ms_pc_val S + Z_to_bv 64 4 = p' -> ms_resv S = r ->
  J (setx S rd (load_word sz sg bs') p' r m) -> J S.
Proof.
  intros S w sz sg rd rs1 imm x a bs' p' r m Hh Hsvc HF HE HD Hx Ha Hm Hrd Hacc Hp Hr Hc.
  subst x a m p' r.
  eapply xj_acc; [exact Hh | exact Hsvc | eapply wacc_Load; [exact HF | exact HE | exact HD | exact Hrd] | exact Hacc | exact Hc].
Qed.

Lemma xj_st : forall S w sz rs1 rs2 (imm : bv 12) x y a p' r m,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  rg S rs1 = x -> x + sext 64 imm = a -> rg S rs2 = y -> ms_mem S = m ->
  store_ok segs m a (msz_n sz) = true -> acc_ok model [(a, msz_n sz)] ->
  ms_pc_val S + Z_to_bv 64 4 = p' -> ms_resv S = r ->
  J (setx S 0 w0 p' (inval a r) (write_to_mem m a (store_bytes sz y))) -> J S.
Proof.
  intros S w sz rs1 rs2 imm x y a p' r m Hh Hsvc HF HE HD Hx Ha Hy Hm Hok Hacc Hp Hr Hc.
  subst x a y m p' r.
  eapply xj_acc; [exact Hh | exact Hsvc | eapply wacc_Store; [exact HF | exact HE | exact HD | exact Hok] | exact Hacc | exact Hc].
Qed.

Lemma xj_br : forall S w bc rs1 rs2 (imm : bv 13) x y p0 r m,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch bc rs1 rs2 imm, 4%Z) ->
  rg S rs1 = x -> rg S rs2 = y -> ms_pc_val S = p0 -> ms_resv S = r -> ms_mem S = m ->
  J (setx S 0 w0 (if branch_taken bc x y then p0 + sext 64 imm else p0 + Z_to_bv 64 4) r m) -> J S.
Proof.
  intros S w bc rs1 rs2 imm x y p0 r m Hh Hsvc HF HE HD Hx Hy Hp Hr Hm Hc.
  subst x y p0 r m.
  eapply xj_acc; [exact Hh | exact Hsvc | eapply wacc_Branch; [exact HF | exact HE | exact HD] | apply acc_ok_nil | exact Hc].
Qed.

Lemma xj_br2 : forall S w bc rs1 rs2 (imm : bv 13) x y pt pn r m,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch bc rs1 rs2 imm, 4%Z) ->
  rg S rs1 = x -> rg S rs2 = y -> ms_pc_val S + sext 64 imm = pt -> ms_pc_val S + Z_to_bv 64 4 = pn ->
  ms_resv S = r -> ms_mem S = m ->
  (branch_taken bc x y = true -> J (setx S 0 w0 pt r m)) ->
  (branch_taken bc x y = false -> J (setx S 0 w0 pn r m)) ->
  J S.
Proof.
  intros S w bc rs1 rs2 imm x y pt pn r m Hh Hsvc HF HE HD Hx Hy Ht Hn Hr Hm H1 H2.
  eapply xj_br; [exact Hh | exact Hsvc | exact HF | exact HE | exact HD | exact Hx | exact Hy | reflexivity | exact Hr | exact Hm |].
  destruct (branch_taken bc x y) eqn:E; [rewrite Ht; exact (H1 eq_refl) | rewrite Hn; exact (H2 eq_refl)].
Qed.

Lemma xj_jal0 : forall S w (imm : bv 21) p' r m,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal 0 imm, 4%Z) ->
  ms_pc_val S + sext 64 imm = p' -> ms_resv S = r -> ms_mem S = m ->
  J (setx S 0 w0 p' r m) -> J S.
Proof.
  intros S w imm p' r m Hh Hsvc HF HE HD Hp Hr Hm Hc.
  subst p' r m.
  eapply xj_acc; [exact Hh | exact Hsvc | eapply wacc_Jal; [exact HF | exact HE | exact HD] | apply acc_ok_nil | exact Hc].
Qed.

End XJ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pcw_assoc : forall b o x y, pcw b (o + x + y) = pcw b (o + (x + y)).
Proof. intros. unfold pcw. f_equal. lia. Qed.

(* [comment removed for export] *)
Ltac litz :=
  repeat match goal with
  | |- context [(?x + ?y)%Z] => is_closed_term x; is_closed_term y;
                                 let v := eval vm_compute in (x + y)%Z in change (x + y)%Z with v
  end.

Ltac rwregsX := repeat match goal with H : rg ?S ?r = _ |- context [rg ?S ?r] => rewrite H end.
Ltac svcX := first [ reflexivity | assumption ].
Ltac ecX := first [ reflexivity | assumption ].
Ltac ftacX F := first [ exact F
                      | match goal with H : ms_pc_val ?S = _ |- fetch_word _ (ms_pc_val ?S) = _ => rewrite H; exact F end
                      | rewrite pc_setx; exact F ].
(* [comment removed for export] *)
Ltac pcX := rewrite ?pc_setx;
  try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end);
  rewrite ?pcw_add, ?pcw_sext; rewrite ?pcw_assoc; lits; litz; rewrite ?Z.add_0_r; reflexivity.
Ltac resvX := rewrite ?resv_setx; reflexivity.
Ltac memX := rewrite ?mem_setx; reflexivity.
(* [comment removed for export] *)
Ltac regX := rgn; rwregsX; reflexivity.
(* [comment removed for export] *)
Ltac valX := rgn; rwregsX; unfold w0; rewrite ?alu_add, ?zw_add, ?zw_add_sext; lits; litz;
             rewrite ?Z.add_0_r, ?Z.add_0_l; reflexivity.
(* [comment removed for export] *)
Ltac addrX := rewrite ?zw_add_sext; lits; litz; rewrite ?Z.add_0_r; reflexivity.

(* [comment removed for export] *)
Ltac wr ACC F D V :=
  eapply xs_reg; [ assumption | svcX | eapply ACC; [ ftacX F | ecX | exact D ] | V | pcX | resvX | memX | ].
(* [comment removed for export] *)
Ltac wl F D RD AC :=
  eapply xs_ld; [ assumption | svcX | ftacX F | ecX | exact D | regX | addrX | memX | RD | AC | pcX | resvX | ].
(* [comment removed for export] *)
Ltac ws F D V OK AC :=
  eapply xs_st; [ assumption | svcX | ftacX F | ecX | exact D | regX | addrX | V | memX | OK | AC | pcX | resvX | ].
(* [comment removed for export] *)
Ltac wb F D :=
  eapply xs_br; [ assumption | svcX | ftacX F | ecX | exact D | regX | regX
                | rewrite ?pc_setx; try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); reflexivity
                | resvX | memX | ].
(* [comment removed for export] *)
Ltac wb2 F D :=
  eapply xs_br2; [ assumption | svcX | ftacX F | ecX | exact D | regX | regX | pcX | pcX | resvX | memX | | ].
(* [comment removed for export] *)
Ltac wj F D := eapply xs_jal0; [ assumption | svcX | ftacX F | ecX | exact D | pcX | resvX | memX | ].

(* [comment removed for export] *)
Ltac jacc := match goal with H : forall ms ms' acc, ms_svc_pending ms = None -> _ |- _ => exact H end.
Ltac jst ACC F D :=
  eapply xj_acc;
  [ jacc
  | assumption
  | first [ reflexivity | assumption ]
  | eapply ACC; [ fetch_tac F | reflexivity | exact D ]
  | apply acc_ok_nil
  | try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn ].
Ltac jr ACC F D V :=
  eapply xj_reg; [ jacc | assumption | svcX | eapply ACC; [ ftacX F | ecX | exact D ] | V | pcX | resvX | memX | ].
Ltac jl F D RD AC :=
  eapply xj_ld; [ jacc | assumption | svcX | ftacX F | ecX | exact D | regX | addrX | memX | RD | AC | pcX | resvX | ].
Ltac js F D V OK AC :=
  eapply xj_st; [ jacc | assumption | svcX | ftacX F | ecX | exact D | regX | addrX | V | memX | OK | AC | pcX | resvX | ].
Ltac jb F D :=
  eapply xj_br; [ jacc | assumption | svcX | ftacX F | ecX | exact D | regX | regX
                | rewrite ?pc_setx; try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); reflexivity
                | resvX | memX | ].
Ltac jb2 F D :=
  eapply xj_br2; [ jacc | assumption | svcX | ftacX F | ecX | exact D | regX | regX | pcX | pcX | resvX | memX | | ].
Ltac jj F D := eapply xj_jal0; [ jacc | assumption | svcX | ftacX F | ecX | exact D | pcX | resvX | memX | ].
