(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma reg_neq_of_eqb : forall a b : reg, bv_eqb a b = false -> a <> b.
Proof. intros a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wt_lay : Type := (reg * word)%type.
Definition wt_l (rd : reg) (v : word) : wt_lay := (rd, v).
Definition wt_regs : Type := bvmap 5 word.
Definition wt_ow : Type := option word.
Definition wt_some (v : word) : wt_ow := Some v.
Definition wt_none : wt_ow := None.
Fixpoint wt_upd_chain (Y : bvmap 5 word) (l : list wt_lay) : bvmap 5 word :=
  match l with
  | [] => Y
  | ly :: l' => regupd (wt_upd_chain Y l') (fst ly) (snd ly)
  end.
Fixpoint wt_chain_look (l : list wt_lay) (r : reg) : option word :=
  match l with
  | [] => None
  | ly :: l' => if bv_eqb r (fst ly) then Some (snd ly) else wt_chain_look l' r
  end.
Lemma wt_getr_hit : forall X Y l r v,
  X = wt_upd_chain Y l -> wt_chain_look l r = wt_some v -> bv_eqb r 0 = false -> getr X r = v.
Proof.
  unfold wt_some. intros X Y l r v -> H H0. induction l as [|[rd v'] l IH]; cbn [wt_upd_chain wt_chain_look fst snd] in *; [discriminate H|].
  destruct (bv_eqb r rd) eqn:E.
  - injection H as ->. assert (r = rd) as <- by (apply bv_eq; apply Z.eqb_eq; exact E).
    apply getr_same. apply reg_neq_of_eqb. exact H0.
  - rewrite getr_other by (apply reg_neq_of_eqb; exact E). apply IH. exact H.
Qed.
Lemma wt_getr_miss : forall X Y l r,
  X = wt_upd_chain Y l -> wt_chain_look l r = wt_none -> getr X r = getr Y r.
Proof.
  unfold wt_none. intros X Y l r -> H. induction l as [|[rd v'] l IH]; cbn [wt_upd_chain wt_chain_look fst snd] in *; [reflexivity|].
  destruct (bv_eqb r rd) eqn:E; [discriminate H|].
  rewrite getr_other by (apply reg_neq_of_eqb; exact E). apply IH. exact H.
Qed.

(* [comment removed for export] *)
Ltac wt_chain_ulist X :=
  lazymatch X with
  | regupd ?Y ?rd ?v => let l := wt_chain_ulist Y in uconstr:(@cons wt_lay (wt_l rd v) l)
  | _ => uconstr:(@nil wt_lay)
  end.
Ltac wt_chain_base X :=
  lazymatch X with
  | regupd ?Y _ _ => wt_chain_base Y
  | _ => X
  end.
Ltac wt_chain_val X r :=
  lazymatch X with
  | regupd ?Y ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in constr:(@Some word v)
      | _ => wt_chain_val Y r
      end
  | _ => constr:(@None word)
  end.

Ltac getr_proof X r :=
  let l := wt_chain_ulist X in
  let Y := wt_chain_base X in
  let fv := wt_chain_val X r in
  lazymatch fv with
  | Some ?v => uconstr:(wt_getr_hit X Y l r v (@eq_refl wt_regs X) (@eq_refl wt_ow (wt_some v)) (@eq_refl bool false))
  | None => uconstr:(wt_getr_miss X Y l r (@eq_refl wt_regs X) (@eq_refl wt_ow wt_none))
  end.

Ltac gres :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let p := getr_proof X r in
             let p' := constr:(p) in rewrite p'
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.

(* [comment removed for export] *)
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Ltac is_pos_lit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_pos_lit q
  | xI ?q => is_pos_lit q
  end.
Ltac is_Z_lit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => is_pos_lit p
  | Zneg ?p => is_pos_lit p
  end.

(* [comment removed for export] *)
Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

(* [comment removed for export] *)
Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

(* [comment removed for export] *)
Ltac vnorm :=
  gres; imm_norm;
  match goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | _ => idtac end;
  match goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  match goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.

(* [comment removed for export] *)
Ltac with_tgt_hidden tac :=
  lazymatch goal with
  | |- msteps _ _ ?t =>
      tryif is_var t then tac ()
      else (let T := fresh "TGTH" in set (T := t); tac (); subst T)
  | |- _ => tac ()
  end.

(* [comment removed for export] *)
Ltac stepn_raw F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.
Ltac stepn F D := with_tgt_hidden ltac:(fun _ => stepn_raw F D).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv_raw F D v := stepiv F D v vres.
Ltac stepv F D v := with_tgt_hidden ltac:(fun _ => stepv_raw F D v).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac stepb_tk_raw F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].
Ltac stepb_tk F D tac := with_tgt_hidden ltac:(fun _ => stepb_tk_raw F D tac).   (* [comment removed for export] *)

Ltac stepb_ft_raw F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].
Ltac stepb_ft F D tac := with_tgt_hidden ltac:(fun _ => stepb_ft_raw F D tac).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

(* [comment removed for export] *)
Ltac stepret_raw F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).
Ltac stepret F D k tac := with_tgt_hidden ltac:(fun _ => stepret_raw F D k tac).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac stepsd_raw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].
Ltac stepsd F D aa vv oktac := with_tgt_hidden ltac:(fun _ => stepsd_raw F D aa vv oktac).   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac stepld_raw F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
Ltac stepld F D vv rtac := with_tgt_hidden ltac:(fun _ => stepld_raw F D vv rtac).   (* [comment removed for export] *)
