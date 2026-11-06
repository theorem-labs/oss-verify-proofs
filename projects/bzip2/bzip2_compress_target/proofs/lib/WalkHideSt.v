(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require StartupTac ZStores.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import WalkHide.
Import ListNotations.
Local Open Scope bv_scope.

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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sn_st_new F D := wh_with ltac:(fun _ => stepn_old F D; StartupTac.pin).
Ltac sv_st_new F D v := wh_with ltac:(fun _ => stepiv_old F D v ltac:(gres; wh_clear_side; StartupTac.vclose)).
Ltac stepb_tk_st_new F D tac := wh_with ltac:(fun _ => stepb_tk_old F D ltac:(wh_clear_side; tac)).
Ltac stepb_ft_st_new F D tac := wh_with ltac:(fun _ => stepb_ft_old F D ltac:(wh_clear_side; tac)).
Ltac stw_st_new F D aa vv oktac :=
  wh_with ltac:(fun _ =>
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; wh_clear_side; StartupTac.vclose | gres; wh_clear_side; StartupTac.vclose | wh_user_mem oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; wh_clear_side; StartupTac.vclose | gres; wh_clear_side; StartupTac.vclose | wh_user_mem oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; wh_clear_side; StartupTac.vclose | gres; wh_clear_side; StartupTac.vclose | wh_user_mem oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; wh_clear_side; StartupTac.vclose | gres; wh_clear_side; StartupTac.vclose | reflexivity | wh_user_mem oktac ]
    end
  | step_simpl; wh_reveal_state_mem_lite; StartupTac.push_store ]).
Ltac ld_step_st_new F D bsv vv rdtac valtac :=
  wh_with ltac:(fun _ =>
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | gres; wh_clear_side; StartupTac.addr_norm; wh_user_mem rdtac | valtac ]
  | step_simpl ]; vnorm_old; StartupTac.pin).
Ltac lb_step_st_new F D bb rdtac :=
  wh_with ltac:(fun _ =>
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | gres; wh_clear_side; StartupTac.addr_norm; wh_user_mem rdtac ]
  | step_simpl ]; vnorm_old; StartupTac.pin).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wh_hide_cmem_comp :=   (* [comment removed for export] *)
  lazymatch goal with
  | |- msteps ?S (mkst ?X ?P (MemSplit.cmem ?sp0 ?m0 ?J ?D) ?ROM) ?T =>
      tryif is_var J then idtac else
      first [ let V := wh_find_hid J in change_no_check (msteps S (mkst X P (MemSplit.cmem sp0 m0 V D) ROM) T)
            | tryif wh_active J then idtac else
              (let V := fresh "WH_J" in pose (V := hid J); change_no_check (msteps S (mkst X P (MemSplit.cmem sp0 m0 V D) ROM) T)) ]
  end;
  lazymatch goal with
  | |- msteps ?S (mkst ?X ?P (MemSplit.cmem ?sp0 ?m0 ?J ?D) ?ROM) ?T =>
      tryif is_var D then idtac else
      first [ let V := wh_find_hid D in change_no_check (msteps S (mkst X P (MemSplit.cmem sp0 m0 J V) ROM) T)
            | tryif wh_active D then idtac else
              (let V := fresh "WH_D" in pose (V := hid D); change_no_check (msteps S (mkst X P (MemSplit.cmem sp0 m0 J V) ROM) T)) ]
  end;
  wh_clear_old_mem.
Ltac wh_unhid_cmem M :=
  lazymatch M with
  | MemSplit.cmem ?sp0 ?m0 ?J ?D => let J' := wh_unhid_mem J in let D' := wh_unhid_mem D in constr:(MemSplit.cmem sp0 m0 J' D')
  end.
Ltac wh_is_cmem M := lazymatch M with MemSplit.cmem _ _ _ _ => idtac end.
(* [comment removed for export] *)
Ltac ok_win_st_hid HJ :=
  apply MemSplit.store_ok_cmem_win;
  [ wh_reveal_scan; try StartupTac.wfJ_peel_fast; repeat apply MemSplit.wfJ_wbytes; exact HJ | StartupTac.region_side | StartupTac.region_side ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma regs_agree_chain_list : forall (Cl : list reg) (regs base : bvmap 5 word) (l : list (reg * word)),
  forallb (fun rv => existsb (bv_eqb (fst rv)) Cl) l = true ->
  regs_agree (fun r => In r Cl) regs base ->
  regs_agree (fun r => In r Cl) regs (chain_apply base l).
Proof.
  intros Cl regs base l. induction l as [|[r v] l IH]; cbn [forallb chain_apply fst]; intros H Hb; [exact Hb|].
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply regs_agree_upd; [|exact (IH H2 Hb)].
  apply existsb_exists in H1. destruct H1 as [x [Hx Hex]].
  apply chain_bv_eqb_true in Hex. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
Ltac ra_run :=
  lazymatch goal with
  | |- regs_agree (fun r => In r ?Cl) ?regs ?X =>
      lazymatch X with regupd (regupd _ _ _) _ _ => idtac end;
      let b := chain_base X in
      let l := chain_list X in
      refine (regs_agree_chain_list Cl regs b l (@eq_refl bool true) _)
  end.
Ltac solve_regs_agree_lin :=
  try ra_run; repeat (apply regs_agree_upd; [ StartupTac.in_list | ]); apply regs_agree_refl.
Ltac ra_chain_lin :=
  first [ apply regs_agree_refl
        | ra_run; ra_chain_lin
        | apply regs_agree_upd; [ StartupTac.in_list | ]; ra_chain_lin
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | StartupTac.regs_agree_weaken Hag ]; ra_chain_lin
          end ].
Ltac carry_st_new Hag H r T :=
  pose proof (Hag r ltac:(StartupTac.notin_list)) as T;
  try match type of T with
      | context [getr ?X ?r'] =>
          lazymatch X with regupd _ _ _ => idtac end; chain_deep X;
          let p := getr_proof_fast X r' in rewrite p in T
      end;
  repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
  rewrite ?H in T.

(* [comment removed for export] *)
Ltac peel_st_old1 :=
  first [ rewrite StartupTac.rdn_wbytes_out_Z by (StartupTac.len_simpl; lia)
        | rewrite rdn_wbytes_out by StartupTac.region_side ].
Ltac peel_st_batch := wh_reveal_rdn_var; repeat first [ wh_peel_batch | (tryif wh_top_overlaps then fail else peel_st_old1) ].

Module OptIn.
Export WalkHide.OptIn.
#[export] Ltac WalkHide.wh_blen_extra bs ::= lazymatch bs with ZStores.zeros ?n => n end.
#[export] Ltac StartupTac.peel ::= peel_st_batch.
#[export] Ltac WalkHide.wh_pin_sensitive ::= idtac.
#[export] Ltac WalkHide.wh_hide_mem_hook ::= wh_hide_cmem_comp.
#[export] Ltac WalkHide.wh_unhid_mem_hook M ::= wh_unhid_cmem M.
#[export] Ltac WalkHide.wh_structured_mem M ::= wh_is_cmem M.
#[export] Ltac StartupTac.ok_win HJ ::= ok_win_st_hid HJ.
#[export] Ltac StartupTac.sn F D ::= sn_st_new F D.
#[export] Ltac StartupTac.sv F D v ::= sv_st_new F D v.
#[export] Ltac StartupTac.stepb_tk F D tac ::= stepb_tk_st_new F D tac.
#[export] Ltac StartupTac.stepb_ft F D tac ::= stepb_ft_st_new F D tac.
#[export] Ltac StartupTac.stw F D aa vv oktac ::= stw_st_new F D aa vv oktac.
#[export] Ltac StartupTac.ld_step F D bsv vv rdtac valtac ::= ld_step_st_new F D bsv vv rdtac valtac.
#[export] Ltac StartupTac.lb_step F D bb rdtac ::= lb_step_st_new F D bb rdtac.
#[export] Ltac StartupTac.carry Hag H r T ::= carry_st_new Hag H r T.
#[export] Ltac StartupTac.ra_chain ::= ra_chain_lin.
#[export] Ltac StartupTac.solve_regs_agree ::= solve_regs_agree_lin.
End OptIn.
