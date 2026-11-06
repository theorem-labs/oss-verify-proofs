(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Export
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  MemSplit StartupAux ZStores.
Unset Nia Cache. Unset Nra Cache.

Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

Ltac region_side :=
  unfold win_lo; rewrite ?stack_max_size_val, ?length_N_to_le_bytes, ?length_zeros, ?repeat_length;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

Ltac sn F D := stepn F D; pin.
Ltac sv F D v := stepiv F D v vclose.

Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

Ltac stw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | reflexivity | oktac ]
    end
  | step_simpl; push_store ].

Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

Ltac ok_win HJ :=
  apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

Ltac ld_step F D bsv vv rdtac valtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac | valtac ]
  | step_simpl ]; vnorm; pin.

Ltac lb_step F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.

Ltac peel := repeat (rewrite rdn_wbytes_out by region_side).

Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
  rewrite ?H in T.

Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].

Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
  forall st st', msteps segs st st' -> G st' -> G st.

Lemma bwd_msteps : forall segs tgt, bwd segs (fun st => msteps segs st tgt).
Proof. intros segs tgt st st' H1 H2. eapply msteps_trans; eassumption. Qed.

Ltac gsteps HG := eapply HG.
