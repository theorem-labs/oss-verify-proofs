(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Export
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  MemSplit StartupAux ZStores.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos37Corelib4Init5Logichf3and46Stdlib6ZArith6BinInt1Zj92le35stdpp9bitvectorbdefinitionsl62bvj93addj96of_natj93pow37Corelib4Init9Datatypesod4listl67Z_to_bvod6lengthod6option01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~sb3rdnj92ltod3nathf2eqhf2or3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehi17Segment69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~hm16wbytes3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshq5dmachine_state69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~hud6msteps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

(* [comment removed for export] *)
Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

(* [comment removed for export] *)
Ltac len_rw :=
  repeat match goal with
         | |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
         | |- context [length (zeros ?n)] => rewrite (length_zeros n)
         | |- context [length (repeat ?x ?n)] => rewrite (repeat_length x n)
         end.

(* [comment removed for export] *)
Ltac region_side :=
  unfold win_lo;
  match goal with |- context [stack_max_size] => rewrite ?stack_max_size_val | _ => idtac end;
  len_rw;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

(* [comment removed for export] *)
Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

(* [comment removed for export] *)
Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

(* [comment removed for export] *)
Ltac with_mem_hidden tac :=
  lazymatch goal with
  | |- msteps _ (mkst _ _ ?m _) _ =>
      let M := fresh "MEMH" in set (M := m); tac (); subst M
  | |- _ => tac ()
  end.

(* [comment removed for export] *)
Ltac sn F D := with_mem_hidden ltac:(fun _ => stepn F D; pin).
Ltac sv F D v := stepiv F D v vclose.

(* [comment removed for export] *)
Ltac stepb_tk F D tac := with_mem_hidden ltac:(fun _ => WalkTac.stepb_tk F D tac).
Ltac stepb_ft F D tac := with_mem_hidden ltac:(fun _ => WalkTac.stepb_ft F D tac).

(* [comment removed for export] *)
Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

(* [comment removed for export] *)
Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

(* [comment removed for export] *)
Ltac ok_win HJ :=
  apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

(* [comment removed for export] *)
Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac lb_step F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma rdn_wbytes_out_Z : ltac2:(zQ "h31!h9!j3!l1!n3!n8!ne!o7!q5!qc!r6!rf!s8!hg6!hgc!hh1!hh7!hhc!hl6!hpb&@2$4^3@1$5@2$9@1$3@1$0#8^5>4segs@1$7$h1>2bs@1$7@1$3@1$0#8>1m>0@1$3@1$0#k0@1$a@1$3@1$0#8>2zb$b>2za$b>1n$e>0@2$1@2$1@2$2Z^2@2$d^2@2$6+2+k0@2$1@2$2@2$4^2@1$5^1@2$6+2+k0@2$1@2$1@2$2Z^3@2$d^3@2$6+2+k0@2$1@2$2~0@2$6+2+k0@2$h0@2$2@2$4^2@1$5^1^3@2$2~0^2@3$f@1$a@1$7@1$3@1$0#8@4$c^7@3$h2^5@2$8@1$0#k0^4^6@2$8@1$0#k0^3^2@4$c^7^5@2$8@1$0#k0^3^2").
Proof.
  (intros segs bs m zb za n nd_i1; ndestruct nd_i1 as (Ha & Han & Hb & Hbn & Hd)).
  apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
End FPX1.

Ltac len_simpl :=
  len_rw; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul Pos.add Pos.mul].

Ltac peel :=
  repeat first [ rewrite rdn_wbytes_out_Z by (len_simpl; lia)
               | rewrite rdn_wbytes_out by region_side ].

(* [comment removed for export] *)
Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

(* [comment removed for export] *)
Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

(* [comment removed for export] *)
Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

(* [comment removed for export] *)
Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

(* [comment removed for export] *)
Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
  rewrite ?H in T.

(* [comment removed for export] *)
Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition bwd : ltac2:(zQ "30!q5!hl6!htc>4segs@1$0$1>1G>0$2PP") := ltac2:(zQ "40!htc!q5!hl6!ii6\4segs@1$1$2\1G>0$0P>2st$0>3st'$0>0@3$3^4^2^1>0@1^4^2@1^5^4").

End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
