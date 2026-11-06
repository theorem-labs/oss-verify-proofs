(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export Tac Walk.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Export ExecA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma policy_var : forall (P : acc -> Prop) (x : word) n,
  P (Z_to_bv 64 (bv_unsigned x), n) -> P (x, n).
Proof. intros P x n H. rewrite Z_to_bv_lit_self in H. exact H. Qed.

Lemma policy_wa : forall (P : acc -> Prop) a n, P (Z_to_bv 64 a, n) -> P (wa a, n).
Proof. intros; assumption. Qed.

(* [comment removed for export] *)
Ltac policy1 :=
  lazymatch goal with
  | |- ?P (?a, ?n) =>
      (lazymatch a with
       | Z_to_bv 64 _ => idtac
       | wa _ => apply policy_wa
       | _ => apply policy_var
       end);
      first [ assumption
            | LiaA.policy_pick ]        (* [comment removed for export] *)
  end.

Ltac solve_policy :=
  lazymatch goal with
  | |- Forall _ [] => apply Forall_nil
  | |- Forall _ (_ :: _) => apply Forall_cons; [ first [policy1 | idtac] | solve_policy ]
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition v_divu (x y : word) : word :=
  if (bv_unsigned y =? 0)%Z then Z_to_bv 64 (-1) else Z_to_bv 64 (bv_unsigned x / bv_unsigned y).
Definition v_remu (x y : word) : word :=
  if (bv_unsigned y =? 0)%Z then x else Z_to_bv 64 (bv_unsigned x mod bv_unsigned y).

Lemma m_divu : forall a b : word, mul_div M_DIVU a b = v_divu a b.
Proof.
  intros. unfold mul_div, v_divu. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E]; [reflexivity|].
  apply bv_eq. rewrite bv_divu_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 b) as Hb. unfold bv_modulus in *.
  split. { apply Z.div_pos; lia. }
  apply Z.le_lt_trans with (bv_unsigned a); [|lia].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma m_remu : forall a b : word, mul_div M_REMU a b = v_remu a b.
Proof.
  intros. unfold mul_div, v_remu. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E]; [reflexivity|].
  apply bv_eq. rewrite bv_modu_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 b) as Hb. unfold bv_modulus in *.
  pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)) as Hm. lia.
Qed.

(* [comment removed for export] *)
Lemma amo_swap_val : forall {n} (a b : bv n), amo_val AMO_SWAP a b = b.
Proof. reflexivity. Qed.
Lemma amo_add64 : forall a b : word, amo_val AMO_ADD a b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof. intros. cbn [amo_val]. apply bv_add_canon. Qed.
Lemma amo_or64 : forall a b : word, amo_val AMO_OR a b = v_or a b.
Proof. intros. cbn [amo_val]. rewrite <- alu_or. reflexivity. Qed.
Lemma amo_and64 : forall a b : word, amo_val AMO_AND a b = v_and a b.
Proof. intros. cbn [amo_val]. rewrite <- alu_and. reflexivity. Qed.

Lemma extract_le4_low32 : forall v : word, bv_extract 0 32 (le_bytes_to_word (le4 v)) = low32 v.
Proof.
  intros. apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r, le_bytes_to_word_le4, low32_unsigned.
  unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma amo_add32 : forall v s : word,
  (amo_val AMO_ADD (low32 v) (low32 s) : bv 32) = low32 (Z_to_bv 64 (bv_unsigned v + bv_unsigned s)).
Proof.
  intros. cbn [amo_val]. apply bv_eq. rewrite bv_add_unsigned, !low32_unsigned, Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z. change (bv_modulus 64) with (2^32 * 2^32)%Z.
  rewrite <- Zplus_mod. rewrite Z.mod_mod_divide; [reflexivity|]. exists (2^32)%Z. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amo_aligned_w : forall a : Z, (0 <= a < 2^64)%Z -> (a mod 4 = 0)%Z -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Lemma amo_aligned_d : forall a : Z, (0 <= a < 2^64)%Z -> (a mod 8 = 0)%Z -> amo_aligned AD (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Lemma amo_aligned_w_var : forall a : word, (bv_unsigned a mod 4 = 0)%Z -> amo_aligned AW a = true.
Proof. intros a Hm. unfold amo_aligned, amo_bytes. rewrite Hm. reflexivity. Qed.
Lemma amo_aligned_d_var : forall a : word, (bv_unsigned a mod 8 = 0)%Z -> amo_aligned AD a = true.
Proof. intros a Hm. unfold amo_aligned, amo_bytes. rewrite Hm. reflexivity. Qed.

(* [comment removed for export] *)
Ltac amo_arith := first [ assumption | lia | Z.div_mod_to_equations; lia ].
Ltac prove_amo_aligned :=
  lazymatch goal with
  | |- amo_aligned ?wd (Z_to_bv 64 ?E) = true =>
      first [ is_Zlit E; vm_compute; reflexivity
            | lazymatch wd with
              | AW => apply amo_aligned_w; [zsimp; lia | zsimp; amo_arith]
              | AD => apply amo_aligned_d; [zsimp; lia | zsimp; amo_arith]
              end ]
  | |- amo_aligned AW ?a = true => apply amo_aligned_w_var; amo_arith
  | |- amo_aligned AD ?a = true => apply amo_aligned_d_var; amo_arith
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac addr_diff_guard k :=
  let b := eval vm_compute in (andb (Z.leb 0 k) (Z.leb k 4096))%Z in
  lazymatch b with true => k end.

Ltac addr_diff E A ::=
  let k :=
    lazymatch E with
    | Z.add ?X ?c1 =>
        lazymatch A with
        | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
        | X => zlit c1
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    | _ =>
        lazymatch A with
        | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
        | E => constr:(0%Z)
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    end in
  addr_diff_guard k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac exec_cbvA :=
  cbv beta iota zeta delta [lift_resultA lift_result interp_eff interp_eff_accesses drop_access_report access_value accessed_ranges
     exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s].

(* [comment removed for export] *)
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 (z mod 256)].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (256 * 2^56)%Z. change (bv_modulus 8) with 256%Z.
  rewrite Z.rem_mul_r by lia. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Ltac norm_le1_lit z :=
  rewrite (le1_lit z);
  first [ is_Zlit z; let v := eval vm_compute in (z mod 256)%Z in change (z mod 256)%Z with v | idtac ].

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- context [MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _] =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- context [MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _] =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- context [MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _] =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- context [MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _] =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- context [MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _] =>
           norm_le1_lit z; mem_after_store
       end).


(* [comment removed for export] *)
Ltac vnorm_extra i :=
  lazymatch i with
  | Mul M_DIVU _ _ _ => rewrite ?m_divu
  | Mul M_REMU _ _ _ => rewrite ?m_remu
  | Amo _ _ _ _ _ _ _ => rewrite ?load_u64, ?extract_le4_low32, ?amo_swap_val, ?amo_add64, ?amo_add32, ?amo_or64, ?amo_and64, ?sext_extract_le4
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac amo_phase i :=
  lazymatch i with
  | Lr _ _ _ _ _ => amo_phase1
  | Sc _ _ _ _ _ _ => amo_phase1
  | Amo _ _ _ _ _ _ _ => amo_phase1
  | _ => idtac
  end
with amo_phase1 :=
  match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let H := fresh "AL" in
      first [ assert (H : amo_aligned wd a = true) by prove_amo_aligned
            | fail 100 "stepA: cannot prove natural alignment of the atomic access at" a ];
      rewrite H; clear H; cbv beta iota delta [negb];
      exec_cbvA; simp_is_x0; simp_regs;
      (* [comment removed for export] *)
      repeat match goal with
      | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?x)] => rewrite (Z.eqb_refl (bv_unsigned x)); cbv beta iota
      | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
          replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with true by (symmetry; apply Z.eqb_eq; first [reflexivity | zsimp; lia]);
          cbv beta iota
      end
  | _ => idtac
  end.

Ltac stepA_core segs P R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evtA_step;
        [ split; [reflexivity|];
          rewrite (step_genA segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbvA; simp_is_x0; simp_regs; vnorm_for i; amo_phase i;
          try solve_load; vnorm_extra i; try solve_store;
          reflexivity
        | solve_policy
        | simp_regs; vnorm_for i; vnorm_extra i; mem_after_store_opt; fix_lit_store; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac stepA :=
  lazymatch goal with
  | |- evtA ?segs ?P ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => stepA_core segs P R F pc fc rv m ro
  | |- evtA _ _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* [comment removed for export] *)
Ltac step ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro
  | |- evtA ?segs ?P ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => stepA_core segs P R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  | |- evtA _ _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Ltac zstepA := stepA; zsimp.

Ltac fstepsA n :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evtA _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => stepA; fstepsA n'
      | _ => idtac
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac goal_state_mem :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) => m
  | |- evtA _ _ _ (MS _ _ _ _ _ ?m _) => m
  end.

Ltac mem_after_store_gen segs R F pc fc rv m A kn bs ro :=
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
      mem_after_store_gen segs R F pc fc rv m A kn bs ro
  | |- evtA ?segs ?P ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
      mem_after_store_gen segs R F pc fc rv m A kn bs ro
  end.

Ltac mem_after_store_opt ::=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | |- evtA ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac goal_cond :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => c
  | |- evtA _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => c
  end.
Ltac if_true ::= let c := goal_cond in replace c with true; [cbv iota| symmetry; solve_cond].
Ltac if_false ::= let c := goal_cond in replace c with false; [cbv iota| symmetry; solve_cond].
Ltac if_true_by H ::= let c := goal_cond in replace c with true; [cbv iota| symmetry; exact H].
Ltac if_false_by H ::= let c := goal_cond in replace c with false; [cbv iota| symmetry; exact H].
Ltac if_cases H ::= let c := goal_cond in destruct c eqn:H; [ | ].

Ltac concretize_regs ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) => let t := eval vm_compute in R in change R with t
  | |- evtA ?segs ?P ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) => let t := eval vm_compute in R in change R with t
  end.

Ltac getreg n ::=
  let R := lazymatch goal with
           | |- evt _ _ (MS ?R _ _ _ _ _ _) => R
           | |- evtA _ _ _ (MS ?R _ _ _ _ _ _) => R
           end in
  let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
  let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
  lazymatch v with
  | Some ?w => w
  | _ => fail "getreg: register" n "not concrete"
  end.

(* [comment removed for export] *)
Ltac finishA :=
  apply evtA_done;
  lazymatch goal with |- ?P0 ?ms => try unfold P0 end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac finish ::=
  lazymatch goal with
  | |- evtA _ _ _ _ => finishA
  | _ => apply evt_done;
         lazymatch goal with |- ?P ?ms => try unfold P end;
         hnf;
         repeat (lazymatch goal with |- ex _ => eexists end);
         lazymatch goal with
         | |- _ = _ /\ _ => split; [ reflexivity | ]
         | |- _ = _ => reflexivity
         end;
         repeat match goal with |- _ /\ _ => split end; try assumption
  end.

(* [comment removed for export] *)
Ltac ret_pc_lit :=
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  | |- evtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "callA" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtA_cut; [ eapply SPEC | post_call segs m; ret_pc_lit ]
  end.

(* [comment removed for export] *)
Lemma evtA_ecall : forall segs P (Q : machine_state -> Prop) R F pc fc rv m ro w,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
  Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
  evtA segs P Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros segs P Q R F pc fc rv m ro w Hf He HQ.
  eapply evtA_step; [| apply Forall_nil | apply evtA_done; exact HQ].
  split; [reflexivity|]. rewrite (step_ecall_genA segs R F (Z_to_bv 64 pc) fc rv m ro w Hf He). reflexivity.
Qed.

Ltac step_ecallA :=
  lazymatch goal with
  | |- evtA ?segs ?P ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          apply (evtA_ecall segs P Q R F pc fc rv m ro w);
          [ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
      | None => fail "no instruction at" pc
      end
  end.
