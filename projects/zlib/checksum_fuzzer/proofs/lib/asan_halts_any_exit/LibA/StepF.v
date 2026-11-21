(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image Tac Bytes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Export StoreFast Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Export ExecF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


Definition lift_resultF (ro : word -> option byte)
    (r : machine_result (access_report (core * (word -> option byte))))
  : machine_result (access_report machine_state) :=
  match r with
  | MachineOk (mkAccessReport _ (c, m') accs) => MachineOk (mkAccessReport _ (MS_of_core c m' ro) accs)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

Lemma stepF_gen : forall segs R F pc fc rv m ro w i sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  RiscvSemantics.step_accesses segs (MS R F pc fc rv m ro) =
  lift_resultF ro (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m).
Proof.
  intros segs R F pc fc rv m ro w i sz Hf He Hd.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He, Hd. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS].
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) m) as [[[c m'] acc]| |]; reflexivity.
Qed.

Lemma stepF_ecall_gen : forall segs R F pc fc rv m ro w,
  fetch_word segs pc = Some w ->
  is_ecall w = true ->
  RiscvSemantics.step_accesses segs (MS R F pc fc rv m ro) =
  MachineOk (mkAccessReport _ (MSsvc R F pc (if is_x0 17 then w0 else reg_get R 17) fc rv m ro) []).
Proof.
  intros segs R F pc fc rv m ro w Hf He.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He. reflexivity.
Qed.


Lemma rng_acc_litZ' : forall RNG lo len E (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> (1 <=? nz)%Z = true -> (lo <= E /\ E + nz <= lo + len)%Z ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof. intros RNG lo len E n nz H Hn Hz HE. eapply rng_acc_litZ; eauto. apply Z.leb_le. exact Hz. Qed.

Ltac acc_hint := fail.

Lemma nth_error_some_bound : forall {A} (l : list A) k x, nth_error l k = Some x -> (k < length l)%nat.
Proof.
  intros A l k x H. destruct (Nat.lt_ge_cases k (length l)) as [L|L]; [exact L|].
  apply nth_error_None in L. congruence.
Qed.

Ltac acc_enrich :=
  repeat match goal with
  | H : nth_error ?l ?k = Some ?x |- _ =>
      lazymatch goal with
      | _ : (k < length l)%nat |- _ => fail
      | _ => pose proof (nth_error_some_bound l k x H)
      end
  end;
  rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length in *;
  cbn [length] in *.

Ltac alia := first [ lia | acc_enrich; lia ].

Ltac solve_acc_with H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia
      end
  end.

Ltac leftmost E := lazymatch E with Z.add ?X _ => leftmost X | Z.sub ?X _ => leftmost X | _ => E end.

Ltac is_closed_lits E :=
  lazymatch E with
  | Z.add ?a ?b => is_closed_lits a; is_closed_lits b
  | Z.sub ?a ?b => is_closed_lits a; is_closed_lits b
  | _ => is_Zlit E
  end.
Ltac decide_lit_bounds :=
  lazymatch goal with
  | |- (?a <= ?b /\ ?c <= ?d)%Z => split; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity
  end.
Ltac solve_acc_lit H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); decide_lit_bounds
      end
  end.
Ltac mentions T X := lazymatch T with context [X] => idtac end.

Ltac solve_acc1 :=
  first [ acc_hint
        | assumption
        |
          lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
              is_closed_lits E;
              match goal with
              | H : rng RNG ?lo ?len |- _ => is_closed_lits lo; is_closed_lits len; solve_acc_lit H
              end
          end
        |
          lazymatch goal with
          | |- acc_in ?RNG (?a, _) =>
              let E := addr_expr a in let X := leftmost E in
              first [ match goal with
                      | H : rng RNG ?lo _ |- _ => let Y := leftmost lo in constr_eq X Y; solve_acc_with H
                      end
                    | is_var X;
                      match goal with
                      | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; solve_acc_with H
                      end
                    | lazymatch X with bv_unsigned ?r => is_var r;
                        match goal with
                        | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; solve_acc_with H
                        end
                      end ]
          end
        | lazymatch goal with
          | |- acc_in ?RNG _ =>
              match goal with
              | H : rng RNG _ _ |- _ => solve_acc_with H
              end
          end
        |
          lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
              let nz := eval cbv in (Z.of_nat n) in
              match goal with
              | H : rng RNG ?lo ?len |- _ => apply (rng_acc_wrapZ RNG lo len E n nz H (@eq_refl Z nz)); alia
              end
          end
        | lazymatch goal with |- acc_in _ (?a, ?n) => fail 0 "footprint: access" a "width" n "not covered by any [rng] hypothesis" end ].

Ltac solve_accs :=
  lazymatch goal with
  | |- Forall _ nil => apply Forall_nil
  | |- Forall _ (cons _ _) => apply Forall_cons; [ solve_acc1 | solve_accs ]
  | |- ?G => fail 0 "solve_accs: unexpected access side goal" G
  end.

Ltac reglia :=
  first [ lia
        | rewrite ?unsigned_lit by lia; lia
        | rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Ltac solve_rng :=
  lazymatch goal with
  | |- rng ?RNG ?lo' ?len' =>
      first [ assumption
            | eassumption
            | tryif match goal with |- ?G => has_evar G end
              then fail 0 "solve_rng: goal has evars:" lo' len'
              else first [
                           is_closed_lits lo'; is_closed_lits len';
                           match goal with
                           | H : rng RNG ?lo ?len |- _ =>
                               is_closed_lits lo; is_closed_lits len; apply (rng_sub' RNG lo len lo' len' H); decide_lit_bounds
                           end
                         |
                           let X := leftmost lo' in
                           first [ match goal with
                                   | H : rng RNG ?lo ?len |- _ => let Y := leftmost lo in constr_eq X Y; apply (rng_sub' RNG lo len lo' len' H); reglia
                                   end
                                 | first [ is_var X | lazymatch X with bv_unsigned ?r => is_var r end ];
                                   match goal with
                                   | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; apply (rng_sub' RNG lo len lo' len' H); reglia
                                   end ]
                         | match goal with
                           | H : rng RNG ?lo ?len |- _ =>
                               apply (rng_sub' RNG lo len lo' len' H); reglia
                           end
                         | fail 0 "solve_rng: no [rng] hypothesis covers" lo' len' ] ]
  end.


Ltac exec_cbv :=
  cbv beta iota zeta delta [lift_resultF lift_result interp_eff interp_eff_accesses drop_access_report access_value accessed_ranges
     exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s].

Ltac lit_of_nat_in H :=
  repeat match type of H with
  | context [Z.of_nat ?n] =>
      lazymatch n with O => idtac | S _ => idtac end;
      let z := eval vm_compute in (Z.of_nat n) in is_Zlit z; change (Z.of_nat n) with z in H
  end.

Ltac mem_after_store :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    let kz := eval vm_compute in (Z.of_nat kn) in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB; lit_of_nat_in HB;
          change (write_to_mem m (wa (A + Z.of_nat kn)) bs) with (write_to_mem m (wa (A + kz)) bs);
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + kz)) c') in HI;
              [ | exact I
                | change (wa (A + kz)) with (wa (A + Z.of_nat kn));
                  apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          change (wa (A + Z.of_nat kn)) with (wa (A + kz)) in H';
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + kz)%Z (cbytes c');
          footprint_after_store segs m (A + kz)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + kz)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store_fast :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    let kz := eval vm_compute in (Z.of_nat kn) in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; literal_cell_sizes_in HB; cbn [cells_size csize Nat.add] in HB; lit_of_nat_in HB;
          change (write_to_mem m (wa (A + Z.of_nat kn)) bs) with (write_to_mem m (wa (A + kz)) bs);
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + kz)) c') in HI;
              [ | exact I
                | change (wa (A + kz)) with (wa (A + Z.of_nat kn));
                  apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          change (wa (A + Z.of_nat kn)) with (wa (A + kz)) in H';
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          store_facts (A + kz)%Z (cbytes c') ltac:(fun n' Hn Ha Hl =>
            transport_chunks_with segs m (A + kz)%Z (cbytes c') n' Hn Ha Hl;
            footprint_after_store_with segs m (A + kz)%Z (cbytes c') n' Hn Ha Hl);
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + kz)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

Ltac norm_lit_store_bytes :=
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           is_Zlit z; change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]
       end).

Ltac mem_after_store_opt :=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Ltac norm_fcsr :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ ?fce _ _ _) =>
      tryif is_var fce then idtac else
      (let fcn := fresh "fc" in
       let E := fresh "Efc" in
       tryif (let H := fresh "FRM" in
              assert (H : frm0 fce) by prove_frm0;
              repeat match goal with
              | H' : frm0 ?f |- _ => lazymatch f with fce => fail | _ => clear H' end
              end;
              remember fce as fcn eqn:E; clear E;
              try rename H into FRM)
       then idtac
       else (remember fce as fcn eqn:E; clear E))
  | _ => idtac
  end.

Ltac post_step i :=
  lazymatch i with
  | Fari _ _ _ _ _ _ => norm_fcsr
  | Fcmp _ _ _ _ _ => norm_fcsr
  | Fcvt _ _ _ _ _ => norm_fcsr
  | Fsqrt _ _ _ _ => norm_fcsr
  | Fminmax _ _ _ _ _ => norm_fcsr
  | Fma _ _ _ _ _ _ _ => norm_fcsr
  | Csr _ _ _ _ => norm_fcsr
  | CsrI _ _ _ _ => norm_fcsr
  | _ => idtac
  end.

Ltac step_core segs RNG R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply (evtF_step_acc segs RNG);
        [ reflexivity
        | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | solve_accs
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac step :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs RNG R F pc fc rv m ro
  | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Ltac if_true :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; solve_cond]
  end.
Ltac if_false :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; solve_cond]
  end.
Ltac if_true_by H :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; exact H]
  end.
Ltac if_false_by H :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; exact H]
  end.
Ltac if_cases H :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      destruct c eqn:H; [ | ]
  end.

Ltac concretize_regs :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let t := eval vm_compute in R in change R with t
  end.

Ltac zstep := step; zsimp.
Ltac fstep := step.
Ltac fsteps n :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; fsteps n'
      | _ => idtac
      end
  end.


Ltac post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      eapply evtF_cut; [ eapply SPEC | post_call segs m ];
      try (lazymatch goal with |- rng _ _ _ => solve_rng end)
  end.

Ltac is_fp_clause A :=
  lazymatch A with
  | ?A1 /\ _ => is_fp_clause A1
  | @eq ?T _ _ => lazymatch eval hnf in T with machine_state => fail | _ => idtac end
  | rng _ _ _ => idtac
  | _ => let A' := eval hnf in A in
         lazymatch A' with
         | ?A1 /\ _ => is_fp_clause A1
         | @eq ?T _ _ => lazymatch eval hnf in T with machine_state => fail | _ => idtac end
         | forall (b : Z) (j : nat), _ => idtac
         | _ -> _ => idtac
         end
  end.

Ltac fp_clause_solve :=
  first [ reflexivity | assumption | solve_rng
        | lazymatch goal with |- _ /\ _ => split; [fp_clause_solve | fp_clause_solve] end
        | idtac ].

Ltac finish_body :=
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac finish_split_fp body :=
  lazymatch goal with
  | |- ?A /\ ex _ => tryif is_fp_clause A then (split; [ fp_clause_solve | hnf; body ]) else body
  | |- ?A /\ (@eq ?T _ _ /\ _) =>
      tryif (lazymatch eval hnf in T with machine_state => is_fp_clause A end)
      then (split; [ fp_clause_solve | hnf; body ]) else body
  | _ => body
  end.

Ltac finish :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  finish_split_fp finish_body.

Ltac finish2_body :=
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac finish2 :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  finish_split_fp finish2_body.

Ltac store_done :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    try (lazymatch goal with
    | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
    end);
    let HBa := fresh "HBarr" in
    try (let X := lazymatch E with Z.add (Z.add ?X _) _ => X | Z.add ?X _ => X | _ => E end in
         first [ lazymatch goal with
                 | H : u32arr segs m X ?xs |- _ => pose proof (u32arr_bound segs m X xs H) as HBa
                 | H : u8arr segs m X ?xs |- _ => pose proof (u8arr_bound segs m X xs H) as HBa
                 | H : u64arr segs m X ?xs |- _ => pose proof (u64arr_bound segs m X xs H) as HBa
                 end
               | lazymatch E with Z.add (Z.add ?X2 _) _ =>
                   lazymatch goal with
                   | H : u32arr segs m X2 ?xs |- _ => pose proof (u32arr_bound segs m X2 xs H) as HBa
                   | H : u8arr segs m X2 ?xs |- _ => pose proof (u8arr_bound segs m X2 xs H) as HBa
                   | H : u64arr segs m X2 ?xs |- _ => pose proof (u64arr_bound segs m X2 xs H) as HBa
                   end
                 end ]);
    transport_chunks segs m E bs;
    footprint_after_store segs m E bs;
    try clear HBa;
    let m' := fresh "m" in
    remember (write_to_mem m (wa E) bs) as m' eqn:Heqm;
    clear Heqm;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    try clear m
  end.


Ltac getreg n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
      lazymatch v with
      | Some ?w => w
      | _ => fail "getreg: register" n "not concrete"
      end
  end.

Ltac name_reg_tac n X :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e => name_as_tac X e
  | _ => fail "name_reg: register" n "holds" w
  end.
Tactic Notation "name_reg" constr(n) ident(X) := name_reg_tac n X.

Ltac model_reg_tac n X mexpr :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      first [ constr_eq e mexpr
            | replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
                by (first [ f_equal; zeq_fast
                          | rewrite Z_to_bv_land64; f_equal; zeq_fast
                          | f_equal; zeq
                          | rewrite Z_to_bv_land64; f_equal; zeq
                          | apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq
                          | apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
                          | apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
      name_as_tac X mexpr
  | _ => fail "model_reg: register" n "holds" w
  end.
Tactic Notation "model_reg" constr(n) ident(X) constr(mexpr) := model_reg_tac n X mexpr.

Ltac reg_val r :=
  lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.


Ltac amo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  end.

Ltac amo_step :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.


Lemma evtF_ecall : forall segs RNG (Q : machine_state -> Prop) R F pc fc rv m ro w,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
  Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
  evtF segs RNG Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros segs RNG Q R F pc fc rv m ro w Hf He HQ.
  eapply evtF_step_acc; [reflexivity| | apply Forall_nil | apply evtF_done; exact HQ].
  rewrite (stepF_ecall_gen segs R F (Z_to_bv 64 pc) fc rv m ro w Hf He). reflexivity.
Qed.

Ltac step_ecall :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          apply (evtF_ecall segs RNG Q R F pc fc rv m ro w);
          [ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
      | None => fail "no instruction at" pc
      end
  end.

Lemma stk_lo_nonneg : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof. intros segs m lo hi (H & _). exact H. Qed.

Ltac name_sp sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
        apply unsigned_lit; lia).

Ltac unname_sp :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1';
      repeat match goal with K : context [bv_unsigned sp1] |- _ => tryif constr_eq K H then fail else rewrite H in K end;
      try rewrite H; clear H; subst sp1
  end.

Tactic Notation "call_sp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF _ _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | _ => call SPEC
  end.

Ltac sys_finish :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  finish_split_fp finish2_body.

From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Import Bool.
Import Ltac2.Bool.BoolNotations.
Set Default Proof Mode "Classic".


Fixpoint eff_fp (P : word * nat -> Prop) (t : eff) : Prop :=
  match t with
  | ELoad n a k => P (a, width_bytes n) /\ (forall v, eff_fp P (k v))
  | EStore n a v k => P (a, width_bytes n) /\ eff_fp P k
  | _ => True
  end.

Lemma eff_fp_sound : forall segs P t m c m',
  interp_eff0 segs t m = MachineOk (c, m') -> eff_fp P t ->
  exists accs, interp_eff_accesses segs t m = MachineOk (mkAccessReport _ (c, m') accs) /\ Forall P accs.
Proof.
  intros segs P t. induction t as [c0|c0|c0|c0|c0|c0|n a k IH|n a v k IH]; intros m c m' H FP;
    cbn [interp_eff0 interp_eff_accesses eff_fp] in *; try discriminate.
  - injection H as <- <-. eexists. split; [reflexivity|constructor].
  - destruct FP as [Pa FPk]. destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|];
      [|destruct (RiscvSemantics.range_meets_vvar segs a (width_bytes n)); discriminate].
    destruct (IH _ m c m' H (FPk _)) as (accs & E & F). rewrite E. cbn [access_value accessed_ranges].
    eexists. split; [reflexivity|]. constructor; assumption.
  - destruct FP as [Pa FPk]. destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (IH _ c m' H FPk) as (accs & E & F). rewrite E. cbn [access_value accessed_ranges].
    eexists. split; [reflexivity|]. constructor; assumption.
Qed.

Lemma eff_fp_load_intro : forall (P : word * nat -> Prop) n a k,
  P (a, width_bytes n) -> (forall v, eff_fp P (k v)) -> eff_fp P (ELoad n a k).
Proof. intros P n a k H1 H2. split; assumption. Qed.
Lemma eff_fp_store_intro : forall (P : word * nat -> Prop) n a v k,
  P (a, width_bytes n) -> eff_fp P k -> eff_fp P (EStore n a v k).
Proof. intros P n a v k H1 H2. split; assumption. Qed.

Lemma sf_acc_conv : forall RNG (a a' : word) (n : nat), a = a' -> Forall (acc_in RNG) [(a', n)] -> acc_in RNG (a, n).
Proof. intros RNG a a' n -> H. inversion H; assumption. Qed.


Lemma sf_evtF_step : forall segs RNG (Q : machine_state -> Prop) R F pc fc rv m ro w i sz ms1,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
  lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  eff_fp (acc_in RNG) (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) ->
  evtF segs RNG Q ms1 -> evtF segs RNG Q (MS R F pc fc rv m ro).
Proof.
  intros segs RNG Q R F pc fc rv m ro w i sz ms1 Hf He Hd Hx FP K.
  destruct (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) as [[c m']| |] eqn:E0; cbn [lift_result] in Hx; try discriminate.
  injection Hx as <-.
  destruct (eff_fp_sound segs (acc_in RNG) _ m c m' E0 FP) as (accs & EA & FA).
  eapply (evtF_step_acc segs RNG Q _ (MS_of_core c m' ro) accs); [reflexivity| | exact FA | exact K].
  rewrite (stepF_gen segs R F pc fc rv m ro w i sz Hf He Hd). rewrite EA. reflexivity.
Qed.

Lemma sf_evtF_mem : forall segs RNG (Q : machine_state -> Prop) R F pc fc rv (m m' ro : word -> option byte),
  m = m' -> evtF segs RNG Q (MS R F pc fc rv m' ro) -> evtF segs RNG Q (MS R F pc fc rv m ro).
Proof. intros. subst. assumption. Qed.


Ltac2 rec pos_smallF (c : constr) (fuel : int) : bool :=
  if Int.le fuel 0 then false else
  lazy_match! c with
  | xH => true
  | xO ?p => pos_smallF p (Int.sub fuel 1)
  | xI ?p => pos_smallF p (Int.sub fuel 1)
  | _ => false
  end.
Ltac2 zlit_smallF (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App _ args => if Int.equal (Array.length args) 1 then pos_smallF (Array.get args 0) 30 else false
  | _ => false
  end.
Ltac2 zlit_addF (a : constr) (b : constr) : constr :=
  if (if zlit_smallF a then zlit_smallF b else false) then zlit_add a b
  else let t := Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(Z.add)) [| a; b |]) in eval cbv in $t.
Ltac2 direct_add_tailF (x : sf_ctx) (z : bool) (v : constr) (a : constr) (n : constr) (imm : constr) (base : constr)
    : (constr * constr) option :=
  let ztobv := gref reference:(Z_to_bv) in
  let n64 := x.(c_n64) in
  let wd := mk_app (gref reference:(bv)) [| n64 |] in
  let zt := gref reference:(Z) in
  let etrans a b c p q := mk_app (gref reference:(eq_trans)) [| wd; a; b; c; p; q |] in
  let fzw (e1 : constr) (e2 : constr) (p : constr) :=
    mk_app (gref reference:(f_equal)) [| zt; wd; mk_app ztobv [| n64 |]; e1; e2; p |] in
      if bad (ctx_mode x z) a then None else
      let k := signed_lit imm in
      let zadd p q := mk_app (gref reference:(Z.add)) [| p; q |] in
      let uns t := mk_app (gref reference:(bv_unsigned)) [| n64; t |] in
      match Constr.Unsafe.kind a with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal a (gref reference:(w0)) then Some (mk_app ztobv [| n64; k |], base) else None
      | Constr.Unsafe.Var id =>
          (match Control.hyp_value id with
           | Some _ => None
           | None =>
               if zlit_eq0 k then Some (a, etrans v (mk_app ztobv [| n64; zadd (uns a) k |]) a base (mk_app (gref reference:(Z_to_bv_plus0)) [| a |]))
               else Some (mk_app ztobv [| n64; zadd (uns a) k |], base)
           end)
      | Constr.Unsafe.App h args =>
          if Constr.equal h ztobv then
            if Int.equal (Array.length args) 2 then
              if Constr.equal (Array.get args 0) n64 then
                let e := Array.get args 1 in
                let p1 := etrans v (mk_app ztobv [| n64; zadd (uns a) k |]) (mk_app ztobv [| n64; zadd e k |]) base
                                 (mk_app (gref reference:(unsigned_Z_to_bv_add)) [| e; k |]) in
                if is_zlit e then
                  let c := zlit_addF e k in
                  (if z then (lazy_match! (eval cbv in (Z.leb 18446744073709551616 $c)) with true => None | _ => Some (mk_app ztobv [| n64; c |], p1) end)
                   else Some (mk_app ztobv [| n64; c |], p1))
                else if (if head_k (x.(k_zadd)) e then is_zlit (arg_last e) else false) then
                  let ea := app_args e in
                  let y := Array.get ea 0 in let a' := Array.get ea 1 in
                  let c' := zlit_addF a' k in
                  let p2 := etrans v (mk_app ztobv [| n64; zadd e k |]) (mk_app ztobv [| n64; zadd y c' |]) p1
                              (fzw (zadd e k) (zadd y (zadd a' k))
                                   (mk_app (gref reference:(eq_sym)) [| zt; zadd y (zadd a' k); zadd e k;
                                                                       mk_app (gref reference:(Z.add_assoc)) [| y; a'; k |] |])) in
                  if zlit_eq0 c' then
                    let p3 := etrans v (mk_app ztobv [| n64; zadd y c' |]) (mk_app ztobv [| n64; y |]) p2
                                (fzw (zadd y c') y (mk_app (gref reference:(Z.add_0_r)) [| y |])) in
                    (if head_k (x.(k_unsigned)) y then
                       (let zz := arg_last y in
                        if Constr.equal (sf_get (app_args y) 0) n64 then
                          Some (zz, etrans v (mk_app ztobv [| n64; y |]) zz p3 (mk_app (gref reference:(Z_to_bv_lit_self)) [| zz |]))
                        else None)
                     else Some (mk_app ztobv [| n64; y |], p3))
                  else Some (mk_app ztobv [| n64; zadd y c' |], p2)
                else if zlit_eq0 k then
                  Some (a, etrans v (mk_app ztobv [| n64; zadd e k |]) a p1 (fzw (zadd e k) e (mk_app (gref reference:(Z.add_0_r)) [| e |])))
                else Some (mk_app ztobv [| n64; zadd e k |], p1)
              else None
            else None
          else None
      | _ => None
      end.
Ltac2 direct_addiF (x : sf_ctx) (z : bool) (v : constr) : (constr * constr) option :=
  lazy_match! v with
  | alu64 ALU_ADD ?a (@sext ?n 64 ?imm) => direct_add_tailF x z v a n imm (mk_app (gref reference:(alu_addi)) [| a; n; imm |])
  | _ => None
  end.
Ltac2 direct_addrF (x : sf_ctx) (v : constr) : (constr * constr) option :=
  lazy_match! v with
  | @bv_add 64 ?a (@sext ?n 64 ?imm) => direct_add_tailF x false v a n imm (mk_app (gref reference:(b_addsext)) [| a; n; imm |])
  | _ => None
  end.
Ltac2 sf_direct_loadF (x : sf_ctx) (z : bool) (segs : constr) (m : constr) (a : constr) (nb : constr) (fl : constr) (n : constr)
    : (constr * constr) option :=
  if Bool.neg (Constr.equal n (x.(c_n64))) then None
  else if Bool.neg (Constr.equal nb '8%nat) then None
  else if Bool.neg (Constr.equal fl '(fun bs : list byte => @bv_extract 64 0 64 (le_bytes_to_word bs))) then None
  else
  match direct_addrF x a with
  | None => None
  | Some (an, pn) =>
      let e := sf_addr_expr x an in
      match sf_find_chunk x segs m e nb with
      | None => None
      | Some (h, aA, cs, kn, c0) =>
          lazy_match! c0 with
          | C8 ?v =>
              let sv := mk_app (gref reference:(Some)) [| mk_app (gref reference:(bv)) [| x.(c_n64) |]; v |] in
              if bad (ctx_mode x false) sv then None
              else if (if z then (let xz := ctx_mode x true in if bad xz sv then true else (xz.(idioms_seen)).(contents)) else false) then None
              else
              match sf_addr_premise x a an pn aA kn with
              | None => None
              | Some pa =>
                  let ocell := mk_app (gref reference:(option)) [| gref reference:(cell) |] in
                  let pc := mk_app (gref reference:(eq_refl)) [| ocell; mk_app (gref reference:(Some)) [| gref reference:(cell); c0 |] |] in
                  Some (v, mk_app (gref reference:(sf_load8_direct)) [| segs; m; aA; cs; kn; v; a; h; pc; pa |])
              end
          | _ => None
          end
      end
  end.
Ltac2 sf_direct_storeF (x : sf_ctx) (segs : constr) (m : constr) (a : constr) (nb : constr) (n : constr) (v : constr)
    : (constr * constr) option :=
  if Bool.neg (Constr.equal n (x.(c_n64))) then None
  else if Bool.neg (Constr.equal nb '8%nat) then None
  else if Bool.neg (match Constr.Unsafe.kind v with
                    | Constr.Unsafe.Var id => (match Control.hyp_value id with Some _ => false | None => true end)
                    | Constr.Unsafe.Constant _ _ => Constr.equal v (gref reference:(w0))
                    | Constr.Unsafe.App h args =>
                        if is_k (x.(k_ztobv)) h then
                          (if Int.equal (Array.length args) 2 then
                             (if Constr.equal (Array.get args 0) (x.(c_n64)) then Bool.neg (zcons (Array.get args 1)) else false)
                           else false)
                        else false
                    | _ => false
                    end) then None
  else
  match direct_addrF x a with
  | None => None
  | Some (an, pn) =>
      let e := sf_addr_expr x an in
      match sf_find_chunk x segs m e nb with
      | None => None
      | Some (h, aA, cs, kn, c0) =>
          let sz := eval cbv beta iota delta [csize] in (csize $c0) in
          if Bool.neg (Constr.equal sz '8%nat) then None else
          let wa_ := mk_app (gref reference:(wa)) [| mk_app (gref reference:(Z.add)) [| aA; mk_app (gref reference:(Z.of_nat)) [| kn |] |] |] in
          let isw0 := Constr.equal v (gref reference:(w0)) in
          let mn := if isw0 then mk_app (gref reference:(write_to_mem)) [| m; wa_; mk_app (gref reference:(Z_to_le_bytes)) [| '8%nat; gref reference:(Z0) |] |]
                    else mk_app (gref reference:(write_to_mem)) [| m; wa_; mk_app (gref reference:(Lib.Mem.le8)) [| v |] |] in
          let sm := mk_app (gref reference:(Some)) [| '(word -> option byte); mn |] in
          if (if isw0 then (if bad (ctx_mode x false) wa_ then true else bad (ctx_mode x false) m) else bad (ctx_mode x false) sm) then None else
          match sf_addr_premise x a an pn aA kn with
          | None => None
          | Some pa =>
              let ocell := mk_app (gref reference:(option)) [| gref reference:(cell) |] in
              let pc := mk_app (gref reference:(eq_refl)) [| ocell; mk_app (gref reference:(Some)) [| gref reference:(cell); c0 |] |] in
              let pz := mk_app (gref reference:(eq_refl)) [| gref reference:(nat); '8%nat |] in
              if isw0 then Some (mn, mk_app (gref reference:(sf_store8_direct0)) [| segs; m; aA; cs; kn; c0; a; h; pc; pz; pa |])
              else Some (mn, mk_app (gref reference:(sf_store8_direct)) [| segs; m; aA; cs; kn; c0; a; v; h; pc; pz; pa |])
          end
      end
  end.

Ltac2 sfF_step_ (ph : int ref) (z : bool) : unit :=
  let stop (k : int) := ph.(contents) := k; stop k in
  lazy_match! goal with
  | [ |- evtF ?segs ?rng ?q (MS ?r ?f (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) ] =>
    stop 1;
    let fw := tm "fetch" (fun () => eval vm_compute in (fetch_word $segs (Z_to_bv 64 $pc))) in
    let w := lazy_match! fw with Some ?w => w | _ => sf_fail "no instruction" end in
    (match reg_int w with
     | Some n => if Int.equal n 115 then sf_fail "ecall" else ()
     | None => let ec := eval vm_compute in (is_ecall $w) in (lazy_match! ec with false => () | _ => sf_fail "ecall" end)
     end);
    let d := tm "decode" (fun () => eval vm_compute in (decode_any $w)) in
    let (i, sz) := lazy_match! d with Some (?i, ?sz) => (i, sz) | _ => sf_fail "undecodable" end in
    let rd := lazy_match! i with
      | OpImm _ ?rd _ _ => Some rd | ShiftImm _ ?rd _ _ => Some rd | Op _ ?rd _ _ => Some rd | OpImm32 ?rd _ _ => Some rd
      | ShiftImm32 _ ?rd _ _ => Some rd | Op32 _ ?rd _ _ => Some rd | Lui ?rd _ => Some rd | Auipc ?rd _ => Some rd
      | Mul _ ?rd _ _ => Some rd | Mul32 _ ?rd _ _ => Some rd | Jal ?rd _ => Some rd | Jalr ?rd _ _ => Some rd
      | Load _ _ ?rd _ _ => Some rd
      | Branch _ _ _ _ => None | Store _ _ _ _ => None
      | _ => sf_fail "unsupported instruction"
      end in
    let rd := match rd with
      | Some rd => (match reg_int rd with Some n => if Int.equal n 0 then None else Some rd | None => sf_fail "rd" end)
      | None => None
      end in
    (if is_concrete_map r then () else sf_fail "symbolic register file");
    stop 2;
    let body := tm "exec_abs" (fun () => exec_abs sz i f pc fc rv) in
    let ru := lazy_match! r with mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eval cbv beta iota delta [mkR] in $r | _ => r end in
    let hit := { contents := false } in
    let body := tm "resolve" (fun () => resolve (kof reference:(reg_get)) (kof reference:(bvmap_set)) ru 0 body hit) in
    let rnew := if hit.(contents) then ru else r in
    let body := Constr.Unsafe.substnl [rnew] 0 body in
    stop 3;
    let x := tm "mk_ctx" (fun () => mk_ctx z) in
    let qchk := match Constr.Unsafe.kind q with Constr.Unsafe.Evar _ _ => [] | _ => [q] end in
    let trig := { contents := [] } in
    let bad_t (t : constr) : bool :=
      let id0 := (x.(idioms_seen)).(contents) in
      (x.(idioms_seen)).(contents) := false;
      let r := bad x t in
      (if (x.(idioms_seen)).(contents) then (if r then () else trig.(contents) := t :: trig.(contents))
       else (x.(idioms_seen)).(contents) := id0);
      (if id0 then (x.(idioms_seen)).(contents) := true else ());
      r in
    (x.(qmode)).(contents) := true;
    (if tm "rest" (fun () => List.exist (fun t => if bad_t t then (if sf_debug then printf "STEPFAST-BADREST: %t@ CULPRIT: %t" t (bad_culprit x t) else ()); true else false)
                                        qchk) then ((x.(qmode)).(contents) := false; sf_fail "rest not normal") else ());
    (x.(qmode)).(contents) := false;
    (if tm "rest" (fun () => List.exist (fun t => if bad_t t then (if sf_debug then printf "STEPFAST-BADREST: %t@ CULPRIT: %t" t (bad_culprit x t) else ()); true else false)
                                        [f; fc; rv; m; ro]) then sf_fail "rest not normal" else ());
    (if List.exist (fun t => let t' := eval cbv delta [mkR] in $t in if Constr.equal t t' then false else true) [f; fc; rv; m; ro; ru]
     then sf_fail "mkR in state" else ());
    let rdpath := match rd with Some rd => Some (key_path rd) | None => None end in
    stop 4;
    let dirty := tm "dirty" (fun () => List.rev (dirty_leaves x trig rdpath rnew [] [])) in
    stop 5;
    (match trig.(contents) with
     | [] => ()
     | tl =>
       if z then
         (if tm "idioms" (fun () => idioms_hit (List.fold_left (fun acc t => '(($acc, $t))) 'tt (List.rev tl)))
          then sf_fail "idioms" else ())
       else ()
     end);
    let ops := lazy_match! i with
      | OpImm ALU_ADD _ ?a _ => [a] | Op ALU_ADD _ ?a ?b => [a; b]
      | Jalr _ ?a _ => [a] | Load _ _ _ ?a _ => [a] | Store _ ?a _ _ => [a]
      | _ => []
      end in
    let susp_op := List.exist (fun k => match reg_int k with
                             | Some 0 => false
                             | Some _ => let l := tree_get (key_path k) ru in suspicious x l
                             | None => true
                             end) ops in
    (if (x.(uz_seen)).(contents) then
       (if susp_op then
          ((if sf_debug then List.iter (fun k => match reg_int k with Some 0 => () | Some _ => printf "STEPFAST-SUSP: %t" (tree_get (key_path k) ru) | None => () end) ops else ());
           sf_fail "suspicious operand")
        else if List.exist (fun (_, l) => risky x l) dirty then sf_fail "risky dirty leaf" else ())
     else ());
    let dirty := List.map (fun (p, l) => (p, leaf_cbv l)) dirty in
    let iv := Ltac1.of_constr i in
    let (fwp, ecp, dcp) := tm "vmeqs" (fun () =>
      let bv32 := mk_app (gref reference:(bv)) [| x.(c_n32) |] in
      let obv32 := mk_app (gref reference:(option)) [| bv32 |] in
      let iz := mk_app (gref reference:(prod)) [| gref reference:(instr); gref reference:(Z) |] in
      (vm_eq obv32 (mk_app (gref reference:(fetch_word)) [| segs; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |] |])
                   (mk_app (gref reference:(Some)) [| bv32; w |]),
       vm_eq (gref reference:(bool)) (mk_app (gref reference:(is_ecall)) [| w |]) (gref reference:(false)),
       vm_eq (mk_app (gref reference:(option)) [| iz |]) (mk_app (gref reference:(decode_any)) [| w |])
             (mk_app (gref reference:(Some)) [| iz; mk_app (gref reference:(pair)) [| gref reference:(instr); gref reference:(Z); i; sz |] |]))) in
    let mr := gref reference:(machine_state) in
    let mrr := mk_app (gref reference:(machine_result)) [| mr |] in
    let ok := gref reference:(MachineOk) in
    let cms := gref reference:(MS) in
    let wd := mk_app (gref reference:(bv)) [| x.(c_n64) |] in
    let ty_mem := '(word -> option byte) in
    let clear_hyps := { contents := [] } in
    let joint (pass : unit -> unit) (l : (constr * constr) list) : constr list * constr :=
      let (ty, t) := tup l in
      let (h, tn) := tm "norm" (fun () => small_goal pass t ty) in
      (if sf_timing then printf "NORMED %t ~> %t" t tn else ());
      clear_hyps.(contents) := h :: clear_hyps.(contents);
      (untup (List.length l) tn, Control.hyp h) in
    let dpaths := List.map (fun (p, _) => p) dirty in
    let draws := List.map (fun (_, l) => l) dirty in
    stop 6;
    let accp := mk_app (gref reference:(acc_in)) [| rng |] in
    let acc_cert (a : constr) (nb : constr) : constr :=
      let (an, pn) := match direct_addrF x a with
        | Some (an, pn) => (an, pn)
        | None =>
            let vt := mk_vt x in
            let (h, an) := tm "normaddr" (fun () => small_goal (fun () => sf_vnorm_for2 vt i) a wd) in
            clear_hyps.(contents) := h :: clear_hyps.(contents);
            (an, Control.hyp h)
        end in
      let pty := '(prod word nat) in
      let ent := mk_app (gref reference:(pair)) [| wd; gref reference:(nat); an; nb |] in
      let lst := mk_app (gref reference:(cons)) [| pty; ent; mk_app (gref reference:(nil)) [| pty |] |] in
      let fty := mk_app (gref reference:(Forall)) [| pty; accp; lst |] in
      let h := Fresh.in_goal @sfA in
      let hv := Ltac1.of_ident h in
      let tyv := Ltac1.of_constr fty in
      tm "accs" (fun () => ltac1:(hv tyv |- assert (hv : tyv) by solve_accs) hv tyv);
      clear_hyps.(contents) := h :: clear_hyps.(contents);
      mk_app (gref reference:(sf_acc_conv)) [| rng; a; an; nb; pn; Control.hyp h |] in
    let (eqp, ms1, fpp) := lazy_match! body with
    | EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1) =>
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        let rdc := match rdpath with
          | Some p => [(p, tree_get p r1)]
          | None => (if Constr.equal r1 rnew then () else sf_fail "changed registers"); []
          end in
        let lcomps := List.append rdc dirty in
        stop 61;
        let dpc := tm "direct_pc" (fun () => direct_pc x i pc sz pc1) in
        stop 62;
        let pcsmall := match dpc with None => true | _ => false end in
        let raws := List.append (List.map (fun (_, v) => v) lcomps) (if pcsmall then [pc1] else []) in
        let k := List.length raws in
        (match raws with [] => () | _ => () end);
        let (norms, hj) := match raws with
          | [] => ([], gref reference:(I))
          | [v] =>
              (match (lazy_match! i with OpImm ALU_ADD _ _ _ => tm "direct" (fun () => direct_addiF x z v) | _ => None end) with
               | Some (vn, pf) => ([vn], pf)
               | None => joint (fun () => sf_passes x z i) [(wd, v)]
               end)
          | _ => joint (fun () => sf_passes x z i) (List.map (fun v => (wd, v)) raws)
          end in
        let lnorms := List.firstn (List.length lcomps) norms in
        let pcn := match dpc with
          | Some (pcn, _) => pcn
          | None => List.last norms
          end in
        let r1n := List.fold_left2 (fun t (p, _) vn => tree_set p vn t) r1 lcomps lnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
        stop 63;
        let e1 :=
          match raws with
          | [] => None
          | _ =>
              let tys := List.map (fun _ => wd) raws in
              let projs := tup_proj tys (mk_rel 1) in
              let lprojs := List.firstn (List.length lcomps) projs in
              let rh := List.fold_left2 (fun t (p, _) pr => tree_set p pr t) r1 lcomps lprojs in
              let pch := if pcsmall then List.last projs else (match dpc with Some (_, None) => pcn | _ => pc1 end) in
              let fn := mk_lam @t (tup_ty tys) (mk_app ok [| mr; mk_app cms [| rh; f; pch; fc; rv; m; ro |] |]) in
              let (_, traw) := tup (List.map (fun v => (wd, v)) raws) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) norms) in
              Some (mk_app (gref reference:(sf_congT)) [| tup_ty tys; fn; traw; tnorm; hj |], pch)
          end in
        let eqp := match dpc with
          | Some (_, Some pf) =>
              let fn2 := mk_lam @y wd (mk_app ok [| mr; mk_app cms [| r1n; f; mk_rel 1; fc; rv; m; ro |] |]) in
              let e2 := mk_app (gref reference:(sf_cong1)) [| fn2; pc1; pcn; pf |] in
              (match e1 with
               | None => e2
               | Some (e, _) =>
                   mk_app (gref reference:(sf_transMR)) [| mk_app ok [| mr; mk_app cms [| r1; f; pc1; fc; rv; m; ro |] |];
                             mk_app ok [| mr; mk_app cms [| r1n; f; pc1; fc; rv; m; ro |] |]; mk_app ok [| mr; ms1 |]; e; e2 |]
               end)
          | _ =>
              (match e1 with
               | None => mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |]
               | Some (e, _) => e
               end)
          end in
        (eqp, ms1, gref reference:(I))
    | ELoad ?n ?a ?kk =>
        (let q' := eval cbv beta iota delta [tset mkR] in $q in if Constr.equal q q' then () else sf_fail "load: Q has mkR/redexes");
        let rdv := match rd with Some rd => rd | None => sf_fail "load to x0" end in
        let rp := match rdpath with Some p => p | None => sf_fail "load to x0" end in
        let (r1, f1, pc1, fc1, rv1) := match Constr.Unsafe.kind kk with
          | Constr.Unsafe.Lambda _ kb =>
              lazy_match! kb with
              | EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1) => (r1, f1, pc1, fc1, rv1)
              | _ => sf_fail "load shape"
              end
          | _ => sf_fail "load shape"
          end in
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        let fv := match Constr.Unsafe.kind r1 with
          | Constr.Unsafe.App h args => if Int.equal (Array.length args) 5 then sf_get args 3 else sf_fail "load shape"
          | _ => sf_fail "load shape"
          end in
        let nb := eval cbv beta iota delta [width_bytes] in (width_bytes $n) in
        let ext := match Constr.Unsafe.kind '(fun bs : list byte => @bv_extract 64 0 $n (le_bytes_to_word bs)) with
          | Constr.Unsafe.Lambda _ eb => eb
          | _ => sf_fail "ext"
          end in
        let fl := mk_lam @bs '(list byte) (Constr.Unsafe.substnl [ext] 0 fv) in
        let lg := mk_app (gref reference:(sf_load_goal)) [| segs; m; a; nb; fl |] in
        let owd := mk_app (gref reference:(option)) [| wd |] in
        let direct := match draws with [] => tm "directld" (fun () => sf_direct_loadF x z segs m a nb fl n) | _ => None end in
        (if sf_timing then (match direct with Some _ => printf "DIRECT-LD yes" | None => printf "DIRECT-LD no %t draws %i" i (List.length draws) end) else ());
        let (norms, hj) := match direct with
          | Some (vl0, pf) => ([mk_app (gref reference:(Some)) [| wd; vl0 |]], pf)
          | None =>
              let vt := mk_vt x in
              joint (fun () => sf_norm_load2 vt z i) ((owd, lg) :: List.map (fun v => (wd, v)) draws)
          end in
        let (vl, dnorms) := match norms with
          | sv :: dn => (lazy_match! sv with Some ?e => e | _ => sf_fail "load result" end, dn)
          | [] => sf_fail "load result"
          end in
        let pcn := match direct_pc x i pc sz pc1 with Some (pcn, None) => pcn | _ => sf_fail "load pc" end in
        let core_pair := mk_app (gref reference:(prod)) [| gref reference:(core); ty_mem |] in
        let kt := mk_lam @x wd (mk_app ok [| core_pair;
                     mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem;
                        mk_app (gref reference:(Core)) [| mk_app (gref reference:(bvmap_set)) [| '5%N; wd; rdv; mk_rel 1; rnew |]; f; pc1; fc; rv |]; m |] |]) in
        let r1v := tree_set rp vl rnew in
        let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) r1v dpaths dnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
        let (h1, ek) := match draws with
          | [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |])
          | _ =>
              let tys := List.map (fun _ => wd) draws in
              let tyl := tup_ty tys in
              let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
              let sv := mk_app (gref reference:(Some)) [| wd; vl |] in
              let h1 := pair_eq1 owd tyl lg sv traw tnorm hj in
              let h2 := pair_eq2 owd tyl lg sv traw tnorm hj in
              let projs := tup_proj tys (mk_rel 1) in
              let rh := List.fold_left2 (fun t p pr => tree_set p pr t) r1v dpaths projs in
              let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| rh; f; pcn; fc; rv; m; ro |] |]) in
              (h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |])
          end in
        let accc := acc_cert a nb in
        let fpp := mk_app (gref reference:(eff_fp_load_intro)) [| accp; n; a; kk; accc;
                     mk_lam @v (mk_app (gref reference:(bv)) [| n |]) (gref reference:(I)) |] in
        (mk_app (gref reference:(sf_install_load)) [| segs; ro; m; a; nb; fl; vl; kt; mk_app ok [| mr; ms1 |]; h1; ek |], ms1, fpp)
    | EStore ?n ?a ?v (EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1)) =>
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        (if Constr.equal r1 rnew then () else sf_fail "store changed registers");
        let nb := eval cbv beta iota delta [width_bytes] in (width_bytes $n) in
        let bs := mk_app (gref reference:(Z_to_le_bytes)) [| nb; mk_app (gref reference:(bv_unsigned)) [| n; v |] |] in
        let sg := mk_app (gref reference:(sf_store_goal)) [| segs; m; a; nb; bs |] in
        let omem := mk_app (gref reference:(option)) [| ty_mem |] in
        let direct := match draws with [] => tm "directst" (fun () => sf_direct_storeF x segs m a nb n v) | _ => None end in
        (if sf_timing then (match direct with Some _ => printf "DIRECT-ST yes" | None => printf "DIRECT-ST no %t draws %i v %t" i (List.length draws) v end) else ());
        let (norms, hj) := match direct with
          | Some (mn0, pf) => ([mk_app (gref reference:(Some)) [| ty_mem; mn0 |]], pf)
          | None =>
              let vt := mk_vt x in
              joint (fun () => sf_norm_store2 vt i) ((omem, sg) :: List.map (fun v => (wd, v)) draws)
          end in
        let (mn, dn1) := match norms with
          | sm :: dn => (lazy_match! sm with Some ?e => e | _ => sf_fail "store result" end, dn)
          | [] => sf_fail "store result"
          end in
        let (dnorms, hz) := match draws with
          | [] => ([], None)
          | _ => if z then
                   (let (dn2, h2) := joint (fun () => sf_zpasses x) (List.map (fun v => (wd, v)) dn1) in (dn2, Some (dn1, h2)))
                 else (dn1, None)
          end in
        let pcn := match direct_pc x i pc sz pc1 with Some (pcn, None) => pcn | _ => sf_fail "store pc" end in
        let core_pair := mk_app (gref reference:(prod)) [| gref reference:(core); ty_mem |] in
        let kt := mk_lam @x ty_mem (mk_app ok [| core_pair;
                     mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem; mk_app (gref reference:(Core)) [| rnew; f; pc1; fc; rv |]; mk_rel 1 |] |]) in
        let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) rnew dpaths dnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; mn; ro |] in
        let (h1, ek) := match draws with
          | [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |])
          | _ =>
              let tys := List.map (fun _ => wd) draws in
              let tyl := tup_ty tys in
              let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
              let (_, tn1) := tup (List.map (fun v => (wd, v)) dn1) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
              let sm := mk_app (gref reference:(Some)) [| ty_mem; mn |] in
              let h1 := pair_eq1 omem tyl sg sm traw tn1 hj in
              let h2 := pair_eq2 omem tyl sg sm traw tn1 hj in
              let h2 := match hz with
                | None => h2
                | Some (_, hz2) => mk_app (gref reference:(sf_trans)) [| tyl; traw; tn1; tnorm; h2; hz2 |]
                end in
              let projs := tup_proj tys (mk_rel 1) in
              let rh := List.fold_left2 (fun t p pr => tree_set p pr t) rnew dpaths projs in
              let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| rh; f; pcn; fc; rv; mn; ro |] |]) in
              (h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |])
          end in
        let accc := acc_cert a nb in
        let fpp := mk_app (gref reference:(eff_fp_store_intro)) [| accp; n; a; v; mk_app (gref reference:(EDone)) [| mk_app (gref reference:(Core)) [| r1; f1; pc1; fc1; rv1 |] |];
                     accc; gref reference:(I) |] in
        (mk_app (gref reference:(sf_install_store)) [| segs; ro; m; a; nb; bs; mn; kt; mk_app ok [| mr; ms1 |]; h1; ek |], ms1, fpp)
    | _ => sf_fail "raw shape"
    end in
    (if (x.(lit_delta)).(contents) then
       (if has_litself x ms1 then sf_fail "litself delta-instance in Q and a syntactic instance in the new state" else ())
     else ());
    stop 7;
    tm "install" (fun () =>
      let k := tm "k" (fun () => strip_cast open_constr:(_ : evtF $segs $rng $q $ms1)) in
      let term := mk_app (gref reference:(sf_evtF_step)) [| segs; rng; q; r; f; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |]; fc; rv; m; ro; w; i; sz; ms1; fwp; ecp; dcp; eqp; fpp; k |] in
      (if sf_check then
         match Constr.Unsafe.check term with
         | Val _ => ()
         | Err e => printf "STEPFAST-ILLTYPED %a" (fun () e => Message.of_exn e) e; sf_fail "ill-typed"
         end
       else ());
      match Constr.Unsafe.kind k with
      | Constr.Unsafe.Evar ev _ => tm "exact" (fun () => Std.exact_no_check term; Control.new_goal ev)
      | _ => sf_fail "install: continuation"
      end);
    stop 8;
    tm "clear" (fun () => Std.clear (clear_hyps.(contents)));
    stop 9;
    tm "post" (fun () => lazy_match! goal with
       | [ |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) ] => ltac1:(iv |- mem_after_store_opt; post_step iv) iv
       | [ |- _ ] => ()
       end);
    (if z then
       lazy_match! goal with
       | [ |- evtF ?segs' ?rng' ?q' (MS ?r' ?f' ?pc' ?fc' ?rv' ?m' ?ro') ] =>
           if Constr.is_var m' then () else
           let (h, mn) := small_goal (fun () => ltac1:(zsimp)) m' '(word -> option byte) in
           let k := strip_cast open_constr:(_ : evtF $segs' $rng' $q' (MS $r' $f' $pc' $fc' $rv' $mn $ro')) in
           let term := mk_app '@sf_evtF_mem [| segs'; rng'; q'; r'; f'; pc'; fc'; rv'; m'; mn; ro'; Control.hyp h; k |] in
           match Constr.Unsafe.kind k with
           | Constr.Unsafe.Evar ev _ => Std.exact_no_check term; Control.new_goal ev; Std.clear [h]
           | _ => sf_fail "install: continuation"
           end
       end
     else ())
  | [ |- _ ] => sf_fail "goal shape"
  end.

Ltac2 sfF_step (z : bool) : unit :=
  let ph := { contents := 0 } in
  if Bool.neg sf_debug then sfF_step_ ph z else
  Control.plus (fun () => sfF_step_ ph z)
    (fun e => (if sf_debug then
                 (lazy_match! goal with
                  | [ |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) ] => printf "STEPFASTF-PHASE %i at pc %t" (ph.(contents)) pc
                  | [ |- _ ] => printf "STEPFASTF-PHASE %i" (ph.(contents))
                  end) else ()); Control.zero e).

Ltac step_coreF_old segs RNG R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply (evtF_step_acc segs RNG);
        [ reflexivity
        | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | solve_accs
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.
Ltac sfF_old_step :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_coreF_old segs RNG R F pc fc rv m ro
  | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
Ltac sfF_old_zstep := sfF_old_step; zsimp.

Ltac2 sfF_old (z : bool) : unit := if z then ltac1:(sfF_old_zstep) else ltac1:(sfF_old_step).

Ltac2 sfF_dual (z : bool) : unit :=
  let g0 := Control.goal () in
  let res := Control.case (fun () =>
     sfF_step z;
     let g := Control.goal () in
     let hs := Control.hyps () in
     Control.zero (SF_Captured g hs)) in
  match res with
  | Val _ => sf_fail "impossible"
  | Err e =>
      match e with
      | SF_Captured gf hf =>
          sfF_old z;
          let go := Control.goal () in
          let ho := Control.hyps () in
          if Constr.equal gf go then
            (if hyps_equal hf ho then printf "STEPFASTF-OK" else printf "STEPFASTF-MISMATCH(hyps) at %t" g0)
          else
            let qev (g : constr) := match Constr.Unsafe.kind g with
              | Constr.Unsafe.App f args =>
                  if Int.equal (Array.length args) 4 then (if is_k (kof reference:(evtF)) f then Some (Array.get args 0, Array.get args 1, Array.get args 3) else None)
                  else None
              | _ => None end in
            match qev gf, qev go with
            | Some (s1, r1, ms1), Some (s2, r2, ms2) =>
                if Constr.equal s1 s2 then
                  (if Constr.equal r1 r2 then
                    (if Constr.equal ms1 ms2 then
                       (if hyps_equal hf ho then printf "STEPFASTF-OK(evarQ)" else printf "STEPFASTF-MISMATCH(hyps) at %t" g0)
                     else printf "STEPFASTF-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go)
                   else printf "STEPFASTF-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go)
                else printf "STEPFASTF-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go
            | _, _ => printf "STEPFASTF-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go
            end
      | _ =>
          printf "STEPFASTF-FALLBACK %a" (fun () e => Message.of_exn e) e;
          sfF_old z
      end
  end.

Ltac2 mutable sfF_mode : int := 1.

Ltac2 sfF_core1 (z : bool) : unit :=
  if Int.equal sfF_mode 0 then sfF_old z
  else if Int.equal sfF_mode 1 then
    Control.once (fun () =>
      Control.plus (fun () => sfF_step z)
        (fun e => (if sf_debug then printf "STEPFASTF-FALLBACK %a" (fun () e => Message.of_exn e) e else ()); sfF_old z))
  else sfF_dual z.

Ltac2 sfF_core (z : bool) : unit := Control.enter (fun () => sfF_core1 z).

Ltac sfF_step_dual := ltac2:(sfF_dual false).
Ltac sfF_zstep_dual := ltac2:(sfF_dual true).
Ltac sfF_step_fast := ltac2:(sfF_step false).
Ltac sfF_zstep_fast := ltac2:(sfF_step true).

Ltac step_core segs RNG R F pc fc rv m ro ::= ltac2:(sfF_core false).
Ltac zstep ::= ltac2:(sfF_core true).
