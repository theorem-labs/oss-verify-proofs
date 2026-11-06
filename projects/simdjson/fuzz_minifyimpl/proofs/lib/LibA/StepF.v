(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image Tac Bytes.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Export StoreFast Walk.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Export ExecF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rng_acc_litZ' : forall RNG lo len E (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> (1 <=? nz)%Z = true -> (lo <= E /\ E + nz <= lo + len)%Z ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof. intros RNG lo len E n nz H Hn Hz HE. eapply rng_acc_litZ; eauto. apply Z.leb_le. exact Hz. Qed.

(* [comment removed for export] *)
Ltac acc_hint := fail.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac leftmost E := lazymatch E with Z.add ?X _ => leftmost X | Z.sub ?X _ => leftmost X | _ => E end.

(* [comment removed for export] *)
Ltac is_closed_lits E :=      (* [comment removed for export] *)
  lazymatch E with
  | Z.add ?a ?b => is_closed_lits a; is_closed_lits b
  | Z.sub ?a ?b => is_closed_lits a; is_closed_lits b
  | _ => is_Zlit E
  end.
Ltac decide_lit_bounds :=      (* [comment removed for export] *)
  lazymatch goal with
  | |- (?a <= ?b /\ ?c <= ?d)%Z => split; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity
  end.
(* [comment removed for export] *)
Ltac solve_acc_lit H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); decide_lit_bounds
      end
  end.
(* [comment removed for export] *)
Ltac mentions T X := lazymatch T with context [X] => idtac end.

Ltac solve_acc1 :=
  first [ acc_hint
        | assumption
        | (* [comment removed for export] *)
          lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
              is_closed_lits E;
              match goal with
              | H : rng RNG ?lo ?len |- _ => is_closed_lits lo; is_closed_lits len; solve_acc_lit H
              end
          end
        | (* [comment removed for export] *)
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
        | (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
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
              else first [ (* [comment removed for export] *)
                           is_closed_lits lo'; is_closed_lits len';
                           match goal with
                           | H : rng RNG ?lo ?len |- _ =>
                               is_closed_lits lo; is_closed_lits len; apply (rng_sub' RNG lo len lo' len' H); decide_lit_bounds
                           end
                         | (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac exec_cbv :=
  lazymatch goal with |- ?G =>
    let G' := eval cbv beta iota zeta delta [lift_resultF lift_result interp_eff interp_eff_accesses drop_access_report access_value accessed_ranges
     exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s] in G in
    change_no_check G' end.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
          change (write_to_mem m (wa (A + Z.of_nat kn)) bs) with (write_to_mem m (wa (A + kz)) bs);   (* [comment removed for export] *)
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

(* [comment removed for export] *)
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
          change (write_to_mem m (wa (A + Z.of_nat kn)) bs) with (write_to_mem m (wa (A + kz)) bs);   (* [comment removed for export] *)
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

(* [comment removed for export] *)
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
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac stepF_body w i sz k :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
        eapply (evtF_step_acc segs RNG);
        [ reflexivity
        | diet_rhs_open;     (* [comment removed for export] *)
          rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          diet_rhs_close;
          reflexivity
        | solve_accs
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i; k ]
  end.

Ltac stepF_core_k segs pc k :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) => diet_run ltac:(idtac; stepF_body w i sz k) ltac:(idtac; diet_open i; stepF_body w i sz k; diet_close)
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac stepF_k k :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => stepF_core_k segs pc k
  | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Ltac step := stepF_k ltac:(idtac).
Ltac step_core segs RNG R F pc fc rv m ro := stepF_core_k segs pc ltac:(idtac).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac if_true :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      diet_run ltac:(idtac; replace c with true; [nc_iota| symmetry; solve_cond])
               ltac:(idtac; diet_open_cond c; replace c with true; [nc_iota; diet_close | diet_close; symmetry; solve_cond])
  end.
Ltac if_false :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      diet_run ltac:(idtac; replace c with false; [nc_iota| symmetry; solve_cond])
               ltac:(idtac; diet_open_cond c; replace c with false; [nc_iota; diet_close | diet_close; symmetry; solve_cond])
  end.
Ltac if_true_by H :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      diet_run ltac:(idtac; replace c with true; [nc_iota| symmetry; exact H])
               ltac:(idtac; diet_open_cond c; replace c with true; [nc_iota; diet_close | diet_close; symmetry; exact H])
  end.
Ltac if_false_by H :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      diet_run ltac:(idtac; replace c with false; [nc_iota| symmetry; exact H])
               ltac:(idtac; diet_open_cond c; replace c with false; [nc_iota; diet_close | diet_close; symmetry; exact H])
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

Ltac zstep := stepF_k ltac:(zsimp).      (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* [comment removed for export] *)
Tactic Notation "call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      eapply evtF_cut; [ eapply SPEC | post_call segs m ];
      try (lazymatch goal with |- rng _ _ _ => solve_rng end)
  end.

(* [comment removed for export] *)
Ltac is_fp_clause A :=
  lazymatch A with
  | ?A1 /\ _ => is_fp_clause A1
  | @eq ?T _ _ => lazymatch eval hnf in T with machine_state => fail | _ => idtac end
  | rng _ _ _ => idtac
  | _ => let A' := eval hnf in A in      (* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac store_done :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma evtF_ecall : forall segs RNG (Q : machine_state -> Prop) R F pc fc rv m ro w,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
  Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
  evtF segs RNG Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros segs RNG Q R F pc fc rv m ro w Hf He HQ.
  eapply evtF_step_acc; [reflexivity| | apply Forall_nil | apply evtF_done; exact HQ].
  rewrite (stepF_ecall_gen segs R F (Z_to_bv 64 pc) fc rv m ro w Hf He). reflexivity.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
      (* [comment removed for export] *)
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
