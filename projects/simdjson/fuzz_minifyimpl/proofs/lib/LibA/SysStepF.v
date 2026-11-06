(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Export ExecF ITreeA NodesA StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation implA segs RNG t Q ms := (@implF node segs (at_nodeA segs) fstepA _ RNG t Q ms).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma implF_from_evtF : forall {node : Type} segs (atn : node -> footprint -> machine_state -> Prop)
    (fst : node -> resp -> footprint -> footprint -> Prop) {R} RNG (t : itree node R) Q ms,
  evtF segs RNG (fun ms' => implF segs atn fst RNG t Q ms') ms -> implF segs atn fst RNG t Q ms.
Proof. intros node segs atn fst R RNG t Q ms H. eapply implF_evtF; [exact H|]. intros ms' H'; exact H'. Qed.

Ltac iprefix := apply implF_from_evtF.
Ltac ihere := apply evtF_done.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac at_nodeA_red :=
  cbn [at_nodeA ncov at_node]; unfold areg, max_write, max_read, TASK_SIZE, cstr_len, path_max;
  cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let R' := eval hnf in R in
      change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end.

Ltac at_nodeA_solve :=
  at_nodeA_red; split_spine;
  first [ reflexivity | lia | assumption | exact I
        | solve_rng
        | lazymatch goal with |- _ = _ \/ _ = _ => first [left; reflexivity | right; reflexivity] end
        | symmetry; apply Z_to_bv_bv_unsigned
        | lazymatch goal with
          | |- wr_at ?segs ?m ?A ?n =>
              match goal with H : rw_cells segs m A ?cs |- _ =>
                apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
          | |- bytes_at ?segs ?m ?A ?bs =>
              match goal with
              | H : rw_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              | H : ro_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              end
          | |- _ /\ _ => split; at_nodeA_solve
          end
        | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fstep_transport HF :=
  lazymatch type of HF with
  | fstepA ?n ?rsp ?RNG ?RNG' =>
      first
        [ (* [comment removed for export] *)
          lazymatch eval hnf in (fstepA n rsp RNG RNG') with
          | RNG' = RNG => idtac
          end;
          let E := fresh in assert (E : RNG' = RNG) by exact HF; subst RNG'; clear HF
        | lazymatch n with
          | NMunmap ?a ?l =>
              repeat match goal with
              | H : rng RNG ?lo ?len |- _ =>
                  first [ apply (fstepA_munmap_rng a l rsp RNG RNG' lo len HF) in H; [| reglia]
                        | idtac "note: dropping footprint hypothesis (overlaps the unmapped range):" H; clear H ]
              end
          | _ =>
              repeat match goal with
              | H : rng RNG ?lo ?len |- _ =>
                  apply (fstepA_rng n rsp RNG RNG' lo len I HF) in H
              end
          end ]
  end.

(* [comment removed for export] *)
Tactic Notation "fstep_intro" ident(rsp) ident(RNG') ident(a) ident(HF) ident(Hdec) :=
  intros rsp RNG' a HF Hdec; fstep_transport HF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac sys_mem_write :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
        clear Heqm; clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

Ltac sys_mem_zeros :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_zeros segs m a n Ha Hn Han;
    let Z' := fresh "ZNEW" in
    pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
    let m' := fresh "m" in
    remember (apply_zeros m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m
  end.

Ltac sys_mem_unmaps :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_unmaps segs m a n Ha Hn Han;
    let m' := fresh "m" in
    remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m
  end.

Ltac sys_nret :=
  cbv beta delta [efferr_ci eff0_ci efferr eff0];
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_none
        | rewrite apply_mem_delivered; sys_mem_write
        | rewrite apply_mem_write; sys_mem_write
        | rewrite apply_mem_zeros; sys_mem_zeros
        | rewrite apply_mem_unmaps; sys_mem_unmaps
        | idtac ].

Ltac sys_nret_raw :=
  cbv beta delta [efferr_ci eff0_ci efferr eff0];
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps | rewrite apply_mem_none | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fp_use FP :=
  lazymatch type of FP with
  | ?A /\ ?B =>
      let F1 := fresh "FP" in let F2 := fresh "FP" in
      destruct FP as [F1 F2]; fp_use F1; fp_use F2
  | ?R' = ?R => first [ subst R' | subst R | idtac ]
  | fp_le ?R ?R' =>
      repeat match goal with
      | H : rng R ?lo ?len |- _ => apply (rng_fp_le R R' lo len FP) in H
      end
  | fstepA _ _ _ _ => fstep_transport FP
  | rng _ _ _ => idtac
  | _ => idtac
  end.

(* [comment removed for export] *)
Lemma implF_post_evtF : forall {node : Type} segs (atn : node -> footprint -> machine_state -> Prop)
    (fst : node -> resp -> footprint -> footprint -> Prop) {R} (t : itree node R) RNG Q Q' ms,
  implF segs atn fst RNG t Q' ms ->
  (forall r RNG' ms', Q' r RNG' ms' -> evtF segs RNG' (Q r RNG') ms') ->
  implF segs atn fst RNG t Q ms.
Proof.
  intros node segs atn fst R t; induction t as [r|n k IH]; intros RNG Q Q' ms H HQ; cbn in *.
  - eapply evtF_cut; eauto.
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' HF. eapply IH; eauto.
Qed.

Lemma implF_epost_evtF : forall {node : Type} segs (atn : node -> footprint -> machine_state -> Prop)
    (fst : node -> resp -> footprint -> footprint -> Prop) {A} (t : itree node (exc A)) RNG Q Q' ms,
  implF segs atn fst RNG t (epostF Q') ms ->
  (forall a RNG' ms', Q' a RNG' ms' -> evtF segs RNG' (Q a RNG') ms') ->
  implF segs atn fst RNG t (epostF Q) ms.
Proof.
  intros node segs atn fst A t RNG Q Q' ms H HQ. eapply implF_post_evtF; [exact H|].
  intros [|a] RNG' ms' Hp; cbn in *; [apply evtF_done; exact I | apply HQ; exact Hp].
Qed.

(* [comment removed for export] *)
Tactic Notation "icall" uconstr(SPEC) :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  first [ eapply SPEC
        | eapply implF_epost_mono; [ eapply SPEC | ] ];
  try (lazymatch goal with |- rng _ _ _ => solve_rng end).

(* [comment removed for export] *)
Tactic Notation "icallk" uconstr(SPEC) :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  eapply implF_epost_evtF; [ eapply SPEC | ];
  try (lazymatch goal with |- rng _ _ _ => solve_rng end).

(* [comment removed for export] *)
Ltac ipost segs :=
  let a := fresh "ans" in let RNG' := fresh "RNG" in let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros a RNG' ms' PO;
  (let T := type of PO in let T := eval hnf in T in
   lazymatch T with
   | ?A /\ _ => tryif is_fp_clause A then (let FP := fresh "FP" in destruct PO as [FP PO]; fp_use FP) else idtac
   | _ => idtac
   end);
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ ?m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (let MIname := fresh "MI" in
       lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
