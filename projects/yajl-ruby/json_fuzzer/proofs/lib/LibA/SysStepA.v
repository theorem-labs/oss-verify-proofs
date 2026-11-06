(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Export StepA ITreeA NodesA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac node_policy_solve :=
  cbn [node_policy node_ranges iov_ranges areg ms_regs ms_mem MSsvc MS map fst snd];
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let R' := eval hnf in R in
      change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end;
  zsimp;
  split; [ intros ?lo ?hi ?a ?k Hin; cbn [In] in Hin;
           repeat (destruct Hin as [Hin|Hin]; [injection Hin; clear Hin; intros; subst|]);
           try contradiction; intros;
           first [ policy1 | idtac ]
         | first [ exact I
                 | (* [comment removed for export] *)
                   intros ] ].

Ltac at_nodeA_solve :=
  lazymatch goal with
  | |- at_nodeA _ _ _ _ => split; [at_node_solve | node_policy_solve]
  | |- at_node _ _ _ => at_node_solve
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac sys_mem_write_gen segs R F pc fc rv m B bs ro :=
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
    end.

Ltac sys_mem_write ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) => sys_mem_write_gen segs R F pc fc rv m B bs ro
  | |- evtA ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) => sys_mem_write_gen segs R F pc fc rv m B bs ro
  end.

Ltac sys_mem_zeros_gen segs m A n :=
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
    clear Heqm Ha Hn Han; try clear m.

Ltac sys_mem_zeros ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) => sys_mem_zeros_gen segs m A n
  | |- evtA ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) => sys_mem_zeros_gen segs m A n
  end.

Ltac sys_mem_unmaps_gen segs m A n :=
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_unmaps segs m a n Ha Hn Han;
    let m' := fresh "m" in
    remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m.

Ltac sys_mem_unmaps ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) => sys_mem_unmaps_gen segs m A n
  | |- evtA ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) => sys_mem_unmaps_gen segs m A n
  end.

Ltac sys_nret ::=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | |- evtA _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Tactic Notation "call_spA" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtA _ _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; callA SPEC; unname_sp
  | |- evtA _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; callA SPEC; unname_sp
  | _ => callA SPEC
  end.

Ltac sys_finish ::=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | |- evtA _ _ _ _ => apply evtA_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma implA_from_evtA : forall {node : Type} segs (atn : (acc -> Prop) -> node -> machine_state -> Prop) P {R} (t : itree node R) Q ms,
  evtA segs P (fun ms' => implA segs atn P t Q ms') ms -> implA segs atn P t Q ms.
Proof. intros node segs atn P R t Q ms H. eapply implA_evtA; [exact H|]. intros ms' H'; exact H'. Qed.

(* [comment removed for export] *)
Lemma implA_extend : forall {node : Type} segs (atn : (acc -> Prop) -> node -> machine_state -> Prop) P {R}
    (t : itree node R) (Q1 Q : R -> machine_state -> Prop) ms,
  implA segs atn P t Q1 ms -> (forall r ms', Q1 r ms' -> evtA segs P (Q r) ms') -> implA segs atn P t Q ms.
Proof.
  intros node segs atn P R t; induction t as [r|n k IH]; intros Q1 Q ms H HQ; cbn in *.
  - eapply evtA_cut; [exact H|]. intros ms' H1. exact (HQ _ _ H1).
  - eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma implA_extend_epost : forall {node : Type} segs (atn : (acc -> Prop) -> node -> machine_state -> Prop) P {A}
    (t : itree node (exc A)) (Q1 Q : A -> machine_state -> Prop) ms,
  implA segs atn P t (epost Q1) ms -> (forall a ms', Q1 a ms' -> evtA segs P (Q a) ms') -> implA segs atn P t (epost Q) ms.
Proof.
  intros node segs atn P A t Q1 Q ms H HQ. eapply implA_extend; [exact H|].
  intros [|a] ms' H1; cbn in *; [apply evtA_done; exact I| exact (HQ _ _ H1)].
Qed.

(* [comment removed for export] *)
End RC__1.
Tactic Notation "icallxA" uconstr(SPEC) :=
  (lazymatch goal with |- evtA _ _ _ _ => apply evtA_done | _ => idtac end);
  eapply implA_extend_epost; [ eapply SPEC | ].

Ltac iprefixA := apply implA_from_evtA.
Ltac ihereA := apply evtA_done.

Tactic Notation "icallA" uconstr(SPEC) :=
  (lazymatch goal with |- evtA _ _ _ _ => apply evtA_done | _ => idtac end);
  first [ eapply SPEC
        | eapply implA_epost_mono; [ eapply SPEC | ] ].
