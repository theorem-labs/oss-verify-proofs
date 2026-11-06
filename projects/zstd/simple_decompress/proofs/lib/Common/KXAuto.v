(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo KXTree.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TRun.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition kx_trun (vmax : Z) (fuel : nat) (stops : list Z) (scalls : bool) (pc : Z) (rz : list zexp) (zks : list zk) (rk : list kentry)
                   (rs ws : list zreg) (nz : nat)
  : ktree * vtree * list rdspec * list kentry * list expr :=
  let kn := map zk_kentry zks ++ rk in
  let t := kx_tree segs vmax fuel true stops scalls (kt_init pc rz kn nz) [] [] in
  let reads := kx_reads_of nz (kt_next t) (kt_scs t) in
  (t, kt_resid kn rs ws t, reads, kx_rk (map zk_kentry zks) (zk_tfs zks) nz reads, map zx rz).

End TRun.

Fixpoint kt_leaves (t : ktree) : nat :=
  match t with KLeaf _ _ _ => 1%nat | KFork _ _ _ _ _ t1 t2 => (kt_leaves t1 + kt_leaves t2)%nat | KSplit _ _ _ _ t1 t2 => (kt_leaves t1 + kt_leaves t2)%nat end.

Fixpoint kentry_list_eqb (x y : list kentry) : bool :=
  match x, y with
  | [], [] => true
  | KRange (EVar i) lo hi :: x', KRange (EVar j) lo' hi' :: y' => Nat.eqb i j && Z.eqb lo lo' && Z.eqb hi hi' && kentry_list_eqb x' y'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition br_propu (c : branch_cond) (t : bool) (u v : Z) : Prop :=
  match c, t with
  | BC_EQ, true | BC_NE, false => u = v
  | BC_EQ, false | BC_NE, true => u <> v
  | BC_LTU, true | BC_GEU, false => u < v
  | BC_LTU, false | BC_GEU, true => v <= u
  | _, _ => True
  end.

Lemma br_propu_ok : forall c t (x y : word), branch_taken c x y = t -> br_propu c t (bv_unsigned x) (bv_unsigned y).
Proof.
  intros c t x y H. destruct c; cbn [branch_taken] in H; unfold bv_eqb, bv_ltu in H; subst t; cbn [br_propu]; try exact I.
  - destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)); assumption.
  - destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)); cbn [negb]; assumption.
  - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); assumption.
  - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); cbn [negb]; assumption.
Qed.

Lemma kx_umod : forall w : word, bv_unsigned w mod 2^64 = bv_unsigned w.
Proof. intro w. apply Z.mod_small. exact (kx_u64_range w). Qed.

Lemma kx_signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. rewrite (zb_signed (Z_to_bv 64 z)), Z_to_bv_unsigned.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  destruct (Z.ltb_spec z (2^63)); [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Ltac kx_path_hyp E zs nz KXA BR :=
  lazymatch type of BR with
  | branch_taken ?c (edenot E ?a) (edenot E ?b) = ?t =>
      lazymatch c with
      | BC_LT => idtac | BC_GE => idtac
      | _ =>
          let ua := kx_uz E zs nz a in
          let ub := kx_uz E zs nz b in
          let BR' := fresh "KXBR" in
          pose proof (br_propu_ok c t _ _ BR) as BR';
          rewrite (uz_sound zs E a KXA), (uz_sound zs E b KXA) in BR';
          change (br_propu c t ua ub) in BR';
          cbv beta iota delta [br_propu] in BR';
          rewrite ?kx_umod in BR';
          (* [comment removed for export] *)
          repeat match type of BR' with
                 | context [?z mod 2^64] =>
                     let HR := fresh "KXBRr" in
                     first [ (* [comment removed for export] *)
                             assert (HR : 0 <= z < 2^64) by (clear BR'; kx_lia);
                             rewrite (Z.mod_small z (2^64) HR) in BR'; clear HR
                           | (* [comment removed for export] *)
                             assert (HR : 0 <= z < 2^64) by kx_lia;
                             rewrite (Z.mod_small z (2^64) HR) in BR' ]
                 end;
          clear BR
      end
  end;
  (* [comment removed for export] *)
  lazymatch goal with
  | BR0 : branch_taken ?c (edenot E ?a) (edenot E ?b) = ?t |- _ =>
      let za := kx_ez E zs nz a in
      let zb := kx_ez E zs nz b in
      let BR' := fresh "KXBR" in
      assert (BR' : branch_taken c (Z_to_bv 64 za) (Z_to_bv 64 zb) = t)
        by (change (branch_taken c (Z_to_bv 64 (ez E zs a)) (Z_to_bv 64 (ez E zs b)) = t);
            rewrite <- (ez_sound zs E a KXA), <- (ez_sound zs E b KXA); exact BR0);
      clear BR0;
      cbn [branch_taken] in BR';
      try zify_cond BR';
      (* [comment removed for export] *)
      repeat match type of BR' with
             | context [bv_signed (Z_to_bv 64 ?z)] =>
                 let HS := fresh "KXBRs" in
                 assert (HS : 0 <= z < 2^63) by (clear BR'; kx_lia);
                 rewrite (kx_signed_small z HS) in BR'; clear HS
             end
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac kx_leaf_cont segs Q F fc m rom E zs nz KXA rz es0 xs pc' sr' log' :=
  let HLF := fresh "KXLF" in let HMI := fresh "KXMI" in
  intros HLF HMI;
  change (log_flat E log') in HLF;
  change (mem_inv segs m -> mem_inv segs (mem_denot E m log')) in HMI;
  first [ match goal with MI0 : mem_inv segs m |- _ => specialize (HMI MI0) end | clear HMI ];
  lazymatch sr' with
  | @cons _ _ ?es =>
      let xs' := kx_exit_xs E zs nz es es0 xs in
      let HR := fresh "KXHR" in
      assert (HR : kx_regs E sr' = mkRl xs') by (apply kx_regs_mkRl; [change (Forall2 (fun e x => edenot E e = x) es xs'); kx_exit_prf E zs KXA rz | reflexivity]);
      rewrite HR; clear HR;
      rewrite <- mkRl_mkR
  end;
  lazymatch log' with
  | @nil _ => change (mem_denot E m (@nil sentry)) with m in *; clear HLF
  | _ => idtac
  end.

Ltac kx_tree_split segs Q F fc m rom E zs nz KXA rz es0 xs p :=
  lazymatch p with
  | VLeaf ?pc' ?sr' ?log' ?rest ?arest =>
      change (Forall (sc_resid segs m E) rest /\
              (log_flat E log' -> (mem_inv segs m -> mem_inv segs (mem_denot E m log')) ->
               evt segs Q (MS (kx_regs E sr') F (Z_to_bv 64 pc') fc None (mem_denot E m log') rom)));
      split; [ kx_split_rest | kx_leaf_cont segs Q F fc m rom E zs nz KXA rz es0 xs pc' sr' log' ]
  | VFork ?c ?a ?b ?rest ?arest ?p1 ?p2 =>
      change (Forall (sc_resid segs m E) rest /\
              (branch_taken c (edenot E a) (edenot E b) = true -> kt_obl2 E (PO1 segs m E) (PC1 segs F fc m rom Q E) p1) /\
              (branch_taken c (edenot E a) (edenot E b) = false -> kt_obl2 E (PO1 segs m E) (PC1 segs F fc m rom Q E) p2));
      let BR := fresh "BR" in
      split; [ kx_split_rest | split; intro BR;
      [ kx_path_hyp E zs nz KXA BR; kx_tree_split segs Q F fc m rom E zs nz KXA rz es0 xs p1
      | kx_path_hyp E zs nz KXA BR; kx_tree_split segs Q F fc m rom E zs nz KXA rz es0 xs p2 ] ]
  end.

(* [comment removed for export] *)
Ltac kx_trun_fix segs VMAX FUEL stops scalls pcv rz zks rk rs ws nz n :=
  let out := eval vm_compute in (kx_trun segs VMAX FUEL stops scalls pcv rz zks rk rs ws nz) in
  lazymatch out with
  | (?t, ?r, ?reads, ?rk', ?es0) =>
      let same := eval vm_compute in (kentry_list_eqb rk rk') in
      lazymatch same with
      | true => constr:((out, rk))
      | false =>
          lazymatch n with
          | O => fail 100 "kx_auto: the fresh-read range facts do not stabilise"
          | S ?n' => kx_trun_fix segs VMAX FUEL stops scalls pcv rz zks rk' rs ws nz n'
          end
      end
  end.

Ltac kx_auto_core VMAX STOPS FUEL SCALLS KZS RRS :=
  kx_mkR_fold;
  lazymatch goal with
  | |- evt ?segs ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let pcv := eval vm_compute in pc in
      let r1 := kx_rws (@nil Z) xs in
      lazymatch r1 with (?l1, ?rz) =>
      let r2 := kx_rks l1 KZS in
      lazymatch r2 with (?l2a, ?zks0) =>
      let r2b := kx_add_cells segs m l2a zks0 in
      lazymatch r2b with (?l2, ?zks1) =>
      let zks := kx_add_wrimgs segs m l2 KZS zks1 in
      let r3 := kx_rrs l2 RRS in
      lazymatch r3 with (?zs, ?rs) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let res := kx_trun_fix segs VMAX FUEL stops SCALLS pcv rz zks (@nil kentry) rs (@nil zreg) nz 4%nat in
      lazymatch res with
      | ((?t, ?r, ?reads, _, ?es0), ?rk) =>
          change (evt segs Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
          refine (kx_tree_evt segs F fc Q VMAX FUEL stops SCALLS zs rz xs zks rk pcv m rom t r reads rs _ _ _ _ _ _);
          [ vm_cast_no_check (@eq_refl ktree t)
          | kx_cert
          | kx_regs_eqs
          | kx_zks_solve
          | kx_zregs_solve
          | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
            let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
            intros E HE HK; destruct HE as [KXA KXRD];
            change (reads_ok segs m nz reads E) in KXRD;
            kx_tree_split segs Q F fc m rom E zs nz KXA rz es0 xs r ]
      end end end end end
  end.

(* [comment removed for export] *)
Tactic Notation "kx_auto" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  kx_auto_core 0 stops (FUEL : nat) true kzs rrs.
Tactic Notation "kx_auto_nocall" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  kx_auto_core 0 stops (FUEL : nat) false kzs rrs.
Tactic Notation "kx_auto_v" constr(VMAX) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in let rrs := constr:(RRS : list (Z * Z)) in
  kx_auto_core (VMAX : Z) stops (FUEL : nat) true kzs rrs.
