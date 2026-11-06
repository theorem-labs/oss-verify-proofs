(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac kx_rng :=
  lazymatch goal with
  | |- rng ?RNG ?A ?N =>
      match goal with
      | H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); kx_lia
      end
  end.
Ltac kx_zwin_pre := lazy beta iota zeta delta [zwin_prop zspan_ok]; kx_zoffs; lazy beta iota zeta delta [zden znth].
Ltac kx_zwins_solve :=
  repeat (apply Forall_cons; [kx_zwin_pre; try solve [split; [kx_lia | kx_rng]]|]); try apply Forall_nil.

Ltac kx_split_arest := repeat (apply Forall_cons; [|]); try apply Forall_nil.

Lemma kx_accP_rng : forall E RNG a (n : nat) A N, rng RNG A N -> (1 <= n)%nat ->
  A <= estart E a -> estart E a + Z.of_nat n <= A + N -> accP E RNG (a, n).
Proof.
  intros E RNG a n A N (H0 & H1 & H) Hn Ha Hb. unfold accP. cbn [fst snd]. rewrite adenot_estart, Z_to_bv_unsigned.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). apply H; lia.
Qed.

(* [comment removed for export] *)
Ltac kx_acc H :=
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- accP ?E ?RNG (?a, ?n) =>
      let nz := kx_len zs in
      lazymatch type of H with
      | rng RNG ?A0 ?N0 =>
          apply (kx_accP_rng E RNG a n A0 N0 H); [ vm_compute; lia | kx_estarts E zs nz KXA; kx_lia | kx_estarts E zs nz KXA; cbn [Z.of_nat]; kx_lia ]
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kx_runF_core STOPS FUEL DIRS KZS RRS WWS :=
  kx_mkR_fold;
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
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
      lazymatch r3 with (?l3, ?rs) =>
      let r4 := kx_rrs l3 WWS in
      lazymatch r4 with (?zs, ?ws) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let rk := eval vm_compute in (kx_run0 segs FUEL stops DIRS pcv rz zks nz) in
      let out := eval vm_compute in (kx_run1 segs FUEL stops DIRS pcv rz zks rk rs ws nz) in
      lazymatch out with
      | (?ss', ?scs, ?scr', ?accs, ?reads, ?rest, ?arest, ?es0) =>
          lazymatch ss' with
          | SSR ?pc' ?sr' ?log' ?kn' ?nx' _ =>
              change (evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
              refine (kx_go_evtF segs F fc RNG Q FUEL stops DIRS zs rz xs zks rk pcv m rom ss' scs scr' accs reads rs rest ws arest _ _ _ _ _ _ _ _ _ _);
              [ vm_cast_no_check (@eq_refl kxout (ss', scs, scr', accs))
              | kx_cert
              | kx_cert
              | kx_regs_eqs
              | kx_zks_solve
              | kx_zregs_solve
              | kx_zwins_solve
              | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
                let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
                intros E HE HK; destruct HE as [KXA KXRD]; clear HK; kx_split_rest
              | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
                let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
                intros E HE HK; destruct HE as [KXA KXRD]; clear HK; kx_split_arest
              | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in let HLF := fresh "KXLF" in
                let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in let HMI := fresh "KXMI" in
                intros E HE HK HLF HMI; destruct HE as [KXA KXRD];
                change (reads_ok segs m nz reads E) in KXRD;
                change (log_flat E log') in HLF;
                change (mem_inv segs m -> mem_inv segs (mem_denot E m log')) in HMI;
                first [ match goal with MI0 : mem_inv segs m |- _ => specialize (HMI MI0) end | clear HMI ];
                change (evtF segs RNG Q (MS (kx_regs E sr') F (Z_to_bv 64 pc') fc None (mem_denot E m log') rom));
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
                end
              ]
          end
      end end end end end end
  end.

Tactic Notation "kx_runF" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_runF_core stops (FUEL : nat) (@nil bool) kzs rrs wws.
Tactic Notation "kx_runFd" uconstr(STOPS) constr(FUEL) uconstr(DIRS) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let dirs := constr:(DIRS : list bool) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_runF_core stops (FUEL : nat) dirs kzs rrs wws.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kx_leaf_contF segs RNG Q F fc m rom E zs nz KXA rz es0 xs pc' sr' log' :=
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

Ltac kx_tree_splitF segs RNG Q F fc m rom E zs nz KXA rz es0 xs p :=
  lazymatch p with
  | VLeaf ?pc' ?sr' ?log' ?rest ?arest =>
      change ((Forall (sc_resid segs m E) rest /\ Forall (accP E RNG) arest) /\
              (log_flat E log' -> (mem_inv segs m -> mem_inv segs (mem_denot E m log')) ->
               evtF segs RNG Q (MS (kx_regs E sr') F (Z_to_bv 64 pc') fc None (mem_denot E m log') rom)));
      split; [ split; [ kx_split_rest | kx_split_arest ] | kx_leaf_contF segs RNG Q F fc m rom E zs nz KXA rz es0 xs pc' sr' log' ]
  | VFork ?c ?a ?b ?rest ?arest ?p1 ?p2 =>
      change ((Forall (sc_resid segs m E) rest /\ Forall (accP E RNG) arest) /\
              (branch_taken c (edenot E a) (edenot E b) = true -> kt_obl2 E (PO2 segs m RNG E) (PC2 segs F fc m rom RNG Q E) p1) /\
              (branch_taken c (edenot E a) (edenot E b) = false -> kt_obl2 E (PO2 segs m RNG E) (PC2 segs F fc m rom RNG Q E) p2));
      let BR := fresh "BR" in
      split; [ split; [ kx_split_rest | kx_split_arest ] | split; intro BR;
      [ kx_path_hyp E zs nz KXA BR; kx_tree_splitF segs RNG Q F fc m rom E zs nz KXA rz es0 xs p1
      | kx_path_hyp E zs nz KXA BR; kx_tree_splitF segs RNG Q F fc m rom E zs nz KXA rz es0 xs p2 ] ]
  end.

Ltac kx_autoF_core VMAX STOPS FUEL SCALLS KZS RRS WWS :=
  kx_mkR_fold;
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
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
      lazymatch r3 with (?l3, ?rs) =>
      let r4 := kx_rrs l3 WWS in
      lazymatch r4 with (?zs, ?ws) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let res := kx_trun_fix segs VMAX FUEL stops SCALLS pcv rz zks (@nil kentry) rs ws nz 4%nat in
      lazymatch res with
      | ((?t, ?r, ?reads, _, ?es0), ?rk) =>
          change (evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
          refine (kx_tree_evtF segs F fc RNG Q VMAX FUEL stops SCALLS zs rz xs zks rk pcv m rom t r reads rs ws _ _ _ _ _ _ _);
          [ vm_cast_no_check (@eq_refl ktree t)
          | kx_cert
          | kx_regs_eqs
          | kx_zks_solve
          | kx_zregs_solve
          | kx_zwins_solve
          | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
            let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
            intros E HE HK; destruct HE as [KXA KXRD];
            change (reads_ok segs m nz reads E) in KXRD;
            kx_tree_splitF segs RNG Q F fc m rom E zs nz KXA rz es0 xs r ]
      end end end end end end
  end.

Tactic Notation "kx_autoF" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoF_core 0 stops (FUEL : nat) true kzs rrs wws.
Tactic Notation "kx_autoF_nocall" uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoF_core 0 stops (FUEL : nat) false kzs rrs wws.
