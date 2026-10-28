(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit AW_Leaves AsDepotInv AW_FreeLeaves.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac blist_eq := repeat (first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]).
(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma rw_cells_reshape : forall m A cs1 cs2,
  cells_bytes cs1 = cells_bytes cs2 -> cells_size cs1 = cells_size cs2 -> cells_wf cs2 -> rw_cells asegs m A cs1 -> rw_cells asegs m A cs2.
Proof. intros m A cs1 cs2 EB ES WF [[W1 B1] WR]. split; [split; [exact WF| rewrite <- EB; exact B1]| rewrite <- ES; exact WR]. Qed.

(* [comment removed for export] *)
Definition ia_after (m : mem) : Prop :=
     u8arr asegs m AIAINST (repeat (b8 0) (Z.to_nat 0x40dc0))
  /\ rw_cells asegs m (AIAINST + 0x40dc0) [C8 (wz 4096); C8 (wz (AIAINST + 0x40dd0))]
  /\ u8arr asegs m (AIAINST + 0x40dd0) (repeat (b8 0) (Z.to_nat (0x81030 - 0x40dd0))).
Definition ia_pristine (m : mem) : Prop := u8arr asegs m AIAINST (repeat (b8 0) (Z.to_nat 0x81030)).

Definition ia_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 a6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz AIAINST) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)]
    /\ ia_after m'.
End HCW2.

Section IAInit.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (inited : bool).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 48 <= bv_unsigned sp.
  Hypothesis FLG : rw_cells asegs m AIAINIT [C1 (b8 (if inited then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Hypothesis IA : if inited then ia_after m else ia_pristine m.
  Hypothesis GOTP : rw_cells asegs m AGOT_LO [C8 (wz APAGESZ)].
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].

  Theorem internal_allocator_spec :
    evt asegs (ia_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1cb408) fc None m (seg_rom asegs)).
  Proof.
    destruct inited;
      [ change (ia_after m) in IA; unfold ia_after in IA; destruct IA as (IA1 & IA2 & IA3)
      | change (ia_pristine m) in IA; unfold ia_pristine in IA ].
    all: unfold AIAINIT, AIAINST, AGOT_LO, APAGESZ in *.
    all: pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR; acb.
    all: pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (7578504, 7578504 + 4); (6994688, 6994688 + 0x81030)]%Z m) as MU.
    all: pose proof (wmono_refl asegs m) as WM.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      remember (Z.to_nat 265664) as K1 eqn:HK1 in IA1. remember (Z.to_nat (528432 - 265680)) as K3 eqn:HK3 in IA3.
      assert (L1 : Z.of_nat (length (repeat (b8 0) K1)) = 265664) by (rewrite repeat_length; subst K1; rewrite Z2Nat.id; lia).
      assert (L3 : Z.of_nat (length (repeat (b8 0) K3)) = 528432 - 265680) by (rewrite repeat_length; subst K3; rewrite Z2Nat.id; lia).
      clear HK1 HK3.
      replace (6994688 + 265664) with 7260352 in IA2 by reflexivity. replace (6994688 + 265680) with 7260368 in IA2, IA3 by reflexivity.
      step. carve_frame 48%nat ST. step. step. step. step. step. step. step. step. step.
      step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
      step. step. step. step. step. step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold ia_post, ia_after, AIAINST. do 7 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FLG|].
      rewrite repeat_length in L1, L3.
      split; [rewrite <- L1, Nat2Z.id; exact IA1|]. split; [exact IA2| rewrite <- L3, Nat2Z.id; exact IA3].
    - (* [comment removed for export] *)
      remember (Z.to_nat 528432) as K0 eqn:HK0 in IA.
      assert (L0 : Z.of_nat (length (repeat (b8 0) K0)) = 528432) by (rewrite repeat_length; subst K0; rewrite Z2Nat.id; lia). clear HK0.
      (* [comment removed for export] *)
      assert (GOTPm : True -> rw_cells asegs m 6191096 [C8 (wz 7578528)]) by (intros _; exact GOTP).
      assert (PSCm : True -> rw_cells asegs m 7578528 [C8 (wz 4096)]) by (intros _; exact PSC). clear GOTP PSC.
      step. carve_frame 48%nat ST. step. step. step. step. step. step. step. step. step.
      step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
      (* [comment removed for export] *)
      apply (rw_cells_reshape _ _ _ [C4 (wz 0)]) in FLG; [| reflexivity| reflexivity| cbn; exact (conj I I)].
      step. step. step. step. step. step. step. step.
      Ltac litx := repeat match goal with
        | |- context [Z_to_bv 64 (bv_swrap ?n ?x)] => let v := eval vm_compute in (bv_swrap n x) in change (bv_swrap n x) with v
        | |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v
        | |- context [Z_to_bv 64 (Z.lxor ?x ?y)] => let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
        | |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v
        | |- context [Z_to_bv 64 (Z.shiftr ?x ?y)] => let v := eval vm_compute in (Z.shiftr x y) in change (Z.shiftr x y) with v
        end.
      litx.
      (* [comment removed for export] *)
      assert (MA : 7578504 mod 4 = 0) by reflexivity. assert (MR : 0 <= 7578504 < 2^64) by (clear; lia).
      astep.
      (* [comment removed for export] *)
      step. step. step. step. litx.
      astep.
      (* [comment removed for export] *)
      step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
      step. step. litx.
      step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
      (* [comment removed for export] *)
      apply (rw_cells_reshape _ _ _ [C1 (b8 0); C1 (b8 1); C2 (wz 0)]) in FLG; [| cbn [cells_bytes cbytes app]; unfold le4, le2; blist_eq| reflexivity| cbn; repeat split; exact I].
      step. step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
      (* [comment removed for export] *)
      assert (SPLIT : forall mm A k1 k2, u8arr asegs mm A (repeat (b8 0) (k1 + k2)) -> u8arr asegs mm A (repeat (b8 0) k1) /\ u8arr asegs mm (A + Z.of_nat k1) (repeat (b8 0) k2)).
      { intros mm A k1 k2 U. rewrite repeat_app in U. apply u8arr_app in U. rewrite repeat_length in U. exact U. }
      replace K0 with (Z.to_nat 8 + (Z.to_nat 262144 + (Z.to_nat 56 + (Z.to_nat 3456 + (Z.to_nat 262728 + Z.to_nat 40)))))%nat in IA by (clear - L0; try acb; rewrite repeat_length in L0; lia).
      apply SPLIT in IA. destruct IA as [P0 R1]. apply SPLIT in R1. destruct R1 as [P1 R2]. apply SPLIT in R2. destruct R2 as [P2 R3].
      apply SPLIT in R3. destruct R3 as [P3 R4]. apply SPLIT in R4. destruct R4 as [P4 P5].
      rewrite (Z2Nat.id 8) in P1, P2, P3, P4, P5 by (clear; lia). rewrite (Z2Nat.id 262144) in P2, P3, P4, P5 by (clear; lia).
      rewrite (Z2Nat.id 56) in P3, P4, P5 by (clear; lia). rewrite (Z2Nat.id 3456) in P4, P5 by (clear; lia). rewrite (Z2Nat.id 262728) in P5 by (clear; lia).
      replace (6994688 + 8) with 6994696 in P1 by reflexivity. replace (6994688 + 8 + 262144) with 7256840 in P2 by reflexivity.
      replace (6994688 + 8 + 262144 + 56) with 7256896 in P3 by reflexivity. replace (6994688 + 8 + 262144 + 56 + 3456) with 7260352 in P4 by reflexivity.
      replace (6994688 + 8 + 262144 + 56 + 3456 + 262728) with 7523080 in P5 by reflexivity.
      assert (LP0 : Z.of_nat (length (repeat (b8 0) (Z.to_nat 8))) = 8) by (rewrite repeat_length; clear; lia).
      assert (LP1 : Z.of_nat (length (repeat (b8 0) (Z.to_nat 262144))) = 262144) by (rewrite repeat_length; clear; lia).
      assert (LP2 : Z.of_nat (length (repeat (b8 0) (Z.to_nat 56))) = 56) by (rewrite repeat_length; clear; lia).
      assert (LP3 : Z.of_nat (length (repeat (b8 0) (Z.to_nat 3456))) = 3456) by (rewrite repeat_length; clear; lia).
      assert (LP4 : Z.of_nat (length (repeat (b8 0) (Z.to_nat 262728))) = 262728) by (rewrite repeat_length; clear; lia).
      assert (LP5 : Z.of_nat (length (repeat (b8 0) (Z.to_nat 40))) = 40) by (rewrite repeat_length; clear; lia).
      clear L0 SPLIT.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step. litx.
      step. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [eapply internal_memset0_bytes_spec; [eassumption| clear; lia| exact P5| vm_compute; discriminate] | post_call asegs mc] end.
      rename POST into P5.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (u8arr_store_ok asegs mc 6994688 _ 0 (wa (6994688 + 0)) P0 ltac:(hci; rewrite repeat_length; clear; lia) eq_refl) as HS end.
      step. match goal with |- context [write_to_mem _ _ ?bs] => change bs with [b8 0] end.
      lazymatch goal with |- context [write_to_mem ?mc _ _] =>
        pose proof (u8arr_write asegs mc 6994688 _ 0 (b8 0) P0 ltac:(hci; rewrite repeat_length; clear; lia)) as P0' end.
      rewrite upd_repeat_same in P0'. replace (6994688 + 0) with 6994688 in P0' by (clear; lia). clear P0. store_done. rename P0' into P0.
      (* [comment removed for export] *)
      step. step. step. step. litx.
      step. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [eapply internal_memset0_bytes_spec; [eassumption| clear; lia| exact P1| vm_compute; discriminate] | post_call asegs mc] end.
      rename POST into P1.
      (* [comment removed for export] *)
      step. step. step. step. step. litx.
      step. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [eapply internal_memset0_16_spec; [eassumption| clear; lia| exact P3| reflexivity| reflexivity] | post_call asegs mc] end.
      rename POST into P3.
      (* [comment removed for export] *)
      step. step. step. step. step. litx.
      step. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [eapply internal_memset0_bytes_spec; [eassumption| clear; lia| exact P4| vm_compute; discriminate] | post_call asegs mc] end.
      rename POST into P4.
      (* [comment removed for export] *)
      lazymatch goal with H : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (GOTPm I) as GOTP; eapply (rw_cells_transport asegs _ m mc) in GOTP; [| exact H| eassumption| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; clear - SPR HI LO; try acb; lia];
        pose proof (PSCm I) as PSC; eapply (rw_cells_transport asegs _ m mc) in PSC; [| exact H| eassumption| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; clear - SPR HI LO; try acb; lia] end.
      unfold wz in GOTP, PSC.
      step. step. step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K GOTP PSC.
      (* [comment removed for export] *)
      step. step. step. step. litx.
      (* [comment removed for export] *)
      replace (Z.to_nat 262728) with (8 + (8 + Z.to_nat (262728 - 16)))%nat in P4 by (clear; lia).
      rewrite !repeat_app in P4. apply u8arr_app in P4. destruct P4 as [C0 P4]. apply u8arr_app in P4. destruct P4 as [C1c P4].
      rewrite !repeat_length in C1c, P4. replace (7260352 + Z.of_nat 8) with 7260360 in C1c by reflexivity.
      replace (7260352 + Z.of_nat 8 + Z.of_nat 8) with 7260368 in P4 by reflexivity.
      apply (rw_cells_of_u8arr asegs) in C0. apply (rw_cells_of_u8arr asegs) in C1c. rewrite repeat_length in C0, C1c.
      assert (LP4' : Z.of_nat (length (repeat (b8 0) (Z.to_nat (262728 - 16)))) = 262728 - 16) by (rewrite repeat_length; clear; lia).
      st1. st1.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (CC : rw_cells asegs mc 7260352 [CB 16 (le8 (Z_to_bv 64 4096) ++ le8 (Z_to_bv 64 7260368))])
          by (apply (rw_cells_reshape mc 7260352 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 7260368)]);
                [cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity| reflexivity| cbn; split; [reflexivity| exact I]
                | apply (proj2 (rw_cells_app asegs _ _ [_] [_])); split; [exact C0| exact C1c]]) end.
      apply (u8arr_of_rw_cells asegs) in CC. clear C0 C1c.
      assert (LCC : Z.of_nat (length (le8 (Z_to_bv 64 4096) ++ le8 (Z_to_bv 64 7260368))) = 16) by (rewrite length_app, !length_le8; reflexivity).
      (* [comment removed for export] *)
      step. st1. step. st1. step. step.
      step. step. step. step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold ia_post, ia_after, AIAINIT, AIAINST. do 7 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FLG|].
      assert (JOIN : forall mm A k1 k2, u8arr asegs mm A (repeat (b8 0) k1) -> u8arr asegs mm (A + Z.of_nat k1) (repeat (b8 0) k2) -> u8arr asegs mm A (repeat (b8 0) (k1 + k2))).
      { intros mm A k1 k2 U1 U2. rewrite repeat_app. apply u8arr_app. rewrite repeat_length. split; assumption. }
      split.
      { replace (Z.to_nat 265664) with (Z.to_nat 8 + (Z.to_nat 262144 + (Z.to_nat 56 + Z.to_nat 3456)))%nat by (clear; lia).
        apply JOIN; [exact P0|]. rewrite (Z2Nat.id 8) by (clear; lia). apply JOIN; [exact P1|]. rewrite (Z2Nat.id 262144) by (clear; lia).
        apply JOIN; [exact P2|]. rewrite (Z2Nat.id 56) by (clear; lia). exact P3. }
      split.
      { apply (rw_cells_of_u8arr asegs) in CC.
        apply (rw_cells_reshape _ _ _ [C8 (wz 4096); C8 (wz (6994688 + 265680))]) in CC; [exact CC| cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity| reflexivity| cbn; repeat split; exact I]. }
      replace (Z.to_nat (528432 - 265680)) with (Z.to_nat (262728 - 16) + Z.to_nat 40)%nat by (clear; lia).
      apply JOIN; [exact P4|]. rewrite (Z2Nat.id (262728 - 16)) by (clear; lia). exact P5.
  Qed.
End IAInit.

