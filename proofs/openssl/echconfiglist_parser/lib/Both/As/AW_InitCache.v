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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_InitCacheA AW_InitCacheB.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocTacX.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].
(* [comment removed for export] *)
Ltac cbr := let K := fresh "K" in if_cases K; zify_cond K; first [ deadK K | clear K ].
(* [comment removed for export] *)
Ltac lits :=
  repeat match goal with
         | |- context [v_sltiu ?a ?b] => let v := eval vm_compute in (v_sltiu a b) in change (v_sltiu a b) with v
         | |- context [v_sltu ?a ?b] => let v := eval vm_compute in (v_sltu a b) in change (v_sltu a b) with v
         end;
  fold_closed_in_goal; zb_fold_lits.
(* [comment removed for export] *)
Ltac run_to tgt :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 tgt) _ _ _ _) => fail
          | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; fix_lit_store; lits; try cbr
          end).

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma ic_trip : forall (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mc0 cs0 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (A c : Z),
  mem_inv asegs m -> akobj A 96 /\ A + 96 <= aceil /\ A mod 8 = 0 ->   (* [comment removed for export] *)
  rw_cells asegs m (A + 4) [C4 mc0] -> rw_cells asegs m (A + 8) [C8 cs0] -> 1 <= c <= 31 ->
  evt asegs (ic_trip_post ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 a2 a4 (wz 15) (wz 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m A c)
    (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 (wz (A + 8)) a2 (wz (32 * c)) a4 (Z_to_bv 64 (c - 16)) (wz 15) (wz 1024)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19be50) fc None m (seg_rom asegs)).
Proof.
  intros. destruct (Z.le_gt_cases c 16).
  - eapply ic_trip_lo; eauto. lia.
  - eapply ic_trip_hi; eauto. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint icW_from (CA : Z) (c : Z) (k : nat) : list (Z * Z) :=
  match k with O => [] | S k' => (CA + 80 * c + 4, CA + 80 * c + 16) :: icW_from CA (c + 1) k' end.
(* [comment removed for export] *)
Definition icW (CA : Z) : list (Z * Z) := icW_from CA 1 31.

(* [comment removed for export] *)
Lemma icW_from_sub : forall CA k c0 c, c0 <= c < c0 + Z.of_nat k -> sub_fp [(CA + 80 * c + 4, CA + 80 * c + 16)]%Z (icW_from CA c0 k).
Proof.
  intros CA k. induction k as [|k IH]; intros c0 c Hc x OUT; [exfalso; clear - Hc; lia|].
  cbn [icW_from outside] in OUT. destruct OUT as [O1 O2].
  destruct (Z.eq_dec c c0) as [->|NE].
  - cbn [outside]. split; [exact O1| exact I].
  - apply (IH (c0 + 1) c); [clear - Hc NE; lia| exact O2].
Qed.
Lemma icW_sub : forall CA c, 1 <= c <= 31 -> sub_fp [(CA + 80 * c + 4, CA + 80 * c + 16)]%Z (icW CA).
Proof. intros CA c Hc. unfold icW. apply icW_from_sub. clear - Hc. cbn. lia. Qed.

Definition ic_loop_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : mem) (CA : Z) : machine_state -> Prop :=
  fun ms' => exists (t3 t4 t5 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (CA + 80 * 32 + 8)) a2 (wz (32 * 32)) a4 (Z_to_bv 64 16) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19bea4) fc None m' (seg_rom asegs)
    /\ munch (icW CA) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ (forall c', 1 <= c' <= 31 -> rw_cells asegs m' (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 (wz (class_size c'))]).

Section Loop.
  Variables (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Variable CA : Z.
  Hypothesis CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0.

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Lemma ic_loop : forall (k : nat) (c : Z) (t3 t4 t5 : word) (m : mem),
    Z.to_nat (32 - c) = k -> 1 <= c <= 31 ->
    mem_inv asegs m -> munch (icW CA) m0 m -> wmono asegs m0 m ->
    (forall c', 1 <= c' < c -> rw_cells asegs m (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m (CA + 80 * c' + 8) [C8 (wz (class_size c'))]) ->
    (forall c', c <= c' <= 31 -> exists mc cs, rw_cells asegs m (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m (CA + 80 * c' + 8) [C8 cs]) ->
    evt asegs (ic_loop_post ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 a2 a4 (wz 15) (wz 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m0 CA)
      (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 (wz (CA + 80 * c + 8)) a2 (wz (32 * c)) a4 (Z_to_bv 64 (c - 16)) (wz 15) (wz 1024)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19be50) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO in CAR. acb.
    induction k as [|k IH]; intros c t3 t4 t5 m HK Hc MI MU WM DONE CELLS. { exfalso. clear - HK Hc; try acb. lia. }
    destruct (CELLS c ltac:(hci; clear - Hc; try acb; lia)) as (mc & cs & MC & CS).
    replace (CA + 80 * c + 8) with (CA + 80 * c + 0 + 8) by (clear; lia).
    replace (CA + 80 * c + 4) with (CA + 80 * c + 0 + 4) in MC by (clear; lia).
    replace (CA + 80 * c + 8) with (CA + 80 * c + 0 + 8) in CS by (clear; lia).
    eapply evt_cut.
    { eapply (ic_trip ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mc cs F fc m (CA + 80 * c + 0) c MI); [| exact MC | exact CS | exact Hc].
      unfold AHI_LO. acb. clear - CAR Hc; try acb. Z.div_mod_to_equations. aunf; lia. }
    intros ms' POST. destruct POST as (t3' & t4' & t5' & m' & -> & MU1 & WM1 & MI1 & MC1 & CS1).
    replace (CA + 80 * c + 0 + 88) with (CA + 80 * (c + 1) + 8) by (clear; lia).
    replace (CA + 80 * c + 0 + 4) with (CA + 80 * c + 4) in * by (clear; lia).
    replace (CA + 80 * c + 0 + 8) with (CA + 80 * c + 8) in * by (clear; lia).
    replace (CA + 80 * c + 0 + 16) with (CA + 80 * c + 16) in * by (clear; lia).
    replace (32 * c + 32) with (32 * (c + 1)) by (clear; lia).
    assert (MU' : munch (icW CA) m0 m').
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [apply icW_sub; exact Hc| exact MU1]. }
    assert (WM' : wmono asegs m0 m') by (eapply wmono_trans; [exact WM| exact WM1]).
    assert (DONE' : forall c', 1 <= c' < c + 1 -> rw_cells asegs m' (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 (wz (class_size c'))]).
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [split; [exact MC1| exact CS1]|].
      destruct (DONE c' ltac:(hci; clear - Hc' NE; try acb; lia)) as [D1 D2]. split.
      - eapply rw_cells_transport; [exact D1| exact MU1| exact WM1|]. cbn. clear - Hc' NE; try acb. lia.
      - eapply rw_cells_transport; [exact D2| exact MU1| exact WM1|]. cbn. clear - Hc' NE; try acb. lia. }
    assert (CELLS' : forall c', c + 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m' (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 cs]).
    { intros c' Hc'. destruct (CELLS c' ltac:(hci; clear - Hc' Hc; try acb; lia)) as (mc' & cs' & D1 & D2). exists mc', cs'. split.
      - eapply rw_cells_transport; [exact D1| exact MU1| exact WM1|]. cbn. clear - Hc'; try acb. lia.
      - eapply rw_cells_transport; [exact D2| exact MU1| exact WM1|]. cbn. clear - Hc'; try acb. lia. }
    clear MC CS MC1 CS1 MU1 WM1 DONE CELLS MU WM MI.
    destruct (Z.eqb_spec c 31) as [E31|N31].
    - (* [comment removed for export] *)
      rewrite E31. apply evt_done. unfold ic_loop_post. exists t3', t4', t5', m'.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI1|].
      intros c' Hc'. apply DONE'. clear - Hc' E31; try acb. lia.
    - replace (c - 15) with ((c + 1) - 16) by (clear; lia).
      eapply (IH (c + 1)); try eassumption. { clear - HK Hc N31; try acb. lia. } { clear - Hc N31; try acb. lia. }
  Qed.
End Loop.

End HCW2.

