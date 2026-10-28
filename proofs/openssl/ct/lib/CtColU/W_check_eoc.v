(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG ApBase ApState ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApWalkTac W_get_object_walk ApUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.
Notation zxb_lit := CtRepU.W_get_object_walk.zxb_lit.
Import CtRepU.W_get_object_walk(signed_small, znth_range).

Lemma land_ones64_small : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Definition CHECK_EOC : Z := 0x112abc.

(* [comment removed for export] *)
Definition eoc_test (d : list Z) (p len : Z) : bool := (2 <=? len) && (znth d p =? 0) && (znth d (p + 1) =? 0).

(* [comment removed for export] *)
Lemma check_eoc_walk : forall (S PP : Z) (ra gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (FA : bvmap 5 word) (fcA : bv 32) (mA : mem) (lo D p len : Z) (d : list Z),
  stk ctusegs mA lo S -> mem_inv ctusegs mA -> lo + 16 <= S -> S <= 2^63 -> S mod 16 = 0 ->
  rw_cells ctusegs mA PP [C8 (Z_to_bv 64 (D + p))] -> PP mod 8 = 0 -> 0 <= PP -> PP + 8 <= 2^63 -> (PP + 8 <= S - 16 \/ S <= PP) -> (D + zlength d <= PP \/ PP + 8 <= D) ->
  bytes_at ctusegs mA D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> 0 < D -> D + zlength d <= lo -> D + zlength d < 2^63 ->
  0 <= p -> 0 < len -> p + len <= zlength d ->
  evt ctusegs (fun ms' => exists (y11 y12 : word) mq,
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp x5 x6 x7 x8 x9
                   (Z_to_bv 64 (if eoc_test d p len then 1 else 0)) y11 y12 x13 x14 x15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               FA (ret_pc ra) fcA None mq (seg_rom ctusegs)
      /\ munch [(S - 16, S); (PP, PP + 8)]%Z mA mq /\ wmono ctusegs mA mq /\ mem_inv ctusegs mq /\ stk ctusegs mq lo S
      /\ rw_cells ctusegs mq PP [C8 (Z_to_bv 64 (D + (if eoc_test d p len then p + 2 else p)))])
    (MS (mkR ra (Z_to_bv 64 S) gp tp x5 x6 x7 x8 x9
             (Z_to_bv 64 PP) (Z_to_bv 64 len) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         FA (Z_to_bv 64 CHECK_EOC) fcA None mA (seg_rom ctusegs)).
Proof.
  intros until d. intros STA MIA LO TOP S16 HPP ALP PP0 PPhi PPoff PPD HB DF D0 DLO D63 P0 LEN0 PL.
  assert (LO0 : 0 <= lo) by (destruct STA as [H _]; exact H).
  assert (BY : forall i, 0 <= i < zlength d -> 0 <= znth d i < 256) by (intros i Hi; apply znth_range; exact DF).
  assert (DLEN : Z.of_nat (length (to_bytes d)) = zlength d) by (unfold to_bytes, zlength; rewrite ?length_map, ?map_length; reflexivity).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; clear - LO LO0 TOP; lia).
  assert (E16 : bv_unsigned (Z_to_bv 64 (S + -16)) = S + -16) by (apply unsigned_lit; clear - LO LO0 TOP; lia).
  assert (EPP : bv_unsigned (Z_to_bv 64 PP) = PP) by (apply unsigned_lit; clear - PP0 PPhi; lia).
  assert (EDP : bv_unsigned (Z_to_bv 64 (D + p)) = D + p) by (apply unsigned_lit; clear - D0 P0 PL LEN0 D63; lia).
  pose proof (munch_refl [(S - 16, S); (PP, PP + 8)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
  ual.
  change (frozen (bytes_at ctusegs mA D (to_bytes d))) in HB.
  unfold CHECK_EOC.
  (* [comment removed for export] *)
  destruct (stk_carve ctusegs mA lo S 16 STA ltac:(clear - LO; lia)) as [STE [junkE FRE]]. clear STA.
  change (Z.of_nat 16) with 16 in STE, FRE. replace (S - 16) with (S + -16) in STE, FRE by (clear; lia).
  step. step. step. step. step.
  (* [comment removed for export] *)
  name_mem m1. unfold frozen in HB.
  assert (HB1 : bytes_at ctusegs m1 D (to_bytes d)).
  { eapply bytes_at_transport; [exact HB| eassumption|]. cbn [disjoint_from fst snd]. rewrite DLEN. clear - DLO LO PPD; lia. }
  clear HB.
  (* [comment removed for export] *)
  step. if_cases KL2; zc KL2.
  - (* [comment removed for export] *)
    replace (eoc_test d p len) with false by (unfold eoc_test; symmetry; replace (2 <=? len) with false by (symmetry; apply Z.leb_gt; revert KL2; rewrite ?signed_small by (clear - LEN0 PL DLO LO TOP D0 P0 D63; lia); clear; intros KL2; lia); reflexivity).
    step. do 3 step. release_frame FRE STE S. step.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. repeat (split; [assumption|]); assumption.
  - assert (L2 : 2 <= len) by (revert KL2; rewrite ?signed_small by (clear - LEN0 PL DLO LO TOP D0 P0 D63; lia); clear; intros KL2; lia). clear KL2.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (BY p ltac:(clear - P0 LEN0 PL L2; lia)) as R0. pose proof (BY (p + 1) ltac:(clear - P0 LEN0 PL L2; lia)) as R1.
    pose proof (payload_read m1 D d p (wa (D + p)) HB1 DF ltac:(clear - P0 LEN0 PL L2; lia) eq_refl) as RD. step. clear RD. rewrite (zxb_lit (znth d p)) by exact R0.
    step. if_cases K2; zc K2; rewrite ?(land_ones64_small (znth d p)) in K2 by (clear - R0; lia).
    + (* [comment removed for export] *)
      replace (eoc_test d p len) with false by (unfold eoc_test; rewrite (proj2 (Z.eqb_neq (znth d p) 0) K2), andb_false_r; reflexivity).
      step. do 3 step. release_frame FRE STE S. step.
      apply evt_done. eexists _, _, _. split; [reflexivity|]. repeat (split; [assumption|]); assumption.
    + (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof (payload_read m1 D d (p + 1) (wa (D + p + 1)) HB1 DF ltac:(clear - P0 LEN0 PL L2; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD.
      rewrite (zxb_lit (znth d (p + 1))) by exact R1.
      step. if_cases K3; zc K3; rewrite ?(land_ones64_small (znth d (p + 1))) in K3 by (clear - R1; lia).
      * (* [comment removed for export] *)
        replace (eoc_test d p len) with true by (unfold eoc_test; rewrite (proj2 (Z.leb_le 2 len) L2), (proj2 (Z.eqb_eq _ _) K2), (proj2 (Z.eqb_eq _ _) K3); reflexivity).
        (* [comment removed for export] *)
        step. setreg 11%Z (Z_to_bv 64 (D + (p + 2))) ltac:(rewrite ?EDP; f_equal; clear; lia).
        step. step. step. do 3 step. release_frame FRE STE S. step.
        apply evt_done. eexists _, _, _. split; [reflexivity|]. repeat (split; [assumption|]); assumption.
      * (* [comment removed for export] *)
        replace (eoc_test d p len) with false by (unfold eoc_test; rewrite (proj2 (Z.eqb_neq (znth d (p + 1)) 0) K3), andb_false_r; reflexivity).
        step. do 3 step. release_frame FRE STE S. step.
        apply evt_done. eexists _, _, _. split; [reflexivity|]. repeat (split; [assumption|]); assumption.
Qed.
