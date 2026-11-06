(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApUTacB.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs W_get_object_walkA.
From OSSVerify.Proofs.openssl.ct.lib.CtColB Require Import ColDefsA.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import CtUbTabB CtUTacB.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtTimeB Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step.
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
Notation zxb_lit := CtRepP.W_get_object_walk.zxb_lit.
Import CtRepP.W_get_object_walk(signed_small, znth_range).

Lemma land_ones64_small : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Definition CHECK_EOC_B : Z := 0x245908.

(* [comment removed for export] *)
Definition eoc_test (d : list Z) (p len : Z) : bool := (2 <=? len) && (znth d p =? 0) && (znth d (p + 1) =? 0).

Section WithRT.
Context {AR : ARun}.

(* [comment removed for export] *)
Lemma check_eoc_walkB : forall (ra S PP : Z) (gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (FA : bvmap 5 word) (fcA : bv 32) (mA : mem) (lo D p len Pa Pn Da Dn : Z) (d : list Z),
  (ra = 0x246394 \/ ra = 0x244660) ->
  stk ctbsegs mA lo S -> mem_inv ctbsegs mA -> shb_cells ctbsegs 6167352 6966904 mA -> SHHI <= lo -> lo + 16 <= S -> S + 16 <= USTACK_TOP -> S mod 16 = 0 ->
  rw_cells ctbsegs mA PP [C8 (Z_to_bv 64 (D + p))] -> PP mod 8 = 0 -> SEGTOP_A <= PP -> PP + 8 <= USTACK_TOP -> (PP + 8 <= SHLO \/ SHHI <= PP) -> (PP + 8 <= S - 16 \/ S <= PP) -> (D + zlength d <= PP \/ PP + 8 <= D) ->
  acc ctbsegs mA Pa Pn -> Pa <= PP -> PP + 8 <= Pa + Pn -> 0 <= Pa -> Pa + Pn <= USTACK_TOP ->
  bytes_at ctbsegs mA D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> 0 < D -> D + zlength d <= lo ->
  acc ctbsegs mA Da Dn -> Da <= D -> D + zlength d <= Da + Dn -> 0 <= Da -> Da + Dn <= lo ->
  0 <= p -> 0 < len -> p + len <= zlength d ->
  evt ctbsegs (fun ms' => exists (y11 y12 y13 y14 y15 : word) mq,
      ms' = MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 S) gp tp x5 x6 x7 x8 x9
                   (Z_to_bv 64 (if eoc_test d p len then 1 else 0)) y11 y12 y13 y14 y15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               FA (Z_to_bv 64 ra) fcA None mq (seg_rom ctbsegs)
      /\ munch [(S - 16, S); (PP, PP + 8)]%Z mA mq /\ wmono ctbsegs mA mq /\ mem_inv ctbsegs mq /\ stk ctbsegs mq lo S
      /\ rw_cells ctbsegs mq PP [C8 (Z_to_bv 64 (D + (if eoc_test d p len then p + 2 else p)))])
    (MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 S) gp tp x5 x6 x7 x8 x9
             (Z_to_bv 64 PP) (Z_to_bv 64 len) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         FA (Z_to_bv 64 CHECK_EOC_B) fcA None mA (seg_rom ctbsegs)).
Proof.
  intros until d. intros RA STA MIA SHBC SEGLO LO TOP S16 HPP ALP PPlo PPhi PPsh PPoff PPD ACCP PaLO PaHI Pa0 PaTop HB DF D0 DLO ACCD DaLO DaHI Da0 DaTop P0 LEN0 PL.
  assert (LO0 : 0 <= lo) by (destruct STA as [H _]; exact H).
  unfold SHHI in SEGLO. unfold SEGTOP_A in PPlo. pose proof PPsh as PPshN. unfold SHLO, SHHI in PPshN. pose proof TOP as TOPN. pose proof PPhi as PPhiN. pose proof PaTop as PaTopN. unfold USTACK_TOP in TOPN, PPhiN, PaTopN.
  assert (BY : forall i, 0 <= i < zlength d -> 0 <= znth d i < 256) by (intros i Hi; apply znth_range; exact DF).
  assert (DLEN : Z.of_nat (length (to_bytes d)) = zlength d) by (unfold to_bytes, zlength; rewrite ?length_map, ?map_length; reflexivity).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; clear - LO LO0 TOPN; lia).
  assert (E16 : bv_unsigned (Z_to_bv 64 (S + -16)) = S + -16) by (apply unsigned_lit; clear - LO LO0 TOPN; lia).
  assert (EPP : bv_unsigned (Z_to_bv 64 PP) = PP) by (apply unsigned_lit; clear - PPlo PPhiN; lia).
  assert (EDP : bv_unsigned (Z_to_bv 64 (D + p)) = D + p) by (apply unsigned_lit; clear - D0 P0 PL LEN0 DLO LO TOPN; lia).
  pose proof (munch_refl [(S - 16, S); (PP, PP + 8)]%Z mA) as MU. pose proof (wmono_refl ctbsegs mA) as WM.
  assert (OFFW : offshW [(S - 16, S); (PP, PP + 8)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - SEGLO LO PPshN; lia).
  ual.
  change (frozen (bytes_at ctbsegs mA D (to_bytes d))) in HB.
  unfold CHECK_EOC_B.
  (* [comment removed for export] *)
  destruct (stk_carve ctbsegs mA lo S 16 STA ltac:(clear - LO; lia)) as [STE [junkE FRE]]. clear STA.
  change (Z.of_nat 16) with 16 in STE, FRE. replace (S - 16) with (S + -16) in STE, FRE by (clear; lia).
  step. step. step. step. step.
  (* [comment removed for export] *)
  name_mem m1. unfold frozen in HB.
  assert (HB1 : bytes_at ctbsegs m1 D (to_bytes d)).
  { eapply bytes_at_transport; [exact HB| eassumption|]. cbn [disjoint_from fst snd]. rewrite DLEN. clear - DLO LO PPD; lia. }
  clear HB.
  (* [comment removed for export] *)
  step. if_cases KL2; zc KL2.
  - (* [comment removed for export] *)
    replace (eoc_test d p len) with false by (unfold eoc_test; symmetry; replace (2 <=? len) with false by (symmetry; apply Z.leb_gt; revert KL2; rewrite ?signed_small by (clear - LEN0 PL DLO LO TOPN D0 P0; lia); clear; intros KL2; lia); reflexivity).
    step. destruct RA as [-> | ->]; (do 3 step; release_frame FRE STE S; step;
      apply evt_done; eexists _, _, _, _, _, _; split; [reflexivity|]; repeat (split; [assumption|]); assumption).
  - assert (L2 : 2 <= len) by (revert KL2; rewrite ?signed_small by (clear - LEN0 PL DLO LO TOPN D0 P0; lia); clear; intros KL2; lia). clear KL2.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. uchk.
    step.
    uchk.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (BY p ltac:(clear - P0 LEN0 PL L2; lia)) as R0. pose proof (BY (p + 1) ltac:(clear - P0 LEN0 PL L2; lia)) as R1.
    pose proof (payload_readA m1 D d p (wa (D + p)) HB1 DF ltac:(clear - P0 LEN0 PL L2; lia) eq_refl) as RD. step. clear RD. rewrite (zxb_lit (znth d p)) by exact R0.
    step. if_cases K2; zc K2; rewrite ?(land_ones64_small (znth d p)) in K2 by (clear - R0; lia).
    + (* [comment removed for export] *)
      replace (eoc_test d p len) with false by (unfold eoc_test; rewrite (proj2 (Z.eqb_neq (znth d p) 0) K2), andb_false_r; reflexivity).
      step. destruct RA as [-> | ->]; (do 3 step; release_frame FRE STE S; step;
        apply evt_done; eexists _, _, _, _, _, _; split; [reflexivity|]; repeat (split; [assumption|]); assumption).
    + (* [comment removed for export] *)
      zstep. uchk.
      (* [comment removed for export] *)
      pose proof (payload_readA m1 D d (p + 1) (wa (D + p + 1)) HB1 DF ltac:(clear - P0 LEN0 PL L2; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD. step. clear RD.
      rewrite (zxb_lit (znth d (p + 1))) by exact R1.
      step. if_cases K3; zc K3; rewrite ?(land_ones64_small (znth d (p + 1))) in K3 by (clear - R1; lia).
      * (* [comment removed for export] *)
        replace (eoc_test d p len) with true by (unfold eoc_test; rewrite (proj2 (Z.leb_le 2 len) L2), (proj2 (Z.eqb_eq _ _) K2), (proj2 (Z.eqb_eq _ _) K3); reflexivity).
        zstep. uchk.
        (* [comment removed for export] *)
        step. setreg 11%Z (Z_to_bv 64 (D + (p + 2))) ltac:(rewrite ?EDP; f_equal; clear; lia).
        step. step. step. destruct RA as [-> | ->]; (do 3 step; release_frame FRE STE S; step;
          apply evt_done; eexists _, _, _, _, _, _; split; [reflexivity|]; repeat (split; [assumption|]); assumption).
      * (* [comment removed for export] *)
        replace (eoc_test d p len) with false by (unfold eoc_test; rewrite (proj2 (Z.eqb_neq (znth d (p + 1)) 0) K3), andb_false_r; reflexivity).
        step. destruct RA as [-> | ->]; (do 3 step; release_frame FRE STE S; step;
          apply evt_done; eexists _, _, _, _, _, _; split; [reflexivity|]; repeat (split; [assumption|]); assumption).
Qed.
End WithRT.
