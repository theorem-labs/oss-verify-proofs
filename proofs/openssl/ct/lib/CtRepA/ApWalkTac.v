(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge Frame Cells Step Mem Arr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac name_mem m := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m end.

Ltac post_call_esp ESP m :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; rewrite ?ESP in PO; revert ms' PO; post_call ctasegs m.

Definition frozen (P : Prop) : Prop := P.

Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => (Z_to_bv 64 0) end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Lemma cells_wf_app' : forall a b, cells_wf (a ++ b) <-> cells_wf a /\ cells_wf b.
Proof. induction a as [|c a IH]; intros b; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells ctasegs m A (cs1 ++ cs2) <-> rw_cells ctasegs m A cs1 /\ rw_cells ctasegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at, wr_at. rewrite cells_wf_app', cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R0 & R1 & R)). rewrite (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption|]| split; [split; assumption|]]; (split; [lia|]; split; [lia|]); intros i Hi; [apply R; lia|].
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply R. lia.
  - intros (((W1 & B1) & (R0 & R1 & R)) & ((W2 & B2) & (R0' & R1' & R'))). rewrite (cells_bytes_length cs1 W1).
    split; [split; [split; assumption| split; assumption]|]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))); [apply R; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply R'. lia.
Qed.


(* [comment removed for export] *)
Lemma shb_cells_munch : forall g c W m m', shb_cells ctasegs g c m -> munch W m m' ->
  (forall x, (g <= x < g + 8 \/ c <= x < c + 8) -> outside W x) -> shb_cells ctasegs g c m'.
Proof.
  intros g c W m m' [H1 H2] MU HO.
  split; (eapply ro_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | eassumption | intros a Ha; apply HO; cbn in Ha; lia]).
Qed.

Section WithRT.
Context {AR : ARun}.
(* [comment removed for export] *)
Lemma AH_shbA : forall Σ OW LB m, BnHeapA.AHEAP Σ OW LB m -> shb_cells ctasegs A_GOT_SHB A_SHB_CELL m.
Proof. intros Σ OW LB m H. exact (AH_shb _ _ _ _ H). Qed.
End WithRT.

(* [comment removed for export] *)
Ltac ApATac.ashb ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let S1 := fresh "SHB1_" in let S2 := fresh "SHB2_" in
      first
        [ match goal with HEAP : BnHeapA.AHEAP _ _ _ mc |- _ => destruct (AH_shb _ _ _ _ HEAP) as [S1 S2] end
        | match goal with SH : shb_cells _ _ _ mc |- _ => destruct SH as [S1 S2] end
        | match goal with
          | HEAP : BnHeapA.AHEAP _ _ _ ?m0, MU : munch ?W ?m0 mc |- _ =>
              destruct (shb_cells_munch _ _ _ _ _ (AH_shb _ _ _ _ HEAP) MU
                          ltac:(intros x Hx; unfold A_GOT_SHB, A_SHB_CELL in Hx; cbn [outside]; unfold BnHeapA.ACEIL, SHLO, SHHI in *; uchk_open; lia)) as [S1 S2]
          | SH : shb_cells _ _ _ ?m0, MU : munch ?W ?m0 mc |- _ =>
              destruct (shb_cells_munch _ _ _ _ _ SH MU ltac:(intros x Hx; cbn [outside]; unfold BnHeapA.ACEIL, SHLO, SHHI in *; uchk_open; lia)) as [S1 S2]
          end
        | fail 100 "ashb: no AHEAP / shb_cells hypothesis reaches the current memory (directly or through a munch footprint)" ]
  end.

(* [comment removed for export] *)
Ltac ablock HEAP HIN ACC OFF :=
  pose proof (proj2 (AH_acc _ _ _ _ _ HEAP HIN)) as ACC; cbn [blk_addr blk_size fst snd] in ACC;
  pose proof (AH_offsh _ _ _ _ _ HEAP HIN) as OFF; cbn [blk_addr blk_size fst snd] in OFF.
