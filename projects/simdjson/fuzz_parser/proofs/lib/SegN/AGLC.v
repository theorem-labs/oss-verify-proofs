(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import SegLibBr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AGLX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module AGC.
Section C.
Variable segs : list Segment.
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma rdn_bytes_at : forall m n A bs, 0 <= A -> A + Z.of_nat n <= 2^64 ->
  rdn segs m (wa A) n = Some bs -> bytes_at segs m A bs.
Proof.
  intros m n. induction n as [|n IH]; intros A bs HA HB H.
  - cbn in H. injection H as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - rewrite rdn_unfold in H.
    change (match m (wa A) with Some b => Some b | None => seg_rom segs (wa A) end) with (mrd segs m (wa A)) in H.
    destruct (mrd segs m (wa A)) as [b|] eqn:Hm; [|discriminate].
    destruct (rdn segs m (wa A + 1)%bv n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    rewrite wa_succ in Hr.
    pose proof (rdn_length _ _ _ _ _ Hr) as Hlen.
    destruct (IH (A + 1) r ltac:(lia) ltac:(lia) Hr) as (_ & _ & IHr).
    split; [lia|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hm.
    + replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IHr. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma kword8_cells : forall E M a v, kentry_ok segs E M (KWord a 8 v) -> cells_at segs M (estart E a) [C8 (edenot E v)].
Proof.
  intros E M a v (_ & Hfl & Hr). split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8.
  rewrite <- AS.PropExec.ov_rdn, Lib.PropExec.ov_rdn in Hr.
  destruct Hfl as (F1 & F2 & F3 & F4).
  apply (rdn_bytes_at M 8 (estart E a)); [lia | cbn [Z.of_nat] in F4 |- *; lia|].
  unfold wa. rewrite <- (flat_u E a (Z.of_nat 8) ltac:(split; [|split; [|split]]; assumption)).
  rewrite Z_to_bv_bv_unsigned. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma kword8_rw : forall E M a v b k n, kentry_ok segs E M (KWord a 8 v) -> kentry_ok segs E M (KWr (SA b k) n) ->
  u (edenot E b) + k <= estart E a -> estart E a + 8 <= u (edenot E b) + k + u (edenot E n) ->
  rw_cells segs M (estart E a) [C8 (edenot E v)].
Proof.
  intros E M a v b k n HW HR H1 H2. split; [exact (kword8_cells E M a v HW)|]. cbn [cells_size csize Nat.add Z.of_nat].
  pose proof (SLB.kn_wr_at segs E M b k n HR) as (W1 & W2 & W3). destruct HW as (_ & (F1 & F2 & F3 & F4) & _).
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (estart E a + i) with (u (edenot E b) + k + (estart E a - (u (edenot E b) + k) + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
Definition awin_eqb (w w' : expr * Z * expr) : bool :=
  let '(b, o, n) := w in let '(b', o', n') := w' in (expr_eqb b b' && Z.eqb o o' && expr_eqb n n')%bool.
Definition awin_cl (G : nat) (w : expr * Z * expr) : bool := let '(b, _, n) := w in (expr_vars_lt G b && expr_vars_lt G n)%bool.

Lemma awin_den_gagree : forall G E0 E w, SP.gagree G E0 E -> eb E0 = eb E -> awin_cl G w = true ->
  SX.awin_den E w = SX.awin_den E0 w.
Proof.
  intros G E0 E [[b o] n] Hg Hb Hc. cbn [awin_cl] in Hc. apply andb_prop in Hc as [Hcb Hcn]. cbn [SX.awin_den].
  rewrite (SP.edenot_gagree G E0 E b Hg Hb Hcb), (SP.edenot_gagree G E0 E n Hg Hb Hcn). reflexivity.
Qed.

Lemma aw_gen_mix : forall E0 E M kn W0 W G,
  know_ok segs E M kn -> SX.aw_genuine E0 (Some W0) -> SP.gagree G E0 E -> eb E0 = eb E ->
  forallb (fun w => (existsb (awin_eqb w) W0 && awin_cl G w) || AGX.win_gen_b kn w)%bool W = true ->
  SX.aw_genuine E (Some W).
Proof.
  intros E0 E M kn W0 W G HK HA0 Hg Hb H w Hw.
  pose proof (proj1 (forallb_forall _ _) H w Hw) as Hw1. apply orb_prop in Hw1 as [Hw1|Hw1].
  - apply andb_prop in Hw1 as [Hex Hcl]. apply existsb_exists in Hex as (w0 & Hw0 & Heq).
    assert (Ew : w = w0).
    { destruct w as [[b o] n], w0 as [[b' o'] n']. cbn [awin_eqb] in Heq.
      apply andb_prop in Heq as [Heq Hn]. apply andb_prop in Heq as [Hb' Ho].
      apply expr_eqb_eq in Hb'. apply Z.eqb_eq in Ho. apply expr_eqb_eq in Hn. subst. reflexivity. }
    subst w0. rewrite (awin_den_gagree G E0 E w Hg Hb Hcl). exact (HA0 w Hw0).
  - exact (AGX.aw_genuine_of_know segs E M kn [w] HK ltac:(cbn [forallb]; rewrite Hw1; reflexivity) w (or_introl eq_refl)).
Qed.

(* [comment removed for export] *)
Lemma sr_map_tl : forall sr, length sr = 32%nat -> map (fun k => sr_get sr (Z_to_bv 5 k)) rkeys = tl sr.
Proof.
  intros sr Hl. do 32 (destruct sr as [|? sr]; [discriminate Hl|]). destruct sr; [|discriminate Hl]. reflexivity.
Qed.
Lemma regs_ok_tl : forall E sr x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31, length sr = 32%nat ->
  map (edenot E) (tl sr) = [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] -> regs_ok E sr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof.
  intros E sr x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Hl H. apply regs_ok_mkR.
  replace (map (fun k => edenot E (sr_get sr (Z_to_bv 5 k))) rkeys) with (map (edenot E) (map (fun k => sr_get sr (Z_to_bv 5 k)) rkeys))
    by (rewrite map_map; reflexivity).
  rewrite (sr_map_tl sr Hl). exact H.
Qed.

(* [comment removed for export] *)
Lemma tm_rename : forall T1 T2 sg E M rom ms,
  ST.tm_okF segs T1 E M rom ms -> ST.t_pc T2 = ST.t_pc T1 ->
  ST.regs_match (ST.t_know T1) (ST.t_regs T1) (map (ST.esub sg) (ST.t_regs T2)) = true ->
  forallb (ST.kimplied segs (ST.t_know T1)) (map (ST.ksub sg) (ST.t_know T2)) = true ->
  ST.tm_okF segs T2 (ST.senv E sg) M rom ms.
Proof.
  intros T1 T2 sg E M rom ms (HZ & HF & (R & Hms & HR & _ & HK)) Hpc HM HB.
  cbn [ST.tstate s_pc s_regs s_log s_know mem_denot] in Hms, HR, HK.
  split; [exact HZ|]. split; [exact HF|]. exists R. cbn [ST.tstate s_pc s_regs s_log s_know mem_denot].
  split; [rewrite Hpc; exact Hms|]. split.
  - intros r. rewrite (HR r). rewrite (ST.regs_match_ok segs E M _ _ _ HK HM r). unfold sr_get.
    destruct (bv_eqb r 0); [reflexivity|]. rewrite ST.esub_den.
    replace (nth (ridx r) (map (ST.esub sg) (ST.t_regs T2)) (ELit 0)) with (ST.esub sg (nth (ridx r) (ST.t_regs T2) (ELit 0)));
      [reflexivity | rewrite <- (map_nth (ST.esub sg) (ST.t_regs T2) (ELit 0) (ridx r)); reflexivity].
  - split; [exact I|]. apply ST.know_ok_ksub. exact (ST.kimplied_all_ok segs E M _ _ HK HB).
Qed.

End C.
End AGC.
