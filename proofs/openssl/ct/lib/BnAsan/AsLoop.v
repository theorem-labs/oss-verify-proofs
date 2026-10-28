(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import BnBase.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition shb_cells (segs : list Segment) (gotc shbv : Z) (m : word -> option byte) : Prop :=
  ro_cells segs m gotc [C8 (Z_to_bv 64 shbv)] /\ ro_cells segs m shbv [C8 (Z_to_bv 64 SHB)].

Definition aptrs3 (rp ap bp n lo : Z) : Prop :=
  rp mod 8 = 0 /\ ap mod 8 = 0 /\ bp mod 8 = 0 /\ (rp + 8 * n <= SHLO \/ SHHI <= rp) /\ SHHI <= lo.

Definition apure (rp ap bp n SP FS : Z) : Prop :=
  (rp mod 8 = 0 /\ ap mod 8 = 0 /\ bp mod 8 = 0)
  /\ (0 <= rp /\ rp + 8 * n <= 140737488355328) /\ (0 <= ap /\ ap + 8 * n <= 140737488355328)
  /\ (0 <= bp /\ bp + 8 * n <= 140737488355328)
  /\ offshW [(rp, rp + 8 * n); (SP - FS, SP)].

Section WithSegs.
Variable segs : list Segment.

Lemma apure_intro : forall m rp ap bp (a b : list Z) lo SP FS,
  aptrs3 rp ap bp (Z.of_nat (length a)) lo -> length b = length a -> 0 < Z.of_nat (length a) ->
  limbs_at segs m ap a -> limbs_at segs m bp b -> wr_at segs m rp (8 * Z.of_nat (length a)) -> mem_inv segs m ->
  lo <= SP - FS -> 0 <= FS ->
  apure rp ap bp (Z.of_nat (length a)) SP FS.
Proof.
  intros m rp ap bp a b lo SP FS (A1 & A2 & A3 & A4 & A5) LEN Hn RA RB WR MI LO HFS.
  pose proof (wr_at_below segs m rp _ MI WR ltac:(lia)) as TR. unfold UTOP in TR.
  assert (NE : forall l : list Z, 0 < Z.of_nat (length l) -> lbytes l <> []).
  { intros l Hl E. pose proof (lbytes_lengthZ l) as L. rewrite E in L. cbn [length] in L. lia. }
  pose proof (NE a Hn) as NA. pose proof (NE b ltac:(rewrite LEN; exact Hn)) as NB.
  pose proof (bytes_at_below segs m ap _ MI RA NA) as TA. rewrite lbytes_lengthZ in TA. unfold UTOP in TA.
  pose proof (bytes_at_below segs m bp _ MI RB NB) as TB. rewrite lbytes_lengthZ, LEN in TB. unfold UTOP in TB.
  pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB.
  destruct WR as (W0 & _).
  unfold apure. split; [tauto|]. split; [lia|]. split; [lia|]. split; [lia|].
  cbn [offshW]. unfold SHLO, SHHI in *. split; [exact A4|]. split; [right; lia | exact I].
Qed.

Lemma acc_rd_limb : forall W m m1 p n off k ad,
  acc segs m p (8 * n) -> munch W m m1 -> offshW W ->
  p mod 8 = 0 -> 0 <= p /\ p + 8 * n <= 140737488355328 ->
  off mod 8 = 0 -> 0 <= off -> 0 <= k -> off + 8 * k + 8 <= 8 * n ->
  ad = wa (shad (p + off + 8 * k)) ->
  ov_read_bytes segs m1 ad 1 = Some [z8].
Proof.
  intros W m m1 p n off k ad ACC MU OFF Hp Rp Ho H0 Hk Hle ->.
  apply (acc_rd0 segs W m m1 p (8 * n) (p + off + 8 * k) _ ACC MU OFF); [ | lia | lia | lia | reflexivity].
  clear - Hp Ho. Z.div_mod_to_equations. lia.
Qed.

End WithSegs.

Lemma INV_munch : forall segs fl fcy CB m rp ap bp SP lo (a : list Z) FS FB FCELLS res cy m1 pre la lb c pa pb pr,
  INV segs fl fcy CB m rp ap bp SP lo a FS FB FCELLS res cy m1 pre la lb c pa pb pr ->
  munch [(rp, rp + 8 * Z.of_nat (length a)); (SP - FS, SP)] m m1.
Proof. intros. unfold INV in H. tauto. Qed.

Lemma apure_off : forall rp ap bp n SP FS, apure rp ap bp n SP FS -> offshW [(rp, rp + 8 * n); (SP - FS, SP)].
Proof. intros. unfold apure in H. tauto. Qed.
Lemma apure_r : forall rp ap bp n SP FS, apure rp ap bp n SP FS -> rp mod 8 = 0 /\ (0 <= rp /\ rp + 8 * n <= 140737488355328).
Proof. intros. unfold apure in H. tauto. Qed.
Lemma apure_a : forall rp ap bp n SP FS, apure rp ap bp n SP FS -> ap mod 8 = 0 /\ (0 <= ap /\ ap + 8 * n <= 140737488355328).
Proof. intros. unfold apure in H. tauto. Qed.
Lemma apure_b : forall rp ap bp n SP FS, apure rp ap bp n SP FS -> bp mod 8 = 0 /\ (0 <= bp /\ bp + 8 * n <= 140737488355328).
Proof. intros. unfold apure in H. tauto. Qed.

Lemma apure_bounds : forall rp ap bp n SP FS, apure rp ap bp n SP FS ->
  (0 <= rp /\ rp + 8 * n <= 140737488355328) /\ (0 <= ap /\ ap + 8 * n <= 140737488355328) /\ (0 <= bp /\ bp + 8 * n <= 140737488355328).
Proof. intros. unfold apure in H. tauto. Qed.

Section KitSh.
  Variable segs : list Segment.
  Variables (fl fcy : Z -> Z -> Z -> Z) (CB : Z).
  Variables (m : word -> option byte) (rp ap bp SP lo : Z) (a : list Z).
  Variables (FS FB : Z) (FCELLS : list cell).
  Variables (res : list Z) (cy : Z).
  Notation n := (Z.of_nat (length a)).
  Hypothesis PB : apure rp ap bp n SP FS.
  Notation KINV := (INV segs fl fcy CB m rp ap bp SP lo a FS FB FCELLS res cy).

  Lemma INV_geom : forall m1 pre la lb c pa pb pr, KINV m1 pre la lb c pa pb pr ->
    pa = ap + 8 * Z.of_nat (length pre) /\ pb = bp + 8 * Z.of_nat (length pre) /\ pr = rp + 8 * Z.of_nat (length pre)
    /\ Z.of_nat (length pre) + Z.of_nat (length la) = n /\ munch [(rp, rp + 8 * n); (SP - FS, SP)] m m1.
  Proof using. intros m1 pre la lb c pa pb pr I. unfold INV in I. tauto. Qed.

  Lemma INV_shA : forall m1 pre la lb c pa pb pr k x ad,
    KINV m1 pre la lb c pa pb pr -> acc segs m ap (8 * n) -> nth_error la k = Some x ->
    ad = wa (shad (pa + 8 * Z.of_nat k)) -> ov_read_bytes segs m1 ad 1 = Some [z8].
  Proof using PB.
    intros m1 pre la lb c pa pb pr k x ad I ACC Hn ->.
    destruct (INV_geom _ _ _ _ _ _ _ _ I) as (Ea & Eb & Er & En & MU).
    assert (Hk : (k < length la)%nat) by (apply nth_error_Some; congruence).
    destruct (apure_a _ _ _ _ _ _ PB) as (P8 & PR).
    apply (acc_rd_limb segs _ m m1 ap n (8 * Z.of_nat (length pre)) (Z.of_nat k) _ ACC MU (apure_off _ _ _ _ _ _ PB) P8 PR);
      [ clear; Z.div_mod_to_equations; lia | lia | lia | lia | rewrite Ea; reflexivity ].
  Qed.

  Lemma INV_shB : forall m1 pre la lb c pa pb pr k x ad,
    KINV m1 pre la lb c pa pb pr -> acc segs m bp (8 * n) -> nth_error la k = Some x ->
    ad = wa (shad (pb + 8 * Z.of_nat k)) -> ov_read_bytes segs m1 ad 1 = Some [z8].
  Proof using PB.
    intros m1 pre la lb c pa pb pr k x ad I ACC Hn ->.
    destruct (INV_geom _ _ _ _ _ _ _ _ I) as (Ea & Eb & Er & En & MU).
    assert (Hk : (k < length la)%nat) by (apply nth_error_Some; congruence).
    destruct (apure_b _ _ _ _ _ _ PB) as (P8 & PR).
    apply (acc_rd_limb segs _ m m1 bp n (8 * Z.of_nat (length pre)) (Z.of_nat k) _ ACC MU (apure_off _ _ _ _ _ _ PB) P8 PR);
      [ clear; Z.div_mod_to_equations; lia | lia | lia | lia | rewrite Eb; reflexivity ].
  Qed.

  Lemma INV_shR : forall m1 pre la lb c pa pb pr k x ad,
    KINV m1 pre la lb c pa pb pr -> acc segs m rp (8 * n) -> nth_error la k = Some x ->
    ad = wa (shad (pr + 8 * Z.of_nat k)) -> ov_read_bytes segs m1 ad 1 = Some [z8].
  Proof using PB.
    intros m1 pre la lb c pa pb pr k x ad I ACC Hn ->.
    destruct (INV_geom _ _ _ _ _ _ _ _ I) as (Ea & Eb & Er & En & MU).
    assert (Hk : (k < length la)%nat) by (apply nth_error_Some; congruence).
    destruct (apure_r _ _ _ _ _ _ PB) as (P8 & PR).
    apply (acc_rd_limb segs _ m m1 rp n (8 * Z.of_nat (length pre)) (Z.of_nat k) _ ACC MU (apure_off _ _ _ _ _ _ PB) P8 PR);
      [ clear; Z.div_mod_to_equations; lia | lia | lia | lia | rewrite Er; reflexivity ].
  Qed.
End KitSh.

Ltac sh_addr_k :=
  unfold wa, shad; f_equal; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear; Z.div_mod_to_equations; lia.

Ltac ld_sh_with L I ACC k := let ad := cur_mem_addr in let RD := fresh "RD" in
  pose proof (L _ _ _ _ _ _ _ _ k _ ad I ACC eq_refl ltac:(sh_addr_k)) as RD; zstep; clear RD.

Ltac sh_addr :=
  unfold wa, shad; f_equal; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8;
  clear; Z.div_mod_to_equations; lia.

Ltac chk0 := zstep; rewrite ?zxb_z8, ?sxb_z8; if_false.
