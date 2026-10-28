(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AsanPlanSoundSums HeapIface
     L5Defs L5Core L5CoreKit PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSrcSMemmove_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit PnModel PnModelFacts.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNCK.
Section G.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Lemma rdn_copy (M M' : word -> option byte) : forall (n : nat) a a', 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> 0 <= a' -> a' + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None) ->
  (forall i, 0 <= i < Z.of_nat n -> M' (Z_to_bv 64 (a' + i)) = M (Z_to_bv 64 (a + i))) ->
  rdn segs M' (Z_to_bv 64 a') n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  induction n as [|n IH]; intros a a' Ha Hn Ha' Hn' D C; [reflexivity|].
  cbn [rdn]. pose proof (C 0 ltac:(lia)) as C0. rewrite !Z.add_0_r in C0. rewrite C0.
  pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
  destruct (M (Z_to_bv 64 a)) as [b0|] eqn:E0; [|exfalso; apply D0; reflexivity].
  rewrite (L5C.add1_lit a), (L5C.add1_lit a').
  rewrite (IH (a + 1) (a' + 1)); [reflexivity|lia|lia|lia|lia| |].
  - intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply D. lia.
  - intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. replace (a' + 1 + i) with (a' + (i + 1)) by lia. apply C. lia.
Qed.

Lemma u64_copy M M' a a' v : 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= a' -> a' + 8 <= 2 ^ 64 -> L5.defined M a 8 ->
  (forall i, 0 <= i < 8 -> M' (Z_to_bv 64 (a' + i)) = M (Z_to_bv 64 (a + i))) -> L5.u64_at segs M a v -> L5.u64_at segs M' a' v.
Proof. intros H1 H2 H3 H4 D C U. unfold L5.u64_at in *. rewrite (rdn_copy M M' 8 a a'); [exact U|lia|lia|lia|lia|exact D|exact C]. Qed.
Lemma u32_copy M M' a a' v : 0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= a' -> a' + 4 <= 2 ^ 64 -> L5.defined M a 4 ->
  (forall i, 0 <= i < 4 -> M' (Z_to_bv 64 (a' + i)) = M (Z_to_bv 64 (a + i))) -> L5.u32_at segs M a v -> L5.u32_at segs M' a' v.
Proof. intros H1 H2 H3 H4 D C U. unfold L5.u32_at in *. rewrite (rdn_copy M M' 4 a a'); [exact U|lia|lia|lia|lia|exact D|exact C]. Qed.
Lemma u8_copy M M' a a' v : 0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= a' -> a' + 1 <= 2 ^ 64 -> L5.defined M a 1 ->
  (forall i, 0 <= i < 1 -> M' (Z_to_bv 64 (a' + i)) = M (Z_to_bv 64 (a + i))) -> L5.u8_at segs M a v -> L5.u8_at segs M' a' v.
Proof. intros H1 H2 H3 H4 D C U. unfold L5.u8_at in *. rewrite (rdn_copy M M' 1 a a'); [exact U|lia|lia|lia|lia|exact D|exact C]. Qed.


Lemma bstate_copy M M' a a' x : 0 <= a -> a + 40 <= 2 ^ 64 -> 0 <= a' -> a' + 40 <= 2 ^ 64 -> L5.defined M a 40 ->
  (forall i, 0 <= i < 40 -> M' (Z_to_bv 64 (a' + i)) = M (Z_to_bv 64 (a + i))) ->
  PNM.bstate_at segs M a x -> PNM.bstate_at segs M' a' x.
Proof.
  intros H1 H2 H3 H4 D C (P0 & P8 & P16 & P24 & P32).
  assert (Cs : forall o n, 0 <= o -> o + n <= 40 -> forall i, 0 <= i < n -> M' (Z_to_bv 64 (a' + o + i)) = M (Z_to_bv 64 (a + o + i))).
  { intros o n Ho Hn i Hi. rewrite <- !Z.add_assoc. apply C. lia. }
  split; [apply (u32_copy M M' a a'); [lia|lia|lia|lia| apply (L5.defined_sub M a 40); [exact D|lia|lia]| intros i Hi; apply C; lia| exact P0]|].
  split; [apply (u64_copy M M' (a + 8) (a' + 8)); [lia|lia|lia|lia| apply (L5.defined_sub M a 40); [exact D|lia|lia]| apply (Cs 8 8); lia| exact P8]|].
  split; [apply (u64_copy M M' (a + 16) (a' + 16)); [lia|lia|lia|lia| apply (L5.defined_sub M a 40); [exact D|lia|lia]| apply (Cs 16 8); lia| exact P16]|].
  split; [apply (u8_copy M M' (a + 24) (a' + 24)); [lia|lia|lia|lia| apply (L5.defined_sub M a 40); [exact D|lia|lia]| apply (Cs 24 1); lia| exact P24]|].
  apply (u64_copy M M' (a + 32) (a' + 32)); [lia|lia|lia|lia| apply (L5.defined_sub M a 40); [exact D|lia|lia]| apply (Cs 32 8); lia| exact P32].
Qed.

Lemma rdn_nth (M : word -> option byte) : forall (n : nat) a bs, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> L5.defined M a (Z.of_nat n) ->
  rdn segs M (Z_to_bv 64 a) n = Some bs -> forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  induction n as [|n IH]; intros a bs Ha Hn D RD i Hi; [lia|].
  cbn [rdn] in RD. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
  destruct (M (Z_to_bv 64 a)) as [b0|] eqn:E0; [|exfalso; apply D0; reflexivity].
  rewrite (L5C.add1_lit a) in RD.
  destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:ER; [|discriminate]. injection RD as <-.
  destruct i as [|i].
  - rewrite Z.add_0_r. exact E0.
  - cbn [nth]. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
    apply (IH (a + 1) rest); [lia|lia| |exact ER|lia]. intros j Hj. replace (a + 1 + j) with (a + (j + 1)) by lia. apply D. lia.
Qed.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Lemma copy_run_eq (pc : Z) (CPY : PMCP.copy1_spec segs pc) (fx : FPState) R M (dst src n r : Z) :
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 n ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  1 <= n -> 0 <= dst -> dst + n < 2 ^ 63 -> 0 <= src -> src + n < 2 ^ 63 -> (dst + n <= src \/ src + n <= dst) ->
  L5.writable segs M dst n -> L5.defined M src n ->
  exists R3 M3, msteps segs (st fx R pc M) (st fx R3 r M3)
    /\ mem_grows M M3
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + n) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ L5.defined M3 dst n
    /\ (forall i, 0 <= i < n -> M3 (Z_to_bv 64 (dst + i)) = M (Z_to_bv 64 (src + i)))
    /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 dst.
Proof.
  intros H10 H11 H12 H1 RA Hn Hd Hdn Hs Hsn AP W D.
  destruct (PMCP.rdn_of_defined segs M (Z.to_nat n) src Hs ltac:(lia)) as (bs & RD & LEN). { rewrite Z2Nat.id by lia. exact D. }
  destruct (CPY fx M (Z_to_bv 64 dst) (Z_to_bv 64 src) n bs R (Z_to_bv 64 r) Hn LEN
              ltac:(rewrite LEN; exact RD)
              ltac:(rewrite LEN; replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
              ltac:(rewrite !L5.unsigned_lit by lia; lia) ltac:(rewrite L5.unsigned_lit by lia; lia) ltac:(rewrite L5.unsigned_lit by lia; lia)
              (L5K.ret_ok_lit r RA) H1 H10 H11 H12) as (R3 & MS & KO & A10).
  exists R3, (wbytes M (Z_to_bv 64 dst) bs). split; [exact MS|]. split; [apply wbytes_grows|].
  split. { intros a Ha Hout. apply PMCP.wbytes_out; [lia| rewrite LEN; lia| exact Ha| rewrite LEN, Z2Nat.id by lia; exact Hout]. }
  split. { pose proof (PMCP.wbytes_defined M dst bs Hd ltac:(rewrite LEN; lia)) as X. rewrite LEN, Z2Nat.id in X by lia. exact X. }
  split.
  { intros i Hi. rewrite <- (Z2Nat.id i) by lia.
    replace (Z_to_bv 64 (dst + Z.of_nat (Z.to_nat i))) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 dst) + Z.of_nat (Z.to_nat i)))
      by (rewrite L5.unsigned_lit by lia; reflexivity).
    rewrite AX2S.wbytes_nth; [| rewrite L5.unsigned_lit by lia; rewrite LEN, Z2Nat.id by lia; lia| rewrite LEN; lia].
    symmetry. apply (rdn_nth M (Z.to_nat n) src bs Hs ltac:(rewrite Z2Nat.id by lia; lia) ltac:(rewrite Z2Nat.id by lia; exact D) RD). lia. }
  split; [intros i Hi; apply (L5K.kept_ok_index R R3 i KO Hi)| exact A10].
Qed.

End G.
End PNCK.
