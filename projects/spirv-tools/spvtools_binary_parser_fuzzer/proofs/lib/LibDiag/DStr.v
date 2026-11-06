(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Ox Require F13.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk MemSplit MmapSim RefMemcpyLib LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition zupd (i : Z) (b : Z) (cs : list Z) : list Z :=
  firstn (Z.to_nat i) cs ++ [b] ++ skipn (S (Z.to_nat i)) cs.

Lemma Zlen_zupd : forall i b cs, 0 <= i < Zlen cs -> Zlen (zupd i b cs) = Zlen cs.
Proof.
  intros i b cs Hi. unfold zupd, Zlen in *. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia.
Qed.

Lemma Znth_zupd_eq : forall i b cs, 0 <= i < Zlen cs -> Znth i (zupd i b cs) = b.
Proof.
  intros i b cs Hi. unfold zupd, Znth, Zlen in *.
  rewrite app_nth2; rewrite length_firstn; [|lia]. replace (Z.to_nat i - Nat.min (Z.to_nat i) (length cs))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma Znth_zupd_ne : forall i b cs j, 0 <= i < Zlen cs -> 0 <= j < Zlen cs -> j <> i -> Znth j (zupd i b cs) = Znth j cs.
Proof.
  intros i b cs j Hi Hj Hne. unfold zupd, Znth, Zlen in *.
  destruct (Z.lt_ge_cases j i) as [Hlt|Hge].
  - rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat i)); [reflexivity | lia].
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Z.to_nat j - Nat.min (Z.to_nat i) (length cs))%nat with (S (Z.to_nat j - Z.to_nat i - 1))%nat by lia.
    cbn [app nth]. rewrite nth_skipn. f_equal. lia.
Qed.

Section S.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.

Lemma str_rep_poke : forall A M s d asz cs i b,
  str_rep MI A M s (SLong d asz) cs -> 0 <= i < Zlen cs -> 0 <= b < 256 ->
  str_rep MI A (wbytes M (Z_to_bv 64 (d + i)) [Z_to_bv 8 b]) s (SLong d asz) (zupd i b cs).
Proof using AC SEGS L MI.
  intros A M s d asz cs i b STR Hi Hb.
  destruct STR as (Hs0 & Hs1 & HD & Hlen & HM & FC & FN). cbn [str_cap str_data] in *.
  destruct HM as (Hd0 & Hd16 & Hdsz & Hal & Hmin & HIn & Hdj & F0 & F1 & F2).
  assert (OUT : forall a (k : nat), 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= d + i \/ d + i + 1 <= a) ->
            rdn SEGS (wbytes M (Z_to_bv 64 (d + i)) [Z_to_bv 8 b]) (Z_to_bv 64 a) k = rdn SEGS M (Z_to_bv 64 a) k).
  { intros a k Ha Hk Hd. apply SumWalkTac.rdn_wbytes_out_Z. cbn [length]. lia. }
  unfold str_rep. rewrite Zlen_zupd by lia. cbn [str_cap str_data].
  split; [exact Hs0|]. split; [exact Hs1|]. split; [apply mdef_wbytes; exact HD|]. split; [lia|].
  split.
  { repeat (split; [assumption|]). unfold fld. rewrite !OUT by (cbn; lia). repeat split; assumption. }
  split.
  - intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite Znth_zupd_eq by lia. split; [lia|]. unfold fld.
      change (word_to_le_bytes 1 (Z_to_bv 64 b)) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 b))]. rewrite u64_of_Z by lia.
      change 1%nat with (length [Z_to_bv 8 b]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
    + rewrite Znth_zupd_ne by lia. destruct (FC j Hj) as [Hr HF]. split; [exact Hr|]. unfold fld. rewrite OUT by (cbn; lia). exact HF.
  - unfold fld. rewrite OUT by (cbn; lia). exact FN.
Qed.

Lemma str_rep_wblob : forall A M s m cs i (bs : list byte),
  str_rep MI A M s m cs -> 0 <= i -> i + Z.of_nat (length bs) <= Zlen cs ->
  exists cs', str_rep MI A (wbytes M (Z_to_bv 64 (str_data s m + i)) bs) s m cs' /\ Zlen cs' = Zlen cs.
Proof using AC SEGS L MI.
  intros A M s m cs i bs. revert M cs i.
  induction bs as [|b bs IH]; intros M cs i STR Hi Hlen.
  - exists cs. split; [exact STR | reflexivity].
  - cbn [length] in Hlen.
    assert (STR1 : exists cs1, str_rep MI A (wbytes M (Z_to_bv 64 (str_data s m + i)) [Z_to_bv 8 (bv_unsigned b)]) s m cs1 /\ Zlen cs1 = Zlen cs).
    { destruct m as [|d asz].
      -
        pose proof STR as (Hs0 & Hs1 & HD & Hl & HM & FC & FN). cbn [str_cap str_data] in *. unfold SSO_CAP in *.
        exists (zupd i (bv_unsigned b) cs). split; [|apply Zlen_zupd; lia].
        pose proof (u8_range b) as Hb.
        assert (OUT : forall a (k : nat), 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= s + 1 + i \/ s + 1 + i + 1 <= a) ->
                  rdn SEGS (wbytes M (Z_to_bv 64 (s + 1 + i)) [Z_to_bv 8 (bv_unsigned b)]) (Z_to_bv 64 a) k = rdn SEGS M (Z_to_bv 64 a) k).
        { intros a k Ha Hk Hd. apply SumWalkTac.rdn_wbytes_out_Z. cbn [length]. lia. }
        unfold str_rep. rewrite Zlen_zupd by lia. cbn [str_cap str_data]. unfold SSO_CAP.
        split; [exact Hs0|]. split; [exact Hs1|]. split; [apply mdef_wbytes; exact HD|]. split; [lia|].
        split; [unfold fld; rewrite OUT by (cbn; lia); exact HM|].
        split.
        + intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
          * rewrite Znth_zupd_eq by lia. split; [lia|]. unfold fld.
            change (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b))) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b)))].
            rewrite u64_of_Z by lia.
            change 1%nat with (length [Z_to_bv 8 (bv_unsigned b)]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
          * rewrite Znth_zupd_ne by lia. destruct (FC j Hj) as [Hr HF]. split; [exact Hr|]. unfold fld. rewrite OUT by (cbn; lia). exact HF.
        + unfold fld. rewrite OUT by (cbn; lia). exact FN.
      - exists (zupd i (bv_unsigned b) cs). split; [|apply Zlen_zupd; lia].
        cbn [str_data]. apply str_rep_poke; [exact STR | lia | pose proof (u8_range b); lia]. }
    destruct STR1 as (cs1 & STR1 & HL1).
    rewrite Z_to_bv_bv_unsigned in STR1.
    assert (Hdat : 0 <= str_data s m /\ str_data s m + Zlen cs + 1 <= 2 ^ 63).
    { pose proof STR as (Hs0 & Hs1 & _ & Hl & HM & _). destruct m as [|d asz]; cbn [str_cap str_data] in *; unfold SSO_CAP in *; [lia|].
      destruct HM as (Hd0 & _ & Hdsz & _). lia. }
    destruct (IH _ cs1 (i + 1) ltac:(cbn [wbytes] in STR1 |- *; exact STR1) ltac:(lia) ltac:(rewrite HL1; lia)) as (cs2 & STR2 & HL2).
    exists cs2. split; [|rewrite HL2, HL1; reflexivity].
    cbn [wbytes]. replace (Z_to_bv 64 (str_data s m + i) + 1)%bv with (Z_to_bv 64 (str_data s m + (i + 1))); [exact STR2|].
    apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_unsigned (1 : word)) with 1.
    rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
End S.
