(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool37Corelib7Numbers7BinNumshe1N37Corelib7StringsaPrimStringjb6string06optionhe4Npos35stdpp9bitvectorbdefinitionsmf2bv05false04true3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticspebhex_byte_at37Corelib4Init5Logicu32eq04None03natu33not69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexScan~~~~~~hgd5scanN46Stdlib6NArith6BinNat1Nhl43addhl42lt04Somehgd6zscanNmf7Z_to_bv46Stdlib6ZArith6BinInt1Zhp34of_N04cons03nil57Corelib7Numbers6Cyclic5Int63cUint63Axiomshre4to_Zjb6lengthpefsegment_byte_athl42lehp33divhp32lthp34to_N" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.

Definition byte_ok : ltac2:(zQ "30!h8!j7!l7>1s$2>3off$1$0") := ltac2:(zQ "90!m0!m8!oc!h8!p1!p8!j7!l7!t5\1s$7\3off$6M0\1x@1$0@1$2@1$1#8$3@2$8^2^1\1b@1$2@1$1#8$5$4").

(* [comment removed for export] *)
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_ok s base
      else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
  end.

Lemma scanN_sound : ltac2:(zQ "f0!j7!v7!m8!oc!vc!h8!hg2!m0!p8!hg7!l7!t5!hkb!hmc!hn3>1s$a>4fuel$6>4base$0>1n$0>0@3$1$5@4$c^4^3^2^1$8>1i$0>0@2$e^1^3@1$9@3$1@1$7@1$3@1$2#8@2$b^7@2$d^5^2@1$4@1$3@1$2#8").
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
      destruct (hex_byte_at s base); [discriminate|discriminate].
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f => if N.eqb n 0 then true
           else if N.eqb n 1 then match hex_byte_at s base with Some b => Z.eqb (bv_unsigned b) 0 | None => false end
           else let hh := N.div2 n in (zscanN s f base hh && zscanN s f (base + hh)%N (n - hh)%N)%bool
  end.
Lemma zscanN_sound : ltac2:(zQ "f0!j7!m8!v7!oc!hn9!h8!hg2!m0!p8!l7!t5!hnf!hmc!hn3!ho9>1s$9>4fuel$6>4base$0>1n$0>0@3$2$5@4$b^4^3^2^1$8>1i$0>0@2$d^1^3@3$2@1$7@1$3@1$1#8@2$a^7@2$c^5^2@2$4@1$3@1$1#8@2$e@1$1#8Z").
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|]. destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. destruct (hex_byte_at s base) as [b|]; [|discriminate].
      apply Z.eqb_eq in H. f_equal. rewrite <- H. symmetry. apply definitions.Z_to_bv_bv_unsigned.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (hh := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i hh) as [Hl|Hge]; [exact (IH _ _ H1 i Hl)|].
      specialize (IH _ _ H2 (i - hh)%N ltac:(lia)). rewrite <- IH. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_some_pt : ltac2:(zQ "h40!m8!oc!j7!l7!vc!m0!v7!hg7!hqb!hr3!hr9!hu9!hv1!t5!hva!igc!hn3!ih2!ih9!ihf>1s$3>1n$2>3off$2>0>1i$2>0@2$h0^1^3@1$7@3$6@1$5@1$1@1$0#8@2$d^5^2@1$4@1$1@1$0#8>0@2$f^3@1$h3@2$h1@1$b@1$c^4+2>0@2$h2@1$8^3@1$8^4@1$7@3$6@1$5@1$1@1$0#8@2$e@3$9$3^6@1$a$3^4@1$4@1$1@1$0#8").
Proof.
  intros s n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
    by (symmetry; apply N.ltb_lt; lia).
  apply Hs. lia.
Qed.
(* [comment removed for export] *)
