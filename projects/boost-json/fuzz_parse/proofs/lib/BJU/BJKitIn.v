(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshfbbv_unsigned37Corelib4Init9Datatypeska4bool01Z37Corelib4Init5Logicmc2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~o53sxb46Stdlib6ZArith6BinInt1Zs53adds53ltbs53pows53subhf2bvs56modulos53lors53muls56shiftlka4consmc3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hi52b8s52les52ltka3nilka4listmc3iffka3nato58bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hp45rsegska6lengthka6option37Corelib4Init3Nathuc3add37Corelib4Init5Peanoig52le37Corelib5Lists7ListDefihf6firstnihf5skipns56of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~il24cellihf3nthil22C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iq38ro_cellso53le1hf7Z_to_bvka4Some79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6StrFun~~~~~~jg1cmemcmp_model" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma sxb_unsigned : ltac2:(zQ "b0!h9!jc!m2!m9!o0!rf!td!u3!u9!uf!v5>1b@1$a@1$0#8@3$4$3@2$1@1$0#k0@1$5^1M2\0$2$3@2$7@2$1@1$0#8^1+o0@2$1@1$0#8^1@2$9@2$6@2$1@1$0#8^1@2$8+2+k0+hg0").
Proof.
  intros b. unfold sxb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap, bv_wrap. cbn [bv_half_modulus bv_modulus N.sub].
  replace (bv_half_modulus 8) with 128 by reflexivity. replace (bv_modulus 8) with 256 by reflexivity.
  replace (bv_modulus 64) with (2^64) by reflexivity.
  destruct (Z.ltb_spec0 (bv_unsigned b) 128).
  - rewrite (Z.mod_small (bv_unsigned b + 128) 256) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((bv_unsigned b + 128) mod 256) with (bv_unsigned b + 128 - 256). 2:{ Z.div_mod_to_equations. lia. }
    Z.div_mod_to_equations. lia.
Qed.

Lemma word4_lor : ltac2:(zQ "c0!h9!jc!u9!va!v5!td!hg3!hg9!hgf!rf!o0!m9>2b0@1$4@1$0#8>2b1@1$4@1$0#8>2b2@1$4@1$0#8>2b3@1$4@1$0#8@3$a$b@2$6@2$6@2$3@2$8@2$1@1$0#k0@1$9^1+h8@2$2+2+k0@2$3@2$8@2$1@1$0#8^2+h0@2$2+2+k0@2$6@2$3@2$8@2$1@1$0#8^3+8@2$2+2+k0@2$1@1$0#8^4@2$5@2$5@2$5@2$1@1$0#8^4@2$7+hg0@2$1@1$0#8^3@2$7+hggg0@2$1@1$0#8^2@2$3@2$7@2$1@1$0#k0@1$9^1@2$2+2+h8@2$2+2+k0").
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2.
  pose proof (bv_unsigned_in_range 64 (sxb b3)) as R3. unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (bv_unsigned b2 * 2^16)) by lia. rewrite (Z.mod_small (bv_unsigned b1 * 2^8)) by lia.
  rewrite (lor_add (bv_unsigned b1 * 2^8) (bv_unsigned b0) 8); [| lia | lia | Z.div_mod_to_equations; lia].
  rewrite (lor_add ((bv_unsigned (sxb b3) * 2^24) mod 2^64) (bv_unsigned b2 * 2^16) 24); [| lia | lia | Z.div_mod_to_equations; nia].
  rewrite (lor_add _ _ 16); [lia | lia | lia | Z.div_mod_to_equations; nia].
Qed.

Lemma lit4_bytes : ltac2:(zQ "h20!h9!v5!hh8!td!hg9!m9!hhf!hm0!hm6!hmb!jc!hn0!o0!u9!hn6!hnd!rf!va>2b0@1$1@1$0#8>2b1@1$1@1$0#8>2b2@1$1@1$0#8>2b3@1$1@1$0#8>2c0$5>2c1$5>2c2$5>2c3$5>0@2$6@2$8Z^4@2$9^4+hg0>0@2$6@2$8Z^4@2$9^4+hg0>0@2$6@2$8Z^4@2$9^4+hg0>0@2$6@2$8Z^4@2$9^4+o0@2$f@3$c$5@2$3@2$3@2$3@2$a@1$0#8^c@2$4+hg0@2$a@1$0#8^b@2$4+hggg0@2$a@1$0#8^a@2$h1@2$4@2$a@1$0#k0@1$h0^9@2$d+2+h8@2$d+2+k0@2$3@2$3@2$3^8@2$4+hg0^7@2$4+hggg0^6@2$4+hggggg0^5@3$c@1$e@1$1@1$0#8@3$2@1$1@1$0#8^c@3$2@1$1@1$0#8^b@3$2@1$1@1$0#8^a@3$2@1$1@1$0#8^9@1$b@1$1@1$0#8@3$2@1$1@1$0#8@1$7^8@3$2@1$1@1$0#8@1$7^7@3$2@1$1@1$0#8@1$7^6@3$2@1$1@1$0#8@1$7^5@1$b@1$1@1$0#8").
Proof.
  intros b0 b1 b2 b3 c0 c1 c2 c3 H0 H1 H2 H3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2.
  pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
  rewrite sxb_unsigned. destruct (Z.ltb_spec0 (bv_unsigned b3) 128) as [l|l].
  - rewrite Z.mod_small by lia. split.
    + intros E.
      assert (bv_unsigned b0 = c0 /\ bv_unsigned b1 = c1 /\ bv_unsigned b2 = c2 /\ bv_unsigned b3 = c3) as (E0 & E1 & E2 & E3) by lia.
      unfold b8. rewrite <- E0, <- E1, <- E2, <- E3, !definitions.Z_to_bv_bv_unsigned. reflexivity.
    + intros E. injection E as E3 E2 E1 E0. subst b0 b1 b2 b3. unfold b8. rewrite !Z_to_bv_unsigned.
      unfold bv_wrap. change (bv_modulus 8) with 256. rewrite !Z.mod_small by lia. lia.
  - split. { intros E. exfalso. Z.div_mod_to_equations. nia. }
    intros E. injection E as E3 E2 E1 E0. subst b3. unfold b8 in l. rewrite Z_to_bv_unsigned in l.
    unfold bv_wrap in l. change (bv_modulus 8) with 256 in l. rewrite Z.mod_small in l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_sub : ltac2:(zQ "f0!h9!v5!ho3!ho9!ht1!hta!hn6!hu3!hve!ih9!ij6!ik0!m9!td!ik9>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1a$c>2bs@1$6@1$1@1$0#8>1i$2>1n$2>0@4$3$4^5^4^3>0@2$9@2$8^3^2@2$5@1$1@1$0#8^4@4$3$4^7@2$d^6@1$e^4@3$a@1$1@1$0#8^3@3$b@1$1@1$0#8^4^5").
Proof.
  intros m a bs i n BA Hin.
  rewrite <- (firstn_skipn i bs) in BA. apply bytes_at_app in BA. destruct BA as [_ B2].
  rewrite firstn_length_le in B2 by lia.
  rewrite <- (firstn_skipn n (skipn i bs)) in B2. apply bytes_at_app in B2. destruct B2 as [B2 _]. exact B2.
Qed.
Lemma bytes_at_ro_cells4 : ltac2:(zQ "h30!h9!v5!ioe!hh8!hve!ip6!ipd!ht1!hta!hn6!ho3!hn0!hu3!ih9!m9!ho9!ite!td!ik9>1m>0@1$1@1$0#k0@1$c@1$1@1$0#8>1a$e>2bs@1$9@1$1@1$0#8>1i$a>1d@1$1@1$0#8>0@4$f$7^5^4^3>0@2$d@2$4^3N4@2$8@1$1@1$0#8^4@4$h0$7^7@2$h1^6@1$h2^4@3$3$2@1$6@4$5@1$1@1$0#8^4^5^3@3$3$2@1$6@4$5@1$1@1$0#8@2$4^4N1^5^3@3$3$2@1$6@4$5@1$1@1$0#8@2$4^4N2^5^3@3$3$2@1$6@4$5@1$1@1$0#8@2$4^4N3^5^3@1$b$2").
Proof.
  intros m a bs i d BA Hin. split; [cbn; repeat split; exact I|].
  cbn [cells_bytes cbytes app].
  pose proof (bytes_at_sub m a bs i 4 BA Hin) as B4.
  replace (nth i bs d) with (nth (i + 0) bs d) by (f_equal; lia).
  rewrite <- !(nth_skipn i bs). pose proof (length_skipn i bs) as LS.
  destruct (skipn i bs) as [|x0 [|x1 [|x2 [|x3 l]]]]; cbn in LS; try lia. cbn in B4 |- *. exact B4.
Qed.

(* [comment removed for export] *)
Lemma le1_byte : ltac2:(zQ "90!h9!v5!hh8!hn6!hn0!o0!iua!iv0!jc>1w@1$1@1$0#k0@3$5@1$3@1$1@1$0#8@1$6^1@3$2@1$1@1$0#8@2$7@1$0#8@2$8@1$0#k0^1@1$4@1$1@1$0#8").
Proof.
  intros w. pose proof (le1_mod (bv_unsigned w)) as E. rewrite Z_to_bv_bv_unsigned in E. rewrite E. unfold b8. f_equal.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma memcmp_model_range : ltac2:(zQ "b0!m9!hn6!h9!hm6!v5!iva!ho3!hu3!hhf!o0!jjf>1l@1$1@1$4@1$2#8>1r@1$1@1$4@1$2#8>1n$6>1v$0>0@3$9@1$7$0@3$a^4^3^2@2$5$0^1@2$8@2$3-vf^2@2$3^2+vf").
Proof.
  intros l r n. revert l r. induction n as [|n IH]; intros l r v HM; cbn in HM.
  - injection HM as <-. lia.
  - destruct l as [|a l']; [discriminate|]. destruct r as [|b r']; [discriminate|].
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Ra, Rb. cbn in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)); [apply (IH _ _ _ HM)|]. injection HM as <-. lia.
Qed.
