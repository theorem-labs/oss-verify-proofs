(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasek1dbytes_le_to_Z37Corelib4Init9Datatypeso04conso04list37Corelib4Init5Logicq62eq01Z46Stdlib6ZArith6BinInt1Zs23adds23mulhfbbv_unsignedo06lengthk1dZ_to_le_byteso03nato06option79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~hhc2SA79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~hm36estarto04Someq63ands22les26of_nathf7Z_to_bvo03nilq62ex37Corelib4Init5Peanohu42lt37Corelib5Lists7ListDefhve3maphve3nth79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~ii3bkread_byteshhc3envhhc4exprhhc6kentryhm37know_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ip43rdns23pow79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~itc9join_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jiddhunspell_scfg3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejn57Segmentii36atableo04bool3h5LinuxProcessSemanticsfLinuxProcessSem2Fsjs62Fs" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma bytes_le_to_Z_cons : ltac2:(zQ "a0!h9!jc!n0!p8!pf!ra!rf!ta!u0!u6>1b@1$1@1$0#8>2bs@1$4@1$1@1$0#8@3$5$6@1$2@3$3@1$1@1$0#8^2^1@2$7@2$9@1$0#8^2@2$8@1$2^1+hg0").
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_to_Z : ltac2:(zQ "70!h9!jc!pf!v4!ra!vd!n0>2bs@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@2$5@2$3@1$1@1$0#8^1@1$6^1^1").
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.
End FPX1.

Section Sound2.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable SEGS : ltac2:(zQ "20!pf!jqa@1$0$1").
Variable A : ltac2:(zQ "10!jr5$0").
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : ltac2:(zQ "40!h9!jc!hh3!in0>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
Variable argH : ltac2:(zQ "40!jrf!h9!in0!jc>0$2>0@1$3@1$1#k0$0").
Variable FS0 : ltac2:(zQ "10!jv1$0").

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Lemma kread_bytes_sound : ltac2:(zQ "he0!h9!jc!pf!rf!ra!hgd!hh3!hld!hqa!hr4!hrb!ta!hs1!hs6!hsf!p8!v4!ht9!htf!hv8!ih5!ihc!im1!in0!in7!inf!io9!isf!it6!u6>1E$h7>1M>0@1$1@1$0#k0@1$6@1$1@1$0#8>1k@1$2$h9>1n$5>1b$h8>3off$3>2zs@1$2$3>0@4$ha?4SEGS^7^6^5>0@3$4@1$6@1$2$3@5$h6?4SEGS^5^6^4^3@2$9@1$2$3^2>0@2$cZ@2$8^9@2$7^5^4>0@2$c@2$b@2$8^a@2$7^6^5@1$d^7@2$hc+2+k0@2$h2@1$2@1$1@1$0#8\2bs@1$2@1$1@1$0#8@2$a@3$4$5@2$h0@1$1@1$0#8^1^9@2$a@3$4@1$2$3@4$h4@1$1@1$0#8$3@1$hd@1$0#8^1^6>1j$5>0@2$h3^1^a@3$4@1$6@1$2@1$1@1$0#8@4$hb?4SEGS^d@2$e@1$0#k0@2$b@2$8^e@2$7^a^9@1$d^2N1@2$9@1$2@1$1@1$0#8@3$f@1$1@1$0#8@4$h5@1$1@1$0#8^2^3@2$e@1$0#8Z@1$h1@1$1@1$0#8").
Proof.
  intros E M k n. induction n as [|n IH]; intros b off zs HK Hr Hlo Hhi.
  - cbn in Hr. injection Hr as <-. exists []. repeat split; try reflexivity. intros j Hj. lia.
  - cbn [kread_bytes] in Hr.
    destruct (kreadZ SEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes SEGS n k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate]. injection Hr as <-.
    unfold kreadZ in Hz.
    pose proof (know_lookup_sound SEGS E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as KL.
    destruct (know_lookup SEGS k b off 1 false [] []) as [v scs nx| |]; try discriminate.
    destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection Hz as <-.
    assert (Hfl : flat E (SA b off) (Z.of_nat 1)) by (unfold flat; change (Z.of_nat 1) with 1; rewrite Nat2Z.inj_succ in Hhi; lia).
    destruct (KL ltac:(constructor) Hfl) as [bs1 (R1 & L1 & V1)].
    destruct bs1 as [|b0 [|? ?]]; try (cbn in L1; lia).
    destruct (IH b (off + 1) rest HK Hrest) as [bs (Lb & Mb & Rb)].
    { unfold estart in *; cbn [a_base a_off] in *. lia. }
    { unfold estart in *; cbn [a_base a_off] in *. rewrite Nat2Z.inj_succ in Hhi. lia. }
    exists (b0 :: bs). split; [cbn; lia|]. split.
    + cbn [map]. rewrite Mb. f_equal.
      cbn [edenot] in V1. apply (f_equal bv_unsigned) in V1. rewrite !u_lit64 in V1.
      unfold extz in V1. cbn [bytes_le_to_Z] in V1. rewrite Z.shiftl_0_l, Z.lor_0_r in V1.
      pose proof (u8_range b0). unfold two64 in *. rewrite Z.mod_small in V1 by lia. exact V1.
    + intros j Hj. destruct j as [|j].
      * cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite <- R1. reflexivity.
      * cbn [nth]. rewrite <- (Rb j) by lia. f_equal. f_equal. unfold estart; cbn [a_base a_off]. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_bytes1 : ltac2:(zQ "h30!h9!jc!pf!hgd!hh3!ra!hr4!isf!ta!hs6!hsf!u6!p8!v4!ht9!hv8!ihc!hs1!it6>1M>0@1$1@1$0#k0@1$4@1$1@1$0#8>1n$3>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>0@3$5$3@2$d@1$1@1$0#8^1^3>0@2$h1@2$8@2$b@1$0#k0^3@1$9^4@2$h2+2+k0>0>1j$3>0@2$f^1^6@3$5@1$4@1$2@1$1@1$0#8@4$7?4SEGS^8@2$a@1$0#k0@2$8@2$b@1$0#k0^6@1$9^2N1@2$6@1$2@1$1@1$0#8@3$c@1$1@1$0#8@4$h0@1$1@1$0#8^2^5@2$a@1$0#8Z@1$e@1$1@1$0#8@3$5@1$4@1$2@1$1@1$0#8@4$7?4SEGS^7^5^6@2$6@1$2@1$1@1$0#8^4").
Proof.
  intros M n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
  - destruct bs; [reflexivity | cbn in Hlen; lia].
  - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
    pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
    destruct n as [|n'].
    + destruct bs'; [exact H0 | cbn in Hlen; lia].
    + apply rdn_cons1; [exact H0|].
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      apply IH; [lia | rewrite Hu1; lia |].
      intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
      exact (Hpt (S j) ltac:(lia)).
Qed.

Theorem node_join_sound : ltac2:(zQ "20!ji0!jm4@9$0?2fx?4SEGS$1?1A?3nx0?5LIMIT?4SINV?4argH?3FS0").
Proof.
  intros b off n cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_join in Hn.
  destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia.
  destruct (kread_bytes_sound E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
  apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH FS0); [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [unfold flat; lia|].
  rewrite (rdn_of_bytes1 _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n)); [lia | unfold flat; lia].
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n)) by (unfold flat; lia). exact (Rb j Hj).
Qed.
End Sound2.
