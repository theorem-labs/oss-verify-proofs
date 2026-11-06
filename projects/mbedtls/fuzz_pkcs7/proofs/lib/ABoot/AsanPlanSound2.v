(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanPlanSound2 () : Init.string Init.list := ["OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.kentry"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.expr"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.know_ok"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.kread_bytes"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.estart"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.SA"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.map"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Peano.lt"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.cons"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Datatypes.nil"].


(* [comment removed for export] *)
Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
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
Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

Section Sound2.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SP0 : Z.   (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SP0 SINV argH FS0).

(* [comment removed for export] *)
#[using="SINV argH"] Lemma kread_bytes_sound : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound2 ()) "PE,$0.PM,P,(1.&40.)(2.(1.&8.))Pk,(3.$4.)Pn,$5.Pb,$6.Poff,$7.Pzs,(3.$7.)P,(8.VSEGS,R7.R6.R5.)P,(9.(2.(3.$7.))(:.VSEGS,R5.R6.R4.R3.)(;.(3.$7.)R2.))P,(<.=(=.R9.(>.R5.R4.)))P,(<.(?.(=.R:.(>.R6.R5.))(10.R7.))(11.+2.+40.))(12.(3.(1.&8.))Lbs,(3.(1.&8.))(13.(9.$5.(14.(1.&8.)R1.)R9.)(13.(9.(3.$7.)(15.(1.&8.)$7.(16.&8.)R1.)R6.)Pj,$5.P,(17.R1.R:.)(9.(2.(3.(1.&8.)))(18.VSEGS,R=.(19.&40.(?.(=.R>.(>.R:.R9.))(10.R2.)))#1.)(;.(3.(1.&8.))(1:.(1.&8.)(1;.(1.&8.)R2.R3.(19.&8.=))(1<.(1.&8.))))))))")
(* [comment removed for export] *).
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
#[using="SINV argH"] Lemma rdn_of_bytes1 : ltac2:(CDefT.buildp (gd_tbl_AsanPlanSound2 ()) "PM,P,(1.&40.)(2.(1.&8.))Pn,$5.Pa,(1.&40.)Pbs,(3.(1.&8.))P,(9.$5.(14.(1.&8.)R1.)R3.)P,(<.(?.(16.&40.R3.)(10.R4.))(11.+2.+40.))P,Pj,$5.P,(17.R1.R6.)(9.(2.(3.(1.&8.)))(18.VSEGS,R8.(19.&40.(?.(16.&40.R6.)(10.R2.)))#1.)(;.(3.(1.&8.))(1:.(1.&8.)(1;.(1.&8.)R2.R5.(19.&8.=))(1<.(1.&8.)))))(9.(2.(3.(1.&8.)))(18.VSEGS,R7.R5.R6.)(;.(3.(1.&8.))R4.))")
(* [comment removed for export] *).
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

#[using="Type"] Theorem node_join_sound : join_stmt SEGS A nx0 LIMIT SP0 SINV argH FS0.
Proof.
  intros b off n cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_join in Hn.
  destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia.
  destruct (kread_bytes_sound E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
  apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SP0 SINV argH FS0); [exact HC|]. constructor; [|exact HK].
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
