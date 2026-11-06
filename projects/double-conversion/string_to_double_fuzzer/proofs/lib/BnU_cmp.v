(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Abbreviation cmpL_pins :=
  [(28%bv : reg, ZAdd (ZV 32) (ZL 1)); (29%bv : reg, ZV 43); (12%bv : reg, ZV 33); (11%bv : reg, ZAdd (ZV 34) (ZV 44));
   (5%bv : reg, ZSub (ZL 18446744073709551611) (ZV 33)); (6%bv : reg, ZSub (ZL 18446744073709551611) (ZV 34));
   (7%bv : reg, ZAdd (ZV 44) (ZL (-4))); (13%bv : reg, ZV 35);
   (14%bv : reg, ZV 36); (15%bv : reg, ZV 37); (16%bv : reg, ZV 38); (17%bv : reg, ZV 39); (10%bv : reg, ZL (-1)); (1%bv : reg, ZV 42);
   (2%bv : reg, ZV 45)].
Abbreviation cmpL_uvi :=
  [Some (-1, 2 ^ 16); Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 2 ^ 15 - 1); Some (0, 2 ^ 15 - 1);
   Some (0, 2 ^ 16); Some (0, 2 ^ 16); Some (0, 2 ^ 15); Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 64 - 1);
   Some (- 2 ^ 18, 2 ^ 19); Some (- 2 ^ 17, 2 ^ 17); Some (0, 2 ^ 62); Some (0, 2 ^ 64 - 1)].
Abbreviation KA := (KC (ZAdd (ZV 33) (ZV 43)) 0 4 (ZV 40)).
Abbreviation KB := (KC (ZAdd (ZAdd (ZV 34) (ZV 44)) (ZV 43)) 0 4 (ZV 41)).
Abbreviation KS := (KC (ZV 45) 8 8 (ZV 46)).
Definition cmpL_keep : list Z := [1; 3; 4; 5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Ltac cmp_run dirs kn regs m rom i oa ob ea eb ca cb ret sp' s0v xa xb :=
  zx_run SEGS_U constr:(CTX (vi_regs ++ cmpL_uvi) kn (@nil kwin)) 30%nat [0x3685c] constr:(SCR dirs (@nil zx)) constr:(cmpL_pins)
         constr:([i; oa; ob; ea; eb; zlen ca + ea; zlen cb + eb; Z.min ea eb; xa; xb; bv_unsigned ret;
                  4 * (i + 1 - ea); 4 * ea - 4 * eb; sp'; s0v])
         constr:(cmpL_uvi) regs m rom 0x3685c.

#[using="Type"] Lemma cmp_loop_U : forall fuel i regs m (oa ob ea eb sp' s0v : Z) (ca cb : list Z) (ret : word),
  let la := zlen ca + ea in let lb := zlen cb + eb in
  getr regs 28%bv = Z_to_bv 64 (i + 1) -> getr regs 29%bv = Z_to_bv 64 (4 * (i + 1 - ea)) ->
  getr regs 12%bv = Z_to_bv 64 oa -> getr regs 11%bv = Z_to_bv 64 (ob + (4 * ea - 4 * eb)) ->
  getr regs 5%bv = Z_to_bv 64 (18446744073709551611 - oa) -> getr regs 6%bv = Z_to_bv 64 (18446744073709551611 - ob) ->
  getr regs 7%bv = Z_to_bv 64 (4 * ea - 4 * eb + -4) ->
  getr regs 13%bv = Z_to_bv 64 ea -> getr regs 14%bv = Z_to_bv 64 eb -> getr regs 15%bv = Z_to_bv 64 la ->
  getr regs 16%bv = Z_to_bv 64 lb -> getr regs 17%bv = Z_to_bv 64 (Z.min ea eb) -> getr regs 10%bv = Z_to_bv 64 (-1) ->
  getr regs 1%bv = ret -> ret_ok ret -> getr regs 2%bv = Z_to_bv 64 sp' ->
  cellN SEGS_U m (sp' + 8) 8 s0v -> 0 <= sp' -> sp' + 16 <= 2 ^ 62 ->
  arr32 SEGS_U m (oa + 4) ca -> arr32 SEGS_U m (ob + 4) cb -> ok ca -> ok cb ->
  zlen ca <= 128 -> zlen cb <= 128 -> 0 <= ea < 2 ^ 15 -> 0 <= eb < 2 ^ 15 ->
  0 <= oa -> oa + 516 <= 2 ^ 62 -> 0 <= ob -> ob + 516 <= 2 ^ 62 ->
  la = lb -> Z.of_nat fuel = i + 1 - Z.min ea eb -> i <= la - 1 ->
  exists regs',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x3685c) m rom) (mkst regs' ret m rom)
    /\ keeps cmpL_keep regs regs'
    /\ getr regs' 10%bv = Z_to_bv 64 (cmp_loop fuel (BN ca ea) (BN cb eb) i)
    /\ getr regs' 8%bv = Z_to_bv 64 s0v /\ getr regs' 2%bv = Z_to_bv 64 (sp' + 16).
Proof.
  induction fuel as [|fuel IH]; intros i regs m oa ob ea eb sp' s0v ca cb ret la lb R28 R29 R12 R11 R5 R6 R7 R13 R14 R15 R16 R17 R10 R1 Hret R2
    CS0 Hsp1 Hsp2 Ha Hb Hoka Hokb Hla Hlb Hea Heb Hoa1 Hoa2 Hob1 Hob2 Hll Hfuel Hi.
  all: subst la lb.
  all: pose proof (cellN_range _ _ _ _ _ CS0) as Hs0r; cbn [Z.of_nat Z.mul Pos.mul] in Hs0r; zwidth.
  all: pose proof (u64_range ret) as Hretr.
  - (* [comment removed for export] *)
    cmp_run [true] [KS] regs m rom i oa ob ea eb ca cb ret sp' s0v 0 0.
    zx_use ZXB ltac:(zx_pins) ltac:(pose proof (zlen_nonneg ca); pose proof (zlen_nonneg cb); zx_lia)
      ltac:(kc1 CS0; exact I) ltac:(exact I) ltac:(cbn in Hfuel; lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (2%bv : reg) as A2.
    eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    rewrite A10. cbn [cmp_loop]. split; [reflexivity|]. split; [exact A8 | exact A2].
  - cbn [cmp_loop BnModel.ex]. cbn in Hfuel.
    replace (i <? Z.min ea eb) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold bigit_or_zero, used. cbn [cells BnModel.ex].
    replace (zlen ca + ea <=? i) with false by (symmetry; apply Z.leb_gt; lia).
    replace (zlen cb + eb <=? i) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    assert (CA : ea <= i -> exists bs, rdn SEGS_U m (Z_to_bv 64 (oa + 4 * (i + 1 - ea))) 4 = Some bs /\ bytes_le_to_Z bs = zget ca (i - ea)).
    { intros Hle. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (i - ea))); [exact Ha | unfold zlen in *; lia | lia | unfold zget; reflexivity]. }
    assert (CB : eb <= i -> exists bs, rdn SEGS_U m (Z_to_bv 64 (ob + (4 * ea - 4 * eb) + 4 * (i + 1 - ea))) 4 = Some bs /\ bytes_le_to_Z bs = zget cb (i - eb)).
    { intros Hle. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (i - eb))); [exact Hb | unfold zlen in *; lia | lia | unfold zget; reflexivity]. }
    assert (XA : ea <= i -> 0 <= zget ca (i - ea) < B).
    { intros Hle. unfold zget. apply (proj1 (Forall_nth _ _) Hoka). unfold zlen in *; lia. }
    assert (XB : eb <= i -> 0 <= zget cb (i - eb) < B).
    { intros Hle. unfold zget. apply (proj1 (Forall_nth _ _) Hokb). unfold zlen in *; lia. }
    pose proof (zlen_nonneg ca) as Hza. pose proof (zlen_nonneg cb) as Hzb.
    set (xa := if i <? ea then 0 else zget ca (i - ea)). set (xb := if i <? eb then 0 else zget cb (i - eb)).
    assert (Hxa : 0 <= xa < B) by (unfold xa; destruct (Z.ltb_spec i ea); [unfold B; lia | apply XA; lia]).
    assert (Hxb : 0 <= xb < B) by (unfold xb; destruct (Z.ltb_spec i eb); [unfold B; lia | apply XB; lia]).
    destruct (Z.ltb_spec xa xb) as [Hlt|Hge]; [|destruct (Z.ltb_spec xb xa) as [Hgt|Hle]];
      destruct (Z.ltb_spec i ea) as [Ea|Ea]; destruct (Z.ltb_spec i eb) as [Eb|Eb]; unfold xa, xb in *; try (exfalso; lia).
    (* [comment removed for export] *)
    + cmp_run [false; true; false; false; false; true] [KB; KS] regs m rom i oa ob ea eb ca cb ret sp' s0v 0 (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CB ltac:(lia)); kc1 CS0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (2%bv : reg) as A2.
      eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| split; [exact A10|split; [exact A8|exact A2]]].
    + cmp_run [false; false; false; false; false; false; false; true] [KA; KB; KS] regs m rom i oa ob ea eb ca cb ret sp' s0v (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kc1 CS0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (2%bv : reg) as A2.
      eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| split; [exact A10|split; [exact A8|exact A2]]].
    (* [comment removed for export] *)
    + cmp_run [false; false; false; false; true; false] [KA; KS] regs m rom i oa ob ea eb ca cb ret sp' s0v (zget ca (i - ea)) 0.
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); kc1 CS0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (2%bv : reg) as A2.
      eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| split; [exact A10|split; [exact A8|exact A2]]].
    + cmp_run [false; false; false; false; false; false; false; false; false] [KA; KB; KS] regs m rom i oa ob ea eb ca cb ret sp' s0v (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kc1 CS0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (2%bv : reg) as A2.
      eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| split; [exact A10|split; [exact A8|exact A2]]].
    (* [comment removed for export] *)
    + cmp_run [false; true; false; false; false; false; true] [KB; KS] regs m rom i oa ob ea eb ca cb ret sp' s0v 0 (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CB ltac:(lia)); kc1 CS0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      zx_reg ZR (28%bv : reg) as A28. zx_reg ZR (29%bv : reg) as A29.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      destruct (IH (i - 1) regs0 m oa ob ea eb sp' s0v ca cb ret) as (regs2 & M2 & K2 & A2 & B8 & B2);
        [ rewrite A28; f_equal; lia | rewrite A29; f_equal; lia | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR
        | exact R1' | exact Hret | zx_regv ZR | exact CS0 | lia | lia | exact Ha | exact Hb | exact Hoka | exact Hokb | lia .. | ].
      exists regs2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split; [exact A2|split; [exact B8|exact B2]].
    + cmp_run [false; false; false; false; true; true] [KA; KS] regs m rom i oa ob ea eb ca cb ret sp' s0v (zget ca (i - ea)) 0.
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); kc1 CS0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      zx_reg ZR (28%bv : reg) as A28. zx_reg ZR (29%bv : reg) as A29.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      destruct (IH (i - 1) regs0 m oa ob ea eb sp' s0v ca cb ret) as (regs2 & M2 & K2 & A2 & B8 & B2);
        [ rewrite A28; f_equal; lia | rewrite A29; f_equal; lia | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR
        | exact R1' | exact Hret | zx_regv ZR | exact CS0 | lia | lia | exact Ha | exact Hb | exact Hoka | exact Hokb | lia .. | ].
      exists regs2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split; [exact A2|split; [exact B8|exact B2]].
    + cmp_run [false; false; false; false; false; false; false; false; true] [KA; KB; KS] regs m rom i oa ob ea eb ca cb ret sp' s0v (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kc1 CS0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      zx_reg ZR (28%bv : reg) as A28. zx_reg ZR (29%bv : reg) as A29.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      destruct (IH (i - 1) regs0 m oa ob ea eb sp' s0v ca cb ret) as (regs2 & M2 & K2 & A2 & B8 & B2);
        [ rewrite A28; f_equal; lia | rewrite A29; f_equal; lia | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR
        | exact R1' | exact Hret | zx_regv ZR | exact CS0 | lia | lia | exact Ha | exact Hb | exact Hoka | exact Hokb | lia .. | ].
      exists regs2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split; [exact A2|split; [exact B8|exact B2]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CS8 : list Z := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma keeps_CS_of8 : forall regs regs', keeps CS8 regs regs' ->
  getr regs' 2%bv = getr regs 2%bv -> getr regs' 8%bv = getr regs 8%bv -> keeps CS regs regs'.
Proof.
  intros regs regs' K H2 H8 r Hr. cbn in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|Hr]]]]; [exact H2|apply K; cbn; tauto|apply K; cbn; tauto|exact H8|]. apply K. cbn. tauto.
Qed.

(* [comment removed for export] *)
Abbreviation cmpE_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (1%bv : reg, ZV 38); (2%bv : reg, ZV 39); (8%bv : reg, ZV 40)].
Abbreviation cmpE_uvi := [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 128); Some (0, 2 ^ 15 - 1); Some (0, 128); Some (0, 2 ^ 15 - 1);
                          Some (0, 2 ^ 64 - 1); Some (16, 2 ^ 62); Some (0, 2 ^ 64 - 1)].
Abbreviation cmpE_kn := [KC (ZV 32) 0 2 (ZV 34); KC (ZV 32) 2 2 (ZV 35); KC (ZV 33) 0 2 (ZV 36); KC (ZV 33) 2 2 (ZV 37)].

Ltac cmpE_run dirs stops regs m rom oa ob ca cb ea eb ret sp :=
  zx_run SEGS_U constr:(CTX (vi_regs ++ cmpE_uvi) cmpE_kn [KW (ZV 39) (-16) 0]) 40%nat stops constr:(SCR dirs (@nil zx)) constr:(cmpE_pins)
         constr:([oa; ob; zlen ca; ea; zlen cb; eb; bv_unsigned ret; sp; bv_unsigned (getr regs 8%bv)]) constr:(cmpE_uvi) regs m rom 0x367d8.

#[using="Type"] Theorem cmp_U : forall regs m (oa ob sp : Z) (ret : word) (A B : bn),
  getr regs 10%bv = Z_to_bv 64 oa -> getr regs 11%bv = Z_to_bv 64 ob -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_U m oa A -> bn_at SEGS_U m ob B -> ok (cells A) -> ok (cells B) ->
  0 <= oa -> oa + 516 <= 2 ^ 62 -> 0 <= ob -> ob + 516 <= 2 ^ 62 ->
  16 <= sp -> sp <= 2 ^ 62 -> (oa + 516 <= sp - 16 \/ sp <= oa) -> (ob + 516 <= sp - 16 \/ sp <= ob) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x367d8) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (compare A B)
    /\ unch m m' [(sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m oa ob sp ret A B R10 R11 R2 R1 Hret HA HB Hoka Hokb Hoa1 Hoa2 Hob1 Hob2 Hsp1 Hsp2 Hda Hdb Hsts.
  destruct A as [ca ea]. destruct B as [cb eb]. cbn [cells] in Hoka, Hokb.
  destruct HA as (Au & Ae & Aarr & Aer & Alen). destruct HB as (Bu & Be & Barr & Ber & Blen). cbn [cells BnModel.ex] in *.
  pose proof (zlen_nonneg ca) as Za. pose proof (zlen_nonneg cb) as Zb.
  pose proof (u64_range ret) as Hretr. pose proof (u64_range (getr regs 8%bv)) as Hs0r.
  unfold compare, used. cbn [cells BnModel.ex].
  destruct (Z.ltb_spec (zlen ca + ea) (zlen cb + eb)) as [L1|L1].
  { (* [comment removed for export] *)
    cmpE_run [true] (@nil Z) regs m rom oa ob ca cb ea eb ret sp.
    zx_use ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia) ltac:(kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I) ltac:(kw1 Hsts; exact I) ltac:(zx_lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (10%bv : reg) as A10.
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| split; [exact A10|split; [unchx|growsx]]]. }
  destruct (Z.ltb_spec (zlen cb + eb) (zlen ca + ea)) as [L2|L2].
  { (* [comment removed for export] *)
    cmpE_run [false; true] (@nil Z) regs m rom oa ob ca cb ea eb ret sp.
    zx_use ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia) ltac:(kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I) ltac:(kw1 Hsts; exact I) ltac:(zx_lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (10%bv : reg) as A10.
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| split; [exact A10|split; [unchx|growsx]]]. }
  (* [comment removed for export] *)
  set (m1 := wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (getr regs 8%bv))))).
  assert (CS1 : cellN SEGS_U m1 (sp - 16 + 8) 8 (bv_unsigned (getr regs 8%bv))).
  { eapply cellN_eqa; [|reflexivity ..]. replace (sp - 16 + 8) with (sp + -8) by lia. unfold m1. cellx. }
  assert (Aarr1 : arr32 SEGS_U m1 (oa + 4) ca) by (unfold m1; apply arr32_store_other; zwidth; unfold zlen in *; try lia; exact Aarr).
  assert (Barr1 : arr32 SEGS_U m1 (ob + 4) cb) by (unfold m1; apply arr32_store_other; zwidth; unfold zlen in *; try lia; exact Barr).
  assert (LOOP : forall regs1 (dmin : bool),
    keeps CS8 regs regs1 -> getr regs1 2%bv = Z_to_bv 64 (sp - 16) ->
    getr regs1 28%bv = Z_to_bv 64 (zlen ca + ea) -> getr regs1 29%bv = Z_to_bv 64 (4 * zlen ca) ->
    getr regs1 12%bv = Z_to_bv 64 oa -> getr regs1 11%bv = Z_to_bv 64 (ob + (4 * ea - 4 * eb)) ->
    getr regs1 5%bv = Z_to_bv 64 (18446744073709551611 - oa) -> getr regs1 6%bv = Z_to_bv 64 (18446744073709551611 - ob) ->
    getr regs1 7%bv = Z_to_bv 64 (4 * ea - 4 * eb + -4) ->
    getr regs1 13%bv = Z_to_bv 64 ea -> getr regs1 14%bv = Z_to_bv 64 eb -> getr regs1 15%bv = Z_to_bv 64 (zlen ca + ea) ->
    getr regs1 16%bv = Z_to_bv 64 (zlen cb + eb) -> getr regs1 17%bv = Z_to_bv 64 (if dmin then eb else ea) ->
    (if dmin then eb < ea else ea <= eb) ->
    getr regs1 10%bv = Z_to_bv 64 (-1) -> getr regs1 1%bv = ret ->
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x367d8) m rom) (mkst regs1 (Z_to_bv 64 0x3685c) m1 rom) ->
    exists regs' m',
      msteps SEGS_U (mkst regs (Z_to_bv 64 0x367d8) m rom) (mkst regs' ret m' rom)
      /\ keeps CS regs regs'
      /\ getr regs' 10%bv = Z_to_bv 64 (cmp_loop (Z.to_nat (zlen ca + ea - Z.min ea eb)) {| cells := ca; ex := ea |} {| cells := cb; ex := eb |} (zlen ca + ea - 1))
      /\ unch m m' [(sp - 16, sp)] /\ mem_grows m m').
  { intros regs1 dmin K1 S1 B28 B29 B12 B11 B5 B6 B7 B13 B14 B15 B16 B17 Hd B10 B1 M1.
    destruct (cmp_loop_U (Z.to_nat (zlen ca + ea - Z.min ea eb)) (zlen ca + ea - 1) regs1 m1 oa ob ea eb (sp - 16) (bv_unsigned (getr regs 8%bv)) ca cb ret)
      as (regs2 & M2 & K2 & A2 & C8 & C2);
      [ rewrite B28; f_equal; lia | rewrite B29; f_equal; lia | exact B12 | exact B11 | exact B5 | exact B6 | exact B7 | exact B13 | exact B14 | exact B15 | exact B16
      | rewrite B17; f_equal; destruct dmin; lia | exact B10 | exact B1 | exact Hret | exact S1 | exact CS1 | lia | lia
      | exact Aarr1 | exact Barr1 | exact Hoka | exact Hokb | lia .. | ].
    exists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    split; [|split; [exact A2|split; [unfold m1; unchx|unfold m1; growsx]]].
    apply keeps_CS_of8; [eapply keeps_trans; [exact K1 | eapply keeps_sub_dec; [exact K2 | vm_compute; reflexivity]]| |].
    - rewrite C2, R2. f_equal. lia.
    - rewrite C8. apply Z_to_bv_bv_unsigned. }
  destruct (Z.lt_ge_cases eb ea) as [D|D].
  - cmpE_run [false; false; true] [0x3685c] regs m rom oa ob ca cb ea eb ret sp.
    zx_use ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia) ltac:(kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I) ltac:(kw1 Hsts; exact I) ltac:(zx_lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    apply (LOOP regs0 true); try assumption; try (zx_regv ZR).
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
  - cmpE_run [false; false; false] [0x3685c] regs m rom oa ob ca cb ea eb ret sp.
    zx_use ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia) ltac:(kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I) ltac:(kw1 Hsts; exact I) ltac:(zx_lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    apply (LOOP regs0 false); try assumption; try (zx_regv ZR).
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
Qed.
End S.
