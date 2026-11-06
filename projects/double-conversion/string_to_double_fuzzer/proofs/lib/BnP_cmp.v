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
  [(5%bv : reg, ZAdd (ZV 32) (ZL 1)); (12%bv : reg, ZV 33); (11%bv : reg, ZV 34); (13%bv : reg, ZV 35);
   (14%bv : reg, ZV 36); (15%bv : reg, ZV 37); (16%bv : reg, ZV 38); (17%bv : reg, ZV 39); (10%bv : reg, ZL (-1)); (1%bv : reg, ZV 42)].
Abbreviation cmpL_uvi :=
  [Some (-1, 2 ^ 16); Some (-2 ^ 20, 2 ^ 62); Some (-2 ^ 20, 2 ^ 62); Some (0, 2 ^ 15 - 1); Some (0, 2 ^ 15 - 1);
   Some (0, 2 ^ 16); Some (0, 2 ^ 16); Some (0, 2 ^ 15); Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 28 - 1); @None (Z * Z)].
Definition cmpL_keep : list Z := [1; 2; 3; 4; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Ltac cmp_run dirs kn regs m rom i oa ob ea eb ca cb ret xa xb :=
  zx_run SEGS_P constr:(CTX (vi_regs ++ cmpL_uvi) kn (@nil kwin)) 30%nat [0x3618c] constr:(SCR dirs (@nil zx)) constr:(cmpL_pins)
         constr:([i; oa + 4 + 4 * (i - ea); ob + 4 + 4 * (i - eb); ea; eb; zlen ca + ea; zlen cb + eb; Z.min ea eb;
                  xa; xb; bv_unsigned ret])
         constr:(cmpL_uvi) regs m rom 0x3618c.

#[using="Type"] Lemma cmp_loop_P : forall fuel i regs m (oa ob ea eb : Z) (ca cb : list Z) (ret : word),
  let pa := oa + 4 + 4 * (i - ea) in let pb := ob + 4 + 4 * (i - eb) in
  let la := zlen ca + ea in let lb := zlen cb + eb in
  getr regs 5%bv = Z_to_bv 64 (i + 1) -> getr regs 12%bv = Z_to_bv 64 pa -> getr regs 11%bv = Z_to_bv 64 pb ->
  getr regs 13%bv = Z_to_bv 64 ea -> getr regs 14%bv = Z_to_bv 64 eb -> getr regs 15%bv = Z_to_bv 64 la ->
  getr regs 16%bv = Z_to_bv 64 lb -> getr regs 17%bv = Z_to_bv 64 (Z.min ea eb) -> getr regs 10%bv = Z_to_bv 64 (-1) ->
  getr regs 1%bv = ret -> ret_ok ret ->
  arr32 SEGS_P m (oa + 4) ca -> arr32 SEGS_P m (ob + 4) cb -> ok ca -> ok cb ->
  zlen ca <= 128 -> zlen cb <= 128 -> 0 <= ea < 2 ^ 15 -> 0 <= eb < 2 ^ 15 ->
  0 <= oa -> oa + 516 <= 2 ^ 62 -> 0 <= ob -> ob + 516 <= 2 ^ 62 ->
  la = lb -> Z.of_nat fuel = i + 1 - Z.min ea eb -> i <= la - 1 ->
  exists regs',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x3618c) m rom) (mkst regs' ret m rom)
    /\ keeps cmpL_keep regs regs'
    /\ getr regs' 10%bv = Z_to_bv 64 (cmp_loop fuel (BN ca ea) (BN cb eb) i).
Proof.
  induction fuel as [|fuel IH]; intros i regs m oa ob ea eb ca cb ret pa pb la lb R5 R12 R11 R13 R14 R15 R16 R17 R10 R1 Hret
    Ha Hb Hoka Hokb Hla Hlb Hea Heb Hoa1 Hoa2 Hob1 Hob2 Hll Hfuel Hi.
  all: subst pa pb la lb.
  - (* [comment removed for export] *)
    cmp_run [true] (@nil kcell) regs m rom i oa ob ea eb ca cb ret 0 0.
    zx_use ZXB ltac:(zx_pins) ltac:(pose proof (zlen_nonneg ca); pose proof (zlen_nonneg cb); zx_lia)
      ltac:(exact I) ltac:(exact I) ltac:(cbn in Hfuel; lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (10%bv : reg) as A10.
    eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    rewrite A10. cbn [cmp_loop]. reflexivity.
  - cbn [cmp_loop BnModel.ex]. cbn in Hfuel.
    replace (i <? Z.min ea eb) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold bigit_or_zero, used. cbn [cells BnModel.ex].
    replace (zlen ca + ea <=? i) with false by (symmetry; apply Z.leb_gt; lia).
    replace (zlen cb + eb <=? i) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    assert (CA : ea <= i -> exists bs, rdn SEGS_P m (Z_to_bv 64 (oa + 4 + 4 * (i - ea))) 4 = Some bs /\ bytes_le_to_Z bs = zget ca (i - ea)).
    { intros Hle. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (i - ea))); [exact Ha | unfold zlen in *; lia | lia | unfold zget; reflexivity]. }
    assert (CB : eb <= i -> exists bs, rdn SEGS_P m (Z_to_bv 64 (ob + 4 + 4 * (i - eb))) 4 = Some bs /\ bytes_le_to_Z bs = zget cb (i - eb)).
    { intros Hle. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (i - eb))); [exact Hb | unfold zlen in *; lia | lia | unfold zget; reflexivity]. }
    assert (XA : ea <= i -> 0 <= zget ca (i - ea) < B).
    { intros Hle. unfold zget. apply (proj1 (Forall_nth _ _) Hoka). unfold zlen in *; lia. }
    assert (XB : eb <= i -> 0 <= zget cb (i - eb) < B).
    { intros Hle. unfold zget. apply (proj1 (Forall_nth _ _) Hokb). unfold zlen in *; lia. }
    pose proof (zlen_nonneg ca) as Hza. pose proof (zlen_nonneg cb) as Hzb.
    set (xa := if i <? ea then 0 else zget ca (i - ea)). set (xb := if i <? eb then 0 else zget cb (i - eb)).
    assert (Hxa : 0 <= xa < B) by (unfold xa; destruct (Z.ltb_spec i ea); [unfold B; lia | apply XA; lia]).
    assert (Hxb : 0 <= xb < B) by (unfold xb; destruct (Z.ltb_spec i eb); [unfold B; lia | apply XB; lia]).
    (* [comment removed for export] *)
    assert (STEP : forall (dx dy : list bool) (kn : list kcell),
      (dx = (if i <? ea then [true] else [false; false])) -> (dy = (if i <? eb then [true] else [false; false])) ->
      kn = ((if i <? ea then [] else [KC (ZV 33) 0 4 (ZV 40)]) ++ (if i <? eb then [] else [KC (ZV 34) 0 4 (ZV 41)])) ->
      True).
    { intros; exact I. }
    clear STEP.
    destruct (Z.ltb_spec xa xb) as [Hlt|Hge]; [|destruct (Z.ltb_spec xb xa) as [Hgt|Hle]];
      destruct (Z.ltb_spec i ea) as [Ea|Ea]; destruct (Z.ltb_spec i eb) as [Eb|Eb]; unfold xa, xb in *; try (exfalso; lia).
    (* [comment removed for export] *)
    + cmp_run [false; true; false; false; true] [KC (ZV 34) 0 4 (ZV 41)] regs m rom i oa ob ea eb ca cb ret 0 (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CB ltac:(lia)); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (10%bv : reg) as A10.
      eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| exact A10].
    + cmp_run [false; false; false; false; false; true] [KC (ZV 33) 0 4 (ZV 40); KC (ZV 34) 0 4 (ZV 41)] regs m rom i oa ob ea eb ca cb ret (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (10%bv : reg) as A10.
      eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| exact A10].
    (* [comment removed for export] *)
    + cmp_run [false; false; false; true; false] [KC (ZV 33) 0 4 (ZV 40)] regs m rom i oa ob ea eb ca cb ret (zget ca (i - ea)) 0.
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (10%bv : reg) as A10.
      eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| exact A10].
    + cmp_run [false; false; false; false; false; false; false] [KC (ZV 33) 0 4 (ZV 40); KC (ZV 34) 0 4 (ZV 41)] regs m rom i oa ob ea eb ca cb ret (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (10%bv : reg) as A10.
      eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| exact A10].
    (* [comment removed for export] *)
    + cmp_run [false; true; false; false; false; true] [KC (ZV 34) 0 4 (ZV 41)] regs m rom i oa ob ea eb ca cb ret 0 (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CB ltac:(lia)); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (11%bv : reg) as A11.
      zx_reg ZR (13%bv : reg) as A13. zx_reg ZR (14%bv : reg) as A14. zx_reg ZR (15%bv : reg) as A15.
      zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (10%bv : reg) as A10.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      destruct (IH (i - 1) regs0 m oa ob ea eb ca cb ret) as (regs2 & M2 & K2 & A2);
        [ rewrite A5; f_equal; lia | rewrite A12; f_equal; lia | rewrite A11; f_equal; lia | exact A13 | exact A14 | exact A15 | exact A16 | exact A17
        | exact A10 | exact R1' | exact Hret | exact Ha | exact Hb | exact Hoka | exact Hokb | lia .. | ].
      exists regs2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      exact A2.
    + cmp_run [false; false; false; true; true] [KC (ZV 33) 0 4 (ZV 40)] regs m rom i oa ob ea eb ca cb ret (zget ca (i - ea)) 0.
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (11%bv : reg) as A11.
      zx_reg ZR (13%bv : reg) as A13. zx_reg ZR (14%bv : reg) as A14. zx_reg ZR (15%bv : reg) as A15.
      zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (10%bv : reg) as A10.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      destruct (IH (i - 1) regs0 m oa ob ea eb ca cb ret) as (regs2 & M2 & K2 & A2);
        [ rewrite A5; f_equal; lia | rewrite A12; f_equal; lia | rewrite A11; f_equal; lia | exact A13 | exact A14 | exact A15 | exact A16 | exact A17
        | exact A10 | exact R1' | exact Hret | exact Ha | exact Hb | exact Hoka | exact Hokb | lia .. | ].
      exists regs2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      exact A2.
    + cmp_run [false; false; false; false; false; false; true] [KC (ZV 33) 0 4 (ZV 40); KC (ZV 34) 0 4 (ZV 41)] regs m rom i oa ob ea eb ca cb ret (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (11%bv : reg) as A11.
      zx_reg ZR (13%bv : reg) as A13. zx_reg ZR (14%bv : reg) as A14. zx_reg ZR (15%bv : reg) as A15.
      zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (10%bv : reg) as A10.
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      destruct (IH (i - 1) regs0 m oa ob ea eb ca cb ret) as (regs2 & M2 & K2 & A2);
        [ rewrite A5; f_equal; lia | rewrite A12; f_equal; lia | rewrite A11; f_equal; lia | exact A13 | exact A14 | exact A15 | exact A16 | exact A17
        | exact A10 | exact R1' | exact Hret | exact Ha | exact Hb | exact Hoka | exact Hokb | lia .. | ].
      exists regs2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      exact A2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Abbreviation cmpE_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (1%bv : reg, ZV 38)].
Abbreviation cmpE_uvi := [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 128); Some (0, 2 ^ 15 - 1); Some (0, 128); Some (0, 2 ^ 15 - 1); @None (Z * Z)].
Abbreviation cmpE_kn := [KC (ZV 32) 0 2 (ZV 34); KC (ZV 32) 2 2 (ZV 35); KC (ZV 33) 0 2 (ZV 36); KC (ZV 33) 2 2 (ZV 37)].

Ltac cmpE_run dirs stops regs m rom oa ob ca cb ea eb ret :=
  zx_run SEGS_P constr:(CTX (vi_regs ++ cmpE_uvi) cmpE_kn (@nil kwin)) 40%nat stops constr:(SCR dirs (@nil zx)) constr:(cmpE_pins)
         constr:([oa; ob; zlen ca; ea; zlen cb; eb; bv_unsigned ret]) constr:(cmpE_uvi) regs m rom 0x36120.

#[using="Type"] Theorem cmp_P : forall regs m (oa ob : Z) (ret : word) (A B : bn),
  getr regs 10%bv = Z_to_bv 64 oa -> getr regs 11%bv = Z_to_bv 64 ob -> getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_P m oa A -> bn_at SEGS_P m ob B -> ok (cells A) -> ok (cells B) ->
  0 <= oa -> oa + 516 <= 2 ^ 62 -> 0 <= ob -> ob + 516 <= 2 ^ 62 ->
  exists regs',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x36120) m rom) (mkst regs' ret m rom)
    /\ keeps CS regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (compare A B).
Proof.
  intros regs m oa ob ret A B R10 R11 R1 Hret HA HB Hoka Hokb Hoa1 Hoa2 Hob1 Hob2.
  destruct A as [ca ea]. destruct B as [cb eb]. cbn [cells] in Hoka, Hokb.
  destruct HA as (Au & Ae & Aarr & Aer & Alen). destruct HB as (Bu & Be & Barr & Ber & Blen). cbn [cells BnModel.ex] in *.
  pose proof (zlen_nonneg ca) as Za. pose proof (zlen_nonneg cb) as Zb.
  unfold compare, used. cbn [cells BnModel.ex].
  destruct (Z.ltb_spec (zlen ca + ea) (zlen cb + eb)) as [L1|L1].
  { (* [comment removed for export] *)
    cmpE_run [true] (@nil Z) regs m rom oa ob ca cb ea eb ret.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (10%bv : reg) as A10.
    eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| exact A10]. }
  destruct (Z.ltb_spec (zlen cb + eb) (zlen ca + ea)) as [L2|L2].
  { (* [comment removed for export] *)
    cmpE_run [false; true] (@nil Z) regs m rom oa ob ca cb ea eb ret.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (10%bv : reg) as A10.
    eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| exact A10]. }
  (* [comment removed for export] *)
  assert (LOOP : forall regs1 (dmin : bool),
    keeps CS' regs regs1 -> getr regs1 2%bv = getr regs 2%bv ->
    getr regs1 5%bv = Z_to_bv 64 (zlen ca + ea) -> getr regs1 12%bv = Z_to_bv 64 (oa + 4 * zlen ca) ->
    getr regs1 11%bv = Z_to_bv 64 (ob - 4 * eb + 4 * (zlen ca + ea)) ->
    getr regs1 13%bv = Z_to_bv 64 ea -> getr regs1 14%bv = Z_to_bv 64 eb -> getr regs1 15%bv = Z_to_bv 64 (zlen ca + ea) ->
    getr regs1 16%bv = Z_to_bv 64 (zlen cb + eb) -> getr regs1 17%bv = Z_to_bv 64 (if dmin then eb else ea) ->
    (if dmin then eb < ea else ea <= eb) ->
    getr regs1 10%bv = Z_to_bv 64 (-1) -> getr regs1 1%bv = ret ->
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x36120) m rom) (mkst regs1 (Z_to_bv 64 0x3618c) m rom) ->
    exists regs',
      msteps SEGS_P (mkst regs (Z_to_bv 64 0x36120) m rom) (mkst regs' ret m rom)
      /\ keeps CS regs regs'
      /\ getr regs' 10%bv = Z_to_bv 64 (cmp_loop (Z.to_nat (zlen ca + ea - Z.min ea eb)) {| cells := ca; ex := ea |} {| cells := cb; ex := eb |} (zlen ca + ea - 1))).
  { intros regs1 dmin K1 S1 B5 B12 B11 B13 B14 B15 B16 B17 Hd B10 B1 M1.
    destruct (cmp_loop_P (Z.to_nat (zlen ca + ea - Z.min ea eb)) (zlen ca + ea - 1) regs1 m oa ob ea eb ca cb ret)
      as (regs2 & M2 & K2 & A2);
      [ rewrite B5; f_equal; lia | rewrite B12; f_equal; lia | rewrite B11; f_equal; lia | exact B13 | exact B14 | exact B15 | exact B16
      | rewrite B17; f_equal; destruct dmin; lia | exact B10 | exact B1 | exact Hret | exact Aarr | exact Barr | exact Hoka | exact Hokb
      | lia .. | ].
    exists regs2. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    split; [|exact A2].
    apply keeps_CS_of; [eapply keeps_trans; [exact K1 | eapply keeps_sub_dec; [exact K2 | vm_compute; reflexivity]]|].
    rewrite <- S1. symmetry. symmetry. exact (K2 2 ltac:(cbn; tauto)). }
  destruct (Z.lt_ge_cases eb ea) as [D|D].
  - cmpE_run [false; false; true] [0x3618c] regs m rom oa ob ca cb ea eb ret.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    apply (LOOP regs0 true); try assumption; try (zx_regv ZR).
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
  - cmpE_run [false; false; false] [0x3618c] regs m rom oa ob ca cb ea eb ret.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    apply (LOOP regs0 false); try assumption; try (zx_regv ZR).
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
Qed.
End S.
