(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Abbreviation cmpL_pins :=
  [(28%bv : reg, ZAdd (ZV 32) (ZL 1)); (12%bv : reg, ZAdd (ZV 33) (ZV 43)); (6%bv : reg, ZAdd (ZV 33) (ZV 43));
   (11%bv : reg, ZAdd (ZV 34) (ZV 44)); (7%bv : reg, ZAdd (ZV 34) (ZV 44));
   (14%bv : reg, ZV 35); (15%bv : reg, ZV 36); (16%bv : reg, ZV 37); (17%bv : reg, ZV 37); (5%bv : reg, ZV 38);
   (10%bv : reg, ZL 18446744073709551615); (2%bv : reg, ZV 42); (13%bv : reg, ZL SHA)].
Abbreviation cmpL_uvi :=
  [Some (-1, 2 ^ 16); Some (IMG, HIE - 516); Some (IMG, HIE - 516); Some (0, 2 ^ 15 - 1); Some (0, 2 ^ 15 - 1);
   Some (0, 2 ^ 16); Some (0, 2 ^ 15); Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 64 - 1);
   Some (IMG, HIE); Some (- 2 ^ 18, 2 ^ 19); Some (- 2 ^ 18, 2 ^ 19)].
Abbreviation KA := (KC (ZAdd (ZV 33) (ZV 43)) 0 4 (ZV 39)).
Abbreviation KB := (KC (ZAdd (ZV 34) (ZV 44)) 0 4 (ZV 40)).
Abbreviation KS := (KC (ZV 42) 8 8 (ZV 41)).
Abbreviation KHA := (KC (ZDivP (ZAdd (ZV 33) (ZV 43)) 3) SHA 1 (ZL 0)).
Abbreviation KHB := (KC (ZDivP (ZAdd (ZV 34) (ZV 44)) 3) SHA 1 (ZL 0)).
Definition cmpL_keep : list Z := [3; 4; 5; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Ltac cmp_run dirs kn regs m rom i oa ob ea eb ca cb rav sp' xa xb :=
  zx_run SEGS_A constr:(CTX (vi_regs ++ cmpL_uvi) kn (@nil kwin)) 40%nat [0x0ab370] constr:(SCR dirs (@nil zx)) constr:(cmpL_pins)
         constr:([i; oa; ob; ea; eb; zlen ca + ea; Z.min ea eb; xa; xb; rav; sp'; 4 * (i + 1 - ea); 4 * (i + 1 - eb)])
         constr:(cmpL_uvi) regs m rom 0x0ab370.

(* [comment removed for export] *)
#[using="Type"] Lemma m1_word : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1).
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Ltac cmp_fin regs0 ret ZM ZR ZE Hrav Hret :=
      let R1' := fresh "R1'" in let HH := fresh "HH" in
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH; exact Hrav);
      let A10 := fresh "A10" in let A2 := fresh "A2" in
      zx_reg ZR (10%bv : reg) as A10; zx_reg ZR (2%bv : reg) as A2;
      eexists regs0; split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|];
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity
            | split; [rewrite A10; first [reflexivity | apply m1_word] | exact A2]].
Ltac cmp_next IH ZM ZR ZE Hrav Hret CS0 Ha Hb Hoka Hokb OSA OSB i regs0 m oa ob ea eb sp' rav ca cb ret :=
      let A28 := fresh "A28" in let A12 := fresh "A12" in let A11 := fresh "A11" in
      zx_reg ZR (28%bv : reg) as A28; zx_reg ZR (12%bv : reg) as A12; zx_reg ZR (11%bv : reg) as A11;
      destruct (IH (i - 1) regs0 m oa ob ea eb sp' rav ca cb ret) as (regs2 & M2 & K2 & B10 & B2);
        [ rewrite A28; f_equal; lia | rewrite A12; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
        | rewrite A11; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
        | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR
        | exact CS0 | exact Hrav | exact Hret | lia | lia | exact Ha | exact Hb | exact Hoka | exact Hokb
        | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact OSA | exact OSB | lia | lia | lia | ];
      exists regs2; split; [eapply msteps_trans; [exact ZM | exact M2]|];
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|];
      split; [exact B10 | exact B2].

#[using="Type"] Lemma cmp_loop_A : forall fuel i regs m (oa ob ea eb sp' rav : Z) (ca cb : list Z) (ret : word),
  let la := zlen ca + ea in let lb := zlen cb + eb in
  getr regs 28%bv = Z_to_bv 64 (i + 1) ->
  getr regs 12%bv = Z_to_bv 64 (oa + 4 * (i + 1 - ea)) -> getr regs 6%bv = Z_to_bv 64 (oa + 4 * (i + 1 - ea)) ->
  getr regs 11%bv = Z_to_bv 64 (ob + 4 * (i + 1 - eb)) -> getr regs 7%bv = Z_to_bv 64 (ob + 4 * (i + 1 - eb)) ->
  getr regs 14%bv = Z_to_bv 64 ea -> getr regs 15%bv = Z_to_bv 64 eb -> getr regs 16%bv = Z_to_bv 64 la ->
  getr regs 17%bv = Z_to_bv 64 lb -> getr regs 5%bv = Z_to_bv 64 (Z.min ea eb) -> getr regs 10%bv = Z_to_bv 64 18446744073709551615 ->
  getr regs 2%bv = Z_to_bv 64 sp' -> getr regs 13%bv = Z_to_bv 64 SHA ->
  cellN SEGS_A m (sp' + 8) 8 rav -> Z_to_bv 64 rav = ret -> ret_ok ret -> KHI <= sp' -> sp' + 16 <= HIE ->
  arr32 SEGS_A m (oa + 4) ca -> arr32 SEGS_A m (ob + 4) cb -> ok ca -> ok cb ->
  zlen ca <= 126 -> zlen cb <= 126 -> 0 <= ea < 2 ^ 15 -> 0 <= eb < 2 ^ 15 ->
  APP oa 516 -> oa + 516 <= HIE -> APP ob 516 -> ob + 516 <= HIE -> oa mod 8 = 0 -> ob mod 8 = 0 ->
  objsh m oa -> objsh m ob ->
  la = lb -> Z.of_nat fuel = i + 1 - Z.min ea eb -> i <= la - 1 ->
  exists regs',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0ab370) m rom) (mkst regs' ret m rom)
    /\ keeps cmpL_keep regs regs'
    /\ getr regs' 10%bv = Z_to_bv 64 (cmp_loop fuel (BN ca ea) (BN cb eb) i)
    /\ getr regs' 2%bv = Z_to_bv 64 (sp' + 16).
Proof.
  induction fuel as [|fuel IH]; intros i regs m oa ob ea eb sp' rav ca cb ret la lb R28 R12 R6 R11 R7 R14 R15 R16 R17 R5 R10 R2 R13
    CS0 Hrav Hret Hsp1 Hsp2 Ha Hb Hoka Hokb Hla Hlb Hea Heb Hoa1 Hoa2 Hob1 Hob2 Hoa8 Hob8 OSA OSB Hll Hfuel Hi.
  all: subst la lb.
  all: pose proof (cellN_range _ _ _ _ _ CS0) as Hs0r; cbn [Z.of_nat Z.mul Pos.mul] in Hs0r; zwidth.
  all: pose proof (zlen_nonneg ca) as Hza; pose proof (zlen_nonneg cb) as Hzb.
  - (* [comment removed for export] *)
    cmp_run [true] [KS] regs m rom i oa ob ea eb ca cb rav sp' 0 0.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 CS0; exact I) ltac:(exact I) ltac:(cbn in Hfuel; lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; exact Hrav).
    zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (2%bv : reg) as A2.
    eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    rewrite A10. cbn [cmp_loop]. split; [reflexivity|]. exact A2.
  - cbn [cmp_loop BnModel.ex]. cbn in Hfuel.
    replace (i <? Z.min ea eb) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold bigit_or_zero, used. cbn [cells BnModel.ex].
    replace (zlen ca + ea <=? i) with false by (symmetry; apply Z.leb_gt; lia).
    replace (zlen cb + eb <=? i) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    assert (CA : ea <= i -> exists bs, rdn SEGS_A m (Z_to_bv 64 (oa + 4 * (i + 1 - ea))) 4 = Some bs /\ bytes_le_to_Z bs = zget ca (i - ea)).
    { intros Hle. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (i - ea))); [exact Ha | unfold zlen in *; lia | lia | unfold zget; reflexivity]. }
    assert (CB : eb <= i -> exists bs, rdn SEGS_A m (Z_to_bv 64 (ob + 4 * (i + 1 - eb))) 4 = Some bs /\ bytes_le_to_Z bs = zget cb (i - eb)).
    { intros Hle. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (i - eb))); [exact Hb | unfold zlen in *; lia | lia | unfold zget; reflexivity]. }
    assert (XA : ea <= i -> 0 <= zget ca (i - ea) < B).
    { intros Hle. unfold zget. apply (proj1 (Forall_nth _ _) Hoka). unfold zlen in *; lia. }
    assert (XB : eb <= i -> 0 <= zget cb (i - eb) < B).
    { intros Hle. unfold zget. apply (proj1 (Forall_nth _ _) Hokb). unfold zlen in *; lia. }
    set (xa := if i <? ea then 0 else zget ca (i - ea)). set (xb := if i <? eb then 0 else zget cb (i - eb)).
    assert (Hxa : 0 <= xa < B) by (unfold xa; destruct (Z.ltb_spec i ea); [unfold B; lia | apply XA; lia]).
    assert (Hxb : 0 <= xb < B) by (unfold xb; destruct (Z.ltb_spec i eb); [unfold B; lia | apply XB; lia]).
    destruct (Z.ltb_spec xa xb) as [Hlt|Hge]; [|destruct (Z.ltb_spec xb xa) as [Hgt|Hle]];
      destruct (Z.ltb_spec i ea) as [Ea|Ea]; destruct (Z.ltb_spec i eb) as [Eb|Eb]; unfold xa, xb in *; try (exfalso; lia).
    (* [comment removed for export] *)
    + cmp_run [false; true; false; false; true] [KB; KS; KHB] regs m rom i oa ob ea eb ca cb rav sp' 0 (zget cb (i - eb)).
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CB ltac:(lia)); kc1 CS0; kcsh OSB ((4 * (i + 1 - eb)) / 8); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_fin regs0 ret ZM ZR ZE Hrav Hret.
    + cmp_run [false; false; false; false; false; true] [KA; KB; KS; KHA; KHB] regs m rom i oa ob ea eb ca cb rav sp' (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kc1 CS0; kcsh OSA ((4 * (i + 1 - ea)) / 8); kcsh OSB ((4 * (i + 1 - eb)) / 8); exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_fin regs0 ret ZM ZR ZE Hrav Hret.
    (* [comment removed for export] *)
    + cmp_run [false; false; false; true; false] [KA; KS; KHA] regs m rom i oa ob ea eb ca cb rav sp' (zget ca (i - ea)) 0.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kc1 CS0; kcsh OSA ((4 * (i + 1 - ea)) / 8); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_fin regs0 ret ZM ZR ZE Hrav Hret.
    + cmp_run [false; false; false; false; false; false; false] [KA; KB; KS; KHA; KHB] regs m rom i oa ob ea eb ca cb rav sp' (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kc1 CS0; kcsh OSA ((4 * (i + 1 - ea)) / 8); kcsh OSB ((4 * (i + 1 - eb)) / 8); exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_fin regs0 ret ZM ZR ZE Hrav Hret.
    (* [comment removed for export] *)
    + cmp_run [false; true; false; false; false; true] [KB; KS; KHB] regs m rom i oa ob ea eb ca cb rav sp' 0 (zget cb (i - eb)).
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CB ltac:(lia)); kc1 CS0; kcsh OSB ((4 * (i + 1 - eb)) / 8); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_next IH ZM ZR ZE Hrav Hret CS0 Ha Hb Hoka Hokb OSA OSB i regs0 m oa ob ea eb sp' rav ca cb ret.
    + cmp_run [false; false; false; true; true] [KA; KS; KHA] regs m rom i oa ob ea eb ca cb rav sp' (zget ca (i - ea)) 0.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kc1 CS0; kcsh OSA ((4 * (i + 1 - ea)) / 8); exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_next IH ZM ZR ZE Hrav Hret CS0 Ha Hb Hoka Hokb OSA OSB i regs0 m oa ob ea eb sp' rav ca cb ret.
    + cmp_run [false; false; false; false; false; false; true] [KA; KB; KS; KHA; KHB] regs m rom i oa ob ea eb ca cb rav sp' (zget ca (i - ea)) (zget cb (i - eb)).
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kc1 CS0; kcsh OSA ((4 * (i + 1 - ea)) / 8); kcsh OSB ((4 * (i + 1 - eb)) / 8); exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_next IH ZM ZR ZE Hrav Hret CS0 Ha Hb Hoka Hokb OSA OSB i regs0 m oa ob ea eb sp' rav ca cb ret.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Abbreviation cmpE_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (1%bv : reg, ZV 38); (2%bv : reg, ZV 39)].
Abbreviation cmpE_uvi := [Some (IMG, HIE - 516); Some (IMG, HIE - 516); Some (0, 126); Some (0, 2 ^ 15 - 1); Some (0, 126); Some (0, 2 ^ 15 - 1);
                          Some (0, 2 ^ 64 - 1); Some (KHI + 16, HIE)].
Abbreviation cmpE_kn := [KC (ZL 0) 0x129ea8 8 (ZL 0x132278); KC (ZL 0) 0x132278 8 (ZL SHA);
   KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 32) (ZL 2)) 3) SHA 1 (ZL 0);
   KC (ZDivP (ZV 33) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 33) (ZL 2)) 3) SHA 1 (ZL 0);
   KC (ZV 32) 0 2 (ZV 34); KC (ZV 32) 2 2 (ZV 35); KC (ZV 33) 0 2 (ZV 36); KC (ZV 33) 2 2 (ZV 37)].

Ltac cmpE_run dirs stops regs m rom oa ob ca cb ea eb ret sp :=
  zx_run SEGS_A constr:(CTX (vi_regs ++ cmpE_uvi) cmpE_kn [KW (ZV 39) (-16) 0]) 60%nat stops constr:(SCR dirs (@nil zx)) constr:(cmpE_pins)
         constr:([oa; ob; zlen ca; ea; zlen cb; eb; bv_unsigned ret; sp]) constr:(cmpE_uvi) regs m rom 0x0ab28c.

Ltac fin1 regs0 ret ZM ZR ZE R1 Hret :=
    let R1' := fresh "R1'" in let HH := fresh "HH" in
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH, <- R1; apply Z_to_bv_bv_unsigned);
    let A10 := fresh "A10" in zx_reg ZR (10%bv : reg) as A10;
    eexists regs0, _; split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|];
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity| split; [rewrite A10; first [reflexivity | apply m1_word] |split; [unchx|growsx]]].

#[using="Type"] Theorem cmp_A : forall regs m (oa ob sp : Z) (ret : word) (A B : bn),
  getr regs 10%bv = Z_to_bv 64 oa -> getr regs 11%bv = Z_to_bv 64 ob -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_A m oa A -> bn_at SEGS_A m ob B -> ok (cells A) -> ok (cells B) -> zlen (cells A) <= 126 -> zlen (cells B) <= 126 ->
  APP oa 516 -> oa + 516 <= HIE -> APP ob 516 -> ob + 516 <= HIE -> oa mod 8 = 0 -> ob mod 8 = 0 ->
  KHI + 16 <= sp -> sp <= HIE -> (oa + 516 <= sp - 16 \/ sp <= oa) -> (ob + 516 <= sp - 16 \/ sp <= ob) ->
  shcells m -> objsh m oa -> objsh m ob ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0ab28c) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (compare A B)
    /\ unch m m' [(sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m oa ob sp ret A B R10 R11 R2 R1 Hret HA HB Hoka Hokb HlA HlB Hoa1 Hoa2 Hob1 Hob2 Hoa8 Hob8 Hsp1 Hsp2 Hda Hdb [SC1 SC2] OSA OSB Hsts.
  destruct A as [ca ea]. destruct B as [cb eb]. cbn [cells] in Hoka, Hokb, HlA, HlB.
  destruct HA as (Au & Ae & Aarr & Aer & Alen). destruct HB as (Bu & Be & Barr & Ber & Blen). cbn [cells BnModel.ex] in *.
  pose proof (zlen_nonneg ca) as Za. pose proof (zlen_nonneg cb) as Zb.
  pose proof (u64_range ret) as Hretr.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  unfold compare, used. cbn [cells BnModel.ex].
  hide Hda; hide Hdb.
  destruct (Z.ltb_spec (zlen ca + ea) (zlen cb + eb)) as [L1|L1].
  { (* [comment removed for export] *)
    cmpE_run [true] (@nil Z) regs m rom oa ob ca cb ea eb ret sp.
    zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSA 0; kcsh OSA 0; kcsh OSB 0; kcsh OSB 0; kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I)
      ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_lia). zx_name regs0.
    fin1 regs0 ret ZM ZR ZE R1 Hret. }
  destruct (Z.ltb_spec (zlen cb + eb) (zlen ca + ea)) as [L2|L2].
  { (* [comment removed for export] *)
    cmpE_run [false; false] (@nil Z) regs m rom oa ob ca cb ea eb ret sp.
    zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSA 0; kcsh OSA 0; kcsh OSB 0; kcsh OSB 0; kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I)
      ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_lia). zx_name regs0.
    fin1 regs0 ret ZM ZR ZE R1 Hret. }
  (* [comment removed for export] *)
  set (m1 := wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned ret)))).
  assert (CS1 : cellN SEGS_A m1 (sp - 16 + 8) 8 (bv_unsigned ret)).
  { unfold m1. cellN_go. }
  unhide.
  assert (Aarr1 : arr32 SEGS_A m1 (oa + 4) ca) by (unfold m1; apply arr32_store_other; zwidth; unfold zlen in *; try lia; exact Aarr).
  assert (Barr1 : arr32 SEGS_A m1 (ob + 4) cb) by (unfold m1; apply arr32_store_other; zwidth; unfold zlen in *; try lia; exact Barr).
  assert (OSA1 : objsh m1 oa).
  { unfold m1. eapply (objsh_unch m _ [(sp - 16, sp)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSA]. }
  assert (OSB1 : objsh m1 ob).
  { unfold m1. eapply (objsh_unch m _ [(sp - 16, sp)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSB]. }
  assert (LOOP : forall regs1 (dmin : bool),
    keeps CS' regs regs1 -> getr regs1 2%bv = Z_to_bv 64 (sp - 16) ->
    getr regs1 28%bv = Z_to_bv 64 (zlen ca + ea) ->
    getr regs1 12%bv = Z_to_bv 64 (oa + 4 * zlen ca) -> getr regs1 6%bv = Z_to_bv 64 (oa + 4 * zlen ca) ->
    getr regs1 11%bv = Z_to_bv 64 (ob + 4 * (zlen ca + ea - eb)) -> getr regs1 7%bv = Z_to_bv 64 (ob + 4 * (zlen ca + ea - eb)) ->
    getr regs1 14%bv = Z_to_bv 64 ea -> getr regs1 15%bv = Z_to_bv 64 eb -> getr regs1 16%bv = Z_to_bv 64 (zlen ca + ea) ->
    getr regs1 17%bv = Z_to_bv 64 (zlen cb + eb) -> getr regs1 5%bv = Z_to_bv 64 (if dmin then eb else ea) ->
    (if dmin then eb < ea else ea <= eb) ->
    getr regs1 10%bv = Z_to_bv 64 18446744073709551615 -> getr regs1 13%bv = Z_to_bv 64 SHA ->
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0ab28c) m rom) (mkst regs1 (Z_to_bv 64 0x0ab370) m1 rom) ->
    exists regs' m',
      msteps SEGS_A (mkst regs (Z_to_bv 64 0x0ab28c) m rom) (mkst regs' ret m' rom)
      /\ keeps CS regs regs'
      /\ getr regs' 10%bv = Z_to_bv 64 (cmp_loop (Z.to_nat (zlen ca + ea - Z.min ea eb)) {| cells := ca; ex := ea |} {| cells := cb; ex := eb |} (zlen ca + ea - 1))
      /\ unch m m' [(sp - 16, sp)] /\ mem_grows m m').
  { intros regs1 dmin K1 S1 B28 B12 B6 B11 B7 B14 B15 B16 B17 B5 Hd B10 B13 M1.
    destruct (cmp_loop_A (Z.to_nat (zlen ca + ea - Z.min ea eb)) (zlen ca + ea - 1) regs1 m1 oa ob ea eb (sp - 16) (bv_unsigned ret) ca cb ret)
      as (regs2 & M2 & K2 & A2 & C2);
      [ rewrite B28; f_equal; lia | rewrite B12; f_equal; lia | rewrite B6; f_equal; lia | rewrite B11; f_equal; lia | rewrite B7; f_equal; lia
      | exact B14 | exact B15 | exact B16 | exact B17 | rewrite B5; f_equal; destruct dmin; lia | exact B10 | exact S1 | exact B13
      | exact CS1 | apply Z_to_bv_bv_unsigned | exact Hret | lia | lia
      | exact Aarr1 | exact Barr1 | exact Hoka | exact Hokb | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
      | exact OSA1 | exact OSB1 | lia | lia | lia | ].
    exists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    split; [|split; [exact A2|split; [unfold m1; unchx|unfold m1; growsx]]].
    apply keeps_CS_of; [eapply keeps_trans; [exact K1 | eapply keeps_sub_dec; [exact K2 | vm_compute; reflexivity]]|].
    rewrite C2, R2. f_equal. lia. }
  destruct (Z.lt_ge_cases eb ea) as [D|D].
  - cmpE_run [false; true; true] [0x0ab370] regs m rom oa ob ca cb ea eb ret sp.
    zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSA 0; kcsh OSA 0; kcsh OSB 0; kcsh OSB 0; kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I)
      ltac:(kw1 Hsts; exact I) ltac:(zx_lia). zx_name regs0.
    apply (LOOP regs0 true); try assumption; try (zx_regv ZR); try (etransitivity; [zx_regv ZR|]; f_equal; lia).
    { eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  - cmpE_run [false; true; false] [0x0ab370] regs m rom oa ob ca cb ea eb ret sp.
    zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSA 0; kcsh OSA 0; kcsh OSB 0; kcsh OSB 0; kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I)
      ltac:(kw1 Hsts; exact I) ltac:(zx_lia). zx_name regs0.
    apply (LOOP regs0 false); try assumption; try (zx_regv ZR); try (etransitivity; [zx_regv ZR|]; f_equal; lia).
    { eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
Qed.

End S.
