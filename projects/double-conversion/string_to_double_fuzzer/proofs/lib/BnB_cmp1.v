(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnB_lib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma lxor_m4 : forall e, 0 <= e -> 4 * e < M64 -> Z.lxor (4 * e) (M64 - 4) = M64 - 4 - 4 * e.
Proof.
  intros e He1 He2.
  assert (Hl : Z.land (Z.lxor (4 * e) (M64 - 4)) (4 * e) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 2) as [Lo|Hi2].
    - replace (Z.testbit (4 * e) i) with false; [destruct (Z.testbit (M64 - 4) i); reflexivity|].
      symmetry. replace (4 * e) with (Z.shiftl e 2) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; lia).
      apply Z.shiftl_spec_low. lia.
    - destruct (Z.lt_ge_cases i 64) as [Lt|Ge].
      + replace (Z.testbit (M64 - 4) i) with true.
        * destruct (Z.testbit (4 * e) i); reflexivity.
        * symmetry. change (M64 - 4) with (Z.shiftl (Z.ones 62) 2). rewrite Z.shiftl_spec_high by lia. rewrite Z.testbit_ones_nonneg by lia. apply (proj2 (Z.ltb_lt _ _)). lia.
      + replace (Z.testbit (4 * e) i) with false; [destruct (Z.testbit (M64 - 4) i); reflexivity|].
        symmetry. apply (Z_testbit_high 64); lia. }
  pose proof (Z.add_nocarry_lxor _ _ Hl) as Ha.
  rewrite Z.lxor_assoc, (Z.lxor_comm (M64 - 4) (4 * e)), <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Ha. lia.
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Abbreviation PA := (ZSub (ZSub (ZV 33) (ZMul (ZV 35) (ZL 4))) (ZV 43)).
Abbreviation PB := (ZSub (ZSub (ZV 34) (ZMul (ZV 36) (ZL 4))) (ZV 43)).
Abbreviation TA := (ZSub (ZSub (ZL 18446744073709551612) (ZMul (ZV 35) (ZL 4))) (ZV 43)).
Abbreviation TB := (ZSub (ZSub (ZL 18446744073709551612) (ZMul (ZV 36) (ZL 4))) (ZV 43)).
Abbreviation L4 := (ZMul (ZV 37) (ZL 4)).
Abbreviation cmpL_pins :=
  [(18%bv : reg, ZV 32); (13%bv : reg, ZV 38); (16%bv : reg, ZV 35); (17%bv : reg, ZV 36); (5%bv : reg, ZV 37); (6%bv : reg, ZV 37);
   (14%bv : reg, L4); (15%bv : reg, ZL SHA); (10%bv : reg, ZL 18446744073709551615);
   (7%bv : reg, ZSub (ZL 18446744073709551615) (ZAdd (ZV 33) (ZL 4))); (28%bv : reg, ZSub (ZL 18446744073709551615) (ZAdd (ZV 34) (ZL 4)));
   (12%bv : reg, PA); (9%bv : reg, PA); (29%bv : reg, TA); (8%bv : reg, PB); (30%bv : reg, PB); (31%bv : reg, TB); (2%bv : reg, ZV 42)].
Abbreviation big := (Some (0, 18446744073709551615)).
Abbreviation cmpL_uvi :=
  [Some (0, 2 ^ 16); Some (IMG, HIE - 516); Some (IMG, HIE - 516); Some (0, 2 ^ 15 - 1); Some (0, 2 ^ 15 - 1);
   Some (0, 2 ^ 16); Some (0, 2 ^ 15); Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 28 - 1); big;
   Some (IMG, HIE - 64); Some (0, 2 ^ 10); big; big; big; big; big; big].
Abbreviation KA := (KC (ZAdd PA L4) 0 4 (ZV 39)).
Abbreviation KB := (KC (ZAdd PB L4) 0 4 (ZV 40)).
Abbreviation KHA := (KC (ZDivP (ZAdd L4 PA) 3) SHA 1 (ZL 0)).
Abbreviation KHB := (KC (ZDivP (ZAdd L4 PB) 3) SHA 1 (ZL 0)).
Abbreviation KS := [KC (ZV 42) 56 8 (ZV 41); KC (ZV 42) 48 8 (ZV 44); KC (ZV 42) 40 8 (ZV 45); KC (ZV 42) 32 8 (ZV 46);
                    KC (ZV 42) 24 8 (ZV 47); KC (ZV 42) 16 8 (ZV 48); KC (ZV 42) 8 8 (ZV 49)].
Definition cmpL_keep : list Z := [3; 4; 22; 23; 24; 25; 26; 27].

Ltac cmp_run dirs kn regs m rom i oa ob ea eb L rav sp' xa xb v8 v9 v18 v19 v20 v21 :=
  zx_run SEGS_B constr:(CTX (vi_regs ++ cmpL_uvi) (kn ++ KS) (@nil kwin)) 60%nat [0x0ab7ec] constr:(SCR dirs (@nil zx)) constr:(cmpL_pins)
         constr:([i + 1; oa; ob; ea; eb; L; Z.min ea eb; xa; xb; rav; sp'; 4 * (L - i - 1); v8; v9; v18; v19; v20; v21])
         constr:(cmpL_uvi) regs m rom 0x0ab7ec.

(* [comment removed for export] *)
#[using="Type"] Lemma m1_word : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1).
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition SAVED (m : word -> option byte) (sp' rav v8 v9 v18 v19 v20 v21 : Z) : Prop :=
  cellN SEGS_B m (sp' + 56) 8 rav /\ cellN SEGS_B m (sp' + 48) 8 v8 /\ cellN SEGS_B m (sp' + 40) 8 v9 /\ cellN SEGS_B m (sp' + 32) 8 v18
  /\ cellN SEGS_B m (sp' + 24) 8 v19 /\ cellN SEGS_B m (sp' + 16) 8 v20 /\ cellN SEGS_B m (sp' + 8) 8 v21.
Definition RESTORED (regs : bvmap 5 word) (sp' v8 v9 v18 v19 v20 v21 : Z) : Prop :=
  getr regs 2%bv = Z_to_bv 64 (sp' + 64) /\ getr regs 8%bv = Z_to_bv 64 v8 /\ getr regs 9%bv = Z_to_bv 64 v9 /\ getr regs 18%bv = Z_to_bv 64 v18
  /\ getr regs 19%bv = Z_to_bv 64 v19 /\ getr regs 20%bv = Z_to_bv 64 v20 /\ getr regs 21%bv = Z_to_bv 64 v21.

(* [comment removed for export] *)
Ltac cmp_fin regs0 ret ZM ZR ZE Hrav Hret :=
      let R1' := fresh "R1'" in let HH := fresh "HH" in
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH; exact Hrav);
      let A10 := fresh "A10" in
      zx_reg ZR (10%bv : reg) as A10;
      eexists regs0; split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|];
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity
            | split; [rewrite A10; first [reflexivity | apply m1_word] | unfold RESTORED; repeat split; zx_regv ZR]].

Ltac cmp_next IH ZM ZR ZE SV Hrav Hret Ha Hb Hoka Hokb OSA OSB i regs0 m oa ob ea eb L sp' rav v8 v9 v18 v19 v20 v21 ca cb ret :=
  destruct (IH (i - 1) regs0 m oa ob ea eb L sp' rav v8 v9 v18 v19 v20 v21 ca cb ret) as (regs2 & M2 & K2 & B10 & RS);
    [ etransitivity; [zx_regv ZR|]; f_equal; lia
    | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR
    | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
    | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
    | zx_regv ZR
    | exact SV | exact Hrav | exact Hret | lia | lia | exact Ha | exact Hb | exact Hoka | exact Hokb
    | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact OSA | exact OSB | lia | lia | lia | lia | ];
  exists regs2; split; [eapply msteps_trans; [exact ZM | exact M2]|];
  split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|];
  split; [exact B10 | exact RS].

#[using="Type"] Lemma cmp_loop_B : forall fuel i regs m (oa ob ea eb L sp' rav v8 v9 v18 v19 v20 v21 : Z) (ca cb : list Z) (ret : word),
  getr regs 18%bv = Z_to_bv 64 (i + 1) -> getr regs 13%bv = Z_to_bv 64 (Z.min ea eb) ->
  getr regs 16%bv = Z_to_bv 64 ea -> getr regs 17%bv = Z_to_bv 64 eb -> getr regs 5%bv = Z_to_bv 64 L -> getr regs 6%bv = Z_to_bv 64 L ->
  getr regs 14%bv = Z_to_bv 64 (4 * L) -> getr regs 15%bv = Z_to_bv 64 SHA -> getr regs 10%bv = Z_to_bv 64 18446744073709551615 ->
  getr regs 7%bv = Z_to_bv 64 (18446744073709551611 - oa) -> getr regs 28%bv = Z_to_bv 64 (18446744073709551611 - ob) ->
  getr regs 12%bv = Z_to_bv 64 (oa - 4 * ea - 4 * (L - i - 1)) -> getr regs 9%bv = Z_to_bv 64 (oa - 4 * ea - 4 * (L - i - 1)) ->
  getr regs 29%bv = Z_to_bv 64 (18446744073709551612 - 4 * ea - 4 * (L - i - 1)) ->
  getr regs 8%bv = Z_to_bv 64 (ob - 4 * eb - 4 * (L - i - 1)) -> getr regs 30%bv = Z_to_bv 64 (ob - 4 * eb - 4 * (L - i - 1)) ->
  getr regs 31%bv = Z_to_bv 64 (18446744073709551612 - 4 * eb - 4 * (L - i - 1)) ->
  getr regs 2%bv = Z_to_bv 64 sp' ->
  SAVED m sp' rav v8 v9 v18 v19 v20 v21 -> Z_to_bv 64 rav = ret -> ret_ok ret -> KHI <= sp' -> sp' + 64 <= HIE ->
  arr32 SEGS_B m (oa + 4) ca -> arr32 SEGS_B m (ob + 4) cb -> ok ca -> ok cb ->
  zlen ca <= 126 -> zlen cb <= 126 -> 0 <= ea < 2 ^ 15 -> 0 <= eb < 2 ^ 15 ->
  APP oa 516 -> oa + 516 <= HIE -> APP ob 516 -> ob + 516 <= HIE -> oa mod 8 = 0 -> ob mod 8 = 0 ->
  objshB m oa -> objshB m ob ->
  L = zlen ca + ea -> L = zlen cb + eb -> Z.of_nat fuel = i + 1 - Z.min ea eb -> i <= L - 1 ->
  exists regs',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab7ec) m rom) (mkst regs' ret m rom)
    /\ keeps cmpL_keep regs regs'
    /\ getr regs' 10%bv = Z_to_bv 64 (cmp_loop fuel (BN ca ea) (BN cb eb) i)
    /\ RESTORED regs' sp' v8 v9 v18 v19 v20 v21.
Proof.
  induction fuel as [|fuel IH]; intros i regs m oa ob ea eb L sp' rav v8 v9 v18 v19 v20 v21 ca cb ret
    R18 R13 R16 R17 R5 R6 R14 R15 R10 R7 R28 R12 R9 R29 R8 R30 R31 R2
    SV Hrav Hret Hsp1 Hsp2 Ha Hb Hoka Hokb Hla Hlb Hea Heb Hoa1 Hoa2 Hob1 Hob2 Hoa8 Hob8 OSA OSB HLa HLb Hfuel Hi.
  all: pose proof SV as (C56 & C48 & C40 & C32 & C24 & C16 & C8).
  all: pose proof (cellN_range _ _ _ _ _ C56) as W56; pose proof (cellN_range _ _ _ _ _ C48) as W48; pose proof (cellN_range _ _ _ _ _ C40) as W40;
       pose proof (cellN_range _ _ _ _ _ C32) as W32; pose proof (cellN_range _ _ _ _ _ C24) as W24; pose proof (cellN_range _ _ _ _ _ C16) as W16;
       pose proof (cellN_range _ _ _ _ _ C8) as W8; cbn [Z.of_nat Z.mul Pos.mul] in W56, W48, W40, W32, W24, W16, W8; zwidth.
  all: pose proof (zlen_nonneg ca) as Hza; pose proof (zlen_nonneg cb) as Hzb.
  - (* [comment removed for export] *)
    cmp_run [true] (@nil kcell) regs m rom i oa ob ea eb L rav sp' 0 0 v8 v9 v18 v19 v20 v21.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 C56; kc1 C48; kc1 C40; kc1 C32; kc1 C24; kc1 C16; kc1 C8; exact I) ltac:(exact I) ltac:(cbn in Hfuel; lia). zx_name regs0.
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; exact Hrav).
    zx_reg ZR (10%bv : reg) as A10.
    eexists regs0. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    rewrite A10. cbn [cmp_loop]. split; [reflexivity|]. unfold RESTORED; repeat split; zx_regv ZR.
  - cbn [cmp_loop BnModel.ex]. cbn in Hfuel.
    replace (i <? Z.min ea eb) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold bigit_or_zero, used. cbn [cells BnModel.ex].
    replace (zlen ca + ea <=? i) with false by (symmetry; apply Z.leb_gt; lia).
    replace (zlen cb + eb <=? i) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    assert (CA : ea <= i -> exists bs, rdn SEGS_B m (Z_to_bv 64 (oa + 4 * (i + 1 - ea))) 4 = Some bs /\ bytes_le_to_Z bs = zget ca (i - ea)).
    { intros Hle. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (i - ea))); [exact Ha | unfold zlen in *; lia | lia | unfold zget; reflexivity]. }
    assert (CB : eb <= i -> exists bs, rdn SEGS_B m (Z_to_bv 64 (ob + 4 * (i + 1 - eb))) 4 = Some bs /\ bytes_le_to_Z bs = zget cb (i - eb)).
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
    + cmp_run [false; true; false; false; false; true] [KB; KHB] regs m rom i oa ob ea eb L rav sp' 0 (zget cb (i - eb)) v8 v9 v18 v19 v20 v21.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CB ltac:(lia)); kcsh OSB ((4 * (i + 1 - eb)) / 8); kc1 C56; kc1 C48; kc1 C40; kc1 C32; kc1 C24; kc1 C16; kc1 C8; exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_fin regs0 ret ZM ZR ZE Hrav Hret.
    + cmp_run [false; false; false; false; false; false; false; true] [KA; KB; KHA; KHB] regs m rom i oa ob ea eb L rav sp' (zget ca (i - ea)) (zget cb (i - eb)) v8 v9 v18 v19 v20 v21.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kcsh OSA ((4 * (i + 1 - ea)) / 8); kcsh OSB ((4 * (i + 1 - eb)) / 8);
              kc1 C56; kc1 C48; kc1 C40; kc1 C32; kc1 C24; kc1 C16; kc1 C8; exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_fin regs0 ret ZM ZR ZE Hrav Hret.
    (* [comment removed for export] *)
    + cmp_run [false; false; false; false; true; false; false] [KA; KHA] regs m rom i oa ob ea eb L rav sp' (zget ca (i - ea)) 0 v8 v9 v18 v19 v20 v21.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kcsh OSA ((4 * (i + 1 - ea)) / 8); kc1 C56; kc1 C48; kc1 C40; kc1 C32; kc1 C24; kc1 C16; kc1 C8; exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_fin regs0 ret ZM ZR ZE Hrav Hret.
    + cmp_run [false; false; false; false; false; false; false; false; false] [KA; KB; KHA; KHB] regs m rom i oa ob ea eb L rav sp' (zget ca (i - ea)) (zget cb (i - eb)) v8 v9 v18 v19 v20 v21.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kcsh OSA ((4 * (i + 1 - ea)) / 8); kcsh OSB ((4 * (i + 1 - eb)) / 8);
              kc1 C56; kc1 C48; kc1 C40; kc1 C32; kc1 C24; kc1 C16; kc1 C8; exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_fin regs0 ret ZM ZR ZE Hrav Hret.
    (* [comment removed for export] *)
    + cmp_run [false; true; false; false; false; false; true] [KB; KHB] regs m rom i oa ob ea eb L rav sp' 0 (zget cb (i - eb)) v8 v9 v18 v19 v20 v21.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CB ltac:(lia)); kcsh OSB ((4 * (i + 1 - eb)) / 8); kc1 C56; kc1 C48; kc1 C40; kc1 C32; kc1 C24; kc1 C16; kc1 C8; exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_next IH ZM ZR ZE SV Hrav Hret Ha Hb Hoka Hokb OSA OSB i regs0 m oa ob ea eb L sp' rav v8 v9 v18 v19 v20 v21 ca cb ret.
    + cmp_run [false; false; false; false; true; true] [KA; KHA] regs m rom i oa ob ea eb L rav sp' (zget ca (i - ea)) 0 v8 v9 v18 v19 v20 v21.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kcsh OSA ((4 * (i + 1 - ea)) / 8); kc1 C56; kc1 C48; kc1 C40; kc1 C32; kc1 C24; kc1 C16; kc1 C8; exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_next IH ZM ZR ZE SV Hrav Hret Ha Hb Hoka Hokb OSA OSB i regs0 m oa ob ea eb L sp' rav v8 v9 v18 v19 v20 v21 ca cb ret.
    + cmp_run [false; false; false; false; false; false; false; false; true] [KA; KB; KHA; KHB] regs m rom i oa ob ea eb L rav sp' (zget ca (i - ea)) (zget cb (i - eb)) v8 v9 v18 v19 v20 v21.
      zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
        ltac:(kc1 (CA ltac:(lia)); kc1 (CB ltac:(lia)); kcsh OSA ((4 * (i + 1 - ea)) / 8); kcsh OSB ((4 * (i + 1 - eb)) / 8);
              kc1 C56; kc1 C48; kc1 C40; kc1 C32; kc1 C24; kc1 C16; kc1 C8; exact I)
        ltac:(exact I) ltac:(zx_lia). zx_name regs0.
      cmp_next IH ZM ZR ZE SV Hrav Hret Ha Hb Hoka Hokb OSA OSB i regs0 m oa ob ea eb L sp' rav v8 v9 v18 v19 v20 v21 ca cb ret.
Qed.

End S.
