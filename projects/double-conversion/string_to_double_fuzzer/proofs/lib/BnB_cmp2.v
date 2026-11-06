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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnB_lib BnB_cmp1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Abbreviation big := (Some (0, 18446744073709551615)).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma keeps_CS_asm : forall regs regs',
  keeps cmpL_keep regs regs' ->
  getr regs' 2%bv = getr regs 2%bv -> getr regs' 8%bv = getr regs 8%bv -> getr regs' 9%bv = getr regs 9%bv ->
  getr regs' 18%bv = getr regs 18%bv -> getr regs' 19%bv = getr regs 19%bv -> getr regs' 20%bv = getr regs 20%bv ->
  getr regs' 21%bv = getr regs 21%bv -> keeps CS regs regs'.
Proof.
  intros regs regs' K H2 H8 H9 H18 H19 H20 H21 r Hr. unfold CS in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
    first [exact H2 | exact H8 | exact H9 | exact H18 | exact H19 | exact H20 | exact H21 | apply K; in_list].
Qed.

(* [comment removed for export] *)
Abbreviation cmpE_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (1%bv : reg, ZV 38); (2%bv : reg, ZV 39)].
Abbreviation cmpE_uvi := [Some (IMG, HIE - 516); Some (IMG, HIE - 516); Some (0, 126); Some (0, 2 ^ 15 - 1); Some (0, 126); Some (0, 2 ^ 15 - 1);
                          big; Some (KHI + 64, HIE)].
Abbreviation cmpE_kn := [KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA);
   KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 32) (ZL 2)) 3) SHA 1 (ZL 0);
   KC (ZDivP (ZV 33) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 33) (ZL 2)) 3) SHA 1 (ZL 0);
   KC (ZV 32) 0 2 (ZV 34); KC (ZV 32) 2 2 (ZV 35); KC (ZV 33) 0 2 (ZV 36); KC (ZV 33) 2 2 (ZV 37)].

Ltac cmpE_run dirs stops regs m rom oa ob ca cb ea eb ret sp :=
  zx_run SEGS_B constr:(CTX (vi_regs ++ cmpE_uvi) cmpE_kn [KW (ZV 39) (-64) 0]) 80%nat stops constr:(SCR dirs (@nil zx)) constr:(cmpE_pins)
         constr:([oa; ob; zlen ca; ea; zlen cb; eb; bv_unsigned ret; sp]) constr:(cmpE_uvi) regs m rom 0x0ab6ec.

Ltac fin1 regs0 ret ZM ZR ZE R1 R2 Hret :=
    let R1' := fresh "R1'" in let HH := fresh "HH" in
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH, <- R1; apply Z_to_bv_bv_unsigned);
    let A10 := fresh "A10" in zx_reg ZR (10%bv : reg) as A10;
    eexists regs0, _; split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|];
    split; [| split; [rewrite A10; first [reflexivity | apply m1_word] |split; [unchx|growsx]]];
    apply keeps_CS_asm; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | rewrite R2; zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR].

(* [comment removed for export] *)
#[using="Type"] Lemma xor4_val : forall e, 0 <= e < 2 ^ 15 ->
  Z_to_bv 64 (Z.lxor ((e * 4) mod 18446744073709551616) 18446744073709551612) = Z_to_bv 64 (18446744073709551612 - 4 * e - 4 * 0).
Proof.
  intros e He. rewrite Z.mod_small by lia. replace (e * 4) with (4 * e) by lia.
  change 18446744073709551612 with (M64 - 4). rewrite lxor_m4 by lia. f_equal. lia.
Qed.

#[using="Type"] Theorem cmp_B : forall regs m (oa ob sp : Z) (ret : word) (A B : bn),
  getr regs 10%bv = Z_to_bv 64 oa -> getr regs 11%bv = Z_to_bv 64 ob -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_B m oa A -> bn_at SEGS_B m ob B -> ok (cells A) -> ok (cells B) -> zlen (cells A) <= 126 -> zlen (cells B) <= 126 ->
  APP oa 516 -> oa + 516 <= HIE -> APP ob 516 -> ob + 516 <= HIE -> oa mod 8 = 0 -> ob mod 8 = 0 ->
  KHI + 64 <= sp -> sp <= HIE -> (oa + 516 <= sp - 64 \/ sp <= oa) -> (ob + 516 <= sp - 64 \/ sp <= ob) ->
  shcellsB m -> objshB m oa -> objshB m ob ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 64)) 64 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab6ec) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (compare A B)
    /\ unch m m' [(sp - 64, sp)] /\ mem_grows m m'.
Proof.
  intros regs m oa ob sp ret A B R10 R11 R2 R1 Hret HA HB Hoka Hokb HlA HlB Hoa1 Hoa2 Hob1 Hob2 Hoa8 Hob8 Hsp1 Hsp2 Hda Hdb [SC1 SC2] OSA OSB Hsts.
  destruct A as [ca ea]. destruct B as [cb eb]. cbn [cells] in Hoka, Hokb, HlA, HlB.
  destruct HA as (Au & Ae & Aarr & Aer & Alen). destruct HB as (Bu & Be & Barr & Ber & Blen). cbn [cells BnModel.ex] in *.
  pose proof (zlen_nonneg ca) as Za. pose proof (zlen_nonneg cb) as Zb.
  pose proof (u64_range ret) as Hretr.
  pose proof (u64_range (getr regs 8%bv)) as W8. pose proof (u64_range (getr regs 9%bv)) as W9. pose proof (u64_range (getr regs 18%bv)) as W18.
  pose proof (u64_range (getr regs 19%bv)) as W19. pose proof (u64_range (getr regs 20%bv)) as W20. pose proof (u64_range (getr regs 21%bv)) as W21.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  unfold compare, used. cbn [cells BnModel.ex].
  hide Hda; hide Hdb.
  destruct (Z.ltb_spec (zlen ca + ea) (zlen cb + eb)) as [L1|L1].
  { (* [comment removed for export] *)
    cmpE_run [true] (@nil Z) regs m rom oa ob ca cb ea eb ret sp.
    zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSA 0; kcsh OSA 0; kcsh OSB 0; kcsh OSB 0; kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I)
      ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs0.
    fin1 regs0 ret ZM ZR ZE R1 R2 Hret. }
  destruct (Z.ltb_spec (zlen cb + eb) (zlen ca + ea)) as [L2|L2].
  { (* [comment removed for export] *)
    cmpE_run [false; false] (@nil Z) regs m rom oa ob ca cb ea eb ret sp.
    zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSA 0; kcsh OSA 0; kcsh OSB 0; kcsh OSB 0; kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I)
      ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs0.
    fin1 regs0 ret ZM ZR ZE R1 R2 Hret. }
  (* [comment removed for export] *)
  set (m1 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
              (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 ret))
              (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (getr regs 8%bv)))
              (Z_to_bv 64 (sp + -24)) (word_to_le_bytes 8 (getr regs 9%bv)))
              (Z_to_bv 64 (sp + -32)) (word_to_le_bytes 8 (getr regs 18%bv)))
              (Z_to_bv 64 (sp + -40)) (word_to_le_bytes 8 (getr regs 19%bv)))
              (Z_to_bv 64 (sp + -48)) (word_to_le_bytes 8 (getr regs 20%bv)))
              (Z_to_bv 64 (sp + -56)) (word_to_le_bytes 8 (getr regs 21%bv))).
  assert (SV1 : SAVED m1 (sp - 64) (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv))).
  { unfold SAVED, m1. clear - Hsp1 Hsp2 Hretr W8 W9 W18 W19 W20 W21.
    replace (sp - 64 + 56) with (sp + -8) by lia. replace (sp - 64 + 48) with (sp + -16) by lia. replace (sp - 64 + 40) with (sp + -24) by lia.
    replace (sp - 64 + 32) with (sp + -32) by lia. replace (sp - 64 + 24) with (sp + -40) by lia. replace (sp - 64 + 16) with (sp + -48) by lia.
    replace (sp - 64 + 8) with (sp + -56) by lia.
    repeat split; cellx. }
  unhide.
  assert (U01 : unch m m1 [(sp - 64, sp)]) by (unfold m1; clear - Hsp1 Hsp2; unchx).
  assert (Aarr1 : arr32 SEGS_B m1 (oa + 4) ca).
  { eapply arr32_unch; [exact U01 | lia | cbn [length]; unfold zlen in *; lia | | exact Aarr]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn [fst snd length]; unfold zlen in *; lia. }
  assert (Barr1 : arr32 SEGS_B m1 (ob + 4) cb).
  { eapply arr32_unch; [exact U01 | lia | cbn [length]; unfold zlen in *; lia | | exact Barr]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn [fst snd length]; unfold zlen in *; lia. }
  assert (OSA1 : objshB m1 oa).
  { eapply (objshB_unch m _ [(sp - 64, sp)]); [exact U01 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSA]. }
  assert (OSB1 : objshB m1 ob).
  { eapply (objshB_unch m _ [(sp - 64, sp)]); [exact U01 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSB]. }
  hide Hda; hide Hdb.
  assert (LOOP : forall regs1 (dmin : bool),
    keeps cmpL_keep regs regs1 -> getr regs1 2%bv = Z_to_bv 64 (sp - 64) ->
    getr regs1 18%bv = Z_to_bv 64 (ea + zlen ca) -> getr regs1 13%bv = Z_to_bv 64 (if dmin then eb else ea) ->
    (if dmin then eb < ea else ea <= eb) ->
    getr regs1 16%bv = Z_to_bv 64 ea -> getr regs1 17%bv = Z_to_bv 64 eb ->
    getr regs1 5%bv = Z_to_bv 64 (ea + zlen ca) -> getr regs1 6%bv = Z_to_bv 64 (eb + zlen cb) -> getr regs1 14%bv = Z_to_bv 64 ((ea + zlen ca) * 4) ->
    getr regs1 15%bv = Z_to_bv 64 SHA -> getr regs1 10%bv = Z_to_bv 64 18446744073709551615 ->
    getr regs1 7%bv = Z_to_bv 64 (18446744073709551615 - (oa + 4)) -> getr regs1 28%bv = Z_to_bv 64 (18446744073709551615 - (ob + 4)) ->
    getr regs1 12%bv = Z_to_bv 64 (oa - ea * 4) -> getr regs1 9%bv = Z_to_bv 64 (oa - ea * 4) ->
    getr regs1 29%bv = Z_to_bv 64 (Z.lxor ((ea * 4) mod 18446744073709551616) 18446744073709551612) ->
    getr regs1 8%bv = Z_to_bv 64 (ob - eb * 4) -> getr regs1 30%bv = Z_to_bv 64 (ob - eb * 4) ->
    getr regs1 31%bv = Z_to_bv 64 (Z.lxor ((eb * 4) mod 18446744073709551616) 18446744073709551612) ->
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab6ec) m rom) (mkst regs1 (Z_to_bv 64 0x0ab7ec) m1 rom) ->
    exists regs' m',
      msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab6ec) m rom) (mkst regs' ret m' rom)
      /\ keeps CS regs regs'
      /\ getr regs' 10%bv = Z_to_bv 64 (cmp_loop (Z.to_nat (zlen ca + ea - Z.min ea eb)) {| cells := ca; ex := ea |} {| cells := cb; ex := eb |} (zlen ca + ea - 1))
      /\ unch m m' [(sp - 64, sp)] /\ mem_grows m m').
  { intros regs1 dmin K1 S1 B18 B13 Hd B16 B17 B5 B6 B14 B15 B10 B7 B28 B12 B9 B29 B8 B30 B31 M1.
    destruct (cmp_loop_B rom (Z.to_nat (zlen ca + ea - Z.min ea eb)) (zlen ca + ea - 1) regs1 m1 oa ob ea eb (zlen ca + ea) (sp - 64) (bv_unsigned ret)
                (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv)) (bv_unsigned (getr regs 19%bv))
                (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) ca cb ret)
      as (regs2 & M2 & K2 & A2 & RS);
      [ rewrite B18; f_equal; lia | rewrite B13; f_equal; destruct dmin; lia | exact B16 | exact B17 | rewrite B5; f_equal; lia | rewrite B6; f_equal; lia
      | rewrite B14; f_equal; lia | exact B15 | exact B10 | rewrite B7; f_equal; lia | rewrite B28; f_equal; lia
      | rewrite B12; f_equal; lia | rewrite B9; f_equal; lia | rewrite B29; etransitivity; [apply xor4_val; lia | f_equal; lia]
      | rewrite B8; f_equal; lia | rewrite B30; f_equal; lia | rewrite B31; etransitivity; [apply xor4_val; lia | f_equal; lia]
      | exact S1 | exact SV1 | apply Z_to_bv_bv_unsigned | exact Hret | lia | lia
      | exact Aarr1 | exact Barr1 | exact Hoka | exact Hokb | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
      | exact OSA1 | exact OSB1 | lia | lia | lia | lia | ].
    exists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    destruct RS as (Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21).
    split; [|split; [exact A2|split; [exact U01|unfold m1; growsx]]].
    apply keeps_CS_asm; [eapply keeps_trans; [exact K1 | exact K2]
      | rewrite Q2, R2; f_equal; lia
      | rewrite Q8; apply Z_to_bv_bv_unsigned | rewrite Q9; apply Z_to_bv_bv_unsigned | rewrite Q18; apply Z_to_bv_bv_unsigned
      | rewrite Q19; apply Z_to_bv_bv_unsigned | rewrite Q20; apply Z_to_bv_bv_unsigned | rewrite Q21; apply Z_to_bv_bv_unsigned]. }
  destruct (Z.lt_ge_cases eb ea) as [D|D].
  - cmpE_run [false; true; true] [0x0ab7ec] regs m rom oa ob ca cb ea eb ret sp.
    zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSA 0; kcsh OSA 0; kcsh OSB 0; kcsh OSB 0; kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I)
      ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs0.
    cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in ZM.
    change (getr regs (Z_to_bv 5 8)) with (getr regs 8%bv) in ZM. change (getr regs (Z_to_bv 5 9)) with (getr regs 9%bv) in ZM.
    change (getr regs (Z_to_bv 5 18)) with (getr regs 18%bv) in ZM. change (getr regs (Z_to_bv 5 19)) with (getr regs 19%bv) in ZM.
    change (getr regs (Z_to_bv 5 20)) with (getr regs 20%bv) in ZM. change (getr regs (Z_to_bv 5 21)) with (getr regs 21%bv) in ZM.
    rewrite !Z_to_bv_bv_unsigned in ZM.
    apply (LOOP regs0 true); try (zx_regv ZR).
    { eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. } { exact D. } { exact ZM. }
  - cmpE_run [false; true; false] [0x0ab7ec] regs m rom oa ob ca cb ea eb ret sp.
    zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSA 0; kcsh OSA 0; kcsh OSB 0; kcsh OSB 0; kc1 Au; kc1 Ae; kc1 Bu; kc1 Be; exact I)
      ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs0.
    cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in ZM.
    change (getr regs (Z_to_bv 5 8)) with (getr regs 8%bv) in ZM. change (getr regs (Z_to_bv 5 9)) with (getr regs 9%bv) in ZM.
    change (getr regs (Z_to_bv 5 18)) with (getr regs 18%bv) in ZM. change (getr regs (Z_to_bv 5 19)) with (getr regs 19%bv) in ZM.
    change (getr regs (Z_to_bv 5 20)) with (getr regs 20%bv) in ZM. change (getr regs (Z_to_bv 5 21)) with (getr regs 21%bv) in ZM.
    rewrite !Z_to_bv_bv_unsigned in ZM.
    apply (LOOP regs0 false); try (zx_regv ZR).
    { eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. } { exact D. } { exact ZM. }
Qed.
End S.
