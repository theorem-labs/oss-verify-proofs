(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface BnP_add BnU_add.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation addL_pins :=
  [(10%bv : reg, ZMul (ZV 34) (ZL 4)); (12%bv : reg, ZV 35); (13%bv : reg, ZV 34); (18%bv : reg, ZV 34);
   (14%bv : reg, ZAdd (ZV 33) (ZL 4)); (15%bv : reg, ZV 32); (16%bv : reg, ZV 32); (17%bv : reg, ZAdd (ZV 32) (ZL 4));
   (5%bv : reg, ZAdd (ZV 32) (ZL 4)); (6%bv : reg, ZMul (ZV 37) (ZL 4)); (11%bv : reg, ZL 268435455);
   (20%bv : reg, ZL SHA); (22%bv : reg, ZV 36)].
(* [comment removed for export] *)
Abbreviation Tb := (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 34) (ZL 4))).
Abbreviation Qb := (ZAdd (ZAdd (ZV 33) (ZL 4)) (ZMul (ZV 34) (ZL 4))).
Abbreviation addL_knx := [KC Tb 0 4 (ZV 38); KC Qb 0 4 (ZV 39); KC (ZDivP Tb 3) SHA 1 (ZL 0); KC (ZDivP Qb 3) SHA 1 (ZL 0)].
Abbreviation addL_kn0 := [KC Qb 0 4 (ZV 39); KC (ZDivP Tb 3) SHA 1 (ZL 0); KC (ZDivP Qb 3) SHA 1 (ZL 0)].
Abbreviation addL_uvi :=
  [Some (IMG, HIE - 516); Some (IMG, HIE - 516); Some (0, 126); Some (0, 1); Some (0, 127); Some (1, 127);
   Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 28 - 1)].
Definition addL_keep : list Z := [1; 2; 3; 4; 5; 6; 8; 9; 11; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma add_loop_A : forall ot odone lt done c regs m (o q u : Z),
  let i := Z.of_nat (length odone) in
  let n := Z.of_nat (length odone) + Z.of_nat (length ot) in
  Z.of_nat (length done) = i ->
  getr regs 10%bv = Z_to_bv 64 (i * 4) -> getr regs 12%bv = Z_to_bv 64 c -> getr regs 13%bv = Z_to_bv 64 i ->
  getr regs 18%bv = Z_to_bv 64 i -> getr regs 14%bv = Z_to_bv 64 (q + 4) -> getr regs 15%bv = Z_to_bv 64 o ->
  getr regs 16%bv = Z_to_bv 64 o -> getr regs 17%bv = Z_to_bv 64 (o + 4) -> getr regs 5%bv = Z_to_bv 64 (o + 4) ->
  getr regs 6%bv = Z_to_bv 64 (n * 4) -> getr regs 11%bv = Z_to_bv 64 MASK -> getr regs 20%bv = Z_to_bv 64 SHA ->
  getr regs 22%bv = Z_to_bv 64 u ->
  Z.max u i = i + zlen lt -> 0 <= u <= 127 -> n <= 127 -> ok lt -> ok ot -> ot <> [] -> 0 <= c <= 1 ->
  APP o 516 -> o + 516 <= HIE -> APP q 516 -> q + 516 <= HIE -> o mod 8 = 0 -> q mod 8 = 0 ->
  (q + 516 <= o \/ o + 516 <= q) -> objsh m o -> objsh m q ->
  arr32 SEGS_A m (o + 4) (done ++ lt) -> arr32 SEGS_A m (q + 4) (odone ++ ot) ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m' S,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aae7c) m rom) (mkst regs' (Z_to_bv 64 0x0aaf2c) m' rom)
    /\ arr32 SEGS_A m' (o + 4) (done ++ fst (addm c lt ot) ++ skipn (length ot) lt)
    /\ getr regs' 12%bv = Z_to_bv 64 (snd (addm c lt ot)) /\ getr regs' 30%bv = Z_to_bv 64 S
    /\ S / 2 ^ 28 = snd (addm c lt ot) /\ 0 <= S < 2 ^ 30
    /\ getr regs' 13%bv = Z_to_bv 64 n /\ getr regs' 18%bv = Z_to_bv 64 n /\ getr regs' 10%bv = Z_to_bv 64 (n * 4)
    /\ keeps addL_keep regs regs'
    /\ unch m m' [(o + 4 + 4 * i, o + 4 + 4 * n)] /\ mem_grows m m'.
Proof.
  induction ot as [|y ot IH]; intros odone lt done c regs m o q u i n Hdone R10 R12 R13 R18 R14 R15 R16 R17 R5 R6 R11 R20 R22
    Hmax Hu Hn Hokl Hoko Hne Hc Ho1 Ho2 Hq1 Hq2 Ho8 Hq8 Hdj OSH QSH Harr Harro Hsto; [congruence|].
  subst i n. apply ok_cons in Hoko as [Hy Hoko]. cbn [length] in *. unfold MASK in R11. unfold B in *.
  set (i := Z.of_nat (length odone)) in *.
  assert (Hidef : i = Z.of_nat (length odone)) by reflexivity.
  assert (Hi : 0 <= i) by lia.
  assert (Hcy : cellN SEGS_A m (q + 4 + 4 * i) 4 y).
  { eapply kc_of_arr32; [exact Harro | lia]. }
  pose proof (zlen_nonneg lt) as Hlt0.
  cbn [addm].
  destruct lt as [|x t].
  - (* [comment removed for export] *)
    cbn [hd tl skipn]. unfold B in *. rewrite zlen_nil in Hmax.
    destruct (addm ((0 + y + c) / 268435456) [] ot) as [r c'] eqn:Hrec. cbn [fst snd].
    destruct ot as [|y2 ot'].
    + (* [comment removed for export] *)
      cbn [length] in *. change (Z.of_nat 1) with 1 in *.
      zx_run SEGS_A constr:(CTX (vi_regs ++ addL_uvi) addL_kn0 [KW Tb 0 4]) 40%nat [0x0aae7c; 0x0aaf2c] (SCR [true; false] [])
        constr:(addL_pins) [o; q; i; c; u; i + 1; 0; y] constr:(addL_uvi) regs m rom 0x0aae7c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
        ltac:(kc1 Hcy; kcsh OSH ((4 + 4 * i) / 8); kcsh QSH ((4 + 4 * i) / 8); exact I)
        ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(lia)).
      zx_name regs1.
      cbn in Hrec. injection Hrec as <- <-. cbn [app skipn length]. rewrite ?skipn_O.
      eexists regs1, _, (y + c). split; [exact ZM|].
      split.
      { rewrite ?app_nil_r. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_snoc' ; [lia | lia | rewrite app_nil_r in Harr; exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      split; [zx_regv ZR; f_equal; lia|]. split; [zx_regv ZR|]. split; [f_equal; lia|]. split; [lia|].
      split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [unchx | growsx].
    + (* [comment removed for export] *)
      cbn [length] in *.
      zx_run SEGS_A constr:(CTX (vi_regs ++ addL_uvi) addL_kn0 [KW Tb 0 4]) 40%nat [0x0aae7c; 0x0aaf2c] (SCR [true; true] [])
        constr:(addL_pins) [o; q; i; c; u; i + Z.of_nat (S (S (length ot'))); 0; y] constr:(addL_uvi) regs m rom 0x0aae7c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(cbn [length] in *; zx_lia)
        ltac:(kc1 Hcy; kcsh OSH ((4 + 4 * i) / 8); kcsh QSH ((4 + 4 * i) / 8); exact I)
        ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(lia)).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_A m1 (o + 4) ((done ++ [(y + c) mod 268435456]) ++ [])).
      { rewrite !app_nil_r. unfold m1. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_snoc'; [lia | lia | rewrite app_nil_r in Harr; exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      assert (Harro1 : arr32 SEGS_A m1 (q + 4) ((odone ++ [y]) ++ y2 :: ot')).
      { rewrite <- app_assoc. cbn [app]. unfold m1. apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia. exact Harro. }
      assert (OSH1 : objsh m1 o).
      { unfold m1. eapply (objsh_unch m _ [(o + 4 + i * 4, o + 4 + i * 4 + 4)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
      assert (QSH1 : objsh m1 q).
      { unfold m1. eapply (objsh_unch m _ [(o + 4 + i * 4, o + 4 + i * 4 + 4)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact QSH]. }
      specialize (IH (odone ++ [y]) [] (done ++ [(y + c) mod 268435456]) ((0 + y + c) / 268435456) regs1 m1 o q u).
      rewrite !length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
      destruct IH as (regs2 & m2 & S & M2 & Harr2 & C12 & C30 & HS & HS2 & C13 & C18 & C10 & K2 & U2 & G2).
      { lia. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { rewrite zlen_nil. lia. } { lia. } { lia. } { apply ok_nil. } { exact Hoko. } { congruence. } { lia. }
      { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact Hq8. } { exact Hdj. } { exact OSH1. } { exact QSH1. }
      { exact Harr1. } { exact Harro1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, S. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      cbn [skipn app] in Harr2. rewrite <- app_assoc in Harr2. cbn [app] in Harr2. rewrite ?app_nil_r in Harr2.
      split; [rewrite ?app_nil_r; replace (0 + y + c) with (y + c) by lia; exact Harr2|].
      split; [exact C12|]. split; [exact C30|]. split; [exact HS|]. split; [exact HS2|].
      split; [rewrite C13; f_equal; lia|]. split; [rewrite C18; f_equal; lia|]. split; [rewrite C10; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
  - (* [comment removed for export] *)
    cbn [hd tl skipn]. unfold B in *. rewrite zlen_cons in Hmax. apply ok_cons in Hokl as [Hx Hokt]. unfold B in Hx.
    pose proof (zlen_nonneg t) as Hlt1. assert (Hzt : zlen t = Z.of_nat (length t)) by reflexivity.
    assert (Hcx : cellN SEGS_A m (o + 4 + 4 * i) 4 x).
    { eapply kc_of_arr32; [exact Harr | lia]. }
    destruct (addm ((x + y + c) / 268435456) t ot) as [r c'] eqn:Hrec. cbn [fst snd].
    destruct ot as [|y2 ot'].
    + (* [comment removed for export] *)
      cbn [length] in *. change (Z.of_nat 1) with 1 in *.
      zx_run SEGS_A constr:(CTX (vi_regs ++ addL_uvi) addL_knx [KW Tb 0 4]) 40%nat [0x0aae7c; 0x0aaf2c] (SCR [false; false] [])
        constr:(addL_pins) [o; q; i; c; u; i + 1; x; y] constr:(addL_uvi) regs m rom 0x0aae7c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
        ltac:(kc1 Hcx; kc1 Hcy; kcsh OSH ((4 + 4 * i) / 8); kcsh QSH ((4 + 4 * i) / 8); exact I)
        ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(lia)).
      zx_name regs1.
      cbn in Hrec. injection Hrec as <- <-. cbn [app skipn length]. rewrite ?skipn_O.
      eexists regs1, _, (x + c + y). split; [exact ZM|].
      split.
      { replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      split; [zx_regv ZR; f_equal; lia|]. split; [zx_regv ZR; f_equal; lia|]. split; [f_equal; lia|]. split; [lia|].
      split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [unchx | growsx].
    + (* [comment removed for export] *)
      cbn [length] in *.
      zx_run SEGS_A constr:(CTX (vi_regs ++ addL_uvi) addL_knx [KW Tb 0 4]) 40%nat [0x0aae7c; 0x0aaf2c] (SCR [false; true] [])
        constr:(addL_pins) [o; q; i; c; u; i + Z.of_nat (S (S (length ot'))); x; y] constr:(addL_uvi) regs m rom 0x0aae7c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(cbn [length] in *; zx_lia)
        ltac:(kc1 Hcx; kc1 Hcy; kcsh OSH ((4 + 4 * i) / 8); kcsh QSH ((4 + 4 * i) / 8); exact I)
        ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(lia)).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_A m1 (o + 4) ((done ++ [(x + y + c) mod 268435456]) ++ t)).
      { rewrite <- app_assoc. cbn [app]. unfold m1. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      assert (Harro1 : arr32 SEGS_A m1 (q + 4) ((odone ++ [y]) ++ y2 :: ot')).
      { rewrite <- app_assoc. cbn [app]. unfold m1. apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia. exact Harro. }
      assert (OSH1 : objsh m1 o).
      { unfold m1. eapply (objsh_unch m _ [(o + 4 + i * 4, o + 4 + i * 4 + 4)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
      assert (QSH1 : objsh m1 q).
      { unfold m1. eapply (objsh_unch m _ [(o + 4 + i * 4, o + 4 + i * 4 + 4)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact QSH]. }
      specialize (IH (odone ++ [y]) t (done ++ [(x + y + c) mod 268435456]) ((x + y + c) / 268435456) regs1 m1 o q u).
      rewrite !length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
      destruct IH as (regs2 & m2 & S & M2 & Harr2 & C12 & C30 & HS & HS2 & C13 & C18 & C10 & K2 & U2 & G2).
      { lia. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { lia. } { lia. } { exact Hokt. } { exact Hoko. } { congruence. } { lia. }
      { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact Hq8. } { exact Hdj. } { exact OSH1. } { exact QSH1. }
      { exact Harr1. } { exact Harro1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, S. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      rewrite <- app_assoc in Harr2. cbn [app] in Harr2.
      split; [exact Harr2|].
      split; [exact C12|]. split; [exact C30|]. split; [exact HS|]. split; [exact HS2|].
      split; [rewrite C13; f_equal; lia|]. split; [rewrite C18; f_equal; lia|]. split; [rewrite C10; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation addC_pins :=
  [(10%bv : reg, ZV 32); (14%bv : reg, ZV 32); (13%bv : reg, ZV 33); (18%bv : reg, ZV 33); (12%bv : reg, ZV 34);
   (11%bv : reg, ZL 268435455); (20%bv : reg, ZL SHA); (22%bv : reg, ZV 35)].
Abbreviation addC_knx := [KC (ZV 32) 0 4 (ZV 36); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)].
Abbreviation addC_kn0 := [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)].
Abbreviation addC_uvi := [Some (IMG, HIE - 8); Some (0, 126); Some (1, 1); Some (0, 127); Some (0, 2 ^ 28 - 1)].
Definition addC_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma addc_loop_A : forall lt (pos c : Z) regs m (o u : Z),
  getr regs 10%bv = Z_to_bv 64 (o + 4 + 4 * pos) -> getr regs 14%bv = Z_to_bv 64 (o + 4 + 4 * pos) ->
  getr regs 13%bv = Z_to_bv 64 pos -> getr regs 18%bv = Z_to_bv 64 pos -> getr regs 12%bv = Z_to_bv 64 c ->
  getr regs 11%bv = Z_to_bv 64 MASK -> getr regs 20%bv = Z_to_bv 64 SHA -> getr regs 22%bv = Z_to_bv 64 u ->
  Z.max u pos = pos + zlen lt -> 0 <= u <= 127 -> 0 <= pos -> pos + zlen lt + 1 <= 127 -> ok lt -> 0 < c <= 1 ->
  APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  arr32 SEGS_A m (o + 4 + 4 * pos) lt ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m' k,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aaf94) m rom) (mkst regs' (Z_to_bv 64 0x0aaf34) m' rom)
    /\ arr32 SEGS_A m' (o + 4 + 4 * pos) (addc_l c lt)
    /\ 1 <= k /\ zlen (addc_l c lt) = Z.max (zlen lt) k
    /\ getr regs' 18%bv = Z_to_bv 64 (pos + k)
    /\ keeps addC_keep regs regs'
    /\ unch m m' [(o + 4 + 4 * pos, o + 4 + 4 * (pos + zlen (addc_l c lt)))] /\ mem_grows m m'.
Proof.
  induction lt as [|x t IH]; intros pos c regs m o u R10 R14 R13 R18 R12 R11 R20 R22 Hmax Hu Hpos Hcap Hok Hc Ho1 Ho2 Ho8 OSH Harr Hsto.
  - (* [comment removed for export] *)
    rewrite zlen_nil in *. unfold MASK in R11.
    cbn [addc_l]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    zx_run SEGS_A constr:(CTX (vi_regs ++ addC_uvi) addC_kn0 [KW (ZV 32) 0 4]) 40%nat [0x0aaf94; 0x0aaf34] (SCR [true] [])
      constr:(addC_pins) [o + 4 + 4 * pos; pos; c; u; 0] constr:(addC_uvi) regs m rom 0x0aaf94.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kcsh OSH ((4 + 4 * pos) / 8); exact I)
      ltac:(kw1 Hsto; exact I)
      ltac:(idtac; zx_scs ltac:(lia)).
    zx_name regs1.
    eexists regs1, _, 1. split; [exact ZM|].
    split.
    { change [c] with ([] ++ [c]). replace (o + 4 + 4 * pos) with (o + 4 + 4 * pos + 4 * Z.of_nat (@length Z [])) at 1 by (cbn; lia).
      apply arr32_snoc'; [lia | cbn; lia | exact Harr |]. rewrite u_Z2bv64. rewrite Z.mod_small by lia. apply Z.mod_small. lia. }
    split; [lia|]. split; [rewrite zlen_cons, zlen_nil; lia|]. split; [zx_regv ZR|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    rewrite zlen_cons, zlen_nil. split; [unchx | growsx].
  - apply ok_cons in Hok as [Hx Hok]. rewrite zlen_cons in *. pose proof (zlen_nonneg t) as Ht0.
    assert (Hzt : zlen t = Z.of_nat (length t)) by reflexivity. unfold MASK in R11. unfold B in Hx.
    assert (Hcx : cellN SEGS_A m (o + 4 + 4 * pos) 4 x).
    { eapply (kc_of_arr32 _ _ _ []); [exact Harr | cbn; lia]. }
    cbn [addc_l]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold addc_l. unfold B in *.
    destruct (Z.eq_dec ((x + c) / 268435456) 0) as [Hz | Hnz].
    + (* [comment removed for export] *)
      zx_run SEGS_A constr:(CTX (vi_regs ++ addC_uvi) addC_knx [KW (ZV 32) 0 4]) 40%nat [0x0aaf94; 0x0aaf34] (SCR [false; false] [])
        constr:(addC_pins) [o + 4 + 4 * pos; pos; c; u; x] constr:(addC_uvi) regs m rom 0x0aaf94.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
        ltac:(kc1 Hcx; kcsh OSH ((4 + 4 * pos) / 8); exact I)
        ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(lia)).
      zx_name regs1.
      rewrite Hz. replace (addc_l 0 t) with t by (destruct t; reflexivity).
      eexists regs1, _, 1. split; [exact ZM|].
      split.
      { change ((x + c) mod 268435456 :: t) with ([] ++ (x + c) mod 268435456 :: t).
        replace (o + 4 + 4 * pos) with (o + 4 + 4 * pos + 4 * Z.of_nat (@length Z [])) at 1 by (cbn; lia).
        apply arr32_store' with (x := x); [lia | cbn [app length]; lia | exact Harr |].
        rewrite u_Z2bv64. change (2 ^ 28) with 268435456. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small; lia. }
      split; [lia|]. split; [rewrite zlen_cons; lia|]. split; [zx_regv ZR|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      rewrite zlen_cons. split; [unchx | growsx].
    + (* [comment removed for export] *)
      assert (Hc1 : (x + c) / 268435456 = 1) by lia.
      replace ((x + c) / 268435456) with 1 by lia.
      zx_run SEGS_A constr:(CTX (vi_regs ++ addC_uvi) addC_knx [KW (ZV 32) 0 4]) 40%nat [0x0aaf94; 0x0aaf34] (SCR [false; true] [])
        constr:(addC_pins) [o + 4 + 4 * pos; pos; c; u; x] constr:(addC_uvi) regs m rom 0x0aaf94.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
        ltac:(kc1 Hcx; kcsh OSH ((4 + 4 * pos) / 8); exact I)
        ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(lia)).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_A m1 (o + 4 + 4 * (pos + 1)) t).
      { unfold m1. apply arr32_store_other; zwidth; try lia. replace (o + 4 + 4 * (pos + 1)) with (o + 4 + 4 * pos + 4) by lia. eapply arr32_tail_g. exact Harr. }
      assert (OSH1 : objsh m1 o).
      { unfold m1. eapply (objsh_unch m _ [(o + 4 + 4 * pos, o + 4 + 4 * pos + 4)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
      destruct (IH (pos + 1) 1 regs1 m1 o u) as (regs2 & m2 & k & M2 & Harr2 & Hk & Hlen2 & C18 & K2 & U2 & G2).
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { lia. } { lia. } { lia. } { exact Hok. } { lia. } { lia. } { lia. } { exact Ho8. } { exact OSH1. } { exact Harr1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, (k + 1). split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split.
      { apply arr32_cons_g; [|replace (o + 4 + 4 * pos + 4) with (o + 4 + 4 * (pos + 1)) by lia; exact Harr2].
        eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
        unfold m1. cellx; try (rewrite Z.mod_small by lia); try reflexivity; try lia. }
      split; [lia|]. split; [rewrite zlen_cons, Hlen2; lia|]. split; [rewrite C18; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; rewrite zlen_cons; pose proof (zlen_nonneg (addc_l 1 t)); unchx|].
        eapply unch_widen; [exact U2|]. intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. rewrite zlen_cons. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation finA1_pins := [(8%bv : reg, ZV 32); (22%bv : reg, ZV 33); (18%bv : reg, ZV 34); (21%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))].
Abbreviation finA1_uvi := [Some (IMG, HIE - 516); Some (0, 127); Some (0, 130)].
Abbreviation finA2_kn := [KC (ZV 32) (-8) 8 (ZV 33); KC (ZV 32) (-16) 8 (ZV 34); KC (ZV 32) (-24) 8 (ZV 35); KC (ZV 32) (-32) 8 (ZV 36);
  KC (ZV 32) (-40) 8 (ZV 37); KC (ZV 32) (-48) 8 (ZV 38); KC (ZV 32) (-56) 8 (ZV 39); KC (ZV 32) (-64) 8 (ZV 40);
  KC (ZV 32) (-72) 8 (ZV 41); KC (ZV 32) (-80) 8 (ZV 42); KC (ZV 32) (-88) 8 (ZV 43); KC (ZV 32) (-96) 8 (ZV 44);
  KC (ZV 32) (-104) 8 (ZV 45)].
Abbreviation big := (Some (0, 18446744073709551615)).
Abbreviation finA2_uvi := [Some (KHI + 112, HIE); big; big; big; big; big; big; big; big; big; big; big; big; big].

#[using="Type"] Lemma fin_add_A : forall regs m (o sp u p : Z) (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 2%bv = Z_to_bv 64 (sp - 112) -> getr regs 22%bv = Z_to_bv 64 u ->
  getr regs 18%bv = Z_to_bv 64 p -> getr regs 21%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) ->
  cellN SEGS_A m (sp - 8) 8 (bv_unsigned ret) -> cellN SEGS_A m (sp - 16) 8 (bv_unsigned s0v) ->
  cellN SEGS_A m (sp - 24) 8 (bv_unsigned s1v) -> cellN SEGS_A m (sp - 32) 8 (bv_unsigned s2v) ->
  cellN SEGS_A m (sp - 40) 8 (bv_unsigned s3v) -> cellN SEGS_A m (sp - 48) 8 (bv_unsigned s4v) ->
  cellN SEGS_A m (sp - 56) 8 (bv_unsigned s5v) -> cellN SEGS_A m (sp - 64) 8 (bv_unsigned s6v) ->
  cellN SEGS_A m (sp - 72) 8 (bv_unsigned s7v) -> cellN SEGS_A m (sp - 80) 8 (bv_unsigned s8v) ->
  cellN SEGS_A m (sp - 88) 8 (bv_unsigned s9v) -> cellN SEGS_A m (sp - 96) 8 (bv_unsigned s10v) ->
  cellN SEGS_A m (sp - 104) 8 (bv_unsigned s11v) ->
  ret_ok ret -> 0 <= u <= 127 -> 0 <= p <= 130 ->
  KHI + 112 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 112 \/ sp <= o) ->
  objsh m o ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aaf34) m rom) (mkst regs' ret m' rom)
    /\ cellN SEGS_A m' o 2 (Z.max u p)
    /\ getr regs' 2%bv = Z_to_bv 64 sp /\ getr regs' 8%bv = s0v /\ getr regs' 9%bv = s1v /\ getr regs' 18%bv = s2v
    /\ getr regs' 19%bv = s3v /\ getr regs' 20%bv = s4v /\ getr regs' 21%bv = s5v /\ getr regs' 22%bv = s6v
    /\ getr regs' 23%bv = s7v /\ getr regs' 24%bv = s8v /\ getr regs' 25%bv = s9v /\ getr regs' 26%bv = s10v
    /\ getr regs' 27%bv = s11v
    /\ keeps [3; 4] regs regs'
    /\ unch m m' [(o, o + 2)] /\ mem_grows m m'.
Proof.
  intros regs m o sp u p ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v R8 R2 R22 R18 R21
    C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 Hret Hu Hp Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj OSH Hsto.
  pose proof (u64_range ret) as U1. pose proof (u64_range s0v) as U2. pose proof (u64_range s1v) as U3. pose proof (u64_range s2v) as U4.
  pose proof (u64_range s3v) as U5. pose proof (u64_range s4v) as U6. pose proof (u64_range s5v) as U7. pose proof (u64_range s6v) as U8.
  pose proof (u64_range s7v) as U9. pose proof (u64_range s8v) as U10. pose proof (u64_range s9v) as U11. pose proof (u64_range s10v) as U12.
  pose proof (u64_range s11v) as U13.
  (* [comment removed for export] *)
  assert (F1 : exists regs1 m1,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aaf34) m rom) (mkst regs1 (Z_to_bv 64 0x0aaf48) m1 rom)
    /\ cellN SEGS_A m1 o 2 (Z.max u p) /\ getr regs1 2%bv = Z_to_bv 64 (sp - 112)
    /\ keeps [2; 3; 4] regs regs1 /\ unch m m1 [(o, o + 2)] /\ mem_grows m m1).
  { hide Hdisj.
    destruct (Z_lt_dec u p) as [Hlt | Hge].
    - zx_run SEGS_A constr:(CTX (vi_regs ++ finA1_uvi) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 2])
        20%nat [0x0aaf48] (SCR [true] []) constr:(finA1_pins) [o; u; p] constr:(finA1_uvi) regs m rom 0x0aaf34.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(lia)).
      zx_name regs1.
      eexists regs1, _. split; [exact ZM|].
      split; [rewrite Z.max_r by lia; cellx; try (rewrite Z.mod_small by lia); try reflexivity; try lia|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R2]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [unchx | growsx].
    - zx_run SEGS_A constr:(CTX (vi_regs ++ finA1_uvi) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 2])
        20%nat [0x0aaf48] (SCR [false] []) constr:(finA1_pins) [o; u; p] constr:(finA1_uvi) regs m rom 0x0aaf34.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(lia)).
      zx_name regs1.
      eexists regs1, _. split; [exact ZM|].
      split; [rewrite Z.max_l by lia; cellx; try (rewrite Z.mod_small by lia); try reflexivity; try lia|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R2]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [unchx | growsx]. }
  destruct F1 as (regs1 & m1 & M1 & Cu1 & Q2 & K1 & U1' & G1).
  assert (SAV : forall a v, cellN SEGS_A m a 8 v -> sp - 112 <= a -> a + 8 <= sp -> cellN SEGS_A m1 a 8 v).
  { intros a v C Ha1 Ha2. eapply cellN_unch; [exact U1' | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; unhide; lia | exact C]. }
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ finA2_uvi) finA2_kn (@nil kwin))
    30%nat [0x0aaf80] (SCR [] []) constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-112)))])
    [sp; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v; bv_unsigned s3v; bv_unsigned s4v; bv_unsigned s5v;
     bv_unsigned s6v; bv_unsigned s7v; bv_unsigned s8v; bv_unsigned s9v; bv_unsigned s10v; bv_unsigned s11v]
    constr:(finA2_uvi) regs1 m1 rom 0x0aaf48.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
    ltac:(kc1 (SAV _ _ C1 ltac:(lia) ltac:(lia)); kc1 (SAV _ _ C2 ltac:(lia) ltac:(lia)); kc1 (SAV _ _ C3 ltac:(lia) ltac:(lia));
          kc1 (SAV _ _ C4 ltac:(lia) ltac:(lia)); kc1 (SAV _ _ C5 ltac:(lia) ltac:(lia)); kc1 (SAV _ _ C6 ltac:(lia) ltac:(lia));
          kc1 (SAV _ _ C7 ltac:(lia) ltac:(lia)); kc1 (SAV _ _ C8 ltac:(lia) ltac:(lia)); kc1 (SAV _ _ C9 ltac:(lia) ltac:(lia));
          kc1 (SAV _ _ C10 ltac:(lia) ltac:(lia)); kc1 (SAV _ _ C11 ltac:(lia) ltac:(lia)); kc1 (SAV _ _ C12 ltac:(lia) ltac:(lia));
          kc1 (SAV _ _ C13 ltac:(lia) ltac:(lia)); exact I)
    ltac:(exact I) ltac:(exact I).
  zx_name regs2.
  assert (R1' : getr regs2 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned).
  eexists regs2, m1. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
  split; [exact Cu1|].
  split; [zx_regv ZR|].
  split; [zx_reg ZR (8%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (9%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (18%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (19%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (20%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (21%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (22%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (23%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (24%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (25%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (26%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (27%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]|].
  split; [exact U1' | exact G1].
Qed.
End S.
