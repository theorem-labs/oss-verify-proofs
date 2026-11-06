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

(* [comment removed for export] *)
Ltac shread OSH u :=
  first [ apply (cellN_eqa _ _ _ _ _ _ _ (OSH ((4 + 4 * u) / 8) ltac:(lia))); [lia|reflexivity]
        | apply (cellN_eqa _ _ _ _ _ _ _ (OSH ((8 + 4 * u) / 8) ltac:(lia))); [lia|reflexivity]
        | apply (cellN_eqa _ _ _ _ _ _ _ (OSH ((12 + 4 * u) / 8) ltac:(lia))); [lia|reflexivity] ].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation car64_pins := [(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (31%bv : reg, ZV 34); (17%bv : reg, ZAdd (ZV 32) (ZL 4)); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (5%bv : reg, ZL 128); (28%bv : reg, ZL 1); (15%bv : reg, ZL 268435455); (13%bv : reg, ZL SHA)].
Abbreviation car64_kw := [KW (ZV 32) 0 2; KW (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 33) (ZL 4))) 0 12].
Definition car64_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 10; 11; 13; 14; 15; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30].

Ltac car64_obls ZXB OSH Hsto u :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; exact I) ltac:(kw1 Hsto; kw1 Hsto; exact I)
    ltac:(idtac; zx_scs ltac:(first [shread OSH u | eapply sc_store_in; [exact Hsto|zwidth; lia]])).

#[using="Type"] Lemma car64_A : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 16%bv = Z_to_bv 64 u -> getr regs 31%bv = Z_to_bv 64 c ->
  getr regs 17%bv = Z_to_bv 64 (o + 4) -> getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 5%bv = Z_to_bv 64 128 -> getr regs 28%bv = Z_to_bv 64 1 ->
  getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 13%bv = Z_to_bv 64 SHA ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  arr32 SEGS_A m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa730) m rom) (mkst regs' (Z_to_bv 64 0x0aa6a4) m' rom)
    /\ arr32 SEGS_A m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_A m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 16%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps car64_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R16 RC R17 R14 R5 R28 R15 R13 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Ho8 OSH Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] car64_kw)
      60%nat [0x0aa6a4] (SCR [] [ZL 0]) constr:(car64_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) regs m rom 0x0aa730.
    car64_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] car64_kw)
      60%nat [0x0aa6a4] (SCR [] [ZL 0; ZL 0]) constr:(car64_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) regs m rom 0x0aa730.
    car64_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    replace (o + 4 + u * 4 + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - rewrite chunks_3 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 56, 2 ^ 63)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] car64_kw)
      60%nat [0x0aa6a4] (SCR [] [ZL 0; ZL 0; ZL 0]) constr:(car64_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 56, 2 ^ 63)]) regs m rom 0x0aa730.
    car64_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456 mod 268435456; c / 268435456 / 268435456])
      with (((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]) ++ [c / 268435456 / 268435456]) by (rewrite <- !app_assoc; reflexivity).
    replace (o + 4 + u * 4 + 8) with (o + 4 + 4 * Z.of_nat (length ((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]))) by (rewrite !length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite !length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + u * 4 + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation car13_pins := [(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (30%bv : reg, ZV 34); (17%bv : reg, ZAdd (ZV 32) (ZL 4)); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (5%bv : reg, ZL 128); (7%bv : reg, ZL 1); (15%bv : reg, ZL 268435455); (13%bv : reg, ZL SHA)].
Abbreviation car13_kw := [KW (ZV 32) 0 2; KW (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 33) (ZL 4))) 0 12].
Definition car13_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 9; 10; 11; 13; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29].

Ltac car13_obls ZXB OSH Hsto u :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; exact I) ltac:(kw1 Hsto; kw1 Hsto; exact I)
    ltac:(idtac; zx_scs ltac:(first [shread OSH u | eapply sc_store_in; [exact Hsto|zwidth; lia]])).

#[using="Type"] Lemma car13_A : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 16%bv = Z_to_bv 64 u -> getr regs 30%bv = Z_to_bv 64 c ->
  getr regs 17%bv = Z_to_bv 64 (o + 4) -> getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 5%bv = Z_to_bv 64 128 -> getr regs 7%bv = Z_to_bv 64 1 ->
  getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 13%bv = Z_to_bv 64 SHA ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  arr32 SEGS_A m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa854) m rom) (mkst regs' (Z_to_bv 64 0x0aa7d8) m' rom)
    /\ arr32 SEGS_A m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_A m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 16%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps car13_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R16 RC R17 R14 R5 R7 R15 R13 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Ho8 OSH Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] car13_kw)
      60%nat [0x0aa7d8] (SCR [] [ZL 0]) constr:(car13_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) regs m rom 0x0aa854.
    car13_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] car13_kw)
      60%nat [0x0aa7d8] (SCR [] [ZL 0; ZL 0]) constr:(car13_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) regs m rom 0x0aa854.
    car13_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    replace (o + 4 + u * 4 + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - rewrite chunks_3 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 56, 2 ^ 63)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] car13_kw)
      60%nat [0x0aa7d8] (SCR [] [ZL 0; ZL 0; ZL 0]) constr:(car13_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 56, 2 ^ 63)]) regs m rom 0x0aa854.
    car13_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456 mod 268435456; c / 268435456 / 268435456])
      with (((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]) ++ [c / 268435456 / 268435456]) by (rewrite <- !app_assoc; reflexivity).
    replace (o + 4 + u * 4 + 8) with (o + 4 + 4 * Z.of_nat (length ((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]))) by (rewrite !length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite !length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + u * 4 + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation cartb_pins := [(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (17%bv : reg, ZV 34); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (15%bv : reg, ZL 268435455); (13%bv : reg, ZL SHA)].
Abbreviation cartb_kw := [KW (ZV 32) 0 2; KW (ZAdd (ZV 32) (ZMul (ZV 33) (ZL 4))) 4 16].
Definition cartb_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 11; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].

Ltac cartb_obls ZXB OSH Hsto u :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; exact I) ltac:(kw1 Hsto; kw1 Hsto; exact I)
    ltac:(idtac; zx_scs ltac:(first [shread OSH u | eapply sc_store_in; [exact Hsto|zwidth; lia]])).

#[using="Type"] Lemma cartb_A : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 16%bv = Z_to_bv 64 u -> getr regs 17%bv = Z_to_bv 64 c ->
  getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) ->
  getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 13%bv = Z_to_bv 64 SHA ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  arr32 SEGS_A m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aaadc) m rom) (mkst regs' (Z_to_bv 64 0x0aa9b8) m' rom)
    /\ arr32 SEGS_A m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_A m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 16%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps cartb_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R16 RC R14 R15 R13 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Ho8 OSH Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] cartb_kw)
      60%nat [0x0aa9b8] (SCR [] [ZL 0]) constr:(cartb_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) regs m rom 0x0aaadc.
    cartb_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + u * 4 + 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] cartb_kw)
      60%nat [0x0aa9b8] (SCR [] [ZL 0; ZL 0]) constr:(cartb_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) regs m rom 0x0aaadc.
    cartb_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    replace (o + u * 4 + 8) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + u * 4 + 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - rewrite chunks_3 by (unfold B; lia). unfold B.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 56, 2 ^ 63)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] cartb_kw)
      60%nat [0x0aa9b8] (SCR [] [ZL 0; ZL 0; ZL 0]) constr:(cartb_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 56, 2 ^ 63)]) regs m rom 0x0aaadc.
    cartb_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456 mod 268435456; c / 268435456 / 268435456])
      with (((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]) ++ [c / 268435456 / 268435456]) by (rewrite <- !app_assoc; reflexivity).
    replace (o + u * 4 + 12) with (o + 4 + 4 * Z.of_nat (length ((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]))) by (rewrite !length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite !length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + u * 4 + 8) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + u * 4 + 4) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
Qed.

End S.
