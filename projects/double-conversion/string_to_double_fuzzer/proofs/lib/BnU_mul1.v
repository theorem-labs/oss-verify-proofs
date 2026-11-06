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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation car64_pins := [(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (30%bv : reg, ZV 34); (9%bv : reg, ZV 35); (8%bv : reg, ZV 36);
                            (15%bv : reg, ZL 128); (13%bv : reg, ZL 268435455); (17%bv : reg, ZSub (ZL 18446744073709551611) (ZV 32))].
Definition car64_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29].

#[using="Type"] Lemma car64_U : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 u -> getr regs 30%bv = Z_to_bv 64 c ->
  getr regs 9%bv = Z_to_bv 64 (o + 4 + 4 * u) -> getr regs 8%bv = Z_to_bv 64 (4 * u) ->
  getr regs 15%bv = Z_to_bv 64 128 -> getr regs 13%bv = Z_to_bv 64 MASK -> getr regs 17%bv = Z_to_bv 64 (18446744073709551611 - o) ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> 0 <= o -> o + 516 <= 2 ^ 62 ->
  arr32 SEGS_U m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x360b8) m rom) (mkst regs' (Z_to_bv 64 0x3602c) m' rom)
    /\ arr32 SEGS_U m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_U m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 12%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps car64_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R12 RC RP R8 R128 R13 R17 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x3602c] (SCR [] []) constr:(car64_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x360b8.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x3602c] (SCR [] []) constr:(car64_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x360b8.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    replace (o + 4 + 4 * u + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - rewrite chunks_3 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x3602c] (SCR [] []) constr:(car64_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x360b8.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456 mod 268435456; c / 268435456 / 268435456])
      with (((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]) ++ [c / 268435456 / 268435456]) by (rewrite <- !app_assoc; reflexivity).
    replace (o + 4 + 4 * u + 8) with (o + 4 + 4 * Z.of_nat (length ((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]))) by (rewrite !length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite !length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation car13_pins := [(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (29%bv : reg, ZV 34); (8%bv : reg, ZV 35); (31%bv : reg, ZV 36);
                            (15%bv : reg, ZL 128); (13%bv : reg, ZL 268435455); (17%bv : reg, ZSub (ZL 18446744073709551611) (ZV 32))].
Definition car13_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28].

#[using="Type"] Lemma car13_U : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 u -> getr regs 29%bv = Z_to_bv 64 c ->
  getr regs 8%bv = Z_to_bv 64 (o + 4 + 4 * u) -> getr regs 31%bv = Z_to_bv 64 (4 * u) ->
  getr regs 15%bv = Z_to_bv 64 128 -> getr regs 13%bv = Z_to_bv 64 MASK -> getr regs 17%bv = Z_to_bv 64 (18446744073709551611 - o) ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> 0 <= o -> o + 516 <= 2 ^ 62 ->
  arr32 SEGS_U m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x36198) m rom) (mkst regs' (Z_to_bv 64 0x36120) m' rom)
    /\ arr32 SEGS_U m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_U m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 12%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps car13_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R12 RC RP R8 R128 R13 R17 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x36120] (SCR [] []) constr:(car13_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x36198.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x36120] (SCR [] []) constr:(car13_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x36198.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    replace (o + 4 + 4 * u + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - rewrite chunks_3 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x36120] (SCR [] []) constr:(car13_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x36198.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456 mod 268435456; c / 268435456 / 268435456])
      with (((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]) ++ [c / 268435456 / 268435456]) by (rewrite <- !app_assoc; reflexivity).
    replace (o + 4 + 4 * u + 8) with (o + 4 + 4 * Z.of_nat (length ((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]))) by (rewrite !length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite !length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation cartb_pins := [(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (14%bv : reg, ZV 34); (5%bv : reg, ZV 35); (17%bv : reg, ZV 36);
                            (6%bv : reg, ZL 128); (13%bv : reg, ZL 268435455); (16%bv : reg, ZSub (ZL 18446744073709551611) (ZV 32))].
Definition cartb_keep : list Z := [1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 13; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma cartb_U : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 u -> getr regs 14%bv = Z_to_bv 64 c ->
  getr regs 5%bv = Z_to_bv 64 (o + 4 + 4 * u) -> getr regs 17%bv = Z_to_bv 64 (4 * u) ->
  getr regs 6%bv = Z_to_bv 64 128 -> getr regs 13%bv = Z_to_bv 64 MASK -> getr regs 16%bv = Z_to_bv 64 (18446744073709551611 - o) ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> 0 <= o -> o + 516 <= 2 ^ 62 ->
  arr32 SEGS_U m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x36384) m rom) (mkst regs' (Z_to_bv 64 0x36280) m' rom)
    /\ arr32 SEGS_U m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_U m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 12%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps cartb_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R12 RC RP R8 R128 R13 R17 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x36280] (SCR [] []) constr:(cartb_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x36384.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x36280] (SCR [] []) constr:(cartb_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x36384.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    replace (o + 4 + 4 * u + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - rewrite chunks_3 by (unfold B; lia). unfold B.
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62); Some (0, 496)]) (@nil kcell) [KW (ZV 32) 0 516])
      50%nat [0x36280] (SCR [] []) constr:(cartb_pins) [o; u; c; o + 4 + 4 * u; 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62); Some (0, 496)]) regs m rom 0x36384.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456 mod 268435456; c / 268435456 / 268435456])
      with (((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]) ++ [c / 268435456 / 268435456]) by (rewrite <- !app_assoc; reflexivity).
    replace (o + 4 + 4 * u + 8) with (o + 4 + 4 * Z.of_nat (length ((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]))) by (rewrite !length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite !length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u + 4) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation mshL_pins :=
  [(6%bv : reg, ZV 32); (16%bv : reg, ZV 33); (5%bv : reg, ZV 34); (11%bv : reg, ZV 35); (15%bv : reg, ZV 36); (13%bv : reg, ZL 268435455)].
Abbreviation mshL_uvi :=
  [Some (0, 2 ^ 63); Some (0, 2 ^ 63); Some (0, 2 ^ 27); Some (0, 27); Some (1, 28); Some (0, 2 ^ 28 - 1)].
Abbreviation mshL_ctx := (CTX (vi_regs ++ mshL_uvi) [KC (ZV 32) 0 4 (ZV 37)] [KW (ZV 32) 0 4]).
Definition mshL_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].

Ltac obls ZXB Hcell Hst :=
  zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
    ltac:(kc1 Hcell; exact I)
    ltac:(kw1 Hst; exact I)
    ltac:(split; [lia | exact I]).

#[using="Type"] Lemma mshl_loop_U : forall t done c regs m (A s : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 6%bv = Z_to_bv 64 p -> getr regs 16%bv = Z_to_bv 64 pend ->
  getr regs 5%bv = Z_to_bv 64 c -> getr regs 11%bv = Z_to_bv 64 s -> getr regs 15%bv = Z_to_bv 64 (28 - s) -> getr regs 13%bv = Z_to_bv 64 MASK ->
  0 <= s < 28 -> 0 <= c < 2 ^ s -> ok t -> t <> [] ->
  0 <= A -> pend + 8 <= 2 ^ 63 ->
  arr32 SEGS_U m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x362fc) m rom) (mkst regs' (Z_to_bv 64 0x3631c) m' rom)
    /\ arr32 SEGS_U m' A (done ++ fst (shl_l s c t))
    /\ getr regs' 5%bv = Z_to_bv 64 (snd (shl_l s c t))
    /\ getr regs' 16%bv = Z_to_bv 64 pend
    /\ keeps mshL_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A s p pend R14 R11 R13 R15 R16 RM Hs Hc Hok Hne HA Hpe Harr Hst; [congruence|]. unfold MASK in RM.
  apply ok_cons in Hok as [Hx Hok]. cbn [length] in pend.
  assert (Hcell : exists bs, rdn SEGS_U m (Z_to_bv 64 p) 4 = Some bs /\ bytes_le_to_Z bs = x).
  { eapply kc_of_arr32; [exact Harr | unfold p; lia]. }
  pose proof (shl_step x c s Hx Hs Hc) as [Hdiv Hnc].
  cbn [shl_l]. destruct (shl_l s (x / 2 ^ (28 - s)) t) as [r c'] eqn:Hrec. cbn [fst snd].
  assert (Hs27 : 2 ^ s <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia).
  destruct t as [|y t'].
  - (* [comment removed for export] *)
    zx_run SEGS_U constr:(mshL_ctx) 20%nat (@nil Z) (SCR [false] []) constr:(mshL_pins) [p; pend; c; s; 28 - s; x] constr:(mshL_uvi) regs m rom 0x362fc.
    unfold p, pend in *. cbn [length] in *. obls ZXB Hcell Hst.
    
    cbn in Hrec. injection Hrec as <- <-.
    zx_reg ZR (5%bv : reg) as R13'. zx_reg ZR (16%bv : reg) as R11'.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [exact R13'|split; [rewrite R11'; f_equal; lia|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. unfold B. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - (* [comment removed for export] *)
    zx_run SEGS_U constr:(mshL_ctx) 20%nat (@nil Z) (SCR [true] []) constr:(mshL_pins) [p; pend; c; s; 28 - s; x] constr:(mshL_uvi) regs m rom 0x362fc.
    unfold p, pend in *. cbn [length] in *. obls ZXB Hcell Hst.
    
    zx_reg ZR (5%bv : reg) as R13'. zx_reg ZR (16%bv : reg) as R11'. zx_reg ZR (6%bv : reg) as R14'.
    zx_reg ZR (11%bv : reg) as R15'. zx_reg ZR (15%bv : reg) as R16'.
    set (m1 := wbytes m _ _) in ZM.
    assert (Harr1 : arr32 SEGS_U m1 A ((done ++ [(x * 2 ^ s + c) mod B]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold B. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia. }
    specialize (IH (done ++ [(x * 2 ^ s + c) mod B]) (x / 2 ^ (28 - s)) regs0 m1 A s).
    rewrite length_app in IH. cbn [length] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & R13'' & R11'' & K2 & U2 & G2).
    + rewrite R14'. f_equal. lia.
    + rewrite R11'. f_equal. lia.
    + exact R13'.
    + exact R15'.
    + exact R16'.
    + unfold MASK; zx_regv ZR.
    + lia.
    + exact Hnc.
    + exact Hok.
    + congruence.
    + lia.
    + cbn [length]. lia.
    + exact Harr1.
    + (* [comment removed for export] *)
      unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply (store_ok_sub SEGS_U m (Z_to_bv 64 p)); try exact Hst;
        rewrite ?u_Z2bv64, ?Z.mod_small; cbn [length]; try lia.
    + rewrite Hrec in *. cbn [fst snd] in *.
      eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [rewrite <- app_assoc in Harr2; exact Harr2|].
      split; [exact R13''|]. split; [rewrite R11''; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

End S.
