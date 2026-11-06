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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Ltac loop_obls ZXB Hcell Hst OSH g :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 Hcell; kcsh OSH g; exact I) ltac:(kw1 Hst; exact I) ltac:(zx_lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation m64_pins := [(12%bv : reg, ZV 32); (8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (31%bv : reg, ZV 34);
                          (6%bv : reg, ZL 4195354525); (7%bv : reg, ZL 27755575600); (15%bv : reg, ZL 268435455); (13%bv : reg, ZL SHA)].
Abbreviation m64_uvi clo chi := [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 63 - 1); Some (0, 2 ^ 28 - 1)].
Definition m64_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 10; 11; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30].

#[using="Type"] Lemma mul64_loop_A : forall t done c regs m (A : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 12%bv = Z_to_bv 64 p -> getr regs 8%bv = Z_to_bv 64 p -> getr regs 9%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 31%bv = Z_to_bv 64 c ->
  getr regs 6%bv = Z_to_bv 64 kFive27_lo -> getr regs 7%bv = Z_to_bv 64 (kFive27_hi * 16) -> getr regs 15%bv = Z_to_bv 64 MASK ->
  getr regs 13%bv = Z_to_bv 64 SHA ->
  0 <= c < 2 ^ 63 -> ok t -> t <> [] ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objsh m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 126 ->
  arr32 SEGS_A m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa6cc) m rom) (mkst regs' (Z_to_bv 64 0x0aa730) m' rom)
    /\ arr32 SEGS_A m' A (done ++ fst (mul64_l kFive27_lo kFive27_hi c t))
    /\ getr regs' 31%bv = Z_to_bv 64 (snd (mul64_l kFive27_lo kFive27_hi c t))
    /\ keeps m64_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A p pend RP RP' RN RC R6 R7 R15 R13 Hc Hok Hne HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok]. cbn [length] in *.
  assert (Hcell : exists bs, rdn SEGS_A m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul64_step_bounds x c Hx Hc) as SB. cbn zeta in SB. destruct SB as (Htmp & Hc' & Hmid & Hcd & Htd).
  cbn [mul64_l]. destruct (mul64_l kFive27_lo kFive27_hi (c / B + (c mod B + kFive27_lo * x) / B + kFive27_hi * x * 16) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold kFive27_lo, kFive27_hi, MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_A constr:(CTX (vi_regs ++ m64_uvi 1 1) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 30%nat [0x0aa6cc; 0x0aa730] (SCR [] [])
      constr:(m64_pins) [A + 4 * Z.of_nat (length done); 1; c; x] constr:(m64_uvi 1 1) regs m rom 0x0aa6cc.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [etransitivity; [zx_regv ZR|]; f_equal; lia|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - zx_run SEGS_A constr:(CTX (vi_regs ++ m64_uvi 2 128) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 30%nat [0x0aa6cc; 0x0aa730] (SCR [] [])
      constr:(m64_pins) [A + 4 * Z.of_nat (length done); Z.of_nat (S (S (length t'))); c; x] constr:(m64_uvi 2 128) regs m rom 0x0aa6cc.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (c mod 268435456 + 4195354525 * x) mod 268435456).
    assert (Harr1 : arr32 SEGS_A m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) (c / 268435456 + (c mod 268435456 + 4195354525 * x) / 268435456 + 1734723475 * x * 16) regs1 m1 A).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & C31 & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | exact Hok | congruence | lia | lia | lia | | lia | exact Harr1 | | ].
    { unfold m1. eapply (objsh_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
        [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact C31|].
    split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
    split.
    + apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
      intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
    + apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation m13_pins := [(12%bv : reg, ZV 32); (31%bv : reg, ZV 32); (8%bv : reg, ZV 33); (30%bv : reg, ZV 34);
                          (6%bv : reg, ZV 36); (15%bv : reg, ZL 268435455); (13%bv : reg, ZL SHA)].
Abbreviation m13_uvi clo chi := [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 32); Some (0, 2 ^ 28 - 1); Some (2, 2 ^ 31 - 1)].
Definition m13_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29].

#[using="Type"] Lemma m13_loop_A : forall t done c regs m (A F : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 12%bv = Z_to_bv 64 p -> getr regs 31%bv = Z_to_bv 64 p -> getr regs 8%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 30%bv = Z_to_bv 64 c ->
  getr regs 6%bv = Z_to_bv 64 F -> getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 13%bv = Z_to_bv 64 SHA ->
  2 <= F < 2 ^ 31 -> 0 <= c <= F -> ok t -> t <> [] ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objsh m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 126 ->
  arr32 SEGS_A m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m' tmp,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa800) m rom) (mkst regs' (Z_to_bv 64 0x0aa84c) m' rom)
    /\ arr32 SEGS_A m' A (done ++ fst (mul32_l F c t))
    /\ getr regs' 30%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 9%bv = Z_to_bv 64 tmp /\ tmp / 2 ^ 28 = snd (mul32_l F c t) /\ 0 <= tmp < 2 ^ 60
    /\ keeps m13_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A F p pend RP RP' RN RC RF R15 R13 HF Hc Hok Hne HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok].
  assert (Hcell : exists bs, rdn SEGS_A m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul32_step_bounds F x c ltac:(lia) Hx Hc) as (Hp1 & Hp2 & Hp3).
  cbn [mul32_l]. destruct (mul32_l F ((F * x + c) / B) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_A constr:(CTX (vi_regs ++ m13_uvi 1 1) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 30%nat [0x0aa800; 0x0aa84c] (SCR [] [])
      constr:(m13_pins) [A + 4 * Z.of_nat (length done); 1; c; x; F] constr:(m13_uvi 1 1) regs m rom 0x0aa800.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _, (x * F + c). split; [exact ZM|].
    split.
    { apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|].
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|].
    split; [f_equal; lia|]. split; [nia|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]].
  - zx_run SEGS_A constr:(CTX (vi_regs ++ m13_uvi 2 128) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 30%nat [0x0aa800; 0x0aa84c] (SCR [] [])
      constr:(m13_pins) [A + 4 * Z.of_nat (length done); Z.of_nat (S (S (length t'))); c; x; F] constr:(m13_uvi 2 128) regs m rom 0x0aa800.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (F * x + c) mod 268435456).
    assert (Harr1 : arr32 SEGS_A m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) ((F * x + c) / 268435456) regs1 m1 A F).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & tmp & M2 & Harr2 & COUT & CT & HT1 & HT2 & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | lia | exact Hok | congruence | lia | lia | lia | | lia | exact Harr1 | | ].
    { unfold m1. eapply (objsh_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
        [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2, tmp. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact COUT|]. split; [exact CT|]. split; [exact HT1|]. split; [exact HT2|].
    split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
    split.
    + apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
      intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
    + apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation mtb_pins := [(12%bv : reg, ZV 32); (5%bv : reg, ZV 32); (7%bv : reg, ZV 33); (17%bv : reg, ZV 34);
                          (6%bv : reg, ZV 36); (15%bv : reg, ZL 268435455); (13%bv : reg, ZL SHA)].
Abbreviation mtb_uvi clo chi := [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 32); Some (0, 2 ^ 28 - 1); Some (2, 2 ^ 31 - 1)].
Definition mtb_keep : list Z := [1; 2; 3; 4; 6; 8; 9; 10; 11; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].

#[using="Type"] Lemma mtb_loop_A : forall t done c regs m (A F : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 12%bv = Z_to_bv 64 p -> getr regs 5%bv = Z_to_bv 64 p -> getr regs 7%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 17%bv = Z_to_bv 64 c ->
  getr regs 6%bv = Z_to_bv 64 F -> getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 13%bv = Z_to_bv 64 SHA ->
  2 <= F < 2 ^ 31 -> 0 <= c <= F -> ok t -> t <> [] ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objsh m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 126 ->
  arr32 SEGS_A m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m' tmp,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa950) m rom) (mkst regs' (Z_to_bv 64 0x0aa9a0) m' rom)
    /\ arr32 SEGS_A m' A (done ++ fst (mul32_l F c t))
    /\ getr regs' 17%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 28%bv = Z_to_bv 64 tmp /\ tmp / 2 ^ 28 = snd (mul32_l F c t) /\ 0 <= tmp < 2 ^ 60
    /\ keeps mtb_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A F p pend RP RP' RN RC RF R15 R13 HF Hc Hok Hne HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok].
  assert (Hcell : exists bs, rdn SEGS_A m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul32_step_bounds F x c ltac:(lia) Hx Hc) as (Hp1 & Hp2 & Hp3).
  cbn [mul32_l]. destruct (mul32_l F ((F * x + c) / B) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_A constr:(CTX (vi_regs ++ mtb_uvi 1 1) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 30%nat [0x0aa950; 0x0aa9a0] (SCR [] [])
      constr:(mtb_pins) [A + 4 * Z.of_nat (length done); 1; c; x; F] constr:(mtb_uvi 1 1) regs m rom 0x0aa950.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _, (x * F + c). split; [exact ZM|].
    split.
    { apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|].
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|].
    split; [f_equal; lia|]. split; [nia|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]].
  - zx_run SEGS_A constr:(CTX (vi_regs ++ mtb_uvi 2 128) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 30%nat [0x0aa950; 0x0aa9a0] (SCR [] [])
      constr:(mtb_pins) [A + 4 * Z.of_nat (length done); Z.of_nat (S (S (length t'))); c; x; F] constr:(mtb_uvi 2 128) regs m rom 0x0aa950.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (F * x + c) mod 268435456).
    assert (Harr1 : arr32 SEGS_A m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) ((F * x + c) / 268435456) regs1 m1 A F).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & tmp & M2 & Harr2 & COUT & CT & HT1 & HT2 & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | lia | exact Hok | congruence | lia | lia | lia | | lia | exact Harr1 | | ].
    { unfold m1. eapply (objsh_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
        [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2, tmp. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact COUT|]. split; [exact CT|]. split; [exact HT1|]. split; [exact HT2|].
    split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
    split.
    + apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
      intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
    + apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation mshL_pins :=
  [(11%bv : reg, ZV 32); (7%bv : reg, ZV 32); (28%bv : reg, ZV 33); (5%bv : reg, ZV 34); (17%bv : reg, ZV 35);
   (6%bv : reg, ZV 36); (15%bv : reg, ZL 268435455); (13%bv : reg, ZL SHA)].
Abbreviation mshL_uvi clo chi :=
  [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 27); Some (0, 27); Some (1, 28); Some (0, 2 ^ 28 - 1)].
Abbreviation mshL_ctx clo chi :=
  (CTX (vi_regs ++ mshL_uvi clo chi) [KC (ZV 32) 0 4 (ZV 37); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]).
Definition mshL_keep : list Z := [1; 2; 3; 4; 6; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31].

#[using="Type"] Lemma mshl_loop_A : forall t done c regs m (A s : Z),
  let p := A + 4 * Z.of_nat (length done) in
  getr regs 11%bv = Z_to_bv 64 p -> getr regs 7%bv = Z_to_bv 64 p -> getr regs 28%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 5%bv = Z_to_bv 64 c -> getr regs 17%bv = Z_to_bv 64 s -> getr regs 6%bv = Z_to_bv 64 (28 - s) ->
  getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 13%bv = Z_to_bv 64 SHA ->
  0 <= s < 28 -> 0 <= c < 2 ^ s -> ok t -> t <> [] ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objsh m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 127 ->
  arr32 SEGS_A m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aaa38) m rom) (mkst regs' (Z_to_bv 64 0x0aaa8c) m' rom)
    /\ arr32 SEGS_A m' A (done ++ fst (shl_l s c t))
    /\ getr regs' 29%bv = Z_to_bv 64 (snd (shl_l s c t))
    /\ keeps mshL_keep regs regs'
    /\ unch m m' [(p, p + 4 * Z.of_nat (length t))] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A s p R11 R7 R28 R5 R17 R6 R15 R13 Hs Hc Hok Hne HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  unfold MASK in R15.
  apply ok_cons in Hok as [Hx Hok]. cbn [length] in R28, Hlen, Hst |- *.
  assert (Hcell : exists bs, rdn SEGS_A m (Z_to_bv 64 p) 4 = Some bs /\ bytes_le_to_Z bs = x).
  { eapply kc_of_arr32; [exact Harr | unfold p; lia]. }
  pose proof (shl_step x c s Hx Hs Hc) as [Hdiv Hnc].
  cbn [shl_l]. destruct (shl_l s (x / 2 ^ (28 - s)) t) as [r c'] eqn:Hrec. cbn [fst snd].
  assert (Hs27 : 2 ^ s <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia).
  destruct t as [|y t'].
  - cbn [length Z.of_nat] in *.
    zx_run SEGS_A constr:(mshL_ctx 1 1) 30%nat [0x0aaa38; 0x0aaa8c] (SCR [] []) constr:(mshL_pins) [p; 1; c; s; 28 - s; x]
           constr:(mshL_uvi 1 1) regs m rom 0x0aaa38.
    unfold p in *.
    zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
      ltac:(kc1 Hcell; kcsh OSH ((4 + 4 * Z.of_nat (length done)) / 8); exact I)
      ltac:(kw1 Hst; exact I) ltac:(exact I).
    cbn in Hrec. injection Hrec as <- <-.
    zx_reg ZR (29%bv : reg) as R29'.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [exact R29'|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. unfold B. change (2 ^ 28) with 268435456. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - cbn [length] in *.
    zx_run SEGS_A constr:(mshL_ctx 2 128) 30%nat [0x0aaa38; 0x0aaa8c] (SCR [] []) constr:(mshL_pins)
           [p; Z.of_nat (S (S (length t'))); c; s; 28 - s; x] constr:(mshL_uvi 2 128) regs m rom 0x0aaa38.
    unfold p in *.
    zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
      ltac:(kc1 Hcell; kcsh OSH ((4 + 4 * Z.of_nat (length done)) / 8); exact I)
      ltac:(kw1 Hst; exact I) ltac:(exact I).
    zx_reg ZR (5%bv : reg) as R5'. zx_reg ZR (28%bv : reg) as R28'. zx_reg ZR (11%bv : reg) as R11'.
    zx_reg ZR (7%bv : reg) as R7'. zx_reg ZR (17%bv : reg) as R17'. zx_reg ZR (6%bv : reg) as R6'. zx_reg ZR (15%bv : reg) as R15'.
    zx_reg ZR (13%bv : reg) as R13'.
    set (m1 := wbytes m _ _) in ZM.
    assert (Harr1 : arr32 SEGS_A m1 A ((done ++ [(x * 2 ^ s + c) mod B]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold B. change (2 ^ 28) with 268435456. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia. }
    specialize (IH (done ++ [(x * 2 ^ s + c) mod B]) (x / 2 ^ (28 - s)) regs0 m1 A s).
    rewrite length_app in IH. cbn [length] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & R29'' & K2 & U2 & G2).
    + rewrite R11'. f_equal. lia.
    + rewrite R7'. f_equal. lia.
    + rewrite R28'. f_equal. lia.
    + exact R5'.
    + exact R17'.
    + exact R6'.
    + rewrite R15'. reflexivity.
    + exact R13'.
    + lia.
    + exact Hnc.
    + exact Hok.
    + congruence.
    + lia.
    + lia.
    + lia.
    + unfold m1. eapply (objsh_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
        [unchx| intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH].
    + lia.
    + exact Harr1.
    + unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply (store_ok_sub SEGS_A m (Z_to_bv 64 p)); try exact Hst;
        rewrite ?u_Z2bv64, ?Z.mod_small; cbn [length]; try lia.
    + rewrite Hrec in *. cbn [fst snd] in *.
      eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [rewrite <- app_assoc in Harr2; exact Harr2|].
      split; [exact R29''|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

End S.
