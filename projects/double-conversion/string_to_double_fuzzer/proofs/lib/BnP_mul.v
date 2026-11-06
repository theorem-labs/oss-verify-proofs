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
Ltac loop_obls ZXB Hcell Hst :=
  zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 Hcell; exact I) ltac:(kw1 Hst; exact I) ltac:(zx_lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation m64_pins := [(29%bv : reg, ZV 32); (7%bv : reg, ZV 33); (28%bv : reg, ZV 34);
                          (16%bv : reg, ZL 4195354525); (17%bv : reg, ZL 27755575600); (13%bv : reg, ZL 268435455)].
Abbreviation m64_uvi := [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 2 ^ 63 - 1); Some (0, 2 ^ 28 - 1)].
Definition m64_keep : list Z := [1; 2; 3; 4; 5; 6; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma mul64_loop_P : forall t done c regs m (A : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 29%bv = Z_to_bv 64 p -> getr regs 7%bv = Z_to_bv 64 pend -> getr regs 28%bv = Z_to_bv 64 c ->
  getr regs 16%bv = Z_to_bv 64 kFive27_lo -> getr regs 17%bv = Z_to_bv 64 (kFive27_hi * 16) -> getr regs 13%bv = Z_to_bv 64 MASK ->
  0 <= c < 2 ^ 63 -> ok t -> t <> [] -> 0 <= A -> pend + 8 <= 2 ^ 62 ->
  arr32 SEGS_P m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35b80) m rom) (mkst regs' (Z_to_bv 64 0x35bb8) m' rom)
    /\ arr32 SEGS_P m' A (done ++ fst (mul64_l kFive27_lo kFive27_hi c t))
    /\ getr regs' 28%bv = Z_to_bv 64 (snd (mul64_l kFive27_lo kFive27_hi c t))
    /\ getr regs' 7%bv = Z_to_bv 64 pend
    /\ keeps m64_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A p pend R29 R7 R28 R16 R17 R13 Hc Hok Hne HA Hpe Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok]. cbn [length] in *.
  assert (Hcell : exists bs, rdn SEGS_P m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul64_step_bounds x c Hx Hc) as SB. cbn zeta in SB. destruct SB as (Htmp & Hc' & Hmid & Hcd & Htd).
  cbn [mul64_l]. destruct (mul64_l kFive27_lo kFive27_hi (c / B + (c mod B + kFive27_lo * x) / B + kFive27_hi * x * 16) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold kFive27_lo, kFive27_hi, MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ m64_uvi) [KC (ZV 32) 0 4 (ZV 35)] [KW (ZV 32) 0 4]) 25%nat (@nil Z) (SCR [false] [])
      constr:(m64_pins) [A + 4 * Z.of_nat (length done); A + 4 * Z.of_nat (length done) + 4 * Z.of_nat 1; c; x] constr:(m64_uvi) regs m rom 0x35b80.
    loop_obls ZXB Hcell Hst. zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [zx_regv ZR|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ m64_uvi) [KC (ZV 32) 0 4 (ZV 35)] [KW (ZV 32) 0 4]) 25%nat (@nil Z) (SCR [true] [])
      constr:(m64_pins) [A + 4 * Z.of_nat (length done); A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (S (S (length t'))); c; x] constr:(m64_uvi) regs m rom 0x35b80.
    loop_obls ZXB Hcell Hst. zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (c mod 268435456 + 4195354525 * x) mod 268435456).
    assert (Harr1 : arr32 SEGS_P m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) (c / 268435456 + (c mod 268435456 + 4195354525 * x) / 268435456 + 1734723475 * x * 16) regs1 m1 A).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & C28 & C7 & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | exact Hok | congruence | lia | lia | exact Harr1 | | ].
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact C28|]. split; [rewrite C7; f_equal; lia|].
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
Abbreviation m13_pins := [(28%bv : reg, ZV 32); (6%bv : reg, ZV 33); (7%bv : reg, ZV 34); (16%bv : reg, ZV 36); (13%bv : reg, ZL 268435455)].
Abbreviation m13_uvi := [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 2 ^ 32); Some (0, 2 ^ 28 - 1); Some (2, 2 ^ 31 - 1)].
Definition m13_keep : list Z := [1; 2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 30; 31].

#[using="Type"] Lemma m13_loop_P : forall t done c regs m (A F : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 28%bv = Z_to_bv 64 p -> getr regs 6%bv = Z_to_bv 64 pend -> getr regs 7%bv = Z_to_bv 64 c ->
  getr regs 16%bv = Z_to_bv 64 F -> getr regs 13%bv = Z_to_bv 64 MASK ->
  2 <= F < 2 ^ 31 -> 0 <= c <= F -> ok t -> t <> [] -> 0 <= A -> pend + 8 <= 2 ^ 62 ->
  arr32 SEGS_P m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35c34) m rom) (mkst regs' (Z_to_bv 64 0x35c58) m' rom)
    /\ arr32 SEGS_P m' A (done ++ fst (mul32_l F c t))
    /\ getr regs' 28%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 7%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 6%bv = Z_to_bv 64 pend
    /\ keeps m13_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A F p pend RP RE RC RF R13 HF Hc Hok Hne HA Hpe Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok].
  assert (Hcell : exists bs, rdn SEGS_P m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul32_step_bounds F x c ltac:(lia) Hx Hc) as (Hp1 & Hp2 & Hp3).
  cbn [mul32_l]. destruct (mul32_l F ((F * x + c) / B) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ m13_uvi) [KC (ZV 32) 0 4 (ZV 35)] [KW (ZV 32) 0 4]) 25%nat (@nil Z) (SCR [false] [])
      constr:(m13_pins) [A + 4 * Z.of_nat (length done); A + 4 * Z.of_nat (length done) + 4 * Z.of_nat 1; c; x; F] constr:(m13_uvi) regs m rom 0x35c34.
    loop_obls ZXB Hcell Hst. zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [zx_regv ZR|split; [zx_regv ZR|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ m13_uvi) [KC (ZV 32) 0 4 (ZV 35)] [KW (ZV 32) 0 4]) 25%nat [0x35c34] (SCR [true] [])
      constr:(m13_pins) [A + 4 * Z.of_nat (length done); A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (S (S (length t'))); c; x; F] constr:(m13_uvi) regs m rom 0x35c34.
    loop_obls ZXB Hcell Hst. zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (F * x + c) mod 268435456).
    assert (Harr1 : arr32 SEGS_P m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) ((F * x + c) / 268435456) regs1 m1 A F).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & COUT & CC & CE & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | lia | exact Hok | congruence | lia | lia | exact Harr1 | | ].
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact COUT|]. split; [exact CC|]. split; [rewrite CE; f_equal; lia|].
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
Abbreviation mtb_pins := [(16%bv : reg, ZV 32); (5%bv : reg, ZV 33); (14%bv : reg, ZV 34); (17%bv : reg, ZV 36); (13%bv : reg, ZL 268435455)].
Abbreviation mtb_uvi := [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 2 ^ 32); Some (0, 2 ^ 28 - 1); Some (2, 2 ^ 31 - 1)].
Definition mtb_keep : list Z := [1; 2; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma mtb_loop_P : forall t done c regs m (A F : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 16%bv = Z_to_bv 64 p -> getr regs 5%bv = Z_to_bv 64 pend -> getr regs 14%bv = Z_to_bv 64 c ->
  getr regs 17%bv = Z_to_bv 64 F -> getr regs 13%bv = Z_to_bv 64 MASK ->
  2 <= F < 2 ^ 31 -> 0 <= c <= F -> ok t -> t <> [] -> 0 <= A -> pend + 8 <= 2 ^ 62 ->
  arr32 SEGS_P m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35ce4) m rom) (mkst regs' (Z_to_bv 64 0x35d08) m' rom)
    /\ arr32 SEGS_P m' A (done ++ fst (mul32_l F c t))
    /\ getr regs' 16%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 14%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 5%bv = Z_to_bv 64 pend
    /\ keeps mtb_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A F p pend RP RE RC RF R13 HF Hc Hok Hne HA Hpe Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok].
  assert (Hcell : exists bs, rdn SEGS_P m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul32_step_bounds F x c ltac:(lia) Hx Hc) as (Hp1 & Hp2 & Hp3).
  cbn [mul32_l]. destruct (mul32_l F ((F * x + c) / B) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ mtb_uvi) [KC (ZV 32) 0 4 (ZV 35)] [KW (ZV 32) 0 4]) 25%nat (@nil Z) (SCR [false] [])
      constr:(mtb_pins) [A + 4 * Z.of_nat (length done); A + 4 * Z.of_nat (length done) + 4 * Z.of_nat 1; c; x; F] constr:(mtb_uvi) regs m rom 0x35ce4.
    loop_obls ZXB Hcell Hst. zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [zx_regv ZR|split; [zx_regv ZR|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ mtb_uvi) [KC (ZV 32) 0 4 (ZV 35)] [KW (ZV 32) 0 4]) 25%nat [0x35ce4] (SCR [true] [])
      constr:(mtb_pins) [A + 4 * Z.of_nat (length done); A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (S (S (length t'))); c; x; F] constr:(mtb_uvi) regs m rom 0x35ce4.
    loop_obls ZXB Hcell Hst. zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (F * x + c) mod 268435456).
    assert (Harr1 : arr32 SEGS_P m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) ((F * x + c) / 268435456) regs1 m1 A F).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & COUT & CC & CE & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | lia | exact Hok | congruence | lia | lia | exact Harr1 | | ].
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact COUT|]. split; [exact CC|]. split; [rewrite CE; f_equal; lia|].
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
Abbreviation car64_pins := [(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (28%bv : reg, ZV 34); (7%bv : reg, ZV 35);
                            (15%bv : reg, ZL 128); (13%bv : reg, ZL 268435455)].
Definition car64_keep : list Z := [1; 2; 3; 4; 5; 6; 8; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 30; 31].

#[using="Type"] Lemma car64_P : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 u -> getr regs 28%bv = Z_to_bv 64 c ->
  getr regs 7%bv = Z_to_bv 64 (o + 4 + 4 * u) -> getr regs 15%bv = Z_to_bv 64 128 -> getr regs 13%bv = Z_to_bv 64 MASK ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> 0 <= o -> o + 516 <= 2 ^ 62 ->
  arr32 SEGS_P m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35bbc) m rom) (mkst regs' (Z_to_bv 64 0x35b58) m' rom)
    /\ arr32 SEGS_P m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_P m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 12%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps car64_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R12 RC RP R128 R13 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35b58] (SCR [] []) constr:(car64_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62)]) regs m rom 0x35bbc.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35b58] (SCR [] []) constr:(car64_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62)]) regs m rom 0x35bbc.
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
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35b58] (SCR [] []) constr:(car64_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62)]) regs m rom 0x35bbc.
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
Abbreviation car13_pins := [(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (7%bv : reg, ZV 34); (6%bv : reg, ZV 35);
                            (15%bv : reg, ZL 128); (13%bv : reg, ZL 268435455)].
Definition car13_keep : list Z := [1; 2; 3; 4; 5; 8; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].

#[using="Type"] Lemma car13_P : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 u -> getr regs 7%bv = Z_to_bv 64 c ->
  getr regs 6%bv = Z_to_bv 64 (o + 4 + 4 * u) -> getr regs 15%bv = Z_to_bv 64 128 -> getr regs 13%bv = Z_to_bv 64 MASK ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> 0 <= o -> o + 516 <= 2 ^ 62 ->
  arr32 SEGS_P m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35c5c) m rom) (mkst regs' (Z_to_bv 64 0x35c0c) m' rom)
    /\ arr32 SEGS_P m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_P m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 12%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps car13_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R12 RC RP R128 R13 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35c0c] (SCR [] []) constr:(car13_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62)]) regs m rom 0x35c5c.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35c0c] (SCR [] []) constr:(car13_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62)]) regs m rom 0x35c5c.
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
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35c0c] (SCR [] []) constr:(car13_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62)]) regs m rom 0x35c5c.
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
Abbreviation cartb_pins := [(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (14%bv : reg, ZV 34); (15%bv : reg, ZV 35);
                            (16%bv : reg, ZL 128); (13%bv : reg, ZL 268435455)].
Definition cartb_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma cartb_P : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 u -> getr regs 14%bv = Z_to_bv 64 c ->
  getr regs 15%bv = Z_to_bv 64 (o + 4 + 4 * u) -> getr regs 16%bv = Z_to_bv 64 128 -> getr regs 13%bv = Z_to_bv 64 MASK ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> 0 <= o -> o + 516 <= 2 ^ 62 ->
  arr32 SEGS_P m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35dc4) m rom) (mkst regs' (Z_to_bv 64 0x35d10) m' rom)
    /\ arr32 SEGS_P m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_P m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 12%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps cartb_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 R12 RC RP R128 R13 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35d10] (SCR [] []) constr:(cartb_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (0, 2 ^ 62)]) regs m rom 0x35dc4.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])). zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellx|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35d10] (SCR [] []) constr:(cartb_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (0, 2 ^ 62)]) regs m rom 0x35dc4.
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
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62)]) (@nil kcell) [KW (ZV 32) 0 516])
      40%nat [0x35d10] (SCR [] []) constr:(cartb_pins) [o; u; c; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (0, 124); Some (2 ^ 56, 2 ^ 63); Some (0, 2 ^ 62)]) regs m rom 0x35dc4.
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
  [(15%bv : reg, ZV 32); (11%bv : reg, ZV 33); (14%bv : reg, ZV 34); (16%bv : reg, ZV 35); (17%bv : reg, ZV 36); (13%bv : reg, ZL 268435455)].
Abbreviation mshL_uvi :=
  [Some (0, 2 ^ 63); Some (0, 2 ^ 63); Some (0, 2 ^ 27); Some (0, 27); Some (1, 28); Some (0, 2 ^ 28 - 1)].
Abbreviation mshL_ctx := (CTX (vi_regs ++ mshL_uvi) [KC (ZV 32) 0 4 (ZV 37)] [KW (ZV 32) 0 4]).
Definition mshL_keep : list Z := [1; 2; 3; 4; 7; 8; 9; 10; 12; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

Ltac obls ZXB Hcell Hst :=
  zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
    ltac:(kc1 Hcell; exact I)
    ltac:(kw1 Hst; exact I)
    ltac:(split; [lia | exact I]).

#[using="Type"] Lemma mshl_loop_P : forall t done c regs m (A s : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 15%bv = Z_to_bv 64 p -> getr regs 11%bv = Z_to_bv 64 pend ->
  getr regs 14%bv = Z_to_bv 64 c -> getr regs 16%bv = Z_to_bv 64 s -> getr regs 17%bv = Z_to_bv 64 (28 - s) -> getr regs 13%bv = Z_to_bv 64 MASK ->
  0 <= s < 28 -> 0 <= c < 2 ^ s -> ok t -> t <> [] ->
  0 <= A -> pend + 8 <= 2 ^ 63 ->
  arr32 SEGS_P m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35d78) m rom) (mkst regs' (Z_to_bv 64 0x35d98) m' rom)
    /\ arr32 SEGS_P m' A (done ++ fst (shl_l s c t))
    /\ getr regs' 14%bv = Z_to_bv 64 (snd (shl_l s c t))
    /\ getr regs' 11%bv = Z_to_bv 64 pend
    /\ keeps mshL_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A s p pend R14 R11 R13 R15 R16 RM Hs Hc Hok Hne HA Hpe Harr Hst; [congruence|]. unfold MASK in RM.
  apply ok_cons in Hok as [Hx Hok]. cbn [length] in pend.
  assert (Hcell : exists bs, rdn SEGS_P m (Z_to_bv 64 p) 4 = Some bs /\ bytes_le_to_Z bs = x).
  { eapply kc_of_arr32; [exact Harr | unfold p; lia]. }
  pose proof (shl_step x c s Hx Hs Hc) as [Hdiv Hnc].
  cbn [shl_l]. destruct (shl_l s (x / 2 ^ (28 - s)) t) as [r c'] eqn:Hrec. cbn [fst snd].
  assert (Hs27 : 2 ^ s <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia).
  destruct t as [|y t'].
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(mshL_ctx) 20%nat (@nil Z) (SCR [false] []) constr:(mshL_pins) [p; pend; c; s; 28 - s; x] constr:(mshL_uvi) regs m rom 0x35d78.
    unfold p, pend in *. cbn [length] in *. obls ZXB Hcell Hst.
    
    cbn in Hrec. injection Hrec as <- <-.
    zx_reg ZR (14%bv : reg) as R13'. zx_reg ZR (11%bv : reg) as R11'.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [exact R13'|split; [rewrite R11'; f_equal; lia|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. unfold B. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(mshL_ctx) 20%nat (@nil Z) (SCR [true] []) constr:(mshL_pins) [p; pend; c; s; 28 - s; x] constr:(mshL_uvi) regs m rom 0x35d78.
    unfold p, pend in *. cbn [length] in *. obls ZXB Hcell Hst.
    
    zx_reg ZR (14%bv : reg) as R13'. zx_reg ZR (11%bv : reg) as R11'. zx_reg ZR (15%bv : reg) as R14'.
    zx_reg ZR (16%bv : reg) as R15'. zx_reg ZR (17%bv : reg) as R16'.
    set (m1 := wbytes m _ _) in ZM.
    assert (Harr1 : arr32 SEGS_P m1 A ((done ++ [(x * 2 ^ s + c) mod B]) ++ y :: t')).
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
      eapply (store_ok_sub SEGS_P m (Z_to_bv 64 p)); try exact Hst;
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
