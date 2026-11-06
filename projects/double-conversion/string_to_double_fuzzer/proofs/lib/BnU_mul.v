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
Abbreviation m64_pins := [(9%bv : reg, ZV 32); (18%bv : reg, ZV 33); (8%bv : reg, ZV 34); (30%bv : reg, ZV 35);
                          (6%bv : reg, ZL 4195354525); (7%bv : reg, ZL 27755575600); (13%bv : reg, ZL 268435455)].
Abbreviation m64_uvi := [Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 2 ^ 63 - 1); Some (0, 2 ^ 28 - 1)].
Definition m64_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 31].

#[using="Type"] Lemma mul64_loop_U : forall t done c regs m (A cnt : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 9%bv = Z_to_bv 64 p -> getr regs 18%bv = Z_to_bv 64 cnt -> getr regs 8%bv = Z_to_bv 64 (cnt - Z.of_nat (length t)) ->
  getr regs 30%bv = Z_to_bv 64 c ->
  getr regs 6%bv = Z_to_bv 64 kFive27_lo -> getr regs 7%bv = Z_to_bv 64 (kFive27_hi * 16) -> getr regs 13%bv = Z_to_bv 64 MASK ->
  0 <= c < 2 ^ 63 -> ok t -> t <> [] -> 0 <= A -> pend + 8 <= 2 ^ 62 -> cnt < 2 ^ 62 -> 0 <= cnt - Z.of_nat (length t) ->
  arr32 SEGS_U m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x36068) m rom) (mkst regs' (Z_to_bv 64 0x360a8) m' rom)
    /\ arr32 SEGS_U m' A (done ++ fst (mul64_l kFive27_lo kFive27_hi c t))
    /\ getr regs' 30%bv = Z_to_bv 64 (snd (mul64_l kFive27_lo kFive27_hi c t))
    /\ keeps m64_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A cnt p pend RP RN RS RC R6 R7 R13 Hc Hok Hne HA Hpe Hcnt Hstop Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok]. cbn [length] in *.
  assert (Hcell : exists bs, rdn SEGS_U m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul64_step_bounds x c Hx Hc) as SB. cbn zeta in SB. destruct SB as (Htmp & Hc' & Hmid & Hcd & Htd).
  cbn [mul64_l]. destruct (mul64_l kFive27_lo kFive27_hi (c / B + (c mod B + kFive27_lo * x) / B + kFive27_hi * x * 16) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold kFive27_lo, kFive27_hi, MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_U constr:(CTX (vi_regs ++ m64_uvi) [KC (ZV 32) 0 4 (ZV 36)] [KW (ZV 32) 0 4]) 25%nat (@nil Z) (SCR [false] [])
      constr:(m64_pins) [A + 4 * Z.of_nat (length done); cnt; cnt - Z.of_nat 1; c; x] constr:(m64_uvi) regs m rom 0x36068.
    loop_obls ZXB Hcell Hst. zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - zx_run SEGS_U constr:(CTX (vi_regs ++ m64_uvi) [KC (ZV 32) 0 4 (ZV 36)] [KW (ZV 32) 0 4]) 25%nat [0x36068] (SCR [true] [])
      constr:(m64_pins) [A + 4 * Z.of_nat (length done); cnt; cnt - Z.of_nat (S (S (length t'))); c; x] constr:(m64_uvi) regs m rom 0x36068.
    loop_obls ZXB Hcell Hst. zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (c mod 268435456 + 4195354525 * x) mod 268435456).
    assert (Harr1 : arr32 SEGS_U m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) (c / 268435456 + (c mod 268435456 + 4195354525 * x) / 268435456 + 1734723475 * x * 16) regs1 m1 A (cnt - 1)).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & C30 & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | exact Hok | congruence | lia | lia | lia | lia | exact Harr1 | | ].
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact C30|].
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
Abbreviation m13_pins := [(8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (31%bv : reg, ZV 34); (29%bv : reg, ZV 35);
                          (5%bv : reg, ZV 37); (13%bv : reg, ZL 268435455)].
Abbreviation m13_uvi := [Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 2 ^ 32); Some (0, 2 ^ 28 - 1); Some (2, 2 ^ 31 - 1)].
Definition m13_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 30].

#[using="Type"] Lemma m13_loop_U : forall t done c regs m (A F cnt : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 8%bv = Z_to_bv 64 p -> getr regs 9%bv = Z_to_bv 64 cnt -> getr regs 31%bv = Z_to_bv 64 (cnt - Z.of_nat (length t)) ->
  getr regs 29%bv = Z_to_bv 64 c ->
  getr regs 5%bv = Z_to_bv 64 F -> getr regs 13%bv = Z_to_bv 64 MASK ->
  2 <= F < 2 ^ 31 -> 0 <= c <= F -> ok t -> t <> [] -> 0 <= A -> pend + 8 <= 2 ^ 62 -> cnt < 2 ^ 62 -> 0 <= cnt - Z.of_nat (length t) ->
  arr32 SEGS_U m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x3615c) m rom) (mkst regs' (Z_to_bv 64 0x36188) m' rom)
    /\ arr32 SEGS_U m' A (done ++ fst (mul32_l F c t))
    /\ getr regs' 31%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 29%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ keeps m13_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A F cnt p pend RP RN RS RC RF R13 HF Hc Hok Hne HA Hpe Hcnt Hstop Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok].
  assert (Hcell : exists bs, rdn SEGS_U m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul32_step_bounds F x c ltac:(lia) Hx Hc) as (Hp1 & Hp2 & Hp3).
  cbn [mul32_l]. destruct (mul32_l F ((F * x + c) / B) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_U constr:(CTX (vi_regs ++ m13_uvi) [KC (ZV 32) 0 4 (ZV 36)] [KW (ZV 32) 0 4]) 25%nat (@nil Z) (SCR [false] [])
      constr:(m13_pins) [A + 4 * Z.of_nat (length done); cnt; cnt - Z.of_nat 1; c; x; F] constr:(m13_uvi) regs m rom 0x3615c.
    loop_obls ZXB Hcell Hst. zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [zx_regv ZR|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - zx_run SEGS_U constr:(CTX (vi_regs ++ m13_uvi) [KC (ZV 32) 0 4 (ZV 36)] [KW (ZV 32) 0 4]) 25%nat [0x3615c] (SCR [true] [])
      constr:(m13_pins) [A + 4 * Z.of_nat (length done); cnt; cnt - Z.of_nat (S (S (length t'))); c; x; F] constr:(m13_uvi) regs m rom 0x3615c.
    loop_obls ZXB Hcell Hst. zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (F * x + c) mod 268435456).
    assert (Harr1 : arr32 SEGS_U m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) ((F * x + c) / 268435456) regs1 m1 A F (cnt - 1)).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & COUT & CC & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | lia | exact Hok | congruence | lia | lia | lia | lia | exact Harr1 | | ].
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact COUT|]. split; [exact CC|].
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
Abbreviation mtb_pins := [(7%bv : reg, ZV 32); (16%bv : reg, ZV 33); (6%bv : reg, ZV 34); (14%bv : reg, ZV 35);
                          (5%bv : reg, ZV 37); (13%bv : reg, ZL 268435455)].
Abbreviation mtb_uvi := [Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 2 ^ 32); Some (0, 2 ^ 28 - 1); Some (2, 2 ^ 31 - 1)].
Definition mtb_keep : list Z := [1; 2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 13; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].

#[using="Type"] Lemma mtb_loop_U : forall t done c regs m (A F cnt : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 7%bv = Z_to_bv 64 p -> getr regs 16%bv = Z_to_bv 64 cnt -> getr regs 6%bv = Z_to_bv 64 (cnt - Z.of_nat (length t)) ->
  getr regs 14%bv = Z_to_bv 64 c ->
  getr regs 5%bv = Z_to_bv 64 F -> getr regs 13%bv = Z_to_bv 64 MASK ->
  2 <= F < 2 ^ 31 -> 0 <= c <= F -> ok t -> t <> [] -> 0 <= A -> pend + 8 <= 2 ^ 62 -> cnt < 2 ^ 62 -> 0 <= cnt - Z.of_nat (length t) ->
  arr32 SEGS_U m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x36248) m rom) (mkst regs' (Z_to_bv 64 0x36274) m' rom)
    /\ arr32 SEGS_U m' A (done ++ fst (mul32_l F c t))
    /\ getr regs' 16%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 14%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ keeps mtb_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A F cnt p pend RP RN RS RC RF R13 HF Hc Hok Hne HA Hpe Hcnt Hstop Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok].
  assert (Hcell : exists bs, rdn SEGS_U m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul32_step_bounds F x c ltac:(lia) Hx Hc) as (Hp1 & Hp2 & Hp3).
  cbn [mul32_l]. destruct (mul32_l F ((F * x + c) / B) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_U constr:(CTX (vi_regs ++ mtb_uvi) [KC (ZV 32) 0 4 (ZV 36)] [KW (ZV 32) 0 4]) 25%nat (@nil Z) (SCR [false] [])
      constr:(mtb_pins) [A + 4 * Z.of_nat (length done); cnt; cnt - Z.of_nat 1; c; x; F] constr:(mtb_uvi) regs m rom 0x36248.
    loop_obls ZXB Hcell Hst. zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [zx_regv ZR|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - zx_run SEGS_U constr:(CTX (vi_regs ++ mtb_uvi) [KC (ZV 32) 0 4 (ZV 36)] [KW (ZV 32) 0 4]) 25%nat [0x36248] (SCR [true] [])
      constr:(mtb_pins) [A + 4 * Z.of_nat (length done); cnt; cnt - Z.of_nat (S (S (length t'))); c; x; F] constr:(mtb_uvi) regs m rom 0x36248.
    loop_obls ZXB Hcell Hst. zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (F * x + c) mod 268435456).
    assert (Harr1 : arr32 SEGS_U m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) ((F * x + c) / 268435456) regs1 m1 A F (cnt - 1)).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & COUT & CC & K2 & U2 & G2);
      [ zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | lia | exact Hok | congruence | lia | lia | lia | lia | exact Harr1 | | ].
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact COUT|]. split; [exact CC|].
    split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
    split.
    + apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
      intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
    + apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.
End S.
