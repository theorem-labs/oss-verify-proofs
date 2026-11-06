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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnA_mul2 BnB_lib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac ptrchk :=
  lazymatch goal with
  | |- Z.lxor _ _ <> _ =>
      repeat match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b); [exfalso; lia|] end;
      vm_compute; discriminate
  end.

Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Ltac loop_obls ZXB Hcell Hst OSH g :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 Hcell; kcsh OSH g; exact I) ltac:(kw1 Hst; exact I) ltac:(zx_lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation m64_pins := [(11%bv : reg, ZV 32); (17%bv : reg, ZV 32); (16%bv : reg, ZV 33); (15%bv : reg, ZV 34); (7%bv : reg, ZV 36);
                          (5%bv : reg, ZL 4195354525); (6%bv : reg, ZL 27755575600); (14%bv : reg, ZL 268435455); (12%bv : reg, ZL SHA)].
Abbreviation m64_uvi clo chi := [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 63 - 1); Some (0, 2 ^ 28 - 1); Some (2 ^ 60, 2 ^ 62)].
Definition m64B_keep : list Z := [1; 2; 3; 4; 5; 6; 8; 9; 10; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31].

#[using="Type"] Lemma m64_loop_B : forall t done c regs m (A g : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 11%bv = Z_to_bv 64 p -> getr regs 17%bv = Z_to_bv 64 p -> getr regs 16%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 15%bv = Z_to_bv 64 c -> getr regs 7%bv = Z_to_bv 64 g ->
  getr regs 5%bv = Z_to_bv 64 kFive27_lo -> getr regs 6%bv = Z_to_bv 64 (kFive27_hi * 16) -> getr regs 14%bv = Z_to_bv 64 MASK ->
  getr regs 12%bv = Z_to_bv 64 SHA ->
  0 <= c < 2 ^ 63 -> ok t -> t <> [] -> 2 ^ 60 + Z.of_nat (length t) <= g <= 2 ^ 62 ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objshB m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 126 ->
  arr32 SEGS_B m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab584) m rom) (mkst regs' (Z_to_bv 64 0x0ab5f4) m' rom)
    /\ arr32 SEGS_B m' A (done ++ fst (mul64_l kFive27_lo kFive27_hi c t))
    /\ getr regs' 15%bv = Z_to_bv 64 (snd (mul64_l kFive27_lo kFive27_hi c t))
    /\ keeps m64B_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A g p pend RP RP' RN RC RG R5 R6 R14 R12 Hc Hok Hne Hg HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok]. cbn [length] in *.
  assert (Hcell : exists bs, rdn SEGS_B m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul64_step_bounds x c Hx Hc) as SB. cbn zeta in SB. destruct SB as (Htmp & Hc' & Hmid & Hcd & Htd).
  cbn [mul64_l]. destruct (mul64_l kFive27_lo kFive27_hi (c / B + (c mod B + kFive27_lo * x) / B + kFive27_hi * x * 16) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold kFive27_lo, kFive27_hi, MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_B constr:(CTX (vi_regs ++ m64_uvi 1 1) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 40%nat [0x0ab584; 0x0ab5f4] (SCR [] [])
      constr:(m64_pins) [A + 4 * Z.of_nat (length done); 1; c; x; g] constr:(m64_uvi 1 1) regs m rom 0x0ab584.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [etransitivity; [zx_regv ZR|]; f_equal; lia|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - zx_run SEGS_B constr:(CTX (vi_regs ++ m64_uvi 2 128) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 40%nat [0x0ab584; 0x0ab5f4] (SCR [] [])
      constr:(m64_pins) [A + 4 * Z.of_nat (length done); Z.of_nat (S (S (length t'))); c; x; g] constr:(m64_uvi 2 128) regs m rom 0x0ab584.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (c mod 268435456 + 4195354525 * x) mod 268435456).
    assert (Harr1 : arr32 SEGS_B m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) (c / 268435456 + (c mod 268435456 + 4195354525 * x) / 268435456 + 1734723475 * x * 16) regs1 m1 A (g - 1)).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & C15 & K2 & U2 & G2);
      [ etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | exact Hok | congruence | lia | lia | lia | lia | | lia | exact Harr1 | | ].
    { unfold m1. eapply (objshB_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
        [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact C15|].
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
Abbreviation car64_pins := [(10%bv : reg, ZV 32); (15%bv : reg, ZV 34); (13%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (14%bv : reg, ZL 268435455); (12%bv : reg, ZL SHA)].
Abbreviation car64_kw := [KW (ZV 32) 0 2].
Abbreviation car64_kn := [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 33)].
Definition car64B_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].

Ltac car64_obls ZXB OSH Hsto Cu u :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; kc1 Cu; exact I) ltac:(kw1 Hsto; exact I)
    ltac:(idtac; zx_scs ltac:(first [shread OSH u | eapply sc_store_in; [exact Hsto|zwidth; lia] | ptrchk])).

#[using="Type"] Lemma car64_B : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 15%bv = Z_to_bv 64 c ->
  getr regs 13%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 14%bv = Z_to_bv 64 MASK -> getr regs 12%bv = Z_to_bv 64 SHA ->
  cellN SEGS_B m o 2 u ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objshB m o ->
  arr32 SEGS_B m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab5f4) m rom) (mkst regs' (Z_to_bv 64 0x0ab68c) m' rom)
    /\ arr32 SEGS_B m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_B m' o 2 (u + zlen (chunks 3 c))
    /\ keeps car64B_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi R10 RC R13 R14 R12 Cu Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Ho8 OSH Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [[-> ->] | [-> ->]]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) car64_kn car64_kw)
      60%nat [0x0ab68c] (SCR [false] [ZL 0]) constr:(car64_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) regs m rom 0x0ab5f4.
    car64_obls ZXB OSH Hsto Cu u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (u * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) car64_kn car64_kw)
      90%nat [0x0ab68c] (SCR [false; false] [ZL 0; ZL 0]) constr:(car64_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) regs m rom 0x0ab5f4.
    car64_obls ZXB OSH Hsto Cu u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    replace ((u + 1) * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (u * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
  - rewrite chunks_3 by (unfold B; lia). unfold B.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 56, 2 ^ 63)]) car64_kn car64_kw)
      120%nat [0x0ab68c] (SCR [false; false; false] [ZL 0; ZL 0; ZL 0]) constr:(car64_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 56, 2 ^ 63)]) regs m rom 0x0ab5f4.
    car64_obls ZXB OSH Hsto Cu u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456 mod 268435456; c / 268435456 / 268435456])
      with (((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]) ++ [c / 268435456 / 268435456]) by (rewrite <- !app_assoc; reflexivity).
    replace ((u + 2) * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length ((l ++ [c mod 268435456]) ++ [c / 268435456 mod 268435456]))) by (rewrite !length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite !length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace ((u + 1) * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (u * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KP64 : list Z := [3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Theorem mulu64_B : forall regs m (o sp : Z) (ret : word) (l : list Z) (exb : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 7450580596923828125 -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_B m o (BN l exb) -> ok l -> l <> [] -> zlen l + 3 <= 126 ->
  KHI + 16 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 16 \/ sp <= o) ->
  shcellsB m -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab4ec) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_B m' o (mul64 kFive27_lo kFive27_hi (BN l exb))
    /\ unch m m' [(o, o + 2); (o + 4, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o sp ret l exb R10 R11 R2 R1 Hret Hbn Hok Hne Hlen Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj [SC1 SC2] OSH Hsto Hsts.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _). cbn [cells BnModel.ex] in *.
  assert (Hl1 : 1 <= zlen l) by (destruct l; [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen l) as u eqn:Eu. assert (Hlen' : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity).
  pose proof (u64_range ret) as Rret.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  hide Hdisj.
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 123); Some (0, 18446744073709551615); Some (KHI + 16, HIE)])
      [KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 33)] [KW (ZV 35) (-16) 0])
    40%nat [0x0ab584] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZL 7450580596923828125); (1%bv : reg, ZV 34); (2%bv : reg, ZV 35)])
    [o; u; bv_unsigned ret; sp] constr:([Some (IMG, HIE - 516); Some (1, 123); Some (0, 18446744073709551615); Some (KHI + 16, HIE)]) regs m rom 0x0ab4ec.
  zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
    ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
  zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (15%bv : reg) as A15.
  zx_reg ZR (7%bv : reg) as A7. zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (6%bv : reg) as A6. zx_reg ZR (14%bv : reg) as A14.
  zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (13%bv : reg) as A13. zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (2%bv : reg) as A2.
  assert (K1 : keeps KP64 regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M1. clear ZE ZR ZF. set (m1 := wbytes m _ _) in M1.
  unhide.
  assert (Carr1 : arr32 SEGS_B m1 (o + 4) l) by (unfold m1; apply arr32_store_other; zwidth; unfold zlen in *; try lia; exact Carr).
  assert (OSH1 : objshB m1 o).
  { unfold m1. eapply (objshB_unch m _ [(sp - 16, sp)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
  assert (Hsto1 : RiscvSemantics.store_ok SEGS_B m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [|exact Hsto]; unfold m1; growsx).
  assert (Cu1 : cellN SEGS_B m1 o 2 u) by (unfold m1; cellN_go).
  assert (Ce1 : cellN SEGS_B m1 (o + 2) 2 exb) by (unfold m1; cellN_go).
  assert (RA1 : cellN SEGS_B m1 (sp + -8) 8 (bv_unsigned ret)) by (unfold m1; cellN_go).
  hide Hdisj.
  (* [comment removed for export] *)
  unfold mul64. cbn [cells BnModel.ex]. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
  pose proof (mul64_l_spec l 0 Hok ltac:(lia)) as SP.
  destruct (mul64_l kFive27_lo kFive27_hi 0 l) as [rr c] eqn:Em. destruct SP as (_ & Hokr & Hlenr & Hc).
  destruct (m64_loop_B l [] 0 regs1 m1 (o + 4) ((18446744073709551615 - o) / 2 ^ 2)) as (regs2 & m2 & M2 & Harr2 & C15 & K2 & U2 & G2);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { exact A11. } { exact A17. } { rewrite A16. f_equal. lia. } { exact A15. } { exact A7. } { exact A5. }
  { rewrite A6. apply bv_eq. vm_compute. reflexivity. } { exact A14. } { exact A12. }
  { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { lia. } { replace (o + 4 - 4) with o by lia. exact Ho8. }
  { replace (o + 4 - 4) with o by lia. exact OSH1. } { lia. } { exact Carr1. }
  { eapply sc_store_in; [exact Hsto1|]. zwidth. lia. }
  rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
  cbn [length app Z.of_nat] in U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
  assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (kept K2 10 A10).
  assert (C13 : getr regs2 13%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K2 13 A13).
  assert (C14 : getr regs2 14%bv = Z_to_bv 64 MASK) by (kept K2 14 A14).
  assert (C12 : getr regs2 12%bv = Z_to_bv 64 SHA) by (kept K2 12 A12).
  assert (C2 : getr regs2 2%bv = Z_to_bv 64 (sp + -16)) by (kept K2 2 A2).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_B m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto1]).
  assert (Cu2 : cellN SEGS_B m2 o 2 u).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu1]. }
  assert (Ce2 : cellN SEGS_B m2 (o + 2) 2 exb).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce1]. }
  assert (RA2 : cellN SEGS_B m2 (sp + -8) 8 (bv_unsigned ret)).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; unhide; lia | exact RA1]. }
  assert (OSH2 : objshB m2 o).
  { eapply (objshB_unch m1 _ _); [exact U2 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH1]. }
  assert (U02 : unch m m2 [(o, o + 2); (o + 4, o + 516); (sp - 16, sp)]).
  { apply (unch_trans m m1 m2); [unfold m1; unhide; unchx|]. eapply unch_widen; [exact U2|].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia]. }
  assert (G02 : mem_grows m m2) by (apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2]).
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* [comment removed for export] *)
    subst c. rewrite chunks_0, app_nil_r.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 16); Some (0, 18446744073709551615)]) [KC (ZV 32) 8 8 (ZV 33)] (@nil kwin))
      10%nat (@nil Z) (SCR [] []) constr:([(15%bv : reg, ZL 0); (2%bv : reg, ZV 32)]) [sp + -16; bv_unsigned ret]
      constr:([Some (IMG, HIE - 16); Some (0, 18446744073709551615)]) regs2 m2 rom 0x0ab5f4.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA2; exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    assert (R1' : getr regs3 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
    split.
    { apply keeps_CS_of; [| etransitivity; [zx_regv ZR|]; rewrite R2; f_equal; lia].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite Hlenr, <- Eu. exact Cu2.
      - exact Ce2.
      - exact Harr2. }
    split; [exact U02 | exact G02].
  - (* [comment removed for export] *)
    assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63))).
    { unfold B. destruct (Z_lt_dec c 268435456); [exists 1, (268435456 - 1); lia|].
      destruct (Z_lt_dec c (268435456 * 268435456)); [exists 268435456, (268435456 * 268435456 - 1); lia|].
      exists (268435456 * 268435456), (2 ^ 63); lia. }
    destruct Hcls as (clo & chi & Hcc & Hcls).
    destruct (car64_B regs2 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & K4 & U4 & G4).
    { exact C10. } { exact C15. } { exact C13. } { exact C14. } { exact C12. } { exact Cu2. }
    { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact OSH2. } { exact Harr2. } { exact Hsto2. }
    assert (RA4 : cellN SEGS_B m4 (sp + -8) 8 (bv_unsigned ret)).
    { eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; unhide; lia | exact RA2]. }
    assert (D2 : getr regs4 2%bv = Z_to_bv 64 (sp + -16)) by (kept K4 2 C2).
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 16); Some (0, 18446744073709551615)]) [KC (ZV 32) 8 8 (ZV 33)] (@nil kwin))
      10%nat (@nil Z) (SCR [] []) constr:([(2%bv : reg, ZV 32)]) [sp + -16; bv_unsigned ret]
      constr:([Some (IMG, HIE - 16); Some (0, 18446744073709551615)]) regs4 m4 rom 0x0ab68c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA4; exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
    assert (R1' : getr regs5 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs5, m4. split.
    { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact ZM|].
      zx_ret SEGS_B; [exact R1' | exact Hret]. }
    assert (Hck : zlen (chunks 3 c) <= 3).
    { pose proof (chunks_spec 3 c ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & _ & _ & H). exact H. }
    split.
    { apply keeps_CS_of; [| etransitivity; [zx_regv ZR|]; rewrite R2; f_equal; lia].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite zlen_app, Hlenr, <- Eu. exact Cu4.
      - eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Ce2].
      - exact Harr4. }
    split; [|eapply mem_grows_trans; [exact G02 | exact G4]].
    apply (unch_trans m m2 m4); [exact U02|].
    eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]].
    * eexists; split; [left; reflexivity|cbn; lia].
    * eexists; split; [right; left; reflexivity|cbn; lia].
Qed.
End S.
