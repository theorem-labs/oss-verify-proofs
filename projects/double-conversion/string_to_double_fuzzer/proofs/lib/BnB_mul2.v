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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnA_mul2 BnB_lib BnB_mul1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

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
Abbreviation m32_pins := [(11%bv : reg, ZV 32); (17%bv : reg, ZV 32); (16%bv : reg, ZV 33); (14%bv : reg, ZV 34); (6%bv : reg, ZV 36);
                          (5%bv : reg, ZV 37); (15%bv : reg, ZL 268435455); (12%bv : reg, ZL SHA)].
Abbreviation m32_uvi clo chi := [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 32); Some (0, 2 ^ 28 - 1); Some (2 ^ 60, 2 ^ 62); Some (2, 2 ^ 31 - 1)].
Definition m32B_keep : list Z := [1; 2; 3; 4; 5; 8; 9; 10; 12; 13; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma m32_loop_B : forall t done c regs m (A F g : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 11%bv = Z_to_bv 64 p -> getr regs 17%bv = Z_to_bv 64 p -> getr regs 16%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 14%bv = Z_to_bv 64 c -> getr regs 6%bv = Z_to_bv 64 g ->
  getr regs 5%bv = Z_to_bv 64 F -> getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 12%bv = Z_to_bv 64 SHA ->
  2 <= F < 2 ^ 31 -> 0 <= c <= F -> ok t -> t <> [] -> 2 ^ 60 + Z.of_nat (length t) <= g <= 2 ^ 62 ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objshB m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 126 ->
  arr32 SEGS_B m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m' tmp,
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab398) m rom) (mkst regs' (Z_to_bv 64 0x0ab3f0) m' rom)
    /\ arr32 SEGS_B m' A (done ++ fst (mul32_l F c t))
    /\ getr regs' 14%bv = Z_to_bv 64 (snd (mul32_l F c t))
    /\ getr regs' 7%bv = Z_to_bv 64 tmp /\ tmp / 2 ^ 28 = snd (mul32_l F c t) /\ 0 <= tmp < 2 ^ 60
    /\ keeps m32B_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A F g p pend RP RP' RN RC RG RF R15 R12 HF Hc Hok Hne Hg HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  subst p pend. apply ok_cons in Hok as [Hx Hok].
  assert (Hcell : exists bs, rdn SEGS_B m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul32_step_bounds F x c ltac:(lia) Hx Hc) as (Hp1 & Hp2 & Hp3).
  cbn [mul32_l]. destruct (mul32_l F ((F * x + c) / B) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_B constr:(CTX (vi_regs ++ m32_uvi 1 1) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 40%nat [0x0ab398; 0x0ab3f0] (SCR [] [])
      constr:(m32_pins) [A + 4 * Z.of_nat (length done); 1; c; x; g; F] constr:(m32_uvi 1 1) regs m rom 0x0ab398.
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
  - zx_run SEGS_B constr:(CTX (vi_regs ++ m32_uvi 2 128) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 40%nat [0x0ab398; 0x0ab3f0] (SCR [] [])
      constr:(m32_pins) [A + 4 * Z.of_nat (length done); Z.of_nat (S (S (length t'))); c; x; g; F] constr:(m32_uvi 2 128) regs m rom 0x0ab398.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (F * x + c) mod 268435456).
    assert (Harr1 : arr32 SEGS_B m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) ((F * x + c) / 268435456) regs1 m1 A F (g - 1)).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & tmp & M2 & Harr2 & COUT & CT & HT1 & HT2 & K2 & U2 & G2);
      [ etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | lia | exact Hok | congruence | lia | lia | lia | lia | | lia | exact Harr1 | | ].
    { unfold m1. eapply (objshB_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
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
Abbreviation car32_pins := [(10%bv : reg, ZV 32); (14%bv : reg, ZV 34); (7%bv : reg, ZV 35); (13%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA));
                            (15%bv : reg, ZL 268435455); (12%bv : reg, ZL SHA)].
Abbreviation car32_kn := [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 33)].
Definition car32B_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 12; 13; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].

Ltac car32_obls ZXB OSH Hsto Cu u :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; kc1 Cu; exact I) ltac:(kw1 Hsto; exact I)
    ltac:(idtac; zx_scs ltac:(first [shread OSH u | eapply sc_store_in; [exact Hsto|zwidth; lia] | ptrchk])).

#[using="Type"] Lemma car32_B : forall regs m (o u c tmp : Z) (l : list Z) (clo chi : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 14%bv = Z_to_bv 64 c -> getr regs 7%bv = Z_to_bv 64 tmp ->
  getr regs 13%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 12%bv = Z_to_bv 64 SHA ->
  cellN SEGS_B m o 2 u -> tmp / 2 ^ 28 = c -> 0 <= tmp < 2 ^ 60 ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objshB m o ->
  arr32 SEGS_B m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab3f0) m rom) (mkst regs' (Z_to_bv 64 0x0ab3f8) m' rom)
    /\ arr32 SEGS_B m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_B m' o 2 (u + zlen (chunks 3 c))
    /\ keeps car32B_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c tmp l clo chi R10 RC R7 R13 R15 R12 Cu Htmp Htmpr Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Ho8 OSH Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [-> ->]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (2 ^ 28, 2 ^ 60 - 1)]) car32_kn [KW (ZV 32) 0 2])
      60%nat [0x0ab3f8] (SCR [false] [ZL 0]) constr:(car32_pins) [o; u; c; tmp]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1); Some (2 ^ 28, 2 ^ 60 - 1)]) regs m rom 0x0ab3f0.
    car32_obls ZXB OSH Hsto Cu u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (u * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (2 ^ 56, 2 ^ 60 - 1)]) car32_kn [KW (ZV 32) 0 2])
      90%nat [0x0ab3f8] (SCR [false; false] [ZL 0; ZL 0]) constr:(car32_pins) [o; u; c; tmp]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1); Some (2 ^ 56, 2 ^ 60 - 1)]) regs m rom 0x0ab3f0.
    car32_obls ZXB OSH Hsto Cu u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    replace ((u + 1) * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length (l ++ [c mod 268435456]))) by (rewrite length_app; cbn [length]; lia).
    apply arr32_snoc'; [lia| rewrite length_app; cbn [length]; lia | | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (u * 4 + (o + 4)) with (o + 4 + 4 * Z.of_nat (length l)) by lia.
    apply arr32_snoc'; [lia|lia|exact Harr|]. rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem mulu32_B : forall regs m (o F sp : Z) (ret : word) (l : list Z) (exb : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 F -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  2 <= F < 2 ^ 31 ->
  bn_at SEGS_B m o (BN l exb) -> ok l -> l <> [] -> zlen l + 2 <= 126 ->
  KHI + 16 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 16 \/ sp <= o) ->
  shcellsB m -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab304) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_B m' o (mul32 F (BN l exb))
    /\ unch m m' [(o, o + 2); (o + 4, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o F sp ret l exb R10 R11 R2 R1 Hret HF Hbn Hok Hne Hlen Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj [SC1 SC2] OSH Hsto Hsts.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _). cbn [cells BnModel.ex] in *.
  assert (Hl1 : 1 <= zlen l) by (destruct l; [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen l) as u eqn:Eu. assert (Hlen' : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity).
  pose proof (u64_range ret) as Rret.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  hide Hdisj.
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 124); Some (0, 18446744073709551615); Some (KHI + 16, HIE); Some (2, 2 ^ 31 - 1)])
      [KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 33)] [KW (ZV 35) (-16) 0])
    40%nat [0x0ab398] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 36); (1%bv : reg, ZV 34); (2%bv : reg, ZV 35)])
    [o; u; bv_unsigned ret; sp; F] constr:([Some (IMG, HIE - 516); Some (1, 124); Some (0, 18446744073709551615); Some (KHI + 16, HIE); Some (2, 2 ^ 31 - 1)]) regs m rom 0x0ab304.
  zx_use2 ZXB ltac:(zx_pins; rewrite Z_to_bv_bv_unsigned; reflexivity) ltac:(zx_lia)
    ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
  zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (14%bv : reg) as A14.
  zx_reg ZR (6%bv : reg) as A6. zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (15%bv : reg) as A15.
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
  unfold mul32. replace (F =? 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (F =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [cells BnModel.ex]. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
  pose proof (mul32_l_spec F l 0 Hok ltac:(lia) ltac:(lia)) as SP.
  destruct (mul32_l F 0 l) as [rr c] eqn:Em. destruct SP as (_ & Hokr & Hlenr & Hc0' & HcF).
  destruct (m32_loop_B l [] 0 regs1 m1 (o + 4) F ((18446744073709551615 - o) / 2 ^ 2)) as (regs2 & m2 & tmp & M2 & Harr2 & C14 & C7 & Htmp & Htmpr & K2 & U2 & G2);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { exact A11. } { exact A17. } { rewrite A16. f_equal. lia. } { exact A14. } { exact A6. } { exact A5. } { exact A15. } { exact A12. }
  { lia. } { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { lia. } { replace (o + 4 - 4) with o by lia. exact Ho8. }
  { replace (o + 4 - 4) with o by lia. exact OSH1. } { lia. } { exact Carr1. }
  { eapply sc_store_in; [exact Hsto1|]. zwidth. lia. }
  rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
  cbn [length app Z.of_nat] in U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
  assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (kept K2 10 A10).
  assert (C13 : getr regs2 13%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K2 13 A13).
  assert (C15 : getr regs2 15%bv = Z_to_bv 64 MASK) by (kept K2 15 A15).
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
  assert (HcF' : c <= F) by (apply HcF; lia).
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* [comment removed for export] *)
    rewrite Hc0 in *. rewrite chunks_0, app_nil_r.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 16); Some (0, 18446744073709551615); Some (0, 2 ^ 28 - 1)]) [KC (ZV 32) 8 8 (ZV 33)] (@nil kwin))
      10%nat (@nil Z) (SCR [] []) constr:([(7%bv : reg, ZV 34); (2%bv : reg, ZV 32)]) [sp + -16; bv_unsigned ret; tmp]
      constr:([Some (IMG, HIE - 16); Some (0, 18446744073709551615); Some (0, 2 ^ 28 - 1)]) regs2 m2 rom 0x0ab3f0.
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
    assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1))).
    { unfold B. destruct (Z_lt_dec c 268435456); [exists 1, (268435456 - 1); lia|]. exists 268435456, (268435456 * 268435456 - 1); lia. }
    destruct Hcls as (clo & chi & Hcc & Hcls).
    destruct (car32_B regs2 m2 o u c tmp rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & K4 & U4 & G4).
    { exact C10. } { exact C14. } { exact C7. } { exact C13. } { exact C15. } { exact C12. } { exact Cu2. } { exact Htmp. } { exact Htmpr. }
    { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact OSH2. } { exact Harr2. } { exact Hsto2. }
    assert (RA4 : cellN SEGS_B m4 (sp + -8) 8 (bv_unsigned ret)).
    { eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; unhide; lia | exact RA2]. }
    assert (D2 : getr regs4 2%bv = Z_to_bv 64 (sp + -16)) by (kept K4 2 C2).
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 16); Some (0, 18446744073709551615)]) [KC (ZV 32) 8 8 (ZV 33)] (@nil kwin))
      10%nat (@nil Z) (SCR [] []) constr:([(2%bv : reg, ZV 32)]) [sp + -16; bv_unsigned ret]
      constr:([Some (IMG, HIE - 16); Some (0, 18446744073709551615)]) regs4 m4 rom 0x0ab3f8.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA4; exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
    assert (R1' : getr regs5 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs5, m4. split.
    { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact ZM|].
      zx_ret SEGS_B; [exact R1' | exact Hret]. }
    assert (Hck : zlen (chunks 3 c) <= 3).
    { pose proof (chunks_spec 3 c ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); unfold B in *; lia)) as (_ & _ & _ & H). exact H. }
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
