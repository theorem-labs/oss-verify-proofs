(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface BnP_add BnP_add2 BnU_add.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_add.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].

(* [comment removed for export] *)
Abbreviation P2_kn :=
  [KC (ZL 0) 0x129ea8 8 (ZL 0x132278); KC (ZL 0) 0x132278 8 (ZL SHA);
   KC (ZDivP (ZAdd (ZV 32) (ZL 2)) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 33) (ZL 2)) 3) SHA 1 (ZL 0);
   KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZV 33) 3) SHA 1 (ZL 0);
   KC (ZV 32) 0 2 (ZV 35); KC (ZV 32) 2 2 (ZL 0); KC (ZV 33) 0 2 (ZV 36); KC (ZV 33) 2 2 (ZL 0)].
Abbreviation P2_uvi := [Some (IMG, HIE - 516); Some (IMG, HIE - 516); Some (KHI + 112, HIE); Some (0, 126); Some (1, 3)].
Abbreviation P_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34)].

#[using="Type"] Theorem add_A : forall regs m (o q sp : Z) (ret : word) (l ol : list Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 q -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_A m o (BN l 0) -> bn_at SEGS_A m q (BN ol 0) -> ok l -> ok ol -> zlen l <= 126 -> 1 <= zlen ol <= 3 ->
  KHI + 112 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> APP q 516 -> q + 516 <= HIE -> o mod 8 = 0 -> q mod 8 = 0 ->
  (q + 516 <= o \/ o + 516 <= q) -> (o + 516 <= sp - 112 \/ sp <= o) -> (q + 516 <= sp - 112 \/ sp <= q) ->
  shcells m -> objsh m o -> objsh m q ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 (sp - 112)) 112 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aac44) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_A m' o (BN (add_l 0 l ol) 0)
    /\ unch m m' [(o, o + 516); (sp - 112, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o q sp ret l ol R10 R11 R2 R1 Hret Hbo Hbq Hokl Hoko Hu Hn Hsp1 Hsp2 Ho1 Ho2 Hq1 Hq2 Ho8 Hq8 Hdj Hdo Hdq SC OSH QSH Hsto Hsts.
  destruct Hbo as (Cu & Ce & Carr & _ & _). destruct Hbq as (Cn & Cqe & Carro & _ & _). cbn [cells BnModel.ex] in *.
  remember (zlen l) as u eqn:Eu. remember (zlen ol) as n eqn:En.
  assert (Hul : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity). assert (Hnl : Z.of_nat (length ol) = n) by (rewrite En; reflexivity).
  pose proof (zlen_nonneg l) as Hu0. rewrite <- Eu in Hu0.
  pose proof (u64_range ret) as W1. pose proof (u64_range (getr regs 8%bv)) as W8. pose proof (u64_range (getr regs 9%bv)) as W9.
  pose proof (u64_range (getr regs 18%bv)) as W18. pose proof (u64_range (getr regs 19%bv)) as W19.
  pose proof (u64_range (getr regs 20%bv)) as W20. pose proof (u64_range (getr regs 21%bv)) as W21.
  pose proof (u64_range (getr regs 22%bv)) as W22. pose proof (u64_range (getr regs 23%bv)) as W23.
  pose proof (u64_range (getr regs 24%bv)) as W24. pose proof (u64_range (getr regs 25%bv)) as W25.
  pose proof (u64_range (getr regs 26%bv)) as W26. pose proof (u64_range (getr regs 27%bv)) as W27.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  (* [comment removed for export] *)
  hide Hdj. hide Hdo. hide Hdq.
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (IMG, HIE - 516); Some (KHI + 112, HIE)]) (@nil kcell) [KW (ZV 34) (-112) 0])
    20%nat [0x0aac7c] (SCR [] []) constr:(P_pins) [o; q; sp]
    constr:([Some (IMG, HIE - 516); Some (IMG, HIE - 516); Some (KHI + 112, HIE)]) regs m rom 0x0aac44.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I). zx_name regs1.
  rename ZM into M1. rename ZE into ZE1. rename ZR into ZR1. clear ZF.
  set (m1 := wbytes _ _ _) in M1.
  assert (SV : cellN SEGS_A m1 (sp - 8) 8 (bv_unsigned ret) /\ cellN SEGS_A m1 (sp - 16) 8 (bv_unsigned (getr regs 8%bv))
    /\ cellN SEGS_A m1 (sp - 24) 8 (bv_unsigned (getr regs 9%bv)) /\ cellN SEGS_A m1 (sp - 32) 8 (bv_unsigned (getr regs 18%bv))
    /\ cellN SEGS_A m1 (sp - 40) 8 (bv_unsigned (getr regs 19%bv)) /\ cellN SEGS_A m1 (sp - 48) 8 (bv_unsigned (getr regs 20%bv))
    /\ cellN SEGS_A m1 (sp - 56) 8 (bv_unsigned (getr regs 21%bv)) /\ cellN SEGS_A m1 (sp - 64) 8 (bv_unsigned (getr regs 22%bv))
    /\ cellN SEGS_A m1 (sp - 72) 8 (bv_unsigned (getr regs 23%bv)) /\ cellN SEGS_A m1 (sp - 80) 8 (bv_unsigned (getr regs 24%bv))
    /\ cellN SEGS_A m1 (sp - 88) 8 (bv_unsigned (getr regs 25%bv)) /\ cellN SEGS_A m1 (sp - 96) 8 (bv_unsigned (getr regs 26%bv))
    /\ cellN SEGS_A m1 (sp - 104) 8 (bv_unsigned (getr regs 27%bv))).
  { unfold m1. rewrite <- R1. clear - Hsp1 Hsp2 W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 R1. rewrite <- R1 in W1.
    repeat split; cellx. }
  destruct SV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
  assert (U01s : unch m m1 [(sp - 112, sp)]) by (unfold m1; clear - Hsp1 Hsp2; unchx).
  assert (G01 : mem_grows m m1) by (unfold m1; growsx).
  assert (A10 : getr regs1 10%bv = Z_to_bv 64 o) by (zx_regv ZR1).
  assert (A11 : getr regs1 11%bv = Z_to_bv 64 q) by (zx_regv ZR1).
  assert (A2 : getr regs1 2%bv = Z_to_bv 64 (sp - 112)) by (zx_regv ZR1).
  assert (K1 : keeps [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE1 ZR1); vm_compute; reflexivity).
  clear ZE1 ZR1.
  (* [comment removed for export] *)
  assert (XFER : forall a k v, cellN SEGS_A m a k v -> (a + Z.of_nat k <= sp - 112 \/ sp <= a) -> 0 <= a -> a + Z.of_nat k <= M64 -> cellN SEGS_A m1 a k v).
  { intros a k v C Ha Hb Hc. eapply cellN_unch; [exact U01s | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact C]. }
  destruct SC as [SC1 SC2].
  assert (SC1' : cellN SEGS_A m1 0x129ea8 8 0x132278) by (apply XFER; [exact SC1 | cbn; lia | lia | cbn; zwidth; lia]).
  assert (SC2' : cellN SEGS_A m1 0x132278 8 SHA) by (apply XFER; [exact SC2 | cbn; lia | lia | cbn; zwidth; lia]).
  assert (OSH1 : objsh m1 o) by (eapply (objsh_unch m m1); [exact U01s | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]).
  assert (QSH1 : objsh m1 q) by (eapply (objsh_unch m m1); [exact U01s | intros r0 [<-|[]]; cbn; lia | lia | lia | exact QSH]).
  unhide.
  assert (Cu1 : cellN SEGS_A m1 o 2 u) by (apply XFER; [exact Cu | cbn; lia | lia | cbn; lia]).
  assert (Ce1 : cellN SEGS_A m1 (o + 2) 2 0) by (apply XFER; [exact Ce | cbn; lia | lia | cbn; lia]).
  assert (Cn1 : cellN SEGS_A m1 q 2 n) by (apply XFER; [exact Cn | cbn; lia | lia | cbn; lia]).
  assert (Cqe1 : cellN SEGS_A m1 (q + 2) 2 0) by (apply XFER; [exact Cqe | cbn; lia | lia | cbn; lia]).
  assert (Carr1 : arr32 SEGS_A m1 (o + 4) l).
  { eapply arr32_unch; [exact U01s | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Carr]. }
  assert (Carro1 : arr32 SEGS_A m1 (q + 4) ol).
  { eapply arr32_unch; [exact U01s | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Carro]. }
  assert (Hsto1 : RiscvSemantics.store_ok SEGS_A m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G01 | exact Hsto]).
  assert (U01 : unch m m1 [(o, o + 516); (sp - 112, sp)]).
  { eapply unch_widen; [exact U01s|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia]. }
  clear Cu Ce Carr Cn Cqe Carro XFER.
  hide Hdj. hide Hdo. hide Hdq.
  (* [comment removed for export] *)
  assert (P2 : exists regs2,
    msteps SEGS_A (mkst regs1 (Z_to_bv 64 0x0aac7c) m1 rom) (mkst regs2 (Z_to_bv 64 0x0aae7c) m1 rom)
    /\ getr regs2 10%bv = Z_to_bv 64 (0 * 4) /\ getr regs2 12%bv = Z_to_bv 64 0 /\ getr regs2 13%bv = Z_to_bv 64 0
    /\ getr regs2 18%bv = Z_to_bv 64 0 /\ getr regs2 14%bv = Z_to_bv 64 (q + 4) /\ getr regs2 15%bv = Z_to_bv 64 o
    /\ getr regs2 16%bv = Z_to_bv 64 o /\ getr regs2 17%bv = Z_to_bv 64 (o + 4) /\ getr regs2 5%bv = Z_to_bv 64 (o + 4)
    /\ getr regs2 6%bv = Z_to_bv 64 ((0 + n) * 4) /\ getr regs2 11%bv = Z_to_bv 64 MASK /\ getr regs2 20%bv = Z_to_bv 64 SHA
    /\ getr regs2 22%bv = Z_to_bv 64 u
    /\ getr regs2 8%bv = Z_to_bv 64 o /\ getr regs2 2%bv = Z_to_bv 64 (sp - 112) /\ getr regs2 21%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)
    /\ keeps [2; 3; 4] regs1 regs2).
  { destruct (Z_lt_dec n u) as [Hlt|Hge].
    - zx_run SEGS_A constr:(CTX (vi_regs ++ P2_uvi) P2_kn (@nil kwin)) 150%nat [0x0aae7c] (SCR [true] [])
        constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-112)))]) [o; q; sp; u; n] constr:(P2_uvi) regs1 m1 rom 0x0aac7c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
        ltac:(kc1 SC1'; kc1 SC2'; kcsh OSH1 0; kcsh QSH1 0; kcsh OSH1 0; kcsh QSH1 0; kc1 Cu1; kc1 Ce1; kc1 Cn1; kc1 Cqe1; exact I)
        ltac:(exact I) ltac:(idtac; zx_scs ltac:((try clear - regs o q sp ret l ol u n Hu Hn Hsp1 Hsp2 Ho1 Ho2 Hq1 Hq2 Hu0 W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 Ho8 Hq8 Hlt; lia))). zx_name regs2.
      eexists regs2. split; [exact ZM|].
      do 16 (split; [zx_regv ZR; unfold MASK; first [reflexivity | f_equal; lia]|]).
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
    - zx_run SEGS_A constr:(CTX (vi_regs ++ P2_uvi) P2_kn (@nil kwin)) 150%nat [0x0aae7c] (SCR [false] [])
        constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-112)))]) [o; q; sp; u; n] constr:(P2_uvi) regs1 m1 rom 0x0aac7c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
        ltac:(kc1 SC1'; kc1 SC2'; kcsh OSH1 0; kcsh QSH1 0; kcsh OSH1 0; kcsh QSH1 0; kc1 Cu1; kc1 Ce1; kc1 Cn1; kc1 Cqe1; exact I)
        ltac:(exact I) ltac:(idtac; zx_scs ltac:((try clear - regs o q sp ret l ol u n Hu Hn Hsp1 Hsp2 Ho1 Ho2 Hq1 Hq2 Hu0 W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 Ho8 Hq8 Hge; lia))). zx_name regs2.
      eexists regs2. split; [exact ZM|].
      do 16 (split; [zx_regv ZR; unfold MASK; first [reflexivity | f_equal; lia]|]).
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  destruct P2 as (regs2 & M2 & D10 & D12 & D13 & D18 & D14 & D15 & D16 & D17 & D5 & D6 & D11 & D20 & D22 & D8 & D2 & D21 & K2).
  unhide.
  (* [comment removed for export] *)
  destruct ol as [|y0 ol'] eqn:Eol; [rewrite zlen_nil in En; lia|]. rewrite <- Eol in * |- *.
  destruct (add_loop_A rom ol [] l [] 0 regs2 m1 o q u) as (regs3 & m3 & S & M3 & Harr3 & E12 & E30 & HS & HS2 & E13 & E18 & E10 & K3 & U3 & G3);
    cbn [length Z.of_nat]; rewrite ?Hnl.
  { reflexivity. } { exact D10. } { exact D12. } { exact D13. } { exact D18. } { exact D14. } { exact D15. } { exact D16. } { exact D17. }
  { exact D5. } { exact D6. } { exact D11. } { exact D20. } { exact D22. }
  { rewrite Z.max_l by lia. lia. } { lia. } { lia. } { exact Hokl. } { exact Hoko. } { rewrite Eol; congruence. } { lia. }
  { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact Hq8. } { exact Hdj. } { exact OSH1. } { exact QSH1. }
  { exact Carr1. } { exact Carro1. } { exact Hsto1. }
  cbn [app] in Harr3. rewrite ?Z.add_0_l, ?Hnl in E13. rewrite ?Z.add_0_l, ?Hnl in E18. rewrite ?Z.add_0_l, ?Hnl in E10.
  rewrite ?Z.mul_0_r, ?Z.add_0_r, ?Z.add_0_l, ?Hnl in U3.
  pose proof (addm_bounds ol l 0 Hokl Hoko ltac:(lia)) as [Hokr Hc'].
  pose proof (addm_length ol l 0) as Hlenr.
  remember (fst (addm 0 l ol)) as r eqn:Er. remember (snd (addm 0 l ol)) as c' eqn:Ec'.
  assert (Hst : exists k, Z.of_nat (length (skipn (length ol) l)) = k /\ Z.max u n = n + k) by (eexists; split; [reflexivity|]; rewrite length_skipn; (try clear - regs o q sp ret l ol u n Hsp1 Ho1 Hq1 Ho8 Hq8 Hdj Hdo Hdq Hul Hnl W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 S r HS2 Hlenr; lia)).
  destruct Hst as (kk & Hkk & Hmaxk).
  assert (Hsto3 : RiscvSemantics.store_ok SEGS_A m3 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G3 | exact Hsto1]).
  assert (OSH3 : objsh m3 o) by (eapply (objsh_unch m1 m3); [exact U3 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH1]).
  assert (E11 : getr regs3 11%bv = Z_to_bv 64 MASK) by (kept K3 11 D11).
  assert (E20 : getr regs3 20%bv = Z_to_bv 64 SHA) by (kept K3 20 D20).
  assert (E22 : getr regs3 22%bv = Z_to_bv 64 u) by (kept K3 22 D22).
  assert (E15 : getr regs3 15%bv = Z_to_bv 64 o) by (kept K3 15 D15).
  assert (E16 : getr regs3 16%bv = Z_to_bv 64 o) by (kept K3 16 D16).
  assert (E8 : getr regs3 8%bv = Z_to_bv 64 o) by (kept K3 8 D8).
  assert (E2 : getr regs3 2%bv = Z_to_bv 64 (sp - 112)) by (kept K3 2 D2).
  assert (E21 : getr regs3 21%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K3 21 D21).
  (* [comment removed for export] *)
  assert (A : exists regs5 m5 p,
    msteps SEGS_A (mkst regs3 (Z_to_bv 64 0x0aaf2c) m3 rom) (mkst regs5 (Z_to_bv 64 0x0aaf34) m5 rom)
    /\ arr32 SEGS_A m5 (o + 4) (add_l 0 l ol) /\ Z.max u p = zlen (add_l 0 l ol) /\ 0 <= p <= 128
    /\ getr regs5 18%bv = Z_to_bv 64 p /\ getr regs5 22%bv = Z_to_bv 64 u /\ getr regs5 8%bv = Z_to_bv 64 o
    /\ getr regs5 2%bv = Z_to_bv 64 (sp - 112) /\ getr regs5 21%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)
    /\ keeps [3; 4] regs3 regs5
    /\ unch m3 m5 [(o + 4, o + 516)] /\ mem_grows m3 m5).
  { rewrite (add_l_addm ol l 0), <- Er, <- Ec'. unfold MASK in E11.
    destruct (Z.eq_dec c' 0) as [Hc0 | Hc1].
    - (* [comment removed for export] *)
      rewrite Hc0 in *. replace (addc_l 0 (skipn (length ol) l)) with (skipn (length ol) l) by (destruct (skipn (length ol) l); reflexivity).
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 3); Some (0, 2 ^ 30 - 1)]) (@nil kcell) (@nil kwin))
        10%nat [0x0aaf34; 0x0aaf94] (SCR [false] [])
        constr:([(30%bv : reg, ZV 34); (10%bv : reg, ZMul (ZV 33) (ZL 4)); (15%bv : reg, ZV 32); (16%bv : reg, ZV 32)])
        [o; n; S] constr:([Some (IMG, HIE - 516); Some (1, 3); Some (0, 2 ^ 30 - 1)]) regs3 m3 rom 0x0aaf2c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs5.
      eexists regs5, m3, n. split; [exact ZM|].
      split; [exact Harr3|].
      split; [rewrite zlen_app; unfold zlen; rewrite Hlenr; unfold zlen in Hkk; lia|].
      split; [lia|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (18%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E18]|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (22%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E22]|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (8%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E8]|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E2]|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (21%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E21]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [apply unch_refl | apply mem_grows_refl].
    - (* [comment removed for export] *)
      assert (Hc'1 : c' = 1) by lia. rewrite Hc'1 in *.
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 3); Some (0, 2 ^ 30 - 1)]) (@nil kcell) (@nil kwin))
        10%nat [0x0aaf34; 0x0aaf94] (SCR [true] [])
        constr:([(30%bv : reg, ZV 34); (10%bv : reg, ZMul (ZV 33) (ZL 4)); (15%bv : reg, ZV 32); (16%bv : reg, ZV 32)])
        [o; n; S] constr:([Some (IMG, HIE - 516); Some (1, 3); Some (0, 2 ^ 30 - 1)]) regs3 m3 rom 0x0aaf2c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs4.
      assert (Harr4 : arr32 SEGS_A m3 (o + 4 + 4 * n) (skipn (length ol) l)).
      { replace (o + 4 + 4 * n) with (o + 4 + 4 * Z.of_nat (length r)) by (rewrite Hlenr; lia). apply arr32_skip_g. exact Harr3. }
      destruct (addc_loop_A rom (skipn (length ol) l) n 1 regs4 m3 o u) as (regs5 & m5 & k & M5 & Harr5 & Hk & Hlen5 & F18 & K5 & U5 & G5).
      { zx_regv ZR. } { zx_regv ZR. }
      { etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E13]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (18%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E18]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E12]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (11%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E11]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (20%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E20]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (22%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E22]. }
      { unfold zlen. rewrite Hkk. lia. } { lia. } { lia. } { unfold zlen. rewrite Hkk. lia. }
      { apply ok_skipn. exact Hokl. }
      { lia. } { lia. } { lia. } { exact Ho8. } { exact OSH3. } { exact Harr4. } { exact Hsto3. }
      assert (Hkb : k <= kk + 1).
      { destruct (addc_l_len_cases (skipn (length ol) l) 1 (ok_skipn _ _ Hokl) ltac:(lia)) as (k' & Hk' & Hlen' & Hkb'). unfold zlen in *. rewrite Hkk in *. lia. }
      eexists regs5, m5, (n + k). split; [eapply msteps_trans; [exact ZM | exact M5]|].
      split.
      { apply arr32_app_g.
        - eapply arr32_unch; [exact U5 | lia | rewrite Hlenr; (try clear - regs o q sp ret l ol u n Hn Hsp2 Ho1 Ho2 Hq1 Hq2 Ho8 Hq8 Hnl W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 S r HS2 Hlenr k; lia) | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; rewrite Hlenr; (try clear - regs o q sp ret l ol u n Hsp1 Ho1 Hq1 Ho8 Hq8 Hdj Hdo Hdq Hnl W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 S r HS2 Hlenr k; lia) |].
          eapply arr32_prefix. exact Harr3.
        - rewrite Hlenr, Hnl. exact Harr5. }
      split; [rewrite zlen_app, Hlen5; unfold zlen in *; rewrite Hlenr, Hkk; (try clear - regs o q sp ret l ol u n Hsp1 Ho1 Hq1 Ho8 Hq8 Hdj Hdo Hdq Hnl W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 S r HS2 Hlenr kk Hkk Hmaxk k Hk; lia)|].
      split; [unfold zlen in *; rewrite Hkk in Hlen5; (try clear - regs o q sp ret l ol u n Hu Hn Hsp1 Ho1 Hq1 Ho8 Hq8 Hdj Hdo Hdq W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 S r HS2 Hlenr kk Hmaxk k Hk Hkb; lia)|].
      split; [exact F18|].
      split; [etransitivity; [exact (K5 22 ltac:(in_list)) |]; etransitivity; [exact (reg_kept _ _ _ _ (22%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E22]|].
      split; [etransitivity; [exact (K5 8 ltac:(in_list)) |]; etransitivity; [exact (reg_kept _ _ _ _ (8%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E8]|].
      split; [etransitivity; [exact (K5 2 ltac:(in_list)) |]; etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E2]|].
      split; [etransitivity; [exact (K5 21 ltac:(in_list)) |]; etransitivity; [exact (reg_kept _ _ _ _ (21%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E21]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity]|].
      split; [|exact G5].
      eapply unch_widen; [exact U5|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]].
      eexists; split; [left; reflexivity|]. cbn. unfold zlen in *. rewrite Hkk in Hlen5. (try clear - regs o q sp ret l ol u n Hu Hn Hsp1 Ho1 Hq1 Ho8 Hq8 Hdj Hdo Hdq W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 S r HS2 Hlenr kk Hmaxk k Hlen5 Hkb; lia). }
  destruct A as (regs5 & m5 & p & M5 & Harr5 & Hmax5 & Hp & F18 & F22 & F8 & F2 & F21 & K5 & U5 & G5).
  assert (U15 : unch m1 m5 [(o + 4, o + 516)]).
  { eapply unch_trans; [|exact U5]. eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia. }
  assert (SAV5 : forall a v, cellN SEGS_A m1 a 8 v -> sp - 112 <= a -> a + 8 <= sp -> cellN SEGS_A m5 a 8 v).
  { intros a v C Ha1 Ha2. eapply cellN_unch; [exact U15 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact C]. }
  assert (OSH5 : objsh m5 o) by (eapply (objsh_unch m1 m5); [exact U15 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH1]).
  (* [comment removed for export] *)
  destruct (fin_add_A rom regs5 m5 o sp u p ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv)
              (getr regs 21%bv) (getr regs 22%bv) (getr regs 23%bv) (getr regs 24%bv) (getr regs 25%bv) (getr regs 26%bv) (getr regs 27%bv))
    as (regs6 & m6 & M6 & Cu6 & G2' & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & K6 & U6 & G6);
    try (apply SAV5; [assumption | lia | lia]).
  { exact F8. } { exact F2. } { exact F22. } { exact F18. } { exact F21. } { exact Hret. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
  { exact Ho8. } { exact Hdo. } { exact OSH5. }
  { eapply store_ok_grows; [exact G5 | exact Hsto3]. }
  eexists regs6, m6. split.
  { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M5 | exact M6]. }
  split.
  { intros rg Hrg. cbn in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ etransitivity; [exact G2' | symmetry; exact R2] | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 | exact G21
            | exact G22 | exact G23 | exact G24 | exact G25 | exact G26 | exact G27
            | lazymatch goal with |- getr _ (Z_to_bv 5 ?nn) = _ =>
                etransitivity; [exact (K6 nn ltac:(in_list))|]; etransitivity; [exact (K5 nn ltac:(in_list))|];
                etransitivity; [exact (K3 nn ltac:(in_list))|]; etransitivity; [exact (K2 nn ltac:(in_list))|];
                exact (K1 nn ltac:(in_list)) end ]. }
  split.
  { split; [|split; [|split; [|split; [cbn; lia | cbn [cells]; rewrite <- Hmax5; lia]]]]; cbn [cells BnModel.ex].
    - rewrite <- Hmax5. exact Cu6.
    - eapply cellN_unch; [exact U6 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      eapply cellN_unch; [exact U15 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce1].
    - unfold zlen in Hmax5. eapply arr32_unch; [exact U6 | lia | (try clear - regs o q sp ret l ol u n Hu Hn Hsp2 Ho1 Ho2 Hq1 Hq2 Ho8 Hq8 W1 W8 W9 W18 W19 W20 W21 W22 W23 W24 W25 W26 W27 S r HS2 Hlenr p Hmax5 Hp; lia) | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Harr5]. }
  split.
  { eapply unch_trans; [exact U01|]. eapply unch_trans.
    - eapply unch_widen; [exact U15|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
    - eapply unch_widen; [exact U6|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia. }
  eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G3|]. eapply mem_grows_trans; [exact G5 | exact G6].
Qed.

End S.
