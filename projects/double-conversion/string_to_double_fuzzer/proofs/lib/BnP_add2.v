(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnP_add.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma ok_skipn : forall n l, ok l -> ok (skipn n l).
Proof.
  induction n as [|n IH]; intros l Hl; destruct l; cbn; auto using ok_nil.
  apply IH. apply ok_cons in Hl. tauto.
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem add_P : forall regs m (o q sp : Z) (ret : word) (l ol : list Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 q -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_P m o (BN l 0) -> bn_at SEGS_P m q (BN ol 0) -> ok l -> ok ol -> zlen l <= 127 -> 1 <= zlen ol <= 3 ->
  96 <= sp -> sp <= 2 ^ 62 -> 0 <= o -> o + 516 <= 2 ^ 62 -> 0 <= q -> q + 516 <= 2 ^ 62 ->
  (q + 516 <= o \/ o + 516 <= q) -> (o + 516 <= sp - 80 \/ sp <= o) -> (q + 516 <= sp - 80 \/ sp <= q) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 (sp - 80)) 80 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35df4) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_P m' o (BN (add_l 0 l ol) 0)
    /\ unch m m' [(o, o + 516); (sp - 80, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o q sp ret l ol R10 R11 R2 R1 Hret Hbo Hbq Hokl Hoko Hu Hn Hsp1 Hsp2 Ho1 Ho2 Hq1 Hq2 Hdj Hdo Hdq Hsto Hsts.
  destruct Hbo as (Cu & Ce & Carr & _ & _). destruct Hbq as (Cn & Cqe & Carro & _ & _). cbn [cells BnModel.ex] in *.
  remember (zlen l) as u eqn:Eu. remember (zlen ol) as n eqn:En.
  assert (Hul : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity). assert (Hnl : Z.of_nat (length ol) = n) by (rewrite En; reflexivity).
  pose proof (zlen_nonneg l) as Hu0. rewrite <- Eu in Hu0.
  pose proof (u64_range ret) as W1. pose proof (u64_range (getr regs 8%bv)) as W8. pose proof (u64_range (getr regs 9%bv)) as W9.
  pose proof (u64_range (getr regs 18%bv)) as W18. pose proof (u64_range (getr regs 19%bv)) as W19. pose proof (u64_range (getr regs 20%bv)) as W20.
  pose proof (u64_range (getr regs 21%bv)) as W21. pose proof (u64_range (getr regs 22%bv)) as W22. pose proof (u64_range (getr regs 23%bv)) as W23.
  pose proof (u64_range (getr regs 24%bv)) as W24.
  (* [comment removed for export] *)
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (96, 2 ^ 62)]) (@nil kcell) [KW (ZV 34) (-80) 0])
    20%nat [0x35e28] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34)]) [o; q; sp]
    constr:([Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (96, 2 ^ 62)]) regs m rom 0x35df4.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I). zx_name regs1.
  set (m1 := wbytes _ _ _) in ZM.
  assert (U01s : unch m m1 [(sp - 80, sp)]) by (unfold m1; unchx).
  assert (U01 : unch m m1 [(o, o + 516); (sp - 80, sp)]) by (unfold m1; unchx).
  assert (G01 : mem_grows m m1) by (unfold m1; growsx).
  assert (SAV : cellN SEGS_P m1 (sp - 8) 8 (bv_unsigned ret) /\ cellN SEGS_P m1 (sp - 16) 8 (bv_unsigned (getr regs 8%bv))
    /\ cellN SEGS_P m1 (sp - 24) 8 (bv_unsigned (getr regs 9%bv)) /\ cellN SEGS_P m1 (sp - 32) 8 (bv_unsigned (getr regs 18%bv))
    /\ cellN SEGS_P m1 (sp - 40) 8 (bv_unsigned (getr regs 19%bv)) /\ cellN SEGS_P m1 (sp - 48) 8 (bv_unsigned (getr regs 20%bv))
    /\ cellN SEGS_P m1 (sp - 56) 8 (bv_unsigned (getr regs 21%bv)) /\ cellN SEGS_P m1 (sp - 64) 8 (bv_unsigned (getr regs 22%bv))
    /\ cellN SEGS_P m1 (sp - 72) 8 (bv_unsigned (getr regs 23%bv)) /\ cellN SEGS_P m1 (sp - 80) 8 (bv_unsigned (getr regs 24%bv))).
  { clear ZE ZR ZF ZM Cu Ce Carr Cn Cqe Carro Hdj Hdo Hdq Hsto Hsts U01s U01 G01. unfold m1. pose proof (u64_range (getr regs 1%bv)). rewrite <- R1. repeat split; cellx. }
  destruct SAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (9%bv : reg) as A9. zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (2%bv : reg) as A2.
  assert (K1 : keeps [3; 4; 25; 26; 27] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M1. clear ZE ZR ZF.
  assert (Cu1 : cellN SEGS_P m1 o 2 u).
  { eapply cellN_unch; [exact U01s | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
  assert (Ce1 : cellN SEGS_P m1 (o + 2) 2 0).
  { eapply cellN_unch; [exact U01s | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce]. }
  assert (Cn1 : cellN SEGS_P m1 q 2 n).
  { eapply cellN_unch; [exact U01s | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cn]. }
  assert (Cqe1 : cellN SEGS_P m1 (q + 2) 2 0).
  { eapply cellN_unch; [exact U01s | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cqe]. }
  assert (Carr1 : arr32 SEGS_P m1 (o + 4) l).
  { eapply arr32_unch; [exact U01s | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Carr]. }
  assert (Carro1 : arr32 SEGS_P m1 (q + 4) ol).
  { eapply arr32_unch; [exact U01s | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Carro]. }
  assert (Hsto1 : RiscvSemantics.store_ok SEGS_P m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G01 | exact Hsto]).
  (* [comment removed for export] *)
  assert (P2 : exists regs2,
    msteps SEGS_P (mkst regs1 (Z_to_bv 64 0x35e28) m1 rom) (mkst regs2 (Z_to_bv 64 0x35fb0) m1 rom)
    /\ getr regs2 5%bv = Z_to_bv 64 (o + 4) /\ getr regs2 9%bv = Z_to_bv 64 (q + 4) /\ getr regs2 13%bv = Z_to_bv 64 0
    /\ getr regs2 21%bv = Z_to_bv 64 0 /\ getr regs2 15%bv = Z_to_bv 64 0 /\ getr regs2 16%bv = Z_to_bv 64 0
    /\ getr regs2 12%bv = Z_to_bv 64 0 /\ getr regs2 11%bv = Z_to_bv 64 u /\ getr regs2 6%bv = Z_to_bv 64 (n * 4)
    /\ getr regs2 10%bv = Z_to_bv 64 MASK /\ getr regs2 14%bv = Z_to_bv 64 0 /\ getr regs2 17%bv = Z_to_bv 64 0
    /\ getr regs2 18%bv = Z_to_bv 64 0 /\ getr regs2 19%bv = Z_to_bv 64 0 /\ getr regs2 20%bv = Z_to_bv 64 u
    /\ getr regs2 8%bv = Z_to_bv 64 o /\ getr regs2 2%bv = Z_to_bv 64 (sp - 80)
    /\ keeps [3; 4; 25; 26; 27] regs1 regs2).
  { destruct (Z_lt_dec n u) as [Hlt|Hge].
    - zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (96, 2 ^ 62); Some (0, 127); Some (1, 3)])
          [KC (ZV 32) 2 2 (ZL 0); KC (ZV 33) 2 2 (ZL 0); KC (ZV 32) 0 2 (ZV 35); KC (ZV 33) 0 2 (ZV 36)] (@nil kwin))
        80%nat [0x35fb0; 0x36010] (SCR [true] []) constr:([(8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-80)))])
        [o; q; sp; u; n] constr:([Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (96, 2 ^ 62); Some (0, 127); Some (1, 3)]) regs1 m1 rom 0x35e28.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Ce1; kc1 Cqe1; kc1 Cu1; kc1 Cn1; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      exists regs2. split; [exact ZM|].
      repeat match goal with |- _ /\ _ => split; [zx_regv ZR; unfold MASK; f_equal; lia|] end.
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
    - zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (96, 2 ^ 62); Some (0, 127); Some (1, 3)])
          [KC (ZV 32) 2 2 (ZL 0); KC (ZV 33) 2 2 (ZL 0); KC (ZV 32) 0 2 (ZV 35); KC (ZV 33) 0 2 (ZV 36)] (@nil kwin))
        80%nat [0x35fb0; 0x36010] (SCR [false] []) constr:([(8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-80)))])
        [o; q; sp; u; n] constr:([Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (96, 2 ^ 62); Some (0, 127); Some (1, 3)]) regs1 m1 rom 0x35e28.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Ce1; kc1 Cqe1; kc1 Cu1; kc1 Cn1; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      exists regs2. split; [exact ZM|].
      repeat match goal with |- _ /\ _ => split; [zx_regv ZR; unfold MASK; f_equal; lia|] end.
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  destruct P2 as (regs2 & M2 & D5 & D9 & D13 & D21 & D15 & D16 & D12 & D11 & D6 & D10 & D14 & D17 & D18 & D19 & D20 & D8 & D2 & K2).
  (* [comment removed for export] *)
  destruct ol as [|y0 ol'] eqn:Eol; [rewrite zlen_nil in En; lia|]. rewrite <- Eol in * |- *.
  destruct (add_loop_P rom ol [] l [] 0 regs2 m1 o q u) as (regs3 & m3 & S & M3 & Harr3 & E12 & E28 & HS & HS2 & E21 & E15 & E16 & E13 & K3 & U3 & G3);
    cbn [length Z.of_nat]; rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.add_0_l, ?Hnl.
  { reflexivity. } { exact D5. } { exact D9. } { exact D13. } { exact D21. } { exact D15. } { exact D16. } { exact D12. } { exact D11. }
  { exact D6. } { exact D10. } { lia. } { lia. } { lia. } { exact Hokl. } { exact Hoko. } { rewrite Eol; congruence. } { lia. }
  { lia. } { lia. } { lia. } { lia. } { exact Hdj. } { exact Carr1. } { exact Carro1. } { exact Hsto1. }
  cbn [app] in Harr3. cbn [length Z.of_nat] in E13, E21, E15, E16, U3.
  rewrite ?Z.add_0_l, ?Hnl in E13. rewrite ?Z.add_0_l, ?Hnl in E21. rewrite ?Z.add_0_l, ?Hnl in E15. rewrite ?Z.add_0_l, ?Hnl in E16.
  rewrite ?Z.mul_0_r, ?Z.add_0_r, ?Z.add_0_l, ?Hnl in U3.
  pose proof (addm_bounds ol l 0 Hokl Hoko ltac:(lia)) as [Hokr Hc'].
  pose proof (addm_length ol l 0) as Hlenr.
  remember (fst (addm 0 l ol)) as r eqn:Er. remember (snd (addm 0 l ol)) as c' eqn:Ec'.
  assert (Hst : exists k, Z.of_nat (length (skipn (length ol) l)) = k /\ Z.max u n = n + k) by (eexists; split; [reflexivity|]; rewrite length_skipn; lia).
  destruct Hst as (kk & Hkk & Hmaxk).
  assert (Hsto3 : RiscvSemantics.store_ok SEGS_P m3 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G3 | exact Hsto1]).
  assert (E8 : getr regs3 8%bv = Z_to_bv 64 o) by (etransitivity; [exact (K3 8 ltac:(cbn; tauto)) | exact D8]).
  assert (E14 : getr regs3 14%bv = Z_to_bv 64 0) by (etransitivity; [exact (K3 14 ltac:(cbn; tauto)) | exact D14]).
  assert (E17 : getr regs3 17%bv = Z_to_bv 64 0) by (etransitivity; [exact (K3 17 ltac:(cbn; tauto)) | exact D17]).
  assert (E18 : getr regs3 18%bv = Z_to_bv 64 0) by (etransitivity; [exact (K3 18 ltac:(cbn; tauto)) | exact D18]).
  assert (E19 : getr regs3 19%bv = Z_to_bv 64 0) by (etransitivity; [exact (K3 19 ltac:(cbn; tauto)) | exact D19]).
  assert (E20 : getr regs3 20%bv = Z_to_bv 64 u) by (etransitivity; [exact (K3 20 ltac:(cbn; tauto)) | exact D20]).
  assert (E11 : getr regs3 11%bv = Z_to_bv 64 u) by (etransitivity; [exact (K3 11 ltac:(cbn; tauto)) | exact D11]).
  assert (E10 : getr regs3 10%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (K3 10 ltac:(cbn; tauto)) | exact D10]).
  assert (E2 : getr regs3 2%bv = Z_to_bv 64 (sp - 80)) by (etransitivity; [exact (K3 2 ltac:(cbn; tauto)) | exact D2]).
  (* [comment removed for export] *)
  assert (A : exists regs5 m5 p,
    msteps SEGS_P (mkst regs3 (Z_to_bv 64 0x35fc0) m3 rom) (mkst regs5 (Z_to_bv 64 0x35fd8) m5 rom)
    /\ arr32 SEGS_P m5 (o + 4) (add_l 0 l ol) /\ Z.max u p = zlen (add_l 0 l ol) /\ 0 <= p <= 128
    /\ getr regs5 21%bv = Z_to_bv 64 p /\ getr regs5 20%bv = Z_to_bv 64 u /\ getr regs5 8%bv = Z_to_bv 64 o /\ getr regs5 2%bv = Z_to_bv 64 (sp - 80)
    /\ keeps [3; 4; 25; 26; 27] regs3 regs5
    /\ unch m3 m5 [(o + 4, o + 516)] /\ mem_grows m3 m5).
  { rewrite (add_l_addm ol l 0), <- Er, <- Ec'. unfold MASK in E10.
    destruct (Z.eq_dec c' 0) as [Hc0 | Hc1].
    - (* [comment removed for export] *)
      rewrite Hc0 in *. replace (addc_l 0 (skipn (length ol) l)) with (skipn (length ol) l) by (destruct (skipn (length ol) l); reflexivity).
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 3); Some (0, 2 ^ 30)]) (@nil kcell) (@nil kwin))
        30%nat [0x35fd8; 0x36054] (SCR [false] [])
        constr:([(18%bv : reg, ZL 0); (19%bv : reg, ZL 0); (28%bv : reg, ZV 34); (15%bv : reg, ZSub (ZL 0) (ZV 33)); (16%bv : reg, ZSub (ZL 0) (ZV 33));
                 (14%bv : reg, ZL 0); (17%bv : reg, ZL 0); (8%bv : reg, ZV 32); (13%bv : reg, ZMul (ZV 33) (ZL 4))])
        [o; n; S] constr:([Some (0, 2 ^ 62); Some (1, 3); Some (0, 2 ^ 30)]) regs3 m3 rom 0x35fc0.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs5.
      eexists regs5, m3, n. split; [exact ZM|].
      split; [exact Harr3|].
      split; [rewrite zlen_app; unfold zlen; rewrite Hlenr; unfold zlen in Hkk; lia|].
      split; [lia|].
      split; [zx_regv ZR|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (20%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E20]|].
      split; [zx_regv ZR|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E2]|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [apply unch_refl | apply mem_grows_refl].
    - (* [comment removed for export] *)
      assert (Hc'1 : c' = 1) by lia. rewrite Hc'1 in *.
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 3); Some (0, 2 ^ 30)]) (@nil kcell) (@nil kwin))
        30%nat [0x35fd8; 0x36054] (SCR [true] [])
        constr:([(18%bv : reg, ZL 0); (19%bv : reg, ZL 0); (28%bv : reg, ZV 34); (15%bv : reg, ZSub (ZL 0) (ZV 33)); (16%bv : reg, ZSub (ZL 0) (ZV 33));
                 (14%bv : reg, ZL 0); (17%bv : reg, ZL 0); (8%bv : reg, ZV 32); (13%bv : reg, ZMul (ZV 33) (ZL 4))])
        [o; n; S] constr:([Some (0, 2 ^ 62); Some (1, 3); Some (0, 2 ^ 30)]) regs3 m3 rom 0x35fc0.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs4.
      assert (Harr4 : arr32 SEGS_P m3 (o + 4 + 4 * n) (skipn (length ol) l)).
      { replace (o + 4 + 4 * n) with (o + 4 + 4 * Z.of_nat (length r)) by (rewrite Hlenr; lia). apply arr32_skip. exact Harr3. }
      destruct (addc_loop_P rom (skipn (length ol) l) n 1 regs4 m3 o u) as (regs5 & m5 & k & M5 & Harr5 & Hk & Hlen5 & F21 & K5 & U5 & G5).
      { zx_regv ZR. } { etransitivity; [exact (reg_kept _ _ _ _ (11%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E11]. }
      { zx_regv ZR. } { zx_regv ZR. }
      { etransitivity; [exact (reg_kept _ _ _ _ (10%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E10]. }
      { zx_regv ZR. }
      { unfold zlen. rewrite Hkk. lia. } { lia. } { lia. } { unfold zlen. rewrite Hkk. lia. }
      { apply ok_skipn. exact Hokl. }
      { lia. } { lia. } { lia. } { exact Harr4. } { exact Hsto3. }
      assert (Hkb : k <= kk + 1).
      { destruct (addc_l_len_cases (skipn (length ol) l) 1 (ok_skipn _ _ Hokl) ltac:(lia)) as (k' & Hk' & Hlen' & Hkb'). unfold zlen in *. rewrite Hkk in *. lia. }
      eexists regs5, m5, (n + k). split; [eapply msteps_trans; [exact ZM | exact M5]|].
      split.
      { apply arr32_app.
        - eapply arr32_unch; [exact U5 | lia | rewrite Hlenr; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; rewrite Hlenr; lia |].
          eapply arr32_prefix. exact Harr3.
        - rewrite Hlenr, Hnl. exact Harr5. }
      split; [rewrite zlen_app, Hlen5; unfold zlen in *; rewrite Hlenr, Hkk; lia|].
      split; [unfold zlen in *; rewrite Hkk in Hlen5; lia|].
      split; [exact F21|].
      split; [etransitivity; [exact (K5 20 ltac:(cbn; tauto)) |]; etransitivity; [exact (reg_kept _ _ _ _ (20%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E20]|].
      split; [etransitivity; [exact (K5 8 ltac:(cbn; tauto)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K5 2 ltac:(cbn; tauto)) |]; etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact E2]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity]|].
      split; [|exact G5].
      eapply unch_widen; [exact U5|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]].
      eexists; split; [left; reflexivity|]. cbn. unfold zlen in *. rewrite Hkk in Hlen5. lia. }
  destruct A as (regs5 & m5 & p & M5 & Harr5 & Hmax5 & Hp & F21 & F20 & F8 & F2 & K5 & U5 & G5).
  assert (U15 : unch m1 m5 [(o + 4, o + 516)]).
  { eapply unch_trans; [|exact U5]. eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia. }
  assert (SAV5 : forall a v, cellN SEGS_P m1 a 8 v -> sp - 80 <= a -> a + 8 <= sp -> cellN SEGS_P m5 a 8 v).
  { intros a v C Ha1 Ha2. eapply cellN_unch; [exact U15 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact C]. }
  (* [comment removed for export] *)
  destruct (fin_add_P rom regs5 m5 o sp u p ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv)
              (getr regs 21%bv) (getr regs 22%bv) (getr regs 23%bv) (getr regs 24%bv))
    as (regs6 & m6 & M6 & Cu6 & G2' & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & K6 & U6 & G6);
    try (apply SAV5; [assumption | lia | lia]).
  { exact F8. } { exact F2. } { exact F20. } { exact F21. } { exact Hret. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Hdo. }
  { eapply store_ok_grows; [exact G5 | exact Hsto3]. }
  eexists regs6, m6. split.
  { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M5 | exact M6]. }
  split.
  { intros rg Hrg. cbn in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ etransitivity; [exact G2' | symmetry; exact R2] | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 | exact G21 | exact G22 | exact G23 | exact G24
            | lazymatch goal with |- getr _ (Z_to_bv 5 ?nn) = _ =>
                etransitivity; [exact (K6 nn ltac:(cbn; tauto))|]; etransitivity; [exact (K5 nn ltac:(cbn; tauto))|];
                etransitivity; [exact (K3 nn ltac:(cbn; tauto))|]; etransitivity; [exact (K2 nn ltac:(cbn; tauto))|]; exact (K1 nn ltac:(cbn; tauto)) end ]. }
  split.
  { split; [|split; [|split; [|split; [cbn; lia | cbn [cells]; rewrite <- Hmax5; lia]]]]; cbn [cells BnModel.ex].
    - rewrite <- Hmax5. exact Cu6.
    - eapply cellN_unch; [exact U6 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      eapply cellN_unch; [exact U15 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce1].
    - unfold zlen in Hmax5. eapply arr32_unch; [exact U6 | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Harr5]. }
  split.
  { eapply unch_trans; [exact U01|]. eapply unch_trans.
    - eapply unch_widen; [exact U15|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
    - eapply unch_widen; [exact U6|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia. }
  eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G3|]. eapply mem_grows_trans; [exact G5 | exact G6].
Qed.

End S.
