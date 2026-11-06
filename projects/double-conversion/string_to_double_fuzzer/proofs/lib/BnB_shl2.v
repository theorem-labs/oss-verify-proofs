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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnA_shl BnB_lib BnB_shl1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

#[using="Type"] Theorem shl_B : forall regs m (o n sp : Z) (ret : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 n -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0 <= n < 2048 -> bn_at SEGS_B m o b -> ok (cells b) -> zlen (cells b) <= 126 -> ex b + n / 28 < 2 ^ 15 ->
  KHI + 16 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 16 \/ sp <= o) ->
  shcellsB m -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab154) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_B m' o (shl n b)
    /\ unch m m' [(o, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o n sp ret b R10 R11 R2 R1 Hret Hn Hbn Hok Hlen Hex Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj [SC1 SC2] OSH Hsto Hsts.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  pose proof (u64_range ret) as Rret.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  remember (cells b) as l eqn:El.
  hide Hdisj.
  destruct l as [|x t].
  - (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (0, 0)])
                              [KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA);
                               KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 35)] [KW (ZV 34) (-16) 0])
      40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34)])
      [o; n; sp; 0] constr:([Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (0, 0)]) regs m rom 0x0ab154.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; exact I)
      ltac:(kw1 Hsts; exact I)
      ltac:(unhide; zx_scs ltac:(lia)).
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H, <- R1; apply Z_to_bv_bv_unsigned).
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    clear ZM ZE ZR ZF. unhide.
    split; [|split; [unchx|growsx]].
    unfold shl. rewrite <- El. cbn [cells BnModel.ex]. unfold bn_at. rewrite <- El.
    split; [cellN_go|split; [cellN_go|split; [|split; [exact Hexr| unfold zlen; cbn; lia]]]].
    apply arr32_nil.
  - (* [comment removed for export] *)
    apply ok_cons in Hok as Hok0. destruct Hok0 as [Hx Hokt].
    assert (Hus : 1 <= zlen (x :: t) <= 126) by (rewrite zlen_cons in *; pose proof (zlen_nonneg t); lia).
    remember (zlen (x :: t)) as u eqn:Hu. unfold zlen in Hu. cbn [length] in Hu.
    (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1)])
                              [KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA);
                               KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 32) (ZL 2)) 3) SHA 1 (ZL 0);
                               KC (ZV 32) 0 2 (ZV 35); KC (ZV 32) 2 2 (ZV 36)] [KW (ZV 34) (-16) 0])
      40%nat [0x0ab1b8] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34)])
      [o; n; sp; u; ex b] constr:([Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1)]) regs m rom 0x0ab154.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kcsh OSH 0; kc1 Cu; kc1 Ce; exact I)
      ltac:(kw1 Hsts; exact I)
      ltac:(unhide; zx_scs ltac:(lia)).
    zx_reg ZR (16%bv : reg) as A16. fold (magic28A n) in A16. rewrite (magic28A_ok n) in A16 by lia.
    zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (13%bv : reg) as A13. zx_reg ZR (12%bv : reg) as A12.
    zx_reg ZR (14%bv : reg) as A14. zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11.
    zx_reg ZR (2%bv : reg) as A2. zx_reg ZR (15%bv : reg) as A15.
    set (m1 := wbytes m _ _) in ZM.
    assert (K1 : keeps CS' regs regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. rename ZM into M1. rename regs0 into regs1.
    (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73)])
                              [] [KW (ZV 32) 0 516])
      40%nat [0x0ab1e0] (SCR [] []) constr:([(16%bv : reg, ZV 37); (17%bv : reg, ZV 36); (13%bv : reg, ZV 35); (12%bv : reg, ZAdd (ZV 32) (ZL 2));
        (10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-16))); (15%bv : reg, ZL SHA);
        (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
      [o; n; sp; u; ex b; n / 28] constr:([Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73)]) regs1 m1 rom 0x0ab1b8.
    assert (Hsto1 : RiscvSemantics.store_ok SEGS_B m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [|exact Hsto]; unfold m1; growsx).
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto1; exact I) ltac:(exact I).
    zx_reg ZR (12%bv : reg) as B12. zx_reg ZR (16%bv : reg) as B16. zx_reg ZR (13%bv : reg) as B13. zx_reg ZR (11%bv : reg) as B11.
    zx_reg ZR (10%bv : reg) as B10. zx_reg ZR (2%bv : reg) as B2. zx_reg ZR (15%bv : reg) as B15. zx_reg ZR (14%bv : reg) as B14.
    set (m2 := wbytes m1 _ _) in ZM.
    assert (K2 : keeps CS' regs1 regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. rename ZM into M2. rename regs0 into regs2.
    assert (Hs : 0 <= n mod 28 < 28) by lia.
    (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73); Some (0, 27)])
                              [] [])
      40%nat [0x0ab204] (SCR [] []) constr:([(12%bv : reg, ZV 38); (16%bv : reg, ZSub (ZL 28) (ZV 38)); (13%bv : reg, ZV 35); (11%bv : reg, ZV 33);
        (10%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 34) (ZL (-16))); (15%bv : reg, ZL SHA); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
      [o; n; sp; u; ex b; n / 28; n mod 28] constr:([Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73); Some (0, 27)]) regs2 m2 rom 0x0ab1e0.
    zx_use2 ZXB ltac:(zx_pins; first [rewrite B12; f_equal; lia | rewrite B16; f_equal; lia]) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I).
    zx_reg ZR (11%bv : reg) as D11. zx_reg ZR (5%bv : reg) as D5. zx_reg ZR (6%bv : reg) as D6. zx_reg ZR (7%bv : reg) as D7.
    zx_reg ZR (12%bv : reg) as D12. zx_reg ZR (16%bv : reg) as D16. zx_reg ZR (15%bv : reg) as D15.
    zx_reg ZR (17%bv : reg) as D17. zx_reg ZR (10%bv : reg) as D10. zx_reg ZR (2%bv : reg) as D2. zx_reg ZR (13%bv : reg) as D13.
    zx_reg ZR (14%bv : reg) as D14.
    assert (K2' : keeps CS' regs2 regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. rename ZM into M2'. rename regs0 into regs2'.
    (* [comment removed for export] *)
    unhide.
    assert (Harr2 : arr32 SEGS_B m2 (o + 4) ([] ++ x :: t)).
    { cbn [app]. unfold m2, m1. apply arr32_store_other; zwidth; try lia.
      apply arr32_store_other; zwidth; try lia. exact Carr. }
    assert (OSH2 : objshB m2 o).
    { unfold m2, m1. eapply (objshB_unch m _ [(o, o + 516); (sp - 16, sp)]); [unchx | intros r0 [<-|[<-|[]]]; cbn; lia | lia | lia | exact OSH]. }
    destruct (shl_loop_B rom (x :: t) [] 0 regs2' m2 (o + 4) (n mod 28)) as (regs3 & m3 & M3 & Harr3 & C28 & K3 & U3 & G3);
      cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
    { rewrite D11; first [reflexivity | f_equal; lia]. }
    { rewrite D5; first [reflexivity | f_equal; lia]. }
    { rewrite D6. f_equal. lia. }
    { exact D7. }
    { exact D12. }
    { rewrite D16; first [reflexivity | f_equal; lia]. }
    { exact D15. }
    { exact Hs. }
    { split; [lia|]. apply Z.pow_pos_nonneg; lia. }
    { exact Hok. }
    { congruence. }
    { lia. }
    { lia. }
    { replace (o + 4 - 4) with o by lia. exact Ho8. }
    { replace (o + 4 - 4) with o by lia. exact OSH2. }
    { lia. }
    { exact Harr2. }
    { eapply sc_store_in; [eapply store_ok_grows; [|exact Hsto1]; unfold m2; growsx |]. cbn [length]. lia. }
    cbn [length app] in Harr3, U3. rewrite ?Z.mul_0_r, ?Z.add_0_r in U3.
    pose proof (shl_l_spec (n mod 28) (x :: t) 0 Hok Hs ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as SPEC.
    destruct (shl_l (n mod 28) 0 (x :: t)) as [r c'] eqn:Eshl. cbn [fst snd] in Harr3, C28.
    destruct SPEC as (_ & Hokr & Hlenr & Hc').
    assert (Hc'27 : c' < 2 ^ 27) by (assert (2 ^ (n mod 28) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia); lia).
    assert (Hlenr' : Z.of_nat (length r) = u) by (unfold zlen in Hlenr; cbn [length] in Hlenr; lia).
    (* [comment removed for export] *)
    assert (C13 : getr regs3 13%bv = Z_to_bv 64 u) by (etransitivity; [exact (K3 13 ltac:(in_list)) | exact D13]).
    assert (C10 : getr regs3 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K3 10 ltac:(in_list)) | exact D10]).
    assert (C2 : getr regs3 2%bv = Z_to_bv 64 (sp + -16)) by (etransitivity; [exact (K3 2 ltac:(in_list)) | exact D2]).
    assert (C17 : getr regs3 17%bv = Z_to_bv 64 (o + 4)) by (etransitivity; [exact (K3 17 ltac:(in_list)) | exact D17]).
    assert (C15 : getr regs3 15%bv = Z_to_bv 64 SHA) by (etransitivity; [exact (K3 15 ltac:(in_list)) | exact D15]).
    assert (C14 : getr regs3 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (etransitivity; [exact (K3 14 ltac:(in_list)) | exact D14]).
    assert (RA3 : cellN SEGS_B m3 (sp + -8) 8 (bv_unsigned ret)).
    { eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; unhide; lia |].
      unfold m2, m1. cbv [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite ?R1. cellN_go. }
    assert (OSH3 : objshB m3 o).
    { eapply (objshB_unch m2 _ _); [exact U3 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH2]. }
    assert (Hsto3 : RiscvSemantics.store_ok SEGS_B m3 (Z_to_bv 64 o) 516 = true).
    { eapply store_ok_grows; [exact G3|]. eapply store_ok_grows; [|exact Hsto1]. unfold m2; growsx. }
    (* [comment removed for export] *)
    assert (EXC : forall m', unch m3 m' [(o, o + 2); (o + 4 + 4 * u, o + 8 + 4 * u)] -> cellN SEGS_B m' (o + 2) 2 (ex b + n / 28)).
    { intros m' U. eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia |].
      eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      unfold m2. cellN_go. }
    assert (UNCH : forall m', unch m3 m' [(o, o + 516)] -> unch m m' [(o, o + 516); (sp - 16, sp)]).
    { intros m' U. apply (unch_trans m m3 m'); [|eapply unch_widen; [exact U|]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; eexists; split; [left; reflexivity|cbn; lia]].
      apply (unch_trans m m2 m3); [unfold m2, m1; unchx|].
      eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|cbn; lia]. }
    assert (KEEPS : forall regs4, keeps CS' regs3 regs4 -> getr regs4 2%bv = Z_to_bv 64 sp -> keeps CS regs regs4).
    { intros regs4 K4 S4. apply keeps_CS_of; [|rewrite S4, R2; reflexivity].
      eapply keeps_trans; [exact K1|]. eapply keeps_trans; [exact K2|]. eapply keeps_trans; [exact K2'|]. eapply keeps_trans; [|exact K4].
      eapply keeps_sub_dec; [exact K3|]. vm_compute. reflexivity. }
    assert (MS : forall st, msteps SEGS_B (mkst regs3 (Z_to_bv 64 0x0ab26c) m3 rom) st ->
                            msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab154) m rom) st).
    { intros st H. eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M2'|].
      eapply msteps_trans; [exact M3|]. exact H. }
    unfold shl. rewrite <- El, Eshl. unfold bn_at. cbn [cells BnModel.ex].
    clear M1 M2 M2' M3 Harr2 OSH2 K1 K2 K2' K3.
    clear A16 A17 A13 A12 A14 A10 A11 A2 A15 B12 B16 B13 B11 B10 B2 B15 B14 D11 D5 D6 D7 D12 D16 D15 D17 D10 D2 D13 D14.
    destruct (Z.eqb_spec c' 0) as [Hc0|Hc0].
    + (* [comment removed for export] *)
      zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (KHI + 16, HIE); Some (1, 126); Some (0, 0); Some (0, 18446744073709551615)])
          [KC (ZV 33) (-8) 8 (ZV 36); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 34) (ZL 4))) 3) SHA 1 (ZL 0)]
          [KW (ZV 32) 0 516])
        40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-16))); (13%bv : reg, ZV 34); (28%bv : reg, ZV 35);
          (17%bv : reg, ZAdd (ZV 32) (ZL 4)); (15%bv : reg, ZL SHA); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
        [o; sp; u; c'; bv_unsigned ret] constr:([Some (IMG, HIE - 516); Some (KHI + 16, HIE); Some (1, 126); Some (0, 0); Some (0, 18446744073709551615)]) regs3 m3 rom 0x0ab26c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA3; kcsh OSH3 0; kcsh OSH3 ((4 + 4 * u) / 8); exact I) ltac:(kw1 Hsto3; exact I) ltac:(exact I).
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (2%bv : reg) as E2.
      eexists regs0, m3. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
      split; [apply KEEPS; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | rewrite E2; f_equal; lia]|].
      clear ZM ZE ZR ZF. unhide.
      split; [|split; [apply UNCH; apply unch_refl | apply (mem_grows_trans m m2 m3); [unfold m2, m1; growsx | exact G3]]].
      split; [|split; [apply EXC; apply unch_refl|split; [exact Harr3|split; [lia| unfold zlen; rewrite Hlenr'; lia]]]].
      unfold zlen; rewrite Hlenr'.
      eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      unfold m2, m1. cellN_go.
    + (* [comment removed for export] *)
      zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (KHI + 16, HIE); Some (1, 126); Some (1, 2 ^ 27); Some (0, 18446744073709551615)])
          [KC (ZV 33) (-8) 8 (ZV 36); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 34) (ZL 4))) 3) SHA 1 (ZL 0)]
          [KW (ZV 32) 0 516])
        40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-16))); (13%bv : reg, ZV 34); (28%bv : reg, ZV 35);
          (17%bv : reg, ZAdd (ZV 32) (ZL 4)); (15%bv : reg, ZL SHA); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
        [o; sp; u; c'; bv_unsigned ret] constr:([Some (IMG, HIE - 516); Some (KHI + 16, HIE); Some (1, 126); Some (1, 2 ^ 27); Some (0, 18446744073709551615)]) regs3 m3 rom 0x0ab26c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA3; kcsh OSH3 0; kcsh OSH3 ((4 + 4 * u) / 8); exact I) ltac:(kw1 Hsto3; exact I)
        ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto3 | zwidth; lia])).
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (2%bv : reg) as E2.
      eexists regs0, _. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
      split; [apply KEEPS; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | rewrite E2; f_equal; lia]|].
      clear ZM ZE ZR ZF. unhide.
      split; [|split; [apply UNCH; unchx | eapply mem_grows_trans; [apply (mem_grows_trans m m2 m3); [unfold m2, m1; growsx | exact G3] | growsx]]].
      rewrite zlen_app. unfold zlen. cbn [length]. rewrite Hlenr'.
      split; [cellN_go|split; [apply EXC; unchx|split; [|lia]]].
      replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length r)) by lia.
      apply arr32_store_other; [lia | rewrite length_app; zwidth; lia | lia | zwidth; lia | rewrite length_app; zwidth; lia |].
      apply arr32_snoc'; try lia; [exact Harr3|].
      rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.

End S.
