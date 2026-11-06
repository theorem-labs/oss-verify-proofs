(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_mul1 BnA_mul2 BnA_mul3.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

Lemma five_tbl_nth : forall r, 1 <= r <= 12 -> nth (Z.to_nat (r - 1)) five_tbl 0 = 5 ^ r.
Proof.
  intros r Hr.
  assert (H : forallb (fun k => nth k five_tbl 0 =? 5 ^ (Z.of_nat k + 1)) (seq 0 12) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (r - 1)) ltac:(apply in_seq; lia)) as H1. cbn beta in H1.
  apply Z.eqb_eq in H1. rewrite H1. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma five_tbl_A0 : arr32 SEGS_A (fun _ => None) 145344 five_tbl.
Proof.
  assert (H : forallb (fun k => match rdn SEGS_A (fun _ => None) (Z_to_bv 64 (145344 + 4 * Z.of_nat k)) 4 with
                                | Some bs => bytes_le_to_Z bs =? nth k five_tbl 0 | None => false end) (seq 0 12) = true)
    by (vm_compute; reflexivity).
  intros i Hi. unfold five_tbl in Hi. cbn [length] in Hi.
  pose proof (proj1 (forallb_forall _ _) H i ltac:(apply in_seq; lia)) as Hk. cbn beta in Hk. unfold cellN.
  destruct (rdn SEGS_A _ _ 4) as [bs|]; [|discriminate]. exists bs. split; [reflexivity|]. apply Z.eqb_eq. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Definition tbl_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 11; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].

#[using="Type"] Lemma tbl_A : forall regs m (o r : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 r ->
  getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 13%bv = Z_to_bv 64 SHA -> getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) ->
  0 <= r < 13 -> bn_at SEGS_A m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  arr32 SEGS_A m 145344 five_tbl -> tblsh m ->
  APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa8c0) m rom) (mkst regs' (Z_to_bv 64 0x0aa9b8) m' rom)
    /\ (let b' := (if 0 <? r then mul32 (kFive r) b else b) in
        bn_at SEGS_A m' o b' /\ getr regs' 16%bv = Z_to_bv 64 (zlen (cells b'))
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b /\ val (cells b') < B ^ 124)
    /\ keeps tbl_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o r b R10 R12 R15 R13 R14 Hr Hbn Hok Hn Hne Hv Htbl TSH Ho1 Ho2 Ho8 OSH Hsto.
  pose proof (cap_bound (cells b) r 0 Hok Hn ltac:(lia) ltac:(lia) Hv (five0_ge r ltac:(lia))) as Hcap.
  pose proof Hbn as Hbn0. destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  assert (Hl1 : 1 <= zlen (cells b)) by (destruct (cells b); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen (cells b)) as u eqn:Eu. assert (Hlen' : Z.of_nat (length (cells b)) = u) by (rewrite Eu; reflexivity).
  assert (Hv0 : val (cells b) < B ^ 124) by (pose proof (val_nonneg _ Hok); pose proof (Z.pow_pos_nonneg 5 r ltac:(lia) ltac:(lia)); nia).
  remember (B ^ 124) as TOP eqn:ETOP. clear ETOP.
  destruct (Z.eq_dec r 0) as [-> | Hr0].
  - (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 124)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 33)] (@nil kwin))
      20%nat [0x0aa9b8] (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZL 0); (13%bv : reg, ZL SHA); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))]) [o; u]
      constr:([Some (IMG, HIE - 516); Some (1, 124)]) regs m rom 0x0aa8c0.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; kc1 Cu; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
    eexists regs1, m. split; [exact ZM|]. replace (0 <? 0) with false by reflexivity. cbn zeta.
    split; [|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply unch_refl | apply mem_grows_refl]]].
    split; [exact Hbn0|]. split; [rewrite <- Eu; zx_regv ZR|]. repeat split; auto.
  - (* [comment removed for export] *)
    replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). cbn zeta.
    assert (HF : kFive r = 5 ^ r) by reflexivity.
    assert (HF5 : 5 <= 5 ^ r) by (change 5 with (5 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
    assert (HF12 : 5 ^ r <= 244140625) by (change 244140625 with (5 ^ 12); apply Z.pow_le_mono_r; lia).
    assert (Hcell : exists bs, rdn SEGS_A m (Z_to_bv 64 (145340 + 4 * r)) 4 = Some bs /\ bytes_le_to_Z bs = 5 ^ r).
    { rewrite <- (five_tbl_nth r) by lia. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (r - 1))); [exact Htbl | cbn; lia | lia | reflexivity]. }
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 124); Some (1, 12); Some (5, 244140625)])
        [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 33)] (@nil kwin))
      40%nat [0x0aa950] (SCR [] [ZL 0; ZV 35])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 34); (15%bv : reg, ZL 268435455); (13%bv : reg, ZL SHA); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
      [o; u; r; 5 ^ r]
      constr:([Some (IMG, HIE - 516); Some (1, 124); Some (1, 12); Some (5, 244140625)]) regs m rom 0x0aa8c0.
    zx_use2 ZXB ltac:(unfold MASK in *; zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; kc1 Cu; exact I) ltac:(exact I)
      ltac:(idtac; zx_scs ltac:(first [ destruct Hcell as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                     | apply (cellN_eqa _ _ _ _ _ _ _ (TSH ((145340 + 4 * r) / 8 - 18168) ltac:(lia))); [lia|reflexivity] ])).
    zx_name regs1.
    assert (K1 : keeps tbl_keep regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (7%bv : reg) as A7. zx_reg ZR (17%bv : reg) as A17.
    zx_reg ZR (6%bv : reg) as A6. zx_reg ZR (16%bv : reg) as A16.
    assert (A10 : getr regs1 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K1 10 ltac:(in_list)) | exact R10]).
    assert (A15 : getr regs1 15%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (K1 15 ltac:(in_list)) | exact R15]).
    assert (A13 : getr regs1 13%bv = Z_to_bv 64 SHA) by (etransitivity; [exact (K1 13 ltac:(in_list)) | exact R13]).
    assert (A14 : getr regs1 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (etransitivity; [exact (K1 14 ltac:(in_list)) | exact R14]).
    rename ZM into M1. clear ZE ZR ZF.
    (* [comment removed for export] *)
    unfold mul32. rewrite HF. replace (5 ^ r =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (5 ^ r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct b as [l exb]; cbn [cells BnModel.ex] in *. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
    pose proof (mul32_l_spec (5 ^ r) l 0 Hok ltac:(lia) ltac:(lia)) as SP.
    destruct (mul32_l (5 ^ r) 0 l) as [rr c] eqn:Em. destruct SP as (Hval & Hokr & Hlenr & Hc0' & HcF). specialize (HcF ltac:(lia)).
    destruct (mtb_loop_A rom l [] 0 regs1 m (o + 4) (5 ^ r)) as (regs2 & m2 & tmp & M2 & Harr2 & C17 & C28 & HT1 & HT2 & K2 & U2 & G2);
      cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
    { exact A12. } { exact A5. } { rewrite A7. f_equal. lia. } { exact A17. } { exact A6. } { exact A15. } { exact A13. }
    { lia. } { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { replace (o + 4 - 4) with o by lia. exact Ho8. }
    { replace (o + 4 - 4) with o by lia. exact OSH. } { lia. } { exact Carr. }
    { eapply sc_store_in; [exact Hsto|]. zwidth. lia. }
    rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
    cbn [length app Z.of_nat] in U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
    assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 10 ltac:(in_list)) | exact A10]).
    assert (C16 : getr regs2 16%bv = Z_to_bv 64 u) by (etransitivity; [exact (K2 16 ltac:(in_list)) | exact A16]).
    assert (C15 : getr regs2 15%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (K2 15 ltac:(in_list)) | exact A15]).
    assert (C13 : getr regs2 13%bv = Z_to_bv 64 SHA) by (etransitivity; [exact (K2 13 ltac:(in_list)) | exact A13]).
    assert (C14 : getr regs2 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (etransitivity; [exact (K2 14 ltac:(in_list)) | exact A14]).
    assert (Hsto2 : RiscvSemantics.store_ok SEGS_A m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
    assert (Cu2 : cellN SEGS_A m2 o 2 u).
    { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
    assert (Ce2 : cellN SEGS_A m2 (o + 2) 2 exb).
    { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce]. }
    assert (OSH2 : objsh m2 o).
    { eapply (objsh_unch m _ _); [exact U2 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
    (* [comment removed for export] *)
    assert (HcB : 0 <= c < B ^ Z.of_nat 3) by (change (B ^ Z.of_nat 3) with (2 ^ 84); lia).
    destruct (chunks_spec 3 c HcB) as (Hcv & Hcok & Hcn & Hck).
    assert (POSTV : ok (rr ++ chunks 3 c) /\ norm (rr ++ chunks 3 c) /\ rr ++ chunks 3 c <> [] /\ exb = exb /\ val (rr ++ chunks 3 c) < TOP).
    { pose proof (mul32_spec (5 ^ r) (BN l exb) Hok Hn ltac:(lia)) as SP3. unfold mul32 in SP3. cbn [cells BnModel.ex] in SP3.
      replace (5 ^ r =? 1) with false in SP3 by (symmetry; apply Z.eqb_neq; lia).
      replace (5 ^ r =? 0) with false in SP3 by (symmetry; apply Z.eqb_neq; lia).
      rewrite El, <- El, Em in SP3. cbn [cells BnModel.ex] in SP3. destruct SP3 as (S1 & S2 & S3 & _).
      repeat split; auto; [destruct rr; [destruct (chunks 3 c)|]; cbn; try congruence; destruct l; [congruence|]; unfold zlen in Hlenr; cbn in Hlenr; lia | ].
      rewrite S3. pose proof (val_nonneg _ Hok). nia. }
    destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
    + (* [comment removed for export] *)
      rewrite Hc0 in *. rewrite chunks_0, app_nil_r in *.
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 124); Some (0, 2 ^ 28 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 33)] (@nil kwin))
        20%nat [0x0aa9b8; 0x0aaadc] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (28%bv : reg, ZV 34); (13%bv : reg, ZL SHA); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))]) [o; u; tmp]
        constr:([Some (IMG, HIE - 516); Some (1, 124); Some (0, 2 ^ 28 - 1)]) regs2 m2 rom 0x0aa9a0.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH2 0; kc1 Cu2; exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact ZM]|].
      split.
      { cbn [cells BnModel.ex]. split; [|split; [rewrite Hlenr, <- Eu; zx_regv ZR | exact POSTV]].
        split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
        - rewrite Hlenr, <- Eu. exact Cu2.
        - exact Ce2.
        - exact Harr2. }
      split; [eapply keeps_trans; [exact K1|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|];
              eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [|exact G2].
      eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
    + (* [comment removed for export] *)
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 124); Some (2 ^ 28, 2 ^ 60 - 1)]) (@nil kcell) (@nil kwin))
        10%nat [0x0aa9b8; 0x0aaadc] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (28%bv : reg, ZV 34)]) [o; u; tmp]
        constr:([Some (IMG, HIE - 516); Some (1, 124); Some (2 ^ 28, 2 ^ 60 - 1)]) regs2 m2 rom 0x0aa9a0.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      assert (K3' : keeps tbl_keep regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      assert (K3 : keeps [10; 16; 17; 14; 15; 13] regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      rename ZM into M3. clear ZE ZR ZF.
      assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63))).
      { unfold B. exists 1, (268435456 - 1); lia. }
      destruct Hcls as (clo & chi & Hcc & Hcls).
      destruct (cartb_A rom regs3 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & E16 & K4 & U4 & G4).
      { etransitivity; [exact (K3 10 ltac:(in_list)) | exact C10]. } { etransitivity; [exact (K3 16 ltac:(in_list)) | exact C16]. }
      { etransitivity; [exact (K3 17 ltac:(in_list)) | exact C17]. } { etransitivity; [exact (K3 14 ltac:(in_list)) | exact C14]. }
      { etransitivity; [exact (K3 15 ltac:(in_list)) | exact C15]. } { etransitivity; [exact (K3 13 ltac:(in_list)) | exact C13]. }
      { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact OSH2. } { exact Harr2. } { exact Hsto2. }
      eexists regs4, m4. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4]|].
      split.
      { cbn [cells BnModel.ex]. split; [|split; [rewrite zlen_app, Hlenr, <- Eu; exact E16 | exact POSTV]].
        split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
        - rewrite zlen_app, Hlenr, <- Eu. exact Cu4.
        - eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Ce2].
        - exact Harr4. }
      split.
      { eapply keeps_trans; [exact K1|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
        eapply keeps_trans; [exact K3'|]. eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
      split; [|eapply mem_grows_trans; [exact G2 | exact G4]].
      apply (unch_trans m m2 m4).
      * eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
      * eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]].
        -- eexists; split; [left; reflexivity|cbn; lia].
        -- eexists; split; [right; left; reflexivity|cbn; lia].
Qed.

End S.
