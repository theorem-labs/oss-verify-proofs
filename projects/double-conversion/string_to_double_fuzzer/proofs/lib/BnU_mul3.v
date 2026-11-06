(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnU_mul BnU_mul1 BnU_mul2.
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
Definition five_tbl : list Z := [5; 25; 125; 625; 3125; 15625; 78125; 390625; 1953125; 9765625; 48828125; 244140625].

#[using="Type"] Lemma five_tbl_nth : forall r, 1 <= r <= 12 -> nth (Z.to_nat (r - 1)) five_tbl 0 = 5 ^ r.
Proof.
  intros r Hr.
  assert (H : forallb (fun k => nth k five_tbl 0 =? 5 ^ (Z.of_nat k + 1)) (seq 0 12) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (r - 1)) ltac:(apply in_seq; lia)) as H1. cbn beta in H1.
  apply Z.eqb_eq in H1. rewrite H1. f_equal. lia.
Qed.

Definition tbl_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 11; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma tbl_U : forall regs m (o r : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 (zlen (cells b)) -> getr regs 30%bv = Z_to_bv 64 r ->
  getr regs 13%bv = Z_to_bv 64 MASK ->
  0 <= r < 13 -> bn_at SEGS_U m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  arr32 SEGS_U m 80520 five_tbl ->
  0 <= o -> o + 516 <= 2 ^ 62 ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x361cc) m rom) (mkst regs' (Z_to_bv 64 0x36280) m' rom)
    /\ (let b' := (if 0 <? r then mul32 (kFive r) b else b) in
        bn_at SEGS_U m' o b' /\ getr regs' 12%bv = Z_to_bv 64 (zlen (cells b'))
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b /\ val (cells b') < B ^ 124)
    /\ keeps tbl_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o r b R10 R12 R30 R13 Hr Hbn Hok Hn Hne Hv Htbl Ho1 Ho2 Hsto.
  pose proof (cap_bound (cells b) r 0 Hok Hn ltac:(lia) ltac:(lia) Hv (five0_ge r ltac:(lia))) as Hcap.
  pose proof Hbn as Hbn0. destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  assert (Hl1 : 1 <= zlen (cells b)) by (destruct (cells b); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen (cells b)) as u eqn:Eu. assert (Hlen' : Z.of_nat (length (cells b)) = u) by (rewrite Eu; reflexivity).
  assert (Hv0 : val (cells b) < B ^ 124) by (pose proof (val_nonneg _ Hok); pose proof (Z.pow_pos_nonneg 5 r ltac:(lia) ltac:(lia)); nia).
  remember (B ^ 124) as TOP eqn:ETOP. clear ETOP.
  destruct (Z.eq_dec r 0) as [-> | Hr0].
  - (* [comment removed for export] *)
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 124)]) (@nil kcell) (@nil kwin)) 10%nat [0x36280] (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (30%bv : reg, ZL 0)]) [o; u] constr:([Some (0, 2 ^ 62); Some (1, 124)]) regs m rom 0x361cc.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
    eexists regs1, m. split; [exact ZM|]. replace (0 <? 0) with false by reflexivity. cbn zeta.
    split; [|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply unch_refl | apply mem_grows_refl]]].
    split; [exact Hbn0|]. split; [rewrite <- Eu; zx_regv ZR|]. repeat split; auto.
  - (* [comment removed for export] *)
    replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). cbn zeta.
    assert (HF : kFive r = 5 ^ r) by reflexivity.
    assert (HF5 : 5 <= 5 ^ r) by (change 5 with (5 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
    assert (HF12 : 5 ^ r <= 244140625) by (change 244140625 with (5 ^ 12); apply Z.pow_le_mono_r; lia).
    assert (Hcell : exists bs, rdn SEGS_U m (Z_to_bv 64 (80516 + 4 * r)) 4 = Some bs /\ bytes_le_to_Z bs = 5 ^ r).
    { rewrite <- (five_tbl_nth r) by lia. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (r - 1))); [exact Htbl | cbn; lia | lia | reflexivity]. }
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 124); Some (1, 12); Some (5, 244140625)]) (@nil kcell) (@nil kwin))
      40%nat [0x36248] (SCR [] [ZV 35])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (30%bv : reg, ZV 34)]) [o; u; r; 5 ^ r]
      constr:([Some (0, 2 ^ 62); Some (1, 124); Some (1, 12); Some (5, 244140625)]) regs m rom 0x361cc.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I)
      ltac:(idtac; zx_scs ltac:(destruct Hcell as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv])).
    zx_name regs1.
    assert (K1 : keeps tbl_keep regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (7%bv : reg) as A7. zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (6%bv : reg) as A6. zx_reg ZR (14%bv : reg) as A14.
    zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (15%bv : reg) as A15.
    zx_reg ZR (17%bv : reg) as A17.
    assert (A13 : getr regs1 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R13]).
    rename ZM into M1. clear ZE ZR ZF.
    (* [comment removed for export] *)
    unfold mul32. rewrite HF. replace (5 ^ r =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (5 ^ r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct b as [l exb]; cbn [cells BnModel.ex] in *. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
    pose proof (mul32_l_spec (5 ^ r) l 0 Hok ltac:(lia) ltac:(lia)) as SP.
    destruct (mul32_l (5 ^ r) 0 l) as [rr c] eqn:Em. destruct SP as (Hval & Hokr & Hlenr & Hc0' & HcF). specialize (HcF ltac:(lia)).
    destruct (mtb_loop_U rom l [] 0 regs1 m (o + 4) (5 ^ r) ((18446744073709551615 - o) / 2 ^ 2)) as (regs2 & m2 & M2 & Harr2 & C16 & C14 & K2 & U2 & G2);
      cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
    { exact A7. } { exact A16. }
    { rewrite A6. apply Z2bv_eqm. rewrite Hlen'. lia. }
    { exact A14. } { exact A5. } { exact A13. }
    { lia. } { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { lia. } { lia. } { exact Carr. }
    { eapply sc_store_in; [exact Hsto|]. zwidth. lia. }
    rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
    cbn [length app Z.of_nat] in U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
    assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 10 ltac:(cbn; tauto)) | exact A10]).
    assert (C12 : getr regs2 12%bv = Z_to_bv 64 u) by (etransitivity; [exact (K2 12 ltac:(cbn; tauto)) | exact A12]).
    assert (C15 : getr regs2 15%bv = Z_to_bv 64 u) by (etransitivity; [exact (K2 15 ltac:(cbn; tauto)) | exact A15]).
    assert (C17 : getr regs2 17%bv = Z_to_bv 64 (o + 4)) by (etransitivity; [exact (K2 17 ltac:(cbn; tauto)) | exact A17]).
    assert (C13 : getr regs2 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (K2 13 ltac:(cbn; tauto)) | exact A13]).
    assert (Hsto2 : RiscvSemantics.store_ok SEGS_U m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
    assert (Cu2 : cellN SEGS_U m2 o 2 u).
    { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
    assert (Ce2 : cellN SEGS_U m2 (o + 2) 2 exb).
    { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce]. }
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
      subst c. rewrite chunks_0, app_nil_r in *.
      zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (1, 124)]) (@nil kcell) (@nil kwin)) 10%nat [0x36280] (SCR [] []) constr:([(16%bv : reg, ZL 0); (12%bv : reg, ZV 32)])
        [u] constr:([Some (1, 124)]) regs2 m2 rom 0x36274.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
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
      zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 124); Some (1, 2 ^ 63 - 1)]) (@nil kcell) (@nil kwin)) 10%nat [0x36384] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (16%bv : reg, ZV 34); (14%bv : reg, ZV 34); (15%bv : reg, ZV 33); (17%bv : reg, ZAdd (ZV 32) (ZL 4))])
        [o; u; c] constr:([Some (0, 2 ^ 62); Some (1, 124); Some (1, 2 ^ 63 - 1)]) regs2 m2 rom 0x36274.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      zx_reg ZR (5%bv : reg) as D5. zx_reg ZR (6%bv : reg) as D6. zx_reg ZR (16%bv : reg) as D16. zx_reg ZR (17%bv : reg) as D17.
      zx_reg ZR (10%bv : reg) as D10. zx_reg ZR (12%bv : reg) as D12'. zx_reg ZR (14%bv : reg) as D14.
      assert (D13 : getr regs3 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C13]).
      assert (K3' : keeps tbl_keep regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      rename ZM into M3. clear ZE ZR ZF.
      assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63))).
      { unfold B. exists 1, (268435456 - 1); lia. }
      destruct Hcls as (clo & chi & Hcc & Hcls).
      destruct (cartb_U rom regs3 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & E12 & K4 & U4 & G4).
      { exact D10. } { exact D12'. } { exact D14. } { rewrite D5. f_equal. lia. } { rewrite D17. f_equal. lia. } { exact D6. } { exact D13. }
      { rewrite D16. f_equal. lia. }
      { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Harr2. } { exact Hsto2. }
      eexists regs4, m4. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4]|].
      split.
      { cbn [cells BnModel.ex]. split; [|split; [rewrite zlen_app, Hlenr, <- Eu; exact E12 | exact POSTV]].
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
