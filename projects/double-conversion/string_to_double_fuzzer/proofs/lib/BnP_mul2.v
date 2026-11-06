(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnP_mul.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Definition all_but28 : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31].
(* [comment removed for export] *)
Definition it27_keep : list Z := [1; 2; 3; 4; 5; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma it27_P : forall regs m (o r : Z) (l : list Z) (exb : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 (zlen l) -> getr regs 7%bv = Z_to_bv 64 r ->
  getr regs 14%bv = Z_to_bv 64 (o + 4) -> getr regs 16%bv = Z_to_bv 64 kFive27_lo ->
  getr regs 17%bv = Z_to_bv 64 (kFive27_hi * 16) -> getr regs 13%bv = Z_to_bv 64 MASK ->
  getr regs 15%bv = Z_to_bv 64 128 -> getr regs 5%bv = Z_to_bv 64 53 ->
  0 <= r < 2048 -> bn_at SEGS_P m o (BN l exb) -> ok l -> l <> [] -> zlen l + 3 <= 127 ->
  0 <= o -> o + 516 <= 2 ^ 62 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35b60) m rom) (mkst regs' (Z_to_bv 64 0x35b58) m' rom)
    /\ bn_at SEGS_P m' o (mul64 kFive27_lo kFive27_hi (BN l exb))
    /\ getr regs' 12%bv = Z_to_bv 64 (zlen (cells (mul64 kFive27_lo kFive27_hi (BN l exb))))
    /\ getr regs' 6%bv = Z_to_bv 64 r
    /\ keeps it27_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o r l exb R10 R12 R7 R14 R16 R17 R13 R15 R5 Hr Hbn Hok Hne Hlen Ho1 Ho2 Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _). cbn [cells BnModel.ex] in *.
  assert (Hl1 : 1 <= zlen l) by (destruct l; [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen l) as u eqn:Eu. assert (Hlen' : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity).
  (* [comment removed for export] *)
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 124); Some (0, 2047)]) (@nil kcell) (@nil kwin))
    30%nat [0x35b80] (SCR [] []) constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (7%bv : reg, ZV 34); (14%bv : reg, ZAdd (ZV 32) (ZL 4)); (5%bv : reg, ZL 53)])
    [o; u; r] constr:([Some (0, 2 ^ 62); Some (1, 124); Some (0, 2047)]) regs m rom 0x35b60.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  assert (K1 : keeps it27_keep regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  zx_reg ZR (7%bv : reg) as A7. zx_reg ZR (29%bv : reg) as A29. zx_reg ZR (28%bv : reg) as A28. zx_reg ZR (6%bv : reg) as A6.
  zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (12%bv : reg) as A12.
  assert (A16 : getr regs1 16%bv = Z_to_bv 64 kFive27_lo) by (etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R16]).
  assert (A17 : getr regs1 17%bv = Z_to_bv 64 (kFive27_hi * 16)) by (etransitivity; [exact (reg_kept _ _ _ _ (17%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R17]).
  assert (A13 : getr regs1 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R13]).
  assert (A15 : getr regs1 15%bv = Z_to_bv 64 128) by (etransitivity; [exact (reg_kept _ _ _ _ (15%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R15]).
  rename ZM into M1. clear ZE ZR ZF.
  (* [comment removed for export] *)
  unfold mul64. cbn [cells BnModel.ex]. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
  pose proof (mul64_l_spec l 0 Hok ltac:(lia)) as SP.
  destruct (mul64_l kFive27_lo kFive27_hi 0 l) as [rr c] eqn:Em. destruct SP as (_ & Hokr & Hlenr & Hc).
  destruct (mul64_loop_P rom l [] 0 regs1 m (o + 4)) as (regs2 & m2 & M2 & Harr2 & C28 & C7 & K2 & U2 & G2);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { exact A29. } { rewrite A7. f_equal. lia. } { exact A28. } { exact A16. } { exact A17. } { exact A13. }
  { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { exact Carr. }
  { eapply sc_store_in; [exact Hsto|]. zwidth. lia. }
  rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
  cbn [length app Z.of_nat] in C7, U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in C7. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
  assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 10 ltac:(cbn; tauto)) | exact A10]).
  assert (C12 : getr regs2 12%bv = Z_to_bv 64 u) by (etransitivity; [exact (K2 12 ltac:(cbn; tauto)) | exact A12]).
  assert (C15 : getr regs2 15%bv = Z_to_bv 64 128) by (etransitivity; [exact (K2 15 ltac:(cbn; tauto)) | exact A15]).
  assert (C13 : getr regs2 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (K2 13 ltac:(cbn; tauto)) | exact A13]).
  assert (C6 : getr regs2 6%bv = Z_to_bv 64 r) by (etransitivity; [exact (K2 6 ltac:(cbn; tauto)) | exact A6]).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_P m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  assert (Cu2 : cellN SEGS_P m2 o 2 u).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
  assert (Ce2 : cellN SEGS_P m2 (o + 2) 2 exb).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce]. }
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* [comment removed for export] *)
    subst c. rewrite chunks_0, app_nil_r.
    zx_run SEGS_P constr:(CTX vi_regs (@nil kcell) (@nil kwin)) 5%nat [0x35b58] (SCR [] []) constr:([(28%bv : reg, ZL 0)])
      (@nil Z) constr:(@nil (option (Z * Z))) regs2 m2 rom 0x35bb8.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact ZM]|].
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite Hlenr, <- Eu. exact Cu2.
      - exact Ce2.
      - exact Harr2. }
    split; [cbn [cells]; rewrite Hlenr, <- Eu; etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]|].
    split; [etransitivity; [exact (reg_kept _ _ _ _ (6%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C6]|].
    split; [eapply keeps_trans; [exact K1|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|];
            eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|exact G2].
    eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (1, 2 ^ 63 - 1)]) (@nil kcell) (@nil kwin)) 5%nat [0x35bbc] (SCR [] []) constr:([(28%bv : reg, ZV 32)])
      [c] constr:([Some (1, 2 ^ 63 - 1)]) regs2 m2 rom 0x35bb8.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    assert (K3 : keeps all_but28 regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (28%bv : reg) as D28.
    rename ZM into M3. clear ZE ZR ZF.
    assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63))).
    { unfold B. destruct (Z_lt_dec c 268435456); [exists 1, (268435456 - 1); lia|].
      destruct (Z_lt_dec c (268435456 * 268435456)); [exists 268435456, (268435456 * 268435456 - 1); lia|].
      exists (268435456 * 268435456), (2 ^ 63); lia. }
    destruct Hcls as (clo & chi & Hcc & Hcls).
    destruct (car64_P rom regs3 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & D12 & K4 & U4 & G4).
    { etransitivity; [exact (K3 10 ltac:(cbn; tauto)) | exact C10]. }
    { etransitivity; [exact (K3 12 ltac:(cbn; tauto)) | exact C12]. }
    { exact D28. }
    { etransitivity; [exact (K3 7 ltac:(cbn; tauto)) | ]; etransitivity; [exact C7 | f_equal; lia]. }
    { etransitivity; [exact (K3 15 ltac:(cbn; tauto)) | exact C15]. }
    { etransitivity; [exact (K3 13 ltac:(cbn; tauto)) | exact C13]. }
    { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Harr2. } { exact Hsto2. }
    eexists regs4, m4. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4]|].
    assert (Hck : zlen (chunks 3 c) <= 3).
    { pose proof (chunks_spec 3 c ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & _ & _ & H). exact H. }
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite zlen_app, Hlenr, <- Eu. exact Cu4.
      - eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Ce2].
      - exact Harr4. }
    split; [cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; exact D12|].
    split; [etransitivity; [exact (K4 6 ltac:(cbn; tauto)) |]; etransitivity; [exact (K3 6 ltac:(cbn; tauto)) | exact C6]|].
    split.
    { eapply keeps_trans; [exact K1|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
    split; [|eapply mem_grows_trans; [exact G2 | exact G4]].
    apply (unch_trans m m2 m4).
    + eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
    + eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]].
      * eexists; split; [left; reflexivity|cbn; lia].
      * eexists; split; [right; left; reflexivity|cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma cap_bound : forall l k j, ok l -> norm l -> 0 <= j <= 124 -> 0 <= k ->
  val l * 5 ^ k < B ^ 124 -> B ^ j <= 5 ^ k -> zlen l <= 124 - j.
Proof.
  intros l k j Hok Hn Hj Hk Hv Hbj.
  apply len_bound; auto; [lia|].
  pose proof (val_nonneg l Hok) as H0.
  assert (HB : B ^ 124 = B ^ (124 - j) * B ^ j) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite HB in Hv.
  assert (Hp : 0 < B ^ j) by (apply Z.pow_pos_nonneg; [reflexivity|lia]).
  assert (H1 : val l * B ^ j <= val l * 5 ^ k) by (apply Z.mul_le_mono_nonneg_l; [exact H0|exact Hbj]).
  apply (Z.mul_lt_mono_pos_r (B ^ j) (val l) (B ^ (124 - j)) Hp).
  eapply Z.le_lt_trans; [exact H1 | exact Hv].
Qed.

#[using="Type"] Lemma five27_ge : B ^ 2 <= 5 ^ 27. Proof. apply Z.lt_le_incl. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma five13_ge : B ^ 1 <= 5 ^ 13. Proof. apply Z.lt_le_incl. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma five0_ge : forall k, 0 <= k -> B ^ 0 <= 5 ^ k. Proof. intros. rewrite Z.pow_0_r. pose proof (Z.pow_pos_nonneg 5 k). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma loop27_P : forall f regs m (o r : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 (zlen (cells b)) -> getr regs 7%bv = Z_to_bv 64 r ->
  getr regs 14%bv = Z_to_bv 64 (o + 4) -> getr regs 16%bv = Z_to_bv 64 kFive27_lo ->
  getr regs 17%bv = Z_to_bv 64 (kFive27_hi * 16) -> getr regs 13%bv = Z_to_bv 64 MASK ->
  getr regs 15%bv = Z_to_bv 64 128 -> getr regs 5%bv = Z_to_bv 64 53 ->
  27 <= r < 2048 -> r - 27 < 27 * (Z.of_nat f + 1) ->
  bn_at SEGS_P m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  0 <= o -> o + 516 <= 2 ^ 62 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35b60) m rom) (mkst regs' (Z_to_bv 64 0x35bec) m' rom)
    /\ (let b' := fst (pow27_loop f (r - 27) (mul64 kFive27_lo kFive27_hi b)) in
        let r' := snd (pow27_loop f (r - 27) (mul64 kFive27_lo kFive27_hi b)) in
        bn_at SEGS_P m' o b' /\ getr regs' 12%bv = Z_to_bv 64 (zlen (cells b')) /\ getr regs' 7%bv = Z_to_bv 64 r'
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b
        /\ val (cells b') * 5 ^ r' < B ^ 124 /\ 0 <= r' < 27)
    /\ keeps it27_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  induction f as [|f IH]; intros regs m o r b R10 R12 R7 R14 R16 R17 R13 R15 R5 Hr Hf Hbn Hok Hn Hne Hv Ho1 Ho2 Hsto.
  all: pose proof (cap_bound (cells b) r 2 Hok Hn ltac:(lia) ltac:(lia) Hv ltac:(eapply Z.le_trans; [apply five27_ge | apply Z.pow_le_mono_r; lia])) as Hcap.
  all: destruct b as [l exb]; cbn [cells BnModel.ex] in *.
  all: destruct (it27_P regs m o r l exb R10 R12 R7 R14 R16 R17 R13 R15 R5 ltac:(lia) Hbn Hok Hne ltac:(lia) Ho1 Ho2 Hsto)
      as (regs1 & m1 & M1 & Hbn1 & C12 & C6 & K1 & U1 & G1).
  all: pose proof (mul64_spec (BN l exb) Hok Hn) as SP1; cbn zeta in SP1; destruct SP1 as (Hok1 & Hn1 & Hv1 & Hex1).
  all: assert (Hne1 : cells (mul64 kFive27_lo kFive27_hi (BN l exb)) <> []) by (intros HH; apply (proj1 (mul64_cells_nil _)) in HH; exact (Hne HH)).
  all: remember (mul64 kFive27_lo kFive27_hi (BN l exb)) as b1 eqn:Eb1; cbn [BnModel.cells BnModel.ex] in *.
  all: assert (Hv1' : val (cells b1) * 5 ^ (r - 27) < B ^ 124)
        by (rewrite Hv1; replace (5 ^ r) with (5 ^ 27 * 5 ^ (r - 27)) in Hv by (rewrite <- Z.pow_add_r by lia; f_equal; lia); lia).
  all: assert (C5 : getr regs1 5%bv = Z_to_bv 64 53) by (etransitivity; [exact (K1 5 ltac:(cbn; tauto)) | exact R5]).
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (27, 53)]) (@nil kcell) (@nil kwin)) 5%nat [0x35b60; 0x35bec] (SCR [true] [])
      constr:([(6%bv : reg, ZV 32); (5%bv : reg, ZL 53)]) [r] constr:([Some (27, 53)]) regs1 m1 rom 0x35b58.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
    eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
    cbn [pow27_loop fst snd].
    split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
    split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]|].
    split; [zx_regv ZR|]. repeat split; auto; lia.
  - destruct (Z_le_dec r 53) as [Hle|Hgt].
    + (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (27, 53)]) (@nil kcell) (@nil kwin)) 5%nat [0x35b60; 0x35bec] (SCR [true] [])
        constr:([(6%bv : reg, ZV 32); (5%bv : reg, ZL 53)]) [r] constr:([Some (27, 53)]) regs1 m1 rom 0x35b58.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
      cbn [pow27_loop]. replace (r - 27 <? 27) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
      split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]|].
      split; [zx_regv ZR|]. repeat split; auto; lia.
    + (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (54, 2047)]) (@nil kcell) (@nil kwin)) 5%nat [0x35b60; 0x35bec] (SCR [false] [])
        constr:([(6%bv : reg, ZV 32); (5%bv : reg, ZL 53)]) [r] constr:([Some (54, 2047)]) regs1 m1 rom 0x35b58.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      assert (K2 : keeps it27_keep regs regs2) by (eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]).
      cbn [pow27_loop]. replace (r - 27 <? 27) with false by (symmetry; apply Z.ltb_ge; lia).
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_P m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G1 | exact Hsto]).
      destruct (IH regs2 m1 o (r - 27) b1) as (regs3 & m3 & M3 & POST & K3 & U3 & G3).
      { etransitivity; [exact (K2 10 ltac:(cbn; tauto)) | exact R10]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]. }
      { zx_regv ZR. }
      { etransitivity; [exact (K2 14 ltac:(cbn; tauto)) | exact R14]. }
      { etransitivity; [exact (K2 16 ltac:(cbn; tauto)) | exact R16]. }
      { etransitivity; [exact (K2 17 ltac:(cbn; tauto)) | exact R17]. }
      { etransitivity; [exact (K2 13 ltac:(cbn; tauto)) | exact R13]. }
      { etransitivity; [exact (K2 15 ltac:(cbn; tauto)) | exact R15]. }
      { etransitivity; [exact (K2 5 ltac:(cbn; tauto)) | exact R5]. }
      { lia. } { lia. } { subst b1; exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1'. } { lia. } { lia. } { exact Hsto1. }
      eexists regs3, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact ZM | exact M3]|].
      subst b1. replace (r - 27 - 27) with (r - 54) in POST by lia. replace (r - 27 - 27) with (r - 54) by lia.
      split; [cbn zeta in POST |- *; rewrite Hex1 in POST; exact POST|].
      split; [eapply keeps_trans; [exact K2 | exact K3]|].
      split; [eapply unch_trans; [exact U1 | exact U3] | eapply mem_grows_trans; [exact G1 | exact G3]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition it13_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition all_regs : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma it13_P : forall regs m (o r : Z) (l : list Z) (exb : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 (zlen l) -> getr regs 7%bv = Z_to_bv 64 r ->
  getr regs 14%bv = Z_to_bv 64 (o + 4) -> getr regs 16%bv = Z_to_bv 64 kFive13 -> getr regs 13%bv = Z_to_bv 64 MASK ->
  getr regs 15%bv = Z_to_bv 64 128 -> getr regs 17%bv = Z_to_bv 64 25 ->
  0 <= r < 2048 -> bn_at SEGS_P m o (BN l exb) -> ok l -> l <> [] -> zlen l + 3 <= 127 ->
  0 <= o -> o + 516 <= 2 ^ 62 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35c14) m rom) (mkst regs' (Z_to_bv 64 0x35c0c) m' rom)
    /\ bn_at SEGS_P m' o (mul32 kFive13 (BN l exb))
    /\ getr regs' 12%bv = Z_to_bv 64 (zlen (cells (mul32 kFive13 (BN l exb))))
    /\ getr regs' 5%bv = Z_to_bv 64 r
    /\ keeps it13_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o r l exb R10 R12 R7 R14 R16 R13 R15 R17 Hr Hbn Hok Hne Hlen Ho1 Ho2 Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _). cbn [cells BnModel.ex] in *.
  assert (Hl1 : 1 <= zlen l) by (destruct l; [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen l) as u eqn:Eu. assert (Hlen' : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity).
  (* [comment removed for export] *)
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 124); Some (0, 2047)]) (@nil kcell) (@nil kwin))
    30%nat [0x35c34] (SCR [] []) constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (7%bv : reg, ZV 34); (14%bv : reg, ZAdd (ZV 32) (ZL 4))])
    [o; u; r] constr:([Some (0, 2 ^ 62); Some (1, 124); Some (0, 2047)]) regs m rom 0x35c14.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  assert (K1 : keeps it13_keep regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  zx_reg ZR (6%bv : reg) as A6. zx_reg ZR (28%bv : reg) as A28. zx_reg ZR (7%bv : reg) as A7. zx_reg ZR (5%bv : reg) as A5.
  zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (12%bv : reg) as A12.
  assert (A16 : getr regs1 16%bv = Z_to_bv 64 kFive13) by (etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R16]).
  assert (A13 : getr regs1 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R13]).
  assert (A15 : getr regs1 15%bv = Z_to_bv 64 128) by (etransitivity; [exact (reg_kept _ _ _ _ (15%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R15]).
  rename ZM into M1. clear ZE ZR ZF.
  (* [comment removed for export] *)
  unfold mul32. cbn [cells BnModel.ex Z.eqb kFive13 Pos.eqb]. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
  pose proof (mul32_l_spec kFive13 l 0 Hok ltac:(unfold kFive13; lia) ltac:(lia)) as SP.
  unfold kFive13 in *.
  destruct (mul32_l 1220703125 0 l) as [rr c] eqn:Em. destruct SP as (_ & Hokr & Hlenr & Hc0' & HcF). specialize (HcF ltac:(lia)).
  destruct (m13_loop_P rom l [] 0 regs1 m (o + 4) 1220703125) as (regs2 & m2 & M2 & Harr2 & C28 & C7 & C6 & K2 & U2 & G2);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { exact A28. } { rewrite A6. f_equal. lia. } { exact A7. } { exact A16. } { exact A13. }
  { lia. } { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { exact Carr. }
  { eapply sc_store_in; [exact Hsto|]. zwidth. lia. }
  rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
  cbn [length app Z.of_nat] in C6, U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in C6. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
  assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 10 ltac:(cbn; tauto)) | exact A10]).
  assert (C12 : getr regs2 12%bv = Z_to_bv 64 u) by (etransitivity; [exact (K2 12 ltac:(cbn; tauto)) | exact A12]).
  assert (C15 : getr regs2 15%bv = Z_to_bv 64 128) by (etransitivity; [exact (K2 15 ltac:(cbn; tauto)) | exact A15]).
  assert (C13 : getr regs2 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (K2 13 ltac:(cbn; tauto)) | exact A13]).
  assert (C5 : getr regs2 5%bv = Z_to_bv 64 r) by (etransitivity; [exact (K2 5 ltac:(cbn; tauto)) | exact A5]).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_P m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  assert (Cu2 : cellN SEGS_P m2 o 2 u).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
  assert (Ce2 : cellN SEGS_P m2 (o + 2) 2 exb).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce]. }
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* [comment removed for export] *)
    subst c. rewrite chunks_0, app_nil_r.
    zx_run SEGS_P constr:(CTX vi_regs (@nil kcell) (@nil kwin)) 5%nat [0x35c0c] (SCR [] []) constr:([(28%bv : reg, ZL 0)])
      (@nil Z) constr:(@nil (option (Z * Z))) regs2 m2 rom 0x35c58.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact ZM]|].
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite Hlenr, <- Eu. exact Cu2.
      - exact Ce2.
      - exact Harr2. }
    split; [cbn [cells]; rewrite Hlenr, <- Eu; etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]|].
    split; [etransitivity; [exact (reg_kept _ _ _ _ (5%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C5]|].
    split; [eapply keeps_trans; [exact K1|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|];
            eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|exact G2].
    eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (1, 2 ^ 63 - 1)]) (@nil kcell) (@nil kwin)) 5%nat [0x35c5c] (SCR [] []) constr:([(28%bv : reg, ZV 32)])
      [c] constr:([Some (1, 2 ^ 63 - 1)]) regs2 m2 rom 0x35c58.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    assert (K3 : keeps all_regs regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    rename ZM into M3. clear ZE ZR ZF.
    assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63))).
    { unfold B. destruct (Z_lt_dec c 268435456); [exists 1, (268435456 - 1); lia|].
      exists 268435456, (268435456 * 268435456 - 1); lia. }
    destruct Hcls as (clo & chi & Hcc & Hcls).
    destruct (car13_P rom regs3 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & D12 & K4 & U4 & G4).
    { etransitivity; [exact (K3 10 ltac:(cbn; tauto)) | exact C10]. }
    { etransitivity; [exact (K3 12 ltac:(cbn; tauto)) | exact C12]. }
    { etransitivity; [exact (K3 7 ltac:(cbn; tauto)) | exact C7]. }
    { etransitivity; [exact (K3 6 ltac:(cbn; tauto)) | ]; etransitivity; [exact C6 | f_equal; lia]. }
    { etransitivity; [exact (K3 15 ltac:(cbn; tauto)) | exact C15]. }
    { etransitivity; [exact (K3 13 ltac:(cbn; tauto)) | exact C13]. }
    { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Harr2. } { exact Hsto2. }
    eexists regs4, m4. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4]|].
    assert (Hck : zlen (chunks 3 c) <= 3).
    { pose proof (chunks_spec 3 c ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & _ & _ & H). exact H. }
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite zlen_app, Hlenr, <- Eu. exact Cu4.
      - eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Ce2].
      - exact Harr4. }
    split; [cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; exact D12|].
    split; [etransitivity; [exact (K4 5 ltac:(cbn; tauto)) |]; etransitivity; [exact (K3 5 ltac:(cbn; tauto)) | exact C5]|].
    split.
    { eapply keeps_trans; [exact K1|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
    split; [|eapply mem_grows_trans; [exact G2 | exact G4]].
    apply (unch_trans m m2 m4).
    + eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
    + eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]].
      * eexists; split; [left; reflexivity|cbn; lia].
      * eexists; split; [right; left; reflexivity|cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma loop13_P : forall f regs m (o r : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 (zlen (cells b)) -> getr regs 7%bv = Z_to_bv 64 r ->
  getr regs 14%bv = Z_to_bv 64 (o + 4) -> getr regs 16%bv = Z_to_bv 64 kFive13 -> getr regs 13%bv = Z_to_bv 64 MASK ->
  getr regs 15%bv = Z_to_bv 64 128 -> getr regs 17%bv = Z_to_bv 64 25 ->
  13 <= r < 2048 -> r - 13 < 13 * (Z.of_nat f + 1) ->
  bn_at SEGS_P m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  0 <= o -> o + 516 <= 2 ^ 62 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35c14) m rom) (mkst regs' (Z_to_bv 64 0x35c88) m' rom)
    /\ (let b' := fst (pow13_loop f (r - 13) (mul32 kFive13 b)) in
        let r' := snd (pow13_loop f (r - 13) (mul32 kFive13 b)) in
        bn_at SEGS_P m' o b' /\ getr regs' 12%bv = Z_to_bv 64 (zlen (cells b')) /\ getr regs' 7%bv = Z_to_bv 64 r'
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b
        /\ val (cells b') * 5 ^ r' < B ^ 124 /\ 0 <= r' < 13)
    /\ keeps it13_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  induction f as [|f IH]; intros regs m o r b R10 R12 R7 R14 R16 R13 R15 R17 Hr Hf Hbn Hok Hn Hne Hv Ho1 Ho2 Hsto.
  all: pose proof (cap_bound (cells b) r 1 Hok Hn ltac:(lia) ltac:(lia) Hv ltac:(eapply Z.le_trans; [apply five13_ge | apply Z.pow_le_mono_r; lia])) as Hcap.
  all: destruct b as [l exb]; cbn [cells BnModel.ex] in *.
  all: destruct (it13_P regs m o r l exb R10 R12 R7 R14 R16 R13 R15 R17 ltac:(lia) Hbn Hok Hne ltac:(lia) Ho1 Ho2 Hsto)
      as (regs1 & m1 & M1 & Hbn1 & C12 & C5 & K1 & U1 & G1).
  all: pose proof (mul32_spec kFive13 (BN l exb) Hok Hn ltac:(unfold kFive13; lia)) as SP1; cbn zeta in SP1; destruct SP1 as (Hok1 & Hn1 & Hv1 & Hex1).
  all: specialize (Hex1 ltac:(unfold kFive13; lia)).
  all: assert (Hne1 : cells (mul32 kFive13 (BN l exb)) <> []) by (intros HH; apply (proj1 (mul32_cells_nil kFive13 _ ltac:(unfold kFive13; lia))) in HH; exact (Hne HH)).
  all: remember (mul32 kFive13 (BN l exb)) as b1 eqn:Eb1; cbn [BnModel.cells BnModel.ex] in *.
  all: assert (Hv1' : val (cells b1) * 5 ^ (r - 13) < B ^ 124)
        by (rewrite Hv1, kFive13_eq; replace (5 ^ r) with (5 ^ 13 * 5 ^ (r - 13)) in Hv by (rewrite <- Z.pow_add_r by lia; f_equal; lia); lia).
  all: assert (C17 : getr regs1 17%bv = Z_to_bv 64 25) by (etransitivity; [exact (K1 17 ltac:(cbn; tauto)) | exact R17]).
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (13, 25)]) (@nil kcell) (@nil kwin)) 5%nat [0x35c14; 0x35c88] (SCR [true] [])
      constr:([(5%bv : reg, ZV 32); (17%bv : reg, ZL 25)]) [r] constr:([Some (13, 25)]) regs1 m1 rom 0x35c0c.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
    eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
    cbn [pow13_loop fst snd].
    split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
    split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]|].
    split; [zx_regv ZR|]. repeat split; auto; lia.
  - destruct (Z_le_dec r 25) as [Hle|Hgt].
    + (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (13, 25)]) (@nil kcell) (@nil kwin)) 5%nat [0x35c14; 0x35c88] (SCR [true] [])
        constr:([(5%bv : reg, ZV 32); (17%bv : reg, ZL 25)]) [r] constr:([Some (13, 25)]) regs1 m1 rom 0x35c0c.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
      cbn [pow13_loop]. replace (r - 13 <? 13) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
      split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]|].
      split; [zx_regv ZR|]. repeat split; auto; lia.
    + (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (26, 2047)]) (@nil kcell) (@nil kwin)) 5%nat [0x35c14; 0x35c88] (SCR [false] [])
        constr:([(5%bv : reg, ZV 32); (17%bv : reg, ZL 25)]) [r] constr:([Some (26, 2047)]) regs1 m1 rom 0x35c0c.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      assert (K2 : keeps it13_keep regs regs2) by (eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]).
      cbn [pow13_loop]. replace (r - 13 <? 13) with false by (symmetry; apply Z.ltb_ge; lia).
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_P m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G1 | exact Hsto]).
      destruct (IH regs2 m1 o (r - 13) b1) as (regs3 & m3 & M3 & POST & K3 & U3 & G3).
      { etransitivity; [exact (K2 10 ltac:(cbn; tauto)) | exact R10]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]. }
      { zx_regv ZR. }
      { etransitivity; [exact (K2 14 ltac:(cbn; tauto)) | exact R14]. }
      { etransitivity; [exact (K2 16 ltac:(cbn; tauto)) | exact R16]. }
      { etransitivity; [exact (K2 13 ltac:(cbn; tauto)) | exact R13]. }
      { etransitivity; [exact (K2 15 ltac:(cbn; tauto)) | exact R15]. }
      { etransitivity; [exact (K2 17 ltac:(cbn; tauto)) | exact R17]. }
      { lia. } { lia. } { subst b1; exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1'. } { lia. } { lia. } { exact Hsto1. }
      eexists regs3, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact ZM | exact M3]|].
      subst b1. replace (r - 13 - 13) with (r - 26) in POST by lia. replace (r - 13 - 13) with (r - 26) by lia.
      split; [cbn zeta in POST |- *; rewrite Hex1 in POST; exact POST|].
      split; [eapply keeps_trans; [exact K2 | exact K3]|].
      split; [eapply unch_trans; [exact U1 | exact U3] | eapply mem_grows_trans; [exact G1 | exact G3]].
Qed.

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

#[using="Type"] Lemma tbl_P : forall regs m (o r : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 12%bv = Z_to_bv 64 (zlen (cells b)) -> getr regs 7%bv = Z_to_bv 64 r ->
  getr regs 13%bv = Z_to_bv 64 MASK ->
  0 <= r < 13 -> bn_at SEGS_P m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  arr32 SEGS_P m 80520 five_tbl ->
  0 <= o -> o + 516 <= 2 ^ 62 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35c88) m rom) (mkst regs' (Z_to_bv 64 0x35d10) m' rom)
    /\ (let b' := (if 0 <? r then mul32 (kFive r) b else b) in
        bn_at SEGS_P m' o b' /\ getr regs' 12%bv = Z_to_bv 64 (zlen (cells b'))
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b /\ val (cells b') < B ^ 124)
    /\ keeps tbl_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o r b R10 R12 R7 R13 Hr Hbn Hok Hn Hne Hv Htbl Ho1 Ho2 Hsto.
  pose proof (cap_bound (cells b) r 0 Hok Hn ltac:(lia) ltac:(lia) Hv (five0_ge r ltac:(lia))) as Hcap.
  pose proof Hbn as Hbn0. destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  assert (Hl1 : 1 <= zlen (cells b)) by (destruct (cells b); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen (cells b)) as u eqn:Eu. assert (Hlen' : Z.of_nat (length (cells b)) = u) by (rewrite Eu; reflexivity).
  assert (Hv0 : val (cells b) < B ^ 124) by (pose proof (val_nonneg _ Hok); pose proof (Z.pow_pos_nonneg 5 r ltac:(lia) ltac:(lia)); nia).
  remember (B ^ 124) as TOP eqn:ETOP. clear ETOP.
  destruct (Z.eq_dec r 0) as [-> | Hr0].
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 124)]) (@nil kcell) (@nil kwin)) 10%nat [0x35d10] (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (7%bv : reg, ZL 0)]) [o; u] constr:([Some (0, 2 ^ 62); Some (1, 124)]) regs m rom 0x35c88.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
    eexists regs1, m. split; [exact ZM|]. replace (0 <? 0) with false by reflexivity. cbn zeta.
    split; [|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply unch_refl | apply mem_grows_refl]]].
    split; [exact Hbn0|]. split; [rewrite <- Eu; zx_regv ZR|]. repeat split; auto.
  - (* [comment removed for export] *)
    replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). cbn zeta.
    assert (HF : kFive r = 5 ^ r) by reflexivity.
    assert (HF5 : 5 <= 5 ^ r) by (change 5 with (5 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
    assert (HF12 : 5 ^ r <= 244140625) by (change 244140625 with (5 ^ 12); apply Z.pow_le_mono_r; lia).
    assert (Hcell : exists bs, rdn SEGS_P m (Z_to_bv 64 (80516 + 4 * r)) 4 = Some bs /\ bytes_le_to_Z bs = 5 ^ r).
    { rewrite <- (five_tbl_nth r) by lia. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (r - 1))); [exact Htbl | cbn; lia | lia | reflexivity]. }
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 124); Some (1, 12); Some (5, 244140625)]) (@nil kcell) (@nil kwin))
      40%nat [0x35ce4] (SCR [] [ZV 35])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (7%bv : reg, ZV 34)]) [o; u; r; 5 ^ r]
      constr:([Some (0, 2 ^ 62); Some (1, 124); Some (1, 12); Some (5, 244140625)]) regs m rom 0x35c88.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I)
      ltac:(idtac; zx_scs ltac:(destruct Hcell as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv])).
    zx_name regs1.
    assert (K1 : keeps tbl_keep regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (14%bv : reg) as A14. zx_reg ZR (17%bv : reg) as A17.
    zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (15%bv : reg) as A15.
    assert (A13 : getr regs1 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R13]).
    rename ZM into M1. clear ZE ZR ZF.
    (* [comment removed for export] *)
    unfold mul32. rewrite HF. replace (5 ^ r =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (5 ^ r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct b as [l exb]; cbn [cells BnModel.ex] in *. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
    pose proof (mul32_l_spec (5 ^ r) l 0 Hok ltac:(lia) ltac:(lia)) as SP.
    destruct (mul32_l (5 ^ r) 0 l) as [rr c] eqn:Em. destruct SP as (Hval & Hokr & Hlenr & Hc0' & HcF). specialize (HcF ltac:(lia)).
    destruct (mtb_loop_P rom l [] 0 regs1 m (o + 4) (5 ^ r)) as (regs2 & m2 & M2 & Harr2 & C16 & C14 & C5 & K2 & U2 & G2);
      cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
    { exact A16. } { rewrite A5. f_equal. lia. } { exact A14. } { exact A17. } { exact A13. }
    { lia. } { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { exact Carr. }
    { eapply sc_store_in; [exact Hsto|]. zwidth. lia. }
    rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
    cbn [length app Z.of_nat] in C5, U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in C5. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
    assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 10 ltac:(cbn; tauto)) | exact A10]).
    assert (C12 : getr regs2 12%bv = Z_to_bv 64 u) by (etransitivity; [exact (K2 12 ltac:(cbn; tauto)) | exact A12]).
    assert (C15 : getr regs2 15%bv = Z_to_bv 64 (u * 4)) by (etransitivity; [exact (K2 15 ltac:(cbn; tauto)) | exact A15]).
    assert (C13 : getr regs2 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (K2 13 ltac:(cbn; tauto)) | exact A13]).
    assert (Hsto2 : RiscvSemantics.store_ok SEGS_P m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
    assert (Cu2 : cellN SEGS_P m2 o 2 u).
    { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
    assert (Ce2 : cellN SEGS_P m2 (o + 2) 2 exb).
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
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (1, 124)]) (@nil kcell) (@nil kwin)) 5%nat [0x35d10] (SCR [] []) constr:([(16%bv : reg, ZL 0); (12%bv : reg, ZV 32)])
        [u] constr:([Some (1, 124)]) regs2 m2 rom 0x35d08.
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
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 124); Some (1, 2 ^ 63 - 1)]) (@nil kcell) (@nil kwin)) 10%nat [0x35dc4] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (16%bv : reg, ZV 34); (15%bv : reg, ZMul (ZV 33) (ZL 4))])
        [o; u; c] constr:([Some (0, 2 ^ 62); Some (1, 124); Some (1, 2 ^ 63 - 1)]) regs2 m2 rom 0x35d08.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      assert (K3 : keeps all_regs regs2 regs3 \/ True) by (right; exact I).
      zx_reg ZR (15%bv : reg) as D15. zx_reg ZR (16%bv : reg) as D16. zx_reg ZR (10%bv : reg) as D10. zx_reg ZR (12%bv : reg) as D12'.
      assert (D14 : getr regs3 14%bv = Z_to_bv 64 c) by (etransitivity; [exact (reg_kept _ _ _ _ (14%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C14]).
      assert (D13 : getr regs3 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C13]).
      assert (K3' : keeps tbl_keep regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      rename ZM into M3. clear ZE ZR ZF.
      assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63))).
      { unfold B. exists 1, (268435456 - 1); lia. }
      destruct Hcls as (clo & chi & Hcc & Hcls).
      destruct (cartb_P rom regs3 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & E12 & K4 & U4 & G4).
      { exact D10. } { exact D12'. } { exact D14. } { rewrite D15. f_equal. lia. } { exact D16. } { exact D13. }
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fin_keep : list Z := [3; 4; 9; 10; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma fin_P : forall regs m (o e sp : Z) (ret s0v : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 12%bv = Z_to_bv 64 (zlen (cells b)) ->
  getr regs 13%bv = Z_to_bv 64 MASK -> getr regs 2%bv = Z_to_bv 64 (sp - 16) ->
  cellN SEGS_P m (sp - 8) 8 (bv_unsigned ret) -> cellN SEGS_P m (sp - 16) 8 (bv_unsigned s0v) -> ret_ok ret ->
  1 <= e < 2048 -> bn_at SEGS_P m o b -> ok (cells b) -> cells b <> [] -> zlen (cells b) <= 127 -> ex b + e / 28 < 2 ^ 15 ->
  16 <= sp -> sp <= 2 ^ 62 -> 0 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 16 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35d10) m rom) (mkst regs' ret m' rom)
    /\ bn_at SEGS_P m' o (shl e b) /\ getr regs' 2%bv = Z_to_bv 64 sp /\ getr regs' 8%bv = s0v
    /\ keeps fin_keep regs regs'
    /\ unch m m' [(o, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o e sp ret s0v b R10 R11 R12 R13 R2 Cra Cs0 Hret He Hbn Hok Hne Hlen Hex Hsp1 Hsp2 Ho1 Ho2 Hdisj Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  assert (Hl1 : 1 <= zlen (cells b)) by (destruct (cells b); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen (cells b)) as u eqn:Eu. assert (Hlen' : Z.of_nat (length (cells b)) = u) by (rewrite Eu; reflexivity).
  pose proof (u64_range ret) as Hrr. pose proof (u64_range s0v) as Hsr.
  (* [comment removed for export] *)
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1)]) [KC (ZV 32) 2 2 (ZV 35)] (@nil kwin))
    40%nat [0x35d3c] (SCR [] []) constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (11%bv : reg, ZV 34)])
    [o; u; e; ex b] constr:([Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1)]) regs m rom 0x35d10.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Ce; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  zx_reg ZR (15%bv : reg) as A15. fold (magic28 e) in A15. rewrite (magic28_ok e) in A15 by lia.
  zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (14%bv : reg) as A14. zx_reg ZR (10%bv : reg) as A10.
  zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (12%bv : reg) as A12.
  assert (A13 : getr regs1 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R13]).
  assert (A2 : getr regs1 2%bv = Z_to_bv 64 (sp - 16)) by (etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R2]).
  assert (K1 : keeps fin_keep regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M1. clear ZE ZR ZF.
  (* [comment removed for export] *)
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (0, 73)]) (@nil kcell) [KW (ZV 32) 0 516])
    40%nat [0x35d78] (SCR [] [])
    constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (11%bv : reg, ZV 34); (14%bv : reg, ZV 33); (16%bv : reg, ZV 35); (15%bv : reg, ZV 36)])
    [o; u; e; ex b; e / 28] constr:([Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (0, 73)]) regs1 m rom 0x35d3c.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(exact I). zx_name regs2.
  zx_reg ZR (15%bv : reg) as B15. zx_reg ZR (11%bv : reg) as B11. zx_reg ZR (14%bv : reg) as B14.
  zx_reg ZR (16%bv : reg) as B16. zx_reg ZR (17%bv : reg) as B17. zx_reg ZR (12%bv : reg) as B12.
  zx_reg ZR (10%bv : reg) as B10.
  assert (B13 : getr regs2 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact A13]).
  assert (B2 : getr regs2 2%bv = Z_to_bv 64 (sp - 16)) by (etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact A2]).
  set (m2 := wbytes m _ _) in ZM.
  assert (K2 : keeps fin_keep regs1 regs2) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  clear ZE ZR ZF. rename ZM into M2.
  (* [comment removed for export] *)
  assert (Hs : 0 <= e mod 28 < 28) by lia.
  destruct (cells b) as [|x t] eqn:El; [congruence|]. cbn [length] in Hlen'.
  assert (Harr2 : arr32 SEGS_P m2 (o + 4) ([] ++ x :: t)).
  { cbn [app]. unfold m2. apply arr32_store_other; zwidth; try lia. exact Carr. }
  pose proof Hok as Hok0.
  destruct (mshl_loop_P rom (x :: t) [] 0 regs2 m2 (o + 4) (e mod 28)) as (regs3 & m3 & M3 & Harr3 & C14 & C11 & K3 & U3 & G3);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { rewrite B15; first [reflexivity | f_equal; lia]. }
  { rewrite B11, <- Hlen'; cbn [length]. f_equal. lia. }
  { exact B14. }
  { rewrite B16; first [reflexivity | f_equal; lia]. }
  { rewrite B17; first [reflexivity | f_equal; lia]. }
  { exact B13. }
  { exact Hs. }
  { split; [lia|]. apply Z.pow_pos_nonneg; lia. }
  { exact Hok. }
  { congruence. }
  { lia. }
  { cbn [length] in Hlen'. lia. }
  { exact Harr2. }
  { eapply sc_store_in; [eapply store_ok_grows; [|exact Hsto]; unfold m2; growsx |]. cbn [length]. cbn [length] in Hlen'. lia. }
  cbn [length app] in Harr3, C11, U3. rewrite ?Z.mul_0_r, ?Z.add_0_r in C11, U3. rewrite Hlen' in C11, U3.
  pose proof (shl_l_spec (e mod 28) (x :: t) 0 Hok Hs ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as SPEC.
  destruct (shl_l (e mod 28) 0 (x :: t)) as [r c'] eqn:Eshl. cbn [fst snd] in Harr3, C14.
  destruct SPEC as (_ & Hokr & Hlenr & Hc').
  assert (Hc'27 : c' < 2 ^ 27) by (assert (2 ^ (e mod 28) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia); lia).
  assert (Hlenr' : Z.of_nat (length r) = u) by (unfold zlen in Hlenr; cbn [length] in Hlenr; cbn [length] in Hlen'; lia).
  (* [comment removed for export] *)
  assert (C12 : getr regs3 12%bv = Z_to_bv 64 u) by (etransitivity; [exact (K3 12 ltac:(cbn; tauto)) | exact B12]).
  assert (C10 : getr regs3 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K3 10 ltac:(cbn; tauto)) | exact B10]).
  assert (C2 : getr regs3 2%bv = Z_to_bv 64 (sp - 16)) by (etransitivity; [exact (K3 2 ltac:(cbn; tauto)) | exact B2]).
  assert (RA3 : cellN SEGS_P m3 (sp - 8) 8 (bv_unsigned ret)).
  { eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m2. cellx. }
  assert (S03 : cellN SEGS_P m3 (sp - 16) 8 (bv_unsigned s0v)).
  { eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m2. cellx. }
  assert (Hsto3 : RiscvSemantics.store_ok SEGS_P m3 (Z_to_bv 64 o) 516 = true).
  { eapply store_ok_grows; [exact G3|]. eapply store_ok_grows; [|exact Hsto]. unfold m2; growsx. }
  assert (EXC : forall m', unch m3 m' [(o, o + 2); (o + 4 + 4 * u, o + 8 + 4 * u)] -> cellN SEGS_P m' (o + 2) 2 (ex b + e / 28)).
  { intros m' U. eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia |].
    eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m2. cellx. }
  assert (UNCH : forall m', unch m3 m' [(o, o + 516)] -> unch m m' [(o, o + 516)]).
  { intros m' U. apply (unch_trans m m3 m'); [|exact U].
    apply (unch_trans m m2 m3); [unfold m2; unchx|].
    eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|cbn; lia]. }
  assert (KEEPS : forall regs4, keeps fin_keep regs3 regs4 -> keeps fin_keep regs regs4).
  { intros regs4 K4. eapply keeps_trans; [exact K1|]. eapply keeps_trans; [exact K2|]. eapply keeps_trans; [|exact K4].
    eapply keeps_sub_dec; [exact K3|]. vm_compute. reflexivity. }
  unfold shl. rewrite El, Eshl. unfold bn_at. cbn [cells BnModel.ex].
  destruct (Z.eqb_spec c' 0) as [Hc0|Hc0].
  + (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (16, 2 ^ 62); None; None]) [KC (ZV 34) (-8) 8 (ZV 35); KC (ZV 34) (-16) 8 (ZV 36)] (@nil kwin))
      40%nat [0x35cbc; 0x35db4] (SCR [] []) constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (14%bv : reg, ZL 0); (2%bv : reg, ZAdd (ZV 34) (ZL (-16)))])
      [o; u; sp; bv_unsigned ret; bv_unsigned s0v] constr:([Some (0, 2 ^ 62); Some (1, 127); Some (16, 2 ^ 62); @None (Z * Z); @None (Z * Z)]) regs3 m3 rom 0x35d98.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA3; kc1 S03; exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
    assert (R1' : getr regs4 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (2%bv : reg) as D2. zx_reg ZR (8%bv : reg) as D8.
    eexists regs4, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3|];
                              eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [|split; [rewrite D2; f_equal; lia | split; [rewrite D8; apply Z_to_bv_bv_unsigned | split; [apply KEEPS; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply UNCH; apply unch_refl | apply (mem_grows_trans m m2 m3); [unfold m2; growsx | exact G3]]]]]].
    split; [|split; [apply EXC; apply unch_refl|split; [exact Harr3|split; [lia| unfold zlen; rewrite Hlenr'; lia]]]].
    unfold zlen; rewrite Hlenr'.
    eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m2. cellx.
  + (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (16, 2 ^ 62); None; None; Some (1, 2 ^ 27); Some (0, 2 ^ 62)])
                            [KC (ZV 34) (-8) 8 (ZV 35); KC (ZV 34) (-16) 8 (ZV 36)] (@nil kwin))
      40%nat [0x35cbc; 0x35db4] (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (14%bv : reg, ZV 37); (2%bv : reg, ZAdd (ZV 34) (ZL (-16))); (11%bv : reg, ZV 38)])
      [o; u; sp; bv_unsigned ret; bv_unsigned s0v; c'; o + 4 + 4 * u]
      constr:([Some (0, 2 ^ 62); Some (1, 127); Some (16, 2 ^ 62); @None (Z * Z); @None (Z * Z); Some (1, 2 ^ 27); Some (0, 2 ^ 62)]) regs3 m3 rom 0x35d98.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA3; kc1 S03; exact I) ltac:(exact I)
      ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto3 | zwidth; lia])).
    zx_name regs4.
    assert (R1' : getr regs4 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (2%bv : reg) as D2. zx_reg ZR (8%bv : reg) as D8.
    eexists regs4, _. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3|];
                             eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [|split; [rewrite D2; f_equal; lia | split; [rewrite D8; apply Z_to_bv_bv_unsigned | split; [apply KEEPS; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply UNCH; unchx | eapply mem_grows_trans; [apply (mem_grows_trans m m2 m3); [unfold m2; growsx | exact G3] | growsx]]]]]].
    rewrite zlen_app. unfold zlen. cbn [length]. rewrite Hlenr'.
    split; [cellx|split; [apply EXC; unchx|split; [|lia]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length r)) by lia.
    apply arr32_snoc'; try lia. exact Harr3.
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.

End S.
