(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_mul1 BnA_mul2.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Definition it27_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 10; 11; 13; 14; 15; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29].
Definition all_but_8_9_12_30_31 : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29].

Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma it27_A : forall regs m (o r : Z) (l : list Z) (exb : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 16%bv = Z_to_bv 64 (zlen l) -> getr regs 12%bv = Z_to_bv 64 r ->
  getr regs 17%bv = Z_to_bv 64 (o + 4) -> getr regs 6%bv = Z_to_bv 64 kFive27_lo ->
  getr regs 7%bv = Z_to_bv 64 (kFive27_hi * 16) -> getr regs 15%bv = Z_to_bv 64 MASK ->
  getr regs 5%bv = Z_to_bv 64 128 -> getr regs 28%bv = Z_to_bv 64 1 -> getr regs 13%bv = Z_to_bv 64 SHA ->
  getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) ->
  0 <= r < 2048 -> bn_at SEGS_A m o (BN l exb) -> ok l -> l <> [] -> zlen l + 3 <= 126 ->
  APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa6ac) m rom) (mkst regs' (Z_to_bv 64 0x0aa6a4) m' rom)
    /\ bn_at SEGS_A m' o (mul64 kFive27_lo kFive27_hi (BN l exb))
    /\ getr regs' 16%bv = Z_to_bv 64 (zlen (cells (mul64 kFive27_lo kFive27_hi (BN l exb))))
    /\ getr regs' 30%bv = Z_to_bv 64 r
    /\ keeps it27_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o r l exb R10 R16 R12 R17 R6 R7 R15 R5 R28 R13 R14 Hr Hbn Hok Hne Hlen Ho1 Ho2 Ho8 OSH Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _). cbn [cells BnModel.ex] in *.
  assert (Hl1 : 1 <= zlen l) by (destruct l; [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen l) as u eqn:Eu. assert (Hlen' : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity).
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 123); Some (0, 2047)]) (@nil kcell) (@nil kwin))
    30%nat [0x0aa6cc] (SCR [] []) constr:([(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (12%bv : reg, ZV 34); (17%bv : reg, ZAdd (ZV 32) (ZL 4))])
    [o; u; r] constr:([Some (IMG, HIE - 516); Some (1, 123); Some (0, 2047)]) regs m rom 0x0aa6ac.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  assert (K1 : keeps all_but_8_9_12_30_31 regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  zx_reg ZR (30%bv : reg) as A30. zx_reg ZR (31%bv : reg) as A31. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (12%bv : reg) as A12.
  zx_reg ZR (9%bv : reg) as A9.
  rename ZM into M1. clear ZE ZR ZF.
  (* [comment removed for export] *)
  unfold mul64. cbn [cells BnModel.ex]. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
  pose proof (mul64_l_spec l 0 Hok ltac:(lia)) as SP.
  destruct (mul64_l kFive27_lo kFive27_hi 0 l) as [rr c] eqn:Em. destruct SP as (_ & Hokr & Hlenr & Hc).
  destruct (mul64_loop_A rom l [] 0 regs1 m (o + 4)) as (regs2 & m2 & M2 & Harr2 & C31 & K2 & U2 & G2);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { exact A12. } { exact A8. } { rewrite A9. f_equal. lia. } { exact A31. } { kept K1 6 R6. } { kept K1 7 R7. } { kept K1 15 R15. }
  { kept K1 13 R13. }
  { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { replace (o + 4 - 4) with o by lia. exact Ho8. }
  { replace (o + 4 - 4) with o by lia. exact OSH. } { lia. } { exact Carr. }
  { eapply sc_store_in; [exact Hsto|]. zwidth. lia. }
  rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
  cbn [length app Z.of_nat] in U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
  assert (B10 : getr regs1 10%bv = Z_to_bv 64 o) by (kept K1 10 R10).
  assert (B16 : getr regs1 16%bv = Z_to_bv 64 u) by (kept K1 16 R16).
  assert (B17 : getr regs1 17%bv = Z_to_bv 64 (o + 4)) by (kept K1 17 R17).
  assert (B5 : getr regs1 5%bv = Z_to_bv 64 128) by (kept K1 5 R5).
  assert (B28 : getr regs1 28%bv = Z_to_bv 64 1) by (kept K1 28 R28).
  assert (B15 : getr regs1 15%bv = Z_to_bv 64 MASK) by (kept K1 15 R15).
  assert (B13 : getr regs1 13%bv = Z_to_bv 64 SHA) by (kept K1 13 R13).
  assert (B14 : getr regs1 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K1 14 R14).
  assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (kept K2 10 B10).
  assert (C16 : getr regs2 16%bv = Z_to_bv 64 u) by (kept K2 16 B16).
  assert (C17 : getr regs2 17%bv = Z_to_bv 64 (o + 4)) by (kept K2 17 B17).
  assert (C5 : getr regs2 5%bv = Z_to_bv 64 128) by (kept K2 5 B5).
  assert (C28 : getr regs2 28%bv = Z_to_bv 64 1) by (kept K2 28 B28).
  assert (C15 : getr regs2 15%bv = Z_to_bv 64 MASK) by (kept K2 15 B15).
  assert (C13 : getr regs2 13%bv = Z_to_bv 64 SHA) by (kept K2 13 B13).
  assert (C14 : getr regs2 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K2 14 B14).
  assert (C30 : getr regs2 30%bv = Z_to_bv 64 r) by (kept K2 30 A30).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_A m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  assert (Cu2 : cellN SEGS_A m2 o 2 u).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
  assert (Ce2 : cellN SEGS_A m2 (o + 2) 2 exb).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce]. }
  assert (OSH2 : objsh m2 o).
  { eapply (objsh_unch m _ _); [exact U2 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* [comment removed for export] *)
    subst c. rewrite chunks_0, app_nil_r.
    zx_run SEGS_A constr:(CTX vi_regs (@nil kcell) (@nil kwin)) 5%nat [0x0aa734; 0x0aa6a4] (SCR [] []) constr:([(31%bv : reg, ZL 0)])
      (@nil Z) constr:(@nil (option (Z * Z))) regs2 m2 rom 0x0aa730.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact ZM]|].
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite Hlenr, <- Eu. exact Cu2.
      - exact Ce2.
      - exact Harr2. }
    split; [cbn [cells]; rewrite Hlenr, <- Eu; etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C16]|].
    split; [etransitivity; [exact (reg_kept _ _ _ _ (30%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C30]|].
    split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|];
            eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|];
            eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|exact G2].
    eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
  - (* [comment removed for export] *)
    assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63))).
    { unfold B. destruct (Z_lt_dec c 268435456); [exists 1, (268435456 - 1); lia|].
      destruct (Z_lt_dec c (268435456 * 268435456)); [exists 268435456, (268435456 * 268435456 - 1); lia|].
      exists (268435456 * 268435456), (2 ^ 63); lia. }
    destruct Hcls as (clo & chi & Hcc & Hcls).
    destruct (car64_A rom regs2 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & D16' & K4 & U4 & G4).
    { exact C10. } { exact C16. } { exact C31. } { exact C17. } { exact C14. } { exact C5. } { exact C28. } { exact C15. } { exact C13. }
    { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact OSH2. } { exact Harr2. } { exact Hsto2. }
    eexists regs4, m4. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact M4]|].
    assert (Hck : zlen (chunks 3 c) <= 3).
    { pose proof (chunks_spec 3 c ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & _ & _ & H). exact H. }
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite zlen_app, Hlenr, <- Eu. exact Cu4.
      - eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Ce2].
      - exact Harr4. }
    split; [cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; exact D16'|].
    split; [kept K4 30 C30|].
    split.
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
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
#[using="Type"] Lemma loop27_A : forall f regs m (o r : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 16%bv = Z_to_bv 64 (zlen (cells b)) -> getr regs 12%bv = Z_to_bv 64 r ->
  getr regs 17%bv = Z_to_bv 64 (o + 4) -> getr regs 6%bv = Z_to_bv 64 kFive27_lo ->
  getr regs 7%bv = Z_to_bv 64 (kFive27_hi * 16) -> getr regs 15%bv = Z_to_bv 64 MASK ->
  getr regs 5%bv = Z_to_bv 64 128 -> getr regs 28%bv = Z_to_bv 64 1 -> getr regs 13%bv = Z_to_bv 64 SHA ->
  getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 29%bv = Z_to_bv 64 53 ->
  27 <= r < 2048 -> r - 27 < 27 * (Z.of_nat f + 1) ->
  bn_at SEGS_A m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa6ac) m rom) (mkst regs' (Z_to_bv 64 0x0aa7a4) m' rom)
    /\ (let b' := fst (pow27_loop f (r - 27) (mul64 kFive27_lo kFive27_hi b)) in
        let r' := snd (pow27_loop f (r - 27) (mul64 kFive27_lo kFive27_hi b)) in
        bn_at SEGS_A m' o b' /\ getr regs' 16%bv = Z_to_bv 64 (zlen (cells b')) /\ getr regs' 12%bv = Z_to_bv 64 r'
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b
        /\ val (cells b') * 5 ^ r' < B ^ 124 /\ 0 <= r' < 27)
    /\ keeps it27_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  induction f as [|f IH]; intros regs m o r b R10 R16 R12 R17 R6 R7 R15 R5 R28 R13 R14 R29 Hr Hf Hbn Hok Hn Hne Hv Ho1 Ho2 Ho8 OSH Hsto.
  all: pose proof (cap_bound (cells b) r 2 Hok Hn ltac:(lia) ltac:(lia) Hv ltac:(eapply Z.le_trans; [apply five27_ge | apply Z.pow_le_mono_r; lia])) as Hcap.
  all: destruct b as [l exb]; cbn [cells BnModel.ex] in *.
  all: destruct (it27_A regs m o r l exb R10 R16 R12 R17 R6 R7 R15 R5 R28 R13 R14 ltac:(lia) Hbn Hok Hne ltac:(lia) Ho1 Ho2 Ho8 OSH Hsto)
      as (regs1 & m1 & M1 & Hbn1 & C16 & C30 & K1 & U1 & G1).
  all: pose proof (mul64_spec (BN l exb) Hok Hn) as SP1; cbn zeta in SP1; destruct SP1 as (Hok1 & Hn1 & Hv1 & Hex1).
  all: assert (Hne1 : cells (mul64 kFive27_lo kFive27_hi (BN l exb)) <> []) by (intros HH; apply (proj1 (mul64_cells_nil _)) in HH; exact (Hne HH)).
  all: remember (mul64 kFive27_lo kFive27_hi (BN l exb)) as b1 eqn:Eb1; cbn [BnModel.cells BnModel.ex] in *.
  all: assert (Hv1' : val (cells b1) * 5 ^ (r - 27) < B ^ 124)
        by (rewrite Hv1; replace (5 ^ r) with (5 ^ 27 * 5 ^ (r - 27)) in Hv by (rewrite <- Z.pow_add_r by lia; f_equal; lia); lia).
  all: assert (C29 : getr regs1 29%bv = Z_to_bv 64 53) by (kept K1 29 R29).
  all: assert (OSH1 : objsh m1 o) by (eapply (objsh_unch m _ _); [exact U1 | intros r0 [<-|[<-|[]]]; cbn; lia | lia | lia | exact OSH]).
  - (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (27, 53)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa6ac; 0x0aa7a4] (SCR [true] [])
      constr:([(30%bv : reg, ZV 32); (29%bv : reg, ZL 53)]) [r] constr:([Some (27, 53)]) regs1 m1 rom 0x0aa6a4.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
    eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
    cbn [pow27_loop fst snd].
    split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
    split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C16]|].
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|]. repeat split; auto; lia.
  - destruct (Z_le_dec r 53) as [Hle|Hgt].
    + (* [comment removed for export] *)
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (27, 53)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa6ac; 0x0aa7a4] (SCR [true] [])
        constr:([(30%bv : reg, ZV 32); (29%bv : reg, ZL 53)]) [r] constr:([Some (27, 53)]) regs1 m1 rom 0x0aa6a4.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
      cbn [pow27_loop]. replace (r - 27 <? 27) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
      split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C16]|].
      split; [etransitivity; [zx_regv ZR|]; f_equal; lia|]. repeat split; auto; lia.
    + (* [comment removed for export] *)
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (54, 2047)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa6ac; 0x0aa7a4] (SCR [false] [])
        constr:([(30%bv : reg, ZV 32); (29%bv : reg, ZL 53)]) [r] constr:([Some (54, 2047)]) regs1 m1 rom 0x0aa6a4.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      assert (K2 : keeps it27_keep regs regs2) by (eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]).
      cbn [pow27_loop]. replace (r - 27 <? 27) with false by (symmetry; apply Z.ltb_ge; lia).
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_A m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G1 | exact Hsto]).
      destruct (IH regs2 m1 o (r - 27) b1) as (regs3 & m3 & M3 & POST & K3 & U3 & G3).
      { kept K2 10 R10. }
      { etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C16]. }
      { etransitivity; [zx_regv ZR|]; f_equal; lia. }
      { kept K2 17 R17. } { kept K2 6 R6. } { kept K2 7 R7. } { kept K2 15 R15. } { kept K2 5 R5. } { kept K2 28 R28. } { kept K2 13 R13. }
      { kept K2 14 R14. } { kept K2 29 R29. }
      { lia. } { lia. } { subst b1; exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1'. } { lia. } { lia. } { lia. }
      { exact OSH1. } { exact Hsto1. }
      eexists regs3, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact ZM | exact M3]|].
      subst b1. replace (r - 27 - 27) with (r - 54) in POST by lia. replace (r - 27 - 27) with (r - 54) by lia.
      split; [cbn zeta in POST |- *; rewrite Hex1 in POST; exact POST|].
      split; [eapply keeps_trans; [exact K2 | exact K3]|].
      split; [eapply unch_trans; [exact U1 | exact U3] | eapply mem_grows_trans; [exact G1 | exact G3]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition it13_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 10; 11; 13; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28].
Definition all_but_8_12_29_30_31 : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28].

#[using="Type"] Lemma it13_A : forall regs m (o r : Z) (l : list Z) (exb : Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 16%bv = Z_to_bv 64 (zlen l) -> getr regs 12%bv = Z_to_bv 64 r ->
  getr regs 17%bv = Z_to_bv 64 (o + 4) -> getr regs 6%bv = Z_to_bv 64 kFive13 -> getr regs 15%bv = Z_to_bv 64 MASK ->
  getr regs 5%bv = Z_to_bv 64 128 -> getr regs 7%bv = Z_to_bv 64 1 -> getr regs 13%bv = Z_to_bv 64 SHA ->
  getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) ->
  0 <= r < 2048 -> bn_at SEGS_A m o (BN l exb) -> ok l -> l <> [] -> zlen l + 3 <= 126 ->
  APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa7e0) m rom) (mkst regs' (Z_to_bv 64 0x0aa7d8) m' rom)
    /\ bn_at SEGS_A m' o (mul32 kFive13 (BN l exb))
    /\ getr regs' 16%bv = Z_to_bv 64 (zlen (cells (mul32 kFive13 (BN l exb))))
    /\ getr regs' 29%bv = Z_to_bv 64 r
    /\ keeps it13_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o r l exb R10 R16 R12 R17 R6 R15 R5 R7 R13 R14 Hr Hbn Hok Hne Hlen Ho1 Ho2 Ho8 OSH Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _). cbn [cells BnModel.ex] in *.
  assert (Hl1 : 1 <= zlen l) by (destruct l; [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen l) as u eqn:Eu. assert (Hlen' : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity).
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 123); Some (0, 2047)]) (@nil kcell) (@nil kwin))
    30%nat [0x0aa800] (SCR [] []) constr:([(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (12%bv : reg, ZV 34); (17%bv : reg, ZAdd (ZV 32) (ZL 4))])
    [o; u; r] constr:([Some (IMG, HIE - 516); Some (1, 123); Some (0, 2047)]) regs m rom 0x0aa7e0.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  assert (K1 : keeps all_but_8_12_29_30_31 regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  zx_reg ZR (29%bv : reg) as A29. zx_reg ZR (30%bv : reg) as A30. zx_reg ZR (31%bv : reg) as A31. zx_reg ZR (12%bv : reg) as A12.
  zx_reg ZR (8%bv : reg) as A8.
  rename ZM into M1. clear ZE ZR ZF.
  assert (B10 : getr regs1 10%bv = Z_to_bv 64 o) by (kept K1 10 R10).
  assert (B16 : getr regs1 16%bv = Z_to_bv 64 u) by (kept K1 16 R16).
  assert (B17 : getr regs1 17%bv = Z_to_bv 64 (o + 4)) by (kept K1 17 R17).
  assert (B6 : getr regs1 6%bv = Z_to_bv 64 kFive13) by (kept K1 6 R6).
  assert (B15 : getr regs1 15%bv = Z_to_bv 64 MASK) by (kept K1 15 R15).
  assert (B5 : getr regs1 5%bv = Z_to_bv 64 128) by (kept K1 5 R5).
  assert (B7 : getr regs1 7%bv = Z_to_bv 64 1) by (kept K1 7 R7).
  assert (B13 : getr regs1 13%bv = Z_to_bv 64 SHA) by (kept K1 13 R13).
  assert (B14 : getr regs1 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K1 14 R14).
  (* [comment removed for export] *)
  unfold mul32. cbn [cells BnModel.ex Z.eqb kFive13 Pos.eqb]. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
  pose proof (mul32_l_spec kFive13 l 0 Hok ltac:(unfold kFive13; lia) ltac:(lia)) as SP.
  unfold kFive13 in *.
  destruct (mul32_l 1220703125 0 l) as [rr c] eqn:Em. destruct SP as (_ & Hokr & Hlenr & Hc0' & HcF). specialize (HcF ltac:(lia)).
  destruct (m13_loop_A rom l [] 0 regs1 m (o + 4) 1220703125) as (regs2 & m2 & tmp & M2 & Harr2 & C30 & C9 & HT1 & HT2 & K2 & U2 & G2);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { exact A12. } { exact A31. } { rewrite A8. f_equal. lia. } { exact A30. } { exact B6. } { exact B15. } { exact B13. }
  { lia. } { lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { replace (o + 4 - 4) with o by lia. exact Ho8. }
  { replace (o + 4 - 4) with o by lia. exact OSH. } { lia. } { exact Carr. }
  { eapply sc_store_in; [exact Hsto|]. zwidth. lia. }
  rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
  cbn [length app Z.of_nat] in U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
  assert (C10 : getr regs2 10%bv = Z_to_bv 64 o) by (kept K2 10 B10).
  assert (C16 : getr regs2 16%bv = Z_to_bv 64 u) by (kept K2 16 B16).
  assert (C17 : getr regs2 17%bv = Z_to_bv 64 (o + 4)) by (kept K2 17 B17).
  assert (C5 : getr regs2 5%bv = Z_to_bv 64 128) by (kept K2 5 B5).
  assert (C7 : getr regs2 7%bv = Z_to_bv 64 1) by (kept K2 7 B7).
  assert (C15 : getr regs2 15%bv = Z_to_bv 64 MASK) by (kept K2 15 B15).
  assert (C13 : getr regs2 13%bv = Z_to_bv 64 SHA) by (kept K2 13 B13).
  assert (C14 : getr regs2 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K2 14 B14).
  assert (C29 : getr regs2 29%bv = Z_to_bv 64 r) by (kept K2 29 A29).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_A m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  assert (Cu2 : cellN SEGS_A m2 o 2 u).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
  assert (Ce2 : cellN SEGS_A m2 (o + 2) 2 exb).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce]. }
  assert (OSH2 : objsh m2 o).
  { eapply (objsh_unch m _ _); [exact U2 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* [comment removed for export] *)
    rewrite Hc0 in *. rewrite chunks_0, app_nil_r.
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (0, 2 ^ 28 - 1)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa854; 0x0aa7d8] (SCR [] [])
      constr:([(9%bv : reg, ZV 32)]) [tmp] constr:([Some (0, 2 ^ 28 - 1)]) regs2 m2 rom 0x0aa84c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact ZM]|].
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite Hlenr, <- Eu. exact Cu2.
      - exact Ce2.
      - exact Harr2. }
    split; [cbn [cells]; rewrite Hlenr, <- Eu; etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C16]|].
    split; [etransitivity; [exact (reg_kept _ _ _ _ (29%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C29]|].
    split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|];
            eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|];
            eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|exact G2].
    eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
  - (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (2 ^ 28, 2 ^ 60 - 1)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa854; 0x0aa7d8] (SCR [] [])
      constr:([(9%bv : reg, ZV 32)]) [tmp] constr:([Some (2 ^ 28, 2 ^ 60 - 1)]) regs2 m2 rom 0x0aa84c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    assert (K3 : keeps it13_keep regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    assert (K3' : keeps [10; 16; 30; 17; 14; 5; 7; 15; 13; 29] regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    rename ZM into M3. clear ZE ZR ZF.
    assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1) \/ (clo = B * B /\ chi = 2 ^ 63))).
    { unfold B. destruct (Z_lt_dec c 268435456); [exists 1, (268435456 - 1); lia|].
      exists 268435456, (268435456 * 268435456 - 1); lia. }
    destruct Hcls as (clo & chi & Hcc & Hcls).
    destruct (car13_A rom regs3 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & D16' & K4 & U4 & G4).
    { kept K3' 10 C10. } { kept K3' 16 C16. } { kept K3' 30 C30. } { kept K3' 17 C17. } { kept K3' 14 C14. } { kept K3' 5 C5. } { kept K3' 7 C7. }
    { kept K3' 15 C15. } { kept K3' 13 C13. }
    { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact OSH2. } { exact Harr2. } { exact Hsto2. }
    eexists regs4, m4. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4]|].
    assert (Hck : zlen (chunks 3 c) <= 3).
    { pose proof (chunks_spec 3 c ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & _ & _ & H). exact H. }
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite zlen_app, Hlenr, <- Eu. exact Cu4.
      - eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Ce2].
      - exact Harr4. }
    split; [cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; exact D16'|].
    split; [etransitivity; [exact (K4 29 ltac:(in_list))|]; kept K3' 29 C29|].
    split.
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
      eapply keeps_trans; [exact K3|]. eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
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
#[using="Type"] Lemma loop13_A : forall f regs m (o r : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 16%bv = Z_to_bv 64 (zlen (cells b)) -> getr regs 12%bv = Z_to_bv 64 r ->
  getr regs 17%bv = Z_to_bv 64 (o + 4) -> getr regs 6%bv = Z_to_bv 64 kFive13 -> getr regs 15%bv = Z_to_bv 64 MASK ->
  getr regs 5%bv = Z_to_bv 64 128 -> getr regs 7%bv = Z_to_bv 64 1 -> getr regs 13%bv = Z_to_bv 64 SHA ->
  getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 28%bv = Z_to_bv 64 25 ->
  13 <= r < 2048 -> r - 13 < 13 * (Z.of_nat f + 1) ->
  bn_at SEGS_A m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objsh m o ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa7e0) m rom) (mkst regs' (Z_to_bv 64 0x0aa8c0) m' rom)
    /\ (let b' := fst (pow13_loop f (r - 13) (mul32 kFive13 b)) in
        let r' := snd (pow13_loop f (r - 13) (mul32 kFive13 b)) in
        bn_at SEGS_A m' o b' /\ getr regs' 16%bv = Z_to_bv 64 (zlen (cells b')) /\ getr regs' 12%bv = Z_to_bv 64 r'
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b
        /\ val (cells b') * 5 ^ r' < B ^ 124 /\ 0 <= r' < 13)
    /\ keeps it13_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  induction f as [|f IH]; intros regs m o r b R10 R16 R12 R17 R6 R15 R5 R7 R13 R14 R28 Hr Hf Hbn Hok Hn Hne Hv Ho1 Ho2 Ho8 OSH Hsto.
  all: pose proof (cap_bound (cells b) r 1 Hok Hn ltac:(lia) ltac:(lia) Hv ltac:(eapply Z.le_trans; [apply five13_ge | apply Z.pow_le_mono_r; lia])) as Hcap.
  all: destruct b as [l exb]; cbn [cells BnModel.ex] in *.
  all: destruct (it13_A regs m o r l exb R10 R16 R12 R17 R6 R15 R5 R7 R13 R14 ltac:(lia) Hbn Hok Hne ltac:(lia) Ho1 Ho2 Ho8 OSH Hsto)
      as (regs1 & m1 & M1 & Hbn1 & C16 & C29 & K1 & U1 & G1).
  all: pose proof (mul32_spec kFive13 (BN l exb) Hok Hn ltac:(unfold kFive13; lia)) as SP1; cbn zeta in SP1; destruct SP1 as (Hok1 & Hn1 & Hv1 & Hex1).
  all: specialize (Hex1 ltac:(unfold kFive13; lia)).
  all: assert (Hne1 : cells (mul32 kFive13 (BN l exb)) <> []) by (intros HH; apply (proj1 (mul32_cells_nil kFive13 _ ltac:(unfold kFive13; lia))) in HH; exact (Hne HH)).
  all: remember (mul32 kFive13 (BN l exb)) as b1 eqn:Eb1; cbn [BnModel.cells BnModel.ex] in *.
  all: assert (Hv1' : val (cells b1) * 5 ^ (r - 13) < B ^ 124)
        by (rewrite Hv1, kFive13_eq; replace (5 ^ r) with (5 ^ 13 * 5 ^ (r - 13)) in Hv by (rewrite <- Z.pow_add_r by lia; f_equal; lia); lia).
  all: assert (C28 : getr regs1 28%bv = Z_to_bv 64 25) by (kept K1 28 R28).
  all: assert (OSH1 : objsh m1 o) by (eapply (objsh_unch m _ _); [exact U1 | intros r0 [<-|[<-|[]]]; cbn; lia | lia | lia | exact OSH]).
  - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (13, 25)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa7e0; 0x0aa8c0] (SCR [true] [])
      constr:([(29%bv : reg, ZV 32); (28%bv : reg, ZL 25)]) [r] constr:([Some (13, 25)]) regs1 m1 rom 0x0aa7d8.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
    eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
    cbn [pow13_loop fst snd].
    split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
    split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C16]|].
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|]. repeat split; auto; lia.
  - destruct (Z_le_dec r 25) as [Hle|Hgt].
    + zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (13, 25)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa7e0; 0x0aa8c0] (SCR [true] [])
        constr:([(29%bv : reg, ZV 32); (28%bv : reg, ZL 25)]) [r] constr:([Some (13, 25)]) regs1 m1 rom 0x0aa7d8.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
      cbn [pow13_loop]. replace (r - 13 <? 13) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
      split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C16]|].
      split; [etransitivity; [zx_regv ZR|]; f_equal; lia|]. repeat split; auto; lia.
    + zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (26, 2047)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa7e0; 0x0aa8c0] (SCR [false] [])
        constr:([(29%bv : reg, ZV 32); (28%bv : reg, ZL 25)]) [r] constr:([Some (26, 2047)]) regs1 m1 rom 0x0aa7d8.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      assert (K2 : keeps it13_keep regs regs2) by (eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]).
      cbn [pow13_loop]. replace (r - 13 <? 13) with false by (symmetry; apply Z.ltb_ge; lia).
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_A m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G1 | exact Hsto]).
      destruct (IH regs2 m1 o (r - 13) b1) as (regs3 & m3 & M3 & POST & K3 & U3 & G3).
      { kept K2 10 R10. }
      { etransitivity; [exact (reg_kept _ _ _ _ (16%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C16]. }
      { etransitivity; [zx_regv ZR|]; f_equal; lia. }
      { kept K2 17 R17. } { kept K2 6 R6. } { kept K2 15 R15. } { kept K2 5 R5. } { kept K2 7 R7. } { kept K2 13 R13. } { kept K2 14 R14. }
      { kept K2 28 R28. }
      { lia. } { lia. } { subst b1; exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1'. } { lia. } { lia. } { lia. }
      { exact OSH1. } { exact Hsto1. }
      eexists regs3, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact ZM | exact M3]|].
      subst b1. replace (r - 13 - 13) with (r - 26) in POST by lia. replace (r - 13 - 13) with (r - 26) by lia.
      split; [cbn zeta in POST |- *; rewrite Hex1 in POST; exact POST|].
      split; [eapply keeps_trans; [exact K2 | exact K3]|].
      split; [eapply unch_trans; [exact U1 | exact U3] | eapply mem_grows_trans; [exact G1 | exact G3]].
Qed.

End S.
