(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnP_ads1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition CS20 : list Z := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Definition add_U_spec : Prop := forall regs m (o q sp : Z) (ret : word) (l ol : list Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 q -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_U m o (BN l 0) -> bn_at SEGS_U m q (BN ol 0) -> ok l -> ok ol -> zlen l <= 127 -> 1 <= zlen ol <= 3 ->
  64 <= sp -> sp <= 2 ^ 62 -> 1 <= o -> o + 516 <= 2 ^ 62 -> 1 <= q -> q + 516 <= 2 ^ 62 ->
  (q + 516 <= o \/ o + 516 <= q) -> (o + 516 <= sp - 48 \/ sp <= o) -> (q + 516 <= sp - 48 \/ sp <= q) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 48)) 48 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x363c4) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_U m' o (BN (add_l 0 l ol) 0)
    /\ unch m m' [(o, o + 516); (sp - 48, sp)] /\ mem_grows m m'.
Hypothesis ADD : add_U_spec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aa_run lo hi regs m rom o sp d :=
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (832, 2 ^ 62); Some (lo, hi)]) (@nil kcell) [KW (ZV 33) (-620) (-104)])
    40%nat [0x363c4] (SCR [] [])
    constr:([(8%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-752))); (20%bv : reg, ZV 34); (25%bv : reg, ZL 268435455)])
    constr:([o; sp; d]) constr:([Some (0, 2 ^ 62); Some (832, 2 ^ 62); Some (lo, hi)]) regs m rom 0x35e44.

#[using="ADD"] Lemma au64add_U1 : forall regs m (o sp d : Z) (l : list Z),
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 2%bv = Z_to_bv 64 (sp - 752) -> getr regs 20%bv = Z_to_bv 64 d -> getr regs 25%bv = Z_to_bv 64 MASK ->
  1 <= d < 2 ^ 64 -> bn_at SEGS_U m o (BN l 0) -> ok l -> zlen l <= 127 ->
  832 <= sp -> sp <= 2 ^ 62 -> 1 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 816 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 816)) 816 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35e44) m rom) (mkst regs' (Z_to_bv 64 0x35bd8) m' rom)
    /\ bn_at SEGS_U m' o (BN (add_l 0 l (chunks 3 d)) 0)
    /\ keeps CS20 regs regs'
    /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m'.
Proof.
  intros regs m o sp d l R8 R2 R20 R25 Hd Hbn Hok Hlen Hsp1 Hsp2 Ho1 Ho2 Hdisj Hsto Hsts.
  unfold MASK in R25.
  pose proof (bn_ctor_store SEGS_U m (sp + -620) ltac:(lia) ltac:(lia)) as [C0 C2].
  pose proof (chunks_spec 3 d ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & Hcok & _ & Hck).
  assert (Hcl : 1 <= zlen (chunks 3 d) <= 3).
  { split; [|exact Hck]. destruct (chunks 3 d) eqn:Ec; [|rewrite zlen_cons; pose proof (zlen_nonneg l0); lia].
    exfalso. assert (CASES : 1 <= d < B \/ B <= d < B * B \/ B * B <= d < M64) by (unfold B; lia).
    destruct CASES as [H|[H|H]]; [rewrite chunks_1 in Ec by exact H | rewrite chunks_2 in Ec by exact H | rewrite chunks_3 in Ec by exact H]; discriminate. }
  (* [comment removed for export] *)
  assert (CONT : forall regs1 m1,
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35e44) m rom) (mkst regs1 (Z_to_bv 64 0x363c4) m1 rom) ->
    getr regs1 10%bv = Z_to_bv 64 o -> getr regs1 11%bv = Z_to_bv 64 (sp + -620) -> getr regs1 2%bv = Z_to_bv 64 (sp + -752) ->
    getr regs1 1%bv = Z_to_bv 64 220792 ->
    bn_at SEGS_U m1 (sp + -620) (BN (chunks 3 d) 0) ->
    keeps CS20 regs regs1 -> unch m m1 [(sp - 620, sp - 104)] -> mem_grows m m1 ->
    exists regs' m',
      msteps SEGS_U (mkst regs (Z_to_bv 64 0x35e44) m rom) (mkst regs' (Z_to_bv 64 0x35bd8) m' rom)
      /\ bn_at SEGS_U m' o (BN (add_l 0 l (chunks 3 d)) 0)
      /\ keeps CS20 regs regs'
      /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m').
  { intros regs1 m1 M1 A10 A11 A2 A1 Hq K1 U1 G1.
    destruct (ADD regs1 m1 o (sp + -620) (sp + -752) (Z_to_bv 64 220792) l (chunks 3 d)) as (regs2 & m2 & M2 & K2 & Hbn2 & U2 & G2).
    { exact A10. } { exact A11. } { exact A2. } { exact A1. } { vm_compute. reflexivity. }
    { eapply (bn_at_unch SEGS_U _ _ o _ _ U1); [lia | cbn; lia | | exact Hbn]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
    { exact Hq. } { exact Hok. } { exact Hcok. } { exact Hlen. } { exact Hcl. }
    { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
    { eapply store_ok_grows; [exact G1 | exact Hsto]. }
    { eapply store_ok_grows; [exact G1 |]. eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
    (* [comment removed for export] *)
    zx_run SEGS_U constr:(CTX vi_regs (@nil kcell) (@nil kwin)) 3%nat [0x35bd8] (SCR [] []) constr:(@nil (reg * zx))
      (@nil Z) constr:(@nil (option (Z * Z))) regs2 m2 rom 0x35e78.
    zx_use ZXB ltac:(exact I) ltac:(exact I) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact ZM]|].
    split; [exact Hbn2|].
    split; [eapply keeps_trans; [exact K1|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|];
            eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|eapply mem_grows_trans; [exact G1 | exact G2]].
    apply (unch_trans m m1 m2).
    - eapply unch_widen; [exact U1|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; right; left; reflexivity|cbn; lia].
    - eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]].
      + eexists; split; [left; reflexivity|cbn; lia].
      + eexists; split; [right; left; reflexivity|cbn; lia]. }
  assert (CASES : 1 <= d < B \/ B <= d < B * B \/ B * B <= d < M64) by (unfold B; lia).
  destruct CASES as [Hv1 | [Hv2 | Hv3]].
  - rewrite chunks_1 in * by exact Hv1. unfold B in *.
    aa_run 1 (2 ^ 28 - 1) regs m rom o sp d.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I). zx_name regs1.
    eapply CONT; [exact ZM | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj; unchx | growsx].
    clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj R8 R2 R20 R25. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [d])) with 1.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. replace (sp + -620 + 4 + 4 * Z.of_nat 0) with (sp + -616) by lia. cellx.
  - rewrite chunks_2 in * by exact Hv2. unfold B in *.
    aa_run (2 ^ 28) (2 ^ 56 - 1) regs m rom o sp d.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I). zx_name regs1.
    assert (HB1 : 0 <= d mod 268435456 < 268435456) by lia. assert (HB2 : 1 <= d / 268435456 < 268435456) by lia.
    change (2 ^ 28) with 268435456 in *.
    remember (d mod 268435456) as c1 eqn:E1. remember (d / 268435456) as c2 eqn:E2. clear E1 E2.
    eapply CONT; [exact ZM | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj; unchx | growsx].
    clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj R8 R2 R20 R25. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [c1; c2])) with 2.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i as [|[|]]; [| |lia]; cbn [nth]; zwidth.
    + replace (sp + -620 + 4 + 4 * 0) with (sp + -616) by lia. cellx.
    + replace (sp + -620 + 4 + 4 * 1) with (sp + -612) by lia. cellx.
  - rewrite chunks_3 in * by exact Hv3. unfold B in *.
    aa_run (2 ^ 56) (2 ^ 64 - 1) regs m rom o sp d.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I). zx_name regs1.
    assert (HB1 : 0 <= d mod 268435456 < 268435456) by lia. assert (HB2 : 0 <= d / 268435456 mod 268435456 < 268435456) by lia.
    assert (HB3 : 1 <= d / 268435456 / 268435456 < 256) by lia.
    change (2 ^ 28) with 268435456 in *.
    remember (d mod 268435456) as c1 eqn:E1. remember (d / 268435456 mod 268435456) as c2 eqn:E2. remember (d / 268435456 / 268435456) as c3 eqn:E3. clear E1 E2 E3.
    eapply CONT; [exact ZM | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj; unchx | growsx].
    clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj R8 R2 R20 R25. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [c1; c2; c3])) with 3.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i as [|[|[|]]]; [| | |lia]; cbn [nth]; zwidth.
    + replace (sp + -620 + 4 + 4 * 0) with (sp + -616) by lia. cellx.
    + replace (sp + -620 + 4 + 4 * 1) with (sp + -612) by lia. cellx.
    + replace (sp + -620 + 4 + 4 * 2) with (sp + -608) by lia. cellx.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ab_run lo hi regs m rom o sp d :=
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (832, 2 ^ 62); Some (lo, hi)]) (@nil kcell) [KW (ZV 33) (-620) (-104)])
    40%nat [0x363c4] (SCR [] [])
    constr:([(8%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-752))); (18%bv : reg, ZV 34)])
    constr:([o; sp; d]) constr:([Some (0, 2 ^ 62); Some (832, 2 ^ 62); Some (lo, hi)]) regs m rom 0x35ed0.

#[using="ADD"] Lemma au64add_U2 : forall regs m (o sp d : Z) (l : list Z),
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 2%bv = Z_to_bv 64 (sp - 752) -> getr regs 18%bv = Z_to_bv 64 d ->
  1 <= d < 2 ^ 64 -> bn_at SEGS_U m o (BN l 0) -> ok l -> zlen l <= 127 ->
  832 <= sp -> sp <= 2 ^ 62 -> 1 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 816 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 816)) 816 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35ed0) m rom) (mkst regs' (Z_to_bv 64 0x35f0c) m' rom)
    /\ bn_at SEGS_U m' o (BN (add_l 0 l (chunks 3 d)) 0)
    /\ keeps CS18 regs regs'
    /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m'.
Proof.
  intros regs m o sp d l R8 R2 R18 Hd Hbn Hok Hlen Hsp1 Hsp2 Ho1 Ho2 Hdisj Hsto Hsts.
  pose proof (bn_ctor_store SEGS_U m (sp + -620) ltac:(lia) ltac:(lia)) as [C0 C2].
  pose proof (chunks_spec 3 d ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & Hcok & _ & Hck).
  assert (Hcl : 1 <= zlen (chunks 3 d) <= 3).
  { split; [|exact Hck]. destruct (chunks 3 d) eqn:Ec; [|rewrite zlen_cons; pose proof (zlen_nonneg l0); lia].
    exfalso. assert (CASES : 1 <= d < B \/ B <= d < B * B \/ B * B <= d < M64) by (unfold B; lia).
    destruct CASES as [H|[H|H]]; [rewrite chunks_1 in Ec by exact H | rewrite chunks_2 in Ec by exact H | rewrite chunks_3 in Ec by exact H]; discriminate. }
  (* [comment removed for export] *)
  assert (CONT : forall regs1 m1,
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35ed0) m rom) (mkst regs1 (Z_to_bv 64 0x363c4) m1 rom) ->
    getr regs1 10%bv = Z_to_bv 64 o -> getr regs1 11%bv = Z_to_bv 64 (sp + -620) -> getr regs1 2%bv = Z_to_bv 64 (sp + -752) ->
    getr regs1 1%bv = Z_to_bv 64 220940 ->
    bn_at SEGS_U m1 (sp + -620) (BN (chunks 3 d) 0) ->
    keeps CS18 regs regs1 -> unch m m1 [(sp - 620, sp - 104)] -> mem_grows m m1 ->
    exists regs' m',
      msteps SEGS_U (mkst regs (Z_to_bv 64 0x35ed0) m rom) (mkst regs' (Z_to_bv 64 0x35f0c) m' rom)
      /\ bn_at SEGS_U m' o (BN (add_l 0 l (chunks 3 d)) 0)
      /\ keeps CS18 regs regs'
      /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m').
  { intros regs1 m1 M1 A10 A11 A2 A1 Hq K1 U1 G1.
    destruct (ADD regs1 m1 o (sp + -620) (sp + -752) (Z_to_bv 64 220940) l (chunks 3 d)) as (regs2 & m2 & M2 & K2 & Hbn2 & U2 & G2).
    { exact A10. } { exact A11. } { exact A2. } { exact A1. } { vm_compute. reflexivity. }
    { eapply (bn_at_unch SEGS_U _ _ o _ _ U1); [lia | cbn; lia | | exact Hbn]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
    { exact Hq. } { exact Hok. } { exact Hcok. } { exact Hlen. } { exact Hcl. }
    { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
    { eapply store_ok_grows; [exact G1 | exact Hsto]. }
    { eapply store_ok_grows; [exact G1 |]. eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact M1 | exact M2]|].
    split; [exact Hbn2|].
    split; [eapply keeps_trans; [exact K1|]; eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
    split; [|eapply mem_grows_trans; [exact G1 | exact G2]].
    apply (unch_trans m m1 m2).
    - eapply unch_widen; [exact U1|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; right; left; reflexivity|cbn; lia].
    - eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]].
      + eexists; split; [left; reflexivity|cbn; lia].
      + eexists; split; [right; left; reflexivity|cbn; lia]. }
  assert (CASES : 1 <= d < B \/ B <= d < B * B \/ B * B <= d < M64) by (unfold B; lia).
  destruct CASES as [Hv1 | [Hv2 | Hv3]].
  - rewrite chunks_1 in * by exact Hv1. unfold B in *.
    ab_run 1 (2 ^ 28 - 1) regs m rom o sp d.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I). zx_name regs1.
    eapply CONT; [exact ZM | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj; unchx | growsx].
    clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj R8 R2 R18. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [d])) with 1.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. replace (sp + -620 + 4 + 4 * Z.of_nat 0) with (sp + -616) by lia. cellx.
  - rewrite chunks_2 in * by exact Hv2. unfold B in *.
    ab_run (2 ^ 28) (2 ^ 56 - 1) regs m rom o sp d.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I). zx_name regs1.
    assert (HB1 : 0 <= d mod 268435456 < 268435456) by lia. assert (HB2 : 1 <= d / 268435456 < 268435456) by lia.
    change (2 ^ 28) with 268435456 in *.
    remember (d mod 268435456) as c1 eqn:E1. remember (d / 268435456) as c2 eqn:E2. clear E1 E2.
    eapply CONT; [exact ZM | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj; unchx | growsx].
    clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj R8 R2 R18. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [c1; c2])) with 2.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i as [|[|]]; [| |lia]; cbn [nth]; zwidth.
    + replace (sp + -620 + 4 + 4 * 0) with (sp + -616) by lia. cellx.
    + replace (sp + -620 + 4 + 4 * 1) with (sp + -612) by lia. cellx.
  - rewrite chunks_3 in * by exact Hv3. unfold B in *.
    ab_run (2 ^ 56) (2 ^ 64 - 1) regs m rom o sp d.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I). zx_name regs1.
    assert (HB1 : 0 <= d mod 268435456 < 268435456) by lia. assert (HB2 : 0 <= d / 268435456 mod 268435456 < 268435456) by lia.
    assert (HB3 : 1 <= d / 268435456 / 268435456 < 256) by lia.
    change (2 ^ 28) with 268435456 in *.
    remember (d mod 268435456) as c1 eqn:E1. remember (d / 268435456 mod 268435456) as c2 eqn:E2. remember (d / 268435456 / 268435456) as c3 eqn:E3. clear E1 E2 E3.
    eapply CONT; [exact ZM | zx_regv ZR | zx_regv ZR | zx_regv ZR | zx_regv ZR | | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj; unchx | growsx].
    clear ZM ZE ZR ZF CONT Hbn Hsto Hsts Hdisj R8 R2 R18. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [c1; c2; c3])) with 3.
    split; [cellx|split; [cellx|split; [|lia]]].
    apply arr32_store_other; zwidth; try lia.
    intros i Hi. cbn in Hi. destruct i as [|[|[|]]]; [| | |lia]; cbn [nth]; zwidth.
    + replace (sp + -620 + 4 + 4 * 0) with (sp + -616) by lia. cellx.
    + replace (sp + -620 + 4 + 4 * 1) with (sp + -612) by lia. cellx.
    + replace (sp + -620 + 4 + 4 * 2) with (sp + -608) by lia. cellx.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ptr_tblU (m : word -> option byte) (sp buf : Z) : Prop :=
  cellN SEGS_U m (sp - 632) 8 (buf + 1) /\
  cellN SEGS_U m (sp - 640) 8 (buf + 2) /\
  cellN SEGS_U m (sp - 648) 8 (buf + 3) /\
  cellN SEGS_U m (sp - 656) 8 (buf + 4) /\
  cellN SEGS_U m (sp - 664) 8 (buf + 5) /\
  cellN SEGS_U m (sp - 672) 8 (buf + 6) /\
  cellN SEGS_U m (sp - 680) 8 (buf + 7) /\
  cellN SEGS_U m (sp - 688) 8 (buf + 8) /\
  cellN SEGS_U m (sp - 696) 8 (buf + 9) /\
  cellN SEGS_U m (sp - 704) 8 (buf + 10) /\
  cellN SEGS_U m (sp - 712) 8 (buf + 11) /\
  cellN SEGS_U m (sp - 720) 8 (buf + 12) /\
  cellN SEGS_U m (sp - 728) 8 (buf + 13) /\
  cellN SEGS_U m (sp - 736) 8 (buf + 14) /\
  cellN SEGS_U m (sp - 744) 8 (buf + 15) /\
  cellN SEGS_U m (sp - 752) 8 (buf + 16).

#[using="Type"] Lemma ptr_tblU_unch : forall m m' sp buf rs,
  unch m m' rs -> 832 <= sp -> sp <= 2 ^ 62 -> (forall r, In r rs -> sp - 624 <= fst r \/ snd r <= sp - 752) ->
  ptr_tblU m sp buf -> ptr_tblU m' sp buf.
Proof.
  intros m m' sp buf rs U Hsp1 Hsp2 Hd P. unfold ptr_tblU in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- cellN _ _ ?a _ _ => eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; specialize (Hd rg Hrg); cbn; zwidth; lia | tauto] end.
Qed.

(* [comment removed for export] *)
Definition rd_regsU (regs : bvmap 5 word) (buf : Z) : Prop :=
  getr regs 21%bv = Z_to_bv 64 (buf + 17) /\ getr regs 22%bv = Z_to_bv 64 (buf + 18)
  /\ getr regs 23%bv = Z_to_bv 64 (18446744073709551615 - buf)
  /\ getr regs 24%bv = Z_to_bv 64 10 /\ getr regs 25%bv = Z_to_bv 64 MASK.

Definition rd_keepU : list Z := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25].

(* [comment removed for export] *)
Abbreviation dI := (Some (48, 57)).
Abbreviation rdU_uvi := [Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (0, 761); Some (832, 2 ^ 62);
                        dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI; dI].
Abbreviation rdU_pins := [(8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (19%bv : reg, ZV 34); (2%bv : reg, ZAdd (ZV 35) (ZL (-752)));
  (24%bv : reg, ZL 10); (25%bv : reg, ZL 268435455); (21%bv : reg, ZAdd (ZV 33) (ZL 17)); (22%bv : reg, ZAdd (ZV 33) (ZL 18));
  (23%bv : reg, ZSub (ZL 18446744073709551615) (ZV 33))].
Abbreviation rdU_kn :=
 [KC (ZV 35) (-632) 8 (ZAdd (ZV 33) (ZL 1));
  KC (ZV 35) (-640) 8 (ZAdd (ZV 33) (ZL 2));
  KC (ZV 35) (-648) 8 (ZAdd (ZV 33) (ZL 3));
  KC (ZV 35) (-656) 8 (ZAdd (ZV 33) (ZL 4));
  KC (ZV 35) (-664) 8 (ZAdd (ZV 33) (ZL 5));
  KC (ZV 35) (-672) 8 (ZAdd (ZV 33) (ZL 6));
  KC (ZV 35) (-680) 8 (ZAdd (ZV 33) (ZL 7));
  KC (ZV 35) (-688) 8 (ZAdd (ZV 33) (ZL 8));
  KC (ZV 35) (-696) 8 (ZAdd (ZV 33) (ZL 9));
  KC (ZV 35) (-704) 8 (ZAdd (ZV 33) (ZL 10));
  KC (ZV 35) (-712) 8 (ZAdd (ZV 33) (ZL 11));
  KC (ZV 35) (-720) 8 (ZAdd (ZV 33) (ZL 12));
  KC (ZV 35) (-728) 8 (ZAdd (ZV 33) (ZL 13));
  KC (ZV 35) (-736) 8 (ZAdd (ZV 33) (ZL 14));
  KC (ZV 35) (-744) 8 (ZAdd (ZV 33) (ZL 15));
  KC (ZV 35) (-752) 8 (ZAdd (ZV 33) (ZL 16));
  KC (ZAdd (ZV 33) (ZV 34)) 0 1 (ZV 36);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 1))) 0 1 (ZV 37);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 2))) 0 1 (ZV 38);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 3))) 0 1 (ZV 39);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 4))) 0 1 (ZV 40);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 5))) 0 1 (ZV 41);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 6))) 0 1 (ZV 42);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 7))) 0 1 (ZV 43);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 8))) 0 1 (ZV 44);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 9))) 0 1 (ZV 45);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 10))) 0 1 (ZV 46);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 11))) 0 1 (ZV 47);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 12))) 0 1 (ZV 48);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 13))) 0 1 (ZV 49);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 14))) 0 1 (ZV 50);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 15))) 0 1 (ZV 51);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 16))) 0 1 (ZV 52);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 17))) 0 1 (ZV 53);
  KC (ZAdd (ZV 34) (ZAdd (ZV 33) (ZL 18))) 0 1 (ZV 54)].
Abbreviation f18 := [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false].

#[using="Type"] Lemma rd19_U : forall regs m (o buf pos sp : Z) (ds : list Z),
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 9%bv = Z_to_bv 64 buf -> getr regs 19%bv = Z_to_bv 64 pos -> getr regs 2%bv = Z_to_bv 64 (sp - 752) ->
  rd_regsU regs buf -> ptr_tblU m sp buf ->
  length ds = 19%nat -> digits_ok ds -> (forall k, (k < 19)%nat -> cellN SEGS_U m (buf + pos + Z.of_nat k) 1 (nth k ds 0)) ->
  0 <= o -> o + 516 <= 2 ^ 62 -> 1 <= buf -> buf + pos + 19 <= 2 ^ 62 -> 0 <= pos -> pos + 19 <= 780 -> 832 <= sp -> sp <= 2 ^ 62 ->
  exists regs',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35bf0) m rom) (mkst regs' (Z_to_bv 64 0x35fb4) m rom)
    /\ getr regs' 20%bv = Z_to_bv 64 (decval ds) /\ getr regs' 1%bv = Z_to_bv 64 0x35e40
    /\ getr regs' 10%bv = Z_to_bv 64 o /\ getr regs' 11%bv = Z_to_bv 64 19
    /\ keeps rd_keepU regs regs'.
Proof.
  intros regs m o buf pos sp ds R8 R9 R19 R2 (Q21 & Q22 & Q23 & Q24 & Q25) PT Hlen Hds Hcells Ho1 Ho2 Hb1 Hb2 Hp1 Hp2 Hsp1 Hsp2.
  unfold MASK in Q25.
  destruct ds as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 [|d6 [|d7 [|d8 [|d9 [|d10 [|d11 [|d12 [|d13 [|d14 [|d15 [|d16 [|d17 [|d18 [|? ?]]]]]]]]]]]]]]]]]]]];
    try (cbn in Hlen; discriminate).
  unfold digits_ok in Hds.
  repeat match type of Hds with Forall _ (_ :: _) => apply Forall_cons_iff in Hds; destruct Hds as [? Hds] end.
  destruct PT as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
  pose proof (Hcells 0%nat ltac:(lia)) as D0. pose proof (Hcells 1%nat ltac:(lia)) as D1. pose proof (Hcells 2%nat ltac:(lia)) as D2.
  pose proof (Hcells 3%nat ltac:(lia)) as D3. pose proof (Hcells 4%nat ltac:(lia)) as D4. pose proof (Hcells 5%nat ltac:(lia)) as D5.
  pose proof (Hcells 6%nat ltac:(lia)) as D6. pose proof (Hcells 7%nat ltac:(lia)) as D7. pose proof (Hcells 8%nat ltac:(lia)) as D8.
  pose proof (Hcells 9%nat ltac:(lia)) as D9. pose proof (Hcells 10%nat ltac:(lia)) as D10. pose proof (Hcells 11%nat ltac:(lia)) as D11.
  pose proof (Hcells 12%nat ltac:(lia)) as D12. pose proof (Hcells 13%nat ltac:(lia)) as D13. pose proof (Hcells 14%nat ltac:(lia)) as D14.
  pose proof (Hcells 15%nat ltac:(lia)) as D15. pose proof (Hcells 16%nat ltac:(lia)) as D16. pose proof (Hcells 17%nat ltac:(lia)) as D17.
  pose proof (Hcells 18%nat ltac:(lia)) as D18. clear Hcells. cbn [nth] in *.
  zx_run SEGS_U constr:(CTX (vi_regs ++ rdU_uvi) rdU_kn (@nil kwin)) 200%nat [0x35fb4] (SCR f18 []) constr:(rdU_pins)
    [o; buf; pos; sp; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11; d12; d13; d14; d15; d16; d17; d18]
    constr:(rdU_uvi) regs m rom 0x35bf0.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia)
    ltac:(kc1 P1; kc1 P2; kc1 P3; kc1 P4; kc1 P5; kc1 P6; kc1 P7; kc1 P8; kc1 P9; kc1 P10; kc1 P11; kc1 P12; kc1 P13; kc1 P14; kc1 P15; kc1 P16;
          kc1 D0; kc1 D1; kc1 D2; kc1 D3; kc1 D4; kc1 D5; kc1 D6; kc1 D7; kc1 D8; kc1 D9; kc1 D10; kc1 D11; kc1 D12; kc1 D13;
          kc1 D14; kc1 D15; kc1 D16; kc1 D17; kc1 D18; exact I)
    ltac:(exact I) ltac:(zx_lia).
  zx_name regs1.
  exists regs1. split; [exact ZM|].
  split; [zx_regv ZR; unfold decval; cbn [read_digits]; f_equal; lia|].
  split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
  eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
Qed.
End S.
