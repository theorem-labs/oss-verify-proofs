(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnContract BnCbdLib
  BnU_au64 BnU_shl BnU_cmp BnU_mul3 BnU_mul5 BnP_ads1 BnP_ads2 BnU_ads2 BnU_ads5.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition CS3 : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma keeps_CS_of3 : forall regs regs',
  keeps CS3 regs regs' -> getr regs' 2%bv = getr regs 2%bv -> getr regs' 8%bv = getr regs 8%bv ->
  getr regs' 9%bv = getr regs 9%bv -> getr regs' 18%bv = getr regs 18%bv -> keeps CS regs regs'.
Proof.
  intros regs regs' K H2 H8 H9 H18 r Hr. cbn in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]; [exact H2 | apply K; cbn; tauto | apply K; cbn; tauto | exact H8 | exact H9 | exact H18 |].
  apply K. cbn. tauto.
Qed.

(* [comment removed for export] *)
Definition cbd_pro (m : word -> option byte) (sp v1 v2 v3 v4 : Z) : word -> option byte := (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 v1))) (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 v2))) (Z_to_bv 64 (sp + -24)) (word_to_le_bytes 8 (Z_to_bv 64 v3))) (Z_to_bv 64 (sp + -32)) (word_to_le_bytes 8 (Z_to_bv 64 v4))) (Z_to_bv 64 (sp + -548)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (sp + -1064)) (word_to_le_bytes 4 (Z_to_bv 64 0))).

Lemma cbd_pro_facts : forall m sp v1 v2 v3 v4,
  1888 <= sp -> sp <= 2 ^ 62 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v3 < 2 ^ 64 -> 0 <= v4 < 2 ^ 64 ->
  let m1 := cbd_pro m sp v1 v2 v3 v4 in
  unch m m1 [(sp - 1072, sp)] /\ mem_grows m m1
  /\ cellN SEGS_U m1 (sp - 8) 8 v1 /\ cellN SEGS_U m1 (sp - 16) 8 v2 /\ cellN SEGS_U m1 (sp - 24) 8 v3 /\ cellN SEGS_U m1 (sp - 32) 8 v4
  /\ bn_at SEGS_U m1 (sp + -548) (BN [] 0) /\ bn_at SEGS_U m1 (sp + -1064) (BN [] 0).
Proof.
  intros m sp v1 v2 v3 v4 Hsp1 Hsp2 H1 H2 H3 H4. cbn zeta. unfold cbd_pro.
  split; [unchx|]. split; [growsx|].
  split; [replace (sp - 8) with (sp + -8) by lia; cellx|]. split; [replace (sp - 16) with (sp + -16) by lia; cellx|].
  split; [replace (sp - 24) with (sp + -24) by lia; cellx|]. split; [replace (sp - 32) with (sp + -32) by lia; cellx|].
  split.
  - pose proof (bn_ctor_store SEGS_U (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 v1))) (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 v2))) (Z_to_bv 64 (sp + -24)) (word_to_le_bytes 8 (Z_to_bv 64 v3))) (Z_to_bv 64 (sp + -32)) (word_to_le_bytes 8 (Z_to_bv 64 v4))) (sp + -548) ltac:(lia) ltac:(lia)) as [C0 C2].
    unfold bn_at; cbn [cells BnModel.ex]. replace (zlen (@nil Z)) with 0 by reflexivity.
    split; [apply (cellN_store_skip SEGS_U _ (sp + -548) 2%nat 0 (sp + -1064) 4%nat); [lia | zwidth; lia | lia | zwidth; lia | zwidth; lia | exact C0]|].
    split; [apply (cellN_store_skip SEGS_U _ (sp + -548 + 2) 2%nat 0 (sp + -1064) 4%nat); [lia | zwidth; lia | lia | zwidth; lia | zwidth; lia | exact C2]|].
    split; [apply arr32_nil|]. lia.
  - pose proof (bn_ctor_store SEGS_U (wbytes (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 v1))) (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 v2))) (Z_to_bv 64 (sp + -24)) (word_to_le_bytes 8 (Z_to_bv 64 v3))) (Z_to_bv 64 (sp + -32)) (word_to_le_bytes 8 (Z_to_bv 64 v4))) (Z_to_bv 64 (sp + -548)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (sp + -1064) ltac:(lia) ltac:(lia)) as [C0 C2].
    unfold bn_at; cbn [cells BnModel.ex]. replace (zlen (@nil Z)) with 0 by reflexivity. split; [exact C0|]. split; [exact C2|]. split; [apply arr32_nil|]. lia.
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Abbreviation big := (Some (0, 18446744073709551615)).

(* [comment removed for export] *)
#[using="Type"] Theorem cbd_core_U : forall regs m (sp buf len expo e a4 : Z) (ret f : word) (ds : list Z),
  getr regs 1%bv = ret -> ret_ok ret -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 10%bv = Z_to_bv 64 buf -> getr regs 11%bv = Z_to_bv 64 len -> getr regs 12%bv = Z_to_bv 64 expo ->
  getr regs 13%bv = f -> getr regs 14%bv = Z_to_bv 64 a4 -> a4 mod 2 ^ 32 = e mod 2 ^ 32 ->
  zlen ds = len -> 1 <= len <= 780 -> -323 <= len + expo <= 309 -> -2047 <= e <= 2047 ->
  digits_ok ds -> digsU m buf ds -> arr32 SEGS_U m 80520 five_tbl ->
  1 <= buf -> buf + len <= 2 ^ 62 -> 82456 <= sp -> sp <= 2 ^ 62 -> (sp <= buf \/ buf + len <= sp - 1888) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 1888)) 1888 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x3569c) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (cbd ds expo (bv_unsigned f) e)
    /\ unch m m' [(sp - 1888, sp)] /\ mem_grows m m'.
Proof.
  intros regs m sp buf len expo e a4 ret f ds R1 Hret R2 R10 R11 R12 R13 R14 E4 Hlen Hlen1 Hle He DOK DG Htbl Hb1 Hb2 Hsp1 Hsp2 Hdb Hsts.
  pose proof (u64_range ret) as Hrr. pose proof (u64_range f) as Hfr.
  pose proof (u64_range (getr regs 8%bv)) as Hs0r. pose proof (u64_range (getr regs 9%bv)) as Hs1r. pose proof (u64_range (getr regs 18%bv)) as Hs2r.
  assert (Ha4 : 0 <= a4 mod 2 ^ 64 <= 18446744073709551615) by lia.
  assert (R14' : getr regs 14%bv = Z_to_bv 64 (a4 mod 2 ^ 64)) by (rewrite R14; symmetry; rewrite <- M64_eq; apply Z2bv_mod).
  assert (He' : bv_swrap 32 (a4 mod 2 ^ 64) = e) by (apply swrap32_low; [exact E4 | lia]).
  remember (a4 mod 2 ^ 64) as w4 eqn:Ew4. clear Ew4 E4 R14.
  (* [comment removed for export] *)
  pose proof (cbd_facts ds len expo (bv_unsigned f) e DOK Hlen Hlen1 Hle ltac:(lia) He) as CF. cbn zeta in CF.
  destruct CF as ((Aok & An & Aex & Aval5) & (Bok & Bn & Bex & Bval5) & (A1ok & A1n & A1len & A1ex) & (B1ok & B1n & B1len & B1ex) & A2ok' & B2ok').
  set (a0 := assign_decimal ds) in *. set (b0 := assign_u64 (bv_unsigned f)) in *.
  (* [comment removed for export] *)
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (1, 2 ^ 62); Some (1, 780); Some (-1103, 308); big; big; big; big; big; big]) (@nil kcell) [KW (ZV 32) (-1888) 0])
    30%nat [0x35ae0] (SCR [] [])
    constr:([(2%bv : reg, ZV 32); (10%bv : reg, ZV 33); (11%bv : reg, ZV 34); (12%bv : reg, ZV 35); (14%bv : reg, ZV 36); (13%bv : reg, ZV 37);
             (1%bv : reg, ZV 38); (8%bv : reg, ZV 39); (9%bv : reg, ZV 40); (18%bv : reg, ZV 41)])
    [sp; buf; len; expo; w4; bv_unsigned f; bv_unsigned ret; bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv)]
    constr:([Some (82456, 2 ^ 62); Some (1, 2 ^ 62); Some (1, 780); Some (-1103, 308); big; big; big; big; big; big]) regs m rom 0x3569c.
  zx_use ZXB ltac:(zx_pins; first [exact R14' | rewrite Z_to_bv_bv_unsigned; first [reflexivity | symmetry; exact R13 | symmetry; exact R1]])
    ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; exact I) ltac:(exact I).
  zx_name regs1.
  change (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) _ _) _ _) _ _)
    with (cbd_pro m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))) in ZM.
  pose proof (cbd_pro_facts m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as PF. cbn zeta in PF.
  destruct PF as (U01 & G01 & V1 & V2 & V3 & V4 & HA1 & HB1).
  set (m1 := cbd_pro _ _ _ _ _ _) in *.
  assert (K1 : keeps CS3 regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  zx_reg ZR (9%bv : reg) as A9. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (18%bv : reg) as A18. zx_reg ZR (2%bv : reg) as A2.
  (* [comment removed for export] *)
  destruct (ads_U rom regs1 m1 (sp + -548) buf len (sp + -1072) (Z_to_bv 64 0x356d4) ds) as (regs2 & m2 & M2 & K2 & HA2 & Htbl2 & U2 & G2);
    try (zx_regv ZR).
  { vm_compute. reflexivity. } { exact Hlen. } { exact Hlen1. } { exact DOK. }
  { eapply digsU_unch; [exact U01 | lia | rewrite Hlen; lia | | exact DG]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; rewrite Hlen; lia. }
  { eapply arr32_unch; [exact U01 | lia | cbn; lia | | exact Htbl]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
  { eapply store_ok_grows; [exact G01|]. eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
  { eapply store_ok_grows; [exact G01|]. eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
  clear ZE ZR ZF. rename ZM into M1.
  (* [comment removed for export] *)
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); big]) (@nil kcell) (@nil kwin)) 5%nat [0x35aac] (SCR [] [])
    constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (18%bv : reg, ZV 33)]) [sp; bv_unsigned f]
    constr:([Some (82456, 2 ^ 62); big]) regs2 m2 rom 0x356d4.
  zx_use ZXB ltac:(zx_pins; first [etransitivity; [exact (K2 2 ltac:(inl)) | exact A2] | etransitivity; [exact (K2 18 ltac:(inl)) | exact A18]])
    ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I).
  zx_name regs2'.
  assert (K2' : keeps CS' regs2 regs2') by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  destruct (au64_U regs2' m2 rom (sp + -1064) (bv_unsigned f) (Z_to_bv 64 0x356e0)) as (regs3 & m3 & M3 & K3 & HB3 & U3 & G3);
    try (zx_regv ZR).
  { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_grows; [eapply mem_grows_trans; [exact G01 | exact G2]|]. eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
  fold b0 in HB3.
  assert (HA3 : bn_at SEGS_U m3 (sp + -548) a0).
  { eapply (bn_at_unch SEGS_U m2 m3); [exact U3 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact HA2]. }
  assert (Htbl3 : arr32 SEGS_U m3 80520 five_tbl).
  { eapply arr32_unch; [exact U3 | lia | cbn; lia | | exact Htbl2]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  assert (K13 : keeps CS3 regs regs3).
  { eapply keeps_trans; [exact K1|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K2'|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity. }
  assert (C9 : getr regs3 9%bv = Z_to_bv 64 expo).
  { etransitivity; [exact (K3 9 ltac:(inl))|]. etransitivity; [exact (K2' 9 ltac:(inl))|]. etransitivity; [exact (K2 9 ltac:(inl)) | exact A9]. }
  assert (C8 : getr regs3 8%bv = Z_to_bv 64 w4).
  { etransitivity; [exact (K3 8 ltac:(inl))|]. etransitivity; [exact (K2' 8 ltac:(inl))|]. etransitivity; [exact (K2 8 ltac:(inl)) | exact A8]. }
  assert (C2 : getr regs3 2%bv = Z_to_bv 64 (sp + -1072)).
  { etransitivity; [exact (K3 2 ltac:(inl))|]. zx_regv ZR. }
  assert (U13 : unch m1 m3 [(sp - 1888, sp - 32)]).
  { apply (unch_trans m1 m2 m3).
    - eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity | cbn; lia]).
    - eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity | cbn; lia]). }
  assert (G13 : mem_grows m1 m3) by (eapply mem_grows_trans; [exact G2 | exact G3]).
  assert (M03 : msteps SEGS_U (mkst regs (Z_to_bv 64 0x3569c) m rom) (mkst regs3 (Z_to_bv 64 0x356e0) m3 rom)).
  { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact ZM | exact M3]. }
  clear ZE ZR ZF ZM M1 M2 M3 K1 K2 K2' K3 A9 A8 A18 A2 HA1 HB1 HA2 Htbl2 U2 G2 U3 G3 Htbl.
  assert (Hsto3 : forall o n, sp - 1888 <= o -> o + Z.of_nat n <= sp -> RiscvSemantics.store_ok SEGS_U m3 (Z_to_bv 64 o) n = true).
  { intros o n Ho1 Ho2. eapply store_ok_grows; [eapply mem_grows_trans; [exact G01 | exact G13]|]. eapply sc_store_in; [exact Hsts|]. lia. }
  (* [comment removed for export] *)
  set (a1 := if 0 <=? expo then mulpow10 expo a0 else a0) in *.
  set (b1 := if 0 <=? expo then b0 else mulpow10 (- expo) b0) in *.
  assert (PH3 : exists regs5 m5 p5,
    (p5 = 0x356f4 \/ p5 = 0x3571c)
    /\ msteps SEGS_U (mkst regs3 (Z_to_bv 64 0x356e0) m3 rom) (mkst regs5 (Z_to_bv 64 p5) m5 rom)
    /\ bn_at SEGS_U m5 (sp + -548) a1 /\ bn_at SEGS_U m5 (sp + -1064) b1
    /\ getr regs5 11%bv = Z_to_bv 64 e /\ getr regs5 2%bv = Z_to_bv 64 (sp + -1072)
    /\ keeps CS3 regs3 regs5
    /\ unch m3 m5 [(sp - 1888, sp - 32)] /\ mem_grows m3 m5).
  { destruct (Z.leb_spec 0 expo) as [Hx|Hx]; subst a1 b1.
    - (* [comment removed for export] *)
      zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (0, 308)]) (@nil kcell) (@nil kwin)) 10%nat [0x35fb4] (SCR [] [])
        constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (9%bv : reg, ZV 33)]) [sp; expo] constr:([Some (82456, 2 ^ 62); Some (0, 308)]) regs3 m3 rom 0x356e0.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
      assert (K4 : keeps CS' regs3 regs4) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      destruct (mulpow10_U rom regs4 m3 (sp + -548) expo (sp + -1072) (Z_to_bv 64 0x356f0) a0) as (regs5 & m5 & M5 & K5 & HA5 & Htbl5 & U5 & G5);
        try (zx_regv ZR).
      { vm_compute. reflexivity. } { lia. } { exact HA3. } { exact Aok. } { exact An. } { exact (Aval5 Hx). } { rewrite Aex. cbn. lia. }
      { exact Htbl3. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { apply Hsto3; lia. } { apply Hsto3; zwidth; lia. }
      (* [comment removed for export] *)
      rename ZE into ZE1. rename ZR into ZR1. rename ZF into ZF1. rename ZM into ZM1.
      zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); big]) (@nil kcell) (@nil kwin)) 3%nat [0x356f4] (SCR [] [])
        constr:([(8%bv : reg, ZV 33)]) [sp; w4] constr:([Some (82456, 2 ^ 62); big]) regs5 m5 rom 0x356f0.
      zx_use ZXB ltac:(zx_pins; etransitivity; [exact (K5 8 ltac:(inl))|]; etransitivity; [exact (K4 8 ltac:(inl)) | exact C8]) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I).
      zx_name regs6.
      eexists regs6, m5, 0x356f4. split; [left; reflexivity|].
      split; [eapply msteps_trans; [exact ZM1|]; eapply msteps_trans; [exact M5 | exact ZM]|].
      split; [exact HA5|].
      split; [eapply (bn_at_unch SEGS_U m3 m5); [exact U5 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact HB3]|].
      split; [zx_reg ZR (11%bv : reg) as H; rewrite H; f_equal; exact He'|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity))|]; etransitivity; [exact (K5 2 ltac:(inl))|]; zx_regv ZR1|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|];
              eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [|exact G5].
      eapply unch_widen; [exact U5|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity | cbn; lia]).
    - (* [comment removed for export] *)
      zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (-1103, -1)]) (@nil kcell) (@nil kwin)) 10%nat [0x35fb4] (SCR [] [])
        constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (9%bv : reg, ZV 33)]) [sp; expo] constr:([Some (82456, 2 ^ 62); Some (-1103, -1)]) regs3 m3 rom 0x356e0.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
      assert (K4 : keeps CS' regs3 regs4) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      destruct (mulpow10_U rom regs4 m3 (sp + -1064) (- expo) (sp + -1072) (Z_to_bv 64 0x35718) b0) as (regs5 & m5 & M5 & K5 & HB5 & Htbl5 & U5 & G5);
        try (zx_regv ZR).
      { vm_compute. reflexivity. } { lia. } { exact HB3. } { exact Bok. } { exact Bn. } { exact (Bval5 Hx). } { rewrite Bex. cbn. lia. }
      { exact Htbl3. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { apply Hsto3; lia. } { apply Hsto3; zwidth; lia. }
      rename ZE into ZE1. rename ZR into ZR1. rename ZF into ZF1. rename ZM into ZM1.
      zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); big]) (@nil kcell) (@nil kwin)) 3%nat [0x3571c] (SCR [] [])
        constr:([(8%bv : reg, ZV 33)]) [sp; w4] constr:([Some (82456, 2 ^ 62); big]) regs5 m5 rom 0x35718.
      zx_use ZXB ltac:(zx_pins; etransitivity; [exact (K5 8 ltac:(inl))|]; etransitivity; [exact (K4 8 ltac:(inl)) | exact C8]) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I).
      zx_name regs6.
      eexists regs6, m5, 0x3571c. split; [right; reflexivity|].
      split; [eapply msteps_trans; [exact ZM1|]; eapply msteps_trans; [exact M5 | exact ZM]|].
      split; [eapply (bn_at_unch SEGS_U m3 m5); [exact U5 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact HA3]|].
      split; [exact HB5|].
      split; [zx_reg ZR (11%bv : reg) as H; rewrite H; f_equal; exact He'|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity))|]; etransitivity; [exact (K5 2 ltac:(inl))|]; zx_regv ZR1|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|];
              eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [|exact G5].
      eapply unch_widen; [exact U5|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity | cbn; lia]). }
  destruct PH3 as (regs5 & m5 & p5 & Hp5 & M35 & HA5 & HB5 & D11 & D2 & K35 & U35 & G35).
  assert (Hsto5 : forall o n, sp - 1888 <= o -> o + Z.of_nat n <= sp -> RiscvSemantics.store_ok SEGS_U m5 (Z_to_bv 64 o) n = true).
  { intros o n Ho1 Ho2. eapply store_ok_grows; [exact G35|]. apply Hsto3; lia. }
  (* [comment removed for export] *)
  set (b2 := if 0 <? e then shl e b1 else b1).
  set (a2 := if 0 <? e then a1 else shl (- e) a1).
  assert (PH4 : exists regs7 m7,
    msteps SEGS_U (mkst regs5 (Z_to_bv 64 p5) m5 rom) (mkst regs7 (Z_to_bv 64 0x35738) m7 rom)
    /\ bn_at SEGS_U m7 (sp + -548) a2 /\ bn_at SEGS_U m7 (sp + -1064) b2 /\ ok (cells a2) /\ ok (cells b2)
    /\ getr regs7 2%bv = Z_to_bv 64 (sp + -1072) /\ keeps CS3 regs5 regs7
    /\ unch m5 m7 [(sp - 1888, sp - 32)] /\ mem_grows m5 m7).
  { (* [comment removed for export] *)
    assert (BR : exists regs6,
      msteps SEGS_U (mkst regs5 (Z_to_bv 64 p5) m5 rom) (mkst regs6 (Z_to_bv 64 0x366f0) m5 rom)
      /\ getr regs6 10%bv = Z_to_bv 64 (if 0 <? e then sp + -1064 else sp + -548)
      /\ getr regs6 11%bv = Z_to_bv 64 (if 0 <? e then e else - e)
      /\ getr regs6 2%bv = Z_to_bv 64 (sp + -1072) /\ getr regs6 1%bv = Z_to_bv 64 0x35738
      /\ keeps CS' regs5 regs6).
    { destruct (Z.ltb_spec 0 e) as [Hx|Hx]; destruct Hp5 as [-> | ->].
      - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (1, 2047)]) (@nil kcell) (@nil kwin)) 20%nat [0x366f0] (SCR [] [])
          constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (11%bv : reg, ZV 33)]) [sp; e] constr:([Some (82456, 2 ^ 62); Some (1, 2047)]) regs5 m5 rom 0x356f4.
        zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs6.
        exists regs6. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
      - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (1, 2047)]) (@nil kcell) (@nil kwin)) 20%nat [0x366f0] (SCR [] [])
          constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (11%bv : reg, ZV 33)]) [sp; e] constr:([Some (82456, 2 ^ 62); Some (1, 2047)]) regs5 m5 rom 0x3571c.
        zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs6.
        exists regs6. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
      - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (-2047, 0)]) (@nil kcell) (@nil kwin)) 20%nat [0x366f0] (SCR [] [])
          constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (11%bv : reg, ZV 33)]) [sp; e] constr:([Some (82456, 2 ^ 62); Some (-2047, 0)]) regs5 m5 rom 0x356f4.
        zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs6.
        exists regs6. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
      - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (-2047, 0)]) (@nil kcell) (@nil kwin)) 20%nat [0x366f0] (SCR [] [])
          constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (11%bv : reg, ZV 33)]) [sp; e] constr:([Some (82456, 2 ^ 62); Some (-2047, 0)]) regs5 m5 rom 0x3571c.
        zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs6.
        exists regs6. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
    destruct BR as (regs6 & M6 & F10 & F11 & F2 & F1 & K6).
    subst a2 b2. destruct (Z.ltb_spec 0 e) as [Hx|Hx].
    - destruct (shl_U rom regs6 m5 (sp + -1064) e (sp + -1072) (Z_to_bv 64 0x35738) b1 F10 F11 F2 F1 ltac:(vm_compute; reflexivity) ltac:(lia) HB5 B1ok ltac:(lia))
        as (regs7 & m7 & M7 & K7 & HB7 & U7 & G7).
      { pose proof (Z.div_le_upper_bound e 28 73). lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { apply Hsto5; lia. } { apply Hsto5; zwidth; lia. }
      eexists regs7, m7. split; [eapply msteps_trans; [exact M6 | exact M7]|].
      split; [eapply (bn_at_unch SEGS_U m5 m7); [exact U7 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact HA5]|].
      split; [exact HB7|]. split; [exact A1ok|]. split; [exact B2ok'|].
      split; [etransitivity; [exact (K7 2 ltac:(inl)) | exact F2]|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K7|]; vm_compute; reflexivity]|].
      split; [|exact G7].
      eapply unch_widen; [exact U7|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity | cbn; lia]).
    - destruct (shl_U rom regs6 m5 (sp + -548) (- e) (sp + -1072) (Z_to_bv 64 0x35738) a1 F10 F11 F2 F1 ltac:(vm_compute; reflexivity) ltac:(lia) HA5 A1ok ltac:(lia))
        as (regs7 & m7 & M7 & K7 & HA7 & U7 & G7).
      { pose proof (Z.div_le_upper_bound (- e) 28 73). lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { apply Hsto5; lia. } { apply Hsto5; zwidth; lia. }
      eexists regs7, m7. split; [eapply msteps_trans; [exact M6 | exact M7]|].
      split; [exact HA7|].
      split; [eapply (bn_at_unch SEGS_U m5 m7); [exact U7 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact HB5]|].
      split; [exact A2ok'|]. split; [exact B1ok|].
      split; [etransitivity; [exact (K7 2 ltac:(inl)) | exact F2]|].
      split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K7|]; vm_compute; reflexivity]|].
      split; [|exact G7].
      eapply unch_widen; [exact U7|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity | cbn; lia]). }
  destruct PH4 as (regs7 & m7 & M57 & HA7 & HB7 & A2ok & B2ok & F2 & K57 & U57 & G57).
  (* [comment removed for export] *)
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62)]) (@nil kcell) (@nil kwin)) 5%nat [0x367d8] (SCR [] [])
    constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072)))]) [sp] constr:([Some (82456, 2 ^ 62)]) regs7 m7 rom 0x35738.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs8.
  assert (K8 : keeps CS' regs7 regs8) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  destruct (cmp_U rom regs8 m7 (sp + -548) (sp + -1064) (sp + -1072) (Z_to_bv 64 0x35744) a2 b2) as (regs9 & m9 & M9 & K9 & R9 & U9 & G9);
    try (zx_regv ZR).
  { vm_compute. reflexivity. } { exact HA7. } { exact HB7. } { exact A2ok. } { exact B2ok. }
  { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
  { eapply store_ok_grows; [exact G57|]. apply Hsto5; zwidth; lia. }
  (* [comment removed for export] *)
  assert (U19 : unch m1 m9 [(sp - 1888, sp - 32)]).
  { eapply unch_trans; [exact U13|]. eapply unch_trans; [exact U35|]. eapply unch_trans; [exact U57|].
    eapply unch_widen; [exact U9|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity | cbn; lia]). }
  assert (SV9 : cellN SEGS_U m9 (sp - 8) 8 (bv_unsigned ret) /\ cellN SEGS_U m9 (sp - 16) 8 (bv_unsigned (getr regs 8%bv))
               /\ cellN SEGS_U m9 (sp - 24) 8 (bv_unsigned (getr regs 9%bv)) /\ cellN SEGS_U m9 (sp - 32) 8 (bv_unsigned (getr regs 18%bv))).
  { repeat split; (eapply cellN_unch; [exact U19 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | assumption]). }
  clear V1 V2 V3 V4.
  destruct SV9 as (V1 & V2 & V3 & V4).
  rename ZE into ZE8. rename ZR into ZR8. rename ZF into ZF8. rename ZM into ZM8.
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); big; big; big; big; None])
                          [KC (ZV 32) (-8) 8 (ZV 33); KC (ZV 32) (-16) 8 (ZV 34); KC (ZV 32) (-24) 8 (ZV 35); KC (ZV 32) (-32) 8 (ZV 36)] (@nil kwin))
    10%nat (@nil Z) (SCR [] [])
    constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (10%bv : reg, ZV 37)])
    [sp; bv_unsigned ret; bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv); compare a2 b2]
    constr:([Some (82456, 2 ^ 62); big; big; big; big; @None (Z * Z)]) regs9 m9 rom 0x35744.
  zx_use ZXB ltac:(zx_pins; etransitivity; [exact (K9 2 ltac:(inl)) | zx_regv ZR8]) ltac:(zx_lia) ltac:(kc1 V1; kc1 V2; kc1 V3; kc1 V4; exact I) ltac:(exact I) ltac:(exact I).
  zx_name regs10.
  assert (R1' : getr regs10 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
  eexists regs10, m9. split.
  { eapply msteps_trans; [exact M03|]. eapply msteps_trans; [exact M35|]. eapply msteps_trans; [exact M57|].
    eapply msteps_trans; [exact ZM8|]. eapply msteps_trans; [exact M9|]. eapply msteps_trans; [exact ZM|]. zx_ret SEGS_U; [exact R1' | exact Hret]. }
  split.
  { apply keeps_CS_of3.
    - eapply keeps_trans; [exact K13|]. eapply keeps_trans; [exact K35|]. eapply keeps_trans; [exact K57|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K8|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K9|]; vm_compute; reflexivity|]. eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
    - zx_reg ZR (2%bv : reg) as H; rewrite H, R2; f_equal; lia.
    - zx_reg ZR (8%bv : reg) as H; rewrite H. apply Z_to_bv_bv_unsigned.
    - zx_reg ZR (9%bv : reg) as H; rewrite H. apply Z_to_bv_bv_unsigned.
    - zx_reg ZR (18%bv : reg) as H; rewrite H. apply Z_to_bv_bv_unsigned. }
  split.
  { zx_reg ZR (10%bv : reg) as H; rewrite H. subst a2 b2 a1 b1 a0 b0. reflexivity. }
  split.
  - eapply unch_trans; [eapply unch_widen; [exact U01|]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity | cbn; lia])|].
    eapply unch_widen; [exact U19|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity | cbn; lia]).
  - eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G13|]. eapply mem_grows_trans; [exact G35|]. eapply mem_grows_trans; [exact G57 | exact G9].
Qed.


End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem cbd_U : cbd_stmt_U.
Proof.
  unfold cbd_stmt_U, cbd_stmt, CBD_ENTRY_U, CBD_FR_U, CBD_TBL_LO, CBD_TBL_HI.
  intros fx regs mem rom sp buf len expo e a4 ret f R1 Hra R2 Hsp16 Hfr Hsp62 R10 Hb0 Hbl R11 R12 R13 R14 He4 Hlen Hle He Hdig Hsto Hdb Htb Hro.
  pose proof (dsof_spec SEGS_U mem buf len ltac:(lia) Hdig) as DS. cbn zeta in DS. destruct DS as (Dlen & Dok & Dcells).
  set (ds := dsof SEGS_U mem buf (Z.to_nat len)) in *.
  assert (Htbl : arr32 SEGS_U mem 80520 five_tbl).
  { unfold five_tbl. apply arr32_rom; [lia | cbn; lia | | exact five_tbl_U0].
    intros x b Hx Hm. apply (Hro x b); [cbn [length] in Hx; lia | exact Hm]. }
  destruct (@cbd_core_U fx rom regs mem sp buf len expo e a4 ret f ds R1 ltac:(apply ret_ok_even; lia) R2 R10 R11 R12 R13 R14 He4
              Dlen Hlen Hle He Dok Dcells Htbl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsto)
    as (regs' & m' & M & K & R & U & G).
  exists regs', m'. split; [exact M|].
  split; [exact K|].
  split; [eexists; split; [exact R | apply compare_range]|].
  split.
  - intros a Ha. apply U. intros (r & Hr & Hin). cbn in Hr. destruct Hr as [<-|[]]. cbn in Hin. lia.
  - intros a b Hm. destruct (m' a) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (G a); [congruence | exact E].
Qed.
