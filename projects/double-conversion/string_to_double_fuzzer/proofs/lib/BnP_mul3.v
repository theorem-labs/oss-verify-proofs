(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnP_mul BnP_mul2.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition CS'' : list Z := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma keeps_CS_of'' : forall regs regs', keeps CS'' regs regs' ->
  getr regs' 2%bv = getr regs 2%bv -> getr regs' 8%bv = getr regs 8%bv -> keeps CS regs regs'.
Proof.
  intros regs regs' K H2 H8 r Hr. cbn in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|Hr]]]]; [exact H2 | apply K; cbn; tauto | apply K; cbn; tauto | exact H8 |]. apply K. cbn. tauto.
Qed.

Ltac zx_pins2 := zx_pins; try (rewrite Z_to_bv_bv_unsigned; reflexivity).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

#[using="Type"] Theorem mulpow10_P : forall regs m (o e sp : Z) (ret : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0 <= e < 2048 -> bn_at SEGS_P m o b -> ok (cells b) -> norm (cells b) ->
  val (cells b) * 5 ^ e < B ^ 124 -> ex b + e / 28 < 2 ^ 15 ->
  arr32 SEGS_P m 80520 five_tbl ->
  16 <= sp -> sp <= 2 ^ 62 -> 80568 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 16 \/ sp <= o) -> 80568 <= sp - 16 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35b04) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_P m' o (mulpow10 e b)
    /\ arr32 SEGS_P m' 80520 five_tbl
    /\ unch m m' [(o, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o e sp ret b R10 R11 R2 R1 Hret He Hbn Hok Hn Hv Hex Htbl Hsp1 Hsp2 Ho1 Ho2 Hdisj Hspt Hsto Hsts.
  pose proof Hbn as Hbn0. destruct Hbn as (Cu & Ce & Carr & Hexr & H128).
  pose proof (u64_range ret) as Hrr. pose proof (u64_range (getr regs 8%bv)) as Hs0r.
  assert (TBL : forall m', unch m m' [(o, o + 516); (sp - 16, sp)] -> arr32 SEGS_P m' 80520 five_tbl).
  { intros m' U. eapply arr32_unch; [exact U | lia | cbn; lia | | exact Htbl]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia. }
  remember (zlen (cells b)) as u eqn:Eu.
  assert (Hu0 : 0 <= u <= 128) by (pose proof (zlen_nonneg (cells b)); lia).
  destruct (Z.eq_dec e 0) as [-> | He0].
  { (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 0); Some (16, 2 ^ 62); Some (0, 128); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                            [KC (ZV 32) 0 2 (ZV 35)] [KW (ZV 34) (-16) 0])
      40%nat [0x35b60; 0x35bec; 0x35cbc] (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34); (1%bv : reg, ZV 36); (8%bv : reg, ZV 37)])
      [o; 0; sp; u; bv_unsigned ret; bv_unsigned (getr regs 8%bv)]
      constr:([Some (0, 2 ^ 62); Some (0, 0); Some (16, 2 ^ 62); Some (0, 128); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs m rom 0x35b04.
    zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(zwidth; lia). zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split.
    { apply keeps_CS_of''; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | zx_reg ZR (2%bv : reg) as H; rewrite H, R2; reflexivity | zx_reg ZR (8%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned]. }
    assert (U0 : unch m (wbytes (wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned ret)))) (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (getr regs 8%bv))))) [(sp - 16, sp)]) by unchx.
    assert (U : unch m (wbytes (wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned ret)))) (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (getr regs 8%bv))))) [(o, o + 516); (sp - 16, sp)]) by unchx.
    split; [|split; [apply TBL; exact U | split; [exact U | growsx]]].
    unfold mulpow10. cbn [Z.eqb]. eapply (bn_at_unch SEGS_P _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  destruct (cells b) as [|x t] eqn:El.
  { (* [comment removed for export] *)
    cbn in Eu. subst u.
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 2047); Some (16, 2 ^ 62); Some (0, 0); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                            [KC (ZV 32) 0 2 (ZV 35)] [KW (ZV 34) (-16) 0])
      40%nat [0x35b60; 0x35bec; 0x35cbc] (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34); (1%bv : reg, ZV 36); (8%bv : reg, ZV 37)])
      [o; e; sp; 0; bv_unsigned ret; bv_unsigned (getr regs 8%bv)]
      constr:([Some (0, 2 ^ 62); Some (1, 2047); Some (16, 2 ^ 62); Some (0, 0); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs m rom 0x35b04.
    zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(zwidth; lia). zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split.
    { apply keeps_CS_of''; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | zx_reg ZR (2%bv : reg) as H; rewrite H, R2; reflexivity | zx_reg ZR (8%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned]. }
    assert (U0 : unch m (wbytes (wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned ret)))) (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (getr regs 8%bv))))) [(sp - 16, sp)]) by unchx.
    assert (U : unch m (wbytes (wbytes m (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned ret)))) (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned (getr regs 8%bv))))) [(o, o + 516); (sp - 16, sp)]) by unchx.
    split; [|split; [apply TBL; exact U | split; [exact U | growsx]]].
    unfold mulpow10. replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite El.
    eapply (bn_at_unch SEGS_P _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  (* [comment removed for export] *)
  rewrite <- El in *.
  assert (Hne : cells b <> []) by (rewrite El; congruence).
  assert (Hu1 : 1 <= u <= 124).
  { pose proof (cap_bound (cells b) e 0 Hok Hn ltac:(lia) ltac:(lia) Hv (five0_ge e ltac:(lia))) as Hc. rewrite El, zlen_cons in Hc. rewrite El, zlen_cons in Eu. pose proof (zlen_nonneg t). lia. }
  (* [comment removed for export] *)
  assert (AB : exists regs2 m2,
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35b04) m rom) (mkst regs2 (Z_to_bv 64 0x35bec) m2 rom)
    /\ (let b1 := fst (pow27_loop (Z.to_nat (e / 27)) e b) in
        let r1 := snd (pow27_loop (Z.to_nat (e / 27)) e b) in
        bn_at SEGS_P m2 o b1 /\ getr regs2 12%bv = Z_to_bv 64 (zlen (cells b1)) /\ getr regs2 7%bv = Z_to_bv 64 r1
        /\ ok (cells b1) /\ norm (cells b1) /\ cells b1 <> [] /\ ex b1 = ex b
        /\ val (cells b1) * 5 ^ r1 < B ^ 124 /\ 0 <= r1 < 27)
    /\ getr regs2 10%bv = Z_to_bv 64 o /\ getr regs2 11%bv = Z_to_bv 64 e /\ getr regs2 13%bv = Z_to_bv 64 MASK
    /\ getr regs2 2%bv = Z_to_bv 64 (sp - 16)
    /\ cellN SEGS_P m2 (sp - 8) 8 (bv_unsigned ret) /\ cellN SEGS_P m2 (sp - 16) 8 (bv_unsigned (getr regs 8%bv))
    /\ keeps CS'' regs regs2
    /\ unch m m2 [(o, o + 516); (sp - 16, sp)] /\ mem_grows m m2).
  { destruct (Z_lt_dec e 27) as [Hlt | Hge].
    - (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 26); Some (16, 2 ^ 62); Some (1, 124); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                              [KC (ZV 32) 0 2 (ZV 35)] [KW (ZV 34) (-16) 0])
        40%nat [0x35b60; 0x35bec; 0x35cbc] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34); (1%bv : reg, ZV 36); (8%bv : reg, ZV 37)])
        [o; e; sp; u; bv_unsigned ret; bv_unsigned (getr regs 8%bv)]
        constr:([Some (0, 2 ^ 62); Some (1, 26); Some (16, 2 ^ 62); Some (1, 124); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs m rom 0x35b04.
      zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(zwidth; lia). zx_name regs1.
      set (m1 := wbytes (wbytes m _ _) _ _) in ZM.
      assert (U0 : unch m m1 [(sp - 16, sp)]) by (unfold m1; unchx).
      assert (U : unch m m1 [(o, o + 516); (sp - 16, sp)]) by (unfold m1; unchx).
      eexists regs1, m1. split; [exact ZM|].
      replace (Z.to_nat (e / 27)) with 0%nat by lia. cbn [pow27_loop fst snd].
      split.
      { split; [eapply (bn_at_unch SEGS_P _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia|].
        split; [rewrite <- Eu; zx_regv ZR|]. split; [zx_regv ZR|]. repeat split; auto; lia. }
      split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [unfold m1; cellx|]. split; [unfold m1; cellx|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [exact U | unfold m1; growsx].
    - (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (27, 2047); Some (16, 2 ^ 62); Some (1, 124); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                              [KC (ZV 32) 0 2 (ZV 35)] [KW (ZV 34) (-16) 0])
        40%nat [0x35b60; 0x35bec; 0x35cbc] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34); (1%bv : reg, ZV 36); (8%bv : reg, ZV 37)])
        [o; e; sp; u; bv_unsigned ret; bv_unsigned (getr regs 8%bv)]
        constr:([Some (0, 2 ^ 62); Some (27, 2047); Some (16, 2 ^ 62); Some (1, 124); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs m rom 0x35b04.
      zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(zwidth; lia). zx_name regs1.
      set (m1 := wbytes (wbytes m _ _) _ _) in ZM.
      assert (U0 : unch m m1 [(sp - 16, sp)]) by (unfold m1; unchx).
      assert (U : unch m m1 [(o, o + 516); (sp - 16, sp)]) by (unfold m1; unchx).
      assert (Hbn1 : bn_at SEGS_P m1 o b).
      { eapply (bn_at_unch SEGS_P _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_P m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [| exact Hsto]; unfold m1; growsx).
      destruct (Z.to_nat (e / 27)) as [|f] eqn:Ef; [lia|].
      cbn [pow27_loop]. replace (e <? 27) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (loop27_P rom f regs1 m1 o e b) as (regs2 & m2 & M2 & POST & K2 & U2 & G2);
        try (rewrite <- ?Eu; zx_regv ZR).
      { lia. } { lia. } { exact Hbn1. } { exact Hok. } { exact Hn. } { exact Hne. } { exact Hv. } { lia. } { lia. } { exact Hsto1. }
      eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [exact POST|].
      split; [etransitivity; [exact (K2 10 ltac:(cbn; tauto)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 11 ltac:(cbn; tauto)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 13 ltac:(cbn; tauto)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 2 ltac:(cbn; tauto)) | zx_regv ZR]|].
      assert (U2' : unch m1 m2 [(o, o + 516); (sp - 16, sp)]).
      { eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
      split; [eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | unfold m1; cellx]|].
      split; [eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | unfold m1; cellx]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]|].
      split; [eapply unch_trans; [exact U | exact U2'] | eapply mem_grows_trans; [| exact G2]; unfold m1; growsx]. }
  clear Cu Ce Carr.
  destruct AB as (regs2 & m2 & M2 & POST2 & C10 & C11 & C13 & C2 & Cra2 & Cs02 & K2 & U2 & G2).
  unfold mulpow10. replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite El.
  destruct (pow27_loop (Z.to_nat (e / 27)) e b) as [b1 r1]. cbn [fst snd] in POST2.
  destruct POST2 as (Hbn1 & C12 & C7 & Hok1 & Hn1 & Hne1 & Hex1 & Hv1 & Hr1).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_P m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  pose proof (cap_bound (cells b1) r1 0 Hok1 Hn1 ltac:(lia) ltac:(lia) Hv1 (five0_ge r1 ltac:(lia))) as Hcap1.
  assert (Hu1' : 1 <= zlen (cells b1)) by (destruct (cells b1); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  (* [comment removed for export] *)
  assert (CD : exists regs4 m4,
    msteps SEGS_P (mkst regs2 (Z_to_bv 64 0x35bec) m2 rom) (mkst regs4 (Z_to_bv 64 0x35c88) m4 rom)
    /\ (let b2 := fst (pow13_loop 2 r1 b1) in
        let r2 := snd (pow13_loop 2 r1 b1) in
        bn_at SEGS_P m4 o b2 /\ getr regs4 12%bv = Z_to_bv 64 (zlen (cells b2)) /\ getr regs4 7%bv = Z_to_bv 64 r2
        /\ ok (cells b2) /\ norm (cells b2) /\ cells b2 <> [] /\ ex b2 = ex b
        /\ val (cells b2) * 5 ^ r2 < B ^ 124 /\ 0 <= r2 < 13)
    /\ keeps tbl_keep regs2 regs4
    /\ unch m2 m4 [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m2 m4).
  { destruct (Z_lt_dec r1 13) as [Hlt | Hge].
    - zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 12)]) (@nil kcell) (@nil kwin)) 10%nat [0x35c14; 0x35c88] (SCR [] [])
        constr:([(7%bv : reg, ZV 32)]) [r1] constr:([Some (0, 12)]) regs2 m2 rom 0x35bec.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      eexists regs3, m2. split; [exact ZM|].
      cbn [pow13_loop]. replace (r1 <? 13) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split.
      { split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]|].
        split; [zx_regv ZR|]. repeat split; auto; lia. }
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [apply unch_refl | apply mem_grows_refl].
    - zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (13, 26)]) (@nil kcell) (@nil kwin)) 10%nat [0x35c14; 0x35c88] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (7%bv : reg, ZV 33)]) [o; r1] constr:([Some (0, 2 ^ 62); Some (13, 26)]) regs2 m2 rom 0x35bec.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      cbn [pow13_loop]. replace (r1 <? 13) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (loop13_P rom 1%nat regs3 m2 o r1 b1) as (regs4 & m4 & M4 & POST & K4 & U4 & G4).
      { zx_regv ZR. }
      { etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]. }
      { zx_regv ZR. }
      { zx_regv ZR. } { zx_regv ZR. }
      { etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C13]. }
      { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { cbn. lia. } { exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1. } { lia. } { lia. } { exact Hsto2. }
      eexists regs4, m4. split; [eapply msteps_trans; [exact ZM | exact M4]|].
      split; [cbn [pow13_loop] in POST |- *; rewrite Hex1 in POST; exact POST|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity]|].
      split; [exact U4 | exact G4]. }
  destruct CD as (regs4 & m4 & M4 & POST4 & K4 & U4 & G4).
  destruct (pow13_loop 2 r1 b1) as [b2 r2]. cbn [fst snd] in POST4.
  destruct POST4 as (Hbn2 & D12 & D7 & Hok2 & Hn2 & Hne2 & Hex2 & Hv2 & Hr2).
  assert (U4' : unch m2 m4 [(o, o + 516); (sp - 16, sp)]).
  { eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (Hsto4 : RiscvSemantics.store_ok SEGS_P m4 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G4 | exact Hsto2]).
  (* [comment removed for export] *)
  destruct (tbl_P rom regs4 m4 o r2 b2) as (regs5 & m5 & M5 & POST5 & K5 & U5 & G5).
  { etransitivity; [exact (K4 10 ltac:(cbn; tauto)) | exact C10]. }
  { exact D12. } { exact D7. }
  { etransitivity; [exact (K4 13 ltac:(cbn; tauto)) | exact C13]. }
  { lia. } { exact Hbn2. } { exact Hok2. } { exact Hn2. } { exact Hne2. } { exact Hv2. }
  { apply TBL. eapply unch_trans; [exact U2 | exact U4']. }
  { lia. } { lia. } { exact Hsto4. }
  cbn zeta in POST5. destruct POST5 as (Hbn3 & E12 & Hok3 & Hn3 & Hne3 & Hex3 & Hv3).
  remember (if 0 <? r2 then mul32 (kFive r2) b2 else b2) as b3 eqn:Eb3.
  assert (U5' : unch m4 m5 [(o, o + 516); (sp - 16, sp)]).
  { eapply unch_widen; [exact U5|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (U25 : unch m2 m5 [(o, o + 516); (sp - 16, sp)]) by (eapply unch_trans; [exact U4' | exact U5']).
  assert (U25n : unch m2 m5 [(o, o + 2); (o + 4, o + 516)]) by (eapply unch_trans; [exact U4 | exact U5]).
  assert (Hsto5 : RiscvSemantics.store_ok SEGS_P m5 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G5 | exact Hsto4]).
  pose proof (cap_bound (cells b3) 0 0 Hok3 Hn3 ltac:(lia) ltac:(lia) ltac:(rewrite Z.pow_0_r, Z.mul_1_r; exact Hv3) ltac:(rewrite !Z.pow_0_r; lia)) as Hcap3.
  (* [comment removed for export] *)
  destruct (fin_P rom regs5 m5 o e sp ret (getr regs 8%bv) b3) as (regs6 & m6 & M6 & Hbn6 & F2 & F8 & K6 & U6 & G6).
  { etransitivity; [exact (K5 10 ltac:(cbn; tauto)) |]. etransitivity; [exact (K4 10 ltac:(cbn; tauto)) | exact C10]. }
  { etransitivity; [exact (K5 11 ltac:(cbn; tauto)) |]. etransitivity; [exact (K4 11 ltac:(cbn; tauto)) | exact C11]. }
  { exact E12. }
  { etransitivity; [exact (K5 13 ltac:(cbn; tauto)) |]. etransitivity; [exact (K4 13 ltac:(cbn; tauto)) | exact C13]. }
  { etransitivity; [exact (K5 2 ltac:(cbn; tauto)) |]. etransitivity; [exact (K4 2 ltac:(cbn; tauto)) | exact C2]. }
  { eapply cellN_unch; [exact U25n | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Cra2]. }
  { eapply cellN_unch; [exact U25n | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Cs02]. }
  { exact Hret. } { lia. } { exact Hbn3. } { exact Hok3. } { exact Hne3. } { lia. } { rewrite Hex3. lia. }
  { lia. } { lia. } { lia. } { lia. } { exact Hdisj. } { exact Hsto5. }
  assert (U6' : unch m5 m6 [(o, o + 516); (sp - 16, sp)]).
  { eapply unch_widen; [exact U6|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (UU : unch m m6 [(o, o + 516); (sp - 16, sp)]).
  { eapply unch_trans; [exact U2|]. eapply unch_trans; [exact U25 | exact U6']. }
  eexists regs6, m6. split; [eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M4|]; eapply msteps_trans; [exact M5 | exact M6]|].
  split.
  { apply keeps_CS_of''; [| rewrite F2, R2; reflexivity | exact F8].
    eapply keeps_trans; [exact K2|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity. }
  split; [subst b3; exact Hbn6|].
  split; [apply TBL; exact UU|].
  split; [exact UU|].
  eapply mem_grows_trans; [exact G2|]. eapply mem_grows_trans; [exact G4|]. eapply mem_grows_trans; [exact G5 | exact G6].
Qed.

End S.
