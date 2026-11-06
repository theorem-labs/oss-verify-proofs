(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnU_mul3 BnU_mul5 BnP_ads1 BnP_ads2 BnP_ads3 BnU_ads1 BnU_ads2 BnU_ads3.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Hypothesis ADD : add_U_spec rom.

#[using="ADD"] Lemma tail_U : forall regs m (o buf sp : Z) (done rest : list Z) (b : bn) (RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word),
  let pos := zlen done in let lr := zlen rest in
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 9%bv = Z_to_bv 64 buf -> getr regs 19%bv = Z_to_bv 64 pos ->
  getr regs 11%bv = Z_to_bv 64 lr -> getr regs 2%bv = Z_to_bv 64 (sp - 752) ->
  digsU m buf (done ++ rest) -> digits_ok (done ++ rest) -> lr < 19 -> pos + lr <= 780 ->
  bn_at SEGS_U m o b -> ok (cells b) -> norm (cells b) -> ex b = 0 -> 0 <= val (cells b) < 10 ^ pos ->
  arr32 SEGS_U m 80520 five_tbl ->
  sv13U m sp RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 -> ret_ok RA ->
  1 <= buf -> buf + zlen (done ++ rest) <= 2 ^ 62 -> 81384 <= sp -> sp <= 2 ^ 62 -> 80568 <= o -> o + 516 <= 2 ^ 62 ->
  (o + 516 <= sp - 816 \/ sp <= o) -> (buf + zlen (done ++ rest) <= sp - 816 \/ sp <= buf) -> (buf + zlen (done ++ rest) <= o \/ o + 516 <= buf) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 816)) 816 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35e7c) m rom) (mkst regs' RA m' rom)
    /\ bn_at SEGS_U m' o (clamp (ads_step rest b)) /\ getr regs' 2%bv = Z_to_bv 64 sp
    /\ s12_rest regs' S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 /\ keeps [3; 4] regs regs'
    /\ arr32 SEGS_U m' 80520 five_tbl
    /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m'.
Proof.
  intros regs m o buf sp done rest b RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 pos lr R8 R9 R19 R11 R2 DG DOK Hlr Hpl
    Hbn Hok Hn Hex Hval Htbl W Hret Hb1 Hb2 Hsp1 Hsp2 Ho1 Ho2 Hdo Hdb Hbo Hsto Hsts.
  assert (Epos : pos = Z.of_nat (length done)) by reflexivity. assert (Elr : lr = Z.of_nat (length rest)) by reflexivity.
  clearbody pos lr. assert (Hpos0 : 0 <= pos) by lia. assert (Hlr0 : 0 <= lr) by lia.
  rewrite zlen_app in Hb2, Hdb, Hbo. unfold zlen in Hb2, Hdb, Hbo. rewrite <- Epos, <- Elr in Hb2, Hdb, Hbo.
  destruct (digits_ok_app_inv _ _ DOK) as [DOKd DOKr].
  pose proof (decval_bound rest DOKr) as Hdv. replace (zlen rest) with lr in Hdv by (unfold zlen; lia).
  assert (Hlr10 : 10 ^ lr <= 10 ^ 18) by (apply Z.pow_le_mono_r; lia).
  (* [comment removed for export] *)
  pose proof (mulpow10_spec lr b Hok Hn Hlr0) as SPM. cbn zeta in SPM. destruct SPM as (Hok2 & Hn2 & Hv2 & Hex2 & Hnil2).
  assert (Hex2' : ex (mulpow10 lr b) = 0).
  { destruct (cells b) eqn:Ec.
    - unfold mulpow10. destruct (lr =? 0); rewrite ?Ec; exact Hex.
    - rewrite Hex2 by congruence. rewrite Hex, Z.div_small by lia. reflexivity. }
  assert (Hv2b : 0 <= val (cells (mulpow10 lr b)) < B ^ 124).
  { split; [apply val_nonneg; exact Hok2|]. rewrite Hv2.
    assert (H1 : 5 ^ lr * 2 ^ (lr mod 28) * val (cells b) <= 10 ^ lr * val (cells b)).
    { rewrite Z.mod_small by lia. replace (10 ^ lr) with (5 ^ lr * 2 ^ lr) by (rewrite <- Z.pow_mul_l; reflexivity). lia. }
    eapply Z.le_lt_trans; [exact H1|].
    assert (H2 : 10 ^ lr * val (cells b) < 10 ^ lr * 10 ^ pos) by (apply Z.mul_lt_mono_pos_l; [apply Z.pow_pos_nonneg|]; lia).
    eapply Z.lt_trans; [exact H2|]. rewrite <- Z.pow_add_r by lia. eapply Z.le_lt_trans; [|exact pow10_780]. apply Z.pow_le_mono_r; lia. }
  assert (Hlen2 : zlen (cells (mulpow10 lr b)) <= 124) by (apply len_bound; auto; lia).
  (* [comment removed for export] *)
  assert (CF : forall p regs5 m5 (b5 : bn),
    (p = 0x35f0c \/ p = 0x35f64) ->
    getr regs5 8%bv = Z_to_bv 64 o -> getr regs5 2%bv = Z_to_bv 64 (sp - 752) ->
    bn_at SEGS_U m5 o b5 -> ok (cells b5) -> norm (cells b5) -> ex b5 = 0 ->
    unch m m5 [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] -> mem_grows m m5 -> keeps [3; 4] regs regs5 ->
    arr32 SEGS_U m5 80520 five_tbl ->
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35e7c) m rom) (mkst regs5 (Z_to_bv 64 p) m5 rom) ->
    exists regs' m',
      msteps SEGS_U (mkst regs (Z_to_bv 64 0x35e7c) m rom) (mkst regs' RA m' rom)
      /\ bn_at SEGS_U m' o (clamp b5) /\ getr regs' 2%bv = Z_to_bv 64 sp
      /\ s12_rest regs' S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 /\ keeps [3; 4] regs regs'
      /\ arr32 SEGS_U m' 80520 five_tbl
      /\ unch m m' [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)] /\ mem_grows m m').
  { intros p regs5 m5 b5 Hp Q8 Q2 Hbn5 Hok5 Hn5 Hex5 U5 G5 K5 T5 M5.
    destruct b5 as [l5 e5]. cbn [cells BnModel.ex] in *. subst e5.
    destruct (clampfin_U rom p regs5 m5 o sp l5 0 RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 Hp Q8 Q2 Hbn5 Hok5 Hn5)
      as (regs6 & m6 & M6 & Hbn6 & E2 & SR & K6 & U6 & G6).
    { eapply (sv13U_unch m m5); [exact U5 | lia | lia | | exact W]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]]; cbn; lia. }
    { exact Hret. } { lia. } { lia. } { lia. } { lia. } { exact Hdo. } { eapply store_ok_grows; [exact G5 | exact Hsto]. }
    eexists regs6, m6. split; [eapply msteps_trans; [exact M5 | exact M6]|].
    split; [exact Hbn6|]. split; [exact E2|]. split; [exact SR|]. split; [eapply keeps_trans; [exact K5 | exact K6]|].
    split; [eapply arr32_unch; [exact U6 | lia | cbn; lia | | exact T5]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia|].
    split; [|eapply mem_grows_trans; [exact G5 | exact G6]].
    eapply unch_trans; [exact U5|]. eapply unch_widen; [exact U6|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity | cbn; lia]. }
  destruct (Z.eq_dec lr 0) as [Hlr0' | Hlr1].
  - (* [comment removed for export] *)
    rewrite Hlr0' in *.
    assert (Erest : rest = []) by (destruct rest; [reflexivity | cbn in Elr; lia]).
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 780); Some (1, 2 ^ 62)]) (@nil kcell) (@nil kwin)) 15%nat [0x35ea4; 0x35fb4] (SCR [true] [])
      constr:([(8%bv : reg, ZV 32); (11%bv : reg, ZL 0); (19%bv : reg, ZV 33); (9%bv : reg, ZV 34)]) [o; pos; buf] constr:([Some (0, 2 ^ 62); Some (0, 780); Some (1, 2 ^ 62)]) regs m rom 0x35e7c.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs1.
    assert (A2 : getr regs1 2%bv = Z_to_bv 64 (sp - 752)) by (etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R2]).
    destruct (mulpow10_U rom regs1 m o 0 (sp - 752) (Z_to_bv 64 0x35f64) b ltac:(zx_regv ZR) ltac:(zx_regv ZR) A2 ltac:(zx_regv ZR)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hbn Hok Hn) as (regs2 & m2 & M2 & K2 & Hbn2 & Htbl2 & U2 & G2).
    { rewrite Z.pow_0_r, Z.mul_1_r. eapply Z.lt_trans; [apply (proj2 Hval)|]. eapply Z.le_lt_trans; [|exact pow10_780]. apply Z.pow_le_mono_r; lia. }
    { rewrite Hex. cbn. lia. }
    { exact Htbl. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Hsto. }
    { eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
    assert (U2' : unch m m2 [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)]).
    { eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [right; left; reflexivity|cbn; lia]]. }
    replace (ads_step rest b) with (mulpow10 0 b).
    2:{ subst rest. unfold ads_step. cbn [read_digits zlen length Z.of_nat]. unfold add_u64. reflexivity. }
    eapply (CF 0x35f64 regs2 m2 (mulpow10 0 b)); [right; reflexivity | | | exact Hbn2 | exact Hok2 | exact Hn2 | exact Hex2' | exact U2' | exact G2 | | exact Htbl2 |].
    { etransitivity; [exact (K2 8 ltac:(inl)) | zx_regv ZR]. }
    { etransitivity; [exact (K2 2 ltac:(inl)) | exact A2]. }
    { eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]. }
    eapply msteps_trans; [exact ZM | exact M2].
  - (* [comment removed for export] *)
    assert (Hne : rest <> []) by (destruct rest; [cbn in Elr; lia | congruence]).
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 780); Some (1, 18); Some (1, 2 ^ 62)]) (@nil kcell) (@nil kwin)) 15%nat [0x35ea4; 0x35f5c] (SCR [false] [])
      constr:([(19%bv : reg, ZV 32); (11%bv : reg, ZV 33); (9%bv : reg, ZV 34)]) [pos; lr; buf] constr:([Some (0, 780); Some (1, 18); Some (1, 2 ^ 62)]) regs m rom 0x35e7c.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs1.
    assert (K1 : keeps [2; 3; 4; 8; 9; 11] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    destruct (rdtail_loop_U rom rest regs1 m buf pos 0 (pos + lr)) as (regs2 & M2 & C18 & C19 & K2).
    { zx_regv ZR. }
    { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
    { unfold zlen; lia. } { exact Hne. } { exact DOKr. }
    { intros k Hk. specialize (DG (length done + k)%nat ltac:(rewrite length_app; lia)).
      rewrite app_nth2 in DG by lia. replace (length done + k - length done)%nat with k in DG by lia.
      eapply cellN_eqa; [exact DG | lia | reflexivity]. }
    { lia. } { replace (zlen rest) with lr by (unfold zlen; lia). lia. } { lia. } { lia. } { lia. } { lia. }
    clear ZE ZR ZF. rename ZM into M1.
    (* [comment removed for export] *)
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62)]) (@nil kcell) (@nil kwin)) 5%nat [0x35fb4] (SCR [] [])
      constr:([(8%bv : reg, ZV 32)]) [o] constr:([Some (0, 2 ^ 62)]) regs2 m rom 0x35ec4.
    zx_use ZXB ltac:(zx_pins; etransitivity; [exact (K2 8 ltac:(inl)) |]; etransitivity; [exact (K1 8 ltac:(inl)) | exact R8]) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I).
    zx_name regs3.
    assert (B2 : getr regs3 2%bv = Z_to_bv 64 (sp - 752)).
    { etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) |].
      etransitivity; [exact (K2 2 ltac:(inl)) |]. etransitivity; [exact (K1 2 ltac:(inl)) | exact R2]. }
    assert (B11 : getr regs3 11%bv = Z_to_bv 64 lr).
    { etransitivity; [exact (reg_kept _ _ _ _ (11%bv : reg) ZR ltac:(vm_compute; reflexivity)) |].
      etransitivity; [exact (K2 11 ltac:(inl)) |]. etransitivity; [exact (K1 11 ltac:(inl)) | exact R11]. }
    assert (B18 : getr regs3 18%bv = Z_to_bv 64 (decval rest)).
    { etransitivity; [exact (reg_kept _ _ _ _ (18%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C18]. }
    destruct (mulpow10_U rom regs3 m o lr (sp - 752) (Z_to_bv 64 0x35ecc) b ltac:(zx_regv ZR) B11 B2 ltac:(zx_regv ZR)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hbn Hok Hn) as (regs4 & m4 & M4 & K4 & Hbn4 & Htbl4 & U4 & G4).
    { apply (val_bound_mul _ pos lr); lia. }
    { rewrite Hex, Z.div_small by lia. cbn. lia. }
    { exact Htbl. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Hsto. }
    { eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
    assert (U4' : unch m m4 [(o, o + 516); (sp - 816, sp - 752); (sp - 620, sp - 104)]).
    { eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [right; left; reflexivity|cbn; lia]]. }
    assert (K14 : keeps [2; 3; 4; 8] regs regs4).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
    assert (D18 : getr regs4 18%bv = Z_to_bv 64 (decval rest)) by (etransitivity; [exact (K4 18 ltac:(inl)) | exact B18]).
    assert (D8 : getr regs4 8%bv = Z_to_bv 64 o) by (etransitivity; [exact (K14 8 ltac:(inl)) | exact R8]).
    assert (D2 : getr regs4 2%bv = Z_to_bv 64 (sp - 752)) by (etransitivity; [exact (K14 2 ltac:(inl)) | exact R2]).
    assert (M14 : msteps SEGS_U (mkst regs (Z_to_bv 64 0x35e7c) m rom) (mkst regs4 (Z_to_bv 64 0x35ecc) m4 rom)).
    { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact ZM | exact M4]. }
    clear ZE ZR ZF ZM.
    remember (mulpow10 lr b) as b1 eqn:Eb1. destruct b1 as [l1 e1]. cbn [cells BnModel.ex] in *. subst e1.
    replace (ads_step rest b) with (add_u64 (decval rest) (BN l1 0)).
    2:{ unfold ads_step. replace (zlen rest) with lr by (unfold zlen; lia). rewrite <- Eb1. reflexivity. }
    unfold add_u64. destruct (Z.eqb_spec (decval rest) 0) as [Hd0|Hd0].
    + (* [comment removed for export] *)
      zx_run SEGS_U constr:(CTX vi_regs (@nil kcell) (@nil kwin)) 10%nat [0x35f0c; 0x35ed0] (SCR [] []) constr:([(18%bv : reg, ZL 0)])
        (@nil Z) constr:(@nil (option (Z * Z))) regs4 m4 rom 0x35ecc.
      zx_use ZXB ltac:(zx_pins; rewrite D18, Hd0; reflexivity) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
      eapply (CF 0x35f0c regs5 m4 (BN l1 0)); [left; reflexivity | | | exact Hbn4 | exact Hok2 | exact Hn2 | reflexivity | exact U4' | exact G4 | | exact Htbl4 |].
      { etransitivity; [exact (reg_kept _ _ _ _ (8%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact D8]. }
      { etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact D2]. }
      { eapply keeps_trans; [eapply keeps_sub_dec; [exact K14|]; vm_compute; reflexivity | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]. }
      eapply msteps_trans; [exact M14 | exact ZM].
    + (* [comment removed for export] *)
      zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (1, 2 ^ 64 - 1)]) (@nil kcell) (@nil kwin)) 10%nat [0x35f0c; 0x35ed0] (SCR [] []) constr:([(18%bv : reg, ZV 32)])
        [decval rest] constr:([Some (1, 2 ^ 64 - 1)]) regs4 m4 rom 0x35ecc.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs4'.
      assert (K4' : keeps CS18 regs4 regs4') by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      destruct (au64add_U2 rom ADD regs4' m4 o sp (decval rest) l1) as (regs5 & m5 & M5 & Hbn5 & K5 & U5 & G5); try lia.
      { etransitivity; [exact (K4' 8 ltac:(inl)) | exact D8]. } { etransitivity; [exact (K4' 2 ltac:(inl)) | exact D2]. } { zx_regv ZR. }
      { exact Hbn4. } { exact Hok2. }
      { eapply store_ok_grows; [exact G4 | exact Hsto]. } { eapply store_ok_grows; [exact G4 | exact Hsts]. }
      pose proof (add_u64_spec (decval rest) (BN l1 0) Hok2 Hn2 ltac:(lia)) as SA. unfold add_u64 in SA.
      replace (decval rest =? 0) with false in SA by (symmetry; apply Z.eqb_neq; exact Hd0). unfold add_bn in SA. cbn [cells BnModel.ex] in SA.
      destruct SA as (Hok5 & Hn5 & _).
      eapply (CF 0x35f0c regs5 m5 (BN (add_l 0 l1 (chunks 3 (decval rest))) 0)); [left; reflexivity | | | exact Hbn5 | exact Hok5 | exact Hn5 | reflexivity | | | | |].
      { etransitivity; [exact (K5 8 ltac:(inl)) |]. etransitivity; [exact (K4' 8 ltac:(inl)) | exact D8]. }
      { etransitivity; [exact (K5 2 ltac:(inl)) |]. etransitivity; [exact (K4' 2 ltac:(inl)) | exact D2]. }
      { eapply unch_trans; [exact U4' | exact U5]. }
      { eapply mem_grows_trans; [exact G4 | exact G5]. }
      { eapply keeps_trans; [eapply keeps_sub_dec; [exact K14|]; vm_compute; reflexivity |].
        eapply keeps_trans; [eapply keeps_sub_dec; [exact K4'|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity]. }
      { eapply arr32_unch; [exact U5 | lia | cbn; lia | | exact Htbl4]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]]; cbn; lia. }
      eapply msteps_trans; [exact M14 |]. eapply msteps_trans; [exact ZM | exact M5].
Qed.
End S.
