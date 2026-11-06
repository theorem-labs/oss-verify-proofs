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
 BnModel BnMath BnMem BnDefs LibIface BnP_add BnP_ads2 BnP_ads3 BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsRtLibB AsZX AsZXTac AsZXDefs BnA_lib BnA_frame
 BnB_lib BnB_mul7 BnB_add2 AsFree5B BnB_ads1 BnB_ads3 BnB_ads4.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Ltac flia0 := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
#[local] Ltac BnB_ads1.flia ::= lf_once flia0.
Ltac inr0 H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac BnB_ads1.inr H tac ::= lf_once ltac:(inr0 H tac).
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (o buf len sp sp1 FS p2 g og bg0 bgl : Z) (ds : list Z).
Hypothesis GG : adsG o buf len sp sp1 FS p2 g og bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.
Hypothesis DOK : digits_ok ds.

#[local] Abbreviation F := (FS + 5279744 + p2 * 2048).
#[local] Abbreviation G := g.
#[local] Abbreviation AMBs := (AMB o buf bg0 bgl ds).
#[local] Abbreviation NSs := (NS o FS p2 g).
#[local] Abbreviation SL1s := (SL1 o sp1 g og).
#[local] Abbreviation SL2s := (SL2 o buf sp1 FS p2).
#[local] Abbreviation WINs := (WIN o sp FS p2 g).
#[local] Abbreviation AMBu := (AMB_unch o buf len sp sp1 FS p2 g og bg0 bgl ds GG Hds).
#[local] Abbreviation SL1u := (SL1_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).
#[local] Abbreviation SL2u := (SL2_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).
#[local] Abbreviation WINg := (WIN_grows o sp FS p2 g).
#[local] Abbreviation SAVu := (SAV_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).


#[using="len GG Hds DOK"] Lemma tail_B : forall regs m (done rest : list Z) (b : bn) (vs : list Z),
  let pos := zlen done in let lr := zlen rest in
  ds = done ++ rest ->
  getr regs 9%bv = Z_to_bv 64 sp1 -> getr regs 2%bv = Z_to_bv 64 sp1 -> getr regs 24%bv = Z_to_bv 64 buf ->
  getr regs 22%bv = Z_to_bv 64 pos -> getr regs 11%bv = Z_to_bv 64 lr -> getr regs 20%bv = Z_to_bv 64 SHA ->
  getr regs 25%bv = Z_to_bv 64 o -> getr regs 26%bv = Z_to_bv 64 F -> getr regs 18%bv = Z_to_bv 64 F ->
  getr regs 8%bv = Z_to_bv 64 sp -> getr regs 4%bv = Z_to_bv 64 TP_B ->
  AMBs m -> SL1s m -> WINs m -> SAV sp m vs -> length vs = 13%nat -> (forall k, (k < 13)%nat -> 0 <= nth k vs 0 < 2 ^ 64) ->
  ret_ok (Z_to_bv 64 (nth 0 vs 0)) -> rt_ok_B m -> ro_ok SEGS_B RO_B m ->
  mem_u64 m (F + 2040) (FS + 35840 + p2) -> mem_def m (FS + 35840 + p2) 1 ->
  lr < 19 ->
  bn_at SEGS_B m o b -> ok (cells b) -> norm (cells b) -> ex b = 0 -> 0 <= val (cells b) < 10 ^ pos ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa41c) m rom) (mkst regs' (Z_to_bv 64 (nth 0 vs 0)) m' rom)
    /\ bn_at SEGS_B m' o (clamp (ads_step rest b))
    /\ getr regs' 2%bv = Z_to_bv 64 sp /\ rest13 regs' vs /\ keeps [3; 4] regs regs'
    /\ mem_byte m' (FS + 35840 + p2) 0
    /\ unch m m' ((sp1 - 128, sp1) :: NSs) /\ mem_grows m m'.
Proof.
  intros regs m done rest b vs pos lr Hsplit R9 R2 R24 R22 R11 R20 R25 R26 R18 R8 R4 AM L1 W SV Hvs Hvr Hret RT RO Hq Hdq
    Hlr Hbn Hok Hn Hex Hval.
  assert (Epos : pos = Z.of_nat (length done)) by reflexivity. assert (Elr : lr = Z.of_nat (length rest)) by reflexivity.
  clearbody pos lr. assert (Hpos0 : 0 <= pos) by lia. assert (Hlr0 : 0 <= lr) by lia.
  assert (Hpr : pos + lr = len).
  { pose proof Hds as X. rewrite Hsplit, length_app in X. pose proof (g_len _ _ _ _ _ _ _ _ _ _ _ GG). lia. }
  pose proof GG as GG0. geom GG.
  pose proof AM as (SC & MC & TBL & TSH & OSH & DG & DSH & K27C). pose proof W as (Wsp & Wo & WF & WG).
  pose proof L1 as (L240 & L64 & L24 & L48 & L32 & L40).
  pose proof DOK as DOK'. rewrite Hsplit in DOK'. destruct (digits_ok_app_inv _ _ DOK') as [DOKd DOKr].
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
  assert (CF : forall regs5 m5 (b5 : bn),
    getr regs5 9%bv = Z_to_bv 64 sp1 -> getr regs5 2%bv = Z_to_bv 64 sp1 -> getr regs5 25%bv = Z_to_bv 64 o ->
    getr regs5 20%bv = Z_to_bv 64 SHA -> getr regs5 26%bv = Z_to_bv 64 F -> getr regs5 18%bv = Z_to_bv 64 F ->
    getr regs5 8%bv = Z_to_bv 64 sp -> getr regs5 4%bv = Z_to_bv 64 TP_B -> getr regs5 24%bv = Z_to_bv 64 (SHA + og) ->
    bn_at SEGS_B m5 o b5 -> ok (cells b5) -> norm (cells b5) -> ex b5 = 0 -> zlen (cells b5) <= 126 ->
    unch m m5 ((sp1 - 128, sp1) :: NSs) -> mem_grows m m5 -> keeps [3; 4] regs regs5 ->
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa41c) m rom) (mkst regs5 (Z_to_bv 64 0x0aa50c) m5 rom) ->
    exists regs' m',
      msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa41c) m rom) (mkst regs' (Z_to_bv 64 (nth 0 vs 0)) m' rom)
      /\ bn_at SEGS_B m' o (clamp b5)
      /\ getr regs' 2%bv = Z_to_bv 64 sp /\ rest13 regs' vs /\ keeps [3; 4] regs regs'
      /\ mem_byte m' (FS + 35840 + p2) 0
      /\ unch m m' ((sp1 - 128, sp1) :: NSs) /\ mem_grows m m').
  { intros regs5 m5 b5 Q9 Q2 Q25 Q20 Q26 Q18 Q8 Q4 Q24 Hbn5 Hok5 Hn5 Hex5 Hl5 U5 G5 K5 M5.
    destruct b5 as [l5 e5]. cbn [cells BnModel.ex] in *. subst e5.
    destruct (clampfin_B rom o buf len sp sp1 FS p2 g og bg0 bgl ds GG0 Hds regs5 m5 l5 0 vs Q9 Q2 Q25 Q20 Q26 Q18 Q8 Q4 Q24 Hbn5 Hok5 Hn5 Hl5)
      as (regs6 & m6 & M6 & Hbn6 & E2 & SR & K6 & FL & U6 & G6).
    { exact (AMBu m m5 _ U5 ltac:(unfold NS; rngs) AM). }
    { exact (SL1u m m5 _ U5 ltac:(unfold NS; rngs) L1). }
    { exact (WINg m m5 G5 W). }
    { exact (SAVu m m5 _ vs U5 ltac:(unfold NS; rngs) SV). }
    { exact Hvs. } { exact Hvr. } { exact Hret. }
    { eapply rt_ok_B_unch; [exact U5 | unfold NS; intros r Hr; unfold highr; inr Hr ltac:(slia) | exact RT]. }
    { eapply ro_ok_unchB; [exact U5 | unfold NS; intros r Hr; unfold highr; inr Hr ltac:(slia) | exact RO]. }
    { eapply mem_u64_unch; [exact U5 | lia | lia | unfold NS; intros r Hr; inr Hr ltac:(slia) | exact Hq]. }
    { eapply mem_def_grows; [exact G5 | exact Hdq]. }
    eexists regs6, m6. split; [eapply msteps_trans; [exact M5 | exact M6]|].
    split; [exact Hbn6|]. split; [exact E2|]. split; [exact SR|]. split; [eapply keeps_trans; [exact K5 | exact K6]|].
    split; [exact FL|]. split; [|eapply mem_grows_trans; [exact G5 | exact G6]].
    eapply unch_trans; [exact U5|]. unfold NS. unch_ns U6. }
  (* [comment removed for export] *)
  assert (RL : forall pc regs4 m4 (dz : Z),
    (pc = 0x0aa490 /\ dz = 0) \/ (pc = 0x0aa4a0 /\ getr regs4 19%bv = Z_to_bv 64 dz /\ 0 <= dz < 2 ^ 64) ->
    getr regs4 9%bv = Z_to_bv 64 sp1 -> SL1s m4 ->
    exists regs5,
      msteps SEGS_B (mkst regs4 (Z_to_bv 64 pc) m4 rom) (mkst regs5 (Z_to_bv 64 (if dz =? 0 then 0x0aa50c else 0x0aa4a8)) m4 rom)
      /\ getr regs5 24%bv = Z_to_bv 64 (SHA + og)
      /\ keeps [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31] regs4 regs5).
  { intros pc regs4 m4 dz Hpc Q9 L14. destruct L14 as (_ & _ & _ & M48 & _ & _).
    destruct Hpc as [[-> ->] | (-> & Q19 & Hdz)].
    - zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (SHA, KHI - 65)]) [KC (ZV 32) 48 8 (ZV 33)] (@nil kwin))
        5%nat [0x0aa50c] (SCR [] []) constr:([(9%bv : reg, ZV 32)]) [sp1; SHA + og] constr:([Some (KHI + 256, HIE - 384); Some (SHA, KHI - 65)]) regs4 m4 rom 0x0aa490.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 M48; exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
      exists regs5. cbn [Z.eqb]. split; [exact ZM|]. split; [zx_regv ZR|]. eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
    - destruct (Z.eqb_spec dz 0) as [Hd0 | Hd0].
      + zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (SHA, KHI - 65)]) [KC (ZV 32) 48 8 (ZV 33)] (@nil kwin))
          5%nat [0x0aa50c; 0x0aa4a8] (SCR [] []) constr:([(9%bv : reg, ZV 32); (19%bv : reg, ZL 0)]) [sp1; SHA + og] constr:([Some (KHI + 256, HIE - 384); Some (SHA, KHI - 65)]) regs4 m4 rom 0x0aa4a0.
        zx_use2 ZXB ltac:(zx_pins; rewrite Q19, Hd0; reflexivity) ltac:(zx_lia) ltac:(kc1 M48; exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
        exists regs5. split; [exact ZM|]. split; [zx_regv ZR|]. eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
      + zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (SHA, KHI - 65); Some (1, 2 ^ 64 - 1)]) [KC (ZV 32) 48 8 (ZV 33)] (@nil kwin))
          5%nat [0x0aa50c; 0x0aa4a8] (SCR [] []) constr:([(9%bv : reg, ZV 32); (19%bv : reg, ZV 34)]) [sp1; SHA + og; dz] constr:([Some (KHI + 256, HIE - 384); Some (SHA, KHI - 65); Some (1, 2 ^ 64 - 1)]) regs4 m4 rom 0x0aa4a0.
        zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 M48; exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
        exists regs5. split; [exact ZM|]. split; [zx_regv ZR|]. eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  destruct (Z.eq_dec lr 0) as [Hlr0' | Hlr1].
  - (* [comment removed for export] *)
    rewrite Hlr0' in *.
    assert (Erest : rest = []) by (destruct rest; [reflexivity | cbn in Elr; lia]).
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (0, 780); Some (IMG, HIE - 516)]) (@nil kcell) (@nil kwin)) 12%nat [0x0aa708; 0x0aa434] (SCR [true] [])
      constr:([(22%bv : reg, ZV 32); (11%bv : reg, ZL 0); (25%bv : reg, ZV 33)]) [pos; o] constr:([Some (0, 780); Some (IMG, HIE - 516)]) regs m rom 0x0aa41c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs1.
    assert (A2 : getr regs1 2%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R2]).
    destruct (mulpow10_B rom regs1 m o 0 sp1 (Z_to_bv 64 0x0aa490) b ltac:(zx_regv ZR) ltac:(zx_regv ZR) A2 ltac:(zx_regv ZR)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hbn Hok Hn) as (regs2 & m2 & M2 & K2 & Hbn2 & Htbl2 & U2 & G2).
    { rewrite Z.pow_0_r, Z.mul_1_r. eapply Z.lt_trans; [apply (proj2 Hval)|]. eapply Z.le_lt_trans; [|exact pow10_780]. apply Z.pow_le_mono_r; lia. }
    { rewrite Hex. cbn. lia. }
    { exact TBL. } { exact TSH. } { exact SC. } { exact OSH. } { exact K27C. } { lia. } { lia. } { lia. } { lia. } { lia. } { flia. }
    { eapply store_ok_of_def_in; [exact Wo|]. zwidth. lia. } { eapply store_ok_of_def_in; [exact Wsp|]. zwidth. lia. }
    assert (K12 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs2).
    { eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]. }
    assert (U2' : unch m m2 ((sp1 - 128, sp1) :: NSs)) by (unfold NS; unch_ns U2).
    destruct (RL 0x0aa490 regs2 m2 0 ltac:(left; split; reflexivity) ltac:(kept K12 9 R9) (SL1u m m2 _ U2' ltac:(unfold NS; rngs) L1)) as (regs3 & M3 & C24 & K3).
    cbn [Z.eqb] in M3.
    assert (K13 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27] regs regs3).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K12|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity]. }
    replace (ads_step rest b) with (mulpow10 0 b).
    2:{ subst rest. unfold ads_step. cbn [read_digits zlen length Z.of_nat]. unfold add_u64. reflexivity. }
    eapply (CF regs3 m2 (mulpow10 0 b)); [kept K13 9 R9 | kept K13 2 R2 | kept K13 25 R25 | kept K13 20 R20 | kept K13 26 R26 | kept K13 18 R18 | kept K13 8 R8 | kept K13 4 R4
      | exact C24 | exact Hbn2 | exact Hok2 | exact Hn2 | exact Hex2' | lia | exact U2' | exact G2 | eapply keeps_sub_dec; [exact K13|]; vm_compute; reflexivity |].
    eapply msteps_trans; [exact ZM|]. eapply msteps_trans; [exact M2 | exact M3].
  - (* [comment removed for export] *)
    assert (Hne : rest <> []) by (destruct rest; [cbn in Elr; lia | congruence]).
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (0, 780); Some (1, 18); Some (IMG, HIE - 1); Some (IMG, HIE - 2048)]) (@nil kcell) (@nil kwin)) 15%nat [0x0aa448; 0x0aa488] (SCR [false] [])
      constr:([(22%bv : reg, ZV 32); (11%bv : reg, ZV 33); (24%bv : reg, ZV 34); (26%bv : reg, ZV 35)]) [pos; lr; buf; F]
      constr:([Some (0, 780); Some (1, 18); Some (IMG, HIE - 1); Some (IMG, HIE - 2048)]) regs m rom 0x0aa41c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs1.
    assert (K1 : keeps [1; 2; 3; 4; 8; 9; 11; 18; 20; 21; 22; 24; 25; 26; 27] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (23%bv : reg) as A23.
    destruct (rdtail_B rom o buf len sp sp1 FS p2 g og bg0 bgl ds GG0 Hds rest regs1 m pos 0 (pos + lr)) as (regs2 & M2 & C19 & C12 & K2).
    { kept K1 24 R24. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { kept K1 20 R20. } { zx_regv ZR. }
    { unfold zlen; lia. } { exact Hne. } { exact DOKr. }
    { intros k Hk. pose proof DG as DG'. unfold digs in DG'. rewrite Hsplit in DG'. specialize (DG' (length done + k)%nat ltac:(rewrite length_app; lia)).
      rewrite app_nth2 in DG' by lia. replace (length done + k - length done)%nat with k in DG' by lia.
      eapply cellN_eqa; [exact DG' | lia | reflexivity]. }
    { exact DSH. } { lia. } { replace (zlen rest) with lr by (unfold zlen; lia). lia. } { lia. } { lia. }
    clear ZE ZR ZF. rename ZM into M1.
    (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa708] (SCR [] [])
      constr:([(25%bv : reg, ZV 32)]) [o] constr:([Some (IMG, HIE - 516)]) regs2 m rom 0x0aa498.
    zx_use2 ZXB ltac:(zx_pins; etransitivity; [exact (K2 25 ltac:(in_list)) | kept K1 25 R25]) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I).
    zx_name regs3.
    assert (K3 : keeps [2; 3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    assert (B2 : getr regs3 2%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K3 2 ltac:(in_list)) |]; etransitivity; [exact (K2 2 ltac:(in_list)) | kept K1 2 R2]).
    assert (B11 : getr regs3 11%bv = Z_to_bv 64 lr) by (etransitivity; [exact (K3 11 ltac:(in_list)) |]; etransitivity; [exact (K2 11 ltac:(in_list)) | kept K1 11 R11]).
    assert (B19 : getr regs3 19%bv = Z_to_bv 64 (decval rest)) by (etransitivity; [exact (K3 19 ltac:(in_list)) | exact C19]).
    assert (B23 : getr regs3 23%bv = Z_to_bv 64 (F + 32)) by (etransitivity; [exact (K3 23 ltac:(in_list)) |]; etransitivity; [exact (K2 23 ltac:(in_list)) | etransitivity; [exact A23 | f_equal; lia]]).
    destruct (mulpow10_B rom regs3 m o lr sp1 (Z_to_bv 64 0x0aa4a0) b ltac:(zx_regv ZR) B11 B2 ltac:(zx_regv ZR)
                ltac:(vm_compute; reflexivity) ltac:(lia) Hbn Hok Hn) as (regs4 & m4 & M4 & K4 & Hbn4 & Htbl4 & U4 & G4).
    { apply (val_bound_mul _ pos lr); lia. }
    { rewrite Hex, Z.div_small by lia. cbn. lia. }
    { exact TBL. } { exact TSH. } { exact SC. } { exact OSH. } { exact K27C. } { lia. } { lia. } { lia. } { lia. } { lia. } { flia. }
    { eapply store_ok_of_def_in; [exact Wo|]. zwidth. lia. } { eapply store_ok_of_def_in; [exact Wsp|]. zwidth. lia. }
    assert (K14 : keeps [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27] regs regs4).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|].
      eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
    assert (D19 : getr regs4 19%bv = Z_to_bv 64 (decval rest)) by (kept K4 19 B19).
    assert (D23 : getr regs4 23%bv = Z_to_bv 64 (F + 32)) by (kept K4 23 B23).
    assert (M14 : msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa41c) m rom) (mkst regs4 (Z_to_bv 64 0x0aa4a0) m4 rom)).
    { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact ZM | exact M4]. }
    clear ZE ZR ZF ZM.
    assert (U4' : unch m m4 ((sp1 - 128, sp1) :: NSs)) by (unfold NS; unch_ns U4).
    pose proof (AMBu m m4 _ U4' ltac:(unfold NS; rngs) AM) as AM4.
    pose proof (SL1u m m4 _ U4' ltac:(unfold NS; rngs) L1) as L14.
    pose proof (WINg m m4 G4 W) as W4.
    remember (mulpow10 lr b) as b1 eqn:Eb1. destruct b1 as [l1 e1]. cbn [cells BnModel.ex] in *. subst e1.
    replace (ads_step rest b) with (add_u64 (decval rest) (BN l1 0)).
    2:{ unfold ads_step. replace (zlen rest) with lr by (unfold zlen; lia). rewrite <- Eb1. reflexivity. }
    destruct (RL 0x0aa4a0 regs4 m4 (decval rest) ltac:(right; split; [reflexivity | split; [exact D19 | lia]]) ltac:(kept K14 9 R9) L14) as (regs4' & M4' & C24 & K4').
    unfold add_u64. destruct (Z.eqb_spec (decval rest) 0) as [Hd0|Hd0].
    + (* [comment removed for export] *)
      assert (K5 : keeps [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26; 27] regs regs4').
      { eapply keeps_trans; [eapply keeps_sub_dec; [exact K14|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K4'|]; vm_compute; reflexivity]. }
      eapply (CF regs4' m4 (BN l1 0)); [kept K5 9 R9 | kept K5 2 R2 | kept K5 25 R25 | kept K5 20 R20 | kept K5 26 R26 | kept K5 18 R18 | kept K5 8 R8 | kept K5 4 R4
        | exact C24 | exact Hbn4 | exact Hok2 | exact Hn2 | reflexivity | cbn [cells]; lia | exact U4' | exact G4 | eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity |].
      eapply msteps_trans; [exact M14 | exact M4'].
    + (* [comment removed for export] *)
      destruct (au64add_B2 rom o buf len sp sp1 FS p2 g og bg0 bgl ds GG0 Hds (add_B rom) regs4' m4 (decval rest) l1) as (regs5 & m5 & M5 & Hbn5 & K5 & U5 & G5); try lia.
      { etransitivity; [exact (K4' 9 ltac:(in_list)) | kept K14 9 R9]. } { etransitivity; [exact (K4' 2 ltac:(in_list)) | kept K14 2 R2]. }
      { etransitivity; [exact (K4' 25 ltac:(in_list)) | kept K14 25 R25]. } { kept K4' 19 D19. } { kept K4' 23 D23. }
      { exact Hbn4. } { exact Hok2. } { exact AM4. } { exact L14. } { exact W4. }
      pose proof (add_u64_spec (decval rest) (BN l1 0) Hok2 Hn2 ltac:(lia)) as SA. unfold add_u64 in SA.
      replace (decval rest =? 0) with false in SA by (symmetry; apply Z.eqb_neq; exact Hd0). unfold add_bn in SA. cbn [cells BnModel.ex] in SA.
      destruct SA as (Hok5 & Hn5 & Hv5 & Hex5 & Hl5).
      assert (K15 : keeps [2; 3; 4; 8; 9; 18; 20; 25; 26; 27] regs regs5).
      { eapply keeps_trans; [eapply keeps_sub_dec; [exact K14|]; vm_compute; reflexivity|].
        eapply keeps_trans; [eapply keeps_sub_dec; [exact K4'|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity]. }
      assert (E24 : getr regs5 24%bv = Z_to_bv 64 (SHA + og)) by (kept K5 24 C24).
      eapply (CF regs5 m5 (BN (add_l 0 l1 (chunks 3 (decval rest))) 0)); [kept K15 9 R9 | kept K15 2 R2 | kept K15 25 R25 | kept K15 20 R20 | kept K15 26 R26 | kept K15 18 R18 | kept K15 8 R8 | kept K15 4 R4
        | exact E24 | exact Hbn5 | exact Hok5 | exact Hn5 | reflexivity | | | | eapply keeps_sub_dec; [exact K15|]; vm_compute; reflexivity |].
      { cbn [cells]. cbn [cells] in Hl5. lia. }
      { eapply unch_trans; [exact U4' | exact U5]. }
      { eapply mem_grows_trans; [exact G4 | exact G5]. }
      eapply msteps_trans; [exact M14 |]. eapply msteps_trans; [exact M4' | exact M5].
Qed.
End S.
