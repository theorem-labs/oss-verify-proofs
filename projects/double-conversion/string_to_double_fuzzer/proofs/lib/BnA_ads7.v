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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_frame BnA_ads1 BnA_ads2 BnA_ads3 BnA_ads4 BnA_ads5 BnA_ads6.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Ltac flia0 := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
#[local] Ltac BnA_ads1.flia ::= lf_once flia0.
Ltac inr0 H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
#[local] Ltac BnA_ads1.inr H tac ::= lf_once ltac:(inr0 H tac).
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (o buf len sp FS og bg0 bgl : Z) (ds : list Z) (fl : Z -> Z).
Hypothesis GE : adsE o buf len sp FS og bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.
Hypothesis DOK : digits_ok ds.
(* [comment removed for export] *)
Hypothesis Hfl01 : forall j, 0 <= j < 512 -> fl j = 0 \/ fl j = 1.
Hypothesis Hflex : exists j, 0 <= j < 512 /\ fl j = 0.
Hypothesis HoFR : forall j, 0 <= j < 512 -> fl j = 0 -> o + 516 <= FS + 5279744 + j * 2048 \/ FS + 5279744 + j * 2048 + 2048 <= o.
Hypothesis HbFR : forall j, 0 <= j < 512 -> fl j = 0 -> buf + len <= FS + 5279744 + j * 2048 \/ FS + 5279744 + j * 2048 + 2048 <= buf.

#[local] Abbreviation sp1 := (sp1 sp).
#[local] Abbreviation AMBs := (AMB o buf bg0 bgl ds).

(* [comment removed for export] *)
Abbreviation b3_pins := [(9%bv : reg, ZV 32); (18%bv : reg, ZV 34); (21%bv : reg, ZV 35); (11%bv : reg, ZV 36); (27%bv : reg, ZL SHA);
   (19%bv : reg, ZAdd (ZV 34) (ZL 4)); (10%bv : reg, ZL 18446744073709551603); (20%bv : reg, ZV 37); (23%bv : reg, ZV 33);
   (25%bv : reg, ZV 33); (26%bv : reg, ZV 38)].
Abbreviation b3_uvi llo lhi := [Some (KHI + 256, HIE - 384); Some (IMG, HIE - 2048); Some (SHA, KHI - 256); Some (IMG, HIE - 516); Some (0, KHI);
   Some (llo, lhi); Some (IMG, HIE - 1)].
Abbreviation b3_kn := [KC (ZV 36) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 35) (ZL 2)) 3) SHA 1 (ZL 0)].
Abbreviation b3_kw := [KW (ZV 34) 0 256; KW (ZV 32) 0 280; KW (ZV 35) 0 516].
(* [comment removed for export] *)
Abbreviation b4_pins := [(9%bv : reg, ZV 32); (25%bv : reg, ZV 33); (23%bv : reg, ZV 33); (26%bv : reg, ZV 34)].
Abbreviation b4_uvi := [Some (KHI + 256, HIE - 384); Some (IMG, HIE - 2048); Some (IMG, HIE - 1)].

#[using="og GE Hds DOK Hfl01 Hflex HoFR HbFR"] Theorem ads_A : forall regs m (ret : word),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 buf -> getr regs 12%bv = Z_to_bv 64 len ->
  getr regs 2%bv = Z_to_bv 64 sp -> getr regs 1%bv = ret -> bv_unsigned ret mod 4 = 0 -> getr regs 4%bv = Z_to_bv 64 TP_A ->
  rt_ok m -> ro_ok SEGS_A RO_A m -> gsh_ok m -> objsh m o -> digs buf ds m -> dsh bg0 bgl m ->
  mem_def m (sp - 656) 656 -> mem_def m o 516 ->
  malloc_ctx_ok (sp - 656) sp FS m -> rd_u64 m FSTLS_A FS ->
  mem_def m FS FS_LEN -> mem_def m (sh FS + FS_SHLO) (FS_SHHI - FS_SHLO) -> mem_u64 m (FS + 88) 20 -> mem_byte m (FS + 96) 0 ->
  (forall j, 0 <= j < 512 -> mem_byte m (fs_flag FS 5 j) (fl j)) ->
  exists regs' m' p,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0a9c3c) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_A m' o (assign_decimal ds)
    /\ 0 <= p < 512 /\ fl p = 0
    /\ (forall j, 0 <= j < 512 -> mem_byte m' (fs_flag FS 5 j) (fl j))
    /\ unch m m' [(sp - 656, sp); (o, o + 516); (FS + 40, FS + 48); (fs_flag FS 5 p, fs_flag FS 5 p + 1);
                  (fs_frame FS 5 p, fs_frame FS 5 p + 2048); (sh (fs_frame FS 5 p), sh (fs_frame FS 5 p) + 256)]
    /\ mem_grows m m'.
Proof.
  intros regs m ret R10 R11 R12 R2 R1 Hret4 R4 RT RO GSH OSH DG DSH Dsp Do MCX TLS DFS DSHD L88 B96 FL.
  pose proof (ret_ok_of_mod4 ret Hret4) as Hret.
  destruct (ads_pro_A rom o buf len sp FS og bg0 bgl ds fl GE Hds Hfl01 Hflex HoFR HbFR regs m ret R10 R11 R12 R2 R1 Hret4 R4 RT RO GSH OSH DG DSH
              Dsp Do MCX TLS DFS DSHD L88 B96 FL)
    as (regs7 & m7 & p & F & g & M07 & Hp & Hflp & HFdef & HgF & GG0 & I9 & I2 & I4 & I8 & I18 & I19 & I20 & I21 & I23 & I25 & I26 & I27 & I10 & I11
        & K07 & AM7 & W7 & SV7 & S240 & RT7 & RO7 & Q2040 & FL1 & U07 & G07).
  clear Hret4. subst F. set (F := FS + 5279744 + p * 2048) in *. assert (HFdef : F = FS + 5279744 + p * 2048) by reflexivity.
  pose proof GG0 as GG. geom GG.
  pose proof AM7 as (SC7 & MC7 & TBL7 & TSH7 & OSH7 & DG7 & DSH7). pose proof W7 as (Wsp7 & Wo7 & WF7 & WG7).
  pose proof (OSH7 0 ltac:(lia)) as SHo. rewrite Z.add_0_r in SHo.
  assert (Elen : zlen ds = len) by (unfold zlen; lia).
  (* [comment removed for export] *)
  assert (FIN : forall regs10 m10 (done rest : list Z) (b : bn),
    ds = done ++ rest ->
    getr regs10 9%bv = Z_to_bv 64 sp1 -> getr regs10 2%bv = Z_to_bv 64 sp1 -> getr regs10 26%bv = Z_to_bv 64 buf ->
    getr regs10 22%bv = Z_to_bv 64 (zlen done) -> getr regs10 11%bv = Z_to_bv 64 (zlen rest) -> getr regs10 27%bv = Z_to_bv 64 SHA ->
    getr regs10 21%bv = Z_to_bv 64 o -> getr regs10 23%bv = Z_to_bv 64 F -> getr regs10 25%bv = Z_to_bv 64 F ->
    getr regs10 8%bv = Z_to_bv 64 sp -> getr regs10 4%bv = Z_to_bv 64 TP_A ->
    AMBs m10 -> SL1 o sp1 g og m10 -> WIN o sp FS p g m10 ->
    unch m7 m10 ((sp1 - 112, sp1) :: (sp1 + 248, sp1 + 256) :: (sp1 + 16, sp1 + 240) :: NS o FS p g) -> mem_grows m7 m10 ->
    keeps [3; 4] regs7 regs10 ->
    zlen rest < 19 ->
    bn_at SEGS_A m10 o b -> ok (cells b) -> norm (cells b) -> ex b = 0 -> 0 <= val (cells b) < 10 ^ zlen done ->
    (b, rest) = ads_loop (Nat.div (length ds) 19) ds bn_zero ->
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0a9c3c) m rom) (mkst regs10 (Z_to_bv 64 0x0aa364) m10 rom) ->
    exists regs' m' p',
      msteps SEGS_A (mkst regs (Z_to_bv 64 0x0a9c3c) m rom) (mkst regs' ret m' rom)
      /\ keeps CS regs regs' /\ bn_at SEGS_A m' o (assign_decimal ds)
      /\ 0 <= p' < 512 /\ fl p' = 0
      /\ (forall j, 0 <= j < 512 -> mem_byte m' (fs_flag FS 5 j) (fl j))
      /\ unch m m' [(sp - 656, sp); (o, o + 516); (FS + 40, FS + 48); (fs_flag FS 5 p', fs_flag FS 5 p' + 1);
                    (fs_frame FS 5 p', fs_frame FS 5 p' + 2048); (sh (fs_frame FS 5 p'), sh (fs_frame FS 5 p') + 256)]
      /\ mem_grows m m').
  { intros regs10 m10 done rest b Hsplit Q9 Q2 Q26 Q22 Q11 Q27 Q21 Q23 Q25 Q8 Q4 AM10 L10 W10 U710 G710 K710 Hlr Hbn Hok Hn Hex Hval Hal M010.
    pose proof (u64_range ret) as Wret.
    destruct (tail_A rom o buf len sp sp1 FS p g og bg0 bgl ds GG0 Hds DOK regs10 m10 done rest b (savs regs ret) Hsplit Q9 Q2 Q26 Q22 Q11 Q27 Q21 Q23 Q25 Q8 Q4
                AM10 L10 W10) as (regs11 & m11 & M11 & Hbn11 & E2 & REST & K11 & FL0 & U1011 & G1011).
    { eapply (SAV_unch o buf len sp sp1 FS p g og bg0 bgl GG0 m7 m10); [exact U710 | unfold NS; rngs | exact SV7]. }
    { reflexivity. }
    { intros k Hk. unfold savs.
      pose proof (u64_range (getr regs 8%bv)). pose proof (u64_range (getr regs 9%bv)). pose proof (u64_range (getr regs 18%bv)).
      pose proof (u64_range (getr regs 19%bv)). pose proof (u64_range (getr regs 20%bv)). pose proof (u64_range (getr regs 21%bv)).
      pose proof (u64_range (getr regs 22%bv)). pose proof (u64_range (getr regs 23%bv)). pose proof (u64_range (getr regs 24%bv)).
      pose proof (u64_range (getr regs 25%bv)). pose proof (u64_range (getr regs 26%bv)). pose proof (u64_range (getr regs 27%bv)).
      destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]; cbn [nth]; lia. }
    { unfold savs. cbn [nth]. rewrite Z_to_bv_bv_unsigned. exact Hret. }
    { eapply rt_ok_unch; [exact U710 | unfold NS; intros r Hr; unfold highr; inr Hr ltac:(slia) | exact RT7]. }
    { eapply ro_ok_unchA; [exact U710 | unfold NS; intros r Hr; unfold highr; inr Hr ltac:(slia) | exact RO7]. }
    { eapply mem_u64_unch; [exact U710 | lia | lia | unfold NS; intros r Hr; inr Hr ltac:(slia) | exact Q2040]. }
    { eapply mem_def_grows; [exact G710|]. eapply mem_def_of_byte. exact FL1. }
    { exact Hlr. } { exact Hbn. } { exact Hok. } { exact Hn. } { exact Hex. } { exact Hval. }
    unfold rest13, savs in M11, REST. cbn [nth] in M11, REST. rewrite Z_to_bv_bv_unsigned in M11.
    exists regs11, m11, p. split; [eapply msteps_trans; [exact M010 | exact M11]|].
    split.
    { destruct REST as (_ & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
      rewrite !Z_to_bv_bv_unsigned in X8, X9, X18, X19, X20, X21, X22, X23, X24, X25, X26, X27.
      intros rg Hrg. cbn in Hrg.
      destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        first [ etransitivity; [exact E2 | symmetry; exact R2] | exact X8 | exact X9 | exact X18 | exact X19 | exact X20 | exact X21 | exact X22 | exact X23
              | exact X24 | exact X25 | exact X26 | exact X27
              | lazymatch goal with |- getr _ (Z_to_bv 5 ?nn) = _ =>
                  etransitivity; [exact (K11 nn ltac:(in_list))|]; etransitivity; [exact (K710 nn ltac:(in_list))|]; exact (K07 nn ltac:(in_list)) end ]. }
    split; [unfold assign_decimal; rewrite <- Hal; exact Hbn11|].
    split; [exact Hp|]. split; [exact Hflp|].
    assert (U011 : unch m m11 [(sp - 656, sp); (o, o + 516); (FS + 40, FS + 48); (FS + 35840 + p, FS + 35840 + p + 1); (F, F + 2048); (g, g + 256)]).
    { eapply unch_trans; [eapply unch_widen; [exact U07|] | eapply unch_trans; [eapply unch_widen; [exact U710|] | eapply unch_widen; [exact U1011|]]];
        unfold NS; intros rg Hrg; cbn [fst snd];
        inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]
          | eexists; split; [do 2 right; left; reflexivity | cbn; lia] | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
          | eexists; split; [do 4 right; left; reflexivity | cbn; lia] | eexists; split; [do 5 right; left; reflexivity | cbn; lia] ]). }
    split.
    { intros j Hj. destruct (Z.eq_dec j p) as [-> | Hne]; [rewrite fs_flag5, Hflp; exact FL0|].
      rewrite fs_flag5. eapply mem_byte_unch; [exact U011 | lia | | rewrite <- fs_flag5; exact (FL j Hj)].
      intros r Hr. inr Hr ltac:(slia). }
    split; [| eapply mem_grows_trans; [exact G07|]; eapply mem_grows_trans; [exact G710 | exact G1011]].
    rewrite fs_flag5, fs_frame5. fold F. unfold sh, SH_A. replace (2147450880 + F / 8) with g by lia. exact U011. }
  destruct (Z_lt_dec len 19) as [Hlt | Hge].
  - (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ b3_uvi 1 18) b3_kn b3_kw) 60%nat [0x0aa364; 0x0a9e30] (SCR [] []) constr:(b3_pins)
      [sp1; F; g; o; og; len; buf] constr:(b3_uvi 1 18) regs7 m7 rom 0x0a9de0.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 SHo; kc1 SHo; exact I) ltac:(kwd WG7; kwd Wsp7; kwd Wo7; exact I) ltac:(idtac; zx_scs ltac:(flia)).
    zx_name regs8. rename ZM into M8.
    assert (K8 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27] regs7 regs8) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (22%bv : reg) as J22. zx_reg ZR (11%bv : reg) as J11.
    clear ZE ZR ZF. set (m8 := wbytes _ _ _) in M8.
    assert (U78 : unch m7 m8 [(sp1 + 32, sp1 + 80); (g + 167, g + 168); (o, o + 4)]) by (subst m8; clear - Gs1a Gs1b Gsp1 Gsp2 Gfs1 Gfs2 Gp2 Go1 Go2 HgF; unchx).
    assert (G78 : mem_grows m7 m8) by (subst m8; growsx).
    assert (L8 : SL1 o sp1 g og m8).
    { unfold SL1. split.
      { eapply cellN_unch; [exact U78 | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact S240]. }
      subst m8; clear - Gs1a Gs1b Gsp1 Gsp2 Gfs1 Gfs2 Gp2 Go1 Go2 Go8 HgF Dosp DoF DspFS.
      repeat split; cellx2. }
    assert (Hbn8 : bn_at SEGS_A m8 o bn_zero).
    { unfold bn_at, bn_zero. cbn [cells BnModel.ex]. change (zlen (@nil Z)) with 0.
      split; [|split; [|split; [apply arr32_nil | lia]]]; subst m8; clear - Gs1a Gs1b Gsp1 Gsp2 Gfs1 Gfs2 Gp2 Go1 Go2 Go8 HgF Dosp DoF DspFS; cellx2. }
    eapply (FIN regs8 m8 [] ds bn_zero); [reflexivity | kept K8 9 I9 | kept K8 2 I2 | kept K8 26 I26 | rewrite J22; reflexivity | rewrite J11, Elen; f_equal; lia
      | kept K8 27 I27 | kept K8 21 I21 | kept K8 23 I23 | kept K8 25 I25 | kept K8 8 I8 | kept K8 4 I4 | | exact L8 | exact (WIN_grows o sp FS p g m7 m8 G78 W7)
      | unfold NS; unch_ns U78 | exact G78 | eapply keeps_sub_dec; [exact K8|]; vm_compute; reflexivity | rewrite Elen; lia | exact Hbn8 | apply ok_nil | apply norm_nil | reflexivity
      | change (zlen (@nil Z)) with 0; rewrite Z.pow_0_r; cbn; lia | | eapply msteps_trans; [exact M07 | exact M8]].
    { eapply (AMB_unch o buf len sp sp1 FS p g og bg0 bgl ds GG0 Hds m7 m8); [exact U78 | rngs | exact AM7]. }
    { replace (Nat.div (length ds) 19) with 0%nat by (symmetry; apply Nat.div_small; lia). reflexivity. }
  - (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ b3_uvi 19 780) b3_kn b3_kw) 60%nat [0x0aa364; 0x0a9e30] (SCR [] []) constr:(b3_pins)
      [sp1; F; g; o; og; len; buf] constr:(b3_uvi 19 780) regs7 m7 rom 0x0a9de0.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 SHo; kc1 SHo; exact I) ltac:(kwd WG7; kwd Wsp7; kwd Wo7; exact I) ltac:(idtac; zx_scs ltac:(flia)).
    zx_name regs8. rename ZM into M8.
    assert (K8 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27] regs7 regs8) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. set (m8 := wbytes _ _ _) in M8.
    assert (U78 : unch m7 m8 [(sp1 + 32, sp1 + 80); (g + 167, g + 168); (o, o + 4)]) by (subst m8; clear - Gs1a Gs1b Gsp1 Gsp2 Gfs1 Gfs2 Gp2 Go1 Go2 HgF; unchx).
    assert (G78 : mem_grows m7 m8) by (subst m8; growsx).
    assert (L8 : SL1 o sp1 g og m8).
    { unfold SL1. split.
      { eapply cellN_unch; [exact U78 | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact S240]. }
      subst m8; clear - Gs1a Gs1b Gsp1 Gsp2 Gfs1 Gfs2 Gp2 Go1 Go2 Go8 HgF Dosp DoF DspFS.
      repeat split; cellx2. }
    assert (Hbn8 : bn_at SEGS_A m8 o bn_zero).
    { unfold bn_at, bn_zero. cbn [cells BnModel.ex]. change (zlen (@nil Z)) with 0.
      split; [|split; [|split; [apply arr32_nil | lia]]]; subst m8; clear - Gs1a Gs1b Gsp1 Gsp2 Gfs1 Gfs2 Gp2 Go1 Go2 Go8 HgF Dosp DoF DspFS; cellx2. }
    pose proof (WIN_grows o sp FS p g m7 m8 G78 W7) as W8. pose proof W8 as (Wsp8 & _).
    (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ b4_uvi) (@nil kcell) [KW (ZV 32) 0 280]) 60%nat [0x0a9f08] (SCR [] []) constr:(b4_pins)
      [sp1; F; buf] constr:(b4_uvi) regs8 m8 rom 0x0a9e30.
    zx_use2 ZXB ltac:(zx_pins; first [kept K8 9 I9 | kept K8 25 I25 | kept K8 23 I23 | kept K8 26 I26]) ltac:(zx_lia) ltac:(exact I) ltac:(kwd Wsp8; exact I) ltac:(exact I).
    zx_name regs9. rename ZM into M9.
    assert (K9 : keeps [2; 3; 4; 8; 9; 19; 20; 21; 24; 25; 26; 27] regs8 regs9) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (22%bv : reg) as J22. zx_reg ZR (23%bv : reg) as J23. zx_reg ZR (18%bv : reg) as J18.
    clear ZE ZR ZF. set (m9 := wbytes _ _ _) in M9.
    assert (U89 : unch m8 m9 [(sp1 + 16, sp1 + 32); (sp1 + 64, sp1 + 72); (sp1 + 80, sp1 + 240)]) by (subst m9; clear - Gs1a Gs1b Gsp1 Gsp2; unchx).
    assert (G89 : mem_grows m8 m9) by (subst m9; growsx).
    assert (L9 : SL1 o sp1 g og m9).
    { destruct L8 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). unfold SL1.
      repeat match goal with |- _ /\ _ => split end;
        (eapply cellN_unch; [exact U89 | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | eassumption]). }
    assert (L29 : SL2 buf sp1 FS p m9).
    { unfold SL2. subst m9; clear - Gs1a Gs1b Gsp1 Gsp2 Gfs1 Gfs2 Gp2 Gb1 Gb2 Glen.
      split; [cellx2|]. split; [cellx2|]. split; [cellx2|]. split; [cellx2|]. split; [cellx2|].
      intros k Hk.
      assert (CASES : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18) by lia.
      destruct CASES as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]]]]]]]];
        [replace (sp1 + 232 - 8 * 1) with (sp1 + 224) by lia; cellx2 | replace (sp1 + 232 - 8 * 2) with (sp1 + 216) by lia; cellx2 | replace (sp1 + 232 - 8 * 3) with (sp1 + 208) by lia; cellx2 | replace (sp1 + 232 - 8 * 4) with (sp1 + 200) by lia; cellx2 | replace (sp1 + 232 - 8 * 5) with (sp1 + 192) by lia; cellx2 | replace (sp1 + 232 - 8 * 6) with (sp1 + 184) by lia; cellx2 | replace (sp1 + 232 - 8 * 7) with (sp1 + 176) by lia; cellx2 | replace (sp1 + 232 - 8 * 8) with (sp1 + 168) by lia; cellx2 | replace (sp1 + 232 - 8 * 9) with (sp1 + 160) by lia; cellx2 | replace (sp1 + 232 - 8 * 10) with (sp1 + 152) by lia; cellx2 | replace (sp1 + 232 - 8 * 11) with (sp1 + 144) by lia; cellx2 | replace (sp1 + 232 - 8 * 12) with (sp1 + 136) by lia; cellx2 | replace (sp1 + 232 - 8 * 13) with (sp1 + 128) by lia; cellx2 | replace (sp1 + 232 - 8 * 14) with (sp1 + 120) by lia; cellx2 | replace (sp1 + 232 - 8 * 15) with (sp1 + 112) by lia; cellx2 | replace (sp1 + 232 - 8 * 16) with (sp1 + 104) by lia; cellx2 | replace (sp1 + 232 - 8 * 17) with (sp1 + 96) by lia; cellx2 | replace (sp1 + 232 - 8 * 18) with (sp1 + 88) by lia; cellx2]. }
    (* [comment removed for export] *)
    assert (U79 : unch m7 m9 [(sp1 + 16, sp1 + 240); (g + 167, g + 168); (o, o + 4)]).
    { eapply unch_trans; [eapply unch_widen; [exact U78|] | eapply unch_widen; [exact U89|]];
        intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]
          | eexists; split; [do 2 right; left; reflexivity | cbn; lia] ]). }
    assert (G79 : mem_grows m7 m9) by (eapply mem_grows_trans; [exact G78 | exact G89]).
    pose proof (AMB_unch o buf len sp sp1 FS p g og bg0 bgl ds GG0 Hds m7 m9 _ U79 ltac:(rngs) AM7) as AM9.
    pose proof (WIN_grows o sp FS p g m7 m9 G79 W7) as W9.
    assert (Hbn9 : bn_at SEGS_A m9 o bn_zero).
    { eapply bn_at_unch; [exact U89 | lia | cbn; lia | intros r Hr; inr Hr ltac:(slia) | exact Hbn8]. }
    remember (ads_loop (Nat.div (length ds) 19) ds bn_zero) as AL eqn:HAL. destruct AL as [b' rest'].
    destruct (loop19_A rom o buf len sp sp1 FS p g og bg0 bgl ds GG0 Hds DOK (Nat.div (length ds) 19) regs9 m9 [] ds bn_zero eq_refl)
      as (regs10 & m10 & M10 & POST & P26 & K10 & AM10 & L110 & L210 & W10 & U910 & G910).
    { etransitivity; [exact (K9 9 ltac:(in_list)) | kept K8 9 I9]. }
    { etransitivity; [exact (K9 2 ltac:(in_list)) | kept K8 2 I2]. }
    { etransitivity; [exact (K9 26 ltac:(in_list)) | kept K8 26 I26]. }
    { change (zlen (@nil Z)) with 0. exact J22. }
    { rewrite Elen. etransitivity; [exact (K9 20 ltac:(in_list)) | kept K8 20 I20]. }
    { etransitivity; [exact (K9 27 ltac:(in_list)) | kept K8 27 I27]. }
    { exact J18. }
    { etransitivity; [exact (K9 21 ltac:(in_list)) | kept K8 21 I21]. }
    { exact J23. }
    { exact AM9. } { exact L9. } { exact L29. } { exact W9. }
    { rewrite Elen. lia. } { apply le_n. }
    { exact Hbn9. } { apply ok_nil. } { apply norm_nil. } { reflexivity. } { change (zlen (@nil Z)) with 0. rewrite Z.pow_0_r. cbn. lia. }
    rewrite <- HAL in POST. cbn [fst snd] in POST. change (zlen (@nil Z)) with 0 in POST. rewrite Elen in POST.
    destruct POST as (Hbn10 & Hok10 & Hn10 & Hex10 & Hval10 & Hlr10 & (mid & Hmid) & P22 & P20 & P11).
    assert (Hzl : len = zlen mid + zlen rest') by (rewrite <- Elen, Hmid, zlen_app; reflexivity).
    pose proof L210 as (T24 & T16 & _).
    (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (IMG, HIE - 2048)]) [KC (ZV 32) 24 8 (ZV 33); KC (ZV 32) 16 8 (ZV 33)] (@nil kwin))
      5%nat [0x0aa364] (SCR [] []) constr:([(9%bv : reg, ZV 32)]) [sp1; F] constr:([Some (KHI + 256, HIE - 384); Some (IMG, HIE - 2048)]) regs10 m10 rom 0x0aa35c.
    zx_use2 ZXB ltac:(zx_pins; etransitivity; [exact (K10 9 ltac:(in_list)) |]; etransitivity; [exact (K9 9 ltac:(in_list)) | kept K8 9 I9])
      ltac:(zx_lia) ltac:(kc1 T24; kc1 T16; exact I) ltac:(exact I) ltac:(exact I). zx_name regs11.
    assert (KB : keeps [1; 2; 3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 24; 26; 27] regs10 regs11) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (23%bv : reg) as Z23. zx_reg ZR (25%bv : reg) as Z25. rename ZM into MB. clear ZE ZR ZF.
    assert (K711 : keeps [3; 4; 8] regs7 regs11).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K8|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K9|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K10|]; vm_compute; reflexivity|].
      eapply keeps_sub_dec; [exact KB|]; vm_compute; reflexivity. }
    assert (P9 : getr regs10 9%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K10 9 ltac:(in_list)) |]; etransitivity; [exact (K9 9 ltac:(in_list)) | kept K8 9 I9]).
    assert (P2 : getr regs10 2%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K10 2 ltac:(in_list)) |]; etransitivity; [exact (K9 2 ltac:(in_list)) | kept K8 2 I2]).
    assert (P27 : getr regs10 27%bv = Z_to_bv 64 SHA) by (etransitivity; [exact (K10 27 ltac:(in_list)) |]; etransitivity; [exact (K9 27 ltac:(in_list)) | kept K8 27 I27]).
    assert (P21 : getr regs10 21%bv = Z_to_bv 64 o) by (etransitivity; [exact (K10 21 ltac:(in_list)) |]; etransitivity; [exact (K9 21 ltac:(in_list)) | kept K8 21 I21]).
    eapply (FIN regs11 m10 mid rest' b'); [exact Hmid | kept KB 9 P9 | kept KB 2 P2 | kept KB 26 P26
      | etransitivity; [exact (KB 22 ltac:(in_list)) | etransitivity; [exact P22 | f_equal; lia]] | kept KB 11 P11 | kept KB 27 P27 | kept KB 21 P21
      | exact Z23 | exact Z25 | kept K711 8 I8 | kept K711 4 I4
      | exact AM10 | exact L110 | exact W10 | | eapply mem_grows_trans; [exact G79 | exact G910] | eapply keeps_sub_dec; [exact K711|]; vm_compute; reflexivity
      | lia | exact Hbn10 | exact Hok10 | exact Hn10 | exact Hex10 | replace (zlen mid) with (0 + len - zlen rest') by lia; exact Hval10 | reflexivity | ].
    { unfold NS2 in U910. unfold NS in U910 |- *.
      eapply unch_trans; [eapply unch_widen; [exact U79|] | eapply unch_widen; [exact U910|]];
        intros rg Hrg; cbn [fst snd]; inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]
          | eexists; split; [do 2 right; left; reflexivity | cbn; lia] | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
          | eexists; split; [do 4 right; left; reflexivity | cbn; lia] | eexists; split; [do 5 right; left; reflexivity | cbn; lia]
          | eexists; split; [do 6 right; left; reflexivity | cbn; lia] | eexists; split; [do 7 right; left; reflexivity | cbn; lia] ]). }
    eapply msteps_trans; [exact M07|]. eapply msteps_trans; [exact M8|]. eapply msteps_trans; [exact M9|]. eapply msteps_trans; [exact M10 | exact MB].
Qed.
End S.
