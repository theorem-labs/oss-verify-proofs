(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface BnP_ads3 BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_frame AsFree5A BnA_ads1.
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
Variables (o buf len sp sp1 FS p2 g og bg0 bgl : Z) (ds : list Z).
Hypothesis GG : adsG o buf len sp sp1 FS p2 g og bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.
Hypothesis DOK : digits_ok ds.

#[local] Abbreviation F := (FS + 5279744 + p2 * 2048).
#[local] Abbreviation G := g.
#[local] Abbreviation AMBs := (AMB o buf bg0 bgl ds).
#[local] Abbreviation NSs := (NS o FS p2 g).
#[local] Abbreviation SL1s := (SL1 o sp1 g og).
#[local] Abbreviation SL2s := (SL2 buf sp1 FS p2).
#[local] Abbreviation WINs := (WIN o sp FS p2 g).
#[local] Abbreviation AMBu := (AMB_unch o buf len sp sp1 FS p2 g og bg0 bgl ds GG Hds).
#[local] Abbreviation SL1u := (SL1_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).
#[local] Abbreviation SL2u := (SL2_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).
#[local] Abbreviation WINg := (WIN_grows o sp FS p2 g).
#[local] Abbreviation SAVu := (SAV_unch o buf len sp sp1 FS p2 g og bg0 bgl GG).

(* [comment removed for export] *)
Ltac cellxf :=
  lazymatch goal with
  | |- cellN _ (wbytes _ (Z_to_bv 64 _) (word_to_le_bytes _ _)) _ _ _ =>
      first
        [ assumption
        | apply bn_ctor_hi; [lia | zwidth; lia | lia]
        | apply cellN_store_same';
          [ cbn; lia | lia | zwidth; lia
          | rewrite ?u_Z2bv64; zwidth;
            first [ reflexivity | lia
                  | rewrite (Z.mod_small _ 18446744073709551616) by lia; first [apply Z.mod_small; lia | rewrite Z.mod_small by lia; lia | idtac]
                  | idtac ] ]
        | apply cellN_store_skip; [ flia | zwidth; flia | flia | zwidth; flia | zwidth; flia | cellxf ]
        | idtac ]
  | |- cellN _ _ _ _ _ => first [assumption | eassumption | idtac]
  end.

(* [comment removed for export] *)
Definition rest13 (regs : bvmap 5 word) (vs : list Z) : Prop :=
  getr regs 1%bv = Z_to_bv 64 (nth 0 vs 0) /\ getr regs 8%bv = Z_to_bv 64 (nth 1 vs 0) /\ getr regs 9%bv = Z_to_bv 64 (nth 2 vs 0)
  /\ getr regs 18%bv = Z_to_bv 64 (nth 3 vs 0) /\ getr regs 19%bv = Z_to_bv 64 (nth 4 vs 0) /\ getr regs 20%bv = Z_to_bv 64 (nth 5 vs 0)
  /\ getr regs 21%bv = Z_to_bv 64 (nth 6 vs 0) /\ getr regs 22%bv = Z_to_bv 64 (nth 7 vs 0) /\ getr regs 23%bv = Z_to_bv 64 (nth 8 vs 0)
  /\ getr regs 24%bv = Z_to_bv 64 (nth 9 vs 0) /\ getr regs 25%bv = Z_to_bv 64 (nth 10 vs 0) /\ getr regs 26%bv = Z_to_bv 64 (nth 11 vs 0)
  /\ getr regs 27%bv = Z_to_bv 64 (nth 12 vs 0).

(* [comment removed for export] *)
Abbreviation cl_pins := [(9%bv : reg, ZV 32); (21%bv : reg, ZV 33); (27%bv : reg, ZL SHA); (23%bv : reg, ZV 37); (25%bv : reg, ZV 37)].
Abbreviation cl_uvi ulo uhi := [Some (KHI + 256, HIE - 384); Some (IMG, HIE - 516); Some (SHA, KHI - 65); Some (ulo, uhi); Some (1, 2 ^ 28 - 1); Some (IMG, HIE - 2048)].
Abbreviation AX := (ZAdd (ZAdd (ZV 33) (ZL 4)) (ZMul (ZModP (ZAdd (ZV 35) (ZL 4294967295)) 32) (ZL 4))).
Abbreviation cl_kn0 := [KC (ZV 32) 56 8 (ZV 34); KC (ZV 34) 0 1 (ZL 0); KC (ZV 33) 0 2 (ZV 35); KC (ZV 32) 40 8 (ZV 34); KC (ZV 32) 48 8 (ZAdd (ZV 33) (ZL 2))].
Abbreviation cl_kn1 := [KC (ZV 32) 56 8 (ZV 34); KC (ZV 34) 0 1 (ZL 0); KC (ZV 33) 0 2 (ZV 35); KC (ZDivP AX 3) SHA 1 (ZL 0); KC AX 0 4 (ZV 36)].
(* [comment removed for export] *)
Abbreviation big := (Some (0, 18446744073709551615)).
Abbreviation ep_uvi := [Some (KHI + 656, HIE); big; big; big; big; big; big; big; big; big; big; big; big; big].
Abbreviation ep_kn := [KC (ZV 32) (-8) 8 (ZV 33); KC (ZV 32) (-16) 8 (ZV 34); KC (ZV 32) (-24) 8 (ZV 35); KC (ZV 32) (-32) 8 (ZV 36);
  KC (ZV 32) (-40) 8 (ZV 37); KC (ZV 32) (-48) 8 (ZV 38); KC (ZV 32) (-56) 8 (ZV 39); KC (ZV 32) (-64) 8 (ZV 40);
  KC (ZV 32) (-72) 8 (ZV 41); KC (ZV 32) (-80) 8 (ZV 42); KC (ZV 32) (-88) 8 (ZV 43); KC (ZV 32) (-96) 8 (ZV 44);
  KC (ZV 32) (-104) 8 (ZV 45)].

#[using="len GG Hds"] Lemma clampfin_A : forall regs m (l : list Z) (e : Z) (vs : list Z),
  getr regs 9%bv = Z_to_bv 64 sp1 -> getr regs 2%bv = Z_to_bv 64 sp1 -> getr regs 21%bv = Z_to_bv 64 o ->
  getr regs 27%bv = Z_to_bv 64 SHA -> getr regs 23%bv = Z_to_bv 64 F -> getr regs 25%bv = Z_to_bv 64 F -> getr regs 8%bv = Z_to_bv 64 sp ->
  getr regs 4%bv = Z_to_bv 64 TP_A ->
  bn_at SEGS_A m o (BN l e) -> ok l -> norm l -> zlen l <= 126 ->
  AMBs m -> SL1s m -> WINs m -> SAV sp m vs -> length vs = 13%nat -> (forall k, (k < 13)%nat -> 0 <= nth k vs 0 < 2 ^ 64) ->
  ret_ok (Z_to_bv 64 (nth 0 vs 0)) ->
  rt_ok m -> ro_ok SEGS_A RO_A m ->
  mem_u64 m (F + 2040) (FS + 35840 + p2) -> mem_def m (FS + 35840 + p2) 1 ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa434) m rom) (mkst regs' (Z_to_bv 64 (nth 0 vs 0)) m' rom)
    /\ bn_at SEGS_A m' o (clamp (BN l e))
    /\ getr regs' 2%bv = Z_to_bv 64 sp /\ rest13 regs' vs /\ keeps [3; 4] regs regs'
    /\ mem_byte m' (FS + 35840 + p2) 0
    /\ unch m m' [(o, o + 4); (sp1 - 16, sp1); (F, F + 8); (FS + 35840 + p2, FS + 35840 + p2 + 1); (G, G + 256)] /\ mem_grows m m'.
Proof.
  intros regs m l e vs R9 R2 R21 R27 R23 R25 R8 R4 Hbn Hok Hn Hlen AM L1 W SV Hvs Hvr Hret RT RO Hq Hdq.
  destruct AM as (SC & MC & TBL & TSH & OSH & DG & DSH). destruct L1 as (L240 & L72 & L32 & L40 & L56 & L48).
  destruct W as (Wsp & Wo & WF & WG). geom GG.
  destruct Hbn as (Cu & Ce & Carr & Hexr & H128). cbn [cells BnModel.ex] in *.
  pose proof (OSH 0 ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0. replace (SHA + o / 8) with (SHA + og) in SH0 by lia.
  unfold clamp. cbn [cells BnModel.ex]. rewrite (clamp_l_norm _ _ Hn).
  pose proof (zlen_nonneg l) as Hl0.
  (* [comment removed for export] *)
  assert (CL : exists regs1 m1,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa434) m rom) (mkst regs1 (Z_to_bv 64 0x5b8ac) m1 rom)
    /\ bn_at SEGS_A m1 o (BN l (match l with [] => 0 | _ => e end))
    /\ getr regs1 10%bv = Z_to_bv 64 F /\ getr regs1 1%bv = Z_to_bv 64 0x0aa4fc /\ getr regs1 2%bv = Z_to_bv 64 sp1
    /\ keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1
    /\ unch m m1 [(o, o + 4); (F, F + 8)] /\ mem_grows m m1).
  { destruct l as [|x t] eqn:El.
    - (* [comment removed for export] *)
      rewrite zlen_nil in Cu.
      zx_run SEGS_A constr:(CTX (vi_regs ++ cl_uvi 0 0) cl_kn0 [KW (ZV 33) 0 516; KW (ZV 37) 0 8]) 60%nat [0x5b8ac] (SCR [] [])
        constr:(cl_pins) [sp1; o; SHA + og; 0; 1; F] constr:(cl_uvi 0 0) regs m rom 0x0aa434.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L56; kc1 SH0; kc1 Cu; kc1 L40; kc1 L48; exact I) ltac:(kwd Wo; kwd WF; exact I)
        ltac:(idtac; zx_scs ltac:(flia)). zx_name regs1.
      eexists regs1, _. split; [exact ZM|].
      split; [|split; [zx_regv ZR|split; [zx_regv ZR|split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R2]|
             split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | clear ZM ZE ZR ZF; split; [unchx | growsx]]]]]].
      clear ZM ZE ZR ZF. unfold bn_at. cbn [cells BnModel.ex]. change (zlen (@nil Z)) with 0.
      split; [cellxf|]. split; [cellxf|]. split; [apply arr32_nil|]. lia.
    - (* [comment removed for export] *)
      rewrite <- El in *.
      assert (Hne : l <> []) by (rewrite El; congruence).
      assert (Hl1 : 1 <= zlen l) by (rewrite El, zlen_cons; pose proof (zlen_nonneg t); lia).
      remember (zlen l) as u eqn:Eu.
      assert (Htop : exists bs, rdn SEGS_A m (Z_to_bv 64 (o + 4 + 4 * (u - 1))) 4 = Some bs /\ bytes_le_to_Z bs = last l 0).
      { rewrite <- (last_nth l 0 Hne). eapply (kc_of_arr32_i _ _ _ _ (length l - 1)%nat); [exact Carr | unfold zlen in Eu; lia | unfold zlen in Eu; lia | reflexivity]. }
      assert (Htr : 1 <= last l 0 < B).
      { destruct Hn as [Hn'|Hn']; [congruence|]. rewrite <- (last_nth l 0 Hne) in Hn' |- *.
        pose proof (proj1 (Forall_nth _ _) Hok (length l - 1)%nat 0 ltac:(unfold zlen in Eu; lia)) as Hx. cbn beta in Hx. lia. }
      unfold B in Htr.
      pose proof (OSH ((4 * u) / 8) ltac:(lia)) as SHt.
      zx_run SEGS_A constr:(CTX (vi_regs ++ cl_uvi 1 126) cl_kn1 [KW (ZV 33) 0 516; KW (ZV 37) 0 8]) 60%nat [0x5b8ac] (SCR [] [])
        constr:(cl_pins) [sp1; o; SHA + og; u; last l 0; F] constr:(cl_uvi 1 126) regs m rom 0x0aa434.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L56; kc1 SH0; kc1 Cu; kc1 SHt; kc1 Htop; exact I) ltac:(kwd Wo; kwd WF; exact I)
        ltac:(idtac; zx_scs ltac:(flia)). zx_name regs1.
      eexists regs1, _. split; [exact ZM|].
      split; [|split; [zx_regv ZR|split; [zx_regv ZR|split; [etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R2]|
             split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | clear ZM ZE ZR ZF; split; [unchx | growsx]]]]]].
      clear ZM ZE ZR ZF. rewrite El. rewrite <- El. unfold bn_at. cbn [cells BnModel.ex]. rewrite <- Eu.
      split; [cellxf|]. split; [cellxf|]. split; [|lia].
      apply arr32_store_other; zwidth; unfold zlen in Eu; try flia. exact Carr. }
  destruct CL as (regs1 & m1 & M1 & Hbn1 & A10 & A1 & A2 & K1 & U01 & G01).
  (* [comment removed for export] *)
  destruct Gs1m as [q1 Hq1].
  assert (RT1 : rt_ok m1) by (eapply rt_ok_unch; [exact U01 | intros r Hr; unfold highr; inr Hr ltac:(slia) | exact RT]).
  assert (RO1 : ro_ok SEGS_A RO_A m1) by (eapply ro_ok_unchA; [exact U01 | intros r Hr; unfold highr; inr Hr ltac:(slia) | exact RO]).
  destruct (free5_A fx regs1 m1 rom (Z_to_bv 64 0x0aa4fc) sp1 F (FS + 35840 + p2)) as (regs2 & m2 & M2 & K2 & Hflag & _ & FR2).
  all: unfold app_mem, KHI_A, HIEND_A, IMGHI_A, LOSH_A, FREE5_FR, sh, SH_A.   (* [comment removed for export] *)
  { exact A1. } { vm_compute. reflexivity. } { exact A2. } { rewrite Hq1. lia. } { lia. } { lia. }
  { eapply mem_def_grows; [exact G01|]. eapply mem_def_sub; [exact Wsp | lia | lia]. }
  { exact A10. } { rewrite GgF. lia. } { lia. } { lia. } { lia. }
  { eapply mem_u64_unch; [exact U01 | lia | lia | intros r Hr; inr Hr ltac:(slia) | exact Hq]. }
  { lia. } { lia. } { lia. } { eapply mem_def_grows; [exact G01 | exact Hdq]. }
  { replace (2147450880 + F / 8) with g by lia. eapply mem_def_grows; [exact G01 | exact WG]. }
  { flia. } { lia. } { flia. } { lia. } { lia. }
  { exact RT1. } { exact RO1. }
  pose proof (unch_of_frame _ _ _ FR2) as U12. pose proof (grows_of_frame _ _ _ FR2) as G12.
  unfold sh, SH_A, FREE5_FR in U12. replace (2147450880 + F / 8) with g in U12 by lia.
  apply keeps_of_cs in K2.
  (* [comment removed for export] *)
  assert (SV2 : SAV sp m2 vs).
  { eapply SAVu; [exact U12 | rngs |]. eapply SAVu; [exact U01 | rngs | exact SV]. }
  destruct vs as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|v8 [|v9 [|v10 [|v11 [|v12 [|? ?]]]]]]]]]]]]]]; try (cbn in Hvs; discriminate).
  pose proof (Hvr 0%nat ltac:(lia)) as V0. pose proof (Hvr 1%nat ltac:(lia)) as V1. pose proof (Hvr 2%nat ltac:(lia)) as V2.
  pose proof (Hvr 3%nat ltac:(lia)) as V3. pose proof (Hvr 4%nat ltac:(lia)) as V4. pose proof (Hvr 5%nat ltac:(lia)) as V5.
  pose proof (Hvr 6%nat ltac:(lia)) as V6. pose proof (Hvr 7%nat ltac:(lia)) as V7. pose proof (Hvr 8%nat ltac:(lia)) as V8.
  pose proof (Hvr 9%nat ltac:(lia)) as V9. pose proof (Hvr 10%nat ltac:(lia)) as V10. pose proof (Hvr 11%nat ltac:(lia)) as V11.
  pose proof (Hvr 12%nat ltac:(lia)) as V12. cbn [nth] in *.
  pose proof (SV2 0%nat ltac:(lia)) as W0. pose proof (SV2 1%nat ltac:(lia)) as W1. pose proof (SV2 2%nat ltac:(lia)) as W2.
  pose proof (SV2 3%nat ltac:(lia)) as W3. pose proof (SV2 4%nat ltac:(lia)) as W4. pose proof (SV2 5%nat ltac:(lia)) as W5.
  pose proof (SV2 6%nat ltac:(lia)) as W6. pose proof (SV2 7%nat ltac:(lia)) as W7. pose proof (SV2 8%nat ltac:(lia)) as W8.
  pose proof (SV2 9%nat ltac:(lia)) as W9. pose proof (SV2 10%nat ltac:(lia)) as W10. pose proof (SV2 11%nat ltac:(lia)) as W11.
  pose proof (SV2 12%nat ltac:(lia)) as W12. cbn [nth Z.of_nat Z.mul Pos.mul Pos.of_succ_nat] in W0, W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, W12.
  assert (B8 : getr regs2 8%bv = Z_to_bv 64 sp) by (etransitivity; [exact (K2 8 ltac:(in_list)) | kept K1 8 R8]).
  zx_run SEGS_A constr:(CTX (vi_regs ++ ep_uvi) ep_kn (@nil kwin)) 30%nat [0x0aa548] (SCR [] []) constr:([(8%bv : reg, ZV 32)])
    [sp; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12] constr:(ep_uvi) regs2 m2 rom 0x0aa4fc.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
    ltac:(kc1 W0; kc1 W1; kc1 W2; kc1 W3; kc1 W4; kc1 W5; kc1 W6; kc1 W7; kc1 W8; kc1 W9; kc1 W10; kc1 W11; kc1 W12; exact I)
    ltac:(exact I) ltac:(exact I). zx_name regs3.
  assert (R1' : getr regs3 1%bv = Z_to_bv 64 v0) by (zx_regv ZR).
  eexists regs3, m2. split.
  { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact ZM|]. zx_ret SEGS_A; [exact R1' | exact Hret]. }
  split.
  { eapply bn_at_unch; [exact U12 | lia | cbn; lia | | exact Hbn1]. intros r Hr. inr Hr ltac:(slia). }
  split; [zx_regv ZR|].
  split; [unfold rest13; cbn [nth]; repeat split; zx_regv ZR|].
  split.
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  split; [exact Hflag|].
  split; [|eapply mem_grows_trans; [exact G01 | exact G12]].
  eapply unch_trans; [eapply unch_widen; [exact U01|] | eapply unch_widen; [exact U12|]];
    intros rg Hrg; cbn [fst snd];
    inr Hrg ltac:(first [ eexists; split; [left; reflexivity | cbn; lia]
                        | eexists; split; [right; left; reflexivity | cbn; lia]
                        | eexists; split; [right; right; left; reflexivity | cbn; lia]
                        | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
                        | eexists; split; [do 4 right; left; reflexivity | cbn; lia] ]).
Qed.

End S.
