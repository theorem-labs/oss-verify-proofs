(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnP_mul2 BnP_mul3 BnCbdLib BnP_cbd.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition CSY : list Z := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma cbd_p2tail_P : forall (p : Z) regs m (S e a4 : Z),
  (p = 0x35374 \/ p = 0x35390) ->
  getr regs 2%bv = Z_to_bv 64 (S - 1072) -> getr regs 8%bv = Z_to_bv 64 a4 ->
  a4 mod 2 ^ 32 = e mod 2 ^ 32 -> -2047 <= e <= 2047 -> 82456 <= S -> S < 2 ^ 62 ->
  exists regs',
    msteps SEGS_P (mkst regs (Z_to_bv 64 p) m rom) (mkst regs' (Z_to_bv 64 0x36064) m rom)
    /\ getr regs' 10%bv = Z_to_bv 64 (if 0 <? e then S - 1064 else S - 548)
    /\ getr regs' 11%bv = Z_to_bv 64 (if 0 <? e then e else - e)
    /\ getr regs' 1%bv = Z_to_bv 64 0x353a4 /\ getr regs' 2%bv = Z_to_bv 64 (S - 1072)
    /\ keeps CSY regs regs'.
Proof.
  intros p regs m S e a4 Hp R2 R8 Ha4 He HS1 HS2.
  pose proof (swrap32_low' a4 e Ha4 ltac:(lia)) as SW. pose proof (swrap32_neg_low' a4 e Ha4 ltac:(lia)) as SWN.
  destruct Hp as [-> | ->]; destruct (Z_lt_dec 0 e) as [Hpos | Hneg].
  - zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); None]) (@nil kcell) (@nil kwin)) 20%nat [0x36064] (SCR [false] [])
      constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (8%bv : reg, ZV 33)]) [S; a4] constr:([Some (82456, 2 ^ 62); @None (Z * Z)]) regs m rom 0x35374.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(rewrite ?SW, ?SWN; zx_lia). zx_name regs1.
    exists regs1. split; [exact ZM|]. replace (0 <? e) with true by (symmetry; apply Z.ltb_lt; lia).
    split; [zx_regv ZR|]. split; [zx_regv ZR; rewrite ?SW, ?SWN; reflexivity|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); None]) (@nil kcell) (@nil kwin)) 20%nat [0x36064] (SCR [true] [])
      constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (8%bv : reg, ZV 33)]) [S; a4] constr:([Some (82456, 2 ^ 62); @None (Z * Z)]) regs m rom 0x35374.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(rewrite ?SW, ?SWN; zx_lia). zx_name regs1.
    exists regs1. split; [exact ZM|]. replace (0 <? e) with false by (symmetry; apply Z.ltb_ge; lia).
    split; [zx_regv ZR|]. split; [zx_regv ZR; rewrite ?SW, ?SWN; reflexivity|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); None]) (@nil kcell) (@nil kwin)) 20%nat [0x36064] (SCR [true] [])
      constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (8%bv : reg, ZV 33)]) [S; a4] constr:([Some (82456, 2 ^ 62); @None (Z * Z)]) regs m rom 0x35390.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(rewrite ?SW, ?SWN; zx_lia). zx_name regs1.
    exists regs1. split; [exact ZM|]. replace (0 <? e) with true by (symmetry; apply Z.ltb_lt; lia).
    split; [zx_regv ZR|]. split; [zx_regv ZR; rewrite ?SW, ?SWN; reflexivity|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
  - zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); None]) (@nil kcell) (@nil kwin)) 20%nat [0x36064] (SCR [false] [])
      constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (8%bv : reg, ZV 33)]) [S; a4] constr:([Some (82456, 2 ^ 62); @None (Z * Z)]) regs m rom 0x35390.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(rewrite ?SW, ?SWN; zx_lia). zx_name regs1.
    exists regs1. split; [exact ZM|]. replace (0 <? e) with false by (symmetry; apply Z.ltb_ge; lia).
    split; [zx_regv ZR|]. split; [zx_regv ZR; rewrite ?SW, ?SWN; reflexivity|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
Qed.

#[using="Type"] Lemma cbd_p2_P : forall regs m (S expo e a4 : Z) (A Bb : bn),
  getr regs 2%bv = Z_to_bv 64 (S - 1072) -> getr regs 8%bv = Z_to_bv 64 a4 -> getr regs 9%bv = Z_to_bv 64 expo ->
  a4 mod 2 ^ 32 = e mod 2 ^ 32 -> -2047 <= e <= 2047 -> -1103 <= expo <= 308 ->
  bn_at SEGS_P m (S - 548) A -> bn_at SEGS_P m (S - 1064) Bb ->
  ok (cells A) -> norm (cells A) -> ok (cells Bb) -> norm (cells Bb) -> ex A = 0 -> ex Bb = 0 ->
  (0 <= expo -> val (cells A) * 5 ^ expo < B ^ 124) -> (expo < 0 -> val (cells Bb) * 5 ^ (- expo) < B ^ 124) ->
  arr32 SEGS_P m 80520 five_tbl -> 82456 <= S -> S < 2 ^ 62 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 (S - 1888)) 1888 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35364) m rom) (mkst regs' (Z_to_bv 64 0x36064) m' rom)
    /\ bn_at SEGS_P m' (S - 548) (if 0 <=? expo then mulpow10 expo A else A)
    /\ bn_at SEGS_P m' (S - 1064) (if 0 <=? expo then Bb else mulpow10 (- expo) Bb)
    /\ getr regs' 10%bv = Z_to_bv 64 (if 0 <? e then S - 1064 else S - 548)
    /\ getr regs' 11%bv = Z_to_bv 64 (if 0 <? e then e else - e)
    /\ getr regs' 1%bv = Z_to_bv 64 0x353a4 /\ getr regs' 2%bv = Z_to_bv 64 (S - 1072)
    /\ keeps CSY regs regs'
    /\ arr32 SEGS_P m' 80520 five_tbl
    /\ unch m m' [(S - 1064, S - 32); (S - 1088, S - 1072)] /\ mem_grows m m'.
Proof.
  intros regs m S expo e a4 A Bb R2 R8 R9 Ha4 He Hexpo HbA HbB HokA HnA HokB HnB HexA HexB HvA HvB Htbl HS1 HS2 Hsto.
  pose proof (swrap64_small expo ltac:(lia)) as SW64. pose proof (swrap32_small (0 - expo) ltac:(lia)) as SW32.
  destruct (Z_le_dec 0 expo) as [Hp | Hn].
  - (* [comment removed for export] *)
    replace (0 <=? expo) with true by (symmetry; apply Z.leb_le; lia).
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); None]) (@nil kcell) (@nil kwin)) 20%nat [0x35b04; 0x36064] (SCR [false] [])
      constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (9%bv : reg, ZV 33)]) [S; expo] constr:([Some (82456, 2 ^ 62); @None (Z * Z)]) regs m rom 0x35364.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(rewrite ?SW64; zx_lia). zx_name regs1.
    zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (1%bv : reg) as A1. zx_reg ZR (2%bv : reg) as A2.
    assert (A8 : getr regs1 8%bv = Z_to_bv 64 a4) by (etransitivity; [exact (reg_kept _ _ _ _ (8%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R8]).
    assert (K1 : keeps CSY regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    rename ZM into M1. clear ZE ZR ZF.
    assert (Hret1 : ret_ok (Z_to_bv 64 0x35374)) by (apply ret_ok_even; reflexivity).
    destruct (mulpow10_P rom regs1 m (S - 548) expo (S - 1072) (Z_to_bv 64 0x35374) A) as (regs2 & m2 & M2 & K2 & Hbn2 & Htbl2 & U2 & G2).
    { regeq A10. } { exact A11. } { regeq A2. } { exact A1. } { exact Hret1. } { lia. } { exact HbA. } { exact HokA. } { exact HnA. }
    { apply HvA. lia. } { rewrite HexA. pose proof (Z.div_pos expo 28). assert (expo / 28 <= 11) by lia. lia. } { exact Htbl. }
    { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
    { eapply sc_store_in; [exact Hsto | cbn; lia]. } { eapply sc_store_in; [exact Hsto | cbn; lia]. }
    destruct (cbd_p2tail_P 0x35374 regs2 m2 S e a4 ltac:(left; reflexivity)) as (regs3 & M3 & C10 & C11 & C1 & C2 & K3).
    { etransitivity; [exact (K2 2 ltac:(cbn; tauto)) | regeq A2]. } { etransitivity; [exact (K2 8 ltac:(cbn; tauto)) | exact A8]. }
    { exact Ha4. } { exact He. } { exact HS1. } { exact HS2. }
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact M3]|].
    split; [exact Hbn2|].
    split; [eapply bn_at_unch; [exact U2 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact HbB]|].
    split; [exact C10|]. split; [exact C11|]. split; [exact C1|]. split; [exact C2|].
    split; [eapply keeps_trans; [exact K1|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity | exact K3]|].
    split; [exact Htbl2|]. split; [|exact G2].
    eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [right; left; reflexivity|cbn; lia]].
  - (* [comment removed for export] *)
    replace (0 <=? expo) with false by (symmetry; apply Z.leb_gt; lia).
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); None]) (@nil kcell) (@nil kwin)) 20%nat [0x35b04; 0x36064] (SCR [true] [])
      constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (9%bv : reg, ZV 33)]) [S; expo] constr:([Some (82456, 2 ^ 62); @None (Z * Z)]) regs m rom 0x35364.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(rewrite ?SW64; zx_lia). zx_name regs1.
    zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (1%bv : reg) as A1. zx_reg ZR (2%bv : reg) as A2.
    rewrite ?SW32 in A11.
    assert (A8 : getr regs1 8%bv = Z_to_bv 64 a4) by (etransitivity; [exact (reg_kept _ _ _ _ (8%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R8]).
    assert (K1 : keeps CSY regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    rename ZM into M1. clear ZE ZR ZF.
    assert (Hret1 : ret_ok (Z_to_bv 64 0x35390)) by (apply ret_ok_even; reflexivity).
    destruct (mulpow10_P rom regs1 m (S - 1064) (- expo) (S - 1072) (Z_to_bv 64 0x35390) Bb) as (regs2 & m2 & M2 & K2 & Hbn2 & Htbl2 & U2 & G2).
    { regeq A10. } { regeq A11. } { regeq A2. } { exact A1. } { exact Hret1. } { lia. } { exact HbB. } { exact HokB. } { exact HnB. }
    { apply HvB. lia. } { rewrite HexB. pose proof (Z.div_pos (- expo) 28). assert (- expo / 28 <= 40) by lia. lia. } { exact Htbl. }
    { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
    { eapply sc_store_in; [exact Hsto | cbn; lia]. } { eapply sc_store_in; [exact Hsto | cbn; lia]. }
    destruct (cbd_p2tail_P 0x35390 regs2 m2 S e a4 ltac:(right; reflexivity)) as (regs3 & M3 & C10 & C11 & C1 & C2 & K3).
    { etransitivity; [exact (K2 2 ltac:(cbn; tauto)) | regeq A2]. } { etransitivity; [exact (K2 8 ltac:(cbn; tauto)) | exact A8]. }
    { exact Ha4. } { exact He. } { exact HS1. } { exact HS2. }
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact M3]|].
    split; [eapply bn_at_unch; [exact U2 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact HbA]|].
    split; [exact Hbn2|].
    split; [exact C10|]. split; [exact C11|]. split; [exact C1|]. split; [exact C2|].
    split; [eapply keeps_trans; [exact K1|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity | exact K3]|].
    split; [exact Htbl2|]. split; [|exact G2].
    eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [right; left; reflexivity|cbn; lia]].
Qed.

End S.
