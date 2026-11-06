(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnContract BnP_mul2 BnP_ads2 BnP_shl BnP_cmp BnCbdLib BnP_cbd BnP_cbd2.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

#[using="Type"] Lemma cbd_p3_P : forall regs m (S e : Z) (ret s0v s1v s2v : word) (A1 B1 : bn),
  getr regs 10%bv = Z_to_bv 64 (if 0 <? e then S - 1064 else S - 548) ->
  getr regs 11%bv = Z_to_bv 64 (if 0 <? e then e else - e) ->
  getr regs 1%bv = Z_to_bv 64 0x353a4 -> getr regs 2%bv = Z_to_bv 64 (S - 1072) ->
  -2047 <= e <= 2047 ->
  bn_at SEGS_P m (S - 548) A1 -> bn_at SEGS_P m (S - 1064) B1 ->
  ok (cells A1) -> ok (cells B1) -> zlen (cells A1) <= 124 -> zlen (cells B1) <= 124 -> 0 <= ex A1 <= 12 -> 0 <= ex B1 <= 40 ->
  cellN SEGS_P m (S - 8) 8 (bv_unsigned ret) -> cellN SEGS_P m (S - 16) 8 (bv_unsigned s0v) ->
  cellN SEGS_P m (S - 24) 8 (bv_unsigned s1v) -> cellN SEGS_P m (S - 32) 8 (bv_unsigned s2v) -> ret_ok ret ->
  82456 <= S -> S < 2 ^ 62 ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 (S - 1888)) 1888 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x36064) m rom) (mkst regs' ret m' rom)
    /\ getr regs' 10%bv = Z_to_bv 64 (compare (if 0 <? e then A1 else shl (- e) A1) (if 0 <? e then shl e B1 else B1))
    /\ getr regs' 2%bv = Z_to_bv 64 S /\ getr regs' 8%bv = s0v /\ getr regs' 9%bv = s1v /\ getr regs' 18%bv = s2v
    /\ keeps CSX regs regs'
    /\ unch m m' [(S - 1064, S - 32); (S - 1088, S - 1072)] /\ mem_grows m m'.
Proof.
  intros regs m S e ret s0v s1v s2v A1 B1 R10 R11 R1 R2 He HbA HbB HokA HokB HlA HlB HexA HexB C1 C2 C3 C4 Hret HS1 HS2 Hsto.
  pose proof (u64_range ret) as W1. pose proof (u64_range s0v) as W2. pose proof (u64_range s1v) as W3. pose proof (u64_range s2v) as W4.
  assert (HretS : ret_ok (Z_to_bv 64 0x353a4)) by (apply ret_ok_even; reflexivity).
  (* [comment removed for export] *)
  assert (SH : exists regs2 m2,
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x36064) m rom) (mkst regs2 (Z_to_bv 64 0x353a4) m2 rom)
    /\ keeps CS regs regs2
    /\ bn_at SEGS_P m2 (S - 548) (if 0 <? e then A1 else shl (- e) A1)
    /\ bn_at SEGS_P m2 (S - 1064) (if 0 <? e then shl e B1 else B1)
    /\ unch m m2 [(S - 1064, S - 32); (S - 1088, S - 1072)] /\ mem_grows m m2).
  { destruct (Z.ltb_spec 0 e) as [Hp|Hn].
    - destruct (shl_P rom regs m (S - 1064) e (S - 1072) (Z_to_bv 64 0x353a4) B1 R10 R11 R2 R1 HretS) as (regs2 & m2 & M2 & K2 & Hbn2 & U2 & G2).
      { lia. } { exact HbB. } { exact HokB. } { lia. } { pose proof (Z.div_pos e 28). assert (e / 28 <= 73) by lia. lia. }
      { lia. } { lia. } { lia. } { lia. } { lia. }
      { eapply sc_store_in; [exact Hsto | cbn; lia]. } { eapply sc_store_in; [exact Hsto | cbn; lia]. }
      eexists regs2, m2. split; [exact M2|]. split; [exact K2|].
      split; [eapply bn_at_unch; [exact U2 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact HbA]|].
      split; [exact Hbn2|]. split; [|exact G2].
      eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [right; left; reflexivity|cbn; lia]].
    - destruct (shl_P rom regs m (S - 548) (- e) (S - 1072) (Z_to_bv 64 0x353a4) A1 R10 R11 R2 R1 HretS) as (regs2 & m2 & M2 & K2 & Hbn2 & U2 & G2).
      { lia. } { exact HbA. } { exact HokA. } { lia. } { pose proof (Z.div_pos (- e) 28). assert (- e / 28 <= 73) by lia. lia. }
      { lia. } { lia. } { lia. } { lia. } { lia. }
      { eapply sc_store_in; [exact Hsto | cbn; lia]. } { eapply sc_store_in; [exact Hsto | cbn; lia]. }
      eexists regs2, m2. split; [exact M2|]. split; [exact K2|].
      split; [exact Hbn2|].
      split; [eapply bn_at_unch; [exact U2 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact HbB]|].
      split; [|exact G2].
      eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [right; left; reflexivity|cbn; lia]]. }
  destruct SH as (regs2 & m2 & M2 & K2 & HbA2 & HbB2 & U2 & G2).
  assert (B2 : getr regs2 2%bv = Z_to_bv 64 (S - 1072)) by (etransitivity; [exact (K2 2 ltac:(cbn; tauto)) | exact R2]).
  (* [comment removed for export] *)
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62)]) (@nil kcell) (@nil kwin)) 10%nat [0x36120] (SCR [] [])
    constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072)))]) [S] constr:([Some (82456, 2 ^ 62)]) regs2 m2 rom 0x353a4.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
  zx_reg ZR (10%bv : reg) as D10. zx_reg ZR (11%bv : reg) as D11. zx_reg ZR (1%bv : reg) as D1.
  assert (K3 : keeps CS regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M3. clear ZE ZR ZF.
  assert (HretC : ret_ok (Z_to_bv 64 0x353b0)) by (apply ret_ok_even; reflexivity).
  destruct (cmp_P rom regs3 m2 (S - 548) (S - 1064) (Z_to_bv 64 0x353b0) _ _ ltac:(regeq D10) ltac:(regeq D11) D1 HretC HbA2 HbB2)
    as (regs4 & M4 & K4 & Hres).
  { destruct (0 <? e); [exact HokA | apply shl_ok_any; exact HokA]. }
  { destruct (0 <? e); [apply shl_ok_any; exact HokB | exact HokB]. }
  { lia. } { lia. } { lia. } { lia. }
  (* [comment removed for export] *)
  assert (SAV : forall a v, cellN SEGS_P m a 8 v -> S - 32 <= a -> a + 8 <= S -> cellN SEGS_P m2 a 8 v).
  { intros a v C Ha1 Ha2. eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact C]. }
  pose proof (SAV _ _ C1 ltac:(lia) ltac:(lia)) as C1'. pose proof (SAV _ _ C2 ltac:(lia) ltac:(lia)) as C2'.
  pose proof (SAV _ _ C3 ltac:(lia) ltac:(lia)) as C3'. pose proof (SAV _ _ C4 ltac:(lia) ltac:(lia)) as C4'.
  assert (E2 : getr regs4 2%bv = Z_to_bv 64 (S - 1072)).
  { etransitivity; [exact (K4 2 ltac:(cbn; tauto)) |]. etransitivity; [exact (K3 2 ltac:(cbn; tauto)) | exact B2]. }
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                          [KC (ZV 32) (-8) 8 (ZV 33); KC (ZV 32) (-16) 8 (ZV 34); KC (ZV 32) (-24) 8 (ZV 35); KC (ZV 32) (-32) 8 (ZV 36)] (@nil kwin))
    10%nat [0x353c4] (SCR [] []) constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072)))])
    [S; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v]
    constr:([Some (82456, 2 ^ 62); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs4 m2 rom 0x353b0.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 C1'; kc1 C2'; kc1 C3'; kc1 C4'; exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
  assert (R1' : getr regs5 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned).
  eexists regs5, m2. split.
  { eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact ZM|].
    zx_ret SEGS_P; [exact R1' | exact Hret]. }
  split; [etransitivity; [exact (reg_kept _ _ _ _ (10%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact Hres]|].
  split; [zx_regv ZR|].
  split; [zx_reg ZR (8%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (9%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split; [zx_reg ZR (18%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
  split.
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  split; [exact U2 | exact G2].
Qed.

End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem cbd_P : cbd_stmt_P.
Proof.
  unfold cbd_stmt_P, cbd_stmt. intros fx regs m rom S buf len expo e a4 ret f.
  intros R1 Hret4 R2 Hsp16 HFR HS62 R10 Hbuf0 Hbuflen R11 R12 R13 R14 Ha4 Hlen Hle He Hdig Hsto Hdisj Htblsp Hro.
  unfold CBD_ENTRY_P, CBD_FR_P, CBD_TBL_LO, CBD_TBL_HI in *.
  change (Z.to_nat 1888) with 1888%nat in Hsto.
  (* [comment removed for export] *)
  pose proof (dsof_spec SEGS_P m buf len ltac:(lia) Hdig) as DS. cbn zeta in DS. destruct DS as (Hzl & Hdok & Hdigs).
  set (ds := dsof SEGS_P m buf (Z.to_nat len)) in *.
  (* [comment removed for export] *)
  assert (Htbl : arr32 SEGS_P m 80520 five_tbl).
  { unfold five_tbl. apply arr32_rom; [lia | cbn; lia | | apply five_tbl_P0]. intros x b Hx Hm. apply (Hro x b); [cbn in Hx; lia | exact Hm]. }
  (* [comment removed for export] *)
  pose proof (u64_range f) as Wf.
  pose proof (cbd_facts ds len expo (bv_unsigned f) e Hdok Hzl ltac:(lia) ltac:(lia) ltac:(lia) He) as CF. cbn zeta in CF.
  destruct CF as ((Aok & An & Aex & Av) & (Bok & Bn & Bex & Bv) & (A1ok & A1n & A1l & A1x) & (B1ok & B1n & B1l & B1x) & _ & _).
  assert (Hret : ret_ok ret) by (apply ret_ok_even; lia).
  (* [comment removed for export] *)
  destruct (cbd_p1_P rom regs m S buf len expo a4 ret f ds R2 R10 R11 R12 R13 R14 R1 Hzl ltac:(lia) Hdok Hdigs Htbl
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsto)
    as (regs1 & m1 & M1 & HbA & HbB & A2 & A8 & A9 & K1 & C1 & C2 & C3 & C4 & Htbl1 & U1 & G1).
  assert (Hsto1 : RiscvSemantics.store_ok SEGS_P m1 (Z_to_bv 64 (S - 1888)) 1888 = true) by (eapply store_ok_grows; [exact G1 | exact Hsto]).
  (* [comment removed for export] *)
  destruct (cbd_p2_P rom regs1 m1 S expo e a4 (assign_decimal ds) (assign_u64 (bv_unsigned f)) A2 A8 A9 Ha4 He ltac:(lia)
             HbA HbB Aok An Bok Bn Aex Bex Av Bv Htbl1 ltac:(lia) ltac:(lia) Hsto1)
    as (regs2 & m2 & M2 & HbA2 & HbB2 & D10 & D11 & D1 & D2 & K2 & Htbl2 & U2 & G2).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_P m2 (Z_to_bv 64 (S - 1888)) 1888 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto1]).
  assert (SAV : forall a v, cellN SEGS_P m1 a 8 v -> S - 32 <= a -> a + 8 <= S -> cellN SEGS_P m2 a 8 v).
  { intros a v C Ha1 Ha2. eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact C]. }
  (* [comment removed for export] *)
  destruct (cbd_p3_P rom regs2 m2 S e ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) _ _ D10 D11 D1 D2 He HbA2 HbB2
             A1ok B1ok A1l B1l A1x B1x
             ltac:(apply SAV; [exact C1 | lia | lia]) ltac:(apply SAV; [exact C2 | lia | lia])
             ltac:(apply SAV; [exact C3 | lia | lia]) ltac:(apply SAV; [exact C4 | lia | lia]) Hret ltac:(lia) ltac:(lia) Hsto2)
    as (regs3 & m3 & M3 & Hres & F2 & F8 & F9 & F18 & K3 & U3 & G3).
  exists regs3, m3.
  split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact M3]|].
  split.
  { intros rg Hrg. cbn in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ etransitivity; [exact F2 | symmetry; exact R2] | exact F8 | exact F9 | exact F18
            | lazymatch goal with |- getr _ (Z_to_bv 5 ?nn) = _ =>
                etransitivity; [exact (K3 nn ltac:(cbn; tauto))|]; etransitivity; [exact (K2 nn ltac:(cbn; tauto))|]; exact (K1 nn ltac:(cbn; tauto)) end ]. }
  split.
  { eexists. split; [exact Hres | apply compare_range]. }
  split.
  - intros a Ha.
    assert (U : unch m m3 [(S - 1888, S)]).
    { eapply unch_trans; [exact U1|]. eapply unch_trans; (eapply unch_widen; [eassumption|]);
        intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
    apply U. intros (r & Hr & Hin). cbn in Hr. destruct Hr as [<-|[]]. cbn in Hin. lia.
  - intros a b Hm. assert (G : mem_grows m m3) by (eapply mem_grows_trans; [exact G1|]; eapply mem_grows_trans; [exact G2 | exact G3]).
    specialize (G a). destruct (m3 a) as [b'|]; [exists b'; reflexivity|]. exfalso. apply G; congruence.
Qed.
