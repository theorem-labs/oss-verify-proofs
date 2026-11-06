(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Abbreviation shlL_pins :=
  [(14%bv : reg, ZV 32); (11%bv : reg, ZV 33); (13%bv : reg, ZV 34); (15%bv : reg, ZV 35); (16%bv : reg, ZV 36)].
Abbreviation shlL_uvi :=
  [Some (0, 2 ^ 63); Some (0, 2 ^ 63); Some (0, 2 ^ 27); Some (0, 27); Some (1, 28); Some (0, 2 ^ 28 - 1)].
Abbreviation shlL_ctx := (CTX (vi_regs ++ shlL_uvi) [KC (ZV 32) 0 4 (ZV 37)] [KW (ZV 32) 0 4]).
Definition shlL_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Ltac obls ZXB Hcell Hst :=
  zx_use ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
    ltac:(kc1 Hcell; exact I)
    ltac:(kw1 Hst; exact I)
    ltac:(split; [lia | exact I]).

#[using="Type"] Lemma shl_loop_P : forall t done c regs m (A s : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 14%bv = Z_to_bv 64 p -> getr regs 11%bv = Z_to_bv 64 pend ->
  getr regs 13%bv = Z_to_bv 64 c -> getr regs 15%bv = Z_to_bv 64 s -> getr regs 16%bv = Z_to_bv 64 (28 - s) ->
  0 <= s < 28 -> 0 <= c < 2 ^ s -> ok t -> t <> [] ->
  0 <= A -> pend + 8 <= 2 ^ 63 ->
  arr32 SEGS_P m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x360dc) m rom) (mkst regs' (Z_to_bv 64 0x36100) m' rom)
    /\ arr32 SEGS_P m' A (done ++ fst (shl_l s c t))
    /\ getr regs' 13%bv = Z_to_bv 64 (snd (shl_l s c t))
    /\ getr regs' 11%bv = Z_to_bv 64 pend
    /\ keeps shlL_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A s p pend R14 R11 R13 R15 R16 Hs Hc Hok Hne HA Hpe Harr Hst; [congruence|].
  apply ok_cons in Hok as [Hx Hok]. cbn [length] in pend.
  assert (Hcell : exists bs, rdn SEGS_P m (Z_to_bv 64 p) 4 = Some bs /\ bytes_le_to_Z bs = x).
  { eapply kc_of_arr32; [exact Harr | unfold p; lia]. }
  pose proof (shl_step x c s Hx Hs Hc) as [Hdiv Hnc].
  cbn [shl_l]. destruct (shl_l s (x / 2 ^ (28 - s)) t) as [r c'] eqn:Hrec. cbn [fst snd].
  assert (Hs27 : 2 ^ s <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia).
  destruct t as [|y t'].
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(shlL_ctx) 20%nat (@nil Z) (SCR [false] []) constr:(shlL_pins) [p; pend; c; s; 28 - s; x] constr:(shlL_uvi) regs m rom 0x360dc.
    unfold p, pend in *. cbn [length] in *. obls ZXB Hcell Hst.
    
    cbn in Hrec. injection Hrec as <- <-.
    zx_reg ZR (13%bv : reg) as R13'. zx_reg ZR (11%bv : reg) as R11'.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [exact R13'|split; [rewrite R11'; f_equal; lia|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. unfold B. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(shlL_ctx) 20%nat (@nil Z) (SCR [true] []) constr:(shlL_pins) [p; pend; c; s; 28 - s; x] constr:(shlL_uvi) regs m rom 0x360dc.
    unfold p, pend in *. cbn [length] in *. obls ZXB Hcell Hst.
    
    zx_reg ZR (13%bv : reg) as R13'. zx_reg ZR (11%bv : reg) as R11'. zx_reg ZR (14%bv : reg) as R14'.
    zx_reg ZR (15%bv : reg) as R15'. zx_reg ZR (16%bv : reg) as R16'.
    set (m1 := wbytes m _ _) in ZM.
    assert (Harr1 : arr32 SEGS_P m1 A ((done ++ [(x * 2 ^ s + c) mod B]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold B. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia. }
    specialize (IH (done ++ [(x * 2 ^ s + c) mod B]) (x / 2 ^ (28 - s)) regs0 m1 A s).
    rewrite length_app in IH. cbn [length] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & R13'' & R11'' & K2 & U2 & G2).
    + rewrite R14'. f_equal. lia.
    + rewrite R11'. f_equal. lia.
    + exact R13'.
    + exact R15'.
    + exact R16'.
    + lia.
    + exact Hnc.
    + exact Hok.
    + congruence.
    + lia.
    + cbn [length]. lia.
    + exact Harr1.
    + (* [comment removed for export] *)
      unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply (store_ok_sub SEGS_P m (Z_to_bv 64 p)); try exact Hst;
        rewrite ?u_Z2bv64, ?Z.mod_small; cbn [length]; try lia.
    + rewrite Hrec in *. cbn [fst snd] in *.
      eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [rewrite <- app_assoc in Harr2; exact Harr2|].
      split; [exact R13''|]. split; [rewrite R11''; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shl_keep : list Z := CS.

#[using="Type"] Theorem shl_P : forall regs m (o n sp : Z) (ret : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 n -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0 <= n < 2048 -> bn_at SEGS_P m o b -> ok (cells b) -> zlen (cells b) <= 127 -> ex b + n / 28 < 2 ^ 15 ->
  16 <= sp -> sp <= 2 ^ 62 -> 0 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 16 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x36064) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_P m' o (shl n b)
    /\ unch m m' [(o, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o n sp ret b R10 R11 R2 R1 Hret Hn Hbn Hok Hlen Hex Hsp1 Hsp2 Ho1 Ho2 Hdisj Hsto Hsts.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  remember (cells b) as l eqn:El.
  destruct l as [|x t].
  - (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 2047); Some (16, 2 ^ 62); Some (0, 0)])
                              [KC (ZV 32) 0 2 (ZV 35)] [KW (ZV 34) (-16) 0])
      40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34)])
      [o; n; sp; 0] constr:([Some (0, 2 ^ 62); Some (0, 2047); Some (16, 2 ^ 62); Some (0, 0)]) regs m rom 0x36064.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 Cu; exact I)
      ltac:(kw1 Hsts; exact I)
      ltac:(zwidth; lia).
    assert (R1' : getr regs0 1%bv = ret).
    { zx_reg ZR (1%bv : reg) as H. rewrite H, <- R1. apply Z_to_bv_bv_unsigned. }
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|split; [unchx|growsx]].
    unfold shl. rewrite <- El. cbn [cells BnModel.ex]. unfold bn_at. rewrite <- El.
    split; [cellx|split; [cellx|split; [|split; [exact Hexr| unfold zlen; cbn; lia]]]].
    apply arr32_nil.
  - (* [comment removed for export] *)
    apply ok_cons in Hok as Hok0. destruct Hok0 as [Hx Hokt].
    assert (Hus : 1 <= zlen (x :: t) <= 127) by (rewrite zlen_cons in *; pose proof (zlen_nonneg t); lia).
    remember (zlen (x :: t)) as u eqn:Hu. unfold zlen in Hu. cbn [length] in Hu.
    (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 2047); Some (16, 2 ^ 62); Some (1, 127); Some (0, 2 ^ 15 - 1); None])
                              [KC (ZV 32) 0 2 (ZV 35); KC (ZV 32) 2 2 (ZV 36)] [KW (ZV 34) (-16) 0])
      40%nat [0x360a0] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34); (1%bv : reg, ZV 37)])
      [o; n; sp; u; ex b; bv_unsigned ret] constr:([Some (0, 2 ^ 62); Some (0, 2047); Some (16, 2 ^ 62); Some (1, 127); Some (0, 2 ^ 15 - 1); @None (Z * Z)]) regs m rom 0x36064.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 Cu; kc1 Ce; exact I)
      ltac:(kw1 Hsts; exact I)
      ltac:(zwidth; lia).
    zx_reg ZR (14%bv : reg) as A14. fold (magic28 n) in A14. rewrite (magic28_ok n) in A14 by lia.
    zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (13%bv : reg) as A13. zx_reg ZR (15%bv : reg) as A15.
    zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (2%bv : reg) as A2.
    set (m1 := wbytes m _ _) in ZM.
    assert (K1 : keeps CS' regs regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. rename ZM into M1. rename regs0 into regs1.
    (* [comment removed for export] *)
    zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (0, 2047); Some (16, 2 ^ 62); Some (1, 127); Some (0, 2 ^ 15 - 1); Some (0, 73)])
                              [] [KW (ZV 32) 0 516])
      40%nat [0x360dc] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-16)));
                                            (12%bv : reg, ZV 35); (13%bv : reg, ZV 35); (14%bv : reg, ZV 37); (15%bv : reg, ZV 36)])
      [o; n; sp; u; ex b; n / 28] constr:([Some (0, 2 ^ 62); Some (0, 2047); Some (16, 2 ^ 62); Some (1, 127); Some (0, 2 ^ 15 - 1); Some (0, 73)]) regs1 m1 rom 0x360a0.
    assert (Hsto1 : RiscvSemantics.store_ok SEGS_P m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [|exact Hsto]; unfold m1; growsx).
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto1; exact I) ltac:(exact I).
    zx_reg ZR (14%bv : reg) as B14. zx_reg ZR (11%bv : reg) as B11. zx_reg ZR (13%bv : reg) as B13.
    zx_reg ZR (15%bv : reg) as B15. zx_reg ZR (16%bv : reg) as B16. zx_reg ZR (12%bv : reg) as B12.
    zx_reg ZR (10%bv : reg) as B10. zx_reg ZR (2%bv : reg) as B2.
    set (m2 := wbytes m1 _ _) in ZM.
    assert (K2 : keeps CS' regs1 regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. rename ZM into M2. rename regs0 into regs2.
    (* [comment removed for export] *)
    assert (Hs : 0 <= n mod 28 < 28) by lia.
    assert (Harr2 : arr32 SEGS_P m2 (o + 4) ([] ++ x :: t)).
    { cbn [app]. unfold m2, m1. apply arr32_store_other; zwidth; try lia.
      apply arr32_store_other; zwidth; try lia. exact Carr. }
    destruct (shl_loop_P (x :: t) [] 0 regs2 m2 (o + 4) (n mod 28)) as (regs3 & m3 & M3 & Harr3 & C13 & C11 & K3 & U3 & G3);
      cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
    { rewrite B14; first [reflexivity | f_equal; lia]. }
    { rewrite B11; first [reflexivity | f_equal; lia]. }
    { exact B13. }
    { rewrite B15; first [reflexivity | f_equal; lia]. }
    { rewrite B16; first [reflexivity | f_equal; lia]. }
    { exact Hs. }
    { split; [lia|]. apply Z.pow_pos_nonneg; lia. }
    { exact Hok. }
    { congruence. }
    { lia. }
    { lia. }
    { exact Harr2. }
    { eapply sc_store_in; [eapply store_ok_grows; [|exact Hsto1]; unfold m2; growsx |]. cbn [length]. lia. }
    cbn [length app] in Harr3, C11, U3. rewrite ?Z.mul_0_r, ?Z.add_0_r in C11, U3.
    pose proof (shl_l_spec (n mod 28) (x :: t) 0 Hok Hs ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as SPEC.
    destruct (shl_l (n mod 28) 0 (x :: t)) as [r c'] eqn:Eshl. cbn [fst snd] in Harr3, C13.
    destruct SPEC as (_ & Hokr & Hlenr & Hc').
    assert (Hc'27 : c' < 2 ^ 27) by (assert (2 ^ (n mod 28) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia); lia).
    assert (Hlenr' : Z.of_nat (length r) = u) by (unfold zlen in Hlenr; cbn [length] in Hlenr; lia).
    (* [comment removed for export] *)
    assert (C12 : getr regs3 12%bv = Z_to_bv 64 u) by (etransitivity; [exact (K3 12 ltac:(cbn; tauto)) | exact B12]).
    assert (C10 : getr regs3 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K3 10 ltac:(cbn; tauto)) | exact B10]).
    assert (C2 : getr regs3 2%bv = Z_to_bv 64 (sp + -16)) by (etransitivity; [exact (K3 2 ltac:(cbn; tauto)) | exact B2]).
    assert (RA3 : cellN SEGS_P m3 (sp + -8) 8 (bv_unsigned ret)).
    { eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      unfold m2, m1. pose proof (u64_range ret). cellx. }
    assert (Hsto3 : RiscvSemantics.store_ok SEGS_P m3 (Z_to_bv 64 o) 516 = true).
    { eapply store_ok_grows; [exact G3|]. eapply store_ok_grows; [|exact Hsto1]. unfold m2; growsx. }
    assert (Hsts3 : RiscvSemantics.store_ok SEGS_P m3 (Z_to_bv 64 (sp - 16)) 16 = true).
    { eapply store_ok_grows; [exact G3|]. eapply store_ok_grows; [|exact Hsts]. unfold m2, m1; growsx. }
    (* [comment removed for export] *)
    assert (EXC : forall m', unch m3 m' [(o, o + 2); (o + 4 + 4 * u, o + 8 + 4 * u)] -> cellN SEGS_P m' (o + 2) 2 (ex b + n / 28)).
    { intros m' U. eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia |].
      eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      unfold m2. cellx. }
    assert (UNCH : forall m', unch m3 m' [(o, o + 516)] -> unch m m' [(o, o + 516); (sp - 16, sp)]).
    { intros m' U. apply (unch_trans m m3 m'); [|eapply unch_widen; [exact U|]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; eexists; split; [left; reflexivity|cbn; lia]].
      apply (unch_trans m m2 m3); [unfold m2, m1; unchx|].
      eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|cbn; lia]. }
    assert (KEEPS : forall regs4, keeps CS' regs3 regs4 -> getr regs4 2%bv = Z_to_bv 64 sp -> keeps CS regs regs4).
    { intros regs4 K4 S4. apply keeps_CS_of; [|rewrite S4, R2; reflexivity].
      eapply keeps_trans; [exact K1|]. eapply keeps_trans; [exact K2|]. eapply keeps_trans; [|exact K4].
      eapply keeps_sub_dec; [exact K3|]. vm_compute. reflexivity. }
    unfold shl. rewrite <- El, Eshl. unfold bn_at. cbn [cells BnModel.ex].
    destruct (Z.eqb_spec c' 0) as [Hc0|Hc0].
    + (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (16, 2 ^ 62); Some (1, 127); Some (0, 0); None]) [KC (ZV 33) (-8) 8 (ZV 36)] [])
        40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-16))); (12%bv : reg, ZV 34); (13%bv : reg, ZV 35)])
        [o; sp; u; c'; bv_unsigned ret] constr:([Some (0, 2 ^ 62); Some (16, 2 ^ 62); Some (1, 127); Some (0, 0); @None (Z*Z)]) regs3 m3 rom 0x36100.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA3; exact I) ltac:(exact I) ltac:(exact I).
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (2%bv : reg) as D2.
      eexists regs0, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3|];
                                eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [apply KEEPS; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | rewrite D2; f_equal; lia]|].
      split; [|split; [apply UNCH; apply unch_refl | apply (mem_grows_trans m m2 m3); [unfold m2, m1; growsx | exact G3]]].
      split; [|split; [apply EXC; apply unch_refl|split; [exact Harr3|split; [lia| unfold zlen; rewrite Hlenr'; lia]]]].
      unfold zlen; rewrite Hlenr'.
      eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      unfold m2, m1. cellx.
    + (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (16, 2 ^ 62); Some (1, 127); Some (1, 2 ^ 27); None; Some (0, 2 ^ 62)]) [KC (ZV 33) (-8) 8 (ZV 36)] [])
        40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-16))); (12%bv : reg, ZV 34); (13%bv : reg, ZV 35); (11%bv : reg, ZV 37)])
        [o; sp; u; c'; bv_unsigned ret; o + 4 + 4 * u] constr:([Some (0, 2 ^ 62); Some (16, 2 ^ 62); Some (1, 127); Some (1, 2 ^ 27); @None (Z*Z); Some (0, 2 ^ 62)]) regs3 m3 rom 0x36100.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA3; exact I) ltac:(exact I)
        ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto3 | zwidth; lia])).
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (2%bv : reg) as D2.
      eexists regs0, _. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3|];
                               eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [apply KEEPS; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | rewrite D2; f_equal; lia]|].
      split; [|split; [apply UNCH; unchx | eapply mem_grows_trans; [apply (mem_grows_trans m m2 m3); [unfold m2, m1; growsx | exact G3] | growsx]]].
      rewrite zlen_app. unfold zlen. cbn [length]. rewrite Hlenr'.
      split; [cellx|split; [apply EXC; unchx|split; [|lia]]].
      apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
      replace (o + 4 + 4 * u) with (o + 4 + 4 * Z.of_nat (length r)) by lia.
      apply arr32_snoc'; try lia. exact Harr3.
      rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.
End S.
