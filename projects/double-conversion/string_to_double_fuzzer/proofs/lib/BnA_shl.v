(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition magic28A (n : Z) : Z :=
  bv_swrap 32 ((n * 18446744071868851347) mod 2 ^ 64 / 2 ^ 32 + n) / 2 ^ 4
  + ((n * 18446744071868851347) mod 2 ^ 64 / 2 ^ 32 + n) mod 2 ^ 32 / 2 ^ 31.

Lemma magic28A_table : forallb (fun k => magic28A (Z.of_nat k) =? Z.of_nat k / 28) (seq 0 2048) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma magic28A_ok : forall n, 0 <= n < 2048 -> magic28A n = n / 28.
Proof.
  intros n Hn.
  pose proof (proj1 (forallb_forall _ _) magic28A_table (Z.to_nat n)) as H. cbn beta in H.
  replace (Z.of_nat (Z.to_nat n)) with n in H by lia.
  apply Z.eqb_eq, H. apply in_seq. lia.
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Abbreviation shlL_pins :=
  [(11%bv : reg, ZV 32); (6%bv : reg, ZV 32); (7%bv : reg, ZV 33); (17%bv : reg, ZV 34); (16%bv : reg, ZV 35);
   (5%bv : reg, ZV 36); (15%bv : reg, ZL SHA)].
Abbreviation shlL_uvi clo chi :=
  [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 27); Some (0, 27); Some (1, 28); Some (0, 2 ^ 28 - 1)].
Abbreviation shlL_ctx clo chi :=
  (CTX (vi_regs ++ shlL_uvi clo chi) [KC (ZV 32) 0 4 (ZV 37); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]).
Definition shlL_keep : list Z := [1; 2; 3; 4; 5; 8; 9; 10; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 30; 31].

#[using="Type"] Lemma shl_loop_A : forall t done c regs m (A s : Z),
  let p := A + 4 * Z.of_nat (length done) in
  getr regs 11%bv = Z_to_bv 64 p -> getr regs 6%bv = Z_to_bv 64 p -> getr regs 7%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 17%bv = Z_to_bv 64 c -> getr regs 16%bv = Z_to_bv 64 s -> getr regs 5%bv = Z_to_bv 64 (28 - s) ->
  getr regs 15%bv = Z_to_bv 64 SHA ->
  0 <= s < 28 -> 0 <= c < 2 ^ s -> ok t -> t <> [] ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objsh m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 127 ->
  arr32 SEGS_A m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0ab1a8) m rom) (mkst regs' (Z_to_bv 64 0x0ab200) m' rom)
    /\ arr32 SEGS_A m' A (done ++ fst (shl_l s c t))
    /\ getr regs' 28%bv = Z_to_bv 64 (snd (shl_l s c t))
    /\ keeps shlL_keep regs regs'
    /\ unch m m' [(p, p + 4 * Z.of_nat (length t))] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A s p R11 R6 R7 R17 R16 R5 R15 Hs Hc Hok Hne HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  apply ok_cons in Hok as [Hx Hok]. cbn [length] in R7, Hlen, Hst |- *.
  assert (Hcell : exists bs, rdn SEGS_A m (Z_to_bv 64 p) 4 = Some bs /\ bytes_le_to_Z bs = x).
  { eapply kc_of_arr32; [exact Harr | unfold p; lia]. }
  pose proof (shl_step x c s Hx Hs Hc) as [Hdiv Hnc].
  cbn [shl_l]. destruct (shl_l s (x / 2 ^ (28 - s)) t) as [r c'] eqn:Hrec. cbn [fst snd].
  assert (Hs27 : 2 ^ s <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia).
  destruct t as [|y t'].
  - (* [comment removed for export] *)
    cbn [length Z.of_nat] in *.
    zx_run SEGS_A constr:(shlL_ctx 1 1) 30%nat [0x0ab1a8; 0x0ab200] (SCR [] []) constr:(shlL_pins) [p; 1; c; s; 28 - s; x]
           constr:(shlL_uvi 1 1) regs m rom 0x0ab1a8.
    unfold p in *.
    zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
      ltac:(kc1 Hcell; kcsh OSH ((4 + 4 * Z.of_nat (length done)) / 8); exact I)
      ltac:(kw1 Hst; exact I) ltac:(exact I).
    cbn in Hrec. injection Hrec as <- <-.
    zx_reg ZR (28%bv : reg) as R28'.
    eexists regs0, _. split; [exact ZM|].
    split; [|split; [exact R28'|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]].
    apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
    rewrite u_Z2bv64. unfold B. change (2 ^ 28) with 268435456. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
  - (* [comment removed for export] *)
    cbn [length] in *.
    zx_run SEGS_A constr:(shlL_ctx 2 128) 30%nat [0x0ab1a8; 0x0ab200] (SCR [] []) constr:(shlL_pins)
           [p; Z.of_nat (S (S (length t'))); c; s; 28 - s; x] constr:(shlL_uvi 2 128) regs m rom 0x0ab1a8.
    unfold p in *.
    zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
      ltac:(kc1 Hcell; kcsh OSH ((4 + 4 * Z.of_nat (length done)) / 8); exact I)
      ltac:(kw1 Hst; exact I) ltac:(exact I).
    zx_reg ZR (17%bv : reg) as R17'. zx_reg ZR (7%bv : reg) as R7'. zx_reg ZR (11%bv : reg) as R11'.
    zx_reg ZR (6%bv : reg) as R6'. zx_reg ZR (16%bv : reg) as R16'. zx_reg ZR (5%bv : reg) as R5'. zx_reg ZR (15%bv : reg) as R15'.
    set (m1 := wbytes m _ _) in ZM.
    assert (Harr1 : arr32 SEGS_A m1 A ((done ++ [(x * 2 ^ s + c) mod B]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold B. change (2 ^ 28) with 268435456. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia. }
    specialize (IH (done ++ [(x * 2 ^ s + c) mod B]) (x / 2 ^ (28 - s)) regs0 m1 A s).
    rewrite length_app in IH. cbn [length] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & R28'' & K2 & U2 & G2).
    + rewrite R11'. f_equal. lia.
    + rewrite R6'. f_equal. lia.
    + rewrite R7'. f_equal. lia.
    + exact R17'.
    + exact R16'.
    + exact R5'.
    + exact R15'.
    + lia.
    + exact Hnc.
    + exact Hok.
    + congruence.
    + lia.
    + lia.
    + lia.
    + unfold m1. eapply (objsh_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
        [unchx| intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH].
    + lia.
    + exact Harr1.
    + (* [comment removed for export] *)
      unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply (store_ok_sub SEGS_A m (Z_to_bv 64 p)); try exact Hst;
        rewrite ?u_Z2bv64, ?Z.mod_small; cbn [length]; try lia.
    + rewrite Hrec in *. cbn [fst snd] in *.
      eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [rewrite <- app_assoc in Harr2; exact Harr2|].
      split; [exact R28''|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem shl_A : forall regs m (o n sp : Z) (ret : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 n -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0 <= n < 2048 -> bn_at SEGS_A m o b -> ok (cells b) -> zlen (cells b) <= 126 -> ex b + n / 28 < 2 ^ 15 ->
  KHI + 16 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 16 \/ sp <= o) ->
  shcells m -> objsh m o ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0ab0fc) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_A m' o (shl n b)
    /\ unch m m' [(o, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o n sp ret b R10 R11 R2 R1 Hret Hn Hbn Hok Hlen Hex Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj [SC1 SC2] OSH Hsto Hsts.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  pose proof (u64_range ret) as Rret.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  remember (cells b) as l eqn:El.
  hide Hdisj.
  destruct l as [|x t].
  - (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (0, 0)])
                              [KC (ZL 0) 0x129ea8 8 (ZL 0x132278); KC (ZL 0) 0x132278 8 (ZL SHA);
                               KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 35)] [KW (ZV 34) (-16) 0])
      40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34)])
      [o; n; sp; 0] constr:([Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (0, 0)]) regs m rom 0x0ab0fc.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; exact I)
      ltac:(kw1 Hsts; exact I)
      ltac:(unhide; zx_scs ltac:(lia)).
    assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H, <- R1; apply Z_to_bv_bv_unsigned).
    eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    clear ZM ZE ZR ZF. unhide.
    split; [|split; [unchx|growsx]].
    unfold shl. rewrite <- El. cbn [cells BnModel.ex]. unfold bn_at. rewrite <- El.
    split; [cellN_go|split; [cellN_go|split; [|split; [exact Hexr| unfold zlen; cbn; lia]]]].
    apply arr32_nil.
  - (* [comment removed for export] *)
    apply ok_cons in Hok as Hok0. destruct Hok0 as [Hx Hokt].
    assert (Hus : 1 <= zlen (x :: t) <= 126) by (rewrite zlen_cons in *; pose proof (zlen_nonneg t); lia).
    remember (zlen (x :: t)) as u eqn:Hu. unfold zlen in Hu. cbn [length] in Hu.
    (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1)])
                              [KC (ZL 0) 0x129ea8 8 (ZL 0x132278); KC (ZL 0) 0x132278 8 (ZL SHA);
                               KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZV 32) (ZL 2)) 3) SHA 1 (ZL 0);
                               KC (ZV 32) 0 2 (ZV 35); KC (ZV 32) 2 2 (ZV 36)] [KW (ZV 34) (-16) 0])
      40%nat [0x0ab168] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34)])
      [o; n; sp; u; ex b] constr:([Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1)]) regs m rom 0x0ab0fc.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kcsh OSH 0; kc1 Cu; kc1 Ce; exact I)
      ltac:(kw1 Hsts; exact I)
      ltac:(unhide; zx_scs ltac:(lia)).
    zx_reg ZR (5%bv : reg) as A5. fold (magic28A n) in A5. rewrite (magic28A_ok n) in A5 by lia.
    zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (12%bv : reg) as A12.
    zx_reg ZR (14%bv : reg) as A14. zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11.
    zx_reg ZR (2%bv : reg) as A2. zx_reg ZR (15%bv : reg) as A15. zx_reg ZR (13%bv : reg) as A13.
    set (m1 := wbytes m _ _) in ZM.
    assert (K1 : keeps CS' regs regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. rename ZM into M1. rename regs0 into regs1.
    (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73)])
                              [] [KW (ZV 32) 0 516])
      40%nat [0x0ab194] (SCR [] []) constr:([(5%bv : reg, ZV 37); (17%bv : reg, ZV 36); (16%bv : reg, ZV 35); (12%bv : reg, ZAdd (ZV 32) (ZL 2));
        (14%bv : reg, ZV 35); (10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-16))); (15%bv : reg, ZL SHA);
        (13%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
      [o; n; sp; u; ex b; n / 28] constr:([Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73)]) regs1 m1 rom 0x0ab168.
    assert (Hsto1 : RiscvSemantics.store_ok SEGS_A m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [|exact Hsto]; unfold m1; growsx).
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto1; exact I) ltac:(exact I).
    zx_reg ZR (16%bv : reg) as B16. zx_reg ZR (12%bv : reg) as B12. zx_reg ZR (14%bv : reg) as B14. zx_reg ZR (17%bv : reg) as B17.
    zx_reg ZR (10%bv : reg) as B10. zx_reg ZR (2%bv : reg) as B2. zx_reg ZR (15%bv : reg) as B15. zx_reg ZR (13%bv : reg) as B13.
    set (m2 := wbytes m1 _ _) in ZM.
    assert (K2 : keeps CS' regs1 regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. rename ZM into M2. rename regs0 into regs2.
    assert (Hs : 0 <= n mod 28 < 28) by lia.
    (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73); Some (0, 27)])
                              [] [])
      40%nat [0x0ab1a8] (SCR [] []) constr:([(16%bv : reg, ZV 38); (12%bv : reg, ZAdd (ZV 32) (ZL 4)); (14%bv : reg, ZV 35); (17%bv : reg, ZL 0);
        (10%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 34) (ZL (-16))); (15%bv : reg, ZL SHA); (13%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
      [o; n; sp; u; ex b; n / 28; n mod 28] constr:([Some (IMG, HIE - 516); Some (0, 2047); Some (KHI + 16, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73); Some (0, 27)]) regs2 m2 rom 0x0ab194.
    zx_use2 ZXB ltac:(zx_pins; rewrite B16; f_equal; lia) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I).
    zx_reg ZR (11%bv : reg) as D11. zx_reg ZR (6%bv : reg) as D6. zx_reg ZR (7%bv : reg) as D7. zx_reg ZR (17%bv : reg) as D17.
    zx_reg ZR (16%bv : reg) as D16. zx_reg ZR (5%bv : reg) as D5. zx_reg ZR (15%bv : reg) as D15.
    zx_reg ZR (12%bv : reg) as D12. zx_reg ZR (10%bv : reg) as D10. zx_reg ZR (2%bv : reg) as D2. zx_reg ZR (14%bv : reg) as D14.
    zx_reg ZR (13%bv : reg) as D13.
    assert (K2' : keeps CS' regs2 regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    clear ZE ZR ZF. rename ZM into M2'. rename regs0 into regs2'.
    (* [comment removed for export] *)
    unhide.
    assert (Harr2 : arr32 SEGS_A m2 (o + 4) ([] ++ x :: t)).
    { cbn [app]. unfold m2, m1. apply arr32_store_other; zwidth; try lia.
      apply arr32_store_other; zwidth; try lia. exact Carr. }
    assert (OSH2 : objsh m2 o).
    { unfold m2, m1. eapply (objsh_unch m _ [(o, o + 516); (sp - 16, sp)]); [unchx | intros r0 [<-|[<-|[]]]; cbn; lia | lia | lia | exact OSH]. }
    destruct (shl_loop_A (x :: t) [] 0 regs2' m2 (o + 4) (n mod 28)) as (regs3 & m3 & M3 & Harr3 & C28 & K3 & U3 & G3);
      cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
    { rewrite D11; first [reflexivity | f_equal; lia]. }
    { rewrite D6; first [reflexivity | f_equal; lia]. }
    { rewrite D7. f_equal. lia. }
    { exact D17. }
    { exact D16. }
    { rewrite D5; first [reflexivity | f_equal; lia]. }
    { exact D15. }
    { exact Hs. }
    { split; [lia|]. apply Z.pow_pos_nonneg; lia. }
    { exact Hok. }
    { congruence. }
    { lia. }
    { lia. }
    { replace (o + 4 - 4) with o by lia. exact Ho8. }
    { replace (o + 4 - 4) with o by lia. exact OSH2. }
    { lia. }
    { exact Harr2. }
    { eapply sc_store_in; [eapply store_ok_grows; [|exact Hsto1]; unfold m2; growsx |]. cbn [length]. lia. }
    cbn [length app] in Harr3, U3. rewrite ?Z.mul_0_r, ?Z.add_0_r in U3.
    pose proof (shl_l_spec (n mod 28) (x :: t) 0 Hok Hs ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as SPEC.
    destruct (shl_l (n mod 28) 0 (x :: t)) as [r c'] eqn:Eshl. cbn [fst snd] in Harr3, C28.
    destruct SPEC as (_ & Hokr & Hlenr & Hc').
    assert (Hc'27 : c' < 2 ^ 27) by (assert (2 ^ (n mod 28) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia); lia).
    assert (Hlenr' : Z.of_nat (length r) = u) by (unfold zlen in Hlenr; cbn [length] in Hlenr; lia).
    (* [comment removed for export] *)
    assert (C14 : getr regs3 14%bv = Z_to_bv 64 u) by (etransitivity; [exact (K3 14 ltac:(in_list)) | exact D14]).
    assert (C10 : getr regs3 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K3 10 ltac:(in_list)) | exact D10]).
    assert (C2 : getr regs3 2%bv = Z_to_bv 64 (sp + -16)) by (etransitivity; [exact (K3 2 ltac:(in_list)) | exact D2]).
    assert (C12 : getr regs3 12%bv = Z_to_bv 64 (o + 4)) by (etransitivity; [exact (K3 12 ltac:(in_list)) | exact D12]).
    assert (C15 : getr regs3 15%bv = Z_to_bv 64 SHA) by (etransitivity; [exact (K3 15 ltac:(in_list)) | exact D15]).
    assert (C13 : getr regs3 13%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (etransitivity; [exact (K3 13 ltac:(in_list)) | exact D13]).
    assert (RA3 : cellN SEGS_A m3 (sp + -8) 8 (bv_unsigned ret)).
    { eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; unhide; lia |].
      unfold m2, m1. cbv [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite ?R1. cellN_go. }
    assert (OSH3 : objsh m3 o).
    { eapply (objsh_unch m2 _ _); [exact U3 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH2]. }
    assert (Hsto3 : RiscvSemantics.store_ok SEGS_A m3 (Z_to_bv 64 o) 516 = true).
    { eapply store_ok_grows; [exact G3|]. eapply store_ok_grows; [|exact Hsto1]. unfold m2; growsx. }
    (* [comment removed for export] *)
    assert (EXC : forall m', unch m3 m' [(o, o + 2); (o + 4 + 4 * u, o + 8 + 4 * u)] -> cellN SEGS_A m' (o + 2) 2 (ex b + n / 28)).
    { intros m' U. eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia |].
      eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      unfold m2. cellN_go. }
    assert (UNCH : forall m', unch m3 m' [(o, o + 516)] -> unch m m' [(o, o + 516); (sp - 16, sp)]).
    { intros m' U. apply (unch_trans m m3 m'); [|eapply unch_widen; [exact U|]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; eexists; split; [left; reflexivity|cbn; lia]].
      apply (unch_trans m m2 m3); [unfold m2, m1; unchx|].
      eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|cbn; lia]. }
    assert (KEEPS : forall regs4, keeps CS' regs3 regs4 -> getr regs4 2%bv = Z_to_bv 64 sp -> keeps CS regs regs4).
    { intros regs4 K4 S4. apply keeps_CS_of; [|rewrite S4, R2; reflexivity].
      eapply keeps_trans; [exact K1|]. eapply keeps_trans; [exact K2|]. eapply keeps_trans; [exact K2'|]. eapply keeps_trans; [|exact K4].
      eapply keeps_sub_dec; [exact K3|]. vm_compute. reflexivity. }
    assert (MS : forall st, msteps SEGS_A (mkst regs3 (Z_to_bv 64 0x0ab200) m3 rom) st ->
                            msteps SEGS_A (mkst regs (Z_to_bv 64 0x0ab0fc) m rom) st).
    { intros st H. eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M2'|].
      eapply msteps_trans; [exact M3|]. exact H. }
    unfold shl. rewrite <- El, Eshl. unfold bn_at. cbn [cells BnModel.ex].
    clear M1 M2 M2' M3 Harr2 OSH2 K1 K2 K2' K3.
    clear A5 A17 A16 A12 A14 A10 A11 A2 A15 A13 B16 B12 B14 B17 B10 B2 B15 B13 D11 D6 D7 D17 D16 D5 D15 D12 D10 D2 D14 D13.
    destruct (Z.eqb_spec c' 0) as [Hc0|Hc0].
    + (* [comment removed for export] *)
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (KHI + 16, HIE); Some (1, 126); Some (0, 0); Some (0, 18446744073709551615)])
          [KC (ZV 33) (-8) 8 (ZV 36); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 34) (ZL 4))) 3) SHA 1 (ZL 0)]
          [KW (ZV 32) 0 516])
        40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-16))); (14%bv : reg, ZV 34); (28%bv : reg, ZV 35);
          (12%bv : reg, ZAdd (ZV 32) (ZL 4)); (15%bv : reg, ZL SHA); (13%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
        [o; sp; u; c'; bv_unsigned ret] constr:([Some (IMG, HIE - 516); Some (KHI + 16, HIE); Some (1, 126); Some (0, 0); Some (0, 18446744073709551615)]) regs3 m3 rom 0x0ab200.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA3; kcsh OSH3 0; kcsh OSH3 ((4 + 4 * u) / 8); exact I) ltac:(kw1 Hsto3; exact I) ltac:(exact I).
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (2%bv : reg) as E2.
      eexists regs0, m3. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
      split; [apply KEEPS; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | rewrite E2; f_equal; lia]|].
      clear ZM ZE ZR ZF. unhide.
      split; [|split; [apply UNCH; apply unch_refl | apply (mem_grows_trans m m2 m3); [unfold m2, m1; growsx | exact G3]]].
      split; [|split; [apply EXC; apply unch_refl|split; [exact Harr3|split; [lia| unfold zlen; rewrite Hlenr'; lia]]]].
      unfold zlen; rewrite Hlenr'.
      eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      unfold m2, m1. cellN_go.
    + (* [comment removed for export] *)
      zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (KHI + 16, HIE); Some (1, 126); Some (1, 2 ^ 27); Some (0, 18446744073709551615)])
          [KC (ZV 33) (-8) 8 (ZV 36); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 34) (ZL 4))) 3) SHA 1 (ZL 0)]
          [KW (ZV 32) 0 516])
        40%nat (@nil Z) (SCR [] []) constr:([(10%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-16))); (14%bv : reg, ZV 34); (28%bv : reg, ZV 35);
          (12%bv : reg, ZAdd (ZV 32) (ZL 4)); (15%bv : reg, ZL SHA); (13%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
        [o; sp; u; c'; bv_unsigned ret] constr:([Some (IMG, HIE - 516); Some (KHI + 16, HIE); Some (1, 126); Some (1, 2 ^ 27); Some (0, 18446744073709551615)]) regs3 m3 rom 0x0ab200.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 RA3; kcsh OSH3 0; kcsh OSH3 ((4 + 4 * u) / 8); exact I) ltac:(kw1 Hsto3; exact I)
        ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto3 | zwidth; lia])).
      assert (R1' : getr regs0 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      zx_reg ZR (2%bv : reg) as E2.
      eexists regs0, _. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
      split; [apply KEEPS; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | rewrite E2; f_equal; lia]|].
      clear ZM ZE ZR ZF. unhide.
      split; [|split; [apply UNCH; unchx | eapply mem_grows_trans; [apply (mem_grows_trans m m2 m3); [unfold m2, m1; growsx | exact G3] | growsx]]].
      rewrite zlen_app. unfold zlen. cbn [length]. rewrite Hlenr'.
      split; [cellN_go|split; [apply EXC; unchx|split; [|lia]]].
      replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length r)) by lia.
      apply arr32_store_other; [lia | rewrite length_app; zwidth; lia | lia | zwidth; lia | rewrite length_app; zwidth; lia |].
      apply arr32_snoc'; try lia; [exact Harr3|].
      rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.

End S.
