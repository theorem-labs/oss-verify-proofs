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
  BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnA_shl BnB_lib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Abbreviation shlL_pins :=
  [(11%bv : reg, ZV 32); (5%bv : reg, ZV 32); (6%bv : reg, ZV 33); (7%bv : reg, ZV 34); (12%bv : reg, ZV 35);
   (16%bv : reg, ZV 36); (15%bv : reg, ZL SHA)].
Abbreviation shlL_uvi clo chi :=
  [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 27); Some (0, 27); Some (1, 28); Some (0, 2 ^ 28 - 1)].
Abbreviation shlL_ctx clo chi :=
  (CTX (vi_regs ++ shlL_uvi clo chi) [KC (ZV 32) 0 4 (ZV 37); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]).
Definition shlLB_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 30; 31].

#[using="Type"] Lemma shl_loop_B : forall t done c regs m (A s : Z),
  let p := A + 4 * Z.of_nat (length done) in
  getr regs 11%bv = Z_to_bv 64 p -> getr regs 5%bv = Z_to_bv 64 p -> getr regs 6%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 7%bv = Z_to_bv 64 c -> getr regs 12%bv = Z_to_bv 64 s -> getr regs 16%bv = Z_to_bv 64 (28 - s) ->
  getr regs 15%bv = Z_to_bv 64 SHA ->
  0 <= s < 28 -> 0 <= c < 2 ^ s -> ok t -> t <> [] ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objshB m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 127 ->
  arr32 SEGS_B m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0ab204) m rom) (mkst regs' (Z_to_bv 64 0x0ab26c) m' rom)
    /\ arr32 SEGS_B m' A (done ++ fst (shl_l s c t))
    /\ getr regs' 28%bv = Z_to_bv 64 (snd (shl_l s c t))
    /\ keeps shlLB_keep regs regs'
    /\ unch m m' [(p, p + 4 * Z.of_nat (length t))] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A s p R11 R5 R6 R7 R12 R16 R15 Hs Hc Hok Hne HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  apply ok_cons in Hok as [Hx Hok]. cbn [length] in R7, Hlen, Hst |- *.
  assert (Hcell : exists bs, rdn SEGS_B m (Z_to_bv 64 p) 4 = Some bs /\ bytes_le_to_Z bs = x).
  { eapply kc_of_arr32; [exact Harr | unfold p; lia]. }
  pose proof (shl_step x c s Hx Hs Hc) as [Hdiv Hnc].
  cbn [shl_l]. destruct (shl_l s (x / 2 ^ (28 - s)) t) as [r c'] eqn:Hrec. cbn [fst snd].
  assert (Hs27 : 2 ^ s <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia).
  destruct t as [|y t'].
  - (* [comment removed for export] *)
    cbn [length Z.of_nat] in *.
    zx_run SEGS_B constr:(shlL_ctx 1 1) 30%nat [0x0ab204; 0x0ab26c] (SCR [] []) constr:(shlL_pins) [p; 1; c; s; 28 - s; x]
           constr:(shlL_uvi 1 1) regs m rom 0x0ab204.
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
    zx_run SEGS_B constr:(shlL_ctx 2 128) 30%nat [0x0ab204; 0x0ab26c] (SCR [] []) constr:(shlL_pins)
           [p; Z.of_nat (S (S (length t'))); c; s; 28 - s; x] constr:(shlL_uvi 2 128) regs m rom 0x0ab204.
    unfold p in *.
    zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia)
      ltac:(kc1 Hcell; kcsh OSH ((4 + 4 * Z.of_nat (length done)) / 8); exact I)
      ltac:(kw1 Hst; exact I) ltac:(exact I).
    zx_reg ZR (7%bv : reg) as R7'. zx_reg ZR (6%bv : reg) as R6'. zx_reg ZR (11%bv : reg) as R11'.
    zx_reg ZR (5%bv : reg) as R5'. zx_reg ZR (12%bv : reg) as R12'. zx_reg ZR (16%bv : reg) as R16'. zx_reg ZR (15%bv : reg) as R15'.
    set (m1 := wbytes m _ _) in ZM.
    assert (Harr1 : arr32 SEGS_B m1 A ((done ++ [(x * 2 ^ s + c) mod B]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold B. change (2 ^ 28) with 268435456. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia. }
    specialize (IH (done ++ [(x * 2 ^ s + c) mod B]) (x / 2 ^ (28 - s)) regs0 m1 A s).
    rewrite length_app in IH. cbn [length] in IH.
    destruct IH as (regs2 & m2 & M2 & Harr2 & R28'' & K2 & U2 & G2).
    + rewrite R11'. f_equal. lia.
    + rewrite R5'. f_equal. lia.
    + rewrite R6'. f_equal. lia.
    + exact R7'.
    + exact R12'.
    + exact R16'.
    + exact R15'.
    + lia.
    + exact Hnc.
    + exact Hok.
    + congruence.
    + lia.
    + lia.
    + lia.
    + unfold m1. eapply (objshB_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
        [unchx| intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH].
    + lia.
    + exact Harr1.
    + (* [comment removed for export] *)
      unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply (store_ok_sub SEGS_B m (Z_to_bv 64 p)); try exact Hst;
        rewrite ?u_Z2bv64, ?Z.mod_small; cbn [length]; try (try clear - x t' done c A s p Hs Hc Hx HA1 HA2 HA8 Hlen Hnc; lia).
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

End S.
