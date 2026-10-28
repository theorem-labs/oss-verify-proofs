(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith GrayLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23LeptRop2Segs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropLow_84000_85000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition RG3_S1 : word := 0x84a08.
Definition RG3_F : word := 0x84a90.
Definition RG3_X1 : word := 0x84b84.
Definition RG3_H2 : word := 0x84bcc.
Definition RG3_I : word := 0x84be8.
Definition RG3_T2 : word := 0x84c7c.
Definition RG3_X2 : word := 0x84cec.
Definition RG3_L : word := 0x84d88.
Definition RG3_JT : Z := 0x1f3a0.
Definition RG3_JTV : Z := 415344.

Section Segs3G.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac rg3_post := repeat split; gres; pin; try reflexivity; solve_regs_agree.
Ltac rgF_tail3 n pd d4 psf off s4 s bd Rd Ld SOK Cz :=
  stepb_tk F_84b04 D_84b04 ltac:(condR);
  stepb_tk F_84b0c D_84b0c ltac:(condZ);
  ld4 F_84b14 D_84b14 pd bd Rd Ld;
  sn F_84b18 D_84b18; sn F_84b1c D_84b1c; sn F_84b20 D_84b20; sn F_84b24 D_84b24;
  zv F_84b28 D_84b28 (Z_to_bv 64 (pd + d4));
  stw F_84b2c D_84b2c (Z_to_bv 64 pd) SOK;
  stepb_tk F_84b30 D_84b30 ltac:(condZ);
  sltu0 F_84b38 D_84b38; sn F_84b3c D_84b3c; sn F_84b40 D_84b40;
  stepb_tk F_84b44 D_84b44 ltac:(condR);
  zv F_84b4c D_84b4c (Z_to_bv 64 (psf + off + s4));
  stepb_tk F_84b50 D_84b50 ltac:(condZ);
  sltu0 F_84b58 D_84b58;
  ld8w F_84b5c D_84b5c (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_84b60 D_84b60; sn F_84b64 D_84b64;
  stepb_tk F_84b68 D_84b68 ltac:(condR);
  sn F_84b70 D_84b70; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_84b74 D_84b74 (Z_to_bv 64 (off + s4));
  zv F_84b78 D_84b78 (Z_to_bv 64 (pd + d4));
  sn F_84b7c D_84b7c;
  first [ stepb_ft F_84b80 D_84b80 ltac:(condSe) | stepb_tk F_84b80 D_84b80 ltac:(condSe) ]; apply mst_refl.
(* [comment removed for export] *)
Lemma rg3_F : forall (f6 f7 last : bool) regs m (s psf off pd s4 d4 n sls : Z) (bs0 bs1 bd : list byte),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= psf)%Z -> (0 <= off)%Z -> (0 <= s4)%Z -> (0 <= d4)%Z ->
  (1 <= psf + off)%Z -> (psf + off + s4 < 2 ^ 64)%Z -> (1 <= pd)%Z -> (pd + d4 < 2 ^ 64)%Z -> (pd + 4 < 2 ^ 64)%Z ->
  (pd + 4 <= s - 240 \/ s <= pd)%Z ->
  (1 <= n < 2 ^ 31)%Z -> (if last then n = 1 else 1 < n)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psf + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  (f6 = true -> f7 = false -> psf + off + 8 < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 (psf + off + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 15 = Z_to_bv 64 psf -> getr regs 11 = Z_to_bv 64 off ->
  getr regs 25 = Z_to_bv 64 pd -> getr regs 16 = Z_to_bv 64 pd -> getr regs 28 = Z_to_bv 64 (- n) ->
  getr regs 13 = Z_to_bv 64 s4 -> getr regs 7 = Z_to_bv 64 d4 -> getr regs 20 = Z_to_bv 64 (psf + s4) ->
  getr regs 19 = Z_to_bv 64 (if f6 then 1 else 0) -> getr regs 24 = Z_to_bv 64 (if f7 then 1 else 0) ->
  getr regs 22 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 0 -> getr regs 1 = Z_to_bv 64 31 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG3_F m rom)
                (mkst regs' (if last then RG3_X1 else RG3_F) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + s4) /\ getr regs' 25 = Z_to_bv 64 (pd + d4) /\ getr regs' 16 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 28 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [11; 12; 16; 21; 25; 26; 28]%list) regs regs'.
Proof.
  intros f6 f7 last regs m s psf off pd s4 d4 n sls bs0 bs1 bd Hs Hs64 Hpsf Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cz H2 H15 H11 H25 H16 H28 H13 H7 H20 H19 H24 H22 H23 H9 H1 H30 H8.
  unfold RG3_F, RG3_X1.
  destruct f6; [destruct f7|].
  - destruct last; eexists; eexists; (split; [
      zv F_84a90 D_84a90 (Z_to_bv 64 (psf + off));
      snez1 F_84a94 D_84a94;
      sn F_84a98 D_84a98;
      stepb_ft F_84a9c D_84a9c ltac:(condR);
      stepb_tk F_84aa0 D_84aa0 ltac:(condR);
      sn F_84aa8 D_84aa8;
      stepb_tk F_84aac D_84aac ltac:(condZ);
      ld4 F_84ab4 D_84ab4 (psf + off)%Z bs0 R0 L0;
      sn F_84ab8 D_84ab8;
      stepb_tk F_84abc D_84abc ltac:(condR);
      rgF_tail3 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg3_post ]).
  - destruct (R1 eq_refl eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      zv F_84a90 D_84a90 (Z_to_bv 64 (psf + off));
      snez1 F_84a94 D_84a94;
      sn F_84a98 D_84a98;
      stepb_ft F_84a9c D_84a9c ltac:(condR);
      stepb_tk F_84aa0 D_84aa0 ltac:(condR);
      sn F_84aa8 D_84aa8;
      stepb_tk F_84aac D_84aac ltac:(condZ);
      ld4 F_84ab4 D_84ab4 (psf + off)%Z bs0 R0 L0;
      sn F_84ab8 D_84ab8;
      stepb_ft F_84abc D_84abc ltac:(condR);
      sn F_84ac0 D_84ac0;
      stepb_tk F_84ac4 D_84ac4 ltac:(condZ);
      stepb_tk F_84acc D_84acc ltac:(condZ);
      ld4 F_84ad4 D_84ad4 (psf + off + 4)%Z bs1 R1' L1;
      sn F_84ad8 D_84ad8; sn F_84adc D_84adc; sn F_84ae0 D_84ae0; sn F_84ae4 D_84ae4;
      stepj F_84ae8 D_84ae8;
      rgF_tail3 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg3_post ]).
  - destruct last; eexists; eexists; (split; [
      zv F_84a90 D_84a90 (Z_to_bv 64 (psf + off));
      snez1 F_84a94 D_84a94;
      sn F_84a98 D_84a98;
      stepb_tk F_84a9c D_84a9c ltac:(condR);
      stepb_tk F_84aec D_84aec ltac:(condR);
      stepb_tk F_84af4 D_84af4 ltac:(condZ);
      ld4 F_84afc D_84afc (psf + off)%Z bs0 R0 L0;
      sn F_84b00 D_84b00;
      rgF_tail3 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg3_post ]).
Qed.

(* [comment removed for export] *)
Ltac rgL_tail3 n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz :=
  stepb_tk F_84dd0 D_84dd0 ltac:(condR);
  stepb_tk F_84dd8 D_84dd8 ltac:(condZ);
  ld4 F_84de0 D_84de0 pd bd Rd Ld;
  sn F_84de4 D_84de4;
  ld8 F_84de8 D_84de8 (s - 144)%Z mk Cmk;
  sn F_84dec D_84dec; sn F_84df0 D_84df0; sn F_84df4 D_84df4;
  zv F_84df8 D_84df8 (Z_to_bv 64 (pd + d4));
  stw F_84dfc D_84dfc (Z_to_bv 64 pd) SOK;
  stepb_tk F_84e00 D_84e00 ltac:(condZ);
  sltu0 F_84e08 D_84e08; sn F_84e0c D_84e0c; sn F_84e10 D_84e10;
  stepb_tk F_84e14 D_84e14 ltac:(condR);
  zv F_84e1c D_84e1c (Z_to_bv 64 (psl + off + s4));
  stepb_tk F_84e20 D_84e20 ltac:(condZ);
  sltu0 F_84e28 D_84e28;
  ld8w F_84e2c D_84e2c (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_84e30 D_84e30; sn F_84e34 D_84e34;
  stepb_tk F_84e38 D_84e38 ltac:(condR);
  sn F_84e40 D_84e40; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_84e44 D_84e44 (Z_to_bv 64 (off + s4));
  zv F_84e48 D_84e48 (Z_to_bv 64 (pd + d4));
  sn F_84e4c D_84e4c;
  first [ stepb_ft F_84e50 D_84e50 ltac:(condSe); stepj F_84e54 D_84e54 | stepb_tk F_84e50 D_84e50 ltac:(condSe) ]; apply mst_refl.
Lemma rg3_L : forall (f3 last : bool) regs m (s psl off pd s4 d4 n sls : Z) (mk : word) (bs0 bs1 bd : list byte),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= psl)%Z -> (0 <= off)%Z -> (0 <= s4)%Z -> (0 <= d4)%Z ->
  (1 <= psl + off)%Z -> (psl + off + s4 < 2 ^ 64)%Z -> (1 <= pd)%Z -> (pd + d4 < 2 ^ 64)%Z -> (pd + 4 < 2 ^ 64)%Z ->
  (pd + 4 <= s - 240 \/ s <= pd)%Z ->
  (1 <= n < 2 ^ 31)%Z -> (if last then n = 1 else 1 < n)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psl + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  (f3 = false -> psl + off + 8 < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 (psl + off + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 off -> getr regs 10 = Z_to_bv 64 pd -> getr regs 20 = Z_to_bv 64 pd ->
  getr regs 9 = Z_to_bv 64 (- n) -> getr regs 5 = Z_to_bv 64 (if f3 then 1 else 0) ->
  getr regs 17 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 18446744073709551611 ->
  getr regs 19 = Z_to_bv 64 31 -> getr regs 16 = Z_to_bv 64 32 ->
  getr regs 28 = Z_to_bv 64 (psl + s4) -> getr regs 15 = Z_to_bv 64 d4 -> getr regs 6 = Z_to_bv 64 s4 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG3_L m rom)
                (mkst regs' (if last then RG_E else RG3_L) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + s4) /\ getr regs' 10 = Z_to_bv 64 (pd + d4) /\ getr regs' 20 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 9 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [9; 10; 11; 18; 20; 21; 22; 23]%list) regs regs'.
Proof.
  intros f3 last regs m s psl off pd s4 d4 n sls mk bs0 bs1 bd Hs Hs64 Hpsl Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cpsl Cmk Cz H2 H11 H10 H20 H9 H5 H17 H14 H7 H19 H16 H28 H15 H6 H30 H8.
  unfold RG3_L, RG_E.
  destruct f3.
  - destruct last; eexists; eexists; (split; [
      ld8 F_84d88 D_84d88 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_84d8c D_84d8c (Z_to_bv 64 (psl + off));
      stepb_tk F_84d90 D_84d90 ltac:(condZ);
      stepb_tk F_84d98 D_84d98 ltac:(condZ);
      ld4 F_84da0 D_84da0 (psl + off)%Z bs0 R0 L0;
      sn F_84da4 D_84da4;
      stepb_tk F_84da8 D_84da8 ltac:(condR);
      rgL_tail3 n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | rg3_post ]).
  - destruct (R1 eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      ld8 F_84d88 D_84d88 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_84d8c D_84d8c (Z_to_bv 64 (psl + off));
      stepb_tk F_84d90 D_84d90 ltac:(condZ);
      stepb_tk F_84d98 D_84d98 ltac:(condZ);
      ld4 F_84da0 D_84da0 (psl + off)%Z bs0 R0 L0;
      sn F_84da4 D_84da4;
      stepb_ft F_84da8 D_84da8 ltac:(condR);
      stepb_tk F_84dac D_84dac ltac:(condZ);
      stepb_tk F_84db4 D_84db4 ltac:(condZ);
      ld4 F_84dbc D_84dbc (psl + off + 4)%Z bs1 R1' L1;
      sn F_84dc0 D_84dc0; sn F_84dc4 D_84dc4; sn F_84dc8 D_84dc8; sn F_84dcc D_84dcc;
      rgL_tail3 n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | rg3_post ]).
Qed.

(* [comment removed for export] *)
Lemma rg3_H2 : forall regs m (s nfw psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= nfw < 2 ^ 26)%Z -> (1 <= psrow < 2 ^ 64)%Z -> (1 <= pdrow < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow ->
  getr regs 22 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (mkst regs RG3_H2 m rom) (mkst regs' RG3_I m rom)
    /\ getr regs' 24 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 28 = Z_to_bv 64 1
    /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [9; 12; 16; 21; 24; 28]%list) regs regs'.
Proof.
  intros regs m s nfw psrow pdrow Hs Hs64 Hnfw Hps Hpd Cnfw H2 H6 H18 H25 H17.
  unfold RG3_H2, RG3_I. eexists. split.
  - ld8 F_84bcc D_84bcc (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
    stepb_ft F_84bd0 D_84bd0 ltac:(condZ).
    sn F_84bd4 D_84bd4.
    snez1 F_84bd8 D_84bd8.
    snez1 F_84bdc D_84bdc.
    sn F_84be0 D_84be0.
    sn F_84be4 D_84be4.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.
Lemma rg3_I : forall (last : bool) regs m (psrow pdrow off n4 sls : Z) (bs0 bs1 : list byte),
  (0 <= off)%Z -> (off + 4 <= n4)%Z -> (if last then off + 4 = n4 else off + 4 < n4)%Z -> (n4 < 2 ^ 28)%Z ->
  (1 <= psrow)%Z -> (psrow + n4 + 4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + n4 < 2 ^ 64)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psrow + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (psrow + off + 4)) 4 = Some bs1 -> length bs1 = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 (pdrow + off)) 4 = true ->
  getr regs 27 = Z_to_bv 64 psrow -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 1 = Z_to_bv 64 pdrow -> getr regs 18 = Z_to_bv 64 pdrow ->
  getr regs 24 = Z_to_bv 64 off -> getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 16 = Z_to_bv 64 1 -> getr regs 28 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 1 ->
  getr regs 19 = Z_to_bv 64 32 -> getr regs 25 = Z_to_bv 64 18446744073709551611 -> getr regs 26 = Z_to_bv 64 31 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG3_I m rom)
                (mkst regs' (if last then RG3_T2 else RG3_I) (wbytes m (Z_to_bv 64 (pdrow + off)) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 24 = Z_to_bv 64 (off + 4)
    /\ regs_agree (fun r => In r [12; 15; 24]%list) regs regs'.
Proof.
  intros last regs m psrow pdrow off n4 sls bs0 bs1 Hoff Hn4 Hlast Hn4b Hps1 Hps2 Hpd1 Hpd2 Hsls R0 L0 R1 L1 SOK
    H27 H6 H1 H18 H24 H20 H16 H28 H9 H21 H23 H22 H26 H30 H8.
  unfold RG3_I, RG3_T2.
  destruct last; eexists; eexists; (split; [
    zv F_84be8 D_84be8 (Z_to_bv 64 (psrow + off));
    stepb_tk F_84bec D_84bec ltac:(condZ);
    seqz0 F_84bf4 D_84bf4;
    sn F_84bf8 D_84bf8;
    stepb_tk F_84bfc D_84bfc ltac:(condR);
    stepb_tk F_84c04 D_84c04 ltac:(condR);
    stepb_tk F_84c0c D_84c0c ltac:(condZ);
    zv F_84c14 D_84c14 (Z_to_bv 64 (psrow + off));
    stepb_tk F_84c18 D_84c18 ltac:(condZ);
    stepb_tk F_84c20 D_84c20 ltac:(condZ);
    zv F_84c28 D_84c28 (Z_to_bv 64 (pdrow + off));
    stepb_tk F_84c2c D_84c2c ltac:(condZ);
    seqz0 F_84c34 D_84c34;
    sn F_84c38 D_84c38;
    stepb_tk F_84c3c D_84c3c ltac:(condR);
    stepb_tk F_84c44 D_84c44 ltac:(condR);
    ld4 F_84c4c D_84c4c (psrow + off)%Z bs0 R0 L0;
    ld4 F_84c50 D_84c50 (psrow + off + 4)%Z bs1 R1 L1;
    sn F_84c54 D_84c54; sn F_84c58 D_84c58; sn F_84c5c D_84c5c; sn F_84c60 D_84c60; sn F_84c64 D_84c64;
    zv F_84c68 D_84c68 (Z_to_bv 64 (pdrow + off));
    sn F_84c6c D_84c6c;
    zv F_84c70 D_84c70 (Z_to_bv 64 (off + 4));
    stw F_84c74 D_84c74 (Z_to_bv 64 (pdrow + off)) SOK;
    first [ stepb_ft F_84c78 D_84c78 ltac:(condZ) | stepb_tk F_84c78 D_84c78 ltac:(condZ) ]; apply mst_refl
  | rg3_post ]).
Qed.

Lemma rg3_T2 : forall (last : bool) regs m (s i dh d4 s4 psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 <= dh)%Z -> (dh < 2 ^ 31)%Z -> (if last then i + 1 = dh else i + 1 < dh)%Z ->
  (0 <= d4)%Z -> (0 <= s4)%Z -> (1 <= psrow)%Z -> (psrow + s4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + d4 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 i -> getr regs 5 = Z_to_bv 64 d4 -> getr regs 7 = Z_to_bv 64 s4 ->
  getr regs 6 = Z_to_bv 64 psrow -> getr regs 27 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow -> getr regs 1 = Z_to_bv 64 pdrow ->
  getr regs 23 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs RG3_T2 m rom) (mkst regs' (if last then RG3_X2 else RG3_H2) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 6 = Z_to_bv 64 (psrow + s4) /\ getr regs' 27 = Z_to_bv 64 (psrow + s4)
    /\ getr regs' 18 = Z_to_bv 64 (pdrow + d4) /\ getr regs' 1 = Z_to_bv 64 (pdrow + d4)
    /\ regs_agree (fun r => In r [1; 6; 11; 12; 15; 16; 18; 27]%list) regs regs'.
Proof.
  intros last regs m s i dh d4 s4 psrow pdrow Hs Hs64 Hi Hidh Hdh Hlast Hd4 Hs4 Hps1 Hps2 Hpd1 Hpd2 Cz Cdh
    H2 H11 H5 H7 H6 H27 H18 H1 H19.
  unfold RG3_T2, RG3_X2, RG3_H2.
  destruct last; eexists; (split; [
    zv F_84c7c D_84c7c (Z_to_bv 64 (pdrow + d4));
    snez1 F_84c80 D_84c80;
    seqz0 F_84c84 D_84c84;
    stepb_tk F_84c88 D_84c88 ltac:(condR);
    sltu0 F_84c90 D_84c90;
    sn F_84c94 D_84c94; sn F_84c98 D_84c98;
    stepb_tk F_84c9c D_84c9c ltac:(condR);
    zv F_84ca4 D_84ca4 (Z_to_bv 64 (psrow + s4));
    snez1 F_84ca8 D_84ca8;
    seqz0 F_84cac D_84cac;
    stepb_tk F_84cb0 D_84cb0 ltac:(condR);
    sltu0 F_84cb8 D_84cb8;
    ld8 F_84cbc D_84cbc (s - 120)%Z (Z_to_bv 64 0) Cz;
    sn F_84cc0 D_84cc0; sn F_84cc4 D_84cc4;
    stepb_tk F_84cc8 D_84cc8 ltac:(condR);
    zv F_84cd0 D_84cd0 (Z_to_bv 64 (pdrow + d4));
    sn F_84cd4 D_84cd4; fixv' (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
    zv F_84cd8 D_84cd8 (Z_to_bv 64 (pdrow + d4));
    zv F_84cdc D_84cdc (Z_to_bv 64 (psrow + s4));
    sn F_84ce0 D_84ce0;
    ld8 F_84ce4 D_84ce4 (s - 112)%Z (Z_to_bv 64 dh) Cdh;
    first [ stepb_ft F_84ce8 D_84ce8 ltac:(condZ) | stepb_tk F_84ce8 D_84ce8 ltac:(condZ) ]; apply mst_refl
  | rg3_post ]).
Qed.

(* [comment removed for export] *)
Lemma rg3_S1 : forall (fw f6 f7 : bool) regs m (s dxb psf pdf swpl dwpl dh : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= dxb < 32)%Z -> (if fw then dxb <> 0 else dxb = 0)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  getr regs 1 = Z_to_bv 64 dxb -> getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  (fw = true ->
     (0 <= psf < 2 ^ 64)%Z /\ (0 <= pdf < 2 ^ 64)%Z /\ (psf mod 4 = 0)%Z /\ (pdf mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
     getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0) /\
     rdn SEGS m (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))) /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     rg_rows m s dh) ->
  exists regs',
    msteps SEGS (mkst regs RG3_S1 m rom) (mkst regs' (if fw then RG3_F else RG3_X1) m rom)
    /\ (fw = true -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 (psf + 4 * swpl) /\ getr regs' 13 = Z_to_bv 64 (4 * swpl)
                     /\ getr regs' 7 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 16 = Z_to_bv 64 pdf /\ getr regs' 28 = Z_to_bv 64 (- dh)
                     /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 (if f6 then 1 else 0) /\ getr regs' 24 = Z_to_bv 64 (if f7 then 1 else 0)
                     /\ getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 31)
    /\ regs_agree (fun r => In r [1; 5; 7; 9; 11; 12; 13; 16; 17; 19; 20; 21; 22; 23; 24; 28]%list) regs regs'.
Proof.
  intros fw f6 f7 regs m s dxb psf pdf swpl dwpl dh Hs Hs64 Hdxb Hfw Hswpl Hdwpl H1 H2 H14 HF.
  unfold RG3_S1, RG3_F, RG3_X1.
  destruct fw.
  2:{ exists regs. split; [| split; [intros; discriminate | apply regs_agree_refl]].
      stepb_tk F_84a08 D_84a08 ltac:(condZ). apply mst_refl. }
  destruct (HF eq_refl) as (Hpsf & Hpdf & ALs & ALd & Hdh & H15 & H25 & H26 & Cf6 & Cswpl & ROWS).
  destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
  eexists. split.
  - stepb_ft F_84a08 D_84a08 ltac:(condZ).
    sn F_84a0c D_84a0c.
    sn F_84a10 D_84a10.
    sn F_84a14 D_84a14.
    slli2 F_84a18 D_84a18 (4 * dwpl)%Z.
    ld8 F_84a1c D_84a1c (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
    slli2 F_84a20 D_84a20 (4 * swpl)%Z.
    zand0 F_84a24 D_84a24 andi_3 ALd.
    zand0 F_84a28 D_84a28 andi_3 ALs.
    ld8 F_84a2c D_84a2c (s - 160)%Z (Z_to_bv 64 c50) R50.
    ld8 F_84a30 D_84a30 (s - 200)%Z (Z_to_bv 64 c28) R28.
    subw_v F_84a34 D_84a34 (c28 - c50)%Z.
    ld8 F_84a38 D_84a38 (s - 184)%Z (Z_to_bv 64 c38) R38.
    ld8 F_84a3c D_84a3c (s - 192)%Z (Z_to_bv 64 c30) R30.
    zv F_84a40 D_84a40 (Z_to_bv 64 (c30 + c38)).
    ld8 F_84a44 D_84a44 (s - 168)%Z (Z_to_bv 64 c48) R48.
    sn F_84a48 D_84a48.
    ld8 F_84a4c D_84a4c (s - 224)%Z (Z_to_bv 64 (if f6 then 1 else 0)) Cf6.
    sn F_84a50 D_84a50. fixv' (Z_to_bv 64 (if f6 then 1 else 0)) ltac:(apply andi1_if).
    sn F_84a54 D_84a54. fixv' (Z_to_bv 64 (if f7 then 1 else 0)) ltac:(apply andi1_if).
    sn F_84a58 D_84a58.
    sn F_84a5c D_84a5c. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
    subw_v F_84a60 D_84a60 (c30 + c38 - c50)%Z.
    sn F_84a64 D_84a64.
    zv F_84a68 D_84a68 (Z_to_bv 64 (psf + 4 * swpl)).
    sn F_84a6c D_84a6c.
    ld8 F_84a70 D_84a70 (s - 176)%Z (Z_to_bv 64 c40) R40.
    subw_v F_84a74 D_84a74 (c30 + c38 - c50 - c40)%Z.
    addw_v F_84a78 D_84a78 (c30 + c38 - c50 - c40 + Z.min 0 c48)%Z.
    sn F_84a7c D_84a7c.
    sn F_84a80 D_84a80. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 - c50 - c40 + Z.min 0 c48))) ltac:(apply and_srai63_min; lia).
    subw_v F_84a84 D_84a84 (- dh)%Z.
    slti0 F_84a88 D_84a88.
    sn F_84a8c D_84a8c.
    apply mst_refl.
  - split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rg3_X1 : forall (nofull : bool) regs m (s psF pdF nfw swpl dwpl : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z -> (0 <= nfw < 2 ^ 26)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0))) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  (nofull = false ->
     (0 <= psF < 2 ^ 64)%Z /\ (0 <= pdF < 2 ^ 64)%Z /\ (psF mod 4 = 0)%Z /\ (pdF mod 4 = 0)%Z /\
     getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw))) ->
  exists regs',
    msteps SEGS (mkst regs RG3_X1 m rom) (mkst regs' (if nofull then RG3_X2 else RG3_H2) m rom)
    /\ (nofull = false -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 5 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 7 = Z_to_bv 64 (4 * swpl)
                          /\ getr regs' 20 = Z_to_bv 64 (4 * nfw) /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 32
                          /\ getr regs' 25 = Z_to_bv 64 18446744073709551611 /\ getr regs' 17 = Z_to_bv 64 1 /\ getr regs' 22 = Z_to_bv 64 1
                          /\ getr regs' 26 = Z_to_bv 64 31 /\ getr regs' 27 = Z_to_bv 64 psF /\ getr regs' 1 = Z_to_bv 64 pdF)
    /\ regs_agree (fun r => In r [1; 5; 7; 11; 12; 13; 15; 17; 19; 20; 22; 23; 25; 26; 27]%list) regs regs'.
Proof.
  intros nofull regs m s psF pdF nfw swpl dwpl Hs Hs64 Hswpl Hdwpl Hnfw Cnf H2 H14 HF.
  unfold RG3_X1, RG3_X2, RG3_H2.
  destruct nofull.
  - eexists. split.
    { ld8 F_84b84 D_84b84 (s - 208)%Z (Z_to_bv 64 1) Cnf.
      stepb_tk F_84b88 D_84b88 ltac:(condR).
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (HpsF & HpdF & ALs & ALd & H6 & H18 & Cswpl & Cnfw).
    eexists. split.
    + ld8 F_84b84 D_84b84 (s - 208)%Z (Z_to_bv 64 0) Cnf.
      stepb_ft F_84b88 D_84b88 ltac:(condR).
      sn F_84b8c D_84b8c.
      slli2 F_84b90 D_84b90 (4 * dwpl)%Z.
      ld8 F_84b94 D_84b94 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_84b98 D_84b98 (4 * swpl)%Z.
      zand0 F_84b9c D_84b9c andi_3 ALs.
      zand0 F_84ba0 D_84ba0 andi_3 ALd.
      ld8 F_84ba4 D_84ba4 (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
      slli2 F_84ba8 D_84ba8 (4 * nfw)%Z.
      slti0 F_84bac D_84bac.
      sn F_84bb0 D_84bb0. sn F_84bb4 D_84bb4. sn F_84bb8 D_84bb8. sn F_84bbc D_84bbc. sn F_84bc0 D_84bc0.
      sn F_84bc4 D_84bc4. sn F_84bc8 D_84bc8.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rg3_X2 : forall (nolast f3 : bool) regs m (s psl pdl swpl dwpl dh : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nolast then 1 else 0))) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  (nolast = false ->
     (0 <= psl < 2 ^ 64)%Z /\ (0 <= pdl < 2 ^ 64)%Z /\ (psl mod 4 = 0)%Z /\ (pdl mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
     getr regs 10 = Z_to_bv 64 pdl /\
     rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) /\
     rdn SEGS m (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))) /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     (exists mk : word, rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk)) /\
     rg_rows m s dh) ->
  exists regs',
    msteps SEGS (mkst regs RG3_X2 m rom) (mkst regs' (if nolast then RG_E else RG3_L) m rom)
    /\ (nolast = false -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 6 = Z_to_bv 64 (4 * swpl)
                          /\ getr regs' 17 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 (- dh) /\ getr regs' 16 = Z_to_bv 64 32
                          /\ getr regs' 5 = Z_to_bv 64 (if f3 then 1 else 0) /\ getr regs' 14 = Z_to_bv 64 0
                          /\ getr regs' 7 = Z_to_bv 64 18446744073709551611 /\ getr regs' 28 = Z_to_bv 64 (psl + 4 * swpl)
                          /\ getr regs' 19 = Z_to_bv 64 31 /\ getr regs' 20 = Z_to_bv 64 pdl)
    /\ regs_agree (fun r => In r [5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 28]%list) regs regs'.
Proof.
  intros nolast f3 regs m s psl pdl swpl dwpl dh Hs Hs64 Hswpl Hdwpl Cnl H2 H14 HF.
  unfold RG3_X2, RG_E, RG3_L.
  destruct nolast.
  - eexists. split.
    { ld8 F_84cec D_84cec (s - 216)%Z (Z_to_bv 64 1) Cnl.
      stepb_ft F_84cf0 D_84cf0 ltac:(condR).
      stepj F_84cf4 D_84cf4.
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (Hpsl & Hpdl & ALs & ALd & Hdh & H10 & Cpsl & Cf3 & Cswpl & (mk & Cmk) & ROWS).
    destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
    eexists. split.
    + ld8 F_84cec D_84cec (s - 216)%Z (Z_to_bv 64 0) Cnl.
      stepb_tk F_84cf0 D_84cf0 ltac:(condR).
      ld8 F_84cf8 D_84cf8 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zand0 F_84cfc D_84cfc andi_3 ALs.
      stepb_tk F_84d00 D_84d00 ltac:(condR).
      sn F_84d08 D_84d08.
      ld8 F_84d0c D_84d0c (s - 144)%Z mk Cmk.
      sn F_84d10 D_84d10.
      slli2 F_84d14 D_84d14 (4 * dwpl)%Z.
      ld8 F_84d18 D_84d18 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_84d1c D_84d1c (4 * swpl)%Z.
      zand0 F_84d20 D_84d20 andi_3 ALd.
      ld8 F_84d24 D_84d24 (s - 160)%Z (Z_to_bv 64 c50) R50.
      ld8 F_84d28 D_84d28 (s - 200)%Z (Z_to_bv 64 c28) R28.
      subw_v F_84d2c D_84d2c (c28 - c50)%Z.
      ld8 F_84d30 D_84d30 (s - 184)%Z (Z_to_bv 64 c38) R38.
      ld8 F_84d34 D_84d34 (s - 192)%Z (Z_to_bv 64 c30) R30.
      zv F_84d38 D_84d38 (Z_to_bv 64 (c30 + c38)).
      ld8 F_84d3c D_84d3c (s - 168)%Z (Z_to_bv 64 c48) R48.
      sn F_84d40 D_84d40.
      sn F_84d44 D_84d44. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
      sn F_84d48 D_84d48.
      ld8 F_84d4c D_84d4c (s - 232)%Z (Z_to_bv 64 (if f3 then 1 else 0)) Cf3.
      sn F_84d50 D_84d50. fixv' (Z_to_bv 64 (if f3 then 1 else 0)) ltac:(apply andi1_if).
      slti0 F_84d54 D_84d54.
      zv F_84d58 D_84d58 (Z_to_bv 64 (c30 + c38 + Z.min 0 c48)).
      sn F_84d5c D_84d5c.
      subw_v F_84d60 D_84d60 (c30 + c38 + Z.min 0 c48 - c50)%Z.
      ld8 F_84d64 D_84d64 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zv F_84d68 D_84d68 (Z_to_bv 64 (psl + 4 * swpl)).
      ld8 F_84d6c D_84d6c (s - 176)%Z (Z_to_bv 64 c40) R40.
      subw_v F_84d70 D_84d70 (c30 + c38 + Z.min 0 c48 - c50 - c40)%Z.
      sn F_84d74 D_84d74.
      sn F_84d78 D_84d78. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 + Z.min 0 c48 - c50 - c40))) ltac:(apply and_srai63_min; lia).
      subw_v F_84d7c D_84d7c (- dh)%Z.
      sn F_84d80 D_84d80.
      sn F_84d84 D_84d84.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

Lemma jt3_gen_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 RG3_JT) 4 = Some (Z_to_le_bytes 4 RG3_JTV).
Proof. unfold RG3_JT, RG3_JTV. vm_refl_bv. Qed.

End Segs3G.
