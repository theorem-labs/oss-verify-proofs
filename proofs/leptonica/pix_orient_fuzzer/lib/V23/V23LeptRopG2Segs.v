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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropLow_85000_86000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition RG2_S1 : word := 0x85718.
Definition RG2_F : word := 0x857a0.
Definition RG2_X1 : word := 0x85890.
Definition RG2_H2 : word := 0x858e0.
Definition RG2_I : word := 0x85904.
Definition RG2_T2 : word := 0x859a0.
Definition RG2_X2 : word := 0x85a10.
Definition RG2_L : word := 0x85aa8.
Definition RG2_JT : Z := 0x1f39c.
Definition RG2_JTV : Z := 418688.

Section Segs2G.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac rg2_post := repeat split; gres; pin; try reflexivity; solve_regs_agree.
Ltac std F D aa SOK :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa); [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; reflexivity | exact SOK ]
  | step_simpl ].
Ltac rgF_tail2 n pd d4 psf off s4 s bd Rd Ld SOK Cz :=
  stepb_tk F_85814 D_85814 ltac:(condR);
  stepb_tk F_8581c D_8581c ltac:(condZ);
  ld4 F_85824 D_85824 pd bd Rd Ld;
  sn F_85828 D_85828; sn F_8582c D_8582c; sn F_85830 D_85830;
  zv F_85834 D_85834 (Z_to_bv 64 (pd + d4));
  stw F_85838 D_85838 (Z_to_bv 64 pd) SOK;
  stepb_tk F_8583c D_8583c ltac:(condZ);
  sltu0 F_85844 D_85844; sn F_85848 D_85848; sn F_8584c D_8584c;
  stepb_tk F_85850 D_85850 ltac:(condR);
  zv F_85858 D_85858 (Z_to_bv 64 (psf + off + s4));
  stepb_tk F_8585c D_8585c ltac:(condZ);
  sltu0 F_85864 D_85864;
  ld8w F_85868 D_85868 (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_8586c D_8586c; sn F_85870 D_85870;
  stepb_tk F_85874 D_85874 ltac:(condR);
  sn F_8587c D_8587c; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_85880 D_85880 (Z_to_bv 64 (off + s4));
  zv F_85884 D_85884 (Z_to_bv 64 (pd + d4));
  sn F_85888 D_85888;
  first [ stepb_ft F_8588c D_8588c ltac:(condSe) | stepb_tk F_8588c D_8588c ltac:(condSe) ]; apply mst_refl.
(* [comment removed for export] *)
Lemma rg2_F : forall (f6 f7 last : bool) regs m (s psf off pd s4 d4 n sls : Z) (sv : word) (bs0 bs1 bd : list byte),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= psf)%Z -> (0 <= off)%Z -> (0 <= s4)%Z -> (0 <= d4)%Z ->
  (1 <= psf + off)%Z -> (psf + off + s4 < 2 ^ 64)%Z -> (1 <= pd)%Z -> (pd + d4 < 2 ^ 64)%Z -> (pd + 4 < 2 ^ 64)%Z ->
  (pd + 4 <= s - 240 \/ s <= pd)%Z ->
  (1 <= n < 2 ^ 31)%Z -> (if last then n = 1 else 1 < n)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psf + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  (f6 = true -> f7 = false -> psf + off + 8 < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 (psf + off + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 240)) 8 = Some (word_to_le_bytes 8 sv) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 15 = Z_to_bv 64 psf -> getr regs 11 = Z_to_bv 64 off ->
  getr regs 25 = Z_to_bv 64 pd -> getr regs 16 = Z_to_bv 64 pd -> getr regs 28 = Z_to_bv 64 (- n) ->
  getr regs 24 = Z_to_bv 64 s4 -> getr regs 5 = Z_to_bv 64 d4 -> getr regs 7 = Z_to_bv 64 (psf + s4) ->
  getr regs 19 = Z_to_bv 64 (if f6 then 1 else 0) -> getr regs 23 = Z_to_bv 64 (if f7 then 1 else 0) ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 0 -> getr regs 1 = Z_to_bv 64 31 -> getr regs 22 = Z_to_bv 64 32 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG2_F m rom)
                (mkst regs' (if last then RG2_X1 else RG2_F) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + s4) /\ getr regs' 25 = Z_to_bv 64 (pd + d4) /\ getr regs' 16 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 28 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [11; 12; 16; 17; 21; 25; 26; 28]%list) regs regs'.
Proof.
  intros f6 f7 last regs m s psf off pd s4 d4 n sls sv bs0 bs1 bd Hs Hs64 Hpsf Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cz Csv H2 H15 H11 H25 H16 H28 H13 H7 H20 H19 H24 H22 H23 H9 H1 H22b H30 H8.
  unfold RG2_F, RG2_X1.
  destruct f6; [destruct f7|].
  - destruct last; eexists; eexists; (split; [
      zv F_857a0 D_857a0 (Z_to_bv 64 (psf + off));
      snez1 F_857a4 D_857a4;
      sn F_857a8 D_857a8;
      stepb_ft F_857ac D_857ac ltac:(condR);
      stepb_tk F_857b0 D_857b0 ltac:(condR);
      stepb_tk F_857b8 D_857b8 ltac:(condZ);
      ld4 F_857c0 D_857c0 (psf + off)%Z bs0 R0 L0;
      sn F_857c4 D_857c4;
      stepb_tk F_857c8 D_857c8 ltac:(condR);
      rgF_tail2 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg2_post ]).
  - destruct (R1 eq_refl eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      zv F_857a0 D_857a0 (Z_to_bv 64 (psf + off));
      snez1 F_857a4 D_857a4;
      sn F_857a8 D_857a8;
      stepb_ft F_857ac D_857ac ltac:(condR);
      stepb_tk F_857b0 D_857b0 ltac:(condR);
      stepb_tk F_857b8 D_857b8 ltac:(condZ);
      ld4 F_857c0 D_857c0 (psf + off)%Z bs0 R0 L0;
      sn F_857c4 D_857c4;
      stepb_ft F_857c8 D_857c8 ltac:(condR);
      sn F_857cc D_857cc;
      stepb_tk F_857d0 D_857d0 ltac:(condZ);
      stepb_tk F_857d8 D_857d8 ltac:(condZ);
      ld4 F_857e0 D_857e0 (psf + off + 4)%Z bs1 R1' L1;
      ld8 F_857e4 D_857e4 (s - 240)%Z sv Csv;
      sn F_857e8 D_857e8; sn F_857ec D_857ec; sn F_857f0 D_857f0; sn F_857f4 D_857f4;
      stepj F_857f8 D_857f8;
      rgF_tail2 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg2_post ]).
  - destruct last; eexists; eexists; (split; [
      zv F_857a0 D_857a0 (Z_to_bv 64 (psf + off));
      snez1 F_857a4 D_857a4;
      sn F_857a8 D_857a8;
      stepb_tk F_857ac D_857ac ltac:(condR);
      stepb_tk F_857fc D_857fc ltac:(condR);
      stepb_tk F_85804 D_85804 ltac:(condZ);
      ld4 F_8580c D_8580c (psf + off)%Z bs0 R0 L0;
      sn F_85810 D_85810;
      rgF_tail2 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg2_post ]).
Qed.

(* [comment removed for export] *)
Lemma rg2_L : forall (f3 last : bool) regs m (s psl off pd s4 d4 n sls : Z) (mk : word) (bs0 bs1 bd : list byte),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= psl)%Z -> (0 <= off)%Z -> (0 <= s4)%Z -> (0 <= d4)%Z ->
  (1 <= psl + off)%Z -> (psl + off + s4 < 2 ^ 64)%Z -> (1 <= pd)%Z -> (pd + d4 < 2 ^ 64)%Z -> (pd + 4 < 2 ^ 64)%Z ->
  (pd + 4 <= s - 240 \/ s <= pd)%Z ->
  (1 <= n < 2 ^ 31)%Z -> (if last then n = 1 else 1 < n)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psl + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  (f3 = false -> psl + off + 8 < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 (psl + off + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 off -> getr regs 10 = Z_to_bv 64 pd -> getr regs 19 = Z_to_bv 64 pd ->
  getr regs 28 = Z_to_bv 64 (- n) -> getr regs 17 = Z_to_bv 64 (if f3 then 1 else 0) ->
  getr regs 15 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 -> getr regs 5 = Z_to_bv 64 18446744073709551611 ->
  getr regs 9 = Z_to_bv 64 31 -> getr regs 16 = Z_to_bv 64 32 ->
  getr regs 7 = Z_to_bv 64 (psl + s4) -> getr regs 13 = Z_to_bv 64 d4 -> getr regs 6 = Z_to_bv 64 s4 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) -> getr regs 22 = mk ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG2_L m rom)
                (mkst regs' (if last then RG_E else RG2_L) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + s4) /\ getr regs' 10 = Z_to_bv 64 (pd + d4) /\ getr regs' 19 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 28 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [10; 11; 18; 19; 20; 21; 28]%list) regs regs'.
Proof.
  intros f3 last regs m s psl off pd s4 d4 n sls mk bs0 bs1 bd Hs Hs64 Hpsl Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cpsl Cz H2 H11 H10 H19 H28 H17 H15 H14 H5 H9 H16 H7 H13 H6 H30 H8 H22.
  unfold RG2_L, RG_E.
  destruct f3.
  - destruct last; eexists; eexists; (split; [
      ld8 F_85aa8 D_85aa8 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_85aac D_85aac (Z_to_bv 64 (psl + off));
      stepb_tk F_85ab0 D_85ab0 ltac:(condZ);
      stepb_tk F_85ab8 D_85ab8 ltac:(condZ);
      ld4 F_85ac0 D_85ac0 (psl + off)%Z bs0 R0 L0;
      sn F_85ac4 D_85ac4;
      stepb_tk F_85ac8 D_85ac8 ltac:(condR);
      stepb_tk F_85af0 D_85af0 ltac:(condR);
      stepb_tk F_85af8 D_85af8 ltac:(condZ);
      ld4 F_85b00 D_85b00 pd bd Rd Ld;
      sn F_85b04 D_85b04; sn F_85b08 D_85b08; sn F_85b0c D_85b0c;
      zv F_85b10 D_85b10 (Z_to_bv 64 (pd + d4));
      stw F_85b14 D_85b14 (Z_to_bv 64 pd) SOK;
      stepb_tk F_85b18 D_85b18 ltac:(condZ);
      sltu0 F_85b20 D_85b20; sn F_85b24 D_85b24; sn F_85b28 D_85b28;
      stepb_tk F_85b2c D_85b2c ltac:(condR);
      zv F_85b34 D_85b34 (Z_to_bv 64 (psl + off + s4));
      stepb_tk F_85b38 D_85b38 ltac:(condZ);
      sltu0 F_85b40 D_85b40;
      ld8w F_85b44 D_85b44 (s - 120)%Z (Z_to_bv 64 0) Cz;
      sn F_85b48 D_85b48; sn F_85b4c D_85b4c;
      stepb_tk F_85b50 D_85b50 ltac:(condR);
      sn F_85b58 D_85b58; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
      zv F_85b5c D_85b5c (Z_to_bv 64 (off + s4));
      zv F_85b60 D_85b60 (Z_to_bv 64 (pd + d4));
      sn F_85b64 D_85b64;
      first [ stepb_ft F_85b68 D_85b68 ltac:(condSe); stepj F_85b6c D_85b6c | stepb_tk F_85b68 D_85b68 ltac:(condSe) ]; apply mst_refl
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ]).
  - destruct (R1 eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      ld8 F_85aa8 D_85aa8 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_85aac D_85aac (Z_to_bv 64 (psl + off));
      stepb_tk F_85ab0 D_85ab0 ltac:(condZ);
      stepb_tk F_85ab8 D_85ab8 ltac:(condZ);
      ld4 F_85ac0 D_85ac0 (psl + off)%Z bs0 R0 L0;
      sn F_85ac4 D_85ac4;
      stepb_ft F_85ac8 D_85ac8 ltac:(condR);
      stepb_tk F_85acc D_85acc ltac:(condZ);
      stepb_tk F_85ad4 D_85ad4 ltac:(condZ);
      ld4 F_85adc D_85adc (psl + off + 4)%Z bs1 R1' L1;
      sn F_85ae0 D_85ae0; sn F_85ae4 D_85ae4; sn F_85ae8 D_85ae8; sn F_85aec D_85aec;
      stepb_tk F_85af0 D_85af0 ltac:(condR);
      stepb_tk F_85af8 D_85af8 ltac:(condZ);
      ld4 F_85b00 D_85b00 pd bd Rd Ld;
      sn F_85b04 D_85b04; sn F_85b08 D_85b08; sn F_85b0c D_85b0c;
      zv F_85b10 D_85b10 (Z_to_bv 64 (pd + d4));
      stw F_85b14 D_85b14 (Z_to_bv 64 pd) SOK;
      stepb_tk F_85b18 D_85b18 ltac:(condZ);
      sltu0 F_85b20 D_85b20; sn F_85b24 D_85b24; sn F_85b28 D_85b28;
      stepb_tk F_85b2c D_85b2c ltac:(condR);
      zv F_85b34 D_85b34 (Z_to_bv 64 (psl + off + s4));
      stepb_tk F_85b38 D_85b38 ltac:(condZ);
      sltu0 F_85b40 D_85b40;
      ld8w F_85b44 D_85b44 (s - 120)%Z (Z_to_bv 64 0) Cz;
      sn F_85b48 D_85b48; sn F_85b4c D_85b4c;
      stepb_tk F_85b50 D_85b50 ltac:(condR);
      sn F_85b58 D_85b58; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
      zv F_85b5c D_85b5c (Z_to_bv 64 (off + s4));
      zv F_85b60 D_85b60 (Z_to_bv 64 (pd + d4));
      sn F_85b64 D_85b64;
      first [ stepb_ft F_85b68 D_85b68 ltac:(condSe); stepj F_85b6c D_85b6c | stepb_tk F_85b68 D_85b68 ltac:(condSe) ]; apply mst_refl
    | repeat split; gres; pin; try reflexivity; solve_regs_agree ]).
Qed.

(* [comment removed for export] *)
Lemma rg2_H2 : forall regs m (s nfw psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= nfw < 2 ^ 26)%Z -> (1 <= psrow < 2 ^ 64)%Z -> (1 <= pdrow < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)) ->
  rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  rdn SEGS m (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow ->
  exists regs',
    msteps SEGS (mkst regs RG2_H2 m rom) (mkst regs' RG2_I m rom)
    /\ getr regs' 27 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 28 = Z_to_bv 64 1
    /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [9; 12; 16; 21; 27; 28]%list) regs regs'.
Proof.
  intros regs m s nfw psrow pdrow Hs Hs64 Hnfw Hps Hpd Cnfw C208 C224 H2 H6 H18.
  unfold RG2_H2, RG2_I. eexists. split.
  - ld8 F_858e0 D_858e0 (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
    stepb_ft F_858e4 D_858e4 ltac:(condZ).
    sn F_858e8 D_858e8.
    snez1 F_858ec D_858ec.
    snez1 F_858f0 D_858f0.
    ld8 F_858f4 D_858f4 (s - 224)%Z (Z_to_bv 64 1) C224.
    sn F_858f8 D_858f8.
    ld8 F_858fc D_858fc (s - 208)%Z (Z_to_bv 64 1) C208.
    sn F_85900 D_85900.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.
Lemma rg2_I : forall (last : bool) regs m (psrow pdrow off n4 sls : Z) (bs0 bs1 bd : list byte),
  (0 <= off)%Z -> (off + 4 <= n4)%Z -> (if last then off + 4 = n4 else off + 4 < n4)%Z -> (n4 < 2 ^ 28)%Z ->
  (1 <= psrow)%Z -> (psrow + n4 + 4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + n4 < 2 ^ 64)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psrow + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (psrow + off + 4)) 4 = Some bs1 -> length bs1 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (pdrow + off)) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 (pdrow + off)) 4 = true ->
  getr regs 24 = Z_to_bv 64 psrow -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 22 = Z_to_bv 64 pdrow ->
  getr regs 18 = Z_to_bv 64 pdrow -> getr regs 27 = Z_to_bv 64 off -> getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 16 = Z_to_bv 64 1 -> getr regs 28 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 32 -> getr regs 26 = Z_to_bv 64 18446744073709551611 -> getr regs 19 = Z_to_bv 64 31 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG2_I m rom) (mkst regs' (if last then RG2_T2 else RG2_I) (wbytes m (Z_to_bv 64 (pdrow + off)) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 27 = Z_to_bv 64 (off + 4)
    /\ regs_agree (fun r => In r [1; 12; 15; 17; 27]%list) regs regs'.
Proof.
  intros last regs m psrow pdrow off n4 sls bs0 bs1 bd Hoff Hn4 Hlast Hn4b Hps1 Hps2 Hpd1 Hpd2 Hsls R0 L0 R1 L1 RD LD SOK
    H24 H6 H22 H18 H27 H20 H16 H28 H9 H21 H25 H26 H19 H30 H8.
  unfold RG2_I, RG2_T2.
  destruct last; eexists; eexists; (split; [
    zv F_85904 D_85904 (Z_to_bv 64 (psrow + off));
    stepb_tk F_85908 D_85908 ltac:(condZ);
    seqz0 F_85910 D_85910;
    sn F_85914 D_85914;
    stepb_tk F_85918 D_85918 ltac:(condR);
    stepb_tk F_85920 D_85920 ltac:(condR);
    stepb_tk F_85928 D_85928 ltac:(condZ);
    zv F_85930 D_85930 (Z_to_bv 64 (psrow + off));
    stepb_tk F_85934 D_85934 ltac:(condZ);
    stepb_tk F_8593c D_8593c ltac:(condZ);
    zv F_85944 D_85944 (Z_to_bv 64 (pdrow + off));
    stepb_tk F_85948 D_85948 ltac:(condZ);
    seqz0 F_85950 D_85950;
    sn F_85954 D_85954;
    stepb_tk F_85958 D_85958 ltac:(condR);
    stepb_tk F_85960 D_85960 ltac:(condR);
    ld4 F_85968 D_85968 (psrow + off)%Z bs0 R0 L0;
    ld4 F_8596c D_8596c (psrow + off + 4)%Z bs1 R1 L1;
    zv F_85970 D_85970 (Z_to_bv 64 (pdrow + off));
    ld4 F_85974 D_85974 (pdrow + off)%Z bd RD LD;
    sn F_85978 D_85978; sn F_8597c D_8597c; sn F_85980 D_85980; sn F_85984 D_85984; sn F_85988 D_85988;
    sn F_8598c D_8598c; sn F_85990 D_85990;
    zv F_85994 D_85994 (Z_to_bv 64 (off + 4));
    stw F_85998 D_85998 (Z_to_bv 64 (pdrow + off)) SOK;
    first [ stepb_ft F_8599c D_8599c ltac:(condZ) | stepb_tk F_8599c D_8599c ltac:(condZ) ]; apply mst_refl
  | repeat split; gres; pin; try reflexivity; solve_regs_agree ]).
Qed.
Lemma rg2_T2 : forall (last : bool) regs m (s i dh d4 s4 psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 <= dh)%Z -> (dh < 2 ^ 31)%Z -> (if last then i + 1 = dh else i + 1 < dh)%Z ->
  (0 <= d4)%Z -> (0 <= s4)%Z -> (1 <= psrow)%Z -> (psrow + s4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + d4 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 i -> getr regs 5 = Z_to_bv 64 d4 -> getr regs 7 = Z_to_bv 64 s4 ->
  getr regs 6 = Z_to_bv 64 psrow -> getr regs 24 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow -> getr regs 22 = Z_to_bv 64 pdrow ->
  getr regs 23 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs RG2_T2 m rom) (mkst regs' (if last then RG2_X2 else RG2_H2) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 6 = Z_to_bv 64 (psrow + s4) /\ getr regs' 24 = Z_to_bv 64 (psrow + s4)
    /\ getr regs' 18 = Z_to_bv 64 (pdrow + d4) /\ getr regs' 22 = Z_to_bv 64 (pdrow + d4)
    /\ regs_agree (fun r => In r [6; 11; 12; 15; 16; 18; 22; 24]%list) regs regs'.
Proof.
  intros last regs m s i dh d4 s4 psrow pdrow Hs Hs64 Hi Hidh Hdh Hlast Hd4 Hs4 Hps1 Hps2 Hpd1 Hpd2 Cz Cdh
    H2 H11 H5 H7 H6 H24 H18 H22 H23.
  unfold RG2_T2, RG2_X2, RG2_H2.
  destruct last; eexists; (split; [
    zv F_859a0 D_859a0 (Z_to_bv 64 (pdrow + d4));
    snez1 F_859a4 D_859a4;
    seqz0 F_859a8 D_859a8;
    stepb_tk F_859ac D_859ac ltac:(condR);
    sltu0 F_859b4 D_859b4;
    sn F_859b8 D_859b8; sn F_859bc D_859bc;
    stepb_tk F_859c0 D_859c0 ltac:(condR);
    zv F_859c8 D_859c8 (Z_to_bv 64 (psrow + s4));
    snez1 F_859cc D_859cc;
    seqz0 F_859d0 D_859d0;
    stepb_tk F_859d4 D_859d4 ltac:(condR);
    sltu0 F_859dc D_859dc;
    ld8 F_859e0 D_859e0 (s - 120)%Z (Z_to_bv 64 0) Cz;
    sn F_859e4 D_859e4; sn F_859e8 D_859e8;
    stepb_tk F_859ec D_859ec ltac:(condR);
    zv F_859f4 D_859f4 (Z_to_bv 64 (pdrow + d4));
    sn F_859f8 D_859f8; fixv' (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
    zv F_859fc D_859fc (Z_to_bv 64 (pdrow + d4));
    zv F_85a00 D_85a00 (Z_to_bv 64 (psrow + s4));
    sn F_85a04 D_85a04;
    ld8 F_85a08 D_85a08 (s - 112)%Z (Z_to_bv 64 dh) Cdh;
    first [ stepb_ft F_85a0c D_85a0c ltac:(condZ) | stepb_tk F_85a0c D_85a0c ltac:(condZ) ]; apply mst_refl
  | repeat split; gres; pin; try reflexivity; solve_regs_agree ]).
Qed.
(* [comment removed for export] *)
Lemma rg2_S1 : forall (fw f6 f7 : bool) regs m (s dxb psf pdf swpl dwpl dh : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= dxb < 32)%Z -> (if fw then dxb <> 0 else dxb = 0)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 240)) 8 = true ->
  getr regs 1 = Z_to_bv 64 dxb -> getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  (fw = true ->
     (0 <= psf < 2 ^ 64)%Z /\ (0 <= pdf < 2 ^ 64)%Z /\ (psf mod 4 = 0)%Z /\ (pdf mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
     getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0) /\
     rdn SEGS m (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))) /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     rg_rows m s dh) ->
  exists regs' (sv : word),
    msteps SEGS (mkst regs RG2_S1 m rom) (mkst regs' (if fw then RG2_F else RG2_X1)
      (if fw then wbytes m (Z_to_bv 64 (s - 240)) (word_to_le_bytes 8 sv) else m) rom)
    /\ (fw = true -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 7 = Z_to_bv 64 (psf + 4 * swpl) /\ getr regs' 24 = Z_to_bv 64 (4 * swpl)
                     /\ getr regs' 5 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 16 = Z_to_bv 64 pdf /\ getr regs' 28 = Z_to_bv 64 (- dh)
                     /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 (if f6 then 1 else 0) /\ getr regs' 23 = Z_to_bv 64 (if f7 then 1 else 0)
                     /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 31
                     /\ getr regs' 22 = Z_to_bv 64 32)
    /\ regs_agree (fun r => In r [1; 5; 7; 9; 11; 12; 13; 16; 17; 19; 20; 22; 23; 24; 28]%list) regs regs'.
Proof.
  intros fw f6 f7 regs m s dxb psf pdf swpl dwpl dh Hs Hs64 Hdxb Hfw Hswpl Hdwpl SOK H1 H2 H14 HF.
  unfold RG2_S1, RG2_F, RG2_X1.
  destruct fw.
  2:{ exists regs, (Z_to_bv 64 0). split; [| split; [intros; discriminate | apply regs_agree_refl]].
      stepb_tk F_85718 D_85718 ltac:(condZ). apply mst_refl. }
  destruct (HF eq_refl) as (Hpsf & Hpdf & ALs & ALd & Hdh & H15 & H25 & H26 & Cf6 & Cswpl & ROWS).
  destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
  do 2 eexists. split.
  - stepb_ft F_85718 D_85718 ltac:(condZ).
    sn F_8571c D_8571c.
    sn F_85720 D_85720.
    std F_85724 D_85724 (Z_to_bv 64 (s - 240)) SOK.
    slli2 F_85728 D_85728 (4 * dwpl)%Z.
    ld8w F_8572c D_8572c (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
    slli2 F_85730 D_85730 (4 * swpl)%Z.
    zand0 F_85734 D_85734 andi_3 ALd.
    zand0 F_85738 D_85738 andi_3 ALs.
    ld8w F_8573c D_8573c (s - 160)%Z (Z_to_bv 64 c50) R50.
    ld8w F_85740 D_85740 (s - 200)%Z (Z_to_bv 64 c28) R28.
    subw_v F_85744 D_85744 (c28 - c50)%Z.
    ld8w F_85748 D_85748 (s - 184)%Z (Z_to_bv 64 c38) R38.
    ld8w F_8574c D_8574c (s - 192)%Z (Z_to_bv 64 c30) R30.
    zv F_85750 D_85750 (Z_to_bv 64 (c30 + c38)).
    ld8w F_85754 D_85754 (s - 168)%Z (Z_to_bv 64 c48) R48.
    sn F_85758 D_85758.
    ld8w F_8575c D_8575c (s - 224)%Z (Z_to_bv 64 (if f6 then 1 else 0)) Cf6.
    sn F_85760 D_85760. fixv' (Z_to_bv 64 (if f6 then 1 else 0)) ltac:(apply andi1_if).
    sn F_85764 D_85764.
    sn F_85768 D_85768. fixv' (Z_to_bv 64 (if f7 then 1 else 0)) ltac:(apply andi1_if).
    sn F_8576c D_8576c.
    sn F_85770 D_85770. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
    subw_v F_85774 D_85774 (c30 + c38 - c50)%Z.
    zv F_85778 D_85778 (Z_to_bv 64 (psf + 4 * swpl)).
    sn F_8577c D_8577c.
    ld8w F_85780 D_85780 (s - 176)%Z (Z_to_bv 64 c40) R40.
    subw_v F_85784 D_85784 (c30 + c38 - c50 - c40)%Z.
    addw_v F_85788 D_85788 (c30 + c38 - c50 - c40 + Z.min 0 c48)%Z.
    sn F_8578c D_8578c.
    sn F_85790 D_85790. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 - c50 - c40 + Z.min 0 c48))) ltac:(apply and_srai63_min; lia).
    subw_v F_85794 D_85794 (- dh)%Z.
    slti0 F_85798 D_85798.
    sn F_8579c D_8579c.
    apply mst_refl.
  - split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rg2_X1 : forall (nofull : bool) regs m (s psF pdF nfw swpl dwpl : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z -> (0 <= nfw < 2 ^ 26)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0))) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  (nofull = false ->
     (0 <= psF < 2 ^ 64)%Z /\ (0 <= pdF < 2 ^ 64)%Z /\ (psF mod 4 = 0)%Z /\ (pdF mod 4 = 0)%Z /\
     getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)) /\
     store_ok SEGS m (Z_to_bv 64 (s - 208)) 8 = true /\ store_ok SEGS m (Z_to_bv 64 (s - 224)) 8 = true) ->
  exists regs',
    msteps SEGS (mkst regs RG2_X1 m rom) (mkst regs' (if nofull then RG2_X2 else RG2_H2)
      (if nofull then m else wbytes (wbytes m (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                                    (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 1))) rom)
    /\ (nofull = false -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 5 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 7 = Z_to_bv 64 (4 * swpl)
                          /\ getr regs' 20 = Z_to_bv 64 (4 * nfw) /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 32
                          /\ getr regs' 26 = Z_to_bv 64 18446744073709551611
                          /\ getr regs' 19 = Z_to_bv 64 31 /\ getr regs' 24 = Z_to_bv 64 psF /\ getr regs' 22 = Z_to_bv 64 pdF)
    /\ regs_agree (fun r => In r [5; 7; 11; 12; 13; 15; 19; 20; 22; 23; 24; 25; 26]%list) regs regs'.
Proof.
  intros nofull regs m s psF pdF nfw swpl dwpl Hs Hs64 Hswpl Hdwpl Hnfw Cnf H2 H14 HF.
  unfold RG2_X1, RG2_X2, RG2_H2.
  destruct nofull.
  - eexists. split.
    { ld8 F_85890 D_85890 (s - 208)%Z (Z_to_bv 64 1) Cnf.
      stepb_tk F_85894 D_85894 ltac:(condR).
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (HpsF & HpdF & ALs & ALd & H6 & H18 & Cswpl & Cnfw & SOK1 & SOK2).
    assert (SOK2' : store_ok SEGS (wbytes m (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 (s - 224)) 8 = true)
      by (eapply store_ok_mono; [apply wbytes_grows | exact SOK2]).
    eexists. split.
    + ld8 F_85890 D_85890 (s - 208)%Z (Z_to_bv 64 0) Cnf.
      stepb_ft F_85894 D_85894 ltac:(condR).
      sn F_85898 D_85898.
      slli2 F_8589c D_8589c (4 * dwpl)%Z.
      ld8 F_858a0 D_858a0 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_858a4 D_858a4 (4 * swpl)%Z.
      zand0 F_858a8 D_858a8 andi_3 ALs.
      zand0 F_858ac D_858ac andi_3 ALd.
      ld8 F_858b0 D_858b0 (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
      slli2 F_858b4 D_858b4 (4 * nfw)%Z.
      slti0 F_858b8 D_858b8.
      sn F_858bc D_858bc. sn F_858c0 D_858c0. sn F_858c4 D_858c4.
      std F_858c8 D_858c8 (Z_to_bv 64 (s - 208)) SOK1.
      sn F_858cc D_858cc.
      std F_858d0 D_858d0 (Z_to_bv 64 (s - 224)) SOK2'.
      sn F_858d4 D_858d4. sn F_858d8 D_858d8. sn F_858dc D_858dc.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rg2_X2 : forall (nolast f3 : bool) regs m (s psl pdl swpl dwpl dh : Z),
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
    msteps SEGS (mkst regs RG2_X2 m rom) (mkst regs' (if nolast then RG_E else RG2_L) m rom)
    /\ (nolast = false -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 6 = Z_to_bv 64 (4 * swpl)
                          /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 28 = Z_to_bv 64 (- dh) /\ getr regs' 16 = Z_to_bv 64 32
                          /\ getr regs' 17 = Z_to_bv 64 (if f3 then 1 else 0) /\ getr regs' 14 = Z_to_bv 64 0
                          /\ getr regs' 5 = Z_to_bv 64 18446744073709551611 /\ getr regs' 7 = Z_to_bv 64 (psl + 4 * swpl)
                          /\ getr regs' 9 = Z_to_bv 64 31 /\ getr regs' 19 = Z_to_bv 64 pdl)
    /\ regs_agree (fun r => In r [5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 22; 28]%list) regs regs'.
Proof.
  intros nolast f3 regs m s psl pdl swpl dwpl dh Hs Hs64 Hswpl Hdwpl Cnl H2 H14 HF.
  unfold RG2_X2, RG_E, RG2_L.
  destruct nolast.
  - eexists. split.
    { ld8 F_85a10 D_85a10 (s - 216)%Z (Z_to_bv 64 1) Cnl.
      stepb_ft F_85a14 D_85a14 ltac:(condR).
      sn F_85a18 D_85a18.
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (Hpsl & Hpdl & ALs & ALd & Hdh & H10 & Cpsl & Cf3 & Cswpl & (mk & Cmk) & ROWS).
    destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
    eexists. split.
    + ld8 F_85a10 D_85a10 (s - 216)%Z (Z_to_bv 64 0) Cnl.
      stepb_tk F_85a14 D_85a14 ltac:(condR).
      ld8 F_85a1c D_85a1c (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zand0 F_85a20 D_85a20 andi_3 ALs.
      stepb_tk F_85a24 D_85a24 ltac:(condR).
      sn F_85a2c D_85a2c.
      slli2 F_85a30 D_85a30 (4 * dwpl)%Z.
      ld8 F_85a34 D_85a34 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_85a38 D_85a38 (4 * swpl)%Z.
      zand0 F_85a3c D_85a3c andi_3 ALd.
      ld8 F_85a40 D_85a40 (s - 160)%Z (Z_to_bv 64 c50) R50.
      ld8 F_85a44 D_85a44 (s - 200)%Z (Z_to_bv 64 c28) R28.
      subw_v F_85a48 D_85a48 (c28 - c50)%Z.
      ld8 F_85a4c D_85a4c (s - 184)%Z (Z_to_bv 64 c38) R38.
      ld8 F_85a50 D_85a50 (s - 192)%Z (Z_to_bv 64 c30) R30.
      zv F_85a54 D_85a54 (Z_to_bv 64 (c30 + c38)).
      ld8 F_85a58 D_85a58 (s - 168)%Z (Z_to_bv 64 c48) R48.
      sn F_85a5c D_85a5c.
      sn F_85a60 D_85a60. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
      sn F_85a64 D_85a64.
      ld8 F_85a68 D_85a68 (s - 232)%Z (Z_to_bv 64 (if f3 then 1 else 0)) Cf3.
      sn F_85a6c D_85a6c. fixv' (Z_to_bv 64 (if f3 then 1 else 0)) ltac:(apply andi1_if).
      slti0 F_85a70 D_85a70.
      zv F_85a74 D_85a74 (Z_to_bv 64 (c30 + c38 + Z.min 0 c48)).
      sn F_85a78 D_85a78.
      subw_v F_85a7c D_85a7c (c30 + c38 + Z.min 0 c48 - c50)%Z.
      ld8 F_85a80 D_85a80 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zv F_85a84 D_85a84 (Z_to_bv 64 (psl + 4 * swpl)).
      ld8 F_85a88 D_85a88 (s - 176)%Z (Z_to_bv 64 c40) R40.
      subw_v F_85a8c D_85a8c (c30 + c38 + Z.min 0 c48 - c50 - c40)%Z.
      sn F_85a90 D_85a90.
      sn F_85a94 D_85a94. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 + Z.min 0 c48 - c50 - c40))) ltac:(apply and_srai63_min; lia).
      subw_v F_85a98 D_85a98 (- dh)%Z.
      sn F_85a9c D_85a9c.
      sn F_85aa0 D_85aa0.
      ld8 F_85aa4 D_85aa4 (s - 144)%Z mk Cmk.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

Lemma jt2_gen_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 RG2_JT) 4 = Some (Z_to_le_bytes 4 RG2_JTV).
Proof. unfold RG2_JT, RG2_JTV. vm_refl_bv. Qed.

End Segs2G.
