(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith GrayLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptUb V2_code_rasteropLow_2e000_2f000 V2_code_rasteropLow_2f000_2f8a8.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac sltu0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
Ltac slti0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
Ltac snez1 F D := sn F D; fixv' (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
Ltac ld8 F D a v H := stepLD F D (word_to_le_bytes 8 v) v ltac:(rdn_addr a; rdn_by H) ltac:(apply bytes_le_to_Z_8).
Ltac ld8w F D a v H := stepLD F D (word_to_le_bytes 8 v) v
  ltac:(rdn_addr a; rewrite rdn_wbytes_out_Z; [exact H | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia])
  ltac:(apply bytes_le_to_Z_8).
Ltac ld4 F D a bs H L := stepLD F D bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(rdn_addr a; exact H) ltac:(symmetry; apply u_lez4; exact L).
Ltac slli2 F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
Ltac zand0 F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM, u_Z2bv by lia; rewrite EQ; reflexivity).
Ltac subw_v F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite subw_fit by lia; f_equal; lia).
Ltac addw_v F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(rewrite addw_fit by lia; f_equal; lia).
Ltac condSe := pin; rewrite ?c_eq_Zs by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
Ltac stw F D aa SOK :=
  chain_step;
  [ reflexivity
  | eapply step_sw_at with (a := aa); [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; reflexivity | exact SOK ]
  | step_simpl ].

Definition RG_S1 : word := 0x2efc0.
Definition RG_F : word := 0x2f048.
Definition RG_X1 : word := 0x2f138.
Definition RG_H2 : word := 0x2f180.
Definition RG_I : word := 0x2f19c.
Definition RG_T2 : word := 0x2f22c.
Definition RG_X2 : word := 0x2f29c.
Definition RG_L : word := 0x2f334.
Definition RG_E : word := 0x2f86c.
Definition RG_JT : Z := 0x12844.
Definition RG_JT12 : Z := 0x12870.
Definition RG_JT12V : Z := 116604.
Definition RG_MASKS : Z := 0x128ec.

Definition rg_rows (M : word -> option byte) (s dh : Z) : Prop :=
  exists c28 c30 c38 c40 c48 c50 : Z,
    rdn SEGS M (Z_to_bv 64 (s - 200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c28)) /\
    rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c30)) /\
    rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c38)) /\
    rdn SEGS M (Z_to_bv 64 (s - 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c40)) /\
    rdn SEGS M (Z_to_bv 64 (s - 168)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c48)) /\
    rdn SEGS M (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c50)) /\
    (- 2 ^ 28 <= c28 < 2 ^ 28)%Z /\ (- 2 ^ 28 <= c30 < 2 ^ 28)%Z /\ (- 2 ^ 28 <= c38 < 2 ^ 28)%Z /\
    (- 2 ^ 28 <= c40 < 2 ^ 28)%Z /\ (- 2 ^ 28 <= c48 < 2 ^ 28)%Z /\ (- 2 ^ 28 <= c50 < 2 ^ 28)%Z /\
    (c28 - c50 - Z.min 0 (c30 + c38 - c50 - c40 + Z.min 0 c48) = - dh)%Z.

Lemma andi1_if : forall b : bool, v_andi (Z_to_bv 64 (if b then 1 else 0)) 1 = Z_to_bv 64 (if b then 1 else 0).
Proof. intros []; apply bv_eq; reflexivity. Qed.

Lemma and_srai63_min : forall x, (- 2 ^ 63 <= x < 2 ^ 63)%Z -> v_and (v_srai (Z_to_bv 64 x) 63) (Z_to_bv 64 x) = Z_to_bv 64 (Z.min 0 x).
Proof.
  intros x Hx. destruct (Z_lt_le_dec x 0) as [N|P].
  - rewrite Z.min_r by lia. apply and_srai63_np. lia.
  - rewrite Z.min_l by lia. rewrite srai63_nn by lia. apply and_0_l.
Qed.

Section Segs2.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac rgF_tail n pd d4 psf off s4 s bd Rd Ld SOK Cz :=
  stepb_tk F_2f0bc D_2f0bc ltac:(condR);
  stepb_tk F_2f0c4 D_2f0c4 ltac:(condZ);
  ld4 F_2f0cc D_2f0cc pd bd Rd Ld;
  sn F_2f0d0 D_2f0d0; sn F_2f0d4 D_2f0d4; sn F_2f0d8 D_2f0d8;
  zv F_2f0dc D_2f0dc (Z_to_bv 64 (pd + d4));
  stw F_2f0e0 D_2f0e0 (Z_to_bv 64 pd) SOK;
  stepb_tk F_2f0e4 D_2f0e4 ltac:(condZ);
  sltu0 F_2f0ec D_2f0ec; sn F_2f0f0 D_2f0f0; sn F_2f0f4 D_2f0f4;
  stepb_tk F_2f0f8 D_2f0f8 ltac:(condR);
  zv F_2f100 D_2f100 (Z_to_bv 64 (psf + off + s4));
  stepb_tk F_2f104 D_2f104 ltac:(condZ);
  sltu0 F_2f10c D_2f10c;
  ld8w F_2f110 D_2f110 (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_2f114 D_2f114; sn F_2f118 D_2f118;
  stepb_tk F_2f11c D_2f11c ltac:(condR);
  sn F_2f124 D_2f124; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_2f128 D_2f128 (Z_to_bv 64 (off + s4));
  zv F_2f12c D_2f12c (Z_to_bv 64 (pd + d4));
  sn F_2f130 D_2f130;
  first [ stepb_ft F_2f134 D_2f134 ltac:(condSe) | stepb_tk F_2f134 D_2f134 ltac:(condSe) ]; apply mst_refl.
Ltac rgL_tail n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz :=
  stepb_tk F_2f37c D_2f37c ltac:(condR);
  stepb_tk F_2f384 D_2f384 ltac:(condZ);
  ld4 F_2f38c D_2f38c pd bd Rd Ld;
  ld8 F_2f390 D_2f390 (s - 144)%Z mk Cmk;
  sn F_2f394 D_2f394; sn F_2f398 D_2f398; sn F_2f39c D_2f39c;
  zv F_2f3a0 D_2f3a0 (Z_to_bv 64 (pd + d4));
  stw F_2f3a4 D_2f3a4 (Z_to_bv 64 pd) SOK;
  stepb_tk F_2f3a8 D_2f3a8 ltac:(condZ);
  sltu0 F_2f3b0 D_2f3b0; sn F_2f3b4 D_2f3b4; sn F_2f3b8 D_2f3b8;
  stepb_tk F_2f3bc D_2f3bc ltac:(condR);
  zv F_2f3c4 D_2f3c4 (Z_to_bv 64 (psl + off + s4));
  stepb_tk F_2f3c8 D_2f3c8 ltac:(condZ);
  sltu0 F_2f3d0 D_2f3d0;
  ld8w F_2f3d4 D_2f3d4 (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_2f3d8 D_2f3d8; sn F_2f3dc D_2f3dc;
  stepb_tk F_2f3e0 D_2f3e0 ltac:(condR);
  sn F_2f3e8 D_2f3e8; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_2f3ec D_2f3ec (Z_to_bv 64 (off + s4));
  zv F_2f3f0 D_2f3f0 (Z_to_bv 64 (pd + d4));
  sn F_2f3f4 D_2f3f4;
  first [ stepb_ft F_2f3f8 D_2f3f8 ltac:(condSe); stepj F_2f3fc D_2f3fc | stepb_tk F_2f3f8 D_2f3f8 ltac:(condSe) ]; apply mst_refl.
Ltac rg_post := repeat split; gres; pin; try reflexivity; solve_regs_agree.

(* [comment removed for export] *)
Lemma rg_F : forall (f6 f7 last : bool) regs m (s psf off pd s4 d4 n sls : Z) (bs0 bs1 bd : list byte),
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
    msteps SEGS (mkst regs RG_F m rom)
                (mkst regs' (if last then RG_X1 else RG_F) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + s4) /\ getr regs' 25 = Z_to_bv 64 (pd + d4) /\ getr regs' 16 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 28 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [11; 12; 16; 21; 25; 26; 28]%list) regs regs'.
Proof.
  intros f6 f7 last regs m s psf off pd s4 d4 n sls bs0 bs1 bd Hs Hs64 Hpsf Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cz H2 H15 H11 H25 H16 H28 H13 H7 H20 H19 H24 H22 H23 H9 H1 H30 H8.
  unfold RG_F, RG_X1.
  destruct f6; [destruct f7|].
  - destruct last; eexists; eexists; (split; [
      zv F_2f048 D_2f048 (Z_to_bv 64 (psf + off));
      snez1 F_2f04c D_2f04c;
      sn F_2f050 D_2f050;
      stepb_ft F_2f054 D_2f054 ltac:(condR);
      stepb_tk F_2f058 D_2f058 ltac:(condR);
      sn F_2f060 D_2f060;
      stepb_tk F_2f064 D_2f064 ltac:(condZ);
      ld4 F_2f06c D_2f06c (psf + off)%Z bs0 R0 L0;
      sn F_2f070 D_2f070;
      stepb_tk F_2f074 D_2f074 ltac:(condR);
      rgF_tail n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg_post ]).
  - destruct (R1 eq_refl eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      zv F_2f048 D_2f048 (Z_to_bv 64 (psf + off));
      snez1 F_2f04c D_2f04c;
      sn F_2f050 D_2f050;
      stepb_ft F_2f054 D_2f054 ltac:(condR);
      stepb_tk F_2f058 D_2f058 ltac:(condR);
      sn F_2f060 D_2f060;
      stepb_tk F_2f064 D_2f064 ltac:(condZ);
      ld4 F_2f06c D_2f06c (psf + off)%Z bs0 R0 L0;
      sn F_2f070 D_2f070;
      stepb_ft F_2f074 D_2f074 ltac:(condR);
      sn F_2f078 D_2f078;
      stepb_tk F_2f07c D_2f07c ltac:(condZ);
      stepb_tk F_2f084 D_2f084 ltac:(condZ);
      ld4 F_2f08c D_2f08c (psf + off + 4)%Z bs1 R1' L1;
      sn F_2f090 D_2f090; sn F_2f094 D_2f094; sn F_2f098 D_2f098; sn F_2f09c D_2f09c;
      stepj F_2f0a0 D_2f0a0;
      rgF_tail n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg_post ]).
  - destruct last; eexists; eexists; (split; [
      zv F_2f048 D_2f048 (Z_to_bv 64 (psf + off));
      snez1 F_2f04c D_2f04c;
      sn F_2f050 D_2f050;
      stepb_tk F_2f054 D_2f054 ltac:(condR);
      stepb_tk F_2f0a4 D_2f0a4 ltac:(condR);
      stepb_tk F_2f0ac D_2f0ac ltac:(condZ);
      ld4 F_2f0b4 D_2f0b4 (psf + off)%Z bs0 R0 L0;
      sn F_2f0b8 D_2f0b8;
      rgF_tail n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg_post ]).
Qed.

(* [comment removed for export] *)
Lemma rg_L : forall (f3 last : bool) regs m (s psl off pd s4 d4 n sls : Z) (mk : word) (bs0 bs1 bd : list byte),
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
    msteps SEGS (mkst regs RG_L m rom)
                (mkst regs' (if last then RG_E else RG_L) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + s4) /\ getr regs' 10 = Z_to_bv 64 (pd + d4) /\ getr regs' 20 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 9 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [9; 10; 11; 18; 20; 21; 22; 23]%list) regs regs'.
Proof.
  intros f3 last regs m s psl off pd s4 d4 n sls mk bs0 bs1 bd Hs Hs64 Hpsl Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cpsl Cmk Cz H2 H11 H10 H20 H9 H5 H17 H14 H7 H19 H16 H28 H15 H6 H30 H8.
  unfold RG_L, RG_E.
  destruct f3.
  - destruct last; eexists; eexists; (split; [
      ld8 F_2f334 D_2f334 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_2f338 D_2f338 (Z_to_bv 64 (psl + off));
      stepb_tk F_2f33c D_2f33c ltac:(condZ);
      stepb_tk F_2f344 D_2f344 ltac:(condZ);
      ld4 F_2f34c D_2f34c (psl + off)%Z bs0 R0 L0;
      sn F_2f350 D_2f350;
      stepb_tk F_2f354 D_2f354 ltac:(condR);
      rgL_tail n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | rg_post ]).
  - destruct (R1 eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      ld8 F_2f334 D_2f334 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_2f338 D_2f338 (Z_to_bv 64 (psl + off));
      stepb_tk F_2f33c D_2f33c ltac:(condZ);
      stepb_tk F_2f344 D_2f344 ltac:(condZ);
      ld4 F_2f34c D_2f34c (psl + off)%Z bs0 R0 L0;
      sn F_2f350 D_2f350;
      stepb_ft F_2f354 D_2f354 ltac:(condR);
      stepb_tk F_2f358 D_2f358 ltac:(condZ);
      stepb_tk F_2f360 D_2f360 ltac:(condZ);
      ld4 F_2f368 D_2f368 (psl + off + 4)%Z bs1 R1' L1;
      sn F_2f36c D_2f36c; sn F_2f370 D_2f370; sn F_2f374 D_2f374; sn F_2f378 D_2f378;
      rgL_tail n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | rg_post ]).
Qed.

(* [comment removed for export] *)
Lemma rg_H2 : forall regs m (s nfw psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= nfw < 2 ^ 26)%Z -> (1 <= psrow < 2 ^ 64)%Z -> (1 <= pdrow < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow ->
  getr regs 25 = Z_to_bv 64 1 -> getr regs 17 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (mkst regs RG_H2 m rom) (mkst regs' RG_I m rom)
    /\ getr regs' 24 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 28 = Z_to_bv 64 1
    /\ getr regs' 9 = Z_to_bv 64 1 /\ getr regs' 21 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [9; 12; 16; 21; 24; 28]%list) regs regs'.
Proof.
  intros regs m s nfw psrow pdrow Hs Hs64 Hnfw Hps Hpd Cnfw H2 H6 H18 H25 H17.
  unfold RG_H2, RG_I. eexists. split.
  - ld8 F_2f180 D_2f180 (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
    stepb_ft F_2f184 D_2f184 ltac:(condZ).
    sn F_2f188 D_2f188.
    snez1 F_2f18c D_2f18c.
    snez1 F_2f190 D_2f190.
    sn F_2f194 D_2f194.
    sn F_2f198 D_2f198.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma rg_I : forall (last : bool) regs m (psrow pdrow off n4 sls : Z) (bs0 bs1 : list byte),
  (0 <= off)%Z -> (off + 4 <= n4)%Z -> (if last then off + 4 = n4 else off + 4 < n4)%Z -> (n4 < 2 ^ 28)%Z ->
  (1 <= psrow)%Z -> (psrow + n4 + 4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + n4 < 2 ^ 64)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psrow + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (psrow + off + 4)) 4 = Some bs1 -> length bs1 = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 (pdrow + off)) 4 = true ->
  getr regs 27 = Z_to_bv 64 psrow -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 1 = Z_to_bv 64 pdrow -> getr regs 18 = Z_to_bv 64 pdrow ->
  getr regs 24 = Z_to_bv 64 off -> getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 16 = Z_to_bv 64 1 -> getr regs 28 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 32 -> getr regs 22 = Z_to_bv 64 18446744073709551611 -> getr regs 26 = Z_to_bv 64 31 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG_I m rom)
                (mkst regs' (if last then RG_T2 else RG_I) (wbytes m (Z_to_bv 64 (pdrow + off)) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 24 = Z_to_bv 64 (off + 4)
    /\ regs_agree (fun r => In r [12; 15; 24]%list) regs regs'.
Proof.
  intros last regs m psrow pdrow off n4 sls bs0 bs1 Hoff Hn4 Hlast Hn4b Hps1 Hps2 Hpd1 Hpd2 Hsls R0 L0 R1 L1 SOK
    H27 H6 H1 H18 H24 H20 H16 H28 H9 H21 H23 H22 H26 H30 H8.
  unfold RG_I, RG_T2.
  destruct last; eexists; eexists; (split; [
    zv F_2f19c D_2f19c (Z_to_bv 64 (psrow + off));
    stepb_tk F_2f1a0 D_2f1a0 ltac:(condZ);
    seqz0 F_2f1a8 D_2f1a8;
    sn F_2f1ac D_2f1ac;
    stepb_tk F_2f1b0 D_2f1b0 ltac:(condR);
    stepb_tk F_2f1b8 D_2f1b8 ltac:(condR);
    stepb_tk F_2f1c0 D_2f1c0 ltac:(condZ);
    zv F_2f1c8 D_2f1c8 (Z_to_bv 64 (psrow + off));
    stepb_tk F_2f1cc D_2f1cc ltac:(condZ);
    stepb_tk F_2f1d4 D_2f1d4 ltac:(condZ);
    zv F_2f1dc D_2f1dc (Z_to_bv 64 (pdrow + off));
    stepb_tk F_2f1e0 D_2f1e0 ltac:(condZ);
    seqz0 F_2f1e8 D_2f1e8;
    sn F_2f1ec D_2f1ec;
    stepb_tk F_2f1f0 D_2f1f0 ltac:(condR);
    stepb_tk F_2f1f8 D_2f1f8 ltac:(condR);
    ld4 F_2f200 D_2f200 (psrow + off)%Z bs0 R0 L0;
    ld4 F_2f204 D_2f204 (psrow + off + 4)%Z bs1 R1 L1;
    sn F_2f208 D_2f208; sn F_2f20c D_2f20c; sn F_2f210 D_2f210; sn F_2f214 D_2f214; sn F_2f218 D_2f218;
    zv F_2f21c D_2f21c (Z_to_bv 64 (pdrow + off));
    zv F_2f220 D_2f220 (Z_to_bv 64 (off + 4));
    stw F_2f224 D_2f224 (Z_to_bv 64 (pdrow + off)) SOK;
    first [ stepb_ft F_2f228 D_2f228 ltac:(condZ) | stepb_tk F_2f228 D_2f228 ltac:(condZ) ]; apply mst_refl
  | rg_post ]).
Qed.

Lemma rg_T2 : forall (last : bool) regs m (s i dh d4 s4 psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 <= dh)%Z -> (dh < 2 ^ 31)%Z -> (if last then i + 1 = dh else i + 1 < dh)%Z ->
  (0 <= d4)%Z -> (0 <= s4)%Z -> (1 <= psrow)%Z -> (psrow + s4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + d4 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 11 = Z_to_bv 64 i -> getr regs 5 = Z_to_bv 64 d4 -> getr regs 7 = Z_to_bv 64 s4 ->
  getr regs 6 = Z_to_bv 64 psrow -> getr regs 27 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow -> getr regs 1 = Z_to_bv 64 pdrow ->
  getr regs 19 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs RG_T2 m rom) (mkst regs' (if last then RG_X2 else RG_H2) m rom)
    /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 6 = Z_to_bv 64 (psrow + s4) /\ getr regs' 27 = Z_to_bv 64 (psrow + s4)
    /\ getr regs' 18 = Z_to_bv 64 (pdrow + d4) /\ getr regs' 1 = Z_to_bv 64 (pdrow + d4)
    /\ regs_agree (fun r => In r [1; 6; 11; 12; 15; 16; 18; 27]%list) regs regs'.
Proof.
  intros last regs m s i dh d4 s4 psrow pdrow Hs Hs64 Hi Hidh Hdh Hlast Hd4 Hs4 Hps1 Hps2 Hpd1 Hpd2 Cz Cdh
    H2 H11 H5 H7 H6 H27 H18 H1 H19.
  unfold RG_T2, RG_X2, RG_H2.
  destruct last; eexists; (split; [
    zv F_2f22c D_2f22c (Z_to_bv 64 (pdrow + d4));
    snez1 F_2f230 D_2f230;
    seqz0 F_2f234 D_2f234;
    stepb_tk F_2f238 D_2f238 ltac:(condR);
    sltu0 F_2f240 D_2f240;
    sn F_2f244 D_2f244; sn F_2f248 D_2f248;
    stepb_tk F_2f24c D_2f24c ltac:(condR);
    zv F_2f254 D_2f254 (Z_to_bv 64 (psrow + s4));
    snez1 F_2f258 D_2f258;
    seqz0 F_2f25c D_2f25c;
    stepb_tk F_2f260 D_2f260 ltac:(condR);
    sltu0 F_2f268 D_2f268;
    ld8 F_2f26c D_2f26c (s - 120)%Z (Z_to_bv 64 0) Cz;
    sn F_2f270 D_2f270; sn F_2f274 D_2f274;
    stepb_tk F_2f278 D_2f278 ltac:(condR);
    zv F_2f280 D_2f280 (Z_to_bv 64 (pdrow + d4));
    sn F_2f284 D_2f284; fixv' (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
    zv F_2f288 D_2f288 (Z_to_bv 64 (pdrow + d4));
    zv F_2f28c D_2f28c (Z_to_bv 64 (psrow + s4));
    sn F_2f290 D_2f290;
    ld8 F_2f294 D_2f294 (s - 112)%Z (Z_to_bv 64 dh) Cdh;
    first [ stepb_ft F_2f298 D_2f298 ltac:(condZ) | stepb_tk F_2f298 D_2f298 ltac:(condZ) ]; apply mst_refl
  | rg_post ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rg_S1 : forall (fw f6 f7 : bool) regs m (s dxb psf pdf swpl dwpl dh : Z),
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
    msteps SEGS (mkst regs RG_S1 m rom) (mkst regs' (if fw then RG_F else RG_X1) m rom)
    /\ (fw = true -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 (psf + 4 * swpl) /\ getr regs' 13 = Z_to_bv 64 (4 * swpl)
                     /\ getr regs' 7 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 16 = Z_to_bv 64 pdf /\ getr regs' 28 = Z_to_bv 64 (- dh)
                     /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 (if f6 then 1 else 0) /\ getr regs' 24 = Z_to_bv 64 (if f7 then 1 else 0)
                     /\ getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 31)
    /\ regs_agree (fun r => In r [1; 5; 7; 9; 11; 12; 13; 16; 17; 19; 20; 21; 22; 23; 24; 28]%list) regs regs'.
Proof.
  intros fw f6 f7 regs m s dxb psf pdf swpl dwpl dh Hs Hs64 Hdxb Hfw Hswpl Hdwpl H1 H2 H14 HF.
  unfold RG_S1, RG_F, RG_X1.
  destruct fw.
  2:{ exists regs. split; [| split; [intros; discriminate | apply regs_agree_refl]].
      stepb_tk F_2efc0 D_2efc0 ltac:(condZ). apply mst_refl. }
  destruct (HF eq_refl) as (Hpsf & Hpdf & ALs & ALd & Hdh & H15 & H25 & H26 & Cf6 & Cswpl & ROWS).
  destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
  eexists. split.
  - stepb_ft F_2efc0 D_2efc0 ltac:(condZ).
    sn F_2efc4 D_2efc4.
    sn F_2efc8 D_2efc8.
    sn F_2efcc D_2efcc.
    slli2 F_2efd0 D_2efd0 (4 * dwpl)%Z.
    ld8 F_2efd4 D_2efd4 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
    slli2 F_2efd8 D_2efd8 (4 * swpl)%Z.
    zand0 F_2efdc D_2efdc andi_3 ALd.
    zand0 F_2efe0 D_2efe0 andi_3 ALs.
    ld8 F_2efe4 D_2efe4 (s - 160)%Z (Z_to_bv 64 c50) R50.
    ld8 F_2efe8 D_2efe8 (s - 200)%Z (Z_to_bv 64 c28) R28.
    subw_v F_2efec D_2efec (c28 - c50)%Z.
    ld8 F_2eff0 D_2eff0 (s - 184)%Z (Z_to_bv 64 c38) R38.
    ld8 F_2eff4 D_2eff4 (s - 192)%Z (Z_to_bv 64 c30) R30.
    zv F_2eff8 D_2eff8 (Z_to_bv 64 (c30 + c38)).
    ld8 F_2effc D_2effc (s - 168)%Z (Z_to_bv 64 c48) R48.
    sn F_2f000 D_2f000.
    ld8 F_2f004 D_2f004 (s - 224)%Z (Z_to_bv 64 (if f6 then 1 else 0)) Cf6.
    sn F_2f008 D_2f008. fixv' (Z_to_bv 64 (if f6 then 1 else 0)) ltac:(apply andi1_if).
    sn F_2f00c D_2f00c. fixv' (Z_to_bv 64 (if f7 then 1 else 0)) ltac:(apply andi1_if).
    sn F_2f010 D_2f010.
    sn F_2f014 D_2f014. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
    subw_v F_2f018 D_2f018 (c30 + c38 - c50)%Z.
    sn F_2f01c D_2f01c.
    zv F_2f020 D_2f020 (Z_to_bv 64 (psf + 4 * swpl)).
    sn F_2f024 D_2f024.
    ld8 F_2f028 D_2f028 (s - 176)%Z (Z_to_bv 64 c40) R40.
    subw_v F_2f02c D_2f02c (c30 + c38 - c50 - c40)%Z.
    addw_v F_2f030 D_2f030 (c30 + c38 - c50 - c40 + Z.min 0 c48)%Z.
    sn F_2f034 D_2f034.
    sn F_2f038 D_2f038. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 - c50 - c40 + Z.min 0 c48))) ltac:(apply and_srai63_min; lia).
    subw_v F_2f03c D_2f03c (- dh)%Z.
    slti0 F_2f040 D_2f040.
    sn F_2f044 D_2f044.
    apply mst_refl.
  - split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rg_X1 : forall (nofull : bool) regs m (s psF pdF nfw swpl dwpl : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z -> (0 <= nfw < 2 ^ 26)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0))) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  (nofull = false ->
     (0 <= psF < 2 ^ 64)%Z /\ (0 <= pdF < 2 ^ 64)%Z /\ (psF mod 4 = 0)%Z /\ (pdF mod 4 = 0)%Z /\
     getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF /\
     rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
     rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw))) ->
  exists regs',
    msteps SEGS (mkst regs RG_X1 m rom) (mkst regs' (if nofull then RG_X2 else RG_H2) m rom)
    /\ (nofull = false -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 5 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 7 = Z_to_bv 64 (4 * swpl)
                          /\ getr regs' 20 = Z_to_bv 64 (4 * nfw) /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 23 = Z_to_bv 64 32
                          /\ getr regs' 22 = Z_to_bv 64 18446744073709551611 /\ getr regs' 17 = Z_to_bv 64 1 /\ getr regs' 25 = Z_to_bv 64 1
                          /\ getr regs' 26 = Z_to_bv 64 31 /\ getr regs' 27 = Z_to_bv 64 psF /\ getr regs' 1 = Z_to_bv 64 pdF)
    /\ regs_agree (fun r => In r [1; 5; 7; 11; 12; 13; 15; 17; 19; 20; 22; 23; 25; 26; 27]%list) regs regs'.
Proof.
  intros nofull regs m s psF pdF nfw swpl dwpl Hs Hs64 Hswpl Hdwpl Hnfw Cnf H2 H14 HF.
  unfold RG_X1, RG_X2, RG_H2.
  destruct nofull.
  - eexists. split.
    { ld8 F_2f138 D_2f138 (s - 208)%Z (Z_to_bv 64 1) Cnf.
      stepb_tk F_2f13c D_2f13c ltac:(condR).
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (HpsF & HpdF & ALs & ALd & H6 & H18 & Cswpl & Cnfw).
    eexists. split.
    + ld8 F_2f138 D_2f138 (s - 208)%Z (Z_to_bv 64 0) Cnf.
      stepb_ft F_2f13c D_2f13c ltac:(condR).
      sn F_2f140 D_2f140.
      slli2 F_2f144 D_2f144 (4 * dwpl)%Z.
      ld8 F_2f148 D_2f148 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_2f14c D_2f14c (4 * swpl)%Z.
      zand0 F_2f150 D_2f150 andi_3 ALs.
      zand0 F_2f154 D_2f154 andi_3 ALd.
      ld8 F_2f158 D_2f158 (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
      slli2 F_2f15c D_2f15c (4 * nfw)%Z.
      slti0 F_2f160 D_2f160.
      sn F_2f164 D_2f164. sn F_2f168 D_2f168. sn F_2f16c D_2f16c. sn F_2f170 D_2f170. sn F_2f174 D_2f174.
      sn F_2f178 D_2f178. sn F_2f17c D_2f17c.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rg_X2 : forall (nolast f3 : bool) regs m (s psl pdl swpl dwpl dh : Z),
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
    msteps SEGS (mkst regs RG_X2 m rom) (mkst regs' (if nolast then RG_E else RG_L) m rom)
    /\ (nolast = false -> getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 6 = Z_to_bv 64 (4 * swpl)
                          /\ getr regs' 17 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 (- dh) /\ getr regs' 16 = Z_to_bv 64 32
                          /\ getr regs' 5 = Z_to_bv 64 (if f3 then 1 else 0) /\ getr regs' 14 = Z_to_bv 64 0
                          /\ getr regs' 7 = Z_to_bv 64 18446744073709551611 /\ getr regs' 28 = Z_to_bv 64 (psl + 4 * swpl)
                          /\ getr regs' 19 = Z_to_bv 64 31 /\ getr regs' 20 = Z_to_bv 64 pdl)
    /\ regs_agree (fun r => In r [5; 6; 7; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 28]%list) regs regs'.
Proof.
  intros nolast f3 regs m s psl pdl swpl dwpl dh Hs Hs64 Hswpl Hdwpl Cnl H2 H14 HF.
  unfold RG_X2, RG_E, RG_L.
  destruct nolast.
  - eexists. split.
    { ld8 F_2f29c D_2f29c (s - 216)%Z (Z_to_bv 64 1) Cnl.
      stepb_tk F_2f2a0 D_2f2a0 ltac:(condR).
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (Hpsl & Hpdl & ALs & ALd & Hdh & H10 & Cpsl & Cf3 & Cswpl & (mk & Cmk) & ROWS).
    destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
    eexists. split.
    + ld8 F_2f29c D_2f29c (s - 216)%Z (Z_to_bv 64 0) Cnl.
      stepb_ft F_2f2a0 D_2f2a0 ltac:(condR).
      ld8 F_2f2a4 D_2f2a4 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zand0 F_2f2a8 D_2f2a8 andi_3 ALs.
      stepb_tk F_2f2ac D_2f2ac ltac:(condR).
      sn F_2f2b4 D_2f2b4.
      ld8 F_2f2b8 D_2f2b8 (s - 144)%Z mk Cmk.
      sn F_2f2bc D_2f2bc.
      slli2 F_2f2c0 D_2f2c0 (4 * dwpl)%Z.
      ld8 F_2f2c4 D_2f2c4 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_2f2c8 D_2f2c8 (4 * swpl)%Z.
      zand0 F_2f2cc D_2f2cc andi_3 ALd.
      ld8 F_2f2d0 D_2f2d0 (s - 160)%Z (Z_to_bv 64 c50) R50.
      ld8 F_2f2d4 D_2f2d4 (s - 200)%Z (Z_to_bv 64 c28) R28.
      subw_v F_2f2d8 D_2f2d8 (c28 - c50)%Z.
      ld8 F_2f2dc D_2f2dc (s - 184)%Z (Z_to_bv 64 c38) R38.
      ld8 F_2f2e0 D_2f2e0 (s - 192)%Z (Z_to_bv 64 c30) R30.
      zv F_2f2e4 D_2f2e4 (Z_to_bv 64 (c30 + c38)).
      ld8 F_2f2e8 D_2f2e8 (s - 168)%Z (Z_to_bv 64 c48) R48.
      sn F_2f2ec D_2f2ec.
      sn F_2f2f0 D_2f2f0. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
      sn F_2f2f4 D_2f2f4.
      ld8 F_2f2f8 D_2f2f8 (s - 232)%Z (Z_to_bv 64 (if f3 then 1 else 0)) Cf3.
      sn F_2f2fc D_2f2fc. fixv' (Z_to_bv 64 (if f3 then 1 else 0)) ltac:(apply andi1_if).
      slti0 F_2f300 D_2f300.
      zv F_2f304 D_2f304 (Z_to_bv 64 (c30 + c38 + Z.min 0 c48)).
      sn F_2f308 D_2f308.
      subw_v F_2f30c D_2f30c (c30 + c38 + Z.min 0 c48 - c50)%Z.
      ld8 F_2f310 D_2f310 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zv F_2f314 D_2f314 (Z_to_bv 64 (psl + 4 * swpl)).
      ld8 F_2f318 D_2f318 (s - 176)%Z (Z_to_bv 64 c40) R40.
      subw_v F_2f31c D_2f31c (c30 + c38 + Z.min 0 c48 - c50 - c40)%Z.
      sn F_2f320 D_2f320.
      sn F_2f324 D_2f324. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 + Z.min 0 c48 - c50 - c40))) ltac:(apply and_srai63_min; lia).
      subw_v F_2f328 D_2f328 (- dh)%Z.
      sn F_2f32c D_2f32c.
      sn F_2f330 D_2f330.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma masks_any : forall (m : word -> option byte) j, (0 <= j <= 65)%Z ->
  exists (bs : list byte) (v : word), rdn SEGS m (Z_to_bv 64 (RG_MASKS + 4 * j)) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned v.
Proof.
  intros m j Hj.
  assert (T : exists T, rdn SEGS (fun _ => None) (Z_to_bv 64 RG_MASKS) 264 = Some T) by (unfold RG_MASKS; img_exists).
  destruct T as [T HT].
  pose proof (rdn_sub SEGS (fun _ => None) 264 (Z_to_bv 64 RG_MASKS) T (Z.to_nat (4 * j)) 4 HT ltac:(lia)) as HS.
  unfold at_ in HS. rewrite u_Z2bv in HS by (unfold RG_MASKS; lia). rewrite Z2Nat.id in HS by lia.
  destruct (rdn_rom_any SEGS m 4 _ _ HS) as (bs & Hbs & Lbs).
  exists bs, (Z_to_bv 64 (bytes_le_to_Z bs)). split; [exact Hbs | symmetry; apply u_lez4; exact Lbs].
Qed.

Lemma jt_gen_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 RG_JT12) 4 = Some (Z_to_le_bytes 4 RG_JT12V).
Proof. unfold RG_JT12, RG_JT12V. vm_refl_bv. Qed.

End Segs2.
