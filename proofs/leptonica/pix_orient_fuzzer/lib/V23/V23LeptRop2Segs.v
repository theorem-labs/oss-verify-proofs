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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_rasteropLow_7fc9c_80000 V23_code_rasteropLow_80000_81000 V23_code_rasteropLow_81000_82000 V23_code_rasteropLow_82000_83000 V23_code_rasteropLow_83000_84000 V23_code_rasteropLow_84000_85000 V23_code_rasteropLow_85000_86000 V23_code_rasteropLow_86000_87000 V23_code_rasteropLow_87000_875f4.
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

Definition RG_S1 : word := 0x86d0c.
Definition RG_F : word := 0x86d94.
Definition RG_X1 : word := 0x86e84.
Definition RG_H2 : word := 0x86ecc.
Definition RG_I : word := 0x86ee8.
Definition RG_T2 : word := 0x86f78.
Definition RG_X2 : word := 0x86fe8.
Definition RG_L : word := 0x87080.
Definition RG_E : word := 0x875b8.
Definition RG_JT : Z := 0x1f398.
Definition RG_JT12 : Z := 0x1f3c4.
Definition RG_JT12V : Z := 424308.
Definition RG_MASKS : Z := 0x1f440.

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
  stepb_tk F_86e08 D_86e08 ltac:(condR);
  stepb_tk F_86e10 D_86e10 ltac:(condZ);
  ld4 F_86e18 D_86e18 pd bd Rd Ld;
  sn F_86e1c D_86e1c; sn F_86e20 D_86e20; sn F_86e24 D_86e24;
  zv F_86e28 D_86e28 (Z_to_bv 64 (pd + d4));
  stw F_86e2c D_86e2c (Z_to_bv 64 pd) SOK;
  stepb_tk F_86e30 D_86e30 ltac:(condZ);
  sltu0 F_86e38 D_86e38; sn F_86e3c D_86e3c; sn F_86e40 D_86e40;
  stepb_tk F_86e44 D_86e44 ltac:(condR);
  zv F_86e4c D_86e4c (Z_to_bv 64 (psf + off + s4));
  stepb_tk F_86e50 D_86e50 ltac:(condZ);
  sltu0 F_86e58 D_86e58;
  ld8w F_86e5c D_86e5c (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_86e60 D_86e60; sn F_86e64 D_86e64;
  stepb_tk F_86e68 D_86e68 ltac:(condR);
  sn F_86e70 D_86e70; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_86e74 D_86e74 (Z_to_bv 64 (off + s4));
  zv F_86e78 D_86e78 (Z_to_bv 64 (pd + d4));
  sn F_86e7c D_86e7c;
  first [ stepb_ft F_86e80 D_86e80 ltac:(condSe) | stepb_tk F_86e80 D_86e80 ltac:(condSe) ]; apply mst_refl.
Ltac rgL_tail n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz :=
  stepb_tk F_870c8 D_870c8 ltac:(condR);
  stepb_tk F_870d0 D_870d0 ltac:(condZ);
  ld4 F_870d8 D_870d8 pd bd Rd Ld;
  ld8 F_870dc D_870dc (s - 144)%Z mk Cmk;
  sn F_870e0 D_870e0; sn F_870e4 D_870e4; sn F_870e8 D_870e8;
  zv F_870ec D_870ec (Z_to_bv 64 (pd + d4));
  stw F_870f0 D_870f0 (Z_to_bv 64 pd) SOK;
  stepb_tk F_870f4 D_870f4 ltac:(condZ);
  sltu0 F_870fc D_870fc; sn F_87100 D_87100; sn F_87104 D_87104;
  stepb_tk F_87108 D_87108 ltac:(condR);
  zv F_87110 D_87110 (Z_to_bv 64 (psl + off + s4));
  stepb_tk F_87114 D_87114 ltac:(condZ);
  sltu0 F_8711c D_8711c;
  ld8w F_87120 D_87120 (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_87124 D_87124; sn F_87128 D_87128;
  stepb_tk F_8712c D_8712c ltac:(condR);
  sn F_87134 D_87134; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_87138 D_87138 (Z_to_bv 64 (off + s4));
  zv F_8713c D_8713c (Z_to_bv 64 (pd + d4));
  sn F_87140 D_87140;
  first [ stepb_ft F_87144 D_87144 ltac:(condSe); stepj F_87148 D_87148 | stepb_tk F_87144 D_87144 ltac:(condSe) ]; apply mst_refl.
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
      zv F_86d94 D_86d94 (Z_to_bv 64 (psf + off));
      snez1 F_86d98 D_86d98;
      sn F_86d9c D_86d9c;
      stepb_ft F_86da0 D_86da0 ltac:(condR);
      stepb_tk F_86da4 D_86da4 ltac:(condR);
      sn F_86dac D_86dac;
      stepb_tk F_86db0 D_86db0 ltac:(condZ);
      ld4 F_86db8 D_86db8 (psf + off)%Z bs0 R0 L0;
      sn F_86dbc D_86dbc;
      stepb_tk F_86dc0 D_86dc0 ltac:(condR);
      rgF_tail n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg_post ]).
  - destruct (R1 eq_refl eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      zv F_86d94 D_86d94 (Z_to_bv 64 (psf + off));
      snez1 F_86d98 D_86d98;
      sn F_86d9c D_86d9c;
      stepb_ft F_86da0 D_86da0 ltac:(condR);
      stepb_tk F_86da4 D_86da4 ltac:(condR);
      sn F_86dac D_86dac;
      stepb_tk F_86db0 D_86db0 ltac:(condZ);
      ld4 F_86db8 D_86db8 (psf + off)%Z bs0 R0 L0;
      sn F_86dbc D_86dbc;
      stepb_ft F_86dc0 D_86dc0 ltac:(condR);
      sn F_86dc4 D_86dc4;
      stepb_tk F_86dc8 D_86dc8 ltac:(condZ);
      stepb_tk F_86dd0 D_86dd0 ltac:(condZ);
      ld4 F_86dd8 D_86dd8 (psf + off + 4)%Z bs1 R1' L1;
      sn F_86ddc D_86ddc; sn F_86de0 D_86de0; sn F_86de4 D_86de4; sn F_86de8 D_86de8;
      stepj F_86dec D_86dec;
      rgF_tail n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg_post ]).
  - destruct last; eexists; eexists; (split; [
      zv F_86d94 D_86d94 (Z_to_bv 64 (psf + off));
      snez1 F_86d98 D_86d98;
      sn F_86d9c D_86d9c;
      stepb_tk F_86da0 D_86da0 ltac:(condR);
      stepb_tk F_86df0 D_86df0 ltac:(condR);
      stepb_tk F_86df8 D_86df8 ltac:(condZ);
      ld4 F_86e00 D_86e00 (psf + off)%Z bs0 R0 L0;
      sn F_86e04 D_86e04;
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
      ld8 F_87080 D_87080 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_87084 D_87084 (Z_to_bv 64 (psl + off));
      stepb_tk F_87088 D_87088 ltac:(condZ);
      stepb_tk F_87090 D_87090 ltac:(condZ);
      ld4 F_87098 D_87098 (psl + off)%Z bs0 R0 L0;
      sn F_8709c D_8709c;
      stepb_tk F_870a0 D_870a0 ltac:(condR);
      rgL_tail n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | rg_post ]).
  - destruct (R1 eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      ld8 F_87080 D_87080 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_87084 D_87084 (Z_to_bv 64 (psl + off));
      stepb_tk F_87088 D_87088 ltac:(condZ);
      stepb_tk F_87090 D_87090 ltac:(condZ);
      ld4 F_87098 D_87098 (psl + off)%Z bs0 R0 L0;
      sn F_8709c D_8709c;
      stepb_ft F_870a0 D_870a0 ltac:(condR);
      stepb_tk F_870a4 D_870a4 ltac:(condZ);
      stepb_tk F_870ac D_870ac ltac:(condZ);
      ld4 F_870b4 D_870b4 (psl + off + 4)%Z bs1 R1' L1;
      sn F_870b8 D_870b8; sn F_870bc D_870bc; sn F_870c0 D_870c0; sn F_870c4 D_870c4;
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
  - ld8 F_86ecc D_86ecc (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
    stepb_ft F_86ed0 D_86ed0 ltac:(condZ).
    sn F_86ed4 D_86ed4.
    snez1 F_86ed8 D_86ed8.
    snez1 F_86edc D_86edc.
    sn F_86ee0 D_86ee0.
    sn F_86ee4 D_86ee4.
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
    zv F_86ee8 D_86ee8 (Z_to_bv 64 (psrow + off));
    stepb_tk F_86eec D_86eec ltac:(condZ);
    seqz0 F_86ef4 D_86ef4;
    sn F_86ef8 D_86ef8;
    stepb_tk F_86efc D_86efc ltac:(condR);
    stepb_tk F_86f04 D_86f04 ltac:(condR);
    stepb_tk F_86f0c D_86f0c ltac:(condZ);
    zv F_86f14 D_86f14 (Z_to_bv 64 (psrow + off));
    stepb_tk F_86f18 D_86f18 ltac:(condZ);
    stepb_tk F_86f20 D_86f20 ltac:(condZ);
    zv F_86f28 D_86f28 (Z_to_bv 64 (pdrow + off));
    stepb_tk F_86f2c D_86f2c ltac:(condZ);
    seqz0 F_86f34 D_86f34;
    sn F_86f38 D_86f38;
    stepb_tk F_86f3c D_86f3c ltac:(condR);
    stepb_tk F_86f44 D_86f44 ltac:(condR);
    ld4 F_86f4c D_86f4c (psrow + off)%Z bs0 R0 L0;
    ld4 F_86f50 D_86f50 (psrow + off + 4)%Z bs1 R1 L1;
    sn F_86f54 D_86f54; sn F_86f58 D_86f58; sn F_86f5c D_86f5c; sn F_86f60 D_86f60; sn F_86f64 D_86f64;
    zv F_86f68 D_86f68 (Z_to_bv 64 (pdrow + off));
    zv F_86f6c D_86f6c (Z_to_bv 64 (off + 4));
    stw F_86f70 D_86f70 (Z_to_bv 64 (pdrow + off)) SOK;
    first [ stepb_ft F_86f74 D_86f74 ltac:(condZ) | stepb_tk F_86f74 D_86f74 ltac:(condZ) ]; apply mst_refl
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
    zv F_86f78 D_86f78 (Z_to_bv 64 (pdrow + d4));
    snez1 F_86f7c D_86f7c;
    seqz0 F_86f80 D_86f80;
    stepb_tk F_86f84 D_86f84 ltac:(condR);
    sltu0 F_86f8c D_86f8c;
    sn F_86f90 D_86f90; sn F_86f94 D_86f94;
    stepb_tk F_86f98 D_86f98 ltac:(condR);
    zv F_86fa0 D_86fa0 (Z_to_bv 64 (psrow + s4));
    snez1 F_86fa4 D_86fa4;
    seqz0 F_86fa8 D_86fa8;
    stepb_tk F_86fac D_86fac ltac:(condR);
    sltu0 F_86fb4 D_86fb4;
    ld8 F_86fb8 D_86fb8 (s - 120)%Z (Z_to_bv 64 0) Cz;
    sn F_86fbc D_86fbc; sn F_86fc0 D_86fc0;
    stepb_tk F_86fc4 D_86fc4 ltac:(condR);
    zv F_86fcc D_86fcc (Z_to_bv 64 (pdrow + d4));
    sn F_86fd0 D_86fd0; fixv' (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
    zv F_86fd4 D_86fd4 (Z_to_bv 64 (pdrow + d4));
    zv F_86fd8 D_86fd8 (Z_to_bv 64 (psrow + s4));
    sn F_86fdc D_86fdc;
    ld8 F_86fe0 D_86fe0 (s - 112)%Z (Z_to_bv 64 dh) Cdh;
    first [ stepb_ft F_86fe4 D_86fe4 ltac:(condZ) | stepb_tk F_86fe4 D_86fe4 ltac:(condZ) ]; apply mst_refl
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
      stepb_tk F_86d0c D_86d0c ltac:(condZ). apply mst_refl. }
  destruct (HF eq_refl) as (Hpsf & Hpdf & ALs & ALd & Hdh & H15 & H25 & H26 & Cf6 & Cswpl & ROWS).
  destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
  eexists. split.
  - stepb_ft F_86d0c D_86d0c ltac:(condZ).
    sn F_86d10 D_86d10.
    sn F_86d14 D_86d14.
    sn F_86d18 D_86d18.
    slli2 F_86d1c D_86d1c (4 * dwpl)%Z.
    ld8 F_86d20 D_86d20 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
    slli2 F_86d24 D_86d24 (4 * swpl)%Z.
    zand0 F_86d28 D_86d28 andi_3 ALd.
    zand0 F_86d2c D_86d2c andi_3 ALs.
    ld8 F_86d30 D_86d30 (s - 160)%Z (Z_to_bv 64 c50) R50.
    ld8 F_86d34 D_86d34 (s - 200)%Z (Z_to_bv 64 c28) R28.
    subw_v F_86d38 D_86d38 (c28 - c50)%Z.
    ld8 F_86d3c D_86d3c (s - 184)%Z (Z_to_bv 64 c38) R38.
    ld8 F_86d40 D_86d40 (s - 192)%Z (Z_to_bv 64 c30) R30.
    zv F_86d44 D_86d44 (Z_to_bv 64 (c30 + c38)).
    ld8 F_86d48 D_86d48 (s - 168)%Z (Z_to_bv 64 c48) R48.
    sn F_86d4c D_86d4c.
    ld8 F_86d50 D_86d50 (s - 224)%Z (Z_to_bv 64 (if f6 then 1 else 0)) Cf6.
    sn F_86d54 D_86d54. fixv' (Z_to_bv 64 (if f6 then 1 else 0)) ltac:(apply andi1_if).
    sn F_86d58 D_86d58. fixv' (Z_to_bv 64 (if f7 then 1 else 0)) ltac:(apply andi1_if).
    sn F_86d5c D_86d5c.
    sn F_86d60 D_86d60. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
    subw_v F_86d64 D_86d64 (c30 + c38 - c50)%Z.
    sn F_86d68 D_86d68.
    zv F_86d6c D_86d6c (Z_to_bv 64 (psf + 4 * swpl)).
    sn F_86d70 D_86d70.
    ld8 F_86d74 D_86d74 (s - 176)%Z (Z_to_bv 64 c40) R40.
    subw_v F_86d78 D_86d78 (c30 + c38 - c50 - c40)%Z.
    addw_v F_86d7c D_86d7c (c30 + c38 - c50 - c40 + Z.min 0 c48)%Z.
    sn F_86d80 D_86d80.
    sn F_86d84 D_86d84. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 - c50 - c40 + Z.min 0 c48))) ltac:(apply and_srai63_min; lia).
    subw_v F_86d88 D_86d88 (- dh)%Z.
    slti0 F_86d8c D_86d8c.
    sn F_86d90 D_86d90.
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
    { ld8 F_86e84 D_86e84 (s - 208)%Z (Z_to_bv 64 1) Cnf.
      stepb_tk F_86e88 D_86e88 ltac:(condR).
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (HpsF & HpdF & ALs & ALd & H6 & H18 & Cswpl & Cnfw).
    eexists. split.
    + ld8 F_86e84 D_86e84 (s - 208)%Z (Z_to_bv 64 0) Cnf.
      stepb_ft F_86e88 D_86e88 ltac:(condR).
      sn F_86e8c D_86e8c.
      slli2 F_86e90 D_86e90 (4 * dwpl)%Z.
      ld8 F_86e94 D_86e94 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_86e98 D_86e98 (4 * swpl)%Z.
      zand0 F_86e9c D_86e9c andi_3 ALs.
      zand0 F_86ea0 D_86ea0 andi_3 ALd.
      ld8 F_86ea4 D_86ea4 (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
      slli2 F_86ea8 D_86ea8 (4 * nfw)%Z.
      slti0 F_86eac D_86eac.
      sn F_86eb0 D_86eb0. sn F_86eb4 D_86eb4. sn F_86eb8 D_86eb8. sn F_86ebc D_86ebc. sn F_86ec0 D_86ec0.
      sn F_86ec4 D_86ec4. sn F_86ec8 D_86ec8.
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
    { ld8 F_86fe8 D_86fe8 (s - 216)%Z (Z_to_bv 64 1) Cnl.
      stepb_tk F_86fec D_86fec ltac:(condR).
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (Hpsl & Hpdl & ALs & ALd & Hdh & H10 & Cpsl & Cf3 & Cswpl & (mk & Cmk) & ROWS).
    destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B28 & B30 & B38 & B40 & B48 & B50 & EQ).
    eexists. split.
    + ld8 F_86fe8 D_86fe8 (s - 216)%Z (Z_to_bv 64 0) Cnl.
      stepb_ft F_86fec D_86fec ltac:(condR).
      ld8 F_86ff0 D_86ff0 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zand0 F_86ff4 D_86ff4 andi_3 ALs.
      stepb_tk F_86ff8 D_86ff8 ltac:(condR).
      sn F_87000 D_87000.
      ld8 F_87004 D_87004 (s - 144)%Z mk Cmk.
      sn F_87008 D_87008.
      slli2 F_8700c D_8700c (4 * dwpl)%Z.
      ld8 F_87010 D_87010 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
      slli2 F_87014 D_87014 (4 * swpl)%Z.
      zand0 F_87018 D_87018 andi_3 ALd.
      ld8 F_8701c D_8701c (s - 160)%Z (Z_to_bv 64 c50) R50.
      ld8 F_87020 D_87020 (s - 200)%Z (Z_to_bv 64 c28) R28.
      subw_v F_87024 D_87024 (c28 - c50)%Z.
      ld8 F_87028 D_87028 (s - 184)%Z (Z_to_bv 64 c38) R38.
      ld8 F_8702c D_8702c (s - 192)%Z (Z_to_bv 64 c30) R30.
      zv F_87030 D_87030 (Z_to_bv 64 (c30 + c38)).
      ld8 F_87034 D_87034 (s - 168)%Z (Z_to_bv 64 c48) R48.
      sn F_87038 D_87038.
      sn F_8703c D_8703c. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(apply and_srai63_min; lia).
      sn F_87040 D_87040.
      ld8 F_87044 D_87044 (s - 232)%Z (Z_to_bv 64 (if f3 then 1 else 0)) Cf3.
      sn F_87048 D_87048. fixv' (Z_to_bv 64 (if f3 then 1 else 0)) ltac:(apply andi1_if).
      slti0 F_8704c D_8704c.
      zv F_87050 D_87050 (Z_to_bv 64 (c30 + c38 + Z.min 0 c48)).
      sn F_87054 D_87054.
      subw_v F_87058 D_87058 (c30 + c38 + Z.min 0 c48 - c50)%Z.
      ld8 F_8705c D_8705c (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zv F_87060 D_87060 (Z_to_bv 64 (psl + 4 * swpl)).
      ld8 F_87064 D_87064 (s - 176)%Z (Z_to_bv 64 c40) R40.
      subw_v F_87068 D_87068 (c30 + c38 + Z.min 0 c48 - c50 - c40)%Z.
      sn F_8706c D_8706c.
      sn F_87070 D_87070. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 + Z.min 0 c48 - c50 - c40))) ltac:(apply and_srai63_min; lia).
      subw_v F_87074 D_87074 (- dh)%Z.
      sn F_87078 D_87078.
      sn F_8707c D_8707c.
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
