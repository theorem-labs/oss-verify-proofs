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

Definition RG14_S1 : word := 0x852cc.
Definition RG14_F : word := 0x85370.
Definition RG14_X1 : word := 0x85468.
Definition RG14_H2 : word := 0x854a4.
Definition RG14_I : word := 0x854c4.
Definition RG14_T2 : word := 0x8555c.
Definition RG14_X2 : word := 0x855cc.
Definition RG14_L : word := 0x85648.
Definition RG14_JT : Z := 0x1f3cc.
Definition RG14_JTV : Z := 417588.

Definition rg14_rc (c28 c30 c38 c40 c48 c50 dh : Z) : Prop :=
  (- 2 ^ 28 <= c28 < 2 ^ 28)%Z /\ (- 2 ^ 28 <= c30 < 2 ^ 28)%Z /\ (- 2 ^ 28 <= c38 < 2 ^ 28)%Z /\
  (- 2 ^ 28 <= c40 < 2 ^ 28)%Z /\ (- 2 ^ 28 <= c48 < 2 ^ 28)%Z /\ (- 2 ^ 28 <= c50 < 2 ^ 28)%Z /\
  (c28 - c50 - Z.min 0 (c30 + c38 - c50 - c40 + Z.min 0 c48) = - dh)%Z.

Definition rg14_rows (M : word -> option byte) (s dh : Z) : Prop :=
  exists c28 c30 c38 c40 c48 c50 : Z,
    rdn SEGS M (Z_to_bv 64 (s - 200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (c28 - c50))) /\
    rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if (c48 <? 0)%Z then -1 else 0))) /\
    rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (c30 + c38))) /\
    rdn SEGS M (Z_to_bv 64 (s - 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c40)) /\
    rdn SEGS M (Z_to_bv 64 (s - 168)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c48)) /\
    rdn SEGS M (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c50)) /\
    rg14_rc c28 c30 c38 c40 c48 c50 dh.

Section Segs14G.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac rg14_post := repeat split; gres; pin; try reflexivity; solve_regs_agree.

Ltac cR := first [ condR | condZ | condSe ].
Ltac cZ := first [ condZ | condR | condSe ].

Ltac rgF_tail14 n pd d4 psf off s4 s bd Rd Ld SOK Cz :=
  stepb_tk F_853e8 D_853e8 ltac:(cR);
  stepb_tk F_853f0 D_853f0 ltac:(cZ);
  ld4 F_853f8 D_853f8 pd bd Rd Ld;
  sn F_853fc D_853fc; sn F_85400 D_85400;
  sn F_85404 D_85404; sn F_85408 D_85408;
  zv F_8540c D_8540c (Z_to_bv 64 (pd + d4));
  stw F_85410 D_85410 (Z_to_bv 64 pd) SOK;
  stepb_tk F_85414 D_85414 ltac:(cZ);
  sltu0 F_8541c D_8541c; sn F_85420 D_85420; sn F_85424 D_85424;
  stepb_tk F_85428 D_85428 ltac:(cR);
  zv F_85430 D_85430 (Z_to_bv 64 (psf + off + s4));
  stepb_tk F_85434 D_85434 ltac:(cZ);
  sltu0 F_8543c D_8543c;
  ld8w F_85440 D_85440 (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_85444 D_85444; sn F_85448 D_85448;
  stepb_tk F_8544c D_8544c ltac:(cR);
  sn F_85454 D_85454; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_85458 D_85458 (Z_to_bv 64 (off + s4));
  zv F_8545c D_8545c (Z_to_bv 64 (pd + d4));
  sn F_85460 D_85460;
  first [ stepb_ft F_85464 D_85464 ltac:(condSe) | stepb_tk F_85464 D_85464 ltac:(condSe) ]; apply mst_refl.
(* [comment removed for export] *)
Lemma rg14_F : forall (f6 f7 last : bool) regs m (s psf off pd s4 d4 n sls : Z) (bs0 bs1 bd : list byte),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= psf)%Z -> (0 <= off)%Z -> (0 <= s4)%Z -> (0 <= d4)%Z ->
  (1 <= psf + off)%Z -> (psf + off + s4 < 2 ^ 64)%Z -> (1 <= pd)%Z -> (pd + d4 < 2 ^ 64)%Z ->
  (pd + 4 < 2 ^ 64)%Z -> (pd + 4 <= s - 240 \/ s <= pd)%Z ->
  (1 <= n < 2 ^ 31)%Z -> (if last then n = 1 else 1 < n)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psf + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  (f6 = true -> f7 = false -> psf + off + 8 < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 (psf + off + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> length bd = 4%nat -> store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 15 = Z_to_bv 64 psf -> getr regs 28 = Z_to_bv 64 off ->
  getr regs 25 = Z_to_bv 64 pd -> getr regs 16 = Z_to_bv 64 pd -> getr regs 9 = Z_to_bv 64 (- n) ->
  getr regs 19 = Z_to_bv 64 s4 -> getr regs 13 = Z_to_bv 64 d4 -> getr regs 23 = Z_to_bv 64 (psf + s4) ->
  getr regs 24 = Z_to_bv 64 (if f6 then 1 else 0) -> getr regs 5 = Z_to_bv 64 (if f7 then 1 else 0) ->
  getr regs 7 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 -> getr regs 17 = Z_to_bv 64 32 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG14_F m rom) (mkst regs' (if last then RG14_X1 else RG14_F) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 28 = Z_to_bv 64 (off + s4) /\ getr regs' 25 = Z_to_bv 64 (pd + d4) /\ getr regs' 16 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 9 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [1; 9; 12; 16; 21; 25; 26; 28]%list) regs regs'.
Proof.
  intros f6 f7 last regs m s psf off pd s4 d4 n sls bs0 bs1 bd Hs Hs64 Hpsf Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cz H2 H15 H28 H25 H16 H9 H19 H13 H23 H24 H5 H7 H22 H14 H17 H30 H8.
  unfold RG14_F, RG14_X1.
  destruct f6; [destruct f7|]; [
    destruct last; eexists; eexists; (split; [
      zv F_85370 D_85370 (Z_to_bv 64 (psf + off));
      snez1 F_85374 D_85374;
      sn F_85378 D_85378;
      stepb_ft F_8537c D_8537c ltac:(cR);
      stepb_tk F_85380 D_85380 ltac:(cR);
      stepb_tk F_85388 D_85388 ltac:(cZ);
      ld4 F_85390 D_85390 (psf + off)%Z bs0 R0 L0;
      sn F_85394 D_85394;
      stepb_tk F_85398 D_85398 ltac:(cR);
      rgF_tail14 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg14_post ])
  | destruct (R1 eq_refl eq_refl) as (Hps8 & R1' & L1);
    destruct last; eexists; eexists; (split; [
      zv F_85370 D_85370 (Z_to_bv 64 (psf + off));
      snez1 F_85374 D_85374;
      sn F_85378 D_85378;
      stepb_ft F_8537c D_8537c ltac:(cR);
      stepb_tk F_85380 D_85380 ltac:(cR);
      stepb_tk F_85388 D_85388 ltac:(cZ);
      ld4 F_85390 D_85390 (psf + off)%Z bs0 R0 L0;
      sn F_85394 D_85394;
      stepb_ft F_85398 D_85398 ltac:(cR);
      sn F_8539c D_8539c;
      stepb_tk F_853a0 D_853a0 ltac:(cZ);
      sn F_853a8 D_853a8;
      stepb_tk F_853ac D_853ac ltac:(cZ);
      ld4 F_853b4 D_853b4 (psf + off + 4)%Z bs1 R1' L1;
      sn F_853b8 D_853b8; sn F_853bc D_853bc; sn F_853c0 D_853c0; sn F_853c4 D_853c4;
      stepj F_853c8 D_853c8;
      rgF_tail14 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg14_post ])
  | destruct last; eexists; eexists; (split; [
      zv F_85370 D_85370 (Z_to_bv 64 (psf + off));
      snez1 F_85374 D_85374;
      sn F_85378 D_85378;
      stepb_tk F_8537c D_8537c ltac:(cR);
      stepb_tk F_853cc D_853cc ltac:(cR);
      sn F_853d4 D_853d4;
      stepb_tk F_853d8 D_853d8 ltac:(cZ);
      ld4 F_853e0 D_853e0 (psf + off)%Z bs0 R0 L0;
      sn F_853e4 D_853e4;
      rgF_tail14 n pd d4 psf off s4 s bd Rd Ld SOK Cz
    | rg14_post ])
  ].
Qed.

Lemma rg14_I : forall (last : bool) regs m (psrow pdrow off n4 sls : Z) (bs0 bs1 bd : list byte),
  (0 <= off)%Z -> (off + 4 <= n4)%Z -> (if last then off + 4 = n4 else off + 4 < n4)%Z -> (n4 < 2 ^ 28)%Z ->
  (1 <= psrow)%Z -> (psrow + n4 + 4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + n4 < 2 ^ 64)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psrow + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (psrow + off + 4)) 4 = Some bs1 -> length bs1 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (pdrow + off)) 4 = Some bd -> length bd = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 (pdrow + off)) 4 = true ->
  getr regs 22 = Z_to_bv 64 psrow -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 24 = Z_to_bv 64 pdrow ->
  getr regs 18 = Z_to_bv 64 pdrow -> getr regs 15 = Z_to_bv 64 off -> getr regs 20 = Z_to_bv 64 n4 ->
  getr regs 16 = Z_to_bv 64 1 -> getr regs 5 = Z_to_bv 64 1 -> getr regs 7 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 1 ->
  getr regs 23 = Z_to_bv 64 32 -> getr regs 25 = Z_to_bv 64 18446744073709551611 -> getr regs 1 = Z_to_bv 64 31 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG14_I m rom) (mkst regs' (if last then RG14_T2 else RG14_I) (wbytes m (Z_to_bv 64 (pdrow + off)) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 15 = Z_to_bv 64 (off + 4)
    /\ regs_agree (fun r => In r [12; 15; 17; 21; 26]%list) regs regs'.
Proof.
  intros last regs m psrow pdrow off n4 sls bs0 bs1 bd Hoff Hn4 Hlast Hn4b Hps1 Hps2 Hpd1 Hpd2 Hsls R0 L0 R1 L1 Rd Ld SOK
    H22 H6 H24 H18 H15 H20 H16 H5 H7 H9 H23 H25 H1 H30 H8.
  unfold RG14_I, RG14_T2.
  destruct last; eexists; eexists; (split; [
    zv F_854c4 D_854c4 (Z_to_bv 64 (psrow + off));
    stepb_tk F_854c8 D_854c8 ltac:(cZ);
    seqz0 F_854d0 D_854d0;
    sn F_854d4 D_854d4;
    stepb_tk F_854d8 D_854d8 ltac:(cR);
    stepb_tk F_854e0 D_854e0 ltac:(cR);
    stepb_tk F_854e8 D_854e8 ltac:(cZ);
    zv F_854f0 D_854f0 (Z_to_bv 64 (psrow + off));
    stepb_tk F_854f4 D_854f4 ltac:(cZ);
    stepb_tk F_854fc D_854fc ltac:(cZ);
    zv F_85504 D_85504 (Z_to_bv 64 (pdrow + off));
    stepb_tk F_85508 D_85508 ltac:(cZ);
    seqz0 F_85510 D_85510;
    sn F_85514 D_85514;
    stepb_tk F_85518 D_85518 ltac:(cR);
    stepb_tk F_85520 D_85520 ltac:(cR);
    ld4 F_85528 D_85528 (psrow + off)%Z bs0 R0 L0;
    ld4 F_8552c D_8552c (psrow + off + 4)%Z bs1 R1 L1;
    zv F_85530 D_85530 (Z_to_bv 64 (pdrow + off));
    ld4 F_85534 D_85534 (pdrow + off)%Z bd Rd Ld;
    sn F_85538 D_85538; sn F_8553c D_8553c; sn F_85540 D_85540; sn F_85544 D_85544; sn F_85548 D_85548;
    sn F_8554c D_8554c;
    zv F_85550 D_85550 (Z_to_bv 64 (off + 4));
    stw F_85554 D_85554 (Z_to_bv 64 (pdrow + off)) SOK;
    first [ stepb_ft F_85558 D_85558 ltac:(condZ) | stepb_tk F_85558 D_85558 ltac:(condZ) ]; apply mst_refl
  | rg14_post ]).
Qed.

Lemma and_sgn_min : forall c : Z,
  v_and (Z_to_bv 64 (if (c <? 0)%Z then (-1)%Z else 0%Z)) (Z_to_bv 64 c) = Z_to_bv 64 (Z.min 0 c).
Proof.
  intros c. destruct (Z.ltb_spec c 0) as [N|P].
  - rewrite Z.min_r by lia. apply and_m1_l.
  - rewrite Z.min_l by lia. apply and_0_l.
Qed.

Lemma v_and_comm14 : forall x y : word, v_and x y = v_and y x.
Proof. intros x y. unfold v_and. rewrite Z.land_comm. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rg14_X2 : forall (nolast f3 : bool) regs m (s psl pdl swpl dh : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= swpl < 2 ^ 24)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nolast then 1 else 0))) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 19 = Z_to_bv 64 (4 * swpl) ->
  (nolast = false ->
     (0 <= psl < 2 ^ 64)%Z /\ (0 <= pdl < 2 ^ 64)%Z /\ (psl mod 4 = 0)%Z /\ (pdl mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
     getr regs 10 = Z_to_bv 64 pdl /\
     rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) /\
     rdn SEGS m (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))) /\
     (exists mk : word, rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk)) /\
     rg14_rows m s dh) ->
  exists regs',
    msteps SEGS (mkst regs RG14_X2 m rom) (mkst regs' (if nolast then RG_E else RG14_L) m rom)
    /\ (nolast = false -> getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 17 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 (- dh)
                          /\ getr regs' 5 = Z_to_bv 64 32 /\ getr regs' 7 = Z_to_bv 64 (if f3 then 1 else 0)
                          /\ getr regs' 28 = Z_to_bv 64 18446744073709551611 /\ getr regs' 16 = Z_to_bv 64 (psl + 4 * swpl)
                          /\ getr regs' 6 = Z_to_bv 64 31 /\ getr regs' 20 = Z_to_bv 64 pdl)
    /\ regs_agree (fun r => In r [5; 6; 7; 9; 12; 15; 16; 17; 20; 28]%list) regs regs'.
Proof.
  intros nolast f3 regs m s psl pdl swpl dh Hs Hs64 Hswpl Cnl H2 H19 HF.
  unfold RG14_X2, RG_E, RG14_L.
  destruct nolast.
  - eexists. split.
    { ld8 F_855cc D_855cc (s - 216)%Z (Z_to_bv 64 1) Cnl.
      stepb_ft F_855d0 D_855d0 ltac:(condR).
      stepj F_855d4 D_855d4.
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (Hpsl & Hpdl & ALs & ALd & Hdh & H10 & Cpsl & Cf3 & (mk & Cmk) & ROWS).
    destruct ROWS as (c28 & c30 & c38 & c40 & c48 & c50 & R200 & R192 & R184 & R176 & R168 & R160 & RC).
    destruct RC as (B28 & B30 & B38 & B40 & B48 & B50 & EQ).
    eexists. split.
    + ld8 F_855cc D_855cc (s - 216)%Z (Z_to_bv 64 0) Cnl.
      stepb_tk F_855d0 D_855d0 ltac:(condR).
      ld8 F_855d8 D_855d8 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zand0 F_855dc D_855dc andi_3 ALs.
      stepb_tk F_855e0 D_855e0 ltac:(condR).
      ld8 F_855e8 D_855e8 (s - 144)%Z mk Cmk.
      sn F_855ec D_855ec.
      zand0 F_855f0 D_855f0 andi_3 ALd.
      ld8 F_855f4 D_855f4 (s - 168)%Z (Z_to_bv 64 c48) R168.
      ld8 F_855f8 D_855f8 (s - 192)%Z (Z_to_bv 64 (if (c48 <? 0)%Z then (-1)%Z else 0%Z)) R192.
      sn F_855fc D_855fc.
      fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(first [apply and_sgn_min | rewrite v_and_comm14; apply and_sgn_min]).
      ld8 F_85600 D_85600 (s - 136)%Z (Z_to_bv 64 psl) Cpsl.
      zv F_85604 D_85604 (Z_to_bv 64 (psl + 4 * swpl)).
      ld8 F_85608 D_85608 (s - 184)%Z (Z_to_bv 64 (c30 + c38)) R184.
      zv F_8560c D_8560c (Z_to_bv 64 (c30 + c38 + Z.min 0 c48)).
      sn F_85610 D_85610.
      ld8 F_85614 D_85614 (s - 232)%Z (Z_to_bv 64 (if f3 then 1 else 0)) Cf3.
      sn F_85618 D_85618. fixv' (Z_to_bv 64 (if f3 then 1 else 0)) ltac:(apply andi1_if).
      ld8 F_8561c D_8561c (s - 160)%Z (Z_to_bv 64 c50) R160.
      subw_v F_85620 D_85620 (c30 + c38 + Z.min 0 c48 - c50)%Z.
      sn F_85624 D_85624.
      ld8 F_85628 D_85628 (s - 176)%Z (Z_to_bv 64 c40) R176.
      subw_v F_8562c D_8562c (c30 + c38 + Z.min 0 c48 - c50 - c40)%Z.
      sn F_85630 D_85630.
      sn F_85634 D_85634. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 + Z.min 0 c48 - c50 - c40))) ltac:(apply and_srai63_min; lia).
      ld8 F_85638 D_85638 (s - 200)%Z (Z_to_bv 64 (c28 - c50)) R200.
      subw_v F_8563c D_8563c (- dh)%Z.
      sn F_85640 D_85640.
      sn F_85644 D_85644.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac rgL_tail14 n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz :=
  stepb_tk F_85690 D_85690 ltac:(condR);
  stepb_tk F_85698 D_85698 ltac:(condZ);
  ld4 F_856a0 D_856a0 pd bd Rd Ld; sn F_856a4 D_856a4; sn F_856a8 D_856a8;
  ld8 F_856ac D_856ac (s - 144)%Z mk Cmk;
  sn F_856b0 D_856b0; sn F_856b4 D_856b4;
  zv F_856b8 D_856b8 (Z_to_bv 64 (pd + d4));
  stw F_856bc D_856bc (Z_to_bv 64 pd) SOK;
  stepb_tk F_856c0 D_856c0 ltac:(condZ);
  sltu0 F_856c8 D_856c8; sn F_856cc D_856cc; sn F_856d0 D_856d0;
  stepb_tk F_856d4 D_856d4 ltac:(condR);
  zv F_856dc D_856dc (Z_to_bv 64 (psl + off + s4));
  stepb_tk F_856e0 D_856e0 ltac:(condZ);
  sltu0 F_856e8 D_856e8;
  ld8w F_856ec D_856ec (s - 120)%Z (Z_to_bv 64 0) Cz;
  sn F_856f0 D_856f0; sn F_856f4 D_856f4;
  stepb_tk F_856f8 D_856f8 ltac:(condR);
  sn F_85700 D_85700; fixv' (Z_to_bv 64 (- (n - 1))) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
  zv F_85704 D_85704 (Z_to_bv 64 (off + s4));
  zv F_85708 D_85708 (Z_to_bv 64 (pd + d4));
  sn F_8570c D_8570c;
  first [ stepb_ft F_85710 D_85710 ltac:(condSe); stepj F_85714 D_85714 | stepb_tk F_85710 D_85710 ltac:(condSe) ]; apply mst_refl.
Lemma rg14_L : forall (f3 last : bool) regs m (s psl off pd s4 d4 n sls : Z) (mk : word) (bs0 bs1 bd : list byte),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= psl)%Z -> (0 <= off)%Z -> (0 <= s4)%Z -> (0 <= d4)%Z ->
  (1 <= psl + off)%Z -> (psl + off + s4 < 2 ^ 64)%Z -> (1 <= pd)%Z -> (pd + d4 < 2 ^ 64)%Z ->
  (pd + 4 < 2 ^ 64)%Z -> (pd + 4 <= s - 240 \/ s <= pd)%Z ->
  (1 <= n < 2 ^ 31)%Z -> (if last then n = 1 else 1 < n)%Z -> (1 <= sls <= 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (psl + off)) 4 = Some bs0 -> length bs0 = 4%nat ->
  (f3 = false -> psl + off + 8 < 2 ^ 64 /\ rdn SEGS m (Z_to_bv 64 (psl + off + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z ->
  rdn SEGS m (Z_to_bv 64 pd) 4 = Some bd -> length bd = 4%nat -> store_ok SEGS m (Z_to_bv 64 pd) 4 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk) ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 12 = Z_to_bv 64 off -> getr regs 10 = Z_to_bv 64 pd ->
  getr regs 20 = Z_to_bv 64 pd -> getr regs 9 = Z_to_bv 64 (- n) -> getr regs 7 = Z_to_bv 64 (if f3 then 1 else 0) ->
  getr regs 17 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 -> getr regs 28 = Z_to_bv 64 18446744073709551611 ->
  getr regs 6 = Z_to_bv 64 31 -> getr regs 5 = Z_to_bv 64 32 -> getr regs 16 = Z_to_bv 64 (psl + s4) ->
  getr regs 13 = Z_to_bv 64 d4 -> getr regs 19 = Z_to_bv 64 s4 ->
  getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
  exists regs' (w : word),
    msteps SEGS (mkst regs RG14_L m rom) (mkst regs' (if last then RG_E else RG14_L) (wbytes m (Z_to_bv 64 pd) (word_to_le_bytes 4 w)) rom)
    /\ getr regs' 12 = Z_to_bv 64 (off + s4) /\ getr regs' 10 = Z_to_bv 64 (pd + d4) /\ getr regs' 20 = Z_to_bv 64 (pd + d4)
    /\ getr regs' 9 = Z_to_bv 64 (- (n - 1))
    /\ regs_agree (fun r => In r [9; 10; 12; 18; 20; 21; 22; 23]%list) regs regs'.
Proof.
  intros f3 last regs m s psl off pd s4 d4 n sls mk bs0 bs1 bd Hs Hs64 Hpsl Hoff Hs4 Hd4 Hps1 Hps2 Hpd1 Hpd2 Hpd4 Hfr Hn Hlast Hsls
    R0 L0 R1 Rd Ld SOK Cpsl Cmk Cz H2 H12 H10 H20 H9 H7 H17 H14 H28 H6 H5 H16 H13 H19 H30 H8.
  unfold RG14_L, RG_E.
  destruct f3.
  - destruct last; eexists; eexists; (split; [
      ld8 F_85648 D_85648 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_8564c D_8564c (Z_to_bv 64 (psl + off));
      stepb_tk F_85650 D_85650 ltac:(condZ);
      stepb_tk F_85658 D_85658 ltac:(condZ);
      ld4 F_85660 D_85660 (psl + off)%Z bs0 R0 L0;
      sn F_85664 D_85664;
      stepb_tk F_85668 D_85668 ltac:(condR);
      rgL_tail14 n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | rg14_post ]).
  - destruct (R1 eq_refl) as (Hps8 & R1' & L1).
    destruct last; eexists; eexists; (split; [
      ld8 F_85648 D_85648 (s - 136)%Z (Z_to_bv 64 psl) Cpsl;
      zv F_8564c D_8564c (Z_to_bv 64 (psl + off));
      stepb_tk F_85650 D_85650 ltac:(condZ);
      stepb_tk F_85658 D_85658 ltac:(condZ);
      ld4 F_85660 D_85660 (psl + off)%Z bs0 R0 L0;
      sn F_85664 D_85664;
      stepb_ft F_85668 D_85668 ltac:(condR);
      stepb_tk F_8566c D_8566c ltac:(condZ);
      stepb_tk F_85674 D_85674 ltac:(condZ);
      ld4 F_8567c D_8567c (psl + off + 4)%Z bs1 R1' L1;
      sn F_85680 D_85680; sn F_85684 D_85684; sn F_85688 D_85688; sn F_8568c D_8568c;
      rgL_tail14 n pd d4 psl off s4 s mk bd Rd Ld SOK Cmk Cz
    | rg14_post ]).
Qed.

(* [comment removed for export] *)
Lemma rg14_H2 : forall regs m (s nfw psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= nfw < 2 ^ 26)%Z -> (1 <= psrow < 2 ^ 64)%Z -> (1 <= pdrow < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 18 = Z_to_bv 64 pdrow ->
  getr regs 27 = Z_to_bv 64 1 ->
  exists regs',
    msteps SEGS (mkst regs RG14_H2 m rom) (mkst regs' RG14_I m rom)
    /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 1 /\ getr regs' 5 = Z_to_bv 64 1
    /\ getr regs' 7 = Z_to_bv 64 1 /\ getr regs' 9 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [5; 7; 9; 12; 15; 16]%list) regs regs'.
Proof.
  intros regs m s nfw psrow pdrow Hs Hs64 Hnfw Hps Hpd Cnfw C152 H2 H6 H18 H27.
  unfold RG14_H2, RG14_I. eexists. split.
  - ld8 F_854a4 D_854a4 (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
    stepb_ft F_854a8 D_854a8 ltac:(condZ).
    sn F_854ac D_854ac.
    snez1 F_854b0 D_854b0.
    snez1 F_854b4 D_854b4.
    sn F_854b8 D_854b8.
    ld8 F_854bc D_854bc (s - 152)%Z (Z_to_bv 64 1) C152.
    sn F_854c0 D_854c0.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma rg14_T2 : forall (last : bool) regs m (s i dh d4 s4 psrow pdrow : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 <= dh)%Z -> (dh < 2 ^ 31)%Z ->
  (if last then i + 1 = dh else i + 1 < dh)%Z -> (0 <= d4)%Z -> (0 <= s4)%Z ->
  (1 <= psrow)%Z -> (psrow + s4 < 2 ^ 64)%Z -> (1 <= pdrow)%Z -> (pdrow + d4 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 28 = Z_to_bv 64 i -> getr regs 13 = Z_to_bv 64 d4 ->
  getr regs 19 = Z_to_bv 64 s4 -> getr regs 6 = Z_to_bv 64 psrow -> getr regs 22 = Z_to_bv 64 psrow ->
  getr regs 18 = Z_to_bv 64 pdrow -> getr regs 24 = Z_to_bv 64 pdrow -> getr regs 14 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs RG14_T2 m rom) (mkst regs' (if last then RG14_X2 else RG14_H2) m rom)
    /\ getr regs' 28 = Z_to_bv 64 (i + 1) /\ getr regs' 6 = Z_to_bv 64 (psrow + s4) /\ getr regs' 22 = Z_to_bv 64 (psrow + s4)
    /\ getr regs' 18 = Z_to_bv 64 (pdrow + d4) /\ getr regs' 24 = Z_to_bv 64 (pdrow + d4)
    /\ regs_agree (fun r => In r [6; 12; 15; 16; 18; 22; 24; 28]%list) regs regs'.
Proof.
  intros last regs m s i dh d4 s4 psrow pdrow Hs Hs64 Hi Hidh Hdh Hlast Hd4 Hs4 Hps1 Hps2 Hpd1 Hpd2 Cz Cdh
    H2 H11 H5 H7 H6 H27 H18 H1 H19.
  unfold RG14_T2, RG14_X2, RG14_H2.
  destruct last; eexists; (split; [
    zv F_8555c D_8555c (Z_to_bv 64 (pdrow + d4));
    snez1 F_85560 D_85560;
    seqz0 F_85564 D_85564;
    stepb_tk F_85568 D_85568 ltac:(condR);
    sltu0 F_85570 D_85570;
    sn F_85574 D_85574; sn F_85578 D_85578;
    stepb_tk F_8557c D_8557c ltac:(condR);
    zv F_85584 D_85584 (Z_to_bv 64 (psrow + s4));
    snez1 F_85588 D_85588;
    seqz0 F_8558c D_8558c;
    stepb_tk F_85590 D_85590 ltac:(condR);
    sltu0 F_85598 D_85598;
    ld8 F_8559c D_8559c (s - 120)%Z (Z_to_bv 64 0) Cz;
    sn F_855a0 D_855a0; sn F_855a4 D_855a4;
    stepb_tk F_855a8 D_855a8 ltac:(condR);
    zv F_855b0 D_855b0 (Z_to_bv 64 (pdrow + d4));
    sn F_855b4 D_855b4; fixv' (Z_to_bv 64 (i + 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia);
    zv F_855b8 D_855b8 (Z_to_bv 64 (pdrow + d4));
    zv F_855bc D_855bc (Z_to_bv 64 (psrow + s4));
    sn F_855c0 D_855c0;
    ld8 F_855c4 D_855c4 (s - 112)%Z (Z_to_bv 64 dh) Cdh;
    first [ stepb_ft F_855c8 D_855c8 ltac:(condZ) | stepb_tk F_855c8 D_855c8 ltac:(condZ) ]; apply mst_refl
  | rg14_post ]).
Qed.

Ltac rs1_ld8h F D a v := stepLD F D (word_to_le_bytes 8 v) v
  ltac:(rdn_addr a; repeat rdn_peel1; apply SeqExec.rdn_wbytes_hit8; unorm; lia)
  ltac:(apply SeqExec.bytes_le_to_Z_8).
Ltac rs1_sok H := first [ eapply store_ok_mono; [ apply wbytes_grows | rs1_sok H ] | exact H ].
Ltac rs1_sd8 F D aa vv H :=
  chain_step;
  [ reflexivity
  | eapply SeqExec.step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; reflexivity | rs1_sok H ]
  | step_simpl ].
Ltac rs1_gen F D ALs ALd v := first [ zand0 F D andi_3 ALs | zand0 F D andi_3 ALd | zv F D v | sn F D ].
Ltac rs1_out := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; do 3 (rewrite MemSplit.wbytes_outside by (zlen; unorm; lia)); reflexivity.
Ltac rs1_grows := eapply mem_grows_trans; [ | apply wbytes_grows ]; eapply mem_grows_trans; [ | apply wbytes_grows ];
  apply wbytes_grows.
Ltac rs1_hit := repeat rdn_peel1; rewrite SeqExec.rdn_wbytes_hit8 by (unorm; lia).
(* [comment removed for export] *)
Lemma rg14_S1 : forall (fw f6 f7 : bool) regs m (s dxb psf pdf swpl dwpl dh c28 c30 c38 c40 c48 c50 : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= dxb < 32)%Z -> (if fw then dxb <> 0 else dxb = 0)%Z -> (0 <= swpl < 2 ^ 24)%Z -> (0 <= dwpl < 2 ^ 24)%Z ->
  getr regs 1 = Z_to_bv 64 dxb -> getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s - 200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c28)) ->
  rdn SEGS m (Z_to_bv 64 (s - 192)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c30)) ->
  rdn SEGS m (Z_to_bv 64 (s - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c38)) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c48)) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c50)) ->
  store_ok SEGS m (Z_to_bv 64 (s - 200)) 24 = true ->
  (fw = true ->
     (0 <= psf < 2 ^ 64)%Z /\ (0 <= pdf < 2 ^ 64)%Z /\ (psf mod 4 = 0)%Z /\ (pdf mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
     getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0) /\
     rdn SEGS m (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))) /\
     rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c40)) /\
     rg14_rc c28 c30 c38 c40 c48 c50 dh) ->
  exists regs' m',
    msteps SEGS (mkst regs RG14_S1 m rom) (mkst regs' (if fw then RG14_F else RG14_X1) m' rom)
    /\ (forall x : word, (u x < s - 200 \/ s - 176 <= u x)%Z -> m' x = m x) /\ mem_grows m m'
    /\ (forall c40' dh' : Z, rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 c40')) ->
          rg14_rc c28 c30 c38 c40' c48 c50 dh' -> rg14_rows m' s dh')
    /\ getr regs' 13 = Z_to_bv 64 (4 * dwpl) /\ getr regs' 19 = Z_to_bv 64 (4 * swpl) /\ getr regs' 14 = Z_to_bv 64 0
    /\ (fw = true -> getr regs' 28 = Z_to_bv 64 0 /\ getr regs' 23 = Z_to_bv 64 (psf + 4 * swpl) /\ getr regs' 16 = Z_to_bv 64 pdf
                     /\ getr regs' 9 = Z_to_bv 64 (- dh) /\ getr regs' 24 = Z_to_bv 64 (if f6 then 1 else 0)
                     /\ getr regs' 5 = Z_to_bv 64 (if f7 then 1 else 0) /\ getr regs' 7 = Z_to_bv 64 1
                     /\ getr regs' 22 = Z_to_bv 64 0 /\ getr regs' 17 = Z_to_bv 64 32)
    /\ regs_agree (fun r => In r [5; 7; 9; 11; 12; 13; 14; 16; 17; 19; 20; 22; 23; 24; 28]%list) regs regs'.
Proof.
  intros fw f6 f7 regs m s dxb psf pdf swpl dwpl dh c28 c30 c38 c40 c48 c50 Hs Hs64 Hdxb Hfw Hswpl Hdwpl H1 H2 H14
    Cswpl R28 R30 R38 R48 R50 SOK HF.
  unfold RG14_S1, RG14_F, RG14_X1.
  assert (SRl : forall x : Z, (- 2 ^ 63 <= x < 2 ^ 63)%Z -> v_srai (Z_to_bv 64 x) 63 = Z_to_bv 64 (if (x <? 0)%Z then -1 else 0)).
  { intros x Hx. unfold v_srai. rewrite bv_signed_Z by lia. rewrite Z.shiftr_div_pow2 by lia. f_equal.
    destruct (Z.ltb_spec x 0) as [N | P]; cbv beta iota.
    - symmetry. apply Z.div_unique with (r := (x + 2 ^ 63)%Z); lia.
    - apply Z.div_small; lia. }
  assert (SOK200 : store_ok SEGS m (Z_to_bv 64 (s - 200)) 8 = true).
  { apply (store_ok_sub SEGS m (Z_to_bv 64 (s - 200)) (Z_to_bv 64 (s - 200)) 24 8); [| exact SOK | |];
      unorm; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (SOK192 : store_ok SEGS m (Z_to_bv 64 (s - 192)) 8 = true).
  { apply (store_ok_sub SEGS m (Z_to_bv 64 (s - 200)) (Z_to_bv 64 (s - 192)) 24 8); [| exact SOK | |];
      unorm; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (SOK184 : store_ok SEGS m (Z_to_bv 64 (s - 184)) 8 = true).
  { apply (store_ok_sub SEGS m (Z_to_bv 64 (s - 200)) (Z_to_bv 64 (s - 184)) 24 8); [| exact SOK | |];
      unorm; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct fw.
  2:{ eexists. eexists. split.
      - sn F_852cc D_852cc.
        slli2 F_852d0 D_852d0 (4 * dwpl)%Z.
        ld8 F_852d4 D_852d4 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
        slli2 F_852d8 D_852d8 (4 * swpl)%Z.
        slti0 F_852dc D_852dc.
        ld8 F_852e0 D_852e0 (s - 160)%Z (Z_to_bv 64 c50) R50.
        ld8 F_852e4 D_852e4 (s - 200)%Z (Z_to_bv 64 c28) R28.
        sn F_852e8 D_852e8.
        rs1_sd8 F_852ec D_852ec (Z_to_bv 64 (s - 200)) (v_subw (Z_to_bv 64 c28) (Z_to_bv 64 c50)) SOK200.
        ld8 F_852f0 D_852f0 (s - 184)%Z (Z_to_bv 64 c38) R38.
        ld8 F_852f4 D_852f4 (s - 192)%Z (Z_to_bv 64 c30) R30.
        zv F_852f8 D_852f8 (Z_to_bv 64 (c30 + c38)).
        rs1_sd8 F_852fc D_852fc (Z_to_bv 64 (s - 184)) (Z_to_bv 64 (c30 + c38)) SOK184.
        ld8 F_85300 D_85300 (s - 168)%Z (Z_to_bv 64 c48) R48.
        sn F_85304 D_85304.
        rs1_sd8 F_85308 D_85308 (Z_to_bv 64 (s - 192)) (v_srai (Z_to_bv 64 c48) 63) SOK192.
        stepb_tk F_8530c D_8530c ltac:(condZ).
        apply mst_refl.
      - split; [ rs1_out | ]. split; [ rs1_grows | ]. split.
        + intros c40' dh' R40' RC'. pose proof RC' as RC2.
          destruct RC2 as (B28 & B30 & B38 & B40 & B48 & B50 & EQ).
          unfold rg14_rows. exists c28, c30, c38, c40', c48, c50.
          refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ RC')))))).
          * rs1_hit. rewrite subw_fit by lia. reflexivity.
          * rs1_hit. rewrite SRl by lia. reflexivity.
          * rs1_hit. reflexivity.
          * rdn_by R40'.
          * rdn_by R48.
          * rdn_by R50.
        + split; [ gres; pin; reflexivity | ]. split; [ gres; pin; reflexivity | ]. split; [ gres; pin; reflexivity | ].
          split; [ intros; discriminate | solve_regs_agree ]. }
  destruct (HF eq_refl) as (Hpsf & Hpdf & ALs & ALd & Hdh & H15 & H25 & H26 & Cf6 & R40 & RC).
  pose proof RC as RC0. destruct RC0 as (B28 & B30 & B38 & B40 & B48 & B50 & EQ).
  eexists. eexists. split.
  - sn F_852cc D_852cc.
    slli2 F_852d0 D_852d0 (4 * dwpl)%Z.
    ld8 F_852d4 D_852d4 (s - 152)%Z (Z_to_bv 64 swpl) Cswpl.
    slli2 F_852d8 D_852d8 (4 * swpl)%Z.
    slti0 F_852dc D_852dc.
    ld8 F_852e0 D_852e0 (s - 160)%Z (Z_to_bv 64 c50) R50.
    ld8 F_852e4 D_852e4 (s - 200)%Z (Z_to_bv 64 c28) R28.
    subw_v F_852e8 D_852e8 (c28 - c50)%Z.
    rs1_sd8 F_852ec D_852ec (Z_to_bv 64 (s - 200)) (Z_to_bv 64 (c28 - c50)) SOK200.
    ld8 F_852f0 D_852f0 (s - 184)%Z (Z_to_bv 64 c38) R38.
    ld8 F_852f4 D_852f4 (s - 192)%Z (Z_to_bv 64 c30) R30.
    zv F_852f8 D_852f8 (Z_to_bv 64 (c30 + c38)).
    rs1_sd8 F_852fc D_852fc (Z_to_bv 64 (s - 184)) (Z_to_bv 64 (c30 + c38)) SOK184.
    ld8 F_85300 D_85300 (s - 168)%Z (Z_to_bv 64 c48) R48.
    sn F_85304 D_85304. fixv' (Z_to_bv 64 (if (c48 <? 0)%Z then -1 else 0)) ltac:(apply SRl; lia).
    rs1_sd8 F_85308 D_85308 (Z_to_bv 64 (s - 192)) (Z_to_bv 64 (if (c48 <? 0)%Z then -1 else 0)) SOK192.
    stepb_ft F_8530c D_8530c ltac:(condZ).
    rs1_gen F_85310 D_85310 ALs ALd (Z_to_bv 64 (psf + 4 * swpl)).
    rs1_gen F_85314 D_85314 ALs ALd (Z_to_bv 64 (psf + 4 * swpl)).
    rs1_gen F_85318 D_85318 ALs ALd (Z_to_bv 64 (psf + 4 * swpl)).
    rs1_gen F_8531c D_8531c ALs ALd (Z_to_bv 64 (psf + 4 * swpl)).
    ld8 F_85320 D_85320 (s - 168)%Z (Z_to_bv 64 c48) R48.
    rs1_ld8h F_85324 D_85324 (s - 192)%Z (Z_to_bv 64 (if (c48 <? 0)%Z then -1 else 0)).
    sn F_85328 D_85328. fixv' (Z_to_bv 64 (Z.min 0 c48)) ltac:(rewrite <- (SRl c48) by lia; apply and_srai63_min; lia).
    ld8 F_8532c D_8532c (s - 160)%Z (Z_to_bv 64 c50) R50.
    rs1_ld8h F_85330 D_85330 (s - 184)%Z (Z_to_bv 64 (c30 + c38)).
    subw_v F_85334 D_85334 (c30 + c38 - c50)%Z.
    rs1_gen F_85338 D_85338 ALs ALd (Z_to_bv 64 (psf + 4 * swpl)).
    ld8 F_8533c D_8533c (s - 224)%Z (Z_to_bv 64 (if f6 then 1 else 0)) Cf6.
    sn F_85340 D_85340. fixv' (Z_to_bv 64 (if f6 then 1 else 0)) ltac:(apply andi1_if).
    sn F_85344 D_85344. fixv' (Z_to_bv 64 (if f7 then 1 else 0)) ltac:(apply andi1_if).
    ld8 F_85348 D_85348 (s - 176)%Z (Z_to_bv 64 c40) R40.
    subw_v F_8534c D_8534c (c30 + c38 - c50 - c40)%Z.
    rs1_gen F_85350 D_85350 ALs ALd (Z_to_bv 64 (psf + 4 * swpl)).
    rs1_gen F_85354 D_85354 ALs ALd (Z_to_bv 64 (psf + 4 * swpl)).
    addw_v F_85358 D_85358 (c30 + c38 - c50 - c40 + Z.min 0 c48)%Z.
    sn F_8535c D_8535c.
    sn F_85360 D_85360. fixv' (Z_to_bv 64 (Z.min 0 (c30 + c38 - c50 - c40 + Z.min 0 c48))) ltac:(apply and_srai63_min; lia).
    rs1_ld8h F_85364 D_85364 (s - 200)%Z (Z_to_bv 64 (c28 - c50)).
    subw_v F_85368 D_85368 (- dh)%Z.
    rs1_gen F_8536c D_8536c ALs ALd (Z_to_bv 64 (psf + 4 * swpl)).
    apply mst_refl.
  - split; [ rs1_out | ]. split; [ rs1_grows | ]. split.
    + intros c40' dh' R40' RC'. pose proof RC' as RC2.
      destruct RC2 as (B28' & B30' & B38' & B40' & B48' & B50' & EQ').
      unfold rg14_rows. exists c28, c30, c38, c40', c48, c50.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ RC')))))).
      * rs1_hit. reflexivity.
      * rs1_hit. reflexivity.
      * rs1_hit. reflexivity.
      * rdn_by R40'.
      * rdn_by R48.
      * rdn_by R50.
    + split; [ gres; pin; reflexivity | ]. split; [ gres; pin; reflexivity | ]. split; [ gres; pin; reflexivity | ].
      split; [ intros _ | solve_regs_agree ]. repeat split; gres; pin; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rg14_X1 : forall (nofull : bool) regs m (s psF pdF nfw : Z),
  (240 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= nfw < 2 ^ 26)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0))) ->
  getr regs 2 = Z_to_bv 64 (s - 240) ->
  (nofull = false ->
     (0 <= psF < 2 ^ 64)%Z /\ (0 <= pdF < 2 ^ 64)%Z /\ (psF mod 4 = 0)%Z /\ (pdF mod 4 = 0)%Z /\
     getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF /\
     rdn SEGS m (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)) /\
     store_ok SEGS m (Z_to_bv 64 (s - 152)) 8 = true) ->
  exists regs',
    msteps SEGS (mkst regs RG14_X1 m rom)
      (mkst regs' (if nofull then RG14_X2 else RG14_H2)
         (if nofull then m else wbytes m (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 1))) rom)
    /\ (nofull = false -> getr regs' 28 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 (4 * nfw) /\ getr regs' 23 = Z_to_bv 64 32
                          /\ getr regs' 25 = Z_to_bv 64 18446744073709551611 /\ getr regs' 15 = Z_to_bv 64 1
                          /\ getr regs' 27 = Z_to_bv 64 1 /\ getr regs' 1 = Z_to_bv 64 31
                          /\ getr regs' 22 = Z_to_bv 64 psF /\ getr regs' 24 = Z_to_bv 64 pdF)
    /\ regs_agree (fun r => In r [1; 12; 15; 20; 22; 23; 24; 25; 27; 28]%list) regs regs'.
Proof.
  intros nofull regs m s psF pdF nfw Hs Hs64 Hnfw Cnf H2 HF.
  unfold RG14_X1, RG14_X2, RG14_H2.
  destruct nofull.
  - eexists. split.
    { ld8 F_85468 D_85468 (s - 208)%Z (Z_to_bv 64 1) Cnf.
      stepb_tk F_8546c D_8546c ltac:(condR).
      apply mst_refl. }
    split; [intros; discriminate | solve_regs_agree].
  - destruct (HF eq_refl) as (HpsF & HpdF & ALs & ALd & H6 & H18 & Cnfw & SOK).
    eexists. split.
    + ld8 F_85468 D_85468 (s - 208)%Z (Z_to_bv 64 0) Cnf.
      stepb_ft F_8546c D_8546c ltac:(condR).
      sn F_85470 D_85470.
      first [ zand0 F_85474 D_85474 andi_3 ALs | zand0 F_85474 D_85474 andi_3 ALd ].
      first [ zand0 F_85478 D_85478 andi_3 ALd | zand0 F_85478 D_85478 andi_3 ALs ].
      ld8 F_8547c D_8547c (s - 128)%Z (Z_to_bv 64 nfw) Cnfw.
      slli2 F_85480 D_85480 (4 * nfw)%Z.
      sn F_85484 D_85484. sn F_85488 D_85488. sn F_8548c D_8548c.
      chain_step;
      [ reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 (s - 152)) (v := Z_to_bv 64 1);
        [ exact F_85490 | reflexivity | exact D_85490 | gres; imm_norm; addr_tac
        | first [ gres; reflexivity | gres; vm_compute; reflexivity ] | exact SOK ]
      | step_simpl ].
      sn F_85494 D_85494. sn F_85498 D_85498.
      sn F_8549c D_8549c. sn F_854a0 D_854a0.
      apply mst_refl.
    + split; [intros _ | solve_regs_agree]. repeat split; gres; pin; try reflexivity.
Qed.

Lemma jt14_gen_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 RG14_JT) 4 = Some (Z_to_le_bytes 4 RG14_JTV).
Proof. unfold RG14_JT, RG14_JTV. vm_refl_bv. Qed.

End Segs14G.
