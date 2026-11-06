(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherLib2 DitherTac DitherLoop.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15Kit.
Import O15Kit.O15MemcpyBase. Import O15Kit.O15Memcpy.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15_code_gqD O15DithBinLL O15DithBinLow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15CL2a.
Import O15CL2a.O15LeptDithBin.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac dl_get2 :=
  first [ eassumption
        | match goal with |- ?a = ?a => reflexivity end
        | match goal with H : getr ?R ?r = Z_to_bv 64 ?z' |- getr ?R ?r = Z_to_bv 64 ?z => rewrite H; f_equal; first [lia | ring] end
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_get2 end
        | match goal with K : keeps ?R ?R' |- getr ?R' ?r = _ => rewrite (K r ltac:(in_kept)); dl_get2 end ].

Section Low.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma memcpy_step : forall (Mr Mi : word -> option byte) regs (dst src n lod los : Z) (Nd Ns : nat) (retz : Z),
  mem_grows Mr Mi ->
  store_ok SEGS Mr (Z_to_bv 64 lod) Nd = true -> (0 <= lod)%Z -> (lod + Z.of_nat Nd <= 2 ^ 63)%Z -> (lod <= dst)%Z -> (dst + n <= lod + Z.of_nat Nd)%Z ->
  store_ok SEGS Mr (Z_to_bv 64 los) Ns = true -> (0 <= los)%Z -> (los + Z.of_nat Ns <= 2 ^ 63)%Z -> (los <= src)%Z -> (src + n <= los + Z.of_nat Ns)%Z ->
  (0 < n)%Z -> (dst + n <= src \/ src + n <= dst)%Z ->
  ret_ok (Z_to_bv 64 retz) -> getr regs 1 = Z_to_bv 64 retz -> getr regs 10 = Z_to_bv 64 dst -> getr regs 11 = Z_to_bv 64 src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs' bs, msteps SEGS (mkst regs (Z_to_bv 64 0x2ac48) Mi rom) (mkst regs' (Z_to_bv 64 retz) (wbytes Mi (Z_to_bv 64 dst) bs) rom)
    /\ Z.of_nat (length bs) = n /\ keeps regs regs'.
Proof.
  intros Mr Mi regs dst src n lod los Nd Ns retz G Sd Hd0 Hd1 Hd2 Hd3 Ss Hs0 Hs1 Hs2 Hs3 Hn D Hret H1 H10 H11 H12.
  destruct (reg_read SEGS Mr Mi los Ns src (Z.to_nat n) wr_readable_img G Ss Hs0 ltac:(lia) Hs2 ltac:(rewrite Z2Nat.id by lia; lia)) as [bs Rs].
  pose proof (rdn_length _ _ _ _ _ Rs) as Lbs.
  assert (HOK : mcH Mi (Z_to_bv 64 dst) (Z_to_bv 64 src) n bs).
  { constructor; rewrite ?u_Z2bv by lia; [lia | exact Lbs | rewrite Lbs; exact Rs | rewrite Lbs | lia | lia | lia].
    apply (reg_sok SEGS Mr Mi lod Nd dst (Z.to_nat n) G Sd Hd0 ltac:(lia) Hd2). rewrite Z2Nat.id by lia. lia. }
  destruct (ref_memcpy Mi _ _ n bs rom HOK regs (Z_to_bv 64 retz) Hret H1 H10 H11 H12) as (r' & RUN & KP).
  exists r', bs. split; [| split; [rewrite Lbs; apply Z2Nat.id; lia | exact KP]].
  replace (Z_to_bv 64 0x2ac48) with (0x2ac48 : word) by (apply bv_eq; reflexivity). exact RUN.
Qed.

(* [comment removed for export] *)
Variables (s datad w h wpld datas wpls bufs1 bufs2 lc uc : Z).
(* [comment removed for export] *)
Definition low_geom : Prop :=
  (4096 <= s - 160 /\ s < 2 ^ 47 /\ s mod 16 = 0 /\
   4096 <= datad /\ datad + 4 * (wpld * h) < 2 ^ 47 /\ datad mod 4 = 0 /\ 4096 <= datas /\ datas + 4 * (wpls * h) < 2 ^ 47 /\ datas mod 4 = 0 /\
   4096 <= bufs1 /\ bufs1 + 4 * wpls < 2 ^ 47 /\ bufs1 mod 4 = 0 /\ 4096 <= bufs2 /\ bufs2 + 4 * wpls < 2 ^ 47 /\ bufs2 mod 4 = 0 /\
   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ 1 <= wpls <= 5000 /\ 1 <= wpld <= 625 /\ w <= 4 * wpls /\ w <= 32 * wpld /\ 0 <= lc <= 255 /\ 0 <= uc <= 255 /\
   wpls * h <= 2 ^ 24 /\ wpld * h <= 2 ^ 24)%Z.
(* [comment removed for export] *)
Definition apart (a na b nb : Z) : Prop := (a + na <= b \/ b + nb <= a)%Z.
Definition low_disj : Prop :=
  apart (s - 160) 160 datad (4 * (wpld * h)) /\ apart (s - 160) 160 datas (4 * (wpls * h)) /\ apart (s - 160) 160 bufs1 (4 * wpls) /\
  apart (s - 160) 160 bufs2 (4 * wpls) /\ apart datad (4 * (wpld * h)) datas (4 * (wpls * h)) /\ apart datad (4 * (wpld * h)) bufs1 (4 * wpls) /\
  apart datad (4 * (wpld * h)) bufs2 (4 * wpls) /\ apart datas (4 * (wpls * h)) bufs1 (4 * wpls) /\ apart datas (4 * (wpls * h)) bufs2 (4 * wpls) /\
  apart bufs1 (4 * wpls) bufs2 (4 * wpls).
Hypothesis G : low_geom.
Hypothesis GD : low_disj.
Ltac geom := pose proof G as (Gs0 & Gs1 & Gs2 & Gd0 & Gd1 & ALd & Gs0' & Gs1' & ALs & Gb10 & Gb11 & ALb1 & Gb20 & Gb21 & ALb2 & Gw & Gh & Gwpls & Gwpld & Gw4 & Gw32 & Glc & Guc & Gsh & Gdh).
(* [comment removed for export] *)
Ltac dlia :=
  let go H := (let D_ := fresh "D_" in pose proof H as D_; unfold apart in D_; lia) in
  let DFd := fresh in let DFs := fresh in let DF1 := fresh in let DF2 := fresh in let Dds := fresh in let Dd1 := fresh in let Dd2 := fresh in
  let Ds1 := fresh in let Ds2 := fresh in let D12 := fresh in
  pose proof GD as (DFd & DFs & DF1 & DF2 & Dds & Dd1 & Dd2 & Ds1 & Ds2 & D12);
  first [ go DFd | go DFs | go DF1 | go DF2 | go Dds | go Dd1 | go Dd2 | go Ds1 | go Ds2 | go D12 ].

Definition RD : Z * Z := (datad, 4 * (wpld * h))%Z.
Definition RS : Z * Z := (datas, 4 * (wpls * h))%Z.
Definition RB1 : Z * Z := (bufs1, 4 * wpls)%Z.
Definition RB2 : Z * Z := (bufs2, 4 * wpls)%Z.
(* [comment removed for export] *)
Definition RW : list (Z * Z) := [((s - 160)%Z, 32%Z); RD; RB1; RB2].

(* [comment removed for export] *)
Definition rowregs (g3 g4 : word) (regs : bvmap 5 word) (i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 128) /\ getr regs 8 = Z_to_bv 64 bufs1 /\ getr regs 9 = Z_to_bv 64 uc /\ getr regs 18 = Z_to_bv 64 lc /\
  getr regs 19 = Z_to_bv 64 w /\ getr regs 20 = Z_to_bv 64 (wpls * 4) /\ getr regs 21 = Z_to_bv 64 bufs2 /\ getr regs 22 = Z_to_bv 64 (h - 1 - i) /\
  getr regs 23 = Z_to_bv 64 (wpls * 4) /\ getr regs 24 = Z_to_bv 64 (datas + 4 * (wpls * (i + 1))) /\ getr regs 25 = Z_to_bv 64 (datad + 4 * (wpld * i)) /\
  getr regs 26 = Z_to_bv 64 (4 * wpld) /\ getr regs 27 = Z_to_bv 64 (h - 1) /\ getr regs 3 = g3 /\ getr regs 4 = g4.
Definition exitregs (g3 g4 : word) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 128) /\ getr regs 8 = Z_to_bv 64 bufs1 /\ getr regs 9 = Z_to_bv 64 uc /\ getr regs 18 = Z_to_bv 64 lc /\
  getr regs 19 = Z_to_bv 64 w /\ getr regs 21 = Z_to_bv 64 bufs2 /\ getr regs 23 = Z_to_bv 64 (wpls * 4) /\ getr regs 27 = Z_to_bv 64 (h - 1) /\
  getr regs 3 = g3 /\ getr regs 4 = g4.

Lemma row_loop : forall (M1 : word -> option byte), regions_ok SEGS M1 [((s - 160)%Z, 32%Z); RD; RB1; RB2; RS] ->
  forall (g3 g4 : word) (n : nat) i regs Mi, (h - 1 - i <= Z.of_nat n)%Z -> (0 <= i < h - 1)%Z -> rinv RW M1 Mi -> rowregs g3 g4 regs i ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1a4f0) Mi rom) (mkst regs' (Z_to_bv 64 0x1a540) Mi' rom)
    /\ rinv RW M1 Mi' /\ exitregs g3 g4 regs'.
Proof.
  intros M1 RO1. geom. intros g3 g4. induction n as [|n IH]; intros i regs Mi Hn Hi RI LR; [lia|].
  destruct LR as (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H3 & H4).
  (* [comment removed for export] *)
  pose proof (row_bounds wpld i h ltac:(lia) ltac:(lia) ltac:(lia)) as P1.
  pose proof (row_bounds wpls (i + 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
  remember (datas + 4 * (wpls * (i + 1)))%Z as srow eqn:Esr. remember (datad + 4 * (wpld * i))%Z as drow eqn:Edr.
  assert (Rsr : (datas <= srow /\ srow + 4 * wpls <= datas + 4 * (wpls * h))%Z) by lia.
  assert (Rdr : (datad <= drow /\ drow + 4 * wpld <= datad + 4 * (wpld * h))%Z) by lia.
  assert (ALsr : (srow mod 4 = 0)%Z) by (subst srow; apply al4_add; exact ALs).
  assert (ALdr : (drow mod 4 = 0)%Z) by (subst drow; apply al4_add; exact ALd).
  clear P1 P2.
  assert (HYPr : wr_hyps s bufs1 bufs2 srow drow w lc uc (wpls * 4) (4 * wpld) (h - 1 - i) (h - 1)).
  { unfold wr_hyps. repeat split; first [assumption | lia]. }
  destruct (RO1 RB1 ltac:(dl_in0)) as (B1a & B1b & B1c & SOK1). destruct (RO1 RB2 ltac:(dl_in0)) as (B2a & B2b & B2c & SOK2).
  destruct (RO1 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS). destruct (RO1 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD).
  destruct (RO1 ((s - 160)%Z, 32%Z) ltac:(dl_in0)) as (Fa & Fb & Fc & SOKF).
  unfold RB1, RB2, RS, RD in *. cbn [fst snd] in *.
  (* [comment removed for export] *)
  destruct (wr_1a3f4 rom s bufs1 bufs2 srow drow w lc uc (wpls * 4) (4 * wpld) (h - 1 - i) (h - 1) HYPr fx regs Mi
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r1 & m1 & RUN1 & FR1 & E1_1 & E1_10 & E1_11 & E1_12 & AG1).
  assert (RI1 : rinv RW M1 m1) by (apply (rinv_cells RW [] M1 Mi m1 RI FR1); intros c []).
  destruct (memcpy_step M1 m1 r1 bufs1 bufs2 (wpls * 4) bufs1 bufs2 _ _ 107776 (proj1 RI1) SOK1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(dlia) ltac:(red; apply bv_eq; reflexivity) E1_1 E1_10 E1_11 E1_12)
    as (r2 & bs2 & RUN2 & L2 & K2).
  set (m2 := wbytes m1 (Z_to_bv 64 bufs1) bs2) in *.
  assert (RI2 : rinv RW M1 m2).
  { apply (rinv_wbytes RW M1 m1 bufs1 (wpls * 4) bs2 RI1 L2); [lia | lia |]. exists (bufs1, 4 * wpls)%Z. split; [unfold RW, RB1; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (wr_1a404 rom s bufs1 bufs2 srow drow w lc uc (wpls * 4) (4 * wpld) (h - 1 - i) (h - 1) HYPr fx r2 m2
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r3 & m3 & RUN3 & FR3 & E3_1 & E3_10 & E3_11 & E3_12 & AG3).
  assert (RI3 : rinv RW M1 m3) by (apply (rinv_cells RW [] M1 m2 m3 RI2 FR3); intros c []).
  destruct (memcpy_step M1 m3 r3 bufs2 srow (wpls * 4) bufs2 datas _ _ 107792 (proj1 RI3) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(dlia) ltac:(red; apply bv_eq; reflexivity) E3_1 E3_10 E3_11 E3_12)
    as (r4 & bs4 & RUN4 & L4 & K4).
  set (m4 := wbytes m3 (Z_to_bv 64 bufs2) bs4) in *.
  assert (RI4 : rinv RW M1 m4).
  { apply (rinv_wbytes RW M1 m3 bufs2 (wpls * 4) bs4 RI3 L4); [lia | lia |]. exists (bufs2, 4 * wpls)%Z. split; [unfold RW, RB2; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (wr_1a414 rom s bufs1 bufs2 srow drow w lc uc (wpls * 4) (4 * wpld) (h - 1 - i) (h - 1) HYPr fx r4 m4
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r5 & m5 & RUN5 & FR5 & E5_1 & E5_10 & E5_11 & E5_12 & E5_13 & E5_14 & E5_15 & E5_16 & AG5).
  assert (RI5 : rinv RW M1 m5) by (apply (rinv_cells RW [] M1 m4 m5 RI4 FR5); intros c []).
  assert (GLL : ll_geom (s - 128) drow bufs1 bufs2 (w - 1) lc uc wpls wpld).
  { unfold ll_geom. repeat split; first [assumption | lia | (apply al16_sub; [assumption | reflexivity]) | dlia]. }
  assert (ROLL : regions_ok SEGS m5 (R3 drow bufs1 bufs2 wpls wpld)).
  { intros r Hr. unfold R3 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M1 m5 datad _ drow _ (proj1 RI5) SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. eapply store_ok_mono; [exact (proj1 RI5) | exact SOK1].
    - repeat split; try lia. eapply store_ok_mono; [exact (proj1 RI5) | exact SOK2]. }
  destruct (dbll0_run rom (s - 128) drow bufs1 bufs2 (w - 1) lc uc wpls wpld GLL m5 ROLL r5 (Z_to_bv 64 107824) ltac:(red; apply bv_eq; reflexivity)
              ltac:(replace (s - 128 - 32)%Z with (s - 160)%Z by lia; eapply store_ok_mono; [exact (proj1 RI5) | exact SOKF])
              ltac:(dl_get2) E5_1 E5_10 ltac:(dl_get2) E5_12 E5_13 E5_14 E5_15 E5_16)
    as (r6 & m6 & RUN6 & RI6 & X2 & X8 & X9 & X18 & AG6).
  assert (RI6' : rinv RW M1 m6).
  { apply (rinv_trans RW M1 m5 m6 RI5). apply (rinv_weaken (R4 (s - 128) drow bufs1 bufs2 wpls wpld) RW m5 m6 RI6).
    intros r Hr. unfold R4, R3 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd].
    - exists ((s - 160)%Z, 32%Z). split; [unfold RW; dl_in0 | cbn [fst snd]; lia].
    - exists (datad, 4 * (wpld * h))%Z. split; [unfold RW, RD; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs1, 4 * wpls)%Z. split; [unfold RW, RB1; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs2, 4 * wpls)%Z. split; [unfold RW, RB2; dl_in0 | cbn [fst snd]; lia]. }
  assert (Y8 : getr r6 8 = Z_to_bv 64 bufs1) by (rewrite X8; dl_get2).
  assert (Y9 : getr r6 9 = Z_to_bv 64 uc) by (rewrite X9; dl_get2).
  assert (Y18 : getr r6 18 = Z_to_bv 64 lc) by (rewrite X18; dl_get2).
  (* [comment removed for export] *)
  destruct (wr_1a434 rom s bufs1 bufs2 srow drow w lc uc (wpls * 4) (4 * wpld) (h - 1 - i) (h - 1) HYPr fx r6 m6
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r7 & m7 & RUN7 & FR7 & E7_22 & E7_24 & E7_25 & AG7).
  assert (RI7 : rinv RW M1 m7) by (apply (rinv_cells RW [] M1 m6 m7 RI6' FR7); intros c []).
  assert (CHAIN : msteps SEGS (mkst regs (Z_to_bv 64 0x1a4f0) Mi rom) (mkst r7 (Z_to_bv 64 0x1a53c) m7 rom)).
  { exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4
           (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6 RUN7)))))). }
  destruct (Z_lt_ge_dec (i + 1) (h - 1)) as [LT|GE].
  - (* [comment removed for export] *)
    destruct (wr_1a440t rom s bufs1 bufs2 srow drow w lc uc (wpls * 4) (4 * wpld) (h - 1 - i) (h - 1) HYPr fx r7 m7 ltac:(ex_br)
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
      as (r8 & m8 & RUN8 & FR8 & AG8).
    assert (RI8 : rinv RW M1 m8) by (apply (rinv_cells RW [] M1 m7 m8 RI7 FR8); intros c []).
    destruct (IH (i + 1)%Z r8 m8 ltac:(lia) ltac:(lia) RI8) as (r9 & m9 & RUN9 & RI9 & EX9).
    { unfold rowregs. repeat split; dl_get2. }
    exists r9, m9. split; [exact (msteps_trans _ _ _ _ CHAIN (msteps_trans _ _ _ _ RUN8 RUN9))|]. split; [exact RI9 | exact EX9].
  - (* [comment removed for export] *)
    destruct (wr_1a440f rom s bufs1 bufs2 srow drow w lc uc (wpls * 4) (4 * wpld) (h - 1 - i) (h - 1) HYPr fx r7 m7 ltac:(ex_br)
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
      as (r8 & m8 & RUN8 & FR8 & AG8).
    assert (RI8 : rinv RW M1 m8) by (apply (rinv_cells RW [] M1 m7 m8 RI7 FR8); intros c []).
    exists r8, m8. split; [exact (msteps_trans _ _ _ _ CHAIN RUN8)|]. split; [exact RI8|].
    unfold exitregs. repeat split; dl_get2.
Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lrow : Z := (datad + 4 * ((h - 1) * wpld))%Z.
Definition RF1 : list (Z * Z) := [(lrow, 4 * wpld)%Z; RB1].
Definition f1regs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 8 = Z_to_bv 64 bufs1 /\ getr regs 9 = Z_to_bv 64 uc /\ getr regs 10 = Z_to_bv 64 j /\ getr regs 11 = Z_to_bv 64 j /\
  getr regs 12 = Z_to_bv 64 (bufs1 + 1) /\ getr regs 13 = Z_to_bv 64 (w - 1) /\ getr regs 14 = Z_to_bv 64 18446744071562067968 /\
  getr regs 18 = Z_to_bv 64 lc /\ getr regs 22 = Z_to_bv 64 lrow.

Lemma lrow_facts : (datad <= lrow /\ lrow + 4 * wpld <= datad + 4 * (wpld * h) /\ lrow mod 4 = 0)%Z.
Proof.
  geom. unfold lrow. pose proof (row_bounds wpld (h - 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as P.
  replace ((h - 1) * wpld)%Z with (wpld * (h - 1))%Z by ring. split; [lia|]. split; [lia|]. apply al4_add. exact ALd.
Qed.

Lemma wfh : forall j, (0 <= j < w - 1)%Z -> wf_hyps bufs1 lrow j (w - 1) lc uc wpls.
Proof. intros j Hj. geom. destruct lrow_facts as (L1 & L2 & L3). unfold wf_hyps. repeat split; first [assumption | lia]. Qed.

Lemma wf_cells_in : forall j, (0 <= j < w - 1)%Z -> cells_in RF1 (wf_1a4a0_cells_def bufs1 lrow j (w - 1) lc uc wpls).
Proof.
  intros j Hj. geom. destruct lrow_facts as (L1 & L2 & L3). destruct (al4_ex _ ALb1) as [cb1 Ecb1].
  pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ.
  intros c Hc. unfold wf_1a4a0_cells_def in Hc. cbn [In] in Hc.
  repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|];
            first [ (exists (lrow, 4 * wpld)%Z; split; [unfold RF1; dl_in0 | cbn [fst snd]; dl_lia])
                  | (exists (bufs1, 4 * wpls)%Z; split; [unfold RF1, RB1; dl_in0 | cbn [fst snd]; dl_lia]) ] |]). destruct Hc.
Qed.

Lemma f1_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr RF1 ->
  forall (n : nat) j regs Mi, (w - 1 - j <= Z.of_nat n)%Z -> (0 <= j < w - 1)%Z -> rinv RF1 Mr Mi -> f1regs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1a59c) Mi rom) (mkst regs' (Z_to_bv 64 0x1a634) Mi' rom)
    /\ rinv RF1 Mr Mi' /\ regs_agree (fun r => In r [5; 10; 11; 15; 16; 17]%list) regs regs'.
Proof.
  intros Mr ROr. geom. induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H8 & H9 & H10 & H11 & H12 & H13 & H14 & H18 & H22).
  pose proof (cells_ok_of SEGS Mr Mi RF1 _ ROr (proj1 RI) (wf_cells_in j Hj)) as CK.
  destruct (wf_1a4a0_path rom bufs1 lrow j (w - 1) lc uc wpls (wfh j Hj) fx regs Mi CK H8 H9 H10 H11 H12 H13 H14 H18 H22)
    as (r1 & m1 & RUN1 & FR1 & E10 & E11 & AG1).
  pose proof (rinv_cells RF1 _ Mr Mi m1 RI FR1 (wf_cells_in j Hj)) as RI1.
  assert (CI0 : cells_in RF1 []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) (w - 1)) as [LT|GE].
  - destruct (wf_1a49cf rom bufs1 lrow j (w - 1) lc uc wpls (wfh j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RF1 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold f1regs. repeat split; dl_get2. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (wf_1a49ct rom bufs1 lrow j (w - 1) lc uc wpls (wfh j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RF1 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RALL : list (Z * Z) := [((s - 160)%Z, 160%Z); RD; RB1; RB2].

Lemma low_ret : forall regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (mkst regs (Z_to_bv 64 0x1a69c) m rom) (mkst regs ret m rom).
Proof.
  intros regs m ret Hret H1. replace (Z_to_bv 64 0x1a69c) with (0x1a69c : word) by (apply bv_eq; reflexivity).
  stepret F_1a644 D_1a644 ret ltac:(exact H1). apply mst_refl.
Qed.

(* [comment removed for export] *)
Lemma frame_keep : forall (M1 Mi : word -> option byte) (k : Z) v, rinv RW M1 Mi -> (8 <= k <= 128)%Z ->
  rdn SEGS M1 (Z_to_bv 64 (s - k)) 8 = Some v -> rdn SEGS Mi (Z_to_bv 64 (s - k)) 8 = Some v.
Proof.
  intros M1 Mi k v RI Hk R. geom. rewrite <- R. apply (rinv_rdn SEGS RW M1 Mi (s - k) 8 RI); [lia | cbn; lia |].
  intros r Hr. unfold RW in Hr. cbn [In] in Hr. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold RD, RB1, RB2; cbn [fst snd]; first [lia | dlia].
Qed.

Lemma dbl_run : forall (M0 : word -> option byte) regs (ret : word), ret_ok ret ->
  regions_ok SEGS M0 [((s - 160)%Z, 160%Z); RD; RB1; RB2; RS] ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 w -> getr regs 12 = Z_to_bv 64 h ->
  getr regs 13 = Z_to_bv 64 wpld -> getr regs 14 = Z_to_bv 64 datas -> getr regs 15 = Z_to_bv 64 wpls -> getr regs 16 = Z_to_bv 64 bufs1 ->
  getr regs 17 = Z_to_bv 64 bufs2 -> getr regs 28 = Z_to_bv 64 lc -> getr regs 29 = Z_to_bv 64 uc ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1a454) M0 rom) (mkst regs' ret M' rom)
    /\ rinv RALL M0 M' /\ getr regs' 2 = Z_to_bv 64 s
    /\ (forall r, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros M0 regs ret Hret RO0 H2 H1 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29. geom.
  destruct (RO0 ((s - 160)%Z, 160%Z) ltac:(dl_in0)) as (Fa & Fb & Fc & SOKF0). destruct (RO0 RB1 ltac:(dl_in0)) as (B1a & B1b & B1c & SOK1).
  destruct (RO0 RB2 ltac:(dl_in0)) as (B2a & B2b & B2c & SOK2). destruct (RO0 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS).
  destruct (RO0 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD).
  unfold RB1, RB2, RS, RD in *. cbn [fst snd] in *.
  assert (sokF : forall k, (8 <= k <= 160)%Z -> store_ok SEGS M0 (Z_to_bv 64 (s - k)) 8 = true).
  { intros k Hk. apply (reg_sok SEGS M0 M0 (s - 160) _ (s - k) 8 (mem_grows_refl _) SOKF0); rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (HYPp : wp_hyps s datad w h wpld datas wpls bufs1 bufs2 lc uc) by (unfold wp_hyps; repeat split; first [assumption | lia]).
  (* [comment removed for export] *)
  destruct (wp_1a358 rom s datad w h wpld datas wpls bufs1 bufs2 lc uc HYPp fx regs M0
              (sokF 8%Z ltac:(lia))
              (sokF 16%Z ltac:(lia))
              (sokF 24%Z ltac:(lia))
              (sokF 32%Z ltac:(lia))
              (sokF 40%Z ltac:(lia))
              (sokF 48%Z ltac:(lia))
              (sokF 56%Z ltac:(lia))
              (sokF 64%Z ltac:(lia))
              (sokF 72%Z ltac:(lia))
              (sokF 80%Z ltac:(lia))
              (sokF 88%Z ltac:(lia))
              (sokF 96%Z ltac:(lia))
              (sokF 104%Z ltac:(lia))
              (sokF 112%Z ltac:(lia))
              (sokF 120%Z ltac:(lia))
              H2 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29)
    as (r1 & m1 & RUN1 & FR1 & E1_1 & E1_2 & E1_8 & E1_9 & E1_10 & E1_11 & E1_12 & E1_18 & E1_19 & E1_21 & E1_23 & E1_24 & E1_25 & E1_26
        & SVra & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & SV22 & SV23 & SV24 & SV25 & SV26 & SV27 & SVwpld & SVdatad & AG1).
  assert (RI1 : rinv RALL M0 m1).
  { apply (rinv_cells RALL _ M0 M0 m1 (rinv_refl _ _) FR1). intros c Hc. cbn [In] in Hc.
    repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|]; exists ((s - 160)%Z, 160%Z); split; [unfold RALL; dl_in0 | cbn [fst snd]; lia] |]). destruct Hc. }
  assert (RO1 : regions_ok SEGS m1 [((s - 160)%Z, 32%Z); RD; RB1; RB2; RS]).
  { intros r Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
    - cbn [fst snd]. repeat split; try lia. apply (reg_sok SEGS M0 m1 (s - 160) _ (s - 160) _ (proj1 FR1) SOKF0); rewrite ?Z2Nat.id by lia; cbn; lia.
    - apply (regions_ok_grows SEGS M0 m1 _ RO0 (proj1 FR1)). right. exact Hr. }
  assert (KCw1 : rdn SEGS m1 (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 wpld)) by (rewrite <- w2b_Z by lia; exact SVwpld).
  assert (KCd1 : rdn SEGS m1 (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 datad)) by (rewrite <- w2b_Z by lia; exact SVdatad).
  (* [comment removed for export] *)
  destruct (memcpy_step M0 m1 r1 bufs2 datas (wpls * 4) bufs2 datas _ _ 107720 (proj1 FR1) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pose proof (row_bounds wpls 0 h ltac:(lia) ltac:(lia) ltac:(lia)); lia) ltac:(lia)
              ltac:(pose proof (row_bounds wpls 0 h ltac:(lia) ltac:(lia) ltac:(lia)); dlia)
              ltac:(red; apply bv_eq; reflexivity) E1_1 E1_10 E1_11 E1_12)
    as (r2 & bs2 & RUN2 & L2 & K2).
  set (m2 := wbytes m1 (Z_to_bv 64 bufs2) bs2) in *.
  assert (RI2 : rinv RW m1 m2).
  { apply (rinv_wbytes RW m1 m1 bufs2 (wpls * 4) bs2 (rinv_refl _ _) L2); [lia | lia |]. exists (bufs2, 4 * wpls)%Z. split; [unfold RW, RB2; dl_in0 | cbn [fst snd]; lia]. }
  assert (HYPa : wa_hyps s datad w h wpld datas wpls bufs1 bufs2 lc uc) by exact HYPp.
  destruct (wa_1a3cc rom s datad w h wpld datas wpls bufs1 bufs2 lc uc HYPa fx r2 m2
              (frame_keep m1 m2 112 _ RI2 ltac:(lia) KCw1) (frame_keep m1 m2 120 _ RI2 ltac:(lia) KCd1) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_27 & AG3).
  assert (RI3 : rinv RW m1 m3) by (apply (rinv_cells RW [] m1 m2 m3 RI2 FR3); intros c []).
  (* [comment removed for export] *)
  assert (MID : exists r5 m5, msteps SEGS (mkst r3 (Z_to_bv 64 0x1a4d0) m3 rom) (mkst r5 (Z_to_bv 64 0x1a540) m5 rom) /\ rinv RW m1 m5 /\ exitregs (getr regs 3) (getr regs 4) r5).
  { destruct (Z.eq_dec h 1) as [H1'|H2'].
    - destruct (wa_1a3d4t rom s datad w h wpld datas wpls bufs1 bufs2 lc uc HYPa fx r3 m3 ltac:(ex_br)
                  (frame_keep m1 m3 112 _ RI3 ltac:(lia) KCw1) (frame_keep m1 m3 120 _ RI3 ltac:(lia) KCd1) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
        as (r4 & m4 & RUN4 & FR4 & AG4).
      exists r4, m4. split; [exact RUN4|]. split; [apply (rinv_cells RW [] m1 m3 m4 RI3 FR4); intros c []|].
      unfold exitregs. repeat split; dl_get2.
    - destruct (wa_1a3d4f rom s datad w h wpld datas wpls bufs1 bufs2 lc uc HYPa fx r3 m3 ltac:(ex_br)
                  (frame_keep m1 m3 112 _ RI3 ltac:(lia) KCw1) (frame_keep m1 m3 120 _ RI3 ltac:(lia) KCd1) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
        as (r4 & m4 & RUN4 & FR4 & E4_10 & E4_20 & E4_22 & E4_24 & E4_25 & E4_26 & AG4).
      assert (RI4 : rinv RW m1 m4) by (apply (rinv_cells RW [] m1 m3 m4 RI3 FR4); intros c []).
      destruct (row_loop m1 RO1 (getr regs 3) (getr regs 4) (Z.to_nat h) 0%Z r4 m4 ltac:(lia) ltac:(lia) RI4) as (r5 & m5 & RUN5 & RI5 & EX5).
      { unfold rowregs. repeat split; dl_get2. }
      exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN4 RUN5)|]. split; [exact RI5 | exact EX5]. }
  destruct MID as (r5 & m5 & RUN5 & RI5 & EX5).
  destruct EX5 as (X2 & X8 & X9 & X18 & X19 & X21 & X23 & X27 & X3 & X4).
  pose proof (row_bounds wpld (h - 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as PR.
  assert (HYPl : wl_hyps s bufs1 bufs2 w lc uc (wpls * 4) (h - 1) wpld datad).
  { unfold wl_hyps. replace ((h - 1) * wpld)%Z with (wpld * (h - 1))%Z by ring. repeat split; first [assumption | lia]. }
  (* [comment removed for export] *)
  destruct (wl_1a444 rom s bufs1 bufs2 w lc uc (wpls * 4) (h - 1) wpld datad HYPl fx r5 m5
              (frame_keep m1 m5 112 _ RI5 ltac:(lia) KCw1) (frame_keep m1 m5 120 _ RI5 ltac:(lia) KCd1) X2 X8 X9 X18 X19 X21 X23 X27)
    as (r6 & m6 & RUN6 & FR6 & E6_1 & E6_10 & E6_11 & E6_12 & AG6).
  assert (RI6 : rinv RW m1 m6) by (apply (rinv_cells RW [] m1 m5 m6 RI5 FR6); intros c []).
  destruct (memcpy_step M0 m6 r6 bufs1 bufs2 (wpls * 4) bufs1 bufs2 _ _ 107856 (mem_grows_trans _ _ _ (proj1 FR1) (proj1 RI6))
              SOK1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(dlia)
              ltac:(red; apply bv_eq; reflexivity) E6_1 E6_10 E6_11 E6_12)
    as (r7 & bs7 & RUN7 & L7 & K7).
  set (m7 := wbytes m6 (Z_to_bv 64 bufs1) bs7) in *.
  assert (RI7 : rinv RW m1 m7).
  { apply (rinv_wbytes RW m1 m6 bufs1 (wpls * 4) bs7 RI6 L7); [lia | lia |]. exists (bufs1, 4 * wpls)%Z. split; [unfold RW, RB1; dl_in0 | cbn [fst snd]; lia]. }
  destruct (wl_1a454 rom s bufs1 bufs2 w lc uc (wpls * 4) (h - 1) wpld datad HYPl fx r7 m7
              (frame_keep m1 m7 112 _ RI7 ltac:(lia) KCw1) (frame_keep m1 m7 120 _ RI7 ltac:(lia) KCd1) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r8 & m8 & RUN8 & FR8 & E8_10 & E8_22 & AG8).
  assert (RI8 : rinv RW m1 m8) by (apply (rinv_cells RW [] m1 m7 m8 RI7 FR8); intros c []).
  destruct lrow_facts as (LR1 & LR2 & LR3).
  (* [comment removed for export] *)
  assert (MID2 : exists r10 m10, msteps SEGS (mkst r8 (Z_to_bv 64 0x1a568) m8 rom) (mkst r10 (Z_to_bv 64 0x1a634) m10 rom) /\ rinv RW m1 m10
                   /\ getr r10 2 = Z_to_bv 64 (s - 128) /\ getr r10 8 = Z_to_bv 64 bufs1 /\ getr r10 19 = Z_to_bv 64 (w - 1) /\ getr r10 22 = Z_to_bv 64 lrow
                   /\ getr r10 3 = getr regs 3 /\ getr r10 4 = getr regs 4).
  { destruct (Z.eq_dec w 1) as [W1|W2].
    - destruct (wl_1a46ct rom s bufs1 bufs2 w lc uc (wpls * 4) (h - 1) wpld datad HYPl fx r8 m8 ltac:(ex_br)
                  (frame_keep m1 m8 112 _ RI8 ltac:(lia) KCw1) (frame_keep m1 m8 120 _ RI8 ltac:(lia) KCd1) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
        as (r9 & m9 & RUN9 & FR9 & E9_19 & AG9).
      exists r9, m9. split; [exact RUN9|]. split; [apply (rinv_cells RW [] m1 m8 m9 RI8 FR9); intros c []|].
      unfold lrow. repeat split; dl_get2.
    - destruct (wl_1a46cf rom s bufs1 bufs2 w lc uc (wpls * 4) (h - 1) wpld datad HYPl fx r8 m8 ltac:(ex_br)
                  (frame_keep m1 m8 112 _ RI8 ltac:(lia) KCw1) (frame_keep m1 m8 120 _ RI8 ltac:(lia) KCd1) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
        as (r9 & m9 & RUN9 & FR9 & E9_10 & E9_11 & E9_12 & E9_13 & E9_14 & E9_19 & AG9).
      assert (RI9 : rinv RW m1 m9) by (apply (rinv_cells RW [] m1 m8 m9 RI8 FR9); intros c []).
      assert (ROF : regions_ok SEGS m9 RF1).
      { intros r Hr. unfold RF1, RB1 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
        - repeat split; try lia. apply (reg_sok SEGS M0 m9 datad _ lrow _ (mem_grows_trans _ _ _ (proj1 FR1) (proj1 RI9)) SOKD); rewrite ?Z2Nat.id by lia; lia.
        - repeat split; try lia. eapply store_ok_mono; [exact (mem_grows_trans _ _ _ (proj1 FR1) (proj1 RI9)) | exact SOK1]. }
      destruct (f1_loop m9 ROF (Z.to_nat w) 0%Z r9 m9 ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r10 & m10 & RUN10 & RI10 & AG10).
      { unfold f1regs, lrow. repeat split; dl_get2. }
      exists r10, m10. split; [exact (msteps_trans _ _ _ _ RUN9 RUN10)|]. split.
      { apply (rinv_trans RW m1 m9 m10 RI9). apply (rinv_weaken RF1 RW m9 m10 RI10).
        intros r Hr. unfold RF1, RB1 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
        - exists (datad, 4 * (wpld * h))%Z. split; [unfold RW, RD; dl_in0 | cbn [fst snd]; lia].
        - exists (bufs1, 4 * wpls)%Z. split; [unfold RW, RB1; dl_in0 | cbn [fst snd]; lia]. }
      unfold lrow. repeat split; dl_get2. }
  destruct MID2 as (r10 & m10 & RUN10 & RI10 & Y2 & Y8 & Y19 & Y22 & Y3 & Y4).
  (* [comment removed for export] *)
  assert (HYPe : we_hyps s bufs1 lrow (w - 1)) by (unfold we_hyps; repeat split; first [assumption | lia]).
  assert (CIe : cells_in RF1 (we_1a538_cells_def s bufs1 lrow (w - 1))).
  { destruct (al4_ex _ ALb1) as [cb1 Ecb1]. pose proof (dl_div_bounds (w - 1) 32 ltac:(lia) ltac:(lia)) as DW.
    intros c Hc. unfold we_1a538_cells_def in Hc. cbn [In] in Hc.
    repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|];
              first [ (exists (lrow, 4 * wpld)%Z; split; [unfold RF1; dl_in0 | cbn [fst snd]; dl_lia])
                    | (exists (bufs1, 4 * wpls)%Z; split; [unfold RF1, RB1; dl_in0 | cbn [fst snd]; dl_lia]) ] |]). destruct Hc. }
  assert (G010 : mem_grows M0 m10) by exact (mem_grows_trans _ _ _ (proj1 FR1) (proj1 RI10)).
  assert (ROF0 : regions_ok SEGS M0 RF1).
  { intros r Hr. unfold RF1, RB1 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M0 M0 datad _ lrow _ (mem_grows_refl _) SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. exact SOK1. }
  pose proof (cells_ok_of SEGS M0 m10 RF1 _ ROF0 G010 CIe) as CKe.
  destruct (we_1a538_path rom s bufs1 lrow (w - 1) HYPe fx r10 m10 CKe Y2 Y8 Y19 Y22) as (r11 & m11 & RUN11 & FR11 & E11_8 & AG11).
  assert (RI11 : rinv RW m1 m11).
  { apply (rinv_cells RW _ m1 m10 m11 RI10 FR11). intros c Hc. destruct (CIe c Hc) as (Hn & r & Hr & R1 & R2). split; [exact Hn|].
    unfold RF1, RB1 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in R1, R2.
    - exists (datad, 4 * (wpld * h))%Z. split; [unfold RW, RD; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs1, 4 * wpls)%Z. split; [unfold RW, RB1; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  assert (HYPee : we_hyps s bufs1 lrow (w - 1)) by exact HYPe.
  destruct (we_1a568_e rom s bufs1 lrow (w - 1) HYPee fx r11 m11 _ _ _ _ _ _ _ _ _ _ _ _ _
              (frame_keep m1 m11 8 _ RI11 ltac:(lia) SVra) (frame_keep m1 m11 16 _ RI11 ltac:(lia) SV8) (frame_keep m1 m11 24 _ RI11 ltac:(lia) SV9)
              (frame_keep m1 m11 32 _ RI11 ltac:(lia) SV18) (frame_keep m1 m11 40 _ RI11 ltac:(lia) SV19) (frame_keep m1 m11 48 _ RI11 ltac:(lia) SV20)
              (frame_keep m1 m11 56 _ RI11 ltac:(lia) SV21) (frame_keep m1 m11 64 _ RI11 ltac:(lia) SV22) (frame_keep m1 m11 72 _ RI11 ltac:(lia) SV23)
              (frame_keep m1 m11 80 _ RI11 ltac:(lia) SV24) (frame_keep m1 m11 88 _ RI11 ltac:(lia) SV25) (frame_keep m1 m11 96 _ RI11 ltac:(lia) SV26)
              (frame_keep m1 m11 104 _ RI11 ltac:(lia) SV27) ltac:(dl_get2))
    as (r12 & m12 & RUN12 & FR12 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & AG12).
  rewrite rdv_word8 in Z1, Z8, Z9, Z18, Z19, Z20, Z21, Z22, Z23, Z24, Z25, Z26, Z27.
  pose proof (low_ret r12 m12 ret Hret ltac:(rewrite Z1; exact H1)) as RUN13.
  assert (Z3 : getr r12 3 = getr regs 3) by (rewrite (AG12 3%bv) by notin_list; rewrite (AG11 3%bv) by notin_list; exact Y3).
  assert (Z4 : getr r12 4 = getr regs 4) by (rewrite (AG12 4%bv) by notin_list; rewrite (AG11 4%bv) by notin_list; exact Y4).
  exists r12, m12. split.
  { exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6
           (msteps_trans _ _ _ _ RUN7 (msteps_trans _ _ _ _ RUN8 (msteps_trans _ _ _ _ RUN10 (msteps_trans _ _ _ _ RUN11 (msteps_trans _ _ _ _ RUN12 RUN13)))))))))). }
  split.
  { apply (rinv_trans RALL M0 m1 m12 RI1). apply (rinv_weaken RW RALL m1 m12).
    - apply (rinv_cells RW [] m1 m11 m12 RI11 FR12). intros c [].
    - intros r Hr. unfold RW in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]].
      + exists ((s - 160)%Z, 160%Z). split; [unfold RALL; dl_in0 | cbn [fst snd]; lia].
      + exists RD. split; [unfold RALL; dl_in0 | lia].
      + exists RB1. split; [unfold RALL; dl_in0 | lia].
      + exists RB2. split; [unfold RALL; dl_in0 | lia]. }
  split; [exact Z2|].
  intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr.
Qed.




End Low.
