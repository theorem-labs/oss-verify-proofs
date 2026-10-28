(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherLib2 DitherTac DitherLoop.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15Kit.
Import V15Kit.V15MemcpyBase. Import V15Kit.V15Memcpy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15_code_gqD V15DithBinLow.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL2a.
Import V15CL2a.V15LeptDithBin.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac dl_get2 :=
  first [ eassumption
        | match goal with |- ?a = ?a => reflexivity end
        | match goal with H : getr ?R ?r = Z_to_bv 64 ?z' |- getr ?R ?r = Z_to_bv 64 ?z => rewrite H; f_equal; first [lia | ring] end
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_get2 end
        | match goal with K : keeps ?R ?R' |- getr ?R' ?r = _ => rewrite (K r ltac:(in_kept)); dl_get2 end
        | match goal with X : getr ?R' ?r = getr ?R ?r |- getr ?R' ?r = _ => rewrite X; dl_get2 end
        | match goal with KP : (forall r0, In r0 _ -> getr ?R' r0 = getr ?R r0) |- getr ?R' ?r = _ => rewrite (KP r ltac:(in_kept)); dl_get2 end ].

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
  exists regs' bs, msteps SEGS (mkst regs (Z_to_bv 64 0x326c4) Mi rom) (mkst regs' (Z_to_bv 64 retz) (wbytes Mi (Z_to_bv 64 dst) bs) rom)
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
  replace (Z_to_bv 64 0x326c4) with (0x326c4 : word) by (apply bv_eq; reflexivity). exact RUN.
Qed.

(* [comment removed for export] *)
Variables (s datad w h wpld datas wpls bufs1 bufs2 lc uc : Z).
(* [comment removed for export] *)
Definition low_geom : Prop :=
  (4096 <= s - 192 /\ s < 2 ^ 47 /\ s mod 16 = 0 /\
   4096 <= datad /\ datad + 4 * (wpld * h) < 2 ^ 47 /\ datad mod 4 = 0 /\ 4096 <= datas /\ datas + 4 * (wpls * h) < 2 ^ 47 /\ datas mod 4 = 0 /\
   4096 <= bufs1 /\ bufs1 + 4 * wpls < 2 ^ 47 /\ bufs1 mod 4 = 0 /\ 4096 <= bufs2 /\ bufs2 + 4 * wpls < 2 ^ 47 /\ bufs2 mod 4 = 0 /\
   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ 1 <= wpls <= 5000 /\ 1 <= wpld <= 625 /\ w <= 4 * wpls /\ w <= 32 * wpld /\ 0 <= lc <= 255 /\ 0 <= uc <= 255 /\
   wpls * h <= 2 ^ 24 /\ wpld * h <= 2 ^ 24)%Z.
(* [comment removed for export] *)
Definition low_disj : Prop :=
  apart (s - 192) 192 datad (4 * (wpld * h)) /\ apart (s - 192) 192 datas (4 * (wpls * h)) /\ apart (s - 192) 192 bufs1 (4 * wpls) /\
  apart (s - 192) 192 bufs2 (4 * wpls) /\ apart datad (4 * (wpld * h)) datas (4 * (wpls * h)) /\ apart datad (4 * (wpld * h)) bufs1 (4 * wpls) /\
  apart datad (4 * (wpld * h)) bufs2 (4 * wpls) /\ apart datas (4 * (wpls * h)) bufs1 (4 * wpls) /\ apart datas (4 * (wpls * h)) bufs2 (4 * wpls) /\
  apart bufs1 (4 * wpls) bufs2 (4 * wpls).
Hypothesis G : low_geom.
Hypothesis GD : low_disj.
Ltac geom := pose proof G as (Gs0 & Gs1 & Gs2 & Gd0 & Gd1 & ALd & Gs0' & Gs1' & ALs & Gb10 & Gb11 & ALb1 & Gb20 & Gb21 & ALb2 & Gw & Gh & Gwpls & Gwpld & Gw4 & Gw32 & Glc & Guc & Gsh & Gdh).
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
Definition RW : list (Z * Z) := [((s - 192)%Z, 48%Z); RD; RB1; RB2].

(* [comment removed for export] *)
Definition rowregs (g3 g4 : word) (regs : bvmap 5 word) (i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 144) /\ getr regs 8 = Z_to_bv 64 (h - 1) /\ getr regs 9 = Z_to_bv 64 1 /\ getr regs 18 = Z_to_bv 64 bufs2 /\
  getr regs 19 = Z_to_bv 64 bufs1 /\ getr regs 21 = Z_to_bv 64 datad /\ getr regs 22 = Z_to_bv 64 wpld /\ getr regs 23 = Z_to_bv 64 wpls /\
  getr regs 24 = Z_to_bv 64 datas /\ getr regs 25 = Z_to_bv 64 (wpls * 4) /\ getr regs 26 = Z_to_bv 64 i /\ getr regs 27 = Z_to_bv 64 1 /\
  getr regs 3 = g3 /\ getr regs 4 = g4.
Definition exitregs (g3 g4 : word) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 144) /\ getr regs 18 = Z_to_bv 64 bufs2 /\ getr regs 19 = Z_to_bv 64 bufs1 /\ getr regs 21 = Z_to_bv 64 datad /\
  getr regs 22 = Z_to_bv 64 wpld /\ getr regs 23 = Z_to_bv 64 wpls /\ getr regs 25 = Z_to_bv 64 (wpls * 4) /\ getr regs 3 = g3 /\ getr regs 4 = g4.

(* [comment removed for export] *)
Definition kcs (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0) /\ rdn SEGS M (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc) /\
  rdn SEGS M (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc) /\ rdn SEGS M (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w).

(* [comment removed for export] *)
Lemma frame_keep : forall (M1 Mi : word -> option byte) (k : Z) v, rinv RW M1 Mi -> (8 <= k <= 144)%Z ->
  rdn SEGS M1 (Z_to_bv 64 (s - k)) 8 = Some v -> rdn SEGS Mi (Z_to_bv 64 (s - k)) 8 = Some v.
Proof.
  intros M1 Mi k v RI Hk R. geom. rewrite <- R. apply (rinv_rdn SEGS RW M1 Mi (s - k) 8 RI); [lia | cbn; lia |].
  intros r Hr. unfold RW in Hr. cbn [In] in Hr. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold RD, RB1, RB2; cbn [fst snd]; first [lia | dlia].
Qed.
Lemma kcs_keep : forall (M1 Mi : word -> option byte), rinv RW M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K0 & K1 & K2 & K3). unfold kcs.
  repeat split; [apply (frame_keep M1 Mi 112 _ RI ltac:(lia) K0) | apply (frame_keep M1 Mi 120 _ RI ltac:(lia) K1)
                | apply (frame_keep M1 Mi 128 _ RI ltac:(lia) K2) | apply (frame_keep M1 Mi 136 _ RI ltac:(lia) K3)].
Qed.

Lemma row_loop : forall (M1 : word -> option byte), regions_ok SEGS M1 [((s - 192)%Z, 48%Z); RD; RB1; RB2; RS] -> kcs M1 ->
  forall (g3 g4 : word) (n : nat) i regs Mi, (h - 1 - i <= Z.of_nat n)%Z -> (0 <= i < h - 1)%Z -> rinv RW M1 Mi -> rowregs g3 g4 regs i ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1ba20) Mi rom) (mkst regs' (Z_to_bv 64 0x1badc) Mi' rom)
    /\ rinv RW M1 Mi' /\ exitregs g3 g4 regs'.
Proof.
  intros M1 RO1 KC1. geom. intros g3 g4. induction n as [|n IH]; intros i regs Mi Hn Hi RI LR; [lia|].
  destruct LR as (H2 & H8 & H9 & H18 & H19 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H3 & H4).
  (* [comment removed for export] *)
  pose proof (row_bounds wpld i h ltac:(lia) ltac:(lia) ltac:(lia)) as P1.
  pose proof (row_bounds wpls (i + 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
  assert (HYPr : xr_hyps s datad w wpld datas wpls bufs1 bufs2 lc uc i (h - 1)).
  { unfold xr_hyps. replace ((i + 1) * wpls)%Z with (wpls * (i + 1))%Z by ring. replace (i * wpld)%Z with (wpld * i)%Z by ring.
    repeat split; first [assumption | lia]. }
  remember (datas + 4 * (wpls * (i + 1)))%Z as srow eqn:Esr. remember (datad + 4 * (wpld * i))%Z as drow eqn:Edr.
  assert (Rsr : (datas <= srow /\ srow + 4 * wpls <= datas + 4 * (wpls * h))%Z) by lia.
  assert (Rdr : (datad <= drow /\ drow + 4 * wpld <= datad + 4 * (wpld * h))%Z) by lia.
  assert (ALsr : (srow mod 4 = 0)%Z) by (subst srow; apply al4_add; exact ALs).
  assert (ALdr : (drow mod 4 = 0)%Z) by (subst drow; apply al4_add; exact ALd).
  assert (Esr' : (datas + 4 * ((i + 1) * wpls))%Z = srow) by (subst srow; ring).
  assert (Edr' : (datad + 4 * (i * wpld))%Z = drow) by (subst drow; ring).
  clear P1 P2 Esr Edr.
  destruct (RO1 RB1 ltac:(dl_in0)) as (B1a & B1b & B1c & SOK1). destruct (RO1 RB2 ltac:(dl_in0)) as (B2a & B2b & B2c & SOK2).
  destruct (RO1 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS). destruct (RO1 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD).
  destruct (RO1 ((s - 192)%Z, 48%Z) ltac:(dl_in0)) as (Fa & Fb & Fc & SOKF).
  unfold RB1, RB2, RS, RD in *. cbn [fst snd] in *.
  (* [comment removed for export] *)
  destruct (kcs_keep M1 Mi RI KC1) as (Ka0 & Ka1 & Ka2 & Ka3).
  destruct (xr_1b91c rom s datad w wpld datas wpls bufs1 bufs2 lc uc i (h - 1) HYPr fx regs Mi Ka0 Ka1 Ka2 Ka3 H2 H8 H9 H18 H19 H21 H22 H23 H24 H25 H26 H27)
    as (r1 & m1 & RUN1 & FR1 & E1_1 & E1_10 & E1_11 & E1_12 & AG1).
  assert (RI1 : rinv RW M1 m1) by (apply (rinv_cells RW [] M1 Mi m1 RI FR1); intros c []).
  destruct (memcpy_step M1 m1 r1 bufs1 bufs2 (wpls * 4) bufs1 bufs2 _ _ 113208 (proj1 RI1) SOK1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(dlia) ltac:(red; apply bv_eq; reflexivity) E1_1 E1_10 E1_11 E1_12)
    as (r2 & bs2 & RUN2 & L2 & K2).
  set (m2 := wbytes m1 (Z_to_bv 64 bufs1) bs2) in *.
  assert (RI2 : rinv RW M1 m2).
  { apply (rinv_wbytes RW M1 m1 bufs1 (wpls * 4) bs2 RI1 L2); [lia | lia |]. exists (bufs1, 4 * wpls)%Z. split; [unfold RW, RB1; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (kcs_keep M1 m2 RI2 KC1) as (Kb0 & Kb1 & Kb2 & Kb3).
  destruct (xr_1b934 rom s datad w wpld datas wpls bufs1 bufs2 lc uc i (h - 1) HYPr fx r2 m2 Kb0 Kb1 Kb2 Kb3
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r3 & m3 & RUN3 & FR3 & E3_1 & E3_10 & E3_11 & E3_12 & E3_20 & AG3).
  rewrite Esr' in E3_11.
  assert (RI3 : rinv RW M1 m3) by (apply (rinv_cells RW [] M1 m2 m3 RI2 FR3); intros c []).
  destruct (memcpy_step M1 m3 r3 bufs2 srow (wpls * 4) bufs2 datas _ _ 113284 (proj1 RI3) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(dlia) ltac:(red; apply bv_eq; reflexivity) E3_1 E3_10 E3_11 E3_12)
    as (r4 & bs4 & RUN4 & L4 & K4).
  set (m4 := wbytes m3 (Z_to_bv 64 bufs2) bs4) in *.
  assert (RI4 : rinv RW M1 m4).
  { apply (rinv_wbytes RW M1 m3 bufs2 (wpls * 4) bs4 RI3 L4); [lia | lia |]. exists (bufs2, 4 * wpls)%Z. split; [unfold RW, RB2; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (kcs_keep M1 m4 RI4 KC1) as (Kc0 & Kc1 & Kc2 & Kc3).
  destruct (xr_1b980 rom s datad w wpld datas wpls bufs1 bufs2 lc uc i (h - 1) HYPr fx r4 m4 Kc0 Kc1 Kc2 Kc3
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r5 & m5 & RUN5 & FR5 & E5_1 & E5_10 & E5_11 & E5_12 & E5_13 & E5_14 & E5_15 & E5_16 & AG5).
  rewrite Edr' in E5_10.
  assert (RI5 : rinv RW M1 m5) by (apply (rinv_cells RW [] M1 m4 m5 RI4 FR5); intros c []).
  assert (GLL : ll_geom (s - 144) drow bufs1 bufs2 (w - 1) lc uc wpls wpld).
  { unfold ll_geom. repeat split; first [assumption | lia | (apply al16_sub; [assumption | reflexivity])]. }
  assert (GDL : ll_disj (s - 144) drow bufs1 bufs2 wpls wpld).
  { unfold ll_disj, apart. repeat split; dlia. }
  assert (ROLL : regions_ok SEGS m5 (R3 drow bufs1 bufs2 wpls wpld)).
  { intros r Hr. unfold R3 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M1 m5 datad _ drow _ (proj1 RI5) SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. eapply store_ok_mono; [exact (proj1 RI5) | exact SOK1].
    - repeat split; try lia. eapply store_ok_mono; [exact (proj1 RI5) | exact SOK2]. }
  destruct (dbll0_run rom (s - 144) drow bufs1 bufs2 (w - 1) lc uc wpls wpld GLL GDL m5 ROLL r5 (Z_to_bv 64 113364) ltac:(red; apply bv_eq; reflexivity)
              ltac:(replace (s - 144 - 48)%Z with (s - 192)%Z by lia; eapply store_ok_mono; [exact (proj1 RI5) | exact SOKF])
              ltac:(dl_get2) E5_1 E5_10 ltac:(dl_get2) E5_12 E5_13 E5_14 E5_15 E5_16)
    as (r6 & m6 & RUN6 & RI6 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & KP6).
  assert (RI6' : rinv RW M1 m6).
  { apply (rinv_trans RW M1 m5 m6 RI5). apply (rinv_weaken (R4 (s - 144) drow bufs1 bufs2 wpls wpld) RW m5 m6 RI6).
    intros r Hr. unfold R4, R3 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd].
    - exists ((s - 192)%Z, 48%Z). split; [unfold RW; dl_in0 | cbn [fst snd]; lia].
    - exists (datad, 4 * (wpld * h))%Z. split; [unfold RW, RD; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs1, 4 * wpls)%Z. split; [unfold RW, RB1; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs2, 4 * wpls)%Z. split; [unfold RW, RB2; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (kcs_keep M1 m6 RI6' KC1) as (Kd0 & Kd1 & Kd2 & Kd3).
  destruct (xr_1b9d0 rom s datad w wpld datas wpls bufs1 bufs2 lc uc i (h - 1) HYPr fx r6 m6 Kd0 Kd1 Kd2 Kd3
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r7 & m7 & RUN7 & FR7 & E7_26 & AG7).
  assert (RI7 : rinv RW M1 m7) by (apply (rinv_cells RW [] M1 m6 m7 RI6' FR7); intros c []).
  destruct (kcs_keep M1 m7 RI7 KC1) as (Ke0 & Ke1 & Ke2 & Ke3).
  assert (CHAIN : msteps SEGS (mkst regs (Z_to_bv 64 0x1ba20) Mi rom) (mkst r7 (Z_to_bv 64 0x1bad8) m7 rom)).
  { exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4
           (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6 RUN7)))))). }
  destruct (Z_lt_ge_dec (i + 1) (h - 1)) as [LT|GE].
  - (* [comment removed for export] *)
    destruct (xr_1b9d4t rom s datad w wpld datas wpls bufs1 bufs2 lc uc i (h - 1) HYPr fx r7 m7 ltac:(ex_br) Ke0 Ke1 Ke2 Ke3
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
      as (r8 & m8 & RUN8 & FR8 & AG8).
    assert (RI8 : rinv RW M1 m8) by (apply (rinv_cells RW [] M1 m7 m8 RI7 FR8); intros c []).
    destruct (IH (i + 1)%Z r8 m8 ltac:(lia) ltac:(lia) RI8) as (r9 & m9 & RUN9 & RI9 & EX9).
    { unfold rowregs. repeat split; dl_get2. }
    exists r9, m9. split; [exact (msteps_trans _ _ _ _ CHAIN (msteps_trans _ _ _ _ RUN8 RUN9))|]. split; [exact RI9 | exact EX9].
  - (* [comment removed for export] *)
    destruct (xr_1b9d4f rom s datad w wpld datas wpls bufs1 bufs2 lc uc i (h - 1) HYPr fx r7 m7 ltac:(ex_br) Ke0 Ke1 Ke2 Ke3
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
      as (r8 & m8 & RUN8 & FR8 & AG8).
    assert (RI8 : rinv RW M1 m8) by (apply (rinv_cells RW [] M1 m7 m8 RI7 FR8); intros c []).
    exists r8, m8. split; [exact (msteps_trans _ _ _ _ CHAIN RUN8)|]. split; [exact RI8|].
    unfold exitregs. repeat split; dl_get2.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lrow : Z := (datad + 4 * ((h - 1) * wpld))%Z.
Definition RALL : list (Z * Z) := [((s - 192)%Z, 192%Z); RD; RB1; RB2].

Lemma lrow_facts : (datad <= lrow /\ lrow + 4 * wpld <= datad + 4 * (wpld * h) /\ lrow mod 4 = 0)%Z.
Proof.
  geom. unfold lrow. pose proof (row_bounds wpld (h - 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as P.
  replace ((h - 1) * wpld)%Z with (wpld * (h - 1))%Z by ring. split; [lia|]. split; [lia|]. apply al4_add. exact ALd.
Qed.

(* [comment removed for export] *)
Lemma pre_keep : forall (m1 m3 : word -> option byte) (bs : list byte) (k : Z) v,
  Z.of_nat (length bs) = (wpls * 4)%Z -> mframe [((s - 112)%Z, 8%Z); ((s - 144)%Z, 8%Z)] (wbytes m1 (Z_to_bv 64 bufs2) bs) m3 ->
  (8 <= k <= 104 \/ 120 <= k <= 136)%Z ->
  rdn SEGS m1 (Z_to_bv 64 (s - k)) 8 = Some v -> rdn SEGS m3 (Z_to_bv 64 (s - k)) 8 = Some v.
Proof.
  intros m1 m3 bs k v L FR Hk R. geom. rewrite <- R.
  set (RX := [((s - 112)%Z, 8%Z); ((s - 144)%Z, 8%Z); RB2]).
  assert (RI2 : rinv RX m1 (wbytes m1 (Z_to_bv 64 bufs2) bs)).
  { apply (rinv_wbytes RX m1 m1 bufs2 (wpls * 4) bs (rinv_refl _ _) L); [lia | lia |]. exists RB2. split; [unfold RX; dl_in0 | unfold RB2; cbn [fst snd]; lia]. }
  assert (RI3 : rinv RX m1 m3).
  { apply (rinv_cells RX _ m1 _ m3 RI2 FR). intros c Hc. cbn [In] in Hc.
    destruct Hc as [<- | [<- | []]]; cbn [fst snd]; (split; [lia|]).
    - exists ((s - 112)%Z, 8%Z). split; [unfold RX; dl_in0 | cbn [fst snd]; lia].
    - exists ((s - 144)%Z, 8%Z). split; [unfold RX; dl_in0 | cbn [fst snd]; lia]. }
  apply (rinv_rdn SEGS RX m1 m3 (s - k) 8 RI3); [lia | cbn; lia |].
  intros r Hr. unfold RX in Hr. cbn [In] in Hr. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  destruct Hr as [<- | [<- | [<- | []]]]; unfold RB2; cbn [fst snd]; first [lia | dlia].
Qed.

Lemma dbl_run : forall (M0 : word -> option byte) regs (ret : word), ret_ok ret ->
  regions_ok SEGS M0 [((s - 192)%Z, 192%Z); RD; RB1; RB2; RS] ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 w -> getr regs 12 = Z_to_bv 64 h ->
  getr regs 13 = Z_to_bv 64 wpld -> getr regs 14 = Z_to_bv 64 datas -> getr regs 15 = Z_to_bv 64 wpls -> getr regs 16 = Z_to_bv 64 bufs1 ->
  getr regs 17 = Z_to_bv 64 bufs2 -> getr regs 28 = Z_to_bv 64 lc -> getr regs 29 = Z_to_bv 64 uc ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1b95c) M0 rom) (mkst regs' ret M' rom)
    /\ rinv RALL M0 M' /\ getr regs' 2 = Z_to_bv 64 s
    /\ (forall r, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros M0 regs ret Hret RO0 H2 H1 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29. geom.
  destruct (RO0 ((s - 192)%Z, 192%Z) ltac:(dl_in0)) as (Fa & Fb & Fc & SOKF0). destruct (RO0 RB1 ltac:(dl_in0)) as (B1a & B1b & B1c & SOK1).
  destruct (RO0 RB2 ltac:(dl_in0)) as (B2a & B2b & B2c & SOK2). destruct (RO0 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS).
  destruct (RO0 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD).
  unfold RB1, RB2, RS, RD in *. cbn [fst snd] in *.
  assert (sokF : forall (Mi : word -> option byte) k, mem_grows M0 Mi -> (8 <= k <= 192)%Z -> store_ok SEGS Mi (Z_to_bv 64 (s - k)) 8 = true).
  { intros Mi k GR Hk. apply (reg_sok SEGS M0 Mi (s - 192) _ (s - k) 8 GR SOKF0); rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (HYPp : xp_hyps s datad w h wpld datas wpls bufs1 bufs2 lc uc) by (unfold xp_hyps; repeat split; first [assumption | lia]).
  pose proof (mem_grows_refl M0) as G00.
  (* [comment removed for export] *)
  destruct (xp_1b858 rom s datad w h wpld datas wpls bufs1 bufs2 lc uc HYPp fx regs M0
              (sokF M0 8%Z G00 ltac:(lia)) (sokF M0 16%Z G00 ltac:(lia)) (sokF M0 24%Z G00 ltac:(lia)) (sokF M0 32%Z G00 ltac:(lia))
              (sokF M0 40%Z G00 ltac:(lia)) (sokF M0 48%Z G00 ltac:(lia)) (sokF M0 56%Z G00 ltac:(lia)) (sokF M0 64%Z G00 ltac:(lia))
              (sokF M0 72%Z G00 ltac:(lia)) (sokF M0 80%Z G00 ltac:(lia)) (sokF M0 88%Z G00 ltac:(lia)) (sokF M0 96%Z G00 ltac:(lia))
              (sokF M0 104%Z G00 ltac:(lia)) (sokF M0 120%Z G00 ltac:(lia)) (sokF M0 128%Z G00 ltac:(lia)) (sokF M0 136%Z G00 ltac:(lia))
              H2 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29)
    as (r1 & m1 & RUN1 & FR1 & E1_1 & E1_2 & E1_10 & E1_11 & E1_12 & E1_18 & E1_19 & E1_21 & E1_22 & E1_23 & E1_24 & E1_25 & E1_26
        & SVra & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & SV22 & SV23 & SV24 & SV25 & SV26 & SV27 & SVuc & SVlc & SVw & AG1).
  assert (RI1 : rinv RALL M0 m1).
  { apply (rinv_cells RALL _ M0 M0 m1 (rinv_refl _ _) FR1). intros c Hc. cbn [In] in Hc.
    repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|]; exists ((s - 192)%Z, 192%Z); split; [unfold RALL; dl_in0 | cbn [fst snd]; lia] |]). destruct Hc. }
  (* [comment removed for export] *)
  pose proof (row_bounds wpls 0 h ltac:(lia) ltac:(lia) ltac:(lia)) as PB0.
  destruct (memcpy_step M0 m1 r1 bufs2 datas (wpls * 4) bufs2 datas _ _ 113132 (proj1 FR1) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(dlia)
              ltac:(red; apply bv_eq; reflexivity) E1_1 E1_10 E1_11 E1_12)
    as (r2 & bs2 & RUN2 & L2 & K2).
  set (m2 := wbytes m1 (Z_to_bv 64 bufs2) bs2) in *.
  assert (RI2 : rinv RALL M0 m2).
  { apply (rinv_wbytes RALL M0 m1 bufs2 (wpls * 4) bs2 RI1 L2); [lia | lia |]. exists (bufs2, 4 * wpls)%Z. split; [unfold RALL, RB2; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  assert (MID : exists r5 m3 m5, msteps SEGS (mkst r2 (Z_to_bv 64 0x1b9ec) m2 rom) (mkst r5 (Z_to_bv 64 0x1badc) m5 rom)
                  /\ mframe [((s - 112)%Z, 8%Z); ((s - 144)%Z, 8%Z)] m2 m3 /\ rinv RW m3 m5 /\ exitregs (getr regs 3) (getr regs 4) r5
                  /\ rdn SEGS m3 (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0)
                  /\ rdn SEGS m3 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 (h - 1))).
  { destruct (Z.eq_dec h 1) as [Hh1|Hh2].
    - assert (HYPa : xa_hyps s datad wpld datas wpls bufs1 bufs2) by (unfold xa_hyps; repeat split; first [assumption | lia]).
      destruct (xa_1b8e8 rom s datad wpld datas wpls bufs1 bufs2 HYPa fx r2 m2 (sokF m2 112%Z (proj1 RI2) ltac:(lia)) (sokF m2 144%Z (proj1 RI2) ltac:(lia))
                  ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
        as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_11 & SVz & SVh & AG3).
      exists r3, m3, m3. split; [exact RUN3|]. split; [exact FR3|]. split; [apply rinv_refl|]. split; [unfold exitregs; repeat split; dl_get2|].
      split; [rewrite <- w2b_Z by lia; exact SVz | replace (h - 1)%Z with 0%Z by lia; rewrite <- w2b_Z by lia; exact SVh].
    - assert (HYPb : xb_hyps s datad wpld datas wpls bufs1 bufs2 h) by (unfold xb_hyps; repeat split; first [assumption | lia]).
      destruct (xb_1b8e8 rom s datad wpld datas wpls bufs1 bufs2 h HYPb fx r2 m2 (sokF m2 112%Z (proj1 RI2) ltac:(lia)) (sokF m2 144%Z (proj1 RI2) ltac:(lia))
                  ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
        as (r3 & m3 & RUN3 & FR3 & E3_8 & E3_9 & E3_11 & E3_26 & E3_27 & SVz & SVh & AG3).
      assert (KZ : rdn SEGS m3 (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 0)) by (rewrite <- w2b_Z by lia; exact SVz).
      assert (KH : rdn SEGS m3 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 (h - 1))) by (rewrite <- w2b_Z by lia; exact SVh).
      assert (G03 : mem_grows M0 m3) by exact (mem_grows_trans _ _ _ (proj1 RI2) (proj1 FR3)).
      assert (RO3 : regions_ok SEGS m3 [((s - 192)%Z, 48%Z); RD; RB1; RB2; RS]).
      { intros r Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
        - cbn [fst snd]. repeat split; try lia. apply (reg_sok SEGS M0 m3 (s - 192) _ (s - 192) _ G03 SOKF0); rewrite ?Z2Nat.id by lia; cbn; lia.
        - apply (regions_ok_grows SEGS M0 m3 _ RO0 G03). right. exact Hr. }
      assert (KC3 : kcs m3).
      { unfold kcs. split; [exact KZ|]. rewrite <- !w2b_Z by lia.
        split; [exact (pre_keep m1 m3 bs2 120 _ L2 FR3 ltac:(lia) SVuc)|]. split; [exact (pre_keep m1 m3 bs2 128 _ L2 FR3 ltac:(lia) SVlc)|].
        exact (pre_keep m1 m3 bs2 136 _ L2 FR3 ltac:(lia) SVw). }
      destruct (row_loop m3 RO3 KC3 (getr regs 3) (getr regs 4) (Z.to_nat h) 0%Z r3 m3 ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r5 & m5 & RUN5 & RI5 & EX5).
      { unfold rowregs. repeat split; dl_get2. }
      exists r5, m3, m5. split; [exact (msteps_trans _ _ _ _ RUN3 RUN5)|]. split; [exact FR3|]. split; [exact RI5|]. split; [exact EX5|]. split; [exact KZ | exact KH]. }
  destruct MID as (r5 & m3 & m5 & RUN5 & FR3 & RI5 & EX5 & KZ & KH).
  destruct EX5 as (X2 & X18 & X19 & X21 & X22 & X23 & X25 & X3 & X4).
  assert (KU : rdn SEGS m3 (Z_to_bv 64 (s - 120)) 8 = Some (Z_to_le_bytes 8 uc)) by (rewrite <- w2b_Z by lia; exact (pre_keep m1 m3 bs2 120 _ L2 FR3 ltac:(lia) SVuc)).
  assert (KL : rdn SEGS m3 (Z_to_bv 64 (s - 128)) 8 = Some (Z_to_le_bytes 8 lc)) by (rewrite <- w2b_Z by lia; exact (pre_keep m1 m3 bs2 128 _ L2 FR3 ltac:(lia) SVlc)).
  assert (KW : rdn SEGS m3 (Z_to_bv 64 (s - 136)) 8 = Some (Z_to_le_bytes 8 w)) by (rewrite <- w2b_Z by lia; exact (pre_keep m1 m3 bs2 136 _ L2 FR3 ltac:(lia) SVw)).
  assert (G03 : mem_grows M0 m3) by exact (mem_grows_trans _ _ _ (proj1 RI2) (proj1 FR3)).
  pose proof (row_bounds wpld (h - 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as PR.
  assert (HYPl : xl_hyps s datad w wpld wpls bufs1 bufs2 lc uc (h - 1)).
  { unfold xl_hyps. replace ((h - 1) * wpld)%Z with (wpld * (h - 1))%Z by ring. repeat split; first [assumption | lia]. }
  (* [comment removed for export] *)
  destruct (xl_1b9d8 rom s datad w wpld wpls bufs1 bufs2 lc uc (h - 1) HYPl fx r5 m5
              (frame_keep m3 m5 112 _ RI5 ltac:(lia) KZ) (frame_keep m3 m5 120 _ RI5 ltac:(lia) KU) (frame_keep m3 m5 128 _ RI5 ltac:(lia) KL)
              (frame_keep m3 m5 136 _ RI5 ltac:(lia) KW) (frame_keep m3 m5 144 _ RI5 ltac:(lia) KH) X2 X18 X19 X21 X22 X23 X25)
    as (r6 & m6 & RUN6 & FR6 & E6_1 & E6_10 & E6_11 & E6_12 & AG6).
  assert (RI6 : rinv RW m3 m6) by (apply (rinv_cells RW [] m3 m5 m6 RI5 FR6); intros c []).
  destruct (memcpy_step M0 m6 r6 bufs1 bufs2 (wpls * 4) bufs1 bufs2 _ _ 113396 (mem_grows_trans _ _ _ G03 (proj1 RI6))
              SOK1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(dlia)
              ltac:(red; apply bv_eq; reflexivity) E6_1 E6_10 E6_11 E6_12)
    as (r7 & bs7 & RUN7 & L7 & K7).
  set (m7 := wbytes m6 (Z_to_bv 64 bufs1) bs7) in *.
  assert (RI7 : rinv RW m3 m7).
  { apply (rinv_wbytes RW m3 m6 bufs1 (wpls * 4) bs7 RI6 L7); [lia | lia |]. exists (bufs1, 4 * wpls)%Z. split; [unfold RW, RB1; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (xl_1b9f0 rom s datad w wpld wpls bufs1 bufs2 lc uc (h - 1) HYPl fx r7 m7 _ _ _ _ _ _ _ _ _ _ _ _ _
              (frame_keep m3 m7 8 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 8 _ L2 FR3 ltac:(lia) SVra))
              (frame_keep m3 m7 16 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 16 _ L2 FR3 ltac:(lia) SV8))
              (frame_keep m3 m7 24 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 24 _ L2 FR3 ltac:(lia) SV9))
              (frame_keep m3 m7 32 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 32 _ L2 FR3 ltac:(lia) SV18))
              (frame_keep m3 m7 40 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 40 _ L2 FR3 ltac:(lia) SV19))
              (frame_keep m3 m7 48 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 48 _ L2 FR3 ltac:(lia) SV20))
              (frame_keep m3 m7 56 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 56 _ L2 FR3 ltac:(lia) SV21))
              (frame_keep m3 m7 64 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 64 _ L2 FR3 ltac:(lia) SV22))
              (frame_keep m3 m7 72 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 72 _ L2 FR3 ltac:(lia) SV23))
              (frame_keep m3 m7 80 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 80 _ L2 FR3 ltac:(lia) SV24))
              (frame_keep m3 m7 88 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 88 _ L2 FR3 ltac:(lia) SV25))
              (frame_keep m3 m7 96 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 96 _ L2 FR3 ltac:(lia) SV26))
              (frame_keep m3 m7 104 _ RI7 ltac:(lia) (pre_keep m1 m3 bs2 104 _ L2 FR3 ltac:(lia) SV27))
              (frame_keep m3 m7 112 _ RI7 ltac:(lia) KZ) (frame_keep m3 m7 120 _ RI7 ltac:(lia) KU) (frame_keep m3 m7 128 _ RI7 ltac:(lia) KL)
              (frame_keep m3 m7 136 _ RI7 ltac:(lia) KW) (frame_keep m3 m7 144 _ RI7 ltac:(lia) KH)
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r8 & m8 & RUN8 & FR8 & Z1 & Z2 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & AG8).
  rewrite rdv_word8 in Z1, Z8, Z9, Z18, Z19, Z20, Z21, Z22, Z23, Z24, Z25, Z26, Z27.
  assert (RI8 : rinv RW m3 m8) by (apply (rinv_cells RW [] m3 m7 m8 RI7 FR8); intros c []).
  assert (Z3 : getr r8 3 = getr regs 3) by dl_get2.
  assert (Z4 : getr r8 4 = getr regs 4) by dl_get2.
  assert (G08 : mem_grows M0 m8) by exact (mem_grows_trans _ _ _ G03 (proj1 RI8)).
  (* [comment removed for export] *)
  destruct lrow_facts as (LR1 & LR2 & LR3).
  assert (GLL : ll_geom s lrow bufs1 bufs2 (w - 1) lc uc wpls wpld).
  { unfold ll_geom. repeat split; first [assumption | lia]. }
  assert (GDL : ll_disj s lrow bufs1 bufs2 wpls wpld).
  { unfold ll_disj, apart. repeat split; dlia. }
  assert (ROLL : regions_ok SEGS m8 (R2 lrow bufs1 wpls wpld)).
  { intros r Hr. unfold R2 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M0 m8 datad _ lrow _ G08 SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. eapply store_ok_mono; [exact G08 | exact SOK1]. }
  destruct (dbll1_run rom s lrow bufs1 bufs2 (w - 1) lc uc wpls wpld GLL GDL m8 ROLL r8 ret Hret
              ltac:(apply (reg_sok SEGS M0 m8 (s - 192) _ (s - 48) 48 G08 SOKF0); rewrite ?Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
              Z2 ltac:(rewrite Z1; exact H1) ltac:(unfold lrow; dl_get2) ltac:(dl_get2) Z12 Z13 Z14 Z15 Z16)
    as (r9 & m9 & RUN9 & RI9 & Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & KP9).
  exists r9, m9. split.
  { exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6
           (msteps_trans _ _ _ _ RUN7 (msteps_trans _ _ _ _ RUN8 RUN9)))))). }
  split.
  { apply (rinv_trans RALL M0 m2 m9 RI2). apply (rinv_trans RALL m2 m3 m9).
    { apply (rinv_cells RALL _ m2 m2 m3 (rinv_refl _ _) FR3). intros c Hc. cbn [In] in Hc.
      repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|]; exists ((s - 192)%Z, 192%Z); split; [unfold RALL; dl_in0 | cbn [fst snd]; lia] |]). destruct Hc. }
    apply (rinv_trans RALL m3 m8 m9).
    - apply (rinv_weaken RW RALL m3 m8 RI8). intros r Hr. unfold RW in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]].
      + exists ((s - 192)%Z, 192%Z). split; [unfold RALL; dl_in0 | cbn [fst snd]; lia].
      + exists RD. split; [unfold RALL; dl_in0 | lia].
      + exists RB1. split; [unfold RALL; dl_in0 | lia].
      + exists RB2. split; [unfold RALL; dl_in0 | lia].
    - apply (rinv_weaken (R4' s lrow bufs1 wpls wpld) RALL m8 m9 RI9). intros r Hr. unfold R4', R2 in Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd].
      + exists ((s - 192)%Z, 192%Z). split; [unfold RALL; dl_in0 | cbn [fst snd]; lia].
      + exists (datad, 4 * (wpld * h))%Z. split; [unfold RALL, RD; dl_in0 | cbn [fst snd]; lia].
      + exists (bufs1, 4 * wpls)%Z. split; [unfold RALL, RB1; dl_in0 | cbn [fst snd]; lia]. }
  split; [exact Y2|].
  intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [first [ (rewrite Y8; exact Z8) | (rewrite Y9; exact Z9) | (rewrite Y18; exact Z18) | (rewrite Y19; exact Z19)
                                           | (rewrite Y20; exact Z20) | (rewrite Y21; exact Z21)
                                           | (match goal with |- getr r9 ?q = _ => rewrite (KP9 q ltac:(in_kept)); assumption end) ] |]). destruct Hr.
Qed.

End Low.
