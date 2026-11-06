(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the one piece of the Bz -> W_sites bridge that every runtime lane needs,
   `aentry_post_of_walk`: a Bz interceptor/intrinsic walk that ends at the return address with a0 = r, whose only
   memory change is the stack window [sp - D, sp) and a list WR of written ranges, read back as W_sites.v's
   `aentry_post`.  Written here (R3Mem) by agreement with R1Str so that RT_kit.v imports it rather than restating it;
   it is FSstrlen.v's post_of_walk (a working branch 3210d71ee38, a Theorem Labs lane, itself a Theorem Labs lane's) with
   three changes: the pre is `ecall_pre` (no POISON-U), the post is W_sites' aentry_post at PI := PB_fr, and the
   written set WR / the result predicate Pr are parameters, so one lemma serves the read-only interceptors
   (WR := []) and the intrinsics (WR := [(d, d + n)]).
   The image facts (FR_IMG_TOP, cj_keep_high, mrd_high) are FSstrlen.v:97-147, 444-449 at fuzz_reply's image end;
   0x600000 is a valid ceiling for fuzz_reply.asan-ubsan too (its last segment ends in the page below 0x5fc000). *)
(* Modified by Theorem Labs, 2026-10-30: from lib/A/RT_post.v, as the new module RT_kit_cells_x: only its ro_c1_one_of_val_mem, restated at the value 0 as ro_c1_zero_of_val_mem; new lemmas discharge RT_kit.v's named premises FrRtCells / FrRtCells_x from the laws and TfibSyms (fr_rest_rows, fr_rest_not_row, cell_val_c, fr_rest_of_cells, FrRtCells_x_of_syms, FrRtCells_of_syms) and give RT_kit.v walk_cells_x's conclusion as FrWalkCells_x (walk_cells_x_of_syms, walk_cells_x_of_cells). *)
(* Modified by Theorem Labs, 2026-10-30: copied from lib/A/RT_kit_cells_x.v to image B (fuzz_reply.asan-ubsan): module paths lib.A -> lib.B with the image modules AB1v / AF0m / AF0x / AE2y -> YB1v / YF0m / YF0x / YE2y and one more Require (Bz.A.I_strncmpw), and the cell addresses and values of fr_rest_rows, fr_rest_not_row and fr_rest_of_cells moved to image B's (generated YF0m.v); lemma names, statements and proofs otherwise unchanged. *)
(* Image B's (fuzz_reply.asan-ubsan) twin of lib/A/RT_kit_cells_x.v
   (a working branch 6b4f6082575), with A's lemma names, statements and proofs and B's numbers:
   RT_kit.v's named premises FrRtCells (over cgif's AR) and FrRtCells_x (over a generic ARx), fr_rt_rest's 14
   conjuncts (RT_kit.v:173-187) at every state AR / ARx accepts, discharged from the laws and TfibSyms B.  RT_kit.v
   is not edited.
   (a) Measurement, by vm_compute in fr_rest_rows / fr_rest_not_row below: under TfibSyms B, as_const B ly is the
   generated YF0m's Tfib_const ly (ts_const); YF0m.v has sha256 4c8cb16b0e68 (internal record; commit
   4fedc522440, which adds the row z8 (ANum 0x9fc90) 0x9740c, REAL(strrchr), YF0m.v:446).  Thirteen of fr_rt_rest's
   conjuncts are direct rows of it (address, width and value all equal; YE2y.const_chk): 0x9df40, 0x9df58 (three
   words), 0x9fc68 (REAL(strlen), YF0m.v:443), 0x9fca8, 0x9fd98, 0xa7318, 0xa7320 (three words), 0x13825d, 0x138262,
   0x138263, 0x9eab8, 0xa7319 and 0x9fc90 (REAL(strrchr) = 0x9740c).  0x138265 (intercept_strchr, 1 byte) is not a
   row, but it is byte 5 of the row 0x138260 = 0x0101010101010101 (YF0m.v:72).
   (b) fr_rest_of_cells: the 14 conjuncts from the const-cells fact `Forall (cell_holds B ly (aview frsegs H mem))
   (as_const B ly)` (RTx.rtl_const_cells) and TfibSyms B.  cell_holds reads aview over the restricted memory and gives
   val_mem on mrestrict (YF0x.cell_holds_val_mem), the same view fr_rt_rest's ro_cells read.  The one extra step is
   byte extraction for 0x138265 (val_mem of the 8-byte row -> its byte 5).
   (c) FrRtCells_x_of_syms : rt_laws + TfibSyms -> FrRtCells_x, at every ARx; FrRtCells_of_syms : AR_laws + TfibSyms
   -> FrRtCells, at cgif's AR (through RTx.rt_laws_AR): a consumer of an original that carries the named premise
   FrRtCells discharges it with this lemma.
   (d) The strlen / strcmp / strncmp walks read only conjuncts 1-10 (RT_kit.v:215 fr_walk_cells_of): FrWalkCells_x
   (RT_kit.v:265 walk_cells_x's conclusion as a predicate over ARx) holds from rt_laws + FrShadowSyms + TfibSyms
   (walk_cells_x_of_syms), and from FrRtCells_x (walk_cells_x_of_cells, the originals' route). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.D_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strcmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strncmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strlen.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memchrw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v W_syms W_listing W_kit W_tbl W_place W_img W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FRbz_str RT_post.
(* the ARx-generic twins (fuzz_reply.runtime_twins) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import RTx.
(* RTx Requires FCiface -> YF0v, which sets Zify's euclidean-division flag to false globally; restore the value the
   header above ended with (true, W_sites' chain), which this file's importers' lia expect. *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m YF0x YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_kit.
(* RTx / FCiface leave Zify's euclidean flag false (YF0v); this file's lia need it on *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- (a) the measurement ---- *)
Lemma fr_rest_rows : forall ly,
  YE2y.const_chk ly 0x9df40 8 0x138168 = true /\
  YE2y.const_chk ly 0x9df58 8 0xa7328 = true /\ YE2y.const_chk ly 0x9df60 8 0xa7330 = true /\
  YE2y.const_chk ly 0x9df68 8 0xa7320 = true /\
  YE2y.const_chk ly 0x9fc68 8 0x970cc = true /\
  YE2y.const_chk ly 0x9fca8 8 0x96950 = true /\
  YE2y.const_chk ly 0x9fd98 8 0x973c8 = true /\
  YE2y.const_chk ly 0xa7318 1 1 = true /\
  YE2y.const_chk ly 0xa7320 8 0x7fffffffffff = true /\ YE2y.const_chk ly 0xa7328 8 0 = true /\
  YE2y.const_chk ly 0xa7330 8 0 = true /\
  YE2y.const_chk ly 0x13825d 1 0 = true /\
  YE2y.const_chk ly 0x138262 1 1 = true /\
  YE2y.const_chk ly 0x138263 1 1 = true /\
  YE2y.const_chk ly 0x9eab8 8 0xa7319 = true /\
  YE2y.const_chk ly 0xa7319 1 1 = true /\
  YE2y.const_chk ly 0x138260 8 0x101010101010101 = true /\
  YE2y.const_chk ly 0x9fc90 8 0x9740c = true.
Proof. intros ly. vm_compute. repeat split. Qed.

(* the one cell that is not a row: 0x138265 sits inside the row 0x138260 *)
Lemma fr_rest_not_row : forall ly, YE2y.const_chk ly 0x138265 1 1 = false.
Proof. intros ly. vm_compute. reflexivity. Qed.

(* ---- (b) the 14 conjuncts from the const-cells fact ---- *)
(* YF0x.v:207 tfib_const_lookup over the cell list (ARm's am_const replaced by the list itself) *)
Lemma cell_val_c : forall B, TfibSyms B -> forall ly (H : word -> bool) mem a (w : N) v,
  Forall (cell_holds B ly (aview frsegs H mem)) (as_const B ly) -> YE2y.const_chk ly a w v = true ->
  val_mem frsegs (mrestrict H mem) a (N.to_nat w) v.
Proof.
  intros B TB ly H mem a w v C Hc.
  apply (cell_holds_val_mem B ly H mem (ANum a) (N.to_nat w) (ANum v)).
  apply (proj1 (Forall_forall (cell_holds B ly (aview frsegs H mem)) (as_const B ly)) C).
  rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ (YE2y.const_chk_sound ly a w v Hc)).
Qed.

(* RT_post.v:586 ro_c1_one_of_val_mem at the value 0 *)
Lemma ro_c1_zero_of_val_mem : forall m A, 0 <= A -> A + 1 <= 2 ^ 64 ->
  val_mem frsegs m A 1 0 -> BSt.ro_cells BI.asegs m A [BC.C1 (Z_to_bv 8 0)].
Proof.
  intros m A HA HA1 HV. split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
  split; [exact HA|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
  change (BM.mrd BI.asegs m (BM.wa (A + Z.of_nat 0))) with (mbyte frsegs m (A + Z.of_nat 0)).
  rewrite (HV 0%nat ltac:(cbn; lia)). reflexivity.
Qed.

Lemma fr_rest_of_cells : forall B, TfibSyms B -> forall ly (H : word -> bool) mem,
  Forall (cell_holds B ly (aview frsegs H mem)) (as_const B ly) -> fr_rt_rest (mrestrict H mem).
Proof.
  intros B TB ly H mem C.
  pose proof (fr_rest_rows ly)
    as (R1 & R2a & R2b & R2c & R3 & R4 & R5 & R6 & R7a & R7b & R7c & R8 & R9 & R10 & R11 & R12 & R13 & R14).
  set (mR := mrestrict H mem).
  assert (V : forall a w v, YE2y.const_chk ly a w v = true -> val_mem frsegs mR a (N.to_nat w) v)
    by (intros a w v Hc; exact (cell_val_c B TB ly H mem a w v C Hc)).
  assert (V5 : val_mem frsegs mR 0x138265 1 1).
  { pose proof (V _ _ _ R13) as W8. intros j Hj. assert (Hj0 : j = 0%nat) by lia. subst j.
    exact (W8 5%nat ltac:(cbn; lia)). }
  unfold fr_rt_rest.
  split; [apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R1)]|].
  split.
  { apply RP.ro_cons8; [apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R2a)]|].
    apply RP.ro_cons8; [apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R2b)]|].
    apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R2c)]. }
  split; [apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R3)]|].
  split; [apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R4)]|].
  split; [apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R5)]|].
  split; [apply RP.ro_c1_one_of_val_mem; [lia | lia | exact (V _ _ _ R6)]|].
  split.
  { apply RP.ro_cons8; [apply RP.ro_c8_of_val_mem; [lia | lia | unfold BR.kHighMemEnd; lia | exact (V _ _ _ R7a)]|].
    apply RP.ro_cons8; [apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R7b)]|].
    apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R7c)]. }
  split; [apply ro_c1_zero_of_val_mem; [lia | lia | exact (V _ _ _ R8)]|].
  split; [apply RP.ro_c1_one_of_val_mem; [lia | lia | exact (V _ _ _ R9)]|].
  split; [apply RP.ro_c1_one_of_val_mem; [lia | lia | exact (V _ _ _ R10)]|].
  split; [apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R11)]|].
  split; [apply RP.ro_c1_one_of_val_mem; [lia | lia | exact (V _ _ _ R12)]|].
  split; [apply RP.ro_c1_one_of_val_mem; [lia | lia | exact V5]|].
  apply RP.ro_c8_of_val_mem; [lia | lia | lia | exact (V _ _ _ R14)].
Qed.

(* ---- (c) the named premises FrRtCells_x / FrRtCells from the laws and TfibSyms ---- *)
Lemma FrRtCells_x_of_syms : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  rt_laws frsegs B ARx -> TfibSyms B -> FrRtCells_x B ARx.
Proof.
  intros B ARx LAWS TB ly S Hp W mem md HAR.
  exact (fr_rest_of_cells B TB ly (w_H W) mem (rtl_const_cells _ _ _ LAWS ly S Hp W mem md HAR)).
Qed.

(* cgif's AR (ARx := FCiface.AR_nohp, Hp := []), whose laws RTx.rt_laws_AR gives *)
Lemma FrRtCells_of_syms : forall B, AR_laws frsegs B -> TfibSyms B -> FrRtCells B.
Proof.
  intros B LAWS TB ly S W mem md HAR.
  exact (FrRtCells_x_of_syms B (FCiface.AR_nohp frsegs B) (rt_laws_AR frsegs B LAWS) TB ly S [] W mem md HAR).
Qed.

(* ---- (d) the string walks' cells. RT_kit.v:215 fr_walk_cells_of destructs fr_rt_rest as (R1 .. R10 & _ & _ & _ &
   _): the walks of strlen, strcmp and strncmp read conjuncts 1-10 only. ---- *)
(* what the strlen / strcmp / strncmp twins read, over ARx: RT_kit.v:265 walk_cells_x's conclusion, as one
   predicate, so that each twin is proved once and instanced from either source below *)
Definition FrWalkCells_x
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall ly S Hp (W : world frsegs) mem md, ARx ly S Hp W mem md ->
  fr_walk_cells (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)).

(* from the laws and TfibSyms only (the twins and their _cf corollaries) *)
Lemma walk_cells_x_of_syms : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  rt_laws frsegs B ARx -> FrShadowSyms B -> TfibSyms B -> FrWalkCells_x ARx.
Proof. intros B ARx LAWS TL TB. exact (walk_cells_x B ARx LAWS TL (FrRtCells_x_of_syms B ARx LAWS TB)). Qed.

(* from RT_kit's wide named premise FrRtCells_x (the originals' route: the _of_x corollaries) *)
Lemma walk_cells_x_of_cells : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  rt_laws frsegs B ARx -> FrShadowSyms B -> FrRtCells_x B ARx -> FrWalkCells_x ARx.
Proof. intros B ARx LAWS TL CELLS. exact (walk_cells_x B ARx LAWS TL CELLS). Qed.

End core.
