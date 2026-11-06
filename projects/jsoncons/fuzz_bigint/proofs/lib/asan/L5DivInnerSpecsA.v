(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA LibIface
     AsanAcct L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5CoreB L5DivLeafSpecsA L5DivSpecsA L5OpmodSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5DIA.
Import L5A. Import L5CA. Import L5CSA. Import L5CB. Import L5DSA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHR : Z := 0x9423c.
Definition MAX_SIZE : Z := 2 ^ 61 - 1.          (* [comment removed for export] *)
Definition DIVN_SCR : Z := 352 + L5DLA.NORM_SCR.        (* [comment removed for export] *)
Definition DIVEQ_SCR : Z := 96 + DIVN_SCR.
Definition UNNORM_SCR : Z := 64 + DIVEQ_SCR.
Definition DIVO_SCR : Z := 352 + UNNORM_SCR.            (* [comment removed for export] *)
Definition OPMOD_SCR : Z := 96 + DIVO_SCR.              (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DIVN_K : Z := 3.
Definition DIVN_BYTES : Z := 192.

(* [comment removed for export] *)
Definition dsaves (R : bvmap 5 word) (M : word -> option byte) (E : Z) : Prop :=
     L5.u64_at RSEGS M (E - 8) (U R 1) /\ L5.u64_at RSEGS M (E - 16) (U R 8) /\ L5.u64_at RSEGS M (E - 24) (U R 9)
  /\ L5.u64_at RSEGS M (E - 32) (U R 18) /\ L5.u64_at RSEGS M (E - 40) (U R 19) /\ L5.u64_at RSEGS M (E - 48) (U R 20)
  /\ L5.u64_at RSEGS M (E - 56) (U R 21) /\ L5.u64_at RSEGS M (E - 64) (U R 22) /\ L5.u64_at RSEGS M (E - 72) (U R 23)
  /\ L5.u64_at RSEGS M (E - 80) (U R 24) /\ L5.u64_at RSEGS M (E - 88) (U R 25) /\ L5.u64_at RSEGS M (E - 96) (U R 26)
  /\ L5.u64_at RSEGS M (E - 104) (U R 27).
(* [comment removed for export] *)
Definition rsaves (R : bvmap 5 word) (M : word -> option byte) (E : Z) : Prop :=
     L5.u64_at RSEGS M (E - 8) (U R 1) /\ L5.u64_at RSEGS M (E - 16) (U R 8) /\ L5.u64_at RSEGS M (E - 24) (U R 9)
  /\ L5.u64_at RSEGS M (E - 32) (U R 18) /\ L5.u64_at RSEGS M (E - 40) (U R 19) /\ L5.u64_at RSEGS M (E - 48) (U R 20)
  /\ L5.u64_at RSEGS M (E - 56) (U R 21) /\ L5.u64_at RSEGS M (E - 64) (U R 22) /\ L5.u64_at RSEGS M (E - 72) (U R 23)
  /\ L5.u64_at RSEGS M (E - 80) (U R 24) /\ L5.u64_at RSEGS M (E - 88) (U R 25) /\ L5.u64_at RSEGS M (E - 96) (U R 26).

(* [comment removed for export] *)
Definition mword_obj (M : word -> option byte) (dv fdv : Z) : Prop :=
  L5.big_at RSEGS M dv (L5.BO fdv 1 (L5.BInl MWORD 0)) /\ Z.testbit fdv 1 = false.
(* [comment removed for export] *)
Definition zero_obj (M : word -> option byte) (o : Z) : Prop := L5.big_at RSEGS M o (L5.BO 0 0 (L5.BInl 0 0)).
(* [comment removed for export] *)
Definition stkobj (ar : asan_run) (E o sz : Z) : Prop := E <= o /\ o + sz <= ar_sptop ar /\ o mod 8 = 0.

(* [comment removed for export] *)
Definition sh_rz (M : word -> option byte) (F : Z) : Prop :=
  sh_run M F 0 4 0xf1 /\ sh_run M F 4 3 0xf8 /\ sh_run M F 7 1 0xf3 /\ sh_run M F 8 4 0xf3 /\ sh_run M F 12 4 0.
(* [comment removed for export] *)
Definition sh_op (M : word -> option byte) (F : Z) : Prop :=
  sh_run M F 0 4 0xf1 /\ sh_run M F 4 4 0 /\ sh_run M F 8 4 0xf3 /\ sh_run M F 12 4 0.
(* [comment removed for export] *)
Definition sh_div (M : word -> option byte) (F vn v0 vq vr vh : Z) : Prop :=
     sh_run M F 0 4 0xf1 /\ sh_run M F 4 4 0
  /\ sh_run M F 8 4 0xf2 /\ sh_run M F 12 4 vn /\ sh_run M F 16 4 0xf2 /\ sh_run M F 20 4 v0 /\ sh_run M F 24 4 0xf2 /\ sh_run M F 28 4 vq
  /\ sh_run M F 32 4 0xf2 /\ sh_run M F 36 4 vr /\ sh_run M F 40 4 0xf2 /\ sh_run M F 44 4 vh /\ sh_run M F 48 4 0xf3 /\ sh_run M F 52 12 0.

Section Specs.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition resize_huge_atA (LB : list (Z * Z)) (FF : list fframe) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o E n : Z) (lenb : nat) (F1c fl1c F1d fl1d : Z) : Prop :=
     getr R' 2%bv = Z_to_bv 64 (E - 256) /\ getr R' 3%bv = getr R 3%bv /\ getr R' 4%bv = getr R 4%bv
  /\ getr R' 10%bv = Z_to_bv 64 16
  /\ getr R' 8%bv = Z_to_bv 64 (E - 128) /\ getr R' 9%bv = Z_to_bv 64 (E - 256)
  /\ getr R' 18%bv = Z_to_bv 64 F1d /\ getr R' 19%bv = Z_to_bv 64 o /\ getr R' 20%bv = Z_to_bv 64 (F1d + 32)
  /\ getr R' 21%bv = Z_to_bv 64 (o + 8) /\ getr R' 22%bv = Z_to_bv 64 (S F1c) /\ getr R' 23%bv = Z_to_bv 64 (S F1d)
  /\ getr R' 24%bv = Z_to_bv 64 F1d /\ getr R' 25%bv = Z_to_bv 64 SB /\ getr R' 26%bv = Z_to_bv 64 (S (o + 8)) /\ getr R' 27%bv = getr R 27%bv
  (* [comment removed for export] *)
  /\ rsaves R M' E /\ L5.u64_at RSEGS M' (E - 104) F1c
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (E - 136) RESERVE_RET /\ L5.u64_at RSEGS M' (E - 144) E /\ L5.u64_at RSEGS M' (E - 152) (E - 128)
  /\ L5.u64_at RSEGS M' (E - 160) F1c /\ L5.u64_at RSEGS M' (E - 168) n /\ L5.u64_at RSEGS M' (E - 176) o
  /\ L5.u64_at RSEGS M' (E - 184) (o + 8) /\ L5.u64_at RSEGS M' (E - 192) (S F1c) /\ L5.u64_at RSEGS M' (E - 200) F1c
  /\ L5.u64_at RSEGS M' (E - 208) SB /\ L5.u64_at RSEGS M' (E - 216) (Z.of_nat lenb) /\ L5.u64_at RSEGS M' (E - 224) (S (o + 8))
  /\ L5.u64_at RSEGS M' (E - 232) F1d
  (* [comment removed for export] *)
  /\ sh_rz M' F1c /\ sh_rz M' F1d
  /\ fr_live L ar LB ((F1c, 1, E - 96) :: FF) M' 1 F1d fl1d (E - 224)
  /\ fr_live L ar LB FF M' 1 F1c fl1c (E - 96)
  (* [comment removed for export] *)
  /\ ahpres L ar LB FF E RESIZE_SCR [] M M'.
Definition ff_rz (FF : list fframe) (E F1c F1d : Z) : list fframe := (F1d, 1, E - 224) :: (F1c, 1, E - 96) :: FF.

Definition resize_hugeA_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r n : Z) (b : L5.bigobj),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> MAX_SIZE <= n < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp RESIZE_SCR ->
    ffr FF LK 4 -> ffrs FF sp ->
    L5.big_at RSEGS M o b -> L5.bo_dyn b = true -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (A' : list (Z * Z))
            (F1c fl1c F1d fl1d : Z),
        resize_huge_atA LB FF M M' R R' o sp n (L5.bo_len b) F1c fl1c F1d fl1d ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB (ff_rz FF sp F1c F1d) LK' cr A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R RESIZE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition divN_postA (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX rr dv fdv E : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists fbq nq wq, L5.big_at RSEGS M' X (L5.BO fbq nq (L5.BDyn 8 qX)) /\ L5C.obj_limbs RSEGS M' (L5.BO fbq nq (L5.BDyn 8 qX)) wq
                       /\ Z.testbit fbq 1 = false /\ (nq <= 6)%nat)
  /\ (exists fbr nr str wr, L5.big_at RSEGS M' rr (L5.BO fbr nr str) /\ L5C.obj_limbs RSEGS M' (L5.BO fbr nr str) wr /\
        match str with
        | L5.BInl _ _ => LB' = LB
        | L5.BDyn cap q => cap = 8 /\ LB' = (q, 64) :: LB /\ afresh L ar LB (FF ++ LKq) M' q 64
        end)
  /\ mword_obj M' dv fdv
  /\ L5OMA.acredit_after L cr DIVN_K DIVN_BYTES cr'
  /\ ahpres L ar LB FF E DIVN_SCR [(X, 32); (qX, 64); (rr, 32)] M M'.

(* [comment removed for export] *)
Definition ff_n (FF : list fframe) (E F3 F1c F1d : Z) : list fframe := ff_rz ((F3, 3, E - 320) :: FF) (E - 352) F1c F1d.

(* [comment removed for export] *)
Definition divN_e3A (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX : Z) (lenX : nat) (rr dv E : Z) (F3 fl3 F1c fl1c F1d fl1d : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists (RZ : bvmap 5 word) (MZ : word -> option byte) (B0 B1 fd0 fn0 fn fden w1 : Z),
  (* [comment removed for export] *)
     U RZ 1 = RESIZE_RET_G /\ U RZ 8 = E /\ U RZ 9 = E - 352
  /\ U RZ 18 = S F3 /\ U RZ 19 = F3 + 32 /\ U RZ 20 = F3 + 96 /\ U RZ 21 = SB /\ U RZ 22 = X /\ U RZ 23 = rr /\ U RZ 24 = X
  /\ U RZ 25 = U R 25 /\ U RZ 26 = F3 + 48 /\ getr RZ 27%bv = Z_to_bv 64 0
  /\ getr RZ 3%bv = getr R 3%bv /\ getr RZ 4%bv = getr R 4%bv
  /\ resize_huge_atA LB' ((F3, 3, E - 320) :: FF) MZ M' RZ R' X (E - 352) (2 ^ 64 - 1) lenX F1c fl1c F1d fl1d
  (* [comment removed for export] *)
  /\ dsaves R M' E
  /\ L5.u64_at RSEGS M' (E - 336) 0 /\ L5.u64_at RSEGS M' (E - 296) F3 /\ L5.u64_at RSEGS M' (E - 280) F3
  /\ L5.u64_at RSEGS M' (E - 272) (F3 + 96) /\ L5.u64_at RSEGS M' (E - 264) (F3 + 32) /\ L5.u64_at RSEGS M' (E - 256) rr
  /\ L5.u64_at RSEGS M' (E - 248) X /\ L5.u64_at RSEGS M' (E - 240) (S F3) /\ L5.u64_at RSEGS M' (E - 224) (F3 + 48)
  /\ L5.u64_at RSEGS M' (E - 216) 1 /\ L5.u64_at RSEGS M' (E - 208) X /\ L5.u64_at RSEGS M' (E - 200) SB /\ L5.u64_at RSEGS M' (E - 192) F3
  /\ L5.u32_at RSEGS M' (E - 172) 0
  (* [comment removed for export] *)
  /\ L5.big_at RSEGS M' (E - 168) (L5.BO fd0 1 (L5.BInl MWORD 0))
  /\ L5.big_at RSEGS M' (E - 136) (L5.BO fn0 lenX (L5.BDyn 8 B0))
  (* [comment removed for export] *)
  /\ L5.big_at RSEGS M' (F3 + 96) (L5.BO fn 0 (L5.BDyn 8 B1)) /\ Z.testbit fn 1 = false
  /\ L5.big_at RSEGS M' (F3 + 32) (L5.BO fden 1 (L5.BInl MWORD w1)) /\ Z.testbit fden 1 = false
  /\ sh_div M' F3 0 0xf8 0xf8 0xf8 0xf8
  /\ fr_live L ar LB' FF M' 3 F3 fl3 (E - 320)
  (* [comment removed for export] *)
  /\ LB' = (B0, 64) :: (B1, 64) :: LB
  /\ cr' = adebit L (adebit L cr 64) 64
  (* [comment removed for export] *)
  /\ ahpres L ar LB FF E DIVN_SCR [] M M'.

Definition divN_specA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (X qX rr dv fdv E r : Z) (bX : L5.bigobj) (wX : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 X -> getr R 11%bv = Z_to_bv 64 dv -> getr R 12%bv = Z_to_bv 64 X -> getr R 13%bv = Z_to_bv 64 rr ->
    getr R 14%bv = Z_to_bv 64 0 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E DIVN_SCR ->
    L5OMA.stksh ar M (E - DIVN_SCR) ->
    ffrk 1 FF LK 4 -> ffrk 3 FF LK 2 -> ffrs FF E ->
    (* [comment removed for export] *)
    L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> L5.bo_st bX = L5.BDyn 8 qX -> (2 <= L5.bo_len bX <= 6)%nat ->
    Z.testbit (L5.bo_fb bX) 1 = false -> In (qX, 64) LB -> aobj FF X 32 -> shadow_zero M X 4 ->
    (* [comment removed for export] *)
    mword_obj M dv fdv -> stkobj ar E dv 32 -> L5.defined M dv 32 ->
    zero_obj M rr -> aobj FF rr 32 -> shadow_zero M rr 4 ->
    (X + 32 <= rr \/ rr + 32 <= X) ->
    L5OMA.acredit_for L cr DIVN_K DIVN_BYTES ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        divN_postA LB FF LK' cr M M' R R' X qX rr dv fdv E LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            (F3 fl3 F1c fl1c F1d fl1d : Z),
        divN_e3A LB FF cr M M' R R' X qX (L5.bo_len bX) rr dv E F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' (ff_n FF E F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R DIVIDE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition diveq_postA (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX dv fdv E : Z) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 X
  /\ (exists fbq nq wq, L5.big_at RSEGS M' X (L5.BO fbq nq (L5.BDyn 8 qX)) /\ L5C.obj_limbs RSEGS M' (L5.BO fbq nq (L5.BDyn 8 qX)) wq
                       /\ Z.testbit fbq 1 = false /\ (nq <= 6)%nat)
  /\ mword_obj M' dv fdv
  /\ L5OMA.acredit_after L cr DIVN_K DIVN_BYTES cr'
  /\ ahpres L ar LB FF E DIVEQ_SCR [(X, 32); (qX, 64)] M M'.

(* [comment removed for export] *)
Definition ff_q (FF : list fframe) (E F1 F3 F1c F1d : Z) : list fframe := ff_n ((F1, 1, E - 64) :: FF) (E - 96) F3 F1c F1d.

(* [comment removed for export] *)
Definition diveq_e3A (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX : Z) (lenX : nat) (dv E : Z) (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists (RN : bvmap 5 word) (MN : word -> option byte),
     U RN 1 = DIV_RET_N /\ U RN 8 = E /\ U RN 9 = E - 96
  /\ U RN 18 = F1 /\ U RN 19 = X /\ U RN 20 = dv /\ U RN 21 = F1 + 32 /\ U RN 22 = S F1 /\ U RN 23 = F1 /\ U RN 24 = RETIRE_MAGIC
  /\ U RN 25 = U R 25 /\ U RN 26 = U R 26 /\ U RN 27 = U R 27
  /\ getr RN 3%bv = getr R 3%bv /\ getr RN 4%bv = getr R 4%bv
  /\ divN_e3A LB ((F1, 1, E - 64) :: FF) cr MN M' RN R' X qX lenX (F1 + 32) dv (E - 96) F3 fl3 F1c fl1c F1d fl1d LB' cr'
  (* [comment removed for export] *)
  /\ opmod_frame R M' E F1
  /\ zero_obj M' (F1 + 32) /\ sh_op M' F1
  /\ fr_live L ar LB' FF M' 1 F1 fl1 (E - 64)
  /\ ahpres L ar LB FF E DIVEQ_SCR [] M M'.

Definition diveq_specA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (X qX dv fdv E r : Z) (bX : L5.bigobj) (wX : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 X -> getr R 11%bv = Z_to_bv 64 dv ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E DIVEQ_SCR ->
    L5OMA.stksh ar M (E - DIVEQ_SCR) ->
    ffrk 1 FF LK 5 -> ffrk 3 FF LK 2 -> ffrs FF E ->
    L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> L5.bo_st bX = L5.BDyn 8 qX -> (2 <= L5.bo_len bX <= 6)%nat ->
    Z.testbit (L5.bo_fb bX) 1 = false -> In (qX, 64) LB -> aobj FF X 32 -> shadow_zero M X 4 ->
    mword_obj M dv fdv -> stkobj ar E dv 32 -> L5.defined M dv 32 ->
    L5OMA.acredit_for L cr DIVN_K DIVN_BYTES ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
        diveq_postA LB FF cr M M' R R' X qX dv fdv E cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
        diveq_e3A LB FF cr M M' R R' X qX (L5.bo_len bX) dv E F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' (ff_q FF E F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPDIV M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unnorm_postA (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X E : Z) (bX : L5.bigobj) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists fb' n' st' w', L5.big_at RSEGS M' X (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' n' st') w'
        /\ Z.testbit fb' 1 = false
        /\ match L5.bo_st bX, st' with
           | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
           | L5.BInl _ _, L5.BInl _ _ => True
           | _, _ => False end)
  /\ L5OMA.acredit_after L cr DIVN_K DIVN_BYTES cr'
  /\ ahpres L ar LB FF E UNNORM_SCR [(X, 32); (L5.bo_data X bX, 8 * L5.bo_cap bX)] M M'.

Definition ff_u (FF : list fframe) (E F1 F3 F1c F1d : Z) : list fframe := ff_q FF (E - 64) F1 F3 F1c F1d.

Definition unnorm_e3A (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX : Z) (lenX : nat) (E : Z) (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists (RQ : bvmap 5 word) (MQ : word -> option byte),      (* [comment removed for export] *)
     U RQ 1 = DIVEQ_RET /\ U RQ 8 = X /\ U RQ 9 = U R 12
  /\ (forall k, 18 <= k <= 27 -> U RQ k = U R k)
  /\ getr RQ 3%bv = getr R 3%bv /\ getr RQ 4%bv = getr R 4%bv
  /\ diveq_e3A LB FF cr MQ M' RQ R' X qX lenX (E - 56) (E - 64) F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr'
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (E - 8) (U R 1) /\ L5.u64_at RSEGS M' (E - 16) (U R 8) /\ L5.u64_at RSEGS M' (E - 24) (U R 9)
  /\ mword_obj M' (E - 56) 0
  /\ ahpres L ar LB FF E UNNORM_SCR [] M M'.

Definition unnorm_specA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (X xs sd E r : Z) (bX : L5.bigobj) (wX : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 11%bv = Z_to_bv 64 X -> getr R 12%bv = Z_to_bv 64 xs -> 0 <= xs <= 63 -> getr R 13%bv = Z_to_bv 64 sd -> (sd = 0 \/ sd = 1) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E UNNORM_SCR ->
    L5OMA.stksh ar M (E - UNNORM_SCR) ->
    ffrk 1 FF LK 5 -> ffrk 3 FF LK 2 -> ffrs FF E ->
    L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> (1 <= L5.bo_len bX <= 299)%nat -> Z.testbit (L5.bo_fb bX) 1 = false ->
    aobj FF X 32 -> shadow_zero M X 4 ->
    (forall cap q, L5.bo_st bX = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (sd = 1 -> exists qX, L5.bo_st bX = L5.BDyn 8 qX /\ (2 <= L5.bo_len bX <= 6)%nat) ->
    (sd = 1 -> L5OMA.acredit_for L cr DIVN_K DIVN_BYTES) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
        unnorm_postA LB FF cr M M' R R' X E bX cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) qX LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
        sd = 1 -> L5.bo_st bX = L5.BDyn 8 qX ->
        unnorm_e3A LB FF cr M M' R R' X qX (L5.bo_len bX) E F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' (ff_u FF E F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R UNNORM M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition q_after (LB : list (Z * Z)) (FFq : list fframe) (M' : word -> option byte) (qo : Z) (LBq : list (Z * Z)) : Prop :=
  exists bq wq, L5.big_at RSEGS M' qo bq /\ L5C.obj_limbs RSEGS M' bq wq /\
    match L5.bo_st bq with
    | L5.BInl _ _ => LBq = []
    | L5.BDyn cap q => LBq = [(q, 8 * cap)] /\ afresh L ar LB FFq M' q (8 * cap)
    end.

(* [comment removed for export] *)
Definition DIVO1_K : Z := 8.
Definition divO1_bytes (capb : Z) : Z := 8 * capb + 640.

Definition divO1_postA (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (xo bo qo E : Z) (bb : L5.bigobj) (wb : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists LBx LBq, LB' = LBx ++ LBq ++ LB
        /\ (exists bx wx, L5.big_at RSEGS M' xo bx /\ L5C.obj_limbs RSEGS M' bx wx /\ L5.bo_neg bx = false /\
              match L5.bo_st bx with
              | L5.BInl _ _ => LBx = []
              | L5.BDyn cap q => cap = 8 /\ LBx = [(q, 64)] /\ afresh L ar (LBq ++ LB) (FF ++ LKq) M' q 64
              end)
        /\ q_after LB (FF ++ LKq) M' qo LBq)
  /\ L5.big_at RSEGS M' bo bb /\ L5C.obj_limbs RSEGS M' bb wb /\ (1 <= L5.bo_len bb)%nat
  /\ L5OMA.acredit_after L cr DIVO1_K (divO1_bytes (L5.bo_cap bb)) cr'
  /\ ahpres L ar LB FF E DIVO_SCR [(xo, 32); (qo, 32)] M M'.

(* [comment removed for export] *)
Definition divO_e2A (LB : list (Z * Z)) (FF : list fframe) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (xo qo E F3 fl3 : Z) : Prop :=
  exists fden v16 v24,
     getr R' 2%bv = Z_to_bv 64 (E - 352) /\ getr R' 3%bv = getr R 3%bv /\ getr R' 4%bv = getr R 4%bv
  /\ getr R' 10%bv = Z_to_bv 64 16
  /\ getr R' 8%bv = Z_to_bv 64 E /\ getr R' 9%bv = Z_to_bv 64 (E - 352)
  /\ getr R' 18%bv = Z_to_bv 64 (S F3) /\ getr R' 19%bv = Z_to_bv 64 qo /\ getr R' 20%bv = Z_to_bv 64 0
  /\ getr R' 21%bv = Z_to_bv 64 fden /\ getr R' 22%bv = Z_to_bv 64 1 /\ getr R' 23%bv = Z_to_bv 64 (F3 + 32)
  /\ getr R' 24%bv = Z_to_bv 64 xo /\ getr R' 25%bv = getr R 25%bv /\ getr R' 26%bv = Z_to_bv 64 (F3 + 48) /\ getr R' 27%bv = Z_to_bv 64 F3
  /\ dsaves R M' E
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (E - 296) F3 /\ L5.u64_at RSEGS M' (E - 280) F3 /\ L5.u64_at RSEGS M' (E - 192) F3
  /\ L5.u64_at RSEGS M' (E - 264) (F3 + 32) /\ L5.u64_at RSEGS M' (E - 256) xo
  /\ L5.u64_at RSEGS M' (E - 240) (S F3) /\ L5.u64_at RSEGS M' (E - 200) SB
  /\ L5.big_at RSEGS M' (F3 + 32) (L5.BO fden 0 (L5.BInl v16 v24))
  /\ sh_div M' F3 0xf8 0xf8 0xf8 0xf8 0xf8
  /\ fr_live L ar LB FF M' 3 F3 fl3 (E - 320)
  /\ ahpres L ar LB FF E DIVO_SCR [] M M'.

(* [comment removed for export] *)
Definition ff_o (FF : list fframe) (E F3a F1b F3b F1c F1d : Z) : list fframe := ff_u ((F3a, 3, E - 320) :: FF) (E - 352) F1b F3b F1c F1d.

(* [comment removed for export] *)
Definition divO1_e3A (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (xo qo E : Z) (F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d : Z) (qx : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists (RU : bvmap 5 word) (MU : word -> option byte) (d3 d4 : Z) (lenX : nat) (LBm : list (Z * Z)) (crm : credit)
         (fbx fd0 fn0 fn fden v0 v1 v2 v3 : Z) (nd0 nn0 nn nd : nat) (bq : L5.bigobj),
     U RU 1 = UNNORM_RET /\ U RU 8 = E /\ U RU 9 = E - 352
  /\ U RU 18 = S F3a /\ U RU 19 = xo /\ U RU 20 = F3a + 32 /\ U RU 21 = F3a + 96 /\ U RU 22 = qo /\ U RU 23 = S xo /\ U RU 24 = F3a
  /\ U RU 27 = F3a
  /\ getr RU 3%bv = getr R 3%bv /\ getr RU 4%bv = getr R 4%bv
  /\ LBm = (qx, 64) :: (d3, 64) :: (d4, 64) :: LB
  /\ unnorm_e3A LBm ((F3a, 3, E - 320) :: FF) crm MU M' RU R' xo qx lenX (E - 352) F1b fl1b F3b fl3b F1c fl1c F1d fl1d LB' cr'
  (* [comment removed for export] *)
  /\ dsaves R M' E
  /\ L5.u64_at RSEGS M' (E - 336) 1 /\ L5.u64_at RSEGS M' (E - 296) F3a /\ L5.u64_at RSEGS M' (E - 280) F3a
  /\ L5.u64_at RSEGS M' (E - 272) (F3a + 96) /\ L5.u64_at RSEGS M' (E - 264) (F3a + 32) /\ L5.u64_at RSEGS M' (E - 256) xo
  /\ L5.u64_at RSEGS M' (E - 248) qo /\ L5.u64_at RSEGS M' (E - 240) (S F3a)
  /\ L5.u64_at RSEGS M' (E - 208) xo /\ L5.u64_at RSEGS M' (E - 200) SB /\ L5.u64_at RSEGS M' (E - 192) F3a
  (* [comment removed for export] *)
  /\ L5.big_at RSEGS M' (E - 168) (L5.BO fd0 nd0 (L5.BInl v0 v1))
  /\ L5.big_at RSEGS M' (E - 136) (L5.BO fn0 nn0 (L5.BInl v2 v3))
  /\ L5.big_at RSEGS M' (F3a + 96) (L5.BO fn nn (L5.BDyn 8 d3))
  /\ L5.big_at RSEGS M' (F3a + 32) (L5.BO fden nd (L5.BDyn 8 d4))
  /\ sh_div M' F3a 0 0xf8 0xf8 0xf8 0xf8
  /\ fr_live L ar LB' FF M' 3 F3a fl3a (E - 320)
  (* [comment removed for export] *)
  /\ L5.big_at RSEGS M' xo (L5.BO fbx lenX (L5.BDyn 8 qx))
  /\ L5.big_at RSEGS M' qo bq /\ L5.bo_dyn bq = false
  /\ afresh L ar LB FF M' qx 64
  /\ credit_le (L5OMA.adebits L cr 5 320) cr'
  /\ ahpres L ar LB FF E DIVO_SCR [(xo, 32); (qo, 32)] M M'.

Definition divO1_specA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (xo bo qo E r fbx : Z) (bb : L5.bigobj) (wb : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 xo -> getr R 11%bv = Z_to_bv 64 bo -> getr R 12%bv = Z_to_bv 64 qo -> getr R 13%bv = Z_to_bv 64 xo ->
    getr R 14%bv = Z_to_bv 64 1 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E DIVO_SCR ->
    L5OMA.stksh ar M (E - DIVO_SCR) ->
    ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 -> ffrs FF E ->
    L5OMA.x_is_a M xo fbx -> aobj FF xo 32 -> shadow_zero M xo 4 ->
    L5OMA.b_ok LB M bo bb wb -> aobj FF bo 32 -> shadow_zero M bo 4 ->
    zero_obj M qo -> aobj FF qo 32 -> shadow_zero M qo 4 ->
    (xo + 32 <= bo \/ bo + 32 <= xo) -> (xo + 32 <= qo \/ qo + 32 <= xo) -> (bo + 32 <= qo \/ qo + 32 <= bo) ->
    L5.bo_cap bb <= 268 -> (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->
    L5OMA.acredit_for L cr DIVO1_K (divO1_bytes (L5.bo_cap bb)) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        divO1_postA LB FF LK' cr M M' R R' xo bo qo E bb wb LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (F3 fl3 : Z),
        L5.bo_len bb = 0%nat ->
        divO_e2A LB FF M M' R R' xo qo E F3 fl3 ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB ((F3, 3, E - 320) :: FF) LK' cr A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' ZERO_THROW M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            (F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx : Z),
        divO1_e3A LB FF cr M M' R R' xo qo E F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d qx LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' (ff_o FF E F3a F1b F3b F1c F1d) LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R DIVIDE M model) K.

(* [comment removed for export] *)
Definition DIVO2_K : Z := 8.
Definition divO2_bytes (capy : Z) : Z := 24 * capy + 640.

Definition divO2_postA (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (yo ao qo E fba : Z) (by_ : L5.bigobj) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists LBy LBq, LB' = LBy ++ LBq ++ LB
        /\ (exists by' wy', L5.big_at RSEGS M' yo by' /\ L5C.obj_limbs RSEGS M' by' wy' /\
              match L5.bo_st by_, L5.bo_st by' with
              | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q /\ LBy = []
              | L5.BInl _ _, L5.BInl _ _ => LBy = []
              | L5.BInl _ _, L5.BDyn cap' q' => cap' = 8 /\ LBy = [(q', 64)] /\ afresh L ar (LBq ++ LB) (FF ++ LKq) M' q' 64
              | L5.BDyn _ _, L5.BInl _ _ => False
              end)
        /\ q_after LB (FF ++ LKq) M' qo LBq)
  /\ L5OMA.a_ok M' ao fba
  /\ L5OMA.acredit_after L cr DIVO2_K (divO2_bytes (L5.bo_cap by_)) cr'
  /\ ahpres L ar LB FF E DIVO_SCR [(yo, 32); (L5.bo_data yo by_, 8 * L5.bo_cap by_); (qo, 32)] M M'.

Definition divO2_specA : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (yo ao qo E r fba : Z) (by_ : L5.bigobj) (wy : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 yo -> getr R 11%bv = Z_to_bv 64 ao -> getr R 12%bv = Z_to_bv 64 qo -> getr R 13%bv = Z_to_bv 64 yo ->
    getr R 14%bv = Z_to_bv 64 1 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E DIVO_SCR ->
    L5OMA.stksh ar M (E - DIVO_SCR) ->
    ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 -> ffrs FF E ->
    L5OMA.y_ok LB M yo by_ wy -> aobj FF yo 32 -> shadow_zero M yo 4 -> (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->
    L5OMA.a_ok M ao fba -> aobj FF ao 32 -> shadow_zero M ao 4 ->
    zero_obj M qo -> aobj FF qo 32 -> shadow_zero M qo 4 ->
    (yo + 32 <= ao \/ ao + 32 <= yo) -> (yo + 32 <= qo \/ qo + 32 <= yo) -> (ao + 32 <= qo \/ qo + 32 <= ao) ->
    L5OMA.acredit_for L cr DIVO2_K (divO2_bytes (L5.bo_cap by_)) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        divO2_postA LB FF LK' cr M M' R R' yo ao qo E fba by_ LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R DIVIDE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition assert_throw_atA (LBT LB1 : list (Z * Z)) (FF : list fframe) (R0 : bvmap 5 word) (M0 : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (S_ xo : Z) (FR : list (Z * Z)) : Prop :=
  exists (F1a fl1a F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d d1 d2 d3 d4 qx bo : Z) (LB0 : list (Z * Z)) (lenX : nat)
         (w9 w10 xs fbx : Z) (fd0N fn0N fnN fdenN w1 : Z) (fd0 fn0 fn fden v0 v1 v2 v3 : Z) (nd0 nn0 nn nd : nat) (bq : L5.bigobj),
     FR = [(F1a, fl1a); (F3a, fl3a); (F1b, fl1b); (F3b, fl3b); (F1c, fl1c); (F1d, fl1d)]
  /\ LBT = [(d1, 64); (d2, 64); (d3, 64); (d4, 64)] /\ LB1 = (qx, 64) :: LB0
  /\ assert_throw_regs R0 R S_ xo F1c F1d
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 1096) RESERVE_RET /\ L5.u64_at RSEGS M (S_ - 1104) (S_ - 960) /\ L5.u64_at RSEGS M (S_ - 1112) (S_ - 1088)
  /\ L5.u64_at RSEGS M (S_ - 1120) F1c /\ L5.u64_at RSEGS M (S_ - 1128) (2 ^ 64 - 1) /\ L5.u64_at RSEGS M (S_ - 1136) xo
  /\ L5.u64_at RSEGS M (S_ - 1144) (xo + 8) /\ L5.u64_at RSEGS M (S_ - 1152) (S F1c) /\ L5.u64_at RSEGS M (S_ - 1160) F1c
  /\ L5.u64_at RSEGS M (S_ - 1168) SB /\ L5.u64_at RSEGS M (S_ - 1176) (Z.of_nat lenX) /\ L5.u64_at RSEGS M (S_ - 1184) (S (xo + 8))
  /\ L5.u64_at RSEGS M (S_ - 1192) F1d
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 968) RESIZE_RET_G /\ L5.u64_at RSEGS M (S_ - 976) (S_ - 608) /\ L5.u64_at RSEGS M (S_ - 984) (S_ - 960)
  /\ L5.u64_at RSEGS M (S_ - 992) (S F3b) /\ L5.u64_at RSEGS M (S_ - 1000) (F3b + 32) /\ L5.u64_at RSEGS M (S_ - 1008) (F3b + 96)
  /\ L5.u64_at RSEGS M (S_ - 1016) SB /\ L5.u64_at RSEGS M (S_ - 1024) xo /\ L5.u64_at RSEGS M (S_ - 1032) (F1b + 32)
  /\ L5.u64_at RSEGS M (S_ - 1040) xo /\ L5.u64_at RSEGS M (S_ - 1048) w9 /\ L5.u64_at RSEGS M (S_ - 1056) (F3b + 48)
  /\ L5.u64_at RSEGS M (S_ - 1064) F1c
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 616) DIV_RET_N /\ L5.u64_at RSEGS M (S_ - 624) (S_ - 512) /\ L5.u64_at RSEGS M (S_ - 632) (S_ - 608)
  /\ L5.u64_at RSEGS M (S_ - 640) F1b /\ L5.u64_at RSEGS M (S_ - 648) xo /\ L5.u64_at RSEGS M (S_ - 656) (S_ - 504)
  /\ L5.u64_at RSEGS M (S_ - 664) (F1b + 32) /\ L5.u64_at RSEGS M (S_ - 672) (S F1b) /\ L5.u64_at RSEGS M (S_ - 680) F1b
  /\ L5.u64_at RSEGS M (S_ - 688) RETIRE_MAGIC /\ L5.u64_at RSEGS M (S_ - 696) w9 /\ L5.u64_at RSEGS M (S_ - 704) w10
  /\ L5.u64_at RSEGS M (S_ - 712) F3a
  /\ L5.u64_at RSEGS M (S_ - 944) 0 /\ L5.u64_at RSEGS M (S_ - 904) F3b /\ L5.u64_at RSEGS M (S_ - 888) F3b
  /\ L5.u64_at RSEGS M (S_ - 880) (F3b + 96) /\ L5.u64_at RSEGS M (S_ - 872) (F3b + 32) /\ L5.u64_at RSEGS M (S_ - 864) (F1b + 32)
  /\ L5.u64_at RSEGS M (S_ - 856) xo /\ L5.u64_at RSEGS M (S_ - 848) (S F3b) /\ L5.u64_at RSEGS M (S_ - 832) (F3b + 48)
  /\ L5.u64_at RSEGS M (S_ - 824) 1 /\ L5.u64_at RSEGS M (S_ - 816) xo /\ L5.u64_at RSEGS M (S_ - 808) SB /\ L5.u64_at RSEGS M (S_ - 800) F3b
  /\ L5.u32_at RSEGS M (S_ - 780) 0
  /\ L5.big_at RSEGS M (S_ - 776) (L5.BO fd0N 1 (L5.BInl MWORD 0))
  /\ L5.big_at RSEGS M (S_ - 744) (L5.BO fn0N lenX (L5.BDyn 8 d1))
  /\ L5.big_at RSEGS M (F3b + 96) (L5.BO fnN 0 (L5.BDyn 8 d2)) /\ Z.testbit fnN 1 = false
  /\ L5.big_at RSEGS M (F3b + 32) (L5.BO fdenN 1 (L5.BInl MWORD w1)) /\ Z.testbit fdenN 1 = false
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 520) DIVEQ_RET /\ L5.u64_at RSEGS M (S_ - 528) xo /\ L5.u64_at RSEGS M (S_ - 536) xs
  /\ L5.u64_at RSEGS M (S_ - 544) (S F3a) /\ L5.u64_at RSEGS M (S_ - 552) xo /\ L5.u64_at RSEGS M (S_ - 560) (F3a + 32)
  /\ L5.u64_at RSEGS M (S_ - 568) (F3a + 96) /\ L5.u64_at RSEGS M (S_ - 576) (F1a + 32) /\ L5.u64_at RSEGS M (S_ - 584) (S xo)
  /\ L5.u64_at RSEGS M (S_ - 592) F3a /\ L5.u64_at RSEGS M (S_ - 600) F1b
  /\ zero_obj M (F1b + 32)
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 456) UNNORM_RET /\ L5.u64_at RSEGS M (S_ - 464) (S_ - 96) /\ L5.u64_at RSEGS M (S_ - 472) (S_ - 448)
  /\ mword_obj M (S_ - 504) 0
  (* [comment removed for export] *)
  /\ divO_saves R0 M S_ F1a xo bo
  /\ L5.u64_at RSEGS M (S_ - 432) 1 /\ L5.u64_at RSEGS M (S_ - 392) F3a /\ L5.u64_at RSEGS M (S_ - 376) F3a
  /\ L5.u64_at RSEGS M (S_ - 368) (F3a + 96) /\ L5.u64_at RSEGS M (S_ - 360) (F3a + 32) /\ L5.u64_at RSEGS M (S_ - 352) xo
  /\ L5.u64_at RSEGS M (S_ - 344) (F1a + 32) /\ L5.u64_at RSEGS M (S_ - 336) (S F3a)
  /\ L5.u64_at RSEGS M (S_ - 304) xo /\ L5.u64_at RSEGS M (S_ - 296) SB /\ L5.u64_at RSEGS M (S_ - 288) F3a
  /\ L5.big_at RSEGS M (S_ - 264) (L5.BO fd0 nd0 (L5.BInl v0 v1))
  /\ L5.big_at RSEGS M (S_ - 232) (L5.BO fn0 nn0 (L5.BInl v2 v3))
  /\ L5.big_at RSEGS M (F3a + 96) (L5.BO fn nn (L5.BDyn 8 d3))
  /\ L5.big_at RSEGS M (F3a + 32) (L5.BO fden nd (L5.BDyn 8 d4))
  (* [comment removed for export] *)
  /\ opmod_frame R0 M S_ F1a
  /\ L5.big_at RSEGS M (F1a + 32) bq /\ L5.bo_dyn bq = false
  /\ L5.big_at RSEGS M xo (L5.BO fbx lenX (L5.BDyn 8 qx))
  (* [comment removed for export] *)
  /\ sh_rz M F1d /\ sh_rz M F1c /\ sh_div M F3b 0 0xf8 0xf8 0xf8 0xf8 /\ sh_op M F1b /\ sh_div M F3a 0 0xf8 0xf8 0xf8 0xf8 /\ sh_op M F1a
  (* [comment removed for export] *)
  /\ fr_live L ar (LBT ++ LB1) ((F1c, 1, S_ - 1056) :: (F3b, 3, S_ - 928) :: (F1b, 1, S_ - 576) :: (F3a, 3, S_ - 416) :: (F1a, 1, S_ - 64) :: FF) M 1 F1d fl1d (S_ - 1184)
  /\ fr_live L ar (LBT ++ LB1) ((F3b, 3, S_ - 928) :: (F1b, 1, S_ - 576) :: (F3a, 3, S_ - 416) :: (F1a, 1, S_ - 64) :: FF) M 1 F1c fl1c (S_ - 1056)
  /\ fr_live L ar (LBT ++ LB1) ((F1b, 1, S_ - 576) :: (F3a, 3, S_ - 416) :: (F1a, 1, S_ - 64) :: FF) M 3 F3b fl3b (S_ - 928)
  /\ fr_live L ar (LBT ++ LB1) ((F3a, 3, S_ - 416) :: (F1a, 1, S_ - 64) :: FF) M 1 F1b fl1b (S_ - 576)
  /\ fr_live L ar (LBT ++ LB1) ((F1a, 1, S_ - 64) :: FF) M 3 F3a fl3a (S_ - 416)
  /\ fr_live L ar (LBT ++ LB1) FF M 1 F1a fl1a (S_ - 64).

(* [comment removed for export] *)
Lemma ff_o_e3 (FF : list fframe) (S_ F1a F3a F1b F3b F1c F1d : Z) :
  ff_o ((F1a, 1, S_ - 64) :: FF) (S_ - 96) F3a F1b F3b F1c F1d = ff_e3 FF S_ F1a F3a F1b F3b F1c F1d.
Proof.
  unfold ff_o, ff_u, ff_q, ff_n, ff_rz, ff_e3.
  repeat (f_equal; try lia).
Qed.

End Specs.
End SCFG_1.
End L5DIA.
