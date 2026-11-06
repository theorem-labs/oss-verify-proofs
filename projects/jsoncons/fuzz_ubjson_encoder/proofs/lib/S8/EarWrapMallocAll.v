(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtTac ArtRuns ArtBridge EarInv EarWrapMalloc EarWrapMallocL.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r5fac4_60344.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EarUkey.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_req_quantities : forall n, 0 < n <= 2 ^ 34 ->
  exists rl rz qz rs qr qn m8,
    rl = AsanTab.rz_log n /\ rz = 16 * 2 ^ rl /\ rz = 16 * qz /\ 1 <= qz <= 128 /\ n = 8 * qn + m8 /\ 0 <= m8 <= 7 /\ rs = 8 * qr /\ n <= rs <= n + 7
    /\ (rs + rz <= 65536 \/ (65536 < rs + rz /\ 8 <= n /\ 2 <= qz)).
Proof.
  intros n Hn. set (qr := if n <? 8 then 1 else (n + 7) / 8).
  assert (CASES : exists k, AsanTab.rz_log n = k /\ ((n <= 64512 /\ (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6)) \/ (64512 < n /\ k = 7))).
  { unfold AsanTab.rz_log. repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end; eexists; (split; [reflexivity|]); lia. }
  destruct CASES as (k & Ek & CK).
  exists k, (16 * 2 ^ k), (2 ^ k), (8 * qr), qr, (n / 8), (n mod 8).
  pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Rm.
  assert (Hrs : n <= 8 * qr <= n + 7 /\ (n <= 64512 -> 8 * qr <= 64512)).
  { unfold qr. destruct (Z.ltb_spec n 8); [lia|]. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
  destruct Hrs as (Hrs & Hrs64). clearbody qr.
  split; [symmetry; exact Ek|]. split; [reflexivity|]. split; [reflexivity|]. clear Ek.
  assert (Hm : 0 <= n mod 8 <= 7) by (clear - Rm; lia).
  destruct CK as [(Hle & [E|[E|[E|[E|[E|[E|E]]]]]])|(Hgt & E)]; rewrite E;
    match goal with |- context [2 ^ ?c] => let v := eval compute in (2 ^ c) in change (2 ^ c) with v end;
    (split; [clear; lia|]); (split; [exact D|]); (split; [exact Hm|]); (split; [reflexivity|]); (split; [exact Hrs|]);
    first [ left; specialize (Hrs64 Hle); clear - Hrs64; lia | right; clear - Hgt Hrs; lia ].
Qed.

Section Wrap.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLmalloc : hl_malloc L = 0x7a19c.
Hypothesis HLscr : hl_scr_malloc L = 4096.
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x698000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLk : 3 <= hl_k_per_malloc L.
Hypothesis HLlin : 2 <= hl_b_lin L.
Hypothesis HLov : 2 ^ 20 <= hl_b_overhead L.
Hypothesis FSLAW : art_fsinv_frame_law FSG FSINV.
Hypothesis FSKEYS : forall rn D g FF LK M, FSINV rn g FF LK M -> FSINV (art_rn_k rn D) g FF LK M.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).

#[using="Halloc Hwx STATIC HLsegs HLmalloc HLscr HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FS_IN"] Theorem art_wrap_mallocN :
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet),
    ri_inv (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn) LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 34 -> acredit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L (rn_ar rn) M (hl_scr_malloc L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    HeapIfaceAEr.HAR.amalloc_postG L (rn_ar rn) scfg (fun _ => art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn) [] (adebit L cr n) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.
Proof.
  intros fx0 R M model LB FF LK cr A n K RI Hhalt HMI H10 Hn ACR H4 Hret AST K0 POST.
  destruct (art_req_quantities n Hn) as (rl & rz & qz & rs & qr & qn & m8 & Erl & Erz & Erz16 & Hqz & En & Hm8 & Ers & Hrs & [Hprim|(Hsec & Hn8 & Hqz2)]).
  - rewrite HLsegs, HLmalloc. replace (Z_to_bv 64 500124) with (0x7a19c%bv : word) by (apply bv_eq; reflexivity).
    exact (art_wrap_malloc_primary FSG FSINV MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg L Halloc Hwx STATIC HLsegs HLscr HLtp HLlo HLhi
             (fun a Ha => HLst a (or_intror (or_intror (or_introl Ha)))) HLk ltac:(lia) HLov FSLAW FS_IN (fx:=fx0)
             R M model LB FF LK cr A n rl rz qz rs qr qn m8 K RI Hhalt HMI H10 (proj1 Hn) Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim ACR H4 Hret AST K0 POST).
  - set (nd := rs + rz + rz). set (q := (nd + 4095) / 4096).
    assert (Hq : 4096 * (q - 1) < nd <= 4096 * q).
    { unfold q. pose proof (Z.div_mod (nd + 4095) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (nd + 4095) 4096 ltac:(lia)). lia. }
    rewrite HLsegs, HLmalloc. replace (Z_to_bv 64 500124) with (0x7a19c%bv : word) by (apply bv_eq; reflexivity).
    exact (art_wrap_malloc_sec FSG FSINV MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg L Halloc Hwx STATIC HLsegs HLscr HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FS_IN (fx:=fx0)
             R M model LB FF LK cr A n rl rz qz rs qr qn m8 nd q (4096 * q + 4096) K RI Hhalt HMI H10 (conj Hn8 (proj2 Hn)) Erl Erz Erz16 (conj Hqz2 (proj2 Hqz)) En Hm8 Ers Hrs Hsec
             eq_refl Hq eq_refl ACR H4 Hret AST K0 POST).
Qed.

#[using="Halloc Hwx STATIC HLsegs HLmalloc HLscr HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FS_IN FSKEYS"] Theorem art_wrap_mallocU :
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet) (Kz : list Z) (warm : bool),
    ri_inv (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn) LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 34 ->
    (if warm then In Kz (rn_keys rn) /\ 64 <= n <= 128 /\ 1 <= fst cr else acredit_ok L cr n) ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L (rn_ar rn) M (hl_scr_malloc L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    ukeyG L (rn_ar rn) 0x7a440 (mrestrict (mkH (m_vm_lazy model) A) M) (bv_unsigned (getr R 2%bv)) (bv_unsigned (getr R 1%bv)) (bv_unsigned (getr R 8%bv)) Kz ->
    HeapIfaceAEr.HAR.amalloc_postG L (rn_ar rn) scfg (fun D => art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV (art_rn_k rn D)) (Kz :: rn_keys rn)
         (if warm then (fst cr - 1, snd cr) else adebit L cr n) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.
Proof.
  intros fx0 R M model LB FF LK cr A n K Kz warm RI Hhalt HMI H10 Hn MODE H4 Hret AST K0 UKz POST.
  destruct (art_req_quantities n Hn) as (rl & rz & qz & rs & qr & qn & m8 & Erl & Erz & Erz16 & Hqz & En & Hm8 & Ers & Hrs & [Hprim|(Hsec & Hn8 & Hqz2)]).
  - rewrite HLsegs, HLmalloc. replace (Z_to_bv 64 500124) with (0x7a19c%bv : word) by (apply bv_eq; reflexivity).
    exact (art_wrap_malloc_primaryU FSG FSINV MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg L Halloc Hwx STATIC HLsegs HLscr HLtp HLlo HLhi
             (fun a Ha => HLst a (or_intror (or_intror (or_introl Ha)))) HLk ltac:(lia) HLov FSLAW FSKEYS FS_IN (fx:=fx0)
             R M model LB FF LK cr A n rl rz qz rs qr qn m8 K Kz warm RI Hhalt HMI H10 (proj1 Hn) Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim MODE H4 Hret AST UKz K0 POST).
  - destruct warm. { exfalso. destruct MODE as (_ & HnW & _). clear - HnW Hsec Hrs Hqz Erz16. lia. }
    set (nd := rs + rz + rz). set (q := (nd + 4095) / 4096).
    assert (Hq : 4096 * (q - 1) < nd <= 4096 * q).
    { unfold q. pose proof (Z.div_mod (nd + 4095) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (nd + 4095) 4096 ltac:(lia)). lia. }
    rewrite HLsegs, HLmalloc. replace (Z_to_bv 64 500124) with (0x7a19c%bv : word) by (apply bv_eq; reflexivity).
    exact (art_wrap_malloc_secL FSG FSINV MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg L Halloc Hwx STATIC HLsegs HLscr HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FSKEYS FS_IN (fx:=fx0)
             R M model LB FF LK cr A n rl rz qz rs qr qn m8 nd q (4096 * q + 4096) K Kz RI Hhalt HMI H10 (conj Hn8 (proj2 Hn)) Erl Erz Erz16 (conj Hqz2 (proj2 Hqz)) En Hm8 Ers Hrs Hsec
             eq_refl Hq eq_refl MODE H4 Hret AST UKz K0 POST).
Qed.
#[using="Halloc Hwx STATIC HLsegs HLmalloc HLscr HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FS_IN"] Theorem art_wrap_malloc : amalloc_spec L (rn_ar rn) scfg (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn).
Proof.
  intros fx0 R M model LB FF LK cr A n K RI Hhalt HMI H10 Hn ACR H4 Hret AST K0 POST.
  apply (art_wrap_mallocN fx0 R M model LB FF LK cr A n K RI Hhalt HMI H10 ltac:(clear - Hn; change (2 ^ 27) with 134217728 in Hn; change (2 ^ 34) with 17179869184; lia) ACR H4 Hret AST K0
           (fun R' M' model' A' u _ => POST R' M' model' A' u)).
Qed.
End Wrap.
