(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA MmStep AImages AImageFacts NodesA_madv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_lkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition flush_statics (m : mem) : Prop :=
     rw_cells bsegs m 0xa55a0 [C8 (Z_to_bv 64 0xae5b8)] /\ rw_cells bsegs m 0xae5b8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0xa55a8 [C8 (Z_to_bv 64 0xaf2a8)] /\ rw_cells bsegs m 0xaf2a8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xa55b0 [C8 (Z_to_bv 64 0xaf2b0)] /\ rw_cells bsegs m 0xaf2b0 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xa55b8 [C8 (Z_to_bv 64 0xaf2a0)] /\ rw_cells bsegs m 0xaf2a0 [C8 (Z_to_bv 64 0x7fffffffffff)]
  /\ rw_cells bsegs m 0xa5580 [C8 (Z_to_bv 64 0x13e060)] /\ rw_cells bsegs m 0x13e060 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0xa55e0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x1400dc)].

Section FLUSH.
Variable P : acc -> Prop.
Hypothesis PDAT : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
Lemma m2s_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (Q : machine_state -> Prop) (m : mem) (p : Z),
  mem_inv bsegs m -> flush_statics m ->
  ((0 <= p /\ p <= 0x7fff7fff) \/ (0x10007fff8000 <= p /\ p <= 0x7fffffffffff)) ->
  (forall (a1' a2' a3' a4' a5' a6' a7' t0' : word),
     evtA bsegs P Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (0x7fff8000 + Z.shiftr p 3)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x53bfc) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until p. intros MI FS HP0 CONT.
  destruct FS as (G1 & V1 & G2 & V2 & G3 & V3 & G4 & V4 & G5 & V5 & G6).
  (* [comment removed for export] *)
  destruct HP0 as [HPL|HP].
  { (* [comment removed for export] *)
    zstepA. zstepA. zstepA. (* [comment removed for export] *)
    zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
    match goal with |- context [Z_to_bv 64 (Z.land ?x 2147450879)] => replace (Z.land x 2147450879) with 2147450879 by (vm_compute; reflexivity) end.
    zstepA. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }   (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    apply CONT. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (Z.land ?x 2147450879)] => replace (Z.land x 2147450879) with 2147450879 by (vm_compute; reflexivity) end.
  zstepA. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  do 4 zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. rewrite ?unsigned_lit by lia. cbn. lia. }  (* [comment removed for export] *)
  do 3 zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  zstepA. if_cases K4; zify_cond K4. { exfalso. revert K4. cbn. lia. }   (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  apply CONT.
Qed.

(* [comment removed for export] *)
Lemma land_m4096_l2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  assert (D : forall y a b, Z.land y (Z.ldiff a b) = Z.ldiff (Z.land y a) b).
  { intros. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit y n), (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite D. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
Definition rmp_pb (b : Z) : Z := b + 4095 - (b + 4095) mod 4096.
Definition rmp_pe (e : Z) : Z := e - e mod 4096.

Lemma rmp_pb_facts : forall b, 0 <= b -> b <= rmp_pb b < b + 4096 /\ rmp_pb b mod 4096 = 0.
Proof. intros b Hb. unfold rmp_pb. Z.div_mod_to_equations. lia. Qed.
Lemma rmp_pe_facts : forall e, 0 <= e -> e - 4096 < rmp_pe e <= e /\ rmp_pe e mod 4096 = 0.
Proof. intros e He. unfold rmp_pe. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma rmp_walk_none :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (Q : machine_state -> Prop) (m : mem) (lo b e : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> flush_statics m -> 0 <= b <= e -> e < 2^47 ->
  rmp_pe e <= rmp_pb b ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall m' (a0' a1' a2' a3' : word),
     mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> wmono bsegs m m' -> munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x6ee28) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until e. intros SK LOC LO SPH MI FS HBE HE HEMP PSTK CONT.
  destruct FS as (G1 & V1 & G2 & V2 & G3 & V3 & G4 & V4 & G5 & V5 & G6).
  aceil. unfold rmp_pb, rmp_pe in HEMP.
  assert (MU : munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 32%nat SK.
  do 5 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  cstep.  (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  cstep.  (* [comment removed for export] *)
  do 5 zstepA. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    do 5 zstepA. release_frame FR SK (bv_unsigned sp). zstepA.
    eapply CONT; [exact MI| exact SK| exact WM| exact MU].
  - exfalso. revert K1. rewrite ?land_m4096_l2 by (clear -HBE HE; lia).
    rewrite ?unsigned_lit by (clear -HBE HE; Z.div_mod_to_equations; lia).
    replace (4096 + b + -1) with (b + 4095) by (clear; lia) || idtac.
    clear -HEMP. lia.
Qed.

(* [comment removed for export] *)
Lemma rmp_walk_madv :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (Q : machine_state -> Prop) (m : mem) (lo b e : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> flush_statics m -> 0x603000 <= b -> b <= e -> e <= lo ->
  rmp_pb b < rmp_pe e ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall m' (a1' a2' a3' a7' : word),
     mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> wmono bsegs m m' ->
     munch [(bv_unsigned sp - 32, bv_unsigned sp); (rmp_pb b, rmp_pe e)] m m' ->
     rw_cells bsegs m' (rmp_pb b) [CB (Z.to_nat (rmp_pe e - rmp_pb b)) (repeat (Z_to_bv 8 0) (Z.to_nat (rmp_pe e - rmp_pb b)))] ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P (fun ms1 => at_madvise (rmp_pb b) (rmp_pe e - rmp_pb b) ms1
                           /\ evtA bsegs P Q (nret ms1 (madv_eff (rmp_pb b) (rmp_pe e - rmp_pb b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x6ee28) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until e. intros SK LOC LO SPH MI FS HB HBE HE HNE PSTK CONT.
  destruct FS as (G1 & V1 & G2 & V2 & G3 & V3 & G4 & V4 & G5 & V5 & G6).
  pose proof LOC as LOC0. aceil.
  pose proof (rmp_pb_facts b ltac:(clear -HB; lia)) as (PB1 & PB2).
  pose proof (rmp_pe_facts e ltac:(clear -HB HBE; lia)) as (PE1 & PE2).
  set (pb := rmp_pb b) in *. set (pe := rmp_pe e) in *.
  assert (MU : munch [(bv_unsigned sp - 32, bv_unsigned sp); (pb, pe)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 32%nat SK.
  do 5 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  cstep.  (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  cstep.  (* [comment removed for export] *)
  do 5 zstepA. (* [comment removed for export] *)
  rewrite ?land_m4096_l2 by (clear -CEILB HB HBE HE LOC0 LO SPH; lia).
  change (b + 4095 - (b + 4095) mod 4096) with pb. change (e - e mod 4096) with pe.
  zstepA. if_cases K1; zify_cond K1.
  { exfalso. revert K1. rewrite ?unsigned_lit by (clear -CEILB HB HBE HE LOC0 LO SPH PB1 PE1; lia). clear -HNE. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  do 5 zstepA. release_frame FR SK (bv_unsigned sp).
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  cstep.  (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  cstep.  (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  step_ecallA.
  split. { unfold at_madvise. at_node_red. split_spine; reflexivity. }
  assert (ROF : forall xw : word, (pb <= bv_unsigned xw < pb + (pe - pb))%Z -> ro_addr bsegs xw = false)
    by (intros xw Hxw; apply both_ro_addr_false; clear -CEILB Hxw HB PB1; lia).
  unfold madv_eff. sys_nret.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply CONT; [exact MI| exact SK| exact WM| exact MU| exact ZNEW].
Qed.

(* [comment removed for export] *)
Definition flush_sb (p : Z) : Z := 0x7fff8000 + Z.shiftr p 3.
Definition flush_se (p n : Z) : Z := 0x7fff8000 + Z.shiftr (p + n) 3.

(* [comment removed for export] *)
Lemma flush_pre :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (Q : machine_state -> Prop) (m : mem) (lo p n : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> flush_statics m -> 0 <= p -> 0 <= n -> p + n <= 0x7fffffffffff ->
  (p + n <= 0x7fff7fff \/ 0x10007fff8000 <= p) ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall m' (a2' a3' a4' a5' a6' a7' t0' : word),
     mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> wmono bsegs m m' -> munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' ->
     flush_statics m' ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (flush_sb p)) (Z_to_bv 64 (flush_se p n)) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x6ee28) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x53bb0) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until n. intros SK LOC LO SPH MI FS HP HN HPN HPL PSTK CONT.
  destruct FS as (G1 & V1 & G2 & V2 & G3 & V3 & G4 & V4 & G5 & V5 & G6).
  aceil.
  assert (MU : munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 32%nat SK.
  do 5 zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (conj G1 (conj V1 (conj G2 (conj V2 (conj G3 (conj V3 (conj G4 (conj V4 (conj G5 (conj V5 G6))))))))) : flush_statics mx) as FS end.
  eapply m2s_walk; [exact MI| exact FS| destruct HPL as [HPL|HPL]; [left|right]; lia|]. intros a1' a2' a3' a4' a5' a6' a7' t0'. ret_pc_lit.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  replace (n + p) with (p + n) by lia.
  zstepA. (* [comment removed for export] *)
  eapply m2s_walk; [exact MI| exact FS| destruct HPL as [HPL|HPL]; [left|right]; lia|]. intros a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0''. ret_pc_lit.
  zstepA. zstepA. (* [comment removed for export] *)
  do 5 zstepA. (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  zstepA. (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (FS' : flush_statics mx) by (exact (conj G1 (conj V1 (conj G2 (conj V2 (conj G3 (conj V3 (conj G4 (conj V4 (conj G5 (conj V5 G6))))))))))) end.
  eapply CONT; [exact MI| exact SK| exact WM| exact MU| exact FS'].
Qed.

Lemma flush_range : forall p n, 0 <= p -> 0 <= n -> p + n <= 0x7fffffffffff ->
  0x7fff8000 <= flush_sb p <= flush_se p n /\ flush_se p n < 0x10007fff8000.
Proof.
  intros p n HP HN HPN. unfold flush_sb, flush_se.
  assert (S1 : 0 <= Z.shiftr p 3) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  assert (S2 : Z.shiftr p 3 <= Z.shiftr (p + n) 3) by (rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
  assert (S3 : Z.shiftr (p + n) 3 < 2^44) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* [comment removed for export] *)
Lemma flush_walk_none :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (Q : machine_state -> Prop) (m : mem) (lo p n : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> flush_statics m -> 0 <= p -> 0 <= n -> p + n <= 0x7fffffffffff ->
  (p + n <= 0x7fff7fff \/ 0x10007fff8000 <= p) ->
  rmp_pe (flush_se p n) <= rmp_pb (flush_sb p) ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall m' (a0' a1' a2' a3' a4' a5' a6' a7' t0' : word),
     mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> wmono bsegs m m' -> munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x53bb0) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until n. intros SK LOC LO SPH MI FS HP HN HPN HPL HEMP PSTK CONT.
  pose proof (flush_range p n HP HN HPN) as (R1 & R2).
  eapply flush_pre; [exact SK| exact LOC| exact LO| exact SPH| exact MI| exact FS| exact HP| exact HN| exact HPN| exact HPL| exact PSTK|].
  intros m1 a2' a3' a4' a5' a6' a7' t0' MI1 SK1 WM1 MU1 FS1.
  eapply rmp_walk_none; [exact SK1| exact LOC| exact LO| exact SPH| exact MI1| exact FS1| clear -R1; lia| clear -R2; lia| exact HEMP| exact PSTK|].
  intros m' a0' a1x a2x a3x MI' SK' WM' MU'.
  eapply CONT; [exact MI'| exact SK'| eapply wmono_trans; [exact WM1| exact WM']|].
  eapply munch_trans; [exact MU1| exact MU'].
Qed.

(* [comment removed for export] *)
Lemma flush_walk_madv :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (Q : machine_state -> Prop) (m : mem) (lo p n : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> flush_statics m -> 0 <= p -> 0 <= n -> p + n <= 0x7fffffffffff ->
  (p + n <= 0x7fff7fff \/ 0x10007fff8000 <= p) ->
  rmp_pb (flush_sb p) < rmp_pe (flush_se p n) ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall m' (a1' a2' a3' a4' a5' a6' a7' t0' : word),
     mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> wmono bsegs m m' ->
     munch [(bv_unsigned sp - 32, bv_unsigned sp); (rmp_pb (flush_sb p), rmp_pe (flush_se p n))] m m' ->
     rw_cells bsegs m' (rmp_pb (flush_sb p)) [CB (Z.to_nat (rmp_pe (flush_se p n) - rmp_pb (flush_sb p)))
                                                 (repeat (Z_to_bv 8 0) (Z.to_nat (rmp_pe (flush_se p n) - rmp_pb (flush_sb p))))] ->
     evtA bsegs P Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P (fun ms1 => at_madvise (rmp_pb (flush_sb p)) (rmp_pe (flush_se p n) - rmp_pb (flush_sb p)) ms1
                           /\ evtA bsegs P Q (nret ms1 (madv_eff (rmp_pb (flush_sb p)) (rmp_pe (flush_se p n) - rmp_pb (flush_sb p)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x53bb0) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until n. intros SK LOC LO SPH MI FS HP HN HPN HPL HNE PSTK CONT.
  pose proof (flush_range p n HP HN HPN) as (R1 & R2).
  pose proof LOC as LOC0. aceil.
  eapply flush_pre; [exact SK| exact LOC0| exact LO| exact SPH| exact MI| exact FS| exact HP| exact HN| exact HPN| exact HPL| exact PSTK|].
  intros m1 a2' a3' a4' a5' a6' a7' t0' MI1 SK1 WM1 MU1 FS1.
  eapply rmp_walk_madv; [exact SK1| exact LOC0| exact LO| exact SPH| exact MI1| exact FS1| clear -R1; lia| clear -R1; lia
                        | clear -CEILB R2 LOC0; lia| exact HNE| exact PSTK|].
  intros m' a1x a2x a3x a7x MI' SK' WM' MU' ZN.
  eapply CONT; [exact MI'| exact SK'| eapply wmono_trans; [exact WM1| exact WM']| | exact ZN].
  eapply munch_trans; [| exact MU']. eapply munch_weaken; [| exact MU1]. intros y Hy. cbn in Hy |- *. clear -Hy. tauto.
Qed.
End FLUSH.
End RC__1.
