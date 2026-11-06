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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit BF_refill1 BF_refill1b BF_primary1b.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac cstep := stepA; try first [if_true | if_false].

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
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
Definition ic_max_count (i : Z) : Z := if i =? 31 then 16 else max_count i.
Definition ic_class_size (i : Z) : Z := if i =? 31 then 64 else class_size i.

(* [comment removed for export] *)
Definition ic_rows (m : mem) (CA : Z) (cnt mx sz : Z -> Z) : Prop :=
  forall i, 1 <= i <= 31 -> rw_cells bsegs m (CA + 80 * i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 (mx i)); C8 (Z_to_bv 64 (sz i))].

(* [comment removed for export] *)
End RC__1.
Ltac lit_of_nat :=
  repeat match goal with |- context [Z.of_nat ?k] => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section IC3.
Variable P : acc -> Prop.

Definition initcache_post_all (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (CA : Z) (cnt : Z -> Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a3 a5 a6 a7 t3 t4 t5 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x378f4) fc None m' (seg_rom bsegs)
    /\ munch (ic_W CA) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ ic_rows m' CA cnt ic_max_count ic_class_size.

Lemma initcache_walk_all :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (CA : Z) (cnt : Z -> Z),
  mem_inv bsegs m -> (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) -> CA + 2584 <= alloc_ceiling -> CA mod 8 = 0 ->
  (forall i, 0 <= cnt i < 2^32) ->
  ic_rows m CA cnt (fun _ => 0) (fun _ => 0) ->
  (forall a n, CA <= a -> a + Z.of_nat n <= CA + 2584 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (initcache_post_all ra sp gp tp s0 s1 (Z_to_bv 64 CA) a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m CA cnt)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37858) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until cnt. intros MI CA1 CA2 CA8 CNT ROWS PCA. unfold ic_rows in ROWS.
  eapply evtA_mono.
  { eapply (initcache_walk P ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m CA cnt MI CA1 CA2 CA8 CNT).
    1: exact (ROWS 1 ltac:(lia)).
    1: exact (ROWS 2 ltac:(lia)).
    1: exact (ROWS 3 ltac:(lia)).
    1: exact (ROWS 4 ltac:(lia)).
    1: exact (ROWS 5 ltac:(lia)).
    1: exact (ROWS 6 ltac:(lia)).
    1: exact (ROWS 7 ltac:(lia)).
    1: exact (ROWS 8 ltac:(lia)).
    1: exact (ROWS 9 ltac:(lia)).
    1: exact (ROWS 10 ltac:(lia)).
    1: exact (ROWS 11 ltac:(lia)).
    1: exact (ROWS 12 ltac:(lia)).
    1: exact (ROWS 13 ltac:(lia)).
    1: exact (ROWS 14 ltac:(lia)).
    1: exact (ROWS 15 ltac:(lia)).
    1: exact (ROWS 16 ltac:(lia)).
    1: exact (ROWS 17 ltac:(lia)).
    1: exact (ROWS 18 ltac:(lia)).
    1: exact (ROWS 19 ltac:(lia)).
    1: exact (ROWS 20 ltac:(lia)).
    1: exact (ROWS 21 ltac:(lia)).
    1: exact (ROWS 22 ltac:(lia)).
    1: exact (ROWS 23 ltac:(lia)).
    1: exact (ROWS 24 ltac:(lia)).
    1: exact (ROWS 25 ltac:(lia)).
    1: exact (ROWS 26 ltac:(lia)).
    1: exact (ROWS 27 ltac:(lia)).
    1: exact (ROWS 28 ltac:(lia)).
    1: exact (ROWS 29 ltac:(lia)).
    1: exact (ROWS 30 ltac:(lia)).
    1: exact (ROWS 31 ltac:(lia)).
    exact PCA. }
  cbv beta. intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & m' & -> & MU & WM & MI' & REST).
  destruct REST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & Q28 & Q29 & Q30 & Q31).
  unfold initcache_post_all. do 12 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  intros i Hi. assert (Hk : exists k, i = Z.of_nat k /\ (1 <= k <= 31)%nat) by (exists (Z.to_nat i); lia).
  destruct Hk as (k & -> & Hk). unfold ic_max_count, ic_class_size.
  destruct k as [|k]; [lia|].
  do 31 (destruct k as [|k]; [lit_of_nat; cbn [Z.eqb Pos.eqb]; assumption|]).
  exfalso; lia.
Qed.
End IC3.

(* [comment removed for export] *)
Lemma srliw_half : forall h, 1 <= h <= 8 -> bv_swrap 32 (bv_wrap 32 ((2 * h) mod 18446744073709551616) ≫ 1) = h.
Proof. aceil.
  intros h Hh. rewrite Z.mod_small by lia. rewrite bv_wrap_small by (unfold bv_modulus; lia).
  rewrite Z.shiftr_div_pow2 by lia. replace (2 * h / 2^1) with h by (Z.div_mod_to_equations; lia).
  unfold bv_swrap. rewrite bv_wrap_small by (unfold bv_modulus, bv_half_modulus, bv_modulus; lia). lia.
Qed.

Section RF.
Variable P : acc -> Prop.
Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
(* [comment removed for export] *)
Variables (lo uspR CA c INST PCB : Z) (cnt : Z -> Z).
Hypothesis HPCB : PCB = CA + 80 * c.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= uspR - 32.
Hypothesis USP : uspR + 48 <= 2^47.
Hypothesis USP8 : uspR mod 8 = 0.
Hypothesis HC : 1 <= c <= 30.
Hypothesis HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0.   (* [comment removed for export] *)
Hypothesis CNT : forall i, 0 <= cnt i < 2^32.
Hypothesis CNTc : cnt c = 0.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= uspR + 48 -> P (Z_to_bv 64 a, k).
Hypothesis PCA : forall a k, CA <= a -> a + Z.of_nat k <= CA + 2584 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition refill_at_gfa (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a5 a6 a7 t3 t4 t5 : word) (m' : mem) (j8 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x3783c) (Z_to_bv 64 (uspR + -32)) gp tp t0 t1 t2 (Z_to_bv 64 PCB) (Z_to_bv 64 (hint c))
                 (Z_to_bv 64 INST) (Z_to_bv 64 (CA + 2560)) (Z_to_bv 64 c) (Z_to_bv 64 (PCB + 16)) (Z_to_bv 64 (hint c)) a5 a6 a7
                 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 xt6)
             F (Z_to_bv 64 0x378fc) fc None m' (seg_rom bsegs)
    /\ munch ((uspR - 32, uspR) :: ic_W CA) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (uspR + -32)
    /\ rw_cells bsegs m' (uspR + -32) [CB 8 j8; C8 xs1; C8 xs0; C8 xra]
    /\ ic_rows m' CA cnt ic_max_count ic_class_size.

Lemma refill_front : forall (ii : bool) (xra xt0 xt1 xt2 xs0 xs1 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) (m : mem),
  mem_inv bsegs m -> stk bsegs m lo uspR ->
  ic_rows m CA cnt (fun i => if ii then ic_max_count i else 0) (fun i => if ii then ic_class_size i else 0) ->
  evtA bsegs P (refill_at_gfa xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 m)
    (MS (mkR xra (Z_to_bv 64 uspR) gp tp xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 CA) (Z_to_bv 64 PCB) (Z_to_bv 64 INST) (Z_to_bv 64 c) xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x377fc) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until m. intros MI SK ROWS.
  pose proof LOC as LOCu. aceil.
  pose proof HCA as (CA1 & CA2 & CA8). aceil.
  pose proof (hint_range c HC) as HR.
  assert (MU : munch [(uspR - 32, uspR)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  pose proof (ROWS c ltac:(lia)) as PC. cbv beta in PC. rewrite <- HPCB, CNTc in PC.
  carve_frame 32%nat SK.
  do 4 zstepA.          (* [comment removed for export] *)
  do 2 zstepA.          (* [comment removed for export] *)
  destruct ii.
  - (* [comment removed for export] *)
    unfold ic_max_count, ic_class_size in PC. replace (c =? 31) with false in PC by (symmetry; apply Z.eqb_neq; lia).
    zstepA. rewrite fsx32_small by (unfold max_count; lia).   (* [comment removed for export] *)
    zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by (unfold max_count; lia). unfold max_count. intros K0. lia. }
    do 8 zstepA.        (* [comment removed for export] *)
    unfold max_count. rewrite srliw_half by lia.
    apply evtA_done. unfold refill_at_gfa. do 11 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
    intros i Hi. eapply rw_cells_transport; [exact (ROWS i Hi)| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. clear -CEILB LOCu LO CA2 Hi. lia.
  - (* [comment removed for export] *)
    zstepA. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).    (* [comment removed for export] *)
    cstep.                                                       (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ROWS0 : ic_rows mx CA cnt (fun _ => 0) (fun _ => 0))
        by (intros i Hi; eapply rw_cells_transport; [exact (ROWS i Hi)| exact MU| exact WM|]; cbn [disjoint_from cells_size csize Nat.add Nat.mul]; clear -CEILB LOCu LO CA2 Hi; lia) end.
    eapply evtA_cut.
    { eapply initcache_walk_all; [exact MI| exact CA1| aceil; lia| exact CA8| exact CNT| exact ROWS0| exact PCA]. }
    cbv beta. clear PC. intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & m' & -> & MU' & WM' & MI' & ROWS').
    assert (FR' : rw_cells bsegs m' (uspR + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 xs1; C8 xs0; C8 xra]).
    { eapply rw_cells_transport; [exact FR| exact MU'| exact WM'|]. unfold ic_W. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. lit_of_nat. clear -CEILB LOCu LO CA2. lia. }
    assert (SK' : stk bsegs m' lo (uspR + -32)).
    { eapply stk_transport_disjoint; [exact SK| exact MU'| exact WM'|]. unfold ic_W. cbn [disjoint_from]. clear -CEILB LOCu LO CA2. lia. }
    assert (MU2 : munch ((uspR - 32, uspR) :: ic_W CA) m m').
    { eapply munch_trans; [| eapply munch_weaken; [| exact MU']]. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
      unfold sub_fp, ic_W. cbn [outside]. clear. intros x Hx. tauto. }
    assert (WM2 : wmono bsegs m m') by (eapply wmono_trans; [exact WM| exact WM']).
    clear MU WM FR SK MU' WM' MI. unfold ic_W in MU2.
    pose proof (ROWS' c ltac:(lia)) as PC. rewrite <- HPCB in PC.
    unfold ic_max_count, ic_class_size in PC. replace (c =? 31) with false in PC by (symmetry; apply Z.eqb_neq; lia).
    zstepA. rewrite fsx32_small by (unfold max_count; lia).   (* [comment removed for export] *)
    cstep.                                                    (* [comment removed for export] *)
    do 8 zstepA.        (* [comment removed for export] *)
    unfold max_count. rewrite srliw_half by lia.
    apply evtA_done. unfold refill_at_gfa. do 11 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
Qed.

(* [comment removed for export] *)
Definition refill_ret (rv : Z) (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 : word) (m : mem) (newcnt mx sz : Z)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 : word) (m' : mem),
    ms' = MS (mkR xra (Z_to_bv 64 uspR) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 xt4 xt5 xt6)
             F (ret_pc xra) fc None m' (seg_rom bsegs)
    /\ munch [(uspR - 32, uspR); (PCB, PCB + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo uspR
    /\ rw_cells bsegs m' PCB [C4 (Z_to_bv 64 newcnt); C4 (Z_to_bv 64 mx); C8 (Z_to_bv 64 sz)].

Lemma refill_back : forall (rv : Z) (xra xs0 xs1 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
    (m : mem) (j8 : list byte) (oldcnt mx sz : Z),
  mem_inv bsegs m -> stk bsegs m lo (uspR + -32) ->
  rw_cells bsegs m (uspR + -32) [CB 8 j8; C8 xs1; C8 xs0; C8 xra] ->
  rw_cells bsegs m PCB [C4 (Z_to_bv 64 oldcnt); C4 (Z_to_bv 64 mx); C8 (Z_to_bv 64 sz)] ->
  rv = 0 \/ rv = 1 ->
  evtA bsegs P (refill_ret rv xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 m (if rv =? 1 then hint c else oldcnt) mx sz)
    (MS (mkR (Z_to_bv 64 0x3783c) (Z_to_bv 64 (uspR + -32)) gp tp xt0 xt1 xt2 (Z_to_bv 64 PCB) (Z_to_bv 64 (hint c)) (Z_to_bv 64 rv) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x3783c) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until sz. intros MI SK FR PC RV.
  pose proof LOC as LOCu. aceil.
  pose proof HCA as (CA1 & CA2 & CA8). aceil.
  pose proof (hint_range c HC) as HR.
  assert (MU : munch [(uspR - 32, uspR); (PCB, PCB + 4)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (PCB4 : PCB mod 4 = 0) by (rewrite HPCB; clear -CEILB CA8; Z.div_mod_to_equations; lia).
  assert (PPCB : forall a k, PCB <= a -> a + Z.of_nat k <= PCB + 80 -> P (Z_to_bv 64 a, k)) by (intros a k H1 H2; apply PCA; rewrite HPCB in H1, H2; lia).
  destruct RV as [-> | ->].
  - cstep.              (* [comment removed for export] *)
    do 5 zstepA.        (* [comment removed for export] *)
    release_frame FR SK uspR. finishA.
  - cstep.              (* [comment removed for export] *)
    zstepA.             (* [comment removed for export] *)
    do 5 zstepA.
    release_frame FR SK uspR. finishA.
Qed.
End RF.
End RC__2.
