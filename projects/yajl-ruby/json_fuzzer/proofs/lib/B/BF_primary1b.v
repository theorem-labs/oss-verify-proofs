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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit BF_unwind.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanClassSwar.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

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
Lemma fsx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. aceil.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap. change (bv_swrap 32 ?z) with ((z + 2^31) mod 2^32 - 2^31).
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma fzx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. aceil. intros. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section Walk.
Variable P : acc -> Prop.

(* [comment removed for export] *)
Definition ca_hit_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SB CA c x cnt alloc : Z) (maxc : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 a1 a2 a3 a4 a5 a6 a7 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SB + c * 2^32 + 16 * x)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (CA + 80 * c, CA + 80 * c + 4); (CA + 2576, CA + 2584)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (CA + 80 * c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 (Z_to_bv 64 (class_size c))]
    /\ rw_cells bsegs m' (CA + 2576) [C8 (Z_to_bv 64 (alloc + class_size c))].

Lemma ca_hit_walk_all :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SB CA sz cnt alloc : Z) (maxc : word) (ws : list word) (x : Z),
  let c := class_id sz in
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  1 <= sz <= 65536 -> 1 <= cnt <= 16 -> 0 <= SB < 2^47 -> SB mod 2^16 = 0 ->
  (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) -> CA + 2584 <= alloc_ceiling -> CA mod 8 = 0 ->   (* [comment removed for export] *)
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB)] ->                                        (* [comment removed for export] *)
  rw_cells bsegs m (CA + 80 * c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 (Z_to_bv 64 (class_size c))] ->
  u32arr bsegs m (CA + 80 * c + 16) ws -> length ws = 16%nat -> nth_error ws (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 x) -> 0 <= x < 2^32 ->
  rw_cells bsegs m (CA + 2576) [C8 (Z_to_bv 64 alloc)] ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  (forall a n, CA <= a -> a + Z.of_nat n <= CA + 2584 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (ca_hit_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo SB CA c x cnt alloc maxc)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaaf58) (Z_to_bv 64 CA) (Z_to_bv 64 sz) (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x370ac) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until x. intros c SK LOC LO SPH MI SZ CNT SBR SBM [CA0 CA1] CA2 CA8 ISB PC ARR LEN NTH XR STA PSTK PDAT PCA.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (class_id_spec sz SZ) as CSPEC. fold c in CSPEC. destruct CSPEC as (HC & CSZ1 & _).
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in *; lia)) as [_ CSZ].
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp); (CA + 80 * c, CA + 80 * c + 4); (CA + 2576, CA + 2584)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  Ltac arith := repeat match goal with
                | H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
                | H : mem_inv _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : u32arr _ _ _ _ |- _ => clear H
                | H : forall a n, _ -> _ -> P _ |- _ => clear H end; lia.
  Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit by arith; intros K; arith.
  Ltac br1 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [kill K|]).
  Ltac br2 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [| kill K]).
  carve_frame 48%nat SK.
  do 7 cstep.                     (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  replace (sz <? 1) with false by (symmetry; apply Z.ltb_ge; clear -CEILB SZ; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small sz 18446744073709551616) by (clear -CEILB SZ; lia).
  rewrite lnot_mod64 by (clear -CEILB SZ; lia). unfold Z.lnot. change (Z.pred (- sz)) with (- sz - 1) || idtac.
  zstepA. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by arith. clear -CEILB SZ. intros K0. Z.div_mod_to_equations. lia. }
  do 2 zstepA. br2.               (* [comment removed for export] *)
  zstepA. cstep.                  (* [comment removed for export] *)
  br1.                            (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
  assert (JOIN : forall (x12 x14 x15 x16 x17 x5 x6 : word),
    evtA bsegs P (ca_hit_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo SB CA c x cnt alloc maxc)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 700248) (Z_to_bv 64 CA) x12 (Z_to_bv 64 8) x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x37240) fc None mx (seg_rom bsegs))) end.
  2:{ zstepA; if_cases KB; zify_cond KB.
      - (* [comment removed for export] *)
        do 29 zstepA. lazymatch goal with |- context [Z.lxor ?e 18446744073709551615] => set (sm := e) in * end.
        do 14 zstepA. lazymatch goal with |- context [Z.shiftr ?e 56] => set (pz := e) in * end.
        do 12 zstepA.
        match goal with |- context [Z_to_bv 64 (?e + -2)] => replace (e + -2) with c by (transitivity (swar_class sz); [symmetry; apply swar_class_ok; unfold kMidSize, kMaxSize; revert KB; rewrite ?unsigned_lit by lia; intros KB; lia| subst pz sm; reflexivity]) end.
        eapply JOIN.
      - (* [comment removed for export] *)
        do 2 zstepA.                    (* [comment removed for export] *)
        replace ((sz + 31) ≫ 5) with c by (subst c; unfold class_id, kMidSize, kMinSize; replace (sz <=? 512) with true by (symmetry; apply Z.leb_le; revert KB; rewrite ?unsigned_lit by lia; intros KB; lia); rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; f_equal; lia).
        cstep.                          (* [comment removed for export] *)
        eapply JOIN. }
  intros x12 x14 x15 x16 x17 x5 x6.
  br1.                            (* [comment removed for export] *)
  zstepA. br1.                    (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  replace (CA + c * 80) with (CA + 80 * c) by (clear; lia). set (PCB := CA + 80 * c) in *.
  zstepA. rewrite fsx32_small by (clear -CEILB CNT; lia).   (* [comment removed for export] *)
  br1.                            (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  do 2 zstepA.                    (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  replace (((cnt + -1) ≪ 32 mod 18446744073709551616) ≫ 30) with (4 * (cnt - 1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by (clear -CEILB CNT; lia); clear -CEILB CNT; Z.div_mod_to_equations; lia).
  zstepA.                         (* [comment removed for export] *)
  pose proof (u32arr_read bsegs _ _ ws (cnt - 1) (Z_to_bv 64 x) (Z_to_bv 64 (PCB + 4 * (cnt - 1) + 16)) ARR NTH ltac:(clear -CEILB CNT; lia)
                ltac:(unfold wa; f_equal; clear; lia)) as RD.
  zstepA. clear RD.               (* [comment removed for export] *)
  rewrite fzx32_small by (clear -CEILB XR; lia).
  assert (AL8 : (CA + 2576) mod 8 = 0) by (clear -CEILB CA8; Z.div_mod_to_equations; lia).
  zstepA.                         (* [comment removed for export] *)
  do 5 zstepA.                    (* [comment removed for export] *)
  zstepA. cstep.                  (* [comment removed for export] *)
  do 7 cstep.                     (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  cstep.                          (* [comment removed for export] *)
  replace (x ≪ 4 + (c ≪ 32 + SB)) with (SB + c * 2^32 + 16 * x) by (rewrite !Z.shiftl_mul_pow2 by lia; clear; lia).
  subst PCB. replace (cnt + -1) with (cnt - 1) in * by (clear; lia).
  (* [comment removed for export] *)
  change 18446744073709551616 with (2^64) in *. rewrite ?ZBridge.Z_to_bv_mod64 in *.
  finishA.
Qed.
End Walk.
End RC__1.
