(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SysStepA MmStep AImages AImageFacts LazyModel ImplRzA NodesA_mm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition a_named_fd := 0x67fc8.
Definition a_iserror := 0x65bfc.
Definition a_mmap_named := 0x673f8.
Definition a_mmap_fixed_impl := 0x6f8dc.
Definition a_mmap_fixed_spin := 0x6f9a0.

(* [comment removed for export] *)
Definition GOT_PAGESIZE := 0xa4990.   (* [comment removed for export] *)
Definition GOT_CFLAGS := 0xa49a0.     (* [comment removed for export] *)
Definition GOT_PAIR := 0xa49f0.       (* [comment removed for export] *)
Definition V_PAGESIZE := 0x13d620.
Definition V_CFLAGS := 0x13f6a8.
Definition V_MMAP_LIMIT := 0x13f738.   (* [comment removed for export] *)
Definition V_DPM := 0x13f7ac.          (* [comment removed for export] *)
Definition V_ABORTFLAG := 0x13f69c.

Definition statics (m : mem) : Prop :=
  rw_cells asegs m GOT_PAGESIZE [C8 (Z_to_bv 64 V_PAGESIZE)]
  /\ rw_cells asegs m GOT_CFLAGS [C8 (Z_to_bv 64 V_CFLAGS)]
  /\ rw_cells asegs m GOT_PAIR [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 V_ABORTFLAG)]
  /\ rw_cells asegs m V_PAGESIZE [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m V_MMAP_LIMIT [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m V_DPM [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m V_ABORTFLAG [C4 (Z_to_bv 64 0)].

End RC__1.
Ltac open_statics STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in
  let V1 := fresh "V1" in let V2 := fresh "V2" in let V3 := fresh "V3" in let V4 := fresh "V4" in
  destruct STA as (G1 & G2 & G3 & V1 & V2 & V3 & V4);
  unfold GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG in G1, G2, G3, V1, V2, V3, V4.

Ltac close_statics :=
  unfold statics, GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG;
  repeat match goal with |- _ /\ _ => split end; assumption.

Local Ltac from_lit_add :=
  repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] => is_Zlit a; is_Zlit b;
    let v := eval vm_compute in (a + b) in change (Z_to_bv 64 (a + b)) with (Z_to_bv 64 v) end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma mmap_len_alignedA : forall len, len mod 4096 = 0 -> mmap_len len = len.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Definition land_m4096A := 18446744073709547520.
Lemma land_m4096_aligned : forall x, 0 <= x < 2^64 -> x mod 4096 = 0 -> Z.land x 18446744073709547520 = x.
Proof.
  intros x Hx Hm.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  assert (D : forall y a b, Z.land y (Z.ldiff a b) = Z.ldiff (Z.land y a) b).
  { intros. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit y n), (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite D. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.
Lemma land_m4096_up : forall x, 0 <= x -> x + 4096 < 2^64 -> x mod 4096 = 0 -> Z.land (x + 4095) 18446744073709547520 = x.
Proof.
  intros x Hx Hb Hm.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  assert (D : forall y a b, Z.land y (Z.ldiff a b) = Z.ldiff (Z.land y a) b).
  { intros. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit y n), (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite D. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. Z.div_mod_to_equations. lia.
Qed.

Section X.
Variable P : acc -> Prop.
Hypothesis PDATA : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition named_fd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a3 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ statics m'.

Lemma named_fd_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 272 -> mem_inv asegs m ->
  statics m -> bv_unsigned a0 <> 0 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  evtA asegs P (named_fd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a3 a4 a5 a6 a7 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 a_named_fd) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LOC LO MI STA A0 PSTK. unfold a_named_fd.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  open_statics STA.
  assert (MU : munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 272%nat ST.
  do 8 stepA.                                  (* [comment removed for export] *)
  stepA. stepA.                                (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. apply A0. rewrite <- (Z_to_bv_lit_self a0). rewrite K0. reflexivity. }
  stepA.                                       (* [comment removed for export] *)
  do 2 stepA.                                  (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  zstepA. if_true.                             (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  do 8 stepA.                                  (* [comment removed for export] *)
  stepA.                                       (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finishA. close_statics.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_err (r : word) : bool := (18446744073709547520 <? bv_unsigned r).

Definition iserror0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (r : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.b2z (is_err r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.   (* [comment removed for export] *)

Lemma iserror0_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  mem_inv asegs m -> a1 = Z_to_bv 64 0 ->
  evtA asegs P (iserror0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a4 a5 a6 a7 F fc m a0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 a_iserror) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI ->. unfold a_iserror.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  zstepA. zstepA.                              (* [comment removed for export] *)
  zstepA. if_cases K; zify_cond K.             (* [comment removed for export] *)
  - zstepA. zstepA. unfold iserror0_post, is_err. finishA.
  - zstepA. if_true.                           (* [comment removed for export] *)
    zstepA. zstepA. unfold iserror0_post, is_err. finishA.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MAP_FIXED_NORESERVE_RW : Z := 16434.  (* [comment removed for export] *)

Definition zshape (A L : Z) (r : word) (u : bool) : resp :=
  if u then mkEffectU r [] [(Z_to_bv 64 A, Z_to_bv 64 (mmap_len L))] [] [] [] else mkEffectU r [] [] [] [] [].

Definition mmap_named_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (lo : Z) (m : mem) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (A, A + mmap_len L)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ statics m'
    /\ (u = true -> rw_cells asegs m' A [CB (Z.to_nat (mmap_len L)) (repeat (Z_to_bv 8 0) (Z.to_nat (mmap_len L)))])
    /\ R a r u.   (* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iserrorp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a4 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (m : mem) (r : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.b2z (is_err r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(B, B + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ exists v, rw_cells asegs m' B [C4 v].

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mfi_W (sp : word) (A L : Z) : list ivl := [(bv_unsigned sp - 368, bv_unsigned sp); (A, A + mmap_len L)].

Definition mmap_fixed_impl_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (lo : Z) (m : mem) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) (R' : bvmap 5 word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = (if is_err r
           then MS R' F (Z_to_bv 64 a_mmap_fixed_spin) fc None m' (seg_rom asegs)       (* [comment removed for export] *)
           else MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom asegs))                             (* [comment removed for export] *)
    /\ munch (mfi_W sp A L) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ statics m'
    /\ (u = true -> rw_cells asegs m' A [CB (Z.to_nat (mmap_len L)) (repeat (Z_to_bv 8 0) (Z.to_nat (mmap_len L)))])
    /\ R a r u.

(* [comment removed for export] *)
Ltac mfi_after_call rr :=
  do 2 stepA;                                   (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  zstepA; zstepA;                               (* [comment removed for export] *)
  zstepA; let K := fresh "K" in if_cases K; zify_cond K.   (* [comment removed for export] *)
Ltac mfi_noerr rr :=
  zstepA;                                       (* [comment removed for export] *)
  replace (18446744073709547520 <? bv_unsigned rr) with false
    by (first [apply (proj2 (Z.ltb_ge _ _)) | symmetry; apply (proj2 (Z.ltb_ge _ _))]; lia);
  cbn [Z.b2z];
  stepA;                                        (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  zstepA; if_true.                              (* [comment removed for export] *)
Ltac mfi_err rr :=
  zstepA; let K1 := fresh "K" in if_cases K1; zify_cond K1; [exfalso; lia|];   (* [comment removed for export] *)
  zstepA; zstepA;                               (* [comment removed for export] *)
  zstepA;                                       (* [comment removed for export] *)
  replace (18446744073709547520 <? bv_unsigned rr) with true
    by (first [apply (proj2 (Z.ltb_lt _ _)) | symmetry; apply (proj2 (Z.ltb_lt _ _))]; lia);
  cbn [Z.b2z];
  stepA; stepA;                                 (* [comment removed for export] *)
  zstepA; if_false.                             (* [comment removed for export] *)
Ltac mfi_grant_tail FR ST sp :=
  stepA; stepA;                                 (* [comment removed for export] *)
  do 2 stepA;                                   (* [comment removed for export] *)
  zstepA;                                       (* [comment removed for export] *)
  zstepA; if_true;                              (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  zstepA;                                       (* [comment removed for export] *)
  do 6 stepA;                                   (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
Ltac mfi_finish_common :=
  split; [ eapply munch_weaken; [|eassumption]; intros y; cbn; lia |];
  split; [assumption|]; split; [assumption|]; split; [assumption|];
  split; [close_statics|];
  split; [ first [intros _; assumption | intros; discriminate] | assumption ].
Ltac mfi_finish_ret rr u :=
  lazymatch goal with |- evtA _ _ _ (MS ?R ?F ?pc ?fc _ ?m _) =>
    apply evtA_done; unfold mmap_fixed_impl_post; exists rr, u, R; do 14 eexists; exists m end;
  split; [ unfold is_err; replace (18446744073709547520 <? bv_unsigned rr) with false
             by (first [apply (proj2 (Z.ltb_ge _ _)) | symmetry; apply (proj2 (Z.ltb_ge _ _))]; lia); reflexivity |];
  mfi_finish_common.
Ltac mfi_finish_spin rr u :=
  lazymatch goal with |- evtA _ _ _ (MS ?R ?F ?pc ?fc _ ?m _) =>
    apply evtA_done; unfold mmap_fixed_impl_post; exists rr, u, R; do 14 (exists rr); exists m end;
  split; [ unfold is_err, a_mmap_fixed_spin; replace (18446744073709547520 <? bv_unsigned rr) with true
             by (first [apply (proj2 (Z.ltb_lt _ _)) | symmetry; apply (proj2 (Z.ltb_lt _ _))]; lia); reflexivity |];
  mfi_finish_common.
Ltac mfi_errno_tail FR ST sp :=
  do 2 stepA;                                   (* [comment removed for export] *)
  zstepA; if_false;                             (* [comment removed for export] *)
  do 2 stepA;                                   (* [comment removed for export] *)
  zstepA;                                       (* [comment removed for export] *)
  zstepA; if_false;                             (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).

(* [comment removed for export] *)


End X.
End RC__2.
