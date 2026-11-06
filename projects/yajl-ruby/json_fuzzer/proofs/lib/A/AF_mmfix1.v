(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SysStepA MmStep AImages AImageFacts LazyModel NodesA ImplRzA NodesA_mm StepA2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_mmfix0.
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
Definition a_mmap_fixed_rw := 0x67934.
Definition a_report_mmap_spin := 0x61498.
Definition MAP_FIXED_RW : Z := 50.  (* [comment removed for export] *)
Definition ENOMEMw : Z := 2^64 - 12.


Definition a_mmap_fixed_die := 0x67a5c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. aceil. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31)%Z. lia. Qed.
Lemma swrap32_neg_errno : forall u, 2^64 - 4096 < u < 2^64 -> bv_swrap 32 (0 - u) = 2^64 - u.
Proof. aceil.
  intros u Hu. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31)%Z. change (bv_modulus 32) with (2^32)%Z.
  replace (0 - u + 2^31) with ((2^64 - u + 2^31) + (- 2^32) * 2^32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.
Lemma errno_load : forall r : word, is_err r = true ->
  sx32 (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned r))) = Z_to_bv 64 (2^64 - bv_unsigned r).
Proof. aceil.
  intros r Hr. unfold is_err in Hr. apply Z.ltb_lt in Hr.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  rewrite swrap32_neg_errno by lia.
  unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  rewrite (Z.mod_small (2^64 - bv_unsigned r)) by lia. rewrite swrap32_small by lia. reflexivity.
Qed.

Section X1.
Variable P : acc -> Prop.
Hypothesis PDATA : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

Definition mfr_W (sp : word) (A L : Z) : list ivl := [(bv_unsigned sp - 368, bv_unsigned sp); (A, A + mmap_len L)].

(* [comment removed for export] *)
Definition mfr_ret (r : word) (tol : Z) : bool := negb (is_err r) || ((tol =? 1) && (bv_unsigned r =? ENOMEMw)).
Lemma mfr_ret_noerr : forall r tol, bv_unsigned r < 18446744073709547521 -> mfr_ret r tol = true.
Proof. aceil. intros r tol H. unfold mfr_ret, is_err. replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma mfr_ret_tol0 : forall r, 18446744073709547521 <= bv_unsigned r -> mfr_ret r 0 = false.
Proof. aceil. intros r H. unfold mfr_ret, is_err. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma mfr_ret_enomem : forall r, bv_unsigned r = ENOMEMw -> mfr_ret r 1 = true.
Proof. aceil. intros r H. unfold mfr_ret, is_err. rewrite H. vm_compute. reflexivity. Qed.
Lemma mfr_ret_other : forall r, 18446744073709547521 <= bv_unsigned r -> bv_unsigned r <> ENOMEMw -> mfr_ret r 1 = false.
Proof. aceil.
  intros r H1 H2. unfold mfr_ret, is_err. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb orb andb Z.eqb Pos.eqb]. apply Z.eqb_neq. exact H2.
Qed.

Definition mmap_fixed_gen_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L tol : Z) (lo : Z) (m : mem) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) (ra' sp' s4' e4 : word) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = (if mfr_ret r tol
           then MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (if is_err r then Z_to_bv 64 0 else r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom asegs)      (* [comment removed for export] *)
           else MS (mkR ra' sp' gp tp t0 t1 t2 (Z_to_bv 64 (mmap_len L)) (Z_to_bv 64 tol) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 A) r s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 a_mmap_fixed_die) fc None m' (seg_rom asegs))  (* [comment removed for export] *)
    /\ munch (mfr_W sp A L) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (if mfr_ret r tol then bv_unsigned sp else bv_unsigned sp - 96) /\ statics m'
    /\ (u = true -> rw_cells asegs m' A [CB (Z.to_nat (mmap_len L)) (repeat (Z_to_bv 8 0) (Z.to_nat (mmap_len L)))])
    /\ (mfr_ret r tol = false -> bv_unsigned sp' = bv_unsigned sp - 96 /\ sx32 e4 = Z_to_bv 64 (2^64 - bv_unsigned r) /\
          exists junk, rw_cells asegs m' (bv_unsigned sp - 96)
                         [C4 (Z_to_bv 64 50); CB 40 junk; C4 e4; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ R a r u.

Lemma mmap_fixed_gen_specA : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L tol : Z) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = zshape A L r u) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 368 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m -> statics m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 tol -> (tol = 0 \/ tol = 1) ->
  A mod 4096 = 0 -> L mod 4096 = 0 ->
  a_image_end <= A -> 0 < L -> A + mmap_len L <= lo ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  implA asegs (at_nodeA asegs) P (enode (NMmap A L 3 MAP_FIXED_RW) dec)
       (epost (mmap_fixed_gen_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L tol lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 a_mmap_fixed_rw) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until lo. intros DEC ST LOC LO SPH MI STA -> -> -> TOL AA LA AI L0 AL PSTK. unfold a_mmap_fixed_rw, MAP_FIXED_RW.
  unfold a_image_end in AI. pose proof LOC as LOC'. aceil.
  pose proof (mmap_len_bound L L0) as ML. pose proof (mmap_len_alignedA L LA) as MLA.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (munch_refl (mfr_W sp A L) m) as MU. unfold mfr_W in MU.
  pose proof (wmono_refl asegs m) as WM.
  open_statics STA.
  apply implA_enode.
  carve_frame 96%nat ST.
  do 7 stepA.                                   (* [comment removed for export] *)
  do 3 stepA.                                   (* [comment removed for export] *)
  do 2 stepA.                                   (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA. if_true.                              (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA.               (* [comment removed for export] *)
  rewrite land_m4096_up by lia.
  zstepA. if_true.                              (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  rewrite land_m4096_aligned by lia.
  zstepA. zstepA.                               (* [comment removed for export] *)
  do 3 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (Z.eq_dec (bv_unsigned a3) 0) as [NAME|NAME];
    [ assert (NM0 : a3 = Z_to_bv 64 0) by (apply bv_eq; rewrite NAME; reflexivity);
      call_spA (named_fd0_specA P); [exact ST| exact LOC'| lia| exact MI| close_statics| exact NM0| intros; apply PSTK; lia|]
    | call_spA (named_fd_specA P PDATA); [exact ST| exact LOC'| lia| exact MI| close_statics| exact NAME| intros; apply PSTK; lia|] ].
  all: rename PC into ST; clear G1 G2 G3 V1 V2 V3 V4; lazymatch goal with H : statics _ |- _ => rename H into STA end.
  all: ret_pc_lit.
  all: zstepA.                                  (* [comment removed for export] *)
  all: do 5 stepA.                              (* [comment removed for export] *)
  all: stepA.                                   (* [comment removed for export] *)
  all: stepA.                                   (* [comment removed for export] *)
  all: step_ecallA.
  all: split; [at_nodeA_solve|].
  all: intros rsp ans Hdec; destruct (DEC rsp ans Hdec) as (r & u & HR & ->); clear Hdec.
  all: assert (ROF : forall xw : word, (A <= bv_unsigned xw < A + mmap_len L)%Z -> ro_addr asegs xw = false)
    by (intros xw Hxw; apply asan_ro_addr_false; lia).
  all: open_statics STA.
  all: pose proof (bv_unsigned_in_range 64 r) as RR; change (bv_modulus 64) with (2^64)%Z in RR.
  all: destruct u; unfold zshape; cbv iota; sys_nret.
  all: stepA.                                   (* [comment removed for export] *)
  all: do 2 stepA.                              (* [comment removed for export] *)
  all: stepA; callA (iserror0_specA P); [lazymatch goal with H : mem_inv _ ?mm |- mem_inv _ ?mm => exact H end| reflexivity| ret_pc_lit].
  all: do 2 stepA.                              (* [comment removed for export] *)
  all: stepA.                                   (* [comment removed for export] *)
  all: do 2 stepA.                              (* [comment removed for export] *)
  all: stepA.                                   (* [comment removed for export] *)
  all: zstepA; zstepA.                          (* [comment removed for export] *)
  all: zstepA; let K := fresh "K" in (if_cases K; zify_cond K).   (* [comment removed for export] *)
  all: match goal with
       | |- evtA _ _ _ (MS _ _ (Z_to_bv 64 0x65c14) _ _ _ _) =>
           (* [comment removed for export] *)
           zstepA;
           replace (18446744073709547520 <? bv_unsigned r) with false by (symmetry; apply (proj2 (Z.ltb_ge _ _)); lia);
           cbn [Z.b2z];
           stepA;                               (* [comment removed for export] *)
           zstepA; if_false;                    (* [comment removed for export] *)
           stepA; stepA;                        (* [comment removed for export] *)
           do 2 stepA;                          (* [comment removed for export] *)
           zstepA;                              (* [comment removed for export] *)
           zstepA; if_true;                     (* [comment removed for export] *)
           stepA;                               (* [comment removed for export] *)
           stepA;                               (* [comment removed for export] *)
           do 7 stepA;                          (* [comment removed for export] *)
           release_frame FR ST (bv_unsigned sp);
           stepA                                (* [comment removed for export] *)
       | _ =>
           (* [comment removed for export] *)
           zstepA; (let K1 := fresh "K" in if_cases K1; zify_cond K1; [exfalso; lia|]);   (* [comment removed for export] *)
           zstepA; zstepA;                      (* [comment removed for export] *)
           zstepA;
           replace (18446744073709547520 <? bv_unsigned r) with true by (symmetry; apply (proj2 (Z.ltb_lt _ _)); lia);
           cbn [Z.b2z];
           stepA;                               (* [comment removed for export] *)
           zstepA; if_true;                     (* [comment removed for export] *)
           destruct TOL as [-> | ->];
           [ zstepA; if_true                    (* [comment removed for export] *)
           | zstepA; if_false;                  (* [comment removed for export] *)
             zstepA;                            (* [comment removed for export] *)
             zstepA;                            (* [comment removed for export] *)
             rewrite (errno_load r) by (unfold is_err; apply Z.ltb_lt; lia);
             destruct (Z.eq_dec (bv_unsigned r) ENOMEMw) as [E12|E12];
             [ replace (Z_to_bv 64 (2^64 - bv_unsigned r)) with (Z_to_bv 64 12) by (f_equal; unfold ENOMEMw in E12; lia);
               zstepA; try first [if_true | if_false];   (* [comment removed for export] *)
               stepA; stepA;                    (* [comment removed for export] *)
               stepA;                           (* [comment removed for export] *)
               do 7 stepA;                      (* [comment removed for export] *)
               release_frame FR ST (bv_unsigned sp);
               stepA                            (* [comment removed for export] *)
             | zstepA; (let K2 := fresh "K" in if_cases K2; zify_cond K2;
                        [ | exfalso; unfold ENOMEMw in E12; first [lia | rewrite Z.mod_small in K2 by lia; lia] ]) ] ]
                                                (* [comment removed for export] *)
       end.
  (* [comment removed for export] *)
  all: lazymatch goal with
       | |- evtA _ _ _ (MS _ _ (Z_to_bv 64 424540) _ _ ?mx _) =>
           apply evtA_done; unfold mmap_fixed_gen_post;
           lazymatch type of HR with _ _ _ ?uu => exists r, uu end;
           first [ rewrite (mfr_ret_tol0 r) by lia | rewrite (mfr_ret_other r) by lia ];
           rewrite MLA in *;
           do 20 eexists; split; [reflexivity|]
       | |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
           apply evtA_done; unfold mmap_fixed_gen_post;
           lazymatch type of HR with _ _ _ ?uu => exists r, uu end;
           first [ rewrite (mfr_ret_noerr r) by lia | rewrite (mfr_ret_enomem r) by assumption ];
           exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0); do 3 eexists; exists (Z_to_bv 64 0);
           do 12 eexists; split;
           [ unfold is_err; first [ replace (18446744073709547520 <? bv_unsigned r) with false by (symmetry; apply (proj2 (Z.ltb_ge _ _)); lia)
                                  | replace (18446744073709547520 <? bv_unsigned r) with true by (symmetry; apply (proj2 (Z.ltb_lt _ _)); lia) ];
             reflexivity |]
       end.
  all: split; [ eapply munch_weaken; [|eassumption]; intros y; cbn; lia |].
  all: split; [assumption|]. all: split; [assumption|].
  all: split; [ first [ assumption | replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia; assumption ] |].
  all: split; [close_statics|].
  all: split; [ first [intros _; assumption | intros; discriminate] |].
  all: split; [| exact HR ].
  all: first [ intros; discriminate
             | intros _; split; [ rewrite unsigned_lit by lia; lia |]; split; [ apply errno_load; unfold is_err; apply Z.ltb_lt; lia |];
               lazymatch goal with H : rw_cells _ _ (bv_unsigned ?spx + -96) _ |- _ =>
                 replace (bv_unsigned spx - 96) with (bv_unsigned spx + -96) by lia; eexists; exact H end ].
Qed.

(* [comment removed for export] *)
Definition mmap_fixed_rw_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (lo : Z) (m : mem) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (if is_err r then Z_to_bv 64 0 else r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)            (* [comment removed for export] *)
    /\ munch (mfr_W sp A L) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ statics m'
    /\ (u = true -> rw_cells asegs m' A [CB (Z.to_nat (mmap_len L)) (repeat (Z_to_bv 8 0) (Z.to_nat (mmap_len L)))])
    /\ R a r u.

(* [comment removed for export] *)
End X1.

End RC__1.
