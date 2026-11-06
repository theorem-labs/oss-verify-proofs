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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_memset BI_shadow BX_unreg BX_unreg2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac amo_phase1x :=
  match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let H := fresh "AL" in
      first [ assert (H : amo_aligned wd a = true) by prove_amo_aligned
            | fail 100 "stepA: cannot prove natural alignment of the atomic access at" a ];
      rewrite H; clear H; cbv beta iota delta [negb];
      exec_cbvA; simp_is_x0; simp_regs;
      repeat match goal with
      | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?x)] => rewrite (Z.eqb_refl (bv_unsigned x)); cbv beta iota
      | |- context [Z.eqb ?x ?x] => rewrite (Z.eqb_refl x); cbv beta iota
      | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
          replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with true by (symmetry; apply Z.eqb_eq; first [reflexivity | zsimp; lia]);
          cbv beta iota
      end
  | _ => idtac
  end.
Ltac amo_phase i ::=
  lazymatch i with
  | Lr _ _ _ _ _ => amo_phase1x
  | Sc _ _ _ _ _ _ => amo_phase1x
  | Amo _ _ _ _ _ _ _ => amo_phase1x
  | _ => idtac
  end.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Walk3.
Variable P : acc -> Prop.
Variables (sp gp tp : word) (F0 : bvmap 5 word) (fc0 : bv 32) (lo : Z) (m0 : mem).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 240.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSHA : forall a k, 0x7fffc000 <= a -> a + Z.of_nat k <= 0x7fffd000 -> P (Z_to_bv 64 a, k).
Hypothesis PSHB : forall a k, 0x8000d065 <= a -> a + Z.of_nat k <= 0x8000dfd8 -> P (Z_to_bv 64 a, k).
Hypothesis G0 : unreg_statics m0.
Hypothesis TAB0 : globals_tab m0.

Notation UGW :=
  [(bv_unsigned sp - 240, bv_unsigned sp); (0xabe70, 0xabe78); (SHA_LO, SHA_HI); (SHB_LO, SHB_HI); (SHC_LO, SHC_HI)]%Z.
Notation Q := (Z_to_bv 64 (bv_unsigned sp + -176)).

(* [comment removed for export] *)
Lemma ug_pro : forall (QQ : machine_state -> Prop)
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  mem_inv bsegs m0 ->
  stk bsegs m0 lo (bv_unsigned sp) ->
  rw_cells bsegs m0 0xabe70 [C8 (Z_to_bv 64 0)] ->
  stk bsegs m0 SHA_LO SHA_HI -> stk bsegs m0 SHB_LO SHB_HI -> stk bsegs m0 SHC_LO SHC_HI ->
  a0 = Z_to_bv 64 A_GTAB -> a1 = Z_to_bv 64 62 ->
  (forall j0, ug_kont P sp gp tp F0 fc0 lo m0 0 QQ j0 (Z_to_bv 64 0xaf2a0) (Z_to_bv 64 0x13e060) (Z_to_bv 64 0xaf2b0) (Z_to_bv 64 0xaf2a8)
                     s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra) ->
  evtA bsegs P QQ
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F0 (Z_to_bv 64 0x40930) fc0 None m0 (seg_rom bsegs)).
Proof.
  intros until t6; intros MI ST MUT SA SB SC -> -> HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl UGW m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
  pose proof G0 as G. unreg_statics_open G.
  carve_frame 176%nat ST.
  stepA. do 13 stepA.
  zstepA. stepA. stepA. zstepA. stepA.
  stepA. if_false.
  zstepA. stepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA.
  stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. stepA. zstepA. zstepA. zstepA. zstepA.
  zstepA. stepA. if_false.
  zstepA. zstepA.
  (* [comment removed for export] *)
  stepA. stepA. if_false. stepA. stepA. if_false. stepA. if_true.
  stepA. stepA. stepA. if_false.
  do 7 stepA.
  stepA. stepA. stepA. stepA. stepA. stepA. stepA. stepA. stepA. stepA. stepA.
  zstepA. stepA. zstepA. stepA. stepA. stepA.
  lazymatch goal with H : rw_cells bsegs ?mx 704112 [C8 ?v] |- _ =>
    let v' := eval vm_compute in (bv_unsigned v) in replace v with (Z_to_bv 64 (2^60)) in H by (apply bv_eq; vm_compute; reflexivity);
    rename H into MUT';
    lazymatch goal with F : rw_cells bsegs mx (bv_unsigned sp + -176) (CB 8 ?j :: _) |- _ =>
      unfold ug_kont, ug_head in HK; cbn [Nat.eqb] in HK;
      eapply evtA_eq; [ | eapply (HK j mx); try eassumption; unfold ug_frame; exact F ] end end.
  cbv delta [mkR]. repeat first [reflexivity | progress f_equal; try lia].
Qed.

(* [comment removed for export] *)
Ltac ug_ea := first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption ].
Lemma ug_spec_sec : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  mem_inv bsegs m0 ->
  stk bsegs m0 lo (bv_unsigned sp) ->
  rw_cells bsegs m0 0xabe70 [C8 (Z_to_bv 64 0)] ->
  stk bsegs m0 SHA_LO SHA_HI -> stk bsegs m0 SHB_LO SHB_HI -> stk bsegs m0 SHC_LO SHC_HI ->
  a0 = Z_to_bv 64 A_GTAB -> a1 = Z_to_bv 64 62 -> bv_unsigned ra mod 2 = 0 ->
  evtA bsegs P (ug_post sp gp tp F0 fc0 lo m0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F0 (Z_to_bv 64 0x40930) fc0 None m0 (seg_rom bsegs)).
Proof.
  intros until t6; intros MI ST MUT SA SB SC HA0 HA1 RA.
  eapply ug_pro; try ug_ea.
  intros j0. unfold ug_kont. intros.
  eapply (ug_loop P sp gp tp F0 fc0 lo m0 LOC LO PIMG PSHA PSHB G0 TAB0 62 0); [reflexivity | ug_ea .. |].
  unfold ug_kont. intros. eapply ug_epi; ug_ea.
Qed.
End Walk3.
End RC__1.
