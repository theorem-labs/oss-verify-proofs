(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AM_memset AI_shadow AX_unreg.
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
Section Walk2.
Variable P : acc -> Prop.
Variables (sp gp tp : word) (F0 : bvmap 5 word) (fc0 : bv 32) (lo : Z) (m0 : mem).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 240.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSHA : forall a k, 0x7fffc000 <= a -> a + Z.of_nat k <= 0x7fffd000 -> P (Z_to_bv 64 a, k).
Hypothesis PSHB : forall a k, 0x8000d065 <= a -> a + Z.of_nat k <= 0x8000e048 -> P (Z_to_bv 64 a, k).
Hypothesis G0 : unreg_statics m0.
Hypothesis TAB0 : globals_tab m0.

Notation UGW :=
  [(bv_unsigned sp - 240, bv_unsigned sp); (0xab430, 0xab438); (SHA_LO, SHA_HI); (SHB_LO, SHB_HI); (SHC_LO, SHC_HI)]%Z.
Notation Q := (Z_to_bv 64 (bv_unsigned sp + -176)).
Lemma UGW_statics' : Forall (fun c => disjoint_from UGW (fst c) (snd c)) unreg_statics_cells.
Proof. unreg_statics_disjoint. Qed.

(* [comment removed for export] *)
Definition ug_post (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F0 (ret_pc ra) fc0 None m' (seg_rom asegs)
    /\ munch UGW m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xab430 [C8 (Z_to_bv 64 0)]
    /\ stk asegs m' SHA_LO SHA_HI /\ stk asegs m' SHB_LO SHB_HI /\ stk asegs m' SHC_LO SHC_HI.

(* [comment removed for export] *)
Lemma ug_epi : forall (m : mem)
    (x1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra,
  mem_inv asegs m -> munch UGW m0 m -> wmono asegs m0 m ->
  stk asegs m lo (bv_unsigned sp + -176) ->
  ug_frame sp m j0 v40 v48 v56 v64 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra ->
  rw_cells asegs m 0xab430 [C8 (Z_to_bv 64 (2^60))] ->
  stk asegs m SHA_LO SHA_HI -> stk asegs m SHB_LO SHB_HI -> stk asegs m SHC_LO SHC_HI ->
  bv_unsigned ra mod 2 = 0 ->
  evtA asegs P (ug_post x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra)
    (ug_head sp gp tp F0 fc0 69 m x1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof.
  intros until ra; intros MI MU WM ST FR MUT SA SB SC RA.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (unreg_statics_transport _ _ _ G0 MU WM UGW_statics') as G.
  unfold ug_frame in FR. unreg_statics_open G. unfold ug_head. cbn [Nat.eqb].
  zstepA. zstepA. stepA. zstepA. stepA. zstepA.
  (* [comment removed for export] *)
  stepA. carve_frame 64%nat ST.
  do 8 stepA.
  stepA. if_true.
  zstepA. stepA. if_false.
  stepA. stepA. stepA. zstepA. zstepA. zstepA. zstepA.
  change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
  stepA. if_true.
  zstepA. stepA. if_false. zstepA. zstepA. stepA. if_true.
  stepA. stepA. stepA. stepA. if_false.
  zstepA. zstepA. zstepA. zstepA. zstepA. stepA. if_false.
  stepA. stepA. stepA. stepA. if_true.
  zstepA. stepA. zstepA.
  do 7 stepA. stepA. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -176).
  stepA. (* [comment removed for export] *)
  destruct (stk_carve _ _ _ _ 552%nat SC ltac:(lia)) as [_ [junkC DST]]. clear SC.
  change (2147538072 - Z.of_nat 552) with 2147537520 in DST.
  callA (memset_specZ 2147537520 552 0); [ | exact DST | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
  { intros a k H1 H2; apply PSHB; lia. }
  lazymatch goal with H : rw_cells asegs ?mx 2147537520 _ |- _ =>
    pose proof (stk_of_rw_cells _ _ _ _ H) as SC; cbn [cells_size csize Nat.add] in SC; clear H end.
  (* [comment removed for export] *)
  stepA. stepA. zstepA. zstepA. zstepA. stepA. zstepA. zstepA. zstepA. stepA. zstepA. zstepA. zstepA. zstepA. stepA.
  zstepA. zstepA. stepA. if_false. zstepA. stepA. if_true.
  zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. stepA. if_true.
  (* [comment removed for export] *)
  stepA. stepA. if_false. stepA. stepA. if_false. stepA. if_true.
  stepA. if_false.
  (* [comment removed for export] *)
  do 13 stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  stepA.
  lazymatch goal with H : rw_cells asegs _ 701488 [C8 ?v] |- _ =>
    let v' := eval vm_compute in (bv_unsigned v) in replace v with (Z_to_bv 64 v') in H by (apply bv_eq; vm_compute; reflexivity); rename H into MUT' end.
  apply evtA_done. unfold ug_post. do 16 eexists.
  split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

End Walk2.
End RC__1.
