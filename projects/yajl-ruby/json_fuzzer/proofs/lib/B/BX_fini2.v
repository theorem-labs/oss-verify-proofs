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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_memset BI_shadow BX_unreg BX_unreg2 BX_unreg3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition fini_statics (m : mem) : Prop :=
     rw_cells bsegs m 0xa6258 [C8 (Z_to_bv 64 0xa5038); C8 (Z_to_bv 64 0xa5028)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa5028 [C8 (Z_to_bv 64 0x822fc); C8 (Z_to_bv 64 0x31884)]    (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa5570 [C8 (Z_to_bv 64 0x927e4); C8 (Z_to_bv 64 0)]          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa72a0 [C8 (Z_to_bv 64 0xa72a0)]                              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xa6218 [C8 (Z_to_bv 64 0xa9f60); C8 (Z_to_bv 64 0xaaee0)].  (* [comment removed for export] *)

Definition fini_statics_cells : list (Z * Z) :=
  [(0xa6258, 16); (0xa5028, 16); (0xa5570, 16); (0xa72a0, 8); (0xa6218, 16)]%Z.

Lemma fini_statics_transport : forall W m m',
  fini_statics m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun c => disjoint_from W (fst c) (snd c)) fini_statics_cells -> fini_statics m'.
Proof.
  intros W m m' G MU WM D. unfold fini_statics_cells in D.
  repeat match type of D with Forall _ (_ :: _) => apply Forall_cons_iff in D; destruct D as [? D] end. cbn [fst snd] in *.
  destruct G as (G1 & G2 & G3 & G4 & G5). unfold fini_statics.
  repeat match goal with
  | |- rw_cells bsegs m' ?A2 ?cs2 /\ _ => split
  | |- rw_cells bsegs m' ?A2 ?cs2 =>
      eapply (rw_cells_transport bsegs W m m' A2 cs2); [ eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add]; assumption ]
  end.
Qed.

(* [comment removed for export] *)
Definition ug_postZ (q : Z) (gp tp : word) (F0 : bvmap 5 word) (fc0 : bv 32) (lo : Z) (m0 : mem)
    (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F0 (ret_pc ra) fc0 None m' (seg_rom bsegs)
    /\ munch [(q - 240, q); (0xabe70, 0xabe78); (SHA_LO, SHA_HI); (SHB_LO, SHB_HI); (SHC_LO, SHC_HI)]%Z m0 m'
    /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q
    /\ rw_cells bsegs m' 0xabe70 [C8 (Z_to_bv 64 0)]
    /\ stk bsegs m' SHA_LO SHA_HI /\ stk bsegs m' SHB_LO SHB_HI /\ stk bsegs m' SHC_LO SHC_HI.

Lemma ug_specZ : forall (P : acc -> Prop) (q : Z) (gp tp : word) (F0 : bvmap 5 word) (fc0 : bv 32) (lo : Z) (m0 : mem)
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo -> lo <= q - 240 -> q < 2^64 ->
  (forall a k, lo <= a -> a + Z.of_nat k <= q -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x7fffc000 <= a -> a + Z.of_nat k <= 0x7fffd000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x8000d065 <= a -> a + Z.of_nat k <= 0x8000dfd8 -> P (Z_to_bv 64 a, k)) ->
  unreg_statics m0 -> globals_tab m0 ->
  mem_inv bsegs m0 -> stk bsegs m0 lo q ->
  rw_cells bsegs m0 0xabe70 [C8 (Z_to_bv 64 0)] ->
  stk bsegs m0 SHA_LO SHA_HI -> stk bsegs m0 SHB_LO SHB_HI -> stk bsegs m0 SHC_LO SHC_HI ->
  a0 = Z_to_bv 64 0xa9f60 -> a1 = Z_to_bv 64 62 -> bv_unsigned ra mod 2 = 0 ->
  evtA bsegs P (ug_postZ q gp tp F0 fc0 lo m0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F0 (Z_to_bv 64 0x40930) fc0 None m0 (seg_rom bsegs)).
Proof.
  intros until t6; intros LOC LO QHI PSTK PIMG PSHA PSHB G TAB MI ST MUT SA SB SC HA0 HA1 RA.
  assert (UQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  pose proof (ug_spec_sec P (Z_to_bv 64 q) gp tp F0 fc0 lo m0) as X. rewrite !UQ in X.
  (* [comment removed for export] *)
  eapply evtA_mono. { eapply X; first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption || lia ]. }
  intros ms' H. unfold ug_post in H. rewrite !UQ in H. exact H.
Qed.

Section Fini.
Variable P : acc -> Prop.
Variables (sp gp tp : word) (F0 : bvmap 5 word) (fc0 : bv 32) (lo : Z) (m0 : mem).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 304.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSHA : forall a k, 0x7fffc000 <= a -> a + Z.of_nat k <= 0x7fffd000 -> P (Z_to_bv 64 a, k).
Hypothesis PSHB : forall a k, 0x8000d065 <= a -> a + Z.of_nat k <= 0x8000dfd8 -> P (Z_to_bv 64 a, k).

Notation FW :=
  [(bv_unsigned sp - 304, bv_unsigned sp); (0xaaf50, 0xaaf51); (0xaaf00, 0xaaf08); (0xabe70, 0xabe78);
   (SHA_LO, SHA_HI); (SHB_LO, SHB_HI); (SHC_LO, SHC_HI)]%Z.

Definition fini_post (ra x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F0 (ret_pc ra) fc0 None m' (seg_rom bsegs)
    /\ munch FW m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0xaaf50 [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' 0xaaf00 [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0xabe70 [C8 (Z_to_bv 64 0)]
    /\ stk bsegs m' SHA_LO SHA_HI /\ stk bsegs m' SHB_LO SHB_HI /\ stk bsegs m' SHC_LO SHC_HI.

Lemma libc_exit_fini_spec : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  mem_inv bsegs m0 ->
  stk bsegs m0 lo (bv_unsigned sp) ->
  fini_statics m0 -> unreg_statics m0 -> globals_tab m0 ->
  rw_cells bsegs m0 0xaaf50 [C1 (Z_to_bv 8 0)] ->            (* [comment removed for export] *)
  rw_cells bsegs m0 0xaaf00 [C8 (Z_to_bv 64 1)] ->           (* [comment removed for export] *)
  rw_cells bsegs m0 0xabe70 [C8 (Z_to_bv 64 0)] ->           (* [comment removed for export] *)
  stk bsegs m0 SHA_LO SHA_HI -> stk bsegs m0 SHB_LO SHB_HI -> stk bsegs m0 SHC_LO SHC_HI ->
  bv_unsigned ra mod 2 = 0 ->
  evtA bsegs P (fini_post ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F0 (Z_to_bv 64 0x928b4) fc0 None m0 (seg_rom bsegs)).
Proof.
  intros until t6; intros MI ST FS G TAB CMPL REGD MUT SA SB SC RA.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl FW m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
  pose proof FS as FS0. destruct FS as (FGOT & FARR & FCXA & FDSO & FMG).
  carve_frame 32%nat ST.
  do 4 stepA. stepA. stepA. stepA. stepA. stepA. if_false.
  stepA. zstepA. stepA. (* [comment removed for export] *)
  carve_frame 16%nat ST.
  stepA. stepA. stepA. zstepA. stepA. zstepA. stepA. zstepA. stepA. if_true.
  stepA. zstepA. zstepA. stepA. (* [comment removed for export] *)
  stepA. stepA. stepA. if_false. stepA. stepA. zstepA. stepA. stepA. (* [comment removed for export] *) stepA.
  stepA. stepA. stepA. stepA. if_true.
  stepA. stepA. stepA. release_frame FR0 ST (bv_unsigned sp + -32). stepA. (* [comment removed for export] *)
  zstepA. stepA. if_true.
  stepA. zstepA. stepA. (* [comment removed for export] *)
  carve_frame 16%nat ST.
  stepA. stepA. stepA. stepA. stepA. stepA. stepA. zstepA. stepA. (* [comment removed for export] *)
  carve_frame 16%nat ST.
  stepA. stepA. stepA. stepA. if_false. zstepA. stepA. stepA. if_false.
  zstepA. zstepA. stepA. if_false. zstepA. zstepA. zstepA.
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (unreg_statics_transport _ _ _ G MU WM ltac:(unreg_statics_disjoint)) as Gx;
    pose proof (globals_tab_transport _ _ _ TAB MU WM ltac:(cbn [disjoint_from]; repeat split; lia)) as TABx end.
  callA (ug_specZ P (bv_unsigned sp + -64) gp tp F0 fc0 lo);
    [ exact LOC | lia | lia
    | intros a k H1 H2; apply PSTK; lia
    | exact PIMG | exact PSHA | exact PSHB | exact Gx | exact TABx
    | exact MI | exact ST | exact MUT | exact SA | exact SB | exact SC
    | reflexivity | reflexivity | vm_compute; reflexivity | ].
  (* [comment removed for export] *)
  stepA. stepA. stepA. stepA.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -64) _, S : stk bsegs _ lo _ |- _ => release_frame H S (bv_unsigned sp + -48) end.
  stepA. (* [comment removed for export] *)
  stepA. stepA.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -48) _, S : stk bsegs _ lo _ |- _ => release_frame H S (bv_unsigned sp + -32) end.
  stepA. (* [comment removed for export] *)
  zstepA. stepA. if_false.
  stepA. stepA. stepA. stepA.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -32) _, S : stk bsegs _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  stepA. (* [comment removed for export] *) stepA.
  apply evtA_done. unfold fini_post. do 16 eexists.
  split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.
End Fini.

(* [comment removed for export] *)
Definition fini_postZ (q : Z) (gp tp : word) (F0 : bvmap 5 word) (fc0 : bv 32) (lo : Z) (m0 : mem)
    (ra x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F0 (ret_pc ra) fc0 None m' (seg_rom bsegs)
    /\ munch [(q - 304, q); (0xaaf50, 0xaaf51); (0xaaf00, 0xaaf08); (0xabe70, 0xabe78);
              (SHA_LO, SHA_HI); (SHB_LO, SHB_HI); (SHC_LO, SHC_HI)]%Z m0 m'
    /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q
    /\ rw_cells bsegs m' 0xaaf50 [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' 0xaaf00 [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0xabe70 [C8 (Z_to_bv 64 0)]
    /\ stk bsegs m' SHA_LO SHA_HI /\ stk bsegs m' SHB_LO SHB_HI /\ stk bsegs m' SHC_LO SHC_HI.

(* [comment removed for export] *)
End RC__1.
