(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_poison AF_free_kit AF_free1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
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

Section QCHUNK2.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo hi cb B A len : Z) (b1 nhi nlo : Z) (aidw uw : word) (TSD CTX T : Z).
Notation INST := 0xaa518.
Notation n := (nhi * 2^32 + nlo).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis SPH : bv_unsigned sp <= B.             (* [comment removed for export] *)
Hypothesis HB : B + 16 <= A /\ A <= hi.              (* [comment removed for export] *)
Hypothesis HI : hi < 2^47.
Hypothesis HLEN : 1 <= len <= 30.                (* [comment removed for export] *)
Hypothesis HCB : 0x603000 <= cb /\ cb + 24 <= alloc_ceiling /\ cb mod 16 = 0.
Hypothesis HNHI : 0 <= nhi < 256.
Hypothesis HNLO : 0 <= nlo < 2^32.
Hypothesis HT1 : 0x5cfdd0 <= TSD. Hypothesis HT2 : TSD + 8 <= 0x603000.
Hypothesis HC : placed_s CTX 4096.        (* [comment removed for export] *)
Hypothesis HTp : placed_s T 4096.         (* [comment removed for export] *)
Hypothesis HTP : 0x5cfdd0 + 88 <= bv_unsigned tp < 0x603000.
Hypothesis HCBT : cb + 24 <= T \/ T + 4096 <= cb.
Hypothesis HCBC : cb + 24 <= CTX \/ CTX + 4096 <= cb.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
(* [comment removed for export] *)
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= hi -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : forall a k, CTX <= a -> a + Z.of_nat k <= CTX + 160 -> P (Z_to_bv 64 a, k).   (* [comment removed for export] *)
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, cb <= a -> a + Z.of_nat k <= cb + 24 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition qchunk_front_post : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x36dec) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 cb) (Z_to_bv 64 B)
                  (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 A) (Z_to_bv 64 CTX) a4 a5 a6 a7
                  (Z_to_bv 64 INST) (Z_to_bv 64 0) (Z_to_bv 64 T) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x73f64) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 48)
    /\ rw_cells asegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw]
    /\ thread_cells m' tp TSD CTX T /\ rw_cells asegs m' T [C8 (Z_to_bv 64 CTX)] /\ rw_cells asegs m' (CTX + 8) [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' B [C8 (Z_to_bv 64 A); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)].

Lemma qchunk_front :
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
  rw_cells asegs m cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw] ->
  thread_cells m tp TSD CTX T -> rw_cells asegs m T [C8 (Z_to_bv 64 CTX)] -> rw_cells asegs m (CTX + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m B [C8 (Z_to_bv 64 A); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)] ->
  evtA asegs P qchunk_front_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 cb) (Z_to_bv 64 (cb + 16)) (Z_to_bv 64 B) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36d94) fc None m (seg_rom asegs)).
Proof. aceil.
  intros SK LO MI HDR TC TCTX TID OBJ.
  destruct HC as (HC1 & HC2 & HCg & HCs). destruct HTp as (HT3 & HT4 & HTg & HTs). unfold A_IMG_END in HCg, HTg. unfold A_LOWAPP_END, A_HIGH_BEG in HCs, HTs.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  assert (MU : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 48%nat SK.
  do 7 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. cstep. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  call_spA (get_current_thread_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
    [exact SK| exact LOC0| lia| lia| exact MI| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| lia| exact HT2| lia| exact HC2| lia
    | lia| intros; apply PSTK; lia| exact PDAT| apply PCTX; lia|].
  rename POST into SK.
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (OBJ8 : rw_cells asegs mx B [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (len + 2^32 * 0))]) end.
  { destruct OBJ as [[WF BA] WR]. split; [split; [first [cbn; clear -WF; tauto | cbn; tauto]|]|].   (* [comment removed for export] *)
    - change [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (len + 2^32 * 0))] with ([C8 (Z_to_bv 64 A)] ++ [C8 (Z_to_bv 64 (len + 2^32 * 0))]).
      rewrite cells_bytes_app, (c8_c4c4 len 0) by lia. exact BA.
    - exact WR. }
  replace (len + 2^32 * 0) with len in OBJ8 by lia.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
  apply evtA_done. unfold qchunk_front_post. exists mZ.
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [lazymatch goal with H : mem_inv asegs mZ |- _ => exact H end|].
  split; [exact SK|]. split; [exact FR|].
  split; [exact HDR|]. split; [exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))|]. split; [exact TCTX|]. split; [exact TID| exact OBJ].
Qed.

(* [comment removed for export] *)
Definition qchunk_back_post (id : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (INST + 728)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 B) (Z_to_bv 64 cb) (Z_to_bv 64 n) a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x36f0c) fc None m' (seg_rom asegs)
    /\ munch [(cb + 16, cb + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (cb + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw].

Lemma qchunk_back :
  forall (id : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  stk asegs m lo (bv_unsigned sp - 48) -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
  0 <= id < 2^32 ->
  rw_cells asegs m (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw] ->
  rw_cells asegs m (cb + 16) [C8 uw] ->
  evtA asegs P (qchunk_back_post id t0' t1' t2' a6' a7' t3' t4' t5' t6')
      (MS (mkR (Z_to_bv 64 0x36dec) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0' t1' t2' (Z_to_bv 64 cb) (Z_to_bv 64 B)
               (Z_to_bv 64 id) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 0) (Z_to_bv 64 T) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x36dec) fc None m (seg_rom asegs)).
Proof. aceil.
  intros id t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' SK LO MI HID FR HDR UW.
  destruct HC as (HC1 & HC2 & HCg & HCs). destruct HTp as (HT3 & HT4 & HTg & HTs). unfold A_IMG_END in HCg, HTg. unfold A_LOWAPP_END, A_HIGH_BEG in HCs, HTs.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MU : munch [(cb + 16, cb + 24)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 48)) = bv_unsigned sp - 48) by (apply unsigned_lit; lia).
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  replace (Z.lor 0 (id mod 4294967296)) with id by (rewrite Z.lor_0_l, Z.mod_small by lia; reflexivity).
  (* [comment removed for export] *)
  pose proof (wr_at_store_ok asegs m (cb + 16) 8 0 8 (proj2 UW) ltac:(lia) ltac:(cbn; lia)) as SOK.
  replace (cb + 16 + 0) with (cb + 16) in SOK by lia. pose proof (proj2 UW) as UWR. cbn [cells_size csize Nat.add] in UWR. clear UW.
  zstepA. settle_storeD (cb + 16) (le8 (Z_to_bv 64 id)) SOK. rename m0 into m3.
  assert (UW : rw_cells asegs m3 (cb + 16) [C8 (Z_to_bv 64 id)]).
  { split; [split; [cbn; tauto| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BAw]|]. cbn [cells_size csize Nat.add]. exact UWR. }
  clear BAw UWR.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) rewrite fzx16_small by lia.
  zstepA. (* [comment removed for export] *) rewrite fzx32_small' by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  replace (Z.shiftl nhi 32 mod 18446744073709551616) with (Z.shiftl nhi 32) by (symmetry; apply Z.mod_small; rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (lor_shiftl nhi nlo 32) by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  do 7 zstepA. (* [comment removed for export] *)
  rewrite ?Hsp. replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia. rewrite ?Z_to_bv_bv_unsigned.
  release_frame FR SK (bv_unsigned sp).
  zstepA. (* [comment removed for export] *)
  apply evtA_done. unfold qchunk_back_post. exists m3.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [| split; [exact UW| exact HDR]].
  first [exact SK | rewrite Hsp in SK; replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) in SK by lia; exact SK].
Qed.
End QCHUNK2.
End RC__1.
