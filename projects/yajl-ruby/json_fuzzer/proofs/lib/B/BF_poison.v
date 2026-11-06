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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit BF_unwind BM_memset.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cstep := stepA; try first [if_true | if_false].

(* [comment removed for export] *)
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
Definition poison_globals (m : mem) : Prop :=
  rw_cells bsegs m 0xa55a0 [C8 (Z_to_bv 64 0xae5b8); C8 (Z_to_bv 64 0xaf2a8); C8 (Z_to_bv 64 0xaf2b0); C8 (Z_to_bv 64 0xaf2a0); C8 (Z_to_bv 64 0xa7408)]
  /\ rw_cells bsegs m 0xa5590 [C8 (Z_to_bv 64 0x1400e8)]
  /\ rw_cells bsegs m 0xae5b8 [C8 (Z_to_bv 64 kShadowBase)]
  /\ rw_cells bsegs m 0xaf2a0 [C8 (Z_to_bv 64 kHighMemEnd); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xa7400 [C8 (Z_to_bv 64 0x9e8cc); C8 (Z_to_bv 64 0x9ecd0)]
  /\ rw_cells bsegs m 0xade1c [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x140160 [C8 (Z_to_bv 64 kClearShadowMmapThreshold)].     (* [comment removed for export] *)

Lemma poison_globals_agree : forall m m', poison_globals m ->
  (forall a, (0xa5000 <= a < 0x140810) -> m' (wa a) = m (wa a)) -> poison_globals m'.
Proof. aceil.
  intros m m' (G1 & G2 & G3 & G4 & G5 & G6 & G7) AG.
  repeat split; (eapply (rw_cells_agree bsegs m m'); [| eassumption]; cbn; intros x Hx; apply AG; lia).
Qed.

Section Walk.
Variable P : acc -> Prop.

Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SH len v : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (SH, SH + len)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' SH [CB (Z.to_nat len) (repeat (Z_to_bv 8 v) (Z.to_nat len))]
    /\ poison_globals m'.

(* [comment removed for export] *)
Definition poison_join_post (ra sp gp tp : word) (s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (A L v : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t2 a4 a5 a6 a7 t3 : word),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 650448) t2
                 (Z_to_bv 64 (((A + L + -8) ≫ 3 + 1) mod 18446744073709551616 - A ≫ 3)) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 (2147450880 + A ≫ 3)) (Z_to_bv 64 ((A + L + -8) ≫ 3)) (Z_to_bv 64 v) (Z_to_bv 64 (A ≫ 3))
                 a4 a5 a6 a7 (Z_to_bv 64 ((A + L + -8) ≫ 3 + 1)) (Z_to_bv 64 685064) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x55338) fc None m (seg_rom bsegs).

Lemma poison_checks_join :
  forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A L v : Z),
  mem_inv bsegs m -> poison_globals m ->
  A mod 8 = 0 -> L mod 8 = 0 -> 0 <= L ->
  0x603000 <= A -> A + L <= alloc_ceiling -> (A + L <= 0x7fff7000 \/ (kHighMemBeg <= A /\ (kHighMemBeg + 8 <= A \/ 8 <= L))) ->
  0 <= v < 256 ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (poison_join_post ra sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m A L v)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x550c4) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until v. intros MI PG AM LM L0 AI AC APL HV PDAT.
  pose proof PG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  aceil.
  rewrite kHighMemBeg_val in APL. unfold kShadowBase, kHighMemEnd, kClearShadowMmapThreshold in *.
  assert (HA8 : A = 8 * (A / 8)) by (pose proof (Z.div_mod A 8 ltac:(lia)); lia).
  assert (HL8 : L = 8 * (L / 8)) by (pose proof (Z.div_mod L 8 ltac:(lia)); lia).
  assert (MU : munch [] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
  Ltac arith := repeat match goal with
                | H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
                | H : mem_inv _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : poison_globals _ |- _ => clear H
                | H : forall a n, _ -> _ -> P _ |- _ => clear H end; lia.
  Ltac land7 K := exfalso; apply K; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); change (2^3) with 8; arith.
  Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit by arith; intros K; arith.
  (* [comment removed for export] *)
  Ltac litland := match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] =>
                    let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
  Ltac br1 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [kill K|]).     (* [comment removed for export] *)
  Ltac br2 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [| kill K]).    (* [comment removed for export] *)
  Ltac br7 := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [land7 K|]).    (* [comment removed for export] *)
  destruct APL as [ALOW|[AHIGH AH8]].
  - (* [comment removed for export] *)
    zstepA; br7.                      (* [comment removed for export] *)
    do 7 zstepA; litland; br2.        (* [comment removed for export] *)
    zstepA; br7.                      (* [comment removed for export] *)
    do 2 zstepA; br2.                 (* [comment removed for export] *)
    do 3 zstepA; cstep.               (* [comment removed for export] *)
    do 5 zstepA.                      (* [comment removed for export] *)
    apply evtA_done. unfold poison_join_post. do 7 eexists. reflexivity.
  - (* [comment removed for export] *)
    zstepA; br7.                      (* [comment removed for export] *)
    do 7 zstepA; litland; br1.        (* [comment removed for export] *)
    do 7 zstepA; br2.                 (* [comment removed for export] *)
    do 5 zstepA; br1.                 (* [comment removed for export] *)
    br2.                              (* [comment removed for export] *)
    do 3 zstepA; br1.                 (* [comment removed for export] *)
    br2.                              (* [comment removed for export] *)
    zstepA; br7.                      (* [comment removed for export] *)
    do 2 zstepA; br1.                 (* [comment removed for export] *)
    do 7 zstepA; br2.                 (* [comment removed for export] *)
    do 5 zstepA; br1.                 (* [comment removed for export] *)
    br1.                              (* [comment removed for export] *)
    do 3 zstepA; cstep.               (* [comment removed for export] *)
    do 5 zstepA.                      (* [comment removed for export] *)
    apply evtA_done. unfold poison_join_post. do 7 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma poison_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A L v : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> poison_globals m ->
  A mod 8 = 0 -> L mod 8 = 0 -> 0 <= L ->
  (* [comment removed for export] *)
  0x603000 <= A -> A + L <= alloc_ceiling -> (A + L <= 0x7fff7000 \/ (kHighMemBeg <= A /\ (kHighMemBeg + 8 <= A \/ 8 <= L))) ->
  0 <= v < 256 ->
  (v <> 0 \/ L / 8 < kClearShadowMmapThreshold) ->
  rw_cells bsegs m (kShadowBase + A / 8) [CB (Z.to_nat (L / 8)) junk] ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  (forall a n, kShadowBase + A / 8 <= a -> a + Z.of_nat n <= kShadowBase + A / 8 + L / 8 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo (kShadowBase + A / 8) (L / 8) v)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55090) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until junk. intros SK LOC LO SPH MI PG AM LM L0 AI AC APL HV CASE DST PSTK PDAT PSH.
  pose proof PG as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof APL as APL0. pose proof AC as AC0.
  pose proof LOC as LOC0. aceil.
  rewrite kHighMemBeg_val in APL. unfold kShadowBase, kHighMemEnd, kClearShadowMmapThreshold in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (SH := 2147450880 + A / 8) in *. set (len := L / 8) in *.
  assert (HA8 : A = 8 * (A / 8)) by (pose proof (Z.div_mod A 8 ltac:(lia)); lia).
  assert (HL8 : L = 8 * len) by (pose proof (Z.div_mod L 8 ltac:(lia)); lia).
  assert (MU : munch [(bv_unsigned sp - 64, bv_unsigned sp); (SH, SH + len)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 64%nat SK.
  assert (SHR : 2147450880 <= SH /\ SH + len <= 2147450880 + 2^44) by (subst SH len; clear -CEILB AM LM L0 AI AC HA8 HL8; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 SH) = SH) by (apply Z_to_bv_small; change (bv_modulus 64) with (2^64); clear -CEILB SHR L0 HL8; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 len) = len) by (apply Z_to_bv_small; change (bv_modulus 64) with (2^64); clear -CEILB SHR L0 HL8; lia).
  assert (E3 : bv_unsigned (Z_to_bv 64 v) = v) by (apply Z_to_bv_small; change (bv_modulus 64) with (2^64); clear -CEILB HV; lia).
  (* [comment removed for export] *)
  Ltac pg_after PG MUx := eapply poison_globals_agree; [exact PG|]; intros a Ha; apply MUx; rewrite wa_unsigned by arith; cbn; arith.
  (* [comment removed for export] *)
  destruct (Z.eq_dec v 0) as [->|NZ].
  - (* [comment removed for export] *)
    destruct CASE as [X|LEN]; [exfalso; exact (X eq_refl)|].
    do 8 cstep.                                                        (* [comment removed for export] *)
    cstep.                                                             (* [comment removed for export] *)
    eapply evtA_cut; [ eapply poison_checks_join | ];
      [ eassumption | lazymatch goal with MUx : munch _ m ?mx |- poison_globals ?mx => pg_after PG MUx end
      | exact AM | exact LM | exact L0 | exact AI | exact AC0 | exact APL0 | exact HV | exact PDAT
      | cbv beta; intros ms' (t0j & t2j & a4j & a5j & a6j & a7j & t3j & ->) ].
    replace (((A + L + -8) ≫ 3 + 1) mod 18446744073709551616 - A ≫ 3) with len
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; rewrite Z.mod_small; clear -CEILB AM LM L0 AI AC HA8 HL8; [nia| nia]).
    replace (A ≫ 3) with (A / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity). fold SH.
    cstep.                                                             (* [comment removed for export] *)
    do 3 zstepA. br2.                                                  (* [comment removed for export] *)
    do 2 cstep.                                                        (* [comment removed for export] *)
    do 9 cstep.                                                        (* [comment removed for export] *)
    release_frame FR SK (bv_unsigned sp).
    cstep.                                                             (* [comment removed for export] *)
    eapply evtA_mono.
    { eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ junk P); [| | exact MI].
      - intros a k H1 H2. rewrite E1 in H1, H2. rewrite E2 in H2. apply PSH; assumption.
      - rewrite E1, E2. exact DST. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & DST').
    rewrite !E1, !E2, ?E3 in MU', DST'.
    assert (MU3 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (SH, SH + len)] m m').
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. intros x Hx. cbn in Hx |- *. intuition lia. }
    unfold poison_post. do 16 eexists. split; [reflexivity|]. split; [exact MU3|].
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    split; [exact MI'|]. split.
    { eapply (stk_transport_disjoint bsegs); [exact SK| exact MU'| exact WM'|]. cbn. clear -CEILB SHR LOC SPR L0 HL8. lia. }
    split.
    2:{ pg_after PG MU3. }
    replace (0 mod 256) with 0 in DST' by (symmetry; apply Z.mod_small; clear -CEILB HV; lia). exact DST'.
  - (* [comment removed for export] *)
    do 8 cstep.                                                        (* [comment removed for export] *)
    br1.                                                               (* [comment removed for export] *)
    do 3 zstepA. cstep.                                                (* [comment removed for export] *)
    eapply evtA_cut; [ eapply poison_checks_join | ];
      [ eassumption | lazymatch goal with MUx : munch _ m ?mx |- poison_globals ?mx => pg_after PG MUx end
      | exact AM | exact LM | exact L0 | exact AI | exact AC0 | exact APL0 | exact HV | exact PDAT
      | cbv beta; intros ms' (t0j & t2j & a4j & a5j & a6j & a7j & t3j & ->) ].
    replace (((A + L + -8) ≫ 3 + 1) mod 18446744073709551616 - A ≫ 3) with len
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; rewrite Z.mod_small; clear -CEILB AM LM L0 AI AC HA8 HL8; [nia| nia]).
    replace (A ≫ 3) with (A / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity). fold SH.
    br2.                                                               (* [comment removed for export] *)
    do 2 cstep.                                                        (* [comment removed for export] *)
    do 9 cstep.                                                        (* [comment removed for export] *)
    release_frame FR SK (bv_unsigned sp).
    cstep.                                                             (* [comment removed for export] *)
    eapply evtA_mono.
    { eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ junk P); [| | exact MI].
      - intros a k H1 H2. rewrite E1 in H1, H2. rewrite E2 in H2. apply PSH; assumption.
      - rewrite E1, E2. exact DST. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & DST').
    rewrite !E1, !E2, ?E3 in MU', DST'.
    assert (MU3 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (SH, SH + len)] m m').
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. intros x Hx. cbn in Hx |- *. intuition lia. }
    unfold poison_post. do 16 eexists. split; [reflexivity|]. split; [exact MU3|].
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    split; [exact MI'|]. split.
    { eapply (stk_transport_disjoint bsegs); [exact SK| exact MU'| exact WM'|]. cbn. clear -CEILB SHR LOC SPR L0 HL8. lia. }
    split.
    2:{ pg_after PG MU3. }
    replace (bv_unsigned (Z_to_bv 64 v)) with v in DST' by (symmetry; apply Z_to_bv_small; change (bv_modulus 64) with (2^64); clear -CEILB HV; lia).
    replace (v mod 256) with v in DST' by (symmetry; apply Z.mod_small; clear -CEILB HV; lia). exact DST'.
Qed.
End Walk.
End RC__1.

(* [comment removed for export] *)
Ltac poison_checks_cut JOIN := eapply evtA_cut; [ eapply JOIN | ].
