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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_poison.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.

Ltac cstep := stepA; try first [if_true | if_false].
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ True => split; [lia| exact I] | |- _ /\ _ => split; [lia| first [exact I| lia]] end | lia ].

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_log_cases : forall n,
  rz_log n = (if n <? 49 then 0 else if n <? 97 then 1 else if n <? 449 then 2 else if n <? 3969 then 3
              else if n <? 16129 then 4 else if n <? 32257 then 5 else if n <? 64513 then 6 else 7).
Proof.
  intros n. unfold rz_log.
  repeat match goal with |- context [n <=? ?a - ?b] => let v := eval vm_compute in (a - b) in change (a - b) with v end.
  repeat match goal with |- context [n <? ?c] =>
    let c' := eval vm_compute in (c - 1) in
    replace (n <? c) with (n <=? c') by (destruct (n <=? c') eqn:E1; destruct (n <? c) eqn:E2; try reflexivity;
      first [apply Z.leb_le in E1 | apply Z.leb_gt in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]; lia) end.
  reflexivity.
Qed.

Lemma rounded_land_max : forall k, 1 <= k < 2^62 -> Z.land (Z.max k 8 + 7) 18446744073709551608 = rounded k.
Proof.
  intros k Hk. change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia.
  unfold rounded, round_up, kChunkHeader2Size. change (2^3) with 8.
  replace (Z.max k 8 + 7) with (Z.max k 8 + 8 - 1) by lia.
  pose proof (Z.div_mod (Z.max k 8 + 8 - 1) 8 ltac:(lia)). lia.
Qed.

Lemma sllw_rz_size : forall n, bv_swrap 32 (Z.shiftl 16 (rz_log n mod 32)) = rz_size n.
Proof.
  intros n. unfold rz_size. pose proof (rz_log_range n) as R. set (k := rz_log n) in *. clearbody k.
  assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.
Lemma from_primary_ltb : forall n, (needed1 n <? 65537) = from_primary n.
Proof.
  intros n. unfold from_primary, kMaxSize. destruct (needed1 n <? 65537) eqn:E1; destruct (needed1 n <=? 65536) eqn:E2; try reflexivity;
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.leb_le in E2 | apply Z.leb_gt in E2]; lia.
Qed.
Lemma needed_range : forall n, 1 <= n <= 2^27 -> n + 16 <= needed1 n <= needed n /\ needed n <= needed1 n + rz_size n /\ needed1 n <= 2^27 + 2064.
Proof.
  intros n Hn. pose proof (needed1_ge n). pose proof (rz_size_pos n). pose proof (rounded_ge n) as (R1 & R2 & _).
  unfold needed. unfold needed1 in *. destruct (from_primary n); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac arith := repeat match goal with
              | H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
              | H : mem_inv _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : AF_poison.poison_globals _ |- _ => clear H
              | H : AF_kit.thread_cells _ _ _ _ _ |- _ => clear H
              | H : forall a k, _ -> _ -> ?Q _ |- _ => clear H end; lia.
(* [comment removed for export] *)
Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit by arith; intros K; arith.
(* [comment removed for export] *)
Ltac is_lit t := idtac; lazymatch t with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | ?x + ?y => is_lit x; is_lit y | ?x * ?y => is_lit x; is_lit y | ?x - ?y => is_lit x; is_lit y | - ?x => is_lit x
  | Z.land ?x ?y => is_lit x; is_lit y | Z.lor ?x ?y => is_lit x; is_lit y | Z.lxor ?x ?y => is_lit x; is_lit y
  | Z.shiftl ?x ?y => is_lit x; is_lit y | Z.shiftr ?x ?y => is_lit x; is_lit y | ?x mod ?y => is_lit x; is_lit y
  | Z.b2z (?x <? ?y) => is_lit x; is_lit y | Z.b2z (?x =? ?y) => is_lit x; is_lit y end.
Ltac is_num t := idtac; lazymatch t with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac evalc e := is_lit e; assert_fails (is_num e); let v := eval vm_compute in e in change e with v.
Ltac litc :=
  repeat match goal with
  | |- context [Z.b2z ?c] => evalc (Z.b2z c)
  | |- context [?a mod 18446744073709551616] => evalc (a mod 18446744073709551616)
  | |- context [?a mod 256] => evalc (a mod 256)
  | |- context [Z.land ?a ?b] => evalc (Z.land a b)
  | |- context [Z.lor ?a ?b] => evalc (Z.lor a b)
  end; rewrite ?Z.add_0_r, ?Z.add_0_l.
(* [comment removed for export] *)
Ltac br1' := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [kill K| try clear K]).
Ltac br2' := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [try clear K| kill K]).
Ltac pg := match goal with |- ?g => idtac g end.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section ALLOC.
Variable P : acc -> Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac arm n K := zstepA; if_cases K; zify_cond K;
  [ match type of K with ?c <= n => replace (n <? c) with false by (symmetry; apply Z.ltb_ge; exact K) end
  | match type of K with n < ?c => replace (n <? c) with true by (symmetry; apply Z.ltb_lt; exact K) end;
    zstepA; cstep; apply evtA_done; eexists; reflexivity ].
Lemma rz_ladder :
  forall (n : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  1 <= n <= 2^27 ->
  evtA asegs P
    (fun ms => exists a0' : word,
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x32d6c) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x32c98) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hn. rewrite (rz_log_cases n).
  arm n K1.                                      (* [comment removed for export] *)
  zstepA. arm n K2.                              (* [comment removed for export] *)
  zstepA. arm n K3.                              (* [comment removed for export] *)
  zstepA. zstepA. arm n K4.                      (* [comment removed for export] *)
  zstepA. zstepA. arm n K5.                      (* [comment removed for export] *)
  zstepA. zstepA. arm n K6.                      (* [comment removed for export] *)
  zstepA. zstepA.                                (* [comment removed for export] *)
  zstepA.                                        (* [comment removed for export] *)
  destruct (n <? 64513) eqn:K7; zstepA; cbn [Z.b2z Z.lxor Pos.lxor]; apply evtA_done; eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_stretch :
  forall (k n : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  0 <= k <= 7 -> 1 <= n <= 2^27 ->
  evtA asegs P
    (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7
                            s2 (Z_to_bv 64 k) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x32db4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 k) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x32d98) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hk Hn.
  zstepA. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    zstepA. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      zstepA. zstepA. zstepA. if_cases K3; zify_cond K3.
      * rewrite Z.max_l by lia. apply evtA_done. reflexivity.
      * zstepA. rewrite Z.max_r by lia. apply evtA_done. reflexivity.
    + (* [comment removed for export] *)
      zstepA. replace k with 7 by lia. zstepA. zstepA. zstepA. if_cases K3; zify_cond K3.
      * zstepA. rewrite Z.max_r by lia. apply evtA_done. reflexivity.
      * zstepA. rewrite Z.max_l by lia. apply evtA_done. reflexivity.
  - (* [comment removed for export] *)
    zstepA. replace k with 0 by lia. cstep. zstepA. zstepA. zstepA. if_cases K3; zify_cond K3.
    + rewrite Z.max_l by lia. apply evtA_done. reflexivity.
    + zstepA. rewrite Z.max_r by lia. apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (lo hi n B : Z) (TSD CTX T : Z).
Definition INST : Z := 0xaa518.
#[local] Notation usp := (bv_unsigned sp).

Hypothesis SK : stk asegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 512.
Hypothesis SPH : bv_unsigned sp <= hi.
Hypothesis HI : hi < 2^47.
Hypothesis MI : mem_inv asegs m.
Hypothesis Hn : 1 <= n <= 2^27.
Hypothesis HB : bv_unsigned sp <= B /\ B + 16 <= hi.            (* [comment removed for export] *)
Hypothesis IMX : rw_cells asegs m 0xab338 [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048); C1 (Z_to_bv 8 1)].
                 (* [comment removed for export] *)
Hypothesis AI : rw_cells asegs m 0xae858 [C1 (Z_to_bv 8 1)].                 (* [comment removed for export] *)
Hypothesis RSS : rw_cells asegs m 0x12fde2 [C1 (Z_to_bv 8 0)].                (* [comment removed for export] *)
Hypothesis TC : thread_cells m tp TSD CTX T.
Hypothesis HTSD : 0x5cfdd0 <= TSD /\ TSD + 8 <= 0x603000.              (* [comment removed for export] *)
Hypothesis HCTX : placed CTX 4096.                                    (* [comment removed for export] *)
Hypothesis HT : placed_s T 4096 /\ T mod 8 = 0.                      (* [comment removed for export] *)
Hypothesis HTP : 0x5cfdd0 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 60 <= 0x603000.   (* [comment removed for export] *)
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= hi -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : forall a k, CTX <= a -> a + Z.of_nat k <= CTX + 160 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition frameA (m1 : mem) (junk : list byte) : Prop :=
  rw_cells asegs m1 (bv_unsigned sp + -128)
    [CB 8 junk; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition segA5_post : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a4' a5' a6' a7' s8' t3' t4' t5' t6' : word) m1 junk,
    ms = MS (mkR (Z_to_bv 64 0x32ea0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n)
                 (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (needed n)) (Z_to_bv 64 8) a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) s8'
                 (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
            F (Z_to_bv 64 0x372a0) fc None m1 (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
    /\ stk asegs m1 lo (bv_unsigned sp + -128) /\ frameA m1 junk.

Lemma alloc5_segA :
  evtA asegs P segA5_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 B) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x32c00) fc None m (seg_rom asegs)).
Proof.
  pose proof LOC as LOCu. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof HCTX as NCTX. unfold placed, A_IMG_END in NCTX. pose proof HT as ((NT1 & NT2 & _) & _).
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  pose proof (rounded_ge n) as (RG1 & RG2 & RG3). pose proof (rz_size_pos n) as RZP. pose proof (rz_log_range n) as RZL.
  unfold INST in *.
  assert (MU : munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 128%nat SK.
  do 14 cstep.                        (* [comment removed for export] *)
  do 6 cstep.                         (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  eapply evtA_cut; [eapply asan_inited_walk; [exact MI| exact AI| exact PDAT]|]. cbv beta. intros ms' ->. ret_pc_lit.
  cstep.                              (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  eapply evtA_cut; [eapply rss_walk; [exact MI| exact RSS| exact PDAT]|]. cbv beta. intros ms' (a1x & ->). ret_pc_lit.
  cstep.                              (* [comment removed for export] *)
  br1'.                               (* [comment removed for export] *)
  zstepA. cstep.                      (* [comment removed for export] *)
  do 2 zstepA. cstep.                 (* [comment removed for export] *)
  do 2 zstepA. cstep.                 (* [comment removed for export] *)
  do 13 zstepA.                       (* [comment removed for export] *)
  zstepA. cstep.                      (* [comment removed for export] *)
  do 3 zstepA. cstep.                 (* [comment removed for export] *)
  do 4 zstepA.                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evtA_cut; [eapply rz_ladder; exact Hn|]. cbv beta. intros ms' (a0x & ->).
  (* [comment removed for export] *)
  do 5 zstepA.                        (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  call_spA (rzs2log_walk P 0); [eassumption| exact LOC| arith| arith| eassumption| intros; apply PSTK; arith| exact PRO| clear; lia| reflexivity|].
  do 4 zstepA.                        (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  call_spA (rzs2log_walk P 7); [eassumption| exact LOC| arith| arith| eassumption| intros; apply PSTK; arith| exact PRO| clear; lia| reflexivity|].
  (* [comment removed for export] *)
  eapply evtA_cut; [eapply (rz_stretch (rz_log n) n); [exact RZL| exact Hn]|]. cbv beta. intros ms' ->.
  (* [comment removed for export] *)
  do 8 (zstepA; litc).                (* [comment removed for export] *)
  rewrite (rounded_land_max n) by (clear -Hn; lia).
  zstepA.                             (* [comment removed for export] *)
  replace (Z.land (rounded n) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); change (2^3) with 8; clear -RG3; lia).
  cstep.                              (* [comment removed for export] *)
  zstepA. zstepA.                     (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; clear -Hn; lia); cbn [Z.b2z]; rewrite ?Z.add_0_r.
  (zstepA; litc).                     (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  rewrite (sllw_rz_size n).
  zstepA. zstepA. rewrite ?Z.add_0_r.  (* [comment removed for export] *)
  (zstepA; litc).                     (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  change (rounded n + rz_size n) with (needed1 n).
  pose proof (needed_range n Hn) as NR. pose proof (eq_refl (needed n)) as NV. unfold needed in NV at 1.
  zstepA.                             (* [comment removed for export] *)
  try rewrite (Z.mod_small (needed1 n) 18446744073709551616) by (clear -NR; lia).
  rewrite (from_primary_ltb n).
  destruct (from_primary n) eqn:FP; cbn [Z.b2z].
  all: (zstepA; litc).                (* [comment removed for export] *)
  all: (zstepA; litc).                (* [comment removed for export] *)
  all: zstepA.                        (* [comment removed for export] *)
  1: rewrite Z.land_0_l.
  2: rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones, (Z.mod_small (rz_size n) (2^64)) by (clear -RZP; lia).
  all: (zstepA; litc).                (* [comment removed for export] *)
  all: zstepA.                        (* [comment removed for export] *)
  1: rewrite Z.add_0_l. 2: replace (rz_size n + needed1 n) with (needed1 n + rz_size n) by (clear; lia).
  all: rewrite NV.
  all: br1'.                          (* [comment removed for export] *)
  all: br1'.                          (* [comment removed for export] *)
  all: zstepA.                        (* [comment removed for export] *)
  all: br2'.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: cstep.                         (* [comment removed for export] *)
  all: (call_spA (get_current_thread_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
    [ eassumption| exact LOC| arith| arith| eassumption| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| arith| arith| arith| arith| arith| arith
    | intros; apply PSTK; arith| exact PDAT| apply PCTX; arith|]).
  all: zstepA.                        (* [comment removed for export] *)
  all: (zstepA; if_cases K0; zify_cond K0; [kill K0| clear K0]).   (* [comment removed for export] *)
  all: do 4 zstepA.                   (* [comment removed for export] *)
  all: cstep.                         (* [comment removed for export] *)
  all: apply evtA_done; unfold segA5_post, frameA; rewrite FP; cbn [Z.b2z];
       do 14 eexists; split; [reflexivity|];
       split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption| eassumption].
Qed.
End ALLOC.
End RC__1.
