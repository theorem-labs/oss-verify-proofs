(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2252 of its 2377 lines of code are new or changed and 886 lines of the source are left out. *)
(* Segment R10 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A), arms b = 0, 1, 2 (block sum) and b = 3, 4 (reply),
   from the entry cut 0x81680 (after reac_ctrl_parse) to the exit cuts 0x81768 (b = 0), 0x817ec (b = 1, 2) and 0x816c4
   (b = 3, 4).  rule 24: no function proved (a slot segment; reac_ctrl_identity_reply is a Section hypothesis on its
   contract).

   Common head 0x81680 .. 0x8169c: li a3,2; sb a3,306(s3); sb zero,308(s3); sb zero,312(s3) (S(fr) + 306 / 308 / 312:
   the reply cells fr + 2448 (2 bytes), fr + 2464 (8) and fr + 2496 (8) made addressable); li a2,4; blt s11,s7 (s11 = 4,
   not taken for b <= 4); addi a1,s7,-3; bgeu a1,a3.
     b = 3, 4: bgeu not taken; li a1,5; beq a0,a1 taken (a0 = rt_k = 5, B3Rtm.a_rtm_k5), so the abort edge 0x816a8 is
               not reached; 0x816ac .. 0x816bc a0 = s8 = Phi, a1 = s2 = n_b, a2 / a3 / a4 = [A + 88] / [A + 80] /
               [A + 72]; jal reac_ctrl_identity_reply (0x83ec4) on its contract, back at 0x816c4.
     b = 0:    bgeu taken; 0x81740 bnez s7 not taken; sb zero,316(s3); sb a2,317(s3) (fr + 2528's 12 bytes
               addressable); li a1,9; beq a0,a1 taken (a_rtm_k0), abort 0x81754 not reached; the block-sum prologue
               li a1,0; addi a2,s8,18; li a3,32; mv a0,a2 -> 0x81768.
     b = 1, 2: bgeu taken; bnez s7 taken -> 0x817d0 li a1,5; beq a0,a1 taken (a_rtm_k5), abort 0x817d8 not reached;
               the same prologue -> 0x817ec.
   The machine runs are Lib-level evt lemmas (r10a_evt0, r10a_evt12, r10a_head34, r10a_call34); the segment lemmas
   r10a_b0 / r10a_b12 / r10a_b34 move FRA and ENT across every write by one landing lemma r10a_land (the write set
   inside the frame shadow, the frame records, the callee window, the class-1 side-stack bytes and the shadow of the
   last two), and carry each cut fact across by its own address range.  The reply's side-stack package (fp [1] / tls)
   is on no cut: Tac_fsfree.fra_fp derives it from FRA at 0x816ac (r10a_b34). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memset asan_memcpy.
Import ListNotations.
Open Scope Z_scope.

(* ======================= Lib-level runs ======================= *)

Lemma r10a_le1_lit : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite MState.unsigned_lit by lia. reflexivity. Qed.

Lemma r10a_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

(* A one-byte store `sb r,o(s3)` writes `le1 r`; the engine records it in the shadow cells once it is a byte list. *)
Ltac r10a_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (r10a_le1_lit z) by lia; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (r10a_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac r10a_sb := step; r10a_fix.

(* One byte of a byte-list fact, by its index (image B's r10_bat_idx). *)
Lemma r10a_bat_idx : forall m a l (i : nat) (x : byte) (b : Z),
  bytes_at rsegs m a l -> nth_error l i = Some x -> b = a + Z.of_nat i -> bytes_at rsegs m b [x].
Proof.
  intros m a l i x b (H0 & H1 & H) Hx ->.
  assert (Hi : (i < length l)%nat) by (apply nth_error_Some; rewrite Hx; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros j Hj. cbn [length] in Hj. assert (Ej : j = 0%nat) by lia. subst j.
  rewrite Z.add_0_r. rewrite (H i Hi). cbn [nth_error]. exact Hx.
Qed.

(* branch conditions (the boolean the engine tests at each conditional branch; a Theorem Labs lane's R10) *)
Lemma r10a_sgn : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite ZBridge.zb_signed, MState.unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt z (2 ^ 63))) by lia. reflexivity.
Qed.

Lemma r10a_blt_f : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> y <= x ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy Hle. unfold bv_lts. rewrite !r10a_sgn by lia. apply Z.ltb_ge. lia. Qed.

Lemma r10a_bgeu_t : forall x y, bv_unsigned (Z_to_bv 64 y) <= bv_unsigned (Z_to_bv 64 x) ->
  negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof.
  intros x y H. apply (proj2 (Bool.negb_true_iff _)). unfold bv_ltu. apply Z.ltb_ge. exact H.
Qed.

Lemma r10a_bgeu_f : forall x y, bv_unsigned (Z_to_bv 64 x) < bv_unsigned (Z_to_bv 64 y) ->
  negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
Proof.
  intros x y H. apply (proj2 (Bool.negb_false_iff _)). unfold bv_ltu. apply Z.ltb_lt. exact H.
Qed.

Lemma r10a_beq_t : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof.
  intros x y Hx Hy ->. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_eq. reflexivity.
Qed.

Lemma r10a_bne_t : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof.
  intros x y Hx Hy Hne. apply (proj2 (Bool.negb_true_iff _)). unfold bv_eqb.
  rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. exact Hne.
Qed.

Lemma r10a_bne_f : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
Proof.
  intros x y Hx Hy ->. apply (proj2 (Bool.negb_false_iff _)). unfold bv_eqb.
  rewrite !MState.unsigned_lit by lia. apply Z.eqb_eq. reflexivity.
Qed.

(* ---- arm b = 0: 0x81680 .. 0x81740 (bnez s7 not taken) .. 0x81764, to the block-sum head 0x81768.  Writes the five
   frame-shadow bytes S(fr) + 306, 308, 312, 316, 317, all inside [S(fr) + 306, S(fr) + 318). ---- *)
Lemma r10a_evt0 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh phi : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 0 -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 9 ->
    s8 = Z_to_bv 64 phi -> 0 <= phi -> phi + 18 < 2 ^ 64 -> 0 <= Sh -> Sh + 318 <= 2 ^ 64 ->
    length xs = 12%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l12 : list byte) (c4 c5 : byte),
         ms' = MS R F (Z_to_bv 64 0x81768) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 13 = Z_to_bv 64 32 /\
         munch [(Sh + 306, Sh + 318)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) l12 /\ length l12 = 12%nat /\
         bytes_at rsegs m' (Sh + 316) [c4] /\ bv_signed c4 = 0 /\
         bytes_at rsegs m' (Sh + 317) [c5] /\ bv_signed c5 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh phi xs -> -> -> -> -> Hphi0 Hphi1 HSh0 HSh1 Hxs CH.
  do 12 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (munch_refl [(Sh + 306, Sh + 318)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  step.
  r10a_sb. r10a_sb. r10a_sb.
  step.
  step. if_false_by (r10a_blt_f 4 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  step. if_true_by (r10a_bgeu_t (0 + -3) 2 ltac:(rewrite !MState.unsigned_lit_wrap; lia)).
  step. if_false_by (r10a_bne_f 0 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  r10a_sb. r10a_sb.
  step.
  step. if_true_by (r10a_beq_t 9 9 ltac:(lia) ltac:(lia) ltac:(lia)).
  step. step. step. step.
  destruct CH as ((Hwfc & Hbc) & Hwrc). cbn [cells_bytes cbytes app] in Hbc.
  apply evt_done. do 5 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact Hbc|]. split; [reflexivity|].
  split; [exact (r10a_bat_idx _ _ _ 10%nat _ (Sh + 316) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  split; [vm_compute; reflexivity|].
  split; [exact (r10a_bat_idx _ _ _ 11%nat _ (Sh + 317) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  vm_compute; reflexivity.
Qed.

(* ---- arm b = 1, 2: 0x81680 .. 0x81740 (bnez s7 taken) .. 0x817d0 .. 0x817e8, to the block-sum head 0x817ec.
   Writes the three frame-shadow bytes S(fr) + 306, 308, 312. ---- *)
Lemma r10a_evt12 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh phi bb : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 bb -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 5 ->
    s8 = Z_to_bv 64 phi -> 1 <= bb <= 2 -> 0 <= phi -> phi + 18 < 2 ^ 64 -> 0 <= Sh -> Sh + 313 <= 2 ^ 64 ->
    length xs = 7%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l7 : list byte),
         ms' = MS R F (Z_to_bv 64 0x817ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 13 = Z_to_bv 64 32 /\
         munch [(Sh + 306, Sh + 313)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh phi bb xs -> -> -> -> -> Hbb Hphi0 Hphi1 HSh0 HSh1 Hxs CH.
  do 7 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (munch_refl [(Sh + 306, Sh + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  step.
  r10a_sb. r10a_sb. r10a_sb.
  step.
  step. if_false_by (r10a_blt_f 4 bb ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  step. if_true_by (r10a_bgeu_t (bb + -3) 2 ltac:(rewrite !MState.unsigned_lit_wrap; lia)).
  step. if_true_by (r10a_bne_t bb 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  step. if_true_by (r10a_beq_t 5 5 ltac:(lia) ltac:(lia) ltac:(lia)).
  step. step. step. step.
  destruct CH as ((Hwfc & Hbc) & Hwrc). cbn [cells_bytes cbytes app] in Hbc.
  apply evt_done. do 3 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact Hbc | reflexivity].
Qed.

(* ---- arm b = 3, 4, head: 0x81680 .. 0x81694 (blt not taken) .. 0x8169c (bgeu not taken, b - 3 in {0, 1}) ..
   0x816a4 (beq a0,5 taken) to 0x816ac.  Writes S(fr) + 306 = 2, 308 = 0, 312 = 0. ---- *)
Lemma r10a_head34 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh bb : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 bb -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 5 ->
    3 <= bb <= 4 -> 0 <= Sh -> Sh + 313 <= 2 ^ 64 ->
    length xs = 7%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS R F (Z_to_bv 64 0x816ac) fc None m' (seg_rom rsegs) /\
         R = mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (getr R 11) (getr R 12) (getr R 13) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 /\
         munch [(Sh + 306, Sh + 313)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m' (Sh + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m' (Sh + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m' (Sh + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh bb xs E3 E7 E11 E0 Hbb HSh0 HSh1 Hxs CH.
  subst s3 s7 s11 a0.
  do 7 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (munch_refl [(Sh + 306, Sh + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  step.
  r10a_sb. r10a_sb. r10a_sb.
  step.
  step. if_false_by (r10a_blt_f 4 bb ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  step. if_false_by (r10a_bgeu_f (bb + -3) 2 ltac:(rewrite !MState.unsigned_lit_wrap; lia)).
  step.
  step. if_true_by (r10a_beq_t 5 5 ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct CH as ((Hwfc & Hbc) & Hwrc). cbn [cells_bytes cbytes app] in Hbc.
  apply evt_done. do 6 eexists.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact (r10a_bat_idx _ _ _ 0%nat _ (Sh + 306) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  split; [vm_compute; reflexivity|].
  split; [exact (r10a_bat_idx _ _ _ 2%nat _ (Sh + 308) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  split; [vm_compute; reflexivity|].
  split; [exact (r10a_bat_idx _ _ _ 6%nat _ (Sh + 312) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  split; [vm_compute; reflexivity|].
  split; [exact Hbc | reflexivity].
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs B3Rtm.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module AMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset.
Module AMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy.

(* ======================= memory and shadow helpers ======================= *)

Lemma r10a_out_dec : forall W x, LF.outside W x \/ ~ LF.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [LF.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma r10a_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma r10a_ba_sub : forall m A bs k j, bytes_at rsegs m A bs -> (k + j <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma r10a_C1 : forall l, cells_wf (map C1 l) /\ cells_bytes (map C1 l) = l /\ cells_size (map C1 l) = length l.
Proof.
  induction l as [|b l (H1 & H2 & H3)]; cbn [map cells_wf cell_wf cells_bytes cbytes cells_size csize length];
    [split; [exact I | split; reflexivity]|].
  split; [split; [exact I | exact H1]|]. split; [cbn [app]; rewrite H2; reflexivity | rewrite H3; reflexivity].
Qed.

Lemma r10a_rw_C1 : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A (map C1 l).
Proof.
  intros m A l Hb Hw. destruct (r10a_C1 l) as (H1 & H2 & H3).
  split; [split; [exact H1 | rewrite H2; exact Hb] | rewrite H3; exact Hw].
Qed.

Lemma r10a_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma r10a_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

Lemma r10a_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> LF.munch W m m' -> LF.wmono rsegs m m' ->
  (forall x, lo <= x < hi -> LF.outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r10a_addr_keep : forall W m m' p n, addressable m p n -> LF.munch W m m' ->
  (forall i, 0 <= i < n -> LF.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

Lemma r10a_addr_byte : forall m p n a, addressable m p n -> p <= a < p + n -> addressable m a 1.
Proof.
  intros m p n a (H0 & H1 & H2 & H) Ha. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (p + (a - p + i)) by lia. apply H. lia.
Qed.

Lemma r10a_addr_cat : forall m p n k, addressable m p n -> addressable m (p + n) k -> addressable m p (n + k).
Proof.
  intros m p n k (H1 & H2 & H3 & H) (K1 & K2 & K3 & K). split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n) as [Hl|Hg]; [apply H; lia|].
  replace (p + i) with (p + n + (i - n)) by lia. apply K. lia.
Qed.

(* The n bytes at fr + k (in one granule of a 32-aligned frame) are addressable when their shadow byte b is 0 or
   at least n (F9's l7_addr_cell). *)
Lemma r10a_addr_cell : forall m fr k n (b : byte), fr mod 32 = 0 -> 0 <= fr -> k mod 8 = 0 -> 0 <= k -> 0 <= n <= 8 ->
  (forall a, fr + k <= a < fr + k + n -> app_mem a) -> fr + k + n <= APPMEM_END ->
  bytes_at rsegs m (Sfr fr + k / 8) [b] ->
  (bv_signed b = 0 \/ n <= bv_signed b <= 7) ->
  addressable m (fr + k) n.
Proof.
  intros m fr k n b Hm H0 Hk Hk0 Hn Happ Hend (_ & _ & Hb) Hv.
  pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as E. cbn [nth_error] in E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|]. exists b. split.
  - replace (shadow_addr (fr + k + i)) with (Sfr fr + k / 8); [exact E|].
    unfold Sfr, shadow_addr. clear - Hm Hk Hk0 H0 Hi Hn. Z.div_mod_to_equations. lia.
  - unfold shadow_ok. destruct Hv as [Hv|Hv]; [left; exact Hv | right].
    split; [|lia]. clear - Hm Hk Hk0 H0 Hi Hn Hv. Z.div_mod_to_equations. lia.
Qed.

Lemma r10a_rw_keep : forall W m m' a n l, rw_cells rsegs m a [CB n l] -> LF.munch W m m' -> LF.wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat n -> LF.outside W x) -> rw_cells rsegs m' a [CB n l].
Proof.
  intros W m m' a n l ((Hwf & Hb) & Hw) MU WM Hd. split; [split; [exact Hwf|]|].
  - cbn [cells_bytes cbytes] in Hb |- *. rewrite app_nil_r in Hb |- *.
    cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Hl & _).
    eapply fl_bytes; [exact Hb | exact MU |]. rewrite Hl. exact Hd.
  - destruct Hw as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (WM _ (H i Hi)).
Qed.

Lemma r10a_wm_uniq : forall m a u v, word_mem rsegs m a u -> word_mem rsegs m a v ->
  0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u = v.
Proof.
  intros m a u v Hu Hv Hur Hvr.
  assert (Hb : forall k, (k < 8)%nat -> le_byte u 8 k = le_byte v 8 k).
  { intros k Hk. pose proof (Hu k Hk) as Eu. pose proof (Hv k Hk) as Ev.
    rewrite Eu in Ev.
    assert (Eb : Z_to_bv 8 (le_byte u 8 k) = Z_to_bv 8 (le_byte v 8 k)) by congruence.
    apply (f_equal bv_unsigned) in Eb. rewrite !kb_byte_unsigned in Eb. exact Eb. }
  rewrite (kb_le8_digits u Hur), (kb_le8_digits v Hvr).
  rewrite (Hb 0%nat), (Hb 1%nat), (Hb 2%nat), (Hb 3%nat), (Hb 4%nat), (Hb 5%nat), (Hb 6%nat), (Hb 7%nat)
    by lia.
  reflexivity.
Qed.

(* The spill base is the A of register 9 (the two agree mod 2^64 and both lie in range). *)
Lemma r10a_spill_at : forall (regs : bvmap 5 word) (mem : word -> option byte) (A off v : Z),
  rg regs 9 A -> 0 <= A -> A + 416 < 2 ^ 64 -> 0 <= off <= 416 -> spill regs mem off v ->
  q64 mem (A + off) v.
Proof.
  intros regs mem A off v Hr HA0 HA1 Hoff (A' & Hr' & Hq).
  pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
  pose proof (rg_eq64 regs 9 A' A Hr' Hr) as Hm.
  change (2 ^ 64) with 18446744073709551616 in *.
  assert (A' = A) by (Z.div_mod_to_equations; lia).
  subst A'. exact Hq.
Qed.

(* A spill word survives a write W that misses the 416-byte save area at the base A of register 9. *)
Lemma r10a_spill_keep : forall regs regs' m m' W A off v,
  getr regs' 9 = getr regs 9 -> rg regs 9 A -> 0 <= A -> A + 416 < 2 ^ 64 -> 0 <= off <= 408 ->
  LF.munch W m m' -> (forall x, A <= x < A + 416 -> LF.outside W x) ->
  spill regs m off v -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v E9 Hr HA0 HA1 Hoff MU HO Hs.
  pose proof (r10a_spill_at regs m A off v Hr HA0 HA1 ltac:(lia) Hs) as Hq.
  exists A. split; [unfold rg in *; rewrite E9; exact Hr|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8. intros x Hx. apply HO. lia.
Qed.

(* ---- shadow arithmetic ---- *)
Lemma r10a_sh_eq : forall y, shadow_addr y = y / 8 + 2147450880.
Proof. intros y. reflexivity. Qed.

Lemma r10a_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r10a_sh_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. rewrite !r10a_sh_eq. pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia. Qed.

Lemma r10a_sh_out : forall lo hi a, lo mod 8 = 0 -> hi mod 8 = 0 -> ~ (lo <= a < hi) ->
  shadow_addr a < shadow_addr lo \/ shadow_addr hi <= shadow_addr a.
Proof. intros lo hi a Hl Hh Ha. rewrite !r10a_sh_eq. Z.div_mod_to_equations. lia. Qed.

Lemma r10a_sh_inv : forall lo hi x, shadow_addr lo <= x < shadow_addr hi ->
  lo - 8 < 8 * (x - 2147450880) < hi /\ shadow_addr (8 * (x - 2147450880)) = x.
Proof.
  intros lo hi x Hx. rewrite !r10a_sh_eq in *.
  assert (Hdv : 8 * (x - 2147450880) / 8 = x - 2147450880) by (rewrite Z.mul_comm, Z.div_mul; lia).
  rewrite Hdv. split; [|lia]. Z.div_mod_to_equations. lia.
Qed.

Lemma r10a_sh_band : forall y, 0 <= y -> y <= 140737488355328 ->
  2147450880 + y / 8 = shadow_addr y /\ 2147450880 <= shadow_addr y <= 17594333495296.
Proof.
  intros y H0 H1. rewrite r10a_sh_eq. split; [lia|].
  pose proof (Z.div_pos y 8 H0 ltac:(lia)). pose proof (Z.div_le_mono y 140737488355328 8 ltac:(lia) H1) as D.
  change (140737488355328 / 8) with 17592186044416 in D. lia.
Qed.

Lemma r10a_Sfr_band : forall fr, 6283264 <= fr -> fr + FRAME_BYTES <= 140737488355328 ->
  2147450880 + 785408 <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= 17594333495296.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros fr H0 H1. unfold Sfr. rewrite r10a_sh_eq.
  pose proof (Z.div_le_mono 6283264 fr 8 ltac:(lia) H0) as D0.
  pose proof (Z.div_le_mono (fr + FRAME_BYTES) 140737488355328 8 ltac:(lia) H1) as D1.
  replace (fr + FRAME_BYTES) with (fr + FRAME_SHADOW * 8) in D1 by lia. rewrite Z.div_add in D1 by lia.
  change (6283264 / 8) with 785408 in D0. change (140737488355328 / 8) with 17592186044416 in D1. lia.
Qed.

Lemma r10a_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW -> in_shadow (Sfr fr + k).
Proof. pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs. intros fr k Happ Hk. rewrite <- r10a_sh8. apply shadow_of_app. apply Happ. lia. Qed.

(* The instrumented globals of the image lie in [0x21140, 0x9f8e8), and so do their shadow bytes' preimages. *)
Lemma r10a_ag_range : forall a, in_globals AFw.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AFw.frame_AG in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma r10a_glob_sh : forall a, 0x21140 <= a < 0x9f8e8 ->
  2147450880 + 16936 <= shadow_addr a <= 2147450880 + 81693.
Proof. intros a Ha. rewrite r10a_sh_eq. Z.div_mod_to_equations. lia. Qed.

(* The shadow byte of an image byte (below GT) or of a byte at or above the entry sp S misses the shadow of the
   class-1 side-stack frames [FS + 1085440, FS + 2134016) and the shadow of a callee window [lo, hi) below S
   (R6's r6_band). *)
Lemma r10a_band : forall FS lo hi S b,
  6283264 <= FS -> FS + 2134016 <= S -> 17594333495296 <= lo -> lo <= hi -> hi <= S ->
  (0 <= b < 6283264 \/ S <= b) ->
  ~ (shadow_addr (FS + 1085440) <= shadow_addr b < shadow_addr (FS + 2134016)) /\
  ~ (shadow_addr lo <= shadow_addr b < shadow_addr hi).
Proof.
  intros FS lo hi S b H1 H2 H3 H4 H5 Hb.
  assert (M : forall x y, x <= y -> x / 8 <= y / 8) by (intros x y Hxy; apply Z.div_le_mono; lia).
  rewrite !r10a_sh_eq. destruct Hb as [Hb|Hb].
  - pose proof (M b 6283263 ltac:(lia)) as E1. pose proof (M (6283264 + 1085440) (FS + 1085440) ltac:(lia)) as E2.
    pose proof (M 17594333495296 lo ltac:(lia)) as E3.
    change (6283263 / 8) with 785407 in E1. change ((6283264 + 1085440) / 8) with 921088 in E2.
    change (17594333495296 / 8) with 2199291686912 in E3. lia.
  - pose proof (M (FS + 2134016) b ltac:(lia)) as E1. pose proof (M hi b ltac:(lia)) as E2. lia.
Qed.

(* ---- the read-only image and the normalized memory (R3 / R6) ---- *)
Definition r10a_tops (sg : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sg.

Lemma r10a_rsegs_below : r10a_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r10a_fseg_below : forall sg top x n s,
  r10a_tops sg top = true -> find_segment sg x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sg as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold r10a_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr]. apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma r10a_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (r10a_fseg_below sg 0x5fe000 x n s r10a_rsegs_below E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma r10a_ro_hi_w : forall x : word, 0x5fe000 <= bv_unsigned x -> ro_addr rsegs x = false.
Proof.
  intros x Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite <- (Z_to_bv_bv_unsigned x). apply r10a_ro_hi. lia.
Qed.

Lemma r10a_ro_munch : forall W m m', ro_agree rsegs m -> LF.munch W m m' ->
  (forall x, ~ LF.outside W x -> 0x5fe000 <= x) -> ro_agree rsegs m'.
Proof.
  intros W m m' HRO MU HW a Ha.
  destruct (r10a_out_dec W (bv_unsigned a)) as [Ho|Hno].
  - unfold mrd. rewrite (MU a Ho). exact (HRO a Ha).
  - rewrite (r10a_ro_hi_w a (HW _ Hno)) in Ha. discriminate Ha.
Qed.

Lemma r10a_wv_hi : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r10a_ro_hi a Ha)). split; auto.
Qed.

Lemma r10a_stk_iff : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi. split; intros (H0 & H1 & H); (split; [lia|]); (split; [lia|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb); split.
  - apply (proj2 (r10a_wv_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
  - apply (proj1 (r10a_wv_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r10a_shadow_iff : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 HR. split; intros H a Ha; pose proof (in_shadow_range a Ha) as Hr;
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha;
    destruct (H a Ha) as (Hw & b & Hb); split.
  - apply (proj2 (r10a_wv_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
  - apply (proj1 (r10a_wv_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r10a_addr_iff : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n HR. split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]);
    (split; [exact H2|]); intros i Hi; destruct (H i Hi) as (Hap & b & Hb & Hok); split; try exact Hap;
    exists b.
  - rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
  - rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma r10a_fsplace_iff : forall m m0 FS, mem_rel rsegs m m0 -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  (fs_place m FS <-> fs_place m0 FS).
Proof.
  intros m m0 FS HR Hlo Hhi. split; intros (P1 & P2 & P3 & P4 & P5);
    (split; [exact P1|]); (split; [exact P2|]); (split; [exact P3|]); (split; [exact P4|]).
  - exact (proj1 (r10a_stk_iff m m0 FS (FS + FS_SIZE) HR Hlo Hhi) P5).
  - exact (proj2 (r10a_stk_iff m m0 FS (FS + FS_SIZE) HR Hlo Hhi) P5).
Qed.

Lemma r10a_ac_iff : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 R. unfold asan_cells. split; intros H;
    repeat match goal with H' : _ /\ _ |- _ => destruct H' end;
    repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs =>
      first [ exact (proj1 (bytes_at_rel rsegs m m0 a bs R) ltac:(assumption))
            | exact (proj2 (bytes_at_rel rsegs m m0 a bs R) ltac:(assumption)) ] end.
Qed.

Lemma r10a_tls_iff : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k R.
  assert (BF : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs H; exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H)).
  assert (BB : forall a bs, bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs)
    by (intros a bs H; exact (proj2 (bytes_at_rel rsegs m m0 a bs R) H)).
  unfold asan_tls_cells.
  split; intros (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19);
    repeat (split;
      [ solve [ first [ assumption
                      | apply BF; assumption
                      | apply BB; assumption
                      | exists tb, te; first [apply BF; assumption | apply BB; assumption] ] ] | ]);
    solve [ first [ assumption
                  | apply BF; assumption
                  | apply BB; assumption
                  | exists tb, te; first [apply BF; assumption | apply BB; assumption] ] ].
Qed.

Lemma r10a_cls_iff : forall m m0 FS c, mem_rel rsegs m m0 -> (fp_cls m FS c <-> fp_cls m0 FS c).
Proof.
  intros m m0 FS c R.
  assert (BF : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs H; exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H)).
  assert (BB : forall a bs, bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs)
    by (intros a bs H; exact (proj2 (bytes_at_rel rsegs m m0 a bs R) H)).
  unfold fp_cls.
  split; intros (Hc & h & flags & H1 & H2 & H3 & H4);
    (split; [exact Hc|]); exists h, flags;
    (split; [first [apply BF; assumption | apply BB; assumption]|]);
    (split; [first [apply BF; assumption | apply BB; assumption]|]);
    (split; [exact H3 | exact H4]).
Qed.

Lemma r10a_fp_iff : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D R Hlo Hhi. unfold fp. split;
    intros (DT & TS & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10);
    exists DT, TS, C, T, DB, k.
  - split; [exact (proj1 (r10a_tls_iff m m0 _ _ _ _ _ _ _ R) H1)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ R) H2)|].
    split; [exact (proj1 (r10a_fsplace_iff m m0 FS R Hlo Hhi) H3)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ R) H4)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ R) H5)|].
    split; [eapply Forall_impl; [|exact H6]; intros c Hc; exact (proj1 (r10a_cls_iff m m0 FS c R) Hc)|].
    split; [exact H7|]. split; [exact H8|]. split; [exact H9 | exact H10].
  - split; [exact (proj2 (r10a_tls_iff m m0 _ _ _ _ _ _ _ R) H1)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ R) H2)|].
    split; [exact (proj2 (r10a_fsplace_iff m m0 FS R Hlo Hhi) H3)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ R) H4)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ R) H5)|].
    split; [eapply Forall_impl; [|exact H6]; intros c Hc; exact (proj2 (r10a_cls_iff m m0 FS c R) Hc)|].
    split; [exact H7|]. split; [exact H8|]. split; [exact H9 | exact H10].
Qed.

Lemma r10a_rtls_iff : forall m m0 TP FS lo hi, mem_rel rsegs m m0 ->
  (reac_ctrl_identity_reply_tls m TP FS lo hi <-> reac_ctrl_identity_reply_tls m0 TP FS lo hi).
Proof.
  intros m m0 TP FS lo hi R. unfold reac_ctrl_identity_reply_tls. split; intros H DT TS C T DB k HT.
  - apply (H DT TS C T DB k). exact (proj2 (r10a_tls_iff m m0 TP DT TS C T DB k R) HT).
  - apply (H DT TS C T DB k). exact (proj1 (r10a_tls_iff m m0 TP DT TS C T DB k R) HT).
Qed.

Lemma r10a_rw_norm : forall m m0 A cs, mem_rel rsegs m m0 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs m A cs -> rw_cells rsegs m0 A cs.
Proof.
  intros m m0 A cs REL HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj1 (bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (wr_at_norm rsegs m m0 A _ REL Hw HR).
Qed.

Lemma r10a_rw_back : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs REL ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (wr_at_rel rsegs m m0 A _ REL Hw).
Qed.

(* A spilled word is a read-only cell for the load engine. *)
Lemma r10a_q64_ro : forall (m : word -> option byte) (A v : Z),
  bytes_at rsegs m A (le8 (Z_to_bv 64 v)) -> ro_cells rsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v H. split; [split; [exact I | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H].
Qed.

(* ---- side-stack geometry, class 1 (F9's l1_* lemmas) ---- *)
Lemma r10a_fs_hint1 : forall FS, fs_hint FS 1%nat = FS + 8.
Proof. intros FS. unfold fs_hint. cbn [Z.of_nat]. lia. Qed.

Lemma r10a_fs_flag1 : forall FS, fs_flag FS 1%nat 0 = FS + 20480.
Proof.
  intros FS. unfold fs_flag. cbn [Z.of_nat]. change (2 ^ 15) with 32768.
  change (2 ^ (15 - 1)) with 16384. lia.
Qed.

Lemma r10a_fs_frame1_0 : forall FS, fs_frame FS 1%nat 0 = FS + 1085440.
Proof.
  intros FS. unfold fs_frame. replace (fs_B 1%nat) with 128 by reflexivity. cbn [Z.of_nat].
  change (2 ^ 20) with 1048576. lia.
Qed.

Lemma r10a_fs_frame1_M : forall FS, fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016.
Proof.
  intros FS. unfold fs_frame. replace (fs_B 1%nat) with 128 by reflexivity.
  replace (fs_M 1%nat) with 8192 by reflexivity. cbn [Z.of_nat].
  change (2 ^ 20) with 1048576. lia.
Qed.

Lemma r10a_fpw1 : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. unfold fp_w. cbn [flat_map]. rewrite app_nil_r. unfold fp_w1.
  rewrite r10a_fs_hint1, r10a_fs_flag1, r10a_fs_frame1_0, r10a_fs_frame1_M.
  replace (fs_M 1%nat) with 8192 by reflexivity.
  replace (FS + 8 + 8) with (FS + 16) by lia.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

(* The call's write list and its pieces. *)
Definition r10a_WC (phi len fr spv FS : Z) (G : list byte) : list (Z * Z) :=
  reac_ctrl_identity_reply_fp phi len (fr + 2448) (fr + 2464) (fr + 2496) spv G ++ fp_w [1%nat] FS ++
  [(shadow_addr (spv - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr spv)].

Lemma r10a_WC_eq : forall phi len fr spv FS G, r10a_WC phi len fr spv FS G =
  (if reply_ok phi len (fr + 2448) (fr + 2464) (fr + 2496) G
   then [(fr + 2448, fr + 2448 + 2); (fr + 2464, fr + 2464 + 8); (fr + 2496, fr + 2496 + 8)] else []) ++
  [(spv - 9072, spv); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016)); (shadow_addr (spv - 9072), shadow_addr spv)].
Proof.
  intros phi len fr spv FS G. unfold r10a_WC, reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K.
  rewrite r10a_fpw1. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma r10a_out_WC : forall phi len fr spv FS G x,
  ~ (fr + 2448 <= x < fr + 2450) -> ~ (fr + 2464 <= x < fr + 2472) -> ~ (fr + 2496 <= x < fr + 2504) ->
  ~ (spv - 9072 <= x < spv) -> ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
  ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (spv - 9072) <= x < shadow_addr spv) ->
  LF.outside (r10a_WC phi len fr spv FS G) x.
Proof.
  intros phi len fr spv FS G x N1 N2 N3 N4 N5 N5' N6 N7 N8. rewrite r10a_WC_eq.
  destruct (reply_ok phi len (fr + 2448) (fr + 2464) (fr + 2496) G); cbn [app LF.outside];
    repeat split; try exact I; lia.
Qed.

Lemma r10a_rng_dec : forall lo hi x, {lo <= x < hi} + {~ (lo <= x < hi)}.
Proof.
  intros lo hi x. destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi);
    [left; lia | right; lia | right; lia | right; lia].
Qed.

(* A byte the call may write is in one of its nine ranges. *)
Lemma r10a_in_WC : forall phi len fr spv FS G x,
  ~ LF.outside (r10a_WC phi len fr spv FS G) x ->
  (fr + 2448 <= x < fr + 2450) \/ (fr + 2464 <= x < fr + 2472) \/ (fr + 2496 <= x < fr + 2504) \/
  (spv - 9072 <= x < spv) \/ (FS + 8 <= x < FS + 16) \/ (FS + 20480 <= x < FS + 28672) \/
  (FS + 1085440 <= x < FS + 2134016) \/
  (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) \/
  (shadow_addr (spv - 9072) <= x < shadow_addr spv).
Proof.
  intros phi len fr spv FS G x Hx.
  destruct (r10a_rng_dec (fr + 2448) (fr + 2450) x) as [H|N1]; [left; exact H|].
  destruct (r10a_rng_dec (fr + 2464) (fr + 2472) x) as [H|N2]; [right; left; exact H|].
  destruct (r10a_rng_dec (fr + 2496) (fr + 2504) x) as [H|N3]; [right; right; left; exact H|].
  destruct (r10a_rng_dec (spv - 9072) spv x) as [H|N4]; [do 3 right; left; exact H|].
  destruct (r10a_rng_dec (FS + 8) (FS + 16) x) as [H|N5]; [do 4 right; left; exact H|].
  destruct (r10a_rng_dec (FS + 20480) (FS + 28672) x) as [H|N6]; [do 5 right; left; exact H|].
  destruct (r10a_rng_dec (FS + 1085440) (FS + 2134016) x) as [H|N7]; [do 6 right; left; exact H|].
  destruct (r10a_rng_dec (shadow_addr (FS + 1085440)) (shadow_addr (FS + 2134016)) x) as [H|N8];
    [do 7 right; left; exact H|].
  destruct (r10a_rng_dec (shadow_addr (spv - 9072)) (shadow_addr spv) x) as [H|N9]; [do 8 right; exact H|].
  exfalso. apply Hx. exact (r10a_out_WC phi len fr spv FS G x N1 N2 N3 N4 N5 N6 N7 N8 N9).
Qed.

(* Small helpers for the reply arm. *)
Lemma r10a_stk_sub : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> stk rsegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' (H0 & H1 & H) Hl Hh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia.
Qed.

Lemma r10a_addr_sub : forall m p n k, addressable m p n -> 0 <= k <= n -> addressable m p k.
Proof.
  intros m p n k (H0 & H1 & H2 & H) Hk.
  split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.

Lemma r10a_addr_bytes1 : forall m p n, (forall a, p <= a < p + n -> addressable m a 1) ->
  0 <= p -> 0 <= n -> p + n <= APPMEM_END -> addressable m p n.
Proof.
  intros m p n H Hp Hn Hpn. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H (p + i) ltac:(lia)) as (_ & _ & _ & K).
  pose proof (K 0 ltac:(lia)) as Kb. rewrite Z.add_0_r in Kb. exact Kb.
Qed.

Lemma r10a_sh_ivl : forall lo hi x, (forall a, lo - 8 < a < hi -> app_mem a) ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  intros lo hi x Happ Hx. destruct (r10a_sh_inv lo hi x Hx) as (Hb & E).
  rewrite <- E. apply shadow_of_app. apply Happ. lia.
Qed.

Lemma r10a_rw_rd : forall m a n l x, rw_cells rsegs m a [CB n l] -> a <= x < a + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a n l x ((Hwf & Hb) & _) Hx. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Hl & _).
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  apply (r10a_ba_rd m a l x Hb). rewrite Hl. exact Hx.
Qed.

Lemma r10a_g50 : forall m phi l, (50 <= length l)%nat -> bytes_at rsegs m phi l -> bytes_at rsegs m phi (fr50 l).
Proof.
  intros m phi l Hl Hb. unfold fr50. rewrite firstn_app.
  replace (50 - length l)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  pose proof (r10a_ba_sub m phi l 0 50 Hb ltac:(lia)) as X. cbn [skipn] in X.
  replace (phi + Z.of_nat 0) with phi in X by lia. exact X.
Qed.

(* Addressability of a range inside one registered global (R6's r6_addr_glob). *)
Definition r10a_AGb (lo len : Z) : bool :=
  existsb (fun p => (fst p =? lo) && (snd p =? len)) AFw.frame_AG.

Lemma r10a_AGb_in : forall lo len a, r10a_AGb lo len = true -> lo <= a < lo + len -> in_globals AFw.frame_AG a.
Proof.
  intros lo len a H Ha. unfold r10a_AGb in H. apply existsb_exists in H. destruct H as ([x y] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_true_iff in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  subst x y. exists lo, len. split; [exact Hin | exact Ha].
Qed.

Lemma r10a_addr_glob : forall (m : word -> option byte) (lo len a n : Z),
  (forall x, in_globals AFw.frame_AG x -> addressable m x 1) ->
  r10a_AGb lo len = true -> lo <= a -> a + n <= lo + len -> 0 <= n -> 0 <= a -> a + n <= APPMEM_END ->
  addressable m a n.
Proof.
  intros m lo len a n HAG Hb H1 H2 Hn Ha Hae.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (HAG (a + i) (r10a_AGb_in lo len (a + i) Hb ltac:(lia))) as (_ & _ & _ & H).
  pose proof (H 0 ltac:(lia)) as Hbb. rewrite Z.add_0_r in Hbb. exact Hbb.
Qed.

Lemma r10a_dj_of : forall (W : list (Z * Z)) a n, (forall p, In p W -> a + n <= fst p) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; [exact I|].
  split; [left; exact (H (lo, hi) (or_introl eq_refl))|].
  apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

(* Every range at or above GT misses the runtime's cells (all of them lie below GT). *)
Lemma r10a_rt_dj : forall W, (forall p, In p W -> 6283264 <= fst p) -> rt_disjoint W.
Proof.
  intros W HL.
  unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
    RT_AGLOB_LEN.
  repeat (split; [solve [apply r10a_dj_of; intros p Hp; pose proof (HL p Hp); lia] |]);
  solve [apply r10a_dj_of; intros p Hp; pose proof (HL p Hp); lia].
Qed.

Lemma r10a_WC_rt : forall phi len fr spv FS G, 6283264 <= fr -> 6283264 <= FS -> 6283264 + 9072 <= spv ->
  rt_disjoint (r10a_WC phi len fr spv FS G).
Proof.
  intros phi len fr spv FS G H1 H2 H3. apply r10a_rt_dj. intros p Hp. rewrite r10a_WC_eq in Hp.
  assert (S1 : 2147450880 <= shadow_addr (FS + 1085440)) by (rewrite r10a_sh_eq; pose proof (Z.div_pos (FS + 1085440) 8); lia).
  assert (S2 : 2147450880 <= shadow_addr (spv - 9072)) by (rewrite r10a_sh_eq; pose proof (Z.div_pos (spv - 9072) 8); lia).
  destruct (reply_ok phi len (fr + 2448) (fr + 2464) (fr + 2496) G); cbn [app In] in Hp;
    repeat (destruct Hp as [<-|Hp]; [cbn [fst]; lia|]); contradiction.
Qed.

(* The frame bytes and the frame-shadow bytes are cells the stores and the callee may use. *)
Lemma r10a_ex_C1 : forall m A n, stk rsegs m A (A + Z.of_nat n) ->
  exists xs, length xs = n /\ rw_cells rsegs m A (map C1 xs).
Proof.
  intros m A n Hs. destruct (stk_bytes rsegs m A (A + Z.of_nat n) Hs ltac:(lia)) as (bs & Hl & Hb).
  exists bs. split; [lia|]. apply r10a_rw_C1; [exact Hb|].
  replace (Z.of_nat (length bs)) with (A + Z.of_nat n - A) by lia. exact (r10a_wr_stk _ _ _ Hs).
Qed.

Lemma r10a_ex_CB : forall m A n, stk rsegs m A (A + Z.of_nat n) ->
  exists xs, length xs = n /\ rw_cells rsegs m A [CB n xs].
Proof.
  intros m A n Hs. destruct (stk_bytes rsegs m A (A + Z.of_nat n) Hs ltac:(lia)) as (bs & Hl & Hb).
  exists bs. split; [lia|]. replace n with (length bs) at 1 by lia. apply r10a_rw_CB; [exact Hb|].
  replace (Z.of_nat (length bs)) with (A + Z.of_nat n - A) by lia. exact (r10a_wr_stk _ _ _ Hs).
Qed.

(* ---- the frame's shadow bytes in granule form ---- *)
Lemma r10a_sh_fr : forall fr j, fr mod 8 = 0 -> 0 <= j -> shadow_addr (fr + j) = Sfr fr + j / 8.
Proof. intros fr j H8 Hj. unfold Sfr. rewrite !r10a_sh_eq. Z.div_mod_to_equations. lia. Qed.

Lemma r10a_sh_below : forall lo x, lo mod 8 = 0 -> x < lo -> shadow_addr x < shadow_addr lo.
Proof. intros lo x H8 Hx. rewrite !r10a_sh_eq. Z.div_mod_to_equations. lia. Qed.

Lemma r10a_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACw.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* ---- the turn-b lengths (computed over the 11 catalogue rows, B3Rtm.a_rows) ---- *)
Lemma r10a_lens : forall inp (b : nat), (b <= 4)%nat ->
  Z.of_nat (length (rt_F inp (Z.of_nat b))) = rt_n inp (Z.of_nat b) /\
  length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b Hb.
  assert (E : b = 0%nat \/ b = 1%nat \/ b = 2%nat \/ b = 3%nat \/ b = 4%nat) by lia.
  destruct E as [->|[->|[->|[->| ->]]]]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; a_rows inp; a_fin.
Qed.

(* ---- the cut facts every arm carries from its entry to its exit, and their transport across a write W that
   misses the save area, the frame outside the reply cells [fr + 2448, fr + 2504), the turn's record Phi_r, the
   frame shadow outside S(fr) + 306 .. 317, the shadow of Phi_r, and (when it exists) the input block and its
   shadow. ---- *)
Definition r10a_K (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  HB m phi (rnb g b) /\ OURb g fr m /\ OUTA fr m /\
  spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
  spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
  spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
  (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
  spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
  (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
  spill regs m 152 (Sfr fr + 68) /\ addressable m (fr + 2176) 38 /\
  IDBr g fr (RID (g_in g) b) m /\ FGBr g fr (RFG (g_in g) b) m /\
  bytes_at rsegs m phi (rt_F (g_in g) (Z.of_nat b)) /\ RXS g fr regs m.

Lemma r10a_keep : forall g b phi fr regs regs' m m' W A,
  r10a_K g b phi fr regs m -> LF.munch W m m' -> LF.wmono rsegs m m' ->
  getr regs' 9 = getr regs 9 -> rg regs 9 A -> 0 <= A -> A + 416 < 2 ^ 64 ->
  (b <= 4)%nat -> 0 <= fr -> fr mod 8 = 0 ->
  (forall x, A <= x < A + 416 -> LF.outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 2448 <= x < fr + 2504) -> LF.outside W x) ->
  (forall x, phi <= x < phi + rnb g b -> LF.outside W x) ->
  (forall k, 0 <= k < FRAME_SHADOW -> ~ (306 <= k < 318) -> LF.outside W (Sfr fr + k)) ->
  (forall i, 0 <= i < ACw.a_size (rnb g b) -> LF.outside W (shadow_addr (phi + i))) ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g -> LF.outside W x) ->
  (0 < g_n g -> forall i, 0 <= i < g_n g -> LF.outside W (shadow_addr (g_p g + i))) ->
  r10a_K g b phi fr regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g b phi fr regs regs' m m' W A
    (HHB & HOUR & HOUTA & H112 & H128 & HPRO & H104 & H96 & H64 & H144 & H208 & (idb & HC2688) & (j1 & HC2768) &
     H280 & H240 & (jy & HC2960) & (j2 & HC2976) & H152 & HA2176 & HID & HFG & HPHI &
     (X48 & X56 & X88 & X80 & X72 & X16 & X8 & X192 & X216 & XA2256))
    MU WM E9 Hr9 HA0 HA1 Hb4 Hfr0 Hfr8 HoA HoF HoP HoS HoPS HoI HoIS.
  destruct (r10a_lens (g_in g) b Hb4) as (LFl & LIl & LGl).
  assert (SK : forall off v, 0 <= off <= 408 -> spill regs m off v -> spill regs' m' off v)
    by (intros off v Ho Hs; exact (r10a_spill_keep regs regs' m m' W A off v E9 Hr9 HA0 HA1 Ho MU HoA Hs)).
  assert (FB : forall a l, fr <= a -> a + Z.of_nat (length l) <= fr + FRAME_BYTES ->
                 (a + Z.of_nat (length l) <= fr + 2448 \/ fr + 2504 <= a) ->
                 bytes_at rsegs m a l -> bytes_at rsegs m' a l).
  { intros a l H1 H2 H3 Hb. eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply HoF; lia. }
  assert (RK : forall a n l, fr <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
                 (a + Z.of_nat n <= fr + 2448 \/ fr + 2504 <= a) ->
                 rw_cells rsegs m a [CB n l] -> rw_cells rsegs m' a [CB n l]).
  { intros a n l H1 H2 H3 Hc. apply (r10a_rw_keep W m m' a n l Hc MU WM). intros x Hx. apply HoF; lia. }
  assert (AK : forall k n, 0 <= k -> 0 <= n -> k + n <= FRAME_BYTES -> (k + n <= 2448 \/ 2544 <= k) ->
                 addressable m (fr + k) n -> addressable m' (fr + k) n).
  { intros k n H1 H2 H3 H4 Ha. apply (r10a_addr_keep W m m' (fr + k) n Ha MU). intros i Hi.
    replace (fr + k + i) with (fr + (k + i)) by lia. rewrite (r10a_sh_fr fr (k + i) Hfr8 ltac:(lia)).
    apply HoS.
    - clear - HFRAMEb HFRAMEs H1 H2 H3 Hi. Z.div_mod_to_equations. lia.
    - clear - HFRAMEb HFRAMEs H1 H2 H3 H4 Hi. Z.div_mod_to_equations. lia. }
  split.
  { destruct HHB as (Hnz & Had). split; [exact Hnz|]. exact (r10a_addr_keep W m m' phi _ Had MU HoPS). }
  split; [unfold OURb in *; apply (FB (fr + 2624) (OUR (g_in g))); [lia | rewrite OUR_length; cbn; lia | right; lia | exact HOUR]|].
  split; [unfold OUTA in *; apply (AK 544 1492); [lia | lia | lia | left; lia | exact HOUTA]|].
  split; [exact (SK 112 _ ltac:(lia) H112)|].
  split; [exact (SK 128 _ ltac:(lia) H128)|].
  split.
  { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P200 & P248 & PA2624 & PIN & PBLK &
      P184 & P256 & P264 & P272 & P32).
    split; [exact (SK 40 _ ltac:(lia) P40)|].
    split; [exact (SK 120 _ ltac:(lia) P120)|].
    split; [exact (SK 136 _ ltac:(lia) P136)|].
    split; [exact (SK 160 _ ltac:(lia) P160)|].
    split; [exact (SK 168 _ ltac:(lia) P168)|].
    split; [exact (SK 176 _ ltac:(lia) P176)|].
    split; [exact (SK 208 _ ltac:(lia) P200)|].
    split; [exact (SK 248 _ ltac:(lia) P248)|].
    split; [apply (AK 2624 6); [lia | lia | lia | right; lia | exact PA2624]|].
    split; [eapply fl_bytes; [exact PIN | exact MU |]; intros x Hx; rewrite <- g_n_len in Hx;
            destruct (Z_lt_le_dec 0 (g_n g)) as [Hn|Hn]; [exact (HoI Hn x Hx) | lia]|].
    split.
    - intros Hn. destruct (PBLK Hn) as (HH & Had). split; [exact HH|].
      exact (r10a_addr_keep W m m' (g_p g) (g_n g) Had MU (HoIS Hn)).
    - split; [exact (SK 184 _ ltac:(lia) P184)|].
      split; [exact (SK 256 _ ltac:(lia) P256)|].
      split; [exact (SK 264 _ ltac:(lia) P264)|].
      split; [exact (SK 272 _ ltac:(lia) P272) | exact (SK 32 _ ltac:(lia) P32)]. }
  split; [exact (SK 104 _ ltac:(lia) H104)|].
  split; [exact (SK 96 _ ltac:(lia) H96)|].
  split; [exact (SK 64 _ ltac:(lia) H64)|].
  split; [exact (SK 144 _ ltac:(lia) H144)|].
  split; [exact (SK 192 _ ltac:(lia) H208)|].
  split; [exists idb; apply (RK (fr + 2688) 38%nat idb); [lia | cbn; lia | right; lia | exact HC2688]|].
  split; [exists j1; apply (RK (fr + 2768) 72%nat j1); [lia | cbn; lia | right; lia | exact HC2768]|].
  split; [exact (SK 280 _ ltac:(lia) H280)|].
  split; [exact (SK 240 _ ltac:(lia) H240)|].
  split; [exists jy; apply (RK (fr + 3040) 1%nat jy); [lia | cbn; lia | right; lia | exact HC2960]|].
  split; [exists j2; apply (RK (fr + 3056) 32%nat j2); [lia | cbn; lia | right; lia | exact HC2976]|].
  split; [exact (SK 152 _ ltac:(lia) H152)|].
  split; [apply (AK 2176 38); [lia | lia | lia | left; lia | exact HA2176]|].
  split; [unfold IDBr in *; apply (FB (fr + 2176) _); [lia | rewrite LIl; cbn; lia | left; rewrite LIl; cbn; lia | exact HID]|].
  split; [unfold FGBr in *; apply (FB (fr + 2256) _); [lia | rewrite LGl; cbn; lia | left; rewrite LGl; cbn; lia | exact HFG]|].
  split.
  { eapply fl_bytes; [exact HPHI | exact MU |]. rewrite LFl. intros x Hx. apply HoP. unfold rnb. lia. }
  split; [exact (SK 48 _ ltac:(lia) X48)|].
  split; [exact (SK 56 _ ltac:(lia) X56)|].
  split; [exact (SK 88 _ ltac:(lia) X88)|].
  split; [exact (SK 80 _ ltac:(lia) X80)|].
  split; [exact (SK 72 _ ltac:(lia) X72)|].
  split; [exact (SK 8 _ ltac:(lia) X16)|].
  split; [exact (SK 0 _ ltac:(lia) X8)|].
  split; [exact (SK 200 _ ltac:(lia) X192)|].
  split; [exact (SK 216 _ ltac:(lia) X216)|].
  apply (AK 2256 72); [lia | lia | lia | left; lia | exact XA2256].
Qed.

Lemma r10a_hb_in : forall phi n (H : list (Z * Z)), In (phi, n) (hb1 phi n ++ H).
Proof. intros phi n H. cbn [hb1 app In]. left. reflexivity. Qed.

(* A fact kept out of lia's sight (disjunctions and implications in a large context make every lia call split
   cases); unfolded only where it is used. *)
Definition r10a_hide (P : Prop) : Prop := P.
Lemma r10a_hide_intro : forall P : Prop, P -> r10a_hide P.
Proof. intros P H. exact H. Qed.

(* ---- arm b = 3, 4, call: 0x816ac mv a0,s8; mv a1,s2; ld a2,88(s1); ld a3,80(s1); ld a4,72(s1);
   0x816c0 jal reac_ctrl_identity_reply, on its contract, back at 0x816c4 (a Theorem Labs lane's r10_evt_R34 tail, not in this delivery). The premises
   are the contract's, at the argument values. ---- *)
Lemma r10a_call34 : reac_ctrl_identity_reply_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi nb pa pp pn A spv FS : Z) (g ja jp jn : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 nb -> s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv ->
    0 <= A -> A + 96 <= 2 ^ 64 ->
    q64 m (A + 88) pa -> q64 m (A + 80) pp -> q64 m (A + 72) pn ->
    0 <= phi < 2 ^ 64 -> 0 <= nb < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= spv -> stk rsegs m (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    mem_inv rsegs m ->
    length g = 50%nat ->
    (reply_args phi pa pp pn = true -> 50 <= nb ->
       phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi g /\
       (phi + 50 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= phi)) ->
    (reply_args phi pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= phi \/ phi + 50 <= pa) /\ (pp + 8 <= phi \/ phi + 50 <= pp) /\
       (pn + 8 <= phi \/ phi + 50 <= pn) /\
       (pa + 2 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pa) /\
       (pp + 8 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pp) /\
       (pn + 8 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pn)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - REAC_CTRL_IDENTITY_REPLY_K -> spv <= APPMEM_END ->
    addressable m (spv - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    (reply_args phi pa pp pn = true -> 50 <= nb -> addressable m phi 50) ->
    (reply_args phi pa pp pn = true ->
       addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv
      (reac_ctrl_identity_reply_W phi pa pp pn spv) (reac_ctrl_identity_reply_D phi nb pa pp pn) ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816c4) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 (reply_ret phi nb pa pp pn g) /\
         munch (reac_ctrl_identity_reply_fp phi nb pa pp pn spv g ++ fp_w [1%nat] FS ++
                [(shadow_addr (spv - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr spv)]) m m' /\
         wmono rsegs m m' /\ stk rsegs m' (spv - REAC_CTRL_IDENTITY_REPLY_K) spv /\
         (reply_ok phi nb pa pp pn g = true ->
            rw_cells rsegs m' pa [CB 2 (reply_addr g)] /\
            rw_cells rsegs m' pp [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
            rw_cells rsegs m' pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]) /\
         shadow_rw m' /\
         addressable m' (spv - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv
           (reac_ctrl_identity_reply_W phi pa pp pn spv) (reac_ctrl_identity_reply_D phi nb pa pp pn))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x816ac) fc None m (seg_rom rsegs)).
Proof.
  intros REPLY0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi nb pa pp pn A spv FS g ja jp jn -> -> -> -> HA0 HAE Qa Qp Qn
    Hphi Hnb Hpa Hpp Hpn Hsp Hsp16 HK ST HMI Hg50 Hgb Hcells HAC HSW HHM HAPP Awin Hga Haddr Abc BCM MCM GCF
    CF254 CF255 HFP HTLS.
  pose proof (r10a_q64_ro m (A + 88) pa Qa) as Rpa.
  pose proof (r10a_q64_ro m (A + 80) pp Qp) as Rpp.
  pose proof (r10a_q64_ro m (A + 72) pn Qn) as Rpn.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply (REPLY0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              phi nb pa pp pn spv FS g ja jp jn).
    all: first [ reflexivity | assumption ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & ST2 & RWo & AC2 & SW2 & Awin2 & FP2 & TLS2).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x816c4)) with (Z_to_bv 64 0x816c4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 15 (split; [reflexivity|]).
  split; [exact MU2|]. split; [exact WM2|]. split; [exact ST2|]. split; [exact RWo|].
  split; [exact SW2|]. split; [exact Awin2 | exact FP2].
Qed.

(* ======================= the segment level ======================= *)
Section R10A.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis REPLY :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_reply_c.reac_ctrl_identity_reply_contract.

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame (R6's r6_fra, the push-5b FRA). *)
Lemma r10a_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, fr <= x < fr + 24 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 16 <= x < bv_unsigned (getr regs 9) + 32 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 304 <= x < bv_unsigned (getr regs 9) + 312 -> LF.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) ->
  (forall x, g_S g - AFw.SLOT_STACK <= x < g_S g -> LF.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AFw.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AFw.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' Hrec' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold ACw.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
          -- unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        * exact (Hrec' Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (r10a_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* The bytes a write of this segment may touch: the frame's 392 shadow bytes, the frame records, the callee window,
   the class-1 side-stack hint / flag bytes and frames, and the shadow of the last two. *)
Definition r10a_in (fr sp Kw FS x : Z) : Prop :=
  (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/ (fr + 2176 <= x < fr + 2624) \/ (sp - Kw <= x < sp) \/
  (FS + 8 <= x < FS + 28672) \/ (FS + 1085440 <= x < FS + 2134016) \/
  (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) \/
  (shadow_addr (sp - Kw) <= x < shadow_addr sp).

(* FRA and ENT across a write of this segment (the shadow stores, or the reply call): the heap invariant by the
   side-stack store law a_laws_fs_store (real arm: the frame, its shadow, the window and its shadow are a_store_ok;
   side arm: the frame is in the FakeStack; the class-1 bytes and their shadow are the FakeStack's), FRA by r10a_fra,
   the side-arm frame record by its three cells, ENT by ent_munch. *)
Lemma r10a_land : forall g fr hb regs regs' mem mem' md FS Kw W,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  0 <= Kw <= FN_STACK -> Kw mod 8 = 0 ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  ACw.a_fs_ok mem' FS -> rt_disjoint W ->
  (forall x, ~ LF.outside W x -> r10a_in fr (ACw.aspZ regs) Kw FS x) ->
  (forall x, ~ LF.outside W x -> exists bb, mrd rsegs mem' (wa x) = Some bb) ->
  shadow_rw mem' ->
  addressable mem' (ACw.aspZ regs - Kw) Kw ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md FS Kw W HFRA HENT Hwtp HFSr HK HK8 MU WM HRO' HFSOK' HDJ HWin Hrd
    HSW' HADw' E2 E3 E4 E8 E9 E19 E26.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ').
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & Hstkw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  destruct (ACw.a_laws_fs_place _ _ _ _ _ ALAWS (hb ++ g_H g) mem md FS HAH Hwtp HFSr)
    as (HGTFS & HFSend & HFSmod & HFSapp).
  pose proof (HfsS FS Hwtp HFSr) as HFSfr.
  pose proof (Hplace Kw HK) as Hpl.
  rewrite Haspz in Hlo, Hstkw, HWin, HADw', Hpl.
  set (stklo := ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) in *.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HGTv : ACw.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  rewrite HbvA in HfrA.
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem in *. lia. }
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem in *. lia. }
  assert (HFSlow : FS + 11571200 <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as H1. pose proof (HFSapp (FS + 11571199) ltac:(lia)) as H2.
    unfold app_mem in *. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - HFRAMEb HFRAMEs HFSmod; Z.div_mod_to_equations; lia).
  assert (Hsp8 : sp mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hspm; Z.div_mod_to_equations; lia).
  assert (HspK8 : (sp - Kw) mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hspm HK8; Z.div_mod_to_equations; lia).
  assert (HARM : (forall a, fr <= a < fr + FRAME_BYTES -> stklo <= a < APPMEM_END) \/
                 (FS <= fr /\ fr + FRAME_BYTES <= FS + 11571200)).
  { destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]]; [left; exact Hreal | right].
    destruct (Hfs fr ltac:(lia)) as (FS1 & HFS1r & Hw1 & Hl1 & Hh1).
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS2 & HFS2r & Hw2 & Hl2 & Hh2).
    assert (EF1 : FS1 = FS) by (apply (r10a_wm_uniq mem (ACw.as_tp ACw.ASYMS) FS1 FS Hw1 Hwtp); lia).
    assert (EF2 : FS2 = FS) by (apply (r10a_wm_uniq mem (ACw.as_tp ACw.ASYMS) FS2 FS Hw2 Hwtp); lia).
    subst FS1 FS2. lia. }
  (* the shadow bands, as atoms for lia *)
  destruct (r10a_Sfr_band fr ltac:(lia) ltac:(lia)) as (FA1 & FA2).
  assert (FB1 : 2147450880 + 921088 <= shadow_addr (FS + 1085440)).
  { rewrite r10a_sh_eq. pose proof (Z.div_le_mono (6283264 + 1085440) (FS + 1085440) 8 ltac:(lia) ltac:(lia)) as D.
    change ((6283264 + 1085440) / 8) with 921088 in D. lia. }
  assert (FB2 : shadow_addr (FS + 2134016) <= 17594333495296)
    by (apply (proj2 (proj2 (r10a_sh_band (FS + 2134016) ltac:(lia) ltac:(lia))))).
  assert (FB3 : shadow_addr (FS + 1085440) <= shadow_addr (FS + 2134016)) by (apply r10a_sh_mono; lia).
  assert (FC : 17594333495296 <= sp - Kw) by lia.
  assert (FD1 : 2147450880 + 2199291686912 <= shadow_addr (sp - Kw)).
  { rewrite r10a_sh_eq. pose proof (Z.div_le_mono 17594333495296 (sp - Kw) 8 ltac:(lia) FC) as D.
    change (17594333495296 / 8) with 2199291686912 in D. lia. }
  assert (FD2 : shadow_addr sp <= 17594333495296)
    by (apply (proj2 (proj2 (r10a_sh_band sp ltac:(lia) ltac:(lia))))).
  assert (Hout : forall x, ~ r10a_in fr sp Kw FS x -> LF.outside W x).
  { intros x Hx. destruct (r10a_out_dec W x) as [Ho|Hno]; [exact Ho | exfalso; exact (Hx (HWin x Hno))]. }
  (* the heap invariant across the write *)
  assert (Hwrit : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)).
  assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
            ~ ACw.a_store_ok (hb ++ g_H g) stklo q ->
            ~ (FS <= q < FS + ACw.FS_SIZE) ->
            ~ (exists bb, FS <= bb < FS + ACw.FS_SIZE /\ q = shadow_addr bb) ->
            mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
  { intros q Hq Hns Hnfs Hnsh. rewrite HFSsz in Hnfs, Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
    apply Hout. unfold r10a_in. intros [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]].
    - destruct HARM as [Hreal|Hside].
      + apply Hns. right; right; right. exists (fr + 8 * (q - Sfr fr)). split; [rewrite r10a_sh8; lia|].
        right; left. apply Hreal. lia.
      + apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia | rewrite r10a_sh8; lia].
    - destruct HARM as [Hreal|Hside]; [apply Hns; right; left; apply Hreal; lia | apply Hnfs; lia].
    - apply Hns. right; left. lia.
    - apply Hnfs. lia.
    - apply Hnfs. lia.
    - destruct (r10a_sh_inv (FS + 1085440) (FS + 2134016) q Hx) as (Hb & Eb).
      apply Hnsh. exists (8 * (q - 2147450880)). split; [lia | symmetry; exact Eb].
    - destruct (r10a_sh_inv (sp - Kw) sp q Hx) as (Hb & Eb).
      assert (Hb' : sp - Kw <= 8 * (q - 2147450880)) by (clear - HFRAMEb HFRAMEs Hb HspK8; Z.div_mod_to_equations; lia).
      apply Hns. right; right; right. exists (8 * (q - 2147450880)). split; [symmetry; exact Eb|].
      right; left. lia. }
  destruct (ACw.a_laws_fs_store _ _ _ _ _ ALAWS (hb ++ g_H g) mem mem' md FS HAH Hwtp HFSr Hagree Hwrit HFSOK')
    as (HAH' & HOWN' & HSTK' & HHI').
  (* the new 392 frame-shadow bytes *)
  assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
  { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
    { split; [lia|]. split; [lia|]. intros a Ha. apply HSW'.
      replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10a_fsh; [exact Happ' | lia]. }
    destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
    exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
  split.
  { apply (r10a_fra g fr hb regs regs' mem mem' md W HFRA MU WM HRO' HDJ HAH' HSTK'
             (fun a Ha => proj2 (HSW' a Ha)) Hshnew).
    - intros x Hx. apply Hout. unfold r10a_in. lia.
    - intros x Hx. apply Hout. unfold r10a_in. lia.
    - intros x Hx. rewrite HbvA in Hx. apply Hout. unfold r10a_in. lia.
    - intros x Hx. rewrite HbvA in Hx. apply Hout. unfold r10a_in. lia.
    - intros x Hx. apply Hout. unfold r10a_in. lia.
    - intros x Hx. destruct (r10a_out_dec W x) as [Ho|Hno]; [left; exact Ho | right; exact (Hrd x Hno)].
    - intros a Ha. pose proof (r10a_glob_sh a (r10a_ag_range a Ha)) as Hsa.
      apply (r10a_addr_keep W mem mem' a 1 (HAG a Ha) MU). intros i Hi. replace (a + i) with a by lia.
      apply Hout. unfold r10a_in. lia.
    - intros a H1 H2.
      destruct (Z_le_gt_dec (sp - Kw) a) as [L1|L1]; [destruct (Z_lt_ge_dec a sp) as [L2|L2]|].
      + exact (r10a_addr_byte mem' (sp - Kw) Kw a HADw' ltac:(lia)).
      + apply (r10a_addr_keep W mem mem' a 1 (HWA a H1 H2) MU). intros i Hi. replace (a + i) with a by lia.
        assert (Happa : app_mem a) by (unfold app_mem; right; lia).
        pose proof (shadow_of_app a Happa) as Hsa.
        pose proof (r10a_sh_out fr (fr + FRAME_BYTES) a Hfr8 ltac:(clear - HFRAMEb HFRAMEs Hfr8; Z.div_mod_to_equations; lia) H2) as Hf.
        replace (shadow_addr (fr + FRAME_BYTES)) with (Sfr fr + FRAME_SHADOW) in Hf by (rewrite <- r10a_sh8; f_equal; lia).
        change (shadow_addr fr) with (Sfr fr) in Hf.
        pose proof (r10a_sh_mono (FS + 2134016) a ltac:(lia)) as Hm.
        apply Hout. unfold r10a_in. intros [HC|[HC|[HC|[HC|[HC|[HC|HC]]]]]].
        * lia.
        * exact (app_not_shadow (shadow_addr a) (Happ' (shadow_addr a) ltac:(lia)) Hsa).
        * exact (app_not_shadow (shadow_addr a) ltac:(unfold app_mem; right; lia) Hsa).
        * exact (app_not_shadow (shadow_addr a) (HFSapp (shadow_addr a) ltac:(lia)) Hsa).
        * exact (app_not_shadow (shadow_addr a) (HFSapp (shadow_addr a) ltac:(lia)) Hsa).
        * lia.
        * pose proof (r10a_sh_out (sp - Kw) sp a HspK8 Hsp8 ltac:(lia)). lia.
      + apply (r10a_addr_keep W mem mem' a 1 (HWA a H1 H2) MU). intros i Hi. replace (a + i) with a by lia.
        assert (Happa : app_mem a) by (unfold app_mem; right; lia).
        pose proof (shadow_of_app a Happa) as Hsa.
        pose proof (r10a_sh_out fr (fr + FRAME_BYTES) a Hfr8 ltac:(clear - HFRAMEb HFRAMEs Hfr8; Z.div_mod_to_equations; lia) H2) as Hf.
        replace (shadow_addr (fr + FRAME_BYTES)) with (Sfr fr + FRAME_SHADOW) in Hf by (rewrite <- r10a_sh8; f_equal; lia).
        change (shadow_addr fr) with (Sfr fr) in Hf.
        pose proof (r10a_sh_mono (FS + 2134016) a ltac:(lia)) as Hm.
        apply Hout. unfold r10a_in. intros [HC|[HC|[HC|[HC|[HC|[HC|HC]]]]]].
        * lia.
        * exact (app_not_shadow (shadow_addr a) (Happ' (shadow_addr a) ltac:(lia)) Hsa).
        * exact (app_not_shadow (shadow_addr a) ltac:(unfold app_mem; right; lia) Hsa).
        * exact (app_not_shadow (shadow_addr a) (HFSapp (shadow_addr a) ltac:(lia)) Hsa).
        * exact (app_not_shadow (shadow_addr a) (HFSapp (shadow_addr a) ltac:(lia)) Hsa).
        * lia.
        * pose proof (r10a_sh_out (sp - Kw) sp a HspK8 Hsp8 ltac:(lia)). lia.
    - intros Hrec0. destruct Hrec0 as (FS' & j & Htp & HFSr' & Hj & Hfrj & Hflag & Htail).
      assert (EF : FS' = FS) by (apply (r10a_wm_uniq mem (ACw.as_tp ACw.ASYMS) FS' FS Htp Hwtp); lia).
      subst FS'.
      assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
      assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
      assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfrj; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
      rewrite HM6 in Hj.
      exists FS, j.
      split.
      { intros k Hk.
        assert (Htpv : ACw.as_tp ACw.ASYMS = 0x5db810) by reflexivity.
        assert (Hx : 0 <= ACw.as_tp ACw.ASYMS + Z.of_nat k < 2 ^ 64) by lia.
        assert (Hm : mem' (Z_to_bv 64 (ACw.as_tp ACw.ASYMS + Z.of_nat k))
                     = mem (Z_to_bv 64 (ACw.as_tp ACw.ASYMS + Z.of_nat k))).
        { apply MU. rewrite MState.unsigned_lit by lia.
          apply Hout. unfold r10a_in. lia. }
        unfold mbyte. rewrite Hm. exact (Htp k Hk). }
      split; [exact HFSr|].
      split; [rewrite HM6; exact Hj|].
      split; [exact Hfrj|].
      split.
      { eapply fl_bytes; [exact Hflag | exact MU |].
        cbn [length]. intros x Hx. rewrite Hfl in Hx. apply Hout. unfold r10a_in. lia. }
      { eapply fl_bytes; [exact Htail | exact MU |].
        rewrite length_le8. intros x Hx. rewrite HB6 in Hx. apply Hout. unfold r10a_in. lia. }
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  (* ENT: no address ENT keeps is written *)
  assert (HoutENT : forall x, ent_kept g x -> LF.outside W x).
  { intros x Hk. apply Hout. destruct Hk as [Hblkk | [Hik | [Habk | [(b0 & Hor & ->) | Hblks]]]].
    - destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
      destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS (hb ++ g_H g) mem md q k HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hend & _ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      assert (HnFS : ~ (FS <= q + i < FS + 11571200)).
      { intros HF. apply Hnfs. exists FS. split; [exact HFSr | split; [exact Hwtp | rewrite HFSsz; exact HF]]. }
      assert (HnFR : ~ (fr <= q + i < fr + FRAME_BYTES)).
      { intros HF. destruct HARM as [Hreal|Hside]; [pose proof (Hreal (q + i) HF); lia | lia]. }
      unfold app_mem in Happq. unfold r10a_in. lia.
    - pose proof (img_below_GT x Hik) as Hx. unfold r10a_in. lia.
    - unfold r10a_in. lia.
    - assert (Hb0 : 0 <= b0 < 6283264 \/ g_S g <= b0 < APPMEM_END).
      { destruct Hor as [Hi|Hr]; [left; pose proof (img_below_GT b0 Hi) as X; lia | right; exact Hr]. }
      assert (Happb : app_mem b0) by (unfold app_mem; lia).
      pose proof (shadow_of_app b0 Happb) as Hsb.
      destruct (r10a_band FS (sp - Kw) sp (g_S g) b0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as (Hbd1 & Hbd2).
      assert (Hbd0 : shadow_addr b0 < Sfr fr \/ Sfr fr + FRAME_SHADOW <= shadow_addr b0).
      { destruct Hb0 as [Hb0|Hb0].
        - left. pose proof (r10a_sh_mono b0 6283263 ltac:(lia)) as M1.
          change (shadow_addr 6283263) with (2147450880 + 785407) in M1. lia.
        - right. pose proof (r10a_sh_mono (fr + FRAME_BYTES) b0 ltac:(lia)) as M1.
          replace (shadow_addr (fr + FRAME_BYTES)) with (Sfr fr + FRAME_SHADOW) in M1 by (rewrite <- r10a_sh8; f_equal; lia).
          exact M1. }
      unfold r10a_in. intros [HC|[HC|[HC|[HC|[HC|[HC|HC]]]]]].
      + lia.
      + exact (app_not_shadow (shadow_addr b0) (Happ' (shadow_addr b0) ltac:(lia)) Hsb).
      + exact (app_not_shadow (shadow_addr b0) ltac:(unfold app_mem; right; lia) Hsb).
      + exact (app_not_shadow (shadow_addr b0) (HFSapp (shadow_addr b0) ltac:(lia)) Hsb).
      + exact (app_not_shadow (shadow_addr b0) (HFSapp (shadow_addr b0) ltac:(lia)) Hsb).
      + exact (Hbd1 HC).
      + exact (Hbd2 HC).
    - (* frame batch 2 item 9: the shadow byte of an entry block byte, which is app memory below stklo, off the
         frame and off the side stack; the frame, the side-stack bands and the window are 8-aligned *)
      destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
      destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS (hb ++ g_H g) mem md q k HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hend & _ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      assert (HnFS : ~ (FS <= q + i < FS + 11571200)).
      { intros HF. apply Hnfs. exists FS. split; [exact HFSr | split; [exact Hwtp | rewrite HFSsz; exact HF]]. }
      assert (HnFR : ~ (fr <= q + i < fr + FRAME_BYTES)).
      { intros HF. destruct HARM as [Hreal|Hside]; [pose proof (Hreal (q + i) HF); lia | lia]. }
      pose proof (shadow_of_app (q + i) Happq) as Hsq.
      pose proof (r10a_sh_out fr (fr + FRAME_BYTES) (q + i) Hfr8
                    ltac:(clear - HFRAMEb HFRAMEs Hfr8; Z.div_mod_to_equations; lia) HnFR) as Hf.
      replace (shadow_addr (fr + FRAME_BYTES)) with (Sfr fr + FRAME_SHADOW) in Hf
        by (rewrite <- r10a_sh8; f_equal; lia).
      change (shadow_addr fr) with (Sfr fr) in Hf.
      pose proof (r10a_sh_out (FS + 1085440) (FS + 2134016) (q + i)
                    ltac:(clear - HFS8; Z.div_mod_to_equations; lia)
                    ltac:(clear - HFS8; Z.div_mod_to_equations; lia) ltac:(lia)) as Hc1.
      pose proof (r10a_sh_out (sp - Kw) sp (q + i) HspK8 Hsp8 ltac:(unfold app_mem in Happq; lia)) as Hw.
      unfold r10a_in. intros [HC|[HC|[HC|[HC|[HC|[HC|HC]]]]]].
      + lia.
      + exact (app_not_shadow (shadow_addr (q + i)) (Happ' (shadow_addr (q + i)) ltac:(lia)) Hsq).
      + exact (app_not_shadow (shadow_addr (q + i)) ltac:(unfold app_mem; right; lia) Hsq).
      + exact (app_not_shadow (shadow_addr (q + i)) (HFSapp (shadow_addr (q + i)) ltac:(lia)) Hsq).
      + exact (app_not_shadow (shadow_addr (q + i)) (HFSapp (shadow_addr (q + i)) ltac:(lia)) Hsq).
      + lia.
      + lia. }
  apply (ent_munch APIf g hb mem mem' md W HENT HAH MU HoutENT HSTK' HHI').
  intros a _ Hown. exact (proj2 (HOWN' a) Hown).
Qed.
(* A byte of a live block is apart from the frame, app memory below stklo, and not a side-stack byte. *)
Lemma r10a_blk : forall g fr hb regs mem md p n,
  FRA B APIf ra g fr hb regs mem md -> In (p, n) (hb ++ g_H g) ->
  forall x, p <= x < p + n -> (x < fr \/ fr + FRAME_BYTES <= x) /\ app_mem x /\
    x < ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ ACw.a_in_fs ACw.ASYMS mem x.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md p n HFRA Hin x Hx.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS (hb ++ g_H g) mem md p n HAH Hin) as (_ & _ & Hend & _ & Hall).
  destruct (Hall x Hx) as (Happ & _ & _ & _ & Hnfs).
  split; [|split; [exact Happ | split; [lia | exact Hnfs]]].
  destruct (Z_lt_le_dec x fr) as [L|L]; [left; exact L|].
  destruct (Z_lt_le_dec x (fr + FRAME_BYTES)) as [L2|L2]; [|right; exact L2].
  exfalso. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal x ltac:(lia)). lia.
  - exact (Hnfs (Hfs x ltac:(lia))).
Qed.

(* The placement numbers of a cut. *)
Lemma r10a_geo : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A, rg regs 9 A /\ 0 <= A /\ A + 416 < 2 ^ 64 /\ ACw.aspZ regs <= A /\ fr + FRAME_BYTES <= A /\
    A + 416 <= g_S g /\ g_S g < 140737488355328 /\ ACw.aspZ regs mod 16 = 0 /\
    17594333495296 + 1044480 <= ACw.aspZ regs /\
    ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md <= ACw.aspZ regs - 1044480 /\
    17594333495296 <= ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
    6283264 <= fr /\ fr + FRAME_BYTES <= 140737488355328 /\ fr mod 32 = 0 /\ fr mod 8 = 0 /\
    (fr + FRAME_BYTES <= 2147450880 \/ 17594333495296 <= fr) /\
    (fr + FRAME_BYTES <= ACw.aspZ regs - 1044480 \/ ACw.aspZ regs <= fr) /\
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
    2147450880 + 785408 <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= 17594333495296.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md HFRA.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ').
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & Hstkw).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & _).
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhigh.
  pose proof (Hplace FN_STACK ltac:(unfold FN_STACK, AFw.SLOT_STACK; lia)) as Hpl.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HGTv : ACw.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  rewrite HbvA in HfrA.
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem in *. lia. }
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem in *. lia. }
  destruct (r10a_Sfr_band fr ltac:(lia) ltac:(lia)) as (FA1 & FA2).
  exists A. rewrite Haspz in *.
  split; [exact Hr9|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact Hspm|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact Hfrm|]. split; [clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|]. split; [exact Happ'|]. split; [exact FA1 | exact FA2].
Qed.

(* FRA and ENT across frame-shadow stores [S(fr) + lo, S(fr) + hi): r10a_land with the side stack of the tp word
   (FSFREE), its state kept (no store reaches the side stack: a_fs_ok_pres) and no callee window. *)
Lemma r10a_landS : forall g fr hb regs regs' mem mem' md lo hi,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  0 <= lo -> lo <= hi -> hi <= FRAME_SHADOW ->
  LF.munch [(Sfr fr + lo, Sfr fr + hi)] mem mem' -> LF.wmono rsegs mem mem' ->
  (forall x, Sfr fr + lo <= x < Sfr fr + hi -> exists bb, mrd rsegs mem' (wa x) = Some bb) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md lo hi HFRA HENT Hlo Hlh Hhi MU WM Hrd E2 E3 E4 E8 E9 E19 E26.
  destruct (r10a_geo g fr hb regs mem md HFRA) as (A & Hr9 & HA0 & HA1 & HspA & HfrA & HAS & HSE & Hsp16 & Hsph &
    Hlo2 & Hhi2 & HGT & Hfre & Hfr32 & Hfr8 & HLH & Hpl & Happ' & FA1 & FA2).
  destruct (fra_fsfree B APIf ra g fr hb regs mem md HFRA)
    as (FS & Hwtp & HFSr & Hok & HGTFS & HAl & HFSapp & HFSend & HFSfr & _).
  pose proof HFRA as HF.
  destruct HF as (A' & sp & s5 & HRT & HAH & Hro & _).
  assert (HFSsz : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (Hin : forall x, Sfr fr + lo <= x < Sfr fr + hi -> in_shadow x).
  { intros x Hx. replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r10a_fsh; [exact Happ' | lia]. }
  assert (Hnot : forall x, ~ LF.outside [(Sfr fr + lo, Sfr fr + hi)] x -> Sfr fr + lo <= x < Sfr fr + hi).
  { intros x Hx. cbn [LF.outside] in Hx. lia. }
  assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
            exists b, mbyte rsegs mem' q = Some b).
  { intros q Hq (b0 & Hb0).
    destruct (r10a_out_dec [(Sfr fr + lo, Sfr fr + hi)] q) as [Ho|Hno].
    - exists b0. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb0|].
      rewrite MState.unsigned_lit by exact Hq. exact Ho.
    - exact (Hrd q (Hnot q Hno)). }
  assert (HSW' : shadow_rw mem').
  { intros a Ha. destruct (AsanRTInv.RT_shadow_rw _ _ _ HRT a Ha) as (Hw & b0 & Hb0).
    split; [exact (WM _ Hw)|].
    destruct (r10a_out_dec [(Sfr fr + lo, Sfr fr + hi)] a) as [Ho|Hno].
    - exists b0. unfold mrd in *. rewrite (MU (wa a)); [exact Hb0|].
      pose proof (in_shadow_range a Ha) as Hr. rewrite wa_unsigned by lia. exact Ho.
    - exact (Hrd a (Hnot a Hno)). }
  assert (HFSOK' : ACw.a_fs_ok mem' FS).
  { apply (a_fs_ok_pres [(Sfr fr + lo, Sfr fr + hi)] mem mem' FS Hok MU); [| exact Hpres | | lia | lia].
    - intros q _ Hq. exact (WM (Z_to_bv 64 q) Hq).
    - intros q Hq. pose proof (r10a_fs_meta_range FS q Hq) as Hqr.
      cbn [LF.outside]. split; [|exact I]. intros Hx.
      exact (app_not_shadow q (HFSapp q ltac:(lia)) (Hin q Hx)). }
  apply (r10a_land g fr hb regs regs' mem mem' md FS 0 [(Sfr fr + lo, Sfr fr + hi)] HFRA HENT Hwtp HFSr
           ltac:(unfold FN_STACK, AFw.SLOT_STACK; lia) ltac:(reflexivity) MU WM).
  - apply (r10a_ro_munch _ mem mem' Hro MU). intros x Hx. pose proof (Hnot x Hx). lia.
  - exact HFSOK'.
  - apply r10a_rt_dj. intros p Hp. destruct Hp as [<-|[]]. cbn [fst]. lia.
  - intros x Hx. left. pose proof (Hnot x Hx). lia.
  - intros x Hx. exact (Hrd x (Hnot x Hx)).
  - exact HSW'.
  - assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
    split; [lia|]. split; [lia|]. split; [rewrite HAPPv; lia|]. intros i Hi. lia.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

(* A live block (Phi_r, the input block) and its shadow are apart from frame-shadow stores. *)
Lemma r10a_blk_outS : forall g fr hb regs mem md p n lo hi,
  FRA B APIf ra g fr hb regs mem md -> In (p, n) (hb ++ g_H g) -> 0 <= lo -> hi <= FRAME_SHADOW ->
  (forall x, p <= x < p + n -> LF.outside [(Sfr fr + lo, Sfr fr + hi)] x) /\
  (forall i, 0 <= i < n -> LF.outside [(Sfr fr + lo, Sfr fr + hi)] (shadow_addr (p + i))).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md p n lo hi HFRA Hin Hlo Hhi.
  destruct (r10a_geo g fr hb regs mem md HFRA) as (A & Hr9 & HA0 & HA1 & HspA & HfrA & HAS & HSE & Hsp16 & Hsph &
    Hlo2 & Hhi2 & HGT & Hfre & Hfr32 & Hfr8 & HLH & Hpl & Happ' & FA1 & FA2).
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  split.
  - intros x Hx. destruct (r10a_blk g fr hb regs mem md p n HFRA Hin x Hx) as (_ & Happx & _).
    unfold app_mem in Happx. cbn [LF.outside]. split; [|exact I]. lia.
  - intros i Hi. destruct (r10a_blk g fr hb regs mem md p n HFRA Hin (p + i) ltac:(lia)) as (Hapart & _).
    cbn [LF.outside]. split; [|exact I].
    destruct Hapart as [L|L].
    + pose proof (r10a_sh_below fr (p + i) Hfr8 L) as M. change (shadow_addr fr) with (Sfr fr) in M. lia.
    + pose proof (r10a_sh_mono (fr + 8 * FRAME_SHADOW) (p + i) ltac:(lia)) as M. rewrite r10a_sh8 in M. lia.
Qed.

(* A live block and its shadow are apart from the reply call's writes. *)
Lemma r10a_blk_outC : forall g fr hb regs mem md p n FS phi len G,
  FRA B APIf ra g fr hb regs mem md -> In (p, n) (hb ++ g_H g) ->
  word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall x, p <= x < p + n -> LF.outside (r10a_WC phi len fr (ACw.aspZ regs) FS G) x) /\
  (forall i, 0 <= i < n -> LF.outside (r10a_WC phi len fr (ACw.aspZ regs) FS G) (shadow_addr (p + i))).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md p n FS phi len G HFRA Hin Hwtp HFSr.
  destruct (r10a_geo g fr hb regs mem md HFRA) as (A & Hr9 & HA0 & HA1 & HspA & HfrA & HAS & HSE & Hsp16 & Hsph &
    Hlo2 & Hhi2 & HGT & Hfre & Hfr32 & Hfr8 & HLH & Hpl & Happ' & FA1 & FA2).
  destruct (fra_fsfree B APIf ra g fr hb regs mem md HFRA)
    as (FS0 & Hwtp0 & HFSr0 & Hok0 & HGT0 & HAl0 & HFSapp0 & HFSend0 & HFSfr0 & _).
  assert (EF : FS0 = FS) by (apply (r10a_wm_uniq mem (ACw.as_tp ACw.ASYMS) FS0 FS Hwtp0 Hwtp); lia).
  subst FS0.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : ACw.GT = 6283264) by reflexivity.
  assert (HFSlow : FS + 11571200 <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp0 FS ltac:(lia)) as H1. pose proof (HFSapp0 (FS + 11571199) ltac:(lia)) as H2.
    unfold app_mem in *. lia. }
  assert (FB1 : 2147450880 + 921088 <= shadow_addr (FS + 1085440)).
  { rewrite r10a_sh_eq. pose proof (Z.div_le_mono (6283264 + 1085440) (FS + 1085440) 8 ltac:(lia) ltac:(lia)) as D.
    change ((6283264 + 1085440) / 8) with 921088 in D. lia. }
  assert (FB2 : shadow_addr (FS + 2134016) <= 17594333495296)
    by (apply (proj2 (proj2 (r10a_sh_band (FS + 2134016) ltac:(lia) ltac:(lia))))).
  assert (FD1 : 2147450880 + 2199291686912 <= shadow_addr (ACw.aspZ regs - 9072)).
  { rewrite r10a_sh_eq.
    pose proof (Z.div_le_mono 17594333495296 (ACw.aspZ regs - 9072) 8 ltac:(lia) ltac:(lia)) as D.
    change (17594333495296 / 8) with 2199291686912 in D. lia. }
  assert (FD2 : shadow_addr (ACw.aspZ regs) <= 17594333495296)
    by (apply (proj2 (proj2 (r10a_sh_band (ACw.aspZ regs) ltac:(lia) ltac:(lia))))).
  split.
  - intros x Hx.
    destruct (r10a_blk g fr hb regs mem md p n HFRA Hin x Hx) as (Hfx & Happx & Hlox & Hnfs).
    assert (HnFS : ~ (FS <= x < FS + 11571200)).
    { intros HFx. apply Hnfs. exists FS. split; [exact HFSr | split; [exact Hwtp | rewrite HFSsz; exact HFx]]. }
    unfold app_mem in Happx. apply r10a_out_WC; lia.
  - intros i Hi.
    destruct (r10a_blk g fr hb regs mem md p n HFRA Hin (p + i) ltac:(lia)) as (Hfx & Happx & Hlox & Hnfs).
    assert (HnFS : ~ (FS <= p + i < FS + 11571200)).
    { intros HFx. apply Hnfs. exists FS. split; [exact HFSr | split; [exact Hwtp | rewrite HFSsz; exact HFx]]. }
    pose proof Happx as Happx'. unfold app_mem in Happx'.
    destruct (r10a_sh_band (p + i) ltac:(lia) ltac:(lia)) as (_ & Bs).
    assert (Bs' : shadow_addr (p + i) < 17594333495296).
    { rewrite r10a_sh_eq. pose proof (Z.div_le_mono (p + i) (140737488355328 - 1) 8 ltac:(lia) ltac:(lia)) as D.
      change ((140737488355328 - 1) / 8) with 17592186044415 in D. lia. }
    pose proof (r10a_sh_below (ACw.aspZ regs - 9072) (p + i)
                  ltac:(clear - HFRAMEb HFRAMEs Hsp16; Z.div_mod_to_equations; lia) ltac:(lia)) as M3.
    destruct (Z_lt_le_dec (p + i) FS) as [L|L].
    + pose proof (r10a_sh_below (FS + 1085440) (p + i)
                    ltac:(clear - HFRAMEb HFRAMEs HAl0; Z.div_mod_to_equations; lia) ltac:(lia)) as M4.
      apply r10a_out_WC; lia.
    + pose proof (r10a_sh_mono (FS + 2134016) (p + i) ltac:(lia)) as M4.
      apply r10a_out_WC; lia.
Qed.

(* ---- arm b = 1, 2 ---- *)
Lemma r10a_b12 : forall b : nat, (b = 1 \/ b = 2)%nat ->
  Hat B APIf ra (Inv_A817ec_at (fx := fx) B APIf ra) b -> Hat B APIf ra (Inv_A81680_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b Hb Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & HBODY & HX).
  subst c.
  destruct HBODY as (Hgn & Hb6 & HHB & Hr23 & HOUR & HOUTA & HCUR & H112 & H128 & HPRO & H104 & H96 & H64 &
    H144 & H208 & HC2688 & HC2768 & H280 & H240 & HC2960 & HC2976 & H152 & Hr21 & HA2176).
  pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPBLK & _).
  destruct HX as (HRF & HRXS & Ha0 & Hr27).
  destruct HRF as (((_ & _ & _ & _ & HID & HFG) & Hnz & Hr24 & HPHI) & Hr18).
  assert (Hb4 : (b <= 4)%nat) by lia.
  assert (Hk5 : rt_k (g_in g) (Z.of_nat b) = 5) by (apply a_rtm_k5; lia).
  rewrite Hk5 in Ha0.
  assert (HK0 : r10a_K g b phi fr regs mem) by (unfold r10a_K; tauto).
  destruct (r10a_geo g fr _ regs mem md HFRA) as (A & Hr9 & HA0 & HA1 & HspA & HfrA & HAS & HSE & Hsp16 & Hsph &
    Hlo2 & Hhi2 & HGT & Hfre & Hfr32 & Hfr8 & HLH & Hpl & Happ' & FA1 & FA2).
  pose proof HFRA as HF.
  destruct HF as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 &
    Hr9' & Hr3 & Hr19 & _).
  destruct (a_rtn_u (g_in g) (Z.of_nat b) Hnz) as (u & Hu & Hur).
  assert (Hrnb : 124 <= rnb g b <= 1492) by (unfold rnb; lia).
  destruct HHB as (Hphinz & HphiA).
  pose proof HphiA as (Hphi0 & _ & HphiE & _).
  assert (Hasz : ACw.a_size (rnb g b) = rnb g b) by (unfold ACw.a_size; lia).
  rewrite Hasz in HphiE.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (Hshstk : stk rsegs mem (Sfr fr + 306) (Sfr fr + 306 + Z.of_nat 7)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply (AsanRTInv.RT_shadow_rw _ _ _ HRT).
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10a_fsh; [exact Happ' | lia]. }
  destruct (r10a_ex_C1 mem (Sfr fr + 306) 7 Hshstk) as (xs & Hxs & CH).
  unfold rg in Hr19, Hr23, Hr27, Hr24. unfold a0v, rg in Ha0.
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81680) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x817ec /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
       getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 13 = Z_to_bv 64 32 /\
       LF.munch [(Sfr fr + 306, Sfr fr + 313)] mem mem' /\ LF.wmono rsegs mem mem' /\
       (exists l7, bytes_at rsegs mem' (Sfr fr + 306) l7 /\ length l7 = 7%nat))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + apply r10a_evt12 with (Sh := Sfr fr) (phi := phi) (bb := Z.of_nat b) (xs := xs).
      all: try assumption.
      all: try lia.
    + intros ms' (R & m' & l7 & Hms & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P21 & P22 & P23 & P24 & P25 & P26 &
                  P10 & P11 & P12 & P13 & MUq & WMq & Bq & Lq).
      exists R, (Z_to_bv 64 0x817ec), m'. split; [exact Hms|].
      split; [reflexivity|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
      split; [exact P18|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
      split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
      split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|].
      split; [exact MUq|]. split; [exact WMq|]. exists l7. split; [exact Bq | exact Lq].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K10 & K11 & K12 & K13 &
       MU & WM & (l7 & B7 & L7)) Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (Hrd : forall x, Sfr fr + 306 <= x < Sfr fr + 313 -> exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. apply (r10a_ba_rd mem' (Sfr fr + 306) l7 x B7). rewrite L7.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    destruct (r10a_landS g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md 306 313 HFRA HENT
                ltac:(lia) ltac:(lia) ltac:(lia) MU WM Hrd E2 E3 E4 E8 E9 E19 E26) as (HFRA1 & HENT1).
    pose proof (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRA1
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat) as HFRA2.
    pose proof (ent_mat APIf g (hb1 phi (rnb g b)) mem' md md' HENT1 Hmat) as HENT2.
    assert (HK1 : r10a_K g b phi fr regs'' mem').
    { apply (r10a_keep g b phi fr regs regs'' mem mem' [(Sfr fr + 306, Sfr fr + 313)] A HK0 MU WM E9 Hr9
               HA0 HA1 Hb4 ltac:(lia) Hfr8).
      - intros x Hx. cbn [LF.outside]. split; [|exact I]. lia.
      - intros x Hx _. cbn [LF.outside]. split; [|exact I]. lia.
      - exact (proj1 (r10a_blk_outS g fr _ regs mem md phi (rnb g b) 306 313 HFRA
                        (r10a_hb_in phi (rnb g b) (g_H g)) ltac:(lia) ltac:(lia))).
      - intros k Hk Hk'. cbn [LF.outside]. split; [|exact I]. lia.
      - rewrite Hasz.
        exact (proj2 (r10a_blk_outS g fr _ regs mem md phi (rnb g b) 306 313 HFRA
                        (r10a_hb_in phi (rnb g b) (g_H g)) ltac:(lia) ltac:(lia))).
      - intros Hn. exact (proj1 (r10a_blk_outS g fr _ regs mem md (g_p g) (g_n g) 306 313 HFRA
                        (in_or_app _ _ _ (or_intror (proj1 (HPBLK Hn)))) ltac:(lia) ltac:(lia))).
      - intros Hn. exact (proj2 (r10a_blk_outS g fr _ regs mem md (g_p g) (g_n g) 306 313 HFRA
                        (in_or_app _ _ _ (or_intror (proj1 (HPBLK Hn)))) ltac:(lia) ltac:(lia))). }
    destruct HK1 as (HHB1 & HOUR1 & HOUTA1 & H112' & H128' & HPRO' & H104' & H96' & H64' & H144' & H208' &
      HC2688' & HC2768' & H280' & H240' & HC2960' & HC2976' & H152' & HA2176' & HID' & HFG' &
      HPHI' & HRXS').
    rewrite <- SEGS. apply Hexit.
    exists phi, 0%nat, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA2|]. split; [exact HENT2|].
    split.
    { split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHB1|].
      split; [unfold rg; rewrite E23; exact Hr23|].
      split; [exact HOUR1|]. split; [exact HOUTA1|].
      split; [destruct HCUR as (Hc0 & Hc22 & Hc25); unfold CUR, rg in *;
              split; [exact Hc0|]; split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]|].
      split; [lia|].
      split; [unfold rg; rewrite Hreg, K10; f_equal; lia|].
      split; [unfold rg; rewrite Hreg, K12; f_equal; lia|].
      unfold rg; rewrite Hreg, K13; f_equal; lia. }
    split; [exact Hb|].
    split; [lia|].
    split; [unfold rg; rewrite Hreg, K11; reflexivity|].
    split.
    { split.
      - split; [exact Hb6|].
        split; [destruct HCUR as (Hc0 & Hc22 & Hc25); unfold CUR, rg in *;
                split; [exact Hc0|]; split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]|].
        split; [exact HOUR1|]. split; [unfold rg; rewrite E23; exact Hr23|].
        split; [exact HID' | exact HFG'].
      - split; [exact Hnz|]. split; [unfold rg; rewrite E24; exact Hr24 | exact HPHI']. }
    split; [exact H128'|]. split; [exact HPRO'|]. split; [exact H104'|]. split; [exact H96'|].
    split; [exact H64'|].
    split; [unfold rg in *; rewrite E21; exact Hr21|].
    split; [exact H112'|]. split; [exact H144'|]. split; [exact H208'|].
    split; [exact HC2688'|]. split; [exact HC2768'|].
    split; [exact H280'|]. split; [exact H240'|].
    split; [exact HC2960'|]. split; [exact HC2976'|].
    split; [exact H152'|]. split; [exact HA2176' | exact HRXS'].
Qed.

(* ---- arm b = 3, 4: the frame-shadow stores to 0x816ac (phase 1), then the reply call to 0x816c4 (phase 2) ---- *)
Lemma r10a_b34 : forall b : nat, (b = 3 \/ b = 4)%nat ->
  Hat B APIf ra (Inv_A816c4_at (fx := fx) B APIf ra) b -> Hat B APIf ra (Inv_A81680_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b Hb Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & HBODY & HX).
  subst c.
  destruct HBODY as (Hgn & Hb6 & HHB & Hr23 & HOUR & HOUTA & HCUR & H112 & H128 & HPRO & H104 & H96 & H64 &
    H144 & H208 & HC2688 & HC2768 & H280 & H240 & HC2960 & HC2976 & H152 & Hr21 & HA2176).
  pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPBLK & _).
  apply r10a_hide_intro in HPBLK.
  destruct HX as (HRF & HRXS & Ha0 & Hr27).
  destruct HRF as (((_ & _ & _ & _ & HID & HFG) & Hnz & Hr24 & HPHI) & Hr18).
  assert (Hb4 : (b <= 4)%nat) by lia.
  assert (Hb34 : (3 <= b <= 4)%nat) by lia.
  clear Hb.
  assert (Hk5 : rt_k (g_in g) (Z.of_nat b) = 5) by (apply a_rtm_k5; lia).
  rewrite Hk5 in Ha0.
  assert (HK0 : r10a_K g b phi fr regs mem) by (unfold r10a_K; tauto).
  destruct (r10a_geo g fr _ regs mem md HFRA) as (A & Hr9 & HA0 & HA1 & HspA & HfrA & HAS & HSE & Hsp16 & Hsph &
    Hlo2 & Hhi2 & HGT & Hfre & Hfr32 & Hfr8 & HLH & Hpl & Happ' & FA1 & FA2).
  apply r10a_hide_intro in HLH. apply r10a_hide_intro in Hpl.
  pose proof HFRA as HF.
  destruct HF as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 &
    Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & _ & HAm & HAS' & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  destruct (a_rtn_u (g_in g) (Z.of_nat b) Hnz) as (u & Hu & Hur).
  assert (Hrnb : 124 <= rnb g b <= 1492) by (unfold rnb; lia).
  destruct HHB as (Hphinz & HphiA).
  pose proof HphiA as (Hphi0 & _ & HphiE & _).
  assert (Hasz : ACw.a_size (rnb g b) = rnb g b) by (unfold ACw.a_size; lia).
  rewrite Hasz in HphiE.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HKv : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (HFSsz' : FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : ACw.GT = 6283264) by reflexivity.
  assert (Hshstk : stk rsegs mem (Sfr fr + 306) (Sfr fr + 306 + Z.of_nat 7)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply (AsanRTInv.RT_shadow_rw _ _ _ HRT).
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10a_fsh; [exact Happ' | lia]. }
  destruct (r10a_ex_C1 mem (Sfr fr + 306) 7 Hshstk) as (xs & Hxs & CH).
  unfold rg in Hr19, Hr23, Hr27, Hr24. unfold a0v, rg in Ha0.
  rewrite SEGS.
  (* ---- phase 1: 0x81680 .. 0x816a8, the three frame-shadow stores ---- *)
  eapply (sl_run_lib regs (Z_to_bv 64 0x81680) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x816ac /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 27 = getr regs 27 /\
       LF.munch [(Sfr fr + 306, Sfr fr + 313)] mem mem' /\ LF.wmono rsegs mem mem' /\
       (exists l7, bytes_at rsegs mem' (Sfr fr + 306) l7 /\ length l7 = 7%nat) /\
       (exists c0 c1 c2 : byte, bytes_at rsegs mem' (Sfr fr + 306) [c0] /\ bv_signed c0 = 2 /\
          bytes_at rsegs mem' (Sfr fr + 308) [c1] /\ bv_signed c1 = 0 /\
          bytes_at rsegs mem' (Sfr fr + 312) [c2] /\ bv_signed c2 = 0))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + apply r10a_head34 with (Sh := Sfr fr) (bb := Z.of_nat b) (xs := xs).
      all: try assumption.
      all: try lia.
    + intros ms' (R & m' & l7 & c0 & c1 & c2 & Hms & HR & MUq & WMq & B0 & V0 & B1 & V1 & B2 & V2 & B7 & L7).
      exists R, (Z_to_bv 64 0x816ac), m'. split; [exact Hms|].
      split; [reflexivity|].
      rewrite HR.
      do 14 (split; [reflexivity|]).
      split; [exact MUq|]. split; [exact WMq|].
      split; [exists l7; split; [exact B7 | exact L7]|].
      exists c0, c1, c2. split; [exact B0|]. split; [exact V0|]. split; [exact B1|]. split; [exact V1|].
      split; [exact B2 | exact V2].
  - intros R pc' mem1 regs1 md1
      (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K27 &
       MU & WM & (l7 & B7 & L7) & (c0 & c1 & c2 & B0 & V0 & B1 & V1 & B2 & V2)) Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs1 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs1 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs1 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs1 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs1 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs1 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs1 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs1 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs1 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs1 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs1 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs1 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs1 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E27 : getr regs1 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (Hrd : forall x, Sfr fr + 306 <= x < Sfr fr + 313 -> exists bb, mrd rsegs mem1 (wa x) = Some bb).
    { intros x Hx. apply (r10a_ba_rd mem1 (Sfr fr + 306) l7 x B7). rewrite L7.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    destruct (r10a_landS g fr (hb1 phi (rnb g b)) regs regs1 mem mem1 md 306 313 HFRA HENT
                ltac:(lia) ltac:(lia) ltac:(lia) MU WM Hrd E2 E3 E4 E8 E9 E19 E26) as (HFRA1 & HENT1).
    pose proof (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs1 regs1 mem1 md md1 HFRA1
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat) as HFRA2.
    pose proof (ent_mat APIf g (hb1 phi (rnb g b)) mem1 md md1 HENT1 Hmat) as HENT2.
    assert (HK1 : r10a_K g b phi fr regs1 mem1).
    { apply (r10a_keep g b phi fr regs regs1 mem mem1 [(Sfr fr + 306, Sfr fr + 313)] A HK0 MU WM E9 Hr9
               HA0 HA1 Hb4 ltac:(lia) Hfr8).
      - intros x Hx. cbn [LF.outside]. split; [|exact I]. lia.
      - intros x Hx _. unfold r10a_hide in HLH. cbn [LF.outside]. split; [|exact I]. lia.
      - exact (proj1 (r10a_blk_outS g fr _ regs mem md phi (rnb g b) 306 313 HFRA
                        (r10a_hb_in phi (rnb g b) (g_H g)) ltac:(lia) ltac:(lia))).
      - intros k Hk Hk'. cbn [LF.outside]. split; [|exact I]. lia.
      - rewrite Hasz.
        exact (proj2 (r10a_blk_outS g fr _ regs mem md phi (rnb g b) 306 313 HFRA
                        (r10a_hb_in phi (rnb g b) (g_H g)) ltac:(lia) ltac:(lia))).
      - intros Hn. exact (proj1 (r10a_blk_outS g fr _ regs mem md (g_p g) (g_n g) 306 313 HFRA
                        (in_or_app _ _ _ (or_intror (proj1 (HPBLK Hn)))) ltac:(lia) ltac:(lia))).
      - intros Hn. exact (proj2 (r10a_blk_outS g fr _ regs mem md (g_p g) (g_n g) 306 313 HFRA
                        (in_or_app _ _ _ (or_intror (proj1 (HPBLK Hn)))) ltac:(lia) ltac:(lia))). }
    pose proof HK1 as (HHB1 & HOUR1 & HOUTA1 & H112' & H128' & HPRO' & H104' & H96' & H64' & H144' & H208' &
      HC2688' & HC2768' & H280' & H240' & HC2960' & HC2976' & H152' & HA2176' & HID' & HFG' &
      HPHI' & HRXS').
    pose proof HRXS' as (X48 & X56 & X88 & X80 & X72 & X16 & X8 & X192 & X216 & XA2256).
    (* the reply cells made addressable by the stores: S(fr) + 306 = 2, 308 = 0, 312 = 0 *)
    assert (Apa : addressable mem1 (fr + 2448) 2).
    { apply (r10a_addr_cell mem1 fr 2448 2 c0); try lia.
      - intros a Ha. apply Happ'. lia.
      - change (2448 / 8) with 306. exact B0. }
    assert (App : addressable mem1 (fr + 2464) 8).
    { apply (r10a_addr_cell mem1 fr 2464 8 c1); try lia.
      - intros a Ha. apply Happ'. lia.
      - change (2464 / 8) with 308. exact B1. }
    assert (Apn : addressable mem1 (fr + 2496) 8).
    { apply (r10a_addr_cell mem1 fr 2496 8 c2); try lia.
      - intros a Ha. apply Happ'. lia.
      - change (2496 / 8) with 312. exact B2. }
    (* ---- the facts of the state at 0x816ac ---- *)
    pose proof HFRA2 as HF2.
    destruct HF2 as (A2 & sp2 & s52 & HRT2 & HAH2 & Hro1 & Hsn2 & Hhalt1 & Hgimg2 & Hr2b & Hspm2 & Haspz2 &
      Hstklo2 & Hr4b & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      HAG2 & HWA2 & _).
    assert (Hasp1 : ACw.aspZ regs1 = sp) by (rewrite <- Haspz; unfold ACw.aspZ; rewrite E2; reflexivity).
    assert (Hargs : reply_args phi (fr + 2448) (fr + 2464) (fr + 2496) = true).
    { unfold reply_args.
      rewrite (proj2 (Z.eqb_neq phi 0) Hphinz), (proj2 (Z.eqb_neq (fr + 2448) 0) ltac:(lia)),
        (proj2 (Z.eqb_neq (fr + 2464) 0) ltac:(lia)), (proj2 (Z.eqb_neq (fr + 2496) 0) ltac:(lia)).
      reflexivity. }
    set (G := rt_g (g_in g) (Z.of_nat b)).
    assert (Hg50 : length G = 50%nat) by (unfold G, rt_g; apply fr50_length).
    assert (Hir : ir (rnb g b) G = true) by (unfold G, rnb; apply a_rtm_ir; lia).
    assert (Hok : reply_ok phi (rnb g b) (fr + 2448) (fr + 2464) (fr + 2496) G = true)
      by (unfold reply_ok; rewrite Hargs, Hir; reflexivity).
    assert (Hret : reply_ret phi (rnb g b) (fr + 2448) (fr + 2464) (fr + 2496) G = 1)
      by (unfold reply_ret; rewrite Hargs, Hir; reflexivity).
    assert (Hlt50 : (rnb g b <? 50) = false) by (apply Z.ltb_ge; lia).
    assert (Hcs : forall c, In c [1%nat] -> (c <= 5)%nat) by (intros c Hc; destruct Hc as [<-|[]]; lia).
    assert (HWf : forall w, In w (reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496)
                                    (ACw.aspZ regs1)) ->
       (g_S g - AFw.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
       (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)).
    { intros w Hw. unfold reac_ctrl_identity_reply_W in Hw. rewrite Hargs, Hasp1 in Hw.
      cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
      - left. lia.
      - right; left; lia.
      - right; left; lia.
      - right; left; lia. }
    assert (HDf : forall d, In d (reac_ctrl_identity_reply_D phi (rnb g b) (fr + 2448) (fr + 2464) (fr + 2496)) ->
       snd d <= ACw.GT \/ (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
       (fst d < snd d /\ exists p n, In (p, n) (hb1 phi (rnb g b) ++ g_H g) /\ p <= fst d /\ snd d <= p + n)).
    { intros d Hd. unfold reac_ctrl_identity_reply_D in Hd. rewrite Hargs, Hlt50 in Hd.
      cbn [In app] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
      - right; right. split; [lia|]. exists phi, (rnb g b).
        split; [exact (r10a_hb_in phi (rnb g b) (g_H g)) | lia].
      - right; left; lia.
      - right; left; lia.
      - right; left; lia. }
    destruct (fra_fp B APIf ra g fr (hb1 phi (rnb g b)) regs1 mem1 md1 [1%nat] REAC_CTRL_IDENTITY_REPLY_K
                (reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496) (ACw.aspZ regs1))
                (reac_ctrl_identity_reply_D phi (rnb g b) (fr + 2448) (fr + 2464) (fr + 2496))
                HFRA2 Hcs ltac:(rewrite HKv, HFN; lia) HWf HDf) as (FS & HFP & HTLS & HDJ & HFS1).
    clear Hlt50.
    rewrite Hasp1 in HFP, HTLS.
    pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & HTPw & HPL & _).
    pose proof HPL as (HFSp & HFSmod & HFSgt & HFSapp & _).
    assert (HFSr : 0 <= FS < 2 ^ 64).
    { pose proof (HFSapp FS ltac:(lia)) as H. unfold app_mem in H. lia. }
    assert (Hwtp : word_mem rsegs mem1 (ACw.as_tp ACw.ASYMS) FS).
    { pose proof (bytes_at_le8_word rsegs mem1 (ACw.as_tp ACw.ASYMS) (Z_to_bv 64 FS) HTPw) as HW.
      rewrite MState.unsigned_lit in HW by lia. exact HW. }
    destruct (fra_fsfree B APIf ra g fr _ regs1 mem1 md1 HFRA2)
      as (FS0 & Hwtp0 & HFSr0 & Hok0 & HGT0 & HAl0 & HFSapp0 & HFSend0 & HFSfr0 & _).
    assert (EF : FS0 = FS) by (apply (r10a_wm_uniq mem1 (ACw.as_tp ACw.ASYMS) FS0 FS Hwtp0 Hwtp); lia).
    subst FS0.
    assert (HFSlow : FS + 11571200 <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
    { pose proof (HFSapp0 FS ltac:(lia)) as H1. pose proof (HFSapp0 (FS + 11571199) ltac:(lia)) as H2.
      unfold app_mem in *. lia. }
    apply r10a_hide_intro in HFSlow.
    (* the shadow bands of the call's shadow writes, as atoms *)
    assert (FB1 : 2147450880 + 921088 <= shadow_addr (FS + 1085440)).
    { rewrite r10a_sh_eq. pose proof (Z.div_le_mono (6283264 + 1085440) (FS + 1085440) 8 ltac:(lia) ltac:(lia)) as D.
      change ((6283264 + 1085440) / 8) with 921088 in D. lia. }
    assert (FB2 : shadow_addr (FS + 2134016) <= 17594333495296)
      by (apply (proj2 (proj2 (r10a_sh_band (FS + 2134016) ltac:(lia) ltac:(lia))))).
    assert (FD1 : 2147450880 + 2199291686912 <= shadow_addr (sp - 9072)).
    { rewrite r10a_sh_eq. pose proof (Z.div_le_mono 17594333495296 (sp - 9072) 8 ltac:(lia) ltac:(lia)) as D.
      change (17594333495296 / 8) with 2199291686912 in D. lia. }
    assert (FD2 : shadow_addr sp <= 17594333495296)
      by (apply (proj2 (proj2 (r10a_sh_band sp ltac:(lia) ltac:(lia))))).
    assert (Htpv : ACw.as_tp ACw.ASYMS = 0x5db810) by reflexivity.
    assert (Htp : bv_unsigned (getr regs1 4) = ACw.as_tp ACw.ASYMS).
    { rewrite Hr4b. apply MState.unsigned_lit. lia. }
    destruct (fra_win B APIf ra g fr _ regs1 mem1 md1 HFRA2) as (Hlo1 & Hstkw1).
    rewrite Hasp1 in Hlo1, Hstkw1.
    destruct (r10a_geo g fr _ regs1 mem1 md1 HFRA2) as (A3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo3 & _).
    rewrite Hasp1 in Hlo3.
    (* the frame's reply cells *)
    pose proof (fra_stk B APIf ra g fr _ regs1 mem1 md1 HFRA2) as Hfrstk.
    destruct (r10a_ex_CB mem1 (fr + 2448) 2
                (r10a_stk_sub mem1 fr (fr + FRAME_BYTES) (fr + 2448) (fr + 2448 + Z.of_nat 2) Hfrstk ltac:(lia) ltac:(lia)))
      as (ja & Hja & Cja).
    destruct (r10a_ex_CB mem1 (fr + 2464) 8
                (r10a_stk_sub mem1 fr (fr + FRAME_BYTES) (fr + 2464) (fr + 2464 + Z.of_nat 8) Hfrstk ltac:(lia) ltac:(lia)))
      as (jp & Hjp & Cjp).
    destruct (r10a_ex_CB mem1 (fr + 2496) 8
                (r10a_stk_sub mem1 fr (fr + FRAME_BYTES) (fr + 2496) (fr + 2496 + Z.of_nat 8) Hfrstk ltac:(lia) ltac:(lia)))
      as (jn & Hjn & Cjn).
    (* ---- the reply's premises at the normalized memory ---- *)
    pose proof (mem_rel_normalize rsegs mem1 Hro1) as REL.
    assert (NMI : mem_inv rsegs (normalize rsegs mem1)) by apply mem_inv_normalize.
    destruct (stk_split rsegs mem1 (sp - FN_STACK) (sp - 9072) sp Hstkw1 ltac:(lia)) as (_ & STc).
    assert (NST : stk rsegs (normalize rsegs mem1) (sp - REAC_CTRL_IDENTITY_REPLY_K) sp).
    { rewrite HKv. apply (proj1 (r10a_stk_iff mem1 _ (sp - 9072) sp REL ltac:(lia) ltac:(lia))). exact STc. }
    destruct (r10a_lens (g_in g) b Hb4) as (LFl & _ & _).
    assert (LFl' : Z.of_nat (length (rt_F (g_in g) (Z.of_nat b))) = rnb g b) by exact LFl.
    destruct (r10a_blk g fr _ regs1 mem1 md1 phi (rnb g b) HFRA2 (r10a_hb_in phi (rnb g b) (g_H g))
                (phi + rnb g b - 1) ltac:(lia)) as (_ & _ & Hxlo & _).
    assert (NG : reply_args phi (fr + 2448) (fr + 2464) (fr + 2496) = true -> 50 <= rnb g b ->
              phi + 50 <= 2 ^ 64 /\ bytes_at rsegs (normalize rsegs mem1) phi G /\
              (phi + 50 <= sp - REAC_CTRL_IDENTITY_REPLY_K \/ sp <= phi)).
    { intros _ _. split; [lia|]. split.
      - apply (proj1 (bytes_at_rel rsegs mem1 _ phi G REL)). unfold G, rt_g.
        apply r10a_g50; [lia | exact HPHI'].
      - left. lia. }
    assert (NC : reply_args phi (fr + 2448) (fr + 2464) (fr + 2496) = true ->
       (fr + 2448) mod 2 = 0 /\ (fr + 2464) mod 8 = 0 /\ (fr + 2496) mod 8 = 0 /\
       rw_cells rsegs (normalize rsegs mem1) (fr + 2448) [CB 2 ja] /\
       rw_cells rsegs (normalize rsegs mem1) (fr + 2464) [CB 8 jp] /\
       rw_cells rsegs (normalize rsegs mem1) (fr + 2496) [CB 8 jn] /\
       (fr + 2448 + 2 <= fr + 2464 \/ fr + 2464 + 8 <= fr + 2448) /\
       (fr + 2448 + 2 <= fr + 2496 \/ fr + 2496 + 8 <= fr + 2448) /\
       (fr + 2464 + 8 <= fr + 2496 \/ fr + 2496 + 8 <= fr + 2464) /\
       (fr + 2448 + 2 <= phi \/ phi + 50 <= fr + 2448) /\ (fr + 2464 + 8 <= phi \/ phi + 50 <= fr + 2464) /\
       (fr + 2496 + 8 <= phi \/ phi + 50 <= fr + 2496) /\
       (fr + 2448 + 2 <= sp - REAC_CTRL_IDENTITY_REPLY_K \/ sp <= fr + 2448) /\
       (fr + 2464 + 8 <= sp - REAC_CTRL_IDENTITY_REPLY_K \/ sp <= fr + 2464) /\
       (fr + 2496 + 8 <= sp - REAC_CTRL_IDENTITY_REPLY_K \/ sp <= fr + 2496)).
    { intros _.
      destruct (r10a_blk g fr _ regs1 mem1 md1 phi (rnb g b) HFRA2 (r10a_hb_in phi (rnb g b) (g_H g))
                  phi ltac:(lia)) as (Hp0 & _).
      destruct (r10a_blk g fr _ regs1 mem1 md1 phi (rnb g b) HFRA2 (r10a_hb_in phi (rnb g b) (g_H g))
                  (phi + 49) ltac:(lia)) as (Hp49 & _).
      split; [clear - HFRAMEb HFRAMEs Hfr32; Z.div_mod_to_equations; lia|].
      split; [clear - HFRAMEb HFRAMEs Hfr32; Z.div_mod_to_equations; lia|].
      split; [clear - HFRAMEb HFRAMEs Hfr32; Z.div_mod_to_equations; lia|].
      split; [apply (r10a_rw_norm mem1 _ _ _ REL); [intros i Hi; apply r10a_ro_hi; cbn in Hi; lia | exact Cja]|].
      split; [apply (r10a_rw_norm mem1 _ _ _ REL); [intros i Hi; apply r10a_ro_hi; cbn in Hi; lia | exact Cjp]|].
      split; [apply (r10a_rw_norm mem1 _ _ _ REL); [intros i Hi; apply r10a_ro_hi; cbn in Hi; lia | exact Cjn]|].
      rewrite HKv. unfold r10a_hide in Hpl. repeat split; lia. }
    assert (NAC : asan_cells (normalize rsegs mem1))
      by (apply (proj1 (r10a_ac_iff mem1 _ REL)); exact (AsanRTInv.RT_cells _ _ _ HRT2)).
    assert (NSW : shadow_rw (normalize rsegs mem1))
      by (apply (proj1 (r10a_shadow_iff mem1 _ REL)); exact (AsanRTInv.RT_shadow_rw _ _ _ HRT2)).
    assert (Awin1 : addressable mem1 (sp - 9072) 9072).
    { apply r10a_addr_bytes1; [| lia | lia | lia]. intros a Ha. unfold r10a_hide in Hpl. apply HWA2; lia. }
    assert (NAwin : addressable (normalize rsegs mem1) (sp - REAC_CTRL_IDENTITY_REPLY_K)
                      REAC_CTRL_IDENTITY_REPLY_K)
      by (rewrite HKv; apply (proj1 (r10a_addr_iff mem1 _ _ _ REL)); exact Awin1).
    assert (NGa : reply_args phi (fr + 2448) (fr + 2464) (fr + 2496) = true -> 50 <= rnb g b ->
              addressable (normalize rsegs mem1) phi 50).
    { intros _ _. apply (proj1 (r10a_addr_iff mem1 _ _ _ REL)).
      destruct HHB1 as (_ & HA1'). rewrite Hasz in HA1'. exact (r10a_addr_sub mem1 phi (rnb g b) 50 HA1' ltac:(lia)). }
    assert (NAD : reply_args phi (fr + 2448) (fr + 2464) (fr + 2496) = true ->
       addressable (normalize rsegs mem1) (fr + 2448) 2 /\ addressable (normalize rsegs mem1) (fr + 2464) 8 /\
       addressable (normalize rsegs mem1) (fr + 2496) 8 /\
       (fr + 2448 + 2 <= RT_LO \/ RT_HI <= fr + 2448) /\ (fr + 2464 + 8 <= RT_LO \/ RT_HI <= fr + 2464) /\
       (fr + 2496 + 8 <= RT_LO \/ RT_HI <= fr + 2496)).
    { intros _. split; [apply (proj1 (r10a_addr_iff mem1 _ _ _ REL)); exact Apa|].
      split; [apply (proj1 (r10a_addr_iff mem1 _ _ _ REL)); exact App|].
      split; [apply (proj1 (r10a_addr_iff mem1 _ _ _ REL)); exact Apn|].
      unfold RT_LO, RT_HI. repeat split; lia. }
    apply r10a_hide_intro in NG. apply r10a_hide_intro in NC.
    apply r10a_hide_intro in NGa. apply r10a_hide_intro in NAD.
    assert (NBC : addressable (normalize rsegs mem1) REAC_CTRL_PARSE_BC 6).
    { apply (proj1 (r10a_addr_iff mem1 _ _ _ REL)).
      apply (r10a_addr_glob mem1 0x21200 7 REAC_CTRL_PARSE_BC 6 HAG2 ltac:(vm_compute; reflexivity));
        unfold REAC_CTRL_PARSE_BC; lia. }
    pose proof (AsanRTInv.RT_real_cells _ _ _ HRT2) as HREAL.
    pose proof (AsanRTInv.RT_cf_cells _ _ _ HRT2) as (HCF1 & _ & _ & _ & _ & _ & HCF240 & _).
    assert (NBCM : bytes_at rsegs (normalize rsegs mem1) REAL_BCMP (le8 (wa BCMP))).
    { apply (proj1 (bytes_at_rel rsegs mem1 _ _ _ REL)).
      exact (real_cell_of mem1 REAL_BCMP BCMP HREAL ltac:(vm_compute; reflexivity)). }
    assert (NMCM : bytes_at rsegs (normalize rsegs mem1) REAL_MEMCMP (le8 (wa MEMCMP))).
    { apply (proj1 (bytes_at_rel rsegs mem1 _ _ _ REL)).
      exact (real_cell_of mem1 REAL_MEMCMP MEMCMP HREAL ltac:(vm_compute; reflexivity)). }
    assert (NGCF : bytes_at rsegs (normalize rsegs mem1) GOT_CF (le8 (wa CF))).
    { apply (proj1 (bytes_at_rel rsegs mem1 _ _ _ REL)). exact HCF1. }
    assert (NCF254 : bytes_at rsegs (normalize rsegs mem1) (CF + 254) [Z_to_bv 8 1]).
    { apply (proj1 (bytes_at_rel rsegs mem1 _ _ _ REL)).
      exact (r10a_bat_idx mem1 _ _ 14%nat (Z_to_bv 8 1) (CF + 254) HCF240 eq_refl
               ltac:(unfold CF, RT_CF; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). }
    assert (NCF255 : bytes_at rsegs (normalize rsegs mem1) (CF + 255) [Z_to_bv 8 1]).
    { apply (proj1 (bytes_at_rel rsegs mem1 _ _ _ REL)).
      exact (r10a_bat_idx mem1 _ _ 15%nat (Z_to_bv 8 1) (CF + 255) HCF240 eq_refl
               ltac:(unfold CF, RT_CF; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)). }
    assert (NFP : fp [1%nat] (normalize rsegs mem1) (bv_unsigned (getr regs1 4)) FS
                    (sp - REAC_CTRL_IDENTITY_REPLY_K) sp
                    (reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496) sp)
                    (reac_ctrl_identity_reply_D phi (rnb g b) (fr + 2448) (fr + 2464) (fr + 2496))).
    { rewrite Htp. apply (proj1 (r10a_fp_iff [1%nat] mem1 _ _ FS _ _ _ _ REL ltac:(lia) ltac:(lia))).
      exact HFP. }
    assert (NTLS : reac_ctrl_identity_reply_tls (normalize rsegs mem1) (bv_unsigned (getr regs1 4)) FS
                     (sp - REAC_CTRL_IDENTITY_REPLY_K) sp).
    { rewrite Htp. apply (proj1 (r10a_rtls_iff mem1 _ _ FS _ _ REL)). exact HTLS. }
    assert (Hr9_1 : rg regs1 9 A) by (unfold rg in *; rewrite E9; exact Hr9).
    assert (NQa : q64 (normalize rsegs mem1) (A + 88) (fr + 2448)).
    { apply (proj1 (bytes_at_rel rsegs mem1 _ _ _ REL)).
      exact (r10a_spill_at regs1 mem1 A 88 _ Hr9_1 HA0 HA1 ltac:(lia) X88). }
    assert (NQp : q64 (normalize rsegs mem1) (A + 80) (fr + 2464)).
    { apply (proj1 (bytes_at_rel rsegs mem1 _ _ _ REL)).
      exact (r10a_spill_at regs1 mem1 A 80 _ Hr9_1 HA0 HA1 ltac:(lia) X80). }
    assert (NQn : q64 (normalize rsegs mem1) (A + 72) (fr + 2496)).
    { apply (proj1 (bytes_at_rel rsegs mem1 _ _ _ REL)).
      exact (r10a_spill_at regs1 mem1 A 72 _ Hr9_1 HA0 HA1 ltac:(lia) X72). }
    assert (R24' : getr regs1 24 = Z_to_bv 64 phi) by (rewrite E24; exact Hr24).
    assert (R18' : getr regs1 18 = Z_to_bv 64 (rnb g b)) by (rewrite E18; exact Hr18).
    assert (R9' : getr regs1 9 = Z_to_bv 64 A) by exact Hr9_1.
    assert (R2' : getr regs1 2 = Z_to_bv 64 sp) by (rewrite E2; exact Hr2).
    (* ---- phase 2: 0x816ac .. the reply call .. 0x816c4 ---- *)
    eapply (sl_run_lib regs1 (Z_to_bv 64 0x816ac) mem1 md1
      (fun R pc' mem2 => pc' = Z_to_bv 64 0x816c4 /\
         getr R 2 = getr regs1 2 /\ getr R 3 = getr regs1 3 /\ getr R 4 = getr regs1 4 /\
         getr R 8 = getr regs1 8 /\ getr R 9 = getr regs1 9 /\ getr R 18 = getr regs1 18 /\
         getr R 19 = getr regs1 19 /\ getr R 21 = getr regs1 21 /\ getr R 22 = getr regs1 22 /\
         getr R 23 = getr regs1 23 /\ getr R 24 = getr regs1 24 /\ getr R 25 = getr regs1 25 /\
         getr R 26 = getr regs1 26 /\ getr R 27 = getr regs1 27 /\ getr R 10 = Z_to_bv 64 1 /\
         LF.munch (r10a_WC phi (rnb g b) fr sp FS G) mem1 mem2 /\ LF.wmono rsegs mem1 mem2 /\
         ro_agree rsegs mem2 /\ stk rsegs mem2 (sp - 9072) sp /\
         rw_cells rsegs mem2 (fr + 2448) [CB 2 (reply_addr G)] /\
         rw_cells rsegs mem2 (fr + 2464) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
         rw_cells rsegs mem2 (fr + 2496) [CB 8 (le8 (Z_to_bv 64 (ir_s G - 13)))] /\
         shadow_rw mem2 /\ addressable mem2 (sp - 9072) 9072 /\
         fp [1%nat] mem2 (ACw.as_tp ACw.ASYMS) FS (sp - 9072) sp
           (reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496) sp)
           (reac_ctrl_identity_reply_D phi (rnb g b) (fr + 2448) (fr + 2464) (fr + 2496)))
      (Post B APIf ra g)).
    + exact Hhalt1.
    + unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
      eapply evt_mono.
      * eapply (evt_normalize rsegs _ _ fp_regs _ fp_csr None mem1 (seg_rom rsegs)
                 ltac:(vm_compute; reflexivity) Hro1).
        apply (r10a_call34 REPLY) with (phi := phi) (nb := rnb g b) (pa := fr + 2448) (pp := fr + 2464)
          (pn := fr + 2496) (A := A) (spv := sp) (FS := FS) (g := G) (ja := ja) (jp := jp) (jn := jn).
        all: try assumption.
        all: try lia.
      * intros ms (s0 & HQ & HREL & HROs).
        destruct HQ as (R2 & m0' & Es0 & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P21 & P22 & P23 & P24 & P25 &
                        P26 & P27 & P10 & MUn & WMn & STn & RWn & SWn & AWn & FPn).
        subst s0.
        destruct HREL as (Hrg & Hrf & Hpcv & Hsv & Hrv & Hfcs & Hrom & HMR).
        destruct ms as [R1 F1 pc1 svc1 rv1 fc1 mr rom1].
        cbn in Hrg, Hrf, Hpcv, Hsv, Hrv, Hfcs, Hrom, HMR, HROs.
        subst R1 F1 pc1 svc1 rv1 fc1 rom1.
        rewrite HKv in STn, AWn, FPn. rewrite Hret in P10.
        destruct (RWn Hok) as (RW1 & RW2 & RW3).
        eexists. exists (Z_to_bv 64 0x816c4), mr.
        split; [reflexivity|].
        split; [reflexivity|].
        split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
        split; [exact P18|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|].
        split; [exact P23|]. split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
        split; [exact P27|]. split; [exact P10|].
        split; [apply (munch_rel rsegs _ mem1 (normalize rsegs mem1) mr m0' REL HMR HROs); exact MUn|].
        split; [apply (wmono_rel rsegs mem1 (normalize rsegs mem1) mr m0' REL HMR HROs); exact WMn|].
        split; [exact (ro_agree_same rsegs mem1 mr Hro1 HROs)|].
        split; [apply (proj2 (r10a_stk_iff mr m0' (sp - 9072) sp HMR ltac:(lia) ltac:(lia))); exact STn|].
        split; [exact (r10a_rw_back mr m0' _ _ HMR RW1)|].
        split; [exact (r10a_rw_back mr m0' _ _ HMR RW2)|].
        split; [exact (r10a_rw_back mr m0' _ _ HMR RW3)|].
        split; [apply (proj2 (r10a_shadow_iff mr m0' HMR)); exact SWn|].
        split; [apply (proj2 (r10a_addr_iff mr m0' _ _ HMR)); exact AWn|].
        apply (proj2 (r10a_fp_iff [1%nat] mr m0' _ FS _ _ _ _ HMR ltac:(lia) ltac:(lia))).
        rewrite <- Htp. exact FPn.
    + intros R3 pc' mem2 regs2 md2
        (Hpc2 & L2 & L3 & L4 & L8 & L9 & L18 & L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27 & L10 &
         MU2 & WM2 & RO2 & ST2 & RW1 & RW2 & RW3 & SW2 & AW2 & FP2) Hreg2 Hmat2.
      subst pc'.
      assert (G2 : getr regs2 2 = getr regs1 2) by (rewrite Hreg2; exact L2).
      assert (G3 : getr regs2 3 = getr regs1 3) by (rewrite Hreg2; exact L3).
      assert (G4 : getr regs2 4 = getr regs1 4) by (rewrite Hreg2; exact L4).
      assert (G8 : getr regs2 8 = getr regs1 8) by (rewrite Hreg2; exact L8).
      assert (G9 : getr regs2 9 = getr regs1 9) by (rewrite Hreg2; exact L9).
      assert (G19 : getr regs2 19 = getr regs1 19) by (rewrite Hreg2; exact L19).
      assert (G26 : getr regs2 26 = getr regs1 26) by (rewrite Hreg2; exact L26).
      assert (F18 : getr regs2 18 = getr regs 18) by (rewrite Hreg2, L18; exact E18).
      assert (F21 : getr regs2 21 = getr regs 21) by (rewrite Hreg2, L21; exact E21).
      assert (F22 : getr regs2 22 = getr regs 22) by (rewrite Hreg2, L22; exact E22).
      assert (F23 : getr regs2 23 = getr regs 23) by (rewrite Hreg2, L23; exact E23).
      assert (F24 : getr regs2 24 = getr regs 24) by (rewrite Hreg2, L24; exact E24).
      assert (F25 : getr regs2 25 = getr regs 25) by (rewrite Hreg2, L25; exact E25).
      (* the side stack's state after the call *)
      assert (HFSOK2 : ACw.a_fs_ok mem2 FS).
      { apply (fp_post_fs_ok mem1 mem2 [1%nat] (ACw.as_tp ACw.ASYMS) FS (sp - 9072) sp _ _
                 (r10a_WC phi (rnb g b) fr sp FS G) Hcs Hok0 ltac:(lia) ltac:(lia) FP2 MU2 WM2).
        intros q Hq Hcls. destruct (Hcls 1%nat (or_introl eq_refl)) as (Hh & Hf).
        rewrite r10a_fs_hint1 in Hh. rewrite r10a_fs_flag1 in Hf.
        replace (fs_M 1%nat) with 8192 in Hf by reflexivity.
        unfold r10a_hide in HFSlow. apply r10a_out_WC; lia. }
      assert (HWin2 : forall x, ~ LF.outside (r10a_WC phi (rnb g b) fr sp FS G) x ->
                        r10a_in fr (ACw.aspZ regs1) 9072 FS x).
      { intros x Hx. rewrite Hasp1. unfold r10a_in.
        pose proof (r10a_in_WC phi (rnb g b) fr sp FS G x Hx). lia. }
      assert (Hrd2 : forall x, ~ LF.outside (r10a_WC phi (rnb g b) fr sp FS G) x ->
                       exists bb, mrd rsegs mem2 (wa x) = Some bb).
      { intros x Hx.
        pose proof FP2 as (DT2 & TS2 & C2 & T2 & DB2 & k2 & _ & _ & (_ & _ & _ & _ & (_ & _ & HFSs2)) & _).
        destruct (r10a_in_WC phi (rnb g b) fr sp FS G x Hx) as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
        - exact (r10a_rw_rd mem2 _ _ _ x RW1 ltac:(lia)).
        - exact (r10a_rw_rd mem2 _ _ _ x RW2 ltac:(lia)).
        - exact (r10a_rw_rd mem2 _ _ _ x RW3 ltac:(lia)).
        - destruct ST2 as (_ & _ & HS2). exact (proj2 (HS2 x H)).
        - exact (proj2 (HFSs2 x ltac:(lia))).
        - exact (proj2 (HFSs2 x ltac:(lia))).
        - exact (proj2 (HFSs2 x ltac:(lia))).
        - apply (proj2 (SW2 x (r10a_sh_ivl (FS + 1085440) (FS + 2134016) x
                                  (fun a Ha => HFSapp0 a ltac:(lia)) H))).
        - apply (proj2 (SW2 x (r10a_sh_ivl (sp - 9072) sp x
                                  (fun a Ha => ltac:(unfold app_mem; right; lia)) H))). }
      destruct (r10a_land g fr (hb1 phi (rnb g b)) regs1 regs2 mem1 mem2 md1 FS 9072
                  (r10a_WC phi (rnb g b) fr sp FS G) HFRA2 HENT2 Hwtp HFSr ltac:(rewrite HFN; lia)
                  ltac:(reflexivity) MU2 WM2 RO2 HFSOK2
                  (r10a_WC_rt phi (rnb g b) fr sp FS G ltac:(lia) ltac:(lia) ltac:(lia)) HWin2 Hrd2 SW2
                  ltac:(rewrite Hasp1; exact AW2) G2 G3 G4 G8 G9 G19 G26) as (HFRA3 & HENT3).
      pose proof (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs2 regs2 mem2 md1 md2 HFRA3
                    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat2) as HFRA4.
      pose proof (ent_mat APIf g (hb1 phi (rnb g b)) mem2 md1 md2 HENT3 Hmat2) as HENT4.
      assert (HK2 : r10a_K g b phi fr regs2 mem2).
      { pose proof (r10a_blk_outC g fr _ regs1 mem1 md1 phi (rnb g b) FS phi (rnb g b) G HFRA2
                      (r10a_hb_in phi (rnb g b) (g_H g)) Hwtp HFSr) as (HoP1 & HoPS1).
        rewrite Hasp1 in HoP1, HoPS1.
        apply (r10a_keep g b phi fr regs1 regs2 mem1 mem2 (r10a_WC phi (rnb g b) fr sp FS G) A HK1 MU2 WM2 G9
                 Hr9_1 HA0 HA1 Hb4 ltac:(lia) Hfr8).
        - intros x Hx. apply r10a_out_WC; lia.
        - intros x Hx Hnx. unfold r10a_hide in HLH, Hpl. apply r10a_out_WC; lia.
        - exact HoP1.
        - intros k Hk Hk'.
          pose proof (r10a_sh_mono (FS + 2134016) fr ltac:(lia)) as M1. change (shadow_addr fr) with (Sfr fr) in M1.
          unfold r10a_hide in HLH, Hpl, HFSlow. destruct Hpl as [Hp|Hp].
          + pose proof (r10a_sh_mono (fr + 8 * FRAME_SHADOW) (sp - 9072) ltac:(lia)) as M2. rewrite r10a_sh8 in M2.
            apply r10a_out_WC; lia.
          + pose proof (r10a_sh_mono sp fr ltac:(lia)) as M2. change (shadow_addr fr) with (Sfr fr) in M2.
            apply r10a_out_WC; lia.
        - rewrite Hasz. exact HoPS1.
        - intros Hn.
          pose proof (r10a_blk_outC g fr _ regs1 mem1 md1 (g_p g) (g_n g) FS phi (rnb g b) G HFRA2
                        (in_or_app _ _ _ (or_intror (proj1 (HPBLK Hn)))) Hwtp HFSr) as (HoI1 & _).
          rewrite Hasp1 in HoI1. exact HoI1.
        - intros Hn.
          pose proof (r10a_blk_outC g fr _ regs1 mem1 md1 (g_p g) (g_n g) FS phi (rnb g b) G HFRA2
                        (in_or_app _ _ _ (or_intror (proj1 (HPBLK Hn)))) Hwtp HFSr) as (_ & HoIS1).
          rewrite Hasp1 in HoIS1. exact HoIS1. }
      destruct HK2 as (HHB2 & HOUR2 & HOUTA2 & H112'' & H128'' & HPRO'' & H104'' & H96'' & H64'' & H144'' &
        H208'' & HC2688'' & HC2768'' & H280'' & H240'' & HC2960'' & HC2976'' & H152'' & HA2176'' &
        HID'' & HFG'' & HPHI'' & HRXS'').
      rewrite <- SEGS. apply Hexit.
      exists phi, regs2, mem2, md2, fr.
      split; [reflexivity|]. split; [exact HFRA4|]. split; [exact HENT4|].
      split.
      { split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHB2|].
        split; [unfold rg; rewrite F23; exact Hr23|].
        split; [exact HOUR2|]. split; [exact HOUTA2|].
        split; [destruct HCUR as (Hc0 & Hc22 & Hc25); unfold CUR, rg in *;
                split; [exact Hc0|]; split; [rewrite F22; exact Hc22 | rewrite F25; exact Hc25]|].
        split; [exact H112''|]. split; [exact H128''|]. split; [exact HPRO''|]. split; [exact H104''|].
        split; [exact H96''|]. split; [exact H64''|]. split; [exact H144''|]. split; [exact H208''|].
        split; [exact HC2688''|]. split; [exact HC2768''|]. split; [exact H280''|]. split; [exact H240''|].
        split; [exact HC2960''|]. split; [exact HC2976''|]. split; [exact H152''|].
        split; [unfold rg in *; rewrite F21; exact Hr21 | exact HA2176'']. }
      split; [lia|].
      split; [unfold a0v, rg; rewrite Hreg2; exact L10|].
      split.
      { split.
        - split.
          + split; [exact Hb6|].
            split; [destruct HCUR as (Hc0 & Hc22 & Hc25); unfold CUR, rg in *;
                    split; [exact Hc0|]; split; [rewrite F22; exact Hc22 | rewrite F25; exact Hc25]|].
            split; [exact HOUR2|]. split; [unfold rg; rewrite F23; exact Hr23|].
            split; [exact HID'' | exact HFG''].
          + split; [exact Hnz|]. split; [unfold rg; rewrite F24; exact Hr24 | exact HPHI''].
        - unfold rg; rewrite F18; exact Hr18. }
      split; [exact HRXS''|].
      split; [exact RW1|]. split; [exact RW2 | exact RW3].
Qed.

(* ---- arm b = 0 ---- *)
Lemma r10a_b0 : Hat B APIf ra (Inv_A81768_at (fx := fx) B APIf ra) 0%nat ->
  Hat B APIf ra (Inv_A81680_at (fx := fx) B APIf ra) 0%nat.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & HBODY & HX).
  subst c.
  destruct HBODY as (Hgn & Hb6 & HHB & Hr23 & HOUR & HOUTA & HCUR & H112 & H128 & HPRO & H104 & H96 & H64 &
    H144 & H208 & HC2688 & HC2768 & H280 & H240 & HC2960 & HC2976 & H152 & Hr21 & HA2176).
  pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPBLK & _).
  destruct HX as (HRF & HRXS & Ha0 & Hr27).
  destruct HRF as (((_ & _ & _ & _ & HID & HFG) & Hnz & Hr24 & HPHI) & Hr18).
  assert (Hb4 : (0 <= 4)%nat) by lia.
  change (Z.of_nat 0) with 0 in Ha0, Hr23.
  rewrite (a_rtm_k0 (g_in g)) in Ha0.
  assert (HK0 : r10a_K g 0 phi fr regs mem) by (unfold r10a_K; tauto).
  destruct (r10a_geo g fr _ regs mem md HFRA) as (A & Hr9 & HA0 & HA1 & HspA & HfrA & HAS & HSE & Hsp16 & Hsph &
    Hlo2 & Hhi2 & HGT & Hfre & Hfr32 & Hfr8 & HLH & Hpl & Happ' & FA1 & FA2).
  pose proof HFRA as HF.
  destruct HF as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 &
    Hr9' & Hr3 & Hr19 & _).
  change (Z.of_nat 0) with 0 in *.
  destruct (a_rtn_u (g_in g) 0 Hnz) as (u & Hu & Hur).
  assert (Hrnb : 124 <= rnb g 0 <= 1492).
  { change (rnb g 0) with (rt_n (g_in g) 0). rewrite Hu. lia. }
  destruct HHB as (Hphinz & HphiA).
  pose proof HphiA as (Hphi0 & _ & HphiE & _).
  assert (Hasz : ACw.a_size (rnb g 0) = rnb g 0) by (unfold ACw.a_size; lia).
  rewrite Hasz in HphiE.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (Hshstk : stk rsegs mem (Sfr fr + 306) (Sfr fr + 306 + Z.of_nat 12)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply (AsanRTInv.RT_shadow_rw _ _ _ HRT).
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10a_fsh; [exact Happ' | lia]. }
  destruct (r10a_ex_C1 mem (Sfr fr + 306) 12 Hshstk) as (xs & Hxs & CH).
  unfold rg in Hr19, Hr23, Hr27, Hr24. unfold a0v, rg in Ha0.
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81680) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81768 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
       getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 13 = Z_to_bv 64 32 /\
       LF.munch [(Sfr fr + 306, Sfr fr + 318)] mem mem' /\ LF.wmono rsegs mem mem' /\
       (exists l12, bytes_at rsegs mem' (Sfr fr + 306) l12 /\ length l12 = 12%nat) /\
       (exists c4 c5 : byte, bytes_at rsegs mem' (Sfr fr + 316) [c4] /\ bv_signed c4 = 0 /\
          bytes_at rsegs mem' (Sfr fr + 317) [c5] /\ bv_signed c5 = 4))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + apply r10a_evt0 with (Sh := Sfr fr) (phi := phi) (xs := xs).
      all: try assumption.
      all: try lia.
    + intros ms' (R & m' & l12 & c4 & c5 & Hms & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P21 & P22 & P23 & P24 &
                  P25 & P26 & P10 & P11 & P12 & P13 & MUq & WMq & Bq & Lq & B4 & V4 & B5 & V5).
      exists R, (Z_to_bv 64 0x81768), m'. split; [exact Hms|].
      split; [reflexivity|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
      split; [exact P18|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
      split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
      split; [exact P10|]. split; [exact P11|]. split; [exact P12|]. split; [exact P13|].
      split; [exact MUq|]. split; [exact WMq|].
      split; [exists l12; split; [exact Bq | exact Lq]|].
      exists c4, c5. split; [exact B4|]. split; [exact V4|]. split; [exact B5 | exact V5].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K10 & K11 & K12 & K13 &
       MU & WM & (l12 & B12 & L12) & (c4 & c5 & B4 & V4 & B5 & V5)) Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (Hrd : forall x, Sfr fr + 306 <= x < Sfr fr + 318 -> exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. apply (r10a_ba_rd mem' (Sfr fr + 306) l12 x B12). rewrite L12.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    destruct (r10a_landS g fr (hb1 phi (rnb g 0)) regs regs'' mem mem' md 306 318 HFRA HENT
                ltac:(lia) ltac:(lia) ltac:(lia) MU WM Hrd E2 E3 E4 E8 E9 E19 E26) as (HFRA1 & HENT1).
    pose proof (sl_fra_move B APIf ra g fr (hb1 phi (rnb g 0)) regs'' regs'' mem' md md' HFRA1
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat) as HFRA2.
    pose proof (ent_mat APIf g (hb1 phi (rnb g 0)) mem' md md' HENT1 Hmat) as HENT2.
    assert (HK1 : r10a_K g 0 phi fr regs'' mem').
    { apply (r10a_keep g 0 phi fr regs regs'' mem mem' [(Sfr fr + 306, Sfr fr + 318)] A HK0 MU WM E9 Hr9
               HA0 HA1 Hb4 ltac:(lia) Hfr8).
      - intros x Hx. cbn [LF.outside]. split; [|exact I]. lia.
      - intros x Hx _. cbn [LF.outside]. split; [|exact I]. lia.
      - exact (proj1 (r10a_blk_outS g fr _ regs mem md phi (rnb g 0) 306 318 HFRA
                        (r10a_hb_in phi (rnb g 0) (g_H g)) ltac:(lia) ltac:(lia))).
      - intros k Hk Hk'. cbn [LF.outside]. split; [|exact I]. lia.
      - rewrite Hasz.
        exact (proj2 (r10a_blk_outS g fr _ regs mem md phi (rnb g 0) 306 318 HFRA
                        (r10a_hb_in phi (rnb g 0) (g_H g)) ltac:(lia) ltac:(lia))).
      - intros Hn. exact (proj1 (r10a_blk_outS g fr _ regs mem md (g_p g) (g_n g) 306 318 HFRA
                        (in_or_app _ _ _ (or_intror (proj1 (HPBLK Hn)))) ltac:(lia) ltac:(lia))).
      - intros Hn. exact (proj2 (r10a_blk_outS g fr _ regs mem md (g_p g) (g_n g) 306 318 HFRA
                        (in_or_app _ _ _ (or_intror (proj1 (HPBLK Hn)))) ltac:(lia) ltac:(lia))). }
    destruct HK1 as (HHB1 & HOUR1 & HOUTA1 & H112' & H128' & HPRO' & H104' & H96' & H64' & H144' & H208' &
      HC2688' & HC2768' & H280' & H240' & HC2960' & HC2976' & H152' & HA2176' & HID' & HFG' &
      HPHI' & HRXS').
    pose proof HRXS' as (X48 & X56 & X88 & X80 & X72 & X16 & X8 & X192 & X216 & XA2256).
    (* fr + 2528's 12 bytes: the shadow bytes S(fr) + 316 = 0 (8 bytes) and S(fr) + 317 = 4 (4 bytes) *)
    assert (HA2528 : addressable mem' (fr + 2528) 12).
    { assert (A1 : addressable mem' (fr + 2528) 8).
      { apply (r10a_addr_cell mem' fr 2528 8 c4); try lia.
        - intros a Ha. apply Happ'. lia.
        - change (2528 / 8) with 316. exact B4. }
      assert (A2 : addressable mem' (fr + 2528 + 8) 4).
      { replace (fr + 2528 + 8) with (fr + 2536) by lia.
        apply (r10a_addr_cell mem' fr 2536 4 c5); try lia.
        - intros a Ha. apply Happ'. lia.
        - change (2536 / 8) with 317. exact B5. }
      exact (r10a_addr_cat mem' (fr + 2528) 8 4 A1 A2). }
    rewrite <- SEGS. apply Hexit.
    exists phi, 0%nat, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA2|]. split; [exact HENT2|].
    split.
    { split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHB1|].
      split; [unfold rg; rewrite E23; exact Hr23|].
      split; [exact HOUR1|]. split; [exact HOUTA1|].
      split; [destruct HCUR as (Hc0 & Hc22 & Hc25); unfold CUR, rg in *;
              split; [exact Hc0|]; split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]|].
      split; [lia|].
      split; [unfold rg; rewrite Hreg, K10; f_equal; lia|].
      split; [unfold rg; rewrite Hreg, K12; f_equal; lia|].
      unfold rg; rewrite Hreg, K13; f_equal; lia. }
    split; [reflexivity|].
    split; [lia|].
    split; [unfold rg; rewrite Hreg, K11; reflexivity|].
    split.
    { split.
      - split.
        + split; [exact Hb6|].
          split; [destruct HCUR as (Hc0 & Hc22 & Hc25); unfold CUR, rg in *;
                  split; [exact Hc0|]; split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]|].
          split; [exact HOUR1|]. split; [unfold rg; rewrite E23; exact Hr23|].
          split; [exact HID' | exact HFG'].
        + split; [exact Hnz|]. split; [unfold rg; rewrite E24; exact Hr24 | exact HPHI'].
      - unfold rg; rewrite E18; exact Hr18. }
    split; [exact H112'|]. split; [exact X16|]. split; [exact X8|]. split; [exact X192|].
    split; [exact X216|]. split; [exact HA2528|].
    split; [exact H128'|]. split; [exact HPRO'|]. split; [exact H104'|]. split; [exact H96'|].
    split; [exact H64'|].
    split; [unfold rg in *; rewrite E21; exact Hr21|].
    split; [exact H144'|]. split; [exact H208'|].
    split; [exact HC2688'|]. split; [exact HC2768'|].
    split; [exact H280'|]. split; [exact H240'|].
    split; [exact HC2960'|]. split; [exact HC2976'|].
    split; [exact H152'|]. split; [exact HA2176' | exact HRXS'].
Qed.

End R10A.
