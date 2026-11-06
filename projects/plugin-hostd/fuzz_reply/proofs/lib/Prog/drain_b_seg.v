(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memchr_c memmove_c memcpy_c strrchr_c strcmp_c
  strncmp_c strlen_c __errno_location_c.
Import ListNotations.
Open Scope Z_scope.

(* Kind A segments of drain (plain [0x135d0, 0x13a58)) between its Kind B calls (realloc, list_push, free,
   send_line, strndup). The register file at the for loop's top (0x1362c): sp = S - 128, s0 = s, s6 = 4, s7 = 384,
   s8 = 0x1000, s10 = 1, s11 = 0x30fc0 (g_thread_up, the base of the harness table g_s at +128); the frame at
   S - 128 holds two scratch words (0(sp), 8(sp)), LINE_LIMIT + 1 = 6001 at 16(sp) and the saved registers. *)

Definition DR_TU : Z := 0x30fc0.

(* The saved registers at 24(sp) .. 120(sp). *)
Definition dr_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma dr_cut : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[W Bs] (H0 & H1 & H)] ->.
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in Bs. apply bytes_at_app in Bs. destruct Bs as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma dr_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

(* A word cell read as its eight bytes. *)
Lemma dr_c8_cb : forall m A v, rw_cells rsegs m A [C8 v] -> rw_cells rsegs m A [CB 8 (le8 v)].
Proof.
  intros m A v [[_ Bs] W]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply length_le8|exact I].
  - exact Bs.
  - exact W.
Qed.

Lemma dr_prologue : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m (bv_unsigned sp - 128) [CB 128 junk] -> 128 <= bv_unsigned sp ->
  evt rsegs (fun ms => exists m' j0 j1,
      ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 a0 s1 (Z_to_bv 64 6001) a1 a2 a3 a4 a5 a6
                   a7 s2 s3 s4 s5 (Z_to_bv 64 4) (Z_to_bv 64 384) (Z_to_bv 64 4096) s9 (Z_to_bv 64 1)
                   (Z_to_bv 64 DR_TU) t3 t4 t5 t6)
              F (Z_to_bv 64 0x1362c) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      length j0 = 8%nat /\ length j1 = 8%nat /\
      rw_cells rsegs m' (bv_unsigned sp - 128)
        ([CB 8 j0; CB 8 j1; C8 (Z_to_bv 64 6001)] ++ dr_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk FR LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize] in FB.
  assert (LJ : length junk = 128%nat) by (destruct FR as [[[W _] _] _]; exact W).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs _ _ [] 128%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) in * by lia.
  do 23 step.
  apply evt_done. eexists. exists (firstn 8 junk), (firstn 8 (skipn 8 junk)). split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [rewrite firstn_length; lia|]. split; [rewrite firstn_length, skipn_length; lia|].
  unfold dr_saved. cbn [app]. exact FR.
Qed.

(* The relay entry s at SA: fd, eof, skip, pad, buf, used, cap, held, nheld, pad (struct.relay's source_t). *)
Notation dr_ent fd eof sk p1 buf used cap hp nh p2 :=
  [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 eof); C4 (Z_to_bv 64 sk); CB 4 p1; C8 (Z_to_bv 64 buf);
   C8 (Z_to_bv 64 used); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 hp); C4 (Z_to_bv 64 nh); CB 4 p2].

(* The capacity drain grows the buffer to: cap ? cap * 2 : 8192. *)
Definition dr_grow (cap : Z) : Z := if cap =? 0 then 8192 else cap * 2.

(* Normalising the words the step tactic leaves: unsigned of a literal in range, shifts as products/quotients. *)
Ltac dlia := first [ lia | Z.div_mod_to_equations; lia ].
Ltac dr_nm := repeat match goal with
  | |- context [Z.shiftr ?x ?n] => rewrite (Z.shiftr_div_pow2 x n) by lia
  | |- context [Z.shiftl ?x ?n] => rewrite (Z.shiftl_mul_pow2 x n) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with context [bv_unsigned (Z_to_bv 64 _)] => fail | _ => idtac end;
      rewrite (unsigned_lit z) by dlia
  end.
Ltac dr_cb := first [ reflexivity | apply Z.ltb_lt; dlia | apply Z.ltb_ge; dlia | apply Z.leb_le; dlia
                    | apply Z.leb_gt; dlia | apply Z.eqb_eq; dlia | apply Z.eqb_neq; dlia ].
Ltac dr_cr := lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); dr_cr
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); dr_cr
  | _ => dr_cb end.
(* Take the branch b (true: taken). *)
Ltac dr_if b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; dr_nm; dr_cr]
  end.

(* The for loop's top (relay.c:176): the growth test; with fewer than 4096 free bytes, the realloc call. *)
Lemma dr_top : forall x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA buf used cap : Z),
  rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used); C8 (Z_to_bv 64 cap)] ->
  0 <= used <= cap -> cap <= 2 ^ 20 -> 0 <= buf < 2 ^ 64 ->
  evt rsegs (fun ms => exists x9' x13',
      (4096 <= cap - used /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9' (Z_to_bv 64 buf) (Z_to_bv 64 (cap - used))
                    (Z_to_bv 64 used) x13' x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13670) fc None m (seg_rom rsegs)) \/
      (cap - used < 4096 /\
       ms = MS (mkR (Z_to_bv 64 0x1365c) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 (dr_grow cap)) (Z_to_bv 64 buf)
                    (Z_to_bv 64 (dr_grow cap)) (Z_to_bv 64 used) x13' x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                    x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x17010) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1362c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m SA buf used cap HC HU HCAP HB.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  step. step. step. step. step. step.
  destruct (Z.ltb_spec (cap - used) 4096) as [LT|GE].
  - dr_if false. step.
    destruct (Z.eqb_spec cap 0) as [C0|C0].
    + subst cap. dr_if false. step. step. step. step. dr_nm.
      apply evt_done. exists x9. eexists. right. split; [lia|reflexivity].
    + dr_if true. step. step. step. dr_nm.
      unfold dr_grow. rewrite (proj2 (Z.eqb_neq cap 0) C0).
      apply evt_done. exists x9. eexists. right. split; [lia|reflexivity].
  - dr_if true. dr_nm. apply evt_done. do 2 eexists. left. split; [lia|reflexivity].
Qed.

(* After realloc returned the new buffer res (relay.c:189-190): s->buf = res, s->cap = c. *)
Lemma dr_regrow : forall x1 sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA buf used cap res c : Z),
  rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used); C8 (Z_to_bv 64 cap)] ->
  0 <= used <= c -> c <= 2 ^ 20 -> 0 < res < 2 ^ 64 ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 c) (Z_to_bv 64 res) (Z_to_bv 64 (c - used))
                   (Z_to_bv 64 used) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13670) fc None m' (seg_rom rsegs) /\
      munch [(SA + 16, SA + 40)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (SA + 16) [C8 (Z_to_bv 64 res); C8 (Z_to_bv 64 used); C8 (Z_to_bv 64 c)])
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 c) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18
             x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1365c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m SA buf used cap res c HC HU HCAP HR.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(SA + 16, SA + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. dr_if false.
  step. step. step. step. dr_nm.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact HC.
Qed.

(* realloc returned NULL (relay.c:183-190): on to s->eof = 1 and the return (dr_eof at 0x139f0). *)
Lemma dr_nomem : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms =>
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                   x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x139f0) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1365c) fc None m (seg_rom rsegs)).
Proof. intros. step. dr_if true. apply evt_done. reflexivity. Qed.

Lemma dr_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* The harness's source_of (fuzz_reply.c:206-214), inlined: g_s[i] for i = j is the first open source with s's fd. *)
Lemma dr_scan : forall (k : nat) x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25
    x26 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fd i j : Z),
  Z.of_nat k = j - i -> 0 <= i <= j -> j < 4 -> 0 <= fd < 2 ^ 31 ->
  (forall i', i <= i' < j -> exists f o, rw_cells rsegs m (DR_TU + 96 * i' + 128) [C4 (Z_to_bv 64 f); C4 (Z_to_bv 64 o)] /\
     (o = 0 \/ (0 <= f < 2 ^ 31 /\ f <> fd))) ->
  rw_cells rsegs m (DR_TU + 96 * j + 128) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1)] ->
  evt rsegs (fun ms => exists x12',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12' (Z_to_bv 64 (96 * j)) (Z_to_bv 64 fd) x15 x16 x17 x18
                   (Z_to_bv 64 (DR_TU + 96 * j)) x20 x21 x22 (Z_to_bv 64 384) x24 x25 x26 (Z_to_bv 64 DR_TU)
                   x28 x29 x30 x31)
              F (Z_to_bv 64 0x1369c) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 (Z_to_bv 64 (96 * i)) (Z_to_bv 64 fd) x15 x16 x17 x18
             x19 x20 x21 x22 (Z_to_bv 64 384) x24 x25 x26 (Z_to_bv 64 DR_TU) x28 x29 x30 x31)
        F (Z_to_bv 64 0x1367c) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25
    x26 x28 x29 x30 x31 F fc m fd i j Hk Hi Hj Hfd HO HJ; unfold DR_TU in *.
  - assert (i = j) by lia. subst i.
    pose proof (rw_cells_bound _ _ _ _ HJ) as CB0. cbn [cells_size csize] in CB0.
    step. dr_nm. step. rewrite (dr_sx32 1) by lia. step. dr_if false.
    step. rewrite (dr_sx32 fd) by lia. step. dr_if true.
    apply evt_done. eexists. reflexivity.
  - destruct (HO i ltac:(lia)) as (f & o & HC & Ho).
    pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
    step. dr_nm.
    assert (TAIL : forall a2, evt rsegs (fun ms => exists x12',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12' (Z_to_bv 64 (96 * j)) (Z_to_bv 64 fd) x15 x16 x17 x18
                   (Z_to_bv 64 (200640 + 96 * j)) x20 x21 x22 (Z_to_bv 64 384) x24 x25 x26 (Z_to_bv 64 200640)
                   x28 x29 x30 x31)
              F (Z_to_bv 64 0x1369c) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 a2 (Z_to_bv 64 (96 * i)) (Z_to_bv 64 fd) x15 x16 x17 x18
             (Z_to_bv 64 (200640 + 96 * i)) x20 x21 x22 (Z_to_bv 64 384) x24 x25 x26 (Z_to_bv 64 200640) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13690) fc None m (seg_rom rsegs))).
    { intros a2. step. dr_nm. step. dr_if true.
      replace (96 * i + 96) with (96 * (i + 1)) by lia.
      exact (IH x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 a2 x15 x16 x17 x18 _ x20 x21 x22 x24 x25 x26 x28 x29 x30 x31
               F fc m fd (i + 1) j ltac:(lia) ltac:(lia) Hj Hfd (fun i' Hi' => HO i' ltac:(lia)) HJ). }
    step.
    destruct Ho as [-> | (Hf & Hne)].
    + rewrite (dr_sx32 0) by lia. step. dr_if true. apply TAIL.
    + step. if_cases E.
      * apply TAIL.
      * step. rewrite (dr_sx32 f) by lia. step. dr_if false. apply TAIL.
Qed.

(* drain's epilogue (0x139f8): the saved registers back, sp = S, return to the saved ra. *)
Lemma dr_epi : forall ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (SP : Z),
  rw_cells rsegs m (SP + 24) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  0 <= SP -> SP + 128 < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ms = MS (mkR ra0 (Z_to_bv 64 (SP + 128)) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
             x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m SP HF H0 H1.
  unfold dr_saved in HF.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB0. cbn [cells_size csize] in CB0.
  do 15 step. dr_nm.
  apply evt_done. reflexivity.
Qed.

(* s->eof = 1, then the epilogue (relay.c:182-185, :200-203). *)
Lemma dr_eof : forall ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (SP SA fd eof sk : Z),
  rw_cells rsegs m (SP + 24) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 eof); C4 (Z_to_bv 64 sk)] ->
  0 <= SP -> SP + 128 < 2 ^ 64 -> SA + 12 <= SP + 24 \/ SP + 128 <= SA ->
  evt rsegs (fun ms => exists m' x10',
      ms = MS (mkR ra0 (Z_to_bv 64 (SP + 128)) gp tp x5 x6 x7 s0 s1 x10' x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      munch [(SA + 4, SA + 8)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 sk)] /\
      rw_cells rsegs m' (SP + 24) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139f0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m SP SA fd eof sk HF HE H0 H1 HD.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB0. cbn [cells_size csize dr_saved] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HE) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(SA + 4, SA + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold dr_saved in HF.
  step. step.
  eapply evt_mono; [apply (dr_epi ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); [exact HF | lia | lia]|].
  intros ms ->. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  split; [exact HE | exact HF].
Qed.

Lemma dr_ret_even : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z H1 H2. apply ret_pc_even; assumption. Qed.

(* fuzz_recv with h.eintr = 1 (fuzz_reply.c:250-254): h.eintr = 0, errno = EINTR, -1; drain continues
   (relay.c:194). X = &g_s[j] - 128. *)
Lemma dr_eintr : __errno_location_contract ->
  forall x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X fd op cl : Z) (ev : word),
  rw_cells rsegs m (X + 128) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 cl); C4 (Z_to_bv 64 1)] ->
  rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
  0 <= X -> 0 <= bv_unsigned tp + -164 ->
  X + 144 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -160 <= X + 128 ->
  evt rsegs (fun ms => exists m' x1' x10' x12',
      ms = MS (mkR x1' sp gp tp x5 x6 x7 s0 x9 x10' x11 x12' x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21
                   (Z_to_bv 64 4) x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x1362c) fc None m' (seg_rom rsegs) /\
      munch [(X + 140, X + 144); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (X + 128) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 cl); C4 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 4)])
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 (Z_to_bv 64 4)
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1369c) fc None m (seg_rom rsegs)).
Proof.
  intros EL x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m X fd op cl ev HS HE HX HT HD.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HE) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(X + 140, X + 144); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (dr_sx32 1) by lia. step. dr_if false.
  step. step.
  eapply evt_cut; [apply EL|]. intros ms' ->. unfold ERRNO_TP_OFF.
  rewrite (dr_ret_even 0x136ac) by lia.
  step. step.
  apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  split; assumption.
Qed.

(* fuzz_recv with no pending text of a closed source (fuzz_reply.c:256-258): 0, so s->eof = 1 and drain returns. *)
Lemma dr_closed : forall ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (SP SA X fd eof sk sfd op pv pc : Z),
  rw_cells rsegs m (SP + 24) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 eof); C4 (Z_to_bv 64 sk)] ->
  rw_cells rsegs m (X + 128) [C4 (Z_to_bv 64 sfd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 pc)] ->
  0 <= SP -> SP + 128 < 2 ^ 64 -> SA + 12 <= SP + 24 \/ SP + 128 <= SA -> 0 <= X ->
  evt rsegs (fun ms => exists m' x10' x12',
      ms = MS (mkR ra0 (Z_to_bv 64 (SP + 128)) gp tp x5 x6 x7 s0 s1 x10' x11 x12' x13 x14 x15 x16 x17 s2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      munch [(SA + 4, SA + 8)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 sk)])
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X)
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1369c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m SP SA X fd eof sk sfd op pv pc HF HE HS HP H0 H1 HD HX.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HP) as CB1. cbn [cells_size csize] in CB1.
  step. rewrite (dr_sx32 0) by lia. step. dr_if true.
  step. rewrite (dr_sx32 0) by lia. step. dr_if true.
  step. rewrite (dr_sx32 1) by lia. step. dr_if true.
  eapply evt_mono; [eapply (dr_eof ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); eassumption|].
  intros ms (m' & x10' & -> & MU & WM & HE' & _). do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact HE'].
Qed.

(* fuzz_recv with no pending text of an open source (fuzz_reply.c:259-260): errno = EAGAIN, -1; drain returns. *)
Lemma dr_again : __errno_location_contract ->
  forall ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (SP SA X sfd op pv pc : Z) (ev : word),
  rw_cells rsegs m (SP + 24) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m (X + 128) [C4 (Z_to_bv 64 sfd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 pc)] ->
  rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
  0 <= SP -> SP + 128 < 2 ^ 64 -> 0 <= X -> 0 <= bv_unsigned tp + -164 ->
  bv_unsigned tp + -160 <= SP + 24 \/ SP + 128 <= bv_unsigned tp + -164 ->
  evt rsegs (fun ms => exists m' x10' x11' x12',
      ms = MS (mkR ra0 (Z_to_bv 64 (SP + 128)) gp tp x5 x6 x7 s0 s1 x10' x11' x12' x13 x14 x15 x16 x17 s2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 11)])
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X)
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1369c) fc None m (seg_rom rsegs)).
Proof.
  intros EL ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m SP SA X sfd op pv pc ev HF HS HP HE H0 H1 HX HT HD.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HP) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HE) as CB2. cbn [cells_size csize] in CB2.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB3. cbn [cells_size csize dr_saved] in CB3.
  pose proof (munch_refl [(bv_unsigned tp + -164, bv_unsigned tp + -160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold dr_saved in HF.
  step. rewrite (dr_sx32 0) by lia. step. dr_if true.
  step. rewrite (dr_sx32 0) by lia. step. dr_if true.
  step. rewrite (dr_sx32 0) by lia. step. dr_if false.
  step.
  eapply evt_cut; [apply EL|]. intros ms' ->. unfold ERRNO_TP_OFF.
  rewrite (dr_ret_even 0x13a40) by lia.
  step. step. step.
  eapply evt_mono; [apply (dr_epi ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); [exact HF | lia | lia]|].
  intros ms ->. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | assumption].
Qed.

(* recv (s->fd, s->buf + s->used, ...) (relay.c:193): the scan for s's harness source g_s[j]. *)
Lemma dr_find : forall x1 sp gp tp x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25
    x26 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA fd eof sk buf used j : Z),
  rw_cells rsegs m SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 eof); C4 (Z_to_bv 64 sk)] ->
  0 <= j < 4 -> 0 <= fd < 2 ^ 31 -> 0 <= buf -> 0 <= used -> buf + used < 2 ^ 64 ->
  (forall i', 0 <= i' < j -> exists f o, rw_cells rsegs m (DR_TU + 96 * i' + 128) [C4 (Z_to_bv 64 f); C4 (Z_to_bv 64 o)] /\
     (o = 0 \/ (0 <= f < 2 ^ 31 /\ f <> fd))) ->
  rw_cells rsegs m (DR_TU + 96 * j + 128) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1)] ->
  evt rsegs (fun ms => exists x12',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 (buf + used)) x11 x12' (Z_to_bv 64 (96 * j))
                   (Z_to_bv 64 fd) x15 x16 x17 x18 (Z_to_bv 64 (DR_TU + 96 * j)) x20 x21 x22 (Z_to_bv 64 384) x24 x25
                   x26 (Z_to_bv 64 DR_TU) x28 x29 x30 x31)
              F (Z_to_bv 64 0x1369c) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 buf) x11 (Z_to_bv 64 used) x13 x14 x15 x16 x17 x18
             x19 x20 x21 x22 (Z_to_bv 64 384) x24 x25 x26 (Z_to_bv 64 DR_TU) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13670) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25
    x26 x28 x29 x30 x31 F fc m SA fd eof sk buf used j HE Hj Hfd Hb Hu Hbu HO HJ.
  pose proof (rw_cells_bound _ _ _ _ HE) as CB0. cbn [cells_size csize] in CB0.
  step. step. rewrite (dr_sx32 fd) by lia. step. dr_nm.
  exact (dr_scan (Z.to_nat j) x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 (buf + used)) x11
           (Z_to_bv 64 used) x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 F fc m fd 0 j
           ltac:(lia) ltac:(lia) ltac:(lia) Hfd HO HJ).
Qed.

(* fuzz_recv's copy (fuzz_reply.c:262-264): n = min (rest of the head text, len) bytes into s->buf + s->used, then
   reference_feed's loop over them set up (fuzz_reply.c:265, :219-221): s4 = p, s5 = p + n, s2 = &h->expected. *)
Lemma dr_data : memcpy_contract ->
  forall x1 sp gp tp x5 x6 x7 s0 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (X sfd op cl pv pn pcap off part np ovl ta tl dst len : Z) (src dj : list byte),
  rw_cells rsegs m (X + 128) [C4 (Z_to_bv 64 sfd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 cl); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv); C4 (Z_to_bv 64 pn); C4 (Z_to_bv 64 pcap)] ->
  rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 ovl)] ->
  rw_cells rsegs m pv [C8 (Z_to_bv 64 ta); C8 (Z_to_bv 64 tl)] ->
  bytes_at rsegs m (ta + off) src -> Z.of_nat (length src) = Z.min (tl - off) len ->
  rw_cells rsegs m dst [CB (Z.to_nat (Z.min (tl - off) len)) dj] ->
  mem_inv rsegs m ->
  0 <= X -> X + 192 <= 2 ^ 64 -> 1 <= pn < 2 ^ 31 -> 0 <= off < tl -> tl < 2 ^ 62 -> 0 < len < 2 ^ 62 ->
  0 <= ta -> ta + tl < 2 ^ 64 -> 0 <= pv -> 0 <= dst -> dst + len < 2 ^ 64 ->
  (dst + len <= ta \/ ta + tl <= dst) ->
  (dst + len <= X + 128 \/ X + 192 <= dst) ->
  (dst + len <= pv \/ pv + 16 <= dst) ->
  evt rsegs (fun ms => exists m' x1' x10' x11' x12' x13' x14' x15' x16' x17' x5' x6' x7' x28' x29' x30' x31',
      ms = MS (mkR x1' sp gp tp x5' x6' x7' s0 (Z_to_bv 64 (Z.min (tl - off) len)) x10' x11' x12' x13' x14' x15' x16' x17'
                   (Z_to_bv 64 (X + 192)) (Z_to_bv 64 X) (Z_to_bv 64 (ta + off))
                   (Z_to_bv 64 (ta + off + Z.min (tl - off) len)) (Z_to_bv 64 4) x23 x24 x25 x26 x27
                   x28' x29' x30' x31')
              F (Z_to_bv 64 0x13704) fc None m' (seg_rom rsegs) /\
      munch [(dst, dst + Z.min (tl - off) len)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' dst [CB (Z.to_nat (Z.min (tl - off) len)) src] /\ bytes_at rsegs m' (ta + off) src)
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 (Z_to_bv 64 dst) (Z_to_bv 64 len) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X)
             x20 x21 (Z_to_bv 64 4) x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1369c) fc None m (seg_rom rsegs)).
Proof.
  intros MC x1 sp gp tp x5 x6 x7 s0 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m X sfd op cl pv pn pcap off part np ovl ta tl dst len src dj
    HS HP HO HR HSRC HLS HD MI HX1 HX2 Hpn Hoff Htl Hlen Hta Htt Hpv Hdst Hdst2 D1 D2 D3.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HP) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB2. cbn [cells_size csize] in CB2.
  pose proof (rw_cells_bound _ _ _ _ HR) as CB3. cbn [cells_size csize] in CB3.
  set (n := Z.min (tl - off) len) in *.
  assert (Hn : 0 < n <= len /\ n <= tl - off) by (subst n; lia).
  step. rewrite (dr_sx32 0) by lia. step. dr_if true.
  step. rewrite (dr_sx32 pn) by lia. step. dr_if false.
  step. step. step. step. dr_nm.
  step.
  match goal with |- evt _ ?Q _ => assert (K : forall v, v = n -> evt rsegs Q
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 (Z_to_bv 64 v) (Z_to_bv 64 dst) (Z_to_bv 64 len) (Z_to_bv 64 pv)
             (Z_to_bv 64 off) x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 (Z_to_bv 64 4) x23 x24 x25 x26 x27 x28 x29
             x30 x31) F (Z_to_bv 64 0x136d4) fc None m (seg_rom rsegs))) end.
  { intros v ->.
    assert (UD : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; lia).
    assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
    assert (UA : bv_unsigned (Z_to_bv 64 (ta + off)) = ta + off) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(dst, dst + n)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    step. step. dr_nm. step. step.
    call (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src dj).
    1: rewrite UA; exact HSRC.
    1: rewrite UN; lia.
    1: rewrite UD, UN; exact HD.
    1: rewrite UD, UN, UA; lia.
    1: exact MI.
    rewrite ?UD, ?UN, ?UA in *.
    step. step. step. dr_if false. step. step. step. step. step. dr_nm.
    replace (ta + (off + n)) with (ta + off + n) by lia.
    apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; assumption. }
  destruct (Z.ltb_spec (tl - off) len) as [LT|GE].
  - dr_if true. apply K. subst n. lia.
  - dr_if false. step. apply K. subst n. lia.
Qed.

Lemma dr_sgn : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus. rewrite unsigned_lit by lia.
  change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

(* Take the signed branch b (true: taken), the signed words' values given as hypotheses bv_signed _ = _. *)
Ltac dr_ifs b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b;
      [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux; fold_closed_in_goal; dr_nm;
                  dr_cr]
  end.

(* s->used += n (relay.c:202) for the n bytes fuzz_recv copied, then memchr (s->buf, 0, s->used) (relay.c:204);
   n = 0 ends the source (relay.c:198-201). *)
Lemma dr_add : forall x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA buf used n : Z),
  rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used)] -> mem_inv rsegs m ->
  0 <= n < 2 ^ 63 -> 0 <= used -> used + n < 2 ^ 64 -> 0 <= buf < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (n = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x139f0) fc None m (seg_rom rsegs)) \/
      (0 < n /\ exists m',
       ms = MS (mkR (Z_to_bv 64 0x137d4) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 n) (Z_to_bv 64 buf)
                    (Z_to_bv 64 0) (Z_to_bv 64 (used + n)) x13 x14 x15 x16 x17 (Z_to_bv 64 buf)
                    (Z_to_bv 64 (used + n)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 MEMCHR) fc None m' (seg_rom rsegs) /\
       munch [(SA + 24, SA + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (used + n))]))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x137ac) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m SA buf used n HC MI HN HU HUN HB.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(SA + 24, SA + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (SN : bv_signed (Z_to_bv 64 n) = n) by (apply dr_sgn; lia).
  step. dr_ifs false. step.
  destruct (Z.eqb_spec n 0) as [N0|N0].
  - dr_if true. apply evt_done. left. split; [exact N0 | reflexivity].
  - dr_if false. step. step. step. step. step. step. step. step. dr_nm.
    apply evt_done. right. split; [lia|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HC].
Qed.

(* The first memchr's result r (relay.c:204): no NUL leaves the buffer as it is (s4 = start = s->buf); a NUL at r
   ends the first line. *)
Lemma dr_hit0 : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  0 <= r < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (r = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x18 x21 x22 x23 x24
                    x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x139b8) fc None m (seg_rom rsegs)) \/
      (r <> 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 r) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137dc) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x137d4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m r Hr.
  step. destruct (Z.eqb_spec r 0) as [R0|R0].
  - dr_if true. step. apply evt_done. left. split; [exact R0 | reflexivity].
  - dr_if false. step. apply evt_done. right. split; [exact R0 | reflexivity].
Qed.

(* A line [st, nul) (relay.c:207-213): with s->skip set or more than LINE_LIMIT bytes, s->skip = 0 and the next
   line; otherwise send_line (st, nul - st + 1). *)
Lemma dr_test : forall x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA sk st nul : Z),
  rw_cells rsegs m (SA + 8) [C4 (Z_to_bv 64 sk)] -> rw_cells rsegs m (SP + 16) [C8 (Z_to_bv 64 6001)] ->
  mem_inv rsegs m -> 0 <= sk < 2 ^ 31 -> 0 <= st <= nul -> nul < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ((sk <> 0 \/ 6001 <= nul - st) /\ exists m' x10' x11',
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 nul) x10' x11' x12 x13 x14 x15
                    x16 x17 (Z_to_bv 64 st) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137f4) fc None m' (seg_rom rsegs) /\
       munch [(SA + 8, SA + 12)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 8) [C4 (Z_to_bv 64 0)]) \/
      (sk = 0 /\ nul - st < 6001 /\
       ms = MS (mkR (Z_to_bv 64 0x13830) (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 nul)
                    (Z_to_bv 64 st) (Z_to_bv 64 (nul - st + 1)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 st) x19 x20 x21
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x131bc) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 nul) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 st) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x137dc) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m SP SA sk st nul HS HL MI Hsk Hst Hnul.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HL) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(SA + 8, SA + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (dr_sx32 sk) by lia.
  step. destruct (Z.eqb_spec sk 0) as [S0|S0].
  - dr_if false. step. step. step. dr_nm.
    destruct (Z.ltb_spec (nul - st) 6001) as [LT|GE].
    + dr_if true. step. step. step. dr_nm.
      apply evt_done. right. split; [exact S0|]. split; [exact LT | reflexivity].
    + dr_if false. step.
      apply evt_done. left. split; [lia|]. do 3 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HS].
  - dr_if true. step.
    apply evt_done. left. split; [lia|]. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HS].
Qed.

(* The next line (relay.c:214, :204): start = nul + 1, memchr (start, 0, s->used - (start - s->buf)). *)
Lemma dr_next : forall x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA buf used nul : Z),
  rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used)] ->
  0 <= buf <= nul -> nul < buf + used -> buf + used < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13818) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 nul) (Z_to_bv 64 (nul + 1))
                   (Z_to_bv 64 0) (Z_to_bv 64 (used - (nul + 1 - buf))) x13 x14 x15 x16 x17 (Z_to_bv 64 (nul + 1))
                   (Z_to_bv 64 (used - (nul + 1 - buf))) (Z_to_bv 64 buf) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 MEMCHR) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 nul) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x137f4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m SA buf used nul HC Hb Hn Hu.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  step. step. step. step. dr_nm. step. step. step. step. step. dr_nm.
  replace (buf - (nul + 1) + used) with (used - (nul + 1 - buf)) by lia.
  apply evt_done. reflexivity.
Qed.

(* The next memchr's result r (relay.c:204): a NUL at r ends the next line; none ends the scan. *)
Lemma dr_hit : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  0 <= r < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (r <> 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 r) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137dc) fc None m (seg_rom rsegs)) \/
      (r = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 r) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x139b8) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13818) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m r Hr.
  step. step. destruct (Z.eqb_spec r 0) as [R0|R0].
  - dr_if false. step. apply evt_done. right. split; [exact R0 | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact R0 | reflexivity].
Qed.

(* s->used -= start - s->buf, memmove (s->buf, start, s->used) (relay.c:216-217): s3 = rem, the bytes left,
   s4 = s->buf, s2 = start. *)
Lemma dr_rest : forall x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA u0 rem : Z),
  rw_cells rsegs m (SA + 24) [C8 (Z_to_bv 64 u0)] -> mem_inv rsegs m -> 0 <= rem < 2 ^ 64 ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR (Z_to_bv 64 0x139cc) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x20 x18 (Z_to_bv 64 rem) x13 x14 x15 x16
                   x17 x18 (Z_to_bv 64 rem) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x1d200) fc None m' (seg_rom rsegs) /\
      munch [(SA + 24, SA + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (SA + 24) [C8 (Z_to_bv 64 rem)])
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 rem) x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139b8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m SA u0 rem HU MI Hr.
  pose proof (rw_cells_bound _ _ _ _ HU) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(SA + 24, SA + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HU].
Qed.

(* The long-line reset (relay.c:218-222): with more than LINE_LIMIT bytes left, s->used = 0 and s->skip = 1; then
   the for loop's top. *)
Lemma dr_back : forall x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA sk u : Z),
  rw_cells rsegs m (SA + 8) [C4 (Z_to_bv 64 sk)] -> rw_cells rsegs m (SA + 24) [C8 (Z_to_bv 64 u)] ->
  rw_cells rsegs m (SP + 16) [C8 (Z_to_bv 64 6001)] -> mem_inv rsegs m -> 0 <= u < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (u < 6001 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 u) (Z_to_bv 64 6001) x12 x13 x14
                    x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1362c) fc None m (seg_rom rsegs)) \/
      (6001 <= u /\ exists m',
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 u) (Z_to_bv 64 6001) x12 x13 x14
                    x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1362c) fc None m' (seg_rom rsegs) /\
       munch [(SA + 8, SA + 12); (SA + 24, SA + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 8) [C4 (Z_to_bv 64 1)] /\ rw_cells rsegs m' (SA + 24) [C8 (Z_to_bv 64 0)]))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             x23 x24 x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139cc) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
    x28 x29 x30 x31 F fc m SP SA sk u HS HU HL MI Hu.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HU) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HL) as CB2. cbn [cells_size csize] in CB2.
  pose proof (munch_refl [(SA + 8, SA + 12); (SA + 24, SA + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. destruct (Z.ltb_spec u 6001) as [LT|GE].
  - dr_if true. apply evt_done. left. split; [exact LT | reflexivity].
  - dr_if false. step. step. step.
    apply evt_done. right. split; [exact GE|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HS | exact HU].
Qed.

(* gesture_seen (s, start) inlined, after send_line returned (relay.c:212, :92): strrchr (line, ' ') with s2 = line.
   Each exit of gesture_seen is the next line (0x137f4). *)
Lemma dr_seen : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x1383c) sp gp tp x5 x6 x7 x8 x9 x18 (Z_to_bv 64 32) x12 x13 x14 x15 x16 x17 x18 x19 x20
                   x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 STRRCHR) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 0x13830) fc None m (seg_rom rsegs)).
Proof. intros. step. step. step. apply evt_done. reflexivity. Qed.

(* strncmp (line, PHD_EVENT_PARAM_GESTURE, verb) with verb = 13 (relay.c:95); s3 = last, strrchr's result. *)
Lemma dr_gverb : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13854) sp gp tp x5 x6 x7 x8 x9 x18 (Z_to_bv 64 0x103e6) (Z_to_bv 64 13) x13 x14 x15
                   x16 x17 x18 x10 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 STRNCMP) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 0x1383c) fc None m (seg_rom rsegs)).
Proof. intros. do 6 step. apply evt_done. reflexivity. Qed.

(* The tests of relay.c:95 after strncmp's result v: line[verb] = ' ', last non-NULL and not line + verb; then
   strcmp (last + 1, PHD_GESTURE_BEGIN) (relay.c:97) with s5 = last + 1. line[verb] is read only when v = 0. *)
Lemma dr_gtest : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v L lst : Z) (b : byte),
  (v = 0 -> rw_cells rsegs m (L + 13) [C1 b]) ->
  0 <= v < 2 ^ 64 -> 0 <= L -> L + 13 < 2 ^ 64 -> 0 <= lst < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ((v <> 0 \/ (v = 0 /\ (bv_unsigned b <> 32 \/ lst = 0 \/ lst = L + 13))) /\ exists x10' x11',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' x11' x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) x20
                    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137f4) fc None m (seg_rom rsegs)) \/
      (v = 0 /\ bv_unsigned b = 32 /\ lst <> 0 /\ lst <> L + 13 /\
       ms = MS (mkR (Z_to_bv 64 0x13884) sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (lst + 1)) (Z_to_bv 64 0x10358) x12 x13
                    x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) x20 (Z_to_bv 64 (lst + 1)) x22 x23 x24 x25 x26 x27
                    x28 x29 x30 x31)
               F (Z_to_bv 64 STRCMP) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) x20
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13854) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m v L lst b HB Hv HL HL13 Hlst.
  pose proof (byte_range b) as RB.
  step. destruct (Z.eqb_spec v 0) as [V0|V0].
  2:{ dr_if true. apply evt_done. left. split; [left; exact V0|]. do 2 eexists. reflexivity. }
  dr_if false. specialize (HB V0).
  pose proof (rw_cells_bound _ _ _ _ HB) as CB0. cbn [cells_size csize] in CB0.
  step. step. step. unfold zxb.
  destruct (Z.eqb_spec (bv_unsigned b) 32) as [B32|B32].
  2:{ dr_if true. apply evt_done. left. split; [right; split; [exact V0 | left; exact B32]|].
      do 2 eexists. reflexivity. }
  dr_if false. step.
  destruct (Z.eqb_spec lst 0) as [S0|S0].
  1:{ dr_if true. apply evt_done. left. split; [right; split; [exact V0 | right; left; exact S0]|].
      do 2 eexists. reflexivity. }
  dr_if false. step. step.
  destruct (Z.eqb_spec lst (L + 13)) as [S1|S1].
  1:{ dr_if true. apply evt_done. left. split; [right; split; [exact V0 | right; right; exact S1]|].
      do 2 eexists. reflexivity. }
  dr_if false. step. step. step. step. step.
  apply evt_done. right. split; [exact V0|]. split; [exact B32|]. split; [exact S0|]. split; [exact S1 | reflexivity].
Qed.

(* begin = !strcmp (last + 1, PHD_GESTURE_BEGIN), its result r kept in s4; not a begin: strcmp (last + 1,
   PHD_GESTURE_END) (relay.c:97-98). *)
Lemma dr_gbeg : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  0 <= r < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (r = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 r) x21 x22
                    x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x138a0) fc None m (seg_rom rsegs)) \/
      (r <> 0 /\
       ms = MS (mkR (Z_to_bv 64 0x1389c) sp gp tp x5 x6 x7 x8 x9 x21 (Z_to_bv 64 0x103af) x12 x13 x14 x15 x16 x17 x18
                    x19 (Z_to_bv 64 r) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 STRCMP) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13884) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m r Hr.
  step. step. destruct (Z.eqb_spec r 0) as [R0|R0].
  - dr_if true. apply evt_done. left. split; [exact R0 | reflexivity].
  - dr_if false. step. step. step. step. apply evt_done. right. split; [exact R0 | reflexivity].
Qed.

(* strcmp (last + 1, PHD_GESTURE_END)'s result r (relay.c:98): neither a begin nor an end returns. *)
Lemma dr_gend : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  0 <= r < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (r <> 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                    x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137f4) fc None m (seg_rom rsegs)) \/
      (r = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                    x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x138a0) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1389c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m r Hr.
  step. destruct (Z.eqb_spec r 0) as [R0|R0].
  - dr_if false. apply evt_done. right. split; [exact R0 | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact R0 | reflexivity].
Qed.

(* The search of s->held for the key [line, last) (relay.c:100), begin's strcmp result bg in s4: with nheld = 0,
   n = 0 in a0 and the test after the search; otherwise bg at 8(sp), nheld at 0(sp), s4 = 8 n = 0,
   s5 = last - line, s8 = s->held, s10 = 8 nheld. *)
Lemma dr_gscan : forall x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA L lst bg held nh : Z) (w0 w1 : word),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 nh)] -> rw_cells rsegs m SP [C8 w0; C8 w1] ->
  mem_inv rsegs m -> SA + 52 <= SP \/ SP + 16 <= SA + 40 ->
  0 <= nh < 2 ^ 31 -> 0 <= L <= lst -> lst < 2 ^ 64 -> 0 <= bg < 2 ^ 64 -> 0 <= held < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (nh = 0 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 0) (Z_to_bv 64 nh) x12 x13 x14 x15
                    x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) (Z_to_bv 64 bg) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13910) fc None m (seg_rom rsegs)) \/
      (0 < nh /\ exists m',
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 (Z_to_bv 64 nh) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 L) (Z_to_bv 64 lst) (Z_to_bv 64 0) (Z_to_bv 64 (lst - L)) x22 x23 (Z_to_bv 64 held) x25
                    (Z_to_bv 64 (nh * 8)) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x138c0) fc None m' (seg_rom rsegs) /\
       munch [(SP, SP + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' SP [C8 (Z_to_bv 64 nh); C8 (Z_to_bv 64 bg)]))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L)
             (Z_to_bv 64 lst) (Z_to_bv 64 bg) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x138a0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m SP SA L lst bg held nh w0 w1 HH HF MI HD Hnh HL Hlst Hbg Hh.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(SP, SP + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (dr_sx32 nh) by lia.
  assert (SN : bv_signed (Z_to_bv 64 nh) = nh) by (apply dr_sgn; lia).
  step. destruct (Z.eqb_spec nh 0) as [N0|N0].
  - dr_ifs true. step. apply evt_done. left. split; [exact N0 | reflexivity].
  - dr_ifs false. step. step. step. step. step. step. dr_nm.
    apply evt_done. right. split; [lia|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HF].
Qed.

(* strlen (s->held[n]) (relay.c:101), s4 = K = 8 n, the slot P = s->held + K holding p. *)
Lemma dr_hlen : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (held K P p : Z),
  P = held + K -> rw_cells rsegs m P [C8 (Z_to_bv 64 p)] ->
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x138d0) sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17 x18 x19
                   (Z_to_bv 64 K) x21 (Z_to_bv 64 p) x23 (Z_to_bv 64 held) (Z_to_bv 64 P) x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 STRLEN) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 K) x21 x22 x23
             (Z_to_bv 64 held) x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x138c0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x26 x27
    x28 x29 x30 x31 F fc m held K P p HP HC.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  step. rewrite <- HP. step. step. step. apply evt_done. reflexivity.
Qed.

(* strlen's result len (relay.c:101): equal to kl = last - line (s5), strncmp (s->held[n], line, kl). *)
Lemma dr_hcmp : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (len kl : Z),
  0 <= len < 2 ^ 64 -> 0 <= kl < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (len <> kl /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 kl)
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x138e8) fc None m (seg_rom rsegs)) \/
      (len = kl /\
       ms = MS (mkR (Z_to_bv 64 0x138e4) sp gp tp x5 x6 x7 x8 x9 x22 x18 (Z_to_bv 64 kl) x13 x14 x15 x16 x17 x18 x19 x20
                    (Z_to_bv 64 kl) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 STRNCMP) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 kl) x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x138d0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m len kl Hl Hk.
  step. destruct (Z.eqb_spec len kl) as [E|E].
  - dr_if false. step. step. step. step. apply evt_done. right. split; [exact E | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact E | reflexivity].
Qed.

(* strncmp's result v (relay.c:101): v = 0 is the key held at the slot P (s9) holding p; a begin (bg = 0,
   relay.c:103) returns, an end frees s->held[n] (relay.c:116-118); s6, s8, s10 back to 4, 0x1000, 1. *)
Lemma dr_hfound : forall x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP P v bg p : Z),
  rw_cells rsegs m (SP + 8) [C8 (Z_to_bv 64 bg)] -> rw_cells rsegs m P [C8 (Z_to_bv 64 p)] ->
  0 <= v < 2 ^ 64 -> 0 <= bg < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (v <> 0 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                    x22 x23 x24 (Z_to_bv 64 P) x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x138e8) fc None m (seg_rom rsegs)) \/
      (v = 0 /\ bg = 0 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 bg) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                    (Z_to_bv 64 4) x23 (Z_to_bv 64 0x1000) (Z_to_bv 64 P) (Z_to_bv 64 1) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137f4) fc None m (seg_rom rsegs)) \/
      (v = 0 /\ bg <> 0 /\
       ms = MS (mkR (Z_to_bv 64 0x1397c) (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 (Z_to_bv 64 4) x23 (Z_to_bv 64 0x1000) (Z_to_bv 64 P) (Z_to_bv 64 1) x27 x28 x29 x30
                    x31)
               F (Z_to_bv 64 0x15664) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 (Z_to_bv 64 P) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x138e4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27
    x28 x29 x30 x31 F fc m SP P v bg p HB HC Hv Hbg.
  pose proof (rw_cells_bound _ _ _ _ HB) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB1. cbn [cells_size csize] in CB1.
  step. destruct (Z.eqb_spec v 0) as [V0|V0].
  2:{ dr_if false. apply evt_done. left. split; [exact V0 | reflexivity]. }
  dr_if true. step. step. step. step. step.
  destruct (Z.eqb_spec bg 0) as [B0|B0].
  - dr_if true. apply evt_done. right. left. split; [exact V0|]. split; [exact B0 | reflexivity].
  - dr_if false. step. step. apply evt_done. right. right. split; [exact V0|]. split; [exact B0 | reflexivity].
Qed.

(* The search's next slot (relay.c:100): K + 8 < 8 nheld goes on with s4 = K + 8; otherwise n = nheld in a0 and a1,
   s4 = bg, s6, s8, s10 back to 4, 0x1000, 1. *)
Lemma dr_hstep : forall x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP K nh bg : Z),
  rw_cells rsegs m SP [C8 (Z_to_bv 64 nh); C8 (Z_to_bv 64 bg)] ->
  0 <= K -> K + 8 < 2 ^ 64 -> 0 <= nh < 2 ^ 31 ->
  evt rsegs (fun ms =>
      (K + 8 <> nh * 8 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (K + 8))
                    x21 x22 x23 x24 x25 (Z_to_bv 64 (nh * 8)) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x138c0) fc None m (seg_rom rsegs)) \/
      (K + 8 = nh * 8 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 nh) (Z_to_bv 64 nh) x12 x13 x14 x15 x16 x17 x18
                    x19 (Z_to_bv 64 bg) x21 (Z_to_bv 64 4) x23 (Z_to_bv 64 0x1000) x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13910) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 K) x21 x22 x23
             x24 x25 (Z_to_bv 64 (nh * 8)) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x138e8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x27
    x28 x29 x30 x31 F fc m SP K nh bg HF HK HK8 Hnh.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB0. cbn [cells_size csize] in CB0.
  step. step. destruct (Z.eqb_spec (K + 8) (nh * 8)) as [E|E].
  - dr_if false. step. step. step. step. step. step. step.
    apply evt_done. right. split; [exact E | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact E | reflexivity].
Qed.

(* After the search (relay.c:103): a begin (bg = 0) not held (n = nheld) grows s->held to 8 (nheld + 1) bytes with
   realloc (relay.c:106); anything else returns (an end not held, relay.c:116). *)
Lemma dr_gadd : forall x1 sp gp tp x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA held bg n nh : Z),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 held)] ->
  0 <= bg < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= nh < 2 ^ 31 ->
  evt rsegs (fun ms =>
      ((bg <> 0 \/ n <> nh) /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 n) (Z_to_bv 64 nh) x12 x13 x14 x15 x16 x17 x18
                    x19 (Z_to_bv 64 bg) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137f4) fc None m (seg_rom rsegs)) \/
      (bg = 0 /\ n = nh /\
       ms = MS (mkR (Z_to_bv 64 0x13928) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 held)
                    (Z_to_bv 64 (nh * 8 + 8)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 bg) x21 x22 x23 x24 x25 x26
                    x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x17010) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 n) (Z_to_bv 64 nh) x12 x13 x14 x15 x16 x17 x18 x19
             (Z_to_bv 64 bg) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13910) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m SA held bg n nh HH Hbg Hn Hnh.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  step. destruct (Z.eqb_spec bg 0) as [B0|B0].
  2:{ dr_if true. apply evt_done. left. split; [left; exact B0 | reflexivity]. }
  dr_if false. step. destruct (Z.eqb_spec n nh) as [N0|N0].
  2:{ dr_if true. apply evt_done. left. split; [right; exact N0 | reflexivity]. }
  dr_if false. step. step. step. step. dr_nm.
  apply evt_done. right. split; [exact B0|]. split; [exact N0 | reflexivity].
Qed.

(* realloc's result res (relay.c:109-112): NULL returns; otherwise s->held = res, strndup (line, last - line). *)
Lemma dr_gnew : forall x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA h0 res L lst : Z),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 h0)] -> mem_inv rsegs m ->
  0 <= res < 2 ^ 64 -> 0 <= L <= lst -> lst < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (res = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L)
                    (Z_to_bv 64 lst) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137f4) fc None m (seg_rom rsegs)) \/
      (res <> 0 /\ exists m',
       ms = MS (mkR (Z_to_bv 64 0x1393c) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 L) (Z_to_bv 64 (lst - L)) x12
                    x13 x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1d59c) fc None m' (seg_rom rsegs) /\
       munch [(SA + 40, SA + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 40) [C8 (Z_to_bv 64 res)]))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L)
             (Z_to_bv 64 lst) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13928) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m SA h0 res L lst HH MI Hr HL Hlst.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(SA + 40, SA + 48)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. destruct (Z.eqb_spec res 0) as [R0|R0].
  - dr_if true. apply evt_done. left. split; [exact R0 | reflexivity].
  - dr_if false. step. step. step. step. dr_nm.
    apply evt_done. right. split; [exact R0|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HH].
Qed.

(* strndup's result cp (relay.c:113-114): non-NULL, s->held[s->nheld++] = cp, the slot P = s->held + 8 nheld. *)
Lemma dr_gkeep : forall x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA held nh P cp : Z) (j : word),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 nh)] -> P = held + 8 * nh ->
  rw_cells rsegs m P [C8 j] -> mem_inv rsegs m -> P + 8 <= SA + 40 \/ SA + 52 <= P ->
  0 <= cp < 2 ^ 64 -> 0 <= nh < 2 ^ 31 - 1 -> 0 <= held ->
  evt rsegs (fun ms =>
      (cp = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 cp) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137f4) fc None m (seg_rom rsegs)) \/
      (cp <> 0 /\ exists m' x11' x12' x13',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 cp) x11' x12' x13' x14 x15 x16 x17 x18 x19 x20
                    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137f4) fc None m' (seg_rom rsegs) /\
       munch [(SA + 48, SA + 52); (P, P + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 (nh + 1))] /\
       rw_cells rsegs m' P [C8 (Z_to_bv 64 cp)]))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 cp) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1393c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m SA held nh P cp j HH HP HC MI HD Hcp Hnh Hh.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(SA + 48, SA + 52); (P, P + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. destruct (Z.eqb_spec cp 0) as [C0|C0].
  - dr_if true. apply evt_done. left. split; [exact C0 | reflexivity].
  - dr_if false. step. rewrite (dr_sx32 nh) by lia. step. step. step. step. step. dr_nm.
    replace (held + nh * 2 ^ 3) with P by (rewrite HP; ring).
    step. step.
    apply evt_done. right. split; [exact C0|]. do 4 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HH | exact HC].
Qed.

(* After free (s->held[n]) (relay.c:118-119): s->held[n] = s->held[--s->nheld], the slot P = s->held + K (K = 8 n in
   s4), the last slot LP = s->held + 8 (nheld - 1) holding q. *)
Lemma dr_gdrop : forall x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA held nh K P LP q : Z) (j : word),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 nh)] ->
  P = held + K -> rw_cells rsegs m P [C8 j] -> LP = held + 8 * (nh - 1) -> rw_cells rsegs m LP [C8 (Z_to_bv 64 q)] ->
  mem_inv rsegs m -> P + 8 <= SA + 40 \/ SA + 52 <= P ->
  1 <= nh < 2 ^ 31 -> 0 <= held -> 0 <= K -> 0 <= q < 2 ^ 64 ->
  evt rsegs (fun ms => exists m' x10' x11' x12',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10' x11' x12' x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 K) x21
                   x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x137f4) fc None m' (seg_rom rsegs) /\
      munch [(SA + 48, SA + 52); (P, P + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 (nh - 1))] /\
      rw_cells rsegs m' P [C8 (Z_to_bv 64 q)])
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 K) x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1397c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m SA held nh K P LP q j HH HP HC HLP HQ MI HD Hnh Hh HK Hq.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HQ) as CB2. cbn [cells_size csize] in CB2.
  pose proof (munch_refl [(SA + 48, SA + 52); (P, P + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (dr_sx32 nh) by lia. step. step. step. dr_nm.
  replace (nh * 2 ^ 3 + held) with (LP + 8) by (rewrite HLP; ring).
  step. step. step. step. rewrite <- HP. step. step.
  apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HH | exact HC].
Qed.

(* reference_feed's loop body (fuzz_reply.c:223-236) on the byte c at p, s->partial = part, s->npartial = np and
   s->overlong = ovl at X + 168 (X = &g_s[j] - 128 in s3): a NUL goes to the line's end (0x13728); otherwise an
   overlong line drops c, a full partial (LINE_LIMIT bytes) turns overlong, else partial[np++] = c at Q = part + np. *)
Lemma dr_byte : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x25 x27 x28 x29
    x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X p part np ovl Q : Z) (c jb : byte),
  bytes_at rsegs m p [c] ->
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 ovl)] ->
  Q = part + np -> (bv_unsigned c <> 0 -> ovl = 0 -> np <> 6000 -> rw_cells rsegs m Q [C1 jb]) ->
  Q + 1 <= X + 168 \/ X + 188 <= Q -> mem_inv rsegs m ->
  0 <= ovl < 2 ^ 31 -> 0 <= np < 2 ^ 63 -> 0 <= part ->
  evt rsegs (fun ms =>
      (bv_unsigned c = 0 /\ exists x10',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' (Z_to_bv 64 ovl) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X)
                    (Z_to_bv 64 p) x21 x22 x23 (Z_to_bv 64 0x1000) x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13728) fc None m (seg_rom rsegs)) \/
      (bv_unsigned c <> 0 /\ ovl <> 0 /\ exists x10' x11',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' x11' x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X)
                    (Z_to_bv 64 p) x21 x22 x23 (Z_to_bv 64 0x1000) x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1375c) fc None m (seg_rom rsegs)) \/
      (bv_unsigned c <> 0 /\ ovl = 0 /\ np = 6000 /\ exists m' x10' x11' x12',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' x11' x12' x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X)
                    (Z_to_bv 64 p) x21 x22 x23 (Z_to_bv 64 0x1000) x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1375c) fc None m' (seg_rom rsegs) /\
       munch [(X + 184, X + 188)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 1)]) \/
      (bv_unsigned c <> 0 /\ ovl = 0 /\ np <> 6000 /\ exists m' x10' x11' x12' x13',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' x11' x12' x13' x14 x15 x16 x17 x18 (Z_to_bv 64 X)
                    (Z_to_bv 64 p) x21 x22 x23 (Z_to_bv 64 0x1000) x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1375c) fc None m' (seg_rom rsegs) /\
       munch [(X + 176, X + 184); (Q, Q + 1)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 (np + 1)); C4 (Z_to_bv 64 ovl)] /\
       rw_cells rsegs m' Q [C1 c]))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) (Z_to_bv 64 p) x21 x22 x23
             (Z_to_bv 64 0x1000) x25 (Z_to_bv 64 1) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13704) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x25 x27 x28 x29
    x30 x31 F fc m X p part np ovl Q c jb HB HO HQ HQC HD MI Hovl Hnp Hpart.
  pose proof (byte_range c) as RB.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB0. cbn [cells_size csize] in CB0.
  assert (HR : ov_read_bytes rsegs m (wa p) 1 = Some [c]).
  { pose proof (bytes_at_read rsegs m p [c] 0 1 HB ltac:(lia) ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. exact H. }
  step. unfold zxb. step. rewrite (dr_sx32 ovl) by lia.
  step.
  destruct (Z.eqb_spec (bv_unsigned c) 0) as [C0|C0].
  1:{ dr_if true. apply evt_done. left. split; [exact C0|]. eexists. reflexivity. }
  dr_if false. step. destruct (Z.eqb_spec ovl 0) as [O0|O0].
  2:{ dr_if true. apply evt_done. right. left. split; [exact C0|]. split; [exact O0|]. do 2 eexists. reflexivity. }
  dr_if false. step. step. step.
  destruct (Z.eqb_spec np 6000) as [N0|N0].
  - dr_if false.
    pose proof (munch_refl [(X + 184, X + 188)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    step. step.
    apply evt_done. right. right. left. split; [exact C0|]. split; [exact O0|]. split; [exact N0|].
    do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
  - dr_if true. specialize (HQC C0 O0 N0).
    pose proof (rw_cells_bound _ _ _ _ HQC) as CB1. cbn [cells_size csize] in CB1.
    pose proof (munch_refl [(X + 176, X + 184); (Q, Q + 1)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    step. step. step. step. rewrite <- HQ. step. rewrite le1_zxb. mem_after_store_opt.
    apply evt_done. right. right. right. split; [exact C0|]. split; [exact O0|]. split; [exact N0|].
    do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact HO | exact HQC].
Qed.

(* A line's end in reference_feed (fuzz_reply.c:225-226): not overlong, list_push (&s->expected, s->partial,
   s->npartial) with s2 = &s->expected; then the reset (0x1373c). *)
Lemma dr_lend : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X part np ovl : Z),
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np)] -> 0 <= ovl < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (ovl <> 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 ovl) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1373c) fc None m (seg_rom rsegs)) \/
      (ovl = 0 /\
       ms = MS (mkR (Z_to_bv 64 0x1373c) sp gp tp x5 x6 x7 x8 x9 x18 (Z_to_bv 64 part) (Z_to_bv 64 np) x13 x14 x15 x16
                    x17 x18 (Z_to_bv 64 X) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x14284) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 ovl) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13728) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m X part np ovl HO Hovl.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB0. cbn [cells_size csize] in CB0.
  step. destruct (Z.eqb_spec ovl 0) as [O0|O0].
  - dr_if false. step. step. step. step. apply evt_done. right. split; [exact O0 | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact O0 | reflexivity].
Qed.

(* s->npartial = 0, s->overlong = 0 (fuzz_reply.c:227-228). *)
Lemma dr_lreset : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X np ovl : Z),
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 ovl)] -> mem_inv rsegs m ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 x22 x23 x24
                   x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x1375c) fc None m' (seg_rom rsegs) /\
      munch [(X + 176, X + 188)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (X + 176) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1373c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m X np ovl HO MI.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(X + 176, X + 188)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
Qed.

(* reference_feed's next byte (fuzz_reply.c:221): p + 1 = e, the end s5, leaves the loop. *)
Lemma dr_bnext : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p e : Z),
  0 <= p -> p + 1 < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (p + 1 <> e /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (p + 1)) (Z_to_bv 64 e)
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13704) fc None m (seg_rom rsegs)) \/
      (p + 1 = e /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (p + 1)) (Z_to_bv 64 e)
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13764) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 p) (Z_to_bv 64 e) x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1375c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m p e Hp Hp1 He.
  step. step. destruct (Z.eqb_spec (p + 1) e) as [E|E].
  - dr_if false. apply evt_done. right. split; [exact E | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact E | reflexivity].
Qed.

(* s->pending_off += n (fuzz_reply.c:269); the head text (ta, tl) at the pending array pv consumed (fuzz_reply.c:270,
   :272): free (ta), the start of list_drop (&s->pending, 0). *)
Lemma dr_off : forall x1 sp gp tp x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n pv off ta tl : Z) (x10 x11 x20 : word),
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv)] -> rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 off)] ->
  rw_cells rsegs m pv [C8 (Z_to_bv 64 ta); C8 (Z_to_bv 64 tl)] -> mem_inv rsegs m ->
  pv + 16 <= X + 160 \/ X + 168 <= pv -> 0 <= off -> 0 <= n -> off + n < 2 ^ 64 -> 0 <= tl < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (off + n <> tl /\ exists m',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 n) (Z_to_bv 64 pv) (Z_to_bv 64 tl) x12 x13 x14 x15 x16 x17 x18
                    (Z_to_bv 64 X) (Z_to_bv 64 (off + n)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x137ac) fc None m' (seg_rom rsegs) /\
       munch [(X + 160, X + 168)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 (off + n))]) \/
      (off + n = tl /\ exists m',
       ms = MS (mkR (Z_to_bv 64 0x13784) sp gp tp x5 x6 x7 x8 (Z_to_bv 64 n) (Z_to_bv 64 ta) (Z_to_bv 64 tl) x12 x13 x14
                    x15 x16 x17 x18 (Z_to_bv 64 X) (Z_to_bv 64 (off + n)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x15664) fc None m' (seg_rom rsegs) /\
       munch [(X + 160, X + 168)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 (off + n))]))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13764) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 F fc m X n pv off ta tl x10 x11 x20 HP HO HR MI HD Hoff Hn Hon Htl.
  pose proof (rw_cells_bound _ _ _ _ HP) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HR) as CB2. cbn [cells_size csize] in CB2.
  pose proof (munch_refl [(X + 160, X + 168)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step.
  destruct (Z.eqb_spec (off + n) tl) as [E|E].
  - dr_if false. step. step.
    apply evt_done. right. split; [exact E|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
  - dr_if true.
    apply evt_done. left. split; [exact E|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
Qed.

Lemma dr_sw32 : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* list_drop (&s->pending, 0) after free (fuzz_reply.c:272): memmove (v, v + 1, (n - 1) * 16) of the pending
   array pv with n = pn entries. *)
Lemma dr_drop : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X pv pn : Z),
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv); C4 (Z_to_bv 64 pn)] -> 1 <= pn < 2 ^ 31 -> 0 <= pv ->
  pv + 16 < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x1379c) sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 pv) (Z_to_bv 64 (pv + 16))
                   (Z_to_bv 64 ((pn - 1) * 16)) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 x22 x23 x24 x25 x26 x27
                   x28 x29 x30 x31)
              F (Z_to_bv 64 0x1d200) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13784) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m X pv pn HP Hpn Hpv Hpv16.
  pose proof (rw_cells_bound _ _ _ _ HP) as CB0. cbn [cells_size csize] in CB0.
  step. step. rewrite (dr_sx32 pn) by lia. step. step. dr_nm. rewrite (dr_sw32 (pn + -1)) by lia.
  step. step. dr_nm.
  apply evt_done. reflexivity.
Qed.

(* The end of list_drop and s->pending_off = 0 (fuzz_reply.c:272-273): s->pending.n -= 1. *)
Lemma dr_dropn : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X pn off : Z) (x10 : word),
  rw_cells rsegs m (X + 152) [C4 (Z_to_bv 64 pn)] -> rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 off)] ->
  mem_inv rsegs m -> 1 <= pn < 2 ^ 31 ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (pn - 1)) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20
                   x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x137ac) fc None m' (seg_rom rsegs) /\
      munch [(X + 152, X + 156); (X + 160, X + 168)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (X + 152) [C4 (Z_to_bv 64 (pn - 1))] /\ rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 0)])
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 X) x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1379c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m X pn off x10 HN HO MI Hpn.
  pose proof (rw_cells_bound _ _ _ _ HN) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(X + 152, X + 156); (X + 160, X + 168)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (dr_sx32 pn) by lia. step. step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact HN | exact HO].
Qed.
