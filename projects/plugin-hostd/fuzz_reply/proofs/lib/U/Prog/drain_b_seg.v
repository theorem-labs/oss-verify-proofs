(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1247 of its 1329 lines of code are new or changed and 2359 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes Arr Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memcpy_c __errno_location_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* The instruction runs of the ubsan drain ([0x138c0, 0x13f08), 144-byte frame) between its calls (realloc,
   __errno_location and memcpy taken through their contracts inside a run, list_push, list_drop, memchr, memmove,
   send_line, strrchr, strncmp, strcmp, strlen, free, strndup), returns and branch targets. Each ubsan check branches
   to the trap at 0x13eb8 (unimp); every such branch is shown not taken from the premises. The register file at the
   for loop's top (0x13924): sp = S - 144, s0 = s, s6 = 384, s7 = 9 (EBADF), s9 = 0x318a0 (g_thread_up, the base of
   the harness table g_s at +128), s10 = 4 (EINTR); the frame at S - 144 holds the scratch words 0(sp), 8(sp),
   16(sp), 32(sp), LINE_LIMIT + 1 = 6001 at 24(sp) and the saved registers at 40(sp) .. 136(sp). *)

Definition DR_TU : Z := 0x318a0.

(* The saved registers at 40(sp) .. 136(sp). *)
Definition dr_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* A trap branch shown not taken. *)
Ltac dr_nt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [cbv iota
      | symmetry;
        first [ solve [unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
              | solve [vm_compute; reflexivity] ] ]
  end.

Ltac dr_land :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] =>
      replace (Z.land (bv_unsigned (Z_to_bv 64 x)) 7) with 0
        by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia;
            Z.div_mod_to_equations; lia)
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] =>
      replace (Z.land (bv_unsigned (Z_to_bv 64 x)) 3) with 0
        by (rewrite unsigned_lit by lia; change 3 with (Z.ones 2); rewrite Z.land_ones by lia;
            Z.div_mod_to_equations; lia)
  | |- context [Z.land ?x 7] =>
      lazymatch x with bv_unsigned (Z_to_bv 64 _) => fail | _ => idtac end;
      replace (Z.land x 7) with 0
        by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia)
  | |- context [Z.land ?x 3] =>
      lazymatch x with bv_unsigned (Z_to_bv 64 _) => fail | _ => idtac end;
      replace (Z.land x 3) with 0
        by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia)
  end.

Lemma dr_prologue : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA : Z) (junk : list byte),
  rw_cells rsegs m (bv_unsigned sp - 144) [CB 144 junk] -> 144 <= bv_unsigned sp ->
  0 <= SA < 2 ^ 64 -> SA mod 8 = 0 ->
  evt rsegs (fun ms => exists m' j0 j1 j2 j4,
      ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 144)) gp tp t0 t1 t2 (Z_to_bv 64 SA) s1 (Z_to_bv 64 6001)
                   (Z_to_bv 64 0x1000) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 384) (Z_to_bv 64 9) s8
                   (Z_to_bv 64 DR_TU) (Z_to_bv 64 4) s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x13924) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      length j0 = 8%nat /\ length j1 = 8%nat /\ length j2 = 8%nat /\ length j4 = 8%nat /\
      rw_cells rsegs m' (bv_unsigned sp - 144)
        ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 6001); CB 8 j4] ++
         dr_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x138c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SA junk FR LO HSA HSA8.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize] in FB.
  assert (LJ : length junk = 144%nat) by (destruct FR as [[[W _] _] _]; exact W).
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs _ _ [] 144%nat junk []
           [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) in * by lia.
  do 15 step.
  step. dr_land. step. dr_nt.
  do 8 step.
  apply evt_done. eexists. exists (firstn 8 junk), (firstn 8 (skipn 8 junk)), (firstn 8 (skipn 8 (skipn 8 junk))),
    (firstn 8 (skipn 8 (skipn 8 (skipn 8 (skipn 8 junk))))).
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [rewrite firstn_length; lia|]. split; [rewrite firstn_length, !skipn_length; lia|].
  split; [rewrite firstn_length, !skipn_length; lia|]. split; [rewrite firstn_length, !skipn_length; lia|].
  unfold dr_saved. cbn [app]. exact FR.
Qed.

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

(* snez / seqz on words of known value. *)
Ltac dr_cmp :=
  repeat match goal with
  | |- context [v_sltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      first
        [ replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 1)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 0)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  | |- context [v_sltiu (Z_to_bv 64 ?x) 1] =>
      first
        [ replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 1)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 0)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  end.

(* The for loop's top (relay.c:176): the growth test; with fewer than 4096 free bytes, the realloc call. *)
Lemma dr_top : forall x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA buf used cap : Z),
  rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used); C8 (Z_to_bv 64 cap)] ->
  0 <= used <= cap -> cap <= 2 ^ 20 ->
  evt rsegs (fun ms => exists x10',
      (4096 <= cap - used /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 cap) x10' x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13960) fc None m (seg_rom rsegs)) \/
      (cap - used < 4096 /\
       ms = MS (mkR (Z_to_bv 64 0x13954) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 (dr_grow cap)) (Z_to_bv 64 buf)
                    (Z_to_bv 64 (dr_grow cap)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                    x30 x31)
               F (Z_to_bv 64 0x178f8) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13924) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m SA buf used cap HC HU HCAP.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  step. step. step. step. step.
  destruct (Z.ltb_spec (cap - used) 4096) as [LT|GE].
  - dr_if false. step.
    destruct (Z.eqb_spec cap 0) as [C0|C0].
    + subst cap. dr_if false. step. step. step. step. step. dr_nm.
      apply evt_done. exists x10. right. split; [lia|reflexivity].
    + dr_if true. step. step. step. step. dr_nm.
      unfold dr_grow. rewrite (proj2 (Z.eqb_neq cap 0) C0).
      apply evt_done. exists x10. right. split; [lia|reflexivity].
  - dr_if true. apply evt_done. eexists. left. split; [lia|reflexivity].
Qed.

(* After realloc returned the new buffer res (relay.c:189-190): s->buf = res, s->cap = c. *)
Lemma dr_regrow : forall x1 sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA buf used cap res c : Z),
  rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used); C8 (Z_to_bv 64 cap)] ->
  0 < res < 2 ^ 64 ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 c) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13960) fc None m' (seg_rom rsegs) /\
      munch [(SA + 16, SA + 40)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (SA + 16) [C8 (Z_to_bv 64 res); C8 (Z_to_bv 64 used); C8 (Z_to_bv 64 c)])
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 c) (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18
             x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13954) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m SA buf used cap res c HC HR.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(SA + 16, SA + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. dr_if false.
  step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact HC.
Qed.

(* realloc returned NULL (relay.c:183-190): on to s->eof = 1 and the return (dr_eof at 0x13ec4). *)
Lemma dr_nomem : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms =>
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                   x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13ec4) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13954) fc None m (seg_rom rsegs)).
Proof. intros. step. dr_if true. apply evt_done. reflexivity. Qed.

Lemma dr_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* The harness's source_of (fuzz_reply.c:206-214), inlined: g_s[i] for i = j is the first open source with s's fd.
   The open flag (+132) is read before the fd (+128). *)
Lemma dr_scan : forall (k : nat) x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fd i j : Z),
  Z.of_nat k = j - i -> 0 <= i <= j -> j < 4 -> 0 <= fd < 2 ^ 31 ->
  (forall i', i <= i' < j -> exists f o, rw_cells rsegs m (DR_TU + 96 * i' + 128) [C4 (Z_to_bv 64 f); C4 (Z_to_bv 64 o)] /\
     (o = 0 \/ (0 <= f < 2 ^ 31 /\ f <> fd))) ->
  rw_cells rsegs m (DR_TU + 96 * j + 128) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1)] ->
  evt rsegs (fun ms => exists x14',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 (Z_to_bv 64 (96 * j)) (Z_to_bv 64 fd) x14' x15 x16 x17 x18 x19
                   (Z_to_bv 64 (DR_TU + 96 * j)) x21 (Z_to_bv 64 384) x23 x24 (Z_to_bv 64 DR_TU) x26 x27 x28 x29 x30
                   x31)
              F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 (Z_to_bv 64 (96 * i)) (Z_to_bv 64 fd) x14 x15 x16 x17 x18 x19 x20 x21
             (Z_to_bv 64 384) x23 x24 (Z_to_bv 64 DR_TU) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1398c) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26
    x27 x28 x29 x30 x31 F fc m fd i j Hk Hi Hj Hfd HO HJ; unfold DR_TU in *.
  - assert (i = j) by lia. subst i.
    pose proof (rw_cells_bound _ _ _ _ HJ) as CB0. cbn [cells_size csize] in CB0.
    step. dr_nm. step. rewrite (dr_sx32 1) by lia. step. dr_if false.
    step. rewrite (dr_sx32 fd) by lia. step. dr_if true.
    apply evt_done. eexists. reflexivity.
  - destruct (HO i ltac:(lia)) as (f & o & HC & Ho).
    pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
    step. dr_nm. step.
    assert (TAIL : forall a4, evt rsegs (fun ms => exists x14',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 (Z_to_bv 64 (96 * j)) (Z_to_bv 64 fd) x14' x15 x16 x17 x18 x19
                   (Z_to_bv 64 (202912 + 96 * j)) x21 (Z_to_bv 64 384) x23 x24 (Z_to_bv 64 202912) x26 x27 x28 x29 x30
                   x31)
              F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 (Z_to_bv 64 (96 * i)) (Z_to_bv 64 fd) a4 x15 x16 x17 x18 x19
             (Z_to_bv 64 (202912 + 96 * i)) x21 (Z_to_bv 64 384) x23 x24 (Z_to_bv 64 202912) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139a0) fc None m (seg_rom rsegs))).
    { intros a4. step. dr_nm. step. dr_if true.
      replace (96 * i + 96) with (96 * (i + 1)) by lia.
      exact (IH x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 a4 x15 x16 x17 x18 x19 _ x21 x23 x24 x26 x27 x28 x29 x30 x31
               F fc m fd (i + 1) j ltac:(lia) ltac:(lia) Hj Hfd (fun i' Hi' => HO i' ltac:(lia)) HJ). }
    destruct Ho as [-> | (Hf & Hne)].
    + rewrite (dr_sx32 0) by lia. step. dr_if true. apply TAIL.
    + step. if_cases E.
      * apply TAIL.
      * step. rewrite (dr_sx32 f) by lia. step. dr_if false. apply TAIL.
Qed.

(* recv (s->fd, s->buf + s->used, s->cap - s->used, ...) (relay.c:193): the checked pointer s->buf + s->used, then
   the scan for s's harness source g_s[j]. *)
Lemma dr_find : forall x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA fd buf used cap j : Z),
  rw_cells rsegs m SA [C4 (Z_to_bv 64 fd)] -> rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used)] ->
  0 <= j < 4 -> 0 <= fd < 2 ^ 31 -> 0 < buf -> 0 <= used -> buf + used < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  (forall i', 0 <= i' < j -> exists f o, rw_cells rsegs m (DR_TU + 96 * i' + 128) [C4 (Z_to_bv 64 f); C4 (Z_to_bv 64 o)] /\
     (o = 0 \/ (0 <= f < 2 ^ 31 /\ f <> fd))) ->
  rw_cells rsegs m (DR_TU + 96 * j + 128) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1)] ->
  evt rsegs (fun ms => exists x14',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 cap) (Z_to_bv 64 (buf + used))
                   (Z_to_bv 64 (cap - used)) (Z_to_bv 64 (96 * j)) (Z_to_bv 64 fd) x14' x15 x16 x17 x18 x19
                   (Z_to_bv 64 (DR_TU + 96 * j)) x21 (Z_to_bv 64 384) x23 x24 (Z_to_bv 64 DR_TU) x26 x27 x28 x29 x30
                   x31)
              F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 cap) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             (Z_to_bv 64 384) x23 x24 (Z_to_bv 64 DR_TU) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13960) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27
    x28 x29 x30 x31 F fc m SA fd buf used cap j HF HB Hj Hfd Hb Hu Hbu Hcap HO HJ.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HB) as CB1. cbn [cells_size csize] in CB1.
  step. step. step. step. dr_nt.
  step. dr_cmp. step. dr_cmp. step. step. dr_nt.
  step. step. rewrite (dr_sx32 fd) by lia. step. dr_nm.
  exact (dr_scan (Z.to_nat j) x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 cap) (Z_to_bv 64 (buf + used))
           (Z_to_bv 64 (cap - used)) x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 F fc m fd 0 j
           ltac:(lia) ltac:(lia) ltac:(lia) Hfd HO HJ).
Qed.

(* drain's epilogue (0x13ecc): the saved registers back, sp = S, return to the saved ra. *)
Lemma dr_epi : forall ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (SP : Z),
  rw_cells rsegs m (SP + 40) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  0 <= SP -> SP + 144 < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ms = MS (mkR ra0 (Z_to_bv 64 (SP + 144)) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
             x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13ecc) fc None m (seg_rom rsegs)).
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
  rw_cells rsegs m (SP + 40) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 eof); C4 (Z_to_bv 64 sk)] ->
  0 <= SP -> SP + 144 < 2 ^ 64 -> SA + 12 <= SP + 40 \/ SP + 144 <= SA ->
  evt rsegs (fun ms => exists m' x10',
      ms = MS (mkR ra0 (Z_to_bv 64 (SP + 144)) gp tp x5 x6 x7 s0 s1 x10' x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      munch [(SA + 4, SA + 8)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 sk)] /\
      rw_cells rsegs m' (SP + 40) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13ec4) fc None m (seg_rom rsegs)).
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

(* fuzz_recv with h.eintr = 1 (fuzz_reply.c:250-254): h.eintr = 0, errno = EINTR (the checked errno pointer,
   ERR = tp - 164 non-NULL and 4-aligned), -1; drain continues (relay.c:194). X = &g_s[j] - 128 in s4. *)
Lemma dr_eintr : __errno_location_contract ->
  forall x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X fd op cl : Z) (ev : word),
  rw_cells rsegs m (X + 128) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 cl); C4 (Z_to_bv 64 1)] ->
  rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
  0 <= X -> 0 < bv_unsigned tp + -164 -> (bv_unsigned tp + -164) mod 4 = 0 ->
  X + 144 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -160 <= X + 128 ->
  evt rsegs (fun ms => exists m' x1' x10' x11' x12',
      ms = MS (mkR x1' sp gp tp x5 x6 x7 s0 x9 x10' x11' x12' x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) x21 x22
                   x23 x24 x25 (Z_to_bv 64 4) x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13924) fc None m' (seg_rom rsegs) /\
      munch [(X + 140, X + 144); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (X + 128) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 cl); C4 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 4)])
    (MS (mkR x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) x21 x22 x23 x24 x25
             (Z_to_bv 64 4) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs)).
Proof.
  intros EL x1 sp gp tp x5 x6 x7 s0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x27
    x28 x29 x30 x31 F fc m X fd op cl ev HS HE HX HT HT4 HD.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HE) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(X + 140, X + 144); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (dr_sx32 1) by lia. step. dr_if false.
  step. step.
  eapply evt_cut; [apply EL|]. intros ms' ->. unfold ERRNO_TP_OFF.
  rewrite (dr_ret_even 0x139d0) by lia.
  step. dr_nt. step. dr_land. step. dr_nt.
  step. step. step. dr_nt. step. dr_nt.
  step. rewrite (dr_sx32 4) by lia. step. dr_if true.
  apply evt_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  split; assumption.
Qed.

(* fuzz_recv with no pending text of a closed source (fuzz_reply.c:256-258): 0, so s->eof = 1 and drain returns. *)
Lemma dr_closed : forall ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (SP SA X fd eof sk sfd op pv pc : Z),
  rw_cells rsegs m (SP + 40) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 eof); C4 (Z_to_bv 64 sk)] ->
  rw_cells rsegs m (X + 128) [C4 (Z_to_bv 64 sfd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 pc)] ->
  0 <= SP -> SP + 144 < 2 ^ 64 -> SA + 12 <= SP + 40 \/ SP + 144 <= SA -> 0 <= X ->
  evt rsegs (fun ms => exists m' x10' x12',
      ms = MS (mkR ra0 (Z_to_bv 64 (SP + 144)) gp tp x5 x6 x7 s0 s1 x10' x11 x12' x13 x14 x15 x16 x17 s2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      munch [(SA + 4, SA + 8)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' SA [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 sk)])
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X)
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m SP SA X fd eof sk sfd op pv pc HF HE HS HP H0 H1 HD HX.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HP) as CB1. cbn [cells_size csize] in CB1.
  step. rewrite (dr_sx32 0) by lia. step. dr_if true.
  step. rewrite (dr_sx32 0) by lia. step. dr_if true.
  step. rewrite (dr_sx32 1) by lia. step. dr_if true.
  eapply evt_mono; [eapply (dr_eof ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); eassumption|].
  intros ms (m' & x10' & -> & MU & WM & HE' & _). do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact HE'].
Qed.

(* fuzz_recv with no pending text of an open source (fuzz_reply.c:259-260): errno = EAGAIN (the checked errno
   pointer), -1; drain returns (the errno test against EINTR in s10 = 4, then against EAGAIN). *)
Lemma dr_again : __errno_location_contract ->
  forall ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (SP SA X sfd op pv pc : Z) (ev : word),
  rw_cells rsegs m (SP + 40) (dr_saved ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells rsegs m (X + 128) [C4 (Z_to_bv 64 sfd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 pc)] ->
  rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
  0 <= SP -> SP + 144 < 2 ^ 64 -> 0 <= X -> 0 < bv_unsigned tp + -164 -> (bv_unsigned tp + -164) mod 4 = 0 ->
  bv_unsigned tp + -160 <= SP + 40 \/ SP + 144 <= bv_unsigned tp + -164 ->
  evt rsegs (fun ms => exists m' x10' x11' x12',
      ms = MS (mkR ra0 (Z_to_bv 64 (SP + 144)) gp tp x5 x6 x7 s0 s1 x10' x11' x12' x13 x14 x15 x16 x17 s2 s3 s4 s5 s6
                   s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 11)])
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X)
             x21 x22 x23 x24 x25 (Z_to_bv 64 4) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs)).
Proof.
  intros EL ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 F fc m SP SA X sfd op pv pc ev HF HS HP HE H0 H1 HX HT HT4 HD.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
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
  rewrite (dr_ret_even 0x13e90) by lia.
  step. dr_nt. step. dr_land. step. dr_nt.
  step. step. step.
  step. step. dr_nt. step. dr_nt.
  step. rewrite (dr_sx32 11) by lia. step. dr_if false.
  step. step. step. dr_if true.
  eapply evt_mono; [apply (dr_epi ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); [exact HF | lia | lia]|].
  intros ms ->. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | assumption].
Qed.

(* fuzz_recv's copy (fuzz_reply.c:262-264): n = min (rest of the head text, len) bytes into s->buf + s->used (the
   checked pending array pv, non-NULL and 8-aligned, and the checked source pointer ta + off), then reference_feed's
   loop over them set up (fuzz_reply.c:265, :219-221): s5 = s7 = p = ta + off, s1 = n, s2 = &h->expected,
   32(sp) = &h->pending. *)
Lemma dr_data : memcpy_contract ->
  forall x1 gp tp x5 x6 x7 s0 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (SP X sfd op cl pv pn off ta tl dst len : Z) (w : word) (src dj : list byte),
  rw_cells rsegs m (X + 128) [C4 (Z_to_bv 64 sfd); C4 (Z_to_bv 64 op); C4 (Z_to_bv 64 cl); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv); C4 (Z_to_bv 64 pn)] ->
  rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 off)] ->
  rw_cells rsegs m pv [C8 (Z_to_bv 64 ta); C8 (Z_to_bv 64 tl)] ->
  rw_cells rsegs m (SP + 32) [C8 w] ->
  bytes_at rsegs m (ta + off) src -> Z.of_nat (length src) = Z.min (tl - off) len ->
  rw_cells rsegs m dst [CB (Z.to_nat (Z.min (tl - off) len)) dj] ->
  mem_inv rsegs m ->
  0 <= SP -> 0 <= X -> X + 192 < 2 ^ 64 -> 1 <= pn < 2 ^ 31 -> 0 <= off < tl -> tl < 2 ^ 62 -> 0 < len < 2 ^ 62 ->
  0 < ta -> ta + tl < 2 ^ 64 -> 0 < pv -> pv mod 8 = 0 -> 0 <= dst -> dst + len < 2 ^ 64 ->
  (dst + len <= ta \/ ta + tl <= dst) ->
  (dst + len <= X + 128 \/ X + 192 <= dst) ->
  (dst + len <= pv \/ pv + 16 <= dst) ->
  (dst + len <= SP + 32 \/ SP + 40 <= dst) ->
  (SP + 40 <= ta \/ ta + tl <= SP + 32) ->
  evt rsegs (fun ms => exists m' x1' x10' x11' x12' x13' x14' x15' x16' x17' x5' x6' x7' x28' x29' x30' x31',
      ms = MS (mkR x1' (Z_to_bv 64 SP) gp tp x5' x6' x7' s0 (Z_to_bv 64 (Z.min (tl - off) len)) x10' x11' x12' x13'
                   x14' x15' x16' x17' (Z_to_bv 64 (X + 192)) (Z_to_bv 64 (Z.min (tl - off) len)) (Z_to_bv 64 X)
                   (Z_to_bv 64 (ta + off)) x22 (Z_to_bv 64 (ta + off)) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta)
                   (Z_to_bv 64 (ta + off)) x28' x29' x30' x31')
              F (Z_to_bv 64 0x13a94) fc None m' (seg_rom rsegs) /\
      munch [(dst, dst + Z.min (tl - off) len); (SP + 32, SP + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' dst [CB (Z.to_nat (Z.min (tl - off) len)) src] /\ bytes_at rsegs m' (ta + off) src /\
      rw_cells rsegs m' (SP + 32) [C8 (Z_to_bv 64 (X + 144))])
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 x9 (Z_to_bv 64 dst) (Z_to_bv 64 len) x12 x13 x14 x15 x16 x17 x18
             x19 (Z_to_bv 64 X) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs)).
Proof.
  intros MC x1 gp tp x5 x6 x7 s0 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m SP X sfd op cl pv pn off ta tl dst len w src dj
    HS HP HO HR HW HSRC HLS HD MI HSP HX1 HX2 Hpn Hoff Htl Hlen Hta Htt Hpv Hpv8 Hdst Hdst2 D1 D2 D3 D4 D5.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HP) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB2. cbn [cells_size csize] in CB2.
  pose proof (rw_cells_bound _ _ _ _ HR) as CB3. cbn [cells_size csize] in CB3.
  pose proof (rw_cells_bound _ _ _ _ HW) as CB4. cbn [cells_size csize] in CB4.
  set (n := Z.min (tl - off) len) in *.
  assert (Hn : 0 < n <= len /\ n <= tl - off) by (subst n; lia).
  step. rewrite (dr_sx32 0) by lia. step. dr_if true.
  step. rewrite (dr_sx32 pn) by lia. step. dr_if false.
  step. step. step. dr_nt. step. dr_land. step. dr_nt.
  step. step. step. dr_nm.
  step.
  match goal with |- evt _ ?Q _ => assert (K : forall v, v = n -> evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 (Z_to_bv 64 (X + 144)) (Z_to_bv 64 dst) (Z_to_bv 64 len)
             (Z_to_bv 64 pv) (Z_to_bv 64 off) (Z_to_bv 64 tl) x15 x16 x17 x18 (Z_to_bv 64 v) (Z_to_bv 64 X) x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13a28) fc None m (seg_rom rsegs))) end.
  { intros v ->.
    assert (UD : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; lia).
    assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
    assert (UA : bv_unsigned (Z_to_bv 64 (ta + off)) = ta + off) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(dst, dst + n); (SP + 32, SP + 40)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    step. step. try rewrite (Z.add_comm off ta).
    step. dr_nt.
    step. dr_cmp. step. dr_cmp. step. step. dr_nt.
    step. step.
    call (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src dj).
    1: rewrite UA; exact HSRC.
    1: rewrite UN; lia.
    1: rewrite UD, UN; exact HD.
    1: rewrite UD, UN, UA; lia.
    1: exact MI.
    rewrite ?UD, ?UN, ?UA in *.
    step. step. dr_nt. step. dr_land. step. dr_nt.
    step. step. step. try rewrite (Z.add_comm off ta).
    step. dr_nt.
    step. dr_cmp. step. dr_cmp. step. step. dr_nt.
    step. dr_if false.
    step. step. step. step. step.
    apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; assumption. }
  destruct (Z.ltb_spec (tl - off) len) as [LT|GE].
  - dr_if true. apply K. subst n. lia.
  - dr_if false. step. apply K. subst n. lia.
Qed.

(* reference_feed's loop body (fuzz_reply.c:223-236) on the byte c at p (s5 = s7 = p, the checked pointer: p0 <= p
   in s11, p non-NULL with s8 = 1, ta non-NULL in s10), s->partial = part, s->npartial = np and s->overlong = ovl at
   X + 168 (X = &g_s[j] - 128 in s4): a NUL goes to the line's end (0x13ad4); otherwise an overlong line drops c, a
   full partial (LINE_LIMIT bytes) turns overlong, else partial[np++] = c at the checked Q = part + np. *)
Lemma dr_byte : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x25 x28 x29
    x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X p p0 ta part np ovl Q : Z) (c jb : byte),
  bytes_at rsegs m p [c] ->
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 ovl)] ->
  Q = part + np -> (bv_unsigned c <> 0 -> ovl = 0 -> np <> 6000 -> rw_cells rsegs m Q [C1 jb]) ->
  Q + 1 <= X + 168 \/ X + 188 <= Q -> mem_inv rsegs m ->
  0 <= ovl < 2 ^ 31 -> 0 <= np < 2 ^ 63 -> 0 < part -> part + np < 2 ^ 64 ->
  0 <= p0 <= p -> 0 < p < 2 ^ 64 -> 0 < ta < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (bv_unsigned c = 0 /\ exists x10',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' (Z_to_bv 64 ovl) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X)
                    (Z_to_bv 64 p) x22 (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta) (Z_to_bv 64 p0) x28 x29 x30
                    x31)
               F (Z_to_bv 64 0x13ad4) fc None m (seg_rom rsegs)) \/
      (bv_unsigned c <> 0 /\ ovl <> 0 /\ exists x10' x11',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' x11' x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X)
                    (Z_to_bv 64 p) x22 (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta) (Z_to_bv 64 p0) x28 x29 x30
                    x31)
               F (Z_to_bv 64 0x13b20) fc None m (seg_rom rsegs)) \/
      (bv_unsigned c <> 0 /\ ovl = 0 /\ np = 6000 /\ exists m' x10' x11' x12',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' x11' x12' x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X)
                    (Z_to_bv 64 p) x22 (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta) (Z_to_bv 64 p0) x28 x29 x30
                    x31)
               F (Z_to_bv 64 0x13b20) fc None m' (seg_rom rsegs) /\
       munch [(X + 184, X + 188)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 1)]) \/
      (bv_unsigned c <> 0 /\ ovl = 0 /\ np <> 6000 /\ exists m' x10' x11' x12' x13' x14',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10' x11' x12' x13' x14' x15 x16 x17 x18 x19 (Z_to_bv 64 X)
                    (Z_to_bv 64 p) x22 (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta) (Z_to_bv 64 p0) x28 x29 x30
                    x31)
               F (Z_to_bv 64 0x13b20) fc None m' (seg_rom rsegs) /\
       munch [(X + 176, X + 184); (Q, Q + 1)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 (np + 1)); C4 (Z_to_bv 64 ovl)] /\
       rw_cells rsegs m' Q [C1 c]))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) (Z_to_bv 64 p) x22
             (Z_to_bv 64 p) (Z_to_bv 64 1) x25 (Z_to_bv 64 ta) (Z_to_bv 64 p0) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13a94) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x25 x28 x29
    x30 x31 F fc m X p p0 ta part np ovl Q c jb HB HO HQ HQC HD MI Hovl Hnp Hpart Hpn Hp0 Hp Hta.
  pose proof (byte_range c) as RB.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB0. cbn [cells_size csize] in CB0.
  assert (HR : ov_read_bytes rsegs m (wa p) 1 = Some [c]).
  { pose proof (bytes_at_read rsegs m p [c] 0 1 HB ltac:(lia) ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. exact H. }
  step. dr_nt. step. dr_cmp. step. step. dr_nt. step. dr_nt.
  step. unfold zxb. step. rewrite (dr_sx32 ovl) by lia.
  step.
  destruct (Z.eqb_spec (bv_unsigned c) 0) as [C0|C0].
  1:{ dr_if true. apply evt_done. left. split; [exact C0|]. eexists. reflexivity. }
  dr_if false. step. destruct (Z.eqb_spec ovl 0) as [O0|O0].
  2:{ dr_if true. apply evt_done. right. left. split; [exact C0|]. split; [exact O0|]. do 2 eexists. reflexivity. }
  dr_if false. step. step. step. step.
  destruct (Z.eqb_spec np 6000) as [N0|N0].
  - dr_if false.
    pose proof (munch_refl [(X + 184, X + 188)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    step. step. step.
    apply evt_done. right. right. left. split; [exact C0|]. split; [exact O0|]. split; [exact N0|].
    do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
  - dr_if true. specialize (HQC C0 O0 N0).
    pose proof (rw_cells_bound _ _ _ _ HQC) as CB1. cbn [cells_size csize] in CB1.
    pose proof (munch_refl [(X + 176, X + 184); (Q, Q + 1)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    step. step. step. rewrite <- HQ. step.
    step. dr_nt. step. dr_cmp. step. dr_cmp. step. step. dr_nt. step. dr_nt.
    step. rewrite le1_zxb. mem_after_store_opt.
    apply evt_done. right. right. right. split; [exact C0|]. split; [exact O0|]. split; [exact N0|].
    do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact HO | exact HQC].
Qed.

(* A line's end in reference_feed (fuzz_reply.c:225-226): not overlong, list_push (&s->expected, s->partial,
   s->npartial) with s2 = &s->expected; then the reset (0x13ae8). *)
Lemma dr_lend : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X part np ovl : Z),
  rw_cells rsegs m (X + 168) [C8 (Z_to_bv 64 part); C8 (Z_to_bv 64 np)] -> 0 <= ovl < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (ovl <> 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 ovl) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) x21
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13ae8) fc None m (seg_rom rsegs)) \/
      (ovl = 0 /\
       ms = MS (mkR (Z_to_bv 64 0x13ae8) sp gp tp x5 x6 x7 x8 x9 x18 (Z_to_bv 64 part) (Z_to_bv 64 np) x13 x14 x15 x16
                    x17 x18 x19 (Z_to_bv 64 X) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1484c) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 ovl) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13ad4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m X part np ovl HO Hovl.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB0. cbn [cells_size csize] in CB0.
  step. destruct (Z.eqb_spec ovl 0) as [O0|O0].
  - dr_if false. step. step. step. step. apply evt_done. right. split; [exact O0 | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact O0 | reflexivity].
Qed.

(* s->npartial = 0, s->overlong = 0 (fuzz_reply.c:227-228). *)
Lemma dr_lreset : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X np ovl : Z),
  rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 np); C4 (Z_to_bv 64 ovl)] -> mem_inv rsegs m ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) x21 x22 x23 x24
                   x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13b20) fc None m' (seg_rom rsegs) /\
      munch [(X + 176, X + 188)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (X + 176) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13ae8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m X np ovl HO MI.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(X + 176, X + 188)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
Qed.

(* reference_feed's next byte (fuzz_reply.c:221): s1 = k bytes left before it, s5 = s7 = p; k - 1 = 0 leaves the
   loop. *)
Lemma dr_bnext : forall x1 sp gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k p : Z),
  1 <= k < 2 ^ 64 -> 0 <= p -> p + 1 < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (k - 1 <> 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 (k - 1)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                    (Z_to_bv 64 (p + 1)) x22 (Z_to_bv 64 (p + 1)) x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13a94) fc None m (seg_rom rsegs)) \/
      (k - 1 = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 (k - 1)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                    (Z_to_bv 64 (p + 1)) x22 (Z_to_bv 64 (p + 1)) x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13b30) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 k) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 p) x22
             (Z_to_bv 64 p) x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13b20) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m k p Hk Hp Hp1.
  step. step. step. step. try replace (k + -1) with (k - 1) by lia.
  destruct (Z.eqb_spec (k - 1) 0) as [E|E].
  - dr_if false. apply evt_done. right. split; [exact E | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact E | reflexivity].
Qed.

(* s->pending_off += n (fuzz_reply.c:269) with s3 = n, s1 = &h->pending reloaded from 32(sp), the checked pending
   array pv (8-aligned, non-NULL); the head text consumed (off + n = tl at pv + 8, fuzz_reply.c:270, :272):
   list_drop (&h->pending, 0); s7, s10, s11 back to 9, 4, -1. *)
Lemma dr_off : forall x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP X n pv off tl : Z),
  rw_cells rsegs m (SP + 32) [C8 (Z_to_bv 64 (X + 144))] ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 pv)] -> rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 off)] ->
  rw_cells rsegs m (pv + 8) [C8 (Z_to_bv 64 tl)] -> mem_inv rsegs m ->
  pv + 16 <= X + 160 \/ X + 168 <= pv + 8 -> 0 <= SP -> 0 <= X -> 0 < pv -> pv mod 8 = 0 ->
  0 <= off -> 0 <= n -> off + n < 2 ^ 64 -> 0 <= tl < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (off + n <> tl /\ exists m' x12',
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 (Z_to_bv 64 (X + 144)) (Z_to_bv 64 tl) (Z_to_bv 64 (off + n))
                    x12' x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) (Z_to_bv 64 X) x21 x22 (Z_to_bv 64 9) x24 x25
                    (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x13b74) fc None m' (seg_rom rsegs) /\
       munch [(X + 160, X + 168)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 (off + n))]) \/
      (off + n = tl /\ exists m' x12',
       ms = MS (mkR (Z_to_bv 64 0x13b70) (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 (Z_to_bv 64 (X + 144))
                    (Z_to_bv 64 (X + 144)) (Z_to_bv 64 0) x12' x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) (Z_to_bv 64 X)
                    x21 x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x14d58) fc None m' (seg_rom rsegs) /\
       munch [(X + 160, X + 168)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 (off + n))]))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) (Z_to_bv 64 X)
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13b30) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m SP X n pv off tl HW HP HO HR MI HD HSP HX Hpv Hpv8 Hoff Hn Hon Htl.
  pose proof (rw_cells_bound _ _ _ _ HW) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HP) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB2. cbn [cells_size csize] in CB2.
  pose proof (rw_cells_bound _ _ _ _ HR) as CB3. cbn [cells_size csize] in CB3.
  pose proof (munch_refl [(X + 160, X + 168)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step. dr_land. step. step. step.
  step. dr_nt. step. dr_nt.
  step. step.
  destruct (Z.eqb_spec (off + n) tl) as [E|E].
  - dr_if false. step. step. step.
    apply evt_done. right. split; [exact E|]. do 2 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
  - dr_if true.
    apply evt_done. left. split; [exact E|]. do 2 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
Qed.

(* After list_drop (&h->pending, 0): s->pending_off = 0 (fuzz_reply.c:273). *)
Lemma dr_dropn : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X off : Z),
  rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 off)] -> mem_inv rsegs m ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) x21 x22 x23 x24
                   x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13b74) fc None m' (seg_rom rsegs) /\
      munch [(X + 160, X + 168)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 0)])
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 X) x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13b70) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m X off HO MI.
  pose proof (rw_cells_bound _ _ _ _ HO) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(X + 160, X + 168)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HO].
Qed.

(* The line scan and gesture_seen (relay.c:196-222, :92-121) inlined in the ubsan build: one memchr call site
   (0x13ba8) for the first and the next lines, the next line at 0x13bcc (start = nul + 1 with the checked nul != -1,
   s11 = -1), the held search over 8-aligned non-NULL slots. s7 = 9, s10 = 4, s11 = -1 are restored before each
   return to 0x13bcc. *)

Lemma dr_sgn : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus. rewrite unsigned_lit by lia.
  change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

Lemma dr_sw32 : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* not x (xori x, -1) and the mask -1 on 64-bit values. *)
Lemma dr_lxor_ones : forall z c, c = Z.ones 64 -> 0 <= z < 2 ^ 64 -> Z.lxor z c = 2 ^ 64 - 1 - z.
Proof.
  intros z c -> Hz.
  assert (E : Z.lxor z (Z.ones 64) = Z.land (Z.lnot z) (Z.ones 64)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases n 64) as [L|L].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit z n); reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite Bool.xorb_false_r, Bool.andb_false_r.
      rewrite <- (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
  rewrite E, Z.land_ones, Z.lnot_eq_pred_opp by lia. unfold Z.pred. Z.div_mod_to_equations. lia.
Qed.

Lemma dr_land_ones : forall a z, a = Z.ones 64 -> 0 <= z < 2 ^ 64 -> Z.land a z = z.
Proof. intros a z -> Hz. rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. exact Hz. Qed.

Ltac dr_lx := repeat match goal with
  | |- context [Z.lxor ?z ?c] => is_Zlit c; rewrite (dr_lxor_ones z c) by first [ reflexivity | dlia ]
  end.
Ltac dr_m1 := repeat match goal with
  | |- context [Z.land ?a ?z] => is_Zlit a; rewrite (dr_land_ones a z) by first [ reflexivity | dlia ]
  end.
Ltac dr_sg := repeat match goal with
  | |- context [bv_signed (Z_to_bv 64 ?z)] => rewrite (dr_sgn z) by dlia
  end.
(* Take the branch b (true: taken) of a signed, unsigned or literal compare. *)
Ltac dr_ifs b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b;
      [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux; fold_closed_in_goal; dr_sg;
                  dr_nm; dr_cr]
  end.
(* sgtz / slti on words of known value. *)
Ltac dr_cmps :=
  repeat match goal with
  | |- context [v_slt (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      first
        [ replace (v_slt (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 1)
            by (unfold v_slt, c_lts, bv_lts; fold_lit_ux; dr_sg; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity)
        | replace (v_slt (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 0)
            by (unfold v_slt, c_lts, bv_lts; fold_lit_ux; dr_sg; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) ]
  | |- context [v_slti (Z_to_bv 64 ?x) ?k] =>
      first
        [ replace (v_slti (Z_to_bv 64 x) k) with (Z_to_bv 64 0)
            by (unfold v_slti, zsig; fold_lit_ux; dr_sg; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity)
        | replace (v_slti (Z_to_bv 64 x) k) with (Z_to_bv 64 1)
            by (unfold v_slti, zsig; fold_lit_ux; dr_sg; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity) ]
  end.

(* s->used += n (relay.c:202) for the n bytes fuzz_recv copied, with s3 = n; n = 0 ends the source (relay.c:198-201)
   at 0x13ec4; otherwise the line scan from start = s->buf (0x13b8c). *)
Lemma dr_add : forall x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA buf used n : Z),
  rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 used)] -> mem_inv rsegs m ->
  0 <= n < 2 ^ 63 -> 0 <= used -> used + n < 2 ^ 64 -> 0 <= buf < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (n = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) x20 x21
                    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13ec4) fc None m (seg_rom rsegs)) \/
      (0 < n /\ exists m',
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 (used + n)) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 buf) (Z_to_bv 64 n) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13b8c) fc None m' (seg_rom rsegs) /\
       munch [(SA + 24, SA + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (used + n))]))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13b74) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F
    fc m SA buf used n HC MI HN HU HUN HB.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(SA + 24, SA + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. dr_ifs false. step.
  destruct (Z.eqb_spec n 0) as [N0|N0].
  - dr_if true. apply evt_done. left. split; [exact N0 | reflexivity].
  - dr_if false. step. step. step. step.
    apply evt_done. right. split; [lia|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HC].
Qed.

(* memchr (start, 0, s->used - (start - s->buf)) (relay.c:204) with s2 = start. *)
Lemma dr_line : forall x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA buf u st : Z),
  rw_cells rsegs m (SA + 16) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 u)] ->
  0 <= buf <= st -> st <= buf + u -> buf + u < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13bac) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 st) (Z_to_bv 64 0)
                   (Z_to_bv 64 (u - (st - buf))) x13 x14 x15 x16 x17 (Z_to_bv 64 st) (Z_to_bv 64 buf)
                   (Z_to_bv 64 (u - (st - buf))) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x1d5e8) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 st) x19 x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13b8c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F
    fc m SA buf u st HC Hb Hs Hu.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  step. step. step. dr_nm. step. dr_nm. step. step. step. step. dr_nm.
  replace (buf - st + u) with (u - (st - buf)) by lia.
  apply evt_done. reflexivity.
Qed.

(* memchr's result r (relay.c:204), the one call site for the first and the next lines: no NUL leaves the rest
   (0x13e54); a NUL at r ends the line [st, r) (relay.c:207-213): with s->skip set or more than LINE_LIMIT bytes,
   s->skip = 0 and the next line (0x13bcc); otherwise send_line (st, r - st + 1). 24(sp) holds LINE_LIMIT + 1. *)
Lemma dr_hit : forall x1 gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA sk st r : Z),
  rw_cells rsegs m (SA + 8) [C4 (Z_to_bv 64 sk)] -> rw_cells rsegs m (SP + 24) [C8 (Z_to_bv 64 6001)] ->
  mem_inv rsegs m -> 0 <= sk < 2 ^ 31 -> 0 <= st -> 0 <= r < 2 ^ 64 -> (r <> 0 -> st <= r) ->
  evt rsegs (fun ms =>
      (r = 0 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 st) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13e54) fc None m (seg_rom rsegs)) \/
      (r <> 0 /\ (sk <> 0 \/ 6001 <= r - st) /\ exists m' e10 e11,
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 r) e10 e11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 st) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13bcc) fc None m' (seg_rom rsegs) /\
       munch [(SA + 8, SA + 12)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 8) [C4 (Z_to_bv 64 0)]) \/
      (r <> 0 /\ sk = 0 /\ r - st < 6001 /\
       ms = MS (mkR (Z_to_bv 64 0x13be4) (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) (Z_to_bv 64 r) (Z_to_bv 64 st)
                    (Z_to_bv 64 (r - st + 1)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 st) x19 x20 x21 x22 x23 x24 x25 x26
                    x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13328) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 st) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13bac) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
    SP SA sk st r HS HL MI Hsk Hst Hr Hsr.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HL) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(SA + 8, SA + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. destruct (Z.eqb_spec r 0) as [R0|R0].
  1:{ dr_if true. apply evt_done. left. split; [exact R0 | reflexivity]. }
  dr_if false. specialize (Hsr R0).
  step. step. rewrite (dr_sx32 sk) by lia.
  step. destruct (Z.eqb_spec sk 0) as [S0|S0].
  - dr_if false. step. step. step. dr_nm.
    destruct (Z.ltb_spec (r - st) 6001) as [LT|GE].
    + dr_if true. step. step. step. dr_nm.
      apply evt_done. right. right. split; [exact R0|]. split; [exact S0|]. split; [exact LT | reflexivity].
    + dr_if false. step.
      apply evt_done. right. left. split; [exact R0|]. split; [right; lia|]. do 3 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HS].
  - dr_if true. step.
    apply evt_done. right. left. split; [exact R0|]. split; [left; exact S0|]. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HS].
Qed.

(* The next line (relay.c:214): start = nul + 1 with the checked nul != -1 (s11 = -1); then the scan (0x13b8c). *)
Lemma dr_next : forall x1 sp gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28
    x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (nul : Z),
  0 <= nul -> nul + 1 < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 nul) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (nul + 1)) x19
                   x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (-1)) x28 x29 x30 x31)
              F (Z_to_bv 64 0x13b8c) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 nul) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             x26 (Z_to_bv 64 (-1)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13bcc) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 F
    fc m nul Hn Hn1.
  step. step. dr_ifs true. apply evt_done. reflexivity.
Qed.

(* s->used = rem, memmove (s->buf, start, rem) (relay.c:216-217): s3 = s->buf, s2 = start, s4 = rem. *)
Lemma dr_rest : forall x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA u0 rem : Z),
  rw_cells rsegs m (SA + 24) [C8 (Z_to_bv 64 u0)] -> mem_inv rsegs m ->
  evt rsegs (fun ms => exists m',
      ms = MS (mkR (Z_to_bv 64 0x13e68) sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x19 x18 (Z_to_bv 64 rem) x13 x14 x15 x16
                   x17 x18 x19 (Z_to_bv 64 rem) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x1dae8) fc None m' (seg_rom rsegs) /\
      munch [(SA + 24, SA + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (SA + 24) [C8 (Z_to_bv 64 rem)])
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 rem) x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13e54) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F
    fc m SA u0 rem HU MI.
  pose proof (rw_cells_bound _ _ _ _ HU) as CB0. cbn [cells_size csize] in CB0.
  pose proof (munch_refl [(SA + 24, SA + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact HU].
Qed.

(* After memmove (relay.c:218-222): with more than LINE_LIMIT bytes left, s->used = 0 and s->skip = 1; then the for
   loop's top. *)
Lemma dr_back : forall x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA sk u : Z),
  rw_cells rsegs m (SA + 8) [C4 (Z_to_bv 64 sk)] -> rw_cells rsegs m (SA + 24) [C8 (Z_to_bv 64 u)] ->
  rw_cells rsegs m (SP + 24) [C8 (Z_to_bv 64 6001)] -> mem_inv rsegs m -> 0 <= u < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (u < 6001 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 u) (Z_to_bv 64 6001) x12 x13 x14
                    x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13924) fc None m (seg_rom rsegs)) \/
      (6001 <= u /\ exists m',
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 1) (Z_to_bv 64 6001) x12 x13 x14
                    x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13924) fc None m' (seg_rom rsegs) /\
       munch [(SA + 8, SA + 12); (SA + 24, SA + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 8) [C4 (Z_to_bv 64 1)] /\ rw_cells rsegs m' (SA + 24) [C8 (Z_to_bv 64 0)]))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13e68) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m SP SA sk u HS HU HL MI Hu.
  pose proof (rw_cells_bound _ _ _ _ HS) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HU) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HL) as CB2. cbn [cells_size csize] in CB2.
  pose proof (munch_refl [(SA + 8, SA + 12); (SA + 24, SA + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. destruct (Z.ltb_spec u 6001) as [LT|GE].
  - dr_if true. apply evt_done. left. split; [exact LT | reflexivity].
  - dr_if false. step. step. step. step.
    apply evt_done. right. split; [exact GE|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HS | exact HU].
Qed.

(* gesture_seen (s, start) inlined after send_line (relay.c:212, :92): strrchr (line, ' ') with s2 = line. *)
Lemma dr_seen : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13bf0) sp gp tp x5 x6 x7 x8 x9 x18 (Z_to_bv 64 32) x12 x13 x14 x15 x16 x17 x18 x19
                   x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x1df28) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 0x13be4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m.
  step. step. step. apply evt_done. reflexivity.
Qed.

(* strncmp (line, PHD_EVENT_PARAM_GESTURE, verb) with verb = 13 (relay.c:95); s3 = last, strrchr's result. *)
Lemma dr_gverb : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13c08) sp gp tp x5 x6 x7 x8 x9 x18 (Z_to_bv 64 0x103e6) (Z_to_bv 64 13) x13 x14 x15
                   x16 x17 x18 x10 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x1de24) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 0x13bf0) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m.
  do 6 step. apply evt_done. reflexivity.
Qed.

(* The tests of relay.c:95 after strncmp's result v: line[verb] = ' ' (the checked line + verb: line non-NULL, no
   wrap), last non-NULL and not line + verb; then strcmp (last + 1, PHD_GESTURE_BEGIN) (relay.c:97) with the checked
   s5 = last + 1. line[verb] is read only when v = 0. *)
Lemma dr_gtest : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x28 x29 x30 x31
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v L lst : Z) (b : byte),
  (v = 0 -> rw_cells rsegs m (L + 13) [C1 b]) ->
  0 <= v < 2 ^ 64 -> 0 < L -> L + 13 < 2 ^ 64 -> 0 <= lst -> lst + 1 < 2 ^ 64 ->
  evt rsegs (fun ms =>
      ((v <> 0 \/ (v = 0 /\ (bv_unsigned b <> 32 \/ lst = 0 \/ lst = L + 13))) /\ exists e10 e11,
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 e10 e11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) x20 x21
                    x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x13bcc) fc None m (seg_rom rsegs)) \/
      (v = 0 /\ bv_unsigned b = 32 /\ lst <> 0 /\ lst <> L + 13 /\
       ms = MS (mkR (Z_to_bv 64 0x13c54) sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (lst + 1)) (Z_to_bv 64 0x10358) x12 x13
                    x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) x20 (Z_to_bv 64 (lst + 1)) x22 (Z_to_bv 64 9) x24
                    x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x1dd5c) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) x20
             x21 x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13c08) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x28 x29 x30 x31 F fc m v L lst b
    HB Hv HL HL13 Hl0 Hl1.
  pose proof (byte_range b) as RB.
  step. destruct (Z.eqb_spec v 0) as [V0|V0].
  2:{ dr_if true. apply evt_done. left. split; [left; exact V0|]. do 2 eexists. reflexivity. }
  dr_if false. specialize (HB V0).
  pose proof (rw_cells_bound _ _ _ _ HB) as CB0. cbn [cells_size csize] in CB0.
  step. dr_ifs false. step. step. dr_ifs false.
  step. unfold zxb. step. step. step. step.
  step. destruct (Z.eqb_spec (bv_unsigned b) 32) as [B32|B32].
  2:{ dr_if true. apply evt_done. left. split; [right; split; [exact V0 | left; exact B32]|].
      do 2 eexists. reflexivity. }
  dr_if false. step. destruct (Z.eqb_spec lst 0) as [S0|S0].
  1:{ dr_if true. apply evt_done. left. split; [right; split; [exact V0 | right; left; exact S0]|].
      do 2 eexists. reflexivity. }
  dr_if false. step. step.
  destruct (Z.eqb_spec lst (L + 13)) as [S1|S1].
  1:{ dr_if true. apply evt_done. left. split; [right; split; [exact V0 | right; right; exact S1]|].
      do 2 eexists. reflexivity. }
  dr_if false. step. dr_ifs false.
  step. step. step. step. step.
  apply evt_done. right. split; [exact V0|]. split; [exact B32|]. split; [exact S0|]. split; [exact S1 | reflexivity].
Qed.

(* begin = !strcmp (last + 1, PHD_GESTURE_BEGIN), its result r kept in s4; s7, s10, s11 back to 9, 4, -1; not a
   begin: strcmp (last + 1, PHD_GESTURE_END) (relay.c:97-98). *)
Lemma dr_gbeg : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  0 <= r < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (r = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 r) x21
                    x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x13c7c) fc None m (seg_rom rsegs)) \/
      (r <> 0 /\
       ms = MS (mkR (Z_to_bv 64 0x13c78) sp gp tp x5 x6 x7 x8 x9 x21 (Z_to_bv 64 0x103af) x12 x13 x14 x15 x16 x17 x18
                    x19 (Z_to_bv 64 r) x21 x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x1dd5c) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13c54) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 F fc m r Hr.
  step. step. step. step. step. destruct (Z.eqb_spec r 0) as [R0|R0].
  - dr_if true. apply evt_done. left. split; [exact R0 | reflexivity].
  - dr_if false. step. step. step. step. apply evt_done. right. split; [exact R0 | reflexivity].
Qed.

(* strcmp (last + 1, PHD_GESTURE_END)'s result r (relay.c:98): neither a begin nor an end is the next line. *)
Lemma dr_gend : forall x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  0 <= r < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (r <> 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                    x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13bcc) fc None m (seg_rom rsegs)) \/
      (r = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                    x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13c7c) fc None m (seg_rom rsegs)))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13c78) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 F fc m r Hr.
  step. destruct (Z.eqb_spec r 0) as [R0|R0].
  - dr_if false. apply evt_done. right. split; [exact R0 | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact R0 | reflexivity].
Qed.

(* The search of s->held for the key [line, last) (relay.c:100): 0(sp) = bg (begin's strcmp result, s4),
   32(sp) = kl = last - line, 8(sp) = nheld; with nheld = 0 the test after the search (0x13d14); otherwise
   16(sp) = 8 nheld, s3 = 8 n = 0, s8 = nheld (the slots left), s10 = s->held and the ubsan flags s11 = (held != 0),
   s4 = (held != 0 and 8-aligned), then the search's head (0x13cc4). *)
Lemma dr_gscan : forall x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA L lst bg held nh : Z) (w0 w1 w2 w4 : word),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 nh)] ->
  rw_cells rsegs m SP [C8 w0; C8 w1; C8 w2] -> rw_cells rsegs m (SP + 32) [C8 w4] ->
  mem_inv rsegs m -> SA + 52 <= SP \/ SP + 40 <= SA + 40 ->
  0 <= nh < 2 ^ 31 -> 0 <= L <= lst -> lst < 2 ^ 64 -> 0 <= bg < 2 ^ 64 ->
  (0 < nh -> 0 < held < 2 ^ 64 /\ held mod 8 = 0) ->
  evt rsegs (fun ms =>
      (nh = 0 /\ exists m',
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 (lst - L)) (Z_to_bv 64 nh) x12
                    x13 x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 lst) (Z_to_bv 64 bg) x21 x22 x23 x24 x25 x26 x27
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x13d14) fc None m' (seg_rom rsegs) /\
       munch [(SP, SP + 24); (SP + 32, SP + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' SP [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 nh); C8 w2] /\
       rw_cells rsegs m' (SP + 32) [C8 (Z_to_bv 64 (lst - L))]) \/
      (0 < nh /\ exists m',
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 (nh * 8)) (Z_to_bv 64 1) x12 x13
                    x14 x15 x16 x17 (Z_to_bv 64 L) (Z_to_bv 64 0) (Z_to_bv 64 1) x21 x22 x23 (Z_to_bv 64 nh) x25
                    (Z_to_bv 64 held) (Z_to_bv 64 1) x28 x29 x30 x31)
               F (Z_to_bv 64 0x13cc4) fc None m' (seg_rom rsegs) /\
       munch [(SP, SP + 24); (SP + 32, SP + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' SP [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 nh); C8 (Z_to_bv 64 (nh * 8))] /\
       rw_cells rsegs m' (SP + 32) [C8 (Z_to_bv 64 (lst - L))]))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L)
             (Z_to_bv 64 lst) (Z_to_bv 64 bg) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13c7c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m SP SA
    L lst bg held nh w0 w1 w2 w4 HH HF HK MI HD Hnh HL Hlst Hbg HHe.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HK) as CB2. cbn [cells_size csize] in CB2.
  pose proof (munch_refl [(SP, SP + 24); (SP + 32, SP + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. rewrite (dr_sx32 nh) by lia. step. dr_nm. step. step.
  step. destruct (Z.eqb_spec nh 0) as [N0|N0].
  - dr_ifs true. apply evt_done. left. split; [exact N0|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HF | exact HK].
  - dr_ifs false. destruct (HHe ltac:(lia)) as [Hh Hh8].
    step. step. step. step. dr_cmps. step. dr_nm. step. dr_nm. dr_m1.
    step. dr_cmp. step. dr_land. step. dr_cmp. step. dr_nm. step. dr_nm. step.
    apply evt_done. right. split; [lia|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HF | exact HK].
Qed.

(* The search's head (relay.c:100-101): the checked slot P = s->held + K (s10 = s->held, s3 = K = 8 n, no wrap, not
   NULL, the flags s11 and s4 set), strlen (s->held[n]) with s5 = s->held[n] = p, s7 = P. *)
Lemma dr_hlen : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x28 x29 x30
    x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (held K P p : Z),
  P = held + K -> rw_cells rsegs m P [C8 (Z_to_bv 64 p)] -> 0 < held -> 0 <= K ->
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13ce8) sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17 x18
                   (Z_to_bv 64 K) (Z_to_bv 64 1) (Z_to_bv 64 p) x22 (Z_to_bv 64 P) x24 x25 (Z_to_bv 64 held)
                   (Z_to_bv 64 1) x28 x29 x30 x31)
              F (Z_to_bv 64 0x1dd94) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 K) (Z_to_bv 64 1) x21 x22 x23
             x24 x25 (Z_to_bv 64 held) (Z_to_bv 64 1) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13cc4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x28 x29 x30 x31 F fc m
    held K P p HP HC Hh HK.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB0. cbn [cells_size csize] in CB0.
  step. rewrite <- HP. step. dr_ifs false.
  step. dr_cmp. step. dr_nm. step. dr_ifs false. step. dr_ifs false.
  step. step. step. apply evt_done. reflexivity.
Qed.

(* strlen's result len (relay.c:101): equal to kl = last - line (32(sp)), strncmp (s->held[n], line, kl). *)
Lemma dr_hcmp : forall x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP len kl : Z),
  rw_cells rsegs m (SP + 32) [C8 (Z_to_bv 64 kl)] -> 0 <= len < 2 ^ 64 -> 0 <= kl < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (len <> kl /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 len) (Z_to_bv 64 kl) x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13d04) fc None m (seg_rom rsegs)) \/
      (len = kl /\
       ms = MS (mkR (Z_to_bv 64 0x13d00) (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x21 x18 (Z_to_bv 64 kl) x13 x14 x15 x16
                    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1de24) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 len) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13ce8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F
    fc m SP len kl HK Hl Hk.
  pose proof (rw_cells_bound _ _ _ _ HK) as CB0. cbn [cells_size csize] in CB0.
  step. step. destruct (Z.eqb_spec len kl) as [E|E].
  - dr_if false. step. step. step. step. apply evt_done. right. split; [exact E | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact E | reflexivity].
Qed.

(* strncmp's result v (relay.c:101): v = 0 is the key held at the slot P (s7) holding p, with s8 = c >= 1 slots
   left; a begin (bg = 0 at 0(sp), relay.c:103) is the next line with s7, s10, s11 back to 9, 4, -1 (c != 0: not
   the add); an end frees s->held[n] (relay.c:116-118) after the checked P = s->held + K (no wrap). *)
Lemma dr_hfound : forall x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x25 x27 x28 x29 x30 x31
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP v bg held K P p c : Z),
  rw_cells rsegs m SP [C8 (Z_to_bv 64 bg)] -> P = held + K -> rw_cells rsegs m P [C8 (Z_to_bv 64 p)] ->
  0 <= v < 2 ^ 64 -> 0 <= bg < 2 ^ 64 -> 0 < held -> 0 <= K -> 1 <= c < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (v <> 0 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18
                    (Z_to_bv 64 K) x20 x21 x22 (Z_to_bv 64 P) (Z_to_bv 64 c) x25 (Z_to_bv 64 held) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13d04) fc None m (seg_rom rsegs)) \/
      (v = 0 /\ bg = 0 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 bg) x11 x12 x13 x14 x15 x16 x17 x18
                    (Z_to_bv 64 K) x20 x21 x22 (Z_to_bv 64 9) (Z_to_bv 64 c) x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28
                    x29 x30 x31)
               F (Z_to_bv 64 0x13bcc) fc None m (seg_rom rsegs)) \/
      (v = 0 /\ bg <> 0 /\
       ms = MS (mkR (Z_to_bv 64 0x13dc8) (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16
                    x17 x18 (Z_to_bv 64 K) x20 x21 x22 (Z_to_bv 64 P) (Z_to_bv 64 c) x25 (Z_to_bv 64 held) x27 x28 x29
                    x30 x31)
               F (Z_to_bv 64 0x15f4c) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 K) x20
             x21 x22 (Z_to_bv 64 P) (Z_to_bv 64 c) x25 (Z_to_bv 64 held) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13d00) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x25 x27 x28 x29 x30 x31 F fc m SP v bg
    held K P p c HB HP HC Hv Hbg Hh HK Hc.
  pose proof (rw_cells_bound _ _ _ _ HB) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB1. cbn [cells_size csize] in CB1.
  step. destruct (Z.eqb_spec v 0) as [V0|V0].
  2:{ dr_if false. apply evt_done. left. split; [exact V0 | reflexivity]. }
  dr_if true. step. step. destruct (Z.eqb_spec bg 0) as [B0|B0].
  - dr_if true. step. step. step. step. dr_if true.
    apply evt_done. right. left. split; [exact V0|]. split; [exact B0 | reflexivity].
  - dr_if false. step. dr_nm. dr_lx. step. dr_ifs false. step. step.
    apply evt_done. right. right. split; [exact V0|]. split; [exact B0 | reflexivity].
Qed.

(* The search's next slot (relay.c:100): s3 = K + 8, s8 = c - 1; K + 8 < 8 nheld (16(sp)) goes on at the head, the
   end to the test after the search (0x13d14). *)
Lemma dr_hstep : forall x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28
    x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP K nh c : Z),
  rw_cells rsegs m (SP + 16) [C8 (Z_to_bv 64 (nh * 8))] ->
  0 <= K -> K + 8 < 2 ^ 64 -> 0 <= nh < 2 ^ 31 -> 1 <= c < 2 ^ 31 ->
  evt rsegs (fun ms =>
      (K + 8 <> nh * 8 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (nh * 8)) x11 x12 x13 x14 x15 x16 x17 x18
                    (Z_to_bv 64 (K + 8)) x20 x21 x22 x23 (Z_to_bv 64 (c - 1)) x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13cc4) fc None m (seg_rom rsegs)) \/
      (K + 8 = nh * 8 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (nh * 8)) x11 x12 x13 x14 x15 x16 x17 x18
                    (Z_to_bv 64 (K + 8)) x20 x21 x22 x23 (Z_to_bv 64 (c - 1)) x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13d14) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 K) x20 x21 x22
             x23 (Z_to_bv 64 c) x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13d04) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 F fc
    m SP K nh c HF HK HK8 Hnh Hc.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB0. cbn [cells_size csize] in CB0.
  step. step. dr_nm. rewrite (dr_sw32 (c + -1)) by lia. replace (c + -1) with (c - 1) by lia.
  step. step. destruct (Z.eqb_spec (K + 8) (nh * 8)) as [E|E].
  - dr_if false. apply evt_done. right. split; [exact E | reflexivity].
  - dr_if true. apply evt_done. left. split; [exact E | reflexivity].
Qed.

(* After the search, the key not held (relay.c:103): s7, s10, s11 back to 9, 4, -1; an end (bg != 0, relay.c:116)
   is the next line; a begin grows s->held to 8 (nheld + 1) bytes with realloc (relay.c:106), the checked
   nheld + 1 (no signed overflow). *)
Lemma dr_gadd : forall x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA held bg nh : Z),
  rw_cells rsegs m SP [C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 nh)] -> rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 held)] ->
  0 <= bg < 2 ^ 64 -> 0 <= nh < 2 ^ 31 - 1 ->
  evt rsegs (fun ms =>
      (bg <> 0 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 bg) x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x13bcc) fc None m (seg_rom rsegs)) \/
      (bg = 0 /\
       ms = MS (mkR (Z_to_bv 64 0x13d48) (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 held)
                    (Z_to_bv 64 (nh * 8 + 8)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 9) x24 x25
                    (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x178f8) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13d14) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m SP SA held bg nh HF HH Hbg Hnh.
  pose proof (rw_cells_bound _ _ _ _ HF) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB1. cbn [cells_size csize] in CB1.
  step. step. step. step. step. destruct (Z.eqb_spec bg 0) as [B0|B0].
  2:{ dr_if true. apply evt_done. left. split; [exact B0 | reflexivity]. }
  dr_if false. step. step. dr_ifs false.
  step. step. dr_nm. rewrite (dr_sw32 (nh + 1)) by lia. step. dr_ifs false.
  step. step. dr_nm. step.
  replace ((nh + 1) * 2 ^ 3) with (nh * 8 + 8) by lia.
  apply evt_done. right. split; [exact B0 | reflexivity].
Qed.

(* realloc's result res (relay.c:109-112): NULL is the next line; otherwise s->held = res, strndup (line, kl). *)
Lemma dr_gnew : forall x1 gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP SA h0 res kl : Z),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 h0)] -> rw_cells rsegs m (SP + 32) [C8 (Z_to_bv 64 kl)] ->
  mem_inv rsegs m -> SA + 48 <= SP + 32 \/ SP + 40 <= SA + 40 -> 0 <= res < 2 ^ 64 ->
  evt rsegs (fun ms =>
      (res = 0 /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x13bcc) fc None m (seg_rom rsegs)) \/
      (res <> 0 /\ exists m',
       ms = MS (mkR (Z_to_bv 64 0x13d5c) (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x18 (Z_to_bv 64 kl) x12 x13
                    x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1de84) fc None m' (seg_rom rsegs) /\
       munch [(SA + 40, SA + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 40) [C8 (Z_to_bv 64 res)] /\ rw_cells rsegs m' (SP + 32) [C8 (Z_to_bv 64 kl)]))
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x19
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13d48) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc
    m SP SA h0 res kl HH HK MI HD Hr.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HK) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(SA + 40, SA + 48)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. destruct (Z.eqb_spec res 0) as [R0|R0].
  - dr_if true. apply evt_done. left. split; [exact R0 | reflexivity].
  - dr_if false. step. step. step. step.
    apply evt_done. right. split; [exact R0|]. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HH | exact HK].
Qed.

(* strndup's result cp (relay.c:113-114): non-NULL, s->held[s->nheld++] = cp with the checked nheld + 1 and the checked
   slot P = s->held + 8 nheld (not NULL, no wrap, 8-aligned); then the next line. *)
Lemma dr_gkeep : forall x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x28 x29 x30
    x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA held nh P cp : Z) (j : word),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 nh)] -> P = held + 8 * nh ->
  rw_cells rsegs m P [C8 j] -> mem_inv rsegs m -> P + 8 <= SA + 40 \/ SA + 52 <= P ->
  0 <= cp < 2 ^ 64 -> 0 <= nh < 2 ^ 31 - 1 -> 0 < held -> held mod 8 = 0 ->
  evt rsegs (fun ms =>
      (cp = 0 /\
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 cp) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                    x21 x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x13bcc) fc None m (seg_rom rsegs)) \/
      (cp <> 0 /\ exists m' e11 e12 e13 e14 e15 e16,
       ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 cp) e11 e12 e13 e14 e15 e16 x17 x18 x19 x20
                    x21 x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
               F (Z_to_bv 64 0x13bcc) fc None m' (seg_rom rsegs) /\
       munch [(SA + 48, SA + 52); (P, P + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 (nh + 1))] /\
       rw_cells rsegs m' P [C8 (Z_to_bv 64 cp)]))
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 (Z_to_bv 64 cp) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13d5c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x28 x29 x30 x31 F fc m SA
    held nh P cp j HH HP HC MI HD Hcp Hnh Hh Hh8.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB1. cbn [cells_size csize] in CB1.
  pose proof (munch_refl [(SA + 48, SA + 52); (P, P + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. destruct (Z.eqb_spec cp 0) as [C0|C0].
  - dr_if true. apply evt_done. left. split; [exact C0 | reflexivity].
  - dr_if false. step. rewrite (dr_sx32 nh) by lia. step. dr_nm. rewrite (dr_sw32 (nh + 1)) by lia.
    step. dr_ifs false.
    step. step. dr_nm. step. dr_nm.
    replace (held + nh * 2 ^ 3) with P by (rewrite HP; ring).
    step. dr_cmp. step. dr_cmp. step. step. dr_ifs false.
    step. dr_cmp. step. dr_cmps. step. step. step. dr_ifs false.
    step. dr_ifs false. step. dr_land. step. dr_ifs false.
    step. step. step. step. step. step.
    apply evt_done. right. split; [exact C0|]. do 7 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HH | exact HC].
Qed.

(* After free (s->held[n]) (relay.c:118-119): s->held[n] = s->held[--s->nheld] with the checked nheld - 1, the
   checked last slot LP = s->held + 8 (nheld - 1) holding q and the checked slot P = s->held + K (K = 8 n in s3);
   s7, s10, s11 back to 9, 4, -1, then the next line. *)
Lemma dr_gdrop : forall x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SA held nh K P LP q : Z) (j : word),
  rw_cells rsegs m (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 nh)] ->
  P = held + K -> rw_cells rsegs m P [C8 j] -> LP = held + 8 * (nh - 1) -> rw_cells rsegs m LP [C8 (Z_to_bv 64 q)] ->
  mem_inv rsegs m -> P + 8 <= SA + 40 \/ SA + 52 <= P -> LP + 8 <= SA + 48 \/ SA + 52 <= LP ->
  1 <= nh < 2 ^ 31 -> 0 < held -> held mod 8 = 0 -> 0 <= K -> K mod 8 = 0 -> 0 <= q < 2 ^ 64 ->
  evt rsegs (fun ms => exists m' e10 e11 e12 e13 e14,
      ms = MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 e10 e11 e12 e13 e14 x15 x16 x17 x18 (Z_to_bv 64 K) x20 x21
                   x22 (Z_to_bv 64 9) x24 x25 (Z_to_bv 64 4) (Z_to_bv 64 (-1)) x28 x29 x30 x31)
              F (Z_to_bv 64 0x13bcc) fc None m' (seg_rom rsegs) /\
      munch [(SA + 48, SA + 52); (P, P + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (SA + 40) [C8 (Z_to_bv 64 held); C4 (Z_to_bv 64 (nh - 1))] /\
      rw_cells rsegs m' P [C8 (Z_to_bv 64 q)])
    (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 SA) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 K) x20 x21 x22
             x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13dc8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F
    fc m SA held nh K P LP q j HH HP HC HLP HQ MI HD HD2 Hnh Hh Hh8 HK HK8 Hq.
  pose proof (rw_cells_bound _ _ _ _ HH) as CB0. cbn [cells_size csize] in CB0.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB1. cbn [cells_size csize] in CB1.
  pose proof (rw_cells_bound _ _ _ _ HQ) as CB2. cbn [cells_size csize] in CB2.
  pose proof (munch_refl [(SA + 48, SA + 52); (P, P + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (dr_sx32 nh) by lia. step. dr_nm. rewrite (dr_sw32 (nh + -1)) by lia.
  replace (nh + -1) with (nh - 1) by lia.
  step. dr_ifs false.
  step. step. dr_nm. step. dr_nm.
  replace (held + (nh - 1) * 2 ^ 3) with LP by (rewrite HLP; ring).
  step. dr_cmp. step. dr_cmp. step. step. dr_ifs false.
  step. dr_cmp. step. dr_cmps. step. step. step. dr_ifs false.
  step. dr_ifs false. step. dr_land. step. dr_ifs false.
  step. dr_nm. dr_lx. step. dr_ifs false.
  step. step. dr_land. step. dr_ifs false.
  step. step. rewrite <- HP. step.
  step. step. step. step.
  apply evt_done. do 6 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HH | exact HC].
Qed.
