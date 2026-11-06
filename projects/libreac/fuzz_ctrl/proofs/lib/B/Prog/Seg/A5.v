(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and addresses changed; 2105 of its 2257 lines of code are new or changed and 859 lines of the source are left out. *)
(* Segment A5 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the our[] loop head 0x81548
   with its body 0x81550 .. 0x8158c (R1's range), the loop exit 0x815a0 .. 0x815f8 and the stubs 0x81af4 (which
   jumps to P2's reload 0x81cac `ld s8,56(s1)`) / 0x82fd0, Inv_B81548_at -> Inv_B815fc (R2, through the catalogue
   call) / Inv_B81cb0 (P3).
   rule 24: no function proved (a slot segment; the v1.8 proof carried to v1.9.0, the changed loop exit re-walked).
   The loop fills our[0..6): on a turn with left <> 0 it copies the input byte at the cursor (the inline shadow
   check 0x81560, whose error call 0x8159c is not reached, and the UBSan cursor test T01 at 0x81554, whose trap
   0x82fa0 is not taken), on a turn with left = 0 it stores 0 (0x81578).  After six turns the exit 0x815a0 spills
   fr + 64 (a7), fr + 32 (a6), the selector (s8) and fr (s9) to [A + 152] / [A + 160] / [A + 48] / [A + 40], and
   then either leaves to P3 (left = 0 through 0x81af4 and 0x81cac, or an even mode byte at 0x815e8; both reload
   s8 = [A + 56] = fr + 3040, the code-byte pointer) or reads the mode byte (the check 0x815cc with its error call
   0x82fe0, and T02 at 0x815bc) and, on an odd mode, marks the catalogue count cell usable (S(fr) + 332 = 00),
   zeroes it and calls reac_box_catalogue (CAT@0x815f8).
   This file owns the loop: it proves one turn (b_turn) and closes the loop by well-founded induction on 5 - t
   (b_loop).  lib/B/Prog/Seg/R1.v uses the same turn lemma from the body cut 0x81550.  All cuts are SlotInv.v's
   official ones (Inv_B81548_at = LOOPB, Inv_B81550, Inv_B815fc, Inv_B81cb0); FRAH carries the input-block facts. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_catalogue_c.
Import ListNotations.
Open Scope Z_scope.

Module RBC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_box_catalogue_c.

(* Proof speed (briefs/common.md, Proof speed (2)): lia and tauto case-split every disjunction (lia also every mod
   fact) of the context.  b_cat_evt and b_turn_gen hide the ones a step does not need behind rs_hold, and open one
   where a step uses it. *)
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.

(* ---- byte, shadow and branch helpers (the image-B twins of lib/B/Prog/Seg/R3.v's) ---- *)

Lemma b_le1_lit : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite MState.unsigned_lit by lia. reflexivity. Qed.

Lemma b_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

Lemma b_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma b_sh_add : forall p i, p mod 8 = 0 -> 0 <= i -> shadow_addr (p + i) = shadow_addr p + i / 8.
Proof. intros p i Hp Hi. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma b_nth_repeat : forall (x : byte) n k, (k < n)%nat -> nth_error (repeat x n) k = Some x.
Proof. intros x n. induction n as [|n IH]; intros k Hk; [lia|]. destruct k; [reflexivity|]. cbn. apply IH. lia. Qed.

(* The shadow of 8 z bytes at p (p mod 8 = 0) is z zero bytes. *)
Lemma b_addr_z : forall m p (z : nat) n, n = 8 * Z.of_nat z -> 0 <= p -> p mod 8 = 0 -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) (repeat (Z_to_bv 8 0) z) -> addressable m p n.
Proof.
  intros m p z n -> Hp Hp8 Hpe Happ (_ & _ & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|].
  exists (Z_to_bv 8 0). split; [|left; reflexivity].
  rewrite b_sh_add by lia.
  assert (Hq : 0 <= i / 8 < Z.of_nat z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hk : (Z.to_nat (i / 8) < z)%nat) by lia.
  pose proof (Hb (Z.to_nat (i / 8))) as E. rewrite repeat_length in E. specialize (E Hk).
  rewrite Z2Nat.id in E by lia. rewrite E. apply b_nth_repeat. exact Hk.
Qed.

Lemma b_shadow_rw : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros W m m' HS MU WM H a Ha. destruct (HS a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma b_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma b_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

Lemma b_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma b_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma b_sh_app_dj : forall x a, in_shadow x -> app_mem a -> x + 1 <= a \/ a + 1 <= x.
Proof.
  intros x a Hx Ha.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha.
  destruct Hx as [Hx|Hx]; destruct Ha as [Ha|Ha]; lia.
Qed.

Lemma b_land1 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof. intros x H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

(* A conditional branch whose condition the engine has not decided yet: replace it by the value the segment's
   premises give.  On a literal condition the engine decides it in the step itself, so the tactic is a no-op. *)
Ltac b_br :=
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first
        [ replace c with true;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?MState.unsigned_lit by lia; solve_cond]
        | replace c with false;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?MState.unsigned_lit by lia; solve_cond] ]
  end).

(* A one-byte store `sb r,o(s3)` writes `le1 r`; the engine folds it into the shadow cells once it is a byte
   list (lib/B/Prog/Seg/R3.v's r3_fix). *)
Ltac b_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (b_le1_lit z) by lia; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (b_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac b_sb := step; b_fix.

(* The end of a turn: the byte v stored at d, nothing else written. *)
Ltac b_post v :=
  lazymatch goal with
  | |- munch _ ?m (write_to_mem ?m _ ?BS) /\ _ =>
      let EBS := fresh "EBS" in
      assert (EBS : BS = [v])
        by (first [apply le1_zxb | (apply b_le1_lit; lia) | (vm_compute; reflexivity) | reflexivity]);
      rewrite EBS;
      split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|];
      split; [apply wmono_write, wmono_refl|];
      apply bytes_at_write_same; cbn [length]; lia
  end.

(* ---- the loop body from the R1 cut 0x81550 (left <> 0): T01, the cursor's shadow check, the byte copy and the
   store our[t] = in[t]; it ends at the head 0x81548 (cnt > 1) or at the loop exit 0x815a0 (cnt = 1) ---- *)
Lemma b_ld_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 (q + 1) ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81550) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq -> -> -> -> -> -> -> Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS.
  pose proof (rc_byte_signed kq) as KRq.
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  (* 0x81550 bltu a1,a3 (T01: 1 < q + 1) *)
  step. b_br.
  (* 0x81558 srli a4,s6,0x3; 0x8155c add a4,a4,s10; 0x81560 lb a4,0(a4); 0x81564 bnez a4,81590 *)
  step. rewrite (MState.unsigned_lit q) by lia. rewrite rc_shr3.
  step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed kq)) by lia.
  enough (KC : forall (x4 x5 : word),
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 1) (Z_to_bv 64 d)
                         (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 v) s3 s4 s5 (Z_to_bv 64 q) s7 s8 s9
                         (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x81568) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed kq) 0) as [E|E]; cbn [negb]; [apply KC|].
    (* 0x81590 andi a5,s6,7; 0x81594 blt a5,a4,81568 *)
    step. rewrite (MState.unsigned_lit q) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed (q mod 8) (bv_signed kq)) by lia.
    replace (q mod 8 <? bv_signed kq) with true by (symmetry; apply Z.ltb_lt; lia).
    apply KC. }
  intros x4 x5.
  (* 0x81568 lbu a4,0(s6); 0x8156c addi s2,s2,-1; 0x81570 mv s6,a3; 0x81574 j 8157c *)
  step. step. step. step.
  (* 0x8157c sb a4,0(a2); 0x81580 addi a0,a0,-1; 0x81584 addi a2,a2,1; 0x81588 beqz a0 *)
  step. step. step. step.
  destruct (Z.eq_dec cnt 1) as [E1|N1].
  - subst cnt. b_br.
    apply evt_done. unfold Q. cbv beta.
    do 3 eexists. split.
    + replace (Z_to_bv 64 (1 + -1)) with (Z_to_bv 64 (1 - 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (v + -1)) with (Z_to_bv 64 (v - 1)) by (f_equal; lia).
      reflexivity.
    + b_post b.
  - b_br.
    (* 0x8158c j 81548 *)
    step.
    apply evt_done. unfold Q. cbv beta.
    rewrite (proj2 (Z.eqb_neq cnt 1) N1).
    do 3 eexists. split.
    + replace (Z_to_bv 64 (cnt + -1)) with (Z_to_bv 64 (cnt - 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (v + -1)) with (Z_to_bv 64 (v - 1)) by (f_equal; lia).
      reflexivity.
    + b_post b.
Qed.

(* The same turn from the loop head 0x81548 with left <> 0: the head's test falls through and 0x8154c computes the
   bumped cursor, which is b_ld_evt's start. *)
Lemma b_hd_ld_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81548) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq -> -> -> -> -> -> Hcnt Hd0 Hd Hq0 Hq Hv0 Hv HK Hsh HRq HOKq HRb HS.
  (* 0x81548 beqz s2 (not taken); 0x8154c addi a3,s6,1 *)
  step. b_br.
  step.
  apply (b_ld_evt ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 1) (Z_to_bv 64 d)
           (Z_to_bv 64 (q + 1)) a4 a5 a6 a7 (Z_to_bv 64 v) s3 s4 s5 (Z_to_bv 64 q) s7 s8 s9 (Z_to_bv 64 K) s11
           t3 t4 t5 t6 F fc m cnt d q v K b kq);
    try reflexivity; try assumption; try lia.
Qed.

(* The zero arm of a turn (left = 0, the head's test taken): our[t] = 0 at 0x81578. *)
Lemma b_z_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d : Z),
    a0 = Z_to_bv 64 cnt -> a2 = Z_to_bv 64 d -> s2 = Z_to_bv 64 0 ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) a1 (Z_to_bv 64 (d + 1)) a3
                       (Z_to_bv 64 0) a5 a6 a7 (Z_to_bv 64 0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81548) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d -> -> -> Hcnt Hd0 Hd HS.
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  (* 0x81548 beqz s2 (taken); 0x81578 li a4,0 *)
  step. b_br.
  step.
  (* 0x8157c sb a4,0(a2); 0x81580 addi a0,a0,-1; 0x81584 addi a2,a2,1; 0x81588 beqz a0 *)
  step. step. step. step.
  destruct (Z.eq_dec cnt 1) as [E1|N1].
  - subst cnt. b_br.
    apply evt_done. unfold Q. cbv beta.
    eexists. split.
    + replace (Z_to_bv 64 (1 + -1)) with (Z_to_bv 64 (1 - 1)) by (f_equal; lia).
      reflexivity.
    + b_post (Z_to_bv 8 0).
  - b_br.
    step.
    apply evt_done. unfold Q. cbv beta.
    rewrite (proj2 (Z.eqb_neq cnt 1) N1).
    eexists. split.
    + replace (Z_to_bv 64 (cnt + -1)) with (Z_to_bv 64 (cnt - 1)) by (f_equal; lia).
      reflexivity.
    + b_post (Z_to_bv 8 0).
Qed.

(* ---- the loop exit 0x815a0 .. 0x815b0 (re-walked for v1.9.0; the v1.8 exit stored three words, s7 = fr, a6 =
   fr + 64, s8 = sel): the four spill stores 0x815a0 sd a7,152(s1) (fr + 64), 0x815a4
   sd a6,160(s1) (fr + 32), 0x815a8 sd s8,48(s1) (sel), 0x815ac sd s9,40(s1) (fr), and the left test 0x815b0
   (left = 0 leaves to P3 through the stub 0x81af4, which sets s9 = 0 and s7 = s6, the cursor, and jumps to P2's
   reload 0x81cac ld s8,56(s1), so P3 0x81cb0 is reached with s8 = [A + 56]) ---- *)
Lemma b_tail_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ab q w frv a6v a7v selv v56 : Z) (xs1 xs2 : list byte),
    s1 = Z_to_bv 64 Ab -> s2 = Z_to_bv 64 w -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 frv ->
    a6 = Z_to_bv 64 a6v -> a7 = Z_to_bv 64 a7v -> s8 = Z_to_bv 64 selv ->
    0 <= Ab -> Ab + 168 <= 2 ^ 64 -> 0 <= q < 2 ^ 64 -> 0 <= w -> w + 2 < 2 ^ 64 ->
    0 <= frv < 2 ^ 64 -> 0 <= a6v < 2 ^ 64 -> 0 <= a7v < 2 ^ 64 -> 0 <= selv < 2 ^ 64 ->
    length xs1 = 16%nat -> length xs2 = 16%nat ->
    rw_cells rsegs m (Ab + 40) [CB 16 xs1] -> rw_cells rsegs m (Ab + 152) [CB 16 xs2] ->
    ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v56)] ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         munch [(Ab + 40, Ab + 56); (Ab + 152, Ab + 168)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Ab + 40) (le8 (Z_to_bv 64 frv)) /\
         bytes_at rsegs m' (Ab + 48) (le8 (Z_to_bv 64 selv)) /\
         bytes_at rsegs m' (Ab + 152) (le8 (Z_to_bv 64 a7v)) /\
         bytes_at rsegs m' (Ab + 160) (le8 (Z_to_bv 64 a6v)) /\
         ((w = 0 /\ exists R : bvmap 5 word,
             ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m' (seg_rom rsegs) /\
             getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\
             getr R 9 = Z_to_bv 64 Ab /\ getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
             getr R 23 = Z_to_bv 64 q /\ getr R 25 = Z_to_bv 64 0 /\ getr R 24 = Z_to_bv 64 v56)
          \/
          (w <> 0 /\
             ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 a6v)
                           (Z_to_bv 64 a7v) (Z_to_bv 64 w) s3 s4 s5 (Z_to_bv 64 q) s7 (Z_to_bv 64 selv)
                           (Z_to_bv 64 frv) s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x815b4) fc None m' (seg_rom rsegs))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab q w frv a6v a7v selv v56 xs1 xs2 -> -> -> -> -> -> ->
    HAb0 HAb Hq Hw0 Hw Hfrv Ha6v Ha7v Hselv Hx1 Hx2 CH1 CH2 RO56.
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  pose proof (munch_refl [(Ab + 40, Ab + 56); (Ab + 152, Ab + 168)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x815a0 sd a7,152(s1); 0x815a4 sd a6,160(s1); 0x815a8 sd s8,48(s1); 0x815ac sd s9,40(s1).  The engine keeps
     the write set in MU / WM, the two spill blocks in CH1 / CH2 and the word [Ab + 56] in RO56
     (mem_after_store). *)
  step. step. step. step.
  destruct CH1 as ((_ & HB1) & _). cbn [cells_bytes cbytes] in HB1. rewrite app_nil_r in HB1.
  apply bytes_at_app in HB1. destruct HB1 as (HB40 & HB48).
  rewrite length_le8 in HB48. change (Z.of_nat 8) with 8 in HB48.
  replace (Ab + 40 + 8) with (Ab + 48) in HB48 by lia.
  destruct CH2 as ((_ & HB2) & _). cbn [cells_bytes cbytes] in HB2. rewrite app_nil_r in HB2.
  apply bytes_at_app in HB2. destruct HB2 as (HB152 & HB160).
  rewrite length_le8 in HB160. change (Z.of_nat 8) with 8 in HB160.
  replace (Ab + 152 + 8) with (Ab + 160) in HB160 by lia.
  (* 0x815b0 beqz s2 *)
  step.
  destruct (Z.eq_dec w 0) as [E0|N0].
  - (* left = 0: 0x81af4 li s9,0; 0x81af8 mv s7,s6; 0x81afc j 81cac; 0x81cac ld s8,56(s1) *)
    subst w. b_br.
    step. step. step. step.
    apply evt_done. unfold Q. cbv beta.
    eexists. split; [exact MU|]. split; [exact WM|].
    split; [exact HB40|]. split; [exact HB48|]. split; [exact HB152|]. split; [exact HB160|].
    left. split; [reflexivity|]. eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [first [reflexivity | (f_equal; lia) | (rewrite Z.add_0_r; reflexivity)]|].
    split; [first [reflexivity | (f_equal; lia)]|].
    first [reflexivity | (f_equal; lia)].
  - b_br.
    apply evt_done. unfold Q. cbv beta.
    eexists. split; [exact MU|]. split; [exact WM|].
    split; [exact HB40|]. split; [exact HB48|]. split; [exact HB152|]. split; [exact HB160|].
    right. split; [exact N0 | reflexivity].
Qed.

(* ---- the mode byte 0x815b4 .. 0x815e8 (no store): T02, the check 0x815cc with its slow path 0x82fd0, the reload
   0x815e4 ld s8,56(s1) of the code-byte pointer (new in v1.9.0) and the parity test (even -> P3 at 0x81cb0,
   odd -> the catalogue arm 0x815ec) ---- *)
Lemma b_mode_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab q w K v56 : Z) (bm km : byte),
    s1 = Z_to_bv 64 Ab -> s2 = Z_to_bv 64 w -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    0 <= Ab -> Ab + 64 <= 2 ^ 64 ->
    0 < q -> q + 2 < 2 ^ 64 -> 1 <= w -> w + 2 < 2 ^ 64 -> 0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [km] ->
    (bv_signed km = 0 \/ q mod 8 < bv_signed km) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [bm] ->
    ro_cells rsegs m (Ab + 56) [C8 (Z_to_bv 64 v56)] ->
    evt rsegs
      (fun ms' =>
         (bv_unsigned bm mod 2 = 0 /\
          exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81cb0) fc None m (seg_rom rsegs) /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = Z_to_bv 64 Ab /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
            getr R 23 = Z_to_bv 64 (q + 1) /\ getr R 25 = Z_to_bv 64 (w - 1) /\ getr R 24 = Z_to_bv 64 v56)
         \/
         (bv_unsigned bm mod 2 = 1 /\
          exists x0 x1 : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab) x0 x1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) s3 s4 s5
                          (zxb bm) (Z_to_bv 64 (q + 1)) (Z_to_bv 64 v56) (Z_to_bv 64 (w - 1)) s10 s11
                          t3 t4 t5 t6)
                     F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab q w K v56 bm km -> -> -> -> HAb0 HAb Hq0 Hq Hw0 Hw HK Hsh HRk HOKk HRm RO56.
  pose proof (rc_byte_signed km) as KRk.
  pose proof (bv_unsigned_in_range 8 bm) as HBM. unfold bv_modulus in HBM. cbn in HBM.
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  (* 0x815b4 addi s7,s6,1; 0x815b8 li a0,1; 0x815bc bltu a0,s7 (T02) *)
  step. step. step. b_br.
  (* 0x815c4 srli a0,s6,0x3; 0x815c8 add a0,a0,s10; 0x815cc lb a0,0(a0); 0x815d0 beqz a0 *)
  step. rewrite (MState.unsigned_lit q) by lia. rewrite rc_shr3.
  step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed km)) by lia.
  enough (KC : forall (x0 x1 : word),
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab) x0 x1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) s3 s4 s5
                         (Z_to_bv 64 q) (Z_to_bv 64 (q + 1)) s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x815d8) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed km) 0) as [E|E]; cbn [negb]; [apply KC|].
    (* 0x815d4 j 82fd0; 0x82fd0 andi a1,s6,7; 0x82fd4 bge a1,a0 (not taken) *)
    step. step. rewrite (MState.unsigned_lit q) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed (q mod 8) (bv_signed km)) by lia.
    replace (q mod 8 <? bv_signed km) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [negb].
    (* 0x82fd8 j 815d8 *)
    step. apply KC. }
  intros x0 x1.
  (* 0x815d8 lbu s6,0(s6); 0x815dc andi a0,s6,1; 0x815e0 addi s9,s2,-1; 0x815e4 ld s8,56(s1); 0x815e8 beqz a0 *)
  step. step. step.
  unfold zxb at 1. rewrite (MState.unsigned_lit (bv_unsigned bm)) by lia. rewrite b_land1 by lia.
  step.
  step.
  destruct (Z.eq_dec (bv_unsigned bm mod 2) 0) as [Ev|Od].
  - rewrite Ev. b_br.
    apply evt_done. unfold Q. cbv beta. left. split; [exact Ev|].
    eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [first [reflexivity | (f_equal; lia)]|].
    split; [first [reflexivity | (f_equal; lia)]|].
    first [reflexivity | (f_equal; lia)].
  - b_br.
    apply evt_done. unfold Q. cbv beta. right. split; [lia|].
    do 2 eexists.
    replace (Z_to_bv 64 (w + -1)) with (Z_to_bv 64 (w - 1)) by (f_equal; lia).
    reflexivity.
Qed.

(* ---- the catalogue arm 0x815ec .. 0x815f8: the count cell's shadow byte S(fr) + 332 = 00 (which makes its 8
   bytes usable), the cell zeroed, and reac_box_catalogue(c) by its contract, returning to 0x815fc with
   a0 = BOX_CATALOGUE and [c] = 11 ---- *)
Lemma b_cat_evt : RBC.reac_box_catalogue_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Sh c spv : Z) (sh1 cs : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s4 = Z_to_bv 64 c ->
    6283264 <= c -> c mod 8 = 0 -> c + 8 <= 140737488355328 ->
    6283264 <= spv - 16 -> spv <= 140737488355328 -> (c + 8 <= spv - 16 \/ spv <= c) ->
    (c + 8 <= Sh + 332 \/ Sh + 333 <= c) -> (spv <= Sh \/ Sh + 333 <= spv - 16) ->
    shadow_addr c = Sh + 332 ->
    (forall i, 0 <= i < 8 -> app_mem (c + i)) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    length sh1 = 1%nat -> length cs = 8%nat ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m c [CB 8 cs] ->
    stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x815fc) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 RBC.BOX_CATALOGUE /\
         munch [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         shadow_rw m' /\ stk rsegs m' (spv - 16) spv /\
         bytes_at rsegs m' c (le8 (Z_to_bv 64 11)) /\ bytes_at rsegs m' (Sh + 332) [Z_to_bv 8 0])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros CATC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh c spv sh1 cs -> -> -> Hc Hc8 Hce Hsp0 Hspe Hsep Hdjc Hdjw Hshc Happc Happw Hsh1 Hcsl CHsh CHc
    ST HAC HSW.
  unfold RBC.reac_box_catalogue_contract, RBC.REAC_BOX_CATALOGUE, RBC.REAC_BOX_CATALOGUE_FRAME,
    RBC.BOX_CATALOGUE in CATC |- *.
  pose proof (rw_cells_bound rsegs m (Sh + 332) _ CHsh) as HBsh.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HBsh.
  pose proof (rw_cells_bound rsegs m c _ CHc) as HBc.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HBc.
  pose proof (munch_refl [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x815ec sb zero,332(s3); 0x815f0 sd zero,0(s4); 0x815f4 mv a0,s4.  The engine keeps the write set in MU / WM
     and the two cells in CHsh / CHc (mem_after_store). *)
  b_sb. step. step.
  lazymatch type of MU with munch _ _ ?mm => set (mc := mm) in * end.
  rename MU into MU1. rename WM into WM1.
  assert (HZsh1 : bytes_at rsegs mc (Sh + 332) [Z_to_bv 8 0]).
  { destruct CHsh as ((_ & HB) & _). cbn [cells_bytes cbytes] in HB. rewrite ?app_nil_r in HB. exact HB. }
  assert (HZc1 : bytes_at rsegs mc c (repeat (Z_to_bv 8 0) 8)).
  { destruct CHc as ((_ & HB) & _). cbn [cells_bytes cbytes] in HB. rewrite ?app_nil_r in HB.
    replace (repeat (Z_to_bv 8 0) 8) with (le8 (Z_to_bv 64 0)) by (vm_compute; reflexivity). exact HB. }
  assert (Happc' : forall x, c <= x < c + 8 -> app_mem x).
  { intros x Hx. replace x with (c + (x - c)) by lia. apply Happc. lia. }
  assert (Hin332 : in_shadow (Sh + 332)).
  { rewrite <- Hshc. apply shadow_of_app.
    replace c with (c + 0) by lia. apply Happc. lia. }
  assert (HShb : 2147450880 <= Sh + 332 < 17592186044416 + 2147450880).
  { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin332. lia. }
  assert (Hshrng : forall a, in_shadow a -> 2147450880 <= a < 17592186044416 + 2147450880).
  { intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
  assert (Hcrng : c + 8 <= 2147450880 \/ 17592186044416 + 2147450880 <= c).
  { pose proof (Happc' c ltac:(lia)) as H1. pose proof (Happc' (c + 7) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (Hwrng : spv <= 2147450880 \/ 17592186044416 + 2147450880 <= spv - 16).
  { pose proof (Happw (spv - 16) ltac:(lia)) as H1. pose proof (Happw (spv - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  assert (HAC1 : asan_cells mc).
  { apply (asan_cells_kept _ m mc HAC MU1). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : shadow_rw mc).
  { apply (b_shadow_rw _ m mc HSW MU1 WM1). intros a Ha.
    destruct (Z.eq_dec a (Sh + 332)) as [->|Hne].
    - right. apply (b_ba_rd mc (Sh + 332) [Z_to_bv 8 0] _ HZsh1). cbn [length]. lia.
    - left. cbn [outside]. pose proof (Hshrng a Ha).
      split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  (* the engine transported the callee window's stk to mc with the stores *)
  pose proof ST as ST1.
  assert (HADc : addressable mc c 8).
  { apply (b_addr_z mc c 1 8); [reflexivity | lia | exact Hc8 | unfold APPMEM_END; lia
      | intros i Hi; apply Happc; lia |].
    rewrite Hshc. cbn [repeat]. exact HZsh1. }
  assert (HWRc : wr_at rsegs mc c 8).
  { destruct CHc as (_ & Hw). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hw. exact Hw. }
  (* 0x815f8 jal reac_box_catalogue (RBC.REAC_BOX_CATALOGUE) *)
  step.
  eapply evt_cut.
  { eapply CATC with (c := c) (lo := spv - 16).
    - reflexivity.
    - rewrite (MState.unsigned_lit spv) by lia. exact ST1.
    - rewrite (MState.unsigned_lit spv) by lia. lia.
    - exact HAC1.
    - exact HSW1.
    - rewrite (MState.unsigned_lit spv) by lia.
      intros x [Hx | [Hx | Hx]].
      + cbn [outside]. unfold GOT_CELL_K in Hx. repeat split; (exact I || lia).
      + cbn [outside]. unfold CELL_K in Hx. repeat split; (exact I || lia).
      + cbn [outside]. pose proof (Hshrng x Hx).
        split; [lia|]. split; [lia | exact I].
    - rewrite (MState.unsigned_lit spv) by lia.
      right. split; [exact Hc8|]. split; [exact HWRc|]. split; [lia | exact HADc]. }
  intros ms' PO.
  destruct PO as (a1' & a2' & m' & E & MU2 & WM2 & MI2 & ST2 & HZ).
  subst ms'.
  rewrite (MState.unsigned_lit spv) in MU2, ST2 by lia.
  rewrite (proj2 (Z.eqb_neq c 0) ltac:(lia)) in HZ.
  replace (ret_pc (Z_to_bv 64 0x815fc)) with (Z_to_bv 64 0x815fc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (Hsub : sub_fp [(spv - 16, spv); (c, c + 8)]
                   [(Sh + 332, Sh + 333); (c, c + 8); (spv - 16, spv)]).
  { intros x Hx. cbn [outside] in Hx |- *. rs_hide_all. tauto. }
  pose proof (munch_trans _ m mc m' MU1 (munch_weaken _ _ mc m' Hsub MU2)) as MUf.
  assert (HSW2 : shadow_rw m').
  { apply (b_shadow_rw _ mc m' HSW1 MU2 WM2). intros a Ha. left. cbn [outside].
    pose proof (Hshrng a Ha). split; [lia|]. split; [lia | exact I]. }
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m mc m' WM1 WM2)|].
  split; [exact HSW2|]. split; [exact ST2|]. split; [exact HZ|].
  apply (bytes_at_transport rsegs [(spv - 16, spv); (c, c + 8)] mc m' _ _ HZsh1 MU2).
  cbn [length disjoint_from].
  split; [lia|]. split; [lia | exact I].
Qed.

(* ---- the cut level.  A later import shadows the Lib engine's getr with YK11's (used by FRA), as in R2.v. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module KNC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_c.
Open Scope Z_scope.

(* The kind-name table [KIND_NAME, KIND_NAME + 112) is one of the registered globals frame_AG (FrameAPI.v:
   (KNC.KIND_NAME, 112)), so FRA's per-byte addressability of those globals gives it as one range. *)
Lemma b_kn_addr : forall m, (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  addressable m KNC.KIND_NAME 112.
Proof.
  intros m H.
  split; [unfold KNC.KIND_NAME; lia|]. split; [lia|]. split; [unfold KNC.KIND_NAME, APPMEM_END; lia|].
  intros i Hi.
  assert (Hg : in_globals AF.frame_AG (KNC.KIND_NAME + i)).
  { exists KNC.KIND_NAME, 112. split; [|lia].
    unfold AF.frame_AG, KNC.KIND_NAME. cbn [In]. repeat (first [left; reflexivity | right]). }
  destruct (H _ Hg) as (_ & _ & _ & Hb). specialize (Hb 0 ltac:(lia)). rewrite Z.add_0_r in Hb. exact Hb.
Qed.

(* ---- model helpers (image A's lib/A/Prog/Seg/R1.v, image-B registers) ---- *)

(* firstn of OUR grows by one model byte per turn. *)
Lemma b_our_step : forall inp t, (t < 6)%nat ->
  firstn (S t) (OUR inp) = firstn t (OUR inp) ++ [RcIdentModel.nthb inp t].
Proof. intros inp t Ht. unfold OUR. cbn [seq map]. do 6 (destruct t as [|t]; [reflexivity|]). lia. Qed.

Lemma b_nth_past : forall inp t, (length inp <= t)%nat -> RcIdentModel.nthb inp t = Z_to_bv 8 0.
Proof. intros inp t H. unfold RcIdentModel.nthb, RcIdentModel.zb. apply nth_overflow. exact H. Qed.

(* A one-byte read of a known byte list. *)
Lemma b_rd_at : forall m a bs i (b : byte), bytes_at rsegs m a bs -> 0 <= i ->
  nth_error bs (Z.to_nat i) = Some b -> ov_read_bytes rsegs m (wa (a + i)) 1 = Some [b].
Proof.
  intros m a bs i b H Hi Hn.
  assert (Hlt : (Z.to_nat i < length bs)%nat) by (apply nth_error_Some; intros E; rewrite E in Hn; discriminate).
  pose proof (bytes_at_ov_read rsegs m a bs (Z.to_nat i) 1 H ltac:(lia)) as HH.
  rewrite Z2Nat.id in HH by lia. rewrite HH. f_equal.
  assert (Hb : nth_error (skipn (Z.to_nat i) bs) 0 = Some b)
    by (rewrite nth_error_skipn, Nat.add_0_r; exact Hn).
  destruct (skipn (Z.to_nat i) bs) as [|b' rest]; cbn in Hb; [discriminate|].
  injection Hb as <-. reflexivity.
Qed.

(* our[] after one turn: the byte v landed at our + t, the rest of the six bytes kept. *)
Lemma b_our_keep : forall m m' ou t (pre junk : list byte) (v : byte),
  bytes_at rsegs m ou (pre ++ junk) -> length pre = Z.to_nat t -> 0 <= t -> (1 <= length junk)%nat ->
  LF.munch [(ou + t, ou + t + 1)] m m' -> bytes_at rsegs m' (ou + t) [v] ->
  bytes_at rsegs m' ou ((pre ++ [v]) ++ tl junk).
Proof.
  intros m m' ou t pre junk v H Hp Ht Hj MU HV.
  pose proof H as Hb. apply bytes_at_bound in Hb. rewrite app_length in Hb.
  apply bytes_at_app in H. destruct H as (H1 & H2).
  rewrite Hp, Z2Nat.id in H2 by lia.
  destruct junk as [|b0 junk']; [cbn in Hj; lia|].
  change (b0 :: junk') with ([b0] ++ junk') in H2.
  apply bytes_at_app in H2. destruct H2 as (H2a & H2b). cbn [length Z.of_nat] in H2b.
  apply bytes_at_app. split.
  - apply bytes_at_app. split.
    + apply (bytes_at_transport rsegs [(ou + t, ou + t + 1)] m m' ou pre H1 MU).
      rewrite Hp, Z2Nat.id by lia. cbn [disjoint_from]. split; [left; lia | exact I].
    + rewrite Hp, Z2Nat.id by lia. exact HV.
  - assert (Hlen2 : Z.of_nat (length (pre ++ [v])) = t + 1)
      by (rewrite length_app, Hp; cbn [length]; lia).
    rewrite Hlen2. cbn [tl]. replace (ou + (t + 1)) with (ou + t + 1) by lia.
    apply (bytes_at_transport rsegs [(ou + t, ou + t + 1)] m m' (ou + t + 1) junk' H2b MU).
    cbn [disjoint_from]. split; [right; lia | exact I].
Qed.

(* Every image byte is below GT; ro_agree across a run that writes no image byte. *)
Lemma b_segs_lo : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < 6283264.
Proof.
  intros x seg H.
  assert (HB : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB.
  destruct (KindBGlue.kb_find_segment rsegs x 1 seg H) as (Hin & Hlo & Hhi).
  pose proof (HB seg Hin) as Hb. apply Z.leb_le in Hb.
  pose proof (N2Z.is_nonneg (seg_base seg)). lia.
Qed.

Lemma b_ro_keep : forall (W : list LF.ivl) m m', ro_agree rsegs m -> LF.munch W m m' ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) -> ro_agree rsegs m'.
Proof.
  intros W m m' HRO MU HW a Hro.
  unfold mrd. rewrite (MU a); [exact (HRO a Hro)|].
  unfold ro_addr in Hro. destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate].
  apply HW. exact (b_segs_lo _ s E).
Qed.

(* The instrumented globals lie below GT; their shadow bytes are the first 785408 bytes of the low shadow. *)
Lemma b_ag_ok : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) b_ag_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma b_sa_lo : forall a, 0 <= a < 0x5fe000 -> ASAN_K <= shadow_addr a < ASAN_K + 785408.
Proof. intros a Ha. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* addressable survives a run keeping each byte's shadow byte outside the write set. *)
Lemma b_addr_keep : forall W m m' p n, addressable m p n -> LF.munch W m m' ->
  (forall i, 0 <= i < n -> LF.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

(* lia on arithmetic goals only: a failing lia on any other goal tries to refute the whole context. *)
Ltac zlia :=
  lazymatch goal with
  | |- (_ <= _)%Z => lia | |- (_ < _)%Z => lia | |- (_ >= _)%Z => lia | |- (_ > _)%Z => lia
  | |- (_ <= _ <= _)%Z => lia | |- (_ <= _ < _)%Z => lia | |- (_ < _ <= _)%Z => lia | |- (_ < _ < _)%Z => lia
  | |- (_ = _)%Z => lia | |- (_ <> _)%Z => lia
  | |- (_ \/ _) => lia
  end.
Ltac weq := lazymatch goal with |- Z_to_bv _ _ = Z_to_bv _ _ => f_equal; lia end.

(* One register equality of a turn's post state: kept, a carried literal, or an arithmetic restatement. *)
Ltac b_kreg := first [ reflexivity | (symmetry; assumption) ].

(* The start register map of a run, in the engine's concrete mkR form (image-B twin of r2_mkR_of). *)
Lemma b_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A write set above the image misses every runtime cell. *)
Lemma b_dj_hi : forall (W : list LF.ivl) a n, a + n <= 6283264 ->
  (forall lo hi, In (lo, hi) W -> 6283264 <= lo) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n Ha HW; cbn [disjoint_from]; [exact I|].
  split.
  - pose proof (HW lo hi (or_introl eq_refl)). lia.
  - apply IH; [exact Ha|]. intros lo' hi' Hin. exact (HW lo' hi' (or_intror Hin)).
Qed.

Lemma b_rtdj : forall (W : list LF.ivl), (forall lo hi, In (lo, hi) W -> 6283264 <= lo) ->
  AsanRTInv.rt_disjoint W.
Proof.
  intros W HW. unfold AsanRTInv.rt_disjoint.
  repeat split; apply b_dj_hi; try exact HW;
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN; lia.
Qed.

(* A spill cell [A + off, A + off + 8) survives a run that misses it. *)
Lemma b_spill_keep : forall (W : list LF.ivl) regs regs' mem mem' off v A,
  spill regs mem off v -> rg regs 9 A -> off <= A < 2 ^ 64 -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> LF.munch W mem mem' ->
  (forall x, A + off <= x < A + off + 8 -> LF.outside W x) -> spill regs' mem' off v.
Proof.
  intros W regs regs' mem mem' off v A (A1 & HA1 & Hq) Hr9 HA Hoff HAe E9 MU HW.
  assert (HA1e : A1 = A).
  { pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    change (Z.of_nat 8) with 8 in Hb.
    pose proof (rg_eq64 regs 9 A1 A HA1 Hr9) as Hm.
    change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
  subst A1. exists A. split; [unfold rg in *; rewrite E9; exact Hr9|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply HW. cbn in Hx. lia.
Qed.

Lemma b_rw_C8 : forall m a v, q64 m a v -> wr_at rsegs m a 8 -> rw_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v Hq Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hq.
  - exact Hw.
Qed.

(* A spill fact's word sits at A + off for the A of register 9. *)
Lemma b_spill_q64 : forall regs mem off v A,
  spill regs mem off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  q64 mem (A + off) v.
Proof.
  intros regs mem off v A (A1 & HA1 & Hq) Hr9 HA Hoff HAe.
  assert (HA1e : A1 = A).
  { pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    change (Z.of_nat 8) with 8 in Hb.
    pose proof (rg_eq64 regs 9 A1 A HA1 Hr9) as Hm.
    change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

(* A spilled word read by `ld`: its 8 bytes as one read-only cell (R2.v's r2_ro8). *)
Lemma b_ro8 : forall m a v, q64 m a v -> ro_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

(* The left <> 0 turn from either start: the head (b_hd_ld_evt) or the body cut with the bumped cursor (b_ld_evt). *)
Lemma b_any_ld_evt :
  forall (pc0 : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt d q v K : Z) (b kq : byte),
    (pc0 = 0x81548 \/ (pc0 = 0x81550 /\ a3 = Z_to_bv 64 (q + 1))) ->
    a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 d ->
    s2 = Z_to_bv 64 v -> s6 = Z_to_bv 64 q -> s10 = Z_to_bv 64 K ->
    1 <= cnt <= 6 -> 0 <= d -> d + 1 < 2 ^ 64 -> 1 <= q -> q + 2 < 2 ^ 64 -> 1 <= v -> v + 1 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (x4 x5 : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 1) (Z_to_bv 64 (d + 1))
                       (Z_to_bv 64 (q + 1)) x4 x5 a6 a7 (Z_to_bv 64 (v - 1)) s3 s4 s5
                       (Z_to_bv 64 (q + 1)) s7 s8 s9 (Z_to_bv 64 K) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if cnt =? 1 then 0x815a0 else 0x81548)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' d [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros pc0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cnt d q v K b kq Hpc. intros.
  destruct Hpc as [-> | (-> & Ha3)].
  - eapply b_hd_ld_evt; eassumption.
  - eapply b_ld_evt; eassumption.
Qed.

(* our[]'s six bytes share the shadow byte S(fr) + 328. *)
Lemma b_sh_our : forall fr i, fr mod 8 = 0 -> 0 <= i < 8 -> shadow_addr (fr + 2624 + i) = Sfr fr + 328.
Proof. intros fr i H Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Section A5.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CATC : RBC.reac_box_catalogue_contract.

(* FRAH survives a run whose write set W (classified by HWcl) lies in the frame body, the frame's FRAME_SHADOW (392) shadow bytes,
   the callee window [sp - 16, sp) or the spill cells [A + 40, A + 168), leaving every byte it wrote readable, with
   the heap invariant / stklo kept by the caller (real arm a_laws_store, side arm a_fs_ok_store_AH).  The run may
   write one shadow byte (the catalogue cell's), so RT is kept by RT_meta_write (shadow_rw mem' from the caller). *)
Lemma b_frah : forall g fr regs regs' mem mem' md sel hdr (W : list LF.ivl),
  FRAH B APIf ra g fr [] regs mem md sel hdr ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> AsanRTInv.rt_disjoint W -> shadow_rw mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W x ->
     (fr + 24 <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
     (AC.aspZ regs - 16 <= x < AC.aspZ regs) \/
     (bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 168)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W x -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRAH B APIf ra g fr [] regs' mem' md sel hdr.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr regs regs' mem mem' md sel hdr W HF MU WM HD HSWm HAH' HSTK HWcl HRD E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HF as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hsel0 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAo & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive &
    Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  rewrite HbvA, Haspz in HWcl.
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr)
        as [HGTb _ _ HFapp].
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  unfold AC.GT in HGT. unfold HIGHMEM_BEG, APPMEM_END, LOWMEM_END in Hhigh, HAPP.
  assert (Hfrm8 : fr mod 8 = 0)
    by (pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
        replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
  assert (Hfr0 : 0 <= fr) by (pose proof (Happ' fr ltac:(lia)) as X;
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
  assert (HSfrlo : 2147450880 <= Sfr fr)
    by (unfold Sfr, shadow_addr, ASAN_K; pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)); lia).
  (* the frame is apart from the callee window [sp - 16, sp): real arm sp = fr, side arm the frame is in the
     FakeStack below stklo <= S - SLOT_STACK < sp - 16 *)
  assert (Hplace : forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
            FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { intros FS Hw HFSr.
    destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FS HAH Hw HFSr) as [_ Hend _ _]. exact Hend. }
  assert (Hwapart : fr + FRAME_BYTES <= sp - 16 \/ sp <= fr).
  { destruct Hloc as [[_ [Hspfr _]] | [_ [_ [Hfs _]]]].
    - right. lia.
    - left. destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (Hplace FSb Hw HFSr) as Hend. lia. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ' _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (Hshfr : forall b, 0 <= b -> ~ (fr <= b < fr + FRAME_BYTES) -> ~ (Sfr fr <= shadow_addr b < Sfr fr + FRAME_SHADOW)).
  { intros b Hb0 Hnb Hin. apply Hnb. unfold Sfr, shadow_addr in Hin.
    revert Hin Hfrm8 Hb0 Hfr0 HFBv HFSv. clear. intros. Z.div_mod_to_equations. lia. }
  assert (Houtapp : forall x, app_mem x -> ~ (fr <= x < fr + FRAME_BYTES) -> ~ (sp - 16 <= x < sp) ->
            ~ (A + 40 <= x < A + 168) -> LF.outside W x).
  { intros x Hap Hnf Hnw Hns. destruct (b_out_dec W x) as [Ho|Hno]; [exact Ho | exfalso].
    assert (Hx64 : 0 <= x < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia).
    destruct (HWcl x Hx64 Hno) as [H|[H|[H|H]]]; try lia.
    exact (app_not_shadow x Hap (HshIS x ltac:(lia))). }
  (* the frame header [fr, fr + 24) is below the frame-body write region [fr + 24, fr + FRAME_BYTES), so outside W *)
  assert (Houthdr : forall x, fr <= x < fr + 24 -> LF.outside W x).
  { intros x Hx. destruct (b_out_dec W x) as [Ho|Hno]; [exact Ho | exfalso].
    assert (Hx64 : 0 <= x < 2 ^ 64)
      by (pose proof (Happ' x ltac:(lia)) as X; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
    destruct (HWcl x Hx64 Hno) as [H|[H|[H|H]]]; try lia.
    exact (app_not_shadow x (Happ' x ltac:(lia)) (HshIS x H)). }
  assert (KBmb : forall sg x, app_mem x -> ~ (fr <= x < fr + FRAME_BYTES) -> ~ (sp - 16 <= x < sp) ->
            ~ (A + 40 <= x < A + 168) -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hap Hnf Hnw Hns.
    assert (Hx64 : 0 <= x < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia).
    unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by exact Hx64. exact (Houtapp x Hap Hnf Hnw Hns). }
  assert (KBlo : forall sg x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. apply KBmb; try (unfold app_mem, LOWMEM_END; left; lia); lia. }
  assert (HRO : ro_agree rsegs mem').
  { apply (b_ro_keep W mem mem' Hro MU). intros x Hx.
    destruct (b_out_dec W x) as [Ho|Hno]; [exact Ho | exfalso].
    destruct (HWcl x ltac:(lia) Hno) as [H|[H|[H|H]]]; lia. }
  assert (HshR : forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b)
    by (intros a Ha; exact (proj2 (HSWm a Ha))).
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= 17592186044416 + 2147450880).
  { pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as Hin.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin. lia. }
  assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
  { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
    { split; [lia|]. split; [lia|]. intros a Ha. apply HSWm. exact (HshIS a Ha). }
    destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
    exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
  exists A, sp.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia|].
        rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia|].
        rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [Ei|[]]; injection Ei as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [Ei|[]]; injection Ei as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hsel0|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply Houtapp; [unfold app_mem, HIGHMEM_BEG, APPMEM_END, LOWMEM_END; right; lia | lia | lia | lia]. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hfsrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0'|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo; [exact (Hw k Hk) | unfold AC.as_tp, AC.ASYMS; cbn; lia
          | unfold AC.as_tp, AC.ASYMS; cbn; lia].
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo; [exact (Hw k Hk) | unfold AC.as_tp, AC.ASYMS; cbn; lia
            | unfold AC.as_tp, AC.ASYMS; cbn; lia].
        * (* the FakeStack frame record (push 5b): its tp word is in the image, its class-6 flag byte and its
             slot's last word are app bytes below the frame, all outside W *)
          destruct Hfsrec as (FS0 & j0 & Htp0 & HFSr0 & Hj0 & Hfreq & Hflag0 & Htail0).
          destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FS0 HAH Htp0 HFSr0)
            as [HGTb0 Hend0 _ Happ0].
          assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
          assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
          assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
          assert (Hfl : SMC.fs_flag FS0 6 j0 = FS0 + 36352 + j0) by (unfold SMC.fs_flag; cbn; lia).
          assert (Hfrv : fr = FS0 + 6328320 + j0 * 4096)
            by (rewrite Hfreq; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
          rewrite HM6 in Hj0.
          pose proof (Hfsb FS0 Htp0 HFSr0) as HFSfr.
          exists FS0, j0.
          split.
          { intros k Hk. rewrite KBlo; [exact (Htp0 k Hk) | unfold AC.as_tp, AC.ASYMS; cbn; lia
              | unfold AC.as_tp, AC.ASYMS; cbn; lia]. }
          split; [exact HFSr0|]. split; [rewrite HM6; exact Hj0|]. split; [exact Hfreq|].
          split.
          { eapply fl_bytes; [exact Hflag0 | exact MU |].
            cbn [length]. intros x Hx. apply Houtapp;
              [apply Happ0; lia | lia | lia | lia]. }
          { eapply fl_bytes; [exact Htail0 | exact MU |].
            rewrite length_le8. intros x Hx. apply Houtapp;
              [apply Happ0; rewrite HB6 in *; lia | rewrite HB6 in *; lia
               | rewrite HB6 in *; lia | rewrite HB6 in *; lia]. } }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply Houthdr; lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply Houthdr; lia. }
  split; [exact Hshnew|].
  split.
  { destruct Hwin as (Hw0 & Hw1 & Hwv). split; [exact Hw0|]. split; [exact Hw1|].
    intros x Hx. destruct (Hwv x Hx) as (Hwx & b & Hb). split; [exact (WM (wa x) Hwx)|].
    destruct (b_out_dec W x) as [Ho|Hno].
    - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
    - exact (HRD x ltac:(lia) Hno). }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
    apply Houtapp; [unfold app_mem, HIGHMEM_BEG, APPMEM_END, LOWMEM_END; right; lia | lia | lia | lia]. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split.
  { intros a Hin. pose proof (b_ag_lo a Hin) as Halo.
    apply (b_addr_keep W mem mem' a 1 (HAG a Hin) MU). intros i Hi.
    replace (a + i) with a by lia.
    destruct (b_out_dec W (shadow_addr a)) as [Ho|Hno]; [exact Ho | exfalso].
    assert (Haapp : app_mem a) by (unfold app_mem, LOWMEM_END; left; lia).
    assert (Hinsh : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Haapp).
    pose proof (b_sa_lo a Halo) as Hsa. unfold ASAN_K in Hsa.
    assert (Hsh64 : 0 <= shadow_addr a < 2 ^ 64)
      by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hinsh; lia).
    destruct (HWcl (shadow_addr a) Hsh64 Hno) as [H|[H|[H|H]]].
    - exact (app_not_shadow (shadow_addr a) (Happ' (shadow_addr a) ltac:(lia)) Hinsh).
    - exact (Hshfr a ltac:(lia) ltac:(lia) H).
    - exact (app_not_shadow (shadow_addr a)
        ltac:(unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia) Hinsh).
    - exact (app_not_shadow (shadow_addr a)
        ltac:(unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia) Hinsh). }
  (* push-5c window addressability: window bytes outside the frame keep their shadow byte (only the frame's shadow
     is written), so they stay addressable *)
  split.
  { intros a Ha Hnf. apply (addr1_munch W mem mem' a MU); [| exact (HWAo a Ha Hnf)].
    destruct (b_out_dec W (shadow_addr a)) as [Ho|Hno]; [exact Ho | exfalso].
    assert (Haapp : app_mem a) by (unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia).
    assert (Hinsh : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Haapp).
    assert (Ha0 : 0 <= a) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG in Haapp; lia).
    assert (Hsh64 : 0 <= shadow_addr a < 2 ^ 64)
      by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hinsh; lia).
    destruct (HWcl (shadow_addr a) Hsh64 Hno) as [H|[H|[H|H]]].
    - exact (app_not_shadow (shadow_addr a) (Happ' (shadow_addr a) ltac:(lia)) Hinsh).
    - exact (Hshfr a Ha0 Hnf H).
    - exact (app_not_shadow (shadow_addr a)
        ltac:(unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia) Hinsh).
    - exact (app_not_shadow (shadow_addr a)
        ltac:(unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia) Hinsh). }
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* FRAH's input facts: for n > 0 the input block is a live block of g_H g, so (a_laws_blocks) app memory below
     stklo <= S - SLOT_STACK < sp - 16 <= A and outside FS, so apart from the frame on both arms (real arm: frame
     bytes at or above stklo; side arm: frame in FS) and from W's app parts; its shadow bytes are apart from the
     frame's FRAME_SHADOW (fr mod 32 = 0) and from W's app parts *)
  assert (Hinap : forall x, g_p g <= x < g_p g + g_n g ->
            app_mem x /\ ~ (fr <= x < fr + FRAME_BYTES) /\ x < sp - 16 /\ 0 <= x).
  { intros x Hx. destruct (Hinblk ltac:(lia)) as (Hin & _).
    destruct (lw_blocks (APIf rc) ([] ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror Hin))) as [_ _ Hend _ Hb].
    destruct (Hb x Hx) as (Hxa & _ & _ & _ & Hnfs).
    split; [exact Hxa|]. split.
    - intros Hfr. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
      + destruct (Hreal x Hfr) as (Hlo & _). lia.
      + exact (Hnfs (Hfs x Hfr)).
    - split; [lia|]. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa. lia. }
  split.
  { eapply fl_bytes; [exact Hinb | exact MU |]. intros x Hx.
    destruct (Hinap x ltac:(unfold g_n, nlen; lia)) as (Hxa & Hxf & Hxs & _).
    apply Houtapp; [exact Hxa | exact Hxf | lia | lia]. }
  intros Hn. destruct (Hinblk Hn) as (Hin & HADp). split; [exact Hin|].
  apply (b_addr_keep W mem mem' (g_p g) (g_n g) HADp MU). intros i Hi.
  destruct (Hinap (g_p g + i) ltac:(lia)) as (Hxa & Hxf & _ & Hx0).
  assert (Hinsh : in_shadow (shadow_addr (g_p g + i))) by (apply shadow_of_app; exact Hxa).
  destruct (b_out_dec W (shadow_addr (g_p g + i))) as [Ho|Hno]; [exact Ho | exfalso].
  assert (Hsh64 : 0 <= shadow_addr (g_p g + i) < 2 ^ 64)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hinsh; lia).
  destruct (HWcl _ Hsh64 Hno) as [H|[H|[H|H]]].
  - exact (app_not_shadow (shadow_addr (g_p g + i)) (Happ' (shadow_addr (g_p g + i)) ltac:(lia)) Hinsh).
  - exact (Hshfr (g_p g + i) Hx0 Hxf H).
  - exact (app_not_shadow (shadow_addr (g_p g + i))
      ltac:(unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia) Hinsh).
  - exact (app_not_shadow (shadow_addr (g_p g + i))
      ltac:(unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia) Hinsh).
Qed.

(* The word at an address determines its value (A4.v's a4_word_uniq). *)
Lemma b_word_uniq : forall m a v w, 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  word_mem rsegs m a v -> word_mem rsegs m a w -> v = w.
Proof.
  intros m a v w Hv Hw H1 H2.
  assert (D : forall k, (k < 8)%nat -> le_byte v 8 k = le_byte w 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte w 8 k)) by congruence.
    transitivity (bv_unsigned (Z_to_bv 8 (le_byte v 8 k))); [symmetry; apply KindBGlue.kb_byte_unsigned|].
    rewrite E. apply KindBGlue.kb_byte_unsigned. }
  rewrite (KindBGlue.kb_le8_digits v Hv), (KindBGlue.kb_le8_digits w Hw).
  rewrite (D 0%nat ltac:(lia)), (D 1%nat ltac:(lia)), (D 2%nat ltac:(lia)), (D 3%nat ltac:(lia)),
          (D 4%nat ltac:(lia)), (D 5%nat ltac:(lia)), (D 6%nat ltac:(lia)), (D 7%nat ltac:(lia)).
  reflexivity.
Qed.

(* The FakeStack's metadata lies in its first 36864 bytes (R2.v's r2_fs_meta_range). *)
Lemma b_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The heap invariant, the runtime's ownership and the real stack's bounds across a run of the same write class as
   b_frah's: on the real arm every written byte is a_store_ok (a frame byte or a stack byte at or above stklo, or
   the shadow byte of a frame byte), on the side arm the frame lies in the FakeStack and the write misses its
   metadata, so Tac_fs.a_fs_ok_store_AH applies. *)
Lemma b_ah : forall g fr regs mem mem' md sel hdr (W : list LF.ivl),
  FRAH B APIf ra g fr [] regs mem md sel hdr ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W x ->
     (fr + 24 <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
     (AC.aspZ regs - 16 <= x < AC.aspZ regs) \/
     (bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 168)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W x -> exists b, mbyte rsegs mem' x = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr regs mem mem' md sel hdr W HF MU WM HWcl HPres.
  destruct HF as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hsel0 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAo & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive &
    _ & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  rewrite HbvA, Haspz in HWcl.
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr)
        as [HGTb _ _ HFapp].
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  unfold AC.GT in HGT. unfold HIGHMEM_BEG, APPMEM_END, LOWMEM_END in Hhigh, HAPP.
  assert (Hfrm8 : fr mod 8 = 0)
    by (pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
        replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
  assert (Hfr0 : 0 <= fr) by (pose proof (Happ' fr ltac:(lia)) as X;
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
  assert (Hsh8 : forall k, 0 <= k < FRAME_SHADOW -> shadow_addr (fr + 8 * k) = Sfr fr + k).
  { intros k Hk. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
    by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
  destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs _]]]].
  - (* real arm *)
    assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
              ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok.
      destruct (b_out_dec W x) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
      - exfalso. apply Hnok. destruct (HWcl x Hx Hno) as [H|[H|[H|H]]].
        + right; left. pose proof (Hreal x ltac:(lia)). unfold APPMEM_END in *. lia.
        + right; right; right. exists (fr + 8 * (x - Sfr fr)).
          split; [rewrite (Hsh8 (x - Sfr fr) ltac:(lia)); lia|].
          right; left. pose proof (Hreal (fr + 8 * (x - Sfr fr)) ltac:(lia)). unfold APPMEM_END in *. lia.
        + right; left. unfold APPMEM_END. lia.
        + right; left. unfold APPMEM_END. lia. }
    destruct (lw_store (APIf rc) ([] ++ g_H g) mem mem' md HAH Hmc Hwrit)
      as [HAH' Hown Hstk' Hhi'].
    split; [exact HAH'|]. split; [exact Hown|]. split; [exact Hstk' | exact Hhi'].
  - (* side arm: the frame lies in the FakeStack *)
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
    pose proof (Hfsb FS HwFS HFSr) as HFSfr.
    destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FS HAH HwFS HFSr)
      as [HGTFS HFSend _ HFSapp].
    assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64).
    { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as H.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
    assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
              exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq (b & Hb).
      destruct (b_out_dec W q) as [Ho|Hno].
      - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
        rewrite MState.unsigned_lit by exact Hq. exact Ho.
      - exact (HPres q Hq Hno). }
    assert (Hmeta : forall q, fs_meta FS q -> LF.outside W q).
    { intros q Hq. pose proof (b_fs_meta_range FS q Hq) as Hqr.
      assert (Hqa : app_mem q) by (apply HFSapp; unfold AC.FS_SIZE in *; lia).
      destruct (b_out_dec W q) as [Ho|Hno]; [exact Ho | exfalso].
      assert (Hq64 : 0 <= q < 2 ^ 64)
        by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hqa; lia).
      destruct (HWcl q Hq64 Hno) as [H|[H|[H|H]]].
      - unfold AC.FS_SIZE in HFSend. lia.
      - exact (app_not_shadow q Hqa
          ltac:(replace q with (Sfr fr + (q - Sfr fr)) by lia;
                rewrite <- (Hsh8 (q - Sfr fr) ltac:(lia)); apply shadow_of_app; apply Happ'; lia)).
      - unfold AC.FS_SIZE in HFSend. lia.
      - unfold AC.FS_SIZE in HFSend. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (FS <= q < FS + AC.FS_SIZE) ->
              ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hnok Hnfs Hnsh.
      destruct (b_out_dec W q) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
      - exfalso. destruct (HWcl q Hq Hno) as [H|[H|[H|H]]].
        + apply Hnfs. destruct (Hfs q ltac:(lia)) as (FSq & HFSqr & Hwq & Hloq & Hhiq).
          assert (FSq = FS)
            by (exact (b_word_uniq mem (AC.as_tp AC.ASYMS) FSq FS HFSqr HFSr Hwq HwFS)).
          subst FSq. unfold AC.FS_SIZE in *. lia.
        + apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
          split; [|rewrite (Hsh8 (q - Sfr fr) ltac:(lia)); lia].
          destruct (Hfs (fr + 8 * (q - Sfr fr)) ltac:(lia)) as (FSq & HFSqr & Hwq & Hloq & Hhiq).
          assert (FSq = FS)
            by (exact (b_word_uniq mem (AC.as_tp AC.ASYMS) FSq FS HFSqr HFSr Hwq HwFS)).
          subst FSq. unfold AC.FS_SIZE in *. lia.
        + apply Hnok. right; left. unfold APPMEM_END. lia.
        + apply Hnok. right; left. unfold APPMEM_END. lia. }
    destruct (a_fs_ok_store_AH _ _ _ _ _ W ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU
                Hwrit Hpres Hmeta Hagree) as (HAH' & Hown & Hstk' & Hhi').
    split; [exact HAH'|]. split; [exact Hown|]. split; [exact Hstk' | exact Hhi'].
Qed.

(* ENT across the segment's own stores, stated on FRAH (Tac_slot's ent_store needs FRA, which the A5 / R1 cuts do
   not have: [A + 40] and [A + 48] are written only at the loop exit).  Same proof as ent_store (v1.9, with ENT's
   block-shadow conjunct): no byte of an entry block, of the image, of the stack at or above S, or of the shadow of
   those is written. *)
Lemma b_ent : forall g fr regs mem mem' md sel hdr (W : list LF.ivl),
  ENT APIf g [] mem md -> FRAH B APIf ra g fr [] regs mem md sel hdr ->
  LF.munch W mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> LF.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
     (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, AC.a_in_img a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a) ->
  ENT APIf g [] mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr regs mem mem' md sel hdr W HENT HF MU HWin Hlo Hhi Hown.
  pose proof HENT as HE0. destruct HE0 as (Hasp & _).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HF as HF0.
  destruct HF0 as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hsel0 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAo & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive &
    _ & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (Happfr : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr)
        as [HGTb _ _ HFapp].
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happfr a Ha))).
  assert (HGTfr : AC.GT <= fr) by exact (proj2 (Happfr fr ltac:(lia))).
  unfold AC.GT in HGTfr. unfold HIGHMEM_BEG in Hhigh.
  assert (Hfr8 : fr mod 8 = 0) by (pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
                                   replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
  assert (Hfr0 : 0 <= fr) by (pose proof (Happ' fr ltac:(lia)) as X;
                              unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ' _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (Hreg : forall x, 0 <= x < 2 ^ 64 -> ~ (g_S g - AF.SLOT_STACK <= x < g_S g) ->
            ~ (fr <= x < fr + FRAME_BYTES) -> ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> LF.outside W x).
  { intros x Hx H1 H2 H3. destruct (HWin x Hx) as [Ho|[Hw|[Hf|Hs]]];
      [exact Ho | contradiction | contradiction | contradiction]. }
  assert (Hshfr : forall b, 0 <= b -> ~ (fr <= b < fr + FRAME_BYTES) ->
            ~ (Sfr fr <= shadow_addr b < Sfr fr + FRAME_SHADOW)).
  { intros b Hb0 Hnb Hin. apply Hnb. unfold Sfr, shadow_addr in Hin.
    revert Hin Hfr8 Hb0 Hfr0 HFBv HFSv. clear. intros. Z.div_mod_to_equations. lia. }
  apply (ent_munch APIf g [] mem mem' md W HENT HAH MU); [| exact Hlo | exact Hhi | exact Hown].
  intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
  - destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
    destruct (lw_blocks (APIf rc) ([] ++ g_H g) mem md q k HAH
                (in_or_app _ _ _ (or_intror Hin))) as [_ Hq4 Hend _ Hall].
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    apply Hreg; [exact Hqr | lia | | ].
    + intro Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hfsrec]]]].
      * destruct (Hreal (q + i) Hf) as (Hr1 & _). lia.
      * exact (Hnfs (Hfs (q + i) Hf)).
    + intro Hs. exact (app_not_shadow (q + i) Happq (HshIS (q + i) Hs)).
  - pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
    assert (Happx : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
    apply Hreg; [lia | lia | lia |].
    intro Hs. exact (app_not_shadow x Happx (HshIS x Hs)).
  - assert (Happx : app_mem x) by (unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia).
    apply Hreg; [lia | lia | lia |].
    intro Hs. exact (app_not_shadow x Happx (HshIS x Hs)).
  - assert (Hb0 : 0 <= b)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hnb : ~ (fr <= b < fr + FRAME_BYTES))
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
    assert (Happb : app_mem b).
    { destruct Hor as [Hi|Hr];
        [pose proof (img_below_GT b Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
        |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
    pose proof (shadow_of_app b Happb) as Hsb.
    destruct (in_shadow_range (shadow_addr b) Hsb) as (R1 & R2).
    pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
    apply Hreg.
    + lia.
    + lia.
    + intro Hf. exact (app_not_shadow (shadow_addr b) (Happ' _ Hf) Hsb).
    + exact (Hshfr b Hb0 Hnb).
  - destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
    destruct (lw_blocks (APIf rc) ([] ++ g_H g) mem md q k HAH
                (in_or_app _ _ _ (or_intror Hin))) as [_ Hq4 Hend _ Hall].
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
    assert (Hb0 : 0 <= q + i) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    assert (Hnb : ~ (fr <= q + i < fr + FRAME_BYTES)).
    { intro Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs _]]]].
      - destruct (Hreal (q + i) Hf) as (Hr1 & _). lia.
      - exact (Hnfs (Hfs (q + i) Hf)). }
    pose proof (shadow_of_app (q + i) Happq) as Hsb.
    destruct (in_shadow_range (shadow_addr (q + i)) Hsb) as (R1 & R2).
    pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
    apply Hreg.
    + lia.
    + lia.
    + intro Hf. exact (app_not_shadow (shadow_addr (q + i)) (Happ' _ Hf) Hsb).
    + exact (Hshfr (q + i) Hb0 Hnb).
Qed.

(* A turn's start, at the head (SlotInv.v's Inv_B81548_at) or at the body cut (Inv_B81550_at): the turn lemma
   serves both. *)
Definition TURN_at (g : ghost) (t pc0 : Z) (c : config) : Prop :=
  CUTST0 B APIf ra g pc0 [] (fun fr sel regs m =>
    LOOPB g t fr sel regs m /\ PRA fr regs m /\
    (pc0 = 0x81548 \/ (pc0 = 0x81550 /\ t < g_n g /\ rg regs 13 (g_p g + t + 1)))) c.

(* FRA and ENT after a run of the segment write class, from FRAS / ENT before it: b_ah, b_frah, FRA_of_FRAS (the
   exit's spills [A + 48] = sel and [A + 40] = fr), sl_fra_move to the run's end model, b_ent and ent_mat. *)
Lemma b_fra_after : forall g fr regs regs' mem mem' md md' sel (W : list LF.ivl) A,
  FRAS B APIf ra g fr [] regs mem md sel -> ENT APIf g [] mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> shadow_rw mem' ->
  (forall lo hi, In (lo, hi) W -> 6283264 <= lo) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W x ->
     (fr + 24 <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
     (AC.aspZ regs - 16 <= x < AC.aspZ regs) \/
     (bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 168)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W x -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  rg regs 9 A -> q64 mem' (A + 48) sel -> q64 mem' (A + 40) fr ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr [] regs' mem' md' /\ ENT APIf g [] mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr regs regs' mem mem' md md' sel W A HFRAS HENT MU WM HSW HWlo HWcl HRD E2 E3 E4 E8 E9 E19 E26
    Hr9A Hsel Hfr Hmat.
  assert (HPres : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W x -> exists b, mbyte rsegs mem' x = Some b)
    by (intros x Hx Hno; destruct (HRD x Hx Hno) as (b & Hb); exists b; exact Hb).
  destruct (b_ah g fr regs mem mem' md sel 0x41b58ab3 W HFRAS MU WM HWcl HPres) as (HAH' & Hown & Hstk' & Hhi').
  assert (HFRAS' : FRAS B APIf ra g fr [] regs' mem' md sel).
  { unfold FRAS. exact (b_frah g fr regs regs' mem mem' md sel 0x41b58ab3 W HFRAS MU WM (b_rtdj W HWlo) HSW
      HAH' Hstk' HWcl HRD E2 E3 E4 E8 E9 E19 E26). }
  assert (HFRA : FRA B APIf ra g fr [] regs' mem' md).
  { eapply FRA_of_FRAS with (sel := sel) (A := A); [exact HFRAS' | | exact Hsel | exact Hfr].
    unfold rg in *. rewrite E9. exact Hr9A. }
  split.
  - eapply sl_fra_move; [exact HFRA | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | exact Hmat].
  - apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
    pose proof HFRAS as HF0. unfold FRAS in HF0.
    destruct HF0 as (A' & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
      Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hsel0 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
      Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAo & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive &
      _ & _).
    assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
    assert (HA64 : 0 <= A' < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
    assert (HbvA : bv_unsigned (getr regs 9) = A')
      by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
    apply (b_ent g fr regs mem mem' md sel 0x41b58ab3 W HENT HFRAS MU); [| exact Hstk' | exact Hhi' |].
    + intros x Hx. destruct (b_out_dec W x) as [Ho|Hno]; [left; exact Ho|].
      destruct (HWcl x Hx Hno) as [H|[H|[H|H]]].
      * right; right; left. lia.
      * right; right; right. exact H.
      * right; left. rewrite Haspz in H. lia.
      * right; left. rewrite HbvA in H. lia.
    + intros a Hin Ho. exact (proj2 (Hown a) Ho).
Qed.

(* The kind-name table is addressable at every FRA cut (b_kn_addr on FRA's frame_AG conjunct). *)
Lemma b_fra_kn : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md -> addressable mem KNC.KIND_NAME 112.
Proof.
  intros g fr hb regs mem md H.
  destruct H as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & _).
  apply b_kn_addr. intros a Ha. exact (HAG a Ha).
Qed.

(* One turn of the our[] loop from the head 0x81548: the fuzz_u8 arm (left > 0: our[t] = in[t] after the cursor's
   shadow check and T01) or the zero arm (left = 0: our[t] = 0), then the back edge to turn t + 1 (t < 5) or, after
   turn 5, the loop exit 0x815a0 and its tail: P3 (0x81cb0) on the left = 0 or even-mode arm, R2 (0x815fc) on the
   odd-mode arm through the catalogue call.  At P3 the cursor is s7 = p + c0, s9 = n - c0 with c0 = min n 7, and
   s8 = [A + 56] = fr + 3040: on the left = 0 arm (n <= 6) the stub 0x81af4 sets s9 = 0, s7 = s6 = p + n and P2's
   reload 0x81cac sets s8; on the even-mode arm (7 <= n) 0x815b4 / 0x815e0 set s7 = p + 7, s9 = n - 7 and 0x815e4
   sets s8. *)
Lemma b_turn_gen : forall t pc0,
  (t < 5 -> Hat B APIf ra (Inv_B81548_at B APIf ra) (t + 1)) ->
  Hcut B APIf ra (Inv_B81cb0 B APIf ra) ->
  Hcut B APIf ra (Inv_B815fc B APIf ra) ->
  Hat B APIf ra (fun g p c => TURN_at g t p c) pc0.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros t pc0 Hnext HP3 HR2 g c HInv.
  pose proof (proj1 FF) as SEGS.
  cbv beta in HInv. unfold TURN_at, CUTST0, LOOPB, PRA in HInv.
  destruct HInv as (regs & mem & md & fr & sel & Ec & HFRAS & HENT & ((Hgn & Ht & Hr24 & Hr25 &
                    L144 & L112 & L312 & L264 & H20 & H10 & H11 & H12 & H17 & H18 & H22 & H27 & L56 & L184 &
                    L176 & L208 & HAour & L96 & L120 & L240 & L232 & L224 & L64 & HINB & HIN & HOURc & H16) &
                    (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b) & Hpc0)).
  subst c.
  assert (Hc0 : c0 (g_in g) = Z.min (g_n g) 7) by reflexivity.
  assert (Hpc0' : pc0 = 0x81548 \/ (pc0 = 0x81550 /\ getr regs 13 = Z_to_bv 64 (g_p g + t + 1)))
    by (destruct Hpc0 as [E|(E & _ & H13')]; [left; exact E | right; split; [exact E | exact H13']]).
  assert (Hpc0n : pc0 = 0x81548 \/ t < g_n g)
    by (destruct Hpc0 as [E|(E & H & _)]; [left | right]; assumption).
  clear Hpc0.
  pose proof HFRAS as HF0. unfold FRAS in HF0.
  destruct HF0 as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hsel0 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAo & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive &
    _ & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  rs_hide_all.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { intros a Ha. unfold rs_hold in Hloc. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr)
        as [HGTb _ _ HFapp].
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  unfold AC.GT in HGT. unfold HIGHMEM_BEG, APPMEM_END, LOWMEM_END in Hhigh, HAPP.
  assert (Hfrm8 : fr mod 8 = 0)
    by (unfold rs_hold in Hfrm; pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
        replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
  assert (Hfr0 : 0 <= fr) by (pose proof (Happ' fr ltac:(lia)) as X;
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
  assert (Hfre : fr + FRAME_BYTES <= 140737488355328)
    by (pose proof (Happ' (fr + FRAME_BYTES - 1) ltac:(lia)) as X;
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
  assert (Hselr : 0 <= sel < 2 ^ 64) by (unfold rs_hold in Hsel0; lia).
  assert (Hfrw : forall a, fr <= a < fr + FRAME_BYTES -> writable_at rsegs mem a).
  { intros a Ha. unfold rs_hold in Hloc. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hwv). exact (proj1 (Hwv a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (lw_fs_bytes mem FSb (lw_fs_ok (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr)) as Hok1.
      exact (proj1 (Hok1 a ltac:(lia))). }
  assert (Hfrd : forall a, fr <= a < fr + FRAME_BYTES -> exists b, mrd rsegs mem (wa a) = Some b).
  { intros a Ha. unfold rs_hold in Hloc. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hwv). exact (proj2 (Hwv a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (lw_fs_bytes mem FSb (lw_fs_ok (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr)) as Hok1.
      destruct (Hok1 a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
  assert (HWRour : wr_at rsegs mem (fr + 2624) 6)
    by (split; [lia|]; split; [lia|]; intros i Hi; exact (Hfrw (fr + 2624 + i) ltac:(lia))).
  assert (HSTour : store_ok rsegs mem (wa (fr + 2624 + t)) 1 = true)
    by exact (wr_at_store_ok rsegs mem (fr + 2624) 6 t 1 HWRour ltac:(lia) ltac:(cbn; lia)).
  assert (Hlen : g_n g = Z.of_nat (length (g_in g))) by reflexivity.
  assert (Hpb : 0 < g_n g -> 4096 <= g_p g /\ g_p g + g_n g <= 140737488355328).
  { intros Hn0. destruct (HIN Hn0) as (HInH & HADp).
    destruct (lw_blocks (APIf rc) ([] ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror HInH))) as [_ H4096 _ _ _].
    destruct HADp as (_ & _ & Hpe & _). unfold APPMEM_END in Hpe. split; [exact H4096 | lia]. }
  assert (Hdj : 0 < g_n g -> g_p g + g_n g <= fr \/ fr + FRAME_BYTES <= g_p g).
  { intros Hn0. destruct (HIN Hn0) as (HInH & HADp).
    destruct (lw_blocks (APIf rc) ([] ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror HInH))) as [_ Hp4096 Hple _ Hbytes].
    destruct (Z_le_gt_dec (g_p g + g_n g) fr) as [Hle|Hgt]; [left; exact Hle|].
    destruct (Z_le_gt_dec (fr + FRAME_BYTES) (g_p g)) as [Hle2|Hgt2]; [right; exact Hle2|].
    exfalso.
    destruct (Hbytes (Z.max (g_p g) fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
    unfold rs_hold in Hloc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal (Z.max (g_p g) fr) ltac:(lia)). lia.
    - exact (Hnfs (Hfs (Z.max (g_p g) fr) ltac:(lia))). }
  rs_hide_all. apply rs_hide in HIN. apply rs_hide in Hpb. apply rs_hide in Hdj.
  unfold rg in H10, H11, H12, H16, H17, H18, H20, H22, H27, Hr25, Hr24, Hr9, Hr26.
  destruct HOURc as (junk & Hjl & HOUR).
  assert (HPRElen : length (firstn (Z.to_nat t) (OUR (g_in g))) = Z.to_nat t)
    by (rewrite length_firstn, OUR_length; lia).
  set (Wf := [(fr + 2624 + t, fr + 2624 + t + 1)]) in *.
  assert (HDJf : AsanRTInv.rt_disjoint Wf).
  { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM,
      RT_MUG, RT_AGLOB, RT_AGLOB_LEN, Wf.
    cbn [disjoint_from]. repeat split; first [exact I | lia]. }
  rewrite SEGS.
  destruct (Z.eq_dec t 5) as [E5|N5].
  - (* turn 5: the store of our[5], then the loop exit 0x815a0 and its tail *)
    subst t.
    assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
    { intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
      pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ' _ Hin)) as His.
      replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
      unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
    assert (HSfrb : 2147450880 <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= 17592186044416 + 2147450880).
    { split.
      - unfold Sfr, shadow_addr, ASAN_K. pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)). lia.
      - pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as Hin.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin. lia. }
    assert (Hshrng : forall a, in_shadow a -> 2147450880 <= a < 17592186044416 + 2147450880).
    { intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
    assert (Hfrrng : fr + FRAME_BYTES <= 2147450880 \/ 17592186044416 + 2147450880 <= fr).
    { pose proof (Happ' fr ltac:(lia)) as X1. pose proof (Happ' (fr + FRAME_BYTES - 1) ltac:(lia)) as X2.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X1, X2. lia. }
    assert (HArng : 17592186044416 + 2147450880 <= A) by lia.
    assert (Hsprng : 17592186044416 + 2147450880 <= sp - 16) by lia.
    assert (Hpstk : 0 < g_n g -> g_p g + g_n g <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { intros Hn0. destruct (HIN Hn0) as (HInH & _).
      destruct (lw_blocks (APIf rc) ([] ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror HInH))) as [_ _ Hend _ _]. exact Hend. }
    apply rs_hide in Hpstk.
    assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES))
      by (split; [lia|]; split; [lia|]; intros a Ha; split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]).
    assert (Hshc : shadow_addr (fr + 2656) = Sfr fr + 332)
      by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
    (* the cells the tail and the catalogue arm write, and the code-byte word [A + 56] the tail reads *)
    destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (A + 40) (g_S g) Hwin ltac:(lia)) as (_ & Hw1).
    destruct (stk_split rsegs mem (A + 40) (A + 56) (g_S g) Hw1 ltac:(lia)) as (Hstk40 & Hw2).
    destruct (stk_split rsegs mem (A + 56) (A + 152) (g_S g) Hw2 ltac:(lia)) as (_ & Hw3).
    destruct (stk_split rsegs mem (A + 152) (A + 168) (g_S g) Hw3 ltac:(lia)) as (Hstk152 & _).
    destruct (stk_bytes rsegs mem (A + 40) (A + 56) Hstk40 ltac:(lia)) as (xs1 & Hxs1 & Hxs1b).
    destruct (stk_bytes rsegs mem (A + 152) (A + 168) Hstk152 ltac:(lia)) as (xs2 & Hxs2 & Hxs2b).
    assert (CH1 : rw_cells rsegs mem (A + 40) [CB 16 xs1]).
    { replace 16%nat with (length xs1) by lia. apply b_rw_CB; [exact Hxs1b|].
      replace (Z.of_nat (length xs1)) with (A + 56 - (A + 40)) by lia. exact (b_wr_stk _ _ _ Hstk40). }
    assert (CH2 : rw_cells rsegs mem (A + 152) [CB 16 xs2]).
    { replace 16%nat with (length xs2) by lia. apply b_rw_CB; [exact Hxs2b|].
      replace (Z.of_nat (length xs2)) with (A + 168 - (A + 152)) by lia. exact (b_wr_stk _ _ _ Hstk152). }
    assert (Hq56 : q64 mem (A + 56) (fr + 3040))
      by exact (b_spill_q64 regs mem 56 (fr + 3040) A L56 Hr9 HA64 ltac:(lia) ltac:(lia)).
    destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (sp - 16) (g_S g) Hwin ltac:(lia)) as (_ & Hw4).
    destruct (stk_split rsegs mem (sp - 16) sp (g_S g) Hw4 ltac:(lia)) as (Hstkw & _).
    assert (Hcstk : stk rsegs mem (fr + 2656) (fr + 2664))
      by (split; [lia|]; split; [lia|]; intros a Ha;
          split; [exact (Hfrw a ltac:(lia)) | exact (Hfrd a ltac:(lia))]).
    destruct (stk_bytes rsegs mem (fr + 2656) (fr + 2664) Hcstk ltac:(lia)) as (cs & Hcsl & Hcsb).
    assert (CHc : rw_cells rsegs mem (fr + 2656) [CB 8 cs]).
    { replace 8%nat with (length cs) by lia. apply b_rw_CB; [exact Hcsb|].
      replace (Z.of_nat (length cs)) with (fr + 2664 - (fr + 2656)) by lia. exact (b_wr_stk _ _ _ Hcstk). }
    assert (HSHstk : stk rsegs mem (Sfr fr + 332) (Sfr fr + 333)).
    { split; [lia|]. split; [lia|]. intros a Ha.
      replace a with (Sfr fr + 332) by lia. exact (HSW0 (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))). }
    destruct (stk_bytes rsegs mem (Sfr fr + 332) (Sfr fr + 333) HSHstk ltac:(lia)) as (sh1 & Hsh1l & Hsh1b).
    assert (CHsh : rw_cells rsegs mem (Sfr fr + 332) [CB 1 sh1]).
    { replace 1%nat with (length sh1) by lia. apply b_rw_CB; [exact Hsh1b|].
      replace (Z.of_nat (length sh1)) with (Sfr fr + 333 - (Sfr fr + 332)) by lia.
      exact (b_wr_stk _ _ _ HSHstk). }
    set (W2p := [(fr + 2624, fr + 2630); (A + 40, A + 56); (A + 152, A + 168)]) in *.
    set (W2 := [(fr + 2624, fr + 2630); (A + 40, A + 56); (A + 152, A + 168);
                (Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)]) in *.
    eapply (sl_run_lib regs (Z_to_bv 64 pc0) mem md
      (fun R pc' mem' =>
         (pc' = Z_to_bv 64 0x81cb0 /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
          getr R 23 = Z_to_bv 64 (g_p g + c0 (g_in g)) /\ getr R 25 = Z_to_bv 64 (g_n g - c0 (g_in g)) /\
          getr R 24 = Z_to_bv 64 (fr + 3040) /\
          LF.munch W2p mem mem' /\ LF.wmono rsegs mem mem' /\
          bytes_at rsegs mem' (fr + 2624) (OUR (g_in g)) /\
          bytes_at rsegs mem' (A + 40) (le8 (Z_to_bv 64 fr)) /\
          bytes_at rsegs mem' (A + 48) (le8 (Z_to_bv 64 sel)) /\
          bytes_at rsegs mem' (A + 152) (le8 (Z_to_bv 64 (fr + 64))) /\
          bytes_at rsegs mem' (A + 160) (le8 (Z_to_bv 64 (fr + 32))))
         \/
         (pc' = Z_to_bv 64 0x815fc /\ 7 <= g_n g /\
          getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
          getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
          getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
          getr R 20 = getr regs 20 /\
          getr R 10 = Z_to_bv 64 CAT /\ getr R 22 = Z_to_bv 64 (mode (g_in g)) /\
          getr R 23 = Z_to_bv 64 (g_p g + 7) /\
          getr R 25 = Z_to_bv 64 (g_n g - 7) /\
          LF.munch W2 mem mem' /\ LF.wmono rsegs mem mem' /\ shadow_rw mem' /\
          stk rsegs mem' (sp - 16) sp /\
          bytes_at rsegs mem' (fr + 2624) (OUR (g_in g)) /\
          bytes_at rsegs mem' (A + 40) (le8 (Z_to_bv 64 fr)) /\
          bytes_at rsegs mem' (A + 48) (le8 (Z_to_bv 64 sel)) /\
          bytes_at rsegs mem' (A + 152) (le8 (Z_to_bv 64 (fr + 64))) /\
          bytes_at rsegs mem' (A + 160) (le8 (Z_to_bv 64 (fr + 32))) /\
          bytes_at rsegs mem' (Sfr fr + 332) [Z_to_bv 8 0] /\
          bytes_at rsegs mem' (fr + 2656) (le8 (Z_to_bv 64 11))))
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite b_mkR_of.
      (* the frame is apart from the callee window on both arms *)
      assert (Hwapart : fr + FRAME_BYTES <= sp - 16 \/ sp <= fr).
      { unfold rs_hold in Hloc. destruct Hloc as [[_ [Hspfr _]] | [_ [_ [Hfs _]]]].
        - right. lia.
        - left. destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
          destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr)
            as [_ Hend _ _].
          assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity. lia. }
      assert (Hspapp : app_mem sp \/ sp = fr).
      { unfold rs_hold in Hloc. destruct Hloc as [[_ [Hspfr _]] | [_ [_ [_ _]]]]; [right; lia|].
        left. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
      assert (Hwapp : forall a, sp - 16 <= a < sp -> app_mem a).
      { intros a Ha. unfold rs_hold in Hloc. destruct Hloc as [[_ [Hspfr _]] | [_ [_ [_ _]]]].
        - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
          pose proof (Happ' fr ltac:(lia)) as X. unfold app_mem, LOWMEM_END, HIGHMEM_BEG in X. lia.
        - unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia. }
      assert (Hcapp : forall i, 0 <= i < 8 -> app_mem (fr + 2656 + i))
        by (intros i Hi; apply Happ'; lia).
      assert (Hdjsh : fr + 2664 <= Sfr fr + 332 \/ Sfr fr + 333 <= fr + 2656).
      { pose proof (Happ' (fr + 2656) ltac:(lia)) as X.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X. lia. }
      assert (Hdjw : sp <= Sfr fr \/ Sfr fr + 333 <= sp - 16).
      { destruct (Hwapp (sp - 16) ltac:(lia)) as [Hlo2|Hhi2];
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia. }
      apply rs_hide in Hspapp. apply rs_hide in Hdjsh. apply rs_hide in Hdjw.
      (* the turn's store, then the tail *)
      destruct (Z_lt_ge_dec 5 (g_n g)) as [Hlt | Hge].
      * (* left > 0 at turn 5 *)
        assert (Hmin : Z.min 5 (g_n g) = 5) by lia.
        destruct (HIN ltac:(lia)) as (HInH & HADp).
        destruct (Hpb ltac:(lia)) as (Hp0 & Hpn).
        assert (HADt : addressable mem (g_p g + 5) 1)
          by (destruct HADp as (D1 & D2 & D3 & D); split; [lia|]; split; [lia|]; split; [lia|];
              intros k Hk; replace (g_p g + 5 + k) with (g_p g + (5 + k)) by lia; apply D; lia).
        destruct (meta_byte mem (g_p g + 5) 1 HADt ltac:(lia)) as (kq & HROq & Hokq & Hinq).
        assert (HRq : ov_read_bytes rsegs mem (wa ((g_p g + 5) / 8 + ASAN_K)) 1 = Some [kq]).
        { pose proof (ro_cells_read rsegs mem _ [C1 kq] 0%nat (C1 kq) HROq ltac:(reflexivity)) as HH.
          cbn [csize cbytes] in HH. change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r in HH.
          rewrite rc_shr3 in HH. exact HH. }
        assert (HRb : ov_read_bytes rsegs mem (wa (g_p g + 5)) 1
                      = Some [RcIdentModel.nthb (g_in g) 5%nat])
          by (pose proof (b_rd_at mem (g_p g) (g_in g) 5 (RcIdentModel.nthb (g_in g) 5%nat) HINB ltac:(lia)
                 ltac:(unfold RcIdentModel.nthb; apply nth_error_nth'; lia)) as HH; exact HH).
        eapply evt_cut.
        { apply (b_any_ld_evt pc0) with (cnt := 1) (d := fr + 2624 + 5) (q := g_p g + 5) (v := g_n g - 5)
            (K := ASAN_K) (b := RcIdentModel.nthb (g_in g) 5%nat) (kq := kq);
            try (rewrite H10; f_equal; lia); try (rewrite H18, Hmin; f_equal; lia);
            try (rewrite H22, Hmin; reflexivity); try assumption; try (unfold ASAN_K; lia); try zlia;
            try (destruct Hokq as [Hk|Hk]; [left; exact Hk | right; lia]). }
        intros ms1 (x4 & x5 & m1 & Ems & MU1 & WM1 & HB1). cbn [Z.eqb] in Ems. subst ms1.
        clear Hokq.
        (* our[] is complete, and the cells the tail writes or reads are carried across the store *)
        assert (HOUR1 : bytes_at rsegs m1 (fr + 2624) (OUR (g_in g))).
        { pose proof (b_our_keep mem m1 (fr + 2624) 5 _ junk (RcIdentModel.nthb (g_in g) 5%nat)
                        HOUR HPRElen ltac:(lia) ltac:(lia) MU1 HB1) as HH.
          replace (tl junk) with (@nil byte) in HH
            by (destruct junk as [|b0 [|b1 r]]; cbn [length] in Hjl; try zlia; reflexivity).
          rewrite app_nil_r in HH. change (Z.to_nat 5) with 5%nat in HH.
          rewrite <- (b_our_step (g_in g) 5%nat ltac:(lia)) in HH.
          rewrite firstn_all2 in HH by (rewrite OUR_length; lia). exact HH. }
        assert (CH1a : rw_cells rsegs m1 (A + 40) [CB 16 xs1]).
        { apply (rw_cells_transport rsegs Wf mem m1 _ _ CH1 MU1 WM1).
          cbn [cells_size csize Nat.add]. unfold Wf. cbn [disjoint_from]. split; [right; lia | exact I]. }
        assert (CH2a : rw_cells rsegs m1 (A + 152) [CB 16 xs2]).
        { apply (rw_cells_transport rsegs Wf mem m1 _ _ CH2 MU1 WM1).
          cbn [cells_size csize Nat.add]. unfold Wf. cbn [disjoint_from]. split; [right; lia | exact I]. }
        assert (Hq56a : q64 m1 (A + 56) (fr + 3040)).
        { apply (bytes_at_transport rsegs Wf mem m1 _ _ Hq56 MU1).
          rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [right; lia | exact I]. }
        pose proof (b_ro8 m1 (A + 56) (fr + 3040) Hq56a) as RO56a.
        assert (HINB1 : bytes_at rsegs m1 (g_p g) (g_in g)).
        { apply (bytes_at_transport rsegs Wf mem m1 _ _ HINB MU1).
          rewrite <- Hlen. unfold Wf. cbn [disjoint_from]. split; [|exact I].
          destruct (Hdj ltac:(lia)) as [H|H]; [left | right]; lia. }
        assert (HADp1 : addressable m1 (g_p g) (g_n g)).
        { apply (b_addr_keep Wf mem m1 (g_p g) (g_n g) HADp MU1). intros i Hi.
          unfold Wf. cbn [LF.outside].
          assert (Hin : in_shadow (shadow_addr (g_p g + i)))
            by (apply shadow_of_app; destruct HADp as (_ & _ & _ & Hb); exact (proj1 (Hb i Hi))).
          pose proof (Hshrng _ Hin). split; [lia | exact I]. }
        assert (CHsh1 : rw_cells rsegs m1 (Sfr fr + 332) [CB 1 sh1]).
        { apply (rw_cells_transport rsegs Wf mem m1 _ _ CHsh MU1 WM1).
          cbn [cells_size csize Nat.add]. unfold Wf. cbn [disjoint_from].
          pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))). split; [lia | exact I]. }
        assert (CHc1 : rw_cells rsegs m1 (fr + 2656) [CB 8 cs]).
        { apply (rw_cells_transport rsegs Wf mem m1 _ _ CHc MU1 WM1).
          cbn [cells_size csize Nat.add]. unfold Wf. cbn [disjoint_from]. split; [right; lia | exact I]. }
        assert (STw1 : stk rsegs m1 (sp - 16) sp).
        { apply (b_stk_tr Wf mem m1 _ _ Hstkw MU1 WM1). intros x Hx. left.
          unfold Wf. cbn [outside]. split; [lia | exact I]. }
        assert (HAC1 : asan_cells m1).
        { apply (asan_cells_kept Wf mem m1 HAC0 MU1). unfold Wf. cbn [disjoint_from].
          unfold RT_LO, RT_HI. split; [lia | exact I]. }
        assert (HSW1 : shadow_rw m1).
        { apply (b_shadow_rw Wf mem m1 HSW0 MU1 WM1). intros a Ha. left.
          unfold Wf. cbn [outside]. pose proof (Hshrng a Ha). split; [lia | exact I]. }
        eapply evt_cut.
        { apply b_tail_evt with (Ab := A) (q := g_p g + 6) (w := g_n g - 6) (frv := fr) (a6v := fr + 32)
            (a7v := fr + 64) (selv := sel) (v56 := fr + 3040) (xs1 := xs1) (xs2 := xs2);
            try assumption; try zlia; try weq. }
        intros ms2 (m2 & MU2 & WM2 & HB40 & HB48 & HB152 & HB160 & Hcase).
        assert (HOUR2 : bytes_at rsegs m2 (fr + 2624) (OUR (g_in g))).
        { apply (bytes_at_transport rsegs [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 _ _ HOUR1 MU2).
          rewrite OUR_length. cbn [disjoint_from]. split; [left; lia | split; [left; lia | exact I]]. }
        destruct Hcase as [(Hw0 & R2x & Ems2 & P2 & P3x & P4 & P8 & P9 & P19 & P26 & P27 & P23 & P25 & P24)
                          | (Hwn & Ems2)];
          subst ms2.
        -- (* n = 6: the left = 0 arm of the tail, to P3 *)
           apply evt_done. do 3 eexists. split; [reflexivity|]. left.
           split; [reflexivity|]. split; [exact P2|]. split; [exact P3x|]. split; [exact P4|].
           split; [exact P8|]. split; [rewrite Hr9; exact P9|]. split; [exact P19|].
           split; [rewrite Hr26; exact P26|]. split; [exact P27|].
           split; [transitivity (Z_to_bv 64 (g_p g + 6)); [exact P23 | rewrite Hc0; f_equal; lia]|].
           split; [transitivity (Z_to_bv 64 0); [exact P25 | rewrite Hc0; f_equal; lia]|].
           split; [exact P24|].
           split.
           { apply (munch_trans W2p mem m1 m2).
             - apply (munch_weaken Wf W2p mem m1); [|exact MU1].
               unfold Wf, W2p. intros x Hx. cbn [outside] in Hx |- *. split; [lia | exact I].
             - apply (munch_weaken [(A + 40, A + 56); (A + 152, A + 168)] W2p m1 m2); [|exact MU2].
               unfold W2p. intros x Hx. cbn [outside] in Hx |- *. tauto. }
           split; [exact (wmono_trans rsegs mem m1 m2 WM1 WM2)|].
           split; [exact HOUR2|]. split; [exact HB40|]. split; [exact HB48|].
           split; [exact HB152 | exact HB160].
        -- (* n >= 7: the mode byte *)
           assert (Hn7 : 7 <= g_n g) by lia.
           assert (HINB2 : bytes_at rsegs m2 (g_p g) (g_in g)).
           { apply (bytes_at_transport rsegs [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 _ _ HINB1 MU2).
             rewrite <- Hlen. cbn [disjoint_from].
             pose proof (Hpstk ltac:(lia)).
             split; [left; lia | split; [left; lia | exact I]]. }
           assert (HADp2 : addressable m2 (g_p g) (g_n g)).
           { apply (b_addr_keep [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 (g_p g) (g_n g) HADp1 MU2).
             intros i Hi. cbn [LF.outside].
             assert (Hin : in_shadow (shadow_addr (g_p g + i)))
               by (apply shadow_of_app; destruct HADp1 as (_ & _ & _ & Hb); exact (proj1 (Hb i Hi))).
             pose proof (Hshrng _ Hin). split; [lia | split; [lia | exact I]]. }
           assert (Hq56b : q64 m2 (A + 56) (fr + 3040)).
           { apply (bytes_at_transport rsegs [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 _ _ Hq56a MU2).
             rewrite length_le8. cbn [disjoint_from]. split; [right; lia | split; [left; lia | exact I]]. }
           pose proof (b_ro8 m2 (A + 56) (fr + 3040) Hq56b) as RO56b.
           assert (HAD6 : addressable m2 (g_p g + 6) 1)
             by (destruct HADp2 as (D1 & D2 & D3 & D); split; [lia|]; split; [lia|]; split; [lia|];
                 intros k Hk; replace (g_p g + 6 + k) with (g_p g + (6 + k)) by lia; apply D; lia).
           destruct (meta_byte m2 (g_p g + 6) 1 HAD6 ltac:(lia)) as (km & HROm & Hokm & Hinm).
           assert (HRk2 : ov_read_bytes rsegs m2 (wa ((g_p g + 6) / 8 + ASAN_K)) 1 = Some [km]).
           { pose proof (ro_cells_read rsegs m2 _ [C1 km] 0%nat (C1 km) HROm ltac:(reflexivity)) as HH.
             cbn [csize cbytes] in HH. change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r in HH.
             rewrite rc_shr3 in HH. exact HH. }
           assert (HRm2 : ov_read_bytes rsegs m2 (wa (g_p g + 6)) 1
                          = Some [RcIdentModel.nthb (g_in g) 6%nat])
             by (apply (b_rd_at m2 (g_p g) (g_in g) 6); [exact HINB2 | lia |];
                 unfold RcIdentModel.nthb; apply nth_error_nth'; lia).
           destruct (Hpb ltac:(lia)) as (Hp0b & Hpnb).
           eapply evt_cut.
           { apply b_mode_evt with (Ab := A) (q := g_p g + 6) (w := g_n g - 6) (K := ASAN_K) (v56 := fr + 3040)
               (bm := RcIdentModel.nthb (g_in g) 6%nat) (km := km);
               try reflexivity; try assumption; try weq; try zlia; try (unfold ASAN_K; lia);
               try (destruct Hokm as [Hk|Hk]; [left; exact Hk | right; lia]). }
           intros ms3 [ (Hev & R3x & Ems3 & Q2 & Q3 & Q4 & Q8 & Q9 & Q19 & Q26 & Q27 & Q23 & Q25 & Q24)
                      | (Hod & x0 & x1 & Ems3) ]; subst ms3; clear Hokm.
           ++ (* even mode: P3 *)
              apply evt_done. do 3 eexists. split; [reflexivity|]. left.
              split; [reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
              split; [exact Q8|]. split; [rewrite Hr9; exact Q9|]. split; [exact Q19|].
              split; [rewrite Hr26; exact Q26|]. split; [exact Q27|].
              split; [transitivity (Z_to_bv 64 (g_p g + 6 + 1)); [exact Q23 | rewrite Hc0; f_equal; lia]|].
              split; [transitivity (Z_to_bv 64 (g_n g - 6 - 1)); [exact Q25 | rewrite Hc0; f_equal; lia]|].
              split; [exact Q24|].
              split.
              { apply (munch_trans W2p mem m1 m2).
                - apply (munch_weaken Wf W2p mem m1); [|exact MU1].
                  unfold Wf, W2p. intros x Hx. cbn [outside] in Hx |- *. split; [lia | exact I].
                - apply (munch_weaken [(A + 40, A + 56); (A + 152, A + 168)] W2p m1 m2); [|exact MU2].
                  unfold W2p. intros x Hx. cbn [outside] in Hx |- *. tauto. }
              split; [exact (wmono_trans rsegs mem m1 m2 WM1 WM2)|].
              split; [exact HOUR2|]. split; [exact HB40|]. split; [exact HB48|].
              split; [exact HB152 | exact HB160].
           ++ (* odd mode: the catalogue call *)
              assert (CHsh2 : rw_cells rsegs m2 (Sfr fr + 332) [CB 1 sh1]).
              { apply (rw_cells_transport rsegs [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 _ _ CHsh1 MU2 WM2).
                cbn [cells_size csize Nat.add disjoint_from].
                pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
                split; [lia | split; [lia | exact I]]. }
              assert (CHc2 : rw_cells rsegs m2 (fr + 2656) [CB 8 cs]).
              { apply (rw_cells_transport rsegs [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 _ _ CHc1 MU2 WM2).
                cbn [cells_size csize Nat.add disjoint_from].
                split; [left; lia | split; [left; lia | exact I]]. }
              assert (STw2 : stk rsegs m2 (sp - 16) sp).
              { apply (b_stk_tr [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 _ _ STw1 MU2 WM2).
                intros x Hx. left. cbn [outside]. split; [lia | split; [lia | exact I]]. }
              assert (HAC2 : asan_cells m2).
              { apply (asan_cells_kept [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 HAC1 MU2).
                cbn [disjoint_from]. unfold RT_LO, RT_HI. split; [lia | split; [lia | exact I]]. }
              assert (HSW2 : shadow_rw m2).
              { apply (b_shadow_rw [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 HSW1 MU2 WM2).
                intros a Ha. left. cbn [outside]. pose proof (Hshrng a Ha).
                split; [lia | split; [lia | exact I]]. }
              eapply evt_mono.
              ** unfold rs_hold in Hdjsh, Hdjw, Hfrm8.
                 apply (b_cat_evt CATC) with (Sh := Sfr fr) (c := fr + 2656) (spv := sp)
                   (sh1 := sh1) (cs := cs);
                   try assumption; try zlia;
                   try (intros i Hi; apply Happ'; lia);
                   try (intros a Ha; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia).
              ** intros ms4 (R4x & m3 & Ems4 & C2 & C3 & C4 & C8 & C9 & C18 & C19 & C20 & C22 & C23 & C24 & C25 &
                             C26 & C27 & C10 & MU3 & WM3 & HSW3 & STw3 & HZc & HZsh).
                 replace (fr + 2656 + 8) with (fr + 2664) in MU3 by lia.
                 subst ms4. do 3 eexists. split; [reflexivity|]. right.
                 split; [reflexivity|]. split; [exact Hn7|].
                 split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C8|].
                 split; [rewrite Hr9; exact C9|]. split; [exact C19|].
                 split; [rewrite Hr26; exact C26|]. split; [exact C27|].
                 split; [exact C20|].
                 split; [exact C10|].
                 split.
                 { etransitivity; [exact C22|]. unfold mode.
                   replace (7 <=? nlen (g_in g)) with true by (symmetry; apply Z.leb_le; unfold nlen; lia).
                   reflexivity. }
                 split; [transitivity (Z_to_bv 64 (g_p g + 6 + 1)); [exact C23 | f_equal; lia]|].
                 split; [transitivity (Z_to_bv 64 (g_n g - 6 - 1)); [exact C25 | f_equal; lia]|].
                 split.
                 { apply (munch_trans W2 mem m1 m3).
                   - apply (munch_weaken Wf W2 mem m1); [|exact MU1].
                     unfold Wf, W2. intros x Hx. cbn [outside] in Hx |- *. split; [lia | exact I].
                   - apply (munch_trans W2 m1 m2 m3).
                     + apply (munch_weaken [(A + 40, A + 56); (A + 152, A + 168)] W2 m1 m2); [|exact MU2].
                       unfold W2. intros x Hx. cbn [outside] in Hx |- *. tauto.
                     + apply (munch_weaken [(Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)]
                                W2 m2 m3); [|exact MU3].
                       unfold W2. intros x Hx. cbn [outside] in Hx |- *. tauto. }
                 split; [exact (wmono_trans rsegs mem m2 m3
                           (wmono_trans rsegs mem m1 m2 WM1 WM2) WM3)|].
                 split; [exact HSW3|]. split; [exact STw3|].
                 split.
                 { apply (bytes_at_transport rsegs
                     [(Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)] m2 m3 _ _ HOUR2 MU3).
                   rewrite OUR_length. cbn [disjoint_from].
                   pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
                   split; [lia | split; [left; lia | split; [lia | exact I]]]. }
                 split.
                 { apply (bytes_at_transport rsegs
                     [(Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)] m2 m3 _ _ HB40 MU3).
                   rewrite length_le8. cbn [disjoint_from].
                   pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
                   split; [lia | split; [lia | split; [lia | exact I]]]. }
                 split.
                 { apply (bytes_at_transport rsegs
                     [(Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)] m2 m3 _ _ HB48 MU3).
                   rewrite length_le8. cbn [disjoint_from].
                   pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
                   split; [lia | split; [lia | split; [lia | exact I]]]. }
                 split.
                 { apply (bytes_at_transport rsegs
                     [(Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)] m2 m3 _ _ HB152 MU3).
                   rewrite length_le8. cbn [disjoint_from].
                   pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
                   split; [lia | split; [lia | split; [lia | exact I]]]. }
                 split.
                 { apply (bytes_at_transport rsegs
                     [(Sfr fr + 332, Sfr fr + 333); (fr + 2656, fr + 2664); (sp - 16, sp)] m2 m3 _ _ HB160 MU3).
                   rewrite length_le8. cbn [disjoint_from].
                   pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
                   split; [lia | split; [lia | split; [lia | exact I]]]. }
                 split; [exact HZsh | exact HZc].
      * (* left = 0 at turn 5: the zero store, then the left = 0 arm of the tail to P3 *)
        assert (Hmin : Z.min 5 (g_n g) = g_n g) by lia.
        assert (Hv0 : RcIdentModel.nthb (g_in g) 5%nat = Z_to_bv 8 0) by (apply b_nth_past; lia).
        unfold rs_hold in Hpc0n. destruct Hpc0n as [Epc | Hlt0]; [subst pc0 | exfalso; lia].
        eapply evt_cut.
        { apply b_z_evt with (cnt := 1) (d := fr + 2624 + 5);
            try (rewrite H10; f_equal; lia); try assumption; try zlia.
          rewrite H18, Hmin. f_equal. lia. }
        intros ms1 (m1 & Ems & MU1 & WM1 & HB1). cbn [Z.eqb] in Ems. subst ms1.
        assert (HOUR1 : bytes_at rsegs m1 (fr + 2624) (OUR (g_in g))).
        { pose proof (b_our_keep mem m1 (fr + 2624) 5 _ junk (Z_to_bv 8 0)
                        HOUR HPRElen ltac:(lia) ltac:(lia) MU1 HB1) as HH.
          replace (tl junk) with (@nil byte) in HH
            by (destruct junk as [|b0 [|b1 r]]; cbn [length] in Hjl; try zlia; reflexivity).
          rewrite app_nil_r in HH. change (Z.to_nat 5) with 5%nat in HH.
          rewrite <- Hv0 in HH.
          rewrite <- (b_our_step (g_in g) 5%nat ltac:(lia)) in HH.
          rewrite firstn_all2 in HH by (rewrite OUR_length; lia). exact HH. }
        assert (CH1a : rw_cells rsegs m1 (A + 40) [CB 16 xs1]).
        { apply (rw_cells_transport rsegs Wf mem m1 _ _ CH1 MU1 WM1).
          cbn [cells_size csize Nat.add]. unfold Wf. cbn [disjoint_from]. split; [right; lia | exact I]. }
        assert (CH2a : rw_cells rsegs m1 (A + 152) [CB 16 xs2]).
        { apply (rw_cells_transport rsegs Wf mem m1 _ _ CH2 MU1 WM1).
          cbn [cells_size csize Nat.add]. unfold Wf. cbn [disjoint_from]. split; [right; lia | exact I]. }
        assert (Hq56a : q64 m1 (A + 56) (fr + 3040)).
        { apply (bytes_at_transport rsegs Wf mem m1 _ _ Hq56 MU1).
          rewrite length_le8. unfold Wf. cbn [disjoint_from]. split; [right; lia | exact I]. }
        pose proof (b_ro8 m1 (A + 56) (fr + 3040) Hq56a) as RO56a.
        pose proof (bv_unsigned_in_range 64 (getr regs 22)) as H22r. unfold bv_modulus in H22r. cbn in H22r.
        eapply evt_cut.
        { apply b_tail_evt with (Ab := A) (q := bv_unsigned (getr regs 22)) (w := 0) (frv := fr)
            (a6v := fr + 32) (a7v := fr + 64) (selv := sel) (v56 := fr + 3040) (xs1 := xs1) (xs2 := xs2);
            try reflexivity; try assumption; try zlia; try (symmetry; apply Z_to_bv_bv_unsigned). }
        intros ms2 (m2 & MU2 & WM2 & HB40 & HB48 & HB152 & HB160 & Hcase).
        assert (HOUR2 : bytes_at rsegs m2 (fr + 2624) (OUR (g_in g))).
        { apply (bytes_at_transport rsegs [(A + 40, A + 56); (A + 152, A + 168)] m1 m2 _ _ HOUR1 MU2).
          rewrite OUR_length. cbn [disjoint_from]. split; [left; lia | split; [left; lia | exact I]]. }
        destruct Hcase as [(Hw0 & R2x & Ems2 & P2 & P3x & P4 & P8 & P9 & P19 & P26 & P27 & P23 & P25 & P24)
                          | (Hwn & Ems2)];
          [| exfalso; exact (Hwn eq_refl)].
        subst ms2.
        apply evt_done. do 3 eexists. split; [reflexivity|]. left.
        split; [reflexivity|]. split; [exact P2|]. split; [exact P3x|]. split; [exact P4|].
        split; [exact P8|]. split; [rewrite Hr9; exact P9|]. split; [exact P19|].
        split; [first [exact P26 | rewrite Hr26; exact P26]|]. split; [exact P27|].
        split.
        { transitivity (Z_to_bv 64 (bv_unsigned (getr regs 22))); [exact P23|].
          rewrite Z_to_bv_bv_unsigned, H22, Hc0. f_equal. lia. }
        split; [transitivity (Z_to_bv 64 0); [exact P25 | rewrite Hc0; f_equal; lia]|].
        split; [exact P24|].
        split.
        { apply (munch_trans W2p mem m1 m2).
          - apply (munch_weaken Wf W2p mem m1); [|exact MU1].
            unfold Wf, W2p. intros x Hx. cbn [outside] in Hx |- *. split; [lia | exact I].
          - apply (munch_weaken [(A + 40, A + 56); (A + 152, A + 168)] W2p m1 m2); [|exact MU2].
            unfold W2p. intros x Hx. cbn [outside] in Hx |- *. tauto. }
        split; [exact (wmono_trans rsegs mem m1 m2 WM1 WM2)|].
        split; [exact HOUR2|]. split; [exact HB40|]. split; [exact HB48|].
        split; [exact HB152 | exact HB160].
    + intros R pc' mem' regs'' md' HK Hreg Hmat.
      assert (Hk2 : getr regs'' 2 = getr R 2) by exact (Hreg _).
      assert (Hsp64 : AC.aspZ regs = sp) by exact Haspz.
      assert (Hwr : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> writable_at rsegs mem a)
        by (intros a Ha; destruct Hwin as (_ & _ & Hwv); exact (proj1 (Hwv a Ha))).
      destruct HK as [(Epc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K23 & K25 & K24 & MU & WM & HOURm &
                       HB40 & HB48 & HB152 & HB160)
                     |(Epc & Hn7 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K20 & K10 & K22 & K23 & K25 &
                       MU & WM & HSWm & STwm & HOURm & HB40 & HB48 & HB152 & HB160 & HZsh & HZc)]; subst pc'.
      * (* P3 (0x81cb0): n = 6 or an even mode byte *)
        assert (HSWm : shadow_rw mem').
        { apply (b_shadow_rw W2p mem mem' HSW0 MU WM). intros a Ha. left.
          unfold W2p. cbn [outside]. pose proof (Hshrng a Ha). repeat split; first [exact I | lia]. }
        assert (HWlo : forall lo hi, In (lo, hi) W2p -> 6283264 <= lo).
        { intros lo hi Hin. unfold W2p in Hin.
          repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
        assert (HWcl : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W2p x ->
                  (fr + 24 <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
                  (AC.aspZ regs - 16 <= x < AC.aspZ regs) \/
                  (bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 168)).
        { intros x Hx Hno. rewrite HbvA, Hsp64. unfold W2p in Hno. cbn [LF.outside] in Hno. lia. }
        assert (HRD : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W2p x -> exists b, mrd rsegs mem' (wa x) = Some b).
        { intros x Hx Hno. unfold W2p in Hno. cbn [LF.outside] in Hno.
          assert (Hin : (fr + 2624 <= x < fr + 2630) \/ (A + 40 <= x < A + 48) \/ (A + 48 <= x < A + 56) \/
                        (A + 152 <= x < A + 160) \/ (A + 160 <= x < A + 168)) by lia.
          destruct Hin as [H|[H|[H|[H|H]]]].
          - apply (b_ba_rd mem' (fr + 2624) (OUR (g_in g)) x HOURm). rewrite OUR_length. lia.
          - apply (b_ba_rd mem' (A + 40) _ x HB40). rewrite length_le8. lia.
          - apply (b_ba_rd mem' (A + 48) _ x HB48). rewrite length_le8. lia.
          - apply (b_ba_rd mem' (A + 152) _ x HB152). rewrite length_le8. lia.
          - apply (b_ba_rd mem' (A + 160) _ x HB160). rewrite length_le8. lia. }
        destruct (b_fra_after g fr regs regs'' mem mem' md md' sel W2p A HFRAS HENT MU WM HSWm HWlo HWcl HRD
                    (eq_trans (Hreg _) K2) (eq_trans (Hreg _) K3) (eq_trans (Hreg _) K4) (eq_trans (Hreg _) K8)
                    (eq_trans (Hreg _) K9) (eq_trans (Hreg _) K19) (eq_trans (Hreg _) K26) Hr9 HB48 HB40 Hmat)
          as (HFRA' & HENT').
        rewrite <- SEGS. apply HP3.
        exists regs'', mem', md', fr.
        split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
        cbv beta. unfold OURb.
        split; [exact Hgn|]. split; [exact HOURm|].
        split; [unfold rg; rewrite Hreg; exact K24|].
        assert (HoutA : forall off, 56 <= off -> off + 8 <= 448 -> (off + 8 <= 152 \/ 168 <= off) ->
                  forall x, A + off <= x < A + off + 8 -> LF.outside W2p x).
        { intros off H1 H2 H3 x Hx. unfold W2p. cbn [LF.outside]. repeat split; first [exact I | lia]. }
        assert (HskP : forall off v, 56 <= off -> off + 8 <= 448 -> (off + 8 <= 152 \/ 168 <= off) ->
                  spill regs mem off v -> spill regs'' mem' off v).
        { intros off v H1 H2 H3 Hs.
          exact (b_spill_keep W2p regs regs'' mem mem' off v A Hs ltac:(unfold rg; exact Hr9)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hreg; exact K9) MU (HoutA off H1 H2 H3)). }
        (* PRO = PRA (A4's spills, kept) /\ [A + 152] = fr + 64 (0x815a0 sd a7,152(s1)) /\ [A + 264] = fr + 2624 /\
           our[]'s 6 bytes addressable (their shadow byte S(fr) + 328 is not written) /\ [A + 160] = fr + 32
           (0x815a4 sd a6,160(s1)) *)
        split.
        { unfold PRO, PRA.
          split; [|split; [|split; [|split]]].
          - split; [exact (HskP 136 (fr + 160) ltac:(lia) ltac:(lia) ltac:(lia) P136)|].
            split; [exact (HskP 280 (fr + 176) ltac:(lia) ltac:(lia) ltac:(lia) P280)|].
            split; [exact (HskP 168 (fr + 2880) ltac:(lia) ltac:(lia) ltac:(lia) P168)|].
            split; [exact (HskP 192 (fr + 528) ltac:(lia) ltac:(lia) ltac:(lia) P192)|].
            split; [exact (HskP 200 (fr + 336) ltac:(lia) ltac:(lia) ltac:(lia) P200)|].
            split; [exact (HskP 216 (fr + 448) ltac:(lia) ltac:(lia) ltac:(lia) P216)|].
            split; [exact (HskP 104 (fr + 128) ltac:(lia) ltac:(lia) ltac:(lia) P104)|].
            split; [exact (HskP 288 (fr + 256) ltac:(lia) ltac:(lia) ltac:(lia) P288)|].
            split; [exact (HskP 296 (fr + 304) ltac:(lia) ltac:(lia) ltac:(lia) P296)|].
            split; [exact (HskP 304 (fr + 272) ltac:(lia) ltac:(lia) ltac:(lia) P304)|].
            exact (HskP 168 (fr + 2880) ltac:(lia) ltac:(lia) ltac:(lia) P168b).
          - exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9 | exact HB152].
          - exact (HskP 264 (fr + 2624) ltac:(lia) ltac:(lia) ltac:(lia) L264).
          - apply (b_addr_keep W2p mem mem' (fr + 2624) 6 HAour MU). intros i Hi.
            rewrite (b_sh_our fr i Hfrm8 ltac:(lia)).
            unfold W2p. cbn [LF.outside]. repeat split; first [exact I | lia].
          - exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9 | exact HB160]. }
        (* [A + 64] = fr + 3056 (A4), the cursor at c0 and the kind-name table *)
        split; [exact (HskP 64 (fr + 3056) ltac:(lia) ltac:(lia) ltac:(lia) L64)|].
        split.
        { unfold CUR, rg. split; [rewrite Hc0; lia|].
          split; [rewrite Hreg; exact K23 | rewrite Hreg; exact K25]. }
        split; [exact (b_fra_kn g fr [] regs'' mem' md' HFRA')|].
        pose proof (HskP 176 (fr + 2688) ltac:(lia) ltac:(lia) ltac:(lia) L176) as H176'.
        pose proof (HskP 208 (fr + 2768) ltac:(lia) ltac:(lia) ltac:(lia) L208) as H208'.
        destruct H176' as (A1 & HA1 & Hq176).
        destruct H208' as (A2 & HA2 & Hq208).
        assert (Hr9'' : getr regs'' 9 = Z_to_bv 64 A) by (rewrite Hreg, K9; exact Hr9).
        assert (HA1e : A1 = A).
        { pose proof Hq176 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
          pose proof (rg_eq64 regs'' 9 A1 A HA1 Hr9'') as Hm.
          change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
        assert (HA2e : A2 = A).
        { pose proof Hq208 as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
          pose proof (rg_eq64 regs'' 9 A2 A HA2 Hr9'') as Hm.
          change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
        subst A1 A2.
        destruct (stk_split rsegs mem fr (fr + 2688) (fr + FRAME_BYTES) Hfstk ltac:(lia)) as (_ & Hf1).
        destruct (stk_split rsegs mem (fr + 2688) (fr + 2726) (fr + FRAME_BYTES) Hf1 ltac:(lia)) as (Hfid & Hf2).
        destruct (stk_split rsegs mem (fr + 2726) (fr + 2768) (fr + FRAME_BYTES) Hf2 ltac:(lia)) as (_ & Hf3).
        destruct (stk_split rsegs mem (fr + 2768) (fr + 2840) (fr + FRAME_BYTES) Hf3 ltac:(lia)) as (Hfjk & Hf4).
        destruct (stk_split rsegs mem (fr + 2840) (fr + 2880) (fr + FRAME_BYTES) Hf4 ltac:(lia)) as (_ & Hf5).
        destruct (stk_split rsegs mem (fr + 2880) (fr + 2920) (fr + FRAME_BYTES) Hf5 ltac:(lia)) as (Hffs & _).
        assert (Hfid' : stk rsegs mem' (fr + 2688) (fr + 2726)).
        { apply (b_stk_tr W2p mem mem' _ _ Hfid MU WM). intros x Hx. left.
          unfold W2p. cbn [outside]. repeat split; first [exact I | lia]. }
        assert (Hfjk' : stk rsegs mem' (fr + 2768) (fr + 2840)).
        { apply (b_stk_tr W2p mem mem' _ _ Hfjk MU WM). intros x Hx. left.
          unfold W2p. cbn [outside]. repeat split; first [exact I | lia]. }
        assert (Hffs' : stk rsegs mem' (fr + 2880) (fr + 2920)).
        { apply (b_stk_tr W2p mem mem' _ _ Hffs MU WM). intros x Hx. left.
          unfold W2p. cbn [outside]. repeat split; first [exact I | lia]. }
        destruct (stk_bytes rsegs mem' _ _ Hfid' ltac:(lia)) as (idb & Hidl & Hidb).
        destruct (stk_bytes rsegs mem' _ _ Hfjk' ltac:(lia)) as (jk & Hjkl & Hjkb).
        destruct (stk_bytes rsegs mem' _ _ Hffs' ltac:(lia)) as (jf & Hjfl & Hjfb).
        exists sp, A, idb, jk.
        split; [rewrite Hk2, K2; exact Hr2|].
        split; [exact Hr9''|].
        split; [exact HA64|]. split; [lia|].
        split; [exact Hq176|].
        split.
        { apply b_rw_C8; [exact Hq208|].
          split; [lia|]. split; [lia|]. intros i Hi. exact (WM _ (Hwr (A + 208 + i) ltac:(lia))). }
        split.
        { replace 38%nat with (length idb) by lia. apply b_rw_CB; [exact Hidb|].
          replace (Z.of_nat (length idb)) with (fr + 2726 - (fr + 2688)) by lia. exact (b_wr_stk _ _ _ Hfid'). }
        split.
        { replace 72%nat with (length jk) by lia. apply b_rw_CB; [exact Hjkb|].
          replace (Z.of_nat (length jk)) with (fr + 2840 - (fr + 2768)) by lia. exact (b_wr_stk _ _ _ Hfjk'). }
        exists jf.
        { replace 40%nat with (length jf) by lia. apply b_rw_CB; [exact Hjfb|].
          replace (Z.of_nat (length jf)) with (fr + 2920 - (fr + 2880)) by lia. exact (b_wr_stk _ _ _ Hffs'). }
      * (* R2 (0x815fc): an odd mode byte, after the catalogue call *)
        assert (HWlo : forall lo hi, In (lo, hi) W2 -> 6283264 <= lo).
        { intros lo hi Hin. unfold W2 in Hin.
          pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
          repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
        assert (HWcl : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W2 x ->
                  (fr + 24 <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
                  (AC.aspZ regs - 16 <= x < AC.aspZ regs) \/
                  (bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 168)).
        { intros x Hx Hno. rewrite HbvA, Hsp64. unfold W2 in Hno. cbn [LF.outside] in Hno. lia. }
        assert (HRD : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside W2 x -> exists b, mrd rsegs mem' (wa x) = Some b).
        { intros x Hx Hno. unfold W2 in Hno. cbn [LF.outside] in Hno.
          assert (Hin : (fr + 2624 <= x < fr + 2630) \/ (A + 40 <= x < A + 48) \/ (A + 48 <= x < A + 56) \/
                        (A + 152 <= x < A + 160) \/ (A + 160 <= x < A + 168) \/
                        (Sfr fr + 332 <= x < Sfr fr + 333) \/
                        (fr + 2656 <= x < fr + 2664) \/ (sp - 16 <= x < sp)) by lia.
          destruct Hin as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
          - apply (b_ba_rd mem' (fr + 2624) (OUR (g_in g)) x HOURm). rewrite OUR_length. lia.
          - apply (b_ba_rd mem' (A + 40) _ x HB40). rewrite length_le8. lia.
          - apply (b_ba_rd mem' (A + 48) _ x HB48). rewrite length_le8. lia.
          - apply (b_ba_rd mem' (A + 152) _ x HB152). rewrite length_le8. lia.
          - apply (b_ba_rd mem' (A + 160) _ x HB160). rewrite length_le8. lia.
          - apply (b_ba_rd mem' (Sfr fr + 332) _ x HZsh). cbn [length]. lia.
          - apply (b_ba_rd mem' (fr + 2656) _ x HZc). rewrite length_le8. lia.
          - destruct STwm as (_ & _ & Hst). exact (proj2 (Hst x H)). }
        destruct (b_fra_after g fr regs regs'' mem mem' md md' sel W2 A HFRAS HENT MU WM HSWm HWlo HWcl HRD
                    (eq_trans (Hreg _) K2) (eq_trans (Hreg _) K3) (eq_trans (Hreg _) K4) (eq_trans (Hreg _) K8)
                    (eq_trans (Hreg _) K9) (eq_trans (Hreg _) K19) (eq_trans (Hreg _) K26) Hr9 HB48 HB40 Hmat)
          as (HFRA' & HENT').
        rewrite <- SEGS. apply HR2.
        exists regs'', mem', md', fr.
        split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
        cbv beta. unfold a0v, OURb, CUR.
        assert (HoutA : forall off, 56 <= off -> off + 8 <= 448 -> (off + 8 <= 152 \/ 168 <= off) ->
                  forall x, A + off <= x < A + off + 8 -> LF.outside W2 x).
        { intros off H1 H2 H3 x Hx. unfold W2. cbn [LF.outside].
          pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
          repeat split; first [exact I | lia]. }
        assert (Hsk : forall off v, 56 <= off -> off + 8 <= 448 -> (off + 8 <= 152 \/ 168 <= off) ->
                  spill regs mem off v -> spill regs'' mem' off v).
        { intros off v H1 H2 H3 Hs.
          exact (b_spill_keep W2 regs regs'' mem mem' off v A Hs ltac:(unfold rg; exact Hr9)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hreg; exact K9) MU (HoutA off H1 H2 H3)). }
        split; [exact Hgn|].
        split; [unfold rg; rewrite Hreg; exact K10|].
        split; [exact HOURm|].
        split; [unfold rg; rewrite Hreg, K27; exact H27|].
        split; [split; [lia|]; split; unfold rg; rewrite Hreg; [exact K23 | exact K25]|].
        split; [exact (Hsk 144 (fr + 2176) ltac:(lia) ltac:(lia) ltac:(lia) L144)|].
        split; [exact (Hsk 112 (fr + 2256) ltac:(lia) ltac:(lia) ltac:(lia) L112)|].
        split; [exact (Hsk 312 (fr + 544) ltac:(lia) ltac:(lia) ltac:(lia) L312)|].
        split; [exact (Hsk 264 (fr + 2624) ltac:(lia) ltac:(lia) ltac:(lia) L264)|].
        split; [unfold rg; rewrite Hreg, K20; exact H20|].
        split; [unfold q64, CAT_N; exact HZc|].
        split; [exact (Hsk 56 (fr + 3040) ltac:(lia) ltac:(lia) ltac:(lia) L56)|].
        split; [exact (Hsk 184 (fr + 2368) ltac:(lia) ltac:(lia) ltac:(lia) L184)|].
        split.
        { apply (b_addr_keep W2 mem mem' (fr + 2624) 6 HAour MU). intros i Hi.
          rewrite (b_sh_our fr i Hfrm8 ltac:(lia)).
          pose proof (Hshrng (Sfr fr + 332) (HshIS (Sfr fr + 332) ltac:(lia))).
          unfold W2. cbn [LF.outside]. repeat split; first [exact I | lia]. }
        split; [exact (Hsk 96 (decl_slot fr) ltac:(lia) ltac:(lia) ltac:(lia) L96)|].
        split; [exact (Hsk 120 (fr + 2528) ltac:(lia) ltac:(lia) ltac:(lia) L120)|].
        split; [exact (Hsk 240 (fr + 2448) ltac:(lia) ltac:(lia) ltac:(lia) L240)|].
        split; [exact (Hsk 232 (fr + 2464) ltac:(lia) ltac:(lia) ltac:(lia) L232)|].
        split; [exact (Hsk 224 (fr + 2496) ltac:(lia) ltac:(lia) ltac:(lia) L224)|].
        split; [exact (Hsk 176 (fr + 2688) ltac:(lia) ltac:(lia) ltac:(lia) L176)|].
        split; [exact (Hsk 208 (fr + 2768) ltac:(lia) ltac:(lia) ltac:(lia) L208)|].
        split; [exact (Hsk 64 (fr + 3056) ltac:(lia) ltac:(lia) ltac:(lia) L64)|].
        (* PRA (A4's spills, kept), [A + 152] = fr + 64 (0x815a0 sd a7,152(s1)), s6 = mode and [A + 160] = fr + 32
           (0x815a4 sd a6,160(s1)) *)
        split.
        { unfold PRA.
          split; [exact (Hsk 136 (fr + 160) ltac:(lia) ltac:(lia) ltac:(lia) P136)|].
          split; [exact (Hsk 280 (fr + 176) ltac:(lia) ltac:(lia) ltac:(lia) P280)|].
          split; [exact (Hsk 168 (fr + 2880) ltac:(lia) ltac:(lia) ltac:(lia) P168)|].
          split; [exact (Hsk 192 (fr + 528) ltac:(lia) ltac:(lia) ltac:(lia) P192)|].
          split; [exact (Hsk 200 (fr + 336) ltac:(lia) ltac:(lia) ltac:(lia) P200)|].
          split; [exact (Hsk 216 (fr + 448) ltac:(lia) ltac:(lia) ltac:(lia) P216)|].
          split; [exact (Hsk 104 (fr + 128) ltac:(lia) ltac:(lia) ltac:(lia) P104)|].
          split; [exact (Hsk 288 (fr + 256) ltac:(lia) ltac:(lia) ltac:(lia) P288)|].
          split; [exact (Hsk 296 (fr + 304) ltac:(lia) ltac:(lia) ltac:(lia) P296)|].
          split; [exact (Hsk 304 (fr + 272) ltac:(lia) ltac:(lia) ltac:(lia) P304)|].
          exact (Hsk 168 (fr + 2880) ltac:(lia) ltac:(lia) ltac:(lia) P168b). }
        split; [exists A; split; [unfold rg; rewrite Hreg, K9; exact Hr9 | exact HB152]|].
        split; [unfold rg; rewrite Hreg; exact K22|].
        exists A; split; [unfold rg; rewrite Hreg, K9; exact Hr9 | exact HB160].
  - eapply (sl_run_lib regs (Z_to_bv 64 pc0) mem md
      (fun R pc' mem' =>
         exists v : byte,
           pc' = Z_to_bv 64 0x81548 /\ v = RcIdentModel.nthb (g_in g) (Z.to_nat t) /\
           getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
           getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
           getr R 26 = getr regs 26 /\ getr R 25 = getr regs 25 /\ getr R 24 = getr regs 24 /\
           getr R 20 = getr regs 20 /\ getr R 17 = getr regs 17 /\ getr R 27 = getr regs 27 /\
           getr R 16 = getr regs 16 /\ getr R 11 = getr regs 11 /\
           getr R 10 = Z_to_bv 64 (6 - (t + 1)) /\ getr R 12 = Z_to_bv 64 (fr + 2624 + (t + 1)) /\
           getr R 18 = Z_to_bv 64 (g_n g - Z.min (t + 1) (g_n g)) /\
           getr R 22 = Z_to_bv 64 (g_p g + Z.min (t + 1) (g_n g)) /\
           LF.munch Wf mem mem' /\ LF.wmono rsegs mem mem' /\
           bytes_at rsegs mem' (fr + 2624 + t) [v])
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite b_mkR_of.
      destruct (Z_lt_ge_dec t (g_n g)) as [Hlt | Hge].
      * assert (Hmin : Z.min t (g_n g) = t) by lia.
        destruct (HIN ltac:(lia)) as (HInH & HADp).
        destruct (Hpb ltac:(lia)) as (Hp0 & Hpn).
        assert (HADt : addressable mem (g_p g + t) 1)
          by (destruct HADp as (D1 & D2 & D3 & D); split; [lia|]; split; [lia|]; split; [lia|];
              intros k Hk; replace (g_p g + t + k) with (g_p g + (t + k)) by lia; apply D; lia).
        destruct (meta_byte mem (g_p g + t) 1 HADt ltac:(lia)) as (kq & HROq & Hokq & Hinq).
        assert (HRq : ov_read_bytes rsegs mem (wa ((g_p g + t) / 8 + ASAN_K)) 1 = Some [kq]).
        { pose proof (ro_cells_read rsegs mem _ [C1 kq] 0%nat (C1 kq) HROq ltac:(reflexivity)) as HH.
          cbn [csize cbytes] in HH. change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r in HH.
          rewrite rc_shr3 in HH. exact HH. }
        assert (HRb : ov_read_bytes rsegs mem (wa (g_p g + t)) 1
                      = Some [RcIdentModel.nthb (g_in g) (Z.to_nat t)])
          by (apply (b_rd_at mem (g_p g) (g_in g) t); [exact HINB | lia |];
              unfold RcIdentModel.nthb; apply nth_error_nth'; lia).
        eapply evt_mono.
        -- apply (b_any_ld_evt pc0) with (cnt := 6 - t) (d := fr + 2624 + t) (q := g_p g + t) (v := g_n g - t)
             (K := ASAN_K) (b := RcIdentModel.nthb (g_in g) (Z.to_nat t)) (kq := kq);
             try (rewrite H10; f_equal; lia); try (rewrite H18, Hmin; f_equal; lia);
             try (rewrite H22, Hmin; reflexivity); try assumption; try (unfold ASAN_K; lia); try zlia;
             try (destruct Hokq as [Hk|Hk]; [left; exact Hk | right; lia]).
        -- intros ms' (x4 & x5 & m' & Ems & MU & WM & HB).
           rewrite (proj2 (Z.eqb_neq (6 - t) 1) ltac:(lia)) in Ems. subst ms'.
           do 3 eexists. split; [reflexivity|].
           exists (RcIdentModel.nthb (g_in g) (Z.to_nat t)).
           rewrite (Z.min_l (t + 1) (g_n g) ltac:(lia)).
           replace (6 - (t + 1)) with (6 - t - 1) by lia.
           replace (fr + 2624 + (t + 1)) with (fr + 2624 + t + 1) by lia.
           replace (g_n g - (t + 1)) with (g_n g - t - 1) by lia.
           replace (g_p g + (t + 1)) with (g_p g + t + 1) by lia.
           repeat (split; [b_kreg|]).
           split; [exact MU|]. split; [exact WM | exact HB].
      * assert (Hmin : Z.min t (g_n g) = g_n g) by lia.
        assert (Hv0 : RcIdentModel.nthb (g_in g) (Z.to_nat t) = Z_to_bv 8 0) by (apply b_nth_past; lia).
        unfold rs_hold in Hpc0n. destruct Hpc0n as [Epc | Hlt0]; [subst pc0 | exfalso; lia].
        eapply evt_mono.
        -- apply b_z_evt with (cnt := 6 - t) (d := fr + 2624 + t);
             try (rewrite H10; f_equal; lia); try assumption; try zlia.
           rewrite H18, Hmin. f_equal. lia.
        -- intros ms' (m' & Ems & MU & WM & HB).
           rewrite (proj2 (Z.eqb_neq (6 - t) 1) ltac:(lia)) in Ems. subst ms'.
           do 3 eexists. split; [reflexivity|].
           exists (Z_to_bv 8 0).
           rewrite Hmin in H18, H22.
           replace (g_n g - g_n g) with 0 in H18 by lia.
           rewrite (Z.min_r (t + 1) (g_n g) ltac:(lia)).
           replace (6 - (t + 1)) with (6 - t - 1) by lia.
           replace (fr + 2624 + (t + 1)) with (fr + 2624 + t + 1) by lia.
           replace (g_n g - g_n g) with 0 by lia.
           rewrite <- H22.
           split; [reflexivity|]. split; [symmetry; exact Hv0|].
           repeat (split; [b_kreg|]).
           split; [exact MU|]. split; [exact WM | exact HB].
    + intros R pc' mem' regs'' md' HK Hreg Hmat.
      destruct HK as (v & Hpc & Hv & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K25 & K24 & K20 & K17 & K27 & K16 & K11 &
                      K10 & K12 & K18 & K22 & MU & WM & HB).
      subst pc'.
      assert (HWcl : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside Wf x ->
                (fr + 24 <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
                (AC.aspZ regs - 16 <= x < AC.aspZ regs) \/
                (bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 168)).
      { intros x Hx Hno. left. unfold Wf in Hno. cbn [LF.outside] in Hno. lia. }
      assert (HRDf : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside Wf x -> exists b, mrd rsegs mem' (wa x) = Some b).
      { intros x Hx Hno. unfold Wf in Hno. cbn [LF.outside] in Hno.
        apply (b_ba_rd mem' (fr + 2624 + t) [v] x HB). cbn [length]. lia. }
      assert (HPresf : forall x, 0 <= x < 2 ^ 64 -> ~ LF.outside Wf x -> exists b, mbyte rsegs mem' x = Some b).
      { intros x Hx Hno. destruct (HRDf x Hx Hno) as (b & Hb). exists b. exact Hb. }
      destruct (b_ah g fr regs mem mem' md sel 0x41b58ab3 Wf HFRAS MU WM HWcl HPresf)
        as (HAH' & Hown & Hstk' & Hhi').
      assert (HSWm : shadow_rw mem').
      { apply (b_shadow_rw Wf mem mem' HSW0 MU WM). intros a Ha. left.
        unfold Wf. cbn [outside]. split; [|exact I].
        pose proof (b_sh_app_dj a (fr + 2624 + t) Ha (Happ' (fr + 2624 + t) ltac:(lia))). lia. }
      assert (HFRAS' : FRAS B APIf ra g fr [] regs'' mem' md sel).
      { unfold FRAS. apply (b_frah g fr regs regs'' mem mem' md sel 0x41b58ab3 Wf HFRAS MU WM HDJf HSWm
          HAH' Hstk' HWcl HRDf);
          [rewrite Hreg; exact K2 | rewrite Hreg; exact K3 | rewrite Hreg; exact K4
          | rewrite Hreg; exact K8 | rewrite Hreg; exact K9 | rewrite Hreg; exact K19
          | rewrite Hreg; exact K26]. }
      assert (HENT1 : ENT APIf g [] mem' md).
      { apply (b_ent g fr regs mem mem' md sel 0x41b58ab3 Wf HENT HFRAS MU); [| exact Hstk' | exact Hhi' |].
        - intros x Hx. destruct (b_out_dec Wf x) as [Ho|Hno]; [left; exact Ho|].
          right; right; left. unfold Wf in Hno. cbn [LF.outside] in Hno. lia.
        - intros a Hin Ho. exact (proj2 (Hown a) Ho). }
      assert (HENT' : ENT APIf g [] mem' md') by exact (ent_mat APIf g [] mem' md md' HENT1 Hmat).
      assert (HFRASm : FRAS B APIf ra g fr [] regs'' mem' md' sel).
      { unfold FRAS, FRAH in HFRAS' |- *.
        destruct HFRAS' as (A1 & sp1 & HRT1 & HAH1 & Hro1 & Hsn1 & Hhalt1 & Hrest1).
        destruct (lw_mat_le (APIf rc) ([] ++ g_H g) mem' md md' Hmat)
          as [HAHm _ Hstklo_eq _].
        destruct Hrest1 as (Hgimg1 & Hr21' & Hspm1 & Haspz1 & Hstklo1 & Hrest1).
        destruct Hrest1 as (Hr41 & Hr81 & Hr91 & Hr31 & Hr191 & Hr261 & Hfrm1 & Hsel1 & HAm1 & HAS1 & Hspa1 &
          Hfa1 & HA4481 & HS41 & HAPP1 & Hspill1 & Hloc1 & Hrest1).
        exists A1, sp1.
        split; [exact (AsanRTInv.RT_any sp1 sp1 mem' md md' HRT1)|].
        split; [exact (HAHm HAH1)|].
        split; [exact Hro1|].
        split; [destruct Hsn1 as (He & Hh & Hf); split; [exact He|];
                split; [exact Hh|]; rewrite (sl_mat_fds md md' Hmat); exact Hf|].
        split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt1|].
        split; [exact Hgimg1|]. split; [exact Hr21'|]. split; [exact Hspm1|]. split; [exact Haspz1|].
        split; [rewrite Hstklo_eq; exact Hstklo1|].
        split; [exact Hr41|]. split; [exact Hr81|]. split; [exact Hr91|]. split; [exact Hr31|].
        split; [exact Hr191|]. split; [exact Hr261|]. split; [exact Hfrm1|]. split; [exact Hsel1|].
        split; [exact HAm1|]. split; [exact HAS1|]. split; [exact Hspa1|]. split; [exact Hfa1|].
        split; [exact HA4481|]. split; [exact HS41|]. split; [exact HAPP1|]. split; [exact Hspill1|].
        split; [|exact Hrest1].
        destruct Hloc1 as [[H0 [Hspfr Hreal]]|[Hfr0' Hfs]].
        - left. split; [exact H0|]. split; [exact Hspfr|]. intros a Ha. rewrite Hstklo_eq. exact (Hreal a Ha).
        - right. split; [exact Hfr0' | exact Hfs]. }
      rewrite <- SEGS. apply (Hnext ltac:(lia)).
      exists regs'', mem', md', fr, sel.
      split; [reflexivity|]. split; [exact HFRASm|]. split; [exact HENT'|].
      assert (Hspk : forall off w, 32 <= off <= 440 -> spill regs mem off w -> spill regs'' mem' off w).
      { intros off w Hoff (A1 & HA1 & Hq).
        assert (HA1e : A1 = A).
        { unfold rg in HA1. pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb.
          rewrite length_le8 in Hb.
          pose proof (rg_eq64 regs 9 A1 A HA1 ltac:(unfold rg; exact Hr9)) as Hm.
          change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
        subst A1. exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9|].
        unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
        rewrite length_le8. intros x Hx. unfold Wf. cbn [LF.outside]. split; [lia | exact I]. }
      (* PRA (A4's spills) is kept by the turn (it writes one our[] byte) *)
      cbv beta. split; cycle 1.
      { unfold PRA.
        split; [exact (Hspk 136 (fr + 160) ltac:(lia) P136)|].
        split; [exact (Hspk 280 (fr + 176) ltac:(lia) P280)|].
        split; [exact (Hspk 168 (fr + 2880) ltac:(lia) P168)|].
        split; [exact (Hspk 192 (fr + 528) ltac:(lia) P192)|].
        split; [exact (Hspk 200 (fr + 336) ltac:(lia) P200)|].
        split; [exact (Hspk 216 (fr + 448) ltac:(lia) P216)|].
        split; [exact (Hspk 104 (fr + 128) ltac:(lia) P104)|].
        split; [exact (Hspk 288 (fr + 256) ltac:(lia) P288)|].
        split; [exact (Hspk 296 (fr + 304) ltac:(lia) P296)|].
        split; [exact (Hspk 304 (fr + 272) ltac:(lia) P304)|].
        exact (Hspk 168 (fr + 2880) ltac:(lia) P168b). }
      unfold LOOPB, rg, spill, q64.
      split; [exact Hgn|]. split; [lia|].
      split; [rewrite Hreg, K24; exact Hr24|].
      split; [rewrite Hreg, K25; exact Hr25|].
      split; [exact (Hspk 144 (fr + 2176) ltac:(lia) L144)|].
      split; [exact (Hspk 112 (fr + 2256) ltac:(lia) L112)|].
      split; [exact (Hspk 312 (fr + 544) ltac:(lia) L312)|].
      split; [exact (Hspk 264 (fr + 2624) ltac:(lia) L264)|].
      split; [rewrite Hreg, K20; exact H20|].
      split; [rewrite Hreg; exact K10|].
      split; [rewrite Hreg, K11; exact H11|].
      split; [rewrite Hreg; exact K12|].
      split; [rewrite Hreg, K17; exact H17|].
      split; [rewrite Hreg; exact K18|].
      split; [rewrite Hreg; exact K22|].
      split; [rewrite Hreg, K27; exact H27|].
      split; [exact (Hspk 56 (fr + 3040) ltac:(lia) L56)|].
      split; [exact (Hspk 184 (fr + 2368) ltac:(lia) L184)|].
      split; [exact (Hspk 176 (fr + 2688) ltac:(lia) L176)|].
      split; [exact (Hspk 208 (fr + 2768) ltac:(lia) L208)|].
      split.
      { apply (b_addr_keep Wf mem mem' (fr + 2624) 6 HAour MU). intros i Hi.
        rewrite (b_sh_our fr i Hfrm8 ltac:(lia)).
        assert (Hin : in_shadow (Sfr fr + 328)).
        { rewrite <- (b_sh_our fr 0 Hfrm8 ltac:(lia)). apply shadow_of_app. apply Happ'. lia. }
        pose proof (b_sh_app_dj (Sfr fr + 328) (fr + 2624 + t) Hin (Happ' (fr + 2624 + t) ltac:(lia))).
        unfold Wf. cbn [LF.outside]. split; [lia | exact I]. }
      split; [exact (Hspk 96 (decl_slot fr) ltac:(lia) L96)|].
      split; [exact (Hspk 120 (fr + 2528) ltac:(lia) L120)|].
      split; [exact (Hspk 240 (fr + 2448) ltac:(lia) L240)|].
      split; [exact (Hspk 232 (fr + 2464) ltac:(lia) L232)|].
      split; [exact (Hspk 224 (fr + 2496) ltac:(lia) L224)|].
      split; [exact (Hspk 64 (fr + 3056) ltac:(lia) L64)|].
      split.
      { destruct (Z_le_gt_dec (g_n g) 0) as [Hz|Hz].
        - (* the empty input: the byte list is nil, so the fact is the same in any memory *)
          assert (Hnil : g_in g = []).
          { unfold g_n, nlen in Hz. destruct (g_in g) as [|b0 l]; [reflexivity | cbn [length] in Hz; lia]. }
          destruct HINB as (HB1 & HB2 & HB3). split; [exact HB1|]. split; [exact HB2|].
          intros i Hi. rewrite Hnil in Hi. cbn [length] in Hi. lia.
        - apply (bytes_at_transport rsegs Wf mem mem' _ _ HINB MU).
          rewrite <- Hlen. unfold Wf. cbn [disjoint_from]. split; [|exact I].
          destruct (Hdj ltac:(lia)) as [H|H]; [left | right]; lia. }
      split.
      { intros Hn0. destruct (HIN Hn0) as (HInH & HADp). split; [exact HInH|].
        apply (b_addr_keep Wf mem mem' (g_p g) (g_n g) HADp MU). intros i Hi.
        unfold Wf. cbn [LF.outside]. split; [|exact I].
        pose proof (b_sh_app_dj (shadow_addr (g_p g + i)) (fr + 2624 + t)
                      ltac:(apply shadow_of_app; destruct HADp as (_ & _ & _ & Hb);
                            exact (proj1 (Hb i Hi)))
                      (Happ' (fr + 2624 + t) ltac:(lia))). lia. }
      split.
      { exists (tl junk). split.
        { destruct junk as [|b0 junk']; cbn [length tl] in *; lia. }
        { pose proof (b_our_keep mem mem' (fr + 2624) t _ junk v HOUR HPRElen ltac:(lia) ltac:(lia) MU HB) as HH.
          rewrite Hv in HH. rewrite <- (b_our_step (g_in g) (Z.to_nat t) ltac:(lia)) in HH.
          replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia. exact HH. } }
      rewrite Hreg, K16. exact H16.
Qed.

(* One turn from the head. *)
Lemma b_turn : forall t,
  (t < 5 -> Hat B APIf ra (Inv_B81548_at B APIf ra) (t + 1)) ->
  Hcut B APIf ra (Inv_B81cb0 B APIf ra) ->
  Hcut B APIf ra (Inv_B815fc B APIf ra) ->
  Hat B APIf ra (Inv_B81548_at B APIf ra) t.
Proof.
  intros t Hnext HP3 HR2 g c (regs & mem & md & fr & sel & Ec & HF & HE & HB & HP).
  apply (b_turn_gen t 0x81548 Hnext HP3 HR2 g c).
  exists regs, mem, md, fr, sel. split; [exact Ec|]. split; [exact HF|]. split; [exact HE|].
  split; [exact HB|]. split; [exact HP | left; reflexivity].
Qed.

(* The loop, closed by induction on the turns left (5 - t): every head cut reaches P3 or R2. *)
Lemma b_loop : Hcut B APIf ra (Inv_B81cb0 B APIf ra) -> Hcut B APIf ra (Inv_B815fc B APIf ra) ->
  forall t, Hat B APIf ra (Inv_B81548_at B APIf ra) t.
Proof.
  intros HP3 HR2.
  assert (Hk : forall k t, Z.to_nat (5 - t) = k -> Hat B APIf ra (Inv_B81548_at B APIf ra) t).
  { induction k as [|k IH]; intros t Ek; apply b_turn; try exact HP3; try exact HR2; intros Ht.
    - exfalso. lia.
    - apply IH. lia. }
  intros t. exact (Hk _ t eq_refl).
Qed.

(* S_A5 (forms-asan-ubsan-v190.md), on SlotInv.v's official cuts.  The body cut 0x81550 is not used: the loop's
   back edge returns to the head, whose turns this file proves itself (b_loop). *)
Lemma seg_A5 : forall t : Z, Hcut B APIf ra (Inv_B81550 B APIf ra) -> Hcut B APIf ra (Inv_B815fc B APIf ra) -> Hcut B APIf ra (Inv_B81cb0 B APIf ra) -> Hat B APIf ra (Inv_B81548_at B APIf ra) t.
Proof. intros t _ HR2 HP3. exact (b_loop HP3 HR2 t). Qed.

End A5.
