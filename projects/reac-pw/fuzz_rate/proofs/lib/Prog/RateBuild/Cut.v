(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 218 of its 245 lines of code are new or changed and 547 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 366 of its 391 lines of code are new or changed and 220 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/RoleBuild/Pre.v, with its module paths and module names changed; 226 of its 250 lines of code are new or changed and 367 lines of the source are left out. *)
(** The cuts of the inlined pod builder of LLVMFuzzerTestOneInput (plain image, [0x13158, 0x141e0)): the states its
    pieces hand each other, and the pieces stated apart from their proofs. Ported from reac-pw/fuzz_role's
    Prog/RoleBuild/Cut.v at rate's registers, frame cells and pcs.

    The builder writes one object into the first block. Its state at a cut is the record so far (Pod/Model.v
    [pb_cut]: the shape, the properties written, and, inside a params Struct, the pods written), the input left, and
    the loop counters; the block holds [Layout.pc_image] of that state, the frame's cells hold the loop's constants
    and counters, and the registers hold what the next piece reads. Unlike fuzz_role, the harness keeps seven header
    values live across the builder (fuzz_rate.c:236-239: flags, mask, buflen, the four bytes of other): inside the
    property loop they sit in the frame's seven low cells [sp, sp + 0x38) ([HDR]: spilled at 0x13188 and
    0x132b4-0x132c4, reloaded at 0x140f4-0x14108), and at the end cut in registers. The predicates below name those
    states:

      [PROPH] the property loop's head 0x13334 after i properties;
      [PROPL] its latch 0x140e4 after the i-th property was written;
      [CNTH]  the pod loop's head 0x13564 of a params Struct after k pods (rb_ent_contract's entry);
      [CNTJ]  its join 0x13cec, where the inlined pod_write_ent begins (rb_ent_contract's exit);
      [CNTL]  its latch 0x13df8, the pod written and, for the first params Struct, recorded;
      [POSTH] 0x14114, every property written, the top size word about to be patched;
      [QBrec] rate_build_contract's postcondition for the record the builder made.

    Frame cells (role's cell + 0x30, except the header): [sp, sp + 0x38) the header (b5, mask, b3, fl, buflen,
    b6 << 8, b4 << 8), 0x38 SPA_PROP_volume's key word 0x10003, 0x40 the shape test (shape = 7), 0x48 nprops, 0x50
    SPA_PROP_params' key word 0x80001, 0x58 the cursor spill of the text kinds, 0x60 seen_params, 0x68 &pp->ent,
    0x70 &pp->n_ent, 0x78 the property index, 0x80 pp, 0x88 the pod count, 0x90 -0x4001, 0x98 -0x3ffd, 0xa0 `first`,
    0xa8 the input left after a pod, 0xb0 &pp->len, e [0xb8, 0x120), parts 0x120, ch[24] 0x140, t[96] 0x158.

    Statement text only: no function is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** The pcs of the builder's cuts. *)
Definition PROP_HEAD : Z := 0x13334.
Definition PROP_LATCH : Z := 0x140e4.
Definition CNT_HEAD : Z := 0x13564.
Definition CNT_JOIN : Z := 0x13cec.
Definition CNT_LATCH : Z := 0x13df8.
Definition CNT_EXIT : Z := 0x14088.
Definition PROP_CLOSE : Z := 0x140a0.
Definition POST_HEAD : Z := 0x14114.

(** The multiplier of `v / 10` the preheader leaves in s4 (0x132d4, 0x132fc, 0x1331c). *)
Definition MULT10 : Z := 0xcccccccd * 2 ^ 32.
(** The head-amp key's part clamp (s0) and the divisor (s3). *)
Definition S8V : Z := 95.
Definition S10V : Z := 10.

(** The first SPA_PROP_params property is the one whose pods are recorded in ent[] (pod.h:409). *)
Definition seen_of (ps : list (Z * pval)) : bool := existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps.
Definition first_of (ps : list (Z * pval)) : bool := negb (seen_of ps).

(** A record the property loop can have built: what [Model.pod_rec_wf] asks of its parts. *)
Definition pc_wf (sh : Z) (ps : list (Z * pval)) : Prop :=
  0 <= sh < 8 /\ Forall (fun kv => 0 <= fst kv < 2^32 /\ pval_wf (snd kv)) ps /\
  Forall ent_wf (all_ents ps) /\ (length ps <= 3)%nat.

(** The offset of the open Struct's size word: the property's key and flags are already written. *)
Definition at_of (sh : Z) (ps : list (Z * pval)) : Z := Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8.

(** The seven header values as the frame's low cells hold them inside the property loop: sp + 0 = b5, sp + 8 = mask,
    sp + 0x10 = b3, sp + 0x18 = fl, sp + 0x20 = buflen, sp + 0x28 = b6 << 8, sp + 0x30 = b4 << 8. *)
Definition hdr_bytes (fl mask buflen b3 b4 b5 b6 : Z) : list byte :=
  le8 (Z_to_bv 64 b5) ++ le8 (Z_to_bv 64 mask) ++ le8 (Z_to_bv 64 b3) ++ le8 (Z_to_bv 64 fl) ++
  le8 (Z_to_bv 64 buflen) ++ le8 (Z_to_bv 64 (b6 * 256)) ++ le8 (Z_to_bv 64 (b4 * 256)).

Lemma length_hdr_bytes : forall fl mask buflen b3 b4 b5 b6, length (hdr_bytes fl mask buflen b3 b4 b5 b6) = 56%nat.
Proof. intros. unfold hdr_bytes. rewrite !length_app, !length_le8. reflexivity. Qed.

Section Cuts.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z).

(** An 8-byte frame cell holding v. *)
Definition cell8 (m1 : word -> option byte) (a v : Z) : Prop :=
  bytes_at rsegs m1 a (le8 (Z_to_bv 64 v)).

(** The header cells, as one run of 56 bytes (a store elsewhere in the frame carries it as any other run). *)
Definition HDR (m1 : word -> option byte) : Prop :=
  bytes_at rsegs m1 (bv_unsigned sp) (hdr_bytes fl mask buflen b3 b4 b5 b6).

Lemma HDR_cells : forall m1, HDR m1 ->
  cell8 m1 (bv_unsigned sp) b5 /\ cell8 m1 (bv_unsigned sp + 0x8) mask /\ cell8 m1 (bv_unsigned sp + 0x10) b3 /\
  cell8 m1 (bv_unsigned sp + 0x18) fl /\ cell8 m1 (bv_unsigned sp + 0x20) buflen /\
  cell8 m1 (bv_unsigned sp + 0x28) (b6 * 256) /\ cell8 m1 (bv_unsigned sp + 0x30) (b4 * 256).
Proof.
  intros m1 H. unfold HDR, hdr_bytes, cell8 in *.
  apply bytes_at_app in H as [C0 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [C8 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [C10 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [C18 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [C20 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [C28 C30]. rewrite length_le8 in C30.
  replace (bv_unsigned sp + Z.of_nat 8) with (bv_unsigned sp + 0x8) in * by lia.
  replace (bv_unsigned sp + 0x8 + Z.of_nat 8) with (bv_unsigned sp + 0x10) in * by lia.
  replace (bv_unsigned sp + 0x10 + Z.of_nat 8) with (bv_unsigned sp + 0x18) in * by lia.
  replace (bv_unsigned sp + 0x18 + Z.of_nat 8) with (bv_unsigned sp + 0x20) in * by lia.
  replace (bv_unsigned sp + 0x20 + Z.of_nat 8) with (bv_unsigned sp + 0x28) in * by lia.
  replace (bv_unsigned sp + 0x28 + Z.of_nat 8) with (bv_unsigned sp + 0x30) in * by lia.
  tauto.
Qed.

Lemma HDR_of_cells : forall m1,
  cell8 m1 (bv_unsigned sp) b5 -> cell8 m1 (bv_unsigned sp + 0x8) mask -> cell8 m1 (bv_unsigned sp + 0x10) b3 ->
  cell8 m1 (bv_unsigned sp + 0x18) fl -> cell8 m1 (bv_unsigned sp + 0x20) buflen ->
  cell8 m1 (bv_unsigned sp + 0x28) (b6 * 256) -> cell8 m1 (bv_unsigned sp + 0x30) (b4 * 256) -> HDR m1.
Proof.
  intros m1 C0 C8 C10 C18 C20 C28 C30. unfold HDR, hdr_bytes, cell8 in *.
  apply bytes_at_app. split; [exact C0|]. rewrite length_le8.
  apply bytes_at_app. split; [replace (bv_unsigned sp + Z.of_nat 8) with (bv_unsigned sp + 0x8) by lia; exact C8|].
  rewrite length_le8.
  apply bytes_at_app. split; [replace (bv_unsigned sp + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + 0x10) by lia;
                              exact C10|].
  rewrite length_le8.
  apply bytes_at_app.
  split; [replace (bv_unsigned sp + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + 0x18) by lia;
          exact C18|].
  rewrite length_le8.
  apply bytes_at_app.
  split; [replace (bv_unsigned sp + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + 0x20)
            by lia; exact C20|].
  rewrite length_le8.
  apply bytes_at_app.
  split; [replace (bv_unsigned sp + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)
            with (bv_unsigned sp + 0x28) by lia; exact C28|].
  rewrite length_le8.
  replace (bv_unsigned sp + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)
    with (bv_unsigned sp + 0x30) by lia. exact C30.
Qed.

(** The cells the preheader sets once and no piece writes again (0x13180-0x13184, 0x132a8, 0x13308-0x13328). *)
Definition CFIX (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp + 0x38) POD_PROP_VOLUME /\
  cell8 m1 (bv_unsigned sp + 0x50) POD_PROP_PARAMS /\
  cell8 m1 (bv_unsigned sp + 0x68) (pp + OFF_ENT) /\
  cell8 m1 (bv_unsigned sp + 0x70) (pp + POD_NENT_OFF) /\
  cell8 m1 (bv_unsigned sp + 0x80) pp /\
  cell8 m1 (bv_unsigned sp + 0x90) (-0x4001) /\
  cell8 m1 (bv_unsigned sp + 0x98) (-0x3ffd) /\
  cell8 m1 (bv_unsigned sp + 0xb0) (pp + POD_LEN_OFF).

(** The input left: a suffix of the builder's input, and the cursor that names it. *)
Definition suffix (r : list byte) : Prop := exists k, (k <= length rest)%nat /\ r = skipn k rest.
Definition cur (r : list byte) : Z := src + Z.of_nat (length rest) - Z.of_nat (length r).

(** ** The property loop's head 0x13334, i properties written *)
Definition PROPH (sh np : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t1 a0 a2 a3 a4 s2 s7 s8 s9 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp (Z_to_bv 64 (-0x4001)) t1 (Z_to_bv 64 np)
                 (Z_to_bv 64 S8V) (Z_to_bv 64 pp)
                 a0 (Z_to_bv 64 (Z.of_nat (length ps))) a2 a3 a4 (Z_to_bv 64 (Z.b2z (sh =? 7)))
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (-0x3ffd))
                 s2 (Z_to_bv 64 S10V) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat (length r))) s7 s8 s9
                 (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120))
                 (Z_to_bv 64 (Z.b2z (seen_of ps))) t4 t5 t6)
             F (Z_to_bv 64 PROP_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\
    HDR m1 /\ cell8 m1 (bv_unsigned sp + 0x48) np /\
    cell8 m1 (bv_unsigned sp + 0x40) (Z.b2z (sh =? 7)) /\
    suffix r /\ pc_wf sh ps.

(** ** The property loop's latch 0x140e4, the i-th property written (a1 is still i) *)
Definition PROPL (sh np : Z) (i : nat) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t1 a0 a2 a3 a4 s2 s7 s8 s9 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp (Z_to_bv 64 (-0x4001)) t1 (Z_to_bv 64 np)
                 (Z_to_bv 64 S8V) (Z_to_bv 64 pp)
                 a0 (Z_to_bv 64 (Z.of_nat i)) a2 a3 a4 (Z_to_bv 64 (Z.b2z (sh =? 7)))
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (-0x3ffd))
                 s2 (Z_to_bv 64 S10V) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat (length r))) s7 s8 s9
                 (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120))
                 (Z_to_bv 64 (Z.b2z (seen_of ps))) t4 t5 t6)
             F (Z_to_bv 64 PROP_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\
    HDR m1 /\ cell8 m1 (bv_unsigned sp + 0x48) np /\
    cell8 m1 (bv_unsigned sp + 0x40) (Z.b2z (sh =? 7)) /\
    suffix r /\ pc_wf sh ps /\ (length ps = S i)%nat.

(** The cells of the property being written: the header, nprops, the shape test, `seen_params` (always set inside a
    params Struct), the property index, the pod count and `first`. *)
Definition CVAR (np : Z) (sh : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z)
    (m1 : word -> option byte) : Prop :=
  HDR m1 /\ cell8 m1 (bv_unsigned sp + 0x48) np /\
  cell8 m1 (bv_unsigned sp + 0x40) (Z.b2z (sh =? 7)) /\
  cell8 m1 (bv_unsigned sp + 0x60) 1 /\
  cell8 m1 (bv_unsigned sp + 0x78) (Z.of_nat i) /\
  cell8 m1 (bv_unsigned sp + 0x88) cnt /\
  cell8 m1 (bv_unsigned sp + 0xa0) (Z.b2z (first_of ps)).

(** ** The pod loop's head 0x13564, k pods of the open Struct written (rb_ent_contract's entry) *)
Definition CNTH (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 S8V) (Z_to_bv 64 pp)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (at_of sh ps))
                 (Z_to_bv 64 S10V) (Z_to_bv 64 MULT10) s5 (Z_to_bv 64 (Z.of_nat (length r))) s7
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat k))
                 (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120)) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf es /\ (length es = k)%nat /\ (k < 32)%nat /\
    (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** The pod loop's join 0x13cec, the pod built (rb_ent_contract's exit) *)
Definition CNTJ (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp (Z_to_bv 64 (-0x4001)) t1 t2
                 (Z_to_bv 64 S8V) (Z_to_bv 64 pp)
                 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (-0x3ffd))
                 (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 S10V) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (e_type e)) (Z_to_bv 64 (e_size e)) (Z_to_bv 64 POD_LEN_OFF) (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 (Z.of_nat k))
                 (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120)) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_JOIN) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    cell8 m1 (bv_unsigned sp + 0xa8) (Z.of_nat (length r)) /\
    bytes_at rsegs m1 (bv_unsigned sp + 0xb8) (ent_mem e) /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf es /\ (length es = k)%nat /\ (k < 32)%nat /\
    ent_wf e /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** The pod loop's latch 0x13df8, the pod written into the buffer and, when this Struct is the first
       SPA_PROP_params property, copied into ent[n_ent++] *)
Definition CNTL (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s5 s7 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 S8V) (Z_to_bv 64 pp)
                 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + POD_LEN_OFF)) a7 (Z_to_bv 64 (at_of sh ps))
                 (Z_to_bv 64 S10V) (Z_to_bv 64 MULT10) s5 (Z_to_bv 64 (Z.of_nat (length r))) s7
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat k))
                 (Z_to_bv 64 (bv_unsigned sp + 0x158)) (Z_to_bv 64 (bv_unsigned sp + 0x120)) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some (es ++ [e])))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf (es ++ [e]) /\ (length es = k)%nat /\
    (k < 32)%nat /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** 0x14114: every property written, the top size word still 0; the header values back in registers (s6 = fl,
       s9 = mask, s10 = buflen, s7 = b3, s2 = b4 << 8, s11 = b5) and the cell sp + 0x28 = b6 << 8 *)
Definition POSTH (sh : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t2 s0 a0 a1 a2 a3 a4 a5 a7 s3 s8 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2 s0 (Z_to_bv 64 pp) a0 a1 a2 a3 a4 a5
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) a7 (Z_to_bv 64 (b4 * 256)) s3
                 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))) (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 fl) (Z_to_bv 64 b3) s8 (Z_to_bv 64 mask) (Z_to_bv 64 buflen) (Z_to_bv 64 b5)
                 t3 t4 t5 t6)
             F (Z_to_bv 64 POST_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\
    cell8 m1 (bv_unsigned sp + 0x28) (b6 * 256) /\ cell8 m1 (bv_unsigned sp + 0x70) (pp + POD_NENT_OFF) /\
    cell8 m1 (bv_unsigned sp + 0x80) pp /\ cell8 m1 (bv_unsigned sp + 0xb0) (pp + POD_LEN_OFF) /\
    suffix r /\ pc_wf sh ps.

(** ** Where the first piece ends: the property loop's head, or the end when the object has no property *)
Definition PREQ (sh np : Z) (r : list byte) : machine_state -> Prop :=
  fun ms => (np = 0 /\ POSTH sh [] r ms) \/ (np <> 0 /\ PROPH sh np [] r ms).

(** ** rate_build_contract's postcondition, for the record the builder made *)
Definition QBrec (rec : pod_rec) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s8' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pp)
                  (Z_to_bv 64 (Z.of_nat (length (buf rec)))) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (b4 * 256)) s3' (Z_to_bv 64 (Z.of_nat (length (buf rec)))) s5'
                  (Z_to_bv 64 fl) (Z_to_bv 64 b3) s8' (Z_to_bv 64 mask) (Z_to_bv 64 buflen) (Z_to_bv 64 b5)
                  t3' t4' t5' t6')
              F (Z_to_bv 64 RATE_MALLOC2) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes rec) /\
    cell8 m' (bv_unsigned sp + 0x28) (b6 * 256) /\ cell8 m' (bv_unsigned sp + 0x70) (pp + POD_NENT_OFF) /\
    cell8 m' (bv_unsigned sp + 0x80) pp /\ cell8 m' (bv_unsigned sp + 0xb0) (pp + POD_LEN_OFF) /\
    munch (W0 sp pp) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

(** ** The pieces stated apart from their proofs *)
(** 0x14114 -> 0x141e0: the top size word (pod.h:440), the corruption (pod.h:441-448) and the request of
    fuzz_dup (fuzz.h:73). *)
Definition S_post : Prop :=
  BOK sp rest src pp lo ->
  forall (sh : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    POSTH sh ps r ms ->
    evt rsegs
      (QBrec (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)))) ms.

(** 0x13334 -> 0x140e4: one property of the object (pod.h:399-438), the pod loop of a params Struct included. *)
Definition S_prop : Prop :=
  BOK sp rest src pp lo ->
  forall (sh np : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    PROPH sh np ps r ms -> Z.of_nat (length ps) < np -> np <= 3 -> bv_unsigned sp mod 16 = 0 ->
    evt rsegs (PROPL sh np (length ps) (ps ++ [fst (prop_step sh r)]) (snd (prop_step sh r))) ms.

(** 0x13cec -> 0x13df8: the inlined pod_write_ent (pod.h:428-430) and the record copy (pod.h:431-432). *)
Definition S_write : Prop :=
  BOK sp rest src pp lo ->
  forall (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
         (e : ent) (r : list byte) (ms : machine_state),
    CNTJ sh np ps i cnt es k e r ms -> evt rsegs (CNTL sh np ps i cnt es k e r) ms.

End Cuts.

(** 0x13158 -> 0x13334 or 0x14114: the NULL test, memset of the block, the header spills, the shape and nprops reads,
    the object header and the property loop's preheader (pod.h:384-398). Same premises as rate_build_contract. *)
Definition S_pre : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s5 = Z_to_bv 64 src -> s0 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s6 = Z_to_bv 64 fl -> s9 = Z_to_bv 64 mask -> s10 = Z_to_bv 64 buflen -> s7 = Z_to_bv 64 b3 ->
    bytes_at rsegs m (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 (b4 * 256))) ->
    s11 = Z_to_bv 64 b5 -> s4 = Z_to_bv 64 (b6 * 256) ->
    0 <= fl < 256 -> 0 <= mask < 256 -> 0 <= buflen < 24 ->
    0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
    s3 = Z_to_bv 64 POD_PROPS -> s1 = Z_to_bv 64 0x5000 ->
    0 < src -> bytes_at rsegs m src rest ->
    rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] ->
    (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) ->
    (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) ->
    src + Z.of_nat (length rest) <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs (PREQ sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo
                 (fst (fuzz_u8 rest) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4)
                 (snd (fuzz_u8 (snd (fuzz_u8 rest)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_BUILD) fc None m (seg_rom rsegs)).
