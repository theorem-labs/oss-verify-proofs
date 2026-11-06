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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Prog/RateBuild/Cut.v, with its module paths and addresses changed; 132 of its 201 lines of code are new or changed and 181 lines of the source are left out. *)
(** The cuts of the inlined pod builder of LLVMFuzzerTestOneInput (UBSan image, [0x13110, 0x14208)): the states
    its pieces hand each other, and the pieces proved apart from the walk that chains them. The form is
    reac-pw/fuzz_role's U/Prog/RoleBuild/Cut.v, re-walked at rate's
    registers, frame cells and addresses (liveness by a backward pass).

    The builder writes one object into the first block. Its state at a cut is the record so far (Pod/Model.v
    [pb_cut]: the shape, the properties written, and, inside a params Struct, the pods written), the input left, and
    the loop counters; the block holds [Layout.pc_image] of that state, the frame's cells hold the loop's constants,
    the counters and the seven header values of fuzz_rate.c:236-239, and the registers hold what the next piece
    reads. The predicates below name those states:

      [PROPH]  the property loop's head 0x1333c before property i (i = the properties written);
      [PKEY]   0x13450, property i's selector read and its key and flags written (shape <> 7);
      [PROPL]  its latch 0x140c8 after property i was written (a7 is still i);
      [CNTH]   the pod loop's head 0x13560 of a params Struct after k pods (EntCut.rb_ent_contract's entry);
      [CNTJ]   its join 0x13ee4, the pod built in e (rb_ent_contract's exit), before the stop test of pod.h:428;
      [CNTL]   its latch 0x13f48, the pod written by pod_write_ent and, for the first params Struct, recorded;
      [PCLOSE] 0x14080, the params Struct's pods all written, its size word about to be patched (pod.h:434);
      [POSTH]  0x140e0, every property written, the top size word about to be patched (pod.h:440);
      [QBrec]  rate_build_contract's postcondition for the record the builder made.

    The registers that hold the loops' constants (set by the preheader 0x132ac-0x13338): s0 = sp + 0x188 (t[96]),
    s1 = 4 (the Int type and size), s2 = 95 (the head-amp key's part clamp), s4 = 0xcccccccd << 32 (the multiplier
    of v / 10), s5 = 10; in the property loop also s6 = ~pp (the pointer-overflow bound of the puts),
    s8 = pp, s11 = pp + 0x4000 = &pp->len, a7 = i, s3 = seen_params (s9 at the latch), s7 = the cursor and t1 = the
    bytes left; in the pod loop s3 = k, s6 = 0x4000, s9 = the cursor and s10 = the bytes left (t1 at the join).
    The frame cells: [CFIX] (set once by the preheader), [CPROP] (flags, nprops, shape and the six header values
    [CHDR] that cross the builder: rate_build_contract hands them back) and, in a params Struct, [CVAR].

    Statement text only: no function is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** The pcs of the builder's cuts. *)
Definition PROP_HEAD : Z := 0x1333c.
Definition PROP_KEY : Z := 0x13450.
Definition PROP_LATCH : Z := 0x140c8.
Definition CNT_HEAD : Z := 0x13560.
Definition CNT_JOIN : Z := 0x13ee4.
Definition CNT_LATCH : Z := 0x13f48.
Definition PROP_CLOSE : Z := 0x14080.
Definition POST_HEAD : Z := 0x140e0.

(** The multiplier of `v / 10` the preheader leaves in s4, the head-amp key's part clamp (s2), the offset of t[96]
    (s0 = sp + T_OFF), and the multiplier of `v / 3` (the cell sp + 0). *)
Definition MULT10 : Z := 0xcccccccd * 2 ^ 32.
Definition S2V : Z := 95.
Definition T_OFF : Z := 0x188.
Definition DIV3 : Z := 0x15555556.

(** The six header values the builder carries in the frame (fuzz_rate.c:237-239): mask = byte 1, buflen = byte 2
    mod 24, and the four bytes of `other`. *)
Record hdr : Type := Hdr { h_mask : Z; h_buflen : Z; h_b3 : Z; h_b4 : Z; h_b5 : Z; h_b6 : Z }.

(** The first SPA_PROP_params property is the one whose pods are recorded in ent[] (pod.h:409). *)
Definition seen_of (ps : list (Z * pval)) : bool := existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps.
Definition first_of (ps : list (Z * pval)) : bool := negb (seen_of ps).

(** A record the property loop can have built: what [Model.pod_rec_wf] asks of its parts. *)
Definition pc_wf (sh : Z) (ps : list (Z * pval)) : Prop :=
  0 <= sh < 8 /\ Forall (fun kv => 0 <= fst kv < 2^32 /\ pval_wf (snd kv)) ps /\
  Forall ent_wf (all_ents ps) /\ (length ps <= 3)%nat.

(** The offset of the open Struct's size word: the property's key and flags are already written. *)
Definition at_of (sh : Z) (ps : list (Z * pval)) : Z := Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8.

(** The property's key (pod.h:407). *)
Definition key_of (sel : Z) : Z := if sel mod 4 =? 0 then POD_PROP_VOLUME else POD_PROP_PARAMS.

(** The block after the key and the flags of property |ps|. *)
Definition kimg (sh : Z) (ps : list (Z * pval)) (sel : Z) : list byte :=
  pp_image (pc_buf (PbCut sh ps None) ++ le32 (key_of sel) ++ le32 0)
    (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
    (pc_ents (PbCut sh ps None)) false.

Section Cuts.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z) (H : hdr).

(** An 8-byte frame cell holding v. *)
Definition cell8 (m1 : word -> option byte) (a v : Z) : Prop :=
  bytes_at rsegs m1 a (le8 (Z_to_bv 64 v)).

(** The header values' cells (b3 at 0x131b8, mask at 0x13190; the others since before the builder). *)
Definition CHDR (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp + 0x8) (h_b3 H) /\
  cell8 m1 (bv_unsigned sp + 0x10) (h_mask H) /\
  cell8 m1 (bv_unsigned sp + 0x18) (h_b6 H * 256) /\
  cell8 m1 (bv_unsigned sp + 0x20) (h_b5 H) /\
  cell8 m1 (bv_unsigned sp + 0x28) (h_b4 H * 256) /\
  cell8 m1 (bv_unsigned sp + 0x30) (h_buflen H).

(** The cells the preheader sets once and no piece writes again (0x13284-0x13338): the multiplier of v / 3, ~pp,
    the two property keys, ~(sp + 0x170) (ch), &pp->ent[0] and its complement, &pp->n_ent, ~(sp + 0xf0) (e->body),
    the two constants of the pod_put capacity test, &pp->len and pp. *)
Definition CFIX (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp + 0x0) DIV3 /\
  cell8 m1 (bv_unsigned sp + 0x50) (Z.lnot pp) /\
  cell8 m1 (bv_unsigned sp + 0x58) POD_PROP_VOLUME /\
  cell8 m1 (bv_unsigned sp + 0x78) POD_PROP_PARAMS /\
  cell8 m1 (bv_unsigned sp + 0x80) (Z.lnot (bv_unsigned sp + 0x170)) /\
  cell8 m1 (bv_unsigned sp + 0x88) (pp + OFF_ENT) /\
  cell8 m1 (bv_unsigned sp + 0x90) (Z.lnot (pp + OFF_ENT)) /\
  cell8 m1 (bv_unsigned sp + 0x98) (pp + POD_NENT_OFF) /\
  cell8 m1 (bv_unsigned sp + 0xa0) (Z.lnot (bv_unsigned sp + 0xf0)) /\
  cell8 m1 (bv_unsigned sp + 0xb8) (-0x4001) /\
  cell8 m1 (bv_unsigned sp + 0xc0) (-0x3ffd) /\
  cell8 m1 (bv_unsigned sp + 0xc8) (pp + POD_LEN_OFF) /\
  cell8 m1 (bv_unsigned sp + 0xd8) pp.

(** The cells of the object: the flags byte (0x13294), nprops (0x1318c) and the shape (0x13144), and the header
    values. *)
Definition CPROP (sh np : Z) (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp + 0x38) fl /\ cell8 m1 (bv_unsigned sp + 0xa8) np /\
  cell8 m1 (bv_unsigned sp + 0xb0) sh /\ CHDR m1.

(** The cells of the params Struct being written: &buf[at] (0x13554), at (0x1350c), `seen_params` (always set
    inside a params Struct, 0x13510), the property index (0x13514), the pod count (0x13548) and `first`
    (0x13468). *)
Definition CVAR (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (m1 : word -> option byte) : Prop :=
  CPROP sh np m1 /\
  cell8 m1 (bv_unsigned sp + 0x40) (pp + at_of sh ps) /\
  cell8 m1 (bv_unsigned sp + 0x60) (at_of sh ps) /\
  cell8 m1 (bv_unsigned sp + 0x68) 1 /\
  cell8 m1 (bv_unsigned sp + 0x70) (Z.of_nat i) /\
  cell8 m1 (bv_unsigned sp + 0xd0) cnt /\
  cell8 m1 (bv_unsigned sp + 0xe0) (Z.b2z (first_of ps)).

(** The input left: a suffix of the builder's input, and the cursor that names it. *)
Definition suffix (r : list byte) : Prop := exists k, (k <= length rest)%nat /\ r = skipn k rest.
Definition cur (r : list byte) : Z := src + Z.of_nat (length rest) - Z.of_nat (length r).

(** ** The property loop's head 0x1333c, before property i = |ps| *)
Definition PROPH (sh np : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s9 s10 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2
                 (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
                 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat (length ps)))
                 (Z_to_bv 64 S2V) (Z_to_bv 64 (Z.b2z (seen_of ps))) (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
                 (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 (cur r)) (Z_to_bv 64 pp) s9 s10
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\ CPROP sh np m1 /\
    suffix r /\ pc_wf sh ps /\ 0 <= np < 4 /\ (length ps < Z.to_nat np)%nat.

(** ** 0x13450: the selector sel of property |ps| read (r is the input after it), the shape test passed
       (sh <> 7), the key and the flags put (a0 = sel, a1 = sel & 3, a5 = the length = at) *)
Definition PKEY (sh np : Z) (ps : list (Z * pval)) (r : list byte) (sel : Z) : machine_state -> Prop :=
  fun ms => exists (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s9 s10 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2
                 (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
                 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat (length ps)))
                 (Z_to_bv 64 S2V) (Z_to_bv 64 (Z.b2z (seen_of ps))) (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
                 (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 (cur r)) (Z_to_bv 64 pp) s9 s10
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_KEY) fc None m1 (seg_rom rsegs) /\
    a0 = Z_to_bv 64 sel /\ a1 = Z_to_bv 64 (Z.land sel 3) /\
    a5 = Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8) /\
    MBr sp m rest src pp lo (kimg sh ps sel) m1 /\ CFIX m1 /\ CPROP sh np m1 /\
    suffix r /\ pc_wf sh ps /\ 0 <= np < 4 /\ (length ps < Z.to_nat np)%nat /\ sh <> 7 /\ 0 <= sel < 256.

(** ** The property loop's latch 0x140c8, property i written (a7 is still i; seen_params in s9) *)
Definition PROPL (sh np : Z) (i : nat) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s3 s10 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2
                 (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
                 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat i))
                 (Z_to_bv 64 S2V) s3 (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
                 (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 (cur r)) (Z_to_bv 64 pp)
                 (Z_to_bv 64 (Z.b2z (seen_of ps))) s10
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\ CPROP sh np m1 /\
    suffix r /\ pc_wf sh ps /\ 0 <= np < 4 /\ length ps = S i /\ (length ps <= Z.to_nat np)%nat.

(** What the pod loop of a params Struct keeps: the record's parts, the open Struct is the (i+1)-th property
    of an object that is not a Struct, and the pods written so far. *)
Definition CNTP (sh np : Z) (ps : list (Z * pval)) (i : nat) (es : list ent) (r : list byte) : Prop :=
  suffix r /\ pc_wf sh ps /\ sh <> 7 /\ 0 <= np < 4 /\ length ps = i /\ (i < Z.to_nat np)%nat /\
  Forall ent_wf es.

(** ** The pod loop's head 0x13560, k pods of the open Struct written (rb_ent_contract's entry) *)
Definition CNTH (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 S2V) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
                 (Z_to_bv 64 POD_BUF_MAX) s7 s8 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat (length r)))
                 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR sh np ps i cnt m1 /\
    CNTP sh np ps i es r /\ length es = k /\ 0 <= cnt <= 32 /\ Z.of_nat k < cnt.

(** ** The pod loop's join 0x13ee4, pod k built in e at sp + 0xe8 (rb_ent_contract's exit) *)
Definition CNTJ (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2
                 (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 S2V) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
                 (Z_to_bv 64 POD_BUF_MAX) s7 (Z_to_bv 64 pp) (Z_to_bv 64 (cur r)) s10
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_JOIN) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR sh np ps i cnt m1 /\
    bytes_at rsegs m1 (bv_unsigned sp + 0xe8) (ent_mem e) /\ ent_wf e /\
    CNTP sh np ps i es r /\ length es = k /\ 0 <= cnt <= 32 /\ Z.of_nat k < cnt.

(** ** The pod loop's latch 0x13f48, pod k written into the buffer and, when this Struct is the first
       SPA_PROP_params property, copied into ent[n_ent++] (s3 is still k) *)
Definition CNTL (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 S2V) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
                 (Z_to_bv 64 POD_BUF_MAX) s7 (Z_to_bv 64 pp) (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some (es ++ [e])))) m1 /\ CFIX m1 /\ CVAR sh np ps i cnt m1 /\
    CNTP sh np ps i (es ++ [e]) r /\ length es = k /\ 0 <= cnt <= 32 /\ Z.of_nat k < cnt.

(** ** 0x14080: the params Struct's pods written, its size word at `at` still 0 (a0 = len, a4 = &buf[at],
       a5 = at, a7 = i, s9 = seen_params = 1; the cells 0x40, 0x60, 0x68, 0x70 and 0xd0 are not asked for: the
       path of an empty input comes here before it writes them) *)
Definition PCLOSE (sh np : Z) (ps : list (Z * pval)) (i : nat) (es : list ent) (r : list byte)
    : machine_state -> Prop :=
  fun ms => exists (ra t0 t2 a1 a2 a3 a6 s3 s10 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2
                 (Z_to_bv 64 (bv_unsigned sp + T_OFF)) (Z_to_bv 64 4)
                 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))))) a1 a2 a3
                 (Z_to_bv 64 (pp + at_of sh ps)) (Z_to_bv 64 (at_of sh ps)) a6 (Z_to_bv 64 (Z.of_nat i))
                 (Z_to_bv 64 S2V) s3 (Z_to_bv 64 MULT10) (Z_to_bv 64 10)
                 (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 (cur r)) (Z_to_bv 64 pp) (Z_to_bv 64 1) s10
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_CLOSE) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CPROP sh np m1 /\
    cell8 m1 (bv_unsigned sp + 0xe0) (Z.b2z (first_of ps)) /\
    CNTP sh np ps i es r /\ (length es <= 32)%nat.

(** ** 0x140e0: every property written, the top size word still 0 (s4 = len, s2 = fl; the nprops = 0 path
       comes here from 0x132a8, the loop's exit by 0x140d8-0x140dc) *)
Definition POSTH (sh : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s9 s10 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 fl) s3 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))) s5 s6
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 pp) s9 s10 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
             F (Z_to_bv 64 POST_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CHDR m1 /\
    cell8 m1 (bv_unsigned sp + 0x38) fl /\ cell8 m1 (bv_unsigned sp + 0x50) (Z.lnot pp) /\
    cell8 m1 (bv_unsigned sp + 0x98) (pp + POD_NENT_OFF) /\ cell8 m1 (bv_unsigned sp + 0xd8) pp /\
    suffix r /\ pc_wf sh ps.

(** ** rate_build_contract's postcondition, for the record the builder made *)
Definition QBrec (rec : pod_rec) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s9' s10'
                     t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (Z.of_nat (length (buf rec))))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 fl) s3' (Z_to_bv 64 (Z.of_nat (length (buf rec))))
                  s5' s6' s7' (Z_to_bv 64 pp) s9' s10' (Z_to_bv 64 (pp + POD_LEN_OFF)) t3' t4' t5' t6')
              F (Z_to_bv 64 RATE_MALLOC2) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes rec) /\ CHDR m' /\
    cell8 m' (bv_unsigned sp + 0x38) fl /\ cell8 m' (bv_unsigned sp + 0x98) (pp + POD_NENT_OFF) /\
    cell8 m' (bv_unsigned sp + 0xd8) pp /\
    munch (W0 sp pp) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

(** ** The pieces stated apart from the walk that chains them *)
(** 0x140e0 -> 0x14208: the top size word (pod.h:440), the corruption (pod.h:441-448, its loop 0x141a0-0x141f0,
    the UBSan checks on the cursor and on buf[off + k] not taken) and the request of fuzz_dup (fuzz.h:73). *)
Definition S_post : Prop :=
  BOK sp rest src pp lo ->
  forall (sh : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    POSTH sh ps r ms ->
    evt rsegs
      (QBrec (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)))) ms.

(** 0x13ee4 -> 0x13f48: the stop test of pod.h:428 (never taken), pod_write_ent(pp, e) (0x13efc, pod.h:430) and
    the record copy (0x13f00-0x13f44, pod.h:431-432: n_ent++, memcpy of e's 104 bytes to ent[n_ent], its three
    UBSan checks not taken). pod_write_ent asks for pp 8-aligned and e = sp + 0xe8 4-aligned. *)
Definition S_write : Prop :=
  BOK sp rest src pp lo -> pp mod 16 = 0 -> bv_unsigned sp mod 16 = 0 ->
  forall (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
         (e : ent) (r : list byte) (ms : machine_state),
    CNTJ sh np ps i cnt es k e r ms -> evt rsegs (CNTL sh np ps i cnt es k e r) ms.

(** 0x14080 -> 0x140c8: the Struct's size word at `at` (pod.h:434, its two UBSan checks not taken), and, for the
    first params Struct, has_params and params_struct (pod.h:435-437). *)
Definition S_close : Prop :=
  BOK sp rest src pp lo ->
  forall (sh np : Z) (ps : list (Z * pval)) (i : nat) (es : list ent) (r : list byte) (ms : machine_state),
    PCLOSE sh np ps i es r ms ->
    evt rsegs (PROPL sh np i (ps ++ [(POD_PROP_PARAMS, PStruct es)]) r) ms.

End Cuts.
