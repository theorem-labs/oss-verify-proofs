(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 218 of its 245 lines of code are new or changed and 547 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 168 of its 183 lines of code are new or changed and 230 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/HeadBuild/Cut.v, with its module paths and addresses changed; 96 of its 167 lines of code are new or changed and 112 lines of the source are left out. *)
(** The cuts of the inlined pod builder of LLVMFuzzerTestOneInput (UBSan image, [0x13090, 0x140e0)): the states
    its pieces hand each other, and the pieces proved apart from the walk that chains them.

    The builder writes one object into the first block. Its state at a cut is the record so far (Pod/Model.v
    [pb_cut]: the shape, the properties written, and, inside a params Struct, the pods written), the input left, and
    the loop counters; the block holds [Layout.pc_image] of that state, the frame's cells hold the loop's constants
    and counters, and the registers hold what the next piece reads. The predicates below name those states:

      [PROPH]  the property loop's head 0x132a8 before property i (i = the properties written);
      [PROPL]  its latch 0x13fb0 after property i was written (a7 is still i);
      [CNTH]   the pod loop's head 0x134bc of a params Struct after k pods (EntCut.rb_ent_contract's entry);
      [CNTJ]   its join 0x13df0, the pod built in e (rb_ent_contract's exit), before the stop test of pod.h:428;
      [CNTL]   its latch 0x13e54, the pod written by pod_write_ent and, for the first params Struct, recorded;
      [PCLOSE] 0x13f64, the params Struct's pods all written, its size word about to be patched (pod.h:434);
      [POSTH]  0x13fbc, every property written, the top size word about to be patched (pod.h:440);
      [QBrec]  headamp_build_contract's postcondition for the record the builder made.

    The registers that hold the loops' constants (set by the preheader 0x13214-0x132a4): s9 = 95 (the head-amp
    key's part clamp), s3 = 0xcccccccd << 32 (the multiplier of v / 10), s11 = 4, s0 = sp + 0x178 (t[96]),
    s7 = pp + 0x4000 = &pp->len, s8 = pp; in the property loop also s4 = ~pp (the pointer-overflow bound of the
    puts), s10 = 7 (the shape test), s5 = nprops, a7 = i, s1 = seen_params, s6 = the cursor and s2 = the bytes
    left; in the pod loop s1 = k and s5 = s10 = the cursor. The frame cells: [CFIX] (set once by the preheader,
    with the harness's cap at sp + 0x8), [CPROP] (flags, nprops, shape) and, in a params Struct, [CVAR].

    Statement text only: no function is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** The pcs of the builder's cuts. *)
Definition PROP_HEAD : Z := 0x132a8.
Definition PROP_LATCH : Z := 0x13fb0.
Definition CNT_HEAD : Z := 0x134bc.
Definition CNT_JOIN : Z := 0x13df0.
Definition CNT_LATCH : Z := 0x13e54.
Definition PROP_CLOSE : Z := 0x13f64.
Definition POST_HEAD : Z := 0x13fbc.

(** The multiplier of `v / 10` the preheader leaves in s3, the head-amp key's part clamp (s9), and the multiplier
    of `v / 3` (the cell sp + 0x0). *)
Definition MULT10 : Z := 0xcccccccd * 2 ^ 32.
Definition S0V : Z := 95.
Definition DIV3 : Z := 0x15555556.

(** The first SPA_PROP_params property is the one whose pods are recorded in ent[] (pod.h:409). *)
Definition seen_of (ps : list (Z * pval)) : bool := existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps.
Definition first_of (ps : list (Z * pval)) : bool := negb (seen_of ps).

(** A record the property loop can have built: what [Model.pod_rec_wf] asks of its parts. *)
Definition pc_wf (sh : Z) (ps : list (Z * pval)) : Prop :=
  0 <= sh < 8 /\ Forall (fun kv => 0 <= fst kv < 2^32 /\ pval_wf (snd kv)) ps /\
  Forall ent_wf (all_ents ps) /\ (length ps <= 3)%nat.

(** The offset of the open Struct's size word: the property's key and flags are already written. *)
Definition at_of (sh : Z) (ps : list (Z * pval)) : Z := Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8.

Section Cuts.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo cap : Z).

(** An 8-byte frame cell holding v. *)
Definition cell8 (m1 : word -> option byte) (a v : Z) : Prop :=
  bytes_at rsegs m1 a (le8 (Z_to_bv 64 v)).

(** The cells the preheader sets once and no piece writes again (0x13200-0x132a0, and 0x1312c for the cap): the
    multiplier of v / 3, ~pp, the two property keys, ~(sp + 0x160) (ch), &pp->ent[0] and its complement, pp,
    &pp->n_ent, &pp->len, ~(sp + 0xc0) (e->body), the two constants of the pod_put capacity test, and the
    harness's cap (s3 at the builder's entry, read back after it). *)
Definition CFIX (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp + 0x0) DIV3 /\
  cell8 m1 (bv_unsigned sp + 0x18) (Z.lnot pp) /\
  cell8 m1 (bv_unsigned sp + 0x30) POD_PROP_VOLUME /\
  cell8 m1 (bv_unsigned sp + 0x48) POD_PROP_PARAMS /\
  cell8 m1 (bv_unsigned sp + 0x50) (Z.lnot (bv_unsigned sp + 0x160)) /\
  cell8 m1 (bv_unsigned sp + 0x58) (pp + OFF_ENT) /\
  cell8 m1 (bv_unsigned sp + 0x60) (Z.lnot (pp + OFF_ENT)) /\
  cell8 m1 (bv_unsigned sp + 0x70) pp /\
  cell8 m1 (bv_unsigned sp + 0x68) (pp + POD_NENT_OFF) /\
  cell8 m1 (bv_unsigned sp + 0x78) (pp + POD_LEN_OFF) /\
  cell8 m1 (bv_unsigned sp + 0x80) (Z.lnot (bv_unsigned sp + 0xc0)) /\
  cell8 m1 (bv_unsigned sp + 0x98) (-0x4001) /\
  cell8 m1 (bv_unsigned sp + 0xa0) (-0x3ffd) /\
  cell8 m1 (bv_unsigned sp + 0x8) cap.

(** The cells of the object: the flags cell (set before the builder), nprops and the shape. *)
Definition CPROP (sh np : Z) (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp + 0x10) fl /\ cell8 m1 (bv_unsigned sp + 0x20) np /\
  cell8 m1 (bv_unsigned sp + 0x90) sh.

(** The cells of the params Struct being written: &buf[at], at, the property index, `seen_params` (always set
    inside a params Struct), the pod count and `first`. *)
Definition CVAR (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (m1 : word -> option byte) : Prop :=
  CPROP sh np m1 /\
  cell8 m1 (bv_unsigned sp + 0x28) (pp + at_of sh ps) /\
  cell8 m1 (bv_unsigned sp + 0x38) (at_of sh ps) /\
  cell8 m1 (bv_unsigned sp + 0x40) (Z.of_nat i) /\
  cell8 m1 (bv_unsigned sp + 0x88) 1 /\
  cell8 m1 (bv_unsigned sp + 0xa8) cnt /\
  cell8 m1 (bv_unsigned sp + 0xb0) (Z.b2z (first_of ps)).

(** The input left: a suffix of the builder's input, and the cursor that names it. *)
Definition suffix (r : list byte) : Prop := exists k, (k <= length rest)%nat /\ r = skipn k rest.
Definition cur (r : list byte) : Z := src + Z.of_nat (length rest) - Z.of_nat (length r).

(** ** The property loop's head 0x132a8, before property i = |ps| *)
Definition PROPH (sh np : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) (Z_to_bv 64 (Z.b2z (seen_of ps)))
                 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat (length ps)))
                 (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 MULT10) (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 np)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 S0V)
                 (Z_to_bv 64 7) (Z_to_bv 64 4) t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\ CPROP sh np m1 /\
    suffix r /\ pc_wf sh ps /\ 0 <= np < 4 /\ (length ps < Z.to_nat np)%nat.

(** ** The property loop's latch 0x13fb0, property i written (a7 is still i) *)
Definition PROPL (sh np : Z) (i : nat) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) (Z_to_bv 64 (Z.b2z (seen_of ps)))
                 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (Z.of_nat i))
                 (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 MULT10) (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 np)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 S0V)
                 (Z_to_bv 64 7) (Z_to_bv 64 4) t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\ CPROP sh np m1 /\
    suffix r /\ pc_wf sh ps /\ 0 <= np < 4 /\ length ps = S i /\ (length ps <= Z.to_nat np)%nat.

(** What the pod loop of a params Struct keeps: the record's parts, the open Struct is the (i+1)-th property
    of an object that is not a Struct, and the pods written so far. *)
Definition CNTP (sh np : Z) (ps : list (Z * pval)) (i : nat) (es : list ent) (r : list byte) : Prop :=
  suffix r /\ pc_wf sh ps /\ sh <> 7 /\ 0 <= np < 4 /\ length ps = i /\ (i < Z.to_nat np)%nat /\
  Forall ent_wf es.

(** ** The pod loop's head 0x134bc, k pods of the open Struct written (rb_ent_contract's entry) *)
Definition CNTH (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) (Z_to_bv 64 (Z.of_nat k))
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 MULT10) s4
                 (Z_to_bv 64 (cur r)) s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 S0V)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 4) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR sh np ps i cnt m1 /\
    CNTP sh np ps i es r /\ length es = k /\ 0 <= cnt <= 32 /\ Z.of_nat k < cnt.

(** ** The pod loop's join 0x13df0, pod k built in e at sp + 0xb8 (rb_ent_contract's exit) *)
Definition CNTJ (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) (Z_to_bv 64 (Z.of_nat k))
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 MULT10) s4
                 (Z_to_bv 64 (cur r)) s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 S0V)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 4) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_JOIN) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR sh np ps i cnt m1 /\
    bytes_at rsegs m1 (bv_unsigned sp + 0xb8) (ent_mem e) /\ ent_wf e /\
    CNTP sh np ps i es r /\ length es = k /\ 0 <= cnt <= 32 /\ Z.of_nat k < cnt.

(** ** The pod loop's latch 0x13e54, pod k written into the buffer and, when this Struct is the first
       SPA_PROP_params property, copied into ent[n_ent++] (s1 is still k) *)
Definition CNTL (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) (Z_to_bv 64 (Z.of_nat k))
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 MULT10) s4
                 (Z_to_bv 64 (cur r)) s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 S0V)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 4) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some (es ++ [e])))) m1 /\ CFIX m1 /\ CVAR sh np ps i cnt m1 /\
    CNTP sh np ps i (es ++ [e]) r /\ length es = k /\ 0 <= cnt <= 32 /\ Z.of_nat k < cnt.

(** ** 0x13f64: the params Struct's pods written, its size word at `at` still 0 (a0 = len, a4 = &buf[at],
       a5 = at, a7 = i, s5 = nprops; the cells 0x28, 0x38, 0x40 and 0xa8 are not asked for: the path of an empty
       input comes here before it writes them) *)
Definition PCLOSE (sh np : Z) (ps : list (Z * pval)) (i : nat) (es : list ent) (r : list byte)
    : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a1 a2 a3 a6 s1 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1
                 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))))) a1 a2 a3
                 (Z_to_bv 64 (pp + at_of sh ps)) (Z_to_bv 64 (at_of sh ps)) a6 (Z_to_bv 64 (Z.of_nat i))
                 (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 MULT10) (Z_to_bv 64 (Z.lnot pp)) (Z_to_bv 64 np)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 S0V)
                 (Z_to_bv 64 7) (Z_to_bv 64 4) t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_CLOSE) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CPROP sh np m1 /\
    cell8 m1 (bv_unsigned sp + 0x88) 1 /\ cell8 m1 (bv_unsigned sp + 0xb0) (Z.b2z (first_of ps)) /\
    CNTP sh np ps i es r /\ (length es <= 32)%nat.

(** ** 0x13fbc: every property written, the top size word still 0 (s3 = len) *)
Definition POSTH (sh : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length r)))
                 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))) s4 s5 (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 POST_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\
    cell8 m1 (bv_unsigned sp + 0x10) fl /\ cell8 m1 (bv_unsigned sp + 0x18) (Z.lnot pp) /\
    cell8 m1 (bv_unsigned sp + 0x70) pp /\ cell8 m1 (bv_unsigned sp + 0x68) (pp + POD_NENT_OFF) /\
    cell8 m1 (bv_unsigned sp + 0x78) (pp + POD_LEN_OFF) /\ cell8 m1 (bv_unsigned sp + 0x8) cap /\
    suffix r /\ pc_wf sh ps.

(** ** headamp_build_contract's postcondition, for the record the builder made *)
Definition QBrec (rec : pod_rec) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s9' s10' s11'
                     t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (Z.of_nat (length (buf rec))))
                  a1' a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 (Z.of_nat (length (buf rec)))) s4' s5' s6'
                  (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9' s10' s11' t3' t4' t5' t6')
              F (Z_to_bv 64 HEAD_MALLOC2) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes rec) /\
    cell8 m' (bv_unsigned sp + 0x10) fl /\ cell8 m' (bv_unsigned sp + 0x70) pp /\
    cell8 m' (bv_unsigned sp + 0x68) (pp + POD_NENT_OFF) /\
    cell8 m' (bv_unsigned sp + 0x78) (pp + POD_LEN_OFF) /\ cell8 m' (bv_unsigned sp + 0x8) cap /\
    munch (W0 sp pp) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

(** ** The pieces stated apart from the walk that chains them *)
(** 0x13fbc -> 0x140e0: the top size word (pod.h:440), the corruption (pod.h:441-448, its loop 0x1407c-0x140c8,
    the UBSan checks on the cursor and on buf[off + k] not taken) and the request of fuzz_dup (fuzz.h:73). *)
Definition S_post : Prop :=
  BOK sp rest src pp lo ->
  forall (sh : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    POSTH sh ps r ms ->
    evt rsegs
      (QBrec (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)))) ms.

(** 0x13df0 -> 0x13e54: the stop test of pod.h:428 (never taken), pod_write_ent(pp, e) (0x13e08, pod.h:430) and
    the record copy (0x13e0c-0x13e50, pod.h:431-432: n_ent++, memcpy of e's 104 bytes to ent[n_ent], its three UBSan
    checks not taken). pod_write_ent asks for pp 8-aligned and e = sp + 0xb8 4-aligned. *)
Definition S_write : Prop :=
  BOK sp rest src pp lo -> pp mod 16 = 0 -> bv_unsigned sp mod 16 = 0 ->
  forall (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
         (e : ent) (r : list byte) (ms : machine_state),
    CNTJ sh np ps i cnt es k e r ms -> evt rsegs (CNTL sh np ps i cnt es k e r) ms.

(** 0x13f64 -> 0x13fb0: the Struct's size word at `at` (pod.h:434, its two UBSan checks not taken), and, for the
    first params Struct, has_params and params_struct (pod.h:435-437); then s1 = seen_params from its cell. *)
Definition S_close : Prop :=
  BOK sp rest src pp lo ->
  forall (sh np : Z) (ps : list (Z * pval)) (i : nat) (es : list ent) (r : list byte) (ms : machine_state),
    PCLOSE sh np ps i es r ms ->
    evt rsegs (PROPL sh np i (ps ++ [(POD_PROP_PARAMS, PStruct es)]) r) ms.

End Cuts.
