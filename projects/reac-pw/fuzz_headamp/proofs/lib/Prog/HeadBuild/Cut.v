(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v, with its module paths changed; 532 of its 580 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/Prog/LLVMFuzzerTestOneInput_fr.v (6874bc78b1f) at fuzz_wire's
   module paths; lf_guard_img reads this image's __stack_chk_guard GOT slot 0x1cef0; lf_fr_call_x is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 455 of its 574 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 218 of its 245 lines of code are new or changed and 547 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 168 of its 183 lines of code are new or changed and 230 lines of the source are left out. *)
(** The cuts of the inlined pod builder of LLVMFuzzerTestOneInput (plain image, [0x13044, 0x14048)): the states its
    pieces hand each other, and the two pieces stated apart from their proofs.

    The builder writes one object into the first block. Its state at a cut is the record so far (Pod/Model.v
    [pb_cut]: the shape, the properties written, and, inside a params Struct, the pods written), the input left, and
    the loop counters; the block holds [Layout.pc_image] of that state, the frame's cells hold the loop's constants
    and counters, and the registers hold what the next piece reads. The predicates below name those states:

      [PROPH] the property loop's head 0x13208 after i properties;
      [PROPL] its latch 0x13f64 after the i-th property was written;
      [CNTH]  the pod loop's head 0x1340c of a params Struct after k pods (rb_ent_contract's entry);
      [CNTJ]  its join 0x13618, where the inlined pod_write_ent begins (rb_ent_contract's exit);
      [CNTL]  its latch 0x13724, the pod written and, for the first params Struct, recorded;
      [POSTH] 0x13f80, every property written, the top size word about to be patched;
      [QBrec] headamp_build_contract's postcondition for the record the builder made.

    The harness's two input values, null (nl) and cap, ride through the builder in s7 and s6 when the object has no
    property, and in the frame cells sp and sp + 8 otherwise (0x13198-0x1319c; reloaded at 0x13f74-0x13f78).

    Statement text only: no function is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** The pcs of the builder's cuts. *)
Definition PROP_HEAD : Z := 0x13208.
Definition PROP_LATCH : Z := 0x13f64.
Definition CNT_HEAD : Z := 0x1340c.
Definition CNT_JOIN : Z := 0x13618.
Definition CNT_LATCH : Z := 0x13724.
Definition CNT_EXIT : Z := 0x13f0c.
Definition PROP_CLOSE : Z := 0x13f20.
Definition POST_HEAD : Z := 0x13f80.

(** The multiplier of `v / 10` the preheader leaves in s9 (0x131b0-0x131f4). *)
Definition MULT10 : Z := 0xcccccccd * 2 ^ 32.
(** The head-amp key's part clamp (s7) and the divisor (s11). *)
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

Section Cuts.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (nl cap src pp lo : Z).


(** An 8-byte frame cell holding v. *)
Definition cell8 (m1 : word -> option byte) (a v : Z) : Prop :=
  bytes_at rsegs m1 a (le8 (Z_to_bv 64 v)).

(** The cells the preheader sets once and no piece writes again (0x1306c, 0x13188, 0x13194, 0x131e0-0x13200). *)
Definition CFIX (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp + 0x10) POD_PROP_VOLUME /\
  cell8 m1 (bv_unsigned sp + 0x18) POD_PROP_PARAMS /\
  cell8 m1 (bv_unsigned sp + 0x30) (pp + OFF_ENT) /\
  cell8 m1 (bv_unsigned sp + 0x38) (pp + POD_NENT_OFF) /\
  cell8 m1 (bv_unsigned sp + 0x50) (pp + POD_LEN_OFF) /\
  cell8 m1 (bv_unsigned sp + 0x58) pp /\
  cell8 m1 (bv_unsigned sp + 0x70) (-0x4001) /\
  cell8 m1 (bv_unsigned sp + 0x78) (-0x3ffd).

(** The cells the preheader sets that hold the object's inputs: cap, null, nprops and the shape test (0x13088 /
    0x13098 / 0x130dc, 0x1310c / 0x13148, 0x13198-0x1319c). *)
Definition CHAR (np sh : Z) (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp) cap /\ cell8 m1 (bv_unsigned sp + 0x8) nl /\
  cell8 m1 (bv_unsigned sp + 0x20) np /\ cell8 m1 (bv_unsigned sp + 0x40) (Z.b2z (sh =? 7)).

(** The input left: a suffix of the builder's input, and the cursor that names it. *)
Definition suffix (r : list byte) : Prop := exists k, (k <= length rest)%nat /\ r = skipn k rest.
Definition cur (r : list byte) : Z := src + Z.of_nat (length rest) - Z.of_nat (length r).

(** ** The property loop's head 0x13208, i properties written *)
Definition PROPH (sh np : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 s6 s8 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 (bv_unsigned sp + 0x150)) (Z_to_bv 64 (Z.b2z (seen_of ps)))
                 a0 a1 a2 a3 (Z_to_bv 64 np) (Z_to_bv 64 (Z.of_nat (length ps)))
                 (Z_to_bv 64 (-0x3ffd)) (Z_to_bv 64 (-0x4001)) (Z_to_bv 64 (pp + POD_LEN_OFF))
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 pp) s6
                 (Z_to_bv 64 S8V) s8 (Z_to_bv 64 MULT10) (Z_to_bv 64 (bv_unsigned sp + 0x118)) (Z_to_bv 64 S10V)
                 t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\ CHAR np sh m1 /\
    suffix r /\ pc_wf sh ps.

(** ** The property loop's latch 0x13f64, the i-th property written (a5 is still i) *)
Definition PROPL (sh np : Z) (i : nat) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 s6 s8 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 (bv_unsigned sp + 0x150)) (Z_to_bv 64 (Z.b2z (seen_of ps)))
                 a0 a1 a2 a3 (Z_to_bv 64 np) (Z_to_bv 64 (Z.of_nat i))
                 (Z_to_bv 64 (-0x3ffd)) (Z_to_bv 64 (-0x4001)) (Z_to_bv 64 (pp + POD_LEN_OFF))
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 pp) s6
                 (Z_to_bv 64 S8V) s8 (Z_to_bv 64 MULT10) (Z_to_bv 64 (bv_unsigned sp + 0x118)) (Z_to_bv 64 S10V)
                 t3 t4 t5 t6)
             F (Z_to_bv 64 PROP_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\ CHAR np sh m1 /\
    suffix r /\ pc_wf sh ps /\ (length ps = S i)%nat.

(** The cells of the property being written: the object's inputs, `seen_params` (always set inside a params
    Struct), the pod count, the property index and `first`. *)
Definition CVAR (np : Z) (sh : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z)
    (m1 : word -> option byte) : Prop :=
  CHAR np sh m1 /\
  cell8 m1 (bv_unsigned sp + 0x48) 1 /\
  cell8 m1 (bv_unsigned sp + 0x60) cnt /\
  cell8 m1 (bv_unsigned sp + 0x68) (Z.of_nat i) /\
  cell8 m1 (bv_unsigned sp + 0x80) (Z.b2z (first_of ps)).

(** ** The pod loop's head 0x1340c, k pods of the open Struct written (rb_ent_contract's entry) *)
Definition CNTH (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 (bv_unsigned sp + 0x150)) (Z_to_bv 64 (Z.of_nat k))
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pp + POD_LEN_OFF))
                 s3 (Z_to_bv 64 (Z.of_nat (length r))) s5 (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 S8V) (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (bv_unsigned sp + 0x118)) (Z_to_bv 64 S10V) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf es /\ (length es = k)%nat /\ (k < 32)%nat /\
    (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** The pod loop's join 0x13618, the pod built (rb_ent_contract's exit) *)
Definition CNTJ (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 (bv_unsigned sp + 0x150)) (Z_to_bv 64 (Z.of_nat k))
                 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (-0x3ffd)) (Z_to_bv 64 (-0x4001)) (Z_to_bv 64 (pp + POD_LEN_OFF))
                 (Z_to_bv 64 (e_type e)) (Z_to_bv 64 (e_size e)) (Z_to_bv 64 pp) (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 S8V) (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (bv_unsigned sp + 0x118)) (Z_to_bv 64 S10V) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_JOIN) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    cell8 m1 (bv_unsigned sp + 0x88) (Z.of_nat (length r)) /\
    bytes_at rsegs m1 (bv_unsigned sp + 0x90) (ent_mem e) /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf es /\ (length es = k)%nat /\ (k < 32)%nat /\
    ent_wf e /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** The pod loop's latch 0x13724, the pod written into the buffer and, when this Struct is the first
       SPA_PROP_params property, copied into ent[n_ent++] *)
Definition CNTL (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 (bv_unsigned sp + 0x150)) (Z_to_bv 64 (Z.of_nat k))
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pp + POD_LEN_OFF))
                 s3 (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 pp) (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 S8V) (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (bv_unsigned sp + 0x118)) (Z_to_bv 64 S10V) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some (es ++ [e])))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf (es ++ [e]) /\ (length es = k)%nat /\
    (k < 32)%nat /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** 0x13f80: every property written, the top size word still 0 *)
Definition POSTH (sh : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat (length r))) t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))) (Z_to_bv 64 pp)
                 (Z_to_bv 64 cap) (Z_to_bv 64 nl) (Z_to_bv 64 (pp + POD_NENT_OFF)) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 POST_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\
    cell8 m1 (bv_unsigned sp + 0x50) (pp + POD_LEN_OFF) /\ cell8 m1 (bv_unsigned sp + 0x58) pp /\
    suffix r /\ pc_wf sh ps.

(** ** Where the first piece ends: the property loop's head, or the end when the object has no property *)
Definition PREQ (sh np : Z) (r : list byte) : machine_state -> Prop :=
  fun ms => (np = 0 /\ POSTH sh [] r ms) \/ (np <> 0 /\ PROPH sh np [] r ms).

(** ** headamp_build_contract's postcondition, for the record the builder made *)
Definition QBrec (rec : pod_rec) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s9' s10' s11'
                     t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1'
                  (Z_to_bv 64 (Z.of_nat (length (buf rec)))) a1' a2' a3' a4' a5' a6' a7'
                  s2' s3' (Z_to_bv 64 (Z.of_nat (length (buf rec)))) (Z_to_bv 64 pp) (Z_to_bv 64 cap)
                  (Z_to_bv 64 nl) (Z_to_bv 64 (pp + POD_NENT_OFF)) s9' s10' s11' t3' t4' t5' t6')
              F (Z_to_bv 64 HEAD_MALLOC2) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes rec) /\
    cell8 m' (bv_unsigned sp + 0x50) (pp + POD_LEN_OFF) /\ cell8 m' (bv_unsigned sp + 0x58) pp /\
    munch (W0 sp pp) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

(** ** The pieces stated apart from their proofs *)
(** 0x13f80 -> 0x14048: the top size word (pod.h:440), the corruption (pod.h:441-448) and the request of
    fuzz_dup (fuzz.h:73). *)
Definition S_post : Prop :=
  BOK sp rest src pp lo ->
  forall (sh : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    POSTH sh ps r ms ->
    evt rsegs
      (QBrec (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)))) ms.

(** 0x13208 -> 0x13f64: one property of the object (pod.h:399-438), the pod loop of a params Struct included. *)
Definition S_prop : Prop :=
  BOK sp rest src pp lo ->
  forall (sh np : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    PROPH sh np ps r ms -> Z.of_nat (length ps) < np -> np <= 3 -> bv_unsigned sp mod 16 = 0 ->
    evt rsegs (PROPL sh np (length ps) (ps ++ [fst (prop_step sh r)]) (snd (prop_step sh r))) ms.

(** 0x13618 -> 0x13724: the inlined pod_write_ent (pod.h:428-430) and the record copy (pod.h:431-432). *)
Definition S_write : Prop :=
  BOK sp rest src pp lo ->
  forall (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
         (e : ent) (r : list byte) (ms : machine_state),
    CNTJ sh np ps i cnt es k e r ms -> evt rsegs (CNTL sh np ps i cnt es k e r) ms.

End Cuts.

(** 0x13044 -> 0x13208 or 0x13f80: the NULL test, memset of the block, the shape and nprops reads, the header and
    the property loop's preheader (pod.h:384-398). Same premises as headamp_build_contract. *)
Definition S_pre : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (nl cap src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s3 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s7 = Z_to_bv 64 nl -> 0 <= nl <= 1 -> s6 = Z_to_bv 64 cap -> 0 <= cap <= 9 ->
    s1 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
    0 < src -> bytes_at rsegs m src rest ->
    rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] ->
    (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) ->
    (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) ->
    src + Z.of_nat (length rest) <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs (PREQ sp gp tp F fc m rest nl cap src pp lo
                 (fst (fuzz_u8 rest) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4)
                 (snd (fuzz_u8 (snd (fuzz_u8 rest)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_BUILD) fc None m (seg_rom rsegs)).
