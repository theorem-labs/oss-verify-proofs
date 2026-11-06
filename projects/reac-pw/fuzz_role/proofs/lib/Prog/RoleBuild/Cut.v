(** The cuts of the inlined pod builder of LLVMFuzzerTestOneInput (plain image, [0x12f14, 0x13f48)): the states its
    pieces hand each other, and the two pieces stated apart from their proofs.

    The builder writes one object into the first block. Its state at a cut is the record so far (Pod/Model.v
    [pb_cut]: the shape, the properties written, and, inside a params Struct, the pods written), the input left, and
    the loop counters; the block holds [Layout.pc_image] of that state, the frame's cells hold the loop's constants
    and counters, and the registers hold what the next piece reads. The predicates below name those states:

      [PROPH] the property loop's head 0x130cc after i properties;
      [PROPL] its latch 0x13e68 after the i-th property was written;
      [CNTH]  the pod loop's head 0x132fc of a params Struct after k pods (rb_ent_contract's entry);
      [CNTJ]  its join 0x1350c, where the inlined pod_write_ent begins (rb_ent_contract's exit);
      [CNTL]  its latch 0x13618, the pod written and, for the first params Struct, recorded;
      [POSTH] 0x13e80, every property written, the top size word about to be patched;
      [QBrec] role_build_contract's postcondition for the record the builder made.

    Statement text only: no function is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import Facts.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** The pcs of the builder's cuts. *)
Definition PROP_HEAD : Z := 0x130cc.
Definition PROP_LATCH : Z := 0x13e68.
Definition CNT_HEAD : Z := 0x132fc.
Definition CNT_JOIN : Z := 0x1350c.
Definition CNT_LATCH : Z := 0x13618.
Definition CNT_EXIT : Z := 0x13e0c.
Definition PROP_CLOSE : Z := 0x13e24.
Definition POST_HEAD : Z := 0x13e80.

(** The multiplier of `v / 10` the preheader leaves in s2 (0x1306c-0x130b4). *)
Definition MULT10 : Z := 0xcccccccd * 2 ^ 32.
(** The head-amp key's part clamp (s8) and the divisor (s10). *)
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
Variables (rest : list byte) (fl src pp lo : Z).


(** An 8-byte frame cell holding v. *)
Definition cell8 (m1 : word -> option byte) (a v : Z) : Prop :=
  bytes_at rsegs m1 a (le8 (Z_to_bv 64 v)).

(** The cells the preheader sets once and no piece writes again (0x13050-0x130bc). *)
Definition CFIX (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp + 0x10) POD_PROP_VOLUME /\
  cell8 m1 (bv_unsigned sp + 0x20) POD_PROP_PARAMS /\
  cell8 m1 (bv_unsigned sp + 0x38) (pp + OFF_ENT) /\
  cell8 m1 (bv_unsigned sp + 0x40) (pp + POD_NENT_OFF) /\
  cell8 m1 (bv_unsigned sp + 0x50) pp /\
  cell8 m1 (bv_unsigned sp + 0x60) (-0x4001) /\
  cell8 m1 (bv_unsigned sp + 0x68) (-0x3ffd) /\
  cell8 m1 (bv_unsigned sp + 0x80) (pp + POD_LEN_OFF).

(** The input left: a suffix of the builder's input, and the cursor that names it. *)
Definition suffix (r : list byte) : Prop := exists k, (k <= length rest)%nat /\ r = skipn k rest.
Definition cur (r : list byte) : Z := src + Z.of_nat (length rest) - Z.of_nat (length r).

(** ** The property loop's head 0x130cc, i properties written *)
Definition PROPH (sh np : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t1 a0 a2 a3 a4 a5 s5 s6 s7 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp (Z_to_bv 64 (-0x4001)) t1 (Z_to_bv 64 np)
                 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
                 a0 (Z_to_bv 64 (Z.of_nat (length ps))) a2 a3 a4 a5
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (-0x3ffd)) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat (length r))) s5 s6 s7
                 (Z_to_bv 64 S8V) (Z_to_bv 64 (Z.b2z (sh =? 7))) (Z_to_bv 64 S10V) (Z_to_bv 64 pp)
                 (Z_to_bv 64 (Z.b2z (seen_of ps))) t4 t5 t6)
             F (Z_to_bv 64 PROP_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\
    cell8 m1 (bv_unsigned sp) fl /\ cell8 m1 (bv_unsigned sp + 0x8) np /\
    cell8 m1 (bv_unsigned sp + 0x18) (Z.b2z (sh =? 7)) /\
    suffix r /\ pc_wf sh ps.

(** ** The property loop's latch 0x13e68, the i-th property written (a1 is still i) *)
Definition PROPL (sh np : Z) (i : nat) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t1 a0 a2 a3 a4 a5 s5 s6 s7 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp (Z_to_bv 64 (-0x4001)) t1 (Z_to_bv 64 np)
                 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
                 a0 (Z_to_bv 64 (Z.of_nat i)) a2 a3 a4 a5
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (-0x3ffd)) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (Z.of_nat (length r))) s5 s6 s7
                 (Z_to_bv 64 S8V) (Z_to_bv 64 (Z.b2z (sh =? 7))) (Z_to_bv 64 S10V) (Z_to_bv 64 pp)
                 (Z_to_bv 64 (Z.b2z (seen_of ps))) t4 t5 t6)
             F (Z_to_bv 64 PROP_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\ CFIX m1 /\
    cell8 m1 (bv_unsigned sp) fl /\ cell8 m1 (bv_unsigned sp + 0x8) np /\
    cell8 m1 (bv_unsigned sp + 0x18) (Z.b2z (sh =? 7)) /\
    suffix r /\ pc_wf sh ps /\ (length ps = S i)%nat.

(** The cells of the property being written: the flags byte, nprops, the shape test, `seen_params` (always set
    inside a params Struct), the property index, the pod count and `first`. *)
Definition CVAR (np : Z) (sh : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z)
    (m1 : word -> option byte) : Prop :=
  cell8 m1 (bv_unsigned sp) fl /\ cell8 m1 (bv_unsigned sp + 0x8) np /\
  cell8 m1 (bv_unsigned sp + 0x18) (Z.b2z (sh =? 7)) /\
  cell8 m1 (bv_unsigned sp + 0x30) 1 /\
  cell8 m1 (bv_unsigned sp + 0x48) (Z.of_nat i) /\
  cell8 m1 (bv_unsigned sp + 0x58) cnt /\
  cell8 m1 (bv_unsigned sp + 0x70) (Z.b2z (first_of ps)).

(** ** The pod loop's head 0x132fc, k pods of the open Struct written (rb_ent_contract's entry) *)
Definition CNTH (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MULT10)
                 s3 (Z_to_bv 64 (Z.of_nat (length r))) s5 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (at_of sh ps))
                 (Z_to_bv 64 S8V) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 S10V) (Z_to_bv 64 pp) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf es /\ (length es = k)%nat /\ (k < 32)%nat /\
    (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** The pod loop's join 0x1350c, the pod built (rb_ent_contract's exit) *)
Definition CNTJ (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp (Z_to_bv 64 (-0x4001)) t1 t2
                 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
                 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (-0x3ffd)) (Z_to_bv 64 MULT10)
                 (Z_to_bv 64 (e_type e)) (Z_to_bv 64 (e_size e)) (Z_to_bv 64 POD_LEN_OFF) (Z_to_bv 64 (cur r)) (Z_to_bv 64 (at_of sh ps))
                 (Z_to_bv 64 S8V) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 S10V) (Z_to_bv 64 pp) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_JOIN) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    cell8 m1 (bv_unsigned sp + 0x78) (Z.of_nat (length r)) /\
    bytes_at rsegs m1 (bv_unsigned sp + 0x88) (ent_mem e) /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf es /\ (length es = k)%nat /\ (k < 32)%nat /\
    ent_wf e /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** The pod loop's latch 0x13618, the pod written into the buffer and, when this Struct is the first
       SPA_PROP_params property, copied into ent[n_ent++] *)
Definition CNTL (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
    (e : ent) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s3 s5 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2
                 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
                 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + POD_LEN_OFF)) a7 (Z_to_bv 64 MULT10)
                 s3 (Z_to_bv 64 (Z.of_nat (length r))) s5 (Z_to_bv 64 (cur r)) (Z_to_bv 64 (at_of sh ps))
                 (Z_to_bv 64 S8V) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 S10V) (Z_to_bv 64 pp) t3 t4 t5 t6)
             F (Z_to_bv 64 CNT_LATCH) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some (es ++ [e])))) m1 /\ CFIX m1 /\ CVAR np sh ps i cnt m1 /\
    suffix r /\ pc_wf sh ps /\ sh <> 7 /\ Forall ent_wf (es ++ [e]) /\ (length es = k)%nat /\
    (k < 32)%nat /\ (length ps <= 2)%nat /\ 0 <= cnt <= 32 /\ (Z.of_nat k < cnt).

(** ** 0x13e80: every property written, the top size word still 0 *)
Definition POSTH (sh : Z) (ps : list (Z * pval)) (r : list byte) : machine_state -> Prop :=
  fun ms => exists (ra t0 t2 s0 s1 a0 a1 a2 a3 a4 a5 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
                   (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2 s0 s1 a0 a1 a2 a3 a4 a5
                 (Z_to_bv 64 (pp + POD_LEN_OFF)) a7
                 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))) (Z_to_bv 64 (cur r))
                 (Z_to_bv 64 (pp + POD_NENT_OFF)) (Z_to_bv 64 fl) s6 s7 s8 s9 s10 (Z_to_bv 64 pp) t3 t4 t5 t6)
             F (Z_to_bv 64 POST_HEAD) fc None m1 (seg_rom rsegs) /\
    MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 /\
    cell8 m1 (bv_unsigned sp + 0x50) pp /\ cell8 m1 (bv_unsigned sp + 0x80) (pp + POD_LEN_OFF) /\
    suffix r /\ pc_wf sh ps.

(** ** Where the first piece ends: the property loop's head, or the end when the object has no property *)
Definition PREQ (sh np : Z) (r : list byte) : machine_state -> Prop :=
  fun ms => (np = 0 /\ POSTH sh [] r ms) \/ (np <> 0 /\ PROPH sh np [] r ms).

(** ** role_build_contract's postcondition, for the record the builder made *)
Definition QBrec (rec : pod_rec) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s10'
                     t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1'
                  (Z_to_bv 64 (Z.of_nat (length (buf rec)))) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (Z.of_nat (length (buf rec)))) s3' (Z_to_bv 64 (pp + POD_NENT_OFF)) (Z_to_bv 64 fl)
                  s6' s7' s8' s9' s10' (Z_to_bv 64 pp) t3' t4' t5' t6')
              F (Z_to_bv 64 ROLE_MALLOC2) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' pp (pp_bytes rec) /\
    cell8 m' (bv_unsigned sp + 0x50) pp /\ cell8 m' (bv_unsigned sp + 0x80) (pp + POD_LEN_OFF) /\
    munch (W0 sp pp) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

(** ** The two pieces stated apart from their proofs *)
(** 0x13e80 -> 0x13f48: the top size word (pod.h:440), the corruption (pod.h:441-448) and the request of
    fuzz_dup (fuzz.h:73). *)
Definition S_post : Prop :=
  BOK sp rest src pp lo ->
  forall (sh : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    POSTH sh ps r ms ->
    evt rsegs
      (QBrec (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)))) ms.

(** 0x130cc -> 0x13e68: one property of the object (pod.h:399-438), the pod loop of a params Struct included. *)
Definition S_prop : Prop :=
  BOK sp rest src pp lo ->
  forall (sh np : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    PROPH sh np ps r ms -> Z.of_nat (length ps) < np -> np <= 3 -> bv_unsigned sp mod 16 = 0 ->
    evt rsegs (PROPL sh np (length ps) (ps ++ [fst (prop_step sh r)]) (snd (prop_step sh r))) ms.

(** 0x1350c -> 0x13618: the inlined pod_write_ent (pod.h:428-430) and the record copy (pod.h:431-432). *)
Definition S_write : Prop :=
  BOK sp rest src pp lo ->
  forall (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z) (es : list ent) (k : nat)
         (e : ent) (r : list byte) (ms : machine_state),
    CNTJ sh np ps i cnt es k e r ms -> evt rsegs (CNTL sh np ps i cnt es k e r) ms.

End Cuts.

(** 0x12f14 -> 0x130cc or 0x13e80: the NULL test, memset of the block, the shape and nprops reads, the header and
    the property loop's preheader (pod.h:384-398). Same premises as role_build_contract. *)
Definition S_pre : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s3 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) -> s5 = Z_to_bv 64 fl -> 0 <= fl < 256 ->
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
    evt rsegs (PREQ sp gp tp F fc m rest fl src pp lo
                 (fst (fuzz_u8 rest) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4)
                 (snd (fuzz_u8 (snd (fuzz_u8 rest)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ROLE_BUILD) fc None m (seg_rom rsegs)).
