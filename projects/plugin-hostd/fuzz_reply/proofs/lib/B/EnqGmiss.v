(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/EnqGmiss.v (commit f38a2a07767, B2 FINAL (im_rmax comment, d236f37c0d0); file sha256 fd42537792fa) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/EnqGmiss.v at commit f303438be5b, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B2; integrator ReallocPrimary).
   rule 24: proves function __sanitizer::QuarantineCache<__asan::QuarantineCallback>::Enqueue (the MISS arm: a new
   batch is needed and the class-24 cache is EMPTY, so Enqueue calls the internal allocator's Refill in the middle
   of its walk), frame-generic, at cgif_file_fuzzer's asan-ubsan image (Enqueue 0x360ec).  Reuse search:
   LOOKUP-B2-enqueue.txt (sha256 7fa7207b8221; internal record) 2026-10-29T23:07:48Z exit 3; rule-24 check B2LookupCheck: CONFIRM.

   The miss arm over [EnqIfaceMiss], generalized from the released arm (YFg6 with YFf2, 908 lines) as
   MnEnqArms.v:186-321 runs it: every call there to a cgif model lemma or to a cgif walk is a field or a parameter
   here.  Like EnqGbase.v / EnqGroom.v / EnqGhit.v, this file names NO image and NO model: the segment list
   [segs], Enqueue's entry [A_ENQ], the two walk segments' posts ([ACALL] / [ARETm]) and windows ([WINc] /
   [WINm]), the callee's leaf ([RLEAF]) and the arm's end state ([Smiss]) are parameters.  The middle
   configuration is read with [ms_mem (cfg_ms _)], so no refill pc, no stack size and no register convention
   appears in any statement.

   WHY THE REFILL IS TWO FIELDS (the scout's fact table, agent ReallocPrimary.WalkB2.FactMiss).  cgif's miss arm
   reads four things out of its own [enq_pre] that the shared cf premise does NOT carry: the budget conjunct
   (YFg6.v:356), all of [refill_reg X kBatchClass] (YFg6.v:356, :862, :876), the [rroom] half of [qloosem]
   (YFg6.v:356), and [wf_fa_room], which the cf Wf drops (YFg6.v:862, YFf2.v:142-150).  NONE of them may be a
   premise of this arm.  They are spent INSIDE two fields that an instance fills from its own refill contract and
   its own refill-tree apost:
   - [im_refill]: the callee's contract AT THE CALL CONFIGURATION the first segment reached, premised on that
     segment's post and on the relation at the call memory, which the named field [im_arx_call] transports from
     the entry memory (cgif: MnRefillLoc.tfib_refill_specR_em applied to YFg6.REFILL_PRE, whose first conjunct
     is YFg6.AR1; the rest of REFILL_PRE is where the budget, [refill_reg] and [rroom] go);
   - [im_apostg]: the refill tree's apath post (cgif: YFg6.refill_tree_apostg at YFg6.WfX1, which is where
     [wf_fa_room] and the pp = 1 slack go).
   The arm below sees only their conclusions.

   What this file proves, once for every instance and every image:
   - the composition of the two walk segments around the call (YFfj.amreal_after_SRr, YFfk.amreal_apostg) and the
     case split on the refilled cache;
   - the THREE-part RAW frame of CLenq.acall_post_x: the tail segment's window frame ([im_frame2] off [WINm]),
     the refill's own raw frame ([im_frameR]), and the first segment's window frame ([im_frame1] off [WINc]),
     each turned into the arm's exclusion set by [im_owned2] / [im_aox] / [im_owned1];
   - the THREE-part memnorm keep of the post of record, from the same three frames with [im_safe1] / [im_safe2],
     chained by MemnormLocG.memnorm_keep_trans.

   SIZE BOUNDS.  No literal bound is written here: [NMAXD] enters through [im_nmax] and the premise of [im_walk1]
   / [im_walk2], [RMAXD] through [im_rmaxd_ok] / [im_rmax] and the premise of [im_walk2].  [im_rmax] is read at
   the REFILLED state, which is where the tail walk needs it and which the pre-state's bound does not give.
   KNOWN OPEN (reviewer, relayed by WalkB2 2026-10-30 00:3xZ): at the cf instance the miss walk needs the
   class-24 OFFSET bound widened as well as the block size; DEALLOC-NMAX covers only the block size.  It is
   carried here as RMAXD and proved by the instance, not by this file.

   EVENT-TERM GATE (Main 22:59Z): no field of this file names [st_nev], [EV_A], [EV_MAX], [EV_BIG], [mtr_ok],
   [aregime] or a non-cf [abudget]; the event count enters only through the opaque [EPRE] and, for the refill,
   inside [im_refill] / [im_apostg], which each instance states. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0l YG0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfp YFfj YFfk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLenq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT MemnormLocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import EnqGbase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

Section b.
(* ---- The image. ---- *)
Variable segs : list Segment.
Variable A_ENQ : Z.

Variable B : asyms.

(* ---- The model. ---- *)
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable EPRE : Z -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk -> Prop.

(* The two size bounds. *)
Variables (NMAXD RMAXD : Z).

(* ---- The two walk segments and the callee's leaf, per image. ---- *)
(* The FIRST segment's post: Enqueue's entry to the Refill call site, with the class-24 cache empty.  cgif_file:
   [YFh5.at_CALLR W ly regs mem md u nn q 0 jst]. *)
Variable ACALL : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk ->
  world segs -> config -> Prop.
(* and its window.  cgif_file: [YFgq.WIN0 ly regs] (Enqueue's stack frame and the thread object's cells). *)
Variable WINc : alayout -> bvmap 5 word -> astate -> Z -> Prop.

(* The internal allocator's leaf AT the configuration [c1] the first segment reached.  cgif_file:
   [MnRefillLoc.refill_leafR_em B ly X W (ms_regs (cfg_ms c1)) (ms_mem (cfg_ms c1)) (cfg_model c1) kBatchClass]. *)
Variable RLEAF : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk ->
  config -> unit * astate -> world segs -> config -> Prop.

(* The TAIL segment's post, at the refilled state [X1] and the leaf's configuration [c5].  cgif_file:
   [YFh6.at_RETR W5 ly (ms_regs (cfg_ms c5)) .. u nn q1 (length l) (last l 0) ra0 s0 s1 s2 s3 s4 s5]. *)
Variable ARETm : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk ->
  astate -> world segs -> config -> list Z -> world segs -> config -> Prop.
(* and its window.  cgif_file: [YFgr.WIN ly (st_qthread X1) (length l) (last l 0)]. *)
Variable WINm : alayout -> bvmap 5 word -> astate -> list Z -> Z -> Prop.

(* The state the miss arm ends in.  cgif_file: [YFf2.S' X1 k l] at the REFILLED state. *)
Variable Smiss : astate -> chunk -> list Z -> astate.

(* ---------------------------------------------------------------------------------------------------------------- *)
Record EnqIfaceMiss : Prop := {
  (* the block-size bound of this instance (NMAXD; no literal here).  BOTH ends are the instance's: cgif_file gets
     `1 <= ck_n k < 2 ^ 28` from YFfq.u_facts; at cf the upper end is enq_pre_cf's `ck_n k < cf_malloc_max`, and the
     LOWER end `1 <= ck_n k` is not in enq_pre_cf, so it comes from the model (req_size_bounds with 0 <= ck_req from
     chunk_ok_cf, through the Wf_cf conjunct of enq_pre_cf), as for ir_nmax / ih_nmax (fresh reviewer, 01:1xZ). *)
  im_nmax : forall inst ly X W regs mem md k, EPRE inst ly X W regs mem md k -> 1 <= ck_n k < NMAXD;

  (* RMAXD's window, in B1's form (DMwalkIF.v:307 rmaxd_ok at 3e29c198d40), as EnqGbase.v:201 [ih_rmaxd_ok]: a
     field, not a Section hypothesis, so that it is a compiled lemma at each instance. *)
  im_rmaxd_ok : 2 ^ 31 <= RMAXD <= kFreeArrayOffset;

  (* the class-24 region's mapped-user bound of this instance, AT THE REFILLED STATE X1: that is where the tail walk
     reads it.  cgif_file: YFf2.nb_geom's fifth conjunct at X1.  At cf, batch_room_cf ALONE does not give it:
     batch_room_cf (YG00cf.v:361-362, `rg_mapped_user + kUserMapSize <= kFreeArrayOffset`) holds at the PRE-state X
     (an enq_pre_cf conjunct), and regs_only X X1 (im_apostg) says nothing about [reg X1].  The cf instance closes it
     at X1 itself: the refill leaf's relation gives Wf_cf at X1 (amc_wf), and YG01cf.mapped_bound_cf (YG01cf.v:251)
     bounds every class's mapped-user bytes by kFreeArrayOffset (CfF1's YGcfInstEnqMisscgif.v:134-138 at
     5a0eabced8d1). *)
  im_rmax : forall inst ly X W regs mem md k c1 X1 W5 c5 l,
    EPRE inst ly X W regs mem md k ->
    RLEAF ly X W regs mem md k c1 (tt, X1) W5 c5 ->
    st_cache_inited X1 = true -> pc_chunks (cache X1 kBatchClass) = l -> l <> [] ->
    rg_mapped_user (reg X1 kBatchClass) <= RMAXD;

  (* the model's step at the arm: the refill tree, then the refilled cache's batch (cgif:
     YFft.amreal_enqueue_nb with YFft.enq_after_refill).  It is a field because the released lemma is stated at
     cgif's own segment list. *)
  im_step : forall X k W c (Q : unit * astate -> world segs -> config -> Prop),
    need_new_batch (st_qthread X) = true ->
    amreal segs (refill_tree kBatchClass X) W c
      (fun r W1 c1 => pc_chunks (cache (snd r) kBatchClass) <> [] /\
         forall l, pc_chunks (cache (snd r) kBatchClass) = l ->
         SRr segs W1 c1 (fun W2 c2 => Q (tt, Smiss (snd r) k l) W2 c2)) ->
    amreal segs (enqueue k X) W c Q;

  (* the FIRST segment: Enqueue's entry to the Refill call site (cgif: YFh5.segR1 with YFg6.FH0_ok and eq_refl) *)
  im_walk1 : forall inst ly X W regs mem md k,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] -> 1 <= ck_n k < NMAXD ->
    SRr segs W (cfg_at segs A_ENQ regs mem md) (ACALL ly X W regs mem md k);

  (* the first segment kept every byte outside its window (cgif: at_CALLR's [YFgq.MEQ0] clause) *)
  im_frame1 : forall inst ly X W regs mem md k W1 c1,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    ACALL ly X W regs mem md k W1 c1 ->
    forall x : word, ~ WINc ly regs X (bv_unsigned x) -> ms_mem (cfg_ms c1) x = mem x;

  (* every byte of the first segment's window is owned by the allocator at the PRE-state, or lies in Enqueue's
     stack scratch (cgif: YFgq.WIN0 is the stack frame and the thread object's cells, YG0q.own_core) *)
  im_owned1 : forall inst ly X W regs mem md k a,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] -> 0 <= a < 2 ^ 64 ->
    WINc ly regs X a -> AOX ly X a \/ (spZ regs - CLenq.QSTACK_G <= a < spZ regs);

  (* every byte of the first segment's window is memnorm-safe (cgif: MnRefillLoccgif.mn_safe_stack /
     mn_safe_thread) *)
  im_safe1 : forall inst ly X W regs mem md k (x : word),
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    WINc ly regs X (bv_unsigned x) -> MemnormT.mn_safe segs x;

  (* the relation at the CALL memory: the first segment kept the allocator's bytes, so ARX transports from the
     entry memory to the memory and model at the Refill call (cgif: YFg6.AR1, the first conjunct of
     YFg6.REFILL_PRE, by AR_frame_law_ok; the cf instance: its own frame-law transport of ARX_cf) *)
  im_arx_call : forall inst ly X W regs mem md k W1 c1,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    ACALL ly X W regs mem md k W1 c1 ->
    ARX inst ly X W1 (ms_mem (cfg_ms c1)) (cfg_model c1);

  (* the internal allocator's contract at the call configuration (cgif: MnRefillLoc.tfib_refill_specR_em applied
     to YFg6.REFILL_PRE), given the relation at the call memory ([im_arx_call]).  The budget, [refill_reg] and the
     [rroom] half of [qloosem] that the cf premise drops are spent HERE, inside the instance's own proof. *)
  im_refill : forall inst ly X W regs mem md k W1 c1,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    ACALL ly X W regs mem md k W1 c1 ->
    ARX inst ly X W1 (ms_mem (cfg_ms c1)) (cfg_model c1) ->
    amreal segs (refill_tree kBatchClass X) W1 c1 (RLEAF ly X W regs mem md k c1);

  (* the refill tree's post on every granted path (cgif: YFg6.refill_tree_apostg at YFg6.WfX1).  [wf_fa_room] and
     the pp = 1 slack, which the cf Wf drops, are spent HERE. *)
  im_apostg : forall inst ly X W regs mem md k,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    forall tr r, apath (refill_tree kBatchClass X) tr r -> gflag tr = true ->
    regs_only X (snd r) /\ st_cache_inited (snd r) = true /\ pc_chunks (cache (snd r) kBatchClass) <> [];

  (* the refill's own raw frame and memnorm keep, between the call configuration and the leaf's (cgif:
     MnRefillLoc.refill_leafR_em's last two clauses, with the callee's stack window inside Enqueue's), on a leaf
     whose class-24 cache is not empty (the refill's granted paths; the cf leaf keeps the layout there) *)
  im_frameR : forall inst ly X W regs mem md k W1 c1 r W5 c5,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    ACALL ly X W regs mem md k W1 c1 -> RLEAF ly X W regs mem md k c1 r W5 c5 ->
    pc_chunks (cache (snd r) kBatchClass) <> [] ->
    (forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ AOX ly (snd r) (bv_unsigned x) ->
       ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) ->
       ms_mem (cfg_ms c5) x = ms_mem (cfg_ms c1) x) /\
    MemnormT.memnorm_keep segs (ms_mem (cfg_ms c1)) (ms_mem (cfg_ms c5));

  (* the TAIL segment, from the leaf's configuration (cgif: YFh6.segT with YFg6.FHR_ok) *)
  im_walk2 : forall inst ly X W regs mem md k W1 c1 X1 W5 c5 l,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    ACALL ly X W regs mem md k W1 c1 -> RLEAF ly X W regs mem md k c1 (tt, X1) W5 c5 ->
    regs_only X X1 -> st_cache_inited X1 = true ->
    pc_chunks (cache X1 kBatchClass) = l -> l <> [] ->
    1 <= ck_n k < NMAXD -> rg_mapped_user (reg X1 kBatchClass) <= RMAXD ->
    SRr segs W5 c5 (ARETm ly X W regs mem md k X1 W5 c5 l);

  (* the tail segment returns to Enqueue's caller and kept every byte outside its window (cgif: at_RETR's config
     clause and its [YFgr.MEQ] clause) *)
  im_frame2 : forall ly X W regs mem md k X1 W5 c5 l W6 c6,
    ARETm ly X W regs mem md k X1 W5 c5 l W6 c6 ->
    exists regs' mem' md', c6 = cfg_at segs (raZ regs) regs' mem' md' /\
      (forall x : word, ~ WINm ly regs X1 l (bv_unsigned x) -> mem' x = ms_mem (cfg_ms c5) x);

  (* the relation at the post state, from the tail walk's post (cgif: YFg6.FINR through YFf2.enq_fin_ARm) *)
  im_post : forall inst ly X W regs mem md k W1 c1 X1 W5 c5 l W6 c6,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    ACALL ly X W regs mem md k W1 c1 -> RLEAF ly X W regs mem md k c1 (tt, X1) W5 c5 ->
    regs_only X X1 -> st_cache_inited X1 = true ->
    pc_chunks (cache X1 kBatchClass) = l -> l <> [] ->
    ARETm ly X W regs mem md k X1 W5 c5 l W6 c6 ->
    enq_leaf_g0 segs B ARX AOX inst ly X W regs mem md k (tt, Smiss X1 k l) W6 c6;

  (* every byte of the tail segment's window is owned at the REFILLED state, or lies in Enqueue's stack scratch
     (cgif: YFgr.WIN inside YFf2.D at X1, then YFf2.D_owned) *)
  im_owned2 : forall inst ly X W regs mem md k c1 X1 W5 c5 l a,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    RLEAF ly X W regs mem md k c1 (tt, X1) W5 c5 ->
    st_cache_inited X1 = true -> pc_chunks (cache X1 kBatchClass) = l -> l <> [] ->
    0 <= a < 2 ^ 64 -> WINm ly regs X1 l a ->
    AOX ly X1 a \/ (spZ regs - CLenq.QSTACK_G <= a < spZ regs);

  (* every byte of the tail segment's window is memnorm-safe (cgif: MemnormLoc.YFf2_D_safe at X1) *)
  im_safe2 : forall inst ly X W regs mem md k c1 X1 W5 c5 l (x : word),
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    RLEAF ly X W regs mem md k c1 (tt, X1) W5 c5 ->
    st_cache_inited X1 = true -> pc_chunks (cache X1 kBatchClass) = l -> l <> [] ->
    WINm ly regs X1 l (bv_unsigned x) -> MemnormT.mn_safe segs x;

  (* a state the refill leaves with the same chunks and the same file state owns no more than the old one
     (cgif: YFg6.aowned_same) *)
  im_aox : forall ly S S' a, st_chunks S' = st_chunks S -> st_fs S' = st_fs S -> AOX ly S' a -> AOX ly S a
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
Hypothesis IF : EnqIfaceMiss.

Theorem enq_miss_g : forall inst ly X W regs mem md k,
EPRE inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = [] ->
amreal segs (enqueue k X) W (cfg_at segs A_ENQ regs mem md)
(enq_arm_post_g segs B ARX AOX inst ly X W regs mem md k).
Proof.
(* the fields, under short names *)
pose proof (im_nmax IF) as NMAX.
pose proof (im_rmax IF) as RMAX.
pose proof (im_step IF) as STEP.
pose proof (im_walk1 IF) as WALK1.
pose proof (im_frame1 IF) as FRAME1.
pose proof (im_owned1 IF) as OWN1.
pose proof (im_safe1 IF) as SAFE1.
pose proof (im_arx_call IF) as ARXC.
pose proof (im_refill IF) as REFILL.
pose proof (im_apostg IF) as APOSTG.
pose proof (im_frameR IF) as FRAMER.
pose proof (im_walk2 IF) as WALK2.
pose proof (im_frame2 IF) as FRAME2.
pose proof (im_post IF) as POSTF.
pose proof (im_owned2 IF) as OWN2.
pose proof (im_safe2 IF) as SAFE2.
pose proof (im_aox IF) as AOXM.
intros inst ly X W regs mem md k PRE HNB Hl0.
pose proof (NMAX inst ly X W regs mem md k PRE) as HN.
(* the model's step at the arm *)
apply (STEP X k W (cfg_at segs A_ENQ regs mem md) _ HNB).
(* the first segment, Enqueue's entry to the Refill call site *)
apply amreal_after_SRr.
eapply SRr_mono; [exact (WALK1 inst ly X W regs mem md k PRE HNB Hl0 HN)|].
intros W1 c1 _ HC.
(* the internal allocator's call, and the refill tree's post on every granted path *)
pose proof (REFILL inst ly X W regs mem md k W1 c1 PRE HNB Hl0 HC
  (ARXC inst ly X W regs mem md k W1 c1 PRE HNB Hl0 HC)) as RR.
pose proof (APOSTG inst ly X W regs mem md k PRE HNB Hl0) as APOST.
pose proof (amreal_apostg segs (refill_tree kBatchClass X)
  (fun r : unit * astate => regs_only X (snd r) /\ st_cache_inited (snd r) = true /\
     pc_chunks (cache (snd r) kBatchClass) <> []) W1 c1 _ APOST RR) as RR2.
clear RR APOST.
eapply amreal_mono; [|exact RR2]. cbv beta.
intros [[] X1] W5 c5 [(RO & CI & NE1) LEAF].
cbn [fst snd] in RO, CI, NE1, LEAF.
split; [exact NE1|].
intros l El1.
assert (Hlne : l <> []) by (rewrite <- El1; exact NE1).
pose proof RO as RO'. destruct RO' as (Rck & _ & _ & _ & _ & _ & Rfs & _).
pose proof (RMAX inst ly X W regs mem md k c1 X1 W5 c5 l PRE LEAF CI El1 Hlne) as HRM.
(* the tail segment, from the leaf's configuration *)
eapply SRr_mono;
[exact (WALK2 inst ly X W regs mem md k W1 c1 X1 W5 c5 l PRE HNB Hl0 HC LEAF RO CI El1 Hlne HN HRM)|].
intros W6 c6 _ HR6.
pose proof (POSTF inst ly X W regs mem md k W1 c1 X1 W5 c5 l W6 c6
  PRE HNB Hl0 HC LEAF RO CI El1 Hlne HR6) as PLEAF.
destruct (FRAME2 ly X W regs mem md k X1 W5 c5 l W6 c6 HR6) as (regs2 & mem2 & md2 & Hc2 & MEQ2).
destruct PLEAF as (regs' & mem' & md' & nb & Hc & POST & Hqt & Hnbm & Hch & Hqg & Hfs).
assert (Em : mem' = mem2).
{ pose proof (cfg_mem_eq_g _ _ (eq_trans (eq_sym Hc) Hc2)) as E. cbn in E. exact E. }
destruct (FRAMER inst ly X W regs mem md k W1 c1 (tt, X1) W5 c5 PRE HNB Hl0 HC LEAF NE1) as (FRR & MKR).
cbn [snd] in FRR.
(* THE RAW FRAME, in three parts: the tail segment's window frame, the refill's own raw frame, the first
   segment's window frame. *)
assert (FRs : forall x : word, ~ AOX ly X (bv_unsigned x) ->
  ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) -> mem' x = mem x).
{ intros x NO NS.
  assert (NO1 : ~ AOX ly X1 (bv_unsigned x))
    by (intros O; apply NO; exact (AOXM ly X X1 (bv_unsigned x) Rck Rfs O)).
  rewrite Em.
  rewrite (MEQ2 x ltac:(intros HW;
    destruct (OWN2 inst ly X W regs mem md k c1 X1 W5 c5 l (bv_unsigned x)
      PRE HNB Hl0 LEAF CI El1 Hlne (u64_range x) HW) as [O|O]; [exact (NO1 O) | exact (NS O)])).
  rewrite (FRR x NO NO1 NS).
  apply (FRAME1 inst ly X W regs mem md k W1 c1 PRE HNB Hl0 HC x).
  intros HW.
  destruct (OWN1 inst ly X W regs mem md k (bv_unsigned x) PRE HNB Hl0 (u64_range x) HW) as [O|O];
    [exact (NO O) | exact (NS O)]. }
(* THE MEMNORM KEEP, in three parts, chained by MemnormLocG.memnorm_keep_trans. *)
assert (MK1 : MemnormT.memnorm_keep segs mem (ms_mem (cfg_ms c1))).
{ apply (MemnormT.memnorm_frame segs (WINc ly regs X) mem (ms_mem (cfg_ms c1))).
  - intros x HW. exact (SAFE1 inst ly X W regs mem md k x PRE HNB Hl0 HW).
  - intros x NW. exact (FRAME1 inst ly X W regs mem md k W1 c1 PRE HNB Hl0 HC x NW). }
assert (MK3 : MemnormT.memnorm_keep segs (ms_mem (cfg_ms c5)) mem').
{ apply (MemnormT.memnorm_frame segs (WINm ly regs X1 l) (ms_mem (cfg_ms c5)) mem').
  - intros x HW. exact (SAFE2 inst ly X W regs mem md k c1 X1 W5 c5 l x PRE HNB Hl0 LEAF CI El1 Hlne HW).
  - intros x NW. rewrite Em. exact (MEQ2 x NW). }
assert (MNK : MemnormT.memnorm_keep segs mem mem')
  by exact (MemnormLocG.memnorm_keep_trans segs mem (ms_mem (cfg_ms c1)) mem' MK1
              (MemnormLocG.memnorm_keep_trans segs (ms_mem (cfg_ms c1)) (ms_mem (cfg_ms c5)) mem' MKR MK3)).
split; [| exists regs', mem', md'; split; [exact Hc | exact MNK]].
split; [| exists regs', mem', md'; split; [exact Hc | exact FRs]].
exists regs', mem', md', nb.
split; [exact Hc|].
split.
{ destruct POST as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
  split; [exact AR'|]. split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
  split; [exact AGV|]. split; [| exact PRS].
  intros x NO NO' NS NE. apply FRs; [exact NO|]. intros O. apply NS. unfold ascratch. left. exact O. }
split; [exact Hqt|]. split; [exact Hnbm|]. split; [exact Hch|]. split; [exact Hqg|]. exact Hfs.
Qed.

End b.
End a.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check enq_miss_g.
Print Assumptions enq_miss_g.
