(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/EnqGbase.v (commit 9910d964c1cb, B2's final arms, taken by path at F1; file sha256 21597ef008ab) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/EnqGbase.v at commit f303438be5b, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B2 of the Theorem Labs lane walk lanes; integrator ReallocPrimary).
   rule 24: proves function __sanitizer::QuarantineCache<__asan::QuarantineCallback>::Enqueue (the room / hit / miss
   arms as called from QuarantineChunk), frame-generic, at cgif_file_fuzzer's asan-ubsan image (Enqueue 0x360ec).
   Reuse search: `proof-index Enqueue QuarantineBatch QuarantineCache Put` 2026-10-29T23:07:48Z, exit 3,
   verbatim in the Theorem Labs lane's frame note LOOKUP-B2-enqueue.txt (sha256 7fa7207b8221; internal record); rule-24 check B2LookupCheck (sonic,
   read-only): CONFIRM.

   THE INTERFACE between the Enqueue arms and an allocator relation.

   cgif's released arms (YFg4 / YFg5 / YFg6 with YFf1 / YFf2, 3,484 lines) are stated over cgif's own relation and
   over cgif's image: they read [ARm] and [Wf] directly, and name [tfibsegs], Enqueue's entry pc and the walk's
   window.  Here all of that becomes NAMED parameters, the way c5 generalized Allocate (AGif0n.AIface):
   - the model side: an opaque relation [ARX], an opaque owned set [AOX], an opaque call premise [EPRE];
   - the image side: the segment list [segs], Enqueue's entry [A_ENQ], and, per arm, the walk's post [ARET*] and
     the walk's window [WIN*].
   So this file and the three arms name NO image and NO model.  An instance proves each field once: cgif_file's is
   EnqGcgif.v (from the released lemmas), the shared cf instance's is the layer's (CfF1's YGcfInstEnq.v), and a
   unit that relocates the walk gives its own [ARET*] / [WIN*] without touching the arms.

   What stays here, and is therefore proved ONCE for every instance and every image:
   - the model's step equation at the arm (YFfp.enqueue_room_eq; the hit arm's is the field [ih_shape], because it
     reads the class-24 cache);
   - the run: the walk's post is turned into the call post the consumer states ([CLenq.enq_leaf_x]);
   - the RAW frame of [CLenq.acall_post_x] (the released post frames the view only), derived from the walk's own
     window frame ([*_frame]) and the field [*_owned]: every byte the arm writes is owned by the allocator or lies
     in Enqueue's stack scratch;
   - the memnorm keep of the post of record, derived from the same window frame and the field [*_safe].

   SIZE BOUNDS (Main 2026-10-29 23:3xZ; the lane brief's "Known open bound").  No literal bound is written in this
   file or in the arms.  Two Section Variables carry them:
   - [NMAXD], the block-size bound of the Deallocate side.  USED ONLY in [ir_nmax] / [ih_nmax] and in the premise
     of [ir_walk] / [ih_walk].  cgif_file's instance takes NMAXD := 2 ^ 28 (the released walk's own bound,
     YFgp.v:97 fh_Hnn and the reg-35 atom :73; YFgq.v:125 / :99).  The cf instance takes NMAXD := cf_malloc_max,
     whose walk is the widened one (route A or B of DEALLOC-NMAX): it plugs into the SAME field, with no change to
     this file or to the arms.
   - [RMAXD], the class-24 region's mapped-user bound, from which the walk's batch-byte bound is derived.  USED
     ONLY in [ih_rmax] and in the premise of [ih_walk].  cgif_file takes RMAXD := 2 ^ 31 (YFf2.nb_geom's fifth
     conjunct, through YFgq.v:134 fh_hit and the reg-41 atom :104); the cf instance takes RMAXD := kFreeArrayOffset,
     which its [batch_room_cf] premise (YG00cf.v:361-362) gives at once.

   EVENT-TERM GATE (Main 22:59Z): the room comes from BYTES.  No field of this file names [st_nev], [EV_A],
   [EV_MAX], [EV_BIG], [mtr_ok], [aregime] or a non-cf [abudget]; the event count enters only through the opaque
   [EPRE], which each instance states. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLenq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* The config's memory, read off a config equation: the walk's frame and the instance's leaf share one config
   (copy of CLenqcgif.v:46, which this file may not import: that file is cgif's instance). *)
Lemma cfg_mem_eq_g : forall (c1 c2 : config), c1 = c2 -> ms_mem (cfg_ms c1) = ms_mem (cfg_ms c2).
Proof. intros c1 c2 E. rewrite E. reflexivity. Qed.

Section b.
(* ---- The image. ---- *)
(* The loaded segments and Enqueue's entry pc.  cgif_file: tfibsegs and YFew.A_Enqueue; the cf layer: im_segs and
   dg_enqueue (ImgBase.AImg, ImgBaseDG.DImg). *)
Variable segs : list Segment.
Variable A_ENQ : Z.

Variable B : asyms.

(* ---- The model. ---- *)
(* [EPRE] is opaque: the cf instance's premise drops cgif's budget, [refill_reg] and the [rroom] half of
   [qloosem] (CfF1, 2026-10-29 23:5xZ), and no arm below reads them. *)
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable EPRE : Z -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk -> Prop.

(* The two size bounds (see the header). *)
Variables (NMAXD RMAXD : Z).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The post of an arm.                                                                                               *)

(* The call post MINUS the raw-memory clause: what an instance's AR transport delivers.  Clause by clause this is
   CLenq.acall_post_x (CLenq.v:52-62) without its clause 7, over [ARX] / [AOX]. *)
Definition acall_post_g0 (inst stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

(* CLenq.enq_leaf_x (CLenq.v:82-91) with [acall_post_g0] in place of [acall_post_x]. *)
Definition enq_leaf_g0 (inst : Z) (ly : alayout) (X : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists regs' mem' md' nb,
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_g0 inst CLenq.QSTACK_G ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
st_qthread (snd r) = qc_push (st_qthread X) k nb /\
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end /\
st_chunks (snd r) = st_chunks X /\ st_qglobal (snd r) = st_qglobal X /\
st_fs (snd r) = st_fs X.

(* CLenqcgif.enq_leaf_xs (CLenqcgif.v:65-72) over [ARX] / [AOX]: the generic leaf with the arm's own raw frame
   (the bytes the pre-state's allocator owns, and Enqueue's stack window). *)
Definition enq_leaf_xs_g (inst : Z) (ly : alayout) (X : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
CLenq.enq_leaf_x segs B ARX AOX inst ly X W regs mem md k r W' c' /\
exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
(forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) ->
   mem' x = mem x).

(* The post of record of an arm (MnEnqArms.v:55-56 / :120-121 / :191-192, and the seam's EnqArmsCf fields): the
   leaf with the raw frame, plus the memnorm keep at the return configuration. *)
Definition enq_arm_post_g (inst : Z) (ly : alayout) (X : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
enq_leaf_xs_g inst ly X W regs mem md k r W' c' /\
exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ MemnormT.memnorm_keep segs mem mem'.

(* The state the room arm ends in (YFfp.enqueue_room_eq). *)
Definition Sroom (X : astate) (k : chunk) : astate := set_qthread (qc_push (st_qthread X) k None) X.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The room arm's interface: the last batch has a free slot (need_new_batch = false).                               *)

(* The walk's post and the walk's window, per image.  cgif_file: [YFgp.at_RETP W ly regs mem md u nn ql qb cnt bsz]
   and [YFgp.WIN ly regs ql cnt], at the numbers YFg4 reads off the state. *)
Variable ARETr : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk ->
  world segs -> config -> Prop.
Variable WINr : alayout -> bvmap 5 word -> astate -> Z -> Prop.

Record EnqIfaceRoom : Prop := {
  (* the block-size bound of this instance (NMAXD; no literal here) *)
  ir_nmax : forall inst ly X W regs mem md k, EPRE inst ly X W regs mem md k -> 1 <= ck_n k < NMAXD;
  (* the walk at the arm: Enqueue's entry to its return (cgif: YFh3.segP with YFg4.FH_ok) *)
  ir_walk : forall inst ly X W regs mem md k,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false -> 1 <= ck_n k < NMAXD ->
    SRr segs W (cfg_at segs A_ENQ regs mem md) (ARETr ly X W regs mem md k);
  (* the walk returns to the caller and kept every byte outside its window (cgif: at_RETP's config clause and its
     [YFgp.MEQ] clause) *)
  ir_frame : forall ly X W regs mem md k W' c',
    ARETr ly X W regs mem md k W' c' ->
    exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\
      (forall x : word, ~ WINr ly regs X (bv_unsigned x) -> mem' x = mem x);
  (* the relation at the post state, from the walk's post (cgif: YFg4.FINPH through YFf1.enq_finp_ARm) *)
  ir_post : forall inst ly X W regs mem md k W' c',
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false ->
    ARETr ly X W regs mem md k W' c' ->
    enq_leaf_g0 inst ly X W regs mem md k (tt, Sroom X k) W' c';
  (* every byte of the arm's window is owned by the allocator or lies in Enqueue's stack scratch
     (cgif: YFgp.WIN inside YFf1.D, then YFf1.D_owned) *)
  ir_owned : forall inst ly X W regs mem md k a,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false -> 0 <= a < 2 ^ 64 ->
    WINr ly regs X a -> AOX ly X a \/ (spZ regs - CLenq.QSTACK_G <= a < spZ regs);
  (* every byte of the arm's window is memnorm-safe (cgif: MemnormLoc.YFf1_D_safe) *)
  ir_safe : forall inst ly X W regs mem md k (x : word),
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false ->
    WINr ly regs X (bv_unsigned x) -> MemnormT.mn_safe segs x
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The hit arm's interface: a new batch is needed and the class-24 cache is not empty.                              *)

(* The walk's post and window of the hit arm, per image.  cgif_file: [YFh4.at_RETQ ...] and [YFgq.WIN ...] at the
   cache list's length and last offset. *)
Variable ARETh : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> chunk ->
  list Z -> world segs -> config -> Prop.
Variable WINh : alayout -> bvmap 5 word -> astate -> list Z -> Z -> Prop.
(* The state the hit arm ends in.  cgif_file: YFf2.S' X k l. *)
Variable Shit : astate -> chunk -> list Z -> astate.

Record EnqIfaceHit : Prop := {
  ih_nmax : forall inst ly X W regs mem md k, EPRE inst ly X W regs mem md k -> 1 <= ck_n k < NMAXD;
  (* RMAXD's window, in B1's form (DMwalkIF.v:307 rmaxd_ok at 3e29c198d40; B1's RevIF2 measured that an upper
     bound of 2 ^ 32 is FALSE at the frame: the class's free array sits at region_off c + kFreeArrayOffset while
     [puser] covers region_base .. + rg_alloc_user, so an allocated part above kFreeArrayOffset would put the
     free-array stores inside puser, YFgk.v:153 fh_Hoff).  It is an interface FIELD, not a Section hypothesis,
     because no arm reads it: Coq abstracts a Section hypothesis only over the lemmas that use it, so a bare
     hypothesis would not reach the tops at all.  As a field it is a compiled lemma at each instance. *)
  ih_rmaxd_ok : 2 ^ 31 <= RMAXD <= kFreeArrayOffset;
  (* the class-24 region's mapped-user bound of this instance (RMAXD; no literal here).  cgif_file takes
     RMAXD := 2 ^ 31 (YFf2.nb_geom's fifth conjunct); the cf instance takes RMAXD := kFreeArrayOffset, which
     [batch_room_cf] (YG00cf.v:361-362, `rg_mapped_user + kUserMapSize <= kFreeArrayOffset`) gives at once. *)
  ih_rmax : forall inst ly X W regs mem md k l, EPRE inst ly X W regs mem md k ->
    need_new_batch (st_qthread X) = true -> pc_chunks (cache X kBatchClass) = l -> l <> [] ->
    rg_mapped_user (reg X kBatchClass) <= RMAXD;
  (* the walk (cgif: YFh4.segQH with YFg5.FH_ok and the cache cell) *)
  ih_walk : forall inst ly X W regs mem md k l,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = l -> l <> [] ->
    1 <= ck_n k < NMAXD -> rg_mapped_user (reg X kBatchClass) <= RMAXD ->
    SRr segs W (cfg_at segs A_ENQ regs mem md) (ARETh ly X W regs mem md k l);
  ih_frame : forall ly X W regs mem md k l W' c',
    ARETh ly X W regs mem md k l W' c' ->
    exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\
      (forall x : word, ~ WINh ly regs X l (bv_unsigned x) -> mem' x = mem x);
  (* the model's step equation at the arm (cgif: YFg5.enqueue_hit_eq) *)
  ih_shape : forall inst ly X W regs mem md k l,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = l -> l <> [] ->
    enqueue k X = IRet (tt, Shit X k l);
  (* the relation at the post state (cgif: YFg5.FINQH through YFf2.enq_fin_ARm) *)
  ih_post : forall inst ly X W regs mem md k l W' c',
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = l -> l <> [] ->
    ARETh ly X W regs mem md k l W' c' ->
    enq_leaf_g0 inst ly X W regs mem md k (tt, Shit X k l) W' c';
  ih_owned : forall inst ly X W regs mem md k l a,
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = l -> l <> [] -> 0 <= a < 2 ^ 64 ->
    WINh ly regs X l a -> AOX ly X a \/ (spZ regs - CLenq.QSTACK_G <= a < spZ regs);
  ih_safe : forall inst ly X W regs mem md k l (x : word),
    EPRE inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = l -> l <> [] ->
    WINh ly regs X l (bv_unsigned x) -> MemnormT.mn_safe segs x
}.

End b.
End a.
