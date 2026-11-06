(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormT.v (commit 30a1993588f, c5 + memnorm; file sha256 5e3ba9244793) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/MemnormT.v (commit d2dafa219c1, file sha256 1881f16d9ea9) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* Theorem Labs, 2026-10: memnorm-keeping twins of the frozen Allocate / Deallocate contracts (task MEMNORM, a Theorem Labs lane;
   integrator ReallocPrimary), image-free.  rule 24: no function proved (kind: top-level corollaries).

   WHAT: a leaf twin carries `memnorm segs mem -> memnorm segs mem'` (YAkMemnorm.memnorm, the overlay normal form) as a
   conjunct inside the leaf's own existential, next to errno:
   - Allocate: [alloc_leaf_em] = ErrnoG.alloc_leaf_e + the keep, [alloc_leaf_m] = AllocG.alloc_leaf + the keep, and
     the contracts aalloc_prim_realizes_em / aalloc_realizes_em / _m;
   - Deallocate: [dealloc_leaf_raw_em] / [dealloc_leaf_raw_m] on the raw post, and the view forms [dealloc_leaf_em] /
     [dealloc_leaf_m] from them (DeallocG.dealloc_post_raw implies DeallocG.dealloc_post);
   - each contract twin is a corollary of the released one by amreal_mono, from the zone Props below; the per-leaf
     forms ([*_keep]) give a consumer the keep at the leaf's end configuration.

   WHY IT IS A COROLLARY (and not a run invariant): the posts carry a RAW frame.  AllocG.alloc_post (AllocG.v:99-100)
   and DeallocG.dealloc_post_raw (DeallocG.v:137-138) state `mem' x = mem x` for every x outside four zones: the
   owned sets AOX ly S and AOX ly' S', the scratch [ascratch B stk regs] (YG0d.v:219-220: the stack window
   [sp - stk, sp) and errno's 4 bytes) and E (the new / freed block).  memnorm (YAkMemnorm.v:41-43) says of the raw
   overlay only: no byte at a read-only address (ro_addr) and every byte in a segment or below TASK_SIZE.  So
   memnorm_frame below: if every zone byte is [mn_safe] (ro_addr false, below TASK_SIZE), the keep holds.  Its proof
   cases on ro_addr (a bool) and on the bound (Z_lt_le_dec), never on zone membership, so no zone needs to be decidable.

   WHY THE BRIEF'S COUNTERMODELS CANNOT ARISE.  "A ROM byte copied into the overlay" puts a byte at an address where
   ro_addr is true; "an extra hidden byte" puts one where the frame does not hold.  Both are outside the frame, so
   both lie in a zone; a zone byte is mn_safe by the Props, so ro_addr is false there and the address is below
   TASK_SIZE: neither countermodel is a state the post admits once the Props hold.

   WHERE THE PROPS FAIL (measured after this file was written): mn_owned_wr is FALSE at cgif_file.  tfibsegs' segment
   [0x10000, 0x30000) is read-only, and the owned statics (YF0m.v:279-285 Tfib_owned_static, through YG0d.v:485
   AR_owned_image_law) include bytes in it ((0x102e8, 8) ... (0x20e62, 0x1e)); a Theorem Labs lane reports the same at preset.  So
   at those instances the contract-level corollaries below do not close: the keep is taken instead from each arm's own
   raw frame (MemnormHitG.v, MemnormHitK.v, MemnormDnull.v, MemnormDcommon.v) and from the callee walks' window frames
   (MemnormLoc.v / MemnormLocG.v).  The other five Props are expected to hold at cgif, from these laws (no file
   discharges them, since the corollaries cannot close without mn_owned_wr): mn_owned_low (YG0d.v:483
   AR_owned_low_law, below alloc_ceiling), mn_stack (layout_ok), mn_block (YG0d.v:434-440 AR_blocks_law, :489-494
   AR_client_img_law), mn_errno (errno in a writable segment), mn_new_block (YG07.v:271 with YG01.v:555-562).  The
   leaf definitions here (alloc_leaf_em, dealloc_leaf_raw_em, dealloc_leaf_em, ...) are the forms the arm twins
   conclude.

   THE ZONE PROPS (each stated once, over ARX / AOX / the image's segs and symbols, so that an instance that satisfies
   them can discharge them for its own image):
   - [mn_owned_low]: an owned address is below TASK_SIZE;
   - [mn_owned_wr]: a segment holding an owned address is writable;
   - [mn_stack]: the layout's stack [ly_stk_lo, ly_stk_hi) is mn_safe;
   - [mn_block]: a live block's bytes are mn_safe;
   - [mn_scratch stk]: the scratch window of a call with stk bytes of stack is mn_safe (a lemma from mn_stack and
     mn_errno: [mn_scratch_of]);
   - [mn_errno]: errno's 4 bytes are mn_safe;
   - and one model Prop, [mn_new_block]: on a block result, the new block is live in the result state (cgif:
     YG07.v:271 malloc_gen with YG01.v:555-562 malloc_post).
   Additive: AllocG, DeallocG, ErrnoG and every existing statement are unchanged.
   FIELD ROUND 3 PART 3b (a Theorem Labs lane, a Theorem Labs lane ruling 2026-10-30 18:50Z): the two Allocate em contracts
   (aalloc_prim_realizes_em, aalloc_realizes_em) take `MP mem ->` right after alloc_pre, as the Deallocate contracts
   took it in part 3; aalloc_*_realizes_em_e now read the em contract at an MP every memory satisfies. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The frame lemma.                                                                                                 *)

(* a byte where the overlay may hold anything without breaking memnorm *)
Definition mn_safe (segs : list Segment) (x : word) : Prop :=
  YAkMemnorm.ro_addr segs x = false /\ bv_unsigned x < TASK_SIZE.

(* the keep the twins carry *)
Definition memnorm_keep (segs : list Segment) (mem mem' : word -> option byte) : Prop :=
  YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'.

Lemma memnorm_frame : forall segs (Zs : Z -> Prop) (mem mem' : word -> option byte),
  (forall x : word, Zs (bv_unsigned x) -> mn_safe segs x) ->
  (forall x : word, ~ Zs (bv_unsigned x) -> mem' x = mem x) ->
  memnorm_keep segs mem mem'.
Proof.
intros segs Zs mem mem' HS Hf [Hi Ht]. split; intros x b E.
- destruct (YAkMemnorm.ro_addr segs x) eqn:R; [|reflexivity]. exfalso.
  assert (NZ : ~ Zs (bv_unsigned x)) by (intros Hz; destruct (HS x Hz) as [R' _]; congruence).
  rewrite (Hf x NZ) in E. rewrite (Hi x b E) in R. discriminate R.
- destruct (Z_lt_le_dec (bv_unsigned x) TASK_SIZE) as [L|L]; [right; exact L|].
  assert (NZ : ~ Zs (bv_unsigned x)) by (intros Hz; destruct (HS x Hz) as [_ L']; lia).
  rewrite (Hf x NZ) in E. exact (Ht x b E).
Qed.

(* the four-zone form of the posts' raw frames (AllocG.v:99-100, DeallocG.v:137-138) *)
Lemma memnorm_frame4 : forall segs (Z1 Z2 Z3 Z4 : Z -> Prop) (mem mem' : word -> option byte),
  (forall x : word, Z1 (bv_unsigned x) -> mn_safe segs x) ->
  (forall x : word, Z2 (bv_unsigned x) -> mn_safe segs x) ->
  (forall x : word, Z3 (bv_unsigned x) -> mn_safe segs x) ->
  (forall x : word, Z4 (bv_unsigned x) -> mn_safe segs x) ->
  (forall x : word, ~ Z1 (bv_unsigned x) -> ~ Z2 (bv_unsigned x) -> ~ Z3 (bv_unsigned x) -> ~ Z4 (bv_unsigned x) ->
    mem' x = mem x) ->
  memnorm_keep segs mem mem'.
Proof.
intros segs Z1 Z2 Z3 Z4 mem mem' H1 H2 H3 H4 Hf.
apply (memnorm_frame segs (fun a => Z1 a \/ Z2 a \/ Z3 a \/ Z4 a)).
- intros x [Hz|[Hz|[Hz|Hz]]]; [exact (H1 x Hz) | exact (H2 x Hz) | exact (H3 x Hz) | exact (H4 x Hz)].
- intros x NZ. apply Hf; intros Hz; apply NZ; tauto.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The zone Props, over ARX / AOX and the image's segs and symbols.                                                 *)
Section zn.
Variable segs : list Segment.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.

Definition mn_owned_low : Prop :=
  forall inst ly S W mem md a, ARX inst ly S W mem md -> AOX ly S a -> 0 <= a < TASK_SIZE.

Definition mn_owned_wr : Prop :=
  forall inst ly S W mem md (x : word) seg, ARX inst ly S W mem md -> AOX ly S (bv_unsigned x) ->
  find_segment segs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true.

Definition mn_stack : Prop :=
  forall inst ly S W mem md (x : word), ARX inst ly S W mem md ->
  ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly -> mn_safe segs x.

Definition mn_block : Prop :=
  forall inst ly S W mem md (p : sptr) (n : Z) (x : word), ARX inst ly S W mem md -> In (p, n) (blocks S) ->
  sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n -> mn_safe segs x.

Definition mn_scratch (stk : Z) : Prop :=
  forall inst ly S W mem md regs (x : word), ARX inst ly S W mem md ->
  ly_stk_lo ly + stk <= spZ regs -> spZ regs <= ly_stk_hi ly -> ascratch B stk regs (bv_unsigned x) -> mn_safe segs x.

Definition mn_errno : Prop :=
  forall x : word, as_errno B <= bv_unsigned x < as_errno B + 4 -> mn_safe segs x.

Lemma mn_owned_safe : mn_owned_low -> mn_owned_wr ->
  forall inst ly S W mem md (x : word), ARX inst ly S W mem md -> AOX ly S (bv_unsigned x) -> mn_safe segs x.
Proof.
intros HL HW inst ly S W mem md x HA Ho. split.
- unfold YAkMemnorm.ro_addr. destruct (find_segment segs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
  rewrite (HW inst ly S W mem md x seg HA Ho F). reflexivity.
- exact (proj2 (HL inst ly S W mem md _ HA Ho)).
Qed.

Lemma mn_scratch_of : mn_stack -> mn_errno -> forall stk, 0 <= stk -> mn_scratch stk.
Proof.
intros HS HE stk Hstk inst ly S W mem md regs x HA Hlo Hhi [Hw|He].
- apply (HS inst ly S W mem md x HA). lia.
- exact (HE x He).
Qed.
End zn.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Allocate: AllocG's section variables, in AllocG's order (as ErrnoG.v's Section al).                             *)
Section al.
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable pcA : Z.
Variable oomb : Z.
Variable al : Z.
Variable atp : Z.
Variable cf : Z.
(* field round 3 part 3b: the memory precondition the Allocate em contracts take at the call, as Deallocate's MP
   (Section dl below); the cf instance sets it to the overlay normal form and arodata_ok_cf (YGcfMallocComposeE). *)
Variable MP : (word -> option byte) -> Prop.

(* the model Prop: on a block result of a granted path, the new block is live in the result state *)
Definition mn_new_block : Prop :=
  forall inst so bp ly S W regs mem md n tr trc (r : sptr * astate),
  alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
  apath (mt n tr S) trc r -> gflag trc = true -> fst r <> PNull -> In (fst r, n) (blocks (snd r)).

(* AllocG.alloc_leaf with the keep *)
Definition alloc_leaf_m (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
alloc_post segs B ARX AOX inst ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
memnorm_keep segs mem mem' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
lpost (snd r) /\
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) /\
(fst r = PNull -> val_mem segs (mrestrict (w_H W') mem') oomb 1 1).

(* ErrnoG.alloc_leaf_e with the keep (the keep right after errno, inside the same existential) *)
Definition alloc_leaf_em (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
alloc_post segs B ARX AOX inst ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
(fst r <> PNull -> ErrnoG.errno_kept B mem mem') /\
memnorm_keep segs mem mem' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
lpost (snd r) /\
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) /\
(fst r = PNull -> val_mem segs (mrestrict (w_H W') mem') oomb 1 1).

Definition aalloc_prim_realizes_m : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr -> n <= 64512 ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md) (alloc_leaf_m inst ly S W regs mem md n tr).

Definition aalloc_realizes_m : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md) (alloc_leaf_m inst ly S W regs mem md n tr).

Definition aalloc_prim_realizes_em : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr -> MP mem -> n <= 64512 ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md) (alloc_leaf_em inst ly S W regs mem md n tr).

Definition aalloc_realizes_em : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr -> MP mem ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md) (alloc_leaf_em inst ly S W regs mem md n tr).

Section z.
Hypothesis OL : mn_owned_low segs ARX AOX.
Hypothesis OW : mn_owned_wr segs ARX AOX.
Hypothesis SC : mn_scratch segs B ARX AFSTACK_G.
Hypothesis BL : mn_block segs B ARX.
Hypothesis NB : mn_new_block.

(* the keep from alloc_post's raw frame (AllocG.v:99-100) *)
Lemma alloc_post_keep : forall inst so bp ly S W regs mem md n tr (r : sptr * astate) ly' W' regs' mem' md',
  alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
  (fst r <> PNull -> In (fst r, n) (blocks (snd r))) ->
  alloc_post segs B ARX AOX inst ly S W regs mem md
    (fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
    ly' (snd r) W' regs' mem' md' ->
  memnorm_keep segs mem mem'.
Proof.
intros inst so bp ly S W regs mem md n tr r ly' W' regs' mem' md' PRE HIN
  (HARX' & _ & _ & _ & _ & _ & RAW & _).
destruct PRE as (HARX & _ & _ & _ & _ & Hlo & _ & Hhi & _).
apply (memnorm_frame4 segs (AOX ly S) (AOX ly' (snd r)) (ascratch B AFSTACK_G regs)
  (fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) mem mem').
- intros x Hx. exact (mn_owned_safe segs ARX AOX OL OW inst ly S W mem md x HARX Hx).
- intros x Hx. exact (mn_owned_safe segs ARX AOX OL OW inst ly' (snd r) W' mem' md' x HARX' Hx).
- intros x Hx. exact (SC inst ly S W mem md regs x HARX Hlo Hhi Hx).
- intros x [Hn Hx]. exact (BL inst ly' (snd r) W' mem' md' (fst r) n x HARX' (HIN Hn) Hx).
- exact RAW.
Qed.

Lemma alloc_leaf_m_of : forall inst so bp ly S W regs mem md n tr r W' c',
  alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
  alloc_leaf segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' ->
  alloc_leaf_m inst ly S W regs mem md n tr r W' c'.
Proof.
intros inst so bp ly S W regs mem md n tr r W' c' PRE (ly' & regs' & mem' & md' & Hc & HP & HR & HL & HT & HO).
assert (HK : memnorm_keep segs mem mem').
{ apply (alloc_post_keep inst so bp ly S W regs mem md n tr r ly' W' regs' mem' md' PRE); [|exact HP].
  intros Hn. destruct HT as (trc & Ha & Hg). exact (NB inst so bp ly S W regs mem md n tr trc r PRE Ha Hg Hn). }
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HK|]. split; [exact HR|].
split; [exact HL|]. split; [exact HT | exact HO].
Qed.

Lemma alloc_leaf_em_of_e : forall inst so bp ly S W regs mem md n tr r W' c',
  alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
  ErrnoG.alloc_leaf_e segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' ->
  alloc_leaf_em inst ly S W regs mem md n tr r W' c'.
Proof.
intros inst so bp ly S W regs mem md n tr r W' c' PRE (ly' & regs' & mem' & md' & Hc & HP & HE & HR & HL & HT & HO).
assert (HK : memnorm_keep segs mem mem').
{ apply (alloc_post_keep inst so bp ly S W regs mem md n tr r ly' W' regs' mem' md' PRE); [|exact HP].
  intros Hn. destruct HT as (trc & Ha & Hg). exact (NB inst so bp ly S W regs mem md n tr trc r PRE Ha Hg Hn). }
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HK|].
split; [exact HR|]. split; [exact HL|]. split; [exact HT | exact HO].
Qed.

(* the consumer's per-leaf shape, one step from the released leaf: the keep at the leaf's end configuration *)
Lemma alloc_leaf_keep : forall inst so bp ly S W regs mem md n tr r W' c',
  alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
  alloc_leaf segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ memnorm_keep segs mem mem'.
Proof.
intros inst so bp ly S W regs mem md n tr r W' c' PRE HL.
destruct (alloc_leaf_m_of inst so bp ly S W regs mem md n tr r W' c' PRE HL) as (ly' & regs' & mem' & md' & Hc & _ & HK & _).
exists regs', mem', md'. exact (conj Hc HK).
Qed.

Corollary aalloc_prim_realizes_m_of : aalloc_prim_realizes segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf ->
  aalloc_prim_realizes_m.
Proof.
intros H inst so bp ly S W regs mem md n tr P N.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P N)].
intros r W' c' HL. exact (alloc_leaf_m_of inst so bp ly S W regs mem md n tr r W' c' P HL).
Qed.

Corollary aalloc_realizes_m_of : aalloc_realizes segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf ->
  aalloc_realizes_m.
Proof.
intros H inst so bp ly S W regs mem md n tr P.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P)].
intros r W' c' HL. exact (alloc_leaf_m_of inst so bp ly S W regs mem md n tr r W' c' P HL).
Qed.

Corollary aalloc_prim_realizes_em_of_e :
  ErrnoG.aalloc_prim_realizes_e segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf ->
  aalloc_prim_realizes_em.
Proof.
intros H inst so bp ly S W regs mem md n tr P _ N.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P N)].
intros r W' c' HL. exact (alloc_leaf_em_of_e inst so bp ly S W regs mem md n tr r W' c' P HL).
Qed.

Corollary aalloc_realizes_em_of_e :
  ErrnoG.aalloc_realizes_e segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf ->
  aalloc_realizes_em.
Proof.
intros H inst so bp ly S W regs mem md n tr P _.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P)].
intros r W' c' HL. exact (alloc_leaf_em_of_e inst so bp ly S W regs mem md n tr r W' c' P HL).
Qed.
End z.

(* the bridges back (drop the keep), and the keep by projection *)
Lemma alloc_leaf_em_e : forall inst ly S W regs mem md n tr r W' c',
  alloc_leaf_em inst ly S W regs mem md n tr r W' c' ->
  ErrnoG.alloc_leaf_e segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & _ & HR & HL & HT & HO).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HR|].
split; [exact HL|]. split; [exact HT | exact HO].
Qed.

Lemma alloc_leaf_m_leaf : forall inst ly S W regs mem md n tr r W' c',
  alloc_leaf_m inst ly S W regs mem md n tr r W' c' ->
  alloc_leaf segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HR & HL & HT & HO).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|].
split; [exact HL|]. split; [exact HT | exact HO].
Qed.

Lemma alloc_leaf_em_m : forall inst ly S W regs mem md n tr r W' c',
  alloc_leaf_em inst ly S W regs mem md n tr r W' c' -> alloc_leaf_m inst ly S W regs mem md n tr r W' c'.
Proof.
intros inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HK & HR & HL & HT & HO).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HK|]. split; [exact HR|].
split; [exact HL|]. split; [exact HT | exact HO].
Qed.

Lemma alloc_leaf_em_keep : forall inst ly S W regs mem md n tr r W' c',
  alloc_leaf_em inst ly S W regs mem md n tr r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ memnorm_keep segs mem mem'.
Proof.
intros inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & _ & _ & HK & _).
exists regs', mem', md'. exact (conj Hc HK).
Qed.

Lemma alloc_leaf_m_keep : forall inst ly S W regs mem md n tr r W' c',
  alloc_leaf_m inst ly S W regs mem md n tr r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ memnorm_keep segs mem mem'.
Proof.
intros inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & _ & HK & _).
exists regs', mem', md'. exact (conj Hc HK).
Qed.

(* At an MP that every memory satisfies (the classic contracts take no memory premise). *)
Lemma aalloc_prim_realizes_em_e : (forall m, MP m) -> aalloc_prim_realizes_em ->
  ErrnoG.aalloc_prim_realizes_e segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf.
Proof.
intros MPT H inst so bp ly S W regs mem md n tr P N.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P (MPT mem) N)].
exact (alloc_leaf_em_e inst ly S W regs mem md n tr).
Qed.

Lemma aalloc_realizes_em_e : (forall m, MP m) -> aalloc_realizes_em ->
  ErrnoG.aalloc_realizes_e segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf.
Proof.
intros MPT H inst so bp ly S W regs mem md n tr P.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P (MPT mem))].
exact (alloc_leaf_em_e inst ly S W regs mem md n tr).
Qed.
End al.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Deallocate: DeallocG's section variables, in DeallocG's order (as ErrnoG.v's Section dl).                       *)
Section dl.
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable pcD : Z.
Variable atp : Z.
Variable MP : (word -> option byte) -> Prop.

(* DeallocG.dealloc_leaf_raw with the keep *)
Definition dealloc_leaf_raw_m (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post_raw segs B ARX AOX inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
memnorm_keep segs mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

(* ErrnoG.dealloc_leaf_raw_e with the keep *)
Definition dealloc_leaf_raw_em (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post_raw segs B ARX AOX inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
ErrnoG.errno_kept B mem mem' /\
memnorm_keep segs mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

(* DeallocG.dealloc_leaf (the view) with the keep *)
Definition dealloc_leaf_m (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post segs B ARX AOX inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
memnorm_keep segs mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

(* ErrnoG.dealloc_leaf_e (the view, errno on the view) with the keep *)
Definition dealloc_leaf_em (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post segs B ARX AOX inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
ErrnoG.errno_kept_v segs B W W' mem mem' /\
memnorm_keep segs mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

Definition adealloc_realizes_raw_m : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md) (dealloc_leaf_raw_m inst ly S W regs mem md p n tr).

Definition adealloc_realizes_raw_em : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md) (dealloc_leaf_raw_em inst ly S W regs mem md p n tr).

Definition adealloc_realizes_m : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md) (dealloc_leaf_m inst ly S W regs mem md p n tr).

Definition adealloc_realizes_em : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md) (dealloc_leaf_em inst ly S W regs mem md p n tr).

(* raw -> view: dealloc_post_raw (DeallocG.v:128-139) holds dealloc_post (DeallocG.v:104-112) *)
Lemma dealloc_post_raw_post : forall inst ly S W regs mem md E ly' S' W' regs' mem' md',
  dealloc_post_raw segs B ARX AOX inst ly S W regs mem md E ly' S' W' regs' mem' md' ->
  dealloc_post segs B ARX AOX inst ly S W regs mem md E ly' S' W' regs' mem' md'.
Proof.
intros inst ly S W regs mem md E ly' S' W' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6 | exact H8].
Qed.

Section z.
Hypothesis OL : mn_owned_low segs ARX AOX.
Hypothesis OW : mn_owned_wr segs ARX AOX.
Hypothesis SC : mn_scratch segs B ARX DFSTACK_G.
Hypothesis BL : mn_block segs B ARX.

(* the keep from dealloc_post_raw's raw frame (DeallocG.v:137-138); the freed block is live at entry *)
Lemma dealloc_post_raw_keep : forall inst so bp ly S W regs mem md p n tr (S' : astate) ly' W' regs' mem' md',
  dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr ->
  dealloc_post_raw segs B ARX AOX inst ly S W regs mem md
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
    ly' S' W' regs' mem' md' ->
  memnorm_keep segs mem mem'.
Proof.
intros inst so bp ly S W regs mem md p n tr S' ly' W' regs' mem' md' PRE
  (HARX' & _ & _ & _ & _ & _ & RAW & _).
destruct PRE as (HARX & _ & _ & _ & _ & Hlo & _ & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & Hp & _).
apply (memnorm_frame4 segs (AOX ly S) (AOX ly' S') (ascratch B DFSTACK_G regs)
  (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) mem mem').
- intros x Hx. exact (mn_owned_safe segs ARX AOX OL OW inst ly S W mem md x HARX Hx).
- intros x Hx. exact (mn_owned_safe segs ARX AOX OL OW inst ly' S' W' mem' md' x HARX' Hx).
- intros x Hx. exact (SC inst ly S W mem md regs x HARX Hlo Hhi Hx).
- intros x [Hn Hx]. destruct Hp as [Hp|Hp]; [exfalso; exact (Hn Hp)|].
  exact (BL inst ly S W mem md p n x HARX Hp Hx).
- exact RAW.
Qed.

Lemma dealloc_leaf_raw_m_of : forall inst so bp ly S W regs mem md p n tr r W' c',
  dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr ->
  dealloc_leaf_raw segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' ->
  dealloc_leaf_raw_m inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst so bp ly S W regs mem md p n tr r W' c' PRE (ly' & regs' & mem' & md' & Hc & HP & HL & HT).
pose proof (dealloc_post_raw_keep inst so bp ly S W regs mem md p n tr (snd r) ly' W' regs' mem' md' PRE HP) as HK.
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HK|]. split; [exact HL | exact HT].
Qed.

Lemma dealloc_leaf_raw_em_of_e : forall inst so bp ly S W regs mem md p n tr r W' c',
  dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr ->
  ErrnoG.dealloc_leaf_raw_e segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' ->
  dealloc_leaf_raw_em inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst so bp ly S W regs mem md p n tr r W' c' PRE (ly' & regs' & mem' & md' & Hc & HP & HE & HL & HT).
pose proof (dealloc_post_raw_keep inst so bp ly S W regs mem md p n tr (snd r) ly' W' regs' mem' md' PRE HP) as HK.
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HK|].
split; [exact HL | exact HT].
Qed.

(* the consumer's per-leaf shape, one step from the released raw leaf *)
Lemma dealloc_leaf_raw_keep : forall inst so bp ly S W regs mem md p n tr r W' c',
  dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr ->
  dealloc_leaf_raw segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ memnorm_keep segs mem mem'.
Proof.
intros inst so bp ly S W regs mem md p n tr r W' c' PRE HL.
destruct (dealloc_leaf_raw_m_of inst so bp ly S W regs mem md p n tr r W' c' PRE HL) as (ly' & regs' & mem' & md' & Hc & _ & HK & _).
exists regs', mem', md'. exact (conj Hc HK).
Qed.

Corollary adealloc_realizes_raw_m_of : adealloc_realizes_raw segs B U ft ARX AOX rpre lpost fpre pcD atp MP ->
  adealloc_realizes_raw_m.
Proof.
intros H inst so bp ly S W regs mem md p n tr P HMP.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md p n tr P HMP)].
intros r W' c' HL. exact (dealloc_leaf_raw_m_of inst so bp ly S W regs mem md p n tr r W' c' P HL).
Qed.

Corollary adealloc_realizes_raw_em_of_e : ErrnoG.adealloc_realizes_raw_e segs B U ft ARX AOX rpre lpost fpre pcD atp MP ->
  adealloc_realizes_raw_em.
Proof.
intros H inst so bp ly S W regs mem md p n tr P HMP.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md p n tr P HMP)].
intros r W' c' HL. exact (dealloc_leaf_raw_em_of_e inst so bp ly S W regs mem md p n tr r W' c' P HL).
Qed.
End z.

(* raw -> view, for the twins *)
Lemma dealloc_leaf_m_of_raw_m : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_m inst ly S W regs mem md p n tr r W' c' -> dealloc_leaf_m inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HK & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact (dealloc_post_raw_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP)|].
split; [exact HK|]. split; [exact HL | exact HT].
Qed.

(* the view's errno conjunct needs errno kept on the raw memory to be kept on the view in any two worlds (cgif:
   ErrnoApart.errno_kept_v_of_raw from the image Prop errno_unhidden) *)
Lemma dealloc_leaf_em_of_raw_em :
  (forall (W W' : world segs) mem mem', ErrnoG.errno_kept B mem mem' -> ErrnoG.errno_kept_v segs B W W' mem mem') ->
  forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_em inst ly S W regs mem md p n tr r W' c' -> dealloc_leaf_em inst ly S W regs mem md p n tr r W' c'.
Proof.
intros EKV inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & HK & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact (dealloc_post_raw_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP)|].
split; [exact (EKV W W' mem mem' HE)|]. split; [exact HK|]. split; [exact HL | exact HT].
Qed.

Corollary adealloc_realizes_m_of_raw_m : adealloc_realizes_raw_m -> adealloc_realizes_m.
Proof.
intros H inst so bp ly S W regs mem md p n tr P HMP.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md p n tr P HMP)].
exact (dealloc_leaf_m_of_raw_m inst ly S W regs mem md p n tr).
Qed.

Corollary adealloc_realizes_em_of_raw_em :
  (forall (W W' : world segs) mem mem', ErrnoG.errno_kept B mem mem' -> ErrnoG.errno_kept_v segs B W W' mem mem') ->
  adealloc_realizes_raw_em -> adealloc_realizes_em.
Proof.
intros EKV H inst so bp ly S W regs mem md p n tr P HMP.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md p n tr P HMP)].
exact (dealloc_leaf_em_of_raw_em EKV inst ly S W regs mem md p n tr).
Qed.

(* the bridges back, and the keep by projection *)
Lemma dealloc_leaf_raw_em_e : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_em inst ly S W regs mem md p n tr r W' c' ->
  ErrnoG.dealloc_leaf_raw_e segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HL | exact HT].
Qed.

Lemma dealloc_leaf_raw_m_raw : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_m inst ly S W regs mem md p n tr r W' c' ->
  dealloc_leaf_raw segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HL | exact HT].
Qed.

Lemma dealloc_leaf_em_e : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_em inst ly S W regs mem md p n tr r W' c' ->
  ErrnoG.dealloc_leaf_e segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HL | exact HT].
Qed.

Lemma dealloc_leaf_raw_em_keep : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_em inst ly S W regs mem md p n tr r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ memnorm_keep segs mem mem'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & _ & _ & HK & _).
exists regs', mem', md'. exact (conj Hc HK).
Qed.

Lemma dealloc_leaf_em_keep : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_em inst ly S W regs mem md p n tr r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ memnorm_keep segs mem mem'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & _ & _ & HK & _).
exists regs', mem', md'. exact (conj Hc HK).
Qed.
End dl.
End a.
