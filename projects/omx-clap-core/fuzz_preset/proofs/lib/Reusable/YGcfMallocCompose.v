(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: the trace premise in the P'' form, `admits (as_universe B) tr S` (YG01.v), replacing the In-form. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.TkSecLink), 2026-10-30: batch_room_cf added to rpreD_free_cf and to its realloc old-block free twin (YGcfReallocCompose.v RDF2); nmax_cf_ok's comment updated (c5's walk covers n < SEC_NMAX since 84ee52cd012). *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfMallocCompose.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfMallocCompose.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Modified by Theorem Labs, 2026-10-30: field round 3 part 3 (MP) from proofs/cgif/cgif_file_fuzzer/lib/YGcfMallocCompose.v applied by 3-way (base commit 5034424e29db, theirs e8a7dd66acf2; preset-side hunks kept), module paths changed. *)
(* Theorem Labs, 2026-10: fuzz_preset's event-free allocator instance (suffix cf): the IMAGE-FREE bridge from a Theorem Labs lane's
   frame-generic Allocate / Deallocate contracts (AllocG.v, DeallocG.v: c5's by-path copies) and an interceptor-walk
   record to the API leaves amalloc_realizes_cf / afree_realizes_cf (YG0dcf.v:159-166 / :188-196).
   Template: a Theorem Labs lane's RGtop.v (seg_npre :340-352, seg_npost :356-373, rg_realloc_null :513-560): the interceptor's
   instructions are two segments, the call segment (the wrapper's entry -> Allocate's / Deallocate's entry) and the
   return segment (Allocate's / Deallocate's return -> the wrapper's return), joined by a consumer-chosen invariant K;
   both are fields of a Record (wrap_malloc_walk_cf / wrap_free_walk_cf), discharged per image by its walk.
   The instance values: U := admits (as_universe B) (the P'' trace premise, YG01.v:158; a Theorem Labs lane 22:05Z); mt := malloc_cf; ft := free_cf;
   lmax := LIVE_MAX; lpost := qtight; oomb := as_oom_byte B; pcA := cf_pc_allocate, pcD := cf_pc_deallocate (CfImg);
   Allocate: rpre := YGcfRmodel.rpre_cfr B, AOX := aowned \/ xs_cf (YGcfRmodel.v:97), nmax a parameter with the named
   premise nmax_cf_ok (cf_malloc_max <= nmax: amalloc_realizes_cf's range, YG0dcf.v:162);
   Deallocate: rpre := rpre_dealloc_cf's body (YGcfDIface.v), AOX := aowned (free_leaf_cf's exception set has no
   errbuf extent), fpre := the freed base is not hidden (~ In (sptr_addr B ly p) Hp, afree_realizes_cf's premise).
   ARX is a parameter indexed by the caller's ghost set Hp (the leaves keep Hp, YG0dcf.v:9), with the projection
   to ARcf at that Hp (ARX_ARcf) and, for malloc, to xs_placed_cf (ARX_xs); the call-site arguments (al, atp, acf;
   atpD) are parameters.
   The free interceptor initializes the internal allocator before Deallocate's entry, on every free (a Theorem Labs lane, 2026-10-29
   13:08Z: ___interceptor_free calls internal_allocator() before its jal to asan_free), so wf_call reaches
   Deallocate's entry at finit_cf S, the state with the flag set; free_cf p tr S is the same tree as
   free_cf p tr (finit_cf S) (free_cf_finit: free_cf sets the flag first, YG00cf.v:330), so Deallocate's run from
   finit_cf S realizes the caller's tree and Deallocate's premise holds there (rpreD_free_cf_of_pre).
   The keep facts a Theorem Labs lane's statements do not carry yet (errno kept: alloc_post_e / dealloc_post_raw_e; memnorm kept)
   are in the named premises aalloc_realizes_cf_em / adealloc_realizes_raw_cf_em, whose first conjunct is AllocG's /
   DeallocG's leaf verbatim (aalloc_realizes_cf_em_allocg / adealloc_realizes_raw_cf_em_deallocg).
   No image constant; no function is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
(* val_mem (AllocG's out-of-memory byte clause) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AllocG DeallocG RGtop YGcfRmodel YG03cf YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs.
(* apost (YG0k), amreal_apost (YFfk) and malloc_cf's path post (YGcfApath): the new block of a granted
   malloc_cf path is live in the result state, which the window widening needs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0k YFfk YGcfApath.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YG0dcf.v. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section J.
Variable segs : list Segment.
Variable B : asyms.

(* ---------------------------------------------------------------------------- *)
(* 0. Shared names.                                                             *)

(* An allocator relation at the caller's ghost set Hp (AllocG's / DeallocG's ARX once Hp is fixed). *)
Definition ARXh_t : Type :=
list Z -> Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.

(* ARX gives ARcf at the SAME ghost set (the leaves' first conjunct, YG0dcf.v:77). *)
Definition ARX_ARcf (ARX : ARXh_t) : Prop :=
forall Hp inst ly S W mem md, ARX Hp inst ly S W mem md -> ARcf segs B ly S Hp W mem md.

(* ARX gives the errbuf slot's placement (malloc_leaf_cf's xs_placed_cf conjunct, YG0dcf.v:116). *)
Definition ARX_xs (ARX : ARXh_t) : Prop :=
forall Hp inst ly S W mem md, ARX Hp inst ly S W mem md -> xs_placed_cf ly S.

(* ARX gives the errbuf extent mapped (acall_post_cf's last conjunct, xs_mapped_cf, YGcfXs.v): preset A5-r6's name. *)
Definition ARX_xsm (ARX : ARXh_t) : Prop :=
forall Hp inst ly S W mem md, ARX Hp inst ly S W mem md -> xs_mapped_cf ly S md.

(* errno's four bytes, raw (the leaves' ERRNO text, YG0dcf.v:119 / :180). *)
Definition errno_kept_cf (mem mem' : word -> option byte) : Prop :=
forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i)).

(* A property of the memory of a configuration. *)
Definition at_mem_cf (c : config) (P : (word -> option byte) -> Prop) : Prop :=
forall pc regs mem md, c = cfg_at segs pc regs mem md -> P mem.

(* What a call segment keeps: outside the caller's owned set at the entry state and the caller's stack window and
   errno (ascratch B ASTACK regs), the view and the raw bytes (part 3c: no memnorm keep). *)
Definition ikeep_cf (ly : alayout) (S : astate) (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte)
(W' : world segs) (mem' : word -> option byte) : Prop :=
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B ASTACK regs a ->
 aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ ascratch B ASTACK regs (bv_unsigned x) -> mem' x = mem x).

(* ---------------------------------------------------------------------------- *)
(* 1. malloc.                                                                   *)
Section M.
(* Allocate's size bound, and its call-site arguments a2 (alignment), a4 (alloc_type), a5 (can_fill). *)
Variables (nmax al atp acf : Z).

(* The named premise on Allocate's size bound: it covers amalloc_realizes_cf's range (YG0dcf.v:162). c5's walk covers
   n < SEC_NMAX = 2 ^ 30 - 16384 (AGi9.SEC_NMAX, since 84ee52cd012), so a unit discharges this premise by arithmetic. *)
Definition nmax_cf_ok : Prop := cf_malloc_max <= nmax.

Definition mtr_cf (ly : alayout) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
call_trace ly (pc_malloc_ra0 (as_code B)) regs ch.

(* amalloc_realizes_cf's premises (YG0dcf.v:160-163). *)
Definition mentry_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (ch : list (Z * Z * Z)) : Prop :=
acall_pre_cf segs B ly S Hp W regs mem md ch /\
getr regs 10 = w64 n /\ 0 <= n < cf_malloc_max /\ blocks_bytes S + n <= LIVE_MAX /\
admits (as_universe B) (mtr_cf ly regs ch) S.

(* Allocate's owned set at the instance (rmodel_ok_cf_wf's, YGcfRmodel.v:97). *)
Definition AOXm_cf (ly : alayout) (S : astate) (a : Z) : Prop := aowned B ly S a \/ Exists (in_zr a) (xs_cf ly S).

(* AllocG's pre / post / leaf at the cf instance, at the ghost set Hp. *)
Definition malloc_apre_cf (ARX : ARXh_t) (Hp : list Z) (inst so bp : Z) (ly : alayout) (S : astate) (W : world segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z) : Prop :=
AllocG.alloc_pre segs B (admits (as_universe B)) (ARX Hp) (YGcfRmodel.rpre_cfr B) nmax LIVE_MAX
al atp acf inst so bp ly S W regs mem md n tr.

Definition malloc_apost_cf (ARX : ARXh_t) (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
AllocG.alloc_post segs B (ARX Hp) AOXm_cf inst ly S W regs mem md E ly' S' W' regs' mem' md'.

Definition malloc_aleaf_cf (ARX : ARXh_t) (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
AllocG.alloc_leaf segs B malloc_cf (ARX Hp) AOXm_cf qtight (as_oom_byte B) inst ly S W regs mem md n tr r W' c'.

(* Allocate's result: AllocG.aalloc_realizes at the instance (every Hp), its leaf strengthened by the two keeps
   AllocG does not state: errno's bytes on a block (a Theorem Labs lane's coming alloc_post_e) and the overlay normal form.  Field
   round 3 part 3b (a Theorem Labs lane 2026-10-30 18:50Z, option B, as Deallocate's in part 3): the memory predicate MP at
   Allocate's entry memory is the cf conjunction, so the premise is here; the composition below supplies it from
   acall_pre_cf through the wrapper's frames. *)
Definition aalloc_realizes_cf_em (ARX : ARXh_t) : Prop :=
forall Hp inst so bp ly S W regs mem md n tr,
malloc_apre_cf ARX Hp inst so bp ly S W regs mem md n tr ->
arodata_ok_cf segs B mem ->
amreal segs (malloc_cf n tr S) W (cfg_at segs cf_pc_allocate regs mem md)
(fun r W' c' => malloc_aleaf_cf ARX Hp inst ly S W regs mem md n tr r W' c' /\
 at_mem_cf c' (fun mem' => (fst r <> PNull -> errno_kept_cf mem mem') /\
   (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'))).

(* Its first conjunct is AllocG's leaf at the instance, under arodata_ok_cf at Allocate's entry memory (AllocG's
   own aalloc_realizes takes no memory premise, so since part 3b this is its form with the premise). *)
Lemma aalloc_realizes_cf_em_allocg : forall ARX, aalloc_realizes_cf_em ARX -> forall Hp inst so bp ly S W regs mem md n tr,
malloc_apre_cf ARX Hp inst so bp ly S W regs mem md n tr ->
arodata_ok_cf segs B mem ->
amreal segs (malloc_cf n tr S) W (cfg_at segs cf_pc_allocate regs mem md)
  (AllocG.alloc_leaf segs B malloc_cf (ARX Hp) AOXm_cf qtight (as_oom_byte B) inst ly S W regs mem md n tr).
Proof.
intros ARX H Hp inst so bp ly S W regs mem md n tr PRE HRO.
eapply amreal_mono; [|exact (H Hp inst so bp ly S W regs mem md n tr PRE HRO)].
intros r W' c' [L _]. exact L.
Qed.

(* The invariant from the call segment to the return segment: the caller's entry
   (ly S Hp W regs mem md n ch), then the state at `jal Allocate` (W1 regsA memA mdA). *)
Definition Kmalloc_t : Type :=
alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Z -> list (Z * Z * Z) ->
world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

Record wrap_malloc_walk_cf (ARX : ARXh_t) (K : Kmalloc_t) : Prop := {
(* M1. __wrap_malloc's entry -> Allocate's entry (the wrapper, the trace unwind, asan_malloc up to its call).
   No model step: the state is the caller's S. At the call: AllocG's pre at Hp, the stack window inside the
   caller's, the keeps across the interceptor's own instructions, and K. *)
wm_call : forall ly S Hp W regs mem md n ch,
  mentry_cf ly S Hp W regs mem md n ch -> YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
  SRr segs W (cfg_at segs (pc_wrap_malloc (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at segs cf_pc_allocate regsA memA mdA /\
    malloc_apre_cf ARX Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf ly regs ch) /\
    same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    ikeep_cf ly S regs W mem W1 memA /\ errno_kept_cf mem memA /\
    K ly S Hp W regs mem md n ch W1 regsA memA mdA);
(* M2. Allocate's return (raZ regsA) with q -> __wrap_malloc's return (raZ regs): a0 passed through, ARX
   re-established at the return memory, the wrapper's NULL-path writes (errno := ENOMEM; the out-of-memory byte
   Allocate set, read on the view), the stack window present, and the keeps. *)
wm_ret : forall ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  mentry_cf ly S Hp W regs mem md n ch ->
  K ly S Hp W regs mem md n ch W1 regsA memA mdA ->
  malloc_apre_cf ARX Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf ly regs ch) ->
  malloc_apost_cf ARX Hp inst ly S W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> qtight S2 ->
  (exists trc, apath (malloc_cf n (mtr_cf ly regs ch) S) trc (q, S2) /\ gflag trc = true) ->
  (q = PNull -> val_mem segs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1) ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (q <> PNull -> errno_kept_cf mem2 mem') /\
    (q = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1))
}.

(* Allocate's state premise from the call's: universe_ok and Wf_cf from ARcf, ROOM_cf from acall_pre_cf's three room
   conjuncts (YG0dcf.v:60, :63, :71), and the hull admission from its cf_hull_ok conjunct (the same state). *)
Lemma rpre_cfr_of_pre : forall ly S Hp W regs mem md ch n,
acall_pre_cf segs B ly S Hp W regs mem md ch -> YGcfRmodel.rpre_cfr B S n.
Proof.
intros ly S Hp W regs mem md ch n (AR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SL & ER & _ & BR & HO & _).
destruct AR as (M & _).
split; [exact (amc_universe _ _ _ _ _ M)|]. split; [exact (amc_wf _ _ _ _ _ M)|].
exact (conj (conj SL (conj ER BR)) HO).
Qed.

Theorem amalloc_realizes_cf_of_parts : forall (ARX : ARXh_t) (K : Kmalloc_t),
nmax_cf_ok -> ARX_ARcf ARX -> ARX_xs ARX ->
(* the unit's two image rows behind arodata_ok_cf's keep, as afree_realizes_cf_of_parts (field round 3 part 3b) *)
relro_seg_t segs -> errno_relro_t B ->
aalloc_realizes_cf_em ARX ->
wrap_malloc_walk_cf ARX K ->
amalloc_realizes_cf segs B.
Proof.
intros ARX K HNM HAR HXS RS ER0 HAL [WCALL WRET].
intros ly S Hp W regs mem md n ch PRE Hn Hrange Hlive Htr.
assert (ENT : mentry_cf ly S Hp W regs mem md n ch) by exact (conj PRE (conj Hn (conj Hrange (conj Hlive Htr)))).
assert (HN : 0 <= n < nmax) by (unfold nmax_cf_ok in HNM; lia).
eapply amreal_SRr_pre; [exact (WCALL ly S Hp W regs mem md n ch ENT (rpre_cfr_of_pre ly S Hp W regs mem md ch n PRE) HN)|].
intros W1 c1 WLE1 (inst & so & bp & regsA & memA & mdA & -> & APRE & IO1 & RIN & KP1 & ER1 & KK).
(* MP at Allocate's entry memory memA (part 3b / 3c): acall_pre_cf's arodata_ok_cf at mem, through the wrapper
   segment's raw frame (ikeep_cf's second conjunct), which misses every non-owned covered byte; the same steps as
   afree_realizes_cf_of_parts at Deallocate's entry, with the caller's S (no init step). *)
pose proof PRE as PREc.
destruct PREc as (ACALL & _ & _ & HSTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO).
assert (ROa : arodata_ok_cf segs B memA).
{ apply (arodata_keep_cf segs B ly S Hp W mem md ly S Hp W1 memA mdA
    (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) ACALL
    (HAR Hp inst ly S W1 memA mdA (proj1 APRE)) RS).
  - intros a Ha NO R I I' NA NA' NX NX' [X|X].
    + exact (NA X).
    + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 ACALL)) HSTK ER0 Ha R X).
  - intros x NX. apply (proj2 KP1); intros Y; apply NX; tauto.
  - exact HRO. }
eapply RGtop.rg_then_SRr; [exact (HAL Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf ly regs ch) APRE ROa)|].
intros [q S2] W2 c2 [LEAF KEEP].
unfold malloc_aleaf_cf, AllocG.alloc_leaf in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & PATH & OOM).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERA _].
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
eapply SRr_mono; [exact (WRET ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
  ENT KK APRE APO A02 LP2 PATH OOM)|].
intros W' c' WLE3 (regs' & mem' & md' & -> & CS' & A0' & ARX' & IO' & [KV KR] & WN' & ER' & NUL').
unfold malloc_leaf_cf. exists ly2, regs', mem', md'. cbn [fst snd].
(* the exception sets: Allocate's owned set and window lie inside the leaf's *)
assert (XO : forall a, ~ aowned B ly S a -> ~ aowned B ly2 S2 a ->
  ~ ((q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) \/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly2 S2)) ->
  ~ AOXm_cf ly S a /\ ~ AOXm_cf ly2 S2 a /\ ~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)).
{ intros a NA NA2 NE. split; [|split].
  - intros [X|X]; [exact (NA X)|]. apply NE. right. apply Exists_app. left. exact X.
  - intros [X|X]; [exact (NA2 X)|]. apply NE. right. apply Exists_app. right. exact X.
  - intros X. apply NE. left. exact X. }
assert (XS : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B AllocG.AFSTACK_G regsA a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsA AllocG.AFSTACK_G a (proj1 RIN) (proj2 RIN) X))).
split; [reflexivity|].
split.
{ unfold acall_post_cf.
  split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE2|].
  split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
  split; [exact CS'|].
  split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
  split; [|exact WN'].
  intros a Ha NA NA2 NS NE. destruct (XO a NA NA2 NE) as (X1 & X2 & X3).
  rewrite (KV a Ha NS), (FR2 a Ha X1 X2 (XS a NS) X3). exact (proj1 KP1 a Ha NA NS). }
split; [exact A0'|]. split; [exact LP2|]. split; [exact NUL'|].
split; [exact (HXS _ _ _ _ _ _ _ ARX2)|].
split.
{ intros Hq i Hi. rewrite (ER' Hq i Hi), (ERA Hq i Hi). exact (ER1 i Hi). }
intros x NA NA2 NS NE. destruct (XO _ NA NA2 NE) as (X1 & X2 & X3).
rewrite (KR x NS), (FR2w x X1 X2 (XS _ NS) X3). exact (proj2 KP1 x NA NS).
Qed.
End M.

(* ---------------------------------------------------------------------------- *)
(* The wrapper contract DERIVED from the body contract (Main, 2026-10-30; the shape of
   fuzz_command's RtDMallocTramp.cmd_amalloc_of_body, commit 8aaeb29ab7b2).
   Two premises the UNIT discharges at its image, both strictly weaker than
   wrap_malloc_walk_cf's wm_call:
   - wrap_to_body_step_cf: the trampoline is one forward jump to the body (cgif 0x52960
     `j 0x52b34`, measured on cgif_file_fuzzer.asan-ubsan), so no register, no byte and no
     model change;
   - malloc_leaf_widen_cf: the body's leaf at the window MALLOC_IN_STK_CF gives the leaf at
     ASTACK. The two windows differ by ASTACK - MALLOC_IN_STK_CF = 2,176 stack bytes, which
     stay present because they lie outside the body's scratch window and the model's post puts
     the new block below the stack (fuzz_command's RtDMallocLeaf.dm_leaf_widen). *)
(* The post is the kit's step rule's (YA0n.v SRr_step): after the jump the model is any
   md' = with_vm_backing (m_vm_lazy md) mat md, a model that differs from md only in its
   materialized set (YK04.v same_but_materialized; A1 a Theorem Labs lane, 2026-10-30). *)
Definition wrap_to_body_step_cf : Prop :=
forall ly S Hp W regs mem md ch,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
SRr segs W (cfg_at segs (pc_wrap_malloc (as_code B)) regs mem md)
(fun W' c' => W' = W /\ exists mat, c' = cfg_at segs (pc_malloc (as_code B)) regs mem (with_vm_backing (m_vm_lazy md) mat md)).

Definition malloc_leaf_widen_cf : Prop :=
forall ly S Hp W regs mem md n ch r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch ->
(* the new block is live in the result state (A1 a Theorem Labs lane, 2026-10-30: without it a gap byte of
   [sp - ASTACK, sp - MALLOC_IN_STK_CF) has no route to presence, because the view frame needs the byte
   outside the new block; the caller supplies it from malloc_cf's path post) *)
(fst r <> PNull -> In (fst r, n) (blocks (snd r))) ->
malloc_leaf_cf_w segs B MALLOC_IN_STK_CF ly S Hp W regs mem md n r W' c' ->
malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c'.

(* The cf relation does not read the materialized set (ARcf's model fields are the maps, the lazy
   set and eager_used, YG0ncf.v / YG0n.v amwf), so it survives the step's change of model, and the
   body's leaf at the step's model is the wrapper's leaf at the call's model: the leaf reads its
   pre model only in same_io, which the materialized set does not touch. *)
Lemma ARcf_wvb_cf : forall ly S Hp W mem md mat,
ARcf segs B ly S Hp W mem md -> ARcf segs B ly S Hp W mem (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S Hp W mem md mat (M & L & BU & WF & HS).
destruct md as [fd [maps lazy mat0] io fs proc lim tm].
split; [exact M|]. split; [destruct L; constructor; assumption|].
split; [exact BU|]. split; [exact WF | exact HS].
Qed.

Lemma acall_pre_cf_w_wvb_cf : forall stk ly S Hp W regs mem md mat ch,
acall_pre_cf_w segs B stk ly S Hp W regs mem md ch ->
acall_pre_cf_w segs B stk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) mat md) ch.
Proof.
intros stk ly S Hp W regs mem md mat ch (HAR & REST).
split; [exact (ARcf_wvb_cf ly S Hp W mem md mat HAR) | exact REST].
Qed.

Lemma malloc_leaf_cf_w_wvb_cf : forall stk ly S Hp W regs mem md mat n r W' c',
malloc_leaf_cf_w segs B stk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) mat md) n r W' c' ->
malloc_leaf_cf_w segs B stk ly S Hp W regs mem md n r W' c'.
Proof.
intros stk ly S Hp W regs mem md mat n r W' c' (ly' & regs' & mem' & md'' & HC & (HA & HL & HW & HR & HIO & HV & HP) & REST).
exists ly', regs', mem', md''. split; [exact HC|]. split; [|exact REST].
split; [exact HA|]. split; [exact HL|]. split; [exact HW|]. split; [exact HR|].
split; [destruct md as [fd [maps lazy mat0] io fs proc lim tm]; exact HIO|].
split; [exact HV | exact HP].
Qed.

Theorem amalloc_realizes_cf_of_body :
wrap_to_body_step_cf -> malloc_leaf_widen_cf ->
amalloc_body_realizes_cf segs B (pc_malloc_ra0 (as_code B)) -> amalloc_realizes_cf segs B.
Proof.
intros STEP WIDEN BODY ly S Hp W regs mem md n ch PRE Hn Hrange Hlive Htr.
eapply amreal_SRr_pre; [exact (STEP ly S Hp W regs mem md ch PRE)|].
intros W1 c1 _ (-> & mat & ->).
pose proof PRE as (HAR & Hret & Hal & Hslo & Hbot & Hshi & Hpres & Hgp & Htp & Hch & Hqm & HSL & HER & HBU & HBR & HHO & HAD).
assert (PREW : acall_pre_cf_w segs B MALLOC_IN_STK_CF ly S Hp W regs mem md ch).
{ split; [exact HAR|]. split; [exact Hret|]. split; [exact Hal|].
  split; [unfold MALLOC_IN_STK_CF, ASTACK in *; lia|].
  split; [unfold MALLOC_BODY_FRAME_CF in *; lia|].
  split; [exact Hshi|].
  split; [intros a Ha; apply Hpres; unfold MALLOC_IN_STK_CF, ASTACK in *; lia|].
  split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch|]. split; [exact Hqm|].
  split; [exact HSL|]. split; [exact HER|]. split; [exact HBU|]. split; [exact HBR|]. split; [exact HHO|].
  exact HAD. }
destruct HAR as (M & _).
assert (BLK : apost (malloc_cf n (call_trace ly (pc_malloc_ra0 (as_code B)) regs ch) S)
  (fun r => fst r <> PNull -> In (fst r, n) (blocks (snd r)))).
{ intros trc [p s'] Hpath Hnn. cbn [fst snd] in *.
  pose proof (malloc_cf_apath_success (as_universe B) S n _ trc p s'
    (amc_universe _ _ _ _ _ M) (amc_wf _ _ _ _ _ M) Hrange Hlive Htr HSL HER HBR Hpath Hnn)
    as (_ & _ & _ & _ & EB & _). rewrite EB. apply in_or_app. right. left. reflexivity. }
eapply amreal_mono;
[| eapply (amreal_apost); [exact BLK |
   exact (BODY ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) mat md) n ch
            (acall_pre_cf_w_wvb_cf _ ly S Hp W regs mem md mat ch PREW) Hn Hrange Hlive Htr)]].
intros r W' c' (HB & HL).
exact (WIDEN ly S Hp W regs mem md n ch r W' c' PRE HB (malloc_leaf_cf_w_wvb_cf _ ly S Hp W regs mem md mat n r W' c' HL)).
Qed.


(* ---------------------------------------------------------------------------- *)
(* 2. free.                                                                     *)
Section F.
(* The free site's alloc_type argument (Deallocate's a5). *)
Variable atpD : Z.

Definition ftr_cf (ly : alayout) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
call_trace ly (pc_free_ra0 (as_code B)) regs ch.

(* afree_realizes_cf's premises (YG0dcf.v:189-193). *)
Definition fentry_cf (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (ch : list (Z * Z * Z)) : Prop :=
acall_pre_cf segs B ly S Hp W regs mem md ch /\
(p = PNull \/ In (p, n) (blocks S)) /\ getr regs 10 = w64 (sptr_addr B ly p) /\
~ In (sptr_addr B ly p) Hp /\
admits (as_universe B) (ftr_cf ly regs ch) S.

(* The state at Deallocate's entry: the free interceptor has initialized the internal allocator. *)
Definition finit_cf (S : astate) : astate := set_internal_inited true S.

(* free_cf sets the flag before anything else (YG00cf.v:328-330), so starting it from finit_cf S is the same tree. *)
Lemma free_cf_finit : forall p tr S, free_cf p tr S = free_cf p tr (finit_cf S).
Proof.
intros p tr [rg ci0 ca chk sc sa sr qt qg fs dp ii nv]. destruct ii; reflexivity.
Qed.

(* finit_cf changes only the internal-allocator flag, so qtight and the budget (YG0ncf.mroom_cf_frame) do not move. *)
Lemma qmeter_cf_finit : forall S, qmeter_cf S -> qmeter_cf (finit_cf S).
Proof.
intros S [QT MR]. split; [exact QT|]. exact (mroom_cf_frame S (finit_cf S) eq_refl eq_refl eq_refl eq_refl MR).
Qed.

(* Deallocate's premise at the instance: YGcfDIface.rpre_dealloc_cf's body, plus the batch class's room: free_cf's
   Enqueue may allocate a new batch from class kBatchClass, whose populate maps one kUserMapSize (YG03cf.v:435-441),
   and that room is a pre fact of the call (acall_pre_cf's batch_room_cf conjunct), not an invariant of the relation;
   and the driver's hull admission at the call (acall_pre_cf's last conjunct, Main 2026-10-30). *)
Definition rpreD_free_cf (S : astate) (n : Z) : Prop :=
YGcfRmodel.rpreD_cfr B S n /\ qmeter_cf S /\ st_internal_inited S = true /\ batch_room_cf S /\ cf_hull_ok S.

(* It holds at Deallocate's entry state: Wf_cf is kept by the flag (YG03cf.WfP_cf_set_internal_inited_cf), qmeter_cf
   does not read it, and the admission reads only the meters, which finit_cf keeps (CfParams.cf_hull_counts). *)
Lemma rpreD_free_cf_of_pre : forall ly S Hp W regs mem md ch n,
acall_pre_cf segs B ly S Hp W regs mem md ch -> rpreD_free_cf (finit_cf S) n.
Proof.
intros ly S Hp W regs mem md ch n (AR & _ & _ & _ & _ & _ & _ & _ & _ & _ & QM & _ & _ & _ & BR & HO & _).
destruct AR as (M & _).
split; [split; [exact (amc_universe _ _ _ _ _ M) | exact (YG03cf.WfP_cf_set_internal_inited_cf _ 0 0 0 S true (amc_wf _ _ _ _ _ M))]|].
split; [exact (qmeter_cf_finit S QM) | split; [reflexivity | split; [exact BR|]]].
exact (cf_hull_counts (finit_cf S) S eq_refl eq_refl HO).
Qed.

(* The free site's premise at the ghost set: the freed base is not hidden (afree_realizes_cf's premise; without it
   ARcf at Hp after the free fails amc_hp_live). *)
Definition fpre_hp_cf (Hp : list Z) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(p : sptr) (n : Z) : Prop :=
~ In (sptr_addr B ly p) Hp.

(* DeallocG's pre / raw post / raw leaf at the cf instance, at the ghost set Hp; AOX := aowned. *)
Definition free_dpre_cf (ARX : ARXh_t) (Hp : list Z) (inst so bp : Z) (ly : alayout) (S : astate) (W : world segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z) : Prop :=
DeallocG.dealloc_pre segs B (admits (as_universe B)) (ARX Hp) rpreD_free_cf (fpre_hp_cf Hp) atpD
inst so bp ly S W regs mem md p n tr.

Definition free_dpost_cf (ARX : ARXh_t) (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
DeallocG.dealloc_post_raw segs B (ARX Hp) (aowned B) inst ly S W regs mem md E ly' S' W' regs' mem' md'.

Definition free_dleaf_cf (ARX : ARXh_t) (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
DeallocG.dealloc_leaf_raw segs B free_cf (ARX Hp) (aowned B) qtight inst ly S W regs mem md p n tr r W' c'.

(* Deallocate's result: DeallocG.adealloc_realizes_raw at the instance (every Hp), its leaf strengthened by errno's
   bytes (a Theorem Labs lane's coming dealloc_post_raw_e) and the overlay normal form.  Field round 3 part 3 (Main 2026-10-30,
   option B): the walk's memory predicate MP at Deallocate's entry memory is the cf conjunction, so the premise is
   here; the composition below supplies it from acall_pre_cf through the wrapper's frames. *)
Definition adealloc_realizes_raw_cf_em (ARX : ARXh_t) : Prop :=
forall Hp inst so bp ly S W regs mem md p n tr,
free_dpre_cf ARX Hp inst so bp ly S W regs mem md p n tr ->
arodata_ok_cf segs B mem ->
amreal segs (free_cf p tr S) W (cfg_at segs cf_pc_deallocate regs mem md)
(fun r W' c' => free_dleaf_cf ARX Hp inst ly S W regs mem md p n tr r W' c' /\
 at_mem_cf c' (fun mem' => errno_kept_cf mem mem' /\ (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'))).

(* Its first conjunct is DeallocG's raw statement at the instance, at MP := arodata_ok_cf (part 3c). *)
Lemma adealloc_realizes_raw_cf_em_deallocg : forall ARX, adealloc_realizes_raw_cf_em ARX -> forall Hp,
DeallocG.adealloc_realizes_raw segs B (admits (as_universe B)) free_cf (ARX Hp) (aowned B) rpreD_free_cf
qtight (fpre_hp_cf Hp) cf_pc_deallocate atpD (fun m => arodata_ok_cf segs B m).
Proof.
intros ARX H Hp inst so bp ly S W regs mem md p n tr PRE HRO.
eapply amreal_mono; [|exact (H Hp inst so bp ly S W regs mem md p n tr PRE HRO)].
intros r W' c' [L _]. exact L.
Qed.

(* The invariant from the call segment to the return segment: the caller's entry
   (ly S Hp W regs mem md p n ch), then the state at Deallocate's entry (W1 regsD memD mdD). *)
Definition Kfree_t : Type :=
alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> sptr -> Z ->
list (Z * Z * Z) -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

Record wrap_free_walk_cf (ARX : ARXh_t) (K : Kfree_t) : Prop := {
(* F1. __wrap_free's entry -> Deallocate's entry (the wrapper, its internal-allocator init, the trace unwind,
   asan_free up to its tail jump). On every free, PNull included, the interceptor initializes the internal allocator
   before Deallocate's entry, which realizes free_cf's init step: Deallocate's pre is at finit_cf S. *)
wf_call : forall ly S Hp W regs mem md p n ch,
  fentry_cf ly S Hp W regs mem md p n ch -> rpreD_free_cf (finit_cf S) n ->
  SRr segs W (cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsD memD mdD,
    c1 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    free_dpre_cf ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf ly regs ch) /\
    same_io md mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    ikeep_cf ly S regs W mem W1 memD /\ errno_kept_cf mem memD /\
    K ly S Hp W regs mem md p n ch W1 regsD memD mdD);
(* F2. Deallocate's return (raZ regsD) -> __wrap_free's return (raZ regs). *)
wf_ret : forall ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2,
  fentry_cf ly S Hp W regs mem md p n ch ->
  K ly S Hp W regs mem md p n ch W1 regsD memD mdD ->
  free_dpre_cf ARX Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf ly regs ch) ->
  free_dpost_cf ARX Hp inst ly (finit_cf S) W1 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  qtight S2 ->
  (exists trc, apath (free_cf p (ftr_cf ly regs ch) (finit_cf S)) trc (tt, S2) /\ gflag trc = true) ->
  SRr segs W2 (cfg_at segs (raZ regsD) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    errno_kept_cf mem2 mem')
}.

Theorem afree_realizes_cf_of_parts : forall (ARX : ARXh_t) (K : Kfree_t),
ARX_ARcf ARX ->
(* the unit's two image rows behind arodata_ok_cf's keep (YG0ncf.v:611 / :613; cgif: YGcfImgcgif.relro_seg_cgif /
   errno_relro_cgif) *)
relro_seg_t segs -> errno_relro_t B ->
adealloc_realizes_raw_cf_em ARX ->
wrap_free_walk_cf ARX K ->
afree_realizes_cf segs B.
Proof.
intros ARX K HAR RS ER0 HDL [WCALL WRET].
intros ly S Hp W regs mem md p n ch PRE Hpn H10 NIN Htr.
assert (ENT : fentry_cf ly S Hp W regs mem md p n ch) by exact (conj PRE (conj Hpn (conj H10 (conj NIN Htr)))).
rewrite (free_cf_finit p _ S).
eapply amreal_SRr_pre; [exact (WCALL ly S Hp W regs mem md p n ch ENT (rpreD_free_cf_of_pre ly S Hp W regs mem md ch n PRE))|].
intros W1 c1 WLE1 (inst & so & bp & regsD & memD & mdD & -> & DPRE & IO1 & RIN & KP1 & ER1 & KK).
(* MP at Deallocate's entry memory memD: acall_pre_cf's arodata_ok_cf at mem, through the wrapper segment's raw frame
   (ikeep_cf's second conjunct), which misses every non-owned covered byte. *)
pose proof PRE as PREc.
destruct PREc as (ACALL & _ & _ & HSTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO).
assert (ROd : arodata_ok_cf segs B memD).
{ apply (arodata_keep_cf segs B ly S Hp W mem md ly (finit_cf S) Hp W1 memD mdD
    (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) ACALL
    (HAR Hp inst ly (finit_cf S) W1 memD mdD (proj1 DPRE)) RS).
  - intros a Ha NO R I I' NA NA' NX NX' [X|X].
    + exact (NA X).
    + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 ACALL)) HSTK ER0 Ha R X).
  - intros x NX. apply (proj2 KP1); intros Y; apply NX; tauto.
  - exact HRO. }
eapply RGtop.rg_then_SRr; [exact (HDL Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf ly regs ch) DPRE ROd)|].
intros [[] S2] W2 c2 [LEAF KEEP].
unfold free_dleaf_cf, DeallocG.dealloc_leaf_raw in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & DPO & LP2 & PATH).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERD _].
pose proof DPO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
eapply SRr_mono; [exact (WRET ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2
  ENT KK DPRE DPO LP2 PATH)|].
intros W' c' WLE3 (regs' & mem' & md' & -> & CS' & ARX' & IO' & [KV KR] & WN' & ER').
unfold free_leaf_cf. exists ly2, regs', mem', md'. cbn [snd].
assert (XS : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B DeallocG.DFSTACK_G regsD a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsD DeallocG.DFSTACK_G a (proj1 RIN) (proj2 RIN) X))).
split; [reflexivity|].
split.
{ unfold acall_post_cf.
  split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE2|].
  split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
  split; [exact CS'|].
  split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
  split; [|exact WN'].
  intros a Ha NA NA2 NS NE.
  rewrite (KV a Ha NS), (FR2 a Ha NA NA2 (XS a NS) NE). exact (proj1 KP1 a Ha NA NS). }
split; [exact LP2|].
split.
{ intros i Hi. rewrite (ER' i Hi), (ERD i Hi). exact (ER1 i Hi). }
intros x NA NA2 NS NE. rewrite (KR x NS), (FR2w x NA NA2 (XS _ NS) NE). exact (proj2 KP1 x NA NS).
Qed.
End F.

End J.
End G.
