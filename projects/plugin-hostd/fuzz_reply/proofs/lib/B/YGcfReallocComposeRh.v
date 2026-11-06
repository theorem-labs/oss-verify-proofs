(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfReallocCompose.v, with its module paths changed; 125 of its 531 lines of code are new or changed and 416 lines of the source are left out. *)
(* CARRIED from commit 08d2b9719e4ba2b74ff3b229a5b7680906920eba,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfReallocComposeRh.v, sha256 199e1971319f541547358f3d17564a200bf507e3ed090a68181bd50b48dcc86e (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree name lib/B; a sentence is split at a directory change, the module order kept.
*)
(* The PRIMED realloc(p, n) composition under the re-hide (a Theorem Labs lane R, plan row R-1; one text for cgif, reply and
   preset).  realloc(p, n) frees the old block inside the call, and a secondary free may re-hide shadow
   (YGcfRehidePost), so its contract is YG0dcfR.arealloc_realizes_cf_rh: the run amreal' over RZ_cf and the leaf
   YG0dcfR.realloc_leaf_cf_rh (world grows only inside dead_shadow_new, view frame except it).  realloc(NULL, n)
   frees nothing and keeps its unprimed composition in YGcfReallocCompose.v.
   - free_dpost_cf_rh: Deallocate's primed raw post at the cf instance (YGcfRehidePost.dealloc_post_raw_rh, the
     twin of YGcfMallocCompose.free_dpost_cf).
   - wrap_realloc_walk_cf_rh: YGcfReallocCompose.wrap_realloc_walk_cf with its S3 field over the primed post;
     wrap_realloc_walk_cf_rh_of builds it from the released record and a primed S3.
   - arealloc_realizes_cf_rp_h_rh RP: YG0dcfR.arealloc_realizes_cf_rh's body with an entry predicate RP after
     acall_pre_cf and the caller's hull admission at every post, right after admits; arealloc_realizes_cf_rp_h_rh_to
     gives YG0dcfR.arealloc_realizes_cf_rh at RP := True.  RP is the room the caller holds (True with the relation's
     batch room, or the room form ROOM_cf_k S RK_realloc of the primed YGcfInstReallocK.arealloc_realizes_cf_k), so the
     primed proof exists once.
   - arealloc_realizes_cf_rp_rh_of_parts: the composition, from Allocate's memnorm-kept contract (lifted to amreal'),
     the PRIMED raw Deallocate contract (YGcfMallocComposeERh.adealloc_realizes_raw_cf_em_m_rh), the primed record and
     one room premise (batch_room_cf after the inner malloc).
   rule 24: no function proved (kind: statement composition over proved contracts). No image constant. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG0f YG0v YG0n YG0d YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YGcfTok YG06bcf YG07cf YGcfRoomPre YG03cf YG03dcf YGcfApath YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AllocG DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require ReallocG ReallocP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGtop YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoGcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc YG0s YGcfXs YGcfSecsStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRodata YGcfRehidePost YG0dcfR YGcfMallocComposeERh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfReallocCompose YGcfReallocIx.
(* stdpp, through the LPS modules, shadows several list names; In and remove here are Stdlib's, as in YGcfRealloc.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.

(* YGcfReallocCompose's Section J names, at these variables. *)
Local Abbreviation K1r_t := (YGcfReallocCompose.K1r_t segs).
Local Abbreviation K2r_t := (YGcfReallocCompose.K2r_t segs).
Local Abbreviation rtr_cf := YGcfReallocCompose.rtr_cf.

(* Deallocate's primed raw post at the cf instance (the twin of YGcfMallocCompose.free_dpost_cf, AOX := aowned). *)
Definition free_dpost_cf_rh (ARX : ARXh_t segs) (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
dealloc_post_raw_rh segs B (ARX Hp) (aowned B) inst ly S W regs mem md E ly' S' W' regs' mem' md'.

(* The primed realloc(p, n) contract with an entry predicate RP and the hull admission at the post. *)
Definition arealloc_realizes_cf_rp_h_rh (RP : astate -> Prop) (Hp : list Z) (pc : Z) : Prop :=
forall ly S W regs mem md p n_old n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch -> RP S ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly cf_pc_realloc_ra0 regs ch) S ->
(forall trc r S', apath (ReallocP.realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S)
  trc (r, S') -> cf_hull_ok S') ->
amreal' segs RZ_cf (ReallocP.realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => realloc_leaf_cf_rh segs B ly S Hp W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> ReallocP.mt_refused malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S (snd r))).

(* At RP := True, under the admission at every realloc post, it is YG0dcfR.arealloc_realizes_cf_rh. *)
Lemma arealloc_realizes_cf_rp_h_rh_to : forall Hp pc,
(forall ly S regs ch p n trc r S',
  apath (ReallocP.realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S) trc (r, S') ->
  cf_hull_ok S') ->
arealloc_realizes_cf_rp_h_rh (fun _ => True) Hp pc -> arealloc_realizes_cf_rh segs B Hp pc.
Proof.
intros Hp pc HO H ly S W regs mem md p n_old n ch PRE Hin H10 NIN H11 Hn Hlive Htr.
exact (H ly S W regs mem md p n_old n ch PRE I Hin H10 NIN H11 Hn Hlive Htr (HO ly S regs ch p n)).
Qed.

(* A released segment inside a primed run, with the strict world step kept for the continuation (the leaf states
   the world exactly: strict outside the inner free, inside its dead set across it). *)
Lemma amreal'_SRr_pre_w {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop)
  (P : world segs -> config -> Prop),
  SRr segs W c P -> (forall W' c', wle W W' -> P W' c' -> amreal' segs RZ_cf t W' c' Q) -> amreal' segs RZ_cf t W c Q.
Proof.
intros t W c Q P H K.
apply (amreal'_SRr_pre segs RZ_cf t W c Q (fun W' c' => wle W W' /\ P W' c')).
- apply SRr_SRr'. eapply SRr_mono; [exact H|]. intros W' c' Hw HP. exact (conj Hw HP).
- intros W' c' _ [Hw HP]. exact (K W' c' Hw HP).
Qed.

Section R.
(* YGcfReallocCompose's Section R variables, in its order. *)
Variables (nmax al atp acf atpD : Z).
Local Abbreviation rentry_cf := (YGcfReallocCompose.rentry_cf segs B).
Local Abbreviation realloc_dpre_cf := (YGcfReallocCompose.realloc_dpre_cf segs B atpD).
Local Abbreviation vm_rd32_cf := (YGcfReallocCompose.vm_rd32_cf segs).
Local Abbreviation vm_byte1_cf := (YGcfReallocCompose.vm_byte1_cf segs).
Local Abbreviation sptr_addr_block_cf := (YGcfReallocCompose.sptr_addr_block_cf B).
Local Abbreviation pw_snoc_cf := YGcfReallocCompose.pw_snoc_cf.
Local Abbreviation realloc_hp_nn_cf := (YGcfReallocCompose.realloc_hp_nn_cf B).
Local Abbreviation aowned_mid_cf := (YGcfReallocCompose.aowned_mid_cf B).
Local Abbreviation realloc_dpre_free := (YGcfReallocCompose.realloc_dpre_free segs B atpD).
Local Abbreviation ci_malloc_cf := YGcfReallocCompose.ci_malloc_cf.

(* realloc(p, n)'s walk under the re-hide. *)
Record wrap_realloc_walk_cf_rh (ARX : ARXh_t segs) (K1 : K1r_t) (K2 K3 : K2r_t) : Prop := {
(* S1 (RGtop seg_pre). The interceptor's entry (cf_pc_wrap_realloc) -> Reallocate's `jal Allocate`; the entry step
   free_cf PNull is realized on the way. At the call: Allocate's pre at Hp under its model premises (which
   rmodel_ok_cf_wf supplies), the stack window inside the caller's, the keeps across the walk's own instructions,
   errno, and K1. The stack room ly_bot ly + 4096 < spZ regs is acall_prefix_cf's and the errbuf placement
   xs_placed_cf ly S acall_xs_cf's (see section 2). *)
rwh_pre : forall ly S Hp W regs mem md p n_old n ch,
  rentry_cf ly S Hp W regs mem md p n_old n ch -> ly_bot ly + 4096 < spZ regs -> xs_placed_cf ly S ->
  YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
  amreal segs (free_cf PNull (rtr_cf ly regs ch) S) W (cfg_at segs cf_pc_wrap_realloc regs mem md)
  (fun r W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at segs cf_pc_allocate regsA memA mdA /\
    (YGcfRmodel.rpre_cfr B (snd r) n -> blocks_bytes (snd r) + n <= LIVE_MAX -> admits (as_universe B) (rtr_cf ly regs ch) (snd r) ->
     malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly (snd r) W1 regsA memA mdA n (rtr_cf ly regs ch)) /\
    wle W W1 /\ same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    ikeep_cf segs B ly S regs W mem W1 memA /\ errno_kept_cf B mem memA /\
    K1 ly S Hp W regs mem md p n_old n ch (snd r) W1 regsA memA mdA);
(* S2a (RGtop seg_mid_a). Allocate's return with a block q (raZ regsA) -> the copy routine's entry (cf_pc_memcpy)
   with dst = q, src = p, len = min (req_size n_old) n. *)
rwh_mid_a : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K1 ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S1 W1 regsA memA mdA n (rtr_cf ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S1 W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> q <> PNull -> In (q, n) (blocks S2) -> q <> p -> qtight S2 ->
  In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) -> rpreD_free_cf B S2 n_old ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W3 c3 => exists regsM memM mdM,
    c3 = cfg_at segs cf_pc_memcpy regsM memM mdM /\
    ReallocG.rmemcpy_pre segs W3 regsM memM (sptr_addr B ly2 q) (sptr_addr B ly p) (Z.min (req_size n_old) n) /\
    (forall i, 0 <= i < Z.min (req_size n_old) n ->
     aview segs (w_H W3) memM (sptr_addr B ly p + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
    (forall a, sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n -> 0 <= a < 2 ^ 64 /\ ~ ascratch B ASTACK regs a) /\
    same_io md2 mdM /\ RGtop.rkeep segs B regs W2 mem2 W3 memM /\
    errno_kept_cf B mem2 memM /\ 
    K2 ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM);
(* The copy routine (REAL(memcpy), reached at cf_pc_memcpy): ReallocG.amemcpy_realizes (ReallocG.v:243-251) at that
   pc, with the overlay normal form kept. *)
rwh_memcpy : forall (W : world segs) regs mem md d s n,
  ReallocG.rmemcpy_pre segs W regs mem d s n ->
  SRr segs W (cfg_at segs cf_pc_memcpy regs mem md)
  (fun W' c' => (W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    (forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) = aview segs (w_H W) mem (s + i)) /\
    (forall x : word, ~ (d <= bv_unsigned x < d + n) -> mem' x = mem x) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)));
(* S2b (RGtop seg_mid_b). The copy routine's return (raZ regsM) -> Reallocate's `jal Deallocate`: Deallocate's pre
   on the old block at Hp (fpre := True). *)
rwh_mid_b : forall ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K2 ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM ->
  In (p, n_old) (blocks S2) -> rpreD_free_cf B S2 n_old -> admits (as_universe B) (rtr_cf ly regs ch) S2 ->
  ly_bot ly + 4096 < spZ regs ->
  aregs_preserved regsM regs3 -> same_but_materialized mdM md3 ->
  (forall i, 0 <= i < Z.min (req_size n_old) n ->
   aview segs (w_H W3) mem3 (sptr_addr B ly2 q + i) = aview segs (w_H W3) memM (sptr_addr B ly p + i)) ->
  (forall x : word, ~ (sptr_addr B ly2 q <= bv_unsigned x < sptr_addr B ly2 q + Z.min (req_size n_old) n) ->
   mem3 x = memM x) ->
  (forall a, apresent (w_H W3) memM a -> apresent (w_H W3) mem3 a) ->
  SRr segs W3 (cfg_at segs (raZ regsM) regs3 mem3 md3)
  (fun W4 c4 => exists inst so bp regsD memD mdD,
    c4 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) /\
    same_io md3 mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    RGtop.rkeep segs B regs W3 mem3 W4 memD /\ RGtop.rwin segs regs W4 memD /\
    errno_kept_cf B mem3 memD /\
    K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD);
(* S3 (RGtop seg_ret) under the re-hide: Deallocate's PRIMED raw post (free_dpost_cf_rh). Every other field is
   wrap_realloc_walk_cf's, token for token. *)
rwh_ret : forall ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
  realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) ->
  free_dpost_cf_rh ARX Hp' inst ly2 S2 W4 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old) ly3 S3 W5 regs5 mem5 md5 ->
  qtight S3 ->
  SRr segs W5 (cfg_at segs (raZ regsD) regs5 mem5 md5)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp' inst ly3 S3 W' mem' md' /\ same_io md5 md' /\
    RGtop.rkeep segs B regs W5 mem5 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    errno_kept_cf B mem5 mem');
(* S4 (RGtop seg_nret). Allocate's return with PNull (raZ regsA) -> the interceptor's return, a0 = 0: errno :=
   ENOMEM and the out-of-memory byte. (RGtop's image premise as_errno B = as_tp B - 0xa4 is the walk's own.) *)
rwh_nret : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K1 ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S1 W1 regsA memA mdA n (rtr_cf ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S1 W1 regsA memA mdA
    (fun a => PNull <> PNull /\ sptr_addr B ly2 PNull <= a < sptr_addr B ly2 PNull + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 PNull) -> qtight S2 ->
  val_mem segs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1 ->
  In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
    val_mem segs (mrestrict (w_H W') mem') (as_oom_byte B) 1 1)
}.

(* The released record and a primed S3 give the primed record. *)
Lemma wrap_realloc_walk_cf_rh_of : forall ARX K1 K2 K3,
YGcfReallocCompose.wrap_realloc_walk_cf segs B nmax al atp acf atpD ARX K1 K2 K3 ->
(forall ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
  realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) ->
  free_dpost_cf_rh ARX Hp' inst ly2 S2 W4 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old) ly3 S3 W5 regs5 mem5 md5 ->
  qtight S3 ->
  SRr segs W5 (cfg_at segs (raZ regsD) regs5 mem5 md5)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp' inst ly3 S3 W' mem' md' /\ same_io md5 md' /\
    RGtop.rkeep segs B regs W5 mem5 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    errno_kept_cf B mem5 mem')) ->
wrap_realloc_walk_cf_rh ARX K1 K2 K3.
Proof.
intros ARX K1 K2 K3 [P MA MC MB _ NR] RET.
exact (Build_wrap_realloc_walk_cf_rh ARX K1 K2 K3 P MA MC MB RET NR).
Qed.

(* The room the composition needs after the inner malloc: from the caller's entry predicate RP and the two model
   steps, or from the relation at the post (the compose's ARX_br). *)
Definition realloc_room_rp (RP : astate -> Prop) (ARX : ARXh_t segs) : Prop :=
forall ly S Hp W regs mem md ch tr trc1 S1 n trc2 (q : sptr) S2 inst ly2 W2 mem2 md2,
acall_pre_cf segs B ly S Hp W regs mem md ch -> RP S ->
apath (free_cf PNull tr S) trc1 (tt, S1) -> apath (malloc_cf n tr S1) trc2 (q, S2) ->
ARX Hp inst ly2 S2 W2 mem2 md2 -> batch_room_cf S2.

(* A relation that carries the batch room (YGcfReallocCompose.ARX_br) gives the room at every entry predicate. *)
Lemma realloc_room_rp_of_br : forall RP ARX, YGcfReallocCompose.ARX_br segs ARX -> realloc_room_rp RP ARX.
Proof.
intros RP ARX HBR ly S Hp W regs mem md ch tr trc1 S1 n trc2 q S2 inst ly2 W2 mem2 md2 _ _ _ _ HX.
exact (HBR _ _ _ _ _ _ _ HX).
Qed.

(* The statement of the primed composition. *)
Definition arealloc_realizes_cf_rp_rh_of_parts_t : Prop :=
forall (RP : astate -> Prop) (ARX : ARXh_t segs) (K1 : K1r_t) (K2 K3 : K2r_t),
YGcfReallocCompose.acall_prefix_cf segs B -> YGcfReallocCompose.acall_xs_cf segs B ->
YGcfReallocCompose.errno_word_cf B -> relro_seg_t segs -> errno_relro_t B ->
nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX -> YGcfReallocCompose.ARX_qmh segs ARX ->
realloc_room_rp RP ARX ->
aalloc_realizes_cf_em_m segs B nmax al atp acf ARX ->
adealloc_realizes_raw_cf_em_m_rh segs B atpD ARX ->
wrap_realloc_walk_cf_rh ARX K1 K2 K3 ->
forall Hp, arealloc_realizes_cf_rp_h_rh RP Hp cf_pc_wrap_realloc.

(* realloc(p, n) under the re-hide: the released realloc(p, n) composition of YGcfReallocCompose.v, step for step,
   over amreal', with the primed Deallocate, the primed S3, and the entry's room. *)
Theorem arealloc_realizes_cf_rp_rh_of_parts : arealloc_realizes_cf_rp_rh_of_parts_t.
Proof.
intros RPe ARX K1 K2 K3 HPFX HXSP HEW RS ER HNM HAR HXS HQM BRP HAM HDM [WPRE WMIDA WMEM WMIDB WRET WNRET] Hp.
intros ly S W regs mem md p n_old n ch PRE RPS Hin H10 NIN H11 Hn Hlive Htr HADM.
pose proof (aalloc_realizes_cf_em_of_m segs B nmax al atp acf ARX HAM) as HA.
assert (ENT : rentry_cf ly S Hp W regs mem md p n_old n ch)
  by exact (conj PRE (conj Hin (conj H10 (conj NIN (conj H11 (conj Hn (conj Hlive Htr))))))).
pose proof (HPFX ly S Hp W regs mem md ch PRE) as HBOT.
pose proof (HXSP ly S Hp W regs mem md ch PRE) as HXS0.
pose proof (rpre_cfr_of_pre segs B ly S Hp W regs mem md ch n PRE) as RP.
assert (HN : 0 <= n < nmax) by (unfold nmax_cf_ok in HNM; lia).
pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 PRE))) as WF0.
set (tr := call_trace ly cf_pc_realloc_ra0 regs ch) in *.
unfold ReallocP.realloc_tree_with.
(* S1: the entry step free_cf PNull, to Allocate's entry *)
eapply (amreal'_mbind segs RZ_cf);
  [exact (amreal_amreal' segs RZ_cf _ _ _ _ (RGtop.rg_apath_gflag segs _ _ _ _ (WPRE ly S Hp W regs mem md p n_old n ch ENT HBOT HXS0 RP HN)))|].
intros [] S1 W1 c1 H1. cbv beta in H1.
destruct H1 as [(inst & so & bp & regsA & memA & mdA & Ec1 & APREi & WLE1 & IO1 & RIN1 & KP1 & ER1 & HK1) (trc1 & HP1 & HG1)].
subst c1. cbn [snd] in *.
destruct (YGcfRmodel.rmodel_ok_cf_wf B) as [MO1 MO2].
destruct (MO1 S n tr trc1 S1 RP Hn Hlive Htr HP1 HG1) as (UA1 & RA1 & BB1 & BL1 & SEC1 & AOX1).
pose proof (APREi RA1 BB1 UA1) as APR.
pose proof RA1 as (HU & WF1 & (HSA1 & HER1 & HBR1) & _).
assert (BLK1 : In (p, n_old) (blocks S1)) by (rewrite BL1; exact Hin).
pose proof (YGcfRmodel.cfr_null_state tr S trc1 S1 HP1) as ES1.
assert (CH1 : st_chunks S1 = st_chunks S) by (rewrite ES1; reflexivity).
assert (II1 : st_internal_inited S1 = true) by (rewrite ES1; reflexivity).
assert (FR1 : frames S1 = frames S) by (rewrite ES1; reflexivity).
assert (XO : forall a, ~ aowned B ly S a -> ~ Exists (in_zr a) (xs_cf ly S) -> ~ AOXm_cf B ly S1 a).
{ intros a N1 N2 X. destruct (AOX1 ly a X) as [Y|Y]; [exact (N1 Y) | exact (N2 Y)]. }
assert (XSA : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B AllocG.AFSTACK_G regsA a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsA AllocG.AFSTACK_G a (proj1 RIN1) (proj2 RIN1) X))).
(* Allocate.  Field round 3 part 3b / 3c: arodata_ok_cf at Allocate's entry memory memA, from the call's
   (acall_pre_cf's last conjunct) through S1's raw frame (ikeep_cf), as YGcfReallocCompose's proof does. *)
pose proof (YGcfReallocCompose.acall_pre_cf_ro segs B ly S Hp W regs mem md ch PRE) as HROa0.
assert (ROa : arodata_ok_cf segs B memA).
{ pose proof (amc_layout _ _ _ _ _ (proj1 (proj1 PRE))) as LOa.
  assert (STKa : ly_stk_lo ly + ASTACK <= spZ regs) by (destruct PRE as (_ & _ & _ & STK & _); exact STK).
  apply (arodata_frame_cf segs B (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) mem memA); [| |exact HROa0].
  - intros x NX. exact (proj2 KP1 x (fun H => NX (or_introl H)) (fun H => NX (or_intror H))).
  - intros a Ha NO. destruct (relro_apart_cf segs B ly S Hp W mem md a (proj1 PRE) RS Ha NO) as (R & _ & NA0 & _).
    split; [unfold kImgLo, kImgEnd in R; lia|].
    intros [X|X]; [exact (NA0 X) | exact (relro_not_scratch_cf B ly ASTACK regs a LOa STKa ER Ha R X)]. }
eapply (amreal'_mbind segs RZ_cf);
  [exact (amreal_amreal' segs RZ_cf _ _ _ _ (HA Hp inst so bp ly S1 W1 regsA memA mdA n tr APR ROa))|].
intros q S2 W2 c2 [LEAF KEEP].
unfold malloc_aleaf_cf, AllocG.alloc_leaf in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & (trc2 & HP2 & HG2) & OOM).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERA _].
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
destruct (MO2 S n tr trc1 S1 trc2 q S2 RP Hn Hlive Htr HP1 HG1 HP2 HG2) as (UD2 & QB2 & PB2).
destruct (PB2 p n_old Hin) as (BLK2 & RD2 & QP2).
pose proof (malloc_cf_apath_post (as_universe B) S1 n tr trc2 (q, S2) HU WF1 ltac:(lia) BB1 UA1 HSA1 HER1 HBR1 HP2) as MPOST.
destruct MPOST as (WF2 & _ & SX2 & FRM2 & MBL2 & _).
assert (LLE02 : layout_le (length (st_secs S)) ly ly2) by exact (layout_le_trans _ _ ly ly ly2 SEC1 (layout_le_refl _ ly) LLE2).
pose proof (YGcfXs.cfx_ipost_apath _ _ trc2 (q, S2) (ci_malloc_cf n tr S1) HP2) as CM. cbn [fst snd] in CM.
destruct CM as [CMi CMc].
destruct (RGtop.rg_null_dec q) as [EQ | HQ].
- (* the NULL-return arm *)
  subst q. cbv beta iota.
  eapply amreal'_SRr_pre_w; [exact (WNRET ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2
    ENT HK1 APR APO A02 LP2 (OOM eq_refl) BLK1 BLK2)|].
  intros W' c' WLE3 (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN' & ERV & OMV). subst c'.
  apply (amreal'_ret segs RZ_cf).
  split.
  + apply realloc_leaf_cf_rh_of. exists ly2, regs', mem', md'. cbn [fst snd YGcfRealloc.realloc_hp_cf].
    split; [reflexivity|].
    split.
    { split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE02|].
      split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
      split; [exact CS'|].
      split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
      split; [|exact WN'].
      intros a Ha NA NA2 NS NE.
      assert (NX0 : ~ Exists (in_zr a) (xs_cf ly S)) by (intros X; apply NE; right; right; apply Exists_app; left; exact X).
      assert (NX2 : ~ Exists (in_zr a) (xs_cf ly2 S2)) by (intros X; apply NE; right; right; apply Exists_app; right; exact X).
      rewrite (proj1 KP' a Ha NS).
      rewrite (FR2 a Ha (XO a NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX2 X)]) (XSA a NS)
        ltac:(intros [X _]; exact (X eq_refl))).
      exact (proj1 KP1 a Ha NA NS). }
    split; [rewrite A0'; reflexivity|].
    split; [exact LP2|].
    split; [intros X; exfalso; exact (X eq_refl)|].
    split; [intros _; exact (conj (vm_rd32_cf _ _ _ _ ERV) (vm_byte1_cf _ _ _ OMV))|].
    split; [exact (HXS _ _ _ _ _ _ _ ARX')|].
    split; [intros X; exfalso; exact (X eq_refl)|].
    intros x NA NA2 NS NE.
      assert (NX0 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly S))
        by (intros X; apply NE; right; right; apply Exists_app; left; exact X).
      assert (NX2 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly2 S2))
        by (intros X; apply NE; right; right; apply Exists_app; right; exact X).
      rewrite (proj2 KP' x NS).
      rewrite (FR2w x (XO _ NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX2 X)]) (XSA _ NS)
        ltac:(intros [X _]; exact (X eq_refl))).
      exact (proj2 KP1 x NA NS).
  + intros _. exists S1, trc1, trc2. exact (conj HP1 (conj HG1 (conj HP2 HG2))).
- (* a block q: the copy, the free of the old block, the return *)
  assert (RK : forall s, (match q with PNull => YG00.ret PNull | _ => YG00.bind (free_cf p tr) (fun _ => YG00.ret q) end) s
    = YG00.bind (free_cf p tr) (fun _ => YG00.ret q) s)
    by (intros s; destruct q; [exfalso; exact (HQ eq_refl) | reflexivity | reflexivity | reflexivity]).
  cbv beta. rewrite RK.
  assert (II2 : st_internal_inited S2 = true) by (rewrite CMi; exact II1).
  (* the batch class's room after the inner malloc, from the caller's entry predicate (realloc_room_rp) *)
  pose proof (BRP ly S Hp W regs mem md ch tr trc1 S1 n trc2 q S2 inst ly2 W2 mem2 md2 PRE RPS HP1 HP2 ARX2) as BR2.
  (* the hull admission at S2, before the inner Deallocate: the inner free's model path from S2 (ml_free_cf at
     batch_room_cf S2), the realloc tree's path through it, the caller's admission at that post (HADM), and the class
     law cf_hull_counts across the free, which keeps both secondary counts (YGcfSecsStep.secs_free_step, :680) *)
  destruct (YGcfReallocCompose.inner_free_path_cf (as_universe B) S2 p n_old tr HU WF2 BR2 BLK2 (UD2 HQ))
    as (trc3' & S3' & HP3').
  pose proof (HADM _ q S3' (YGcfReallocCompose.realloc_tree_path_cf p n tr S trc1 S1 trc2 q S2 trc3' S3' HQ HP1 HP2 HP3')) as HO3.
  destruct (YGcfSecsStep.secs_free_step p tr S2 trc3' S3' HP3') as [SN ST].
  pose proof (cf_hull_counts S2 S3' SN ST HO3) as HO2.
  assert (RDF2 : rpreD_free_cf B S2 n_old)
    by exact (conj (RD2 HQ) (conj (HQM _ _ _ _ _ _ _ ARX2 HO2) (conj II2 (conj BR2 HO2)))).
  (* S2a, the copy routine, S2b *)
  eapply amreal'_SRr_pre_w; [exact (WMIDA ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
    ENT HK1 APR APO A02 HQ (QB2 HQ) (QP2 HQ) LP2 BLK1 BLK2 RDF2)|].
  intros W3 c3 WLE23 (regsM & memM & mdM & Ec3 & MPRE & SRC & NBLK & IO3 & KP3 & ER3 & HK2). subst c3.
  eapply amreal'_SRr_pre_w; [exact (WMEM W3 regsM memM mdM _ _ _ MPRE)|].
  intros W3' c3' _ (EW3 & regs3 & mem3 & md3 & Ec3' & CS3 & IO3' & CPY3 & FR3 & PR3). subst W3' c3'.
  eapply amreal'_SRr_pre_w; [exact (WMIDB ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3
    ENT HK2 BLK2 RDF2 (UD2 HQ) HBOT CS3 IO3' CPY3 FR3 PR3)|].
  intros W4 c4 WLE34 (inst' & so' & bp' & regsD & memD & mdD & Ec4 & DPR & IO4 & RIN4 & KP4 & WN4 & ER4 & HK3). subst c4.
  (* Deallocate, at Hp: the old base is not hidden *)
  assert (AP2 : sptr_addr B ly2 p = sptr_addr B ly p) by exact (sptr_addr_block_cf _ ly ly2 S p n_old WF0 Hin LLE02).
  assert (DPRF : free_dpre_cf segs B atpD ARX Hp inst' so' bp' ly2 S2 W4 regsD memD mdD p n_old tr)
    by (apply realloc_dpre_free; [exact DPR | rewrite AP2; exact NIN]).
  (* field round 3, part 3 / 3c: arodata_ok_cf at Deallocate's entry memory memD, from the call's
     (acall_pre_cf's last conjunct) through the raw frames of S1 (ikeep_cf), Allocate (FR2w), S2a and
     S2b (RGtop.rkeep) and the copy routine *)
  pose proof (YGcfReallocCompose.acall_pre_cf_ro segs B ly S Hp W regs mem md ch PRE) as HRO0.
  assert (ROd : arodata_ok_cf segs B memD).
  { pose proof (amc_layout _ _ _ _ _ (proj1 (proj1 PRE))) as LO0.
    assert (STK0 : ly_stk_lo ly + ASTACK <= spZ regs) by (destruct PRE as (_ & _ & _ & STK & _); exact STK).
    assert (ARS1 : ARcf segs B ly S1 Hp W1 memA mdA) by exact (HAR _ _ _ _ _ _ _ (proj1 APR)).
    assert (STKA : ly_stk_lo ly + AllocG.AFSTACK_G <= spZ regsA)
      by (destruct APR as (_ & _ & _ & _ & _ & STK & _); exact STK).
    assert (ARS2 : ARcf segs B ly2 S2 Hp W2 mem2 md2) by exact (HAR _ _ _ _ _ _ _ ARX2).
    pose proof (blocks_chunk_cf S2 q n (QB2 HQ)) as QK.
    (* every non-owned RELRO byte misses each exception set of the five frames *)
    assert (RF : forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) ->
      0 <= a < 2 ^ 64 /\ ~ aowned B ly S a /\ ~ AOXm_cf B ly S1 a /\ ~ AOXm_cf B ly2 S2 a /\
      ~ ascratch B ASTACK regs a /\ ~ ascratch B AllocG.AFSTACK_G regsA a /\
      ~ (sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)).
    { intros a Ha NO.
      destruct (relro_apart_cf segs B ly S Hp W mem md a (proj1 PRE) RS Ha NO) as (R & _ & NA0 & _).
      destruct (relro_apart_cf segs B ly S1 Hp W1 memA mdA a ARS1 RS Ha NO) as (_ & _ & NA1 & NX1).
      destruct (relro_apart_cf segs B ly2 S2 Hp W2 mem2 md2 a ARS2 RS Ha NO) as (_ & I2 & NA2 & NX2).
      split; [unfold kImgLo, kImgEnd in R; lia|]. split; [exact NA0|].
      split; [intros [X|X]; [exact (NA1 X) | exact (NX1 X)]|].
      split; [intros [X|X]; [exact (NA2 X) | exact (NX2 X)]|].
      split; [exact (relro_not_scratch_cf B ly ASTACK regs a LO0 STK0 ER Ha R)|].
      split; [exact (relro_not_scratch_cf B ly AllocG.AFSTACK_G regsA a LO0 STKA ER Ha R)|].
      exact (relro_not_block_cf B ly2 S2 Hp _ q n a (proj1 ARS2) QK I2). }
    (* S1: mem -> memA *)
    assert (RO1 : arodata_ok_cf segs B memA).
    { apply (arodata_frame_cf segs B (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) mem memA); [| |exact HRO0].
      - intros x NX. exact (proj2 KP1 x (fun H => NX (or_introl H)) (fun H => NX (or_intror H))).
      - intros a Ha NO. destruct (RF a Ha NO) as (H64 & NA0 & _ & _ & NS & _). split; [exact H64|].
        intros [X|X]; [exact (NA0 X) | exact (NS X)]. }
    (* Allocate: memA -> mem2 *)
    assert (RO2 : arodata_ok_cf segs B mem2).
    { apply (arodata_frame_cf segs B (fun a => AOXm_cf B ly S1 a \/ AOXm_cf B ly2 S2 a \/
        ascratch B AllocG.AFSTACK_G regsA a \/ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n))
        memA mem2); [| |exact RO1].
      - intros x NX. first [apply FR2w | symmetry; apply FR2w]; intros Y; apply NX; cbv beta; tauto.
      - intros a Ha NO. destruct (RF a Ha NO) as (H64 & _ & N1 & N2 & _ & NSA & NB). split; [exact H64|].
        intros [X|[X|[X|[_ X]]]]; [exact (N1 X) | exact (N2 X) | exact (NSA X) | exact (NB X)]. }
    (* S2a: mem2 -> memM *)
    assert (ROM : arodata_ok_cf segs B memM).
    { apply (arodata_frame_cf segs B (fun a => ascratch B ASTACK regs a) mem2 memM); [| |exact RO2].
      - intros x NX. exact (proj2 KP3 x NX).
      - intros a Ha NO. destruct (RF a Ha NO) as (H64 & _ & _ & _ & NS & _). exact (conj H64 NS). }
    (* the copy routine: memM -> mem3 *)
    assert (RO3 : arodata_ok_cf segs B mem3).
    { apply (arodata_frame_cf segs B (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + Z.min (req_size n_old) n)
        memM mem3); [| |exact ROM].
      - intros x NX. exact (FR3 x NX).
      - intros a Ha NO. destruct (RF a Ha NO) as (H64 & _ & _ & _ & _ & _ & NB). split; [exact H64|].
        intros X. apply NB. pose proof (RGtop.rg_req_size_ge n). lia. }
    (* S2b: mem3 -> memD *)
    apply (arodata_frame_cf segs B (fun a => ascratch B ASTACK regs a) mem3 memD); [| |exact RO3].
    - intros x NX. exact (proj2 KP4 x NX).
    - intros a Ha NO. destruct (RF a Ha NO) as (H64 & _ & _ & _ & NS & _). exact (conj H64 NS). }
  (* Deallocate, primed: its post may re-hide inside dead_shadow_new ly2 S2 S3 *)
  eapply (amreal'_mbind segs RZ_cf); [exact (HDM Hp inst' so' bp' ly2 S2 W4 regsD memD mdD p n_old tr DPRF ROd)|].
  intros [] S3 W5 c5 DLEAF.
  unfold dealloc_leaf_raw_em_rh in DLEAF.
  destruct DLEAF as (ly3 & regs5 & mem5 & md5 & Ec5 & DPO & ERD & MND & LP3 & (trc3 & HP3 & HG3)). subst c5. cbn [snd] in *.
  pose proof DPO as ((ARX3 & LLE3 & WLE45 & CS5 & IO5 & FR5 & PR5) & FR5w).
  (* the inner free's dead set lies in the call's (YGcfReallocIx.realloc_dead_ix_of_paths); Wf_cf at the realloc's
     entry is the call's own (acall_pre_cf's ARcf, WF0) *)
  pose (INC := fun a => YGcfReallocIx.realloc_dead_ix_of_paths _ ly ly2 S S1 S2 S3 n p q tr tr tr trc1 trc2 trc3 a
    WF0 HP1 HP2 (QP2 HQ) HP3 LLE02).
  (* S3 *)
  eapply amreal'_SRr_pre_w; [exact (WRET ly S Hp Hp W regs mem md p n_old n ch q ly2 S2 W4 inst' so' bp' regsD memD mdD
    ly3 S3 W5 regs5 mem5 md5 ENT HK3 DPR DPO LP3)|].
  intros W' c' WLE5' (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN' & ER'). subst c'.
  cbv beta. apply (amreal'_ret segs RZ_cf).
  (* the model after the free: blocks and frames *)
  assert (AF : atok_cf true (free_cf p tr S2) (free_post_ycf (as_universe B) S2 p n_old)).
  { eapply ml_free_cf; first [exact HU | exact WF2 | exact BR2 | (right; exact BLK2) | exact (UD2 HQ)]. }
  destruct (atok_cf_apath _ _ _ _ _ AF HP3) as [ns3 FP3].
  destruct FP3 as (WF3 & _ & _ & FRM3 & (l1 & l2 & HL12 & BL3) & _).
  cbn [snd] in WF3, FRM3, BL3.
  assert (BL3S2 : forall b, In b (blocks S3) -> In b (blocks S2)).
  { intros b Hb. rewrite BL3 in Hb. destruct HL12 as [(_ & E) | E].
    - rewrite <- E. exact Hb.
    - rewrite E. apply in_app_iff in Hb as [Hb|Hb]; apply in_app_iff; [left; exact Hb | right; right; exact Hb]. }
  assert (QB3 : In (q, n) (blocks S3)).
  { pose proof (QB2 HQ) as Q2. rewrite BL3. destruct HL12 as [(_ & E) | E].
    - rewrite E. exact Q2.
    - rewrite E in Q2. apply in_app_iff in Q2 as [Q2|[Q2|Q2]]; apply in_app_iff.
      + left. exact Q2.
      + exfalso. injection Q2 as Eq _. exact (QP2 HQ (eq_sym Eq)).
      + right. exact Q2. }
  assert (MBL2' : blocks S2 = blocks S1 ++ [(q, n)])
    by (destruct q; [exfalso; exact (HQ eq_refl) | exact (proj1 MBL2) | exact (proj1 MBL2) | exact (proj1 MBL2)]).
  (* layouts and addresses *)
  assert (AQ3 : sptr_addr B ly3 q = sptr_addr B ly2 q) by exact (sptr_addr_block_cf _ ly2 ly3 S2 q n WF2 (QB2 HQ) LLE3).
  pose proof (proj1 SX2) as SL12.
  assert (LLE03 : layout_le (length (st_secs S)) ly ly3)
    by exact (layout_le_trans (length (st_secs S)) (length (st_secs S2)) ly ly2 ly3 ltac:(lia) LLE02 LLE3).
  (* the owned set of the middle state, at one layout (aowned_mid_cf) *)
  pose proof (YG0scf.AR_layout_law_ok_cf segs B) as LAYL.
  assert (OWN0 : forall a, aowned B ly3 S a <-> aowned B ly S a)
    by exact (proj2 (proj2 (LAYL ly S Hp W mem md ly3 (proj1 PRE) LLE03))).
  assert (OWN2 : forall a, aowned B ly3 S2 a <-> aowned B ly2 S2 a)
    by exact (proj2 (proj2 (LAYL ly2 S2 Hp W2 mem2 md2 ly3 (HAR _ _ _ _ _ _ _ ARX2) LLE3))).
  assert (MID : forall a, ~ aowned B ly S a -> ~ aowned B ly3 S3 a -> ~ aowned B ly2 S2 a).
  { intros a NA NA3 O2.
    apply (aowned_mid_cf ly3 S S2 S3 q n a).
    - intros k Hk. destruct (CMc k Hk) as [X|X]; [left; rewrite <- CH1; exact X | right; exact X].
    - intros [b1 b2] Hb. exact (proj1 (PB2 b1 b2 Hb)).
    - rewrite FRM2. exact FR1.
    - exact QB3.
    - exact BL3S2.
    - exact FRM3.
    - exact (proj2 (OWN2 a) O2).
    - intros X. exact (NA (proj1 (OWN0 a) X)).
    - exact NA3. }
  (* the errbuf extent of the middle state is the end state's *)
  assert (XS23 : forall a, Exists (in_zr a) (xs_cf ly2 S2) -> Exists (in_zr a) (xs_cf ly3 S3)).
  { intros a X. rewrite <- (YGcfXs.xs_cf_layout ly2 ly3 S2 LLE3) in X.
    rewrite <- (proj1 (YGcfXs.free_cf_frame p tr S2 trc3 S3 HP3) ly3) in X. exact X. }
  (* the new block: apart from the old one at S2, and client bytes at S2 and S3 *)
  pose proof (YG0scf.AR_blocks_law_ok_cf segs B) as LAWB.
  assert (QA2 : In (sptr_addr B ly2 q, n) (ablocks B ly2 S2))
    by exact (in_map (fun b => (sptr_addr B ly2 (fst b), snd b)) _ _ (QB2 HQ)).
  destruct (LAWB ly2 S2 Hp W2 mem2 md2 _ _ (HAR _ _ _ _ _ _ _ ARX2) QA2) as (_ & _ & _ & QIA2 & QOWN2 & PW & _).
  assert (QA3 : In (sptr_addr B ly3 q, n) (ablocks B ly3 S3))
    by exact (in_map (fun b => (sptr_addr B ly3 (fst b), snd b)) _ _ QB3).
  destruct (LAWB ly3 S3 Hp W5 mem5 md5 _ _ (HAR _ _ _ _ _ _ _ ARX3) QA3) as (_ & _ & _ & _ & QOWN3 & _ & _).
  assert (DJ : sptr_addr B ly2 p + req_size n_old <= sptr_addr B ly2 q \/ sptr_addr B ly2 q + req_size n <= sptr_addr B ly2 p).
  { unfold ablocks in PW. rewrite MBL2' in PW. rewrite !map_app in PW. cbn [map fst snd] in PW.
    assert (D : zdisjoint (sptr_addr B ly2 p, req_size n_old) (sptr_addr B ly2 q, req_size n)).
    { eapply pw_snoc_cf; [exact PW|]. apply in_map_iff. exists (sptr_addr B ly2 p, n_old). split; [reflexivity|].
      apply in_map_iff. exists (p, n_old). split; [reflexivity | exact BLK1]. }
    unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
  assert (NOWN2 : forall a, sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n -> ~ aowned B ly2 S2 a)
    by (intros a Ha; exact (proj2 (QOWN2 a Ha))).
  assert (NOWN3 : forall a, sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n -> ~ aowned B ly3 S3 a)
    by (intros a Ha; rewrite <- AQ3 in Ha; exact (proj2 (QOWN3 a Ha))).
  assert (XSD : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B DeallocG.DFSTACK_G regsD a)
    by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsD DeallocG.DFSTACK_G a (proj1 RIN4) (proj2 RIN4) X))).
  pose proof (RGtop.rg_req_size n (proj1 Hn)) as RQ.
  pose proof (RGtop.rg_req_size_ge n_old) as RQO.
  (* the leaf *)
  split; [|intros X; exfalso; exact (HQ X)].
  exists ly3, regs', mem', md'. cbn [fst snd].
  rewrite (realloc_hp_nn_cf ly p q Hp HQ). rewrite notin_remove; [|exact NIN].
  split; [reflexivity|].
  split.
  { split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE03|].
    (* the world: strict before and after the inner free, inside the inner free's dead set across it *)
    split.
    { intros x Hx. destruct (WLE45 x (WLE5' x Hx)) as [H4 | HD4].
      - left. exact (WLE1 x (WLE2 x (WLE23 x (WLE34 x H4)))).
      - right. exact (INC _ HD4). }
    split; [exact CS'|].
    split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _
      (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO3)
      (RGtop.rg_sbm_io _ _ IO3')) IO4) IO5) IO')|].
    split; [|exact WN'].
    intros a Ha NA NA3 NS NE NDS.
    assert (NEn : ~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n))
      by (rewrite <- AQ3; intros X; apply NE; left; exact X).
    assert (NEo : ~ (p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old))
      by (rewrite AP2; intros [_ X]; apply NE; right; left; exact (conj HQ X)).
    assert (NX0 : ~ Exists (in_zr a) (xs_cf ly S)) by (intros X; apply NE; right; right; apply Exists_app; left; exact X).
    assert (NX3 : ~ Exists (in_zr a) (xs_cf ly3 S3)) by (intros X; apply NE; right; right; apply Exists_app; right; exact X).
    pose proof (MID a NA NA3) as NA2.
    rewrite (proj1 KP' a Ha NS).
    rewrite (FR5 a Ha NA2 NA3 (XSD a NS) NEo (fun X => NDS (INC _ X))).
    rewrite (proj1 KP4 a Ha NS).
    rewrite (RGtop.rg_aview_same segs (w_H W3) memM mem3 a
      (FR3 _ ltac:(rewrite (RGtop.rg_unsigned_small a Ha); intros X; apply NEn; split; [exact HQ | lia]))).
    rewrite (proj1 KP3 a Ha NS).
    rewrite (FR2 a Ha (XO a NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX3 (XS23 a X))]) (XSA a NS) NEn).
    exact (proj1 KP1 a Ha NA NS). }
  split; [rewrite AQ3; exact A0'|].
  split; [exact LP3|].
  split.
  { intros _ i Hi.
    assert (Hi' : 0 <= i < Z.min (req_size n_old) n) by lia.
    assert (Hq : sptr_addr B ly2 q <= sptr_addr B ly2 q + i < sptr_addr B ly2 q + req_size n) by lia.
    destruct (NBLK _ Hq) as [Ra NS].
    rewrite AQ3.
    rewrite (proj1 KP' _ Ra NS).
    rewrite (FR5 _ Ra (NOWN2 _ Hq) (NOWN3 _ Hq) (XSD _ NS) ltac:(intros [_ X]; lia)
      (dead_shadow_new_app ly2 S2 S3 _ (in_app_addr _ _ _ QIA2 Hq))).
    rewrite (proj1 KP4 _ Ra NS), (CPY3 i Hi'), (SRC i Hi'). reflexivity. }
  split; [intros X; exfalso; exact (HQ X)|].
  split; [exact (HXS _ _ _ _ _ _ _ ARX')|].
  split.
  { intros _ i Hi.
    rewrite (ER' i Hi), (ERD i Hi), (ER4 i Hi).
    assert (EM : mem3 (w64 (as_errno B + i)) = memM (w64 (as_errno B + i))).
    { apply FR3. assert (Hr : 0 <= as_errno B + i < 2 ^ 64) by (destruct HEW; lia).
      unfold w64. rewrite (RGtop.rg_unsigned_small _ Hr). intros X.
      assert (Hx : sptr_addr B ly2 q <= as_errno B + i < sptr_addr B ly2 q + req_size n) by lia.
      destruct (NBLK _ Hx) as [_ NS]. apply NS. right. lia. }
    rewrite EM, (ER3 i Hi), (ERA HQ i Hi). exact (ER1 i Hi). }
  intros x NA NA3 NS NE.
    assert (NEn : ~ (q <> PNull /\ sptr_addr B ly2 q <= bv_unsigned x < sptr_addr B ly2 q + req_size n))
      by (rewrite <- AQ3; intros X; apply NE; left; exact X).
    assert (NEo : ~ (p <> PNull /\ sptr_addr B ly2 p <= bv_unsigned x < sptr_addr B ly2 p + req_size n_old))
      by (rewrite AP2; intros [_ X]; apply NE; right; left; exact (conj HQ X)).
    assert (NX0 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly S))
      by (intros X; apply NE; right; right; apply Exists_app; left; exact X).
    assert (NX3 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly3 S3))
      by (intros X; apply NE; right; right; apply Exists_app; right; exact X).
    pose proof (MID _ NA NA3) as NA2.
    rewrite (proj2 KP' x NS), (FR5w x NA2 NA3 (XSD _ NS) NEo), (proj2 KP4 x NS).
    rewrite (FR3 x ltac:(intros X; apply NEn; split; [exact HQ | lia])).
    rewrite (proj2 KP3 x NS).
    rewrite (FR2w x (XO _ NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX3 (XS23 _ X))]) (XSA _ NS) NEn).
    exact (proj2 KP1 x NA NS).
Qed.

End R.
End J.
End G.

Print Assumptions arealloc_realizes_cf_rp_h_rh_to.
Print Assumptions amreal'_SRr_pre_w.
Print Assumptions wrap_realloc_walk_cf_rh_of.
Print Assumptions realloc_room_rp_of_br.
Print Assumptions arealloc_realizes_cf_rp_rh_of_parts.
