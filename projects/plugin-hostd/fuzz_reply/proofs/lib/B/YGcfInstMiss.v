(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMiss.v (commit 3295f3a9fd5, CfInstMiss lane M field round 3 (cf-miss 3295f3a9fd5); file sha256 1c327db94e02) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstMiss.v at commit f7d0d764e77, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   The cf twin of proofs/cgif/cgif_file_fuzzer/lib/AGif1m.v, AGif1mE.v and MnRefillcgif.v at c5 30a1993588f: the miss
   interface, its errno add-on and the memnorm-kept refill field at the call-site relation YGcfInstBase.ARXq_cf, over
   the refill window YGcfInstRefill.REP_STACK: MnRefillW.AIfaceMw / AIfaceMEw / amm_refill_w_t (AGif0n.AIfaceM /
   ErrnoG.AIfaceME / MnRefill.amm_refill_t with their RSTACK = 1024 replaced by the window; the cf refill's class-full
   report writes more than 1024 bytes below the refill's sp, so the RSTACK forms are false at cf).
   rule 24: no function proved (interface-instance discharge at a model relation; no machine walk is written).

   Fixed arguments (YGcfInstBase.v section 4): U := U_cf B, mt := malloc_cf, ARX := ARXq_cf B IOK Hp at every ghost set
   Hp, AOX := AOX_cf B, rpre := rpre_cf B, nmax := cf_malloc_max, lmax := LIVE_MAX, lpost := qtight,
   dpost := YGcfInstHit.dpost_cf B, mtag / stag := CfImg's cf_pc_malloc_max / cf_pc_spin_shadow (malloc_cf's mcheck tag
   and shadow-remap spin, YG00cf.v:237 / :249), rtree := YGcfInstRefill.refill_tree_cf.

   Field by field, against cgif's proof:
   - if_mview (mview_cf): ARmcf's layout / tsd / const cells / cache count cell / unwinding cell (AGif1m.mview_cgif's
     script over acells_cf); the instance's cells from INST_CELLS (CfInstSec's image text) and IOK_inst;
   - if_shape_miss (shape_miss_cf): malloc_cf's primary arm, by the monad laws (YFi3.malloc_primary_eq's script);
   - ifw_refill (refill_cf): from amm_refill_cf, dropping errno and the memnorm keep (MnRefillW);
   - if_post_miss / if_post_miss_k (post_miss_cf / post_miss_k_cf): the AR link of the hit arms at the pop state
     (YGcfInstHit.hit_bridge_g / hit_bridge_k, generic in the pop state and the depot post), Wf_cf and qtight of the
     final state from malloc_cf's contract at the entry state along the granted path (YGcfApath.malloc_cf_apath_post),
     the errbuf mapped (st_final keeps st_secs; with_vm_backing keeps the maps);
   - if_depot_miss (depot_miss_cf): the depot field (named premise HDEP, YGcfInstHit's text) at the pop state; U_cf
     does not read the state;
   - if_oom (oom_cf): ARcf after Allocate's out-of-memory tail by AR_oom_law_cf_ok, PROVED here (the cf twin of
     YFi5.AR_oom: AR_frame_law_ok_cf's script with the agreement relaxed at the OOM byte, which no cell reads, from the
     unit image facts oom_owned_img / oom_const_img); the OOM byte owned by own_area_cf, the unwinding byte by
     own_core_cf;
   - if_stack (stack_cf): AR_stack_law_ok_cf, and the errbuf slot lies apart from the stack (xs_placed_cf);
   - if_view_m / if_owned_m / if_owned_m_k: YGcfInstHit's rpre-free view_cf / owned_cf / owned_cf_k;
   - if_mono_join (mono_join_cf): AGif1m.mono_join_cgif's script for aowned; the errbuf slot is the same (st_final
     keeps st_secs).
   - amm_refill_cf: the unit's refill walk is the named premise HRW : YGcfInstRefill.refill_walk_cf, stated through
     the interface's own premises (ARX and rpre at the entry state S0, at the call-time memory); this file proves ARX
     at the call-time memory and model (ARcf_call_mem_cf, by AR_frame_law_ok_cf; xs_mapped_cf by xs_mapped_cf_wvb),
     qtight / st_cache_inited / blocks_bytes on every path of the refill tree (an ipost walk, refill_tree_cf_post),
     and errno kept (errno is no aowned byte and no errbuf byte at either end, and lies below the stack; the refill's
     window [spZ - REP_STACK, spZ) lies above the stack's base by MnRefillW.win_stk_w at REP_STACK_af).
   - ifaceME_cf: ame_refill_v from the view frame, ame_refill by MnRefillW.amm_refill_w_e, ame_depot_miss by
     YGcfInstHit.ae_depot_cf at the pop state.
   EVENT-FREE: no event counter, event bound, meter or regime appears in this file; the only event term is the tick
   update inside MnRefillW's refill field statements. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLdepot ErrnoG ErrnoApart MemnormT MnRefillW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG02cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0qcf YG0scf YG07cf YGcfApath YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstErrno.
(* the kit's image-window premise IMG_COVER only (never its ARXs_cf instance) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfDIface.
(* the class-free image row EXH_OFF_t (ARmcf's amc_cells_owned carries it) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfImgRows.
(* the cells' footprint family (cell_bytes_in and its range lemmas) and YG0t's fake-stack cells *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0t YG0tcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstRefill YGcfInstHit.
(* field round 3: memnorm at the refill call (MemnormLocG's window keep) and the RELRO frame (YGcfRodata) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormLocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRodata.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YG0dcf.v. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Helpers over any state.                                                                                          *)

(* generalised from AGif1m.v:55-56 (tfibsegs -> im_segs) *)
Lemma apresent_aview_some_cf : forall (H : word -> bool) m a, apresent H m a -> aview im_segs H m a <> None.
Proof. intros H m a Hp. destruct (ImgBase.apresent_mbyte im_segs H m a Hp) as [b Hb]. unfold aview. rewrite Hb. cbn. discriminate. Qed.

(* a byte the segments give is never None in the view *)
Lemma aview_rom_some_cf : forall (H : word -> bool) m a, seg_rom im_segs (Z_to_bv 64 a) <> None -> aview im_segs H m a <> None.
Proof.
intros H m a Hr. unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)); cbn; [discriminate|].
destruct (seg_rom im_segs (Z_to_bv 64 a)); cbn; [discriminate | exfalso; exact (Hr eq_refl)].
Qed.

(* copy of AGif1m.v:77-92: a primary chunk put by upd_chunk adds no section extent *)
Lemma flat_map_upd_prim_cf : forall (g : chunk -> list (Z * Z)) l k,
(forall k' o, ck_beg k' = PPrim o -> g k' = []) -> (exists p, ck_beg k = PPrim p) ->
flat_map g (upd_chunk l k) = flat_map g l.
Proof.
intros g l k Hg [p Hp]. induction l as [|k' t IH]; cbn [upd_chunk].
- cbn [flat_map]. rewrite (Hg k p Hp). reflexivity.
- rewrite Hp. destruct (ck_beg k') as [|o|r o|c q] eqn:Eb; cbn [sptr_eqb]; try (cbn [flat_map]; rewrite IH; reflexivity).
  destruct (o =? p); cbn [flat_map]; [|rewrite IH; reflexivity].
  rewrite (Hg k p Hp), (Hg k' o Eb). reflexivity.
Qed.
Lemma sec_extents_upd_prim_cf : forall ly S S' k, st_chunks S' = upd_chunk (st_chunks S) k -> (exists p, ck_beg k = PPrim p) ->
sec_extents ly S' = sec_extents ly S.
Proof.
intros ly S S' k E Pk. unfold sec_extents. rewrite E. apply flat_map_upd_prim_cf; [|exact Pk].
intros k' o Eo. cbv beta. rewrite Eo. reflexivity.
Qed.

(* copy of YFi3.v:55-65 (the monad laws malloc_cf's shape needs) *)
Lemma bind_assoc_mcf {A B0 C} : forall (m : M A) (f : A -> M B0) (g : B0 -> M C) s,
bind (bind m f) g s = bind m (fun a => bind (f a) g) s.
Proof.
intros m f g s. unfold bind. generalize (m s). clear m. intros t.
induction t as [[a s1] | q snap k IH | pc | e]; cbn; try reflexivity.
f_equal. apply FunctionalExtensionality.functional_extensionality. intros b. apply IH.
Qed.
Lemma bind_cong_mcf {A R} : forall (m : M A) (f g : A -> M R) s, (forall a s', f a s' = g a s') -> bind m f s = bind m g s.
Proof.
intros m f g s H. unfold bind. f_equal. apply FunctionalExtensionality.functional_extensionality. intros [a s']. apply H.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The refill tree keeps the chunks and the quarantine, and leaves the caches inited, on EVERY path: an all-paths    *)
(* walk (YGcfXs.cfx_ipost), YGcfReallocCompose.v's ci_* walk (:84-158) over this relation.                          *)
Definition rq_same (s s' : astate) : Prop :=
st_chunks s' = st_chunks s /\ st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\
st_cache_inited s' = st_cache_inited s /\ st_depot s' = st_depot s.

Create HintDb rqdb.

Ltac rq_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin, rq_same in *).

Ltac rq_cbn :=
cbn [ibind cfx_ipost fst snd st_secs st_chunks st_regions st_cache st_cache_inited st_sec_arr st_sec_reserved
st_qthread st_qglobal st_fs st_depot st_internal_inited set_regions set_cache set_chunks set_secs set_sec_arr
set_sec_reserved set_depot set_cache_inited set_qglobal set_qthread set_internal_inited] in *.

Ltac rq_hint :=
first
[ match goal with |- cfx_ipost (ibind _ _) _ =>
  apply cfx_ipost_ibind; eapply cfx_ipost_mono; [|solve [eauto with rqdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hq" in
  intros [x sx] H1; cbn [fst snd] in H1; unfold rq_same in H1; destruct H1 as (? & ? & ? & ? & ?) end
| match goal with |- cfx_ipost _ _ =>
  eapply cfx_ipost_mono; [|solve [eauto with rqdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hq" in
  intros [x sx] H1; cbn [fst snd] in H1; unfold rq_same in H1; destruct H1 as (? & ? & ? & ? & ?) end ].

Ltac rq_step :=
first
[ progress rq_cbn
| rq_unf
| progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| rq_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x eqn:? end
| exact I
| (repeat split; congruence) ].

(* the tick touches only the event count *)
Lemma rq_tick : forall s, cfx_ipost (tick s) (fun r => rq_same s (snd r)).
Proof. intros s. unfold tick, modify. cbn. repeat split. Qed.
#[local] Hint Resolve rq_tick : rqdb.
Lemma rq_ensure : forall c need sof s, cfx_ipost (ensure_free_array c need sof s) (fun r => rq_same s (snd r)).
Proof. intros c need sof s. unfold ensure_free_array. repeat rq_step. Qed.
#[local] Hint Resolve rq_ensure : rqdb.
Lemma rq_mmu : forall c need s, cfx_ipost (map_more_user c need s) (fun r => rq_same s (snd r)).
Proof. intros c need s. unfold map_more_user. repeat rq_step. Qed.
#[local] Hint Resolve rq_mmu : rqdb.
Lemma rq_populate : forall c need s, cfx_ipost (populate c need s) (fun r => rq_same s (snd r)).
Proof. intros c need s. unfold populate. repeat rq_step. Qed.
#[local] Hint Resolve rq_populate : rqdb.
Lemma rq_set_exh : forall c s, cfx_ipost (set_exh_cf c s) (fun r => rq_same s (snd r)).
Proof. intros c s. unfold set_exh_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_set_exh : rqdb.
Lemma rq_clear_exh : forall c s, cfx_ipost (clear_exh_cf c s) (fun r => rq_same s (snd r)).
Proof. intros c s. unfold clear_exh_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_clear_exh : rqdb.
Lemma rq_errb_set_size : forall ns s, cfx_ipost (errb_set_size ns s) (fun r => rq_same s (snd r)).
Proof. intros ns s. unfold errb_set_size. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_set_size : rqdb.
Lemma rq_errb_retire : forall s, cfx_ipost (errb_retire s) (fun r => rq_same s (snd r)).
Proof. intros s. unfold errb_retire. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_retire : rqdb.
Lemma rq_errb_map : forall w s, cfx_ipost (errb_map_cf w s) (fun r => rq_same s (snd r)).
Proof. intros w s. unfold errb_map_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_map : rqdb.
Lemma rq_errb_append : forall len s, cfx_ipost (errb_append_cf len s) (fun r => rq_same s (snd r)).
Proof. intros len s. unfold errb_append_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_append : rqdb.
Lemma rq_errb_report : forall c s, cfx_ipost (errb_report_cf c s) (fun r => rq_same s (snd r)).
Proof. intros c s. unfold errb_report_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_report : rqdb.
Lemma rq_mmu_cf : forall c need s, cfx_ipost (map_more_user_cf c need s) (fun r => rq_same s (snd r)).
Proof. intros c need s. unfold map_more_user_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_mmu_cf : rqdb.
Lemma rq_populate_cf : forall c need s, cfx_ipost (populate_cf c need s) (fun r => rq_same s (snd r)).
Proof. intros c need s. unfold populate_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_populate_cf : rqdb.
Lemma rq_gfa_cf : forall c n s, cfx_ipost (get_from_allocator_cf c n s) (fun r => rq_same s (snd r)).
Proof. intros c n s. unfold get_from_allocator_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_gfa_cf : rqdb.
Lemma rq_refill_cf : forall c s, cfx_ipost (refill_if_empty_cf c s) (fun r => rq_same s (snd r)).
Proof. intros c s. unfold refill_if_empty_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_refill_cf : rqdb.

(* The refill tree's post on every returning path.  The depot clause: no step of the refill tree puts into the depot
   (refill_tree_cf, YGcfInstRefill.v:62, and its steps YG00cf.v:38-218 and cgif's YG00 steps for the batch class have
   no depot_put / set_depot; the only depot_put of the cf model is malloc_cf's join tail, YG00cf.v:245, after the
   refill, and free_cf's, YG00cf.v:338); this walk checks it on every path. *)
Lemma refill_tree_cf_post : forall c s, cfx_ipost (refill_tree_cf c s) (fun r =>
st_chunks (snd r) = st_chunks s /\ st_qthread (snd r) = st_qthread s /\ st_qglobal (snd r) = st_qglobal s /\
st_cache_inited (snd r) = true /\ st_depot (snd r) = st_depot s).
Proof. intros c s. unfold refill_tree_cf. repeat rq_step. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_shape_miss: malloc_cf's primary arm (YFi3.malloc_primary_eq's script).                                        *)
Lemma shape_miss_cf : forall n tr S, 0 <= n -> from_primary n = true -> pc_chunks (cache S (chunk_class n)) = [] ->
malloc_cf n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) cf_pc_malloc_max ;; refill_tree_cf (chunk_class n) ;;
                    malloc_join_t cf_pc_spin_shadow n tr (chunk_class n)) S.
Proof.
intros n tr S _ FP _.
unfold malloc_cf, malloc_join_t, malloc_K_t, refill_tree_cf, cache_alloc_cf, ImgBaseAG.pop_part. rewrite FP.
apply bind_cong_mcf. intros u1 s1. apply bind_cong_mcf. intros u2 s2. rewrite !bind_assoc_mcf.
apply bind_cong_mcf. intros a s3. cbv beta. rewrite !bind_assoc_mcf.
apply bind_cong_mcf. intros b s4. cbv beta. rewrite !bind_assoc_mcf. reflexivity.
Qed.

(* The cache join's state keeps st_secs and the fake frames, and puts the popped chunk. *)
Lemma st_final_parts_cf : forall S cl l off n tr z,
st_secs (st_final S cl l off n tr z) = st_secs S /\ frames (st_final S cl l off n tr z) = frames S /\
st_chunks (st_final S cl l off n tr z) = upd_chunk (st_chunks S) (new_chunk cl off n).
Proof. intros S cl l off n tr z. cbv [ImgBaseAG.st_final ImgBaseAG.depot_after]. destruct (z =? 0); repeat split; reflexivity. Qed.

Section b.
Variable B : asyms.
(* the unit's instance object (YGcfInstBase's IOK) *)
Variable IOK : Z -> Prop.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The unit's premises.  Each is a fact of the unit's image or of its own walk; none is a model fact of the cf       *)
(* relation.                                                                                                        *)
(* image: the symbol facts of the binary (ImgBase.im_syms) *)
Hypothesis TS : im_syms B.
(* image: the TSD slot, the out-of-memory byte and errno of the symbol table are the image class's cells *)
Hypothesis HTSD : as_tsd B = im_tsd.
Hypothesis HOOM : as_oom_byte B = im_oom.
Hypothesis HERR : as_errno B = im_errno.
(* image: the ledger's image window covers the image (the kit's YGcfDIface.IMG_COVER) *)
Hypothesis HIMG : YGcfDIface.IMG_COVER.
(* the walk's instance object is the symbol table's (YGcfInstBase.IOK_ok) *)
Hypothesis IOK_inst : IOK_ok B IOK.
(* image: the instance object's constant cells wherever the constant cells hold (CfInstSec's INST_CELLS text, carried
   as YGcfInstHit.INST_CELLS_t; cgif: tfib_const_lookup / tfib_const_lookup_sym over Tfib_const) *)
Hypothesis INST_CELLS : INST_CELLS_t B.
(* YGcfInstHit's bridge premises (YGcfInstHit.v:137-152, same texts): the shadow offset, the depot's write zone and
   footprint, and the constant cells apart from the thread cells the hit walk writes *)
Hypothesis HSHB : ag_shadow = SHADOW_OFF.
Hypothesis HDZO : forall ly' a, ag_dzone ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Hypothesis HDZX : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ag_dzone ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Hypothesis HFP : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  CLdepot.depot_footprint B ly' a -> ag_dzone ly' a.
Hypothesis HCW : forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
(* image: errno lies in the image window (ErrnoApart's image fact); UNIT IMAGE obligations (YGcfInstErrno): errno's
   bytes are segment bytes (errno_seg_t; cgif YB13.tfib_rw_rom) and no owned static range holds them
   (errno_nstatic_t; cgif Tfib_owned_static) *)
Hypothesis EII : ErrnoApart.errno_in_img.
Hypothesis HEROM : errno_seg_t B.
Hypothesis HENS : errno_nstatic_t B.
(* image: errno lies apart from the depot's write zone (ErrnoApart's image fact) *)
Hypothesis EDZ : ErrnoApart.errno_apart_dzone_ag.
(* the unit's depot field at the cf relation (YGcfInstHit's HDEP; YGcfInstDepot.if_depot_cf gives it) *)
Hypothesis HDEP : forall Hp, CLdepot.depot_field im_segs ag_depot_put im_tp B (ARXq_cf B IOK Hp) (U_cf B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The out-of-memory law (the cf twin of YFi5.v:371 AR_oom): ARcf survives Allocate's out-of-memory tail, which may  *)
(* change the OOM byte (owned, junk in ARmcf) besides the frame law's memory (YG0dcf.AR_frame_law_cf with the owned *)
(* clause relaxed at im_oom).  PROVED below (AR_oom_law_cf_ok) from ARcf and two UNIT IMAGE facts of the byte.      *)
Definition AR_oom_law_cf : Prop :=
forall ly S Hp (W : world im_segs) mem md mem' md',
ARcf im_segs B ly S Hp W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> im_oom -> aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem a) ->
(forall a, aview im_segs (w_H W) mem a <> None -> aview im_segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
ARcf im_segs B ly S Hp W mem' md'.

(* UNIT IMAGE obligations of the out-of-memory byte: it lies apart from the image-located areas the cells read
   (cgif: YFi5.Z_inst / Z_depot / Z_store / Z_ial / Z_flag), and it is no byte of a constant cell in an owned static
   range at a layout the image's symbol cells may sit at (YGcfInstBase.ly_img_ok: layout_ok, the TSD slot, the owned
   static inside the image window; cgif: YFi5.abs_cells_okJ, by computation over Tfib_const_abs / Tfib_const_shadow).
   The ly_img_ok premise is required: without it the row is false (a Theorem Labs lane's ReplyImg_oomconst.oom_const_t_refuted_A,
   a working branch 0e400063292: at ly_T = the OOM byte a symbol cell of the thread object is it). *)
Definition oom_areas_t : Prop :=
~ (as_inst B <= as_oom_byte B < as_inst B + 3632) /\
~ (as_depot B <= as_oom_byte B < as_depot B + (4 * 2 ^ 20 + 32)) /\
~ (as_store B <= as_oom_byte B < as_store B + 32) /\
~ (as_ialloc_lo B <= as_oom_byte B < as_ialloc_hi B) /\
~ (as_ialloc_flag B <= as_oom_byte B < as_ialloc_flag B + 2).
Definition oom_const_t : Prop :=
forall ly c k, ly_img_ok B ly -> In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
Exists (in_zr (aeval B ly (c_at c) + k)) (as_owned_static B) -> aeval B ly (c_at c) + k <> as_oom_byte B.
Hypothesis oom_owned_img : oom_areas_t.
Hypothesis oom_const_img : oom_const_t.
(* UNIT IMAGE obligation: the OOM byte is not in the errbuf object (the out-of-memory tail keeps the errbuf cells). *)
Hypothesis HOEB : ~ (cf_errbuf_obj <= as_oom_byte B < cf_errbuf_obj + 56).
(* UNIT IMAGE obligation (field round 3): the layer's row pf_cells_apart_t (YG0ncf.v:197): Printf's two writable cells
   are below the store, not the OOM byte and apart from the errbuf object; the out-of-memory tail keeps ARmcf's
   amc_pf_cells by its second conjunct. *)
Hypothesis HPFA : pf_cells_apart_t B.
(* UNIT IMAGE obligation (field round 3, the layer's row relro_seg_t, F1's name HRS): the RELRO range lies in one
   segment of the image; amm_refill_cf carries arodata_ok_cf from the field's entry memory to the refill call. *)
Hypothesis HRS : relro_seg_t im_segs.
(* YGcfInstHit's bridge premise ERRB_AG (same text): the depot's write zone misses the errbuf object (the ag_dzone part
   of YGcfErrbSep.ERRB_SEP_t) *)
Hypothesis ERRB_AG : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
(* YGcfInstHit's round-3 bridge premise PF_AG (same text, CfInstHit's local premise): the depot's write zone misses
   Printf's two writable cells *)
Hypothesis PF_AG : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8).

Definition not_oom_cf (a : Z) : Prop := a <> as_oom_byte B.
Local Notation CBO := (YG0tcf.cell_bytes_in B not_oom_cf).

(* The cells' footprint avoids the OOM byte: YG0tcf.v's _in_cf family (:96-326) at P := not_oom_cf, with fz_img
   (which holds the byte) replaced by the five areas of oom_areas_t and the constant cells by oom_const_t. *)
Section z.
Variables (ly : alayout) (S : astate) (Hp : list Z) (rd : reader).
Hypothesis M : ARmcf B ly S Hp rd.
Local Ltac fcons_o := apply Forall_cons; [cbn; lia|].

Lemma oom_img_cf : in_zr (as_oom_byte B) (ly_img ly).
Proof.
pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amc_syms _ _ _ _ _ M)) (as_oom_byte B, 1)
  ltac:(unfold asyms_areas; cbn; tauto)) as X.
apply Exists_exists in X as (r & Hr & [X1 X2]). cbn [fst snd] in X1, X2.
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [S1 S2].
unfold in_zr. lia.
Qed.
Lemma oom_range_cf : kImgLo <= as_oom_byte B < kImgEnd.
Proof. pose proof oom_img_cf as H. pose proof (lo_img ly (amc_layout _ _ _ _ _ M)) as (L1 & _ & L3 & _). unfold in_zr in H. lia. Qed.
Lemma no_high_cf : forall a, kImgEnd <= a -> not_oom_cf a.
Proof. intros a Ha E. pose proof oom_range_cf. lia. Qed.
Lemma no_offimg_cf : forall a, ~ in_zr a (ly_img ly) -> not_oom_cf a.
Proof. intros a H E. apply H. rewrite E. exact oom_img_cf. Qed.
Lemma no_ext_cf : forall e a, In e (owned_extents ly) -> fst e <= a < fst e + snd e -> not_oom_cf a.
Proof.
intros e a He Ha. apply no_offimg_cf.
destruct (owned_extents_bound ly a (amc_layout _ _ _ _ _ M) ltac:(apply Exists_exists; exists e; split; [exact He | exact Ha]))
  as (_ & _ & NI).
exact NI.
Qed.
Lemma no_core_cf : forall e a, In e (core_extents ly) -> fst e <= a < fst e + snd e -> not_oom_cf a.
Proof. intros e a He Ha. apply (no_ext_cf e a); [|exact Ha]. unfold core_extents in He; unfold owned_extents; cbn in He |- *; tauto. Qed.
Lemma no_prim_cf : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> not_oom_cf a.
Proof. intros a Ha. apply (no_ext_cf (ly_prim ly, kPrimResvSize) a); [unfold owned_extents; cbn; tauto | exact Ha]. Qed.
Lemma no_F_cf : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> not_oom_cf a.
Proof. intros a Ha. apply (no_ext_cf (ly_F ly, kFakeStackSize) a); [unfold owned_extents; cbn; tauto | exact Ha]. Qed.
Lemma no_sec_cf : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> not_oom_cf a.
Proof.
intros e a He Ha. apply no_offimg_cf. pose proof (amc_placed _ _ _ _ _ M) as [_ PD].
assert (HI : In (ly_img ly) (static_extents ly)) by (unfold static_extents; apply in_or_app; right; right; left; reflexivity).
pose proof (cfb_pairwise_app zdisjoint _ _ e (ly_img ly) PD He HI) as D. unfold zdisjoint, in_zr in *. lia.
Qed.
Lemma no_shadow_static_cf : forall r a, In r (as_owned_static B) ->
shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> not_oom_cf a.
Proof.
intros r a Hr Ha. apply no_high_cf.
pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (T1 & _ & _).
pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)). unfold shadow_addr, SHADOW_OFF, kImgEnd in *. lia.
Qed.
Lemma no_inst_cf : forall a, as_inst B <= a < as_inst B + 3632 -> not_oom_cf a.
Proof. intros a Ha E. rewrite E in Ha. exact (proj1 oom_owned_img Ha). Qed.
Lemma no_depot_cf : forall a, as_depot B <= a < as_depot B + (4 * 2 ^ 20 + 32) -> not_oom_cf a.
Proof. intros a Ha E. rewrite E in Ha. exact (proj1 (proj2 oom_owned_img) Ha). Qed.
Lemma no_store_cf : forall a, as_store B <= a < as_store B + 32 -> not_oom_cf a.
Proof. intros a Ha E. rewrite E in Ha. exact (proj1 (proj2 (proj2 oom_owned_img)) Ha). Qed.
Lemma no_ialloc_cf : forall a, as_ialloc_lo B <= a < as_ialloc_hi B -> not_oom_cf a.
Proof. intros a Ha E. rewrite E in Ha. exact (proj1 (proj2 (proj2 (proj2 oom_owned_img))) Ha). Qed.
Lemma no_iflag_cf : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> not_oom_cf a.
Proof. intros a Ha E. rewrite E in Ha. exact (proj2 (proj2 (proj2 (proj2 oom_owned_img))) Ha). Qed.

(* copy of YG0tcf.v:141-172 (rinfo_in_cf / meta_in_cf / batch_in_cf) at not_oom_cf *)
Lemma rinfo_no_cf : forall a, ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> not_oom_cf a.
Proof.
intros a Ha. pose proof (lo_space_in _ (amc_layout _ _ _ _ _ M)) as [S1 S2]. unfold kRegionInfoOff, kSpaceSize in *.
apply no_prim_cf. lia.
Qed.
Lemma meta_no_cf : forall k a, In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> not_oom_cf a.
Proof.
intros k a Hk Ha. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
  pose proof (region_in_prim ly (prim_class o) (amc_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
  apply no_prim_cf. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  apply (no_sec_cf (ly_sec ly r, sec_map_size (ck_req k)) a Gin). cbn [fst snd]. unfold kPage in *. lia.
Qed.
Lemma batch_no_cf : forall b a, In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> not_oom_cf a.
Proof.
intros b a Hb Ha. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
unfold kBatchBytes, kFreeArrayOffset in *.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
apply no_prim_cf. lia.
Qed.

(* copy of YG0tcf.v:174-326 (the cell families) at not_oom_cf *)
Lemma region_cells_no_cf : forall c, 1 <= c <= 31 -> Forall (CBO ly) (region_cells S c).
Proof.
intros c Hc. apply (YG0tcf.Forall_cbi_of_range B not_oom_cf ly _ (ly_space ly + kRegionInfoOff) 4096); [exact rinfo_no_cf|].
unfold region_cells, kRegionInfoOff. repeat fcons_o. apply Forall_nil.
Qed.
Lemma cache_cells_no_cf : forall c, 1 <= c <= 31 -> Forall (CBO ly) (cache_cells S c).
Proof.
intros c Hc.
assert (OR : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> not_oom_cf a).
{ intros a Ha. apply (no_core_cf (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]. }
apply (YG0tcf.Forall_cbi_of_range B not_oom_cf ly _ (ly_T ly) kThreadObjSize OR).
pose proof (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC.
pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
- destruct WC as [PM PL]. repeat fcons_o. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv).
  cbn [fst snd c_at c_w z4 c4 aeval aoff]. apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- repeat fcons_o. apply Forall_nil.
Qed.
Lemma chunk_cells_no_cf : forall k, In k (st_chunks S) -> Forall (CBO ly) (chunk_cells k).
Proof.
intros k Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (OR : forall a, ck_base B ly k <= a < ck_base B ly k + ck_rz k -> not_oom_cf a).
{ intros a Ha. eapply meta_no_cf; [exact Hk |]. destruct (ck_beg k); unfold kPage; lia. }
apply (YG0tcf.Forall_cbi_of_range B not_oom_cf ly _ _ _ OR).
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
- repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
  apply Forall_nil.
- destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
  assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
  repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
  apply Forall_nil.
Qed.
Lemma sec_cells_no_cf : Forall (CBO ly) (sec_cells S).
Proof.
pose proof (wfc_secondary _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as X. destruct X as [Snd Sac Sal Sres Sral].
unfold sec_cells.
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_inst_cf | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_inst_cf | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_inst_cf | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  eapply YG0tcf.cbi_of_range;
    [intros a Ha; apply (no_core_cf (ly_Q ly, kPtrArrayResv)); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia |].
  cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
  pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
  destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  assert (OR : forall a, ly_sec ly r <= a < ly_sec ly r + kPage -> not_oom_cf a).
  { intros a Ha. eapply meta_no_cf; [exact Hk |]. rewrite Eb. unfold kPage in *. lia. }
  unfold kPage in OR.
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply YG0tcf.cbi_of_range; [exact OR | cbn; lia | cbn; lia]).
Qed.
Lemma batch_cells_no_cf : forall l, incl l (all_batches S) -> Forall (CBO ly) (batch_cells l).
Proof.
induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfc_quarantine _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OR : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> not_oom_cf a)
  by (intros a Ha; eapply batch_no_cf; [apply Hincl; left; reflexivity | exact Ha]).
unfold kBatchBytes in OR.
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
  eapply YG0tcf.cbi_of_range; [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.
Lemma quar_cells_no_cf : Forall (CBO ly) (quar_cells S).
Proof.
assert (ORT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> not_oom_cf a).
{ intros a Ha. apply (no_core_cf (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]. }
unfold kThreadObjSize in ORT.
unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_inst_cf | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_inst_cf | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact ORT | cbn; lia | cbn; lia]|]).
  apply batch_cells_no_cf. intros b Hb. unfold all_batches. apply in_app_iff. left. exact Hb.
- do 4 (apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_inst_cf | cbn; lia | cbn; lia]|]).
  apply batch_cells_no_cf. intros b Hb. unfold all_batches. apply in_app_iff. right. exact Hb.
Qed.
Lemma fs_hdr_no_cf : Forall (CBO ly) YG0t.fs_hdr.
Proof.
assert (OR : forall a, ly_F ly + 88 <= a < ly_F ly + 88 + (kFakeFlagsOff - 88) -> not_oom_cf a)
  by (intros a Ha; apply no_F_cf; unfold kFakeFlagsOff, kFakeStackSize in *; lia).
unfold kFakeFlagsOff in OR. unfold YG0t.fs_hdr.
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact OR | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma depot_cells_no_cf : Forall (CBO ly) (depot_cells ly S).
Proof.
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_depot_cf | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_depot_cf | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_store_cf | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_store_cf | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma ialloc_cells_no_cf : Forall (CBO ly) (ialloc_cells B S).
Proof.
pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ M)) as [I1 I2].
assert (ORA : forall a, as_ialloc_lo B <= a < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B) -> not_oom_cf a)
  by (intros a Ha; apply no_ialloc_cf; lia).
unfold ialloc_cells.
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_iflag_cf | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact no_iflag_cf | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact ORA | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply YG0tcf.cbi_of_range; [exact ORA | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma thread_cells_no_cf : Forall (CBO ly) thread_cells.
Proof.
unfold thread_cells, t_unwinding. apply Forall_cons; [|apply Forall_nil].
eapply YG0tcf.cbi_of_range;
  [intros a Ha; apply (no_core_cf (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]
  | cbn; lia | cbn; unfold kThreadObjSize; lia].
Qed.
Lemma const_cells_no_cf : Forall (CBO ly) (as_const B ly).
Proof.
apply Forall_forall. intros c Hin k Hk.
destruct (proj1 (Forall_forall _ _) (amc_const_owned _ _ _ _ _ M) c Hin k Hk) as [O|[O|O]].
- exact (oom_const_img ly c k (ly_img_ok_of_ARmcf B ly S Hp rd M) Hin Hk O).
- apply Exists_exists in O as (e & He & Hie). exact (no_core_cf e _ He Hie).
- apply Exists_exists in O as (r & Hr & Hir). exact (no_shadow_static_cf r _ Hr Hir).
Qed.
Lemma acells_no_cf : Forall (CBO ly) (acells_cf B ly S).
Proof.
unfold acells_cf. rewrite (YG0t.fs_cells_split S).
assert (RCF : forall c, In c (zseq 1 31) -> Forall (CBO ly) (region_cells_cf S c)).
{ intros c Hc. apply Forall_forall. intros x Hx.
  apply (proj1 (Forall_forall _ _) (region_cells_no_cf c ltac:(pose proof (YG0t.zseq_In' 1 31 c Hc); lia))).
  eapply region_cells_cf_incl. exact Hx. }
apply Forall_app; split; [exact (YG0t.Forall_flat_map'' _ _ _ RCF)|].
apply Forall_app; split;
  [exact (YG0t.Forall_flat_map'' _ _ _ (fun c Hc => cache_cells_no_cf c ltac:(pose proof (YG0t.zseq_In' 1 31 c Hc); lia)))|].
apply Forall_app; split; [exact (YG0t.Forall_flat_map'' _ _ _ (fun k Hk => chunk_cells_no_cf k Hk))|].
apply Forall_app; split; [exact sec_cells_no_cf|].
apply Forall_app; split; [exact quar_cells_no_cf|].
apply Forall_app; split.
{ apply Forall_app; split; [exact fs_hdr_no_cf|]. unfold YG0t.fs_hints. apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
  eapply YG0tcf.cbi_of_range;
    [exact (fun a (Ha : ly_F ly <= a < ly_F ly + 88) => no_F_cf a ltac:(unfold kFakeStackSize; lia))
    | cbn; lia | cbn [c_at c_w z8 c8 aeval aoff fst snd]; cbn; lia]. }
apply Forall_app; split; [exact depot_cells_no_cf|].
apply Forall_app; split; [exact ialloc_cells_no_cf|].
exact thread_cells_no_cf.
Qed.

(* a shadow byte the model reads lies at or above SHADOW_OFF (ashadow is defined only on non-negative granules) *)
Lemma ashadow_pos_cf : forall g v, ashadow B ly S g = Some v -> 0 <= g.
Proof.
intros g v H. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_high _ LO) as [HH _].
pose proof (amc_placed _ _ _ _ _ M) as [PL _].
unfold ashadow in H. destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg].
  destruct (extent_zone_cf B ly S Hp rd k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
  + unfold kHighMemBeg in HH. lia.
  + pose proof (proj1 (Forall_forall _ _) PL (m, len) Hin) as (_ & A & _). unfold in_app in A. cbn [fst snd] in A.
    unfold kPage in X1. YM03.lf_lia_orig.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
  apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
  + apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
    pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & _ & _ & R4 & _).
    unfold fa_base, region_base in *. unfold kHighMemBeg, kFreeArrayOffset in *.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
  + pose proof (proj1 (Forall_forall _ _) PL (lo, len) Hin) as (_ & A & _). unfold in_app in A. cbn [fst snd] in A. lia.
Qed.
End z.

(* The law. AR_frame_law_ok_cf's proof (YG0qcf.v:669) with its owned-agreement AG at the bytes other than the OOM byte:
   every byte the cells, the free arrays, the flags, the depot, the shadow and the internal allocator's zero ranges
   read is not the OOM byte (the _no_cf family above). *)
Lemma AR_oom_law_cf_ok : AR_oom_law_cf.
Proof.
intros ly S Hp W mem md mem' md' (M & L & BUD & MW & HS) AGR VIS Hvm Hlz He HK.
set (rd := aview im_segs (w_H W) mem) in *. set (rd' := aview im_segs (w_H W) mem') in *.
assert (AGo : forall a, aowned B ly S a -> not_oom_cf a -> rd' a = rd a).
{ intros a Ha Hn. apply AGR; [| exact Ha | rewrite <- HOOM; exact Hn].
  pose proof (AR_owned_low_law_ok_cf im_segs B ly S Hp W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha).
  pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR. lia. }
pose proof (oom_range_cf ly S Hp rd M) as OR0.
assert (NH : forall a, kImgEnd <= a -> not_oom_cf a) by (intros a Ha E; lia).
split; [|split; [eapply ALedger_same_cf; eassumption | split; [exact BUD | split; [exact (amwf_same md md' Hvm Hlz MW)|]]]].
{ pose proof M as M0.
  destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero
    Xtsd Ximg Xhp Xxs Xexh Xerrb [HEXO [HEO HEIA]] Xpf Xpo].
  constructor; try assumption; try exact (conj HEXO (conj HEO HEIA)).
  - eapply YG0tcf.Forall_cell_holds_agree_in;
      [exact AGo | eapply const_cells_owned_cf; exact M0 | exact (const_cells_no_cf ly S Hp rd M0) | assumption].
  - eapply YG0tcf.Forall_cell_holds_agree_in;
      [exact AGo | eapply acells_owned_cf; exact M0 | exact (acells_no_cf ly S Hp rd M0) | assumption].
  - intros c i v Hc Hi Hv k Hk.
    pose proof (wfc_classes _ _ _ _ _ Xwf c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
    pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
    pose proof (region_in_prim ly c Xlay Hc) as (_ & _ & _ & R4 & _).
    rewrite AGo; [exact (Xfa c i v Hc Hi Hv k Hk) | eapply own_fa_cf; [exact M0 | exact Hc | lia] |].
    apply NH. unfold fa_base. unfold region_base in R4. unfold kHighMemBeg, kImgEnd, kFreeArrayOffset in *. lia.
  - intros cid pos Hc Hpos. pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
    rewrite AGo; [exact (Xflags cid pos Hc Hpos) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low_cf; [exact M0 | lia] |].
    apply (no_F_cf ly S Hp rd M0). unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
  - destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
    + intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk.
      rewrite AGo; [exact (H2 k Hk)
        | eapply own_area_cf with (r := (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia]
        | apply no_depot_cf; unfold d_tab_words in Hb; lia].
    + intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
      assert (NB : depot_ids S <= 4097).
      { unfold depot_ids. pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)) as DL. unfold DEPOT_MAX in DL. lia. }
      assert (OR : forall k, 0 <= k < 16 -> aowned B ly S (ly_NB ly + 16 * id + k) /\ not_oom_cf (ly_NB ly + 16 * id + k)).
      { intros k Hk. split.
        - eapply own_core_cf with (e := (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia].
        - apply (no_core_cf ly S Hp rd M0 (ly_NB ly, kNodesBlockSize)); [unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
      split; intros k Hk.
      * destruct (OR (Z.of_nat k) ltac:(lia)) as [O1 O2]. rewrite AGo; [exact (H2 k Hk) | exact O1 | exact O2].
      * replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia.
        destruct (OR (8 + Z.of_nat k) ltac:(lia)) as [O1 O2]. rewrite AGo; [|exact O1 | exact O2].
        replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia. exact (H3 k Hk).
  - intros g v Hg Hv0. pose proof (ashadow_pos_cf ly S Hp rd M0 g v Hv0) as G0.
    rewrite AGo; [exact (Xshadow g v Hg Hv0) | eapply ashadow_owned_cf; [exact M0 | exact Hv0] |].
    apply NH. pose proof (Z.div_pos g 8 ltac:(lia) ltac:(lia)). unfold shadow_addr, SHADOW_OFF, kImgEnd in *. lia.
  - unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. fold (shadow_addr (fst r)).
    change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
    assert (R0 : 0 <= fst r).
    { unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst].
      - pose proof (lo_top ly Xlay) as (_ & _ & _ & _ & _ & _ & K1). unfold kHighMemBeg in K1. lia.
      - pose proof (proj1 (Forall_forall _ _) Ximg r ltac:(apply in_app_iff; right; exact Hr)) as [Z1 _].
        pose proof (lo_img ly Xlay) as (I0 & _). unfold kImgLo in I0. lia. }
    rewrite AGo; [exact (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) | eapply own_shadow_zero_cf; [exact M0 | exact Hr | exact Hi] |].
    apply NH. pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)). unfold shadow_addr, SHADOW_OFF, kImgEnd in *. lia.
  - eapply Forall_range_vis_keep; [exact VIS | assumption].
  - eapply Forall_range_vis_keep; [exact VIS | assumption].
  - eapply Forall_range_vis_keep; [exact VIS | assumption].
  - apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
    assert (IR : as_ialloc_lo B <= aeval B ly (fst r) + i < as_ialloc_hi B)
      by (unfold ialloc_zero in Hr; destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia).
    rewrite AGo; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)
      | eapply own_area_cf with (r := (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia]
      | exact (no_ialloc_cf _ IR)].
  - (* amc_exh_cell: the exhausted bytes are owned RegionInfo bytes, none the OOM byte (YG0qcf.exh_cell_move_cf) *)
    apply (exh_cell_move_cf B ly S S Hp rd rd' not_oom_cf M0 HEXO (fun _ => eq_refl) AGo); [|exact Xexh].
    intros c Hc. exact (rinfo_no_cf ly S Hp rd M0 _ (proj1 (exh_byte_where_cf B ly S Hp rd c M0 HEXO Hc))).
  - (* amc_errb_cells: the errbuf object's bytes are owned static bytes, none the OOM byte (HOEB) *)
    apply (errb_cells_move_cf B ly S S Hp rd rd' not_oom_cf M0 HEO eq_refl eq_refl eq_refl eq_refl AGo VIS);
      [|exact Xerrb].
    intros a Ha E. apply HOEB. rewrite <- E. exact Ha.
  - (* amc_pf_cells: Printf's two cells are owned static bytes, neither the OOM byte (pf_cells_apart_t) *)
    apply (pf_cells_move_cf B ly S Hp rd rd' not_oom_cf M0 Xpo AGo); [|exact Xpf].
    intros a Ha E. exact (proj1 (proj2 (HPFA a Ha)) E). }
exact (ahs_transfer_cf im_segs B ly S Hp S (w_H W) mem mem' (al_img_env_cf im_segs ly S md (amc_layout _ _ _ _ _ M) L) M HS VIS
  ltac:(intros a Ha Hh; exact (HK a Ha Hh)) ltac:(intros a _ C; exact C) eq_refl
  ltac:(intros g Hg HA HF _; apply AGo;
    [eapply hfree_shadow_owned_cf; [exact M | exact Hg | exact HA | exact HF]
    | apply NH; destruct HA as [HA _]; pose proof (Z.div_pos g 8 ltac:(lia) ltac:(lia));
      unfold shadow_addr, SHADOW_OFF, kImgEnd in *; lia])).
Qed.

(* The unit's refill walk (cgif: CLrefillR.tfib_refill_okR / MnRefillR.tfib_refill_okR_em): YGcfInstRefill's
   refill_walk_cf, stated through the interface's own premises (ARX and rpre at the ENTRY state S0, at the call-time
   memory and model, and AIfaceM's if_refill registers and stack).  The model facts of the result (qtight, the caches
   inited, the blocks) and errno are this file's. *)
Hypothesis HRW : refill_walk_cf B IOK.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* errno at the cf relation.                                                                                        *)
Lemma errno_range_cf : forall ly S md, layout_ok ly -> ALedger_cf im_segs ly S md -> kImgLo <= as_errno B /\ as_errno B + 4 <= kImgEnd.
Proof.
intros ly S md LY L. destruct (EII B ly TS (HIMG ly S md L)) as [E1 E2].
pose proof (lo_img ly LY) as (L1 & _ & L3 & _). lia.
Qed.

(* errno lies outside every set rleaf's frames exclude (AGif1mE.errno_apart_rleaf_cgif at ARcf): the owned sets at the
   call and at the return, and a stack window above the stack's base. *)
Lemma errno_apart_rleaf_cf : forall ly S Hp W mem md ly' S' Hp' W' mem' md' (lo hi : Z) a,
ARcf im_segs B ly S Hp W mem md -> ARcf im_segs B ly' S' Hp' W' mem' md' -> ly_stk_lo ly <= lo ->
as_errno B <= a < as_errno B + 4 ->
0 <= a < 2 ^ 64 /\ ~ AOX_cf B ly S a /\ ~ AOX_cf B ly' S' a /\ ~ (lo <= a < hi).
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' lo hi a HAR HAR' HLO Ha.
pose proof HAR as (M & L & _). pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (HIMG ly S md L) as IMG.
destruct (errno_range_cf ly S md LY L) as [E1 E2].
split; [unfold kImgLo, kImgEnd in *; lia|].
split; [intros [O|O]; [exact (errno_not_owned_cf B TS EII HIMG HEROM HENS ly S Hp W mem md a HAR Ha O)
                     | exact (errno_not_xs_cf B TS EII HIMG ly S Hp W mem md a HAR Ha O)]|].
split; [intros [O|O]; [exact (errno_not_owned_cf B TS EII HIMG HEROM HENS ly' S' Hp' W' mem' md' a HAR' Ha O)
                     | exact (errno_not_xs_cf B TS EII HIMG ly' S' Hp' W' mem' md' a HAR' Ha O)]|].
intros Hs. exact (ErrnoApart.errno_apart_stack EII B ly lo hi a TS LY IMG HLO Hs Ha).
Qed.

(* errno kept by a raw frame of rleaf's shape. *)
Lemma errno_kept_frame_cf : forall ly S Hp W mem md ly' S' Hp' W' mem' md' (lo hi : Z) (m m' : word -> option byte),
ARcf im_segs B ly S Hp W mem md -> ARcf im_segs B ly' S' Hp' W' mem' md' -> ly_stk_lo ly <= lo ->
(forall x : word, ~ AOX_cf B ly S (bv_unsigned x) -> ~ AOX_cf B ly' S' (bv_unsigned x) -> ~ (lo <= bv_unsigned x < hi) ->
   m' x = m x) ->
ErrnoG.errno_kept B m m'.
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' lo hi m m' HAR HAR' HLO FR i Hi.
destruct (errno_apart_rleaf_cf ly S Hp W mem md ly' S' Hp' W' mem' md' lo hi (as_errno B + i) HAR HAR' HLO ltac:(lia))
  as (Ra & N0 & N1 & NS).
unfold YG0d.w64, YG0n.w64 in *.
apply FR; rewrite (unsigned_lit_small (as_errno B + i) Ra); assumption.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_mview: the miss seed's cells (AGif1m.mview_cgif's script over ARmcf).                                        *)
Lemma mview_cf : forall Hp inst ly S W mem md n,
ARXq_cf B IOK Hp inst ly S W mem md -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S (chunk_class n)) = [] -> mview B W ly inst mem (chunk_class n).
Proof.
intros Hp inst ly S W mem md n [[I [HAR _]] _] Hn0 FP Hc.
pose proof HAR as (M & L & _).
pose proof (primary_geometry n Hn0 FP) as (Gc & _).
pose proof (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M)) as AC.
constructor.
- exact (amc_layout _ _ _ _ _ M).
- exact (HIMG ly S md L).
- rewrite (amc_tsd _ _ _ _ _ M). exact HTSD.
- exact (amc_const _ _ _ _ _ M).
- exact (inst_cells_cf B IOK IOK_inst INST_CELLS Hp inst ly S W mem md I HAR).
- assert (E : Pv ly (chunk_class n) = aeval B ly (AT (t_cache + 80 * chunk_class n))) by (cbn; unfold Pv; lia).
  rewrite E. refine (ImgBase.cell_holds_val_mem im_segs B ly (w_H W) mem (AT (t_cache + 80 * chunk_class n)) 4 (ANum 0) _).
  apply AC. unfold acells_cf. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists (chunk_class n).
  split; [apply YG0s.In_zseq; lia|]. unfold cache_cells. rewrite Hc. destruct (st_cache_inited S); left; reflexivity.
- refine (ImgBase.cell_holds_val_mem im_segs B ly (w_H W) mem (AT t_unwinding) 1 (ANum 0) _).
  apply AC. unfold acells_cf. do 8 (apply in_or_app; right). left. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The refill: the call-time memory keeps every visible byte visible (Allocate's window is present at the call). *)
Lemma vis_call_cf : forall (W : world im_segs) (mem0 mem : word -> option byte) (sp0 : Z),
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
forall a, aview im_segs (w_H W) mem0 a <> None -> aview im_segs (w_H W) mem a <> None.
Proof.
intros W mem0 mem sp0 AG1 PRES1 a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (AV : forall m, aview im_segs (w_H W) m a = aview im_segs (w_H W) m a')
  by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
destruct (Z_lt_le_dec a' (sp0 - AFSTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a' sp0) as [H2|H2]].
2:{ apply apresent_aview_some_cf. apply PRES1. lia. }
all: rewrite (AG1 a' Ha' ltac:(lia)); exact Hv.
Qed.

(* The refill: ARcf at the call-time memory (YFim.AR1 / AGif1m.refill_cgif's first step at ARcf).                  *)
Lemma ARcf_call_mem_cf : forall Hp ly S0 W mem0 md0 (sp0 : Z) (mem : word -> option byte) (mat : list word),
ARcf im_segs B ly S0 Hp W mem0 md0 ->
ly_stk_lo ly + AFSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
ARcf im_segs B ly S0 Hp W mem (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
intros Hp ly S0 W mem0 md0 sp0 mem mat HAR Hlo Hhi AG1 RAW1 PRES1.
pose proof HAR as (M & _). pose proof (amc_layout _ _ _ _ _ M) as LY.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & K1).
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as TA.
cbn [fst snd] in TA.
apply (AR_frame_law_ok_cf im_segs B ly S0 Hp W mem0 md0 mem _ HAR).
- intros a Ha Ho. apply AG1; [exact Ha|]. intros Hst.
  apply (AR_stack_law_ok_cf im_segs B ly S0 Hp W mem0 md0 a HAR); [unfold AFSTACK in *; lia | exact Ho].
- exact (vis_call_cf W mem0 mem sp0 AG1 PRES1).
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx.
  assert (Ha' : 0 <= a < 2 ^ 64)
    by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
  assert (HB : kLowShadowBeg <= a < kHighMemBeg)
    by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
  unfold YG0d.w64, YG0n.w64 in *. apply RAW1; rewrite unsigned_lit_small by exact Ha'.
  + clear - HB K1 Hlo. unfold kHighMemBeg, AFSTACK in *. lia.
  + clear - HB TA. unfold in_app, t_unwinding, kThreadObjSize, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* REP_STACK (YGcfInstRefill) lies in Allocate's window below the refill's sp: 176 + REP_STACK <= AFSTACK. *)
Lemma REP_STACK_af : 0 <= REP_STACK /\ 176 + REP_STACK <= AFSTACK.
Proof. pose proof REP_STACK_le. unfold AFSTACK. lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Field round 3: the refill walk takes memnorm, arodata_ok_cf and cf_hull_ok at the CALL; the field gives the first  *)
(* two at its ENTRY memory mem0, and the call memory equals mem0 outside Allocate's stack window and the thread's     *)
(* unwinding byte (RAW1).  Neither of those two areas holds a segment byte (segments lie in ly_img, ALedger_cf's      *)
(* alc_img; the stack and the thread object are apart from ly_img, lo_disj) or a non-owned RELRO byte.               *)

(* a segment byte lies in the layout's image window *)
Lemma seg_byte_img_cf : forall ly S Hp W mem md (x : word) sg, ARcf im_segs B ly S Hp W mem md ->
  find_segment im_segs (bv_unsigned x) 1 = Some sg -> in_zr (bv_unsigned x) (ly_img ly).
Proof.
intros ly S Hp W mem md x sg (_ & L & _) F. destruct (find_segment_some_spec im_segs (bv_unsigned x) 1 sg F) as (Hin & Hb & Ht).
destruct (alc_img _ _ _ _ L sg Hin) as [I1 I2]. unfold in_zr. lia.
Qed.

(* the thread object is apart from the image window *)
Lemma thread_img_apart_cf : forall ly, layout_ok ly -> forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> ~ in_zr a (ly_img ly).
Proof.
intros ly LO a Ha Hin.
pose proof (cfb_pairwise_app zdisjoint (owned_extents ly) [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly]
  (ly_T ly, kThreadObjSize) (ly_img ly) (lo_disj _ LO) ltac:(unfold owned_extents; cbn; tauto) ltac:(right; left; reflexivity))
  as D.
unfold zdisjoint, in_zr in *. cbn [fst snd] in D. lia.
Qed.

Lemma arodata_call_cf : forall ly S Hp W mem0 md0 (sp0 : Z) (mem : word -> option byte),
  ARcf im_segs B ly S Hp W mem0 md0 -> ly_stk_lo ly + AFSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
  (forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
     mem x = mem0 x) ->
  arodata_ok_cf im_segs B mem0 -> arodata_ok_cf im_segs B mem.
Proof.
intros ly S Hp W mem0 md0 sp0 mem HAR Hlo Hhi RAW1.
pose proof HAR as (M & _). pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (lo_top ly LO) as (_ & _ & _ & T4 & _ & _ & T7).
apply (arodata_frame_cf im_segs B
  (fun a => (sp0 - AFSTACK <= a < sp0) \/ (ly_T ly + t_unwinding <= a < ly_T ly + t_unwinding + 1)) mem0 mem).
- intros x Hx. apply RAW1; intros H; apply Hx; [left | right]; exact H.
- intros a Ha NO. destruct (relro_apart_cf im_segs B ly S Hp W mem0 md0 a HAR HRS Ha NO) as (R & I & NA & _).
  split; [unfold kImgLo, kImgEnd in R; lia|]. intros [X|X].
  + unfold AFSTACK, kHighMemBeg, kImgEnd in *. lia.
  + exact (thread_img_apart_cf ly LO a ltac:(unfold t_unwinding, kThreadObjSize in *; lia) I).
Qed.

(* the driver's hull admission at the entry state: rpre_cfr's last conjunct (field round 3) *)
Lemma rpre_hull_cf : forall S n, rpre_cf B S n -> cf_hull_ok S.
Proof. intros S n (_ & _ & _ & HO). exact HO. Qed.

(* amm_refill_cf: the refill callee with errno and memnorm kept (MnRefillcgif.amm_refill_cgif at the cf relation, over
   the refill window REP_STACK: MnRefillW.amm_refill_w_t), from the unit's refill walk at the call-time memory; part 3c:
   the call-state facts are arodata_ok_cf (carried to the call memory by arodata_call_cf) and the hull admission. *)
Lemma amm_refill_cf : forall Hp,
MnRefillW.amm_refill_w_t B (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) qtight refill_tree_cf REP_STACK.
Proof.
intros Hp inst ly S0 W mem0 md0 n sp0 regs mem mat [[I [HAR0 XM0]] HQ] HR HRO0 Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1
  RAW1 PRES1 SP R1 R3 R4 R10 R11 R12 R13.
pose proof (ARcf_call_mem_cf Hp ly S0 W mem0 md0 sp0 mem mat HAR0 Hlo Hhi AG1 RAW1 PRES1) as HARc.
pose proof (xs_mapped_cf_wvb ly S0 md0 (m_vm_lazy md0) mat XM0) as XMc.
pose proof (MnRefillW.win_stk_w REP_STACK REP_STACK_af ly sp0 regs Hlo SP) as HSP.
pose proof (HRW Hp inst ly S0 W mem (with_vm_backing (m_vm_lazy md0) mat md0) n sp0 regs
  (conj (conj I (conj HARc XMc)) HQ) HR Hn0 FP Hmiss
  (arodata_call_cf ly S0 Hp W mem0 md0 sp0 mem HAR0 Hlo Hhi RAW1 HRO0) (rpre_hull_cf S0 n HR)
  Hlo Hbot Hhi Hal PRES1 SP R1 R3 R4 R10 R11 R12 R13) as RR.
pose proof (amreal_apath_gflag im_segs _ W _ _ RR) as RR2.
eapply amreal_mono; [|exact RR2].
intros r W' c' [(ly' & regs' & mem' & md' & Ec & HAR' & XM' & _ & _ & LLE & WLE & RP & IO & FRV & FRR & MNK & PR & A0)
  (trc & HP & _)].
destruct (cfx_ipost_apath _ _ trc r (refill_tree_cf_post (chunk_class n) _) HP) as (Rck & Rqt & Rqg & CI & Rdp).
assert (QT' : qtight (snd r)) by exact (qtight_ext _ (snd r) Rck Rqt Rqg HQ).
unfold MnRefillW.rleaf_em_w. exists ly', regs', mem', md'.
split; [exact Ec|].
split; [exact (conj (conj I (conj HAR' XM')) QT')|].
split; [exact QT'|].
split; [exact CI|].
split; [unfold blocks_bytes; rewrite Rck; reflexivity|].
(* the refill keeps the depot (refill_tree_cf_post's depot clause; the tick does not touch it) *)
split; [rewrite Rdp; reflexivity|].
split; [exact LLE|]. split; [exact WLE|]. split; [exact RP|]. split; [exact IO|]. split; [exact FRV|]. split; [exact FRR|].
split; [exact (errno_kept_frame_cf ly S0 Hp W mem0 md0 ly' (snd r) Hp W' mem' md' _ (spZ regs) mem mem' HAR0 HAR' HSP FRR)|].
split; [exact MNK|]. split; [exact PR | exact A0].
Qed.

(* if_refill (over REP_STACK): amm_refill_cf, dropping errno and the memnorm keep. *)
Lemma refill_cf : forall Hp, MnRefillW.refill_w_t B (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) qtight refill_tree_cf REP_STACK.
Proof. intros Hp. exact (MnRefillW.ame_refill_w_refill _ _ _ _ _ _ _ (MnRefillW.amm_refill_w_e _ _ _ _ _ _ _ (amm_refill_cf Hp))). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_post_miss: ARcf of the final state from the hit walk's post at the pop state Sp (YGcfInstHit.hit_bridge_g, the  *)
(* cf AGj1.AR_final, generic in the pop state); Wf_cf and qtight of the final state from malloc_cf's contract at the  *)
(* entry state S0 along the path (YGcfApath.malloc_cf_apath_post; AGif1m.post_miss_cgif); the errbuf mapped: st_final *)
(* keeps st_secs and the model's maps (with_vm_backing).  The entry ARX is read for qtight only.                       *)
Lemma post_miss_cf : forall Hp inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z
(regs' : bvmap 5 word) mem' mat,
ARXq_cf B IOK Hp inst ly0 S0 W0 mem00 md00 -> rpre_cf B S0 n -> blocks_bytes S0 + n <= LIVE_MAX ->
ARXq_cf B IOK Hp inst ly Sp W mem0 md0 -> n < cf_malloc_max -> blocks_bytes Sp + n <= LIVE_MAX -> U_cf B tr S0 ->
49 <= n <= 64512 -> st_cache_inited Sp = true -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
val_mem im_segs (mrestrict (w_H W) mem0) (Kv ly (chunk_class n) (off / 16) + RZ (rz_log n) - 15) 1 jb ->
at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
  (fun z m => dpost_cf B inst ly Sp W tr z m) odd z W
  (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> n mod 8 <> 0) ->
(exists trc, apath (malloc_cf n tr S0) trc (ck_user (new_chunk (chunk_class n) off n), st_final Sp (chunk_class n) l off n tr z) /\
  gflag trc = true) ->
ARXq_cf B IOK Hp inst ly (st_final Sp (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
qtight (st_final Sp (chunk_class n) l off n tr z).
Proof.
intros Hp inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat
  [_ HQ0] (HU & HW & (HS & HE & HB) & _) Hlive0 [[I [HARp XMp]] _] Hmax _ Htr Nr Hinited Hcache WFR Hjb _ HRET Hodd
  [trc [HP _]].
pose proof (malloc_cf_apath_post (as_universe B) S0 n tr trc _ HU HW ltac:(lia) Hlive0 Htr HS HE HB HP) as MP.
unfold malloc_post_cf in MP. cbv beta iota in MP. destruct MP as (WF' & _ & _ & _ & _ & QT). pose proof (QT HQ0) as QT'.
split; [|exact QT']. split; [split; [exact I | split] | exact QT'].
- eapply (hit_bridge_g B) with (DPOST := fun z0 m => dpost_cf B inst ly Sp W tr z0 m); try eassumption.
  intros z0 m H. exact (proj2 H).
- apply xs_mapped_cf_wvb. intros e He.
  rewrite (xs_cf_secs ly Sp _ (proj1 (st_final_parts_cf Sp (chunk_class n) l off n tr z))) in He. exact (XMp e He).
Qed.

(* if_post_miss_k: the k twin (0 <= n <= 48), over YGcfInstHit.hit_bridge_k. *)
Lemma post_miss_k_cf : forall Hp inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z
(regs' : bvmap 5 word) mem' mat,
ARXq_cf B IOK Hp inst ly0 S0 W0 mem00 md00 -> rpre_cf B S0 n -> blocks_bytes S0 + n <= LIVE_MAX ->
ARXq_cf B IOK Hp inst ly Sp W mem0 md0 -> n < cf_malloc_max -> blocks_bytes Sp + n <= LIVE_MAX -> U_cf B tr S0 ->
0 <= n <= 48 -> st_cache_inited Sp = true -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
val_mem im_segs (mrestrict (w_H W) mem0) (K6.Kv ly (chunk_class n) (off / 16) + K6.RZ - 15) 1 jb ->
at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
  (fun z m => dpost_cf B inst ly Sp W tr z m) odd z W
  (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> K6.NPv n mod 8 <> 0) ->
(exists trc, apath (malloc_cf n tr S0) trc (ck_user (new_chunk (chunk_class n) off n), st_final Sp (chunk_class n) l off n tr z) /\
  gflag trc = true) ->
ARXq_cf B IOK Hp inst ly (st_final Sp (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
qtight (st_final Sp (chunk_class n) l off n tr z).
Proof.
intros Hp inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat
  [_ HQ0] (HU & HW & (HS & HE & HB) & _) Hlive0 [[I [HARp XMp]] _] Hmax _ Htr Nr Hinited Hcache WFR Hjb _ HRET Hodd
  [trc [HP _]].
pose proof (malloc_cf_apath_post (as_universe B) S0 n tr trc _ HU HW ltac:(lia) Hlive0 Htr HS HE HB HP) as MP.
unfold malloc_post_cf in MP. cbv beta iota in MP. destruct MP as (WF' & _ & _ & _ & _ & QT). pose proof (QT HQ0) as QT'.
split; [|exact QT']. split; [split; [exact I | split] | exact QT'].
- eapply (hit_bridge_k B) with (DPOST := fun z0 m => dpost_cf B inst ly Sp W tr z0 m); try eassumption.
  intros z0 m H. exact (proj2 H).
- apply xs_mapped_cf_wvb. intros e He.
  rewrite (xs_cf_secs ly Sp _ (proj1 (st_final_parts_cf Sp (chunk_class n) l off n tr z))) in He. exact (XMp e He).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_depot_miss: the depot field at the pop state Sp.  At P'' U_cf (admits, YG01.v:155) reads the depot: the entry's *)
(* trace premise carries to Sp through the field's depot equation (YG01.admits_keep, YG01.v:223); the entry ARX is   *)
(* not read (AGif1m.depot_miss_cgif).                                                                              *)
Lemma depot_miss_cf : forall Hp inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (buf : Z),
ARXq_cf B IOK Hp inst ly0 S0 W0 mem00 md00 -> U_cf B tr S0 ->
ARXq_cf B IOK Hp inst ly Sp W mem0 md0 -> st_depot Sp = st_depot S0 ->
(forall x : word, ag_dzone ly (bv_unsigned x) \/ ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 ag_depot_put) mem (seg_rom im_segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ ag_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  dpost_cf B inst ly Sp W tr z mem').
Proof.
intros Hp inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr regs mem md buf _ HU HARXp HDP.
assert (HU' : U_cf B tr Sp) by exact (admits_keep _ _ _ _ HU (or_introl HDP)).
exact (HDEP Hp inst ly Sp W mem0 md0 tr regs mem md buf HARXp HU').
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_oom: ARcf after Allocate's out-of-memory tail (the unit's law AR_oom_law_cf, as cgif's YFi5.AR_oom), the OOM  *)
(* byte owned (own_area_cf) and the thread's unwinding byte owned (own_core_cf).                                    *)
Lemma oom_cf : forall Hp inst ly S0 Sp W mem md n tr (sp0 : Z) mem' md',
ARXq_cf B IOK Hp inst ly Sp W mem md -> qtight Sp -> pc_chunks (cache Sp (chunk_class n)) = [] ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> a <> im_oom -> ~ (im_errno <= a < im_errno + 4) ->
   aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> bv_unsigned x <> im_oom -> ~ (im_errno <= bv_unsigned x < im_errno + 4) ->
   mem' x = mem x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) -> (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem' a) ->
ly_stk_lo ly + AFSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
val_mem im_segs (mrestrict (w_H W) mem') im_oom 1 1 -> same_io md md' -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
(exists trc, apath (malloc_cf n tr S0) trc (PNull, Sp) /\ gflag trc = true) ->
ARXq_cf B IOK Hp inst ly Sp W mem' md' /\ qtight Sp /\ AOX_cf B ly Sp im_oom /\ AOX_cf B ly Sp (ly_T ly + t_unwinding).
Proof.
intros Hp inst ly S0 Sp W mem md n tr sp0 mem' md' [[I [HAR XM]] HQ] _ _ AGV RAWV _ P1 Hlo Hhi VAL _ Hvm Hlz _.
pose proof HAR as (M & L & _). pose proof (amc_layout _ _ _ _ _ M) as LY.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & K1).
destruct (errno_range_cf ly Sp md LY L) as [E1 E2].
assert (OL : 4096 <= as_oom_byte B /\ as_oom_byte B < kImgEnd).
{ pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amc_syms _ _ _ _ _ M)) (as_oom_byte B, 1)
    ltac:(unfold asyms_areas; cbn; tauto)) as X.
  apply Exists_exists in X as (r & Hr & [S1 S2]).
  pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (R1 & R2 & R3).
  cbn [fst snd] in *. lia. }
assert (OOMo : AOX_cf B ly Sp im_oom).
{ unfold AOX_cf, AOXm_cf. left. rewrite <- HOOM.
  eapply own_area_cf with (r := (as_oom_byte B, 1)); [exact M | unfold asyms_areas; cbn; tauto | cbn [fst snd]; lia]. }
assert (UNWo : AOX_cf B ly Sp (ly_T ly + t_unwinding)).
{ unfold AOX_cf, AOXm_cf. left.
  eapply own_core_cf with (e := (ly_T ly, kThreadObjSize));
    [exact M | unfold core_extents; cbn; tauto | cbn [fst snd]; unfold t_unwinding, kThreadObjSize; lia]. }
(* the tail keeps every visible byte visible *)
assert (VIS : forall a, aview im_segs (w_H W) mem a <> None -> aview im_segs (w_H W) mem' a <> None).
{ intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (AV : forall m, aview im_segs (w_H W) m a = aview im_segs (w_H W) m a')
    by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
  rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  destruct (Z_le_gt_dec (sp0 - AFSTACK) a') as [G1|G1]; [destruct (Z_lt_ge_dec a' sp0) as [G2|G2]|].
  { apply apresent_aview_some_cf. apply P1. lia. }
  all: destruct (Z.eq_dec a' im_oom) as [EO|NO];
    [rewrite EO; pose proof (VAL 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0;
     unfold aview; rewrite V0; cbn; discriminate|].
  all: destruct (Z_le_gt_dec im_errno a') as [G3|G3];
    [destruct (Z_lt_ge_dec a' (im_errno + 4)) as [G4|G4];
     [apply aview_rom_some_cf; apply HEROM; rewrite HERR; lia|]|].
  all: rewrite (AGV a' Ha' ltac:(lia) NO ltac:(lia)); exact Hv. }
split; [|split; [exact HQ | split; [exact OOMo | exact UNWo]]].
assert (XM' : xs_mapped_cf ly Sp md') by (intros e He; rewrite Hvm; exact (XM e He)).
split; [|exact HQ]. split; [exact I|]. split; [|exact XM'].
apply (AR_oom_law_cf_ok ly Sp Hp W mem md mem' md' HAR).
- intros a Ra Ho NO. apply AGV; [exact Ra | | exact NO |].
  + intros ST. exact (AR_stack_law_ok_cf im_segs B ly Sp Hp W mem md a HAR ltac:(unfold AFSTACK in *; lia) Ho).
  + rewrite <- HERR. intros ER'. exact (errno_not_owned_cf B TS EII HIMG HEROM HENS ly Sp Hp W mem md a HAR ER' Ho).
- exact VIS.
- exact Hvm.
- exact Hlz.
- unfold eager_used. rewrite Hvm, Hlz. reflexivity.
- intros a Ha Hx.
  assert (Ra : 0 <= a < 2 ^ 64)
    by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
  assert (HB : kLowShadowBeg <= a < kHighMemBeg)
    by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
  apply RAWV; rewrite unsigned_lit_small by exact Ra.
  + clear - HB K1 Hlo. unfold kHighMemBeg, AFSTACK in *. lia.
  + rewrite <- HOOM. clear - HB OL. unfold kLowShadowBeg, kImgEnd in *. lia.
  + rewrite <- HERR. clear - HB E2. unfold kLowShadowBeg, kImgEnd in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_stack: the stack is never owned (AR_stack_law_ok_cf), and the errbuf slot is apart from it (xs_placed_cf).     *)
Lemma stack_cf : forall Hp inst ly S W mem md a, ARXq_cf B IOK Hp inst ly S W mem md ->
ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX_cf B ly S a.
Proof.
intros Hp inst ly S W mem md a [[_ [HAR _]] _] Ha O. unfold AOX_cf, AOXm_cf in O. destruct O as [O|O].
- exact (AR_stack_law_ok_cf im_segs B ly S Hp W mem md a HAR Ha O).
- pose proof HAR as (M & _). pose proof (amc_xs_placed _ _ _ _ _ M) as XP. unfold xs_placed_cf in XP.
  apply Exists_exists in O as (e & He & Hin).
  destruct (proj1 (Forall_forall _ _) XP e He) as (_ & _ & _ & D).
  assert (HS : In (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (sec_extents ly S ++ static_extents ly ++ ly_extra ly)).
  { apply in_or_app. right. apply in_or_app. left. unfold static_extents. apply in_or_app. right. left. reflexivity. }
  pose proof (proj1 (Forall_forall _ _) D _ HS) as DJ. unfold zdisjoint, in_zr in *. cbn [fst snd] in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_mono_join: st_final only adds the popped chunk and keeps the sections, the fake frames and st_secs, so an     *)
(* owned byte outside the new block stays owned and the errbuf slot is the same (AGif1m.mono_join_cgif).           *)
Lemma mono_join_cf : forall Hp inst ly Sp W mem md n l off tr z a,
ARXq_cf B IOK Hp inst ly Sp W mem md -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
~ (sptr_addr B ly (ck_user (new_chunk (chunk_class n) off n)) <= a <
   sptr_addr B ly (ck_user (new_chunk (chunk_class n) off n)) + req_size n) ->
AOX_cf B ly Sp a -> AOX_cf B ly (st_final Sp (chunk_class n) l off n tr z) a.
Proof.
intros Hp inst ly Sp W mem md n l off tr z a _ _ NB HO. unfold AOX_cf, AOXm_cf in HO |- *. destruct HO as [[Hpart NC]|X].
- left.
  assert (Pnc : exists p, ck_beg (new_chunk (chunk_class n) off n) = PPrim p) by (eexists; reflexivity).
  destruct (st_final_parts_cf Sp (chunk_class n) l off n tr z) as (_ & FS & CK).
  pose proof (sec_extents_upd_prim_cf ly Sp _ _ CK Pnc) as SE.
  unfold aowned. rewrite SE. split; [exact Hpart|].
  intros [(k & Hk & Hst & Hr) | (fq & Hcp & Hfr)].
  + rewrite CK in Hk. apply cfx_upd_in in Hk as [Ek|Hk].
    * subst k. apply NB. exact Hr.
    * apply NC. left. exists k. split; [exact Hk|]. split; [exact Hst | exact Hr].
  + rewrite FS in Hcp. apply NC. right. exists fq. split; [exact Hcp | exact Hfr].
- right. rewrite (xs_cf_secs ly Sp _ (proj1 (st_final_parts_cf Sp (chunk_class n) l off n tr z))). exact X.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AIfaceMEw's add-ons (AGif1mE.ame_cgif at the cf relation, over REP_STACK).                                       *)

(* ame_refill_v: amm_refill_cf's view frame gives errno on the view (errno is no AOX byte at either end and lies
   below the refill's window: errno_apart_rleaf_cf). *)
Lemma ame_refill_v_cf : forall Hp,
MnRefillW.ame_refill_v_w_t B (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) qtight refill_tree_cf REP_STACK.
Proof.
intros Hp inst ly S0 W mem0 md0 n sp0 regs mem mat HARX HR HRO0 Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1 RAW1 PRES1
  SP R1 R3 R4 R10 R11 R12 R13.
pose proof HARX as [[_ [HAR0 _]] _].
pose proof (MnRefillW.win_stk_w REP_STACK REP_STACK_af ly sp0 regs Hlo SP) as HSP.
eapply amreal_mono;
  [|exact (amm_refill_cf Hp inst ly S0 W mem0 md0 n sp0 regs mem mat HARX HR HRO0 Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1
             RAW1 PRES1 SP R1 R3 R4 R10 R11 R12 R13)].
intros r W' c' (ly' & regs' & mem' & md' & Ec & HARX' & HL & CI & BB & HD & LLE & WLE & RP & IO & FRV & FRR & _ & _ & PR & A0).
pose proof HARX' as [[_ [HAR' _]] _].
unfold MnRefillW.rleaf_ev_w. exists ly', regs', mem', md'.
split; [exact Ec|]. split; [exact HARX'|]. split; [exact HL|]. split; [exact CI|]. split; [exact BB|]. split; [exact HD|].
split; [exact LLE|]. split; [exact WLE|]. split; [exact RP|]. split; [exact IO|]. split; [exact FRV|].
split; [|split; [exact FRR | split; [exact PR | exact A0]]].
intros a Ha.
destruct (errno_apart_rleaf_cf ly S0 Hp W mem0 md0 ly' (snd r) Hp W' mem' md' _ (spZ regs) a HAR0 HAR' HSP Ha)
  as (Ra & N0 & N1 & NS).
exact (FRV a Ra N0 N1 NS).
Qed.

(* ame_depot_miss: YGcfInstHit.ae_depot_cf (the depot field with errno kept, AGif1mE.errno_kept_depot_cgif's script)
   at the pop state Sp.  At P'' U_cf (admits, YG01.v:155) reads the depot: the entry's trace premise carries to Sp
   through the field's depot equation (YG01.admits_keep, YG01.v:223); the entry ARX is not read. *)
Lemma ame_depot_miss_cf : forall Hp, MnRefillW.ame_depot_miss_w_t B (U_cf B) (ARXq_cf B IOK Hp) (dpost_cf B).
Proof.
intros Hp inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr regs mem md buf _ HU HARXp HDP.
assert (HU' : U_cf B tr Sp) by exact (admits_keep _ _ _ _ HU (or_introl HDP)).
exact (ae_depot_cf B IOK HIMG HDEP TS EII EDZ Hp inst ly Sp W mem0 md0 tr regs mem md buf HARXp HU').
Qed.

Theorem ifaceME_cf : forall Hp, MnRefillW.AIfaceMEw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow refill_tree_cf REP_STACK.
Proof.
intros Hp. constructor.
- exact (ame_refill_v_cf Hp).
- exact (MnRefillW.amm_refill_w_e _ _ _ _ _ _ _ (amm_refill_cf Hp)).
- exact (ame_depot_miss_cf Hp).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_view_m / if_owned_m / if_owned_m_k: YGcfInstHit's rpre-free view_cf / owned_cf / owned_cf_k (AGif1m.view_m_cgif /
   owned_m_cgif / owned_m_k_cgif reuse AGif1's / AGif1k's proofs the same way). *)
Lemma view_m_cf : forall Hp inst ly S W mem md n l off,
ARXq_cf B IOK Hp inst ly S W mem md -> 0 <= n -> from_primary n = true ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
off mod 32 = 0 /\ hview B W ly inst mem (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16).
Proof. intros Hp. exact (view_cf B IOK HIMG HSHB HTSD IOK_inst INST_CELLS Hp). Qed.

Lemma owned_m_cf : forall Hp inst ly S W mem md n l off odd a,
ARXq_cf B IOK Hp inst ly S W mem md -> 49 <= n <= 64512 ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
0 <= a < 2 ^ 64 -> (odd = true -> n mod 8 <> 0) ->
hit_writes ly n (chunk_class n) (off / 16) (rz_log n) odd a -> AOX_cf B ly S a.
Proof. intros Hp. exact (owned_cf B IOK HSHB HDZO Hp). Qed.

Lemma owned_m_k_cf : forall Hp inst ly S W mem md n l off odd a,
ARXq_cf B IOK Hp inst ly S W mem md -> 0 <= n <= 48 ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
0 <= a < 2 ^ 64 -> (odd = true -> K6.NPv n mod 8 <> 0) ->
hit_writes_k ly n (chunk_class n) (off / 16) odd a -> AOX_cf B ly S a.
Proof. intros Hp. exact (owned_cf_k B IOK HSHB HDZO Hp). Qed.

(* ================================================================================================================ *)
(* The interface: MnRefillW.AIfaceMw (AGif0n.AIfaceM with the refill window REP_STACK) at the cf instance, field by   *)
(* field in AIfaceM's order (AGif1m.iface_cgif_m).                                                                  *)
Theorem ifaceM_cf : forall Hp, MnRefillW.AIfaceMw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow refill_tree_cf REP_STACK.
Proof.
intros Hp. constructor.
- exact (mview_cf Hp).
- exact shape_miss_cf.
- exact (refill_cf Hp).
- exact (post_miss_cf Hp).
- exact (post_miss_k_cf Hp).
- exact (depot_miss_cf Hp).
- exact (oom_cf Hp).
- exact (stack_cf Hp).
- exact (view_m_cf Hp).
- exact (owned_m_cf Hp).
- exact (owned_m_k_cf Hp).
- exact (mono_join_cf Hp).
Qed.

End b.
End a.
