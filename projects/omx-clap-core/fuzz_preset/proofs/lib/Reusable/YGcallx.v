(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): acall_pre_x's last conjunct is
   `QMm S mem`, a NEW Section Variable that sees the call memory (cf: acall_pre_cf's trailing conjuncts, which since the
   cf layer's field round 3 end with arodata_ok_cf on the memory; part 3c took memnorm out). QM stays the state
   predicate of the model laws (alloc_model_laws_x) and the rules; Hypothesis QMQ : QMm S mem -> QM S beside AMX links
   them. The eight rules that BUILD the callee's acall_pre_x take `QMm Sc <call memory>` instead of `QM Sc`. Non-cf
   instances take QMm := fun S _ => QM S and QMQ := fun _ _ H => H. *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): a call whose callee may re-hide shadow (an ASan free
   or realloc that recycles a secondary) has a post whose world step is not wle and whose view frame excepts the
   re-hidden set. The rules over such a callee are stated over the callee's call post APOST and the journal's world
   relation R (YCbqG.ajournal_xwR). apost_ar_law / apost_j_law name what a rule reads off APOST; POST_AR_x / POST_J_x
   are the two laws at acall_post_x and R := wle. call_effect_journal_xwR is call_effect_journal_xw over R, for a
   post frame with a further exception DX that misses each view-frame domain of the call's journal;
   call_effect_journal_xw is its case R := wle, DX empty. The free rules are proved once over R and APOST (Section rR:
   aj_free_at_x_ctR, aj_free_x_ctR, over the text afree_realizes_xR, whose leaf free_leaf_xA is free_leaf_x with its
   post APOST, and aj_free_at_xR, aj_free_xR, their call_trace0 forms); aj_free_at_x_ct / aj_free_x_ct / aj_free_at_x /
   aj_free_x are their instances at wle and acall_post_x. The malloc rules aj_malloc_at_x_ctR / aj_malloc_at_xR /
   aj_malloc_xR / aj_malloc_x_ctR take the journal at a reflexive and transitive R that contains wle: the malloc text is
   the plain one (a malloc re-hides nothing), so the call's journal is at wle and enters the caller's by that
   inclusion; the old names are their instances at wle. Every statement that existed before keeps its text. *)
(* Modified by Theorem Labs, 2026-10-31 (field round 3 part 3c: memnorm out of every call text): malloc_leaf_x,
   free_leaf_x and free_leaf_xA lose their last conjunct, the memnorm keep (YAkMemnorm.memnorm segs mem ->
   YAkMemnorm.memnorm segs mem'), as YG0dcf.v's malloc_leaf_cf / free_leaf_cf lost theirs; each now ends with the
   errno keep and the raw frame. No rule of this file read that conjunct. *)
(* Theorem Labs, 2026-10: the allocator CALL FORMS and the malloc / free CALL-SITE RULES, GENERIC over the allocator
   invariant ARx of YCbqG.v (Section Variables segs B PST ARx). No allocator instance, no image class, no address and
   no ledger is named here; YGcallcf.v shows that the cf instance's forms (YG0dcf.v) are these at ARx := ARcf.

   1. THE FORMS (Section gx): acall_pre_x, acall_post_x, malloc_leaf_x, amalloc_realizes_x, free_leaf_x,
      afree_realizes_x are YG0dcf.v's acall_pre_cf / acall_post_cf / malloc_leaf_cf / amalloc_realizes_cf /
      free_leaf_cf / afree_realizes_cf (h-mani-a8) with
        ARcf segs B                                       -> ARx (Hp right after the state, as there),
        the trailing conjuncts of acall_pre_cf           -> QMm S mem, one predicate on the allocator state and the
                                                             call memory (QM S: its state part, for the model laws),
        malloc_cf -> mt (the model malloc), cf_malloc_max -> nmax, free_cf -> ft (the model free).
      afree_realizes_x keeps the premise `~ In (sptr_addr B ly p) Hp`; amalloc_realizes_x keeps
      `blocks_bytes S + n <= LIVE_MAX`. cgif's originals: YG0d.v:226-277. ecall_pre_x (YG0d.v:278-284 over ARx) is
      NOT restated: it is the frame-class lane's frozen FCiface.v, imported.
      REUSED AS THEY STAND, because they name neither AR nor Wf: cfg_at, ascratch, chain_pre, call_trace (YG0d.v:213-225),
      acall_kept (YCbq.v:824, here acall_kept_x), api_env (YCbq.v:808), in_ablocks (:836), map_eq_In (:853),
      asptr_null_dec (:1352), call_trace_in (:319), and YCbqG.v's ajournal_x, ajournal_x_sub, blk_img_x, frm_img_x,
      sep_blocks_x, sep_block_frame_x, frames_bounds_x.

   2. THE MODEL LAWS (alloc_model_laws_x): what cgif's call-site rules take from model_laws (YG0d.v:513, ml_malloc /
      ml_free) over mt / ft and a state predicate WFx (cgif's Wf), with `st_nev s < EV_MAX` replaced by QM s. cgif
      reads four facts off its token `atok true t Q` (asafe t, agprog t, is_spin t = false, and Q on every apath);
      the record states those four facts, not a token, so the instance supplies them from its own token (cf:
      atok_cf, YGcfTok.v, whose areq_ok_cf admits the error-buffer KMmapSec plain atok refuses; YGcallcf.v
      alloc_model_laws_x_cf). The posts keep only what the rules read from malloc_post / free_post (YG01.v:449-461):
      the secondary list does not shrink (cgif: secs_ext, read only through its length), the frames are kept, the
      blocks change by the call's own block, and the event count does not go down (cgif's `st_nev s' = st_nev s + 1`
      is NOT kept: an instance's model may tick several times in one call; the journal's relative count k then grows
      by st_nev S2 - st_nev Sc, the call's own count).

   3. THE CALL-SITE RULES (Section r): the x twins of cgif's YCbq.v, released at ossv/recipes
      proofs/cgif/cgif_file_fuzzer/lib/YCbq.v (this tree's copy, lib/Reusable/YCbq.v, is the same text two lines lower):
      call_effect_journal :856, acall_post_journal :956, acall_kept_of_journal :971, sep_blocks_pos :710,
      aj_free_at :990, aj_malloc_at :1352, aj_malloc :1715, aj_free :2109; the model laws are YG0d.v:513 model_laws.
      Rule 24: `proof-index malloc free` (index of 2026-10-28T21:58Z) lists runtime walks of malloc / free in other
      units, none a call-site rule over a generic allocator invariant; cgif's YCbq.v is the released source ported.
      The differences, each minimal:
      (a) no `st_nev Sc < EV_MAX` premise and no aregime: acall_pre_x has neither, and the model laws take QM; the
          journal's count grows by `st_nev S2 - st_nev Sc` where cgif's grows by 1;
      (b) the size premise is `0 <= n < nmax` (cgif: MALLOC_MAX); `blocks_bytes Sc + n <= LIVE_MAX` is kept;
      (c) `QMm Sc memT` is a premise of aj_malloc_at_x / aj_free_at_x (acall_pre_x's last conjunct; the model laws get
          QM Sc from it by QMQ; cgif derived its qmeter from aregime by mroom_of_regime);
      (d) Hp is threaded unchanged through the call: the caller's journal is at Hpc before and after;
      (e) aj_free_at_x / aj_free_x take `~ In pa Hpc` (afree_realizes_x's premise);
      (f) the call's own journal (call_effect_journal_x, acall_post_journal_x) is at PST = []: the runtime writes no
          program static, so acall_kept_of_journal_x keeps cgif's UNCONDITIONAL image clause, and ajournal_x_nil_pst
          lifts that journal to the caller's PST before ajournal_x_sub;
      (g) call_effect_journal_x takes the post ghost set Hp2 free (a call that moves Hp can use it);
      (h) every arm of the malloc and free rules adds, at the call's state, acall_pre_x, the admission of the call
          trace, the model path (`apath (mt n trace Sc) trc (p, S2)`, free: `apath (ft q trace Sc) trc (tt, S2)`)
          with every ask granted (`gflag trc = true`, from amreal_SRr04, YG0d.v:185, where cgif's rule uses
          amreal_SRr), and the leaf at that result (malloc: with `p = PNull <-> res = 0` and, off NULL,
          `res = sptr_addr B ly2 p`; free: with `sptr_addr B lyc q = pa` and `In (q, n) (blocks Sc)`), so a text can
          derive the instance's refusal post (YG0dcf.v malloc_cf_null_post) and the room after the call from them;
      (j) malloc_leaf_x's frame exception adds the extents `XS ly S ++ XS ly' S'` (cf: the error-message buffer, xs_cf):
          a refused malloc may write them. The call journal then takes them as an extra write set (call_effect_journal_xw
          / acall_post_journal_xw; the _x forms are the case of an empty set), with the AR law ARx_xs_law below;
      (k) malloc_leaf_x also states the wrapper's NULL-path stores, errno = 12 (ENOMEM) and the out-of-memory byte = 1
          (as malloc_leaf_cf does), and the rule's res = 0 arm exposes them at the post memory;
      (i) each rule has a twin suffixed _ct whose trace premise is `admits U (call_trace lyc pc0 regsT ch) Sc` instead
          of cgif's form on call_trace0 (admits_call_trace0, YCbqG.v, turns that into this one): a tail call at a
          function's entry has the call_trace form from that function's text even when frame0_ok fails. The _ct
          lemmas carry the proofs; the call_trace0 forms are their corollaries.
      (l) THE TRACE CARRIER (the internal file TRACE-CARRIER.md section 7 items 5 and 13): the trace premise is the realizes texts'
          `admits (as_universe B) trace Sc` (YG01.v), and every rule is stated over the journal ajournal_xw at the
          caller's wild-trace budget WS (implicit; ajournal_x is WS = []). The call stores at most its own trace
          (alloc_model_laws_x's depot laws), so the post's budget is WS ++ [trace]; for a FIXED trace the caller
          returns to WS by YCbqG.v's ajournal_xw_fix1 (admits_ct_fix gives the premise from the fixed trace).
      Section hypotheses of the rules: LAWS (YCbqG.v AR_laws_x), segs_low, errno_low (cgif's api_env), AMX
      (alloc_model_laws_x), and THREE AR LAWS that AR_laws_x lacks, in YCbqG's style:
        ARx_owned_low_law (cgif's AR_owned_low_law, YG0d.v; AR_laws_cf's alc_owned_low),
          used by call_effect_journal_xw as cgif's call_effect_journal uses al_owned_low;
        ARx_wf_law (ARx S -> WFx S; cgif reads it as am_wf (proj1 HAR); at ARcf it is amc_wf, YG0ncf.v),
          used to meet the model laws' premise;
        ARx_xs_law (the extents XS lie below alloc_ceiling in application memory, outside the image, the blocks, the
          frames and the extra areas), used by the malloc rules only; cgif has no such extents.
      Of the candidate laws wle, flag, owned_low, zshadow and shadow, these proofs use owned_low only.
   SK (YI16.sink_head) is a Context parameter of every lemma; global sink_head instances exist (YI5b, YE2k, AE2k):
   pass SK explicitly, never let it be inferred.

   4. A TAIL CALL (fuzz_free's `j` to the free wrapper with ra = its caller's ra and sp = its entry sp) is aj_free_at_x_ct
      / aj_free_x_ct at o = 0 with raw = the entry ra: spZ = sp0 + 0, 0 mod 16 = 0, 0 <= 0, and ASTACK - 0 <= STK holds
      for STK_fuzz_free = FR F_fuzz_free + zmaxl [STK_RT_ALLOC; STK_RT_ECALL] with STK_RT_ALLOC = ASTACK (PRH_Base.v:98,
      :141); ret_ok raw and 4096 <= raZ come from afn_pre_x, chain_pre from achain_chain_pre (YCbq.v:281) at the entry
      sp and s0, the trace premise from the text's fixed trace `In (call_trace ly (pc_free_ra0 _) regs ch) _` by
      admits_ct_fix (YCbqG.v), and the post's journal back at the empty budget by ajournal_xw_fix1. The rule asks
      nothing a tail call cannot give.

   Numerals: 1, 2, 3, 4, 10 are RISC-V register numbers and 12 (ENOMEM) / 1 (the out-of-memory byte) are stored values
   (WORD); 0, 16 (stack alignment), 4096 (cgif's lowest block address), 16384 (= ASTACK, YG0d.v:18) and 2 ^ 64 are
   LENGTH / DERIVED constants of cgif's rules. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
(* the step relation and the allocator realization over a world relation (SRrG, amrealG) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH.
(* ecall_pre_x is the frame-class lane's (FCiface.v, frozen); it is not restated here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* ---------------------------------------------------------------------------- *)
(* 0. THE DEPOT STEP of an instance's model law that is stated for EVERY universe (cf: YG0ucf.v model_laws_cf_ok,  *)
(*    whose posts keep the invariant at their universe). Run the law at univ_at d tr, the universe whose fixed part *)
(*    is the call's depot d plus its trace tr and which has no wild part: the post's depot_fits then says that the  *)
(*    new depot holds no trace but those of d and tr (univ_at_step), the alloc_model_laws_x depot laws.            *)
Definition univ_at (d : list (list Z)) (tr : list Z) : Univ :=
MkUniv (if mem_trace tr d then d else d ++ [tr]) [] 0%nat.
Lemma wild_part_nil_of : forall V d, (forall t, In t d -> In t (u_fix V)) -> wild_part V d = [].
Proof.
intros V d H. unfold wild_part. induction d as [|t d IH]; [reflexivity|].
assert (E : mem_trace t (u_fix V) = true) by (apply mem_trace_In; apply H; left; reflexivity).
simpl. destruct (mem_trace t (u_fix V)); [|discriminate]. simpl. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.
(* a trace that is admitted and new finds room: the depot holds fewer than DEPOT_MAX traces *)
Lemma depot_room : forall U s tr, universe_ok U -> depot_fits U (st_depot s) -> admits U tr s ->
mem_trace tr (st_depot s) = false -> Z.of_nat (length (st_depot s)) < DEPOT_MAX.
Proof.
intros U s tr (HL & _ & _) (Hnd & _ & Hw) (_ & [Hm | [Hf | Hr]]) Hn; [congruence| |].
- apply mem_trace_In in Hf.
  assert (Hn' : ~ In tr (st_depot s)) by (intros H; apply mem_trace_In in H; congruence).
  rewrite (wild_split U (st_depot s)).
  assert (Hle : (length (tr :: List.filter (fun t => mem_trace t (u_fix U)) (st_depot s)) <= length (u_fix U))%nat).
  { apply NoDup_incl_length.
    - constructor; [intros Ht; apply filter_In in Ht as [Ht _]; exact (Hn' Ht) | apply NoDup_filter; exact Hnd].
    - intros t [<-|Ht]; [exact Hf|]. apply filter_In in Ht. apply mem_trace_In. exact (proj2 Ht). }
  cbn [length] in Hle. lia.
- rewrite (wild_split U (st_depot s)).
  assert (Hle : (length (List.filter (fun t => mem_trace t (u_fix U)) (st_depot s)) <= length (u_fix U))%nat).
  { apply NoDup_incl_length; [apply NoDup_filter; exact Hnd|].
    intros t Ht. apply filter_In in Ht. apply mem_trace_In. exact (proj2 Ht). }
  lia.
Qed.
Lemma univ_at_ok : forall U s tr, universe_ok U -> depot_fits U (st_depot s) -> admits U tr s ->
universe_ok (univ_at (st_depot s) tr).
Proof.
intros U s tr HU Hd Ha. pose proof (depot_len_bound U _ HU Hd) as HL.
pose proof Hd as (Hnd & HI & _). pose proof Ha as ((Htl & _) & _).
assert (HF : Forall (fun t => (length t <= kUnwindMax)%nat) (st_depot s)).
{ apply Forall_forall. intros t Ht. exact (proj1 (proj1 (Forall_forall _ _) HI t Ht)). }
unfold universe_ok, univ_at. cbn [u_fix u_wmax]. destruct (mem_trace tr (st_depot s)) eqn:Em.
- split; [lia|]. split; [exact HF | exact Hnd].
- pose proof (depot_room U s tr HU Hd Ha Em) as Hlt.
  split; [rewrite length_app; cbn [length]; lia|]. split.
  + apply Forall_app. split; [exact HF | constructor; [exact Htl | constructor]].
  + apply NoDup_app; [exact Hnd | constructor; [intros [] | constructor] |].
    intros x Hx [<-|[]]. apply mem_trace_In in Hx. congruence.
Qed.
Lemma univ_at_fits : forall U d tr, depot_fits U d -> depot_fits (univ_at d tr) d.
Proof.
intros U d tr (Hnd & HI & _).
assert (Hsub : forall t, In t d -> In t (u_fix (univ_at d tr))).
{ intros t Ht. unfold univ_at. cbn [u_fix]. destruct (mem_trace tr d); [exact Ht | apply in_or_app; left; exact Ht]. }
split; [exact Hnd|]. split.
- apply Forall_forall. intros t Ht. split; [exact (proj1 (proj1 (Forall_forall _ _) HI t Ht)) | left; exact (Hsub t Ht)].
- rewrite (wild_part_nil_of _ _ Hsub). cbn. lia.
Qed.
Lemma univ_at_admits : forall U s tr, admits U tr s -> admits (univ_at (st_depot s) tr) tr s.
Proof.
intros U s tr ((Htl & _) & _).
assert (Hin : In tr (u_fix (univ_at (st_depot s) tr))).
{ unfold univ_at. cbn [u_fix]. destruct (mem_trace tr (st_depot s)) eqn:Em;
  [apply mem_trace_In; exact Em | apply in_or_app; right; left; reflexivity]. }
split; [split; [exact Htl | left; exact Hin]|]. right. left. apply mem_trace_In. exact Hin.
Qed.
Lemma univ_at_step : forall d tr d', depot_fits (univ_at d tr) d' -> incl d' (d ++ [tr]).
Proof.
intros d tr d' (_ & HI & _) t Ht. destruct (proj1 (Forall_forall _ _) HI t Ht) as [_ [Hf | (p & sfx & Hp & _)]].
- unfold univ_at in Hf. cbn [u_fix] in Hf. destruct (mem_trace tr d); [apply in_or_app; left; exact Hf | exact Hf].
- unfold univ_at in Hp. cbn [u_wild] in Hp. destruct Hp.
Qed.


Section gx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* the room / live-count conjuncts the allocator call carries on its state (cf: qmeter_cf, the live-secondary
   bound and ERRB_ROOM, YG0dcf.v:40-47) *)
Variable QM : astate -> Prop.
(* the call's trailing conjuncts on the state AND the call memory (cf: acall_pre_cf's, which end with arodata_ok_cf
   on mem since the layer's field round 3; part 3c took memnorm out); used ONLY in acall_pre_x. Non-cf: fun S _ => QM S. *)
Variable QMm : astate -> (word -> option byte) -> Prop.
(* the model malloc and its request bound, the model free *)
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
(* the model's state invariant (cgif: Wf (as_universe B); cf: Wf_cf (as_universe B)) *)
Variable WFx : astate -> Prop.
(* the extents a refused malloc may write besides its block (cf: the error-message buffer, xs_cf of YG0ncf.v) *)
Variable XS : alayout -> astate -> list (Z * Z).
Local Abbreviation code := (as_code B).

(* ---------------------------------------------------------------------------- *)
(* 1. The call forms: YG0dcf.v:32-132 over ARx and QM.                            *)
Definition acall_pre_x (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARx ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ASTACK <= spZ regs /\ ly_bot ly + ACALL_PREFIX < spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch /\
QMm S mem.

Definition acall_post_x (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARx ly' S' Hp W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

Definition malloc_leaf_x (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_x ASTACK ly S Hp W regs mem md
(fun a => (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) \/
Exists (in_zr a) (XS ly S ++ XS ly' (snd r)))
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r) /\
(fst r = PNull -> rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
(* YG0dcf.v malloc_leaf_cf's last two conjuncts: errno kept on success (raw), the raw frame *)
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ Exists (in_zr (bv_unsigned x)) (XS ly S ++ XS ly' (snd r))) ->
 mem' x = mem x).

Definition amalloc_realizes_x : Prop :=
forall ly S Hp W regs mem md n ch,
acall_pre_x ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < nmax -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly (pc_malloc_ra0 code) regs ch) S ->
amreal segs (mt n (call_trace ly (pc_malloc_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_malloc code) regs mem md)
(malloc_leaf_x ly S Hp W regs mem md n).

Definition free_leaf_x (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_x ASTACK ly S Hp W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
qtight (snd r) /\
(* YG0dcf.v free_leaf_cf's last two conjuncts: errno kept (raw), the raw frame *)
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
 mem' x = mem x).

Definition afree_realizes_x : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_x ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 code) regs ch) S ->
amreal segs (ft p (call_trace ly (pc_free_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_free code) regs mem md)
(free_leaf_x ly S Hp W regs mem md p n).

(* The free leaf and text GENERIC in the callee's call post APOST (acall_post_x's type) and, for the text, in the world
   relation R its realization composes through (amrealG). free_leaf_xA is free_leaf_x's body with acall_post_x
   replaced by APOST; free_leaf_x keeps its own body (proofs elsewhere unfold it), and free_leaf_x_A shows by
   reflexivity that it is free_leaf_xA at acall_post_x. afree_realizes_x_R lifts the plain text to wle. *)
Definition free_leaf_xA
(APOST : Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
(ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
APOST ASTACK ly S Hp W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
qtight (snd r) /\
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
 mem' x = mem x).

Lemma free_leaf_x_A : forall ly S Hp W regs mem md p n r W' c',
free_leaf_x ly S Hp W regs mem md p n r W' c' = free_leaf_xA acall_post_x ly S Hp W regs mem md p n r W' c'.
Proof. reflexivity. Qed.

Definition afree_realizes_xR (R : world segs -> world segs -> Prop)
(APOST : Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_x ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 code) regs ch) S ->
amrealG segs R (ft p (call_trace ly (pc_free_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_free code) regs mem md)
(free_leaf_xA APOST ly S Hp W regs mem md p n).

Lemma afree_realizes_x_R : afree_realizes_x -> afree_realizes_xR (@wle segs) acall_post_x.
Proof.
intros AF ly S Hp W regs mem md p n ch Hpre H1 H2 H3 H4.
exact (amreal_amrealG segs (@wle segs) (fun _ _ H => H) _ W _ _ (AF ly S Hp W regs mem md p n ch Hpre H1 H2 H3 H4)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The model laws the rules read (cgif's model_laws, YG0d.v:513).              *)
Definition malloc_post_x (s : astate) (n : Z) (r : sptr * astate) : Prop :=
let (p, s') := r in
st_nev s <= st_nev s' /\ (length (st_secs s) <= length (st_secs s'))%nat /\ frames s' = frames s /\
match p with
| PNull => blocks s' = blocks s
| _ => blocks s' = blocks s ++ [(p, n)]
end.
Definition free_post_x (s : astate) (p : sptr) (n : Z) (r : unit * astate) : Prop :=
let s' := snd r in
st_nev s <= st_nev s' /\ (length (st_secs s) <= length (st_secs s'))%nat /\ frames s' = frames s /\
(exists l1 l2, ((p = PNull /\ l1 ++ l2 = blocks s) \/ blocks s = l1 ++ (p, n) :: l2) /\ blocks s' = l1 ++ l2).
(* What the rules take from cgif's `atok true (malloc n tr s) (malloc_post U s n)`: the four facts its proofs read
   off the token (atok_asafe, atok_agprog, atok_nospin, atok_apath, YG01.v). Stated without a token predicate, so an
   instance whose model needs a wider request check (cf: atok_cf over areq_ok_cf, YGcfTok.v) supplies them from its
   own token; YGcallcf.v alloc_model_laws_x_cf does that from atok_cf. The trace premise is the realizes texts'
   `admits (as_universe B) tr s` (YG01.v). amx_malloc_depot / amx_free_depot: a call stores at most its own trace
   (YG01.v depot_put_grow on every path); the rules read them for the journal's wild-trace count. *)
Record alloc_model_laws_x : Prop := {
amx_malloc : forall s n tr, WFx s -> QM s -> 0 <= n < nmax -> blocks_bytes s + n <= LIVE_MAX ->
admits (as_universe B) tr s ->
asafe (mt n tr s) /\ agprog (mt n tr s) /\ is_spin (mt n tr s) = false /\
(forall tr' r, apath (mt n tr s) tr' r -> malloc_post_x s n r);
amx_free : forall s p n tr, WFx s -> QM s -> (p = PNull \/ In (p, n) (blocks s)) -> admits (as_universe B) tr s ->
asafe (ft p tr s) /\ agprog (ft p tr s) /\ is_spin (ft p tr s) = false /\
(forall tr' r, apath (ft p tr s) tr' r -> free_post_x s p n r);
amx_malloc_depot : forall s n tr, WFx s -> QM s -> 0 <= n < nmax -> blocks_bytes s + n <= LIVE_MAX ->
admits (as_universe B) tr s ->
forall tr' r, apath (mt n tr s) tr' r -> incl (st_depot (snd r)) (st_depot s ++ [tr]);
amx_free_depot : forall s p n tr, WFx s -> QM s -> (p = PNull \/ In (p, n) (blocks s)) -> admits (as_universe B) tr s ->
forall tr' r, apath (ft p tr s) tr' r -> incl (st_depot (snd r)) (st_depot s ++ [tr])
}.

(* The three AR laws the rules use that YCbqG.v's AR_laws_x lacks. *)
Definition ARx_owned_low_law : Prop :=
forall ly S Hp W mem md a, ARx ly S Hp W mem md -> aowned B ly S a -> 0 <= a < alloc_ceiling.
Definition ARx_wf_law : Prop :=
forall ly S Hp W mem md, ARx ly S Hp W mem md -> WFx S.
Definition ARx_xs_law : Prop :=
forall ly S Hp W mem md a, ARx ly S Hp W mem md -> Exists (in_zr a) (XS ly S) ->
a < alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
(forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames S) -> ~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid)) /\
~ Exists (in_zr a) (ly_extra ly).

(* cgif's acall_kept (YCbq.v:824) as it stands: it names neither AR nor Wf. *)
Definition acall_kept_x (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
(W2 : world segs) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
acall_kept segs B lyc Sc W memc W2 mem2 slo shi E.

(* THE CALLEE POST'S TWO LAWS, for call rules generic in the callee's call post APOST (acall_post_x's type) and in the
   journal's world relation R. apost_ar_law: the post gives the invariant at the post state (at the post's ghost set),
   the layout step and the saved registers. apost_j_law: with the invariant and the stack window at the call state and
   the call's own state facts (frames kept, the event and slot counts, an extra write set XW placed below the ceiling
   in application memory off the image, the blocks, the frames and the extra areas, the post frame's exception Eb
   inside XW or the blocks, a block that leaves inside the footprint FP1, qtight, the stored traces), the post gives the
   call's own journal at R, at PST = [] and the post's ghost set Hp2. At acall_post_x and R := wle they are POST_AR_x
   and POST_J_x (POST_AR_x in Section gx, POST_J_x in its Section r). *)
Definition apost_ar_law
(APOST : Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) : Prop :=
forall stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
APOST stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
ARx ly' S' Hp W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ aregs_preserved regs regs'.
Definition apost_j_law (R : world segs -> world segs -> Prop)
(APOST : Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) : Prop :=
forall lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2 (Eb XW : Z -> Prop) FP1 k1 WS,
APOST ASTACK lyc Sc Hp2 W regs memc mdc Eb ly2 S2 W2 regs2 mem2 md2 ->
ARx lyc Sc Hpc W memc mdc ->
astk_ok ASTACK lyc (spZ regs) ->
frames S2 = frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, XW a -> a < alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
(forall p n, In (p, n) (ablocks B lyc Sc) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
~ Exists (in_zr a) (ly_extra lyc)) ->
(forall a, Eb a -> XW a \/ exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
incl (wild_part (as_universe B) (st_depot S2)) (wild_part (as_universe B) (st_depot Sc) ++ WS) ->
ajournal_xwR segs B [] ARx R ASTACK (spZ regs) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS.

Lemma POST_AR_x : apost_ar_law acall_post_x.
Proof. intros stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' (H1 & H2 & _ & H4 & _). exact (conj H1 (conj H2 H4)). Qed.

Lemma not_Exists_nil_zr : forall a, ~ Exists (in_zr a) [].
Proof. intros a H. inversion H. Qed.

(* A journal whose image clause exempts nothing is one at any PST (any budget), over any world relation R. *)
Lemma ajournal_xwR_nil_pst : forall (R : world segs -> world segs -> Prop)
P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
ajournal_xwR segs B [] ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
ajournal_xwR segs B P ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
Proof.
intros R P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS HJ.
pose proof (ajxR_img HJ) as F3.
exact (ajxR_intro (ajxR_ar HJ) (ajxR_ly HJ) (ajxR_secs HJ) (ajxR_rel HJ) (ajxR_io HJ) (ajxR_frs HJ) (ajxR_nev HJ)
  (ajxR_k HJ) (ajxR_hi HJ) (ajxR_blk HJ) (fun a Hi Hns He _ Hsp => F3 a Hi Hns He (not_Exists_nil_zr a) Hsp)
  (ajxR_frm HJ) (ajxR_gone HJ) (ajxR_pres HJ) (ajxR_stk HJ) (ajxR_extra HJ) (ajxR_qt HJ) (ajxR_wild HJ)).
Qed.
(* A journal whose image clause exempts nothing is one at any PST (any budget). *)
Lemma ajournal_xw_nil_pst : forall P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
ajournal_xw segs B [] ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
ajournal_xw segs B P ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
Proof. exact (ajournal_xwR_nil_pst (@wle segs)). Qed.
Lemma ajournal_x_nil_pst : forall P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_x segs B [] ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_x segs B P ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (ajournal_xw_nil_pst P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k [] HJ).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The call-site rules.                                                        *)
Section r.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law.
Hypothesis WFL : ARx_wf_law.
Hypothesis AMX : alloc_model_laws_x.
(* the call's memory-aware conjuncts give the state predicate the model laws take (non-cf: the identity) *)
Hypothesis QMQ : forall S mem, QMm S mem -> QM S.
Hypothesis XSL : ARx_xs_law.
Let UNIV0 : In [pc_malloc_ra0 code] (as_universe B) /\ In [pc_free_ra0 code] (as_universe B) := proj2 (proj2 errno_low).
Let ERRIMG : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a := proj1 (proj2 errno_low).
Local Abbreviation LBLK := (alx_blocks segs B ARx LAWS).
Local Abbreviation LLAY := (alx_layout segs B ARx LAWS).
Local Abbreviation LFRS := (alx_frames segs B ARx LAWS).
Local Abbreviation LOIM := (alx_owned_image segs B ARx LAWS).
Local Abbreviation LSEP := (alx_sep segs B ARx LAWS).
Local Abbreviation LEXT := (alx_extra segs B ARx LAWS).

(* cgif YCbq.v:712 sep_blocks_pos (released :710) *)
Lemma sep_blocks_pos_x : forall ly S Hp W mem md x y l1 l2 l3,
ARx ly S Hp W mem md -> ablocks B ly S = l1 ++ x :: l2 ++ y :: l3 ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l1 l2 l3 HAR E.
destruct (LSEP ly S Hp W mem md HAR) as [Hq _]. apply pairwise_app_l in Hq as [Hq _].
rewrite E, !map_app in Hq. cbn in Hq. rewrite map_app in Hq. cbn in Hq.
exact (pairwise_In2 zdisjoint _ _ _ _ _ _ Hq eq_refl).
Qed.

(* cgif YCbq.v:858 call_effect_journal (released :856); the post ghost set Hp2 is free, the journal is at PST = [],
   and the call may also write an extra set XW (cf: the error-message buffer) outside every block, frame, image byte
   and extra area, below alloc_ceiling in application memory. The call's budget WS: the wild traces it stored are
   among WS (an allocator call: its own trace, from the model law's depot step). Over a world relation R: the post's
   world step R W W2 is the journal's; the post frame may except a further set DX (a re-hiding call's dead shadow),
   which misses each view-frame domain of the call's journal: above the ceiling, the bytes of the blocks live after
   the call, the image, the call state's frames and their shadow, and the call layout's extra areas. *)
Lemma call_effect_journal_xwR : forall (R : world segs -> world segs -> Prop) (DX : Z -> Prop)
stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb XW : Z -> Prop) FP1 nf k1 WS,
ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> R W W2 -> same_io mdc md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ ascratch B stk regs a -> ~ Eb a -> ~ DX a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
ARx lyc Sc Hpc W memc mdc ->
astk_ok stk lyc (spZ regs) ->
frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, XW a -> a < alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
(forall p n, In (p, n) (ablocks B lyc Sc) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
~ Exists (in_zr a) (ly_extra lyc)) ->
(forall a, Eb a -> XW a \/ exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
incl (wild_part (as_universe B) (st_depot S2)) (wild_part (as_universe B) (st_depot Sc) ++ WS) ->
(forall a, alloc_ceiling <= a -> ~ DX a) /\
(forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> ~ DX (p + i)) /\
(forall a, in_img segs a -> ~ DX a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  ~ DX a) /\
(forall a, Exists (in_zr a) (ly_extra lyc) -> ~ DX a) ->
ajournal_xwR segs B [] ARx R stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS.
Proof.
intros R DX stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb XW FP1 nf k1 WS
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2 HW (D1 & D2 & D3 & D4 & D5).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (KEEP : forall a, ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
~ (spZ regs - stk <= a < spZ regs) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ Eb a -> ~ DX a -> 0 <= a < 2 ^ 64 ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a H1 H2 H3 H4 H5 H6 H7. apply (Hfr a H7 H1 H2); [|exact H5 | exact H6].
unfold ascratch. intros [H|H]; [exact (H3 H) | exact (H4 H)]. }
assert (BLK : forall b m a, In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
app_addr a).
{ intros b m a [Hb|Hb] Hr.
- destruct (LBLK lyc Sc Hpc W memc mdc b m HAR Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia.
- destruct (LBLK ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia. }
split; [exact HAR2|]. split; [exact Hly2|]. split; [exact Hsecs|]. split; [exact Hwle2|]. split; [apply aos_step_of_same_io, Hio2|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk1|].
split.
{   intros a Ha Hs. apply KEEP.
- intros Ho. pose proof (OWNLOW _ _ _ _ _ _ a HAR Ho). zlia.
- intros Ho. pose proof (OWNLOW _ _ _ _ _ _ a HAR2 Ho). zlia.
- exact Hs.
- zlia.
- intros He. destruct (HE a He) as [Hx | (b & m & Hbm & Hr & _)];
[destruct (XWP a Hx) as (Xc & _); zlia | pose proof (BLK b m a Hbm Hr); zlia].
- exact (D1 a (proj1 Ha)).
- zlia. }
split.
{   intros p n i H1 H2 Hi Hnf. apply KEEP.
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (LBLK lyc Sc Hpc W memc mdc p n HAR H1))))) (p + i) ltac:(zlia))).
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (LBLK ly2 S2 Hp2 W2 mem2 md2 p n HAR2 H2))))) (p + i) ltac:(zlia))).
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). zlia.
- intros Herr. exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ p n (p + i) HAR H1 ltac:(zlia) (ERRIMG _ Herr)).
- intros He. destruct (HE _ He) as [Hx | (b & m & Hbm & Hr & [Hf | Hnot])];
[exact (proj1 (proj2 (proj2 (proj2 (XWP _ Hx)))) p n H1 ltac:(zlia)) | exact (Hnf Hf)|].
destruct Hbm as [Hbm|Hbm]; [exact (Hnot Hbm)|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m p n HAR2 Hbm H2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- exact (D2 p n i H2 Hi).
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). pose proof asan_consts. zlia. }
split.
{   intros a Hi Hns He _ _. pose proof (segs_low a Hi). apply KEEP.
- intros Ho. exact (Hns (proj1 (LOIM _ _ _ _ _ _ a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (LOIM _ _ _ _ _ _ a HAR2 Hi) Ho)).
- zlia.
- exact He.
- intros Heb. destruct (HE a Heb) as [Hx | (b & m & Hbm & Hr & _)]; [exact (proj1 (proj2 (proj2 (XWP a Hx))) Hi)|].
destruct Hbm as [Hbm|Hbm];
[exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ b m a HAR Hbm Hr Hi) | exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ b m a HAR2 Hbm Hr Hi)].
- exact (D3 a Hi).
- zlia. }
split.
{   intros cid pos a Hin Hr Hnf. pose proof (D4 cid pos a Hin Hr) as HDa.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (LFRS lyc Sc Hpc W memc mdc cid pos HAR Hin) as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (LFRS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & Hb2 & Hsh2). rewrite Efa in Hb2, Hsh2.
destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply KEEP.
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia. exact (proj2 Hsh).
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb2 a Hr))|].
specialize (Hsh2 (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh2 by zlia. exact (proj2 Hsh2).
- destruct Hr as [Hr|Hr]; zlia.
- intros Herr. destruct Hr as [Hr|Hr];
[exact (frm_img_x segs B ARx LAWS _ _ _ _ _ _ cid pos a HAR Hin Hr (ERRIMG _ Herr)) | zlia].
- intros Heb. destruct (HE a Heb) as [Hx | (b & m & Hbm & Hrb & _)].
{ destruct (XWP a Hx) as (Xc & Xa & _ & _ & Xf & _). destruct Hr as [Hr|Hr]; [exact (Xf cid pos Hin Hr) | zlia]. }
pose proof (BLK b m a Hbm Hrb).
destruct Hr as [Hr|Hr]; [|zlia].
destruct Hbm as [Hbm|Hbm].
+ pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc W memc mdc b m cid pos HAR Hbm Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
+ pose proof (sep_block_frame_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m cid pos HAR2 Hbm Hin2) as Hd. rewrite Efa in Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- exact HDa.
- destruct Hr as [Hr|Hr]; zlia. }
split; [exact Hgone|]. split; [exact Hpres2|]. split; [exact Hstk|]. split; [|split; [exact HQT2 | exact HW]].
{   intros a HXa He.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
pose proof (LEXT lyc Sc Hpc W memc mdc a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
pose proof (LEXT ly2 S2 Hp2 W2 mem2 md2 a HAR2 ltac:(rewrite Eextra; exact HXa)) as (Yo & Yb & _).
apply KEEP.
- exact Xo.
- exact Yo.
- intros Hs. apply Xs. zlia.
- exact He.
- intros Heb. destruct (HE a Heb) as [Hx | (b & m & [Hbm|Hbm] & Hr & _)];
[exact (proj2 (proj2 (proj2 (proj2 (proj2 (XWP a Hx))))) HXa) | exact (Xb b m Hbm Hr) | exact (Yb b m Hbm Hr)].
- exact (D5 a HXa).
- unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. zlia. }
Qed.

(* cgif YCbq.v:858 call_effect_journal (released :856); the post ghost set Hp2 is free, the journal is at PST = [],
   and the call may also write an extra set XW (cf: the error-message buffer) outside every block, frame, image byte
   and extra area, below alloc_ceiling in application memory. The call's budget WS: the wild traces it stored are
   among WS (an allocator call: its own trace, from the model law's depot step). call_effect_journal_xwR at wle, with
   no further exception. *)
Lemma call_effect_journal_xw : forall stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb XW : Z -> Prop) FP1 nf k1 WS,
ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> wle W W2 -> same_io mdc md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ ascratch B stk regs a -> ~ Eb a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
ARx lyc Sc Hpc W memc mdc ->
astk_ok stk lyc (spZ regs) ->
frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, XW a -> a < alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
(forall p n, In (p, n) (ablocks B lyc Sc) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
~ Exists (in_zr a) (ly_extra lyc)) ->
(forall a, Eb a -> XW a \/ exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
incl (wild_part (as_universe B) (st_depot S2)) (wild_part (as_universe B) (st_depot Sc) ++ WS) ->
ajournal_xw segs B [] ARx stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS.
Proof.
intros stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb XW FP1 nf k1 WS
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2 HW.
exact (call_effect_journal_xwR (@wle segs) (fun _ => False) stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb XW
FP1 nf k1 WS HAR2 Hly2 Hwle2 Hio2 (fun a H1 H2 H3 H4 H5 _ => Hfr a H1 H2 H3 H4 H5) Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs
XWP HE Hgone HQT2 HW
(conj (fun _ _ H => H) (conj (fun _ _ _ _ _ H => H) (conj (fun _ _ H => H) (conj (fun _ _ _ _ _ H => H) (fun _ _ H => H)))))).
Qed.

(* cgif YCbq.v:858 call_effect_journal (released :856): call_effect_journal_xw with no extra write set. *)
Lemma call_effect_journal_x : forall stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb : Z -> Prop) FP1 nf k1 WS,
ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> wle W W2 -> same_io mdc md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ ascratch B stk regs a -> ~ Eb a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
ARx lyc Sc Hpc W memc mdc ->
astk_ok stk lyc (spZ regs) ->
frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, Eb a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
incl (wild_part (as_universe B) (st_depot S2)) (wild_part (as_universe B) (st_depot Sc) ++ WS) ->
ajournal_xw segs B [] ARx stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS.
Proof.
intros stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb FP1 nf k1 WS
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs HE Hgone HQT2 HW.
exact (call_effect_journal_xw stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb (fun _ => False) FP1 nf k1 WS
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs (fun a Hx => False_ind _ Hx) (fun a Ha => or_intror (HE a Ha))
Hgone HQT2 HW).
Qed.

(* cgif YCbq.v:958 acall_post_journal (released :956), with the extra write set XW of call_effect_journal_xw. *)
Lemma acall_post_journal_xw : forall lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 (Eb XW : Z -> Prop) FP1 k1 WS,
acall_post_x ASTACK lyc Sc Hpc W regs memc mdc Eb ly2 S2 W2 regs2 mem2 md2 ->
ARx lyc Sc Hpc W memc mdc ->
astk_ok ASTACK lyc (spZ regs) ->
frames S2 = frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, XW a -> a < alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
(forall p n, In (p, n) (ablocks B lyc Sc) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
~ Exists (in_zr a) (ly_extra lyc)) ->
(forall a, Eb a -> XW a \/ exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
incl (wild_part (as_universe B) (st_depot S2)) (wild_part (as_universe B) (st_depot Sc) ++ WS) ->
ajournal_xw segs B [] ARx ASTACK (spZ regs) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hpc W2 mem2 md2 k1 WS.
Proof.
intros lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 Eb XW FP1 k1 WS (HAR2 & Hly2 & Hwle2 & HP & Hio2 & Hfr & Hpres2)
HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2 HW.
exact (call_effect_journal_xw ASTACK lyc Sc Hpc W regs memc mdc ly2 S2 Hpc W2 mem2 md2 Eb XW FP1 [] k1 WS
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2 HW).
Qed.

(* cgif YCbq.v:958 acall_post_journal (released :956); Hp kept through the call. *)
Lemma acall_post_journal_x : forall lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 (Eb : Z -> Prop) FP1 k1 WS,
acall_post_x ASTACK lyc Sc Hpc W regs memc mdc Eb ly2 S2 W2 regs2 mem2 md2 ->
ARx lyc Sc Hpc W memc mdc ->
astk_ok ASTACK lyc (spZ regs) ->
frames S2 = frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, Eb a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
incl (wild_part (as_universe B) (st_depot S2)) (wild_part (as_universe B) (st_depot Sc) ++ WS) ->
ajournal_xw segs B [] ARx ASTACK (spZ regs) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hpc W2 mem2 md2 k1 WS.
Proof.
intros lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 Eb FP1 k1 WS (HAR2 & Hly2 & Hwle2 & HP & Hio2 & Hfr & Hpres2)
HAR Hstk Hfrs Hnev Hk1 Hsecs HE Hgone HQT2 HW.
eapply (call_effect_journal_x ASTACK lyc Sc Hpc W regs memc mdc ly2 S2 Hpc W2 mem2 md2 Eb FP1 [] k1 WS); try eassumption.
Qed.

(* POST_J at the plain post: call_effect_journal_xw on acall_post_x's conjuncts. *)
Lemma POST_J_x : apost_j_law (@wle segs) acall_post_x.
Proof.
intros lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2 Eb XW FP1 k1 WS (HAR2 & Hly2 & Hwle2 & _ & Hio2 & Hfr & Hpres2)
HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2 HW.
exact (call_effect_journal_xw ASTACK lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb XW FP1 [] k1 WS
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2 HW).
Qed.

(* acall_kept_of_journal_x over a call journal at any world relation R (acall_kept reads no world step) *)
Lemma acall_kept_of_journal_xR : forall (R : world segs -> world segs -> Prop)
stk sp1 FP1 nf lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 (E : Z -> Prop) {WS},
ajournal_xwR segs B [] ARx R stk sp1 FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
ARx lyc Sc Hpc W memc mdc ->
(forall a, inFP FP1 a -> E a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) -> In (b, m) (ablocks B ly2 S2)) ->
~ YI16.sink_open_fp FP1 ->
acall_kept_x lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof.
intros R stk sp1 FP1 nf lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 E WS HJ HAR HFE Hlive Hcl.
pose proof (ajxR_hi HJ) as G1. pose proof (ajxR_blk HJ) as G2. pose proof (ajxR_img HJ) as G3. pose proof (ajxR_frm HJ) as G4.
pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold acall_kept_x, acall_kept.
split; [exact G1|]. split.
{ intros b m i Hb Hi HnE. apply (G2 b m i Hb (Hlive b m i Hb Hi HnE) Hi). intros Hf. exact (HnE (HFE _ Hf)). }
split; [intros a Hi Hns He; exact (G3 a Hi Hns He (not_Exists_nil_zr a) (fp_spares_closed FP1 a Hcl))|]. split.
{ intros cid pos a Hin Hr HnE. apply (G4 cid pos a); [cbn; exact Hin | exact Hr | intros Hf; exact (HnE (HFE _ Hf))]. }
split; [|exact Hpres].
intros a Ha Hs Hp0. eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; [exact Ha | exact Hs] | exact Hp0].
Qed.

(* cgif YCbq.v:973 acall_kept_of_journal (released :971), over a call journal at PST = [] (any budget). *)
Lemma acall_kept_of_journal_x : forall stk sp1 FP1 nf lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 (E : Z -> Prop) {WS},
ajournal_xw segs B [] ARx stk sp1 FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
ARx lyc Sc Hpc W memc mdc ->
(forall a, inFP FP1 a -> E a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) -> In (b, m) (ablocks B ly2 S2)) ->
~ YI16.sink_open_fp FP1 ->
acall_kept_x lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof. exact (acall_kept_of_journal_xR (@wle segs)). Qed.

(* ---------------------------------------------------------------------------- *)
(* THE FREE RULES OVER R AND APOST: the callee's text realizes through amrealG R (afree_realizes_xR), and the rule  *)
(* reads the callee's post only through POST_AR and POST_J. The plain rules aj_free_at_x_ct / aj_free_x_ct are the   *)
(* case R := wle, APOST := acall_post_x (POST_AR_x, POST_J_x, afree_realizes_x_R).                                 *)
Section rR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Variable APOST : Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Hypothesis POST_AR : apost_ar_law APOST.
Hypothesis POST_J : apost_j_law R APOST.

(* cgif YCbq.v:992 aj_free_at (released :990), with the call's trace premise stated on call_trace itself: a tail call
   at a function's entry has it from that function's text even when the frame-pointer chain is not walkable. *)
Lemma aj_free_at_x_ctR : afree_realizes_xR R APOST ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA APOST lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (proj1 (in_ablocks B lyc Sc pa n) Hin) as (q & Hq & Hqin).
destruct (LBLK lyc Sc Hpc W memT mdc pa n HAR Hin) as (Hpa16 & Hpa4096 & Hpaceil & [Hpah Hpah2] & Hpab & _).
assert (Hqnn : q <> PNull) by (intros ->; cbn in Hq; zlia).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof Htr as Htr'.
pose proof (amx_free AMX Sc q n (call_trace lyc (pc_free_ra0 code) regsT ch) HWF (QMQ Sc memT HQM) (or_intror Hqin) Htr')
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AFREE lyc Sc Hpc W regsT memT mdc q n ch HPRE (or_intror Hqin) ltac:(rewrite Hq; exact Ha0)
ltac:(rewrite Hq; exact Hnhp) Htr') as HREAL.
eapply (SRrG_mono segs R).
{ exact (amrealG_SRrG04 segs R R_trans _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (amx_free_depot AMX Sc q n (call_trace lyc (pc_free_ra0 code) regsT ch) HWF (QMQ Sc memT HQM) (or_intror Hqin) Htr' tr r Hpath) as HDEP.
pose proof (HMP tr r Hpath) as HQ. destruct r as [[] S2]. unfold free_post_x in HQ. cbn [fst snd] in HQ, HDEP.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2)).
destruct Hsplit as [[Hnull _] | Hsplit]; [exfalso; exact (Hqnn Hnull)|].
cbn [fst snd] in *.
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2 & _).
destruct (POST_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) as (HAR2 & Hly2 & HP).
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Eab2 : ablocks B ly2 S2 = map fc l1 ++ map fc l2).
{ unfold ablocks. change (map f2 (blocks S2) = map fc l1 ++ map fc l2). rewrite Hbl2, map_app.
f_equal; apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
assert (EabC : ablocks B lyc Sc = map fc l1 ++ (pa, n) :: map fc l2).
{ unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n) :: map fc l2). rewrite Hsplit, map_app. cbn [map app].
replace (fc (q, n)) with (pa, n) by (subst fc; cbn [fst snd]; rewrite Hq; reflexivity). reflexivity. }
assert (Hlive : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (pa <= b + i < pa + req_size n) ->
In (b, m) (ablocks B ly2 S2)).
{ intros b m i Hb Hi HnE. rewrite Eab2. rewrite EabC in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]].
- apply in_or_app. left. exact Hb.
- exfalso. injection Hb as <- <-. apply HnE. zlia.
- apply in_or_app. right. exact Hb. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
inFP [(pa, pa + req_size n)] (p + i)).
{ intros p m i Hp0 Hnp Hi. exists (pa, pa + req_size n). split; [left; reflexivity|]. cbn [fst snd].
destruct (Z_lt_le_dec (p + i) pa) as [H1|H1]; [exfalso; apply Hnp; apply (Hlive p m i Hp0 Hi); zlia|].
destruct (Z_lt_le_dec (p + i) (pa + req_size n)) as [H2|H2]; [zlia|]. exfalso; apply Hnp; apply (Hlive p m i Hp0 Hi); zlia. }
assert (HJ1 : ajournal_xwR segs B [] ARx R ASTACK (spZ regsT) [(pa, pa + req_size n)] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2
mem2 md2 (st_nev S2 - st_nev Sc) [call_trace lyc (pc_free_ra0 code) regsT ch]).
{ refine (POST_J lyc Sc Hpc W regsT memT mdc ly2 S2 Hpc W2 regs2 mem2 md2 _ (fun _ => False) [(pa, pa + req_size n)]
    (st_nev S2 - st_nev Sc) [call_trace lyc (pc_free_ra0 code) regsT ch] HPOST HAR HstkC Hfrs2 ltac:(zlia) ltac:(zlia)
    Hsecs2 (fun a Hx => False_ind _ Hx) _ HgoneC HQT2 (wild_part_step _ _ _ _ HDEP)).
  intros a [_ Ha]. rewrite Hq in Ha. right. exists pa, n. split; [left; exact Hin|]. split; [exact Ha|]. left.
  exists (pa, pa + req_size n). split; [left; reflexivity | cbn; zlia]. }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low R R_trans);
[exact HJ | exact (ajournal_xwR_nil_pst R PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n) (ablocks B ly S)) as [H0|H0].
- left. replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right; left. exists pa, n. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|].
split; [exists (map fc l1), (map fc l2); split; [exact EabC | exact Eab2]|].
split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr'|].
split; [exists q, tr; split; [exact Hq|]; split; [exact Hqin|]; split; [exact Hpath|]; split; [exact Hgf | exact Hleaf0]|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal_xR R); [exact HJ1 | exact HAR | | exact Hlive | apply sink_closed_pos; constructor; [cbn [fst]; zlia | constructor]].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. exact Ha.
Qed.

(* aj_free_x_ct over R and APOST: the rule at a symbolic state reaching the free wrapper. *)
Lemma aj_free_x_ctR : afree_realizes_xR R APOST ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA APOST lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch
HS Hpcs Hrv HJ Hin Hnhp Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply aj_free_at_x_ctR; eassumption.
Qed.
(* aj_free_at_x over R and APOST (the call_trace0 form); aj_free_at_x is its case R := wle, APOST := acall_post_x *)
Lemma aj_free_at_xR : afree_realizes_xR R APOST ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA APOST lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
exact (aj_free_at_x_ctR AFREE W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch (admits_call_trace0 _ lyc _ regsT ch Sc (proj2 UNIV0) Htr) HFP).
Qed.

(* aj_free_x over R and APOST (the call_trace0 form at a symbolic state); aj_free_x is its case R := wle, APOST := acall_post_x *)
Lemma aj_free_xR : afree_realizes_xR R APOST ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA APOST lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch
HS Hpcs Hrv HJ Hin Hnhp Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply aj_free_at_xR; eassumption.
Qed.

End rR.

(* cgif YCbq.v:992 aj_free_at (released :990), with the call's trace premise stated on call_trace itself: a tail call
   at a function's entry has it from that function's text even when the frame-pointer chain is not walkable.
   aj_free_at_x_ctR at wle and acall_post_x. *)
Lemma aj_free_at_x_ct : afree_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS.
exact (aj_free_at_x_ctR (@wle segs) (wle_trans segs) acall_post_x POST_AR_x POST_J_x (afree_realizes_x_R AFREE)).
Qed.

(* cgif YCbq.v:992 aj_free_at (released :990): the trace premise in cgif's call_trace0 form. *)
Lemma aj_free_at_x : afree_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS.
exact (aj_free_at_xR (@wle segs) (wle_trans segs) acall_post_x POST_AR_x POST_J_x (afree_realizes_x_R AFREE)).
Qed.

(* The XS write set of a malloc call: its pre extents and its post extents, at the pre state's blocks, frames
   and extra areas (ARx_xs_law at both states, the layout law, and the call's block / frame growth). *)
Lemma Exists_app_or_zr : forall a l1 l2, Exists (in_zr a) (l1 ++ l2) -> Exists (in_zr a) l1 \/ Exists (in_zr a) l2.
Proof.
intros a l1 l2 H. apply Exists_exists in H as (x & Hx & Ha). apply in_app_or in Hx as [Hx|Hx]; [left | right];
apply Exists_exists; exists x; split; assumption.
Qed.
Lemma xs_write_ok : forall lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 a,
ARx lyc Sc Hpc W memc mdc -> ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 ->
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2)) -> (forall f, In f (frames Sc) -> In f (frames S2)) ->
Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2) ->
a < alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
(forall p n, In (p, n) (ablocks B lyc Sc) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
~ Exists (in_zr a) (ly_extra lyc).
Proof.
intros lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 a HAR HAR2 Hly2 Hab Hfr HX.
destruct (Exists_app_or_zr a _ _ HX) as [HX1 | HX2].
- exact (XSL lyc Sc Hpc W memc mdc a HAR HX1).
- destruct (XSL ly2 S2 Hp2 W2 mem2 md2 a HAR2 HX2) as (Xc & Xa & Xi & Xb & Xf & Xe).
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
split; [exact Xc|]. split; [exact Xa|]. split; [exact Xi|].
split; [intros p n Hin; exact (Xb p n (Hab _ Hin))|].
split; [intros cid pos Hin; rewrite <- Efa; exact (Xf cid pos (Hfr _ Hin))|].
rewrite <- Eextra. exact Xe.
Qed.


(* aj_malloc_at_x_ct over a journal at a reflexive and transitive world relation R that contains wle: the callee text is the
   plain one (a malloc re-hides nothing), so the call's own journal is at wle and enters the caller's by R_wle and
   transitivity; aj_malloc_at_x_ct is its case R := wle *)
Lemma aj_malloc_at_x_ctR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
amalloc_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros R R_refl R_trans R_wle AMALLOC WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof Htr as Htr'.
pose proof (amx_malloc AMX Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF (QMQ Sc memT HQM) Hn Hlive Htr')
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AMALLOC lyc Sc Hpc W regsT memT mdc n ch HPRE Ha0 Hn Hlive Htr') as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (amx_malloc_depot AMX Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF (QMQ Sc memT HQM) Hn Hlive Htr' tr r Hpath) as HDEP.
pose proof (HMP tr r Hpath) as HQ. destruct r as [p S2]. unfold malloc_post_x in HQ. cbn [fst snd] in HDEP.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & Hbl).
pose proof Hleaf as Hleaf0.
cbn [fst snd] in Hleaf.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2 & HERR & _).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
destruct (asptr_null_dec p) as [-> | Hnn].
-
cbn in Hres.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Hbl. apply map_ext_in. exact Efc. }
assert (HJ1 : ajournal_xw segs B [] ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc) [call_trace lyc (pc_malloc_ra0 code) regsT ch]).
{ eapply (acall_post_journal_xw lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2
 | exact (wild_part_step _ _ _ _ HDEP)].
- intros a Ha. apply (xs_write_ok lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b' Hb'; rewrite Eab2; exact Hb' | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[Hf _] | Hx]; [exfalso; exact (Hf eq_refl) | left; exact Hx].
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low R R_trans);
[exact HJ | exact (ajournal_xwR_nil_pst R PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (ajournal_xwR_mono segs B [] ARx (@wle segs) R R_wle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1)) | zlia | zlia
| intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr'|].
split; [exists PNull, tr; split; [exact Hpath|]; split; [exact Hgf|]; split; [exact Hleaf0|];
split; [split; intros _; reflexivity | intros Hc; exfalso; exact (Hc eq_refl)]|].
left. split; [reflexivity|]. split; [exact Eab2|].
split.
{ rewrite Hsp' in HJ1. eapply acall_kept_of_journal_x; [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
exact (HERR eq_refl).
-
assert (Hbl' : blocks S2 = blocks Sc ++ [(p, n)]).
{ destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
clear Hbl.
set (res := sptr_addr B ly2 p) in *.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl', map_app. cbn [map].
f_equal. apply map_ext_in. exact Efc. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (LBLK ly2 S2 Hpc W2 mem2 md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos_x ly2 S2 Hpc W2 mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal_xw segs B [] ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc) [call_trace lyc (pc_malloc_ra0 code) regsT ch]).
{ eapply (acall_post_journal_xw lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2
 | exact (wild_part_step _ _ _ _ HDEP)].
- intros a Ha. apply (xs_write_ok lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b' Hb'; rewrite Eab2; apply in_or_app; left; exact Hb' | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[_ Ha] | Hx]; [right | left; exact Hx].
exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res n a Hold Ha Ha).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_xw_subR segs B PST ARx LAWS segs_low R R_trans);
[exact HJ | exact (ajournal_xwR_nil_pst R PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (ajournal_xwR_mono segs B [] ARx (@wle segs) R R_wle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1)) | zlia | zlia
| intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr'|].
split; [exists p, tr; split; [exact Hpath|]; split; [exact Hgf|]; split; [exact Hleaf0|];
split; [split; [intros Hc; exfalso; exact (Hnn Hc) | intros Hc; zlia] | intros _; reflexivity]|].
right. split; [exact Hr4096|]. split; [exact Eab2|].
rewrite Hsp' in HJ1. eapply acall_kept_of_journal_x; [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.

(* cgif YCbq.v:1354 aj_malloc_at (released :1352), with the trace premise on call_trace; on BOTH arms the post also
   carries the call's pre, its trace in the universe, the granted model path to (p, S2) and the leaf at (p, S2), with
   p = PNull exactly on the res = 0 arm; the res = 0 arm adds the wrapper's NULL-path stores at the post memory. *)
Lemma aj_malloc_at_x_ct : amalloc_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (aj_malloc_at_x_ctR (@wle segs) (wle_refl segs) (wle_trans segs) (fun _ _ H => H)). Qed.

(* aj_malloc_at_x over a journal at a reflexive and transitive world relation R that contains wle: the callee text is the
   plain one (a malloc re-hides nothing), so the call's own journal is at wle and enters the caller's by R_wle and
   transitivity; aj_malloc_at_x is its case R := wle *)
Lemma aj_malloc_at_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
amalloc_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros R R_refl R_trans R_wle AMALLOC WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
exact (aj_malloc_at_x_ctR R R_refl R_trans R_wle AMALLOC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch (admits_call_trace0 _ lyc _ regsT ch Sc (proj1 UNIV0) Htr)).
Qed.

(* cgif YCbq.v:1354 aj_malloc_at (released :1352): the trace premise in cgif's call_trace0 form. *)
Lemma aj_malloc_at_x : amalloc_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (aj_malloc_at_xR (@wle segs) (wle_refl segs) (wle_trans segs) (fun _ _ H => H)). Qed.

(* aj_malloc_x over a journal at a reflexive and transitive world relation R that contains wle: the callee text is the
   plain one (a malloc re-hides nothing), so the call's own journal is at wle and enters the caller's by R_wle and
   transitivity; aj_malloc_x is its case R := wle *)
Lemma aj_malloc_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
amalloc_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros R R_refl R_trans R_wle AMALLOC WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch
HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply (aj_malloc_at_xR R R_refl R_trans R_wle); eassumption.
Qed.

(* cgif YCbq.v:1717 aj_malloc (released :1715): the rule at a symbolic state reaching the malloc wrapper. *)
Lemma aj_malloc_x : amalloc_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (aj_malloc_xR (@wle segs) (wle_refl segs) (wle_trans segs) (fun _ _ H => H)). Qed.

(* aj_malloc_x_ct over a journal at a reflexive and transitive world relation R that contains wle: the callee text is the
   plain one (a malloc re-hides nothing), so the call's own journal is at wle and enters the caller's by R_wle and
   transitivity; aj_malloc_x_ct is its case R := wle *)
Lemma aj_malloc_x_ctR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
amalloc_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros R R_refl R_trans R_wle AMALLOC WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch
HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply (aj_malloc_at_x_ctR R R_refl R_trans R_wle); eassumption.
Qed.

(* aj_malloc_x with the trace premise on call_trace (aj_malloc_at_x_ct). *)
Lemma aj_malloc_x_ct : amalloc_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (aj_malloc_x_ctR (@wle segs) (wle_refl segs) (wle_trans segs) (fun _ _ H => H)). Qed.

(* cgif YCbq.v:2111 aj_free (released :2109): the rule at a symbolic state reaching the free wrapper. *)
Lemma aj_free_x : afree_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS.
exact (aj_free_xR (@wle segs) (wle_trans segs) acall_post_x POST_AR_x POST_J_x (afree_realizes_x_R AFREE)).
Qed.

(* aj_free_x with the trace premise on call_trace (aj_free_at_x_ct); a tail call at entry uses it at o = 0. *)
Lemma aj_free_x_ct : afree_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS.
exact (aj_free_x_ctR (@wle segs) (wle_trans segs) acall_post_x POST_AR_x POST_J_x (afree_realizes_x_R AFREE)).
Qed.
End r.
End gx.
