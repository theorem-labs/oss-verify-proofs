(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* CARRIED from this tree's proofs/plugin-hostd/fuzz_reply/lib/Reusable/YGcallx.v, sha256 1dd2a7cdc3eec31be1d3a34115f09ab1f4a35139d5037583f209733bb980f322
   (that file is carried from commit a0fed4266a1b18b1453af093bfe2ee477dcbe241, proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallx.v).
   Re-pointed for lib/B (fuzz_reply.asan-ubsan): each Require of a module that lib/B instantiates now names lib/B's
   module (lib/B/YCbq.v, the instance whose off_img cites YImgTop.IMG_TOP_B; lib/B/YCbqG.v, this carry's own lib/B
   copy).
   The exact changes (`lib.` is OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.; each source line is replaced
   by the lines after `->`, in that order):
   - line 104: `From lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.` -> `From lib.Reusable Require Import YM05 YI16 YG0p.` / `From lib.B Require Import YCbq YCbqG.`
   - line 109: `Unset Lia Cache. Unset Nia Cache.` -> `Local Unset Lia Cache. Local Unset Nia Cache.`
   The Unset Lia Cache / Unset Nia Cache line is made Local: a new file carries only Local settings.
   Nothing else changes: below this comment the bytes are the source's.
   DO NOT EDIT: change the source file on its branch, carry it again, and re-point it again. *)
(* CARRIED from commit a0fed4266a1b18b1453af093bfe2ee477dcbe241,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallx.v, sha256 c531b4318cac5569505a2813069e2cb68d8635cecac08335eca0c755f51e456d.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, round 6g; a Theorem Labs lane's approval (B'')): acall_pre_x's last conjunct is
   `QMm S mem`, a NEW Section Variable that sees the call memory (cf: acall_pre_cf's trailing conjuncts, which since the
   cf layer's field round 3 end with arodata_ok_cf on the memory; part 3c dropped memnorm). QM stays the state predicate of the model
   laws (alloc_model_laws_x) and the rules; Hypothesis QMQ : QMm S mem -> QM S beside AMX links them. The eight rules
   that BUILD the callee's acall_pre_x take `QMm Sc <call memory>` instead of `QM Sc`. Non-cf instances take
   QMm := fun S _ => QM S and QMQ := fun _ _ H => H. *)
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
      `blocks_bytes S + n <= LIVE_MAX`. cgif's originals: YG0d.v:238-289. ecall_pre_x (YG0d.v:290-296 over ARx) is
      NOT restated: it is the frame-class lane's frozen FCiface.v, imported.
      REUSED AS THEY STAND, because they name neither AR nor Wf: cfg_at, ascratch, chain_pre, call_trace (YG0d.v:218-230),
      acall_kept (YCbq.v:825, here acall_kept_x), api_env (YCbq.v:809), in_ablocks (:836), map_eq_In (:853),
      asptr_null_dec (:1352), call_trace_in (:319), and YCbqG.v's ajournal_x, ajournal_x_sub, blk_img_x, frm_img_x,
      sep_blocks_x, sep_block_frame_x, frames_bounds_x.

   2. THE MODEL LAWS (alloc_model_laws_x): what cgif's call-site rules take from model_laws (YG0d.v:525, ml_malloc /
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
      aj_free_at :990, aj_malloc_at :1352, aj_malloc :1715, aj_free :2109; the model laws are YG0d.v:525 model_laws.
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
      (h) every arm of the malloc and free rules adds, at the call's state, acall_pre_x, the call trace in the
          universe, the model path (`apath (mt n trace Sc) trc (p, S2)`, free: `apath (ft q trace Sc) trc (tt, S2)`)
          with every ask granted (`gflag trc = true`, from amreal_SRr04, YG0d.v:190, where cgif's rule uses
          amreal_SRr), and the leaf at that result (malloc: with `p = PNull <-> res = 0` and, off NULL,
          `res = sptr_addr B ly2 p`; free: with `sptr_addr B lyc q = pa` and `In (q, n) (blocks Sc)`), so a text can
          derive the instance's refusal post (YG0dcf.v malloc_cf_null_post) and the room after the call from them;
      (j) malloc_leaf_x's frame exception adds the extents `XS ly S ++ XS ly' S'` (cf: the error-message buffer, xs_cf):
          a refused malloc may write them. The call journal then takes them as an extra write set (call_effect_journal_xw
          / acall_post_journal_xw; the _x forms are the case of an empty set), with the AR law ARx_xs_law below;
      (k) malloc_leaf_x also states the wrapper's NULL-path stores, errno = 12 (ENOMEM) and the out-of-memory byte = 1
          (as malloc_leaf_cf does), and the rule's res = 0 arm exposes them at the post memory;
      (i) each rule has a twin suffixed _ct whose trace premise is `In (call_trace lyc pc0 regsT ch) U` instead of
          cgif's `In (call_trace0 pc0 regsT ch) U` (the only use of that premise is call_trace_in, YCbq.v:320): a tail
          call at a function's entry has the call_trace form from that function's text even when frame0_ok fails.
          The _ct lemmas carry the proofs; the call_trace0 forms are their corollaries.
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
      :141); ret_ok raw and 4096 <= raZ come from afn_pre_x, chain_pre from achain_chain_pre (YCbq.v:282) at the entry
      sp and s0, the trace premise from the text's `In (call_trace ly (pc_free_ra0 _) regs ch) _`. The rule asks
      nothing a tail call cannot give.

   Numerals: 1, 2, 3, 4, 10 are RISC-V register numbers and 12 (ENOMEM) / 1 (the out-of-memory byte) are stored values
   (WORD); 0, 16 (stack alignment), 4096 (cgif's lowest block address), 16384 (= ASTACK, YG0d.v:23) and 2 ^ 64 are
   LENGTH / DERIVED constants of cgif's rules. No ADDRESS. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH.
(* ecall_pre_x is the frame-class lane's (FCiface.v, frozen); it is not restated here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section gx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* the room / live-count conjuncts the allocator call carries on its state (cf: qmeter_cf, the live-secondary
   bound and ERRB_ROOM, YG0dcf.v:54-229) *)
Variable QM : astate -> Prop.
(* the call's trailing conjuncts on the state AND the call memory (cf: acall_pre_cf's, which end with
   arodata_ok_cf on mem since the layer's field round 3); used ONLY in acall_pre_x. Non-cf: fun S _ => QM S. *)
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
(* 1. The call forms: YG0dcf.v:46-331 over ARx and QM.                            *)
Definition acall_pre_x (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
ARx ly S Hp W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ASTACK <= spZ regs /\ ly_bot ly + ACALL_PREFIX < spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch /\
QMm S mem.

Definition acall_post_xR (R : world segs -> world segs -> Prop) (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARx ly' S' Hp W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ R W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).
Definition acall_post_x (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARx ly' S' Hp W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).
(* acall_post_x keeps its body, for the proofs that unfold it; acall_post_x_wle checks that it is acall_post_xR at wle *)
Lemma acall_post_x_wle : acall_post_x = acall_post_xR (@wle segs). Proof. reflexivity. Qed.

Definition malloc_leaf_xR (R : world segs -> world segs -> Prop) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
(acall_post_xR R) ASTACK ly S Hp W regs mem md
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
(* malloc_leaf_x keeps its body, for the proofs that unfold it; malloc_leaf_x_wle checks that it is malloc_leaf_xR at wle *)
Lemma malloc_leaf_x_wle : malloc_leaf_x = malloc_leaf_xR (@wle segs). Proof. reflexivity. Qed.

Definition amalloc_realizes_xR (R : world segs -> world segs -> Prop) : Prop :=
forall ly S Hp W regs mem md n ch,
acall_pre_x ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < nmax -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly (pc_malloc_ra0 code) regs ch) S ->
amrealG segs R (mt n (call_trace ly (pc_malloc_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_malloc code) regs mem md)
((malloc_leaf_xR R) ly S Hp W regs mem md n).
Definition amalloc_realizes_x : Prop :=
forall ly S Hp W regs mem md n ch,
acall_pre_x ly S Hp W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < nmax -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly (pc_malloc_ra0 code) regs ch) S ->
amreal segs (mt n (call_trace ly (pc_malloc_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_malloc code) regs mem md)
(malloc_leaf_x ly S Hp W regs mem md n).
(* amalloc_realizes_x keeps its body, for the proofs that unfold it; amalloc_realizes_x_wle checks that it is amalloc_realizes_xR at wle *)
Lemma amalloc_realizes_x_wle : amalloc_realizes_x = amalloc_realizes_xR (@wle segs). Proof. reflexivity. Qed.

Definition free_leaf_xR (R : world segs -> world segs -> Prop) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
(acall_post_xR R) ASTACK ly S Hp W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
qtight (snd r) /\
(* YG0dcf.v free_leaf_cf's last two conjuncts: errno kept (raw), the raw frame *)
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
 mem' x = mem x).
Definition free_leaf_x (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_x ASTACK ly S Hp W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
qtight (snd r) /\
(* YG0dcf.v free_leaf_cf's last conjuncts: errno kept (raw), the raw frame (part 3c: no memnorm keep) *)
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
 mem' x = mem x).
(* free_leaf_x keeps its body, for the proofs that unfold it; free_leaf_x_wle checks that it is free_leaf_xR at wle *)
Lemma free_leaf_x_wle : free_leaf_x = free_leaf_xR (@wle segs). Proof. reflexivity. Qed.

Definition afree_realizes_xR (R : world segs -> world segs -> Prop) : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_x ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 code) regs ch) S ->
amrealG segs R (ft p (call_trace ly (pc_free_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_free code) regs mem md)
((free_leaf_xR R) ly S Hp W regs mem md p n).
Definition afree_realizes_x : Prop :=
forall ly S Hp W regs mem md p n ch,
acall_pre_x ly S Hp W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 code) regs ch) S ->
amreal segs (ft p (call_trace ly (pc_free_ra0 code) regs ch) S) W
(cfg_at segs (pc_wrap_free code) regs mem md)
(free_leaf_x ly S Hp W regs mem md p n).
(* afree_realizes_x keeps its body, for the proofs that unfold it; afree_realizes_x_wle checks that it is afree_realizes_xR at wle *)
Lemma afree_realizes_x_wle : afree_realizes_x = afree_realizes_xR (@wle segs). Proof. reflexivity. Qed.
(* route R: a post / leaf / realization at wle is one at any R that contains wle (the realization by amreal_amrealG,
   Reusable/YG0dH.v:165, and amrealG_mono); a RE-HIDING realization is not of this form (its frame also excludes the dead
   set): its crossing goes through call_effect_journal_rh_cf (lib/A|B/AjxCallRh.v) *)
Lemma acall_post_xR_of_x {R : world segs -> world segs -> Prop} (WLE_R : forall W W', wle W W' -> R W W') :
  forall stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
  acall_post_x stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
  acall_post_xR R stk ly S Hp W regs mem md E ly' S' W' regs' mem' md'.
Proof.
intros stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' (H1 & H2 & H3 & H4).
exact (conj H1 (conj H2 (conj (WLE_R _ _ H3) H4))).
Qed.
Lemma malloc_leaf_xR_of_x {R : world segs -> world segs -> Prop} (WLE_R : forall W W', wle W W' -> R W W') :
  forall ly S Hp W regs mem md n r W' c',
  malloc_leaf_x ly S Hp W regs mem md n r W' c' -> malloc_leaf_xR R ly S Hp W regs mem md n r W' c'.
Proof.
intros ly S Hp W regs mem md n r W' c' (ly' & regs' & mem' & md' & Hc & HP & Hrest).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [|exact Hrest].
exact (acall_post_xR_of_x WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.
Lemma free_leaf_xR_of_x {R : world segs -> world segs -> Prop} (WLE_R : forall W W', wle W W' -> R W W') :
  forall ly S Hp W regs mem md p n r W' c',
  free_leaf_x ly S Hp W regs mem md p n r W' c' -> free_leaf_xR R ly S Hp W regs mem md p n r W' c'.
Proof.
intros ly S Hp W regs mem md p n r W' c' (ly' & regs' & mem' & md' & Hc & HP & Hrest).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [|exact Hrest].
exact (acall_post_xR_of_x WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.
Lemma amalloc_realizes_xR_of_x {R : world segs -> world segs -> Prop} (WLE_R : forall W W', wle W W' -> R W W') :
  amalloc_realizes_x -> amalloc_realizes_xR R.
Proof.
intros AM ly S Hp W regs mem md n ch H1 H2 H3 H4 H5.
eapply amrealG_mono; [|eapply amreal_amrealG; [exact WLE_R | exact (AM ly S Hp W regs mem md n ch H1 H2 H3 H4 H5)]].
intros r W' c' HL. exact (malloc_leaf_xR_of_x WLE_R _ _ _ _ _ _ _ _ r W' c' HL).
Qed.
Lemma afree_realizes_xR_of_x {R : world segs -> world segs -> Prop} (WLE_R : forall W W', wle W W' -> R W W') :
  afree_realizes_x -> afree_realizes_xR R.
Proof.
intros AF ly S Hp W regs mem md p n ch H1 H2 H3 H4 H5.
eapply amrealG_mono; [|eapply amreal_amrealG; [exact WLE_R | exact (AF ly S Hp W regs mem md p n ch H1 H2 H3 H4 H5)]].
intros r W' c' HL. exact (free_leaf_xR_of_x WLE_R _ _ _ _ _ _ _ _ _ r W' c' HL).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The model laws the rules read (cgif's model_laws, YG0d.v:525).              *)
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
   own token; YGcallcf.v alloc_model_laws_x_cf does that from atok_cf. *)
Record alloc_model_laws_x : Prop := {
amx_malloc : forall s n tr, WFx s -> QM s -> 0 <= n < nmax -> blocks_bytes s + n <= LIVE_MAX ->
admits (as_universe B) tr s ->
asafe (mt n tr s) /\ agprog (mt n tr s) /\ is_spin (mt n tr s) = false /\
(forall tr' r, apath (mt n tr s) tr' r -> malloc_post_x s n r);
amx_free : forall s p n tr, WFx s -> QM s -> (p = PNull \/ In (p, n) (blocks s)) -> admits (as_universe B) tr s ->
asafe (ft p tr s) /\ agprog (ft p tr s) /\ is_spin (ft p tr s) = false /\
(forall tr' r, apath (ft p tr s) tr' r -> free_post_x s p n r)
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

(* cgif's acall_kept (YCbq.v:825) as it stands: it names neither AR nor Wf. *)
Definition acall_kept_x (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
(W2 : world segs) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
acall_kept segs B lyc Sc W memc W2 mem2 slo shi E.

Lemma not_Exists_nil_zr : forall a, ~ Exists (in_zr a) [].
Proof. intros a H. inversion H. Qed.

(* A journal whose image clause exempts nothing is one at any PST. *)
Lemma ajournal_x_nil_pstR {R : world segs -> world segs -> Prop} : forall P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_xR segs B [] ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_xR segs B P ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & REST).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|]. split; [exact F2|].
split; [|exact REST].
intros a Hi Hns He _ Hsp. exact (F3 a Hi Hns He (not_Exists_nil_zr a) Hsp).
Qed.
Lemma ajournal_x_nil_pst : forall P STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_x segs B [] ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_x segs B P ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. exact (@ajournal_x_nil_pstR (@wle segs)). Qed.

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
(* the universe's bounds (YG01.universe_ok): with it a rule turns its call trace's universe membership into the
   admission that the P'' realizes texts and model laws take (admits_fix) *)
Hypothesis UOK : universe_ok (as_universe B).
Let UNIV0 : In [pc_malloc_ra0 code] (as_universe B) /\ In [pc_free_ra0 code] (as_universe B) := proj2 (proj2 errno_low).
Let ERRIMG : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a := proj1 (proj2 errno_low).
Local Abbreviation LBLK := (alx_blocks segs B ARx LAWS).
Local Abbreviation LLAY := (alx_layout segs B ARx LAWS).
Local Abbreviation LFRS := (alx_frames segs B ARx LAWS).
Local Abbreviation LOIM := (alx_owned_image segs B ARx LAWS).
Local Abbreviation LSEP := (alx_sep segs B ARx LAWS).
Local Abbreviation LEXT := (alx_extra segs B ARx LAWS).

(* cgif YCbq.v:713 sep_blocks_pos (released :710) *)
Lemma sep_blocks_pos_x : forall ly S Hp W mem md x y l1 l2 l3,
ARx ly S Hp W mem md -> ablocks B ly S = l1 ++ x :: l2 ++ y :: l3 ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l1 l2 l3 HAR E.
destruct (LSEP ly S Hp W mem md HAR) as [Hq _]. apply pairwise_app_l in Hq as [Hq _].
rewrite E, !map_app in Hq. cbn in Hq. rewrite map_app in Hq. cbn in Hq.
exact (pairwise_In2 zdisjoint _ _ _ _ _ _ Hq eq_refl).
Qed.

(* cgif YCbq.v:859 call_effect_journal (released :856); the post ghost set Hp2 is free, the journal is at PST = [],
   and the call may also write an extra set XW (cf: the error-message buffer) outside every block, frame, image byte
   and extra area, below alloc_ceiling in application memory. *)
Lemma call_effect_journal_xwR {R : world segs -> world segs -> Prop} : forall stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb XW : Z -> Prop) FP1 nf k1,
ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> R W W2 -> same_io mdc md2 ->
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
ajournal_xR segs B [] ARx R stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1.
Proof.
intros stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb XW FP1 nf k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (KEEP : forall a, ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
~ (spZ regs - stk <= a < spZ regs) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ Eb a -> 0 <= a < 2 ^ 64 ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a H1 H2 H3 H4 H5 H6. apply (Hfr a H6 H1 H2); [|exact H5]. unfold ascratch. intros [H|H]; [exact (H3 H) | exact (H4 H)]. }
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
- zlia. }
split.
{   intros cid pos a Hin Hr Hnf.
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
- destruct Hr as [Hr|Hr]; zlia. }
split; [exact Hgone|]. split; [exact Hpres2|]. split; [exact Hstk|]. split; [|exact HQT2].
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
- unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. zlia. }
Qed.
Lemma call_effect_journal_xw : forall stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb XW : Z -> Prop) FP1 nf k1,
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
ajournal_x segs B [] ARx stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1.
Proof. exact (@call_effect_journal_xwR (@wle segs)). Qed.

(* cgif YCbq.v:859 call_effect_journal (released :856): call_effect_journal_xw with no extra write set. *)
Lemma call_effect_journal_xR {R : world segs -> world segs -> Prop} : forall stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb : Z -> Prop) FP1 nf k1,
ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 -> R W W2 -> same_io mdc md2 ->
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
ajournal_xR segs B [] ARx R stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1.
Proof.
intros stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb FP1 nf k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs HE Hgone HQT2.
exact (call_effect_journal_xwR stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb (fun _ => False) FP1 nf k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs (fun a Hx => False_ind _ Hx) (fun a Ha => or_intror (HE a Ha))
Hgone HQT2).
Qed.
Lemma call_effect_journal_x : forall stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb : Z -> Prop) FP1 nf k1,
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
ajournal_x segs B [] ARx stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1.
Proof. exact (@call_effect_journal_xR (@wle segs)). Qed.

(* cgif YCbq.v:959 acall_post_journal (released :956), with the extra write set XW of call_effect_journal_xw. *)
Lemma acall_post_journal_xwR {R : world segs -> world segs -> Prop} : forall lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 (Eb XW : Z -> Prop) FP1 k1,
(acall_post_xR R) ASTACK lyc Sc Hpc W regs memc mdc Eb ly2 S2 W2 regs2 mem2 md2 ->
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
ajournal_xR segs B [] ARx R ASTACK (spZ regs) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hpc W2 mem2 md2 k1.
Proof.
intros lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 Eb XW FP1 k1 (HAR2 & Hly2 & Hwle2 & HP & Hio2 & Hfr & Hpres2)
HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2.
exact (call_effect_journal_xwR ASTACK lyc Sc Hpc W regs memc mdc ly2 S2 Hpc W2 mem2 md2 Eb XW FP1 [] k1
HAR2 Hly2 Hwle2 Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2).
Qed.
Lemma acall_post_journal_xw : forall lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 (Eb XW : Z -> Prop) FP1 k1,
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
ajournal_x segs B [] ARx ASTACK (spZ regs) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hpc W2 mem2 md2 k1.
Proof. exact (@acall_post_journal_xwR (@wle segs)). Qed.

(* cgif YCbq.v:959 acall_post_journal (released :956); Hp kept through the call. *)
Lemma acall_post_journal_xR {R : world segs -> world segs -> Prop} : forall lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 (Eb : Z -> Prop) FP1 k1,
(acall_post_xR R) ASTACK lyc Sc Hpc W regs memc mdc Eb ly2 S2 W2 regs2 mem2 md2 ->
ARx lyc Sc Hpc W memc mdc ->
astk_ok ASTACK lyc (spZ regs) ->
frames S2 = frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, Eb a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
ajournal_xR segs B [] ARx R ASTACK (spZ regs) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hpc W2 mem2 md2 k1.
Proof.
intros lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 Eb FP1 k1 (HAR2 & Hly2 & Hwle2 & HP & Hio2 & Hfr & Hpres2)
HAR Hstk Hfrs Hnev Hk1 Hsecs HE Hgone HQT2.
eapply (call_effect_journal_xR ASTACK lyc Sc Hpc W regs memc mdc ly2 S2 Hpc W2 mem2 md2 Eb FP1 [] k1); try eassumption.
Qed.
Lemma acall_post_journal_x : forall lyc Sc Hpc W regs memc mdc ly2 S2 W2 regs2 mem2 md2 (Eb : Z -> Prop) FP1 k1,
acall_post_x ASTACK lyc Sc Hpc W regs memc mdc Eb ly2 S2 W2 regs2 mem2 md2 ->
ARx lyc Sc Hpc W memc mdc ->
astk_ok ASTACK lyc (spZ regs) ->
frames S2 = frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
(length (st_secs Sc) <= length (st_secs S2))%nat ->
(forall a, Eb a -> exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
(forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
qtight S2 ->
ajournal_x segs B [] ARx ASTACK (spZ regs) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hpc W2 mem2 md2 k1.
Proof. exact (@acall_post_journal_xR (@wle segs)). Qed.

(* cgif YCbq.v:974 acall_kept_of_journal (released :971), over a call journal at PST = []. *)
Lemma acall_kept_of_journal_xR {R : world segs -> world segs -> Prop} : forall stk sp1 FP1 nf lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 (E : Z -> Prop),
ajournal_xR segs B [] ARx R stk sp1 FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
ARx lyc Sc Hpc W memc mdc ->
(forall a, inFP FP1 a -> E a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) -> In (b, m) (ablocks B ly2 S2)) ->
~ YI16.sink_open_fp FP1 ->
acall_kept_x lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof.
intros stk sp1 FP1 nf lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 E
(HAR2 & Hly2 & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5 & HQT) HAR HFE Hlive Hcl.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold acall_kept_x, acall_kept.
split; [exact G1|]. split.
{ intros b m i Hb Hi HnE. apply (G2 b m i Hb (Hlive b m i Hb Hi HnE) Hi). intros Hf. exact (HnE (HFE _ Hf)). }
split; [intros a Hi Hns He; exact (G3 a Hi Hns He (not_Exists_nil_zr a) (fp_spares_closed FP1 a Hcl))|]. split.
{ intros cid pos a Hin Hr HnE. apply (G4 cid pos a); [cbn; exact Hin | exact Hr | intros Hf; exact (HnE (HFE _ Hf))]. }
split; [|exact Hpres].
intros a Ha Hs Hp0. eapply apresent_transfer; [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; [exact Ha | exact Hs] | exact Hp0].
Qed.
Lemma acall_kept_of_journal_x : forall stk sp1 FP1 nf lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 (E : Z -> Prop),
ajournal_x segs B [] ARx stk sp1 FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 ->
ARx lyc Sc Hpc W memc mdc ->
(forall a, inFP FP1 a -> E a) ->
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) -> In (b, m) (ablocks B ly2 S2)) ->
~ YI16.sink_open_fp FP1 ->
acall_kept_x lyc Sc W memc W2 mem2 (sp1 - stk) sp1 E.
Proof. exact (@acall_kept_of_journal_xR (@wle segs)). Qed.

(* cgif YCbq.v:993 aj_free_at (released :990), with the call's trace premise stated on call_trace itself: a tail call
   at a function's entry has it from that function's text even when the frame-pointer chain is not walkable. *)
Lemma aj_free_at_x_ctR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : (afree_realizes_xR R) ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc (pc_free_ra0 code) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_free_ra0 code) regsT ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
(free_leaf_xR R) lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
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
pose proof (admits_fix _ _ Sc UOK Htr) as Htr'.
pose proof (amx_free AMX Sc q n (call_trace lyc (pc_free_ra0 code) regsT ch) HWF (QMQ Sc memT HQM) (or_intror Hqin) Htr')
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AFREE lyc Sc Hpc W regsT memT mdc q n ch HPRE (or_intror Hqin) ltac:(rewrite Hq; exact Ha0)
ltac:(rewrite Hq; exact Hnhp) Htr') as HREAL.
eapply SRrG_mono.
{ exact (amrealG_SRrG04 segs R R_trans _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (HMP tr r Hpath) as HQ. destruct r as [[] S2]. unfold free_post_x in HQ. cbn [fst snd] in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2)).
destruct Hsplit as [[Hnull _] | Hsplit]; [exfalso; exact (Hqnn Hnull)|].
cbn [fst snd] in *.
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2 & _).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
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
assert (HJ1 : ajournal_xR segs B [] ARx R ASTACK (spZ regsT) [(pa, pa + req_size n)] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply acall_post_journal_xR; [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | exact HgoneC | exact HQT2].
intros a [_ Ha]. rewrite Hq in Ha. exists pa, n. split; [left; exact Hin|]. split; [exact Ha|]. left.
exists (pa, pa + req_size n). split; [left; reflexivity | cbn; zlia]. }
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at, raZ. rewrite Hra. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R_trans); [exact HJ | exact (ajournal_x_nil_pstR PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n) (ablocks B ly S)) as [H0|H0].
- left. replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right; left. exists pa, n. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|].
split; [exists (map fc l1), (map fc l2); split; [exact EabC | exact Eab2]|].
split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr|].
split; [exists q, tr; split; [exact Hq|]; split; [exact Hqin|]; split; [exact Hpath|]; split; [exact Hgf | exact Hleaf0]|].
rewrite Hsp' in HJ1.
eapply acall_kept_of_journal_xR; [exact HJ1 | exact HAR | | exact Hlive | apply sink_closed_pos; constructor; [cbn [fst]; zlia | constructor]].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. exact Ha.
Qed.
Lemma aj_free_at_x_ct : afree_realizes_x ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc (pc_free_ra0 code) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_free_ra0 code) regsT ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof. exact (@aj_free_at_x_ctR (@wle segs) (wle_trans segs)). Qed.

(* cgif YCbq.v:993 aj_free_at (released :990): the trace premise in cgif's call_trace0 form. *)
Lemma aj_free_at_xR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : (afree_realizes_xR R) ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_free_ra0 code) regsT ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
(free_leaf_xR R) lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
exact ((aj_free_at_x_ctR R_trans) AFREE W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch (call_trace_in lyc _ regsT ch _ (proj2 UNIV0) Htr) HFP).
Qed.
Lemma aj_free_at_x : afree_realizes_x ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_free_ra0 code) regsT ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_free_ra0 code) regsT ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof. exact (@aj_free_at_xR (@wle segs) (wle_trans segs)). Qed.

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


(* cgif YCbq.v:1355 aj_malloc_at (released :1352), with the trace premise on call_trace; on BOTH arms the post also
   carries the call's pre, its trace in the universe, the granted model path to (p, S2) and the leaf at (p, S2), with
   p = PNull exactly on the res = 0 arm; the res = 0 arm adds the wrapper's NULL-path stores at the post memory. *)
Lemma aj_malloc_at_x_ctR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : (amalloc_realizes_xR R) ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_malloc_ra0 code) regsT ch) (as_universe B) /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
(malloc_leaf_xR R) lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
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
pose proof (admits_fix _ _ Sc UOK Htr) as Htr'.
pose proof (amx_malloc AMX Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF (QMQ Sc memT HQM) Hn Hlive Htr')
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AMALLOC lyc Sc Hpc W regsT memT mdc n ch HPRE Ha0 Hn Hlive Htr') as HREAL.
eapply SRrG_mono.
{ exact (amrealG_SRrG04 segs R R_trans _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (HMP tr r Hpath) as HQ. destruct r as [p S2]. unfold malloc_post_x in HQ.
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
assert (HJ1 : ajournal_xR segs B [] ARx R ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_xwR lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a Ha. apply (xs_write_ok lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b' Hb'; rewrite Eab2; exact Hb' | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[Hf _] | Hx]; [exfalso; exact (Hf eq_refl) | left; exact Hx].
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R_trans);
[exact HJ | exact (ajournal_x_nil_pstR PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr|].
split; [exists PNull, tr; split; [exact Hpath|]; split; [exact Hgf|]; split; [exact Hleaf0|];
split; [split; intros _; reflexivity | intros Hc; exfalso; exact (Hc eq_refl)]|].
left. split; [reflexivity|]. split; [exact Eab2|].
split.
{ rewrite Hsp' in HJ1. eapply acall_kept_of_journal_xR; [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
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
assert (HJ1 : ajournal_xR segs B [] ARx R ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_xwR lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
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
eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R_trans);
[exact HJ | exact (ajournal_x_nil_pstR PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr|].
split; [exists p, tr; split; [exact Hpath|]; split; [exact Hgf|]; split; [exact Hleaf0|];
split; [split; [intros Hc; exfalso; exact (Hnn Hc) | intros Hc; zlia] | intros _; reflexivity]|].
right. split; [exact Hr4096|]. split; [exact Eab2|].
rewrite Hsp' in HJ1. eapply acall_kept_of_journal_xR; [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.
Lemma aj_malloc_at_x_ct : amalloc_realizes_x ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_malloc_ra0 code) regsT ch) (as_universe B) /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (@aj_malloc_at_x_ctR (@wle segs) (wle_trans segs)). Qed.

(* cgif YCbq.v:1355 aj_malloc_at (released :1352): the trace premise in cgif's call_trace0 form. *)
Lemma aj_malloc_at_xR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : (amalloc_realizes_xR R) ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_malloc_ra0 code) regsT ch) (as_universe B) /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
(malloc_leaf_xR R) lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
exact ((aj_malloc_at_x_ctR R_trans) AMALLOC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch (call_trace_in lyc _ regsT ch _ (proj1 UNIV0) Htr)).
Qed.
Lemma aj_malloc_at_x : amalloc_realizes_x ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
In (call_trace lyc (pc_malloc_ra0 code) regsT ch) (as_universe B) /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (@aj_malloc_at_xR (@wle segs) (wle_trans segs)). Qed.

(* cgif YCbq.v:1718 aj_malloc (released :1715): the rule at a symbolic state reaching the malloc wrapper. *)
Lemma aj_malloc_xR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : (amalloc_realizes_xR R) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
In (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
(malloc_leaf_xR R) lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros AMALLOC W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch
HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply (aj_malloc_at_xR R_trans); eassumption.
Qed.
Lemma aj_malloc_x : amalloc_realizes_x ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
In (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (@aj_malloc_xR (@wle segs) (wle_trans segs)). Qed.

(* aj_malloc_x with the trace premise on call_trace (aj_malloc_at_x_ct). *)
Lemma aj_malloc_x_ctR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : (amalloc_realizes_xR R) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
In (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
(malloc_leaf_xR R) lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros AMALLOC W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch
HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply (aj_malloc_at_x_ctR R_trans); eassumption.
Qed.
Lemma aj_malloc_x_ct : amalloc_realizes_x ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
In (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) (as_universe B) /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (@aj_malloc_x_ctR (@wle segs) (wle_trans segs)). Qed.

(* cgif YCbq.v:2112 aj_free (released :2109): the rule at a symbolic state reaching the free wrapper. *)
Lemma aj_free_xR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : (afree_realizes_xR R) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
In (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
(free_leaf_xR R) lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch
HS Hpcs Hrv HJ Hin Hnhp Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply (aj_free_at_xR R_trans); eassumption.
Qed.
Lemma aj_free_x : afree_realizes_x ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace0 (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
In (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof. exact (@aj_free_xR (@wle segs) (wle_trans segs)). Qed.

(* aj_free_x with the trace premise on call_trace (aj_free_at_x_ct); a tail call at entry uses it at o = 0. *)
Lemma aj_free_x_ctR {R : world segs -> world segs -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) : (afree_realizes_xR R) ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
In (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
(free_leaf_xR R) lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch
HS Hpcs Hrv HJ Hin Hnhp Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply (aj_free_at_x_ctR R_trans); eassumption.
Qed.
Lemma aj_free_x_ct : afree_realizes_x ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
In (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
In (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) (as_universe B) /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof. exact (@aj_free_x_ctR (@wle segs) (wle_trans segs)). Qed.
End r.
End gx.
