(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): the call predicate is
   QMm : astate -> (word -> option byte) -> Prop (YGcallx.v's QMm), used only to build acall_pre_x; the two rules take
   `QMm Sc <call memory>` instead of `QM Sc`. The realloc model law reads RQ, not QM, so nothing else changes. *)
(* Modified by Theorem Labs, 2026-10-30 (the realloc rules over a world relation R): realloc_leaf_xR (the leaf over a
   callee post APOST of acall_post_x's type), arealloc_realizes_xR (the text over the walk amrealG segs R, the leaf
   realloc_leaf_xR APOST and the realloc room RQ at the call, the premise the cgif layer's primed row
   YGcfInstReallocK.arealloc_realizes_cf_k needs), and Section rR's aj_realloc_at_xR / aj_realloc_xR (the journal
   ajournal_xwR R of YCbqG.v's R core, the step SRrG segs R, the post laws apost_ar_law / apost_j_law of YGcallx.v).
   realloc_leaf_x keeps its body (proofs destruct it) and realloc_leaf_xR is a copy of it over APOST, guarded by
   realloc_leaf_x_R_wle (realloc_leaf_x is realloc_leaf_xR at acall_post_x, by reflexivity); arealloc_realizes_x keeps
   its text and implies arealloc_realizes_xR at R := wle (arealloc_realizes_x_R_wle); aj_realloc_at_x / aj_realloc_x
   keep their statements and are the R rules at R := wle, APOST := acall_post_x (POST_AR_x, POST_J_x). *)
(* Theorem Labs, 2026-10: the REALLOC call-site rule, GENERIC over the allocator invariant ARx of YCbqG.v, in the form of
   YGcallx.v's malloc / free rules. No allocator instance, no image class, no address and no ledger is named here.

   1. THE TEXT OF RECORD: c-asan's parametric realloc, lib/Reusable/ReallocP.v (copied from
      proofs/cgif/cgif_rgb_fuzzer/lib/ReallocP.v at origin/cold/c-asan-realloc-primary b97c2fd1d44): realloc_tree_with,
      realloc_null_tree_with, mt_refused, arealloc_realizes_allP, arealloc_null_realizesP, cited, not restated.
      ReallocP.v defines its own gflag (the same fixpoint as YG0d.gflag); this file's statements name YG0d.gflag, the
      flag amreal_SRr04 exports, and mt_refused keeps ReallocP's.

   2. THE GENERIC INSTANCE (Section gr): the P forms at
        cpre  := acall_pre_x segs B ARx QMm at a fixed Hp (YGcallx.v; YG0dcf.v's acall_pre_cf at ARx := ARcf),
        rpre  := fun _ _ => True (no aregime), nmax := nmax, lmax := LIVE_MAX,
        U     := admits (as_universe B) (ReallocP.v's trace predicate on the trace and the state: YG01.v's admission,
                 the trace carrier's form, the internal file TRACE-CARRIER.md section 7; a Theorem Labs lane's cf texts take the same, YGcfRealloc.v),
        areal := amreal segs, mleaf := YGcallx.v's malloc_leaf_x at Hp,
        rleaf := realloc_leaf_x Hp, whose post carries YGcfNames.v's Hp effects (d) / (e):
          success (old block p freed, new block q): ARx at Hp' = remove p Hp, writes allowed on the new and the old
            block (YG0d.v malloc_leaf / free_leaf's E) and on the extents XS before and after (YGcallx.v's XS, cf: the
            error-message buffer xs_cf, as in malloc_leaf_cf), the first min (n_old, n) bytes of p copied to q;
          NULL: ARx at Hp, writes allowed only on the extents XS before and after besides the allocator and the scratch
            (so the old block's bytes are kept; its shadow follows from ARx at the same Hp with the block still live),
            a0 = 0, errno = 12 (the wrapper's SetErrnoOnNull) and the allocator's out-of-memory byte = 1 (AllocG.v's
            alloc_leaf at PNull, c615b709977; malloc_leaf_cf's NULL conjunct).
      arealloc_realizes_x is arealloc_realizes_allP (ReallocP.v:73-82) at these, written out, with rpre dropped and
      the freed base not hidden, ~ In (sptr_addr B ly p) Hp, after a0 (afree_realizes_x's premise and place,
      YGcallx.v:200-201; h-mani-a8's YGcfRealloc.v arealloc_realizes_cf takes it at the same place, :96-97): the
      harness shows a hidden head before it reallocates (fuzz_realloc's disown, alloc.c:97, before its realloc,
      alloc.c:98), so the base is never hidden at the call. arealloc_null_realizes_x is arealloc_null_realizesP at
      these as it stands (its old pointer is NULL).
      realloc_model_law_x is the model part of the realloc text, in the four-fact form of YGcallx.v's
      alloc_model_laws_x (cgif's model_laws, YG0d.v:514-518, has no realloc field; the facts are what atok gives through
      atok_asafe / atok_agprog / atok_nospin / atok_apath, so an instance proves them from its own atok, e.g. YGcfTok.v's
      atok_cf): from a WFx state with the realloc room RQ s n tr the realloc tree is safe, granted-progressing and not
      a spin, and every model path
      moves the blocks exactly: NULL keeps them, success turns l1 ++ (p, n_old) :: l2 into l1 ++ l2 ++ [(q, n)] (the
      free's list surgery after the malloc's append, YG01.v:449-461). RQ is a separate predicate on the state, the
      size and the trace, not QM: the inner free of the old block runs after the inner malloc, so an instance may need
      room at the post-malloc state (cf: h-mani-a8's amx_realloc_cf needs batch_room_cf there), which QM at the entry
      state does not give. At cf, RQ := qtight s /\ ROOM_cf_k s (RK_realloc + k), and RMX is h-mani-a8's amx_realloc_cf
      (YGcfAmx2.v), cited by YGcallRcf.v's realloc_model_law_x_cf.

   3. THE RULE (Section r): aj_realloc_at_x / aj_realloc_x, in cgif's aj_malloc_at shape (YCbq.v:1354, :1717; its x twin
      YGcallx.v aj_malloc_at_x / aj_malloc_x), with both arms. Differences from aj_malloc_at_x:
      (a) the call trace is the text's own premise `admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc`, and the
          rule is stated over the journal ajournal_xw at the caller's budget WS, the post at WS ++ [call trace]
          (YGcallx.v's (l));
      (b) the old block (pa, n_old) is live at the call, its base pa is not in the ghost set Hpc (aj_free_at_x's
          premise `~ In pa Hpc`, which the text arealloc_realizes_x takes) and, if live at the function's entry, it is
          in the footprint (aj_free_at_x's premise);
      (c) the journal counts st_nev S2 - st_nev Sc events, as YGcallx.v's rules do; the rule also takes the realloc
          room RQ Sc n (call_trace lyc pc0 regsT ch) at the call, for the model law;
      (d) the success arm's ghost set is remove pa Hpc, its blocks move EXACTLY as realloc_model_law_x says (not up to
          a Permutation), and it carries the copy;
      (e) BOTH arms carry, at the call's state, acall_pre_x, the trace in the universe, the old block's sptr p and the
          result's sptr q (q = PNull exactly when res = 0), the granted model path of the realloc tree to (q, S2)
          (amreal_SRr04's gflag), and realloc_leaf_x at (q, S2), so a caller reads model-level facts of the call (e.g.
          the room left after it) from its own lemmas; the NULL arm adds the P form's refusal witness mt_refused,
          errno 12 and the OOM byte.
      Section hypotheses: LAWS, segs_low, errno_low, OWNLOW, WFL, XSL (YGcallx.v's), and RMX : realloc_model_law_x. The
      realloc text arealloc_realizes_x enters as the rule's premise (the callee text), as amalloc_realizes_x does in
      YGcallx.v. xs_write_ok_except is YGcallx.v's xs_write_ok with an exception for the freed old block (the post
      extents may reuse its bytes). Every sink_head use is explicit (@ajournal_x rc SK ...).

   Numerals: 1, 2, 3, 4, 10, 11 in getr are RISC-V register numbers (WORD); 12 (ENOMEM) and 1 (the OOM byte's value)
   are WORD; 16 (stack alignment), 4096 (cgif's lowest block address), 16384 (= ASTACK, YG0d.v:18) and 2 ^ 64 are
   LENGTH constants of cgif's rules. No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 2. The generic instance over ARx.                                              *)
Section gr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* the call's trailing conjuncts on the state and the call memory (YGcallx.v's QMm, round 6g; non-cf: fun S _ => QM S) *)
Variable QMm : astate -> (word -> option byte) -> Prop.
(* the room the realloc model law needs, on the state, the request size and the trace (cf: qtight and the headroom
   ROOM_cf_k s (RK_realloc + k), the premises of h-mani-a8's amx_realloc_cf, YGcallRcf.v realloc_model_law_x_cf) *)
Variable RQ : astate -> Z -> list Z -> Prop.
(* the model malloc and its request bound, the model free, the model's state invariant (YGcallx.v's) *)
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
Variable WFx : astate -> Prop.
(* the extents an allocator call may write besides its blocks (YGcallx.v's XS; cf: the error-message buffer xs_cf) *)
Variable XS : alayout -> astate -> list (Z * Z).

(* The realloc leaf at a fixed ghost set Hp (YGcfNames.v's Hp effects (d) / (e) in the post). *)
Definition realloc_leaf_x (Hp : list Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\ qtight (snd r) /\
(fst r = PNull ->
 acall_post_x segs B ARx ASTACK ly S Hp W regs mem md (fun a => Exists (in_zr a) (XS ly S ++ XS ly' (snd r)))
   ly' (snd r) W' regs' mem' md' /\
 rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
(fst r <> PNull ->
 acall_post_x segs B ARx ASTACK ly S (remove Z.eq_dec (sptr_addr B ly p) Hp) W regs mem md
   (fun a => (sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) \/
             (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old) \/
             Exists (in_zr a) (XS ly S ++ XS ly' (snd r)))
   ly' (snd r) W' regs' mem' md' /\
 (forall i, 0 <= i < Z.min n_old n ->
   aview segs (w_H W') mem' (sptr_addr B ly' (fst r) + i) = aview segs (w_H W) mem (sptr_addr B ly p + i))) /\
(* YGcfRealloc.v realloc_leaf_cf's last two conjuncts: errno kept on success (raw), the raw frame *)
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ (fst r <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n_old)
    \/ Exists (in_zr (bv_unsigned x)) (XS ly S ++ XS ly' (snd r))) ->
 mem' x = mem x).

(* The same leaf over a callee post APOST of acall_post_x's type (YGcallx.v's apost_ar_law / apost_j_law read it): a
   COPY of realloc_leaf_x's body with acall_post_x segs B ARx replaced by APOST. realloc_leaf_x keeps its own body
   because proofs destruct a realloc_leaf_x hypothesis; realloc_leaf_x_R_wle (by reflexivity) checks that the two
   copies agree at APOST := acall_post_x. The cf rules over R take it at YGcallcf.v's APOST_cf, the post of a call
   that may re-hide (acall_post_cf_rh with the error-message buffer placed). *)
Definition realloc_leaf_xR
(APOST : (Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop))
(Hp : list Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\ qtight (snd r) /\
(fst r = PNull ->
 APOST ASTACK ly S Hp W regs mem md (fun a => Exists (in_zr a) (XS ly S ++ XS ly' (snd r)))
   ly' (snd r) W' regs' mem' md' /\
 rd32 (aview segs (w_H W') mem') (as_errno B) 12 /\ aview segs (w_H W') mem' (as_oom_byte B) = Some 1) /\
(fst r <> PNull ->
 APOST ASTACK ly S (remove Z.eq_dec (sptr_addr B ly p) Hp) W regs mem md
   (fun a => (sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) \/
             (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old) \/
             Exists (in_zr a) (XS ly S ++ XS ly' (snd r)))
   ly' (snd r) W' regs' mem' md' /\
 (forall i, 0 <= i < Z.min n_old n ->
   aview segs (w_H W') mem' (sptr_addr B ly' (fst r) + i) = aview segs (w_H W) mem (sptr_addr B ly p + i))) /\
(* YGcfRealloc.v realloc_leaf_cf's last two conjuncts: errno kept on success (raw), the raw frame *)
(fst r <> PNull -> forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= bv_unsigned x < sptr_addr B ly' (fst r) + req_size n)
    \/ (fst r <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n_old)
    \/ Exists (in_zr (bv_unsigned x)) (XS ly S ++ XS ly' (snd r))) ->
 mem' x = mem x).

Lemma realloc_leaf_x_R_wle : forall Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_x Hp ly S W regs mem md p n_old n r W' c' =
realloc_leaf_xR (acall_post_x segs B ARx) Hp ly S W regs mem md p n_old n r W' c'.
Proof. reflexivity. Qed.

(* The realloc text over ARx: arealloc_realizes_allP at cpre := acall_pre_x at Hp, lmax := LIVE_MAX, written out, with
   rpre := True dropped and the freed base not hidden, ~ In (sptr_addr B ly p) Hp, after a0 (afree_realizes_x's place;
   YGcfRealloc.v arealloc_realizes_cf's form). *)
Definition arealloc_realizes_x (pc pc0 : Z) : Prop :=
forall Hp ly S W regs mem md p n_old n ch,
acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < nmax -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly pc0 regs ch) S ->
amreal segs (realloc_tree_with mt ft p n (call_trace ly pc0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => realloc_leaf_x Hp ly S W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> mt_refused mt ft n (call_trace ly pc0 regs ch) S (snd r))).

(* The realloc text over a world relation R and a callee post APOST: arealloc_realizes_x's premises with the realloc
   room RQ S n (call trace) after acall_pre_x, the walk amrealG segs R (YG0dH.v; amreal' segs RZ is its instance at
   R := wle' segs RZ) and the leaf realloc_leaf_xR APOST. At the cf instance (YGcallRcf.v arealloc_realizes_x_cfR,
   R := wle' segs RZ_cf, APOST := APOST_cf, RQ := qtight /\ ROOM_cf_k (RK_realloc + k) /\ cf_hull_adm) it is the
   cgif layer's primed row YGcfInstReallocK.arealloc_realizes_cf_k: its two premises beyond the call pre, the entry room
   and the entry hull admission, are RQ's second and third conjuncts. The RQ premise is the one difference from
   arealloc_realizes_x besides R and APOST, so arealloc_realizes_x is not this text at wle by definition: it implies
   it (arealloc_realizes_x_R_wle), for every RQ. *)
Definition arealloc_realizes_xR (R : world segs -> world segs -> Prop)
(APOST : (Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop))
(pc pc0 : Z) : Prop :=
forall Hp ly S W regs mem md p n_old n ch,
acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch ->
RQ S n (call_trace ly pc0 regs ch) ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < nmax -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly pc0 regs ch) S ->
amrealG segs R (realloc_tree_with mt ft p n (call_trace ly pc0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => realloc_leaf_xR APOST Hp ly S W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> mt_refused mt ft n (call_trace ly pc0 regs ch) S (snd r))).

Lemma arealloc_realizes_x_R_wle : forall pc pc0, arealloc_realizes_x pc pc0 ->
arealloc_realizes_xR (@wle segs) (acall_post_x segs B ARx) pc pc0.
Proof.
intros pc pc0 H Hp ly S W regs mem md p n_old n ch HPRE _ Hin H10 Hhid H11 Hn Hlive Htr.
exact (amreal_amrealG segs (@wle segs) (fun W1 W2 Hw => Hw) _ W _ _
  (H Hp ly S W regs mem md p n_old n ch HPRE Hin H10 Hhid H11 Hn Hlive Htr)).
Qed.


Definition arealloc_null_realizes_x (pc pc0 : Z) : Prop :=
forall Hp, arealloc_null_realizesP segs (admits (as_universe B)) mt ft
(fun ly S W regs mem md ch => acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch)
(fun _ _ => True) nmax LIVE_MAX (fun R t W c Q => amreal segs t W c Q)
(fun ly S W regs mem md n r W' c' => malloc_leaf_x segs B ARx XS ly S Hp W regs mem md n r W' c') pc pc0.

(* The model part of the realloc text. *)
Definition realloc_post_x (s : astate) (p : sptr) (n_old n : Z) (r : sptr * astate) : Prop :=
st_nev s <= st_nev (snd r) /\ (length (st_secs s) <= length (st_secs (snd r)))%nat /\ frames (snd r) = frames s /\
(fst r = PNull -> blocks (snd r) = blocks s) /\
(fst r <> PNull -> exists l1 l2, blocks s = l1 ++ (p, n_old) :: l2 /\ blocks (snd r) = l1 ++ l2 ++ [(fst r, n)]).
Definition realloc_model_law_x : Prop :=
forall s p n_old n tr, WFx s -> RQ s n tr -> In (p, n_old) (blocks s) -> 1 <= n < nmax -> blocks_bytes s + n <= LIVE_MAX ->
admits (as_universe B) tr s ->
asafe (realloc_tree_with mt ft p n tr s) /\ agprog (realloc_tree_with mt ft p n tr s) /\
is_spin (realloc_tree_with mt ft p n tr s) = false /\
(forall tr' r, apath (realloc_tree_with mt ft p n tr s) tr' r -> realloc_post_x s p n_old n r) /\
(forall tr' r, apath (realloc_tree_with mt ft p n tr s) tr' r -> incl (st_depot (snd r)) (st_depot s ++ [tr])).

(* ---------------------------------------------------------------------------- *)
(* 3. The rule.                                                                   *)
Section r.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis RMX : realloc_model_law_x.
Hypothesis XSL : ARx_xs_law segs B ARx XS.

(* YGcallx.v's xs_write_ok with an exception X for the pre-state blocks that leave (realloc frees the old block, and
   the post extents XS may reuse its bytes): a write-set byte outside X is outside every pre-state block. *)
Lemma xs_write_ok_except : forall lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 (X : Z -> Prop) a,
ARx lyc Sc Hpc W memc mdc -> ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 ->
(forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly2 S2) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> X a)) ->
(forall f, In f (frames Sc) -> In f (frames S2)) ->
Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2) -> ~ X a ->
a < alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
(forall p n, In (p, n) (ablocks B lyc Sc) -> ~ (p <= a < p + req_size n)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
~ Exists (in_zr a) (ly_extra lyc).
Proof.
intros lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 X a HAR HAR2 Hly2 Hab Hfr HX HnX.
destruct (Exists_app_or_zr a _ _ HX) as [HX1 | HX2].
- exact (XSL lyc Sc Hpc W memc mdc a HAR HX1).
- destruct (XSL ly2 S2 Hp2 W2 mem2 md2 a HAR2 HX2) as (Xc & Xa & Xi & Xb & Xf & Xe).
destruct (alx_layout segs B ARx LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
split; [exact Xc|]. split; [exact Xa|]. split; [exact Xi|].
split.
{ intros p n Hin Hr. destruct (Hab (p, n) Hin) as [Hin2 | HXr]; [exact (Xb p n Hin2 Hr) | exact (HnX (HXr a Hr))]. }
split; [intros cid pos Hin; rewrite <- Efa; exact (Xf cid pos (Hfr _ Hin))|].
rewrite <- Eextra. exact Xe.
Qed.


(* ---------------------------------------------------------------------------- *)
(* 3R. The rule over a world relation R and a callee post APOST.                    *)
(*    The rules of 3 with the journal ajournal_xwR R (YCbqG.v's R core), the step SRrG segs R (YA0nH.v), the text    *)
(*    arealloc_realizes_xR R APOST and the leaf realloc_leaf_xR APOST. R is transitive (the walk's bind and the       *)
(*    journal's composition ajournal_xw_subR need it). The post's two laws are YGcallx.v's: POST_AR (the invariant,   *)
(*    the layout step and the saved registers at the post) and POST_J (the call's own journal at R). The plain rules *)
(*    aj_realloc_at_x / aj_realloc_x below are these at R := wle, APOST := acall_post_x (POST_AR_x, POST_J_x); the   *)
(*    cf instance is at R := wle' segs RZ_cf, APOST := APOST_cf (POST_AR_cf, POST_J_cf), YGcallRcf.v.               *)
Section rR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Variable APOST : (Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop).
Hypothesis POST_AR : apost_ar_law segs ARx APOST.
Hypothesis POST_J : apost_j_law (SK := SK) segs B ARx R APOST.

Lemma aj_realloc_at_xR : forall pcR pc0, arealloc_realizes_xR R APOST pcR pc0 ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n (o : Z) raw ch,
@ajournal_xwR rc SK segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n_old) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa -> getr regsT 11 = w64 n -> 1 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
RQ Sc n (call_trace lyc pc0 regsT ch) ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc ->
(In (pa, n_old) (ablocks B ly S) -> forall i, 0 <= i < req_size n_old -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 pcR) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xwR rc SK segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc pc0 regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc /\
(exists p q, sptr_addr B lyc p = pa /\ In (p, n_old) (blocks Sc) /\ sptr_addr B ly2 q = res /\ (q = PNull <-> res = 0) /\
  (exists trc, apath (realloc_tree_with mt ft p n (call_trace lyc pc0 regsT ch) Sc) trc (q, S2) /\ YG0d.gflag trc = true) /\
  realloc_leaf_xR APOST Hpc lyc Sc W regsT memT mdc p n_old n (q, S2) W2 c2) /\
((res = 0 /\ Hp2 = Hpc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ blocks S2 = blocks Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1 /\
  mt_refused mt ft n (call_trace lyc pc0 regsT ch) Sc S2)
 \/
 (4096 <= res /\ res mod 16 = 0 /\ Hp2 = remove Z.eq_dec pa Hpc /\
  (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n_old) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)]) /\
  (forall i, 0 <= i < Z.min n_old n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (pa + i)) /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
    (fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n_old))))).
Proof.
intros pcR pc0 AREAL WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n o raw ch
HJ Hin Hhid Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRQ Hch Htr HFP.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
destruct (proj1 (in_ablocks B lyc Sc pa n_old) Hin) as (p & Ep & Hpin).
destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc W memT mdc pa n_old HAR Hin) as (_ & Hpa4096 & _).
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
destruct (RMX Sc p n_old n (call_trace lyc pc0 regsT ch) HWF HRQ Hpin Hn Hlive Htr) as (Hsafe & Hprog & Hnspin & Hmpost & Hmdep).
pose proof (AREAL Hpc lyc Sc W regsT memT mdc p n_old n ch HPRE HRQ Hpin ltac:(rewrite Ep; exact Ha0)
  ltac:(rewrite Ep; exact Hhid) Ha1 Hn Hlive Htr) as HREAL.
cbv beta in HREAL.
eapply (SRrG_mono segs R).
{ exact (amrealG_SRrG04 segs R R_trans _ W _ _ HREAL Hsafe Hprog Hnspin). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf & Href).
pose proof (Hmpost tr r Hpath) as HQ. pose proof (Hmdep tr r Hpath) as HDEP. destruct r as [q S2].
unfold realloc_post_x in HQ. cbn [fst snd] in HQ, Href, HDEP.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & HblN & HblS).
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & Hres & HQT2 & LN & LS & _).
cbn [fst snd] in Hres, HQT2, LN, LS.
destruct (asptr_null_dec q) as [-> | Hqn].
-
destruct (LN eq_refl) as (HPOST & Herr & Hoom).
specialize (HblN eq_refl). specialize (Href eq_refl).
destruct (POST_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) as (HAR2 & Hly2 & HP).
destruct (alx_layout segs B ARx LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite HblN. apply map_ext_in. exact Efc. }
assert (HJ1 : @ajournal_xwR rc SK segs B [] ARx R ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
  (st_nev S2 - st_nev Sc) [call_trace lyc pc0 regsT ch]).
{ refine (POST_J lyc Sc Hpc W regsT memT mdc ly2 S2 Hpc W2 regs2 mem2 md2
    (fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2))
    (fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2)) [] (st_nev S2 - st_nev Sc) [call_trace lyc pc0 regsT ch]
    HPOST HAR HstkC Hfrs2 ltac:(zlia) ltac:(zlia) Hsecs2 _ _ _ HQT2 (wild_part_step _ _ _ _ HDEP)).
- intros a Ha.
apply (xs_write_ok_except lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 (fun _ => False) a HAR HAR2 Hly2);
[intros b Hb; left; rewrite Eab2; exact Hb | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha | intros Hf; exact Hf].
- intros a Ha. left. exact Ha.
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, Hpc, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (@ajournal_xw_subR rc SK segs B PST ARx HL LAWS segs_low R R_trans);
[exact HJ | exact (ajournal_xwR_nil_pst (SK := SK) segs B ARx R PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia
| intros a (rg & [] & _)]. }
split; [exact HP|]. split; [cbn in Hres; exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr|].
split.
{ exists p, PNull. split; [exact Ep|]. split; [exact Hpin|]. split; [reflexivity|].
split; [split; intros _; reflexivity|].
split; [exists tr; split; [exact Hpath | exact Hgf] | exact Hleaf0]. }
left. split; [reflexivity|]. split; [reflexivity|]. split; [exact Eab2|]. split; [exact HblN|].
split.
{ rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal_xR (SK := SK) segs B ARx segs_low R); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
split; [exact Herr|]. split; [exact Hoom|]. exact Href.
-
destruct (LS Hqn) as (HPOST & Hcopy).
destruct (HblS Hqn) as (l1 & l2 & Ebl1 & Ebl2).
rewrite Ep in HPOST, Hcopy.
destruct (POST_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) as (HAR2 & Hly2 & HP).
destruct (alx_layout segs B ARx LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
set (res := sptr_addr B ly2 q) in *.
assert (Eab2 : ablocks B ly2 S2 = map fc l1 ++ map fc l2 ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc l1 ++ map fc l2 ++ [(res, n)]). rewrite Ebl2, !map_app.
assert (E1 : map f2 l1 = map fc l1).
{ apply map_ext_in. intros b Hb. apply Efc. rewrite Ebl1. apply in_or_app. left. exact Hb. }
assert (E2 : map f2 l2 = map fc l2).
{ apply map_ext_in. intros b Hb. apply Efc. rewrite Ebl1. apply in_or_app. right. right. exact Hb. }
rewrite E1, E2. reflexivity. }
assert (EabC : ablocks B lyc Sc = map fc l1 ++ (pa, n_old) :: map fc l2).
{ unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n_old) :: map fc l2). rewrite Ebl1, map_app. cbn [map].
replace (fc (p, n_old)) with (pa, n_old) by (subst fc; cbn [fst snd]; rewrite Ep; reflexivity). reflexivity. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)).
{ rewrite Eab2. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
destruct (alx_blocks segs B ARx LAWS ly2 S2 (remove Z.eq_dec pa Hpc) W2 mem2 md2 res n HAR2 Hnew) as (Hr16 & Hr4096 & _).
assert (HinFP : forall a, pa <= a < pa + req_size n_old -> inFP [(pa, pa + req_size n_old)] a).
{ intros a Ha. exists (pa, pa + req_size n_old). split; [left; reflexivity | cbn [fst snd]; zlia]. }
assert (Hsep2 : forall b m a, In (b, m) (map fc l1 ++ map fc l2) -> b <= a < b + req_size m ->
~ (res <= a < res + req_size n)).
{ intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
pose proof (@sep_blocks_pos_x rc segs B ARx HL LAWS ly2 S2 (remove Z.eq_dec pa Hpc) W2 mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, app_assoc, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HE : forall a, (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n_old) \/
  Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2) ->
(Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2) /\ ~ (pa <= a < pa + req_size n_old)) \/
exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\ b <= a < b + req_size m /\
(inFP [(pa, pa + req_size n_old)] a \/ ~ In (b, m) (ablocks B lyc Sc))).
{ intros a [Ha | [Ha | Hx]].
- right. exists res, n. split; [right; exact Hnew|]. split; [exact Ha|].
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, n) (ablocks B lyc Sc)) as [Hold | Hold];
[|right; exact Hold].
rewrite EabC in Hold. apply in_app_or in Hold as [Hold | [Hold | Hold]].
+ exfalso. exact (Hsep2 res n a ltac:(apply in_or_app; left; exact Hold) Ha Ha).
+ left. injection Hold as E1 E2. apply HinFP. rewrite E2. zlia.
+ exfalso. exact (Hsep2 res n a ltac:(apply in_or_app; right; exact Hold) Ha Ha).
- right. exists pa, n_old. split; [left; exact Hin|]. split; [exact Ha|]. left. apply HinFP. exact Ha.
- destruct (Z_le_gt_dec pa a) as [H1 | H1]; [destruct (Z_lt_ge_dec a (pa + req_size n_old)) as [H2 | H2]|].
+ right. exists pa, n_old. split; [left; exact Hin|]. split; [zlia|]. left. apply HinFP. zlia.
+ left. split; [exact Hx | zlia].
+ left. split; [exact Hx | zlia]. }
assert (XWP : forall a, (Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2) /\ ~ (pa <= a < pa + req_size n_old)) ->
a < alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
(forall p0 n0, In (p0, n0) (ablocks B lyc Sc) -> ~ (p0 <= a < p0 + req_size n0)) /\
(forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
~ Exists (in_zr a) (ly_extra lyc)).
{ intros a [Hx Hno].
apply (xs_write_ok_except lyc Sc Hpc W memT mdc ly2 S2 (remove Z.eq_dec pa Hpc) W2 mem2 md2
  (fun a => pa <= a < pa + req_size n_old) a HAR HAR2 Hly2);
[| intros f Hf; rewrite Hfrs2; exact Hf | exact Hx | exact Hno].
intros [b m] Hb. rewrite EabC in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]].
- left. rewrite Eab2. apply in_or_app. left. exact Hb.
- right. injection Hb as E1 E2. subst b m. intros a0 Hr0. exact Hr0.
- left. rewrite Eab2. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (Hgone2 : forall p0 n0 i, In (p0, n0) (ablocks B lyc Sc) -> ~ In (p0, n0) (ablocks B ly2 S2) -> 0 <= i < req_size n0 ->
inFP [(pa, pa + req_size n_old)] (p0 + i)).
{ intros p0 n0 i H0 Hn0 Hi. rewrite EabC in H0. apply in_app_or in H0 as [H0 | [H0 | H0]].
- exfalso. apply Hn0. rewrite Eab2. apply in_or_app. left. exact H0.
- injection H0 as E1 E2. subst p0 n0. apply HinFP. zlia.
- exfalso. apply Hn0. rewrite Eab2. apply in_or_app. right. apply in_or_app. left. exact H0. }
assert (Hlive2 : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
~ ((res <= b + i < res + req_size n) \/ (pa <= b + i < pa + req_size n_old)) -> In (b, m) (ablocks B ly2 S2)).
{ intros b m i Hb Hi HnE. rewrite EabC in Hb. rewrite Eab2. apply in_app_or in Hb as [Hb | [Hb | Hb]].
- apply in_or_app. left. exact Hb.
- exfalso. injection Hb as E1 E2. subst b m. apply HnE. right. zlia.
- apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (HJ1 : @ajournal_xwR rc SK segs B [] ARx R ASTACK (spZ regsT) [(pa, pa + req_size n_old)] lyc Sc Hpc W memT mdc []
ly2 S2 (remove Z.eq_dec pa Hpc) W2 mem2 md2 (st_nev S2 - st_nev Sc) [call_trace lyc pc0 regsT ch]).
{ exact (POST_J lyc Sc Hpc W regsT memT mdc ly2 S2 (remove Z.eq_dec pa Hpc) W2 regs2 mem2 md2
(fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n_old) \/ Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2))
(fun a => Exists (in_zr a) (XS lyc Sc ++ XS ly2 S2) /\ ~ (pa <= a < pa + req_size n_old))
[(pa, pa + req_size n_old)] (st_nev S2 - st_nev Sc) [call_trace lyc pc0 regsT ch]
HPOST HAR HstkC Hfrs2 ltac:(zlia) ltac:(zlia) Hsecs2 XWP HE Hgone2 HQT2
(wild_part_step _ _ _ _ HDEP)). }
exists ly2, S2, (remove Z.eq_dec pa Hpc), regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (@ajournal_xw_subR rc SK segs B PST ARx HL LAWS segs_low R R_trans);
[exact HJ | exact (ajournal_xwR_nil_pst (SK := SK) segs B ARx R PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n_old) (ablocks B ly S)) as [H0|H0].
- left. replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right. left. exists pa, n_old. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|]. split; [exact Htr|].
split.
{ exists p, q. split; [exact Ep|]. split; [exact Hpin|]. split; [reflexivity|].
split; [split; [intros E0; exfalso; exact (Hqn E0) | intros E0; exfalso; zlia]|].
split; [exists tr; split; [exact Hpath | exact Hgf] | exact Hleaf0]. }
right. split; [exact Hr4096|]. split; [exact Hr16|]. split; [reflexivity|].
split; [exists (map fc l1), (map fc l2); split; [exact EabC | exact Eab2]|].
split; [exact Hcopy|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal_xR (SK := SK) segs B ARx segs_low R);
[exact HJ1 | exact HAR | | exact Hlive2 | apply sink_closed_pos; constructor; [cbn [fst]; zlia | constructor]].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. cbv beta. right. exact Ha.
Qed.

(* aj_realloc_xR: cgif YCbq.v:1715's form over R: the rule at a symbolic state reaching the realloc entry. *)
Lemma aj_realloc_xR : forall pcR pc0, arealloc_realizes_xR R APOST pcR pc0 ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pcR -> ss_resv ss = None ->
@ajournal_xwR rc SK segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n_old) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa -> getr (ms_regs ms) 11 = w64 n -> 1 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
RQ Sc n (call_trace lyc pc0 (ms_regs ms) ch) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc pc0 (ms_regs ms) ch) Sc ->
(In (pa, n_old) (ablocks B ly S) -> forall i, 0 <= i < req_size n_old -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xwR rc SK segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc pc0 (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARx QMm lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc pc0 (ms_regs ms) ch) Sc /\
(exists p q, sptr_addr B lyc p = pa /\ In (p, n_old) (blocks Sc) /\ sptr_addr B ly2 q = res /\ (q = PNull <-> res = 0) /\
  (exists trc, apath (realloc_tree_with mt ft p n (call_trace lyc pc0 (ms_regs ms) ch) Sc) trc (q, S2) /\ YG0d.gflag trc = true) /\
  realloc_leaf_xR APOST Hpc lyc Sc W (ms_regs ms) (ms_mem ms) mdc p n_old n (q, S2) W2 c2) /\
((res = 0 /\ Hp2 = Hpc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ blocks S2 = blocks Sc /\
  acall_kept_x segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1 /\
  mt_refused mt ft n (call_trace lyc pc0 (ms_regs ms) ch) Sc S2)
 \/
 (4096 <= res /\ res mod 16 = 0 /\ Hp2 = remove Z.eq_dec pa Hpc /\
  (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n_old) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)]) /\
  (forall i, 0 <= i < Z.min n_old n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) (ms_mem ms) (pa + i)) /\
  acall_kept_x segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
    (fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n_old))))).
Proof.
intros pcR pc0 AREAL WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n o spw raw ch
HS Hpcs Hrv HJ Hin Hhid Ha0 Ha1 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRQ Hch Htr HFP.
pose proof (ajxR_stk HJ) as (_ & _ & Hceil & Hslo & Hshi & H47 & _). pose proof (ajxR_qt HJ) as HQT.
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply zcanon_small. zlia. }
rewrite (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpcs.
eapply aj_realloc_at_xR; eassumption.
Qed.
End rR.

Lemma aj_realloc_at_x : forall pcR pc0, arealloc_realizes_x pcR pc0 ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n (o : Z) raw ch,
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n_old) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa -> getr regsT 11 = w64 n -> 1 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
RQ Sc n (call_trace lyc pc0 regsT ch) ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc ->
(In (pa, n_old) (ablocks B ly S) -> forall i, 0 <= i < req_size n_old -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pcR) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc pc0 regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc pc0 regsT ch) Sc /\
(exists p q, sptr_addr B lyc p = pa /\ In (p, n_old) (blocks Sc) /\ sptr_addr B ly2 q = res /\ (q = PNull <-> res = 0) /\
  (exists trc, apath (realloc_tree_with mt ft p n (call_trace lyc pc0 regsT ch) Sc) trc (q, S2) /\ YG0d.gflag trc = true) /\
  realloc_leaf_x Hpc lyc Sc W regsT memT mdc p n_old n (q, S2) W2 c2) /\
((res = 0 /\ Hp2 = Hpc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ blocks S2 = blocks Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1 /\
  mt_refused mt ft n (call_trace lyc pc0 regsT ch) Sc S2)
 \/
 (4096 <= res /\ res mod 16 = 0 /\ Hp2 = remove Z.eq_dec pa Hpc /\
  (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n_old) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)]) /\
  (forall i, 0 <= i < Z.min n_old n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (pa + i)) /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
    (fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n_old))))).
Proof.
intros pcR pc0 AREAL WS.
exact (aj_realloc_at_xR (@wle segs) (wle_trans segs) (acall_post_x segs B ARx) (POST_AR_x segs B ARx)
  (POST_J_x (SK := SK) segs B ARx LAWS segs_low errno_low OWNLOW) pcR pc0 (arealloc_realizes_x_R_wle pcR pc0 AREAL)
  (WS := WS)).
Qed.

(* cgif YCbq.v:1717's form: the rule at a symbolic state reaching the realloc entry. *)
Lemma aj_realloc_x : forall pcR pc0, arealloc_realizes_x pcR pc0 ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n_old n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pcR -> ss_resv ss = None ->
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n_old) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa -> getr (ms_regs ms) 11 = w64 n -> 1 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
RQ Sc n (call_trace lyc pc0 (ms_regs ms) ch) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc pc0 (ms_regs ms) ch) Sc ->
(In (pa, n_old) (ablocks B ly S) -> forall i, 0 <= i < req_size n_old -> inFP FP (pa + i)) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
@ajournal_xw rc SK segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc pc0 (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARx QMm lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc pc0 (ms_regs ms) ch) Sc /\
(exists p q, sptr_addr B lyc p = pa /\ In (p, n_old) (blocks Sc) /\ sptr_addr B ly2 q = res /\ (q = PNull <-> res = 0) /\
  (exists trc, apath (realloc_tree_with mt ft p n (call_trace lyc pc0 (ms_regs ms) ch) Sc) trc (q, S2) /\ YG0d.gflag trc = true) /\
  realloc_leaf_x Hpc lyc Sc W (ms_regs ms) (ms_mem ms) mdc p n_old n (q, S2) W2 c2) /\
((res = 0 /\ Hp2 = Hpc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ blocks S2 = blocks Sc /\
  acall_kept_x segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1 /\
  mt_refused mt ft n (call_trace lyc pc0 (ms_regs ms) ch) Sc S2)
 \/
 (4096 <= res /\ res mod 16 = 0 /\ Hp2 = remove Z.eq_dec pa Hpc /\
  (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n_old) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)]) /\
  (forall i, 0 <= i < Z.min n_old n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) (ms_mem ms) (pa + i)) /\
  acall_kept_x segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
    (fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n_old))))).
Proof.
intros pcR pc0 AREAL WS.
exact (aj_realloc_xR (@wle segs) (wle_trans segs) (acall_post_x segs B ARx) (POST_AR_x segs B ARx)
  (POST_J_x (SK := SK) segs B ARx LAWS segs_low errno_low OWNLOW) pcR pc0 (arealloc_realizes_x_R_wle pcR pc0 AREAL)
  (WS := WS)).
Qed.
End r.
End gr.

(* ---------------------------------------------------------------------------- *)
(* 4. The realloc text at a conjunct relation AR0 /\ P (cf: ARcf /\ xs_placed_cf, YGcallcf.v's relation): from the   *)
(*    text at AR0 and a leaf-level law that the realloc leaf keeps P (the twin of YGcallcf.v's                       *)
(*    xs_placed_cf_malloc_law for malloc), as YGcallcf.v's amalloc_realizes_x_xs lifts the malloc text.              *)
Section lift. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
Variable XS : alayout -> astate -> list (Z * Z).
Lemma arealloc_realizes_x_and :
forall (AR0 : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
(P : alayout -> astate -> Prop) pc pc0,
arealloc_realizes_x segs B AR0 QMm mt nmax ft XS pc pc0 ->
(forall Hp ly S W regs mem md p n_old n ch r W' c',
  acall_pre_x segs B AR0 QMm ly S Hp W regs mem md ch -> P ly S ->
  realloc_leaf_x segs B AR0 XS Hp ly S W regs mem md p n_old n r W' c' ->
  realloc_leaf_x segs B (fun ly S Hp W mem md => AR0 ly S Hp W mem md /\ P ly S) XS Hp ly S W regs mem md p n_old n r W' c') ->
arealloc_realizes_x segs B (fun ly S Hp W mem md => AR0 ly S Hp W mem md /\ P ly S) QMm mt nmax ft XS pc pc0.
Proof.
intros AR0 P pc pc0 H XP Hp ly S W regs mem md p n_old n ch HPRE Hin H10 Hhid H11 Hn Hlive Htr.
destruct HPRE as ((HA & HP) & REST).
pose proof (H Hp ly S W regs mem md p n_old n ch (conj HA REST) Hin H10 Hhid H11 Hn Hlive Htr) as H0.
cbv beta in H0 |- *.
eapply amreal_mono; [| exact H0].
intros r W' c' [HL HN]. split; [exact (XP Hp ly S W regs mem md p n_old n ch r W' c' (conj HA REST) HP HL) | exact HN].
Qed.
End lift.
