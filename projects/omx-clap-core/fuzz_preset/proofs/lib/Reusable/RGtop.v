(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AllocG.v at
   origin/cold/c-asan-realloc-primary b97c2fd1d44 (c-asan's milestone M1, the revision whose leaf gives
   apath + gflag instead of ireturns), with its module paths changed and the cgif_file instantiation at the end
   dropped: libreac/fuzz_decode instantiates the Section at its own image in lib/A/DecodeCalloc.v, and the cgif
   image files (YB1v, YB1q, YF0l, YF0m) that only the dropped instantiation needed are not imported. Statement
   only; no proof of it is on this branch (rule 24). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/Reusable/YGAlloc.v, with its module paths changed; 4 of its 82 lines of code are new or changed and 7 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AllocG.v at 95e6f1d72b6 (sha256 9fd0d69116a5) into lib/Reusable (shared by both images), with its module paths changed; the M1 text of this file (10c1218e6df) is replaced, not kept beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/Reusable/YGAlloc.v, with its module paths and module names changed; 438 of its 463 lines of code are new or changed and 57 lines of the source are left out. *)
(* copy of proofs/cgif/cgif_file_fuzzer/lib/RGtop.v@e8a7dd66acf2; do not edit. Only this line is added, the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib is this unit's OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable, and line 17 rewords the donor's citation of its table as the internal file REALLOC-THIN-SEGMENTS.md. *)
(* realloc's composition on the cgif_file core: the ReallocG statements from the frame-generic Allocate and
   Deallocate contracts (AllocG.aalloc_realizes, DeallocG.adealloc_realizes), the copy routine's contract
   (ReallocG.amemcpy_realizes), the model obligations [rmodel_ok] and the thin caller segments below.

   ported from proofs/cgif/cgif_rgb_fuzzer/lib/YF78.v (tfx_arealloc: the binds over realloc_tree, pa_arm, the
   copy c1_at_mid, the free arm c2_arm, succ_leaf and null_arm), with the Allocate / Deallocate runs replaced by the
   frame-generic contracts and every image-specific step made a segment hypothesis; thin-caller control flow from
   msgpack-c AsanW/ARealloc_x.v:205.

   This file is image-generic.  A consumer proves, on its own image, the thin segments (S1, S2a, S2b, S3, S4 for
   realloc(p, n), S5, S6 for realloc(NULL, n); each an [amreal] or [SRr] run between two call sites, with the
   AllocG / DeallocG pre-states as the call frames), the contracts and the model obligations, and gets
   [rg_realloc_all] / [rg_realloc_null].  The segments carry consumer-chosen
   invariants [K1] (at Reallocate's call of Allocate), [K2] (at the call of the copy routine), [K3] (at
   Reallocate's call of Deallocate) and [Kn] (at asan_realloc's NULL-input call of Allocate): the registers and the
   stack contents the next segment needs.  The table is the internal file REALLOC-THIN-SEGMENTS.md.

   Section variables: the shared order (segs B U mt ft ARX AOX rpre nmax lmax lpost fpre, then rU), then Allocate's and
   Deallocate's premises [rpreA] [rpreD], then the image constants (pcR pc0 inst oomb pcM as in ReallocG.v, and
   Allocate's / Deallocate's entry pcs [pcA] [pcD]).  The call sites pass Allocate(inst, n, 8, so, FROM_MALLOC = 1,
   can_fill = 1) and Deallocate(inst, p, 0, 0, so, FROM_MALLOC = 1). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG DeallocG ReallocG.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Generic lemmas.                                                                                                   *)

(* A post on every granted path's result holds at every leaf (YFfk.amreal_apostg, here over any image). *)
Lemma rg_amreal_apostg (segs : list Segment) {R} : forall (t : itree astate R) (P : R -> Prop) W c
(Q : R -> world segs -> config -> Prop),
(forall tr r, apath t tr r -> gflag tr = true -> P r) -> amreal segs t W c Q ->
amreal segs t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros P W c Q HP H; cbn [amreal] in *.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ. split; [|exact HQ]. apply (HP []); reflexivity.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ.
  assert (HPk : forall z, aok snap q z -> progz q z = true -> forall tr a, apath (k z) tr a -> gflag tr = true -> P a).
  { intros z Hz Hpz tr a Hp Hg. apply (HP ((q, z) :: tr)); cbn; [split; [reflexivity|]; split; [exact Hz | exact Hp] | rewrite Hpz, Hg; reflexivity]. }
  destruct q; cbn beta iota in *;
  try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
  repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (HPk _ (H3 i) ltac:(rewrite (H6 i Hi); reflexivity)) | exact (H8 i Hi)]).
  destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact (HPk _ Hz eq_refl) | exact HR].
- exact H.
- exact I.
Qed.

(* Every result of a realization is the end of a granted path. *)
Lemma rg_apath_gflag (segs : list Segment) {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal segs t W c Q ->
amreal segs t W c (fun r W' c' => Q r W' c' /\ exists trc, apath t trc r /\ gflag trc = true).
Proof.
intros t W c Q H.
eapply amreal_mono; [| exact (rg_amreal_apostg segs t (fun r => exists trc, apath t trc r /\ gflag trc = true) W c Q
  (fun trc r Hp Hg => ex_intro _ trc (conj Hp Hg)) H)].
intros r W' c' [HP HQ]. exact (conj HQ HP).
Qed.

(* Machine steps after every leaf (YFeu.amreal_then_SRr, over any image). *)
Lemma rg_then_SRr (segs : list Segment) {R} : forall (t : itree astate R) W c (P Q : R -> world segs -> config -> Prop),
amreal segs t W c P -> (forall r W' c', P r W' c' -> SRr segs W' c' (Q r)) -> amreal segs t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HPQ; cbn [amreal] in *.
- eapply SRr_bind; [exact H|]. intros W' c' _ HP. exact (HPQ r W' c' HP).
- eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk. destruct q; cbn beta iota in *;
  try (destruct Hk as (J & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists J, nx, bit, sp, i0;
  repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (H8 i Hi) | exact HPQ]).
  destruct Hk as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact HR | exact HPQ].
- exact H.
- exact I.
Qed.

Lemma rg_apath_bind {A R} : forall (m : M A) (f : A -> M R) s trc1 a s' trc2 r,
apath (m s) trc1 (a, s') -> apath (f a s') trc2 r -> apath (YG00.bind m f s) (trc1 ++ trc2) r.
Proof.
intros m f s trc1 a s' trc2 r H1 H2. unfold YG00.bind. revert trc1 H1. generalize (m s) as t.
induction t as [x | q snap k IH | pc | fl]; intros trc1 H1.
- destruct trc1 as [|e trc1']; cbn [apath] in H1; [|destruct H1]. subst x. cbn [ibind app]. exact H2.
- destruct trc1 as [|[q' z] trc1']; cbn [apath] in H1; [destruct H1|]. destruct H1 as (-> & Hz & H1).
  cbn [ibind app apath]. split; [reflexivity|]. split; [exact Hz|]. exact (IH z trc1' H1).
- destruct trc1; cbn [apath] in H1; destruct H1.
- destruct trc1; cbn [apath] in H1; destruct H1.
Qed.

Lemma rg_gflag_app : forall l1 l2, gflag (l1 ++ l2) = (gflag l1 && gflag l2)%bool.
Proof. induction l1 as [|[q z] l1 IH]; intros l2; cbn [gflag app]; [reflexivity|]. rewrite IH. apply andb_assoc. Qed.

Lemma rg_same_io_trans : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.

Lemma rg_sbm_io : forall m m', same_but_materialized m m' -> same_io m m'.
Proof.
intros m m' H. destruct (same_but_materialized_frame m m' H) as (F & _ & _ & I & S & P & _).
exact (conj F (conj I (conj S P))).
Qed.

Lemma rg_aview_same : forall segs (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview segs H mem' a = aview segs H mem a.
Proof. intros segs H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma rg_unsigned_small : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma rg_req_size : forall n, 1 <= n -> req_size n = n.
Proof. intros n H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma rg_req_size_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma rg_null_dec : forall q : sptr, {q = PNull} + {q <> PNull}.
Proof. intros q. destruct q; [left; reflexivity | right; discriminate | right; discriminate | right; discriminate]. Qed.

Lemma rg_scratch_in : forall (B : asyms) regs regsX stk a,
spZ regs - ASTACK <= spZ regsX - stk -> spZ regsX <= spZ regs ->
ascratch B stk regsX a -> ascratch B ASTACK regs a.
Proof. intros B regs regsX stk a H1 H2 [H|H]; [left; lia | right; exact H]. Qed.

(* The granted path of the realloc tree through the NULL-return arm and through the success arm. *)
Lemma rg_trace_null : forall mt ft p n tr S trc1 S1 trc2 S2,
apath (ft PNull tr S) trc1 (tt, S1) -> apath (mt n tr S1) trc2 (PNull, S2) ->
apath (realloc_tree_with mt ft p n tr S) (trc1 ++ trc2 ++ []) (PNull, S2).
Proof.
intros mt ft p n tr S trc1 S1 trc2 S2 H1 H2. unfold realloc_tree_with.
eapply rg_apath_bind; [exact H1|]. cbv beta. eapply rg_apath_bind; [exact H2|].
rewrite realloc_k_null. cbn. reflexivity.
Qed.

Lemma rg_trace_block : forall mt ft p n tr S trc1 S1 trc2 q S2 trc3 S3,
q <> PNull ->
apath (ft PNull tr S) trc1 (tt, S1) -> apath (mt n tr S1) trc2 (q, S2) -> apath (ft p tr S2) trc3 (tt, S3) ->
apath (realloc_tree_with mt ft p n tr S) (trc1 ++ trc2 ++ trc3 ++ []) (q, S3).
Proof.
intros mt ft p n tr S trc1 S1 trc2 q S2 trc3 S3 HQ H1 H2 H3. unfold realloc_tree_with.
eapply rg_apath_bind; [exact H1|]. cbv beta. eapply rg_apath_bind; [exact H2|].
rewrite (realloc_k_block ft p tr q HQ). eapply rg_apath_bind; [exact H3|]. cbn. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The consumer contract: model obligations and thin segments.                                                       *)

Section b.
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
Variable rU : list Z -> astate -> Prop.
Variable RSTACK : Z.
Variable rpreA : astate -> Z -> Prop.
Variable rpreD : astate -> Z -> Prop.
Variable pcR : Z.
Variable pc0 : Z.
Variable inst : Z.
Variable oomb : Z.
Variable pcM : Z.
Variable pcA : Z.
Variable pcD : Z.

Local Abbreviation APRE := (alloc_pre segs B U ARX rpreA nmax lmax 8 1 1).
Local Abbreviation APOST := (alloc_post segs B ARX AOX).
Local Abbreviation DPRE := (dealloc_pre segs B U ARX rpreD fpre 1).
Local Abbreviation DPOST := (dealloc_post_raw segs B ARX AOX).

(* realloc(p, n)'s entry facts (the premises of arealloc_realizes_all). *)
Definition rentry (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z) (ch : list (Z * Z * Z)) : Prop :=
realloc_pre segs B ARX RSTACK inst ly S W regs mem md ch /\ rpre S n /\
In (p, n_old) (blocks S) /\ fpre ly S W mem p n_old /\
getr regs 10 = w64 (sptr_addr B ly p) /\ getr regs 11 = w64 n /\
1 <= n < nmax /\ blocks_bytes S + n <= lmax /\ rU (call_trace ly pc0 regs ch) S.

(* realloc(NULL, n)'s entry facts (the premises of arealloc_null_realizes). *)
Definition rnentry (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (ch : list (Z * Z * Z)) : Prop :=
realloc_pre segs B ARX RSTACK inst ly S W regs mem md ch /\ rpre S n /\
getr regs 10 = w64 0 /\ getr regs 11 = w64 n /\
1 <= n < nmax /\ blocks_bytes S + n <= lmax /\ rU (call_trace ly pc0 regs ch) S.

(* A thin segment changes memory only in realloc's stack window and errno ([ascratch B ASTACK regs], regs =
   realloc's entry registers), in the view and in the raw memory. *)
Definition rkeep (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte)
(W' : world segs) (mem' : word -> option byte) : Prop :=
(forall a, 0 <= a < 2 ^ 64 -> ~ ascratch B ASTACK regs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall x : word, ~ ascratch B ASTACK regs (bv_unsigned x) -> mem' x = mem x).

(* realloc's stack window is present. *)
Definition rwin (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a.

(* A callee's stack window [sp - stk, sp) lies inside realloc's. *)
Definition rin (regs : bvmap 5 word) (sp stk : Z) : Prop := spZ regs - ASTACK <= sp - stk /\ sp <= spZ regs.

(* The model obligations: after the entry step, the trace premise U and Allocate's premise, the live bytes, the
   blocks, the secondary records and the owned set; after the inner malloc, on a block q the trace premise U for the
   free, the new block (q, n) live, every old block p still live and, on a block, Deallocate's premise for it and
   q <> p (cgif: realloc_s1 / realloc_mpost / aregime3_s1 / aregime3_s2 / aowned_s1 of cgif_rgb's YG0f and YF78;
   rU = U = fun tr _ => In tr (as_universe B)). *)
Definition rmodel_ok : Prop :=
(forall S n tr trc S1, rpre S n -> 1 <= n < nmax -> blocks_bytes S + n <= lmax -> rU tr S ->
apath (ft PNull tr S) trc (tt, S1) -> gflag trc = true ->
U tr S1 /\ rpreA S1 n /\ blocks_bytes S1 + n <= lmax /\ blocks S1 = blocks S /\
(length (st_secs S) <= length (st_secs S1))%nat /\ (forall ly a, AOX ly S1 a -> AOX ly S a)) /\
(forall S n tr trc1 S1 trc2 q S2, rpre S n -> 1 <= n < nmax -> blocks_bytes S + n <= lmax -> rU tr S ->
apath (ft PNull tr S) trc1 (tt, S1) -> gflag trc1 = true ->
apath (mt n tr S1) trc2 (q, S2) -> gflag trc2 = true ->
(q <> PNull -> U tr S2) /\ (q <> PNull -> In (q, n) (blocks S2)) /\
(forall p n_old, In (p, n_old) (blocks S) ->
In (p, n_old) (blocks S2) /\ (q <> PNull -> rpreD S2 n_old) /\ (q <> PNull -> q <> p))).

(* The invariants' types: realloc's entry, then the state at the call site. *)
Definition K1_t : Type := alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
sptr -> Z -> Z -> list (Z * Z * Z) ->
astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Definition K2_t : Type := alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
sptr -> Z -> Z -> list (Z * Z * Z) ->
sptr -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Definition Kn_t : Type := alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
Z -> list (Z * Z * Z) ->
astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

(* S1. The prefix: realloc's entry (pcR, p live) -> Reallocate's `jal Allocate`, through the interceptor, the
   unwinder, asan_realloc and Reallocate's chunk checks; the entry step [ft PNull] is realized on the way.  At the
   call, Allocate's pre-state (under Allocate's two model premises, which RGtop supplies). *)
Definition seg_pre (K1 : K1_t) : Prop :=
forall ly S W regs mem md p n_old n ch,
rentry ly S W regs mem md p n_old n ch ->
amreal segs (ft PNull (call_trace ly pc0 regs ch) S) W (cfg_at segs pcR regs mem md)
(fun r W1 c1 => exists so bp regsA memA mdA,
c1 = cfg_at segs pcA regsA memA mdA /\
(rpreA (snd r) n -> blocks_bytes (snd r) + n <= lmax -> U (call_trace ly pc0 regs ch) (snd r) ->
APRE inst so bp ly (snd r) W1 regsA memA mdA n (call_trace ly pc0 regs ch)) /\
wle W W1 /\ same_io md mdA /\ rin regs (spZ regsA) AFSTACK_G /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ ascratch B ASTACK regs a ->
aview segs (w_H W1) memA a = aview segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ ascratch B ASTACK regs (bv_unsigned x) -> memA x = mem x) /\
K1 ly S W regs mem md p n_old n ch (snd r) W1 regsA memA mdA).

(* S2a. Allocate's return with a block q (at raZ regsA, in Reallocate) -> the call of the copy routine (pcM) with
   dst = q, src = p, len = min(req_size n_old, n) (the old header's UsedSize): the read of the old chunk's size and
   of REAL(memcpy). *)
Definition seg_mid_a (K1 : K1_t) (K2 : K2_t) : Prop :=
forall ly S W regs mem md p n_old n ch S1 W1 so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
rentry ly S W regs mem md p n_old n ch ->
K1 ly S W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
APRE inst so bp ly S1 W1 regsA memA mdA n (call_trace ly pc0 regs ch) ->
APOST inst ly S1 W1 regsA memA mdA (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)
ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 10 = w64 (sptr_addr B ly2 q) -> q <> PNull -> In (q, n) (blocks S2) -> q <> p -> lpost S2 ->
In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) -> rpreD S2 n_old ->
SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
(fun W3 c3 => exists regsM memM mdM,
c3 = cfg_at segs pcM regsM memM mdM /\
rmemcpy_pre segs W3 regsM memM (sptr_addr B ly2 q) (sptr_addr B ly p) (Z.min (req_size n_old) n) /\
(forall i, 0 <= i < Z.min (req_size n_old) n ->
aview segs (w_H W3) memM (sptr_addr B ly p + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
(forall a, sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n -> 0 <= a < 2 ^ 64 /\ ~ ascratch B ASTACK regs a) /\
same_io md2 mdM /\ rkeep regs W2 mem2 W3 memM /\
K2 ly S W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM).

(* S2b. The copy routine's return (at raZ regsM) -> Reallocate's `jal Deallocate`.  At the call, Deallocate's
   pre-state on the old block (with fpre). *)
Definition seg_mid_b (K2 K3 : K2_t) : Prop :=
forall ly S W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3,
rentry ly S W regs mem md p n_old n ch ->
K2 ly S W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM ->
In (p, n_old) (blocks S2) -> rpreD S2 n_old -> U (call_trace ly pc0 regs ch) S2 ->
aregs_preserved regsM regs3 -> same_but_materialized mdM md3 ->
(forall i, 0 <= i < Z.min (req_size n_old) n ->
aview segs (w_H W3) mem3 (sptr_addr B ly2 q + i) = aview segs (w_H W3) memM (sptr_addr B ly p + i)) ->
(forall x : word, ~ (sptr_addr B ly2 q <= bv_unsigned x < sptr_addr B ly2 q + Z.min (req_size n_old) n) ->
mem3 x = memM x) ->
(forall a, apresent (w_H W3) memM a -> apresent (w_H W3) mem3 a) ->
SRr segs W3 (cfg_at segs (raZ regsM) regs3 mem3 md3)
(fun W4 c4 => exists so bp regsD memD mdD,
c4 = cfg_at segs pcD regsD memD mdD /\
DPRE inst so bp ly2 S2 W4 regsD memD mdD p n_old (call_trace ly pc0 regs ch) /\
same_io md3 mdD /\ rin regs (spZ regsD) DFSTACK_G /\ rkeep regs W3 mem3 W4 memD /\ rwin regs W4 memD /\
K3 ly S W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD).

(* S3. Deallocate's return (at raZ regsD, in Reallocate) -> realloc's return (raZ regs), a0 = q: Reallocate's,
   asan_realloc's and the interceptor's epilogues. *)
Definition seg_ret (K3 : K2_t) : Prop :=
forall ly S W regs mem md p n_old n ch q ly2 S2 W4 so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
rentry ly S W regs mem md p n_old n ch ->
K3 ly S W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
DPRE inst so bp ly2 S2 W4 regsD memD mdD p n_old (call_trace ly pc0 regs ch) ->
DPOST inst ly2 S2 W4 regsD memD mdD (fun a => p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old)
ly3 S3 W5 regs5 mem5 md5 ->
lpost S3 ->
SRr segs W5 (cfg_at segs (raZ regsD) regs5 mem5 md5)
(fun W' c' => exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
getr regs' 10 = w64 (sptr_addr B ly2 q) /\
ARX inst ly3 S3 W' mem' md' /\ same_io md5 md' /\ rkeep regs W5 mem5 W' mem' /\ rwin regs W' mem').

(* S4. The NULL-return arm: Allocate's return with PNull (at raZ regsA, in Reallocate) -> realloc's return, a0 = 0:
   Reallocate's NULL return, asan_realloc's errno_ENOMEM call (errno := 12), the epilogues. *)
Definition seg_nret (K1 : K1_t) : Prop :=
(* errno is the musl thread slot at tp - 0xa4 (an image-symbol fact of every consumer; __errno_location). *)
as_errno B = as_tp B - 0xa4 ->
forall ly S W regs mem md p n_old n ch S1 W1 so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2,
rentry ly S W regs mem md p n_old n ch ->
K1 ly S W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
APRE inst so bp ly S1 W1 regsA memA mdA n (call_trace ly pc0 regs ch) ->
APOST inst ly S1 W1 regsA memA mdA
(fun a => PNull <> PNull /\ sptr_addr B ly2 PNull <= a < sptr_addr B ly2 PNull + req_size n)
ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 10 = w64 (sptr_addr B ly2 PNull) -> lpost S2 ->
val_mem segs (mrestrict (w_H W2) mem2) oomb 1 1 ->
In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) ->
SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
(fun W' c' => exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
ARX inst ly2 S2 W' mem' md' /\ same_io md2 md' /\ rkeep regs W2 mem2 W' mem' /\ rwin regs W' mem' /\
val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
val_mem segs (mrestrict (w_H W') mem') oomb 1 1).

(* S5. The NULL-input prefix: realloc's entry (pcR, a0 = 0) -> asan_realloc's NULL-input `jal Allocate`; the entry
   step [ft PNull] is realized on the way.  At the call, Allocate's pre-state. *)
Definition seg_npre (Kn : Kn_t) : Prop :=
forall ly S W regs mem md n ch,
rnentry ly S W regs mem md n ch ->
amreal segs (ft PNull (call_trace ly pc0 regs ch) S) W (cfg_at segs pcR regs mem md)
(fun r W1 c1 => exists so bp regsA memA mdA,
c1 = cfg_at segs pcA regsA memA mdA /\
(rpreA (snd r) n -> blocks_bytes (snd r) + n <= lmax -> U (call_trace ly pc0 regs ch) (snd r) ->
APRE inst so bp ly (snd r) W1 regsA memA mdA n (call_trace ly pc0 regs ch)) /\
wle W W1 /\ same_io md mdA /\ rin regs (spZ regsA) AFSTACK_G /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ ascratch B ASTACK regs a ->
aview segs (w_H W1) memA a = aview segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ ascratch B ASTACK regs (bv_unsigned x) -> memA x = mem x) /\
Kn ly S W regs mem md n ch (snd r) W1 regsA memA mdA).

(* S6. The NULL-input return: Allocate's return (at raZ regsA, in asan_realloc) with a block or PNull -> realloc's
   return, a0 = the result; on PNull asan_realloc's errno_ENOMEM call. *)
Definition seg_npost (Kn : Kn_t) : Prop :=
as_errno B = as_tp B - 0xa4 ->
forall ly S W regs mem md n ch S1 W1 so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
rnentry ly S W regs mem md n ch ->
Kn ly S W regs mem md n ch S1 W1 regsA memA mdA ->
APRE inst so bp ly S1 W1 regsA memA mdA n (call_trace ly pc0 regs ch) ->
APOST inst ly S1 W1 regsA memA mdA (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)
ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 10 = w64 (sptr_addr B ly2 q) -> lpost S2 ->
(q = PNull -> val_mem segs (mrestrict (w_H W2) mem2) oomb 1 1) ->
(q <> PNull -> In (q, n) (blocks S2)) ->
SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
(fun W' c' => exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
getr regs' 10 = w64 (sptr_addr B ly2 q) /\
ARX inst ly2 S2 W' mem' md' /\ same_io md2 md' /\ rkeep regs W2 mem2 W' mem' /\ rwin regs W' mem' /\
(q = PNull -> val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
val_mem segs (mrestrict (w_H W') mem') oomb 1 1)).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The composition.                                                                                                  *)

Theorem rg_realloc_all : forall (K1 : K1_t) (K2 K3 : K2_t),
as_errno B = as_tp B - 0xa4 ->
aalloc_realizes segs B U mt ARX AOX rpreA nmax lmax lpost pcA oomb 8 1 1 ->
adealloc_realizes_raw segs B U ft ARX AOX rpreD lpost fpre pcD 1 (fun _ => True) ->
amemcpy_realizes segs pcM -> rmodel_ok ->
seg_pre K1 -> seg_mid_a K1 K2 -> seg_mid_b K2 K3 -> seg_ret K3 -> seg_nret K1 ->
arealloc_realizes_all segs B mt ft ARX AOX rpre nmax lmax lpost fpre rU RSTACK pcR pc0 inst oomb.
Proof.
intros K1 K2 K3 HERR HA HD HM [MO1 MO2] SPRE SMA SMB SRET SNRET.
intros ly S W regs mem md p n_old n ch PRE RP HBLK HFP HA0 HA1 HN HL HU.
set (tr := call_trace ly pc0 regs ch) in *.
assert (ENT : rentry ly S W regs mem md p n_old n ch)
by exact (conj PRE (conj RP (conj HBLK (conj HFP (conj HA0 (conj HA1 (conj HN (conj HL HU)))))))).
unfold realloc_tree_with.
eapply amreal_mbind; [exact (rg_apath_gflag segs _ _ _ _ (SPRE ly S W regs mem md p n_old n ch ENT))|].
intros [] S1 W1 c1 H1. cbv beta in H1.
destruct H1 as [(so & bp & regsA & memA & mdA & Ec1 & APREi & WLE1 & IO1 & WIN1 & FR1 & FR1w & HK1) (trc1 & HP1 & HG1)].
subst c1. cbn [snd] in *.
destruct (MO1 S n tr trc1 S1 RP HN HL HU HP1 HG1) as (UA1 & RA1 & BB1 & BL1 & SEC1 & AOX1).
pose proof (APREi RA1 BB1 UA1) as APR.
assert (BLK1 : In (p, n_old) (blocks S1)) by (rewrite BL1; exact HBLK).
eapply amreal_mbind; [exact (HA inst so bp ly S1 W1 regsA memA mdA n tr APR)|].
intros q S2 W2 c2 HAL.
destruct HAL as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & (trc2 & HP2 & HG2) & OOM2).
subst c2. cbn [fst snd] in *.
destruct (MO2 S n tr trc1 S1 trc2 q S2 RP HN HL HU HP1 HG1 HP2 HG2) as (UD2 & QB2 & PB2).
destruct (PB2 p n_old HBLK) as (BLK2 & RD2 & QP2).
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
assert (LLE02 : layout_le (length (st_secs S)) ly ly2)
by exact (layout_le_trans _ _ ly ly ly2 SEC1 (layout_le_refl _ ly) LLE2).
(* The frame from realloc's entry to Allocate's return, outside Allocate's block. *)
assert (FR02 : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly2 S2 a -> ~ ascratch B ASTACK regs a ->
~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha NA NA2 NS NE.
  rewrite (FR2 a Ha (fun X => NA (AOX1 ly a X)) NA2 (fun X => NS (rg_scratch_in B regs regsA AFSTACK_G a (proj1 WIN1) (proj2 WIN1) X)) NE).
  exact (FR1 a Ha NA NS). }
assert (FR02w : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly2 S2 (bv_unsigned x) ->
~ ascratch B ASTACK regs (bv_unsigned x) ->
~ (q <> PNull /\ sptr_addr B ly2 q <= bv_unsigned x < sptr_addr B ly2 q + req_size n) -> mem2 x = mem x).
{ intros x NA NA2 NS NE.
  rewrite (FR2w x (fun X => NA (AOX1 ly _ X)) NA2 (fun X => NS (rg_scratch_in B regs regsA AFSTACK_G _ (proj1 WIN1) (proj2 WIN1) X)) NE).
  exact (FR1w x NA NS). }
destruct (rg_null_dec q) as [EQ | HQ].
- (* The NULL-return arm. *)
  subst q.
  eapply amreal_SRr_pre; [exact (SNRET HERR ly S W regs mem md p n_old n ch S1 W1 so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2
    ENT HK1 APR APO A02 LP2 (OOM2 eq_refl) BLK1 BLK2)|].
  intros W' c' WLE2' (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN' & ER' & OM'). subst c'.
  rewrite realloc_k_null. apply amreal_ret.
  split.
  { exists (trc1 ++ trc2 ++ []). split; [exact (rg_trace_null mt ft p n tr S trc1 S1 trc2 S2 HP1 HP2)|].
    rewrite !rg_gflag_app, HG1, HG2. reflexivity. }
  exists ly2, regs', mem', md'. cbn [fst snd].
  split; [reflexivity|]. split; [exact CS'|]. split; [exact LP2|].
  split; [|intros X; exfalso; exact (X eq_refl)].
  intros _. split; [exact A0'|].
  split.
  { split; [exact ARX'|]. split; [exact LLE02|].
    split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE2']|].
    split; [exact (rg_same_io_trans _ _ _ (rg_same_io_trans _ _ _ IO1 IO2) IO')|].
    split.
    { intros a Ha NA NA2 NS _. rewrite (proj1 KP' a Ha NS). exact (FR02 a Ha NA NA2 NS (fun X => proj1 X eq_refl)). }
    split; [|exact WN'].
    intros x NA NA2 NS _. rewrite (proj2 KP' x NS). exact (FR02w x NA NA2 NS (fun X => proj1 X eq_refl)). }
  split; [exact (ex_intro _ S1 (ex_intro _ trc1 (ex_intro _ trc2 (conj HP1 (conj HG1 (conj HP2 HG2))))))|].
  split; [exact BLK2|]. split; [exact ER' | exact OM'].
- (* A block q: the copy, the free of the old block, the return. *)
  rewrite (realloc_k_block ft p tr q HQ).
  eapply amreal_SRr_pre; [exact (SMA ly S W regs mem md p n_old n ch S1 W1 so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
    ENT HK1 APR APO A02 HQ (QB2 HQ) (QP2 HQ) LP2 BLK1 BLK2 (RD2 HQ))|].
  intros W3 c3 WLE23 (regsM & memM & mdM & Ec3 & MPRE & SRC & NBLK & IO3 & KP3 & HK2). subst c3.
  eapply amreal_SRr_pre; [exact (HM W3 regsM memM mdM _ _ _ MPRE)|].
  intros W3' c3' _ (EW3 & regs3 & mem3 & md3 & Ec3' & CS3 & IO3' & CPY3 & FR3 & PR3). subst W3' c3'.
  eapply amreal_SRr_pre; [exact (SMB ly S W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3
    ENT HK2 BLK2 (RD2 HQ) (UD2 HQ) CS3 IO3' CPY3 FR3 PR3)|].
  intros W4 c4 WLE34 (so' & bp' & regsD & memD & mdD & Ec4 & DPR & IO4 & WIN4 & KP4 & WN4 & HK3). subst c4.
  eapply amreal_mbind; [exact (HD inst so' bp' ly2 S2 W4 regsD memD mdD p n_old tr DPR I)|].
  intros [] S3 W5 c5 HDL.
  destruct HDL as (ly3 & regs5 & mem5 & md5 & Ec5 & DPO & LP3 & (trc3 & HP3 & HG3)). subst c5. cbn [snd] in *.
  pose proof DPO as (ARX3 & LLE3 & WLE45 & CS5 & IO5 & FR5 & FR5w & PR5).
  eapply amreal_SRr_pre; [exact (SRET ly S W regs mem md p n_old n ch q ly2 S2 W4 so' bp' regsD memD mdD ly3 S3 W5 regs5 mem5 md5
    ENT HK3 DPR DPO LP3)|].
  intros W' c' WLE5' (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN'). subst c'.
  cbv beta. apply amreal_ret.
  pose proof (rg_req_size n (proj1 HN)) as RQ.
  split.
  { exists (trc1 ++ trc2 ++ trc3 ++ []). split; [exact (rg_trace_block mt ft p n tr S trc1 S1 trc2 q S2 trc3 S3 HQ HP1 HP2 HP3)|].
    rewrite !rg_gflag_app, HG1, HG2, HG3. reflexivity. }
  exists ly3, regs', mem', md'. cbn [fst snd].
  split; [reflexivity|]. split; [exact CS'|]. split; [exact LP3|].
  split; [intros X; exfalso; exact (HQ X)|].
  intros _. exists ly2, S2, W4, memD, mdD.
  split; [exact A0'|].
  split.
  { split; [exact (proj1 DPR)|]. split; [exact LLE02|].
    split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2|]; eapply wle_trans; [exact WLE23 | exact WLE34]|].
    split; [exact (rg_same_io_trans _ _ _ (rg_same_io_trans _ _ _ (rg_same_io_trans _ _ _ (rg_same_io_trans _ _ _ IO1 IO2) IO3) (rg_sbm_io _ _ IO3')) IO4)|].
    split.
    { intros a Ha NA NA2 NS NE.
      rewrite (proj1 KP4 a Ha NS).
      rewrite (rg_aview_same segs (w_H W3) memM mem3 a (FR3 _ ltac:(rewrite (rg_unsigned_small a Ha); intros X; apply NE; rewrite RQ; lia))).
      rewrite (proj1 KP3 a Ha NS).
      exact (FR02 a Ha NA NA2 NS (fun X => NE (proj2 X))). }
    split; [|exact WN4].
    intros x NA NA2 NS NE.
    rewrite (proj2 KP4 x NS).
    rewrite (FR3 x ltac:(intros X; apply NE; rewrite RQ; lia)).
    rewrite (proj2 KP3 x NS).
    exact (FR02w x NA NA2 NS (fun X => NE (proj2 X))). }
  split.
  { exists (trc1 ++ trc2). split; [exact (rg_apath_bind (ft PNull tr) (fun _ => mt n tr) S trc1 tt S1 trc2 (q, S2) HP1 HP2)|].
    rewrite rg_gflag_app, HG1, HG2. reflexivity. }
  split; [exact LP2|].
  split.
  { intros i Hi.
    assert (Hi' : 0 <= i < Z.min (req_size n_old) n) by (pose proof (rg_req_size_ge n_old); lia).
    assert (Hq : sptr_addr B ly2 q <= sptr_addr B ly2 q + i < sptr_addr B ly2 q + req_size n) by (rewrite RQ; lia).
    destruct (NBLK _ Hq) as [Ra NS].
    rewrite (proj1 KP4 _ Ra NS), (CPY3 i Hi'), (SRC i Hi'). reflexivity. }
  split.
  { split; [exact ARX'|]. split; [exact LLE3|].
    split; [eapply wle_trans; [exact WLE45 | exact WLE5']|].
    split; [exact (rg_same_io_trans _ _ _ IO5 IO')|].
    split.
    { intros a Ha NA2 NA3 NS NE.
      rewrite (proj1 KP' a Ha NS).
      exact (FR5 a Ha NA2 NA3 (fun X => NS (rg_scratch_in B regs regsD DFSTACK_G a (proj1 WIN4) (proj2 WIN4) X)) (fun X => NE (proj2 X))). }
    split; [|exact WN'].
    intros x NA2 NA3 NS NE.
    rewrite (proj2 KP' x NS).
    exact (FR5w x NA2 NA3 (fun X => NS (rg_scratch_in B regs regsD DFSTACK_G _ (proj1 WIN4) (proj2 WIN4) X)) (fun X => NE (proj2 X))). }
  exists trc3. split; [exact HP3 | exact HG3].
Qed.

Theorem rg_realloc_null : forall (Kn : Kn_t),
as_errno B = as_tp B - 0xa4 ->
aalloc_realizes segs B U mt ARX AOX rpreA nmax lmax lpost pcA oomb 8 1 1 -> rmodel_ok ->
seg_npre Kn -> seg_npost Kn ->
arealloc_null_realizes segs B mt ft ARX AOX rpre nmax lmax lpost rU RSTACK pcR pc0 inst oomb.
Proof.
intros Kn HERR HA [MO1 MO2] SNPRE SNPOST.
intros ly S W regs mem md n ch PRE RP HA0 HA1 HN HL HU.
set (tr := call_trace ly pc0 regs ch) in *.
assert (ENT : rnentry ly S W regs mem md n ch)
by exact (conj PRE (conj RP (conj HA0 (conj HA1 (conj HN (conj HL HU)))))).
unfold realloc_null_tree_with.
eapply amreal_mbind; [exact (rg_apath_gflag segs _ _ _ _ (SNPRE ly S W regs mem md n ch ENT))|].
intros [] S1 W1 c1 H1. cbv beta in H1.
destruct H1 as [(so & bp & regsA & memA & mdA & Ec1 & APREi & WLE1 & IO1 & WIN1 & FR1 & FR1w & HKn) (trc1 & HP1 & HG1)].
subst c1. cbn [snd] in *.
destruct (MO1 S n tr trc1 S1 RP HN HL HU HP1 HG1) as (UA1 & RA1 & BB1 & BL1 & SEC1 & AOX1).
pose proof (APREi RA1 BB1 UA1) as APR.
eapply rg_then_SRr; [exact (HA inst so bp ly S1 W1 regsA memA mdA n tr APR)|].
intros [q S2] W2 c2 HAL.
destruct HAL as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & (trc2 & HP2 & HG2) & OOM2).
subst c2. cbn [fst snd] in *.
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
destruct (MO2 S n tr trc1 S1 trc2 q S2 RP HN HL HU HP1 HG1 HP2 HG2) as (_ & QB2 & _).
eapply SRr_mono; [exact (SNPOST HERR ly S W regs mem md n ch S1 W1 so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
  ENT HKn APR APO A02 LP2 OOM2 QB2)|].
intros W' c' WLE2' (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN' & ENM'). subst c'.
split.
{ exists (trc1 ++ trc2). split; [exact (rg_apath_bind (ft PNull tr) (fun _ => mt n tr) S trc1 tt S1 trc2 (q, S2) HP1 HP2)|].
  rewrite rg_gflag_app, HG1, HG2. reflexivity. }
exists ly2, regs', mem', md'. cbn [fst snd].
split; [reflexivity|]. split; [exact CS'|]. split; [exact LP2|]. split; [exact A0'|].
split.
{ split; [exact ARX'|]. split; [exact (layout_le_trans _ _ ly ly ly2 SEC1 (layout_le_refl _ ly) LLE2)|].
  split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE2']|].
  split; [exact (rg_same_io_trans _ _ _ (rg_same_io_trans _ _ _ IO1 IO2) IO')|].
  split.
  { intros a Ha NA NA2 NS NE. rewrite (proj1 KP' a Ha NS).
    rewrite (FR2 a Ha (fun X => NA (AOX1 ly a X)) NA2 (fun X => NS (rg_scratch_in B regs regsA AFSTACK_G a (proj1 WIN1) (proj2 WIN1) X)) NE).
    exact (FR1 a Ha NA NS). }
  split; [|exact WN'].
  intros x NA NA2 NS NE. rewrite (proj2 KP' x NS).
  rewrite (FR2w x (fun X => NA (AOX1 ly _ X)) NA2 (fun X => NS (rg_scratch_in B regs regsA AFSTACK_G _ (proj1 WIN1) (proj2 WIN1) X)) NE).
  exact (FR1w x NA NS). }
intros EQ. subst q. destruct (ENM' eq_refl) as [ER' OM'].
split; [exact (ex_intro _ S1 (ex_intro _ trc1 (ex_intro _ trc2 (conj HP1 (conj HG1 (conj HP2 HG2))))))|].
split; [exact ER' | exact OM'].
Qed.
End b.
End a.
