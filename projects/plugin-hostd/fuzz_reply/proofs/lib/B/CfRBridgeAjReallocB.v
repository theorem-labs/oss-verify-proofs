(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: plugin-hostd/fuzz_reply.asan-ubsan, the cf allocator bridge (new file).
   IMAGE B TWIN (row G-BCF): lib/A/CfRBridgeAjRealloc.v at c6394a5bd7e, under lib/B so the B tree is self-contained
   (as lib/B/CfParamsReplyB.v). One change, the P'' carry of record (Reusable YGcallx.v (sha256 1dd2a7cdc3ee; internal record), YGcfRealloc.v,
   YGcfAmx2.v, YG03dcf.v, YG07cf.v): the realizes texts and the model lemmas take `admits (as_universe B) tr S`.
   The two definitions arealloc_realizes_cf_rp and amx_realloc_rp take it too (one text at A and B: CfR takes them by
   path), so arealloc_realizes_cf_rp_true and amx_realloc_rp_room stay one exact each; the rules and the model
   facts of this file keep their `In` premise and convert it by YG01.admits_fix from the universe_ok they already
   take, as YGcallx.v's own rules do (its header, line 6). So aj_realloc_at_x_ct now also uses Section J's HU, and
   after the Section it takes one more argument, universe_ok (as_universe B), right after errno_low (as
   aj_realloc_null_at_x_ct already did on A). The A file's text follows. This file holds the
   journal-level CALL-SITE RULES for realloc(p, n) on a live block and for realloc(NULL, n), over the cf realloc
   contracts (Reusable/YGcfRealloc.v:97-116 arealloc_realizes_cf / arealloc_null_realizes_cf, over
   Reusable/ReallocP.v:32-44 realloc_tree_with / realloc_null_tree_with). They are the twins of
   Reusable/YGcallx.v:927-1056 aj_malloc_at_x_ct (and, for the old block, :507-613 aj_free_at_x_ct), at the shared
   shape of Reusable/YGcallcf.v:252-394: ARx := ARxs (ARcf /\ xs_placed_cf), QM := QM_cf, XS := xs_cf, with the
   laws AR_laws_x_xs / ARx_owned_low_law_xs / ARx_wf_law_xs / ARx_xs_law_xs. Same steps as the template: the call's
   pre (acall_pre_x, YGcallx.v:959-968), amreal_SRr04 + SRr_mono with the model's safety / progress / no-spin facts,
   the model post on the granted path, acall_post_journal_xw (with the error-buffer write set and xs_cf), then
   ajournal_x_nil_pst + ajournal_x_sub to the caller's journal and acall_kept_of_journal_x.
   1. arealloc_realizes_cf_rp: arealloc_realizes_cf's text with `RP S ->` after acall_pre_cf, for a room
      predicate RP; RP := fun _ => True is implied by arealloc_realizes_cf (arealloc_realizes_cf_rp_true), and
      RP := fun S => ROOM_cf_k S RK_realloc is the lane's room form.
   2. The model facts. realloc(p, n): the inner free of the old block runs after the malloc, so its room at the
      post-malloc state is not a consequence of QM_cf; amx_realloc_rp RP states the facts as a premise (the
      weakest form the rule needs), and amx_realloc_rp_room proves it at the room form from
      Reusable/YGcfAmx2.v:233 amx_realloc_cf (k = 0). realloc(NULL, n): the facts are proved here
      (cfr_aj_null_atok, cfr_aj_amx_null) by composing the free(NULL) token (YG03dcf ml_free_cf, YGcfAmx2
      ipost_free_null) with the malloc token (YG07cf malloc_ok_cf), as YGcfAmx2.v:129-183 realloc_cf_atok does.
   3. The rules aj_realloc_at_x_ct and aj_realloc_null_at_x_ct. The realloc post hands back the granted model path,
      the realloc leaf, the refusal witness on NULL, and realloc_hp_cf = Hpc (the base is not hidden at the call, so
      the ghost set after the call is the caller's); on success the old block's bytes are the call's footprint
      (as aj_free_at_x_ct's) and the new block's are fresh.
   Rule 24: no function is proved; statement composition over the cf contracts and model lemmas only.
   Event terms: st_nev appears only in the journal index k + (st_nev S2 - st_nev Sc) and, inside the proofs, in the
   call journal's index st_nev S2 - st_nev Sc, both as YGcallx.v:940 / :993 (exception 3, the tick update).
   Numerals: 1, 3, 4, 10, 11 are RISC-V register numbers; 12 (ENOMEM) and 1 (the out-of-memory byte) are stored
   values; 0, 16, 4096, 16384 (= ASTACK) are YGcallx's LENGTH / DERIVED constants. No ADDRESS. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YGcfRoomPre YGcfXs YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG03cf YG03dcf YG06bcf YG07cf YGcfAmx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfPath ReallocP YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomKeep.
(* Required, not Imported: YGcfAmx2 restates universe_ok_of_ARcf (YGcallcf's name); cited by qualified name. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfAmx2.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section CfRAj. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.

(* ---------------------------------------------------------------------------- *)
(* 1. The realizes form with a room predicate.                                    *)
(* YGcfRealloc.v:97-108 arealloc_realizes_cf with `RP S ->` right after acall_pre_cf. *)
Definition arealloc_realizes_cf_rp (segs : list Segment) (B : asyms) (RP : astate -> Prop) (Hp : list Z) (pc : Z) : Prop :=
forall ly S W regs mem md p n_old n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch -> RP S ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly cf_pc_realloc_ra0 regs ch) S ->
amreal segs (realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => realloc_leaf_cf segs B ly S Hp W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> mt_refused malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S (snd r))).

Lemma arealloc_realizes_cf_rp_true : forall segs B Hp pc,
arealloc_realizes_cf segs B Hp pc -> arealloc_realizes_cf_rp segs B (fun _ => True) Hp pc.
Proof. intros segs B Hp pc H ly S W regs mem md p n_old n ch Hpre _. exact (H ly S W regs mem md p n_old n ch Hpre). Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The model facts.                                                            *)
(* realloc(p, n): what the rule reads off the model at a QM_cf state with room RP (YGcallx.v:347-354's four facts,
   with YGcfAmx2.v:58 realloc_post_cf as the post). *)
Definition amx_realloc_rp (B : asyms) (RP : astate -> Prop) : Prop :=
forall s p n_old n tr, Wf_cf (as_universe B) s -> QM_cf s -> RP s ->
In (p, n_old) (blocks s) -> 1 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits (as_universe B) tr s ->
asafe (realloc_tree_with malloc_cf free_cf p n tr s) /\ agprog (realloc_tree_with malloc_cf free_cf p n tr s) /\
is_spin (realloc_tree_with malloc_cf free_cf p n tr s) = false /\
(forall tr' r, apath (realloc_tree_with malloc_cf free_cf p n tr s) tr' r -> YGcfAmx2.realloc_post_cf s p n_old n r).

(* At the room form: YGcfAmx2.v:233 amx_realloc_cf at k = 0 (qtight from qmeter_cf). *)
Lemma amx_realloc_rp_room : forall B, universe_ok (as_universe B) -> amx_realloc_rp B (fun S => ROOM_cf_k S RK_realloc).
Proof.
intros B HU s p n_old n tr HW HQ HR Hp Hn Hl Ht.
exact (YGcfAmx2.amx_realloc_cf B s p n_old n tr 0 HU HW (proj1 (proj1 HQ)) HR Hp Hn Hl Ht).
Qed.

(* realloc(NULL, n): free_cf PNull, then malloc_cf n (YGcfAmx2.v:137-157's first two steps). *)
Lemma cfr_aj_null_atok : forall U s n tr,
universe_ok U -> Wf_cf U s -> ROOM_cf s -> 0 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok_cf true (realloc_null_tree_with malloc_cf free_cf n tr s) (fun _ r => malloc_post_x s n r).
Proof.
intros U s n tr HU W HR Hn Hlive Htr.
unfold realloc_null_tree_with. apply atok_cf_bind.
assert (A1 : atok_cf true (free_cf PNull tr s) (free_post_ycf U s PNull 0)).
{ destruct HR as (_ & _ & HB). eapply ml_free_cf; eauto using admits_fix. }
eapply atok_cf_mono; [|exact (atok_cf_ipost _ _ _ _ A1 (YGcfAmx2.ipost_free_null tr s))].
intros b [[] s1] [F1 N1]. cbn [fst snd] in *.
unfold free_post_ycf in F1. cbn [snd] in F1. destruct F1 as (W1 & Nev1 & X1 & Fr1 & (l1 & l2 & Bs1 & Bl1) & _).
assert (B1 : blocks s1 = blocks s).
{ rewrite Bl1. destruct Bs1 as [[_ E]|E]; [exact E|].
  exfalso. apply (YGcfAmx2.no_null_block _ _ _ _ s 0 W). rewrite E. apply in_or_app. right. left. reflexivity. }
pose proof (YGcfAmx2.ROOM_cf_nfr s s1 N1 HR) as HR1. destruct HR1 as (HS1 & HE1 & HB1).
assert (Hlive1 : blocks_bytes s1 + n <= LIVE_MAX)
  by (rewrite YGcfAmx2.blocks_bytes_blocks, B1, <- YGcfAmx2.blocks_bytes_blocks; exact Hlive).
pose proof (malloc_ok_cf U s1 n tr HU W1 Hn Hlive1 (admits_fix _ _ s1 HU Htr) HS1 HE1 HB1) as A2.
apply YGcfAmx2.atok_cf_any_ns; [intros b1 b2 a H; exact H|].
eapply atok_cf_mono; [|exact A2].
intros b2 [q s2] M2. unfold malloc_post_cf in M2. cbv beta iota in M2. destruct M2 as (W2 & Nev2 & X2 & Fr2 & Bl2 & _).
pose proof (proj1 (secs_ext_cf_of_secs_ext _ _ X1)) as L1. pose proof (proj1 X2) as L2.
unfold malloc_post_x. cbv beta iota.
split; [lia|]. split; [lia|]. split; [congruence|].
destruct q as [|qo|qr qo|qc qp]; cbv beta iota in Bl2 |- *.
- rewrite Bl2. exact B1.
- rewrite (proj1 Bl2), B1. reflexivity.
- rewrite (proj1 Bl2), B1. reflexivity.
- rewrite (proj1 Bl2), B1. reflexivity.
Qed.

Lemma cfr_aj_amx_null : forall B s n tr,
universe_ok (as_universe B) -> Wf_cf (as_universe B) s -> QM_cf s -> 0 <= n < cf_malloc_max ->
blocks_bytes s + n <= LIVE_MAX -> In tr (as_universe B) ->
asafe (realloc_null_tree_with malloc_cf free_cf n tr s) /\ agprog (realloc_null_tree_with malloc_cf free_cf n tr s) /\
is_spin (realloc_null_tree_with malloc_cf free_cf n tr s) = false /\
(forall tr' r, apath (realloc_null_tree_with malloc_cf free_cf n tr s) tr' r -> malloc_post_x s n r).
Proof.
intros B s n tr HU W HQ Hn Hl Ht.
assert (HR : ROOM_cf s) by (destruct HQ as (_ & R1 & R2 & _ & R3 & _); exact (conj R1 (conj R2 R3))).
pose proof (cfr_aj_null_atok (as_universe B) s n tr HU W HR Hn Hl Ht) as A.
split; [exact (atok_cf_asafe _ _ _ A)|]. split; [exact (atok_cf_agprog _ _ _ A)|].
split; [exact (atok_cf_nospin _ _ A)|].
intros tr' r Hpath. destruct (atok_cf_apath _ _ _ tr' r A Hpath) as [ns H]. exact H.
Qed.

(* ---------------------------------------------------------------------------- *)
(* Small facts.                                                                   *)
(* The ghost set after the call is the caller's when the base is not hidden (YGcfRealloc.v:46-50). *)
Lemma cfr_aj_hp_notin : forall B ly p q Hp, ~ In (sptr_addr B ly p) Hp -> realloc_hp_cf B ly p q Hp = Hp.
Proof.
intros B ly p q Hp H. unfold realloc_hp_cf.
destruct q; [reflexivity | exact (notin_remove Z.eq_dec Hp (sptr_addr B ly p) H) ..].
Qed.

Lemma cfr_aj_rng_dec : forall a b l : Z, (b <= a < b + l) \/ ~ (b <= a < b + l).
Proof. intros a b l. lia. Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The call-site rules, at the shared cf shape (YGcallcf.v:241-394).          *)
Section J.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Hypothesis L : AR_laws_cf segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis HU : universe_ok (as_universe B).
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).
Local Abbreviation LAWS := (AR_laws_x_xs segs B L).
Local Abbreviation OWNLOW := (ARx_owned_low_law_xs segs B L).
Local Abbreviation WFL := (ARx_wf_law_xs segs B).
Local Abbreviation XSL := (ARx_xs_law_xs segs B).
Local Abbreviation LBLK := (alx_blocks segs B ARxs LAWS).
Local Abbreviation LLAY := (alx_layout segs B ARxs LAWS).

(* YGcallx.v:848 xs_write_ok, where a pre block may be gone after the call provided the byte is not in it. *)
Lemma cfr_aj_xs_write_ok : forall lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 a,
ARxs lyc Sc Hpc W memc mdc -> ARxs ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 ->
(forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) \/ ~ (b <= a < b + req_size m)) ->
(forall f, In f (frames Sc) -> In f (frames S2)) ->
Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2) ->
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
  split; [intros p n Hin; destruct (Hab p n Hin) as [H|H]; [exact (Xb p n H) | exact H]|].
  split; [intros cid pos Hin; rewrite <- Efa; exact (Xf cid pos (Hfr _ Hin))|].
  rewrite <- Eextra. exact Xe.
Qed.

(* (1) realloc(p, n) of a live block: YGcallx.v:927 aj_malloc_at_x_ct's steps over YGcfRealloc's contract, with
   aj_free_at_x_ct's footprint for the old block. *)
Lemma aj_realloc_at_x_ct : forall (RP : astate -> Prop) (pc : Z), amx_realloc_rp B RP ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n0 n (o : Z) raw ch,
arealloc_realizes_cf_rp segs B RP Hpc pc ->
ajournal_x segs B PST ARxs STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n0) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa -> getr regsT 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc memT -> RP Sc ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc cf_pc_realloc_ra0 regsT ch) (as_universe B) ->
(In (pa, n0) (ablocks B ly S) -> forall i, 0 <= i < req_size n0 -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARxs STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
(exists q p trc, sptr_addr B lyc p = pa /\ In (p, n0) (blocks Sc) /\
 apath (realloc_tree_with malloc_cf free_cf p n (call_trace lyc cf_pc_realloc_ra0 regsT ch) Sc) trc (q, S2) /\
 YG0d.gflag trc = true /\
 realloc_leaf_cf segs B lyc Sc Hpc W regsT memT mdc p n0 n (q, S2) W2 c2 /\
 (q = PNull -> mt_refused malloc_cf free_cf n (call_trace lyc cf_pc_realloc_ra0 regsT ch) Sc S2) /\
 realloc_hp_cf B lyc p q Hpc = Hpc /\
 (q = PNull <-> res = 0) /\ (q <> PNull -> res = sptr_addr B ly2 q) /\
 (q <> PNull -> forall i, 0 <= i < Z.min n0 n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (pa + i)) /\
 (q <> PNull -> forall i, 0 <= i < 4 -> mem2 (w64 (as_errno B + i)) = memT (w64 (as_errno B + i))) /\
 (forall x : word, ~ aowned B lyc Sc (bv_unsigned x) -> ~ aowned B ly2 S2 (bv_unsigned x) ->
  ~ ascratch B ASTACK regsT (bv_unsigned x) ->
  ~ ((q <> PNull /\ res <= bv_unsigned x < res + req_size n) \/ (q <> PNull /\ pa <= bv_unsigned x < pa + req_size n0)
     \/ Exists (in_zr (bv_unsigned x)) (xs_cf lyc Sc ++ xs_cf ly2 S2)) ->
  mem2 x = memT x)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
 \/ (4096 <= res /\
  (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n0) :: l2 /\ Permutation (ablocks B ly2 S2) ((res, n) :: l1 ++ l2)) /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
   (fun a => (res <= a < res + req_size n) \/ (pa <= a < pa + req_size n0))))).
Proof.
intros RP pc AMR W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n0 n o raw ch
AREAL HJ Hin Hnhp Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM HRP Hch Htr HFP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (proj1 (in_ablocks B lyc Sc pa n0) Hin) as (p & Hpq & Hpin).
destruct (LBLK lyc Sc Hpc W memT mdc pa n0 HAR Hin) as (Hpa16 & Hpa4096 & Hpaceil & [Hpah Hpah2] & Hpab & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
destruct (proj1 (acall_pre_x_xs segs B lyc Sc Hpc W regsT memT mdc ch) HPRE) as [HPREcf HXc].
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof (AMR Sc p n0 n (call_trace lyc cf_pc_realloc_ra0 regsT ch) HWF (QMQ_cf segs B Sc memT HQM) HRP Hpin Hn Hlive
  (admits_fix _ _ Sc HU Htr))
as (HSAFE & HPROG & HNSP & HMP).
pose proof (AREAL lyc Sc W regsT memT mdc p n0 n ch HPREcf HRP Hpin ltac:(rewrite Hpq; exact Ha0)
ltac:(rewrite Hpq; exact Hnhp) Ha1 Hn Hlive (admits_fix _ _ Sc HU Htr)) as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & [Hleaf Href]).
pose proof (HMP tr r Hpath) as HQ. destruct r as [q S2]. unfold YGcfAmx2.realloc_post_cf in HQ.
cbn [fst snd] in HQ, Href.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & HblN & HblS).
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOSTcf & Hres & HQT2 & Hcopy & HERR & HX2 & Herrno & Hrawf).
cbn [fst snd] in HPOSTcf, Hres, HQT2, HERR, HX2, Hcopy, Herrno, Hrawf.
assert (EHp : realloc_hp_cf B lyc p q Hpc = Hpc) by (apply cfr_aj_hp_notin; rewrite Hpq; exact Hnhp).
rewrite EHp in HPOSTcf.
pose proof HPOSTcf as (HAR2cf & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
assert (HAR2 : ARxs ly2 S2 Hpc W2 mem2 md2) by exact (conj HAR2cf HX2).
assert (HPOST : acall_post_x segs B ARxs ASTACK lyc Sc Hpc W regsT memT mdc
  (fun a => (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)
   \/ (q <> PNull /\ sptr_addr B lyc p <= a < sptr_addr B lyc p + req_size n0)
   \/ Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2)) ly2 S2 W2 regs2 mem2 md2).
{ split; [exact HAR2|]. exact (conj Hly2 (conj Hwle2' (conj HP (conj Hio2 (conj Hfr2 Hpres2))))). }
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
destruct (asptr_null_dec q) as [-> | Hqn].
- (* NULL: the old block stays, Hp and the blocks are unchanged *)
cbn in Hres.
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite (HblN eq_refl). apply map_ext_in. exact Efc. }
assert (HJ1 : ajournal_x segs B [] ARxs ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_xw segs B ARxs LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2)) [] (st_nev S2 - st_nev Sc));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a Ha. apply (cfr_aj_xs_write_ok lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b m Hb; left; rewrite Eab2; exact Hb | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[Hf _] | [[Hf _] | Hx]]; [exfalso; exact (Hf eq_refl) | exfalso; exact (Hf eq_refl) | left; exact Hx].
- intros q' m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_sub segs B PST ARxs LAWS segs_low);
[exact HJ | exact (ajournal_x_nil_pst segs B ARxs PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|].
split.
{ exists PNull, p, tr. split; [exact Hpq|]. split; [exact Hpin|]. split; [exact Hpath|]. split; [exact Hgf|].
split; [exact Hleaf0|]. split; [exact Href|]. split; [exact EHp|].
split; [split; intros _; reflexivity|].
split; [intros Hc; exfalso; exact (Hc eq_refl)|]. split; [intros Hc; exfalso; exact (Hc eq_refl)|].
split; [intros Hc; exfalso; exact (Hc eq_refl)|].
intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
intros [[Hc _]|[[Hc _]|Hx]]; [exact (Hc eq_refl) | exact (Hc eq_refl) | apply H4; right; right; exact Hx]. }
left. split; [reflexivity|]. split; [exact Eab2|].
split.
{ rewrite Hsp' in HJ1. eapply (acall_kept_of_journal_x segs B ARxs segs_low);
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
exact (HERR eq_refl).
- (* success: the old block leaves, the new block is appended *)
destruct (HblS Hqn) as (l1 & l2 & Hsplit & Hbl2).
set (res := sptr_addr B ly2 q) in *.
assert (EabC : ablocks B lyc Sc = map fc l1 ++ (pa, n0) :: map fc l2).
{ unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n0) :: map fc l2). rewrite Hsplit, map_app. cbn [map app].
replace (fc (p, n0)) with (pa, n0) by (subst fc; cbn [fst snd]; rewrite Hpq; reflexivity). reflexivity. }
assert (Eab2 : ablocks B ly2 S2 = map fc l1 ++ map fc l2 ++ [(res, n)]).
{ unfold ablocks. change (map f2 (blocks S2) = map fc l1 ++ map fc l2 ++ [(res, n)]). rewrite Hbl2, !map_app. cbn [map].
assert (E1 : map f2 l1 = map fc l1)
by (apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app; left; exact Hb).
assert (E2 : map f2 l2 = map fc l2)
by (apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app; right; right; exact Hb).
rewrite E1, E2. reflexivity. }
assert (Hnew : In (res, n) (ablocks B ly2 S2)).
{ rewrite Eab2. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
destruct (LBLK ly2 S2 Hpc W2 mem2 md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
assert (HnewNotPre : forall a, res <= a < res + req_size n -> ~ (pa <= a < pa + req_size n0) ->
~ In (res, n) (ablocks B lyc Sc)).
{ intros a Ha Hna Hin'. rewrite EabC in Hin'. apply in_app_or in Hin' as [H1 | [H1 | H1]].
- apply in_split in H1 as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos_x segs B ARxs LAWS ly2 S2 Hpc W2 mem2 md2 (res, n) (res, n) b1 (b2 ++ map fc l2) [] HAR2
ltac:(rewrite Eab2, Ebq, <- !app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia.
- injection H1 as E1 E2. apply Hna. rewrite E1, E2. exact Ha.
- apply in_split in H1 as (b1 & b2 & Ebq).
pose proof (sep_blocks_pos_x segs B ARxs LAWS ly2 S2 Hpc W2 mem2 md2 (res, n) (res, n) (map fc l1 ++ b1) b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- !app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal_x segs B [] ARxs ASTACK (spZ regsT) [(pa, pa + req_size n0)] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_xw segs B ARxs LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2) /\ ~ (pa <= a < pa + req_size n0))
[(pa, pa + req_size n0)] (st_nev S2 - st_nev Sc));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a [Hx Hna]. apply (cfr_aj_xs_write_ok lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[ | intros f Hf; rewrite Hfrs2; exact Hf | exact Hx].
intros b m Hb. rewrite EabC in Hb. apply in_app_or in Hb as [H1 | [H1 | H1]].
+ left. rewrite Eab2. apply in_or_app. left. exact H1.
+ right. injection H1 as <- <-. exact Hna.
+ left. rewrite Eab2. apply in_or_app. right. apply in_or_app. left. exact H1.
- intros a Ha. destruct (cfr_aj_rng_dec a pa (req_size n0)) as [Hold | Hnold].
+ right. exists pa, n0. split; [left; exact Hin|]. split; [exact Hold|]. left.
exists (pa, pa + req_size n0). split; [left; reflexivity | cbn [fst snd]; zlia].
+ destruct Ha as [[_ Ha] | [[_ Ha] | Hx]].
* right. exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right. exact (HnewNotPre a Ha Hnold).
* exfalso. rewrite Hpq in Ha. exact (Hnold Ha).
* left. exact (conj Hx Hnold).
- intros p' m i Hp' Hnp Hi. exists (pa, pa + req_size n0). split; [left; reflexivity|]. cbn [fst snd].
rewrite EabC in Hp'. apply in_app_or in Hp' as [H1 | [H1 | H1]].
+ exfalso. apply Hnp. rewrite Eab2. apply in_or_app. left. exact H1.
+ injection H1 as <- <-. zlia.
+ exfalso. apply Hnp. rewrite Eab2. apply in_or_app. right. apply in_or_app. left. exact H1. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_sub segs B PST ARxs LAWS segs_low);
[exact HJ | exact (ajournal_x_nil_pst segs B ARxs PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia |].
intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n0) (ablocks B ly S)) as [H0|H0].
- left. replace a with (pa + (a - pa)) by zlia. apply (HFP H0). zlia.
- right; left. exists pa, n0. split; [exact Hin|]. split; [exact H0 | zlia]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|].
split.
{ exists q, p, tr. split; [exact Hpq|]. split; [exact Hpin|]. split; [exact Hpath|]. split; [exact Hgf|].
split; [exact Hleaf0|]. split; [exact Href|]. split; [exact EHp|].
split; [split; [intros Hc; exfalso; exact (Hqn Hc) | intros Hc; zlia]|].
split; [intros _; reflexivity|].
split; [intros _ i Hi; rewrite <- Hpq; exact (Hcopy Hqn i Hi)|].
split; [exact Herrno|].
intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |]. rewrite Hpq. exact H4. }
right. split; [exact Hr4096|].
split.
{ exists (map fc l1), (map fc l2). split; [exact EabC|].
rewrite Eab2, app_assoc. apply Permutation_sym. apply Permutation_cons_append. }
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal_x segs B ARxs segs_low);
[exact HJ1 | exact HAR | | | apply sink_closed_pos; constructor; [cbn [fst]; zlia | constructor]].
+ intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right. exact Ha.
+ intros b m i Hb Hi HnE. rewrite EabC in Hb. apply in_app_or in Hb as [H1 | [H1 | H1]].
* rewrite Eab2. apply in_or_app. left. exact H1.
* exfalso. injection H1 as <- <-. apply HnE. right. zlia.
* rewrite Eab2. apply in_or_app. right. apply in_or_app. left. exact H1.
Qed.

(* (2) realloc(NULL, n): YGcallx.v:927 aj_malloc_at_x_ct over YGcfRealloc's arealloc_null_realizes_cf (leaf
   malloc_leaf_cf, tree free_cf PNull ;; malloc_cf n), the model facts from cfr_aj_amx_null. *)
Lemma aj_realloc_null_at_x_ct : forall (pc : Z),
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
arealloc_null_realizes_cf segs B Hpc pc ->
ajournal_x segs B PST ARxs STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 0 -> getr regsT 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (call_trace lyc cf_pc_realloc_ra0 regsT ch) (as_universe B) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs B PST ARxs STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc)) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
(exists q trc, apath (realloc_null_tree_with malloc_cf free_cf n (call_trace lyc cf_pc_realloc_ra0 regsT ch) Sc) trc (q, S2) /\
 YG0d.gflag trc = true /\
 malloc_leaf_cf segs B lyc Sc Hpc W regsT memT mdc n (q, S2) W2 c2 /\
 (q = PNull -> mt_refused malloc_cf free_cf n (call_trace lyc cf_pc_realloc_ra0 regsT ch) Sc S2) /\
 (q = PNull <-> res = 0) /\ (q <> PNull -> res = sptr_addr B ly2 q) /\
 (q <> PNull -> forall i, 0 <= i < 4 -> mem2 (w64 (as_errno B + i)) = memT (w64 (as_errno B + i))) /\
 (forall x : word, ~ aowned B lyc Sc (bv_unsigned x) -> ~ aowned B ly2 S2 (bv_unsigned x) ->
  ~ ascratch B ASTACK regsT (bv_unsigned x) ->
  ~ ((q <> PNull /\ res <= bv_unsigned x < res + req_size n) \/ Exists (in_zr (bv_unsigned x)) (xs_cf lyc Sc ++ xs_cf ly2 S2)) ->
  mem2 x = memT x)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
  rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
 \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
  acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros pc W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
ANULL HJ Ha0 Ha1 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact HQM]. }
destruct (proj1 (acall_pre_x_xs segs B lyc Sc Hpc W regsT memT mdc ch) HPRE) as [HPREcf HXc].
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof (cfr_aj_amx_null B Sc n (call_trace lyc cf_pc_realloc_ra0 regsT ch) HU HWF (QMQ_cf segs B Sc memT HQM)
  ltac:(zlia) Hlive Htr)
as (HSAFE & HPROG & HNSP & HMP).
pose proof (ANULL lyc Sc W regsT memT mdc n ch HPREcf I Ha0 Ha1 Hn Hlive (admits_fix _ _ Sc HU Htr)) as HREAL.
cbv beta in HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 segs _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & [Hleaf Href]).
pose proof (HMP tr r Hpath) as HQ. destruct r as [p S2]. unfold malloc_post_x in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & Hbl).
cbn [fst snd] in Href.
pose proof Hleaf as Hleaf0.
destruct (proj1 (malloc_leaf_cf_xs segs B lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2) Hleaf)
as (ly2 & regs2 & mem2 & md2 & -> & HPOST & Hres & HQT2 & HERR & Herrno & Hrawf).
cbn [fst snd] in Herrno, Hrawf.
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
assert (HJ1 : ajournal_x segs B [] ARxs ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_xw segs B ARxs LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2)) [] (st_nev S2 - st_nev Sc));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a Ha. apply (cfr_aj_xs_write_ok lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b m Hb; left; rewrite Eab2; exact Hb | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[Hf _] | Hx]; [exfalso; exact (Hf eq_refl) | left; exact Hx].
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. exact Hq. }
exists ly2, S2, regs2, mem2, md2, 0.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_sub segs B PST ARxs LAWS segs_low);
[exact HJ | exact (ajournal_x_nil_pst segs B ARxs PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|].
split.
{ exists PNull, tr. split; [exact Hpath|]. split; [exact Hgf|]. split; [exact Hleaf0|]. split; [exact Href|].
split; [split; intros _; reflexivity|].
split; [intros Hc; exfalso; exact (Hc eq_refl)|]. split; [intros Hc; exfalso; exact (Hc eq_refl)|].
intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
intros [[Hc _]|Hx]; [exact (Hc eq_refl) | apply H4; right; exact Hx]. }
left. split; [reflexivity|]. split; [exact Eab2|].
split.
{ rewrite Hsp' in HJ1. eapply (acall_kept_of_journal_x segs B ARxs segs_low);
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
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
pose proof (sep_blocks_pos_x segs B ARxs LAWS ly2 S2 Hpc W2 mem2 md2 (b, m) (res, n) b1 b2 [] HAR2
ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
assert (HJ1 : ajournal_x segs B [] ARxs ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
(st_nev S2 - st_nev Sc)).
{ eapply (acall_post_journal_xw segs B ARxs LAWS segs_low errno_low OWNLOW lyc Sc Hpc W regsT memT mdc ly2 S2 W2 regs2 mem2 md2 _
(fun a => Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly2 S2)) [] (st_nev S2 - st_nev Sc));
[exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | | | exact HQT2].
- intros a Ha. apply (cfr_aj_xs_write_ok lyc Sc Hpc W memT mdc ly2 S2 Hpc W2 mem2 md2 a HAR HAR2 Hly2);
[intros b m Hb; left; rewrite Eab2; apply in_or_app; left; exact Hb | intros f Hf; rewrite Hfrs2; exact Hf | exact Ha].
- intros a [[_ Ha] | Hx]; [right | left; exact Hx].
exists res, n. split; [right; exact Hnew|]. split; [exact Ha|]. right.
intros Hold. exact (Hdisj res n a Hold Ha Ha).
- intros q m i Hq Hnq Hi. exfalso. apply Hnq. rewrite Eab2. apply in_or_app. left. exact Hq. }
exists ly2, S2, regs2, mem2, md2, res.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own).
eapply (ajournal_x_sub segs B PST ARxs LAWS segs_low);
[exact HJ | exact (ajournal_x_nil_pst segs B ARxs PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|].
split; [exact HPRE|].
split.
{ exists p, tr. split; [exact Hpath|]. split; [exact Hgf|]. split; [exact Hleaf0|]. split; [exact Href|].
split; [split; [intros Hc; exfalso; exact (Hnn Hc) | intros Hc; zlia]|].
split; [intros _; reflexivity|]. split; [exact Herrno|].
intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 | exact H4]. }
right. split; [exact Hr4096|]. split; [exact Eab2|].
rewrite Hsp' in HJ1. eapply (acall_kept_of_journal_x segs B ARxs segs_low);
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. apply in_or_app. left. exact Hb.
Qed.
End J.
End CfRAj.

Print Assumptions arealloc_realizes_cf_rp_true.
Print Assumptions amx_realloc_rp_room.
Print Assumptions cfr_aj_null_atok.
Print Assumptions cfr_aj_amx_null.
Print Assumptions cfr_aj_hp_notin.
Print Assumptions cfr_aj_rng_dec.
Print Assumptions cfr_aj_xs_write_ok.
Print Assumptions aj_realloc_at_x_ct.
Print Assumptions aj_realloc_null_at_x_ct.
