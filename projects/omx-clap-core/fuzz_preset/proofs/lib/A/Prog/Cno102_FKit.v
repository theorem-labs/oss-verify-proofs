(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): aj_flag_store_xR is aj_flag_store_x over a journal at
   a world relation R and the step relation SRrG R (YSRrG.SRrG_msteps for the run, YCbqG's R forms for the journal);
   the run keeps the world, so no law of R is read, and the R form takes R reflexive and transitive as every R rule
   does. aj_flag_store_x keeps its statement and is the instance at wle. aj_stack_malloc_at_xR (the call's own journal
   enters the caller's at R by reflexivity and transitivity; the post's own-call journal stays at wle) and
   aj_set_shadow_at_xR are the other two rules over R; their old names are the instances at wle. *)
(* Modified by Theorem Labs, 2026-10: cgif's frame-area call rule aj_stack_malloc_at (proofs/cgif/cgif_file_fuzzer/lib/
   YCbq.v:1749-1809, this tree's copy lib/Reusable/YCbq.v:1749) restated over YCbqG.v's journal ajournal_x (allocator
   invariant a parameter ARx, ghost head set Hp after S / Hpc after Sc, program statics PST), for the frame-area
   contract astack_malloc_realizes_x of the frozen lib/Reusable/FCiface.v (frameclass d9a884240c6e, sha256
   673aac5ee2f6ed86). Generic: no image
   class, no address, no allocator instance.
   Differences from the donor, each minimal:
   (a) cgif read the model's progress and post from model_laws (stack_malloc_progressP, ml_stack_malloc through
       am_wf); here they are ONE hypothesis in ARx form, SMX, which an instance discharges from its own model laws
       (the cf instance: YG05cf.v stack_malloc_progress_cf and stack_malloc_ok_cf with Wf_cf from ARcf);
   (b) the call's own journal is call_effect_journal_x (YGcallx.v:251) at PST = [], lifted by ajournal_x_nil_pst, and
       composed by ajournal_x_sub (YCbqG.v, footprint FP1 = []); Hp is threaded unchanged (FCiface: a frame-area call
       neither poisons nor unpoisons a head);
   (c) the frame's presence (FCiface's post) is also returned, which a caller writing its new frame needs;
   (d) as cgif's aj_stack_malloc_atS (cgif_file_fuzzer lib/YC85.v:292), the post ends with the call's own journal and
       `exists f, S2 = set_fs f Sc` (the call changes st_fs only), so a caller carries a state fact across the call.
   SECOND RULE, aj_flag_store_x: cgif's aj_flag_store (YCbq.v:2362-2439, the inline release under astack_free_law)
   for the LISTING engine over ajournal_x; its ARx-form hypotheses and their cf discharges are stated at the rule
   (ASFX = YG0dcf.v astack_free_law_cf; FFLX = the two conjuncts of cgif's frame_flag_lawP the rule reads, over ARx;
   SFX = YG05cf.v stack_free_ok_cf).
   THIRD RULE, aj_set_shadow_at_x: cgif's frame-area set_shadow call rule (cgif_rgb_fuzzer lib/YC05.v:206) over
   ajournal_x for FCiface's aset_shadow_realizes_x, taken from WalkH6's set-shadow-v2.patch (cold/h-hpreset-7-walk-H6
   321efcb143d) unchanged but for its comment.
   Rule 24: no ajournal_x port of aj_stack_malloc_at or aj_flag_store existed on any branch read (WalkS8a confirmed,
   2026-10-28 ~23:40Z; h-hpreset-7 stopped c-omx-alloc's lane for both); cgif's released YCbq.v is the source ported.
   Numerals: 0, 10 (cgif's class range), 16 (stack alignment), 64 (the smallest frame), 4096 (= ESTACK, YG0d.v),
   2 ^ 40, 2 ^ 64: LENGTH / DERIVED. No ADDRESS. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSx.v, with its module names changed; 735 of its 901 lines of code are new or changed and 195 lines of the source are left out. *)
(* Theorem Labs, 2026-10: fuzz_preset #102, the IMAGE-FREE kit of check_no_overread's Free and End segments (lane
   CnoA102f of a Theorem Labs lane; cited by the cno A' walk lib/A/Prog/Cno102A_F.v and the cno B' walk lib/B/Prog/Cno102B_F.v,
   lane CnoB102f, so the lemmas have ONE home).
   rule 24: no function proved. rule 24: proves no function (kind: segment-kit lemmas: tree port + runner twin).
   FILE SET: every path at the kit cut 7cdbb61b5fa0's blob (lib/A/PRH_Reader.v, the
   engine's YGcallSx.v / YCbqG.v / YC80x.v / YSRrMemnorm.v); first written against walkkit-next 3438f3406f33 and the
   engine s1b 459129c18903, re-fitted at the cut (the journal's 18th conjunct, ajx_qt; the free's admits).
   WHAT:
   1. The PORT of preset's plain tree lemmas (lib/Prog/PjStruct.v) to the kit's reader predicates (lib/A/PRH_Reader.v), the
      premise the kit's tpj_free_specX asks (`pj_fdR .. n v D`, lib/A/PRH_FnPj.v). Transcribed from the donor
      103fdaa2432 lib/B/Prog/CnoB_Free.v (never compiled there), clause by clause against
      PjStruct.v (donor lines in each comment); no plain file is Required and no plain lemma is cited. The zero case is
      lib/Prog/PvMain0.v pv_fd_zeroR (afdd7e86e67b), not repeated here.
   2. pjf_fdR_lblk: pj_fdR over a block predicate that agrees on the tree's own blocks (lane CnoB102f's request: after
      pj_free #1 the ledger list is Lam' with Lam ~ D1 ++ Lam', so trees 2 and 3 move to prh_lin Lam').
   3. aj_flag_store_x_inv: YGcallSx.v's aj_flag_store_x (the inline release of an own fake frame, :248-335) with the
      runner's memory invariant P carried (YSRrMemnorm's form: P of the start memory after the journal premise, P of
      the end memory after the journal in the continuation). Its proof is aj_flag_store_x's with YA0n.SRr_msteps
      replaced by YC80x.SRr_msteps_inv; nothing else moves.
   4. (REMOVED 2026-10-29 ~17:00Z: aset_shadow_realizes_xm / aset_shadow_realizes_xm_forget / aj_set_shadow_at_xm now
      have their one home in the engine, lib/Reusable/YGcallMxmn.v (a Theorem Labs lane), with
      the same statements; the walks cite YGcallMxmn's.)
   5. aj_free_null_at_x (author lane CnoB102f; at the cut it also takes the free's `admits` and the depot keep of a
      free(NULL)): YGcallx.v aj_free_at_x_ct at a0 = 0, the free wrapper on PNull (a NULL padded copy): ablocks unchanged, the leaf at PNull
      (the plain leaf free_leaf_x, which carries no memnorm keep; item 6 is the keep form), acall_kept_x with
      E = False. YGcallx states the rule only for a live block; YCbq.v:1186 aj_free_null_at is the same arm over the
      old ajournal.
   6. aj_free_null_at_cf_rh_keep: aj_free_null_at_cf_rh with the memnorm keep `memnorm memT -> memnorm mem2` as the
      LAST conclusion conjunct, from the cf keep contract YGcfMallocComposeKeep.afree_realizes_cf_rh_keep. It is the
      route of YGcallMxmnKeep.aj_free_at_x_ct_m_rh_keep (the live free): aj_free_null_at_xRA is the NULL rule generic
      in the callee's call post APOST (read only through apost_ar_law / apost_j_law, as YGcallx.aj_free_at_x_ctR),
      taken at APOST := YGcallMxmnKeep.APOST_cf_keep, R := wle' segs RZ_cf. WHY THE KEEP CONTRACT IS NEEDED: the plain
      post does not give the keep. free_leaf_x's raw frame lets mem2 differ from memT on the owned bytes and the
      scratch, and at preset an owned static lies in the read-only segment (lib/Reusable/YF0m.v Tfib_owned_static;
      lib/Prog/RttModel.v img_empty proves that byte read-only), so the post admits an overlay byte there, which
      memnorm forbids (YGcfMallocComposeE.v:33-35, MemnormT.v:29-31).
   Numerals: 56 (LENGTH: a node), 8 (LENGTH: a key pointer); 0 (DERIVED); 16 (LENGTH: stack alignment), 2 ^ 64
   (LENGTH: the word range), 2 ^ 40 (LENGTH: the code-span bound), 4 (LENGTH: an instruction). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0s YG0q YG0t YF0v FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YP0a YP0d YP0c YC80x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs YGcfRehidePost YG0dcfR YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNullCall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep YGcfMallocComposeKeep YGcallMxmnKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==== 1. the PORT: a tree is freeable to any depth at or above its own ==== *)
Section pjf.
Variable segs : list Segment.

(* PjStruct.v:412 pf_items_mono *)
Lemma pjf_pf_itemsR_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a1 D1, P a1 D1 -> Q a1 D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *; [exact Hp|].
destruct Hp as (Dk & D1 & D2 & E & Hk & H1 & H2). exists Dk, D1, D2.
split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 H1)|]. exact (IH (a + 56) (ka + 8) D2 H H2).
Qed.

(* PjStruct.v:436 pj_fshape_mono *)
Lemma pjf_fshapeR_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
intros m lblk Pi Pi' p D H
  (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
exact (H _ _ _ _ _ H6).
Qed.

(* PjStruct.v:447 pj_fd_succ *)
Lemma pjf_fdR_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (S d) p D.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
- eapply (pjf_fshapeR_mono m lblk); [|exact H].
  intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
- eapply (pjf_fshapeR_mono m lblk); [|exact H].
  intros ks kids keys n Di Hi. cbv beta in Hi |- *.
  apply (pjf_pf_itemsR_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi].
  intros a D1 H1. exact (IH a D1 H1).
Qed.

(* PjStruct.v:458 pj_fd_mono *)
Lemma pjf_fdR_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof.
intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|].
apply pjf_fdR_succ. apply IH. exact H.
Qed.

(* PjStruct.v:464 pj_items_pf *)
Lemma pjf_itemsR_pf : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a0 u D1, In u l -> P a0 u D1 -> Q a0 D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *.
- exact Hl.
- destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
  split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
  apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.

(* PjStruct.v:475 pj_mems_pf *)
Lemma pjf_memsR_pf : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a0 u D1, (exists nm, In (nm, u) l) -> P a0 u D1 -> Q a0 D1) ->
  pj_memsR segs m lblk P a ka l D -> pf_itemsR segs m lblk Q true a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR pf_itemsR length] in *.
- exact Hl.
- destruct Hl as (x & k & D1 & D2 & E & Hx & (Hb & _) & HP & HR). exists [(x, k)], D1, D2.
  split; [exact E|].
  split; [unfold pj_keyR; exists x; split; [exact Hx | right; exists k; split; [exact Hb | reflexivity]]|].
  split; [apply (H a u D1); [exists nm; left; reflexivity | exact HP]|].
  apply IH; [intros a' v D3 (nm' & Hv) HP3; apply (H a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.

(* PjStruct.v:488 pj_node_fd: the lemma the kit's pj_free premise needs *)
Lemma pjf_nodeR_fdR : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (depth t) p D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind'; intros m lblk p D H;
  cbn [pj_nodeR] in H.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (tag JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (tag JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (tag JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (tag (JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (tag (JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  remember (depth (JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR.
  split; [exact Hn|]. split; [exact Ha|].
  assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk d') false kids keys (Z.to_nat n) Di).
  { rewrite En, Nat2Z.id. apply (pjf_itemsR_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 Hu HP. rewrite Forall_forall in IH.
    apply (pjf_fdR_mono m lblk (depth u)); [|exact (IH u Hu m lblk a D1 HP)].
    pose proof (depth_item items u Hu) as Hdu. rewrite <- Edd in Hdu. lia. }
  destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
  + subst cap.
    exists (tag (JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ek | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. exact HI.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (tag (JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ek | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  remember (depth (JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR.
  split; [exact Hn|]. split; [exact Ha|].
  destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
  + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia].
    cbn [pj_memsR] in Hi.
    exists (tag (JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
    split; [left; split; [exact Hy0 | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|].
    cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (tag (JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
    split; [subst D; cbn [app]; apply Permutation_refl|].
    cbv beta. rewrite En, Nat2Z.id. apply (pjf_memsR_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (pjf_fdR_mono m lblk (depth u)); [|exact (IH m lblk a D1 HP)].
    pose proof (depth_member members nm u Hu) as Hdu. rewrite <- Edd in Hdu. lia.
Qed.

(* the form a walk cites: a parsed tree no deeper than n is freeable to depth n *)
Lemma pjf_fd_of_node : forall m lblk t n p D, (depth t <= n)%nat -> pj_nodeR segs m lblk p t D ->
  pj_fdR segs m lblk n p D.
Proof.
intros m lblk t n p D Hle H. apply (pjf_fdR_mono m lblk (depth t) n p D Hle). exact (pjf_nodeR_fdR t m lblk p D H).
Qed.

(* ==== 2. the block predicate matters only on the tree's own blocks ==== *)
Lemma pjf_pf_itemsR_lblk : forall m lblk lblk' (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall b k, In (b, k) D -> lblk b k -> lblk' b k) ->
  (forall a1 D1, incl D1 D -> P a1 D1 -> P' a1 D1) ->
  pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk' P' ks a ka n D.
Proof.
intros m lblk lblk' P P' ks n. induction n as [|n IH]; intros a ka D HL HP H; cbn [pf_itemsR] in *; [exact H|].
destruct H as (Dk & D1 & D2 & E & Hk & H1 & H2). exists Dk, D1, D2.
split; [exact E|].
split.
{ unfold pj_keyR in *. destruct ks; [|exact Hk].
  destruct Hk as (x & Hx & [Hz | (k & Hl & EDk)]); exists x; split; [exact Hx | left; exact Hz | exact Hx|].
  right. exists k. split; [|exact EDk]. apply HL; [|exact Hl]. rewrite E, EDk. left. reflexivity. }
split.
{ apply HP; [|exact H1]. intros y Hy. rewrite E. apply in_or_app. right. apply in_or_app. left. exact Hy. }
apply (IH (a + 56) (ka + 8) D2).
- intros b k Hin. apply HL. rewrite E. apply in_or_app. right. apply in_or_app. right. exact Hin.
- intros a1 D3 Hinc HP3. apply HP; [|exact HP3].
  intros y Hy. rewrite E. apply in_or_app. right. apply in_or_app. right. exact (Hinc y Hy).
- exact H2.
Qed.

Lemma pjf_fdR_lblk : forall m lblk lblk' d p D,
  (forall b k, In (b, k) D -> lblk b k -> lblk' b k) ->
  pj_fdR segs m lblk d p D -> pj_fdR segs m lblk' d p D.
Proof.
intros m lblk lblk' d. induction d as [|d IH]; intros p D HL H; cbn [pj_fdR] in H |- *;
  destruct H as (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6);
  (assert (Hsub : forall x, In x (Ds ++ Dk ++ Dy ++ Di) -> In x D)
     by (intros x Hx; exact (Permutation_in _ (Permutation_sym H5) Hx)));
  (split; [exact Hn|]); (split; [exact Ha|]); exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
  (split; [exact H1|]);
  (split; [destruct H2 as [H2 | (k & Hl & EDs)]; [left; exact H2 | right; exists k; split; [|exact EDs];
     apply HL; [apply Hsub; rewrite EDs; left; reflexivity | exact Hl]]|]);
  (split; [destruct H3 as [H3 | (k & Hl & Hk & EDk)]; [left; exact H3 | right; exists k; split; [|split; [exact Hk | exact EDk]];
     apply HL; [apply Hsub; rewrite EDk; apply in_or_app; right; apply in_or_app; left; left; reflexivity | exact Hl]]|]);
  (split; [destruct H4 as [H4 | (Eks & k & Hl & Hk & EDy)]; [left; exact H4 | right; split; [exact Eks|]; exists k;
     split; [|split; [exact Hk | exact EDy]]; apply HL;
     [apply Hsub; rewrite EDy; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity
     | exact Hl]]|]);
  (split; [exact H5|]).
- exact H6.
- cbv beta in H6 |- *. apply (pjf_pf_itemsR_lblk m lblk lblk' (pj_fdR segs m lblk d)); [| |exact H6].
  + intros b k Hin. apply HL. apply Hsub. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    exact Hin.
  + intros a1 D1 Hinc HP. apply (IH a1 D1); [|exact HP]. intros b k Hin. apply HL. apply Hsub.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact (Hinc _ Hin).
Qed.

(* the same for a parsed tree (pj_nodeR): after an earlier pj_free the ledger list is Lam' with Lam ~ D1 ++ Lam', and
   a tree still to be freed holds only blocks of Lam' *)
Lemma pjf_cstrR_lblk : forall m lblk lblk' a k s, pj_cstrR segs m lblk a k s -> (lblk a k -> lblk' a k) ->
  pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (Hl & Hr) H. exact (conj (H Hl) Hr). Qed.

Lemma pjf_itemsR_lblk : forall (P P' : Z -> jv -> list (Z * Z) -> Prop) l a D,
  (forall a0 u D1, In u l -> incl D1 D -> P a0 u D1 -> P' a0 u D1) ->
  pj_itemsR P a l D -> pj_itemsR P' a l D.
Proof.
intros P P' l. induction l as [|u r IH]; intros a D H Hl; cbn [pj_itemsR] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & H1 & H2). exists D1, D2. split; [exact E|].
split; [apply (H a u D1); [left; reflexivity | rewrite E; apply incl_appl, incl_refl | exact H1]|].
apply (IH (a + 56) D2); [|exact H2].
intros a0 v D3 Hv Hinc HP. apply (H a0 v D3); [right; exact Hv | rewrite E; apply incl_appr; exact Hinc | exact HP].
Qed.

Lemma pjf_memsR_lblk : forall m lblk lblk' (P P' : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  (forall b k, In (b, k) D -> lblk b k -> lblk' b k) ->
  (forall a0 u D1, (exists nm, In (nm, u) l) -> incl D1 D -> P a0 u D1 -> P' a0 u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D HL H Hl; cbn [pj_memsR] in *; [exact Hl|].
destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & H1 & H2). exists x, k, D1, D2.
split; [exact E|]. split; [exact Hx|].
split; [apply (pjf_cstrR_lblk m lblk lblk'); [exact Hc | apply HL; rewrite E; left; reflexivity]|].
split; [apply (H a u D1); [exists nm; left; reflexivity | rewrite E; intros y Hy; right; apply in_or_app; left; exact Hy
  | exact H1]|].
apply (IH (a + 56) (ka + 8) D2); [| |exact H2].
- intros b k' Hin. apply HL. rewrite E. right. apply in_or_app. right. exact Hin.
- intros a0 v D3 (nm' & Hv) Hinc HP. apply (H a0 v D3); [exists nm'; right; exact Hv | | exact HP].
  rewrite E. intros y Hy. right. apply in_or_app. right. exact (Hinc y Hy).
Qed.

Lemma pjf_nodeR_lblk : forall t m lblk lblk' p D,
  (forall b k, In (b, k) D -> lblk b k -> lblk' b k) ->
  pj_nodeR segs m lblk p t D -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind'; intros m lblk lblk' p D HL H;
  cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (pjf_cstrR_lblk m lblk lblk'); [exact Hc|]. apply HL. rewrite ED. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (pjf_cstrR_lblk m lblk lblk'); [exact Hc|]. apply HL. rewrite ED. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hz | (Hp & Hl)]; [left; exact Hz | right; split; [exact Hp|]].
    apply HL; [|exact Hl]. rewrite ED, (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pjf_itemsR_lblk (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di); [|exact Hi].
  intros a0 u D1 Hu Hinc HP. rewrite Forall_forall in IH. apply (IH u Hu m lblk lblk' a0 D1); [|exact HP].
  intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact (Hinc _ Hin).
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hz | (Hp & L0 & L1)]; [left; exact Hz | right; split; [exact Hp|]].
    rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    split; apply HL; [rewrite ED; left; reflexivity | exact L0 | rewrite ED; right; left; reflexivity | exact L1]. }
  exists Di. split; [exact ED|].
  apply (pjf_memsR_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di); [| |exact Hi].
  + intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact Hin.
  + intros a0 u D1 (nm & Hu) Hinc HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (IH m lblk lblk' a0 D1); [|exact HP].
    intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact (Hinc _ Hin).
Qed.
End pjf.

(* ==== 3. the inline release carrying the runner's invariant P: YGcallSx.v:248 aj_flag_store_x, with
   SRr_msteps -> SRr_msteps_inv (YC80x.v:83). Section hypotheses: YGcallSx.v Section x's that aj_flag_store_x
   reads (LAWS, segs_low, ASFX, FFLX, SFX; verbatim) and Section e's listing hypotheses (verbatim), then P, PLAW. ==== *)
Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Notation AJ := (ajournal_x segs B PST ARx).
Local Notation AJR := (ajournal_xR segs B PST ARx).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview segs (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world segs) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img segs (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Section e.
Variable psym : Type.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Variable tw0 : ctable.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Hypothesis Htw : tw_of 0 listing = tw0.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).

(* the same over a world relation R (the journal at ajournal_xR R, the run at SRrG segs R): what a walk that has
   crossed a free needs. aj_flag_store_x_inv is its instance at R := wle. *)
Lemma aj_flag_store_x_invR : forall (R : world segs -> world segs -> Prop) W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q,
(A_LIM <= K)%nat -> img_env E -> 0 <= cid ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
AJR R STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
(forall ws msr, length ws = sh_j st' -> st_ok_pi (extK E K ws) (sh_ss st') msr ->
  mbyte segs (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
(forall ws ms' mat',
  length ws = sh_j st' -> img_env (extK E K ws) ->
  st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
  sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
  AJR R STK sp0 FP ly S Hp W0 mem md own' lyc (stack_free_state cid pos Sc) Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  P (ms_mem ms') ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRrG segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q
HK HE Hcid HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hflag0 Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
  HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
assert (HS' : st_ok_pi (extK E K ws) (sh_ss st') msr') by (destruct r; cbn [ptok_post] in HP; first [exact HP | destruct Hr | destruct HP]).
clear HP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFLX lyc Sc Hpc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfo & Hfr_rng).
apply (SRr_msteps_invR segs Hwx P PLAW R W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x).
{ subst memc'. rewrite Hmm. exact Hfr. }
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc')) by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a -> aview segs (w_H W) memc' a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
pose proof (same_but_materialized_wvb mdc _ Hsame') as Emd.
destruct (SFX lyc Sc Hpc W (ms_mem ms) mdc cid pos HAR Hin) as (l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
  rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
  pose proof (sep_frames_pos_x segs B ARx LAWS lyc Sc Hpc W (ms_mem ms) mdc (cid, pos) (cid, pos) [] l1' l2 HAR
    ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). zlia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
assert (HAR' : ARx lyc (stack_free_state cid pos Sc) Hpc W memc' (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ eapply (ASFX lyc Sc Hpc W (ms_mem ms) mdc memc' _ cid pos HAR Hin).
  - unfold aview. subst memc'. rewrite Hmm. rewrite (Hflag0 ws msr' Hlen HS'). reflexivity.
  - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
    destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
    exact (proj1 (awr_byte_cases_xR segs B PST ARx LAWS R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a _ Hh. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- subst memc'. rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_after_writeR segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W
    (ms_mem ms) mdc k memc' _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc) Hpc own' HJ Heqw
    ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
  + intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  + exact HAR'.
  + unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  + reflexivity.
  + cbn. zlia.
  + etransitivity; [exact E2 | symmetry; exact E1].
  + pose proof (ajxR_qt HJ) as HQT.
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
  + reflexivity.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.

Lemma aj_flag_store_x_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q,
(A_LIM <= K)%nat -> img_env E -> 0 <= cid ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
AJ STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
(forall ws msr, length ws = sh_j st' -> st_ok_pi (extK E K ws) (sh_ss st') msr ->
  mbyte segs (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
(forall ws ms' mat',
  length ws = sh_j st' -> img_env (extK E K ws) ->
  st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
  sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
  AJ STK sp0 FP ly S Hp W0 mem md own' lyc (stack_free_state cid pos Sc) Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  P (ms_mem ms') ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (aj_flag_store_x_invR (@wle segs)). Qed.
End e.

End x.

(* the twin at a PAImg instance, as YC1fPx.v instantiates paj_run_x_inv and S10TxString.v ts_flag_store
   instantiates aj_flag_store_x *)
Section gi. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview pa_segs (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview pa_segs (w_H W) mem' a = aview pa_segs (w_H W) mem a) ->
  (forall a, aview pa_segs (w_H W) mem a <> None -> aview pa_segs (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world pa_segs) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img pa_segs (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws pa_segs P.
Definition paj_flag_store_x_inv :=
  aj_flag_store_x_inv (SK := SK) pa_segs B PST ARx LAWS pa_segs_low ASFX FFLX SFX
    asym pa_wx (clookup pa_tbl) pa_val pa_sigma L pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text
    pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_flag_store_x_invR :=
  aj_flag_store_x_invR (SK := SK) pa_segs B PST ARx LAWS pa_segs_low ASFX FFLX SFX
    asym pa_wx (clookup pa_tbl) pa_val pa_sigma L pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text
    pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
End gi.

(* ---- section 5, pasted by path from lane CnoB102f's worker file aj_free_null_at_x.v (sha256 87fab44c84cd1179;
   author CnoB102f, a Theorem Labs lane), re-fitted at the kit cut: the free's `admits` and the free(NULL) depot keep ---- *)
(* ==== 1. THE free(NULL) CALL RULE over ajournal_x (engine-generic; for lib/A/Prog/Cno102_FKit.v, one home) ====
   YGcallx.v aj_free_at_x_ct for a0 = 0: the free wrapper on PNull, which YGcallx states only
   for a live block (In (pa, n) (ablocks ..)). The proof is aj_free_at_x_ct's with the PNull arm of free_post_x
   (YCbq.v:1186 aj_free_null_at is the same arm over the old ajournal). The block list is unchanged, the call writes
   no client byte (E = False). Its conclusion is aj_free_at_x_ct's at pa := 0, n := 0 with the split ablocks clause
   replaced by equality. *)
Section fnull. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable QM : astate -> Prop.
(* the call's trailing conjuncts on the state AND the call memory (the engine's QMm, YGcallx.v Section gx): what
   acall_pre_x asks; QMQ gives the model laws' state predicate from it, as YGcallx's Section r takes it *)
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
Variable WFx : astate -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis AMX : alloc_model_laws_x B QM mt nmax ft WFx.
Hypothesis QMQ : forall S mem, QMm S mem -> QM S.
Local Abbreviation code := (as_code B).

(* THE PNull-ONLY FREE TEXT (the engine-generic form of the released free(NULL) contract): the free wrapper on a
   NULL pointer realizes free_leaf_x. The whole free text gives it at p := PNull (afree_null_realizes_x_of_x); a cf
   instance gives it from the PRIMED free row, which is the only route there. *)
Definition afree_null_realizes_x : Prop :=
  forall ly S Hp W regs mem md n ch,
  acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch ->
  getr regs 10 = w64 (sptr_addr B ly PNull) -> ~ In (sptr_addr B ly PNull) Hp ->
  admits (as_universe B) (call_trace ly (pc_free_ra0 code) regs ch) S ->
  amreal segs (ft PNull (call_trace ly (pc_free_ra0 code) regs ch) S) W
    (cfg_at segs (pc_wrap_free code) regs mem md)
    (free_leaf_x segs B ARx ly S Hp W regs mem md PNull n).

Lemma afree_null_realizes_x_of_x : afree_realizes_x segs B ARx QMm ft -> afree_null_realizes_x.
Proof.
intros AF ly S Hp W regs mem md n ch Hpre Ha0 Hnhp Htr.
exact (AF ly S Hp W regs mem md PNull n ch Hpre (or_introl eq_refl) Ha0 Hnhp Htr).
Qed.

(* THE RULE OVER A WORLD RELATION R: the cuts after a live free reach the NULL free inside a journal at R, not at
   wle. R is any transitive relation containing wle; the realization is lifted by amreal_amrealG and run out by
   amrealG_SRrG04, the call's own journal (at wle, from the unprimed leaf) by ajournal_xwR_mono. The leaf and
   acall_kept_x stay unprimed. aj_free_null_at_x below is the instance at R := wle. *)
Lemma aj_free_null_at_xR : forall (R : world segs -> world segs -> Prop),
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
  afree_null_realizes_x ->
  forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch,
  ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  getr regsT 10 = w64 0 -> ~ In 0 Hpc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  QMm Sc memT ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
  (* free(NULL) keeps the depot (at the cf instance: YGcfAmx2.ipost_free_null_depot), so the call adds no wild trace *)
  (forall trc S2, apath (ft PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) ->
     st_depot S2 = st_depot Sc) ->
  SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
      (k + (st_nev S2 - st_nev Sc)) /\
    aregs_preserved regsT regs2 /\
    ablocks B ly2 S2 = ablocks B lyc Sc /\
    frames S2 = frames Sc /\
    acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
    (exists trc, apath (ft PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
       free_leaf_x segs B ARx lyc Sc Hpc W regsT memT mdc PNull 0 (tt, S2) W2 c2) /\
    acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False)).
Proof.
intros R R_trans R_wle AFREE W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch
  HJ Ha0 Hnhp Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HDEP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
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
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof (@amx_free B QM mt nmax ft WFx AMX Sc PNull 0 (call_trace lyc (pc_free_ra0 code) regsT ch) HWF (QMQ Sc memT HQM)
  (or_introl eq_refl) Htr) as (HSAFE & HPROG & HNSP & HMP).
pose proof (AFREE lyc Sc Hpc W regsT memT mdc 0 ch HPRE ltac:(cbn; exact Ha0) ltac:(cbn; exact Hnhp) Htr) as HREAL.
eapply (SRrG_mono segs R).
{ exact (amrealG_SRrG04 segs R R_trans _ W _ _ (amreal_amrealG segs R R_wle _ W _ _ HREAL)
    HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (HMP tr r Hpath) as HQ. destruct r as [[] S2]. unfold free_post_x in HQ. cbn [fst snd] in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2)).
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2 & _).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (alx_layout segs B ARx LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Ebl : blocks S2 = blocks Sc).
{ destruct Hsplit as [[_ E12] | E12]; [rewrite Hbl2, E12; reflexivity|].
  exfalso.
  assert (Hin : In (fc (PNull, 0)) (ablocks B lyc Sc)).
  { unfold ablocks. change (In (fc (PNull, 0)) (map fc (blocks Sc))). apply in_map. rewrite E12.
    apply in_or_app. right. left. reflexivity. }
  destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc W memT mdc _ _ HAR Hin) as (_ & H4096 & _).
  subst fc. cbn in H4096. zlia. }
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Ebl. apply map_ext_in. exact Efc. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  inFP [] (p + i)).
{ intros p m i Hp0 Hnp Hi. exfalso. apply Hnp. rewrite Eab2. exact Hp0. }
assert (HJ1 : ajournal_xw (SK := SK) segs B [] ARx ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2 mem2 md2
  (st_nev S2 - st_nev Sc) []).
{ eapply (acall_post_journal_x (SK := SK) segs B ARx LAWS segs_low errno_low OWNLOW);
    [exact HPOST | exact HAR | exact HstkC | exact Hfrs2 | zlia | zlia | exact Hsecs2 | | exact HgoneC | exact HQT2 |].
  - intros a [Hnn _]. exfalso. exact (Hnn eq_refl).
  - rewrite (HDEP tr S2 Hpath), app_nil_r. apply incl_refl. }
assert (HJ1R : ajournal_xwR (SK := SK) segs B [] ARx R ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2
  mem2 md2 (st_nev S2 - st_nev Sc) []).
{ eapply (ajournal_xwR_mono (SK := SK) segs B [] ARx (@wle segs) R R_wle). exact HJ1. }
exists ly2, S2, regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1R. change own with ([] ++ own).
  eapply (ajournal_x_subR (SK := SK) segs B PST ARx LAWS segs_low R R_trans);
    [exact HJ | apply (ajournal_xwR_nil_pst (SK := SK) segs B ARx R PST); exact HJ1R | zlia | zlia |].
  intros a (rg & [] & _). }
split; [exact HP|].
split; [exact Eab2|].
split; [exact Hfrs2|].
split; [exact HPRE|].
split; [exists tr; split; [exact Hpath|]; split; [exact Hgf | exact Hleaf0]|].
rewrite Hsp' in HJ1R.
eapply (acall_kept_of_journal_xR (SK := SK) segs B ARx segs_low R); [exact HJ1R | exact HAR | | | exact sink_closed_nil].
- intros a (rg & [] & _).
- intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
Lemma aj_free_null_at_x : afree_realizes_x segs B ARx QMm ft ->
  forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch,
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  getr regsT 10 = w64 0 -> ~ In 0 Hpc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  QMm Sc memT ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
  (* free(NULL) keeps the depot (at the cf instance: YGcfAmx2.ipost_free_null_depot), so the call adds no wild trace *)
  (forall trc S2, apath (ft PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) ->
     st_depot S2 = st_depot Sc) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
      (k + (st_nev S2 - st_nev Sc)) /\
    aregs_preserved regsT regs2 /\
    ablocks B ly2 S2 = ablocks B lyc Sc /\
    frames S2 = frames Sc /\
    acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
    (exists trc, apath (ft PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
       free_leaf_x segs B ARx lyc Sc Hpc W regsT memT mdc PNull 0 (tt, S2) W2 c2) /\
    acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False)).
Proof.
intros AFREE.
exact (aj_free_null_at_xR (@wle segs) (wle_trans segs) (fun _ _ H => H)
  (afree_null_realizes_x_of_x AFREE)).
Qed.

(* THE RULE OVER R AND THE CALLEE'S CALL POST APOST (YGcallx Section rR, YGcallMxmn Section allocmR): the PNull text
   realizes through amrealG R at the leaf free_leaf_xA APOST, and the rule reads the post only through POST_AR and
   POST_J. The proof is aj_free_null_at_xR's with the call's own journal from POST_J (in place of
   acall_post_journal_x at wle and ajournal_xwR_mono) and the post's invariant, layout step and saved registers from
   POST_AR. aj_free_null_at_cf_rh_keep below is its instance at the keep post. *)
Section fnullA.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Variable APOST : Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Hypothesis POST_AR : apost_ar_law segs ARx APOST.
Hypothesis POST_J : apost_j_law (SK := SK) segs B ARx R APOST.

(* afree_null_realizes_x over R and APOST: YGcallx.afree_realizes_xR at p := PNull *)
Definition afree_null_realizes_xRA : Prop :=
  forall ly S Hp W regs mem md n ch,
  acall_pre_x segs B ARx QMm ly S Hp W regs mem md ch ->
  getr regs 10 = w64 (sptr_addr B ly PNull) -> ~ In (sptr_addr B ly PNull) Hp ->
  admits (as_universe B) (call_trace ly (pc_free_ra0 code) regs ch) S ->
  amrealG segs R (ft PNull (call_trace ly (pc_free_ra0 code) regs ch) S) W
    (cfg_at segs (pc_wrap_free code) regs mem md)
    (free_leaf_xA segs B APOST ly S Hp W regs mem md PNull n).

Lemma afree_null_realizes_xRA_of_xR : afree_realizes_xR segs B ARx QMm ft R APOST -> afree_null_realizes_xRA.
Proof.
intros AF ly S Hp W regs mem md n ch Hpre Ha0 Hnhp Htr.
exact (AF ly S Hp W regs mem md PNull n ch Hpre (or_introl eq_refl) Ha0 Hnhp Htr).
Qed.

Lemma aj_free_null_at_xRA : afree_null_realizes_xRA ->
  forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch,
  ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  getr regsT 10 = w64 0 -> ~ In 0 Hpc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  QMm Sc memT ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
  (forall trc S2, apath (ft PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) ->
     st_depot S2 = st_depot Sc) ->
  SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
      (k + (st_nev S2 - st_nev Sc)) /\
    aregs_preserved regsT regs2 /\
    ablocks B ly2 S2 = ablocks B lyc Sc /\
    frames S2 = frames Sc /\
    acall_pre_x segs B ARx QMm lyc Sc Hpc W regsT memT mdc ch /\
    (exists trc, apath (ft PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
       free_leaf_xA segs B APOST lyc Sc Hpc W regsT memT mdc PNull 0 (tt, S2) W2 c2) /\
    acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False)).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch
  HJ Ha0 Hnhp Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HDEP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
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
pose proof (WFL lyc Sc Hpc W memT mdc HAR) as HWF.
pose proof (@amx_free B QM mt nmax ft WFx AMX Sc PNull 0 (call_trace lyc (pc_free_ra0 code) regsT ch) HWF (QMQ Sc memT HQM)
  (or_introl eq_refl) Htr) as (HSAFE & HPROG & HNSP & HMP).
pose proof (AFREE lyc Sc Hpc W regsT memT mdc 0 ch HPRE ltac:(cbn; exact Ha0) ltac:(cbn; exact Hnhp) Htr) as HREAL.
eapply (SRrG_mono segs R).
{ exact (amrealG_SRrG04 segs R R_trans _ W _ _ HREAL HSAFE HPROG HNSP). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (HMP tr r Hpath) as HQ. destruct r as [[] S2]. unfold free_post_x in HQ. cbn [fst snd] in HQ.
destruct HQ as (Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2)).
pose proof Hleaf as Hleaf0.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOST & HQT2 & _).
destruct (POST_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) as (HAR2 & Hly2 & HP).
destruct (alx_layout segs B ARx LAWS _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Ebl : blocks S2 = blocks Sc).
{ destruct Hsplit as [[_ E12] | E12]; [rewrite Hbl2, E12; reflexivity|].
  exfalso.
  assert (Hin : In (fc (PNull, 0)) (ablocks B lyc Sc)).
  { unfold ablocks. change (In (fc (PNull, 0)) (map fc (blocks Sc))). apply in_map. rewrite E12.
    apply in_or_app. right. left. reflexivity. }
  destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc W memT mdc _ _ HAR Hin) as (_ & H4096 & _).
  subst fc. cbn in H4096. zlia. }
assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
{ unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Ebl. apply map_ext_in. exact Efc. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  inFP [] (p + i)).
{ intros p m i Hp0 Hnp Hi. exfalso. apply Hnp. rewrite Eab2. exact Hp0. }
assert (HJ1R : ajournal_xwR (SK := SK) segs B [] ARx R ASTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [] ly2 S2 Hpc W2
  mem2 md2 (st_nev S2 - st_nev Sc) []).
{ refine (POST_J lyc Sc Hpc W regsT memT mdc ly2 S2 Hpc W2 regs2 mem2 md2 _ (fun _ => False) [] (st_nev S2 - st_nev Sc) []
    HPOST HAR HstkC Hfrs2 ltac:(zlia) ltac:(zlia) Hsecs2 (fun a Hx => False_ind _ Hx) _ HgoneC HQT2 _).
  - intros a [Hnn _]. exfalso. exact (Hnn eq_refl).
  - rewrite (HDEP tr S2 Hpath), app_nil_r. apply incl_refl. }
exists ly2, S2, regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1R. change own with ([] ++ own).
  eapply (ajournal_x_subR (SK := SK) segs B PST ARx LAWS segs_low R R_trans);
    [exact HJ | apply (ajournal_xwR_nil_pst (SK := SK) segs B ARx R PST); exact HJ1R | zlia | zlia |].
  intros a (rg & [] & _). }
split; [exact HP|].
split; [exact Eab2|].
split; [exact Hfrs2|].
split; [exact HPRE|].
split; [exists tr; split; [exact Hpath|]; split; [exact Hgf | exact Hleaf0]|].
rewrite Hsp' in HJ1R.
eapply (acall_kept_of_journal_xR (SK := SK) segs B ARx segs_low R); [exact HJ1R | exact HAR | | | exact sink_closed_nil].
- intros a (rg & [] & _).
- intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End fnullA.
End fnull.

(* ---- THE cf INSTANCE of the rule, at the world relation the free move runs in (wle' segs RZ_cf): the PNull text
   comes from the PRIMED free row by one citation, afree_null_realizes_cf_of_rh segs B Hrh (basis: no live slot
   dies, dead set empty (free(NULL) keeps st_secs: secs_free_null_step, dead_shadow_new_same_secs_empty; inside
   afree_null_realizes_cf_of_rh)), and the bridge below carries it to the generic text at ARxs, as YGcallcf's
   afree_realizes_x_xs carries the whole free text. ---- *)
Section fnullcf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).
Local Abbreviation code := (as_code B).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARxs HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARxs.
Hypothesis WFL : ARx_wf_law segs ARxs (Wf_cf (as_universe B)).
Hypothesis AMX : alloc_model_laws_x B QM_cf malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)).

(* the released PNull text at the generic parameters (YGcallcf.afree_realizes_x_xs for the PNull row; the cf leaf's
   own xs_placed_cf comes from xs_placed_cf at the call and free_cf's state frame) *)
Lemma afree_null_realizes_x_xs : afree_null_realizes_cf segs B ->
  afree_null_realizes_x segs B ARxs (QMm_cf segs B) free_cf.
Proof.
intros AF ly S Hp W regs mem md n ch Hpre Ha0 Hnhp Htr.
destruct (proj1 (YGcallcf.acall_pre_x_xs segs B ly S Hp W regs mem md ch) Hpre) as [Hpc HX].
pose proof (YGcallcf.amreal_ipost segs _ _ _ _ _
  (cfx_fr_free_cf PNull (call_trace ly (pc_free_ra0 code) regs ch) S)
  (AF ly S Hp W regs mem md n ch Hpc Ha0 Hnhp Htr)) as HR.
exact (amreal_mono segs _ _ _ _ _ (fun r W' c' Hl =>
  YGcallcf.free_leaf_cf_xs segs B ly S Hp W regs mem md ch PNull n r W' c' Hpc HX
    (free_frame_cf_of_state S (snd r) (proj1 (proj2 Hl)) (proj2 (proj2 Hl))) (proj1 (proj1 Hl))) HR).
Qed.

Lemma aj_free_null_at_cf_rh : afree_realizes_cf_rh segs B ->
  forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch,
  ajournal_xR (SK := SK) segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  getr regsT 10 = w64 0 -> ~ In 0 Hpc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  QMm_cf segs B Sc memT ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
  (* free(NULL) keeps the depot (at the cf instance: YGcfAmx2.ipost_free_null_depot), so the call adds no wild trace *)
  (forall trc S2, apath (free_cf PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) ->
     st_depot S2 = st_depot Sc) ->
  SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_xR (SK := SK) segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
      (k + (st_nev S2 - st_nev Sc)) /\
    aregs_preserved regsT regs2 /\
    ablocks B ly2 S2 = ablocks B lyc Sc /\
    frames S2 = frames Sc /\
    acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
    (exists trc, apath (free_cf PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
       free_leaf_x segs B ARxs lyc Sc Hpc W regsT memT mdc PNull 0 (tt, S2) W2 c2) /\
    acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False)).
Proof.
intros Hrh.
exact (aj_free_null_at_xR (fx := fx) (rc := rc) (SK := SK) segs B PST ARxs QM_cf (QMm_cf segs B) malloc_cf
  cf_malloc_max free_cf (Wf_cf (as_universe B)) LAWS segs_low errno_low OWNLOW WFL AMX (QMQ_cf segs B)
  (wle' segs RZ_cf) (wle'_trans segs RZ_cf) (wle_wle' segs RZ_cf)
  (afree_null_realizes_x_xs (afree_null_realizes_cf_of_rh segs B Hrh))).
Qed.

(* THE KEEP FORM: aj_free_null_at_cf_rh with `memnorm memT -> memnorm mem2` as its LAST conclusion conjunct, from the
   cf keep contract. As YGcallMxmnKeep.aj_free_at_x_ct_m_rh_keep for a live block: the generic rule aj_free_null_at_xRA
   at R := wle' segs RZ_cf and APOST := YGcallMxmnKeep.APOST_cf_keep (laws POST_AR_cf_keep / POST_J_cf_keep), its PNull
   text from the keep contract's generic text (YGcallMxmnKeep.afree_realizes_x_cf_rh_keep at p := PNull); the keep is
   read off the leaf at the leaf's end memory. The leaf is given at the plain post (free_leaf_x at ARxs), the leaf of
   aj_free_null_at_cf_rh: free(NULL) keeps st_secs on its path (YGcfSecsStep.secs_free_null_step), so the primed
   post's dead set is empty (dead_shadow_new_same_secs_empty); its world step wle_in at that set is wle and the extra
   antecedent of its view frame holds (the argument of YGcfNullCall.afree_null_realizes_cf_of_rh). *)
Lemma aj_free_null_at_cf_rh_keep : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep segs B ->
  forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch,
  ajournal_xR (SK := SK) segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
  getr regsT 10 = w64 0 -> ~ In 0 Hpc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  QMm_cf segs B Sc memT ->
  chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
  admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
  (* free(NULL) keeps the depot (at the cf instance: YGcfAmx2.ipost_free_null_depot), so the call adds no wild trace *)
  (forall trc S2, apath (free_cf PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) ->
     st_depot S2 = st_depot Sc) ->
  SRrG segs (wle' segs RZ_cf) W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_xR (SK := SK) segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
      (k + (st_nev S2 - st_nev Sc)) /\
    aregs_preserved regsT regs2 /\
    ablocks B ly2 S2 = ablocks B lyc Sc /\
    frames S2 = frames Sc /\
    acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
    (exists trc, apath (free_cf PNull (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
       free_leaf_x segs B ARxs lyc Sc Hpc W regsT memT mdc PNull 0 (tt, S2) W2 c2) /\
    acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
    (YAkMemnorm.memnorm segs memT -> YAkMemnorm.memnorm segs mem2)).
Proof.
intros AF W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch
  HJ Ha0 Hnhp Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HDEP.
eapply (SRrG_mono segs (wle' segs RZ_cf)).
{ exact (aj_free_null_at_xRA (fx := fx) (rc := rc) (SK := SK) segs B PST ARxs QM_cf (QMm_cf segs B) malloc_cf
    cf_malloc_max free_cf (Wf_cf (as_universe B)) LAWS segs_low WFL AMX (QMQ_cf segs B)
    (wle' segs RZ_cf) (wle'_trans segs RZ_cf) (YGcallMxmnKeep.APOST_cf_keep segs B)
    (YGcallMxmnKeep.POST_AR_cf_keep segs B)
    (YGcallMxmnKeep.POST_J_cf_keep (SK := SK) segs B LAWS segs_low errno_low OWNLOW)
    (afree_null_realizes_xRA_of_xR segs B ARxs (QMm_cf segs B) free_cf (wle' segs RZ_cf)
      (YGcallMxmnKeep.APOST_cf_keep segs B) (YGcallMxmnKeep.afree_realizes_x_cf_rh_keep segs B AF))
    W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch
    HJ Ha0 Hnhp Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HDEP). }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HP2 & HB2 & HF2 & HPRE2 & (trc & Hpath & Hgf & Hleaf) & HK2).
destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & ((HA' & HX') & HMN') & HQ').
assert (Em : mem' = mem2)
  by exact (f_equal (fun c => ms_mem (cfg_ms c)) (eq_trans (eq_sym Hc') Hc)).
pose proof (YGcfSecsStep.secs_free_null_step _ Sc trc S2 Hpath) as SS.
assert (DN : forall a, ~ dead_shadow_new lyc Sc S2 a)
  by (intros a; exact (dead_shadow_new_same_secs_empty lyc Sc S2 a SS)).
exists ly2, S2, regs2, mem2, md2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HB2|]. split; [exact HF2|].
split; [exact HPRE2|].
split.
{ exists trc. split; [exact Hpath|]. split; [exact Hgf|].
  exists ly', regs', mem', md'. split; [exact Hc'|]. split; [|exact HQ'].
  rewrite acall_post_cf_rh_unfold in HA'. destruct HA' as (AR & LL & WI & AP & IO & VW & ST).
  refine (conj (conj AR HX') (conj LL (conj _ (conj AP (conj IO (conj _ ST)))))).
  - hnf. intros a Ha. destruct (WI a Ha) as [H1 | H2]; [exact H1 | destruct (DN _ H2)].
  - intros a Ha N1 N2 N3 N4. exact (VW a Ha N1 N2 N3 N4 (DN a)). }
split; [exact HK2|].
rewrite <- Em. exact HMN'.
Qed.
End fnullcf.


Check aj_free_null_at_x.
Check aj_free_null_at_xR.
Check afree_null_realizes_x_of_x.
Check aj_flag_store_x_invR.
Check paj_flag_store_x_invR.
Check aj_free_null_at_cf_rh.
Check afree_null_realizes_x_xs.
Check pjf_nodeR_fdR.
Check pjf_fd_of_node.
Check pjf_fdR_lblk.
Check aj_flag_store_x_inv.
Check paj_flag_store_x_inv.
Check afree_null_realizes_xRA_of_xR.
Check aj_free_null_at_xRA.
Check aj_free_null_at_cf_rh_keep.
Print Assumptions aj_free_null_at_cf_rh_keep.
