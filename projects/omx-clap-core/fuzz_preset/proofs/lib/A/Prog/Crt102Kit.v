(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1682 of its 1758 lines of code are new or changed and 438 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): every journal of this kit is the
   engine's R form at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (ajournal_xwR / ajournal_xR, the notations AJW / AJ)
   and every step statement is YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (the glue's crt_live_journal and QF are there).
   PART 1b's runners run YC1fPx's R runners (paj_run_xR / paj_run_to_xR / paj_run_x_invR / paj_run_to_x_invR at R with
   wle'_refl / wle'_trans) over YCbqGwild.ajournal_xw_rebaseR / unbase0R; the call rules run YCbqGwild.aj_call_xbFR
   at R under YSRrG.SRr'_bind / SRr'_mono and take the callee's text at R (apost_base_xFR / apost_base_xbFR at wle',
   i.e. PRH_Base's fpostF / fpostFb); crt102rw_lift_xF / crt102rw_lift_x lift a plain (wle) callee text to that form.
   Names and binder lists unchanged. Contract note: the internal file WLE-CONTRACT.md. *)
(* base: commit 2fdcfd7be069 (post-landing line). kb round (brief
   the internal file wild-budget-kb-reshape.md): crt_live carries its budget kb and its journal
   at a budget WS with wbudget [] kb WS; the kit's live-state lemmas take and give that journal (the caller's at any
   WS, the callee's at its own WS1), its call rules run over YCbqGwild.aj_call_xbF (crt102rw_call / _call_ch at the
   callee's empty budget, crt102rw_call_b at a budgeted callee text), and its runs over PART 1b's wrappers. *)
(* fuzz_preset, the KIT of check_round_trip's walk on image A' (asan
   1be0f53d96cb9d6c, twin bff8519bbe3ea0e4): the Qed infrastructure the rewrite (Crt102Rewrite.v) and the loop slice
   (Crt102Loops.v) both bind, split out of Crt102Rewrite.v with every name kept.
   rule 24: no function proved (proof-index check_round_trip, exit 0, an internal record of that lookup);
   this file proves no function (kind: segment lemma support).
   INPUTS OF RECORD: the lane's glue lib/A/Prog/Crt102Glue.v (crt_live, crt_side, crt_saved, crt_frame, crt_spill,
   crt_bregs, crt_cfg, crt_at_J, crt_at_X), Crt102Img.v (the cut offsets), Crt102Model.v; the contract texts at the
   kit tip caa965672d21 by path on base 33ff96ae153c; engine 67637094dec6; listing d42e123915ae; build route
   pins102.
   CONTENTS. Part 1 (image-free, Section over segs): pj_fdR facts - crt102rw_nodeR_fdR (a represented tree is freeable
   at its depth), crt102rw_fdR_mono, crt102rw_fdR_frame (a freeable tree whose footprint keeps its bytes),
   crt102rw_nodeR_lblk / crt102rw_fdR_lblk (the block predicate may change as long as the tree's blocks stay blocks),
   crt102rw_rdword_of_vm. Part 2 (image A', the glue's Section variables as implicit Context): the entry's stack facts
   (crt102rw_sp), the class-3 frame (crt102rw_ff), the live state across a run of the body (crt102rw_live_run, whose
   writes are crt102rw_wr: the frame's shadow bytes 4 .. 22 and the spill words s1 + 0x38 .. 0x60) and across a call
   (crt102rw_live_call), the chain a callee is given (crt102rw_chain), the return site (crt102rw_ret), the call rule
   at the realigned sp (crt102rw_call, over YCbqGcall.v aj_call_xF), the symbolic-state readback (crt102rw_chunk_vm),
   the document's home (crt102rw_home_keep), and the shared re-poison X into the join (crt102rw_at_X, under TAIL);
   an IMAGE STRING as a C string from PRH_Base's kept_img (crt_cstr_img; crt_cstr_stamp_A / crt_cstr_modat_A at the two
   literals check_round_trip passes), over S10TxState.v's two MARKED STAND-INS, taken verbatim as Section hypotheses:
   zs_aligned (the unit's image binding of B; owner: the contract texts) and img_shadow_vis_x (owner: the image row).
   NUMERALS: 4752 (DERIVED, 4 * check_round_trip's listing slot), 512 / 64 (LENGTH, fs_frame_bytes 3 and its shadow),
   27632 (DERIVED, STK_check_round_trip by computation), 224 / 240 / 32 (LENGTH, the frame and the realignment),
   4 .. 22, 56 .. 96 (LENGTH, shadow offsets and spill offsets), 2 ^ 30 / 2 ^ 31 / 2 ^ 40 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64
   (DERIVED, address bounds), 2048 (LENGTH, a bound on the function's own offsets). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
(* the re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the
   zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* PART 1, image-free: the freeable-tree facts the join needs (pj_free (&copy) at STK_pj_free DOC_D).
   crt102rw_nodeR_fdR: a represented tree is freeable at its depth (transcribed from an earlier walk's H5CrtS7.v
   cx_nodeR_fd at commit 1934271f1f40, :264 (that file is not in this tree), itself plain PjStruct.v pj_node_fd over PRH_Reader's predicates);
   crt102rw_fdR_mono: freeable at d is freeable at every d' >= d; crt102rw_fdR_frame: a freeable tree whose footprint
   keeps its bytes (and writability) is the same freeable tree. *)
Section rd.
Variable segs : list Segment.

Lemma crt102rw_pf_items_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *; [exact Hp|].
destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.
Lemma crt102rw_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
intros m lblk Pi Pi' p D H (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. exact (H _ _ _ _ _ H6).
Qed.
Lemma crt102rw_fdR_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (S d) p D.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
- eapply (crt102rw_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
- eapply (crt102rw_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di Hi. cbv beta in Hi |- *.
  apply (crt102rw_pf_items_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi]. intros a D1 H1. exact (IH a D1 H1).
Qed.
Lemma crt102rw_fdR_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof.
intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|]. apply crt102rw_fdR_succ. apply IH. exact H.
Qed.
Lemma crt102rw_items_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma crt102rw_mems_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a D1) ->
  pj_memsR segs m lblk P a ka l D -> pf_itemsR segs m lblk Q true a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (x & k & D1 & D2 & E & Hx & (Hb & _) & HP & HR). exists [(x, k)], D1, D2.
split; [exact E|].
split; [unfold pj_keyR; exists x; split; [exact Hx | right; exists k; split; [exact Hb | reflexivity]]|].
split; [apply (H a u D1); [exists nm; left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 (nm' & Hv) HP3; apply (H a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma crt102rw_nodeR_fdR : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (PjTree.depth t) p D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk p D H;
  cbn [pj_nodeR] in H.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
  assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk d') false kids keys (Z.to_nat n) Di).
  { rewrite En, Nat2Z.id. apply (crt102rw_items_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 Hu HP. rewrite Forall_forall in IH.
    apply (crt102rw_fdR_mono m lblk (PjTree.depth u)); [|exact (IH u Hu m lblk a D1 HP)].
    pose proof (PjTree.depth_item items u Hu). lia. }
  destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
  + subst cap. exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|]. split; [left; split; [exact Ek | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. exact HI.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ek | split; reflexivity]|]. split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR. split; [exact Hn|]. split; [exact Ha|].
  destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
  + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia]. cbn [pj_memsR] in Hi.
    exists (PjTree.tag (PjTree.JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|]. split; [left; split; [exact Hy0 | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
    split; [subst D; cbn [app]; apply Permutation_refl|].
    cbv beta. rewrite En, Nat2Z.id. apply (crt102rw_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (crt102rw_fdR_mono m lblk (PjTree.depth u)); [|exact (IH m lblk a D1 HP)].
    pose proof (PjTree.depth_member members nm u Hu). lia.
Qed.

(* the frame lemma of a freeable tree: its header, its key words and its items lie in its footprint *)
Lemma crt102rw_pf_frame : forall m m' lblk (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D (X : Z -> Prop),
  pf_itemsR segs m lblk P ks a ka n D ->
  (ks = true -> forall x, ka <= x < ka + 8 * Z.of_nat n -> X x) ->
  (forall x, X x -> mbyte segs m' x = mbyte segs m x) ->
  (forall i a1 D1, (i < n)%nat -> a1 = a + 56 * Z.of_nat i -> incl D1 D -> P a1 D1 -> P' a1 D1) ->
  pf_itemsR segs m' lblk P' ks a ka n D.
Proof.
intros m m' lblk P P' ks n. induction n as [|n IH]; intros a ka D X H HX HM HP; cbn [pf_itemsR] in H |- *; [exact H|].
destruct H as (Dk & D1 & D2 & E & Hk & H1 & H2). exists Dk, D1, D2. split; [exact E|]. split.
- unfold pj_keyR in Hk |- *. destruct ks; [|exact Hk]. destruct Hk as (x & Hx & Hd). exists x. split; [|exact Hd].
  apply (rd_u64_frame segs m m' ka x Hx). intros y Hy. apply HM. apply (HX eq_refl). lia.
- split.
  + apply (HP 0%nat a D1); [lia | lia | |exact H1]. subst D. intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
  + apply (IH (a + 56) (ka + 8) D2 X H2).
    * intros Hks y Hy. apply (HX Hks). lia.
    * exact HM.
    * intros i a1 D3 Hi Ea Hinc HP3. apply (HP (S i) a1 D3); [lia | lia | |exact HP3].
      subst D. intros b Hb. apply in_or_app. right. apply in_or_app. right. exact (Hinc b Hb).
Qed.
Lemma crt102rw_fdR_frame : forall d m m' lblk p D, pj_fdR segs m lblk d p D ->
  pj_agreeR segs m m' (pj_footR p D) -> pj_fdR segs m' lblk d p D.
Proof.
intros d. induction d as [|d IH]; intros m m' lblk p D H HM; cbn [pj_fdR] in H |- *;
  destruct H as (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6);
  (split; [exact Hn|]); (split; [exact Ha|]); exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
  (split; [apply (pj_hdrR_frame segs m m'); [exact H1 | intros x Hx; apply HM; left; exact Hx]|]);
  (split; [exact H2|]); (split; [exact H3|]); (split; [exact H4|]); (split; [exact H5|]).
- exact H6.
- assert (HDi : forall b, In b Di -> In b D).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym H5)). rewrite !in_app_iff. tauto. }
  destruct (Z.eq_dec n 0) as [En0 | Hn0].
  + rewrite En0 in H6 |- *. cbn [Z.to_nat pf_itemsR] in H6 |- *. exact H6.
  + destruct H3 as [(_ & En & _) | (kb & Hkb & Hkn & EDk)]; [lia|].
    assert (HinK : In (kids, kb) D).
    { apply (Permutation_in _ (Permutation_sym H5)). rewrite !in_app_iff. subst Dk. cbn. tauto. }
    apply (crt102rw_pf_frame m m' lblk (pj_fdR segs m lblk d) (pj_fdR segs m' lblk d) ks (Z.to_nat n) kids keys Di
      (pj_footR p D) H6).
    * intros Hks x Hx. destruct H4 as [(_ & Ek & _) | (_ & yb & Hyb & Hyn & EDy)]; [rewrite Ek in Hks; discriminate|].
      right. exists (keys, yb). split.
      { apply (Permutation_in _ (Permutation_sym H5)). rewrite !in_app_iff. subst Dy. cbn. tauto. }
      unfold pj_holdsR. cbn [fst snd]. rewrite Z2Nat.id in Hx by lia. lia.
    * intros x Hx. exact (proj1 (HM x Hx)).
    * intros i a1 D1 Hi Ea Hinc HP. apply (IH m m' lblk a1 D1 HP). intros x Hx. apply HM.
      destruct Hx as [Hx | (b & Hb & Hx)].
      { right. exists (kids, kb). split; [exact HinK|]. unfold pj_holdsR. cbn [fst snd].
        apply Nat2Z.inj_lt in Hi. rewrite Z2Nat.id in Hi by lia. subst a1. lia. }
      { right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx]. }
Qed.

(* a word stored as 8 bytes reads back (YCem.v rdword_of_val_mem, over any segs) *)
Lemma crt102rw_rdword_of_vm : forall H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* the block predicate a tree is read under may change, as long as the tree's own blocks stay blocks (the ledger's
   list moves from call to call; a tree's blocks are what the new list must still hold) *)
Lemma crt102rw_mems_lblk : forall m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D -> (forall x k, In (x, k) D -> lblk' x k) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H HL HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & (Hl & Hc) & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|]. split; [split; [apply HL; left; reflexivity | exact Hc]|]. split.
- specialize (HP 0%nat nm u D1 eq_refl (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))).
  replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1).
- apply (IH (a + 56) (ka + 8) D2 H2).
  + intros y k' Hy. apply HL. right. apply in_or_app. right. exact Hy.
  + intros i nm' u' D1' Hi Hinc HPi.
    specialize (HP (S i) nm' u' D1' Hi (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia. exact (HP HPi).
Qed.
Lemma crt102rw_nodeR_lblk : forall t m lblk lblk' p D, pj_nodeR segs m lblk p t D ->
  (forall x k, In (x, k) D -> lblk' x k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. split; [apply HL; subst D; left; reflexivity | exact Hc].
- destruct Hb as (E2 & E3 & E4 & E5 & k & (Hl & Hc) & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. split; [apply HL; subst D; left; reflexivity | exact Hc].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hc0 & _)]; [left; exact Hcap | right; split; [exact Hc0|]].
    apply HL. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros x k Hxk. apply HL. apply HDi. apply Hinc. exact Hxk.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hc0 & _ & _)]; [left; exact Hcap | right; split; [exact Hc0|]].
    split; apply HL; rewrite ED; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; [left; reflexivity | right; left; reflexivity]. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (crt102rw_mems_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi).
  + intros x k Hxk. apply HL. apply HDi. exact Hxk.
  + intros i nm u D1 Hil Hinc HP. rewrite Forall_forall in IH.
    specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m lblk lblk' _ D1 HP). intros x k Hxk. apply HL. apply HDi. apply Hinc. exact Hxk.
Qed.
Lemma crt102rw_pf_lblk : forall m lblk lblk' (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D,
  pf_itemsR segs m lblk P ks a ka n D -> (forall x k, In (x, k) D -> lblk' x k) ->
  (forall a1 D1, incl D1 D -> P a1 D1 -> P' a1 D1) ->
  pf_itemsR segs m lblk' P' ks a ka n D.
Proof.
intros m lblk lblk' P P' ks n. induction n as [|n IH]; intros a ka D H HL HP; cbn [pf_itemsR] in H |- *; [exact H|].
destruct H as (Dk & D1 & D2 & E & Hk & H1 & H2). exists Dk, D1, D2. split; [exact E|]. split.
- unfold pj_keyR in Hk |- *. destruct ks; [|exact Hk]. destruct Hk as (x & Hx & [Hd | (k & Hl & Hd)]).
  + exists x. split; [exact Hx | left; exact Hd].
  + exists x. split; [exact Hx|]. right. exists k. split; [|exact Hd]. apply HL. subst D Dk. left. reflexivity.
- split.
  + apply HP; [|exact H1]. intros y Hy. subst D. apply in_or_app. right. apply in_or_app. left. exact Hy.
  + apply (IH (a + 56) (ka + 8) D2 H2).
    * intros x k Hxk. apply HL. subst D. apply in_or_app. right. apply in_or_app. right. exact Hxk.
    * intros a1 D3 Hinc HP3. apply HP; [|exact HP3]. intros y Hy. subst D. apply in_or_app. right.
      apply in_or_app. right. exact (Hinc y Hy).
Qed.
Lemma crt102rw_fdR_lblk : forall d m lblk lblk' p D, pj_fdR segs m lblk d p D ->
  (forall x k, In (x, k) D -> lblk' x k) -> pj_fdR segs m lblk' d p D.
Proof.
intros d. induction d as [|d IH]; intros m lblk lblk' p D H HL; cbn [pj_fdR] in H |- *;
  destruct H as (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6);
  (split; [exact Hn|]); (split; [exact Ha|]); exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
  assert (HIn : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D) by (intros b Hb; exact (Permutation_in _ (Permutation_sym H5) Hb));
  (split; [exact H1|]).
all: split; [destruct H2 as [H2 | (k & Hl & Hd)]; [left; exact H2 | right; exists k; split; [apply HL; apply HIn; subst Ds; left; reflexivity | exact Hd]]|].
all: split; [destruct H3 as [H3 | (k & Hl & Hk & Hd)]; [left; exact H3 | right; exists k; split; [apply HL; apply HIn; subst Dk; apply in_or_app; right; left; reflexivity | split; [exact Hk | exact Hd]]]|].
all: split; [destruct H4 as [H4 | (Hks & k & Hl & Hk & Hd)]; [left; exact H4 | right; split; [exact Hks|]; exists k; split; [apply HL; apply HIn; subst Dy; rewrite !in_app_iff; right; right; left; left; reflexivity | split; [exact Hk | exact Hd]]]|].
all: split; [exact H5|].
- exact H6.
- apply (crt102rw_pf_lblk m lblk lblk' (pj_fdR segs m lblk d) (pj_fdR segs m lblk' d) ks (Z.to_nat n) kids keys Di H6).
  + intros x k Hxk. apply HL. apply HIn. rewrite !in_app_iff. tauto.
  + intros a1 D1 Hinc HP. apply (IH m lblk lblk' a1 D1 HP). intros x k Hxk. apply HL. apply HIn.
    rewrite !in_app_iff. right; right; right. exact (Hinc _ Hxk).
Qed.
End rd.

(* ======================================================================================================== *)
(* PART 1b (kb round), image-free: YC1fPx.v's four runners (paj_run_x, paj_run_to_x, paj_run_x_inv, paj_run_to_x_inv)
   over a journal AT A WILD-TRACE BUDGET WS (YCbqG.v ajournal_xw; ajournal_x is it at WS = []). A straight-line run
   stores no wild trace, so the journal after it is at the same WS: each wrapper rebases the journal to the entry whose
   depot is the current one (YCbqGwild.ajournal_xw_rebase), runs YC1fPx's runner, and steps back to the budget WS
   (YCbqGwild.ajournal_xw_unbase0, from the journal's own wild clause YCbqG.ajx_wild). WS is the FIRST binder, so
   `@crt_run_xw .. LAWS WS` has the binder list of `@paj_run_x .. LAWS` and YC1fPx's tactics paj_run_tok_x /
   paj_run_to_tok_x / paj_run_tok_x_inv / paj_run_to_tok_x_inv run it unchanged; the post's journal is at WS again.
   The re-hiding move: the journal is at R := YA0nH.wle' pa_segs YGcfRehidePost.RZ_cf
   (ajournal_xwR) and the step relation is YA0nH.SRr' pa_segs RZ_cf, both in the premise and in the post
   crt_run_post_w(_inv); the wrappers run the R runners paj_run_xR / paj_run_to_xR / paj_run_x_invR /
   paj_run_to_x_invR at R (wle'_refl / wle'_trans) over ajournal_xw_rebaseR / ajournal_xw_unbase0R and YCbqG.ajxR_wild.
   Binder lists unchanged, so the same tactics run them.
   rule 24: no function proved (kind: engine lemma wrappers). *)
Section kbw. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
#[local] Notation RZW := (YA0nH.wle' pa_segs YGcfRehidePost.RZ_cf).
#[local] Notation AJW := (ajournal_xwR (SK := SK) pa_segs B PST ARx RZW).

(* YC80x.v's run_post_pi_tok_AJx with the journal at WS *)
Definition crt_run_post_w (WS : list (list Z)) (W : world pa_segs) (E : env) (K : nat) (Bx : sv) (SH : list shent)
  (ss : sstate) (st' : shst) (r : ptrun_status asym) (ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z))
  ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z) (Q : world pa_segs -> config -> Prop) : Prop :=
  forall ws ms' mat',
  length ws = sh_j st' ->
  img_env pa_val A_LIM (extK E K ws) ->
  match r with
  | PTS_call s => st_ok pa_segs (extK E K ws) (setpc (sh_ss st') (pa_sigma s)) (restrict (w_H W) ms')
  | _ => st_ok_pi pa_segs pa_val (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
  end ->
  sh_ok pa_segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k WS ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  YA0nH.SRr' pa_segs YGcfRehidePost.RZ_cf W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.

(* the journal's wild clause, read from an ajournal_xwR hypothesis at RZW *)
Lemma crt_jw_wild : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS,
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS ->
  incl (wild_part (as_universe B) (st_depot Sc)) (wild_part (as_universe B) (st_depot S) ++ WS).
Proof. intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS HJ. exact (ajxR_wild HJ). Qed.

Lemma crt_run_xw : forall (WS : list (list Z)) W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc
    Hpc mdc k Q,
  (A_LIM <= K)%nat -> img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sh_ok pa_segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_runN_pi_tok pl_tpi pl_tw K Bx Bspan SH n ss = (st', r) ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
  Forall (ob_holds pa_segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  crt_run_post_w WS W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  YA0nH.SRr' pa_segs YGcfRehidePost.RZ_cf W (mkCfg ms mdc) Q.
Proof.
intros WS W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ
  Hobl Hwr Hk.
pose proof (crt_jw_wild _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
apply (@paj_run_xR fx rc SK L PL PI B PST ARx HL LAWS RZW (YA0nH.wle'_refl pa_segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans pa_segs YGcfRehidePost.RZ_cf) W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly
  (set_depot (st_depot Sc) S) Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun
  HJr Hobl Hwr).
intros ws ms' mat' H1 H2 H3 H4 HJ' H5 H6 H7. apply (Hk ws ms' mat' H1 H2 H3 H4); [|exact H5 | exact H6 | exact H7].
eapply YCbqGwild.ajournal_xw_unbase0R; [exact HJ' | exact Hinc].
Qed.
Lemma crt_run_to_xw : forall (WS : list (list Z)) W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md
    own lyc Sc Hpc mdc k Q,
  (A_LIM <= K)%nat -> img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sh_ok pa_segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok pl_tpi pl_tw K Bx Bspan SH n stop ss = (st', r) ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
  Forall (ob_holds pa_segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  crt_run_post_w WS W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  YA0nH.SRr' pa_segs YGcfRehidePost.RZ_cf W (mkCfg ms mdc) Q.
Proof.
intros WS W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk
  Hrun HJ Hobl Hwr Hk.
pose proof (crt_jw_wild _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
apply (@paj_run_to_xR fx rc SK L PL PI B PST ARx HL LAWS RZW (YA0nH.wle'_refl pa_segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans pa_segs YGcfRehidePost.RZ_cf) W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly
  (set_depot (st_depot Sc) S) Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun
  HJr Hobl Hwr).
intros ws ms' mat' H1 H2 H3 H4 HJ' H5 H6 H7. apply (Hk ws ms' mat' H1 H2 H3 H4); [|exact H5 | exact H6 | exact H7].
eapply YCbqGwild.ajournal_xw_unbase0R; [exact HJ' | exact Hinc].
Qed.

(* the memory-invariant forms (YC1fPx.v paj_run_x_inv / paj_run_to_x_inv, at R: paj_run_x_invR / paj_run_to_x_invR):
   P and its laws after LAWS *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws pa_segs P.
Definition crt_run_post_w_inv (WS : list (list Z)) (W : world pa_segs) (E : env) (K : nat) (Bx : sv) (SH : list shent)
  (ss : sstate) (st' : shst) (r : ptrun_status asym) (ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z))
  ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z) (Q : world pa_segs -> config -> Prop) : Prop :=
  forall ws ms' mat',
  length ws = sh_j st' ->
  img_env pa_val A_LIM (extK E K ws) ->
  match r with
  | PTS_call s => st_ok pa_segs (extK E K ws) (setpc (sh_ss st') (pa_sigma s)) (restrict (w_H W) ms')
  | _ => st_ok_pi pa_segs pa_val (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
  end ->
  sh_ok pa_segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k WS ->
  P (ms_mem ms') ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  YA0nH.SRr' pa_segs YGcfRehidePost.RZ_cf W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma crt_run_xw_inv : forall (WS : list (list Z)) W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own
    lyc Sc Hpc mdc k Q,
  (A_LIM <= K)%nat -> img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sh_ok pa_segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_runN_pi_tok pl_tpi pl_tw K Bx Bspan SH n ss = (st', r) ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
  P (ms_mem ms) ->
  Forall (ob_holds pa_segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  crt_run_post_w_inv WS W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  YA0nH.SRr' pa_segs YGcfRehidePost.RZ_cf W (mkCfg ms mdc) Q.
Proof.
intros WS W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ
  HPm Hobl Hwr Hk.
pose proof (crt_jw_wild _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
apply (@paj_run_x_invR fx rc SK L PL PI B PST ARx HL LAWS P PLAW RZW (YA0nH.wle'_refl pa_segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans pa_segs YGcfRehidePost.RZ_cf) W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly
  (set_depot (st_depot Sc) S) Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun
  HJr HPm Hobl Hwr).
intros ws ms' mat' H1 H2 H3 H4 HJ' HP' H5 H6 H7.
apply (Hk ws ms' mat' H1 H2 H3 H4); [| exact HP' | exact H5 | exact H6 | exact H7].
eapply YCbqGwild.ajournal_xw_unbase0R; [exact HJ' | exact Hinc].
Qed.
Lemma crt_run_to_xw_inv : forall (WS : list (list Z)) W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md
    own lyc Sc Hpc mdc k Q,
  (A_LIM <= K)%nat -> img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sh_ok pa_segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok pl_tpi pl_tw K Bx Bspan SH n stop ss = (st', r) ->
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
  P (ms_mem ms) ->
  Forall (ob_holds pa_segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  crt_run_post_w_inv WS W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  YA0nH.SRr' pa_segs YGcfRehidePost.RZ_cf W (mkCfg ms mdc) Q.
Proof.
intros WS W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk
  Hrun HJ HPm Hobl Hwr Hk.
pose proof (crt_jw_wild _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
apply (@paj_run_to_x_invR fx rc SK L PL PI B PST ARx HL LAWS P PLAW RZW (YA0nH.wle'_refl pa_segs YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans pa_segs YGcfRehidePost.RZ_cf) W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly
  (set_depot (st_depot Sc) S) Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun
  HJr HPm Hobl Hwr).
intros ws ms' mat' H1 H2 H3 H4 HJ' HP' H5 H6 H7.
apply (Hk ws ms' mat' H1 H2 H3 H4); [| exact HP' | exact H5 | exact H6 | exact H7].
eapply YCbqGwild.ajournal_xw_unbase0R; [exact HJ' | exact Hinc].
Qed.
End kbw.

(* ======================================================================================================== *)
(* PART 2, image A': the kit of check_round_trip's own frame - the live state across a run and across a call, the
   call rule at the realigned sp, the chain a callee is given, and the shared re-poison X into the join. *)
Section crtA. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation STKC := (@STK_check_round_trip prh_img_A).

Lemma crt102rw_pc : CRT_PC_A = 4752.
Proof. vm_compute. reflexivity. Qed.
Lemma crt102rw_fb : fs_frame_bytes CRT_CID = 512.
Proof. vm_compute. reflexivity. Qed.
Section f.
Context {B : asyms}.
Context {ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop}.
(* the re-hiding move: the world relation of every journal below, the glue's crt_live_journal's
   and QF's, R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* the callee's journal at the empty budget (YCbqG.v ajournal_xR at RZW) *)
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR at RZW; AJ is it at WS = []); crt_live's journal is at
   the boundary's budget kb (kb round) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* ---- AN IMAGE STRING HANDED TO A CALLEE AS A C STRING (pj_string's STAMP at +0x24c, pj_set's MOD_AT at +0x278, and
   the loop slice's strcmp literals): the state-free kept_img (PRH_Base.v, kept_at's third case) and the image's own
   bytes give cstr_ok at ANY ARx state with the read-only view. The derivation is S10TxState.v's s10_src_img
   (commit 88b4aea723f, lib/A/Prog/S10TxState.v:562-594), extended by the NUL, the 8-byte slack
   and the tail granule cstr_ok asks; it takes S10's two stand-ins byte for byte (the statement over this file's
   SEGS), so there is one derivation and one place both appear. ---- *)
(* MARKED STAND-IN (the unit's image binding of B; owner: the contract texts; ARcf gives it by amc_syms / aso_zshadow,
   YG0f.v:191). Verbatim S10TxState.v:141. *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN (owner: the image row; FuzzStrdup.v's img_shadow_vis_cf restated over ARx). Verbatim
   S10TxState.v:143. *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.

(* the hull of a range at least 64 bytes inside [IMG_LO, IMG_TOP) is the shadow of image bytes (S10TxState.v:110-124
   s10_hull_img, verbatim) *)
Lemma crt_hull_img : forall a n s, 0 < n -> IMG_LO + 64 <= a -> a + n + 64 <= IMG_TOP ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ IMG_LO <= 8 * (s - SHADOW_OFF) < IMG_TOP.
Proof.
intros a n s Hn Hlo Hhi Hs. unfold IMG_LO, IMG_TOP in *. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
(* one read-back byte (S10TxState.v:183-194 s10_val1_of_aview, verbatim) *)
Lemma crt_val1_of_aview : forall (H : word -> bool) mem a v, aview SEGS H mem a = Some v ->
  val_mem SEGS (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros H mem a v E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H mem) a) as [bb|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb.
f_equal. rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

Lemma crt_cstr_img : forall ly S Hp W mem md p cs,
  ARx ly S Hp W mem md -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  kept_img B p (Z.of_nat (length cs) + 1) -> Forall (fun b => 0 < b < 256) cs ->
  (forall j, (j < length (cs ++ [0%Z]))%nat ->
     option_map (fun bb : byte => bv_unsigned bb) (YK11.seg_rom SEGS (Z_to_bv 64 (p + Z.of_nat j))) =
     Some (nth j (cs ++ [0]) 0)) ->
  (forall a, p + Z.of_nat (length cs) < a < p + Z.of_nat (length cs) - (p + Z.of_nat (length cs)) mod 8 + 8 ->
     YK11.seg_rom SEGS (Z_to_bv 64 a) <> None) ->
  cstr_ok W mem p cs.
Proof.
intros ly S Hp W mem md p cs HAR HRO HKI Hcs Hrom Htail.
pose proof HKI as (Hlo & Hhi & Hro).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (YM05.alloc_ceiling_val) as Hcv.
assert (Hn : length (cs ++ [0%Z]) = Datatypes.S (length cs)) by (rewrite length_app; cbn; lia).
change (@pa_lo _ _ PA) with YImgTop.IMG_LO in Hlo. change (@pa_hi _ _ PA) with YImgTop.IMG_TOP in Hhi.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hlo, Hhi.
split; [split|].
{ (* the bytes, NUL included, from the read-only view *)
  intros j Hj. rewrite Hn in Hj.
  destruct (Hro (p + Z.of_nat j) ltac:(lia)) as (Hr & Hno & Her & _).
  pose proof (HRO _ Hr Hno Her) as E. rewrite (Hrom j ltac:(rewrite Hn; lia)) in E.
  exact (crt_val1_of_aview (w_H W) mem _ _ E). }
{ eapply Forall_impl; [|exact Hcs]. cbv beta. intros b Hb. lia. }
split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold YGcfStr.amem_range8; left; lia|].
split.
{ intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hc & Hv)]).
  - destruct Hzs as (q & m & Hin & Hq & Hqm).
    pose proof (proj1 (Forall_forall _ _) zs_aligned (q, m) Hin) as (Hq8 & Hm8). cbn [fst snd] in Hq8, Hm8.
    pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (q, m) HAR ltac:(right; exact Hin)) as Hz.
    cbn [fst snd] in Hz. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Hq8 Hm8 Hz x ltac:(lia)).
  - pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARx LAWS ly S Hp W mem md HAR) _ (Hc ly)) as Hcell.
    unfold cell_holds, z1, c1 in Hcell. cbn [c_at c_w c_val aeval] in Hcell.
    specialize (Hcell 0%nat ltac:(lia)). rewrite Z.add_0_r in Hcell.
    exists v. split; [|unfold saddr_ok; lia].
    unfold shadow_of_addr. unfold shadow_addr in Hcell. rewrite Hcell. f_equal.
    unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r, (Z.mod_small v (2 ^ 8)) by lia. apply Z.mod_small. lia. }
split.
{ intros s0 Hs. destruct (crt_hull_img p (Z.of_nat (length cs) + 1) s0 ltac:(lia) ltac:(unfold IMG_LO; lia)
    ltac:(unfold IMG_TOP; lia) Hs)
    as [E Hr].
  rewrite E. exact (img_shadow_vis_x ly S Hp W mem md _ HAR Hr). }
{ intros a Ha. unfold aview, mbyte. destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)); [cbn; discriminate|].
  destruct (YK11.seg_rom SEGS (Z_to_bv 64 a)) eqn:Er; [cbn; discriminate|]. exfalso. exact (Htail a Ha Er). }
Qed.

(* the tail granule of a string ending at q is image bytes: a computed check over q + 0 .. q + 8 *)
Lemma crt_tail_rom_of_check : forall q,
  forallb (fun k => match YK11.seg_rom SEGS (Z_to_bv 64 (q + Z.of_nat k)) with Some _ => true | None => false end)
    (seq 0 9) = true ->
  forall a, q < a < q - q mod 8 + 8 -> YK11.seg_rom SEGS (Z_to_bv 64 a) <> None.
Proof.
intros q Hc a Ha. pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
rewrite forallb_forall in Hc. specialize (Hc (Z.to_nat (a - q))).
rewrite Z2Nat.id in Hc by lia. replace (q + (a - q)) with a in Hc by lia.
assert (Hin : In (Z.to_nat (a - q)) (seq 0 9)) by (apply in_seq; lia).
specialize (Hc Hin). destruct (YK11.seg_rom SEGS (Z_to_bv 64 a)); [discriminate | discriminate Hc].
Qed.

(* the two strings check_round_trip hands its callees, as C strings at any ARx state with the read-only view *)
Lemma crt_cstr_stamp_A : forall ly S Hp W mem md,
  ARx ly S Hp W mem md -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  kept_img B CRT_STAMP_A (Z.of_nat (length ck_STAMP) + 1) -> cstr_ok W mem CRT_STAMP_A ck_STAMP.
Proof.
intros ly S Hp W mem md HAR HRO HKI.
apply (crt_cstr_img ly S Hp W mem md CRT_STAMP_A ck_STAMP HAR HRO HKI cm_STAMP_bytes).
- exact (proj2 crt_str_rom_A).
- apply crt_tail_rom_of_check. vm_compute. reflexivity.
Qed.
Lemma crt_cstr_modat_A : forall ly S Hp W mem md,
  ARx ly S Hp W mem md -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  kept_img B CRT_MOD_AT_A (Z.of_nat (length ck_MOD_AT) + 1) -> cstr_ok W mem CRT_MOD_AT_A ck_MOD_AT.
Proof.
intros ly S Hp W mem md HAR HRO HKI.
apply (crt_cstr_img ly S Hp W mem md CRT_MOD_AT_A ck_MOD_AT HAR HRO HKI cm_MOD_AT_bytes).
- exact (proj1 crt_str_rom_A).
- apply crt_tail_rom_of_check. vm_compute. reflexivity.
Qed.

(* ---- A PLAIN CALLEE TEXT IN THE WALK AT wle'. A callee whose text still concludes SRr (at wle)
   with apost_base_xF / apost_base_x (fpost) meets the R premise of crt102rw_call / crt102rw_call_ch (apost_base_xFR at
   RZW under SRr', i.e. PRH_Base's fpostF): YA0nH.SRr_SRr' on the step relation, YCbqG.apost_base_xF_R_lift at
   YA0nH.wle_wle' on the post; a text that leaves the float state alone first takes apost_base_x_F at frm_zero. ---- *)
Lemma crt102rw_lift_xF : forall (fxk : YK11.FPState) (Wc : world SEGS) (c : config) STK1 FP1 (rg : bvmap 5 word)
    lyc Sc Hpc memc mdc Q,
  SRr SEGS Wc c (apost_base_xF (fx := fxk) (SK := SK) SEGS B PST ARx STK1 FP1 rg lyc Sc Hpc Wc memc mdc Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc c
    (apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx RZW STK1 FP1 rg lyc Sc Hpc Wc memc mdc Q).
Proof.
intros fxk Wc c STK1 FP1 rg lyc Sc Hpc memc mdc Q H.
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf); [exact (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf Wc c _ H)|].
intros W' c' _ Hp. eapply apost_base_xF_R_lift; [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact Hp].
Qed.
Lemma crt102rw_lift_x : forall (fxk : YK11.FPState) (Wc : world SEGS) (c : config) STK1 FP1 (rg : bvmap 5 word)
    lyc Sc Hpc memc mdc Q,
  frm_zero (@YK11.fp_csr fxk) ->
  SRr SEGS Wc c (apost_base_x (fx := fxk) (SK := SK) SEGS B PST ARx STK1 FP1 rg lyc Sc Hpc Wc memc mdc Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc c
    (apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx RZW STK1 FP1 rg lyc Sc Hpc Wc memc mdc Q).
Proof.
intros fxk Wc c STK1 FP1 rg lyc Sc Hpc memc mdc Q HFZ H.
apply (crt102rw_lift_xF fxk Wc c STK1 FP1 rg lyc Sc Hpc memc mdc Q).
eapply SRr_mono; [exact H|]. intros W' c' _ Hp. eapply (apost_base_x_F (fx := fxk)); [exact HFZ | exact Hp].
Qed.

Section g.
Context {rp_sm : list Z -> Z * Z} {rp_x : list Z} {rp_os : list (option nat * option nat * option nat)}
  {rp_i : nat} {rp_H0 : list Z}.
Context {ly : alayout} {S : astate} {Hp : list Z} {W : world SEGS} {regs : bvmap 5 word}
  {mem : word -> option byte} {md : Model} {ch : list (Z * Z * Z)}
  {doc : Z} {t : PjTree.jv} {D : list (Z * Z)} {Lam : list (Z * Z)} {peak cnt ran most : Z}.
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (CRT_sp1 (regs := regs)).
#[local] Notation liveA := (crt_live (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation atJ := (crt_at_J (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation atX := (crt_at_X (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation QFa := (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgA := (crt_cfg (rc := rc) (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A)).
#[local] Notation bregsA := (crt_bregs (regs := regs)).

(* ---- the entry's premises the kit reads: tcheck_round_trip_specX's fpre and ck_tree_ok (Crt102Top.v discharges them
   from the text's own) ---- *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
(* the universe closure and the observed context, for the free calls' traces (crt102rw_free_trace only) *)
Context {CTX0 : list (list Z)}.
Hypothesis HCL : prh_univ_closure B CTX0.
Hypothesis HCTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).

(* ---- the join: Crt102Tail.v's crt102_tail, the single lemma every arm ends in; only
   crt102rw_at_X takes it ---- *)
Hypothesis TAIL : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  atJ fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_J_OFF rg memc mdc) QFa.

(* ---- the entry's stack facts ---- *)
Lemma crt102rw_stkc : STKC = 27632.
Proof. vm_compute. reflexivity. Qed.
Lemma crt102rw_sp : sp0 mod 16 = 0 /\ YM05.alloc_ceiling + 27632 <= sp0 /\ sp0 <= 2 ^ 47 /\
  sp0 - 240 <= sp1 <= sp0 - 224 /\ sp1 mod 32 = 0 /\ 0 <= sp1.
Proof.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
rewrite crt102rw_stkc in *.
pose proof (YM05.alloc_ceiling_val) as Hc.
unfold CRT_sp1, CRT_FRAME, CRT_ALIGN.
pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
split; [exact Hal16|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [apply Z.mod_mul; lia|]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.

(* the entry's float state and ARx *)
Lemma crt102rw_ar0 : ARx ly S Hp W mem md.
Proof. exact (proj1 (proj1 HPRE)). Qed.

(* ---- the frame (CRT_CID, pos) the journal owns: on the frame list, bounded, its bytes and shadow present ---- *)
Lemma crt102rw_ff : forall lyc Sc Hpc Wc memc mdc kj pos {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  In (CRT_CID, pos) (frames Sc) /\
  4096 <= frame_addr lyc CRT_CID pos /\ frame_addr lyc CRT_CID pos + 512 <= YM05.alloc_ceiling /\
  in_app (frame_addr lyc CRT_CID pos) 512 /\ frame_addr lyc CRT_CID pos mod 32 = 0 /\
  (forall a, frame_addr lyc CRT_CID pos <= a < frame_addr lyc CRT_CID pos + 512 ->
     apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr (frame_addr lyc CRT_CID pos) + i) /\
     ~ aowned B lyc Sc (shadow_addr (frame_addr lyc CRT_CID pos) + i)).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos WS HJ.
pose proof HJ as (HARc & _ & _ & _ & _ & HFRc & _).
assert (Hin : In (CRT_CID, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (F32 & _ & Ffr & Fsh).
rewrite crt102rw_fb in Fb2, Fb3, Ffr, Fsh. change (512 / 8) with 64 in Fsh.
split; [exact Hin|]. split; [exact Fb1|]. split; [exact Fb2|]. split; [exact Fb3|]. split; [exact F32|].
split; [exact Ffr | exact Fsh].
Qed.

(* ---- the document's 56 bytes lie in a fake frame of the entry: application memory below alloc_ceiling ---- *)
Lemma crt102rw_doc_home : 4096 <= doc /\ doc + 56 <= YM05.alloc_ceiling /\ in_app doc 56 /\ doc mod 8 = 0.
Proof.
pose proof HTREE as (_ & _ & _ & (Hd8 & (cid & pos' & Hin & H1 & H2) & _)).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos' crt102rw_ar0 Hin) as (Fb1 & Fb2 & Fb3).
split; [lia|]. split; [lia|]. split; [|exact Hd8].
apply (in_app_sub _ _ _ _ Fb3); lia.
Qed.

(* ---- THE WRITES OF THIS SLICE'S OWN RUNS: the shadow of back and v (frame shadow bytes 4 .. 22) and the spill words
   at sp1 + 0x38 .. sp1 + 0x58 ---- *)
Definition crt102rw_wr (F a : Z) : Prop :=
  (shadow_addr F + 4 <= a < shadow_addr F + 23) \/ (sp1 + 56 <= a < sp1 + 96).

Lemma crt102rw_nw_low : forall F a, 0 <= F -> 0 <= a < kLowMemEnd -> ~ crt102rw_wr F a.
Proof.
intros F a HF Ha [Hw | Hw]; pose proof crt102rw_sp as (_ & Hc & _ & Hs1 & _); pose proof (YM05.alloc_ceiling_val);
  unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *; lia.
Qed.
Lemma crt102rw_nw_app : forall F a, 0 <= F -> F + 512 <= YM05.alloc_ceiling -> in_app a 1 -> a < YM05.alloc_ceiling ->
  ~ crt102rw_wr F a.
Proof.
intros F a HF HF2 Ha Hac [Hw | Hw]; pose proof crt102rw_sp as (_ & Hc & _ & Hs1 & _); pose proof (YM05.alloc_ceiling_val);
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia.
Qed.
Lemma crt102rw_nw_stack : forall F a, 0 <= F -> F + 512 <= YM05.alloc_ceiling -> YM05.alloc_ceiling <= a ->
  ~ (sp1 + 56 <= a < sp1 + 96) -> ~ crt102rw_wr F a.
Proof.
intros F a HF HF2 Ha Hn [Hw | Hw]; [|exact (Hn Hw)]. pose proof (YM05.alloc_ceiling_val).
unfold shadow_addr, SHADOW_OFF in *; lia.
Qed.

Lemma crt102rw_pst_most : forall k, (k < pi_gz_most)%nat -> Exists (in_zr (pi_g_most + Z.of_nat k)) PST.
Proof. intros k Hk. unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma crt102rw_pst_own : forall k, (k < pi_gz_own_ran_out)%nat -> Exists (in_zr (pi_g_own_ran_out + Z.of_nat k)) PST.
Proof. intros k Hk. unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma crt102rw_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* ---- the live state across one of this slice's own runs (its writes in crt102rw_wr) ---- *)
Lemma crt102rw_live_run : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc {kbg : nat}
    {WS : list (list Z)},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS -> YCbqGwild.wbudget [] kbg WS ->
  (forall xw : word, ~ crt102rw_wr (frame_addr lyc CRT_CID pos) (bv_unsigned xw) ->
     mrestrict (w_H Wc) memc' xw = mrestrict (w_H Wc) memc xw) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  liveA kbg lyc Sc Hpc Wc memc' mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc kbg WS HL HJ' HB' Hag HMN'.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH. clear HL.
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ') as (_ & _ & _ & _ & _ & Ffr' & Fsh').
pose proof HJ as (HARc & _).
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof crt102rw_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt102rw_doc_home as (Hd1 & Hd2 & Hd3 & Hd4).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ crt102rw_wr F a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply aview_eq_of. apply Hag. rewrite unsigned_lit_small by lia. exact Hn. }
assert (Kmb : forall a, 0 <= a < 2 ^ 64 -> ~ crt102rw_wr F a ->
  mbyte SEGS (mrestrict (w_H Wc) memc') a = mbyte SEGS (mrestrict (w_H Wc) memc) a).
{ intros a Ha Hn. unfold mbyte. rewrite (Hag (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn. }
assert (Kw : forall a, 0 <= a < 2 ^ 64 -> ~ crt102rw_wr F a ->
  writable_at SEGS (mrestrict (w_H Wc) memc) a -> writable_at SEGS (mrestrict (w_H Wc) memc') a).
{ intros a Ha Hn Hw. unfold writable_at, wview in *. rewrite (Hag (Z_to_bv 64 a)); [exact Hw|].
  rewrite unsigned_lit_small by lia. exact Hn. }
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
assert (Kblk : forall a k, In (a, k) Lamc -> 0 <= k /\ forall i, 0 <= i < k + 16 ->
  0 <= a - 16 + i < 2 ^ 64 /\ ~ crt102rw_wr F (a - 16 + i)).
{ intros a k Hk. pose proof (crt_side_ledger HSD) as HLED.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hk) as (Hk0 & Hab & _).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
  rewrite Hch16 in *.
  assert (Hrs : k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
  split; [exact Hk0|]. intros i Hi.
  split; [lia|]. apply (crt102rw_nw_app F _ ltac:(lia) ltac:(lia)); [|lia].
  apply (in_app_sub _ _ _ _ Bapp); lia. }
assert (Hs2 : shadow_addr F mod 4 = 0 /\ SHADOW_OFF <= shadow_addr F /\ shadow_addr F + 64 <= SHADOW_OFF + 2 ^ 44).
{ unfold shadow_addr, SHADOW_OFF. split; lia. }
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB'); crt_live_side := _; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB;
          crt_live_dx_apart := HAP; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _;
          crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := HMN' |}.
{ pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
  pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HRO.
  pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
  refine {| crt_side_ledger := _; crt_side_peak := HPK; crt_side_room := HRL; crt_side_arodata := _;
            crt_side_doc := _; crt_side_doc_blocks := HDL |}.
  { apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc lyc Sc Hpc Wc memc' Lamc peakc cntc SIZE_MAXZ ranc most ownc HLED).
    - intros a Ha. pose proof (pa_segs_low a (pst_in_img_A a Ha)) as Hl. apply K; [unfold kLowMemEnd in Hl; lia|].
      apply crt102rw_nw_low; [lia | exact Hl].
    - intros a k i Hk Hi. destruct (Kblk a k Hk) as (Hk0 & Hb). rewrite Hch16.
      destruct (Hb i ltac:(lia)) as (H1 & H2). apply K; assumption.
    - intros a k _ Hab. exact Hab.
    - apply Permutation_refl. }
  { intros a Hro Ho He. pose proof (pa_segs_low a (crt102rw_ro_img a Hro)) as Hl.
    rewrite K; [exact (HRO a Hro Ho He) | unfold kLowMemEnd in Hl; lia | apply crt102rw_nw_low; [lia | exact Hl]]. }
  { apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') (prh_lin Lamc) doc D HDOC).
    intros y Hy.
    assert (Hyr : 0 <= y < 2 ^ 64 /\ ~ crt102rw_wr F y).
    { destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
      - split; [lia|]. apply (crt102rw_nw_app F y ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ Hd3); lia.
      - unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
        destruct (Kblk b kb (HDL _ Hb)) as (Hk0 & Hbb).
        destruct (Hbb (y - (b - 16)) ltac:(lia)) as (H1 & H2).
        replace (b - 16 + (y - (b - 16))) with y in H1, H2 by lia. split; assumption. }
    split; [apply Kmb; apply Hyr | apply Kw; apply Hyr]. } }
{ intros j Hj k Hk. rewrite Kmb; [exact (HSV j Hj k Hk) | lia |].
  apply (crt102rw_nw_stack F _ ltac:(lia) ltac:(lia)); lia. }
{ pose proof (crt_frame_listed HFRM) as Hinf. pose proof (crt_frame_flag_word HFRM) as Hfl.
  refine {| crt_frame_listed := Hinf; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - rewrite <- Hfl. apply ts_rdword_keep. intros j Hj. rewrite crt102rw_fb.
    apply K; [lia|]. apply (crt102rw_nw_app F _ ltac:(lia) ltac:(lia)); [|lia]. apply (in_app_sub _ _ _ _ Fb3); lia.
  - intros a Ha. rewrite crt102rw_fb in Ha. exact (proj1 (Ffr' a Ha)). }
{ intros k Hk. unfold CRT_SP_F in *. rewrite Kmb; [exact (HSPF k Hk) | lia |].
  apply (crt102rw_nw_stack F _ ltac:(lia) ltac:(lia)); lia. }
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr. apply K; [unfold SHADOW_OFF; lia|].
  intros [Hw | Hw]; [|unfold SHADOW_OFF in *; pose proof (YM05.alloc_ceiling_val); lia].
  unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_mod F 32 ltac:(lia)).
  assert (F / 8 + 28 <= y / 8) by (apply Z.div_le_lower_bound; lia). lia. }
{ intros s Hs. pose proof (YM05.alloc_ceiling_val).
  rewrite K; [exact (HCH s Hs) | unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *; lia |].
  intros [Hw | Hw]; unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *; lia. }
Qed.

(* ---- the frame-pointer chain a callee of check_round_trip is given (H5CrtS1.v crt_chain's argument, at the glue's
   crt_saved and the journal's keep above the entry sp) ---- *)
Lemma crt102rw_fpchain_keep : forall (r1 r2 : reader) lo top ch0 bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch0 -> fpchain (rdword r2) bp top ch0.
Proof.
intros r1 r2 lo top ch0. induction ch0 as [|[[fp ra] nfp] ch0 IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r. rewrite (Hkeep (bp - 8)) by lia. auto.
- cbn [fpchain] in *. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite (Hkeep (fp - 8)) by lia; exact E3|].
  split; [rewrite (Hkeep (fp - 16)) by lia; exact E4|].
  split; [exact E5|].
  destruct (bad_next fp top nfp) eqn:Eb; [exact E6|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb1 _].
  apply orb_false_iff in Eb1 as [Eb11 Eb12]. apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12.
  apply (IH nfp Hkeep); [lia | lia | exact E6].
Qed.

Lemma crt102rw_chain : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc sp2 {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  sp0 - 256 <= sp2 <= sp0 - 16 ->
  exists ch1, achain lyc (aview SEGS (w_H Wc) memc) sp2 sp0 ch1 /\
    (ch1 = [] \/ ch1 = (sp0, raZ regs, s0Z regs) :: ch).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc sp2 kbg HL Hsp2.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_saved HL) as HSV.
pose proof HPRE as ((HAR0 & Hra & Hra4 & _ & _ & Hstk & _ & Hch & _) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof (YM05.alloc_ceiling_val) as Hc.
assert (H8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (HSV 0%nat ltac:(lia)) as Hw1. pose proof (HSV 1%nat ltac:(lia)) as Hw8.
cbn [nth CRT_SAVED Z.of_nat] in Hw1, Hw8.
replace (sp0 - 8 * (0 + 1)) with (sp0 - 8) in Hw1 by lia.
replace (sp0 - 8 * (1 + 1)) with (sp0 - 16) in Hw8 by lia.
assert (R1 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 8) = Some (raZ regs)).
{ apply crt102rw_rdword_of_vm; [exact Hw1 | exact (bv_unsigned_in_range 64 (getr regs 1))]. }
assert (R8 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 16) = Some (s0Z regs)).
{ apply crt102rw_rdword_of_vm; [exact Hw8 | exact (bv_unsigned_in_range 64 (getr regs 8))]. }
destruct (Z_le_gt_dec (ly_top lyc - 16) sp0) as [Hbad|Hgood].
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hbad | reflexivity].
- exists ((sp0, raZ regs, s0Z regs) :: ch). split; [|right; reflexivity]. right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, sp0 <= a -> a < ly_top ly ->
            rdword (aview SEGS (w_H Wc) memc) a = rdword (aview SEGS (w_H W) mem) a).
  { intros a Ha Hat. apply ts_rdword_keep. intros j Hj. apply F1; lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact R1|]. split; [exact R8|]. split; [exact Hra4|].
    destruct (bad_next sp0 (ly_top lyc) (s0Z regs)) eqn:Eb.
    * destruct Hch as [[_ Hnil] | (Hge & Hlt & Hm8 & _ & _)]; [exact Hnil|].
      exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_true_iff in Eb as [Eb1 | Eb2].
      { apply orb_true_iff in Eb1 as [Eb11 | Eb12]; [apply Z.leb_le in Eb11 | apply Z.leb_le in Eb12]; lia. }
      { apply negb_true_iff, Z.eqb_neq in Eb2. exact (Eb2 Hm8). }
    * destruct Hch as [[Hb _] | (Hge & Hlt & Hm8 & Hfp & _)].
      { exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
        apply orb_false_iff in Eb as [Eb1 Eb2]. apply orb_false_iff in Eb1 as [Eb11 Eb12].
        apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12. apply negb_false_iff, Z.eqb_eq in Eb2.
        destruct Hb as [Hb | [Hb | Hb]]; lia. }
      rewrite Etop. apply (crt102rw_fpchain_keep (aview SEGS (w_H W) mem) (aview SEGS (w_H Wc) memc) sp0);
        [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbv beta. intros y Hy. lia.
Qed.

(* ---- a byte of a live harness block, or of a tree whose blocks are harness blocks, is application memory below
   alloc_ceiling, so no run of this slice writes it ---- *)
Lemma crt102rw_lam_app : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k y {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  In (a, k) Lamc -> a <= y < a + k -> 4096 <= y < YM05.alloc_ceiling /\ in_app y 1.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc a k y kbg HL Hk Hy.
destruct (crt_live_journal HL) as (? & (HARc & _) & _).
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc a k _ _ HLED Hk) as (Hk0 & Hab & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in *.
assert (Hrs : k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
split; [lia|]. apply (in_app_sub _ _ _ _ Bapp); lia.
Qed.
Lemma crt102rw_foot_nw : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc D' p y {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall bk, In bk D' -> In bk Lamc) ->
  frame_addr lyc CRT_CID pos <= p -> p + 56 <= frame_addr lyc CRT_CID pos + 512 ->
  pj_footR p D' y -> 0 <= y < 2 ^ 64 /\ ~ crt102rw_wr (frame_addr lyc CRT_CID pos) y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc D' p y kbg HL HD Hp1 Hp2 Hy.
destruct (crt_live_journal HL) as (WSj & HJ & HBj).
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- split; [lia|]. apply crt102rw_nw_app; [lia | lia | apply (in_app_sub _ _ _ _ Fb3); lia | lia].
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (crt102rw_lam_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ b kb y HL (HD _ Hb) Hy) as (H1 & H2).
  split; [lia|]. apply crt102rw_nw_app; [lia | lia | exact H2 | lia].
Qed.

(* ---- bytes outside the image that the journal's view keeps are the same bytes, writability included ---- *)
Lemma crt102rw_mr_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H' m' a = aview SEGS H m a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. unfold aview, mbyte in E.
rewrite (seg_rom_none SEGS a Ha Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 a)) as [b'|]; destruct (mrestrict H m (Z_to_bv 64 a)) as [b|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma crt102rw_agree_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) (X : Z -> Prop),
  (forall x, X x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS H' m' x = aview SEGS H m x) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H' m') X.
Proof.
intros H H' m m' X HX y Hy. destruct (HX y Hy) as (Hr & Hn & E).
pose proof (crt102rw_mr_of_aview H H' m m' y Hr Hn E) as Em.
split; [unfold mbyte; rewrite Em; reflexivity|].
intros Hw. unfold writable_at, wview in *. rewrite Em. exact Hw.
Qed.

(* ---- THE LIVE STATE ACROSS A CALL: the callee's journal (from this function's state, at its sp sp1) keeps the saved
   words, the spills, the frame's flag word and copy's shadow; the caller supplies the new side facts and blocks ---- *)
Lemma crt102rw_live_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
  STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Dx' Lamc' peakc' cntc' ownc' ranc' {kbg kbg' : nat} {WS1 : list (list Z)},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (exists WS2, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS2 /\
     YCbqGwild.wbudget [] kbg' WS2) ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  0 <= STK1 ->
  (forall a, inFP FP1 a -> a < YM05.alloc_ceiling /\ in_app a 1 /\
     ~ (frame_addr lyc CRT_CID pos + 504 <= a < frame_addr lyc CRT_CID pos + 512)) ->
  crt_side (rc := rc) (PI := prh_img_A) (RL := RL) (L := A_prog_listing) (PA := PA) (B := B) (doc := doc) (t := t)
    (D := D) (peak := peak) (most := most) ly2 S2 Hp2 W2 mem2 Lamc' peakc' cntc' ownc' ranc' ->
  Permutation Lamc' (Dx' ++ Lam) -> Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dx') ->
  (forall bk, In bk Dx' -> ~ In bk D) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  liveA kbg' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dx' Lamc' peakc' cntc' ownc' ranc'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Dx' Lamc'
  peakc' cntc' ownc' ranc' kbg kbg' WS1 HL (WS2 & HJ2 & HB2) HJ1 HSTK1 HFP HSD HPL HPB HAP HMN'.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMN. clear HL.
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ2) as (_ & _ & _ & _ & _ & Ffr2 & Fsh2).
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & KS1 & _ & _ & KF1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos) by (unfold frame_addr; rewrite EFF; reflexivity).
assert (EFl : flag_addr ly2 CRT_CID pos = flag_addr lyc CRT_CID pos) by (unfold flag_addr; rewrite EFF; reflexivity).
rewrite EF in Ffr2, Fsh2.
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof crt102rw_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the stack above the callee's window is kept *)
assert (KS : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply KS1; lia. }
(* the own frame's bytes and shadow are kept outside FP1 *)
assert (KF : forall a, (F <= a < F + 512 \/ shadow_addr F <= a < shadow_addr F + 64) -> ~ inFP FP1 a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply (KF1 CRT_CID pos a Hin); [|exact Hn].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite crt102rw_fb. change (512 / 8) with 64. fold F. lia. }
assert (KSH : forall a, shadow_addr F <= a < shadow_addr F + 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply KF; [right; exact Ha|]. intros Hf. destruct (HFP a Hf) as (H1 & H2 & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia. }
refine {| crt_live_journal := ex_intro _ WS2 (conj HJ2 HB2); crt_live_side := HSD; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB;
          crt_live_dx_apart := HAP; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _;
          crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := _ |}.
{ intros j Hj. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact (HSV j Hj)].
  intros i Hi. apply KS. lia. }
{ pose proof (crt_frame_flag_word HFRM) as Hfl.
  refine {| crt_frame_listed := _; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - pose proof HJ2 as (_ & _ & _ & _ & _ & HFR2 & _). rewrite HFR2. left. reflexivity.
  - rewrite EF, EFl, <- Hfl. apply ts_rdword_keep. intros j Hj. rewrite crt102rw_fb. fold F.
    apply KF; [left; lia|]. intros Hf. destruct (HFP _ Hf) as (_ & _ & H3). apply H3. lia.
  - intros a Ha. rewrite EF, crt102rw_fb in Ha. fold F in Ha. exact (proj1 (Ffr2 a Ha)). }
{ unfold crt_spill in *. rewrite EF. fold F.
  apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact HSPF].
  intros i Hi. apply KS. unfold CRT_SP_F. lia. }
{ rewrite EF. fold F. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr. apply KSH.
  unfold shadow_addr, SHADOW_OFF in *. lia. }
{ rewrite EF. fold F. intros s Hs. pose proof (YM05.alloc_ceiling_val). rewrite KSH; [exact (HCH s Hs)|].
  unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *. lia. }
intros H0. exact (HMN' (HMN H0)).
Qed.

(* ---- the return site of a call this slice makes: a text address of check_round_trip, below the ceiling ---- *)
Lemma crt102rw_ret : forall off, 0 <= off < 2048 -> off mod 2 = 0 ->
  4096 <= BASE + (CRT_PC_A + off) < 2 ^ 31 /\ (CRT_PC_A + off) mod 2 = 0 /\ 0 <= CRT_PC_A + off < 2 ^ 40.
Proof.
intros off H1 H2. rewrite crt102rw_pc.
assert (HB : 4096 <= BASE < 2 ^ 30) by (split; vm_compute; first [discriminate | reflexivity]).
split; [lia|]. split; [|lia]. rewrite Z.add_mod by lia. rewrite H2. reflexivity.
Qed.

(* ---- A CALL FROM check_round_trip AT THE REALIGNED sp (the model is Crt102Arms.v's arms_rtt_call, generalised over the
   callee): the live state with the jal next, the kept registers, the return site, the callee's budget and footprint.
   The callee's text is supplied at the fpre the call establishes, in the float form (a callee whose text leaves the
   float state alone gives it by apost_base_x_F); the continuation receives both journals, the kept registers, the
   float state the callee left and the callee's Q.
   The re-hiding move: the callee's text at RZW (SRr' with apost_base_xFR at RZW = PRH_Base's
   fpostF; a plain text by crt102rw_lift_xF / crt102rw_lift_x), both journals of the continuation at RZW, the walk in
   SRr'; the rule is YCbqGwild.aj_call_xbFR at RZW under YSRrG.SRr'_bind. ---- *)
Lemma crt102rw_call : forall (fxk : YK11.FPState) STK1 FP1 (off pcc : Z) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc
    peakc cntc ownc ranc Q {kbg : nat},
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = pcc ->
  bv_unsigned (ew E 2) = sp0 ->
  liveA kbg lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  bregsA (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  0 <= STK1 -> STK1 + 240 <= STKC ->
  fp_sub_x B STKC sp0 [] FP1 ly S [(CRT_CID, pos)] lyc Sc ->
  (forall ch1, fpre (fx := fxk) B ARx STK1 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
       (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 pcc) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
       (apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx RZW STK1 FP1 (ms_regs ms) lyc Sc Hpc Wc (ms_mem ms) mdc Q)) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
        YCbqGwild.wbudget [] kbg WS) ->
     AJ STK1 sp1 FP1 lyc Sc Hpc Wc (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + off))) mem2 (YK11.seg_rom SEGS)) md2) QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk STK1 FP1 off pcc Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ownc ranc Q kbg HFZ HS Hrv Hpcs HE2 HL
  HBR Hra Hoff Hoff2 HSTK0 HSTK1 HFP Hcallee HK.
destruct (crt_live_journal HL) as (WS0 & HJ & HB0). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof crt102rw_sp as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & Hs0).
pose proof HJ as (HARc & HLYc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (crt102rw_ret off Hoff Hoff2) as (Hr1 & Hr2 & Hr3).
destruct (crt102rw_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp1 HL ltac:(lia)) as (ch1 & Hch1 & _).
set (o := sp1 - sp0).
assert (Hspz : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspc : getr (ms_regs ms) 2 = sv_denot E (SOff 2 o)).
{ apply bv_eq. rewrite denot_SOff, HE2, R2. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite YP0m.zcanon_small by (unfold o; lia). unfold o. lia. }
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_A + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ (* the caller's journal is at its budget WS0 (crt_live's kb journal): the budgeted call rule at RZW at the callee's
     empty budget, P := (fun WS1 => WS1 = []), the callee's text by YCbqGwild.apost_base_xbF_of_xR *)
  refine (@YCbqGwild.aj_call_xbFR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low rc A_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms
    STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdc kj WS0 STK1 FP1 o (ew E 2) (getr (ms_regs ms) 1) ch1
    (fun WS1 => WS1 = []) Q HS Hrv HJ Hspc eq_refl HE2 _ _ HSTK0 _ _ _ eq_refl _ _ _ _ HFP).
  - unfold o. apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q Hq]. apply Z.mod_divide in Hs32; [|lia].
    destruct Hs32 as [q' Hq']. apply Z.mod_divide; [lia|]. exists (2 * q' - q). lia.
  - unfold o. lia.
  - unfold o. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + o) with sp1 by (unfold o; lia). rewrite Hs0z. exact Hch1.
  - intros HPRE1. rewrite Hpcs. eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    + apply (Hcallee ch1). split; [exact HPRE1|]. split; [exact HRO|].
      split; [rewrite Hspz, Eshi; lia|]. split; [rewrite Hraz; lia | exact HFZ].
    + intros W' c' _ Hpo. apply YCbqGwild.apost_base_xbF_of_xR; [reflexivity | exact Hpo]. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW & HJ2 & HJ1 &
  HP & HQ).
subst WS1. rewrite app_nil_r in HJ2.
replace (sp0 + o) with sp1 in HJ1 by (unfold o; lia).
rewrite Hra. exact (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 (ex_intro _ WS0 (conj HJ2 HB0)) HJ1 HP HQ).
Qed.

(* ---- crt102rw_call for a callee whose text posts a BUDGETED journal (kb round; tparse_noting_specX's fpostFbm ..
   (wbudget [] (prh_wk F_parse_noting)), PRH_FnCheck.v:649): the callee's text in apost_base_xbF (wbudget [] kw)
   (fpostFbm unfolds to it), over YCbqGwild.aj_call_xbF; the continuation receives the caller's journal at WS0 ++ WS1
   (WS0 the live state's, wbudget [] kbg WS0; WS1 the callee's, wbudget [] kw WS1) and the callee's journal at WS1;
   the caller's landing at a boundary budget is the call site's (Crt102Rewrite.crt102rw_wild_budget_pn).
   The re-hiding move: the callee's text is SRr' with apost_base_xbFR at RZW (PRH_Base's
   fpostFb / fpostFbm at wle', exactly the texts' form), the rule YCbqGwild.aj_call_xbFR at RZW, the walk in SRr'. ---- *)
Lemma crt102rw_call_b : forall (fxk : YK11.FPState) STK1 FP1 (off pcc : Z) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc
    peakc cntc ownc ranc (kw : nat) Q {kbg : nat},
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = pcc ->
  bv_unsigned (ew E 2) = sp0 ->
  liveA kbg lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  bregsA (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  0 <= STK1 -> STK1 + 240 <= STKC ->
  fp_sub_x B STKC sp0 [] FP1 ly S [(CRT_CID, pos)] lyc Sc ->
  (forall ch1, fpre (fx := fxk) B ARx STK1 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
       (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 pcc) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
       (YCbqGwild.apost_base_xbFR (fx := fxk) (SK := SK) SEGS B PST ARx RZW (YCbqGwild.wbudget [] kw) STK1 FP1
          (ms_regs ms) lyc Sc Hpc Wc (ms_mem ms) mdc Q)) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS0 WS1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     YCbqGwild.wbudget [] kbg WS0 -> YCbqGwild.wbudget [] kw WS1 ->
     AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) (WS0 ++ WS1) ->
     AJW STK1 sp1 FP1 lyc Sc Hpc Wc (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
     aregs_preserved (ms_regs ms) regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + off))) mem2 (YK11.seg_rom SEGS)) md2) QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk STK1 FP1 off pcc Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ownc ranc kw Q kbg HFZ HS Hrv Hpcs HE2 HL
  HBR Hra Hoff Hoff2 HSTK0 HSTK1 HFP Hcallee HK.
destruct (crt_live_journal HL) as (WS0 & HJ & HB0). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof crt102rw_sp as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & Hs0).
pose proof HJ as (HARc & HLYc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (crt102rw_ret off Hoff Hoff2) as (Hr1 & Hr2 & Hr3).
destruct (crt102rw_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp1 HL ltac:(lia)) as (ch1 & Hch1 & _).
set (o := sp1 - sp0).
assert (Hspz : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspc : getr (ms_regs ms) 2 = sv_denot E (SOff 2 o)).
{ apply bv_eq. rewrite denot_SOff, HE2, R2. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite YP0m.zcanon_small by (unfold o; lia). unfold o. lia. }
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_A + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ (* the caller's journal is at its budget WS0 (crt_live's kb journal): the budgeted call rule at RZW at the callee
     text's budget P *)
  refine (@YCbqGwild.aj_call_xbFR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low rc A_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms
    STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdc kj WS0 STK1 FP1 o (ew E 2) (getr (ms_regs ms) 1) ch1
    (YCbqGwild.wbudget [] kw) Q HS Hrv HJ Hspc eq_refl HE2 _ _ HSTK0 _ _ _ eq_refl _ _ _ _ HFP).
  - unfold o. apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q Hq]. apply Z.mod_divide in Hs32; [|lia].
    destruct Hs32 as [q' Hq']. apply Z.mod_divide; [lia|]. exists (2 * q' - q). lia.
  - unfold o. lia.
  - unfold o. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + o) with sp1 by (unfold o; lia). rewrite Hs0z. exact Hch1.
  - intros HPRE1. rewrite Hpcs. apply (Hcallee ch1). split; [exact HPRE1|]. split; [exact HRO|].
    split; [rewrite Hspz, Eshi; lia|]. split; [rewrite Hraz; lia | exact HFZ]. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW & HJ2 & HJ1 &
  HP & HQ).
replace (sp0 + o) with sp1 in HJ1 by (unfold o; lia).
rewrite Hra. exact (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 WS0 WS1 HFZ2 HFK2 HB0 HPW HJ2 HJ1 HP HQ).
Qed.

(* ---- A LOCAL OF check_round_trip's CLASS-3 FRAME AS A CALLEE'S pj SLOT (back F + 0x20, v F + 0x80, copy F + 0xe0):
   a fake frame of frames Sc (prhReader_at's third case), 8-aligned, present hence writable, application memory, not
   the allocator's, below the callee's stack window, addressable with a visible hull (the caller supplies the last two
   from the frame's shadow) ---- *)
Lemma crt102rw_frame_slot : forall lyc Sc Hpc Wc memc mdc kj pos (STK1 d off : Z) (rgc : bvmap 5 word) Lamc
    {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  spZ rgc = sp1 -> 0 <= STK1 -> STK1 + 240 <= STKC ->
  0 <= off -> off + 56 <= 512 -> off mod 8 = 0 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + off) 56 ->
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (frame_addr lyc CRT_CID pos + off) 56 ->
  PRH_FnPj.prhPj_slot B STK1 d lyc Sc Lamc Wc rgc memc (frame_addr lyc CRT_CID pos + off).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos STK1 d off rgc Lamc WS HJ Hsp HS0 HS1 Ho0 Ho1 Ho8 HRA HHV.
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof crt102rw_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof crt102rw_stkc as ESTK.
pose proof (YM05.alloc_ceiling_val) as Hcv.
set (F := frame_addr lyc CRT_CID pos) in *.
unfold PRH_FnPj.prhPj_slot.
split; [lia|].
split; [right; right; left; exists CRT_CID, pos; split; [exact Hin|]; rewrite crt102rw_fb; fold F; lia|].
split.
{ split; [pose proof (Z.div_mod F 32 ltac:(lia)); apply Z.mod_divide in Ho8; [|lia]; destruct Ho8 as [q Hq];
    apply Z.mod_divide; [lia|]; exists (4 * (F / 32) + q); lia|].
  intros y Hy. apply (apresent_writable SEGS). exact (proj1 (Ffr y ltac:(lia))). }
split.
{ unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
split.
{ intros y Hy. split; [exact (proj2 (Ffr y ltac:(lia)))|]. rewrite Hsp. lia. }
split; [exact HRA | exact HHV].
Qed.

(* ---- crt102rw_call with the shape of the chain the callee is given (the free calls need it for their trace).
   At RZW / SRr', as crt102rw_call ---- *)
Lemma crt102rw_call_ch : forall (fxk : YK11.FPState) STK1 FP1 (off pcc : Z) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc
    peakc cntc ownc ranc Q {kbg : nat},
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = pcc ->
  bv_unsigned (ew E 2) = sp0 ->
  liveA kbg lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  bregsA (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  0 <= STK1 -> STK1 + 240 <= STKC ->
  fp_sub_x B STKC sp0 [] FP1 ly S [(CRT_CID, pos)] lyc Sc ->
  (forall ch1, (ch1 = [] \/ ch1 = (sp0, raZ regs, s0Z regs) :: ch) ->
     fpre (fx := fxk) B ARx STK1 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
       (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 pcc) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
       (apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx RZW STK1 FP1 (ms_regs ms) lyc Sc Hpc Wc (ms_mem ms) mdc Q)) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
        YCbqGwild.wbudget [] kbg WS) ->
     AJ STK1 sp1 FP1 lyc Sc Hpc Wc (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + off))) mem2 (YK11.seg_rom SEGS)) md2) QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk STK1 FP1 off pcc Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ownc ranc Q kbg HFZ HS Hrv Hpcs HE2 HL
  HBR Hra Hoff Hoff2 HSTK0 HSTK1 HFP Hcallee HK.
destruct (crt_live_journal HL) as (WS0 & HJ & HB0). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof crt102rw_sp as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & Hs0).
pose proof HJ as (HARc & HLYc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (crt102rw_ret off Hoff Hoff2) as (Hr1 & Hr2 & Hr3).
destruct (crt102rw_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp1 HL ltac:(lia)) as (ch1 & Hch1 & Ech1).
set (o := sp1 - sp0).
assert (Hspz : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspc : getr (ms_regs ms) 2 = sv_denot E (SOff 2 o)).
{ apply bv_eq. rewrite denot_SOff, HE2, R2. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite YP0m.zcanon_small by (unfold o; lia). unfold o. lia. }
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_A + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ (* the caller's journal is at its budget WS0 (crt_live's kb journal): the budgeted call rule at RZW at the callee's
     empty budget, P := (fun WS1 => WS1 = []), the callee's text by YCbqGwild.apost_base_xbF_of_xR *)
  refine (@YCbqGwild.aj_call_xbFR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low rc A_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms
    STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdc kj WS0 STK1 FP1 o (ew E 2) (getr (ms_regs ms) 1) ch1
    (fun WS1 => WS1 = []) Q HS Hrv HJ Hspc eq_refl HE2 _ _ HSTK0 _ _ _ eq_refl _ _ _ _ HFP).
  - unfold o. apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q Hq]. apply Z.mod_divide in Hs32; [|lia].
    destruct Hs32 as [q' Hq']. apply Z.mod_divide; [lia|]. exists (2 * q' - q). lia.
  - unfold o. lia.
  - unfold o. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + o) with sp1 by (unfold o; lia). rewrite Hs0z. exact Hch1.
  - intros HPRE1. rewrite Hpcs. eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    + apply (Hcallee ch1 Ech1). split; [exact HPRE1|]. split; [exact HRO|].
      split; [rewrite Hspz, Eshi; lia|]. split; [rewrite Hraz; lia | exact HFZ].
    + intros W' c' _ Hpo. apply YCbqGwild.apost_base_xbF_of_xR; [reflexivity | exact Hpo]. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW & HJ2 & HJ1 &
  HP & HQ).
subst WS1. rewrite app_nil_r in HJ2.
replace (sp0 + o) with sp1 in HJ1 by (unfold o; lia).
rewrite Hra. exact (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 (ex_intro _ WS0 (conj HJ2 HB0)) HJ1 HP HQ).
Qed.

(* ---- a block the walk holds beyond the entry's is a live allocator block that was not live at entry (the sep law:
   no live block occurs twice) ---- *)
Definition crt102rw_zz_dec : forall x0 y0 : Z * Z, {x0 = y0} + {x0 <> y0}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma crt102rw_count2 : forall (l : list (Z * Z)) z, (2 <= count_occ crt102rw_zz_dec l z)%nat ->
  exists la lb lc, l = la ++ z :: lb ++ z :: lc.
Proof.
intros l z. induction l as [|y l IH]; intros H; cbn in H; [lia|].
destruct (crt102rw_zz_dec y z) as [<-|Hne].
- assert (H1 : (1 <= count_occ crt102rw_zz_dec l y)%nat) by lia.
  apply count_occ_In in H1. apply in_split in H1 as (lb & lc & ->). exists [], lb, lc. reflexivity.
- destruct (IH H) as (la & lb & lc & ->). exists (y :: la), lb, lc. reflexivity.
Qed.
Lemma crt102rw_fresh : forall lyc Sc Hpc Wc memc mdc Dx a k,
  ARx lyc Sc Hpc Wc memc mdc -> Permutation (ablocks B lyc Sc) (ablocks B ly S ++ ck_hblks Dx) -> In (a, k) Dx ->
  0 <= k ->
  In (a - cf_head, k + cf_head) (ablocks B lyc Sc) /\ ~ In (a - cf_head, k + cf_head) (ablocks B ly S).
Proof.
intros lyc Sc Hpc Wc memc mdc Dx a k HAR HP Hin Hk.
assert (Hh : In (a - cf_head, k + cf_head) (ck_hblks Dx)) by (unfold ck_hblks; apply (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Dx (a, k)); exact Hin).
split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hh|].
intros H0. pose proof (proj1 (Permutation_count_occ crt102rw_zz_dec _ _) HP (a - cf_head, k + cf_head)) as Hc.
rewrite count_occ_app in Hc.
pose proof (proj1 (count_occ_In crt102rw_zz_dec _ _) H0).
pose proof (proj1 (count_occ_In crt102rw_zz_dec _ _) Hh).
destruct (crt102rw_count2 (ablocks B lyc Sc) (a - cf_head, k + cf_head) ltac:(lia)) as (la & lb & lc & El).
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HAR) as (Hsep & _). rewrite El in Hsep.
apply pairwise_app_l in Hsep as [Hsep _]. rewrite map_app in Hsep. apply pairwise_app_l in Hsep as [_ Hsep].
cbn [map pairwise] in Hsep. destruct Hsep as (Hf & _). rewrite map_app, Forall_app in Hf. destruct Hf as (_ & Hf).
cbn [map] in Hf. inversion Hf as [|? ? Hd _]. unfold zdisjoint in Hd. cbv beta in Hd. cbn [fst snd] in Hd.
assert (Hk16 : 0 <= k + cf_head) by (pose proof (@cf_head_nonneg CfParams_preset); lia).
pose proof (req_size_pos (k + cf_head) Hk16) as Hrs. change (@cf_head CfParams_preset) with 16 in *. lia.
Qed.

(* ---- the free call's trace from check_round_trip: the return site's prh_trace at the observed context (the chain
   the call is given is check_round_trip's own record on top of its entry chain, or empty) ---- *)
Lemma crt102rw_free_trace : forall lyc rgc ch1 r,
  spZ rgc + 16 < ly_top lyc -> raZ rgc = r -> s0Z rgc = sp0 -> 0 <= r ->
  (ch1 = [] \/ ch1 = (sp0, raZ regs, s0Z regs) :: ch) ->
  In r (pi_ret_sites F_check_round_trip RT_fuzz_free) ->
  In (call_trace lyc (pc_free_ra0 (as_code B)) rgc ch1) (as_universe B).
Proof.
intros lyc rgc ch1 r Htop Hra Hs0 Hr0 Hch Hr.
unfold call_trace, frame0_ok. rewrite (proj2 (Z.ltb_lt _ _) Htop).
assert (E : forall l, unwind_of_chain (pc_free_ra0 (as_code B)) ((spZ rgc, raZ rgc, s0Z rgc) :: l) =
  prh_trace (prh_pc0 B RT_fuzz_free) r (spine l)).
{ intros l. unfold unwind_of_chain, prh_trace, prh_pc0. rewrite Hra. f_equal. f_equal.
  cbn [flat_map]. f_equal. induction l as [|[[fp ra] nfp] l IH]; [reflexivity|]. cbn [flat_map spine map fst snd].
  rewrite IH. reflexivity. }
rewrite E.
destruct Hch as [-> | ->].
- exact (prh_univ_closure_lit B CTX0 F_check_round_trip RT_fuzz_free r HCL Hr).
- cbn [spine map fst snd]. apply (prh_univ_closure_site B CTX0 F_check_round_trip); [exact HCL | exact HCTX | |exact Hr].
  vm_compute. reflexivity.
Qed.

(* ---- WHAT A CALL KEEPS OF check_round_trip's OWN STATE: the frame's address, the stack above the callee's window
   (the saves and the spills), and the frame's shadow (the callee's footprint is application memory) ---- *)
Lemma crt102rw_call_keep : forall lyc Sc Hpc Wc memc mdc kj pos STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    {WS WS1 : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, inFP FP1 a -> a < YM05.alloc_ceiling /\ in_app a 1) ->
  frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos /\
  (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall a, shadow_addr (frame_addr lyc CRT_CID pos) <= a < shadow_addr (frame_addr lyc CRT_CID pos) + 64 ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 WS WS1 HJ HJ1 HFP.
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & KS1 & _ & _ & KF1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt102rw_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
split; [unfold frame_addr; rewrite EFF; reflexivity|].
split; [intros a Ha; apply KS1; lia|].
intros a Ha. apply (KF1 CRT_CID pos a Hin).
- unfold in_zr, frame_rng. cbn [fst snd]. rewrite crt102rw_fb. change (512 / 8) with 64. fold F. lia.
- intros Hf. destruct (HFP a Hf) as (H1 & H2).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia.
Qed.
Lemma crt102rw_spill_keep : forall (Wc W2 : world SEGS) (memc mem2 : word -> option byte) off v,
  (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) -> 0 <= off -> off + 8 <= 240 ->
  crt_spill (regs := regs) Wc memc off v -> crt_spill (regs := regs) W2 mem2 off v.
Proof.
intros Wc W2 memc mem2 off v KS Ho0 Ho1 H. unfold crt_spill in *.
pose proof crt102rw_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact H].
intros i Hi. apply KS. lia.
Qed.
Lemma crt102rw_local_keep : forall (Wc W2 : world SEGS) (memc mem2 : word -> option byte) F off,
  0 <= F -> F mod 32 = 0 -> F + 512 <= YM05.alloc_ceiling ->
  (forall a, shadow_addr F <= a < shadow_addr F + 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  32 <= off -> off <= 400 ->
  (range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + off) 56 ->
   range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (F + off) 56) /\
  (shadow_hull_vis (aview SEGS (w_H Wc) memc) (F + off) 56 -> shadow_hull_vis (aview SEGS (w_H W2) mem2) (F + off) 56).
Proof.
intros Wc W2 memc mem2 F off HF0 F32 HF KSH Ho0 Ho1.
pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite F32, Z.add_0_r in DF.
assert (F8 : F / 8 = 4 * (F / 32)) by (symmetry; apply Z.div_unique with 0; lia).
assert (Eo : forall j, 0 <= j -> (F + j) / 8 = F / 8 + j / 8).
{ intros j Hj. rewrite F8. replace (F + j) with (j + (4 * (F / 32)) * 8) by lia. rewrite Z.div_add by lia. lia. }
split.
- intros H. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact H].
  intros y Hy. unfold shadow_of_addr. apply KSH. unfold shadow_addr.
  replace y with (F + (y - F)) by lia. rewrite (Eo (y - F)) by lia.
  pose proof (Z.div_le_upper_bound (y - F) 8 63 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (y - F) 8 ltac:(lia) ltac:(lia)).
  lia.
- intros H s0 Hs0. rewrite KSH; [exact (H s0 Hs0)|]. unfold shadow_addr in *.
  replace (F + off + 56 - 1) with (F + (off + 56 - 1)) in Hs0 by lia.
  rewrite (Eo off) in Hs0 by lia. rewrite (Eo (off + 56 - 1)) in Hs0 by lia.
  set (q := SHADOW_OFF + F / 8 + off / 8) in *.
  set (q' := SHADOW_OFF + F / 8 + (off + 56 - 1) / 8) in *.
  replace (SHADOW_OFF + (F / 8 + off / 8)) with q in Hs0 by (unfold q; lia).
  replace (SHADOW_OFF + (F / 8 + (off + 56 - 1) / 8)) with q' in Hs0 by (unfold q'; lia).
  pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  pose proof (Z.div_mod q' 8 ltac:(lia)). pose proof (Z.mod_pos_bound q' 8 ltac:(lia)).
  pose proof (Z.div_mod off 8 ltac:(lia)). pose proof (Z.mod_pos_bound off 8 ltac:(lia)).
  pose proof (Z.div_mod (off + 56 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (off + 56 - 1) 8 ltac:(lia)).
  unfold q, q', SHADOW_OFF in *. rewrite F8 in *. lia.
Qed.



(* ---- A LOCAL OF THE CLASS-3 FRAME IS OFF A TREE whose root is apart from it and whose blocks are harness blocks (the
   frame and the allocator's blocks are apart: the sep law) ---- *)
Lemma crt102rw_local_off_blocks : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off Dt a {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall bk, In bk Dt -> In bk Lamc) -> 0 <= off -> off + 56 <= 512 ->
  frame_addr lyc CRT_CID pos + off <= a < frame_addr lyc CRT_CID pos + off + 56 ->
  ~ (exists b, In b Dt /\ pj_holdsR b a).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off Dt a kbg HL HDt Ho0 Ho1 Ha ((b & kb) & Hb & Hf).
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ) as (Hin & _).
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDt _ Hb)) as (Hk0 & Hab & _).
pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hab Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite crt102rw_fb in Hd. unfold pj_holdsR in Hf. cbn [fst snd] in Hf.
change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb + 16) ltac:(lia)). lia.
Qed.
Lemma crt102rw_local_off_tree : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off q Dt a {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (forall bk, In bk Dt -> In bk Lamc) -> 0 <= off -> off + 56 <= 512 ->
  q + 56 <= frame_addr lyc CRT_CID pos + off \/ frame_addr lyc CRT_CID pos + off + 56 <= q ->
  frame_addr lyc CRT_CID pos + off <= a < frame_addr lyc CRT_CID pos + off + 56 -> ~ pj_footR q Dt a.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off q Dt a kbg HL HDt Ho0 Ho1 Hq Ha [Hf | Hb]; [lia|].
exact (crt102rw_local_off_blocks lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off Dt a HL HDt Ho0 Ho1 Ha
  Hb).
Qed.

(* ---- a local of the class-3 frame is off the document's footprint: doc lies in a frame of the entry, which is apart
   from the frame this function took (the sep law over frames), and doc's blocks are allocator blocks ---- *)
Lemma crt102rw_local_off_doc : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off a {kbg : nat},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> 0 <= off -> off + 56 <= 512 ->
  frame_addr lyc CRT_CID pos + off <= a < frame_addr lyc CRT_CID pos + off + 56 -> ~ pj_footR doc D a.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off a kbg HL Ho0 Ho1 Ha.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_side_doc_blocks (crt_live_side HL)) as HDL.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & _ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR HLYc) as (_ & Efa & _).
intros [Hf | Hb].
- destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HARc) as (Hsep & _).
  apply pairwise_app_l in Hsep as [_ Hsep]. rewrite HFRc in Hsep. cbn [app map pairwise] in Hsep.
  destruct Hsep as (Hsep & _). rewrite Forall_map in Hsep.
  pose proof (proj1 (Forall_forall _ _) Hsep (cid, pos') Hfin) as Hd. cbn [fst snd] in Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (Efa cid pos') in Hd. rewrite crt102rw_fb in Hd. lia.
- exact (crt102rw_local_off_blocks lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc off D a HL HDL Ho0 Ho1
    Ha Hb).
Qed.

(* ---- A TREE ACROSS A CALL: a node in a fake frame of Sc whose blocks are harness blocks before and after, off the
   callee's footprint, is the same tree after the call (the journal keeps frame bytes and live blocks off FP) ---- *)
Lemma crt102rw_tree_call : forall lyc Sc Hpc Wc memc mdc (kj : Z) STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p t' Dt {WS1 : list (list Z)},
  ARx lyc Sc Hpc Wc memc mdc ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  forall {mo1 ow1 mo2 ow2 : Z},
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc mo1 ow1 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 mo2 ow2 ->
  (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= p /\
     p + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) ->
  (forall bk, In bk Dt -> In bk Lamc) -> (forall bk, In bk Dt -> In bk Lam2) ->
  (forall a, inFP FP1 a -> ~ pj_footR p Dt a) ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) p t' Dt ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) p t' Dt.
Proof.
intros lyc Sc Hpc Wc memc mdc kj STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p t' Dt
  WS1 HARc HJ1 mo1 ow1 mo2 ow2 HLED HLED2 (cid & pos' & Hfin' & Hfa1 & Hfa2) HDL HDL2 HFPD HND.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _).
apply (crt102rw_nodeR_lblk SEGS t' _ (prh_lin Lamc) (prh_lin Lam2) p Dt); [|intros x0 k0 H0; exact (HDL2 _ H0)].
apply (pj_nodeR_frame SEGS t' (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) p Dt HND).
apply crt102rw_agree_of_aview. intros y Hy.
assert (Hyc : (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
                 frame_addr lyc cid0 pos0 <= y < frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) \/
              (exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ In (p0, n0) (ablocks B ly2 S2) /\
                 p0 <= y < p0 + req_size n0)).
{ destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
  - left. exists cid, pos'. split; [exact Hfin'|]. lia.
  - right. unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb)) as (Hk0 & Hab & _).
    destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 b kb _ _ HLED2 (HDL2 _ Hb)) as (_ & Hab2 & _).
    exists (b - cf_head), (kb + cf_head). split; [exact Hab|]. split; [exact Hab2|].
    change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb + 16) ltac:(lia)). lia. }
assert (Himg : ~ in_img SEGS y).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_intror (or_introl (ex_intro _ cid0 (ex_intro _ pos0 (conj Hin0 Hy0))))))).
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hab Hy0)))))). }
assert (Hyr : 0 <= y < 2 ^ 64).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HARc Hin0) as (? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia.
  - destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & ? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia. }
split; [exact Hyr|]. split; [exact Himg|].
assert (HnFP : ~ inFP FP1 y) by (intros Hf; exact (HFPD y Hf Hy)).
destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & Hab2 & Hy0)].
- apply (G4 cid0 pos0 y Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP].
- replace y with (p0 + (y - p0)) by lia. apply (G2 p0 n0 (y - p0) Hab Hab2); [lia|]. replace (p0 + (y - p0)) with y by lia.
  exact HnFP.
Qed.
(* the same for a freeable tree *)
Lemma crt102rw_fd_call : forall lyc Sc Hpc Wc memc mdc (kj : Z) STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p d Dt {WS1 : list (list Z)},
  ARx lyc Sc Hpc Wc memc mdc ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  forall {mo1 ow1 mo2 ow2 : Z},
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc mo1 ow1 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 mo2 ow2 ->
  (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= p /\
     p + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) ->
  (forall bk, In bk Dt -> In bk Lamc) -> (forall bk, In bk Dt -> In bk Lam2) ->
  (forall a, inFP FP1 a -> ~ pj_footR p Dt a) ->
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d p Dt ->
  pj_fdR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) d p Dt.
Proof.
intros lyc Sc Hpc Wc memc mdc kj STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p d Dt
  WS1 HARc HJ1 mo1 ow1 mo2 ow2 HLED HLED2 (cid & pos' & Hfin' & Hfa1 & Hfa2) HDL HDL2 HFPD HND.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _).
apply (crt102rw_fdR_lblk SEGS d _ (prh_lin Lamc) (prh_lin Lam2) p Dt); [|intros x0 k0 H0; exact (HDL2 _ H0)].
apply (crt102rw_fdR_frame SEGS d (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) p Dt HND).
apply crt102rw_agree_of_aview. intros y Hy.
assert (Hyc : (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
                 frame_addr lyc cid0 pos0 <= y < frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) \/
              (exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ In (p0, n0) (ablocks B ly2 S2) /\
                 p0 <= y < p0 + req_size n0)).
{ destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
  - left. exists cid, pos'. split; [exact Hfin'|]. lia.
  - right. unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb)) as (Hk0 & Hab & _).
    destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 b kb _ _ HLED2 (HDL2 _ Hb)) as (_ & Hab2 & _).
    exists (b - cf_head), (kb + cf_head). split; [exact Hab|]. split; [exact Hab2|].
    change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb + 16) ltac:(lia)). lia. }
assert (Himg : ~ in_img SEGS y).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_intror (or_introl (ex_intro _ cid0 (ex_intro _ pos0 (conj Hin0 Hy0))))))).
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hab Hy0)))))). }
assert (Hyr : 0 <= y < 2 ^ 64).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HARc Hin0) as (? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia.
  - destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & ? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia. }
split; [exact Hyr|]. split; [exact Himg|].
assert (HnFP : ~ inFP FP1 y) by (intros Hf; exact (HFPD y Hf Hy)).
destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & Hab2 & Hy0)].
- apply (G4 cid0 pos0 y Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP].
- replace y with (p0 + (y - p0)) by lia. apply (G2 p0 n0 (y - p0) Hab Hab2); [lia|]. replace (p0 + (y - p0)) with y by lia.
  exact HnFP.
Qed.

(* ---- THE SIDE FACTS AFTER A CALL: the read-only view and the document's tree survive a callee journal whose
   footprint is above page 0 and off the document's footprint; the ledger, the flags, the peak and the room are the
   callee's post's ---- *)
Lemma crt102rw_side_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1
    ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 own2 ran2 {kbg : nat} {WS1 : list (list Z)},
  liveA kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  Forall (fun r => 0 < fst r) FP1 ->
  (forall a, inFP FP1 a -> ~ pj_footR doc D a) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 most own2 -> peakc <= peak2 -> room_live_cf S2 ->
  (forall bk, In bk D -> In bk Lam2) ->
  crt_side (rc := rc) (PI := prh_img_A) (RL := RL) (L := A_prog_listing) (PA := PA) (B := B) (doc := doc) (t := t)
    (D := D) (peak := peak) (most := most) ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 own2 ran2.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2
  own2 ran2 kbg WS1 HL HJ1 HFP0 HFPD HLED2 Hpk2 HROOM2 HDL2.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HROOM. pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HND. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _ & _ & _ & _ & HFRc & _).
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _).
pose proof HTREE as (_ & _ & _ & Hd8 & (cid & pos' & Hfin & Hfa1 & Hfa2) & _).
pose proof HPRE as ((HAR & _) & _).
assert (Hfin' : In (cid, pos') (frames Sc)) by (rewrite HFRc; apply in_or_app; right; exact Hfin).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR (proj1 (proj2 HJ))) as (_ & Efa & _).
refine {| crt_side_ledger := HLED2; crt_side_peak := _; crt_side_room := HROOM2; crt_side_arodata := _;
          crt_side_doc := _; crt_side_doc_blocks := HDL2 |}.
{ lia. }
{ intros a Hro Hno Her. rewrite (G3 a); [exact (HRO a Hro Hno Her) | | exact Hno | exact Her | |].
  - destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
  - intros Hps. exact (pst_not_ro_A a Hps Hro).
  - apply fp_spares_closed. apply sink_closed_pos. exact HFP0. }
apply (crt102rw_nodeR_lblk SEGS t _ (prh_lin Lamc) (prh_lin Lam2) doc D); [|intros x0 k0 H0; exact (HDL2 _ H0)].
apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) doc D HND).
apply crt102rw_agree_of_aview. intros y Hy.
assert (Hyc : (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
                 frame_addr lyc cid0 pos0 <= y < frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) \/
              (exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ In (p0, n0) (ablocks B ly2 S2) /\
                 p0 <= y < p0 + req_size n0)).
{ destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
  - left. exists cid, pos'. rewrite (Efa cid pos'). split; [exact Hfin'|]. lia.
  - right. unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLED (HDL _ Hb)) as (Hk0 & Hab & _).
    destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 b kb _ _ HLED2 (HDL2 _ Hb)) as (_ & Hab2 & _).
    exists (b - cf_head), (kb + cf_head). split; [exact Hab|]. split; [exact Hab2|].
    change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb + 16) ltac:(lia)).
    first [lia | match goal with |- ?g => idtac "GG2" g end; fail]. }
assert (Himg : ~ in_img SEGS y).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_intror (or_introl (ex_intro _ cid0 (ex_intro _ pos0 (conj Hin0 Hy0))))))).
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hab Hy0)))))). }
assert (Hyr : 0 <= y < 2 ^ 64).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HARc Hin0) as (? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia.
  - destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & ? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia. }
split; [exact Hyr|]. split; [exact Himg|].
assert (HnFP : ~ inFP FP1 y) by (intros Hf; exact (HFPD y Hf Hy)).
destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & Hab2 & Hy0)].
- apply (G4 cid0 pos0 y Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP].
- replace y with (p0 + (y - p0)) by lia. apply (G2 p0 n0 (y - p0) Hab Hab2); [lia|]. replace (p0 + (y - p0)) with y by lia.
  exact HnFP.
Qed.

(* ---- the shadow-store segment shape (U1's unpoison and X's re-poison): one region, the frame's shadow bytes 4 .. 22 *)
Definition crt102rw_ssSH (pc : Z) : sstate := mkSS pc cur_atoms
  [YP09.mkRegion (Some (xr 18)) 4 23 4 23 []] None (mkFacts [(xr 18, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] [] []).
Lemma crt102rw_SH_entry : forall (fxk : YK11.FPState) pc (Wc : world SEGS) memc rg F,
  getr rg 18 = w64 (shadow_addr F) -> 0 <= F -> F + 512 <= 2 ^ 47 ->
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr F + i)) ->
  st_ok_pi SEGS VAL (TE regs rg []) (crt102rw_ssSH pc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk pc Wc memc rg F R18 HF0 HF HP.
set (E := TE regs rg []).
assert (X18 : bv_unsigned (ew E (xr 18)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 18) (shadow_addr F)); [exact X18 | unfold shadow_addr, SHADOW_OFF; lia
    | unfold shadow_addr, SHADOW_OFF; lia | | constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X18.
  split; [|exact I]. unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Ltac crt102rw_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* ---- X (+0x304 .. +0x33c): the shared re-poison of back and v (f8 into the frame's shadow bytes 4 .. 10 and
   16 .. 22), then the join ---- *)
Lemma crt102rw_at_X : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  atX fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgA fxk CRT_X_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HX.
pose proof (crt_at_X_join HX) as HXJ.
pose proof (crt_at_J_live HXJ) as HL. pose proof (crt_at_J_frm_zero HXJ) as HFZ.
pose proof (crt_at_J_fregs HXJ) as HFK. pose proof (crt_at_J_bregs HXJ) as HBR.
pose proof (crt_at_J_ret HXJ) as R22. pose proof (crt_at_J_copy_fd HXJ) as HFD.
pose proof (crt_at_J_r0 HXJ) as Er0. pose proof (crt_at_J_count HXJ) as HCNT.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMN.
destruct (crt102rw_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (crt_bregs_sp HBR) as R2. pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4. pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20. pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23. pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof crt102rw_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (crt102rw_SH_entry fxk (CRT_PC_A + CRT_X_OFF) Wc memc rg F R18 ltac:(lia) ltac:(lia)
  (fun i Hi => proj1 (Fsh i Hi))) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
assert (X18 : bv_unsigned (ew (TE regs rg []) (xr 18)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
pose proof HMN as HPM.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WSj).
unfold crt_cfg.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (2 ^ 63, 2 ^ 63) (CRT_PC_A + CRT_J_OFF).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 18) (shadow_addr F)); [reflexivity | exact X18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists CRT_CID, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite crt102rw_fb. change (512 / 8) with 64.
    fold F. lia. }
  apply awr_ok_nil. }
pmkst HS.
set (WSH := ss_mem (crt102rw_ssSH (CRT_PC_A + CRT_X_OFF))) in *.
assert (Hwr : forall a, in_wrange (TE regs rg []) WSH a -> shadow_addr F + 4 <= a < shadow_addr F + 23).
{ intros a (rr & Hr & Ha). cbv [WSH crt102rw_ssSH ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X18 in Ha. lia. }
assert (Hag : forall xw : word, ~ crt102rw_wr F (bv_unsigned xw) ->
  mrestrict (w_H Wc) (ms_mem ms) xw = mrestrict (w_H Wc) memc xw).
{ intros xw Hn. apply HFr. intros Hw. apply Hn. left. exact (Hwr _ Hw). }
pose proof (crt102rw_live_run lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ pos Dc Lamc peakc cntc ownc ranc HL HJ HBj Hag
  HPM) as HL1.
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [crt102rw_keep HS |]). destruct Hr. }
clear HF HG.
lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
  change n with (CRT_PC_A + CRT_J_OFF) end.
apply (TAIL fxk lyc Sc Hpc Wc (ms_mem ms) _ kj pos Lamc peakc cntc ownc ranc Dc (ms_regs ms) r).
assert (HDc : forall bk, In bk Dc -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hbk. }
(* copy's footprint is application memory below the ceiling, so the re-poison kept it *)
assert (HAGc : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (pj_footR (F + CRT_OFF_COPY) Dc)).
{ intros y Hy.
  destruct (crt102rw_foot_nw _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dc (F + CRT_OFF_COPY) y HL HDc
    ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy) as (Hy1 & Hy2).
  assert (E : mrestrict (w_H Wc) (ms_mem ms) (Z_to_bv 64 y) = mrestrict (w_H Wc) memc (Z_to_bv 64 y)).
  { apply Hag. rewrite unsigned_lit_small by lia. exact Hy2. }
  split; [unfold mbyte; rewrite E; reflexivity|].
  intros Hw. unfold writable_at, wview in *. rewrite E. exact Hw. }
refine {| crt_at_J_live := HL1; crt_at_J_frm_zero := HFZ; crt_at_J_fregs := HFK; crt_at_J_bregs := _;
          crt_at_J_ret := _; crt_at_J_copy_fd := _; crt_at_J_r0 := Er0; crt_at_J_count := _ |}.
{ refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _;
            crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
            crt_bregs_s11 := _ |}; rewrite !KR by (cbv; tauto).
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R8.
  - exact R9.
  - exact R18.
  - exact R20.
  - exact R19.
  - exact R23.
  - exact R26.
  - exact R27. }
{ rewrite KR by (cbv; tauto). exact R22. }
{ exact (crt102rw_fdR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc)
    (F + CRT_OFF_COPY) Dc HFD HAGc). }
destruct HCNT as (cset & Hc03 & Hcm & [HC1 | (Hr0 & Hown & Hran & Hcnt & Hpos & HND & Htblk & (Fc & HFo & HFoe) &
  Hdep)]).
- exists cset. split; [exact Hc03|]. split; [exact Hcm|]. left. exact HC1.
- exists cset. split; [exact Hc03|]. split; [exact Hcm|]. right.
  split; [exact Hr0|]. split; [exact Hown|]. split; [exact Hran|]. split; [exact Hcnt|]. split; [exact Hpos|].
  split.
  { exact (pj_nodeR_frame SEGS crt_tree_J (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc)
      (F + CRT_OFF_COPY) Dc HND HAGc). }
  split; [exact Htblk|].
  split; [|exact Hdep].
  (* copy's free order: its footprint is untouched by the shadow stores (the same agreement as pj_fdR's) *)
  exists Fc. split; [|exact HFoe].
  exact (PRH_PjOrder.pj_foR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc)
    (prh_lin Lamc) (F + CRT_OFF_COPY) Dc Fc HFo (fun a k Hk => HDc (a, k) Hk) HAGc).
Qed.

(* ---- reading the symbolic state back: a chunk of a region of the final state holds its value ---- *)
Lemma crt102rw_chunk_vm : forall E ss (H : word -> bool) ms0 i r k b o (n : N) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some r ->
  YP09.r_base r = Some k -> bv_unsigned (ew E k) = b ->
  In (YP09.mkChunk o (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms0)) (b + o) (N.to_nat n) v.
Proof.
intros E ss H ms0 i r k b o n e v HS Hi Hb Hk Hc He Hv Hn.
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict H ms0) HS) as (_ & Hrs & _).
assert (Hi' : nth_error (ss_mem (abs_ss VAL ss)) i = Some r) by (destruct ss; exact Hi).
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi')) as Hr.
pose proof (region_ok_chunk SEGS E _ r _ Hr Hc) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck. rewrite Hk in Hck.
exact (val_of_chunk_ok SEGS E _ b o n e v Hck He Hv Hn).
Qed.
Lemma crt102rw_vm1_zero : forall (H : word -> bool) m a, val_mem SEGS (mrestrict H m) a 1 0 -> aview SEGS H m a = Some 0.
Proof.
intros H m a Hv. unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv. cbn [option_map].
f_equal; try (rewrite Z_to_bv_unsigned; unfold bv_wrap, le_byte; change (bv_modulus 8) with 256;
  rewrite Z.div_0_l by (apply Z.pow_nonzero; lia); reflexivity).
Qed.
Lemma crt102rw_apresent_vis : forall (H : word -> bool) m a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* ---- the document's home stays a live fake frame of the entry (Crt102Arms.v arms_home_keep's argument) ---- *)
Lemma crt102rw_home_keep : forall own lyc Sc Hpc Wc memc mdc kj {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS -> ck_obj_home lyc Sc Wc memc doc.
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ.
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & Hd8 & (cid & pos & Hfin & Hfa1 & Hfa2) & HRA).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR Hly) as (_ & Efa & _).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (F32 & _).
split; [exact Hd8|]. split.
- exists cid, pos. rewrite Efa. split; [rewrite Hfrs; apply in_or_app; right; exact Hfin|]. split; lia.
- intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr. apply (F4 cid pos); [exact Hfin | right | apply inFP_nil].
  unfold in_zr, shadow_addr. cbn [fst snd].
  assert (E8 : (frame_addr ly cid pos + fs_frame_bytes cid) / 8 = frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8).
  { apply Z.mod_divide in F32; [|lia]. destruct F32 as [q Hq]. rewrite Hq.
    replace (q * 32 + fs_frame_bytes cid) with (fs_frame_bytes cid + (4 * q) * 8) by lia. rewrite Z.div_add by lia.
    replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert ((doc + 55) / 8 = doc / 8 + 6).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 55) with (7 + (q + 6) * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. cbn. lia. }
  assert (Hd : (doc + 56) / 8 = doc / 8 + 7).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 56) with ((q + 7) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  pose proof (Z.div_le_mono (frame_addr ly cid pos) a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono a (doc + 55) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (doc + 56) (frame_addr ly cid pos + fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

End g.
End f.
End crtA.
