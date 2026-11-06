(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Loop_kitQ.v, with its module paths and module names changed; 1902 of its 1944 lines of code are new or changed and 154 lines of the source are left out. *)
(* fuzz_preset, program walk of round_trip_text on the #102 pins, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped
   twin bff8519bbe3ea0e4, entry A' 0x8496c): STRETCH CK of the cut layer lib/A/Prog/Rtt102Cut.v (lane WalkRtt102.RttX
   for the text owner): RTT_SEG_CK = rtt_seg RT_X rtt_at_x -> rtt_seg RT_CK rtt_at_ck.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma): stretch CK of round_trip_text; the
   function-level gate is the text owner's (proof-index round_trip_text, EXIT=0; an index lookup, see the brief).
   THE CODE, A' +0x33c .. +0x374 (A' capstone listing lines 209-223): `bnez s8` -> abort (rc = 0
   at the cut: not taken), `mv a0, s4; mv a1, s7; jal same` (the kit's tsame_specX at DOC_D: doc and back hold the same tree
   t, so a0 = 1), `beqz a0` -> abort (not taken), `beqz s3` (copy = 0 ?): copy <> 0 -> `li a2, 0x38; mv a0, s3;
   mv a1, s7; jal __asan_memcpy; j +0x370` (the memcpy row's _xm text through YGcallMxmn.v aj_intrin_at_xm_fr: copy is
   a caller-frame byte range named by the text's FP), copy = 0 -> `mv a0, s7; jal pj_free` (the kit's tpj_free_specX at
   DOC_D in its post-implication form: back's tree over Db is freed, the ledger returns to the entry's list; its run
   event from the cut's free-order conjunct (rtt_rb: pj_free's order list at back, requests fo t) and the model's
   HBulk (fo t) at RT_K_T; the class-24 bound by ck_ccnt24); `mv s5, zero; j X` (+0x1e0) with rtt_Qx's r = 0 arm.
   The register-only instructions are single concrete steps (Rtt102FR1KitA.v fr_addi / fr_jal /
   fr_beqz_* of lane RttFR1, built green at 31b52895a2f, copied here under ck_ names: they are H5RttS4.v s4_* of
   the H2H5 walk head 1934271f1f40); a call is fr_call_at (YCbqGcall.v aj_call_x_sp from a concrete
   state), copied as ck_call_at; the frame-pointer chain at a call is rtt_chain_at, copied as ck_chain_at.
   AT THE BATCH KIT'S CUT (Rtt102Cut.v at 80a1d52c32c7): DW is gone; rtt_J is the journal from the DEPOT-MOVED entry, so each
   call here is made from rtt_J at the call state and returns the caller journal rtt_Jc, which ck_carry_keep turns back
   into rtt_J (rtt_J_of_Jc) and across which rtt_carry's last conjunct rtt_wild is kept (rtt_wild_Jc); same's text
   gained the guarded live-stack premise, false here (doc lies below alloc_ceiling <= sp); rtt_rb gained back's free
   order at every depth bound and K0-CAP (pj_ncapR), which `*copy = back` moves to copy as it moves pj_nodeR
   (ck_foR_move, ck_ncapR_move) for rtt_Qx's two new conjuncts.
   AT THE R CUT (Rtt102Cut.v at 448ecd157e57): every statement concludes YA0nH.SRr' SEGS RZ_cf and every journal is
   at RZW := YA0nH.wle' SEGS RZ_cf. The steps are YSRrG.SRrG_step; ck_call_at takes an SRr' callee at apost_base_xR
   RZW (as Rtt102FR1Kit.v fr_call_at); same's text is still a plain SRr, lifted (YA0nH.SRr_SRr',
   YCbqG.apost_base_x_R_lift); pj_free's text concludes SRr' with the W-post fpostWmR at RZW, read at d = 0 by
   ck_fpostW0; the memcpy is YGcallMxmn.v aj_intrin_at_xm_frR at RZW. No fact crosses a wle' step: every keep is
   read from a journal's aview clauses or re-derived from ARx at the new state.
   NUMERALS. DERIVED: 828 (RT_CK), 480 (RT_X), the byte offsets 832 .. 884 of the stretch's instructions (4 * the slot
   from round_trip_text's entry), RTT_PC_A (Rtt102XA.v). LENGTH: 56 (struct pj; the memcpy length 0x38), 32 (back =
   F + 32), 120 (the flag-pointer slot), 104 (the 13 saves), 128 (fs_frame_bytes 1), 64 (the fake frames' alignment),
   8 (a word, a shadow granule), 2 ^ 32 / 2 ^ 40 / 2 ^ 44 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (widths and bands), 176 / 192 / 16
   (the realigned sp below the entry sp). WORD: register indices. No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YGcfTreeVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnEx PRH_FnPj PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnWriter CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveSec PresetRun PresetReqAt PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Rtt102Cut Rtt102XA.
(* the re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the zone
   (YGcfRehidePost.RZ_cf), used qualified: the stretch concludes YA0nH.SRr' SEGS RZ_cf and every journal is at
   RZW := YA0nH.wle' SEGS RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
(* the hull budget at pj_free's call (PRH_FnPj.v tpj_free_specX), paid from the cut's position (CrsSeg_Z.v's route) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvHullA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
(* a runaway sentence fails at its own line instead of holding the VM (build 83048a40cf2 ran past 3600 s) *)


(* ======================================================================================================== *)
(* ---- 1. pure tree lemmas over PRH_Reader.v's predicates ---- *)
Section tr.
Variable segs : list Segment.

(* a tree is freeable to its depth (plain lib/Prog/PjStruct.v:412-572 pf_items_mono .. pj_node_fd, restated over
   PRH_Reader.v's pj_nodeR / pj_fdR, which have the same shapes over rd_u64 / pj_cstrR; no plain lemma cited) *)
Lemma ck_pf_items_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *.
- exact Hp.
- destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
  split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.

Lemma ck_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
intros m lblk Pi Pi' p D H (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
exact (H _ _ _ _ _ H6).
Qed.

Lemma ck_fd_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (S d) p D.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
- eapply (ck_fshape_mono m lblk); [|exact H].
  intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
- eapply (ck_fshape_mono m lblk); [|exact H].
  intros ks kids keys n Di Hi. cbv beta in Hi |- *.
  apply (ck_pf_items_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi].
  intros a D1 H1. exact (IH a D1 H1).
Qed.

Lemma ck_fd_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof.
intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|].
apply ck_fd_succ. apply IH. exact H.
Qed.

Lemma ck_items_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *.
- exact Hl.
- destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
  split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
  apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.

Lemma ck_mems_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a D1) ->
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

Lemma ck_nodeR_fd : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (PjTree.depth t) p D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk p D H;
  cbn [pj_nodeR] in H.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag PjTree.JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
  split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
  cbn [PjTree.depth pj_fdR]. split; [exact Hn|]. split; [exact Ha|].
  exists (PjTree.tag (PjTree.JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
  split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
  split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
  split; [left; split; [exact E3 | split; reflexivity]|].
  split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR.
  split; [exact Hn|]. split; [exact Ha|].
  assert (HI : pf_itemsR segs m lblk (pj_fdR segs m lblk d') false kids keys (Z.to_nat n) Di).
  { rewrite En, Nat2Z.id. apply (ck_items_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 Hu HP. rewrite Forall_forall in IH.
    apply (ck_fd_mono m lblk (PjTree.depth u)); [|exact (IH u Hu m lblk a D1 HP)].
    pose proof (PjTree.depth_item items u Hu). lia. }
  destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
  + subst cap.
    exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ek | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|]. exact HI.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
    split; [left; split; [exact Ek | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
- destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  remember (PjTree.depth (PjTree.JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [PjTree.depth] in Edd; discriminate|].
  cbn [pj_fdR]. unfold pj_fshapeR.
  split; [exact Hn|]. split; [exact Ha|].
  destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
  + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia].
    cbn [pj_memsR] in Hi.
    exists (PjTree.tag (PjTree.JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
    split; [left; split; [exact Hy0 | split; reflexivity]|].
    split; [subst D; cbn; apply Permutation_refl|].
    cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    exists (PjTree.tag (PjTree.JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
    split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
    split; [subst D; cbn [app]; apply Permutation_refl|].
    cbv beta. rewrite En, Nat2Z.id. apply (ck_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (ck_fd_mono m lblk (PjTree.depth u)); [|exact (IH m lblk a D1 HP)].
    pose proof (PjTree.depth_member members nm u Hu). lia.
Qed.

(* the tree moved: *copy = back copies the 56-byte root, the subtree hangs off D's blocks, so the same tree stands at the
   new place when those blocks keep their bytes (H5RttS4.v s4_val_move .. s4_nodeR_move at 1934271f1f40, restated over
   this tree's PRH_Reader.v frame lemmas) *)
Lemma ck_val_move : forall m m' a a' n v, val_mem segs m a n v ->
  (forall k, (k < n)%nat -> mbyte segs m' (a' + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) ->
  val_mem segs m' a' n v.
Proof. intros m m' a a' n v Hv E k Hk. rewrite E by exact Hk. exact (Hv k Hk). Qed.

Lemma ck_u64_move : forall m m' a a' v, rd_u64 segs m a v ->
  (forall j, 0 <= j < 8 -> mbyte segs m' (a' + j) = mbyte segs m (a + j)) -> rd_u64 segs m' a' v.
Proof.
intros m m' a a' v (Hr & Hv) E. split; [exact Hr|]. apply (ck_val_move m m' a a' 8 v Hv).
intros k Hk. apply E. lia.
Qed.
Lemma ck_u32_move : forall m m' a a' v, rd_u32 segs m a v ->
  (forall j, 0 <= j < 4 -> mbyte segs m' (a' + j) = mbyte segs m (a + j)) -> rd_u32 segs m' a' v.
Proof.
intros m m' a a' v (Hr & Hv) E. split; [exact Hr|]. apply (ck_val_move m m' a a' 4 v Hv).
intros k Hk. apply E. lia.
Qed.

Lemma ck_hdr_move : forall m m' p p' ty num str kids keys n cap,
  pj_hdrR segs m p ty num str kids keys n cap -> pj_rwR segs m' p' ->
  (forall j, 0 <= j < 56 -> mbyte segs m' (p' + j) = mbyte segs m (p + j)) ->
  pj_hdrR segs m' p' ty num str kids keys n cap.
Proof.
intros m m' p p' ty num str kids keys n cap (_ & Ht & Hn & Hs & Hk & Hy & Hc & Hp) Hrw E.
assert (EO : forall o, 0 <= o -> o + 8 <= 56 -> forall j, 0 <= j < 8 ->
          mbyte segs m' (p' + o + j) = mbyte segs m (p + o + j)).
{ intros o Ho1 Ho2 j Hj. rewrite <- !Z.add_assoc. apply E. lia. }
split; [exact Hrw|].
split; [apply (ck_u32_move m m' p p' ty Ht); intros j Hj; apply E; lia|].
split; [apply (ck_u64_move m m' (p + 8) (p' + 8) num Hn); apply EO; lia|].
split; [apply (ck_u64_move m m' (p + 16) (p' + 16) str Hs); apply EO; lia|].
split; [apply (ck_u64_move m m' (p + 24) (p' + 24) kids Hk); apply EO; lia|].
split; [apply (ck_u64_move m m' (p + 32) (p' + 32) keys Hy); apply EO; lia|].
split; [apply (ck_u64_move m m' (p + 40) (p' + 40) n Hc); apply EO; lia|].
apply (ck_u64_move m m' (p + 48) (p' + 48) cap Hp); apply EO; lia.
Qed.

Lemma ck_nodeR_move : forall t m m' lblk p p' D,
  pj_nodeR segs m lblk p t D -> pj_apartR D p' -> pj_rwR segs m' p' ->
  (forall j, 0 <= j < 56 -> mbyte segs m' (p' + j) = mbyte segs m (p + j)) ->
  pj_agreeR segs m m' (fun x => exists b, In b D /\ pj_holdsR b x) ->
  pj_nodeR segs m' lblk p' t D.
Proof.
intros t m m' lblk p p' D H Hap Hrw E HM.
assert (HM1 : forall x, (exists b, In b D /\ pj_holdsR b x) -> mbyte segs m' x = mbyte segs m x)
  by (intros x Hx; exact (proj1 (HM x Hx))).
destruct t as [| | | txt bits | s | items | members]; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Hap|]); exists num, str, kids, keys, n, cap;
  (split; [exact (ck_hdr_move m m' p p' _ num str kids keys n cap Hh Hrw E)|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (pj_cstrR_frame segs m m'); [exact Hc|].
  intros x Hx. apply HM1. exists (str, k).
  split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (pj_cstrR_frame segs m m'); [exact Hc|].
  intros x Hx. apply HM1. exists (str, k).
  split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk) items kids Di Hi).
  intros i u D1 Hil Hinc HP.
  pose proof (pj_nth_lenR items i u Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  apply (pj_nodeR_frame segs u m m' lblk _ D1 HP).
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pj_memsR_mono segs m m' lblk (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk) members kids keys Di Hi).
  intros i nm u x k D1 Hil Hxk Hinc Hx Hcs HP.
  pose proof (pj_nth_lenR members i (nm, u) Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
  split; [|split].
  + apply (rd_u64_frame segs m m'); [exact Hx|]. intros y Hy. apply HM1. exists (keys, 8 * cap).
    split; [exact (proj2 Hin) | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply (pj_cstrR_frame segs m m'); [exact Hcs|].
    intros y Hy. apply HM1. exists (x, k).
    split; [apply HDi; exact Hxk | unfold pj_holdsR; cbn [fst snd]; exact Hy].
  + apply (pj_nodeR_frame segs u m m' lblk _ D1 HP).
    intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
    * exists (kids, 56 * cap). split; [exact (proj1 Hin) | unfold pj_holdsR; cbn [fst snd]; lia].
    * exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

(* the ordered free list moves with the root as the tree does (pj_foR reads the root's header, then D's blocks) *)
Lemma ck_foR_move : forall d m m' lblk p p' D F,
  pj_foR segs m lblk d p D F -> pj_apartR D p' -> pj_rwR segs m' p' ->
  (forall j, 0 <= j < 56 -> mbyte segs m' (p' + j) = mbyte segs m (p + j)) ->
  pj_agreeR segs m m' (fun x => exists b, In b D /\ pj_holdsR b x) ->
  pj_foR segs m' lblk d p' D F.
Proof.
intros d m m' lblk p p' D F H Hap Hrw E HM.
destruct d as [|d]; cbn [pj_foR] in H |- *; unfold pj_oshapeR in H |- *;
  destruct H as (Hnd & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
    Hh & Hs & Hk & Hy & Hp & HPi & EF);
  (split; [exact Hnd|]); (split; [exact Hap|]);
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi;
  (split; [exact (ck_hdr_move m m' p p' ty num str kids keys n cap Hh Hrw E)|]);
  (split; [exact Hs|]); (split; [exact Hk|]); (split; [exact Hy|]); (split; [exact Hp|]); (split; [|exact EF]).
- exact HPi.
- cbv beta in HPi |- *.
  assert (HinD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
    by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hb]).
  apply (pf_oitemsR_frame segs d m m' lblk lblk ks kids keys (Z.to_nat n) Di Fi HPi).
  + exact (pf_oitemsR_lblk segs m lblk d ks kids keys (Z.to_nat n) Di Fi HPi).
  + apply (pf_agree_mono segs m m' _ _ HM). unfold pf_ofoot.
    intros y [Hy'|[(Hks & Hy')|(b & Hb & Hy')]].
    * destruct Hk as [(-> & -> & ->)|(k & _ & Hnk & ->)]; [cbn in Hy'; lia|].
      exists (kids, k). split; [apply HinD; apply in_or_app; right; apply in_or_app; left; apply in_eq|].
      unfold pj_holdsR; cbn [fst snd]. lia.
    * destruct Hy as [(-> & -> & ->)|(_ & k & _ & Hnk & ->)]; [discriminate Hks|].
      exists (keys, k).
      split; [apply HinD; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; apply in_eq|].
      unfold pj_holdsR; cbn [fst snd]. lia.
    * exists b. split; [|exact Hy']. apply HinD. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hb.
Qed.

(* K0-CAP moves with the root as the tree does: the root's cap and kids words are moved bytes, the kids' capacities
   lie in D's blocks (Rtt102Cut.v rtt_kids_frame / rtt_mkids_frame / rtt_ncapR_frame) *)
Lemma ck_ncapR_move : forall t m m' lblk p p' D,
  pj_nodeR segs m lblk p t D -> pj_ncapR segs m p t ->
  (forall j, 0 <= j < 56 -> mbyte segs m' (p' + j) = mbyte segs m (p + j)) ->
  (forall x, (exists b, In b D /\ pj_holdsR b x) -> mbyte segs m' x = mbyte segs m x) ->
  pj_ncapR segs m' p' t.
Proof.
intros t m m' lblk p p' D H HC E HM.
assert (EO : forall o, 0 <= o -> o + 8 <= 56 -> forall j, 0 <= j < 8 ->
          mbyte segs m' (p' + o + j) = mbyte segs m (p + o + j)).
{ intros o Ho1 Ho2 j Hj. rewrite <- !Z.add_assoc. apply E. lia. }
destruct t as [| | | txt bits | s | items | members]; cbn [pj_ncapR pj_nodeR] in H, HC |- *; try exact I.
- destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (HC48 & kids' & HK24 & HKi).
  pose proof Hh as (_ & _ & _ & _ & K24 & _).
  pose proof (PjFoMember.pfm_rd_u64_det segs m (p + 24) kids' kids HK24 K24) as Ekd. subst kids'.
  split; [apply (ck_u64_move m m' (p + 48) (p' + 48) _ HC48); apply EO; lia|].
  exists kids. split; [apply (ck_u64_move m m' (p + 24) (p' + 24) kids HK24); apply EO; lia|].
  apply (rtt_kids_frame (pj_nodeR segs m lblk) (pj_ncapR segs m) (pj_ncapR segs m') items kids Di Hi HKi).
  intros a' u D1 Hu Hinc HP HQ H1 H2.
  assert (Hl : (1 <= length items)%nat) by (destruct items; [destruct Hu | cbn [length]; lia]).
  assert (Hp : 0 < cap) by lia.
  apply (rtt_ncapR_frame segs u m m' lblk a' D1 HP HQ).
  intros x [Hx | (b & Hb & Hx)].
  + apply HM. exists (kids, 56 * cap).
    split; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply HM. exists b. split; [subst D; apply in_or_app; right; exact (Hinc b Hb) | exact Hx].
- destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (HC48 & kids' & HK24 & HKi).
  pose proof Hh as (_ & _ & _ & _ & K24 & _).
  pose proof (PjFoMember.pfm_rd_u64_det segs m (p + 24) kids' kids HK24 K24) as Ekd. subst kids'.
  split; [apply (ck_u64_move m m' (p + 48) (p' + 48) _ HC48); apply EO; lia|].
  exists kids. split; [apply (ck_u64_move m m' (p + 24) (p' + 24) kids HK24); apply EO; lia|].
  apply (rtt_mkids_frame segs m lblk (pj_nodeR segs m lblk) (pj_ncapR segs m) (pj_ncapR segs m') members kids keys Di
    Hi HKi).
  intros a' nm u D1 Hu Hinc HP HQ H1 H2.
  assert (Hl : (1 <= length members)%nat) by (destruct members; [destruct Hu | cbn [length]; lia]).
  assert (Hp : 0 < cap) by lia.
  apply (rtt_ncapR_frame segs u m m' lblk a' D1 HP HQ).
  intros x [Hx | (b & Hb & Hx)].
  + apply HM. exists (kids, 56 * cap).
    split; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply HM. exists b. split; [subst D; apply in_or_app; right; exact (Hinc b Hb) | exact Hx].
Qed.
End tr.

(* ======================================================================================================== *)
(* ---- 2. concrete steps of register-only code (Rtt102FR1KitA.v :57-164 at 31b52895a2f, = H5RttS4.v's s4_ steps), and the
   two forms that file lacks: `bnez` not taken and the unlinked `j` ---- *)
Section stp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation BASE := (@pa_val _ L PI A_TEXT).

Lemma ck_addi : forall (W : world SEGS) regs mem md Q w k (rd rs : bv 5) (imm : bv 12) (rd0 rs0 : bv 5) (i0 : Z),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
rd = rd0 -> rs = rs0 -> bv_signed imm = i0 ->
bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx (regupd regs rd0 (v_addi (getr regs rs0) i0))
             (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rd rs imm rd0 rs0 i0 Hpl Hdec Erd Ers Ei Hrd Hk0 Hk4 HK. subst rd rs i0.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_addi SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 rs0 imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma ck_jal : forall (W : world SEGS) regs mem md Q w k tgt (rd : bv 5) (imm : bv 21),
clookup pa_tbl (BASE + k) = Some w ->
decode_any (Z_to_bv 32 w) = Some (Jal rd imm, 4%Z) -> rd = 1%bv ->
0 <= k -> k + 4 < 2 ^ 40 ->
btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = Z_to_bv 64 tgt ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx (regupd regs 1%bv (Z_to_bv 64 (BASE + (k + 4))))
             (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k tgt rd imm Hl Hdec Hrd1 Hk0 Hk4 Htgt HK. subst rd.
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (H10 : bv_eqb (1%bv : bv 5) 0 = false) by (vm_compute; reflexivity).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) 1%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite H10. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

(* `j off` = jal x0, off: the unlinked jump *)
Lemma ck_j : forall (W : world SEGS) regs mem md Q w k tgt (r0 : bv 5) (imm : bv 21),
clookup pa_tbl (BASE + k) = Some w ->
decode_any (Z_to_bv 32 w) = Some (Jal r0 imm, 4%Z) -> r0 = 0%bv ->
btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = Z_to_bv 64 tgt ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k tgt r0 imm Hl Hdec Hr0 Htgt HK. subst r0.
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_jal_x0 SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt. apply HK.
Qed.

(* `beqz rs, off`: beq rs, x0 - the taken and the fall-through step *)
Lemma ck_beqz_tk : forall (W : world SEGS) regs mem md Q w k tgt (rs r0 rs0 : bv 5) (imm : bv 13),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs r0 imm, 4%Z) -> r0 = 0%bv -> rs = rs0 ->
0 <= k -> k + 4 < 2 ^ 40 ->
btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = Z_to_bv 64 tgt ->
c_eq (getr regs rs0) (getr regs 0%bv) = true ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k tgt rs r0 rs0 imm Hpl Hdec Hr0 Hrs Hk0 Hk4 Htgt Hc HK. subst r0 rs.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_beq_tk SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs0 0%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt. apply HK.
Qed.

Lemma ck_beqz_ft : forall (W : world SEGS) regs mem md Q w k (rs r0 rs0 : bv 5) (imm : bv 13),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs r0 imm, 4%Z) -> r0 = 0%bv -> rs = rs0 ->
0 <= k -> k + 4 < 2 ^ 40 ->
c_eq (getr regs rs0) (getr regs 0%bv) = false ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rs r0 rs0 imm Hpl Hdec Hr0 Hrs Hk0 Hk4 Hc HK. subst r0 rs.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_beq_ft SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs0 0%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

(* `bnez rs, off`: bne rs, x0, not taken *)
Lemma ck_bnez_ft : forall (W : world SEGS) regs mem md Q w k (rs r0 rs0 : bv 5) (imm : bv 13),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs r0 imm, 4%Z) -> r0 = 0%bv -> rs = rs0 ->
0 <= k -> k + 4 < 2 ^ 40 ->
c_eq (getr regs rs0) (getr regs 0%bv) = true ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rs r0 rs0 imm Hpl Hdec Hr0 Hrs Hk0 Hk4 Hc HK. subst r0 rs.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_bne_ft SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs0 0%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.
End stp.

(* ---- pure helpers (Rtt102FR1KitA.v :168-204 at 31b52895a2f) ---- *)
Lemma ck_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

Lemma ck_fpchain_keep : forall (r1 r2 : reader) lo top ch bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch -> fpchain (rdword r2) bp top ch.
Proof.
intros r1 r2 lo top ch. induction ch as [|[[fp ra] nfp] ch IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r.
  rewrite (Hkeep (bp - 8)) by lia. auto.
- cbn [fpchain] in *. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite (Hkeep (fp - 8)) by lia; exact E3|].
  split; [rewrite (Hkeep (fp - 16)) by lia; exact E4|].
  split; [exact E5|].
  destruct (bad_next fp top nfp) eqn:Eb; [exact E6|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb1 _].
  apply orb_false_iff in Eb1 as [Eb11 Eb12].
  apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12.
  apply (IH nfp Hkeep); [lia | lia | exact E6].
Qed.

Lemma ck_aview_of_apresent : forall segs (H : word -> bool) mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
intros segs H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* ---- the class-24 bound from the run position: the driver interface owner's PresetCfnA.v:456-484 (iface_hruns_big, counts_of_room_pos,
   counts_of_room_pos_rl), restated over the same two lemmas it cites: PresetCfnA.v Requires the plain image's
   lib/ZImage.v, which does not build on the #102 pins (pins102 build 2de0f514036: "Unable to unify zpc0 with
   Z.of_N Plain.M.init_pc"); PresetLiveSec and CfRoomLivePreset do not need it ---- *)
Lemma ck_hruns_big : forall sm x os, PresetReqAt.MAXB < Z.of_nat (length x) -> PresetRun.hruns sm x os = [].
Proof.
intros sm x os Hx. induction os as [|[[o1 o2] o0] os IH]; [reflexivity|].
rewrite PresetRun.hruns_cons, IH, app_nil_r. unfold PresetRun.call_evs. cbv zeta.
rewrite (proj2 (Z.ltb_lt _ _) Hx). reflexivity.
Qed.
Lemma ck_ccnt24 : forall sm x os i H0 hist S, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os i H0 hist S ((d & Hd & Hp) & _). apply CfRoomLivePreset.preset_ccnt24.
destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx|Hx].
- exact (PresetLiveSec.live_c24_state sm x os i _ d Hx Hd Hp).
- rewrite (ck_hruns_big sm x os ltac:(lia)), List.firstn_nil in Hp.
  pose proof (PresetLiveSec.cnt_state (PresetRoom.in_cls 24) _ _ d Hd Hp) as C2.
  assert (Z0 : forall f, PresetReqAt.cnt f (PresetReqAt.hlive []) = 0%nat) by reflexivity.
  rewrite Z0 in C2. rewrite PresetLiveBounds.L24_value. unfold PresetLiveBounds.DRV. lia.
Qed.

(* ---- frame sizes, shadow ranges, views ---- *)
Lemma ck_fs_cid : forall cid, 56 <= fs_frame_bytes cid -> 0 <= cid.
Proof.
intros cid H. unfold fs_frame_bytes in H. destruct (Z_lt_le_dec cid 0) as [Hn|Hn]; [exfalso|exact Hn].
rewrite <- (Z.opp_involutive cid), Z.shiftl_opp_r, Z.shiftr_div_pow2 in H by lia.
assert (H2 : 2 ^ 1 <= 2 ^ (- cid)) by (apply Z.pow_le_mono_r; lia).
assert (H3 : 64 / 2 ^ (- cid) <= 64 / 2 ^ 1) by (apply Z.div_le_compat_l; lia).
change (64 / 2 ^ 1) with 32 in H3. lia.
Qed.
Lemma ck_fs8 : forall cid, 0 <= cid -> fs_frame_bytes cid mod 8 = 0 /\ 64 <= fs_frame_bytes cid.
Proof.
intros cid H. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) H) as Hp. split; [|lia].
replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring. apply Z.mod_mul. lia.
Qed.
(* a range inside an 8-aligned frame is addressable in a view that keeps the frame's shadow *)
Lemma ck_ra_frame : forall (r1 r2 : Z -> option Z) F fsz p n, F mod 8 = 0 -> fsz mod 8 = 0 ->
  F <= p -> p + n <= F + fsz ->
  (forall i, 0 <= i < fsz / 8 -> r2 (shadow_addr F + i) = r1 (shadow_addr F + i)) ->
  range_addressable r1 SHADOW_OFF p n -> range_addressable r2 SHADOW_OFF p n.
Proof.
intros r1 r2 F fsz p n HF8 Hfs8 Hp1 Hp2 HK. apply range_addressable_agree.
intros x Hx. unfold shadow_of_addr.
assert (Hs : SHADOW_OFF + x / 8 = shadow_addr F + (x - F) / 8).
{ unfold shadow_addr. assert (EF : F = F / 8 * 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
  replace x with ((x - F) + F / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
rewrite Hs. apply HK. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod fsz 8 ltac:(lia)). lia.
Qed.
(* two views agreeing at two addresses agree on the overlay bytes there (YCbq.v mbyte_of_aview, two addresses) *)
Lemma ck_mbyte_of_aview2 : forall segs H H' (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
intros segs H H' m m' a a' E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [b|]; cbn in E;
  try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma ck_preserved : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H. exact Hr. Qed.
Lemma ck_len_snoc : forall {A : Type} (l : list A) x, length (l ++ [x]) = (length l + 1)%nat.
Proof. intros A l x. induction l as [|y l IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.
Ltac ck_notin := let H := fresh in intros H; cbn [In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac ck_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (acallee_saved v) end; unfold acallee_saved; lia.

(* ======================================================================================================== *)
(* the stretch's run is at the cut's float state fxc, the text's post at the entry's fx: the sections below take no
   float state; Section r (a run, at its own fx) and Section m (the entry's fx) do *)
Section w. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation STKR := (@STK_round_trip_text prh_img_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
(* every journal of the walk is at RZW := YA0nH.wle' SEGS RZ_cf (Rtt102Cut.v's rtt_J) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
#[local] Notation RJ := (rtt_J (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
(* the journal a call rule returns from RJ at the call state Sc (Rtt102Cut.v rtt_Jc) *)
#[local] Notation RJc := (rtt_Jc (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation RIN := (@rtt_in _ A_prog_listing PA).

(* ---- engine / instance interface (the brief's category (a)) ---- *)
(* the allocator laws at the cf instance's head (engine fold, YCbqG.v AR_laws_x; S10TxString.v:163) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* The kit's ONE spelling of the head width (PRH_Base.v:187-195; owner the preset instantiation, the cf instance owner's
   preset_head_wide, lib/A/CfParamsPreset.v:95) *)
Hypothesis HW : prh_head_wide.

Section r. Context {fx : YK11.FPState}.
(* ---- 3. a call of a program text from a concrete state (Rtt102FR1Kit.v fr_call_at at 448ecd157e57, =
   YCbqGcall.v:107 aj_call_x_sp without its symbolic-state premise), at RZW: the callee concludes SRr' with its
   journal at RZW (apost_base_xR) ---- *)
Lemma ck_call_at : forall W regs memc STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1 pc
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJ STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regs = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regs) ch1 ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regs memc mdc ch1 ->
   YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regs (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
     (apost_base_xR (SK := SK) SEGS B PST ARx RZW STK1 FP1 regs lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK0 sp0 FP FP1 ly S own lyc Sc ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regs (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    AJ STK0 sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
    AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
    aregs_preserved regs regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regs memc STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 pc Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ apply Hcallee.
  exact (afn_pre_x_atR (SK := SK) SEGS B PST ARx RZW STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regs
    STK1 o ch1
    HJ Hsp' Hal Hneg Hstk1 Hbud ltac:(rewrite Hra; exact Hraw) ltac:(unfold raZ; rewrite Hra; exact Hra4) Hgp Htp
    ltac:(rewrite Hsp'; exact Hch)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
eapply (ajournal_x_subR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf));
  [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* the caller-window post at d = 0 is the journal post (PRH_Base.v fpostWR: the window clause is empty), at RZW *)
Lemma ck_fpostW0 : forall STK FP regs ly S Hp W mem md Q W' c',
  fpostWR (fx := fx) (PI := prh_img_A) (PA := PA) B ARx SK RZW STK 0 FP regs ly S Hp W mem md Q W' c' ->
  apost_base_xR (SK := SK) SEGS B PST ARx RZW STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & Ec & HJ & _ & HAP & HQ).
exists ly', S', Hp', regs', mem', md', k. rewrite !Z.add_0_r in HJ.
exact (conj Ec (conj HJ (conj HAP HQ))).
Qed.
End r.

(* ======================================================================================================== *)
(* from here the entry's float state fx (rtt_pre, rtt_carry, rtt_post take it, BY NAME below) *)
Section m. Context {fx : YK11.FPState}.
#[local] Notation PRE := (rtt_pre (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx CTX0).
#[local] Notation RC := (rtt_carry (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation POST := (rtt_post (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation SEGX := (@RTT_SEG_X fx rc ci cp prh_img_A RL A_prog_listing PA B ARx SK CTX0).

(* ---- 4. the chain at a call in round_trip_text's body (Rtt102FR1KitA.v rtt_keep_above / rtt_chain_at /
   rtt_lyF / rtt_fa_eq at 31b52895a2f, = H5RttS4.v s4_chain) ---- *)
Lemma ck_keep_above : forall D ly S Hp W mem md k pos, RJ D ly S Hp W mem md k pos ->
  forall a, ri_sp D <= a < 2 ^ 64 -> aview SEGS (w_H W) mem a = aview SEGS (w_H (ri_W D)) (ri_mem D) a.
Proof.
intros D ly S Hp W mem md k pos HJ a Ha.
pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_stk HJ) as Hstatic.
pose proof Hstatic as (_ & Hstk0 & Hceil & Hslo & _).
apply F1; lia.
Qed.

Lemma ck_chain_at : forall D ly S Hp W mem md k pos sp1,
  PRE D -> RJ D ly S Hp W mem md k pos -> rtt_saved D W mem ->
  ri_sp D - 192 <= sp1 <= ri_sp D - 16 ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) sp1 (ri_sp D) ch1.
Proof.
intros D ly S Hp W mem md k pos sp1 HP HJ HSV Hsp1.
destruct HP as ((HAFN & _) & _).
pose proof HAFN as (HAR0 & Hra & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
unfold ri_sp in *.
assert (H8 : spZ (ri_regs D) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
assert (Hce : YM05.alloc_ceiling <= spZ (ri_regs D)) by lia.
pose proof (HSV 0%nat ltac:(lia)) as Hw1. pose proof (HSV 1%nat ltac:(lia)) as Hw8.
unfold RTT_SAVED, ri_sp in Hw1, Hw8. cbn [nth Z.of_nat] in Hw1, Hw8.
replace (spZ (ri_regs D) - 8 * (0 + 1)) with (spZ (ri_regs D) - 8) in Hw1 by lia.
replace (spZ (ri_regs D) - 8 * (1 + 1)) with (spZ (ri_regs D) - 16) in Hw8 by lia.
apply ck_rdword_of_val_mem in Hw1; [|exact (bv_unsigned_in_range 64 _)].
apply ck_rdword_of_val_mem in Hw8; [|exact (bv_unsigned_in_range 64 _)].
destruct (Z_le_gt_dec (ly_top ly - 16) (spZ (ri_regs D))) as [Hbad|Hgood].
- exists []. left. split; [right; left; exact Hbad | reflexivity].
- exists ((spZ (ri_regs D), raZ (ri_regs D), s0Z (ri_regs D)) :: ri_ch D). right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, spZ (ri_regs D) <= a -> a < ly_top (ri_ly D) ->
            rdword (aview SEGS (w_H W) mem) a = rdword (aview SEGS (w_H (ri_W D)) (ri_mem D)) a).
  { intros a Ha Hat. apply ts_rdword_keep. intros j Hj.
    apply (ck_keep_above D ly S Hp W mem md k pos HJ). unfold ri_sp. lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact Hw1|]. split; [exact Hw8|]. split; [exact Hra4|].
    destruct (bad_next (spZ (ri_regs D)) (ly_top ly) (s0Z (ri_regs D))) eqn:Eb.
    * destruct Hch as [[_ Hnil] | (Hge & Hlt & Hm8 & _ & _)]; [exact Hnil|].
      exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_true_iff in Eb as [Eb1 | Eb2].
      { apply orb_true_iff in Eb1 as [Eb11 | Eb12].
        - apply Z.leb_le in Eb11. lia.
        - apply Z.leb_le in Eb12. lia. }
      { apply negb_true_iff, Z.eqb_neq in Eb2. exact (Eb2 Hm8). }
    * destruct Hch as [[Hb _] | (Hge & Hlt & Hm8 & Hfp & _)].
      { exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
        apply orb_false_iff in Eb as [Eb1 Eb2]. apply orb_false_iff in Eb1 as [Eb11 Eb12].
        apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12. apply negb_false_iff, Z.eqb_eq in Eb2.
        destruct Hb as [Hb | [Hb | Hb]]; lia. }
      rewrite Etop. apply (ck_fpchain_keep (aview SEGS (w_H (ri_W D)) (ri_mem D))
               (aview SEGS (w_H W) mem) (spZ (ri_regs D))); [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbn beta. intros x Hx. lia.
Qed.

Lemma ck_fa_eq : forall D ly S Hp W mem md k pos, RJ D ly S Hp W mem md k pos ->
  (forall cid pos', frame_addr ly cid pos' = frame_addr (ri_ly D) cid pos') /\
  (forall cid pos', flag_addr ly cid pos' = flag_addr (ri_ly D) cid pos').
Proof.
intros D ly S Hp W mem md k pos HJ. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & E & _).
split; intros cid pos'; unfold frame_addr, flag_addr; rewrite E; reflexivity.
Qed.

(* ---- 5. frame and shadow facts ---- *)
(* EVERY FAKE FRAME OF A NON-NEGATIVE CLASS IS 64-ALIGNED (lane RttO2CK's rtt_frame_al64, Rtt102O2A.v at
   the O2 / CK lane at 6a734ed1713, on WalkRtt102's derivation; restated): frame_addr ly cid pos =
   ly_F ly + kFakeFramesOff + cid * 2 ^ kStackSizeLog + pos * fs_frame_bytes cid, ly_F page aligned by layout_ok's
   lo_F_al, the layout ok by AR_laws_x's field 18 *)
Lemma ck_frame_al64 : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> 0 <= cid ->
  frame_addr ly cid pos mod 64 = 0.
Proof.
intros ly S Hp W mem md cid pos HAR Hc.
pose proof (alx_layout_ok SEGS B ARx LAWS ly S Hp W mem md HAR) as LO.
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL.
apply Z.mod_divide in FAL as [q Hq]; [|lia].
unfold frame_addr, fs_frame_off.
assert (EK : kFakeFramesOff = 576 * 64) by reflexivity.
assert (ES : Z.shiftl 1 kStackSizeLog = 16384 * 64) by reflexivity.
assert (EF : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; apply Z.shiftl_mul_pow2; exact Hc).
rewrite Hq, EK, ES, EF.
replace (q * 4096 + (576 * 64 + cid * (16384 * 64) + pos * (64 * 2 ^ cid)))
  with ((q * 64 + 576 + cid * 16384 + pos * 2 ^ cid) * 64) by ring.
apply Z.mod_mul. lia.
Qed.

(* a byte range inside a live fake frame has its shadow hull visible: the hull's granules are the frame's own shadow
   (the frame 64-aligned, its shadow present by alx_frames) *)
Lemma ck_hull : forall ly S Hp W mem md cid pos p n, ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 0 <= cid ->
  frame_addr ly cid pos <= p -> p + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md cid pos p n HAR Hin Hc Hp1 Hp2 Hn s Hs.
pose proof (ck_frame_al64 ly S Hp W mem md cid pos HAR Hc) as F64.
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & _ & _ & Fsh).
set (F := frame_addr ly cid pos) in *.
assert (Efs : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; apply Z.shiftl_mul_pow2; exact Hc).
assert (Hm : 1 <= 2 ^ cid) by (pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hc); lia).
set (mm := 2 ^ cid) in *.
rewrite Efs in Hp2, Fsh.
assert (Hq : exists q, F = 64 * q) by (exists (F / 64); pose proof (Z.div_mod F 64 ltac:(lia)); lia).
destruct Hq as [q Hq].
assert (Ef8 : (64 * mm) / 8 = 8 * mm) by (replace (64 * mm) with ((8 * mm) * 8) by ring; apply Z.div_mul; lia).
rewrite Ef8 in Fsh.
assert (EsF : shadow_addr F = SHADOW_OFF + 8 * q).
{ unfold shadow_addr. rewrite Hq. replace (64 * q) with ((8 * q) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (H1 : SHADOW_OFF + 8 * q <= s < SHADOW_OFF + 8 * q + 8 * mm).
{ unfold shadow_addr, SHADOW_OFF in *. lia. }
apply ck_aview_of_apresent.
replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
exact (proj1 (Fsh (s - shadow_addr F) ltac:(rewrite EsF; lia))).
Qed.

(* ---- 6. the callee texts, cited (the brief's category (a)) ---- *)
(* The kit's same text at nesting DOC_D (PRH_FnEx.v tsame_specX, blob 45ddb7a7d5ae at walkkit-next de5e947c224b; owned by the kit),
   at any float state (the call is at fxc) *)
Hypothesis TSAME : forall fx' : YK11.FPState, tsame_specX (fx := fx') (PI := prh_img_A) (PA := PA) B ARx SK DOC_D.
(* The kit's pj_free text at nesting DOC_D, the post-implication form with the exact advance (PRH_FnPj.v tpj_free_specX,
   blob 12fa597dc74c at walkkit-next de5e947c224b; owned by the kit), at any float state *)
Hypothesis TPJF : forall fx' : YK11.FPState,
  tpj_free_specX (fx := fx') (PI := prh_img_A) (PA := PA) B ARx SK CTX0 DOC_D.
(* the memcpy interceptor's text with the memnorm keep (YGcallMxmn.v aintrin_realizes_xm, the memcpy row of its
   table, YGcallMxmn.v blob 2b01e06e3fc4; owner a Theorem Labs lane, at the cf instance, its owner's row), at any float state *)
Hypothesis AMCPY : forall fx' : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fx') SEGS B ARx OCpy (SIGMA AS___asan_memcpy).
(* THE HULL'S INSTANCE FACT (added at the Step-2 tip, LAST so no earlier argument moves; CrsSeg_Z.v / CrsSeg_W1.v
   HI_hull, verbatim; instance witness CrsSeg_W1.crs_W1_HI_hull at CfParams_preset): tpj_free_specX now takes the
   hull budget `v <> 0 -> hull_budget S []` (PRH_FnPj.v, its fuzz_free calls). The run's count at the cut's position
   bounds both meters by A17's caps (PresetDrvHullA.drv_cf_hull_ok_at_call_A, a run of at most 4 calls: rtt_pre_os4),
   and this puts those caps within cp's *)
Hypothesis HI_hull : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax cp /\
  PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max cp.

(* ---- 7. the entry's facts ---- *)
Lemma ck_pre_facts : forall D, PRE D ->
  ARx (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) /\
  YM05.alloc_ceiling + STKR <= ri_sp D <= 2 ^ 47 /\ ri_sp D mod 16 = 0 /\ ri_sp D + 64 <= ly_stk_hi (ri_ly D) /\
  (forall bk, In bk (ri_D D) -> In bk (ri_Lam D)) /\
  ri_doc D mod 8 = 0 /\ ck_in_frame (ri_ly D) (ri_S D) (ri_doc D) 56 /\
  range_addressable (aview SEGS (w_H (ri_W D)) (ri_mem D)) SHADOW_OFF (ri_doc D) 56 /\
  (ri_copy D = 0 \/ (ri_copy D mod 8 = 0 /\ ck_in_frame (ri_ly D) (ri_S D) (ri_copy D) 56 /\
     amem_range (ri_copy D) 56 /\
     range_addressable (aview SEGS (w_H (ri_W D)) (ri_mem D)) SHADOW_OFF (ri_copy D) 56 /\
     (ri_copy D + 56 <= ri_doc D \/ ri_doc D + 56 <= ri_copy D))) /\
  (PjTree.depth (ri_t D) <= 32)%nat /\ ri_ran D = 0.
Proof.
intros D HP.
destruct HP as ((HAFN & _ & H64 & _) & _ & _ & _ & _ & _ & _ & _ & _ & HTREE & _ & HDEP & _ & HCOPY & _ & _ & _ &
  HRAN & _).
pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HTREE as (_ & HDL & _ & (Hd8 & Hhome & Hra)).
unfold ri_sp. split; [exact HAR0|]. split; [lia|]. split; [exact Hal16|]. split; [exact H64|].
split; [exact HDL|]. split; [exact Hd8|]. split; [exact Hhome|]. split; [exact Hra|].
split; [| split; [exact HDEP | exact HRAN]].
destruct HCOPY as [H0 | (_ & Hc8 & (Hin & (_ & _ & Ham & _ & Hcra & _)) & Hdisj)]; [left; exact H0|].
right. split; [exact Hc8|]. split; [exact Hin|]. split; [exact Ham|]. split; [exact Hcra | exact Hdisj].
Qed.

Lemma ck_pre_more : forall D, PRE D ->
  prh_univ_closure B CTX0 /\
  prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D)
    (ck_rtt_evs ReaderRes.jr_strtod (ri_t D) (ri_p D) (ri_copy D)).
Proof.
intros D HP.
destruct HP as (_ & _ & HU & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRA & _).
exact (conj HU HRA).
Qed.

(* the shadow of an entry frame is the entry's at every cut (the journal's frame clause; FP is *copy's 56 bytes, in a
   frame, never a shadow byte) *)
Lemma ck_entry_shadow : forall D ly S Hp W mem md k pos cid pos' i, PRE D -> RJ D ly S Hp W mem md k pos ->
  In (cid, pos') (frames (ri_S D)) -> 0 <= i < fs_frame_bytes cid / 8 ->
  aview SEGS (w_H W) mem (shadow_addr (frame_addr (ri_ly D) cid pos') + i) =
  aview SEGS (w_H (ri_W D)) (ri_mem D) (shadow_addr (frame_addr (ri_ly D) cid pos') + i).
Proof.
intros D ly S Hp W mem md k pos cid pos' i HP HJ Hf Hi.
pose proof (ck_pre_facts D HP) as (HAR0 & _ & _ & _ & _ & _ & _ & _ & HC & _).
pose proof (ajxR_frm HJ) as F4.
apply (F4 cid pos' _ Hf); [right; unfold in_zr; cbn [fst snd]; lia|].
intros (r & Hr & Hx). unfold ri_FP in Hr. destruct (ri_copy D =? 0) eqn:Ec; [destruct Hr|].
destruct Hr as [<- | []]. cbn [fst snd] in Hx.
destruct HC as [H0 | (_ & (cid2 & pos2 & Hf2 & Hc1 & Hc2) & _)]; [apply Z.eqb_neq in Ec; contradiction|].
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ cid2 pos2 HAR0 Hf2) as (_ & _ & Happ2).
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ cid pos' HAR0 Hf) as (_ & _ & Happ).
pose proof (fs_frame_bytes_nonneg cid). pose proof (fs_frame_bytes_nonneg cid2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hdv : fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, ASAN_CEIL in *. lia.
Qed.

(* doc's and *copy's 56 bytes are addressable at every cut (their entry frame's shadow is kept) *)
Lemma ck_obj_ra : forall D ly S Hp W mem md k pos p cid pos', PRE D -> RJ D ly S Hp W mem md k pos ->
  In (cid, pos') (frames (ri_S D)) -> frame_addr (ri_ly D) cid pos' <= p ->
  p + 56 <= frame_addr (ri_ly D) cid pos' + fs_frame_bytes cid ->
  range_addressable (aview SEGS (w_H (ri_W D)) (ri_mem D)) SHADOW_OFF p 56 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 56.
Proof.
intros D ly S Hp W mem md k pos p cid pos' HP HJ Hf Hp1 Hp2 Hra.
pose proof (ck_pre_facts D HP) as (HAR0 & _).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ cid pos' HAR0 Hf) as (F32 & _).
assert (Hc : 0 <= cid) by (apply ck_fs_cid; lia).
destruct (ck_fs8 cid Hc) as [Hfs8 _].
apply (ck_ra_frame (aview SEGS (w_H (ri_W D)) (ri_mem D)) _ (frame_addr (ri_ly D) cid pos') (fs_frame_bytes cid) p 56);
  [| exact Hfs8 | exact Hp1 | exact Hp2 | | exact Hra].
- apply Z.mod_divide; [lia|]. apply Z.mod_divide in F32; [|lia]. destruct F32 as [q Hq]. exists (4 * q). lia.
- intros i Hi. exact (ck_entry_shadow D ly S Hp W mem md k pos cid pos' i HP HJ Hf Hi).
Qed.

(* a footprint in a frame and in ledger blocks lies below the ceiling, so off every stack window *)
Lemma ck_foot_low : forall ly S Hp W mem md Lamc peak cnt fail ran most own p D cid pos,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lamc peak cnt fail ran most own ->
  In (cid, pos) (frames S) -> frame_addr ly cid pos <= p -> p + 56 <= frame_addr ly cid pos + fs_frame_bytes cid ->
  (forall bk, In bk D -> In bk Lamc) ->
  forall z, pj_footR p D z -> z < YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lamc peak cnt fail ran most own p D cid pos HAR HL Hf Hp1 Hp2 HD z [Hz | ((a, k) & Hb & Hz)].
- destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ cid pos HAR Hf) as (_ & Hb2 & _). lia.
- unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL (HD _ Hb)) as (Hk0 & Hab & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hce & _).
  pose proof HW as HW'. unfold prh_head_wide in HW'.
  assert (Hn0 : 0 <= k + cf_head) by lia.
  pose proof (req_size_pos (k + cf_head) Hn0) as [_ Hrq]. lia.
Qed.

(* The kit's fpre at a call of the stretch *)
Lemma ck_fpre : forall (fxc : YK11.FPState) D lyc Sc Hpc Wc memc mdc kc pos STK1 regsT ch1, PRE D ->
  RJ D lyc Sc Hpc Wc memc mdc kc pos ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) ->
  afn_pre_x SEGS B ARx STK1 lyc Sc Hpc Wc regsT memc mdc ch1 -> spZ regsT <= ri_sp D ->
  raZ regsT < YM05.alloc_ceiling -> frm_zero (@YK11.fp_csr fxc) ->
  fpre (fx := fxc) (PA := PA) B ARx STK1 lyc Sc Hpc Wc regsT memc mdc ch1.
Proof.
intros fxc D lyc Sc Hpc Wc memc mdc kc pos STK1 regsT ch1 HP HJ HRO HAFN Hsp Hra Hfrm.
pose proof (ck_pre_facts D HP) as (_ & _ & _ & H64 & _).
pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _).
split; [exact HAFN|]. split; [exact HRO|]. split; [lia|]. split; [exact Hra | exact Hfrm].
Qed.

(* rodata lies in the image (Rtt102FR1KitA.v rtt_ro_img, S10TxStrGlue.v ts_ro_img) *)
Lemma ck_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* ---- 8. what a call keeps (Rtt102FR1KitA.v rtt_kept / rtt_kept_of_journal of lane RttFR1,
   the RttFR1 lane at ec69f124f67, restated) and the write-set bound of this stretch ---- *)
Definition ck_kept (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mem2 : word -> option byte)
  (slo shi : Z) (E : Z -> Prop) (P : list (Z * Z)) : Prop :=
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H Wc) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) P -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).

Lemma ck_kept_of_journal : forall STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ~ YI16.sink_open_fp FP1 ->
  ck_kept lyc Sc Wc memc ly2 S2 W2 mem2 (sp1 - STK1) sp1 (inFP FP1) PST.
Proof.
intros STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 HJ Hcl.
pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3.
pose proof (ajxR_frm HJ) as F4.
split; [exact F1|]. split; [exact F2|].
split; [intros a Hi Ho He Hp; exact (F3 a Hi Ho He Hp (fp_spares_closed FP1 a Hcl))|].
exact F4.
Qed.

(* the bytes the carried state reads: the entry's harness blocks, the own frame's flag-pointer word, doc's node
   (FINER than Rtt102FR1KitA.v rtt_off, which excludes every live frame: *copy and back are written here) *)
Definition ck_off (D : RIN) (lyc : alayout) (pos x : Z) : Prop :=
  (forall a k, In (a, k) (ri_Lam D) -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head))) /\
  ~ (frame_addr lyc RT_CID pos + RT_FLAGP <= x < frame_addr lyc RT_CID pos + RT_FLAGP + 8) /\
  ~ (ri_doc D <= x < ri_doc D + 56).

(* the registers the prologue fixed survive a write of any other register, and a call *)
Lemma ck_cregs_upd : forall (D : RIN) ly regs pos (r : bv 5) v, ~ In r [2; 8; 9; 18; 19; 20; 25; 26; 3; 4]%bv ->
  rtt_cregs B D ly regs pos -> rtt_cregs B D ly (regupd regs r v) pos.
Proof.
intros D ly regs pos r v Hr H.
assert (G : forall r', In r' [2; 8; 9; 18; 19; 20; 25; 26; 3; 4]%bv -> getr (regupd regs r v) r' = getr regs r').
{ intros r' Hin. apply getr_other. intros E. subst r'. exact (Hr Hin). }
unfold rtt_cregs in *. cbv zeta in *.
destruct H as (H2 & H8 & H9 & H18 & H19 & H20 & H25 & H26 & H3 & H4).
rewrite !G by (cbn [In]; repeat (first [left; reflexivity | right])).
exact (conj H2 (conj H8 (conj H9 (conj H18 (conj H19 (conj H20 (conj H25 (conj H26 (conj H3 H4))))))))).
Qed.
Lemma ck_cregs_pres : forall (D : RIN) ly regs regs' pos, aregs_preserved regs regs' ->
  rtt_cregs B D ly regs pos -> rtt_cregs B D ly regs' pos.
Proof.
intros D ly regs regs' pos HAP H. unfold rtt_cregs in *. cbv zeta in *.
destruct H as (H2 & H8 & H9 & H18 & H19 & H20 & H25 & H26 & H3 & H4).
assert (G : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r)
  by (intros r Hr; exact (ck_preserved regs regs' r HAP Hr)).
rewrite !G by ck_cs.
exact (conj H2 (conj H8 (conj H9 (conj H18 (conj H19 (conj H20 (conj H25 (conj H26 (conj H3 H4))))))))).
Qed.
Lemma ck_cregs_ly : forall (D : RIN) ly ly' regs pos,
  (forall cid pos', frame_addr ly' cid pos' = frame_addr ly cid pos') ->
  rtt_cregs B D ly regs pos -> rtt_cregs B D ly' regs pos.
Proof. intros D ly ly' regs pos Fa H. unfold rtt_cregs in *. cbv zeta in *. rewrite !Fa. exact H. Qed.

(* the realigned sp: 160 .. 191 below the entry sp, 32-aligned, the offset 16-aligned (Rtt102R1A.v r1_sp1) *)
Lemma ck_sp1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 192 <= RT_R sp0 <= sp0 - 160 /\ (RT_R sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H. unfold RT_R, RT_FRAME.
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as Hm.
split; [lia|].
assert (E : sp0 - 160 - (sp0 - 160) mod 32 - sp0 = - 160 - (sp0 - 160) mod 32) by lia. rewrite E.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd2. rewrite H in Hd2.
lia.
Qed.

Lemma ck_vaddi0 : forall x, v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma ck_sigma : SIGMA AS_round_trip_text = BASE + RTT_PC_A.
Proof. vm_compute. reflexivity. Qed.
Lemma ck_stkr : STKR = 27392.
Proof. vm_compute. reflexivity. Qed.

(* ======================================================================================================== *)

Lemma ck_carry_md : forall D fxc ly S Hp W regs mem md k pos mat,
  RC D fxc ly S Hp W regs mem md k pos -> RC D fxc ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) mat md) k pos.
Proof.
intros D fxc ly S Hp W regs mem md k pos mat (HFX & HJ & HR). split; [exact HFX|]. split; [|exact HR].
unfold rtt_J in *. apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW). exact HJ.
Qed.
Lemma ck_carry_upd : forall D fxc ly S Hp W regs mem md k pos (r : bv 5) v,
  ~ In r [2; 8; 9; 18; 19; 20; 25; 26; 3; 4]%bv ->
  RC D fxc ly S Hp W regs mem md k pos -> RC D fxc ly S Hp W (regupd regs r v) mem md k pos.
Proof.
intros D fxc ly S Hp W regs mem md k pos r v Hr (HFX & HJ & HFR & HSV & HCR & HR).
exact (conj HFX (conj HJ (conj HFR (conj HSV (conj (ck_cregs_upd D ly regs pos r v Hr HCR) HR))))).
Qed.

(* ---- 9. THE CARRIED STATE ACROSS A CALL whose keeps are ck_kept and whose write set misses ck_off
   (Rtt102FR1KitA.v rtt_carry_keep at ec69f124f67, restated with the finer bound) ---- *)
Lemma ck_carry_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 Hp2 W2 regs2 mem2 md2 k2 slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2,
  PRE D ->
  RC D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  RJc D Sc ly2 S2 Hp2 W2 mem2 md2 k2 pos ->
  frames S2 = frames Sc ->
  ck_kept lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  shi <= ri_sp D - 104 ->
  (forall a, Exists (in_zr a) P -> Exists (in_zr a) PST) ->
  (forall x, E x -> ck_off D lyc pos x) ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> incl (ri_Lam D) Lamc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 -> incl (ri_Lam D) Lam2 ->
  rtt_cregs B D ly2 regs2 pos ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  rtt_room D S2 ->
  RC D fxc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 Hp2 W2 regs2 mem2 md2 k2 slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2
  HP HC HJ2 HFR HK Hshi HPP HEoff HLc Hincc HL2 Hinc2 HCR2 HMN2 HROOM2.
pose proof (ck_pre_facts D HP) as (HAR0 & Hsp0 & Hsp16 & _ & HDL & _ & (cidd & posd & Hfd & Hd1 & Hd2) & _).
pose proof HC as (HFX & HJc & HFRc & HSVc & _ & HMNc & HRODc & _ & HNODEc & HVISc & HWc).
pose proof HK as (K1 & K2 & K3 & K4).
pose proof (ajxR_ar HJ2) as HAR2.
(* the call rule's caller journal (from RJ at Sc) is RJ at the new state *)
assert (HJ2' : RJ D ly2 S2 Hp2 W2 mem2 md2 k2 pos) by (eapply rtt_J_of_Jc; exact HJ2).
destruct (ck_fa_eq D lyc Sc Hpc Wc memc mdc kc pos HJc) as (Fac & Flc).
destruct (ck_fa_eq D ly2 S2 Hp2 W2 mem2 md2 k2 pos HJ2') as (Fa2 & Fl2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ck_stkr as HSTKv.
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
pose proof HW as HW'. unfold prh_head_wide in HW'.
destruct HFRc as (Efr & Hni & Hflag & Hfpres).
assert (HF0c : forall cid pos', In (cid, pos') (frames (ri_S D)) -> In (cid, pos') (frames Sc))
  by (intros cid pos' Hf; rewrite Efr; right; exact Hf).
assert (HF02 : forall cid pos', In (cid, pos') (frames (ri_S D)) -> In (cid, pos') (frames S2))
  by (intros cid pos' Hf; rewrite HFR; exact (HF0c cid pos' Hf)).
(* a byte of an entry harness block is kept *)
assert (KB : forall a k x, In (a, k) (ri_Lam D) -> a - cf_head <= x < a - cf_head + req_size (k + cf_head) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
{ intros a k x Hin Hx.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLc (Hincc _ Hin)) as (_ & Hbc & _).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL2 (Hinc2 _ Hin)) as (_ & Hb2 & _).
  replace x with (a - cf_head + (x - (a - cf_head))) by lia.
  apply (K2 (a - cf_head) (k + cf_head) (x - (a - cf_head)) Hbc Hb2); [lia|].
  intros HE. destruct (HEoff _ HE) as (Hbl & _). apply (Hbl a k Hin). lia. }
(* doc's 56 bytes are kept *)
assert (KD : forall x, ri_doc D <= x < ri_doc D + 56 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
{ intros x Hx. apply (K4 cidd posd x (HF0c cidd posd Hfd)).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac. lia.
  - intros HE. destruct (HEoff _ HE) as (_ & _ & Hn). exact (Hn Hx). }
split; [exact HFX|].
split; [exact HJ2'|].
split.
{ (* rtt_frame *)
  split; [rewrite HFR; exact Efr|]. split; [exact Hni|]. split.
  - rewrite Fa2, Fl2. rewrite Fac, Flc in Hflag. rewrite <- Hflag. apply ts_rdword_keep. intros j Hj.
    apply (K4 RT_CID pos); [rewrite Efr; left; reflexivity | left | ].
    + unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac, Efs1. unfold RT_FLAGP. lia.
    + intros HE. destruct (HEoff _ HE) as (_ & Hn & _). apply Hn. rewrite Fac. lia.
  - intros a Ha. destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 RT_CID pos HAR2
      ltac:(rewrite HFR, Efr; left; reflexivity)) as (_ & _ & Hpr & _).
    exact (proj1 (Hpr a Ha)). }
split.
{ (* rtt_saved *)
  intros j Hj. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2); [|exact (HSVc j Hj)].
  intros i Hi. apply K1; unfold ri_sp in *; lia. }
split; [exact HCR2|].
split; [intros H; exact (HMN2 (HMNc H))|].
split.
{ (* the read-only view *)
  intros a Hro Hown Herr. rewrite (K3 a (ck_ro_img a Hro) Hown Herr).
  - exact (HRODc a Hro Hown Herr).
  - intros HPa. exact (pst_not_ro_A a (HPP a HPa) Hro). }
split; [exact HROOM2|].
split.
{ (* doc's tree *)
  apply (pj_nodeR_frame SEGS _ _ _ _ _ _ HNODEc). intros x Hx.
  destruct Hx as [Hx | ((a, k) & HinD & Hx)].
  - split; [apply mbyte_of_aview; exact (KD x Hx)|].
    intros _. apply apresent_writable.
    destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 cidd posd HAR2 (HF02 cidd posd Hfd)) as (_ & _ & Hpr & _).
    apply (Hpr x). rewrite Fa2. lia.
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (HDL _ HinD) as HinL.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL2 (Hinc2 _ HinL)) as (Hk0 & Hb2 & _).
    assert (Hn0 : 0 <= k + cf_head) by lia.
    pose proof (req_size_pos (k + cf_head) Hn0) as Hrq.
    assert (Hx' : a - cf_head <= x < a - cf_head + req_size (k + cf_head)) by lia.
    split; [apply mbyte_of_aview; exact (KB a k x HinL Hx')|].
    intros _. apply apresent_writable.
    destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2)
      as (_ & _ & _ & _ & Hpr & _).
    exact (proj1 (Hpr x Hx')). }
split.
{ (* the tree's visibility, re-derived at the new state from the harness-block laws *)
  unfold PRH_FnWriter.prhWriter_tree_vis, YGcfTreeVis.tree_vis_cf in *. intros a k HinD.
  destruct (HVISc a k HinD) as (V1 & V2 & V3 & V4 & _ & _ & _).
  pose proof (HDL _ HinD) as HinL.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL2 (Hinc2 _ HinL)) as (Hk0 & Hb2 & Hh2 & _).
  assert (Hn0 : 0 <= k + cf_head) by lia.
  pose proof (req_size_pos (k + cf_head) Hn0) as Hrq.
  destruct (alx_hshadow _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2 Hh2) as (Hbs & Hhull).
  replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia.
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2)
    as (_ & _ & _ & _ & Hpr & _).
  split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|].
  split.
  { intros x Hx. exact (block_shadow_range _ _ _ _ a k Hbs ltac:(lia) ltac:(lia) x Hx). }
  split.
  { intros Hk. assert (Er : req_size (k + cf_head) = k + cf_head)
      by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    rewrite Er in Hhull. replace (k + cf_head - cf_head) with k in Hhull by lia. apply Hhull. lia. }
  intros x Hx.
  destruct (Z_lt_le_dec x (a - cf_head + req_size (k + cf_head))) as [Hin | Hge].
  - apply ck_aview_of_apresent. exact (proj1 (Hpr x ltac:(lia))).
  - apply (alx_blocks_tail _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) x HAR2 Hb2).
    assert (Hmono : (a + k + 7) / 8 <= (a - cf_head + req_size (k + cf_head) + 7) / 8) by (apply Z.div_le_mono; lia).
    lia. }
(* the wild traces: the call stored none beyond the caller journal's (Rtt102Cut.v rtt_wild_Jc) *)
eapply rtt_wild_Jc; [exact HWc | exact HJ2].
Qed.

(* back (F + 32, 56 bytes) stays unpoisoned across a call whose write set misses the own frame's shadow *)
Lemma ck_back_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E P,
  RC D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  ck_kept lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  (forall x, E x -> ~ (shadow_addr (frame_addr lyc RT_CID pos) <= x < shadow_addr (frame_addr lyc RT_CID pos) + 16)) ->
  (forall cid pos', frame_addr ly2 cid pos' = frame_addr lyc cid pos') ->
  rtt_back lyc Wc memc pos -> rtt_back ly2 W2 mem2 pos.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E P HC HK HEsh Fa2 HB.
pose proof HC as (_ & HJc & (Efr & _ & _ & _) & _).
pose proof (ajxR_ar HJc) as HARc.
pose proof HK as (_ & _ & _ & K4).
assert (Hin : In (RT_CID, pos) (frames Sc)) by (rewrite Efr; left; reflexivity).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc RT_CID pos HARc Hin) as (F32 & _).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
unfold rtt_back in *. rewrite Fa2.
apply (ck_ra_frame (aview SEGS (w_H Wc) memc) _ (frame_addr lyc RT_CID pos) 128);
  [| reflexivity | unfold RT_BACK; lia | unfold RT_BACK; lia | | exact HB].
- apply Z.mod_divide; [lia|]. apply Z.mod_divide in F32; [|lia]. destruct F32 as [q Hq]. exists (4 * q). lia.
- intros i Hi. change (128 / 8) with 16 in Hi.
  apply (K4 RT_CID pos); [exact Hin | right; unfold in_zr; cbn [fst snd]; rewrite Efs1; change (128 / 8) with 16; lia |].
  intros HE. apply (HEsh _ HE). lia.
Qed.

(* ---- 10. where the stretch writes, against ck_off ---- *)
Lemma ck_rc_frames : forall D fxc ly S Hp W regs mem md k pos, RC D fxc ly S Hp W regs mem md k pos ->
  ARx ly S Hp W mem md /\ frames S = (RT_CID, pos) :: frames (ri_S D) /\ ~ In (RT_CID, pos) (frames (ri_S D)) /\
  (forall cid pos', frame_addr ly cid pos' = frame_addr (ri_ly D) cid pos').
Proof.
intros D fxc ly S Hp W regs mem md k pos (_ & HJ & (Efr & Hni & _) & _).
pose proof (ajxR_ar HJ) as HAR. destruct (ck_fa_eq D ly S Hp W mem md k pos HJ) as (Fa & _).
exact (conj HAR (conj Efr (conj Hni Fa))).
Qed.

(* an entry frame and the own frame are apart *)
Lemma ck_own_apart : forall D fxc ly S Hp W regs mem md k pos cid pos', RC D fxc ly S Hp W regs mem md k pos ->
  In (cid, pos') (frames (ri_S D)) ->
  zdisjoint (frame_rng ly (RT_CID, pos)) (frame_rng ly (cid, pos')).
Proof.
intros D fxc ly S Hp W regs mem md k pos cid pos' HC Hf.
destruct (ck_rc_frames D fxc ly S Hp W regs mem md k pos HC) as (HAR & Efr & _ & _).
destruct (in_split _ _ Hf) as (l2 & l3 & El).
apply (sep_frames_pos_x _ _ _ LAWS ly S Hp W mem md (RT_CID, pos) (cid, pos') [] l2 l3 HAR).
rewrite Efr, El. reflexivity.
Qed.

(* a byte of an entry frame, off doc's node *)
Lemma ck_off_entry : forall D fxc ly S Hp W regs mem md k pos Lamc peak cnt fail ran most own cid pos' x,
  RC D fxc ly S Hp W regs mem md k pos -> prh_ledger B ly S Hp W mem Lamc peak cnt fail ran most own ->
  incl (ri_Lam D) Lamc -> In (cid, pos') (frames (ri_S D)) ->
  frame_addr ly cid pos' <= x < frame_addr ly cid pos' + fs_frame_bytes cid -> ~ (ri_doc D <= x < ri_doc D + 56) ->
  ck_off D ly pos x.
Proof.
intros D fxc ly S Hp W regs mem md k pos Lamc peak cnt fail ran most own cid pos' x HC HL Hinc Hf Hx Hnd.
destruct (ck_rc_frames D fxc ly S Hp W regs mem md k pos HC) as (HAR & Efr & _ & _).
assert (Hfs : In (cid, pos') (frames S)) by (rewrite Efr; right; exact Hf).
pose proof (ck_own_apart D fxc ly S Hp W regs mem md k pos cid pos' HC Hf) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
split; [|split; [|exact Hnd]].
- intros a k0 Hin Hx2.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HL (Hinc _ Hin)) as (_ & Hab & _).
  pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md _ _ cid pos' HAR Hab Hfs) as Hd2.
  unfold zdisjoint in Hd2. cbn [fst snd] in Hd2. lia.
- rewrite Efs1 in Hd. unfold RT_FLAGP. lia.
Qed.

(* a byte of back (F + 32 .. F + 88) *)
Lemma ck_off_back : forall D fxc ly S Hp W regs mem md k pos Lamc peak cnt fail ran most own x, PRE D ->
  RC D fxc ly S Hp W regs mem md k pos -> prh_ledger B ly S Hp W mem Lamc peak cnt fail ran most own ->
  incl (ri_Lam D) Lamc ->
  frame_addr ly RT_CID pos + RT_BACK <= x < frame_addr ly RT_CID pos + RT_BACK + 56 ->
  ck_off D ly pos x.
Proof.
intros D fxc ly S Hp W regs mem md k pos Lamc peak cnt fail ran most own x HP HC HL Hinc Hx.
destruct (ck_rc_frames D fxc ly S Hp W regs mem md k pos HC) as (HAR & Efr & _ & Fa).
pose proof (ck_pre_facts D HP) as (_ & _ & _ & _ & _ & _ & (cidd & posd & Hfd & Hd1 & Hd2) & _).
assert (Hin : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
unfold RT_BACK in Hx.
split; [|split].
- intros a k0 Hin0 Hx2.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HL (Hinc _ Hin0)) as (_ & Hab & _).
  pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md _ _ RT_CID pos HAR Hab Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efs1 in Hd. lia.
- unfold RT_FLAGP. lia.
- pose proof (ck_own_apart D fxc ly S Hp W regs mem md k pos cidd posd HC Hfd) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Efs1, !Fa in Hd. rewrite Fa in Hx. lia.
Qed.

(* a byte of a live block that is not one of the entry's *)
Lemma ck_off_newblk : forall D fxc ly S Hp W regs mem md k pos Lamc peak cnt fail ran most own b m x, PRE D ->
  RC D fxc ly S Hp W regs mem md k pos -> prh_ledger B ly S Hp W mem Lamc peak cnt fail ran most own ->
  incl (ri_Lam D) Lamc ->
  In (b, m) (ablocks B ly S) -> ~ In (b, m) (ablocks B (ri_ly D) (ri_S D)) -> b <= x < b + req_size m ->
  ck_off D ly pos x.
Proof.
intros D fxc ly S Hp W regs mem md k pos Lamc peak cnt fail ran most own b m x HP HC HL Hinc Hb Hnb Hx.
destruct (ck_rc_frames D fxc ly S Hp W regs mem md k pos HC) as (HAR & Efr & _ & Fa).
pose proof (ck_pre_facts D HP) as (_ & _ & _ & _ & _ & _ & (cidd & posd & Hfd & Hd1 & Hd2) & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _).
assert (Hin : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
assert (Hfs : In (cidd, posd) (frames S)) by (rewrite Efr; right; exact Hfd).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
split; [|split].
- intros a k0 Hin0 Hx2.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HLED0 Hin0) as (_ & Hab0 & _).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HL (Hinc _ Hin0)) as (_ & Hab & _).
  assert (Hne : (b, m) <> (a - cf_head, k0 + cf_head)) by (intros E; rewrite E in Hnb; exact (Hnb Hab0)).
  pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md _ _ _ _ HAR Hb Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md _ _ RT_CID pos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efs1 in Hd. unfold RT_FLAGP. lia.
- pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md _ _ cidd posd HAR Hb Hfs) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Fa in Hd. lia.
Qed.

(* ---- 11. the trees at a cut, as the kit's same text reads them ---- *)
Lemma ck_doc_tree : forall D fxc ly S Hp W regs mem md k pos Lamc, PRE D -> RC D fxc ly S Hp W regs mem md k pos ->
  incl (ri_Lam D) Lamc ->
  prhex_tree (PA := PA) ly S Lamc W regs mem (ri_doc D) (ri_t D) (ri_D D).
Proof.
intros D fxc ly S Hp W regs mem md k pos Lamc HP HC Hinc.
pose proof (ck_pre_facts D HP) as (_ & _ & _ & _ & _ & _ & (cid & pos' & Hf & Hd1 & Hd2) & Hra & _).
pose proof HC as (_ & HJ & _ & _ & _ & _ & _ & _ & HND & _).
destruct (ck_rc_frames D fxc ly S Hp W regs mem md k pos HC) as (HAR & Efr & _ & Fa).
assert (Hfc : In (cid, pos') (frames S)) by (rewrite Efr; right; exact Hf).
assert (Hc : 0 <= cid) by (apply ck_fs_cid; lia).
unfold prhex_tree. split; [|split; [|split]].
- apply (rx_nodeR_lblk SEGS _ _ (prh_lin (ri_Lam D))); [exact HND|].
  intros x k0 _ Hl. unfold prh_lin in *. exact (Hinc _ Hl).
- right; left. exists cid, pos'. rewrite Fa. split; [exact Hfc | lia].
- exact (ck_obj_ra D ly S Hp W mem md k pos (ri_doc D) cid pos' HP HJ Hf Hd1 Hd2 Hra).
- apply (ck_hull ly S Hp W mem md cid pos' (ri_doc D) 56 HAR Hfc Hc); rewrite ?Fa; lia.
Qed.

Lemma ck_back_tree : forall D fxc ly S Hp W regs mem md k pos Lamc Db, RC D fxc ly S Hp W regs mem md k pos ->
  rtt_back ly W mem pos ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lamc) (frame_addr ly RT_CID pos + RT_BACK) (ri_t D) Db ->
  prhex_tree (PA := PA) ly S Lamc W regs mem (frame_addr ly RT_CID pos + RT_BACK) (ri_t D) Db.
Proof.
intros D fxc ly S Hp W regs mem md k pos Lamc Db HC HBK HN.
destruct (ck_rc_frames D fxc ly S Hp W regs mem md k pos HC) as (HAR & Efr & _ & _).
assert (Hin : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
unfold prhex_tree. split; [exact HN|]. split; [|split].
- right; left. exists RT_CID, pos. split; [exact Hin|]. rewrite Efs1. unfold RT_BACK. lia.
- exact HBK.
- apply (ck_hull ly S Hp W mem md RT_CID pos _ 56 HAR Hin ltac:(vm_compute; discriminate)); rewrite ?Efs1;
    unfold RT_BACK; lia.
Qed.

(* ---- 12. the state from RT_CK to the split at +848: rtt_at_ck's not-ran-out arm (the ran-out arm is refuted:
   ran = 0 at entry) ---- *)
Definition ck_mid (D : RIN) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  RC D fxc ly S Hp W regs mem md k pos /\ rtt_back ly W mem pos /\
  getr regs 23 = w64 (frame_addr ly RT_CID pos + RT_BACK) /\ rtt_pos D S (RT_K_T D) /\
  exists Lamr peakr Db,
    rtt_led (PI := prh_img_A) B D ly S Hp W mem Lamr peakr
      (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) + Z.of_nat (PjRoundTrip.tcalls (ri_t D))) (ri_ran D) 0 /\
    Permutation Lamr (Db ++ ri_Lam D) /\
    (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B (ri_ly D) (ri_S D))) /\
    Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace (ri_t D)))) /\
    (cf_head = PresetReqAt.HEAD ->
       Permutation (map (fun b => snd b + cf_head) Db)
         (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc (ri_t D) (ri_p D))))) /\
    (exists F, pj_foR SEGS (mrestrict (w_H W) mem) (prh_lin Lamr) DOC_D (frame_addr ly RT_CID pos + RT_BACK) Db F /\
       map (fun b => snd b + cf_head) F = PresetReqAt.fo (ri_t D)) /\
    Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace (ri_t D)) /\
    Permutation (ablocks B ly S) (ablocks B (ri_ly D) (ri_S D) ++ ck_hblks Db) /\
    pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lamr) (frame_addr ly RT_CID pos + RT_BACK) (ri_t D) Db /\
    (* rtt_rb's two last conjuncts: back's free order at every depth bound over the reader's pj_frees, K0-CAP *)
    (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (ri_t D) <= nn)%nat ->
       exists F, pj_foR SEGS (mrestrict (w_H W) mem) (prh_lin Lamr) nn (frame_addr ly RT_CID pos + RT_BACK) Db F /\
         map (fun b => snd b + cf_head) F =
           PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc (ri_t D) (ri_p D))) /\
    pj_ncapR SEGS (mrestrict (w_H W) mem) (frame_addr ly RT_CID pos + RT_BACK) (ri_t D).

Lemma ck_mid_of_ck : forall D fxc ly S Hp W regs mem md k pos, PRE D ->
  rtt_at_ck (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK D fxc ly S Hp W regs mem md k pos ->
  ck_mid D fxc ly S Hp W regs mem md k pos /\ getr regs 24 = w64 0.
Proof.
intros D fxc ly S Hp W regs mem md k pos HP (HC & HBK & R23 & R24 & Lamr & peakr & HLED & HRB).
split; [|exact R24].
destruct HRB as (_ & _ & _ & HPOS & Db & HPL & HDb & HDs & HTB & HFOF & HDn & HPB & HNB & HFRS & HCAP).
split; [exact HC|]. split; [exact HBK|]. split; [exact R23|]. split; [exact HPOS|].
exists Lamr, peakr, Db.
exact (conj HLED (conj HPL (conj HDb (conj HDs (conj HTB (conj HFOF (conj HDn (conj HPB (conj HNB
  (conj HFRS HCAP)))))))))).
Qed.

Lemma ck_mid_md : forall D fxc ly S Hp W regs mem md k pos mat, ck_mid D fxc ly S Hp W regs mem md k pos ->
  ck_mid D fxc ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) mat md) k pos.
Proof.
intros D fxc ly S Hp W regs mem md k pos mat (HC & HR). exact (conj (ck_carry_md D fxc ly S Hp W regs mem md k pos mat HC) HR).
Qed.

(* ---- 13. the tail +880 .. +884: s5 := 0, j RT_X ---- *)
Lemma ck_tail : forall D fxc ly S Hp W regs mem md k pos,
  PRE D -> SEGX -> RC D fxc ly S Hp W regs mem md k pos -> rtt_Qx (PI := prh_img_A) B D ly S Hp W mem 0 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_PC_A + 880))) mem (YK11.seg_rom SEGS)) md) (POST D).
Proof.
intros D fxc ly S Hp W regs mem md k pos HP SX HC HQx.
eapply (ck_addi (fx := fxc) (PL := PL) (PI := PA) W regs mem md _ _ (RTT_PC_A + 880) _ _ _ 21%bv 0%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity | intros mat1].
eapply (ck_j (fx := fxc) (PI := PA) W _ mem _ _ _ (RTT_PC_A + 880 + 4) (SIGMA AS_round_trip_text + RT_X));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | intros mat2].
unfold RTT_SEG_X, rtt_seg in SX.
apply (SX D HP fxc ly S Hp W _ mem _ k pos).
unfold rtt_at_x. split.
- apply ck_carry_md. apply ck_carry_md. apply ck_carry_upd; [ck_notin | exact HC].
- exists 0. split; [|exact HQx].
  rewrite getr_same by reg_neq_tac. rewrite getr_zero. apply bv_eq. vm_compute. reflexivity.
Qed.

(* +868 j +880, then the tail, in a small context (the same step inside ck_arm1's context ran past a 240 s sentence
   timeout at its first vm_compute, builds a9fb6693e55 and 3e18a45b064) *)
Lemma ck_tail868 : forall D fxc ly S Hp W regs mem md k pos,
  PRE D -> SEGX -> RC D fxc ly S Hp W regs mem md k pos -> rtt_Qx (PI := prh_img_A) B D ly S Hp W mem 0 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_PC_A + 848 + 4 + 4 + 4 + 4 + 4))) mem
    (YK11.seg_rom SEGS)) md) (POST D).
Proof.
intros D fxc ly S Hp W regs mem md k pos HP SX HC HQx.
eapply (ck_j (fx := fxc) (PI := PA) W regs mem md _ _ (RTT_PC_A + 848 + 4 + 4 + 4 + 4 + 4) (BASE + (RTT_PC_A + 880)));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | intros mat5].
apply (ck_tail D fxc ly S Hp W regs mem _ k pos HP SX); [apply ck_carry_md; exact HC | exact HQx].
Qed.

(* register facts after the stretch's writes *)
Ltac ck_rg := repeat first [rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac].

(* ---- 14. *copy <> 0: li a2, 56; mv a0, s3; mv a1, s7; jal __asan_memcpy; j +880. The tree moves to *copy ---- *)
Lemma ck_arm1 : forall D fxc ly S Hp W regs mem md k pos,
  PRE D -> SEGX -> ri_copy D <> 0 -> ck_mid D fxc ly S Hp W regs mem md k pos ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_PC_A + 848 + 4))) mem (YK11.seg_rom SEGS)) md)
    (POST D).
Proof.
intros D fxc ly S Hp W regs mem md k pos HP SX Hc1 HM.
pose proof HM as (HC & HBK & R23 & HPOS & Lamr & peakr & Db & (HLED & HPK) & HPL & HDbn & HDs & HTB & HFOF & HDn &
  HPB & HNB & HFRS & HCAP).
pose proof HC as (_ & _ & _ & _ & HCR & _ & _ & HRL & _ & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
(* +852 li a2, 0x38 *)
eapply (ck_addi (fx := fxc) (PL := PL) (PI := PA) W regs mem md _ _ (RTT_PC_A + 848 + 4) _ _ _ 12%bv 0%bv 56);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity | intros mat1].
(* +856 mv a0, s3 *)
eapply (ck_addi (fx := fxc) (PL := PL) (PI := PA) W _ mem _ _ _ (RTT_PC_A + 848 + 4 + 4) _ _ _ 10%bv 19%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity | intros mat2].
(* +860 mv a1, s7 *)
eapply (ck_addi (fx := fxc) (PL := PL) (PI := PA) W _ mem _ _ _ (RTT_PC_A + 848 + 4 + 4 + 4) _ _ _ 11%bv 23%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity | intros mat3].
(* +864 jal __asan_memcpy *)
eapply (ck_jal (fx := fxc) (PI := PA) W _ mem _ _ _ (RTT_PC_A + 848 + 4 + 4 + 4 + 4) (SIGMA AS___asan_memcpy));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | intros mat4].
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (YK11.mkst ?r _ _ _) ?m) _ => set (regsT := r); set (mdT := m) end.
set (back := frame_addr ly RT_CID pos + RT_BACK) in *.
set (cntr := ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) + Z.of_nat (PjRoundTrip.tcalls (ri_t D))) in *.
(* the facts the call reads *)
pose proof (ck_pre_facts D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & HDL & Hd8 & (cidd & posd & Hfd & Hd1 & Hd2) & Hdra &
  HCOPY & HDEP & HRAN).
destruct HCOPY as [Hc0 | (Hc8 & (cidc & posc & Hfc & Hc1' & Hc2') & Hcam & Hcra & Hcd)]; [contradiction|].
assert (HCT : RC D fxc ly S Hp W regsT mem mdT k pos).
{ unfold regsT, mdT. repeat apply ck_carry_md. repeat (apply ck_carry_upd; [ck_notin|]). exact HC. }
pose proof HCT as (HFXT & HJT & _ & HSVT & HCRT & HMNT & HROT & _).
destruct (ck_rc_frames D fxc ly S Hp W regsT mem mdT k pos HCT) as (HAR & Efr & Hni & Fa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ck_stkr as HSTKv.
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
destruct (ck_sp1 (ri_sp D) Hsp16) as (Hs1 & Hs16).
assert (Hfcs : In (cidc, posc) (frames S)) by (rewrite Efr; right; exact Hfc).
assert (Hown : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ cidc posc HAR Hfcs) as (Fc1 & Fc2 & Fc3).
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HAR Hown) as (Fo1 & Fo2 & Fo3).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HAR Hown) as (Fo32 & _ & Fopr & _).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ cidc posc HAR Hfcs) as (Fc32 & _ & Fcpr & _).
rewrite Efs1 in Fo2, Fo3, Fopr. rewrite Fa in Fc1, Fc2, Fc3, Fcpr.
pose proof (ck_own_apart D fxc ly S Hp W regsT mem mdT k pos cidc posc HCT Hfc) as Hap.
unfold zdisjoint, frame_rng in Hap. cbn [fst snd] in Hap. rewrite Efs1, (Fa cidc posc) in Hap.
assert (Hcc : 0 <= cidc) by (apply ck_fs_cid; lia).
assert (T10 : getr regsT 10 = w64 (ri_copy D)) by (unfold regsT; ck_rg; rewrite R19, ck_vaddi0; reflexivity).
assert (T11 : getr regsT 11 = w64 back) by (unfold regsT; ck_rg; rewrite R23, ck_vaddi0; reflexivity).
assert (T12 : getr regsT 12 = w64 56) by (unfold regsT; ck_rg; rewrite getr_zero; apply bv_eq; vm_compute; reflexivity).
assert (T2 : spZ regsT = RT_R (ri_sp D)).
{ unfold spZ, regsT. ck_rg. rewrite R2. unfold w64. apply unsigned_lit_small. unfold ri_sp in *. lia. }
assert (T3 : getr regsT 3 = w64 (as_gp B)) by (unfold regsT; ck_rg; exact R3).
assert (T4 : getr regsT 4 = w64 (as_tp B)) by (unfold regsT; ck_rg; exact R4).
(* the memcpy *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (YGcallMxmn.aj_intrin_at_xm_frR (fx := fxc) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) OCpy
    (SIGMA AS___asan_memcpy) (AMCPY fxc) W regsT mem STKR (ri_sp D) (ri_FP D) (ri_ly D)
    (set_depot (st_depot S) (ri_S D)) (ri_Hp D)
    (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp mdT k (ri_copy D) back 56 (RT_R (ri_sp D) - ri_sp D) _
    HJT T10 T11 T12).
  - lia.
  - lia.
  - lia.
  - rewrite T2. ring.
  - exact Hs16.
  - lia.
  - unfold ESTACK. lia.
  - exact T3.
  - exact T4.
  - unfold regsT. rewrite getr_same by reg_neq_tac. reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split.
    + right. split.
      * exists (ri_copy D, ri_copy D + 56). unfold ri_FP. rewrite (proj2 (Z.eqb_neq _ 0) Hc1).
        split; [left; reflexivity | cbn [fst snd]; lia].
      * exists cidc, posc. split; [exact Hfc|]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fa. lia.
    + unfold ESTACK. lia.
  - exact Hcam.
  - exact (ck_obj_ra D ly S Hp W mem mdT k pos (ri_copy D) cidc posc HP HJT Hfc Hc1' Hc2' Hcra).
  - intros _. exact (ck_hull ly S Hp W mem mdT cidc posc (ri_copy D) 56 HAR Hfcs Hcc ltac:(rewrite Fa; lia)
      ltac:(rewrite Fa; lia) ltac:(lia)).
  - split; [unfold back, RT_BACK; lia|]. split; [unfold back, RT_BACK; lia|]. split.
    + intros a Ha. rewrite T2. split; [apply ck_aview_of_apresent; apply (proj1 (Fopr a ltac:(unfold back, RT_BACK in *; lia)))|].
      unfold back, RT_BACK, ESTACK in *. lia.
    + split; [unfold back, RT_BACK; lia|]. split.
      * pose proof ASAN_CEIL_range as CR. clear - Fo1 Fo2 Fo3 C1 C2 C3 C4 C5 CR.
        unfold amem_range, in_app, back, RT_BACK, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
        lia.
      * split; [exact HBK|]. intros _. exact (ck_hull ly S Hp W mem mdT RT_CID pos back 56 HAR Hown
          ltac:(vm_compute; discriminate) ltac:(unfold back, RT_BACK; lia) ltac:(rewrite Efs1; unfold back, RT_BACK; lia)
          ltac:(lia)). }
cbv beta. intros W2 c2 _ (EW & regs2 & mem2 & md2 & Ec & HJ2 & HAP2 & A0 & HEFF & HKEEP & HPRES & HMN2).
subst W2 c2.
(* +868 j +880 and the tail: ck_tail868 at the end *)
(* the bytes the memcpy keeps *)
assert (KEEP : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (ri_copy D <= a < ri_copy D + 56) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. apply HKEEP; [lia | exact Hn |]. unfold ri_sp in *. unfold ESTACK. lia. }
assert (HBLK : forall b m x, In (b, m) (ablocks B ly S) -> b <= x < b + req_size m -> ~ (ri_copy D <= x < ri_copy D + 56)).
{ intros b m x Hb Hx Hxc.
  pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem mdT _ _ cidc posc HAR Hb Hfcs) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Fa in Hd. lia. }
assert (KBLK : forall b m x, In (b, m) (ablocks B ly S) -> b <= x < b + req_size m ->
  aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x).
{ intros b m x Hb Hx. destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4 & Hbc & _).
  apply KEEP; [lia | exact (HBLK b m x Hb Hx)]. }
assert (KIMG : forall a, in_img SEGS a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (pa_segs_low a Ha) as Hlow. apply KEEP; [unfold kLowMemEnd in Hlow; lia|].
  intros Hx. apply (frm_img_x _ _ _ LAWS ly S Hp W mem mdT cidc posc a HAR Hfcs ltac:(rewrite Fa; lia) Ha). }
assert (KPST : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; exact (KIMG a (pst_img_A a Ha))).
pose proof HW as HW'. unfold prh_head_wide in HW'.
assert (HLED2 : prh_ledger B ly S Hp W mem2 Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0).
{ eapply prh_ledger_kept_aview; [exact HLED | exact KPST | | | apply Permutation_refl].
  - intros a k0 i Hak Hi.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED Hak) as (Hk0 & Hab & _).
    assert (Hn0 : 0 <= k0 + cf_head) by lia.
    pose proof (req_size_pos (k0 + cf_head) Hn0) as [_ Hrq].
    apply (KBLK _ _ _ Hab). lia.
  - intros a k0 _ Hab. exact Hab. }
assert (HincL : incl (ri_Lam D) Lamr).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. exact Hbk. }
apply (ck_tail868 D fxc ly S Hp W regs2 mem2 md2 k pos HP SX).
- idtac.
  apply (ck_carry_keep D fxc ly S Hp W regsT mem mdT k pos ly S Hp W regs2 mem2 md2 k
    (RT_R (ri_sp D) - ESTACK) (RT_R (ri_sp D))
    (fun a => ri_copy D <= a < ri_copy D + 56) [] Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0
    Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0 HP HCT HJ2 eq_refl).
  + split; [|split; [|split]].
    * intros a Ha Hn. apply HKEEP; unfold ESTACK in *; lia.
    * intros b m i Hb _ Hi Hn. apply HKEEP; [| exact Hn |].
      -- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4 & Hbc & _). lia.
      -- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4 & Hbc & _). unfold ri_sp, ESTACK in *. lia.
    * intros a Ha _ _ _. exact (KIMG a Ha).
    * intros cid pos' a Hf Ha Hn. destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ cid pos' HAR Hf) as (G1 & G2 & G3).
      pose proof (fs_frame_bytes_nonneg cid) as G4.
      assert (G5 : fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
      unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
      assert (Ha' : 0 <= a < 2 ^ 64 /\ ~ (ri_sp D + (RT_R (ri_sp D) - ri_sp D) - ESTACK <= a <
                                         ri_sp D + (RT_R (ri_sp D) - ri_sp D))).
      { clear - Ha G1 G2 G3 G4 G5 Hsp0 Hs1 HSTKv C1 C2 C3 C4 C5.
        unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, ASAN_CEIL, ri_sp, ESTACK in *; lia. }
      apply HKEEP; [exact (proj1 Ha') | exact Hn | exact (proj2 Ha')].
  + unfold ri_sp in *. lia.
  + intros a Ha. inversion Ha.
  + intros x Hx. apply (ck_off_entry D fxc ly S Hp W regsT mem mdT k pos Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0
      cidc posc x HCT HLED HincL Hfc); [rewrite Fa; lia | lia].
  + exact HLED.
  + exact HincL.
  + exact HLED2.
  + exact HincL.
  + exact (ck_cregs_pres D ly regsT regs2 pos HAP2 HCRT).
  + exact HMN2.
  + exact HRL.
- exists Lamr, peakr, cntr, (ri_ran D). split; [split; [exact HLED2 | exact HPK]|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  { destruct HPOS as (hist & HIP). exists hist.
    assert (EK : RT_K_ALL D = RT_K_T D).
    { unfold RT_K_ALL, RT_K_T, ck_rtt_evs. rewrite (proj2 (Z.eqb_neq _ 0) Hc1), app_nil_r. reflexivity. }
    rewrite EK. exact HIP. }
  split; [intros Hc; contradiction|].
  intros _. exists Db.
  (* the tree moves from back to *copy: the 56 bytes are back's, Db's bytes are kept; the ordered free list and K0-CAP
     move with it *)
  assert (MAP : pj_apartR Db (ri_copy D)).
  { intros b x Hb Hx Hxc. destruct b as [a0 k0]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    assert (HinL : In (a0, k0) Lamr) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HinL) as (Hk0 & Hab & _).
    assert (Hn0 : 0 <= k0 + cf_head) by lia.
    pose proof (req_size_pos (k0 + cf_head) Hn0) as [_ Hrq].
    assert (Hx2 : a0 - cf_head <= x < a0 - cf_head + req_size (k0 + cf_head)) by lia.
    exact (HBLK _ _ x Hab Hx2 Hxc). }
  assert (MRW : pj_rwR SEGS (mrestrict (w_H W) mem2) (ri_copy D)).
  { split; [exact Hc8|]. intros x Hx. apply apresent_writable. apply HPRES.
    exact (proj1 (Fcpr x ltac:(lia))). }
  assert (MHD : forall j, 0 <= j < 56 ->
    mbyte SEGS (mrestrict (w_H W) mem2) (ri_copy D + j) = mbyte SEGS (mrestrict (w_H W) mem) (back + j)).
  { intros j Hj. apply ck_mbyte_of_aview2. exact (HEFF j Hj). }
  assert (MAG : pj_agreeR SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2)
    (fun x => exists b, In b Db /\ pj_holdsR b x)).
  { intros x (b & Hb & Hx). destruct b as [a0 k0]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    assert (HinL : In (a0, k0) Lamr) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HinL) as (Hk0 & Hab & _).
    assert (Hn0 : 0 <= k0 + cf_head) by lia.
    pose proof (req_size_pos (k0 + cf_head) Hn0) as [_ Hrq].
    assert (Hx2 : a0 - cf_head <= x < a0 - cf_head + req_size (k0 + cf_head)) by lia.
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & _ & _ & Hbpr & _).
    split; [apply mbyte_of_aview; exact (KBLK _ _ x Hab Hx2)|].
    intros _. apply apresent_writable. apply HPRES. exact (proj1 (Hbpr x Hx2)). }
  split; [exact HPL|]. split; [exact HDbn|]. split; [exact HDs|]. split; [exact HTB|].
  split.
  { intros Hhd nn Hnn. destruct (HFRS Hhd nn Hnn) as (F & HF & HFm). exists F. split; [|exact HFm].
    exact (ck_foR_move SEGS nn (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2) (prh_lin Lamr) back (ri_copy D) Db F
      HF MAP MRW MHD MAG). }
  split; [exact HDn|].
  split; [exact HPB|].
  split; [exact (ck_nodeR_move SEGS (ri_t D) (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2) (prh_lin Lamr) back
    (ri_copy D) Db HNB MAP MRW MHD MAG)|].
  exact (ck_ncapR_move SEGS (ri_t D) (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2) (prh_lin Lamr) back (ri_copy D) Db
    HNB HCAP MHD (fun x Hx => proj1 (MAG x Hx))).
Qed.

(* ---- 15. *copy = 0: mv a0, s7; jal pj_free (&back): back's tree is freed, Lam back to the entry's, the position
   advances by pj_free's one bulk event, which is the model's HBulk (fo t) ---- *)
Lemma ck_arm0 : forall D fxc ly S Hp W regs mem md k pos,
  PRE D -> SEGX -> ri_copy D = 0 -> ck_mid D fxc ly S Hp W regs mem md k pos ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_PC_A + 872))) mem (YK11.seg_rom SEGS)) md)
    (POST D).
Proof.
intros D fxc ly S Hp W regs mem md k pos HP SX Hc0 HM.
pose proof HM as (HC & HBK & R23 & HPOS & Lamr & peakr & Db & (HLED & HPK) & HPL & HDbn & HDs & HTB & HFOF & HDn &
  HPB & HNB & _ & _).
pose proof HC as (_ & _ & _ & _ & HCR & _ & _ & HRL & _ & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
(* +872 mv a0, s7 *)
eapply (ck_addi (fx := fxc) (PL := PL) (PI := PA) W regs mem md _ _ (RTT_PC_A + 872) _ _ _ 10%bv 23%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity | intros mat1].
(* +876 jal pj_free *)
eapply (ck_jal (fx := fxc) (PI := PA) W _ mem _ _ _ (RTT_PC_A + 872 + 4) (SIGMA AS_pj_free));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | intros mat2].
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (YK11.mkst ?r _ _ _) ?m) _ => set (regsT := r); set (mdT := m) end.
set (back := frame_addr ly RT_CID pos + RT_BACK) in *.
set (cntr := ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) + Z.of_nat (PjRoundTrip.tcalls (ri_t D))) in *.
pose proof (ck_pre_facts D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & HDL & Hd8 & _ & _ & _ & HDEP & HRAN).
pose proof (ck_pre_more D HP) as (HUNIV & HRA).
assert (HCT : RC D fxc ly S Hp W regsT mem mdT k pos).
{ unfold regsT, mdT. repeat apply ck_carry_md. repeat (apply ck_carry_upd; [ck_notin|]). exact HC. }
pose proof HCT as (HFXT & HJT & _ & HSVT & HCRT & HMNT & HROT & _).
destruct (ck_rc_frames D fxc ly S Hp W regsT mem mdT k pos HCT) as (HAR & Efr & Hni & Fa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ck_stkr as HSTKv.
let v := eval vm_compute in (STK_pj_free DOC_D) in assert (ESTP : STK_pj_free DOC_D = v) by (vm_compute; reflexivity).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
destruct (ck_sp1 (ri_sp D) Hsp16) as (Hs1 & Hs16).
assert (Hown : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HAR Hown) as (Fo1 & Fo2 & Fo3).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ RT_CID pos HAR Hown) as (Fo32 & _ & Fopr & _).
rewrite Efs1 in Fo2, Fo3, Fopr.
pose proof HW as HW'. unfold prh_head_wide in HW'.
assert (T10 : getr regsT 10 = w64 back) by (unfold regsT; ck_rg; rewrite R23, ck_vaddi0; reflexivity).
assert (T2 : spZ regsT = RT_R (ri_sp D)).
{ unfold spZ, regsT. ck_rg. rewrite R2. unfold w64. apply unsigned_lit_small. unfold ri_sp in *. lia. }
assert (T3 : getr regsT 3 = w64 (as_gp B)) by (unfold regsT; ck_rg; exact R3).
assert (T4 : getr regsT 4 = w64 (as_tp B)) by (unfold regsT; ck_rg; exact R4).
assert (T8 : s0Z regsT = ri_sp D).
{ unfold s0Z, regsT. ck_rg. rewrite R8. unfold w64. apply unsigned_lit_small. unfold ri_sp in *. lia. }
destruct (ck_chain_at D ly S Hp W mem mdT k pos (RT_R (ri_sp D)) HP HJT HSVT ltac:(lia)) as (ch1 & Hch1).
(* the position, the run's next event, the class-24 bound *)
destruct HPOS as (hist & HIP).
assert (HRUN : prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_T D)%nat
  [PresetReqAt.HBulk (PresetReqAt.fo (ri_t D))]).
{ unfold ck_rtt_evs in HRA. rewrite Hc0, Z.eqb_refl in HRA.
  apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in HRA as [_ H2]. exact H2. }
(* pj_free's order list over back's tree and its requests fo t: the cut's free-order conjunct (rtt_rb, the text owner's
   ruling: the writer-side free list is a list equality); its run event by PRH_FnPj.v prhPj_free_evs_supply *)
destruct HFOF as (F & HFO & HFt).
pose proof (prhPj_free_evs_supply ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_T D)%nat F
  (PresetReqAt.fo (ri_t D))
  HFt HRUN) as HRF.
pose proof (ck_ccnt24 _ _ _ _ _ _ _ HIP) as Hc24.
(* THE HULL BUDGET at pj_free's call (back <> 0; PRH_FnPj.v tpj_free_specX): the run's count at the cut's position
   bounds both meters by A17's caps (a run of at most 4 calls, rtt_pre_os4), within the instance's caps (HI_hull);
   CrsSeg_Z.v's route *)
assert (Hos4 : (length (ri_os D) <= 4)%nat) by (eapply (rtt_pre_os4 (fx := fx)); exact HP).
assert (HULL : @PresetHullBudget.hull_budget cp S []).
{ destruct (PresetDrvHullA.drv_cf_hull_ok_at_call_A _ _ _ _ _ _ S Hos4 HIP) as [Nh Th].
  rewrite PresetRoomPos.rp_nsec_layer in Nh. destruct HI_hull as [Kn Kt].
  unfold PresetHullBudget.hull_budget. change (Z.of_nat (PresetSecTotal.nsec [])) with 0.
  change (PresetSecTotal.tsec []) with 0. split; lia. }
assert (HincL : incl (ri_Lam D) Lamr).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. exact Hbk. }
(* Db's blocks: live now, none of the entry's *)
assert (HDbB : forall a k0, In (a, k0) Db -> In (a - cf_head, k0 + cf_head) (ablocks B ly S)).
{ intros a k0 Hak. apply (Permutation_in _ (Permutation_sym HPB)). apply in_or_app. right.
  exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) Db (a, k0) Hak). }
assert (Hb0 : back <> 0) by (unfold back, RT_BACK; lia).
set (FP1 := (back, back + 56) :: ablocks_fp (prhPj_hbl Db)).
(* the call *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (ck_call_at (fx := fxc) W regsT mem STKR (ri_sp D) (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D))
    (ri_Hp D) (ri_W D)
    (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp mdT k (STK_pj_free DOC_D) FP1 (RT_R (ri_sp D) - ri_sp D) _ ch1
    (SIGMA AS_pj_free) _ HJT).
  - rewrite T2. ring.
  - exact Hs16.
  - lia.
  - vm_compute. discriminate.
  - rewrite HSTKv. let v := eval vm_compute in (STK_pj_free DOC_D) in change (STK_pj_free DOC_D) with v. lia.
  - exact T3.
  - exact T4.
  - unfold regsT. rewrite getr_same by reg_neq_tac. reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - vm_compute. discriminate.
  - replace (ri_sp D + (RT_R (ri_sp D) - ri_sp D)) with (RT_R (ri_sp D)) by ring. rewrite T8. exact Hch1.
  - intros HAFN.
    assert (HFP : fpre (fx := fxc) (PA := PA) B ARx (STK_pj_free DOC_D) ly S Hp W regsT mem mdT ch1).
    { apply (ck_fpre fxc D ly S Hp W mem mdT k pos _ regsT ch1 HP HJT HROT HAFN);
        [rewrite T2; lia | | exact (proj1 HFXT)].
      unfold raZ, regsT. rewrite getr_same by reg_neq_tac. pose proof ASAN_CEIL_range as [[CR1 _] _].
      unfold ASAN_CEIL in CR1.
      match goal with |- bv_unsigned ?w < _ => let v := eval vm_compute in (bv_unsigned w) in
        change (bv_unsigned w) with v end. lia. }
    pose proof HAFN as (_ & _ & _ & _ & _ & HstkT & _).
    pose proof HstkT as (_ & _ & Hceil1 & Hslo1 & _ & _ & _ & HtopT & _).
    assert (HSLOT : prhPj_slot (PA := PA) B (STK_pj_free DOC_D) 0 ly S Lamr W regsT mem back).
    { split; [unfold back, RT_BACK; lia|]. split.
      { right; right; left. exists RT_CID, pos. split; [exact Hown|]. rewrite Efs1. unfold back, RT_BACK. lia. }
      split.
      { split.
        - unfold back, RT_BACK. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Fo32; [|lia].
          destruct Fo32 as [q Hq]. exists (4 * q + 4). lia.
        - intros x Hx. apply apresent_writable. exact (proj1 (Fopr x ltac:(unfold back, RT_BACK in *; lia))). }
      split.
      { pose proof ASAN_CEIL_range as CR. clear - Fo1 Fo2 Fo3 C1 C2 C3 C4 C5 CR.
        unfold amem_range, in_app, back, RT_BACK, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
        lia. }
      split.
      { intros a Ha. unfold back, RT_BACK in Ha. split; [exact (proj2 (Fopr a ltac:(lia)))|]. rewrite T2, ESTP. lia. }
      split; [exact HBK|].
      exact (ck_hull ly S Hp W mem mdT RT_CID pos back 56 HAR Hown ltac:(vm_compute; discriminate)
        ltac:(unfold back, RT_BACK; lia) ltac:(rewrite Efs1; unfold back, RT_BACK; lia) ltac:(lia)). }
    assert (HFW : fwin (PA := PA) ly W regsT mem 0).
    { split; [lia|]. split; [reflexivity|]. split; [lia|]. intros a Ha. lia. }
    assert (Hbc : back < YM05.alloc_ceiling) by (unfold back, RT_BACK; lia).
    pose proof (TPJF fxc (ri_most D) 0 ly S Hp W regsT mem mdT ch1 0 back Db F Lamr peakr cntr SIZE_MAXZ (ri_ran D)
      HFP HUNIV HRL (fun _ => Hc24) (fun _ => HULL) T10 HFW
      (or_intror (conj Hb0 (conj Hbc (conj HFO HSLOT)))) HW HLED) as HR.
    rewrite (proj2 (Z.eqb_neq back 0) Hb0) in HR.
    eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf); [exact HR|].
    intros W' c' _ HWp. exact (ck_fpostW0 (fx := fxc) _ _ _ _ _ _ _ _ _ _ _ _ HWp).
  - intros a Ha. unfold FP1 in Ha. apply inFP_cons in Ha as [Ha | Ha].
    + right; right; left. exists (RT_CID, pos). split; [left; reflexivity|]. unfold in_zr, frame_rng. cbn [fst snd].
      rewrite Efs1. unfold back, RT_BACK in Ha. lia.
    + right; left. destruct Ha as (r & Hr & Hx). unfold ablocks_fp, prhPj_hbl in Hr.
      rewrite map_map in Hr. apply in_map_iff in Hr as ([a0 k0] & Er & Hak). subst r. cbn [fst snd] in Hx.
      exists (a0 - cf_head), (k0 + cf_head). split; [exact (HDbB a0 k0 Hak)|]. split; [exact (HDbn a0 k0 Hak)|]. lia. }
cbv beta. intros W3 c3 _ (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k1 & Ec3 & HJ3 & HJc3 & HAP3 & (HQ3 & HMN3)).
subst c3.
destruct HQ3 as (HRL3 & _ & HPOSI & Lam3 & HPL3 & HPB3 & HLED3 & _ & _ & _).
destruct (HPOSI ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + RT_K_T D)%nat (ri_H0 D) hist HIP HRF)
  as (hist3 & HIP3).
clear HPOSI.
replace (RTT_PC_A + 872 + 4 + 4) with (RTT_PC_A + 880) by ring.
assert (HPL' : Permutation Lam3 (ri_Lam D)).
{ apply (Permutation_app_inv_l Db). exact (Permutation_trans (Permutation_sym HPL3) HPL). }
assert (HincL3 : incl (ri_Lam D) Lam3) by (intros bk Hbk; exact (Permutation_in _ (Permutation_sym HPL') Hbk)).
assert (HFR3 : frames S3 = frames S) by exact (ajxR_frs HJc3).
(* the caller journal from RJ at S is RJ at S3 *)
assert (HJ3' : RJ D ly3 S3 Hp3 W3 mem3 md3 (k + k1) pos) by (eapply rtt_J_of_Jc; exact HJ3).
apply (ck_tail D fxc ly3 S3 Hp3 W3 regs3 mem3 md3 (k + k1) pos HP SX).
- apply (ck_carry_keep D fxc ly S Hp W regsT mem mdT k pos ly3 S3 Hp3 W3 regs3 mem3 md3 (k + k1)
    (RT_R (ri_sp D) - STK_pj_free DOC_D) (RT_R (ri_sp D)) (inFP FP1) PST
    Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0
    Lam3 peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0 HP HCT HJ3 HFR3).
  + rewrite Zplus_minus in HJc3.
    apply (ck_kept_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3).
    apply sink_closed_pos. unfold FP1. apply Forall_cons; [cbn [fst]; unfold back, RT_BACK; lia|].
    unfold ablocks_fp, prhPj_hbl. rewrite map_map. apply Forall_forall. intros r Hr.
    apply in_map_iff in Hr as ([a0 k0] & <- & Hak). cbn [fst].
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR (HDbB a0 k0 Hak)) as (_ & Hb4 & _). lia.
  + unfold ri_sp in *. lia.
  + intros a Ha. exact Ha.
  + intros x Hx. unfold FP1 in Hx. apply inFP_cons in Hx as [Hx | Hx].
    * exact (ck_off_back D fxc ly S Hp W regsT mem mdT k pos Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0 x
        HP HCT HLED HincL Hx).
    * destruct Hx as (r & Hr & Hx). unfold ablocks_fp, prhPj_hbl in Hr.
      rewrite map_map in Hr. apply in_map_iff in Hr as ([a0 k0] & Er & Hak). subst r. cbn [fst snd] in Hx.
      assert (HinL : In (a0, k0) Lamr)
        by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hak).
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HinL) as (Hk0 & _).
      assert (Hn0 : 0 <= k0 + cf_head) by lia.
      pose proof (req_size_pos (k0 + cf_head) Hn0) as [_ Hrq].
      try unfold in_zr in Hx. cbn [fst snd] in Hx.
      assert (Hx2 : a0 - cf_head <= x < a0 - cf_head + req_size (k0 + cf_head)) by lia.
      exact (ck_off_newblk D fxc ly S Hp W regsT mem mdT k pos Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0
        (a0 - cf_head) (k0 + cf_head) x HP HCT HLED HincL (HDbB a0 k0 Hak) (HDbn a0 k0 Hak) Hx2).
  + exact HLED.
  + exact HincL.
  + exact HLED3.
  + exact HincL3.
  + destruct (ck_fa_eq D ly3 S3 Hp3 W3 mem3 md3 (k + k1) pos HJ3') as (Fa3 & _).
    exact (ck_cregs_pres D ly3 regsT regs3 pos HAP3
      (ck_cregs_ly D ly ly3 regsT pos ltac:(intros; rewrite Fa3, Fa; reflexivity) HCRT)).
  + exact HMN3.
  + exact HRL3.
- exists Lam3, peakr, cntr, (ri_ran D). split; [split; [exact HLED3 | exact HPK]|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  { assert (EK : RT_K_ALL D = (RT_K_T D + 1)%nat).
    { unfold RT_K_ALL, RT_K_T, ck_rtt_evs. rewrite Hc0, Z.eqb_refl. apply ck_len_snoc. }
    unfold rtt_pos. rewrite EK, Nat.add_assoc.
    destruct F as [|b F'].
    - (* no blocks: the model's event is HBulk [], which pj_free does not make; the caller steps over it *)
      cbn [prhPj_free_evs length] in HIP3. rewrite Nat.add_0_r in HIP3.
      assert (Hnth : nth_error (PresetRun.hruns ReaderRes.jr_strtod (ri_x D) (ri_os D)) (ri_i D + RT_K_T D)%nat =
        Some (PresetReqAt.HBulk [])).
      { cbn [map] in HFt. rewrite <- HFt in HRUN. exact (proj1 (prh_run_at_one _ _ _ _ _) HRUN). }
      exists hist3. rewrite Nat.add_1_r.
      exact (proj1 (prhPj_bulk_nil_pos _ _ _ _ _ _ _ Hnth) HIP3).
    - exists hist3. exact HIP3. }
  split.
  { intros _. split; [exact HPL'|].
    apply (Permutation_app_inv_l (prhPj_hbl Db)). eapply Permutation_trans; [exact (Permutation_sym HPB3)|].
    eapply Permutation_trans; [exact HPB|]. apply Permutation_app_comm. }
  intros Hc; contradiction.
Qed.

(* ---- 15b. +844 beqz a0 (same said 1: not taken), +848 beqz s3 (copy): the two arms ---- *)
Lemma ck_split844 : forall D fxc ly S Hp W regs mem md k pos, PRE D -> SEGX ->
  ck_mid D fxc ly S Hp W regs mem md k pos -> getr regs 10 = w64 1 ->
  (ri_copy D <> 0 -> forall ly2 W2 regs2 mem2 md2 k2, ck_mid D fxc ly2 S Hp W2 regs2 mem2 md2 k2 pos ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_PC_A + 848 + 4))) mem2 (YK11.seg_rom SEGS))
       md2) (POST D)) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_PC_A + 828 + 4 + 4 + 4 + 4))) mem
    (YK11.seg_rom SEGS)) md) (POST D).
Proof.
intros D fxc ly2 S Hp W2 regs2 mem2 md2 k2 pos HP SX HM2 A1 HARM1.
pose proof (ck_pre_facts D HP) as (HAR0 & _).
(* +844 beqz a0 (a0 = 1) *)
eapply (ck_beqz_ft (fx := fxc) (PL := PL) (PI := PA) W2 regs2 mem2 md2 _ _ (RTT_PC_A + 828 + 4 + 4 + 4 + 4) _ _ 10%bv _);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | unfold RTT_PC_A; vm_compute; discriminate
  | unfold RTT_PC_A; vm_compute; reflexivity | rewrite A1, getr_zero; vm_compute; reflexivity | intros mat5].
pose proof HM2 as (HC2 & _).
pose proof HC2 as (_ & _ & _ & _ & HCR2 & _).
pose proof HCR2 as (_ & _ & _ & _ & R19' & _).
destruct (Z.eq_dec (ri_copy D) 0) as [Hc0 | Hc1].
- (* +848 beqz s3 taken *)
  eapply (ck_beqz_tk (fx := fxc) (PL := PL) (PI := PA) W2 regs2 mem2 _ _ _ (RTT_PC_A + 828 + 4 + 4 + 4 + 4 + 4)
    (BASE + (RTT_PC_A + 872)) _ _ 19%bv _);
    [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
    | apply bv_eq; vm_compute; reflexivity | unfold RTT_PC_A; vm_compute; discriminate
    | unfold RTT_PC_A; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
    | rewrite R19', Hc0, getr_zero; vm_compute; reflexivity | intros mat6].
  apply (ck_arm0 D fxc ly2 S Hp W2 regs2 mem2 _ k2 pos HP SX Hc0).
  apply ck_mid_md. apply ck_mid_md. exact HM2.
- (* +848 beqz s3 not taken *)
  eapply (ck_beqz_ft (fx := fxc) (PL := PL) (PI := PA) W2 regs2 mem2 _ _ _ (RTT_PC_A + 828 + 4 + 4 + 4 + 4 + 4) _ _
    19%bv _);
    [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
    | apply bv_eq; vm_compute; reflexivity | unfold RTT_PC_A; vm_compute; discriminate
    | unfold RTT_PC_A; vm_compute; reflexivity | | intros mat6].
  + rewrite R19', getr_zero. unfold c_eq, w64.
    pose proof (ck_pre_facts D HP) as (_ & _ & _ & _ & _ & _ & _ & _ & HCP & _).
    destruct HCP as [H0 | (_ & (cidc & posc & Hfc & Hc1' & Hc2') & _)]; [contradiction|].
    destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ cidc posc HAR0 Hfc) as (G1 & G2 & _).
    pose proof ASAN_CEIL_range as [[_ CR2] _]. unfold ASAN_CEIL in CR2.
    apply bv_eqb_neq. intros E. apply (f_equal (@bv_unsigned 64)) in E.
    rewrite !unsigned_lit_small in E by lia. lia.
  + replace (RTT_PC_A + 828 + 4 + 4 + 4 + 4 + 4 + 4) with (RTT_PC_A + 848 + 4) by ring.
    apply (HARM1 Hc1 ly2 W2 regs2 mem2 _ k2).
    apply ck_mid_md. apply ck_mid_md. exact HM2.
Qed.

(* ---- 16. RT_CK .. +848: bnez s8 (rc = 0); mv a0, s4; mv a1, s7; jal same (doc and back hold t: a0 = 1); beqz a0;
   beqz s3 (copy) to the two arms; the copy <> 0 arm as a continuation (ck_arm1's open point) ---- *)
Lemma ck_main : forall D fxc ly S Hp W regs mem md k pos, PRE D -> SEGX ->
  rtt_at_ck (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK D fxc ly S Hp W regs mem md k pos ->
  (ri_copy D <> 0 -> forall ly2 W2 regs2 mem2 md2 k2, ck_mid D fxc ly2 S Hp W2 regs2 mem2 md2 k2 pos ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_PC_A + 848 + 4))) mem2 (YK11.seg_rom SEGS))
       md2) (POST D)) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (SIGMA AS_round_trip_text + RT_CK)) mem (YK11.seg_rom SEGS)) md)
    (POST D).
Proof.
intros D fxc ly S Hp W regs mem md k pos HP SX HCK HARM1.
destruct (ck_mid_of_ck D fxc ly S Hp W regs mem md k pos HP HCK) as [HM R24].
pose proof HM as (HC & HBK & R23 & HPOS & Lamr & peakr & Db & (HLED & HPK) & HPL & HDbn & HDs & HTB & HFOF & HDn &
  HPB & HNB & HFRS & HCAP).
pose proof HC as (_ & _ & _ & _ & HCR & _ & _ & HRL & _ & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
rewrite ck_sigma. replace (BASE + RTT_PC_A + RT_CK) with (BASE + (RTT_PC_A + 828)) by (unfold RT_CK; ring).
(* +828 bnez s8 *)
eapply (ck_bnez_ft (fx := fxc) (PL := PL) (PI := PA) W regs mem md _ _ (RTT_PC_A + 828) _ _ 24%bv _);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | unfold RTT_PC_A; vm_compute; discriminate
  | unfold RTT_PC_A; vm_compute; reflexivity | rewrite R24, getr_zero; vm_compute; reflexivity | intros mat1].
(* +832 mv a0, s4 *)
eapply (ck_addi (fx := fxc) (PL := PL) (PI := PA) W regs mem _ _ _ (RTT_PC_A + 828 + 4) _ _ _ 10%bv 20%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity | intros mat2].
(* +836 mv a1, s7 *)
eapply (ck_addi (fx := fxc) (PL := PL) (PI := PA) W _ mem _ _ _ (RTT_PC_A + 828 + 4 + 4) _ _ _ 11%bv 23%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity | intros mat3].
(* +840 jal same *)
eapply (ck_jal (fx := fxc) (PI := PA) W _ mem _ _ _ (RTT_PC_A + 828 + 4 + 4 + 4) (SIGMA AS_same));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | unfold RTT_PC_A; vm_compute; discriminate | unfold RTT_PC_A; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | intros mat4].
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (YK11.mkst ?r _ _ _) ?m) _ => set (regsT := r); set (mdT := m) end.
set (back := frame_addr ly RT_CID pos + RT_BACK) in *.
set (cntr := ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) + Z.of_nat (PjRoundTrip.tcalls (ri_t D))) in *.
pose proof (ck_pre_facts D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & HDL & Hd8 & _ & _ & _ & HDEP & HRAN).
assert (HCT : RC D fxc ly S Hp W regsT mem mdT k pos).
{ unfold regsT, mdT. repeat apply ck_carry_md. repeat (apply ck_carry_upd; [ck_notin|]). exact HC. }
pose proof HCT as (HFXT & HJT & _ & HSVT & HCRT & HMNT & HROT & _).
destruct (ck_rc_frames D fxc ly S Hp W regsT mem mdT k pos HCT) as (HAR & Efr & Hni & Fa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ck_stkr as HSTKv.
let v := eval vm_compute in (STK_same DOC_D) in assert (ESTS : STK_same DOC_D = v) by (vm_compute; reflexivity).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
destruct (ck_sp1 (ri_sp D) Hsp16) as (Hs1 & Hs16).
assert (Hown : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
assert (HincL : incl (ri_Lam D) Lamr).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. exact Hbk. }
assert (T10 : getr regsT 10 = w64 (ri_doc D)) by (unfold regsT; ck_rg; rewrite R20, ck_vaddi0; reflexivity).
assert (T11 : getr regsT 11 = w64 back) by (unfold regsT; ck_rg; rewrite R23, ck_vaddi0; reflexivity).
assert (T2 : spZ regsT = RT_R (ri_sp D)).
{ unfold spZ, regsT. ck_rg. rewrite R2. unfold w64. apply unsigned_lit_small. unfold ri_sp in *. lia. }
assert (T3 : getr regsT 3 = w64 (as_gp B)) by (unfold regsT; ck_rg; exact R3).
assert (T4 : getr regsT 4 = w64 (as_tp B)) by (unfold regsT; ck_rg; exact R4).
assert (T8 : s0Z regsT = ri_sp D).
{ unfold s0Z, regsT. ck_rg. rewrite R8. unfold w64. apply unsigned_lit_small. unfold ri_sp in *. lia. }
destruct (ck_chain_at D ly S Hp W mem mdT k pos (RT_R (ri_sp D)) HP HJT HSVT ltac:(lia)) as (ch1 & Hch1).
pose proof (ck_doc_tree D fxc ly S Hp W regsT mem mdT k pos Lamr HP HCT HincL) as HDT.
pose proof (ck_back_tree D fxc ly S Hp W regsT mem mdT k pos Lamr Db HCT HBK HNB) as HBT.
pose proof (ck_pre_facts D HP) as (_ & _ & _ & _ & _ & _ & (cidd & posd & Hfd & Hd1 & Hd2) & _).
assert (Hfds : In (cidd, posd) (frames S)) by (rewrite Efr; right; exact Hfd).
(* the call *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (ck_call_at (fx := fxc) W regsT mem STKR (ri_sp D) (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D))
    (ri_Hp D) (ri_W D)
    (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp mdT k (STK_same DOC_D) [] (RT_R (ri_sp D) - ri_sp D) _ ch1
    (SIGMA AS_same) _ HJT).
  - rewrite T2. ring.
  - exact Hs16.
  - lia.
  - vm_compute. discriminate.
  - rewrite HSTKv. let v := eval vm_compute in (STK_same DOC_D) in change (STK_same DOC_D) with v. lia.
  - exact T3.
  - exact T4.
  - unfold regsT. rewrite getr_same by reg_neq_tac. reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - vm_compute. discriminate.
  - replace (ri_sp D + (RT_R (ri_sp D) - ri_sp D)) with (RT_R (ri_sp D)) by ring. rewrite T8. exact Hch1.
  - intros HAFN.
    assert (HFP : fpre (fx := fxc) (PA := PA) B ARx (STK_same DOC_D) ly S Hp W regsT mem mdT ch1).
    { apply (ck_fpre fxc D ly S Hp W mem mdT k pos _ regsT ch1 HP HJT HROT HAFN);
        [rewrite T2; lia | | exact (proj1 HFXT)].
      unfold raZ, regsT. rewrite getr_same by reg_neq_tac. pose proof ASAN_CEIL_range as [[CR1 _] _].
      unfold ASAN_CEIL in CR1.
      match goal with |- bv_unsigned ?w < _ => let v := eval vm_compute in (bv_unsigned w) in
        change (bv_unsigned w) with v end. lia. }
    pose proof HAFN as (_ & _ & _ & _ & _ & HstkT & _).
    pose proof HstkT as (_ & HstkS0 & Hceil1 & Hslo1 & _).
    assert (HF1 : forall z, pj_footR (ri_doc D) (ri_D D) z -> ~ (spZ regsT - STK_same DOC_D <= z < spZ regsT)).
    { intros z Hz. pose proof (ck_foot_low ly S Hp W mem mdT Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0
        (ri_doc D) (ri_D D)
        cidd posd HAR HLED Hfds ltac:(rewrite Fa; lia) ltac:(rewrite Fa; lia)
        ltac:(intros bk Hbk; exact (HincL _ (HDL _ Hbk))) z Hz). lia. }
    assert (HF2 : forall z, pj_footR back Db z -> ~ (spZ regsT - STK_same DOC_D <= z < spZ regsT)).
    { intros z Hz. pose proof (ck_foot_low ly S Hp W mem mdT Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0 back Db
        RT_CID pos HAR HLED Hown ltac:(unfold back, RT_BACK; lia) ltac:(rewrite Efs1; unfold back, RT_BACK; lia)
        ltac:(intros bk Hbk; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hbk) z Hz).
      lia. }
    (* same's GUARDED live-stack premise (PRH_FnEx.v tsame_specX at the cut): its guard is false here, doc lies below
       alloc_ceiling <= ly_stk_lo <= the callee's sp *)
    assert (HSU : spZ regsT <= ri_doc D -> YGcallStackUp.astack_up_x SEGS ly W (spZ regsT) mem).
    { intros Hle. exfalso.
      pose proof (ck_foot_low ly S Hp W mem mdT Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0
        (ri_doc D) (ri_D D)
        cidd posd HAR HLED Hfds ltac:(rewrite Fa; lia) ltac:(rewrite Fa; lia)
        ltac:(intros bk Hbk; exact (HincL _ (HDL _ Hbk))) (ri_doc D) ltac:(left; lia)) as Hz.
      lia. }
    (* same's text is a PLAIN SRr (fpostm, its journal at wle): lifted into the R premise (the internal file WLE-CONTRACT.md recipe R5,
       YA0nH.SRr_SRr' and YCbqG.apost_base_x_R_lift at YA0nH.wle_wle') *)
    pose proof (TSAME fxc ly S Hp W regsT mem mdT ch1 (ri_doc D) back (ri_t D) (ri_t D) (ri_D D) Db Lamr peakr cntr
      SIZE_MAXZ (ri_ran D) (ri_most D) 0 HFP HSU T10 T11 HDT HBT ltac:(unfold DOC_D, PjGrammar.MAXD in *; lia) HF1 HF2
      HLED) as HS0.
    eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf); [exact (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf _ _ _ HS0)|].
    intros W' c' _ HWp. unfold fpostm, fpost in HWp.
    exact (apost_base_x_R_lift (SK := SK) SEGS B PST ARx RZW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ HWp).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Ec2 & HJ2 & HJc2 & HAP2 & (HQ2 & HMN2)).
subst c2.
destruct HQ2 as (HRL2 & Hsame & HND2 & HNB2 & EHp & ES & EAB & HLED2).
subst Hp2 S2.
destruct Hsame as [(_ & A1) | (Hne & _)]; [|exfalso; exact (Hne eq_refl)].
destruct (ck_fa_eq D ly2 S Hp W2 mem2 md2 (k + k1) pos HJ2) as (Fa2 & _).
assert (Fa2' : forall cid pos', frame_addr ly2 cid pos' = frame_addr ly cid pos') by (intros; rewrite Fa2, Fa; reflexivity).
assert (HK2 : ck_kept ly S W mem ly2 S W2 mem2 (RT_R (ri_sp D) - STK_same DOC_D) (RT_R (ri_sp D)) (inFP []) PST).
{ rewrite Zplus_minus in HJc2.
  apply (ck_kept_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc2). apply sink_closed_pos. apply Forall_nil. }
(* back's tree footprint (back's 56 bytes in the own frame, Db's blocks) is kept across same *)
assert (KFOOT : pj_agreeR SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (pj_footR back Db)).
{ pose proof (ajxR_ar HJ2) as HAR2. pose proof HK2 as (_ & K2 & _ & K4).
  pose proof HW as HW'. unfold prh_head_wide in HW'.
  intros x [Hx | ((a0, k0) & Hb & Hx)].
  - unfold back, RT_BACK in Hx.
    assert (Ex : aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x).
    { apply (K4 RT_CID pos x Hown); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efs1; lia|].
      intros HE. exact (inFP_nil x HE). }
    split; [apply mbyte_of_aview; exact Ex|]. intros _. apply apresent_writable.
    destruct (alx_frames _ _ _ LAWS ly2 S Hp W2 mem2 md2 RT_CID pos HAR2 Hown) as (_ & _ & Hpr & _).
    apply (Hpr x). rewrite Fa2', Efs1. lia.
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    assert (HinL : In (a0, k0) Lamr)
      by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HinL) as (Hk0 & Hab & _).
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED2 HinL) as (_ & Hab2 & _).
    assert (Hn0 : 0 <= k0 + cf_head) by lia.
    pose proof (req_size_pos (k0 + cf_head) Hn0) as [_ Hrq].
    assert (Ex : aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x).
    { replace x with (a0 - cf_head + (x - (a0 - cf_head))) by lia.
      apply (K2 (a0 - cf_head) (k0 + cf_head) (x - (a0 - cf_head)) Hab Hab2); [lia|].
      intros HE. exact (inFP_nil _ HE). }
    split; [apply mbyte_of_aview; exact Ex|]. intros _. apply apresent_writable.
    destruct (alx_blocks _ _ _ LAWS ly2 S Hp W2 mem2 md2 (a0 - cf_head) (k0 + cf_head) HAR2 Hab2)
      as (_ & _ & _ & _ & Hpr & _).
    exact (proj1 (Hpr x ltac:(lia))). }
assert (HM2 : ck_mid D fxc ly2 S Hp W2 regs2 mem2 md2 (k + k1) pos).
{ split.
  { apply (ck_carry_keep D fxc ly S Hp W regsT mem mdT k pos ly2 S Hp W2 regs2 mem2 md2 (k + k1)
      _ _ (inFP []) PST Lamr peakr cntr SIZE_MAXZ (ri_ran D) (ri_most D) 0 Lamr peakr cntr SIZE_MAXZ (ri_ran D)
      (ri_most D) 0 HP HCT HJ2 eq_refl HK2).
    - unfold ri_sp in *. lia.
    - intros a Ha. exact Ha.
    - intros x Hx. exfalso. exact (inFP_nil x Hx).
    - exact HLED.
    - exact HincL.
    - exact HLED2.
    - exact HincL.
    - exact (ck_cregs_pres D ly2 regsT regs2 pos HAP2 (ck_cregs_ly D ly ly2 regsT pos Fa2' HCRT)).
    - exact HMN2.
    - exact (HRL2 HRL). }
  split; [exact (ck_back_keep D fxc ly S Hp W regsT mem mdT k pos ly2 S W2 mem2 _ _ _ _ HCT HK2
    ltac:(intros x Hx; exfalso; exact (inFP_nil x Hx)) Fa2' HBK)|].
  split; [rewrite (ck_preserved regsT regs2 _ HAP2) by ck_cs; unfold regsT; ck_rg; rewrite R23, Fa2'; reflexivity|].
  split; [exact HPOS|].
  exists Lamr, peakr, Db. split; [split; [exact HLED2 | exact HPK]|].
  split; [exact HPL|]. split; [exact HDbn|]. split; [exact HDs|]. split; [exact HTB|].
  split.
  { destruct HFOF as (F & HFO & HFt). exists F. split; [|exact HFt]. rewrite Fa2'.
    apply (pj_foR_frame SEGS DOC_D (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (prh_lin Lamr) (prh_lin Lamr)
      _ Db F HFO); [exact (pj_foR_lblk SEGS _ _ _ _ _ _ HFO) | exact KFOOT]. }
  split; [exact HDn|].
  split; [rewrite EAB; exact HPB|].
  split; [unfold back in HNB2; rewrite Fa2'; exact HNB2|].
  split.
  { (* back's free order at every depth bound: PRH_PjOrder.v pj_foR_frame over the kept footprint *)
    intros Hhd nn Hnn. destruct (HFRS Hhd nn Hnn) as (F & HFO' & HFt'). exists F. split; [|exact HFt']. rewrite Fa2'.
    apply (pj_foR_frame SEGS nn (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (prh_lin Lamr) (prh_lin Lamr)
      _ Db F HFO'); [exact (pj_foR_lblk SEGS _ _ _ _ _ _ HFO') | exact KFOOT]. }
  (* K0-CAP at back: Rtt102Cut.v rtt_ncapR_agree over the kept footprint *)
  rewrite Fa2'.
  exact (rtt_ncapR_agree SEGS (ri_t D) (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (prh_lin Lamr) back Db HNB HCAP
    KFOOT). }
(* +844 beqz a0 (a0 = 1), +848 beqz s3: ck_split844, in a small context *)
exact (ck_split844 D fxc ly2 S Hp W2 regs2 mem2 md2 (k + k1) pos HP SX HM2 A1 HARM1).
Qed.

(* ---- THE STRETCH: RTT_SEG_CK at image A' ---- *)
Theorem rtt_seg_ck_A : @RTT_SEG_CK fx rc ci cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK CTX0.
Proof.
unfold RTT_SEG_CK. intros SX. unfold rtt_seg.
intros D HP fxc ly S Hp W regs mem md k pos HCK.
apply (ck_main D fxc ly S Hp W regs mem md k pos HP SX HCK).
intros Hc1 ly2 W2 regs2 mem2 md2 k2 HM. exact (ck_arm1 D fxc ly2 S Hp W2 regs2 mem2 md2 k2 pos HP SX Hc1 HM).
Qed.
Print Assumptions rtt_seg_ck_A.
End m.
End w.
(* the elaborated statements: every FPState, PI, PA argument of the top theorem and of each helper whose statement
   binds a second float state fxc (the run's), by name (the text owner's rule, statements and proof contexts) *)
Set Printing Implicit.
Check @rtt_seg_ck_A.
Check @ck_main. Check @ck_split844. Check @ck_arm0. Check @ck_arm1. Check @ck_tail. Check @ck_tail868.
Check @ck_fpre. Check @ck_mid. Check @ck_carry_keep. Check @ck_fpostW0. Check @ck_call_at.
Unset Printing Implicit.
Print Assumptions rtt_seg_ck_A.
