(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Loop_kitQ.v, with its module paths and module names changed; 678 of its 721 lines of code are new or changed and 153 lines of the source are left out. *)
(* kb round (the contract's wild budget in crt_live): S and O1 carry crt_live at kb 64, the budget of U and W
   ((prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat, the glue's spelling); pj_string, pj_set and
   fuzz_alloc_ran_out have no wild site, so the journal stays at the budget it had at U. crt3_ff / crt3_home_keep /
   crt3_chain read a journal at any budget WS (ajournal_xw), crt3_tree_ok a live state at any kb. No other statement
   changed. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T3 (CRT-B-UGKO1): the segment
   U, G, K, O1 = B' entry + 0x1ec -> + 0x2a4 (round_trip_rewrite inlined, fuzz_preset.c new:719-734).
   Owned by the row holder, under the family lead. THIS FILE: the row's inner cuts, the stage statements the three
   stage files prove (Crt102B_T3U.v, Crt102B_T3S.v, Crt102B_T3O.v) and the shared image facts; Crt102B_T3.v composes.

   proves no function (kind: segment statements and image lemmas).

   INPUTS OF RECORD (this row was built on the check_round_trip walk head
   71a8716672850d3cc31b00bbc497633106293cac, merged, no rebase; no PRH_* file by path):
   - pins: A' asan 1be0f53d96cb9d6c (twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin c90d4fa54d43160b).
   - the lane's glue lib/A/Prog/Crt102Glue.v (records, read by name): crt_at_U_B (the pre; its crt_at_U_B_copy_fo is
     copy's ordered free list, producer row T2), crt_at_X_B (the C4a post, unreachable at this head), crt_at_W_B (the
     post; crt_at_W_B_copy_fo produced here), crt_live / crt_side, crt_pos / crt_evs_U / crt_evs_W, crt_tree_J,
     crt_dregs_B, QF, crt_cfg, CRT_OWN_LO_B, CRT_W0_OFF_B; image facts lib/A/Prog/Crt102Img.v (Section b: the B'
     values only the B PAImg instance carries, the HB hypotheses); model lib/A/Prog/Crt102Model.v.
   - texts: the head's (the kit cut 7cdbb61b5fa0 merged into the lane): PRH_FnPj 5aca5cbe2cfb - tpj_string_specX /
     tpj_set_specX keyed on ReaderRes.jr_strtod, with prh_cons_from, DEAD-PJSTRING / -PJSET and FREEORD-COPY.
   - listing: lib/B/Listing_prog.v, runner tables lib/B/Prog/PLB102.v (TxPutB102's PAListing of that listing, the
     lane's blob); the body read off the B' disassembly of check_round_trip (B' entry 0x82828).
   - build route pins102: the pins102 route script zfb-targets (sha256 85055e6079bc), FACTS 8f3e7e1a07f1,
     the PAU directory pau-preset-102.

   THE B' CODE (the internal file crt.B.s; offsets from the B' entry; doc = s6, F = s3 = s7, &copy = s4, shadow base s11):
     +0x1ec .. +0x220  fourteen `sb zero, k(s2)`, k = 4 .. 10, 16 .. 22: back's and v's shadow opened
     +0x224 addi a0, s6, 0x28   +0x228 srli a1, a0, 3   +0x22c add a1, a1, s11   +0x230 sd a1, 0x50(s1)
     +0x234 lbu a1, 0(a1)       +0x238 bnez a1, +0x83c (ASan report: dead)
     +0x23c sd a0, 0x58(s1)     +0x240 ld a0, 0(a0)     +0x244 sd a0, 0x48(s1)
     +0x248 addi s5, s3, 0x80 (&v)   +0x24c auipc / +0x250 addi a1 (STAMP)   +0x254 mv a0, s5
     +0x258 jal pj_string       +0x25c beqz a0, +0x270   +0x260 mv s8, zero   +0x264 j +0x288
     +0x270 auipc / +0x274 addi a1 (MOD_AT)   +0x278 mv a0, s4   +0x27c mv a2, s5   +0x280 jal pj_set
     +0x284 seqz s8, a0
     +0x288 auipc s10           +0x28c lbu a0, 0x2d0(s10) (g_own_ran_out)   +0x290 addi s5, zero, 1
     +0x294 bnez a0, +0x30c (X) +0x298 jal fuzz_alloc_ran_out   +0x29c bnez a0, +0x30c (X)
     +0x2a0 beqz s8, +0x824 (the `!set` abort: unreachable, below)   +0x2a4 W.
   THE INNER CUTS: S (+0x270, pj_string returned 0) and O1 (+0x288, the two flag tests), each a predicate below.
     U -> pj_string -> S          (a = 0 is dead: DEAD-PJSTRING)         [Crt102B_T3U.v]
     S -> pj_set -> seqz s8 -> O1 (res = -1 is dead: DEAD-PJSET)         [Crt102B_T3S.v]
     O1 -> fuzz_alloc_ran_out -> W (own = ran = 0, s8 = 1)               [Crt102B_T3O.v]
   THE REFUSALS ARE DEAD AT THEIR SOURCE (the callee TEXTS' own clauses, PRH_FnPj 5aca5cbe2cfb :1275 / :1046): at
   fail = SIZE_MAXZ and cnt < 2 ^ 62, pj_string's post gives a <> 0 and pj_set's res = 0. So O1 is reached only
   granted (crt_at_O1_3: sbit = 1, ranc = 0), both flag tests fall through, and the `!set` abort (+0x2a0) and the C4a
   exit to X (+0x30c, r = 1) are unreachable.
   THE ROOM POSITION (crt_pos, the glue's): crt_evs_U ms = set_evs ms ++ crt_evs_W ms (PresetReqAt rw_evs), and
   set_evs ms = HMal (21 + HEAD) :: <pj_set's events>. So S carries crt_pos Sc (tl (set_evs ms) ++ crt_evs_W ms)
   (pj_string's event done), and O1 carries crt_pos Sc (crt_evs_W ms) (both calls granted).
   copy's free order: tpj_set_specX takes copy's ORDERED free list (crt3_copy_fo0, from crt_at_U_B_copy_fo carried to
   S) and returns the result's (FREEORD-COPY), which O1 carries to W as crt3_copy_fo = crt_at_W_B_copy_fo.

   NUMERALS. DERIVED: the cut offsets 0x270 (CRT_S_OFF_B) and 0x2a4 (CRT_W0_OFF_B, row T4's value), from the internal file crt.B.s
   and checked against the listing by vm_compute below; 720 = the lbu immediate 0x2d0 of +0x28c (the glue's
   CRT_OWN_LO_B); the A_HI / A_OBJ indices 35 / 13 of the listing's PHi / PLdHi pair at +0x288 / +0x28c. LENGTH: 56
   (struct pj), 21 / 11 (the two strings with their NUL). WORD: register indices. No ADDRESS literal: the image
   values below are vm_compute results over the B segments under Crt102Img's HB hypotheses. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcfTreeVis YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcfAmx2.
(* The re-hiding move: the stage statements conclude at YA0nH.SRr' SEGS
   YGcfRehidePost.RZ_cf and the journal is at YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (the re-hiding contract) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Glue Crt102Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the inner cut S of this row on B' (DERIVED: 4 * the slot inside the function, the internal file crt.B.s) ---- *)
Definition CRT_S_OFF_B : Z := 0x270.   (* +0x270: pj_string returned 0 (beqz a0 taken): the pj_set set-up *)
Lemma crt_cut_S_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_S_OFF_B) = Some (PHi (10%bv : bv 5) 34).
Proof. vm_compute. reflexivity. Qed.
(* the cut W (+0x2a4, O1's fall-through `addi a0, s3, 0x20`): THE GLUE'S `CRT_W0_OFF_B` (Crt102Glue.v, `Definition
   CRT_W0_OFF_B : Z := 676`, the glue's one home; T3's and T4's copies are deleted and both cite it). It is NOT
   Crt102Img's CRT_W_OFF_B (0x2bc), which is pj_write's RETURN, a different cut. *)
Lemma crt_cut_W0_B : plookup_list asym B_prog_listing (CRT_PC_B + CRT_W0_OFF_B) = Some (PW 0x2098513).
Proof. vm_compute. reflexivity. Qed.
(* O1's auipc / lbu pair: the listing's PHi at +0x288 and the PLdHi at +0x28c that reads g_own_ran_out *)
Lemma crt_own_lst_B :
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_O1_OFF_B) = Some (PHi (26%bv : bv 5) 35) /\
  plookup_list asym B_prog_listing (CRT_PC_B + CRT_O1_OFF_B + 4) =
    Some (PLdHi (10%bv : bv 5) (26%bv : bv 5) 35 (A_OBJ 13) 0x0 SZ1 false).
Proof. split; vm_compute; reflexivity. Qed.
(* the text's two strings are the model's (PresetReqAt's MOD_VAL / MOD_KEY), and the head size is the model's HEAD *)
Lemma crt3_stamp_model : ck_STAMP = PresetReqAt.MOD_VAL.
Proof. vm_compute. reflexivity. Qed.
Lemma crt3_modat_model : ck_MOD_AT = PresetReqAt.MOD_KEY.
Proof. vm_compute. reflexivity. Qed.
Lemma crt3_head_model : @cf_head CfParams_preset = PresetReqAt.HEAD.
Proof. vm_compute. reflexivity. Qed.

(* the high half alone, from a listing certificate (Crt102Img's res_cert_add, its first half) *)
Lemma crt3_hi_cert : forall (fetch : Z -> option Z) (val : nat -> Z) (sigma : asym -> Z) (L : ptable asym)
  k1 (rd : bv 5) j,
  pi_check asym fetch val sigma L = true -> plookup_list asym L k1 = Some (PHi rd j) ->
  exists rd', hi_of (zf fetch) (val A_TEXT + k1) = Some (rd', val (A_HI j)).
Proof.
intros fetch val sigma L k1 rd j HC H1.
pose proof (pi_check_lookup asym fetch val sigma L k1 _ HC H1) as C1.
unfold pi_slot_check in C1. cbv zeta beta iota in C1.
unfold hi_of, zf. cbv beta.
destruct (fetch (val A_TEXT + k1)) as [w1|]; cbn [option_map]; cbv beta iota in C1 |- *; [|discriminate C1].
destruct (decode_any (Z_to_bv 32 w1)) as [[i1 s1]|]; cbv beta iota in C1 |- *; [|discriminate C1].
apply andb_prop in C1 as [S1 C1].
destruct i1; cbv beta iota in C1; try discriminate C1.
cbv beta iota. rewrite S1. cbv beta iota.
apply andb_prop in C1 as [_ E1]. apply Z.eqb_eq in E1. exists rd0. rewrite E1. reflexivity.
Qed.

(* ======================================================================================================== *)
(* ---- IMAGE-FREE TREE AND WORD LEMMAS, transcribed from the lane's unlanded slice files (Crt102Arms.v at
   commit 9cd06e6c389 :72-226 / :237-271 / :330-347, dev build rc=0 there; Crt102Rewrite.v at
   commit 2eddf107d30 :165-213), names prefixed crt3_; delete at the slices' landing. ---- *)
Section rd.
Variable segs : list Segment.

Lemma crt3_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi' p D.
Proof.
intros m lblk Pi Pi' p D H (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. exact (H _ _ _ _ _ H6).
Qed.
Lemma crt3_pf_items_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_itemsR segs m lblk P ks a ka n D -> pf_itemsR segs m lblk Q ks a ka n D.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_itemsR] in *; [exact Hp|].
destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.
Lemma crt3_fd_succ : forall m lblk d p D, pj_fdR segs m lblk d p D -> pj_fdR segs m lblk (Datatypes.S d) p D.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fdR] in H |- *.
- eapply (crt3_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
- eapply (crt3_fshape_mono m lblk); [|exact H]. intros ks kids keys n Di Hi. cbv beta in Hi |- *.
  apply (crt3_pf_items_mono m lblk (pj_fdR segs m lblk d)); [|exact Hi]. intros a D1 H1. exact (IH a D1 H1).
Qed.
Lemma crt3_fd_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d' p D.
Proof. intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|]. apply crt3_fd_succ. apply IH. exact H. Qed.
Lemma crt3_items_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_itemsR P a l D -> pf_itemsR segs m lblk Q false a ka (length l) D.
Proof.
intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_itemsR pf_itemsR length] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.
Lemma crt3_mems_pf : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
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
Lemma crt3_nodeR_fd : forall t m lblk p D, pj_nodeR segs m lblk p t D -> pj_fdR segs m lblk (PjTree.depth t) p D.
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
  { rewrite En, Nat2Z.id. apply (crt3_items_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 Hu HP. rewrite Forall_forall in IH. apply (crt3_fd_mono m lblk (PjTree.depth u)); [|exact (IH u Hu m lblk a D1 HP)].
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
    cbv beta. rewrite En, Nat2Z.id. apply (crt3_mems_pf m lblk (pj_nodeR segs m lblk)); [|exact Hi].
    intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (crt3_fd_mono m lblk (PjTree.depth u)); [|exact (IH m lblk a D1 HP)]. pose proof (PjTree.depth_member members nm u Hu). lia.
Qed.
(* the header word of a node is its tag (pj_nodeR's pj_hdrR clause; H2H5's H5CrtS2.v s2_node_hdr) *)
Lemma crt3_node_hdr : forall m lblk p t D, pj_nodeR segs m lblk p t D -> rd_u32 segs m p (PjTree.tag t).
Proof.
intros m lblk p t D H.
destruct t; cbn [pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & (_ & Hty & _) & _);
exact Hty.
Qed.
(* the frame lemma of a freeable tree: its header, its key words and its items lie in its footprint *)
Lemma crt3_pf_frame : forall m m' lblk (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D (X : Z -> Prop),
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
Lemma crt3_fdR_frame : forall d m m' lblk p D, pj_fdR segs m lblk d p D ->
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
    apply (crt3_pf_frame m m' lblk (pj_fdR segs m lblk d) (pj_fdR segs m' lblk d) ks (Z.to_nat n) kids keys Di
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
End rd.

(* the tag of an object is 6, of anything else not *)
Lemma crt3_tag_obj : forall t, PjTree.tag t = 6 -> exists ms, t = PjTree.JObj ms.
Proof. intros t H. destruct t; cbn in H; try discriminate H. exists members. reflexivity. Qed.
Lemma crt3_tag_nobj : forall t, PjTree.tag t <> 6 -> forall ms, t <> PjTree.JObj ms.
Proof. intros t H ms E. apply H. rewrite E. reflexivity. Qed.
Lemma crt3_tag_range : forall t, 0 <= PjTree.tag t <= 6.
Proof. intros t. destruct t; cbn; lia. Qed.

(* the callee-saved float registers kept twice are kept *)
Lemma crt3_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

(* a word read back through the view (transcribed from Reusable/YCem.v rdword_of_val_mem, which this lane cannot
   Require: its YCeh is an image-specific file that does not build on pins102) *)
Lemma crt3_rdword_of_val_mem : forall segs H mem a v,
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

Lemma crt3_fpchain_keep : forall (r1 r2 : reader) lo top ch bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch -> fpchain (rdword r2) bp top ch.
Proof.
intros r1 r2 lo top ch. induction ch as [|[[fp ra] nfp] ch IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r. rewrite (Hkeep (bp - 8)) by lia. auto.
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

(* ======================================================================================================== *)
(* ---- THE WRITER'S TREE VISIBILITY AT ANY ARx STATE (the A' walk's ruling: derivable, no named hypothesis).
   prhWriter_tree_vis W mem Dt (= YGcfTreeVis.tree_vis_cf) for a list of HARNESS blocks the ledger at that state
   lists: per block (a, k), prh_hblock gives the allocator block (a - cf_head, k + cf_head) with its base in Hp and
   a mod 16 = 0; the user range's shadow and hull are AR_laws_x field 14 (alx_hshadow at hl = cf_head), the user bytes
   are present by field 1 (alx_blocks), the granule after them by field 15 (alx_blocks_tail; the block's end
   a - cf_head + (k + cf_head) IS a + k). The four memory-free conjuncts are a per-block hypothesis: for the
   document's blocks they come from the text's own entry premise ck_tree_ok, for a block a callee made from its
   request bound. Model: walk S10's S10TxState.v s10_bvis_lam. ---- *)
Section tv. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {PI : PrhImg}.
#[local] Existing Instance CfParams_preset.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.

Lemma crt3_tree_vis_keep : forall ly S Hp W mem md Lamc peakc cntc failc ranc mostc ownc Dt,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lamc peakc cntc failc ranc mostc ownc ->
  (forall bk, In bk Dt -> In bk Lamc) ->
  (forall a k, In (a, k) Dt -> 4096 <= a /\ 0 <= k < 2 ^ 32 /\ (a + k + 7) / 8 * 8 <= YM05.alloc_ceiling /\
     amem_range a ((a + k + 7) / 8 * 8 - a)) ->
  PRH_FnWriter.prhWriter_tree_vis W mem Dt.
Proof.
intros ly S Hp W mem md Lamc peakc cntc failc ranc mostc ownc Dt HAR HL HDt HP a k Hin.
destruct (HP a k Hin) as (H4096 & Hk & Hceil & Hamr).
pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lamc peakc cntc failc ranc mostc ownc HL)
  (a, k) (HDt _ Hin))
  as (Hk0 & Hab & Hhp & H16 & _).
cbn [fst snd] in Hk0, Hab, Hhp, H16.
assert (Hh0 : @cf_head CfParams_preset = 16) by reflexivity.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & _ & Hpres & _).
assert (Hrq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_hshadow segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab Hhp) as [Hbs Hhull].
rewrite Hrq in Hbs, Hhull, Hpres. replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia.
replace (k + cf_head - cf_head) with k in Hbs, Hhull by lia.
split; [exact H4096|]. split; [exact Hk|]. split; [exact Hceil|]. split; [exact Hamr|].
split; [exact (block_shadow_range (aview segs (w_H W) mem) SHADOW_OFF a k a k Hbs ltac:(lia) ltac:(lia))|].
split; [intros Hkp; apply Hhull; lia|].
intros x Hx. destruct (Z_lt_le_dec x (a + k)) as [Hlt|Hge].
- destruct (proj1 (Hpres x ltac:(lia))) as (Hh & bb & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
- apply (alx_blocks_tail segs B ARx LAWS ly S Hp W mem md _ _ x HAR Hab). rewrite Hrq.
  replace (a - cf_head + (k + cf_head)) with (a + k) by lia. lia.
Qed.
End tv.

(* a word read through readers that agree on its 8 bytes (S10Env.v:223 ts_rdword_keep, which is image-A' only) *)
Lemma crt3_rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* ---- IMAGE B's BOUNDS, never image A's (YImgTop.v:27-32: on #102 IMG_TOP = 0x600000 is A's top, B's is IMG_TOP_B =
   0x601000; a sweep of the unit, 19:21Z). ---- *)
(* image B's shadow is visible, the STAND-IN for the image fact (owner: the instance owner, the instance's supply):
   the instance owner's YGcfAmx2.img_shadow_vis_cf (lib/Reusable/YGcfAmx2.v:47-49) at image B's CfImgB.CfImg_B,
   i.e. over [cf_img_lo, cf_img_top) = [IMG_LO_B, IMG_TOP_B) (lib/AU/CfImgB.v:60-62), as the allocator lane's
   FuzzStrdupB (commit e8c226ad89c3, lib/B/Prog/FuzzStrdupB.v:301-305) states it, with
   ARcf segs B -> ARx: this row's stage Sections take the allocator relation ARx as a Variable, as the contract
   texts do. At ARx := ARcf (ci := CfImg_B) segs B it IS the
   instance owner's definition at ci := CfImg_B (crt3_img_shadow_vis_B_a8, both directions by the identity; ARcf
   takes its CfImg by name, the AU/CfApiPresetB.v form). Replaces walk S4's PRW_HShadow.ARx_img_shadow_vis,
   which is stated over image A's IMG_LO / IMG_TOP. *)
Section t3vis. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition crt3_img_shadow_vis_B (segs : list Segment)
  (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall ly S Hp (W : world segs) mem md a, ARx ly S Hp W mem md ->
  @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview segs (w_H W) mem (shadow_addr a) <> None.
Lemma crt3_img_shadow_vis_B_a8 : forall (cp : CfParams) (segs : list Segment) (B : asyms),
  YGcfAmx2.img_shadow_vis_cf (ci := CfImgB.CfImg_B) (cp := cp) segs B <->
  crt3_img_shadow_vis_B segs (YG0ncf.ARcf (ci := CfImgB.CfImg_B) (cp := cp) segs B).
Proof. intros cp segs B. split; intro H; exact H. Qed.
End t3vis.
(* CfImg_B's hull is image B's, by name *)
Lemma crt3_cfimgB_lo : @cf_img_lo CfImgB.CfImg_B = IMG_LO_B.
Proof. reflexivity. Qed.
Lemma crt3_cfimgB_top : @cf_img_top CfImgB.CfImg_B = IMG_TOP_B.
Proof. reflexivity. Qed.

Section t3img. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
(* Crt102Img's Section b hypotheses, the two this file reads (B' values in Crt102Img.v:1002-1008) *)
Hypothesis HB_base : BASE = B_prog_base.
Hypothesis HB_segs : SEGS = B.Img0.rsegs.

(* the instance's high half at +0x288 *)
Lemma crt3_hi_pa : exists rd', hi_of (segf SEGS) (BASE + (CRT_PC_B + CRT_O1_OFF_B)) = Some (rd', VAL (A_HI 35)).
Proof.
destruct (crt3_hi_cert (clookup pa_tbl) pa_val pa_sigma B_prog_listing (CRT_PC_B + CRT_O1_OFF_B) (26%bv : bv 5) 35
  pa_cert (proj1 crt_own_lst_B)) as (rd' & H).
exists rd'. exact (hi_of_tbl SEGS pa_tbl pa_tbl_ok _ _ H).
Qed.

(* g_own_ran_out is the listing's object 13 on B', and O1's auipc leaves its address - 0x2d0 in s10 *)
Lemma crt3_own13 : VAL (A_OBJ 13) = @pi_g_own_ran_out prh_img_B.
Proof.
destruct crt_own_lst_B as (H1 & H2).
pose proof (pa_res_ld (PA := PA) (CRT_PC_B + CRT_O1_OFF_B) (CRT_PC_B + CRT_O1_OFF_B + 4) _ _ _ _ _ _ _ H1 H2) as R.
rewrite HB_segs, HB_base in R. rewrite Z.add_0_r in R.
assert (C : res_pair (segf B.Img0.rsegs) (B_prog_base + (CRT_PC_B + CRT_O1_OFF_B))
              (B_prog_base + (CRT_PC_B + CRT_O1_OFF_B + 4)) = Some (@pi_g_own_ran_out prh_img_B))
  by (vm_compute; reflexivity).
rewrite C in R. injection R as R. symmetry. exact R.
Qed.
Lemma crt3_hi35 : VAL (A_HI 35) = @pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B.
Proof.
destruct crt3_hi_pa as (rd' & H). rewrite HB_segs, HB_base in H.
apply (f_equal (option_map snd)) in H. cbn [option_map snd] in H.
assert (C : option_map snd (hi_of (segf B.Img0.rsegs) (B_prog_base + (CRT_PC_B + CRT_O1_OFF_B))) =
            Some (@pi_g_own_ran_out prh_img_B - CRT_OWN_LO_B))
  by (vm_compute; reflexivity).
rewrite C in H. injection H as H. symmetry. exact H.
Qed.

(* the two strings lie inside IMAGE B's hull with the 64-byte margin the image route asks (kept_img's hull, at image B's
   bounds IMG_LO_B / IMG_TOP_B): read off the instance's own instruction words (crt_str_res_B: the auipc / addi pairs
   at +0x24c / +0x250 and +0x270 / +0x274) at the B segments, by vm_compute. The B' fact the stage files' hull lemmas
   take, never derived from image A's IMG_LO / IMG_TOP (the text's kept_img premise is not read for it). *)
Lemma crt3_str_hull_B :
  IMG_LO_B + 64 <= CRT_MOD_AT_B (PA := PA) /\
  CRT_MOD_AT_B (PA := PA) + (Z.of_nat (length ck_MOD_AT) + 1) + 64 <= IMG_TOP_B /\
  IMG_LO_B + 64 <= CRT_STAMP_B (PA := PA) /\
  CRT_STAMP_B (PA := PA) + (Z.of_nat (length ck_STAMP) + 1) + 64 <= IMG_TOP_B.
Proof.
destruct (crt_str_res_B (PA := PA)) as (H1 & H2 & _). rewrite HB_segs, HB_base in H1, H2.
assert (C : match res_pair (segf B.Img0.rsegs) (B_prog_base + (CRT_PC_B + CRT_MODAT1_HI_B))
                    (B_prog_base + (CRT_PC_B + CRT_MODAT1_LO_B)),
                  res_pair (segf B.Img0.rsegs) (B_prog_base + (CRT_PC_B + CRT_STAMP1_HI_B))
                    (B_prog_base + (CRT_PC_B + CRT_STAMP1_LO_B)) with
            | Some pm, Some ps =>
                (IMG_LO_B + 64 <=? pm) && (pm + (Z.of_nat (length ck_MOD_AT) + 1) + 64 <=? IMG_TOP_B) &&
                (IMG_LO_B + 64 <=? ps) && (ps + (Z.of_nat (length ck_STAMP) + 1) + 64 <=? IMG_TOP_B)
            | _, _ => false
            end = true)
  by (vm_compute; reflexivity).
rewrite H1, H2 in C.
apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
apply Z.leb_le in C1, C2, C3, C4. repeat split; assumption.
Qed.
End t3img.

(* ======================================================================================================== *)
(* THE ROW'S SECTION: the same binders, as IMPLICIT Contexts, in the same order as Crt102Glue.v (Section w / f / g),
   so every name below is instantiated BY NAME, as the glue's are. Every stage file opens this Section with the same
   lines.                                                                                                       *)
Section t3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head} {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).

Section f.
Context {B : asyms}.
Context {ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop}.

Section g.
Context {rp_sm : list Z -> Z * Z} {rp_x : list Z} {rp_os : list (option nat * option nat * option nat)}
  {rp_i : nat} {rp_H0 : list Z} {rp_hist : list YG00.chunk}.
Context {ly : alayout} {S : astate} {Hp : list Z} {W : world SEGS} {regs : bvmap 5 word}
  {mem : word -> option byte} {md : Model} {ch : list (Z * Z * Z)}
  {doc : Z} {t : PjTree.jv} {D : list (Z * Z)} {x : list Z}
  {Lam : list (Z * Z)} {peak cnt ran most : Z}
  {CTX0 : list (list Z)}.
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (CRT_sp1 (regs := regs)).
(* crt_side / crt_live take no rp_* since 11c39f7e88b7 (the position moved to crt_pos) *)
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation posB := (crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (t := t)).
#[local] Notation evsW := (crt_evs_W (rp_sm := rp_sm)).
#[local] Notation spillB := (crt_spill (L := B_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation dregsB := (crt_dregs_B (regs := regs) (doc := doc)).
#[local] Notation QFb := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgB := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).
#[local] Notation atU := (crt_at_U_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os)
  (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation atX := (crt_at_X_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os)
  (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation atW := (crt_at_W_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os)
  (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation tcB := (crt_tc (t := t)).
#[local] Notation cwB := (crt_cw (t := t) (cnt := cnt)).
#[local] Notation F_ lyc pos := (frame_addr lyc CRT_CID pos).

(* ---- copy's blocks against the writer's sizes UP TO PERMUTATION: crt_at_U_B's block conjunct, which S carries
   (tpj_set_specX's premise, PRH_FnPj.v:829 `Permutation (map (fun b => snd b + cf_head) D) (tblk (JObj ms))`).
   The ORDERED form is gone at this base (the glue's ruling ~20:0xZ: the model ties the live set to the run only
   up to permutation), so the header's cap no longer follows from it - crt3_cap below carries it instead. ---- *)
Definition crt3_tblk (Db : list (Z * Z)) : Prop :=
  Permutation (map (fun b => snd b + cf_head) Db) (PresetReqAtNoMiss.tblk t).

(* ---- copy's HEADER CAP: crt_at_U_B's own conjunct (Crt102Glue.v, `cap = Z.of_nat (PresetReqAt.ncap (length ms))`
   at the copy's pj_hdrR), CITED, never re-derived. It is pj_set's `cap` argument (prhPj_set_evs .. n cap, supplied
   through prhPj_set_evs_supply, PRH_FnPj.v:456-457). Crt102Model.cm_cap_of_tblk still asks the ORDERED block list,
   which no instance has at this base; the row holder's counterexample in the glue shows the Permutation does not fix
   cap. U carries this through pj_string's call to S. ---- *)
Definition crt3_cap (Wc : world SEGS) (memc : word -> option byte) (p : Z)
  (ms : list (list Z * PjTree.jv)) : Prop :=
  forall ty num str kids keys n cap,
    pj_hdrR SEGS (mrestrict (w_H Wc) memc) p ty num str kids keys n cap ->
    cap = Z.of_nat (PresetReqAt.ncap (length ms)).

(* ---- copy's blocks after the rewrite, up to permutation, and the tree's depth: what crt_at_W_B, crt_at_L3_B /
   crt_at_C_B and crt_at_J_B's r = 0 arm ask of copy (Crt102Glue fffec0d3ce0d). Produced at S by tpj_set_specX's
   granted arms (PRH_FnPj dc0d0aa79c0f:825-845, both in the permutation form) and carried to O1. ---- *)
Definition crt3_copy_tblk (Dc : list (Z * Z)) : Prop :=
  Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk (crt_tree_J (t := t))) /\
  (PjTree.depth (crt_tree_J (t := t)) <= DOC_D)%nat.

(* ---- copy's ORDERED FREE LIST before the rewrite: crt_at_U_B_copy_fo's text (Crt102Glue.v, the U field, producer
   row T2) at a later state of the stage, i.e. at S, where it is tpj_set_specX's ordered entry premise
   (PRH_FnPj 5aca5cbe2cfb, `cf_head = PresetReqAt.HEAD -> forall nn, .. exists F, pj_foR .. nn o D F /\ map .. F =
   fo (JObj ms)`). U carries it across pj_string's call by PRH_PjOrder.pj_foR_frame. ---- *)
Definition crt3_copy_fo0 (Wc : world SEGS) (memc : word -> option byte) (Lamc : list (Z * Z)) (p : Z)
  (Db : list (Z * Z)) (ms : list (list Z * PjTree.jv)) : Prop :=
  cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
    exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) nn p Db F /\
      map (fun b => snd b + cf_head) F = PresetReqAt.fo (PjTree.JObj ms).

(* ---- copy's ORDERED FREE LIST after the rewrite: crt_at_W_B_copy_fo's text (Crt102Glue.v), produced at S by
   tpj_set_specX's FREEORD-COPY conjunct on both granted arms and carried to O1 and W. ---- *)
Definition crt3_copy_fo (Wc : world SEGS) (memc : word -> option byte) (Lamc : list (Z * Z)) (p : Z)
  (Dc : list (Z * Z)) : Prop :=
  exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D p Dc Fc /\
    map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (crt_tree_J (t := t)).

(* ---- THE ROOM POSITION across a call: crt_pos Sc (evs1 ++ evs2) names the model position i the walk is at, with
   the run's events from i and the CONSUMER WINDOW over them (crt_pos's two new conjuncts at this base,
   Crt102Glue.v: `rp_sm = ReaderRes.jr_strtod` in front and `PRH_Base.prh_cons_from .. (length evs)` at the end); a
   callee text applied at i whose post gives the position at i + length evs1 leaves the walk at crt_pos Sc' evs2.
   DESTRUCTURED BY NAME: the window splits with PRH_Base.prh_cons_from_app_iff, exactly as the run premise splits
   with prh_run_at_app_iff. ---- *)
Lemma crt3_pos_adv : forall Sc evs1 evs2, posB Sc (evs1 ++ evs2) ->
  exists i hist, rp_sm = ReaderRes.jr_strtod /\
    PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 hist Sc /\
    prh_run_at rp_sm rp_x rp_os i (evs1 ++ evs2) /\
    prh_cons_from rp_sm rp_x rp_os i (length (evs1 ++ evs2)) /\
    forall Sc', (exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (i + length evs1)%nat rp_H0 hist' Sc') ->
      posB Sc' evs2.
Proof.
intros Sc evs1 evs2 H.
pose proof (crt_pos_strtod H) as Hsm.
destruct (crt_pos_ex H) as (pre & hist & HA).
pose proof (crt_pos_split HA) as Ert.
pose proof (crt_pos_room HA) as Hpos.
pose proof (crt_pos_run HA) as Hrun.
pose proof (crt_pos_cons HA) as Hcons.
exists (rp_i + length pre)%nat, hist.
split; [exact Hsm|]. split; [exact Hpos|]. split; [exact Hrun|]. split; [exact Hcons|].
intros Sc' (hist' & Hpos').
refine {| crt_pos_strtod := Hsm; crt_pos_ex := _ |}.
exists (pre ++ evs1), hist'.
refine {| crt_pos_split := _; crt_pos_room := _; crt_pos_run := _; crt_pos_cons := _ |}.
- rewrite Ert, app_assoc; reflexivity.
- rewrite length_app, Nat.add_assoc. exact Hpos'.
- rewrite length_app, Nat.add_assoc. exact (proj2 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) Hrun)).
- rewrite length_app, Nat.add_assoc. rewrite length_app in Hcons.
  exact (proj2 (proj1 (prh_cons_from_app_iff _ _ _ _ _ _) Hcons)).
Qed.

(* U's suffix is the rewrite's pj_string / pj_set events, then W's (PresetReqAt.rw_evs, the glue's crt_evs_U / _W / _L0) *)
Lemma crt3_evsU_split : forall ms, crt_evs_U (rp_sm := rp_sm) ms = PresetReqAt.set_evs ms ++ evsW ms.
Proof. intros ms. unfold crt_evs_U, crt_evs_W, crt_evs_L0, PresetReqAt.rw_evs. rewrite <- !app_assoc. reflexivity. Qed.
(* set_evs's head is pj_string's strdup; its tail is pj_set's own list at copy's parsed header *)
Lemma crt3_set_evs_cons : forall ms, PresetReqAt.set_evs ms =
  PresetReqAt.HMal (Z.of_nat (Datatypes.S (length PresetReqAt.MOD_VAL)) + PresetReqAt.HEAD) ::
  tl (PresetReqAt.set_evs ms).
Proof. intros ms. reflexivity. Qed.
Lemma crt3_set_evs_tl : forall ms, tl (PresetReqAt.set_evs ms) =
  PRH_FnPj.prhPj_set_evs ms PresetReqAt.MOD_KEY (Z.of_nat (length ms)) (Z.of_nat (PresetReqAt.ncap (length ms))).
Proof.
intros ms. unfold PRH_FnPj.prhPj_set_evs. rewrite PRH_FnPj.prhPj_mfind_mod, !Nat2Z.id. reflexivity.
Qed.

(* ---- S (+0x270): pj_string (&v, STAMP) returned 0. Its new block (a, 21) is v's string and the walk holds it beside
   the read-back Db; v (F + 0x80) is the string node; copy is still the read-back tree; s5 = &v (+0x248); the U spills
   are written; g_count is the two round_trip_text calls' plus the strdup; the room position is one event on (the
   strdup's HMal, set_evs's head). pj_set's premises at +0x280 follow from it and the Section's text premises
   (Crt102B_T3S.v). ---- *)
Definition crt_at_S3 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Db Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (a : Z) : Prop :=
  t = PjTree.JObj ms /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveB (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos
    ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) Lamc peakc cntc 0 0 /\
  dregsB rg (F_ lyc pos) /\ getr rg 21 = w64 (F_ lyc pos + CRT_OFF_V) /\
  spillB Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) /\
  spillB Wc memc CRT_SP_PN_B (doc + PJ_OFF_N) /\
  spillB Wc memc CRT_SP_N_B (Z.of_nat (length ms)) /\
  ck_tree_ok lyc Sc Lamc Wc memc doc t D /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F_ lyc pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F_ lyc pos + CRT_OFF_V) 56 /\
  crt_copy_tree Wc memc Lamc (F_ lyc pos) t Db /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (F_ lyc pos + CRT_OFF_V) (PjTree.JStr ck_STAMP)
    [(a, Z.of_nat (length ck_STAMP) + 1)] /\
  (forall a' k, In (a', k) ((a, Z.of_nat (length ck_STAMP) + 1) :: Db) ->
     ~ In (a' - cf_head, k + cf_head) (ablocks B ly S)) /\
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
  cntc = ck_cnt2 cnt t + 1 /\
  crt3_tblk Db /\
  (* copy's header cap, CITED from crt_at_U_B and carried across pj_string's call (U is the only producer: the
     glue's counterexample shows the block permutation does not fix it) *)
  crt3_cap Wc memc (F_ lyc pos + CRT_OFF_COPY) ms /\
  posB Sc (tl (PresetReqAt.set_evs ms) ++ evsW ms) /\
  (* copy's ordered free list, crt_at_U_B_copy_fo carried across pj_string's call: tpj_set_specX's ordered entry
     premise *)
  crt3_copy_fo0 Wc memc Lamc (F_ lyc pos + CRT_OFF_COPY) Db ms.

(* ---- O1 (+0x288): the two flag tests, reached ONLY with both calls granted. A refusal in pj_string or pj_set is
   DEAD at its source, by the callee TEXT's own clause: tpj_string_specX's DEAD-PJSTRING conjunct
   `(cnt <> fail -> a <> 0)` and tpj_set_specX's DEAD-PJSET conjunct `(fail < cnt \/ cnt + |trace| <= fail) ->
   res = 0` (PRH_FnPj 5aca5cbe2cfb), at fail = SIZE_MAXZ (the text's entry ledger) and cnt < 2 ^ 62. So s8 = sbit = 1
   (pj_set's `seqz` of 0) and g_ran_out = ranc = 0 here, both flag tests fall through, the `!set` abort at +0x2a0 and
   the C4a exit to X (+0x30c, r = 1, which crt_at_X_B's crt_at_J_B_r0 forbids) are unreachable. The walk holds
   exactly the blocks of copy (Dc); cset is pj_set's allocation count; copy holds crt_tc over Dc, the count is crt_cw
   cset, the facts crt_at_W_B asks beyond the boundary's (incl. copy's ordered free list), and the room position
   after set_evs. ---- *)
Definition crt_at_O1_3 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cntc ranc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset sbit : Z) : Prop :=
  t = PjTree.JObj ms /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveB (prh_wk F_round_trip_text + prh_wk F_round_trip_text)%nat lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc
    0 ranc /\
  dregsB rg (F_ lyc pos) /\ getr rg 24 = w64 sbit /\ sbit = 1 /\
  spillB Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) /\
  spillB Wc memc CRT_SP_PN_B (doc + PJ_OFF_N) /\
  spillB Wc memc CRT_SP_N_B (Z.of_nat (length ms)) /\
  doc mod 8 = 0 /\ range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F_ lyc pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F_ lyc pos + CRT_OFF_V) 56 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (F_ lyc pos + CRT_OFF_COPY) Dc /\
  cnt <= cntc <= cnt + ck_crt_count t cset /\
  ranc = 0 /\
  (sbit = 1 ->
     cntc = cwB cset /\
     pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (F_ lyc pos + CRT_OFF_COPY) tcB Dc /\
     PRH_FnWriter.prhWriter_tree_vis Wc memc Dc /\
     YCbq.bsum (ck_hblks Dc) <= LIVE_round_trip_text t false + LIVE_round_trip_text t true +
       PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
       PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) /\
     posB Sc (evsW ms) /\
     crt3_copy_tblk Dc /\
     crt3_copy_fo Wc memc Lamc (F_ lyc pos + CRT_OFF_COPY) Dc).

(* ---- the stage statements: each boundary is `the run from this configuration reaches QF` (Crt102Glue.v:244-247).
   CRT3_X is the glue's CRT_B_AT_X at CRT_PC := CRT_PC_B, CRT_X_OFF := CRT_X_OFF_B, convertible to it
   (Crt102B_T3.v checks it by reflexivity). ---- *)
Definition CRT3_X : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  atX fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_X_OFF_B rg memc mdc) QFb.
Definition CRT3_W : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset,
  atW fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc rg ms cset ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_W0_OFF_B rg memc mdc) QFb.
Definition CRT3_O1 : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg ms cset sbit,
  crt_at_O1_3 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cntc ranc rg ms cset sbit ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_O1_OFF_B rg memc mdc) QFb.
Definition CRT3_S : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a,
  crt_at_S3 fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms a ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_S_OFF_B rg memc mdc) QFb.
Definition CRT3_U : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
  atU fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_U_OFF_B rg memc mdc) QFb.

(* ======================================================================================================== *)
(* ---- THE ROW'S SUPPORT LEMMAS at the Section's entry binders: the stack, the frame, the document's home and tree,
   the chain at a call. Ports of the A' walk's slice lemmas (Crt102Arms.v arms_sp1 / arms_home_keep /
   arms_tree_ok / arms_chain, Crt102Rewrite.v crt102rw_ff) with the B' image's numbers (crt_stk_B, crt_frame_B). ---- *)
Section h.
(* the journal at a wild-trace budget WS at the contract's R (YCbqG.v ajournal_xwR at YA0nH.wle' SEGS
   YGcfRehidePost.RZ_cf; crt_live's journal is at a budget WS with wbudget [] kb WS, kb round) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.

(* the own frame of check_round_trip on B' is 240 bytes (0xe0 and the 32-byte realignment), within its budget *)
Lemma crt3_pi_frame : @pi_frame prh_img_B F_check_round_trip = 240.
Proof. vm_compute. reflexivity. Qed.
Lemma crt3_stk : 240 <= STKC.
Proof. pose proof crt_stk_B as (H & _). rewrite crt3_pi_frame in H. unfold ESTACK in H. lia. Qed.

(* ---- the entry sp and the realigned sp: 224 or 240 bytes below it, 32-aligned ---- *)
Lemma crt3_sp0 : sp0 mod 16 = 0 /\ YM05.alloc_ceiling + STKC <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 + 64 <= ly_stk_hi ly.
Proof.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO & Hhi & Hrac & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
split; [exact Hal16|]. split; [lia|]. split; [lia | exact Hhi].
Qed.
Lemma crt3_sp1 : sp1 mod 32 = 0 /\ sp0 - 240 <= sp1 <= sp0 - 224 /\ 0 <= sp1.
Proof.
pose proof crt3_sp0 as (Hal16 & Hc & H47 & _). pose proof crt3_stk.
pose proof (YM05.alloc_ceiling_val) as Hcv.
unfold CRT_sp1, CRT_FRAME, CRT_ALIGN. pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
assert ((sp0 - 224) mod 32 = 0 \/ (sp0 - 224) mod 32 = 16).
{ apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. lia. }
split; [apply Z.mod_mul; lia|]. split; [lia|]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.

(* ---- the frame (CRT_CID, pos) the journal owns: on the frame list, bounded, its bytes and shadow present ---- *)
Lemma crt3_ff : forall lyc Sc Hpc Wc memc mdc kj pos {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  In (CRT_CID, pos) (frames Sc) /\ ~ In (CRT_CID, pos) (frames S) /\
  4096 <= F_ lyc pos /\ F_ lyc pos + 512 <= YM05.alloc_ceiling /\
  in_app (F_ lyc pos) 512 /\ F_ lyc pos mod 32 = 0 /\
  (forall a, F_ lyc pos <= a < F_ lyc pos + 512 -> apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr (F_ lyc pos) + i) /\
     ~ aowned B lyc Sc (shadow_addr (F_ lyc pos) + i)).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos WS HJ.
pose proof HJ as (HARc & _ & _ & _ & _ & HFRc & _).
assert (HFB : fs_frame_bytes CRT_CID = 512) by (vm_compute; reflexivity).
assert (Hin : In (CRT_CID, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (F32 & _ & Ffr & Fsh).
rewrite HFB in Fb2, Fb3, Ffr, Fsh. change (512 / 8) with 64 in Fsh.
split; [exact Hin|]. split.
{ intros Hc. apply in_split in Hc as (l1 & l2 & El).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc
    (CRT_CID, pos) (CRT_CID, pos) [] l1 l2 HARc ltac:(rewrite HFRc, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd. lia. }
split; [exact Fb1|]. split; [exact Fb2|]. split; [exact Fb3|]. split; [exact F32|].
split; [exact Ffr | exact Fsh].
Qed.

(* ---- the document's home is a live fake frame of the entry, so its 56 bytes stay addressable at every state the
   journal from the entry reaches (FP = []: the frame clause keeps the frame's shadow) ---- *)
Lemma crt3_home_keep : forall own lyc Sc Hpc Wc memc mdc kj {WS : list (list Z)},
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
  assert (Hd : (doc + 56) / 8 = doc / 8 + 7).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 56) with ((q + 7) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
  pose proof (Z.div_le_mono (frame_addr ly cid pos) a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono a (doc + 55) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (doc + 56) (frame_addr ly cid pos + fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
  assert ((doc + 55) / 8 = doc / 8 + 6).
  { apply Z.mod_divide in Hd8; [|lia]. destruct Hd8 as [q Hq]. rewrite Hq.
    replace (q * 8 + 55) with (7 + (q + 6) * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. cbn. lia. }
  lia.
Qed.

(* ---- the document's tree as a callee asks it (ck_tree_ok) at any live state: the node and its blocks from
   crt_side, the blocks' visibility from crt3_tree_vis_keep (its memory-free facts from the entry's ck_tree_ok), the
   home from crt3_home_keep ---- *)
Lemma crt3_tree_ok : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc {kbg : nat},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> ck_tree_ok lyc Sc Lamc Wc memc doc t D.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kbg H.
destruct (crt_live_journal H) as (WSj & HJ & HBj). pose proof (crt_live_side H) as HSD.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_doc HSD) as HND.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HTREE as (_ & _ & HTV & _).
split; [exact HND|]. split; [exact HDL|]. split; [|exact (crt3_home_keep _ _ _ _ _ _ _ _ HJ)].
apply (crt3_tree_vis_keep B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc SIZE_MAXZ ranc most ownc D (proj1 HJ)
  HLED HDL).
intros a k Hin. destruct (HTV a k Hin) as (H1 & H2 & H3 & H4 & _). auto.
Qed.

(* ---- the frame-pointer chain at a call made at the realigned sp with s0 = the entry sp: check_round_trip's own
   record (its ra at sp0 - 8 and the caller's s0 at sp0 - 16, crt_saved's first two slots) pushed onto the chain it
   was given, unless the entry sp is within 16 of the layout's top ---- *)
Lemma crt3_chain : forall own lyc Sc Hpc Wc memc mdc kj {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS ->
  crt_saved (L := B_prog_listing) (PA := PA) (regs := regs) Wc memc ->
  exists ch1, achain lyc (aview SEGS (w_H Wc) memc) sp1 sp0 ch1 /\
    (ch1 = [] \/ ch1 = (sp0, raZ regs, s0Z regs) :: ch).
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ HSV.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO & Hhi & Hrac & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct crt3_sp1 as (Hs32 & Hs1 & Hs0).
assert (H8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr1. change (bv_modulus 64) with (2 ^ 64) in Hr1.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr8. change (bv_modulus 64) with (2 ^ 64) in Hr8.
assert (Hw1 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 8) = Some (raZ regs)).
{ apply crt3_rdword_of_val_mem; [|unfold raZ; lia]. exact (HSV 0%nat ltac:(lia)). }
assert (Hw8 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 16) = Some (s0Z regs)).
{ apply crt3_rdword_of_val_mem; [|unfold s0Z; lia]. exact (HSV 1%nat ltac:(lia)). }
destruct (Z_le_gt_dec (ly_top lyc - 16) sp0) as [Hbad|Hgood].
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hbad | reflexivity].
- exists ((sp0, raZ regs, s0Z regs) :: ch). split; [|right; reflexivity]. right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, sp0 <= a -> a < ly_top ly ->
            rdword (aview SEGS (w_H Wc) memc) a = rdword (aview SEGS (w_H W) mem) a).
  { intros a Ha Hat. apply crt3_rdword_keep. intros j Hj. apply F1; lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact Hw1|]. split; [exact Hw8|]. split; [exact Hra4|].
    destruct (bad_next sp0 (ly_top lyc) (s0Z regs)) eqn:Eb.
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
      rewrite Etop. apply (crt3_fpchain_keep (aview SEGS (w_H W) mem) (aview SEGS (w_H Wc) memc) sp0);
        [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbv beta. intros r Hr. lia.
Qed.
End h.

End g.
End f.
End t3.
