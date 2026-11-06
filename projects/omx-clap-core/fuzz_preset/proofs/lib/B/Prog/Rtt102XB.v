(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 551 of its 598 lines of code are new or changed and 467 lines of the source are left out. *)
(* B' TWIN (asan-ubsan d663f82d7f488d30, unstripped twin c90d4fa54d43160b) of lib/A/Prog/Rtt102XA.v, by a name map:
   round_trip_text's body on image B is image A's instruction sequence with only pc-relative immediates changed
   (capstone over both twins' symtab bodies; every call site at the same offset), so the twin is the A' file with
   image A's listing / image / PrhImg / CfImg names replaced by image B's (A_prog_* -> B_prog_*, PI_prog_A /
   PL_prog_A -> _B, prh_img_A -> prh_img_B, CfImg_A -> CfImg_B, S1ImgA -> S1ImgB, IMG_LO / IMG_TOP -> IMG_LO_B /
   IMG_TOP_B, the A' stretch modules Rtt102*A -> Rtt102*B, the file's own *_A names -> *_B) and image B's own value
   for each image numeral the file states (a load offset, the function's listing offset, a witness address); every
   closed image check is re-run at B' by the build. The comments below are the A' file's: their addresses and slot
   numbers are image A's. *)
(* fuzz_preset, program walk of round_trip_text on the #102 pins, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped
   twin bff8519bbe3ea0e4, entry A' 0x8496c, slot 3299 of lib/A/Listing_prog.v): STRETCH X of the cut layer
   lib/A/Prog/Rtt102Cut.v (lane WalkRtt102.RttX for the text owner): RTT_SEG_X = rtt_seg RT_X rtt_at_x.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma): stretch X of round_trip_text; the
   function-level gate is the text owner's (proof-index round_trip_text, EXIT=0, no released ASan proof).
   THE CODE, the function's bytes +0x1e0 .. +0x2e0 (A' 0x84b4c .. 0x84c4c, A' capstone listing 
   lines 122-186): back re-poisoned (F's shadow bytes 4 .. 10 := f8 through s9 = shadow_addr F), F + 0 := the retired
   magic (through s10 = F), `beqz s2` (+0x20c; s2 = F >= 4096, so the real-stack path +0x260 .. +0x29c is not taken:
   the segment's symbolic state carries the condition s2 <> 0, so the runner decides the branch), the fake path: the
   16 shadow bytes := f5, `ld a0, 0x78(s2)` (the flag pointer at F + RT_FLAGP, rtt_frame), `sb zero, 0(a0)` (the
   release), `mv a0, s5`, the epilogue (`addi sp, s0, -0xa0`, the 13 restores of rtt_saved's slots, `addi sp, sp,
   0xa0`) and `ret`. NO CALL: no open kit goal (G2 / G4 / C-TXTRACE) is on this stretch.
   THE PROOF. ONE run of the listing engine from a fresh symbolic state at +480 to the `ret`, through YGcallSx.v's
   aj_flag_store_xR (the journal's own [(1, pos)] becomes [] at stack_free_state 1 pos S), then YC1fP.v's
   paj_ret_at (a plain SRr, lifted by YA0nH.SRr_SRr'); the generic machine-level lemma is rx_run. AT THE R CUT
   (Rtt102Cut.v at 448ecd157e57) the stretch concludes YA0nH.SRr' SEGS RZ_cf and the journal is at RZW := YA0nH.wle'
   SEGS RZ_cf; the run keeps the world, so no fact crosses a wle' step. Template: S10TxString.v ts_G_entry / ts_at_G
   (the S10 walk at 37251f6b9a5, class 0; here class 1, the frame 128 bytes, its shadow 16). The
   text's post rtt_Q is built from the cut's rtt_Qx by keeping every byte the run does not write (rx_wr: F's first
   word, F's 16 shadow bytes, the flag byte): the ledger by S1Ledger.v prh_ledger_kept_aview, the trees by
   PRH_Reader.v pj_nodeR_frame and rx_nodeR_lblk (the block predicate widened to the cut's ledger list; the pure
   lemma s4_nodeR_lblk of the H2H5 walk head 1934271f1f40 lib/A/Prog/H5RttS4.v, restated here), the
   room by RL_stack_free / PresetRoomPosKeep.room_pos_stack_free, memnorm by YGcallMxmn.v memnorm_frame_of.
   AT THE BATCH KIT'S CUT (Rtt102Cut.v at 80a1d52c32c7): rtt_J is the journal from the DEPOT-MOVED entry, so the run's journal
   is too; the post is the BUDGETED fpostFbm, whose journal from the entry itself at a budget of at most 32 fresh wild
   traces is Rtt102Cut.v rtt_unbase of the run's journal and rtt_carry's last conjunct (rtt_wild at 32). rtt_Qx's
   copy <> 0 arm carries copy's ordered free list at every depth bound and K0-CAP (pj_ncapR); the run keeps both by
   PRH_PjOrder.v pj_foR_frame and Rtt102Cut.v rtt_ncapR_frame (PRH_Reader.v has no frame lemma for pj_ncapR).
   NUMERALS. DERIVED: 480 (RT_X of the cut layer), RTT_PC_B (4 * the listing slot of round_trip_text). LENGTH: 128
   (fs_frame_bytes 1), 16 (its shadow, 128 / 8), 8 (a word; F's first word), 120 (RT_FLAGP = 128 - 8), 104 (the
   13 saved words), 1 (a byte), 56 (struct pj), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (the shadow span, the
   stack band, the user range, the empty check span, the word). WORD: register indices, atom indices (64 = the flag
   address, the segment's one extra). No ADDRESS literal: the code address is pa_sigma / pa_val of PAImg_prog.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
(* the re-hiding move's world relation and step relation (YA0nH), the zone (YGcfRehidePost.RZ_cf), used qualified:
   the stretch concludes YA0nH.SRr' SEGS RZ_cf and the journal is at RZW := YA0nH.wle' SEGS RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image A': round_trip_text's entry (DERIVED: 4 * its listing slot) ---- *)
Definition RTT_PC_B : Z := 4 * Z.of_nat (B_prog_slot AS_round_trip_text).

(* ---- the tree with a wider block predicate (image-free; H5RttS4.v s4_cstr_lblk / s4_items_in / s4_mems_lblk /
   s4_nodeR_lblk at 1934271f1f40, restated over this tree's PRH_Reader.v): a tree reads its block predicate only on
   the blocks of its own D, so any predicate that holds there serves ---- *)
Section tr.
Variable segs : list Segment.

Lemma rx_cstr_lblk : forall m (lblk lblk' : Z -> Z -> Prop) a k s, pj_cstrR segs m lblk a k s ->
  (lblk a k -> lblk' a k) -> pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (Hl & Hr) H. split; [exact (H Hl) | exact Hr]. Qed.

Lemma rx_items_in : forall (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  pj_itemsR P a l D -> (forall a' u D1, In u l -> incl D1 D -> P a' u D1 -> P' a' u D1) -> pj_itemsR P' a l D.
Proof.
intros P P' l. induction l as [|u l IH]; intros a D H HP; cbn [pj_itemsR] in *; [exact H|].
destruct H as (D1 & D2 & ED & Hu & Hr). exists D1, D2. split; [exact ED|].
split; [apply HP; [left; reflexivity | subst D; intros b Hb; apply in_or_app; left; exact Hb | exact Hu]|].
apply (IH (a + 56) D2 Hr). intros a' u' D' Hu' Hinc HP'. apply HP; [right; exact Hu' | | exact HP'].
intros b Hb. subst D. apply in_or_app. right. exact (Hinc b Hb).
Qed.

Lemma rx_mems_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  (forall a' nm u D1, In (nm, u) l -> incl D1 D -> P a' u D1 -> P' a' u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] l IH]; intros a ka D H HL HP; cbn [pj_memsR] in *; [exact H|].
destruct H as (x & k & D1 & D2 & ED & Hx & Hc & Hu & Hr).
exists x, k, D1, D2. split; [exact ED|]. split; [exact Hx|].
split; [apply (rx_cstr_lblk m lblk lblk' x k nm Hc); apply HL; subst D; left; reflexivity|].
split; [apply (HP a nm u D1); [left; reflexivity | subst D; intros b Hb; right; apply in_or_app; left; exact Hb | exact Hu]|].
apply (IH (a + 56) (ka + 8) D2 Hr).
- intros x' k' Hin. apply HL. subst D. right. apply in_or_app. right. exact Hin.
- intros a' nm' u' D' Hu' Hinc HP'. apply (HP a' nm' u' D'); [right; exact Hu' | | exact HP'].
  intros b Hb. subst D. right. apply in_or_app. right. exact (Hinc b Hb).
Qed.

Lemma rx_nodeR_lblk : forall t m (lblk lblk' : Z -> Z -> Prop) p D, pj_nodeR segs m lblk p t D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (rx_cstr_lblk m lblk lblk' str k txt Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (rx_cstr_lblk m lblk lblk' str k s Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hc0 | (Hcp & Hl)]; [left; exact Hc0 | right; split; [exact Hcp|]].
    apply HL; [|exact Hl]. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (rx_items_in (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros a' u D1 Hu Hinc HP.
  rewrite Forall_forall in IH. apply (IH u Hu m lblk lblk' a' D1 HP).
  intros x k Hxk Hl. apply HL; [|exact Hl]. subst D. apply in_or_app. right. exact (Hinc _ Hxk).
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hc0 | (Hcp & Hl1 & Hl2)]; [left; exact Hc0 | right; split; [exact Hcp|]].
    split; (apply HL; [|assumption]); subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia;
      [left; reflexivity | right; left; reflexivity]. }
  exists Di. split; [exact ED|].
  apply (rx_mems_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi).
  + intros x k Hxk Hl. apply HL; [|exact Hl]. subst D. apply in_or_app. right. exact Hxk.
  + intros a' nm u D1 Hu Hinc HP.
    rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (IH m lblk lblk' a' D1 HP).
    intros x k Hxk Hl. apply HL; [|exact Hl]. subst D. apply in_or_app. right. exact (Hinc _ Hxk).
Qed.

(* a tree whose footprint keeps its bytes, in a memory that only grows, is the same tree *)
Lemma rx_nodeR_keep : forall m m' lblk p t D, pj_nodeR segs m lblk p t D -> mem_grows m m' ->
  (forall x, pj_footR p D x -> mbyte segs m' x = mbyte segs m x) -> pj_nodeR segs m' lblk p t D.
Proof.
intros m m' lblk p t D H Hg HK. apply (pj_nodeR_frame segs t m m' lblk p D H).
intros x Hx. split; [exact (HK x Hx) | intros Hw; exact (writable_at_grows segs m m' x Hg Hw)].
Qed.
End tr.

(* ---- X's writes: the frame's first word, its 16 shadow bytes, the flag byte ---- *)
Definition rx_wr (ly : alayout) (pos a : Z) : Prop :=
  (frame_addr ly 1 pos <= a < frame_addr ly 1 pos + 8) \/
  (shadow_addr (frame_addr ly 1 pos) <= a < shadow_addr (frame_addr ly 1 pos) + 16) \/
  a = flag_addr ly 1 pos.

(* ---- the segment's symbolic state at +480: gp, tp pinned to the entry's, s0 to the entry sp (atom 2); the
   condition s2 <> 0 (s2 = F); regions: F's 16 shadow bytes (s9, written), F's first word (s10, written), the flag
   pointer at F + 120 (s2, read), the flag byte (atom 64, written), the prologue's saves below the entry sp ---- *)
Definition sr_X : list sv := sr_set (sr_set (sr_set cur_atoms 3%bv (SOff 3 0)) 4%bv (SOff 4 0)) 8%bv (SOff 2 0).
Definition X_saves : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
   YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-104) (CVal 8 (SOff 27 0))].
Definition ss_X : sstate := mkSS (RTT_PC_B + RT_X) sr_X
  [ YP09.mkRegion (Some (xr 25)) 0 16 0 16 [];
    YP09.mkRegion (Some (xr 26)) 0 8 0 8 [];
    YP09.mkRegion (Some (xr 18)) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some 64%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 2%nat) (-104) 0 0 0 X_saves ] None
  (mkFacts [(xr 25, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (xr 26, mkAF 4096 (2 ^ 47) 5);
            (xr 18, mkAF 4096 (2 ^ 47) 5); (64%nat, mkAF 0 (2 ^ 47) 0); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)]
           [mkAC BC_NE (SOff (xr 18) 0) (SLit 0)] []).

Section w. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

Lemma RTT_PC_val : BASE + RTT_PC_B = SIGMA AS_round_trip_text.
Proof. vm_compute. reflexivity. Qed.
Lemma pst_img_B : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. exact pst_in_img_B. Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variables (CTX0 : list (list Z)).
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the allocator laws at the cf instance's head (engine fold, YCbqG.v: AR_laws_x at hl := cf_head) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* ---- frame class 1, the inline release: exactly the hypotheses of YGcallSx.v's aj_flag_store_x (engine fold), as
   S10TxString.v:173-196 takes them for class 0 (owned by the kit / the frame-class lane at the instance: ASFX =
   YG0dcf.v astack_free_law_cf, FFLX = the two conjuncts of frame_flag_lawP over ARx, SFX = YG05cf.v
   stack_free_ok_cf; OWNLOW = YGcallx.v ARx_owned_low_law, a Section hypothesis of YGcallSx.v Section x) ---- *)
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* MARKED STAND-IN (owner: the cf instance owner; WalkS10's ruling 2026-10-29, as S10TxString.v:192-196): the frame's flag byte is
   present, so the release's flag store has a writable region (discharged at ARcf by AR_flag_law_ok_cf's first
   conjunct, as H5CrtS7.v crt7_fflx does) *)
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
(* The kit's ONE spelling of the head width (PRH_Base.v:187-195; owner the preset instantiation, the cf instance owner's
   preset_head_wide, lib/A/CfParamsPreset.v:95): a harness block's 8 head bytes lie inside its allocator block, so the
   run (which writes none of a live block's bytes) keeps the ledger's head words *)
Hypothesis HW : prh_head_wide.

(* ---- what the run keeps: every byte of a live block, of another live frame, of the image ---- *)
Lemma rx_ablocks_sf : forall ly c p S, ablocks B ly (stack_free_state c p S) = ablocks B ly S.
Proof. intros ly c p S. unfold ablocks. rewrite blocks_stack_free_state. reflexivity. Qed.

Lemma rx_keep_blk : forall ly S Hp W mem md pos p n a, ARx ly S Hp W mem md -> In (1, pos) (frames S) ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ rx_wr ly pos a /\ 0 <= a < 2 ^ 64.
Proof.
intros ly S Hp W mem md pos p n a HAR Hin Hpn Ha.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hpn) as (_ & Hb4 & Hbc & Hbapp & Hbown & _).
pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md p n 1 pos HAR Hpn Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
destruct (FFLX ly S Hp W mem md 1 pos HAR Hin) as (Fown & _ & _).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md 1 pos HAR Hin) as (Fb1 & Fb2 & _).
change (fs_frame_bytes 1) with 128 in Fb2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|lia].
unfold rx_wr. intros [Hw | [Hw | Hw]].
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF, ASAN_CEIL in *. lia.
- exact (proj2 (Hbown a Ha) ltac:(rewrite Hw; exact Fown)).
Qed.

Lemma rx_keep_frm : forall ly S Hp W mem md pos l1 l2 cid p a, ARx ly S Hp W mem md ->
  frames S = (1, pos) :: l1 ++ (cid, p) :: l2 ->
  frame_addr ly cid p <= a < frame_addr ly cid p + fs_frame_bytes cid -> ~ rx_wr ly pos a /\ 0 <= a < 2 ^ 64.
Proof.
intros ly S Hp W mem md pos l1 l2 cid p a HAR EF Ha.
assert (Hin1 : In (1, pos) (frames S)) by (rewrite EF; left; reflexivity).
assert (Hin2 : In (cid, p) (frames S)) by (rewrite EF; right; apply in_or_app; right; left; reflexivity).
pose proof (sep_frames_pos_x _ _ _ LAWS ly S Hp W mem md (1, pos) (cid, p) [] l1 l2 HAR
  ltac:(rewrite EF; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid p HAR Hin2) as (G1 & G2 & G3).
destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid p HAR Hin2) as (_ & _ & Gfr & _).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md 1 pos HAR Hin1) as (Fb1 & Fb2 & _).
change (fs_frame_bytes 1) with 128 in Fb2.
destruct (FFLX ly S Hp W mem md 1 pos HAR Hin1) as (Fown & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|lia].
unfold rx_wr. intros [Hw | [Hw | Hw]].
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF, ASAN_CEIL in *. lia.
- exact (proj2 (Gfr a Ha) ltac:(rewrite Hw; exact Fown)).
Qed.

Lemma rx_keep_img : forall ly S Hp W mem md pos a, ARx ly S Hp W mem md -> In (1, pos) (frames S) ->
  in_img SEGS a -> ~ rx_wr ly pos a /\ 0 <= a < 2 ^ 64.
Proof.
intros ly S Hp W mem md pos a HAR Hin Ha.
pose proof (pa_segs_low a Ha) as Hlow.
destruct (FFLX ly S Hp W mem md 1 pos HAR Hin) as (_ & _ & Fimg).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md 1 pos HAR Hin) as (Fb1 & _).
split; [|unfold kLowMemEnd in Hlow; lia].
unfold rx_wr. intros [Hw | [Hw | Hw]].
- exact (frm_img_x _ _ _ LAWS ly S Hp W mem md 1 pos a HAR Hin ltac:(change (fs_frame_bytes 1) with 128; lia) Ha).
- unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
- apply Fimg. rewrite <- Hw. exact Ha.
Qed.

(* a byte off the writes keeps its view and its overlay byte *)
Lemma rx_av : forall (W : world SEGS) mem mem' ly pos,
  (forall x : word, ~ rx_wr ly pos (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ rx_wr ly pos a ->
  aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a /\
  mbyte SEGS (mrestrict (w_H W) mem') a = mbyte SEGS (mrestrict (w_H W) mem) a.
Proof.
intros W mem mem' ly pos HK a Ha Hn.
assert (E : mrestrict (w_H W) mem' (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ apply HK. rewrite unsigned_lit_small by lia. exact Hn. }
split; [exact (aview_eq_of SEGS (w_H W) mem mem' a E) | unfold mbyte; rewrite E; reflexivity].
Qed.

(* the prologue's 13 saves, below the entry sp (rtt_saved's form at regs0) *)
Definition rx_saved (regs0 : bvmap 5 word) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  forall j, (j < 13)%nat ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs0 - 8 * (Z.of_nat j + 1)) 8
    (bv_unsigned (getr regs0 (nth j RTT_SAVED 0%bv))).

Section r. Context {fx : YK11.FPState}.
(* the flag-store runner: YGcallSx.v's aj_flag_store_xR at image A''s listing (as YC1fPx.v instantiates its runners),
   at the walk's relation RZW (reflexive, transitive: YA0nH.wle'_refl / wle'_trans) *)
Definition rx_flag_store := aj_flag_store_xR (SK := SK) SEGS B PST ARx LAWS pa_segs_low ASFX FFLX SFX
  asym pa_wx (clookup pa_tbl) VAL SIGMA B_prog_listing (@pl_tpi _ PL) (@pl_tw _ PL)
  pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text (@pl_lim _ PL) (@pl_len _ PL) (@pl_tpi_eq _ PL) (@pl_tw_eq _ PL)
  RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* ---- the segment's symbolic state from concrete facts (S10TxString.v ts_G_entry's shape) ---- *)
Lemma rx_entry : forall (regs0 : bvmap 5 word) (Wc : world SEGS) memc rg F fl,
  getr rg 25 = w64 (shadow_addr F) -> getr rg 26 = w64 F -> getr rg 18 = w64 F ->
  getr rg 3 = getr regs0 3 -> getr rg 4 = getr regs0 4 -> getr rg 8 = getr regs0 2 ->
  2 ^ 46 <= spZ regs0 <= 2 ^ 47 -> spZ regs0 mod 16 = 0 ->
  4096 <= F -> F + 128 <= spZ regs0 - 104 -> F mod 32 = 0 -> in_app F 128 ->
  0 <= fl -> fl + 1 <= spZ regs0 - 104 -> (fl + 1 <= F \/ F + 128 <= fl) ->
  (fl + 1 <= shadow_addr F \/ shadow_addr F + 16 <= fl) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + 120) 8 fl ->
  rx_saved regs0 Wc memc ->
  (forall a, F <= a < F + 8 -> apresent (w_H Wc) memc a) ->
  (forall a, shadow_addr F <= a < shadow_addr F + 16 -> apresent (w_H Wc) memc a) ->
  apresent (w_H Wc) memc fl ->
  st_ok_pi SEGS VAL (TE regs0 rg [w64 fl]) ss_X
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (RTT_PC_B + RT_X))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs0 rg [w64 fl]) (mrestrict (w_H Wc) memc).
Proof.
intros regs0 Wc memc rg F fl R25 R26 R18 R3 R4 R8 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 VFL HSV PF PSH PFL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := TE regs0 rg [w64 fl]).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Hsh' := Hsh). unfold SHADOW_OFF in Hsh'.
assert (X25 : bv_unsigned (ew E (xr 25)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs0 rg _ 25%bv 25) by reflexivity. rewrite R25. apply unsigned_lit_small. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = F).
{ unfold E, xr. rewrite (te_cur regs0 rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small. lia. }
assert (X18 : bv_unsigned (ew E (xr 18)) = F).
{ unfold E, xr. rewrite (te_cur regs0 rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small. lia. }
assert (E64 : ew E 64 = w64 fl) by exact (te_more_lt regs0 rg [w64 fl] 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = fl) by (rewrite E64; apply unsigned_lit_small; lia).
assert (X2 : bv_unsigned (ew E 2) = spZ regs0) by (unfold E; rewrite (te_entry regs0 rg _ 2%bv 2) by reflexivity; reflexivity).
assert (EN : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs0 r)
  by (intros r n Hn; unfold E; apply te_entry; exact Hn).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs0 rg [w64 fl]) with E.
- unfold sr_X.
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 2%bv 2%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R8].
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 4%bv 4%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R4].
  apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 3%bv 3%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R3].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 25) (shadow_addr F)); [exact X25 | lia | lia |
      intros o Ho; apply (apresent_writable SEGS); apply PSH; lia | constructor].
  + apply (ts_rok E _ (xr 26) F); [exact X26 | lia | lia |
      intros o Ho; apply (apresent_writable SEGS); apply PF; lia | constructor].
  + apply (ts_rok E _ (xr 18) F); [exact X18 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 120 8 (SOff 64 0) fl);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact VFL.
  + apply (ts_rok E _ 64 fl); [exact X64 | lia | lia | intros o Ho; apply (apresent_writable SEGS);
      replace (fl + o) with fl by lia; exact PFL | constructor].
  + apply (ts_rok E _ 2 (spZ regs0)); [exact X2 | lia | lia | intros o Ho; lia |].
    unfold X_saves. repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval vm_compute in (Z.to_nat (- off / 8 - 1)) in
      let r := eval vm_compute in (nth j RTT_SAVED 0%bv) in
      apply (ts_chunk E _ _ off 8 (SOff n 0) (bv_unsigned (getr regs0 r)));
      [ cbn [sv_denot]; rewrite (EN r n) by reflexivity; rewrite Z.add_0_r; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as BR; change (bv_modulus 64) with (2 ^ 64) in BR; cbn; lia
      | cbn; lia
      | pose proof (HSV j ltac:(lia)) as V; change (nth j RTT_SAVED 0%bv) with r in V;
        replace (spZ regs0 - 8 * (Z.of_nat j + 1)) with (spZ regs0 + off) in V by (cbn; lia); exact V ]
    end.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X25, X26, X18, X64, X2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF, ASAN_CEIL in *. repeat split; lia.
- split; [|split; [|exact I]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X25, X26, X18, X64, X2.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
    unfold SHADOW_OFF in *. repeat split; lia.
  + refine (ts_conds_ne E (xr 18) F [0] X18 _). apply Forall_cons; [split; lia | apply Forall_nil].
Qed.

(* ---- THE RUN: +480 to `ret` in one aj_flag_store_x segment, then paj_ret_at; the post as a continuation ---- *)
Lemma rx_run : forall STK FP ly0 S0 Hp0 (W0 : world SEGS) mem0 md0 regs0 lyc Sc Hpc (Wc : world SEGS) memc mdc kj pos
  rg (Q : world SEGS -> config -> Prop),
  AJ STK (spZ regs0) FP ly0 S0 Hp0 W0 mem0 md0 [(1, pos)] lyc Sc Hpc Wc memc mdc kj ->
  YK0s.ret_ok (getr regs0 1) -> 104 <= STK ->
  getr rg 25 = w64 (shadow_addr (frame_addr lyc 1 pos)) -> getr rg 26 = w64 (frame_addr lyc 1 pos) ->
  getr rg 18 = w64 (frame_addr lyc 1 pos) ->
  getr rg 3 = getr regs0 3 -> getr rg 4 = getr regs0 4 -> getr rg 8 = getr regs0 2 ->
  rdword (aview SEGS (w_H Wc) memc) (frame_addr lyc 1 pos + 120) = Some (flag_addr lyc 1 pos) ->
  rx_saved regs0 Wc memc ->
  (forall regs' memc' mdc',
     AJ STK (spZ regs0) FP ly0 S0 Hp0 W0 mem0 md0 [] lyc (stack_free_state 1 pos Sc) Hpc Wc memc' mdc' kj ->
     aregs_preserved regs0 regs' -> getr regs' 10 = getr rg 21 ->
     (forall x : word, ~ rx_wr lyc pos (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
     mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
     (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS memc') ->
     Q Wc (mkCfg (mkst regs' (getr regs0 1) memc' (seg_rom SEGS)) mdc')) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (RTT_PC_B + RT_X))) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros STK FP ly0 S0 Hp0 W0 mem0 md0 regs0 lyc Sc Hpc Wc memc mdc kj pos rg Q HJ Hra H104 R25 R26 R18 R3 R4 R8
  HFL HSV HK.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_frs HJ) as HFRc. pose proof (ajxR_stk HJ) as Hstk.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 1 pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 1 pos HARc Hin) as (F32 & _ & Ffr & Fsh).
change (fs_frame_bytes 1) with 128 in Fb2, Fb3, Ffr, Fsh.
destruct (FFLX lyc Sc Hpc Wc memc mdc 1 pos HARc Hin) as (Fown & Fapp & Fimg).
pose proof (OWNLOW lyc Sc Hpc Wc memc mdc _ HARc Fown) as Flow.
pose proof (FFLP lyc Sc Hpc Wc memc mdc 1 pos HARc Hin) as Fpr.
assert (Hflf : flag_addr lyc 1 pos + 1 <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= flag_addr lyc 1 pos).
{ destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (frame_addr lyc 1 pos)) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (frame_addr lyc 1 pos + 128) (flag_addr lyc 1 pos)) as [Hg|Hg]; [right; lia|].
  exfalso. exact (proj2 (Ffr (flag_addr lyc 1 pos) ltac:(lia)) Fown). }
assert (Hfls : flag_addr lyc 1 pos + 1 <= shadow_addr (frame_addr lyc 1 pos) \/
               shadow_addr (frame_addr lyc 1 pos) + 16 <= flag_addr lyc 1 pos).
{ destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (shadow_addr (frame_addr lyc 1 pos))) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (shadow_addr (frame_addr lyc 1 pos) + 16) (flag_addr lyc 1 pos)) as [Hg|Hg]; [right; lia|].
  exfalso.
  replace (flag_addr lyc 1 pos) with (shadow_addr (frame_addr lyc 1 pos) + (flag_addr lyc 1 pos - shadow_addr (frame_addr lyc 1 pos))) in Fown by lia.
  exact (proj2 (Fsh (flag_addr lyc 1 pos - shadow_addr (frame_addr lyc 1 pos)) ltac:(change (128 / 8) with 16; lia)) Fown). }
destruct (rx_entry regs0 Wc memc rg (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) R25 R26 R18 R3 R4 R8
  ltac:(lia) Hal16 Fb1 ltac:(lia) F32 Fb3 ltac:(lia) ltac:(lia) Hflf Hfls
  (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HFL) HSV
  ltac:(intros a Ha; exact (proj1 (Ffr a ltac:(lia))))
  ltac:(intros a Ha; replace a with (shadow_addr (frame_addr lyc 1 pos) + (a - shadow_addr (frame_addr lyc 1 pos))) by lia;
        exact (proj1 (Fsh (a - shadow_addr (frame_addr lyc 1 pos)) ltac:(change (128 / 8) with 16; lia)))) Fpr)
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs0 rg [w64 (flag_addr lyc 1 pos)])) by apply te_env.
assert (Hsh : SHADOW_OFF <= shadow_addr (frame_addr lyc 1 pos) < SHADOW_OFF + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew (TE regs0 rg [w64 (flag_addr lyc 1 pos)]) (xr 25)) = shadow_addr (frame_addr lyc 1 pos)).
{ unfold xr. rewrite (te_cur regs0 rg _ 25%bv 25) by reflexivity. rewrite R25. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (U26 : bv_unsigned (ew (TE regs0 rg [w64 (flag_addr lyc 1 pos)]) (xr 26)) = frame_addr lyc 1 pos).
{ unfold xr. rewrite (te_cur regs0 rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small. lia. }
assert (U64 : bv_unsigned (ew (TE regs0 rg [w64 (flag_addr lyc 1 pos)]) 64) = flag_addr lyc 1 pos).
{ rewrite (te_more_lt regs0 rg [w64 (flag_addr lyc 1 pos)] 0) by lia. cbn [nth]. apply unsigned_lit_small. lia. }
(* the run's writes: F's shadow, F's first word, the flag byte *)
assert (Hwr : forall a, in_wrange (TE regs0 rg [w64 (flag_addr lyc 1 pos)]) (ss_mem ss_X) a -> rx_wr lyc pos a).
{ intros a (rr & Hr & Ha). unfold rx_wr. cbv [ss_X ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
    rewrite ts_bv_some in Ha.
  - right; left. rewrite U25 in Ha. lia.
  - left. rewrite U26 in Ha. lia.
  - lia.
  - right; right. rewrite U64 in Ha. lia.
  - lia. }
(* the run has no inline check: its shadow span is a point far above every region *)
unfold YA0nH.SRr'.
lazymatch type of HS with st_ok_pi _ _ ?E ?ss _ =>
  let K := eval vm_compute in (run_K A_LIM (SLit 0) [] ss) in
  let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss) in
  lazymatch r with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss = (st', rs))
    by (vm_compute; reflexivity);
  eapply (rx_flag_store Wc FUEL E K (SLit 0) (2 ^ 63, 2 ^ 63) [] ss st' rs _ STK (spZ regs0) FP ly0 S0 Hp0 W0 mem0 md0
    [] lyc Sc Hpc _ _ 1 pos _ ltac:(unfold A_LIM; cbn; lia) HEI ltac:(lia) HS SHOK ltac:(vm_compute; reflexivity) Hrun I
    HJ)
  end end.
- (* no inline check, no obligation *)
  match goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end. apply Forall_nil.
- (* the writes: the own frame's first word and shadow, and the flag *)
  intros a HWa. destruct (Hwr a HWa) as [H1 | [H1 | H1]].
  + left. right; right; right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr.
    cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
  + left. right; right; right. exists 1, pos. split; [left; reflexivity|]. right. unfold in_zr.
    cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. lia.
  + right. exact H1.
- (* the flag is 0 after the run *)
  intros ws msr Hlen HSr.
  pose proof (ts_region_nth _ _ _ 3 _ HSr eq_refl) as HR3.
  lazymatch type of HSr with st_ok_pi _ _ (extK ?E0 ?KK ?ws0) _ _ =>
    assert (X64 : bv_unsigned (ew (extK E0 KK ws0) 64) = flag_addr lyc 1 pos)
      by (rewrite (proj1 (env_agree_extK E0 KK ws0) 64%nat) by (cbv; lia); exact U64) end.
  pose proof (ts_field _ _ 64 (flag_addr lyc 1 pos) _ 0 1 0 1 0 1%N (SLit 0) HR3 X64
    ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0.
  rewrite V0. f_equal; try (rewrite U_SLit; apply bv_eq; vm_compute; reflexivity).
- (* the epilogue's `ret` *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HFr1 HFr2 Hgr.
  cbn [ms_mem mkst] in HFr1, HFr2, Hgr.
  prreg HS' (1%bv : bv 5) Q1.
  assert (X1 : getr (ms_regs ms') 1 = getr regs0 1).
  { rewrite Q1. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) 1 = _ =>
      rewrite (proj1 (env_agree_extK E0 KK ws0) 1%nat) by (cbv; lia) end.
    apply te_entry. reflexivity. }
  prreg HS' (10%bv : bv 5) Q10.
  assert (X10 : getr (ms_regs ms') 10 = getr rg 21).
  { rewrite Q10. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) _ = _ =>
      rewrite (proj1 (env_agree_extK E0 KK ws0) 53%nat) by (cbv; lia) end.
    apply (te_cur regs0 rg _ 21%bv 21). reflexivity. }
  apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (paj_ret_at (PL := PL) (PI := PA) Wc _ _ ms' _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat''.
  rewrite X1. unfold YK0s.ret_ok in Hra. rewrite Hra.
  apply HK.
  + apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW). exact HJ'.
  + eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs0 (map (getr rg) all_regs ++ [w64 (flag_addr lyc 1 pos)]) HS');
      [| vm_compute; reflexivity].
    split.
    * intros n Hn. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) n = _ =>
        rewrite (proj1 (env_agree_extK E0 KK ws0) n) by lia end.
      unfold TE. apply Eimg_low. unfold A_TEXT. lia.
    * lazymatch goal with |- ed (extK ?E0 ?KK ?ws0) = _ => rewrite (proj2 (env_agree_extK E0 KK ws0)) end.
      reflexivity.
  + exact X10.
  + intros x Hx. apply HFr2. intros HWx. exact (Hx (Hwr _ HWx)).
  + exact Hgr.
  + intros HMN0.
    exact (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) (TE regs0 rg [w64 (flag_addr lyc 1 pos)]) (abs_ss VAL ss_X)
      (mkst rg (Z_to_bv 64 (BASE + (RTT_PC_B + RT_X))) memc (seg_rom SEGS)) (ms_mem ms') HMN0 HS HFr1).
Qed.
End r.

Section m. Context {fx : YK11.FPState}.

(* ---- THE STRETCH: RTT_SEG_X at image A' ---- *)
Theorem rtt_seg_x_B : @RTT_SEG_X fx rc ci cp prh_img_B RL B_prog_listing PI_prog_B B ARx SK CTX0.
Proof.
unfold RTT_SEG_X, rtt_seg.
intros D HP fxc ly S Hp W regs mem md k pos HX.
unfold rtt_at_x, rtt_carry, rtt_frame, rtt_cregs, rtt_J, RT_CID, RT_FLAGP in HX.
destruct HX as ((HFX & HJ & HFR & HSV & HCR & HMN & HRO & HRM & HND & HTV & HWD) & r & R21 & HQx).
destruct HFX as [Hfrm Hfk].
destruct HFR as (EFR & Hnew & HFL & HFP).
destruct HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof HP as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HTREE & _ & _ & _ & HCOPY & _).
pose proof HPRE as ((HAR0 & Hra & _ & Hgp & Htp & _) & _).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as HLY.
assert (Hin1 : In (1, pos) (frames S)) by (rewrite EFR; left; reflexivity).
assert (EPC : SIGMA AS_round_trip_text + RT_X = BASE + (RTT_PC_B + RT_X)) by (rewrite <- RTT_PC_val; ring).
rewrite EPC.
eapply (rx_run (fx := fxc) _ _ _ _ _ _ _ _ (ri_regs D)).
- exact HJ.
- exact Hra.
- vm_compute. discriminate.
- exact R25.
- exact R26.
- exact R18.
- rewrite R3, Hgp. reflexivity.
- rewrite R4, Htp. reflexivity.
- rewrite R8. unfold ri_sp, spZ, w64. apply Z_to_bv_bv_unsigned.
- exact HFL.
- exact HSV.
- intros regs' mem' md' HJ' HAP R10' HKP HGR HMN'.
  (* THE POST'S BUDGET: the run's journal is from the depot-moved entry; the wild traces since the entry are within
     the text's 32 (rtt_carry's last conjunct), so the journal from the entry itself is at a budget WS of at most 32
     fresh traces (Rtt102Cut.v rtt_unbase) *)
  destruct (rtt_unbase (PI := prh_img_B) B ARx SK D S (prh_wk F_round_trip_text) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HWD HJ') as (WS & HWS & HJW).
  unfold rtt_post, fpostFbm, fpostFb, YCbqGwild.apost_base_xbFR, fQmn. cbv beta.
  exists fxc, ly, (stack_free_state 1 pos S), Hp, regs', mem', md', k, WS.
  split; [reflexivity|]. split; [exact Hfrm|]. split; [exact Hfk|]. split; [exact HWS|]. split; [exact HJW|].
  split; [exact HAP|].
  split; [|intros H0; exact (HMN' (HMN H0))].
  (* ---- the text's post rtt_Q at the released state ---- *)
  destruct (alx_layout _ _ _ LAWS (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) ly HAR0 HLY)
    as (_ & EFA & _).
  pose proof HTREE as (_ & HDL & _ & HOH). pose proof HOH as (_ & HDF & _).
  assert (KBLK : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + req_size n ->
    aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x /\
    mbyte SEGS (mrestrict (w_H W) mem') x = mbyte SEGS (mrestrict (w_H W) mem) x).
  { intros p n x Hpn Hx. destruct (rx_keep_blk ly S Hp W mem md pos p n x HAR Hin1 Hpn Hx) as [Hn Hr].
    exact (rx_av W mem mem' ly pos HKP x Hr Hn). }
  assert (KIMG : forall x, in_img SEGS x -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x).
  { intros x Hx. destruct (rx_keep_img ly S Hp W mem md pos x HAR Hin1 Hx) as [Hn Hr].
    exact (proj1 (rx_av W mem mem' ly pos HKP x Hr Hn)). }
  assert (KFRM : forall a n x, ck_in_frame (ri_ly D) (ri_S D) a n -> a <= x < a + n ->
    aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x /\
    mbyte SEGS (mrestrict (w_H W) mem') x = mbyte SEGS (mrestrict (w_H W) mem) x).
  { intros a n x (cid & p & Hcp & Ha1 & Ha2) Hx. rewrite <- !EFA in Ha1, Ha2.
    destruct (in_split _ _ Hcp) as (l1 & l2 & El).
    destruct (rx_keep_frm ly S Hp W mem md pos l1 l2 cid p x HAR ltac:(rewrite EFR, El; reflexivity) ltac:(lia))
      as [Hn Hr].
    exact (rx_av W mem mem' ly pos HKP x Hr Hn). }
  destruct HQx as (Lamc & peakc & cntc & ranc & (HLED & HPK) & Er & Ecn & Eran & HPOS & H0 & H1).
  (* the entry's harness blocks are still the cut ledger's *)
  assert (HLin : forall bk, In bk (ri_Lam D) -> In bk Lamc).
  { intros bk Hbk. destruct (Z.eq_dec (ri_copy D) 0) as [Hc|Hc].
    - destruct (H0 Hc) as [HPL _]. exact (Permutation_in _ (Permutation_sym HPL) Hbk).
    - destruct (H1 Hc) as (Db & HPL & _). apply (Permutation_in _ (Permutation_sym HPL)).
      apply in_or_app. right. exact Hbk. }
  (* a byte of a ledger block of the cut *)
  assert (KLED : forall a k0 x, In (a, k0) Lamc -> a - cf_head <= x < a + k0 ->
    aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x /\
    mbyte SEGS (mrestrict (w_H W) mem') x = mbyte SEGS (mrestrict (w_H W) mem) x).
  { intros a k0 x Hak Hx.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED Hak) as (Hk0 & Hab & _).
    pose proof HW as HW'. unfold prh_head_wide in HW'.
    assert (Hn0 : 0 <= k0 + cf_head) by lia.
    destruct (req_size_pos (k0 + cf_head) Hn0) as [_ Hrq].
    apply (KBLK _ _ x Hab). lia. }
  unfold rtt_Q. cbv zeta.
  unfold rtt_room in HRM.
  split; [exact (RL_stack_free S 1 pos HRM)|].
  exists Lamc, peakc, cntc, ranc, 0.
  split.
  { eapply prh_ledger_kept_aview; [exact HLED | | | | apply Permutation_refl].
    - intros a Ha. apply KIMG. exact (pst_img_B a Ha).
    - intros a k0 i Hak Hi.
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED Hak) as (Hk0 & _).
      pose proof HW as HW'. unfold prh_head_wide in HW'.
      assert (Hx : a - cf_head <= a - cf_head + i < a + k0) by lia.
      exact (proj1 (KLED a k0 _ Hak Hx)).
    - intros a k0 _ Hab. rewrite rx_ablocks_sf. exact Hab. }
  split; [exact HPK|].
  split.
  { apply (rx_nodeR_keep SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')); [| exact HGR |].
    - apply (rx_nodeR_lblk SEGS _ _ (prh_lin (ri_Lam D))); [exact HND|].
      intros x k0 Hxk Hl. unfold prh_lin in *. exact (HLin _ Hl).
    - intros x [Hx | (b & Hb & Hx)].
      + exact (proj2 (KFRM _ _ x HDF Hx)).
      + destruct b as [bx bk]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
        pose proof HW as HW'. unfold prh_head_wide in HW'.
        assert (Hx' : bx - cf_head <= x < bx + bk) by lia.
        exact (proj2 (KLED bx bk x (HLin _ (HDL _ Hb)) Hx')). }
  exists r.
  split; [rewrite R10', R21; reflexivity|].
  split; [exact Er|].
  right. split; [exact Er|]. split; [reflexivity|]. split; [exact Ecn|]. split; [exact Eran|].
    split; [destruct HPOS as (hist & HPOS); exists hist;
      exact (PresetRoomPosKeep.room_pos_stack_free _ _ _ _ _ _ _ 1 pos HPOS)|].
    split.
    * intros Hc. destruct (H0 Hc) as [HPL HPB]. split; [exact HPL | rewrite rx_ablocks_sf; exact HPB].
    * intros Hc. destruct (H1 Hc) as (Db & HPL & HDb & HDs & HTB & HFO & HDn & HPB & HNC & HCAP). exists Db.
      destruct HCOPY as [Hc0 | (_ & _ & (HCIF & _) & _)]; [exfalso; exact (Hc Hc0)|].
      (* copy's footprint (its 56 bytes in a caller frame, Db's blocks) keeps its bytes across the run *)
      assert (KFC : forall x, pj_footR (ri_copy D) Db x ->
        mbyte SEGS (mrestrict (w_H W) mem') x = mbyte SEGS (mrestrict (w_H W) mem) x).
      { intros x [Hx | (b & Hb & Hx)].
        - exact (proj2 (KFRM _ _ x HCIF Hx)).
        - destruct b as [bx bk]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
          assert (Hab : In (bx - cf_head, bk + cf_head) (ablocks B ly S)).
          { apply (Permutation_in _ (Permutation_sym HPB)). apply in_or_app. right.
            exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) Db (bx, bk) Hb). }
          pose proof HW as HW'. unfold prh_head_wide in HW'.
          assert (Hn0 : 0 <= bk + cf_head) by lia.
          destruct (req_size_pos (bk + cf_head) Hn0) as [_ Hrq].
          assert (Hx' : bx - cf_head <= x < bx - cf_head + req_size (bk + cf_head)) by lia.
          exact (proj2 (KBLK _ _ x Hab Hx')). }
      split; [exact HPL|]. split; [exact HDb|]. split; [exact HDs|]. split; [exact HTB|].
      split.
      { (* copy's ordered free list at every depth bound: PRH_PjOrder.pj_foR_frame *)
        intros Hhd nn Hnn. destruct (HFO Hhd nn Hnn) as (F & HF & HFm). exists F. split; [|exact HFm].
        apply (PRH_PjOrder.pj_foR_frame SEGS nn (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') (prh_lin Lamc)
          (prh_lin Lamc) (ri_copy D) Db F HF).
        - intros a0 k0 Hak. unfold prh_lin. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left.
          exact Hak.
        - intros x Hx. split; [exact (KFC x Hx) | intros Hw; exact (writable_at_grows SEGS _ _ x HGR Hw)]. }
      split; [exact HDn|].
      split; [rewrite rx_ablocks_sf; exact HPB|].
      split.
      { apply (rx_nodeR_keep SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')); [exact HNC | exact HGR |].
        exact KFC. }
      (* K0-CAP: Rtt102Cut.v rtt_ncapR_frame over copy's tree *)
      exact (rtt_ncapR_frame SEGS (ri_t D) (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') (prh_lin Lamc) (ri_copy D) Db
        HNC HCAP KFC).
Qed.
Print Assumptions rtt_seg_x_B.
End m.
End f.
End w.
(* the elaborated statement: every FPState, PI, PA argument of the top theorem, by name (the text owner's rule) *)
Set Printing Implicit.
Check @rtt_seg_x_B.
Unset Printing Implicit.
Print Assumptions rtt_seg_x_B.
