(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the composition of the image-B (fuzz_reply.asan-ubsan) walk of check_shape_ends, after
   lib/A/W_check_shape_ends.v (a working branch), a NEW walk over lib/B/W_listing.v.  The pieces meet at the interface
   predicates of lib/B/W_cshe_epi.v: the head (lib/B/W_cshe_hd.v) ends in cshe_out_B, cshe_l2_in or cshe_l3_in; loop 2
   (lib/B/W_cshe_l2.v) and loop 3 (lib/B/W_cshe_l3.v) take cshe_l2_in / cshe_l3_in to cshe_out_B; this file takes
   cshe_out_B through the epilogue 0x8592c (cshe_epi_m_B) to whatever the caller's post asks of the run, which is the
   form the kit's cshe_post has. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin W_cshe_epi.
(* the three pieces: the head (BCsheHead), loop 2 (BCsheL2), loop 3 (BCsheL3) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_cshe_hd W_cshe_l2 W_cshe_l3.
(* The sink-instance guard, after every import (MERGE.md (sha256 0694aca87ccd; internal record) item 3) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x W_frame_x.
(* the laws at ARi0 from cgif's laws (Section cAR's proof) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YLX0.
(* route R: SRrG and the R contract texts (check_shape_ends; list_drop) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6 W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).

Section c.
Variable B : asyms.
(* ARx conversion (route (b); A's lib/A/W_check_shape_ends.v on a working branch 4f281bf9308): the walk is
   stated over a generic allocator relation ARx with its laws (YCbqG.AR_laws_x), the placement PST and the room record
   RP; HP0 (every ghost list is []), IMGC (the image's cover), BLKN (a block's size is >= 0), FRMF (the fake frames'
   alignment, W_frame_x.v) and HPST (the image is off PST) are the facts the generic relation does not carry by itself.
   pb_check_shape_ends_x proves cshe_spec_x (lib/B/W_contract_x.v); Section cAR re-derives pb_check_shape_ends,
   statement unchanged, at ARx := W_journal_x.ARi0, PST := [], RP := RP_AR through W_contract_x.cshe_spec_x_AR0. *)
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* W_frame_x.v Section q's FRMF (the fake frames' alignment: the generic counterpart of YG0s.v frame_facts; at ARi0:
   W_frame_x.FRMF_AR) *)
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
(* the image is off the placement PST: the generic journal's image clause keeps a byte only outside PST *)
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis HG : gx_ok SEGS B G.
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
(* ---- the walk at the empty ghost list (HP0: every ARx state's ghost list is []): AR0 / AJ0 / AJi0 / AFP0 are cgif's
   AR / journal / inner journal / afn_pre at Hp = [], and each kit lemma the AR walk cites is its _x twin at [] ---- *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x SEGS B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFP0 STK ly S W regs mem md ch := (afn_pre_x SEGS B ARx STK ly S [] W regs mem md ch).

(* the source's representation reads memory only through the ASan view (W_rep.v arm), so two memories with the same
   view carry the same source *)
Lemma asrc_at_meq_B : forall ly S (W : world SEGS) m m' HA h,
(forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
asrc_at B ly S W m HA h -> asrc_at B ly S W m' HA h.
Proof.
intros ly S W m m' HA h Hq Hs.
assert (E : arm W m' = arm W m) by (apply functional_extensionality; exact Hq).
unfold asrc_at, alist_at, awr in *. rewrite E. exact Hs.
Qed.

(* cshe_out_B through the epilogue: the run 0x8592c -> ret writes nothing (cshe_epi_m_B), so every fact the pieces
   established at the epilogue's entry holds at the return, with the callee-saved registers restored. *)
Lemma cshe_out_epi_B : forall regs0 ly S W mem md XO AT HA A0 gone h P ob (kr : nat) (Q : world SEGS -> config -> Prop),
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK_B <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
(forall W' ly' S' regs' mem' md' kk (H' : hlist) (ds : list (Z * list byte)) (c : Z),
  AJ0 G XO [(AT, AT + 8)] CSHE_STK_B (spZ regs0) (blk_FP (list_blks (hs_held h)))
    ly S W mem md [] ly' S' W' mem' md' kk ->
  aregs_preserved regs0 regs' ->
  asrc_at B ly' S' W' mem' HA (CheckRep.set_held h H') ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  NoDup (CheckRep.texts H') ->
  ((gone <> 0 /\
    hl_recs H' = filter (fun r => negb (CheckRep.prefixb P (snd r))) (hl_recs (hs_held h)) /\
    ds = filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h)) /\ c = 0) \/
   (gone = 0 /\
    CheckRep.ends_run P (hl_recs (hs_held h)) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs (hs_held h))) =
    Some (hl_recs H', ds, c))) ->
  0 <= c ->
  val_mem SEGS (mrestrict (w_H W') mem') AT 8 (A0 + c) ->
  val_mem SEGS (mrestrict (w_H W') mem') (VAL A_g_gone) 1 gone ->
  (forall rest, Permutation (ablocks B ly S) (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) ds ++ rest) ->
    Permutation (ablocks B ly' S') rest) ->
  frames S' = frames S ->
  mo_le MT S S' (hl_n (hs_held h) * mo_free MT) ->
  (forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
  rp_RM RP S' kr ->
  Q W' (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
forall W' c', cshe_out_B B PST ARx G MT RP regs0 ly S W mem md XO AT HA A0 gone h P ob kr W' c' -> SRr SEGS W' c' Q.
Proof.
intros regs0 ly S W mem md XO AT HA A0 gone h P ob kr Q Hra Hal Hceil H47 HQ W' c'
  (ly' & S' & regs' & mem' & md' & kk & H' & ds & c & -> & HJ & R2 & R3 & R4 & R27 & HSV & HSRC & HV & HC & HND &
   HDIS & Hc0 & MAT & MG & HPERM & HFR & HMO & HERR & HRMo).
apply (cshe_epi_m_B B PST ARx G LAWS HG W ly S mem md XO [(AT, AT + 8)] (blk_FP (list_blks (hs_held h))) ly' S' W' regs0 regs'
  mem' md' kk Q HJ Hra Hal Hceil H47 R2 R3 R4 R27 HSV).
intros regs'' mem'' md'' HP HMEQ HJ''.
assert (EM : mrestrict (w_H W') mem'' = mrestrict (w_H W') mem') by (apply functional_extensionality; exact HMEQ).
apply (HQ W' ly' S' regs'' mem'' md'' kk H' ds c HJ'' HP); try assumption.
- exact (asrc_at_meq_B ly' S' W' mem' mem'' HA (CheckRep.set_held h H') HMEQ HSRC).
- rewrite EM. exact MAT.
- rewrite EM. exact MG.
- intros jj Hjj. rewrite <- (HERR jj Hjj). apply (aview_eq_of SEGS). apply HMEQ.
Qed.


(* ------------------------------------------------------------------ the composition *)
(* The Section hypotheses the pieces take, by the names of lib/B/W_cshe_epi.v's list, at their B _x specs. *)
Hypothesis ML : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
(* list_drop's contract at any globals G' with the usual conditions: at the caller's G its journal keeps no byte of G,
   and cshe_spec puts HA+64..HA+96 in G; this is B's pb_list_drop's Section form (W_cshe_epi.v's list) *)
Hypothesis LDROP : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec_x B PST ARx MT RP G' (BASE + AF_fr_list_drop).
Hypothesis HP : hp_spec_x B PST ARx (BASE + AF_fr_has_prefix).
Hypothesis HGR : gx_ok SEGS B cshe_ro_B.
Hypothesis HGRR : gx_rt B cshe_ro_B.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp_x ARx (VAL A_lit_end5) 4.
Hypothesis HGS : forall a, VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).

(* a premise of a piece: one of cshe_spec_x's premises, or a Section hypothesis *)
Ltac csheB_close :=
  first [ assumption
        | exact HEND5S ].

Theorem pb_check_shape_ends_x : cshe_spec_x B PST ARx MT RP G A_csheBP.
Proof.
unfold cshe_spec_x. intros W ly S Hp regs mem md ch XO AT HA j PF h P A0 gone O OUT ob. cbv zeta. intros HPRE0.
(* the entry's ghost list is empty (HP0 on the pre's ARx): the pieces run at [] *)
hp0a (proj1 HPRE0).
intros until kr. intros HRM0 HCN0.
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal160 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
assert (HCEIL : alloc_ceiling + CSHE_STK_B <= spZ regs)
  by (unfold CSHE_STK, CSHE_FRAME, CSHE_STK_B, CSHE_FRAME_B in *; lia).
assert (HSP47 : spZ regs <= 2 ^ 47) by lia.
(* the epilogue's bridge, at this entry, into the kit's post *)
lazymatch goal with |- SRr _ _ _ ?Q =>
  assert (EPI : forall W' c', cshe_out_B B PST ARx G MT RP regs ly S W mem md XO AT HA A0 gone h P ob kr W' c' ->
    SRr SEGS W' c' Q) end.
{ apply (cshe_out_epi_B regs ly S W mem md XO AT HA A0 gone h P ob kr); [exact Hra0 | exact Hal160 | exact HCEIL | exact HSP47 |].
  intros W' ly' S' regs' mem' md' kk H' ds c HJ HPR HSRC HV HC HND HDIS Hc0 MAT MG HPERM HFR HMO HERR HRMo.
  unfold cshe_post_x. exists ly', S', [], regs', mem', md', kk, H', ds, c.
  (* cshe_post_x: errno's view right after aregs_preserved; the room past the call last *)
  split; [reflexivity|]. split; [exact HJ|]. split; [exact HPR|]. split; [exact HERR|]. split; [exact HSRC|].
  split; [exact HV|]. split; [exact HC|]. split; [exact HND|]. split; [exact HDIS|]. split; [exact Hc0|].
  split; [exact MAT|]. split; [exact MG|]. split; [exact HPERM|]. split; [exact HFR|]. split; [exact HMO | exact HRMo]. }
eapply SRr_bind.
{ eapply cshe_hd_B with (B := B) (PST := PST) (ARx := ARx) (MT := MT) (RP := RP) (G := G) (hl := hl) (W := W) (ly := ly) (S := S)
    (regs := regs) (mem := mem) (md := md) (ch := ch) (XO := XO) (AT := AT) (HA := HA) (j := j) (PF := PF) (h := h)
    (P := P) (A0 := A0) (gone := gone) (O := O) (OUT := OUT) (ob := ob) (kr := kr); csheB_close. }
cbv beta. intros W1 c1 _ [HO | [HL2 | HL3]].
- exact (EPI W1 c1 HO).
- eapply SRr_bind.
  { eapply cshe_l2_B with (B := B) (PST := PST) (ARx := ARx) (MT := MT) (RP := RP) (G := G) (hl := hl) (W := W) (ly := ly) (S := S)
      (regs := regs) (mem := mem) (md := md) (ch := ch) (XO := XO) (AT := AT) (HA := HA) (j := j) (PF := PF) (h := h)
      (P := P) (A0 := A0) (gone := gone) (O := O) (OUT := OUT) (ob := ob) (kr := kr); first [exact HL2 | csheB_close]. }
  cbv beta. intros W2 c2 _ HO2. exact (EPI W2 c2 HO2).
- eapply SRr_bind.
  { eapply cshe_l3_B with (B := B) (PST := PST) (ARx := ARx) (MT := MT) (RP := RP) (G := G) (hl := hl) (W := W) (ly := ly) (S := S)
      (regs := regs) (mem := mem) (md := md) (ch := ch) (XO := XO) (AT := AT) (HA := HA) (j := j) (PF := PF) (h := h)
      (P := P) (A0 := A0) (gone := gone) (O := O) (OUT := OUT) (ob := ob) (kr := kr); first [exact HL3 | csheB_close]. }
  cbv beta. intros W2 c2 _ HO2. exact (EPI W2 c2 HO2).
Qed.
(* the closure, printed into every build log *)
Print Assumptions pb_check_shape_ends_x.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): pb_check_shape_ends_x at a world relation R, cshe_spec_xR (W_contract_xR_g6.v).
   list_drop is the one callee at its R contract (LDROP_R : ldrop_spec_xR, W_contract_xR_g3.v; it calls free); has_prefix,
   next_line, bcmp and list_find stay at their strict contracts.  The head (W_cshe_hd.v cshe_hd_B) calls only strict
   leaves, so its strict fact lifts by SRr_SRrG (WLE_R) and its interface facts by W_cshe_epi.v cshe_*_xR_of; the loops
   are their R twins (W_cshe_l2.v cshe_l2_B_xR, W_cshe_l3.v cshe_l3_B_xR), composed by SRrG_bind (R_trans); the epilogue
   is W_cshe_epi.v cshe_epi_m_B_xR.  The strict pb_check_shape_ends_x above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis LDROP_R : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec_xR B PST ARx R MT RP G' (BASE + AF_fr_list_drop).
Local Notation AJ0R G0 XOq OUTq STKq spq FPq lyq Sq Wq memq mdq ownq lyq' Sq' Wq' memq' mdq' kq :=
  (ajournal_gx_xR SEGS B PST ARx R G0 XOq OUTq STKq spq FPq lyq Sq [] Wq memq mdq ownq lyq' Sq' [] Wq' memq' mdq' kq).
(* cshe_out_epi_B at R *)
Lemma cshe_out_epi_B_xR : forall regs0 ly S W mem md XO AT HA A0 gone h P ob (kr : nat) (Q : world SEGS -> config -> Prop),
YK0s.ret_ok (getr regs0 1) ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + CSHE_STK_B <= spZ regs0 -> spZ regs0 <= 2 ^ 47 ->
(forall W' ly' S' regs' mem' md' kk (H' : hlist) (ds : list (Z * list byte)) (c : Z),
  AJ0R G XO [(AT, AT + 8)] CSHE_STK_B (spZ regs0) (blk_FP (list_blks (hs_held h)))
    ly S W mem md [] ly' S' W' mem' md' kk ->
  aregs_preserved regs0 regs' ->
  asrc_at B ly' S' W' mem' HA (CheckRep.set_held h H') ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  NoDup (CheckRep.texts H') ->
  ((gone <> 0 /\
    hl_recs H' = filter (fun r => negb (CheckRep.prefixb P (snd r))) (hl_recs (hs_held h)) /\
    ds = filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h)) /\ c = 0) \/
   (gone = 0 /\
    CheckRep.ends_run P (hl_recs (hs_held h)) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs (hs_held h))) =
    Some (hl_recs H', ds, c))) ->
  0 <= c ->
  val_mem SEGS (mrestrict (w_H W') mem') AT 8 (A0 + c) ->
  val_mem SEGS (mrestrict (w_H W') mem') (VAL A_g_gone) 1 gone ->
  (forall rest, Permutation (ablocks B ly S) (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) ds ++ rest) ->
    Permutation (ablocks B ly' S') rest) ->
  frames S' = frames S ->
  mo_le MT S S' (hl_n (hs_held h) * mo_free MT) ->
  (forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
  rp_RM RP S' kr ->
  Q W' (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md')) ->
forall W' c', cshe_out_B_xR B PST ARx G R MT RP regs0 ly S W mem md XO AT HA A0 gone h P ob kr W' c' -> SRrG SEGS R W' c' Q.
Proof.
intros regs0 ly S W mem md XO AT HA A0 gone h P ob kr Q Hra Hal Hceil H47 HQ W' c'
  (ly' & S' & regs' & mem' & md' & kk & H' & ds & c & -> & HJ & R2 & R3 & R4 & R27 & HSV & HSRC & HV & HC & HND &
   HDIS & Hc0 & MAT & MG & HPERM & HFR & HMO & HERR & HRMo).
apply (cshe_epi_m_B_xR B PST ARx G LAWS HG R WLE_R W ly S mem md XO [(AT, AT + 8)] (blk_FP (list_blks (hs_held h))) ly' S' W' regs0 regs'
  mem' md' kk Q HJ Hra Hal Hceil H47 R2 R3 R4 R27 HSV).
intros regs'' mem'' md'' HPRS HMEQ HJ''.
assert (EM : mrestrict (w_H W') mem'' = mrestrict (w_H W') mem') by (apply functional_extensionality; exact HMEQ).
apply (HQ W' ly' S' regs'' mem'' md'' kk H' ds c HJ'' HPRS); try assumption.
- exact (asrc_at_meq_B ly' S' W' mem' mem'' HA (CheckRep.set_held h H') HMEQ HSRC).
- rewrite EM. exact MAT.
- rewrite EM. exact MG.
- intros jj Hjj. rewrite <- (HERR jj Hjj). apply (aview_eq_of SEGS). apply HMEQ.
Qed.
Theorem pb_check_shape_ends_xR : cshe_spec_xR B PST ARx R MT RP G A_csheBP.
Proof.
unfold cshe_spec_xR. intros W ly S Hp regs mem md ch XO AT HA j PF h P A0 gone O OUT ob. cbv zeta. intros HPRE0.
(* the entry's ghost list is empty (HP0 on the pre's ARx): the pieces run at [] *)
hp0a (proj1 HPRE0).
intros until kr. intros HRM0 HCN0.
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal160 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
assert (HCEIL : alloc_ceiling + CSHE_STK_B <= spZ regs)
  by (unfold CSHE_STK, CSHE_FRAME, CSHE_STK_B, CSHE_FRAME_B in *; lia).
assert (HSP47 : spZ regs <= 2 ^ 47) by lia.
(* the epilogue's bridge, at this entry, into the kit's post *)
lazymatch goal with |- SRrG _ _ _ _ ?Q =>
  assert (EPI : forall W' c', cshe_out_B_xR B PST ARx G R MT RP regs ly S W mem md XO AT HA A0 gone h P ob kr W' c' ->
    SRrG SEGS R W' c' Q) end.
{ apply (cshe_out_epi_B_xR regs ly S W mem md XO AT HA A0 gone h P ob kr); [exact Hra0 | exact Hal160 | exact HCEIL | exact HSP47 |].
  intros W' ly' S' regs' mem' md' kk H' ds c HJ HPR HSRC HV HC HND HDIS Hc0 MAT MG HPERM HFR HMO HERR HRMo.
  unfold cshe_post_xR. exists ly', S', [], regs', mem', md', kk, H', ds, c.
  (* cshe_post_xR: errno's view right after aregs_preserved; the room past the call last *)
  split; [reflexivity|]. split; [exact HJ|]. split; [exact HPR|]. split; [exact HERR|]. split; [exact HSRC|].
  split; [exact HV|]. split; [exact HC|]. split; [exact HND|]. split; [exact HDIS|]. split; [exact Hc0|].
  split; [exact MAT|]. split; [exact MG|]. split; [exact HPERM|]. split; [exact HFR|]. split; [exact HMO | exact HRMo]. }
eapply (SRrG_bind SEGS R R_trans).
{ (* the head calls only strict leaves (has_prefix): its strict SRr fact lifts to R *)
  apply (SRr_SRrG SEGS R WLE_R).
  eapply cshe_hd_B with (B := B) (PST := PST) (ARx := ARx) (MT := MT) (RP := RP) (G := G) (hl := hl) (W := W) (ly := ly) (S := S)
    (regs := regs) (mem := mem) (md := md) (ch := ch) (XO := XO) (AT := AT) (HA := HA) (j := j) (PF := PF) (h := h)
    (P := P) (A0 := A0) (gone := gone) (O := O) (OUT := OUT) (ob := ob) (kr := kr); csheB_close. }
cbv beta. intros W1 c1 _ [HO | [HL2 | HL3]].
- (* the head's strict interface facts are ones at R (W_cshe_epi.v cshe_*_xR_of) *)
  apply EPI. eapply cshe_out_B_xR_of; first [exact WLE_R | exact HO].
- assert (HL2R : cshe_l2_in_xR B PST ARx G R regs ly S W mem md XO AT HA PF gone h W1 c1)
    by (eapply cshe_l2_in_xR_of; first [exact WLE_R | exact HL2]).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply cshe_l2_B_xR with (B := B) (PST := PST) (ARx := ARx) (MT := MT) (RP := RP) (G := G) (hl := hl) (R := R) (W := W)
      (ly := ly) (S := S) (regs := regs) (mem := mem) (md := md) (ch := ch) (XO := XO) (AT := AT) (HA := HA) (j := j) (PF := PF)
      (h := h) (P := P) (A0 := A0) (gone := gone) (O := O) (OUT := OUT) (ob := ob) (kr := kr); first [exact HL2R | csheB_close]. }
  cbv beta. intros W2 c2 _ HO2. exact (EPI W2 c2 HO2).
- assert (HL3R : cshe_l3_in_xR B PST ARx G R regs ly S W mem md XO AT HA PF gone h P W1 c1)
    by (eapply cshe_l3_in_xR_of; first [exact WLE_R | exact HL3]).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply cshe_l3_B_xR with (B := B) (PST := PST) (ARx := ARx) (MT := MT) (RP := RP) (G := G) (hl := hl) (R := R) (W := W)
      (ly := ly) (S := S) (regs := regs) (mem := mem) (md := md) (ch := ch) (XO := XO) (AT := AT) (HA := HA) (j := j) (PF := PF)
      (h := h) (P := P) (A0 := A0) (gone := gone) (O := O) (OUT := OUT) (ob := ob) (kr := kr); first [exact HL3R | csheB_close]. }
  cbv beta. intros W2 c2 _ HO2. exact (EPI W2 c2 HO2).
Qed.
Print Assumptions pb_check_shape_ends_xR.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b); A's Section cAR): pb_check_shape_ends's statement is the AR walk's,
   byte-identical, now a corollary of pb_check_shape_ends_x at ARx := ARi0 (cgif's AR with the head set empty),
   PST := [], RP := RP_AR.  Its Section keeps LAWS : AR_laws (a Theorem Labs lane's ruling 03:30Z: the plain names keep their
   B-old statements, Section hypotheses included); the proof derives LX0 (the laws at ARi0) from LAWS by
   lib/B/YLX0.v lx_AR_laws_x_ARi0_of, as lib/B/W_list_drop.v does.  The bridges are the kit's: W_contract_x
   cshe_spec_x_AR0 for the conclusion; nl_spec_x_of_AR0, lfind_spec_x_of_AR0, ldrop_spec_x_of_AR0, hp_spec_x_of_AR0
   (W_contract_x) and abcmp_realizes_x_of_AR0 (W_sites_x) for the callees; HP0 at ARi0 is W_journal_x.ARi0_hp0;
   IMGC / BLKN are W_kit_x.AR_imgc / AR_blkn, FRMF is W_frame_x.FRMF_AR; HPST holds at PST = []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis ML : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Hypothesis NL : nl_spec B (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec B G (BASE + AF_fr_list_find).
Hypothesis LDROP : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec B MT G' (BASE + AF_fr_list_drop).
Hypothesis HP : hp_spec B (BASE + AF_fr_has_prefix).
Hypothesis HGR : gx_ok SEGS B cshe_ro_B.
Hypothesis HGRR : gx_rt B cshe_ro_B.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp B (VAL A_lit_end5) 4.
Hypothesis HGS : forall a, VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).

Theorem pb_check_shape_ends : cshe_spec B MT G A_csheBP.
Proof.
pose proof (YLX0.lx_AR_laws_x_ARi0_of SEGS B LAWS) as LX0.
apply cshe_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
assert (FRMF : forall ly S Hp W mem md cid pos, ARi0 SEGS B ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0)
  by (intros ly S Hp W mem md cid pos H Hin; destruct H as [HAR _]; exact (FRMF_AR SEGS B ly S Hp W mem md cid pos HAR Hin)).
assert (HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
assert (ABCx : abcmp_realizes_x SEGS B (ARi0 SEGS B) (SIGMA WS_bcmp)) by (apply abcmp_realizes_x_of_AR0; exact ABCMP).
assert (NLx : nl_spec_x B [] (ARi0 SEGS B) (BASE + AF_fr_next_line)) by (apply nl_spec_x_of_AR0; exact NL).
assert (LFx : lfind_spec_x B [] (ARi0 SEGS B) G (BASE + AF_fr_list_find)) by (apply lfind_spec_x_of_AR0; exact LFIND).
assert (LDx : forall G', gx_ok SEGS B G' -> gx_rt B G' ->
  (forall a, in_rom SEGS a -> (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G' a) ->
  ldrop_spec_x B [] (ARi0 SEGS B) MT RP_AR G' (BASE + AF_fr_list_drop))
  by (intros G0 H1 H2 H3; apply ldrop_spec_x_of_AR0; exact (LDROP G0 H1 H2 H3)).
assert (HPx : hp_spec_x B [] (ARi0 SEGS B) (BASE + AF_fr_has_prefix)) by (apply hp_spec_x_of_AR0; exact HP).
assert (HE5x : ashp_x (ARi0 SEGS B) (VAL A_lit_end5) 4)
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (HEND5S ly S W mem md HAR)).
exact (pb_check_shape_ends_x B [] (ARi0 SEGS B) MT RP_AR G LX0 HP0 IMGC BLKN FRMF HPST HG ML TL ABCx NLx LFx LDx HPx HGR
  HGRR ROMNS HEND5R HE5x HGS).
Qed.
(* the closure, printed into every build log *)
Print Assumptions pb_check_shape_ends.
End cAR.
End b.
End a.
