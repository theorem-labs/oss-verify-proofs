(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 361 of its 425 lines of code are new or changed and 340 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputDec.v, with its module paths and module names changed; 784 of its 888 lines of code are new or changed and 321 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: mark_quietly's OPENING arm (0x883d4, listing
   (internal path) (internal record, sha256 83bb83545bf3), g_sink = 0) at its tail jump
   into reac_served_mark (+0x70). The jump state is related to the entry by mark_quietlyDefs.v `mqo_rel` (AR at the
   jump, the entry's kept clause with the write set mqo_E, every block of the entry a block of the jump state),
   and the FILE block res is a block of the jump state and not of the entry. Then:
   - mqo_rsm_pre: reac_served_mark's Pre at the jump, its FILE block res;
   - mqo_rsm_rd: its read set at the jump is `akb` at the jump state and its window;
   - mqo_q: mark_quietly's opening-arm PostA from reac_served_mark's Post.
   A byte the Pre reads through a pointer (the name, a live table string, the marks block) is an `akb` byte of the
   entry outside mqo_E (the Pre's separations from the four globals and errno), so the entry's kept clause keeps
   its value, and its shadow moves by LinkWalkShadow.v shadow_transport_akb. The image's shadow is the same at
   every AR state (LinkWalkShadow.v img_sh_eq), its bytes are always visible (AB13.v tfib_rom_all) and its rw bytes
   always writable (AB13.v tfib_rw_window). The fresh block is apart from every `akb` byte of the entry together
   with the 16 bytes before it (`mqb_fresh_ext`: they lie in the chunk of res at the jump, YG0s.v chunk_facts, and
   that chunk is disjoint from the stack row, the image, every other chunk and the side stack), which also covers
   the name's 8-byte slack past its NUL. The 8 bytes past the marks block are visible at every AR state (the
   chunk's junk; the same proof as srm_blk_tail_vis16 of
   lib/A/Prog/reac_served_markKitAt.v).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkMfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk LinkWalkNlk LinkWalkErrno LinkWalkSide LinkWalkZsh LinkWalkShadow LinkWalkMkTail
model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c mark_quietlyDefs mark_quietlyRsm
PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m AB13.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. Generic facts (no section hypothesis)
   ========================================================================== *)

(* a closed comparison of constants *)
Ltac mqb_cmp := repeat match goal with |- _ /\ _ => split end; apply Z.leb_le; vm_compute; reflexivity.

(* two members of a list whose keys have no duplicate are equal or have different keys *)
Lemma mqb_nodup : forall (X Y : Type) (f : X -> Y) (l : list X) x y,
  List.NoDup (map f l) -> In x l -> In y l -> x = y \/ f x <> f y.
Proof.
  intros X Y f l. induction l as [|h t IH]; intros x y ND Hx Hy; [destruct Hx|].
  cbn [map] in ND. apply NoDup_cons_iff in ND as [Hni ND'].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - left. reflexivity.
  - right. intros E. apply Hni. rewrite E. apply in_map. exact Hy.
  - right. intros E. apply Hni. rewrite <- E. apply in_map. exact Hx.
  - exact (IH x y ND' Hx Hy).
Qed.

(* a range whose every byte misses the fresh block and the 16 bytes before it lies apart from the block, also
   with up to 16 bytes of slack past its end *)
Lemma mqb_apart_ext : forall r p n m, 0 < n -> m <= n + 16 ->
  (forall a, p <= a < p + n -> ~ (r - 16 <= a < r + AMF_BLOCK)) -> apart r AMF_BLOCK p m.
Proof.
  intros r p n m Hn Hm H. unfold apart. unfold AMF_BLOCK in *.
  pose proof (H p ltac:(lia)) as H1.
  destruct (Z_lt_le_dec p (r - 16)) as [Hl|Hl].
  - destruct (Z_lt_le_dec (r - 16) (p + n)) as [Hl2|Hl2].
    + exfalso. apply (H (r - 16)); lia.
    + right. lia.
  - left. lia.
Qed.

(* the image segment that holds .rodata, g_nl's segment, and g_nl apart from every owned static range *)
Lemma mqb_seg0 : existsb (relro_in_seg 0x10000 (0x10000 + 0x21000)) AB1v.tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mqb_seg_nl : existsb (relro_in_seg LA_G_NL (LA_G_NL + NK_SIZE)) AB1v.tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mqb_own_nl :
  forallb (fun r => (LA_G_NL + NK_SIZE <=? fst r) || (fst r + snd r <=? LA_G_NL)) AF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* the bytes past a heap block, to the next multiple of 16 of its size, are visible at every AR state (the rest of
   its chunk is AR's junk); the proof of reac_served_markKitAt.v srm_blk_tail_vis16 *)
Section tv. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma mqb_chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
  In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
  intros ly S k Hk. unfold ajunk. right. right.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma mqb_chunk_room_mod16 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
  (ck_extent k - ck_rz k) mod 16 = 0.
Proof.
  intros ly S rd k M Hk.
  pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & RZ & _ & _ & G).
  assert (EX : ck_extent k mod 16 = 0).
  { destruct (ck_beg k) as [|off|r o|c q]; try solve [destruct G].
    - cbv zeta in G. destruct G as (Gc & _ & _ & Gext & _).
      pose proof (class_ok (prim_class off) ltac:(lia)) as (_ & K2 & _). rewrite Gext.
      apply Z.mod_divide in K2 as [q K2]; [|lia]. rewrite K2. replace (q * 32) with ((q * 2) * 16) by lia.
      apply Z.mod_mul. lia.
    - destruct G as (_ & Hp & _ & Gext & _). pose proof (secondary_geometry (ck_req k)) as SG.
      pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & Hn & _).
      destruct (SG ltac:(lia) Hp) as (_ & _ & _ & _ & S5 & _). rewrite Gext.
      apply Z.mod_divide in S5 as [q S5]; [|unfold kPage; lia]. rewrite S5. unfold kPage.
      replace (q * 4096 - 4096) with ((q * 256 - 256) * 16) by lia. apply Z.mod_mul. lia. }
  apply Z.mod_divide in EX as [a EX]; [|lia]. apply Z.mod_divide in RZ as [b RZ]; [|lia].
  rewrite EX, RZ. replace (a * 16 - b * 16) with ((a - b) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma mqb_blk_tail_vis16 : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + n <= a < p + round_up n 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (mqb_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (N1 : 1 <= n).
  { destruct (Z.eq_dec n 0) as [->|]; [|lia]. unfold round_up in Ha. cbn in Ha. lia. }
  assert (CN : ck_n k = n) by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
  assert (RU : round_up n 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [lia | | exact R16]. unfold ck_n in CN. lia. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (mqb_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + n) + (a - (ck_base B ly k + (ck_rz k + n)))) by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
(* the same past the user bytes of any block: [p + req_size n, p + round_up (req_size n) 16) *)
Lemma mqb_blk_tail_vis_r : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= a < p + round_up (req_size n) 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (mqb_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (CN : ck_n k = req_size n)
    by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); destruct (Z.eqb_spec n 0); lia).
  assert (RU : round_up (req_size n) 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [unfold req_size; destruct (Z.eqb_spec n 0); lia | | exact R16].
    rewrite <- CN. unfold ck_n in *. lia. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (mqb_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + req_size n) + (a - (ck_base B ly k + (ck_rz k + req_size n)))) by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
End tv.

(* ==========================================================================
   1. The image, at any memory and any AR state
   ========================================================================== *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.

(* every image byte is visible at any memory (the segments have a byte for it) *)
Lemma mqb_vis_img : forall (H : word -> bool) m a, 0x10000 <= a < pcap_img_end -> aview SEGS H m a <> None.
Proof.
  intros H m a Ha. rewrite HSEGS. unfold aview, mbyte.
  destruct (mrestrict H m (Z_to_bv 64 a)); cbn; [discriminate|].
  pose proof (AB13.tfib_rom_all a Ha) as X.
  destruct (seg_rom AB1v.tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | exfalso; exact (X eq_refl)].
Qed.

(* every rw byte of the image is writable at any memory *)
Lemma mqb_wr_img : forall m a, 0xa1000 <= a < pcap_img_end -> writable_at SEGS m a.
Proof.
  intros m a Ha. rewrite HSEGS. unfold writable_at. apply AB13.tfib_rw_window.
  rewrite unsigned_lit_small by (unfold pcap_img_end, YImgTop.IMG_TOP in *; lia). exact Ha.
Qed.

(* a present byte is writable *)
Lemma mqb_wr_pres : forall (H : word -> bool) m a, apresent H m a -> writable_at SEGS (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* the image's shadow: the same at every AR state, and visible *)
Lemma mqb_img_sh : forall ly1 S1 rd1 ly2 S2 rd2 p n,
  ARm B ly1 S1 rd1 -> ARm B ly2 S2 rd2 -> 0x10000 <= p -> p + n <= pcap_img_end -> 0 < n ->
  range_addressable rd1 SHADOW_OFF p n ->
  range_addressable rd2 SHADOW_OFF p n /\ shadow_hull_vis rd2 p n.
Proof.
  intros ly1 S1 rd1 ly2 S2 rd2 p n M1 M2 H0 H1 Hn HR. unfold pcap_img_end, YImgTop.IMG_TOP in H1.
  split.
  - apply (ra_shadow_eq rd1 rd2 p n HR). intros x Hx.
    refine (proj1 (img_sh_eq B TB ly1 S1 rd1 ly2 S2 rd2 _ M1 M2 _)). unfold shadow_addr, SHADOW_OFF. lia.
  - intros s Hs. refine (proj2 (img_sh_eq B TB ly2 S2 rd2 ly2 S2 rd2 s M2 M2 _)).
    unfold shadow_addr, SHADOW_OFF in Hs |- *. lia.
Qed.

(* ==========================================================================
   2. The entry and the jump state
   ========================================================================== *)

Definition mqb_ctx (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model)
    (sp : Z) (lyj : alayout) (Sj : astate) (Wj : world SEGS) (memj : word -> option byte) (mdj : Model) : Prop :=
  AR SEGS B lyc Sc W memc mdc /\ alloc_ceiling <= sp - MARK_QUIETLY_AK /\
  mqo_rel SEGS B sp lyc Sc W memc lyj Sj Wj memj mdj.

Lemma mqb_E_img : forall a, mqo_E B a -> 0xa1000 <= a < LA_OFL_HEAD + 8.
Proof.
  intros a H. unfold mqo_E in H. rewrite (AF0m.ts_errno B TB) in H.
  unfold LA_G_SINK, LA_G_SAID, SAID_SIZE, LA_G_SAY, LA_OFL_HEAD, AF0m.TFIB_ERRNO in *. lia.
Qed.

Lemma mqb_E_low : forall a, a < LA_G_SINK -> ~ mqo_E B a.
Proof.
  intros a Ha H. unfold mqo_E in H. rewrite (AF0m.ts_errno B TB) in H.
  unfold LA_G_SINK, LA_G_SAID, SAID_SIZE, LA_G_SAY, LA_OFL_HEAD, AF0m.TFIB_ERRNO in *. lia.
Qed.

(* a range apart from the four globals and errno holds no byte of mqo_E *)
Lemma mqb_notE : forall p n, (forall g k, In (g, k) amq_globals -> apart g k p n) ->
  apart (as_errno B) 4 p n -> forall x, p <= x < p + n -> ~ mqo_E B x.
Proof.
  intros p n HG HE x Hx HX.
  pose proof (HG LA_G_SINK 8 ltac:(unfold amq_globals; left; reflexivity)) as G1.
  pose proof (HG LA_G_SAID SAID_SIZE ltac:(unfold amq_globals; right; left; reflexivity)) as G2.
  pose proof (HG LA_G_SAY 8 ltac:(unfold amq_globals; right; right; left; reflexivity)) as G3.
  pose proof (HG LA_OFL_HEAD 8 ltac:(unfold amq_globals; right; right; right; left; reflexivity)) as G4.
  unfold mqo_E, apart in *. lia.
Qed.

Lemma mqb_fmiss : forall lyc Sc (W : world SEGS) memc mdc, AR SEGS B lyc Sc W memc mdc -> fmiss lyc Sc (mqo_E B).
Proof.
  intros lyc Sc W memc mdc HAR. apply (fmiss_app SEGS B LAWS lyc Sc W memc mdc (mqo_E B) HAR).
  intros a Ha. left. pose proof (mqb_E_img a Ha). unfold kLowMemEnd, LA_OFL_HEAD in *. lia.
Qed.

Lemma mqb_row : forall lyc Sc (W : world SEGS) memc mdc, AR SEGS B lyc Sc W memc mdc ->
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_hi lyc <= 2 ^ 64.
Proof.
  intros lyc Sc W memc mdc (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_stk_ceil _ LO) as H1. destruct (lo_top _ LO) as (_ & _ & _ & H2 & _).
  unfold ASAN_CEIL, kHighMemEnd in *. lia.
Qed.

(* an akb byte of the entry outside mqo_E: the jump state's view of it is the entry's *)
Lemma mqb_akb_av : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj a,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj ->
  akb SEGS B lyc Sc (sp - MARK_QUIETLY_AK) sp a -> ~ mqo_E B a ->
  aview SEGS (w_H Wj) memj a = aview SEGS (w_H W) memc a.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj a (HAR & _ & (_ & _ & _ & _ & _ & HK)) Ha HE.
  destruct (mqb_row lyc Sc W memc mdc HAR) as [R1 R2].
  exact (akept_akb SEGS B lyc Sc W memc Wj memj _ _ (mqo_E B) a R1 R2 HK Ha HE).
Qed.

(* an image byte that akept speaks of *)
Lemma mqb_img_av : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj a,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ mqo_E B a -> aview SEGS (w_H Wj) memj a = aview SEGS (w_H W) memc a.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj a (_ & _ & (_ & _ & _ & _ & _ & (_ & _ & K3 & _))) Hi Ho He HE.
  exact (K3 a Hi Ho He HE).
Qed.

(* an akb byte of the entry visible at the entry is visible at the jump *)
Lemma mqb_akb_vis : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj a,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj -> akb SEGS B lyc Sc (sp - MARK_QUIETLY_AK) sp a ->
  ard SEGS (rdW W memc) a <> None -> ard SEGS (rdW Wj memj) a <> None.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj a C Ha Hv.
  destruct (Z_lt_le_dec a 0x10000) as [L|L]; [|destruct (Z_lt_le_dec a pcap_img_end) as [L2|L2]].
  - change (ard SEGS (rdW Wj memj) a) with (aview SEGS (w_H Wj) memj a).
    rewrite (mqb_akb_av lyc Sc W memc mdc sp lyj Sj Wj memj mdj a C Ha); [exact Hv|].
    intros HE. pose proof (mqb_E_img a HE). lia.
  - exact (mqb_vis_img (w_H Wj) memj a ltac:(lia)).
  - change (ard SEGS (rdW Wj memj) a) with (aview SEGS (w_H Wj) memj a).
    rewrite (mqb_akb_av lyc Sc W memc mdc sp lyj Sj Wj memj mdj a C Ha); [exact Hv|].
    intros HE. pose proof (mqb_E_img a HE). unfold pcap_img_end, YImgTop.IMG_TOP, LA_OFL_HEAD in *. lia.
Qed.

(* a present byte is visible *)
Lemma mqb_pres_vis : forall (H : word -> bool) m a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* the bytes of mqo_E are image bytes *)
Lemma mqb_E_in_img : forall a, mqo_E B a -> in_img SEGS a.
Proof.
  intros a H. unfold mqo_E in H. rewrite (AF0m.ts_errno B TB) in H.
  destruct H as [H | [H | [H | [H | H]]]];
  [ apply (mq_in_img HSEGS LA_G_SINK 8) | apply (mq_in_img HSEGS LA_G_SAID SAID_SIZE)
  | apply (mq_in_img HSEGS LA_G_SAY 8) | apply (mq_in_img HSEGS LA_OFL_HEAD 8)
  | apply (mq_in_img HSEGS AF0m.TFIB_ERRNO 4) ]; try exact H; vm_compute; reflexivity.
Qed.

(* THE TAIL OF A STRING'S NUL GRANULE (W6): x, the NUL, is an akb byte of the entry; a byte b after it in its
   8-byte word visible at the entry is visible at the jump: a stack byte by akept's stack clauses, a block byte by
   akept's block clause or past the block by the chunk's tail, an image byte by the ROM at any memory, a side-frame
   byte by akept's frame clause *)
Lemma mqb_tail_vis : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj x b,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj ->
  akb SEGS B lyc Sc (sp - MARK_QUIETLY_AK) sp x -> x < b < x - x mod 8 + 8 ->
  ard SEGS (rdW W memc) b <> None -> ard SEGS (rdW Wj memj) b <> None.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj x b C Hx Hb Hv.
  pose proof C as (HAR & HC & (HARj & Hwle & Hly & Hfr & Hbl & HK)).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  change (ard SEGS (rdW Wj memj) b) with (aview SEGS (w_H Wj) memj b).
  change (ard SEGS (rdW W memc) b) with (aview SEGS (w_H W) memc b) in Hv.
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (NE : forall y, ~ in_img SEGS y -> ~ mqo_E B y) by (intros y Hy HE; exact (Hy (mqb_E_in_img y HE))).
  destruct Hx as [(Hs & Hw) | [(b0 & m & Hin & Hb0) | [(Hi & _ & _) | (cid & pos & Hin & Hr)]]].
  - destruct (mqb_row lyc Sc W memc mdc HAR) as [R1 R2].
    pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
    destruct (lo_top _ LO) as (_ & _ & _ & H2 & _).
    pose proof (@ASAN_CEIL_range rc) as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
    assert (Hb64 : b < 2 ^ 64) by (unfold kHighMemEnd in *; lia).
    assert (Hnim : ~ in_img SEGS b).
    { intros Hi. pose proof (pa_img_range b Hi). unfold pcap_img_end, YImgTop.IMG_TOP in *. unfold alloc_ceiling in *. lia. }
    destruct (Z_lt_le_dec b (sp - MARK_QUIETLY_AK)) as [B1|B1]; [|destruct (Z_lt_le_dec b sp) as [B2|B2]].
    + rewrite (K1 b ltac:(lia) ltac:(lia) (NE b Hnim)). exact Hv.
    + apply mqb_pres_vis. exact (K6 b ltac:(lia)).
    + rewrite (K1 b ltac:(lia) ltac:(lia) (NE b Hnim)). exact Hv.
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HAR Hin) as (H16 & H4096 & Hc & _).
    destruct (Z_lt_le_dec b (b0 + req_size m)) as [B1|B1].
    + assert (Hbr : b0 <= b < b0 + req_size m) by lia.
      assert (Hnim : ~ in_img SEGS b).
      { destruct (al_client_img _ _ LAWS lyc Sc W memc mdc b HAR
          (or_introl (ex_intro _ b0 (ex_intro _ m (conj Hin Hbr))))) as (_ & Hni). exact Hni. }
      pose proof (K2 b0 m (b - b0) Hin ltac:(lia)) as Kb.
      replace (b0 + (b - b0)) with b in Kb by lia.
      rewrite (Kb (NE b Hnim)). exact Hv.
    + apply (mqb_blk_tail_vis_r SEGS B lyj Sj Wj memj mdj b0 m b HARj (Hbl b0 m Hin)).
      split; [lia|]. unfold round_up. lia.
  - pose proof (pa_img_range x Hi) as [X1 X2].
    apply (mqb_vis_img (w_H Wj) memj b). unfold pcap_img_end, YImgTop.IMG_TOP in *. lia.
  - pose proof HAR as (M & _).
    destruct (frame_facts B lyc Sc _ cid pos M Hin) as (Cc & _).
    destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F32 & _).
    assert (Hfb : fs_frame_bytes cid mod 8 = 0).
    { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
      apply Z.mod_divide; [lia|]. exists (8 * 2 ^ cid). lia. }
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    assert (Hrb : in_zr b (frame_rng lyc (cid, pos))) by (unfold in_zr, frame_rng; cbn [fst snd]; lia).
    assert (Hfr' : frame_addr lyc cid pos <= b < frame_addr lyc cid pos + fs_frame_bytes cid)
      by (unfold in_zr, frame_rng in Hrb; cbn [fst snd] in Hrb; lia).
    assert (Hnim : ~ in_img SEGS b).
    { destruct (al_client_img _ _ LAWS lyc Sc W memc mdc b HAR
        (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Hfr')))))) as (_ & Hni).
      exact Hni. }
    rewrite (K4 cid pos b Hin (or_introl Hrb) (NE b Hnim)). exact Hv.
Qed.

(* an akb byte of the entry is an akb byte of the jump state at the callee's window *)
Lemma mqb_akb_conv : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj a,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj ->
  akb SEGS B lyc Sc (sp - MARK_QUIETLY_AK) sp a -> akb SEGS B lyj Sj (sp - REAC_SERVED_MARK_AK) sp a.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj a (_ & _ & (_ & _ & Hly & Hfr & Hbl & _)) Ha.
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  pose proof MARK_QUIETLY_AK_covers_tail as HKK.
  destruct Ha as [(Hs & Hw) | [(b & m & Hin & Hb) | [Hi | (cid & pos & Hin & Hr)]]].
  - left. rewrite Elo, Ehi. split; [exact Hs | lia].
  - right; left. exists b, m. split; [exact (Hbl b m Hin) | exact Hb].
  - right; right; left. exact Hi.
  - right; right; right. exists cid, pos. split; [rewrite Hfr; exact Hin|].
    unfold frame_rng, frame_addr in *. rewrite EF. exact Hr.
Qed.

(* THE FRESH BLOCK: no akb byte of the entry lies in it or in the 16 bytes before it (its chunk at the jump) *)
Lemma mqb_fresh_ext : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj res a,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj ->
  In (res, AMF_BLOCK) (ablocks B lyj Sj) -> ~ In (res, AMF_BLOCK) (ablocks B lyc Sc) ->
  akb SEGS B lyc Sc (sp - MARK_QUIETLY_AK) sp a -> ~ (res - 16 <= a < res + AMF_BLOCK).
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj res a (HAR & _ & (HARj & _ & Hly & Hfr & Hbl & _)) Hres Hnres Ha Hx.
  pose proof HARj as (Mj & LGj & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  apply In_ablocks in Hres as (kr & Hkr & _ & Hur & Hnr).
  pose proof (chunk_facts B lyj Sj _ kr Mj Hkr) as (_ & _ & _ & G4 & G5 & _ & _ & G8 & _).
  rewrite Hur in G4. rewrite Hnr in G8. change (req_size AMF_BLOCK) with AMF_BLOCK in G8.
  assert (Hax : ck_base B lyj kr <= a < ck_base B lyj kr + ck_extent kr) by lia.
  destruct Ha as [(Hs & _) | [(b & m & Hin & Hb) | [(Hi & _ & _) | (cid & pos & Hin & Hr)]]].
  - destruct (chunk_apart B lyj Sj _ kr a Mj Hkr Hax) as [_ NS]. apply NS. rewrite Elo, Ehi. exact Hs.
  - pose proof (Hbl b m Hin) as Hinj. apply In_ablocks in Hinj as (kb & Hkb & _ & Hub & Hnb).
    pose proof (chunk_facts B lyj Sj _ kb Mj Hkb) as (_ & _ & _ & U4 & U5 & _ & _ & U8 & _).
    pose proof (wf_chunks_nodup _ _ _ _ _ (am_wf _ _ _ _ Mj)) as ND.
    destruct (mqb_nodup _ _ ck_beg (st_chunks Sj) kb kr ND Hkb Hkr) as [E | Hne].
    + subst kb. apply Hnres. replace res with b by congruence. replace AMF_BLOCK with m by congruence. exact Hin.
    + pose proof (chunks_disjoint B lyj Sj _ kb kr Mj Hkb Hkr Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
      rewrite Hnb in U8. rewrite Hub in U4. lia.
  - destruct (chunk_apart B lyj Sj _ kr a Mj Hkr Hax) as [NI _]. apply NI.
    destruct Hi as (sg & Hsg & Hr). pose proof (al_img _ _ _ _ LGj sg Hsg) as [I1 I2].
    unfold in_zr. lia.
  - assert (Hin' : In (cid, pos) (frames Sj)) by (rewrite Hfr; exact Hin).
    destruct (frame_facts B lyj Sj _ cid pos Mj Hin') as (C1 & C2 & _ & _ & _ & P1 & P2 & _).
    pose proof (chunk_vs_F B lyj Sj _ kr Mj Hkr) as D. unfold zdisjoint in D. cbn [fst snd] in D.
    unfold in_zr, frame_rng, frame_addr in Hr. cbn [fst snd] in Hr. rewrite <- EF in Hr.
    assert (0 <= cid * 2 ^ 20) by (apply Z.mul_nonneg_nonneg; lia).
    unfold kFakeFramesOff in P1. lia.
Qed.

(* ==========================================================================
   3. The pieces of reac_served_mark's Pre at the jump
   ========================================================================== *)

(* a byte of g_nl *)
Lemma mqb_gnl_mb : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj x,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj -> LA_G_NL <= x < LA_G_NL + NK_SIZE ->
  mbyte SEGS (rdW Wj memj) x = mbyte SEGS (rdW W memc) x.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj x C Hx. apply mq_mb_of_av.
  apply (mqb_img_av lyc Sc W memc mdc sp lyj Sj Wj memj mdj x C).
  - exact (mq_in_img HSEGS LA_G_NL NK_SIZE mqb_seg_nl x Hx).
  - exact (mq_not_owned B TB LA_G_NL NK_SIZE mqb_own_nl x Hx).
  - rewrite (AF0m.ts_errno B TB). unfold LA_G_NL, NK_SIZE, AF0m.TFIB_ERRNO in *. lia.
  - apply mqb_E_low. unfold LA_G_NL, NK_SIZE, LA_G_SINK in *. lia.
Qed.

(* a literal of .rodata that is not an owned static *)
Lemma mqb_lit_mb : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj p s,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj -> 0x10000 <= p -> p + Z.of_nat (length s) + 1 <= 0x31000 ->
  forallb (fun r => (p + (Z.of_nat (length s) + 1) <=? fst r) || (fst r + snd r <=? p)) AF0m.Tfib_owned_static
    = true ->
  acstr_at SEGS (rdW W memc) p s -> acstr_at SEGS (rdW Wj memj) p s.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj p s C H0 H1 Ho Cs.
  apply (mq_cstr_tr (rdW W memc) (rdW Wj memj) p s); [|exact Cs].
  intros x Hx. apply mq_mb_of_av. apply (mqb_img_av lyc Sc W memc mdc sp lyj Sj Wj memj mdj x C).
  - apply (mq_in_img HSEGS 0x10000 0x21000 mqb_seg0 x). lia.
  - exact (mq_not_owned B TB p (Z.of_nat (length s) + 1) Ho x ltac:(lia)).
  - rewrite (AF0m.ts_errno B TB). unfold AF0m.TFIB_ERRNO. lia.
  - apply mqb_E_low. unfold LA_G_SINK. lia.
Qed.

(* a string of the image, as a string wrapper reads it *)
Lemma mqb_rt_img : forall lyc Sc (W : world SEGS) memc mdc lyj Sj (Wj : world SEGS) memj mdj
    (regs regs' : bvmap 5 word) K K' p s,
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyj Sj Wj memj mdj ->
  K' <= K -> spZ regs' = spZ regs -> 0x10000 <= p -> p + Z.of_nat (length s) + 8 <= pcap_img_end ->
  astr_rt_ok SEGS regs K (rdW W memc) p s -> astr_rt_ok SEGS regs' K' (rdW Wj memj) p s.
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs regs' K K' p s (M1 & _) (M2 & _) HK Hs H0 H1
    (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (mqb_img_sh lyc Sc _ lyj Sj _ p (Z.of_nat (length s) + 1) M1 M2 H0 ltac:(lia) ltac:(lia) R4) as [A1 A2].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact A1|]. split; [exact A2|].
  split; [intros b Hb; exact (mqb_vis_img (w_H Wj) memj b ltac:(lia))|].
  exact (mq_af regs regs' K K' p _ HK Hs R7).
Qed.

(* a string of the read set, as a string wrapper reads it *)
Lemma mqb_rt_rd : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj (regs regs' : bvmap 5 word) p s,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj -> spZ regs = sp -> spZ regs' = sp ->
  (forall a, p <= a <= p + Z.of_nat (length s) -> akb SEGS B lyc Sc (sp - MARK_QUIETLY_AK) sp a) ->
  astr_rt_ok SEGS regs MARK_QUIETLY_AK (rdW W memc) p s ->
  astr_rt_ok SEGS regs' REAC_SERVED_MARK_AK (rdW Wj memj) p s.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj regs regs' p s C Hs Hs' Hrd (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  pose proof C as (HAR & HC & (HARj & Hwle & Hly & Hfr & Hbl & HK)).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct (shadow_transport_akb SEGS B LAWS TB (@pa_img_range _ _ PI) lyc Sc W memc mdc lyj Sj Wj memj mdj
    (sp - MARK_QUIETLY_AK) sp (mqo_E B) p (Z.of_nat (length s) + 1) HAR HARj Elo Ehi Hbl HK
    (mqb_fmiss lyc Sc W memc mdc HAR) ltac:(lia) ltac:(intros a Ha; apply Hrd; lia) R4 R5) as [A1 A2].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact A1|]. split; [exact A2|].
  split.
  - intros b Hb.
    assert (Hx : p <= p + Z.of_nat (length s) <= p + Z.of_nat (length s)) by (split; [pose proof (Nat2Z.is_nonneg (length s)); lia | lia]).
    exact (mqb_tail_vis lyc Sc W memc mdc sp lyj Sj Wj memj mdj (p + Z.of_nat (length s)) b C
             (Hrd _ Hx) Hb (R6 b Hb)).
  - apply (mq_af regs regs' _ _ p _ MARK_QUIETLY_AK_covers_tail); [congruence | exact R7].
Qed.

(* the name's bytes and its NUL: akb at the entry and outside mqo_E *)
Lemma mqb_name_mb : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs : bvmap 5 word) s,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  astr_arg SEGS (rdW W memc) (aarg regs 1) (Some s) ->
  (forall g n, In (g, n) amq_globals -> apart g n (aarg regs 1) (Z.of_nat (length s) + 8)) ->
  apart (as_errno B) 4 (aarg regs 1) (Z.of_nat (length s) + 8) ->
  forall x, aarg regs 1 <= x <= aarg regs 1 + Z.of_nat (length s) ->
    akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) x /\ ~ mqo_E B x.
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs s C HRD [Hn Cs] HG HE x Hx. split.
  - apply HRD. unfold mark_quietly_ard, amk_rd. left. split; [exact Hn|]. exists s. split; [exact Cs | exact Hx].
  - apply (mqb_notE (aarg regs 1) (Z.of_nat (length s) + 8)); [exact HG | exact HE | lia].
Qed.

(* a live table string's bytes and its NUL: akb at the entry *)
Lemma mqb_tab_rd : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs : bvmap 5 word) kbs tab i n2 ix p,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  anlk_at SEGS (rdW W memc) LA_G_NL kbs -> aiftab_at SEGS (rdW W memc) LA_G_NL kbs tab ->
  nth_error tab i = Some (n2, ix) -> au64_at SEGS (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  acstr_at SEGS (rdW W memc) p n2 ->
  forall x, p <= x <= p + Z.of_nat (length n2) ->
    akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) x.
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab i n2 ix p C HRD Hn Hi Ht Hp Cs x Hx. apply HRD.
  unfold mark_quietly_ard, amk_rd. right; right. unfold amk_tab_rd.
  exists kbs, tab, i, n2, ix, p. split; [exact Hn|]. split; [exact Hi|]. split; [exact Ht|]. split; [exact Hp|].
  split; [exact Cs | exact Hx].
Qed.

(* a live table string's bytes: kept *)
Lemma mqb_tab_mb : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs : bvmap 5 word) kbs tab,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  amk_nlk_ok SEGS (rdW W memc) kbs tab 2 -> amk_table_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W memc) tab ->
  (forall g n, In (g, n) amq_globals -> forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     apart g n p (Z.of_nat (length n2) + 1)) ->
  forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
  au64_at SEGS (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> acstr_at SEGS (rdW W memc) p n2 ->
  forall x, p <= x < p + Z.of_nat (length n2) + 1 -> mbyte SEGS (rdW Wj memj) x = mbyte SEGS (rdW W memc) x.
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab C HRD HNLK HT HG i n2 ix p Hi Hp Cs x Hx.
  pose proof HNLK as (Hn & _ & _ & _ & _ & Hift & _).
  destruct (mq_cstr_rng _ p n2 Cs) as [R0 R1].
  destruct (HT i n2 ix p Hi Hp ltac:(lia)) as (_ & _ & G2 & _).
  apply mq_mb_of_av. apply (mqb_akb_av lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj x C).
  - apply (mqb_tab_rd lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab i n2 ix p C HRD Hn Hift Hi Hp Cs). lia.
  - apply (mqb_notE p (Z.of_nat (length n2) + 1)); [|exact G2|lia].
    intros g k Hg. exact (HG g k Hg i n2 ix p Hi Hp ltac:(lia)).
Qed.

Lemma mqb_nlk_at : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj bs,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj ->
  anlk_at SEGS (rdW W memc) LA_G_NL bs -> anlk_at SEGS (rdW Wj memj) LA_G_NL bs.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj bs C [[Hab Haw] HL]. split; [|exact HL]. split.
  - apply (mq_ab_tr (rdW W memc) (rdW Wj memj) LA_G_NL bs); [|exact Hab]. intros i Hi.
    apply (mqb_gnl_mb lyc Sc W memc mdc sp lyj Sj Wj memj mdj _ C). lia.
  - intros i Hi. apply mqb_wr_img. rewrite HL in Hi. unfold LA_G_NL, NK_SIZE, pcap_img_end, YImgTop.IMG_TOP in *. lia.
Qed.

Lemma mqb_iftab : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj bs tab,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj ->
  aiftab_at SEGS (rdW W memc) LA_G_NL bs tab ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     acstr_at SEGS (rdW W memc) p n2 ->
     forall x, p <= x < p + Z.of_nat (length n2) + 1 -> mbyte SEGS (rdW Wj memj) x = mbyte SEGS (rdW W memc) x) ->
  aiftab_at SEGS (rdW Wj memj) LA_G_NL bs tab.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj bs tab C (N & L & E) ST. split; [exact N|]. split; [exact L|].
  intros i nm ix Hi. destruct (E i nm ix Hi) as (R & p & P & Pn & Cs & I).
  assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  split; [exact R|]. exists p. split; [|split; [exact Pn|split]].
  - apply (mq_vm_tr (rdW W memc) (rdW Wj memj) _ 8 p); [|exact P]. intros k Hk.
    apply (mqb_gnl_mb lyc Sc W memc mdc sp lyj Sj Wj memj mdj _ C). unfold NK_IF_NAME, NK_SIZE in *. lia.
  - exact (mq_cstr_tr _ _ p nm (ST i nm ix p Hi P Cs) Cs).
  - apply (mq_vm_tr (rdW W memc) (rdW Wj memj) _ 4 ix); [|exact I]. intros k Hk.
    apply (mqb_gnl_mb lyc Sc W memc mdc sp lyj Sj Wj memj mdj _ C). unfold NK_IF_INDEX, NK_SIZE in *. lia.
Qed.

Lemma mqb_nlk_ok : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs : bvmap 5 word) kbs tab,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  amk_table_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W memc) tab ->
  (forall g n, In (g, n) amq_globals -> forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     apart g n p (Z.of_nat (length n2) + 1)) ->
  amk_nlk_ok SEGS (rdW W memc) kbs tab 2 -> amk_nlk_ok SEGS (rdW Wj memj) kbs tab 2.
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab C HRD HT HG HN.
  pose proof HN as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  pose proof C as (HAR & _ & (HARj & _)). pose proof HAR as (M1 & _). pose proof HARj as (M2 & _).
  destruct (mqb_img_sh lyc Sc _ lyj Sj _ LA_G_NL NK_SIZE M1 M2
    ltac:(unfold LA_G_NL; lia) ltac:(unfold LA_G_NL, NK_SIZE, pcap_img_end, YImgTop.IMG_TOP; lia)
    ltac:(unfold NK_SIZE; lia) N7) as [A1 A2].
  split; [exact (mqb_nlk_at lyc Sc W memc mdc _ lyj Sj Wj memj mdj kbs C N1)|].
  split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|].
  split; [exact (mqb_iftab lyc Sc W memc mdc _ lyj Sj Wj memj mdj kbs tab C N6
                   (mqb_tab_mb lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab C HRD HN HT HG))|].
  split; [exact A1 | exact A2].
Qed.

Lemma mqb_errno : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs regsj : bvmap 5 word) res,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj -> In (res, AMF_BLOCK) (ablocks B lyj Sj) ->
  spZ regsj = spZ regs -> aarg regsj 0 = aarg regs 0 ->
  amk_errno_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W memc) ->
  amk_errno_ok SEGS B regsj REAC_SERVED_MARK_AK res AMF_BLOCK (rdW Wj memj).
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj res C Hres Hsp Ha0 (E1 & E2 & E3 & E4 & E5 & _ & E7).
  pose proof C as (HAR & _ & (HARj & _)). pose proof HAR as (M1 & _). pose proof HARj as (M2 & _).
  pose proof (AF0m.ts_errno B TB) as He.
  pose proof (blk_off_imgP B lyj Sj Wj memj mdj res AMF_BLOCK HARj Hres) as Hoff.
  change (req_size AMF_BLOCK) with AMF_BLOCK in Hoff. unfold off_img in Hoff.
  assert (Hlo : 0x10000 <= as_errno B) by (rewrite He; unfold AF0m.TFIB_ERRNO; lia).
  assert (Hhi : as_errno B + 4 <= pcap_img_end) by (rewrite He; unfold AF0m.TFIB_ERRNO, pcap_img_end, YImgTop.IMG_TOP; lia).
  split; [exact E1|].
  split; [intros i Hi; apply mqb_wr_img; rewrite He; unfold AF0m.TFIB_ERRNO, pcap_img_end, YImgTop.IMG_TOP; lia|].
  split; [exact (proj1 (mqb_img_sh lyc Sc _ lyj Sj _ (as_errno B) 4 M1 M2 Hlo Hhi ltac:(lia) E3))|].
  split; [exact (mq_af regs regsj _ _ _ _ MARK_QUIETLY_AK_covers_tail Hsp E4)|].
  split; [exact E5|].
  split; [unfold apart; rewrite He; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, AF0m.TFIB_ERRNO, AMF_BLOCK in *; lia|].
  rewrite Ha0. exact E7.
Qed.

Lemma mqb_table : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs regsj : bvmap 5 word) res kbs tab,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  In (res, AMF_BLOCK) (ablocks B lyj Sj) -> ~ In (res, AMF_BLOCK) (ablocks B lyc Sc) ->
  spZ regsj = spZ regs -> aarg regsj 0 = aarg regs 0 ->
  amk_nlk_ok SEGS (rdW W memc) kbs tab 2 ->
  amk_table_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W memc) tab ->
  amk_table_ok SEGS B regsj REAC_SERVED_MARK_AK res AMF_BLOCK (rdW Wj memj) tab.
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj res kbs tab C HRD Hres Hnres Hsp Ha0 HNLK HT
    i n2 ix p Hi Hp Hr.
  pose proof HNLK as (Hn & _ & _ & _ & _ & Hift & _).
  pose proof Hift as (_ & L80 & EI).
  assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  assert (Hp0 : au64_at SEGS (rdW W memc) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { apply (mq_vm_tr (rdW Wj memj) (rdW W memc) _ 8 p); [|exact Hp]. intros k Hk. symmetry.
    apply (mqb_gnl_mb lyc Sc W memc mdc _ lyj Sj Wj memj mdj _ C). unfold NK_IF_NAME, NK_SIZE in *. lia. }
  destruct (HT i n2 ix p Hi Hp0 Hr) as (RT & G1 & G2 & _ & G4).
  destruct (EI i n2 ix Hi) as (_ & p0 & P0 & _ & C0 & _).
  pose proof (mq_cstr_rng _ p0 n2 C0) as Q0.
  assert (Ep : p = p0) by (apply (mq_vm_unique _ _ 8 p p0 Hp0 P0); change (8 * Z.of_nat 8) with 64; lia).
  subst p0.
  pose proof (mqb_tab_rd lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab i n2 ix p C HRD Hn Hift Hi Hp0 C0) as AK.
  split; [exact (mqb_rt_rd lyc Sc W memc mdc _ lyj Sj Wj memj mdj regs regsj p n2 C eq_refl Hsp AK RT)|].
  split; [exact G1|]. split; [exact G2|].
  split.
  - apply (mqb_apart_ext res p (Z.of_nat (length n2) + 1)); [lia | lia |].
    intros a Ha. exact (mqb_fresh_ext lyc Sc W memc mdc _ lyj Sj Wj memj mdj res a C Hres Hnres (AK a ltac:(lia))).
  - rewrite Ha0. exact G4.
Qed.

Lemma mqb_policy : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj (regs regsj : bvmap 5 word),
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj -> spZ regsj = spZ regs ->
  amk_policy_ok SEGS regs MARK_QUIETLY_AK (rdW W memc) ->
  amk_policy_ok SEGS regsj REAC_SERVED_MARK_AK (rdW Wj memj).
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj regs regsj C Hsp
    (P1 & R1 & P2 & R2 & P3 & R3 & P4 & R4 & P5 & R5 & P6 & R6 & P7 & R7 & P8 & R8 & P9 & R9 & P10 & R10 & P11 & R11
     & P12 & R12 & P13 & R13).
  pose proof C as (HAR & _ & (HARj & _)).
  pose proof MARK_QUIETLY_AK_covers_tail as HKK.
  assert (LT : forall p s, 0x10000 <= p -> p + Z.of_nat (length s) + 1 <= 0x31000 ->
    forallb (fun r => (p + (Z.of_nat (length s) + 1) <=? fst r) || (fst r + snd r <=? p)) AF0m.Tfib_owned_static
      = true ->
    acstr_at SEGS (rdW W memc) p s -> acstr_at SEGS (rdW Wj memj) p s)
    by (intros p s; exact (mqb_lit_mb lyc Sc W memc mdc sp lyj Sj Wj memj mdj p s C)).
  assert (RT : forall p s, 0x10000 <= p -> p + Z.of_nat (length s) + 8 <= pcap_img_end ->
    astr_rt_ok SEGS regs MARK_QUIETLY_AK (rdW W memc) p s ->
    astr_rt_ok SEGS regsj REAC_SERVED_MARK_AK (rdW Wj memj) p s)
    by (intros p s; exact (mqb_rt_img lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj _ _ p s HAR HARj HKK Hsp)).
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P1]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R1]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P2]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R2]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P3]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R3]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P4]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R4]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P5]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R5]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P6]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R6]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P7]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R7]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P8]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R8]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P9]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R9]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P10]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R10]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P11]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R11]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P12]|].
  split; [apply RT; [mqb_cmp | mqb_cmp | exact R12]|].
  split; [apply LT; [mqb_cmp | mqb_cmp | vm_compute; reflexivity | exact P13]|].
  apply RT; [mqb_cmp | mqb_cmp | exact R13].
Qed.

Lemma mqb_arg : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs : bvmap 5 word) nm,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  astr_arg SEGS (rdW W memc) (aarg regs 1) nm ->
  (forall g n, In (g, n) amq_globals -> forall s, nm = Some s -> apart g n (aarg regs 1) (Z.of_nat (length s) + 8)) ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W memc) nm ->
  astr_arg SEGS (rdW Wj memj) (aarg regs 1) nm.
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs nm C HRD HA HG HN.
  destruct nm as [s|]; [|exact HA].
  destruct (HN s eq_refl) as (_ & _ & _ & _ & G3 & _).
  pose proof (mqb_name_mb lyc Sc W memc mdc lyj Sj Wj memj mdj regs s C HRD HA (fun g n H => HG g n H s eq_refl) G3)
    as AK.
  destruct HA as [Hn Cs]. split; [exact Hn|].
  apply (mq_cstr_tr (rdW W memc) (rdW Wj memj) _ s); [|exact Cs]. intros x Hx. apply mq_mb_of_av.
  destruct (AK x ltac:(lia)) as [A1 A2].
  exact (mqb_akb_av lyc Sc W memc mdc _ lyj Sj Wj memj mdj x C A1 A2).
Qed.

Lemma mqb_name_ok : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs regsj : bvmap 5 word) res nm,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  In (res, AMF_BLOCK) (ablocks B lyj Sj) -> ~ In (res, AMF_BLOCK) (ablocks B lyc Sc) ->
  spZ regsj = spZ regs -> aarg regsj 0 = aarg regs 0 -> aarg regsj 1 = aarg regs 1 ->
  astr_arg SEGS (rdW W memc) (aarg regs 1) nm ->
  (forall g n, In (g, n) amq_globals -> forall s, nm = Some s -> apart g n (aarg regs 1) (Z.of_nat (length s) + 8)) ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W memc) nm ->
  amk_name_ok SEGS B regsj REAC_SERVED_MARK_AK res AMF_BLOCK (rdW Wj memj) nm.
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj res nm C HRD Hres Hnres Hsp Ha0 Ha1 HA HG HN s Es.
  subst nm. rewrite Ha0, Ha1.
  destruct (HN s eq_refl) as (L & RT & G1 & _ & G3 & G4).
  pose proof (mqb_name_mb lyc Sc W memc mdc lyj Sj Wj memj mdj regs s C HRD HA (fun g n H => HG g n H s eq_refl) G3)
    as AK.
  split; [exact L|].
  split; [exact (mqb_rt_rd lyc Sc W memc mdc _ lyj Sj Wj memj mdj regs regsj _ s C eq_refl Hsp
                   (fun a Ha => proj1 (AK a Ha)) RT)|].
  split; [exact G1|].
  split.
  - apply (mqb_apart_ext res (aarg regs 1) (Z.of_nat (length s) + 1)); [lia | lia |].
    intros a Ha.
    exact (mqb_fresh_ext lyc Sc W memc mdc _ lyj Sj Wj memj mdj res a C Hres Hnres (proj1 (AK a ltac:(lia)))).
  - split; [exact G3 | exact G4].
Qed.

(* the marks block at the jump: its bytes kept (a block of the entry), writable (a block of the jump state) *)
Lemma mqb_marks_at : forall lyc Sc W memc mdc sp lyj Sj Wj memj mdj p gbs,
  mqb_ctx lyc Sc W memc mdc sp lyj Sj Wj memj mdj ->
  In (p, MK_SIZE) (ablocks B lyc Sc) -> YCbq.off_img p MK_SIZE ->
  amarks_at SEGS (rdW W memc) p gbs -> amarks_at SEGS (rdW Wj memj) p gbs.
Proof.
  intros lyc Sc W memc mdc sp lyj Sj Wj memj mdj p gbs C Hin Htop [[Hab Haw] HLn].
  pose proof C as (_ & _ & (HARj & _ & _ & _ & Hbl & _)).
  destruct (al_blocks _ _ LAWS lyj Sj Wj memj mdj _ _ HARj (Hbl _ _ Hin)) as (_ & _ & _ & _ & Hpr & _).
  split; [|exact HLn]. split.
  - apply (mq_ab_tr (rdW W memc) (rdW Wj memj) p gbs); [|exact Hab]. intros i Hi. apply mq_mb_of_av.
    apply (mqb_akb_av lyc Sc W memc mdc sp lyj Sj Wj memj mdj _ C).
    + right; left. exists p, MK_SIZE. split; [exact Hin|]. change (req_size MK_SIZE) with MK_SIZE. lia.
    + intros HE. pose proof (mqb_E_img _ HE). unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_OFL_HEAD, MK_SIZE in *.
      destruct Htop as [Htop | Htop]; lia.
  - intros i Hi. apply mqb_wr_pres.
    exact (proj1 (Hpr (p + i) ltac:(change (req_size MK_SIZE) with MK_SIZE; lia))).
Qed.

Lemma mqb_marks : forall lyc Sc W memc mdc lyj Sj Wj memj mdj (regs regsj : bvmap 5 word) res,
  mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj ->
  In (res, AMF_BLOCK) (ablocks B lyj Sj) -> ~ In (res, AMF_BLOCK) (ablocks B lyc Sc) ->
  spZ regsj = spZ regs -> aarg regsj 0 = aarg regs 0 ->
  (aarg regs 0 <> 0 -> amarks_ledger (ablocks B lyc Sc) (aarg regs 0)) ->
  amk_block_ok SEGS B regs MARK_QUIETLY_AK 0 0 (rdW W memc) ->
  amk_block_ok SEGS B regsj REAC_SERVED_MARK_AK res AMF_BLOCK (rdW Wj memj).
Proof.
  intros lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj res C Hres Hnres Hsp Ha0 HL HB.
  unfold amk_block_ok. rewrite Ha0. intros Hn.
  destruct (HB Hn) as ((M1 & M2 & M3 & M4 & M5 & M6) & G1 & G2 & _ & gbs & Hm & Hwf).
  destruct (HL Hn) as [Hin Htop].
  pose proof C as (HAR & HC & (HARj & Hwle & Hly & Hfr & Hbl & HK)).
  pose proof (Hbl _ _ Hin) as Hinj.
  destruct (al_shadow _ _ LAWS lyj Sj Wj memj mdj _ _ HARj Hinj) as [HBS HHV].
  change (req_size MK_SIZE) with MK_SIZE in HBS, HHV.
  assert (RU : round_up MK_SIZE 16 = 528) by (vm_compute; reflexivity).
  split; [|split; [exact G1|split; [exact G2|split]]].
  - split; [exact M1|]. split; [exact M2|].
    split; [exact (block_shadow_range _ _ _ _ (aarg regs 0) MK_SIZE HBS ltac:(lia) ltac:(lia))|].
    split; [exact HHV|].
    split.
    + intros b Hb. exact (mqb_blk_tail_vis16 SEGS B lyj Sj Wj memj mdj _ _ b HARj Hinj
                            ltac:(rewrite RU; unfold MK_SIZE in *; lia)).
    + exact (mq_af regs regsj _ _ _ _ MARK_QUIETLY_AK_covers_tail Hsp M6).
  - apply (mqb_apart_ext res (aarg regs 0) MK_SIZE MK_SIZE); [unfold MK_SIZE; lia | lia |].
    intros a Ha. apply (mqb_fresh_ext lyc Sc W memc mdc _ lyj Sj Wj memj mdj res a C Hres Hnres).
    right; left. exists (aarg regs 0), MK_SIZE. split; [exact Hin|]. change (req_size MK_SIZE) with MK_SIZE. lia.
  - exists gbs. split; [|exact Hwf].
    exact (mqb_marks_at lyc Sc W memc mdc _ lyj Sj Wj memj mdj _ gbs C Hin Htop Hm).
Qed.

(* the FILE at the jump: amf_k, the block writable (a block of the jump state), g_said writable (image rw) *)
Lemma mqb_mf0 : forall lyj Sj (Wj : world SEGS) memj mdj res,
  AR SEGS B lyj Sj Wj memj mdj -> In (res, AMF_BLOCK) (ablocks B lyj Sj) ->
  LinkMfDefs.amf_k SEGS link_amf (rdW Wj memj) res 0 -> amemfile_k SEGS (rdW Wj memj) res 0.
Proof.
  intros lyj Sj Wj memj mdj res HARj Hres (A & Wn).
  destruct (al_blocks _ _ LAWS lyj Sj Wj memj mdj _ _ HARj Hres) as (_ & _ & _ & _ & Hpr & _).
  split; [exact A|]. split; [exact Wn|]. split.
  - intros i Hi. apply mqb_wr_pres.
    exact (proj1 (Hpr (res + i) ltac:(change (req_size AMF_BLOCK) with AMF_BLOCK; lia))).
  - intros i Hi. apply mqb_wr_img. unfold LA_G_SAID, SAID_SIZE, pcap_img_end, YImgTop.IMG_TOP in *. lia.
Qed.

(* the FILE block at the jump: in memory, its shadow (AR's block shadow), below the callee's window *)
Lemma mqb_blk : forall lyj Sj (Wj : world SEGS) memj mdj (regs regsj : bvmap 5 word) res,
  AR SEGS B lyj Sj Wj memj mdj -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK -> spZ regsj = spZ regs ->
  In (res, AMF_BLOCK) (ablocks B lyj Sj) -> amf_blk_ok SEGS regsj REAC_SERVED_MARK_AK (rdW Wj memj) res.
Proof.
  intros lyj Sj Wj memj mdj regs regsj res HARj HC Hsp Hres.
  destruct (al_blocks _ _ LAWS lyj Sj Wj memj mdj _ _ HARj Hres) as (_ & H4 & Hceil & Happ & _).
  destruct (al_shadow _ _ LAWS lyj Sj Wj memj mdj _ _ HARj Hres) as [HBS HHV].
  change (req_size AMF_BLOCK) with AMF_BLOCK in Hceil, Happ, HBS, HHV.
  pose proof (@ASAN_CEIL_range rc) as [[CR1 CR2] _]. unfold ASAN_CEIL in CR1, CR2.
  pose proof MARK_QUIETLY_AK_covers_tail as HKK.
  split; [unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AMF_BLOCK in *;
          lia|].
  split; [exact (block_shadow_range _ _ _ _ res AMF_BLOCK HBS ltac:(lia) ltac:(lia))|].
  split; [exact HHV|].
  unfold apart_frame. rewrite Hsp. lia.
Qed.

(* ==========================================================================
   4. The three lemmas
   ========================================================================== *)

Lemma mqo_rsm_pre : forall res lyc Sc (W : world SEGS) memc mdc (regs : bvmap 5 word) lyj Sj Wj memj mdj
    (regsj : bvmap 5 word),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  mark_quietly_apre_open SEGS B (ablocks B lyc Sc) regs (rdW W memc) ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  mqo_rel SEGS B (spZ regs) lyc Sc W memc lyj Sj Wj memj mdj ->
  In (res, AMF_BLOCK) (ablocks B lyj Sj) -> ~ In (res, AMF_BLOCK) (ablocks B lyc Sc) ->
  au64_at SEGS (rdW Wj memj) LA_G_SAY res ->
  LinkMfDefs.amf_k SEGS link_amf (rdW Wj memj) res 0 ->
  aarg regsj 0 = aarg regs 0 -> aarg regsj 1 = aarg regs 1 -> spZ regsj = spZ regs ->
  reac_served_mark_apre SEGS B res (ablocks B lyj Sj) regsj (rdW Wj memj).
Proof.
  intros res lyc Sc W memc mdc regs lyj Sj Wj memj mdj regsj HAR HC HP HRD HREL Hres Hnres Hsay HMF Ha0 Ha1 Hsp.
  assert (C : mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj) by exact (conj HAR (conj HC HREL)).
  destruct HP as (_ & HCX & _).
  destruct HCX as (kbs & tab & nm & HL & HFIX & HNLK & HERR & Esay & Esaid & _ & _ & HTAB & HPOL & HARG & HNAME
    & HBLK).
  pose proof HREL as (HARj & _ & _ & _ & Hbl & _).
  assert (H00 : res <> 0).
  { destruct (al_blocks _ _ LAWS lyj Sj Wj memj mdj _ _ HARj Hres) as (_ & H4 & _). lia. }
  exists kbs, tab, nm, 0.
  split; [exact Hres|].
  split; [rewrite Ha0; intros H0; destruct (HL H0) as [Hin Htop]; split; [exact (Hbl _ _ Hin) | exact Htop]|].
  split; [exact (mqb_nlk_ok lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab C HRD HTAB
                   (fun g n H => proj2 (HFIX g n H)) HNLK)|].
  split; [exact (mqb_errno lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj res C Hres Hsp Ha0 HERR)|].
  split; [exact Esay|]. split; [exact Esaid|].
  split; [exact (mqb_table lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj res kbs tab C HRD Hres Hnres Hsp Ha0
                   HNLK HTAB)|].
  split; [exact (mqb_policy lyc Sc W memc mdc _ lyj Sj Wj memj mdj regs regsj C Hsp HPOL)|].
  split; [exact Hsay|].
  split; [exact H00|].
  split; [exact (mqb_mf0 lyj Sj Wj memj mdj res HARj Hres HMF)|].
  split; [unfold MARK_LINE_MAX, AMF_BUFSIZ; lia|].
  split; [exact (mqb_blk lyj Sj Wj memj mdj regs regsj res HARj HC Hsp Hres)|].
  split; [rewrite Ha1; exact (mqb_arg lyc Sc W memc mdc lyj Sj Wj memj mdj regs nm C HRD HARG
                                (fun g n H => proj1 (HFIX g n H)) HNAME)|].
  split; [exact (mqb_name_ok lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj res nm C HRD Hres Hnres Hsp Ha0 Ha1
                   HARG (fun g n H => proj1 (HFIX g n H)) HNAME)|].
  exact (mqb_marks lyc Sc W memc mdc lyj Sj Wj memj mdj regs regsj res C Hres Hnres Hsp Ha0 HL HBLK).
Qed.

Lemma mqo_rsm_rd : forall lyc Sc (W : world SEGS) memc mdc (regs : bvmap 5 word) lyj Sj Wj memj mdj
    (regsj : bvmap 5 word),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  mark_quietly_apre_open SEGS B (ablocks B lyc Sc) regs (rdW W memc) ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  mqo_rel SEGS B (spZ regs) lyc Sc W memc lyj Sj Wj memj mdj ->
  aarg regsj 0 = aarg regs 0 -> aarg regsj 1 = aarg regs 1 -> spZ regsj = spZ regs ->
  forall a, amk_rd SEGS regsj (rdW Wj memj) a -> akb SEGS B lyj Sj (spZ regsj - REAC_SERVED_MARK_AK) (spZ regsj) a.
Proof.
  intros lyc Sc W memc mdc regs lyj Sj Wj memj mdj regsj HAR HC HP HRD HREL Ha0 Ha1 Hsp a Ha.
  assert (C : mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj) by exact (conj HAR (conj HC HREL)).
  destruct HP as (_ & HCX & _).
  destruct HCX as (kbs & tab & nm & HL & HFIX & HNLK & HERR & _ & _ & _ & _ & HTAB & _ & HARG & HNAME & _).
  rewrite Hsp. apply (mqb_akb_conv lyc Sc W memc mdc _ lyj Sj Wj memj mdj a C). apply HRD.
  unfold mark_quietly_ard, amk_rd.
  destruct Ha as [H1|[H2|H3]].
  - left. destruct H1 as (Hn & s' & C' & Hr). rewrite Ha1 in Hn, C', Hr.
    destruct nm as [s|]; [|exfalso; exact (Hn HARG)].
    pose proof (mqb_arg lyc Sc W memc mdc lyj Sj Wj memj mdj regs (Some s) C HRD HARG
      (fun g n H => proj1 (HFIX g n H)) HNAME) as [_ Cj].
    pose proof (mq_cstr_unique _ _ s' s C' Cj) as E. subst s'.
    split; [exact Hn|]. exists s. split; [exact (proj2 HARG) | exact Hr].
  - right; left. exact H2.
  - right; right. destruct H3 as (bs & tab' & i & n2 & ix & p & Hn' & Hi' & Ht & Hp & Hc & Hr).
    pose proof HNLK as (Hn & _ & _ & _ & _ & Hi & _).
    pose proof (mqb_nlk_at lyc Sc W memc mdc _ lyj Sj Wj memj mdj kbs C Hn) as Hn2.
    pose proof (anlk_at_unique SEGS _ _ _ _ Hn' Hn2) as Eb. subst bs.
    pose proof (mqb_iftab lyc Sc W memc mdc _ lyj Sj Wj memj mdj kbs tab C Hi
      (mqb_tab_mb lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab C HRD HNLK HTAB
         (fun g n H => proj2 (HFIX g n H)))) as Hi2.
    pose proof (mq_iftab_unique _ _ _ _ _ Hi' Hi2) as Et. subst tab'.
    pose proof Hi as (_ & L80 & EI).
    destruct (EI i n2 ix Ht) as (_ & p0 & P0 & _ & C0 & _).
    assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; congruence).
    assert (P0' : au64_at SEGS (rdW Wj memj) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0).
    { apply (mq_vm_tr (rdW W memc) (rdW Wj memj) _ 8 p0); [|exact P0]. intros k Hk.
      apply (mqb_gnl_mb lyc Sc W memc mdc _ lyj Sj Wj memj mdj _ C). unfold NK_IF_NAME, NK_SIZE in *. lia. }
    pose proof (mq_cstr_rng _ p n2 Hc) as Q1. pose proof (mq_cstr_rng _ p0 n2 C0) as Q0.
    assert (Ep : p = p0) by (apply (mq_vm_unique _ _ 8 p p0 Hp P0'); change (8 * Z.of_nat 8) with 64; lia).
    subst p0. unfold amk_tab_rd. exists kbs, tab, i, n2, ix, p.
    split; [exact Hn|]. split; [exact Hi|]. split; [exact Ht|]. split; [exact P0|]. split; [exact C0 | exact Hr].
Qed.

Lemma mqo_q : forall res lyc Sc (W : world SEGS) memc mdc (regs : bvmap 5 word) lyj Sj Wj memj mdj
    (regsj : bvmap 5 word) ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  mark_quietly_apre_open SEGS B (ablocks B lyc Sc) regs (rdW W memc) ->
  (forall a, mark_quietly_ard SEGS regs (rdW W memc) a ->
     akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  mqo_rel SEGS B (spZ regs) lyc Sc W memc lyj Sj Wj memj mdj ->
  In (res, AMF_BLOCK) (ablocks B lyj Sj) -> ~ In (res, AMF_BLOCK) (ablocks B lyc Sc) ->
  au64_at SEGS (rdW Wj memj) LA_G_SINK res -> au64_at SEGS (rdW Wj memj) LA_G_SAY res ->
  au64_at SEGS (rdW Wj memj) LA_OFL_HEAD res ->
  LinkMfDefs.amf_k SEGS link_amf (rdW Wj memj) res 0 ->
  aarg regsj 0 = aarg regs 0 -> aarg regsj 1 = aarg regs 1 -> spZ regsj = spZ regs ->
  wle Wj W2 ->
  akept SEGS B lyj Sj Wj memj W2 mem2 (spZ regsj - REAC_SERVED_MARK_AK) (spZ regsj)
    (fun a => inFP (reac_served_mark_awr res regsj (rdW Wj memj)) a) ->
  reac_served_mark_apost SEGS res regsj (rdW Wj memj) regs2 (rdW W2 mem2) ->
  Permutation (ablocks B ly2 S2) (ablocks B lyj Sj) ->
  Permutation (ablocks B lyj Sj) (ablocks B lyc Sc ++ [(res, AMF_BLOCK)]) ->
  mark_quietly_aposta_open SEGS regs (rdW W memc) regs2 (rdW W2 mem2) (ablocks B lyc Sc) (ablocks B ly2 S2).
Proof.
  intros res lyc Sc W memc mdc regs lyj Sj Wj memj mdj regsj ly2 S2 W2 regs2 mem2
    HAR HC HP HRD HREL Hres Hnres Hsink Hsay Hofl HMF Ha0 Ha1 Hsp Hle2 HKP HQ HP2 HPj.
  assert (C : mqb_ctx lyc Sc W memc mdc (spZ regs) lyj Sj Wj memj mdj) by exact (conj HAR (conj HC HREL)).
  destruct HP as (_ & HCX & _).
  destruct HCX as (kbs & tab & nm & HL & HFIX & HNLK & _ & _ & _ & _ & _ & HTAB & _ & HARG & HNAME & HBLK).
  pose proof HREL as (HARj & _ & _ & _ & Hbl & _).
  pose proof (blk_off_imgP B lyj Sj Wj memj mdj res AMF_BLOCK HARj Hres) as Hoff.
  change (req_size AMF_BLOCK) with AMF_BLOCK in Hoff. unfold off_img in Hoff.
  pose proof (AF0m.ts_errno B TB) as He.
  pose proof mq_word_facts as (I1 & I2 & I3 & O1 & O2 & O3).
  assert (Hm : aarg regsj 0 <> 0 -> YCbq.off_img (aarg regsj 0) MK_SIZE)
    by (rewrite Ha0; intros H0; exact (proj2 (HL H0))).
  assert (KW : forall lo v, (lo = LA_G_SINK \/ lo = LA_G_SAY \/ lo = LA_OFL_HEAD) ->
    existsb (relro_in_seg lo (lo + 8)) AB1v.tfibsegs = true ->
    forallb (fun r => (lo + 8 <=? fst r) || (fst r + snd r <=? lo)) AF0m.Tfib_owned_static = true ->
    au64_at SEGS (rdW Wj memj) lo v -> au64_at SEGS (rdW W2 mem2) lo v).
  { intros lo v Hlo Hi Ho Hv.
    apply (mq_word_kept B TB HSEGS lyj Sj Wj memj W2 mem2 _ _ _ lo v HKP Hi Ho).
    - rewrite He. unfold LA_G_SINK, LA_G_SAY, LA_OFL_HEAD, AF0m.TFIB_ERRNO in *. lia.
    - apply (mq_not_wr res regsj _ lo Hoff Hm);
        unfold LA_G_NL, NK_N_SENT, YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_SINK, LA_G_SAY, LA_OFL_HEAD in *; lia.
    - exact Hv. }
  assert (H00 : res <> 0).
  { destruct (al_blocks _ _ LAWS lyj Sj Wj memj mdj _ _ HARj Hres) as (_ & H4 & _). lia. }
  destruct HQ as (Q1 & Q2 & Q3).
  exists res. split; [exact H00|].
  split; [exact (KW _ _ (or_introl eq_refl) I1 O1 Hsink)|].
  split; [exact (KW _ _ (or_intror (or_introl eq_refl)) I2 O2 Hsay)|].
  split; [exact (KW _ _ (or_intror (or_intror eq_refl)) I3 O3 Hofl)|].
  split; [exact (Permutation_trans HP2 HPj)|].
  split.
  - destruct (Q1 0 (mqb_mf0 lyj Sj Wj memj mdj res HARj Hres HMF)) as (k' & Hk' & Hmf).
    exists k'. split; [lia | exact Hmf].
  - pose proof HNLK as (Hn & _ & _ & _ & _ & Hi & _).
    pose proof (mqb_tab_mb lyc Sc W memc mdc lyj Sj Wj memj mdj regs kbs tab C HRD HNLK HTAB
      (fun g n H => proj2 (HFIX g n H))) as TM.
    split.
    + intros H0. rewrite <- Ha0 in H0. destruct (Q2 H0) as (R & N). split; [exact R|].
      intros bs Hb. apply N. exact (mqb_nlk_at lyc Sc W memc mdc _ lyj Sj Wj memj mdj bs C Hb).
    + intros H0 bs tab' nm' gbs Hb Ht Ha Hmk.
      pose proof (anlk_at_unique SEGS _ _ _ _ Hb Hn) as Eb. subst bs.
      pose proof (mq_iftab_unique _ _ _ _ _ Ht Hi) as Et. subst tab'.
      pose proof (mq_sarg_unique _ _ _ _ Ha HARG) as En. subst nm'.
      assert (H0j : aarg regsj 0 <> 0) by (rewrite Ha0; exact H0).
      destruct (HL H0) as [Hin Htop].
      assert (Hmk' : amarks_at SEGS (rdW Wj memj) (aarg regsj 0) gbs)
        by (rewrite Ha0; exact (mqb_marks_at lyc Sc W memc mdc _ lyj Sj Wj memj mdj _ gbs C Hin Htop Hmk)).
      assert (Ha' : astr_arg SEGS (rdW Wj memj) (aarg regsj 1) nm)
        by (rewrite Ha1; exact (mqb_arg lyc Sc W memc mdc lyj Sj Wj memj mdj regs nm C HRD HARG
                                  (fun g n H => proj1 (HFIX g n H)) HNAME)).
      pose proof (Q3 H0j kbs tab nm gbs (mqb_nlk_at lyc Sc W memc mdc _ lyj Sj Wj memj mdj kbs C Hn)
        (mqb_iftab lyc Sc W memc mdc _ lyj Sj Wj memj mdj kbs tab C Hi TM) Ha' Hmk') as R.
      rewrite Ha0 in R. exact R.
Qed.
End s.

Print Assumptions mqo_rsm_pre.
Print Assumptions mqo_rsm_rd.
Print Assumptions mqo_q.
