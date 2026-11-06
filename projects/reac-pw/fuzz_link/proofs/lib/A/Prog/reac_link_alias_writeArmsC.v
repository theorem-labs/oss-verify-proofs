(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module paths and module names changed; 558 of its 655 lines of code are new or changed and 494 lines of the source are left out. *)
(* reac_link_alias_write on image A: the kit of the two calls of the stretch +0x1a8 .. +0x1f0 (wrapper_strlen at
   +0x1cc, fuzz_if_nametoindex at +0x1e8), for the piece `aw_mid_obl` of lib/A/Prog/reac_link_alias_writeDefs.v.

   - the bytes after a heap block, to the next multiple of 16 of its size, are visible at every AR state
     (`awc_blk_tail_vis`; srm_blk_tail_vis16 of lib/A/Prog/reac_served_markKitAt.v,
     with req_size in place of the size so a malloc(0) block is covered);
   - THE ALIAS'S SLACK AT A CUT (`awc_tail_cut`): the bytes after the alias's NUL to the end of its 8-byte granule,
     which the contract's Pre shows at the call's memory, are visible at a cut's memory. The NUL is a read-set byte
     (`akb`), and each of akb's four places keeps the granule visible: the real stack row by akept's presence
     clauses, a heap block by AR's block law and the block's tail, a side frame by AR's frame law, and the image by
     akept's image clause or, where the granule meets the runtime's statics or errno, by the image's file bytes
     (computed: every segment ends on a multiple of 8, and every granule of a static or of errno that starts
     inside a granule is file-backed);
   - the premises of RtString.astrlen_realizes at a cut (`awc_strlen_pre`), from the Pre's achk, apart_frame and
     slack of the alias;
   - the invariant the stretch carries across a call (`awc_inv`: aw_base without the registers), with the step
     lemma for a callee that writes only below sp1, and the fake kernel's views at a later memory. They are the
     algebra of lib/A/Prog/reac_link_alias_writeSend.v (aws_inv, aws_inv_step, aws_tab_kept, ...) restated here:
     that file's lemmas carry its Section's nl_talk contract and SEND-cut strings as arguments, which this piece
     does not have.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_if_nametoindex_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeArmsA reac_link_alias_writeArmsB.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeSendA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall LinkWalkZsh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the ArmsB lemmas this file applies, with their closed signatures *)
About aw_rd_kept. About aw_shadow_at. About aw_base_jx. About aw_jc. About aw_ar_of_jx. About AW_FPOS.
About aw_base_kept. About aw_base_wit. About aw_pf_at. About aw_base_step_nomem.

(* ==========================================================================
   1. The bytes after a heap block, to the next multiple of 16 of its size, are visible at every AR state
   ========================================================================== *)
Section tv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma awc_chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
  In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
  intros ly S k Hk. unfold ajunk. right. right.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma awc_chunk_room_mod16 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
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

Lemma awc_blk_tail_vis : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= a < p + round_up (req_size n) 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (awc_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (CN : ck_n k = req_size n) by (unfold ck_n; congruence).
  assert (RS : 1 <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  replace (req_size (ck_req k)) with (req_size n) in HX by congruence.
  assert (RU : round_up (req_size n) 16 <= ck_extent k - ck_rz k) by (apply round_up_le; [lia | lia | exact R16]).
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (awc_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + req_size n) + (a - (ck_base B ly k + (ck_rz k + req_size n)))) by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
End tv.

(* ==========================================================================
   2. Views, presence and the image's file bytes
   ========================================================================== *)
Definition awc_rom_b (lo hi : Z) : bool :=
  forallb (fun i => match seg_rom tfibsegs (Z_to_bv 64 (lo + Z.of_nat i)) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat (hi - lo))).

(* the image's segments end on multiples of 8 (they are [0x10000, 0x31000), [0x31000, 0xa1000), [0xa1000, 0xa3000)
   and [0xa3000, 0x654000)) *)
Lemma awc_seg_ends : forallb (fun sg => (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) mod 8 =? 0) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* every runtime static that starts inside a granule has file bytes from its start to the granule's end *)
Lemma awc_owned_rom : forallb (fun r => if fst r mod 8 =? 0 then true else awc_rom_b (fst r) (fst r - fst r mod 8 + 8))
  Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

(* errno's four bytes, the second half of a granule, have file bytes *)
Lemma awc_errno_rom : awc_rom_b TFIB_ERRNO (TFIB_ERRNO + 4) = true.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
(* the read-only window is image bytes: discharged in lib/A/Prog/reac_link_alias_write.v (aw_relro_img_tfib) *)
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.

Lemma awc_vis_rom : forall (H : word -> bool) m x, seg_rom SEGS (Z_to_bv 64 x) <> None -> aview SEGS H m x <> None.
Proof.
  intros H m x Hr. unfold aview, mbyte.
  destruct (mrestrict H m (Z_to_bv 64 x)) as [b|]; cbn [option_map]; [discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 x)) as [b|] eqn:E; cbn [option_map]; [discriminate | exfalso; first [exact (Hr E) | exact (Hr eq_refl)]].
Qed.

Lemma awc_present_of_mbyte : forall (H : word -> bool) m x,
  mbyte SEGS (mrestrict H m) x <> None -> seg_rom SEGS (Z_to_bv 64 x) = None -> apresent H m x.
Proof.
  intros H m x Hm Hr. unfold apresent. revert Hm. unfold mbyte, mrestrict.
  destruct (H (Z_to_bv 64 x)) eqn:EH.
  - rewrite Hr. intros Hm. exfalso. exact (Hm eq_refl).
  - destruct (m (Z_to_bv 64 x)) as [b|] eqn:Em.
    + intros _. split; [reflexivity | exists b; reflexivity].
    + rewrite Hr. intros Hm. exfalso. exact (Hm eq_refl).
Qed.

Lemma awc_vis_present : forall (H : word -> bool) m x, apresent H m x -> aview SEGS H m x <> None.
Proof. intros H m x (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

Lemma awc_mbyte_vis : forall (H : word -> bool) m x, mbyte SEGS (mrestrict H m) x <> None -> aview SEGS H m x <> None.
Proof.
  intros H m x Hm. unfold aview.
  destruct (mbyte SEGS (mrestrict H m) x) eqn:E; cbn [option_map]; [discriminate | exfalso; first [exact (Hm E) | exact (Hm eq_refl)]].
Qed.

Lemma awc_rom_vis : forall lo hi a (H : word -> bool) m, awc_rom_b lo hi = true -> lo <= a < hi ->
  aview SEGS H m a <> None.
Proof.
  intros lo hi a H m Hb Ha. apply awc_vis_rom. rewrite HSEGS.
  unfold awc_rom_b in Hb. rewrite forallb_forall in Hb.
  assert (Hin : In (Z.to_nat (a - lo)) (seq 0 (Z.to_nat (hi - lo)))) by (apply in_seq; lia).
  specialize (Hb (Z.to_nat (a - lo)) Hin). cbv beta in Hb.
  rewrite Z2Nat.id in Hb by lia. replace (lo + (a - lo)) with a in Hb by lia.
  destruct (seg_rom tfibsegs (Z_to_bv 64 a)) eqn:E; [discriminate|].
  exfalso. revert Hb. try rewrite E. cbn. discriminate.
Qed.

(* a C string the walk's reader shows is the runtime's C string *)
Lemma awc_astr_of_acstr : forall (W : world SEGS) m p s,
  acstr_at SEGS (mrestrict (w_H W) m) p s -> RtDefs.astr_at SEGS W m p s.
Proof.
  intros W m p s ((_ & _ & Hb) & Hn). split; [|exact Hn].
  intros i Hi. unfold aview. rewrite (Hb i Hi). erewrite nth_error_nth' by exact Hi.
  reflexivity.
Qed.

(* the in-segment half of arodata_okP is the runtime's read-only view *)
Lemma awc_rt_rom : forall (W : world SEGS) m,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) m) -> RtDefs.rt_rom_view SEGS B W m.
Proof. intros W m Hro a Hrom Hno Herr. exact (Hro a (or_introl Hrom) Hno Herr). Qed.

(* a byte of the image past a byte e of the image that is outside the runtime's statics and errno, inside e's
   granule, is visible wherever the image bytes outside the statics and errno are kept *)
Lemma awc_img_tail : forall e x (H H0 : word -> bool) m m0,
  in_img SEGS e -> ~ Exists (in_zr e) (as_owned_static B) -> ~ (as_errno B <= e < as_errno B + 4) ->
  e < x < e - e mod 8 + 8 ->
  (in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     aview SEGS H m x = aview SEGS H0 m0 x) ->
  aview SEGS H0 m0 x <> None ->
  aview SEGS H m x <> None.
Proof.
  intros e x H H0 m m0 Hie Hoe Hee Hx Hkeep Hv0.
  assert (Hix : in_img SEGS x).
  { destruct Hie as (sg & Hsg & H1). exists sg. split; [exact Hsg|].
    pose proof awc_seg_ends as SE. rewrite <- HSEGS in SE. rewrite forallb_forall in SE.
    specialize (SE sg Hsg). apply Z.eqb_eq in SE. lia. }
  rewrite (ts_errno B TB) in Hee, Hkeep. rewrite (ts_owned B TB) in Hoe, Hkeep.
  destruct (Z_lt_le_dec x TFIB_ERRNO) as [Lt1|Le1];
    [|destruct (Z_lt_le_dec x (TFIB_ERRNO + 4)) as [Lt2|Le2]].
  2:{ exact (awc_rom_vis TFIB_ERRNO (TFIB_ERRNO + 4) x H m awc_errno_rom ltac:(lia)). }
  - destruct (existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) Tfib_owned_static) eqn:Ex.
    + apply existsb_exists in Ex as (r & Hr & Hb). apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      assert (Hne : ~ (fst r <= e < fst r + snd r)).
      { intros He. apply Hoe. apply Exists_exists. exists r. split; [exact Hr | unfold in_zr; exact He]. }
      pose proof awc_owned_rom as OR. rewrite forallb_forall in OR. specialize (OR r Hr).
      assert (E8 : fst r mod 8 <> 0) by lia. apply Z.eqb_neq in E8. rewrite E8 in OR.
      exact (awc_rom_vis (fst r) (fst r - fst r mod 8 + 8) x H m OR ltac:(lia)).
    + rewrite (Hkeep Hix); [exact Hv0| |lia].
      intros Hex. apply Exists_exists in Hex as (r & Hr & Hin). unfold in_zr in Hin.
      assert (Hf : existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) Tfib_owned_static = true).
      { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff.
        split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      rewrite Hf in Ex. discriminate.
  - destruct (existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) Tfib_owned_static) eqn:Ex.
    + apply existsb_exists in Ex as (r & Hr & Hb). apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      assert (Hne : ~ (fst r <= e < fst r + snd r)).
      { intros He. apply Hoe. apply Exists_exists. exists r. split; [exact Hr | unfold in_zr; exact He]. }
      pose proof awc_owned_rom as OR. rewrite forallb_forall in OR. specialize (OR r Hr).
      assert (E8 : fst r mod 8 <> 0) by lia. apply Z.eqb_neq in E8. rewrite E8 in OR.
      exact (awc_rom_vis (fst r) (fst r - fst r mod 8 + 8) x H m OR ltac:(lia)).
    + rewrite (Hkeep Hix); [exact Hv0| |lia].
      intros Hex. apply Exists_exists in Hex as (r & Hr & Hin). unfold in_zr in Hin.
      assert (Hf : existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) Tfib_owned_static = true).
      { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff.
        split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      rewrite Hf in Ex. discriminate.
Qed.

(* ---- generic journal facts (reac_link_alias_writeSend.v aws_aj_ar, aws_aj_row) ---- *)
Lemma awc_aj_ar : forall G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k -> AR SEGS B ly' S' W' mem' md'.
Proof. intros G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _). exact (proj1 HJ). Qed.

Lemma awc_aj_row : forall G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
  0 <= STK /\ 0 <= XO /\ alloc_ceiling <= sp0 - STK /\ sp0 + XO <= 2 ^ 47.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k (HSTK & HXO & (memS & HJ & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.

Lemma awc_ro_img : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hb) | Hr]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG a Hr)]. Qed.

Lemma awc_arodata_call : forall lyc Sc (W : world SEGS) m W2 m2 slo shi (E : Z -> Prop),
  akept SEGS B lyc Sc W m W2 m2 slo shi E ->
  (forall a, E a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) m) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) m2).
Proof.
  intros lyc Sc W m W2 m2 slo shi E (_ & _ & K3 & _) HE Hro a Ha Ho He.
  rewrite (K3 a (awc_ro_img a Ha) Ho He (fun HEa => HE a HEa Ha)). exact (Hro a Ha Ho He).
Qed.

Lemma awc_gnl_writable : forall m a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS m a.
Proof. rewrite HSEGS. intros m a Ha. apply LA_G_NL_writable. unfold NK_SIZE in Ha. exact Ha. Qed.

(* g_nl is an image byte outside the runtime's statics and errno (a computation at the image's segments) *)
Lemma awc_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB). split; [|split].
  - assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? LA_G_NL) &&
        (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true)
      by (vm_compute; reflexivity).
    apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_true_iff in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
  - assert (Hb : forallb (fun r => (LA_G_NL + NK_SIZE <=? fst r) || (fst r + snd r <=? LA_G_NL))
        Tfib_owned_static = true) by (vm_compute; reflexivity).
    intros Hex. apply Exists_exists in Hex as (r & Hin & Hr). rewrite forallb_forall in Hb. specialize (Hb r Hin).
    apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; unfold in_zr in Hr; lia.
  - assert (He : LA_G_NL + NK_SIZE <= TFIB_ERRNO) by (vm_compute; congruence). lia.
Qed.

Lemma awc_wr_eq : forall (cx : awcx) a, inFP (aw_wr cx) a <-> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4.
Proof.
  intros cx a. unfold aw_wr, reac_link_alias_write_awr. split.
  - intros (r & [<- | []] & H). exact H.
  - intros H. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact H].
Qed.

Lemma awc_pres : forall (R R2 : bvmap 5 word) (r : Z) v, aregs_preserved R R2 -> acallee_saved r ->
  getr R (Z_to_bv 5 r) = v -> getr R2 (Z_to_bv 5 r) = v.
Proof. intros R R2 r v P Hr H. rewrite (P r Hr). exact H. Qed.

Lemma awc_aarg : forall (R : bvmap 5 word) (i : Z) v, getr R (Z_to_bv 5 (10 + i)) = w64 v -> 0 <= v < 2 ^ 64 ->
  aarg R i = v.
Proof. intros R i v H Hv. unfold aarg, argZ. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

Lemma awc_set_fs_set_fs : forall f g S, set_fs f (set_fs g S) = set_fs f S.
Proof. intros f g S. reflexivity. Qed.

(* ==========================================================================
   3. The call's context: its window, the frame, the invariant the stretch carries
   ========================================================================== *)
Section c.
Variable cx : awcx.
Variable fpos : Z.
#[local] Notation F := (aw_F cx fpos).
#[local] Notation SH := (aw_SH cx fpos).
#[local] Notation Eacc := (fun a => aw_E cx a \/ aside_rng (aw_lyc cx) AW_CID fpos a).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
     (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx) ly S W m md (aw_k cx)).

Hypothesis HPRE : aw_pre SK B cx.
Hypothesis HNIN : ~ In (AW_CID, fpos) (frames (aw_Sc cx)).
Hypothesis HS1 : exists S1 W1 mem1 md1, AR SEGS B (aw_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (AW_CID, fpos) :: frames (aw_Sc cx) /\ ablocks B (aw_lyc cx) S1 = ablocks B (aw_lyc cx) (aw_Sc cx).

Lemma awc_pre_j : ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
  (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) (aw_own cx)
  (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) (aw_k cx).
Proof. exact (proj1 (proj1 HPRE)). Qed.

Lemma awc_pre_g : gx_ok SEGS B (aw_G cx).
Proof. exact (proj1 (proj2 (proj1 HPRE))). Qed.

Lemma awc_pre_ar : AR SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx).
Proof. exact (awc_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ awc_pre_j). Qed.

Lemma awc_win : aw_sp cx mod 16 = 0 /\ alloc_ceiling <= aw_sp0 cx - aw_STK cx /\
  aw_sp0 cx - aw_STK cx <= aw_sp cx - 8560 /\ aw_sp cx <= aw_sp0 cx /\ aw_sp0 cx <= 2 ^ 47 /\
  aw_sp cx - 112 <= aw_sp1 cx <= aw_sp cx - 96 /\ aw_sp1 cx mod 32 = 0 /\ aw_sp1 cx mod 16 = 0.
Proof.
  destruct HPRE as ((HJ & _ & _ & _ & _ & _ & _ & H16 & Hlo & Hhi & _) & _ & _).
  destruct (awc_aj_row _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (R1 & R2 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & _).
  rewrite REAC_LINK_ALIAS_WRITE_AK_val in Hlo.
  fold (aw_sp cx) in H16, Hlo, Hhi.
  destruct (sp1_facts (aw_sp cx - 96) ltac:(lia) ltac:(rewrite Zminus_mod, H16; reflexivity)) as (S1 & S2 & S3).
  unfold aw_sp1, AW_FRAME. repeat split; lia.
Qed.

Lemma awc_F : 4096 <= F /\ F + 512 <= alloc_ceiling /\ F mod 64 = 0 /\ in_app F 512 /\ off_img F 512 /\
  0 <= fpos < fs_frames AW_CID.
Proof.
  destruct HS1 as (S1 & W1 & mem1 & md1 & HAR & Hfr & _).
  assert (Hin : In (AW_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ S1 W1 mem1 md1 _ _ HAR Hin) as (H1 & H2 & H3).
  destruct (frame_al64 SEGS B _ S1 W1 mem1 md1 _ _ HAR Hin) as (H4 & _).
  pose proof (frm_off_imgP B _ S1 W1 mem1 md1 _ _ HAR Hin) as H5.
  destruct HAR as [M _]. destruct (frame_facts B _ S1 _ _ _ M Hin) as (_ & H6 & _).
  change (fs_frame_bytes AW_CID) with 512 in H2, H3, H5. unfold aw_F.
  exact (conj H1 (conj H2 (conj H4 (conj H3 (conj H5 H6))))).
Qed.

Lemma awc_SH_val : SH = SHADOW_OFF + F / 8 /\ SH mod 8 = 0 /\ SHADOW_OFF + 512 <= SH /\ SH + 64 <= kHighMemBeg /\
  SH + 64 <= alloc_ceiling.
Proof.
  destruct awc_F as (H1 & H2 & H3 & _). pose proof asan_consts as ((C1a & C1b) & _).
  unfold aw_SH. fold (aw_F cx fpos). unfold SHADOW_OFF, kHighMemBeg. repeat split; lia.
Qed.

(* the facts of the contract's Pre the stretch reads, at the call *)
Lemma awc_pre_ajw : forall a, inFP (aw_wr cx) a ->
  ajw B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx) (aw_ly cx) (aw_S cx)
    (aw_lyc cx) (aw_Sc cx) (aw_own cx) a.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.

Lemma awc_pre_nro : forall a, inFP (aw_wr cx) a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.

Lemma awc_pre_misc : getr (aw_regs cx) 3 = w64 (as_gp B) /\ getr (aw_regs cx) 4 = w64 (as_tp B) /\
  st_nev (aw_S cx) + aw_k cx + 0 <= EV_MAX /\ aside_room (aw_Sc cx) REAC_LINK_ALIAS_WRITE_ASIDE.
Proof.
  destruct HPRE as ((_ & _ & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hnev & Hside & _) & _).
  exact (conj Hgp (conj Htp (conj Hnev Hside))).
Qed.

Lemma awc_spZ : forall (R : bvmap 5 word), getr R 2 = w64 (aw_sp1 cx) -> spZ R = aw_sp1 cx.
Proof.
  intros R H. destruct awc_win as (_ & Wc & Wlo & Whi & W47 & S1 & _). pose proof asan_consts as ((C1a & C1b) & _).
  unfold spZ. rewrite H. apply unsigned_lit_small. lia.
Qed.

(* THE INVARIANT the stretch carries: aw_base without the registers and the machine state's shape *)
Definition awc_inv (ly : alayout) (S : astate) (W : world SEGS) (m : word -> option byte) (md : Model) : Prop :=
  AJ ly S W m md /\
  frames S = (AW_CID, fpos) :: frames (aw_Sc cx) /\
  (exists fs, S = set_fs fs (aw_Sc cx)) /\
  Permutation (ablocks B ly S) (ablocks B (aw_lyc cx) (aw_Sc cx)) /\
  (forall c q, frame_addr ly c q = frame_addr (aw_lyc cx) c q) /\
  rdword (aview SEGS (w_H W) m) (aw_sp cx - 8) = Some (raZ (aw_regs cx)) /\
  (forall j, 0 <= j < 9 -> rdword (aview SEGS (w_H W) m) (aw_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr (aw_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  rdword (aview SEGS (w_H W) m) (F + AW_FLAGPTR) = Some (aw_FL cx fpos) /\
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc /\
  m_fds md = m_fds (aw_mdc cx) /\ m_fs md = m_fs (aw_mdc cx) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) m).

Lemma awc_inv_of_base : forall ly S W ms md, aw_base SK B cx fpos ly S W ms md -> awc_inv ly S W (ms_mem ms) md.
Proof.
  intros ly S W ms md (_ & _ & _ & _ & _ & HJ & Hfr & _ & Hfs & Hperm & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & Hra & Hsv & Hfl & _ & _ & HK & Hfds & Hfs' & Hro).
  unfold awc_inv. repeat (split; [assumption|]). assumption.
Qed.

(* the frame and its shadow are present at every AR state where the frame is live *)
Lemma awc_frame_present : forall ly S (W : world SEGS) m md,
  AR SEGS B ly S W m md -> In (AW_CID, fpos) (frames S) -> frame_addr ly AW_CID fpos = F ->
  (forall a, F <= a < F + AW_FB -> apresent (w_H W) m a) /\
  (forall a, SH <= a < SH + AW_SHN -> apresent (w_H W) m a).
Proof.
  intros ly S W m md HAR Hin Hfa.
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & HF & HS).
  rewrite Hfa in HF, HS. change (fs_frame_bytes AW_CID) with 512 in HF, HS. change (512 / 8) with 64 in HS.
  split.
  - intros a Ha. exact (proj1 (HF a Ha)).
  - intros a Ha. unfold aw_SH in Ha. fold (aw_F cx fpos) in Ha.
    replace a with (shadow_addr F + (a - shadow_addr F)) by ring.
    apply (proj1 (HS (a - shadow_addr F) ltac:(unfold shadow_addr; unfold AW_SHN in Ha; lia))).
Qed.

Lemma awc_base_of_inv : forall ly S W ms md,
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs ->
  ms_fcsr ms = fp_csr ->
  getr (ms_regs ms) 2 = w64 (aw_sp1 cx) -> getr (ms_regs ms) 9 = w64 (aw_sp1 cx) ->
  getr (ms_regs ms) 8 = w64 (aw_sp cx) ->
  getr (ms_regs ms) 18 = w64 SH -> getr (ms_regs ms) 19 = w64 F -> getr (ms_regs ms) 24 = w64 F ->
  getr (ms_regs ms) 3 = getr (aw_regs cx) 3 -> getr (ms_regs ms) 4 = getr (aw_regs cx) 4 ->
  getr (ms_regs ms) 25 = getr (aw_regs cx) 25 -> getr (ms_regs ms) 26 = getr (aw_regs cx) 26 ->
  getr (ms_regs ms) 27 = getr (aw_regs cx) 27 ->
  awc_inv ly S W (ms_mem ms) md -> aw_base SK B cx fpos ly S W ms md.
Proof.
  intros ly S W ms md Hr Hs Hrom Hf Hc R2 R9 R8 R18 R19 R24 R3 R4 R25 R26 R27
    (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro).
  pose proof (awc_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  destruct (awc_frame_present ly S W (ms_mem ms) md HAR Hin (Hfa AW_CID fpos)) as [HFp HSp].
  unfold aw_base. cbv zeta. repeat (split; [assumption|]). assumption.
Qed.

(* ---- a step of the walk's own code or of a runtime call that writes only below sp1, in the request's part of
   F, or in F's shadow: the invariant at the new memory (reac_link_alias_writeSend.v aws_inv_step) ---- *)
Lemma awc_inv_step : forall ly S W m md m' md' (X : Z -> Prop),
  awc_inv ly S W m md ->
  AJ ly S W m' md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (F + 32 <= a < F + 324) \/
     (SH <= a < SH + 64)) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  awc_inv ly S W m' md'.
Proof.
  intros ly S W m md m' md' X (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro)
    HJ' UN HX Hpres Efds Efs.
  destruct awc_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & _).
  destruct awc_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct awc_SH_val as (SH1 & SH2 & SH3 & SH4 & SH5).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK8560.
  assert (Hstk : forall a, aw_sp cx - 80 <= a < aw_sp cx -> ~ X a).
  { intros a Ha HXa. destruct (HX a HXa) as [H|[H|H]]; lia. }
  assert (Hflag : forall a, F + 504 <= a < F + 512 -> ~ X a).
  { intros a Ha HXa. destruct (HX a HXa) as [H|[H|H]]; [lia | lia |].
    unfold in_app, ASAN_CEIL in F4. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  split; [exact HJ'|]. split; [exact Hfr|]. split; [exact Hfs|]. split; [exact Hperm|]. split; [exact Hfa|].
  split.
  { rewrite <- Hra. apply aws_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { intros j Hj. rewrite <- (Hsv j Hj). apply aws_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { rewrite <- Hfl. apply aws_rdword_eq. intros i Hi. unfold AW_FLAGPTR in *. apply UN; [lia | apply Hflag; lia]. }
  split.
  { eapply (akept_step SK SEGS B LAWS pa_segs_low (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) W m W m'
      (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc Eacc X awc_pre_ar);
      [lia | lia | exact HK | exact UN | intros a _ Ha; exact (Hpres a Ha) | intros a Ha; exact Ha |].
    intros a HXa. destruct (HX a HXa) as [H|[H|H]].
    - right. lia.
    - left. right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes AW_CID) with 512.
      fold (aw_F cx fpos). lia.
    - left. right. right. left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes AW_CID / 8) with 64.
      unfold aw_SH in H. fold (aw_F cx fpos). unfold shadow_addr. lia. }
  split; [rewrite Efds; exact Hfds|]. split; [rewrite Efs; exact Hfs'|].
  apply (aws_arodata_eq SEGS PCAP_RLO PCAP_RHI B _ _ Hro). intros a Hro_a.
  pose proof (pa_img_range a (awc_ro_img a Hro_a)) as Hir.
  apply UN; [unfold pcap_img_end, YImgTop.IMG_TOP in Hir; lia|]. intros HXa.
  destruct (HX a HXa) as [H|[H|H]]; unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5;
    unfold pcap_img_end, YImgTop.IMG_TOP, SHADOW_OFF in *; lia.
Qed.

(* ---- the read set and g_nl, kept by the walk's akept ---- *)
Lemma awc_kept_akb : forall (W : world SEGS) m a,
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc ->
  akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a -> ~ aw_E cx a ->
  aview SEGS (w_H W) m a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a.
Proof.
  intros W m a HK Hb HnE.
  destruct awc_F as (_ & _ & _ & _ & _ & Hfp).
  eapply (akept_akb_gx SK SEGS B); [exact awc_pre_j | exact HK | exact Hb |].
  intros [H | H]; [exact (HnE H) |].
  exact (akb_not_side SK SEGS B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AW_CID fpos a awc_pre_j
           ltac:(unfold AW_CID; lia) Hfp HNIN Hb H).
Qed.

Lemma awc_kept_gnl : forall (W : world SEGS) m a,
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc ->
  LA_G_NL + NK_N_SENT + 4 <= a < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W) m a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a.
Proof.
  intros W m a (_ & _ & K3 & _) Ha.
  destruct (awc_gnl_img a ltac:(unfold NK_N_SENT, NK_SIZE in *; lia)) as (Hi & Ho & He).
  apply (K3 a Hi Ho He). intros [H | H].
  - unfold aw_E in H. apply awc_wr_eq in H. lia.
  - destruct HS1 as (S1 & W1 & mem1 & md1 & HAR & Hfr & _).
    assert (Hin : In (AW_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
    exact (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ S1 W1 mem1 md1 _ _ a HAR Hin H) Hi).
Qed.

(* g_nl at a later memory of a step that writes below sp1 only *)
Lemma awc_gnl_step : forall (W : world SEGS) m m' (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) ->
  aw_gnl_kept cx W m -> aw_gnl_kept cx W m'.
Proof.
  intros W m m' X UN HX HG a Ha. rewrite <- (HG a Ha).
  destruct awc_win as (_ & Wc & Wlo & _). pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK.
  apply UN; [unfold LA_G_NL, NK_SIZE in Ha; lia|]. intros HXa. specialize (HX a HXa).
  unfold LA_G_NL, NK_SIZE in Ha. lia.
Qed.

(* g_nl at the memory a callee returns, when its akept excepts no byte of g_nl *)
Lemma awc_gnl_call : forall lyc Sc (W : world SEGS) m W2 m2 slo shi (E : Z -> Prop),
  akept SEGS B lyc Sc W m W2 m2 slo shi E -> (forall a, E a -> ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE)) ->
  aw_gnl_kept cx W m -> aw_gnl_kept cx W2 m2.
Proof.
  intros lyc Sc W m W2 m2 slo shi E (_ & _ & K3 & _) HE HG a Ha.
  destruct (awc_gnl_img a Ha) as (Hi & Ho & He).
  rewrite (K3 a Hi Ho He (fun HEa => HE a HEa Ha)). exact (HG a Ha).
Qed.

(* ==========================================================================
   4. THE ALIAS'S SLACK AT A CUT
   ========================================================================== *)
Lemma awc_tail_cut : forall ly3 S3 W3 ms3 md3 e,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) e ->
  (e + 1 <= LA_G_NL \/ LA_G_NL + NK_SIZE <= e) -> 0 <= e -> e + 8 <= 2 ^ 64 ->
  (forall x, e < x < e - e mod 8 + 8 -> mbyte SEGS (aw_m0 cx) x <> None) ->
  forall x, e < x < e - e mod 8 + 8 -> aview SEGS (w_H W3) (ms_mem ms3) x <> None.
Proof.
  intros ly3 S3 W3 ms3 md3 e HB Hakb Hg He0 He8 Hm0 x Hx.
  unfold aw_m0 in Hm0.
  pose proof HB as (_ & _ & _ & _ & _ & HJ3 & Hfr3 & _ & _ & Hperm & Hwit & Hfa & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & _ & HK & _).
  pose proof (awc_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  destruct (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ awc_pre_j) as (Rlo & _ & _ & _).
  destruct (Z_lt_le_dec x alloc_ceiling) as [Hlow | Hhigh].
  - destruct Hakb as [(H1 & H2) | [(b & n & Hin & Hr) | [(H1 & H2 & H3) | (c & q & Hin & Hr)]]].
    + exfalso. lia.
    + assert (Hin3 : In (b, n) (ablocks B ly3 S3))
        by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin]).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hb16 & _ & _ & _ & Hpr & _).
      destruct (Z_lt_le_dec x (b + req_size n)) as [L|L].
      * apply awc_vis_present. exact (proj1 (Hpr x ltac:(lia))).
      * apply (awc_blk_tail_vis SEGS B ly3 S3 W3 (ms_mem ms3) md3 b n x HAR3 Hin3). split; [exact L|].
        unfold round_up. lia.
    + apply (awc_img_tail e x (w_H W3) (w_H (aw_W cx)) (ms_mem ms3) (aw_memc cx) H1 H2 H3 Hx).
      * intros Hix Hox Hex. destruct HK as (_ & _ & K3 & _). apply K3; [exact Hix | exact Hox | exact Hex |].
        intros [HE | HS].
        -- unfold aw_E in HE. apply awc_wr_eq in HE. unfold LA_G_NL, NK_N_SENT, NK_SIZE in *. lia.
        -- destruct Hwit as (S1 & W1 & mem1 & md1 & HAR1 & Hfr1 & _).
           exact (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ S1 W1 mem1 md1 _ _ x HAR1
                    ltac:(rewrite Hfr1; left; reflexivity) HS) Hix).
      * apply awc_mbyte_vis. exact (Hm0 x Hx).
    + assert (Hin3 : In (c, q) (frames S3)) by (rewrite Hfr3; right; exact Hin).
      destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & Hpr & _).
      destruct (frame_al64 SEGS B _ _ _ _ _ c q HAR3 Hin3) as (Hf64 & Hfb & _).
      unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. rewrite <- (Hfa c q) in Hr.
      apply awc_vis_present. apply (proj1 (Hpr x ltac:(lia))).
  - destruct (seg_rom SEGS (Z_to_bv 64 x)) eqn:Er.
    + apply awc_vis_rom. rewrite Er. discriminate.
    + pose proof (awc_present_of_mbyte _ _ x (Hm0 x Hx) Er) as Hpc.
      destruct HK as (_ & _ & _ & _ & K5 & K6).
      apply awc_vis_present.
      destruct (Z_lt_le_dec x (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK)) as [L1|L1];
        [| destruct (Z_lt_le_dec x (aw_sp cx)) as [L2|L2]].
      * apply K5; [lia | lia | exact Hpc].
      * apply K6. lia.
      * apply K5; [lia | lia | exact Hpc].
Qed.

(* ==========================================================================
   5. The premises of RtString.astrlen_realizes at a cut, for the alias
   ========================================================================== *)
Lemma awc_strlen_pre : forall ly3 S3 W3 ms3 md3 sa (R : bvmap 5 word),
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  aw_alias cx <> 0 -> acstr_at SEGS (aw_m0 cx) (aw_alias cx) sa ->
  spZ R = aw_sp1 cx ->
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (aw_alias cx) sa /\
  RtDefs.astr_at SEGS W3 (ms_mem ms3) (aw_alias cx) sa /\
  RtDefs.aread_ok SEGS ESTACK W3 R (ms_mem ms3) (aw_alias cx) (RtDefs.astr_len sa + 1) /\
  RtDefs.atail_vis SEGS W3 (ms_mem ms3) (aw_alias cx + RtDefs.astr_len sa) /\
  RtDefs.rt_rom_view SEGS B W3 (ms_mem ms3) /\
  Z.of_nat (length sa) + 1 < 2 ^ 32.
Proof.
  intros ly3 S3 W3 ms3 md3 sa R HB Ha0 Hca Hsp.
  pose proof HPRE as (HAPRE & HRD & HP).
  pose proof HP as (kbs0 & tab0 & nm0 & al0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNM0 & HAL0 & _ & _ & HAS0 & HSL0).
  assert (Eal : al0 = Some sa)
    by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_alias cx)); [exact HAL0 | split; assumption]).
  destruct (HAS0 sa Eal) as (Hapf & Hapg & Hl32 & Hmr & Hra & Hhv).
  destruct (HSL0 sa Eal) as (slack & Hsl & Hsln).
  change (aarg (aw_regs cx) 1) with (aw_alias cx) in Hapf, Hapg, Hmr, Hra, Hhv, Hsl, Hsln.
  unfold apart_frame in Hapf. change (spZ (aw_regs cx)) with (aw_sp cx) in Hapf.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & Hro).
  assert (Hakb : forall a, aw_alias cx <= a <= aw_alias cx + Z.of_nat (length sa) ->
     akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a).
  { intros a Ha. apply HRD. right; left. split; [exact Ha0|]. exists sa. split; [exact Hca | exact Ha]. }
  destruct (aw_shadow_at SK B LAWS TB cx fpos ly3 S3 W3 ms3 md3 (aw_alias cx) (Z.of_nat (length sa) + 1)
              HPRE HB ltac:(lia) ltac:(intros a Ha; apply Hakb; lia) Hra Hhv) as (Hra3 & Hhv3).
  assert (Hcs3 : acstr_at SEGS (rdW W3 (ms_mem ms3)) (aw_alias cx) sa).
  { apply (aw_acstr_move SEGS (aw_m0 cx) _ (aw_alias cx) sa Hca). intros x Hx.
    apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    apply (aw_rd_kept SK B cx fpos ly3 S3 W3 ms3 md3 x HPRE HB). right; left.
    split; [exact Ha0|]. exists sa. split; [exact Hca | exact Hx]. }
  pose proof (aw_acstr_range SEGS _ _ _ Hca) as (Hr0 & Hr1).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct awc_win as (_ & Wc & Wlo & Whi & _ & S1lo & _).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK8560.
  assert (Hmr' : aw_alias cx + (Z.of_nat (length sa) + 1) <= 2 ^ 63)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr; lia).
  split; [exact Hcs3|].
  split; [exact (awc_astr_of_acstr W3 (ms_mem ms3) (aw_alias cx) sa Hcs3)|].
  split.
  { unfold RtDefs.aread_ok, RtDefs.astr_len. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - intros a Ha. split.
      + apply awc_mbyte_vis. destruct Hcs3 as ((_ & _ & Hby) & _).
        pose proof (Hby (Z.to_nat (a - aw_alias cx)) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
        rewrite Z2Nat.id in Hb by lia. replace (aw_alias cx + (a - aw_alias cx)) with a in Hb by lia.
        rewrite Hb. destruct (nth_error (sa ++ [zb 0]) (Z.to_nat (a - aw_alias cx))) eqn:En; [discriminate|].
        apply nth_error_None in En. rewrite length_app in En. cbn [length] in En. lia.
      + unfold RtDefs.ascratch_stk. rewrite Hsp. unfold ESTACK. lia.
    - split; [exact Hmr|]. split; [exact Hra3 | intros _; exact Hhv3]. }
  split.
  { intros a Ha. unfold RtDefs.astr_len in Ha.
    apply (awc_tail_cut ly3 S3 W3 ms3 md3 (aw_alias cx + Z.of_nat (length sa)) HB).
    - apply Hakb. lia.
    - unfold apart_gnl in Hapg. lia.
    - lia.
    - lia.
    - intros x Hx. destruct Hsl as (_ & _ & Hsb).
      pose proof (Hsb (Z.to_nat (x - (aw_alias cx + Z.of_nat (length sa) + 1))) ltac:(lia)) as Hb.
      rewrite Z2Nat.id in Hb by lia.
      replace (aw_alias cx + Z.of_nat (length sa) + 1 + (x - (aw_alias cx + Z.of_nat (length sa) + 1))) with x in Hb
        by lia.
      rewrite Hb. destruct (nth_error slack (Z.to_nat (x - (aw_alias cx + Z.of_nat (length sa) + 1)))) eqn:En;
        [discriminate|].
      apply nth_error_None in En. lia.
    - exact Ha. }
  split; [exact (awc_rt_rom W3 (ms_mem ms3) Hro) | exact Hl32].
Qed.

End c.

(* ==========================================================================
   6. The fake kernel's views at a later memory (reac_link_alias_writeSend.v aws_nk_now / aws_tab_kept)
   ========================================================================== *)
Section d.
Variable cx : awcx.
Variable fpos : Z.
#[local] Notation Eacc := (fun a => aw_E cx a \/ aside_rng (aw_lyc cx) AW_CID fpos a).
Hypothesis HPRE : aw_pre SK B cx.
Hypothesis HNIN : ~ In (AW_CID, fpos) (frames (aw_Sc cx)).
Hypothesis HS1 : exists S1 W1 mem1 md1, AR SEGS B (aw_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (AW_CID, fpos) :: frames (aw_Sc cx) /\ ablocks B (aw_lyc cx) S1 = ablocks B (aw_lyc cx) (aw_Sc cx).
Variables (tab : list (list byte * Z)) (kbs : list byte).
Hypothesis HNK : anlk_at SEGS (aw_m0 cx) LA_G_NL kbs.
Hypothesis HIT : aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab.

Lemma awc_nk_now : forall (W : world SEGS) m, aw_gnl_kept cx W m -> anlk_at SEGS (rdW W m) LA_G_NL kbs.
Proof.
  intros W m HG. apply (aw_anlk_move SEGS (aw_m0 cx) _ LA_G_NL kbs HNK).
  - intros x Hx. unfold aw_m0. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x). apply HG. exact Hx.
  - intros x Hx. apply awc_gnl_writable. exact Hx.
Qed.

Lemma awc_rd_tab : forall i n2 ix p a, nth_error tab i = Some (n2, ix) ->
  au64_at SEGS (aw_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> acstr_at SEGS (aw_m0 cx) p n2 ->
  p <= a <= p + Z.of_nat (length n2) ->
  akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a.
Proof.
  intros i n2 ix p a H1 H2 H3 H4. apply (proj1 (proj2 HPRE)). right; right.
  exists kbs, tab, i, n2, ix, p. exact (conj HNK (conj HIT (conj H1 (conj H2 (conj H3 H4))))).
Qed.

(* the Pre's per-entry facts of the table, at the call's memory *)
Lemma awc_tab_pre : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
  au64_at SEGS (aw_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  apart_frame (aw_regs cx) REAC_LINK_ALIAS_WRITE_AK p (Z.of_nat (length n2) + 1)
  /\ apart_gnl LA_G_NL p (Z.of_nat (length n2) + 1)
  /\ (0 <= p < 2 ^ 64 -> 0 < p /\
        Z.of_nat (length n2) + 1 < 2 ^ 32 /\ achk SEGS (aw_m0 cx) p (Z.of_nat (length n2) + 1)).
Proof.
  intros i n2 ix p Hi Hp.
  destruct HPRE as (_ & _ & (kbs0 & tab0 & nm & al & NK0 & _ & _ & _ & _ & IT0 & _ & _ & _ & _ & _ & TABC & _)).
  assert (kbs0 = kbs) by exact (aw_anlk_unique SEGS _ _ _ _ NK0 HNK). subst kbs0.
  assert (tab0 = tab) by exact (aw_aiftab_unique SEGS _ _ _ _ _ IT0 HIT). subst tab0.
  destruct (TABC i n2 ix p Hi Hp) as (A1 & A2 & _ & A4).
  split; [exact A1|]. split; [exact A2|].
  intros H64. destruct (A4 H64) as (B1 & B2 & B3 & _). exact (conj B1 (conj B2 B3)).
Qed.

Lemma awc_tab_kept : forall (W : world SEGS) m kbs',
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc ->
  nk_n_if kbs' = nk_n_if kbs -> aiftab_at SEGS (rdW W m) LA_G_NL kbs' tab.
Proof.
  intros W m kbs' HK Hn.
  pose proof HIT as (L1 & L80 & _).
  apply (aws_aiftab_keep SEGS (aw_m0 cx) _ kbs kbs' tab HIT Hn).
  - intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x). apply (awc_kept_gnl cx fpos HS1 W m x HK).
    unfold NK_IF_NAME, NK_N_SENT, NK_SIZE in *. lia.
  - intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x). apply (awc_kept_gnl cx fpos HS1 W m x HK).
    unfold NK_IF_INDEX, NK_N_SENT, NK_SIZE in *. lia.
  - intros i n2 ix p Hi Hp Hp64 x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    destruct HIT as (_ & _ & E). destruct (E i n2 ix Hi) as (_ & p' & P' & _ & C' & _).
    pose proof (aws_au64_unique SEGS _ _ _ _ Hp P') as Ep. pose proof (aw_acstr_range SEGS _ _ _ C') as Rp.
    rewrite !Z.mod_small in Ep by lia. subst p'.
    apply (awc_kept_akb cx fpos HPRE HNIN HS1 W m x HK (awc_rd_tab i n2 ix p x Hi Hp C' Hx)).
    unfold aw_E. rewrite awc_wr_eq. destruct (awc_tab_pre i n2 ix p Hi Hp) as (_ & Hg & _).
    unfold apart_gnl, NK_SIZE, NK_N_SENT in *. lia.
Qed.
End d.

End b.
End a.

About awc_tail_cut. About awc_strlen_pre. About awc_inv_step. About awc_base_of_inv. About awc_inv_of_base.
About awc_tab_kept. About awc_nk_now. About awc_tab_pre. About awc_gnl_step. About awc_gnl_call.
About awc_kept_akb. About awc_win. About awc_F. About awc_SH_val. About awc_pre_misc. About awc_spZ.
Print Assumptions awc_strlen_pre.
Print Assumptions awc_inv_step.
Print Assumptions awc_tab_kept.
