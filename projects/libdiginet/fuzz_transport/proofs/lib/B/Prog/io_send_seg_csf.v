(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 342 of its 407 lines of code are new or changed and 700 lines of the source are left out. *)
(* io_send_seg_csf: the call of check_sent_frame in the image-B walk of io_send (fuzz_transport.asan-ubsan
   41113a03c82f, entry 0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v
   transport_io_send_cg_holds_stmt), from the cut 0x83054 = transportb_text + IOS_SRF to the cut
   0x83064 = transportb_text + IOS_CSF (lib/B/Prog/io_send_seg_cut.v), as one segment lemma in continuation form:
   ios_csf_seg, the statement io_send_seg_cut.v ios_csf_seg_stmt. The image-A twin is lib/A/Prog/io_send_seg_csf.v.

   The code (io_send_cg.v header lines 90-91; listing slots of lib/B/Prog/DgnTransportBList.v transportb_listing):
     0x83054 - 0x8305c a2 = sp + 8, a0 = s1 (p), a1 = s0 (len);
     0x83060           the call of check_sent_frame (transportb_sigma TB_check_sent_frame), return address 0x83064.
   Image A stores f.code before these; image B's code stores nothing on the stretch.

   How it is proved.
     the run (0x83054 .. 0x83060)  a run of TransportGRunB.v paj_run_x over the caller's G journal from a fresh state
                                 at the cut with no memory region: the run writes nothing, so every byte reads as before
                                 (YC4b.v kept_of_frame with no window) and the presence of bytes only grows;
     check_sent_frame            TransportGCg.v gx_call_cg with the contract check_sent_frame_cg.v
                                 transport_check_sent_frame_cg (ios_laws' 10th conjunct; its post DgnTransportBCg.v
                                 decode_cg_post, read as dcg_post by decode_cg_post_dcg). Its premises: ra = 0x83064;
                                 gp, tp, a0 = p, a1 = len, a2 = sp + 8 from the run; its window CSF_STK below sp - 160
                                 (IOSEND_STK = 160 + CLS_STK >= 160 + CSF_STK); the frame's garr8 and trans_src_ok at the
                                 call's memory (trans_src_ok_view), its decode_off_win at CSF_STK; trans_sframe_at at
                                 sp + 8; trans_src_ok of the struct (the machine-stack case: ics_sf_src); trans_rom_view_rd
                                 at the cut from io_send_seg_cut.v ios_rom_cur, then at the call's memory (the run keeps
                                 every byte); tw_at at ios_B0 Bw; the model call.
   After the call: the journal (no event), the running acall_kept_g composed with the callee's by TransportGCg.v
   dk_kept_trans_nf_g (the callee writes nothing: E = False), the saved words and the struct kept (they lie in
   io_send's frame, above the callee's window: acall_kept_g's first clause), the callee-saved registers
   (aregs_preserved), the frame's placement and bytes by DgnTransportBCg.v trans_src_ok_acall_g (ios_laws carries
   trans_ro_rd_unowned and trans_rom_no_errno, so the TRANS_RO_RD case is kept as the others; 0 < len by
   io_send_seg_frm.v ios_len60), the struct's trans_src_ok again by ics_sf_src at the return's journal, the world
   relation at ios_B0 Bw (gx_call_cg's gx_kept, from gx_ok and gx_noerrno by gx_kept_of_acall_kept, then TWorldG.v
   tw_kept). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg io_send_cg check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut                                       *)
(* ------------------------------------------------------------------ *)

(* Atoms: the 32 registers at the cut. No region: the stretch reads and writes no memory. *)
Definition ics_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 0)] [] [].
Definition ss_ics : sstate := mkSS IOS_SRF sr_atoms [] None ics_facts.
(* No instrumented check on the stretch: the empty shadow entry, at the shadow base s4. *)
Definition ICS_Bx : sv := SOff 20 0.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ics_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ics_reg: no match for" T; fail
  end.

(* ------------------------------------------------------------------ *)
(* Bytes, the struct and the registers                                 *)
(* ------------------------------------------------------------------ *)

(* An aview equality is an mbyte equality of the restricted memories (any two hidden sets). *)
Lemma ics_mbyte_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H' m' a = aview tfibsegs H m a ->
  YP09.mbyte tfibsegs (mrestrict H' m') a = YP09.mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (YP09.mbyte tfibsegs (mrestrict H' m') a) as [b1|]; destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b2|];
  cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* garr8 at a later memory (and world) that reads the range's bytes as before. *)
Lemma ics_garr8_xw : forall (H H' : word -> bool) (m m' : word -> option byte) p l,
  garr8 tfibsegs (mrestrict H m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs H' m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H' m') p l.
Proof.
intros H H' m m' p l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros i Hi. assert (Ei : i = 0%nat) by lia. subst i.
rewrite (ics_mbyte_of_aview H H' m m' (p + Z.of_nat j + Z.of_nat 0)).
- exact (Hv 0%nat Hi).
- apply Hk. lia.
Qed.

(* The struct at a later memory (and world) that reads its 80 bytes as before. *)
Lemma ics_sframe_xw : forall (W W' : world tfibsegs) mem mem' q fa f,
  (forall a, q <= a < q + 80 -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  trans_sframe_at W mem q fa f -> trans_sframe_at W' mem' q fa f.
Proof.
intros W W' mem mem' q fa f Heq (H0 & H8 & SB & HG & HL & R). split; [exact H0|]. split; [exact H8|].
exists SB. split; [|split; [exact HL | exact R]].
apply (ics_garr8_xw _ _ _ _ _ _ HG). intros a Ha. rewrite length_map, HL in Ha. apply Heq. lia.
Qed.

(* A present byte is visible. *)
Lemma ics_some_of_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, YP09.mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma ics_tw_in_G : forall x, tw_in TMAP_B x -> inG TG.G_HARNESS_B x.
Proof.
intros x (o & b & n & Hin & Hx). unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma ics_ap_trans : forall r1 r2 r3 : bvmap 5 word,
  aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* ios_regs and s8 .. s11 through a call that keeps the callee-saved registers. *)
Lemma ics_regs_pres : forall regs (r2 r3 : bvmap 5 word) p frame fb,
  ios_regs regs r2 p frame fb -> aregs_preserved r2 r3 -> ios_regs regs r3 p frame fb.
Proof.
intros regs r2 r3 p frame fb (R2 & R3 & R4 & R8 & R9 & R19 & R20) HP. unfold ios_regs.
split; [refine (eq_trans (HP 2 ltac:(unfold acallee_saved; lia)) _); exact R2|].
split; [refine (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) _); exact R3|].
split; [refine (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) _); exact R4|].
split; [refine (eq_trans (HP 8 ltac:(unfold acallee_saved; lia)) _); exact R8|].
split; [refine (eq_trans (HP 9 ltac:(unfold acallee_saved; lia)) _); exact R9|].
split; [refine (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) _); exact R19|].
refine (eq_trans (HP 20 ltac:(unfold acallee_saved; lia)) _); exact R20.
Qed.

Lemma ics_s811 : forall regs (r2 r3 : bvmap 5 word),
  (forall r, 24 <= r <= 27 -> YK11.getr r2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  aregs_preserved r2 r3 ->
  forall r, 24 <= r <= 27 -> YK11.getr r3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r).
Proof.
intros regs r2 r3 H HP r Hr. rewrite (HP r ltac:(unfold acallee_saved; lia)). exact (H r Hr).
Qed.

Section icsw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuation of the cut's state: the 32 registers. *)
Definition ics_E (r : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg r []).

(* The return address of the call is the cut IOS_CSF. *)
Lemma ics_pc : Z_to_bv 64 (BASE + 7620) = w64 (transportb_text + IOS_CSF).
Proof. unfold w64. f_equal; try (vm_compute; reflexivity). Qed.

(* The cut's state: the registers, no memory region. *)
Lemma ics_entry : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (sp : Z),
  YK11.getr r 2 = w64 sp -> 2 ^ 46 <= sp -> sp + 12 <= 2 ^ 47 ->
  st_ok_pi segs VAL (ics_E r) ss_ics
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_SRF)) mem (YK11.seg_rom segs))).
Proof.
  intros W r mem sp R2 H0 H1.
  assert (U2 : bv_unsigned (ew (ics_E r) 2) = sp)
    by (unfold ics_E; rewrite (ew_Eimg_Ereg_nat r [] 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold ss_ics.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - unfold ics_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - unfold facts_ok, ics_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try exact I; lia.
Qed.

(* A step of the walk that changes only bytes of io_send's stack window or bytes of G in its written range keeps the
   running kept fact (at any world of the step). *)
Lemma ics_kept_step : forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 mem3 slo shi (E Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B G ->
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (slo <= a < shi) \/ (inG G a /\ E a)) ->
  YM05.alloc_ceiling <= slo -> shi <= 2 ^ 47 ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
  intros G lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ Hce Hhi.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG G a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transportb_segs_low G a HGX Ha)).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia |].
    intros HZa. destruct (HZ a HZa) as [Hs | [Hg _]]; [exact (Hw Hs) | pose proof (GLOW a Hg); lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow.
    rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [Hg _]]; [lia | exact (HnG Hg)].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < YM05.alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Ha Hw Hp. apply Hgr. apply K5; [exact Ha | exact Hw | exact Hp].
  - intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* The struct's 80 bytes at sp + 8 placed by trans_src_ok at any state of the walk's journal: the machine-stack case,
   with decode_rd_ok (the window's bytes present by the journal, the stack's zero shadow by stack_zshadow_ra). *)
Lemma ics_sf_src : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem2 md2 k q,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem2 md2 k ->
  sp0 - STK <= q -> q + 88 <= sp0 ->
  trans_src_ok B ly2 S2 W2 mem2 q SF_SIZE.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k q HJ H1 H2.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold SF_SIZE.
destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q 80 HAR ltac:(lia) ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
  as [HRA HHL].
right. split.
- right. right. left. rewrite Elo, Ehi. lia.
- split; [|split; [exact HRA | split; [exact HHL | split; [| split; lia]]]].
  + intros a Ha. apply ics_some_of_present. apply Hpres. lia.
  + unfold amem_range. right. lia.
Qed.

(* The stretch 0x83054 .. 0x83060 and the call of check_sent_frame, from the cut IOS_SRF to the cut IOS_CSF. *)
Lemma ios_csf_seg : @ios_csf_seg_stmt fx rc B MT.
Proof.
unfold ios_csf_seg_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 Q
  HL HF HM HC HK.
(* the read-only bytes at the cut (ios_rom_cur) *)
assert (HROM : trans_rom_view_rd W2 mem2)
  by (eapply ios_rom_cur; [exact HL | exact HF | exact (proj1 HC)]).
pose proof (ios_len60 _ _ _ HM) as H60.
destruct HL as (HCELLS & _ & HRU & HRE & LAWS & MTL & HGX & HGE & _ & HCSF & _).
destruct HF as (HJe & _ & _ & Hgp & Htp & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _ & _ & Hoff & _
  & _ & _ & _ & _ & _ & Hev).
destruct HC as ((HJ & HFR2 & HPM2 & HMO2 & HK2) & HSV & HR & H811 & HSF & HGA & HSRC & HTW).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
(* the entry journal: its AR, the stack, the layout *)
pose proof HJe as (_ & _ & (memS & HJei & _) & _). rewrite !Z.add_0_r in HJei.
pose proof HJei as (HAR & HLEc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HLEc as (_ & _ & _ & _ & _ & EFc & _ & _ & _ & Eloc & Ehic & _).
clear HJei memS.
(* the journal at the cut *)
pose proof HJ as (_ & _ & (memS & HJ2i & _) & _). rewrite !Z.add_0_r in HJ2i.
pose proof HJ2i as (HAR2 & HLE2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
destruct HLE2 as (_ & _ & _ & _ & _ & EF2 & _ & _ & _ & Elo2 & Ehi2 & _).
clear HJ2i memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8512) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (CS : CSF_STK = 8240) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (GLOW : forall a, inG TG.G_HARNESS_B a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
assert (ERA : BASE + 7620 = 536676) by (vm_compute; reflexivity).
replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) in HSF by (unfold IOS_F_OFF; lia).
(* the cut's state *)
pose proof (ics_entry W2 regs2 mem2 (spZ regs - 160) ltac:(exact R2) ltac:(lia) ltac:(lia)) as HS.
assert (SHOK : sh_ok segs ICS_Bx [] (ics_E regs2) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
set (E0 := ics_E regs2) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ics_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ics_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs - 160)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, IOSEND_FRAME; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_SRF)) mem2 (YK11.seg_rom segs)) md2)
    Qx) end.
(* the run, 0x83054 .. 0x83060: the arguments, the call of check_sent_frame; no store *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
rename ms into msT.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem2 a).
{ intros a Ha.
  apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros Hf; exact Hf].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end.
  cbn [In] in Hin. destruct Hin. }
assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msT) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the call's memory: every byte as at the cut *)
assert (HSFT : trans_sframe_at W2 (ms_mem msT) (spZ regs - 152) p (TC.rf frame)).
{ eapply (ics_sframe_xw W2 W2 mem2 (ms_mem msT)); [|exact HSF]. intros a Ha. apply KR. lia. }
pose proof (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 p (Z.of_nat (length frame)) HAR2 HSRC ltac:(lia))
  as Hplace.
assert (KF : forall a, p <= a < p + Z.of_nat (length frame) ->
  aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply KR. destruct Hplace as [Pl | Pl]; lia. }
assert (KS : forall s, kLowMemEnd <= s < kHighShadowEnd ->
  aview segs (w_H W2) (ms_mem msT) s = aview segs (w_H W2) mem2 s)
  by (intros s Hs; apply KR; lia).
assert (HGAT : garr8 segs (mrestrict (w_H W2) (ms_mem msT)) p (map DSpec.bz frame)).
{ apply (ics_garr8_xw (w_H W2) (w_H W2) mem2 (ms_mem msT) p _ HGA). intros a Ha. rewrite length_map in Ha.
  exact (KF a Ha). }
assert (HSRCT : trans_src_ok B ly2 S2 W2 (ms_mem msT) p (Z.of_nat (length frame))).
{ eapply trans_src_ok_view; [exact HSRC | exact KF | exact KS]. }
assert (HROMT : trans_rom_view_rd W2 (ms_mem msT)).
{ intros a Ha. rewrite <- (HROM a Ha). pose proof (trans_ro_rd_bounds a Ha) as Rb. apply KR; lia. }
assert (HTWT : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msT)) (ios_B0 Bw)).
{ apply (tw_kept TMAP_B _ _ _ HTW). intros x Hx. pose proof (GLOW x (ics_tw_in_G x Hx)) as Hl.
  unfold kLowMemEnd in Hl. apply KR; lia. }
assert (HKT : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem msT) (spZ regs - IOSEND_STK) (spZ regs)
                 (iosend_wr (Z.of_nat (length frame)))).
{ apply (ics_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 (ms_mem msT) (spZ regs - IOSEND_STK) (spZ regs) _
    (fun _ => False) LAWS HGX HAR HK2 (fun a Ha _ => KR a Ha) GA);
    [intros a Ha; cbv beta in Ha; destruct Ha | lia | lia]. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HART.
(* the registers at the call *)
pmkst HS.
ics_reg HS (Z_to_bv 5 10) (w64 p) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
ics_reg HS (Z_to_bv 5 11) (w64 (Z.of_nat (length frame))) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
ics_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (spZ regs - 152)) Q12 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ics_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 160)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ics_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 7620)) RA ltac:(apply codeptr_val; exact HEI).
ics_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
ics_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (HPR : aregs_preserved regs2 (ms_regs msT)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E0 _ msT regs2 [] HS).
  - split; [intros n Hn; unfold E0, ics_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
  - vm_compute. reflexivity. }
assert (ESP : bv_unsigned (YK11.getr (ms_regs msT) (Z_to_bv 5 2)) = spZ regs - 160)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs msT) = spZ regs - 160) by exact ESP.
assert (RAok : YK0s.ret_ok (Z_to_bv 64 (BASE + 7620)))
  by (apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
(* 0x83060: check_sent_frame, through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_check_sent_frame)) mm rom) mdx) Qx) end.
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2
    (ms_mem msT) md3 (k + 0) _ (ms_regs msT) CSF_STK CSF_EV 0 (fun _ => False)
    (fun _ _ _ => ios_B0 Bw = ios_B0 Bw) HGX HGE HJ).
  intros memS HJd.
  eapply SRr_mono.
  { apply (HCSF fx STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 (ms_mem msT) md3 (k + 0) (ms_regs msT)
      p (spZ regs - 152) frame (ios_B0 Bw) (ios_B0 Bw) HJd).
    - exact (eq_ind_r (fun w => YK0s.ret_ok w) RAok RA).
    - unfold raZ. rewrite RA, ERA, unsigned_lit_small by lia. lia.
    - exact Q3.
    - exact Q4.
    - exact Q10.
    - exact Q11.
    - exact Q12.
    - rewrite Hsp1. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia.
      rewrite Z_mod_plus_full. exact Hsp16.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact Hp0.
    - exact HGAT.
    - exact HSRCT.
    - unfold decode_off_win in *. rewrite Hsp1. destruct Hoff as [Ho | Ho]; [left | right]; lia.
    - exact HSFT.
    - exact (ics_sf_src STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem msT) md3 (k + 0) (spZ regs - 152) HJ
        ltac:(lia) ltac:(lia)).
    - unfold decode_off_win. right. rewrite Hsp1. lia.
    - exact HROMT.
    - exact HTWT.
    - exact HM.
    - unfold CSF_EV, IOSEND_EV in *. lia. }
  cbv beta. intros W3 c3 _ H3. apply decode_cg_post_dcg. exact H3. }
cbv beta.
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md4 & e & -> & He & HJ3 & HP3 & HFR3 & HPM3 & HK3 & HMO3 & (_ & HGK3)).
assert (Ee : e = 0) by (unfold CSF_EV in He; lia). subst e.
replace (k + 0 + 0) with (k + 0) in HJ3 by lia.
(* the journal at the return *)
pose proof HJ3 as (_ & _ & (memS & HJ3i & _) & _). rewrite !Z.add_0_r in HJ3i.
pose proof HJ3i as (HAR3 & HLE3 & _).
destruct HLE3 as (_ & _ & _ & _ & _ & EF3 & _ & _ & _ & Elo3 & Ehi3 & _).
clear HJ3i memS.
pose proof HK3 as (K31 & _).
(* the frame across the callee *)
assert (Hoff3 : p + Z.of_nat (length frame) <= spZ (ms_regs msT) - CSF_STK \/ spZ (ms_regs msT) <= p).
{ unfold decode_off_win in Hoff. rewrite Hsp1. destruct Hoff as [Ho | Ho]; [left | right]; lia. }
destruct (trans_src_ok_acall_g B LAWS HRU HRE ly2 S2 W2 (ms_mem msT) md3 ly3 S3 W3 mem3 md4
  (spZ (ms_regs msT) - CSF_STK) (spZ (ms_regs msT)) (fun _ => False) p (Z.of_nat (length frame))
  HART HAR3 HPM3 HFR3 ltac:(intros cid pos; unfold frame_addr; rewrite EF3, EF2; reflexivity)
  ltac:(rewrite Elo3, Elo2; reflexivity) ltac:(rewrite Ehi3, Ehi2; reflexivity)
  HK3 HGK3 ltac:(intros a _ Hf; exact Hf) ltac:(intros a _ Hf; exact Hf)
  Hoff3 HSRCT ltac:(lia)) as [HSRC3 KF3].
assert (HGA3 : garr8 segs (mrestrict (w_H W3) mem3) p (map DSpec.bz frame)).
{ apply (ics_garr8_xw (w_H W2) (w_H W3) (ms_mem msT) mem3 p _ HGAT). intros a Ha. rewrite length_map in Ha.
  exact (KF3 a Ha). }
(* the running kept fact *)
assert (HK4 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - IOSEND_STK) (spZ regs)
                 (iosend_wr (Z.of_nat (length frame)))).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 (ms_mem msT) W3 mem3
    (spZ regs - IOSEND_STK) (spZ regs) (spZ (ms_regs msT) - CSF_STK) (spZ (ms_regs msT))
    (iosend_wr (Z.of_nat (length frame))) (fun _ => False) (fun _ => False)).
  - lia.
  - lia.
  - intros cid pos. unfold frame_addr. rewrite EF2, EFc. reflexivity.
  - intros f Hf. rewrite HFR2. exact Hf.
  - intros bm Hbm. exact (Permutation_in _ (Permutation_sym HPM2) Hbm).
  - intros b m i _ _ Hf. exact Hf.
  - intros cid pos a _ _ Hf. exact Hf.
  - exact HKT.
  - exact HK3.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - intros a Hf. destruct Hf. }
(* the saved words, the struct, the world *)
assert (HSV3 : ios_saved W3 mem3 regs).
{ unfold ios_saved in *. rewrite Forall_forall in HSV |- *. intros o Ho. rewrite <- (HSV o Ho).
  assert (Hd : 8 <= fst o <= 72)
    by (unfold IOS_SAVED in Ho; cbn [In] in Ho; repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]); destruct Ho).
  apply rdword_ext. intros j Hj.
  rewrite K31 by (rewrite ?Hsp1; lia). apply KR; lia. }
assert (HSF3 : trans_sframe_at W3 mem3 (spZ regs - 152) p (TC.rf frame)).
{ eapply (ics_sframe_xw W2 W3 (ms_mem msT) mem3); [|exact HSFT].
  intros a Ha. apply K31; [lia | rewrite Hsp1; lia]. }
assert (HTW3 : tw_at TMAP_B (aview segs (w_H W3) mem3) (ios_B0 Bw)).
{ apply (tw_kept TMAP_B _ _ _ HTWT). intros x Hx. exact (HGK3 x (ics_tw_in_G x Hx)). }
(* the registers *)
assert (HPT : aregs_preserved regs2 regs3) by exact (ics_ap_trans _ _ _ HPR HP3).
assert (HR3 : ios_regs regs regs3 p frame (TW.g_fail_next Bw)) by exact (ics_regs_pres _ _ _ _ _ _ HR HPT).
pose proof (ics_s811 regs regs2 regs3 H811 HPT) as H8113.
assert (HCUR3 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly3 S3 W3 mem3 md4).
{ unfold ios_cur. split; [exact HJ3|]. split; [rewrite HFR3; exact HFR2|].
  split; [exact (Permutation_trans HPM3 HPM2)|].
  split; [exact (mo_le_trans MT MTL Sc S2 S3 0 0 HMO2 HMO3) | exact HK4]. }
(* the cut *)
rewrite RA, ics_pc.
specialize (HK ly3 S3 W3 mem3 md4 regs3). unfold cfg_at in HK. apply HK.
unfold ios_at_csf, ios_e2_at.
replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) by (unfold IOS_F_OFF; lia).
split; [exact HCUR3|]. split; [exact HSV3|]. split; [exact HR3|]. split; [exact H8113|].
split; [exact HSF3|].
split; [exact (ics_sf_src STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 mem3 md4 (k + 0) (spZ regs - 152) HJ3
          ltac:(lia) ltac:(lia))|].
split; [exact HGA3|]. split; [exact HSRC3 | exact HTW3].
Qed.

End icsw.
