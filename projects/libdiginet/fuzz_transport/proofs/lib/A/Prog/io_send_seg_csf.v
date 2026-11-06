(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1878 of its 1989 lines of code are new or changed and 815 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_send_seg_tail.v, with its module names changed; 388 of its 483 lines of code are new or changed and 1894 lines of the source are left out. *)
(* io_send_seg_csf: the call of check_sent_frame in the image-A walk of io_send (fuzz_transport.asan e89be137db17,
   entry 0x82d60 = TImgA.v ti_io_send timg_A; the statement is lib/A/Prog/io_send_cg.v
   transport_io_send_cg_holds_stmt), from the join 0x83074 = transport_text + IOS_AT 0x314 to the cut
   0x83088 = transport_text + IOS_CSF (lib/A/Prog/io_send_seg_cut.v), as one segment lemma in continuation form:
   ios_csf_seg.

   The code (io_send_cg.v header lines 99-102; listing slots 2004-2008 of lib/A/Prog/DgnTransportList.v):
     0x83074           the 4-byte store of a0 at sp + 8 (f.code; a0 = 0 on the path the model allows);
     0x83078 - 0x83080 a2 = sp + 8, a0 = s1 (p), a1 = s0 (len);
     0x83084           `jal` check_sent_frame (transport_sigma TS_check_sent_frame), return address 0x83088.

   How it is proved.
     the run (0x83074 .. 0x83084)  a run of TransportGRunA.v paj_run_x over the caller's G journal from a fresh state
                                 at the join whose one region is the 4 bytes f + 0 .. f + 3 (writable: bytes of the
                                 caller's window, awr_byte); it stores 0 there (the chunk of atom 10, a0 = 0), and the
                                 memory is kept outside them (YC4b.v kept_of_frame);
     check_sent_frame            TransportGCg.v gx_call_cg with the contract check_sent_frame_cg.v
                                 transport_check_sent_frame_cg (its post DgnTransportCg.v decode_cg_post, read as
                                 dcg_post by decode_cg_post_dcg). Its premises: ra = 0x83088; gp, tp, a0 = p, a1 = len,
                                 a2 = sp + 8 from the run; its window CSF_STK below sp - 160 (IOSEND_STK = 160 +
                                 CLS_STK >= 160 + CSF_STK); the frame's garr8 and trans_src_ok at the call's memory
                                 (the store misses the frame: decode_off_win at IOSEND_STK; trans_src_ok_view), its
                                 decode_off_win at CSF_STK; trans_sframe_at at sp + 8 (the store writes 0 over the code
                                 bytes, which trans_sframe_at already makes sf_code (rf frame) = 0: ics_code0);
                                 trans_src_ok of the struct (the machine-stack case: ics_sf_src); trans_rom_view_rd and
                                 tw_at at the call's memory (the store misses them); the model call.
   After the call: the journal (no event), the running acall_kept_g composed with the callee's by TransportGCg.v
   dk_kept_trans_nf_g (the callee writes nothing: E = False), the saved words and the struct kept (they lie in
   io_send's frame, above the callee's window: acall_kept_g's first clause), the callee-saved registers
   (aregs_preserved), the frame's placement by io_send_seg_src.v ios_src_ok_acall_g (60 <= len, so the TRANS_RO_RD
   case is out and the two record facts are not needed) and its bytes by the same lemma, the world relation (the callee
   keeps G: gx_kept, then TWorldG.v tw_kept).

   THE PREMISES at the join (io_send_seg_cut.v ios_at_join, at (ly2, S2, W2, mem2, md2) with registers regs2):
     ios_cur; ios_saved W2 mem2 regs; ios_regs regs regs2 p frame (g_fail_next Bw); s8 .. s11 as at the entry;
     a0 = w64 0; trans_sframe_at W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (rf frame); garr8 and trans_src_ok
     of the frame; trans_rom_view_rd W2 mem2; tw_at TMAP_A (aview segs (w_H W2) mem2) (ios_B0 Bw);
   and besides: ios_laws, ios_fix, check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt), 60 <= len.

   THE CONCLUSION at IOS_CSF (io_send_seg_cut.v ios_at_csf, at (ly3, S3, W3, mem3, md3) with registers regs3, the
   state check_sent_frame returns to):
     ios_cur ... ly3 S3 W3 mem3 md3 (the journal at k + 0, frames S3 = frames Sc, the blocks a Permutation of the
     caller's, mo_le MT Sc S3 0, acall_kept_g over [spZ regs - IOSEND_STK, spZ regs) and iosend_wr len);
     ios_saved W3 mem3 regs; ios_regs regs regs3 p frame (g_fail_next Bw); s8 .. s11 as at the entry;
     trans_sframe_at W3 mem3 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (rf frame);
     trans_src_ok B ly3 S3 W3 mem3 (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE;
     garr8 of the frame at p and trans_src_ok B ly3 S3 W3 mem3 p len;
     tw_at TMAP_A (aview segs (w_H W3) mem3) (ios_B0 Bw).
   trans_rom_view_rd is not carried past the callee (it would need trans_ro_rd_unowned / trans_rom_no_errno); no
   later callee of io_send reads TRANS_RO_RD. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg io_send_cg check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_segs io_send_seg_cut io_send_seg_frm io_send_seg_src.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the join                                      *)
(* ------------------------------------------------------------------ *)

(* Atoms: the 32 registers at the join. One region: f + 0 .. f + 3 at sp + 8, writable. *)
Definition ics_region : YP09.region := YP09.mkRegion (Some 2%nat) 8 12 8 12 [].
Definition ics_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 0)] [] [].
Definition ss_ics : sstate := mkSS (IOS_AT 0x314) sr_atoms [ics_region] None ics_facts.
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

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac ics_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* ------------------------------------------------------------------ *)
(* Bytes, the struct and the registers                                 *)
(* ------------------------------------------------------------------ *)

(* The n bytes of a val_mem fact, read through the view. *)
Lemma ics_val_rd : forall (H : word -> bool) (m : word -> option byte) a n v k,
  YI04.val_mem tfibsegs (mrestrict H m) a n v -> (k < n)%nat ->
  aview tfibsegs H m (a + Z.of_nat k) = Some (YO0f.le_byte v n k).
Proof.
intros H m a n v k Hv Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* Byte j of a garr8 list, read through the view. *)
Lemma ics_garr8_rd : forall (H : word -> bool) (m : word -> option byte) q l j,
  garr8 tfibsegs (mrestrict H m) q l -> (j < length l)%nat -> aview tfibsegs H m (q + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m q l j HG Hj. destruct (HG j Hj) as [Hv Hr].
pose proof (ics_val_rd H m (q + Z.of_nat j) 1 (nth j l 0) 0 Hv ltac:(lia)) as R.
rewrite Nat2Z.inj_0, Z.add_0_r in R. rewrite R. f_equal. apply tw_le_byte1. exact Hr.
Qed.

(* A struct whose 4-byte code field is 0 (trans_sframe_at at code SPEC_OK): its first four bytes read 0. *)
Lemma ics_code0 : forall (H : word -> bool) (m : word -> option byte) q (SB : list byte),
  garr8 tfibsegs (mrestrict H m) q (map DSpec.bz SB) -> length SB = 80%nat -> TW.s32_at SB 0 = 0 ->
  forall j, 0 <= j < 4 -> aview tfibsegs H m (q + j) = Some 0.
Proof.
intros H m q SB HG HL HS j Hj.
pose proof (TWL.u_at_range SB 0 4) as Ru. change (8 * Z.of_nat 4) with 32 in Ru.
assert (HU : TW.u_at SB 0 4 = 0).
{ unfold TW.s32_at in HS. destruct (Z_lt_le_dec (TW.u_at SB 0 4) (2 ^ 31)) as [Hlt | Hge].
  - rewrite bv_swrap_small in HS by (change (bv_half_modulus 32) with (2 ^ 31); lia). exact HS.
  - exfalso. unfold bv_swrap, bv_wrap in HS. change (bv_half_modulus 32) with 2147483648 in HS.
    change (bv_modulus 32) with 4294967296 in HS. Z.div_mod_to_equations. lia. }
assert (L4 : length (TW.sub SB 0 4) = 4%nat) by (apply TWL.length_sub; rewrite ?HL; lia).
assert (Hj' : (Z.to_nat j < 4)%nat) by lia.
pose proof (tw_le_byte_ble (TW.sub SB 0 4) (Z.to_nat j) (Z_to_bv 8 0) ltac:(lia)) as Hb.
fold (TW.u_at SB 0 4) in Hb. rewrite HU, L4 in Hb.
rewrite (tw_nth_sub SB 0 4 (Z.to_nat j) (Z_to_bv 8 0)) in Hb by (rewrite ?HL; lia).
change (Z.to_nat 0) with 0%nat in Hb. rewrite Nat.add_0_l in Hb.
replace (q + j) with (q + Z.of_nat (Z.to_nat j)) by lia.
rewrite (ics_garr8_rd H m q _ (Z.to_nat j) HG ltac:(rewrite length_map, HL; lia)).
f_equal.
assert (Ev : nth (Z.to_nat j) (map DSpec.bz SB) 0 = DSpec.bz (nth (Z.to_nat j) SB (Z_to_bv 8 0)))
  by exact (map_nth DSpec.bz SB (Z_to_bv 8 0) (Z.to_nat j)).
rewrite Ev. unfold DSpec.bz. rewrite <- Hb. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l.
reflexivity.
Qed.

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
Lemma ics_tw_in_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof.
intros x (o & b & n & Hin & Hx). unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
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
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of the join's state: the 32 registers. *)
Definition ics_E (r : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg r []).

(* The return address of the call is the cut IOS_CSF. *)
Lemma ics_pc : Z_to_bv 64 (BASE + 7716) = w64 (transport_text + IOS_CSF).
Proof. unfold w64. f_equal; try (vm_compute; reflexivity). Qed.

(* The join's state: f + 0 .. f + 3 (at sp + 8) writable bytes of the stack. *)
Lemma ics_entry : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (sp : Z),
  YK11.getr r 2 = w64 sp -> 2 ^ 46 <= sp -> sp + 12 <= 2 ^ 47 ->
  (forall a, sp + 8 <= a < sp + 12 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ics_E r) ss_ics
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_AT 0x314)) mem (YK11.seg_rom segs))).
Proof.
  intros W r mem sp R2 H0 H1 Hp.
  assert (U2 : bv_unsigned (ew (ics_E r) 2) = sp)
    by (unfold ics_E; rewrite (ew_Eimg_Ereg_nat r [] 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold ss_ics.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - unfold ics_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold ics_region, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable segs). apply Hp. lia.
  - exact (conj I I).
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
  alloc_ceiling <= slo -> shi <= 2 ^ 47 ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
  intros G lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ Hce Hhi.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG G a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transport_segs_low G a HGX Ha)).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia |].
    intros HZa. destruct (HZ a HZa) as [Hs | [Hg _]]; [exact (Hw Hs) | pose proof (GLOW a Hg); lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hlow.
    rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [Hg _]]; [lia | exact (HnG Hg)].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < alloc_ceiling).
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
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
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

(* The stretch 0x83074 .. 0x83084 and the call of check_sent_frame, from the join to the cut IOS_CSF. *)
Lemma ios_csf_seg : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
    p frame Bw ly2 S2 (W2 : world segs) mem2 md2 regs2 (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  60 <= Z.of_nat (length frame) ->
  ios_at_join B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
  (forall ly3 S3 (W3 : world segs) mem3 md3 regs3,
     ios_at_csf B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly3 S3 W3 mem3 md3 regs3 ->
     SRr segs W3 (@cfg_at fx segs (transport_text + IOS_CSF) regs3 mem3 md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_AT 0x314) regs2 mem2 md2) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 Q
  HL HF HM H60 HC HK.
destruct HL as (HCELLS & _ & LAWS & MTL & HGX & HGE & _ & HCSF & _).
destruct HF as (HJe & _ & _ & Hgp & Htp & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _ & _ & Hoff & _
  & _ & _ & _ & _ & _ & Hev).
destruct HC as ((HJ & HFR2 & HPM2 & HMO2 & HK2) & HSV & HR & H811 & HA0 & HSF & HGA & HSRC & HROM & HTW).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
(* the entry journal: its AR, the stack, the layout *)
pose proof HJe as (_ & _ & (memS & HJei & _) & _). rewrite !Z.add_0_r in HJei.
pose proof HJei as (HAR & HLEc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HLEc as (_ & _ & _ & _ & _ & EFc & _ & _ & _ & Eloc & Ehic & _).
clear HJei memS.
(* the journal at the join *)
pose proof HJ as (_ & _ & (memS & HJ2i & _) & _). rewrite !Z.add_0_r in HJ2i.
pose proof HJ2i as (HAR2 & HLE2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
destruct HLE2 as (_ & _ & _ & _ & _ & EF2 & _ & _ & _ & Elo2 & Ehi2 & _).
clear HJ2i memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (CS : CSF_STK = 8240) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
assert (ERA : BASE + 7716 = 536712) by (vm_compute; reflexivity).
(* the struct's code bytes are 0: trans_sframe_at at sf_code (rf frame) = SPEC_OK *)
replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) in HSF by (unfold IOS_F_OFF; lia).
assert (Hcode : DSpec.sf_code (TC.rf frame) = 0) by (rewrite (ios_sf_code _ _ _ HM); reflexivity).
assert (HZ4 : forall j, 0 <= j < 4 -> aview segs (w_H W2) mem2 (spZ regs - 152 + j) = Some 0).
{ pose proof HSF as (_ & _ & SB & HGS & HLS & HCS & _). rewrite Hcode in HCS.
  exact (ics_code0 (w_H W2) mem2 (spZ regs - 152) SB HGS HLS HCS). }
(* the join's state *)
pose proof (ics_entry W2 regs2 mem2 (spZ regs - 160) ltac:(exact R2) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; apply Hpres2; lia)) as HS.
assert (SHOK : sh_ok segs ICS_Bx [] (ics_E regs2) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
set (E0 := ics_E regs2) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ics_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ics_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs - 160)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, IOSEND_FRAME; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_AT 0x314)) mem2 (YK11.seg_rom segs)) md2)
    Qx) end.
(* the run, 0x83074 .. 0x83084: the store of a0 = 0 at sp + 8, the arguments, `jal check_sent_frame` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
rename ms into msT.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 152 <= a < spZ regs - 148) ->
  aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem2 a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 152 <= x < spZ regs - 148) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  ics_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msT) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the stored 0 *)
pose proof (YC4b.st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
destruct RG0 as (_ & _ & _ & HC0). cbn [YP09.r_base YP09.r_chunks base_val] in HC0. rewrite Usp in HC0.
pose proof (Forall_inv HC0) as HCk. clear HC0.
assert (VZ : forall j, 0 <= j < 4 -> aview segs (w_H W2) (ms_mem msT) (spZ regs - 152 + j) = Some 0).
{ intros j Hj.
  pose proof (val_of_chunk_ok segs E0 (mrestrict (w_H W2) (ms_mem msT)) (spZ regs - 160) 8 4%N _ 0 HCk
    ltac:(first [reflexivity | cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), HA0; reflexivity])
    ltac:(cbn; lia) ltac:(cbn; lia)) as Vm.
  replace (spZ regs - 152 + j) with (spZ regs - 160 + 8 + Z.of_nat (Z.to_nat j)) by lia.
  rewrite (ics_val_rd _ _ _ _ _ (Z.to_nat j) Vm ltac:(cbn; lia)).
  unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l. reflexivity. }
clear HCk.
(* the call's memory: the struct's 80 bytes read as before (the 4 code bytes 0 both times), every byte outside
   f + 0 .. f + 3 kept *)
assert (KM : forall a, spZ regs - 152 <= a < spZ regs - 72 ->
  aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_lt_le_dec a (spZ regs - 148)) as [H1 | H1].
  - replace a with (spZ regs - 152 + (a - (spZ regs - 152))) by lia.
    rewrite (VZ (a - (spZ regs - 152)) ltac:(lia)), (HZ4 (a - (spZ regs - 152)) ltac:(lia)). reflexivity.
  - apply KR; lia. }
assert (HSFT : trans_sframe_at W2 (ms_mem msT) (spZ regs - 152) p (TC.rf frame)).
{ eapply (ics_sframe_xw W2 W2 mem2 (ms_mem msT)); [|exact HSF]. intros a Ha. apply KM. lia. }
pose proof (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 p (Z.of_nat (length frame)) HAR2 HSRC ltac:(lia))
  as Hplace.
assert (KF : forall a, p <= a < p + Z.of_nat (length frame) ->
  aview segs (w_H W2) (ms_mem msT) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply KR; [destruct Hplace as [Pl | Pl]; lia | unfold decode_off_win in Hoff; lia]. }
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
assert (HTWT : tw_at TMAP_A (aview segs (w_H W2) (ms_mem msT)) (ios_B0 Bw)).
{ apply (tw_kept TMAP_A _ _ _ HTW). intros x Hx. pose proof (GLOW x (ics_tw_in_G x Hx)) as Hl.
  unfold kLowMemEnd in Hl. apply KR; lia. }
assert (HKT : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem msT) (spZ regs - IOSEND_STK) (spZ regs)
                 (iosend_wr (Z.of_nat (length frame)))).
{ apply (ics_kept_step TG.G_HARNESS lyc Sc W memc mdc W2 mem2 (ms_mem msT) (spZ regs - IOSEND_STK) (spZ regs) _
    (fun a => spZ regs - 152 <= a < spZ regs - 148) LAWS HGX HAR HK2 KR GA); [intros a Ha; left; lia | lia | lia]. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HART.
(* the registers at the call *)
pmkst HS.
ics_reg HS (Z_to_bv 5 10) (w64 p) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
ics_reg HS (Z_to_bv 5 11) (w64 (Z.of_nat (length frame))) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
ics_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (spZ regs - 152)) Q12 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ics_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 160)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ics_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 7716)) RA ltac:(apply codeptr_val; exact HEI).
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
assert (RAok : YK0s.ret_ok (Z_to_bv 64 (BASE + 7716)))
  by (apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity]).
(* 0x83084: check_sent_frame, through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS_check_sent_frame)) mm rom) mdx) Qx) end.
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2
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
    - unfold decode_off_win in *. rewrite Hsp1. lia.
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
destruct (ios_src_ok_acall_g B LAWS ly2 S2 W2 (ms_mem msT) md3 ly3 S3 W3 mem3 md4
  (spZ (ms_regs msT) - CSF_STK) (spZ (ms_regs msT)) (fun _ => False) p (Z.of_nat (length frame))
  HART HAR3 HPM3 HFR3 ltac:(intros cid pos; unfold frame_addr; rewrite EF3, EF2; reflexivity)
  ltac:(rewrite Elo3, Elo2; reflexivity) ltac:(rewrite Ehi3, Ehi2; reflexivity)
  HK3 HGK3 ltac:(intros a _ Hf; exact Hf) ltac:(intros a _ Hf; exact Hf)
  ltac:(unfold decode_off_win in Hoff; rewrite Hsp1; lia) HSRCT H60) as [HSRC3 KF3].
assert (HGA3 : garr8 segs (mrestrict (w_H W3) mem3) p (map DSpec.bz frame)).
{ apply (ics_garr8_xw (w_H W2) (w_H W3) (ms_mem msT) mem3 p _ HGAT). intros a Ha. rewrite length_map in Ha.
  exact (KF3 a Ha). }
(* the running kept fact *)
assert (HK4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - IOSEND_STK) (spZ regs)
                 (iosend_wr (Z.of_nat (length frame)))).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem msT) W3 mem3
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
assert (HTW3 : tw_at TMAP_A (aview segs (w_H W3) mem3) (ios_B0 Bw)).
{ apply (tw_kept TMAP_A _ _ _ HTWT). intros x Hx. exact (HGK3 x (ics_tw_in_G x Hx)). }
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
unfold ios_at_csf.
replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) by (unfold IOS_F_OFF; lia).
split; [exact HCUR3|]. split; [exact HSV3|]. split; [exact HR3|]. split; [exact H8113|].
split; [exact HSF3|].
split; [exact (ics_sf_src STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 mem3 md4 (k + 0) (spZ regs - 152) HJ3
          ltac:(lia) ltac:(lia))|].
split; [exact HGA3|]. split; [exact HSRC3 | exact HTW3].
Qed.

End icsw.
