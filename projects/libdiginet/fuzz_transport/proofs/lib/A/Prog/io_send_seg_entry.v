(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module paths and module names changed; 409 of its 501 lines of code are new or changed and 986 lines of the source are left out. *)
(* io_send_seg_entry: the entry stretch of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry
   0x82d60 = TImgA.v ti_io_send timg_A; the statement is lib/A/Prog/io_send_cg.v transport_io_send_cg_holds_stmt),
   from the entry to the cut IOS_PARSE (0x82db8, lib/A/Prog/io_send_seg_cut.v).

   The code (io_send_cg.v header, lines 73-85; listing slots 1807-1828 of lib/A/Prog/DgnTransportList.v):
     0x82d60 - 0x82d84  sp = sp - 160 (IOSEND_FRAME); ra at sp + 152, s0 .. s7 at sp + 144 .. sp + 88 (IOS_SAVED);
     0x82d88 - 0x82d8c  s0 = a2 = len, s1 = a1 = p;
     0x82d90 - 0x82d9c  a0 = the GOT word 0xa4090 (object 1), s4 = the cell 0xac9f8 it points to (object 93): the
                        shadow base SHADOW_OFF;
     0x82da0 - 0x82da4  s3 = the 1-byte unsigned load of g_fail_next (object 24 = TA_g_fail_next; no instrumented
                        check), then the 1-byte store of 0 there;
     0x82da8 - 0x82db4  a0 = sp + 8, a1 = 0, a2 = 80, `jal` __asan_memset, return address 0x82db8.
   No instrumented check and no error path is on this stretch.

   The walk, as lib/A/Prog/diginet_session_config_default.v (E2) walks its first run and its call:
     run 1 (0x82d60 .. 0x82db4)  a run of TransportGRunA.v paj_run_x over the caller's G journal, from the symbolic
                                 state ient_regions (the 160-byte frame below sp, the shadow base's GOT word and cell,
                                 and the byte of g_fail_next, whose chunk is the world's byte as atom 33, read from
                                 the world relation by TWorldG.v tw_read_val at the row TMAP_A_g_fail_next) and the
                                 empty shadow entry; its write right awr_ok_x: the frame is a byte of the caller's
                                 window (awr_byte), the two image cells have no writable byte, g_fail_next's byte is
                                 a byte of G;
     __asan_memset (sp + 8, 0, 80)  TransportGCg.v gx_intrin_at: the destination is io_send's own machine frame, a
                                 byte of the caller's window above the call's ESTACK window (transport_twr_ok_g_intro,
                                 its awr_byte case); its two shadow facts from DgnTransportCg.v stack_zshadow_ra at
                                 the call's AR state (the machine stack's shadow is 0); amem_range: a stack range.
   No symbolic state is carried past the call: the cut is stated as plain facts (io_send_seg_cut.v ios_at_parse), each
   read from the run's last state (registers, chunks) and carried across the memset by its post (aregs_preserved, the
   bytes outside its destination and its ESTACK window kept).

   THE CUT (io_send_seg_cut.v ios_at_parse, at the state (ly2, S2, W2, mem2, md2) with registers regs2 reached at
   transport_text + IOS_PARSE; the entry stretch produces it at ly2 = lyc, S2 = Sc, W2 = W):
     - ios_cur: the journal from the entry with no event, frames S2 = frames Sc, the caller's blocks (Permutation),
       mo_le MT Sc S2 0, and acall_kept_g G_HARNESS over [spZ regs - IOSEND_STK, spZ regs) and
       iosend_wr (length frame);
     - ios_saved W2 mem2 regs: ra, s0 .. s7 of the entry as rdword facts at spZ regs - 8 .. spZ regs - 72;
     - ios_regs regs regs2 p frame (g_fail_next Bw): sp = spZ regs - 160, gp, tp kept, s0 = len, s1 = p,
       s3 = g_fail_next Bw, s4 = SHADOW_OFF; and s8 .. s11 (registers 24 .. 27) equal to the entry's;
     - the SF_SIZE = 80 bytes at spZ regs - IOSEND_FRAME + IOS_F_OFF (f) read 0;
     - tw_at TMAP_A (aview segs (w_H W2) mem2) (ios_B0 Bw), the world after the store at 0x82da4;
     - garr8 of the frame at p, trans_src_ok B ly2 S2 W2 mem2 p (length frame), trans_rom_view_rd W2 mem2.
   The lemma (ios_entry): from io_send_seg_cut.v ios_laws and ios_fix, whatever holds at every state satisfying
   ios_at_parse holds at the entry configuration. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base, 33 the byte of g_fail_next. Regions: the 160-byte
   frame below sp, the shadow base's GOT word (object 1) and its cell (object 93), and the byte of g_fail_next
   (object 24), writable (a byte of G), whose chunk is atom 33. The load of g_fail_next names object 24 (PLdHi); the
   store after it is a plain word, `sb zero, 904(a1)`, with a1 the high part A_HI 48 of the same address: the alias
   (A_HI 48) + 904 = (A_OBJ 24) + 0 lets the run find the region (ient_alias). *)
Definition ient_fail_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 24)) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition ient_regions : smem := [stack_region IOSEND_FRAME; got_regionP; bcell_regionP 32; ient_fail_region].
Definition ient_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 255 0);
           (A_OBJ 24, mkAF TA_g_fail_next TA_g_fail_next 5)] [] [(SOff (A_HI 48) 904, SOff (A_OBJ 24) 0)].
Definition ss_ient : sstate := mkSS AF_io_send sr_atoms ient_regions None ient_facts.
(* No instrumented check on the stretch: the empty shadow entry; the shadow base of the token engine. *)
Definition IENT_SH : list shent := [].
Definition IENT_Bx : sv := SOff 32 0.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ient_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ient_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac ient_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* g_fail_next's byte is a byte of G. *)
Lemma ient_inG_fail : forall a, TA_g_fail_next <= a < TA_g_fail_next + 1 -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TA_g_fail_next, 1).
split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_fail_next) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma ient_tw_in_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof.
intros x (o & b & n & Hin & Hx). unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The write rights of the run: the frame below sp (inside the caller's stack window), the two read-only image
   regions (no writable byte), and g_fail_next's byte (a byte of G). *)
Ltac ient_awr UspE U24E :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite UspE in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24E in Ha; apply ient_inG_fail; lia |];
  apply awr_ok_x_nil.

(* An aview equality is an mbyte equality of the restricted memories. *)
Lemma ient_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H m') a) as [b1|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b2|];
  cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* garr8 at a later memory that keeps the range's bytes. *)
Lemma ient_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) p l,
  garr8 tfibsegs (mrestrict H m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H m') p l.
Proof.
intros H m m' p l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros i Hi. assert (Ei : i = 0%nat) by lia. subst i.
rewrite (ient_mbyte_of_aview H m m' (p + Z.of_nat j + Z.of_nat 0)).
- exact (Hv 0%nat Hi).
- apply Hk. lia.
Qed.

(* A saved word: the 8-byte chunk of a register's value, read as a word of the view. *)
Lemma ient_save_rd : forall E (H : word -> bool) m sp off e (v : word),
  YP09.chunk_ok tfibsegs E (mrestrict H m) sp (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = v ->
  rdword (aview tfibsegs H m) (sp + off) = Some (bv_unsigned v).
Proof.
intros E H m sp off e v Hc He.
pose proof (bv_unsigned_in_range 64 v) as Rv. change (bv_modulus 64) with (2 ^ 64) in Rv.
apply AF0x.val_mem_rdword; [exact Rv|].
exact (val_of_chunk_ok tfibsegs E (mrestrict H m) sp off 8%N e (bv_unsigned v) Hc
  ltac:(rewrite He; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* One saved word of IOS_SAVED, from the frame region's chunks HC (forall c, In c cs -> chunk_ok ..) and the
   valuation's registers EE. *)
Ltac ient_save HC EE :=
  lazymatch goal with |- rdword (aview _ _ _) (?sp - ?d) = Some (bv_unsigned (YK11.getr _ (Z_to_bv 5 ?r))) =>
    replace (sp - d) with (sp + - d) by lia;
    eapply ient_save_rd;
    [ apply HC; cbn [In]; repeat (first [left; reflexivity | right])
    | lazymatch goal with |- sv_denot _ (SOff ?n 0) = _ =>
        cbn [sv_denot]; rewrite (EE n (Z_to_bv 5 r) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ]
  end.

(* The world after the store of 0 at g_fail_next, in TWorldG.v tw_write's form. *)
Lemma ient_B0 : forall Bw, ios_B0 Bw = TW.upd Bw (TW.OFF_g_fail_next + 0) (TW.put 1 0).
Proof. intros Bw. unfold ios_B0, TW.set_g_fail_next. rewrite Z.add_0_r. reflexivity. Qed.

Section ientw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma ient_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 24) = TA_g_fail_next.
Proof. vm_compute. repeat split. Qed.

(* The return address of the call of __asan_memset is the cut IOS_PARSE. *)
Lemma ient_pc : Z_to_bv 64 (BASE + 6996) = w64 (transport_text + IOS_PARSE).
Proof. unfold w64. f_equal; try (vm_compute; reflexivity). Qed.

(* The two image regions hold what transport_cells says they hold, at any AR state. *)
Lemma ient_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct ient_vals as (V1 & V93 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (Rgot : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (Rcell : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
    [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the byte of g_fail_next. *)
Definition ient_E (regs : bvmap 5 word) (fb : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 fb]).

(* The alias of the run's facts: the high part of g_fail_next's address plus the store's offset is the object. *)
Lemma ient_alias : forall E, img_env VAL A_LIM E -> sv_denot E (SOff (A_HI 48) 904) = sv_denot E (SOff (A_OBJ 24) 0).
Proof.
intros E HE. cbn [sv_denot].
rewrite (HE (A_HI 48) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
rewrite (HE (A_OBJ 24) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
f_equal; try (vm_compute; reflexivity).
Qed.

(* The entry state and its (empty) shadow entry. *)
Lemma ient_entry : forall ly S (W : world segs) regs mem md fb,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - IOSEND_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> 0 <= fb < 256 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TA_g_fail_next + 0) 1 fb ->
  st_ok_pi segs VAL (ient_E regs fb) ss_ient
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_io_send)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs IENT_Bx IENT_SH (ient_E regs fb) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md fb HCELLS HAR Hpres Hsp Hsp16 Hf Vf.
  assert (EF : TA_g_fail_next = 6156576) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (E2 : ew (ient_E regs fb) 2 = YK11.getr regs 2) by (unfold ient_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew (ient_E regs fb) 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E32 : ew (ient_E regs fb) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold ient_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew (ient_E regs fb) 33 = Z_to_bv 64 fb)
    by (unfold ient_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U33 : bv_unsigned (ew (ient_E regs fb) 33) = fb) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (EOB : forall j, (j < 95)%nat -> ew (ient_E regs fb) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold ient_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (ient_img_ok ly S W mem md (ient_E regs fb) HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 93%nat ltac:(lia)) E32)
    as [RG RC].
  destruct ient_vals as (V1 & V93 & V24).
  assert (VB : forall n v0, ew (ient_E regs fb) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (ient_E regs fb) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B24 : base_val (ient_E regs fb) (Some (A_OBJ 24)) = TA_g_fail_next)
    by (apply VB; [rewrite (EOB 24%nat ltac:(lia)), V24; reflexivity | rewrite EF; lia]).
  assert (U24 : bv_unsigned (ew (ient_E regs fb) (A_OBJ 24)) = TA_g_fail_next) by exact B24.
  split.
  - rewrite restrict_mkst_fx. unfold ss_ient, ient_regions.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC |]]].
      * unfold stack_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. rewrite FF.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_nil].
        unfold ient_fail_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite B24. split; [rewrite EF; lia|]. split; [rewrite EF; lia|]. split.
        -- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_g_fail_next + o) G_HARNESS_rw).
           apply ient_inG_fail. lia.
        -- constructor; [|constructor].
           apply (chunk_ok_val segs (ient_E regs fb) _ TA_g_fail_next 0 1 (SOff 33 0) fb);
           [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vf].
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, ient_fail_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (EOB 93%nat ltac:(lia))) by (rewrite V93; unfold FCells.CELL_K; lia).
      rewrite B24.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V93. unfold FCells.GOT_CELL_K, FCells.CELL_K in *. rewrite FF, EF.
      repeat split; first [exact I | lia].
    + unfold ient_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U24, U33, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I;
        first [lia | rewrite EF; reflexivity | apply ient_alias; unfold ient_E; apply Eimg_env].
  - unfold sh_ok, IENT_SH. constructor.
Qed.

(* The walk's valuation agrees with the entry registers below atom 32. *)
Lemma ient_agree : forall regs fb, env_agree 32 (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 fb]) (ient_E regs fb).
Proof.
  intros regs fb. split.
  - intros n Hn. unfold ient_E. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
  - reflexivity.
Qed.

(* The entry stretch: from the entry configuration to the cut IOS_PARSE. *)
Lemma ios_entry : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
    p frame Bw (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  (forall ly2 S2 (W2 : world segs) mem2 md2 regs2,
     ios_at_parse B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_PARSE) regs2 mem2 md2) Q) ->
  SRr segs W (@cfg_at fx segs (TI.ti_io_send timg_A) regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Q HL HF HK.
destruct HL as (HCELLS & _ & LAWS & MTL & HGX & _ & HAI0 & _).
destruct HF as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff & Hfat
  & Hfail & Hrom & Htw & _ & _ & _).
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8496) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EF : TA_g_fail_next = 6156576) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hm16 : (spZ regs - 160 - sp0) mod 16 = 0).
{ replace (spZ regs - 160 - sp0) with (spZ regs - sp0 + (-10) * 16) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity. }
assert (Hwin : forall a, spZ regs - IOSEND_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
(* the byte of g_fail_next, as the world holds it *)
pose proof (TWL.u_at_range Bw TW.OFF_g_fail_next 1) as Rf. change (8 * Z.of_nat 1) with 8 in Rf.
change (TW.u_at Bw TW.OFF_g_fail_next 1) with (TW.g_fail_next Bw) in Rf.
assert (Vf : YI04.val_mem segs (mrestrict (w_H W) memc) (TA_g_fail_next + 0) 1 (TW.g_fail_next Bw))
  by exact (tw_read_val segs (mrestrict (w_H W) memc) TMAP_A Bw TW.OFF_g_fail_next TA_g_fail_next 1 0 1
    TMAP_A_ok Htw TMAP_A_g_fail_next ltac:(lia) ltac:(lia)).
set (fb := TW.g_fail_next Bw) in *.
(* the valuation of the walk and its atoms *)
set (E0 := ient_E regs fb).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ient_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0, ient_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E0, ient_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 fb)
  by (unfold E0, ient_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
destruct ient_vals as (V1 & V93 & V24).
assert (U24 : bv_unsigned (ew E0 (A_OBJ 24)) = TA_g_fail_next).
{ unfold E0, ient_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V24.
  apply unsigned_lit_small. rewrite EF. lia. }
assert (U24' : bv_unsigned (ew E0 265%nat) = TA_g_fail_next) by exact U24.
destruct (ient_entry lyc Sc W regs memc mdc fb HCELLS HAR ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16
  ltac:(lia) Vf) as [HS SHOK].
fold E0 in HS, SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_io_send)) memc (YK11.seg_rom segs)) mdc) Qx)
end.
(* run 1, +0x00 .. +0x54: the frame, the nine saves, s0 = len, s1 = p, the shadow base into s4, g_fail_next's byte
   into s3 and the store of 0 there, the arguments, `jal __asan_memset`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ient_awr Usp U24'. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
(* the bytes the run wrote: its frame and g_fail_next's byte *)
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) ->
  ~ (TA_g_fail_next <= a < TA_g_fail_next + 1) -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _
    (fun x => (spZ regs - 160 <= x < spZ regs) \/ (TA_g_fail_next <= x < TA_g_fail_next + 1)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta.
  ient_win Hin Hx ltac:(rewrite ?Usp, ?U24' in Hx; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the run's last state: the nine saved words (region 0) and the 0 stored at g_fail_next (region 3) *)
pose proof (YC4b.st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ _ 3%nat _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG0, RG3.
destruct RG0 as (_ & _ & _ & HC0). destruct RG3 as (_ & _ & _ & HC3).
cbn [YP09.r_base YP09.r_chunks base_val] in HC0, HC3.
rewrite Usp in HC0. rewrite U24' in HC3.
rewrite Forall_forall in HC0.
pose proof (Forall_inv HC3) as HCk3. clear HC3.
assert (SV1 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs - fst o) =
          Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) IOS_SAVED).
{ unfold IOS_SAVED.
  repeat (apply Forall_cons; [cbn [fst snd]; ient_save HC0 EE |]).
  apply Forall_nil. }
assert (VF1 : aview segs (w_H W) (ms_mem ms) TA_g_fail_next = Some 0).
{ pose proof (val_of_chunk_ok segs E0 (mrestrict (w_H W) (ms_mem ms)) TA_g_fail_next 0 1%N (SLit 0) 0 HCk3 eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia) 0%nat ltac:(cbn; lia)) as Vm.
  unfold aview. replace TA_g_fail_next with (TA_g_fail_next + 0 + Z.of_nat 0) by lia. rewrite Vm. reflexivity. }
clear HC0 HCk3.
(* the registers at the call *)
pmkst HS.
ient_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (spZ regs - 152)) Q10 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ient_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
ient_reg HS (Z_to_bv 5 12) (Z_to_bv 64 80) Q12 ltac:(reflexivity).
ient_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 160)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ient_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 6996)) R1 ltac:(apply codeptr_val; exact HEI).
ient_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ient_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ient_reg HS (Z_to_bv 5 8) (w64 (Z.of_nat (length frame))) R8
  ltac:(cbn [sv_denot]; rewrite (EE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
ient_reg HS (Z_to_bv 5 9) (w64 p) R9
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
ient_reg HS (Z_to_bv 5 19) (w64 fb) R19
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 20) (w64 SHADOW_OFF) R20
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) R24
  ltac:(cbn [sv_denot]; rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 25) (YK11.getr regs (Z_to_bv 5 25)) R25
  ltac:(cbn [sv_denot]; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) R26
  ltac:(cbn [sv_denot]; rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 27) (YK11.getr regs (Z_to_bv 5 27)) R27
  ltac:(cbn [sv_denot]; rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 160)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 160) by exact ESP.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (stack_zshadow_ra B lyc Sc W (ms_mem ms) md1 (spZ regs - 152) 80 HAR1 ltac:(lia)
  ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia)) as [HRA1 HHL1].
(* +0x54: __asan_memset (sp + 8, 0, 80) into io_send's own frame, through the G call kit. *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Qx) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HAI0 fx) TG.G_HARNESS W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k
    (spZ regs - 152) 0 80 (spZ regs - 160 - sp0) (Z_to_bv 64 (BASE + 6996)) HGX G_HARNESS_rw HJ Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp1. lia.
  - exact Hm16.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. left. split.
    + unfold awr_byte. left. lia.
    + rewrite Hsp1. lia.
  - unfold amem_range. right. lia.
  - exact HRA1.
  - intros _. exact HHL1.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
(* the cut's facts *)
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IOSEND_STK <= a < spZ regs) ->
  ~ (TA_g_fail_next <= a < TA_g_fail_next + 1) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha H1 H2. rewrite (Heff2 a Ha ltac:(lia) ltac:(lia)). apply KR1; [exact Ha | lia | exact H2]. }
assert (VF2 : aview segs (w_H W) mem2 TA_g_fail_next = Some 0).
{ rewrite (Heff2 TA_g_fail_next ltac:(rewrite EF; lia) ltac:(lia) ltac:(lia)). exact VF1. }
assert (KZ2 : forall i, 0 <= i < SF_SIZE ->
  aview segs (w_H W) mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF + i) = Some 0).
{ intros i Hi. unfold SF_SIZE in Hi.
  replace (spZ regs - IOSEND_FRAME + IOS_F_OFF + i) with (spZ regs - 152 + i) by (unfold IOS_F_OFF; lia).
  rewrite (Hset2 i Hi). reflexivity. }
assert (SV2 : ios_saved W mem2 regs).
{ unfold ios_saved. rewrite Forall_forall in SV1 |- *. intros o Ho. rewrite <- (SV1 o Ho).
  assert (Hd : 8 <= fst o <= 72)
    by (unfold IOS_SAVED in Ho; cbn [In] in Ho; repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]); destruct Ho).
  apply rdword_ext. intros j Hj. apply Heff2; lia. }
assert (HR : ios_regs regs regs2 p frame fb).
{ unfold ios_regs.
  split; [refine (eq_trans (HP2 2 ltac:(unfold acallee_saved; lia)) _); exact Q2|].
  split; [refine (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) _); exact (eq_trans R3 (eq_sym Hgp))|].
  split; [refine (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) _); exact (eq_trans R4 (eq_sym Htp))|].
  split; [refine (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) _); exact R8|].
  split; [refine (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) _); exact R9|].
  split; [refine (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) _); exact R19|].
  refine (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) _); exact R20. }
assert (H811 : forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
  assert (Hc : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]]; [exact R24 | exact R25 | exact R26 | exact R27]. }
assert (HTW : tw_at TMAP_A (aview segs (w_H W) mem2) (ios_B0 Bw)).
{ rewrite ient_B0.
  apply (tw_write TMAP_A (aview segs (w_H W) memc) (aview segs (w_H W) mem2) Bw TW.OFF_g_fail_next TA_g_fail_next
    1 0 1 0 TMAP_A_ok Htw TMAP_A_g_fail_next ltac:(lia) ltac:(lia)).
  - intros j Hj. assert (Ej : j = 0%nat) by lia. subst j. cbn [Z.of_nat]. rewrite !Z.add_0_r. rewrite VF2.
    reflexivity.
  - intros x Hx Hn. pose proof (GLOW x (ient_tw_in_G x Hx)) as Hl. unfold kLowMemEnd in Hl.
    apply KA2; [lia | lia | lia]. }
assert (KF : forall a, p <= a < p + Z.of_nat (length frame) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha.
  destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc p (Z.of_nat (length frame)) HAR Hsrc ltac:(lia))
    as [Pl | Pl].
  - apply KA2; [lia | unfold decode_off_win in Hoff; lia |].
    intros Hta. destruct Hfat as [Hng | Hgs]; [exact (Hng a Ha (ient_inG_fail a Hta))|].
    unfold TA_g_s in Hgs. rewrite EF in Hta. lia.
  - apply KA2; [lia | unfold decode_off_win in Hoff; lia |].
    intros Hta. destruct Hfat as [Hng | Hgs]; [exact (Hng a Ha (ient_inG_fail a Hta))|].
    unfold TA_g_s in Hgs. rewrite EF in Hta. lia. }
assert (KS : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) mem2 s = aview segs (w_H W) memc s).
{ intros s Hs. apply KA2; [lia | lia | rewrite EF; lia]. }
assert (HGA2 : garr8 segs (mrestrict (w_H W) mem2) p (map DSpec.bz frame)).
{ apply (ient_garr8_kept (w_H W) memc mem2 p _ Hgarr). intros a Ha. rewrite length_map in Ha. exact (KF a Ha). }
assert (HSR2 : trans_src_ok B lyc Sc W mem2 p (Z.of_nat (length frame))).
{ eapply trans_src_ok_view; [exact Hsrc | exact KF | exact KS]. }
assert (HROM2 : trans_rom_view_rd W mem2).
{ intros a Ha. rewrite <- (Hrom a Ha). pose proof (trans_ro_rd_bounds a Ha) as Rb.
  apply KA2; [lia | lia | rewrite EF; lia]. }
assert (HK2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 (spZ regs - IOSEND_STK) (spZ regs)
                 (iosend_wr (Z.of_nat (length frame)))).
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc mem2
    (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame)))
    (fun a => (spZ regs - IOSEND_STK <= a < spZ regs) \/ (TA_g_fail_next <= a < TA_g_fail_next + 1)) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. apply KA2; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
  - intros a Ha. apply Hgr2. apply GA1. exact Ha.
  - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. rewrite EF in Hw. lia.
  - intros b m i Hb Hi [Hw | Hw].
    + exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    + unfold iosend_wr. left. unfold twa_fld. lia.
  - intros a [Hw | Hw] Hi HnG _ _.
    + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
    + apply HnG. apply ient_inG_fail. exact Hw.
  - intros cid pos a Hin Hr [Hw | Hw].
    + exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    + unfold iosend_wr. left. unfold twa_fld. lia. }
assert (HCUR : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame lyc Sc W mem2 md2).
{ unfold ios_cur. rewrite Z.add_0_r.
  split; [exact HJ2|]. split; [reflexivity|]. split; [apply Permutation_refl|].
  split; [exact (mo_le_refl MT MTL Sc) | exact HK2]. }
(* the cut *)
rewrite ient_pc.
specialize (HK lyc Sc W mem2 md2 regs2). unfold cfg_at in HK. apply HK.
unfold ios_at_parse.
split; [exact HCUR|]. split; [exact SV2|]. split; [exact HR|]. split; [exact H811|].
split; [exact KZ2|]. split; [exact HTW|]. split; [exact HGA2|]. split; [exact HSR2 | exact HROM2].
Qed.

End ientw.
