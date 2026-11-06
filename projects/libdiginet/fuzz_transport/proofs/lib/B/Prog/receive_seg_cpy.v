(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1223 of its 1346 lines of code are new or changed and 1016 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_poll_seg_head.v, with its module paths and module names changed; 422 of its 475 lines of code are new or changed and 1293 lines of the source are left out. *)
(* receive_seg_cpy: Lemma recv_cpy : recv_cpy_stmt (lib/B/Prog/receive_seg_cut.v), the cpy piece of the image-B ASan
   walk of receive (fuzz_transport.asan-ubsan 0x836a8 = transportb_sigma TB_receive, AF_receive = 0x2408 of
   lib/B/Prog/DgnTransportBList.v), from the mal cut RECV_MAL (+0x038, 0x836e0) to the opb cut RECV_OPB (+0x054,
   0x836fc). The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) at k + 1
   events. Every run is lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x from a symbolic state of the cut's
   registers (atoms 0 .. 31) with no region and no fact (rcb_st): the code of the piece reads and writes no memory,
   so a run keeps every byte (rcb_kept_run).
     +0x038            `beqz a0, +0x150` (the trap at 0x83830): a0 = a (recv_regs_mal) and 4096 <= a (recv_cur), so
                       the taken arm of DgnTransportBPaLib.v paj_branch is refuted.
     +0x03c            `mv s0, a0`.
     +0x040            `beqz s1, +0x14`: s1 = n. Taken (n = 0): the run reaches RECV_OPB with no copy; the bytes are
                       [] and recv_blk of [] holds (garr8_nil).
     +0x044 .. +0x04c  a0 = s0 = a, a1 = s4 = p, a2 = s1 = n.
     +0x050            `jal __asan_memcpy` (return RECV_OPB): TransportGCg.v gx_intrin_at at OCpy from sp - 128. The
                       destination [a, a + n) lies in the block (a, max (n, 1)) the malloc added to the current state;
                       each byte is an awr_byte of the journal (a block of the current state that is no block of the
                       journal's start state, or, when it is one, a byte of the footprint by
                       lib/A/Prog/receive_seg_alloc.v gx_start_fp: the block is none of the caller's blocks,
                       rcb_blk_apart through YCbq.v sep_blocks_perm) and lies below the call's ESTACK window
                       (TransportGCg.v transport_twr_ok_g_intro); its amem_range, range_addressable and
                       shadow_hull_vis are the block's (YCbq.v amem_range_of_block, range_addressable_of_block,
                       shadow_hull_vis_of_block). The source [p, p + n): recv_src's trans_src_ok gives decode_rd_ok
                       (DgnTransportBCg.v trans_src_ok_rd, moved to the call's memory by trans_rd_ok_view); it lies
                       off the ESTACK window below sp - 128 by recv_fix's decode_off_win at RECV_STK = 128 + ASTACK,
                       apart from the destination by recv_src's disjunction; n <= 65535.
   At RECV_OPB (both arms): recv_blk (after the copy the destination's bytes are the source's: rcb_garr8_shift);
   recv_cur's acall_kept_g kept (rcb_kept_cpy: lib/A/Prog/TransportGFrame.v dk_kept_step_gw over the block's bytes
   and the ESTACK window below sp - 128; the block is none of the caller's blocks, frame bytes, frame shadow bytes or
   image bytes and lies below alloc_ceiling, the window lies in [sp - RECV_STK, sp)); the six saved words at
   sp - 48 .. sp - 1 and tw_at Bw (bytes of G: image bytes below kLowMemEnd, no block byte by YCbq.v blk_img) kept;
   recv_regs_opb (rcb_regs_opb: s0 = a; every other register the cut names as at the mal cut, kept by the runs and by
   the memcpy's aregs_preserved).
   Image A's twin is lib/A/Prog/receive_seg_cpy.v; its byte and block lemmas are stated at image A's segments, so the
   ones this piece needs are restated here over any segments (rcb_mbyte_eq, rcb_garr8_shift, rcb_kept_run,
   rcb_blk_apart). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame receive_seg_alloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module AGF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGFrame.
Module ALC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_alloc.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states and the machinery                               *)
(* ------------------------------------------------------------------ *)

(* Every run of the piece starts from the registers of a concrete machine state (atoms 0 .. 31), with no region and
   no fact. *)
Definition rcb_E {rc : YM05.RunCeil} (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition rcb_ss (off : Z) : sstate := mkSS (AF_receive + off) sr_atoms [] None (mkFacts [] [] []).

(* The value of register rr in the machine state of a symbolic state HS. *)
Ltac rcb_reg HS rr v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
      assert (H : YK11.getr (ms_regs msx) rr = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx rr HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
      assert (H : YK11.getr (ms_regs msx) rr = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx rr HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "rcb_reg: no match for" T; fail
  end.
(* A register the run kept: atom nn of the start state, whose register value G gives. *)
Ltac rcb_kreg EE nn rr G := cbn [sv_denot]; rewrite (EE nn rr eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G.
(* A register the run kept, as the start state's register. *)
Ltac rcb_same EE nn rr := cbn [sv_denot]; rewrite (EE nn rr eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity.
(* No region: no write right to give. *)
Ltac rcb_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma rcb_st : forall (Wx : world tfibsegs) regs mem off,
  st_ok_pi tfibsegs (@pa_val _ transportb_listing PI_transportb) (rcb_E regs) (rcb_ss off)
    (restrict (w_H Wx) (@YK11.mkst fx regs
      (Z_to_bv 64 (@pa_val _ transportb_listing PI_transportb A_TEXT + (AF_receive + off))) mem
      (YK11.seg_rom tfibsegs))).
Proof.
intros Wx regs mem off. rewrite restrict_mkst_fx. unfold rcb_ss.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

(* A run from a state with no region keeps every byte of the view. *)
Lemma rcb_kept_run : forall (segs : list Segment) E rs (Wc : world segs) (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') -> rs = [] ->
  forall x, aview segs (w_H Wc) m' x = aview segs (w_H Wc) m x.
Proof.
intros segs E rs Wc m m' HFr -> x.
rewrite (aview_wrap64 segs (w_H Wc) m' x), (aview_wrap64 segs (w_H Wc) m x).
pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Hx.
apply (kept_of_frame E [] (w_H Wc) m m' (fun _ => False) HFr); [| exact Hx | intros []].
intros b wlo whi y Hin _. cbn in Hin. destruct Hin.
Qed.
End st.

(* ------------------------------------------------------------------ *)
(* Bytes, blocks and the kept memory                                   *)
(* ------------------------------------------------------------------ *)

Section bytes.
Variable segs : list Segment.

(* Two bytes with the same view value are the same raw byte. *)
Lemma rcb_mbyte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) x y,
  aview segs H' m' y = aview segs H m x ->
  mbyte segs (mrestrict H' m') y = mbyte segs (mrestrict H m) x.
Proof.
intros H H' m m' x y E. unfold aview in E. revert E.
destruct (mbyte segs (mrestrict H' m') y) as [b'|]; destruct (mbyte segs (mrestrict H m) x) as [b|];
  cbn [option_map]; intros E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A byte array at p read again at a, when the view at a + i is the view at p + i. *)
Lemma rcb_garr8_shift : forall (H H' : word -> bool) (m m' : word -> option byte) p a (l : list Z),
  garr8 segs (mrestrict H m) p l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs H' m' (a + i) = aview segs H m (p + i)) ->
  garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' p a l Hg Hv j Hj. destruct (Hg j Hj) as [Hm Hr]. split; [|exact Hr].
intros kk Hk. assert (Ek : kk = 0%nat) by lia. subst kk.
specialize (Hm 0%nat Hk). cbn [Z.of_nat] in Hm |- *. rewrite Z.add_0_r in Hm |- *.
rewrite <- Hm. apply rcb_mbyte_eq. exact (Hv (Z.of_nat j) ltac:(lia)).
Qed.
End bytes.

(* The opb cut's registers: s0 = a and every other register the cut names as at the mal cut. *)
Lemma rcb_regs_opb : forall (regs regs2 regsX : bvmap 5 word) p by_poll a (bytes : list byte),
  recv_regs_mal regs regs2 p by_poll a bytes ->
  YK11.getr regsX (Z_to_bv 5 2) = YK11.getr regs2 (Z_to_bv 5 2) ->
  YK11.getr regsX (Z_to_bv 5 3) = YK11.getr regs2 (Z_to_bv 5 3) ->
  YK11.getr regsX (Z_to_bv 5 4) = YK11.getr regs2 (Z_to_bv 5 4) ->
  YK11.getr regsX (Z_to_bv 5 9) = YK11.getr regs2 (Z_to_bv 5 9) ->
  YK11.getr regsX (Z_to_bv 5 18) = YK11.getr regs2 (Z_to_bv 5 18) ->
  YK11.getr regsX (Z_to_bv 5 19) = YK11.getr regs2 (Z_to_bv 5 19) ->
  YK11.getr regsX (Z_to_bv 5 21) = YK11.getr regs2 (Z_to_bv 5 21) ->
  YK11.getr regsX (Z_to_bv 5 22) = YK11.getr regs2 (Z_to_bv 5 22) ->
  YK11.getr regsX (Z_to_bv 5 23) = YK11.getr regs2 (Z_to_bv 5 23) ->
  YK11.getr regsX (Z_to_bv 5 24) = YK11.getr regs2 (Z_to_bv 5 24) ->
  YK11.getr regsX (Z_to_bv 5 25) = YK11.getr regs2 (Z_to_bv 5 25) ->
  YK11.getr regsX (Z_to_bv 5 26) = YK11.getr regs2 (Z_to_bv 5 26) ->
  YK11.getr regsX (Z_to_bv 5 27) = YK11.getr regs2 (Z_to_bv 5 27) ->
  YK11.getr regsX (Z_to_bv 5 8) = w64 a ->
  recv_regs_opb regs regsX by_poll a bytes.
Proof.
intros regs regs2 regsX p by_poll a bytes
  ((Q2 & Q3 & Q4 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27) & _ & Q9 & Q18 & Q19 & _ & _)
  R2 R3 R4 R9 R18 R19 R21 R22 R23 R24 R25 R26 R27 R8.
unfold recv_regs_opb, recv_regs_keep.
exact (conj (conj (eq_trans R2 Q2) (conj (eq_trans R3 Q3) (conj (eq_trans R4 Q4) (conj (eq_trans R21 Q21)
  (conj (eq_trans R22 Q22) (conj (eq_trans R23 Q23) (conj (eq_trans R24 Q24) (conj (eq_trans R25 Q25)
  (conj (eq_trans R26 Q26) (eq_trans R27 Q27))))))))))
  (conj R8 (conj (eq_trans R9 Q9) (conj (eq_trans R18 Q18) (eq_trans R19 Q19))))).
Qed.

Section kit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* The malloc's block (a, M), at a state whose blocks are the caller's with it added, is apart from each of the
   caller's blocks (and so none of them: rcb_blk_apart at (b, m) = (a, M) contradicts 1 <= req_size M). *)
Lemma rcb_blk_apart : forall ly2 S2 (W2 : world segs) mem2 md2 lyc Sc a M b m,
  AR segs B ly2 S2 W2 mem2 md2 -> Permutation (ablocks B ly2 S2) ((a, M) :: ablocks B lyc Sc) ->
  In (b, m) (ablocks B lyc Sc) -> a + req_size M <= b \/ b + req_size m <= a.
Proof.
intros ly2 S2 W2 mem2 md2 lyc Sc a M b m HAR Hp Hin.
apply in_split in Hin as (L1 & L2 & EL). rewrite EL in Hp.
assert (HP2 : Permutation (ablocks B ly2 S2) ((a, M) :: (b, m) :: L1 ++ L2)).
{ eapply Permutation_trans; [exact Hp|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm segs B LAWS ly2 S2 W2 mem2 md2 (a, M) (b, m) (L1 ++ L2) HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.
End kit.

Section kitB. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* What the call keeps, across a step that changes only the bytes [a, a + n) of the malloc's block (a, M) and the
   ESTACK window below sp (the memcpy). *)
Lemma rcb_kept_cpy : forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 mem3
    (sp lo hi a M n : Z) (E : Z -> Prop),
  AR segs B lyc Sc W memc mdc -> AR segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = frames Sc -> ly_F ly2 = ly_F lyc ->
  Permutation (ablocks B ly2 S2) ((a, M) :: ablocks B lyc Sc) -> 0 <= n <= M ->
  alloc_ceiling <= lo -> lo <= sp - ESTACK -> sp <= hi ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 lo hi E ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + n) -> ~ (sp - ESTACK <= x < sp) ->
     aview segs (w_H W2) mem3 x = aview segs (w_H W2) mem2 x) ->
  (forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) mem3 x) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem3 lo hi E.
Proof.
intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 mem3 sp lo hi a M n E HAR HAR2 Hfrs HlyF Hperm Hn Hlo Hlos Hhi HK
  KALL GR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EES : ESTACK = 4096) by reflexivity.
assert (HB2 : In (a, M) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 a M HAR2 HB2) as (_ & Ha4 & Hace & Haapp & _ & _ & HM).
pose proof (req_size_pos M ltac:(lia)) as [Hr1 Hr2].
apply (AGF.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 mem3 lo hi E
  (fun x => (a <= x < a + n) \/ (sp - ESTACK <= x < sp)) HAR HK).
- intros x Hx Hn'. apply KALL; [exact Hx | intros H; apply Hn'; left; exact H | intros H; apply Hn'; right; exact H].
- exact GR.
- intros x [Hx|Hx] Hc; lia.
- intros b m i Hb Hi [Hx|Hx]; exfalso.
  + pose proof (rcb_blk_apart segs B LAWS ly2 S2 W2 mem2 md2 lyc Sc a M b m HAR2 Hperm Hb) as Hd. lia.
  + destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hbc & _). lia.
- intros x [Hx|Hx] Hi _ _ _.
  + exact (blk_img segs B LAWS ly2 S2 W2 mem2 md2 a M x HAR2 HB2 ltac:(lia) Hi).
  + pose proof (transportb_segs_low x Hi) as Hl. unfold kLowMemEnd in Hl. lia.
- intros cid pos x Hin Hr [Hx|Hx]; exfalso.
  + assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; exact Hin).
    assert (Efa : frame_addr ly2 cid pos = frame_addr lyc cid pos) by (unfold frame_addr; rewrite HlyF; reflexivity).
    pose proof (sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 a M cid pos HAR2 HB2 Hin2) as Hd.
    rewrite Efa in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd1 : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    assert (Hd0 : 4096 / 8 <= frame_addr lyc cid pos / 8) by (apply Z.div_le_mono; lia).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Haapp.
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd1. change (4096 / 8) with 512 in Hd0.
    lia.
  + destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.
End kitB.

(* ------------------------------------------------------------------ *)
(* The cpy piece                                                       *)
(* ------------------------------------------------------------------ *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma recv_cpy : @recv_cpy_stmt fx rc B MT.
Proof.
unfold recv_cpy_stmt. intros OPB.
unfold recv_mal_at. intros HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T
  bytes Bw ch a Bw' ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HRES HSRC HTW HREGS.
pose proof HLAWS as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof HCALLS as (HAM & MCPY & MSET & HSRF & HPOLL & HMRX & HRX & HSET & HAF).
pose proof HFIX as (HJe & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & Hal & Hwlo & Hwhi & _ & _ & Hnb & _ & Hsrc0 & _).
pose proof HCUR as (HJ & Hfrs & Hperm & HMO & HK & HSV & Ha4).
pose proof HRES as ((Ha0 & Ha64) & _).
pose proof HSRC as (Hg8p & Hsrc).
pose proof HREGS as ((Q2 & Q3 & Q4 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27) & Q8 & Q9 & Q18 & Q19 & Q20 & Q10).
(* the journal's stack and layout facts *)
pose proof HJe as (_ & _ & (memSe & HJie & _) & _).
rewrite !Z.add_0_r in HJie.
pose proof HJie as (HARe & Hlye & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstke & _).
pose proof Hstke as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (_ & _ & (memS2 & HJi2 & _) & _).
rewrite !Z.add_0_r in HJi2.
pose proof HJi2 as (HAR2 & Hly2 & _).
assert (HlyF : ly_F ly2 = ly_F lyc).
{ destruct Hlye as (_ & _ & _ & _ & _ & Fe & _). destruct Hly2 as (_ & _ & _ & _ & _ & F2 & _).
  rewrite F2, Fe. reflexivity. }
clear HJie HJi2. clear Hlye Hly2 Hstke. clear memSe memS2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ERS : RECV_STK = 16512) by reflexivity.
assert (ERF : RECV_FRAME = 128) by reflexivity.
assert (EES : ESTACK = 4096) by reflexivity.
assert (Hspb : alloc_ceiling + 16512 <= spZ regs <= 2 ^ 47) by lia.
(* the malloc's block in the current state *)
assert (HB2 : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 HB2) as (_ & _ & Hbce & _ & _ & _ & _).
pose proof (req_size_pos (Z.max 1 (Z.of_nat (length bytes))) ltac:(lia)) as [Hrq1 Hrq2].
assert (Hfresh : ~ In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B lyc Sc)).
{ intros Hin. pose proof (rcb_blk_apart segs B LAWS ly2 S2 W2 mem2 md2 lyc Sc a _ a _ HAR2 Hperm Hin) as Hd. lia. }
assert (Q2' : YK11.getr regs2 (Z_to_bv 5 2) = w64 (spZ regs - RECV_FRAME)) by exact Q2.
assert (Q9' : YK11.getr regs2 (Z_to_bv 5 9) = w64 (Z.of_nat (length bytes))) by exact Q9.
assert (Q10' : YK11.getr regs2 (Z_to_bv 5 10) = w64 a) by exact Q10.
assert (Q20' : YK11.getr regs2 (Z_to_bv 5 20) = w64 p) by exact Q20.
(* the symbolic machinery, from a state at the mal cut *)
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
unfold RECV_MAL.
pose proof (rcb_st (fx := fx) (rc := rc) W2 regs2 mem2 0x38) as HS.
set (E0 := rcb_E regs2) in HS.
assert (EE0 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs2 rr)
  by (intros nn rr Hn; unfold E0, rcb_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HEI0 : img_env VAL A_LIM E0) by (unfold E0, rcb_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
(* +0x038: `beqz a0`, a0 = a *)
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* taken: a = 0, against 4096 <= a *)
  exfalso. cbn [branch_taken sv_denot] in Hc.
  rewrite (EE0 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
  apply bv_eqb_true_iff in Hc.
  assert (Hz : bv_unsigned (YK11.getr regs2 (Z_to_bv 5 10)) = 0)
    by (first [rewrite Hc; reflexivity | rewrite <- Hc; reflexivity]).
  rewrite Q10' in Hz. unfold w64 in Hz. rewrite unsigned_lit_small in Hz by lia. lia.
- (* not taken: `mv s0, a0`, up to `beqz s1` at +0x040 *)
  clear Hc.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { rcb_awr. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into ms1 end.
  pose proof (rcb_kept_run segs _ _ W2 _ _ HFr eq_refl) as KD1.
  pose proof (fun x => apresent_grows _ _ _ x HG) as GR1.
  clear HF HFr HG.
  (* +0x040: `beqz s1`, s1 = n *)
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  + (* taken: n = 0, to RECV_OPB with no copy *)
    cbn [branch_taken sv_denot] in Hc.
    rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
    apply bv_eqb_true_iff in Hc.
    assert (Hz : bv_unsigned (YK11.getr regs2 (Z_to_bv 5 9)) = 0)
      by (first [rewrite Hc; reflexivity | rewrite <- Hc; reflexivity]).
    rewrite Q9' in Hz. unfold w64 in Hz. rewrite unsigned_lit_small in Hz by lia.
    assert (Hlen0 : length bytes = 0%nat) by lia.
    clear Hc Hz.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) RECV_OPB.
    { rcb_awr. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mz) => rename mz into msF end.
    pose proof (rcb_kept_run segs _ _ W2 _ _ HFr eq_refl) as KD2.
    pose proof (fun x => apresent_grows _ _ _ x HG) as GR2.
    clear HF HFr HG.
    assert (KDF : forall x, aview segs (w_H W2) (ms_mem msF) x = aview segs (w_H W2) mem2 x)
      by (intros x; rewrite KD2; exact (KD1 x)).
    assert (GRF : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem msF) x)
      by (intros x Hx; exact (GR2 x (GR1 x Hx))).
    pmkst HS.
    rcb_reg HS (Z_to_bv 5 2) (YK11.getr regs2 (Z_to_bv 5 2)) R2 ltac:(rcb_same EE0 2%nat (Z_to_bv 5 2)).
    rcb_reg HS (Z_to_bv 5 3) (YK11.getr regs2 (Z_to_bv 5 3)) R3 ltac:(rcb_same EE0 3%nat (Z_to_bv 5 3)).
    rcb_reg HS (Z_to_bv 5 4) (YK11.getr regs2 (Z_to_bv 5 4)) R4 ltac:(rcb_same EE0 4%nat (Z_to_bv 5 4)).
    rcb_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 10)) R8 ltac:(rcb_same EE0 10%nat (Z_to_bv 5 10)).
    rcb_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) R9 ltac:(rcb_same EE0 9%nat (Z_to_bv 5 9)).
    rcb_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) R18 ltac:(rcb_same EE0 18%nat (Z_to_bv 5 18)).
    rcb_reg HS (Z_to_bv 5 19) (YK11.getr regs2 (Z_to_bv 5 19)) R19 ltac:(rcb_same EE0 19%nat (Z_to_bv 5 19)).
    rcb_reg HS (Z_to_bv 5 21) (YK11.getr regs2 (Z_to_bv 5 21)) R21 ltac:(rcb_same EE0 21%nat (Z_to_bv 5 21)).
    rcb_reg HS (Z_to_bv 5 22) (YK11.getr regs2 (Z_to_bv 5 22)) R22 ltac:(rcb_same EE0 22%nat (Z_to_bv 5 22)).
    rcb_reg HS (Z_to_bv 5 23) (YK11.getr regs2 (Z_to_bv 5 23)) R23 ltac:(rcb_same EE0 23%nat (Z_to_bv 5 23)).
    rcb_reg HS (Z_to_bv 5 24) (YK11.getr regs2 (Z_to_bv 5 24)) R24 ltac:(rcb_same EE0 24%nat (Z_to_bv 5 24)).
    rcb_reg HS (Z_to_bv 5 25) (YK11.getr regs2 (Z_to_bv 5 25)) R25 ltac:(rcb_same EE0 25%nat (Z_to_bv 5 25)).
    rcb_reg HS (Z_to_bv 5 26) (YK11.getr regs2 (Z_to_bv 5 26)) R26 ltac:(rcb_same EE0 26%nat (Z_to_bv 5 26)).
    rcb_reg HS (Z_to_bv 5 27) (YK11.getr regs2 (Z_to_bv 5 27)) R27 ltac:(rcb_same EE0 27%nat (Z_to_bv 5 27)).
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + RECV_OPB)) mm rom) mdx) Q) end.
    apply (OPB HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a
      Bw' ly2 S2 W2 (ms_mem msF) _ (ms_regs msF) HFIX).
    * split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact HMO|].
      split.
      { apply (AGF.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2
          (ms_mem msF) (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes) (fun _ => False) HARe HK).
        - intros x _ _. exact (KDF x).
        - exact GRF.
        - intros x [].
        - intros b m i _ _ [].
        - intros x [].
        - intros cid pos x _ _ []. }
      split; [|exact Ha4].
      refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KDF _)). exact Ho.
    * exact HRES.
    * unfold recv_blk. apply length_zero_iff_nil in Hlen0. rewrite Hlen0. apply garr8_nil.
    * apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW | intros x _; exact (KDF x)].
    * exact (rcb_regs_opb regs regs2 (ms_regs msF) p by_poll a bytes HREGS R2 R3 R4 R9 R18 R19 R21 R22 R23 R24
        R25 R26 R27 (eq_trans R8 Q10')).
  + (* not taken: n <> 0 *)
    cbn [branch_taken sv_denot] in Hc.
    rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
    rewrite Q9' in Hc.
    assert (Hn0 : (0 < length bytes)%nat).
    { destruct (Nat.eq_dec (length bytes) 0) as [El|El]; [|lia]. exfalso.
      rewrite El in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    (* +0x044 .. +0x050: a0 = s0, a1 = s4, a2 = s1, `jal __asan_memcpy` *)
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { rcb_awr. }
    lazymatch type of HS with context [restrict _ ?mz] => rename mz into msT end.
    pose proof (rcb_kept_run segs _ _ W2 _ _ HFr eq_refl) as KD2.
    pose proof (fun x => apresent_grows _ _ _ x HG) as GR2.
    clear HF HFr HG.
    assert (KDT : forall x, aview segs (w_H W2) (ms_mem msT) x = aview segs (w_H W2) mem2 x)
      by (intros x; rewrite KD2; exact (KD1 x)).
    assert (GRT : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem msT) x)
      by (intros x Hx; exact (GR2 x (GR1 x Hx))).
    pmkst HS.
    rcb_reg HS (Z_to_bv 5 10) (w64 a) T10 ltac:(rcb_kreg EE0 10%nat (Z_to_bv 5 10) Q10').
    rcb_reg HS (Z_to_bv 5 11) (w64 p) T11 ltac:(rcb_kreg EE0 20%nat (Z_to_bv 5 20) Q20').
    rcb_reg HS (Z_to_bv 5 12) (w64 (Z.of_nat (length bytes))) T12 ltac:(rcb_kreg EE0 9%nat (Z_to_bv 5 9) Q9').
    rcb_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + RECV_OPB)) T1 ltac:(apply codeptr_val; exact HEI0).
    rcb_reg HS (Z_to_bv 5 2) (YK11.getr regs2 (Z_to_bv 5 2)) T2 ltac:(rcb_same EE0 2%nat (Z_to_bv 5 2)).
    rcb_reg HS (Z_to_bv 5 3) (YK11.getr regs2 (Z_to_bv 5 3)) T3 ltac:(rcb_same EE0 3%nat (Z_to_bv 5 3)).
    rcb_reg HS (Z_to_bv 5 4) (YK11.getr regs2 (Z_to_bv 5 4)) T4 ltac:(rcb_same EE0 4%nat (Z_to_bv 5 4)).
    rcb_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 10)) T8 ltac:(rcb_same EE0 10%nat (Z_to_bv 5 10)).
    rcb_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9 ltac:(rcb_same EE0 9%nat (Z_to_bv 5 9)).
    rcb_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) T18 ltac:(rcb_same EE0 18%nat (Z_to_bv 5 18)).
    rcb_reg HS (Z_to_bv 5 19) (YK11.getr regs2 (Z_to_bv 5 19)) T19 ltac:(rcb_same EE0 19%nat (Z_to_bv 5 19)).
    rcb_reg HS (Z_to_bv 5 21) (YK11.getr regs2 (Z_to_bv 5 21)) T21 ltac:(rcb_same EE0 21%nat (Z_to_bv 5 21)).
    rcb_reg HS (Z_to_bv 5 22) (YK11.getr regs2 (Z_to_bv 5 22)) T22 ltac:(rcb_same EE0 22%nat (Z_to_bv 5 22)).
    rcb_reg HS (Z_to_bv 5 23) (YK11.getr regs2 (Z_to_bv 5 23)) T23 ltac:(rcb_same EE0 23%nat (Z_to_bv 5 23)).
    rcb_reg HS (Z_to_bv 5 24) (YK11.getr regs2 (Z_to_bv 5 24)) T24 ltac:(rcb_same EE0 24%nat (Z_to_bv 5 24)).
    rcb_reg HS (Z_to_bv 5 25) (YK11.getr regs2 (Z_to_bv 5 25)) T25 ltac:(rcb_same EE0 25%nat (Z_to_bv 5 25)).
    rcb_reg HS (Z_to_bv 5 26) (YK11.getr regs2 (Z_to_bv 5 26)) T26 ltac:(rcb_same EE0 26%nat (Z_to_bv 5 26)).
    rcb_reg HS (Z_to_bv 5 27) (YK11.getr regs2 (Z_to_bv 5 27)) T27 ltac:(rcb_same EE0 27%nat (Z_to_bv 5 27)).
    assert (HspT : spZ (ms_regs msT) = spZ regs - 128).
    { change (bv_unsigned (YK11.getr (ms_regs msT) (Z_to_bv 5 2)) = spZ regs - 128).
      rewrite T2, Q2'. unfold w64. rewrite unsigned_lit_small by lia. lia. }
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q) end.
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HART.
    (* the source's facts at the call's memory *)
    pose proof (Hsrc Hn0) as [HsrcS Hdisj].
    pose proof (proj2 (Hsrc0 Hn0)) as Hoff.
    pose proof (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 p (Z.of_nat (length bytes)) HAR2 HsrcS ltac:(lia)) as Hrd2.
    pose proof (trans_rd_ok_view W2 W2 mem2 (ms_mem msT) p (Z.of_nat (length bytes)) Hrd2 (fun x _ => KDT x)
      (fun s _ => KDT s)) as (Hv & Hra & Hh & Ham & Hq0 & Hq63).
    clear Hrd2.
    assert (PD : forall u v : Z * Z, {u = v} + {u <> v}).
    { intros [u1 u2] [v1 v2]. destruct (Z.eq_dec u1 v1) as [E1|E1]; [destruct (Z.eq_dec u2 v2) as [E2|E2]|].
      - left. rewrite E1, E2. reflexivity.
      - right. intros Huv. injection Huv as _ Huv. exact (E2 Huv).
      - right. intros Huv. injection Huv as Huv _. exact (E1 Huv). }
    (* +0x050: __asan_memcpy (a, p, n) *)
    eapply SRr_bind.
    { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
        (transportb_sigma TB___asan_memcpy) (MCPY fx) TG.G_HARNESS_B W2 (ms_regs msT) (ms_mem msT) STK sp0 FP ly S
        W0 mem0 md0 own ly2 S2 _ (k + 1) a p (Z.of_nat (length bytes)) (spZ regs - 128 - sp0)
        (Z_to_bv 64 (BASE + RECV_OPB)) HGX G_HARNESS_B_rw HJ T10 T11 T12).
      - lia.
      - lia.
      - lia.
      - rewrite HspT. lia.
      - replace (spZ regs - 128 - sp0) with ((spZ regs - sp0) + (-8) * 16) by lia.
        rewrite Z_mod_plus_full, Zminus_mod, Hal, Hsp0a. reflexivity.
      - lia.
      - lia.
      - exact (eq_trans T3 (eq_trans Q3 Hgp)).
      - exact (eq_trans T4 (eq_trans Q4 Htp)).
      - exact T1.
      - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold RECV_OPB, AF_receive; lia | reflexivity].
      - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|].
        intros x Hx. left. split; [|rewrite HspT; lia].
        unfold awr_byte.
        destruct (in_dec PD (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly S)) as [HinS|HnS].
        + right. left. split.
          * replace x with (a + (x - a)) by lia.
            exact (ALC.gx_start_fp segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a _
              HJe Hfresh HinS (x - a) ltac:(lia)).
          * exists a, (Z.max 1 (Z.of_nat (length bytes))). split; [exact HB2 | lia].
        + right. right. left. exists a, (Z.max 1 (Z.of_nat (length bytes))).
          split; [exact HB2|]. split; [exact HnS | lia].
      - exact (amem_range_of_block segs B LAWS ly2 S2 W2 (ms_mem msT) _ a _ a (Z.of_nat (length bytes)) HART HB2
          (Z.le_refl a) ltac:(lia)).
      - exact (range_addressable_of_block segs B LAWS ly2 S2 W2 (ms_mem msT) _ a _ a (Z.of_nat (length bytes))
          HART HB2 (Z.le_refl a) ltac:(lia)).
      - intros Hp. exact (shadow_hull_vis_of_block segs B LAWS ly2 S2 W2 (ms_mem msT) _ a _ a
          (Z.of_nat (length bytes)) HART HB2 (Z.le_refl a) ltac:(lia) Hp).
      - cbv beta iota.
        refine (conj _ (conj _ (conj _ (conj _ (conj Ham (conj Hra (fun _ => Hh))))))).
        + exact Hq0.
        + exact Hq63.
        + intros x Hx. split; [exact (Hv x Hx)|]. rewrite HspT. unfold decode_off_win in Hoff. lia.
        + destruct Hdisj as [Hd|Hd]; [right; exact Hd | left; lia]. }
    cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcpy & Heff & Hgr3).
    cbv beta iota in Hcpy.
    assert (KALL : forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + Z.of_nat (length bytes)) ->
      ~ (spZ regs - 128 - ESTACK <= x < spZ regs - 128) -> aview segs (w_H W2) mem3 x = aview segs (w_H W2) mem2 x).
    { intros x Hx H1 H2. rewrite (Heff x Hx H1 ltac:(lia)). exact (KDT x). }
    assert (GR3 : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) mem3 x)
      by (intros x Hx; exact (Hgr3 x (GRT x Hx))).
    assert (PR : forall rr v, acallee_saved rr -> YK11.getr (ms_regs msT) (Z_to_bv 5 rr) = v ->
      YK11.getr regs3 (Z_to_bv 5 rr) = v) by (intros rr v Hrr Hv'; rewrite (HP3 rr Hrr); exact Hv').
    apply (OPB HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a
      Bw' ly2 S2 W2 mem3 md3 regs3 HFIX).
    * split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact HMO|].
      split; [exact (rcb_kept_cpy B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 mem3 (spZ regs - 128)
                 (spZ regs - RECV_STK) (spZ regs) a _ (Z.of_nat (length bytes)) (recv_wr bytes)
                 HARe HAR2 Hfrs HlyF Hperm ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK KALL GR3)|].
      split; [|exact Ha4].
      apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HSV o Ho) as Hvw.
      assert (Hob : 8 <= fst o <= 48).
      { unfold RECV_SAVED in Ho. cbn [In] in Ho.
        repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
      rewrite <- Hvw. apply rdword_ext. intros i Hi. apply KALL; lia.
    * exact HRES.
    * unfold recv_blk. apply (rcb_garr8_shift segs (w_H W2) (w_H W2) mem2 mem3 p a (TW.zs bytes) Hg8p).
      intros i Hi. unfold TW.zs in Hi. rewrite length_map in Hi. rewrite (Hcpy i Hi). exact (KDT (p + i)).
    * apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW|].
      intros x Hx.
      assert (HxG : inG TG.G_HARNESS_B x).
      { destruct Hx as (o & b & nn & Hin & Hb). unfold inG. apply Exists_exists. exists (b, nn).
        split; [exact (TMAP_B_in_G o b nn Hin) | unfold in_zr; cbn [fst snd]; lia]. }
      pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
      apply KALL; [lia | | lia].
      intros Hxa. exact (blk_img segs B LAWS ly2 S2 W2 mem2 md2 a _ x HAR2 HB2 ltac:(lia) (proj1 (HGX x HxG))).
    * exact (rcb_regs_opb regs regs2 regs3 p by_poll a bytes HREGS
        (PR 2 _ ltac:(unfold acallee_saved; lia) T2) (PR 3 _ ltac:(unfold acallee_saved; lia) T3)
        (PR 4 _ ltac:(unfold acallee_saved; lia) T4) (PR 9 _ ltac:(unfold acallee_saved; lia) T9)
        (PR 18 _ ltac:(unfold acallee_saved; lia) T18) (PR 19 _ ltac:(unfold acallee_saved; lia) T19)
        (PR 21 _ ltac:(unfold acallee_saved; lia) T21) (PR 22 _ ltac:(unfold acallee_saved; lia) T22)
        (PR 23 _ ltac:(unfold acallee_saved; lia) T23) (PR 24 _ ltac:(unfold acallee_saved; lia) T24)
        (PR 25 _ ltac:(unfold acallee_saved; lia) T25) (PR 26 _ ltac:(unfold acallee_saved; lia) T26)
        (PR 27 _ ltac:(unfold acallee_saved; lia) T27)
        (PR 8 _ ltac:(unfold acallee_saved; lia) (eq_trans T8 Q10'))).
Qed.

End s.
