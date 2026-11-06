(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 346 of its 399 lines of code are new or changed and 1086 lines of the source are left out. *)
(* diginet_session_close_seg_send: Lemma close_send : close_send_stmt (lib/A/Prog/diginet_session_close_segs.v), the
   send piece of diginet_session_close, offsets +0x3c4 .. +0x3e0 of the listing lib/A/Prog/DgnTransportList.v
   (fuzz_transport.asan 0x87500 .. 0x8751c), reached from the head when close_go Bw holds.

   What the code does. +0x3c4 `li a1, 0xe3` (DIGINET_CMD_DISCONNECT), +0x3c8 `mv a0, s3` (&g_s), +0x3cc `mv a2, zero`
   (ack), +0x3d0 `mv a3, zero` (kp), +0x3d4 `mv a4, zero` (klp), +0x3d8 `jal send_control` (return address +0x3dc);
   +0x3dc `mv a3, a0` (the result r) and +0x3e0 `j +0x18c`, the join cut.

   send_control is a G-form callee composed in the same G journal (no gx_call_cg): its statement
   lib/A/Prog/send_control_cg.v transport_send_control_cg is a premise of this walk, taken with kp = klp = 0, so its
   out cells sendctl_outs 0 0 are [] and its post's acall_kept_g is read at the memory it returned (TransportGCg.v
   gover_nil_mem, acall_kept_g_mem_ext). What this call keeps folds into the walk's own kept fact with
   TransportGCg.v dk_kept_trans_nf_g, whose NF is the own frame (dkg_nf) and whose written range sendctl_wr 0 0 lies
   inside close_wr TF Bw on this path (close_go Bw = true). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_close_segs diginet_session_close_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The return address of the call of send_control, and the two symbolic states: at the cut (s3 = &g_s pinned, no
   region) and at the return (every register an atom, no region). *)
Definition CLOSE_SRET : Z := AF_diginet_session_close + 0x3dc.
Definition cs_ss : sstate :=
  mkSS CLOSE_SEND (sr_set sr_atoms (Z_to_bv 5 19) (SLit CLOSE_S)) [] None (mkFacts [] [] []).
Definition cs_ss2 : sstate := mkSS CLOSE_SRET sr_atoms [] None (mkFacts [] [] []).
Definition CS_B0 : Z * Z := (0, 0).
Definition CS_Bx : sv := SLit 0.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cs_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* The write right of a run from a state with no region. *)
Ltac cs_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* A run from a state with no region writes no byte. *)
Ltac cs_kept HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin; destruct Hin
  | ].

Section send. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition cs_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma cs_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cs_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold cs_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma cs_env_img : forall regs, img_env VAL A_LIM (cs_E regs).
Proof. intros regs. unfold cs_E. apply Eimg_env. Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma cs_entry0 : forall (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (cs_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* At the cut, with s3 = &g_s. *)
Lemma cs_entry : forall (W : world segs) regs mem, YK11.getr regs 19 = w64 CLOSE_S ->
  st_ok_pi segs VAL (cs_E regs) cs_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLOSE_SEND)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem R19.
  exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 19) CLOSE_S (cs_entry0 W regs mem CLOSE_SEND) R19 eq_refl).
Qed.

Lemma close_send : @close_send_stmt fx rc B MT.
Proof.
unfold close_send_stmt. intros JOIN. unfold close_send_at.
intros LAWS0 HMS HN HSC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HSCELLS & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE & HGU & HGN).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF &
  Hrom & Hapart & Htfg & Hinv1 & Hinv4 & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hbl & Htw1 & Hgo).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R21 & R25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite Z.add_0_r in HJ1.
unfold CLOSE_FBYTES in HFc, HFapp, HFLw.
(* every event count of this walk is 0 *)
assert (ECE : CLOSE_EV = 0) by reflexivity.
assert (ESE : SENDCTL_EV = 0) by reflexivity.
(* the stack geometry *)
assert (HSS : CLOSE_STK = 176 + SENDCTL_STK) by exact close_stk_eq.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold CLOSE_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 160) / 32) in *. set (rm := (spZ regs - 160) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
destruct Hsp1 as [Hsp1a Hsp1b].
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HBS : 4272 <= CLOSE_STK).
{ unfold CLOSE_STK, CLOSE_FRAME, CLOSE_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hmx; assert (Hax : a = 4096) by reflexivity end.
  lia. }
pose proof (bv_unsigned_in_range 64 (YK11.getr regs 2)) as HspR.
change (bv_modulus 64) with (2 ^ 64) in HspR. change (bv_unsigned (YK11.getr regs 2)) with (spZ regs) in HspR.
clear HJi memS.
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
assert (Hin : In (CLOSE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
set (FL := flag_addr lyc CLOSE_CID pos) in *.
destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mem2 md2 CLOSE_CID pos F FL HAR2 Hfrs Hbl EF eq_refl
  FFL) as (N1 & N2 & N3 & N4).
(* the model: the send gives B1 and r *)
destruct (close_send_some timg_A TF Bw now Bw' r Hm Hgo) as (B1 & f & HSM1 & HS1).
(* ---- +0x3c4 .. +0x3d8: the five argument moves and the call ---- *)
pose proof (cs_entry W regs2 mem2 R19) as HS.
assert (HEI : img_env VAL A_LIM (cs_E regs2)) by apply cs_env_img.
assert (SHOK : sh_ok segs CS_Bx (@nil shent) (cs_E regs2) (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_SEND)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ1 SHOK CS_B0.
{ cs_awr. }
cs_kept HFr KR W mem2 ms.
assert (GR1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the registers at the call *)
cs_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + CLOSE_SRET)) Q1 ltac:(apply codeptr_val; exact HEI).
cs_reg HS (2%bv : bv 5) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 2 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
cs_reg HS (3%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 3)) Q3
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 3 (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (4%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 4)) Q4
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 4 (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (10%bv : bv 5) (w64 SENDCTL_S) Q10 ltac:(reflexivity).
cs_reg HS (11%bv : bv 5) (w64 TS0.DIGINET_CMD_DISCONNECT) Q11 ltac:(reflexivity).
cs_reg HS (12%bv : bv 5) (w64 (bv_swrap 32 0)) Q12 ltac:(reflexivity).
cs_reg HS (13%bv : bv 5) (w64 0) Q13 ltac:(reflexivity).
cs_reg HS (14%bv : bv 5) (w64 0) Q14 ltac:(reflexivity).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
(* the callee-saved registers the join and the release read, at the call *)
cs_reg HS (8%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 8)) Q8
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 8 (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (9%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 9)) Q9
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 9 (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (18%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 18)) Q18
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 18 (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (19%bv : bv 5) (w64 CLOSE_S) Q19 ltac:(reflexivity).
cs_reg HS (21%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 21)) Q21
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 21 (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (23%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 23)) Q23
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 23 (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (24%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 24)) Q24
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 24 (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cs_reg HS (25%bv : bv 5) (YK11.getr regs2 (Z_to_bv 5 25)) Q25
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs2 25 (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
(* the world relation and the read-only bytes at the call memory *)
assert (TWc : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) Bw).
{ apply (tw_kept TMAP_A (aview segs (w_H W) mem2)); [exact Htw1|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR. lia. }
assert (ROMc : trans_rom_view_rd W (ms_mem ms)).
{ intros a Ha. rewrite <- (Hrom a Ha). rewrite KR by (pose proof (trans_ro_rd_bounds a Ha); lia).
  pose proof HK as (_ & _ & K3 & _).
  destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
  apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_LO in Gh. lia. }
(* the count of class-2 frames at the call state *)
assert (HCNT : count_cid SENDCTL_CID (frames S2) + 1 < fs_frames SENDCTL_CID).
{ rewrite Hfrs. change SENDCTL_CID with CLOSE_CID. cbn [count_cid]. change (CLOSE_CID =? CLOSE_CID) with true.
  cbn [Z.add]. lia. }
assert (EBR : BASE + CLOSE_SRET = 0x87518) by (vm_compute; reflexivity).
(* +0x3d8: the call of send_control *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS_send_control)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ exact (HSC fx STK sp0 FP ly S W0 mem0 md0 ((CLOSE_CID, pos) :: own) lyc S2 W (ms_mem ms) _ k (ms_regs ms)
    TS0.DIGINET_CMD_DISCONNECT 0 0 0 r [] [] f TF Bw B1
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ1)
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transport));
          [unfold CLOSE_SRET, AF_diginet_session_close; lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBR; rewrite unsigned_lit_small by lia; lia)
    ltac:(exact (eq_trans Q3 (eq_trans R3 Hgp))) ltac:(exact (eq_trans Q4 (eq_trans R4 Htp)))
    Q10 Q11 Q12 Q13 Q14
    ltac:(rewrite QSP; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1;
          rewrite Hsp1b, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
          apply Z.mod_mul; lia)
    ltac:(rewrite QSP; lia) ltac:(rewrite QSP; lia)
    ltac:(unfold TS0.DIGINET_CMD_DISCONNECT; lia) ltac:(lia)
    (or_introl eq_refl)
    TWc Hgf HSM1 ROMc Hinv1 Hinv4 HCNT ltac:(lia)). }
cbv beta.
intros W3 c3 _ HPOST.
unfold transport_sendctl_post, transport_cg_post_out in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & Ec3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HKg & Hmo3 &
  (HA0 & HTW3 & HGF3 & _)).
assert (Ee3 : e3 = 0) by lia. subst e3. rewrite Z.add_0_r in HJ3.
rewrite Q1 in Ec3. subst c3.
(* the callee's kept fact, at the memory it returned (no out cell) *)
assert (HK3 : acall_kept_g segs B TG.G_HARNESS lyc S2 W (ms_mem ms) W3 mem3
  (spZ (ms_regs ms) - SENDCTL_STK) (spZ (ms_regs ms)) (sendctl_wr 0 0)).
{ apply (acall_kept_g_mem_ext segs B TG.G_HARNESS lyc S2 W (ms_mem ms) W3
    (gover (sendctl_outs 0 0) mem3 (ms_mem ms)) mem3 _ _ (sendctl_wr 0 0)
    (fun x => eq_sym (gover_nil_mem mem3 (ms_mem ms) x)) HKg). }
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
clear HJi3 memS3.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
assert (Hfrs3 : frames S3 = (CLOSE_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hperm3c : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc)) by (rewrite <- Hbl; exact Hperm3).
(* what the call kept, folded into the walk's own kept fact *)
assert (KCN : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms) (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc mem2 (ms_mem ms)
    (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw) (fun _ : Z => False) HARc HK
    ltac:(intros a Ha Hn; exact (KR a Ha)) GR1); intros; contradiction. }
assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W (ms_mem ms) W3 mem3
    (spZ regs - CLOSE_STK) (spZ regs) (spZ (ms_regs ms) - SENDCTL_STK) (spZ (ms_regs ms)) (close_wr TF Bw)
    (sendctl_wr 0 0) (dkg_nf CLOSE_CID F FL)).
  - lia.
  - lia.
  - intros c p. reflexivity.
  - intros fr Hf. rewrite Hfrs. right. exact Hf.
  - intros bm Hbm. rewrite Hbl. exact Hbm.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK3.
  - rewrite QSP. lia.
  - rewrite QSP. lia.
  - intros a Ha. left. left. split; [exact Hgo | exact Ha]. }
(* the saved words and the frame's last word at the call's return *)
pose proof HK3 as (K31 & _ & _ & K34 & _).
rewrite QSP in K31.
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha. rewrite K31 by lia. apply KR. lia. }
assert (KFL : forall i, 0 <= i < 8 -> aview segs (w_H W3) mem3 (F + 248 + i) = aview segs (w_H W) mem2 (F + 248 + i)).
{ intros i Hi. transitivity (aview segs (w_H W) (ms_mem ms) (F + 248 + i)).
  - apply (K34 CLOSE_CID pos (F + 248 + i) Hin).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CLOSE_CID) with 256. lia.
    + intros Hw. apply (N2 (F + 248 + i)); [left; change (fs_frame_bytes CLOSE_CID) with 256; lia|].
      exact (trans_g_img _ (close_sendctl_wr_G _ Hw)).
  - apply KR. lia. }
assert (HSo : forall o, In o CLOSE_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold CLOSE_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
assert (HFW3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED).
{ rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia. }
assert (HFL3 : rdword (aview segs (w_H W3) mem3) (F + 256 - 8) = Some FL).
{ rewrite <- HFLw. replace (F + 256 - 8) with (F + 248) by lia.
  apply rdword_ext. intros i Hi. exact (KFL i Hi). }
(* the callee-saved registers at the return, as the cut left them *)
assert (P2' : YK11.getr regs3 (Z_to_bv 5 2) = w64 sp1)
  by (rewrite (HP3 2 ltac:(hnf; lia)); exact Q2).
assert (P3' : YK11.getr regs3 (Z_to_bv 5 3) = YK11.getr regs 3)
  by exact (eq_trans (HP3 3 ltac:(hnf; lia)) (eq_trans Q3 R3)).
assert (P4' : YK11.getr regs3 (Z_to_bv 5 4) = YK11.getr regs 4)
  by exact (eq_trans (HP3 4 ltac:(hnf; lia)) (eq_trans Q4 R4)).
assert (P8' : YK11.getr regs3 (Z_to_bv 5 8) = w64 (spZ regs))
  by exact (eq_trans (HP3 8 ltac:(hnf; lia)) (eq_trans Q8 R8)).
assert (P9' : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1)
  by exact (eq_trans (HP3 9 ltac:(hnf; lia)) (eq_trans Q9 R9)).
assert (P18' : YK11.getr regs3 (Z_to_bv 5 18) = w64 F)
  by exact (eq_trans (HP3 18 ltac:(hnf; lia)) (eq_trans Q18 R18)).
assert (P19' : YK11.getr regs3 (Z_to_bv 5 19) = w64 CLOSE_S)
  by (rewrite (HP3 19 ltac:(hnf; lia)); exact Q19).
assert (P21' : YK11.getr regs3 (Z_to_bv 5 21) = w64 (CLOSE_S + 112))
  by exact (eq_trans (HP3 21 ltac:(hnf; lia)) (eq_trans Q21 R21)).
assert (P23' : YK11.getr regs3 (Z_to_bv 5 23) = w64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (HP3 23 ltac:(hnf; lia)) (eq_trans Q23 R23)).
assert (P24' : YK11.getr regs3 (Z_to_bv 5 24) = w64 F)
  by exact (eq_trans (HP3 24 ltac:(hnf; lia)) (eq_trans Q24 R24)).
assert (P25' : YK11.getr regs3 (Z_to_bv 5 25) = w64 SHADOW_OFF)
  by exact (eq_trans (HP3 25 ltac:(hnf; lia)) (eq_trans Q25 R25)).
clear dependent ms.
(* ---- +0x3dc .. +0x3e0: a3 = a0, then the join cut ---- *)
pose proof (cs_entry0 W3 regs3 mem3 CLOSE_SRET) as HS3.
assert (HEI3 : img_env VAL A_LIM (cs_E regs3)) by apply cs_env_img.
assert (SHOK3 : sh_ok segs CS_Bx (@nil shent) (cs_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
change (mkSS CLOSE_SRET sr_atoms [] None (mkFacts [] [] [])) with cs_ss2 in HS3.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_SRET)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 CS_B0 CLOSE_JOIN.
{ cs_awr. }
cs_kept HFr KR2 W3 mem3 ms.
assert (GR2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
rename HS3 into HS.
(* the registers at the join cut *)
cs_reg HS (2%bv : bv 5) (w64 sp1) G2
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 2 (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P2').
cs_reg HS (3%bv : bv 5) (YK11.getr regs 3) G3
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 3 (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P3').
cs_reg HS (4%bv : bv 5) (YK11.getr regs 4) G4
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 4 (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P4').
cs_reg HS (8%bv : bv 5) (w64 (spZ regs)) G8
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 8 (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P8').
cs_reg HS (9%bv : bv 5) (w64 sp1) G9
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 9 (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P9').
cs_reg HS (18%bv : bv 5) (w64 F) G18
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 18 (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P18').
cs_reg HS (19%bv : bv 5) (w64 CLOSE_S) G19
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 19 (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P19').
cs_reg HS (21%bv : bv 5) (w64 (CLOSE_S + 112)) G21
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 21 (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P21').
cs_reg HS (23%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) G23
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 23 (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P23').
cs_reg HS (24%bv : bv 5) (w64 F) G24
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 24 (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P24').
cs_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) G25
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 25 (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact P25').
cs_reg HS (13%bv : bv 5) (w64 r) G13
  ltac:(cbn [sv_denot]; rewrite (cs_ew_reg regs3 10 (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact HA0).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JOIN)) mm rom) mdx) Q) end.
apply (JOIN LAWS0 HMS HN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1 pos sp1 F
  ly3 S3 W3 (ms_mem ms) _ 0 (ms_regs ms) HFIX).
- unfold close_join_cur. split; [|split; [exact HS1 | split]].
  + refine (conj _ (conj _ (conj Hfrs3 (conj Hperm3c (conj ELF3c (conj _ (conj _ (conj _ _)))))))).
    * rewrite Z.add_0_r. exact HJ3.
    * lia.
    * exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3).
    * apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly3 S3 W memc mdc W3 mem3 md3 mem3
        (ms_mem ms) (spZ regs - CLOSE_STK) (spZ regs) CLOSE_CID pos F FL (close_wr TF Bw) (fun _ : Z => False)
        HGX HARc HAR3 Hfrs3 ltac:(intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm3c) Hbm)) ELF3c
        EF eq_refl FFL ltac:(lia) ltac:(lia) ltac:(intros a []) KC3 ltac:(intros a Ha Hn; exact (KR2 a Ha)) GR2).
    * rewrite Forall_forall in HFW3 |- *. intros o Ho. rewrite <- (HFW3 o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KR2. lia.
    * unfold CLOSE_FBYTES. fold FL. rewrite <- HFL3. apply rdword_ext. intros i Hi. apply KR2. lia.
  + apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact HTW3|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR2. lia.
  + exact HGF3.
- unfold close_regs_join, close_regs_send, close_regs_base.
  exact (conj (conj (conj G2 (conj G3 (conj G4 (conj G8 (conj G9 (conj G18 (conj G23 G24)))))))
    (conj G19 (conj G21 G25))) G13).
Qed.

End send.
