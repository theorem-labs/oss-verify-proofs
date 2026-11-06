(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 524 of its 583 lines of code are new or changed and 1865 lines of the source are left out. *)
(* diginet_session_poll_seg_rel: Theorem pw_rel_piece : pw_rel_stmt (lib/A/Prog/diginet_session_poll_segs.v),
   the release piece: from the cut rel (+0x30c, 0x8b094) to the return: `jal __asan_set_shadow_f8` (+0x314; buf's
   shadow bytes 4 .. 193 := 0xf8, diginet_session_poll_seg_rt.v gx_set_shadow_at), the header word 0x45e0360e at the
   frame, the slot s1 + 16 (the frame, not 0: `beqz` not taken), `jal __asan_stack_free_5` (+0x330; the frame's 256
   shadow bytes := 0xf5 and its flag byte 0, the frame released: gx_stack_free_at), `j`, a0 = s10, sp = s0 - 160, the
   13 reloads, sp = sp + 160, `ret`; the post pw_post.

   Three runs of the position-abstract engine over the caller's G journal (TransportGRunA.v paj_run_x):
     run A  +0x30c .. +0x314  a1 = 190, a0 = the slot s1 + 8 (atom 32: the shadow address of buf), up to the jal;
     run B  +0x318 .. +0x330  a0 = 0x45e0360e stored at the frame (s2, atom 18), a0 = the slot s1 + 16 (atom 18 again,
                              the frame; the fact 4096 <= atom 18 decides `beqz`), a1 = 1696, up to the jal;
     run C  +0x334 .. +0x384  `j`, a0 = s10, sp = s0 - 160, the 13 reloads (atoms 32 .. 44: the entry values of ra, s0,
                              s1, s2 .. s11, in POLL_SAVED's order), sp = sp + 160, up to the `ret`.
   The two calls between the runs are the stated runtime entries; each keeps the callee-saved registers, so s0, s1, s2
   and s10 reach run C as the cut holds them.

   What the call kept (acall_kept_g at the final memory): every byte outside the own frame (its bytes, its shadow
   bytes, its flag byte: TransportGCg.v dkg_nf) and outside the runtime entries' window [sp1 - ESTACK, sp1) is the
   cut's. pr_kept_nfz carries the cut's acall_kept_g over that change: it is TransportGFrame.v dk_kept_nfz_gw with
   the presence of the statement's window at the final memory (the journal's) in place of presence grown at every
   byte, since the stack free states no presence of the shadow bytes and the flag byte it writes (those lie below
   alloc_ceiling, where acall_kept_g asks no presence). The frame is released in the journal (stack_free_state, own =
   the caller's), the frames are the call's (CanKit.v can_sf_frames), the state changes in st_fs only
   (mo_le_set_fs_r). The world relation at Bw' is the cut's: no byte of G is in the own frame or the window
   (TWorldA.v tw_kept_GA). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg notice_cg io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg SrxCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  diginet_session_poll_seg_rt diginet_session_poll_seg_leaf diginet_session_poll_seg_grecv diginet_session_poll_seg_grx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TPoll TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TPL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TPoll.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.


(* ------------------------------------------------------------------ *)
(* 1. The three symbolic states                                        *)
(* ------------------------------------------------------------------ *)

(* The return points of the two calls. *)
Definition PR_C1 : Z := AF_diginet_session_poll + 0x318.
Definition PR_C2 : Z := AF_diginet_session_poll + 0x334.
Definition PR_B0 : Z * Z := (0, 0).

(* run A: the slot s1 + 8 (s1 = atom 9) holds atom 32. *)
Definition pra_rg_s8 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))].
Definition ss_pra : sstate := mkSS PW_REL sr_atoms [pra_rg_s8] None (mkFacts [] [] []).

(* run B: the frame's first word (s2 = atom 18, written) and the slot s1 + 16, which holds atom 18. *)
Definition prb_rg_hd : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 8 [].
Definition prb_rg_s16 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 18 0))].
Definition prb_facts : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_prb : sstate := mkSS PR_C1 sr_atoms [prb_rg_hd; prb_rg_s16] None prb_facts.

(* run C: the 13 saved words below s0 = atom 8, as atoms 32 .. 44. *)
Definition prc_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].
Definition ss_prc : sstate := mkSS PR_C2 sr_atoms [prc_rg_sv] None (mkFacts [] [] []).

(* A byte of a 2048-byte frame in application memory is not one of the frame's shadow bytes. *)
Lemma pr_frame_not_shadow {rc : YM05.RunCeil} : forall F i, in_app F 2048 -> 0 <= i < 2048 ->
  ~ (SHADOW_OFF + F / 8 <= F + i < SHADOW_OFF + F / 8 + 256).
Proof.
intros F i (H4 & [HL | (HH & _)]) Hi; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *;
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le F 8 ltac:(lia)); lia.
Qed.

(* The callee-saved registers, one by one. *)
Lemma pr_saved_cases : forall r, acallee_saved r ->
  r = 2 \/ r = 3 \/ r = 4 \/ (r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27).
Proof.
intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]];
  [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
  | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity |].
do 5 right. lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac pr_reg HS r v H tac :=
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
(* A register the run did not write, from the equation Q of its value at the run's start (EW: the valuation's
   registers). *)
Ltac pr_kreg HS EW r n Q H :=
  lazymatch type of Q with _ = ?v =>
    pr_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EW n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The value of a register at the end of run C, as its symbolic value. *)
Ltac pr_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.
(* The awr obligation's regions, computed. *)
Ltac pr_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A run's frame keeps every byte outside Zs (U: the base of a written window). *)
Ltac pr_frame_kept HFr Zs U :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn; apply (kept_of_frame _ _ _ _ _ Zs HFr); [| exact Ha | exact Hn];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; cbv beta; first [exfalso; lia | rewrite U in Hx; lia] |]);
  destruct Hin.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition pra_E (regs : bvmap 5 word) (q : Z) : env := Eimg (PI := PI_transport) (Ereg regs [w64 q]).
Definition prb_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).
Definition prc_extra (regs : bvmap 5 word) : list word :=
  map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) POLL_SAVED.
Definition prc_E (regsC regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regsC (prc_extra regs)).

(* run A's state at +0x30c. *)
Lemma pra_entry : forall (W : world segs) regs mem (sp1 q : Z),
  YK11.getr regs 9 = w64 sp1 -> 0 <= sp1 -> sp1 + 16 <= 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 8) = Some q ->
  st_ok_pi segs VAL (pra_E regs q) ss_pra
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + PW_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp1 q R9 H0 H1 Hq Hrd.
set (E := pra_E regs q).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E, pra_E; rewrite (can_ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), R9; unfold w64;
      apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 q)
  by (unfold E, pra_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold ss_pra.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks pra_rg_s8 base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val segs E _ sp1 8 8 (SOff 32 0) q);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  exact (val_mem_of_rdword segs _ _ _ _ Hrd).
- apply pairwise_disjoint_of_extents.
  unfold pra_rg_s8, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* run B's state at +0x318. *)
Lemma prb_entry : forall (W : world segs) regs mem (F sp1 : Z),
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F ->
  4096 <= F -> F + 8 <= sp1 -> F mod 64 = 0 -> sp1 + 24 <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 16) = Some F ->
  st_ok_pi segs VAL (prb_E regs) ss_prb
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + PR_C1)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F sp1 R9 R18 HF0 HFs HF64 Hs47 Hpf Hrd.
set (E := prb_E regs).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E, prb_E; rewrite (can_ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), R9; unfold w64;
      apply unsigned_lit_small; lia).
assert (E18 : ew E 18 = w64 F)
  by (unfold E, prb_E; rewrite (can_ew_Eimg_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_prb.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks prb_rg_hd prb_rg_s16 base_val];
    rewrite ?U9, ?U18.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ sp1 16 8 (SOff 18 0) F);
      [cbn [sv_denot]; rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ Hrd).
- apply pairwise_disjoint_of_extents.
  unfold prb_rg_hd, prb_rg_s16, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U18. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold prb_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18.
  change (2 ^ 6) with 64.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* run C's state at +0x334. *)
Lemma prc_entry : forall (W : world segs) (regsC regs : bvmap 5 word) mem (SP : Z),
  YK11.getr regsC 8 = w64 SP -> 104 <= SP <= 2 ^ 47 ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) POLL_SAVED ->
  st_ok_pi segs VAL (prc_E regsC regs) ss_prc
    (restrict (w_H W) (@YK11.mkst fx regsC (Z_to_bv 64 (BASE + PR_C2)) mem (YK11.seg_rom segs))).
Proof.
intros W regsC regs mem SP R8 HSP Hsaved.
set (E := prc_E regsC regs).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E, prc_E; rewrite (can_ew_Eimg_Ereg_nat regsC _ 8 8%bv eq_refl), R8; unfold w64;
      apply unsigned_lit_small; lia).
unfold POLL_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_prc.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks prc_rg_sv base_val]. rewrite U8.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  all: lazymatch goal with |- YP09.chunk_ok _ _ _ ?b (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    match goal with Sv : rdword _ (?b0 - ?o) = Some (bv_unsigned ?x) |- _ =>
      apply (chunk_ok_val segs E _ b off 8 (SOff n 0) (bv_unsigned x));
      [ cbn [sv_denot]; rewrite Z.add_0_r; reflexivity
      | let Hrr := fresh "Hrr" in pose proof (bv_unsigned_in_range 64 x) as Hrr;
        change (bv_modulus 64) with (2 ^ 64) in Hrr; exact Hrr
      | zside
      | replace (b + off) with (b0 - o) by lia; exact (val_mem_of_rdword segs _ _ _ _ Sv) ]
    end end.
- apply pairwise_disjoint_of_extents.
  unfold prc_rg_sv, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. What the call keeps, and the stack window at a journal state     *)
(* ------------------------------------------------------------------ *)

(* TransportGFrame.v dk_kept_nfz_gw (with no byte of G among the changed ones) whose presence premise is only the
   statement's window at the new memory: a step from a state of the frame (cid, fpos) that changes only bytes of the
   window [slo, shi) or of that frame (its bytes, its shadow bytes, its flag byte) keeps acall_kept_g. The changed
   bytes of the frame lie below alloc_ceiling, where acall_kept_g asks no presence. *)
Lemma pr_kept_nfz : forall (LAWS : AR_laws segs B) G lyc Sc ly2 S2 (W : world segs) memc mdc (W1 : world segs) mem2
    md2 memY slo shi cid fpos F FL (Eo Zs : Z -> Prop),
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W1 mem2 md2 ->
  frames S2 = (cid, fpos) :: frames Sc ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_F ly2 = ly_F lyc ->
  F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos -> frame_flag_lawP segs B ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, Zs a -> (slo <= a < shi) \/ dkg_nf cid F FL a) ->
  acall_kept_g segs B G lyc Sc W memc W1 mem2 slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) mem2 a) ->
  (forall a, slo <= a < shi -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B G lyc Sc W memc W1 memY slo shi Eo.
Proof.
intros LAWS G lyc Sc ly2 S2 W memc mdc W1 mem2 md2 memY slo shi cid fpos F FL Eo Zs HAR HAR2 Hfrs Hbl ELF EF EFL FFL
  Hce Hshi HZ (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hpw.
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W1 mem2 md2 cid fpos F FL HAR2 Hfrs Hbl ELF EF
  EFL FFL) as (N1 & N2 & N3 & N4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (NZ : forall a, alloc_ceiling <= a -> ~ (slo <= a < shi) -> ~ Zs a).
{ intros a Ha Hw HZa. destruct (HZ a HZa) as [X | X]; [exact (Hw X) | pose proof (N4 a X) as Hx; lia]. }
assert (NZl : forall a, a < alloc_ceiling -> ~ dkg_nf cid F FL a -> ~ Zs a).
{ intros a Ha Hn HZa. destruct (HZ a HZa) as [X | X]; [lia | exact (Hn X)]. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [exact (K1 a Ha Hw) | lia | exact (NZ a ltac:(lia) Hw)].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  rewrite Hkp; [exact (K2 b m i Hb Hi Hn) | lia |].
  apply NZl; [lia | intros X; exact (N1 b m i Hb Hi X)].
- intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hkp; [exact (K3 a Hi HnG Hno He) | lia |].
  apply NZl; [lia | intros X; exact (N2 a X Hi)].
- intros c pos a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c pos HAR Hin) as (G4096 & Gce & _).
  pose proof (fs_frame_bytes_nonneg c) as Hfs.
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc c pos) (fs_frame_bytes c) Hfs) as Hse.
    assert (Hd : (frame_addr lyc c pos + fs_frame_bytes c) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc c pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [exact (K4 c pos a Hin Hr Hn) | lia |].
  apply NZl; [lia | intros X; exact (N3 c pos a Hin Hr X)].
- intros a Ha Hw Hp. pose proof (K5 a Ha Hw Hp) as HpX.
  apply (apresent_of_aview segs);
    [lia | intros Hi; pose proof (transport_segs_low a Hi) as Hl; unfold kLowMemEnd in Hl; lia |].
  rewrite Hkp; [exact (can_aview_vis (segs := segs) _ _ a HpX) | lia | exact (NZ a ltac:(lia) Hw)].
- exact Hpw.
Qed.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma pr_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W'
    mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma pw_rel_holds : @pw_rel_stmt fx rc B MT.
Proof.
unfold pw_rel_stmt, pw_rel_at.
intros c RT OK pos ly2 S2 W2 mem2 md2 regs2 CUR RG R26.
pose proof (pw_ok_sp B MT c OK) as (HARc & HSP & HCE & _ & HS1al & HS1r & Hsp0al & Hstk & Hsp0 & EPS & EES & EIS & _).
pose proof (pw_cur_frame B MT c pos ly2 S2 W2 mem2 md2 (cx_Bw' c) RT OK CUR)
  as (HAR2 & Hin & EFA & _ & _ & _ & HF0 & HF64 & HFc & HFapp & _).
pose proof RT as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & FFL & HGX & HGNE & _ & SF8 & _ & _ & _ & _ & _ &
  _ & SFREE).
pose proof OK as (_ & Hret & _ & Hgp & Htp & _).
destruct CUR as (HJ & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw & Hslot8 & Hslot16 & HTW & Hgf & Hinv & _).
destruct RG as (R2 & R3 & R4 & R8 & R9 & R18).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (SP := pw_SP c) in *.
set (sp1 := pw_sp1 c) in *.
set (F := pw_F c pos) in *.
set (FL := flag_addr (cx_lyc c) POLL_CID pos) in *.
unfold POLL_FBYTES in HFc, HFapp, HFLw.
assert (EFL : flag_addr ly2 POLL_CID pos = FL) by (unfold FL, flag_addr; rewrite ELF; reflexivity).
assert (ESH : forall x, shadow_addr x = SHADOW_OFF + x / 8) by (intros x; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hwin : SP - POLL_STK <= sp1 - ESTACK) by lia.
assert (HFd : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hs16 : sp1 mod 16 = 0) by (clear - HS1al; lia).
assert (Hbl : forall bm, In bm (ablocks B (cx_lyc c) (cx_Sc c)) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low (cx_lyc c) (cx_Sc c) ly2 S2 W2 mem2 md2 POLL_CID pos F FL
  HAR2 Hfrs Hbl ELF eq_refl eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
(* ---- run A, +0x30c .. +0x314 ---- *)
pose proof (pra_entry W2 regs2 mem2 sp1 (SHADOW_OFF + F / 8 + 4) R9 ltac:(lia) ltac:(lia)
  ltac:(unfold SHADOW_OFF; lia) Hslot8) as HS.
assert (HEI : img_env VAL A_LIM (pra_E regs2 (SHADOW_OFF + F / 8 + 4))) by (unfold pra_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (pra_E regs2 (SHADOW_OFF + F / 8 + 4)) (mrestrict (w_H W2) mem2))
  by constructor.
assert (EWA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (pra_E regs2 (SHADOW_OFF + F / 8 + 4)) n = YK11.getr regs2 r)
  by (intros n r Hn; unfold pra_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (EA32 : ew (pra_E regs2 (SHADOW_OFF + F / 8 + 4)) 32 = w64 (SHADOW_OFF + F / 8 + 4))
  by (unfold pra_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + PW_REL)) mem2 (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ SHOK PR_B0.
{ pr_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
rename HF into HFa, HFr into HFra, HG into HGa.
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
pr_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + PR_C1)) A1 ltac:(apply codeptr_val; exact HEI).
pr_reg HS (10%bv : bv 5) (w64 (SHADOW_OFF + F / 8 + 4)) A10
  ltac:(cbn [sv_denot]; rewrite EA32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
pr_reg HS (11%bv : bv 5) (w64 190) A11 ltac:(reflexivity).
pr_kreg HS EWA (2%bv : bv 5) 2%nat R2 A2. pr_kreg HS EWA (3%bv : bv 5) 3%nat R3 A3.
pr_kreg HS EWA (4%bv : bv 5) 4%nat R4 A4. pr_kreg HS EWA (8%bv : bv 5) 8%nat R8 A8.
pr_kreg HS EWA (9%bv : bv 5) 9%nat R9 A9. pr_kreg HS EWA (18%bv : bv 5) 18%nat R18 A18.
pr_kreg HS EWA (26%bv : bv 5) 26%nat R26 A26.
(* run A writes no byte *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
  aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a) by pr_frame_kept HFra (fun _ : Z => False) A2.
(* +0x314: __asan_set_shadow_f8 on buf's shadow bytes 4 .. 193 *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_set_shadow_f8)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_set_shadow_at (SK := tfib_sink_head) segs B LAWS transport_segs_low
    (transport_sigma TS___asan_set_shadow_f8) 0xf8 (SF8 fx) TG.G_HARNESS W2 rg mm
    (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((POLL_CID, pos) :: cx_own c) ly2 S2 mdx (cx_k c) (sp1 - cx_sp0 c) (Z_to_bv 64 (BASE + PR_C1))
    POLL_CID pos (SHADOW_OFF + F / 8 + 4) 190 HGX HJ) end.
  - left; reflexivity.
  - exact Hin.
  - unfold spZ at 1. rewrite A2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hs16, Hsp0al. reflexivity.
  - lia.
  - lia.
  - exact A3.
  - exact A4.
  - exact A1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold PR_C1, AF_diginet_session_poll; lia | reflexivity].
  - exact A10.
  - exact A11.
  - lia.
  - rewrite EFA, ESH. lia.
  - rewrite EFA, ESH. change (fs_frame_bytes POLL_CID / 8) with 256. lia. }
cbv beta.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hk3 & _).
assert (T2 : YK11.getr regs3 2 = w64 sp1)
  by (transitivity (YK11.getr (ms_regs msA) 2); [exact (HP3 2 ltac:(unfold acallee_saved; lia)) | exact A2]).
assert (T3 : YK11.getr regs3 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs msA) 3); [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact A3]).
assert (T4 : YK11.getr regs3 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs msA) 4); [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact A4]).
assert (T8 : YK11.getr regs3 8 = w64 SP)
  by (transitivity (YK11.getr (ms_regs msA) 8); [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact A8]).
assert (T9 : YK11.getr regs3 9 = w64 sp1)
  by (transitivity (YK11.getr (ms_regs msA) 9); [exact (HP3 9 ltac:(unfold acallee_saved; lia)) | exact A9]).
assert (T18 : YK11.getr regs3 18 = w64 F)
  by (transitivity (YK11.getr (ms_regs msA) 18); [exact (HP3 18 ltac:(unfold acallee_saved; lia)) | exact A18]).
assert (T26 : YK11.getr regs3 26 = w64 (cx_r c))
  by (transitivity (YK11.getr (ms_regs msA) 26); [exact (HP3 26 ltac:(unfold acallee_saved; lia)) | exact A26]).
(* ---- run B, +0x318 .. +0x330 ---- *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
destruct (al_frames _ _ LAWS _ _ _ _ _ POLL_CID pos HAR3 Hin) as (_ & _ & HFb3 & _).
rewrite EFA in HFb3. change (fs_frame_bytes POLL_CID) with 2048 in HFb3.
assert (HS16 : rdword (aview segs (w_H W2) mem3) (sp1 + 16) = Some F).
{ rewrite <- Hslot16. apply rdword_ext. intros i Hi.
  rewrite (Hk3 (sp1 + 16 + i) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia)).
  exact (KA (sp1 + 16 + i) ltac:(lia) ltac:(tauto)). }
clear HS SHOK.
pose proof (prb_entry W2 regs3 mem3 F sp1 T9 T18 HF0 ltac:(lia) HF64 ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb3 a ltac:(lia)))) HS16) as HS.
assert (HEIb : img_env VAL A_LIM (prb_E regs3)) by (unfold prb_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (prb_E regs3) (mrestrict (w_H W2) mem3)) by constructor.
assert (EWB : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (prb_E regs3) n = YK11.getr regs3 r)
  by (intros n r Hn; unfold prb_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (UB18 : bv_unsigned (ew (prb_E regs3) 18) = F)
  by (rewrite (EWB 18%nat 18%bv eq_refl), T18; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + PR_C1)) mem3 (YK11.seg_rom segs)) md3) Q) end.
paj_run_tok RUN HS HJ3 SHOK PR_B0.
{ pr_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ POLL_CID pos); [left; reflexivity | |].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UB18 in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes POLL_CID) with 2048. lia.
  - apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_nil. }
rename HF into HFb, HFr into HFrb, HG into HGb.
lazymatch type of HS with context [restrict _ ?m] => rename m into msB end.
pr_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + PR_C2)) B1 ltac:(apply codeptr_val; exact HEIb).
pr_reg HS (10%bv : bv 5) (w64 F) B10
  ltac:(cbn [sv_denot]; rewrite (EWB 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact T18).
pr_reg HS (11%bv : bv 5) (w64 1696) B11 ltac:(reflexivity).
pr_kreg HS EWB (2%bv : bv 5) 2%nat T2 B2. pr_kreg HS EWB (3%bv : bv 5) 3%nat T3 B3.
pr_kreg HS EWB (4%bv : bv 5) 4%nat T4 B4. pr_kreg HS EWB (8%bv : bv 5) 8%nat T8 B8.
pr_kreg HS EWB (26%bv : bv 5) 26%nat T26 B26.
(* run B writes the frame's first word only *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) ->
  aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem3 a)
  by pr_frame_kept HFrb (fun x : Z => F <= x < F + 8) UB18.
(* the frame's last word, at the stack free *)
assert (HFLB : rdword (aview segs (w_H W2) (ms_mem msB)) (frame_addr ly2 POLL_CID pos + fs_frame_bytes POLL_CID - 8)
  = Some (flag_addr ly2 POLL_CID pos)).
{ rewrite EFA, EFL. change (fs_frame_bytes POLL_CID) with 2048.
  rewrite <- HFLw. apply rdword_ext. intros i Hi.
  rewrite (KB (F + 2048 - 8 + i) ltac:(lia) ltac:(lia)).
  pose proof (pr_frame_not_shadow F (2040 + i) HFapp ltac:(lia)) as HNS.
  rewrite (Hk3 (F + 2048 - 8 + i) ltac:(lia) ltac:(lia) ltac:(lia)).
  exact (KA (F + 2048 - 8 + i) ltac:(lia) ltac:(tauto)). }
(* +0x330: __asan_stack_free_5 releases the frame *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_free_5)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_free_at (SK := tfib_sink_head) segs B LAWS transport_segs_low
    (transport_sigma TS___asan_stack_free_5) POLL_CID (SFREE fx) FFL ltac:(unfold POLL_CID; lia)
    TG.G_HARNESS W2 rg mm (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    (cx_own c) ly2 S2 mdx (cx_k c) (sp1 - cx_sp0 c) (Z_to_bv 64 (BASE + PR_C2)) pos 1696 HGX HJ3) end.
  - exact Hin.
  - unfold spZ at 1. rewrite B2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hs16, Hsp0al. reflexivity.
  - lia.
  - lia.
  - exact B3.
  - exact B4.
  - exact B1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold PR_C2, AF_diginet_session_poll; lia | reflexivity].
  - rewrite EFA. exact B10.
  - exact B11.
  - exact HFLB. }
cbv beta.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hk4).
assert (V3 : YK11.getr regs4 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs msB) 3); [exact (HP4 3 ltac:(unfold acallee_saved; lia)) | exact B3]).
assert (V4 : YK11.getr regs4 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs msB) 4); [exact (HP4 4 ltac:(unfold acallee_saved; lia)) | exact B4]).
assert (V8 : YK11.getr regs4 8 = w64 SP)
  by (transitivity (YK11.getr (ms_regs msB) 8); [exact (HP4 8 ltac:(unfold acallee_saved; lia)) | exact B8]).
assert (V26 : YK11.getr regs4 26 = w64 (cx_r c))
  by (transitivity (YK11.getr (ms_regs msB) 26); [exact (HP4 26 ltac:(unfold acallee_saved; lia)) | exact B26]).
(* every byte outside the own frame and the runtime entries' window is the cut's *)
assert (KP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) -> ~ dkg_nf POLL_CID F FL a ->
  aview segs (w_H W2) mem4 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hw Hd. unfold dkg_nf in Hd.
  change (fs_frame_bytes POLL_CID) with 2048 in Hd. change (fs_frame_bytes POLL_CID / 8) with 256 in Hd.
  assert (Hd1 : ~ (F <= a < F + 2048)) by (intros X; apply Hd; left; exact X).
  assert (Hd2 : ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 256)) by (intros X; apply Hd; right; left; exact X).
  assert (Hd3 : a <> FL) by (intros X; apply Hd; right; right; exact X).
  clear Hd.
  rewrite (Hk4 a Ha); [| rewrite EFA, ESH; change (fs_frame_bytes POLL_CID / 8) with 256; lia
    | rewrite EFL; exact Hd3 | lia].
  rewrite (KB a Ha ltac:(lia)).
  rewrite (Hk3 a Ha ltac:(lia) ltac:(lia)).
  exact (KA a Ha ltac:(tauto)). }
(* the 13 saved words at the stack free's return *)
assert (Hsaved4 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem4) (SP - fst o) =
    Some (bv_unsigned (YK11.getr (cx_regs c) (Z_to_bv 5 (snd o))))) POLL_SAVED).
{ apply Forall_forall. intros o Hino. cbv beta.
  pose proof (proj1 (Forall_forall _ _) Hsaved o Hino) as Ho. cbv beta in Ho.
  assert (Hfo : 8 <= fst o <= 104).
  { unfold POLL_SAVED in Hino. cbn [In] in Hino.
    repeat (destruct Hino as [<- | Hino]; [cbn [fst]; lia |]). destruct Hino. }
  rewrite <- Ho. apply rdword_ext. intros i Hi.
  apply KP4; [lia | lia | intros X; pose proof (N4 _ X); lia]. }
(* ---- run C, +0x334 .. +0x384 ---- *)
clear HS SHOK.
pose proof (prc_entry W2 regs4 (cx_regs c) mem4 SP V8 ltac:(lia) Hsaved4) as HS.
assert (HEIc : img_env VAL A_LIM (prc_E regs4 (cx_regs c))) by (unfold prc_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (prc_E regs4 (cx_regs c)) (mrestrict (w_H W2) mem4))
  by constructor.
assert (EWC : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (prc_E regs4 (cx_regs c)) n = YK11.getr regs4 r)
  by (intros n r Hn; unfold prc_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + PR_C2)) mem4 (YK11.seg_rom segs)) md4) Q) end.
paj_run_tok RUN HS HJ4 SHOK PR_B0.
{ pr_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
rename HF into HFc', HFr into HFrc, HG into HGc.
lazymatch type of HS with context [restrict _ ?m] => rename m into msC end.
(* run C writes no byte *)
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
  aview segs (w_H W2) (ms_mem msC) a = aview segs (w_H W2) mem4 a) by pr_frame_kept HFrc (fun _ : Z => False) V8.
(* the registers at the ret *)
assert (C1e : YK11.getr (ms_regs msC) 1 = YK11.getr (cx_regs c) 1).
{ pr_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (C10 : YK11.getr (ms_regs msC) 10 = w64 (cx_r c)).
{ pr_regv HS. cbn [sv_denot]. rewrite (EWC 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact V26. }
assert (HP : aregs_preserved (cx_regs c) (ms_regs msC)).
{ intros r Hr. apply pr_saved_cases in Hr.
  destruct Hr as [-> | [-> | [-> | Hr]]].
  - pr_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EWC 8%nat 8%bv eq_refl), V8.
    unfold SP, pw_SP, w64, spZ. apply Z_to_bv_bv_unsigned.
  - pr_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EWC 3%nat 3%bv eq_refl), V3.
    symmetry. exact Hgp.
  - pr_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EWC 4%nat 4%bv eq_refl), V4.
    symmetry. exact Htp.
  - destruct Hr as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
      pr_regv HS; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity. }
assert (Hpc : v_jalr (YK11.getr (ms_regs msC) 1) 0 = YK11.getr (cx_regs c) 1) by (rewrite C1e; exact Hret).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md5 := mdx) in * end.
clearbody md5.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  eapply (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport) W2 Ex ssx msx md5 _ HS eq_refl
    ltac:(clear; vm_compute; reflexivity)) end.
intros mat3.
set (md6 := with_vm_backing (m_vm_lazy md5) mat3 md5).
pose proof (ajournal_gx_materialize segs B LAWS transport_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ4)
  as HJ6.
fold md6 in HJ6. clearbody md6.
(* every byte outside the own frame and the window is the cut's, at the return *)
assert (KP5 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp1 - ESTACK <= a < sp1) \/ dkg_nf POLL_CID F FL a) ->
  aview segs (w_H W2) (ms_mem msC) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (KC a Ha ltac:(tauto)).
  apply KP4; [exact Ha | intros X; apply Hn; left; exact X | intros X; apply Hn; right; exact X]. }
assert (Eab' : ablocks B ly2 (stack_free_state POLL_CID pos S2) = ablocks B ly2 S2)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
unfold pw_post, transport_cg_post.
exists ly2, (stack_free_state POLL_CID pos S2), (ms_regs msC), (ms_mem msC), md6, 0.
split; [rewrite Hpc; reflexivity|].
split; [unfold POLL_EV; lia|].
split; [rewrite Z.add_0_r; exact HJ6|].
split; [exact HP|].
split; [exact (can_sf_frames POLL_CID pos S2 (frames (cx_Sc c)) Hfrs)|].
split; [rewrite Eab'; exact Hperm|].
split.
{ apply (pr_kept_nfz LAWS TG.G_HARNESS (cx_lyc c) (cx_Sc c) ly2 S2 (cx_W c) (cx_memc c) (cx_mdc c) W2 mem2 md2
    (ms_mem msC) (SP - POLL_STK) SP POLL_CID pos F FL poll_wr
    (fun a => (sp1 - ESTACK <= a < sp1) \/ dkg_nf POLL_CID F FL a)
    HARc HAR2 Hfrs Hbl ELF eq_refl eq_refl FFL HCE ltac:(lia)).
  - intros a [X | X]; [left; lia | right; exact X].
  - exact HK.
  - exact KP5.
  - intros a Ha. exact (pr_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6 a ltac:(lia)). }
split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
unfold pw_X.
split; [exact C10|].
split; [|split; [exact Hgf | exact Hinv]].
apply (tw_kept_GA (aview segs (w_H W2) mem2)); [exact HTW|].
intros b n i Hbn Hi.
assert (HG : inG TG.G_HARNESS (b + i))
  by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
destruct (HGX _ HG) as [HiG _].
pose proof (transport_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
apply KP5; [lia|]. intros [X | X]; [lia | exact (N2 _ X HiG)].
Qed.

End s.

Theorem pw_rel_piece : forall fx rc B MT, @pw_rel_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pw_rel_holds fx rc B MT). Qed.
