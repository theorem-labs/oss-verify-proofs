(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 445 of its 528 lines of code are new or changed and 682 lines of the source are left out. *)
(* diginet_session_close_seg_join: Lemma close_join : close_join_stmt (lib/B/Prog/diginet_session_close_segs.v), the
   join piece of image B's walk of diginet_session_close, offsets +0x8c .. +0xd4 of the listing
   lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x876d4 .. 0x8771c), reached from the head (close_go Bw
   false, s1 = 0) and from the send piece (s1 = the result of send_control).

   What the code does. +0x8c `addi a0, s0, 212` and the instrumented check of the 4-byte store at s + 212 (its shadow
   byte is 0: trans_close_cells), +0xa0 `sw zero, 212(s0)`: g_s.inflight := 0, so the world is close_w1 B1;
   +0xa4 `li a1, 3`, +0xa8 `li a2, 8`, +0xac `mv a0, s0`, +0xb0 `jal set_state` (return address +0xb4); +0xb4 `j`,
   +0xbc `mv a0, s1`, the four reloads of ra, s0, s1, s2 from the frame, `addi sp, sp, 32`, `ret`.

   One run of the token engine (lib/B/Prog/TransportGRunB.v paj_run_x) covers +0x8c .. +0xb0 from a state whose one
   region is g_s.inflight (writable, a byte of G) and whose shadow entry is g_s's payload; it stops at the call.
   set_state is a G-form callee composed in the same G journal (set_state_cg.v transport_set_state_cg, a premise of
   the walk), at the world close_w1 B1 with S_CLOSED and R_CLOSED (diginet_session_close_segs.v close_sstate_some);
   its trans_tframe_at is carried from the entry by lib/B/Prog/TransportGNoticeB.v trans_tframe_at_kept_gx over the
   written range widened by G (TransportGCg.v acall_kept_g_weaken; trans_tf_off_g and close_apart put TF outside it),
   its trans_rom_view_rd by close_rom, its
   sstate_apart is close_apart through close_wr_sstate. What it keeps folds into the walk's kept fact by
   lib/A/Prog/TransportGCg.v dk_kept_trans_nf_g (no own frame: NF is empty). After the return a second run, from a
   state whose one region is the frame with the four saved words as chunks (cr_entry), reloads them and stops at the
   `ret` (DgnTransportBPaLib.v paj_ret_at). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_close_cg diginet_session_close_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The return address of the call of set_state; the state at the cut (g_s.inflight as a writable region of s0, atom
   8; s0 is s and s2, atom 18, the shadow base, both exact); the shadow entry of g_s's payload; and the state at the
   return: the frame (base sp, atom 2) with the four saved words as chunks, valued by the extra atoms 32 .. 35 (s2, s1,
   s0 and ra at the entry). *)
Definition CLOSE_SRET : Z := AF_diginet_session_close + 0xb4.
Definition cj_rg_inf : YP09.region := YP09.mkRegion (Some 8%nat) 212 216 212 216 [].
Definition cj_facts : facts :=
  mkFacts [(8%nat, mkAF CLOSE_S CLOSE_S 6); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition cj_ss : sstate := mkSS CLOSE_JOIN sr_atoms [cj_rg_inf] None cj_facts.
Definition CJ_SH : list shent := [mkSHE 8 0 TW.SZ_g_s].
Definition CJ_Bx : sv := SOff 18 0.
Definition cr_rg_fr : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
   YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0))].
Definition cr_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition cr_ss : sstate := mkSS CLOSE_SRET sr_atoms [cr_rg_fr] None cr_facts.
Definition CR_B0 : Z * Z := (0, 0).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cj_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "cj_reg: no match for" T; fail
  end.

(* A callee-saved register, from the registers' equations. *)
Lemma cj_ap : forall regs regsF : bvmap 5 word,
  (forall q, q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ 18 <= q <= 27 ->
     YK11.getr regsF (Z_to_bv 5 q) = YK11.getr regs (Z_to_bv 5 q)) ->
  aregs_preserved regs regsF.
Proof. intros regs regsF H q Hq. exact (H q Hq). Qed.

Section join. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition cj_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition cr_E (regs4 regs : bvmap 5 word) : env :=
  Eimg (PI := PI_transportb)
    (Ereg regs4 [YK11.getr regs 18; YK11.getr regs 9; YK11.getr regs 8; YK11.getr regs 1]).

Lemma cj_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cj_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold cj_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma cr_ew_reg : forall regs4 regs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (cr_E regs4 regs) n = YK11.getr regs4 r.
Proof. intros regs4 regs n r Hn. unfold cr_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma cr_ew_extra : forall regs4 regs j, (j < 4)%nat ->
  ew (cr_E regs4 regs) (32 + j) =
  nth j [YK11.getr regs 18; YK11.getr regs 9; YK11.getr regs 8; YK11.getr regs 1] (Z_to_bv 64 0).
Proof. intros regs4 regs j Hj. unfold cr_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* g_s's payload is addressable at every AR state: the shadow of its 2283 whole granules is 0 (trans_close_cells). *)
Lemma cj_ra : forall ly S (W : world segs) mem md,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF CLOSE_S TW.SZ_g_s.
Proof.
intros ly S W mem md HZ HAR x Hx.
assert (ES : CLOSE_S = 6157888) by reflexivity. assert (SZ : TW.SZ_g_s = 18264) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md CLOSE_S (CLOSE_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow entry holds at every AR state. *)
Lemma cj_shok : forall ly S (W : world segs) mem md (E : env),
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  bv_unsigned (ew E 8) = CLOSE_S -> bv_unsigned (ew E 18) = SHADOW_OFF ->
  sh_ok segs CJ_Bx CJ_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HZ HAR U8 U18.
assert (ES : CLOSE_S = 6157888) by reflexivity. assert (SZ : TW.SZ_g_s = 18264) by reflexivity.
unfold sh_ok, CJ_SH. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E CJ_Bx 8 CLOSE_S TW.SZ_g_s CLOSE_S 0 TW.SZ_g_s
  (cj_ra ly S W mem md HZ HAR)).
- unfold U, CJ_Bx. cbn [sv_denot]. rewrite Z.add_0_r, U18. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, U8. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. rewrite SZ in Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The state at the cut, and the shadow entry. *)
Lemma cj_entry : forall ly S (W : world segs) regs mem md,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 8 = w64 CLOSE_S -> YK11.getr regs 18 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (cj_E regs) cj_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLOSE_JOIN)) mem (YK11.seg_rom segs))) /\
  sh_ok segs CJ_Bx CJ_SH (cj_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HZ HAR R8 R18.
assert (ES : CLOSE_S = 6157888) by reflexivity.
assert (U8 : bv_unsigned (ew (cj_E regs) 8) = CLOSE_S)
  by (rewrite (cj_ew_reg regs 8 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew (cj_E regs) 18) = SHADOW_OFF)
  by (rewrite (cj_ew_reg regs 18 18%bv eq_refl), R18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold cj_ss.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold cj_rg_inf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U8. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs G_HARNESS_B (CLOSE_S + o) G_HARNESS_B_rw).
    apply close_inG. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  + unfold cj_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U18. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ES; reflexivity].
- exact (cj_shok ly S W mem md (cj_E regs) HZ HAR U8 U18).
Qed.

(* The state at the return of set_state: the frame at sp holds the four saved words. *)
Lemma cr_entry : forall (W : world segs) regs4 regs mem,
  2 ^ 46 <= spZ regs4 <= 2 ^ 47 - 32 -> spZ regs4 mod 16 = 0 ->
  rdword (aview segs (w_H W) mem) (spZ regs4) = Some (bv_unsigned (YK11.getr regs 18)) ->
  rdword (aview segs (w_H W) mem) (spZ regs4 + 8) = Some (bv_unsigned (YK11.getr regs 9)) ->
  rdword (aview segs (w_H W) mem) (spZ regs4 + 16) = Some (bv_unsigned (YK11.getr regs 8)) ->
  rdword (aview segs (w_H W) mem) (spZ regs4 + 24) = Some (bv_unsigned (YK11.getr regs 1)) ->
  st_ok_pi segs VAL (cr_E regs4 regs) cr_ss
    (restrict (w_H W) (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + CLOSE_SRET)) mem (YK11.seg_rom segs))).
Proof.
intros W regs4 regs mem Hsp Hal V0 V8 V16 V24.
set (E := cr_E regs4 regs).
assert (Usp : bv_unsigned (ew E 2) = spZ regs4) by (unfold E; rewrite (cr_ew_reg regs4 regs 2 2%bv eq_refl); reflexivity).
pose proof (cr_ew_extra regs4 regs 0 ltac:(lia)) as E32. pose proof (cr_ew_extra regs4 regs 1 ltac:(lia)) as E33.
pose proof (cr_ew_extra regs4 regs 2 ltac:(lia)) as E34. pose proof (cr_ew_extra regs4 regs 3 ltac:(lia)) as E35.
cbn [Nat.add nth] in E32, E33, E34, E35. fold E in E32, E33, E34, E35.
assert (DEN : forall n (w : word), ew E n = w -> sv_denot E (SOff n 0) = Z_to_bv 64 (bv_unsigned w))
  by (intros n w Hn; cbn [sv_denot]; rewrite Hn, Z.add_0_r; reflexivity).
assert (RW : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8))
  by (intros w; pose proof (bv_unsigned_in_range 64 w) as Hw; change (bv_modulus 64) with (2 ^ 64) in Hw;
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
rewrite restrict_mkst_fx. unfold cr_ss.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold cr_rg_fr, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  + apply (chunk_ok_val segs E _ (spZ regs4) 0 8 (SOff 32 0) (bv_unsigned (YK11.getr regs 18)));
      [exact (DEN _ _ E32) | apply RW | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ V0).
  + apply (chunk_ok_val segs E _ (spZ regs4) 8 8 (SOff 33 0) (bv_unsigned (YK11.getr regs 9)));
      [exact (DEN _ _ E33) | apply RW | lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ V8).
  + apply (chunk_ok_val segs E _ (spZ regs4) 16 8 (SOff 34 0) (bv_unsigned (YK11.getr regs 8)));
      [exact (DEN _ _ E34) | apply RW | lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ V16).
  + apply (chunk_ok_val segs E _ (spZ regs4) 24 8 (SOff 35 0) (bv_unsigned (YK11.getr regs 1)));
      [exact (DEN _ _ E35) | apply RW | lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ V24).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split; exact I.
- unfold cr_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma close_join : @close_join_stmt fx rc B MT.
Proof.
unfold close_join_stmt, close_join_at.
intros LAWS0 HSS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HCELLS & HCC & HRU & HRE & LAWS & MTL & HGX).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF &
  Hrom & Hapart & Htfg & Hinv1 & Hinv4 & Hcnt & Hev).
pose proof HCUR as ((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved) & HS1 & Htw1 & Hgf1).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R18 & R1927) & R9).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct close_stk_val as (FSTK & FSC & FSS & FFR).
destruct close_ev_val as (EV0 & EVS & EVSS).
assert (Ee : e = 0) by lia. subst e. rewrite Z.add_0_r in HJ1.
assert (CS : CLOSE_S = 6157888) by reflexivity.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof HJ1 as (_ & _ & (memS1 & HJi1 & _) & _).
rewrite ?Z.add_0_r in HJi1.
pose proof HJi1 as (_ & Hlyle1 & _).
clear HJi1 memS1.
pose proof Hlyle as (_ & _ & _ & _ & _ & ELF0 & _ & _ & _ & ESLO0 & ESHI0 & _).
pose proof Hlyle1 as (_ & _ & _ & _ & _ & ELF1 & _ & _ & _ & ESLO1 & ESHI1 & _).
assert (Elo : ly_stk_lo ly2 = ly_stk_lo lyc) by congruence.
assert (Ehi : ly_stk_hi ly2 = ly_stk_hi lyc) by congruence.
assert (Hfa : forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos)
  by (intros cid pos; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
assert (Hfr : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfrs; exact Hf).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - CLOSE_STK) by lia.
pose proof (bv_unsigned_in_range 64 (YK11.getr regs 2)) as HspR.
change (bv_modulus 64) with (2 ^ 64) in HspR. change (bv_unsigned (YK11.getr regs 2)) with (spZ regs) in HspR.
assert (USP2 : spZ regs2 = spZ regs - 32)
  by (unfold spZ at 1; rewrite R2; unfold w64, CLOSE_FRAME; apply unsigned_lit_small; lia).
(* the model and the world B1 *)
assert (HLB : length B1 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw1).
assert (LB1 : Z.of_nat (length B1) = TW.W_LEN) by (rewrite HLB; rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
pose proof (close_sstate_some timg_B TF Bw now Bw' B1 r r Hm HS1) as HSM.
(* ---- +0x8c .. +0xb0: the checked store at s + 212, the arguments, the call ---- *)
destruct (cj_entry ly2 S2 W2 regs2 mem2 md2 HCC HAR2 R8 R18) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (cj_E regs2)) by (unfold cj_E; apply Eimg_env).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
assert (U8c : bv_unsigned (ew (cj_E regs2) 8) = CLOSE_S)
  by (rewrite (cj_ew_reg regs2 8 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLOSE_JOIN)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ1 SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  repeat (apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U8c in Ha;
      apply close_inG; unfold TW.SZ_g_s; lia |]).
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
(* the run wrote g_s.inflight only *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (CLOSE_S + 212 <= a < CLOSE_S + 216) ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => CLOSE_S + 212 <= x < CLOSE_S + 216) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin' Hx.
  lazymatch type of Hin' with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin' end.
  cbn [In] in Hin'.
  repeat (destruct Hin' as [Hin' | Hin']; [injection Hin' as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U8c in Hx; lia |]).
  destruct Hin'. }
assert (GRo : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the store left 0 *)
lazymatch type of HS with
| OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?EF _ (restrict ?Hh ?m) =>
    pose proof (st_ok_region_nth (segs := sg) EF _ (restrict Hh m) 0 _ HS eq_refl) as RG0; set (E1 := EF) in *
| st_ok_pi _ _ ?EF _ _ => pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0; set (E1 := EF) in *
end.
cbn [ms_mem restrict] in RG0.
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew (cj_E regs2) n)
  by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
assert (U8f : bv_unsigned (ew E1 8) = CLOSE_S) by (rewrite E1lo by lia; exact U8c).
assert (ZI : forall j, 0 <= j < 4 -> aview segs (w_H W2) (ms_mem ms) (CLOSE_S + 212 + j) = Some 0).
{ intros j Hj.
  assert (HV : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (CLOSE_S + 212) 4 0)
    by exact (can_field_of_region E1 _ 8 CLOSE_S _ 212 216 212 216 212 4%N (SLit 0) 0 RG0 U8f
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  pose proof (HV (Z.to_nat j) ltac:(lia)) as H0. rewrite Z2Nat.id in H0 by lia.
  unfold aview. rewrite H0. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  lazymatch goal with |- context [?f 0 4%nat (Z.to_nat j)] => unfold f end.
  rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity. }
clear RG0.
set (mC := ms_mem ms) in *.
(* the world at the call memory *)
assert (TWC : tw_at TMAP_B (aview segs (w_H W2) mC) (close_w1 B1)).
{ apply (close_tw_w1 (aview segs (w_H W2) mem2) _ B1 Htw1 ZI).
  intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
  apply KR; [lia | exact Hn]. }
(* what the call keeps, at the call memory *)
assert (KCJ : acall_kept_g segs B G_HARNESS_B lyc Sc W memc W2 mC (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ apply (dk_kept_step_gw segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc W2 mem2 mC
    (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw) (fun x => CLOSE_S + 212 <= x < CLOSE_S + 216) HARc HK).
  - intros a Ha Hn. exact (KR a Ha Hn).
  - exact GRo.
  - intros a Ha Hc. exfalso. lia.
  - intros b m i Hb Hi Hz. right; left. unfold twb_fld, TW.A_S_inflight, TB_g_s. unfold CLOSE_S, TB_g_s in Hz. lia.
  - intros a Hz Hi HnG _ _. apply HnG. apply close_inG. unfold TW.SZ_g_s. lia.
  - intros cid pos a Hin Hr Hz. right; left. unfold twb_fld, TW.A_S_inflight, TB_g_s. unfold CLOSE_S, TB_g_s in Hz.
    lia. }
(* the four saved words, at the call memory *)
assert (HSo : forall o, In o CLOSE_SAVED -> 8 <= fst o <= 32).
{ intros o Ho. unfold CLOSE_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
(* the registers at the call *)
cj_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + CLOSE_SRET)) Q1 ltac:(apply codeptr_val; exact HEI).
cj_reg HS (2%bv : bv 5) (YK11.getr regs2 2) Q2
  ltac:(cbn [sv_denot]; rewrite (E1lo 2%nat ltac:(lia)), (cj_ew_reg regs2 2 2%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cj_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (E1lo 3%nat ltac:(lia)), (cj_ew_reg regs2 3 3%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
cj_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (E1lo 4%nat ltac:(lia)), (cj_ew_reg regs2 4 4%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
cj_reg HS (10%bv : bv 5) (w64 SSTATE_S) Q10
  ltac:(cbn [sv_denot]; rewrite (E1lo 8%nat ltac:(lia)), (cj_ew_reg regs2 8 8%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact R8).
cj_reg HS (11%bv : bv 5) (w64 TS0.DIGINET_S_CLOSED) Q11 ltac:(reflexivity).
cj_reg HS (12%bv : bv 5) (w64 TS0.DIGINET_R_CLOSED) Q12 ltac:(reflexivity).
assert (HPC : aregs_preserved regs2 (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ ms regs2 [] HS).
  - split; [intros n Hn; rewrite E1lo by lia; unfold cj_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity. }
assert (USPC : spZ (ms_regs ms) = spZ regs - 32) by (unfold spZ at 1; rewrite Q2; exact USP2).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HARC.
(* set_state's premises at the call state *)
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO0, ESHI0; lia).
assert (PTF : trans_tframe_at B ly2 S2 W2 mC (ms_regs ms) SSTATE_STK TF).
{ apply (trans_tframe_at_kept_gx B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mC md1
    (fun a => close_wr TF Bw a \/ inG G_HARNESS_B a) regs (ms_regs ms) CLOSE_STK SSTATE_STK TF HARc HARC Hbl Hfr Hfa
    Elo Ehi HSTKLT).
  - eapply acall_kept_g_weaken; [|exact KCJ]. intros a Ha. left. exact Ha.
  - unfold gx_kept_ex. intros a HaG HnE. exfalso. exact (HnE (or_intror HaG)).
  - intros fr Efr a Ha [Hw | HaG]; [exact (Hapart a Hw fr Efr Ha) | exact (Htfg fr Efr a Ha HaG)].
  - intros a Ha [Hw | HaG].
    + pose proof (inG_low segs B transportb_segs_low _ a HGX (close_wr_G TF Bw a Hw)) as Hl.
      unfold kLowMemEnd in *. lia.
    + pose proof (inG_low segs B transportb_segs_low _ a HGX HaG) as Hl. unfold kLowMemEnd in *. lia.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - exact HTF. }
assert (PROM : trans_rom_view_rd W2 mC) by exact (close_rom B HRU HRE lyc Sc W memc W2 mC _ _ _ KCJ Hrom).
assert (PAP : sstate_apart TF (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED).
{ intros x Hx fr Efr. apply (Hapart x); [|exact Efr].
  apply (proj2 (close_wr_sstate TF Bw x)). right; right. exists B1, r. split; [exact HS1 | exact Hx]. }
assert (HCNT : count_cid SSTATE_CID (frames S2) < fs_frames SSTATE_CID).
{ rewrite Hfrs. change SSTATE_CID with CLOSE_CID. lia. }
assert (PGF : TW.g_fail_next (close_w1 B1) <= 1) by (rewrite (close_gfn1 B1 LB1); exact Hgf1).
assert (EBR : BASE + CLOSE_SRET = 0x876fc) by (vm_compute; reflexivity).
(* +0xb0: the call of set_state *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_set_state)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ exact (HSS fx STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mC md1 k (ms_regs ms)
    TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED TF (close_w1 B1) Bw' HJ1
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb));
          [unfold CLOSE_SRET, AF_diginet_session_close; lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, EBR; rewrite unsigned_lit_small by lia; lia)
    Q3 Q4 Q10 Q11 Q12
    ltac:(rewrite USPC; replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia;
          rewrite Z_mod_plus_full; exact Hsp16)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    TWC PGF HSM
    ltac:(unfold TS0.DIGINET_S_CLOSED; lia) ltac:(unfold TS0.DIGINET_R_CLOSED; lia)
    PTF PROM PAP HCNT ltac:(lia)). }
cbv beta.
intros W4 c4 _ HPOST.
unfold transport_sstate_post, transport_cg_post in HPOST.
destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & e4 & Ec4 & He4 & HJ4 & HP4 & Hfr4 & Hperm4 & HK4 & Hmo4 &
  (HTW4 & HGF4)).
assert (Ee4 : e4 = 0) by lia. subst e4. rewrite Z.add_0_r in HJ4.
rewrite Q1 in Ec4. subst c4.
rewrite USPC in HK4.
(* what the call keeps, at mem4 *)
assert (KC4 : acall_kept_g segs B G_HARNESS_B lyc Sc W memc W4 mem4 (spZ regs - CLOSE_STK) (spZ regs)
  (close_wr TF Bw)).
{ apply (dk_kept_trans_nf_g segs B G_HARNESS_B lyc Sc ly2 S2 W memc W2 mC W4 mem4
    (spZ regs - CLOSE_STK) (spZ regs) (spZ regs - 32 - SSTATE_STK) (spZ regs - 32) (close_wr TF Bw)
    (sstate_wr (close_w1 B1) TS0.DIGINET_S_CLOSED TS0.DIGINET_R_CLOSED) (fun _ : Z => False)).
  - lia.
  - lia.
  - exact Hfa.
  - exact Hfr.
  - exact Hbl.
  - intros b m i _ _ [].
  - intros cid pos a _ _ [].
  - exact KCJ.
  - exact HK4.
  - lia.
  - lia.
  - intros a Ha. left. apply (proj2 (close_wr_sstate TF Bw a)). right; right. exists B1, r.
    split; [exact HS1 | exact Ha]. }
(* the four saved words at mem4: above alloc_ceiling, outside set_state's window, outside g_s.inflight *)
assert (KSV : forall o, In o CLOSE_SAVED ->
  rdword (aview segs (w_H W4) mem4) (spZ regs - fst o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))).
{ intros o Ho. rewrite Forall_forall in Hsaved. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. pose proof HK4 as (K41 & _).
  apply rdword_ext. intros i Hi.
  transitivity (aview segs (w_H W2) mC (spZ regs - fst o + i)).
  - apply K41; lia.
  - apply KR; lia. }
pose proof (KSV (32, 18) ltac:(unfold CLOSE_SAVED; cbn [In]; right; right; right; left; reflexivity)) as V0.
pose proof (KSV (24, 9) ltac:(unfold CLOSE_SAVED; cbn [In]; right; right; left; reflexivity)) as V8.
pose proof (KSV (16, 8) ltac:(unfold CLOSE_SAVED; cbn [In]; right; left; reflexivity)) as V16.
pose proof (KSV (8, 1) ltac:(unfold CLOSE_SAVED; cbn [In]; left; reflexivity)) as V24.
cbn [fst snd] in V0, V8, V16, V24.
(* the callee-saved registers at the return *)
assert (P4 : forall q, acallee_saved q -> YK11.getr regs4 (Z_to_bv 5 q) = YK11.getr regs2 (Z_to_bv 5 q))
  by (intros q Hq; rewrite (HP4 q Hq); exact (HPC q Hq)).
assert (USP4 : spZ regs4 = spZ regs - 32).
{ rewrite <- USP2. unfold spZ. f_equal. exact (P4 2 ltac:(unfold acallee_saved; lia)). }
clear dependent ms.
(* ---- +0xb4 .. +0xd4: the epilogue, from the frame's four saved words ---- *)
pose proof (cr_entry W4 regs4 regs mem4 ltac:(rewrite USP4; lia)
  ltac:(rewrite USP4; replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia;
        rewrite Z_mod_plus_full; exact Hsp16)
  ltac:(rewrite USP4; replace (spZ regs - 32) with (spZ regs - 32) by lia; exact V0)
  ltac:(rewrite USP4; replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia; exact V8)
  ltac:(rewrite USP4; replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia; exact V16)
  ltac:(rewrite USP4; replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia; exact V24)) as HSR.
assert (HEIR : img_env VAL A_LIM (cr_E regs4 regs)) by (unfold cr_E; apply Eimg_env).
assert (SHOKR : sh_ok segs (SOff 32 0) (@nil shent) (cr_E regs4 regs) (mrestrict (w_H W4) mem4)) by constructor.
assert (UspR : bv_unsigned (ew (cr_E regs4 regs) 2) = spZ regs - 32)
  by (rewrite (cr_ew_reg regs4 regs 2 2%bv eq_refl); exact USP4).
try clear HEI. try clear SHOK.
rename HEIR into HEI.
paj_run_tok RUN HSR HJ4 SHOKR CR_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
set (mdF := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody mdF. clear mat.
lazymatch type of HSR with st_ok_pi _ _ ?EF _ (restrict _ ?m) => rename m into msF; set (EX := EF) in HSR end.
assert (KRF : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W4) (ms_mem msF) a = aview segs (w_H W4) mem4 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin' Hx.
  lazymatch type of Hin' with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin' end.
  cbn [In] in Hin'.
  repeat (destruct Hin' as [Hin' | Hin']; [injection Hin' as <- <- <-; cbn [base_val] in Hx; lia |]).
  destruct Hin'. }
assert (GRF : forall a, apresent (w_H W4) mem4 a -> apresent (w_H W4) (ms_mem msF) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (HEF : forall n, (n < 1024)%nat -> ew EX n = ew (cr_E regs4 regs) n)
  by (intros n Hn; unfold EX; rewrite ?ew_ewset_other by lia; reflexivity).
(* the registers at the return *)
pose proof (cr_ew_extra regs4 regs 0 ltac:(lia)) as X32. pose proof (cr_ew_extra regs4 regs 1 ltac:(lia)) as X33.
pose proof (cr_ew_extra regs4 regs 2 ltac:(lia)) as X34. pose proof (cr_ew_extra regs4 regs 3 ltac:(lia)) as X35.
cbn [Nat.add nth] in X32, X33, X34, X35.
cj_reg HSR (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite (HEF 35%nat ltac:(lia)), X35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HSR (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) RF2
  ltac:(cbn [sv_denot]; rewrite (HEF 2%nat ltac:(lia)), UspR;
        rewrite <- (Z_to_bv_bv_unsigned 64 (YK11.getr regs (Z_to_bv 5 2))); f_equal;
        change (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))) with (spZ regs); lia).
cj_reg HSR (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) RF8
  ltac:(cbn [sv_denot]; rewrite (HEF 34%nat ltac:(lia)), X34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HSR (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) RF9
  ltac:(cbn [sv_denot]; rewrite (HEF 33%nat ltac:(lia)), X33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HSR (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) RF18
  ltac:(cbn [sv_denot]; rewrite (HEF 32%nat ltac:(lia)), X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cj_reg HSR (10%bv : bv 5) (w64 r) RF10
  ltac:(cbn [sv_denot]; rewrite (HEF 9%nat ltac:(lia)), (cr_ew_reg regs4 regs 9 (Z_to_bv 5 9) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; rewrite (P4 9 ltac:(unfold acallee_saved; lia)); exact R9).
cj_reg HSR (Z_to_bv 5 3) (YK11.getr regs4 (Z_to_bv 5 3)) RF3
  ltac:(cbn [sv_denot]; rewrite (HEF 3%nat ltac:(lia)), (cr_ew_reg regs4 regs 3 (Z_to_bv 5 3) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cj_reg HSR (Z_to_bv 5 4) (YK11.getr regs4 (Z_to_bv 5 4)) RF4
  ltac:(cbn [sv_denot]; rewrite (HEF 4%nat ltac:(lia)), (cr_ew_reg regs4 regs 4 (Z_to_bv 5 4) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
assert (RFq : forall q, 19 <= q <= 27 -> YK11.getr (ms_regs msF) (Z_to_bv 5 q) = YK11.getr regs4 (Z_to_bv 5 q)).
{ intros q Hq.
  assert (Hq' : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
  destruct Hq' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]]];
  lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?qq) = _ =>
    let n := eval vm_compute in (Z.to_nat qq) in
    refine (eq_trans (st_ok_pi_restrict_reg _ _ _ _ _ HSR) _);
    lazymatch type of HSR with st_ok_pi _ _ _ ?ssx _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) (Z_to_bv 5 qq)) in
      change (sv_denot EX e = YK11.getr regs4 (Z_to_bv 5 qq)) end;
    cbn [sv_denot]; rewrite (HEF n ltac:(lia)), (cr_ew_reg regs4 regs n (Z_to_bv 5 qq) eq_refl), Z.add_0_r,
      Z_to_bv_bv_unsigned; reflexivity end. }
assert (HPF : aregs_preserved regs (ms_regs msF)).
{ apply cj_ap. intros q Hq.
  destruct Hq as [->|[->|[->|[->|[->|Hq]]]]].
  - exact RF2.
  - rewrite RF3, (P4 3 ltac:(unfold acallee_saved; lia)). exact R3.
  - rewrite RF4, (P4 4 ltac:(unfold acallee_saved; lia)). exact R4.
  - exact RF8.
  - exact RF9.
  - destruct (Z.eq_dec q 18) as [->|Hq18]; [exact RF18|].
    rewrite (RFq q ltac:(lia)), (P4 q ltac:(unfold acallee_saved; lia)). exact (R1927 q ltac:(lia)). }
(* ---- the return ---- *)
eapply (RET W4 _ _ _ _ _ HSR eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
unfold transport_close_post, transport_cg_post.
exists ly4, S4, (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy mdF) mat' mdF), 0.
split; [rewrite RF1; unfold YK0s.ret_ok in Hret; rewrite Hret; reflexivity|].
split; [rewrite EV0; lia|].
split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ4|].
split; [exact HPF|].
split; [rewrite Hfr4; exact Hfrs|].
split; [exact (Permutation_trans Hperm4 Hperm)|].
split.
{ apply (dk_kept_step_gw segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc W4 mem4 (ms_mem msF)
    (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw) (fun _ : Z => False) HARc KC4).
  - intros a Ha _. exact (KRF a Ha).
  - exact GRF.
  - intros a [].
  - intros b m i _ _ [].
  - intros a [].
  - intros cid pos a _ _ []. }
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo4)|].
split; [exact RF10|].
split; [|exact HGF4].
apply (tw_kept TMAP_B (aview segs (w_H W4) mem4)); [exact HTW4|].
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
apply KRF. lia.
Qed.

End join.
