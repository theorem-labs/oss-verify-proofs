(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v; 507 of its 577 lines of code are new or changed and 960 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_submit_seg_app.v, with its numbers changed; 282 of its 480 lines of code are new or changed and 379 lines of the source are left out. *)
(* diginet_session_submit_seg_loop: Lemma ssw_seg_loop, the search of diginet_session_submit over the queue
   (diginet_session.c:337-343) from the cut LOOP (+0x164, 0x8a054) of lib/A/Prog/diginet_session_submit_segs.v,
   given the cut APP (lib/A/Prog/diginet_session_submit_seg_app.v).

   What the code does at the head, at index j (a0 = &s->queue[j], a1 = a0 + 28, a3 = queued - j, a4 = the key
   sign-extended):
     +0x164 .. +0x174  the shadow check of the 4-byte load at a1 (g_s's zero shadow), a5 = s->queue[j].key;
     +0x178            `beq a5, a4`: a match goes to +0x1a4;
     +0x17c .. +0x188  a0 += 32, a3 -= 1, a1 += 32, `beq a3, 0`: the end of the queue goes to the append (+0xcc);
     +0x18c            back to the head at j + 1;
     +0x1a4 .. +0x1ac  a2 = 32, a1 = c, the call of __asan_memcpy at +0x1ac (return address +0x1b0): s->queue[j] = *c;
     +0x1b0 .. +0x1d0  the check of the 8-byte access at s + 18248, the load of g_s.stats.coalesced, + 1, the store,
                       a0 = the shadow byte (0), to the epilogue and the return.

   The loop is YA0n.v SRr_loopZ over the measure queued - j: a turn either returns (a match), goes to the append
   (the cut APP, with the model's search at Some None), or comes back to the head at j + 1.

   The symbolic state at the head: the registers as atoms 0 .. 31 (a1, a2, s2, s3 as the cut says), atom 32 the shadow
   base, atom 33 s->queue[j].key, atom 34 g_s.stats.coalesced, atoms 35 .. 39 the entry values of s3, s2, s1, s0,
   ra. Regions: the key of entry j (read-only) and the frame (read-only); after the memcpy, g_s.stats.coalesced
   (writable, atom 34). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_body_check_cg diginet_session_submit_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_submit_segs diginet_session_submit_seg_app.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_body_check_cg.
Module SSK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_submit_seg_kit.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the head                                      *)
(* ------------------------------------------------------------------ *)

Definition loop_sr : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 11 (SOff 10 28)) 12 (SAlu ALU_SRL (SOff 9 18144) (SLit 3)))
    18 (SOff 9 18144)) 19 (SOff 32 0).
(* s->queue[j].key at a0 + 28, read-only. *)
Definition loop_key : YP09.region := YP09.mkRegion (Some 10%nat) 28 32 0 0 [YP09.mkChunk 28 (CVal 4 (SOff 33 0))].
(* g_s.stats.coalesced (s + 18248, 8 bytes), writable, added after the memcpy. *)
Definition loop_gc : YP09.region :=
  YP09.mkRegion (Some 9%nat) 18248 18256 18248 18256 [YP09.mkChunk 18248 (CVal 8 (SOff 34 0))].
Definition loop_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - 48) (2 ^ 47 - 48) 4); (8%nat, mkAF 4096 (2 ^ 47 - 32) 2);
           (9%nat, mkAF TA_g_s TA_g_s 6); (10%nat, mkAF (TA_g_s + 1760) (TA_g_s + 1760 + 32 * 511) 5);
           (13%nat, mkAF 1 (2 ^ 32 - 1) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition loop_ss : sstate := mkSS SSW_LOOP loop_sr [loop_key; ssw_fr 35] None loop_facts.
Definition LOOP_SH : list shent := [mkSHE 10 28 36; mkSHE 9 18248 18256].

(* `addi a3, a3, -1; beq a3, 0` (+0x180 / +0x188): the last entry was scanned. *)
Lemma ssw_br_a3 : forall E v, ew E 13 = Z_to_bv 64 v -> 1 <= v < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SOff 13 (-1))) (sv_denot E (SLit 0)) = (v - 1 =? 0).
Proof.
  intros E v H Hv. rewrite SSK.ssk_br_eq_U, U_SOff, U_SLit, H, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Section loop. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The head's valuation: the registers, the shadow base, the entry's key, coalesced, the five saved words. *)
Definition loop_extra (c : ssw_ctx) (j : Z) : list word :=
  [w64 SHADOW_OFF; w64 (TW.S_queue_key (cx_Bw c) j); w64 (TW.S_stats_coalesced (cx_Bw c));
   YK11.getr (cx_regs c) 19; YK11.getr (cx_regs c) 18; YK11.getr (cx_regs c) 9; YK11.getr (cx_regs c) 8;
   YK11.getr (cx_regs c) 1].
Definition loop_E (c : ssw_ctx) (j : Z) (regs' : bvmap 5 word) : env :=
  Eimg (PI := PI_transport) (Ereg regs' (loop_extra c j)).

(* The head's shadow entries: the key's granule of entry j, coalesced's granule, at every AR state. *)
Lemma loop_shok : forall ly S (W : world segs) mem md (E : env) j,
  trans_ssubmit_cells B -> @AR rc segs B ly S W mem md -> 0 <= j < 512 ->
  ew E 9 = w64 TA_g_s -> ew E 10 = w64 (TA_g_s + 1760 + 32 * j) -> ew E 32 = w64 SHADOW_OFF ->
  sh_ok segs SSW_Bx LOOP_SH E (mrestrict (w_H W) mem).
Proof.
  intros ly S W mem md E j HSC HAR Hj E9 E10 E32.
  assert (EC : TA_g_s = 6158784) by reflexivity.
  assert (UB : U E SSW_Bx = SHADOW_OFF).
  { unfold U, SSW_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity. }
  unfold sh_ok, LOOP_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range segs (w_H W) mem E SSW_Bx 10 TA_g_s 18264 (TA_g_s + 1760 + 32 * j) 28 36
      (ssw_gs_ra B ly S W mem md HSC HAR) UB).
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E SSW_Bx 9 TA_g_s 18264 TA_g_s 18248 18256
      (ssw_gs_ra B ly S W mem md HSC HAR) UB).
    + unfold U. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The symbolic state at the head holds of the machine state there. *)
Lemma loop_entry : forall c j lyX SX (WX : world segs) regs' m md,
  ssw_rt B MT -> ssw_ok B c -> ssw_cur B MT c lyX SX WX m md -> ssw_rg B c regs' ->
  YK11.getr regs' 10 = w64 (TA_g_s + 1760 + 32 * j) -> YK11.getr regs' 11 = w64 (TA_g_s + 1788 + 32 * j) ->
  YK11.getr regs' 13 = w64 (ssw_q c - j) -> 0 <= j < ssw_q c -> j < 512 ->
  st_ok_pi segs VAL (loop_E c j regs') loop_ss
    (restrict (w_H WX) (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + SSW_LOOP)) m (YK11.seg_rom segs))) /\
  sh_ok segs SSW_Bx LOOP_SH (loop_E c j regs') (mrestrict (w_H WX) m).
Proof.
  intros c j lyX SX WX regs' m md HRT HOK HCUR HRG G10 G11 G13 Hj Hj512.
  pose proof HRT as (_ & HSC & LAWS & _).
  pose proof (ssw_ok_stack B c HOK) as (_ & Hsp & _).
  pose proof (ssw_ok_cp B MT c HRT HOK) as (Hc0 & Hc47 & _).
  assert (Hcp4 : cx_cp c mod 4 = 0)
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H4 & _); exact H4).
  assert (Hsp16 : ssw_SP c mod 16 = 0) by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & H16 & _); exact H16).
  destruct HCUR as (HJ & _ & _ & _ & (_ & _ & _ & Htw) & HSV).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof HRG as (G2 & G3 & G4 & G8 & G9 & G12 & G18 & G19 & _).
  set (E := loop_E c j regs').
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
    by (intros n r Hn; unfold E, loop_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (EX : forall i, (i < 8)%nat -> ew E (32 + i) = nth i (loop_extra c j) (Z_to_bv 64 0))
    by (intros i Hi; unfold E, loop_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
  pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38.
  pose proof (EX 7%nat ltac:(lia)) as E39.
  cbn [Nat.add nth loop_extra] in E32, E33, E35, E36, E37, E38, E39.
  pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite G2 in E2.
  pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite G8 in E8.
  pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite G9 in E9.
  pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite G10 in E10.
  pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite G13 in E13.
  assert (EC : TA_g_s = 6158784) by reflexivity.
  assert (Rq : 0 <= ssw_q c < 2 ^ 32) by (unfold ssw_q; exact (TWL.u_at_range _ _ 4)).
  assert (Rk : 0 <= TW.S_queue_key (cx_Bw c) j < 2 ^ 32) by (unfold TW.S_queue_key; exact (TWL.u_at_range _ _ 4)).
  assert (U2 : bv_unsigned (ew E 2) = ssw_SP c - 48) by (apply ssw_U; [exact E2 | lia]).
  assert (U10 : bv_unsigned (ew E 10) = TA_g_s + 1760 + 32 * j) by (apply ssw_U; [exact E10 | lia]).
  split.
  - rewrite restrict_mkst_fx. unfold loop_ss.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + unfold loop_sr.
      apply ssw_regs_ok_pin; [| reflexivity | rewrite G19; apply ssw_soff0; exact E32].
      apply ssw_regs_ok_pin; [| reflexivity | rewrite G18; cbn [sv_denot]; rewrite E9; apply bv_eq; vm_compute; reflexivity].
      apply ssw_regs_ok_pin; [| reflexivity | rewrite G12; cbn [sv_denot]; rewrite E9; apply bv_eq; vm_compute; reflexivity].
      apply ssw_regs_ok_pin; [apply regs_ok_Eimg_Ereg | reflexivity |].
      rewrite G11. rewrite (ssw_soffk E 10 28 (TA_g_s + 1760 + 32 * j) E10) by lia. f_equal. lia.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold loop_key, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (TA_g_s + 1760 + 32 * j) 28 4 (SOff 33 0) (TW.S_queue_key (cx_Bw c) j));
          [apply ssw_soff0; exact E33 | exact Rk | lia |].
        pose proof (tw_read_val segs _ TMAP_A (cx_Bw c) TW.OFF_g_s TA_g_s TW.SZ_g_s (1788 + 32 * j) 4 TMAP_A_ok Htw
          TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as V.
        replace (TA_g_s + 1760 + 32 * j + 28) with (TA_g_s + (1788 + 32 * j)) by lia.
        unfold TW.S_queue_key, TW.A_S_queue_key.
        replace (TW.OFF_g_s + 1760 + 32 * j + 28) with (TW.OFF_g_s + (1788 + 32 * j)) by lia. exact V.
      * exact (ssw_fr_ok c E WX m 35 HSV U2 Hsp E35 E36 E37 E38 E39).
    + apply pairwise_disjoint_of_extents.
      unfold loop_key, ssw_fr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U2, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; first [exact I | lia].
    + unfold loop_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U10, (ssw_U E 8 (cx_cp c) E8 ltac:(lia)), (ssw_U E 9 TA_g_s E9 ltac:(lia)),
        (ssw_U E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)),
        (ssw_U E 33 (TW.S_queue_key (cx_Bw c) j) E33 ltac:(lia)), (ssw_U E 13 (ssw_q c - j) E13 ltac:(lia)).
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 6) with 64. change (2 ^ 5) with 32.
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (H48 : (ssw_SP c - 48) mod 16 = 0)
        by (replace (ssw_SP c - 48) with (ssw_SP c + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp16).
      assert (H10 : (TA_g_s + 1760 + 32 * j) mod 32 = 0)
        by (rewrite EC; replace (6158784 + 1760 + 32 * j) with (j * 32 + 192517 * 32) by lia;
            rewrite Z_mod_plus_full; apply Z_mod_mult).
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite EC; reflexivity].
  - exact (loop_shok lyX SX WX m md E j HSC HAR ltac:(lia) E9 E10 E32).
Qed.

End loop.

(* ssw_rg of the machine state of HS, whose symbolic registers keep the cut's layout (a cut's run). *)
Ltac ssw_rg_cut HS HEXF EE E2 E3 E4 E8 E9 E32 G20 :=
  let at_ := (fun H => first [exact H | rewrite HEXF by lia; exact H]) in
  split; [ssw_rv_open HS; apply ssw_soff0; at_ E2 |];
  split; [ssw_rv_open HS; apply ssw_soff0; at_ E3 |];
  split; [ssw_rv_open HS; apply ssw_soff0; at_ E4 |];
  split; [ssw_rv_open HS; apply ssw_soff0; at_ E8 |];
  split; [ssw_rv_open HS; apply ssw_soff0; at_ E9 |];
  split; [ssw_rv_open HS; cbn [sv_denot]; rewrite ?HEXF by lia; rewrite E9; apply bv_eq; vm_compute; reflexivity |];
  split; [ssw_rv_open HS; cbn [sv_denot]; rewrite ?HEXF by lia; rewrite E9; apply bv_eq; vm_compute; reflexivity |];
  split; [ssw_rv_open HS; apply ssw_soff0; at_ E32 |];
  let r := fresh "r" in let Hr := fresh "Hr" in let Er := fresh "Er" in
  intros r Hr; rewrite <- (G20 r Hr);
  assert (Er : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Er as [-> | Er];
    [ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXF by lia; apply EE; reflexivity |]);
  subst r; ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXF by lia; apply EE; reflexivity.

Section loopw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* One turn of the search from the head at j. *)
Lemma loop_turn : (forall c, @ssw_app_cut fx rc B MT c) -> forall c, ssw_rt B MT -> ssw_ok B c ->
  forall j (WX : world segs) cf, @ssw_loop_at fx rc B MT c j WX cf ->
  SRr segs WX cf (fun W' c' => ssw_post B MT c W' c' \/
    exists j', 0 <= ssw_q c - j' < ssw_q c - j /\ @ssw_loop_at fx rc B MT c j' W' c').
Proof.
intros HAPP c HRT HOK j WX cf (lyX & SX & regs' & m & md & -> & HCUR & HRG & G10 & G11 & G13 & G14 & Hj & HM).
pose proof HRT as (HCELLS & HSC & LAWS & MTL & HGX & HGE & HBC & HAI0).
pose proof (ssw_ok_stack B c HOK) as (HAR0 & Hsp & Hce & _).
pose proof (ssw_ok_sp B c HOK) as (Hsp16 & Hsp0 & Hlo & Hhi & Ho16 & ESS).
pose proof (ssw_ok_cp B MT c HRT HOK) as (Hc0 & Hc47 & Hcoff & _).
assert (HL0 : length (cx_C c) = 32%nat)
  by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL0 & _); exact HL0).
assert (HLB : length (cx_Bw c) = Z.to_nat TW.W_LEN)
  by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htw0 & _); exact (tw_len _ _ _ Htw0)).
assert (HNG : forall x, cx_cp c <= x < cx_cp c + 32 -> ~ inG G x)
  by (intros x Hx; destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNG & _);
      exact (proj1 (HNG x ltac:(unfold SSUBMIT_CMD_LEN; lia)))).
assert (Hgp : YK11.getr (cx_regs c) 3 = w64 (as_gp B)) by (destruct HOK as (_ & _ & _ & H3 & _); exact H3).
assert (Htp : YK11.getr (cx_regs c) 4 = w64 (as_tp B)) by (destruct HOK as (_ & _ & _ & _ & H4 & _); exact H4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EST : ESTACK = 4096) by reflexivity.
assert (EC : TA_g_s = 6158784) by reflexivity.
assert (Rq : 0 <= ssw_q c < 2 ^ 32) by (unfold ssw_q; exact (TWL.u_at_range _ _ 4)).
assert (Rkey : 0 <= ssw_key c < 2 ^ 32) by (unfold ssw_key, TS0.cmd_key_of; exact (TWL.u_at_range _ _ 4)).
assert (Rk : 0 <= TW.S_queue_key (cx_Bw c) j < 2 ^ 32) by (unfold TW.S_queue_key; exact (TWL.u_at_range _ _ 4)).
assert (Rco : 0 <= TW.S_stats_coalesced (cx_Bw c) < 2 ^ 64)
  by (unfold TW.S_stats_coalesced; exact (TWL.u_at_range _ _ 8)).
(* the model: entry j is below 512, then the match test *)
replace (Z.to_nat (ssw_q c - j)) with (S (Z.to_nat (ssw_q c - j - 1))) in HM by lia.
rewrite SSK.ssk_find_S in HM.
destruct (512 <=? j) eqn:E512; [discriminate HM|]. apply Z.leb_gt in E512. rename E512 into Hj512.
destruct (loop_entry B MT c j lyX SX WX regs' m md HRT HOK HCUR HRG G10 G11 G13 Hj Hj512) as [HS SHOK].
destruct HCUR as (HJ & Hfr & Hperm & Hmo & HL & HSV).
pose proof HRG as (G2 & G3 & G4 & G8 & G9 & G12 & G18 & G19 & G20).
set (E0 := loop_E c j regs') in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, loop_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs' r)
  by (intros n r Hn; unfold E0, loop_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EXT : forall i, (i < 8)%nat -> ew E0 (32 + i) = nth i (loop_extra c j) (Z_to_bv 64 0))
  by (intros i Hi; unfold E0, loop_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
pose proof (EXT 4%nat ltac:(lia)) as E36. pose proof (EXT 5%nat ltac:(lia)) as E37.
pose proof (EXT 6%nat ltac:(lia)) as E38. pose proof (EXT 7%nat ltac:(lia)) as E39.
cbn [Nat.add nth loop_extra] in E32, E33, E34, E35, E36, E37, E38, E39. clear EXT.
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite G2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite G3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite G4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite G8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite G9 in E9.
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite G10 in E10.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite G13 in E13.
pose proof (EE 14%nat 14%bv eq_refl) as E14. rewrite G14 in E14.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS G HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS G HGX 0 []) as RUNTO.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + SSW_LOOP)) m (YK11.seg_rom segs)) md) Q) end.
(* +0x164 .. +0x178: the key's check, a5 = s->queue[j].key, `beq a5, a4` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ssw_awr_ro. }
ssw_after_ro B MT c HRT HOK HL HSV.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* a match: the memcpy into entry j, coalesced + 1 *)
  ssw_low HS E0 HEX.
  rewrite (SSK.ssk_br_key _ 33 14 (TW.S_queue_key (cx_Bw c) j) (ssw_key c)
    ltac:(first [exact E33 | rewrite HEX by lia; exact E33]) ltac:(first [exact E14 | rewrite HEX by lia; exact E14])
    Rk Rkey) in Hc.
  rewrite Hc in HM. destruct (SSK.ssk_k_some _ _ _ _ _ HM) as [HBw' Hr].
  (* +0x1a4 .. +0x1ac: a2 = 32, a1 = c, `jal __asan_memcpy` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ssw_awr_ro. }
  ssw_after_ro B MT c HRT HOK HL HSV.
  ssw_low HS E0 HEX1.
  pmkst HS.
  ssw_reg HS (Z_to_bv 5 10) (w64 (TA_g_s + 1760 + 32 * j)) Q10
    ltac:(apply ssw_soff0; first [exact E10 | rewrite HEX1 by lia; exact E10]).
  ssw_reg HS (Z_to_bv 5 11) (w64 (cx_cp c)) Q11
    ltac:(apply ssw_soff0; first [exact E8 | rewrite HEX1 by lia; exact E8]).
  ssw_reg HS (Z_to_bv 5 12) (w64 32) Q12 ltac:(reflexivity).
  ssw_reg HS (Z_to_bv 5 2) (w64 (ssw_SP c - 48)) Q2
    ltac:(apply ssw_soff0; first [exact E2 | rewrite HEX1 by lia; exact E2]).
  ssw_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + SSW_RET_CC)) R1
    ltac:(apply codeptr_val; lazymatch goal with H : img_env _ _ ?Ex |- img_env _ _ ?Ex => exact H end).
  ssw_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) R3
    ltac:(apply ssw_soff0; first [exact E3 | rewrite HEX1 by lia; exact E3]).
  ssw_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) R4
    ltac:(apply ssw_soff0; first [exact E4 | rewrite HEX1 by lia; exact E4]).
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
  pose proof HL as (_ & _ & HRD & _).
  pose proof HRD as (Hvis & Hra_c & Hhull_c & Hamr_c & Hc0' & Hc63).
  lazymatch type of Q2 with YK11.getr ?rg _ = _ =>
    assert (Hsp1 : spZ rg = ssw_SP c - 48)
      by (change (bv_unsigned (YK11.getr rg (Z_to_bv 5 2)) = ssw_SP c - 48); rewrite Q2; apply unsigned_lit_small; lia)
  end.
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy (transport_sigma TS___asan_memcpy)
      (HAI0 fx) G WX _ _ (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
      (cx_own c) lyX SX _ (cx_k c) (TA_g_s + 1760 + 32 * j) (cx_cp c) 32 (ssw_SP c - 48 - cx_sp0 c)
      (Z_to_bv 64 (BASE + SSW_RET_CC)) HGX G_HARNESS_rw HJ Q10 Q11 Q12).
    - lia.
    - lia.
    - lia.
    - rewrite Hsp1. lia.
    - exact Ho16.
    - lia.
    - lia.
    - exact R3.
    - exact R4.
    - exact R1.
    - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold SSW_RET_CC, AF_diginet_session_submit; lia | reflexivity].
    - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply ssw_gs_inG.
      unfold TW.SZ_g_s. lia.
    - left. unfold kLowMemEnd. lia.
    - exact (proj1 (ssw_entry_ra B _ _ _ _ _ j HSC HAR1 ltac:(lia))).
    - intros _. exact (proj2 (ssw_entry_ra B _ _ _ _ _ j HSC HAR1 ltac:(lia))).
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [exact (Hvis a Ha)|]. rewrite Hsp1. lia. }
      split.
      { destruct (Z_le_gt_dec (TA_g_s + 1760 + 32 * j + 32) (cx_cp c)) as [H1|H1]; [left; exact H1|].
        destruct (Z_le_gt_dec (cx_cp c + 32) (TA_g_s + 1760 + 32 * j)) as [H2|H2]; [right; exact H2|].
        exfalso. apply (HNG (Z.max (cx_cp c) (TA_g_s + 1760 + 32 * j))); [lia|].
        apply ssw_gs_inG. unfold TW.SZ_g_s. lia. }
      split; [exact Hamr_c|]. split; [exact Hra_c | intros _; exact Hhull_c]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hcpy & Heff & Hgr2).
  lazymatch type of HL with ssw_lite _ _ _ ?mm _ =>
    pose proof (ssw_lite_cpy B MT c WX mm mem2 _ j HRT HOK HL ltac:(lia) Hcpy
      (fun a Ha H1 H2 => Heff a Ha H1 ltac:(lia)) Hgr2) as HL2;
    assert (HSV2 : ssw_saved c WX mem2)
      by (apply (ssw_saved_xfer c WX WX mm mem2); [intros a Ha; apply Heff; lia | exact HSV])
  end.
  clear HL HSV.
  (* the frame kept by the call *)
  jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H WX) mem2) HP2 [1%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    apply (region_kept_aview _ _ _ _ 2%nat (ssw_SP c - 48)); [| | exact Hgr2].
    - apply ssw_U; [first [exact E2 | rewrite HEX1 by lia; exact E2] | lia].
    - intros a Ha. apply Heff; lia. }
  specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Ex ?kk ?ws) _ _ =>
    lazymatch goal with H : img_env _ _ Ex |- _ =>
      assert (HEIc : img_env VAL A_LIM (havoc Ex kk ws)) by (apply img_env_havoc_hi; [exact H | cbv; lia]) end end.
  ssw_low HS E0 HEX3.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  (* g_s.stats.coalesced added, writable *)
  lazymatch type of HS with st_ok_pi _ _ ?E1 ?s ?msx =>
    assert (HSg : st_ok_pi segs VAL E1 (mkSS (ss_pc s) (ss_regs s) (loop_gc :: ss_mem s) (ss_resv s) (ss_facts s)) msx)
  end.
  { apply (st_ok_pi_add_region (PI := PI_transport) _ _ _ loop_gc HS); [vm_compute; reflexivity | |].
    - cbn [ms_mem restrict]. unfold loop_gc, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (ssw_base _ 9 TA_g_s) by (first [rewrite HEX3 by lia; exact E9 | rewrite EC; lia]).
      split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (gx_rw_writable segs G _ G_HARNESS_rw). apply ssw_gs_inG. unfold TW.SZ_g_s. lia. }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs _ _ TA_g_s 18248 8 (SOff 34 0) (TW.S_stats_coalesced (cx_Bw c)));
        [apply ssw_soff0; rewrite HEX3 by lia; exact E34 | exact Rco | lia |].
      destruct HL2 as (_ & _ & _ & Htw2).
      pose proof (tw_read_val segs _ TMAP_A _ TW.OFF_g_s TA_g_s TW.SZ_g_s 18248 8 TMAP_A_ok Htw2 TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as V.
      replace (TW.OFF_g_s + (1760 + 32 * j)) with (TW.A_S_queue_bytes j) in V by (unfold TW.A_S_queue_bytes; lia).
      replace (TW.OFF_g_s + 18248) with TW.A_S_stats_coalesced in V by (unfold TW.A_S_stats_coalesced; lia).
      rewrite (SSK.ssk_coal_read (cx_Bw c) (cx_C c) j HLB HL0 ltac:(lia)) in V. exact V.
    - cbn [ss_mem all_disjoint]. unfold extent_disjoint, loop_gc. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (ssw_base _ 9 TA_g_s) by (first [rewrite HEX3 by lia; exact E9 | rewrite EC; lia]).
      rewrite (ssw_base _ 2 (ssw_SP c - 48)) by (first [rewrite HEX3 by lia; exact E2 | lia]).
      split; [lia | exact I]. }
  clear HS. rename HSg into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
    assert (SHOK1 : sh_ok segs SSW_Bx LOOP_SH E1 (mrestrict (w_H WX) mem2))
      by (apply (loop_shok B _ _ _ _ _ _ j HSC HAR2 ltac:(lia));
          [rewrite HEX3 by lia; exact E9 | rewrite HEX3 by lia; exact E10 | rewrite HEX3 by lia; exact E32]) end.
  clear SHOK.
  (* +0x1b0 .. +0x1d0 and the epilogue: coalesced's check, + 1, the store, `ret` *)
  paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons_g.
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha.
      rewrite (ssw_base _ 9 TA_g_s) in Ha by (first [rewrite HEX3 by lia; exact E9 | rewrite EC; lia]).
      apply ssw_gs_inG. unfold TW.SZ_g_s. lia.
    - ssw_awr_ro. }
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    set (mdF := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdF; clear mt end.
  ssw_low HS E0 HEXF.
  assert (HWR : forall a, TA_g_s + 18248 <= a < TA_g_s + 18248 + Z.of_nat 8 -> ssubmit_wr a)
    by (intros a Ha; right; left; unfold twa_fld, TW.A_S_stats_coalesced; lia).
  lazymatch goal with HFr : frame_of _ _ (mrestrict (w_H WX) ?m1) (mrestrict (w_H WX) ?m2), HG : mem_grows _ _ |- _ =>
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_g_s + 18248 <= a < TA_g_s + 18248 + Z.of_nat 8) ->
      aview segs (w_H WX) m2 a = aview segs (w_H WX) m1 a)
      by (intros a Ha Hn;
          apply (kept_of_frame _ _ _ _ _ (fun x => TA_g_s + 18248 <= x < TA_g_s + 18248 + Z.of_nat 8) HFr);
          [ intros b wlo whi x Hin Hx; ssw_win Hin Hx ltac:(first [lia |
              rewrite ?HEX3 in Hx by lia; rewrite E9 in Hx; unfold w64 in Hx;
              rewrite unsigned_lit_small in Hx by (rewrite EC; lia); cbv beta; lia]) | exact Ha | exact Hn ]);
    pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 0 _ HS eq_refl) as RGC;
    cbn [ms_mem restrict] in RGC;
    pose proof (field_of_region_any _ _ 9%nat TA_g_s _ _ _ _ _ 18248 8 (SOff 34 1) RGC
      ltac:(apply ssw_U; [rewrite HEXF by lia; exact E9 | rewrite EC; lia])
      ltac:(cbn; tauto) ltac:(lia)) as VQ;
    rewrite (ssw_soffk _ 34 1 (TW.S_stats_coalesced (cx_Bw c))) in VQ by (first [rewrite HEXF by lia; exact E34 | lia]);
    change (N.to_nat 8) with 8%nat in VQ;
    pose proof (ssw_lite_store B MT c WX m1 m2 _ 18248 8 (TW.S_stats_coalesced (cx_Bw c) + 1) HRT HOK HL2 ltac:(lia)
      ltac:(unfold TW.SZ_g_s; lia) HWR (fun a Ha _ H2 => KW a Ha H2) (fun a Ha => apresent_grows _ _ _ a HG Ha)
      (fun i Hi => eq_trans (ssw_vm_aview (w_H WX) m2 _ 8 _ i VQ Hi) (f_equal Some (ssw_le8' _ i)))) as HL3;
    clear RGC VQ
  end.
  lazymatch goal with HF : frame_of _ _ _ _, HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ => clear HF HFr HG end.
  eapply (RET WX _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. left.
  apply (ssw_close B MT c lyX SX WX _ _ _ HRT HOK HJ2 Hfr Hperm Hmo (proj1 HL3)).
  + ssw_aregs_tac HS B c regs' 35%nat HRG Hsp HEXF EE E35 E36 E37 E38 Hgp Htp.
  + ssw_rv_open HS. apply ssw_soff0. first [exact E39 | rewrite HEXF by lia; exact E39].
  + ssw_rv_open HS. rewrite Hr. apply bv_eq. reflexivity.
  + destruct HL3 as (_ & _ & _ & Htw3). rewrite HBw'.
    rewrite <- SSK.ssk_put_coal. rewrite (SSK.ssk_coal_read (cx_Bw c) (cx_C c) j HLB HL0 ltac:(lia)).
    replace (TW.A_S_queue_bytes j) with (TW.OFF_g_s + (1760 + 32 * j)) by (unfold TW.A_S_queue_bytes; lia).
    replace TW.A_S_stats_coalesced with (TW.OFF_g_s + 18248) by (unfold TW.A_S_stats_coalesced; lia).
    exact Htw3.
- (* no match: the next entry *)
  ssw_low HS E0 HEX.
  rewrite (SSK.ssk_br_key _ 33 14 (TW.S_queue_key (cx_Bw c) j) (ssw_key c)
    ltac:(first [exact E33 | rewrite HEX by lia; exact E33]) ltac:(first [exact E14 | rewrite HEX by lia; exact E14])
    Rk Rkey) in Hc.
  rewrite Hc in HM. clear Hc.
  (* +0x17c .. +0x188: a0 += 32, a3 -= 1, a1 += 32, `beq a3, 0` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ssw_awr_ro. }
  ssw_after_ro B MT c HRT HOK HL HSV.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* the last entry: the append *)
    ssw_low HS E0 HEX2.
    lazymatch type of Hc with context [sv_denot ?Ex (SOff 13 (-1))] =>
      rewrite (ssw_br_a3 Ex (ssw_q c - j) ltac:(first [exact E13 | rewrite HEX2 by lia; exact E13]) ltac:(lia)) in Hc end.
    apply Z.eqb_eq in Hc.
    replace (Z.to_nat (ssw_q c - j - 1)) with O in HM by lia. cbn [TS0.submit_find_m] in HM.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SSW_APP.
    { ssw_awr_ro. }
    ssw_after_ro B MT c HRT HOK HL HSV.
    ssw_low HS E0 HEX4.
    pmkst HS.
    eapply SRr_mono; [| intros W' c' _ HQ; left; exact HQ].
    apply (HAPP c lyX SX WX _ _ _ HRT HOK).
    * exact (conj HJ (conj Hfr (conj Hperm (conj Hmo (conj HL HSV))))).
    * ssw_rg_cut HS HEX4 EE E2 E3 E4 E8 E9 E32 G20.
    * exact HM.
  + (* back to the head at j + 1 *)
    ssw_low HS E0 HEX2.
    lazymatch type of Hc with context [sv_denot ?Ex (SOff 13 (-1))] =>
      rewrite (ssw_br_a3 Ex (ssw_q c - j) ltac:(first [exact E13 | rewrite HEX2 by lia; exact E13]) ltac:(lia)) in Hc end.
    apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan SSW_LOOP.
    { ssw_awr_ro. }
    ssw_after_ro B MT c HRT HOK HL HSV.
    ssw_low HS E0 HEX4.
    pmkst HS.
    apply SRr_ret. right. exists (j + 1). split; [lia|].
    do 5 eexists. split; [reflexivity|].
    split; [exact (conj HJ (conj Hfr (conj Hperm (conj Hmo (conj HL HSV))))) |].
    split; [ssw_rg_cut HS HEX4 EE E2 E3 E4 E8 E9 E32 G20 |].
    split.
    { ssw_rv_open HS. rewrite (ssw_soffk _ 10 32 (TA_g_s + 1760 + 32 * j)) by (first [exact E10 | rewrite HEX4 by lia; exact E10 | lia]).
      unfold w64. f_equal. lia. }
    split.
    { ssw_rv_open HS. rewrite (ssw_soffk _ 10 60 (TA_g_s + 1760 + 32 * j)) by (first [exact E10 | rewrite HEX4 by lia; exact E10 | lia]).
      unfold w64. f_equal. lia. }
    split.
    { ssw_rv_open HS. rewrite (ssw_soffk _ 13 (-1) (ssw_q c - j)) by (first [exact E13 | rewrite HEX4 by lia; exact E13 | lia]).
      unfold w64. f_equal. lia. }
    split.
    { ssw_rv_open HS. apply ssw_soff0. first [exact E14 | rewrite HEX4 by lia; exact E14]. }
    split; [lia|].
    replace (ssw_q c - (j + 1)) with (ssw_q c - j - 1) by lia. exact HM.
Qed.

(* The search from the head: SRr_loopZ over the measure queued - j. *)
Lemma ssw_seg_loop : (forall c, @ssw_app_cut fx rc B MT c) -> forall c, @ssw_loop_cut fx rc B MT c.
Proof.
  intros HAPP c HRT HOK j WX cf Hat.
  exact (SRr_loopZ segs Z (fun j => ssw_q c - j) (fun j => @ssw_loop_at fx rc B MT c j) (ssw_post B MT c)
    (loop_turn HAPP c HRT HOK) j WX cf Hat).
Qed.

End loopw.
