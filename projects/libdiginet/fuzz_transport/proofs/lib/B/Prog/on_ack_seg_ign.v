(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 369 of its 416 lines of code are new or changed and 1877 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlRel.v, with its module names changed; 750 of its 827 lines of code are new or changed and 339 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlSend.v, with its module paths, module names and numbers changed; 227 of its 313 lines of code are new or changed and 741 lines of the source are left out. *)
(* on_ack_seg_ign: Lemma onack_ign_piece : onack_ign_stmt (lib/B/Prog/on_ack_segs.v), the ignored path of on_ack's
   image-B walk, offsets +0x2c0 .. +0x2e4 of the listing lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan
   0x8884c .. 0x88870), then the release cut +0x2e8, which the onack_rel_at it is given closes. Image B's twin of
   lib/A/Prog/on_ack_seg_ign.v (the same ten instructions at other offsets, image B's g_s base).

   What the code does (:226-227). +0x2c0 `lui a0, 4`, +0x2c4 `addiw a0, a0, 0x708`, +0x2c8 `add a0, s3, a0`:
   a0 = s + 18184, g_s.stats.rx_ignored; +0x2cc `srli a1, a0, 3`, +0x2d0 `add a1, a1, s9`, +0x2d4 `lbu a1, 0(a1)`:
   the shadow byte of the 8-byte access; +0x2d8 `bnez a1, +0x4ac`: not taken, the shadow byte is 0 (g_s's payload
   lies in the record's zero shadow, on_ack_cg.v trans_onack_cells, read by DgnTransportBCg.v decode_zshadow_rd);
   +0x2dc `ld a1, 0(a0)`, +0x2e0 `addi a1, a1, 1`, +0x2e4 `sd a1, 0(a0)`: the 8-byte read-modify-write. The next
   instruction is the release cut.

   One run of the token engine over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_to_x, stopped at
   ONACK_REL). The symbolic state: the registers at +0x2c0 as atoms 0 .. 31, atom 32 the shadow base, atom 33 the 8
   bytes at s + 18184 (S_stats_rx_ignored Bw, by the world relation at the cut: TWorldG.v tw_read_val); one region over
   s3 (atom 19) covering [s + 18184, s + 18192), read and written; the shadow entry of that range. The bytes the run
   writes are bytes of G (W_journalG.v awr_ok_x_cons_g).

   At the release cut: the stored bytes are u64 (S_stats_rx_ignored Bw + 1), so the world relation holds at
   onack_wign Bw (TWorldG.v tw_write), the model's world on this path (on_ack_segs.v onack_model_ign); g_fail_next lies
   outside the stored field (oig_fail_next). onack_cur is carried to the run's memory: the run changed only
   [s + 18184, s + 18192), bytes of G in onack_wr Bw b, so the cut's acall_kept_g goes over the run by
   on_ack_seg_kit.v oak_dk_kept_step_gw; the 13 saved words (in the stack, above alloc_ceiling) and the frame's last
   word (in the frame, not in the image) are unchanged. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import maybe_online_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_seg_kit on_ack_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x2c0                                     *)
(* ------------------------------------------------------------------ *)

(* The 8 bytes of g_s.stats.rx_ignored at s + 18184 (s3, atom 19), read (atom 33) and written. *)
Definition oig_rg : YP09.region :=
  YP09.mkRegion (Some 19%nat) 18184 18192 18184 18192 [YP09.mkChunk 18184 (YP09.CVal 8 (SOff 33 0))].
(* s3 = s and s9 = the shadow base. *)
Definition oig_facts : facts :=
  mkFacts [(19%nat, mkAF ONACK_S ONACK_S 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_oig : sstate := mkSS ONACK_IGN sr_atoms [oig_rg] None oig_facts.
(* The shadow entry of the run's one check ([s + 18184, s + 18192)), and the shadow base s9. *)
Definition OIG_SH : list shent := [mkSHE 19 18184 18192].
Definition OIG_Bx : sv := SOff 25 0.

(* ------------------------------------------------------------------ *)
(* 2. The model's world after the store                                *)
(* ------------------------------------------------------------------ *)

(* onack_wign at the numeral offset of the field (OFF_g_s + 18152 + 32). *)
Lemma oig_wign_eq : forall Bw, onack_wign Bw =
  TW.upd Bw (TW.OFF_g_s + 18184) (TW.put 8 (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8 + 1))).
Proof.
intros Bw. unfold onack_wign, TW.set_S_stats_rx_ignored, TW.S_stats_rx_ignored.
replace TW.A_S_stats_rx_ignored with (TW.OFF_g_s + 18184) by reflexivity. reflexivity.
Qed.

(* The store keeps g_fail_next (world offset 0xfdc8, outside [OFF_g_s + 18184, + 8)). *)
Lemma oig_fail_next : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.g_fail_next (onack_wign Bw) = TW.g_fail_next Bw.
Proof.
intros Bw HL. rewrite oig_wign_eq. unfold TW.g_fail_next.
apply TWL.u_at_upd_out; [unfold TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia | |].
- right. rewrite TWL.length_put. unfold TW.OFF_g_s, TW.OFF_g_fail_next. lia.
- rewrite TWL.length_put, HL. unfold TW.OFF_g_s, TW.W_LEN. lia.
Qed.

(* A 64-bit literal is the literal of its wrap. *)
Lemma oig_bv_u64 : forall x, Z_to_bv 64 x = Z_to_bv 64 (TS0.u64 x).
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, TS0.u64.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia; reflexivity.
Qed.

(* The register and region readers of a symbolic state, as lib/A/Prog/DgnTransportBPaLib.v states them. *)
Ltac oig_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register the run does not write, at the run's end, from the equation Q of its value at the run's start: the
   run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac oig_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    oig_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac oig_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac oig_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac oig_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.

Section ig. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* g_s's payload bytes are bytes of G. *)
Lemma oig_inG : forall a, ONACK_S <= a < ONACK_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONACK_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* g_s's bytes [s + 18184, s + 18192) are addressable at every AR state: a whole granule of the record's zero
   shadow. *)
Lemma oig_ra : forall ly S (W : world segs) mem md,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONACK_S + 18184) 8.
Proof.
intros ly S W mem md HZ HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONACK_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONACK_S + TW.SZ_g_s)
  by (unfold ONACK_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's valuation: the 32 registers at +0x2c0, the shadow base (atom 32) and the 8 bytes of
   g_s.stats.rx_ignored (atom 33). *)
Definition oig_E (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8)]).

(* The symbolic state at +0x2c0 holds of the machine state there, and the run's shadow entry holds. *)
Lemma oig_entry : forall ly S (W : world segs) regs mem md Bw,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 ONACK_S -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (oig_E regs Bw) ss_oig
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONACK_IGN)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OIG_Bx OIG_SH (oig_E regs Bw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HSC HAR Htw R19 R25.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oig_E regs Bw) n = YK11.getr regs r)
  by (intros n r Hn; unfold oig_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew (oig_E regs Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8))
  by (unfold oig_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (U19 : bv_unsigned (ew (oig_E regs Bw) 19) = ONACK_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (oig_E regs Bw) 25) = SHADOW_OFF)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 18184) 8 < 2 ^ 64) by exact (TWL.u_at_range Bw _ 8).
assert (U33 : bv_unsigned (ew (oig_E regs Bw) 33) = TW.u_at Bw (TW.OFF_g_s + 18184) 8)
  by (rewrite E33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_oig.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold oig_rg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONACK_S + o) G_HARNESS_B_rw).
      apply oig_inG. unfold TW.SZ_g_s. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs _ _ ONACK_S 18184 8 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 18184) 8));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 18184 8 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold oig_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold oig_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U25.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (oig_ra ly S W mem md HSC HAR) as HRA.
  assert (UB : U (oig_E regs Bw) OIG_Bx = SHADOW_OFF).
  { unfold U, OIG_Bx. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, OIG_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ OIG_Bx 19 (ONACK_S + 18184) 8 ONACK_S 18184 18192 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma oig_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma oig_holds : @onack_ign_stmt fx rc B MT.
Proof.
unfold onack_ign_stmt, onack_ign_at.
intros REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & HSC & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & _ & HGX & _).
pose proof HFIX as (HJe & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _ & _ & Hfn & Hm & _ & _ & _ & _ & _ & _ & HFa &
  HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL) & _ & _ & Htw2 & Hig).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (CS' : ONACK_S = TB_g_s) by reflexivity.
unfold ONACK_FBYTES in HFc, HFapp, HFL.
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJe as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4240 <= ONACK_STK).
{ unfold ONACK_STK, ONACK_FRAME, ONACK_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hsp : alloc_ceiling <= spZ regs - 104 /\ spZ regs <= 2 ^ 47) by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin2 : In (ONACK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof (onack_model_ign _ _ _ _ _ Hig Hm) as EBw'.
pose proof (onack_wlen _ _ Htw2) as HWL.
(* +0x2c0 .. +0x2e4: the check of s + 18184, the load, + 1, the store; the run stops at the release cut. *)
destruct (oig_entry lyc S2 W regs2 mem2 md2 Bw HSC HAR2 Htw2 R19 R25) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (oig_E regs2 Bw)) by (unfold oig_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oig_E regs2 Bw) n = YK11.getr regs2 r)
  by (intros n r Hn; unfold oig_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U19c : bv_unsigned (ew (oig_E regs2 Bw) 19) = ONACK_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (E33 : ew (oig_E regs2 Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8))
  by (unfold oig_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 18184) 8 < 2 ^ 64) by exact (TWL.u_at_range Bw _ 8).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ONACK_REL.
{ oig_awr_rs.
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19c in Ha;
    apply oig_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msF end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew (oig_E regs2 Bw) n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
(* the registers the release reads, at the cut *)
oig_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. oig_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
oig_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. oig_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
oig_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. oig_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
oig_kreg HS E5lo EE (23%bv : bv 5) 23%nat R23 X23. oig_kreg HS E5lo EE (24%bv : bv 5) 24%nat R24 X24.
(* the run wrote [s + 18184, s + 18192) only *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (ONACK_S + 18184 <= a < ONACK_S + 18192) ->
  aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => ONACK_S + 18184 <= x < ONACK_S + 18192) HFr1);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U19c in Hx; lia |]).
  destruct Hin. }
assert (GR : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msF) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG1 Ha)).
(* the stored bytes: u64 (S_stats_rx_ignored Bw + 1) *)
oig_region HS 0%nat HR.
assert (U19f : bv_unsigned (ew E5 19) = ONACK_S) by (rewrite E5lo by lia; exact U19c).
assert (E33f : ew E5 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8)) by (rewrite E5lo by lia; exact E33).
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?e)]) =>
  assert (DEN : sv_denot E5 e = Z_to_bv 64 (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8 + 1)));
  [ cbn [sv_denot]; rewrite E33f, unsigned_lit_small by lia; apply oig_bv_u64
  | pose proof (can_field_of_region E5 _ 19 ONACK_S _ 18184 18192 18184 18192 18184 8%N e
      (TS0.u64 (TW.u_at Bw (TW.OFF_g_s + 18184) 8 + 1)) HR U19f ltac:(oig_in) DEN
      ltac:(unfold TS0.u64; change (8 * Z.of_N 8) with 64; apply Z.mod_pos_bound; lia) ltac:(cbn; lia)) as VB ]
end.
change (N.to_nat 8) with 8%nat in VB.
clear HR DEN.
(* the world relation at the model's world *)
assert (TWn : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) (onack_wign Bw)).
{ rewrite oig_wign_eq.
  apply (tw_write TMAP_B (aview segs (w_H W) mem2) (aview segs (w_H W) (ms_mem msF)) Bw TW.OFF_g_s TB_g_s TW.SZ_g_s
    18184 8 _ TMAP_B_ok Htw2 TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. rewrite <- CS'. exact (oig_aview_of_val _ _ _ 8 _ VB j Hj).
  - intros x Hx Hn.
    assert (Hg : inG TG.G_HARNESS_B x).
    { destruct Hx as (o & b0 & n & Hin & Hb). pose proof (TMAP_B_in_G o b0 n Hin) as HG0.
      unfold inG. apply Exists_exists. exists (b0, n). split; [exact HG0 | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hg) as Hl. unfold kLowMemEnd in Hl.
    apply KF; [lia|]. intros X. apply Hn. lia. }
(* what the call keeps, over the run *)
assert (KG : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem msF) (spZ regs - ONACK_STK) (spZ regs)
  (onack_wr Bw b)).
{ apply (oak_dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W mem2 (ms_mem msF)
    (spZ regs - ONACK_STK) (spZ regs) (onack_wr Bw b) (fun x => ONACK_S + 18184 <= x < ONACK_S + 18192)
    HARc HK KF GR).
  - intros a Hz Hc. cbv beta in Hz. exfalso. lia.
  - intros b0 m i _ _ Hz. cbv beta in Hz. left. unfold twb_fld, TW.A_S_stats_rx_ignored, TW.OFF_g_s. lia.
  - intros a Hz _ HnG _ _. cbv beta in Hz. exfalso. apply HnG. apply oig_inG. unfold TW.SZ_g_s. lia.
  - intros c p a _ _ Hz. cbv beta in Hz. left. unfold twb_fld, TW.A_S_stats_rx_ignored, TW.OFF_g_s. lia. }
(* the thirteen saved words, at the run's memory *)
assert (HSVn : Forall (fun o : Z * Z => rdword (aview segs (w_H W) (ms_mem msF)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONACK_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONACK_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KF; lia. }
(* the frame's last word, at the run's memory *)
assert (HFLn : rdword (aview segs (w_H W) (ms_mem msF)) (F + 256 - 8) = Some (flag_addr lyc ONACK_CID pos)).
{ rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KF; [lia|]. intros X.
  assert (Hg : inG TG.G_HARNESS_B (F + 256 - 8 + i)) by (apply oig_inG; unfold TW.SZ_g_s; lia).
  destruct (HGX _ Hg) as [HiG _].
  apply (frm_img segs B LAWS _ _ _ _ _ ONACK_CID pos (F + 256 - 8 + i) HAR2 Hin2); [|exact HiG].
  rewrite <- HFa, onack_fbytes. unfold ONACK_FBYTES. lia. }
(* the release cut *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_REL)) mm rom) mdx) Q) end.
apply (REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F lyc S2 W
  (ms_mem msF) _ 0 (ms_regs msF) HFIX).
- unfold onack_rel_cur, onack_cur.
  refine (conj (conj HJ (conj He (conj Hfrs (conj Hperm (conj HlyF (conj HMO (conj KG (conj HSVn _))))))))
    (conj _ _)).
  + unfold ONACK_FBYTES. exact HFLn.
  + rewrite EBw'. exact TWn.
  + rewrite EBw', (oig_fail_next Bw HWL). exact Hfn.
- exact (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X23 X24))))))).
Qed.
End ig.

(* The ignored path of the walk of on_ack (on_ack_segs.v onack_ign_stmt), at every machine, run ceiling, record and
   meter. *)
Lemma onack_ign_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onack_ign_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@oig_holds fx rc B MT). Qed.

Print Assumptions onack_ign_piece.
