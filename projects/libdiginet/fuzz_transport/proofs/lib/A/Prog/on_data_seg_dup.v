(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 708 of its 755 lines of code are new or changed and 512 lines of the source are left out. *)
(* on_data_seg_dup: Theorem od_dup : forall fx rc B MT, @od_dup_stmt fx rc B MT (lib/A/Prog/on_data_seg_cut.v),
   the duplicate test of the image-A walk of on_data, offsets +0x228 .. +0x290 of the listing
   lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x88af8 .. 0x88b60).

   What the code does (diginet_session.c:249-251). +0x228 - +0x238 the checked 4-byte load of s + 168
   (S_desk_counter_valid): a0 = s + 168, a3 = its shadow address, the shadow byte is 0 (trans_ondata_cells, the
   shadow entry of the token engine over s11), so `bnez a1` is not taken; +0x23c `lw a4, 0(a0)` and +0x240
   `addi a1, s3, 0xa4` (a1 = s + 164); +0x244 `beqz a4`: S_desk_counter_valid = 0 goes to the not-a-duplicate
   target +0x294 (od_set_at).
   +0x248 - +0x260 the checked 4-byte loads of f + 20 (its shadow byte read through s2, 0 since f's 64 bytes are
   marked usable) and of s + 164, with a4 = the sign extension of fr_send b (`lw a4, 0(s5)`); +0x264 `beqz a2`:
   a2 is fr_retry b, and 0 goes to +0x294. +0x268 `lw a2, 0(a1)` = the sign extension of S_desk_counter and +0x26c
   `bne a4, a2`: different goes to +0x294. Past +0x26c the three tests of ondata_dup (ondata_w2 B1 b r now) b hold.
   +0x270 - +0x28c the checked read-modify-write of stats.rx_duplicates (s + 18168, over s8) and +0x290 `j` to the
   release cut +0x3f8 (od_rel_at), where the world is the model's Bw' (on_data_cg.v ondata_model, read off by
   on_data_seg_cut.v od_some_inv).

   The runs are the token engine's over the caller's G journal (lib/A/Prog/TransportGRunA.v paj_run_x /
   paj_run_to_x); the three tests are branches the engine cannot decide, taken apart by
   lib/A/Prog/DgnTransportPaLib.v paj_branch. Runs 1 to 3 have no writable region, so they leave the view of the
   cut (on_data_seg_midkit.v odm_cur_move); their shared symbolic state odd_ssA reads the 8 bytes of s + 164 and
   s + 168, the shadow byte of f + 20 and the 4 bytes of f + 20. The duplicate path's run is taken from a second
   state odd_ssB whose one region is the 8 bytes of stats.rx_duplicates, bytes of G (W_journalG.v
   awr_ok_x_cons_g); what the call has kept runs over it by odm_kept_step and the world moves by TWorldG.v
   tw_write. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x AE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_data_cg on_data_seg_cut on_data_seg_midkit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas TOpsKeep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require on_data.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module POD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.on_data.
Module TOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The two symbolic states                                           *)
(* ------------------------------------------------------------------ *)

Definition ODD_P4 : Z := AF_on_data + 0x270.
Definition odd_SH13 : Z := SHADOW_OFF + (ONDATA_S + 168) / 8.

Definition odd_rg_dc : YP09.region :=
  YP09.mkRegion (Some 19%nat) 164 172 0 0
    [YP09.mkChunk 164 (CVal 4 (SOff 34 0)); YP09.mkChunk 168 (CVal 4 (SOff 35 0))].
Definition odd_rg_sh18 : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition odd_rg_f20 : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition odd_factsA : facts :=
  mkFacts [(18%nat, mkAF SHADOW_OFF (2 ^ 47 - 64) 0); (19%nat, mkAF ONDATA_S ONDATA_S 6);
           (21%nat, mkAF 4096 (2 ^ 47 - 64) 2); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition odd_SHA : list shent := [mkSHE 19 0 200].
Definition odd_Bx : sv := SOff 27 0.
Definition odd_ssA : sstate := mkSS OD_DUP sr_atoms [odd_rg_dc; odd_rg_sh18; odd_rg_f20] None odd_factsA.

Definition odd_rg_dup : YP09.region :=
  YP09.mkRegion (Some 24%nat) 8 16 8 16 [YP09.mkChunk 8 (CVal 8 (SOff 36 0))].
Definition odd_factsB : facts :=
  mkFacts [(24%nat, mkAF (ONDATA_S + 18160) (ONDATA_S + 18160) 4);
           (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition odd_SHB : list shent := [mkSHE 24 0 56].
Definition odd_ssB : sstate := mkSS ODD_P4 sr_atoms [odd_rg_dup] None odd_factsB.

(* The world after the duplicate store. *)
Lemma odd_tw : forall (rd rd' : Z -> option Z) Bx,
  tw_at TMAP_A rd Bx ->
  (forall j, (j < 8)%nat -> rd' (ONDATA_S + 18168 + Z.of_nat j) =
     Some (YO0f.le_byte (TS0.u64 (TW.S_stats_rx_duplicates Bx + 1)) 8 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (ONDATA_S + 18168 <= x < ONDATA_S + 18176) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (TW.set_S_stats_rx_duplicates Bx (TS0.u64 (TW.S_stats_rx_duplicates Bx + 1))).
Proof.
intros rd rd' Bx Hat H1 HO.
assert (CS : ONDATA_S = TA_g_s) by reflexivity.
unfold TW.set_S_stats_rx_duplicates, TW.A_S_stats_rx_duplicates.
replace (TW.OFF_g_s + 18152 + 16) with (TW.OFF_g_s + 18168) by lia.
apply (tw_write TMAP_A rd rd' Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 18168 8
  (TS0.u64 (TW.S_stats_rx_duplicates Bx + 1)) TMAP_A_ok Hat TMAP_A_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS. exact (H1 j Hj).
- intros x Hx Hn. rewrite <- CS in Hn. apply HO; [exact Hx | cbn in Hn; lia].
Qed.

Ltac odd_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac odd_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* the register r of the machine state HS describes, when the run kept it *)
Ltac odd_keep HS EEq n r R :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _);
      lazymatch goal with |- sv_denot ?E0 ?ee = ?v =>
        let e' := eval vm_compute in ee in change (sv_denot E0 e' = v) end;
      cbn [sv_denot]; rewrite (EEq n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R
  end.
(* a register the run set to s + off *)
Ltac odd_off HS EEq R19 r :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _);
      lazymatch goal with |- sv_denot ?E0 ?ee = ?v =>
        let e' := eval vm_compute in ee in change (sv_denot E0 e' = v) end;
      cbn [sv_denot]; rewrite (EEq 19%nat (19%bv : bv 5) eq_refl), R19; unfold w64;
      rewrite (unsigned_lit_small ONDATA_S) by (unfold ONDATA_S, TA_g_s; lia); reflexivity
  end.
(* a3, the shadow address of s + 168 *)
Ltac odd_sh HS EEq R19 R27 :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx (13%bv : bv 5) HS) _);
      lazymatch goal with |- sv_denot ?E0 ?ee = ?v =>
        let e' := eval vm_compute in ee in change (sv_denot E0 e' = v) end;
      cbn [sv_denot]; rewrite (EEq 19%nat (19%bv : bv 5) eq_refl), (EEq 27%nat (27%bv : bv 5) eq_refl), R19, R27;
      unfold w64, ONDATA_S, TA_g_s, SHADOW_OFF; vm_compute; reflexivity
  end.
Ltac odd_regsset HS EEq R2 R3 R4 R8 R9 R25 R26 R18 R19 R20 R21 R27 R22 R17 :=
  unfold od_regs_set, od_regs_s, od_regs_rel; repeat apply conj;
  [ odd_keep HS EEq 2%nat (2%bv : bv 5) R2 | odd_keep HS EEq 3%nat (3%bv : bv 5) R3
  | odd_keep HS EEq 4%nat (4%bv : bv 5) R4 | odd_keep HS EEq 8%nat (8%bv : bv 5) R8
  | odd_keep HS EEq 9%nat (9%bv : bv 5) R9 | odd_keep HS EEq 25%nat (25%bv : bv 5) R25
  | odd_keep HS EEq 26%nat (26%bv : bv 5) R26 | odd_keep HS EEq 18%nat (18%bv : bv 5) R18
  | odd_keep HS EEq 19%nat (19%bv : bv 5) R19 | odd_keep HS EEq 20%nat (20%bv : bv 5) R20
  | odd_keep HS EEq 21%nat (21%bv : bv 5) R21 | odd_keep HS EEq 27%nat (27%bv : bv 5) R27
  | odd_keep HS EEq 22%nat (22%bv : bv 5) R22
  | odd_off HS EEq R19 (10%bv : bv 5) | odd_off HS EEq R19 (11%bv : bv 5)
  | odd_sh HS EEq R19 R27
  | odd_keep HS EEq 17%nat (17%bv : bv 5) R17 ].

Section dup. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition odd_EA (regs2 : bvmap 5 word) (sd dc dv : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs2 [Z_to_bv 64 0; Z_to_bv 64 sd; Z_to_bv 64 dc; Z_to_bv 64 dv]).
Definition odd_EB (regs2 : bvmap 5 word) (du : Z) : env :=
  Eimg (PI := PI_transport)
    (Ereg regs2 [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 du]).

Lemma odd_ewA : forall regs2 sd dc dv n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (odd_EA regs2 sd dc dv) n = YK11.getr regs2 rr.
Proof. intros. unfold odd_EA. apply can_ew_Eimg_Ereg_nat. assumption. Qed.
Lemma odd_ewA33 : forall regs2 sd dc dv, ew (odd_EA regs2 sd dc dv) 33 = Z_to_bv 64 sd.
Proof. intros. unfold odd_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 1). Qed.
Lemma odd_ewA34 : forall regs2 sd dc dv, ew (odd_EA regs2 sd dc dv) 34 = Z_to_bv 64 dc.
Proof. intros. unfold odd_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 2). Qed.
Lemma odd_ewA35 : forall regs2 sd dc dv, ew (odd_EA regs2 sd dc dv) 35 = Z_to_bv 64 dv.
Proof. intros. unfold odd_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 3). Qed.
Lemma odd_envA : forall regs2 sd dc dv, img_env VAL A_LIM (odd_EA regs2 sd dc dv).
Proof. intros. unfold odd_EA. apply Eimg_env. Qed.
Lemma odd_ewB : forall regs2 du n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (odd_EB regs2 du) n = YK11.getr regs2 rr.
Proof. intros. unfold odd_EB. apply can_ew_Eimg_Ereg_nat. assumption. Qed.
Lemma odd_ewB36 : forall regs2 du, ew (odd_EB regs2 du) 36 = Z_to_bv 64 du.
Proof. intros. unfold odd_EB. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 4). Qed.
Lemma odd_envB : forall regs2 du, img_env VAL A_LIM (odd_EB regs2 du).
Proof. intros. unfold odd_EB. apply Eimg_env. Qed.

(* The value a register holds. *)
Lemma odd_off0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia.
rewrite Z.add_0_r. reflexivity.
Qed.

(* The 4-byte signed load of a word. *)
Lemma odd_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The state of runs 1 to 3 holds at the machine state of each of their three pcs. *)
Lemma odd_entryA : forall (W2 : world segs) (regs2 : bvmap 5 word) mem2 (fp sd dc dv : Z),
  YK11.getr regs2 18 = w64 (SHADOW_OFF + (fp + 20) / 8) ->
  YK11.getr regs2 19 = w64 ONDATA_S ->
  YK11.getr regs2 21 = w64 (fp + 20) ->
  YK11.getr regs2 27 = w64 SHADOW_OFF ->
  4096 <= fp -> fp mod 8 = 0 -> fp + 64 <= 2 ^ 47 - 128 ->
  (fp + 64 <= kLowShadowBeg \/ kHighMemBeg <= fp) ->
  (fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp) ->
  0 <= sd < 2 ^ 32 -> 0 <= dc < 2 ^ 32 -> 0 <= dv < 2 ^ 32 ->
  aview segs (w_H W2) mem2 (SHADOW_OFF + (fp + 20) / 8) = Some 0 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (fp + 20) 4 sd ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 164) 4 dc ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 168) 4 dv ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF ONDATA_S 200 ->
  st_ok_pi segs VAL (odd_EA regs2 sd dc dv) odd_ssA
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_DUP)) mem2 (YK11.seg_rom segs))) /\
  sh_ok segs odd_Bx odd_SHA (odd_EA regs2 sd dc dv) (mrestrict (w_H W2) mem2).
Proof.
intros W2 regs2 mem2 fp sd dc dv R18 R19 R21 R27 Hfp4 Hfp8 Hfph HAP HFG Hsd Hdc Hdv HS18 HV20 HVc HVv HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := odd_EA regs2 sd dc dv).
assert (HSH : 0 <= (fp + 20) / 8 /\ (fp + 20) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos; lia|]; apply Z.div_le_upper_bound; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + (fp + 20) / 8)
  by (unfold E; rewrite (odd_ewA regs2 sd dc dv 18%nat (18%bv : bv 5) eq_refl), R18; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U19 : bv_unsigned (ew E 19) = ONDATA_S)
  by (unfold E; rewrite (odd_ewA regs2 sd dc dv 19%nat (19%bv : bv 5) eq_refl), R19; unfold w64;
      apply unsigned_lit_small; unfold ONDATA_S, TA_g_s; lia).
assert (U21 : bv_unsigned (ew E 21) = fp + 20)
  by (unfold E; rewrite (odd_ewA regs2 sd dc dv 21%nat (21%bv : bv 5) eq_refl), R21; unfold w64;
      apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (unfold E; rewrite (odd_ewA regs2 sd dc dv 27%nat (27%bv : bv 5) eq_refl), R27; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = sd)
  by (unfold E; rewrite (odd_ewA33 regs2 sd dc dv); apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = dc)
  by (unfold E; rewrite (odd_ewA34 regs2 sd dc dv); apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = dv)
  by (unfold E; rewrite (odd_ewA35 regs2 sd dc dv); apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold odd_ssA.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [odd_rg_dc odd_rg_sh18 odd_rg_f20
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U19. split; [unfold ONDATA_S, TA_g_s; lia|]. split; [unfold ONDATA_S, TA_g_s; lia|].
      split; [intros o Ho; lia|]. repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val segs E _ ONDATA_S 164 4 (SOff 34 0) dc);
         [cbn [sv_denot]; rewrite U34; unfold w64; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
         exact HVc.
      -- apply (chunk_ok_val segs E _ ONDATA_S 168 4 (SOff 35 0) dv);
         [cbn [sv_denot]; rewrite U35; unfold w64; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
         exact HVv.
    * rewrite U18. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (SHADOW_OFF + (fp + 20) / 8) 0 1 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply odm_val0. exact HS18.
    * rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (fp + 20) 0 4 (SOff 33 0) sd);
        [cbn [sv_denot]; rewrite U33; unfold w64; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact HV20.
  + apply pairwise_disjoint_of_extents.
    unfold odd_rg_dc, odd_rg_sh18, odd_rg_f20, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U18, U19, U21.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold ONDATA_S, TA_g_s, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, TW.SZ_g_s in *.
    repeat split;
      first [ exact I | lia | destruct HAP as [h | h]; lia | destruct HFG as [h | h]; lia ].
  + unfold odd_factsA, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U19, U21, U27.
    change (2 ^ 6) with 64. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (M19 : ONDATA_S mod 64 = 0) by reflexivity.
    assert (M21 : (fp + 20) mod 4 = 0).
    { pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite Hfp8, Z.add_0_r in D.
      replace (fp + 20) with ((2 * (fp / 8) + 5) * 4) by lia. apply Z_mod_mult. }
    repeat match goal with |- _ /\ _ => split end; try exact I;
    unfold ONDATA_S, TA_g_s, SHADOW_OFF in *; first [exact M19 | exact M21 | lia].
- assert (UB : U E odd_Bx = SHADOW_OFF).
  { unfold U, odd_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, odd_SHA. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W2) mem2 E odd_Bx 19 ONDATA_S 200 ONDATA_S 0 200 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small.
    unfold ONDATA_S, TA_g_s; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold ONDATA_S, TA_g_s, SHADOW_OFF in *. lia.
Qed.

(* The state of the duplicate path's run holds at +0x270. *)
Lemma odd_entryB : forall (W2 : world segs) (regs2 : bvmap 5 word) memX (du : Z),
  YK11.getr regs2 24 = w64 (ONDATA_S + 18160) ->
  YK11.getr regs2 27 = w64 SHADOW_OFF ->
  0 <= du < 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W2) memX) (ONDATA_S + 18168) 8 du ->
  range_addressable (aview segs (w_H W2) memX) SHADOW_OFF (ONDATA_S + 18160) 56 ->
  st_ok_pi segs VAL (odd_EB regs2 du) odd_ssB
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ODD_P4)) memX (YK11.seg_rom segs))) /\
  sh_ok segs odd_Bx odd_SHB (odd_EB regs2 du) (mrestrict (w_H W2) memX).
Proof.
intros W2 regs2 memX du R24 R27 Hdu HV HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := odd_EB regs2 du).
assert (U24 : bv_unsigned (ew E 24) = ONDATA_S + 18160)
  by (unfold E; rewrite (odd_ewB regs2 du 24%nat (24%bv : bv 5) eq_refl), R24; unfold w64;
      apply unsigned_lit_small; unfold ONDATA_S, TA_g_s; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (unfold E; rewrite (odd_ewB regs2 du 27%nat (27%bv : bv 5) eq_refl), R27; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U36 : bv_unsigned (ew E 36) = du)
  by (unfold E; rewrite (odd_ewB36 regs2 du); apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold odd_ssB.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [odd_rg_dup YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [unfold ONDATA_S, TA_g_s; lia|]. split; [unfold ONDATA_S, TA_g_s; lia|].
    split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (ONDATA_S + 18160 + o) G_HARNESS_rw).
      apply odm_inG. unfold TW.SZ_g_s. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs E _ (ONDATA_S + 18160) 8 8 (SOff 36 0) du);
        [cbn [sv_denot]; rewrite U36; unfold w64; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      replace (ONDATA_S + 18160 + 8) with (ONDATA_S + 18168) by lia. exact HV.
  + apply pairwise_disjoint_of_extents.
    unfold odd_rg_dup, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold odd_factsB, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24, U27.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (M24 : (ONDATA_S + 18160) mod 16 = 0) by reflexivity.
    repeat match goal with |- _ /\ _ => split end; try exact I;
    unfold ONDATA_S, TA_g_s, SHADOW_OFF in *; first [exact M24 | lia].
- assert (UB : U E odd_Bx = SHADOW_OFF).
  { unfold U, odd_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, odd_SHB. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W2) memX E odd_Bx 24 (ONDATA_S + 18160) 56 (ONDATA_S + 18160) 0 56 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small.
    unfold ONDATA_S, TA_g_s; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold ONDATA_S, TA_g_s, SHADOW_OFF in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

(* a run with no writable region: the journal admits it and it changes no byte *)
Ltac odd_nowin :=
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
Ltac odd_same HFrx :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a;
  lazymatch goal with
  | |- aview _ ?Hh ?m1 _ = aview _ _ ?m2 _ =>
      rewrite (AE2y.aview_mod Hh m1 a), (AE2y.aview_mod Hh m2 a)
  end;
  assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia);
  apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFrx);
  [ let b0 := fresh in let wlo := fresh in let whi := fresh in let x := fresh in
    let Hin := fresh in let Hx := fresh in intros b0 wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]);
    destruct Hin
  | exact Ha
  | let HF0 := fresh in intros HF0; destruct HF0 ].

Lemma odd_dup_at : @od_dup_stmt fx rc B MT.
Proof.
unfold od_dup_stmt, od_dup_at.
intros SET REL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F B1 r f ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HPCS & HCELLS & HSC & HROU & HRNE & HROR & HRNO & LAWS & MTL & MTF & SMP & ASF & FFL & HGX
  & HGNE).
pose proof HFIX as (HPRE & HTFN & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HPRE as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hfn0
  & Hm & HTF & HROM & HAPT & HINV1 & HINV4 & HINV3 & Hcnt & Hev).
pose proof HCUR as (HCUR0 & Hs24 & Hsc & HTW2 & Hgf1).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as ((HRR & R18 & R19 & R20 & R21 & R27) & R22 & R24 & R12 & R17).
pose proof HRR as (R2 & R3 & R4 & R8 & R9 & R25 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDF as (Hcode & Hbuf0 & Hgb & Hsrc & Hdow & HnoG & Hfp0 & Hfp8 & Hfjl & Hgf & Hfake & Hrdok & Hfow).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0a & Hstk1 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4272 <= ONDATA_STK).
{ unfold ONDATA_STK, ONDATA_FRAME, ONDATA_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?bb =>
    pose proof (Z.le_max_l a bb) as Hm2; assert (Ha4 : a = 4096) by reflexivity end.
  lia. }
assert (Hsp1 : spZ regs - 192 < sp1 <= spZ regs - 160).
{ rewrite Esp1. unfold ONDATA_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M. lia. }
assert (Hwin : alloc_ceiling <= spZ regs - ONDATA_STK) by lia.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* f at the cut's memory *)
destruct (odm_f_kept B LAWS lyc Sc W memc mdc W2 mem2 (spZ regs - ONDATA_STK) (spZ regs) Bw b fp
  HARc HGX HK Hfake) as [KF KS].
assert (LB : length (frame_f_bytes buf b fj) = 64%nat).
{ unfold frame_f_bytes, frame_f_cells. rewrite Hcode. cbn [Z.eqb]. rewrite length_map.
  apply LC.cells_bytes_length. cbn [PParse.parse_cells LC.cells_wf LC.cell_wf].
  pose proof (odm_blen b Hcode) as Hb30.
  repeat split;
    first [ unfold DSpec.fr_dst; rewrite length_firstn; lia
          | unfold DSpec.fr_src; rewrite length_firstn, length_skipn; lia
          | rewrite length_firstn, length_skipn, Hfjl; lia
          | rewrite length_skipn, Hfjl; lia
          | exact I ]. }
assert (Hgb2 : YI00.garr8 segs (mrestrict (w_H W2) mem2) fp (frame_f_bytes buf b fj)).
{ intros j Hj. destruct (Hgf j Hj) as [HV HRg]. split; [|exact HRg].
  intros t Ht. rewrite <- (HV t Ht). apply odm_mb_eq. apply KF. rewrite LB in Hj. lia. }
pose proof (odm_f20 (mrestrict (w_H W2) mem2) fp buf b fj Hcode Hfjl Hgb2) as HV20.
pose proof Hrdok as (Hvis & HRAf & Hhull & Hamem & Hfp0' & Hfp63).
assert (HRAf2 : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF fp FRAME_F_SIZE).
{ intros x Hx. destruct (HRAf x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite KS by (unfold FRAME_F_SIZE in Hx; lia). exact Hs. }
unfold FRAME_F_SIZE in HRAf2.
assert (HS18 : aview segs (w_H W2) mem2 (SHADOW_OFF + (fp + 20) / 8) = Some 0)
  by (apply (odm_sh0 _ fp 64 20); [exact Hfp8 | lia | lia | exact HRAf2]).
assert (HRAg : forall q n, ONDATA_S <= q -> q + n <= ONDATA_S + TW.SZ_g_s ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF q n)
  by (intros q n Hq Hn; exact (odm_ra_gs B ly2 S2 W2 mem2 md2 q n HSC HAR2 Hq Hn)).
(* f is apart from g_s and from the shadow band *)
destruct Hfake as (cid0 & pos0 & Hin0 & Hlo0 & Hhi0).
assert (HFNG : forall a, fp <= a < fp + 64 -> ~ (ONDATA_S <= a < ONDATA_S + TW.SZ_g_s)).
{ intros a Ha Hg0. destruct (HGX a (odm_inG a Hg0)) as [Hi _].
  exact (frm_img segs B LAWS lyc Sc W memc mdc cid0 pos0 a HARc Hin0
    ltac:(unfold FRAME_F_SIZE in Hhi0; lia) Hi). }
assert (HFG : fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp).
{ destruct (Z_le_gt_dec (fp + 64) ONDATA_S) as [h | h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONDATA_S + TW.SZ_g_s) fp) as [h2 | h2]; [right; exact h2|].
  exfalso. apply (HFNG (Z.max fp ONDATA_S)); unfold ONDATA_S, TA_g_s, TW.SZ_g_s in *; lia. }
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid0 pos0 HARc Hin0) as (_ & HFapp0 & _ & _).
pose proof (@ASAN_CEIL_range rc) as (HCE & _).
unfold in_app in HFapp0. unfold FRAME_F_SIZE in Hhi0.
assert (HAPf : fp + 64 <= kLowShadowBeg \/ kHighMemBeg <= fp).
{ destruct HFapp0 as (_ & [HL | (HH & _)]); [left | right]; lia. }
assert (Hfph : fp + 64 <= 2 ^ 47 - 128).
{ destruct HFapp0 as (_ & [HL | (HH & HC)]); unfold kLowShadowBeg in *; lia. }
assert (Hfp4 : 4096 <= fp) by (destruct HFapp0 as (H4 & _); lia).
(* the values the three tests read *)
set (Bx := ondata_w2 B1 b r now) in *.
assert (Hsdr : 0 <= DSpec.fr_send b < 2 ^ 32) by apply DSpec.be32_range.
assert (Hrtr : 0 <= DSpec.fr_retry b < 2 ^ 16) by apply DSpec.be16_range.
assert (Hdcr : 0 <= TW.u_at Bx TW.A_S_desk_counter 4 < 2 ^ 32) by exact (TWL.u_at_range Bx _ 4).
assert (Hdvr : 0 <= TW.u_at Bx TW.A_S_desk_counter_valid 4 < 2 ^ 32) by exact (TWL.u_at_range Bx _ 4).
assert (HVc : YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 164) 4
  (TW.u_at Bx TW.A_S_desk_counter 4))
  by (unfold TW.A_S_desk_counter;
      exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 164 4 TMAP_A_ok HTW2 TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia))).
assert (HVv : YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 168) 4
  (TW.u_at Bx TW.A_S_desk_counter_valid 4))
  by (unfold TW.A_S_desk_counter_valid;
      exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 168 4 TMAP_A_ok HTW2 TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia))).
(* what every leaf that reaches the not-a-duplicate target has to show *)
assert (TOSET : forall (memE : word -> option byte) (mdE : Model) (regsE : bvmap 5 word),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONDATA_CID, pos) :: own) ly2 S2 W2 memE mdE (k + e) ->
  (forall a, aview segs (w_H W2) memE a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memE a) ->
  od_regs_set regs regsE fp sp1 F ->
  ondata_dup Bx b = false ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsE (Z_to_bv 64 (BASE + OD_SET)) memE (YK11.seg_rom segs)) mdE)
    (@transport_ondata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b)).
{ intros memE mdE regsE HJE KD GR HRG HND.
  apply (SET LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F B1 r f ly2 S2 W2 memE mdE e regsE HFIX); [|exact HRG].
  refine (conj (conj (odm_cur_move B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F
    ly2 S2 W2 mem2 md2 memE mdE e HCUR0 HJE KD GR) (conj _ (conj Hsc (conj _ Hgf1)))) HND).
  - apply (AF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) memE) (sp1 + 24) F);
    [intros i Hi; apply KD | exact Hs24].
  - apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact HTW2 | intros x _; exact (KD x)]. }
(* ---- run 1: +0x228 .. +0x244 ---- *)
destruct (odd_entryA W2 regs2 mem2 fp (DSpec.fr_send b) (TW.u_at Bx TW.A_S_desk_counter 4)
  (TW.u_at Bx TW.A_S_desk_counter_valid 4) R18 R19 R21 R27 Hfp4 Hfp8 Hfph HAPf HFG Hsdr Hdcr Hdvr HS18 HV20
  HVc HVv ltac:(apply HRAg; [lia | unfold TW.SZ_g_s; lia])) as [HS SHOK].
set (E := odd_EA regs2 (DSpec.fr_send b) (TW.u_at Bx TW.A_S_desk_counter 4)
  (TW.u_at Bx TW.A_S_desk_counter_valid 4)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply odd_envA).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E; apply odd_ewA; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 (DSpec.fr_send b)) by (unfold E; apply odd_ewA33).
assert (E34 : ew E 34 = Z_to_bv 64 (TW.u_at Bx TW.A_S_desk_counter 4)) by (unfold E; apply odd_ewA34).
assert (E35 : ew E 35 = Z_to_bv 64 (TW.u_at Bx TW.A_S_desk_counter_valid 4)) by (unfold E; apply odd_ewA35).
assert (E12 : ew E 12 = w64 (DSpec.fr_retry b)) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl); exact R12).
assert (Hsw1 : - 2 ^ 63 <= bv_swrap 32 (TW.u_at Bx TW.A_S_desk_counter_valid 4) < 2 ^ 63).
{ pose proof (bv_swrap_in_range 32 (TW.u_at Bx TW.A_S_desk_counter_valid 4) ltac:(discriminate)) as Hr.
  change (bv_half_modulus 32) with (2 ^ 31) in Hr. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
pose proof HJ1 as HJ.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_DUP)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ odd_awr_rs. odd_nowin. }
rename HF into HFa, HFr into HFra, HG into HGa.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msA end.
assert (KDA : forall a, aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a)
  by (odd_same HFra).
assert (GRA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGa Ha)).
(* branch 1: S_desk_counter_valid = 0 ? *)

psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* taken: the counter is not valid, so not a duplicate *)
  cbn [branch_taken] in Hc.
  rewrite (odd_sext E 35 (TW.u_at Bx TW.A_S_desk_counter_valid 4) E35 Hdvr) in Hc.
  change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (POD.od_eqb0 _ Hsw1) in Hc. apply Z.eqb_eq in Hc.
  assert (HND : ondata_dup Bx b = false).
  { unfold ondata_dup, TW.S_desk_counter_valid, TW.s32_at. rewrite Hc. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan OD_SET.
  { odd_awr_rs. odd_nowin. }
  rename HF into HFc1, HFr into HFrc1, HG into HGc1.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msC end.
  assert (KDC : forall a, aview segs (w_H W2) (ms_mem msC) a = aview segs (w_H W2) mem2 a).
  { intros a. rewrite <- (KDA a). revert a. odd_same HFrc1. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_SET)) mm rom) mdx) Q) end.
  apply (TOSET (ms_mem msC) _ (ms_regs msC));
  [ exact HJ
  | exact KDC
  | intros a Ha; exact (apresent_grows _ _ _ a HGc1 (GRA a Ha))
  | odd_regsset HS EE R2 R3 R4 R8 R9 R25 R26 R18 R19 R20 R21 R27 R22 R17
  | exact HND ].
- (* not taken: the counter is valid *)
  cbn [branch_taken] in Hc.
  rewrite (odd_sext E 35 (TW.u_at Bx TW.A_S_desk_counter_valid 4) E35 Hdvr) in Hc.
  change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (POD.od_eqb0 _ Hsw1) in Hc. apply Z.eqb_neq in Hc.
  assert (HV1 : negb (TW.S_desk_counter_valid Bx =? 0) = true)
    by (unfold TW.S_desk_counter_valid, TW.s32_at; apply negb_true_iff; apply Z.eqb_neq; exact Hc).
  clear Hc.
  (* ---- run 2: +0x248 .. +0x264 ---- *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { odd_awr_rs. odd_nowin. }
  rename HF into HFb, HFr into HFrb, HG into HGb.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msB end.
  assert (KDB : forall a, aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mem2 a).
  { intros a. rewrite <- (KDA a). revert a. odd_same HFrb. }
  assert (GRB : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HGb (GRA a Ha))).
  (* branch 2: fr_retry b = 0 ? *)

  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* taken: no retry, so not a duplicate *)
    cbn [branch_taken] in Hc.

    rewrite (odd_off0 E 12 (DSpec.fr_retry b) E12 ltac:(lia)) in Hc.
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (POD.od_eqb0 (DSpec.fr_retry b) ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (HND : ondata_dup Bx b = false)
      by (unfold ondata_dup; rewrite Hc; rewrite andb_false_r; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan OD_SET.
    { odd_awr_rs. odd_nowin. }
    rename HF into HFd, HFr into HFrd, HG into HGd.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msD end.
    assert (KDD : forall a, aview segs (w_H W2) (ms_mem msD) a = aview segs (w_H W2) mem2 a).
    { intros a. rewrite <- (KDB a). revert a. odd_same HFrd. }
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_SET)) mm rom) mdx) Q) end.
    apply (TOSET (ms_mem msD) _ (ms_regs msD));
    [ exact HJ
    | exact KDD
    | intros a Ha; exact (apresent_grows _ _ _ a HGd (GRB a Ha))
    | odd_regsset HS EE R2 R3 R4 R8 R9 R25 R26 R18 R19 R20 R21 R27 R22 R17
    | exact HND ].
  + (* not taken: there is a retry *)
    cbn [branch_taken] in Hc.
    rewrite (odd_off0 E 12 (DSpec.fr_retry b) E12 ltac:(lia)) in Hc.
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (POD.od_eqb0 (DSpec.fr_retry b) ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
    assert (HV3 : negb (DSpec.fr_retry b =? 0) = true)
      by (apply negb_true_iff; apply Z.eqb_neq; exact Hc).
    clear Hc.
    (* ---- run 3: +0x268 .. +0x26c ---- *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { odd_awr_rs. odd_nowin. }
    rename HF into HFe, HFr into HFre, HG into HGe.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msE end.
    assert (KDE : forall a, aview segs (w_H W2) (ms_mem msE) a = aview segs (w_H W2) mem2 a).
    { intros a. rewrite <- (KDB a). revert a. odd_same HFre. }
    assert (GRE : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msE) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HGe (GRB a Ha))).
    (* branch 3: fr_send b <> S_desk_counter ? *)

    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* taken: the counters differ, so not a duplicate *)
      cbn [branch_taken] in Hc.
      rewrite (odd_sext E 33 (DSpec.fr_send b) E33 Hsdr) in Hc.
      rewrite (odd_sext E 34 (TW.u_at Bx TW.A_S_desk_counter 4) E34 Hdcr) in Hc.
      rewrite (POD.od_eqb_s32 _ _ Hsdr Hdcr) in Hc. apply negb_true_iff in Hc.
      assert (HND : ondata_dup Bx b = false).
      { unfold ondata_dup, TW.S_desk_counter. rewrite Hc, andb_false_r, andb_false_l. reflexivity. }
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan OD_SET.
      { odd_awr_rs. odd_nowin. }
      rename HF into HFg, HFr into HFrg, HG into HGg.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msG end.
      assert (KDG : forall a, aview segs (w_H W2) (ms_mem msG) a = aview segs (w_H W2) mem2 a).
      { intros a. rewrite <- (KDE a). revert a. odd_same HFrg. }
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_SET)) mm rom) mdx) Q) end.
      apply (TOSET (ms_mem msG) _ (ms_regs msG));
      [ exact HJ
      | exact KDG
      | intros a Ha; exact (apresent_grows _ _ _ a HGg (GRE a Ha))
      | odd_regsset HS EE R2 R3 R4 R8 R9 R25 R26 R18 R19 R20 R21 R27 R22 R17
      | exact HND ].
    * (* not taken: the frame is a duplicate *)
      cbn [branch_taken] in Hc.
      rewrite (odd_sext E 33 (DSpec.fr_send b) E33 Hsdr) in Hc.
      rewrite (odd_sext E 34 (TW.u_at Bx TW.A_S_desk_counter 4) E34 Hdcr) in Hc.
      rewrite (POD.od_eqb_s32 _ _ Hsdr Hdcr) in Hc. apply negb_false_iff in Hc.
      assert (HDUPT : ondata_dup Bx b = true).
      { unfold ondata_dup, TW.S_desk_counter. rewrite HV1, Hc, HV3. reflexivity. }
      assert (EBw' : TW.set_S_stats_rx_duplicates Bx (TS0.u64 (TW.S_stats_rx_duplicates Bx + 1)) = Bw').
      { rewrite ondata_model, Hsc in Hm. cbv beta iota in Hm. fold Bx in Hm.
        rewrite HDUPT in Hm. cbv beta iota in Hm. exact (od_some_inv _ _ Hm). }
      (* ---- run 3b: the branch instruction, to +0x270 ---- *)
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ODD_P4.
      { odd_awr_rs. odd_nowin. }
      rename HF into HFh, HFr into HFrh, HG into HGh.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msH end.
      assert (KDH : forall a, aview segs (w_H W2) (ms_mem msH) a = aview segs (w_H W2) mem2 a).
      { intros a. rewrite <- (KDE a). revert a. odd_same HFrh. }
      assert (GRH : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msH) a)
        by (intros a Ha; exact (apresent_grows _ _ _ a HGh (GRE a Ha))).
      (* the registers at +0x270 *)

      assert (Y2 : YK11.getr (ms_regs msH) 2 = w64 sp1) by (odd_keep HS EE 2%nat (2%bv : bv 5) R2).
      assert (Y3 : YK11.getr (ms_regs msH) 3 = YK11.getr regs 3) by (odd_keep HS EE 3%nat (3%bv : bv 5) R3).
      assert (Y4 : YK11.getr (ms_regs msH) 4 = YK11.getr regs 4) by (odd_keep HS EE 4%nat (4%bv : bv 5) R4).
      assert (Y8 : YK11.getr (ms_regs msH) 8 = w64 (spZ regs)) by (odd_keep HS EE 8%nat (8%bv : bv 5) R8).
      assert (Y9 : YK11.getr (ms_regs msH) 9 = w64 sp1) by (odd_keep HS EE 9%nat (9%bv : bv 5) R9).
      assert (Y25 : YK11.getr (ms_regs msH) 25 = w64 (SHADOW_OFF + F / 8))
        by (odd_keep HS EE 25%nat (25%bv : bv 5) R25).
      assert (Y26 : YK11.getr (ms_regs msH) 26 = w64 F) by (odd_keep HS EE 26%nat (26%bv : bv 5) R26).
      assert (Y24 : YK11.getr (ms_regs msH) 24 = w64 (ONDATA_S + 18160))
        by (odd_keep HS EE 24%nat (24%bv : bv 5) R24).
      assert (Y27 : YK11.getr (ms_regs msH) 27 = w64 SHADOW_OFF)
        by (odd_keep HS EE 27%nat (27%bv : bv 5) R27).
      (* ---- run 4: +0x270 .. +0x290, then the jump to the release cut ---- *)
      assert (Hdur : 0 <= TW.u_at Bx (TW.OFF_g_s + 18168) 8 < 2 ^ 64) by exact (TWL.u_at_range Bx _ 8).
      assert (HVd0 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (ONDATA_S + 18168) 8
        (TW.u_at Bx (TW.OFF_g_s + 18168) 8))
        by exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 18168 8 TMAP_A_ok HTW2 TMAP_A_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      assert (HVd : YI04.val_mem segs (mrestrict (w_H W2) (ms_mem msH)) (ONDATA_S + 18168) 8
        (TW.u_at Bx (TW.OFF_g_s + 18168) 8)).
      { intros t Ht.
        rewrite (odm_mb_eq (w_H W2) (w_H W2) mem2 (ms_mem msH) (ONDATA_S + 18168 + Z.of_nat t) (KDH _)).
        exact (HVd0 t Ht). }
      assert (HRAd : range_addressable (aview segs (w_H W2) (ms_mem msH)) SHADOW_OFF (ONDATA_S + 18160) 56).
      { intros x Hx. destruct (HRAg (ONDATA_S + 18160) 56 ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) x Hx)
          as (s & Hs & Hok).
        exists s. split; [|exact Hok]. unfold shadow_of_addr in *. rewrite KDH. exact Hs. }
      pmkst HS.
      clear HS SHOK.
      destruct (odd_entryB W2 (ms_regs msH) (ms_mem msH) (TW.u_at Bx (TW.OFF_g_s + 18168) 8) Y24 Y27 Hdur
        HVd HRAd) as [HS SHOK].
      set (EB := odd_EB (ms_regs msH) (TW.u_at Bx (TW.OFF_g_s + 18168) 8)) in HS, SHOK.
      assert (HEIB : img_env VAL A_LIM EB) by (unfold EB; apply odd_envB).
      assert (EEB : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew EB n = YK11.getr (ms_regs msH) rr)
        by (intros n rr Hn; unfold EB; apply odd_ewB; exact Hn).
      assert (EB36 : ew EB 36 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18168) 8))
        by (unfold EB; apply odd_ewB36).
      assert (U24 : bv_unsigned (ew EB 24) = ONDATA_S + 18160)
        by (rewrite (EEB 24%nat (24%bv : bv 5) eq_refl), Y24; unfold w64; apply unsigned_lit_small;
            unfold ONDATA_S, TA_g_s; lia).
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan OD_REL.
      { odd_awr_rs.
        apply awr_ok_x_cons_g;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U24 in Ha;
          apply odm_inG; unfold TW.SZ_g_s; lia |].
        apply awr_ok_x_nil. }
      rename HF into HFf, HFr into HFrf, HG into HGf.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end.
      set (Zs := fun a => ONDATA_S + 18168 <= a < ONDATA_S + 18176) in *.
      assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a ->
        aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) (ms_mem msH) a).
      { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ Zs HFrf); [|exact Ha|exact Hn].
        intros b0 wlo whi x Hin Hx.
        lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
        cbn [In] in Hin.
        repeat (destruct Hin as [Hin | Hin];
          [ injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U24 in Hx; unfold Zs; cbv beta; lia |]).
        destruct Hin. }
      assert (GRF : forall a, apresent (w_H W2) (ms_mem msH) a -> apresent (w_H W2) (ms_mem msF) a)
        by (intros a Ha; exact (apresent_grows _ _ _ a HGf Ha)).
      (* the bytes the store left *)
      odd_region HS 0%nat HRdup.
      assert (ESD : TW.S_stats_rx_duplicates Bx = TW.u_at Bx (TW.OFF_g_s + 18168) 8).
      { unfold TW.S_stats_rx_duplicates, TW.A_S_stats_rx_duplicates.
        replace (TW.OFF_g_s + 18152 + 16) with (TW.OFF_g_s + 18168) by lia. reflexivity. }
      assert (RESd : bv_unsigned (sv_denot EB (SOff 36 1)) mod 2 ^ (8 * Z.of_nat (N.to_nat 8)) =
        TS0.u64 (TW.S_stats_rx_duplicates Bx + 1) mod 2 ^ (8 * Z.of_nat (N.to_nat 8))).
      { cbn [sv_denot]. rewrite MState.unsigned_lit_wrap, EB36, (unsigned_lit_small _ Hdur).
        change (8 * Z.of_nat (N.to_nat 8)) with 64. rewrite ESD. unfold TS0.u64.
        rewrite Z.mod_mod by lia. reflexivity. }
      assert (Bd : forall j, (j < 8)%nat ->
        aview segs (w_H W2) (ms_mem msF) (ONDATA_S + 18168 + Z.of_nat j) =
        Some (YO0f.le_byte (TS0.u64 (TW.S_stats_rx_duplicates Bx + 1)) 8 j)).
      { intros j Hj.
        replace (ONDATA_S + 18168 + Z.of_nat j) with (ONDATA_S + 18160 + 8 + Z.of_nat j) by lia.
        exact (odm_wr_bytes EB (w_H W2) (ms_mem msF) 24 (ONDATA_S + 18160) 8 16 8 16 _ 8 8
          (SOff 36 1) (TS0.u64 (TW.S_stats_rx_duplicates Bx + 1)) HRdup U24 ltac:(cbn [In]; auto)
          RESd j Hj). }
      (* the world at the release cut *)
      assert (TWF : tw_at TMAP_A (aview segs (w_H W2) (ms_mem msF)) Bw').
      { rewrite <- EBw'. apply (odd_tw (aview segs (w_H W2) (ms_mem msH))
          (aview segs (w_H W2) (ms_mem msF)) Bx); [| exact Bd |].
        - apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact HTW2 | intros x _; exact (KDH x)].
        - intros x Hx Hn. apply KP; [|exact Hn].
          pose proof (inG_low segs B transport_segs_low TG.G_HARNESS x HGX (odm_tw_in_G x Hx)) as Hl.
          unfold kLowMemEnd in Hl. lia. }
      (* what the call has kept *)
      assert (KPH : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem msH)
        (spZ regs - ONDATA_STK) (spZ regs) (ondata_wr Bw b)).
      { apply (odm_kept_step B LAWS lyc Sc W memc mdc W2 mem2 (ms_mem msH) (spZ regs - ONDATA_STK)
          (spZ regs) Bw b (fun _ : Z => False) HARc HGX ltac:(lia) ltac:(lia) ltac:(intros a []) HK);
        [ intros a Ha _; exact (KDH a) | exact GRH ]. }
      assert (KGE : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem msF)
        (spZ regs - ONDATA_STK) (spZ regs) (ondata_wr Bw b)).
      { assert (HZS : forall a, Zs a -> (spZ regs - ONDATA_STK <= a < spZ regs) \/ ondata_wr Bw b a).
        { intros a Ha. unfold Zs in Ha. cbv beta in Ha. right. unfold ondata_wr.
          right; right; right; right; right; right; left.
          unfold twa_fld, TW.A_S_stats_rx_duplicates, TW.OFF_g_s, ONDATA_S, TA_g_s in *. lia. }
        exact (odm_kept_step B LAWS lyc Sc W memc mdc W2 (ms_mem msH) (ms_mem msF) (spZ regs - ONDATA_STK)
          (spZ regs) Bw b Zs HARc HGX ltac:(lia) ltac:(lia) HZS KPH KP GRF). }
      (* the saved words, the frame's last word and the frame word at s1 + 24 *)
      assert (EFA : frame_addr ly2 ONDATA_CID pos = F)
        by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
      assert (HinF : In (ONDATA_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
      assert (HFfNG : forall a, F <= a < F + 256 -> ~ (ONDATA_S <= a < ONDATA_S + TW.SZ_g_s)).
      { intros a Ha Hg0. destruct (HGX a (odm_inG a Hg0)) as [Hi _].
        exact (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos a HAR2 HinF
          ltac:(rewrite EFA; change (fs_frame_bytes ONDATA_CID) with 256; lia) Hi). }
      assert (KDF : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a ->
        aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a)
        by (intros a Ha Hn; rewrite (KP a Ha Hn); exact (KDH a)).
      assert (HSV : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem msF)) (spZ regs - fst o) =
          Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) OD_SAVED).
      { apply Forall_forall. intros o Hin.
        assert (Hb : 8 <= fst o <= 104).
        { unfold OD_SAVED in Hin. cbn [In] in Hin.
          repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
        apply (AF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem msF))
          (spZ regs - fst o) (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))).
        - intros i Hi. apply KDF; [lia|]. unfold Zs, ONDATA_S, TA_g_s. cbv beta. lia.
        - exact (proj1 (Forall_forall _ _) Hsaved o Hin). }
      assert (HFL2 : rdword (aview segs (w_H W2) (ms_mem msF)) (F + OD_FBYTES - 8) =
        Some (flag_addr lyc ONDATA_CID pos)).
      { apply (AF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem msF))
          (F + OD_FBYTES - 8) (flag_addr lyc ONDATA_CID pos)); [|exact HFLw].
        intros i Hi. apply KDF; [unfold OD_FBYTES in *; lia|].
        unfold Zs. cbv beta. intros Hc2.
        exact (HFfNG (F + OD_FBYTES - 8 + i) ltac:(unfold OD_FBYTES; lia) ltac:(unfold TW.SZ_g_s; lia)). }
      assert (Hs24F : rdword (aview segs (w_H W2) (ms_mem msF)) (sp1 + 24) = Some F).
      { apply (AF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem msF)) (sp1 + 24) F);
        [|exact Hs24].
        intros i Hi. apply KDF; [lia|]. unfold Zs, ONDATA_S, TA_g_s. cbv beta. lia. }
      assert (Hgf2 : TW.g_fail_next Bw' <= 1).
      { assert (HLBw : length Bw = Z.to_nat TW.W_LEN)
          by exact (tw_len TMAP_A (aview segs (w_H W) memc) Bw Htw0).
        assert (HLB1 : length B1 = Z.to_nat TW.W_LEN)
          by exact (proj1 (TOK.send_control_m_keep _ _ _ _ _ _ _ HLBw Hsc)).
        rewrite <- EBw'.
        destruct (odm_w2_ok B1 b r now HLB1) as (G2 & LBx & _ & _).
        destruct (odm_dupw_ok Bx LBx) as (Gd & _).
        rewrite Gd. unfold Bx. rewrite G2. exact Hgf1. }
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OD_REL)) mm rom) mdx) Q) end.
      apply (REL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF
        Bw Bw' pos sp1 F ly2 S2 W2 (ms_mem msF) _ e (ms_regs msF) HFIX).
      -- unfold od_rel_cur.
         refine (conj _ (conj Hs24F (conj TWF Hgf2))).
         unfold od_cur.
         refine (conj _ (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj KGE (conj HSV HFL2)))))))).
         exact HJ.
      -- unfold od_regs_rel. repeat apply conj;
         [ odd_keep HS EEB 2%nat (2%bv : bv 5) Y2 | odd_keep HS EEB 3%nat (3%bv : bv 5) Y3
         | odd_keep HS EEB 4%nat (4%bv : bv 5) Y4 | odd_keep HS EEB 8%nat (8%bv : bv 5) Y8
         | odd_keep HS EEB 9%nat (9%bv : bv 5) Y9 | odd_keep HS EEB 25%nat (25%bv : bv 5) Y25
         | odd_keep HS EEB 26%nat (26%bv : bv 5) Y26 ].
Qed.

End dup.

Theorem od_dup : forall fx rc B MT, @od_dup_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@odd_dup_at fx rc B MT). Qed.

Print Assumptions od_dup.
