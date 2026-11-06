(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 460 of its 514 lines of code are new or changed and 505 lines of the source are left out. *)
(* on_data_seg_set: Theorem od_set : forall fx rc B MT, @od_set_stmt fx rc B MT (lib/B/Prog/on_data_seg_cut.v),
   the not-a-duplicate piece of the image-B walk of on_data, offsets +0x2ac .. +0x2e4 of the listing
   lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x88cf4 .. 0x88d2c). Image B's twin of
   lib/A/Prog/on_data_seg_set.v: image A's +0x294 .. +0x2cc at image B's offsets + 0x18, but for +0x2c8, where image
   B has `mv s8, a7` and image A `sd a7, 0x10(s1)`: image B writes no frame word here and hands the shadow address of
   f + 28 to the leaf's entry in s8 (od_regs_ka).

   What the code does. +0x2ac `lb a2, 0(s2)`: the shadow byte of f + 20, read through s2 (0, since f's 64 bytes are
   marked usable: on_ack_cg.v trans_dframe_at's decode_rd_ok, carried to this memory by od_cur's acall_kept_g), so
   +0x2b0 `bnez a2` is not taken; +0x2b4 - +0x2bc the shadow byte of s + 164 through s11 (0: trans_ondata_cells,
   the shadow entry of the token engine), +0x2c0 `lw a2, 0(s5)`: the 4-byte signed load of f + 20 (fr_send b
   through DgnTransportBCg.v frame_f_bytes), +0x2c4 `bnez a4` not taken; +0x2c8 `mv s8, a7`: s8 = the shadow
   address of f + 28; +0x2cc `sw a2, 0(a1)`: the low 32 bits of the sign extension at s + 164
   (set_S_desk_counter .. (fr_send b)); +0x2d0 - +0x2d4 the shadow byte of s + 168 through a3 (0), +0x2d8 - +0x2dc
   `sw 1` at s + 168 (set_S_desk_counter_valid: the world is now ondata_w3 (ondata_w2 B1 b r now) b); +0x2e0
   `mv a0, s4` (a0 = fp) and the `jal` at +0x2e4 (transportb_sigma TB_diginet_frame_is_keepalive = 0x8b128), whose
   return address is BASE + OD_KAR: the run ends at the leaf's entry and od_ka_at concludes.

   One run of the token engine (lib/B/Prog/TransportGRunB.v paj_run_x over the caller's G journal). The symbolic
   state at +0x2ac: the registers as atoms 0 .. 31, atom 33 the 4 bytes of f + 20; regions: the shadow byte of
   s + 168 (a3, read 0), the 4 bytes at s + 164 (a1, written), the 4 bytes at s + 168 (a0, written), the shadow
   byte of f + 20 (s2, read 0) and the 4 bytes at f + 20 (s5, read); the shadow entry of [s + 164, s + 172) over
   the base s11 decides the check of the access at s + 164.

   The two stores into g_s are bytes of G (W_journalG.v awr_ok_x_cons_g); what the call has kept runs over them by
   on_data_seg_midkit.v odm_kept_step, and the world relation moves by TWorldG.v tw_write twice (ods_tw). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg on_data_seg_cut on_data_seg_midkit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require on_data.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module POD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.on_data.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x2ac                                      *)
(* ------------------------------------------------------------------ *)

Definition ods_SH13 : Z := SHADOW_OFF + (ONDATA_S + 168) / 8.

Definition ods_rg_sh13 : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition ods_rg_s164 : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 4 [].
Definition ods_rg_s168 : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 4 [].
Definition ods_rg_sh18 : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition ods_rg_f20 : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition ods_facts : facts :=
  mkFacts [(10%nat, mkAF (ONDATA_S + 168) (ONDATA_S + 168) 3);
           (11%nat, mkAF (ONDATA_S + 164) (ONDATA_S + 164) 2);
           (13%nat, mkAF ods_SH13 ods_SH13 0);
           (18%nat, mkAF SHADOW_OFF (2 ^ 47 - 64) 0); (21%nat, mkAF 4096 (2 ^ 47 - 64) 2);
           (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ods_SH : list shent := [mkSHE 11 0 8].
Definition ods_Bx : sv := SOff 27 0.
Definition ods_ss : sstate :=
  mkSS OD_SET sr_atoms [ods_rg_sh13; ods_rg_s164; ods_rg_s168; ods_rg_sh18; ods_rg_f20]
    None ods_facts.

(* The world after the two stores: set_S_desk_counter, then set_S_desk_counter_valid. *)
Lemma ods_tw : forall (rd rd' : Z -> option Z) B2 b,
  tw_at TMAP_B rd B2 ->
  (forall j, (j < 4)%nat -> rd' (ONDATA_S + 164 + Z.of_nat j) =
     Some (YO0f.le_byte (bv_swrap 32 (DSpec.fr_send b)) 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (ONDATA_S + 168 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (ONDATA_S + 164 <= x < ONDATA_S + 172) -> rd' x = rd x) ->
  tw_at TMAP_B rd' (ondata_w3 B2 b).
Proof.
intros rd rd' B2 b Hat H1 H2 HO.
assert (CS : ONDATA_S = TB_g_s) by reflexivity.
set (rdm := fun x => if ((ONDATA_S + 168 <=? x) && (x <? ONDATA_S + 172))%bool then rd x else rd' x).
assert (Ha : tw_at TMAP_B rdm (TW.upd B2 (TW.OFF_g_s + 164) (TW.put 4 (bv_swrap 32 (DSpec.fr_send b))))).
{ apply (tw_write TMAP_B rd rdm B2 TW.OFF_g_s TB_g_s TW.SZ_g_s 164 4 (bv_swrap 32 (DSpec.fr_send b))
    TMAP_B_ok Hat TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold rdm. rewrite <- CS.
    assert (Hb : ((ONDATA_S + 168 <=? ONDATA_S + 164 + Z.of_nat j) &&
                  (ONDATA_S + 164 + Z.of_nat j <? ONDATA_S + 172))%bool = false)
      by (apply andb_false_iff; left; apply Z.leb_gt; lia).
    rewrite Hb. exact (H1 j Hj).
  - intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
    destruct ((ONDATA_S + 168 <=? x) && (x <? ONDATA_S + 172))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb. apply HO; [exact Hx|].
    destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; cbn in Hn; lia. }
rewrite POD.od_put4_swrap in Ha.
unfold ondata_w3, TW.set_S_desk_counter_valid, TW.set_S_desk_counter,
  TW.A_S_desk_counter_valid, TW.A_S_desk_counter.
apply (tw_write TMAP_B rdm rd' _ TW.OFF_g_s TB_g_s TW.SZ_g_s 168 4 1 TMAP_B_ok Ha TMAP_B_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS. exact (H2 j Hj).
- intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
  destruct ((ONDATA_S + 168 <=? x) && (x <? ONDATA_S + 172))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. cbn in Hn. apply Hn. lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac ods_reg HS r v H tac :=
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
Ltac ods_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac ods_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.

Section set. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition ods_E (regs2 : bvmap 5 word) (sd : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [Z_to_bv 64 0; Z_to_bv 64 sd]).

Lemma ods_ew_reg : forall regs2 sd n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ods_E regs2 sd) n = YK11.getr regs2 r.
Proof. intros regs2 sd n r Hn. unfold ods_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma ods_ew_33 : forall regs2 sd, ew (ods_E regs2 sd) 33 = Z_to_bv 64 sd.
Proof.
intros regs2 sd. unfold ods_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs2 _ 1).
Qed.

Lemma ods_env : forall regs2 sd, img_env VAL A_LIM (ods_E regs2 sd).
Proof. intros regs2 sd. unfold ods_E. apply Eimg_env. Qed.

(* The symbolic state at +0x2ac holds of the machine state there. *)
Lemma ods_entry : forall (W2 : world segs) (regs2 : bvmap 5 word) mem2 (fp sd : Z),
  YK11.getr regs2 10 = w64 (ONDATA_S + 168) ->
  YK11.getr regs2 11 = w64 (ONDATA_S + 164) ->
  YK11.getr regs2 13 = w64 ods_SH13 ->
  YK11.getr regs2 18 = w64 (SHADOW_OFF + (fp + 20) / 8) ->
  YK11.getr regs2 21 = w64 (fp + 20) ->
  YK11.getr regs2 27 = w64 SHADOW_OFF ->
  4096 <= fp -> fp mod 8 = 0 -> fp + 64 <= 2 ^ 47 - 128 ->
  (fp + 64 <= kLowShadowBeg \/ kHighMemBeg <= fp) ->
  (fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp) ->
  0 <= sd < 2 ^ 32 ->
  aview segs (w_H W2) mem2 ods_SH13 = Some 0 ->
  aview segs (w_H W2) mem2 (SHADOW_OFF + (fp + 20) / 8) = Some 0 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (fp + 20) 4 sd ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (ONDATA_S + 164) 8 ->
  st_ok_pi segs VAL (ods_E regs2 sd) ods_ss
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_SET)) mem2 (YK11.seg_rom segs))) /\
  sh_ok segs ods_Bx ods_SH (ods_E regs2 sd) (mrestrict (w_H W2) mem2).
Proof.
intros W2 regs2 mem2 fp sd R10 R11 R13 R18 R21 R27 Hfp0 Hfp8 Hfph HAP HFG Hsd HS13 HS18 HV20 HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := ods_E regs2 sd).
assert (EG : (ONDATA_S + 168) / 8 = 769757) by reflexivity.
assert (HSH : 0 <= (fp + 20) / 8 /\ (fp + 20) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos; lia|]; apply Z.div_le_upper_bound; lia).
assert (U10 : bv_unsigned (ew E 10) = ONDATA_S + 168)
  by (unfold E; rewrite (ods_ew_reg regs2 sd 10 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small;
      unfold ONDATA_S, TB_g_s; lia).
assert (U11 : bv_unsigned (ew E 11) = ONDATA_S + 164)
  by (unfold E; rewrite (ods_ew_reg regs2 sd 11 11%bv eq_refl), R11; unfold w64; apply unsigned_lit_small;
      unfold ONDATA_S, TB_g_s; lia).
assert (U13 : bv_unsigned (ew E 13) = ods_SH13)
  by (unfold E; rewrite (ods_ew_reg regs2 sd 13 13%bv eq_refl), R13; unfold w64; apply unsigned_lit_small;
      unfold ods_SH13, SHADOW_OFF; rewrite EG; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + (fp + 20) / 8)
  by (unfold E; rewrite (ods_ew_reg regs2 sd 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF in *; lia).
assert (U21 : bv_unsigned (ew E 21) = fp + 20)
  by (unfold E; rewrite (ods_ew_reg regs2 sd 21 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (unfold E; rewrite (ods_ew_reg regs2 sd 27 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = sd)
  by (unfold E; rewrite (ods_ew_33 regs2 sd); apply unsigned_lit_small; lia).
(* the shadow byte of f + 20 is not the shadow byte of s + 168: f lies below or above g_s *)
assert (HNE : (fp + 20) / 8 <= 769735 \/ 772021 <= (fp + 20) / 8).
{ destruct HFG as [h | h].
  - left. assert (Hle : (fp + 20) / 8 <= 6157887 / 8)
      by (apply Z.div_le_mono; [lia | unfold ONDATA_S, TB_g_s in h; lia]).
    change (6157887 / 8) with 769735 in Hle. exact Hle.
  - right. assert (Hge : 6176172 / 8 <= (fp + 20) / 8)
      by (apply Z.div_le_mono; [lia | unfold ONDATA_S, TB_g_s, TW.SZ_g_s in h; lia]).
    change (6176172 / 8) with 772021 in Hge. exact Hge. }
split.
- rewrite restrict_mkst_fx. unfold ods_ss.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [ods_rg_sh13 ods_rg_s164 ods_rg_s168 ods_rg_sh18 ods_rg_f20
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U13. split; [unfold ods_SH13, SHADOW_OFF; rewrite EG; lia|].
      split; [unfold ods_SH13, SHADOW_OFF; rewrite EG; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ ods_SH13 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply odm_val0. exact HS13.
    * rewrite U11. split; [unfold ONDATA_S, TB_g_s; lia|]. split; [unfold ONDATA_S, TB_g_s; lia|].
      split; [|constructor]. intros o Ho.
      apply (gx_rw_writable segs TG.G_HARNESS_B (ONDATA_S + 164 + o) G_HARNESS_B_rw).
      apply odm_inG. unfold TW.SZ_g_s. lia.
    * rewrite U10. split; [unfold ONDATA_S, TB_g_s; lia|]. split; [unfold ONDATA_S, TB_g_s; lia|].
      split; [|constructor]. intros o Ho.
      apply (gx_rw_writable segs TG.G_HARNESS_B (ONDATA_S + 168 + o) G_HARNESS_B_rw).
      apply odm_inG. unfold TW.SZ_g_s. lia.
    * rewrite U18. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (SHADOW_OFF + (fp + 20) / 8) 0 1 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply odm_val0. exact HS18.
    * rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (fp + 20) 0 4 (SOff 33 0) sd);
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact HV20.
  + apply pairwise_disjoint_of_extents.
    unfold ods_rg_sh13, ods_rg_s164, ods_rg_s168, ods_rg_sh18, ods_rg_f20, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U10, U11, U13, U18, U21.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold ods_SH13 in *. rewrite EG in *.
    unfold ONDATA_S, TB_g_s, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, TW.SZ_g_s in *.
    repeat split;
      first [ exact I | lia
            | destruct HNE as [h | h]; lia
            | destruct HAP as [h | h]; lia
            | destruct HFG as [h | h]; lia ].
  + unfold ods_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U11, U13, U18, U21, U27.
    change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (M11 : (ONDATA_S + 164) mod 4 = 0) by reflexivity.
    assert (M10 : (ONDATA_S + 168) mod 8 = 0) by reflexivity.
    assert (M21 : (fp + 20) mod 4 = 0).
    { pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite Hfp8, Z.add_0_r in D.
      replace (fp + 20) with ((2 * (fp / 8) + 5) * 4) by lia. apply Z_mod_mult. }
    repeat match goal with |- _ /\ _ => split end; try exact I;
    unfold ods_SH13 in *; rewrite ?EG in *;
    unfold ONDATA_S, TB_g_s, SHADOW_OFF in *; first [exact M11 | exact M10 | exact M21 | lia].
- assert (UB : U E ods_Bx = SHADOW_OFF).
  { unfold U, ods_Bx. cbn [sv_denot]. rewrite U27, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, ods_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W2) mem2 E ods_Bx 11 (ONDATA_S + 164) 8 (ONDATA_S + 164) 0 8 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U11, Z.add_0_r. apply unsigned_lit_small.
    unfold ONDATA_S, TB_g_s; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold ONDATA_S, TB_g_s, SHADOW_OFF in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma ods_set_at : @od_set_stmt fx rc B MT.
Proof.
unfold od_set_stmt, od_set_at.
intros KA LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F B1 r f ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HPCS & HCELLS & HSC & HROU & HRNE & HROR & HRNO & LAWS & MTL & MTF & SMP & ASF & FFL & HGX
  & HGNE).
pose proof HFIX as (HPRE & HTFN & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HPRE as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hfn0
  & Hm & HTF & HROM & HAPT & HINV1 & HINV4 & HINV3 & Hcnt & Hev).
pose proof HCUR as ((HCUR0 & Hs24 & Hsc & HTW2 & Hgf1) & HDUP).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as ((HRR & R18 & R19 & R20 & R21 & R27) & R22 & R10 & R11 & R13 & R17).
pose proof HRR as (R2 & R3 & R4 & R8 & R9 & R25 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDF as (Hcode & Hbuf0 & Hgb & Hsrc & Hdow & HnoG & Hfp0 & Hfp8 & Hfjl & Hgf & Hfake & Hrdok & Hfow).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0a & Hstk1 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4272 <= ONDATA_STK).
{ unfold ONDATA_STK, ONDATA_FRAME, ONDATA_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm2; assert (Ha4 : a = 4096) by reflexivity end.
  lia. }
assert (Hsp1 : spZ regs - 192 < sp1 <= spZ regs - 160).
{ rewrite Esp1. unfold ONDATA_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M. lia. }
assert (Hsp1al : sp1 mod 32 = 0).
{ rewrite Esp1.
  replace (32 * ((spZ regs - ONDATA_FRAME) / 32)) with (((spZ regs - ONDATA_FRAME) / 32) * 32) by lia.
  apply Z_mod_mult. }
assert (Hsp1R : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
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
assert (HS13 : aview segs (w_H W2) mem2 ods_SH13 = Some 0).
{ unfold ods_SH13. apply (odm_sh0 _ ONDATA_S TW.SZ_g_s 168);
  [reflexivity | lia | unfold TW.SZ_g_s; lia | apply HRAg; [lia | lia]]. }
(* f is apart from g_s, from its own shadow and from the stack window *)
destruct Hfake as (cid0 & pos0 & Hin0 & Hlo0 & Hhi0).
assert (HFNG : forall a, fp <= a < fp + 64 -> ~ (ONDATA_S <= a < ONDATA_S + TW.SZ_g_s)).
{ intros a Ha Hg0. destruct (HGX a (odm_inG a Hg0)) as [Hi _].
  exact (frm_img segs B LAWS lyc Sc W memc mdc cid0 pos0 a HARc Hin0
    ltac:(unfold FRAME_F_SIZE in Hhi0; lia) Hi). }
assert (HFG : fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp).
{ destruct (Z_le_gt_dec (fp + 64) ONDATA_S) as [h | h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONDATA_S + TW.SZ_g_s) fp) as [h2 | h2]; [right; exact h2|].
  exfalso. apply (HFNG (Z.max fp ONDATA_S)); unfold ONDATA_S, TB_g_s, TW.SZ_g_s in *; lia. }
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid0 pos0 HARc Hin0) as (_ & HFapp0 & _ & _).
pose proof (@ASAN_CEIL_range rc) as (HCE & _).
unfold in_app in HFapp0. unfold FRAME_F_SIZE in Hhi0.
assert (HAPf : fp + 64 <= kLowShadowBeg \/ kHighMemBeg <= fp).
{ destruct HFapp0 as (_ & [HL | (HH & _)]); [left | right]; lia. }
assert (Hfph : fp + 64 <= 2 ^ 47 - 128).
{ destruct HFapp0 as (_ & [HL | (HH & HC)]); unfold kLowShadowBeg in *; lia. }
assert (Hsdr : 0 <= DSpec.fr_send b < 2 ^ 32) by apply DSpec.be32_range.
(* the own frame is apart from g_s (its last word is read at the release) *)
assert (EFA : frame_addr ly2 ONDATA_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (HinF : In (ONDATA_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFfNG : forall a, F <= a < F + 256 -> ~ (ONDATA_S <= a < ONDATA_S + TW.SZ_g_s)).
{ intros a Ha Hg0. destruct (HGX a (odm_inG a Hg0)) as [Hi _].
  exact (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos a HAR2 HinF
    ltac:(rewrite EFA; change (fs_frame_bytes ONDATA_CID) with 256; lia) Hi). }
destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos HAR2 HinF) as (HF4096 & HFceil & _).
rewrite EFA in HF4096, HFceil. change (fs_frame_bytes ONDATA_CID) with 256 in HFceil.
assert (Hfp4 : 4096 <= fp) by (destruct HFapp0 as (H4 & _); lia).
(* ---- the run ---- *)
destruct (ods_entry W2 regs2 mem2 fp (DSpec.fr_send b) R10 R11 R13 R18 R21 R27
  Hfp4 Hfp8 Hfph HAPf HFG Hsdr HS13 HS18 HV20 ltac:(apply HRAg; [lia | unfold TW.SZ_g_s; lia]))
  as [HS SHOK].
set (E := ods_E regs2 (DSpec.fr_send b)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply ods_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E; apply ods_ew_reg; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 (DSpec.fr_send b)) by (unfold E; apply ods_ew_33).
assert (U10 : bv_unsigned (ew E 10) = ONDATA_S + 168)
  by (unfold E; rewrite (ods_ew_reg regs2 _ 10 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small;
      unfold ONDATA_S, TB_g_s; lia).
assert (U11 : bv_unsigned (ew E 11) = ONDATA_S + 164)
  by (unfold E; rewrite (ods_ew_reg regs2 _ 11 11%bv eq_refl), R11; unfold w64; apply unsigned_lit_small;
      unfold ONDATA_S, TB_g_s; lia).
assert (U17 : bv_unsigned (ew E 17) = SHADOW_OFF + (fp + 28) / 8).
{ assert (HD : 0 <= (fp + 28) / 8 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold E; rewrite (ods_ew_reg regs2 _ 17 17%bv eq_refl), R17; unfold w64; apply unsigned_lit_small;
  unfold SHADOW_OFF in *; lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof HJ1 as HJ.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_SET)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ods_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U11 in Ha;
    apply odm_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U10 in Ha;
    apply odm_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
(* ---- the state at the leaf's entry ---- *)
(* what the run wrote *)
set (Zs := fun a => ONDATA_S + 164 <= a < ONDATA_S + 172) in *.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ Zs HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U10, ?U11 in Hx;
      unfold Zs; lia |]).
  destruct Hin. }
assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
(* the registers at the leaf's entry *)
ods_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + OD_KAR)) X1 ltac:(apply codeptr_val; exact HEI).
ods_reg HS (10%bv : bv 5) (w64 fp) X10
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
ods_reg HS (2%bv : bv 5) (w64 sp1) X2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
ods_reg HS (3%bv : bv 5) (YK11.getr regs 3) X3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3).
ods_reg HS (4%bv : bv 5) (YK11.getr regs 4) X4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4).
ods_reg HS (8%bv : bv 5) (w64 (spZ regs)) X8
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
ods_reg HS (9%bv : bv 5) (w64 sp1) X9
  ltac:(cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
ods_reg HS (25%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) X25
  ltac:(cbn [sv_denot]; rewrite (EE 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R25).
ods_reg HS (26%bv : bv 5) (w64 F) X26
  ltac:(cbn [sv_denot]; rewrite (EE 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R26).
ods_reg HS (18%bv : bv 5) (w64 (SHADOW_OFF + (fp + 20) / 8)) X18
  ltac:(cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
ods_reg HS (19%bv : bv 5) (w64 ONDATA_S) X19
  ltac:(cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R19).
ods_reg HS (20%bv : bv 5) (w64 fp) X20
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
ods_reg HS (21%bv : bv 5) (w64 (fp + 20)) X21
  ltac:(cbn [sv_denot]; rewrite (EE 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R21).
ods_reg HS (22%bv : bv 5) (w64 (fp + 28)) X22
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
ods_reg HS (24%bv : bv 5) (w64 (SHADOW_OFF + (fp + 28) / 8)) X24
  ltac:(cbn [sv_denot]; rewrite (EE 17%nat 17%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R17).
ods_reg HS (27%bv : bv 5) (w64 SHADOW_OFF) X27
  ltac:(cbn [sv_denot]; rewrite (EE 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R27).
(* the bytes the run left *)
ods_region HS 1%nat HR164. ods_region HS 2%nat HR168.
assert (SEXT : sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (bv_swrap 32 (DSpec.fr_send b))).
{ cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia. rewrite unsigned_lit_small by lia. reflexivity. }
assert (RES164 : bv_unsigned (sv_denot E (SExt true 32 (SOff 33 0))) mod 2 ^ (8 * Z.of_nat (N.to_nat 4)) =
  bv_swrap 32 (DSpec.fr_send b) mod 2 ^ (8 * Z.of_nat (N.to_nat 4))).
{ rewrite SEXT, MState.unsigned_lit_wrap. change (8 * Z.of_nat (N.to_nat 4)) with 32.
  set (x := bv_swrap 32 (DSpec.fr_send b)).
  pose proof (Z.div_mod x (2 ^ 64) ltac:(lia)) as D.
  replace (x mod 2 ^ 64) with (x + (- (2 ^ 32 * (x / 2 ^ 64))) * 2 ^ 32) by lia.
  apply Z_mod_plus_full. }
assert (RES168 : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_nat (N.to_nat 4)) =
  1 mod 2 ^ (8 * Z.of_nat (N.to_nat 4))).
{ cbn [sv_denot]. rewrite unsigned_lit_small by lia. reflexivity. }
assert (B164 : forall j, (j < 4)%nat -> aview segs (w_H W2) (ms_mem ms) (ONDATA_S + 164 + Z.of_nat j) =
  Some (YO0f.le_byte (bv_swrap 32 (DSpec.fr_send b)) 4 j)).
{ intros j Hj.
  replace (ONDATA_S + 164 + Z.of_nat j) with (ONDATA_S + 164 + 0 + Z.of_nat j) by lia.
  exact (odm_wr_bytes E (w_H W2) (ms_mem ms) 11 (ONDATA_S + 164) 0 4 0 4 _ 0 4
    (SExt true 32 (SOff 33 0)) (bv_swrap 32 (DSpec.fr_send b)) HR164 U11 ltac:(cbn [In]; auto) RES164 j Hj). }
assert (B168 : forall j, (j < 4)%nat -> aview segs (w_H W2) (ms_mem ms) (ONDATA_S + 168 + Z.of_nat j) =
  Some (YO0f.le_byte 1 4 j)).
{ intros j Hj.
  replace (ONDATA_S + 168 + Z.of_nat j) with (ONDATA_S + 168 + 0 + Z.of_nat j) by lia.
  exact (odm_wr_bytes E (w_H W2) (ms_mem ms) 10 (ONDATA_S + 168) 0 4 0 4 _ 0 4 (SLit 1) 1
    HR168 U10 ltac:(cbn [In]; auto) RES168 j Hj). }
(* the world relation after the two stores *)
assert (TWE : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms)) (ondata_w3 (ondata_w2 B1 b r now) b)).
{ apply (ods_tw (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) (ondata_w2 B1 b r now) b HTW2
    B164 B168).
  intros x Hx Hn. apply KP.
  - pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX (odm_tw_in_G x Hx)) as Hl.
    unfold kLowMemEnd in Hl. lia.
  - unfold Zs. exact Hn. }
(* what the call has kept, over the run *)
assert (KGE : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem ms)
  (spZ regs - ONDATA_STK) (spZ regs) (ondata_wr Bw b)).
{ assert (HZS : forall a, Zs a -> (spZ regs - ONDATA_STK <= a < spZ regs) \/ ondata_wr Bw b a).
  { intros a Ha. unfold Zs in Ha. right.
    unfold ondata_wr. destruct (Z_lt_le_dec a (ONDATA_S + 168)) as [h | h].
    - right; right; right; right; right; right; right; left.
      unfold twb_fld, TW.A_S_desk_counter, TW.OFF_g_s, ONDATA_S, TB_g_s in *. lia.
    - right; right; right; right; right; right; right; right; left.
      unfold twb_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s, ONDATA_S, TB_g_s in *. lia. }
  exact (odm_kept_step B LAWS lyc Sc W memc mdc W2 mem2 (ms_mem ms) (spZ regs - ONDATA_STK) (spZ regs) Bw b Zs
    HARc HGX ltac:(lia) ltac:(lia) HZS HK KP GA). }
(* the saved words and the frame's last word *)
assert (HSV : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem ms)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) OD_SAVED).
{ apply Forall_forall. intros o Hin.
  assert (Hb : 8 <= fst o <= 104).
  { unfold OD_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  apply (YF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) (spZ regs - fst o)
    (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))).
  - intros i Hi. apply KP; [lia|]. unfold Zs, ONDATA_S, TB_g_s. lia.
  - exact (proj1 (Forall_forall _ _) Hsaved o Hin). }
assert (HFL2 : rdword (aview segs (w_H W2) (ms_mem ms)) (F + OD_FBYTES - 8) =
  Some (flag_addr lyc ONDATA_CID pos)).
{ apply (YF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) (F + OD_FBYTES - 8)
    (flag_addr lyc ONDATA_CID pos)); [|exact HFLw].
  intros i Hi. apply KP; [unfold OD_FBYTES in *; lia|].
  unfold Zs. intros Hc.
  exact (HFfNG (F + OD_FBYTES - 8 + i) ltac:(unfold OD_FBYTES; lia) ltac:(unfold TW.SZ_g_s; lia)). }
(* the frame word at s1 + 24 *)
assert (Hs24E : rdword (aview segs (w_H W2) (ms_mem ms)) (sp1 + 24) = Some F).
{ apply (YF0x.rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) (sp1 + 24) F);
  [|exact Hs24].
  intros i Hi. apply KP; [lia|]. unfold Zs, ONDATA_S, TB_g_s. lia. }
(* ---- conclude by od_ka_at ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
    (Z_to_bv 64 (transportb_sigma TB_diginet_frame_is_keepalive)) mm rom) mdx) Q) end.
apply (KA LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F B1 r f ly2 S2 W2 (ms_mem ms) _ e (ms_regs ms) HFIX).
- unfold od_ka_cur.
  refine (conj _ (conj Hs24E (conj Hsc (conj TWE (conj Hgf1 HDUP))))).
  unfold od_cur.
  refine (conj _ (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj KGE (conj HSV HFL2)))))))).
  exact HJ.
- unfold od_regs_ka, od_regs_s, od_regs_rel.
  refine (conj (conj (conj X2 (conj _ (conj _ (conj X8 (conj X9 (conj X25 X26))))))
    (conj X18 (conj X19 (conj X20 (conj X21 X27))))) (conj X1 (conj X22 (conj X24 X10))))%type.
  + rewrite X3. reflexivity.
  + rewrite X4. reflexivity.
Qed.

End set.

Theorem od_set : forall fx rc B MT, @od_set_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ods_set_at fx rc B MT). Qed.

Print Assumptions od_set.
