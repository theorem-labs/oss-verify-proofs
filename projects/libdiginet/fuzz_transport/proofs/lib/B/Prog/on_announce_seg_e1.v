(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 697 of its 763 lines of code are new or changed and 1858 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/on_announce_seg_tail.v; 548 of its 637 lines of code are new or changed and 674 lines of the source are left out. *)
(* on_announce_seg_e1: Lemma onann_e1_piece : onann_e1_stmt (lib/B/Prog/OnannCutB.v), the e1 arm of the walk of
   on_announce on fuzz_transport.asan-ubsan (cmd 0xe1 after the desk notice, diginet_session.c:209-214), offsets
   +0x4a0 .. +0x4e0 of the listing lib/B/Prog/DgnTransportBList.v (AF_on_announce = 0x6a28; 0x88168 .. 0x881a8). It ends
   at the foreign cut ONANN_FN (+0x4e4, off < 0), which the onann_fn_at it is given closes, or, after maybe_online, at
   the release cut ONANN_NREL (+0x61c), which the onann_nrel_at it is given closes.

   proves function on_announce (reuse search: git grep -nE '\bon_announce\b' on origin/main, origin/ossv/recipes,
   origin/ossv/candidates, origin/release/pau-projects-recipes -- 'proofs/*' 'projects/*/*/proofs/*' / proof-index
   on_announce; no released proof of it, by name or by address; none: written new)

   What the code does. +0x4a0 `addi a0, s4, 136`, +0x4a4 `srli a1, a0, 3`, +0x4a8 `add a1, a1, s8`: a0 = s + 136
   (g_s.foreign), a1 = its shadow address; +0x4ac `blt s7, zero, +0x4e4` on off = find_mac's result (s7).
     off < 0: the foreign cut +0x4e4 with a0 = s + 136, a1 = its shadow address (onann_regs_fn); the memory is the
     cut's; the model continues at set_S_foreign B2 1 (OnannCutB.v onann_k_e1 at off < 0 is onann_k_fn).
     0 <= off: +0x4b0 `lb a1, 0(a1)`, +0x4b4 `bne a1, zero, +0x7d0`: the shadow byte of s + 136 is 0 (g_s's payload
     lies in the record's zero shadow, on_announce_cg.v trans_onann_cells), so the report path is not taken;
     +0x4b8 `sw zero, 136(s4)` (:213, g_s.foreign = 0); +0x4bc .. +0x4cc the same check of s + 140; +0x4d0 `li a0, 1`,
     +0x4d4 `sw a0, 140(s4)` (:214, g_s.e1_named_us = 1); +0x4d8 `mv a0, s4`; +0x4dc `jal maybe_online` (return
     +0x4e0); +0x4e0 `j +0x61c`, the release cut.
   The runs are the token engine's over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x),
   with s4 = atom 20 pinned to ONANN_S (alignment 2 ^ 6), s8 = atom 24 the shadow base, and the shadow entry of
   [s + 136, s + 152) (both checks are covered: their 8-byte granules lie in g_s's zero shadow):
     run 1   +0x4a0 .. +0x4ac  no region; it stops at the `blt` (DgnTransportBPaLib.v psrr_branch_tok splits it);
     the arm off < 0           a run to +0x4e4, no region, no byte written;
     the arm 0 <= off          the region [s + 136, s + 144) of s4 added (st_ok_pi_add_region), written: a run to the
                               call of maybe_online (chunks 0 at s + 136 and 1 at s + 140);
     after maybe_online        a run from +0x4e0 to +0x61c, no region.
   The maybe_online call (maybe_online_cg.v transport_maybe_online_cg at transportb_sigma TB_maybe_online), premise by
   premise: the journal at the call state; ra = +0x4e0; gp, tp, a0 = s = MAYBEON_S; sp = sp1 (32-aligned), its window
   MAYBEON_STK inside on_announce's (ONANN_STK = 9008, MAYBEON_STK = 8416, sp1 >= spZ - 208); tw_at at
   set_S_e1_named_us (set_S_foreign B2 0) 1 by two TWorldG.v tw_writes; g_fail_next of that world is B2's
   (on_announce_seg_kit.v onann_gfn_upd); the model (onann_k_e1 at 0 <= off); trans_tframe_at and trans_rom_view_rd at
   the call state (kit onann_tf_cur, onann_rom_cur); maybeon_apart (kit onann_apart_mo, with B2 = set_GOT_desk
   (onann_w1 ..) d from onann_b2); count_cid 2 of the call state = count_cid 2 (frames Sc) (the own frame is of class
   3); no event. Its post folds into onann_cur by TransportGCg.v dk_kept_trans_nf_g (its written range is a part of
   onann_wr Bw b: kit onann_wr_mo), the saved words and the frame's last word by its kept clauses.
   onann_cur is carried over each run by oe1_cur_step (lib/A/Prog/TransportGFrame.v dk_kept_step_gw: the run changed
   at most g_s's foreign and e1_named_us, bytes of G in onann_wr Bw b, kit onann_wr_foreign / onann_wr_e1nu).

   Trap and error paths on this piece: the slow paths of the two checks (`bne` at +0x4b4 to +0x7d0 and at +0x4cc to
   +0x7e0): the shadow bytes of s + 136 and s + 140 are 0. This piece passes no UBSan trap word. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg set_state_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states and the model on this piece                  *)
(* ------------------------------------------------------------------ *)

(* s4 = s (64-aligned) and s8 = the shadow base; no region at +0x4a0. *)
Definition oe1_facts : facts :=
  mkFacts [(20%nat, mkAF ONANN_S ONANN_S 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_oe1 : sstate := mkSS ONANN_E1 sr_atoms [] None oe1_facts.
(* The shadow entry of the two checks ([s + 136, s + 152) covers the 8 bytes from s + 136 and from s + 140) and the
   shadow base s8. *)
Definition OE1_SH : list shent := [mkSHE 20 136 152].
Definition OE1_Bx : sv := SOff 24 0.
(* The two 4-byte fields g_s.foreign and g_s.e1_named_us at s4 + 136, written (added after the `blt`). *)
Definition oe1_rg : YP09.region := YP09.mkRegion (Some 20%nat) 136 144 136 144 [].
(* maybe_online's return address: the `j +0x61c` at +0x4e0; the run from it has no region and no shadow entry. *)
Definition OE1_RET : Z := AF_on_announce + 0x4e0.
Definition OE1_B0 : Z * Z := (0, 0).
Definition OE1_BJ : sv := SOff 25 0.

(* find_mac's result is -1 or an index below the loop's bound. *)
Lemma oe1_loop_range : forall u m (f : nat) i, 0 <= i -> -1 <= TSS.find_mac_loop u m i f < i + Z.of_nat f.
Proof.
intros u m f. induction f as [|f IH]; intros i Hi; cbn [TSS.find_mac_loop].
- lia.
- lazymatch goal with |- context [if ?c then _ else _] => destruct c end.
  + lia.
  + pose proof (IH (i + 1) ltac:(lia)) as H. lia.
Qed.

Lemma oe1_off_range : forall Bx b, -1 <= onann_off Bx b < 2 ^ 31.
Proof.
intros Bx b. unfold onann_off.
lazymatch goal with |- context [if ?c then _ else _] => destruct c end; [|lia].
unfold TSS.find_mac_m.
lazymatch goal with |- context [TSS.find_mac_loop ?u ?m 0 ?f] =>
  pose proof (oe1_loop_range u m f 0 ltac:(lia)) as H;
  assert (Hf : Z.of_nat f <= 64) by (vm_compute; intros Hx; discriminate Hx) end.
lia.
Qed.

(* `blt` on the sign-extended values. *)
Lemma oe1_lts : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2^63); lia). reflexivity.
Qed.

(* The model on the two arms (OnannCutB.v onann_k_e1). *)
Lemma oe1_k_neg : forall I Fr B2 off b, off < 0 ->
  onann_k_e1 I Fr B2 off b = onann_k_fn I Fr (TW.set_S_foreign B2 1) b.
Proof.
intros I Fr B2 off b H. unfold onann_k_e1.
replace (0 <=? off) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity.
Qed.
Lemma oe1_k_pos : forall I Fr B2 off b, 0 <= off ->
  onann_k_e1 I Fr B2 off b = TSS.maybe_online_m I Fr (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1).
Proof.
intros I Fr B2 off b H. unfold onann_k_e1.
replace (0 <=? off) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

(* The register and region readers of a symbolic state (on_ack's image-B after-notice piece's, the second form for
   the st_ok a run leaves at a call). *)
Ltac oe1_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Register r of the machine state of HS, whose symbolic value is atom n, the start value of register rn (Q its
   value): the run's valuation agrees with the start valuation below atom 1024 (Elo), which reads the registers (EE). *)
Ltac oe1_kreg_of HS Elo EE r n rn Q H :=
  lazymatch type of Q with _ = ?v =>
    oe1_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n rn eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac oe1_kreg HS Elo EE r n Q H := oe1_kreg_of HS Elo EE r n r Q H.
Ltac oe1_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac oe1_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac oe1_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows of a run's start state, computed, against the bytes Zs a run may change. *)
Ltac oe1_win Hin Hx U :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
          [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U in Hx; lia |]);
  destruct Hin.
(* The model of the goal, named. *)
Ltac oe1_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
(* After a run: its valuation agrees with the start valuation E0 below atom 1024 (Hlo), and its machine state is
   named m. *)
Ltac oe1_lo HS E0 Hlo m :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  end.

Section e1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* ------------------------------------------------------------------ *)
(* 2. The entry states, bytes read off the view                         *)
(* ------------------------------------------------------------------ *)

(* g_s's payload bytes are bytes of G. *)
Lemma oe1_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONANN_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* g_s's bytes [s + 136, s + 152) are addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma oe1_ra : forall ly S (W : world segs) mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONANN_S + 136) 16.
Proof.
intros ly S W mem md HZ HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONANN_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONANN_S + TW.SZ_g_s)
  by (unfold ONANN_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The runs' valuation: the 32 registers at +0x4a0 (and at +0x4e0 after the call). *)
Definition oe1_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma oe1_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oe1_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold oe1_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

(* The symbolic state at +0x4a0 holds of the machine state there, and the run's shadow entry holds. *)
Lemma oe1_entry : forall ly S (W : world segs) regs mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (oe1_E regs) ss_oe1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E1)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OE1_Bx OE1_SH (oe1_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HSC HAR R20 R24.
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew (oe1_E regs) 20) = ONANN_S)
  by (rewrite (oe1_ew regs 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew (oe1_E regs) 24) = SHADOW_OFF)
  by (rewrite (oe1_ew regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_oe1.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  + unfold oe1_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U24.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (oe1_ra ly S W mem md HSC HAR) as HRA.
  assert (UB : U (oe1_E regs) OE1_Bx = SHADOW_OFF).
  { unfold U, OE1_Bx. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, OE1_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ OE1_Bx 20 (ONANN_S + 136) 16 ONANN_S 136 152 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* A state with no region at any pc of the listing (the `j` at +0x4e0, after maybe_online). *)
Lemma oe1_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (oe1_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The region of g_s.foreign and g_s.e1_named_us holds at any memory: bytes of G are writable everywhere. *)
Lemma oe1_rg_ok : forall E (m : word -> option byte), bv_unsigned (ew E 20) = ONANN_S ->
  region_ok segs E m oe1_rg.
Proof.
intros E m U20. unfold oe1_rg, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U20. assert (CS : ONANN_S = 6157888) by reflexivity.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONANN_S + o) G_HARNESS_B_rw).
apply oe1_inG. unfold TW.SZ_g_s. lia.
Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma oe1_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* Two views equal at a byte read the same byte. *)
Lemma oe1_mbyte_of_aview : forall H (m m' : word -> option byte) a,
  aview segs H m' a = aview segs H m a -> mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte segs (mrestrict H m') a) as [x|], (mbyte segs (mrestrict H m) a) as [y|];
  cbn [option_map] in E; [| discriminate E | discriminate E | reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A view equal on [0, 2 ^ 64) is equal everywhere (an address is read modulo 2 ^ 64). *)
Lemma oe1_aview_all : forall H (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview segs H m' a = aview segs H m a) ->
  forall a, aview segs H m' a = aview segs H m a.
Proof.
intros H m m' KV a. rewrite (aview_wrap64 segs H m' a), (aview_wrap64 segs H m a).
apply KV. apply Z.mod_pos_bound. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The cut's facts at a later memory                                *)
(* ------------------------------------------------------------------ *)

(* The world relation at a later memory of the same view on [0, 2 ^ 64). *)
Lemma oe1_tw_move : forall (W2 : world segs) (m m' : word -> option byte) X,
  gx_ok segs B TG.G_HARNESS_B ->
  tw_at TMAP_B (aview segs (w_H W2) m) X ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) m' a = aview segs (w_H W2) m a) ->
  tw_at TMAP_B (aview segs (w_H W2) m') X.
Proof.
intros W2 m m' X HGX Htw KV. apply (tw_kept_GB (aview segs (w_H W2) m)); [exact Htw|].
intros b0 n i Hbn Hi.
assert (Hg : inG TG.G_HARNESS_B (b0 + i))
  by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
apply KV. lia.
Qed.

(* a's fields at a later memory of the same view. *)
Lemma oe1_aok_move : forall (W2 : world segs) (m m' : word -> option byte) F buf b,
  (forall a, aview segs (w_H W2) m' a = aview segs (w_H W2) m a) ->
  onann_a_ok W2 m F buf b -> onann_a_ok W2 m' F buf b.
Proof.
intros W2 m m' F buf b KV (G1 & G2 & R1 & R2 & SH).
split; [|split; [|split; [|split]]].
- apply (garr8_frame segs (mrestrict (w_H W2) m) (mrestrict (w_H W2) m') _ _ G1).
  intros a _. exact (oe1_mbyte_of_aview _ _ _ a (KV a)).
- apply (garr8_frame segs (mrestrict (w_H W2) m) (mrestrict (w_H W2) m') _ _ G2).
  intros a _. exact (oe1_mbyte_of_aview _ _ _ a (KV a)).
- rewrite <- R1. apply YCbq.rdword_ext. intros i _. apply KV.
- rewrite <- R2. apply YCbq.rdword_ext. intros i _. apply KV.
- intros i Hi. rewrite KV. exact (SH i Hi).
Qed.

(* A spill slot at a later memory of the same view. *)
Lemma oe1_slot_move : forall (W2 : world segs) (m m' : word -> option byte) sp1 o v,
  (forall a, aview segs (w_H W2) m' a = aview segs (w_H W2) m a) ->
  onann_slot W2 m sp1 o v -> onann_slot W2 m' sp1 o v.
Proof.
intros W2 m m' sp1 o v KV H. unfold onann_slot in *. rewrite <- H. apply YCbq.rdword_ext. intros i _. apply KV.
Qed.

(* The cut's facts at a later memory of the same state whose view differs at most at [s + 136, s + 144) (g_s.foreign
   and g_s.e1_named_us, bytes of G in onann_wr Bw b). *)
Lemma oe1_cur_step : onann_laws B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 mem3 : word -> option byte) (md2 md3 : Model) (e : Z),
    onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 136 <= a < ONANN_S + 144) ->
       aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
    (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
    onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ly2 S2 W2
  mem2 mem3 md2 md3 e HFIX HCUR HJ3 KD GA.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & _ & HGX & _).
pose proof (onann_cur_ar B MT LAWS HFIX HCUR) as (HARc & HAR2 & _ & _ & _ & _ & Hin2 & EFA2 & _ & _ & FNG &
  HF4096 & _ & HFc & _ & Hce & Hslo & Hshi & H47 & _).
pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & Hmo & HK & HSV & HFL).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (ESTK : ONANN_STK = 9008) by reflexivity.
refine (conj HJ3 (conj He (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj _ (conj _ _)))))))).
- apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2
    mem3 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) (fun x => ONANN_S + 136 <= x < ONANN_S + 144) HARc HK KD GA).
  + intros a Hz Hc. cbv beta in Hz. exfalso. lia.
  + intros b0 m i _ _ Hz. cbv beta in Hz.
    destruct (Z_lt_le_dec (b0 + i) (ONANN_S + 140)) as [Hl | Hl].
    * apply onann_wr_foreign. unfold twb_fld, TW.A_S_foreign, TW.OFF_g_s, TB_g_s. unfold ONANN_S, TB_g_s in Hz, Hl. lia.
    * apply onann_wr_e1nu. unfold twb_fld, TW.A_S_e1_named_us, TW.OFF_g_s, TB_g_s. unfold ONANN_S, TB_g_s in Hz, Hl. lia.
  + intros a Hz _ HnG _ _. cbv beta in Hz. exfalso. apply HnG. apply oe1_inG. unfold TW.SZ_g_s. lia.
  + intros c p a _ _ Hz. cbv beta in Hz.
    destruct (Z_lt_le_dec a (ONANN_S + 140)) as [Hl | Hl].
    * apply onann_wr_foreign. unfold twb_fld, TW.A_S_foreign, TW.OFF_g_s, TB_g_s. unfold ONANN_S, TB_g_s in Hz, Hl. lia.
    * apply onann_wr_e1nu. unfold twb_fld, TW.A_S_e1_named_us, TW.OFF_g_s, TB_g_s. unfold ONANN_S, TB_g_s in Hz, Hl. lia.
- apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KD; lia.
- unfold ONANN_FBYTES in HFL |- *. rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KD; [lia|]. intros X.
  apply (FNG (F + 512 - 8 + i) ltac:(lia)). apply oe1_inG. unfold TW.SZ_g_s. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma oe1_holds : @onann_e1_stmt fx rc B MT.
Proof.
unfold onann_e1_stmt, onann_e1_at.
intros FN NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B2 ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & HSC & _ & _ & _ & _ & LAWS & MTL & _ & _ & _ & FFL & HGX & _).
pose proof HCALL as (_ & _ & _ & _ & _ & _ & _ & _ & HMON & _).
pose proof HFIX as (HJe & _ & _ & Hgp & Htp & _ & _ & _ & _ & Hwin1 & Hwin2 & _ & _ & Htw0 & _ & _ & _ & _ & _ &
  Hapart & _ & _ & _ & Hcnt2 & Hnev & _ & EF & _ & _ & _ & _).
pose proof HCUR as (HCUR0 & Htw2 & Hb2 & _ & Hk & Hgf2 & Haok & (Hs32 & Hs40) & (Hs8 & Hs0) & Hs16).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24) & R23 & R22 & R26 & R27).
pose proof (onann_cur_ar B MT LAWS HFIX HCUR0) as (HARc & HAR2 & _ & _ & EFAll & _ & Hin2 & EFA2 & _ & _ & FNG &
  HF4096 & _ & HFc & _ & Hce & Hslo & Hshi & H47 & _ & _ & _ & _ & _ & Hsp1 & Hsp132 & Hsp146).
pose proof (oe1_off_range (onann_w1 timg_B Bw b) b) as Hoff.
set (off := onann_off (onann_w1 timg_B Bw b) b) in *. clearbody off.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (CS' : ONANN_S = TB_g_s) by reflexivity.
assert (EV0 : ONANN_EV = 0) by reflexivity.
assert (EVM : MAYBEON_EV = 0) by reflexivity.
assert (ESTK : ONANN_STK = 9008) by reflexivity.
assert (EMS : MAYBEON_STK = 8416) by reflexivity.
pose proof (tw_len _ _ _ Htw0) as HLw.
pose proof (tw_len _ _ _ Htw2) as HL2.
pose proof Hb2 as (_ & d & EB2).
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
(* run 1, +0x4a0 .. +0x4ac: a0 = s + 136, a1 = its shadow address; it stops at the `blt` *)
destruct (oe1_entry ly2 S2 W2 regs2 mem2 md2 HSC HAR2 R20 R24) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (oe1_E regs2)) by (unfold oe1_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oe1_E regs2) n = YK11.getr regs2 r)
  by (intros n r Hn; exact (oe1_ew regs2 n r Hn)).
assert (U20c : bv_unsigned (ew (oe1_E regs2) 20) = ONANN_S)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof HJ1 as HJ.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ oe1_awr_rs. apply awr_ok_x_nil. }
oe1_name_md md1.
oe1_lo HS (oe1_E regs2) E1lo ms1.
(* run 1 wrote no byte *)
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta. oe1_win Hin Hx U20c. }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* +0x4ac: `blt s7, zero` on off *)
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
  assert (D23 : sv_denot EF (SOff 23 0) = Z_to_bv 64 off)
    by (cbn [sv_denot]; try rewrite (E1lo 23%nat ltac:(lia));
        rewrite (EE 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23);
  assert (U20e : bv_unsigned (ew EF 20) = ONANN_S) by (try rewrite (E1lo 20%nat ltac:(lia)); exact U20c)
end.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* off < 0: to the foreign cut +0x4e4 *)
  rewrite D23 in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (oe1_lts off 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ONANN_FN.
  { oe1_awr_rs. apply awr_ok_x_nil. }
  oe1_name_md mdT.
  oe1_lo HS (oe1_E regs2) E2lo ms2.
  (* the registers the foreign cut reads *)
  oe1_kreg HS E2lo EE (2%bv : bv 5) 2%nat R2 Y2. oe1_kreg HS E2lo EE (3%bv : bv 5) 3%nat R3 Y3.
  oe1_kreg HS E2lo EE (4%bv : bv 5) 4%nat R4 Y4. oe1_kreg HS E2lo EE (8%bv : bv 5) 8%nat R8 Y8.
  oe1_kreg HS E2lo EE (9%bv : bv 5) 9%nat R9 Y9. oe1_kreg HS E2lo EE (18%bv : bv 5) 18%nat R18 Y18.
  oe1_kreg HS E2lo EE (19%bv : bv 5) 19%nat R19 Y19. oe1_kreg HS E2lo EE (25%bv : bv 5) 25%nat R25 Y25.
  oe1_kreg HS E2lo EE (20%bv : bv 5) 20%nat R20 Y20. oe1_kreg HS E2lo EE (24%bv : bv 5) 24%nat R24 Y24.
  oe1_kreg HS E2lo EE (22%bv : bv 5) 22%nat R22 Y22. oe1_kreg HS E2lo EE (26%bv : bv 5) 26%nat R26 Y26.
  oe1_kreg HS E2lo EE (27%bv : bv 5) 27%nat R27 Y27.
  oe1_reg HS (10%bv : bv 5) (w64 (ONANN_S + 136)) Y10
    ltac:(cbn [sv_denot]; try rewrite (E2lo 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl), R20;
          unfold w64, ONANN_S, TB_g_s; vm_compute; reflexivity).
  oe1_reg HS (11%bv : bv 5) (w64 (SHADOW_OFF + (ONANN_S + 136) / 8)) Y11
    ltac:(cbn [sv_denot]; try rewrite (E2lo 20%nat ltac:(lia)); try rewrite (E2lo 24%nat ltac:(lia));
          rewrite (EE 20%nat 20%bv eq_refl), (EE 24%nat 24%bv eq_refl), R20, R24;
          unfold w64, ONANN_S, TB_g_s, SHADOW_OFF; vm_compute; reflexivity).
  (* the run wrote no byte *)
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
  { intros a Ha. rewrite <- (KA1 a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. oe1_win Hin Hx U20e. }
  assert (GA2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  pose proof (oe1_aview_all (w_H W2) mem2 (ms_mem ms2) KA2) as KV2.
  pose proof (oe1_cur_step HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly2 S2 W2 mem2 (ms_mem ms2) md2 mdT 0 HFIX HCUR0 HJ ltac:(intros a Ha _; exact (KA2 a Ha)) GA2) as CURF.
  rewrite (oe1_k_neg timg_B TF B2 off b Hc) in Hk.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FN)) mm rom) mdx) Q) end.
  apply (FN HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    B2 ly2 S2 W2 (ms_mem ms2) mdT (ms_regs ms2) HFIX).
  + unfold onann_fn_cur.
    refine (conj CURF (conj (oe1_tw_move W2 mem2 (ms_mem ms2) B2 HGX Htw2 KA2) (conj Hb2 (conj Hk (conj Hgf2
      (conj (oe1_aok_move W2 mem2 (ms_mem ms2) F buf b KV2 Haok) (conj _ (conj _ _)))))))).
    * exact (conj (oe1_slot_move W2 mem2 (ms_mem ms2) sp1 _ _ KV2 Hs32) (oe1_slot_move W2 mem2 (ms_mem ms2) sp1 _ _ KV2 Hs40)).
    * exact (conj (oe1_slot_move W2 mem2 (ms_mem ms2) sp1 _ _ KV2 Hs8) (oe1_slot_move W2 mem2 (ms_mem ms2) sp1 _ _ KV2 Hs0)).
    * exact (oe1_slot_move W2 mem2 (ms_mem ms2) sp1 _ _ KV2 Hs16).
  + exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y19 Y25))))))) (conj Y20 Y24))
      (conj Y10 (conj Y11 (conj Y22 (conj Y26 Y27))))).
- (* 0 <= off: the stores of :213-214, then maybe_online *)
  rewrite D23 in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (oe1_lts off 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
  pose proof (st_ok_pi_add_region _ _ _ oe1_rg HS ltac:(vm_compute; reflexivity)
    (oe1_rg_ok _ _ U20e) ltac:(cbn [add_cond ss_mem all_disjoint]; exact I)) as HSx.
  clear HS. rename HSx into HS.
  (* run 2, +0x4ac .. +0x4dc: the two checks, the stores at s + 136 and s + 140, a0 = s, `jal maybe_online` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { oe1_awr_rs.
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20e in Ha;
      apply oe1_inG; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_nil. }
  oe1_name_md mdW.
  oe1_lo HS (oe1_E regs2) E3lo msW.
  (* the registers at maybe_online's entry *)
  oe1_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 28424)) W1 ltac:(apply codeptr_val; assumption).
  oe1_kreg HS E3lo EE (2%bv : bv 5) 2%nat R2 W2'. oe1_kreg HS E3lo EE (3%bv : bv 5) 3%nat R3 W3'.
  oe1_kreg HS E3lo EE (4%bv : bv 5) 4%nat R4 W4'. oe1_kreg HS E3lo EE (8%bv : bv 5) 8%nat R8 W8'.
  oe1_kreg HS E3lo EE (9%bv : bv 5) 9%nat R9 W9'. oe1_kreg HS E3lo EE (18%bv : bv 5) 18%nat R18 W18'.
  oe1_kreg HS E3lo EE (19%bv : bv 5) 19%nat R19 W19'. oe1_kreg HS E3lo EE (25%bv : bv 5) 25%nat R25 W25'.
  oe1_kreg_of HS E3lo EE (10%bv : bv 5) 20%nat (20%bv : bv 5) R20 W10'.
  (* the run wrote [s + 136, s + 144) only *)
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 136 <= a < ONANN_S + 144) ->
    aview segs (w_H W2) (ms_mem msW) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite <- (KA1 a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun x => ONANN_S + 136 <= x < ONANN_S + 144) HFr); [| exact Ha | exact Hn].
    intros b0 wlo whi x Hin Hx. cbv beta. oe1_win Hin Hx U20e. }
  assert (GW : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msW) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
  clear HF HFr HG.
  (* the stored values: 0 at s + 136, 1 at s + 140 *)
  oe1_region HS 0%nat HRw.
  lazymatch type of HRw with region_ok _ ?Ex _ _ =>
    assert (U20f : bv_unsigned (ew Ex 20) = ONANN_S) by (try rewrite (E3lo 20%nat ltac:(lia)); exact U20c);
    pose proof (can_field_of_region Ex _ 20 ONANN_S _ 136 144 136 144 136 4%N (SLit 0) 0 HRw U20f ltac:(oe1_in)
      ltac:(cbn [sv_denot]; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VB0;
    pose proof (can_field_of_region Ex _ 20 ONANN_S _ 136 144 136 144 140 4%N (SLit 1) 1 HRw U20f ltac:(oe1_in)
      ltac:(cbn [sv_denot]; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VB1
  end.
  change (N.to_nat 4) with 4%nat in VB0, VB1.
  clear HRw U20f.
  set (mW := ms_mem msW) in *. set (rW := ms_regs msW) in *.
  (* the cut's facts at the call's memory *)
  pose proof (oe1_cur_step HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly2 S2 W2 mem2 mW md2 mdW 0 HFIX HCUR0 HJ KW GW) as CURW.
  pose proof CURW as (_ & _ & _ & _ & _ & _ & KCw & HSVw & HFLww).
  unfold ONANN_FBYTES in HFLww.
  pose proof (onann_cur_ar B MT LAWS HFIX CURW) as (_ & HARW & _).
  (* the world after the stores of :213 and :214 *)
  set (rd1 := fun x => if (ONANN_S + 136 <=? x) && (x <? ONANN_S + 140) then aview segs (w_H W2) mW x
                       else aview segs (w_H W2) mem2 x).
  assert (TW1 : tw_at TMAP_B rd1 (TW.set_S_foreign B2 0)).
  { rewrite onann_st_foreign.
    apply (tw_write TMAP_B (aview segs (w_H W2) mem2) rd1 B2 TW.OFF_g_s TB_g_s TW.SZ_g_s 136 4 0 TMAP_B_ok Htw2
      TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. unfold rd1. cbv beta. rewrite <- CS'.
      lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:Eb end.
      + exact (oe1_aview_of_val _ _ _ 4 _ VB0 j Hj).
      + exfalso. apply andb_false_iff in Eb.
        destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia.
    - intros x Hx Hn. unfold rd1. cbv beta. rewrite <- CS' in Hn.
      lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:Eb end; [|reflexivity].
      exfalso. apply andb_true_iff in Eb. destruct Eb as [Eb1 Eb2].
      apply Z.leb_le in Eb1. apply Z.ltb_lt in Eb2. apply Hn. lia. }
  assert (TWw : tw_at TMAP_B (aview segs (w_H W2) mW) (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1)).
  { rewrite (onann_st_e1nu (TW.set_S_foreign B2 0) 1).
    apply (tw_write TMAP_B rd1 (aview segs (w_H W2) mW) (TW.set_S_foreign B2 0) TW.OFF_g_s TB_g_s TW.SZ_g_s 140 4 1
      TMAP_B_ok TW1 TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. rewrite <- CS'. exact (oe1_aview_of_val _ _ _ 4 _ VB1 j Hj).
    - intros x Hx Hn. unfold rd1. cbv beta. rewrite <- CS' in Hn.
      lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:Eb end; [reflexivity|].
      assert (Hg : inG TG.G_HARNESS_B x).
      { destruct Hx as (o & b0 & n & Hin & Hb). pose proof (TMAP_B_in_G o b0 n Hin) as HG0.
        unfold inG. apply Exists_exists. exists (b0, n). split; [exact HG0 | unfold in_zr; cbn [fst snd]; lia]. }
      pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hg) as Hl. unfold kLowMemEnd in Hl.
      apply KW; [lia|]. intros (Xa & Xb).
      apply andb_false_iff in Eb. destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb; lia | apply Z.ltb_ge in Eb].
      apply Hn. lia. }
  (* maybe_online's premises *)
  assert (NSP : spZ rW = sp1) by (unfold spZ; rewrite W2'; unfold w64; apply unsigned_lit_small; lia).
  assert (EBR : BASE + 28424 = 0x881a8) by (vm_compute; reflexivity).
  assert (Pret : YK0s.ret_ok (YK11.getr rW 1))
    by (rewrite W1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
  assert (Pra4 : 4096 <= raZ rW) by (unfold raZ; rewrite W1, EBR, unsigned_lit_small by lia; lia).
  assert (Pgp : YK11.getr rW 3 = w64 (as_gp B)) by (rewrite W3'; exact Hgp).
  assert (Ptp : YK11.getr rW 4 = w64 (as_tp B)) by (rewrite W4'; exact Htp).
  assert (Pa0 : YK11.getr rW 10 = w64 MAYBEON_S) by exact W10'.
  assert (Psp16 : spZ rW mod 16 = 0).
  { rewrite NSP. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
    replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
  assert (Pwin1 : sp0 - STK <= spZ rW - MAYBEON_STK) by (rewrite NSP; lia).
  assert (Pwin2 : spZ rW <= sp0) by (rewrite NSP; lia).
  assert (LX1 : length (TW.set_S_foreign B2 0) = Z.to_nat TW.W_LEN)
    by (rewrite onann_st_foreign; apply onann_upd_len; [exact HL2 | unfold TW.OFF_g_s; lia |
                                                        unfold TW.OFF_g_s, TW.W_LEN; lia]).
  assert (Pgf : TW.g_fail_next (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1) <= 1).
  { rewrite (onann_st_e1nu (TW.set_S_foreign B2 0) 1),
      (onann_gfn_upd (TW.set_S_foreign B2 0) (TW.OFF_g_s + 140) 4 1 LX1
         ltac:(left; unfold TW.OFF_g_s, TW.SZ_g_s; lia)).
    rewrite (onann_st_foreign B2 0),
      (onann_gfn_upd B2 (TW.OFF_g_s + 136) 4 0 HL2 ltac:(left; unfold TW.OFF_g_s, TW.SZ_g_s; lia)).
    exact Hgf2. }
  assert (Pmod : TSS.maybe_online_m timg_B TF (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1) = Some (Bw', tt))
    by (rewrite <- (oe1_k_pos timg_B TF B2 off b Hc); exact Hk).
  assert (Ptf : trans_tframe_at B ly2 S2 W2 mW rW MAYBEON_STK TF)
    by exact (onann_tf_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
      Bw' pos sp1 F ly2 S2 W2 mW mdW 0 rW MAYBEON_STK HFIX CURW ltac:(rewrite NSP; lia) ltac:(rewrite NSP; lia)).
  assert (Prom : trans_rom_view_rd W2 mW)
    by exact (onann_rom_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
      Bw' pos sp1 F ly2 S2 W2 mW mdW 0 HFIX CURW).
  assert (Pap : maybeon_apart TF (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1))
    by (rewrite EB2; exact (onann_apart_mo TF Bw b d HLw Hapart)).
  assert (Pcnt : count_cid MAYBEON_CID (frames S2) < fs_frames MAYBEON_CID).
  { rewrite Hfrs. cbn [count_cid]. change MAYBEON_CID with SENDCTL_CID.
    change (ONANN_CID =? SENDCTL_CID) with false. cbv iota. lia. }
  assert (Pnev : st_nev S + (k + 0) + MAYBEON_EV <= EV_MAX) by (rewrite EVM; rewrite EV0 in Hnev; lia).
  (* +0x4dc: maybe_online, in the same G journal *)
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_maybe_online) rg mm mdx) Q) end.
  eapply SRr_bind.
  { exact (HMON fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mW mdW (k + 0) rW TF
      (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1) Bw' HJ Pret Pra4 Pgp Ptp Pa0 Psp16 Pwin1 Pwin2 TWw Pgf Pmod
      Ptf Prom Pap Pcnt Pnev). }
  intros W3 c3 _ HPOST.
  unfold transport_maybeon_post, transport_cg_post in HPOST.
  destruct HPOST as (ly3 & S3 & regs5 & mem5 & md6 & e' & -> & He' & HJ6 & HP6 & Hfr6 & Hperm6 & HK6 & Hmo6 & Htw6 &
    Hgf6).
  rewrite NSP in HK6.
  (* the state maybe_online returned: the cut's facts there *)
  assert (ELF3 : ly_F ly3 = ly_F lyc).
  { pose proof HJe as (_ & _ & (memSe & HJei & _) & _). pose proof HJei as (_ & Hlyc & _).
    pose proof HJ6 as (_ & _ & (memS6 & HJ6i & _) & _). pose proof HJ6i as (_ & Hly3 & _).
    pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
    rewrite E3, Ec. reflexivity. }
  destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mW mdW ONANN_CID pos F
    (flag_addr lyc ONANN_CID pos) HARW Hfrs Hbl2 HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
  assert (K5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem5 (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b)).
  { assert (Hce1 : YM05.alloc_ceiling <= spZ regs - ONANN_STK) by lia.
    assert (Hhi1 : spZ regs <= 2 ^ 64) by lia.
    apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mW W3 mem5
      (spZ regs - ONANN_STK) (spZ regs) (sp1 - MAYBEON_STK) sp1 (onann_wr Bw b)
      (maybeon_wr (TW.set_S_e1_named_us (TW.set_S_foreign B2 0) 1)) (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))
      Hce1 Hhi1 EFAll ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) Hbl2 N1 N3 KCw HK6).
    - lia.
    - lia.
    - intros a Ha. left. rewrite EB2 in Ha. exact (onann_wr_mo Bw b d a HLw Ha). }
  assert (HSV5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem5) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
  { apply Forall_forall. intros o Hin. cbv beta.
    pose proof (proj1 (Forall_forall _ _) HSVw o Hin) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (L1 & _). apply L1; lia. }
  assert (HFL5 : rdword (aview segs (w_H W3) mem5) (F + 512 - 8) = Some (flag_addr lyc ONANN_CID pos)).
  { rewrite <- HFLww. apply YCbq.rdword_ext. intros i Hi. destruct HK6 as (_ & _ & _ & L4 & _).
    apply (L4 ONANN_CID pos (F + 512 - 8 + i) Hin2).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes ONANN_CID) with 512. lia.
    - intros Hw. exact (FNG (F + 512 - 8 + i) ltac:(lia) (onann_mo_wr_G _ _ Hw)). }
  replace (k + 0 + e') with (k + e') in HJ6 by lia.
  assert (CUR5 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem5 md6 e').
  { unfold onann_cur.
    refine (conj HJ6 (conj _ (conj _ (conj _ (conj ELF3 (conj _ (conj K5 (conj HSV5 _)))))))).
    - rewrite EV0. rewrite EVM in He'. lia.
    - rewrite Hfr6. exact Hfrs.
    - exact (Permutation_trans Hperm6 Hperm).
    - exact (mo_le_trans MT MTL Sc S2 S3 0 0 Hmo Hmo6).
    - unfold ONANN_FBYTES. exact HFL5. }
  (* the registers the release reads, at maybe_online's return *)
  assert (Q2 : YK11.getr regs5 2 = w64 sp1) by exact (eq_trans (HP6 2 ltac:(hnf; lia)) W2').
  assert (Q3 : YK11.getr regs5 3 = YK11.getr regs 3) by exact (eq_trans (HP6 3 ltac:(hnf; lia)) W3').
  assert (Q4 : YK11.getr regs5 4 = YK11.getr regs 4) by exact (eq_trans (HP6 4 ltac:(hnf; lia)) W4').
  assert (Q8 : YK11.getr regs5 8 = w64 (spZ regs)) by exact (eq_trans (HP6 8 ltac:(hnf; lia)) W8').
  assert (Q9 : YK11.getr regs5 9 = w64 sp1) by exact (eq_trans (HP6 9 ltac:(hnf; lia)) W9').
  assert (Q18 : YK11.getr regs5 18 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HP6 18 ltac:(hnf; lia)) W18').
  assert (Q19 : YK11.getr regs5 19 = w64 F) by exact (eq_trans (HP6 19 ltac:(hnf; lia)) W19').
  assert (Q25 : YK11.getr regs5 25 = w64 F) by exact (eq_trans (HP6 25 ltac:(hnf; lia)) W25').
  (* +0x4e0 .. +0x61c: `j`, to the release cut *)
  rewrite W1.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OE1_RET)) mm rom) mdx) Q) end.
  clear HS SHOK.
  pose proof (oe1_entry0 W3 regs5 mem5 OE1_RET) as HS.
  assert (SHOK : sh_ok segs OE1_BJ [] (oe1_E regs5) (mrestrict (w_H W3) mem5)) by constructor.
  assert (HEIj : img_env VAL A_LIM (oe1_E regs5)) by (unfold oe1_E; apply Eimg_env).
  assert (EEj : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oe1_E regs5) n = YK11.getr regs5 r)
    by (intros n r Hn; exact (oe1_ew regs5 n r Hn)).
  paj_run_to_tok RUNTO HS HJ6 SHOK OE1_B0 ONANN_NREL.
  { oe1_awr_rs. apply awr_ok_x_nil. }
  oe1_name_md mdJ.
  oe1_lo HS (oe1_E regs5) EJlo msJ.
  oe1_kreg HS EJlo EEj (2%bv : bv 5) 2%nat Q2 Z2. oe1_kreg HS EJlo EEj (3%bv : bv 5) 3%nat Q3 Z3.
  oe1_kreg HS EJlo EEj (4%bv : bv 5) 4%nat Q4 Z4. oe1_kreg HS EJlo EEj (8%bv : bv 5) 8%nat Q8 Z8.
  oe1_kreg HS EJlo EEj (9%bv : bv 5) 9%nat Q9 Z9. oe1_kreg HS EJlo EEj (18%bv : bv 5) 18%nat Q18 Z18.
  oe1_kreg HS EJlo EEj (19%bv : bv 5) 19%nat Q19 Z19. oe1_kreg HS EJlo EEj (25%bv : bv 5) 25%nat Q25 Z25.
  assert (KJ : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msJ) a = aview segs (w_H W3) mem5 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. oe1_win Hin Hx EJlo. }
  assert (GJ : forall a, apresent (w_H W3) mem5 a -> apresent (w_H W3) (ms_mem msJ) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (oe1_cur_step HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly3 S3 W3 mem5 (ms_mem msJ) md6 mdJ e' HFIX CUR5 HJ6 ltac:(intros a Ha _; exact (KJ a Ha)) GJ) as CURJ.
  (* the release cut *)
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_NREL)) mm rom) mdx) Q) end.
  apply (NREL HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly3 S3 W3 (ms_mem msJ) mdJ e' (ms_regs msJ) HFIX).
  + exact (conj CURJ (conj (oe1_tw_move W3 mem5 (ms_mem msJ) Bw' HGX Htw6 KJ) Hgf6)).
  + exact (conj Z2 (conj Z3 (conj Z4 (conj Z8 (conj Z9 (conj Z18 (conj Z19 Z25))))))).
Qed.
End e1.

(* The e1 piece of the walk of on_announce (OnannCutB.v onann_e1_stmt), at every machine, run ceiling, record and
   meter. *)
Lemma onann_e1_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onann_e1_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@oe1_holds fx rc B MT). Qed.
