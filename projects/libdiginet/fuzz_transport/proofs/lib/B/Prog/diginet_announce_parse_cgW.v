(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1124 of its 1216 lines of code are new or changed and 1047 lines of the source are left out. *)
(* diginet_announce_parse_cgW: Theorem frame_diginet_announce_parse_cg_holds, the statement
   frame_diginet_announce_parse_cg_holds_stmt of lib/B/Prog/diginet_announce_parse_cg.v for every record B, for
   diginet_announce_parse of fuzz_frame.asan-ubsan (entry 0x82c44 = frameb_sigma
   FB_diginet_announce_parse, AF_diginet_announce_parse = 0x2f04 of lib/B/Prog/FrameBList.v).
   The walk runs the position-abstract engine with its shadow tokens (lib/B/Prog/FrameBPaLib.v paj_run_tok) in the
   caller's journal itself, so each byte a run or a callee writes is one the caller lets it write: the 32 bytes of
   the frame lie in the caller's stack window, the bytes of ap are frame_twr_ok's.
     run a  +0x000 .. +0x038  the frame and the four saves, s0 = ap, the tests f = 0 and ap = 0 and the UBSan test of
                              f's alignment (the engine decides them from the facts f >= 8, ap >= 8, f mod 8 = 0),
                              the shadow base from its GOT word into a2;
     run b  +0x038 .. +0x0c8  the check of f + 30 (a token of f's 64 addressable bytes), cmd, `bne` on cmd & 0xfe
                              (split; its taken arm returns -9), the check of f + 40, `bgeu` on the length (split; its
                              arm not taken returns -4), s1 = f + 32, s2 = its shadow address, the checks of f + 32
                              and ap + 24, the UBSan test of ap's alignment, body, up to `sd a1,24(s0)` at +0x0c8,
                              where the engine stops: ap's bytes are not yet a region, so the runs of -9 and -4
                              store nothing;
     run c  +0x0c8 .. +0x0f4  with ap + 24 .. ap + 40 added as a writable region: the two stores, the check of
                              ap + 32, the UBSan tests of body = 0 and body + 15 (decided from body's facts), and
                              `jal copy_strz` with dst = ap, src = body + 15;
     call 1                   copy_strz's leaf statement (frame_leaf_wr_at), through CanLeafb.v can_leafb_journal;
     run d  +0x0f8 .. +0x118  from a fresh state: the shadow byte of f + 32 (0, a region), body again, the UBSan tests
                              of body = 0 and body + 24, `jal copy_strz` with dst = ap + 10, src = body + 24;
     call 2                   as call 1;
     run e  +0x11c .. +0x138  a0 = 0, the four reloads, `addi sp,sp,32`, the `ret`.
   Each run keeps every byte outside its writable regions and each call every byte outside its stack window and
   its field, so the call keeps every byte outside [sp - 32 - ESTACK, sp) and frame_anp_wr ap (acall_kept). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib DgnTransportBCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg CanKit CanLeafb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit AsanKA TransportFevt copy_strz_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_announce_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require copy_strz_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FFv := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TransportFevt.
Module LCZ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.copy_strz_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

Definition AA (k : Z) : Z := AF_diginet_announce_parse + k.
(* No shadow read (runs a, d, e), and the shadow band of the token runs b and c. *)
Definition ANP_B0 : Z * Z := (0, 0).
Definition ANP_Bsp : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* run a, at the entry: the registers as atoms 0 .. 31, the shadow base as atom 32; the frame, the shadow base's GOT
   word (object 1) and its cell (object 14). *)
Definition anp_facts_a : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 65) 3);
           (11%nat, mkAF 8 (2 ^ 47 - 41) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_anp_a : sstate :=
  mkSS AF_diginet_announce_parse sr_atoms [stack_region 32; got_regionP; bcell_regionP 32] None anp_facts_a.

(* run b, at +0x038: s0 = ap (atom 8), a0 = f (atom 10), a2 = the shadow base (atom 12); atoms 32 .. 34 the byte cmd,
   body and the length of bb; atoms 35 .. 38 the entry values of s2, s1, s0, ra, which the frame holds. *)
Definition anp_rg_sv : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0));
     YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0))].
Definition anp_rg_f : YP09.region :=
  YP09.mkRegion (Some 10%nat) 30 48 0 0
    [YP09.mkChunk 30 (CVal 1 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
     YP09.mkChunk 40 (CVal 8 (SOff 34 0))].
(* run c adds ap + 24 .. ap + 40 as a writable region. *)
Definition anp_rg_ap : YP09.region := YP09.mkRegion (Some 8%nat) 24 40 24 40 [].
Definition anp_SH : list shent := [mkSHE 10 0 64; mkSHE 8 0 40].
(* body (atom 33) has no fact here: an empty body may be any value; the walk adds 1 <= body <= 2 ^ 47 after the
   length test at +0x078, where trans_src_ok places the body. *)
Definition anp_facts_b : facts :=
  mkFacts [(8%nat, mkAF 8 (2 ^ 47 - 41) 3); (10%nat, mkAF 8 (2 ^ 47 - 65) 3);
           (12%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0);
           (34%nat, mkAF 0 (2 ^ 47) 0)] [] [].
Definition ss_anp_b : sstate := mkSS (AA 0x38) sr_atoms [anp_rg_sv; anp_rg_f] None anp_facts_b.

(* run d, at +0x0f8: s1 = f + 32 (atom 9), s2 = its shadow address (atom 18); atom 32 body. *)
Definition anp_rg_sh2 : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition anp_rg_f2 : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition ss_anp_d : sstate :=
  mkSS (AA 0xf8) sr_atoms [anp_rg_sh2; anp_rg_f2] None (mkFacts [(32%nat, mkAF 1 (2 ^ 47) 0)] [] []).

(* run e, at +0x11c: atoms 32 .. 35 the entry values of s2, s1, s0, ra, which the frame holds. *)
Definition anp_rg_sv3 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 32 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
     YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0))].
Definition ss_anp_e : sstate := mkSS (AA 0x11c) sr_atoms [anp_rg_sv3] None (mkFacts [] [] []).

Module SYP0l := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.
(* H : the value v of register r in the machine state of the symbolic state HS, its symbolic value computed and then
   shown equal to v by tac. *)
Ltac anp_reg HS r v H tac :=
  lazymatch type of HS with
  | SYP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* HR : region i of the symbolic state HS, at the machine state's memory. *)
Ltac anp_region HS i HR :=
  lazymatch type of HS with
  | SYP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac anp_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]; anp_ro_rec ].
Ltac anp_awr_norm := lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
Ltac anp_awr_ro := anp_awr_norm; anp_ro_rec.
Ltac anp_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the callee-saved registers no instruction of the function writes *)
Definition anp_kregs : list (bv 5) := map (Z_to_bv 5) [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Module LStp := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Step.
(* the register of anp_kregs that is the image of the number n *)
Ltac anp_kin n := unfold anp_kregs; apply in_map_iff; exists n; split;
  [apply bv_eq; vm_compute; reflexivity | cbn [In]; repeat (first [left; reflexivity | right])].

(* A fact held for later: lia does not look inside it (the body's facts hold only once the length test places it). *)
Definition anp_hold (P : Prop) : Prop := P.

Section anpw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Variable B : asyms.

(* The environments of the five runs. *)
Definition anp_Ea (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).
Definition anp_Eb (regs regs0 : bvmap 5 word) (cmd body len : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 cmd; w64 body; w64 len; YK11.getr regs0 18; YK11.getr regs0 9;
                                     YK11.getr regs0 8; YK11.getr regs0 1]).
Definition anp_Ed (regs : bvmap 5 word) (body : Z) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 body]).
Definition anp_Ee (regs regs0 : bvmap 5 word) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [YK11.getr regs0 18; YK11.getr regs0 9; YK11.getr regs0 8; YK11.getr regs0 1]).

Lemma anp_ew_x : forall (regs : bvmap 5 word) extra j, (32 + j < A_TEXT)%nat ->
  ew (Eimg (PI := PI_transportb) (Ereg regs extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.

Lemma anp_vals : VAL (A_OBJ 1) = AsanCells.GOT_CELL_K /\ VAL (A_OBJ 95) = AsanCells.CELL_K /\
  VAL A_TEXT + AF_diginet_announce_parse = transportb_sigma TB_diginet_announce_parse /\
  VAL A_TEXT + AF_copy_strz = transportb_sigma TB_copy_strz /\ transportb_sigma TB_copy_strz = LCZ.COPY_STRZ.
Proof. vm_compute. repeat split. Qed.

Lemma anp_u64 : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

(* The symbolic state of run a holds at the entry. *)
Lemma anp_entry_a : forall ly S (W : world segs) regs mem md f ap,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 ap ->
  8 <= f <= 2 ^ 47 - 65 -> f mod 8 = 0 -> 8 <= ap <= 2 ^ 47 - 41 -> ap mod 8 = 0 ->
  st_ok_pi segs VAL (anp_Ea regs) ss_anp_a
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_announce_parse)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md f ap HCELLS HAR Hpres Hsp Hsp16 R10 R11 Hf Hf8 Hap Hap8.
  rewrite restrict_mkst_fx. unfold ss_anp_a.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct anp_vals as (V1 & V14 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) AsanCells.CELL_K = Some AsanCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold AsanCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) AsanCells.GOT_CELL_K = Some AsanCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold AsanCells.CELL_K; lia | exact (CH _ I2)]).
  set (E := anp_Ea regs).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (unfold E, anp_Ea; rewrite (can_ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = w64 f) by (unfold E, anp_Ea; rewrite (can_ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
  assert (E11 : ew E 11 = w64 ap) by (unfold E, anp_Ea; rewrite (can_ew_Eimg_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
  assert (E32 : ew E 32 = w64 SHADOW_OFF) by (unfold E, anp_Ea; exact (anp_ew_x regs _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (unfold E, anp_Ea; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E14 : ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95))) by (unfold E, anp_Ea; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold AsanCells.GOT_CELL_K; lia).
  assert (R14 : 0 <= VAL (A_OBJ 95) < 2 ^ 47) by (rewrite V14; unfold AsanCells.CELL_K; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold stack_region, got_regionP, bcell_regionP, region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
      [cbn [sv_denot]; rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V1, V14. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E14) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r, V14. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E14) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V14. unfold AsanCells.GOT_CELL_K, AsanCells.CELL_K.
    repeat split; first [exact I | lia].
  - unfold anp_facts_a, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, !anp_u64 by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Ltac anp_rng64 x := let Hrr := fresh "Hrr" in pose proof (bv_unsigned_in_range 64 x) as Hrr;
  change (bv_modulus 64) with (2 ^ 64) in Hrr; exact Hrr.

(* The symbolic state of run b holds at +0x038. *)
Lemma anp_entry_b : forall (W : world segs) (regs1 regs0 : bvmap 5 word) mem (sp1 f ap cmd body len : Z),
  YK11.getr regs1 2 = w64 sp1 -> YK11.getr regs1 8 = w64 ap -> YK11.getr regs1 10 = w64 f ->
  YK11.getr regs1 12 = w64 SHADOW_OFF ->
  0 <= sp1 -> sp1 + 32 <= 2 ^ 47 ->
  8 <= f <= 2 ^ 47 - 65 -> f mod 8 = 0 -> 8 <= ap <= 2 ^ 47 - 41 -> ap mod 8 = 0 ->
  f + 48 <= sp1 \/ sp1 + 32 <= f + 30 ->
  0 <= cmd < 256 -> 0 <= body < 2 ^ 64 -> 0 <= len <= 2 ^ 47 ->
  val_mem segs (mrestrict (w_H W) mem) (f + 30) 1 cmd ->
  val_mem segs (mrestrict (w_H W) mem) (f + 32) 8 body ->
  val_mem segs (mrestrict (w_H W) mem) (f + 40) 8 len ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 0) 8 (bv_unsigned (YK11.getr regs0 18)) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 8) 8 (bv_unsigned (YK11.getr regs0 9)) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 16) 8 (bv_unsigned (YK11.getr regs0 8)) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 24) 8 (bv_unsigned (YK11.getr regs0 1)) ->
  st_ok_pi segs VAL (anp_Eb regs1 regs0 cmd body len) ss_anp_b
    (restrict (w_H W) (@YK11.mkst fx regs1 (Z_to_bv 64 (BASE + AA 0x38)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs1 regs0 mem sp1 f ap cmd body len R2 R8 R10 R12 Hsp0 Hsp1 Hf Hf8 Hap Hap8 Hdis Hcmd Hbody Hlen
    Vc Vb Vl S0 S8 S16 S24.
  rewrite restrict_mkst_fx. unfold ss_anp_b.
  set (E := anp_Eb regs1 regs0 cmd body len).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2; apply anp_u64; lia).
  assert (U8 : bv_unsigned (ew E 8) = ap)
    by (unfold E, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat regs1 _ 8 8%bv eq_refl), R8; apply anp_u64; lia).
  assert (U10 : bv_unsigned (ew E 10) = f)
    by (unfold E, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat regs1 _ 10 10%bv eq_refl), R10; apply anp_u64; lia).
  assert (U12 : bv_unsigned (ew E 12) = SHADOW_OFF)
    by (unfold E, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat regs1 _ 12 12%bv eq_refl), R12; apply anp_u64;
        unfold SHADOW_OFF; lia).
  assert (E32 : ew E 32 = w64 cmd) by (unfold E, anp_Eb; exact (anp_ew_x regs1 _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew E 33 = w64 body) by (unfold E, anp_Eb; exact (anp_ew_x regs1 _ 1 ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew E 34 = w64 len) by (unfold E, anp_Eb; exact (anp_ew_x regs1 _ 2 ltac:(unfold A_TEXT; lia))).
  assert (E35 : ew E 35 = YK11.getr regs0 18) by (unfold E, anp_Eb; exact (anp_ew_x regs1 _ 3 ltac:(unfold A_TEXT; lia))).
  assert (E36 : ew E 36 = YK11.getr regs0 9) by (unfold E, anp_Eb; exact (anp_ew_x regs1 _ 4 ltac:(unfold A_TEXT; lia))).
  assert (E37 : ew E 37 = YK11.getr regs0 8) by (unfold E, anp_Eb; exact (anp_ew_x regs1 _ 5 ltac:(unfold A_TEXT; lia))).
  assert (E38 : ew E 38 = YK11.getr regs0 1) by (unfold E, anp_Eb; exact (anp_ew_x regs1 _ 6 ltac:(unfold A_TEXT; lia))).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold anp_rg_sv, anp_rg_f, region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U2, ?U10.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ sp1 0 8 (SOff 35 0) (bv_unsigned (YK11.getr regs0 18)));
          [cbn [sv_denot]; rewrite E35, Z.add_0_r; reflexivity | anp_rng64 (YK11.getr regs0 18) | zside | exact S0].
      * apply (chunk_ok_val segs E _ sp1 8 8 (SOff 36 0) (bv_unsigned (YK11.getr regs0 9)));
          [cbn [sv_denot]; rewrite E36, Z.add_0_r; reflexivity | anp_rng64 (YK11.getr regs0 9) | zside | exact S8].
      * apply (chunk_ok_val segs E _ sp1 16 8 (SOff 37 0) (bv_unsigned (YK11.getr regs0 8)));
          [cbn [sv_denot]; rewrite E37, Z.add_0_r; reflexivity | anp_rng64 (YK11.getr regs0 8) | zside | exact S16].
      * apply (chunk_ok_val segs E _ sp1 24 8 (SOff 38 0) (bv_unsigned (YK11.getr regs0 1)));
          [cbn [sv_denot]; rewrite E38, Z.add_0_r; reflexivity | anp_rng64 (YK11.getr regs0 1) | zside | exact S24].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ f 30 1 (SOff 32 0) cmd);
          [cbn [sv_denot]; rewrite E32, anp_u64, Z.add_0_r by lia; reflexivity | zside | zside | exact Vc].
      * apply (chunk_ok_val segs E _ f 32 8 (SOff 33 0) body);
          [cbn [sv_denot]; rewrite E33, anp_u64, Z.add_0_r by lia; reflexivity | zside | zside | exact Vb].
      * apply (chunk_ok_val segs E _ f 40 8 (SOff 34 0) len);
          [cbn [sv_denot]; rewrite E34, anp_u64, Z.add_0_r by lia; reflexivity | zside | zside | exact Vl].
  - apply pairwise_disjoint_of_extents.
    unfold anp_rg_sv, anp_rg_f, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold anp_facts_b, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U10, U12, E32, E34, !anp_u64 by lia.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The symbolic state of run d holds at +0x0f8. *)
Lemma anp_entry_d : forall (W : world segs) (regs : bvmap 5 word) mem (f body : Z),
  YK11.getr regs 9 = w64 (f + 32) -> YK11.getr regs 18 = w64 (SHADOW_OFF + (f + 32) / 8) ->
  8 <= f <= 2 ^ 47 - 65 -> 1 <= body <= 2 ^ 47 ->
  f + 40 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= f + 32 ->
  val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + (f + 32) / 8 + 0) 1 0 ->
  val_mem segs (mrestrict (w_H W) mem) (f + 32 + 0) 8 body ->
  st_ok_pi segs VAL (anp_Ed regs body) ss_anp_d
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AA 0xf8)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem f body R9 R18 Hf Hbody Hdis Vs Vb.
  rewrite restrict_mkst_fx. unfold ss_anp_d.
  set (E := anp_Ed regs body).
  assert (Hq : 0 <= (f + 32) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (U9 : bv_unsigned (ew E 9) = f + 32)
    by (unfold E, anp_Ed; rewrite (can_ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), R9; apply anp_u64; lia).
  assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + (f + 32) / 8)
    by (unfold E, anp_Ed; rewrite (can_ew_Eimg_Ereg_nat regs _ 18 18%bv eq_refl), R18; apply anp_u64;
        unfold SHADOW_OFF; lia).
  assert (E32 : ew E 32 = w64 body) by (unfold E, anp_Ed; exact (anp_ew_x regs _ 0 ltac:(unfold A_TEXT; lia))).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold anp_rg_sh2, anp_rg_f2, region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9, ?U18.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ _ 0 1 (SLit 0) 0); [reflexivity | zside | zside | exact Vs].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ _ 0 8 (SOff 32 0) body);
        [cbn [sv_denot]; rewrite E32, anp_u64, Z.add_0_r by lia; reflexivity | zside | zside | exact Vb].
  - apply pairwise_disjoint_of_extents.
    unfold anp_rg_sh2, anp_rg_f2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, anp_u64 by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The symbolic state of run e holds at +0x11c. *)
Lemma anp_entry_e : forall (W : world segs) (regs regs0 : bvmap 5 word) mem (sp1 : Z),
  YK11.getr regs 2 = w64 sp1 -> 0 <= sp1 -> sp1 + 32 <= 2 ^ 47 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 0) 8 (bv_unsigned (YK11.getr regs0 18)) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 8) 8 (bv_unsigned (YK11.getr regs0 9)) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 16) 8 (bv_unsigned (YK11.getr regs0 8)) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 24) 8 (bv_unsigned (YK11.getr regs0 1)) ->
  st_ok_pi segs VAL (anp_Ee regs regs0) ss_anp_e
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AA 0x11c)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs regs0 mem sp1 R2 Hsp0 Hsp1 S0 S8 S16 S24.
  rewrite restrict_mkst_fx. unfold ss_anp_e.
  set (E := anp_Ee regs regs0).
  assert (U2 : bv_unsigned (ew E 2) = sp1)
    by (unfold E, anp_Ee; rewrite (can_ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl), R2; apply anp_u64; lia).
  assert (E32 : ew E 32 = YK11.getr regs0 18) by (unfold E, anp_Ee; exact (anp_ew_x regs _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew E 33 = YK11.getr regs0 9) by (unfold E, anp_Ee; exact (anp_ew_x regs _ 1 ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew E 34 = YK11.getr regs0 8) by (unfold E, anp_Ee; exact (anp_ew_x regs _ 2 ltac:(unfold A_TEXT; lia))).
  assert (E35 : ew E 35 = YK11.getr regs0 1) by (unfold E, anp_Ee; exact (anp_ew_x regs _ 3 ltac:(unfold A_TEXT; lia))).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold anp_rg_sv3, region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val segs E _ sp1 0 8 (SOff 32 0) (bv_unsigned (YK11.getr regs0 18)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | anp_rng64 (YK11.getr regs0 18) | zside | exact S0].
    + apply (chunk_ok_val segs E _ sp1 8 8 (SOff 33 0) (bv_unsigned (YK11.getr regs0 9)));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; reflexivity | anp_rng64 (YK11.getr regs0 9) | zside | exact S8].
    + apply (chunk_ok_val segs E _ sp1 16 8 (SOff 34 0) (bv_unsigned (YK11.getr regs0 8)));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity | anp_rng64 (YK11.getr regs0 8) | zside | exact S16].
    + apply (chunk_ok_val segs E _ sp1 24 8 (SOff 35 0) (bv_unsigned (YK11.getr regs0 1)));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r; reflexivity | anp_rng64 (YK11.getr regs0 1) | zside | exact S24].
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* What the walk leaves at the `ret`, as the statement's post. *)
Variable MT : ameter_ops.

Lemma anp_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ap cmd body bb aj
    (regsF : bvmap 5 word) memF mdF,
  AR_laws segs B -> ameter_laws MT ->
  @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k ->
  sp0 - STK <= spZ regs - TRANS_ANP_STK -> spZ regs <= sp0 ->
  decode_in_fake lyc Sc ap 40 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - TRANS_ANP_STK <= x < spZ regs) -> ~ trans_anp_wr ap x ->
     aview segs (w_H W) memF x = aview segs (w_H W) memc x) ->
  aregs_preserved regs regsF ->
  YK0s.ret_ok (YK11.getr regs 1) -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  YK11.getr regsF 10 = w64 (ann_code cmd (Z.of_nat (length bb))) ->
  garr8 segs (mrestrict (w_H W) memF) ap (trans_anp_bytes cmd body bb aj) ->
  @trans_anp_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs ap cmd body bb aj W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) memF (YK11.seg_rom segs)) mdF).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ap cmd body bb aj regsF memF mdF
    LAWS MTL HJ0 HJF Hlo Hhi Hfake HK HP Hret R1 R10 HG.
  pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & _).
  pose proof HJF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Hfake as (cid & pos & Hin & Hfa1 & Hfa2).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfapp).
  assert (HFS : TRANS_ANP_STK = 4128) by reflexivity.
  assert (HE : forall x, trans_anp_wr ap x -> frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid)
    by (intros x Hx; unfold trans_anp_wr in Hx; lia).
  assert (Hpc : v_jalr (YK11.getr regsF 1) 0 = YK11.getr regs 1) by (rewrite R1; exact Hret).
  unfold trans_anp_post, decode_cg_post.
  exists lyc, Sc, regsF, memF, mdF, 0.
  split; [rewrite Hpc; reflexivity|].
  split; [unfold TRANS_ANP_EV; lia|].
  split; [rewrite Z.add_0_r; exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { unfold acall_kept.
    split. { intros a Ha Hw. apply HK; [lia | exact Hw | intros Hx; pose proof (HE a Hx); lia]. }
    split.
    { intros b m i Hb Hi Hn.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbc & _).
      apply HK; [lia | lia | exact Hn]. }
    split.
    { intros a Hi Hns Herr. pose proof (transportb_segs_low a Hi) as Hl. apply HK; [lia | lia |].
      intros Hx. exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin (HE a Hx) Hi). }
    split.
    { intros cid' pos' a Hin' Hr Hn.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid' pos' HAR Hin') as (Hg0 & _ & _).
      destruct (frame_zone segs B LAWS lyc Sc W memc mdc cid' pos' a HAR Hin' Hr) as (Hlt & Hz).
      apply HK; [destruct Hz as [(Hz & _) | Hz]; lia | lia | exact Hn]. }
    split.
    { intros a Ha Hw Hp. eapply apresent_transfer; [lia | intros Him; pose proof (transportb_segs_low a Him); lia | | exact Hp].
      apply HK; [lia | exact Hw | intros Hx; pose proof (HE a Hx); lia]. }
    intros a Ha. apply HpresF. lia. }
  split; [apply (mo_le_refl MT MTL)|].
  split; [exact R10 | exact HG].
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Bytes, frames and registers                                       *)
(* ------------------------------------------------------------------ *)

Lemma anp_kept_of : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview segs H m' a = aview segs H m a.
Proof.
  intros E rs H m m' P HF HP a Ha Hn. apply (aview_eq_of segs). apply HF.
  rewrite unsigned_lit_small by lia. intros Hw. exact (Hn (HP a Hw)).
Qed.

Lemma anp_ra_kept : forall (H : word -> bool) (m m' : word -> option byte) a n,
  (forall x, a <= x < a + n -> aview segs H m' (shadow_of_addr SHADOW_OFF x) = aview segs H m (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H m') SHADOW_OFF a n.
Proof. intros H m m' a n Hk Hr x Hx. destruct (Hr x Hx) as (s & Hs & Hok). exists s. rewrite (Hk x Hx). auto. Qed.

Lemma anp_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) p l,
  garr8 segs (mrestrict H m) p l ->
  (forall x, p <= x < p + Z.of_nat (length l) -> aview segs H m' x = aview segs H m x) ->
  garr8 segs (mrestrict H m') p l.
Proof.
  intros H m m' p l HG Hk. apply (garr8_frame segs _ _ p l HG). intros a Ha. apply (can_mbyte_of_aview (segs := segs)). exact (Hk a Ha).
Qed.

Lemma anp_shadow_range : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44.
Proof.
  intros x Hx. unfold shadow_of_addr. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma anp_env_agree : forall (regs : bvmap 5 word) extra,
  env_agree 32 (Ereg regs extra) (Eimg (PI := PI_transportb) (Ereg regs extra)).
Proof. intros regs extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma anp_le8_nth : forall v k, (k < 8)%nat -> bv_unsigned (nth k (LMem.le8 (LMem.wa v)) (Z_to_bv 8 0)) = le_byte v 8 k.
Proof.
  intros v k Hk. pose proof (can_leafb_le8_byte v k Hk) as H.
  rewrite (nth_error_nth' _ (Z_to_bv 8 0)) in H by (rewrite LMem.length_le8; lia).
  cbn [option_map] in H. injection H as H. exact H.
Qed.

Lemma anp_nth_le8 : forall v j, (j < 8)%nat -> nth j (map bz (LMem.le8 (w64 v))) 0 = le_byte v 8 j.
Proof.
  intros v j Hj. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, LMem.length_le8; lia).
  rewrite map_nth. unfold bz. change (w64 v) with (LMem.wa v). apply anp_le8_nth. exact Hj.
Qed.

Lemma anp_le_byte_range : forall v w k, 0 <= le_byte v w k < 256.
Proof. intros v w k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma anp_val8 : forall m p v, 0 <= v < 2 ^ 64 ->
  garr8 segs m p (map bz (LMem.le8 (w64 v))) -> val_mem segs m p 8 v.
Proof.
  intros m p v Hv HG k Hk.
  assert (Hl : (k < length (map bz (LMem.le8 (w64 v))))%nat) by (rewrite length_map, LMem.length_le8; lia).
  rewrite (garr8_mbyte segs m p _ k HG Hl), anp_nth_le8 by exact Hk. reflexivity.
Qed.

Lemma anp_le_byte1 : forall x, 0 <= x < 256 -> le_byte x 1 0 = x.
Proof.
  intros x Hx. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  change (2 ^ 8) with 256. rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity.
Qed.

Lemma anp_garr8_val8 : forall m p v, val_mem segs m p 8 v -> garr8 segs m p (map bz (LMem.le8 (w64 v))).
Proof.
  intros m p v HV j Hj. rewrite length_map, LMem.length_le8 in Hj.
  rewrite anp_nth_le8 by exact Hj. split; [|apply anp_le_byte_range].
  intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (HV j Hj). rewrite anp_le_byte1 by apply anp_le_byte_range. reflexivity.
Qed.

Lemma anp_val1_of_garr8 : forall m p v, garr8 segs m p [v] -> val_mem segs m p 1 v.
Proof.
  intros m p v HG. pose proof (HG 0%nat ltac:(cbn; lia)) as [H _]. cbn [nth Z.of_nat] in H.
  rewrite Z.add_0_r in H. exact H.
Qed.

Lemma anp_val1_of_aview : forall (H : word -> bool) m a v, aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
  intros H m a v Ha k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  destruct (aview_byte segs H m a v Ha) as (b & Hm & Hvb & Hr). rewrite Hm. f_equal.
  rewrite anp_le_byte1 by lia. subst v. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The 16 bytes at f + 32: body and the length of bb. *)
Lemma anp_f32_vals : forall m f body bb, 0 <= body < 2 ^ 64 -> 0 <= Z.of_nat (length bb) < 2 ^ 64 ->
  garr8 segs m (f + 32) (trans_anp_f32_bytes body bb) ->
  val_mem segs m (f + 32) 8 body /\ val_mem segs m (f + 40) 8 (Z.of_nat (length bb)).
Proof.
  intros m f body bb Hb Hl HG. unfold trans_anp_f32_bytes in HG. cbn [LC.cells_bytes LC.cbytes] in HG.
  rewrite app_nil_r, map_app in HG. apply garr8_app in HG as [H1 H2].
  rewrite length_map, LMem.length_le8 in H2. replace (f + 32 + Z.of_nat 8) with (f + 40) in H2 by lia.
  split; [exact (anp_val8 m _ body Hb H1) | exact (anp_val8 m _ _ Hl H2)].
Qed.

Lemma anp_vis : forall (W : world segs) mem a, aview segs (w_H W) mem a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a H. destruct (aview segs (w_H W) mem a) as [v|] eqn:E; [exact (can_leafb_aview_vis W mem a v E) | congruence].
Qed.

(* `srli s2,s1,3` with s1 = f + 32, then `add s2,s2,a2`: the shadow address of f + 32. *)
Lemma anp_denot_shadow : forall E n m F c SHB,
  ew E n = Z_to_bv 64 F -> ew E m = Z_to_bv 64 SHB ->
  0 <= F -> 0 <= c -> F + c < 2 ^ 64 -> 0 <= SHB -> SHB + (F + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SHB + (F + c) / 8).
Proof.
  intros E n m F c SHB Hn Hm HF Hc HFc HS1 HS2.
  assert (HD : 0 <= (F + c) / 8) by (apply Z.div_pos; lia).
  assert (HD2 : (F + c) / 8 <= F + c) by (apply Z.div_le_upper_bound; lia).
  assert (Un : U E (SOff n c) = F + c)
    by (rewrite U_SOff, Hn, (unsigned_lit_small F ltac:(lia)); apply zcanon_id; unfold M64; lia).
  assert (Um : U E (SOff m 0) = SHB)
    by (rewrite U_SOff, Hm, (unsigned_lit_small SHB ltac:(lia)), Z.add_0_r; apply zcanon_id; unfold M64; lia).
  rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite Un, Um, U_SLit, (zcanon_id 3) by (unfold M64; lia).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((F + c) / 8)) by (unfold M64; lia).
  rewrite (Z.add_comm ((F + c) / 8) SHB). apply zcanon_id. unfold M64. lia.
Qed.


Lemma anp_preserved : forall (regs regsF : bvmap 5 word),
  YK11.getr regsF 2 = YK11.getr regs 2 -> YK11.getr regsF 8 = YK11.getr regs 8 ->
  YK11.getr regsF 9 = YK11.getr regs 9 -> YK11.getr regsF 18 = YK11.getr regs 18 ->
  (forall r, In r anp_kregs -> YK11.getr regsF r = YK11.getr regs r) -> aregs_preserved regs regsF.
Proof.
  intros regs regsF R2 R8 R9 R18 RK r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27])
    by (cbn [In]; lia).
  destruct Hr' as [-> | [-> | [-> | [-> | Hin]]]]; [exact R2 | exact R8 | exact R9 | exact R18 |].
  apply RK. unfold anp_kregs. apply in_map. exact Hin.
Qed.

Lemma anp_restrict_regs : forall (H : word -> bool) ms, ms_regs (restrict H ms) = ms_regs ms.
Proof. intros H ms. destruct ms; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Lemma anp_holds : @transport_diginet_announce_parse_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_diginet_announce_parse_cg_holds_stmt.
intros HCELLS LAWS MTL LEAF0.
unfold transport_diginet_announce_parse_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f ap cmd body bb aj
  HJ0 Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Hf0 Hap0 Hf8 Hap8 Hbody Hcmd Hgcmd Hgf32 Hfrd Hfoff Hbsrc Hboff Hgbb
  Hlaj Hgaj Hfake Htwr Hard Haoff Hdisf Hdisb Hev.
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFS : TRANS_ANP_STK = 4128) by reflexivity.
assert (HFF : FRAME_F_SIZE = 64) by reflexivity.
unfold decode_off_win in Hfoff, Haoff. rewrite HFS in Hlo, Hfoff, Haoff. rewrite HFF in Hfrd, Hfoff, Hdisf.
assert (Hsp : alloc_ceiling + 4128 <= spZ regs <= 2 ^ 47) by lia.
destruct Hfrd as (Hfv & Hfra & _ & Hfam & Hfq0 & Hfq63).
destruct Hard as (Hav & Hara & _ & Haam & Haq0 & Haq63).
unfold amem_range in Hfam, Haam. rewrite C3, C4, C5 in Hfam, Haam.
assert (Hfr : 8 <= f <= 2 ^ 47 - 65) by (pose proof (Z.div_mod f 8 ltac:(lia)); lia).
assert (Hapr : 8 <= ap <= 2 ^ 47 - 41) by (pose proof (Z.div_mod ap 8 ltac:(lia)); lia).
set (len := Z.of_nat (length bb)) in *.
assert (Hlen0 : 0 <= len) by (unfold len; lia).
(* the length is at most 2 ^ 47: 0, or placed with the body by trans_src_ok (trans_src_ok_place) *)
assert (Hlen47 : len <= 2 ^ 47).
{ destruct (Nat.eq_dec (length bb) 0) as [E0|E0]; [unfold len; rewrite E0; cbn; lia|].
  destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc body len HAR (Hbsrc ltac:(lia)) ltac:(unfold len; lia))
    as [Hp|Hp]; lia. }
(* the 64-bit value at f + 32 the code reads as body; it is body once the length test places the body *)
remember (body mod 2 ^ 64) as bw eqn:EBW.
assert (Hbw : 0 <= bw < 2 ^ 64) by (rewrite EBW; apply Z.mod_pos_bound; lia).
assert (Ew : w64 body = w64 bw).
{ rewrite EBW. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64. rewrite Zmod_mod. reflexivity. }
clear EBW.
assert (HBH : anp_hold (((0 < length bb)%nat -> decode_off_win regs TRANS_ANP_STK body len) /\
                       ((0 < length bb)%nat -> ap + 40 <= body \/ body + len <= ap))) by (split; assumption).
clear Hboff Hdisb.
pose proof Hfake as (cidA & posA & HinF & HF1 & HF2).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cidA posA HAR HinF) as (HFa0 & HFac & _).
(* ---- run a: +0x000 .. +0x038 ---- *)
(* the 40 bytes aj at ap: the version field, the name field and the 4 bytes that no path writes *)
pose proof Hgaj as Gaj. rewrite <- (firstn_skipn 10 aj), map_app in Gaj. apply garr8_app in Gaj as [GA0 Gaj].
rewrite length_map, length_firstn, Hlaj in Gaj. change (Z.of_nat (Nat.min 10 40)) with 10 in Gaj.
rewrite <- (firstn_skipn 10 (skipn 10 aj)), map_app in Gaj. apply garr8_app in Gaj as [GA10 Gaj].
rewrite length_map, length_firstn, length_skipn, Hlaj in Gaj. change (Z.of_nat (Nat.min 10 (40 - 10))) with 10 in Gaj.
rewrite skipn_skipn in Gaj. change (10 + 10)%nat with 20%nat in Gaj.
rewrite <- (firstn_skipn 4 (skipn 20 aj)), map_app in Gaj. apply garr8_app in Gaj as [GA20 _].
replace (ap + 10 + 10) with (ap + 20) in GA20 by lia.
assert (EA2 : bv_unsigned (ew (anp_Ea regs) 2) = spZ regs)
  by (unfold anp_Ea; rewrite (can_ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (EA10 : ew (anp_Ea regs) 10 = w64 f)
  by (unfold anp_Ea; rewrite (can_ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EA11 : ew (anp_Ea regs) 11 = w64 ap)
  by (unfold anp_Ea; rewrite (can_ew_Eimg_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EA32 : ew (anp_Ea regs) 32 = w64 SHADOW_OFF)
  by (unfold anp_Ea; exact (anp_ew_x regs _ 0 ltac:(unfold A_TEXT; lia))).
assert (Hpres1 : forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres0; lia).
pose proof (anp_entry_a lyc Sc W regs memc mdc f ap HCELLS HAR Hpres1 ltac:(lia) Hsp16 H10 H11 Hfr Hf8 Hapr Hap8) as HS.
assert (HEI : img_env VAL A_LIM (anp_Ea regs)) by apply Eimg_env.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (anp_Ea regs) (mrestrict (w_H W) memc)) by constructor.
pose proof (paj_run (SK := tfib_sink_head) (PI := PI_transportb) B LAWS) as RUN.
pose proof (paj_run_to (SK := tfib_sink_head) (PI := PI_transportb) B LAWS) as RUNTO.
pose proof (@paj_branch fx rc transportb_listing PI_transportb) as BR.
pose proof HJ0 as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_announce_parse)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK ANP_B0 (AA 0x38).
{ anp_awr_norm.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite EA2; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  anp_ro_rec. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msA := msx) in * end.
(* the run wrote the frame only *)
assert (Ka : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 32 <= x < spZ regs) ->
  aview segs (w_H W) (ms_mem msA) x = aview segs (w_H W) memc x).
{ apply (anp_kept_of _ _ _ _ _ _ HFr). intros a (r & Hr & Ha).
  unfold ss_anp_a, stack_region, got_regionP, bcell_regionP in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    [rewrite EA2 in Ha|..]; lia. }
clear HF HFr. rename HG into HGa.
anp_reg HS (2%bv : bv 5) (w64 (spZ regs - 32)) R2a ltac:(cbn [sv_denot]; rewrite EA2; unfold w64; f_equal; lia).
anp_reg HS (8%bv : bv 5) (w64 ap) R8a ltac:(cbn [sv_denot]; rewrite EA11, anp_u64, Z.add_0_r by lia; reflexivity).
anp_reg HS (10%bv : bv 5) (w64 f) R10a ltac:(cbn [sv_denot]; rewrite EA10, anp_u64, Z.add_0_r by lia; reflexivity).
anp_reg HS (12%bv : bv 5) (w64 SHADOW_OFF) R12a
  ltac:(cbn [sv_denot]; rewrite EA32, anp_u64, Z.add_0_r by (unfold SHADOW_OFF; lia); reflexivity).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) _ _ _ regs _ anp_kregs HS (anp_env_agree regs _)
  ltac:(vm_compute; reflexivity)) as KRa.
rewrite anp_restrict_regs in KRa.
(* the four saved words *)
anp_region HS 0%nat HRa.
assert (S0a : val_mem segs (mrestrict (w_H W) (ms_mem msA)) (spZ regs - 32 + 0) 8 (bv_unsigned (YK11.getr regs 18))).
{ replace (spZ regs - 32 + 0) with (spZ regs + -32) by lia.
  apply (can_field_of_region (anp_Ea regs) _ 2 (spZ regs) _ (-32) 0 (-32) 0 (-32) 8%N (SOff 18 0) _ HRa EA2);
  [anp_in | unfold anp_Ea; cbn [sv_denot]; rewrite (can_ew_Eimg_Ereg_nat regs _ 18 18%bv eq_refl), Z.add_0_r; reflexivity
  | anp_rng64 (YK11.getr regs 18) | cbn; lia]. }
assert (S8a : val_mem segs (mrestrict (w_H W) (ms_mem msA)) (spZ regs - 32 + 8) 8 (bv_unsigned (YK11.getr regs 9))).
{ replace (spZ regs - 32 + 8) with (spZ regs + -24) by lia.
  apply (can_field_of_region (anp_Ea regs) _ 2 (spZ regs) _ (-32) 0 (-32) 0 (-24) 8%N (SOff 9 0) _ HRa EA2);
  [anp_in | unfold anp_Ea; cbn [sv_denot]; rewrite (can_ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), Z.add_0_r; reflexivity
  | anp_rng64 (YK11.getr regs 9) | cbn; lia]. }
assert (S16a : val_mem segs (mrestrict (w_H W) (ms_mem msA)) (spZ regs - 32 + 16) 8 (bv_unsigned (YK11.getr regs 8))).
{ replace (spZ regs - 32 + 16) with (spZ regs + -16) by lia.
  apply (can_field_of_region (anp_Ea regs) _ 2 (spZ regs) _ (-32) 0 (-32) 0 (-16) 8%N (SOff 8 0) _ HRa EA2);
  [anp_in | unfold anp_Ea; cbn [sv_denot]; rewrite (can_ew_Eimg_Ereg_nat regs _ 8 8%bv eq_refl), Z.add_0_r; reflexivity
  | anp_rng64 (YK11.getr regs 8) | cbn; lia]. }
assert (S24a : val_mem segs (mrestrict (w_H W) (ms_mem msA)) (spZ regs - 32 + 24) 8 (bv_unsigned (YK11.getr regs 1))).
{ replace (spZ regs - 32 + 24) with (spZ regs + -8) by lia.
  apply (can_field_of_region (anp_Ea regs) _ 2 (spZ regs) _ (-32) 0 (-32) 0 (-8) 8%N (SOff 1 0) _ HRa EA2);
  [anp_in | unfold anp_Ea; cbn [sv_denot]; rewrite (can_ew_Eimg_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r; reflexivity
  | anp_rng64 (YK11.getr regs 1) | cbn; lia]. }
clear HRa.
(* ---- run b: +0x038 .. +0x0c8 ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + AA 0x38)) mm rom) mdx) Q) end.
assert (Gcmd : garr8 segs (mrestrict (w_H W) (ms_mem msA)) (f + 30) [cmd])
  by (apply (anp_garr8_kept _ memc); [exact Hgcmd | intros x Hx; cbn [length Z.of_nat] in Hx; apply Ka; lia]).
assert (Hl16 : length (trans_anp_f32_bytes body bb) = 16%nat).
{ unfold trans_anp_f32_bytes. cbn [LC.cells_bytes LC.cbytes].
  rewrite app_nil_r, length_map, length_app, !LMem.length_le8. reflexivity. }
assert (Gf32 : garr8 segs (mrestrict (w_H W) (ms_mem msA)) (f + 32) (trans_anp_f32_bytes body bb))
  by (apply (anp_garr8_kept _ memc); [exact Hgf32 | intros x Hx; rewrite Hl16 in Hx; apply Ka; lia]).
assert (Gf32w : garr8 segs (mrestrict (w_H W) (ms_mem msA)) (f + 32) (trans_anp_f32_bytes bw bb)).
{ replace (trans_anp_f32_bytes bw bb) with (trans_anp_f32_bytes body bb); [exact Gf32|].
  unfold trans_anp_f32_bytes. rewrite Ew. reflexivity. }
destruct (anp_f32_vals _ f bw bb ltac:(lia) ltac:(lia) Gf32w) as (Vb & Vl).
pose proof (anp_entry_b W (ms_regs msA) regs (ms_mem msA) (spZ regs - 32) f ap cmd bw len R2a R8a R10a R12a
  ltac:(lia) ltac:(lia) Hfr Hf8 Hapr Hap8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  (anp_val1_of_garr8 _ _ _ Gcmd) Vb Vl S0a S8a S16a S24a) as HSb.
clear HS. rename HSb into HS.
set (Eb := anp_Eb (ms_regs msA) regs cmd bw len) in HS.
assert (HEIb : img_env VAL A_LIM Eb) by apply Eimg_env.
assert (Eb8 : ew Eb 8 = w64 ap) by (unfold Eb, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat _ _ 8 8%bv eq_refl); exact R8a).
assert (Eb10 : ew Eb 10 = w64 f) by (unfold Eb, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat _ _ 10 10%bv eq_refl); exact R10a).
assert (Eb12 : ew Eb 12 = w64 SHADOW_OFF)
  by (unfold Eb, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat _ _ 12 12%bv eq_refl); exact R12a).
assert (Eb32 : ew Eb 32 = w64 cmd) by (unfold Eb, anp_Eb; exact (anp_ew_x _ _ 0 ltac:(unfold A_TEXT; lia))).
assert (Eb33 : ew Eb 33 = w64 bw) by (unfold Eb, anp_Eb; exact (anp_ew_x _ _ 1 ltac:(unfold A_TEXT; lia))).
assert (Eb34 : ew Eb 34 = w64 len) by (unfold Eb, anp_Eb; exact (anp_ew_x _ _ 2 ltac:(unfold A_TEXT; lia))).
assert (UB : U Eb (SOff 12 0) = SHADOW_OFF)
  by (rewrite U_SOff, Eb12, anp_u64, Z.add_0_r by (unfold SHADOW_OFF; lia); apply zcanon_id; unfold M64, SHADOW_OFF; lia).
assert (UF : U Eb (SOff 10 0) = f)
  by (rewrite U_SOff, Eb10, anp_u64, Z.add_0_r by lia; apply zcanon_id; unfold M64; lia).
assert (UAp : U Eb (SOff 8 0) = ap)
  by (rewrite U_SOff, Eb8, anp_u64, Z.add_0_r by lia; apply zcanon_id; unfold M64; lia).
assert (SHOKb : sh_ok segs (SOff 12 0) anp_SH Eb (mrestrict (w_H W) (ms_mem msA))).
{ unfold anp_SH, sh_ok. repeat apply Forall_cons; try apply Forall_nil.
  - apply (shent_ok_of_range segs (w_H W) (ms_mem msA) Eb (SOff 12 0) 10 f 64 f 0 64); [ | exact UB | exact UF | lia | lia | ].
    + apply (anp_ra_kept _ memc); [| exact Hfra]. intros x Hx. pose proof (anp_shadow_range x ltac:(lia)).
      apply Ka; unfold SHADOW_OFF in *; lia.
    + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range segs (w_H W) (ms_mem msA) Eb (SOff 12 0) 8 ap 40 ap 0 40); [ | exact UB | exact UAp | lia | lia | ].
    + apply (anp_ra_kept _ memc); [| exact Hara]. intros x Hx. pose proof (anp_shadow_range x ltac:(lia)).
      apply Ka; unfold SHADOW_OFF in *; lia.
    + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF. lia. }
clear SHOK. rename SHOKb into SHOK.
paj_run_tok RUN HS HJ SHOK ANP_Bsp; [anp_awr_ro|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msB1 := msx) in * end.
assert (Kb1 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W) (ms_mem msB1) x = aview segs (w_H W) (ms_mem msA) x).
{ intros x Hx. apply (anp_kept_of _ _ _ _ _ (fun _ => False) HFr); [| exact Hx | auto].
  intros a (r & Hr & Ha). unfold ss_anp_b, anp_rg_sv, anp_rg_f in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
clear HF HFr. rename HG into HGb1.
assert (Eb2 : ew Eb 2 = w64 (spZ regs - 32)) by (unfold Eb, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat _ _ 2 2%bv eq_refl); exact R2a).
assert (Eb35 : ew Eb 35 = YK11.getr regs 18) by (unfold Eb, anp_Eb; exact (anp_ew_x _ _ 3 ltac:(unfold A_TEXT; lia))).
assert (Eb36 : ew Eb 36 = YK11.getr regs 9) by (unfold Eb, anp_Eb; exact (anp_ew_x _ _ 4 ltac:(unfold A_TEXT; lia))).
assert (Eb37 : ew Eb 37 = YK11.getr regs 8) by (unfold Eb, anp_Eb; exact (anp_ew_x _ _ 5 ltac:(unfold A_TEXT; lia))).
assert (Eb38 : ew Eb 38 = YK11.getr regs 1) by (unfold Eb, anp_Eb; exact (anp_ew_x _ _ 6 ltac:(unfold A_TEXT; lia))).
assert (Uc : U Eb (SOff 32 0) = cmd) by (apply (U_atom Eb 32 cmd Eb32); lia).
assert (Ul : U Eb (SOff 34 0) = len) by (apply (U_atom Eb 34 len Eb34); lia).
psrr_branch_tok RUN BR HS SHOK ANP_Bsp.
{ (* +0x058 `bne` taken: cmd & 0xfe is not 0xe0, the code is -9 *)
  assert (Hcf : ann_cmd cmd = false).
  { rewrite branch_ne_U, U_and_lit, Uc, U_lit in Hc by lia.
    rewrite <- (ann_cmd_land cmd Hcmd). apply negb_true_iff in Hc. exact Hc. }
  paj_run_tok RUN HS HJ SHOK ANP_Bsp; [anp_awr_ro|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msF := msx) in * end.
  assert (KF : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W) (ms_mem msF) x = aview segs (w_H W) (ms_mem msB1) x).
  { intros x Hx. apply (anp_kept_of _ _ _ _ _ (fun _ => False) HFr); [| exact Hx | auto].
    intros a (r & Hr & Ha). vm_compute in Hr.
    repeat (destruct Hr as [<- | Hr]; [cbn in Ha; lia|]). destruct Hr. }
  anp_reg HS (2%bv : bv 5) (YK11.getr regs 2) F2
    ltac:(cbn [sv_denot]; rewrite Eb2, anp_u64 by lia; replace (spZ regs - 32 + 32) with (spZ regs) by lia;
          unfold spZ; apply Z_to_bv_bv_unsigned).
  anp_reg HS (1%bv : bv 5) (YK11.getr regs 1) F1 ltac:(cbn [sv_denot]; rewrite Eb38, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  anp_reg HS (8%bv : bv 5) (YK11.getr regs 8) F8 ltac:(cbn [sv_denot]; rewrite Eb37, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  anp_reg HS (9%bv : bv 5) (YK11.getr regs 9) F9 ltac:(cbn [sv_denot]; rewrite Eb36, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  anp_reg HS (18%bv : bv 5) (YK11.getr regs 18) F18 ltac:(cbn [sv_denot]; rewrite Eb35, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  anp_reg HS (10%bv : bv 5) (w64 (ann_code cmd len)) F10
    ltac:(unfold ann_code; rewrite Hcf; apply bv_eq; vm_compute; reflexivity).
  pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) _ _ _ (ms_regs msA) _ anp_kregs HS (anp_env_agree (ms_regs msA) _)
    ltac:(vm_compute; reflexivity)) as KRF.
  rewrite anp_restrict_regs in KRF.
  eapply (paj_ret_at (L := transportb_listing) (PL := PL_transportb) (PI := PI_transportb) W _ _ _ _ _ HS eq_refl
    ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  apply (anp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ap cmd body bb aj _ _ _ LAWS MTL HJ0
    (ajournal_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ)).
  - rewrite HFS. lia.
  - lia.
  - exact Hfake.
  - intros x Hx Hw Hn. rewrite HFS in Hw. rewrite KF, Kb1, Ka by lia. reflexivity.
  - apply anp_preserved; [exact F2 | exact F8 | exact F9 | exact F18 |].
    intros r Hr. rewrite KRF, KRa by exact Hr. reflexivity.
  - exact Hra.
  - exact F1.
  - exact F10.
  - unfold trans_anp_bytes, trans_anp_cells, ann_ok. fold len.
    replace (ann_code cmd len =? 0) with false by (unfold ann_code; rewrite Hcf; reflexivity).
    cbn [LC.cells_bytes LC.cbytes]. rewrite app_nil_r.
    apply (anp_garr8_kept _ memc); [exact Hgaj|].
    intros x Hx. rewrite length_map, Hlaj in Hx. change (Z.of_nat 40) with 40 in Hx.
    rewrite KF, Kb1, Ka by lia. reflexivity. }
(* +0x058 `bne` not taken: cmd & 0xfe is 0xe0 *)
assert (Hct : ann_cmd cmd = true).
{ rewrite branch_ne_U, U_and_lit, Uc, U_lit in Hc by lia.
  rewrite <- (ann_cmd_land cmd Hcmd). apply negb_false_iff in Hc. exact Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK ANP_Bsp; [anp_awr_ro|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msB2 := msx) in * end.
assert (Kb2 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W) (ms_mem msB2) x = aview segs (w_H W) (ms_mem msB1) x).
{ intros x Hx. apply (anp_kept_of _ _ _ _ _ (fun _ => False) HFr); [| exact Hx | auto].
  intros a (r & Hr & Ha). vm_compute in Hr.
  repeat (destruct Hr as [<- | Hr]; [cbn in Ha; lia|]). destruct Hr. }
clear HF HFr. rename HG into HGb2.
psrr_branch_tok RUN BR HS SHOK ANP_Bsp.
2:{ (* +0x078 `bgeu` not taken: the length is under 33, the code is -4 *)
  assert (Hl33 : len < 33).
  { rewrite branch_geu_U, Ul, U_lit in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
  assert (Hcode : ann_code cmd len = -4)
    by (unfold ann_code; rewrite Hct; cbn [negb]; rewrite (proj2 (Z.ltb_lt len 33) Hl33); reflexivity).
  paj_run_tok RUN HS HJ SHOK ANP_Bsp; [anp_awr_ro|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msF := msx) in * end.
  assert (KF : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W) (ms_mem msF) x = aview segs (w_H W) (ms_mem msB2) x).
  { intros x Hx. apply (anp_kept_of _ _ _ _ _ (fun _ => False) HFr); [| exact Hx | auto].
    intros a (r & Hr & Ha). vm_compute in Hr.
    repeat (destruct Hr as [<- | Hr]; [cbn in Ha; lia|]). destruct Hr. }
  anp_reg HS (2%bv : bv 5) (YK11.getr regs 2) F2
    ltac:(cbn [sv_denot]; rewrite Eb2, anp_u64 by lia; replace (spZ regs - 32 + 32) with (spZ regs) by lia;
          unfold spZ; apply Z_to_bv_bv_unsigned).
  anp_reg HS (1%bv : bv 5) (YK11.getr regs 1) F1 ltac:(cbn [sv_denot]; rewrite Eb38, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  anp_reg HS (8%bv : bv 5) (YK11.getr regs 8) F8 ltac:(cbn [sv_denot]; rewrite Eb37, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  anp_reg HS (9%bv : bv 5) (YK11.getr regs 9) F9 ltac:(cbn [sv_denot]; rewrite Eb36, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  anp_reg HS (18%bv : bv 5) (YK11.getr regs 18) F18 ltac:(cbn [sv_denot]; rewrite Eb35, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  anp_reg HS (10%bv : bv 5) (w64 (ann_code cmd len)) F10 ltac:(rewrite Hcode; apply bv_eq; vm_compute; reflexivity).
  pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) _ _ _ (ms_regs msA) _ anp_kregs HS (anp_env_agree (ms_regs msA) _)
    ltac:(vm_compute; reflexivity)) as KRF.
  rewrite anp_restrict_regs in KRF.
  eapply (paj_ret_at (L := transportb_listing) (PL := PL_transportb) (PI := PI_transportb) W _ _ _ _ _ HS eq_refl
    ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  apply (anp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ap cmd body bb aj _ _ _ LAWS MTL HJ0
    (ajournal_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ)).
  - rewrite HFS. lia.
  - lia.
  - exact Hfake.
  - intros x Hx Hw Hn. rewrite HFS in Hw. rewrite KF, Kb2, Kb1, Ka by lia. reflexivity.
  - apply anp_preserved; [exact F2 | exact F8 | exact F9 | exact F18 |].
    intros r Hr. rewrite KRF, KRa by exact Hr. reflexivity.
  - exact Hra.
  - exact F1.
  - exact F10.
  - unfold trans_anp_bytes, trans_anp_cells, ann_ok. fold len. rewrite Hcode. cbn [Z.eqb].
    cbn [LC.cells_bytes LC.cbytes]. rewrite app_nil_r.
    apply (anp_garr8_kept _ memc); [exact Hgaj|].
    intros x Hx. rewrite length_map, Hlaj in Hx. change (Z.of_nat 40) with 40 in Hx.
    rewrite KF, Kb2, Kb1, Ka by lia. reflexivity. }
(* +0x078 `bgeu` taken: 33 <= the length, the code is 0 *)
assert (Hl33 : 33 <= len).
{ rewrite branch_geu_U, Ul, U_lit in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. exact Hc. }
clear Hc.
assert (Hcode : ann_code cmd len = 0)
  by (unfold ann_code; rewrite Hct; cbn [negb]; rewrite (proj2 (Z.ltb_ge len 33) Hl33); reflexivity).
assert (Hlb : (33 <= length bb)%nat) by (unfold len in Hl33; lia).
(* the body is not empty: trans_src_ok places it (trans_src_ok_place), its bytes are visible and marked usable
   (trans_src_ok_rd), it lies outside this call's window (decode_off_win) and outside ap; so the 64-bit value at
   f + 32 is body, and the engine takes the fact 1 <= body <= 2 ^ 47 for the code that reads it *)
assert (HL0 : (0 < length bb)%nat) by lia.
pose proof (trans_src_ok_place B LAWS lyc Sc W memc mdc body len HAR (Hbsrc HL0) ltac:(lia)) as Hpl.
pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc body len HAR (Hbsrc HL0) ltac:(lia))
  as (Hbv & Hbra & _ & Hbam & Hbq0 & Hbq63).
assert (Hb47 : 4096 <= body /\ body + len <= 2 ^ 47) by (destruct Hpl as [Hp | Hp]; lia).
clear Hpl.
destruct HBH as [Hboff Hdisb].
pose proof (Hdisb HL0) as Hdb. clear Hdisb.
assert (HBO : anp_hold (decode_off_win regs TRANS_ANP_STK body len)) by exact (Hboff HL0). clear Hboff.
assert (Ebw : bw = body).
{ pose proof (f_equal bv_unsigned Ew) as E. rewrite !anp_u64 in E by lia. lia. }
unfold amem_range in Hbam. rewrite C3, C4, C5 in Hbam.
assert (HBapp : forall a, body <= a < body + len -> AsanCells.app_mem a).
{ intros a Ha. unfold AsanCells.app_mem, AsanCells.LOWMEM_END, AsanCells.HIGHMEM_BEG, AsanCells.APPMEM_END. lia. }
clear Hbam.
assert (HFb : afact_ok Eb 33 (mkAF 1 (2 ^ 47) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Eb33, anp_u64 by lia. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pose proof (st_ok_pi_add_fact _ _ _ 33%nat _ HS HFb) as HS1. clear HS. rename HS1 into HS.
(* +0x078 .. +0x0c8, up to the first store to ap *)
paj_run_tok RUN HS HJ SHOK ANP_Bsp; [anp_awr_ro|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msB3 := msx) in * end.
assert (Kb3 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W) (ms_mem msB3) x = aview segs (w_H W) (ms_mem msB2) x).
{ intros x Hx. apply (anp_kept_of _ _ _ _ _ (fun _ => False) HFr); [| exact Hx | auto].
  intros a (r & Hr & Ha). vm_compute in Hr.
  repeat (destruct Hr as [<- | Hr]; [cbn in Ha; lia|]). destruct Hr. }
clear HF HFr. rename HG into HGb3.
assert (Pap : forall a, ap <= a < ap + 40 -> apresent (w_H W) (ms_mem msB3) a).
{ intros a Ha. apply (apresent_grows _ _ _ a HGb3), (apresent_grows _ _ _ a HGb2), (apresent_grows _ _ _ a HGb1),
    (apresent_grows _ _ _ a HGa).
  exact (proj1 (proj2 (Htwr a Ha))). }
(* ---- run c: ap + 24 .. ap + 40 becomes a writable region ---- *)
assert (U8 : bv_unsigned (ew Eb 8) = ap) by (rewrite Eb8; apply anp_u64; lia).
assert (U2 : bv_unsigned (ew Eb 2) = spZ regs - 32) by (rewrite Eb2; apply anp_u64; lia).
assert (U10 : bv_unsigned (ew Eb 10) = f) by (rewrite Eb10; apply anp_u64; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  assert (HSr : region_ok segs Ex (ms_mem msx) anp_rg_ap);
  [ unfold region_ok, anp_rg_ap; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite U8; cbn [ms_mem restrict];
    split; [lia|]; split; [lia|]; split; [| apply Forall_nil];
    intros o Ho; apply (apresent_writable segs); apply Pap; lia
  | assert (HSd : all_disjoint Ex anp_rg_ap (ss_mem ssx));
    [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, anp_rg_ap;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U8, U2, U10; repeat split; lia
    | pose proof (st_ok_pi_add_region (PI := PI_transportb) _ _ _ anp_rg_ap HS eq_refl HSr HSd) as HSc ] ] end.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSc.
clear HS HSr HSd. rename HSc into HS.
paj_run_tok RUN HS HJ SHOK ANP_Bsp.
{ anp_awr_norm.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat ap); [reflexivity | exact U8 | | anp_ro_rec].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. exact (proj1 (Htwr a ltac:(lia))). }
match type of HS with context [restrict _ ?msx] => set (msC := msx) in * end.
assert (Kc : forall x, 0 <= x < 2 ^ 64 -> ~ (ap + 24 <= x < ap + 40) ->
  aview segs (w_H W) (ms_mem msC) x = aview segs (w_H W) (ms_mem msB3) x).
{ apply (anp_kept_of _ _ _ _ _ _ HFr). intros a (r & Hr & Ha). vm_compute in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U8 in Ha; lia|]). destruct Hr. }
clear HF HFr. rename HG into HGc.
(* everything outside the frame and ap + 24 .. ap + 40 is as at the entry *)
assert (KCc : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 32 <= x < spZ regs) -> ~ (ap + 24 <= x < ap + 40) ->
  aview segs (w_H W) (ms_mem msC) x = aview segs (w_H W) memc x).
{ intros x Hx H1 H2. rewrite Kc, Kb3, Kb2, Kb1, Ka by assumption. reflexivity. }
assert (Pc : forall a, ap <= a < ap + 40 -> apresent (w_H W) (ms_mem msC) a)
  by (intros a Ha; apply (apresent_grows _ _ _ a HGc); exact (Pap a Ha)).
assert (Elen : len = Z.of_nat (length bb)) by reflexivity.
assert (Hq32 : 0 <= (f + 32) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
(* the registers at `jal copy_strz` (+0x0f4) *)
assert (Eb3 : ew Eb 3 = w64 (as_gp B))
  by (unfold Eb, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat _ _ 3 3%bv eq_refl), (KRa 3%bv) by anp_kin 3; exact Hgp).
assert (Eb4 : ew Eb 4 = w64 (as_tp B))
  by (unfold Eb, anp_Eb; rewrite (can_ew_Eimg_Ereg_nat _ _ 4 4%bv eq_refl), (KRa 4%bv) by anp_kin 4; exact Htp).
anp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + AA 0xf8)) P1 ltac:(apply codeptr_val; exact HEIb).
anp_reg HS (2%bv : bv 5) (w64 (spZ regs - 32)) P2 ltac:(cbn [sv_denot]; rewrite U2, Z.add_0_r; reflexivity).
anp_reg HS (Z_to_bv 5 2) (w64 (spZ regs - 32)) P2z ltac:(cbn [sv_denot]; rewrite U2, Z.add_0_r; reflexivity).
anp_reg HS (3%bv : bv 5) (w64 (as_gp B)) P3 ltac:(cbn [sv_denot]; rewrite Eb3, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (4%bv : bv 5) (w64 (as_tp B)) P4 ltac:(cbn [sv_denot]; rewrite Eb4, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (8%bv : bv 5) (w64 ap) P8 ltac:(cbn [sv_denot]; rewrite U8, Z.add_0_r; reflexivity).
anp_reg HS (9%bv : bv 5) (w64 (f + 32)) P9 ltac:(cbn [sv_denot]; rewrite U10; reflexivity).
anp_reg HS (18%bv : bv 5) (w64 (SHADOW_OFF + (f + 32) / 8)) P18
  ltac:(exact (anp_denot_shadow Eb 10 12 f 32 SHADOW_OFF Eb10 Eb12 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
anp_reg HS (Z_to_bv 5 10) (Z_to_bv 64 ap) P10 ltac:(cbn [sv_denot]; rewrite U8, Z.add_0_r; reflexivity).
anp_reg HS (Z_to_bv 5 11) (Z_to_bv 64 (body + 15)) P11
  ltac:(cbn [sv_denot]; rewrite Eb33, anp_u64, Ebw by lia; reflexivity).
pose proof (regs_kept_of_st_ok segs Eb _ _ (ms_regs msA) _ anp_kregs HS (anp_env_agree _ _)
  ltac:(vm_compute; reflexivity)) as KRc.
rewrite anp_restrict_regs in KRc.
(* ap + 24 holds body and ap + 32 holds 15 *)
anp_region HS 0%nat HRc.
assert (A24c : val_mem segs (mrestrict (w_H W) (ms_mem msC)) (ap + 24) 8 body)
  by (apply (can_field_of_region Eb _ 8 ap _ 24 40 24 40 24 8%N (SOff 33 0) body HRc U8);
      [anp_in | cbn [sv_denot]; rewrite Eb33, anp_u64, Z.add_0_r, Ebw by lia; reflexivity | cbn; lia | cbn; lia]).
assert (A32c : val_mem segs (mrestrict (w_H W) (ms_mem msC)) (ap + 32) 8 15)
  by (apply (can_field_of_region Eb _ 8 ap _ 24 40 24 40 32 8%N (SLit 15) 15 HRc U8);
      [anp_in | reflexivity | cbn; lia | cbn; lia]).
clear HRc.
assert (ESP : bv_unsigned (YK11.getr (ms_regs msC) (Z_to_bv 5 2)) = spZ regs - 32) by (rewrite P2z; apply anp_u64; lia).
(* the bytes the two calls read *)
assert (GB : forall o, (o <= 33)%nat ->
  garr8 segs (mrestrict (w_H W) memc) (body + Z.of_nat o) (map bz (skipn o bb))).
{ intros o Ho. pose proof Hgbb as G. rewrite <- (firstn_skipn o bb), map_app in G. apply garr8_app in G as [_ G].
  rewrite length_map, length_firstn, Nat.min_l in G by lia. exact G. }
assert (GB15 : garr8 segs (mrestrict (w_H W) (ms_mem msC)) (body + 15) (map bz (skipn 15 bb))).
{ apply (anp_garr8_kept _ memc); [exact (GB 15%nat ltac:(lia))|].
  intros x Hx. rewrite length_map, length_skipn in Hx.
  pose proof HBO as Hbo. unfold anp_hold, decode_off_win in Hbo. rewrite HFS in Hbo. apply KCc; lia. }
assert (GA0c : garr8 segs (mrestrict (w_H W) (ms_mem msC)) ap (map bz (firstn 10 aj))).
{ apply (anp_garr8_kept _ memc); [exact GA0|].
  intros x Hx. rewrite length_map, length_firstn, Hlaj in Hx. change (Z.of_nat (Nat.min 10 40)) with 10 in Hx.
  apply KCc; lia. }
assert (RAc : range_addressable (aview segs (w_H W) (ms_mem msC)) SHADOW_OFF ap 40).
{ apply (anp_ra_kept _ memc); [| exact Hara]. intros x Hx. pose proof (anp_shadow_range x ltac:(lia)).
  apply KCc; unfold SHADOW_OFF in *; lia. }
assert (RBc : range_addressable (aview segs (w_H W) (ms_mem msC)) SHADOW_OFF body len).
{ apply (anp_ra_kept _ memc); [| exact Hbra]. intros x Hx. pose proof (anp_shadow_range x ltac:(lia)).
  apply KCc; unfold SHADOW_OFF in *; lia. }
(* ---- call 1: copy_strz (ap, body + 15) ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 LCZ.COPY_STRZ) mm rom) mdx) Q) end.
eapply SRr_bind.
{ eapply (can_leafb_journal B LAWS W (ms_regs msC) (ms_mem msC) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (spZ regs - 32 - sp0) LCZ.COPY_STRZ None [(ap, ap + 10)]
    (fun m2 => LStp.rw_cells segs m2 ap [LC.CB 10 (DgnSpec.copy_strz 10 9 (skipn 15 bb) (firstn 10 aj))]) HJ).
  - unfold spZ at 1. first [rewrite ESP | rewrite P2, anp_u64 by lia]. lia.
  - Z.div_mod_to_equations. lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite P1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold AA, AF_diginet_announce_parse; lia | reflexivity].
  - exact P3.
  - exact P4.
  - intros a Ha. unfold LCK.in_wr in Ha. apply Exists_cons in Ha. destruct Ha as [Ha | Ha]; [|inversion Ha].
    cbn [fst snd] in Ha. exact (proj1 (Htwr a ltac:(lia))).
  - intros HPRE.
    pose proof (LEAF0 fx) as LF.
    unfold transport_leaf_wr_at, LCpy.transport_copy_strz_cg in LF.
    specialize (LF lyc Sc W (ms_regs msC) (ms_mem msC) _ (skipn 15 bb) (firstn 10 aj) ap (body + 15)
      (spZ regs - 32 - 16) HPRE).
    cbv zeta in LF. rewrite ESP in LF. unfold LCZ.COPY_STRZ_FRAME in LF.
    apply LF; clear LF.
    + exact P10.
    + exact P11.
    + lia.
    + rewrite length_skipn. lia.
    + apply (can_leafb_bytes_garr8 W (ms_mem msC) (body + 15) (skipn 15 bb)); [exact GB15 | lia | rewrite length_skipn; lia].
    + apply (FFv.decode_rw_of_garr8 (w_H W) (ms_mem msC) ap [LC.CB 10 (firstn 10 aj)]).
      * cbn [LC.cells_wf LC.cell_wf]. rewrite length_firstn, Hlaj. split; [reflexivity | exact I].
      * lia.
      * cbn. lia.
      * intros i Hi. cbn in Hi. apply Pc. lia.
      * cbn [LC.cells_bytes LC.cbytes]. rewrite app_nil_r. exact GA0c.
    + lia.
    + eapply (can_leafb_stk_journal B); [exact HJ | lia | lia].
    + lia.
    + unfold AsanKA.off_stk. rewrite ESP.
      pose proof HBO as Hbo. unfold anp_hold, decode_off_win in Hbo. rewrite HFS in Hbo. lia.
    + unfold AsanKA.off_stk. rewrite ESP. left. lia.
    + apply (@can_leafb_app_stack rc). lia.
    + apply (@can_leafb_app_stack rc). lia.
    + exact (can_leafb_asan_cells B HCELLS lyc Sc W (ms_mem msC) _ (proj1 HJ)).
    + unfold AsanKA.off_stk. rewrite ESP. left. unfold AsanCells.GOT_CELL_K. lia.
    + unfold AsanKA.off_stk. rewrite ESP. left. unfold AsanCells.CELL_K. lia.
    + apply (can_leafb_addressable W (ms_mem msC) (body + 15) 9); [eapply range_addressable_sub; [exact RBc | lia | lia]
        | lia | lia | unfold AsanCells.APPMEM_END; lia |].
      intros i Hi. apply HBapp. lia.
    + apply (can_leafb_addressable W (ms_mem msC) ap 10); [eapply range_addressable_sub; [exact RAc | lia | lia] | lia | lia
        | unfold AsanCells.APPMEM_END; lia |].
      intros i Hi. unfold AsanCells.app_mem, AsanCells.LOWMEM_END, AsanCells.HIGHMEM_BEG, AsanCells.APPMEM_END. lia.
    + eapply (can_leafb_rng_journal B); [exact HJ | lia | lia].
    + exact (proj1 (can_leafb_rng_cells W)).
    + exact (proj2 (can_leafb_rng_cells W)).
    + apply (can_leafb_rng W (body + 15) 9); [lia | lia |]. intros a Ha. apply (anp_vis W memc). apply Hbv. lia.
    + apply (can_leafb_rng_shadow W memc (body + 15) 9); [eapply range_addressable_sub; [exact Hbra | lia | lia] | lia | lia | lia].
    + apply (can_leafb_rng W ap 10); [lia | lia |]. intros a Ha. apply (anp_vis W memc). apply Hav. lia.
    + apply (can_leafb_rng_shadow W memc ap 10); [eapply range_addressable_sub; [exact Hara | lia | lia] | lia | lia | lia].
    + intros x Hx. unfold LCK.in_wr in Hx. apply Exists_cons in Hx. destruct Hx as [Hx | Hx]; [cbn [fst snd] in Hx | inversion Hx].
      split; [exact (proj1 (proj2 (proj2 (Htwr x ltac:(lia))))) |].
      exact (frm_img segs B LAWS lyc Sc W (ms_mem msC) _ cidA posA x (proj1 HJ) HinF ltac:(lia)). }
cbv beta.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & _ & Heff5 & Hpres5 & HRW5).
assert (K5 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 32 - 4096 <= x < spZ regs - 32) -> ~ (ap <= x < ap + 10) ->
  aview segs (w_H W) mem5 x = aview segs (w_H W) (ms_mem msC) x).
{ intros x Hx H1 H2. apply Heff5; [exact Hx | unfold spZ; first [rewrite ESP | rewrite P2, anp_u64 by lia]; unfold ESTACK; lia |].
  intros Hw. unfold LCK.in_wr in Hw. apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; [cbn [fst snd] in Hw; lia | inversion Hw]. }
destruct HRW5 as [[Hwf5 Hbt5] _]. cbn [LC.cells_wf LC.cell_wf] in Hwf5. destruct Hwf5 as [HlV1 _].
assert (GV1 : garr8 segs (mrestrict (w_H W) mem5) ap (map bz (DgnSpec.copy_strz 10 9 (skipn 15 bb) (firstn 10 aj)))).
{ cbn [LC.cells_bytes LC.cbytes] in Hbt5. rewrite app_nil_r in Hbt5.
  apply (FFv.decode_bytes_garr8 (w_H W) mem5 ap); [| exact Hbt5].
  intros j Hj. rewrite HlV1 in Hj. apply (anp_vis W memc). apply Hav. lia. }
clear Hbt5.
(* ---- run d: +0x0f8 .. +0x118 ---- *)
rewrite P1.
assert (Q2 : YK11.getr regs5 2 = w64 (spZ regs - 32))
  by (transitivity (YK11.getr (ms_regs msC) 2); [exact (HP5 2 ltac:(unfold acallee_saved; lia)) | exact P2]).
assert (Q8 : YK11.getr regs5 8 = w64 ap)
  by (transitivity (YK11.getr (ms_regs msC) 8); [exact (HP5 8 ltac:(unfold acallee_saved; lia)) | exact P8]).
assert (Q9 : YK11.getr regs5 9 = w64 (f + 32))
  by (transitivity (YK11.getr (ms_regs msC) 9); [exact (HP5 9 ltac:(unfold acallee_saved; lia)) | exact P9]).
assert (Q18 : YK11.getr regs5 18 = w64 (SHADOW_OFF + (f + 32) / 8))
  by (transitivity (YK11.getr (ms_regs msC) 18); [exact (HP5 18 ltac:(unfold acallee_saved; lia)) | exact P18]).
assert (KR5 : forall r, In r anp_kregs -> YK11.getr regs5 r = YK11.getr (ms_regs msC) r).
{ intros r Hr. unfold anp_kregs in Hr. apply in_map_iff in Hr as (z & <- & Hz). apply HP5. unfold acallee_saved.
  cbn [In] in Hz. lia. }
(* the shadow byte of f + 32 is 0: its granule's 8 bytes are usable *)
pose proof (Z.div_mod f 8 ltac:(lia)) as Df. rewrite Hf8, Z.add_0_r in Df.
assert (Hsh : shadow_of_addr SHADOW_OFF (f + 39) = SHADOW_OFF + (f + 32) / 8).
{ unfold shadow_of_addr. f_equal. replace (f + 39) with (7 + (f / 8 + 4) * 8) by lia.
  replace (f + 32) with (0 + (f / 8 + 4) * 8) by lia. rewrite !Z.div_add by lia. reflexivity. }
assert (Hm39 : (f + 39) mod 8 = 7).
{ replace (f + 39) with (7 + (f / 8 + 4) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
destruct (Hfra (f + 39) ltac:(lia)) as (s39 & Hs39 & Hok39).
assert (Hs0 : s39 = 0) by (destruct Hok39 as [-> | [Hm Hlt]]; [reflexivity | lia]).
rewrite Hs0 in Hs39.
pose proof (anp_shadow_range (f + 39) ltac:(lia)) as Hsr.
assert (Vs5 : val_mem segs (mrestrict (w_H W) mem5) (SHADOW_OFF + (f + 32) / 8 + 0) 1 0).
{ rewrite Z.add_0_r. apply anp_val1_of_aview. rewrite <- Hsh.
  rewrite K5, KCc by (unfold SHADOW_OFF in *; lia). exact Hs39. }
assert (Vb5 : val_mem segs (mrestrict (w_H W) mem5) (f + 32 + 0) 8 body).
{ rewrite Z.add_0_r. eapply val_mem_kept; [| rewrite <- Ebw; exact Vb].
  intros i Hi. change (Z.of_nat 8) with 8 in Hi. rewrite K5, Kc, Kb3, Kb2, Kb1 by lia. reflexivity. }
pose proof (anp_entry_d W regs5 mem5 f body Q9 Q18 Hfr ltac:(lia) ltac:(unfold SHADOW_OFF; lia) Vs5 Vb5) as HSd.
clear HS. rename HSd into HS.
set (Ed := anp_Ed regs5 body) in HS.
assert (HEId : img_env VAL A_LIM Ed) by apply Eimg_env.
assert (SHOKd : sh_ok segs (SOff 32 0) (@nil shent) Ed (mrestrict (w_H W) mem5)) by constructor.
clear SHOK. rename SHOKd into SHOK.
paj_run_tok RUN HS HJ5 SHOK ANP_B0; [anp_awr_ro|].
match type of HS with context [restrict _ ?msx] => set (msD := msx) in * end.
assert (Kd : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W) (ms_mem msD) x = aview segs (w_H W) mem5 x).
{ intros x Hx. apply (anp_kept_of _ _ _ _ _ (fun _ => False) HFr); [| exact Hx | auto].
  intros a (r & Hr & Ha). unfold ss_anp_d, anp_rg_sh2, anp_rg_f2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
clear HF HFr. rename HG into HGd.
assert (Ed2 : ew Ed 2 = w64 (spZ regs - 32)) by (unfold Ed, anp_Ed; rewrite (can_ew_Eimg_Ereg_nat _ _ 2 2%bv eq_refl); exact Q2).
assert (Ed8 : ew Ed 8 = w64 ap) by (unfold Ed, anp_Ed; rewrite (can_ew_Eimg_Ereg_nat _ _ 8 8%bv eq_refl); exact Q8).
assert (Ed9 : ew Ed 9 = w64 (f + 32)) by (unfold Ed, anp_Ed; rewrite (can_ew_Eimg_Ereg_nat _ _ 9 9%bv eq_refl); exact Q9).
assert (Ed18 : ew Ed 18 = w64 (SHADOW_OFF + (f + 32) / 8))
  by (unfold Ed, anp_Ed; rewrite (can_ew_Eimg_Ereg_nat _ _ 18 18%bv eq_refl); exact Q18).
assert (Ed32 : ew Ed 32 = w64 body) by (unfold Ed, anp_Ed; exact (anp_ew_x _ _ 0 ltac:(unfold A_TEXT; lia))).
assert (Ed3 : ew Ed 3 = w64 (as_gp B))
  by (unfold Ed, anp_Ed; rewrite (can_ew_Eimg_Ereg_nat _ _ 3 3%bv eq_refl), (KR5 3%bv) by anp_kin 3; exact P3).
assert (Ed4 : ew Ed 4 = w64 (as_tp B))
  by (unfold Ed, anp_Ed; rewrite (can_ew_Eimg_Ereg_nat _ _ 4 4%bv eq_refl), (KR5 4%bv) by anp_kin 4; exact P4).
anp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + AA 0x11c)) P1d ltac:(apply codeptr_val; exact HEId).
anp_reg HS (2%bv : bv 5) (w64 (spZ regs - 32)) P2d ltac:(cbn [sv_denot]; rewrite Ed2, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (Z_to_bv 5 2) (w64 (spZ regs - 32)) P2dz ltac:(cbn [sv_denot]; rewrite Ed2, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (3%bv : bv 5) (w64 (as_gp B)) P3d ltac:(cbn [sv_denot]; rewrite Ed3, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (4%bv : bv 5) (w64 (as_tp B)) P4d ltac:(cbn [sv_denot]; rewrite Ed4, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (8%bv : bv 5) (w64 ap) P8d ltac:(cbn [sv_denot]; rewrite Ed8, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (9%bv : bv 5) (w64 (f + 32)) P9d ltac:(cbn [sv_denot]; rewrite Ed9, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (18%bv : bv 5) (w64 (SHADOW_OFF + (f + 32) / 8)) P18d
  ltac:(cbn [sv_denot]; rewrite Ed18, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (ap + 10)) P10d ltac:(cbn [sv_denot]; rewrite Ed8, anp_u64 by lia; reflexivity).
anp_reg HS (Z_to_bv 5 11) (Z_to_bv 64 (body + 24)) P11d ltac:(cbn [sv_denot]; rewrite Ed32, anp_u64 by lia; reflexivity).
pose proof (regs_kept_of_st_ok segs Ed _ _ regs5 _ anp_kregs HS (anp_env_agree _ _) ltac:(vm_compute; reflexivity)) as KRd.
rewrite anp_restrict_regs in KRd.
assert (ESPd : bv_unsigned (YK11.getr (ms_regs msD) (Z_to_bv 5 2)) = spZ regs - 32) by (rewrite P2dz; apply anp_u64; lia).
(* everything outside the frame, the leaf's window and ap .. ap + 10, ap + 24 .. ap + 40 is as at the entry *)
assert (KDd : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 4128 <= x < spZ regs) -> ~ (ap <= x < ap + 10) ->
  ~ (ap + 24 <= x < ap + 40) -> aview segs (w_H W) (ms_mem msD) x = aview segs (w_H W) memc x).
{ intros x Hx H1 H2 H3. rewrite Kd, K5, KCc by lia. reflexivity. }
assert (GB24 : garr8 segs (mrestrict (w_H W) (ms_mem msD)) (body + 24) (map bz (skipn 24 bb))).
{ apply (anp_garr8_kept _ memc); [exact (GB 24%nat ltac:(lia))|].
  intros x Hx. rewrite length_map, length_skipn in Hx.
  pose proof HBO as Hbo. unfold anp_hold, decode_off_win in Hbo. rewrite HFS in Hbo. apply KDd; lia. }
assert (GA10d : garr8 segs (mrestrict (w_H W) (ms_mem msD)) (ap + 10) (map bz (firstn 10 (skipn 10 aj)))).
{ apply (anp_garr8_kept _ memc); [exact GA10|].
  intros x Hx. rewrite length_map, length_firstn, length_skipn, Hlaj in Hx.
  change (Z.of_nat (Nat.min 10 (40 - 10))) with 10 in Hx. apply KDd; lia. }
assert (RAd : range_addressable (aview segs (w_H W) (ms_mem msD)) SHADOW_OFF ap 40).
{ apply (anp_ra_kept _ memc); [| exact Hara]. intros x Hx. pose proof (anp_shadow_range x ltac:(lia)).
  apply KDd; unfold SHADOW_OFF in *; lia. }
assert (RBd : range_addressable (aview segs (w_H W) (ms_mem msD)) SHADOW_OFF body len).
{ apply (anp_ra_kept _ memc); [| exact Hbra]. intros x Hx. pose proof (anp_shadow_range x ltac:(lia)).
  apply KDd; unfold SHADOW_OFF in *; lia. }
assert (Pd : forall a, ap <= a < ap + 40 -> apresent (w_H W) (ms_mem msD) a)
  by (intros a Ha; apply (apresent_grows _ _ _ a HGd); apply Hpres5; exact (Pc a Ha)).
(* ---- call 2: copy_strz (ap + 10, body + 24) ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 LCZ.COPY_STRZ) mm rom) mdx) Q) end.
eapply SRr_bind.
{ eapply (can_leafb_journal B LAWS W (ms_regs msD) (ms_mem msD) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (spZ regs - 32 - sp0) LCZ.COPY_STRZ None [(ap + 10, ap + 10 + 10)]
    (fun m2 => LStp.rw_cells segs m2 (ap + 10)
       [LC.CB 10 (DgnSpec.copy_strz 10 9 (skipn 24 bb) (firstn 10 (skipn 10 aj)))]) HJ5).
  - unfold spZ at 1. first [rewrite ESPd | rewrite P2d, anp_u64 by lia]. lia.
  - Z.div_mod_to_equations. lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite P1d. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold AA, AF_diginet_announce_parse; lia | reflexivity].
  - exact P3d.
  - exact P4d.
  - intros a Ha. unfold LCK.in_wr in Ha. apply Exists_cons in Ha. destruct Ha as [Ha | Ha]; [|inversion Ha].
    cbn [fst snd] in Ha. exact (proj1 (Htwr a ltac:(lia))).
  - intros HPRE.
    pose proof (LEAF0 fx) as LF.
    unfold transport_leaf_wr_at, LCpy.transport_copy_strz_cg in LF.
    specialize (LF lyc Sc W (ms_regs msD) (ms_mem msD) _ (skipn 24 bb) (firstn 10 (skipn 10 aj)) (ap + 10) (body + 24)
      (spZ regs - 32 - 16) HPRE).
    cbv zeta in LF. rewrite ESPd in LF. unfold LCZ.COPY_STRZ_FRAME in LF.
    apply LF; clear LF.
    + exact P10d.
    + exact P11d.
    + lia.
    + rewrite length_skipn. lia.
    + apply (can_leafb_bytes_garr8 W (ms_mem msD) (body + 24) (skipn 24 bb)); [exact GB24 | lia | rewrite length_skipn; lia].
    + apply (FFv.decode_rw_of_garr8 (w_H W) (ms_mem msD) (ap + 10) [LC.CB 10 (firstn 10 (skipn 10 aj))]).
      * cbn [LC.cells_wf LC.cell_wf]. rewrite length_firstn, length_skipn, Hlaj. split; [reflexivity | exact I].
      * lia.
      * cbn. lia.
      * intros i Hi. cbn in Hi. apply Pd. lia.
      * cbn [LC.cells_bytes LC.cbytes]. rewrite app_nil_r. exact GA10d.
    + lia.
    + eapply (can_leafb_stk_journal B); [exact HJ5 | lia | lia].
    + lia.
    + unfold AsanKA.off_stk. rewrite ESPd.
      pose proof HBO as Hbo. unfold anp_hold, decode_off_win in Hbo. rewrite HFS in Hbo. lia.
    + unfold AsanKA.off_stk. rewrite ESPd. left. lia.
    + apply (@can_leafb_app_stack rc). lia.
    + apply (@can_leafb_app_stack rc). lia.
    + exact (can_leafb_asan_cells B HCELLS lyc Sc W (ms_mem msD) _ (proj1 HJ5)).
    + unfold AsanKA.off_stk. rewrite ESPd. left. unfold AsanCells.GOT_CELL_K. lia.
    + unfold AsanKA.off_stk. rewrite ESPd. left. unfold AsanCells.CELL_K. lia.
    + apply (can_leafb_addressable W (ms_mem msD) (body + 24) 9); [eapply range_addressable_sub; [exact RBd | lia | lia]
        | lia | lia | unfold AsanCells.APPMEM_END; lia |].
      intros i Hi. apply HBapp. lia.
    + apply (can_leafb_addressable W (ms_mem msD) (ap + 10) 10); [eapply range_addressable_sub; [exact RAd | lia | lia] | lia | lia
        | unfold AsanCells.APPMEM_END; lia |].
      intros i Hi. unfold AsanCells.app_mem, AsanCells.LOWMEM_END, AsanCells.HIGHMEM_BEG, AsanCells.APPMEM_END. lia.
    + eapply (can_leafb_rng_journal B); [exact HJ5 | lia | lia].
    + exact (proj1 (can_leafb_rng_cells W)).
    + exact (proj2 (can_leafb_rng_cells W)).
    + apply (can_leafb_rng W (body + 24) 9); [lia | lia |]. intros a Ha. apply (anp_vis W memc). apply Hbv. lia.
    + apply (can_leafb_rng_shadow W memc (body + 24) 9); [eapply range_addressable_sub; [exact Hbra | lia | lia] | lia | lia | lia].
    + apply (can_leafb_rng W (ap + 10) 10); [lia | lia |]. intros a Ha. apply (anp_vis W memc). apply Hav. lia.
    + apply (can_leafb_rng_shadow W memc (ap + 10) 10); [eapply range_addressable_sub; [exact Hara | lia | lia] | lia | lia | lia].
    + intros x Hx. unfold LCK.in_wr in Hx. apply Exists_cons in Hx. destruct Hx as [Hx | Hx]; [cbn [fst snd] in Hx | inversion Hx].
      split; [exact (proj1 (proj2 (proj2 (Htwr x ltac:(lia))))) |].
      exact (frm_img segs B LAWS lyc Sc W (ms_mem msD) _ cidA posA x (proj1 HJ5) HinF ltac:(lia)). }
cbv beta.
intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & _ & Heff6 & Hpres6 & HRW6).
assert (K6 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 32 - 4096 <= x < spZ regs - 32) -> ~ (ap + 10 <= x < ap + 20) ->
  aview segs (w_H W) mem6 x = aview segs (w_H W) (ms_mem msD) x).
{ intros x Hx H1 H2. apply Heff6; [exact Hx | unfold spZ; first [rewrite ESPd | rewrite P2d, anp_u64 by lia]; unfold ESTACK; lia |].
  intros Hw. unfold LCK.in_wr in Hw. apply Exists_cons in Hw. destruct Hw as [Hw | Hw]; [cbn [fst snd] in Hw; lia | inversion Hw]. }
destruct HRW6 as [[Hwf6 Hbt6] _]. cbn [LC.cells_wf LC.cell_wf] in Hwf6. destruct Hwf6 as [HlV2 _].
assert (GV2 : garr8 segs (mrestrict (w_H W) mem6) (ap + 10)
  (map bz (DgnSpec.copy_strz 10 9 (skipn 24 bb) (firstn 10 (skipn 10 aj))))).
{ cbn [LC.cells_bytes LC.cbytes] in Hbt6. rewrite app_nil_r in Hbt6.
  apply (FFv.decode_bytes_garr8 (w_H W) mem6 (ap + 10)); [| exact Hbt6].
  intros j Hj. rewrite HlV2 in Hj. apply (anp_vis W memc). apply Hav. lia. }
clear Hbt6.
(* ---- run e: +0x11c .. the `ret` at +0x138 ---- *)
rewrite P1d.
assert (Q2e : YK11.getr regs6 2 = w64 (spZ regs - 32))
  by (transitivity (YK11.getr (ms_regs msD) 2); [exact (HP6 2 ltac:(unfold acallee_saved; lia)) | exact P2d]).
assert (KR6 : forall r, In r anp_kregs -> YK11.getr regs6 r = YK11.getr (ms_regs msD) r).
{ intros r Hr. unfold anp_kregs in Hr. apply in_map_iff in Hr as (z & <- & Hz). apply HP6. unfold acallee_saved.
  cbn [In] in Hz. lia. }
(* the frame, kept by everything since run a *)
assert (KSv : forall x, spZ regs - 32 <= x < spZ regs -> aview segs (w_H W) mem6 x = aview segs (w_H W) (ms_mem msA) x).
{ intros x Hx. rewrite K6, Kd, K5, Kc, Kb3, Kb2, Kb1 by lia. reflexivity. }
assert (S0e : val_mem segs (mrestrict (w_H W) mem6) (spZ regs - 32 + 0) 8 (bv_unsigned (YK11.getr regs 18)))
  by (eapply val_mem_kept; [| exact S0a]; intros i Hi; change (Z.of_nat 8) with 8 in Hi; apply KSv; lia).
assert (S8e : val_mem segs (mrestrict (w_H W) mem6) (spZ regs - 32 + 8) 8 (bv_unsigned (YK11.getr regs 9)))
  by (eapply val_mem_kept; [| exact S8a]; intros i Hi; change (Z.of_nat 8) with 8 in Hi; apply KSv; lia).
assert (S16e : val_mem segs (mrestrict (w_H W) mem6) (spZ regs - 32 + 16) 8 (bv_unsigned (YK11.getr regs 8)))
  by (eapply val_mem_kept; [| exact S16a]; intros i Hi; change (Z.of_nat 8) with 8 in Hi; apply KSv; lia).
assert (S24e : val_mem segs (mrestrict (w_H W) mem6) (spZ regs - 32 + 24) 8 (bv_unsigned (YK11.getr regs 1)))
  by (eapply val_mem_kept; [| exact S24a]; intros i Hi; change (Z.of_nat 8) with 8 in Hi; apply KSv; lia).
pose proof (anp_entry_e W regs6 regs mem6 (spZ regs - 32) Q2e ltac:(lia) ltac:(lia) S0e S8e S16e S24e) as HSe.
clear HS. rename HSe into HS.
set (Ee := anp_Ee regs6 regs) in HS.
assert (HEIe : img_env VAL A_LIM Ee) by apply Eimg_env.
assert (SHOKe : sh_ok segs (SOff 32 0) (@nil shent) Ee (mrestrict (w_H W) mem6)) by constructor.
clear SHOK. rename SHOKe into SHOK.
paj_run_tok RUN HS HJ6 SHOK ANP_B0; [anp_awr_ro|].
match type of HS with context [restrict _ ?msx] => set (msE := msx) in * end.
assert (Ke : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W) (ms_mem msE) x = aview segs (w_H W) mem6 x).
{ intros x Hx. apply (anp_kept_of _ _ _ _ _ (fun _ => False) HFr); [| exact Hx | auto].
  intros a (r & Hr & Ha). unfold ss_anp_e, anp_rg_sv3 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
clear HF HFr.
assert (Ee2 : ew Ee 2 = w64 (spZ regs - 32)) by (unfold Ee, anp_Ee; rewrite (can_ew_Eimg_Ereg_nat _ _ 2 2%bv eq_refl); exact Q2e).
assert (Ee32 : ew Ee 32 = YK11.getr regs 18) by (unfold Ee, anp_Ee; exact (anp_ew_x _ _ 0 ltac:(unfold A_TEXT; lia))).
assert (Ee33 : ew Ee 33 = YK11.getr regs 9) by (unfold Ee, anp_Ee; exact (anp_ew_x _ _ 1 ltac:(unfold A_TEXT; lia))).
assert (Ee34 : ew Ee 34 = YK11.getr regs 8) by (unfold Ee, anp_Ee; exact (anp_ew_x _ _ 2 ltac:(unfold A_TEXT; lia))).
assert (Ee35 : ew Ee 35 = YK11.getr regs 1) by (unfold Ee, anp_Ee; exact (anp_ew_x _ _ 3 ltac:(unfold A_TEXT; lia))).
anp_reg HS (2%bv : bv 5) (YK11.getr regs 2) F2
  ltac:(cbn [sv_denot]; rewrite Ee2, anp_u64 by lia; replace (spZ regs - 32 + 32) with (spZ regs) by lia;
        unfold spZ; apply Z_to_bv_bv_unsigned).
anp_reg HS (1%bv : bv 5) (YK11.getr regs 1) F1 ltac:(cbn [sv_denot]; rewrite Ee35, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (8%bv : bv 5) (YK11.getr regs 8) F8 ltac:(cbn [sv_denot]; rewrite Ee34, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (9%bv : bv 5) (YK11.getr regs 9) F9 ltac:(cbn [sv_denot]; rewrite Ee33, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (18%bv : bv 5) (YK11.getr regs 18) F18 ltac:(cbn [sv_denot]; rewrite Ee32, Z.add_0_r; apply Z_to_bv_bv_unsigned).
anp_reg HS (10%bv : bv 5) (w64 (ann_code cmd len)) F10 ltac:(rewrite Hcode; reflexivity).
pose proof (regs_kept_of_st_ok_pi (PI := PI_transportb) _ _ _ regs6 _ anp_kregs HS (anp_env_agree regs6 _)
  ltac:(vm_compute; reflexivity)) as KRe.
rewrite anp_restrict_regs in KRe.
eapply (paj_ret_at (L := transportb_listing) (PL := PL_transportb) (PI := PI_transportb) W _ _ _ _ _ HS eq_refl
  ltac:(clear; vm_compute; reflexivity)).
intros matE.
(* everything outside the call's window and frame_anp_wr ap is as at the entry *)
assert (KE : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 4128 <= x < spZ regs) -> ~ trans_anp_wr ap x ->
  aview segs (w_H W) (ms_mem msE) x = aview segs (w_H W) memc x).
{ intros x Hx Hw Hn. unfold trans_anp_wr in Hn. rewrite Ke, K6, KDd by lia. reflexivity. }
apply (anp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ap cmd body bb aj _ _ _ LAWS MTL HJ0
  (ajournal_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matE HJ6)).
- rewrite HFS. lia.
- lia.
- exact Hfake.
- intros x Hx Hw Hn. rewrite HFS in Hw. exact (KE x Hx Hw Hn).
- apply anp_preserved; [exact F2 | exact F8 | exact F9 | exact F18 |].
  intros r Hr. rewrite KRe, KR6, KRd, KR5, KRc, KRa by exact Hr. reflexivity.
- exact Hra.
- exact F1.
- exact F10.
- (* the 40 bytes at ap: version, name, the 4 untouched bytes, body, 15 *)
  unfold trans_anp_bytes, trans_anp_cells, ann_ok. fold len. rewrite Hcode. cbn [Z.eqb].
  unfold PAnn.ann_cells, ann_version, ann_name. cbn [LC.cells_bytes LC.cbytes]. rewrite !map_app.
  apply garr8_app. split.
  { apply (anp_garr8_kept _ mem5); [exact GV1|]. intros x Hx. rewrite length_map, HlV1 in Hx.
    change (Z.of_nat 10) with 10 in Hx. rewrite Ke, K6, Kd by lia. reflexivity. }
  rewrite length_map, HlV1. change (Z.of_nat 10) with 10.
  apply garr8_app. split.
  { apply (anp_garr8_kept _ mem6); [exact GV2|]. intros x Hx. rewrite length_map, HlV2 in Hx.
    change (Z.of_nat 10) with 10 in Hx. rewrite Ke by lia. reflexivity. }
  rewrite length_map, HlV2. change (Z.of_nat 10) with 10. replace (ap + 10 + 10) with (ap + 20) by lia.
  apply garr8_app. split.
  { apply (anp_garr8_kept _ memc); [exact GA20|]. intros x Hx.
    rewrite length_map, length_firstn, length_skipn, Hlaj in Hx. change (Z.of_nat (Nat.min 4 (40 - 20))) with 4 in Hx.
    apply KE; unfold trans_anp_wr; lia. }
  rewrite length_map, length_firstn, length_skipn, Hlaj. change (Z.of_nat (Nat.min 4 (40 - 20))) with 4.
  replace (ap + 20 + 4) with (ap + 24) by lia.
  apply garr8_app. split.
  { apply anp_garr8_val8. eapply val_mem_kept; [| exact A24c].
    intros i Hi. change (Z.of_nat 8) with 8 in Hi. rewrite Ke, K6, Kd, K5 by lia. reflexivity. }
  rewrite length_map, LMem.length_le8. change (Z.of_nat 8) with 8. replace (ap + 24 + 8) with (ap + 32) by lia.
  apply garr8_app. split.
  { apply anp_garr8_val8. eapply val_mem_kept; [| exact A32c].
    intros i Hi. change (Z.of_nat 8) with 8 in Hi. rewrite Ke, K6, Kd, K5 by lia. reflexivity. }
  apply garr8_nil.
Qed.

End anpw.

(* The statement for every record B; at the core's record TransportB it is this theorem at that record. *)
Theorem transport_diginet_announce_parse_cg_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms)
    (MT : ameter_ops),
  @transport_diginet_announce_parse_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@anp_holds fx rc B MT). Qed.
