(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* SlostHead: Theorem slost_head : slost_head_stmt (lib/A/Prog/SlostCut.v), the head piece of the walk of
   session_lost on fuzz_transport.asan (0x88f08 = transport_sigma TS_session_lost, AF_session_lost = 0x7ca4 of
   lib/A/Prog/DgnTransportList.v), from the entry to the two cuts slost_ntc_at (+0x17c) and slost_rel_at (+0x230).
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []); the runs are the
   position-abstract runs of lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x:
     run 1   +0x000 .. +0x06c  the frame (`addi sp, sp, -128`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into
                               s1, s4 = why, the flag word through its GOT word (1, so `beq a2, zero` is not taken),
                               s9 = the shadow base, s3 = s, a0 = 160, up to `jal __asan_stack_malloc_2`;
     +0x070                    the class-2 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (the frame F in a0, 4096 <= F);
     run 2a  +0x074 .. +0x0d8  `bne s2, zero` taken (the real-stack arm is not reached), the frame's 24-byte header,
                               s7 = the frame's shadow address;
     run 2b  +0x0dc .. +0x12c  the frame's shadow bytes 0 .. 19 (a run to +0x130);
     run 2c  +0x130 .. +0x174  the frame word at s1 + 16, the checked stores of 0 at s + 212 and s + 168, s5 = s + 112,
                               s10 = its shadow address, the checked load of s11 = S_state; each check reads a shadow
                               byte 0 of g_s's payload (trans_slost_cells, the shadow entries SLH_SH);
     +0x178                    `beq s11, zero`, taken up from a state with no region: S_IDLE runs one instruction to
                               +0x230 and concludes by slost_rel_at (the model's world is slost_w1 Bw:
                               slh_model_idle); any other state runs one instruction to +0x17c and concludes by
                               slost_ntc_at.
   The facts the cuts carry are proved once at +0x178 (slost_cur at that memory, the world relation at slost_w1 Bw, G
   kept outside slost_wr) and moved to the cut's memory, whose view is the same (slh_cur_move). What the call keeps
   (acall_kept_g) runs from the entry to the stack malloc's return (TransportGCg.v dk_kept_step_g, then
   dk_kept_trans_g with the call's acall_kept) and from there over the five written ranges (dk_kept_own_g: the
   frame's header and shadow bytes, the slot s1 + 16 in the call's window, g_s's two fields in G). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg SlostCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition SLH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x070 *)
Definition slh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 94) 0))].
Definition slh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition slh_img_regions : smem := [got_regionP; bcell_regionP 32; slh_got_uar; slh_uar_cell].
Definition slh_regions1 : smem := stack_region SLOST_FRAME :: slh_img_regions.
Definition slh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_slh1 : sstate := mkSS AF_session_lost sr_atoms slh_regions1 None slh_facts1.

(* run 2a, +0x074 .. +0x0d8: after the stack malloc, the frame F in a0 (atom 10); the run writes the frame's 24-byte
   header and stops at the first shadow store. *)
Definition SLH_C1 : Z := AF_session_lost + 0x74.
Definition slh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition slh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_slh2 : sstate := mkSS SLH_C1 sr_atoms [slh_rg_hdr] None slh_facts2.

(* run 2b, +0x0dc .. +0x12c: s7 (atom 23) holds the frame's shadow address; the run writes the frame's shadow bytes
   0 .. 19, up to +0x130. *)
Definition SLH_C2 : Z := AF_session_lost + 0xdc.
Definition SLH_C3 : Z := AF_session_lost + 0x130.
Definition slh_rg_sh : YP09.region := YP09.mkRegion (Some 23%nat) 0 20 0 20 [].
Definition slh_facts3 : facts := mkFacts [(23%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_slh3 : sstate := mkSS SLH_C2 sr_atoms [slh_rg_sh] None slh_facts3.

(* run 2c, +0x130 .. +0x178: the frame word at s1 + 16, the checked stores of 0 at s + 212 and s + 168, the checked
   load of s + 112 (atom 33, the 4 bytes of S_state) and `beq s11, zero`. a0 (atom 10) is s + 212, s3 (atom 19) is s,
   s9 (atom 25) the shadow base. *)
Definition slh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 16 24 [].
Definition slh_rg_st : YP09.region :=
  YP09.mkRegion (Some 19%nat) 112 116 0 0 [YP09.mkChunk 112 (YP09.CVal 4 (SOff 33 0))].
Definition slh_rg_dcv : YP09.region := YP09.mkRegion (Some 19%nat) 168 172 168 172 [].
Definition slh_rg_inf : YP09.region := YP09.mkRegion (Some 19%nat) 212 216 212 216 [].
Definition slh_regions4 : smem := [slh_rg_slot; slh_rg_st; slh_rg_dcv; slh_rg_inf].
Definition slh_facts4 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF (SLOST_S + 212) (SLOST_S + 212) 2);
           (19%nat, mkAF SLOST_S SLOST_S 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_slh4 : sstate := mkSS SLH_C3 sr_atoms slh_regions4 None slh_facts4.
(* The shadow entries of the run's three checks ([s + 112, s + 216) and a0's [s + 212, s + 216)), and the shadow base. *)
Definition SLH_SH : list shent := [mkSHE 19 112 216; mkSHE 10 0 4].
Definition SLH_Bx : sv := SOff 25 0.

(* +0x178, `beq s11, zero`, taken up again from a state with no region: the branch on s11 (atom 27), then a run of
   one instruction to the cut, which writes no byte. *)
Definition SLH_C4 : Z := AF_session_lost + 0x178.
Definition ss_slh5 : sstate := mkSS SLH_C4 sr_atoms [] None (mkFacts [] [] []).

(* ------------------------------------------------------------------ *)
(* The model's world after the two stores                              *)
(* ------------------------------------------------------------------ *)

Lemma slh_w1_eq : forall Bw,
  slost_w1 Bw = TW.upd (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0)) (TW.OFF_g_s + 168) (TW.put 4 0).
Proof. intros Bw. reflexivity. Qed.

(* The two stores keep g_s's state and g_fail_next. *)
Lemma slh_w1_facts : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_state (slost_w1 Bw) = TW.S_state Bw /\ TW.g_fail_next (slost_w1 Bw) = TW.g_fail_next Bw.
Proof.
intros Bw HL.
assert (LZ : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
assert (L1 : Z.of_nat (length (TW.upd Bw TW.A_S_inflight (TW.put 4 0))) = TW.W_LEN).
{ rewrite TWL.length_upd_put; [exact LZ | unfold TW.A_S_inflight, TW.OFF_g_s; lia |].
  rewrite LZ. unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN. lia. }
unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight, TW.S_state, TW.g_fail_next.
split.
- rewrite TWL.s32_at_upd_out;
    [| unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia | unfold TW.A_S_state, TW.OFF_g_s; lia
     | rewrite TWL.length_put; unfold TW.A_S_desk_counter_valid, TW.A_S_state, TW.OFF_g_s; lia
     | rewrite TWL.length_put, L1; unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.W_LEN; lia].
  rewrite TWL.s32_at_upd_out;
    [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia | unfold TW.A_S_state, TW.OFF_g_s; lia
     | rewrite TWL.length_put; unfold TW.A_S_inflight, TW.A_S_state, TW.OFF_g_s; lia
     | rewrite TWL.length_put, LZ; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out;
    [| unfold TW.A_S_desk_counter_valid, TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
     | rewrite TWL.length_put; unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.OFF_g_fail_next; lia
     | rewrite TWL.length_put, L1; unfold TW.A_S_desk_counter_valid, TW.OFF_g_s, TW.W_LEN; lia].
  rewrite TWL.u_at_upd_out;
    [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
     | rewrite TWL.length_put; unfold TW.A_S_inflight, TW.OFF_g_s, TW.OFF_g_fail_next; lia
     | rewrite TWL.length_put, LZ; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* S_IDLE: the model's world is slost_w1 Bw (slost_model's first branch). *)
Lemma slh_model_idle : forall I Fr Bw why Bw', TW.S_state (slost_w1 Bw) = TS0.DIGINET_S_IDLE ->
  TSS.session_lost_m I Fr Bw why = Some (Bw', tt) -> Bw' = slost_w1 Bw.
Proof.
intros I Fr Bw why Bw' Hs Hm. rewrite slost_model in Hm. rewrite (proj2 (Z.eqb_eq _ _) Hs) in Hm.
symmetry. exact (slost_some_inv _ _ Hm).
Qed.

(* The world relation after the stores of 0 at s + 212 and s + 168. *)
Lemma slh_tw_w1 : forall (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_A rd Bw ->
  (forall j, 0 <= j < 4 -> rd' (SLOST_S + 212 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (SLOST_S + 168 + j) = Some 0) ->
  (forall x, tw_in TMAP_A x -> ~ (SLOST_S + 212 <= x < SLOST_S + 216) -> ~ (SLOST_S + 168 <= x < SLOST_S + 172) ->
     rd' x = rd x) ->
  tw_at TMAP_A rd' (slost_w1 Bw).
Proof.
intros rd rd' Bw Hat HI HD HO.
assert (CS : SLOST_S = TA_g_s) by reflexivity.
set (rdm := fun x => if ((SLOST_S + 168 <=? x) && (x <? SLOST_S + 172))%bool then rd x else rd' x).
assert (H1 : tw_at TMAP_A rdm (TW.upd Bw (TW.OFF_g_s + 212) (TW.put 4 0))).
{ apply (tw_write TMAP_A rd rdm Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 212 4 0 TMAP_A_ok Hat TMAP_A_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold rdm. rewrite <- CS.
    assert (Hb : ((SLOST_S + 168 <=? SLOST_S + 212 + Z.of_nat j) && (SLOST_S + 212 + Z.of_nat j <? SLOST_S + 172))%bool
      = false) by (apply andb_false_iff; right; apply Z.ltb_ge; lia).
    rewrite Hb, (HI (Z.of_nat j) ltac:(lia)).
    destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  - intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
    destruct ((SLOST_S + 168 <=? x) && (x <? SLOST_S + 172))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    apply HO; [exact Hx | lia |].
    destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
rewrite slh_w1_eq.
apply (tw_write TMAP_A rdm rd' _ TW.OFF_g_s TA_g_s TW.SZ_g_s 168 4 0 TMAP_A_ok H1 TMAP_A_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS, (HD (Z.of_nat j) ltac:(lia)).
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
- intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
  destruct ((SLOST_S + 168 <=? x) && (x <? SLOST_S + 172))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. apply Hn. lia.
Qed.

(* `beq s11, zero` on the sign-extended state: the model's S_state = 0 test. *)
Lemma slh_eqb0 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma slh_state_range : forall Bw, - 2 ^ 31 <= TW.S_state Bw < 2 ^ 31.
Proof.
intros Bw. pose proof (bv_swrap_in_range 32 (TW.u_at Bw TW.A_S_state 4) ltac:(discriminate)) as R.
change (bv_swrap 32 (TW.u_at Bw TW.A_S_state 4)) with (TW.S_state Bw) in R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma slh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_session_lost = transport_sigma TS_session_lost.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma slh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) slh_img_regions /\
  pairwise_disjoint E slh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct slh_vals as (V1 & V93 & V0 & V94 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (Kguar : rdword (aview segs (w_H W) mem) FCells.GOT_UAR = Some FCells.UAR)
    by (apply (rdword_cell B ly); [unfold FCells.UAR; lia | exact (CH _ I7)]).
  assert (Kuar : rd32 (aview segs (w_H W) mem) FCells.UAR 1).
  { pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6.
    intros k Hk. exact (H6 k Hk). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold FCells.GOT_UAR; lia).
  assert (R94 : 0 <= VAL (A_OBJ 94) < 2 ^ 47) by (rewrite V94; unfold FCells.UAR; lia).
  split.
  - unfold slh_img_regions, got_regionP, bcell_regionP, slh_got_uar, slh_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
      [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 94) 0) (VAL (A_OBJ 94)));
      [cbn [sv_denot]; rewrite E94, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V0, V94. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 94)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r, V94. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold slh_img_regions, got_regionP, bcell_regionP, slh_got_uar, slh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuation at the entry: the 32 registers and the shadow base (atom 32). *)
Definition slh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).

Lemma slh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (slh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold slh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma slh_ew_32 : forall regs, ew (slh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold slh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma slh_ew_obj : forall regs i, (i < 95)%nat -> ew (slh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold slh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma slh_env_img : forall regs, img_env VAL A_LIM (slh_E regs).
Proof. intros regs. unfold slh_E. apply Eimg_env. Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma slh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - SLOST_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (slh_E regs) ss_slh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_session_lost)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_slh1, slh_regions1.
  assert (Usp : bv_unsigned (ew (slh_E regs) 2) = spZ regs)
    by (rewrite (slh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (slh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply slh_ew_32.
  destruct (slh_img_ok ly S W mem md (slh_E regs) HCELLS HAR
    (slh_ew_obj regs 1 ltac:(lia)) (slh_ew_obj regs 93 ltac:(lia))
    (slh_ew_obj regs 0 ltac:(lia)) (slh_ew_obj regs 94 ltac:(lia)) E32) as [HRs HPd].
  destruct slh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew (slh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (slh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold SLOST_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold slh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, slh_got_uar, slh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (slh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (slh_ew_obj regs 93 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (slh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (slh_ew_obj regs 94 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, SLOST_FRAME.
    repeat split; first [exact I | lia].
  - unfold slh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma slh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 256 <= 2 ^ 47 -> F mod 64 = 0 ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (slh_E regs) ss_slh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SLH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R25 Hsp Hsp32 HF0 HFs HF64 Hpframe.
  rewrite restrict_mkst_fx. unfold ss_slh2.
  assert (U2 : bv_unsigned (ew (slh_E regs) 2) = spv)
    by (rewrite (slh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (slh_E regs) 9) = spv)
    by (rewrite (slh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (slh_E regs) 10) = F)
    by (rewrite (slh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (slh_E regs) 25) = SHADOW_OFF)
    by (rewrite (slh_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (slh_E regs) 32) = SHADOW_OFF)
    by (rewrite (slh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold slh_rg_hdr, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold slh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold slh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U25, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma slh_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 23 = w64 SH -> SHADOW_OFF <= SH -> SH + 20 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 20 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (slh_E regs) ss_slh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SLH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R23 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_slh3.
  assert (U23 : bv_unsigned (ew (slh_E regs) 23) = SH)
    by (rewrite (slh_ew_reg regs 23 23%bv eq_refl), R23; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold slh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold slh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold slh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma slh_inG : forall a, SLOST_S <= a < SLOST_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df9c0, 18264). split.
- unfold TG.G_HARNESS. cbn [In]. tauto.
- unfold in_zr, SLOST_S, TA_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* g_s's bytes [s + 112, s + 216) are addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma slh_ra : forall ly S (W : world segs) mem md,
  trans_slost_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (SLOST_S + 112) 104.
Proof.
intros ly S W mem md HZ HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : SLOST_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= SLOST_S + TW.SZ_g_s)
  by (unfold SLOST_S, TA_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md SLOST_S (SLOST_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The valuation of run 2c: the 32 registers at +0x130, the shadow base (atom 32) and the 4 bytes of g_s's state
   (atom 33). *)
Definition slh_E4 (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4)]).

Lemma slh_entry4 : forall ly S (W : world segs) regs mem md Bw spv,
  trans_slost_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  (forall a, spv + 16 <= a < spv + 24 -> apresent (w_H W) mem a) ->
  YK11.getr regs 10 = w64 (SLOST_S + 212) -> YK11.getr regs 19 = w64 SLOST_S ->
  YK11.getr regs 25 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (slh_E4 regs Bw) ss_slh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SLH_C3)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SLH_Bx SLH_SH (slh_E4 regs Bw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw spv HSC HAR Htw R9 Hsp Hsp32 Hpslot R10 R19 R25.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (slh_E4 regs Bw) n = YK11.getr regs r)
  by (intros n r Hn; unfold slh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (slh_E4 regs Bw) 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold slh_E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (slh_E4 regs Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4))
  by (unfold slh_E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (CS : SLOST_S = 6158784) by reflexivity.
assert (U9 : bv_unsigned (ew (slh_E4 regs Bw) 9) = spv)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew (slh_E4 regs Bw) 10) = SLOST_S + 212)
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew (slh_E4 regs Bw) 19) = SLOST_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (slh_E4 regs Bw) 25) = SHADOW_OFF)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U33 : bv_unsigned (ew (slh_E4 regs Bw) 33) = TW.u_at Bw (TW.OFF_g_s + 112) 4)
  by (rewrite E33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_slh4, slh_regions4.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [slh_rg_slot slh_rg_st slh_rg_dcv slh_rg_inf
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ SLOST_S 112 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 112) 4));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    * rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (SLOST_S + o) G_HARNESS_rw).
      apply slh_inG. unfold TW.SZ_g_s. lia.
    * rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (SLOST_S + o) G_HARNESS_rw).
      apply slh_inG. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold slh_rg_slot, slh_rg_st, slh_rg_dcv, slh_rg_inf, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U19. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold slh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U10, U19, U25, U33.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (slh_ra ly S W mem md HSC HAR) as HRA.
  assert (UB : U (slh_E4 regs Bw) SLH_Bx = SHADOW_OFF).
  { unfold U, SLH_Bx. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, SLH_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range segs (w_H W) mem _ SLH_Bx 19 (SLOST_S + 112) 104 SLOST_S 112 216 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range segs (w_H W) mem _ SLH_Bx 10 (SLOST_S + 112) 104 (SLOST_S + 212) 0 4 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U10, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac slh_reg HS r v H tac :=
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
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac slh_region HS i HR :=
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
Ltac slh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac slh_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The awr obligation's regions, computed. *)
Ltac slh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A callee-saved register at the machine state of HS, from the equation Q of its value at the run's start. *)
Ltac slh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    slh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (slh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The same at the state of run 2c's end, whose valuation (ewset over slh_E4) agrees with slh_E4 below atom 1024. *)
Ltac slh_kreg5 HS E5lo EE4 r n Q H :=
  lazymatch type of Q with _ = ?v =>
    slh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (E5lo n ltac:(lia)), (EE4 n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* After the one instruction to a cut (a run from a state with no region): every byte of the view as at +0x178
   (KD), presence grown (GR). *)
Ltac slh_after_cut HS W KD GR m5 msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m5 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m5 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition slh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma slh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* The state at +0x178 with no region. *)
Lemma slh_entry5 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (slh_E regs) ss_slh5
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SLH_C4)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_slh5.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* A region cell of n bytes holding 0, read byte by byte through the view. *)
Lemma slh_aview_of_val0 : forall H (m : word -> option byte) a (n : nat),
  val_mem segs (mrestrict H m) a n 0 -> forall j, 0 <= j < Z.of_nat n -> aview segs H m (a + j) = Some 0.
Proof.
intros H m a n HV j Hj. pose proof (HV (Z.to_nat j) ltac:(lia)) as H0.
rewrite Z2Nat.id in H0 by lia. unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
lazymatch goal with |- context [?f 0 n (Z.to_nat j)] => unfold f end.
rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity.
Qed.

(* The sign-extended 4-byte load of g_s's state is the model's S_state. *)
Lemma slh_sext : forall E Bw, ew E 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.S_state Bw).
Proof.
intros E Bw H. pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 112) 4) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The facts the cuts carry move to a later memory whose view is the same at every address. *)
Lemma slh_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  slost_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((SLOST_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  slost_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b m i Hb Hi Hn. rewrite KD. exact (K2 b m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

Lemma slh_holds : @slost_head_stmt fx rc B MT.
Proof.
unfold slost_head_stmt. intros NTC REL.
unfold transport_session_lost_cg_holds_stmt.
intros HPCS HCELLS HSC HROU HRNE LAWS MTL MTF SMP ASF FFL HGX HGNE ASM0 AI0 NT0.
unfold transport_session_lost_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Htw Hfn Hm Hwhy HTF HROM HAP Hcnt Hev.
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SLOST_STK = 8384) by reflexivity.
assert (FF : SLOST_FRAME = 128) by reflexivity.
assert (CS : SLOST_S = 6158784) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - SLOST_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (slh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (slh_E regs)) by apply slh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (slh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (slh_E regs) 2) = spZ regs)
  by (rewrite (slh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_session_lost)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x000 .. +0x070 *)
paj_run_tok RUN HS HJ SHOK SLH_B0.
{ slh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (can_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia).
assert (E2' : ew (slh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (slh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
slh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 32024)) R1 ltac:(apply codeptr_val; exact HEI).
slh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (slh_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
slh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (slh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
slh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (slh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
slh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
slh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (slh_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
slh_reg HS (19%bv : bv 5) (w64 SLOST_S) R19
  ltac:(cbn [sv_denot]; rewrite (slh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
slh_reg HS (20%bv : bv 5) (w64 why) R20
  ltac:(cbn [sv_denot]; rewrite (slh_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
slh_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) R25
  ltac:(cbn [sv_denot]; rewrite (slh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
slh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) slh_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold slh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) slh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold slh_saved in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(slh_u64 (YK11.getr regs r))).
  apply (can_field_of_region (slh_E regs) _ 2 (spZ regs) _ (-128) 0 (-128) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (slh_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; slh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsk.
(* +0x070: the class-2 stack malloc, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_2)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transport_segs_low SMP SLOST_CID ASM
    ltac:(unfold SLOST_CID; lia) TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 32024)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (SLOST_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ SLOST_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ SLOST_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ SLOST_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes SLOST_CID / 8) with 32 in HFsh.
change (fs_frame_bytes SLOST_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc SLOST_CID pos) in *.
(* the thirteen saved words, kept by the class-2 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) slh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q19 : YK11.getr regs2 19 = w64 SLOST_S)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 why)
  by (transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q25 : YK11.getr regs2 25 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25]).
clear HS.
set (memT := ms_mem ms) in *. set (regsT := ms_regs ms) in *. clearbody memT regsT. clear ms.
(* +0x074 .. +0x0d8: the frame taken, its 24-byte header, s7 = the frame's shadow address. *)
pose proof (slh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q25 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64
  ltac:(intros a Ha; apply Hfpres; lia)) as HS.
assert (HEI2 : img_env VAL A_LIM (slh_E regs2)) by apply slh_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (slh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U10' : bv_unsigned (ew (slh_E regs2) 10) = F)
  by (rewrite (slh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SLH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_tok RUN HS HJ SHOK SLH_B0.
{ slh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SLOST_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SLOST_CID) with 256.
  change (frame_addr lyc SLOST_CID pos) with F. lia. }
clear HEI0 HEI1. rename HF into HF2a, HFr into HFr2a, HG into HG2a.
(* What the call keeps from memc to mem2 (the memory the stack malloc returned). *)
assert (Hwin : forall a, spZ regs - SLOST_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 128 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memT (spZ regs - SLOST_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc memT
    (spZ regs - SLOST_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 128 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros b m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 (spZ regs - SLOST_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W memT W mem2 (spZ regs - SLOST_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* the registers at +0x0dc *)
assert (EF10 : ew (slh_E regs2) 10 = Z_to_bv 64 F) by (rewrite (slh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF25 : ew (slh_E regs2) 25 = Z_to_bv 64 SHADOW_OFF) by (rewrite (slh_ew_reg regs2 25 25%bv eq_refl); exact Q25).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
slh_reg HS (23%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T23
  ltac:(exact (can_denot_shadow (slh_E regs2) 10 25 F SHADOW_OFF EF10 EF25 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
slh_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. slh_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
slh_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. slh_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
slh_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. slh_kreg HS regs2 (19%bv : bv 5) 19%nat Q19 T19.
slh_kreg HS regs2 (20%bv : bv 5) 20%nat Q20 T20. slh_kreg HS regs2 (25%bv : bv 5) 25%nat Q25 T25.
slh_reg HS (24%bv : bv 5) (w64 F) T24
  ltac:(cbn [sv_denot]; rewrite (slh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
slh_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (slh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
(* run 2a wrote the frame's header only *)
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => F <= x < F + 24) HFr2a); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U10' in Hx; lia |]).
  destruct Hin. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* +0x0dc .. +0x12c: the frame's shadow bytes 0 .. 19. *)
pmkst HS.
set (ms3 := ms) in *. clearbody ms3. clear HS.
pose proof (slh_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) T23
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI3 : img_env VAL A_LIM (slh_E (ms_regs ms3))) by apply slh_env_img.
clear HEI. rename HEI3 into HEI.
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (slh_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U23 : bv_unsigned (ew (slh_E (ms_regs ms3)) 23) = SHADOW_OFF + F / 8)
  by (rewrite (slh_ew_reg (ms_regs ms3) 23 23%bv eq_refl), T23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SLH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK SLH_B0 SLH_C3.
{ slh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SLOST_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SLOST_CID / 8) with 32.
  change (frame_addr lyc SLOST_CID pos) with F. unfold shadow_addr. lia. }
match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
(* run 2b wrote the frame's shadow bytes 0 .. 19 only *)
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 20) HFr2b);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U23 in Hx; lia |]).
  destruct Hin. }
pose proof HG2b as G2b. clear HF2b HFr2b HG2b.
(* the registers at +0x130 *)
slh_kreg HS (ms_regs ms3) (2%bv : bv 5) 2%nat T2 V2. slh_kreg HS (ms_regs ms3) (3%bv : bv 5) 3%nat T3 V3.
slh_kreg HS (ms_regs ms3) (4%bv : bv 5) 4%nat T4 V4. slh_kreg HS (ms_regs ms3) (8%bv : bv 5) 8%nat T8 V8.
slh_kreg HS (ms_regs ms3) (9%bv : bv 5) 9%nat T9 V9. slh_kreg HS (ms_regs ms3) (18%bv : bv 5) 18%nat T18 V18.
slh_kreg HS (ms_regs ms3) (19%bv : bv 5) 19%nat T19 V19. slh_kreg HS (ms_regs ms3) (20%bv : bv 5) 20%nat T20 V20.
slh_kreg HS (ms_regs ms3) (23%bv : bv 5) 23%nat T23 V23. slh_kreg HS (ms_regs ms3) (24%bv : bv 5) 24%nat T24 V24.
slh_kreg HS (ms_regs ms3) (25%bv : bv 5) 25%nat T25 V25.
slh_reg HS (10%bv : bv 5) (w64 (SLOST_S + 212)) V10
  ltac:(cbn [sv_denot]; rewrite (slh_ew_reg (ms_regs ms3) 19 19%bv eq_refl), T19; unfold w64;
        rewrite (unsigned_lit_small SLOST_S) by lia; reflexivity).
(* the bytes of G at +0x130 are the entry's *)
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ SLOST_CID pos a HAR2 Hin2 ltac:(change (fs_frame_bytes SLOST_CID) with 256; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (Htw4 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms0)) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (K2b (b + i) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
  rewrite (K2a (b + i) ltac:(lia) ltac:(intros Hx; exact (NGF (b + i) ltac:(lia) Hg))).
  exact (GK2 (b + i) Hg). }
(* +0x130 .. +0x178: the frame word at s1 + 16, the checked stores at s + 212 and s + 168, the checked load of
   s + 112, `beq s11, zero`. *)
pmkst HS.
set (ms4 := ms0) in *. clearbody ms4. clear HS SHOK.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR4.
destruct (slh_entry4 lyc S2 W (ms_regs ms4) (ms_mem ms4) _ Bw sp1 HSC HAR4 Htw4 V9 ltac:(lia) Hsp1al
  ltac:(intros a Ha; apply (slh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia) V10 V19 V25) as [HS SHOK].
clear HEI.
assert (HEI : img_env VAL A_LIM (slh_E4 (ms_regs ms4) Bw)) by (unfold slh_E4; apply Eimg_env).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (slh_E4 (ms_regs ms4) Bw) n = YK11.getr (ms_regs ms4) r)
  by (intros n r Hn; unfold slh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U9c : bv_unsigned (ew (slh_E4 (ms_regs ms4) Bw) 9) = sp1)
  by (rewrite (EE4 9%nat 9%bv eq_refl), V9; apply unsigned_lit_small; lia).
assert (U19c : bv_unsigned (ew (slh_E4 (ms_regs ms4) Bw) 19) = SLOST_S)
  by (rewrite (EE4 19%nat 19%bv eq_refl), V19; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SLH_C3)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ slh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9c in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19c in Ha;
    apply slh_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19c in Ha;
    apply slh_inG; unfold TW.SZ_g_s; lia |].
  apply awr_ok_x_nil. }
rename HF into HF2c, HFr into HFr2c, HG into HG2c.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E5 := EF) in * end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew (slh_E4 (ms_regs ms4) Bw) n)
  by (intros n Hn; unfold E5; rewrite !ew_ewset_other by lia; reflexivity).
(* run 2c wrote the slot s1 + 16 and g_s's fields at s + 168 and s + 212 only *)
assert (K2c : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp1 + 16 <= a < sp1 + 24 \/ SLOST_S + 168 <= a < SLOST_S + 172 \/ SLOST_S + 212 <= a < SLOST_S + 216) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _
    (fun x => sp1 + 16 <= x < sp1 + 24 \/ SLOST_S + 168 <= x < SLOST_S + 172 \/ SLOST_S + 212 <= x < SLOST_S + 216)
    HFr2c); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9c, ?U19c in Hx;
    first [left; lia | right; left; lia | right; right; lia | lia] |]).
  destruct Hin. }
(* the two stores left 0 *)
slh_region HS 2%nat HRd. slh_region HS 3%nat HRi.
assert (U19f : bv_unsigned (ew E5 19) = SLOST_S) by (rewrite E5lo by lia; exact U19c).
assert (ZD5 : forall j, 0 <= j < 4 -> aview segs (w_H W) (ms_mem ms) (SLOST_S + 168 + j) = Some 0).
{ apply (slh_aview_of_val0 (w_H W) (ms_mem ms) (SLOST_S + 168) 4).
  exact (can_field_of_region E5 _ 19 SLOST_S _ 168 172 168 172 168 4%N (SLit 0) 0 HRd U19f ltac:(slh_in) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (ZI5 : forall j, 0 <= j < 4 -> aview segs (w_H W) (ms_mem ms) (SLOST_S + 212 + j) = Some 0).
{ apply (slh_aview_of_val0 (w_H W) (ms_mem ms) (SLOST_S + 212) 4).
  exact (can_field_of_region E5 _ 19 SLOST_S _ 212 216 212 216 212 4%N (SLit 0) 0 HRi U19f ltac:(slh_in) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)). }
clear HRd HRi.
slh_kreg5 HS E5lo EE4 (2%bv : bv 5) 2%nat V2 X2. slh_kreg5 HS E5lo EE4 (3%bv : bv 5) 3%nat V3 X3.
slh_kreg5 HS E5lo EE4 (4%bv : bv 5) 4%nat V4 X4. slh_kreg5 HS E5lo EE4 (8%bv : bv 5) 8%nat V8 X8.
slh_kreg5 HS E5lo EE4 (9%bv : bv 5) 9%nat V9 X9. slh_kreg5 HS E5lo EE4 (18%bv : bv 5) 18%nat V18 X18.
slh_kreg5 HS E5lo EE4 (19%bv : bv 5) 19%nat V19 X19. slh_kreg5 HS E5lo EE4 (20%bv : bv 5) 20%nat V20 X20.
slh_kreg5 HS E5lo EE4 (23%bv : bv 5) 23%nat V23 X23. slh_kreg5 HS E5lo EE4 (24%bv : bv 5) 24%nat V24 X24.
slh_kreg5 HS E5lo EE4 (25%bv : bv 5) 25%nat V25 X25.
assert (E33' : ew E5 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4)).
{ rewrite E5lo by lia. unfold slh_E4. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ _ 1). }
slh_reg HS (27%bv : bv 5) (Z_to_bv 64 (TW.S_state Bw)) X27 ltac:(exact (slh_sext E5 Bw E33')).
slh_reg HS (26%bv : bv 5) (w64 (SHADOW_OFF + (SLOST_S + 112) / 8)) X26
  ltac:(cbn [sv_denot]; rewrite (E5lo 19%nat ltac:(lia)), (E5lo 25%nat ltac:(lia)), (EE4 19%nat 19%bv eq_refl),
        (EE4 25%nat 25%bv eq_refl), V19, V25; unfold w64, SLOST_S, TA_g_s, SHADOW_OFF; vm_compute; reflexivity).
(* ---- the facts both cuts carry, at the memory of +0x178 ---- *)
set (m5 := ms_mem ms) in *.
(* every byte outside the five written ranges is the one the stack malloc left *)
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 16 <= a < sp1 + 24 \/
     SLOST_S + 168 <= a < SLOST_S + 172 \/ SLOST_S + 212 <= a < SLOST_S + 216) ->
  aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2c a Ha ltac:(intros [X | [X | X]]; apply Hn; tauto)).
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros X; apply Hn; tauto)). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG2c). apply (apresent_grows _ _ _ a G2b).
  exact (apresent_grows _ _ _ a G2a Ha). }
assert (Htw2 : tw_at TMAP_A (aview segs (w_H W) mem2) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  apply GK2. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (NGS : forall a, F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 16 <= a < sp1 + 24 ->
  ~ inG TG.G_HARNESS a).
{ intros a [X | [X | X]]; [apply NGF; lia | apply NGH; unfold SHADOW_OFF in *; lia | apply NGH; unfold SHADOW_OFF; lia]. }
(* the world relation at slost_w1 Bw *)
assert (TW5 : tw_at TMAP_A (aview segs (w_H W) m5) (slost_w1 Bw)).
{ apply (slh_tw_w1 (aview segs (w_H W) mem2) (aview segs (w_H W) m5) Bw Htw2 ZI5 ZD5).
  intros x Hx H1 H2.
  assert (Hg : inG TG.G_HARNESS x).
  { destruct Hx as (o & b & n & Hin & Hb). pose proof (TMAP_A_in_G o b n Hin) as HG.
    unfold inG. apply Exists_exists. exists (b, n). split; [exact HG | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS x HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KF5; [lia|]. intros [X | [X | [X | [X | X]]]]; [| | | exact (H2 X) | exact (H1 X)];
  exact (NGS x ltac:(tauto) Hg). }
(* the bytes of G outside the written range *)
assert (GXE5 : gx_kept_ex segs TG.G_HARNESS (slost_wr Bw why) W memc W m5).
{ intros a Hg Hn. rewrite <- (GK2 a Hg).
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KF5; [lia|]. intros [X | [X | [X | [X | X]]]].
  - exact (NGS a ltac:(tauto) Hg).
  - exact (NGS a ltac:(tauto) Hg).
  - exact (NGS a ltac:(tauto) Hg).
  - apply Hn. right; left. unfold twa_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s, TA_g_s. lia.
  - apply Hn. left. unfold twa_fld, TW.A_S_inflight, TW.OFF_g_s, TA_g_s. lia. }
(* what the call keeps, at m5 *)
assert (KG5 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W m5 (spZ regs - SLOST_STK) (spZ regs) (slost_wr Bw why)).
{ apply (acall_kept_g_weaken segs B TG.G_HARNESS lyc Sc W memc W m5 (spZ regs - SLOST_STK) (spZ regs)
    (fun _ => False) (slost_wr Bw why)); [tauto|].
  apply (dk_kept_own_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc S2 W memc mdc mem2 md2 mem2 m5
    (spZ regs - SLOST_STK) (spZ regs) SLOST_CID pos F (flag_addr lyc SLOST_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 16 <= a < sp1 + 24 \/
       SLOST_S + 168 <= a < SLOST_S + 172 \/ SLOST_S + 212 <= a < SLOST_S + 216)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF5].
  - intros a [X | [X | [X | [X | X]]]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes SLOST_CID) with 256. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes SLOST_CID / 8) with 32. lia.
    + left. lia.
    + right; right; right. apply slh_inG. unfold TW.SZ_g_s. lia.
    + right; right; right. apply slh_inG. unfold TW.SZ_g_s. lia.
  - intros a Ha Hn. exact (KF5 a Ha Hn). }
(* the thirteen saved words, at m5 *)
assert (HSV5 : forall (o : Z) (r : bv 5), In (o, r) slh_saved ->
  rdword (aview segs (w_H W) m5) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho. rewrite <- (HSV2 o r Hin).
  apply rdword_ext. intros i Hi. apply KF5; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFW5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SLOST_SAVED).
{ unfold SLOST_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV5 (- o) (Z_to_bv 5 r)); unfold slh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
(* the frame's last word, at m5 *)
assert (HFL5 : rdword (aview segs (w_H W) m5) (F + SLOST_FBYTES - 8) = Some (flag_addr lyc SLOST_CID pos)).
{ rewrite <- Hflag. unfold SLOST_FBYTES. apply rdword_ext. intros i Hi. apply KF5; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  intros [X | [X | [X | [X | X]]]]; [lia | | lia | |].
  - destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
  - exact (NGF (F + 256 - 8 + i) ltac:(lia) (slh_inG (F + 256 - 8 + i) ltac:(unfold TW.SZ_g_s; lia))).
  - exact (NGF (F + 256 - 8 + i) ltac:(lia) (slh_inG (F + 256 - 8 + i) ltac:(unfold TW.SZ_g_s; lia))). }
(* the class-2 frame changed the allocator state's st_fs only *)
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
    ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md5 := md') in * end.
assert (CUR5 : slost_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F lyc S2 W m5 md5 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj KG5 (conj HFW5 HFL5)))))))).
  - rewrite Z.add_0_r. exact HJ.
  - unfold SLOST_EV, NOTICE_EV. lia.
  - rewrite Eab2. apply Permutation_refl. }
(* the record facts and the caller's facts, as the cuts state them *)
assert (HLAWS : slost_laws B MT)
  by exact (conj HPCS (conj HCELLS (conj HSC (conj HROU (conj HRNE (conj LAWS (conj MTL (conj MTF
    (conj SMP (conj ASF (conj FFL (conj HGX HGNE)))))))))))).
assert (HFIX : slost_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why TF Bw Bw' pos sp1 F).
{ unfold slost_fix.
  refine (conj HJe (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj Hsp16 (conj Hlo (conj Hhi
    (conj Htw (conj Hfn (conj Hm (conj Hwhy (conj HTF (conj HROM (conj HAP (conj Hcnt (conj Hev
    (conj _ (conj eq_refl (conj HF0 (conj HF64 (conj HFc HFapp)))))))))))))))))))))))).
  unfold sp1, SLOST_FRAME. replace (spZ regs - 128) with (spZ regs + -128) by lia. reflexivity. }
destruct (slh_w1_facts Bw (tw_len _ _ _ Htw)) as [EST EFN].
assert (D27 : sv_denot (slh_E (ms_regs ms)) (SOff 27 0) = Z_to_bv 64 (TW.S_state Bw))
  by (cbn [sv_denot]; rewrite (slh_ew_reg (ms_regs ms) 27 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X27).
(* +0x178: `beq s11, zero`, from a state with no region *)
pmkst HS.
clear HS SHOK.
pose proof (slh_entry5 W (ms_regs ms) m5) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (slh_E (ms_regs ms)) (mrestrict (w_H W) m5)) by constructor.
assert (HEI5 : img_env VAL A_LIM (slh_E (ms_regs ms))) by apply slh_env_img.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SLH_C4)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOK SLH_B0.
- (* S_state = S_IDLE: to the release cut +0x230 *)
  cbn [branch_taken] in Hc. rewrite D27 in Hc.
  change (sv_denot (slh_E (ms_regs ms)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (slh_eqb0 _ (slh_state_range Bw)) in Hc. apply Z.eqb_eq in Hc.
  assert (HId : TW.S_state (slost_w1 Bw) = TS0.DIGINET_S_IDLE) by (rewrite EST, Hc; reflexivity).
  pose proof (slh_model_idle _ _ _ _ _ HId Hm) as EBw'.
  paj_run_to_tok RUNTO HS HJ SHOK SLH_B0 SLOST_REL.
  { slh_awr_rs. apply awr_ok_x_nil. }
  slh_after_cut HS W KD GR m5 msF.
  slh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat X2 Y2. slh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat X3 Y3.
  slh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat X4 Y4. slh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat X8 Y8.
  slh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat X9 Y9. slh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat X18 Y18.
  slh_kreg HS (ms_regs ms) (23%bv : bv 5) 23%nat X23 Y23. slh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat X24 Y24.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SLOST_REL)) mm rom) mdx) Q) end.
  apply (REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why TF Bw Bw' pos sp1 F lyc S2 W
    (ms_mem msF) _ 0 (ms_regs msF) HFIX).
  + refine (conj (slh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F lyc S2 W m5 md5
      (ms_mem msF) _ 0 CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KD GR) (conj _ _)).
    * rewrite EBw'. apply (tw_kept TMAP_A (aview segs (w_H W) m5)); [exact TW5 | intros x _; exact (KD x)].
    * rewrite EBw', EFN. exact Hfn.
  + unfold slost_regs_rel. refine (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
- (* S_state <> S_IDLE: to the notice cut +0x17c *)
  cbn [branch_taken] in Hc. rewrite D27 in Hc.
  change (sv_denot (slh_E (ms_regs ms)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (slh_eqb0 _ (slh_state_range Bw)) in Hc. apply Z.eqb_neq in Hc.
  assert (HNI : TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE) by (rewrite EST; exact Hc).
  paj_run_to_tok RUNTO HS HJ SHOK SLH_B0 SLOST_NTC.
  { slh_awr_rs. apply awr_ok_x_nil. }
  slh_after_cut HS W KD GR m5 msF.
  slh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat X2 Y2. slh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat X3 Y3.
  slh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat X4 Y4. slh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat X8 Y8.
  slh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat X9 Y9. slh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat X18 Y18.
  slh_kreg HS (ms_regs ms) (23%bv : bv 5) 23%nat X23 Y23. slh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat X24 Y24.
  slh_kreg HS (ms_regs ms) (19%bv : bv 5) 19%nat X19 Y19. slh_kreg HS (ms_regs ms) (20%bv : bv 5) 20%nat X20 Y20.
  slh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat X25 Y25. slh_kreg HS (ms_regs ms) (26%bv : bv 5) 26%nat X26 Y26.
  slh_kreg HS (ms_regs ms) (27%bv : bv 5) 27%nat X27 Y27.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SLOST_NTC)) mm rom) mdx) Q) end.
  apply (NTC HLAWS AI0 NT0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs why TF Bw Bw' pos sp1 F S2
    (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold slost_ntc_cur.
    refine (conj (slh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs why Bw pos F lyc S2 W m5 md5
      (ms_mem msF) _ 0 CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KD GR) (conj Eab2 (conj _ (conj _ HNI)))).
    * intros a Hg Hn. rewrite KD. exact (GXE5 a Hg Hn).
    * apply (tw_kept TMAP_A (aview segs (w_H W) m5)); [exact TW5 | intros x _; exact (KD x)].
  + unfold slost_regs_ntc, slost_regs_rel.
    refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24)))))))
      (conj Y19 (conj Y20 (conj Y25 (conj Y26 _))))).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
    * rewrite EST. exact Y27.
Qed.
End sh.

(* The head piece of the walk of session_lost (SlostCut.v slost_head_stmt), at every machine, run ceiling, record
   and meter. *)
Theorem slost_head : forall fx rc B MT, @slost_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@slh_holds fx rc B MT). Qed.
