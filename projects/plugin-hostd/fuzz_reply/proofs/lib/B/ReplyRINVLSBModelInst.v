(* proves no function (rule 24; kind: model and invariant lemmas) *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, model and invariant lemmas over lib/B/ReplyRINVB.v and lib/B/ReplyLSB.v
   (its Check / Print Assumptions pairs are in the unit's internal record).
   - lf_seg_head_b_fr: lib/B/W_LLVMFuzzerTestOneInput_head.v's SEG_HEAD theorem lf_seg_head_b (:1549) at
     RINV := ReplyRINVB.fr_RINV and LS := ReplyLSB.fr_LS B CALL_ROOM_B, its four model premises RI_head_nout /
     LS_head_nout / RI_head_skip / LS_head_skip (_head.v :274, :275, :278, :281) discharged by ReplyRINVB.RI_head_nout_b
     / RI_head_skip_b and ReplyLSB.LS_head_nout_b / LS_head_skip_b.  Its premises are _head.v's Section variables and
     its three other premises HGnout / HERRNO / HZS (_head.v :260, :263-264, :268-269), text for text; no model
     premise is left.
   - fr_start_b: both invariants at ONE first-head state, for every meter MT and every CALL_ROOM_B (the witnesses
     RI_pro_holds_b and fr_LS_pro_b; pro_m and ls_pro_m are the same model).
   - fr_entry_room_b, fr_start_b_2p33: fr_start_b is NOT vacuous at CALL_ROOM_B := 2 ^ 33 (A's value,
     lib/A/ACfn_cf.v :47).  Its lf_base premise holds only if blocks_bytes (c_S cx) + CALL_ROOM_B <= LIVE_MAX at the
     entry.  At B's own driver's call (lib/B/YD1r.v calls_loop :578-579: the live blocks are the input buffer
     (buf, cap) and, when the payload is not empty, its copy (q, len); :583: 65536 <= cap <= 2 ^ 26; :595:
     0 <= len < cap) the entry's live bytes are cap + len < 2 ^ 27, so with LIVE_MAX = 2 ^ 34 (lib/Reusable/YG01.v
     :225) the room is more than 2 ^ 34 - 2 ^ 27 = 17045651456 >= 2 ^ 33 = 8589934592 (fr_entry_room_b).
     fr_start_b_2p33 then gives both invariants at the first head from lf_base at ANY live-state clause P (the
     contract's own) and that driver split: the fr_live_pre conjunct at 2 ^ 33 is proved, not assumed.  The split is
     the B driver's at the FIRST call; at a later call the entry keeps g_src's table and g_out's buffer
     (lib/A/AD1r_heap_cf.v :1-4), and image B has no cf driver at cb5e14dbcf9 to bound those. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_head.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyRINVB ReplyLSB.
Import ListNotations.
Open Scope Z_scope.

Section chk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* _head.v :230-240, variable for variable *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
(* LS's call room *)
Variable CALL_ROOM_B : Z.
(* _head.v :260, :263-264, :268-269: the three non-model premises, text for text (discharged from
   W_LLVMFuzzerTestOneInput_G.v at the pin, not here) *)
Hypothesis HGnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
Hypothesis HERRNO : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64 /\
  (as_errno B + 4 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= as_errno B).
Hypothesis HZS : exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= rg_s fr_RG /\
  rg_s fr_RG + 4 * ASRC <= fst r + snd r / 8 * 8.
Local Notation LS := (fr_LS B CALL_ROOM_B).
Local Notation RINV := fr_RINV.

(* SEG_HEAD (_cut.v :744) at RINV := fr_RINV, LS := fr_LS B CALL_ROOM_B: no model premise left *)
Theorem lf_seg_head_b_fr : forall cx t W c, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_H B G_fr fr_FP LS RINV cx t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D B G_fr fr_FP LS RINV cx t op W' c') \/
    INV_A B G_fr fr_FP LS RINV 1 cx t W' c' \/
    INV_H B G_fr fr_FP LS RINV cx (t + 1) W' c' \/ INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros cx t W c HB HH.
  eapply lf_seg_head_b.
  all: first [ exact HB | exact HH | exact LAWS | exact HG | exact HGnout | exact HERRNO | exact HZS
             | exact RI_head_nout_b | exact (LS_head_nout_b B CALL_ROOM_B)
             | exact RI_head_skip_b | exact (LS_head_skip_b B CALL_ROOM_B) ].
Qed.
End chk.

(* both invariants at ONE first-head state: pro_m (ReplyRINVB) is ls_pro_m (ReplyLSB) *)
Section start.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma fr_start_b : forall B MT XM_LIB RLO RHI G_fr CALL_ROOM_B cx q T' pj c O cap out ly S,
  lf_base B MT XM_LIB RLO RHI (fun S0 => blocks_bytes S0 + CALL_ROOM_B <= LIVE_MAX) G_fr cx ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_RINV cx 0 (pro_m q T' pj c O cap out) /\ fr_LS B CALL_ROOM_B cx 0 (pro_m q T' pj c O cap out) ly S.
Proof.
  intros B MT XM_LIB RLO RHI G_fr CALL_ROOM_B cx q T' pj c O cap out ly S HB HO H1 H2 H3 H4 HS. split.
  - exact (RI_pro_holds_b B MT XM_LIB RLO RHI _ G_fr cx q T' pj c O cap out HB HO H1 H2 H3 H4).
  - change (pro_m q T' pj c O cap out) with (ls_pro_m q T' pj c O cap out).
    exact (fr_LS_pro_b B CALL_ROOM_B MT XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S HB HS).
Qed.

(* the B driver's entry has 2 ^ 33 bytes of room under LIVE_MAX (lib/B/YD1r.v :579-580, :584, :596; the same
   discharge as lib/B/YD1r.v :647 for YCfn.v :26 LIVE_LIB = 2 ^ 33) *)
Lemma fr_entry_room_b : forall B ly S buf cap q len,
  ((len = 0 /\ q = 0 /\ Permutation (ablocks B ly S) [(buf, cap)]) \/
   (0 < len /\ Permutation (ablocks B ly S) [(buf, cap); (q, len)])) ->
  65536 <= cap <= 2 ^ 26 -> 0 <= len < cap ->
  blocks_bytes S + 2 ^ 33 <= LIVE_MAX.
Proof.
  intros B ly S buf cap q len HBL Hc Hl.
  assert (E : blocks_bytes S = bsum (ablocks B ly S)) by apply blocks_bytes_bsum.
  assert (HL : LIVE_MAX = 17179869184) by reflexivity.
  assert (H33 : 2 ^ 33 = 8589934592) by reflexivity.
  assert (H26 : 2 ^ 26 = 67108864) by reflexivity.
  rewrite E, HL, H33. rewrite H26 in Hc.
  destruct HBL as [(_ & _ & HP) | (_ & HP)]; rewrite (bsum_perm _ _ HP); unfold bsum; cbn [fold_right snd]; lia.
Qed.
(* fr_start_b at CALL_ROOM_B := 2 ^ 33, with its fr_live_pre conjunct proved from the B driver's entry split *)
Lemma fr_start_b_2p33 : forall B MT XM_LIB RLO RHI (P : astate -> Prop) G_fr cx q T' pj c O cap out ly S
    buf dcap dq len,
  lf_base B MT XM_LIB RLO RHI P G_fr cx ->
  ((len = 0 /\ dq = 0 /\ Permutation (ablocks B (c_ly cx) (c_S cx)) [(buf, dcap)]) \/
   (0 < len /\ Permutation (ablocks B (c_ly cx) (c_S cx)) [(buf, dcap); (dq, len)])) ->
  65536 <= dcap <= 2 ^ 26 -> 0 <= len < dcap ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_RINV cx 0 (pro_m q T' pj c O cap out) /\ fr_LS B (2 ^ 33) cx 0 (pro_m q T' pj c O cap out) ly S.
Proof.
  intros B MT XM_LIB RLO RHI P G_fr cx q T' pj c O cap out ly S buf dcap dq len HB HBL Hc Hl HO H1 H2 H3 H4 HS.
  pose proof (fr_entry_room_b B (c_ly cx) (c_S cx) buf dcap dq len HBL Hc Hl) as HR.
  assert (HB' : lf_base B MT XM_LIB RLO RHI (fun S0 => blocks_bytes S0 + 2 ^ 33 <= LIVE_MAX) G_fr cx).
  { destruct HB as (HAI & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _ & P10).
    exact (conj HAI (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj HR P10)))))))))). }
  exact (fr_start_b B MT XM_LIB RLO RHI G_fr (2 ^ 33) cx q T' pj c O cap out ly S HB' HO H1 H2 H3 H4 HS).
Qed.
End start.
