(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the cut points of segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a04 .. the jal to check_round_trip at 0x86a38): the states after check_reply, check_arity, check_words and check_refusal, the statements of the five step lemmas between them (statement pass 4: the continuations at every FP state) and their composition, and the message facts the four calls share; the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Kcut.v, in the form of lib/B/Prog/LLVMFuzzerTestOneInput_defs.v (LT_K_stmt, LT_RT_stmt, the LTA forms) and proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (the local statements CL_RC_stmtX, CL_PF_stmtX, CL_FC_stmtX between two program calls, and their composition cl_BX_of_FR0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c verbs_receive_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require HarnessPropsAProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotRec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---- the return points of the four calls (offsets from BASE = 0x86530; listing 0x86a04 .. 0x86a38) ----
   0x86a04 add s7,s3,s4; 0x86a08 sub s8,s6,s4; 0x86a0c addi a0,sp,120; 0x86a10 jal check_reply   -> 0x86a14
   0x86a14 addi a0,sp,120; 0x86a18 jal check_arity                                               -> 0x86a1c
   0x86a1c addi a0,sp,120; 0x86a20 jal check_words                                               -> 0x86a24
   0x86a24 mv a0,s5; 0x86a28 jal check_refusal                                                    -> 0x86a2c
   0x86a2c addi a0,sp,120; 0x86a30 mv a1,s5; 0x86a34 ld a2,112(sp); 0x86a38 jal check_round_trip (LT_RT_stmt)
   No branch, no inline check and no UBSan trap site in between; every abort edge is inside a callee. B keeps
   g_rec.state of before the send in s5 (callee-saved) and g_rec.host_settings in the frame word at sp + 112. *)
Definition LO_K1 : Z := 0x4e4.   (* 0x86a14: after check_reply *)
Definition LO_K2 : Z := 0x4ec.   (* 0x86a1c: after check_arity *)
Definition LO_K3 : Z := 0x4f4.   (* 0x86a24: after check_words *)
Definition LO_K4 : Z := 0x4fc.   (* 0x86a2c: after check_refusal *)

(* ---- the message facts the four checks share: they read the payload and the recorder only ---- *)

Lemma lt_len_le : forall pl n r, lt_len pl n r <= 8192.
Proof. intros pl n r. unfold lt_len, SlotSpec.msg_len. lia. Qed.

Lemma lt_D_shortZ : forall pl n r, Z.of_nat (length (lt_D pl n r)) <= 8192.
Proof. intros pl n r. unfold lt_D. rewrite length_firstn. pose proof (lt_len_le pl n r) as H. lia. Qed.

Lemma lt_D_short : forall pl n r, (length (lt_D pl n r) <= 8192)%nat.
Proof.
intros pl n r. pose proof (lt_D_shortZ pl n r) as H. apply Nat2Z.inj_le.
replace (Z.of_nat 8192) with 8192 by reflexivity. exact H.
Qed.

Lemma lt_declared_nth : forall i, (i < 58)%nat -> declared (nth i rec_codes 0) = true.
Proof.
intros i Hi. unfold declared. apply existsb_exists. exists (nth i rec_codes 0).
split; [apply nth_In; rewrite rec_codes_length; exact Hi | apply Z.eqb_refl].
Qed.

(* the code the loop writes before the send (rec_codes[(flags >> 1) % 58]) is declared *)
Lemma lt_declared : forall pl n r Rh, declared (r_code (lt_R0 pl n r Rh)) = true.
Proof.
intros pl n r Rh. unfold lt_R0, rec_set_rc, SlotSpec.msg_cd. cbn [r_code]. apply lt_declared_nth.
pose proof (Z.mod_pos_bound (SlotSpec.hbyte (lt_hdr pl n r) 0 / 2) 58 ltac:(lia)) as H.
revert H. generalize ((SlotSpec.hbyte (lt_hdr pl n r) 0 / 2) mod 58). intros z H. lia.
Qed.

(* the harness facts of the message (lib/B/Prog/HarnessPropsAProof.v harness_props_holds_a), at the recorder the
   loop hands to send_message: its state (s5) and host settings (the frame word at sp + 112) are 64-bit values *)
Lemma lt_msg_props : forall pl n r Rh, 0 <= r_state Rh < 2 ^ 64 -> 0 <= r_host Rh < 2 ^ 64 ->
  msg_props_at atoi_a reply_code_a (lt_R0 pl n r Rh) (lt_D pl n r).
Proof.
intros pl n r Rh Hs Hh. apply (HarnessPropsAProof.harness_props_holds_a (lt_R0 pl n r Rh) (lt_D pl n r)).
- apply lt_D_short.
- exact Hs.
- exact Hh.
- intros _. apply lt_declared.
Qed.

(* strnlen's result is at most its bound *)
Lemma lt_strnlen_rng : forall n buf, 0 <= n -> 0 <= StrFun.strnlen_res n buf <= n.
Proof.
intros n buf Hn. unfold StrFun.strnlen_res.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:F; [|lia].
destruct (StrFun.find_byte_Some _ _ _ F) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

(* the word count of a message of at most 8192 bytes, against words_of's pointer array (arr_size L0, the
   allocation at 0x867f4) and joined's allocation (join_need ws + 1, check_words' premise) *)
Lemma lt_ws_bounds : forall pl n r,
  let D := lt_D pl n r in let L0 := StrFun.strnlen_res (Z.of_nat (length D)) D in let ws := lt_ws pl n r in
  0 <= L0 <= 8192 /\ 2 * Z.of_nat (length ws) <= L0 + 1 /\ Z.of_nat (length ws) <= 4096 /\
  8 * Z.of_nat (length ws) <= SlotSpec.arr_size L0 /\ join_need ws + 1 <= 8194.
Proof.
intros pl n r D L0 ws.
assert (HL : L0 = Z.of_nat (length (Verbs.upto0 D))) by exact (SlotRec.strnlen_upto0 D _ eq_refl).
assert (HR : 0 <= L0 <= Z.of_nat (length D)) by exact (lt_strnlen_rng (Z.of_nat (length D)) D (Nat2Z.is_nonneg _)).
assert (HD : Z.of_nat (length D) <= 8192) by exact (lt_D_shortZ pl n r).
pose proof (SlotRec.words_count (Verbs.line D)) as HC.
pose proof (SlotRec.line_len D) as HLL.
pose proof (SlotRec.join_need_words (Verbs.line D)) as HJ.
assert (Hws : ws = Verbs.words (Verbs.line D)) by reflexivity.
rewrite <- Hws in HC, HJ.
unfold SlotSpec.arr_size.
clearbody ws L0. clearbody D.
pose proof (Z.div_mod L0 2 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound L0 2 ltac:(lia)) as Hmb.
lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a byte read through the ASan view is a byte *)
Lemma lt_aview_rng : forall (segs : list Segment) H mem a b, aview segs H mem a = Some b -> 0 <= b < 256.
Proof.
intros segs H mem a b E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [x|]; cbn in E; [|discriminate].
injection E as <-. pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

(* a word read through the ASan view is a 64-bit value *)
Lemma lt_rdword_rng : forall (segs : list Segment) H mem a v, rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros segs H mem a v E. unfold rdword in E.
destruct (aview segs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
pose proof (lt_aview_rng _ _ _ _ _ E0). pose proof (lt_aview_rng _ _ _ _ _ E1).
pose proof (lt_aview_rng _ _ _ _ _ E2). pose proof (lt_aview_rng _ _ _ _ _ E3).
pose proof (lt_aview_rng _ _ _ _ _ E4). pose proof (lt_aview_rng _ _ _ _ _ E5).
pose proof (lt_aview_rng _ _ _ _ _ E6). pose proof (lt_aview_rng _ _ _ _ _ E7).
lia.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the registers and the frame word every cut of segment K keeps: s7 (x23) = the next cursor and s8 (x24) = the
   bytes left after the message (0x86a04, 0x86a08), s5 (x21) = g_rec.state before the send, and the frame word at
   sp + 112 = g_rec.host_settings before the send; s3, s4 and s6 are read no more *)
Definition lt_kregs (cx : lcx) (regs : bvmap 5 word) (rd : reader) (r : Z) (Rh : rstate) : Prop :=
  0 < r <= x_n cx /\
  getr regs 23 = w64 (x_p cx + (x_n cx - lt_r' (x_pl cx) (x_n cx) r)) /\
  getr regs 24 = w64 (lt_r' (x_pl cx) (x_n cx) r) /\
  getr regs 21 = w64 (r_state Rh) /\
  0 <= r_state Rh < 2 ^ 64 /\ 0 <= r_host Rh < 2 ^ 64 /\
  rdword rd (x_sp1 cx + LT_HOSTB) = Some (r_host Rh).

(* the harness facts at a cut *)
Lemma lt_kregs_props : forall cx regs rd r Rh, lt_kregs cx regs rd r Rh ->
  msg_props_at atoi_a reply_code_a (lt_R0 (x_pl cx) (x_n cx) r Rh) (lt_D (x_pl cx) (x_n cx) r).
Proof. intros cx regs rd r Rh (_ & _ & _ & _ & Hs & Hh & _). exact (lt_msg_props _ _ r Rh Hs Hh). Qed.

(* the struct words w = sp + 120 the four calls take in a0 are 8-aligned (the entry's sp is 16-aligned, astk_ok) *)
Lemma lt_w_align : forall cx, lt_base B MT cx -> (x_sp1 cx + LT_W) mod 8 = 0.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (Hal & _).
unfold x_sp1, LT_FRAME, LT_W.
pose proof (Z.div_mod (spZ (x_regs cx)) 16 ltac:(lia)) as D. rewrite Hal in D.
replace (spZ (x_regs cx) - 256 + 120) with ((2 * (spZ (x_regs cx) / 16) - 17) * 8) by lia.
apply Z.mod_mul. lia.
Qed.

(* ---- the cut statements: from a return point of segment K to the function's post, under the entry's context, at
   the FP state of the point (statement pass 4: the rounding-mode premise right after lt_base). Each keeps
   LT_K_stmt's facts (the words, the recorder, the budget) with the events of the checks already made moved from
   the budget's rest into k. ---- *)

(* 0x86a14: check_reply returned *)
Definition LT_K1_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O1 : list (Z * Z)) text copy arr (wp : list Z),
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body B cx ly S W regs mem md k m ->
  lt_kregs cx regs (rdW W mem) r Rh ->
  let R0 := lt_R0 (x_pl cx) (x_n cx) r Rh in let D := lt_D (x_pl cx) (x_n cx) r in
  let ws := lt_ws (x_pl cx) (x_n cx) r in
  let '(R1, _, quit) := vr_runA (RecModel.rec_clear R0) D in
  lt_words cx (rdW W mem) D ws text copy arr wp ->
  lt_rec B cx ly S W mem R1 O1 (if quit then 1 else 0) (lt_wblocks D text copy arr) ->
  lt_bud MT cx S k acc (3 + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
    EV_CHECK_ROUND_TRIP R1 ws + ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K1)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x86a1c: check_arity returned *)
Definition LT_K2_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O1 : list (Z * Z)) text copy arr (wp : list Z),
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body B cx ly S W regs mem md k m ->
  lt_kregs cx regs (rdW W mem) r Rh ->
  let R0 := lt_R0 (x_pl cx) (x_n cx) r Rh in let D := lt_D (x_pl cx) (x_n cx) r in
  let ws := lt_ws (x_pl cx) (x_n cx) r in
  let '(R1, _, quit) := vr_runA (RecModel.rec_clear R0) D in
  lt_words cx (rdW W mem) D ws text copy arr wp ->
  lt_rec B cx ly S W mem R1 O1 (if quit then 1 else 0) (lt_wblocks D text copy arr) ->
  lt_bud MT cx S k acc (3 + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
    EV_CHECK_ROUND_TRIP R1 ws + ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K2)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x86a24: check_words returned (joined's block allocated and freed again; the layout may have changed) *)
Definition LT_K3_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O1 : list (Z * Z)) text copy arr (wp : list Z),
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body B cx ly S W regs mem md k m ->
  lt_kregs cx regs (rdW W mem) r Rh ->
  let R0 := lt_R0 (x_pl cx) (x_n cx) r Rh in let D := lt_D (x_pl cx) (x_n cx) r in
  let ws := lt_ws (x_pl cx) (x_n cx) r in
  let '(R1, _, quit) := vr_runA (RecModel.rec_clear R0) D in
  lt_words cx (rdW W mem) D ws text copy arr wp ->
  lt_rec B cx ly S W mem R1 O1 (if quit then 1 else 0) (lt_wblocks D text copy arr) ->
  lt_bud MT cx S k acc (3 + EV_CHECK_REFUSAL +
    EV_CHECK_ROUND_TRIP R1 ws + ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K3)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x86a2c: check_refusal returned *)
Definition LT_K4_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O1 : list (Z * Z)) text copy arr (wp : list Z),
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body B cx ly S W regs mem md k m ->
  lt_kregs cx regs (rdW W mem) r Rh ->
  let R0 := lt_R0 (x_pl cx) (x_n cx) r Rh in let D := lt_D (x_pl cx) (x_n cx) r in
  let ws := lt_ws (x_pl cx) (x_n cx) r in
  let '(R1, _, quit) := vr_runA (RecModel.rec_clear R0) D in
  lt_words cx (rdW W mem) D ws text copy arr wp ->
  lt_rec B cx ly S W mem R1 O1 (if quit then 1 else 0) (lt_wblocks D text copy arr) ->
  lt_bud MT cx S k acc (3 + EV_CHECK_ROUND_TRIP R1 ws + ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K4)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

End e.
End f.
End d.

(* the cut statements at every FP state (the defs' LTA form) *)
Section lta. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing}.
Definition LTA_K1 (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_K1_stmt (fx := fx1) B MT m.
Definition LTA_K2 (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_K2_stmt (fx := fx1) B MT m.
Definition LTA_K3 (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_K3_stmt (fx := fx1) B MT m.
Definition LTA_K4 (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_K4_stmt (fx := fx1) B MT m.
End lta.

(* ---- the step lemmas' statements, at the FP state of their start, with LTA continuations (each proved in its own
   file, with the callee's statement and the walk's facts as Section hypotheses) ---- *)
Section steps. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing}.
(* 0x86a04 .. jal check_reply (0x86a10) and the call: LLVMFuzzerTestOneInput_Kreply.v *)
Definition lt_seg_K0_stmt (B : asyms) (MT : ameter_ops) : Prop := forall m, LTA_K1 B MT m -> LT_K_stmt (fx := fx) B MT m.
(* 0x86a14 .. jal check_arity (0x86a18) and the call: LLVMFuzzerTestOneInput_Karity.v *)
Definition lt_seg_K1_stmt (B : asyms) (MT : ameter_ops) : Prop := forall m, LTA_K2 B MT m -> LT_K1_stmt (fx := fx) B MT m.
(* 0x86a1c .. jal check_words (0x86a20) and the call: LLVMFuzzerTestOneInput_Kwords.v *)
Definition lt_seg_K2_stmt (B : asyms) (MT : ameter_ops) : Prop := forall m, LTA_K3 B MT m -> LT_K2_stmt (fx := fx) B MT m.
(* 0x86a24 .. jal check_refusal (0x86a28) and the call: LLVMFuzzerTestOneInput_Krefusal.v *)
Definition lt_seg_K3_stmt (B : asyms) (MT : ameter_ops) : Prop := forall m, LTA_K4 B MT m -> LT_K3_stmt (fx := fx) B MT m.
(* 0x86a2c .. jal check_round_trip (0x86a38), to check_round_trip's entry: LLVMFuzzerTestOneInput_Krefusal.v *)
Definition lt_seg_K4_stmt (B : asyms) (MT : ameter_ops) : Prop := forall m, LTA_RT B MT m -> LT_K4_stmt (fx := fx) B MT m.
End steps.

(* segment K from its five steps, each at every FP state (a call may return at an FP state of its own) *)
Section compose. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing}.
Lemma lt_seg_K_compose : forall (B : asyms) (MT : ameter_ops),
  (forall fx1 : YK11.FPState, lt_seg_K0_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_K1_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_K2_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_K3_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_K4_stmt (fx := fx1) B MT) ->
  forall m, LTA_RT B MT m -> LT_K_stmt (fx := fx) B MT m.
Proof.
intros B MT K0 K1 K2 K3 K4 m H.
exact (K0 fx m (fun fx1 => K1 fx1 m (fun fx2 => K2 fx2 m (fun fx3 => K3 fx3 m (fun fx4 => K4 fx4 m H))))).
Qed.
End compose.
