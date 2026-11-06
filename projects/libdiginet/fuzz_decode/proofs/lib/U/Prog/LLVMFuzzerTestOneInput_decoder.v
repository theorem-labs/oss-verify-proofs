(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the decoder loop of LLVMFuzzerTestOneInput on the UBSan image (fuzz_decode.ubsan,
   fuzz_decode.c:324-339), from the cut 0x12e8c (the cursor loop has left) to the cut 0x13384 (the decoder loop has
   left) of LLVMFuzzerTestOneInput_mid.v, an evt walk over the contracts of its callees: llvm_decoder_evt.
   - The set-up 0x12e8c-0x12f0c (dec_setup, dec_tail): sel % 3 as x - 3 (x * 0xab >> 9) with x = sel & 0xff
     (0x12e8c-0x12eac, `subw`), whose low byte is x mod 3 (LLVMFuzzerTestOneInput_declib.v desk_sub), so the UBSan
     check 0x12ebc of DESK + 4 (sel % 3) (DESK = 0x103d8, a constant) is not taken in any of the three cases; the
     `lw` of DESK[sel % 3] from the image (0x12ec4); diginet_personality_of at 0x12ec8; diginet_decoder_init (&d, p,
     body, len) at 0x12edc with d at sp + 0x108; then s7 = 0, a0 = a2 = 0, s3 = sp + 0x50, s9 = 1, s10 = 13,
     s11 = 0x90, s8 = 0xb0, s0 = 0x1f, `sd (body != 0), 0x10(sp)` (0x12f08), s4 = -1. The walk does not use which
     personality p is: every check of the loop passes for every personality.
   - The loop head 0x12f10 after k passes (dec_head): a0 = st, a2 = pos, s7 = k <= len, the decoder at sp + 0x108 is
     decoder_cells of a model decoder whose cursor stands at pos <= len with a running status st_ok st.
   - One pass (dec_pass, dec_latch): the inlined owed_at 0x12f10-0x131cc is the hypothesis owed_segment (proved in
     its own file): it leaves owed_cells of owed_at body len pos st at o = sp + 0x18; then memset (&ev, 0, 80) at
     0x131d8 (ev = sp + 0x90), rd = diginet_decoder_next (&d, &ev) at 0x131e4, check_events_step (body, &o, rd, &ev)
     at 0x131f8 and, when o.m.code is 1, check_events_fields (body, &o, &ev) at 0x13210. By
     DgnAgreeDecoder.decoder_step_ok (declib dec_pass_model) rd is the code of owed_at's step, both checks hold, and
     the decoder's cursor moves to owed_at's next place and status. The loop leaves at 0x13218 when the code is 0;
     else it takes at = o.next (`ld` 0x80(sp)), status = o.status_out (`lbu` 0x88(sp)), s7 += 1, and goes back to
     the head while len >=u s7 (0x13228), else to 0x13384 (0x1322c). dec_loop: by induction on len - k.
   - The exits build the cut at 0x13384 (dec_exit): the 376 bytes at sp + 0x10 are joined again. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0d.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import
  DgnSpec DgnLib DgnDecHarness DgnAgreeCursor DgnAgreeDecoder.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout DgnCellsU
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_mid LLVMFuzzerTestOneInput_declib
  memset_c diginet_personality_of_c diginet_decoder_init_c diginet_decoder_next_c
  check_events_step_c check_events_fields_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* The walk of the inlined owed_at, 0x12f10 to 0x131cc: from the loop head with a0 = status, a2 = pos, the 120 bytes
   of struct owed o at sp + 0x18, the 56 bytes of struct spec_msg lsb at sp + 0x150 and (body != 0) at sp + 0x10, to
   0x131cc with o holding owed_cells of owed_at, every register the rest of the pass reads as it was, and the memory
   changed only in o, lsb and the 48 bytes of spec_msg_step's frame below sp. *)
Definition owed_segment : Prop :=
  forall (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 gp tp : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Sp lo body pos status : Z) (bb j120 j56 : list byte) (Q : machine_state -> Prop),
    0 <= lo -> lo + 8192 <= Sp -> Sp mod 16 = 0 -> Sp + 496 <= 2 ^ 47 ->
    4096 <= body -> body + Z.of_nat (length bb) <= lo ->
    0 <= pos < 2 ^ 64 -> 0 <= status < 2 ^ 64 ->
    stk rsegs m lo Sp -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
    rw_cells rsegs m (Sp + 0x18) [CB 120 j120] ->
    rw_cells rsegs m (Sp + 0x150) [CB 56 j56] ->
    rw_cells rsegs m (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word)
            (m' : word -> option byte) (p1 p2 j56' : list byte),
       munch [(Sp + 0x18, Sp + 0x90); (Sp + 0x150, Sp + 0x188); (Sp - 48, Sp)] m m' ->
       wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo Sp ->
       rw_cells rsegs m' (Sp + 0x18)
         (owed_cells p1 p2 (owed_at (map bz bb) (Z.of_nat (length bb)) pos (status mod 256))) ->
       rw_cells rsegs m' (Sp + 0x150) [CB 56 j56'] ->
       rw_cells rsegs m' (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
       evt rsegs Q (MS (mkR y1 (Z_to_bv 64 Sp) gp tp y5 y6 y7 (Z_to_bv 64 0x1f)
            (Z_to_bv 64 (Z.of_nat (length bb))) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 body)
            (Z_to_bv 64 (Sp + 0x50)) (Z_to_bv 64 (2 ^ 64 - 1)) y21 y22 x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1)
            (Z_to_bv 64 13) (Z_to_bv 64 0x90) y28 y29 y30 y31)
            F (Z_to_bv 64 0x131cc) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 (Z_to_bv 64 0x1f) (Z_to_bv 64 (Z.of_nat (length bb)))
        (Z_to_bv 64 status) x11 (Z_to_bv 64 pos) x13 x14 x15 x16 x17 (Z_to_bv 64 body) (Z_to_bv 64 (Sp + 0x50))
        (Z_to_bv 64 (2 ^ 64 - 1)) x21 x22 x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1) (Z_to_bv 64 13) (Z_to_bv 64 0x90)
        x28 x29 x30 x31)
        F (Z_to_bv 64 0x12f10) fc None m (seg_rom rsegs)).

(* ---- tactics of the walk ---- *)

(* a disjointness or a footprint inclusion of concrete intervals *)
Local Ltac sizes := rewrite ?decoder_cells_size, ?owed_cells_size, ?event_cells_size;
  cbn [disjoint_from cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
Local Ltac djs := sizes; repeat split; first [exact I | lia].
Local Ltac subfp := unfold sub_fp; intros ?x; cbn [outside]; intros [? _]; repeat split; first [exact I | lia].

(* after a call with footprint MU from m to m': each fact about m outside the footprint is a fact about m'; the
   others (and the old mem_inv) are dropped *)
Local Ltac trc m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at rsegs m ?A ?bs |- _ =>
      first [ apply (bytes_at_transport rsegs W m m' A bs) in H; [ | exact MU | djs ] | clear H ]
  | H : rw_cells rsegs m ?A ?cs |- _ =>
      first [ apply (rw_cells_transport rsegs W m m' A cs) in H; [ | exact MU | exact WM | djs ] | clear H ]
  | H : ro_cells rsegs m ?A ?cs |- _ => clear H
  | H : stk rsegs m ?l ?h |- _ =>
      first [ apply (stk_transport_disjoint rsegs W m m' l h) in H; [ | exact MU | exact WM | djs ] | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ subfp | exact MU ] ]
  | H : wmono rsegs ?mq m |- _ => apply (wmono_trans rsegs mq m m') in H; [ | exact WM ]
  | H : mem_inv rsegs m |- _ => clear H
  end.

(* the return address after a call *)
Local Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* mid_inv from its seven facts in the context *)
Local Ltac mkmid := unfold mid_inv; repeat (split; [assumption|]); assumption.

(* the sum of two literals in the goal, for the address of the `lw` of DESK[sel % 3] *)
Local Ltac lit_fold :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in
      change (Z.add a b) with v
  end.

Section Dec.
Context (OWED : owed_segment) (PO : diginet_personality_of_contract) (DI : diginet_decoder_init_contract)
  (DN : diginet_decoder_next_contract) (IMS : memset_contract) (CES : check_events_step_contract)
  (CEF : check_events_fields_contract).
Variables (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (sv : list cell) (Sp lo buf nn body : Z)
  (bb : list byte) (m0 : word -> option byte).
Hypothesis ENV : mid_env sv Sp lo buf nn body bb.

Local Abbreviation QD := (mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_DECODER_OUT).

(* the facts of mid_env the walk uses; the alignment of sp is kept from lia *)
Lemma env_facts : 0 <= lo /\ lo + 8192 <= Sp /\ dl_al16 Sp /\ Sp + 496 <= 2 ^ 47 /\ 4096 <= body /\
  body + Z.of_nat (length bb) <= lo.
Proof.
  destruct ENV as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & _).
  unfold ALLOC_STACK, LLVM_FRAME, mid_len, dl_al16 in *. repeat split; lia.
Qed.

(* the machine state at the loop head 0x12f10 after k passes *)
Definition dec_head (k : Z) (ms : machine_state) : Prop :=
  exists (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) (m : word -> option byte)
         (pos st : Z) (d : dgn_decoder) (j0 j18 j90 je0 jc j150 cpad : list byte),
    ms = MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 (Z_to_bv 64 0x1f) (Z_to_bv 64 (Z.of_nat (length bb)))
               (Z_to_bv 64 st) x11 (Z_to_bv 64 pos) x13 x14 x15 x16 x17 (Z_to_bv 64 body) (Z_to_bv 64 (Sp + 0x50))
               (Z_to_bv 64 (2 ^ 64 - 1)) x21 x22 (Z_to_bv 64 k) (Z_to_bv 64 0xb0) (Z_to_bv 64 1) (Z_to_bv 64 13)
               (Z_to_bv 64 0x90) x28 x29 x30 x31)
            F (Z_to_bv 64 0x12f10) fc None m (seg_rom rsegs) /\
    0 <= k <= Z.of_nat (length bb) /\ 0 <= pos <= Z.of_nat (length bb) /\ st_ok st /\
    dd_c d = DgnCursor (Z.of_nat (length bb)) pos st /\
    mid_inv sv Sp lo buf body bb m0 m /\
    rw_cells rsegs m Sp [CB 8 j0] /\ rw_cells rsegs m (Sp + 0x10) [C8 (Z_to_bv 64 1)] /\
    rw_cells rsegs m (Sp + 0x18) [CB 120 j18] /\ rw_cells rsegs m (Sp + 0x90) [CB 80 j90] /\
    rw_cells rsegs m (Sp + 0xe0) [CB 40 je0] /\ rw_cells rsegs m (Sp + 0x108) (decoder_cells body cpad d) /\
    rw_cells rsegs m (Sp + 0x130) [CB 32 jc] /\ rw_cells rsegs m (Sp + 0x150) [CB 56 j150].

(* the cut 0x13384 *)
Lemma dec_exit : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 : word) m j0 j10 j18 j90 je0 j108 jc j150,
  mid_inv sv Sp lo buf body bb m0 m ->
  rw_cells rsegs m Sp [CB 8 j0] -> rw_cells rsegs m (Sp + 16) [CB 8 j10] ->
  rw_cells rsegs m (Sp + 24) [CB 120 j18] -> rw_cells rsegs m (Sp + 144) [CB 80 j90] ->
  rw_cells rsegs m (Sp + 224) [CB 40 je0] -> rw_cells rsegs m (Sp + 264) [CB 40 j108] ->
  rw_cells rsegs m (Sp + 304) [CB 32 jc] -> rw_cells rsegs m (Sp + 336) [CB 56 j150] ->
  QD (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 x8 (Z_to_bv 64 (Z.of_nat (length bb))) x10 x11 x12 x13 x14 x15 x16
            x17 (Z_to_bv 64 body) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13384) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m
    j0 j10 j18 j90 je0 j108 jc j150 MI C0 C10 C18 C90 Ce0 C108 C130 C150.
  destruct (join376 m Sp j10 j18 j90 je0 j108 jc j150 C10 C18 C90 Ce0 C108 C130 C150) as [j1 J].
  unfold mid_at. exists x1, x5, x6, x7, x8, x10, x11, x12, x13, x14, x15, x16, x17, x19, x20, x21, x22, x23, x24,
    x25, x26, x27, x28, x29, x30, x31, m, j0, j1.
  split; [reflexivity|]. split; [exact MI|]. split; [exact C0 | exact J].
Qed.

(* 0x13218 to the next loop head or to the cut 0x13384: beqz on o.m.code, the latch, bgeu len, s7 *)
Lemma dec_latch : forall k c (o : owed) (d : dgn_decoder)
    (r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r21 r22 r28 r29 r30 r31 : word) m p1 p2 j0 j90 je0 jc j150 cpad,
  (k + 1 <= Z.of_nat (length bb) -> forall ms', dec_head (k + 1) ms' -> evt rsegs QD ms') ->
  0 <= k <= Z.of_nat (length bb) -> c = sm_code (ow_m o) -> -8 <= c <= 1 ->
  (c <> 0 -> 0 <= ow_next o <= Z.of_nat (length bb)) -> st_ok (ow_status_out o) ->
  dd_c d = DgnCursor (Z.of_nat (length bb)) (ow_next o) (ow_status_out o) ->
  mid_inv sv Sp lo buf body bb m0 m ->
  rw_cells rsegs m Sp [CB 8 j0] -> rw_cells rsegs m (Sp + 16) [C8 (Z_to_bv 64 1)] ->
  rw_cells rsegs m (Sp + 24) (owed_cells p1 p2 o) -> rw_cells rsegs m (Sp + 144) [CB 80 j90] ->
  rw_cells rsegs m (Sp + 224) [CB 40 je0] -> rw_cells rsegs m (Sp + 264) (decoder_cells body cpad d) ->
  rw_cells rsegs m (Sp + 304) [CB 32 jc] -> rw_cells rsegs m (Sp + 336) [CB 56 j150] ->
  evt rsegs QD (MS (mkR r1 (Z_to_bv 64 Sp) gp tp r5 r6 r7 (Z_to_bv 64 31) (Z_to_bv 64 (Z.of_nat (length bb)))
      (Z_to_bv 64 c) r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 body) (Z_to_bv 64 (Sp + 80))
      (Z_to_bv 64 (2 ^ 64 - 1)) r21 r22 (Z_to_bv 64 k) (Z_to_bv 64 176) (Z_to_bv 64 1) (Z_to_bv 64 13)
      (Z_to_bv 64 144) r28 r29 r30 r31) F (Z_to_bv 64 0x13218) fc None m (seg_rom rsegs)).
Proof.
  intros k c o d r1 r5 r6 r7 r11 r12 r13 r14 r15 r16 r17 r21 r22 r28 r29 r30 r31 m p1 p2 j0 j90 je0 jc j150 cpad
    IH Hk Hc SC ON OSO HD MI C0 C10 HO C90 Ce0 C108 C130 C150.
  pose proof env_facts as (E0 & E1 & E2 & E3 & E4 & E5).
  assert (OSB : 0 <= ow_status_out o < 256) by (unfold st_ok in OSO; lia).
  (* 0x13218: beqz a0, the exit when o.m.code = 0 *)
  step. rewrite (dl_eqb64 c 0) by lia.
  destruct (Z.eqb_spec c 0) as [Z0 | Z0]; cbv beta iota.
  - destruct (rw_cells_forget _ _ _ _ C10) as [j10 C10']. cbn [cells_size csize Nat.add] in C10'.
    destruct (rw_cells_forget _ _ _ _ HO) as [j18 HO']. rewrite owed_cells_size in HO'.
    destruct (rw_cells_forget _ _ _ _ C108) as [j108 C108']. rewrite decoder_cells_size in C108'.
    apply evt_done. eapply dec_exit; eassumption.
  - specialize (ON Z0).
    assert (HOu : ro_cells rsegs m (Sp + 24) (owed_cells p1 p2 o)) by exact (proj1 HO).
    unfold owed_cells, spec_msg_cells, spec_event_cells, arr_cells in HOu. cbn [map seq app] in HOu.
    (* 0x1321c ld a2, 0x80(sp) (o.next); 0x13220 lbu a0, 0x88(sp) (o.status_out); 0x13224 s7 += 1 *)
    do 3 step. rewrite (dl_zxb8 (ow_status_out o)) by lia. clear HOu.
    (* 0x13228: bgeu s1, s7 *)
    step. rewrite dl_ltu by lia.
    destruct (rw_cells_forget _ _ _ _ HO) as [j18 HO']. rewrite owed_cells_size in HO'.
    destruct (Z.ltb_spec (Z.of_nat (length bb)) (k + 1)) as [B | B]; cbv beta iota delta [negb].
    + (* 0x1322c: j 0x13384 *)
      step.
      destruct (rw_cells_forget _ _ _ _ C10) as [j10 C10']. cbn [cells_size csize Nat.add] in C10'.
      destruct (rw_cells_forget _ _ _ _ C108) as [j108 C108']. rewrite decoder_cells_size in C108'.
      apply evt_done. eapply dec_exit; eassumption.
    + apply IH; [lia|]. unfold dec_head. do 17 eexists. exists (ow_next o), (ow_status_out o), d.
      do 7 eexists. split; [reflexivity|].
      split; [lia|]. split; [lia|]. split; [exact OSO|]. split; [exact HD|]. split; [exact MI|].
      repeat (split; [eassumption|]). eassumption.
Qed.

(* one pass, from the loop head 0x12f10 to 0x13218 *)
Lemma dec_pass : forall k ms,
  (k + 1 <= Z.of_nat (length bb) -> forall ms', dec_head (k + 1) ms' -> evt rsegs QD ms') ->
  dec_head k ms -> evt rsegs QD ms.
Proof.
  intros k ms IH (x1 & x5 & x6 & x7 & x11 & x13 & x14 & x15 & x16 & x17 & x21 & x22 & x28 & x29 & x30 & x31 & m
    & pos & st & d & j0 & j18 & j90 & je0 & jc & j150 & cpad & -> & Hk & Hp & Hst & Hd
    & (M1 & M2 & M3 & M4 & M5 & M6 & M7) & C0 & C10 & C18 & C90 & Ce0 & C108 & C130 & C150).
  pose proof env_facts as (E0 & E1 & E2 & E3 & E4 & E5).
  unfold LLVM_FRAME in M6.
  assert (Hst' : 0 <= st < 256) by (unfold st_ok in Hst; lia).

  (* 0x12f10-0x131cc: the inlined owed_at *)
  apply (OWED x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 (Z_to_bv 64 k) x28 x29 x30 x31 gp tp F fc m Sp lo body
    pos st bb j18 j150 QD).
  all: try first [ exact E2 | assumption | lia ].
  intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 m1 p1 p2 j56 MU WM MI1 ST1 HO HL H10.
  rewrite (Z.mod_small st 256 Hst') in HO.
  trc m m1 MU WM. clear MU WM.
  pose proof (owed_facts (map bz bb) (Z.of_nat (length bb)) pos st (Forall_bz bb) ltac:(lia) ltac:(lia) Hst)
    as (OM & OK & OL & OS & OSO & ON).
  pose proof (sms_facts (map bz bb) (Z.of_nat (length bb)) pos st (Forall_bz bb) ltac:(lia) ltac:(lia) Hst)
    as (SC & SS & SX & SL & _).
  rewrite <- OM in SC, SS, SX, SL. clear OM.
  pose proof (dec_pass_model bb d pos st Hd) as (HR & HEV & HD').
  remember (owed_at (map bz bb) (Z.of_nat (length bb)) pos st) as o eqn:Ho. clear Ho.

  (* 0x131cc-0x131d8: memset (&ev, 0, 80) *)
  do 4 step.
  eapply evt_cut.
  { eapply IMS with (junk := j90); [rewrite !unsigned_lit by lia; exact C90 | exact MI1]. }
  intros ms' POST. unfold memset_post in POST.
  destruct POST as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU & WM & MI2 & HE).
  rewrite ?unsigned_lit in MU, HE by lia.
  change (Z.to_nat 80) with 80%nat in HE. change (0 mod 256) with 0 in HE.
  fix_ret. trc m1 m2 MU WM. clear MU WM.

  (* 0x131dc-0x131e4: rd = diginet_decoder_next (&d, &ev) *)
  do 3 step.
  eapply evt_cut.
  { eapply DN with (body := body) (lo := lo) (bb := bb) (cpad := cpad) (ej := repeat (Z_to_bv 8 0) 80) (dc := d).
    all: rewrite ?Hd; cbn [dc_len dc_pos dc_status]; unfold DIGINET_DECODER_NEXT_FRAME;
         rewrite ?unsigned_lit by lia.
    all: first [ assumption | exact E2 | (apply dl_al16_8; [exact E2 | reflexivity]) | lia ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & mpad & -> & MU & WM & MI3 & ST3 & HD3
    & HMP & HE3).
  unfold DIGINET_DECODER_NEXT_FRAME in MU. rewrite ?unsigned_lit in MU, ST3 by lia.
  fix_ret. trc m2 m3 MU WM. clear MU WM.
  rewrite HR in HE3 |- *.

  destruct (Z.eq_dec (sm_code (ow_m o)) 1) as [C1 | C1].
  - (* o.m.code = 1: a message, its event *)
    rewrite C1 in HE3 |- *. change (1 =? 1) with true in HE3. cbv beta iota in HE3.
    rewrite HR in HEV. unfold events_step_ok in HEV. cbn [es_o es_rd es_ev] in HEV. rewrite C1 in HEV.
    apply andb_true_iff in HEV as [HCS HCF]. change (1 =? 1) with true in HCF. cbn [implb] in HCF.

    (* 0x131e8-0x131f8: check_events_step (body, &o, rd, &ev) *)
    do 5 step.
    eapply evt_cut.
    { eapply CES with (b := body) (o := Sp + 24) (e := Sp + 144) (rd := 1) (lo := lo) (ow := o) (ev := dn_e bb d)
        (p1 := p1) (p2 := p2) (mpad := mpad).
      all: unfold OW_SIZE, DE_SIZE, CHECK_EVENTS_STEP_FRAME; rewrite ?unsigned_lit by lia.
      all: first [ exact HCS | exact (proj1 HO) | exact (proj1 HE3) | assumption
                 | (apply dl_al16_8; [exact E2 | reflexivity]) | (intros HS; specialize (SX HS); lia) | lia ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU & WM & MI4 & ST4).
    unfold CHECK_EVENTS_STEP_FRAME in MU. rewrite ?unsigned_lit in MU, ST4 by lia.
    fix_ret. trc m3 m4 MU WM. clear MU WM.

    (* 0x131fc lw a0, 0x18(sp) (o.m.code); 0x13200 bne a0, s9 *)
    assert (HOu : ro_cells rsegs m4 (Sp + 24) (owed_cells p1 p2 o)) by exact (proj1 HO).
    unfold owed_cells, spec_msg_cells, spec_event_cells, arr_cells in HOu. cbn [map seq app] in HOu.
    step. rewrite C1, (dl_sx32 1) by lia. clear HOu.
    step. rewrite bv_eqb_refl. cbv beta iota delta [negb].

    (* 0x13204-0x13210: check_events_fields (body, &o, &ev) *)
    do 4 step.
    eapply evt_cut.
    { eapply CEF with (b := body) (o := Sp + 24) (e := Sp + 144) (lo := lo) (bb := bb) (ow := o) (ev := dn_e bb d)
        (p1 := p1) (p2 := p2) (mpad := mpad).
      all: unfold OW_SIZE, DE_SIZE, CHECK_EVENTS_FIELDS_FRAME; rewrite ?unsigned_lit by lia.
      all: first [ exact HCF | exact (proj1 HO) | exact (proj1 HE3) | assumption
                 | (apply dl_al16_8; [exact E2 | reflexivity]) | (intros HS; specialize (SX HS); lia)
                 | (intros _; lia) | lia ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MU & WM & MI5 & ST5).
    unfold CHECK_EVENTS_FIELDS_FRAME in MU. rewrite ?unsigned_lit in MU, ST5 by lia.
    fix_ret. trc m4 m5 MU WM. clear MU WM.

    (* 0x13214 lw a0, 0x18(sp) (o.m.code) *)
    assert (HOu : ro_cells rsegs m5 (Sp + 24) (owed_cells p1 p2 o)) by exact (proj1 HO).
    unfold owed_cells, spec_msg_cells, spec_event_cells, arr_cells in HOu. cbn [map seq app] in HOu.
    step. rewrite C1, (dl_sx32 1) by lia. clear HOu.
    destruct (rw_cells_forget _ _ _ _ HE3) as [j90' HE']. rewrite event_cells_size in HE'. clear HE3.
    eapply (dec_latch k 1 o (dn_d bb d)).
    all: first [ exact IH | exact OSO | exact HD' | lia | (intros HZ; specialize (ON ltac:(lia)); lia)
               | (lazymatch goal with |- mid_inv _ _ _ _ _ _ _ _ => mkmid end) | eassumption ].

  - (* o.m.code <> 1: no event; ev keeps the zeros of the memset *)
    replace (sm_code (ow_m o) =? 1) with false in HE3 by (symmetry; apply Z.eqb_neq; exact C1).
    cbv beta iota in HE3.
    pose proof (event_zero_cells m3 (Sp + 144) body HE3) as HEZ.

    (* 0x131e8-0x131f8: check_events_step (body, &o, rd, &ev) *)
    do 5 step.
    eapply evt_cut.
    { eapply CES with (b := body) (o := Sp + 24) (e := Sp + 144) (rd := sm_code (ow_m o)) (lo := lo) (ow := o)
        (ev := dgn_event_zero) (p1 := p1) (p2 := p2) (mpad := repeat (Z_to_bv 8 0) 4).
      all: unfold OW_SIZE, DE_SIZE, CHECK_EVENTS_STEP_FRAME; rewrite ?unsigned_lit by lia.
      all: first [ (apply ces_nomsg; [reflexivity | exact C1]) | exact (proj1 HO) | exact HEZ | assumption
                 | (apply dl_al16_8; [exact E2 | reflexivity]) | (intros HS; specialize (SX HS); lia) | lia ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU & WM & MI4 & ST4).
    unfold CHECK_EVENTS_STEP_FRAME in MU. rewrite ?unsigned_lit in MU, ST4 by lia.
    fix_ret. clear HEZ. trc m3 m4 MU WM. clear MU WM.

    (* 0x131fc lw a0, 0x18(sp) (o.m.code); 0x13200 bne a0, s9 to 0x13218 *)
    assert (HOu : ro_cells rsegs m4 (Sp + 24) (owed_cells p1 p2 o)) by exact (proj1 HO).
    unfold owed_cells, spec_msg_cells, spec_event_cells, arr_cells in HOu. cbn [map seq app] in HOu.
    step. rewrite (dl_sx32 (sm_code (ow_m o))) by lia. clear HOu.
    step. rewrite (dl_eqb64 (sm_code (ow_m o)) 1) by lia.
    replace (sm_code (ow_m o) =? 1) with false by (symmetry; apply Z.eqb_neq; exact C1).
    cbv beta iota delta [negb].
    eapply (dec_latch k (sm_code (ow_m o)) o (dn_d bb d)).
    all: first [ exact IH | exact OSO | exact HD' | reflexivity | lia
               | (intros HZ; specialize (ON HZ); lia)
               | (lazymatch goal with |- mid_inv _ _ _ _ _ _ _ _ => mkmid end) | eassumption ].
Qed.

(* the loop, by induction on the passes left *)
Lemma dec_loop : forall n k ms,
  (Z.to_nat (Z.of_nat (length bb) - k) <= n)%nat -> dec_head k ms -> evt rsegs QD ms.
Proof.
  induction n as [|n IHn]; intros k ms Hn H.
  - apply (dec_pass k ms); [intros Hk; exfalso; lia | exact H].
  - apply (dec_pass k ms); [| exact H]. intros Hk ms' H'. apply (IHn (k + 1) ms'); [lia | exact H'].
Qed.

(* 0x12ec8 to the loop head: diginet_personality_of, diginet_decoder_init, the loop registers *)
Lemma dec_tail : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 : word) m j0 j10 j18 j90 je0 j108 jc j150,
  mid_inv sv Sp lo buf body bb m0 m ->
  rw_cells rsegs m Sp [CB 8 j0] -> rw_cells rsegs m (Sp + 16) [CB 8 j10] ->
  rw_cells rsegs m (Sp + 24) [CB 120 j18] -> rw_cells rsegs m (Sp + 144) [CB 80 j90] ->
  rw_cells rsegs m (Sp + 224) [CB 40 je0] -> rw_cells rsegs m (Sp + 264) [CB 40 j108] ->
  rw_cells rsegs m (Sp + 304) [CB 32 jc] -> rw_cells rsegs m (Sp + 336) [CB 56 j150] ->
  evt rsegs QD (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 x8 (Z_to_bv 64 (Z.of_nat (length bb))) x10 x11 x12 x13 x14
      x15 x16 x17 (Z_to_bv 64 body) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x12ec8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m
    j0 j10 j18 j90 je0 j108 jc j150 (M1 & M2 & M3 & M4 & M5 & M6 & M7) C0 C10 C18 C90 Ce0 C108 C130 C150.
  pose proof env_facts as (E0 & E1 & E2 & E3 & E4 & E5).
  unfold LLVM_FRAME in M6.
  (* 0x12ec8: p = diginet_personality_of (DESK[sel % 3]) *)
  step.
  eapply evt_cut; [eapply PO|].
  intros ms' (a1' & ->). fix_ret.
  (* 0x12ecc-0x12edc: diginet_decoder_init (&d, p, body, len) *)
  do 5 step.
  eapply evt_cut.
  { eapply DI with (lo := lo) (dj := j108).
    all: unfold DIGINET_DECODER_INIT_FRAME; rewrite ?unsigned_lit by lia.
    all: first [ apply pers_cases | assumption | (apply dl_al16_8; [exact E2 | reflexivity]) | lia ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU & WM & MI1 & ST1 & HD1).
  unfold DIGINET_DECODER_INIT_FRAME in MU. rewrite ?unsigned_lit in MU, ST1 by lia.
  fix_ret. trc m m1 MU WM. clear MU WM.
  (* 0x12ee0-0x12f0c: s7 = 0, a0 = 0, a2 = 0, s3 = sp + 0x50, s9 = 1, s10 = 13, s11 = 0x90, s8 = 0xb0, s0 = 0x1f,
     (body != 0) at sp + 0x10, s4 = -1 *)
  do 10 step. rewrite (dl_snez body) by lia.
  step. step. rewrite dl_m1.
  apply (dec_loop (Z.to_nat (Z.of_nat (length bb) - 0)) 0); [lia|].
  unfold dec_head. do 17 eexists.
  exists 0, 0, (diginet_decoder_init (diginet_personality_of (bv_unsigned x10)) (Z.of_nat (length bb))).
  do 7 eexists. split; [reflexivity|].
  split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|].
  split; [mkmid|].
  repeat (split; [eassumption|]). eassumption.
Qed.

(* the set-up from the cut 0x12e8c to 0x12ec8 *)
Lemma dec_setup : forall ms,
  mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_CURSOR_OUT ms -> evt rsegs QD ms.
Proof.
  intros ms (x1 & x5 & x6 & x7 & x8 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x22 & x23
    & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m & j0 & j1 & -> & MI & C0 & C1).
  pose proof env_facts as (E0 & E1 & E2 & E3 & E4 & E5).
  destruct (carve376 m Sp j1 C1) as (j10 & j18 & j90 & je0 & j108 & jc & j150 & C10 & C18 & C90 & Ce0 & C108
    & C130 & C150).
  clear C1.
  pose proof MI as (M1 & _).
  unfold LLVM_PC_CURSOR_OUT, mid_len.
  pose proof (bv_unsigned_in_range 64 x8) as R8. unfold bv_modulus in R8. change (2 ^ Z.of_N 64) with (2 ^ 64) in R8.
  (* 0x12e8c andi a0, s0, 0xff: x = sel & 0xff *)
  step.
  remember (Z.land (bv_unsigned x8) 255) as X eqn:HX.
  assert (XB : 0 <= X < 256).
  { rewrite HX. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
    apply Z.mod_pos_bound. lia. }
  (* 0x12e90-0x12eb4: a0 = x * 0xab >> 9 = x / 3; s0 = sel - 3 (x / 3) (subw); a1 = (s0 & 0xff) << 2 = 4 (x mod 3) *)
  do 10 step.
  rewrite (unsigned_lit X) by lia. rewrite (unsigned_lit (X * 171)) by lia. rewrite (div3_byte X XB).
  rewrite (unsigned_lit (X / 3)) by lia. rewrite (desk_sub (bv_unsigned x8) X HX R8).
  rewrite (unsigned_lit (X mod 3)) by lia.
  assert (K : X mod 3 = 0 \/ X mod 3 = 1 \/ X mod 3 = 2) by lia.
  destruct K as [K | [K | K]]; rewrite K;
    [change (Z.shiftl 0 2) with 0 | change (Z.shiftl 1 2) with 4 | change (Z.shiftl 2 2) with 8].
  (* 0x12eb8 not a2, a0; 0x12ebc bltu a2, a1: the UBSan check of DESK + 4 (sel % 3) is not taken; 0x12ec0 add a0,
     a0, a1; 0x12ec4 lw a0, 0(a0): DESK[sel % 3] from the image *)
  all: step; step; if_false; step; lit_fold; step; eapply dec_tail; eassumption.
Qed.

End Dec.

(* The decoder loop of LLVMFuzzerTestOneInput on the UBSan image, from the cut 0x12e8c to the cut 0x13384. *)
Lemma llvm_decoder_evt :
  owed_segment ->
  diginet_personality_of_contract -> diginet_decoder_init_contract -> diginet_decoder_next_contract ->
  memset_contract -> check_events_step_contract -> check_events_fields_contract ->
  forall F fc gp tp sv Sp lo buf nn body bb m0 ms,
    mid_env sv Sp lo buf nn body bb ->
    mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_CURSOR_OUT ms ->
    evt rsegs (mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_DECODER_OUT) ms.
Proof.
  intros OWED PO DI DN IMS CES CEF F fc gp tp sv Sp lo buf nn body bb m0 ms ENV AT.
  eapply dec_setup; eassumption.
Qed.
