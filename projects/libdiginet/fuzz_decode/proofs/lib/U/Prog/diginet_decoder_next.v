(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the entry part of the UBSan walk of diginet_decoder_next (0x13fe4), and the
   composition of the entry part with the four decode segments into diginet_decoder_next_c.v's contract.
   The entry part runs 0x13fe4-0x14054: the 144-byte frame and the four saves, the NULL tests of d and ev
   (diginet_decode.c:110-111), the alignment check of d, the call of diginet_msg_next on d->c (0x1401c), the test of
   its result (0x14028, :113-114), the memset of the event (0x14038, :115), the alignment check of ev and the memcpy
   of the message into ev + 40 (0x14050, :116). When diginet_msg_next does not return 1 the event is left as it was
   and the function returns its result through the epilogue (0x1429c-0x142b4); otherwise the walk hands DN_DECODE
   to a decode segment (lib/U/Prog/diginet_decoder_next_seg.v), chosen by the model's message: the note
   (diginet_decoder_next_note.v), the system-exclusive (diginet_decoder_next_sysex.v), the fader
   (diginet_decoder_next_fader.v) or the control changes and the other statuses (diginet_decoder_next_cc.v). Each
   segment ends at DN_RET through dn_seg_cont, which `cont` proves with the same epilogue walk (`fin`): the four
   saves at sp - 0x20 lie outside the segments' footprint [sp - 0x90, sp - 0x48).
   Unwalked arms of the entry part: 0x13ffc `beqz a0` and 0x14004 `beqz a1` taken (d or ev NULL, to 0x1429c), not
   taken by the premises d <> 0 and ev <> 0; 0x14010 `bnez` and 0x14040 `bnez` taken (the UBSan alignment checks
   of d and ev, to the unimp at 0x14478), not taken by the premises d mod 8 = 0 and ev mod 8 = 0.
   The segments' continuation says nothing of the bytes of [sp - 0x90, sp - 0x48) but that they stay writable, so
   the contract's stk fact is carried by stk_wmono: in this image every writable segment is readable
   (rsegs_writable_readable, checked on the image), so a byte that stays writable stays readable.
   msg_cells_dmsg_cells is the cell-layout half of the bridge from the callee's reading of a step
   (lib/U/Prog/diginet_msg_next_c.v's msg_cells over FrameSpec's msg_step, now in lib/Spec/DgnLib.v) to this unit's
   (DgnLayout.v's dmsg_cells over the DgnLib.v message): for a step whose code is 1 every field is written, so the
   two cell lists are equal whatever the message held before; dn_msg_next_step is the model half (DgnLib.v's
   diginet_msg_next_msg_step on the decoder's cursor). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step
  Tac ZBridge Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout DgnCellsU
  diginet_cursor_init_c diginet_msg_next_c diginet_decoder_next_c diginet_decoder_next_seg
  memset_c memset memcpy_c memcpy
  diginet_decoder_next_note diginet_decoder_next_cc diginet_decoder_next_fader diginet_decoder_next_sysex
  diginet_msg_next.
Import ListNotations.
Open Scope Z_scope.

(* a step whose code is 1 is a whole sysex or a whole channel message *)
Lemma mr_code_one_kind : forall r, mr_code r = 1 -> mr_kind r = MkSysex \/ mr_kind r = MkChan.
Proof.
  intros r H. unfold mr_code in H. destruct (mr_kind r); auto; discriminate.
Qed.

(* the payload offset of a sysex step is at least 1 (it starts after the F0 at mr_start) *)
Lemma msg_step_sysex_pos : forall bb pos st,
  mr_kind (msg_step bb pos st) = MkSysex -> mr_sysex (msg_step bb pos st) = S pos.
Proof.
  intros bb pos st H. unfold msg_step in *; cbv beta zeta in *.
  destruct (Nat.leb_spec (length bb) pos); [cbn in H; discriminate|].
  destruct (Z.eqb_spec (at8 bb pos) 0xf0).
  - destruct (find_f7 (skipn (S pos) bb)); [reflexivity | cbn in H; discriminate].
  - destruct (Z.leb_spec 0xf0 (at8 bb pos)); [cbn in H; discriminate|].
    destruct (Z.leb_spec 0x80 (at8 bb pos));
      [|destruct (Z.eqb_spec st 0); [cbn in H; discriminate|]];
      unfold chan_step in H; cbv beta zeta in H;
      repeat (match type of H with context [if ?x then _ else _] => destruct x end); cbn in H; discriminate.
Qed.

(* The cell-layout bridge for a step whose code is 1: the callee's msg_cells and this unit's dmsg_cells over the
   model's message agree, whatever the 40 bytes mj held before the call. *)
Lemma msg_cells_dmsg_cells : forall body bb pos st (mj : list byte) (m0 : dgn_msg),
  mr_code (msg_step bb pos st) = 1 ->
  msg_cells body mj (msg_step bb pos st)
  = dmsg_cells body (firstn 4 (skipn 4 mj)) (msg_after (msg_step bb pos st) m0).
Proof.
  intros body bb pos st mj m0 H1.
  pose proof (mr_code_one_kind _ H1) as HK.
  unfold msg_cells, dmsg_cells, msg_after, sysex_ptr, is_end, writes_status, writes_running, writes_len,
    writes_sysex.
  destruct HK as [HK|HK]; rewrite HK; cbv beta iota; cbn [dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len
    dm_offset dm_len].
  - (* MkSysex: the payload offset is S mr_start >= 1, so sysex_ptr is body + it *)
    rewrite (msg_step_sysex_pos bb pos st HK).
    replace (Z.of_nat (S pos) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
  - (* MkChan: no payload, so both give the null pointer *)
    cbv beta iota. reflexivity.
Qed.

(* ---- the stack after a callee ---- *)

Lemma dn_find_segment_in : forall (l : list Segment) x n seg, find_segment l x n = Some seg -> In seg l.
Proof.
  induction l as [|s l IH]; intros x n seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c end.
  - injection H as <-. left. reflexivity.
  - right. exact (IH x n seg H).
Qed.

(* every writable segment of the image is readable *)
Lemma rsegs_writable_readable : forall seg, In seg rsegs -> seg_writable seg = true -> seg_readable seg = true.
Proof.
  intros seg H Hw.
  assert (A : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A seg H). rewrite Hw in A. exact A.
Qed.

(* a byte the program may write it may also read *)
Lemma mrd_of_wview : forall m (x : word), wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x H. unfold mrd. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|].
  unfold wview in H. rewrite E in H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:Hf; [|exfalso; apply H; reflexivity].
  destruct (seg_writable seg) eqn:Hw; [|exfalso; apply H; reflexivity].
  rewrite (rsegs_writable_readable seg (dn_find_segment_in _ _ _ _ Hf) Hw).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base seg)))) as [b|];
    [exists b; reflexivity | exfalso; apply H; reflexivity].
Qed.

(* so a stack region stays a stack region over any run that keeps its bytes writable *)
Lemma stk_wmono : forall m m' lo hi, stk rsegs m lo hi -> wmono rsegs m m' -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) Hw. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa _]. pose proof (Hw _ Hwa) as Hwa'.
  split; [exact Hwa'|]. apply mrd_of_wview. exact Hwa'.
Qed.

(* ---- the model ---- *)

Lemma mr_code_range : forall r, -8 <= mr_code r <= 1.
Proof. intros r. unfold mr_code. destruct (mr_kind r); lia. Qed.

(* 0x14028 `bne a0, a1`: a result other than 1 is another word than 1 *)
Lemma bv_eqb_neq_1 : forall c, -8 <= c <= 1 -> c <> 1 -> negb (bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 1)) = true.
Proof.
  intros c Hc H1. assert (E : bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 1) = false).
  { unfold bv_eqb. rewrite !unsigned_lit_wrap. apply Z.eqb_neq. intros E. Z.div_mod_to_equations. lia. }
  rewrite E. reflexivity.
Qed.

(* diginet_msg_next on the decoder's cursor is fuzz_frame's msg_step *)
Lemma dn_msg_next_step : forall (bb : list byte) (c : dgn_cursor),
  dc_len c = Z.of_nat (length bb) -> 0 <= dc_pos c ->
  diginet_msg_next (map bv_unsigned bb) c dgn_msg_zero =
  (mr_code (msg_step bb (Z.to_nat (dc_pos c)) (dc_status c)),
   msg_after (msg_step bb (Z.to_nat (dc_pos c)) (dc_status c)) dgn_msg_zero,
   cursor_of bb (mr_pos (msg_step bb (Z.to_nat (dc_pos c)) (dc_status c)))
     (mr_st (msg_step bb (Z.to_nat (dc_pos c)) (dc_status c)))).
Proof.
  intros bb [l p s] HL HP. cbn [dc_len dc_pos dc_status] in *. subst l.
  pose proof (diginet_msg_next_msg_step (map bv_unsigned bb) bb (Z.to_nat p) s dgn_msg_zero (holds_body_map bb))
    as E.
  unfold cursor_of at 1 in E. rewrite Z2Nat.id in E by lia. exact E.
Qed.

(* when diginet_msg_next does not return 1, the function returns its result and the decoder's new cursor *)
Lemma dn_step_not_one : forall bb dc r msg c1,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (r, msg, c1) -> r <> 1 ->
  dn_r bb dc = r /\ dn_d bb dc = {| dd_c := c1; dd_p := dd_p dc |}.
Proof.
  intros bb dc r msg c1 H Hr. unfold dn_r, dn_d, dn_step, diginet_decoder_next. rewrite H.
  rewrite (proj2 (Z.eqb_neq r 1) Hr). cbn. split; reflexivity.
Qed.

(* when it returns 1 the function returns 1 on every path *)
Lemma dn_step_one : forall bb dc msg c1,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) -> dn_r bb dc = 1.
Proof.
  intros bb dc msg c1 H. unfold dn_r, dn_step, diginet_decoder_next. rewrite H. cbv beta iota zeta.
  cbn [negb Z.eqb Pos.eqb].
  repeat match goal with
         | |- context [if ?c then _ else _] => destruct c
         | |- context [match ?p with pair _ _ => _ end] => destruct p
         end; reflexivity.
Qed.

(* the zeroed event's first 40 bytes, the cells before its message *)
Definition ev_head (e : dgn_event) : list cell :=
  [ C4 (Z_to_bv 64 (de_kind e));
    C1 (b8 (de_strip e)); C1 (b8 (de_button e)); C1 (b8 (de_zone e)); C1 (b8 (de_on e));
    C1 (b8 (de_right e)); C1 (b8 (de_addr e)); C1 (b8 (de_lsb_missing e)); C1 (b8 0);
    C2 (Z_to_bv 64 (de_value e)); C2 (Z_to_bv 64 (de_delta e)); C2 (Z_to_bv 64 (de_mask e));
    C1 (b8 (de_segments e)); C1 (b8 (de_len e)) ]
  ++ arr_cells 9 (de_text e) ++ arr_cells 8 (de_seg e)
  ++ [ C1 (b8 (de_dots e)); C1 (b8 (de_device e)); C1 (b8 0) ].

Lemma event_cells_head : forall body mpad e, event_cells body mpad e = ev_head e ++ dmsg_cells body mpad (de_msg e).
Proof. intros body mpad e. unfold event_cells, ev_head. rewrite <- !app_assoc. reflexivity. Qed.

Section Walk.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (d ev body lo : Z) (bb cpad ej : list byte) (dc : dgn_decoder).

(* the contract's post *)
Definition DPOST : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (mpad : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (dn_r bb dc)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(d, d + 40); (ev, ev + 80);
           (bv_unsigned sp - DIGINET_DECODER_NEXT_FRAME, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' d (decoder_cells body cpad (dn_d bb dc)) /\
    length mpad = 4%nat /\
    rw_cells rsegs m' ev (if dn_r bb dc =? 1 then event_cells body mpad (dn_e bb dc) else [CB 80 ej]).

(* 0x1429c-0x142b4: a0 = s1, reload ra, s0, s1, s2 from the frame, pop it, return *)
Lemma fin : forall (ra' s0' s2' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m2 (mpad : list byte),
  0 < lo -> lo + 144 <= bv_unsigned sp ->
  rw_cells rsegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp) ->
  munch [(d, d + 40); (ev, ev + 80); (bv_unsigned sp + -144, bv_unsigned sp)] m m2 ->
  wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 d (decoder_cells body cpad (dn_d bb dc)) ->
  length mpad = 4%nat ->
  rw_cells rsegs m2 ev (if dn_r bb dc =? 1 then event_cells body mpad (dn_e bb dc) else [CB 80 ej]) ->
  evt rsegs DPOST
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0' (Z_to_bv 64 (dn_r bb dc))
             a0 a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DN_RET) fc None m2 (seg_rom rsegs)).
Proof.
  intros ra' s0' s2' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 mpad HLO0 HLO FR ST MU WM MI HD HL HE.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  unfold DN_RET.
  do 7 step.
  apply evt_done. unfold DPOST. do 16 eexists. split; [reflexivity|].
  unfold DIGINET_DECODER_NEXT_FRAME. replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact (stk_wmono m m2 lo _ ST WM)|].
  split; [exact HD|]. split; [exact HL|]. exact HE.
Qed.

(* the decode part's continuation: from DN_RET with s1 = 1 the epilogue, the frame's saves untouched by the segment *)
Lemma cont : forall m2 (mpad : list byte),
  0 < lo -> lo + 144 <= bv_unsigned sp ->
  d + 40 <= bv_unsigned sp + -144 \/ bv_unsigned sp <= d ->
  ev + 80 <= bv_unsigned sp + -144 \/ bv_unsigned sp <= ev ->
  rw_cells rsegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp) ->
  munch [(d, d + 40); (ev, ev + 80); (bv_unsigned sp + -144, bv_unsigned sp)] m m2 ->
  wmono rsegs m m2 -> length mpad = 4%nat -> dn_r bb dc = 1 ->
  dn_seg_cont DPOST (bv_unsigned sp + -144) gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 d ev body bb cpad mpad dc.
Proof.
  intros m2 mpad HLO0 HLO Hds Hes FR ST MU WM HL HR1.
  unfold dn_seg_cont. intros ra0 s0' s2' a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 m' MU' WM' MI' HE' HD'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  replace (Z_to_bv 64 1) with (Z_to_bv 64 (dn_r bb dc)) by (rewrite HR1; reflexivity).
  apply fin with (mpad := mpad); try assumption.
  - apply (rw_cells_transport rsegs [(d, d + 40); (ev, ev + 80); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 72)]
             m2 m'); [exact FR | exact MU' | exact WM' | ].
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - apply (munch_trans _ m m2 m' MU). refine (munch_weaken _ _ m2 m' _ MU').
    intros x Hx. cbn [outside] in *. repeat split; lia.
  - exact (wmono_trans rsegs m m2 m' WM WM').
  - rewrite HR1. exact HE'.
Qed.

(* DN_DECODE: the four decode segments, by the model's message *)
Lemma decode : forall m2 (mpad junk2 : list byte) (msg : dgn_msg) (c1 : dgn_cursor)
    (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  diginet_msg_next_contract ->
  0 < lo -> lo + 144 <= bv_unsigned sp ->
  dn_seg_pre m2 (bv_unsigned sp + -144) d ev body bb cpad mpad junk2 dc msg c1 ->
  rw_cells rsegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp) ->
  munch [(d, d + 40); (ev, ev + 80); (bv_unsigned sp + -144, bv_unsigned sp)] m m2 ->
  wmono rsegs m m2 ->
  evt rsegs DPOST
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 d) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DN_DECODE) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 mpad junk2 msg c1 ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HMN HLO0 HLO PRE FR ST MU WM.
  pose proof PRE as (Hmn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _ & _ & _ & _ & Hds & Hes & _ & _).
  pose proof (dn_step_one bb dc msg c1 Hmn) as HR1.
  assert (HL : length mpad = 4%nat) by (destruct HM as [[(_ & _ & _ & _ & HP & _) _] _]; exact HP).
  pose proof (cont m2 mpad HLO0 HLO ltac:(lia) ltac:(lia) FR ST MU WM HL HR1) as K.
  destruct (Z.eq_dec (Z.land (dm_status msg) 0xf0) 0x90) as [N|N].
  { eapply diginet_decoder_next_note_seg; [exact PRE | exact N | exact K]. }
  destruct (Z.eq_dec (dm_status msg) 0xf0) as [X|X].
  { eapply diginet_decoder_next_sysex_seg; [exact PRE | exact X | exact K]. }
  destruct (Z.eq_dec (Z.land (dm_status msg) 0xf0) 0xb0) as [B|B].
  - destruct (Z_lt_dec (dm_d1 msg) 0x20) as [L|L].
    + eapply diginet_decoder_next_fader_seg; [exact HMN | exact PRE | lia | split; assumption | exact K].
    + eapply diginet_decoder_next_cc_seg; [exact PRE | split; [exact X | split; [exact N | right; lia]] | exact K].
  - eapply diginet_decoder_next_cc_seg; [exact PRE | split; [exact X | split; [exact N | left; exact B]] | exact K].
Qed.

End Walk.

Theorem diginet_decoder_next_holds_of : diginet_msg_next_contract -> diginet_decoder_next_contract.
Proof.
  intros HMN0. pose proof HMN0 as HMN. unfold diginet_msg_next_contract in HMN.
  unfold diginet_decoder_next_contract, DIGINET_DECODER_NEXT, DIGINET_DECODER_NEXT_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m d ev body lo bb cpad ej dc
    Hd0 Hev0 Hdal Heval Hspal Hbody Hlen Hpos Hst HBA HD HE Hde Hdb Heb HST Hlo0 Hlo Hdsp Hesp Hbsp HI.
  change (evt rsegs (DPOST ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body lo bb cpad ej dc)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 ev) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fe4) fc None m (seg_rom rsegs))).
  pose proof (dn_msg_next_step bb (dd_c dc) Hlen ltac:(lia)) as HMS.
  pose proof (munch_refl [(d, d + 40); (ev, ev + 80); (bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* the caller's stack as it was, kept out of the kit's transports (which drop a stk fact a callee's footprint
     meets); stk_wmono carries it to the end *)
  assert (HST0 : stk rsegs m lo (bv_unsigned sp) /\ True) by (split; [exact HST | exact I]).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  carve_frame 144%nat HST.
  unfold decoder_cells, cursor_cells in HD. cbn [app] in HD.
  pose proof (rw_cells_bound rsegs m d _ HD) as HDB. cbn [cells_size csize] in HDB.
  pose proof (rw_cells_bound rsegs m ev _ HE) as HEB. cbn [cells_size csize] in HEB.
  pose proof (bytes_at_bound rsegs m body bb HBA) as HBB.
  assert (Ud : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (Uev : bv_unsigned (Z_to_bv 64 ev) = ev) by (apply unsigned_lit; lia).
  assert (L7 : forall x, 0 <= x -> Z.land x 7 = x mod 8)
    by (intros x Hx; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  destruct HST as (HSTlo & HSThi & HSTw).
  assert (Hsplo : lo <= bv_unsigned sp + -144) by lia.
  apply (rw_cells_split_CB rsegs m _ nil 144 junk nil [72;40;8;8;8;8]%nat) in FR; [|reflexivity].
  cbn [app mk_CB_cells firstn skipn] in FR.
  (* 0x13fe4-0x13ff8: the frame, the four saves, s1 = -1 *)
  do 6 step.
  (* 0x13ffc `beqz a0`: d <> 0 *)
  step. unfold bv_eqb; rewrite ?Ud, ?Uev; if_false.
  (* 0x14000 `mv s0, a1`; 0x14004 `beqz a1`: ev <> 0 *)
  step. step. unfold bv_eqb; rewrite ?Ud, ?Uev; if_false.
  (* 0x14008-0x14010: s2 = d, the alignment check of d *)
  step. step. step. unfold bv_eqb; rewrite ?Ud, ?Uev, ?L7, ?(unsigned_lit (d mod 8)), Hdal by lia; if_false.
  (* 0x14014 / 0x14018: a1 = the message at sp' + 0x48, a0 = d *)
  step. step.
  apply rw_cells_split with (cs1 := [CB 72 (firstn 72 junk)]) in FR. destruct FR as [FRlo FR].
  cbn [cells_size csize] in FR.
  apply rw_cells_split with (cs1 := [CB 40 (firstn 40 (skipn 72 junk))]) in FR.
  destruct FR as [FRm FRsave]. cbn [cells_size csize] in FRsave.
  apply rw_cells_split with
    (cs1 := [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (dc_len (dd_c dc)));
             C8 (Z_to_bv 64 (Z.of_nat (Z.to_nat (dc_pos (dd_c dc))))); C1 (b8 (dc_status (dd_c dc)))]) in HD.
  destruct HD as [HDc HDp]. cbn [cells_size csize] in HDp.
  replace (bv_unsigned sp + -144 + Z.of_nat (72 + 0)) with (bv_unsigned sp + -72) in FRm by lia.
  replace (bv_unsigned sp + -144 + Z.of_nat (72 + 0) + Z.of_nat (40 + 0)) with (bv_unsigned sp + -32)
    in FRsave by lia.
  rewrite Hlen in HDc.
  change [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (Z.of_nat (length bb)));
          C8 (Z_to_bv 64 (Z.of_nat (Z.to_nat (dc_pos (dd_c dc))))); C1 (b8 (dc_status (dd_c dc)))]
    with (cursor_cells body (Z.of_nat (length bb)) (Z.to_nat (dc_pos (dd_c dc))) (dc_status (dd_c dc))) in HDc.
  (* 0x1401c: diginet_msg_next (&d->c, &m) over the cursor's 25 bytes and the message's 40 *)
  step.
  eapply evt_cut.
  { eapply HMN; [ exact Hd0 | | exact Hdal | | exact Hbody | | exact Hst | exact HDc | exact HBA | exact FRm
                | | | | exact HI ].
    all: try lia. all: try (Z.div_mod_to_equations; lia). }
  lazymatch goal with H : mem_inv rsegs ?mm |- _ => post_call rsegs mm end.
  remember (msg_step bb (Z.to_nat (dc_pos (dd_c dc))) (dc_status (dd_c dc))) as r eqn:Hr.
  try rewrite <- Hr in HMS; try rewrite <- Hr in POST; try rewrite <- Hr in PC.
  pose proof (mr_code_range r) as RC.
  (* 0x14020 li a1, 1; 0x14024 mv s1, a0; 0x14028 bne a0, a1 *)
  step. step. step.
  destruct (Z.eq_dec (mr_code r) 1) as [C1|C1].
  - rewrite C1. if_false. rewrite C1 in HMS.
    pose proof (dn_step_one bb dc _ _ HMS) as HR1.
    pose proof POST as POSTd. rewrite Hr in C1, POSTd.
    rewrite (msg_cells_dmsg_cells body bb _ _ _ dgn_msg_zero C1) in POSTd.
    rewrite <- Hr in C1, POSTd. clear POST.
    unfold dmsg_cells in POSTd. unfold cursor_cells in PC.
    (* 0x1402c-0x14038: memset (ev, 0, 80) *)
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      eapply evt_cut; [eapply memset_holds | ];
      [ rewrite Uev; replace (Z.to_nat (bv_unsigned (Z_to_bv 64 80))) with 80%nat by (vm_compute; reflexivity);
        exact HE
      | exact MI
      | intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
                    MUc & WMc & MIc & CHc);
        rewrite Uev in MUc, CHc;
        replace (bv_unsigned (Z_to_bv 64 80)) with 80 in MUc, CHc by (vm_compute; reflexivity);
        clear HE; transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc;
        repeat match goal with H : mem_inv rsegs m1 |- _ => clear H end ]
    end.
    replace (ret_pc (Z_to_bv 64 0x1403c)) with (Z_to_bv 64 0x1403c)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    change (Z.to_nat 80) with 80%nat in CHc.
    (* 0x1403c / 0x14040: ev mod 8 = 0 *)
    step. step. unfold bv_eqb; rewrite ?Uev, ?L7, ?(unsigned_lit (ev mod 8)), Heval by lia; if_false.
    (* 0x14044-0x14050: memcpy (ev + 40, &m, 40) *)
    do 4 step.
    replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (b8 0) in CHc
      by (apply bv_eq; vm_compute; reflexivity).
    apply (rw_cells_recast _ _ _ [CB 40 (repeat (b8 0) 40); CB 40 (repeat (b8 0) 40)]) in CHc;
      [ | cbn; repeat split | vm_compute; reflexivity | reflexivity ].
    apply rw_cells_split with (cs1 := [CB 40 (repeat (b8 0) 40)]) in CHc. destruct CHc as [EH0 EH1].
    cbn [cells_size csize Nat.add] in EH1. change (Z.of_nat 40) with 40 in EH1.
    pose proof (proj2 (proj1 POSTd)) as MB. pose proof (proj1 (proj1 POSTd)) as MWF.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      eapply evt_cut; [eapply memcpy_holds | ];
      [ rewrite (unsigned_lit (bv_unsigned sp + -72)) by lia; exact MB
      | rewrite (unsigned_lit 40) by lia; rewrite cells_bytes_length by exact MWF; reflexivity
      | rewrite (unsigned_lit (ev + 40)), (unsigned_lit 40) by lia; exact EH1
      | rewrite (unsigned_lit (ev + 40)), (unsigned_lit 40), (unsigned_lit (bv_unsigned sp + -72)) by lia; lia
      | exact MIc
      | intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                    & m3 & -> & MUc & WMc & MIc' & CPc & MBc);
        rewrite (unsigned_lit (ev + 40)), (unsigned_lit 40) in MUc, CPc by lia;
        clear EH1 MB MBc; transport_after_call rsegs m1 m3 MUc WMc; clear MUc WMc;
        repeat match goal with H : mem_inv rsegs m1 |- _ => clear H end ]
    end.
    replace (ret_pc (Z_to_bv 64 0x14054)) with (Z_to_bv 64 0x14054)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    (* DN_DECODE: the zeroed event with the message at ev + 40, the cursor after the step *)
    assert (HEd : rw_cells rsegs m3 ev (event_cells body (firstn 4 (skipn 4 (firstn 40 (skipn 72 junk))))
                                         (de_set_msg (msg_after r dgn_msg_zero) dgn_event_zero))).
    { rewrite event_cells_head. apply rw_cells_join.
      - apply (rw_cells_recast _ _ _ _ EH0); [cbn; repeat split | vm_compute; reflexivity | reflexivity].
      - apply (rw_cells_recast _ _ _ _ CPc);
          [exact MWF | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity | reflexivity]. }
    assert (HDd : rw_cells rsegs m3 d
                    (decoder_cells body cpad {| dd_c := cursor_of bb (mr_pos r) (mr_st r); dd_p := dd_p dc |})).
    { unfold decoder_cells, cursor_of, cursor_cells. cbn [dd_c dd_p dc_len dc_pos dc_status].
      rewrite Nat2Z.id. apply rw_cells_join; [exact PC | exact HDp]. }
    replace (bv_unsigned sp + -72) with (bv_unsigned sp + -144 + 72) in POSTd by lia.
    eapply decode; [exact HMN0 | lia | lia | | exact FRsave | exact (proj1 HST0) | exact MU | exact WM].
    refine (conj HMS (conj Hd0 (conj Hev0 (conj Hdal (conj Heval (conj _ (conj Hbody (conj Hlen (conj Hpos
             (conj Hst (conj HBA (conj HDd (conj HEd (conj POSTd (conj FRlo (conj Hde (conj Hdb (conj Heb
             (conj _ (conj _ (conj _ MIc'))))))))))))))))))))); first [lia | Z.div_mod_to_equations; lia].
  - destruct (dn_step_not_one bb dc _ _ _ HMS C1) as [ER ED].
    rewrite (bv_eqb_neq_1 _ RC C1). cbv iota.
    replace (Z_to_bv 64 (mr_code r)) with (Z_to_bv 64 (dn_r bb dc)) by (rewrite ER; reflexivity).
    apply fin with (mpad := [b8 0; b8 0; b8 0; b8 0]); [lia | lia | exact FRsave | exact (proj1 HST0) | exact MU
                                                       | exact WM | exact MI | | reflexivity | ].
    + rewrite ED. unfold decoder_cells. cbn [dd_c dd_p]. unfold cursor_of. cbn [dc_len dc_pos dc_status].
      rewrite Nat2Z.id. apply rw_cells_join; [exact PC | exact HDp].
    + rewrite ER, (proj2 (Z.eqb_neq _ _) C1). exact HE.
Qed.

(* the closed walk: diginet_msg_next's own walk (lib/U/Prog/diginet_msg_next.v, relocated from fuzz_frame)
   discharges the callee contract *)
Theorem diginet_decoder_next_holds : diginet_decoder_next_contract.
Proof. exact (diginet_decoder_next_holds_of diginet_msg_next_holds). Qed.
