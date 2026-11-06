(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: segment D of the UBSan walk of diginet_decoder_next (lib/U/Prog/
   diginet_decoder_next_seg.v cuts the walk at DN_DECODE = 0x14054): the fader, status & 0xf0 = 0xb0 with d1 < 0x20,
   from DN_DECODE to DN_RET = 0x1429c (src/diginet_decode.c:130-145), the one segment with a second call of
   diginet_msg_next. Its contract (lib/U/Prog/diginet_msg_next_c.v) is a premise of the lemma.
   - 0x14054-0x14068, 0x140a4-0x140a8, 0x141d0-0x141d8, 0x141dc-0x141e4: kind = OTHER (0x14064 `sw a2, 0(s0)`), and
     the note, sysex, control-change and d1 tests, decided by the path condition;
   - 0x141e8-0x141fc: kind = FADER (`sw s1, 0(s0)`, s1 = 1), strip = d1 (`sb a0, 4(s0)`), value = d2 << 3
     (`sh a1, 0xc(s0)`; for a byte d2 the model's u16 is the identity) (:131-134);
   - 0x14200-0x1421c: the 32 bytes of d->c to the peek cursor at sp + 0x28 (four ld / sd pairs). The fourth word holds
     c->status and the cursor's 7 padding bytes cpad: fd_dec_merge reads that pair of cells as one word, and
     fd_peek_split cuts the frame's 72 scratch bytes into the LSB message (sp + 0, 40 bytes), the cursor's 25 bytes
     (cursor_cells) and the padding (sp + 0x41), so that the callee's footprint is exactly its two objects;
   - 0x14220-0x14228: diginet_msg_next (peek cursor, LSB message), whose result the model reads through
     DgnLib.v diginet_msg_next_msg_step (fd_step) (:135-137);
   - 0x1422c, 0x1423c, 0x1424c: the three tests of :138 (result 1, lsb.status & 0xf0 = 0xb0, lsb.d1 = 0x20 + m.d1;
     LSB fields from msg_cells, fd_lsb_cells); a failure goes to 0x142d8 `sb s1, 0xa(s0)` (lsb_missing = 1, :142),
     0x142dc and 0x14298 with the decoder as dn_seg_pre has it;
   - 0x14250-0x14264: value |= (lsb.d2 >> 4) & 7 (`lh`, `slli 57`, `srli 61`, `or`, `sh`; fd_value) (:139);
   - 0x14268-0x14288: the peek cursor's 32 bytes back into d->c (:140); fd_peek_join and fd_dec_unmerge give the
     model's decoder with the same cpad (the copy writes back the 7 padding bytes 0x14200-0x1420c read);
   - 0x14298 `addi s1, zero, 1`, then DN_RET (the continuation dn_seg_cont).
   58 instructions; the paths of this segment reach no other pc of the function: 0x1406c (the note) needs
   status & 0xf0 = 0x90, 0x140ac (the sysex) status = 0xf0, 0x142b8 (jog / V-Pot) d1 >= 0x20, and 0x1428c-0x14294
   only follow the note; the path condition excludes each. The stores write only the event, the decoder and the
   72 bytes at sp (the callee writes its two objects there).
   The one premise besides the cut's: 0 < spf. The call passes the LSB message at spf, and the callee's contract
   needs mp <> 0; dn_seg_pre does not say it, and the composition gives it from diginet_decoder_next_contract's
   0 < lo (stk's lo <= sp - 144 = spf). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_msg_next_c diginet_decoder_next_c diginet_decoder_next_seg.
Import ListNotations.
Open Scope Z_scope.

(* ---- the cursor's last word: c->status and the 7 padding bytes ---- *)

Lemma fd_le8_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs H. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2 ^ 64).
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- H.
  apply OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Spec.StrFun.Z_to_le_bytes_to_Z.
Qed.

(* the decoder with its cursor's status and padding as one word (the loads 0x14200-0x1420c, the stores
   0x14278-0x14284), and back *)
Lemma fd_dec_merge : forall m A (v0 v1 v2 v4 : word) (b : byte) cpad,
  rw_cells rsegs m A [C8 v0; C8 v1; C8 v2; C1 b; CB 7 cpad; C8 v4] ->
  length cpad = 7%nat /\
  rw_cells rsegs m A [C8 v0; C8 v1; C8 v2; C8 (le_bytes_to_word (b :: cpad)); C8 v4].
Proof.
  intros m A v0 v1 v2 v4 b cpad H.
  assert (L : length cpad = 7%nat) by (destruct H as [[Hwf _] _]; cbn in Hwf; tauto).
  split; [exact L|].
  apply (rw_cells_recast _ _ _ _ H); [cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes]. rewrite fd_le8_word by (cbn; lia). reflexivity.
Qed.

Lemma fd_dec_unmerge : forall m A (v0 v1 v2 v4 : word) (b : byte) cpad,
  length cpad = 7%nat ->
  rw_cells rsegs m A [C8 v0; C8 v1; C8 v2; C8 (le_bytes_to_word (b :: cpad)); C8 v4] ->
  rw_cells rsegs m A [C8 v0; C8 v1; C8 v2; C1 b; CB 7 cpad; C8 v4].
Proof.
  intros m A v0 v1 v2 v4 b cpad L H.
  apply (rw_cells_recast _ _ _ _ H); [cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes]. rewrite fd_le8_word by (cbn; lia). reflexivity.
Qed.

(* the 72 scratch bytes after the copy 0x14210-0x1421c: the LSB message's 40 bytes, the peek cursor's 25 bytes
   (cursor_cells) and its 7 padding bytes *)
Lemma fd_peek_split : forall m A j0 (v0 v1 v2 : word) (b : byte) cpad,
  length cpad = 7%nat ->
  rw_cells rsegs m A [CB 40 j0; C8 v0; C8 v1; C8 v2; C8 (le_bytes_to_word (b :: cpad))] ->
  rw_cells rsegs m A [CB 40 j0] /\ rw_cells rsegs m (A + 40) [C8 v0; C8 v1; C8 v2; C1 b] /\
  rw_cells rsegs m (A + 65) [CB 7 cpad].
Proof.
  intros m A j0 v0 v1 v2 b cpad L H.
  assert (L0 : length j0 = 40%nat) by (destruct H as [[Hwf _] _]; cbn in Hwf; tauto).
  assert (H' : rw_cells rsegs m A ([CB 40 j0] ++ [C8 v0; C8 v1; C8 v2; C1 b] ++ [CB 7 cpad])).
  { apply (rw_cells_recast _ _ _ _ H); [cbn; tauto | | reflexivity].
    cbn [cells_bytes cbytes app]. rewrite fd_le8_word by (cbn; lia). reflexivity. }
  apply rw_cells_split in H' as [H1 H2]. apply rw_cells_split in H2 as [H2 H3].
  match type of H2 with rw_cells _ _ ?X _ => replace X with (A + 40) in H2 by (cbn; lia) end.
  match type of H3 with rw_cells _ _ ?X _ => replace X with (A + 65) in H3 by (cbn; lia) end.
  tauto.
Qed.

(* the peek cursor and its padding after the call, as the copy-back 0x14268-0x14274 reads them *)
Lemma fd_peek_join : forall m A B (v0 v1 v2 : word) (b : byte) cpad,
  B = A + 25 ->
  rw_cells rsegs m A [C8 v0; C8 v1; C8 v2; C1 b] -> rw_cells rsegs m B [CB 7 cpad] ->
  rw_cells rsegs m A [C8 v0; C8 v1; C8 v2; C8 (le_bytes_to_word (b :: cpad))].
Proof.
  intros m A B v0 v1 v2 b cpad EB H1 H2.
  assert (L : length cpad = 7%nat) by (destruct H2 as [[Hwf _] _]; cbn in Hwf; tauto).
  subst B.
  pose proof (rw_cells_join m A [C8 v0; C8 v1; C8 v2; C1 b] [CB 7 cpad] H1 H2) as H.
  apply (rw_cells_recast _ _ _ _ H); [cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite fd_le8_word by (cbn; lia). reflexivity.
Qed.

(* ---- the peek step: msg_cells and msg_after of a step that returns 1 ---- *)

Lemma fd_lsb_cells : forall body mj r, mr_code r = 1 ->
  exists tail, msg_cells body mj r =
    C1 (b8 (mr_status r)) :: C1 (b8 (mr_running r)) :: C1 (b8 (mr_d1 r)) :: C1 (b8 (mr_d2 r)) :: tail.
Proof.
  intros body mj r H. unfold msg_cells.
  destruct r as [k a b c e f g h i j l]; destruct k; cbn in H |- *; try discriminate; eexists; reflexivity.
Qed.

Lemma fd_after : forall r m0, mr_code r = 1 ->
  dm_status (msg_after r m0) = mr_status r /\ dm_d1 (msg_after r m0) = mr_d1 r /\
  dm_d2 (msg_after r m0) = mr_d2 r.
Proof.
  intros r m0 H. unfold msg_after.
  destruct r as [k a b c e f g h i j l]; destruct k; cbn in H |- *; try discriminate; repeat split.
Qed.

(* 0x1422c `bne a0, s1`: a result other than 1 is not 1 as a word (the codes are 0, -6, -7, -8) *)
Lemma fd_code_word : forall r, mr_code r <> 1 -> bv_unsigned (Z_to_bv 64 (mr_code r)) <> 1.
Proof.
  intros r H. rewrite unsigned_lit_wrap. unfold mr_code in *.
  destruct (mr_kind r); cbn in H |- *; try congruence; compute; discriminate.
Qed.

(* ---- the model's step under the path condition of this segment ---- *)

(* the event the fader writes before its peek (diginet_decode.c:131-134) *)
Definition fd_e (msg : dgn_msg) : dgn_event :=
  de_set_value (u16 (Z.shiftl (dm_d2 msg) 3))
    (de_set_strip (dm_d1 msg)
       (de_set_kind DIGINET_EV_FADER (de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero)))).

(* DgnLib.v diginet_decoder_next on a fader, with the peek read as msg_step over the cursor c1 *)
Lemma fd_step : forall bb dc msg c1 pos st,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) ->
  Z.land (dm_status msg) 0xf0 = 0xb0 -> dm_d1 msg < 0x20 ->
  c1 = cursor_of bb pos st ->
  dn_step bb dc =
    (let r := msg_step bb pos st in
     if (mr_code r =? 1) && (Z.land (dm_status (msg_after r dgn_msg_zero)) 0xf0 =? 0xb0) &&
        (dm_d1 (msg_after r dgn_msg_zero) =? 0x20 + dm_d1 msg) then
       (1, de_set_value (u16 (Z.lor (de_value (fd_e msg))
                                    (u16 (Z.land (Z.shiftr (dm_d2 (msg_after r dgn_msg_zero)) 4) 7)))) (fd_e msg),
        {| dd_c := cursor_of bb (mr_pos r) (mr_st r); dd_p := dd_p dc |})
     else (1, de_set_lsb_missing 1 (fd_e msg), {| dd_c := c1; dd_p := dd_p dc |})).
Proof.
  intros bb dc msg c1 pos st H P1 P2 EC.
  assert (Pf0 : dm_status msg <> 0xf0) by (intros E; rewrite E in P1; discriminate).
  unfold dn_step, diginet_decoder_next. rewrite H. cbv beta iota zeta.
  rewrite Z.eqb_refl. cbn [negb].
  rewrite P1. cbn [Z.eqb Pos.eqb negb].
  rewrite (proj2 (Z.eqb_neq _ _) Pf0).
  rewrite (proj2 (Z.ltb_lt _ _) P2).
  pose proof (diginet_msg_next_msg_step (map bz bb) bb pos st dgn_msg_zero (holds_body_map bb)) as HN.
  change (map bz bb) with (map bv_unsigned bb) in HN. rewrite <- EC in HN. rewrite HN.
  unfold fd_e. reflexivity.
Qed.

(* the LSB matches (:138-140) *)
Lemma fd_hit : forall bb dc msg c1 pos st,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) ->
  Z.land (dm_status msg) 0xf0 = 0xb0 -> dm_d1 msg < 0x20 ->
  c1 = cursor_of bb pos st ->
  mr_code (msg_step bb pos st) = 1 ->
  Z.land (mr_status (msg_step bb pos st)) 0xf0 = 0xb0 ->
  mr_d1 (msg_step bb pos st) = 0x20 + dm_d1 msg ->
  dn_e bb dc = de_set_value (u16 (Z.lor (u16 (Z.shiftl (dm_d2 msg) 3))
                                        (u16 (Z.land (Z.shiftr (mr_d2 (msg_step bb pos st)) 4) 7)))) (fd_e msg) /\
  dn_d bb dc = {| dd_c := cursor_of bb (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st));
                  dd_p := dd_p dc |}.
Proof.
  intros bb dc msg c1 pos st H P1 P2 EC C1 C2 C3.
  destruct (fd_after (msg_step bb pos st) dgn_msg_zero C1) as (A1 & A2 & A3).
  unfold dn_e, dn_d. rewrite (fd_step bb dc msg c1 pos st H P1 P2 EC). cbv zeta.
  rewrite A1, A2, A3, C1, C2, C3, !Z.eqb_refl. cbn [andb fst snd].
  split; reflexivity.
Qed.

(* no LSB, or not the matching one (:141-142) *)
Lemma fd_miss : forall bb dc msg c1 pos st,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) ->
  Z.land (dm_status msg) 0xf0 = 0xb0 -> dm_d1 msg < 0x20 ->
  c1 = cursor_of bb pos st ->
  mr_code (msg_step bb pos st) <> 1 \/
  (mr_code (msg_step bb pos st) = 1 /\
   (Z.land (mr_status (msg_step bb pos st)) 0xf0 <> 0xb0 \/ mr_d1 (msg_step bb pos st) <> 0x20 + dm_d1 msg)) ->
  dn_e bb dc = de_set_lsb_missing 1 (fd_e msg) /\ dn_d bb dc = {| dd_c := c1; dd_p := dd_p dc |}.
Proof.
  intros bb dc msg c1 pos st H P1 P2 EC M.
  unfold dn_e, dn_d. rewrite (fd_step bb dc msg c1 pos st H P1 P2 EC). cbv zeta.
  destruct M as [M | (C1 & M)].
  - rewrite (proj2 (Z.eqb_neq _ _) M). cbn [andb fst snd]. split; reflexivity.
  - destruct (fd_after (msg_step bb pos st) dgn_msg_zero C1) as (A1 & A2 & _).
    rewrite A1, A2, C1, Z.eqb_refl. cbn [andb].
    destruct M as [M | M].
    + rewrite (proj2 (Z.eqb_neq _ _) M). cbn [andb fst snd]. split; reflexivity.
    + rewrite (proj2 (Z.eqb_neq _ _) M), andb_false_r. cbn [fst snd]. split; reflexivity.
Qed.

(* ---- word and byte facts of the walk ---- *)

(* lbu of a byte cell *)
Lemma fd_zxb_b8 : forall x, 0 <= x < 256 -> zxb (b8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. change (bv_unsigned (b8 x)) with (bz (b8 x)). rewrite bz_b8 by lia. reflexivity. Qed.

(* sb of a register: its low byte *)
Lemma fd_le1_lit : forall e, le1 (Z_to_bv 64 e) = [Z_to_bv 8 e].
Proof.
  intros e. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 8 * 2 ^ 56). change (2 ^ Z.of_N 8) with (2 ^ 8).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

(* :134, (uint16_t)(d2 << 3) of a byte d2 *)
Lemma fd_u16_sl3 : forall x, 0 <= x < 256 -> u16 (Z.shiftl x 3) = Z.shiftl x 3.
Proof.
  intros x Hx. unfold u16. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  apply Z.mod_small. lia.
Qed.

(* a boolean property of every byte value, checked on the 256 values *)
Lemma fd_byte_cases : forall P : Z -> bool, forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x).
  split; [lia|]. apply in_seq. lia.
Qed.

(* 0x14234 `andi a0, a0, 0xf0` of a byte *)
Lemma fd_land_range : forall x, 0 <= x < 256 -> 0 <= Z.land x 240 < 256.
Proof.
  intros x Hx.
  assert (B : (0 <=? Z.land x 240) && (Z.land x 240 <? 256) = true).
  { revert x Hx. apply (fd_byte_cases (fun x => (0 <=? Z.land x 240) && (Z.land x 240 <? 256))).
    vm_compute. reflexivity. }
  apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia.
Qed.

(* 0x14254 `lh a1, 0xc(s0)` of the stored d2 << 3 *)
Lemma fd_sx16 : forall x, 0 <= x < 256 -> bv_unsigned (sx16 (Z_to_bv 64 (Z.shiftl x 3))) = Z.shiftl x 3.
Proof.
  intros x Hx. apply Z.eqb_eq. revert x Hx.
  apply (fd_byte_cases (fun x => bv_unsigned (sx16 (Z_to_bv 64 (Z.shiftl x 3))) =? Z.shiftl x 3)).
  vm_compute. reflexivity.
Qed.

(* 0x14258 `slli a0, a0, 0x39` / 0x1425c `srli a0, a0, 0x3d`: (lsb.d2 >> 4) & 7 *)
Lemma fd_lsb_bits : forall y, 0 <= y < 256 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl y 57))) 61)) = Z.land (Z.shiftr y 4) 7.
Proof.
  intros y Hy. apply Z.eqb_eq. revert y Hy.
  apply (fd_byte_cases (fun y => bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl y 57))) 61))
                                 =? Z.land (Z.shiftr y 4) 7)).
  vm_compute. reflexivity.
Qed.

Lemma fd_land7 : forall y, 0 <= Z.land (Z.shiftr y 4) 7 < 8.
Proof.
  intros y. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change 8 with (2 ^ 3).
  apply Z.mod_pos_bound. lia.
Qed.

Lemma fd_lor_u16 : forall x z, 0 <= x < 256 -> 0 <= z < 8 ->
  Z.lor (Z.shiftl x 3) z = u16 (Z.lor (u16 (Z.shiftl x 3)) (u16 z)).
Proof.
  intros x z Hx Hz.
  assert (H : forallb (fun z => Z.lor (Z.shiftl x 3) z =? u16 (Z.lor (u16 (Z.shiftl x 3)) (u16 z)))
                (map Z.of_nat (seq 0 8)) = true).
  { revert x Hx.
    apply (fd_byte_cases (fun x => forallb (fun z => Z.lor (Z.shiftl x 3) z =? u16 (Z.lor (u16 (Z.shiftl x 3)) (u16 z)))
                                     (map Z.of_nat (seq 0 8)))).
    vm_compute. reflexivity. }
  rewrite forallb_forall in H. apply Z.eqb_eq, H, in_map_iff. exists (Z.to_nat z). split; [lia | apply in_seq; lia].
Qed.

(* 0x14260 `or a0, a1, a0`: the model's value of diginet_decode.c:139 *)
Lemma fd_value : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  Z.lor (bv_unsigned (sx16 (Z_to_bv 64 (Z.shiftl x 3))))
        (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl y 57))) 61)))
  = u16 (Z.lor (u16 (Z.shiftl x 3)) (u16 (Z.land (Z.shiftr y 4) 7))).
Proof. intros x y Hx Hy. rewrite fd_sx16, fd_lsb_bits by lia. apply fd_lor_u16; [lia | apply fd_land7]. Qed.

(* the registers after a load: a model byte, and bv_unsigned of an in-range value *)
Ltac fd_regs :=
  repeat match goal with
  | |- context [zxb (b8 ?x)] => rewrite (fd_zxb_b8 x) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
  end.

(* ---- the walk ---- *)

Lemma diginet_decoder_next_fader_seg : forall (ra s3 s4 s5 s6 s7 s8 s9 s10 s11 gp tp : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
    (spf d ev body : Z) (bb cpad mpad junk : list byte) (dc : dgn_decoder) (msg : dgn_msg) (c1 : dgn_cursor)
    (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word),
  diginet_msg_next_contract ->
  dn_seg_pre m spf d ev body bb cpad mpad junk dc msg c1 ->
  0 < spf ->
  Z.land (dm_status msg) 0xf0 = 0xb0 /\ dm_d1 msg < 0x20 ->
  dn_seg_cont Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body bb cpad mpad dc ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 d) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 DN_DECODE) fc None m (seg_rom rsegs)).
Proof.
  intros ra s3 s4 s5 s6 s7 s8 s9 s10 s11 gp tp F fc m Q spf d ev body bb cpad mpad junk dc msg c1
    a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 HMN PRE Hsp (P1 & P2) K.
  destruct PRE as (MN & Hd0 & He0 & Hd8 & He8 & Hs16 & Hb0 & HLEN & HPOS & HST & HB & HD & HE & HM & HJ &
                   Dde & Ddb & Deb & Dds & Des & Dbs & MI).
  destruct (msg_next_one bb (dd_c dc) dgn_msg_zero msg c1 HLEN ltac:(lia) HST MN)
    as (Rst & Rd1 & Rd2 & _ & _ & L1 & Q1 & S1).
  (* the cursor c1 of the first call, as the peek call's cursor *)
  assert (EC1 : c1 = cursor_of bb (Z.to_nat (dc_pos c1)) (dc_status c1)).
  { destruct c1 as [l p s]. unfold cursor_of. cbn [dc_len dc_pos dc_status] in *. f_equal; lia. }
  assert (Ppos : (Z.to_nat (dc_pos c1) <= length bb)%nat) by lia.
  assert (Lc1 : dc_len c1 = Z.of_nat (length bb)) by lia.
  clear L1 Q1.
  pose proof (rw_cells_bound _ _ _ _ HE) as BE. rewrite event_cells_size in BE.
  pose proof (rw_cells_bound _ _ _ _ HD) as BD. rewrite decoder_cells_size in BD.
  pose proof (rw_cells_bound _ _ _ _ HM) as BM. rewrite dmsg_cells_size in BM.
  pose proof (rw_cells_bound _ _ _ _ HJ) as BJ. cbn [cells_size csize Nat.add] in BJ.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  pose proof (munch_refl [(d, d + 40); (ev, ev + 80); (spf, spf + 72)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold dn_seg_cont, DN_RET in K.
  (* the cells as the kit's loads and stores read them *)
  destruct msg as [mst mrun md1 md2 msx msxl moff mlen]. cbn [dm_status dm_d1 dm_d2] in *.
  unfold dmsg_cells in HM. cbn [dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len dm_offset dm_len] in HM.
  unfold event_cells, dmsg_cells, arr_cells, de_set_msg, dgn_event_zero in HE.
  cbn [map seq app nth repeat de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value
       de_delta de_mask de_segments de_len de_text de_seg de_dots de_device de_msg dm_status dm_running dm_d1
       dm_d2 dm_sysex dm_sysex_len dm_offset dm_len] in HE.
  unfold decoder_cells, cursor_cells in HD. cbn [dd_c dd_p app] in HD. rewrite Lc1 in HD.
  set (pos := Z.to_nat (dc_pos c1)) in *. set (st := dc_status c1) in *. clearbody pos st.
  destruct (fd_dec_merge _ _ _ _ _ _ _ _ HD) as [Lcp HD']. clear HD. rename HD' into HD.
  assert (Pf0 : mst <> 240) by (intros E; rewrite E in P1; discriminate).
  unfold DN_DECODE.
  (* 0x14054-0x14068: status, kind = OTHER, not a note *)
  step. fd_regs.
  step. step. step. step. fd_regs.
  step. rewrite P1. if_true.
  (* 0x140a4-0x140a8: not a sysex *)
  step. step. unfold bv_eqb. fd_regs. if_true.
  (* 0x141d0-0x141d8: a control change *)
  step. step. step. if_false.
  (* 0x141dc-0x141e4: d1 < 0x20, the fader *)
  step. fd_regs. step. step. unfold bv_ltu. fd_regs. if_false.
  (* 0x141e8-0x141fc: kind = FADER, strip = d1, value = d2 << 3 *)
  step. fd_regs. step. step. fd_regs.
  step. step. rewrite fd_le1_lit. mem_after_store.
  step.
  (* 0x14200-0x1421c: d->c to the peek cursor *)
  step. step. step. step. step. step. step. step.
  (* 0x14220-0x14228: diginet_msg_next (peek cursor, LSB message) *)
  step. step. step.
  destruct (fd_peek_split _ _ _ _ _ _ _ _ Lcp HJ) as (HLS & HPC & HP7). clear HJ.
  call (HMN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (spf + 40) spf body bb (firstn 40 junk) pos st).
  all: try solve [ lia | Z.div_mod_to_equations; lia | eassumption ].
  set (r := msg_step bb pos st) in *. unfold cursor_cells in PC.
  assert (Pc1 : 0 <= dc_pos c1) by (rewrite EC1; unfold cursor_of; cbn [dc_pos]; lia).
  assert (Sc1 : st_ok (dc_status c1)) by (rewrite EC1; exact S1).
  assert (EV1 : u16 (Z.shiftl md2 3) = Z.shiftl md2 3) by (apply fd_u16_sl3; lia).
  (* the three misses: 0x142d8 (lsb_missing = 1), 0x142dc, 0x14298, DN_RET *)
  lazymatch type of HE with rw_cells _ _ _ ?cs => set (CSE := cs) in HE end.
  lazymatch type of HD with rw_cells _ _ _ ?cs => set (CSD := cs) in HD end.
  assert (MISS : mr_code r <> 1 \/ (mr_code r = 1 /\ (Z.land (mr_status r) 0xf0 <> 0xb0 \/
                                                       mr_d1 r <> 0x20 + md1)) ->
                 forall (ra' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word) m',
                 munch [(d, d + 40); (ev, ev + 80); (spf, spf + 72)] m m' -> wmono rsegs m m' ->
                 mem_inv rsegs m' -> rw_cells rsegs m' ev CSE -> rw_cells rsegs m' d CSD ->
                 evt rsegs Q (MS (mkR ra' (Z_to_bv 64 spf) gp tp t0' t1' t2' (Z_to_bv 64 ev) (Z_to_bv 64 1)
                                      a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                                 F (Z_to_bv 64 0x142d8) fc None m' (seg_rom rsegs))).
  { intros MC ra' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' m' MU' WM' MI' HE' HD'.
    unfold CSE in HE'. unfold CSD in HD'.
    clear - MC MU' WM' MI' HE' HD' K MN P1 P2 EC1 Lcp EV1 Dde Des Dds BE BD BJ.
    step. rewrite fd_le1_lit. mem_after_store. step. step.
    destruct (fd_miss bb dc (DgnMsg mst mrun md1 md2 msx msxl moff mlen) c1 pos st MN P1 P2 EC1 MC) as [EE ED].
    eapply K; [exact MU' | exact WM' | exact MI' | | ].
    - rewrite EE. unfold fd_e. cbn [dm_d1 dm_d2]. rewrite EV1. exact HE'.
    - rewrite ED, EC1. unfold decoder_cells, cursor_cells, cursor_of. cbn [dd_c dd_p dc_len dc_pos dc_status app].
      rewrite Nat2Z.id. apply fd_dec_unmerge; [exact Lcp | exact HD']. }
  destruct (Z.eqb_spec (mr_code r) 1) as [C1|C1].
  2:{ (* 0x1422c: the peek found no message *)
      pose proof (fd_code_word r C1) as CW.
      step. if_true.
      eapply MISS; [left; exact C1 | exact MU | exact WM | exact MI0 | exact HE | exact HD]. }
  rewrite C1. step. if_false.
  (* the LSB message's fields and their byte ranges *)
  pose proof (diginet_msg_next_msg_step (map bz bb) bb pos st dgn_msg_zero (holds_body_map bb)) as HN2.
  change (map bz bb) with (map bv_unsigned bb) in HN2. rewrite <- EC1 in HN2.
  change (msg_step bb pos st) with r in HN2. rewrite C1 in HN2.
  destruct (msg_next_one bb c1 dgn_msg_zero _ _ Lc1 Pc1 Sc1 HN2) as (Ls & Ld1 & Ld2 & _).
  destruct (fd_after r dgn_msg_zero C1) as (A1 & A2 & A3). rewrite A1 in Ls. rewrite A2 in Ld1. rewrite A3 in Ld2.
  destruct (fd_lsb_cells body (firstn 40 junk) r C1) as [tail Etl]. rewrite Etl in POST.
  (* 0x14230-0x1423c: lsb.status & 0xf0 == 0xb0 *)
  pose proof (fd_land_range (mr_status r) Ls) as Ls'.
  step. fd_regs. step. fd_regs. step. step.
  destruct (Z.eqb_spec (Z.land (mr_status r) 240) 176) as [S2|S2].
  2:{ unfold bv_eqb. fd_regs. if_true.
      eapply MISS; [right; split; [exact C1 | left; exact S2] | exact MU | exact WM | exact MI0 | exact HE | exact HD]. }
  rewrite S2. if_false.
  (* 0x14240-0x1424c: lsb.d1 == 0x20 + m.d1 *)
  step. fd_regs. step. fd_regs. step. step.
  unfold bv_eqb. fd_regs.
  destruct (Z.eqb_spec (md1 + 32) (mr_d1 r)) as [D3|D3].
  2:{ if_true.
      eapply MISS; [right; split; [exact C1 | right; lia] | exact MU | exact WM | exact MI0 | exact HE | exact HD]. }
  if_false.
  unfold CSE in HE. unfold CSD in HD.
  (* 0x14250-0x14264: value |= (lsb.d2 >> 4) & 7 *)
  step. fd_regs. step. step. fd_regs. step. step.
  rewrite (fd_value md2 (mr_d2 r)) by lia.
  step.
  (* 0x14268-0x14288: the peek cursor back into d->c *)
  pose proof (fd_peek_join _ (spf + 40) (spf + 65) _ _ _ _ _ ltac:(lia) PC HP7) as HPK. clear PC HP7.
  step. step. step. step. step. step. step. step. step.
  (* 0x14298, DN_RET *)
  step.
  destruct (fd_hit bb dc (DgnMsg mst mrun md1 md2 msx msxl moff mlen) c1 pos st MN P1 P2 EC1 C1 S2
              (eq_trans (eq_sym D3) (Z.add_comm md1 32))) as [EE ED].
  eapply K; [exact MU | exact WM | exact MI0 | | ].
  - rewrite EE. exact HE.
  - rewrite ED. unfold decoder_cells, cursor_cells, cursor_of. cbn [dd_c dd_p dc_len dc_pos dc_status app].
    rewrite Nat2Z.id. apply fd_dec_unmerge; [exact Lcp | exact HD].
Qed.
