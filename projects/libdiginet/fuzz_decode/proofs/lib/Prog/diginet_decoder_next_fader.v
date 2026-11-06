(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* diginet_decoder_next in fuzz_decode.plain, the fader path (from 0x14044, controller number d1 < 0x20 of a
   control change): kind, strip, the MSB value, the peek copy of d->c at sp' + 0x30, the second
   diginet_msg_next call on it (0x14084) with the message lsb at sp' + 8, the LSB test and either the value's
   low bits and the copy of the peek cursor back to d->c (0x140c4 .. 0x140e0) or lsb_missing (0x14138)
   (diginet_decode.c:130-145).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_msg_next_c diginet_decoder_next_c diginet_decoder_next_bridge diginet_decoder_next_lib.
Import ListNotations.
Open Scope Z_scope.

(* ---- the cursor's last word: the status byte and the 7 padding bytes after the cursor, which the code
   copies as one 8-byte word (ld / sd at offset 24) ---- *)

Lemma fd_le8_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs H. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2 ^ 64).
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- H. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma fd_word : forall (b : byte) cpad, length cpad = 7%nat -> exists w, le8 w = b :: cpad.
Proof. intros b cpad L. exists (le_bytes_to_word (b :: cpad)). apply fd_le8_word. cbn [length]. lia. Qed.

Lemma fd_join : forall segs m A B (v0 v1 v2 w : word) (b : byte) cpad,
  B = A + 25 -> le8 w = b :: cpad ->
  rw_cells segs m A [C8 v0; C8 v1; C8 v2; C1 b] -> rw_cells segs m B [CB 7 cpad] ->
  rw_cells segs m A [C8 v0; C8 v1; C8 v2; C8 w].
Proof.
  intros segs m A B v0 v1 v2 w b cpad -> Lw H1 H2.
  assert (H : rw_cells segs m A ([C8 v0; C8 v1; C8 v2; C1 b] ++ [CB 7 cpad])).
  { apply rw_cells_app_merge; [exact H1|]. cbn [cells_size csize Nat.add].
    replace (A + Z.of_nat 25) with (A + 25) by lia. exact H2. }
  eapply rw_cells_bytes; [exact H | cbn; tauto |].
  cbn [cells_bytes cbytes app]. rewrite Lw. cbn [app]. reflexivity.
Qed.

Lemma fd_split : forall segs m A (v0 v1 v2 w : word) (b : byte) cpad,
  le8 w = b :: cpad -> rw_cells segs m A [C8 v0; C8 v1; C8 v2; C8 w] ->
  rw_cells segs m A [C8 v0; C8 v1; C8 v2; C1 b] /\ rw_cells segs m (A + 25) [CB 7 cpad].
Proof.
  intros segs m A v0 v1 v2 w b cpad Lw H.
  assert (L : length cpad = 7%nat).
  { pose proof (length_le8 w) as E. rewrite Lw in E. cbn [length] in E. lia. }
  assert (H' : rw_cells segs m A ([C8 v0; C8 v1; C8 v2; C1 b] ++ [CB 7 cpad])).
  { eapply rw_cells_bytes; [exact H | cbn; tauto |].
    cbn [cells_bytes cbytes app]. rewrite Lw. cbn [app]. reflexivity. }
  apply rw_cells_app in H' as [H1 H2]. cbn [cells_size csize Nat.add] in H2.
  replace (A + Z.of_nat 25) with (A + 25) in H2 by lia. split; assumption.
Qed.

(* two adjacent pieces as one *)
Lemma fd_app2 : forall segs m A B cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m B cs2 -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells segs m A (cs1 ++ cs2).
Proof. intros segs m A B cs1 cs2 H1 H2 ->. apply rw_cells_app_merge; assumption. Qed.

(* ---- values ---- *)

Lemma fd_sl3 : forall x, 0 <= x < 128 -> u16 (Z.shiftl x 3) = Z.shiftl x 3.
Proof.
  intros x Hx. apply u16_small. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.

(* 0x140b0 lh of the stored d2 << 3 *)
Lemma fd_sx16 : forall x, 0 <= x < 256 -> bv_unsigned (sx16 (Z_to_bv 64 (Z.shiftl x 3))) = Z.shiftl x 3.
Proof.
  intros x Hx. apply Z.eqb_eq. revert x Hx.
  apply (byte_forall (fun x => bv_unsigned (sx16 (Z_to_bv 64 (Z.shiftl x 3))) =? Z.shiftl x 3)).
  vm_compute. reflexivity.
Qed.

(* 0x140b4 slli 57 / 0x140b8 srli 61 of a byte: its bits 4..6 *)
Lemma fd_lsb_bits : forall y, 0 <= y < 256 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 y)) 57))) 61))
  = Z.land (Z.shiftr y 4) 7.
Proof.
  intros y Hy. apply Z.eqb_eq. revert y Hy.
  apply (byte_forall (fun y =>
    bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 y)) 57))) 61))
    =? Z.land (Z.shiftr y 4) 7)).
  vm_compute. reflexivity.
Qed.

Lemma fd_land7 : forall y, 0 <= Z.land (Z.shiftr y 4) 7 < 8.
Proof.
  intros y. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change 8 with (2 ^ 3).
  apply Z.mod_pos_bound. lia.
Qed.

Lemma fd_lor : forall x z, 0 <= x < 256 -> 0 <= z < 8 ->
  Z.lor (Z.shiftl x 3) z = u16 (Z.lor (u16 (Z.shiftl x 3)) (u16 z)).
Proof.
  intros x z Hx Hz.
  assert (H : forallb (fun n => Z.lor (Z.shiftl x 3) (Z.of_nat n) =?
                                u16 (Z.lor (u16 (Z.shiftl x 3)) (u16 (Z.of_nat n)))) (seq 0 8) = true).
  { revert x Hx.
    apply (byte_forall (fun x => forallb (fun n => Z.lor (Z.shiftl x 3) (Z.of_nat n) =?
                                                   u16 (Z.lor (u16 (Z.shiftl x 3)) (u16 (Z.of_nat n))))
                                         (seq 0 8))).
    vm_compute. reflexivity. }
  rewrite forallb_forall in H. specialize (H (Z.to_nat z) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.

(* 0x140bc or: the value of diginet_decode.c:139 *)
Lemma fd_value : forall x y, 0 <= x < 128 -> 0 <= y < 128 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (sx16 (Z_to_bv 64 (Z.shiftl x 3))))
    (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 y)) 57))) 61))))
  = Z_to_bv 64 (u16 (Z.lor (u16 (Z.shiftl x 3)) (u16 (Z.land (Z.shiftr y 4) 7)))).
Proof.
  intros x y Hx Hy. rewrite fd_sx16, fd_lsb_bits by lia. f_equal. apply fd_lor; [lia | apply fd_land7].
Qed.

(* ---- the model ---- *)

(* the event the fader writes before the peek (diginet_decode.c:131-134) *)
Definition fd_e (msg : dgn_msg) : dgn_event :=
  de_set_value (u16 (Z.shiftl (dm_d2 msg) 3))
    (de_set_strip (dm_d1 msg) (de_set_kind DIGINET_EV_FADER (dn_e0 msg))).

(* dn_tail for a fader: the second step r over the cursor after the first, its LSB test, and either the
   value's low bits with the cursor after r, or lsb_missing with the cursor before r *)
Lemma fd_model : forall bb msg pos1 st1 p,
  Z.land (dm_status msg) 240 = 176 -> dm_d1 msg < 32 ->
  dn_tail (map bz bb) msg (cursor_of bb pos1 st1) p =
  if (mr_code (msg_step bb pos1 st1) =? 1) && (Z.land (mr_status (msg_step bb pos1 st1)) 240 =? 176) &&
     (mr_d1 (msg_step bb pos1 st1) =? 32 + dm_d1 msg)
  then (1, de_set_value (u16 (Z.lor (u16 (Z.shiftl (dm_d2 msg) 3))
                                    (u16 (Z.land (Z.shiftr (mr_d2 (msg_step bb pos1 st1)) 4) 7)))) (fd_e msg),
        {| dd_c := cursor_of bb (mr_pos (msg_step bb pos1 st1)) (mr_st (msg_step bb pos1 st1)); dd_p := p |})
  else (1, de_set_lsb_missing 1 (fd_e msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |}).
Proof.
  intros bb msg pos1 st1 p H1 H2.
  assert (N90 : (Z.land (dm_status msg) 240 =? 144) = false) by (rewrite H1; reflexivity).
  assert (NF0 : (dm_status msg =? 240) = false).
  { apply Z.eqb_neq. intros E. rewrite E in H1. discriminate. }
  unfold dn_tail. rewrite N90, NF0, H1, (proj2 (Z.ltb_lt _ _) H2). cbn [Z.eqb Pos.eqb negb].
  destruct (dn_msg_next bb pos1 st1 dgn_msg_zero) as (E1 & E2 & E3).
  destruct (diginet_msg_next (map bz bb) (cursor_of bb pos1 st1) dgn_msg_zero) as [[rl lsb] peek] eqn:EE.
  cbn [fst snd] in E1, E2, E3. subst rl peek.
  destruct (Z.eqb_spec (mr_code (msg_step bb pos1 st1)) 1) as [C|C].
  - rewrite (E3 C). reflexivity.
  - cbn [andb]. reflexivity.
Qed.

(* the lsb_missing exit at 0x14138 (sb s1, 0xa(s0); j 0x140f4; s1 = 1) and the epilogue, with the peek
   cursor and its padding as one 32-byte piece and d->c as dn_fin takes it; HR is the model's result *)
Ltac fd_miss HR HPc HP7 HDw HDp Lw HE HEM :=
  step; step; step;
  let HPk := fresh "HPk" in let HDc := fresh "HDc" in let HD7 := fresh "HD7" in let HD2 := fresh "HD2" in
  pose proof (fd_app2 _ _ _ _ _ _ HPc HP7 ltac:(cbn [cells_size csize Nat.add]; lia)) as HPk;
  cbn [app] in HPk; clear HPc HP7;
  destruct (fd_split _ _ _ _ _ _ _ _ _ Lw HDw) as [HDc HD7]; clear HDw;
  pose proof (fd_app2 _ _ _ _ _ _ HD7 HDp ltac:(cbn [cells_size csize Nat.add]; lia)) as HD2;
  cbn [app] in HD2; clear HD7 HDp;
  dn_fin HR HDc HD2 HE HEM; unfold fd_e;
  [ dmsg_eq | ev_head_lit; unfold DIGINET_EV_FADER; rewrite fd_sl3 by lia; reflexivity ].

Section Fader.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte).

Lemma dn_fader : diginet_msg_next_contract ->
  forall (ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 : word) (m1 : word -> option byte),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad ->
  dn_at sp m0 m1 d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra (dn_e0 msg) ->
  Z.land (dm_status msg) 240 = 176 -> 0 <= dm_d1 msg < 32 -> 0 <= dm_d2 msg < 128 ->
  (pos1 <= length bb)%nat -> st_ok st1 ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1)
             (Z_to_bv 64 (dm_d1 msg)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 d) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14044) fc None m1 (seg_rom rsegs)).
Proof.
  intros MN ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 m1 HCTX HAT HB0 RD1 RD2 HPOS1 HST1.
  dn_ctx_open HCTX. dn_open HAT.
  rewrite (fd_model bb msg pos1 st1 p HB0 ltac:(lia)) in HRES.
  (* the decoder's last word: st1 and the 7 padding bytes as one 8-byte cell *)
  apply rw_cells_cons in HD2 as [HD7 HDp]. cbn [csize] in HDp.
  replace (d + 25 + Z.of_nat 7) with (d + 32) in HDp by lia.
  pose proof (rw_cells_wf _ _ _ _ HD7) as [L7 _]. cbn [cell_wf] in L7.
  destruct (fd_word (b8 st1) cpad L7) as [w Lw].
  pose proof (fd_join _ _ d (d + 25) _ _ _ w _ cpad ltac:(lia) Lw HDc HD7) as HDw. clear HDc HD7.
  (* lbu d2; s1 = 1; slli 3; kind, strip and value stored *)
  step.
  rewrite (dn_zxb_b8 (dm_d2 msg)) by lia.
  step. step.
  rewrite (unsigned_lit (dm_d2 msg)) by lia.
  step. step. step.
  (* the four words of d->c to the peek cursor at sp' + 0x30 *)
  do 8 step.
  (* the peek as the callee's cursor and the 7 padding bytes after it *)
  destruct (fd_split _ _ _ _ _ _ _ _ _ Lw HP) as [HPc HP7]. clear HP.
  replace (bv_unsigned sp + -112 + 25) with (bv_unsigned sp + -87) in HP7 by lia.
  (* a0 = sp' + 0x30, a1 = sp' + 8; jal diginet_msg_next *)
  step. step. step.
  assert (U112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112)
    by (apply unsigned_lit; lia).
  assert (U152 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -152)) = bv_unsigned sp + -152)
    by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MN; [lia | lia | exact HPOS1 | exact HST1 | exact HPc | exact HBB | exact HL | lia | lia | lia | exact MI]
    | post_call rsegs mm ]
  end.
  rename POST into HLm, PC into HPc, MI0 into MI.
  unfold cursor_cells in HPc.
  pose proof (mr_code_range (msg_step bb pos1 st1)) as RC.
  (* bne a0, s1: the peek gave no message *)
  step.
  rewrite (dn_eqb_int64 (mr_code (msg_step bb pos1 st1)) 1) by lia.
  destruct (Z.eq_dec (mr_code (msg_step bb pos1 st1)) 1) as [C1|C1].
  2: {
    if_true.
    destruct (rw_cells_forget _ _ _ _ HLm) as [jl' HLf]. clear HLm. rewrite msg_cells_size in HLf.
    assert (HR : res = (1, de_set_lsb_missing 1 (fd_e msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |}))
      by (rewrite HRES, (proj2 (Z.eqb_neq _ 1) C1); reflexivity).
    fd_miss HR HPc HP7 HDw HDp Lw HE HEM. }
  if_false.
  pose proof (dn_msg_facts bb pos1 st1 HST1 C1) as (LD1 & LD2 & LST).
  rewrite (msg_cells_dmsg body jl bb pos1 st1 C1) in HLm.
  unfold dmsg_cells in HLm.
  cbn [dn_msg dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len dm_offset dm_len] in LD1, LD2, LST, HLm.
  set (r := msg_step bb pos1 st1) in *. clearbody r.
  assert (RS : 0 <= mr_status r < 256) by lia.
  (* lbu lsb.status; andi 0xf0; bne 0xb0 *)
  step.
  rewrite (dn_zxb_b8 (mr_status r)) by lia.
  step.
  rewrite (unsigned_lit (mr_status r)) by lia.
  step. step.
  pose proof (byte_land_le (mr_status r) 240 RS ltac:(lia)) as RL.
  rewrite (dn_eqb_u64 (Z.land (mr_status r) 240) 176) by lia.
  destruct (Z.eq_dec (Z.land (mr_status r) 240) 176) as [S2|S2].
  2: {
    if_true.
    assert (HR : res = (1, de_set_lsb_missing 1 (fd_e msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |}))
      by (rewrite HRES, C1, (proj2 (Z.eqb_neq _ _) S2); reflexivity).
    fd_miss HR HPc HP7 HDw HDp Lw HE HEM. }
  if_false.
  (* lbu m.d1; lbu lsb.d1; addi 0x20; bne *)
  step.
  rewrite (dn_zxb_b8 (dm_d1 msg)) by lia.
  step.
  rewrite (dn_zxb_b8 (mr_d1 r)) by lia.
  step. step.
  rewrite (dn_eqb_u64 (dm_d1 msg + 32) (mr_d1 r)) by lia.
  destruct (Z.eq_dec (dm_d1 msg + 32) (mr_d1 r)) as [D3|D3].
  2: {
    if_true.
    assert (HR : res = (1, de_set_lsb_missing 1 (fd_e msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |}))
      by (rewrite HRES, C1, S2, (proj2 (Z.eqb_neq (mr_d1 r) (32 + dm_d1 msg))) by lia; reflexivity).
    fd_miss HR HPc HP7 HDw HDp Lw HE HEM. }
  if_false.
  (* the value's low bits: lbu lsb.d2; lh value; slli 57; srli 61; or; sh *)
  step.
  rewrite (dn_zxb_b8 (mr_d2 r)) by lia.
  step. step. step. step.
  rewrite (fd_value (dm_d2 msg) (mr_d2 r)) by lia.
  step.
  (* the peek cursor back to d->c (0x140c4 .. 0x140e0) *)
  destruct (fd_word (b8 (mr_st r)) cpad L7) as [w2 Lw2].
  pose proof (fd_join _ _ (bv_unsigned sp + -112) (bv_unsigned sp + -87) _ _ _ w2 _ cpad ltac:(lia) Lw2 HPc HP7)
    as HPw.
  clear HPc HP7.
  do 8 step.
  (* j 0x140f4; s1 = 1 *)
  step. step.
  destruct (fd_split _ _ _ _ _ _ _ _ _ Lw2 HDw) as [HDc HD7]. clear HDw.
  pose proof (fd_app2 _ _ _ _ _ _ HD7 HDp ltac:(cbn [cells_size csize Nat.add]; lia)) as HD2.
  cbn [app] in HD2. clear HD7 HDp.
  assert (HR : res = (1, de_set_value (u16 (Z.lor (u16 (Z.shiftl (dm_d2 msg) 3))
                                                  (u16 (Z.land (Z.shiftr (mr_d2 r) 4) 7)))) (fd_e msg),
                      {| dd_c := cursor_of bb (mr_pos r) (mr_st r); dd_p := p |})).
  { rewrite HRES, C1, S2, (proj2 (Z.eqb_eq (mr_d1 r) (32 + dm_d1 msg))) by lia. reflexivity. }
  dn_fin HR HDc HD2 HE HEM; unfold fd_e.
  - dmsg_eq.
  - ev_head_lit. unfold DIGINET_EV_FADER. reflexivity.
Qed.

End Fader.
