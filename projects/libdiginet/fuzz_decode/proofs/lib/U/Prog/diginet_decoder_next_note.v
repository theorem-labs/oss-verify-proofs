(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the note segment of the UBSan walk of diginet_decoder_next
   (lib/U/Prog/diginet_decoder_next_c.v), from DN_DECODE (0x14054) to DN_RET (0x1429c) when the model's message is
   a note, Z.land (dm_status msg) 0xf0 = 0x90: diginet_decode.c:115-122 with decode_note (:20-35) inlined, against
   the cut lib/U/Prog/diginet_decoder_next_seg.v. No call, no UBSan check site, no abort site on these paths; the
   28 instructions 0x14054-0x14068, 0x1406c-0x140a0, 0x141c0-0x141cc and 0x1428c-0x14298 are all walked.
   - 0x14054 `lbu a1, 0x48(sp)` reads m.status (dmsg_cells at sp + 72); 0x1405c `andi 0xf0`; 0x14064 `sw a2, 0(s0)`
     is ev->kind = DIGINET_EV_OTHER (13); 0x14068 `bne a0, a3(0x90)` is not taken by the path condition.
   - 0x1406c / 0x14070 read d2 and d1; 0x14078 `andi a0, a2, 0x3f` is id; 0x1407c `slli 57` / 0x14080 `srli 63` is
     bit 6 of d2, the model's u8 (d2 & 0x40 != 0) (note_on_bit); 0x14088 `sb a1, 5(s0)` is ev->button = d1,
     0x1408c `sb a2, 7(s0)` is ev->on.
   - 0x14084 `addi a4, a0, -0x18` / 0x14090 `bltu a3(5), a4`: unsigned id - 24 > 5 exactly when id is not in
     0x18..0x1d (note_zone_test). In the zone, 0x14094-0x1409c write kind = DIGINET_EV_SECTION_BUTTON (4) and
     zone = id, and 0x140a0 jumps to 0x14298.
   - Else 0x141c0 / 0x141c4 `bne a1, a2(9)`: for d1 = DIGINET_BTN_TOUCH 0x141c8 sets a1 = DIGINET_EV_TOUCH (2) and
     jumps to 0x14290; else 0x1428c sets a1 = DIGINET_EV_STRIP_BUTTON (3). 0x14290 `sw a1, 0(s0)` is the kind,
     0x14294 `sb a0, 4(s0)` is strip = id.
   - 0x14298 `addi s1, zero, 1` and DN_RET: the event is event_cells of the model's event, the decoder and the frame
     are not written. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_decoder_next_c diginet_decoder_next_seg.
Import ListNotations.
Open Scope Z_scope.

(* the model's step on a note: the decoder takes the cursor c1 of diginet_msg_next, the event is decode_note of
   the zeroed event with the message and kind DIGINET_EV_OTHER (diginet_decode.c:115-122) *)
Lemma diginet_decoder_next_note_model : forall bb dc msg c1,
  diginet_msg_next (map bv_unsigned bb) (dd_c dc) dgn_msg_zero = (1, msg, c1) ->
  Z.land (dm_status msg) 0xf0 = 0x90 ->
  dn_d bb dc = {| dd_c := c1; dd_p := dd_p dc |} /\
  dn_e bb dc = decode_note msg (de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero)).
Proof.
  intros bb dc msg c1 MN PC. unfold dn_d, dn_e, dn_step, diginet_decoder_next. rewrite MN.
  cbv beta iota zeta. rewrite Z.eqb_refl. cbn [negb]. rewrite PC, Z.eqb_refl. cbn [fst snd].
  split; reflexivity.
Qed.

(* lbu of a byte cell *)
Lemma note_zxb_b8 : forall x, 0 <= x < 256 -> zxb (b8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. change (bv_unsigned (b8 x)) with (bz (b8 x)). rewrite bz_b8 by lia. reflexivity. Qed.

(* sb of a register: its low byte *)
Lemma note_le1_lit : forall e, le1 (Z_to_bv 64 e) = [Z_to_bv 8 e].
Proof.
  intros e. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 8 * 2 ^ 56). change (2 ^ Z.of_N 8) with (2 ^ 8).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

(* a boolean property of every byte value, checked on the 256 values *)
Lemma note_byte_cases : forall P : Z -> bool, forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x).
  split; [lia|]. apply in_seq. lia.
Qed.

(* 0x1407c `slli a2, a2, 0x39` / 0x14080 `srli a2, a2, 0x3f`: bit 6 of d2, diginet_decode.c:23 *)
Lemma note_on_bit : forall x, 0 <= x < 256 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 57))) 63 = u8 (int_of_bool (negb (Z.land x 0x40 =? 0))).
Proof.
  intros x Hx. apply Z.eqb_eq. revert x Hx.
  apply (note_byte_cases (fun x => Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 57))) 63 =?
                                   u8 (int_of_bool (negb (Z.land x 0x40 =? 0))))).
  vm_compute. reflexivity.
Qed.

(* 0x14084 `addi a4, a0, -0x18` / 0x14090 `bltu a3(5), a4`: the zone test of diginet_decode.c:25 *)
Lemma note_zone_test : forall id, 0 <= id < 64 ->
  (5 <? bv_unsigned (Z_to_bv 64 (id + -24))) = negb ((24 <=? id) && (id <=? 29)).
Proof.
  intros id Hid. rewrite unsigned_lit_wrap. destruct (Z.ltb_spec id 24) as [L|L].
  - rewrite <- (Z.mod_unique (id + -24) (2 ^ 64) (-1) (id + -24 + 2 ^ 64)) by lia.
    destruct (Z.leb_spec 24 id); [lia|]. cbn [andb negb]. apply Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia. destruct (Z.leb_spec 24 id); [|lia].
    destruct (Z.leb_spec id 29); cbn [andb negb]; [apply Z.ltb_ge | apply Z.ltb_lt]; lia.
Qed.

Lemma diginet_decoder_next_note_seg : forall (ra s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
    (spf d ev body : Z) (bb cpad mpad junk : list byte) (dc : dgn_decoder) (msg : dgn_msg) (c1 : dgn_cursor)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  dn_seg_pre m spf d ev body bb cpad mpad junk dc msg c1 ->
  Z.land (dm_status msg) 0xf0 = 0x90 ->
  dn_seg_cont Q spf gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d ev body bb cpad mpad dc ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DN_DECODE) fc None m (seg_rom rsegs)).
Proof.
  intros ra s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gp tp F fc m Q spf d ev body bb cpad mpad junk dc msg c1
    t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PRE PC K.
  destruct PRE as (MN & Hd0 & He0 & Hd8 & He8 & Hs16 & Hb0 & HLEN & HPOS & HST & HB & HD & HE & HM & HJ &
                   Dde & Ddb & Deb & Dds & Des & Dbs & MI).
  destruct (msg_next_one bb (dd_c dc) dgn_msg_zero msg c1 HLEN ltac:(lia) HST MN)
    as (Rst & Rd1 & Rd2 & _ & _ & _ & _ & _).
  destruct (diginet_decoder_next_note_model bb dc msg c1 MN PC) as [ED EE].
  pose proof (rw_cells_bound _ _ _ _ HE) as BE. rewrite event_cells_size in BE.
  pose proof (rw_cells_bound _ _ _ _ HD) as BD. rewrite decoder_cells_size in BD.
  pose proof (rw_cells_bound _ _ _ _ HM) as BM. rewrite dmsg_cells_size in BM.
  pose proof (rw_cells_bound _ _ _ _ HJ) as BJ. cbn [cells_size csize Nat.add] in BJ.
  clear HB HJ.
  pose proof (munch_refl [(d, d + 40); (ev, ev + 80); (spf, spf + 72)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold dn_seg_cont, DN_RET in K. rewrite ED, EE in K.
  destruct msg as [st run d1 d2 sx sxl off len]. cbn [dm_status dm_d1 dm_d2] in *.
  (* the cells as the kit's loads and stores read them *)
  unfold dmsg_cells in HM. cbn [dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len dm_offset dm_len] in HM.
  unfold event_cells, dmsg_cells, arr_cells, de_set_msg, dgn_event_zero in HE.
  cbn [map seq app nth repeat de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value
       de_delta de_mask de_segments de_len de_text de_seg de_dots de_device de_msg dm_status dm_running dm_d1
       dm_d2 dm_sysex dm_sysex_len dm_offset dm_len] in HE.
  unfold decoder_cells, cursor_cells in HD. cbn [dd_c dd_p app] in HD.
  assert (RID : 0 <= Z.land d2 63 < 64)
    by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (U : u8 (Z.land d2 63) = Z.land d2 63) by (unfold u8; apply Z.mod_small; lia).
  unfold DN_DECODE.
  (* 0x14054-0x14068: status, ev->kind = DIGINET_EV_OTHER, the note test *)
  step. rewrite (note_zxb_b8 st) by lia.
  step. step. rewrite (unsigned_lit st) by lia. rewrite PC.
  step. step.
  step. if_false.
  (* 0x1406c-0x1408c: id, on, button *)
  step. rewrite (note_zxb_b8 d2) by lia.
  step. rewrite (note_zxb_b8 d1) by lia.
  clear HM.
  step. step. step. step. step.
  rewrite (unsigned_lit d2) by lia. rewrite (note_on_bit d2) by lia.
  step. rewrite note_le1_lit. mem_after_store.
  step. rewrite note_le1_lit. mem_after_store.
  (* 0x14090: the zone test *)
  step. unfold bv_ltu. fold_lit_ux. rewrite (note_zone_test (Z.land d2 63) RID).
  destruct ((24 <=? Z.land d2 63) && (Z.land d2 63 <=? 29)) eqn:ZN; cbv beta iota delta [negb].
  - (* 0x14094-0x140a0 and 0x14298: a zone key *)
    step. step. step. rewrite note_le1_lit. mem_after_store.
    step. step.
    eapply K; [exact MU | exact WM | exact MI | | exact HD].
    unfold decode_note, DIGINET_ZONE_FIRST, DIGINET_ZONE_LAST. cbv zeta. cbn [dm_d1 dm_d2].
    rewrite U, ZN. cbv beta iota.
    exact HE.
  - (* 0x141c0 / 0x141c4: the touch test *)
    step. step. unfold bv_eqb. rewrite (unsigned_lit d1) by lia. fold_lit_ux.
    destruct (Z.eqb_spec d1 9) as [T9|T9]; cbv beta iota delta [negb].
    + (* 0x141c8, 0x141cc, 0x14290-0x14298: a touch *)
      step. step. step. step. rewrite note_le1_lit. mem_after_store. step.
      eapply K; [exact MU | exact WM | exact MI | | exact HD].
      unfold decode_note, DIGINET_ZONE_FIRST, DIGINET_ZONE_LAST, DIGINET_BTN_TOUCH. cbv zeta. cbn [dm_d1 dm_d2].
      rewrite U, ZN, (proj2 (Z.eqb_eq d1 9) T9). cbv beta iota.
      exact HE.
    + (* 0x1428c-0x14298: a strip button *)
      step. step. step. rewrite note_le1_lit. mem_after_store. step.
      eapply K; [exact MU | exact WM | exact MI | | exact HD].
      unfold decode_note, DIGINET_ZONE_FIRST, DIGINET_ZONE_LAST, DIGINET_BTN_TOUCH. cbv zeta. cbn [dm_d1 dm_d2].
      rewrite U, ZN, (proj2 (Z.eqb_neq d1 9) T9). cbv beta iota.
      exact HE.
Qed.
