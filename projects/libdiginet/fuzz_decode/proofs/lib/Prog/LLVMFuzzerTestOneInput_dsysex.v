(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: dsysex_holds, the segment lemma dsysex_stmt of LLVMFuzzerTestOneInput_seg.v.
   From 0x13228 (o = owed0 of a sysex message M) the inlined spec_event_of runs to 0x13180 with o = owed_at: kind
   OTHER; sysex_len < 3 or maker byte != 0x13: OTHER device 0; the device byte; the jump table at 0x103a4 on the
   function byte rotated (fn >> 4 | fn << 28, at most 7 only for fn = 0x00 .. 0x70, so the table load is read from
   the image at a concrete address in each case): ring 0x13284 with its LED loop 0x132b8 .. 0x13308 (one LED per
   dsysex_ring_it, the 14 LEDs in dsysex_ring_loop), meter 0x134c0 with its segments loop 0x13518 .. 0x13528,
   LEDs 0x1348c, counter 0x13538 with its digit loop 0x13560 .. 0x13578, scribble 0x13580 with memcpy at 0x135b0
   (through memcpy_contract, one case per text length 1 .. 8), 0x50 / 0x60 OTHER, system 0x134b4. Each handler's
   event is DgnSpec.spec_event_of by the dsysex_ev_* lemmas; a sysex event is never FADER, so owed_at keeps
   next and status_out (dsysex_owed_at). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Open Scope Z_scope.

Lemma dsysex_rd : forall m body bb i, bytes_at rsegs m body bb -> 0 <= i < Z.of_nat (length bb) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (body + i)) 1 = Some [nth (Z.to_nat i) bb (Z_to_bv 8 0)].
Proof.
  intros m body bb i H Hi.
  change (Z_to_bv 64 (body + i)) with (wa (body + i)).
  rewrite (bytes_at_read rsegs m body bb i 1 H ltac:(lia) ltac:(lia)).
  f_equal. clear H. remember (Z.to_nat i) as k. assert (Hk : (k < length bb)%nat) by lia. clear Heqk Hi.
  revert k Hk. induction bb as [|x bb IH]; intros [|k] Hk; cbn [length] in Hk; try lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma dsysex_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

(* ---- the model ---- *)

Lemma dsysex_scan_le : forall b len i fuel, i <= len -> scan_f7 b len i fuel <= len.
Proof.
  intros b len i fuel. revert i. induction fuel as [|f IH]; intros i Hi; cbn [scan_f7]; [lia|].
  destruct ((i <? len) && negb (byte_at b i =? 247)) eqn:E; [|lia].
  apply andb_true_iff in E as [E _]. apply Z.ltb_lt in E. apply IH. lia.
Qed.

Lemma dsysex_scan_ge : forall b len i fuel, i <= scan_f7 b len i fuel.
Proof.
  intros b len i fuel. revert i. induction fuel as [|f IH]; intros i; cbn [scan_f7]; [lia|].
  destruct (_ && _); [specialize (IH (i + 1)); lia | lia].
Qed.

(* a step's sysex fields: a length that is not 0 is the F0 message's, at pos + 1 and before the F7 *)
Lemma dsysex_msg : forall b len pos status, 0 <= pos ->
  0 <= sm_sysex_len (spec_msg_step b len pos status) /\
  (0 < sm_sysex_len (spec_msg_step b len pos status) ->
   sm_sysex_at (spec_msg_step b len pos status) = pos + 1 /\
   sm_sysex_at (spec_msg_step b len pos status) + sm_sysex_len (spec_msg_step b len pos status) < len).
Proof.
  intros b len pos status Hp. unfold spec_msg_step. cbv zeta.
  destruct (len <=? pos) eqn:E0; [cbn; lia|]. apply Z.leb_gt in E0.
  destruct (byte_at b pos =? 240).
  - pose proof (dsysex_scan_le b len (pos + 1) (Z.to_nat (len - (pos + 1))) ltac:(lia)).
    pose proof (dsysex_scan_ge b len (pos + 1) (Z.to_nat (len - (pos + 1)))).
    destruct (scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1))) =? len) eqn:E1; cbn [sm_sysex_len sm_sysex_at];
      [lia|]. apply Z.eqb_neq in E1. split; [lia|]. intros _. split; lia.
  - repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [sm_sysex_len]; lia.
Qed.

Lemma dsysex_byte_at : forall bb i, byte_at (bzl bb) i = bz (nth (Z.to_nat i) bb (Z_to_bv 8 0)).
Proof.
  intros bb i. unfold byte_at, bzl. change 0 with (bz (Z_to_bv 8 0)). apply map_nth.
Qed.

Lemma dsysex_owed_at : forall b len pos status,
  sm_code (spec_msg_step b len pos status) = 1 -> sm_status (spec_msg_step b len pos status) = 240 ->
  owed_at b len pos status =
  Owed (spec_msg_step b len pos status) (spec_event_of b (spec_msg_step b len pos status)) 0
    (sm_next (spec_msg_step b len pos status)) (sm_status_out (spec_msg_step b len pos status)).
Proof.
  intros b len pos status Hc Hs. unfold owed_at. cbv zeta. rewrite Hc. cbn [Z.eqb negb Pos.eqb].
  replace (se_kind (spec_event_of b (spec_msg_step b len pos status)) =? SPEC_EV_FADER) with false;
    [reflexivity|].
  symmetry. apply Z.eqb_neq. unfold spec_event_of. cbv zeta. rewrite Hs.
  change (Z.land 240 240 =? 144) with false. change (Z.land 240 240 =? 176) with false.
  change (negb (240 =? 240)) with false. cbv iota.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    cbn [se_kind se_other]; unfold SPEC_EV_FADER, SPEC_EV_OTHER, SPEC_EV_RING, SPEC_EV_METER, SPEC_EV_STRIP_LEDS,
      SPEC_EV_SCRIBBLE, SPEC_EV_COUNTER, SPEC_EV_SYSTEM; lia.
Qed.

Lemma dsysex_ev_other0 : forall b M, sm_status M = 240 ->
  (sm_sysex_len M < 3 \/ byte_at b (sm_sysex_at M) <> 19) -> spec_event_of b M = se_other 0.
Proof.
  intros b M Hs H. unfold spec_event_of. cbv zeta. rewrite Hs.
  change (Z.land 240 240 =? 144) with false. change (Z.land 240 240 =? 176) with false.
  change (negb (240 =? 240)) with false. cbv iota.
  replace ((sm_sysex_len M <? 3) || negb (byte_at b (sm_sysex_at M) =? SPEC_MAKER)) with true; [reflexivity|].
  symmetry. unfold SPEC_MAKER. destruct H as [H|H].
  - apply orb_true_iff. left. apply Z.ltb_lt. exact H.
  - apply orb_true_iff. right. apply negb_true_iff. apply Z.eqb_neq. exact H.
Qed.
Lemma dsysex_brng : forall b : byte, 0 <= bz b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma dsysex_eqb : forall (b : byte) k, 0 <= k < 256 -> bv_eqb (zxb b) (Z_to_bv 64 k) = (bz b =? k).
Proof.
  intros b k Hk. pose proof (dsysex_brng b). unfold bv_eqb, zxb, bz in *. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma dsysex_b8_bz : forall b : byte, b8 (bz b) = b.
Proof.
  intros b. unfold b8, bz. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* the jump-table index fn >> 4 | fn << 28 (32-bit): at most 7 exactly when fn is 0x00, 0x10, .., 0x70 *)
Lemma dsysex_fn_cases : forall f, 0 <= f < 256 ->
  f = 0 \/ f = 16 \/ f = 32 \/ f = 48 \/ f = 64 \/ f = 80 \/ f = 96 \/ f = 112 \/ (Z.land f 15 <> 0 \/ 128 <= f).
Proof.
  intros f Hf. change 15 with (Z.ones 4). rewrite (Z.land_ones f 4) by lia. change (2 ^ 4) with 16.
  destruct (Z.eq_dec (f mod 16) 0) as [E|E]; [| do 8 right; left; exact E].
  destruct (Z_lt_le_dec f 128) as [L|L]; [| do 8 right; right; exact L].
  assert (Q : f = 16 * (f / 16)) by (Z.div_mod_to_equations; lia).
  assert (R : 0 <= f / 16 < 8) by (Z.div_mod_to_equations; lia).
  remember (f / 16) as q eqn:Eq. clear Eq. subst f.
  assert (C : q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.mul Pos.mul]; tauto.
Qed.

Lemma dsysex_fn_notin : forall f, (Z.land f 15 <> 0 \/ 128 <= f) -> ~ In f [0; 16; 32; 48; 64; 112].
Proof.
  intros f H HI. cbn [In] in HI.
  destruct HI as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; destruct H as [H|H]; try lia; apply H; reflexivity.
Qed.

Lemma dsysex_idx_big : forall b : byte, (Z.land (bz b) 15 <> 0 \/ 128 <= bz b) ->
  bv_ltu (Z_to_bv 64 7)
    (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (zxb b)) 28))))
                       (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (zxb b)) 4))))) = true.
Proof.
  intros b H. pose proof (dsysex_brng b) as R. unfold bz in *.
  assert (U : bv_unsigned (zxb b) = bv_unsigned b) by (unfold zxb; apply unsigned_lit; lia).
  rewrite U. remember (bv_unsigned b) as f eqn:Ef. clear Ef U b.
  assert (C : forallb (fun f => implb (negb ((Z.land f 15 =? 0) && (f <? 128)))
     (bv_ltu (Z_to_bv 64 7)
       (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl f 28))))
                          (bv_unsigned (Z_to_bv 64 (Z.shiftr f 4))))))) (zseq 256) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C.
  assert (I : In f (zseq 256)).
  { unfold zseq. apply in_map_iff. exists (Z.to_nat f). split; [lia|]. apply in_seq. lia. }
  specialize (C f I).
  replace (negb ((Z.land f 15 =? 0) && (f <? 128))) with true in C; [exact C|].
  symmetry. apply negb_true_iff, andb_false_iff. destruct H as [H|H].
  - left. apply Z.eqb_neq. exact H.
  - right. apply Z.ltb_ge. exact H.
Qed.

(* opening spec_event_of at a sysex message whose maker byte is 0x13 *)
Ltac ev_open Hs Hn Hm :=
  unfold spec_event_of; cbv zeta; rewrite Hs;
  change (Z.land 240 240 =? 144) with false; change (Z.land 240 240 =? 176) with false;
  change (negb (240 =? 240)) with false; cbv iota;
  lazymatch goal with
  | |- context [(sm_sysex_len ?M <? 3) || negb (byte_at ?b (sm_sysex_at ?M) =? SPEC_MAKER)] =>
      replace ((sm_sysex_len M <? 3) || negb (byte_at b (sm_sysex_at M) =? SPEC_MAKER)) with false
        by (symmetry; rewrite Hm; apply orb_false_iff; split; [apply Z.ltb_ge; lia | reflexivity])
  end;
  cbv iota;
  unfold SPEC_FN_RING, SPEC_FN_METER, SPEC_FN_LEDS, SPEC_FN_SCRIBBLE, SPEC_FN_COUNTER, SPEC_FN_SYSTEM.

Lemma dsysex_ev_fn_other : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M ->
  byte_at b (sm_sysex_at M) = 19 -> ~ In (byte_at b (sm_sysex_at M + 2)) [0; 16; 32; 48; 64; 112] ->
  spec_event_of b M = se_other (byte_at b (sm_sysex_at M + 1)).
Proof.
  intros b M Hs Hn Hm Hf. ev_open Hs Hn Hm. cbn [In] in Hf.
  replace (byte_at b (sm_sysex_at M + 2) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (byte_at b (sm_sysex_at M + 2) =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (byte_at b (sm_sysex_at M + 2) =? 32) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (byte_at b (sm_sysex_at M + 2) =? 64) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (byte_at b (sm_sysex_at M + 2) =? 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (byte_at b (sm_sysex_at M + 2) =? 112) with false by (symmetry; apply Z.eqb_neq; lia).
  reflexivity.
Qed.

Ltac fn_lit b Fk :=
  lazymatch type of Fk with
  | bz b = ?k =>
      let E := fresh "E" in
      assert (E : b = Z_to_bv 8 k) by (rewrite <- Fk; symmetry; apply dsysex_b8_bz);
      rewrite E in *; clear E; change (zxb (Z_to_bv 8 k)) with (Z_to_bv 64 k)
  end.


Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; usub; fold_lit_ux; solve_cond_rec.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.
Ltac rdb i :=
  lazymatch goal with
  | BA : bytes_at rsegs ?mm ?body ?bb |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let R := fresh "RD" in pose proof (dsysex_rd mm body bb i BA ltac:(lia)) as R
  end.
Ltac sbstep := step; rewrite ?le1_zxb, ?dsysex_le1; mem_after_store_opt.
(* a term with no local variable *)
Ltac dsx_closed t :=
  lazymatch t with
  | bv_unsigned ?a => dsx_closed a
  | ?f ?a => dsx_closed f; dsx_closed a
  | _ => first [ is_const t | is_constructor t | is_ind t ]
  end.
(* a closed word or condition, computed *)
Ltac fold_cl :=
  repeat match goal with
  | |- context [bv_unsigned ?t] =>
      dsx_closed t;
      let v := eval vm_compute in (bv_unsigned t) in is_Zlit v;
      replace (bv_unsigned t) with v by (vm_compute; reflexivity)
  | |- context [Z.modulo ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [if ?c then _ else _] =>
      dsx_closed c;
      let v := eval vm_compute in c in
      lazymatch v with
      | true => replace c with true by (vm_compute; reflexivity)
      | false => replace c with false by (vm_compute; reflexivity)
      end; cbv iota
  end.

(* ---- the ring's LED loop, 0x132b8 .. 0x13308 ---- *)

Lemma dsysex_in_zseq : forall n z, 0 <= z < Z.of_nat n -> In z (zseq n).
Proof.
  intros n z H. unfold zseq. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma dsysex_byte_all : forall P : Z -> bool, forallb P (zseq 256) = true -> forall p : byte, P (bz p) = true.
Proof.
  intros P H p. rewrite forallb_forall in H. apply H. apply dsysex_in_zseq. pose proof (dsysex_brng p). lia.
Qed.

(* beqz of (byte >> sh) & 1, srlw on the zero-extended byte *)
Lemma dsysex_bit : forall (p : byte) sh, 0 <= sh < 8 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (zxb p))) sh))))
    1)) (Z_to_bv 64 0) = negb (Z.land (Z.shiftr (bz p) sh) 1 =? 1).
Proof.
  intros p sh Hsh.
  assert (C : forallb (fun z => forallb (fun sh =>
      Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32
        (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 z))) sh)))) 1)) (Z_to_bv 64 0))
        (negb (Z.land (Z.shiftr z sh) 1 =? 1))) (zseq 8)) (zseq 256) = true) by (vm_compute; reflexivity).
  pose proof (dsysex_byte_all _ C p) as C1. cbv beta in C1. rewrite forallb_forall in C1.
  specialize (C1 sh (dsysex_in_zseq 8 sh ltac:(lia))). apply Bool.eqb_prop in C1. exact C1.
Qed.

Lemma dsysex_lor_lt : forall a b n, 0 < n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|A]; [cbn; lia | apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec b 0) as [->|B]; [cbn; lia | apply Z.log2_lt_pow2; lia].
Qed.

Lemma dsysex_ring_set : forall p1 p2 mask led, 2 <= led <= 15 -> 0 <= mask < 2 ^ 15 ->
  Z.land (Z.shiftr (if led <=? 8 then p1 else p2) (if led <=? 8 then 8 - led else 15 - led)) 1 = 1 ->
  ring_step p1 p2 mask led = Z.lor mask (2 ^ (led - 1)).
Proof.
  intros p1 p2 mask led Hl Hm Hb. unfold ring_step. cbv zeta. rewrite Hb, Z.eqb_refl.
  assert (P : 0 <= 2 ^ (led - 1) < 2 ^ 15) by (split; [lia|]; apply Z.pow_lt_mono_r; lia).
  pose proof (dsysex_lor_lt mask (2 ^ (led - 1)) 15 ltac:(lia) Hm P) as L.
  unfold u16. rewrite Z.shiftl_1_l, (Z.mod_small (2 ^ (led - 1))) by lia. apply Z.mod_small. lia.
Qed.

Lemma dsysex_ring_clr : forall p1 p2 mask led,
  Z.land (Z.shiftr (if led <=? 8 then p1 else p2) (if led <=? 8 then 8 - led else 15 - led)) 1 <> 1 ->
  ring_step p1 p2 mask led = mask.
Proof.
  intros p1 p2 mask led Hb. unfold ring_step. cbv zeta.
  destruct (Z.eqb_spec (Z.land (Z.shiftr (if led <=? 8 then p1 else p2) (if led <=? 8 then 8 - led else 15 - led)) 1) 1);
    [contradiction | reflexivity].
Qed.

Lemma dsysex_ring_rng : forall p1 p2 mask led, 2 <= led <= 15 -> 0 <= mask < 2 ^ 15 ->
  0 <= ring_step p1 p2 mask led < 2 ^ 15.
Proof.
  intros p1 p2 mask led Hl Hm.
  destruct (Z.eq_dec (Z.land (Z.shiftr (if led <=? 8 then p1 else p2) (if led <=? 8 then 8 - led else 15 - led)) 1) 1)
    as [B|B].
  - rewrite dsysex_ring_set by assumption. apply dsysex_lor_lt; [lia | exact Hm |].
    split; [lia|]. apply Z.pow_lt_mono_r; lia.
  - rewrite dsysex_ring_clr by exact B. exact Hm.
Qed.

Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => idtac end.

Lemma dsysex_ev_sys : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M ->
  byte_at b (sm_sysex_at M) = 19 -> byte_at b (sm_sysex_at M + 2) = 112 ->
  spec_event_of b M =
  {| se_kind := SPEC_EV_SYSTEM; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0; se_right := 0;
     se_addr := 0; se_device := byte_at b (sm_sysex_at M + 1); se_len := 0; se_dots := 0; se_value := 0;
     se_mask := 0; se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}.
Proof. intros b M Hs Hn Hm Hf. ev_open Hs Hn Hm. rewrite Hf. fold_cl. reflexivity. Qed.

Lemma dsysex_ev_leds : forall b M, sm_status M = 240 -> sm_sysex_len M = 5 ->
  byte_at b (sm_sysex_at M) = 19 -> byte_at b (sm_sysex_at M + 2) = 32 ->
  spec_event_of b M =
  {| se_kind := SPEC_EV_STRIP_LEDS; se_strip := byte_at b (sm_sysex_at M + 3); se_button := 0; se_zone := 0;
     se_on := 0; se_right := 0; se_addr := byte_at b (sm_sysex_at M + 3);
     se_device := byte_at b (sm_sysex_at M + 1); se_len := 0; se_dots := 0; se_value := 0;
     se_mask := byte_at b (sm_sysex_at M + 4); se_delta := 0; se_segments := 0; se_text := repeat 0 8;
     se_seg := repeat 0 8 |}.
Proof.
  intros b M Hs Hn Hm Hf. assert (Hn3 : 3 <= sm_sysex_len M) by lia. ev_open Hs Hn3 Hm.
  rewrite Hf, Hn. fold_cl.
  replace (sm_sysex_at M + 3 + 1) with (sm_sysex_at M + 4) by lia. reflexivity.
Qed.

Lemma dsysex_ev_counter : forall b M, sm_status M = 240 -> sm_sysex_len M = 13 ->
  byte_at b (sm_sysex_at M) = 19 -> byte_at b (sm_sysex_at M + 2) = 48 ->
  spec_event_of b M =
  {| se_kind := SPEC_EV_COUNTER; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0; se_right := 0;
     se_addr := byte_at b (sm_sysex_at M + 3); se_device := byte_at b (sm_sysex_at M + 1); se_len := 0;
     se_dots := byte_at b (sm_sysex_at M + 4); se_value := 0; se_mask := 0; se_delta := 0; se_segments := 0;
     se_text := repeat 0 8;
     se_seg := [byte_at b (sm_sysex_at M + 12); byte_at b (sm_sysex_at M + 11); byte_at b (sm_sysex_at M + 10);
                byte_at b (sm_sysex_at M + 9); byte_at b (sm_sysex_at M + 8); byte_at b (sm_sysex_at M + 7);
                byte_at b (sm_sysex_at M + 6); byte_at b (sm_sysex_at M + 5)] |}.
Proof.
  intros b M Hs Hn Hm Hf. assert (Hn3 : 3 <= sm_sysex_len M) by lia. ev_open Hs Hn3 Hm.
  rewrite Hf, Hn. fold_cl.
  replace (sm_sysex_at M + 3 + 1) with (sm_sysex_at M + 4) by lia.
  unfold zseq, SPEC_DIGITS. cbn [map seq Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat match goal with
  | |- context [byte_at b (sm_sysex_at M + 3 + 2 + 8 - 1 - ?k)] =>
      let v := eval vm_compute in (3 + 2 + 8 - 1 - k) in
      replace (sm_sysex_at M + 3 + 2 + 8 - 1 - k) with (sm_sysex_at M + v) by lia
  end.
  reflexivity.
Qed.

Lemma dsysex_ev_meter : forall b M, sm_status M = 240 -> sm_sysex_len M = 6 ->
  byte_at b (sm_sysex_at M) = 19 -> byte_at b (sm_sysex_at M + 2) = 16 ->
  spec_event_of b M =
  let p0 := byte_at b (sm_sysex_at M + 3) in
  let mk := u16 (Z.lor (Z.shiftl (Z.land (byte_at b (sm_sysex_at M + 4)) 127) 7)
                       (Z.land (byte_at b (sm_sysex_at M + 5)) 127)) in
  {| se_kind := SPEC_EV_METER; se_strip := Z.land p0 31; se_button := 0; se_zone := 0; se_on := 0;
     se_right := Z.land (Z.shiftr p0 5) 1; se_addr := p0; se_device := byte_at b (sm_sysex_at M + 1);
     se_len := 0; se_dots := 0; se_value := 0; se_mask := mk; se_delta := 0;
     se_segments := s8 (spec_segments mk); se_text := repeat 0 8; se_seg := repeat 0 8 |}.
Proof.
  intros b M Hs Hn Hm Hf. assert (Hn3 : 3 <= sm_sysex_len M) by lia. ev_open Hs Hn3 Hm.
  rewrite Hf, Hn. fold_cl.
  replace (sm_sysex_at M + 3 + 1) with (sm_sysex_at M + 4) by lia.
  replace (sm_sysex_at M + 3 + 2) with (sm_sysex_at M + 5) by lia.
  reflexivity.
Qed.

Lemma dsysex_ev_scribble : forall b M, sm_status M = 240 -> 6 <= sm_sysex_len M <= 13 ->
  byte_at b (sm_sysex_at M) = 19 -> byte_at b (sm_sysex_at M + 2) = 64 ->
  spec_event_of b M =
  {| se_kind := SPEC_EV_SCRIBBLE; se_strip := 0; se_button := 0; se_zone := 0; se_on := 0; se_right := 0;
     se_addr := byte_at b (sm_sysex_at M + 3); se_device := byte_at b (sm_sysex_at M + 1);
     se_len := sm_sysex_len M - 5; se_dots := 0; se_value := 0; se_mask := 0; se_delta := 0;
     se_segments := 0;
     se_text := map (fun k => if k <? sm_sysex_len M - 5 then byte_at b (sm_sysex_at M + 5 + k) else 0) (zseq 8);
     se_seg := repeat 0 8 |}.
Proof.
  intros b M Hs Hn Hm Hf. assert (Hn3 : 3 <= sm_sysex_len M) by lia. ev_open Hs Hn3 Hm.
  rewrite Hf. fold_cl.
  replace ((sm_sysex_len M - 3 <? 3) || (SPEC_CHARS_MAX <? sm_sysex_len M - 3 - 2)) with false
    by (symmetry; apply orb_false_iff; unfold SPEC_CHARS_MAX; split; apply Z.ltb_ge; lia).
  cbv iota.
  replace (u8 (sm_sysex_len M - 3 - 2)) with (sm_sysex_len M - 5) by (unfold u8; rewrite Z.mod_small; lia).
  replace (sm_sysex_at M + 3 + 2) with (sm_sysex_at M + 5) by lia.
  reflexivity.
Qed.

(* a mask none of whose 15 thermometer values matches *)
Lemma dsysex_seg_none : forall mk,
  mk <> 0 -> mk <> 1 -> mk <> 3 -> mk <> 7 -> mk <> 15 -> mk <> 31 -> mk <> 63 -> mk <> 127 -> mk <> 255 ->
  mk <> 511 -> mk <> 1023 -> mk <> 2047 -> mk <> 4095 -> mk <> 8191 -> mk <> 16383 -> spec_segments mk = -1.
Proof.
  intros mk N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 N14.
  unfold spec_segments. cbn [segments_loop]. fold_cl.
  repeat match goal with
  | |- context [mk =? ?v] => replace (mk =? v) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.

Lemma dsysex_zxb_u : forall p : byte, bv_unsigned (zxb p) = bz p.
Proof. intros p. pose proof (dsysex_brng p). unfold zxb, bz in *. apply unsigned_lit. lia. Qed.
Lemma dsysex_land_rng : forall x n, 0 <= n -> 0 <= Z.land x (Z.ones n) < 2 ^ n.
Proof. intros x n Hn. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.
(* the meter's right bit, p0 >> 5 & 1 by slli 58; srli 63 *)
Lemma dsysex_m5 : forall p : byte,
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb p)) 58))) 63 = Z.land (Z.shiftr (bz p) 5) 1.
Proof.
  intros p.
  assert (C : forallb (fun z => Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 58))) 63
                                =? Z.land (Z.shiftr z 5) 1) (zseq 256) = true) by (vm_compute; reflexivity).
  apply Z.eqb_eq. exact (dsysex_byte_all _ C p).
Qed.

Lemma dsysex_l127 : forall a, 0 <= Z.land a 127 < 128.
Proof. intros a. pose proof (dsysex_land_rng a 7 ltac:(lia)) as L. change (Z.ones 7) with 127 in L. exact L. Qed.

(* the meter mask (p1 & 0x7f) << 7 | (p2 & 0x7f) *)
Lemma dsysex_mk_rng : forall a c, 0 <= Z.lor (Z.shiftl (Z.land a 127) 7) (Z.land c 127) < 2 ^ 14.
Proof.
  intros a c. pose proof (dsysex_l127 a). pose proof (dsysex_l127 c).
  apply dsysex_lor_lt; [lia | | lia]. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma dsysex_mk : forall p1 p2 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb p1)) 127))) 7)))
        (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb p2)) 127)))
  = Z.lor (Z.shiftl (Z.land (bz p1) 127) 7) (Z.land (bz p2) 127).
Proof.
  intros p1 p2. rewrite !dsysex_zxb_u. pose proof (dsysex_l127 (bz p1)). pose proof (dsysex_l127 (bz p2)).
  rewrite (unsigned_lit (Z.land (bz p1) 127)), (unsigned_lit (Z.land (bz p2) 127)) by lia.
  rewrite unsigned_lit; [reflexivity|]. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma dsysex_mk_u16 : forall a c,
  u16 (Z.lor (Z.shiftl (Z.land a 127) 7) (Z.land c 127)) = Z.lor (Z.shiftl (Z.land a 127) 7) (Z.land c 127).
Proof. intros a c. pose proof (dsysex_mk_rng a c). unfold u16. apply Z.mod_small. lia. Qed.

(* beq of (-1 << n) ^ mask with -1 *)
Lemma dsysex_meq : forall a x, 0 <= a < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 (Z.lxor a x)) (Z_to_bv 64 (-1)) = (x =? Z.lxor a 18446744073709551615).
Proof.
  intros a x Ha Hx. unfold bv_eqb.
  assert (R : 0 <= Z.lxor a x < 2 ^ 64) by (apply Z_lxor_range; lia).
  rewrite unsigned_lit by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by (vm_compute; reflexivity).
  destruct (Z.eqb_spec (Z.lxor a x) 18446744073709551615) as [E|E];
    destruct (Z.eqb_spec x (Z.lxor a 18446744073709551615)) as [E'|E']; try reflexivity; exfalso.
  - apply E'. rewrite <- E, <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
  - apply E. rewrite E', <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
Qed.

(* one LED: from the loop head with led, mask to the next head (or the loop exit 0x1330c) *)
Lemma dsysex_ring_it :
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 a4 a5 : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) (Sp body s led mask : Z) (bb : list byte)
    (pre post : list cell) (mb m : word -> option byte),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> 0 < body -> body + Z.of_nat (length bb) <= Sp -> 0 <= s ->
  s + 5 < Z.of_nat (length bb) -> cells_size pre = 104%nat -> 2 <= led <= 15 -> 0 <= mask < 2 ^ 15 ->
  bytes_at rsegs m body bb -> rw_cells rsegs m Sp pre -> rw_cells rsegs m (Sp + 104) [C2 (Z_to_bv 64 mask)] ->
  rw_cells rsegs m (Sp + 106) post -> munch [(Sp + 32, Sp + 152)] mb m -> wmono rsegs mb m -> mem_inv rsegs m ->
  (forall (m' : word -> option byte) (a4' a5' : word),
     bytes_at rsegs m' body bb -> rw_cells rsegs m' Sp pre ->
     rw_cells rsegs m' (Sp + 104)
       [C2 (Z_to_bv 64 (ring_step (bz (nth (Z.to_nat (s + 4)) bb (Z_to_bv 8 0)))
                                  (bz (nth (Z.to_nat (s + 5)) bb (Z_to_bv 8 0))) mask led))] ->
     rw_cells rsegs m' (Sp + 106) post -> munch [(Sp + 32, Sp + 152)] mb m' -> wmono rsegs mb m' ->
     mem_inv rsegs m' ->
     evt rsegs Q
       (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (led + 1)) (Z_to_bv 64 (body + s))
              (Z_to_bv 64 (ring_step (bz (nth (Z.to_nat (s + 4)) bb (Z_to_bv 8 0)))
                                     (bz (nth (Z.to_nat (s + 5)) bb (Z_to_bv 8 0))) mask led))
              (Z_to_bv 64 (- (led + 1))) a4' a5' x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 1)
              x28 x29 x30 x31)
           F (Z_to_bv 64 (if led =? 15 then 0x1330c else 0x132b8)) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 led) (Z_to_bv 64 (body + s)) (Z_to_bv 64 mask)
           (Z_to_bv 64 (- led)) a4 a5 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 1)
           x28 x29 x30 x31)
        F (Z_to_bv 64 0x132b8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 a4 a5
    F fc Q Sp body s led mask bb pre post mb m H0 H1 H2 H3 Hs Hs5 Hpre Hled Hmask BA FP FM FQ MU WM MI K.
  pose proof (dsysex_rd m body bb (s + 4) BA ltac:(lia)) as RD4.
  pose proof (dsysex_rd m body bb (s + 5) BA ltac:(lia)) as RD5.
  remember (nth (Z.to_nat (s + 4)) bb (Z_to_bv 8 0)) as P1 eqn:EP1.
  remember (nth (Z.to_nat (s + 5)) bb (Z_to_bv 8 0)) as P2 eqn:EP2.
  assert (C : led = 2 \/ led = 3 \/ led = 4 \/ led = 5 \/ led = 6 \/ led = 7 \/ led = 8 \/ led = 9 \/
              led = 10 \/ led = 11 \/ led = 12 \/ led = 13 \/ led = 14 \/ led = 15) by lia.
  destruct C as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ]]]]]]]]]]]]].
  all: step; repeat (tryif at_pc 0x132e8 then fail else (step; fold_cl)).
  all: step; rewrite dsysex_bit by lia.
  all: lazymatch goal with
       | |- context [Z.land (Z.shiftr ?b ?k) 1 =? 1] => destruct (Z.land (Z.shiftr b k) 1 =? 1) eqn:BIT
       end; cbn [negb]; cbv iota.
  all: repeat (tryif (first [at_pc 0x132b8 | at_pc 0x1330c]) then fail
               else (step; fold_cl; rewrite ?(unsigned_lit mask) by lia)).
  all: lazymatch type of K with
       | context [ring_step ?a ?b ?mk ?L] =>
           lazymatch goal with
           | BIT : (_ =? 1) = true |- _ =>
               rewrite (dsysex_ring_set a b mask L ltac:(lia) Hmask (proj1 (Z.eqb_eq _ _) BIT)) in K
           | BIT : (_ =? 1) = false |- _ =>
               rewrite (dsysex_ring_clr a b mask L (proj1 (Z.eqb_neq _ _) BIT)) in K
           end
       end.
  all: eapply K; eassumption.
Qed.

Ltac ring_bnd := repeat (apply dsysex_ring_rng; [lia|]); assumption.
Ltac ring_next B P O W :=
  eapply dsysex_ring_it with (bb := B) (pre := P) (post := O) (mb := W);
  [ lia | lia | lia | lia | lia | lia | assumption | lia | ring_bnd
  | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | ];
  let m' := fresh "m" in intros m' ? ? ? ? ? ? ? ? ?.

(* the 14 LEDs 2..15 *)
Lemma dsysex_ring_loop :
  forall (x1 x3 x4 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 a4 a5 : word)
    (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) (Sp body s mask : Z) (bb : list byte)
    (pre post : list cell) (mb m : word -> option byte),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> 0 < body -> body + Z.of_nat (length bb) <= Sp -> 0 <= s ->
  s + 5 < Z.of_nat (length bb) -> cells_size pre = 104%nat -> 0 <= mask < 2 ^ 15 ->
  bytes_at rsegs m body bb -> rw_cells rsegs m Sp pre -> rw_cells rsegs m (Sp + 104) [C2 (Z_to_bv 64 mask)] ->
  rw_cells rsegs m (Sp + 106) post -> munch [(Sp + 32, Sp + 152)] mb m -> wmono rsegs mb m -> mem_inv rsegs m ->
  (forall (m' : word -> option byte) (a4' a5' : word),
     let mk := fold_left (ring_step (bz (nth (Z.to_nat (s + 4)) bb (Z_to_bv 8 0)))
                                    (bz (nth (Z.to_nat (s + 5)) bb (Z_to_bv 8 0))))
                 [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] mask in
     bytes_at rsegs m' body bb -> rw_cells rsegs m' Sp pre ->
     rw_cells rsegs m' (Sp + 104) [C2 (Z_to_bv 64 mk)] ->
     rw_cells rsegs m' (Sp + 106) post -> munch [(Sp + 32, Sp + 152)] mb m' -> wmono rsegs mb m' ->
     mem_inv rsegs m' ->
     evt rsegs Q
       (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 16) (Z_to_bv 64 (body + s))
              (Z_to_bv 64 mk) (Z_to_bv 64 (-16)) a4' a5' x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 1)
              x28 x29 x30 x31)
           F (Z_to_bv 64 0x1330c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 2) (Z_to_bv 64 (body + s)) (Z_to_bv 64 mask)
           (Z_to_bv 64 (-2)) a4 a5 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 1)
           x28 x29 x30 x31)
        F (Z_to_bv 64 0x132b8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 a4 a5
    F fc Q Sp body s mask bb pre post mb m H0 H1 H2 H3 Hs Hs5 Hpre Hmask BA FP FM FQ MU WM MI K.
  do 14 ring_next bb pre post mb.
  cbn [fold_left] in K. cbv zeta in K. eapply K; eassumption.
Qed.

(* ---- cells ---- *)

Lemma dsysex_rwc_split : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[W B] (Ra & Rb & R)].
  apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in Rb, R.
  split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]); intros i Hi.
  - apply R. lia.
  - replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply R. lia.
Qed.

Lemma dsysex_rwc_app : forall segs m A cs1 cs2, rw_cells segs m A cs1 ->
  rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] (R1a & R1b & R1)] [[W2 B2] (R2a & R2b & R2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [H|H]; [apply R1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply R2. lia.
Qed.

Lemma dsysex_rwc_cut : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H. apply dsysex_rwc_split. exact H. Qed.

Lemma dsysex_rwc_eq : forall segs m A cs cs', rw_cells segs m A cs -> cs = cs' -> rw_cells segs m A cs'.
Proof. intros segs m A cs cs' H ->. exact H. Qed.

(* the body bytes i .. i + l - 1, as one list *)
Lemma dsysex_bytes_sub : forall m body bb i l, bytes_at rsegs m body bb -> 0 <= i ->
  i + Z.of_nat l <= Z.of_nat (length bb) ->
  bytes_at rsegs m (body + i) (map (fun k => nth (Z.to_nat (i + Z.of_nat k)) bb (Z_to_bv 8 0)) (seq 0 l)).
Proof.
  intros m body bb i l (B0 & B1 & B) Hi Hl.
  split; [lia|]. rewrite length_map, length_seq. split; [lia|]. intros j Hj.
  assert (E1 : nth_error (seq 0 l) j = Some j).
  { rewrite nth_error_nth' with (d := 0%nat) by (rewrite length_seq; lia). rewrite seq_nth by lia. reflexivity. }
  rewrite (map_nth_error _ _ _ E1).
  rewrite <- (nth_error_nth' bb (Z_to_bv 8 0)) by lia.
  replace (body + i + Z.of_nat j) with (body + Z.of_nat (Z.to_nat (i + Z.of_nat j))) by lia.
  apply B. lia.
Qed.

Lemma dsysex_rwc_one : forall segs m A cs, rw_cells segs m A cs ->
  rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros segs m A cs H. pose proof (rw_cells_merge segs m A [] cs []) as M.
  rewrite app_nil_r in M. cbn [app] in M. apply M. exact H.
Qed.

Lemma dsysex_rwc_c1s : forall segs m A n bs, rw_cells segs m A [CB n bs] -> rw_cells segs m A (map C1 bs).
Proof.
  intros segs m A n bs [[W B] R]. cbn [cells_wf cell_wf] in W. destruct W as [W _].
  assert (E : cells_bytes (map C1 bs) = bs) by (clear; induction bs as [|x bs IH]; cbn; [reflexivity | rewrite IH; reflexivity]).
  assert (S : cells_size (map C1 bs) = length bs) by (clear; induction bs as [|x bs IH]; cbn; [reflexivity | rewrite IH; reflexivity]).
  assert (WF : cells_wf (map C1 bs)) by (clear; induction bs as [|x bs IH]; cbn; [exact I | split; [exact I | exact IH]]).
  split; [split; [exact WF | rewrite E; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B]|].
  rewrite S, W. cbn [cells_size csize] in R. rewrite Nat.add_0_r in R. exact R.
Qed.


(* the ring's first mask bit, p0 >> 6 & 1 by slli 57; srli 63 *)
Lemma dsysex_m0 : forall p : byte,
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb p)) 57))) 63 = Z.land (Z.shiftr (bz p) 6) 1.
Proof.
  intros p.
  assert (C : forallb (fun z => Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 57))) 63
                                =? Z.land (Z.shiftr z 6) 1) (zseq 256) = true) by (vm_compute; reflexivity).
  apply Z.eqb_eq. exact (dsysex_byte_all _ C p).
Qed.

Lemma dsysex_ev_ring : forall b M, sm_status M = 240 -> sm_sysex_len M = 6 ->
  byte_at b (sm_sysex_at M) = 19 -> byte_at b (sm_sysex_at M + 2) = 0 ->
  spec_event_of b M =
  {| se_kind := SPEC_EV_RING; se_strip := Z.land (byte_at b (sm_sysex_at M + 3)) 63; se_button := 0;
     se_zone := 0; se_on := 0; se_right := 0; se_addr := 0; se_device := byte_at b (sm_sysex_at M + 1);
     se_len := 0; se_dots := 0; se_value := 0;
     se_mask := ring_mask (byte_at b (sm_sysex_at M + 3)) (byte_at b (sm_sysex_at M + 4))
                  (byte_at b (sm_sysex_at M + 5));
     se_delta := 0; se_segments := 0; se_text := repeat 0 8; se_seg := repeat 0 8 |}.
Proof.
  intros b M Hs Hn Hm Hf. assert (Hn3 : 3 <= sm_sysex_len M) by lia. ev_open Hs Hn3 Hm.
  rewrite Hf, Hn. fold_cl.
  replace (sm_sysex_at M + 3 + 1) with (sm_sysex_at M + 4) by lia.
  replace (sm_sysex_at M + 3 + 2) with (sm_sysex_at M + 5) by lia.
  reflexivity.
Qed.

(* a known function whose payload length is wrong: OTHER with the device *)
Lemma dsysex_ev_pn_other : forall b M, sm_status M = 240 -> 3 <= sm_sysex_len M ->
  byte_at b (sm_sysex_at M) = 19 ->
  (byte_at b (sm_sysex_at M + 2) = 0 /\ sm_sysex_len M <> 6 \/
   byte_at b (sm_sysex_at M + 2) = 16 /\ sm_sysex_len M <> 6 \/
   byte_at b (sm_sysex_at M + 2) = 32 /\ sm_sysex_len M <> 5 \/
   byte_at b (sm_sysex_at M + 2) = 64 /\ (sm_sysex_len M < 6 \/ 13 < sm_sysex_len M) \/
   byte_at b (sm_sysex_at M + 2) = 48 /\ sm_sysex_len M <> 13) ->
  spec_event_of b M = se_other (byte_at b (sm_sysex_at M + 1)).
Proof.
  intros b M Hs Hn Hm H. ev_open Hs Hn Hm.
  destruct H as [[F N]|[[F N]|[[F N]|[[F N]|[F N]]]]]; rewrite F; fold_cl.
  - replace (sm_sysex_len M - 3 =? 3) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - replace (sm_sysex_len M - 3 =? 3) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - replace (sm_sysex_len M - 3 =? 2) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - replace ((sm_sysex_len M - 3 <? 3) || (SPEC_CHARS_MAX <? sm_sysex_len M - 3 - 2)) with true;
      [reflexivity|].
    symmetry. apply orb_true_iff. unfold SPEC_CHARS_MAX. destruct N as [N|N].
    + left. apply Z.ltb_lt. lia.
    + right. apply Z.ltb_lt. lia.
  - replace (sm_sysex_len M - 3 =? 2 + SPEC_DIGITS) with false
      by (symmetry; apply Z.eqb_neq; unfold SPEC_DIGITS; lia). reflexivity.
Qed.

(* 0x13180 with an event whose cells are FR's as they stand *)
Ltac dsx_end K FR :=
  apply K; try assumption;
  cbn [fr_head owed_cells spec_msg_cells spec_event_cells arr_cells ow_m ow_e ow_lsb_missing
    ow_next ow_status_out se_kind se_strip se_button se_zone se_on se_right se_addr se_device se_len se_dots
    se_value se_mask se_delta se_segments se_text se_seg se_other app map seq nth repeat];
  rewrite ?dsysex_b8_bz; exact FR.

(* one value n of the meter's segments loop 0x13518 .. 0x13528, and its exit at 0x13530 *)
Ltac meter_it mk :=
  step; fold_cl; step; rewrite ?(unsigned_lit mk) by lia; step; rewrite dsysex_meq by lia; fold_cl;
  lazymatch goal with
  | |- context [mk =? ?v] => destruct (Z.eqb_spec mk v) as [?EQ|?NE]; cbv iota
  end.
Ltac meter_fin K FR :=
  sbstep; step; apply K; try assumption; eapply dsysex_rwc_eq; [exact FR|];
  cbn [fr_head owed_cells spec_msg_cells spec_event_cells arr_cells ow_m ow_e ow_lsb_missing
    ow_next ow_status_out se_kind se_strip se_button se_zone se_on se_right se_addr se_device se_len se_dots
    se_value se_mask se_delta se_segments se_text se_seg app map seq nth repeat];
  rewrite ?dsysex_b8_bz; reflexivity.

Theorem dsysex_holds : dsysex_stmt.
Proof.
  unfold dsysex_stmt, devent_stmt.
  intros MSC MCC r1 x3 x4 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 x22 r25 r28 r29 r30 r31 F fc m
    Sp body pos status bb j0 oj w10 rest Q OK Hpos Hst Hcode Hsys Hoj BA H25 FR MI K.
  apply Z.eqb_eq in Hsys.
  rewrite (dsysex_owed_at _ _ _ _ Hcode Hsys) in K.
  destruct (dsysex_msg (bzl bb) (Z.of_nat (length bb)) pos status ltac:(lia)) as [Hn0 Hn].
  set (M := spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) in *.
  clearbody M. clear H25.
  cbn [fr_head owed_cells owed0 spec_msg_cells spec_event_cells arr_cells se_zero ow_m ow_e ow_lsb_missing
       ow_next ow_status_out se_kind se_strip se_button se_zone se_on se_right se_addr se_device se_len se_dots
       se_value se_mask se_delta se_segments se_text se_seg app map seq nth repeat] in FR.
  pose proof (munch_refl [(Sp + 32, Sp + 152)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct OK as (H0 & H1 & H2 & H3 & H4).
  assert (HnB : sm_sysex_len M < 2 ^ 26)
    by (destruct (Z_lt_le_dec 0 (sm_sysex_len M)) as [L0|L0]; [specialize (Hn L0); lia | lia]).
  unfold dend in K.
  do 4 step.
  destruct (Z_lt_le_dec (sm_sysex_len M) 3) as [Hn3 | Hn3].
  - take true.
    rewrite (dsysex_ev_other0 _ _ Hsys (or_introl Hn3)) in K.
    apply K; assumption.
  - take false.
    destruct (Hn ltac:(lia)) as [Hs1 Hsn]. clear Hn.
    step.
    rdb (sm_sysex_at M).
    step. clear RD.
    remember (nth (Z.to_nat (sm_sysex_at M)) bb (Z_to_bv 8 0)) as b0 eqn:Eb0.
    step. step.
    rewrite (dsysex_eqb b0 19) by lia.
    destruct (Z.eqb_spec (bz b0) 19) as [Mk|Mk]; cbn [negb]; cbv iota.
    2: { rewrite (dsysex_ev_other0 _ _ Hsys) in K.
         2: { right. rewrite dsysex_byte_at, <- Eb0. exact Mk. }
         apply K; assumption. }
    rdb (sm_sysex_at M + 1).
    step. clear RD.
    remember (nth (Z.to_nat (sm_sysex_at M + 1)) bb (Z_to_bv 8 0)) as b1 eqn:Eb1.
    sbstep.
    rdb (sm_sysex_at M + 2).
    step. clear RD.
    remember (nth (Z.to_nat (sm_sysex_at M + 2)) bb (Z_to_bv 8 0)) as b2 eqn:Eb2.
    assert (Hmk : byte_at (bzl bb) (sm_sysex_at M) = 19) by (rewrite dsysex_byte_at, <- Eb0; exact Mk).
    assert (Hdv : byte_at (bzl bb) (sm_sysex_at M + 1) = bz b1) by (rewrite dsysex_byte_at, <- Eb1; reflexivity).
    assert (Hfb : byte_at (bzl bb) (sm_sysex_at M + 2) = bz b2) by (rewrite dsysex_byte_at, <- Eb2; reflexivity).
    clear Eb0 Mk.
    pose proof (dsysex_brng b2) as Rb2.
    destruct (dsysex_fn_cases (bz b2) Rb2) as [Fk|[Fk|[Fk|[Fk|[Fk|[Fk|[Fk|[Fk|Fk]]]]]]]].
    9: { do 5 step. rewrite (dsysex_idx_big b2 Fk). cbv iota.
         rewrite (dsysex_ev_fn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb; apply dsysex_fn_notin; exact Fk).
         rewrite Hdv in K. dsx_end K FR. }
    all: fn_lit b2 Fk.
    all: do 5 step; take false; do 7 step.
    (* ring, 0x13284 *)
    1: { do 2 step.
         destruct (Z.eq_dec (sm_sysex_len M) 6) as [N6|N6].
         2: { take true.
              rewrite (dsysex_ev_pn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb, Fk; lia).
              rewrite Hdv in K. dsx_end K FR. }
         take false.
         do 2 step.
         rdb (sm_sysex_at M + 3). step. clear RD.
         remember (nth (Z.to_nat (sm_sysex_at M + 3)) bb (Z_to_bv 8 0)) as p0 eqn:Ep0.
         step. sbstep.
         rdb (sm_sysex_at M + 3). step. clear RD. rewrite <- Ep0.
         do 4 step. step.
         rewrite dsysex_m0 in FR |- *.
         lazymatch type of FR with
         | rw_cells _ _ _ ?L =>
             destruct (dsysex_rwc_cut _ _ _ _ 29 FR) as [FP FR2];
             destruct (dsysex_rwc_cut _ _ _ _ 1 FR2) as [FM FQ];
             replace (Sp + Z.of_nat (cells_size (firstn 29 L))) with (Sp + 104) in FM, FQ by (cbn; lia);
             replace (Sp + 104 + Z.of_nat (cells_size (firstn 1 (skipn 29 L)))) with (Sp + 106) in FQ
               by (cbn; lia);
             cbn [firstn skipn] in FM; clear FR FR2;
             eapply dsysex_ring_loop with (bb := bb) (pre := firstn 29 L) (post := skipn 1 (skipn 29 L)) (mb := m);
             [ lia | lia | lia | lia | lia | lia | reflexivity
             | pose proof (dsysex_land_rng (Z.shiftr (bz p0) 6) 1 ltac:(lia)) as Q6;
               change (Z.ones 1) with 1 in Q6; lia
             | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | ];
             intros m1 a4' a5' mk BA1 FP1 FM1 FQ1 MU1 WM1 MI1;
             assert (FR : rw_cells rsegs m1 Sp (firstn 29 L ++ [C2 (Z_to_bv 64 mk)] ++ skipn 1 (skipn 29 L)))
         end.
         { apply dsysex_rwc_app; [exact FP1|].
           replace (Sp + Z.of_nat (cells_size (firstn 29 _))) with (Sp + 104) by (cbn; lia).
           apply dsysex_rwc_app; [exact FM1|].
           replace (Sp + 104 + Z.of_nat (cells_size [C2 (Z_to_bv 64 mk)])) with (Sp + 106) by (cbn; lia).
           exact FQ1. }
         clear FP1 FM1 FQ1.
         step.
         rewrite (dsysex_ev_ring _ _ Hsys N6 Hmk) in K by (rewrite Hfb; exact Fk).
         rewrite Hdv, !dsysex_byte_at, <- Ep0 in K.
         apply K; try assumption.
         eapply dsysex_rwc_eq; [exact FR|].
         cbn [firstn skipn app fr_head owed_cells spec_msg_cells spec_event_cells arr_cells ow_m ow_e
           ow_lsb_missing ow_next ow_status_out se_kind se_strip se_button se_zone se_on se_right se_addr se_device
           se_len se_dots se_value se_mask se_delta se_segments se_text se_seg map seq nth repeat].
         rewrite dsysex_b8_bz, dsysex_zxb_u.
         pose proof (dsysex_land_rng (bz p0) 6 ltac:(lia)) as Q63. change (Z.ones 6) with 63 in Q63.
         rewrite (unsigned_lit (Z.land (bz p0) 63)) by lia.
         reflexivity. }
    (* meter, 0x134c0 *)
    1: { do 2 step.
         destruct (Z.eq_dec (sm_sysex_len M) 6) as [N6|N6].
         2: { take true.
              rewrite (dsysex_ev_pn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb, Fk; lia).
              rewrite Hdv in K. dsx_end K FR. }
         take false.
         do 3 step.
         rdb (sm_sysex_at M + 3). step. clear RD.
         remember (nth (Z.to_nat (sm_sysex_at M + 3)) bb (Z_to_bv 8 0)) as p0 eqn:Ep0.
         step. sbstep. sbstep.
         rdb (sm_sysex_at M + 3). step. clear RD. rewrite <- Ep0.
         do 2 step. sbstep.
         rdb (sm_sysex_at M + 4). rdb (sm_sysex_at M + 5).
         step. step. clear RD RD0.
         remember (nth (Z.to_nat (sm_sysex_at M + 4)) bb (Z_to_bv 8 0)) as p1 eqn:Ep1.
         remember (nth (Z.to_nat (sm_sysex_at M + 5)) bb (Z_to_bv 8 0)) as p2 eqn:Ep2.
         do 4 step. step. do 2 step.
         rewrite dsysex_m5 in FR. rewrite dsysex_mk in FR |- *. rewrite !dsysex_zxb_u in FR.
         pose proof (dsysex_land_rng (bz p0) 5 ltac:(lia)) as L31. change (Z.ones 5) with 31 in L31.
         pose proof (dsysex_land_rng (Z.shiftr (bz p0) 5) 1 ltac:(lia)) as L1. change (Z.ones 1) with 1 in L1.
         rewrite (unsigned_lit (Z.land (bz p0) 31)), (unsigned_lit (Z.land (Z.shiftr (bz p0) 5) 1)) in FR by lia.
         rewrite (dsysex_ev_meter _ _ Hsys N6 Hmk) in K by (rewrite Hfb; exact Fk). cbv zeta in K.
         rewrite Hdv, !dsysex_byte_at, <- Ep0, <- Ep1, <- Ep2, dsysex_mk_u16 in K.
         pose proof (dsysex_mk_rng (bz p1) (bz p2)) as LM.
         remember (Z.lor (Z.shiftl (Z.land (bz p1) 127) 7) (Z.land (bz p2) 127)) as mk eqn:Emk.
         do 15 (meter_it mk;
           [ match goal with EQ : mk = _ |- _ => rewrite EQ in K, FR end; meter_fin K FR
           | step; fold_cl; step; fold_cl ]).
         step. sbstep. step.
         rewrite (dsysex_seg_none mk) in K by assumption.
         replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-1)))) with (b8 (s8 (-1))) in FR
           by (apply bv_eq; reflexivity).
         apply K; try assumption; eapply dsysex_rwc_eq; [exact FR|].
         cbn [fr_head owed_cells spec_msg_cells spec_event_cells arr_cells ow_m ow_e ow_lsb_missing
           ow_next ow_status_out se_kind se_strip se_button se_zone se_on se_right se_addr se_device se_len se_dots
           se_value se_mask se_delta se_segments se_text se_seg app map seq nth repeat].
         rewrite ?dsysex_b8_bz; reflexivity. }
    (* LEDs, 0x1348c *)
    1: { do 2 step.
         destruct (Z.eq_dec (sm_sysex_len M) 5) as [N5|N5].
         2: { take true.
              rewrite (dsysex_ev_pn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb, Fk; lia).
              rewrite Hdv in K. dsx_end K FR. }
         take false.
         do 2 step.
         rdb (sm_sysex_at M + 3). step. clear RD.
         remember (nth (Z.to_nat (sm_sysex_at M + 3)) bb (Z_to_bv 8 0)) as p0 eqn:Ep0.
         sbstep. sbstep.
         rdb (sm_sysex_at M + 4). step. clear RD.
         remember (nth (Z.to_nat (sm_sysex_at M + 4)) bb (Z_to_bv 8 0)) as p1 eqn:Ep1.
         step. step.
         rewrite (dsysex_ev_leds _ _ Hsys N5 Hmk) in K by (rewrite Hfb; exact Fk).
         rewrite Hdv, !dsysex_byte_at, <- Ep0, <- Ep1 in K.
         dsx_end K FR. }
    (* counter, 0x13538 *)
    1: { do 2 step.
         destruct (Z.eq_dec (sm_sysex_len M) 13) as [N13|N13].
         2: { take true.
              rewrite (dsysex_ev_pn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb, Fk; lia).
              rewrite Hdv in K. dsx_end K FR. }
         take false.
         do 2 step.
         rdb (sm_sysex_at M + 3). step. clear RD.
         remember (nth (Z.to_nat (sm_sysex_at M + 3)) bb (Z_to_bv 8 0)) as p0 eqn:Ep0.
         sbstep.
         rdb (sm_sysex_at M + 4). step. clear RD.
         remember (nth (Z.to_nat (sm_sysex_at M + 4)) bb (Z_to_bv 8 0)) as p1 eqn:Ep1.
         sbstep.
         do 2 step.
         step. rdb (sm_sysex_at M + 12). step. clear RD. step. sbstep. do 3 step. fold_cl.
         step. rdb (sm_sysex_at M + 11). step. clear RD. step. sbstep. do 3 step. fold_cl.
         step. rdb (sm_sysex_at M + 10). step. clear RD. step. sbstep. do 3 step. fold_cl.
         step. rdb (sm_sysex_at M + 9). step. clear RD. step. sbstep. do 3 step. fold_cl.
         step. rdb (sm_sysex_at M + 8). step. clear RD. step. sbstep. do 3 step. fold_cl.
         step. rdb (sm_sysex_at M + 7). step. clear RD. step. sbstep. do 3 step. fold_cl.
         step. rdb (sm_sysex_at M + 6). step. clear RD. step. sbstep. do 3 step. fold_cl.
         step. rdb (sm_sysex_at M + 5). step. clear RD. step. sbstep. do 3 step. fold_cl.
         step.
         rewrite (dsysex_ev_counter _ _ Hsys N13 Hmk) in K by (rewrite Hfb; exact Fk).
         rewrite Hdv, !dsysex_byte_at, <- Ep0, <- Ep1 in K.
         dsx_end K FR. }
    (* scribble, 0x13580 *)
    1: { do 2 step.
         destruct (Z_lt_le_dec (sm_sysex_len M) 6) as [N6|N6].
         1: { take true.
              rewrite (dsysex_ev_pn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb, Fk; lia).
              rewrite Hdv in K. dsx_end K FR. }
         take false.
         do 3 step.
         destruct (Z_lt_le_dec 13 (sm_sysex_len M)) as [N13|N13].
         1: { take true.
              rewrite (dsysex_ev_pn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb, Fk; lia).
              rewrite Hdv in K. dsx_end K FR. }
         take false.
         rewrite (dsysex_ev_scribble _ _ Hsys (conj N6 N13) Hmk) in K by (rewrite Hfb; exact Fk).
         rewrite Hdv, !dsysex_byte_at in K.
         do 2 step.
         rdb (sm_sysex_at M + 3). step. clear RD.
         remember (nth (Z.to_nat (sm_sysex_at M + 3)) bb (Z_to_bv 8 0)) as p0 eqn:Ep0.
         assert (C : sm_sysex_len M = 6 \/ sm_sysex_len M = 7 \/ sm_sysex_len M = 8 \/ sm_sysex_len M = 9 \/
                     sm_sysex_len M = 10 \/ sm_sysex_len M = 11 \/ sm_sysex_len M = 12 \/ sm_sysex_len M = 13)
           by lia.
         destruct C as [Nk|[Nk|[Nk|[Nk|[Nk|[Nk|[Nk|Nk]]]]]]].
         all: rewrite Nk; fold_closed_in_goal.
         all: sbstep; sbstep; do 3 step.
         all: lazymatch goal with
              | Nk : sm_sysex_len _ = ?n |- _ =>
                let l := eval vm_compute in (n - 5) in
                let ln := eval vm_compute in (Z.to_nat l) in
                lazymatch type of FR with
                | rw_cells _ _ _ ?L =>
                  destruct (dsysex_rwc_cut _ _ _ _ 32 FR) as [FP FR2];
                  destruct (dsysex_rwc_cut _ _ _ _ ln FR2) as [FT FQ];
                  replace (Sp + Z.of_nat (cells_size (firstn 32 L))) with (Sp + 109) in FT, FQ by (cbn; lia);
                  replace (Sp + 109 + Z.of_nat (cells_size (firstn ln (skipn 32 L)))) with (Sp + 109 + l) in FQ
                    by (cbn; lia);
                  apply dsysex_rwc_one in FT;
                  cbn [firstn skipn] in FP, FT, FQ; clear FR FR2;
                  eapply evt_cut;
                  [ eapply MCC with
                      (src := map (fun k => nth (Z.to_nat (sm_sysex_at M + 5 + Z.of_nat k)) bb (Z_to_bv 8 0))
                                (seq 0 ln));
                    [ rewrite unsigned_lit by lia;
                      replace (body + sm_sysex_at M + 5) with (body + (sm_sysex_at M + 5)) by lia;
                      apply dsysex_bytes_sub; [exact BA | lia | cbn; lia]
                    | rewrite unsigned_lit by lia; reflexivity
                    | rewrite !unsigned_lit by lia; exact FT
                    | rewrite !unsigned_lit by lia; lia
                    | assumption ]
                  | ]
                end
              end.
         all: intros ms' PO;
              destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
                              & Ems & MUc & WMc & MIc & RWc & BAc);
              subst ms'; rewrite !unsigned_lit in MUc, RWc by lia.
         all: lazymatch type of MUc with
              | munch _ ?m0 ?m1 => transport_after_call rsegs m0 m1 MUc WMc; clear MUc WMc;
                                   try match goal with H : mem_inv rsegs m0 |- _ => clear H end
              end.
         all: replace (ret_pc (Z_to_bv 64 79284)) with (Z_to_bv 64 79284)
                by (symmetry; apply ret_pc_even; [lia | reflexivity]).
         all: apply dsysex_rwc_c1s in RWc; cbn [map seq] in RWc.
         all: lazymatch type of FP with
              | rw_cells _ ?mm _ ?L1 =>
                lazymatch type of RWc with
                | rw_cells _ _ _ ?L2 =>
                  lazymatch type of FQ with
                  | rw_cells _ _ _ ?L3 =>
                    assert (FR : rw_cells rsegs mm Sp (L1 ++ L2 ++ L3))
                      by (apply dsysex_rwc_app; [exact FP|];
                          replace (Sp + Z.of_nat (cells_size L1)) with (Sp + 109) by (cbn; lia);
                          apply dsysex_rwc_app; [exact RWc|];
                          replace (Sp + 109 + Z.of_nat (cells_size L2)) with (Sp + 109 + Z.of_nat (length L2))
                            by (cbn; lia);
                          cbn [length]; exact FQ)
                  end
                end
              end.
         all: clear FP RWc FQ BAc; step.
         all: apply K; try assumption; eapply dsysex_rwc_eq; [exact FR|].
         all: cbn [fr_head owed_cells spec_msg_cells spec_event_cells arr_cells ow_m ow_e ow_lsb_missing
                ow_next ow_status_out se_kind se_strip se_button se_zone se_on se_right se_addr se_device se_len
                se_dots se_value se_mask se_delta se_segments se_text se_seg app map seq nth repeat zseq].
         all: rewrite Nk; fold_cl; rewrite ?dsysex_byte_at, <- ?Ep0, ?dsysex_b8_bz; reflexivity. }
    (* 0x50 and 0x60: OTHER *)
    1: { rewrite (dsysex_ev_fn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb, Fk; cbn [In]; lia).
         rewrite Hdv in K. dsx_end K FR. }
    1: { rewrite (dsysex_ev_fn_other _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb, Fk; cbn [In]; lia).
         rewrite Hdv in K. dsx_end K FR. }
    (* system, 0x134b4 *)
    1: { do 3 step.
         rewrite (dsysex_ev_sys _ _ Hsys Hn3 Hmk) in K by (rewrite Hfb; exact Fk).
         rewrite Hdv in K. dsx_end K FR. }
Qed.
