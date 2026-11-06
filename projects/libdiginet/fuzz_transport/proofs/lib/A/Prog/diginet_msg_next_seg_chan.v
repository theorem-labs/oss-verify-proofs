(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: twin of lib/AZ/LibA/StepF.v over lib.Lib. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode to libdiginet/fuzz_decode image A; module paths changed *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libdiginet/fuzz_decode/lib/Lib/StepF.v to libdiginet/fuzz_codec; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Lib/StepF.v; 416 of its 450 lines of code are new or changed and 688 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof diginet_msg_next_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c diginet_msg_next_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of mn_chan_of_fin: from 0x823b8 every path of the channel message reaches the epilogue 0x82528, where the
   hypothesis mn_fin_F gives the post state. The paths follow chan_step (DgnSpec): too few bytes (0x823e8), a data
   byte with bit 7 set (0x82444, at index d or d + 1), and all data bytes (0x82474).
   Each shadow byte the code loads lies outside the frame, the cursor and the message (mn_sh_out), the only bytes the
   run changes, so it keeps its value from the memory at 0x823b8. A 1-byte check at a loads the shadow byte k of a
   (lb), which is 0 or a mod 8 < k (addressable); when k <> 0 the code goes to the andi / blt pair, which goes back,
   so no errpath_* call is reached. The tactic mn_chk1 proves the code after the check once, for any value of the
   register the andi writes, and uses it for both paths. An 8-byte check loads the shadow byte of a granule whose
   last byte lies in the accessed object (mn_sh_gran): it is 0. *)

(* ---------- bytes and words ---------- *)

Lemma mn_rd8 : forall m A l i E, bytes_at rsegs m A l -> (i < length l)%nat -> E = A + Z.of_nat i ->
  ov_read_bytes rsegs m (Z_to_bv 64 E) 1 = Some [b8 (at8 l i)].
Proof.
  intros m A l i E BL Hi ->. change (Z_to_bv 64 (A + Z.of_nat i)) with (wa (A + Z.of_nat i)).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL) by lia. f_equal. clear BL.
  unfold at8. rewrite b8_bz.
  revert i Hi. induction l as [|x l IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma mn_at8_range : forall l i, 0 <= at8 l i < 256.
Proof. intros l i. unfold at8. apply bz_range. Qed.

Lemma mn_sxb_lts : forall x, 0 <= x < 256 -> bv_lts (sxb (b8 x)) (Z_to_bv 64 0) = (128 <=? x).
Proof.
  assert (G : forall x, 0 <= x < 2^8 -> Bool.eqb (bv_lts (sxb (b8 x)) (Z_to_bv 64 0)) (128 <=? x) = true).
  { apply (byte_forall (fun x => Bool.eqb (bv_lts (sxb (b8 x)) (Z_to_bv 64 0)) (128 <=? x))).
    vm_compute. reflexivity. }
  intros x Hx. apply Bool.eqb_prop, G. lia.
Qed.

(* 0x823cc - 0x823d8, the inlined channel_data_len: 1 + ((status & 0xe0) != 0xc0) *)
Lemma mn_snez_n : forall s, 0 <= s < 256 ->
  bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1 = Z.of_nat (chan_n s).
Proof.
  assert (G : forall s, 0 <= s < 2^8 ->
            Z.eqb (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1)
                  (Z.of_nat (chan_n s)) = true).
  { apply (byte_forall (fun s => Z.eqb (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1)
                                       (Z.of_nat (chan_n s)))).
    vm_compute. reflexivity. }
  intros s Hs. apply Z.eqb_eq, G. lia.
Qed.

(* 0x824b0: (status & 0xe0) == 0xc0 *)
Lemma mn_land_c0 : forall s, 0 <= s < 256 ->
  bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192) = (chan_n s =? 1)%nat.
Proof.
  assert (G : forall s, 0 <= s < 2^8 ->
            Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192)) (chan_n s =? 1)%nat = true).
  { apply (byte_forall (fun s => Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192)) (chan_n s =? 1)%nat)).
    vm_compute. reflexivity. }
  intros s Hs. apply Bool.eqb_prop, G. lia.
Qed.

(* the same bytes under other cells *)
Lemma mn_rw_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite <- (cells_bytes_length cs' W'), EB, (cells_bytes_length cs W). exact V.
Qed.

(* 0x824f8: end - pos *)
Lemma mn_sub_nat : forall a b : nat, (b <= a)%nat -> Z.of_nat a < 2^64 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.of_nat a)) - bv_unsigned (Z_to_bv 64 (Z.of_nat b))) =
  Z_to_bv 64 (Z.of_nat (a - b)).
Proof. intros a b H1 H2. rewrite !unsigned_lit by lia. f_equal. lia. Qed.

(* srli by 3 of an address *)
Lemma mn_srl3 : forall x, 0 <= x < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof. intros x Hx. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* ---------- shadow bytes ---------- *)

Lemma mn_signed0 : forall k : byte, bv_signed k = 0 -> k = Z_to_bv 8 0.
Proof.
  intros k H. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0.
  pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mn_sh_not_app : forall x, app_mem x -> ~ app_mem (x / 8 + 2147450880).
Proof.
  intros x H. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of an application byte lies outside the frame [S - 128, S), the cursor [c, c + 25) and the
   message [mp, mp + 40). *)
Lemma mn_sh_out : forall m S c mp x, app_mem (S - 128) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> app_mem x ->
  outside [(S - 128, S); (c, c + 25); (mp, mp + 40)] (x / 8 + 2147450880).
Proof.
  intros m S c mp x A1 A2 (P0 & N0 & PE & AB) (Q0 & M0 & QE & AM) Ax. pose proof (mn_sh_not_app x Ax) as N.
  cbn [outside]. split; [|split; [|split; [|exact I]]]; intros W; apply N.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - destruct (AB (x / 8 + 2147450880 - c) ltac:(lia)) as (Ay & _).
    replace (c + (x / 8 + 2147450880 - c)) with (x / 8 + 2147450880) in Ay by lia. exact Ay.
  - destruct (AM (x / 8 + 2147450880 - mp) ltac:(lia)) as (Ay & _).
    replace (mp + (x / 8 + 2147450880 - mp)) with (x / 8 + 2147450880) in Ay by lia. exact Ay.
Qed.

(* The shadow byte of p + i, read in a memory that differs from m only in the three ranges. *)
Lemma mn_sh_byte : forall m m' S c mp p n i, app_mem (S - 128) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> addressable m p n -> 0 <= i < n ->
  munch [(S - 128, S); (c, c + 25); (mp, mp + 40)] m m' ->
  exists k, mrd rsegs m' (wa ((p + i) / 8 + 2147450880)) = Some k /\ shadow_ok (p + i) (bv_signed k).
Proof.
  intros m m' S c mp p n i A1 A2 AC AM (P0 & N0 & PE & AB) Hi MU.
  destruct (AB i Hi) as (Ax & k & MK & SK). exists k. split; [|exact SK].
  unfold shadow_addr, ASAN_K in MK. unfold mrd in *. rewrite MU; [exact MK|].
  rewrite wa_unsigned by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ax; Z.div_mod_to_equations; lia).
  exact (mn_sh_out m S c mp _ A1 A2 AC AM Ax).
Qed.

(* The shadow byte of the granule of p + j is 0 when the 8 bytes from p + j lie in [p, p + n). *)
Lemma mn_sh_gran : forall m m' S c mp p n j, app_mem (S - 128) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> addressable m p n -> 0 <= j -> j + 8 <= n ->
  munch [(S - 128, S); (c, c + 25); (mp, mp + 40)] m m' ->
  mrd rsegs m' (wa ((p + j) / 8 + 2147450880)) = Some (Z_to_bv 8 0).
Proof.
  intros m m' S c mp p n j A1 A2 AC AM AP Hj Hn MU.
  pose proof (Z.mod_pos_bound (p + j) 8 ltac:(lia)) as Mp.
  destruct (mn_sh_byte m m' S c mp p n (j + 7 - (p + j) mod 8) A1 A2 AC AM AP ltac:(lia) MU) as (k & MK & SK).
  assert (E1 : (p + (j + 7 - (p + j) mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  assert (E2 : (p + (j + 7 - (p + j) mod 8)) / 8 = (p + j) / 8) by (Z.div_mod_to_equations; lia).
  rewrite E2 in MK. rewrite MK. f_equal. apply mn_signed0.
  unfold shadow_ok in SK. rewrite E1 in SK. lia.
Qed.

(* The shadow byte of x, x in [p, p + n), lies in the shadow range of [p, p + n). *)
Lemma mn_rng_sh : forall RNG p n x, 0 <= p ->
  rng RNG (p / 8 + 2147450880) ((p + n - 1) / 8 + 2147450880 - (p / 8 + 2147450880) + 1) ->
  p <= x < p + n -> rng RNG (x / 8 + 2147450880) 1.
Proof. intros RNG p n x Hp H Hx. eapply rng_sub'; [exact H|]. Z.div_mod_to_equations. lia. Qed.

(* ---------- tactics ---------- *)

(* a 1-byte store of a word Z_to_bv 64 z writes the byte Z_to_bv 8 z, of zxb b the byte b *)
Ltac norm_lit_store_bytes ::=
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; rewrite (Z_to_le_bytes_lit8 z)
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           is_Zlit z; rewrite (Z_to_le_bytes_lit4 z)
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           is_Zlit z; rewrite (Z_to_le_bytes_lit2 z)
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) =>
           rewrite (le1_zxb b)
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           rewrite (le1_lit_byte z)
       end).

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

Ltac nsteps n := lazymatch n with O => idtac | S ?n' => step; nsteps n' end.

Ltac norm_tset := lazymatch goal with
  | |- context [tset ?p ?x ?R] =>
      let t := eval cbv beta iota delta [tset mkR] in (tset p x R) in change (tset p x R) with t
  end.

(* At a bnez on the shadow byte k of the address E (the register r is what the andi of the check writes, nerr the
   number of instructions before its blt): prove the code after the check once, for every value of r. *)
Ltac mn_chk1 r E k SK nerr :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?N) ?fc ?rv ?mm ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
      let J := fresh "J" in
      assert (J : forall x : word, evtF segs RNG Q (MS (tset p x R) F N fc rv mm ro));
      [ let x := fresh "x" in intros x; norm_tset
      | let C := fresh "C" in let Cu := fresh "Cu" in
        destruct SK as [C|[C Cu]];
        [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]; let v := getreg r in exact (J v)
        | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
          nsteps nerr;
          rewrite land7; rewrite (unsigned_lit E) by lia;
          rewrite (lts_low (E mod 8) k ltac:(apply Z.mod_pos_bound; lia)), (proj2 (Z.ltb_lt _ _) C); cbn [negb];
          let v := getreg r in exact (J v) ] ]
  end.

(* ---------- the walk ---------- *)

Section MC.
Variables (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
  (ra gp tp t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (c mp body : Z) (bb mj : list byte) (pos : nat) (st s run : Z) (d : nat).
Hypothesis FIN : mn_fin_F.
Hypothesis Hlt : (pos < length bb)%nat.
Hypothesis HF : 128 <= bv_unsigned sp0.
Hypothesis AP1 : app_mem (bv_unsigned sp0 - 128).
Hypothesis AP2 : app_mem (bv_unsigned sp0 - 1).
Hypothesis ADc : addressable m c 25.
Hypothesis ADm : addressable m mp 40.
Hypothesis ADb : addressable m body (Z.of_nat (length bb)).
Hypothesis OSc : c + 25 <= bv_unsigned sp0 - 128 \/ bv_unsigned sp0 <= c.
Hypothesis OSm : mp + 40 <= bv_unsigned sp0 - 128 \/ bv_unsigned sp0 <= mp.
Hypothesis OSb : body + Z.of_nat (length bb) <= bv_unsigned sp0 - 128 \/ bv_unsigned sp0 <= body.
Hypothesis D1 : c + 25 <= mp \/ mp + 40 <= c.
Hypothesis D2 : c + 25 <= body \/ body + Z.of_nat (length bb) <= c.
Hypothesis D3 : mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp.
Hypothesis Bc : 0 <= c /\ c + 25 <= 0x800000000000.
Hypothesis Bm : 0 <= mp /\ mp + 40 <= 0x800000000000.
Hypothesis Bb : 0 <= body /\ body + Z.of_nat (length bb) <= 0x800000000000.
Hypothesis RFR : rng RNG (bv_unsigned sp0 - 128) 128.
Hypothesis RC : rng RNG c 25.
Hypothesis RM : rng RNG mp 40.
Hypothesis RB : rng RNG body (Z.of_nat (length bb)).
Hypothesis RSC : rng RNG (c / 8 + 2147450880) ((c + 25 - 1) / 8 + 2147450880 - (c / 8 + 2147450880) + 1).
Hypothesis RSM : rng RNG (mp / 8 + 2147450880) ((mp + 40 - 1) / 8 + 2147450880 - (mp / 8 + 2147450880) + 1).
Hypothesis RSB : rng RNG (body / 8 + 2147450880)
  ((body + Z.of_nat (length bb) - 1) / 8 + 2147450880 - (body / 8 + 2147450880) + 1).
Hypothesis Hs : 128 <= s < 240.
Hypothesis Hrun : run = 0 \/ run = 1.
Hypothesis Hd : (pos <= d <= S pos)%nat.
Hypothesis RS : msg_step bb pos st = chan_step bb pos st s run d.

Local Abbreviation W := [(bv_unsigned sp0 - 128, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)].
Local Abbreviation L := (Z.of_nat (length bb)).
Local Abbreviation Q := (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m c mp body bb mj pos st).
(* the frame words *)
Local Abbreviation FRC := [C8 (Z_to_bv 64 (mp + 3)); C8 (Z_to_bv 64 ((mp + 3) / 8 + 2147450880)); C8 (Z_to_bv 64 (c + 16));
  C8 x27; C8 x26; C8 x25; C8 x24; C8 x23; C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 ra0].
(* the cursor at 0x823b8 *)
Local Abbreviation CUR0 := [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 (Z.of_nat pos)); C1 (b8 st)].
(* the message at 0x823b8, and after m->running := run (0x823e0) *)
Local Abbreviation MC0 := [C1 (nth 0 mj (b8 0)); C1 (nth 1 mj (b8 0)); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].
Local Abbreviation MC1 := [C1 (nth 0 mj (b8 0)); C1 (Z_to_bv 8 run); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].
(* the state: t0 and a0 - a7 vary, the other registers are those of mn_chan_F *)
Local Abbreviation ST pc x5 x10 x11 x12 x13 x14 x15 x16 x17 mm :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 128)) gp tp x5 t1 t2
           (Z_to_bv 64 ((mp + 2) / 8 + 2147450880)) (Z_to_bv 64 mp) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 c) (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) (Z_to_bv 64 (body + Z.of_nat pos))
           (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 ((c + 16) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 L) (Z_to_bv 64 s) (Z_to_bv 64 body) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* 0x82528: the epilogue, by mn_fin_F *)
Lemma mn_fin_at : forall (x5 x10 x11 x12 x13 x14 x15 x16 x17 : word) (mm : word -> option byte),
  x10 = Z_to_bv 64 (mr_code (msg_step bb pos st)) ->
  munch W m mm -> rw_cells rsegs mm (bv_unsigned sp0 - 128) FRC ->
  rw_cells rsegs mm c (PCur.cursor_cells body L (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))) ->
  rw_cells rsegs mm mp (PMsg.msg_cells body mj (msg_step bb pos st)) ->
  evtF rsegs RNG Q (ST 0x8ce38 x5 x10 x11 x12 x13 x14 x15 x16 x17 mm).
Proof.
  intros x5 x10 x11 x12 x13 x14 x15 x16 x17 mm -> MU FRm CCm CMm.
  eapply FIN.
  - unfold MN_FRAME. lia.
  - unfold MN_FRAME. exact RFR.
  - unfold mn_fr, MN_FRAME. exact FRm.
  - unfold MN_FRAME. exact MU.
  - exact CCm.
  - exact CMm.
Qed.

(* 0x82444: data byte q has bit 7 set; a5 is -q. c->pos := q, c->status := 0, a0 = -6. *)
Lemma mn_cut_at : forall (q : nat) (x5 x10 x11 x12 x13 x14 x15 x16 x17 : word) (mm : word -> option byte),
  msg_step bb pos st = mr_plain MkChanCut pos q 0 run ->
  Z_to_bv 64 (0 - bv_unsigned x15) = Z_to_bv 64 (Z.of_nat q) ->
  munch W m mm -> rw_cells rsegs mm (bv_unsigned sp0 - 128) FRC ->
  rw_cells rsegs mm c CUR0 -> rw_cells rsegs mm mp MC1 ->
  evtF rsegs RNG Q (ST 0x8cd54 x5 x10 x11 x12 x13 x14 x15 x16 x17 mm).
Proof.
  intros q x5 x10 x11 x12 x13 x14 x15 x16 x17 mm RS' E15 MU FRm CCm CMm.
  (* 0x82444 lbu a0,0(s7); 0x82448 bnez a0: the shadow byte of the granule of c + 16 is 0 *)
  pose proof (mn_sh_gran _ mm (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (mn_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x8244c neg a0,a5; 0x82450 sd a0,16(s2): c->pos := q *)
  step. rewrite E15.
  step.
  (* 0x82454 addi a0,s2,24; 0x82458 srli; 0x8245c add; 0x82460 lb: the shadow byte of c + 24 *)
  step. step. step. rewrite (mn_srl3 (c + 24)) by lia.
  destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp c 25 24 AP1 AP2 ADc ADm ADc ltac:(lia) MU) as (k & MK & SK).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG c 25 (c + 24) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x82464 bnez a1; 0x825f0 andi a2,a0,7; 0x825f4 blt a2,a1 *)
  step. mn_chk1 12 (c + 24) k SK 2%nat.
  (* 0x82468 sb zero,0(a0): c->status := 0; 0x8246c li a0,-6; 0x82470 j *)
  step. step. step.
  eapply mn_fin_at.
  - rewrite RS'. reflexivity.
  - exact MU.
  - exact FRm.
  - rewrite RS'. exact CCm.
  - rewrite RS'. exact CMm.
Qed.

(* 0x82474: the n = chan_n s data bytes from d are data bytes. m->status := s, d1, d2, m->len := end - pos,
   c->pos := end, c->status := s, a0 = 1. *)
Lemma mn_data_at : forall (x5 x10 x11 x12 x13 x14 x15 x16 x17 : word) (mm : word -> option byte),
  x11 = Z_to_bv 64 (Z.of_nat (d + chan_n s)) -> x12 = Z_to_bv 64 (Z.of_nat d) -> x13 = Z_to_bv 64 (Z.land s 224) ->
  (d + chan_n s <= length bb)%nat -> at8 bb d < 128 -> (chan_n s = 2%nat -> at8 bb (S d) < 128) ->
  munch W m mm -> rw_cells rsegs mm (bv_unsigned sp0 - 128) FRC ->
  rw_cells rsegs mm c CUR0 -> rw_cells rsegs mm mp MC1 -> bytes_at rsegs mm body bb ->
  evtF rsegs RNG Q (ST 0x8cd84 x5 x10 x11 x12 x13 x14 x15 x16 x17 mm).
Proof.
  intros x5 x10 x11 x12 x13 x14 x15 x16 x17 mm -> -> -> Hn B1 B2 MU FRm CCm CMm BBm.
  pose proof (chan_n_cases s) as HN.
  pose proof (mn_at8_range bb d) as X1. pose proof (mn_at8_range bb (S d)) as X2.
  assert (RS' : msg_step bb pos st = MsgRes MkChan pos (d + chan_n s) s s run (at8 bb d)
                  (if (chan_n s =? 2)%nat then at8 bb (S d) else 0) 0 0 (d + chan_n s - pos)).
  { rewrite RS. unfold chan_step.
    replace (length bb <? d + chan_n s)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (0x80 <=? at8 bb d) with false by (symmetry; apply Z.leb_gt; lia).
    destruct HN as [N|N]; rewrite N; cbn [Nat.eqb andb]; [reflexivity|].
    replace (0x80 <=? at8 bb (S d)) with false by (symmetry; apply Z.leb_gt; specialize (B2 N); lia).
    reflexivity. }
  (* 0x82474 srli; 0x82478 add; 0x8247c lb: the shadow byte of mp *)
  step. step. rewrite (mn_srl3 mp) by lia.
  destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp mp 40 0 AP1 AP2 ADc ADm ADm ltac:(lia) MU) as (k0 & MK & SK0).
  rewrite Z.add_0_r in MK, SK0.
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG mp 40 mp ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x82480 bnez a0; 0x825fc andi a4,s1,7; 0x82600 blt a4,a0 *)
  step. mn_chk1 14 mp k0 SK0 2%nat.
  (* 0x82484 sb s10,0(s1): m->status := s *)
  step.
  (* 0x82488 add a0,a2,s11; 0x8248c srli; 0x82490 add; 0x82494 lb: the shadow byte of body + d *)
  step. step. step. rewrite (mn_srl3 (Z.of_nat d + body)) by lia.
  destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp body L (Z.of_nat d) AP1 AP2 ADc ADm ADb ltac:(lia) MU)
    as (k1 & MK & SK1).
  rewrite (Z.add_comm body (Z.of_nat d)) in MK, SK1.
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG body L (Z.of_nat d + body) ltac:(lia) RSB ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x82498 bnez a2; 0x8260c andi a4,a0,7; 0x82610 blt a4,a2 *)
  step. mn_chk1 14 (Z.of_nat d + body) k1 SK1 2%nat.
  (* 0x8249c lb a4,0(s0): the shadow byte of mp + 2 *)
  destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp mp 40 2 AP1 AP2 ADc ADm ADm ltac:(lia) MU) as (k2 & MK & SK2).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG mp 40 (mp + 2) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x824a0 lbu a2,0(a0): d1 = body[d] *)
  pose proof (mn_rd8 _ body bb d (Z.of_nat d + body) BBm ltac:(lia) ltac:(lia)) as HR.
  pose proof (rng_sub' RNG body L (Z.of_nat d + body) 1 RB ltac:(lia)) as RH.
  step. clear HR RH.
  (* 0x824a4 bnez a4; 0x82618 andi a5,s4,7; 0x8261c blt a5,a4 *)
  step. mn_chk1 15 (mp + 2) k2 SK2 2%nat.
  (* 0x824a8 li a4,192; 0x824ac sb a2,0(s4): m->d1 := body[d] *)
  step. step.
  (* 0x824b0 bne a3,a4: n = 1 iff (s & 0xe0) = 0xc0 *)
  step. rewrite mn_land_c0 by lia.
  destruct HN as [N|N]; rewrite N; cbn [negb Nat.eqb].
  (* n = 1: 0x824b4 li a0,0; 0x824b8 j: d2 = 0 *)
  1: step; step.
  (* n = 2: 0x824bc addi a0,a0,1; 0x824c0 srli; 0x824c4 add; 0x824c8 lb: the shadow byte of body + d + 1 *)
  2: step; step; step; rewrite (mn_srl3 (Z.of_nat d + body + 1)) by lia.
  2: destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp body L (Z.of_nat d + 1) AP1 AP2 ADc ADm ADb ltac:(lia) MU)
       as (k3 & MK & SK3).
  2: replace (body + (Z.of_nat d + 1)) with (Z.of_nat d + body + 1) in MK, SK3 by lia.
  2: pose proof (rd1 _ _ _ MK) as HR.
  2: pose proof (mn_rng_sh RNG body L (Z.of_nat d + body + 1) ltac:(lia) RSB ltac:(lia)) as RH.
  2: step; clear HR RH MK.
  (* 0x824cc bnez a2; 0x82648 andi a3,a0,7; 0x8264c blt a3,a2 *)
  2: step; mn_chk1 13 (Z.of_nat d + body + 1) k3 SK3 2%nat.
  (* 0x824d0 lbu a0,0(a0): d2 = body[d + 1] *)
  2: pose proof (mn_rd8 _ body bb (S d) (Z.of_nat d + body + 1) BBm ltac:(lia) ltac:(lia)) as HR.
  2: pose proof (rng_sub' RNG body L (Z.of_nat d + body + 1) 1 RB ltac:(lia)) as RH.
  2: step; clear HR RH.
  (* 0x824d4 ld a2,8(sp); 0x824d8 lb a2,0(a2): the shadow byte of mp + 3 *)
  all: step.
  all: destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp mp 40 3 AP1 AP2 ADc ADm ADm ltac:(lia) MU) as (k4 & MK & SK4).
  all: pose proof (rd1 _ _ _ MK) as HR.
  all: pose proof (mn_rng_sh RNG mp 40 (mp + 3) ltac:(lia) RSM ltac:(lia)) as RH.
  all: step; clear HR RH MK.
  (* 0x824dc bnez a2; 0x82628 ld a3,0(sp); 0x8262c andi a3,a3,7; 0x82630 blt a3,a2 *)
  all: step; mn_chk1 13 (mp + 3) k4 SK4 3%nat.
  (* 0x824e0 sb a0,3(s1): m->d2 *)
  all: step.
  (* 0x824e4 addi a0,s1,32; 0x824e8 srli; 0x824ec add; 0x824f0 lbu; 0x824f4 bnez: the shadow byte of the granule
     of mp + 32 is 0 *)
  all: step; step; step; rewrite (mn_srl3 (mp + 32)) by lia.
  all: pose proof (mn_sh_gran _ _ (bv_unsigned sp0) c mp mp 40 32 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU) as G.
  all: pose proof (rd1 _ _ _ G) as HR.
  all: pose proof (mn_rng_sh RNG mp 40 (mp + 32) ltac:(lia) RSM ltac:(lia)) as RH.
  all: step; clear HR RH G.
  all: step; if_false.
  (* 0x824f8 sub a2,a1,s3; 0x824fc sd a2,0(a0): m->len := end - pos *)
  all: step; step.
  (* 0x82500 lbu a0,0(s7); 0x82504 bnez a0: the shadow byte of the granule of c + 16 is 0 *)
  all: pose proof (mn_sh_gran _ _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU) as G.
  all: pose proof (rd1 _ _ _ G) as HR.
  all: pose proof (mn_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
  all: step; clear HR RH G.
  all: step; if_false.
  (* 0x82508 sd a1,16(s2): c->pos := end *)
  all: step.
  (* 0x8250c addi a0,s2,24; 0x82510 srli; 0x82514 add; 0x82518 lb: the shadow byte of c + 24 *)
  all: step; step; step; rewrite (mn_srl3 (c + 24)) by lia.
  all: destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp c 25 24 AP1 AP2 ADc ADm ADc ltac:(lia) MU) as (k5 & MK & SK5).
  all: pose proof (rd1 _ _ _ MK) as HR.
  all: pose proof (mn_rng_sh RNG c 25 (c + 24) ltac:(lia) RSC ltac:(lia)) as RH.
  all: step; clear HR RH MK.
  (* 0x8251c bnez a1; 0x8263c andi a2,a0,7; 0x82640 blt a2,a1 *)
  all: step; mn_chk1 12 (c + 24) k5 SK5 2%nat.
  (* 0x82520 sb s10,0(a0): c->status := s; 0x82524 li a0,1 *)
  all: step; step.
  all: eapply mn_fin_at;
       [ rewrite RS'; reflexivity
       | exact MU
       | exact FRm
       | rewrite RS', N; exact CCm
       | rewrite mn_sub_nat in CMm by lia; rewrite RS', N; exact CMm ].
Qed.

(* 0x823b8 *)
Lemma mn_main : forall (t0 a0 a1 a3 a4 a6 a7 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 128) FRC -> rw_cells rsegs m c CUR0 -> rw_cells rsegs m mp MC0 ->
  bytes_at rsegs m body bb ->
  evtF rsegs RNG Q (ST 0x8ccc8 t0 a0 a1 (Z_to_bv 64 (Z.of_nat d)) a3 a4 (Z_to_bv 64 run) a6 a7 m).
Proof.
  intros t0 a0 a1 a3 a4 a6 a7 FRm CCm CMm BBm.
  pose proof (munch_refl W m) as MU.
  pose proof (chan_n_cases s) as HN.
  (* 0x823b8 addi a0,s1,1; 0x823bc srli; 0x823c0 add; 0x823c4 lb: the shadow byte of mp + 1 *)
  step. step. step. rewrite (mn_srl3 (mp + 1)) by lia.
  destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp mp 40 1 AP1 AP2 ADc ADm ADm ltac:(lia) MU) as (k & MK & SK).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG mp 40 (mp + 1) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x823c8 bnez a1; 0x8259c andi a3,a0,7; 0x825a0 blt a3,a1 *)
  step. mn_chk1 13 (mp + 1) k SK 2%nat.
  (* 0x823cc andi a3,s10,224; 0x823d0 addi a1,a3,-192; 0x823d4 snez a4,a1; 0x823d8 addi a4,a4,1: a4 = n *)
  step. rewrite (unsigned_lit s) by lia.
  step. step. step. rewrite mn_snez_n by lia.
  (* 0x823dc add a1,a4,a2: a1 = d + n *)
  step.
  (* 0x823e0 sb a5,0(a0): m->running := run *)
  step.
  (* 0x823e4 bgeu s9,a1: len >= d + n *)
  step.
  destruct (Nat.ltb_spec (length bb) (d + chan_n s)) as [SH|SH].
  { (* too few bytes: 0x823e8 lbu a0,0(s7); 0x823ec bnez a0: the shadow byte of the granule of c + 16 is 0 *)
    br false.
    assert (RS' : msg_step bb pos st = mr_plain MkChanShort pos (length bb) st run).
    { rewrite RS. unfold chan_step.
      replace (length bb <? d + chan_n s)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    pose proof (mn_sh_gran _ _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU) as G.
    pose proof (rd1 _ _ _ G) as HR.
    pose proof (mn_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
    step. clear HR RH G.
    step. if_false.
    (* 0x823f0 ld a0,16(sp); 0x823f4 sd s9,0(a0): c->pos := len; 0x823f8 j; 0x8246c li a0,-6; 0x82470 j *)
    step. step. step. step. step.
    eapply mn_fin_at;
      [ rewrite RS'; reflexivity | exact MU | exact FRm | rewrite RS'; exact CCm | rewrite RS'; exact CMm ]. }
  br true.
  (* 0x823fc add a6,a2,s11; 0x82400 neg a5,a2; 0x82404 mv a0,a6 *)
  step. step. step.
  destruct HN as [N|N]; rewrite N; [change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2].
  (* the data byte d: 0x82408 srli; 0x8240c add; 0x82410 lb: its shadow byte *)
  all: step; step; rewrite (mn_srl3 (Z.of_nat d + body)) by lia.
  all: destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp body L (Z.of_nat d) AP1 AP2 ADc ADm ADb ltac:(lia) MU)
         as (k1 & MK & SK1).
  all: rewrite (Z.add_comm body (Z.of_nat d)) in MK, SK1.
  all: pose proof (rd1 _ _ _ MK) as HR.
  all: pose proof (mn_rng_sh RNG body L (Z.of_nat d + body) ltac:(lia) RSB ltac:(lia)) as RH.
  all: step; clear HR RH MK.
  (* 0x82414 bnez a7; 0x82438 andi t0,a0,7; 0x8243c blt t0,a7 *)
  all: step; mn_chk1 5 (Z.of_nat d + body) k1 SK1 2%nat.
  (* 0x82418 lb a7,0(a6): body[d]; 0x8241c bltz a7 *)
  all: pose proof (mn_rd8 _ body bb d (Z.of_nat d + body) BBm ltac:(lia) ltac:(lia)) as HR.
  all: pose proof (rng_sub' RNG body L (Z.of_nat d + body) 1 RB ltac:(lia)) as RH.
  all: pose proof (mn_at8_range bb d) as X1.
  all: step; clear HR RH.
  all: step; rewrite mn_sxb_lts by lia.
  all: destruct (Z.leb_spec 128 (at8 bb d)) as [C1d|C1d]; cbv iota;
       [ (* bit 7 set: 0x82444 with a5 = -d *)
         eapply (mn_cut_at d);
         [ rewrite RS; unfold chan_step;
           replace (length bb <? d + chan_n s)%nat with false by (symmetry; apply Nat.ltb_ge; lia);
           replace (0x80 <=? at8 bb d) with true by (symmetry; apply Z.leb_le; lia); reflexivity
         | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia
         | exact MU | exact FRm | exact CCm | exact CMm ]
       | ].
  (* 0x82420 addi a4,a4,-1; 0x82424 addi a5,a5,-1; 0x82428 addi a0,a0,1; 0x8242c addi a6,a6,1; 0x82430 bnez a4 *)
  all: step; step; step; step; step.
  (* n = 1: 0x82434 j 0x82474 *)
  1: if_false.
  1: step; eapply mn_data_at;
       [ rewrite N; f_equal; lia | reflexivity | reflexivity | lia | lia | intros; lia
       | exact MU | exact FRm | exact CCm | exact CMm | exact BBm ].
  (* n = 2: the data byte d + 1 *)
  if_true.
  step. step. rewrite (mn_srl3 (Z.of_nat d + body + 1)) by lia.
  destruct (mn_sh_byte _ _ (bv_unsigned sp0) c mp body L (Z.of_nat d + 1) AP1 AP2 ADc ADm ADb ltac:(lia) MU)
    as (k2 & MK & SK2).
  replace (body + (Z.of_nat d + 1)) with (Z.of_nat d + body + 1) in MK, SK2 by lia.
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG body L (Z.of_nat d + body + 1) ltac:(lia) RSB ltac:(lia)) as RH.
  step. clear HR RH MK.
  step. mn_chk1 5 (Z.of_nat d + body + 1) k2 SK2 2%nat.
  pose proof (mn_rd8 _ body bb (S d) (Z.of_nat d + body + 1) BBm ltac:(lia) ltac:(lia)) as HR.
  pose proof (rng_sub' RNG body L (Z.of_nat d + body + 1) 1 RB ltac:(lia)) as RH.
  pose proof (mn_at8_range bb (S d)) as X2.
  step. clear HR RH.
  step. rewrite mn_sxb_lts by lia.
  destruct (Z.leb_spec 128 (at8 bb (S d))) as [C2d|C2d]; cbv iota.
  { (* bit 7 set: 0x82444 with a5 = -(d + 1) *)
    eapply (mn_cut_at (S d)).
    - rewrite RS. unfold chan_step. rewrite N.
      replace (length bb <? d + 2)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (0x80 <=? at8 bb d) with false by (symmetry; apply Z.leb_gt; lia).
      replace (0x80 <=? at8 bb (S d)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - apply Z_to_bv_eqm. rewrite ?unsigned_lit_wrap. Z.div_mod_to_equations. lia.
    - exact MU.
    - exact FRm.
    - exact CCm.
    - exact CMm. }
  step. step. step. step. step.
  if_false.
  step. eapply mn_data_at;
    [ rewrite N; f_equal; lia | reflexivity | reflexivity | lia | lia | intros; lia
    | exact MU | exact FRm | exact CCm | exact CMm | exact BBm ].
Qed.

End MC.

Theorem mn_chan_of_fin : mn_fin_F -> mn_chan_F.
Proof.
  intros FIN. unfold mn_chan_F.
  intros RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra gp tp t0 t1 t2 a0 a1 a3 a4 a6 a7 t3 t4 t5 t6
    F fc m c mp body bb mj pos st s run d CTX Hs Hrun Hd RS.
  destruct CTX as (Hlt & Hst & Hmj & HF & AP1 & AP2 & FR & CC & CM & BB & ADc & ADm & ADb & OSc & OSm & OSb &
                   D1 & D2 & D3 & RFR & RC & RM & RB & RSC & RSM & RSB).
  unfold MN_FRAME, mn_fr, mn_msg0, PCur.cursor_cells, off_stk, shadow_addr, ASAN_K in *.
  assert (Bc : 0 <= c /\ c + 25 <= 0x800000000000) by (destruct ADc as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  assert (Bm : 0 <= mp /\ mp + 40 <= 0x800000000000) by (destruct ADm as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  assert (Bb : 0 <= body /\ body + Z.of_nat (length bb) <= 0x800000000000)
    by (destruct ADb as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  eapply mn_main; eassumption.
Qed.
