(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: twin of lib/AZ/LibA/StepF.v over lib.Lib. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode to libdiginet/fuzz_decode image A; module paths changed *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libdiginet/fuzz_decode/lib/Lib/StepF.v to libdiginet/fuzz_codec; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Lib/StepF.v; 410 of its 445 lines of code are new or changed and 687 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of diginet_msg_next in fuzz_frame.ubsan (0x141a0) proves its contract, and no UBSan check branch is taken. *)
(* Modified by Theorem Labs, 2026-10: the footprint walk of diginet_cursor_init in libdiginet/fuzz_frame's image A (fuzz_frame.asan), after proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_counter_F.v (StepF's step, the frame carve, the asan shadow loads), with the four stores to the caller's cursor. *)
(* Modified by Theorem Labs, 2026-10: proof of diginet_mac_is_digidesign_contract_F (fuzz_frame.asan, image A) in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_nosh.v, for three bytes and the result DgnSpec.oui_of. *)
(* Modified by Theorem Labs, 2026-10: the channel piece mn_chan_F of the image-A walk of diginet_msg_next (fuzz_frame.asan, 0x835a0 to the epilogue 0x83710); rd8, at8_range, sxb_lts, snez_n, land_c0 and rw_conv taken from the UBSan walk; cinit_signed0, the shadow-outside and granule lemmas of the cursor walk generalized to the frame, the cursor and the message; the 1-byte check of the mac walk made a tactic that joins its two paths. *)
(* Modified by Theorem Labs, 2026-10: the channel piece mn_chan_F of the image-B walk of diginet_msg_next (fuzz_frame.asan-ubsan, 0x836d0 to the epilogue 0x83828): the 64-byte frame, the shadow bytes read from the entry memory through the munch fact of mn_ctx, the data-byte loop of 0x83700 - 0x83728 unrolled for one and two bytes, the UBSan checks 0x83700 / 0x83780 / 0x837bc shown not taken by not_val of the UBSan walk, and the checks of the granules of m, m + 2, m + 3 shown to fall through. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof diginet_msg_next_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c diginet_msg_next_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of mn_chan_of_fin: from 0x82640 every path of the channel message reaches the epilogue 0x82798, where the
   hypothesis mn_fin_F gives the post state. The paths follow chan_step (the libdiginet model): too few bytes (0x82658), a data
   byte with bit 7 set (0x826b0, at index d or d + 1), and all data bytes (0x826dc).
   Each shadow byte the code loads lies outside the frame, the cursor and the message (mn_sh_out), the only bytes the
   run changes, so it keeps its value from the entry memory m0 (the munch fact of mn_ctx). A 1-byte check at a loads
   the shadow byte k of a (lb), which is 0 or a mod 8 < k (addressable at m0); when k <> 0 the code goes to the andi /
   blt pair, which goes back to the access, so no errpath_* call is reached. The tactic mn_chk1 proves the code after
   the check once, for any value of the register the andi writes, and uses it for both paths. The checks of m, m + 2
   and m + 3 (and the 8-byte checks of c + 16 and m + 32) load the shadow byte of a granule whose last byte lies in the
   accessed object (mn_sh_gran): it is 0, and the check falls through.
   The UBSan checks 0x82670 `bltu t5,s4`, 0x826f0 `bltu t5,a7` and 0x8272c `bltu t5,a4` compare t5 = not body
   = 2^64 - 1 - body with an index below length bb: body + length bb <= APPMEM_END, so each is not taken. *)

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

(* 0x82640 - 0x8264c, the inlined channel_data_len: 1 + ((status & 0xe0) != 0xc0) *)
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

(* 0x8271c: (status & 0xe0) == 0xc0 *)
Lemma mn_land_c0 : forall s, 0 <= s < 256 ->
  bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192) = (chan_n s =? 1)%nat.
Proof.
  assert (G : forall s, 0 <= s < 2^8 ->
            Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192)) (chan_n s =? 1)%nat = true).
  { apply (byte_forall (fun s => Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192)) (chan_n s =? 1)%nat)).
    vm_compute. reflexivity. }
  intros s Hs. apply Bool.eqb_prop, G. lia.
Qed.

(* 0x82668 not t5,t4: the bound of the UBSan checks *)
Lemma mn_not_val : forall x w, 0 <= x < 2^64 -> w = 18446744073709551615 ->
  Z.lxor (bv_unsigned (Z_to_bv 64 x)) w = 2^64 - 1 - x.
Proof. intros x w Hx ->. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. lia. Qed.

(* 0x82768: end - pos *)
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

(* The shadow byte of an application byte lies outside the frame [S - 64, S), the cursor [c, c + 25) and the
   message [mp, mp + 40). *)
Lemma mn_sh_out : forall m S c mp x, app_mem (S - 64) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> app_mem x ->
  outside [(S - 64, S); (c, c + 25); (mp, mp + 40)] (x / 8 + 2147450880).
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
Lemma mn_sh_byte : forall m m' S c mp p n i, app_mem (S - 64) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> addressable m p n -> 0 <= i < n ->
  munch [(S - 64, S); (c, c + 25); (mp, mp + 40)] m m' ->
  exists k, mrd rsegs m' (wa ((p + i) / 8 + 2147450880)) = Some k /\ shadow_ok (p + i) (bv_signed k).
Proof.
  intros m m' S c mp p n i A1 A2 AC AM (P0 & N0 & PE & AB) Hi MU.
  destruct (AB i Hi) as (Ax & k & MK & SK). exists k. split; [|exact SK].
  unfold shadow_addr, ASAN_K in MK. unfold mrd in *. rewrite MU; [exact MK|].
  rewrite wa_unsigned by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ax; Z.div_mod_to_equations; lia).
  exact (mn_sh_out m S c mp _ A1 A2 AC AM Ax).
Qed.

(* The shadow byte of the granule of p + j is 0 when the 8 bytes from p + j lie in [p, p + n). *)
Lemma mn_sh_gran : forall m m' S c mp p n j, app_mem (S - 64) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> addressable m p n -> 0 <= j -> j + 8 <= n ->
  munch [(S - 64, S); (c, c + 25); (mp, mp + 40)] m m' ->
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
(* a branch on a closed condition *)
Ltac brc v := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v by (vm_compute; reflexivity); cbv iota
  end.
(* two words Z_to_bv 64 e1, Z_to_bv 64 e2 with e1 = e2 mod 2^64 *)
Ltac weq := first [ reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

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
  (ra gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (c mp body : Z) (bb mj : list byte) (pos : nat) (st s run : Z) (d : nat).
Hypothesis FIN : mn_fin_F.
Hypothesis Hlt : (pos < length bb)%nat.
Hypothesis HF : 64 <= bv_unsigned sp0.
Hypothesis AP1 : app_mem (bv_unsigned sp0 - 64).
Hypothesis AP2 : app_mem (bv_unsigned sp0 - 1).
Hypothesis ADc : addressable m0 c 25.
Hypothesis ADm : addressable m0 mp 40.
Hypothesis ADb : addressable m0 body (Z.of_nat (length bb)).
Hypothesis OSc : c + 25 <= bv_unsigned sp0 - 64 \/ bv_unsigned sp0 <= c.
Hypothesis OSm : mp + 40 <= bv_unsigned sp0 - 64 \/ bv_unsigned sp0 <= mp.
Hypothesis OSb : body + Z.of_nat (length bb) <= bv_unsigned sp0 - 64 \/ bv_unsigned sp0 <= body.
Hypothesis D1 : c + 25 <= mp \/ mp + 40 <= c.
Hypothesis D2 : c + 25 <= body \/ body + Z.of_nat (length bb) <= c.
Hypothesis D3 : mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp.
Hypothesis Bc : 0 <= c /\ c + 25 <= 0x800000000000.
Hypothesis Bm : 0 <= mp /\ mp + 40 <= 0x800000000000.
Hypothesis Bb : 0 <= body /\ body + Z.of_nat (length bb) <= 0x800000000000.
Hypothesis RFR : rng RNG (bv_unsigned sp0 - 64) 64.
Hypothesis RC : rng RNG c 25.
Hypothesis RM : rng RNG mp 40.
Hypothesis RB : rng RNG body (Z.of_nat (length bb)).
Hypothesis RSC : rng RNG (c / 8 + 2147450880) ((c + 25 - 1) / 8 + 2147450880 - (c / 8 + 2147450880) + 1).
Hypothesis RSM : rng RNG (mp / 8 + 2147450880) ((mp + 40 - 1) / 8 + 2147450880 - (mp / 8 + 2147450880) + 1).
Hypothesis RSB : rng RNG (body / 8 + 2147450880)
  ((body + Z.of_nat (length bb) - 1) / 8 + 2147450880 - (body / 8 + 2147450880) + 1).
Hypothesis Hs : 128 <= s < 240.
Hypothesis Hd : (pos <= d <= S pos)%nat.
Hypothesis RS : msg_step bb pos st = chan_step bb pos st s run d.

Local Abbreviation W := [(bv_unsigned sp0 - 64, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)].
Local Abbreviation L := (Z.of_nat (length bb)).
Local Abbreviation Q := (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st).
(* the frame words *)
Local Abbreviation FRC := [C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 ra0].
(* the cursor at 0x82640 *)
Local Abbreviation CUR0 := [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 (Z.of_nat pos)); C1 (b8 st)].
(* the message at 0x82640: m + 1 = run already stored *)
Local Abbreviation MC1 := [C1 (nth 0 mj (b8 0)); C1 (b8 run); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].
(* the state: a0 - a7, s2 - s6, t5 and t6 vary, the other registers are those of mn_chan_F *)
Local Abbreviation ST pc r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r30 r31 mm :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 64)) gp tp
           (Z_to_bv 64 ((c + 16) / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.of_nat pos))
           (Z_to_bv 64 ((mp + 3) / 8 + 2147450880)) (Z_to_bv 64 ((mp + 2) / 8 + 2147450880))
           r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 x23 x24 x25 x26 x27
           (Z_to_bv 64 s) (Z_to_bv 64 body) r30 r31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* 0x82798: the epilogue, by mn_fin_F *)
Lemma mn_fin_at : forall (r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r28 r29 r30 r31 : word)
    (mm : word -> option byte),
  r13 = Z_to_bv 64 (mr_code (msg_step bb pos st)) ->
  munch W m0 mm -> rw_cells rsegs mm (bv_unsigned sp0 - 64) FRC ->
  rw_cells rsegs mm c (PCur.cursor_cells body L (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))) ->
  rw_cells rsegs mm mp (PMsg.msg_cells body mj (msg_step bb pos st)) ->
  evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 64)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
             r18 r19 r20 r21 r22 x23 x24 x25 x26 x27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x8ca7c) fc None mm (seg_rom rsegs)).
Proof.
  intros r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r28 r29 r30 r31 mm -> MU FRm CCm CMm.
  pose proof FIN as FN. unfold mn_fin_F, MN_FRAME, MN_FIN, mn_fr in FN.
  eapply FN.
  - lia.
  - exact RFR.
  - exact FRm.
  - exact MU.
  - exact CCm.
  - exact CMm.
Qed.

(* 0x826b0: data byte q has bit 7 set; s4 = q. c->pos := q, c->status := 0, a3 = -6. *)
Lemma mn_cut_at : forall (q : nat) (r10 r11 r13 r14 r15 r16 r17 r18 r19 r21 r22 r30 r31 : word)
    (mm : word -> option byte),
  msg_step bb pos st = mr_plain MkChanCut pos q 0 run ->
  munch W m0 mm -> rw_cells rsegs mm (bv_unsigned sp0 - 64) FRC ->
  rw_cells rsegs mm c CUR0 -> rw_cells rsegs mm mp MC1 ->
  evtF rsegs RNG Q (ST 0x8c994 r10 r11 (Z_to_bv 64 c) r13 r14 r15 r16 r17 r18 r19 (Z_to_bv 64 (Z.of_nat q))
                       r21 r22 r30 r31 mm).
Proof.
  intros q r10 r11 r13 r14 r15 r16 r17 r18 r19 r21 r22 r30 r31 mm RS' MU FRm CCm CMm.
  (* 0x826b0 lbu a1,0(t0); 0x826b4 bnez a1: the shadow byte of the granule of c + 16 is 0 *)
  pose proof (mn_sh_gran m0 _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (mn_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH G.
  step. brc false.
  (* 0x826b8 sd s4,16(a2): c->pos := q *)
  step.
  (* 0x826bc addi a0,a2,24; 0x826c0 srli a1,a0,3; 0x826c4 add a1,a1,t1; 0x826c8 lb: the shadow byte of c + 24 *)
  step. step. step. rewrite (mn_srl3 (c + 24)) by lia.
  destruct (mn_sh_byte m0 _ (bv_unsigned sp0) c mp c 25 24 AP1 AP2 ADc ADm ADc ltac:(lia) MU) as (k & MK & SK).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG c 25 (c + 24) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x826cc bnez a1; 0x82870 andi a2,a0,7; 0x82874 blt a2,a1 *)
  step. mn_chk1 12 (c + 24) k SK 2%nat.
  (* 0x826d0 sb zero,0(a0): c->status := 0; 0x826d4 li a3,-6; 0x826d8 j 0x82798 *)
  step. step. step.
  eapply mn_fin_at.
  - rewrite RS'. reflexivity.
  - exact MU.
  - exact FRm.
  - rewrite RS'. exact CCm.
  - rewrite RS'. exact CMm.
Qed.

(* 0x826dc: the n = chan_n s data bytes from d are data bytes. m->status := s, d1, d2, m->len := end - pos,
   c->pos := end, c->status := s, a3 = 1. *)
Lemma mn_data_at : forall (r10 r13 r14 r16 r17 r18 r19 r20 r21 r22 r30 r31 : word) (mm : word -> option byte),
  r16 = Z_to_bv 64 (Z.of_nat (d + chan_n s)) -> r17 = Z_to_bv 64 (Z.of_nat d) -> r18 = Z_to_bv 64 (Z.land s 224) ->
  r30 = Z_to_bv 64 (2^64 - 1 - body) ->
  (d + chan_n s <= length bb)%nat -> at8 bb d < 128 -> (chan_n s = 2%nat -> at8 bb (S d) < 128) ->
  munch W m0 mm -> rw_cells rsegs mm (bv_unsigned sp0 - 64) FRC ->
  rw_cells rsegs mm c CUR0 -> rw_cells rsegs mm mp MC1 -> bytes_at rsegs mm body bb ->
  evtF rsegs RNG Q (ST 0x8c9c0 r10 (Z_to_bv 64 mp) (Z_to_bv 64 c) r13 r14 (Z_to_bv 64 (mp + 2)) r16 r17 r18 r19
                       r20 r21 r22 r30 r31 mm).
Proof.
  intros r10 r13 r14 r16 r17 r18 r19 r20 r21 r22 r30 r31 mm -> -> -> -> Hn B1 B2 MU FRm CCm CMm BBm.
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
  (* 0x826dc srli a4,a1,3; 0x826e0 add a4,a4,t1; 0x826e4 lb a4,0(a4): the shadow byte of the granule of mp is 0 *)
  step. step. rewrite (mn_srl3 mp) by lia.
  pose proof (mn_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 0 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU) as G.
  rewrite Z.add_0_r in G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (mn_rng_sh RNG mp 40 mp ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  (* 0x826e8 bnez a4: falls through *)
  step. brc false.
  (* 0x826ec sb t3,0(a1): m->status := s *)
  step.
  (* 0x826f0 bltu t5,a7: the UBSan check, not taken *)
  step. br false.
  (* 0x826f4 add a4,t4,a7; 0x826f8 srli t6,a4,3; 0x826fc add t6,t6,t1; 0x82700 lb: the shadow byte of body + d *)
  step. step. step. rewrite (mn_srl3 (body + Z.of_nat d)) by lia.
  destruct (mn_sh_byte m0 _ (bv_unsigned sp0) c mp body L (Z.of_nat d) AP1 AP2 ADc ADm ADb ltac:(lia) MU)
    as (k1 & MK & SK1).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG body L (body + Z.of_nat d) ltac:(lia) RSB ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x82704 bnez t6; 0x82888 andi s3,a4,7; 0x8288c blt s3,t6 *)
  step. mn_chk1 19 (body + Z.of_nat d) k1 SK1 2%nat.
  (* 0x82708 lb t6,0(s1): the shadow byte of the granule of mp + 2 is 0 *)
  pose proof (mn_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 2 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (mn_rng_sh RNG mp 40 (mp + 2) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  (* 0x8270c lbu a4,0(a4): d1 = body[d] *)
  pose proof (mn_rd8 _ body bb d (body + Z.of_nat d) BBm ltac:(lia) ltac:(lia)) as HR.
  pose proof (rng_sub' RNG body L (body + Z.of_nat d) 1 RB ltac:(lia)) as RH.
  step. clear HR RH.
  (* 0x82710 bnez t6: falls through *)
  step. brc false.
  (* 0x82714 li t6,192; 0x82718 sb a4,0(a5): m->d1 := body[d] *)
  step. step.
  (* 0x8271c bne s2,t6: n = 1 iff (s & 0xe0) = 0xc0 *)
  step. rewrite mn_land_c0 by lia.
  destruct HN as [N|N]; rewrite N; cbn [negb Nat.eqb].
  (* n = 1: 0x82720 li a4,0; 0x82724 j 0x82748: d2 = 0 *)
  1: step; step.
  (* n = 2: 0x82728 addi a4,a7,1; 0x8272c bltu t5,a4: the UBSan check, not taken *)
  2: step; setreg 14 (Z_to_bv 64 (Z.of_nat (S d))) ltac:(weq).
  2: step; br false.
  (* 0x82730 add a4,t4,a4; 0x82734 srli a5,a4,3; 0x82738 add a5,a5,t1; 0x8273c lb: the shadow byte of
     body + d + 1 *)
  2: step; step; step; rewrite (mn_srl3 (body + Z.of_nat (S d))) by lia.
  2: destruct (mn_sh_byte m0 _ (bv_unsigned sp0) c mp body L (Z.of_nat (S d)) AP1 AP2 ADc ADm ADb ltac:(lia) MU)
       as (k3 & MK & SK3).
  2: pose proof (rd1 _ _ _ MK) as HR.
  2: pose proof (mn_rng_sh RNG body L (body + Z.of_nat (S d)) ltac:(lia) RSB ltac:(lia)) as RH.
  2: step; clear HR RH MK.
  (* 0x82740 bnez a5; 0x828c4 andi a7,a4,7; 0x828c8 blt a7,a5 *)
  2: step; mn_chk1 17 (body + Z.of_nat (S d)) k3 SK3 2%nat.
  (* 0x82744 lbu a4,0(a4): d2 = body[d + 1] *)
  2: pose proof (mn_rd8 _ body bb (S d) (body + Z.of_nat (S d)) BBm ltac:(lia) ltac:(lia)) as HR.
  2: pose proof (rng_sub' RNG body L (body + Z.of_nat (S d)) 1 RB ltac:(lia)) as RH.
  2: step; clear HR RH.
  (* 0x82748 lb a5,0(s0): the shadow byte of the granule of mp + 3 is 0; 0x8274c bnez a5: falls through *)
  all: pose proof (mn_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 3 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU) as G.
  all: pose proof (rd1 _ _ _ G) as HR.
  all: pose proof (mn_rng_sh RNG mp 40 (mp + 3) ltac:(lia) RSM ltac:(lia)) as RH.
  all: step; clear HR RH G.
  all: step; brc false.
  (* 0x82750 sb a4,3(a1): m->d2 *)
  all: step.
  (* 0x82754 addi a1,a1,32; 0x82758 srli a3,a1,3; 0x8275c add a3,a3,t1; 0x82760 lbu; 0x82764 bnez: the shadow byte
     of the granule of mp + 32 is 0 *)
  all: step; step; step; rewrite (mn_srl3 (mp + 32)) by lia.
  all: pose proof (mn_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 32 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU) as G.
  all: pose proof (rd1 _ _ _ G) as HR.
  all: pose proof (mn_rng_sh RNG mp 40 (mp + 32) ltac:(lia) RSM ltac:(lia)) as RH.
  all: step; clear HR RH G.
  all: step; brc false.
  (* 0x82768 sub a3,a6,t2; 0x8276c sd a3,0(a1): m->len := end - pos *)
  all: step; step.
  (* 0x82770 lbu a1,0(t0); 0x82774 bnez a1: the shadow byte of the granule of c + 16 is 0 *)
  all: pose proof (mn_sh_gran m0 _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU) as G.
  all: pose proof (rd1 _ _ _ G) as HR.
  all: pose proof (mn_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
  all: step; clear HR RH G.
  all: step; brc false.
  (* 0x82778 sd a6,16(a2): c->pos := end *)
  all: step.
  (* 0x8277c addi a0,a2,24; 0x82780 srli a1,a0,3; 0x82784 add a1,a1,t1; 0x82788 lb: the shadow byte of c + 24 *)
  all: step; step; step; rewrite (mn_srl3 (c + 24)) by lia.
  all: destruct (mn_sh_byte m0 _ (bv_unsigned sp0) c mp c 25 24 AP1 AP2 ADc ADm ADc ltac:(lia) MU) as (k5 & MK & SK5).
  all: pose proof (rd1 _ _ _ MK) as HR.
  all: pose proof (mn_rng_sh RNG c 25 (c + 24) ltac:(lia) RSC ltac:(lia)) as RH.
  all: step; clear HR RH MK.
  (* 0x8278c bnez a1; 0x828b8 andi a2,a0,7; 0x828bc blt a2,a1 *)
  all: step; mn_chk1 12 (c + 24) k5 SK5 2%nat.
  (* 0x82790 sb t3,0(a0): c->status := s; 0x82794 li a3,1 *)
  all: step; step.
  all: eapply mn_fin_at;
       [ rewrite RS'; reflexivity
       | exact MU
       | exact FRm
       | rewrite RS', N; exact CCm
       | rewrite mn_sub_nat in CMm by lia; rewrite RS', N; exact CMm ].
Qed.

(* 0x82640 *)
Lemma mn_main : forall (r13 r14 r16 r18 r19 r20 r21 r22 r31 : word) (m : word -> option byte),
  munch W m0 m -> rw_cells rsegs m (bv_unsigned sp0 - 64) FRC -> rw_cells rsegs m c CUR0 ->
  rw_cells rsegs m mp MC1 -> bytes_at rsegs m body bb ->
  evtF rsegs RNG Q (ST 0x8c924 (Z_to_bv 64 (c + 16)) (Z_to_bv 64 mp) (Z_to_bv 64 c) r13 r14 (Z_to_bv 64 (mp + 2))
                       r16 (Z_to_bv 64 (Z.of_nat d)) r18 r19 r20 r21 r22 (Z_to_bv 64 L) r31 m).
Proof.
  intros r13 r14 r16 r18 r19 r20 r21 r22 r31 m MU FRm CCm CMm BBm.
  pose proof (chan_n_cases s) as HN.
  (* 0x82640 andi s2,t3,224; 0x82644 addi a4,s2,-192; 0x82648 snez s3,a4; 0x8264c addi s3,s3,1: s3 = n *)
  step. rewrite (unsigned_lit s) by lia.
  step. step. step. rewrite mn_snez_n by lia.
  (* 0x82650 add a6,s3,a7: a6 = d + n *)
  step.
  (* 0x82654 bgeu t5,a6: len >= d + n *)
  step.
  destruct (Nat.ltb_spec (length bb) (d + chan_n s)) as [SH|SH].
  { (* too few bytes: 0x82658 lbu a1,0(t0); 0x8265c bnez a1: the shadow byte of the granule of c + 16 is 0 *)
    br false.
    assert (RS' : msg_step bb pos st = mr_plain MkChanShort pos (length bb) st run).
    { rewrite RS. unfold chan_step.
      replace (length bb <? d + chan_n s)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    pose proof (mn_sh_gran m0 _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU) as G.
    pose proof (rd1 _ _ _ G) as HR.
    pose proof (mn_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
    step. clear HR RH G.
    step. brc false.
    (* 0x82660 sd t5,0(a0): c->pos := len; 0x82664 j 0x826d4; 0x826d4 li a3,-6; 0x826d8 j 0x82798 *)
    step. step. step. step.
    eapply mn_fin_at;
      [ rewrite RS'; reflexivity | exact MU | exact FRm | rewrite RS'; exact CCm | rewrite RS'; exact CMm ]. }
  br true.
  (* 0x82668 not t5,t4: t5 = 2^64 - 1 - body; 0x8266c mv s4,a7: s4 = q = d *)
  step. rewrite (mn_not_val body) by first [lia | reflexivity].
  step.
  destruct HN as [N|N]; rewrite N; [change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2].
  (* the data byte d. 0x82670 bltu t5,s4: the UBSan check, not taken *)
  all: step; br false.
  (* 0x82674 add a4,t4,s4; 0x82678 srli s5,a4,3; 0x8267c add s5,s5,t1; 0x82680 lb: its shadow byte *)
  all: step; step; step; rewrite (mn_srl3 (body + Z.of_nat d)) by lia.
  all: destruct (mn_sh_byte m0 _ (bv_unsigned sp0) c mp body L (Z.of_nat d) AP1 AP2 ADc ADm ADb ltac:(lia) MU)
         as (k1 & MK & SK1).
  all: pose proof (rd1 _ _ _ MK) as HR.
  all: pose proof (mn_rng_sh RNG body L (body + Z.of_nat d) ltac:(lia) RSB ltac:(lia)) as RH.
  all: step; clear HR RH MK.
  (* 0x82684 bnez s5; 0x826a0 andi s6,a4,7; 0x826a4 blt s6,s5 *)
  all: step; mn_chk1 22 (body + Z.of_nat d) k1 SK1 2%nat.
  (* 0x82688 lb a4,0(a4): body[d]; 0x8268c bltz a4 *)
  all: pose proof (mn_rd8 _ body bb d (body + Z.of_nat d) BBm ltac:(lia) ltac:(lia)) as HR.
  all: pose proof (rng_sub' RNG body L (body + Z.of_nat d) 1 RB ltac:(lia)) as RH.
  all: pose proof (mn_at8_range bb d) as X1.
  all: step; clear HR RH.
  all: step; rewrite mn_sxb_lts by lia.
  all: destruct (Z.leb_spec 128 (at8 bb d)) as [C1d|C1d]; cbv iota;
       [ (* bit 7 set: 0x826b0 with s4 = d *)
         eapply (mn_cut_at d);
         [ rewrite RS; unfold chan_step;
           replace (length bb <? d + chan_n s)%nat with false by (symmetry; apply Nat.ltb_ge; lia);
           replace (0x80 <=? at8 bb d) with true by (symmetry; apply Z.leb_le; lia); reflexivity
         | exact MU | exact FRm | exact CCm | exact CMm ]
       | ].
  (* 0x82690 addi s3,s3,-1; 0x82694 addi s4,s4,1; 0x82698 bnez s3 *)
  all: step; step; setreg 20 (Z_to_bv 64 (Z.of_nat (S d))) ltac:(weq); step.
  (* n = 1: 0x8269c j 0x826dc *)
  1: brc false.
  1: step; eapply mn_data_at;
       [ rewrite N; weq | reflexivity | reflexivity | reflexivity | lia | lia | intros; lia
       | exact MU | exact FRm | exact CCm | exact CMm | exact BBm ].
  (* n = 2: the data byte d + 1. 0x82670 bltu t5,s4: the UBSan check, not taken *)
  brc true.
  step. br false.
  step. step. step. rewrite (mn_srl3 (body + Z.of_nat (S d))) by lia.
  destruct (mn_sh_byte m0 _ (bv_unsigned sp0) c mp body L (Z.of_nat (S d)) AP1 AP2 ADc ADm ADb ltac:(lia) MU)
    as (k2 & MK & SK2).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (mn_rng_sh RNG body L (body + Z.of_nat (S d)) ltac:(lia) RSB ltac:(lia)) as RH.
  step. clear HR RH MK.
  step. mn_chk1 22 (body + Z.of_nat (S d)) k2 SK2 2%nat.
  pose proof (mn_rd8 _ body bb (S d) (body + Z.of_nat (S d)) BBm ltac:(lia) ltac:(lia)) as HR.
  pose proof (rng_sub' RNG body L (body + Z.of_nat (S d)) 1 RB ltac:(lia)) as RH.
  pose proof (mn_at8_range bb (S d)) as X2.
  step. clear HR RH.
  step. rewrite mn_sxb_lts by lia.
  destruct (Z.leb_spec 128 (at8 bb (S d))) as [C2d|C2d]; cbv iota.
  { (* bit 7 set: 0x826b0 with s4 = d + 1 *)
    eapply (mn_cut_at (S d)).
    - rewrite RS. unfold chan_step. rewrite N.
      replace (length bb <? d + 2)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (0x80 <=? at8 bb d) with false by (symmetry; apply Z.leb_gt; lia).
      replace (0x80 <=? at8 bb (S d)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - exact MU.
    - exact FRm.
    - exact CCm.
    - exact CMm. }
  (* 0x82690 addi s3,s3,-1; 0x82694 addi s4,s4,1; 0x82698 bnez s3; 0x8269c j 0x826dc *)
  step. step. step.
  brc false.
  step. eapply mn_data_at;
    [ rewrite N; weq | reflexivity | reflexivity | reflexivity | lia | lia | intros; lia
    | exact MU | exact FRm | exact CCm | exact CMm | exact BBm ].
Qed.

End MC.

Theorem mn_chan_of_fin : mn_fin_F -> mn_chan_F.
Proof.
  intros FIN. unfold mn_chan_F.
  intros RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra gp tp a6 y21 y22 F fc m0 m c mp body bb mj
    pos st s run d CTX Hs Hrun Hd RS.
  destruct CTX as (Hlt & Hst & Hmj & Hc8 & Hm8 & Hb0 & HF & AP1 & AP2 & MU & FR & CC & CM & BB & ADc & ADm & ADb &
                   OSc & OSm & OSb & D1 & D2 & D3 & RFR & RC & RM & RB & RSC & RSM & RSB).
  unfold MN_FRAME, MN_CHAN, mn_fr, mn_msg1, PCur.cursor_cells, off_stk, shadow_addr, ASAN_K in *.
  assert (Bc : 0 <= c /\ c + 25 <= 0x800000000000) by (destruct ADc as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  assert (Bm : 0 <= mp /\ mp + 40 <= 0x800000000000) by (destruct ADm as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  assert (Bb : 0 <= body /\ body + Z.of_nat (length bb) <= 0x800000000000)
    by (destruct ADb as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  eapply mn_main; eassumption.
Qed.
