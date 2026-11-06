(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: twin of lib/AZ/LibA/StepF.v over lib.Lib. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode to libdiginet/fuzz_decode image A; module paths changed *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libdiginet/fuzz_decode/lib/Lib/StepF.v to libdiginet/fuzz_codec; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Lib/StepF.v; 366 of its 400 lines of code are new or changed and 688 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of diginet_msg_next in fuzz_frame.ubsan (0x141a0) proves its contract, and no UBSan check branch is taken. *)
(* Modified by Theorem Labs, 2026-10: the footprint walk of diginet_cursor_init in libdiginet/fuzz_frame's image A (fuzz_frame.asan), after proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_counter_F.v (StepF's step, the frame carve, the asan shadow loads), with the four stores to the caller's cursor. *)
(* Modified by Theorem Labs, 2026-10: proof of diginet_mac_is_digidesign_contract_F (fuzz_frame.asan, image A) in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_nosh.v, for three bytes and the result DgnSpec.oui_of. *)
(* Modified by Theorem Labs, 2026-10: the channel piece mn_chan_F of the image-A walk of diginet_msg_next (fuzz_frame.asan, 0x835a0 to the epilogue 0x83710); rd8, at8_range, sxb_lts, snez_n, land_c0 and rw_conv taken from the UBSan walk; cinit_signed0, the shadow-outside and granule lemmas of the cursor walk generalized to the frame, the cursor and the message; the 1-byte check of the mac walk made a tactic that joins its two paths. *)
(* Modified by Theorem Labs, 2026-10: the sysex piece mn_sys_F (0x833f8 to the epilogue); the byte, shadow, granule and range lemmas and the tactics of the channel piece taken unchanged under the names ms_..., at8_skipn added from the UBSan walk, and two compares added: the loop's end test (a sum of two words against 0) and the test of a loaded byte against 247. *)
(* Modified by Theorem Labs, 2026-10: the sysex piece mn_sys_F of the image-B walk (fuzz_frame.asan-ubsan, 0x83500 to the epilogue 0x83828); the lemmas restated for the 64-byte frame and for shadow bytes read from the entry memory m0, not_val taken from the UBSan walk, and the two UBSan checks of this arm (0x8351c, 0x83610) shown not taken. *)
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

(* Proof of mn_sys_of_fin: from 0x82470 (body[pos] = 0xf0) the search for the first 0xf7 after pos
   (0x82480 - 0x824ac) reaches the epilogue 0x82798 on both its ends, where the hypothesis mn_fin_F gives the
   post state. 0x82470 - 0x8247c set t3 = not body = 2^64 - 1 - body (ms_not_val), t4 = pos - len (as a 64-bit
   word), a5 = 1 and s0 = 247. The loop keeps a5 = i, the index of the byte it reads next relative to pos; its test
   `add a3,t4,a5; beqz a3` is pos + i = len (ms_loop_test), the UBSan check `bltu t3,a3` (a3 = pos + i) is not taken
   because body + pos + i < body + len <= APPMEM_END, and the compare `bne a3,s0` is body[pos + i] = 0xf7
   (ms_zxb_eqb). The loop lemma ms_loop runs by induction on the number of bytes left, with the invariant that none
   of body[pos + 1 .. pos + i) is 0xf7; the loop stores nothing.
   No 0xf7 (0x82514): c + 24 := 0, a3 = -6 and (in the shared tail 0x825c4) c + 16 := len (t5), which is msg_step's
   MkSysexCut. A 0xf7 at pos + 1 + j (0x82534, a5 = j + 2): c + 24 := 0, mp + 0 := 0xf0, mp + 1 := 0, the UBSan
   check `beq a4,a3` (a3 = -1) not taken because body + pos < 2^64 - 1, mp + 8 := body + pos + 1, mp + 16 := j,
   mp + 32 := j + 2, a3 = 1 and c + 16 := pos + j + 2 (t5), which is msg_step's MkSysex for find_f7 = Some j.
   Each shadow byte the code loads lies outside the frame, the cursor and the message (ms_sh_out), the only bytes
   the run changes, so it keeps its value from the entry memory m0, where mn_ctx states the three ranges
   addressable. A 1-byte check at a loads the shadow byte k of a (lb), which is 0 or a mod 8 < k (addressable);
   when k <> 0 the code goes to the andi / blt pair, which goes back, so the error path (a call of errpath_load1 /
   errpath_store1) is not reached. The tactic ms_chk1 proves the code after the check once, for any value of the
   register the andi writes, and uses it for both paths. The checks of mp and mp + 1 and the 8-byte checks of
   mp + 8, mp + 16, mp + 32 and c + 16 load the shadow byte of a granule whose last byte lies in the accessed
   object (ms_sh_gran): it is 0, so the `bnez` is not taken. *)

(* ---------- bytes and words ---------- *)

Lemma ms_rd8 : forall m A l i E, bytes_at rsegs m A l -> (i < length l)%nat -> E = A + Z.of_nat i ->
  ov_read_bytes rsegs m (Z_to_bv 64 E) 1 = Some [b8 (at8 l i)].
Proof.
  intros m A l i E BL Hi ->. change (Z_to_bv 64 (A + Z.of_nat i)) with (wa (A + Z.of_nat i)).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL) by lia. f_equal. clear BL.
  unfold at8. rewrite b8_bz.
  revert i Hi. induction l as [|x l IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma ms_at8_range : forall l i, 0 <= at8 l i < 256.
Proof. intros l i. unfold at8. apply bz_range. Qed.

Lemma ms_at8_skipn : forall n l k, at8 (skipn n l) k = at8 l (n + k).
Proof.
  induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn [skipn Nat.add].
  - unfold at8. destruct k; reflexivity.
  - exact (IH l k).
Qed.

Lemma ms_zxbu : forall x, 0 <= x < 256 -> bv_unsigned (zxb (b8 x)) = x.
Proof.
  intros x Hx. unfold zxb. pose proof (bz_range (b8 x)) as R. unfold bz in R.
  rewrite unsigned_lit by lia. apply bz_b8. lia.
Qed.

(* 0x824ac: the loaded byte against 247 *)
Lemma ms_zxb_eqb : forall x z, 0 <= x < 256 -> 0 <= z < 2^64 ->
  bv_eqb (zxb (b8 x)) (Z_to_bv 64 z) = (x =? z).
Proof.
  intros x z Hx Hz. unfold bv_eqb. rewrite ms_zxbu by lia. rewrite unsigned_lit by lia. reflexivity.
Qed.

(* 0x82480 - 0x82484: (pos - len) + i is 0 exactly when pos + i = len *)
Lemma ms_loop_test : forall p l k, 0 <= p -> 0 <= k -> p + k <= l -> l < 2^64 ->
  bv_eqb (Z_to_bv 64 (p - l + k)) (Z_to_bv 64 0) = (p + k =? l).
Proof.
  intros p l k Hp Hk Hpk Hl. unfold bv_eqb. rewrite unsigned_lit_wrap, (unsigned_lit 0) by lia.
  destruct (Z.eqb_spec (p + k) l) as [E|E].
  - replace (p - l + k) with 0 by lia. reflexivity.
  - apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

(* 0x82470 not t3,t4: not x, the bound of the UBSan check 0x8248c *)
Lemma ms_not_val : forall x w, 0 <= x < 2^64 -> w = 18446744073709551615 ->
  Z.lxor (bv_unsigned (Z_to_bv 64 x)) w = 2^64 - 1 - x.
Proof. intros x w Hx ->. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. lia. Qed.

(* srli by 3 of an address *)
Lemma ms_srl3 : forall x, 0 <= x < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof. intros x Hx. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* 0x82564 stores the low byte of -16: m->status = 0xf0 *)
Lemma ms_m16 : Z_to_bv 8 (-16) = b8 240.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* the value of a zero shadow byte loaded by lb *)
Lemma ms_sxb0 : sxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---------- shadow bytes ---------- *)

Lemma ms_signed0 : forall k : byte, bv_signed k = 0 -> k = Z_to_bv 8 0.
Proof.
  intros k H. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0.
  pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ms_sh_not_app : forall x, app_mem x -> ~ app_mem (x / 8 + 2147450880).
Proof.
  intros x H. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of an application byte lies outside the frame [S - 64, S), the cursor [c, c + 25) and the
   message [mp, mp + 40). *)
Lemma ms_sh_out : forall m S c mp x, app_mem (S - 64) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> app_mem x ->
  outside [(S - 64, S); (c, c + 25); (mp, mp + 40)] (x / 8 + 2147450880).
Proof.
  intros m S c mp x A1 A2 (P0 & N0 & PE & AB) (Q0 & M0 & QE & AM) Ax. pose proof (ms_sh_not_app x Ax) as N.
  cbn [outside]. split; [|split; [|split; [|exact I]]]; intros W; apply N.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - destruct (AB (x / 8 + 2147450880 - c) ltac:(lia)) as (Ay & _).
    replace (c + (x / 8 + 2147450880 - c)) with (x / 8 + 2147450880) in Ay by lia. exact Ay.
  - destruct (AM (x / 8 + 2147450880 - mp) ltac:(lia)) as (Ay & _).
    replace (mp + (x / 8 + 2147450880 - mp)) with (x / 8 + 2147450880) in Ay by lia. exact Ay.
Qed.

(* The shadow byte of p + i, read in a memory that differs from m only in the three ranges. *)
Lemma ms_sh_byte : forall m m' S c mp p n i, app_mem (S - 64) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> addressable m p n -> 0 <= i < n ->
  munch [(S - 64, S); (c, c + 25); (mp, mp + 40)] m m' ->
  exists k, mrd rsegs m' (wa ((p + i) / 8 + 2147450880)) = Some k /\ shadow_ok (p + i) (bv_signed k).
Proof.
  intros m m' S c mp p n i A1 A2 AC AM (P0 & N0 & PE & AB) Hi MU.
  destruct (AB i Hi) as (Ax & k & MK & SK). exists k. split; [|exact SK].
  unfold shadow_addr, ASAN_K in MK. unfold mrd in *. rewrite MU; [exact MK|].
  rewrite wa_unsigned by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ax; Z.div_mod_to_equations; lia).
  exact (ms_sh_out m S c mp _ A1 A2 AC AM Ax).
Qed.

(* The shadow byte of the granule of p + j is 0 when the 8 bytes from p + j lie in [p, p + n). *)
Lemma ms_sh_gran : forall m m' S c mp p n j, app_mem (S - 64) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> addressable m p n -> 0 <= j -> j + 8 <= n ->
  munch [(S - 64, S); (c, c + 25); (mp, mp + 40)] m m' ->
  mrd rsegs m' (wa ((p + j) / 8 + 2147450880)) = Some (Z_to_bv 8 0).
Proof.
  intros m m' S c mp p n j A1 A2 AC AM AP Hj Hn MU.
  pose proof (Z.mod_pos_bound (p + j) 8 ltac:(lia)) as Mp.
  destruct (ms_sh_byte m m' S c mp p n (j + 7 - (p + j) mod 8) A1 A2 AC AM AP ltac:(lia) MU) as (k & MK & SK).
  assert (E1 : (p + (j + 7 - (p + j) mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  assert (E2 : (p + (j + 7 - (p + j) mod 8)) / 8 = (p + j) / 8) by (Z.div_mod_to_equations; lia).
  rewrite E2 in MK. rewrite MK. f_equal. apply ms_signed0.
  unfold shadow_ok in SK. rewrite E1 in SK. lia.
Qed.

(* The shadow byte of x, x in [p, p + n), lies in the shadow range of [p, p + n). *)
Lemma ms_rng_sh : forall RNG p n x, 0 <= p ->
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
Ltac ms_chk1 r E k SK nerr :=
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

Section MS.
Variables (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
  (ra gp tp y21 y22 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
  (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z).
Hypothesis FIN : mn_fin_F.
Hypothesis E0 : at8 bb pos = 240.
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

Local Abbreviation W := [(bv_unsigned sp0 - 64, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)].
Local Abbreviation L := (Z.of_nat (length bb)).
Local Abbreviation Q := (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st).
(* the frame words *)
Local Abbreviation FRC := [C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 ra0].
(* the cursor at 0x82470 *)
Local Abbreviation CUR0 := [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 (Z.of_nat pos)); C1 (b8 st)].
(* the message at 0x82470 *)
Local Abbreviation MC0 := [C1 (nth 0 mj (b8 0)); C1 (nth 1 mj (b8 0)); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].
Hypothesis MU0 : munch W m0 m.
Hypothesis FRm : rw_cells rsegs m (bv_unsigned sp0 - 64) FRC.
Hypothesis CCm : rw_cells rsegs m c CUR0.
Hypothesis CMm : rw_cells rsegs m mp MC0.
Hypothesis BBm : bytes_at rsegs m body bb.

(* the state: s0, s1, a3, a5, s4, t3 and t4 vary, the other registers are those of mn_sys_F *)
Local Abbreviation ST pc v8 v9 v13 v15 v20 v28 v29 mm :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 64)) gp tp
           (Z_to_bv 64 ((c + 16) / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.of_nat pos))
           v8 v9 (Z_to_bv 64 (c + 16)) (Z_to_bv 64 mp) (Z_to_bv 64 c) v13
           (Z_to_bv 64 (body + Z.of_nat pos)) v15 (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 (mp + 16))
           (Z_to_bv 64 ((mp + 8) / 8 + 2147450880)) (Z_to_bv 64 ((mp + 16) / 8 + 2147450880)) v20 y21 y22
           x23 x24 x25 x26 x27 v28 v29 (Z_to_bv 64 L) (Z_to_bv 64 0))
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* 0x82798: the epilogue, by mn_fin_F; a3 holds the result *)
Lemma ms_fin_at : forall (ra' t0' t1' t2' v8 v9 a0' a1' a2' v13 a4' a5' a6' a7' v18 v19 v20 v21 v22 t3' t4' t5' t6' : word)
    (mm : word -> option byte),
  v13 = Z_to_bv 64 (mr_code (msg_step bb pos st)) ->
  munch W m0 mm -> rw_cells rsegs mm (bv_unsigned sp0 - 64) FRC ->
  rw_cells rsegs mm c (PCur.cursor_cells body L (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))) ->
  rw_cells rsegs mm mp (PMsg.msg_cells body mj (msg_step bb pos st)) ->
  evtF rsegs RNG Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp0 - 64)) gp tp t0' t1' t2' v8 v9 a0' a1' a2' v13 a4' a5' a6' a7'
             v18 v19 v20 v21 v22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
        F (Z_to_bv 64 0x8ca7c) fc None mm (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' v8 v9 a0' a1' a2' v13 a4' a5' a6' a7' v18 v19 v20 v21 v22 t3' t4' t5' t6' mm
    -> MU FRz CCz CMz.
  eapply FIN.
  - unfold MN_FRAME. lia.
  - unfold MN_FRAME. exact RFR.
  - unfold mn_fr, MN_FRAME. exact FRz.
  - unfold MN_FRAME. exact MU.
  - exact CCz.
  - exact CMz.
Qed.

(* 0x82514: the search ran to the end of the body, no 0xf7. c->status := 0, c->pos := len, a3 = -6. *)
Lemma ms_cut_at : forall (v8 v9 v13 v15 v20 v28 v29 : word),
  (forall q, (pos < q < length bb)%nat -> at8 bb q <> 247) ->
  evtF rsegs RNG Q (ST 0x8c7f8 v8 v9 v13 v15 v20 v28 v29 m).
Proof.
  intros v8 v9 v13 v15 v20 v28 v29 Hnf.
  assert (RS : msg_step bb pos st = mr_plain MkSysexCut pos (length bb) 0 0).
  { unfold msg_step.
    replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    replace (at8 bb pos =? 0xf0) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite (find_f7_none_intro (skipn (S pos) bb)); [reflexivity|].
    intros q Hq. rewrite length_skipn in Hq. rewrite ms_at8_skipn. apply Hnf. lia. }
  (* 0x82514 addi a2,a2,24; 0x82518 srli a1,a2,3; 0x8251c add a1,a1,t1; 0x82520 lb a1,0(a1): the shadow byte
     of c + 24 *)
  step. step. rewrite (ms_srl3 (c + 24)) by lia.
  step.
  destruct (ms_sh_byte m0 m (bv_unsigned sp0) c mp c 25 24 AP1 AP2 ADc ADm ADc ltac:(lia) MU0) as (k0 & MK & SK0).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (ms_rng_sh RNG c 25 (c + 24) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x82524 bnez a1; 0x82808 andi a3,a2,7; 0x8280c blt a3,a1 *)
  step. ms_chk1 13 (c + 24) k0 SK0 2%nat.
  (* 0x82528 sb zero,0(a2): c->status := 0; 0x8252c li a3,-6; 0x82530 j 0x825c4 *)
  step. step. step.
  (* 0x825c4 lbu a1,0(t0); 0x825c8 bnez a1: the shadow byte of the granule of c + 16 *)
  pose proof (ms_sh_gran m0 _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU0) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x825cc sd t5,0(a0): c->pos := len; 0x825d0 j 0x82798 *)
  step. step.
  eapply ms_fin_at;
    [ rewrite RS; first [reflexivity | apply bv_eq; reflexivity]
    | exact MU0 | exact FRm | rewrite RS; exact CCm | rewrite RS; exact CMm ].
Qed.

(* 0x82534: body[pos + 1 + j] is the first 0xf7 after pos, a5 = j + 2. m->status := 0xf0, m->running := 0,
   m->sysex := body + pos + 1, m->sysex_len := j, m->len := j + 2, c->pos := pos + j + 2, c->status := 0,
   a3 = 1. *)
Lemma ms_found_at : forall (j : nat) (v8 v9 v13 v15 v20 v28 v29 : word),
  (S pos + j < length bb)%nat -> at8 bb (S pos + j) = 247 ->
  (forall q, (pos < q < S pos + j)%nat -> at8 bb q <> 247) ->
  v15 = Z_to_bv 64 (Z.of_nat (j + 2)) ->
  evtF rsegs RNG Q (ST 0x8c818 v8 v9 v13 v15 v20 v28 v29 m).
Proof.
  intros j v8 v9 v13 v15 v20 v28 v29 Hj F7 Hnf ->.
  assert (RS : msg_step bb pos st = MsgRes MkSysex pos (pos + j + 2) 0 240 0 0 0 (S pos) j (j + 2)).
  { unfold msg_step.
    replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    replace (at8 bb pos =? 0xf0) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite (find_f7_intro (skipn (S pos) bb) j); [reflexivity | | |].
    - rewrite length_skipn. lia.
    - rewrite ms_at8_skipn. exact F7.
    - intros q Hq. rewrite ms_at8_skipn. apply Hnf. lia. }
  (* 0x82534 addi a2,a2,24; 0x82538 srli a3,a2,3; 0x8253c add a3,a3,t1; 0x82540 lb a3,0(a3): the shadow byte
     of c + 24 *)
  step. step. rewrite (ms_srl3 (c + 24)) by lia.
  step.
  destruct (ms_sh_byte m0 m (bv_unsigned sp0) c mp c 25 24 AP1 AP2 ADc ADm ADc ltac:(lia) MU0) as (k0 & MK & SK0).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (ms_rng_sh RNG c 25 (c + 24) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x82544 bnez a3; 0x82818 andi t3,a2,7; 0x8281c blt t3,a3 *)
  step. ms_chk1 28 (c + 24) k0 SK0 2%nat.
  (* 0x82548 sb zero,0(a2): c->status := 0 *)
  step.
  (* 0x8254c srli a2,a1,3; 0x82550 add a2,a2,t1; 0x82554 lb a2,0(a2): the shadow byte of the granule of mp *)
  step. rewrite (ms_srl3 mp) by lia.
  step.
  pose proof (ms_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 0 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU0) as G.
  rewrite Z.add_0_r in G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG mp 40 mp ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  (* 0x82558 bnez a2: not taken *)
  rewrite ?ms_sxb0. step. if_false.
  (* 0x8255c li a3,-16; 0x82560 addi a2,a1,1; 0x82564 sb a3,0(a1): m->status := 0xf0 *)
  step. step. step.
  rewrite ms_m16 in CMm.
  (* 0x82568 srli a3,a2,3; 0x8256c add a3,a3,t1; 0x82570 lb a3,0(a3): the shadow byte of the granule of mp + 1 *)
  step. rewrite (ms_srl3 (mp + 1)) by lia.
  step.
  pose proof (ms_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 1 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU0) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG mp 40 (mp + 1) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  (* 0x82574 bnez a3: not taken *)
  rewrite ?ms_sxb0. step. if_false.
  (* 0x82578 li a3,-1; 0x8257c sb zero,0(a2): m->running := 0 *)
  step. step.
  (* 0x82580 beq a4,a3: the UBSan check, not taken (body + pos <> 2^64 - 1) *)
  step. br false.
  (* 0x82584 lbu a2,0(s2); 0x82588 bnez a2: the shadow byte of the granule of mp + 8 *)
  pose proof (ms_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 8 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU0) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG mp 40 (mp + 8) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x8258c addi a4,a4,1; 0x82590 sd a4,0(a6): m->sysex := body + pos + 1 *)
  step.
  replace (Z_to_bv 64 (body + Z.of_nat pos + 1)) with (Z_to_bv 64 (body + Z.of_nat (S pos))) by (f_equal; lia).
  step.
  (* 0x82594 lbu a2,0(s3); 0x82598 bnez a2: the shadow byte of the granule of mp + 16 *)
  pose proof (ms_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 16 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU0) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG mp 40 (mp + 16) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x8259c addi a2,a5,-2; 0x825a0 sd a2,16(a1): m->sysex_len := j *)
  step.
  replace (Z_to_bv 64 (Z.of_nat (j + 2) + -2)) with (Z_to_bv 64 (Z.of_nat j)) by (f_equal; lia).
  step.
  (* 0x825a4 addi a1,a1,32; 0x825a8 srli a2,a1,3; 0x825ac add a2,a2,t1; 0x825b0 lbu a2,0(a2); 0x825b4 bnez a2:
     the shadow byte of the granule of mp + 32 *)
  step. step. rewrite (ms_srl3 (mp + 32)) by lia.
  step.
  pose proof (ms_sh_gran m0 _ (bv_unsigned sp0) c mp mp 40 32 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU0) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG mp 40 (mp + 32) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x825b8 add t5,t2,a5: t5 = pos + j + 2; 0x825bc sd a5,0(a1): m->len := j + 2; 0x825c0 li a3,1 *)
  step.
  replace (Z_to_bv 64 (Z.of_nat pos + Z.of_nat (j + 2))) with (Z_to_bv 64 (Z.of_nat (pos + j + 2)))
    by (f_equal; lia).
  step. step.
  (* 0x825c4 lbu a1,0(t0); 0x825c8 bnez a1: the shadow byte of the granule of c + 16 *)
  pose proof (ms_sh_gran m0 _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU0) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x825cc sd t5,0(a0): c->pos := pos + j + 2; 0x825d0 j 0x82798 *)
  step. step.
  eapply ms_fin_at;
    [ rewrite RS; first [reflexivity | apply bv_eq; reflexivity]
    | exact MU0 | exact FRm | rewrite RS; exact CCm | rewrite RS; exact CMm ].
Qed.

(* 0x82480: the search for 0xf7. a5 = i is the index of the next byte relative to pos, t4 = pos - len,
   t3 = 2^64 - 1 - body, s0 = 247; n is the number of bytes left. *)
Lemma ms_loop : forall (n i : nat) (v8 v9 v13 v15 v20 v28 v29 : word),
  (1 <= i)%nat -> (n + pos + i = length bb)%nat ->
  v8 = Z_to_bv 64 247 -> v15 = Z_to_bv 64 (Z.of_nat i) ->
  v28 = Z_to_bv 64 (2^64 - 1 - body) -> v29 = Z_to_bv 64 (Z.of_nat pos - L) ->
  (forall q, (pos < q < pos + i)%nat -> at8 bb q <> 247) ->
  evtF rsegs RNG Q (ST 0x8c764 v8 v9 v13 v15 v20 v28 v29 m).
Proof.
  induction n as [|n IH]; intros i v8 v9 v13 v15 v20 v28 v29 Hi Hn -> -> -> -> Hnf.
  - (* pos + i = len: 0x82480 add a3,t4,a5; 0x82484 beqz a3 *)
    step. step.
    rewrite (ms_loop_test (Z.of_nat pos) L (Z.of_nat i)) by lia.
    replace (Z.of_nat pos + Z.of_nat i =? L) with true by (symmetry; apply Z.eqb_eq; lia).
    cbv iota.
    apply ms_cut_at. intros q Hq. apply Hnf. lia.
  - (* pos + i < len *)
    step. step.
    rewrite (ms_loop_test (Z.of_nat pos) L (Z.of_nat i)) by lia.
    replace (Z.of_nat pos + Z.of_nat i =? L) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv iota.
    (* 0x82488 add a3,t2,a5; 0x8248c bltu t3,a3: the UBSan check, not taken (pos + i <= 2^64 - 1 - body) *)
    step. step. br false.
    (* 0x82490 add a3,a4,a5; 0x82494 srli s1,a3,3; 0x82498 add s1,s1,t1; 0x8249c lb s1,0(s1): the shadow byte of
       body + pos + i *)
    step.
    step. rewrite (ms_srl3 (body + Z.of_nat pos + Z.of_nat i)) by lia.
    step.
    destruct (ms_sh_byte m0 m (bv_unsigned sp0) c mp body L (Z.of_nat pos + Z.of_nat i)
                AP1 AP2 ADc ADm ADb ltac:(lia) MU0) as (k1 & MK & SK1).
    replace (body + (Z.of_nat pos + Z.of_nat i)) with (body + Z.of_nat pos + Z.of_nat i) in MK, SK1 by lia.
    pose proof (rd1 _ _ _ MK) as HR.
    pose proof (ms_rng_sh RNG body L (body + Z.of_nat pos + Z.of_nat i) ltac:(lia) RSB ltac:(lia)) as RH.
    step. clear HR RH MK.
    (* 0x824a0 bnez s1; 0x824b4 andi s4,a3,7; 0x824b8 blt s4,s1 *)
    step. ms_chk1 20 (body + Z.of_nat pos + Z.of_nat i) k1 SK1 2%nat.
    (* 0x824a4 lbu a3,0(a3): body[pos + i]; 0x824a8 addi a5,a5,1; 0x824ac bne a3,s0 *)
    pose proof (ms_rd8 _ body bb (pos + i) (body + Z.of_nat pos + Z.of_nat i) BBm ltac:(lia) ltac:(lia)) as HR.
    pose proof (rng_sub' RNG body L (body + Z.of_nat pos + Z.of_nat i) 1 RB ltac:(lia)) as RH.
    pose proof (ms_at8_range bb (pos + i)) as XR.
    step. clear HR RH.
    step.
    step. rewrite ms_zxb_eqb by lia.
    destruct (Z.eqb_spec (at8 bb (pos + i)) 247) as [EQ|NE]; cbn [negb]; cbv iota.
    + (* 0x824b0 j 0x82534: the 0xf7 at pos + i *)
      step.
      replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (i - 1 + 2))) by (f_equal; lia).
      apply (ms_found_at (i - 1)%nat); try reflexivity.
      * lia.
      * replace (S pos + (i - 1))%nat with (pos + i)%nat by lia. exact EQ.
      * intros q Hq. apply Hnf. lia.
    + (* back to 0x82480 with i + 1 *)
      replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
      apply (IH (S i)); try reflexivity.
      * lia.
      * lia.
      * intros q Hq. destruct (Nat.eq_dec q (pos + i)) as [->|NEq]; [exact NE | apply Hnf; lia].
Qed.

(* 0x82470 *)
Lemma ms_main : forall (v8 v9 v13 v15 v20 : word),
  evtF rsegs RNG Q (ST 0x8c754 v8 v9 v13 v15 v20 (Z_to_bv 64 240) (Z_to_bv 64 body) m).
Proof.
  intros v8 v9 v13 v15 v20.
  (* 0x82470 not t3,t4: t3 = 2^64 - 1 - body *)
  step. rewrite (ms_not_val body) by first [lia | reflexivity].
  (* 0x82474 sub t4,t2,t5; 0x82478 li a5,1; 0x8247c li s0,247 *)
  step. uns. step. step.
  apply (ms_loop (length bb - pos - 1) 1); try reflexivity; try lia; intros q Hq; lia.
Qed.

End MS.

Theorem mn_sys_of_fin : mn_fin_F -> mn_sys_F.
Proof.
  intros FIN. unfold mn_sys_F.
  intros RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra gp tp y21 y22 F fc m0 m c mp body bb mj pos st
    CTX E0.
  destruct CTX as (Hlt & Hst & Hmj & Hc8 & Hm8 & Hb0 & HF & AP1 & AP2 & MU & FR & CC & CM & BB & ADc & ADm & ADb &
                   OSc & OSm & OSb & D1 & D2 & D3 & RFR & RC & RM & RB & RSC & RSM & RSB).
  unfold MN_FRAME, MN_SYS, mn_fr, mn_msg0, PCur.cursor_cells, off_stk, shadow_addr, ASAN_K in *.
  assert (Bc : 0 <= c /\ c + 25 <= 0x800000000000) by (destruct ADc as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  assert (Bm : 0 <= mp /\ mp + 40 <= 0x800000000000) by (destruct ADm as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  assert (Bb : 0 <= body /\ body + Z.of_nat (length bb) <= 0x800000000000)
    by (destruct ADb as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  eapply ms_main; eassumption.
Qed.
