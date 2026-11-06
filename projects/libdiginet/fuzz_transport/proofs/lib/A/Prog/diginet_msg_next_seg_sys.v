(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: twin of lib/AZ/LibA/StepF.v over lib.Lib. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode to libdiginet/fuzz_decode image A; module paths changed *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libdiginet/fuzz_decode/lib/Lib/StepF.v to libdiginet/fuzz_codec; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Lib/StepF.v; 370 of its 403 lines of code are new or changed and 689 lines of the source are left out. *)
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

(* Proof of mn_sys_of_fin: from 0x82210 (body[pos] = 0xf0) the search for the first 0xf7 after pos
   (0x82220 - 0x82244) reaches the epilogue 0x82528 on both its ends, where the hypothesis mn_fin_F gives the
   post state. The loop keeps a2 = k, the index of the byte it reads next relative to pos, and
   a3 = pos - len (as a 64-bit word); its test `add a1, a3, a2; beqz a1` is pos + k = len (ms_loop_test), its
   compare `bne a1, a4` with a4 = 247 is body[pos + k] = 0xf7 (ms_zxb_eqb). The loop lemma ms_loop runs by
   induction on the number of bytes left, with the invariant that none of body[pos + 1 .. pos + k) is 0xf7.
   No 0xf7: 0x82294 writes c->status = 0, a0 = -6 and (in the shared tail 0x8234c) c->pos = len, which is
   msg_step's MkSysexCut. A 0xf7 at pos + 1 + j: 0x822b4 writes c->status = 0, m->status = 0xf0,
   m->running = 0, m->sysex = body + pos + 1, m->sysex_len = j, m->len = j + 2, a0 = 1 and c->pos = pos + j + 2,
   which is msg_step's MkSysex for find_f7 = Some j.
   Each shadow byte the code loads lies outside the frame, the cursor and the message (ms_sh_out), the only bytes
   the run changes, so it keeps its value from the memory at 0x82210. A 1-byte check at a loads the shadow byte k
   of a (lb), which is 0 or a mod 8 < k (addressable); when k <> 0 the code goes to the andi / blt pair, which
   goes back, so no errpath_* call is reached. The tactic ms_chk1 proves the code after the check once, for any
   value of the register the andi writes, and uses it for both paths. An 8-byte check loads the shadow byte of a
   granule whose last byte lies in the accessed object (ms_sh_gran): it is 0. *)

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

(* 0x82244: the loaded byte against 247 *)
Lemma ms_zxb_eqb : forall x z, 0 <= x < 256 -> 0 <= z < 2^64 ->
  bv_eqb (zxb (b8 x)) (Z_to_bv 64 z) = (x =? z).
Proof.
  intros x z Hx Hz. unfold bv_eqb. rewrite ms_zxbu by lia. rewrite unsigned_lit by lia. reflexivity.
Qed.

(* 0x82220 - 0x82224: (pos - len) + k is 0 exactly when pos + k = len *)
Lemma ms_loop_test : forall p l k, 0 <= p -> 0 <= k -> p + k <= l -> l < 2^64 ->
  bv_eqb (Z_to_bv 64 (p - l + k)) (Z_to_bv 64 0) = (p + k =? l).
Proof.
  intros p l k Hp Hk Hpk Hl. unfold bv_eqb. rewrite unsigned_lit_wrap, (unsigned_lit 0) by lia.
  destruct (Z.eqb_spec (p + k) l) as [E|E].
  - replace (p - l + k) with 0 by lia. reflexivity.
  - apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

(* the same bytes under other cells *)
Lemma ms_rw_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite <- (cells_bytes_length cs' W'), EB, (cells_bytes_length cs W). exact V.
Qed.

(* srli by 3 of an address *)
Lemma ms_srl3 : forall x, 0 <= x < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof. intros x Hx. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* 0x822e4 stores the low byte of -16: m->status = 0xf0 *)
Lemma ms_m16 : Z_to_bv 8 (-16) = b8 240.
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

(* The shadow byte of an application byte lies outside the frame [S - 128, S), the cursor [c, c + 25) and the
   message [mp, mp + 40). *)
Lemma ms_sh_out : forall m S c mp x, app_mem (S - 128) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> app_mem x ->
  outside [(S - 128, S); (c, c + 25); (mp, mp + 40)] (x / 8 + 2147450880).
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
Lemma ms_sh_byte : forall m m' S c mp p n i, app_mem (S - 128) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> addressable m p n -> 0 <= i < n ->
  munch [(S - 128, S); (c, c + 25); (mp, mp + 40)] m m' ->
  exists k, mrd rsegs m' (wa ((p + i) / 8 + 2147450880)) = Some k /\ shadow_ok (p + i) (bv_signed k).
Proof.
  intros m m' S c mp p n i A1 A2 AC AM (P0 & N0 & PE & AB) Hi MU.
  destruct (AB i Hi) as (Ax & k & MK & SK). exists k. split; [|exact SK].
  unfold shadow_addr, ASAN_K in MK. unfold mrd in *. rewrite MU; [exact MK|].
  rewrite wa_unsigned by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ax; Z.div_mod_to_equations; lia).
  exact (ms_sh_out m S c mp _ A1 A2 AC AM Ax).
Qed.

(* The shadow byte of the granule of p + j is 0 when the 8 bytes from p + j lie in [p, p + n). *)
Lemma ms_sh_gran : forall m m' S c mp p n j, app_mem (S - 128) -> app_mem (S - 1) ->
  addressable m c 25 -> addressable m mp 40 -> addressable m p n -> 0 <= j -> j + 8 <= n ->
  munch [(S - 128, S); (c, c + 25); (mp, mp + 40)] m m' ->
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
  (ra gp tp t0 t1 t2 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z).
Hypothesis FIN : mn_fin_F.
Hypothesis E0 : at8 bb pos = 240.
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

Local Abbreviation W := [(bv_unsigned sp0 - 128, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)].
Local Abbreviation L := (Z.of_nat (length bb)).
Local Abbreviation Q := (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m c mp body bb mj pos st).
(* the frame words *)
Local Abbreviation FRC := [C8 (Z_to_bv 64 (mp + 3)); C8 (Z_to_bv 64 ((mp + 3) / 8 + 2147450880)); C8 (Z_to_bv 64 (c + 16));
  C8 x27; C8 x26; C8 x25; C8 x24; C8 x23; C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 ra0].
(* the cursor at 0x82210 *)
Local Abbreviation CUR0 := [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 (Z.of_nat pos)); C1 (b8 st)].
(* the message at 0x82210 *)
Local Abbreviation MC0 := [C1 (nth 0 mj (b8 0)); C1 (nth 1 mj (b8 0)); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].
Hypothesis FRm : rw_cells rsegs m (bv_unsigned sp0 - 128) FRC.
Hypothesis CCm : rw_cells rsegs m c CUR0.
Hypothesis CMm : rw_cells rsegs m mp MC0.
Hypothesis BBm : bytes_at rsegs m body bb.

(* the state: a0 - a6 vary, the other registers are those of mn_sys_F *)
Local Abbreviation ST pc x10 x11 x12 x13 x14 x15 x16 mm :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 128)) gp tp t0 t1 t2
           (Z_to_bv 64 ((mp + 2) / 8 + 2147450880)) (Z_to_bv 64 mp) x10 x11 x12 x13 x14 x15 x16 a7
           (Z_to_bv 64 c) (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) (Z_to_bv 64 (body + Z.of_nat pos))
           (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 ((c + 16) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 L) (Z_to_bv 64 (at8 bb pos)) (Z_to_bv 64 body) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* 0x82528: the epilogue, by mn_fin_F; s2, s5 and s9 are what the found path left in them *)
Lemma ms_fin_at : forall (x10 x11 x12 x13 x14 x15 x16 y18 y21 y25 : word) (mm : word -> option byte),
  x10 = Z_to_bv 64 (mr_code (msg_step bb pos st)) ->
  munch W m mm -> rw_cells rsegs mm (bv_unsigned sp0 - 128) FRC ->
  rw_cells rsegs mm c (PCur.cursor_cells body L (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))) ->
  rw_cells rsegs mm mp (PMsg.msg_cells body mj (msg_step bb pos st)) ->
  evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 128)) gp tp t0 t1 t2
             (Z_to_bv 64 ((mp + 2) / 8 + 2147450880)) (Z_to_bv 64 mp) x10 x11 x12 x13 x14 x15 x16 a7
             y18 (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) y21
             (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 ((c + 16) / 8 + 2147450880)) (Z_to_bv 64 2147450880)
             y25 (Z_to_bv 64 (at8 bb pos)) (Z_to_bv 64 body) t3 t4 t5 t6)
        F (Z_to_bv 64 0x8ce38) fc None mm (seg_rom rsegs)).
Proof.
  intros x10 x11 x12 x13 x14 x15 x16 y18 y21 y25 mm -> MU FRz CCz CMz.
  eapply FIN.
  - unfold MN_FRAME. lia.
  - unfold MN_FRAME. exact RFR.
  - unfold mn_fr, MN_FRAME. exact FRz.
  - unfold MN_FRAME. exact MU.
  - exact CCz.
  - exact CMz.
Qed.

(* 0x82294: the search ran to the end of the body, no 0xf7. c->status := 0, c->pos := len, a0 = -6. *)
Lemma ms_cut_at : forall (x10 x11 x12 x13 x14 x15 x16 : word),
  (forall q, (pos < q < length bb)%nat -> at8 bb q <> 247) ->
  evtF rsegs RNG Q (ST 0x8cba4 x10 x11 x12 x13 x14 x15 x16 m).
Proof.
  intros x10 x11 x12 x13 x14 x15 x16 Hnf.
  assert (RS : msg_step bb pos st = mr_plain MkSysexCut pos (length bb) 0 0).
  { unfold msg_step.
    replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    replace (at8 bb pos =? 0xf0) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite (find_f7_none_intro (skipn (S pos) bb)); [reflexivity|].
    intros q Hq. rewrite length_skipn in Hq. rewrite ms_at8_skipn. apply Hnf. lia. }
  pose proof (munch_refl W m) as MU.
  (* 0x82294 addi a0,s2,24; 0x82298 srli; 0x8229c add; 0x822a0 lb: the shadow byte of c + 24 *)
  step. step. rewrite (ms_srl3 (c + 24)) by lia.
  step.
  destruct (ms_sh_byte _ _ (bv_unsigned sp0) c mp c 25 24 AP1 AP2 ADc ADm ADc ltac:(lia) MU) as (k0 & MK & SK0).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (ms_rng_sh RNG c 25 (c + 24) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x822a4 bnez a1; 0x825a8 andi a2,a0,7; 0x825ac blt a2,a1 *)
  step. ms_chk1 12 (c + 24) k0 SK0 2%nat.
  (* 0x822a8 sb zero,0(a0): c->status := 0; 0x822ac li a0,-6; 0x822b0 j 0x8234c *)
  step. step. step.
  (* 0x8234c lbu a1,0(s7); 0x82350 ld a2,16(sp); 0x82354 bnez a1: the granule of c + 16 *)
  pose proof (ms_sh_gran _ _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH G.
  step.
  step. if_false.
  (* 0x82358 sd s9,0(a2): c->pos := len; 0x8235c j 0x82528 *)
  step. step.
  eapply ms_fin_at;
    [ rewrite RS; reflexivity | exact MU | exact FRm | rewrite RS; exact CCm | rewrite RS; exact CMm ].
Qed.

(* 0x822b4: body[pos + 1 + j] is the first 0xf7 after pos. m->status := 0xf0, m->running := 0,
   m->sysex := body + pos + 1, m->sysex_len := j, m->len := j + 2, c->pos := pos + j + 2, c->status := 0, a0 = 1. *)
Lemma ms_found_at : forall (j : nat) (x10 x11 x12 x13 x14 x15 x16 : word),
  (S pos + j < length bb)%nat -> at8 bb (S pos + j) = 247 ->
  (forall q, (pos < q < S pos + j)%nat -> at8 bb q <> 247) ->
  x10 = Z_to_bv 64 (mp + 16) -> x12 = Z_to_bv 64 (Z.of_nat (j + 2)) ->
  evtF rsegs RNG Q (ST 0x8cbc4 x10 x11 x12 x13 x14 x15 x16 m).
Proof.
  intros j x10 x11 x12 x13 x14 x15 x16 Hj F7 Hnf -> ->.
  assert (RS : msg_step bb pos st = MsgRes MkSysex pos (pos + j + 2) 0 240 0 0 0 (S pos) j (j + 2)).
  { unfold msg_step.
    replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    replace (at8 bb pos =? 0xf0) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite (find_f7_intro (skipn (S pos) bb) j); [reflexivity | | |].
    - rewrite length_skipn. lia.
    - rewrite ms_at8_skipn. exact F7.
    - intros q Hq. rewrite ms_at8_skipn. apply Hnf. lia. }
  pose proof (munch_refl W m) as MU.
  (* 0x822b4 addi s2,s2,24; 0x822b8 srli; 0x822bc add; 0x822c0 lb: the shadow byte of c + 24 *)
  step. step. rewrite (ms_srl3 (c + 24)) by lia.
  step.
  destruct (ms_sh_byte _ _ (bv_unsigned sp0) c mp c 25 24 AP1 AP2 ADc ADm ADc ltac:(lia) MU) as (k0 & MK & SK0).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (ms_rng_sh RNG c 25 (c + 24) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x822c4 bnez a1; 0x825b4 andi a3,s2,7; 0x825b8 blt a3,a1 *)
  step. ms_chk1 13 (c + 24) k0 SK0 2%nat.
  (* 0x822c8 sb zero,0(s2): c->status := 0 *)
  step.
  (* 0x822cc srli; 0x822d0 add; 0x822d4 lb: the shadow byte of mp *)
  step. rewrite (ms_srl3 mp) by lia.
  step.
  destruct (ms_sh_byte _ _ (bv_unsigned sp0) c mp mp 40 0 AP1 AP2 ADc ADm ADm ltac:(lia) MU) as (k1 & MK & SK1).
  rewrite Z.add_0_r in MK, SK1.
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (ms_rng_sh RNG mp 40 mp ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x822d8 bnez a1; 0x825c4 andi a3,s1,7; 0x825c8 blt a3,a1 *)
  step. ms_chk1 13 mp k1 SK1 2%nat.
  (* 0x822dc li a3,-16; 0x822e0 addi a1,s1,1; 0x822e4 sb a3,0(s1): m->status := 0xf0 *)
  step. step. step.
  rewrite ms_m16 in CMm.
  (* 0x822e8 srli; 0x822ec add; 0x822f0 lb: the shadow byte of mp + 1 *)
  step. rewrite (ms_srl3 (mp + 1)) by lia.
  step.
  destruct (ms_sh_byte _ _ (bv_unsigned sp0) c mp mp 40 1 AP1 AP2 ADc ADm ADm ltac:(lia) MU) as (k2 & MK & SK2).
  pose proof (rd1 _ _ _ MK) as HR.
  pose proof (ms_rng_sh RNG mp 40 (mp + 1) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH MK.
  (* 0x822f4 bnez a3; 0x825d4 andi a4,a1,7; 0x825d8 blt a4,a3 *)
  step. ms_chk1 14 (mp + 1) k2 SK2 2%nat.
  (* 0x822f8 sb zero,0(a1): m->running := 0 *)
  step.
  (* 0x822fc srli; 0x82300 add; 0x82304 lbu; 0x82308 bnez: the granule of mp + 8 *)
  step. rewrite (ms_srl3 (mp + 8)) by lia.
  step.
  pose proof (ms_sh_gran _ _ (bv_unsigned sp0) c mp mp 40 8 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG mp 40 (mp + 8) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x8230c addi s5,s5,1; 0x82310 sd s5,0(s6): m->sysex := body + pos + 1 *)
  step.
  replace (Z_to_bv 64 (body + Z.of_nat pos + 1)) with (Z_to_bv 64 (body + Z.of_nat (S pos))) by (f_equal; lia).
  step.
  (* 0x82314 srli; 0x82318 add; 0x8231c lbu; 0x82320 bnez: the granule of mp + 16 *)
  step. rewrite (ms_srl3 (mp + 16)) by lia.
  step.
  pose proof (ms_sh_gran _ _ (bv_unsigned sp0) c mp mp 40 16 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG mp 40 (mp + 16) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x82324 addi a0,a2,-2; 0x82328 sd a0,16(s1): m->sysex_len := j *)
  step.
  replace (Z_to_bv 64 (Z.of_nat (j + 2) + -2)) with (Z_to_bv 64 (Z.of_nat j)) by (f_equal; lia).
  step.
  (* 0x8232c addi a0,s1,32; 0x82330 srli; 0x82334 add; 0x82338 lbu; 0x8233c bnez: the granule of mp + 32 *)
  step. step. rewrite (ms_srl3 (mp + 32)) by lia.
  step.
  pose proof (ms_sh_gran _ _ (bv_unsigned sp0) c mp mp 40 32 AP1 AP2 ADc ADm ADm ltac:(lia) ltac:(lia) MU) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG mp 40 (mp + 32) ltac:(lia) RSM ltac:(lia)) as RH.
  step. clear HR RH G.
  step. if_false.
  (* 0x82340 add s9,s3,a2; 0x82344 sd a2,0(a0): m->len := j + 2; 0x82348 li a0,1 *)
  step.
  replace (Z_to_bv 64 (Z.of_nat pos + Z.of_nat (j + 2))) with (Z_to_bv 64 (Z.of_nat (pos + j + 2)))
    by (f_equal; lia).
  step. step.
  (* 0x8234c lbu a1,0(s7); 0x82350 ld a2,16(sp); 0x82354 bnez a1: the granule of c + 16 *)
  pose proof (ms_sh_gran _ _ (bv_unsigned sp0) c mp c 25 16 AP1 AP2 ADc ADm ADc ltac:(lia) ltac:(lia) MU) as G.
  pose proof (rd1 _ _ _ G) as HR.
  pose proof (ms_rng_sh RNG c 25 (c + 16) ltac:(lia) RSC ltac:(lia)) as RH.
  step. clear HR RH G.
  step.
  step. if_false.
  (* 0x82358 sd s9,0(a2): c->pos := pos + j + 2; 0x8235c j 0x82528 *)
  step. step.
  eapply ms_fin_at;
    [ rewrite RS; reflexivity | exact MU | exact FRm | rewrite RS; exact CCm | rewrite RS; exact CMm ].
Qed.

(* 0x82220: the search for 0xf7. a2 = k is the index of the next byte relative to pos, a3 = pos - len,
   a4 = 247, a0 = mp + 16; n is the number of bytes left. *)
Lemma ms_loop : forall (n k : nat) (x10 x11 x12 x13 x14 x15 x16 : word),
  (1 <= k)%nat -> (n + pos + k = length bb)%nat ->
  x10 = Z_to_bv 64 (mp + 16) -> x12 = Z_to_bv 64 (Z.of_nat k) ->
  x13 = Z_to_bv 64 (Z.of_nat pos - L) -> x14 = Z_to_bv 64 247 ->
  (forall q, (pos < q < pos + k)%nat -> at8 bb q <> 247) ->
  evtF rsegs RNG Q (ST 0x8cb30 x10 x11 x12 x13 x14 x15 x16 m).
Proof.
  induction n as [|n IH]; intros k x10 x11 x12 x13 x14 x15 x16 Hk Hn -> -> -> -> Hnf.
  - (* pos + k = len: 0x82220 add a1,a3,a2; 0x82224 beqz a1 *)
    step. step.
    rewrite (ms_loop_test (Z.of_nat pos) L (Z.of_nat k)) by lia.
    replace (Z.of_nat pos + Z.of_nat k =? L) with true by (symmetry; apply Z.eqb_eq; lia).
    cbv iota.
    apply ms_cut_at. intros q Hq. apply Hnf. lia.
  - (* pos + k < len *)
    step. step.
    rewrite (ms_loop_test (Z.of_nat pos) L (Z.of_nat k)) by lia.
    replace (Z.of_nat pos + Z.of_nat k =? L) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv iota.
    (* 0x82228 add a1,s5,a2; 0x8222c srli; 0x82230 add; 0x82234 lb: the shadow byte of body + pos + k *)
    step.
    step. rewrite (ms_srl3 (body + Z.of_nat pos + Z.of_nat k)) by lia.
    step.
    pose proof (munch_refl W m) as MU.
    destruct (ms_sh_byte _ _ (bv_unsigned sp0) c mp body L (Z.of_nat pos + Z.of_nat k)
                AP1 AP2 ADc ADm ADb ltac:(lia) MU) as (k1 & MK & SK1).
    replace (body + (Z.of_nat pos + Z.of_nat k)) with (body + Z.of_nat pos + Z.of_nat k) in MK, SK1 by lia.
    pose proof (rd1 _ _ _ MK) as HR.
    pose proof (ms_rng_sh RNG body L (body + Z.of_nat pos + Z.of_nat k) ltac:(lia) RSB ltac:(lia)) as RH.
    step. clear HR RH MK.
    (* 0x82238 bnez a5; 0x8224c andi a6,a1,7; 0x82250 blt a6,a5 *)
    step. ms_chk1 16 (body + Z.of_nat pos + Z.of_nat k) k1 SK1 2%nat.
    (* 0x8223c lbu a1,0(a1): body[pos + k]; 0x82240 addi a2,a2,1; 0x82244 bne a1,a4 *)
    pose proof (ms_rd8 _ body bb (pos + k) (body + Z.of_nat pos + Z.of_nat k) BBm ltac:(lia) ltac:(lia)) as HR.
    pose proof (rng_sub' RNG body L (body + Z.of_nat pos + Z.of_nat k) 1 RB ltac:(lia)) as RH.
    pose proof (ms_at8_range bb (pos + k)) as XR.
    step. clear HR RH.
    step.
    step. rewrite ms_zxb_eqb by lia.
    destruct (Z.eqb_spec (at8 bb (pos + k)) 247) as [EQ|NE]; cbn [negb]; cbv iota.
    + (* 0x82248 j 0x822b4: the 0xf7 at pos + k *)
      step.
      replace (Z_to_bv 64 (Z.of_nat k + 1)) with (Z_to_bv 64 (Z.of_nat (k - 1 + 2))) by (f_equal; lia).
      apply (ms_found_at (k - 1)%nat); try reflexivity.
      * lia.
      * replace (S pos + (k - 1))%nat with (pos + k)%nat by lia. exact EQ.
      * intros q Hq. apply Hnf. lia.
    + (* back to 0x82220 with k + 1 *)
      replace (Z_to_bv 64 (Z.of_nat k + 1)) with (Z_to_bv 64 (Z.of_nat (S k))) by (f_equal; lia).
      apply (IH (S k)); try reflexivity.
      * lia.
      * lia.
      * intros q Hq. destruct (Nat.eq_dec q (pos + k)) as [->|NEq]; [exact NE | apply Hnf; lia].
Qed.

(* 0x82210 *)
Lemma ms_main : forall (x11 x12 x13 x14 x15 x16 : word),
  evtF rsegs RNG Q (ST 0x8cb20 (Z_to_bv 64 240) x11 x12 x13 x14 x15 x16 m).
Proof.
  intros x11 x12 x13 x14 x15 x16.
  (* 0x82210 addi a0,s1,16; 0x82214 sub a3,s3,s9; 0x82218 li a2,1; 0x8221c li a4,247 *)
  step. step. uns. step. step.
  apply (ms_loop (length bb - pos - 1)%nat 1%nat); try reflexivity; try lia; intros q Hq; lia.
Qed.

End MS.

Theorem mn_sys_of_fin : mn_fin_F -> mn_sys_F.
Proof.
  intros FIN. unfold mn_sys_F.
  intros RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    F fc m c mp body bb mj pos st CTX E0.
  destruct CTX as (Hlt & Hst & Hmj & HF & AP1 & AP2 & FR & CC & CM & BB & ADc & ADm & ADb & OSc & OSm & OSb &
                   D1 & D2 & D3 & RFR & RC & RM & RB & RSC & RSM & RSB).
  unfold MN_FRAME, mn_fr, mn_msg0, PCur.cursor_cells, off_stk, shadow_addr, ASAN_K in *.
  assert (Bc : 0 <= c /\ c + 25 <= 0x800000000000) by (destruct ADc as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  assert (Bm : 0 <= mp /\ mp + 40 <= 0x800000000000) by (destruct ADm as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  assert (Bb : 0 <= body /\ body + Z.of_nat (length bb) <= 0x800000000000)
    by (destruct ADb as (H0 & _ & H1 & _); unfold APPMEM_END in H1; lia).
  eapply ms_main; eassumption.
Qed.
