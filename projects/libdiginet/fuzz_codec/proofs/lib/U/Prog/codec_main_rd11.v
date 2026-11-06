(** Segment RD11 of the walk of LLVMFuzzerTestOneInput in the UBSan image: the SYSEX reader of
    fuzz_codec.c:616-620 (k.a and k.b by fuzz_u8, len = fuzz_u8 % 25, fuzz_take of fuzz.h:62-68, and
    memcpy of the taken bytes into k.bytes), from its arm 0x134e8 of the reader switch to run()'s
    switch at 0x14390. The four paths (no, one, two, three or more header bytes left) meet at
    0x13cfc, which [rd11_take] proves once. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  memcpy_c codec_main_inv codec_main_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the record of a SYSEX operation ---- *)

(** The record the reader builds: kind 11, a and b, bytes and n; the rest is the head's. *)
Definition k_sx (i a b : Z) (bs : list byte) (nv : Z) : kcall :=
  mkKcall 11 (repeat (b8 0) 4) (pers_of i) (sdesk i) a b 0 0 bs nv 0
          (repeat (b8 0xa5) 32) (repeat (b8 0xa5) 32) 0 (repeat (b8 0) 24) 0 0 0.

(** The 40 bytes before k.bytes, and the 120 after it. *)
Definition ka (i a b : Z) : list cell :=
  [C4 (Z_to_bv 64 11); CB 4 (repeat (b8 0) 4); C8 (Z_to_bv 64 (pers_of i)); C8 (Z_to_bv 64 (sdesk i));
   C4 (Z_to_bv 64 a); C4 (Z_to_bv 64 b); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Definition kt (nv : Z) : list cell :=
  [C8 (Z_to_bv 64 nv); C4 (Z_to_bv 64 0); CB 32 (repeat (b8 0xa5) 32); CB 32 (repeat (b8 0xa5) 32);
   C4 (Z_to_bv 64 0); CB 24 (repeat (b8 0) 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

Lemma k_sx_split : forall m s i a b bs nv,
  rw_cells rsegs m (s + -384) (kcall_cells (k_sx i a b bs nv)) ->
  rw_cells rsegs m (s + -384) (ka i a b) /\ rw_cells rsegs m (s + -344) [CB 24 bs] /\
  rw_cells rsegs m (s + -320) (kt nv).
Proof.
  intros m s i a b bs nv H.
  change (kcall_cells (k_sx i a b bs nv)) with (ka i a b ++ [CB 24 bs] ++ kt nv) in H.
  apply rw_cells_app_split in H. destruct H as [H1 H].
  apply rw_cells_app_split in H. destruct H as [H2 H3].
  change (Z.of_nat (cells_size (ka i a b))) with 40 in H2, H3.
  change (Z.of_nat (cells_size [CB 24 bs])) with 24 in H3.
  replace (s + -384 + 40) with (s + -344) in H2, H3 by lia.
  replace (s + -344 + 24) with (s + -320) in H3 by lia.
  auto.
Qed.

Lemma k_sx_join : forall m s i a b bs nv,
  rw_cells rsegs m (s + -384) (ka i a b) -> rw_cells rsegs m (s + -344) [CB 24 bs] ->
  rw_cells rsegs m (s + -320) (kt nv) ->
  rw_cells rsegs m (s + -384) (kcall_cells (k_sx i a b bs nv)).
Proof.
  intros m s i a b bs nv H1 H2 H3.
  change (kcall_cells (k_sx i a b bs nv)) with (ka i a b ++ [CB 24 bs] ++ kt nv).
  apply rw_cells_app_join; [exact H1 |].
  change (Z.of_nat (cells_size (ka i a b))) with 40.
  replace (s + -384 + 40) with (s + -344) by lia.
  apply rw_cells_app_join; [exact H2 |].
  change (Z.of_nat (cells_size [CB 24 bs])) with 24.
  replace (s + -344 + 24) with (s + -320) by lia.
  exact H3.
Qed.

(** A byte block from two blocks side by side. *)
Lemma rw_cells_CB_cat : forall m A n bs1 bs2,
  length bs2 = (n - length bs1)%nat -> (length bs1 <= n)%nat ->
  rw_cells rsegs m A [CB (length bs1) bs1] ->
  rw_cells rsegs m (A + Z.of_nat (length bs1)) [CB (n - length bs1) bs2] ->
  rw_cells rsegs m A [CB n (bs1 ++ bs2)].
Proof.
  intros m A n bs1 bs2 H2 Hk R1 R2.
  apply (rw_cells_CB_join m A n (length bs1) (bs1 ++ bs2)); [rewrite length_app; lia | exact Hk | |].
  - rewrite firstn_app_exact. exact R1.
  - rewrite skipn_app_exact. exact R2.
Qed.

Lemma bytes_at_firstn : forall m a bs j, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn j bs).
Proof.
  intros m a bs j H. rewrite <- (firstn_skipn j bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma zb_range : forall l : list byte, Forall (fun x => 0 <= x < 256) (zb l).
Proof.
  intros l. unfold zb. apply Forall_map. apply Forall_forall. intros x _.
  pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma desk_at_sx : forall i a b bs nv, 0 <= i <= 2 -> desk_at (k_sx i a b bs nv).
Proof.
  intros i a b bs nv Hi. unfold desk_at, k_sx. cbn [k_p k_desk].
  assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia; cbn.
  - left; split; reflexivity.
  - right; left; split; reflexivity.
  - right; right; split; reflexivity.
Qed.

Lemma rec_wf_sx : forall i a b bs nv, 0 <= i <= 2 -> 0 <= a < 256 -> 0 <= b < 256 ->
  length bs = 24%nat -> 0 <= nv <= 24 -> rec_wf (k_sx i a b bs nv).
Proof.
  intros i a b bs nv Hi Ha Hb Hl Hn.
  unfold rec_wf. refine (conj _ (conj (desk_at_sx i a b bs nv Hi) _)).
  - cbn. lia.
  - unfold k_sx. cbn [k_kind k_before k_out k_rc k_want_rc k_want_len k_want_key k_want_display
                      k_a k_b k_c k_delta k_bytes k_n].
    do 7 (split; [reflexivity |]).
    unfold reader_ok.
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    split; [unfold zb; rewrite length_map; exact Hl |].
    split; [apply zb_range |].
    split; [lia |]. split; [intros H; discriminate H |]. split; [intros H; discriminate H |].
    intros _. lia.
Qed.

(** ---- the take and the copy: 0x13cfc-0x13d2c ---- *)

(** A region of the frame across memcpy: it is off the n bytes the copy writes. *)
Ltac tp_cells MU WM H :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    apply (rw_cells_transport rsegs W ma mb _ _) in H;
      [ | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I] ]
  end.

(** fuzz_take's end (fuzz.h:67-68) with n in a2, the remaining count in a0 and the cursor in a1,
    the k.n store, memcpy(k.bytes, cursor, n), and the jump to run()'s switch. *)
Lemma rd11_take : forall E n i, env_ok E -> memcpy_contract -> rd_run E n -> 0 <= i <= 2 ->
  forall (ra' t0' t1' t2' w0 w1 w2 a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' x y : word)
         (u0 pj tj plj : list byte) (a b c r nn ops : Z) (m1 : word -> option byte),
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  0 <= a < 256 -> 0 <= b < 256 ->
  bv_unsigned w1 = bv_unsigned (c_p E) + c -> 1 <= c -> c + r = Z.of_nat (length (c_data E)) ->
  bv_unsigned w0 = r -> bv_unsigned w2 = nn -> 0 <= nn <= r -> nn <= 24 ->
  fr E m1 (kcall_cells (k_sx i a b (repeat (b8 0) 24) 0)) x y u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
             w0 w1 w2 a3' a4' a5' a6' a7'
             (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
             (Z_to_bv 64 (pers_of i)) (Z_to_bv 64 ops) s7'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
             (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 0x13cfc) (c_fc E) None m1 (seg_rom rsegs)).
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n i ENV MEMC RUN Hi.
  intros ra' t0' t1' t2' w0 w1 w2 a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' x y u0 pj tj plj a b c r nn ops m1
    HN HOPS Ha Hb HW1 HC1 HCR HW0 HW2 HNR HN24 FR ST MU WM HMI.
  pose proof ENV as ENV0.
  unfold env_ok in ENV. cenv_cbn.
  destruct ENV as (HD & HMI0 & ST0 & HLO & SPA & DJ & HPB & HPNZ & RI & DJR).
  unfold fr in FR. cenv_cbn.
  destruct FR as (HKS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (data_at _ m1 ENV0 MU) as HDAT. cenv_cbn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
  pose proof (bv_unsigned_in_range 64 w0) as Rw0. unfold bv_modulus in Rw0.
  pose proof (bv_unsigned_in_range 64 w1) as Rw1. unfold bv_modulus in Rw1.
  pose proof (bv_unsigned_in_range 64 w2) as Rw2. unfold bv_modulus in Rw2.
  pose proof ST as (Hlo0 & _).
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, Rp, Rw0, Rw1, Rw2.
  assert (Hp1 : 0 < bv_unsigned p) by (apply HPNZ; lia).
  clear HD RI HKS.
  apply k_sx_split in FK. destruct FK as (KA & KB & KT).
  unfold ka in KA. unfold kt in KT.
  zstep. zstep.
  if_cases T0; [ refute_trap T0 | clear T0 ].
  do 4 zstep.
  if_cases T1.
  { exfalso. zify_cond T1.
    replace (0 <? bv_unsigned w1) with true in T1 by (symmetry; apply Z.ltb_lt; lia).
    replace (bv_unsigned w2 + bv_unsigned w1 <? 1) with false in T1 by (symmetry; apply Z.ltb_ge; lia).
    cbn in T1. discriminate T1. }
  clear T1.
  do 6 zstep.
  (* 0x13d28: memcpy(k.bytes, cursor, n) into the first n bytes of k.bytes *)
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -344)) = bv_unsigned sp + -344)
    by (apply unsigned_lit; lia).
  destruct (rw_cells_CB_split _ _ 24 (Z.to_nat nn) (repeat (b8 0) 24) (repeat_length _ _) ltac:(lia) KB)
    as [KB1 KB2].
  clear KB.
  rewrite Z2Nat.id in KB2 by lia.
  set (src := firstn (Z.to_nat nn) (skipn (Z.to_nat c) data)).
  assert (LS : length src = Z.to_nat nn) by (unfold src; rewrite length_firstn, length_skipn; lia).
  eapply evt_cut.
  { eapply MEMC with (src := src) (junk := firstn (Z.to_nat nn) (repeat (b8 0) 24)).
    - rewrite HW1. apply bytes_at_firstn. apply bytes_at_skipn; [exact HDAT | lia].
    - rewrite HW2. exact LS.
    - rewrite U344, HW2. exact KB1.
    - rewrite U344, HW1, HW2. lia.
    - assumption. }
  intros ms' (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m2
              & -> & MU2 & WM2 & MI2 & RB & _).
  fix_ret.
  rewrite U344, HW2 in MU2, RB.
  tp_cells MU2 WM2 F0. tp_cells MU2 WM2 F8. tp_cells MU2 WM2 KA. tp_cells MU2 WM2 KB2.
  tp_cells MU2 WM2 KT. tp_cells MU2 WM2 FIN. tp_cells MU2 WM2 FPD. tp_cells MU2 WM2 FTX.
  tp_cells MU2 WM2 FPL. tp_cells MU2 WM2 FSV.
  lazymatch type of MU2 with munch ?W ?ma ?mb =>
    apply (stk_transport_disjoint rsegs W ma mb _ _) in ST;
      [ | exact MU2 | exact WM2 | cbn [disjoint_from]; split; [lia | exact I] ]
  end.
  assert (MU3 : munch [(bv_unsigned sp - 640, bv_unsigned sp)] m m2).
  { eapply munch_trans; [exact MU |].
    eapply munch_weaken; [ | exact MU2 ].
    intros z Hz. cbn [outside] in *. destruct Hz as [Hz _]. split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
  pose proof (rw_cells_CB_cat m2 (bv_unsigned sp + -344) 24 src (skipn (Z.to_nat nn) (repeat (b8 0) 24))) as KBN.
  rewrite LS, Z2Nat.id in KBN by lia.
  specialize (KBN ltac:(rewrite length_skipn, repeat_length; lia) ltac:(lia) RB KB2).
  replace w2 with (Z_to_bv 64 nn) in KT by (rewrite <- HW2; apply Z_to_bv_bv_unsigned).
  pose proof (k_sx_join m2 (bv_unsigned sp) i a b _ nn KA KBN KT) as FKN.
  (* 0x13d2c: j 0x14390, run()'s switch *)
  zstep.
  pose proof (rec_wf_sx i a b (src ++ skipn (Z.to_nat nn) (repeat (b8 0) 24)) nn Hi Ha Hb
                ltac:(rewrite length_app, length_skipn, repeat_length, LS; lia) ltac:(lia)) as WF.
  specialize (RUN _ WF). unfold rec_ok in RUN. cenv_cbn.
  eapply RUN with (c := c + nn) (cur := Z_to_bv 64 (bv_unsigned w2 + bv_unsigned w1))
                  (rem := Z_to_bv 64 (bv_unsigned w0 - bv_unsigned w2)) (ops := ops).
  all: first [ exact WF
             | lia
             | (rewrite unsigned_lit by lia; lia)
             | (unfold fr; cenv_cbn;
                exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FKN (conj FIN (conj FPD
                         (conj FTX (conj FPL FSV)))))))))
             | eassumption ].
Qed.

(** ---- the reader: 0x134e8-0x13584, 0x13ce0-0x13cf8, 0x14b24-0x14b30 ---- *)

(** An identity of byte values, checked on all 256 of them. *)
Lemma z256 : forall (f g : Z -> Z), zall (fun x => f x =? g x) 0 256 = true ->
  forall x, 0 <= x < 256 -> f x = g x.
Proof. intros f g H x Hx. apply Z.eqb_eq. exact (zall_spec _ 256 0 H x ltac:(lia)). Qed.

(** The side goals of [rd11_take] at a join: arithmetic, the frame, and the memory facts. *)
Ltac take_side F0 F8 FK FIN FPD FTX FPL FSV :=
  first [ lia
        | (rewrite unsigned_lit by lia; lia)
        | (unfold fr; cenv_cbn;
           exact (conj eq_refl (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))))
        | eassumption ].

Lemma codec_main_rd11 : seg_rd11_stmt.
Proof.
  unfold seg_rd11_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV MEMC RUN i Hi.
  unfold rd_ok. cenv_cbn.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ HN HOPS HCUR HC1 HCN FR ST MU WM HMI.
  pose proof ENV as ENV0.
  unfold env_ok in ENV. cenv_cbn.
  destruct ENV as (HD & HMI0 & ST0 & HLO & SPA & DJ & HPB & HPNZ & RI & DJR).
  unfold fr in FR. cenv_cbn.
  destruct FR as (HKS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (data_at _ m1 ENV0 MU) as HDAT. cenv_cbn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
  pose proof (bv_unsigned_in_range 64 rem) as Rrem. unfold bv_modulus in Rrem.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur. unfold bv_modulus in Rcur.
  pose proof ST as (Hlo0 & _).
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, Rp, Rrem, Rcur.
  assert (Hp1 : 0 < bv_unsigned p) by (apply HPNZ; lia).
  clear HD RI HKS.
  unfold kcall_cells, k_head in FK.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out
       k_want_rc k_want k_want_len k_want_key k_want_display] in FK.
  pose proof (rd11_take _ n i ENV0 MEMC RUN Hi) as TAKE. clear RUN MEMC.
  cbn [c_ra c_sp c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10
       c_s11 c_p c_F c_fc c_m c_lo c_data] in TAKE.
  change (pc_rd 11) with 79080.
  (* 0x134e8-0x134ec: in.n = 0? *)
  zstep. zstep.
  if_cases B0.
  - (* no byte left: a = b = 0, n = 0 (0x13ce0-0x13cf8, the never-taken 0x13cf4) *)
    zify_cond B0.
    do 5 zstep.
    zstep. if_false.
    zstep.
    eapply TAKE with (c := c) (r := 0) (nn := 0) (a := 0) (b := 0).
    all: take_side F0 F8 FK FIN FPD FTX FPL FSV.
  - zify_cond B0.
    (* 0x134f0-0x13510: a = fuzz_u8; the trap edge needs cur + 1 <=u 1 *)
    do 5 zstep.
    if_cases T1; [ | refute_trap T1 ].
    zstep.
    match goal with H : bytes_at rsegs ?mm (bv_unsigned p) data |- _ =>
      assert (HB0 : ov_read_bytes rsegs mm cur 1 = Some [nth (Z.to_nat c) data (Z_to_bv 8 0)])
      by (rewrite <- (Z_to_bv_bv_unsigned cur), HCUR; apply (bytes_at_byte mm (bv_unsigned p) data c); [exact H | lia]) end.
    zstep. clear HB0.
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat c) data (Z_to_bv 8 0))) as Rb0.
    change (bv_modulus 8) with 256 in Rb0.
    zstep. zstep.
    if_cases B1.
    + (* one byte: b = 0, n = 0 (0x13ce8-0x13cf8) *)
      zify_cond B1.
      do 3 zstep.
      zstep. if_false.
      zstep.
      eapply TAKE with (c := c + 1) (r := 0) (nn := 0)
                       (a := bv_unsigned (nth (Z.to_nat c) data (Z_to_bv 8 0))) (b := 0).
      all: take_side F0 F8 FK FIN FPD FTX FPL FSV.
    + zify_cond B1.
      (* 0x13518-0x13538: b = fuzz_u8 *)
      do 4 zstep.
      if_cases T2; [ | refute_trap T2 ].
      zstep. zstep.
      match goal with H : bytes_at rsegs ?mm (bv_unsigned p) data |- _ =>
        assert (HB1 : ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned cur + 1)) 1
                      = Some [nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0)])
        by (rewrite HCUR; replace (bv_unsigned p + c + 1) with (bv_unsigned p + (c + 1)) by lia;
            apply (bytes_at_byte mm (bv_unsigned p) data (c + 1)); [exact H | lia]) end.
      zstep. clear HB1.
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0))) as Rb1.
      change (bv_modulus 8) with 256 in Rb1.
      zstep. zstep.
      if_cases B2.
      * zify_cond B2.
        (* 0x13544-0x1357c: len = fuzz_u8 % 25 by the magic multiply *)
        do 4 zstep.
        if_cases T3; [ | refute_trap T3 ].
        zstep. zstep.
        match goal with H : bytes_at rsegs ?mm (bv_unsigned p) data |- _ =>
          assert (HB2 : ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned cur + 2)) 1
                        = Some [nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0)])
          by (rewrite HCUR; replace (bv_unsigned p + c + 2) with (bv_unsigned p + (c + 2)) by lia;
              apply (bytes_at_byte mm (bv_unsigned p) data (c + 2)); [exact H | lia]) end.
        zstep. clear HB2.
        pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0))) as Rb2.
        change (bv_modulus 8) with 256 in Rb2.
        do 7 zstep.
        remember (bv_unsigned (nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0))) as L eqn:EL.
        match goal with |- context [Z_to_bv 64 (Z.land ?e 255)] =>
          let f := eval pattern L in (Z.land e 255) in
          lazymatch f with
          | ?g L => replace (Z.land e 255) with (L mod 25)
                      by (symmetry; apply (z256 g (fun x => x mod 25)); [vm_compute; reflexivity | exact Rb2])
          end
        end.
        pose proof (Z.mod_pos_bound L 25 ltac:(lia)) as Hlen.
        remember (L mod 25) as len eqn:Elen. clear Elen EL.
        (* 0x13580: n = min(len, in.n) *)
        zstep.
        if_cases B3.
        -- (* len >= in.n: n = in.n through 0x13cf8 *)
           zify_cond B3.
           zstep.
           eapply TAKE with (c := c + 3) (r := bv_unsigned rem - 3) (nn := bv_unsigned rem - 3)
                            (a := bv_unsigned (nth (Z.to_nat c) data (Z_to_bv 8 0)))
                            (b := bv_unsigned (nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0))).
           all: take_side F0 F8 FK FIN FPD FTX FPL FSV.
        -- (* len < in.n: n = len, straight to 0x13cfc *)
           zify_cond B3.
           zstep.
           eapply TAKE with (c := c + 3) (r := bv_unsigned rem - 3) (nn := len)
                            (a := bv_unsigned (nth (Z.to_nat c) data (Z_to_bv 8 0)))
                            (b := bv_unsigned (nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0))).
           all: take_side F0 F8 FK FIN FPD FTX FPL FSV.
      * zify_cond B2.
        (* two bytes: n = 0 through 0x14b24-0x14b2c, the always-taken 0x14b2c *)
        do 3 zstep.
        zstep. if_true.
        zstep.
        eapply TAKE with (c := c + 2) (r := 0) (nn := 0)
                         (a := bv_unsigned (nth (Z.to_nat c) data (Z_to_bv 8 0)))
                         (b := bv_unsigned (nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0))).
        all: take_side F0 F8 FK FIN FPD FTX FPL FSV.
Qed.
