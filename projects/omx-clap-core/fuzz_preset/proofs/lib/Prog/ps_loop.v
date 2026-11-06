From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ReaderRes parse_string_loops ps_seg_turn ps_seg_utail put_utf8_c ps_seg_putback.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PsDecStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require hex4_c.
Import ListNotations.
Open Scope Z_scope.

Lemma pslp_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma pslp_zb1 : forall z, 0 <= z < 256 -> zb [Z_to_bv 8 z] = [z].
Proof. intros z H. unfold zb. cbn [map]. rewrite pslp_u8 by exact H. reflexivity. Qed.

Lemma pslp_zb_app : forall a b : list byte, zb (a ++ b) = zb a ++ zb b.
Proof. intros a b. unfold zb. apply map_app. Qed.

Lemma pslp_utf8 : forall cp, 0 <= cp <= 0x10FFFF -> zb (put_utf8_c.utf8 cp) = PjGrammar.utf8 cp.
Proof.
  intros cp H. unfold put_utf8_c.utf8, PjGrammar.utf8, zb.
  destruct (Z.ltb_spec cp 128); [|destruct (Z.ltb_spec cp 2048); [|destruct (Z.ltb_spec cp 65536)]];
    cbn [map]; rewrite ?pslp_u8 by (Z.div_mod_to_equations; lia); reflexivity.
Qed.

Lemma pslp_utf8_len : forall cp, (length (put_utf8_c.utf8 cp) <= 4)%nat.
Proof.
  intros cp. unfold put_utf8_c.utf8.
  destruct (cp <? 128); [|destruct (cp <? 2048); [|destruct (cp <? 65536)]]; cbn [length]; lia.
Qed.

Lemma pslp_esc_rng : forall e b, pst_esc e = Some b -> 0 <= b < 256.
Proof.
  intros e b H. unfold pst_esc in H.
  repeat match type of H with (if ?t then _ else _) = _ => destruct t end;
    try discriminate H; injection H as <-; lia.
Qed.

Lemma pslp_lo_rng : forall bs lo, ps_lo bs = Some lo -> 0xDC00 <= lo <= 0xDFFF.
Proof.
  intros bs lo H. unfold ps_lo in H.
  destruct bs as [|b0 [|b1 hs]]; cbv beta iota in H; try discriminate H.
  destruct ((bv_unsigned b0 =? 92) && (bv_unsigned b1 =? 117)); [|discriminate H].
  destruct (hex4_c.hex4 hs) as [v|]; [|discriminate H].
  destruct (0xDC00 <=? v) eqn:E1; destruct (v <=? 0xDFFF) eqn:E2; cbn [andb] in H; try discriminate H.
  injection H as <-. apply Z.leb_le in E1, E2. lia.
Qed.

Lemma pslp_cp : forall h bs cp k, 0 <= h < 65536 -> ps_cp h bs = Some (cp, k) ->
  0 < cp <= 0x10FFFF /\ (k = 6 \/ k = 12 /\ exists lo, ps_lo bs = Some lo).
Proof.
  intros h bs cp k Hh H. unfold ps_cp in H.
  destruct (h =? 0) eqn:E0; [discriminate H|]. apply Z.eqb_neq in E0.
  destruct (0xD800 <=? h) eqn:E1; destruct (h <? 0xDC00) eqn:E2; cbn [andb] in H.
  { destruct (ps_lo bs) as [lo|] eqn:El; [|discriminate H].
    injection H as <- <-. pose proof (pslp_lo_rng _ _ El) as Hl.
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    split; [lia|]. right. split; [reflexivity|]. exists lo. reflexivity. }
  all: destruct ((0xDC00 <=? h) && (h <? 0xE000)); [discriminate H|];
    injection H as <- <-; split; [lia | left; reflexivity].
Qed.

Lemma pslp_lt : forall tb text len x q, Z.of_nat (length tb) = len -> text <= x ->
  scan (rest_at tb text x) = Some q -> x < text + len.
Proof.
  intros tb text len x q HL Hx H. destruct (Z_lt_le_dec x (text + len)) as [L|L]; [exact L|].
  rewrite (psl_rest_end tb text x) in H by lia. cbn in H. discriminate H.
Qed.

Lemma pslp_rest_skip : forall tb text P j, text <= P -> 0 <= j ->
  rest_at tb text (P + j) = skipn (Z.to_nat j) (rest_at tb text P).
Proof.
  intros tb text P j HP Hj. unfold rest_at, zb. rewrite skipn_map, skipn_skipn.
  replace (Z.to_nat (P + j - text)) with (Z.to_nat j + Z.to_nat (P - text))%nat by lia. reflexivity.
Qed.

Lemma pslp_rest_len : forall tb text len x, Z.of_nat (length tb) = len -> text <= x <= text + len ->
  Z.of_nat (length (rest_at tb text x)) = text + len - x.
Proof. intros tb text len x HL Hx. unfold rest_at, zb. rewrite length_map, length_skipn. lia. Qed.

Lemma pslp_wr_sub : forall m a n b k, wr_at rsegs m a n -> a <= b -> 0 <= k -> b + k <= a + n -> wr_at rsegs m b k.
Proof.
  intros m a n b k (Ha & Hn & H) Hb Hk Hbk. split; [lia|]. split; [lia|].
  intros i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply H. lia.
Qed.

Lemma pslp_push1 : forall m O0 ws x, bytes_at rsegs m O0 ws -> 0 <= O0 -> O0 + Z.of_nat (length ws) + 1 <= 2 ^ 64 ->
  bytes_at rsegs (write_to_mem m (wa (O0 + Z.of_nat (length ws))) [x]) O0 (ws ++ [x]).
Proof.
  intros m O0 ws x HB H0 H1. apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia | lia].
  - apply bytes_at_write_same; [lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia].
Qed.

Lemma pslp_scan_u : forall tb text P h cp k q,
  text <= P -> 0 <= h < 65536 ->
  rest_at tb text P = 92 :: 117 :: rest_at tb text (P + 2) ->
  hex4_c.hex4 (skipn (Z.to_nat (P + 2 - text)) tb) = Some h ->
  ps_cp h (skipn (Z.to_nat (P + 6 - text)) tb) = Some (cp, k) ->
  scan (rest_at tb text P) = Some q ->
  6 <= k /\ (Z.to_nat k <= q)%nat /\ scan (rest_at tb text (P + k)) = Some (q - Z.to_nat k)%nat.
Proof.
  intros tb text P h cp k q HP Hh RP Hx Hc Hs.
  rewrite <- psd_hex4 in Hx.
  change (zb (skipn (Z.to_nat (P + 2 - text)) tb)) with (rest_at tb text (P + 2)) in Hx.
  destruct (hex4_some _ _ Hx) as (d0 & d1 & d2 & d3 & r & Er & N0 & B0 & N1 & B1 & N2 & B2 & N3 & B3 & _).
  assert (E6 : rest_at tb text (P + 6) = r).
  { replace (P + 6) with (P + 2 + 4) by lia. rewrite (pslp_rest_skip tb text (P + 2) 4) by lia. rewrite Er. reflexivity. }
  rewrite RP, Er, scan_bs in Hs.
  rewrite (scan_ndq d0), (scan_ndq d1), (scan_ndq d2), (scan_ndq d3) in Hs by assumption.
  destruct (scan r) as [q6|] eqn:E6s; cbn [option_map] in Hs; [|discriminate Hs]. injection Hs as Hq.
  destruct (pslp_cp h _ cp k Hh Hc) as (_ & [-> | (-> & lo & Hlo)]).
  - rewrite E6, E6s. split; [lia|]. split; [lia|]. f_equal. lia.
  - rewrite <- psd_low in Hlo.
    change (zb (skipn (Z.to_nat (P + 6 - text)) tb)) with (rest_at tb text (P + 6)) in Hlo. rewrite E6 in Hlo.
    destruct (low_some _ _ Hlo) as (e0 & e1 & e2 & e3 & r' & Er' & M0 & C0 & M1 & C1 & M2 & C2 & M3 & C3 & _).
    rewrite Er', scan_bs in E6s.
    rewrite (scan_ndq e0), (scan_ndq e1), (scan_ndq e2), (scan_ndq e3) in E6s by assumption.
    destruct (scan r') as [q12|] eqn:E12; cbn [option_map] in E6s; [|discriminate E6s]. injection E6s as Hq6.
    assert (E12' : rest_at tb text (P + 12) = r').
    { replace (P + 12) with (P + 6 + 6) by lia. rewrite (pslp_rest_skip tb text (P + 6) 6) by lia.
      rewrite E6, Er'. reflexivity. }
    rewrite E12', E12. split; [lia|]. split; [lia|]. f_equal. lia.
Qed.

Definition ps_head (sp gp tp s1 a1 a2 a3 s10 : word) (F : bvmap 5 word) (fc : bv 32) (st text len O P : Z)
    (m : word -> option byte) : machine_state :=
  MS (mkR (Z_to_bv 64 117) sp gp tp (Z_to_bv 64 113) (Z_to_bv 64 102) (Z_to_bv 64 12) (Z_to_bv 64 st) s1
          (Z_to_bv 64 (text + len)) a1 a2 a3 (Z_to_bv 64 91) (Z_to_bv 64 47) (Z_to_bv 64 98) (Z_to_bv 64 8)
          (Z_to_bv 64 O) (Z_to_bv 64 9) (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 92) (Z_to_bv 64 101)
          (Z_to_bv 64 P) (Z_to_bv 64 10) s10 (Z_to_bv 64 6) (Z_to_bv 64 110) (Z_to_bv 64 114) (Z_to_bv 64 13)
          (Z_to_bv 64 116))
     F (Z_to_bv 64 0x166ec) fc None m (seg_rom rsegs).

Definition ps_inv (tb : list byte) (text len s : Z) (Q : nat) (st S O0 : Z) (m0 : word -> option byte)
    (P O : Z) (m : word -> option byte) : Prop :=
  Z.of_nat (length tb) = len /\ text + len < 2 ^ 62 /\ text <= s /\
  bytes_at rsegs m0 text tb /\
  bytes_at rsegs m0 (st + 8) (le8 (Z_to_bv 64 (text + len))) /\
  bytes_at rsegs m0 (S + 8) (le8 (Z_to_bv 64 0xFFFFFFFFFCA02400)) /\
  bytes_at rsegs m0 (S + 16) (le8 (Z_to_bv 64 0xDC00)) /\
  bytes_at rsegs m0 (S + 24) (le8 (Z_to_bv 64 0xD800)) /\
  wr_at rsegs m0 O0 (Z.of_nat Q + 1) /\ wr_at rsegs m0 (S + 36) 4 /\
  0 < O0 /\ 0 <= S /\ S mod 4 = 0 /\
  (O0 + Z.of_nat Q + 1 <= text \/ text + len <= O0) /\
  (S + 40 <= text \/ text + len <= S + 36) /\
  (O0 + Z.of_nat Q + 1 <= st + 8 \/ st + 16 <= O0) /\
  (S + 40 <= st + 8 \/ st + 16 <= S + 36) /\
  (O0 + Z.of_nat Q + 1 <= S + 8 \/ S + 40 <= O0) /\
  s <= P <= s + Z.of_nat Q /\
  scan (rest_at tb text P) = Some (Z.to_nat (s + Z.of_nat Q - P)) /\
  munch [(O0, O0 + Z.of_nat Q + 1); (S + 36, S + 40)] m0 m /\ wmono rsegs m0 m /\
  exists ws : list byte, bytes_at rsegs m O0 ws /\ O = O0 + Z.of_nat (length ws) /\ Z.of_nat (length ws) <= P - s /\
    decode (rest_at tb text s) = emit (zb ws) (decode (rest_at tb text P)).

Definition ps_post (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (tb : list byte) (text len s : Z) (Q : nat)
    (st S O0 : Z) (m0 : word -> option byte) (ms' : machine_state) : Prop :=
  (exists (a2' a3' s10' : word) (ws : list byte) (m' : word -> option byte),
     ms' = MS (mkR (Z_to_bv 64 117) sp gp tp (Z_to_bv 64 113) (Z_to_bv 64 102) (Z_to_bv 64 12) (Z_to_bv 64 st) s1
                   (Z_to_bv 64 (text + len)) (Z_to_bv 64 34) a2' a3' (Z_to_bv 64 91) (Z_to_bv 64 47) (Z_to_bv 64 98)
                   (Z_to_bv 64 8) (Z_to_bv 64 (O0 + Z.of_nat (length ws))) (Z_to_bv 64 9) (Z_to_bv 64 34)
                   (Z_to_bv 64 32) (Z_to_bv 64 92) (Z_to_bv 64 101) (Z_to_bv 64 (s + Z.of_nat Q)) (Z_to_bv 64 10)
                   s10' (Z_to_bv 64 6) (Z_to_bv 64 110) (Z_to_bv 64 114) (Z_to_bv 64 13) (Z_to_bv 64 116))
              F (Z_to_bv 64 0x1691c) fc None m' (seg_rom rsegs) /\
     decode (rest_at tb text s) = Some (zb ws, rest_at tb text (s + Z.of_nat Q + 1)) /\
     (length ws <= Q)%nat /\ bytes_at rsegs m' O0 ws /\
     munch [(O0, O0 + Z.of_nat Q + 1); (S + 36, S + 40)] m0 m' /\ wmono rsegs m0 m')
  \/
  (exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s8' s10' t3' t4' t5' t6' : word)
          (m' : word -> option byte),
     ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 st) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3'
                   (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 92) (Z_to_bv 64 101) s8' (Z_to_bv 64 10) s10'
                   (Z_to_bv 64 6) t3' t4' t5' t6')
              F (Z_to_bv 64 0x168d0) fc None m' (seg_rom rsegs) /\
     decode (rest_at tb text s) = None /\
     munch [(O0, O0 + Z.of_nat Q + 1); (S + 36, S + 40)] m0 m' /\ wmono rsegs m0 m').

Lemma ps_inv_step : forall tb text len s Q st S O0 m0 P O m P' O' m' ws',
  ps_inv tb text len s Q st S O0 m0 P O m -> s <= P' <= s + Z.of_nat Q ->
  scan (rest_at tb text P') = Some (Z.to_nat (s + Z.of_nat Q - P')) ->
  munch [(O0, O0 + Z.of_nat Q + 1); (S + 36, S + 40)] m0 m' -> wmono rsegs m0 m' ->
  bytes_at rsegs m' O0 ws' -> O' = O0 + Z.of_nat (length ws') -> Z.of_nat (length ws') <= P' - s ->
  decode (rest_at tb text s) = emit (zb ws') (decode (rest_at tb text P')) ->
  ps_inv tb text len s Q st S O0 m0 P' O' m'.
Proof.
  intros tb text len s Q st S O0 m0 P O m P' O' m' ws' HI H1 H2 H3 H4 H5 H6 H7 H8.
  destruct HI as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & _).
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11
    (conj A12 (conj A13 (conj A14 (conj A15 (conj A16 (conj A17 (conj A18 (conj H1 (conj H2 (conj H3 (conj H4
    (ex_intro _ ws' (conj H5 (conj H6 (conj H7 H8)))))))))))))))))))))))))).
Qed.

Local Ltac dj := cbn [disjoint_from]; rewrite ?length_le8; repeat split; lia.

Local Ltac fail_post M :=
  apply evt_done; cbv beta; left; unfold ps_post; right; do 20 eexists; exists M; split; [reflexivity|].

Lemma ps_step : forall (sp gp tp s1 a1 a2 a3 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (tb : list byte) (text len s st S O0 P O : Z) (Q : nat),
  put_utf8_contract -> hex4_c.hex4_contract -> sp = Z_to_bv 64 S ->
  ps_inv tb text len s Q st S O0 m0 P O m ->
  evt rsegs (fun ms' => ps_post sp gp tp s1 F fc tb text len s Q st S O0 m0 ms' \/
      exists (a1' a2' a3' s10' : word) (P' O' : Z) (m' : word -> option byte),
        P < P' < text + len /\ ps_inv tb text len s Q st S O0 m0 P' O' m' /\
        ms' = ps_head sp gp tp s1 a1' a2' a3' s10' F fc st text len O' P' m')
    (ps_head sp gp tp s1 a1 a2 a3 s10 F fc st text len O P m).
Proof.
  intros sp gp tp s1 a1 a2 a3 s10 F fc m0 m tb text len s st S O0 P O Q PU HX Esp HI.
  pose proof HI as HI0.
  destruct HI as (HL & Hend & Hts & HB0 & HE0 & H80 & H160 & H240 & HW0 & HW360 & HO0 & HS & HSm & D1 & D2 & D3 & D4 & D5
    & HPs & Hsc & MU & WM & ws & HBw & EO & Hws & Hdec).
  subst O.
  pose proof (bytes_at_bound rsegs m0 text tb HB0) as [Ht _].
  pose proof HW0 as (HWa & HWb & _).
  assert (SUB36 : sub_fp [(S + 36, S + 40)] [(O0, O0 + Z.of_nat Q + 1); (S + 36, S + 40)]).
  { intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (_ & Hx & _). split; [exact Hx | exact I]. }
  assert (HB : bytes_at rsegs m text tb) by (apply (bytes_at_transport rsegs _ m0 m _ _ HB0 MU); dj).
  assert (HE : bytes_at rsegs m (st + 8) (le8 (Z_to_bv 64 (text + len))))
    by (apply (bytes_at_transport rsegs _ m0 m _ _ HE0 MU); dj).
  assert (H8 : bytes_at rsegs m (S + 8) (le8 (Z_to_bv 64 0xFFFFFFFFFCA02400)))
    by (apply (bytes_at_transport rsegs _ m0 m _ _ H80 MU); dj).
  assert (H16 : bytes_at rsegs m (S + 16) (le8 (Z_to_bv 64 0xDC00)))
    by (apply (bytes_at_transport rsegs _ m0 m _ _ H160 MU); dj).
  assert (H24 : bytes_at rsegs m (S + 24) (le8 (Z_to_bv 64 0xD800)))
    by (apply (bytes_at_transport rsegs _ m0 m _ _ H240 MU); dj).
  assert (HWm : wr_at rsegs m O0 (Z.of_nat Q + 1)) by exact (wr_at_transport rsegs m0 m _ _ HW0 WM).
  assert (HW36 : wr_at rsegs m (S + 36) 4) by exact (wr_at_transport rsegs m0 m _ _ HW360 WM).
  assert (HPe : P < text + len) by exact (pslp_lt tb text len P _ HL ltac:(lia) Hsc).
  destruct (nth_error tb (Z.to_nat (P - text))) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  pose proof (psl_rest_cons tb text P c ltac:(lia) Hc) as RC.
  pose proof (pst_br c) as Hcr.
  pose proof Hsc as Hsc0. rewrite RC in Hsc.
  unfold ps_head.
  eapply evt_cut.
  { eapply ps_turn with (text := text) (len := len) (st := st) (P := P) (O := O0 + Z.of_nat (length ws)) (tb := tb);
      try reflexivity.
    - exact HB.
    - exact HL.
    - exact Hend.
    - lia.
    - exact HE.
    - apply (pslp_wr_sub m O0 (Z.of_nat Q + 1)); [exact HWm | lia | lia | lia].
    - lia. }
  intros ms' Hm. cbv beta in Hm. rewrite RC in Hm. cbv iota in Hm.
  destruct (Z.eq_dec (bv_unsigned c) 34) as [C34|C34].
  { rewrite (proj2 (Z.eqb_eq _ _) C34) in Hm. cbv iota in Hm. subst ms'.
    rewrite C34, psl_scan_q in Hsc. injection Hsc as Hq.
    assert (EP : P = s + Z.of_nat Q) by lia.
    apply evt_done. cbv beta. left. unfold ps_post. left.
    exists a2, a3, s10, ws, m.
    split; [rewrite <- EP; reflexivity|].
    split; [rewrite Hdec, RC, C34, psd_quote, psd_emit_some, app_nil_r, EP; reflexivity|].
    split; [lia|]. split; [exact HBw|]. split; [exact MU | exact WM]. }
  rewrite (proj2 (Z.eqb_neq _ _) C34) in Hm. cbv iota in Hm.
  destruct (Z_lt_le_dec (bv_unsigned c) 32) as [C32|C32].
  { rewrite (proj2 (Z.ltb_lt _ _) C32) in Hm. cbv iota in Hm. subst ms'.
    fail_post m.
    split; [rewrite Hdec, RC, (psd_ctl _ _ C32); reflexivity|]. split; [exact MU | exact WM]. }
  rewrite (proj2 (Z.ltb_ge _ _) C32) in Hm. cbv iota in Hm.
  destruct (Z.eq_dec (bv_unsigned c) 92) as [C92|C92].
  2: {
    rewrite (proj2 (Z.eqb_neq _ _) C92) in Hm. cbv iota in Hm.
    rewrite (scan_ndq _ _ C34 C92) in Hsc.
    destruct (scan (rest_at tb text (P + 1))) as [q1|] eqn:Hq1; try rewrite Hq1 in Hsc; cbn [option_map] in Hsc;
      [|discriminate Hsc].
    injection Hsc as Hq.
    assert (L1 : P + 1 < text + len) by exact (pslp_lt tb text len (P + 1) q1 HL ltac:(lia) Hq1).
    rewrite (proj2 (Z.ltb_lt _ _) L1) in Hm. cbv iota in Hm. subst ms'.
    apply evt_done. cbv beta. right.
    exists (Z_to_bv 64 (bv_unsigned c)), a2, a3, (Z_to_bv 64 (P + 1)), (P + 1), (O0 + Z.of_nat (length ws) + 1),
      (write_to_mem m (wa (O0 + Z.of_nat (length ws))) [Z_to_bv 8 (bv_unsigned c)]).
    split; [lia|]. split; [|reflexivity].
    apply (ps_inv_step tb text len s Q st S O0 m0 P (O0 + Z.of_nat (length ws)) m _ _ _
             (ws ++ [Z_to_bv 8 (bv_unsigned c)]) HI0).
    - lia.
    - rewrite Hq1. f_equal. lia.
    - apply munch_write; [exact MU | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia
                         | cbn [inside length Z.of_nat Pos.of_succ_nat]; left; lia].
    - apply wmono_write. exact WM.
    - apply pslp_push1; [exact HBw | lia | lia].
    - rewrite length_app. cbn [length]. lia.
    - rewrite length_app. cbn [length]. lia.
    - rewrite Hdec, RC, (psd_plain _ _ C32 C34 C92), psd_emit_app, pslp_zb_app, (pslp_zb1 _ Hcr). reflexivity. }
  rewrite (proj2 (Z.eqb_eq _ _) C92) in Hm. cbv iota in Hm.
  destruct (Z_lt_le_dec (P + 1) (text + len)) as [L1|L1].
  2: { rewrite (psl_rest_end tb text (P + 1)), C92, psl_scan_bs1 in Hsc by lia. discriminate Hsc. }
  destruct (nth_error tb (Z.to_nat (P + 1 - text))) as [e|] eqn:He; [|apply nth_error_None in He; lia].
  pose proof (psl_rest_cons tb text (P + 1) e ltac:(lia) He) as RC1.
  replace (P + 1 + 1) with (P + 2) in RC1 by lia.
  rewrite RC1 in Hm, Hsc. cbv iota in Hm. rewrite C92, scan_bs in Hsc.
  pose proof (pst_br e) as Her.
  assert (RP : rest_at tb text P = 92 :: bv_unsigned e :: rest_at tb text (P + 2)) by (rewrite RC, RC1, C92; reflexivity).
  destruct (scan (rest_at tb text (P + 2))) as [q2|] eqn:Hq2; try rewrite Hq2 in Hsc; cbn [option_map] in Hsc;
    [|discriminate Hsc].
  injection Hsc as Hq.
  assert (L2 : P + 2 < text + len) by exact (pslp_lt tb text len (P + 2) q2 HL ltac:(lia) Hq2).
  destruct (Z.eq_dec (bv_unsigned e) 117) as [C117|C117].
  2: {
    rewrite (proj2 (Z.eqb_neq _ _) C117) in Hm. cbv iota in Hm.
    revert Hm. destruct (pst_esc (bv_unsigned e)) as [b|] eqn:Eb; intros Hm.
    2: { subst ms'. fail_post m.
         split; [rewrite Hdec, RP, (psd_esc_bad _ _ C117 Eb); reflexivity|]. split; [exact MU | exact WM]. }
    rewrite (proj2 (Z.ltb_lt _ _) L2) in Hm. cbv iota in Hm. subst ms'.
    pose proof (pslp_esc_rng _ _ Eb) as Hbr.
    apply evt_done. cbv beta. right.
    exists (Z_to_bv 64 (bv_unsigned e)), a2, a3, (Z_to_bv 64 (P + 2)), (P + 2), (O0 + Z.of_nat (length ws) + 1),
      (write_to_mem m (wa (O0 + Z.of_nat (length ws))) [Z_to_bv 8 b]).
    split; [lia|]. split; [|reflexivity].
    apply (ps_inv_step tb text len s Q st S O0 m0 P (O0 + Z.of_nat (length ws)) m _ _ _ (ws ++ [Z_to_bv 8 b]) HI0).
    - lia.
    - rewrite Hq2. f_equal. lia.
    - apply munch_write; [exact MU | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia
                         | cbn [inside length Z.of_nat Pos.of_succ_nat]; left; lia].
    - apply wmono_write. exact WM.
    - apply pslp_push1; [exact HBw | lia | lia].
    - rewrite length_app. cbn [length]. lia.
    - rewrite length_app. cbn [length]. lia.
    - rewrite Hdec, RP, (psd_esc _ _ _ C117 Eb), psd_emit_app, pslp_zb_app, (pslp_zb1 _ Hbr). reflexivity. }
  rewrite (proj2 (Z.eqb_eq _ _) C117) in Hm. cbv iota in Hm. subst ms'.
  assert (RU : rest_at tb text P = 92 :: 117 :: rest_at tb text (P + 2)) by (rewrite RP, C117; reflexivity).
  eapply evt_cut.
  { eapply ps_utail_pre with (e := text + len) (q := P + 2); [reflexivity | reflexivity | lia | lia]. }
  intros ms1 Hm1. cbv beta in Hm1.
  destruct (Z_lt_le_dec (text + len - (P + 2)) 4) as [L4|L4].
  { rewrite (proj2 (Z.leb_gt _ _) L4) in Hm1. cbv iota in Hm1. subst ms1.
    fail_post m.
    split; [|split; [exact MU | exact WM]].
    pose proof (pslp_rest_len tb text len (P + 2) HL ltac:(lia)) as HR2.
    rewrite Hdec, RU, psd_u_short by lia. reflexivity. }
  rewrite (proj2 (Z.leb_le _ _) L4) in Hm1. cbv iota in Hm1. subst ms1.
  assert (HL2 : length (skipn (Z.to_nat (P + 2 - text)) tb) = Z.to_nat (text + len - (P + 2)))
    by (rewrite length_skipn; lia).
  pose proof (psu_skip m text tb (Z.to_nat (P + 2 - text)) HB ltac:(lia)) as HB2.
  rewrite Z2Nat.id in HB2 by lia. replace (text + (P + 2 - text)) with (P + 2) in HB2 by lia.
  revert HL2 HB2.
  destruct (skipn (Z.to_nat (P + 2 - text)) tb) as [|b0 [|b1 [|b2 [|b3 r']]]] eqn:Er2; intros HL2 HB2;
    try (cbn [length] in HL2; lia).
  assert (HB4 : bytes_at rsegs m (P + 2) [b0; b1; b2; b3]).
  { change (b0 :: b1 :: b2 :: b3 :: r') with ([b0; b1; b2; b3] ++ r') in HB2.
    apply bytes_at_app in HB2. exact (proj1 HB2). }
  eapply evt_cut.
  { eapply ps_hex_loop with (P := P + 2); [reflexivity | reflexivity | reflexivity | exact HB4]. }
  intros ms2 (a1' & a2' & a3' & a4' & s3' & s10' & Hm2).
  revert Hm2. destruct (hex4_c.hex4 [b0; b1; b2; b3]) as [h|] eqn:Hh; intros Hm2; subst ms2.
  2: { fail_post m. split; [|split; [exact MU | exact WM]].
       rewrite Hdec, (psd_u_at tb text P _ ltac:(lia) RU), Er2, psd_hex4_4, Hh. reflexivity. }
  assert (EH : hex4_c.hex4 (skipn (Z.to_nat (P + 2 - text)) tb) = Some h) by (rewrite Er2, psd_hex4_4; exact Hh).
  pose proof (psu_hex4_range _ _ Hh) as Hhr.
  eapply evt_cut.
  { eapply ps_utail with (text := text) (len := len) (P := P) (S := S) (h := h) (tb := tb);
      [exact HX | reflexivity | exact Esp | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact Hhr | exact HB | exact HL | exact Hend | lia | lia | exact HS | exact HSm | exact D2
      | exact H8 | exact H16 | exact H24 | exact HW36]. }
  intros ms3 Hm3. cbv beta in Hm3.
  revert Hm3. destruct (ps_cp h (skipn (Z.to_nat (P + 6 - text)) tb)) as [[cp k]|] eqn:Hcp; intros Hm3.
  2: {
    destruct Hm3 as (ra' & t0' & t1' & t2' & a0' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s3'' & s10''
      & t3' & t4' & t5' & t6' & m1 & MU1 & WM1 & ->).
    fail_post m1.
    split; [rewrite Hdec, (psd_u_at tb text P _ ltac:(lia) RU), EH; cbv iota; rewrite Hcp; reflexivity|].
    split; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB36 MU1)) | exact (wmono_trans rsegs _ _ _ WM WM1)]. }
  destruct Hm3 as (ra' & t0' & t1' & t2' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3' & t4' & t5' & t6'
    & m1 & MU1 & WM1 & ->).
  destruct (pslp_scan_u tb text P h cp k _ ltac:(lia) Hhr RU EH Hcp Hsc0) as (Hk6 & Hkq & Hsk).
  destruct (pslp_cp h _ cp k Hhr Hcp) as (Hcpr & _).
  pose proof (pslp_utf8_len cp) as Hul.
  assert (MU01 : munch [(O0, O0 + Z.of_nat Q + 1); (S + 36, S + 40)] m0 m1)
    by exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB36 MU1)).
  assert (WM01 : wmono rsegs m0 m1) by exact (wmono_trans rsegs _ _ _ WM WM1).
  assert (HE1 : bytes_at rsegs m1 (st + 8) (le8 (Z_to_bv 64 (text + len))))
    by (apply (bytes_at_transport rsegs _ m0 m1 _ _ HE0 MU01); dj).
  assert (HBw1 : bytes_at rsegs m1 O0 ws) by (apply (bytes_at_transport rsegs _ m m1 _ _ HBw MU1); dj).
  eapply evt_cut.
  { eapply ps_putback with (o := O0 + Z.of_nat (length ws)) (cp := cp) (p := P + k) (st := st) (en := text + len);
      [exact PU | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia
      | apply (pslp_wr_sub m1 O0 (Z.of_nat Q + 1)); [exact (wr_at_transport rsegs m0 m1 _ _ HW0 WM01) | lia | lia | lia]
      | exact HE1 | lia | lia | lia]. }
  intros ms4 (a1'' & a2''' & a3''' & m2 & Hm4 & HBu & HE2 & MU2 & WM2).
  assert (L6 : P + k < text + len) by exact (pslp_lt tb text len (P + k) _ HL ltac:(lia) Hsk).
  rewrite (proj2 (Z.ltb_lt _ _) L6) in Hm4. cbv iota in Hm4. subst ms4.
  apply evt_done. cbv beta. right.
  exists a1'', a2''', a3''', (Z_to_bv 64 (P + k)), (P + k),
    (O0 + Z.of_nat (length ws) + Z.of_nat (length (put_utf8_c.utf8 cp))), m2.
  split; [lia|]. split; [|reflexivity].
  apply (ps_inv_step tb text len s Q st S O0 m0 P (O0 + Z.of_nat (length ws)) m _ _ _ (ws ++ put_utf8_c.utf8 cp) HI0).
  - lia.
  - rewrite Hsk. f_equal. lia.
  - apply (munch_trans _ _ _ _ MU01). apply (munch_weaken [(O0 + Z.of_nat (length ws),
      O0 + Z.of_nat (length ws) + Z.of_nat (length (put_utf8_c.utf8 cp)))]); [|exact MU2].
    intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx & _). split; [lia | exact I].
  - exact (wmono_trans rsegs _ _ _ WM01 WM2).
  - apply bytes_at_app. split; [apply (bytes_at_transport rsegs _ m1 m2 _ _ HBw1 MU2); dj | exact HBu].
  - rewrite length_app. lia.
  - rewrite length_app. lia.
  - rewrite Hdec, (psd_u_at tb text P _ ltac:(lia) RU), EH. cbv iota. rewrite Hcp. cbv iota.
    rewrite psd_emit_app, pslp_zb_app, (pslp_utf8 cp) by lia. reflexivity.
Qed.

Lemma ps_loop_h : forall n (sp gp tp s1 a1 a2 a3 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (tb : list byte) (text len s st S O0 P O : Z) (Q : nat),
  Z.to_nat (text + len - P) = n -> put_utf8_contract -> hex4_c.hex4_contract -> sp = Z_to_bv 64 S ->
  ps_inv tb text len s Q st S O0 m0 P O m ->
  evt rsegs (ps_post sp gp tp s1 F fc tb text len s Q st S O0 m0)
    (ps_head sp gp tp s1 a1 a2 a3 s10 F fc st text len O P m).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros sp gp tp s1 a1 a2 a3 s10 F fc m0 m tb text len s st S O0 P O Q Hn PU HX Esp HI.
  eapply evt_cut; [exact (ps_step sp gp tp s1 a1 a2 a3 s10 F fc m0 m tb text len s st S O0 P O Q PU HX Esp HI)|].
  intros ms' [Hp | (a1' & a2' & a3' & s10' & P' & O' & m' & HP' & HI' & ->)].
  - apply evt_done. exact Hp.
  - exact (IH (Z.to_nat (text + len - P')) ltac:(lia) sp gp tp s1 a1' a2' a3' s10' F fc m0 m' tb text len s st S O0
      P' O' Q eq_refl PU HX Esp HI').
Qed.

Lemma ps_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (tb : list byte) (text len s st S O0 P O : Z) (Q : nat),
  put_utf8_contract -> hex4_c.hex4_contract ->
  ra = Z_to_bv 64 117 -> sp = Z_to_bv 64 S -> t0 = Z_to_bv 64 113 -> t1 = Z_to_bv 64 102 -> t2 = Z_to_bv 64 12 ->
  s0 = Z_to_bv 64 st -> a0 = Z_to_bv 64 (text + len) ->
  a4 = Z_to_bv 64 91 -> a5 = Z_to_bv 64 47 -> a6 = Z_to_bv 64 98 -> a7 = Z_to_bv 64 8 ->
  s2 = Z_to_bv 64 O -> s3 = Z_to_bv 64 9 -> s4 = Z_to_bv 64 34 -> s5 = Z_to_bv 64 32 -> s6 = Z_to_bv 64 92 ->
  s7 = Z_to_bv 64 101 -> s8 = Z_to_bv 64 P -> s9 = Z_to_bv 64 10 -> s11 = Z_to_bv 64 6 ->
  t3 = Z_to_bv 64 110 -> t4 = Z_to_bv 64 114 -> t5 = Z_to_bv 64 13 -> t6 = Z_to_bv 64 116 ->
  ps_inv tb text len s Q st S O0 m0 P O m ->
  evt rsegs (ps_post sp gp tp s1 F fc tb text len s Q st S O0 m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x166ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m tb
    text len s st S O0 P O Q PU HX Era Esp Et0 Et1 Et2 Es0 Ea0 Ea4 Ea5 Ea6 Ea7 Es2 Es3 Es4 Es5 Es6 Es7 Es8 Es9 Es11
    Et3 Et4 Et5 Et6 HI.
  subst ra t0 t1 t2 s0 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6.
  exact (ps_loop_h _ sp gp tp s1 a1 a2 a3 s10 F fc m0 m tb text len s st S O0 P O Q eq_refl PU HX Esp HI).
Qed.
