From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img owe_sysex_c
  codec_main_inv codec_main_lib codec_main_owe0 codec_main_owe10.
Import ListNotations.
Open Scope Z_scope.

(** Segment OWE11 of the walk of LLVMFuzzerTestOneInput in the UBSan image: the SYSEX case of owe()
    (fuzz_codec.c:234-251), 0x145a0-0x145b0, 0x14ac0-0x14af0 and 0x14b34-0x14b74. Four early exits
    store SPEC_E_ARG, SPEC_E_REFUSED, SPEC_E_RANGE or SPEC_E_SPACE in want_rc (0x14a30); the
    seven_bit loop over the first n bytes (lemma [seven_loop]) leaves to SPEC_E_RANGE on a byte with
    bit 7 set; otherwise owe_sysex (0x14b70) writes want[0 .. n + 5), want_len and want_display. The
    pointer test of seven_bit (0x14b44) is dead: the pointer is a frame address. SYSEX needs no desk. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the seven_bit loop (0x14b40-0x14b5c) ---- *)

Lemma seven_bit_bad_n : forall l j n, (j < n)%nat -> (j < length l)%nat -> Z.testbit (nth j l 0) 7 = true ->
  seven_bit (firstn n l) = false.
Proof.
  intros l j n Hj Hl Ht. destruct (seven_bit (firstn n l)) eqn:E; [|reflexivity].
  unfold seven_bit in E. rewrite forallb_forall in E. specialize (E _ (In_nth_firstn l j n 0 Hj Hl)).
  rewrite Ht in E. discriminate E.
Qed.

Lemma seven_loop : forall (Q : machine_state -> Prop) F fc m
    ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (B n : Z) (bs : list byte),
  bytes_at rsegs m B bs -> 0 < B -> B + n < 2 ^ 64 -> 0 <= n -> n <= Z.of_nat (length bs) ->
  (seven_bit (firstn (Z.to_nat n) (zb bs)) = true -> forall a1' a3' a5' a6',
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3' (Z_to_bv 64 n) a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14b60) fc None m (seg_rom rsegs))) ->
  (seven_bit (firstn (Z.to_nat n) (zb bs)) = false -> forall a1' a3' a5' a6',
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3' (Z_to_bv 64 n) a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14a2c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 B) a2 (Z_to_bv 64 n) (Z_to_bv 64 n)
                   (Z_to_bv 64 B) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x14b40) fc None m (seg_rom rsegs)).
Proof.
  intros Q F fc m ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         B n bs BB HB0 HBn Hn0 Hnl KOK KBAD.
  assert (G : forall r i, r = Z.to_nat (n - i) -> 0 <= i < n ->
            seven_bit (firstn (Z.to_nat i) (zb bs)) = true -> forall a6x,
            evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (B + i)) a2 (Z_to_bv 64 (n - i))
                             (Z_to_bv 64 n) (Z_to_bv 64 (B + i)) a6x a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x14b44) fc None m (seg_rom rsegs))).
  { induction r as [|r IH]; intros i Hr Hi H7 a6x; [lia|].
    pose proof (bytes_at_byte m B bs i BB ltac:(lia)) as HR.
    zstep. if_cases T1.
    { exfalso. zify_cond T1. lia. }
    zstep. zstep. if_cases T2.
    - (* a byte with bit 7 set: SPEC_E_RANGE *)
      rewrite sxb_lts0 in T2.
      assert (SB : seven_bit (firstn (Z.to_nat n) (zb bs)) = false).
      { apply (seven_bit_bad_n (zb bs) (Z.to_nat i) (Z.to_nat n)); [lia | unfold zb; rewrite length_map; lia |].
        rewrite zb_nth. exact T2. }
      exact (KBAD SB _ _ _ _).
    - rewrite sxb_lts0 in T2.
      assert (H7' : seven_bit (firstn (Z.to_nat (i + 1)) (zb bs)) = true).
      { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        rewrite (firstn_S_nth _ (zb bs) (Z.to_nat i) 0) by (unfold zb; rewrite length_map; lia).
        rewrite seven_bit_snoc, H7, zb_nth, T2. reflexivity. }
      zstep. zstep. zstep. zstep. if_cases T3.
      + zify_cond T3.
        replace (B + i + 1) with (B + (i + 1)) by lia.
        replace (n - i + -1) with (n - (i + 1)) by lia.
        apply IH; [lia | lia | exact H7'].
      + zify_cond T3.
        replace (i + 1) with n in H7' by lia.
        exact (KOK H7' _ _ _ _). }
  zstep. if_cases T0.
  - zify_cond T0.
    assert (SB : seven_bit (firstn (Z.to_nat n) (zb bs)) = true)
      by (replace (Z.to_nat n) with 0%nat by lia; reflexivity).
    exact (KOK SB _ _ _ _).
  - zify_cond T0.
    pose proof (G (Z.to_nat (n - 0)) 0 eq_refl ltac:(lia) eq_refl a6) as H.
    rewrite Z.add_0_r, Z.sub_0_r in H. exact H.
Qed.

(** ---- the record owe() hands the checks ---- *)

(** owe() of kind 11 (fuzz_codec.c:234-251); the case never reads the desk. *)
Lemma owe_k11 : forall k, k_kind k = 11 ->
  owe_k k = if 0x7f <? k_a k then (E_ARG, noc) else if k_b k =? 0x70 then (E_REFUSED, noc)
            else if 0x7f <? k_b k then (E_RANGE, noc) else if 24 <? k_n k + 5 then (E_SPACE, noc)
            else if negb (seven_bit (firstn (Z.to_nat (k_n k)) (zb (k_bytes k)))) then (E_RANGE, noc)
            else (0, (fst (owe_sx (u8 (k_a k)) (u8 (k_b k)) (firstn (Z.to_nat (k_n k)) (zb (k_bytes k)))), 0,
                      snd (owe_sx (u8 (k_a k)) (u8 (k_b k)) (firstn (Z.to_nat (k_n k)) (zb (k_bytes k)))))).
Proof. intros k HK. unfold owe_k, owe_spec. rewrite HK. destruct (od_of k); reflexivity. Qed.

(** An early exit of owe(): want_rc = rc (0x14a30), the want fields still 0. *)
Lemma chk_wf_code11 : forall k rc, rec_wf k -> fst (owe_k k) = rc -> rc <> 0 -> - 2 ^ 31 <= rc < 2 ^ 31 ->
  chk_wf (with_want_rc (k_run k) rc).
Proof.
  intros k rc WF OW Hnz Hr.
  pose proof WF as (HK & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof (enc_owe_rc_o0 k WF) as EC. rewrite OW in EC.
  assert (E1 : enc_k (with_want_rc (k_run k) rc) = enc_k k) by reflexivity.
  assert (E2 : owe_k (with_want_rc (k_run k) rc) = owe_k k) by reflexivity.
  unfold chk_wf. rewrite E1, E2. kproj_o0.
  pose proof (desk_range_o0 k HDA) as [Rp Rd].
  pose proof HRD as (Ra & Rb & Rc & Rdl & _ & _ & Rn & _).
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj_o0. rewrite EC, HWL0, HWK0, HWD0. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [symmetry; exact OW|]. intros H. exfalso. apply Hnz. rewrite <- OW. exact H.
Qed.

(** owe_sysex wrote the owed bytes: the record of the success. *)
Lemma chk_wf_ok11 : forall k w dp, rec_wf k -> k_kind k = 11 ->
  k_a k <= 0x7f -> k_b k <> 0x70 -> k_b k <= 0x7f -> k_n k <= 19 ->
  seven_bit (firstn (Z.to_nat (k_n k)) (zb (k_bytes k))) = true ->
  owe_sx (u8 (k_a k)) (u8 (k_b k)) (zb (firstn (Z.to_nat (k_n k)) (k_bytes k))) = (w, dp) ->
  chk_wf (set_want (k_run k) (bz w ++ skipn (length w) (k_want (k_run k))) (Z.of_nat (length w)) dp).
Proof.
  intros k w dp WF HK Ha Hb70 Hb Hn H7 EX.
  pose proof WF as (HK' & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & _ & Rn & _).
  assert (EZ : zb (firstn (Z.to_nat (k_n k)) (k_bytes k)) = firstn (Z.to_nat (k_n k)) (zb (k_bytes k)))
    by (unfold zb; rewrite firstn_map; reflexivity).
  rewrite EZ in EX.
  assert (OW : owe_k k = (0, (w, 0, dp))).
  { rewrite (owe_k11 k HK).
    replace (0x7f <? k_a k) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (k_b k =? 0x70) with false by (symmetry; apply Z.eqb_neq; exact Hb70).
    replace (0x7f <? k_b k) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (24 <? k_n k + 5) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite H7. cbn [negb]. rewrite EX. reflexivity. }
  assert (LW : length w = (Z.to_nat (k_n k) + 5)%nat).
  { unfold owe_sx in EX. injection EX as Ew Ed. rewrite <- Ew.
    cbn [length app]. rewrite ?length_app, length_firstn, Rlen. cbn [length]. lia. }
  assert (DP : dp = 0 \/ dp = 1).
  { unfold owe_sx in EX. injection EX as Ew Ed. rewrite <- Ed. apply bit_01. }
  pose proof (enc_owe_rc_o0 k WF) as EC. rewrite OW in EC. cbn [fst] in EC.
  assert (E1 : enc_k (set_want (k_run k) (bz w ++ skipn (length w) (k_want (k_run k))) (Z.of_nat (length w)) dp)
               = enc_k k) by reflexivity.
  assert (E2 : owe_k (set_want (k_run k) (bz w ++ skipn (length w) (k_want (k_run k))) (Z.of_nat (length w)) dp)
               = owe_k k) by reflexivity.
  unfold chk_wf. rewrite E1, E2, OW. kproj_o0.
  pose proof (desk_range_o0 k HDA) as [Rp Rd].
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj_o0. rewrite EC, HWRC0, HWK0, LW. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [cbn [fst]; exact HWRC0|]. intros _. cbn [snd].
  split; [unfold bz; rewrite <- (length_map b8 w); apply firstn_app_exact |].
  split; [reflexivity|]. split; [rewrite LW; lia|]. split; [exact HWK0 | reflexivity].
Qed.

(** The record owe_sysex is called with. *)
Lemma kwf_run11 : forall k, rec_wf k -> fst (enc_k k) = 0 -> kcall_wf (k_run k).
Proof.
  intros k WF EC.
  pose proof WF as (HK & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rdl & _ & _ & Rn & _).
  pose proof (desk_range_o0 k HDA) as [Rp Rd].
  unfold kcall_wf, k_run, with_rc, with_out. kproj_o0. rewrite EC, HWRC0, HWL0, HWK0, HWD0. lia.
Qed.

Lemma bytes_at_firstn : forall m a bs j, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn j bs).
Proof.
  intros m a bs j H. rewrite <- (firstn_skipn j bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rw_cells_bytes_pick : forall m A pre n bs post,
  rw_cells rsegs m A (pre ++ CB n bs :: post) -> bytes_at rsegs m (A + Z.of_nat (cells_size pre)) bs.
Proof.
  intros m A pre n bs post H. apply rw_cells_app_split in H. destruct H as [_ H].
  change (CB n bs :: post) with ([CB n bs] ++ post) in H. apply rw_cells_app_split in H.
  destruct H as [H _]. exact (rw_cells_bytes_at _ _ _ _ H).
Qed.

Lemma codec_main_owe11 : seg_owe11_stmt.
Proof.
  unfold seg_owe11_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV OSX CHK k WF K11.
  unfold owe_sysex_contract, OWE_SYSEX, OWE_SYSEX_DEPTH in OSX.
  unfold owe_ok, chk_ok, fr in *. cenv_cbn.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ ND HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  clear ND.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & Rby & Rn & _ & _ & R11). specialize (R11 K11).
  destruct R11 as [Ra8 Rb8].
  destruct ENV as (BY & HMI0 & ST0 & LO & SPA & DJ & HPB & HPNZ & RI & DJR). cenv_cbn.
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST0 as (Hlo0 & Hhi0 & _).
  (* k.bytes, the 24 bytes at sp + 0x48, inside the record *)
  pose proof (rw_cells_bytes_pick m1 (bv_unsigned sp + -384) (firstn 8 (kcall_cells (k_run k))) 24 (k_bytes k)
                (skipn 9 (kcall_cells (k_run k))) FK) as BB.
  replace (bv_unsigned sp + -384 + Z.of_nat (cells_size (firstn 8 (kcall_cells (k_run k)))))
    with (bv_unsigned sp + -344) in BB by (cbn [cells_size csize firstn kcall_cells Nat.add]; lia).
  unfold kcall_cells, k_run, with_rc, with_out in FK.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in FK.
  rewrite K11. replace (pc_owe 11) with 0x145a0 by reflexivity.
  (* 0x145a0-0x145a8: a > 0x7f -> SPEC_E_ARG (0x145ac-0x145b0, 0x14a30) *)
  zstep. rewrite (sx32_small (k_a k)) by lia. zstep. zstep. if_cases T1.
  2: { zify_cond T1. zstep. zstep. zstep.
       eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_ARG)); try eassumption.
       - apply (chk_wf_code11 k E_ARG WF); [| unfold E_ARG; lia | unfold E_ARG; lia].
         rewrite (owe_k11 k K11). replace (0x7f <? k_a k) with true by (symmetry; apply Z.ltb_lt; lia).
         reflexivity.
       - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  zify_cond T1. assert (Ha7 : k_a k <= 0x7f) by lia.
  (* 0x14ac0-0x14ad0: b == 0x70 -> SPEC_E_REFUSED *)
  zstep. rewrite (sx32_small (k_b k)) by lia. zstep. zstep. if_cases T2.
  2: { zify_cond T2. zstep. zstep. zstep.
       eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_REFUSED)); try eassumption.
       - apply (chk_wf_code11 k E_REFUSED WF); [| unfold E_REFUSED; lia | unfold E_REFUSED; lia].
         rewrite (owe_k11 k K11). replace (0x7f <? k_a k) with false by (symmetry; apply Z.ltb_ge; lia).
         replace (k_b k =? 0x70) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
       - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  zify_cond T2. assert (Hb70 : k_b k <> 0x70) by lia.
  (* 0x14ad4-0x14ad8: b > 0x7f -> SPEC_E_RANGE *)
  zstep. zstep. if_cases T3.
  { zify_cond T3. zstep. zstep.
    eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_RANGE)); try eassumption.
    - apply (chk_wf_code11 k E_RANGE WF); [| unfold E_RANGE; lia | unfold E_RANGE; lia].
      rewrite (owe_k11 k K11). replace (0x7f <? k_a k) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (k_b k =? 0x70) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (0x7f <? k_b k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  zify_cond T3. assert (Hb7 : k_b k <= 0x7f) by lia.
  (* 0x14adc-0x14af0: n + 5 > 24 -> SPEC_E_SPACE *)
  zstep. zstep. zstep. zstep. if_cases T4.
  2: { zify_cond T4. assert (Hn20 : 20 <= k_n k) by (Z.div_mod_to_equations; lia).
       zstep. zstep. zstep.
       eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_SPACE)); try eassumption.
       - apply (chk_wf_code11 k E_SPACE WF); [| unfold E_SPACE; lia | unfold E_SPACE; lia].
         rewrite (owe_k11 k K11). replace (0x7f <? k_a k) with false by (symmetry; apply Z.ltb_ge; lia).
         replace (k_b k =? 0x70) with false by (symmetry; apply Z.eqb_neq; lia).
         replace (0x7f <? k_b k) with false by (symmetry; apply Z.ltb_ge; lia).
         replace (24 <? k_n k + 5) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
       - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  zify_cond T4. assert (Hn19 : k_n k <= 19) by (Z.div_mod_to_equations; lia).
  (* 0x14b34-0x14b3c, then seven_bit (0x14b40-0x14b5c) *)
  zstep. zstep. zstep.
  eapply seven_loop with (B := bv_unsigned sp + -344) (n := k_n k) (bs := k_bytes k);
    [exact BB | lia | lia | lia | pose proof Rlen as RL; unfold zb in RL; rewrite length_map in RL; rewrite RL; lia | |].
  2: { intros H7 a1x a3x a5x a6x. zstep. zstep.
       eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_RANGE)); try eassumption.
       - apply (chk_wf_code11 k E_RANGE WF); [| unfold E_RANGE; lia | unfold E_RANGE; lia].
         rewrite (owe_k11 k K11). replace (0x7f <? k_a k) with false by (symmetry; apply Z.ltb_ge; lia).
         replace (k_b k =? 0x70) with false by (symmetry; apply Z.eqb_neq; lia).
         replace (0x7f <? k_b k) with false by (symmetry; apply Z.ltb_ge; lia).
         replace (24 <? k_n k + 5) with false by (symmetry; apply Z.ltb_ge; lia).
         rewrite H7. reflexivity.
       - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  intros H7 a1x a3x a5x a6x.
  (* 0x14b60-0x14b70: the arguments of owe_sysex *)
  zstep. zstep. zstep. zstep. zstep.
  (* 0x14b70: owe_sysex(&k, a & 0xff, b & 0xff, k.bytes, k.n) *)
  assert (U416 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -416)) = bv_unsigned sp + -416)
    by (apply unsigned_lit; lia).
  assert (U384 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -384)) = bv_unsigned sp + -384)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -344)) = bv_unsigned sp + -344)
    by (apply unsigned_lit; lia).
  assert (EC : fst (enc_k k) = 0).
  { rewrite (enc_owe_rc_o0 k WF), (owe_k11 k K11).
    replace (0x7f <? k_a k) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (k_b k =? 0x70) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (0x7f <? k_b k) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (24 <? k_n k + 5) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite H7. reflexivity. }
  assert (RL : length (k_bytes k) = 24%nat) by (pose proof Rlen as RL; unfold zb in RL; rewrite length_map in RL; exact RL).
  pose proof (bytes_at_firstn m1 _ _ (Z.to_nat (k_n k)) BB) as BPL.
  assert (LPL : length (firstn (Z.to_nat (k_n k)) (k_bytes k)) = Z.to_nat (k_n k))
    by (rewrite length_firstn, RL; lia).
  assert (A8 : (bv_unsigned sp + -384) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
  eapply evt_cut.
  { eapply OSX with (lo := lo) (dev := u8 (k_a k)) (fn := u8 (k_b k)) (k := k_run k)
                    (pl := firstn (Z.to_nat (k_n k)) (k_bytes k)).
    unfold owe_sysex_pre, arg_zx, OWE_SYSEX_DEPTH. rewrite U416, U384, U344.
    split; [exact FK|]. split; [exact (kwf_run11 k WF EC)|]. split; [exact A8|].
    split; [split; [unfold u8; change (2 ^ 8) with 256; apply Z.mod_pos_bound; lia
                   | f_equal; unfold u8; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity]|].
    split; [split; [unfold u8; change (2 ^ 8) with 256; apply Z.mod_pos_bound; lia
                   | f_equal; unfold u8; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity]|].
    split; [exact BPL|]. split; [rewrite unsigned_lit by lia; rewrite LPL; lia|].
    split; [rewrite LPL; lia|]. split; [unfold disj; rewrite LPL; lia|].
    split; [lia|]. split; [lia|]. split; [exact HMI|]. split; [exact ST | lia]. }
  intros ms' (t0x & t1x & t2x & a0x & a1y & a2y & a3y & a4y & a5y & a6y & a7y & t3x & t4x & t5x & t6x & m3
              & -> & MU3 & WM3 & MI3 & ST3 & PST).
  fix_ret.
  rewrite U416 in MU3, ST3. rewrite U384 in MU3, PST.
  revert PST.
  destruct (owe_sx (u8 (k_a k)) (u8 (k_b k)) (zb (firstn (Z.to_nat (k_n k)) (k_bytes k)))) as [w dp] eqn:EX.
  intros PST.
  (* the frame outside owe_sysex's window and the record's want *)
  assert (TR : forall A cs, rw_cells rsegs m1 A cs -> bv_unsigned sp + -416 <= A ->
                 A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -384 + 144 \/ bv_unsigned sp + -384 + 184 <= A ->
                 rw_cells rsegs m3 A cs).
  { intros A cs H H1 H2. eapply rw_cells_transport; [exact H | exact MU3 | exact WM3 |].
    cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  apply TR in F0; [| lia | cbn [cells_size csize Nat.add]; lia].
  apply TR in F8; [| lia | cbn [cells_size csize Nat.add]; lia].
  apply TR in FIN; [| lia | right; lia].
  apply TR in FPD; [| lia | right; lia].
  apply TR in FTX; [| lia | right; lia].
  apply TR in FPL; [| lia | right; lia].
  apply TR in FSV; [| lia | right; lia].
  clear TR.
  assert (MU4 : munch [(bv_unsigned sp - 640, bv_unsigned sp)] m m3).
  { apply (munch_trans _ m m1 m3 MU).
    apply (munch_weaken [(bv_unsigned sp + -416 - 32, bv_unsigned sp + -416);
                         (bv_unsigned sp + -384 + 144, bv_unsigned sp + -384 + 184)]); [| exact MU3].
    intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia|]. split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM WM3) as WM4.
  (* 0x14b74: j 0x14a34, the checks *)
  zstep.
  eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (set_want (k_run k) (bz w ++ skipn (length w) (k_want (k_run k))) (Z.of_nat (length w)) dp));
    try eassumption.
  - exact (chk_wf_ok11 k w dp WF K11 Ha7 Hb70 Hb7 Hn19 H7 EX).
  - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj PST (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))).
Qed.
