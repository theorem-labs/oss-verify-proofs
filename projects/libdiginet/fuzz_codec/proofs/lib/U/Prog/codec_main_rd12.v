From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  diginet_personality_of_c text_arg_c check_text_scribble_c codec_main_inv codec_main_lib.
Import ListNotations.
Open Scope Z_scope.

(** Segment RD12 of the walk of LLVMFuzzerTestOneInput in the UBSan image: SCRIBBLE_TEXT
    (fuzz_codec.c:621-631), 0x13628-0x13670 and 0x13d40-0x13d7c. A NULL k.p takes
    diginet_personality_of(DIGINET_DESK_CONTROL24) and &SPEC_C24, which is the record of index 1;
    then k.a = fuzz_u8 & 0x7f, text_arg(&in, text), the null and alignment checks of k.desk,
    check_text_scribble(text, k.bytes, k.desk->chars), k.kind = SCRIBBLE and the jump to run()'s
    SCRIBBLE arm. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the call record cut around k.bytes ---- *)

(** The 40 bytes before k.bytes (offset 40) and the 120 after it. *)
Definition kpre (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))].
Definition kpost (k : kcall) : list cell :=
  [C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k); CB 32 (k_out k);
   C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].

Lemma krec_split : forall m (s : Z) k,
  rw_cells rsegs m (s + -384) (kcall_cells k) ->
  rw_cells rsegs m (s + -384) (kpre k) /\ rw_cells rsegs m (s + -344) [CB 24 (k_bytes k)] /\
  rw_cells rsegs m (s + -320) (kpost k).
Proof.
  intros m s k H.
  change (kcall_cells k) with (kpre k ++ [CB 24 (k_bytes k)] ++ kpost k) in H.
  apply rw_cells_app_split in H. destruct H as [H1 H].
  apply rw_cells_app_split in H. destruct H as [H2 H3].
  change (Z.of_nat (cells_size (kpre k))) with 40 in H2, H3.
  change (Z.of_nat (cells_size [CB 24 (k_bytes k)])) with 24 in H3.
  replace (s + -384 + 40) with (s + -344) in H2, H3 by lia.
  replace (s + -344 + 24) with (s + -320) in H3 by lia.
  auto.
Qed.

Lemma krec_join : forall m (s : Z) k,
  rw_cells rsegs m (s + -384) (kpre k) -> rw_cells rsegs m (s + -344) [CB 24 (k_bytes k)] ->
  rw_cells rsegs m (s + -320) (kpost k) -> rw_cells rsegs m (s + -384) (kcall_cells k).
Proof.
  intros m s k H1 H2 H3.
  change (kcall_cells k) with (kpre k ++ [CB 24 (k_bytes k)] ++ kpost k).
  apply rw_cells_app_join; [exact H1 |].
  change (Z.of_nat (cells_size (kpre k))) with 40.
  replace (s + -384 + 40) with (s + -344) by lia.
  apply rw_cells_app_join; [exact H2 |].
  change (Z.of_nat (cells_size [CB 24 (k_bytes k)])) with 24.
  replace (s + -344 + 24) with (s + -320) by lia. exact H3.
Qed.

(** The record this reader hands to run(): kind SCRIBBLE, p and desk of index i (1 or 2), a, and the
    24 bytes check_text_scribble leaves; the rest as the head left it. *)
Definition k9 (i a : Z) (bs : list byte) : kcall :=
  mkKcall 9 (repeat (b8 0) 4) (pers_of i) (sdesk i) a 0 0 0 bs 0 0
          (repeat (b8 0xa5) 32) (repeat (b8 0xa5) 32) 0 (repeat (b8 0) 24) 0 0 0.

(** ---- the desk of index 1 or 2 ---- *)

(** k.desk->chars: 4 for SPEC_C24, 8 for SPEC_PC. *)
Definition dch (i : Z) : Z := if i =? 1 then 4 else 8.

Lemma sdesk_ok : forall i, i = 1 \/ i = 2 -> 0 < sdesk i < 2 ^ 63.
Proof. intros i [-> | ->]; unfold sdesk, SDESK_C24, SDESK_PC; cbn; lia. Qed.

Lemma dch_ok : forall i, i = 1 \/ i = 2 -> 0 <= dch i <= 8.
Proof. intros i [-> | ->]; unfold dch; cbn; lia. Qed.

(** lbu a2, 0xa(k.desk): the chars field of SPEC_C24 / SPEC_PC in the RELRO tables. *)
Lemma rd12_chars : forall m i, relro_img m -> i = 1 \/ i = 2 ->
  ov_read_bytes rsegs m (Z_to_bv 64 (sdesk i + 10)) 1 = Some [Z_to_bv 8 (dch i)].
Proof.
  intros m i HR [-> | ->].
  - pose proof (codec_SPEC_C24_at m HR) as DK. unfold codec_SPEC_C24_cells in DK.
    exact (ro_cells_read_at rsegs m 0x1f690 _ 10 (C1 (Z_to_bv 8 4)) 1 _ DK eq_refl eq_refl eq_refl).
  - pose proof (codec_SPEC_PC_at m HR) as DK. unfold codec_SPEC_PC_cells in DK.
    exact (ro_cells_read_at rsegs m 0x1f6a0 _ 10 (C1 (Z_to_bv 8 8)) 1 _ DK eq_refl eq_refl eq_refl).
Qed.

(** ---- small facts ---- *)

Lemma used_le : forall d, (text_used d <= length d)%nat.
Proof. intros d. unfold text_used, text_len, text_hdr. lia. Qed.

Lemma cb_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[W B] _]. cbn [cells_bytes cbytes cells_wf cell_wf] in W, B.
  rewrite app_nil_r in B. destruct W as [W _]. split; assumption.
Qed.

Lemma b8_val : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof.
  intros x Hx. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.

Lemma zb_bz_id : forall l, Forall (fun x => 0 <= x < 256) l -> zb (bz l) = l.
Proof.
  intros l H. unfold zb, bz. rewrite map_map.
  transitivity (map (fun x : Z => x) l); [ | apply map_id ].
  apply map_ext_in. intros x Hx. apply b8_val. rewrite Forall_forall in H. apply H. exact Hx.
Qed.

Lemma land127 : forall x, 0 <= x -> 0 <= Z.land x 127 < 128.
Proof.
  intros x Hx. rewrite Z.land_comm.
  pose proof (land_lt_pow2 127 x 7 ltac:(change (2 ^ 7) with 128; lia) Hx) as H.
  change (2 ^ 7) with 128 in H. exact H.
Qed.

(** &in = sp + 0xd8 after the prologue: 8-aligned. *)
Lemma mod8_200 : forall x, x mod 16 = 0 -> (x + -200) mod 8 = 0.
Proof.
  intros x H. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in H. destruct H as [q ->].
  replace (q * 16 + -200) with ((2 * q - 25) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(** The record of index i after check_text_scribble: what run() may be handed. *)
Lemma rec_wf_k9 : forall i a tb, (i = 1 \/ i = 2) -> 0 <= a < 128 ->
  rec_wf (k9 i a (bz (scribble_bytes (zb tb) (dch i)))).
Proof.
  intros i a tb Hi Ha. unfold rec_wf, k9.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display].
  split; [lia |].
  split.
  { unfold desk_at. cbn [k_p k_desk].
    destruct Hi as [-> | ->]; [right; left | right; right]; split; reflexivity. }
  do 7 (split; [reflexivity |]).
  pose proof (reader_ok_12 (zb tb) a (dch i) ltac:(change (2 ^ 32) with 4294967296; lia)
                ltac:(pose proof (dch_ok i Hi); lia) (bytes_ok_map tb)) as R.
  pose proof R as (_ & _ & _ & _ & _ & RF & _).
  rewrite zb_bz_id by exact RF. exact R.
Qed.

(** ---- tactics ---- *)

(** A frame region across a call whose footprint misses it. *)
Ltac tr MU WM H :=
  lazymatch type of MU with
  | munch ?W ?m ?m' =>
      apply (rw_cells_transport rsegs W m m') in H;
      [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; repeat split; lia ]
  end.

(** A branch on a value of the desk of index 1 or 2, decided on both. *)
Ltac dec_i Hi :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false by (destruct Hi as [-> | ->]; vm_compute; reflexivity)
            | replace c with true by (destruct Hi as [-> | ->]; vm_compute; reflexivity) ];
      cbv iota
  end.

(** A branch on a closed value. *)
Ltac dec_closed :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in
      replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(** ---- the machine state of the segment ---- *)

Definition st12 (E : cenv) (ra' t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 s5' s7' t3' t4' t5' t6' : word)
  (ops pcv : Z) (m1 : word -> option byte) : machine_state :=
  MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
          (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
          a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
          s5' (Z_to_bv 64 ops) s7' (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
          (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
     (c_F E) (Z_to_bv 64 pcv) (c_fc E) None m1 (seg_rom rsegs).

(** ---- 0x13d44-0x13d7c: k.a, text_arg, the desk checks, check_text_scribble, kind, run() ---- *)

Lemma rd12_text : forall E n, env_ok E -> text_arg_contract -> check_text_scribble_contract ->
  rd_run_arm E n ->
  forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
         (i a c ops : Z) (u0 pj tj plj : list byte) (m1 : word -> option byte),
  (i = 1 \/ i = 2) -> 0 <= a < 128 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  0 < Z.of_nat (length (c_data E)) -> 0 <= c <= Z.of_nat (length (c_data E)) ->
  fr E m1 (kcall_cells (k_head 12 i)) (Z_to_bv 64 (bv_unsigned (c_p E) + c))
     (Z_to_bv 64 (Z.of_nat (length (c_data E)) - c)) u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (st12 E ra' t0' t1' t2' (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s5' s7'
                     t3' t4' t5' t6' ops 0x13d44 m1).
Proof.
  intros E n ENV CTA CTS RUN ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
         i a c ops u0 pj tj plj m1 Hi Ha HN HOPS HL HC FR ST MU WM HMI.
  unfold st12.
  pose proof ENV as (HD & _ & _ & HLO & SPA & DJ & HPB & HPNZ & _).
  specialize (HPNZ HL).
  pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (c_p E)) as Rp. unfold bv_modulus in Rp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, Rp.
  pose proof ST as (Hlo0 & _).
  unfold fr in FR. destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (data_at E m1 ENV MU) as HDAT.
  assert (DATA : bytes_at rsegs m1 (bv_unsigned (c_p E) + c) (skipn (Z.to_nat c) (c_data E)))
    by (apply bytes_at_skipn; [exact HDAT | lia]).
  assert (LD : Z.of_nat (length (skipn (Z.to_nat c) (c_data E))) = Z.of_nat (length (c_data E)) - c)
    by (rewrite length_skipn; lia).
  rewrite <- LD in FIN.
  pose proof (used_le (skipn (Z.to_nat c) (c_data E))) as TU.
  remember (skipn (Z.to_nat c) (c_data E)) as dd eqn:Edd. clear Edd HDAT HD.
  destruct (krec_split _ _ _ FK) as (K1 & K2 & K3). clear FK.
  unfold kpre in K1. cbn [k_head k_kind k_pad k_p k_desk k_a k_b k_c k_delta] in K1.
  cbn [k_head k_bytes] in K2.
  unfold kpost in K3.
  cbn [k_head k_n k_rc k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display] in K3.
  unfold saved in FSV.
  assert (U416 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) = bv_unsigned (c_sp E) + -416)
    by (apply u_frame; lia).
  assert (U200 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -200)) = bv_unsigned (c_sp E) + -200)
    by (apply unsigned_lit; lia).
  assert (U179 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -179)) = bv_unsigned (c_sp E) + -179)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -344)) = bv_unsigned (c_sp E) + -344)
    by (apply unsigned_lit; lia).
  (* 0x13d44 sw a0 -> k.a; 0x13d48-0x13d50 text_arg(&in, text) *)
  zstep. zstep. zstep. zstep.
  unfold text_arg_contract, TEXT_ARG, TEXT_ARG_DEPTH in CTA.
  eapply evt_cut;
    [ eapply CTA with (lo := c_lo E) (p := bv_unsigned (c_p E) + c) (data := dd) (tj := tj)
    | intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x
                  & mT & -> & MU2 & WM2 & MI2 & ST2 & FIN2 & FTX2) ].
  { unfold text_arg_pre, TEXT_ARG_DEPTH. rewrite ?U416, ?U200, ?U179.
    split; [exact FIN |]. split; [exact DATA |]. split; [exact FTX |].
    split; [unfold disj; lia |]. split; [unfold disj; lia |]. split; [unfold disj; lia |].
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [apply mod8_200; exact SPA |].
    split; [lia |]. split; [lia |].
    split; [assumption |]. split; [assumption | lia]. }
  fix_ret.
  rewrite U416 in ST2. rewrite U200 in FIN2. rewrite U179 in FTX2.
  clear FIN FTX DATA DJ.
  tr MU2 WM2 F0. tr MU2 WM2 F8. tr MU2 WM2 K1. tr MU2 WM2 K2. tr MU2 WM2 K3.
  tr MU2 WM2 FPD. tr MU2 WM2 FPL. tr MU2 WM2 FSV.
  match goal with
  | HM : munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) ?mm,
    HW : wmono rsegs (c_m E) ?mm |- _ =>
      assert (MU2' : munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) mT)
        by (apply (munch_trans _ _ _ _ HM); refine (munch_weaken _ _ _ _ _ MU2);
            intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; repeat split; lia);
      pose proof (wmono_trans rsegs _ _ _ HW WM2) as WM2';
      clear HM HW
  end.
  clear MU2 WM2.
  (* 0x13d54-0x13d60: k.desk and its null and alignment traps (group D) *)
  pose proof (sdesk_ok i Hi) as SDR.
  assert (UDK : bv_unsigned (Z_to_bv 64 (sdesk i)) = sdesk i) by (apply unsigned_lit; lia).
  pose proof (rd12_chars mT i (relro_at E mT ENV MU2') Hi) as CHR.
  step. step. dec_i Hi.
  step. step. dec_i Hi.
  (* 0x13d64 lbu a2 = k.desk->chars; 0x13d68-0x13d70 check_text_scribble(text, k.bytes, chars) *)
  step. clear CHR.
  zstep. zstep. zstep.
  unfold check_text_scribble_contract, CHECK_TEXT_SCRIBBLE, CHECK_TEXT_SCRIBBLE_DEPTH in CTS.
  destruct (cb_bytes _ _ _ _ FTX2) as [TBB LTB].
  assert (TB0 : In (b8 0) (text_taken dd ++ [b8 0] ++ skipn (S (text_len dd)) tj))
    by (apply in_or_app; right; left; reflexivity).
  remember (text_taken dd ++ [b8 0] ++ skipn (S (text_len dd)) tj) as tb eqn:Etb. clear Etb.
  eapply evt_cut;
    [ eapply CTS with (lo := c_lo E) (n := dch i) (tb := tb) (cj := repeat (b8 0) 24)
    | intros ms' (t0y & t1y & t2y & a0y & a1y & a2y & a3y & a4y & a5y & a6y & a7y & t3y & t4y & t5y & t6y
                  & mS & -> & MU3 & WM3 & MI3 & ST3 & KB3) ].
  { unfold check_text_scribble_pre, CHECK_TEXT_SCRIBBLE_DEPTH. rewrite ?U416, ?U179, ?U344.
    split; [lia |].
    split; [split; [exact TBB | exact TB0] |].
    split; [exact K2 |].
    split; [unfold disj; rewrite LTB; lia |].
    split; [clear - Hi; destruct Hi as [-> | ->]; vm_compute; reflexivity |].
    split; [apply dch_ok; exact Hi |].
    split; [lia |]. split; [lia |].
    split; [assumption |]. split; [assumption |]. split; [lia |].
    symmetry. apply scribble_agree. }
  fix_ret.
  rewrite U416 in ST3. rewrite U344 in KB3.
  clear K2 TBB.
  tr MU3 WM3 F0. tr MU3 WM3 F8. tr MU3 WM3 K1. tr MU3 WM3 K3. tr MU3 WM3 FIN2. tr MU3 WM3 FTX2.
  tr MU3 WM3 FPD. tr MU3 WM3 FPL. tr MU3 WM3 FSV.
  assert (MU3' : munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) mS)
    by (apply (munch_trans _ _ _ _ MU2'); refine (munch_weaken _ _ _ _ _ MU3);
        intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; repeat split; lia).
  pose proof (wmono_trans rsegs _ _ _ WM2' WM3) as WM3'.
  clear MU2' WM2' MU3 WM3.
  (* 0x13d74-0x13d7c: kind = SCRIBBLE, then run()'s SCRIBBLE arm *)
  zstep. zstep. zstep.
  set (kf := k9 i a (bz (scribble_bytes (zb tb) (dch i)))).
  pose proof (krec_join _ _ kf K1 KB3 K3) as KF.
  pose proof (rec_wf_k9 i a tb Hi Ha) as WFK. fold kf in WFK.
  pose proof (RUN kf WFK) as RK. unfold rec_ok in RK.
  change (pc_run (k_kind kf)) with 0x143cc in RK.
  eapply RK with (cur := Z_to_bv 64 (bv_unsigned (c_p E) + c + Z.of_nat (text_used dd)))
                 (rem := Z_to_bv 64 (Z.of_nat (length dd - text_used dd)))
                 (c := c + Z.of_nat (text_used dd)) (u0 := u0) (pj := pj) (tj := tb) (plj := plj).
  - exact WFK.
  - exact HN.
  - exact HOPS.
  - rewrite unsigned_lit by lia. lia.
  - lia.
  - rewrite unsigned_lit by lia. lia.
  - unfold fr. exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj KF (conj FIN2 (conj FPD
                        (conj FTX2 (conj FPL FSV)))))))).
  - exact ST3.
  - exact MU3'.
  - exact WM3'.
  - exact MI3.
Qed.

(** ---- 0x13644-0x13670 and 0x13d40: k.a = fuzz_u8(&in) & 0x7f ---- *)

Lemma rd12_u8 : forall E n, env_ok E -> text_arg_contract -> check_text_scribble_contract ->
  rd_run_arm E n ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
         (cur rem : word) (i c ops : Z) (u0 pj tj plj : list byte) (m1 : word -> option byte),
  (i = 1 \/ i = 2) ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 1 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 (kcall_cells (k_head 12 i)) cur rem u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (st12 E ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7'
                     t3' t4' t5' t6' ops 0x13644 m1).
Proof.
  intros E n ENV CTA CTS RUN ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
         cur rem i c ops u0 pj tj plj m1 Hi HN HOPS HCUR HC1 HCN FR ST MU WM HMI.
  pose proof (rd12_text E n ENV CTA CTS RUN) as K. unfold st12 in K |- *.
  pose proof ENV as (_ & _ & _ & HLO & _ & DJ & HPB & HPNZ & _).
  pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (c_p E)) as Rp. unfold bv_modulus in Rp.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur. unfold bv_modulus in Rcur.
  pose proof (bv_unsigned_in_range 64 rem) as Rrem. unfold bv_modulus in Rrem.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, Rp, Rcur, Rrem.
  assert (HL : 0 < Z.of_nat (length (c_data E))) by lia.
  specialize (HPNZ HL).
  pose proof ST as (Hlo0 & _).
  unfold fr in FR. destruct FR as (HKS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (data_at E m1 ENV MU) as HDAT.
  (* 0x13644-0x13648: in.n == 0 gives a = 0 (0x13d40) *)
  zstep. zstep.
  if_cases EZ.
  - zify_cond EZ.
    zstep.
    rewrite <- (Z_to_bv_bv_unsigned cur), <- (Z_to_bv_bv_unsigned rem) in FIN.
    rewrite HCUR in FIN.
    replace (bv_unsigned rem) with (Z.of_nat (length (c_data E)) - c) in FIN by lia.
    eapply K with (i := i) (a := 0) (c := c).
    all: first [ eassumption | lia
               | (unfold fr; exact (conj HKS (conj F0 (conj F8 (conj FK (conj FIN (conj FPD
                                      (conj FTX (conj FPL FSV)))))))))].
  - zify_cond EZ.
    (* 0x1364c-0x13664: in.n - 1, in.p + 1 and its pointer-overflow trap (group A) *)
    zstep. zstep. zstep. zstep. zstep.
    if_cases T; [ | refute_trap T ].
    zstep.
    match goal with H : bytes_at rsegs ?mm (bv_unsigned (c_p E)) (c_data E) |- _ =>
      assert (HB0 : ov_read_bytes rsegs mm cur 1 = Some [nth (Z.to_nat c) (c_data E) (Z_to_bv 8 0)])
      by (rewrite <- (Z_to_bv_bv_unsigned cur), HCUR;
          apply (bytes_at_byte mm (bv_unsigned (c_p E)) (c_data E) c); [exact H | lia]) end.
    (* 0x13668-0x13670: the byte, & 0x7f *)
    zstep. clear HB0.
    remember (nth (Z.to_nat c) (c_data E) (Z_to_bv 8 0)) as b eqn:Eb. clear Eb.
    zstep. zstep.
    rewrite HCUR in FIN.
    replace (bv_unsigned rem + -1) with (Z.of_nat (length (c_data E)) - (c + 1)) in FIN by lia.
    replace (bv_unsigned (c_p E) + c + 1) with (bv_unsigned (c_p E) + (c + 1)) in FIN by lia.
    eapply K with (i := i) (c := c + 1).
    all: first [ eassumption | lia
               | (apply land127; match goal with |- 0 <= bv_unsigned ?w =>
                                   exact (proj1 (bv_unsigned_in_range _ w)) end)
               | (unfold fr; exact (conj HKS (conj F0 (conj F8 (conj FK (conj FIN (conj FPD
                                      (conj FTX (conj FPL FSV)))))))))].
Qed.

(** ---- 0x13628-0x13640: a NULL k.p takes the personality and desk of index 1 ---- *)

Lemma codec_main_rd12 : seg_rd12_stmt.
Proof.
  unfold seg_rd12_stmt.
  intros E n ENV PERSOF CTA CTS RUN i Hi0.
  pose proof (rd12_u8 E n ENV CTA CTS RUN) as K. unfold st12 in K.
  unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ HN HOPS HCUR HC1 HCN FR ST MU WM HMI.
  change (pc_rd 12) with 0x13628.
  assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia.
  - pose proof ENV as (_ & _ & _ & HLO & _).
    pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
    pose proof ST as (Hlo0 & _).
    unfold fr in FR. destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
    unfold kcall_cells, k_head in FK.
    cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
         k_want_len k_want_key k_want_display] in FK.
    (* 0x13628 bnez s5 (k.p = pers_of 0 = NULL) falls through *)
    step. dec_closed.
    (* 0x1362c-0x13630: diginet_personality_of(DIGINET_DESK_CONTROL24) *)
    zstep. zstep.
    eapply evt_cut; [ apply PERSOF | ]. intros ms' [a1p ->]. fix_ret.
    match goal with |- context [pers_of ?x] => replace (pers_of x) with (pers_of 1) by reflexivity end.
    (* 0x13634-0x13640: k.desk = &SPEC_C24, k.p = the personality *)
    zstep. zstep. zstep. zstep.
    eapply K with (i := 1) (c := c).
    all: first [ eassumption | lia
               | (unfold fr; exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD
                                      (conj FTX (conj FPL FSV)))))))))].
  - step. dec_closed.
    eapply K with (i := 1) (c := c).
    all: first [ eassumption | lia ].
  - step. dec_closed.
    eapply K with (i := 2) (c := c).
    all: first [ eassumption | lia ].
Qed.
