From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_text codec_main_inv
  diginet_personality_of_c text_arg_c check_text_seg7_c check_text_counter_c owed_counter_text_c
  LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** COUNTER_TEXT (fuzz_codec.c:635-646): k.p NULL -> personality_of(1) and k.desk = SPEC_C24; text_arg(&in, text);
    check_text_seg7(); check_text_counter(text, k.bytes, &dots); owed_counter_text(text, k.bytes, &dots); a refusal
    goes to LATCH, else kind = 10, k.b = dots and run()'s COUNTER call (ENC10). *)

(** ---- the frame in pieces: the call record around k.bytes, the cursor, the tail around text and dots ---- *)

Definition kc_lo (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))].

Definition kc_hi (k : kcall) : list cell :=
  [C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k); CB 32 (k_out k);
   C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].

Lemma rd13_conv : forall m A cs cs', rw_cells rsegs m A cs ->
  cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] WR] W' Eb Es.
  split; [split; [exact W' | rewrite Eb; exact B] | rewrite Es; exact WR].
Qed.

Lemma rd13_split' : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof. intros m A B cs1 cs2 H ->. apply rw_cells_app_split. exact H. Qed.

Lemma rd13_join' : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply rw_cells_app_join; assumption. Qed.

Lemma rd13_CB_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma rd13_list_cut : forall (X : Type) (l : list X) n, (n <= length l)%nat ->
  exists l1 l2, l = l1 ++ l2 /\ length l1 = n.
Proof.
  intros X l n H. exists (firstn n l), (skipn n l).
  split; [symmetry; apply firstn_skipn | apply firstn_length_le; exact H].
Qed.

Ltac rd13_sz := cbn [cells_size csize app kc_lo kc_hi Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Lemma rd13_frame_split : forall e m1 k c rem tl,
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  exists t5 tt (dj : byte) t9,
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] ++ kc_lo k) /\
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -344) [CB 24 (k_bytes k)] /\
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -320) (kc_hi k) /\
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -200)
      [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)] /\
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -184) [CB 5 t5] /\
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -179) [CB 65 tt] /\
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -114) [C1 dj] /\
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -113) [CB 9 t9].
Proof.
  intros e m1 k c rem tl H. unfold body_cells in H.
  destruct (rd13_split' m1 _ (bv_unsigned (e_sp e) + -344)
              ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] ++ kc_lo k)
              ([CB 24 (k_bytes k)] ++ kc_hi k ++
               [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)] ++ [CB 80 tl])
              H ltac:(rd13_sz)) as [P1 H1].
  destruct (rd13_split' m1 _ (bv_unsigned (e_sp e) + -320) [CB 24 (k_bytes k)] _ H1 ltac:(rd13_sz)) as [P2 H2].
  destruct (rd13_split' m1 _ (bv_unsigned (e_sp e) + -200) (kc_hi k) _ H2 ltac:(rd13_sz)) as [P3 H3].
  destruct (rd13_split' m1 _ (bv_unsigned (e_sp e) + -184)
              [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)] _ H3 ltac:(rd13_sz)) as [P4 H4].
  pose proof H4 as [[[W _] _] _]. cbn [cell_wf] in W.
  destruct (rd13_list_cut _ tl 5 ltac:(lia)) as (t5 & r1 & -> & L5).
  rewrite length_app in W.
  destruct (rd13_list_cut _ r1 65 ltac:(lia)) as (tt & r2 & -> & L65).
  rewrite length_app in W.
  destruct r2 as [|dj t9]; [cbn [length] in W; lia |]. cbn [length] in W.
  assert (H5 : rw_cells rsegs m1 (bv_unsigned (e_sp e) + -184) ([CB 5 t5] ++ [CB 65 tt] ++ [C1 dj] ++ [CB 9 t9])).
  { apply (rd13_conv _ _ _ _ H4).
    - cbn [cells_wf cell_wf app]. repeat split; lia.
    - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
    - cbn [cells_size csize app]. lia. }
  destruct (rd13_split' m1 _ (bv_unsigned (e_sp e) + -179) [CB 5 t5] _ H5 ltac:(rd13_sz)) as [Q1 H6].
  destruct (rd13_split' m1 _ (bv_unsigned (e_sp e) + -114) [CB 65 tt] _ H6 ltac:(rd13_sz)) as [Q2 H7].
  destruct (rd13_split' m1 _ (bv_unsigned (e_sp e) + -113) [C1 dj] _ H7 ltac:(rd13_sz)) as [Q3 Q4].
  exists t5, tt, dj, t9.
  split; [exact P1 |]. split; [exact P2 |]. split; [exact P3 |]. split; [exact P4 |].
  split; [exact Q1 |]. split; [exact Q2 |]. split; [exact Q3 | exact Q4].
Qed.

Lemma rd13_frame_join : forall e m1 k c rem t5 tt (dj : byte) t9 b1 b2,
  k_bytes k = b1 ++ b2 ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] ++ kc_lo k) ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -344) [CB 8 b1] ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -336) [CB 16 b2] ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -320) (kc_hi k) ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -200)
    [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem)] ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -184) [CB 5 t5] ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -179) [CB 65 tt] ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -114) [C1 dj] ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -113) [CB 9 t9] ->
  rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem (t5 ++ tt ++ dj :: t9)).
Proof.
  intros e m1 k c rem t5 tt dj t9 b1 b2 Hb P1 B1 B2 P3 P4 T1 T2 T3 T4.
  pose proof B1 as [[[L1 _] _] _]. pose proof B2 as [[[L2 _] _] _].
  pose proof T1 as [[[L5 _] _] _]. pose proof T2 as [[[L65 _] _] _]. pose proof T4 as [[[L9 _] _] _].
  cbn [cell_wf] in L1, L2, L5, L65, L9.
  pose proof (rd13_join' _ _ _ _ _ B1 B2 ltac:(rd13_sz)) as B12.
  assert (BB : rw_cells rsegs m1 (bv_unsigned (e_sp e) + -344) [CB 24 (k_bytes k)]).
  { rewrite Hb. apply (rd13_conv _ _ _ _ B12).
    - cbn [cells_wf cell_wf]. rewrite length_app. split; [lia | exact I].
    - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
    - reflexivity. }
  pose proof (rd13_join' _ _ _ _ _ T1 T2 ltac:(rd13_sz)) as T12.
  pose proof (rd13_join' _ _ _ _ _ T12 T3 ltac:(rd13_sz)) as T123.
  pose proof (rd13_join' _ _ _ _ _ T123 T4 ltac:(rd13_sz)) as T1234.
  assert (TT : rw_cells rsegs m1 (bv_unsigned (e_sp e) + -184) [CB 80 (t5 ++ tt ++ dj :: t9)]).
  { apply (rd13_conv _ _ _ _ T1234).
    - cbn [cells_wf cell_wf]. rewrite !length_app. cbn [length]. split; [lia | exact I].
    - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
    - reflexivity. }
  pose proof (rd13_join' _ _ _ _ _ P1 BB ltac:(rd13_sz)) as J1.
  pose proof (rd13_join' _ _ _ _ _ J1 P3 ltac:(rd13_sz)) as J2.
  pose proof (rd13_join' _ _ _ _ _ J2 P4 ltac:(rd13_sz)) as J3.
  pose proof (rd13_join' _ _ _ _ _ J3 TT ltac:(rd13_sz)) as J4.
  unfold body_cells. exact J4.
Qed.

(** ---- values ---- *)

Lemma rd13_b8_unsigned : forall v, 0 <= v < 256 -> bv_unsigned (b8 v) = v.
Proof.
  intros v Hv. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma rd13_zb_range : forall l, Forall (fun x => 0 <= x < 256) (zb l).
Proof.
  intros l. unfold zb. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma rd13_zb_bz : forall l, Forall (fun x => 0 <= x < 256) l -> zb (bz l) = l.
Proof.
  intros l H. induction H as [|x l Hx _ IH]; [reflexivity |].
  change (zb (bz (x :: l))) with (bv_unsigned (b8 x) :: zb (bz l)).
  rewrite rd13_b8_unsigned by exact Hx. rewrite IH. reflexivity.
Qed.

Lemma rd13_bz_counter : forall s, bz (counter_bytes s) = bz s ++ repeat (b8 0xa5) 16.
Proof. intros s. unfold counter_bytes, bz. rewrite map_app. reflexivity. Qed.

(** owed_counter_text returns 0 or E_RANGE. *)
Lemma rd13_ct2_go_rc : forall k n s dot i seg d,
  fst (fst (ct2_go n s dot i k seg d)) = 0 \/ fst (fst (ct2_go n s dot i k seg d)) = E_RANGE.
Proof.
  induction k as [|k IH]; intros n s dot i seg d; cbn [ct2_go].
  - left. reflexivity.
  - repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [ apply IH | left; reflexivity | right; reflexivity ].
Qed.

Lemma rd13_owed_rc : forall t rc sg d, owed_counter_text_spec t = (rc, sg, d) -> rc = 0 \/ rc = E_RANGE.
Proof.
  intros t rc sg d H. unfold owed_counter_text_spec in H.
  destruct (ct1_owe t 0 [] (repeat 0 8)) as [[[n s] dot]|].
  - unfold ct2 in H. pose proof (rd13_ct2_go_rc 8 n s dot 0 [] 0) as R. rewrite H in R. cbn [fst] in R. exact R.
  - injection H as <- _ _. right. reflexivity.
Qed.

(** A branch: keep the arms the facts allow. *)
Ltac rd13_br :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "BR" in if_cases H; zify_cond H; try (exfalso; lia); try clear H
  | _ => idtac
  end.

(** ---- 0x1384c-0x13898: k.p and k.desk set (pd_ok on the desk of the text operation) ---- *)

Lemma rd13_tail :
  text_arg_contract -> check_text_seg7_contract -> check_text_counter_contract -> owed_counter_text_contract ->
  forall e fuel, env_ok e -> enc10_ok e fuel -> latch_ok e fuel ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops : word)
         (pv dv : Z) (d0 : desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) -> pd_ok pv dv (Some d0) -> cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e (k_rd 13 pv dv) c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' ops s8' s10' t3' t4' t5' t6')
          0x1384c m1).
Proof.
  intros CTA CS7 CTC COC e fuel HE EN LA
         ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops pv dv d0 c rem tl m1
         HF HPD HC FR HFR.
  unfold st, body_regs.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & _ & _ & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  destruct HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  destruct HC as (Hc0 & Hr0 & Hcr).
  destruct (rd13_frame_split e m1 _ c rem tl FR) as (t5 & tt & dj & t9 & FA & FB & FH & FC & F5 & FT & FD & F9).
  clear FR.
  unfold kc_lo, kc_hi, k_rd in FA, FB, FH.
  cbn [app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out
       k_want_rc k_want k_want_len k_want_key k_want_display] in FA, FB, FH.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  assert (U200 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -200)) = bv_unsigned (e_sp e) + -200)
    by (apply unsigned_lit; lia).
  assert (U179 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -179)) = bv_unsigned (e_sp e) + -179)
    by (apply unsigned_lit; lia).
  assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -344)) = bv_unsigned (e_sp e) + -344)
    by (apply unsigned_lit; lia).
  assert (U114 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -114)) = bv_unsigned (e_sp e) + -114)
    by (apply unsigned_lit; lia).
  (* the input bytes from the cursor on *)
  set (din := skipn (Z.to_nat c) (e_data e)).
  assert (HLd : Z.of_nat (length din) = rem) by (unfold din; rewrite length_skipn; lia).
  assert (HBd : bytes_at rsegs m1 (bv_unsigned (e_p e) + c) din).
  { pose proof (data_of_munch e m1 HE MU) as HD.
    rewrite <- (firstn_skipn (Z.to_nat c) (e_data e)) in HD.
    apply bytes_at_app in HD. destruct HD as [_ HD].
    rewrite firstn_length_le in HD by lia. rewrite Z2Nat.id in HD by lia. exact HD. }
  (* 0x1384c addi a0 = &in; addi a1 = text; jal text_arg *)
  zstep. zstep. zstep.
  unfold text_arg_contract, TEXT_ARG, TEXT_ARG_DEPTH in CTA.
  eapply evt_cut;
    [ eapply CTA with (lo := e_lo e) (p := bv_unsigned (e_p e) + c) (data := din) (tj := tt)
    | clear HBd; post_call rsegs m1 ].
  { unfold text_arg_pre, TEXT_ARG_DEPTH. rewrite ?USP, ?U200, ?U179, HLd.
    split; [exact FC |]. split; [exact HBd |]. split; [exact FT |].
    split; [unfold disj; lia |]. split; [unfold disj; lia |]. split; [unfold disj; lia |].
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [exact HMI |]. split; [exact ST | lia]. }
  rewrite ?USP, ?U200, ?U179, ?U344, ?U114 in *.
  clear DJ.
  match goal with H : rw_cells _ _ (bv_unsigned (e_sp e) + -200) _ |- _ => rename H into FC end.
  match goal with H : rw_cells _ _ (bv_unsigned (e_sp e) + -179) _ |- _ => rename H into FT end.
  (* the new cursor and the text *)
  assert (HU : (text_used din <= length din)%nat).
  { unfold text_used, text_len, text_hdr.
    pose proof (Nat.le_min_r (Z.to_nat (text_u16 din mod 65)) (length din - Nat.min 2 (length din))).
    pose proof (Nat.le_min_r 2 (length din)). lia. }
  set (c2 := c + Z.of_nat (text_used din)).
  set (r2 := rem - Z.of_nat (text_used din)).
  replace (bv_unsigned (e_p e) + c + Z.of_nat (text_used din)) with (bv_unsigned (e_p e) + c2) in FC
    by (unfold c2; lia).
  replace (Z.of_nat (length din - text_used din)) with r2 in FC by (unfold r2; lia).
  assert (HC2 : cur_ok e c2 r2) by (unfold cur_ok, c2, r2; lia).
  clearbody c2 r2.
  remember (text_taken din ++ [b8 0] ++ skipn (S (text_len din)) tt) as tb eqn:Etb.
  assert (HIn : In (b8 0) tb) by (rewrite Etb; apply in_or_app; right; left; reflexivity).
  clear Etb HU HLd.
  pose proof FT as [[[Ltb _] _] _]. cbn [cell_wf] in Ltb.
  (* 0x13858 jal check_text_seg7 *)
  zstep.
  unfold check_text_seg7_contract, CHECK_TEXT_SEG7, CHECK_TEXT_SEG7_DEPTH in CS7.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    eapply evt_cut; [ eapply CS7 with (lo := e_lo e) | post_call rsegs m ] end.
  { unfold check_text_seg7_pre, CHECK_TEXT_SEG7_DEPTH. rewrite ?USP.
    split; [exact (relro_of_munch e _ HE MU) |].
    split; [apply (callee_relro_disj e); [exact HE | lia] |].
    split; [eassumption |]. split; [eassumption |]. split; [lia | exact seg7_agree]. }
  rewrite ?USP, ?U200, ?U179, ?U344, ?U114 in *.
  (* 0x1385c addi a0 = text; addi a2 = &dots; addi s5 = k.bytes; mv a1, s5; jal check_text_counter *)
  zstep. zstep. zstep. zstep. zstep.
  unfold check_text_counter_contract, CHECK_TEXT_COUNTER, CHECK_TEXT_COUNTER_DEPTH in CTC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    eapply evt_cut; [ eapply CTC with (lo := e_lo e) (tb := tb) (sj := fz0 24) (dj := dj) | post_call rsegs m ] end.
  { unfold check_text_counter_pre, CHECK_TEXT_COUNTER_DEPTH. rewrite ?USP, ?U179, ?U344, ?U114.
    split; [lia |]. split; [split; [exact (rd13_CB_bytes _ _ _ _ FT) | exact HIn] |].
    split; [lia |]. split; [exact FB |]. split; [lia |]. split; [exact FD |].
    split; [unfold disj; lia |].
    split; [unfold disj; rewrite Ltb; change (Z.of_nat 65) with 65; lia |].
    split; [unfold disj; rewrite Ltb; change (Z.of_nat 65) with 65; lia |].
    split; [exact (relro_of_munch e _ HE MU) |].
    split; [apply (callee_relro_disj e); [exact HE | lia] |].
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [eassumption |]. split; [eassumption |]. split; [lia |].
    rewrite (counter_text_agree (zb tb) (rd13_zb_range tb)).
    destruct (owed_counter_text_spec (zb tb)) as [[rr ss] xx].
    split; [reflexivity | intros _; split; reflexivity]. }
  rewrite ?USP, ?U200, ?U179, ?U344, ?U114 in *.
  match goal with H : ex _ |- _ => destruct H as (sg & dv1 & FB2 & FD) end.
  destruct (rd13_split' _ _ (bv_unsigned (e_sp e) + -336) [CB 8 sg] [CB 16 (repeat (b8 0xa5) 16)] FB2
              ltac:(rd13_sz)) as [FB8 FB16].
  clear FB2.
  (* 0x13870 addi a0 = text; addi a2 = &dots; mv a1, s5; jal owed_counter_text *)
  zstep. zstep. zstep. zstep.
  unfold owed_counter_text_contract, OWED_COUNTER_TEXT, OWED_COUNTER_TEXT_DEPTH in COC.
  destruct (owed_counter_text_spec (zb tb)) as [[rc sgo] dts] eqn:EOC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    eapply evt_cut; [ eapply COC with (lo := e_lo e) (tb := tb) (sj := sg) (dj := dv1) | post_call rsegs m ] end.
  { unfold owed_counter_text_pre, OWED_COUNTER_TEXT_DEPTH. rewrite ?USP, ?U179, ?U344, ?U114.
    split; [lia |]. split; [split; [exact (rd13_CB_bytes _ _ _ _ FT) | exact HIn] |].
    split; [lia |]. split; [exact FB8 |]. split; [lia |]. split; [exact FD |].
    split; [unfold disj; lia |].
    split; [exact (relro_of_munch e _ HE MU) |].
    split; [apply (callee_relro_disj e); [exact HE | lia] |].
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [eassumption |]. split; [eassumption | lia]. }
  rewrite ?USP, ?U200, ?U179, ?U344, ?U114 in *.
  match goal with H : context [owed_counter_text_spec (zb tb)] |- _ =>
    tryif constr_eq H EOC then fail
    else (rewrite EOC in H; cbv beta iota zeta in H; destruct H as (HA0 & HOK & HNO)) end.
  match type of HA0 with ?v = _ => subst v end.
  pose proof (rd13_owed_rc _ _ _ _ EOC) as [Erc | Erc]; subst rc.
  - (* the text is a counter: 0x13880 bnez falls through; dots, k.p, kind = 10, k.b = dots, j ENC10 *)
    destruct (HOK eq_refl) as [FB8' FD']. clear HOK HNO.
    rewrite ?U344, ?U114 in FB8', FD'.
    destruct (owed_counter_ok _ _ _ _ EOC eq_refl) as (Lsg & Fsg & Rdts).
    zstep. rd13_br.
    zstep. zstep. zstep. zstep. zstep. zstep.
    unfold enc10_ok, st, body_regs in EN.
    eapply EN with (k := mkKcall 10 (fz0 4) pv dv 0 (bv_unsigned (b8 dts)) 0 0 (bz (counter_bytes sgo)) 0 0
                           (fa5 32) (fa5 32) 0 (fz0 24) 0 0 0)
                   (od := Some d0) (c := c2) (rem := r2) (tl := t5 ++ tb ++ b8 dts :: t9);
      [ exact HF | reflexivity | exact HPD | | reflexivity | reflexivity | exact HC2 | | ].
    + unfold rdr_k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n].
      rewrite (rd13_b8_unsigned dts) by lia.
      pose proof (reader_ok_13 _ _ _ EOC) as RD.
      rewrite rd13_zb_bz; [exact RD |]. destruct RD as (_ & _ & _ & _ & _ & HFa & _). exact HFa.
    + eapply (rd13_frame_join e _ _ c2 r2 t5 tb (b8 dts) t9 (bz sgo) (repeat (b8 0xa5) 16));
        [ apply rd13_bz_counter | eassumption .. ].
    + split; [exact SV |]. split; [eassumption |]. split; [exact MU |]. split; [exact WM | eassumption].
  - (* refused: 0x13880 bnez to LATCH *)
    destruct (HNO ltac:(unfold E_RANGE; lia)) as (sg' & dv' & FB8' & FD'). clear HOK HNO.
    rewrite ?U344, ?U114 in FB8', FD'.
    try unfold E_RANGE.
    zstep. rd13_br.
    unfold latch_ok, st, body_regs in LA.
    eapply LA with (k := mkKcall 13 (fz0 4) pv dv 0 0 0 0 (sg' ++ repeat (b8 0xa5) 16) 0 0 (fa5 32) (fa5 32)
                           0 (fz0 24) 0 0 0)
                   (c := c2) (rem := r2) (tl := t5 ++ tb ++ dv' :: t9);
      [ exact HF | exact HC2 | | ].
    + eapply (rd13_frame_join e _ _ c2 r2 t5 tb dv' t9 sg' (repeat (b8 0xa5) 16));
        [ reflexivity | eassumption .. ].
    + split; [exact SV |]. split; [eassumption |]. split; [exact MU |]. split; [exact WM | eassumption].
Qed.

(** ---- 0x13830-0x13848: bnez s5 (k.p); k.p NULL -> personality_of(1), k.desk = SPEC_C24 ---- *)

Lemma codec_main_rd13 : S_rd13.
Proof.
  unfold S_rd13. intros CPOF CTA CS7 CTC COC e fuel HE EN LA.
  pose proof (rd13_tail CTA CS7 CTC COC e fuel HE EN LA) as TAIL.
  unfold st, body_regs in TAIL.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
         HF HPD HC FR HFR.
  change (rd_pc 13) with 0x13830.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  destruct HPD as [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]].
  - destruct HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
    pose proof ST as [Hlo0 _].
    unfold body_cells, k_rd in FR.
    cbn [kcall_cells app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out
         k_want_rc k_want k_want_len k_want_key k_want_display] in FR.
    zstep. rd13_br.
    zstep. zstep.
    unfold diginet_personality_of_contract, DIGINET_PERSONALITY_OF in CPOF.
    eapply evt_cut; [ apply CPOF | intros ms' (a1x & a2x & ->) ].
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
    match goal with |- context [pers_of ?x] => replace (pers_of x) with 127992 by (vm_compute; reflexivity) end.
    zstep. zstep. zstep. zstep.
    eapply TAIL with (pv := PERS) (dv := 0x1f208) (c := c) (rem := rem) (tl := tl);
      [ exact HF | right; left; split; [reflexivity | split; reflexivity] | exact HC | exact FR
      | exact (conj SV (conj ST (conj MU (conj WM HMI)))) ].
  - unfold PERS in *. zstep. rd13_br.
    eapply TAIL with (pv := 127992) (dv := 0x1f208) (c := c) (rem := rem) (tl := tl);
      [ exact HF | right; left; split; [reflexivity | split; reflexivity] | exact HC | exact FR | exact HFR ].
  - unfold PERS in *. zstep. rd13_br.
    eapply TAIL with (pv := 127992 + 24) (dv := 0x1f218) (c := c) (rem := rem) (tl := tl);
      [ exact HF | right; right; split; [reflexivity | split; reflexivity] | exact HC | exact FR | exact HFR ].
Qed.
