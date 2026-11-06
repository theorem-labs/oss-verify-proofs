(* io_send_seg_world: the world-relation and written-range lemmas the segment files of the image-A walk of io_send
   share (lib/A/Prog/io_send_cg.v transport_io_send_cg_holds_stmt, entry 0x82d60 = TImgA.v ti_io_send timg_A).

   This file names no machine state and runs no code. It holds, for image A's world table TMAP_A (TWorldA.v) and the
   whole G of the image (TransportG.v G_HARNESS):
   - G: ios_inG_row (a payload byte of a row of TMAP_A is a byte of G), ios_tw_in_G (every payload byte is), and
     ios_wr_inG (every byte of io_send_cg.v iosend_wr is), the facts a run's write right awr_ok_x needs;
   - the converse facts, one per field of iosend_wr (ios_wr_fail .. ios_wr_nq): a byte the walk stores, given by its
     image base and its offset in the global (TModel/TWorld.v), is a byte of iosend_wr. The offsets:
       g_fail_next + 0 (ONE byte in image A); GOT + 196 / 200 / 204 (e2, e3, acks; 4 bytes each);
       g_last_counter + 0 (4); M + 84 (host_counter, 4), + 48 (next_ka, 8), + 64 (last_display, 8),
       + 72 (display_sent, 4), + 96 (fly.on, 4), + 100 (fly.cmd, 1), + 104 (fly.counter, 4), + 108 (fly.retries, 4),
       + 112 (fly.sent, 8), + 1640 (fly.len, 8), + 120 (fly.frame, min n 1514); g_cmd + 40 s (Cmd.st of command s,
       4); g_q + 0 (its 4096 bytes); g_nq + 0 (4);
   - the running view of the stores (m_lost_cgW.v's ml_* for any width and for a span): ios_mix P rdF rd0 is the
     final view rdF on the bytes P marks (written so far) and the entry's view rd0 elsewhere. ios_tw_start (nothing
     written), ios_tw_step (a store of m bytes of v at a row's offset k: TWorldG.v tw_write), ios_tw_fill (a span
     written with the byte list src: TWorldG.v tw_fill), ios_tw_end (every payload byte that P does not mark is
     unchanged), and the tactic ios_unP that splits a P x = false into its ranges;
   - ios_inN: a byte of a range of n bytes is the range's byte j, j < n. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA m_lost_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.

(* ------------------------------------------------------------------ *)
(* G                                                                   *)
(* ------------------------------------------------------------------ *)

(* A payload byte of a row of TMAP_A is a byte of G. *)
Lemma ios_inG_row : forall o b n a, In (o, b, n) TMAP_A -> b <= a < b + n -> inG TG.G_HARNESS a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma ios_tw_in_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof. intros x (o & b & n & Hin & Hx). exact (ios_inG_row o b n x Hin Hx). Qed.

(* The field addresses of iosend_wr, to their offsets in the world. *)
Local Ltac ios_flds :=
  unfold twa_fld, TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_M_host_counter, TW.A_M_next_ka,
    TW.A_M_last_display, TW.A_M_display_sent, TW.A_M_fly_on, TW.A_M_fly_cmd, TW.A_M_fly_counter,
    TW.A_M_fly_retries, TW.A_M_fly_sent, TW.A_M_fly_len, TW.A_M_fly_frame, TW.A_Cmd_st, TW.SZ_M, TW.SZ_GOT,
    TW.SZ_g_cmd, TW.SZ_g_q, TW.SZ_g_nq, TW.SZ_g_last_counter, TC.CMDS_MAX, TC.SPEC_MAX_FRAME in *.

(* The bytes io_send stores are bytes of G: each field lies inside its global's payload (M.fly.frame's first
   min (n, 1514) bytes end at M + 1634 < M + 1648; Cmd.st of command s < 1024 ends at g_cmd + 40924 < g_cmd + 40960). *)
Lemma ios_wr_inG : forall n a, iosend_wr n a -> inG TG.G_HARNESS a.
Proof.
intros n a H. unfold iosend_wr in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[(s & Hs & H)|[H|H]]]]]]]]]]]]]]]]]].
- apply (ios_inG_row _ _ _ a TMAP_A_g_fail_next). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_GOT). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_GOT). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_GOT). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_g_last_counter). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- pose proof (Z.le_min_r n TC.SPEC_MAX_FRAME) as Hmin.
  apply (ios_inG_row _ _ _ a TMAP_A_M). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_g_cmd). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_g_q). ios_flds. lia.
- apply (ios_inG_row _ _ _ a TMAP_A_g_nq). ios_flds. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The bytes of each field io_send stores are bytes of iosend_wr       *)
(* ------------------------------------------------------------------ *)

Lemma ios_wr_fail : forall n a, TA_g_fail_next <= a < TA_g_fail_next + 1 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. left. ios_flds. lia. Qed.

Lemma ios_wr_got_e2 : forall n a, TA_GOT + 196 <= a < TA_GOT + 196 + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 1 right; left. ios_flds. lia. Qed.

Lemma ios_wr_got_e3 : forall n a, TA_GOT + 200 <= a < TA_GOT + 200 + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 2 right; left. ios_flds. lia. Qed.

Lemma ios_wr_got_acks : forall n a, TA_GOT + 204 <= a < TA_GOT + 204 + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 3 right; left. ios_flds. lia. Qed.

Lemma ios_wr_lastc : forall n a, TA_g_last_counter <= a < TA_g_last_counter + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 4 right; left. ios_flds. lia. Qed.

Lemma ios_wr_hostc : forall n a, TA_M + 84 <= a < TA_M + 84 + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 5 right; left. ios_flds. lia. Qed.

Lemma ios_wr_nextka : forall n a, TA_M + 48 <= a < TA_M + 48 + 8 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 6 right; left. ios_flds. lia. Qed.

Lemma ios_wr_lastdisp : forall n a, TA_M + 64 <= a < TA_M + 64 + 8 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 7 right; left. ios_flds. lia. Qed.

Lemma ios_wr_dispsent : forall n a, TA_M + 72 <= a < TA_M + 72 + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 8 right; left. ios_flds. lia. Qed.

Lemma ios_wr_fly_on : forall n a, TA_M + 96 <= a < TA_M + 96 + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 9 right; left. ios_flds. lia. Qed.

Lemma ios_wr_fly_cmd : forall n a, TA_M + 100 <= a < TA_M + 100 + 1 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 10 right; left. ios_flds. lia. Qed.

Lemma ios_wr_fly_counter : forall n a, TA_M + 104 <= a < TA_M + 104 + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 11 right; left. ios_flds. lia. Qed.

Lemma ios_wr_fly_retries : forall n a, TA_M + 108 <= a < TA_M + 108 + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 12 right; left. ios_flds. lia. Qed.

Lemma ios_wr_fly_sent : forall n a, TA_M + 112 <= a < TA_M + 112 + 8 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 13 right; left. ios_flds. lia. Qed.

Lemma ios_wr_fly_len : forall n a, TA_M + 1640 <= a < TA_M + 1640 + 8 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 14 right; left. ios_flds. lia. Qed.

Lemma ios_wr_fly_frame : forall n a, 0 <= n ->
  TA_M + (TW.A_M_fly_frame - TW.OFF_M) <= a < TA_M + (TW.A_M_fly_frame - TW.OFF_M) + Z.min n TC.SPEC_MAX_FRAME ->
  iosend_wr n a.
Proof. intros n a _ H. unfold iosend_wr. do 15 right; left. exact H. Qed.

Lemma ios_wr_cmd_st : forall n s a, 0 <= s < TC.CMDS_MAX -> twa_fld TW.OFF_g_cmd TA_g_cmd (TW.A_Cmd_st s) 4 a ->
  iosend_wr n a.
Proof. intros n s a Hs H. unfold iosend_wr. do 16 right; left. exists s. split; [exact Hs | exact H]. Qed.

Lemma ios_wr_q : forall n a, TA_g_q <= a < TA_g_q + 4096 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 17 right; left. ios_flds. lia. Qed.

Lemma ios_wr_nq : forall n a, TA_g_nq <= a < TA_g_nq + 4 -> iosend_wr n a.
Proof. intros n a H. unfold iosend_wr. do 18 right. ios_flds. lia. Qed.

(* ------------------------------------------------------------------ *)
(* The running view of the stores                                      *)
(* ------------------------------------------------------------------ *)

(* A view that is rdF on the bytes P marks and rd0 elsewhere: the written bytes so far, the entry's on the others. *)
Definition ios_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition ios_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma ios_in_true : forall lo n x, lo <= x < lo + n -> ios_in lo n x = true.
Proof. intros lo n x H. unfold ios_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma ios_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> ios_in lo n x = false.
Proof.
intros lo n x H. unfold ios_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma ios_in_false : forall lo n x, ios_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (ios_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma ios_tw_start : forall rdF rd0 Bw, tw_at TMAP_A rd0 Bw -> tw_at TMAP_A (ios_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_A rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One store of m bytes of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma ios_tw_step : forall rdF rd0 P Bw o b n k ko (m : nat) v,
  tw_at TMAP_A (ios_mix P rdF rd0) Bw -> In (o, b, n) TMAP_A -> ko = o + k -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_A (ios_mix (fun x => P x || ios_in (b + k) (Z.of_nat m) x) rdF rd0) (TW.upd Bw ko (TW.put m v)).
Proof.
intros rdF rd0 P Bw o b n k ko m v H Hin Hko Hk Hkm HV. subst ko.
apply (tw_write TMAP_A (ios_mix P rdF rd0) (ios_mix (fun x => P x || ios_in (b + k) (Z.of_nat m) x) rdF rd0)
  Bw o b n k m v TMAP_A_ok H Hin Hk Hkm).
- intros j Hj. unfold ios_mix. cbv beta.
  rewrite (ios_in_true (b + k) (Z.of_nat m) (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold ios_mix. cbv beta.
  rewrite (ios_in_false' (b + k) (Z.of_nat m) x Hn). rewrite orb_false_r. reflexivity.
Qed.

(* A span at the world offset ko = o + k of the row (o, b, n) written with the bytes src (a memcpy / memset). *)
Lemma ios_tw_fill : forall rdF rd0 P Bw o b n k ko (src : list byte),
  tw_at TMAP_A (ios_mix P rdF rd0) Bw -> In (o, b, n) TMAP_A -> ko = o + k -> 0 <= k ->
  k + Z.of_nat (length src) <= n ->
  (forall i, 0 <= i < Z.of_nat (length src) ->
     rdF (b + k + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))) ->
  tw_at TMAP_A (ios_mix (fun x => P x || ios_in (b + k) (Z.of_nat (length src)) x) rdF rd0) (TW.upd Bw ko src).
Proof.
intros rdF rd0 P Bw o b n k ko src H Hin Hko Hk Hkn HV. subst ko.
apply (tw_fill TMAP_A (ios_mix P rdF rd0)
  (ios_mix (fun x => P x || ios_in (b + k) (Z.of_nat (length src)) x) rdF rd0) Bw o b n k src
  TMAP_A_ok H Hin Hk Hkn).
- intros i Hi. unfold ios_mix. cbv beta.
  rewrite (ios_in_true (b + k) (Z.of_nat (length src)) (b + k + i)) by lia. rewrite orb_true_r. exact (HV i Hi).
- intros x Hx Hn. unfold ios_mix. cbv beta.
  rewrite (ios_in_false' (b + k) (Z.of_nat (length src)) x Hn). rewrite orb_false_r. reflexivity.
Qed.

Lemma ios_tw_end : forall rdF rd0 P Bw, tw_at TMAP_A (ios_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_A x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_A rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_A (ios_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold ios_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac ios_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply ios_in_false in Hq
  end.

(* A byte of a range of n bytes is the range's byte j. *)
Lemma ios_inN : forall b a n, b <= a < b + Z.of_nat n -> exists j, (j < n)%nat /\ a = b + Z.of_nat j.
Proof. intros b a n H. exists (Z.to_nat (a - b)). split; lia. Qed.
