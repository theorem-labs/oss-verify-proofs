(** Segments RD9 and RD10 of the UBSan LLVMFuzzerTestOneInput walk: the SCRIBBLE reader
    (fuzz_codec.c:606-610, k.a = fuzz_u32, then k.bytes[0..8) = fuzz_u8) and the COUNTER reader
    (fuzz_codec.c:611-615, k.b = fuzz_u8, then the same 8-byte loop), from the reader switch to
    run()'s switch. Each loop stores a byte on every pass, the input byte while one is left and 0
    after; the loop lemma is by induction on the passes left. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img codec_main_inv
  codec_main_lib codec_main_rdlib codec_main_rd11.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the record around k.bytes ---- *)

(** The record with k.bytes replaced. *)
Definition kby (k : kcall) (bs : list byte) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k) bs (k_n k) (k_rc k)
          (k_before k) (k_out k) (k_want_rc k) (k_want k) (k_want_len k) (k_want_key k) (k_want_display k).

(** The 40 bytes before k.bytes and the 120 after it. *)
Definition kbpre (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))].
Definition kbpost (k : kcall) : list cell :=
  [C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k); CB 32 (k_out k);
   C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].

Lemma kb_split : forall m s k,
  rw_cells rsegs m (s + -384) (kcall_cells k) ->
  rw_cells rsegs m (s + -384) (kbpre k) /\ rw_cells rsegs m (s + -344) [CB 24 (k_bytes k)] /\
  rw_cells rsegs m (s + -320) (kbpost k).
Proof.
  intros m s k H.
  change (kcall_cells k) with (kbpre k ++ [CB 24 (k_bytes k)] ++ kbpost k) in H.
  apply rw_cells_app_split in H. destruct H as [H1 H].
  apply rw_cells_app_split in H. destruct H as [H2 H3].
  change (Z.of_nat (cells_size (kbpre k))) with 40 in H2, H3.
  change (Z.of_nat (cells_size [CB 24 (k_bytes k)])) with 24 in H3.
  replace (s + -384 + 40) with (s + -344) in H2, H3 by lia.
  replace (s + -344 + 24) with (s + -320) in H3 by lia.
  auto.
Qed.

Lemma kb_join : forall m s k bs,
  rw_cells rsegs m (s + -384) (kbpre k) -> rw_cells rsegs m (s + -344) [CB 24 bs] ->
  rw_cells rsegs m (s + -320) (kbpost k) ->
  rw_cells rsegs m (s + -384) (kcall_cells (kby k bs)).
Proof.
  intros m s k bs H1 H2 H3.
  change (kcall_cells (kby k bs)) with (kbpre k ++ [CB 24 bs] ++ kbpost k).
  apply rw_cells_app_join; [exact H1 |].
  change (Z.of_nat (cells_size (kbpre k))) with 40.
  replace (s + -384 + 40) with (s + -344) by lia.
  apply rw_cells_app_join; [exact H2 |].
  change (Z.of_nat (cells_size [CB 24 bs])) with 24.
  replace (s + -344 + 24) with (s + -320) by lia.
  exact H3.
Qed.

(** The zero byte a pass of the loop overwrites, cut off the zeros still ahead of it. *)
Lemma kr_split : forall m A (r : nat), rw_cells rsegs m A [CB (S r) (repeat (b8 0) (S r))] ->
  rw_cells rsegs m A [C1 (b8 0)] /\ rw_cells rsegs m (A + 1) [CB r (repeat (b8 0) r)].
Proof.
  intros m A r H.
  destruct (rw_cells_CB_split m A (S r) 1 (repeat (b8 0) (S r)) (repeat_length _ _) ltac:(lia) H) as [H1 H2].
  cbn [firstn skipn repeat] in H1, H2. rewrite Nat.sub_succ, Nat.sub_0_r in H2.
  split; [apply rw_cells_CB1; exact H1 | exact H2].
Qed.

(** The bytes stored so far, with the one a pass stored after them. *)
Lemma kd_join : forall m A (j : nat) (done : list byte) (x : byte), length done = j ->
  rw_cells rsegs m A [CB j done] -> rw_cells rsegs m (A + Z.of_nat j) [C1 x] ->
  rw_cells rsegs m A [CB (S j) (done ++ [x])].
Proof.
  intros m A j done x HL H1 H2. subst j.
  apply rw_cells_C1B in H2.
  apply (rw_cells_CB_cat m A (S (length done)) done [x]); [cbn [length]; lia | lia | exact H1 |].
  rewrite Nat.sub_succ_l, Nat.sub_diag by lia. exact H2.
Qed.

(** The eight bytes of the loop and the sixteen zeros after them. *)
Lemma kb_fin : forall m A bs, length bs = 8%nat ->
  rw_cells rsegs m A [CB 8 bs] -> rw_cells rsegs m (A + 8) [CB 16 (repeat (b8 0) 16)] ->
  rw_cells rsegs m A [CB 24 (bs ++ repeat (b8 0) 16)].
Proof.
  intros m A bs HL H1 H2.
  apply (rw_cells_CB_cat m A 24 bs (repeat (b8 0) 16)); rewrite HL; [reflexivity | lia | exact H1 | exact H2].
Qed.

(** What run() accepts of the SCRIBBLE and COUNTER records, whatever the 24 bytes. *)
Lemma rec_wf_kby : forall kind i a b bs, (kind = 9 \/ kind = 10) -> 0 <= i <= 2 ->
  0 <= a < 2 ^ 32 -> 0 <= b < 256 -> length bs = 24%nat -> rec_wf (kby (kfl (k_head kind i) a b 0 0) bs).
Proof.
  intros kind i a b bs HK HI Ha Hb HL.
  unfold rec_wf, kby, kfl, k_head.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display].
  split; [lia|].
  split.
  { unfold desk_at. cbn [k_p k_desk].
    assert (EI : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct EI as [-> | [-> | ->]]; cbn.
    - left. split; reflexivity.
    - right. left. split; reflexivity.
    - right. right. split; reflexivity. }
  do 7 (split; [reflexivity|]).
  unfold reader_ok.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold zb; rewrite length_map; exact HL|].
  split; [apply zb_range|].
  split; [lia|]. split; [intros; lia|]. split; [intros; lia|]. intros; lia.
Qed.

(** A record whose every byte content run() accepts. *)
Definition kwb (k : kcall) : Prop := forall bs, length bs = 24%nat -> rec_wf (kby k bs).

Lemma kwb_9 : forall i a, 0 <= i <= 2 -> 0 <= a < 2 ^ 32 -> kwb (kfl (k_head 9 i) a 0 0 0).
Proof. intros i a HI Ha bs HL. apply rec_wf_kby; [left; reflexivity | exact HI | exact Ha | lia | exact HL]. Qed.

Lemma kwb_10 : forall i b, 0 <= i <= 2 -> 0 <= b < 256 -> kwb (kfl (k_head 10 i) 0 b 0 0).
Proof. intros i b HI Hb bs HL. apply rec_wf_kby; [right; reflexivity | exact HI | lia | exact Hb | exact HL]. Qed.

Section RD910.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** The loop's [sb]: the stepper leaves the write as [le1 v]; as the one byte it is, the cell
    writer puts it in the [C1] cell of k.bytes[j]. *)
Ltac byte_store := zstep; unfold le1; cbn [Z_to_le_bytes]; mem_after_store.

(** The arithmetic side goals of a loop cut, once the frame goals have fixed every word. *)
Ltac loop_side := first [ (rewrite length_app; cbn [length]; lia) | reflexivity | lia
                        | (rewrite unsigned_lit by lia; lia) ].

(** The end of a loop at 0x14390: k.bytes is the eight bytes the loop stored and sixteen zeros. *)
Ltac loop_end k KW KP KD KR1 KT FIN HL x0 x1 HX0 HX1 :=
  replace (bv_unsigned (c_sp E) + -344 + Z.of_nat 7 + 1) with (bv_unsigned (c_sp E) + -344 + 8) in KR1 by lia;
  let KB := fresh "KB" in let FK := fresh "FK" in
  lazymatch type of KD with rw_cells _ _ _ [CB _ ?D] =>
    pose proof (kb_fin _ _ D ltac:(rewrite length_app, HL; reflexivity) KD KR1) as KB;
    pose proof (kb_join _ (bv_unsigned (c_sp E)) k _ KP KB KT) as FK;
    try (rewrite <- (Z_to_bv_bv_unsigned x0), <- (Z_to_bv_bv_unsigned x1), HX0, HX1 in FIN);
    lazymatch type of FIN with rw_cells _ _ _ [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)] =>
      eapply (rd_end E _ _ (kby k (D ++ repeat (b8 0) 16)) CZ RZ); [ exact ENV | exact (RUN _) | .. ];
      first [ (apply KW; rewrite !length_app, repeat_length, HL; reflexivity)
            | eassumption
            | lia ]
    end
  end.

(** ---- RD9: the loop 0x13f70-0x13fa4, a0 the cursor, a1 in.n, a2 the passes left, a3 &k.bytes[j] ---- *)

(** The loop head after j passes, S kk passes left: k.bytes[0..j) holds the j bytes the passes
    stored ([done]; run() accepts any bytes, so the invariant does not fix them), k.bytes[j..24)
    still the head's zeros, and the cursor and in.n, in their registers and in memory, still
    describe the input ([cz - p + rz] is its length). By induction on kk. *)
Lemma rd9_loop : forall (kk : nat) (k : kcall) (j : nat) (done : list byte) (cz rz ops : Z)
    (ra' t0' t1' t2' w0 w1 wc pa a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' x0 x1 : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwb k -> (S kk + j = 8)%nat -> length done = j ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned w0 = cz -> bv_unsigned w1 = rz -> bv_unsigned x0 = cz -> bv_unsigned x1 = rz ->
  bv_unsigned wc = Z.of_nat (S kk) -> bv_unsigned pa = bv_unsigned (c_sp E) + -344 + Z.of_nat j ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kbpre k) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -344) [CB j done] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -344 + Z.of_nat j) [CB (24 - j) (repeat (b8 0) (24 - j))] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -320) (kbpost k) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 x0; C8 x1] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' w0 w1 wc pa a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x13f70 m1).
Proof.
  induction kk as [| kk IH];
    intros k j done cz rz ops ra' t0' t1' t2' w0 w1 wc pa a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' x0 x1
      u0 pj tj plj m1 KW HJ HL Ho1 Ho2 HW0 HW1 HX0 HX1 HWC HPA Hcz Hrz Hcr
      F0 F8 KP KD KR KT FIN FPD FTX FPL FSV ST MU WM HMI;
    rd_pre; unfold rd_st; unfold kbpre in KP; unfold kbpost in KT;
    replace (24 - j)%nat with (S (23 - j)) in KR by lia;
    destruct (kr_split _ _ _ KR) as [KC KR1]; clear KR;
    rewrite <- HPA in KC.
  - (* the last pass, then 0x13fa8: j 0x14390 *)
    assert (EJ : j = 7%nat) by lia. rewrite EJ in *. clear EJ.
    destruct (Z.eq_dec rz 0) as [R0 | R0]; [rewrite R0 in *; clear R0 |].
    all: rd_p0.
    all: zstep; drive 0x13f98; byte_store; drive 0x14390.
    all: lazymatch goal with KC : rw_cells _ _ _ [C1 ?x] |- _ =>
           let KD' := fresh "KD" in
           rewrite HPA in KC;
           pose proof (kd_join _ _ _ done x HL KD KC) as KD'; clear KD KC;
           loop_end k KW KP KD' KR1 KT FIN HL x0 x1 HX0 HX1
         end.
  - (* a pass, and back to the loop head *)
    destruct (Z.eq_dec rz 0) as [R0 | R0]; [rewrite R0 in *; clear R0 |].
    all: rd_p0.
    all: zstep; drive 0x13f98; byte_store; drive 0x13f70.
    all: replace (bv_unsigned (c_sp E) + -344 + Z.of_nat j + 1)
           with (bv_unsigned (c_sp E) + -344 + Z.of_nat (S j)) in KR1 by lia.
    all: lazymatch goal with KC : rw_cells _ _ _ [C1 ?x] |- _ =>
           let KD' := fresh "KD" in
           rewrite HPA in KC;
           pose proof (kd_join _ _ _ done x HL KD KC) as KD'; clear KD KC
         end.
    + eapply (IH k (S j) _ cz 0 ops).
      all: try eassumption.
      all: loop_side.
    + eapply (IH k (S j) _ (cz + 1) (rz - 1) ops).
      all: try eassumption.
      all: loop_side.
Qed.

(** ---- RD10: the loop 0x13df8-0x13e2c, a0 in.n, a1 the cursor, a2 the passes left, a3 &k.bytes[j] ---- *)

(** The invariant of [rd9_loop], with in.n and the cursor in the other two registers. *)
Lemma rd10_loop : forall (kk : nat) (k : kcall) (j : nat) (done : list byte) (cz rz ops : Z)
    (ra' t0' t1' t2' w0 w1 wc pa a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' x0 x1 : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwb k -> (S kk + j = 8)%nat -> length done = j ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned w0 = cz -> bv_unsigned w1 = rz -> bv_unsigned x0 = cz -> bv_unsigned x1 = rz ->
  bv_unsigned wc = Z.of_nat (S kk) -> bv_unsigned pa = bv_unsigned (c_sp E) + -344 + Z.of_nat j ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kbpre k) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -344) [CB j done] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -344 + Z.of_nat j) [CB (24 - j) (repeat (b8 0) (24 - j))] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -320) (kbpost k) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 x0; C8 x1] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' w1 w0 wc pa a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x13df8 m1).
Proof.
  induction kk as [| kk IH];
    intros k j done cz rz ops ra' t0' t1' t2' w0 w1 wc pa a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' x0 x1
      u0 pj tj plj m1 KW HJ HL Ho1 Ho2 HW0 HW1 HX0 HX1 HWC HPA Hcz Hrz Hcr
      F0 F8 KP KD KR KT FIN FPD FTX FPL FSV ST MU WM HMI;
    rd_pre; unfold rd_st; unfold kbpre in KP; unfold kbpost in KT;
    replace (24 - j)%nat with (S (23 - j)) in KR by lia;
    destruct (kr_split _ _ _ KR) as [KC KR1]; clear KR;
    rewrite <- HPA in KC.
  - (* the last pass, then 0x13e30: j 0x14390 *)
    assert (EJ : j = 7%nat) by lia. rewrite EJ in *. clear EJ.
    destruct (Z.eq_dec rz 0) as [R0 | R0]; [rewrite R0 in *; clear R0 |].
    all: rd_p0.
    all: zstep; drive 0x13e20; byte_store; drive 0x14390.
    all: lazymatch goal with KC : rw_cells _ _ _ [C1 ?x] |- _ =>
           let KD' := fresh "KD" in
           rewrite HPA in KC;
           pose proof (kd_join _ _ _ done x HL KD KC) as KD'; clear KD KC;
           loop_end k KW KP KD' KR1 KT FIN HL x0 x1 HX0 HX1
         end.
  - (* a pass, and back to the loop head *)
    destruct (Z.eq_dec rz 0) as [R0 | R0]; [rewrite R0 in *; clear R0 |].
    all: rd_p0.
    all: zstep; drive 0x13e20; byte_store; drive 0x13df8.
    all: replace (bv_unsigned (c_sp E) + -344 + Z.of_nat j + 1)
           with (bv_unsigned (c_sp E) + -344 + Z.of_nat (S j)) in KR1 by lia.
    all: lazymatch goal with KC : rw_cells _ _ _ [C1 ?x] |- _ =>
           let KD' := fresh "KD" in
           rewrite HPA in KC;
           pose proof (kd_join _ _ _ done x HL KD KC) as KD'; clear KD KC
         end.
    + eapply (IH k (S j) _ cz 0 ops).
      all: try eassumption.
      all: loop_side.
    + eapply (IH k (S j) _ (cz + 1) (rz - 1) ops).
      all: try eassumption.
      all: loop_side.
Qed.

(** ---- the entries: the scalar read, then the loop with no byte stored ---- *)

(** At a loop head with the scalar stored: cut the record around k.bytes and start the loop with
    no byte stored. The side goals are left: the frame ones first (they fix the cursor words). *)
Ltac to_loop kind i LOOP :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384)
           (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?A) :: C4 (Z_to_bv 64 ?B) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)] |- _ =>
      let KP := fresh "KP" in let KB := fresh "KB" in let KT := fresh "KT" in
      let KD := fresh "KD" in let KR := fresh "KR" in
      destruct (kb_split _ _ (kfl (k_head kind i) A B 0 0) FK) as (KP & KB & KT); clear FK;
      destruct (rw_cells_CB_split _ _ 24 0 _ (repeat_length _ _) ltac:(lia) KB) as [KD KR]; clear KB;
      eapply (LOOP 7%nat (kfl (k_head kind i) A B 0 0) 0%nat [] CZ RZ)
  end.

(** 0x13674-0x13710, 0x13d80-0x13d90, 0x13e5c-0x13e60, 0x13f48-0x13f6c: k.a = fuzz_u32. *)
Lemma rd9_a : forall (i cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  0 <= i <= 2 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (k_head 9 i)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x13674 m1).
Proof.
  intros i cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    HI Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x13f70.
  all: to_loop 9 i rd9_loop.
  all: try eassumption.
  all: first [ (apply kwb_9; [lia | bnd]) | loop_side ].
Qed.

(** 0x13a9c-0x13ac4, 0x13de4-0x13df4: k.b = fuzz_u8. *)
Lemma rd10_b : forall (i cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  0 <= i <= 2 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (k_head 10 i)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x13a9c m1).
Proof.
  intros i cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    HI Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (Z.eq_dec rz 0) as [R | R]; [subst rz |].
  all: rd_p0.
  all: drive 0x13df8.
  all: to_loop 10 i rd10_loop.
  all: try eassumption.
  all: first [ (apply kwb_10; [lia | bnd]) | loop_side ].
Qed.

(** The reader switch's entries: T1[9] = 0x13674, T1[10] = 0x13a9c. *)
Lemma rd9_ok : forall i, 0 <= i <= 2 -> rd_ok E n 9 i.
Proof.
  intros i HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC1 HCN FR ST MU WM HMI.
  replace (pc_rd 9) with 0x13674 by reflexivity.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  exact (rd9_a i (bv_unsigned cur) (bv_unsigned rem) ops
           ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
           u0 pj tj plj m1 HI Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
           F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

Lemma rd10_ok : forall i, 0 <= i <= 2 -> rd_ok E n 10 i.
Proof.
  intros i HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC1 HCN FR ST MU WM HMI.
  replace (pc_rd 10) with 0x13a9c by reflexivity.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  exact (rd10_b i (bv_unsigned cur) (bv_unsigned rem) ops
           ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
           u0 pj tj plj m1 HI Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
           F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

End RD910.

Lemma codec_main_rd9 : seg_rd9_stmt.
Proof.
  unfold seg_rd9_stmt. intros E n ENV RUN i HI. split.
  - exact (rd9_ok E n ENV RUN i HI).
  - exact (rd10_ok E n ENV RUN i HI).
Qed.
