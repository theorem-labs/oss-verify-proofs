(* Support for the tagged path of case 4 of the ubsan op loop of LLVMFuzzerTestOneInput (op_submit's g_raw == 0
   arm, fuzz/fuzz_transport.c:1085-1121), walked in U/Prog/T/LLVMFuzzerTestOneInput_op4_tag.v:

   - the model's arm (U/Prog/T/LLVMFuzzerTestOneInput_op4_mid.v op4_tagged_m) named piece by piece (t4_len,
     t4_n, t4_cb, t4_sys, t4_atopt, t4_want, t4_cs, t4_Bw, t4_rec), restated as t4_run (by conversion) and split
     at its five calls (t4_split);
   - the bytes of llvm_frame's j60 cell at Sp + 0x60 (the struct diginet_cmd of :1070) and of its j10 cell at
     Sp + 0x10: reads, byte stores, a memcpy into an offset of j60, and the loop's llvm_mem around them;
   - a store into the world (the g_q / g_nq / g_ncmd writes of :1115-1120) as llvm_mem's upd;
   - the arithmetic of the system-family scan (:1096): the machine's loop over the struct's bytes against
     DgnSpec's system_at / sys_hit. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem
  TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- small arithmetic and list facts *)

Lemma t4_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma t4_bytes_one : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof. intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

Lemma t4_land127 : forall x, 0 <= x -> Z.land x 127 = x mod 128.
Proof. intros x Hx. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma t4_shiftr7 : forall x, 0 <= x < 1024 -> Z.land (Z.shiftr x 7) 127 = Z.shiftr x 7.
Proof.
  intros x Hx. rewrite t4_land127 by (apply Z.shiftr_nonneg; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 7) with 128.
  apply Z.mod_small. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma t4_put1 : forall v, put 1 v = [b8 v].
Proof.
  intros v. pose proof (length_put 1 v) as L.
  destruct (put 1 v) as [|x r] eqn:E; cbn in L; [lia|].
  destruct r as [|y r']; cbn in L; [|lia].
  pose proof (u_at_put 1 v) as U. rewrite E in U.
  unfold u_at in U. rewrite (sub_all [x] 1 eq_refl) in U. rewrite t4_bytes_one in U.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in U.
  f_equal. apply bv_eq. rewrite U. unfold b8. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma t4_put4_mod : forall x, put 4 (x mod 2 ^ 32) = put 4 x.
Proof.
  intros x. unfold put. rewrite <- (Z_to_le_bytes_mod 4 x 32) by lia. reflexivity.
Qed.

Lemma t4_put4_swrap : forall x, put 4 (bv_swrap 32 x) = put 4 x.
Proof.
  intros x. rewrite <- (t4_put4_mod x), <- (t4_put4_mod (bv_swrap 32 x)). f_equal.
  unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Zminus_mod_idemp_l.
  replace (x + 2 ^ 31 - 2 ^ 31) with x by lia. reflexivity.
Qed.

Lemma t4_sub1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l (b8 0)].
Proof.
  induction l as [|d l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma t4_u_at1 : forall (l : list byte) i, 0 <= i -> (Z.to_nat i < length l)%nat ->
  u_at l i 1 = at8 l (Z.to_nat i).
Proof.
  intros l i Hi Hl. unfold u_at, sub. rewrite t4_sub1 by exact Hl.
  rewrite t4_bytes_one. reflexivity.
Qed.

Lemma t4_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros n i d Hi.
  - rewrite firstn_nil. destruct i; reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; cbn [nth]; [reflexivity|].
    apply IH. lia.
Qed.

Lemma t4_skipn_rep_app : forall (k m : nat) (R : list byte), (k <= m)%nat ->
  skipn k (repeat (b8 0) m ++ R) = repeat (b8 0) (m - k) ++ R.
Proof.
  induction k as [|k IH]; intros m R H.
  - cbn [skipn]. rewrite Nat.sub_0_r. reflexivity.
  - destruct m as [|m]; [lia|]. cbn [repeat app skipn Nat.sub]. apply IH. lia.
Qed.

Lemma t4_upd_app_l : forall (a b v : list byte) k, 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length a) -> upd (a ++ b) k v = upd a k v ++ b.
Proof.
  intros a b v k Hk Hl. unfold upd.
  rewrite firstn_app, skipn_app.
  replace (Z.to_nat k - length a)%nat with 0%nat by lia.
  replace (Z.to_nat k + length v - length a)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma t4_upd_app_r : forall (a b v : list byte) k j, 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length b) -> j = Z.of_nat (length a) + k ->
  upd (a ++ b) j v = a ++ upd b k v.
Proof.
  intros a b v k j Hk Hl ->. unfold upd.
  rewrite firstn_app, skipn_app.
  rewrite (firstn_all2 a) by lia.
  replace (Z.to_nat (Z.of_nat (length a) + k) - length a)%nat with (Z.to_nat k) by lia.
  rewrite (skipn_all2 a) by lia.
  replace (Z.to_nat (Z.of_nat (length a) + k) + length v - length a)%nat
    with (Z.to_nat k + length v)%nat by lia.
  cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma t4_upd0 : forall (bs v : list byte) n, length v = n -> (n <= length bs)%nat ->
  upd bs 0 v = v ++ skipn n bs.
Proof. intros bs v n Hv Hn. unfold upd. cbn [Z.to_nat firstn]. rewrite Hv. reflexivity. Qed.

Lemma t4_upd_adj : forall (bs v w : list byte) k, 0 <= k ->
  k + Z.of_nat (length v) + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  upd (upd bs k v) (k + Z.of_nat (length v)) w = upd bs k (v ++ w).
Proof.
  intros bs v w k Hk Hl.
  assert (EU : upd bs k v = (firstn (Z.to_nat k) bs ++ v) ++ skipn (Z.to_nat k + length v) bs)
    by (unfold upd; rewrite <- app_assoc; reflexivity).
  assert (LP : length (firstn (Z.to_nat k) bs ++ v) = (Z.to_nat k + length v)%nat)
    by (rewrite app_length, firstn_length; lia).
  unfold upd at 1. rewrite EU.
  replace (Z.to_nat (k + Z.of_nat (length v))) with (length (firstn (Z.to_nat k) bs ++ v)) by lia.
  rewrite firstn_app_exact.
  rewrite skipn_app, (skipn_all2 (firstn (Z.to_nat k) bs ++ v)) by lia.
  replace (length (firstn (Z.to_nat k) bs ++ v) + length w - length (firstn (Z.to_nat k) bs ++ v))%nat
    with (length w) by lia.
  rewrite skipn_skipn. cbn [app].
  unfold upd. rewrite app_length.
  replace (Z.to_nat k + (length v + length w))%nat with (length w + (Z.to_nat k + length v))%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------- the model's tagged arm, by name *)

Definition t4_B2 (B1 : list byte) : list byte :=
  upd B1 (A_Cmd_st (g_ncmd B1)) (repeat (b8 0) (Z.to_nat Cmd_ESZ)).

Definition t4_len (D : list byte) (c3 : fuzz_in) : Z := snd (fuzz_u8_m D c3) mod 22 + 3.
Definition t4_c4 (D : list byte) (c3 : fuzz_in) : fuzz_in := fst (fuzz_u8_m D c3).
Definition t4_tk (D : list byte) (c3 : fuzz_in) : fuzz_in * Z * Z :=
  fuzz_take_m (t4_c4 D c3) (t4_len D c3 - 3).
Definition t4_c5 (D : list byte) (c3 : fuzz_in) : fuzz_in := fst (fst (t4_tk D c3)).
Definition t4_off (D : list byte) (c3 : fuzz_in) : Z := snd (fst (t4_tk D c3)).
Definition t4_n (D : list byte) (c3 : fuzz_in) : Z := snd (t4_tk D c3).

Definition t4_cb (B1 D : list byte) (c3 : fuzz_in) : list byte :=
  [b8 TAG; b8 (Z.land (g_ncmd B1) 0x7f); b8 (Z.land (Z.shiftr (g_ncmd B1) 7) 0x7f)]
  ++ sub D (t4_off D c3) (Z.to_nat (t4_n D c3)) ++ repeat (b8 0) (Z.to_nat (21 - t4_n D c3)).

Definition t4_sys (B1 D : list byte) (c3 : fuzz_in) : bool :=
  system_at (firstn (Z.to_nat (t4_len D c3)) (t4_cb B1 D c3)).

Definition t4_atopt (B1 : list byte) (key : Z) : option Z :=
  if negb (h_coalescable_m key =? 0)
  then submit_find_at (S (Z.to_nat CMDS_MAX)) (t4_B2 B1) key 0 else Some (-1).

Definition t4_want (B1 D : list byte) (c3 : fuzz_in) (at_ : Z) : Z :=
  if t4_sys B1 D c3 then SPEC_E_REFUSED
  else if (at_ <? 0) && (g_nq (t4_B2 B1) =? QUEUE_MAX) then SPEC_E_SPACE else SPEC_OK.

Definition t4_cs (B1 D : list byte) (c3 : fuzz_in) (display key : Z) : list byte :=
  cmd_struct (t4_cb B1 D c3) (t4_len D c3) display key.

Definition t4_Bw (B5 : list byte) (serial key display len : Z) (cb : list byte) : list byte :=
  set_Cmd_bytes (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B5 serial PENDING) serial key)
                   serial display) serial len) serial (firstn (Z.to_nat len) cb).

Definition t4_rec (B5 : list byte) (serial key display len : Z) (cb : list byte) (at_ : Z) : option (list byte) :=
  if 0 <=? at_ then
    (if CMDS_MAX <=? Q_at (t4_Bw B5 serial key display len cb) at_ then None
     else Some (set_Q_at (set_Cmd_st (t4_Bw B5 serial key display len cb)
                            (Q_at (t4_Bw B5 serial key display len cb) at_) REPLACED) at_ serial))
  else
    (if CMDS_MAX <=? g_nq (t4_Bw B5 serial key display len cb) then None
     else Some (set_g_nq (set_Q_at (t4_Bw B5 serial key display len cb)
                            (g_nq (t4_Bw B5 serial key display len cb)) serial)
                  ((g_nq (t4_Bw B5 serial key display len cb) + 1) mod 2 ^ 32))).

(* op4_tagged_m with every piece named; the two are equal by conversion once the two cursor pairs are split *)
Definition t4_run (B1 D : list byte) (c3 : fuzz_in) (before display key : Z) : option (list byte * fuzz_in) :=
  if CMDS_MAX <=? g_ncmd B1 then None else
  match t4_atopt B1 key with
  | Some at_ =>
    match diginet_session_submit_m (t4_B2 B1) (t4_cs B1 D c3 display key) with
    | Some (B3, rc) =>
      match check_refusal_submit_m B3 (t4_cs B1 D c3 display key) rc before with
      | Some (B4, _) =>
        match (if t4_sys B1 D c3 then Some (B4, tt)
               else check_latest_submit_m B4 rc (t4_want B1 D c3 at_)) with
        | Some (B5, _) =>
          match (if t4_want B1 D c3 at_ =? SPEC_OK
                 then t4_rec B5 (g_ncmd B1) key display (t4_len D c3) (t4_cb B1 D c3) at_
                 else Some B5) with
          | Some B6 =>
            match settle_m (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) 0 with
            | Some (B8, _) => Some (B8, t4_c5 D c3)
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Lemma t4_run_eq : forall B1 D c3 before display key,
  op4_tagged_m B1 D c3 before display key = t4_run B1 D c3 before display key.
Proof.
  intros B1 D c3 before display key.
  cbv beta zeta delta [op4_tagged_m t4_run t4_B2 t4_atopt t4_cs t4_cb t4_sys t4_want t4_len
    t4_n t4_off t4_c5 t4_c4 t4_tk t4_rec t4_Bw].
  destruct (fuzz_u8_m D c3) as [c4 lb]. cbn [fst snd].
  destruct (fuzz_take_m c4 (lb mod 22 + 3 - 3)) as [[c5 off] n]. cbn [fst snd].
  reflexivity.
Qed.

Lemma t4_inv_wc : forall (X Y : list byte) (u v : fuzz_in), Some (X, u) = Some (Y, v) -> X = Y /\ u = v.
Proof. intros X Y u v H. injection H as E1 E2. split; [exact E1 | exact E2]. Qed.

Lemma t4_split : forall B1 D c3 before display key B8 c5,
  op4_tagged_m B1 D c3 before display key = Some (B8, c5) ->
  c5 = t4_c5 D c3 /\ g_ncmd B1 < CMDS_MAX /\
  exists (at_ rc : Z) (B3 B4 B5 B6 : list byte),
    t4_atopt B1 key = Some at_ /\
    diginet_session_submit_m (t4_B2 B1) (t4_cs B1 D c3 display key) = Some (B3, rc) /\
    check_refusal_submit_m B3 (t4_cs B1 D c3 display key) rc before = Some (B4, tt) /\
    (if t4_sys B1 D c3 then Some (B4, tt)
     else check_latest_submit_m B4 rc (t4_want B1 D c3 at_)) = Some (B5, tt) /\
    (if t4_want B1 D c3 at_ =? SPEC_OK
     then t4_rec B5 (g_ncmd B1) key display (t4_len D c3) (t4_cb B1 D c3) at_
     else Some B5) = Some B6 /\
    settle_m (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) 0 = Some (B8, tt).
Proof.
  intros B1 D c3 before display key B8 c5 H.
  rewrite t4_run_eq in H. unfold t4_run in H.
  destruct (Z.leb_spec CMDS_MAX (g_ncmd B1)) as [HC|HC]; [discriminate H|].
  destruct (t4_atopt B1 key) as [at_|] eqn:EA; [|discriminate H].
  destruct (diginet_session_submit_m (t4_B2 B1) (t4_cs B1 D c3 display key)) as [[B3 rc]|] eqn:ES;
    [|discriminate H].
  destruct (check_refusal_submit_m B3 (t4_cs B1 D c3 display key) rc before) as [[B4 u4]|] eqn:ER;
    [|discriminate H].
  destruct u4.
  destruct (if t4_sys B1 D c3 then Some (B4, tt)
            else check_latest_submit_m B4 rc (t4_want B1 D c3 at_)) as [[B5 u5]|] eqn:EL;
    [|discriminate H].
  destruct u5.
  destruct (if t4_want B1 D c3 at_ =? SPEC_OK
            then t4_rec B5 (g_ncmd B1) key display (t4_len D c3) (t4_cb B1 D c3) at_
            else Some B5) as [B6|] eqn:E6; [|discriminate H].
  destruct (settle_m (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) 0) as [[B8' u8]|] eqn:E8;
    [|discriminate H].
  destruct u8.
  apply t4_inv_wc in H. destruct H as [EB EC].
  split; [symmetry; exact EC|]. split; [exact HC|].
  exists at_, rc, B3, B4, B5, B6.
  split; [first [reflexivity | exact EA]|]. split; [first [reflexivity | exact ES]|].
  split; [first [reflexivity | exact ER]|]. split; [first [reflexivity | exact EL]|].
  split; [first [reflexivity | exact E6]|].
  first [ rewrite EB; reflexivity | rewrite E8, EB; reflexivity | exact E8 ].
Qed.

(* the cursor after the arm *)
Lemma t4_cursor_u8 : forall D c, llvm_cursor D c -> llvm_cursor D (fst (fuzz_u8_m D c)).
Proof.
  intros D c (H1 & H2 & H3). unfold llvm_cursor, fuzz_u8_m.
  destruct (Z.eqb_spec (fi_n c) 0) as [E|E]; cbn [fst fi_off fi_n]; lia.
Qed.

Lemma t4_cursor_take : forall D c w, llvm_cursor D c -> 0 <= w ->
  llvm_cursor D (fst (fst (fuzz_take_m c w))).
Proof.
  intros D c w (H1 & H2 & H3) Hw. unfold fuzz_take_m, llvm_cursor. cbn [fst snd fi_off fi_n].
  destruct (Z.ltb_spec w (fi_n c)); lia.
Qed.

Lemma t4_cb_len : forall B1 D c3, 0 <= t4_off D c3 -> 0 <= t4_n D c3 <= 21 ->
  t4_off D c3 + t4_n D c3 <= Z.of_nat (length D) ->
  length (t4_cb B1 D c3) = 24%nat.
Proof.
  intros B1 D c3 Ho Hn HD. unfold t4_cb.
  assert (LS : length (sub D (t4_off D c3) (Z.to_nat (t4_n D c3))) = Z.to_nat (t4_n D c3))
    by (apply length_sub; lia).
  rewrite !app_length, repeat_length, LS. cbn [length]. lia.
Qed.

Lemma t4_cs_len : forall B1 D c3 display key, 0 <= t4_off D c3 -> 0 <= t4_n D c3 <= 21 ->
  t4_off D c3 + t4_n D c3 <= Z.of_nat (length D) ->
  length (t4_cs B1 D c3 display key) = 32%nat.
Proof.
  intros B1 D c3 display key Ho Hn HD. unfold t4_cs, cmd_struct.
  rewrite !app_length, length_put, (t4_cb_len B1 D c3 Ho Hn HD). cbn [length]. lia.
Qed.

(* ---------------------------------------------------------------- the system-family scan *)

Lemma t4_sys_val : forall (cb rest : list byte) (len : Z), length cb = 24%nat -> 3 <= len <= 24 ->
  existsb (sys_hit (cb ++ rest)) (seq 0 (Z.to_nat len - 3)) = system_at (firstn (Z.to_nat len) cb).
Proof.
  intros cb rest len Lcb Hl.
  assert (LF : length (firstn (Z.to_nat len) cb) = Z.to_nat len) by (rewrite firstn_length; lia).
  unfold system_at. rewrite LF.
  assert (HE : forall i, (i + 3 < Z.to_nat len)%nat ->
            sys_hit (cb ++ rest) i = sys_hit (firstn (Z.to_nat len) cb) i).
  { intros i Hi. unfold sys_hit, at8, bz.
    rewrite !(app_nth1 cb rest) by lia. rewrite !t4_nth_firstn by lia. reflexivity. }
  apply eq_true_iff_eq. rewrite !existsb_exists.
  split; intros [i [Hi Hh]]; exists i; apply in_seq in Hi; (split; [apply in_seq; lia|]).
  - rewrite <- (HE i ltac:(lia)). exact Hh.
  - rewrite (HE i ltac:(lia)). exact Hh.
Qed.

Lemma t4_sys_step : forall (b : list byte) (i : nat),
  existsb (sys_hit b) (seq 0 (S i)) = (existsb (sys_hit b) (seq 0 i) || sys_hit b i)%bool.
Proof.
  intros b i. rewrite seq_S, existsb_app. cbn [existsb orb].
  rewrite ?Nat.add_0_l, orb_false_r. reflexivity.
Qed.

(* ---------------------------------------------------------------- the loop's frame, flat *)

Definition t4_pre : list byte :=
  le8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) ++ le8 (Z_to_bv 64 (2 ^ 32 - 3)).

Definition t4_mid (Sp : Z) (jio : list byte) : list byte :=
  le8 (Z_to_bv 64 0x610f) ++ le8 (Z_to_bv 64 0xffff) ++
  le8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))) ++ le8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96))) ++ jio.

Lemma t4_pre_len : length t4_pre = 16%nat.
Proof. unfold t4_pre. rewrite app_length, !length_le8. reflexivity. Qed.

Lemma t4_mid_len : forall Sp jio, length jio = 32%nat -> length (t4_mid Sp jio) = 64%nat.
Proof. intros Sp jio H. unfold t4_mid. rewrite !app_length, !length_le8, H. reflexivity. Qed.

Lemma t4_sav_len : forall regs0, length (cells_bytes (llvm_saved regs0)) = 104%nat.
Proof.
  intros regs0. unfold llvm_saved.
  rewrite cells_bytes_length by (cbn [cells_wf cell_wf]; tauto). reflexivity.
Qed.

Lemma t4_frame_size : forall regs0 Sp j10 jio j60,
  cells_size (llvm_frame regs0 Sp j10 jio j60) = 240%nat.
Proof. intros. unfold llvm_frame, llvm_saved. reflexivity. Qed.

Lemma t4_frame_wf : forall regs0 Sp j10 jio j60,
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  cells_wf (llvm_frame regs0 Sp j10 jio j60).
Proof.
  intros regs0 Sp j10 jio j60 H1 H2 H3. unfold llvm_frame, llvm_saved.
  cbn [cells_wf cell_wf app]. tauto.
Qed.

Lemma t4_fb : forall regs0 Sp j10 jio j60,
  cells_bytes (llvm_frame regs0 Sp j10 jio j60)
  = t4_pre ++ j10 ++ t4_mid Sp jio ++ j60 ++ cells_bytes (llvm_saved regs0).
Proof.
  intros. unfold llvm_frame. rewrite cells_bytes_app. unfold t4_pre, t4_mid.
  cbn [cells_bytes cbytes]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma t4_frame_blen : forall regs0 Sp j10 jio j60,
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  length (cells_bytes (llvm_frame regs0 Sp j10 jio j60)) = 240%nat.
Proof.
  intros regs0 Sp j10 jio j60 H1 H2 H3.
  rewrite cells_bytes_length by (apply t4_frame_wf; assumption). apply t4_frame_size.
Qed.

(* the two scratch cells of the frame, as bytes *)
Lemma t4_frame_j : forall m regs0 Sp j10 jio j60,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  bytes_at rsegs m (Sp + 16) j10 /\ bytes_at rsegs m (Sp + 96) j60.
Proof.
  intros m regs0 Sp j10 jio j60 HF H1 H2 H3.
  pose proof (t4_frame_blen regs0 Sp j10 jio j60 H1 H2 H3) as LB.
  destruct HF as [[_ Hb] _]. rewrite t4_fb in Hb. rewrite t4_fb in LB.
  rewrite !app_length, t4_pre_len, (t4_mid_len Sp jio H2), H1, H3, (t4_sav_len regs0) in LB.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb1]. rewrite t4_pre_len in Hb1.
  pose proof Hb1 as Hb2.
  apply bytes_at_app in Hb1. destruct Hb1 as [Hb1 _].
  apply bytes_at_app in Hb2. destruct Hb2 as [_ Hb2]. rewrite H1 in Hb2.
  apply bytes_at_app in Hb2. destruct Hb2 as [_ Hb2]. rewrite (t4_mid_len Sp jio H2) in Hb2.
  apply bytes_at_app in Hb2. destruct Hb2 as [Hb2 _].
  split.
  - replace (Sp + 16) with (Sp + Z.of_nat 16) by lia. exact Hb1.
  - replace (Sp + 96) with (Sp + Z.of_nat 16 + Z.of_nat 16 + Z.of_nat 64) by lia. exact Hb2.
Qed.

Lemma t4_sub_bytes : forall m a bs (k : Z) q X, bytes_at rsegs m a bs -> 0 <= k ->
  (Z.to_nat k + q <= length bs)%nat -> X = a + k -> bytes_at rsegs m X (sub bs k q).
Proof.
  intros m a bs k q X (Ha & Hl & Hb) Hk Hn ->.
  assert (LS : length (sub bs k q) = q) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite LS; lia|].
  intros i Hi. rewrite LS in Hi. rewrite ne_sub by lia.
  replace (i <? q)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply Hb. lia.
Qed.

(* a span of a byte block filled by a callee or a store, the rest untouched *)
Lemma t4_bytes_fill : forall m m' A bs W X k c src,
  bytes_at rsegs m A bs -> munch W m m' -> rw_cells rsegs m' X [CB c src] ->
  X = A + k -> 0 <= k -> k + Z.of_nat c <= Z.of_nat (length bs) ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> ~ (X <= x < X + Z.of_nat c) -> outside W x) ->
  bytes_at rsegs m' A (upd bs k src).
Proof.
  intros m m' A bs W X k c src HB MU D -> Hk Hkc OUT.
  destruct HB as (HBa & HBl & HBi).
  destruct D as [[Dwf Db] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  cbn [cells_bytes cbytes] in Db. rewrite app_nil_r in Db. destruct Db as (_ & _ & Dbi).
  assert (LU : length (upd bs k src) = length bs) by (apply length_upd; [exact Hk | rewrite LS; lia]).
  split; [lia|]. split; [rewrite LU; lia|].
  intros i Hi. rewrite LU in Hi.
  rewrite ne_upd by (rewrite ?LS; lia). rewrite LS.
  destruct ((Z.to_nat k <=? i) && (i <? Z.to_nat k + c))%nat eqn:C.
  - apply andb_true_iff in C. destruct C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.ltb_lt in C2.
    rewrite <- Dbi by (rewrite ?LS; lia). f_equal. unfold wa. f_equal. lia.
  - rewrite <- HBi by lia. unfold mrd. rewrite MU; [reflexivity|].
    rewrite wa_unsigned by lia. apply OUT; [lia|].
    apply andb_false_iff in C. destruct C as [C|C]; [apply Nat.leb_gt in C | apply Nat.ltb_ge in C]; lia.
Qed.

Lemma t4_frame_fill60 : forall m m' regs0 Sp j10 jio j60 W X k c src,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  munch W m m' -> wmono rsegs m m' -> rw_cells rsegs m' X [CB c src] ->
  X = Sp + 96 + k -> 0 <= k -> k + Z.of_nat c <= 40 ->
  (forall x, Sp <= x < Sp + 240 -> ~ (X <= x < X + Z.of_nat c) -> outside W x) ->
  rw_cells rsegs m' Sp (llvm_frame regs0 Sp j10 jio (upd j60 k src)).
Proof.
  intros m m' regs0 Sp j10 jio j60 W X k c src HF H1 H2 H3 MU WMO D EX Hk Hkc OUT.
  pose proof D as D'. destruct D' as [[Dwf _] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  assert (LU : length (upd j60 k src) = 40%nat)
    by (rewrite length_upd; [exact H3 | exact Hk | rewrite LS, H3; lia]).
  pose proof (t4_frame_blen regs0 Sp j10 jio j60 H1 H2 H3) as LB.
  split; [split|].
  - apply t4_frame_wf; assumption.
  - assert (EB : cells_bytes (llvm_frame regs0 Sp j10 jio (upd j60 k src))
               = upd (cells_bytes (llvm_frame regs0 Sp j10 jio j60)) (96 + k) src).
    { rewrite !t4_fb.
      rewrite (t4_upd_app_r t4_pre (j10 ++ t4_mid Sp jio ++ j60 ++ cells_bytes (llvm_saved regs0))
                 src (80 + k) (96 + k));
        [| lia | rewrite !app_length, H1, (t4_mid_len Sp jio H2), H3, (t4_sav_len regs0); lia
         | rewrite t4_pre_len; lia ].
      rewrite (t4_upd_app_r j10 (t4_mid Sp jio ++ j60 ++ cells_bytes (llvm_saved regs0))
                 src (64 + k) (80 + k));
        [| lia | rewrite !app_length, (t4_mid_len Sp jio H2), H3, (t4_sav_len regs0); lia
         | rewrite H1; lia ].
      rewrite (t4_upd_app_r (t4_mid Sp jio) (j60 ++ cells_bytes (llvm_saved regs0)) src k (64 + k));
        [| lia | rewrite app_length, H3, (t4_sav_len regs0); lia | rewrite (t4_mid_len Sp jio H2); lia ].
      rewrite (t4_upd_app_l j60 (cells_bytes (llvm_saved regs0)) src k);
        [reflexivity | lia | rewrite H3; lia]. }
    rewrite EB.
    apply (t4_bytes_fill m m' Sp (cells_bytes (llvm_frame regs0 Sp j10 jio j60)) W X (96 + k) c src);
      [ destruct HF as [[_ Hb] _]; exact Hb | exact MU | exact D | lia | lia | rewrite LB; lia | ].
    rewrite LB. exact OUT.
  - destruct HF as [_ Hw]. rewrite t4_frame_size in Hw |- *.
    eapply wr_at_transport; [exact Hw | exact WMO].
Qed.

Lemma t4_frame_fill10 : forall m m' regs0 Sp j10 jio j60 W X k c src,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  munch W m m' -> wmono rsegs m m' -> rw_cells rsegs m' X [CB c src] ->
  X = Sp + 16 + k -> 0 <= k -> k + Z.of_nat c <= 16 ->
  (forall x, Sp <= x < Sp + 240 -> ~ (X <= x < X + Z.of_nat c) -> outside W x) ->
  rw_cells rsegs m' Sp (llvm_frame regs0 Sp (upd j10 k src) jio j60).
Proof.
  intros m m' regs0 Sp j10 jio j60 W X k c src HF H1 H2 H3 MU WMO D EX Hk Hkc OUT.
  pose proof D as D'. destruct D' as [[Dwf _] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  assert (LU : length (upd j10 k src) = 16%nat)
    by (rewrite length_upd; [exact H1 | exact Hk | rewrite LS, H1; lia]).
  pose proof (t4_frame_blen regs0 Sp j10 jio j60 H1 H2 H3) as LB.
  split; [split|].
  - apply t4_frame_wf; assumption.
  - assert (EB : cells_bytes (llvm_frame regs0 Sp (upd j10 k src) jio j60)
               = upd (cells_bytes (llvm_frame regs0 Sp j10 jio j60)) (16 + k) src).
    { rewrite !t4_fb.
      rewrite (t4_upd_app_r t4_pre (j10 ++ t4_mid Sp jio ++ j60 ++ cells_bytes (llvm_saved regs0))
                 src k (16 + k));
        [| lia | rewrite !app_length, H1, (t4_mid_len Sp jio H2), H3, (t4_sav_len regs0); lia
         | rewrite t4_pre_len; lia ].
      rewrite (t4_upd_app_l j10 (t4_mid Sp jio ++ j60 ++ cells_bytes (llvm_saved regs0)) src k);
        [reflexivity | lia | rewrite H1; lia]. }
    rewrite EB.
    apply (t4_bytes_fill m m' Sp (cells_bytes (llvm_frame regs0 Sp j10 jio j60)) W X (16 + k) c src);
      [ destruct HF as [[_ Hb] _]; exact Hb | exact MU | exact D | lia | lia | rewrite LB; lia | ].
    rewrite LB. exact OUT.
  - destruct HF as [_ Hw]. rewrite t4_frame_size in Hw |- *.
    eapply wr_at_transport; [exact Hw | exact WMO].
Qed.

(* ---------------------------------------------------------------- the loop's llvm_mem *)

Lemma t4_mem_facts : forall data D regs0 m0 Sp lo B m j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 < data /\ data + Z.of_nat (length D) <= lo /\ lo + 9936 <= Sp /\ Sp + 240 <= 2 ^ 63 /\
  W_BASE_UBSAN + W_LEN <= lo /\ Sp mod 16 = 0 /\
  length j10 = 16%nat /\ length jio = 32%nat /\ length j60 = 40%nat /\
  mem_inv rsegs m /\ relro_img m /\ bytes_at rsegs m data D /\ stk rsegs m lo Sp /\
  wmem rsegs m B /\ g_fail_next B <= 1 /\ length B = Z.to_nat W_LEN /\
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 HM. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & _ & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & _ & _ &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  pose proof (wm_len rsegs W_BASE_UBSAN m B HWM) as LB.
  split; [exact HD0|]. split; [exact HDL|]. split; [exact HLO|]. split; [exact HSP2|].
  split; [exact HWL|]. split; [exact HSP|]. split; [exact HJ1|]. split; [exact HJ2|].
  split; [exact HJ3|]. split; [exact HMI|]. split; [exact HRO|]. split; [exact HD|].
  split; [exact HSTK|]. split; [exact HWM|]. split; [exact HFN|]. split; [exact LB|]. exact HRW.
Qed.

Lemma t4_mem_j60 : forall data D regs0 m0 Sp lo B m j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 -> bytes_at rsegs m (Sp + 96) j60.
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 HM.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & HJ1 & HJ2 & HJ3 & _ & _ & _ & _ & _ & _ & _ & HRW).
  exact (proj2 (t4_frame_j m regs0 Sp j10 jio j60 HRW HJ1 HJ2 HJ3)).
Qed.

Lemma t4_mem_j10 : forall data D regs0 m0 Sp lo B m j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 -> bytes_at rsegs m (Sp + 16) j10.
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 HM.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & HJ1 & HJ2 & HJ3 & _ & _ & _ & _ & _ & _ & _ & HRW).
  exact (proj1 (t4_frame_j m regs0 Sp j10 jio j60 HRW HJ1 HJ2 HJ3)).
Qed.

Lemma t4_mem_rd60 : forall data D regs0 m0 Sp lo B m j10 jio j60 k (n : nat) a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat n <= 40 -> a = Sp + 96 + k ->
  ov_read_bytes rsegs m (wa a) n = Some (sub j60 k n).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k n a HM Hk Hn ->.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & HJ3 & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (t4_mem_j60 _ _ _ _ _ _ _ _ _ _ _ HM) as HJ.
  exact (bytes_at_read rsegs m (Sp + 96) j60 k n HJ Hk ltac:(rewrite HJ3; lia)).
Qed.

Lemma t4_mem_rd10 : forall data D regs0 m0 Sp lo B m j10 jio j60 k (n : nat) a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat n <= 16 -> a = Sp + 16 + k ->
  ov_read_bytes rsegs m (wa a) n = Some (sub j10 k n).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k n a HM Hk Hn ->.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & HJ1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (t4_mem_j10 _ _ _ _ _ _ _ _ _ _ _ HM) as HJ.
  exact (bytes_at_read rsegs m (Sp + 16) j10 k n HJ Hk ltac:(rewrite HJ1; lia)).
Qed.

Lemma t4_mem_rd8 : forall data D regs0 m0 Sp lo B m j10 jio j60 (kn : nat) v a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  cell_at (llvm_frame regs0 Sp j10 jio j60) kn = Some (C8 v) ->
  a = Sp + Z.of_nat kn ->
  ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 kn v a HM HC ->.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRW).
  exact (rw_cells_read_at rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) kn (C8 v) 8
           (wa (Sp + Z.of_nat kn)) HRW HC eq_refl eq_refl).
Qed.

Lemma t4_frame_wr : forall m regs0 Sp j10 jio j60 k (n : nat),
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) -> 0 <= k -> k + Z.of_nat n <= 240 ->
  wr_at rsegs m (Sp + k) (Z.of_nat n).
Proof.
  intros m regs0 Sp j10 jio j60 k n HF Hk Hn.
  destruct HF as [_ (Hw0 & Hw1 & Hw)]. rewrite t4_frame_size in Hw1, Hw.
  split; [lia|]. split; [lia|].
  intros i Hi. replace (Sp + k + i) with (Sp + (k + i)) by lia. apply Hw. lia.
Qed.

Lemma t4_mem_store_ok60 : forall data D regs0 m0 Sp lo B m j10 jio j60 k (n : nat) a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat n <= 40 -> a = Sp + 96 + k -> store_ok rsegs m (wa a) n = true.
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k n a HM Hk Hn ->.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRW).
  destruct HRW as [_ Hw]. rewrite t4_frame_size in Hw.
  replace (Sp + 96 + k) with (Sp + (96 + k)) by lia.
  exact (wr_at_store_ok rsegs m Sp (Z.of_nat 240) (96 + k) n Hw ltac:(lia) ltac:(lia)).
Qed.

Lemma t4_mem_store_ok10 : forall data D regs0 m0 Sp lo B m j10 jio j60 k (n : nat) a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat n <= 16 -> a = Sp + 16 + k -> store_ok rsegs m (wa a) n = true.
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k n a HM Hk Hn ->.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRW).
  destruct HRW as [_ Hw]. rewrite t4_frame_size in Hw.
  replace (Sp + 16 + k) with (Sp + (16 + k)) by lia.
  exact (wr_at_store_ok rsegs m Sp (Z.of_nat 240) (16 + k) n Hw ltac:(lia) ltac:(lia)).
Qed.

Lemma t4_mem_cell60 : forall data D regs0 m0 Sp lo B m j10 jio j60 k n X,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  X = Sp + 96 + k -> 0 <= k -> 0 <= n -> k + n <= 40 ->
  rw_cells rsegs m X [CB (Z.to_nat n) (sub j60 k (Z.to_nat n))].
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k n X HM -> Hk Hn Hkn.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & HJ3 & _ & _ & _ & _ & _ & _ & _ & HRW).
  assert (LS : length (sub j60 k (Z.to_nat n)) = Z.to_nat n) by (apply length_sub; rewrite ?HJ3; lia).
  pose proof (t4_mem_j60 _ _ _ _ _ _ _ _ _ _ _ HM) as HJ.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LS | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply (t4_sub_bytes m (Sp + 96) j60 k (Z.to_nat n)); [exact HJ | lia | rewrite HJ3; lia | lia].
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    replace (Sp + 96 + k) with (Sp + (96 + k)) by lia.
    exact (t4_frame_wr m regs0 Sp j10 jio j60 (96 + k) (Z.to_nat n) HRW ltac:(lia) ltac:(lia)).
Qed.

Lemma t4_relro_keep : forall m m' X n, relro_img m -> munch [(X, X + n)] m m' ->
  RELRO_BASE + RELRO_LEN <= X -> relro_img m'.
Proof.
  intros m m' X n HR MU HX i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))).
  - exact (HR i Hi).
  - cbn [outside]. unfold wa.
    rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia).
    unfold RELRO_BASE, RELRO_LEN in *. split; [lia | exact I].
Qed.

Lemma t4_mem_fill60 : forall data D regs0 m0 Sp lo B m m' j10 jio j60 k n src X,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  munch [(X, X + n)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' X [CB (Z.to_nat n) src] ->
  X = Sp + 96 + k -> 0 <= k -> 0 <= n -> k + n <= 40 ->
  llvm_mem data D regs0 m0 Sp lo B m' j10 jio (upd j60 k src).
Proof.
  intros data D regs0 m0 Sp lo B m m' j10 jio j60 k n src X HM MU WMO MI D0 EX Hk Hn Hkn.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & _ & HRO & _ & _ & _ & _ & _ & HRW).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  pose proof D0 as D1. destruct D1 as [[Dwf _] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  unfold llvm_mem in HM |- *.
  destruct HM as (_ & _ & HOW & HD & _ & HSTK & _ & _ & _ & _ & _ & HWM & HFN & HMU & HWMO & _ & _ & _ & _).
  unfold LH_K, LH_FRAME in *.
  assert (LU : length (upd j60 k src) = 40%nat)
    by (rewrite length_upd; [exact HJ3 | exact Hk | rewrite LS, HJ3; lia]).
  split; [exact HD0|]. split; [exact HDL|]. split; [exact HOW|].
  split.
  { eapply bytes_at_transport; [exact HD | exact MU |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split; [exact HSP16|].
  split; [eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |];
          cbn [disjoint_from]; split; [lia | exact I]|].
  split; [lia|]. split; [lia|]. split; [unfold W_BASE_UBSAN, W_LEN; lia|].
  split; [exact MI|].
  split; [eapply t4_relro_keep; [exact HRO | exact MU | unfold RELRO_BASE, RELRO_LEN; lia]|].
  split.
  { eapply rw_cells_transport; [exact HWM | exact MU | exact WMO |].
    rewrite wm_size. cbn [disjoint_from]. unfold W_BASE_UBSAN, W_LEN in *. split; [lia | exact I]. }
  split; [exact HFN|].
  split.
  { eapply munch_trans; [exact HMU|]. eapply munch_weaken; [| exact MU].
    unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *.
    destruct Hx as (Hx1 & _). split; [intros Hcc; apply Hx1; lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ HWMO WMO)|].
  split; [exact HJ1|]. split; [exact HJ2|]. split; [exact LU|].
  eapply t4_frame_fill60;
    [ exact HRW | exact HJ1 | exact HJ2 | exact HJ3 | exact MU | exact WMO | exact D0 | exact EX | exact Hk
    | lia |].
  intros x Hx Hc. cbn [outside]. split; [intros Hcc; apply Hc; lia | exact I].
Qed.

Lemma t4_mem_fill10 : forall data D regs0 m0 Sp lo B m m' j10 jio j60 k n src X,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  munch [(X, X + n)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' X [CB (Z.to_nat n) src] ->
  X = Sp + 16 + k -> 0 <= k -> 0 <= n -> k + n <= 16 ->
  llvm_mem data D regs0 m0 Sp lo B m' (upd j10 k src) jio j60.
Proof.
  intros data D regs0 m0 Sp lo B m m' j10 jio j60 k n src X HM MU WMO MI D0 EX Hk Hn Hkn.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & _ & HRO & _ & _ & _ & _ & _ & HRW).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  pose proof D0 as D1. destruct D1 as [[Dwf _] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  unfold llvm_mem in HM |- *.
  destruct HM as (_ & _ & HOW & HD & _ & HSTK & _ & _ & _ & _ & _ & HWM & HFN & HMU & HWMO & _ & _ & _ & _).
  unfold LH_K, LH_FRAME in *.
  assert (LU : length (upd j10 k src) = 16%nat)
    by (rewrite length_upd; [exact HJ1 | exact Hk | rewrite LS, HJ1; lia]).
  split; [exact HD0|]. split; [exact HDL|]. split; [exact HOW|].
  split.
  { eapply bytes_at_transport; [exact HD | exact MU |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split; [exact HSP16|].
  split; [eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |];
          cbn [disjoint_from]; split; [lia | exact I]|].
  split; [lia|]. split; [lia|]. split; [unfold W_BASE_UBSAN, W_LEN; lia|].
  split; [exact MI|].
  split; [eapply t4_relro_keep; [exact HRO | exact MU | unfold RELRO_BASE, RELRO_LEN; lia]|].
  split.
  { eapply rw_cells_transport; [exact HWM | exact MU | exact WMO |].
    rewrite wm_size. cbn [disjoint_from]. unfold W_BASE_UBSAN, W_LEN in *. split; [lia | exact I]. }
  split; [exact HFN|].
  split.
  { eapply munch_trans; [exact HMU|]. eapply munch_weaken; [| exact MU].
    unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *.
    destruct Hx as (Hx1 & _). split; [intros Hcc; apply Hx1; lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ HWMO WMO)|].
  split; [exact LU|]. split; [exact HJ2|]. split; [exact HJ3|].
  eapply t4_frame_fill10;
    [ exact HRW | exact HJ1 | exact HJ2 | exact HJ3 | exact MU | exact WMO | exact D0 | exact EX | exact Hk
    | lia |].
  intros x Hx Hc. cbn [outside]. split; [intros Hcc; apply Hc; lia | exact I].
Qed.

Lemma t4_wr_cell : forall m A v, 0 <= A -> A + Z.of_nat (length v) <= 2 ^ 64 ->
  wr_at rsegs m A (Z.of_nat (length v)) ->
  rw_cells rsegs (write_to_mem m (wa A) v) A [CB (Z.to_nat (Z.of_nat (length v))) v].
Proof.
  intros m A v HA HL HW. rewrite Nat2Z.id. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_write_same; lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    destruct HW as (Hw0 & Hw1 & Hw). split; [lia|]. split; [lia|].
    intros i Hi. apply wview_write_mono. apply Hw. lia.
Qed.

Lemma t4_mem_store60 : forall data D regs0 m0 Sp lo B m j10 jio j60 k v a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat (length v) <= 40 -> a = Sp + 96 + k ->
  llvm_mem data D regs0 m0 Sp lo B (write_to_mem m (wa a) v) j10 jio (upd j60 k v).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k v a HM Hk Hn ->.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & HRW).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  assert (HW : wr_at rsegs m (Sp + 96 + k) (Z.of_nat (length v))).
  { replace (Sp + 96 + k) with (Sp + (96 + k)) by lia.
    exact (t4_frame_wr m regs0 Sp j10 jio j60 (96 + k) (length v) HRW ltac:(lia) ltac:(lia)). }
  pose proof (t4_mem_store_ok60 _ _ _ _ _ _ _ _ _ _ _ k (length v) _ HM Hk Hn eq_refl) as HSO.
  pose proof (wm_write_munch m (Sp + 96 + k) v ltac:(lia) ltac:(lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (Sp + 96 + k)) v (wmono_refl rsegs m)) as WMO.
  pose proof (mem_inv_store rsegs m (wa (Sp + 96 + k)) v HMI HSO) as MI.
  pose proof (t4_wr_cell m (Sp + 96 + k) v ltac:(lia) ltac:(lia) HW) as DST.
  eapply (t4_mem_fill60 data D regs0 m0 Sp lo B m _ j10 jio j60 k (Z.of_nat (length v)) v (Sp + 96 + k));
    [ exact HM | exact MU | exact WMO | exact MI | exact DST | reflexivity | exact Hk | lia | lia ].
Qed.

Lemma t4_mem_store10 : forall data D regs0 m0 Sp lo B m j10 jio j60 k v a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat (length v) <= 16 -> a = Sp + 16 + k ->
  llvm_mem data D regs0 m0 Sp lo B (write_to_mem m (wa a) v) (upd j10 k v) jio j60.
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k v a HM Hk Hn ->.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & HRW).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  assert (HW : wr_at rsegs m (Sp + 16 + k) (Z.of_nat (length v))).
  { replace (Sp + 16 + k) with (Sp + (16 + k)) by lia.
    exact (t4_frame_wr m regs0 Sp j10 jio j60 (16 + k) (length v) HRW ltac:(lia) ltac:(lia)). }
  pose proof (t4_mem_store_ok10 _ _ _ _ _ _ _ _ _ _ _ k (length v) _ HM Hk Hn eq_refl) as HSO.
  pose proof (wm_write_munch m (Sp + 16 + k) v ltac:(lia) ltac:(lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (Sp + 16 + k)) v (wmono_refl rsegs m)) as WMO.
  pose proof (mem_inv_store rsegs m (wa (Sp + 16 + k)) v HMI HSO) as MI.
  pose proof (t4_wr_cell m (Sp + 16 + k) v ltac:(lia) ltac:(lia) HW) as DST.
  eapply (t4_mem_fill10 data D regs0 m0 Sp lo B m _ j10 jio j60 k (Z.of_nat (length v)) v (Sp + 16 + k));
    [ exact HM | exact MU | exact WMO | exact MI | exact DST | reflexivity | exact Hk | lia | lia ].
Qed.

(* a store into the world: llvm_mem's world becomes the model's upd *)
Lemma t4_mem_wstore : forall data D regs0 m0 Sp lo B m j10 jio j60 k v a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat (length v) <= W_LEN -> a = W_BASE_UBSAN + k ->
  g_fail_next (upd B k v) <= 1 ->
  llvm_mem data D regs0 m0 Sp lo (upd B k v) (write_to_mem m (wa a) v) j10 jio j60.
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k v a HM Hk Hn -> HFN.
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & _ & _ & HWM & _ & _ & _).
  pose proof (wm_wr rsegs W_BASE_UBSAN m B HWM) as HW.
  pose proof (wm_bound rsegs W_BASE_UBSAN m B HWM) as HB.
  assert (HW' : wr_at rsegs m (W_BASE_UBSAN + k) (Z.of_nat (length v))).
  { destruct HW as (Hw0 & Hw1 & Hw). split; [lia|]. split; [lia|].
    intros i Hi. replace (W_BASE_UBSAN + k + i) with (W_BASE_UBSAN + (k + i)) by lia. apply Hw. lia. }
  pose proof (wm_store_ok rsegs W_BASE_UBSAN m B k (length v) (Z_to_bv 64 (W_BASE_UBSAN + k))
                HWM Hk Hn eq_refl) as HSO.
  pose proof (wm_write_munch m (W_BASE_UBSAN + k) v ltac:(lia) ltac:(lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (W_BASE_UBSAN + k)) v (wmono_refl rsegs m)) as WMO.
  pose proof (mem_inv_store rsegs m (wa (W_BASE_UBSAN + k)) v HMI HSO) as MI.
  pose proof (t4_wr_cell m (W_BASE_UBSAN + k) v ltac:(lia) ltac:(lia) HW') as DST.
  rewrite Nat2Z.id in DST.
  eapply (llvm_mem_after_fill data D regs0 m0 Sp lo B m _ k (Z.of_nat (length v)) v j10 jio j60 HM);
    [ exact MU | exact WMO | exact MI | rewrite Nat2Z.id; exact DST
    | exact Hk | lia | lia | exact HFN ].
Qed.

(* ---------------------------------------------------------------- the struct after the stores *)

(* The machine writes, in this order: 0xa0 at +0, serial & 0x7f at +1, serial >> 7 at +2, len at +24, then
   memcpy of the n input bytes at +3. The result is the model's cmd_struct over t4_cb's bytes. *)
Lemma t4_j60_eq : forall display key serial len n (p jhi : list byte),
  length jhi = 8%nat -> length p = Z.to_nat n -> 0 <= n <= 21 ->
  upd (upd (upd (upd (upd (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi)
                      0 [b8 TAG]) 1 [b8 (Z.land serial 127)]) 2 [b8 (Z.land (Z.shiftr serial 7) 127)])
       24 [b8 len]) 3 p
  = cmd_struct ([b8 TAG; b8 (Z.land serial 127); b8 (Z.land (Z.shiftr serial 7) 127)]
                ++ p ++ repeat (b8 0) (Z.to_nat (21 - n))) len display key ++ jhi.
Proof.
  intros display key serial len n p jhi Lj Lp Hn.
  set (R0 := [b8 0; b8 display; b8 0; b8 0] ++ put 4 key ++ jhi).
  assert (LR0 : length R0 = 16%nat)
    by (unfold R0; rewrite !app_length, length_put, Lj; cbn [length]; lia).
  assert (EJ : cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi = repeat (b8 0) 24 ++ R0)
    by (unfold cmd_struct, R0; rewrite <- !app_assoc; reflexivity).
  rewrite EJ.
  set (J := repeat (b8 0) 24 ++ R0).
  assert (LJ : length J = 40%nat) by (unfold J; rewrite app_length, repeat_length, LR0; lia).
  assert (L1 : length (upd J 0 [b8 TAG]) = 40%nat)
    by (rewrite length_upd; [exact LJ | lia | rewrite LJ; cbn [length]; lia]).
  assert (L2 : length (upd (upd J 0 [b8 TAG]) 1 [b8 (Z.land serial 127)]) = 40%nat)
    by (rewrite length_upd; [exact L1 | lia | rewrite L1; cbn [length]; lia]).
  assert (L3 : length (upd (upd (upd J 0 [b8 TAG]) 1 [b8 (Z.land serial 127)]) 2
                         [b8 (Z.land (Z.shiftr serial 7) 127)]) = 40%nat)
    by (rewrite length_upd; [exact L2 | lia | rewrite L2; cbn [length]; lia]).
  rewrite (upd_upd_comm _ [b8 len] p 24 3); [| lia | lia | cbn [length]; rewrite Lp; lia
                                             | rewrite L3; cbn [length]; lia
                                             | rewrite L3, Lp; lia ].
  replace 1 with (0 + Z.of_nat (length [b8 TAG])) by (cbn [length]; lia).
  rewrite (t4_upd_adj J [b8 TAG] [b8 (Z.land serial 127)] 0); [| lia | rewrite LJ; cbn [length]; lia].
  replace 2 with (0 + Z.of_nat (length ([b8 TAG] ++ [b8 (Z.land serial 127)])))
    by (rewrite app_length; cbn [length]; lia).
  rewrite (t4_upd_adj J ([b8 TAG] ++ [b8 (Z.land serial 127)]) [b8 (Z.land (Z.shiftr serial 7) 127)] 0);
    [| lia | rewrite LJ, app_length; cbn [length]; lia].
  replace 3 with (0 + Z.of_nat (length (([b8 TAG] ++ [b8 (Z.land serial 127)])
                                        ++ [b8 (Z.land (Z.shiftr serial 7) 127)])))
    by (rewrite !app_length; cbn [length]; lia).
  rewrite (t4_upd_adj J (([b8 TAG] ++ [b8 (Z.land serial 127)])
                         ++ [b8 (Z.land (Z.shiftr serial 7) 127)]) p 0);
    [| lia | rewrite LJ, !app_length, Lp; cbn [length]; lia].
  set (abc := ([b8 TAG] ++ [b8 (Z.land serial 127)]) ++ [b8 (Z.land (Z.shiftr serial 7) 127)]).
  assert (Labc : length abc = 3%nat) by (unfold abc; rewrite !app_length; cbn [length]; lia).
  rewrite (t4_upd0 J (abc ++ p) (3 + Z.to_nat n));
    [| rewrite app_length, Labc, Lp; lia | rewrite LJ; lia].
  unfold J at 1. rewrite t4_skipn_rep_app by lia.
  replace (24 - (3 + Z.to_nat n))%nat with (Z.to_nat (21 - n)) by lia.
  assert (Lcb : length ((abc ++ p) ++ repeat (b8 0) (Z.to_nat (21 - n))) = 24%nat)
    by (rewrite !app_length, Labc, Lp, repeat_length; lia).
  rewrite (app_assoc (abc ++ p) (repeat (b8 0) (Z.to_nat (21 - n))) R0).
  rewrite (t4_upd_app_r ((abc ++ p) ++ repeat (b8 0) (Z.to_nat (21 - n))) R0 [b8 len] 0 24);
    [| lia | rewrite LR0; cbn [length]; lia | rewrite Lcb; lia].
  assert (ER : upd R0 0 [b8 len] = [b8 len; b8 display; b8 0; b8 0] ++ put 4 key ++ jhi).
  { unfold R0.
    rewrite (t4_upd_app_l [b8 0; b8 display; b8 0; b8 0] (put 4 key ++ jhi) [b8 len] 0)
      by (cbn [length]; lia).
    reflexivity. }
  rewrite ER.
  unfold cmd_struct, abc. rewrite <- !app_assoc. reflexivity.
Qed.
