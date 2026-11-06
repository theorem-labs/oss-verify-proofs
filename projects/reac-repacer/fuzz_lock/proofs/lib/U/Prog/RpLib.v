(* Walk of reac-repacer's rp_lock_lookup (src/repace_conf.c:114-145 at 3ac1cf10) in fuzz_lock.ubsan, 0x13258:
   frame, string and word facts; field / digits calls with their argument registers given by equations; the frame
   invariant of the loop (INV0 / INV); the exit at 0x132ec; the digits tests at 0x13444 (repace_conf.c:137-142).
   The rest of the walk: RpDec.v, RpMid.v, RpLoop.v, rp_lock_lookup.v.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import DigitsMach field_c field digits_c digits
  strlen_c memchr_c bcmp_c rp_lock_lookup_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

(** * Facts about frames and byte strings *)

Lemma wr_split : forall m A n1 n2, wr_at rsegs m A (n1 + n2) -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 (H1 & H2 & H) P1 P2. split.
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
Qed.

Lemma wr_join : forall m A n1 n2, wr_at rsegs m A n1 -> wr_at rsegs m (A + n1) n2 -> 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2).
Proof.
  intros m A n1 n2 (H1 & H2 & H) (G1 & G2 & G) P1 P2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.ltb_spec0 i n1); [apply H; lia|].
  replace (A + i) with (A + n1 + (i - n1)) by lia. apply G. lia.
Qed.

Lemma rw_split2 : forall m A cs1 cs2 B, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A cs1 cs2 B [[Hwf Hb] Hw] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  apply wr_split in Hw; [| lia | lia]. destruct Hw as [V1 V2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; (split; [split|]); assumption.
Qed.

Lemma rw_app2 : forall m A cs1 cs2 B, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 B [[W1 B1] V1] [[W2 B2] V2] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. apply wr_join; [exact V1 | exact V2 | lia | lia].
Qed.

Lemma rw_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB ES. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite ES. exact V.
Qed.

Lemma c8_cb : forall m A v, rw_cells rsegs m A [C8 v] -> exists J, rw_cells rsegs m A [CB 8 J].
Proof.
  intros m A v H. exists (le8 v). eapply rw_conv; [exact H | | |].
  - cbn [cells_wf cell_wf]. split; [apply length_le8 | exact I].
  - cbn [cells_bytes cbytes]. reflexivity.
  - reflexivity.
Qed.

Lemma cb_ex : forall m A J, rw_cells rsegs m A [CB 8 J] -> exists J', rw_cells rsegs m A [CB 8 J'].
Proof. intros m A J H. exists J. exact H. Qed.

Lemma bytes_sub : forall m A (bs : list byte) k n, bytes_at rsegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Init.Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma bytes_skip : forall m A (bs : list byte) k, bytes_at rsegs m A bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Init.Nat.min k (length bs)) with k in H by lia. exact H.
Qed.

Lemma bytes_sub' : forall m A (bs : list byte) k n A' bs', bytes_at rsegs m A bs -> (k + n <= length bs)%nat ->
  A' = A + Z.of_nat k -> bs' = firstn n (skipn k bs) -> bytes_at rsegs m A' bs'.
Proof. intros m A bs k n A' bs' H Hk -> ->. apply bytes_sub; assumption. Qed.

Lemma nth_of_error : forall (l : list byte) i c d, nth_error l i = Some c -> nth i l d = c.
Proof.
  intros l; induction l as [|x l IH]; intros [|i] c d N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH. exact N.
Qed.

(** * Facts about the grammar *)

Lemma lk_nil : forall f p rate x, lk f p rate [] x = x.
Proof. intros [|f] p rate x; reflexivity. Qed.

Lemma lk_cons : forall f p rate t x, t <> [] ->
  lk (S f) p rate t x = match find_byte 10 t with
                        | Some j => lk f p rate (skipn (S j) t) (upd p rate (firstn j t) x)
                        | None => upd p rate t x
                        end.
Proof. intros f p rate [|c t] x H; [congruence | reflexivity]. Qed.

Lemma fld_at : forall l k, fld l k = (k + fld_s (skipn k l), fld_n (skipn k l))%nat.
Proof.
  intros l k. unfold fld, fld_s, fld_n. cbv zeta. rewrite skipn_skipn.
  replace (sep_run (skipn k l) + k)%nat with (k + sep_run (skipn k l))%nat by lia. reflexivity.
Qed.

Lemma slice_len : forall (l : list byte) s n, (s + n <= length l)%nat -> length (slice l s n) = n.
Proof. intros l s n H. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma memcmp_app : forall n (l r x : list byte), (n <= length r)%nat -> memcmp_model l (r ++ x) n = memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros l r x H; [reflexivity|].
  destruct l as [|a l]; destruct r as [|c r]; cbn in H |- *; try lia; try reflexivity.
  rewrite IH by lia. reflexivity.
Qed.

Lemma memcmp_range : forall n (l r : list byte) v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H; cbn in H.
  - injection H as <-. lia.
  - destruct l as [|a l]; destruct r as [|c r]; try discriminate.
    pose proof (byte_range a). pose proof (byte_range c).
    destruct (bv_unsigned a =? bv_unsigned c); [eapply IH; exact H|]. injection H as <-. lia.
Qed.

Lemma line_val_eq : forall p rate l o1 n1 o2 n2 o3 n3,
  fld l 0 = (o1, n1) -> fld l (o1 + n1) = (o2, n2) -> fld l (o2 + n2) = (o3, n3) ->
  line_val p rate l =
  if is_some (find_byte 0 l) then None
  else if (n1 =? 0)%nat || (bz (nth o1 l (Z_to_bv 8 0)) =? 35) then None
  else if (15 <? n1)%nat || negb (n1 =? length p)%nat
          || negb (match memcmp_model (slice l o1 n1) p n1 with Some 0 => true | _ => false end)
  then None
  else if (digits (slice l o2 n2) <? 0) || negb (digits (slice l o3 n3) =? rate) then None
  else if (digits (slice l o2 n2) <? std_period rate - std_period rate / 20)
          || (std_period rate + std_period rate / 20 <? digits (slice l o2 n2)) then None
  else Some (digits (slice l o2 n2)).
Proof.
  intros p rate l o1 n1 o2 n2 o3 n3 F1 F2 F3. unfold line_val. rewrite F1. cbv iota beta.
  rewrite F2. cbv iota beta. rewrite F3. cbv iota beta. reflexivity.
Qed.

(** * Facts about words *)

Lemma sgn_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_lt_le_dec z 0) as [L|L].
  - rewrite <- (Z.mod_add z 1 (2^64)) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (z + 1 * 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
Qed.

Lemma weq_small : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  apply eq_true_iff_eq. rewrite !Z.eqb_eq. split; [|intros ->; reflexivity].
  intros E. Z.div_mod_to_equations. lia.
Qed.

Lemma lts_small : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !sgn_lit by lia. reflexivity. Qed.

Lemma div20 : forall std, std = 272109 \/ std = 250000 \/ std = 125000 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (std * 214748365))) 32 = std / 20.
Proof. intros std [->|[->| ->]]; vm_compute; reflexivity. Qed.

Lemma memchr_ok_len : forall A c n buf, n <= Z.of_nat (length buf) -> memchr_ok A c n buf.
Proof. intros A c n buf H. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat n) buf)); lia. Qed.

Lemma find_byte_lt : forall c l j, find_byte c l = Some j -> (j < length l)%nat.
Proof. intros c l j H. apply find_byte_Some in H. tauto. Qed.


Lemma w_neq0 : forall v, -2^63 <= v < 2^63 -> v <> 0 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof. intros v Hv H. rewrite weq_small by lia. apply Z.eqb_neq. exact H. Qed.

Lemma range_test : forall per lw hi, -2^63 <= per < 2^63 -> -2^63 <= lw < 2^63 -> -2^63 <= hi < 2^63 ->
  negb (bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (v_slt (Z_to_bv 64 per) (Z_to_bv 64 lw)))
                                  (bv_unsigned (v_slt (Z_to_bv 64 hi) (Z_to_bv 64 per))))) (Z_to_bv 64 0))
  = (per <? lw) || (hi <? per).
Proof.
  intros per lw hi H1 H2 H3. unfold v_slt, c_lts. rewrite !lts_small by lia.
  destruct (per <? lw), (hi <? per); vm_compute; reflexivity.
Qed.

(** * Calls, with the argument registers given by equations *)

Lemma field_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pp ap s e : Z) (l J : list byte),
  e = s + Z.of_nat (length l) ->
  0 < s -> s + Z.of_nat (length l) < 2^64 -> bytes_at rsegs m s l ->
  rw_cells rsegs m pp [C8 (Z_to_bv 64 s)] -> rw_cells rsegs m ap [CB 8 J] ->
  pp + 8 <= ap \/ ap + 8 <= pp -> pp mod 8 = 0 -> ap mod 8 = 0 -> mem_inv rsegs m ->
  evt rsegs (field_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pp ap s l)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pp) (Z_to_bv 64 e) (Z_to_bv 64 ap) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FIELD) fc None m (seg_rom rsegs)).
Proof. intros. subst e. eapply field_holds; eassumption. Qed.

Lemma digits_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sv nv : Z) (l : list byte),
  nv = Z.of_nat (length l) -> 0 < sv -> bytes_at rsegs m sv l -> mem_inv rsegs m ->
  evt rsegs (digits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m l)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sv) (Z_to_bv 64 nv) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DIGITS) fc None m (seg_rom rsegs)).
Proof. intros. subst nv. apply digits_holds; assumption. Qed.

(** * The walk *)

Section R.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (tx pa rate lo b std : Z) (T P SL : list byte).
Hypothesis Htx : 0 < tx.
Hypothesis HtxE : tx + Z.of_nat (length T) < 2^64.
Hypothesis Hpa : 0 < pa.
Hypothesis HPb : pa + Z.of_nat (length P + 1 + length SL) <= 2^64.
Hypothesis Hrate : rate = 44100 \/ rate = 48000 \/ rate = 96000.
Hypothesis HSTD : std_period rate = std.
Hypothesis Hstd : std = 272109 \/ std = 250000 \/ std = 125000.
Hypothesis Hb : b + 160 = bv_unsigned sp.
Hypothesis Hb8 : b mod 8 = 0.
Hypothesis Hlo : 0 <= lo <= b.
Hypothesis DT : tx + Z.of_nat (length T) <= b \/ b + 160 <= tx.
Hypothesis DP : pa + Z.of_nat (length P + 1 + length SL) <= b \/ b + 160 <= pa.

Local Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Local Notation Q := (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lock_lookup T P rate)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_FRAME, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp)).

(* the registers in the loop: s0 rate, s1 -1, s2 the line, s3 strlen(port), s4 found, s10 stop, s11 '#' *)
Local Notation LS pc mm xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 vs2 vs4 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 :=
  (MS (mkR xra (Z_to_bv 64 b) gp tp xt0 xt1 xt2 (Z_to_bv 64 rate) (Z_to_bv 64 (-1)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           vs2 (Z_to_bv 64 (Z.of_nat (length P))) vs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (tx + Z.of_nat (length T)))
           (Z_to_bv 64 35) xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Definition INV0 (m : word -> option byte) : Prop :=
  bytes_at rsegs m tx T /\ bytes_at rsegs m pa (P ++ Z_to_bv 8 0 :: SL) /\
  rw_cells rsegs m b [C8 (Z_to_bv 64 (std + std / 20)); C8 (Z_to_bv 64 (std - std / 20)); C8 (Z_to_bv 64 pa)] /\
  rw_cells rsegs m (b + 56) SAVED /\ stk rsegs m lo b /\ munch [(b, b + 160)] m0 m /\ wmono rsegs m0 m /\
  mem_inv rsegs m.

Definition INV (m : word -> option byte) : Prop :=
  INV0 m /\ (exists J, rw_cells rsegs m (b + 24) [CB 8 J]) /\ (exists J, rw_cells rsegs m (b + 32) [CB 8 J]) /\
  (exists J, rw_cells rsegs m (b + 40) [CB 8 J]) /\ (exists J, rw_cells rsegs m (b + 48) [CB 8 J]).

Ltac slot := first [ eapply c8_cb; eassumption | eapply cb_ex; eassumption ].
Ltac mk_inv0 := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); assumption.
Ltac mk_inv := refine (conj _ (conj _ (conj _ (conj _ _)))); [mk_inv0 | slot | slot | slot | slot].

Lemma bnd_sp : 0 <= bv_unsigned sp < 2^64.
Proof. pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2^64) in R. exact R. Qed.

(* 0x132ec: mv a0,s4; restore ra, s0-s11; addi sp,sp,160; ret *)
Lemma rp_exit : forall (m : word -> option byte) (cs : list cell) (r : Z)
    (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  r = lock_lookup T P rate ->
  rw_cells rsegs m b cs -> cells_size cs = 56%nat -> rw_cells rsegs m (b + 56) SAVED ->
  stk rsegs m lo b -> munch [(b, b + 160)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs Q (MS (mkR xra (Z_to_bv 64 b) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 (Z_to_bv 64 r) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                  F (Z_to_bv 64 0x132ec) fc None m (seg_rom rsegs)).
Proof.
  intros m cs r xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 -> FR Hcs FS ST MU WM MI.
  pose proof bnd_sp as Rsp.
  pose proof (stk_release rsegs m lo b (cs ++ SAVED) ST (rw_app2 m b cs SAVED (b + 56) FR FS
                ltac:(rewrite Hcs; reflexivity)) ltac:(lia)) as ST2.
  rewrite cells_size_app, Hcs in ST2. change (Z.of_nat (56 + cells_size SAVED)) with 160 in ST2.
  do 16 step.
  rewrite ?Z.add_0_r. replace (b + 160) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [unfold RP_FRAME; replace (bv_unsigned sp - 160) with b by lia; rewrite <- Hb; exact MU|].
  split; [exact WM|]. split; [exact MI|]. rewrite <- Hb. exact ST2.
Qed.


(* 0x13444: per = digits(per_at, per_len), lab = digits(lab_at, lab_len); the tests of repace_conf.c:138-142 *)
Lemma rp_dec2 : forall (l : list byte) (o o2 n2 o3 n3 : nat) (fnd v2 v3 w2 w3 : Z) (m : word -> option byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs7 xs8 xs9 xt3 xt4 xt5 xt6 c40 c48 : word),
  (o2 + n2 <= length l)%nat -> (o3 + n3 <= length l)%nat ->
  line_val P rate l = (if (digits (slice l o2 n2) <? 0) || negb (digits (slice l o3 n3) =? rate) then None
                       else if (digits (slice l o2 n2) <? std - std / 20) || (std + std / 20 <? digits (slice l o2 n2))
                            then None else Some (digits (slice l o2 n2))) ->
  v2 = tx + Z.of_nat o + Z.of_nat o2 -> v3 = tx + Z.of_nat o + Z.of_nat o3 ->
  w2 = Z.of_nat n2 -> w3 = Z.of_nat n3 ->
  bytes_at rsegs m (tx + Z.of_nat o) l -> INV0 m ->
  rw_cells rsegs m (b + 24) [C8 (Z_to_bv 64 v3)] -> rw_cells rsegs m (b + 32) [C8 (Z_to_bv 64 v2)] ->
  rw_cells rsegs m (b + 40) [C8 c40] -> rw_cells rsegs m (b + 48) [C8 c48] ->
  (forall (m' : word -> option byte) (v4 : Z)
          (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 : word),
     v4 = upd P rate l fnd -> INV m' ->
     evt rsegs Q (LS 0x1343c m' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 (Z_to_bv 64 v4)
                     ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6)) ->
  evt rsegs Q (LS 0x13444 m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 fnd)
                  (Z_to_bv 64 w2) (Z_to_bv 64 w3) xs7 xs8 xs9 xt3 xt4 xt5 xt6).
Proof.
  intros l o o2 n2 o3 n3 fnd v2 v3 w2 w3 m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs7 xs8 xs9
    xt3 xt4 xt5 xt6 c40 c48 B2 B3 LV -> -> -> -> BL I0 C18 C20 C28 C30 K.
  destruct I0 as (BT & BP & FHL & FS & ST & MU & WM & MI).
  pose proof (bytes_at_bound _ _ _ _ BL) as BLb.
  pose proof bnd_sp as Rsp.
  (* 0x13444 ld a0,0x20(sp); mv a1,s5; jal digits *)
  step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply digits_call with (l := slice l o2 n2);
      [ rewrite slice_len by lia; lia | lia | eapply (bytes_sub' _ _ _ o2 n2); [exact BL | lia | lia | reflexivity] | exact MI ]
    | post_call segs mm ] end.
  (* 0x13450 ld a1,0x18(sp); mv s5,a0; mv a0,a1; mv a1,s6; jal digits *)
  step. step. step. step. step.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply digits_call with (l := slice l o3 n3);
      [ rewrite slice_len by lia; lia | lia | eapply (bytes_sub' _ _ _ o3 n3); [exact BL | lia | lia | reflexivity] | assumption ]
    | post_call segs mm ] end.
  pose proof (digits_range (slice l o2 n2)) as R2. pose proof (digits_range (slice l o3 n3)) as R3.
  rewrite ?Z.add_0_r.
  (* 0x13464 bltz s5 *)
  step. rewrite (lts_small (digits (slice l o2 n2)) 0) by lia.
  destruct (Z.ltb_spec (digits (slice l o2 n2)) 0) as [PN|PN]; cbv iota.
  { eapply K; [unfold upd; rewrite LV; try rewrite (proj2 (Z.ltb_lt _ _) PN); reflexivity | mk_inv]. }
  (* 0x13468 bne a0,s0 *)
  step. rewrite (weq_small (digits (slice l o3 n3)) rate) by lia.
  destruct (Z.eqb_spec (digits (slice l o3 n3)) rate) as [LR|LR]; cbn [negb]; cbv iota.
  2: { eapply K; [unfold upd; rewrite LV; try rewrite (proj2 (Z.ltb_ge _ _) PN);
                  try rewrite (proj2 (Z.eqb_neq _ _) LR); reflexivity | mk_inv]. }
  (* 0x1346c ld a0,8(sp); slt a0,s5,a0; ld a1,0(sp); slt a1,a1,s5; or a0,a0,a1; bnez a0 *)
  step. step. step. step. step. step.
  assert (SB : 0 < std - std / 20 /\ std + std / 20 < 2^62) by (destruct Hstd as [->|[->| ->]]; vm_compute; tauto).
  rewrite range_test by lia.
  destruct ((digits (slice l o2 n2) <? std - std / 20) || (std + std / 20 <? digits (slice l o2 n2))) eqn:RG;
    cbv iota.
  { eapply K; [unfold upd; rewrite LV; try rewrite (proj2 (Z.ltb_ge _ _) PN);
               try rewrite (proj2 (Z.eqb_eq _ _) LR); cbn [orb negb]; try rewrite RG; reflexivity | mk_inv]. }
  (* 0x13484 mv s4,s5; j 0x1343c *)
  step. step. rewrite ?Z.add_0_r.
  eapply K; [unfold upd; rewrite LV; try rewrite (proj2 (Z.ltb_ge _ _) PN);
             try rewrite (proj2 (Z.eqb_eq _ _) LR); cbn [orb negb]; try rewrite RG; reflexivity | mk_inv].
Qed.

End R.
