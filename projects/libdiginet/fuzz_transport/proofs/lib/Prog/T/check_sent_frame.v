From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import StrFun DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract check_sent_frame_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- bytes and lists ---- *)

Lemma csf_map_inj : forall a b : list byte, map bv_unsigned a = map bv_unsigned b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] E; cbn [map] in E; try discriminate; [reflexivity|].
  injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma csf_beq : forall a b, beq_bytes a b = true -> a = b.
Proof.
  intros a b. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs a) (zs b)) as [E|E]; [|discriminate].
  intros _. apply csf_map_inj. exact E.
Qed.

Lemma csf_memcmp : forall n l r v, (n <= length l)%nat -> (n <= length r)%nat -> memcmp_model l r n = Some v ->
  (v = 0 <-> firstn n l = firstn n r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr Hm.
  - cbn in Hm. injection Hm as <-. cbn [firstn]. split; [split; intros; reflexivity | lia].
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn in Hl, Hr, Hm. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) Hm) as [[I1 I2] I3]. split; [|exact I3].
      assert (a = b) by (apply bv_eq; exact E). subst b. cbn [firstn]. split.
      * intros Hv. f_equal. tauto.
      * intros Q. injection Q as Q. tauto.
    + injection Hm as <-. split; [|lia]. cbn [firstn]. split.
      * intros. lia.
      * intros Q. injection Q as Q1 Q2. subst. lia.
Qed.

Lemma csf_bytes_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk Hn.
  assert (Ln : length (sub bs k n) = n) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite Ln; lia|].
  intros i Hi. rewrite Ln in Hi. rewrite ne_sub by lia.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

Lemma csf_rd : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (sub bs k n).
Proof. intros m a bs k n H Hk Hn. apply (bytes_at_read rsegs m a bs k n H Hk). lia. Qed.

(* ---- comparisons of words ---- *)

Lemma csf_eqb0 : forall v, -256 < v < 256 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma csf_eqb0_s32 : forall v, -2^31 <= v < 2^31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma csf_ltu : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma csf_eqb : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

(* ---- the parse ---- *)

Lemma csf_be16_range : forall b p, 0 <= spec_be16 b p < 65536.
Proof. intros. unfold spec_be16, u16. apply Z.mod_pos_bound. lia. Qed.

Lemma csf_rf_ok : forall frame, sf_code (rf frame) = 0 ->
  30 <= Z.of_nat (length frame) /\ sf_src (rf frame) = 6 /\ sf_dst (rf frame) = 0 /\ sf_body (rf frame) = 30 /\
  0 <= sf_body_len (rf frame) /\ 30 + sf_body_len (rf frame) <= Z.of_nat (length frame) /\
  sf_body_len (rf frame) < 65536.
Proof.
  intros frame. unfold rf, spec_read_frame. cbv beta zeta.
  destruct (Z.of_nat (length frame) <? SPEC_BODY_AT) eqn:C1; [cbn [sf_code]; intros E; discriminate E|].
  destruct (negb (spec_be16 (zs frame) 12 =? SPEC_ETHERTYPE)) eqn:C2; [cbn [sf_code]; intros E; discriminate E|].
  destruct ((spec_be16 (zs frame) SPEC_AT_NUMBYTES <? SPEC_HDR)
            || (Z.of_nat (length frame) - SPEC_ETH_HDR <? spec_be16 (zs frame) SPEC_AT_NUMBYTES)) eqn:C3;
    [cbn [sf_code]; intros E; discriminate E|].
  intros _. cbn [sf_src sf_dst sf_body sf_body_len].
  pose proof (csf_be16_range (zs frame) SPEC_AT_NUMBYTES).
  apply Z.ltb_ge in C1. apply orb_false_iff in C3 as [C3a C3b]. apply Z.ltb_ge in C3a. apply Z.ltb_ge in C3b.
  unfold SPEC_BODY_AT, SPEC_HDR, SPEC_ETH_HDR, SPEC_MAC in *. lia.
Qed.

Lemma csf_eqb_sgn : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intros E. apply N.
  assert (D : (a - b) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in D; [|lia]. destruct D as [c Hc]. assert (c = 0) by nia. subst c. lia.
Qed.

(* two addresses in (0, 2^64]: the end of a buffer may be 2^64 itself *)
Lemma csf_eqb_le : forall a b, 0 < a <= 2^64 -> 0 < b <= 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intros E. apply N.
  destruct (Z.eq_dec a (2^64)) as [A|A]; destruct (Z.eq_dec b (2^64)) as [B'|B']; lia.
Qed.

(* slli 48; srli 48 *)
Lemma csf_shift : forall s, 0 <= s < 2^64 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 s)) 48))) 48 = s mod 65536.
Proof.
  intros s Hs. rewrite (unsigned_lit s) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap.
  rewrite Z.shiftr_div_pow2 by lia. replace (2^64) with (2^16 * 2^48) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* ---- bytes of the frame as the model reads them ---- *)

Lemma csf_u1_nat : forall (l : list byte) (k : nat) x, nth_error l k = Some x ->
  bytes_le_to_Z (firstn 1 (skipn k l)) = bv_unsigned x.
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in H; try discriminate.
  - injection H as <-. cbn [skipn]. change (firstn 1 (y :: l)) with [y]. rewrite bytes_le_to_Z_le_val.
    cbn [map le_val]. lia.
  - cbn [skipn]. apply IH. exact H.
Qed.

Lemma csf_byte : forall (l : list byte) n i, 0 <= i -> Z.of_nat n + i < Z.of_nat (length l) ->
  byte_at (zs (skipn n l)) i = u_at l (Z.of_nat n + i) 1.
Proof.
  intros l n i Hi Hl.
  destruct (nth_error l (n + Z.to_nat i)) as [x|] eqn:E; [| apply nth_error_None in E; lia].
  unfold u_at, sub. replace (Z.to_nat (Z.of_nat n + i)) with (n + Z.to_nat i)%nat by lia.
  rewrite (csf_u1_nat l _ x E).
  unfold byte_at, zs. apply nth_error_nth. rewrite nth_error_map, nth_skipn, E. reflexivity.
Qed.

Lemma csf_byte_range : forall (l : list byte) t, 0 <= byte_at (zs l) t < 256.
Proof.
  intros l t. unfold byte_at, zs.
  destruct (nth_error (map bv_unsigned l) (Z.to_nat t)) as [z|] eqn:E.
  - erewrite nth_error_nth by exact E. rewrite nth_error_map in E.
    destruct (nth_error l (Z.to_nat t)) as [x|]; cbn in E; [|discriminate E]. injection E as <-.
    pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
  - apply nth_error_None in E. rewrite nth_overflow by exact E. lia.
Qed.

Lemma csf_u1_range : forall (l : list byte) k, 0 <= u_at l k 1 < 256.
Proof. intros l k. pose proof (u_at_range l k 1) as R. change (2 ^ (8 * Z.of_nat 1)) with 256 in R. exact R. Qed.

(* no F0 13 xx 70 in the body: the model's spec_system_at is negative *)
Lemma csf_sys_loop : forall b len fuel j, system_at_loop b len j fuel < 0 -> 0 <= j ->
  forall i, j <= i -> i < j + Z.of_nat fuel -> i + 3 < len ->
  byte_at b i = 240 -> byte_at b (i + 1) = 19 -> byte_at b (i + 3) = 112 -> False.
Proof.
  intros b len fuel. induction fuel as [|f IH]; intros j H Hj i Hji Hif Hil E1 E2 E3; [lia|].
  cbn [system_at_loop] in H.
  destruct (j + 3 <? len) eqn:C; [|apply Z.ltb_ge in C; lia].
  cbv iota in H.
  destruct ((byte_at b j =? 240) && (byte_at b (j + 1) =? SPEC_MAKER) && (byte_at b (j + 3) =? SPEC_FN_SYSTEM))
    eqn:M; cbv iota in H; [lia|].
  destruct (Z.eq_dec i j) as [->|N].
  - rewrite E1, E2, E3 in M. cbv in M. discriminate M.
  - apply (IH (j + 1) H ltac:(lia) i); lia.
Qed.

Lemma csf_sys : forall (frame : list byte) blen i, spec_system_at (zs (skipn 30 frame)) blen < 0 ->
  0 <= i -> i + 3 < blen -> 30 + blen <= Z.of_nat (length frame) ->
  u_at frame (30 + i) 1 = 240 -> u_at frame (30 + i + 1) 1 = 19 -> u_at frame (30 + i + 3) 1 = 112 -> False.
Proof.
  intros frame blen i H Hi Hb Hl E1 E2 E3. unfold spec_system_at in H.
  apply (csf_sys_loop _ _ _ 0 H ltac:(lia) i ltac:(lia) ltac:(lia) Hb).
  - rewrite csf_byte by lia. exact E1.
  - rewrite csf_byte by lia. replace (Z.of_nat 30 + (i + 1)) with (30 + i + 1) by lia. exact E2.
  - rewrite csf_byte by lia. replace (Z.of_nat 30 + (i + 3)) with (30 + i + 3) by lia. exact E3.
Qed.

(* the padding is zero *)
Lemma csf_zero : forall (l : list byte) n, forallb (fun x => bz x =? 0) (skipn n l) = true ->
  forall k, (n <= k < length l)%nat -> u_at l (Z.of_nat k) 1 = 0.
Proof.
  intros l n H k Hk. destruct (nth_error l k) as [x|] eqn:E; [|apply nth_error_None in E; lia].
  unfold u_at, sub. rewrite Nat2Z.id. rewrite (csf_u1_nat l k x E).
  rewrite forallb_forall in H.
  assert (I : In x (skipn n l)).
  { apply nth_error_In with (n := (k - n)%nat). rewrite nth_skipn. replace (n + (k - n))%nat with k by lia. exact E. }
  specialize (H x I). cbv beta in H. unfold bz in H. apply Z.eqb_eq in H. exact H.
Qed.

(* the body sum: the machine adds the bytes, the model masks after each one *)
Fixpoint csum (l : list byte) (k : Z) (j : nat) : Z :=
  match j with O => 0 | S j' => csum l k j' + u_at l (k + Z.of_nat j') 1 end.

Lemma csum_range : forall l k j, 0 <= csum l k j <= 255 * Z.of_nat j.
Proof. intros l k. induction j as [|j IH]; cbn [csum]; [lia|]. pose proof (csf_u1_range l (k + Z.of_nat j)). lia. Qed.

Fixpoint csf_sumg (b : list Z) (p i : Z) (f : nat) : Z :=
  match f with O => 0 | S f' => byte_at b (p + i) + csf_sumg b p (i + 1) f' end.

Lemma csf_loop_sumg : forall (l : list byte) p f s i, 0 <= s < 65536 ->
  spec_sum_loop (zs l) p s i f = (s + csf_sumg (zs l) p i f) mod 65536.
Proof.
  intros l p f. induction f as [|f IH]; intros s i Hs; cbn [spec_sum_loop csf_sumg].
  - rewrite Z.add_0_r, Z.mod_small; lia.
  - pose proof (csf_byte_range l (p + i)) as R.
    replace (Z.land (s + byte_at (zs l) (p + i)) 65535) with ((s + byte_at (zs l) (p + i)) mod 65536)
      by (change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity).
    rewrite IH by (apply Z.mod_pos_bound; lia). rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma csf_sumg_snoc : forall b p f i, csf_sumg b p i (S f) = csf_sumg b p i f + byte_at b (p + i + Z.of_nat f).
Proof.
  intros b p f. induction f as [|f IH]; intros i.
  - cbn [csf_sumg Z.of_nat]. rewrite !Z.add_0_r. lia.
  - change (csf_sumg b p i (S (S f))) with (byte_at b (p + i) + csf_sumg b p (i + 1) (S f)).
    rewrite IH. change (csf_sumg b p i (S f)) with (byte_at b (p + i) + csf_sumg b p (i + 1) f).
    replace (p + (i + 1) + Z.of_nat f) with (p + i + Z.of_nat (S f)) by lia. lia.
Qed.

Lemma csf_csum_sumg : forall l p n, 0 <= p -> p + Z.of_nat n <= Z.of_nat (length l) ->
  csum l p n = csf_sumg (zs l) p 0 n.
Proof.
  intros l p n Hp. induction n as [|n IH]; intros Hn; [reflexivity|].
  rewrite csf_sumg_snoc. cbn [csum]. rewrite IH by lia. f_equal.
  pose proof (csf_byte l 0 (p + 0 + Z.of_nat n) ltac:(lia) ltac:(lia)) as E. change (skipn 0 l) with l in E. rewrite E.
  f_equal. lia.
Qed.

Lemma csf_sum_at : forall l p n, 0 <= p -> 0 <= n -> p + n <= Z.of_nat (length l) ->
  spec_sum_at (zs l) p n = csum l p (Z.to_nat n) mod 65536.
Proof.
  intros l p n Hp Hn Hl. unfold spec_sum_at, u16. rewrite csf_loop_sumg by lia. rewrite Z.add_0_l, Z.mod_mod by lia.
  rewrite csf_csum_sumg by lia. reflexivity.
Qed.

(* ---- the model ---- *)

Lemma csf_model : forall B B' frame, check_sent_frame_m B frame = Some (B', tt) ->
  B' = B /\ sf_code (rf frame) = 0 /\ sub frame 6 6 = HOST /\ s32_at B 0 <> 0 /\ sub frame 0 6 = sub B 4 6 /\
  spec_system_at (zs (skipn 30 frame)) (sf_body_len (rf frame)) < 0 /\
  Z.of_nat (length frame) = (if 30 + sf_body_len (rf frame) <? 60 then 60 else 30 + sf_body_len (rf frame)) /\
  forallb (fun x => bz x =? 0) (skipn (Z.to_nat (30 + sf_body_len (rf frame))) frame) = true /\
  sf_sum (rf frame) = (if s32_at B 65044 =? 1 then 0 else spec_sum_at (zs frame) 30 (sf_body_len (rf frame))).
Proof.
  intros B B' frame H. unfold check_sent_frame_m in H. cbv zeta in H.
  change (M_desk_known B) with (s32_at B 0) in H. change (M_desk B) with (sub B 4 6) in H.
  change (Cfg_sum_mode B =? DIGINET_SUM_ZERO) with (s32_at B 65044 =? 1) in H.
  change SPEC_BODY_AT with 30 in H. change SPEC_MIN_FRAME with 60 in H.
  revert H.
  destruct (negb (sf_code (rf frame) =? SPEC_OK) || negb (beq_bytes (sub frame (sf_src (rf frame)) 6) HOST)
            || negb (truth (s32_at B 0)) || negb (beq_bytes (sub frame (sf_dst (rf frame)) 6) (sub B 4 6))
            || (0 <=? spec_system_at (zs (skipn (Z.to_nat (sf_body (rf frame))) frame)) (sf_body_len (rf frame))))
    eqn:C1; [intros H; discriminate H|].
  destruct (negb (Z.of_nat (length frame) =?
                  (if 30 + sf_body_len (rf frame) <? 60 then 60 else 30 + sf_body_len (rf frame)))
            || negb (forallb (fun x => bz x =? 0) (skipn (Z.to_nat (30 + sf_body_len (rf frame))) frame))
            || negb (sf_sum (rf frame) =?
                     (if s32_at B 65044 =? 1 then 0 else spec_sum_at (zs frame) (sf_body (rf frame))
                                                            (sf_body_len (rf frame))))) eqn:C2;
    [intros H; discriminate H|].
  intros H. injection H; intros; subst B'.
  apply orb_false_iff in C1 as [C1 C1e]. apply orb_false_iff in C1 as [C1 C1d].
  apply orb_false_iff in C1 as [C1 C1c]. apply orb_false_iff in C1 as [C1a C1b].
  apply negb_false_iff in C1a. apply Z.eqb_eq in C1a. unfold SPEC_OK in C1a.
  destruct (csf_rf_ok frame C1a) as (L30 & Hsrc & Hdst & Hbody & Hbl0 & Hbl & Hb16).
  rewrite Hsrc in C1b. rewrite Hdst in C1d. rewrite Hbody in C1e, C2.
  apply negb_false_iff in C1b. apply csf_beq in C1b.
  apply negb_false_iff in C1c. unfold truth in C1c. apply negb_true_iff in C1c. apply Z.eqb_neq in C1c.
  apply negb_false_iff in C1d. apply csf_beq in C1d.
  apply Z.leb_gt in C1e.
  apply orb_false_iff in C2 as [C2 C2c]. apply orb_false_iff in C2 as [C2a C2b].
  apply negb_false_iff in C2a. apply Z.eqb_eq in C2a.
  apply negb_false_iff in C2b.
  apply negb_false_iff in C2c. apply Z.eqb_eq in C2c.
  repeat split; try assumption; try reflexivity.
Qed.

Ltac weq := first [ reflexivity | (f_equal; lia) | (rewrite !unsigned_lit by lia; first [reflexivity | (f_equal; lia)]) ].
Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.
Ltac brf tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac] end.

Theorem check_sent_frame_holds : bcmp_contract -> check_sent_frame_contract.
Proof.
  intros BC. unfold check_sent_frame_contract, check_sent_frame_ENTRY, check_sent_frame_FRAME.
  unfold BCMP in BC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' fa fp frame -> -> -> Hfa HFR OWF SFR OWP WM HM S16 ST LO WOS MI.
  unfold off_window in OWF, OWP. unfold w_off_stack in WOS.
  destruct SFR as (Hfp0 & Hfp8 & SB & HSB & LSB & SB0 & SB8 & SB16 & SB24 & SB26 & SB28 & SB30 & SB32 & SB36 & SB40
    & SB41 & SB48 & SB56 & SB64 & SB72).
  clear SB24 SB26 SB30 SB32 SB36 SB40 SB41 SB64 SB72.
  destruct (csf_model B B' frame HM) as (-> & Hcode & HHOST & HDK & HDESK & HSYS & HN & HZ & HSUM).
  clear HM.
  destruct (csf_rf_ok frame Hcode) as (L30 & Hsrc & Hdst & Hbody & Hbl0 & Hbl & Hb16).
  set (len := Z.of_nat (length frame)) in *.
  assert (Elen : len = Z.of_nat (length frame)) by reflexivity.
  set (blen := sf_body_len (rf frame)) in *.
  clearbody len blen.
  assert (P8 : u_at SB 8 8 = fa).
  { rewrite SB8. unfold sf_ptr. rewrite Hcode, Hdst. change (0 =? SPEC_OK) with true. cbv iota. lia. }
  assert (P16 : u_at SB 16 8 = fa + 6).
  { rewrite SB16. unfold sf_ptr. rewrite Hcode, Hsrc. change (0 =? SPEC_OK) with true. cbv iota. lia. }
  assert (P48 : u_at SB 48 8 = fa + 30).
  { rewrite SB48. unfold sf_ptr. rewrite Hcode, Hbody. change (0 =? SPEC_OK) with true. cbv iota. lia. }
  clear SB8 SB16 SB48.
  pose proof (wm_len rsegs W_BASE_PLAIN m B WM) as LB.
  pose proof (bytes_at_bound rsegs m fa frame HFR) as FB.
  pose proof (bytes_at_bound rsegs m fp SB HSB) as PB. rewrite LSB in PB.
  pose proof (s32_range B 0) as R0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  wk_facts.
  (* the two bcmp calls *)
  assert (HHB : bytes_at rsegs m 66688 HOST).
  { apply ro_bytes_at; [exact MI | lia | vm_compute; discriminate |]. apply ro_bytes_b_sound. vm_compute. reflexivity. }
  assert (HF6 : bytes_at rsegs m (fa + 6) (sub frame 6 6)) by (apply csf_bytes_sub; [exact HFR | lia | lia]).
  assert (HF0 : bytes_at rsegs m fa (sub frame 0 6)).
  { replace fa with (fa + 0) at 1 by lia. apply csf_bytes_sub; [exact HFR | lia | lia]. }
  assert (L6a : length (sub frame 6 6) = 6%nat) by (apply length_sub; lia).
  assert (L6b : length HOST = 6%nat) by reflexivity.
  destruct (memcmp_model_total (sub frame 6 6) HOST 6 ltac:(lia) ltac:(lia)) as [v1 Hv1].
  pose proof (csf_memcmp 6 (sub frame 6 6) HOST v1 ltac:(lia) ltac:(lia) Hv1) as [[V1a V1b] V1r].
  assert (V10 : v1 = 0) by (apply V1b; rewrite HHOST; reflexivity).
  subst v1. clear V1a V1b V1r.
  assert (L6c : length (sub frame 0 6) = 6%nat) by (apply length_sub; lia).
  assert (L6d : length (sub B 4 6) = 6%nat) by (apply length_sub; lia).
  destruct (memcmp_model_total (sub frame 0 6) (sub B 4 6) 6 ltac:(lia) ltac:(lia)) as [v2 Hv2].
  pose proof (csf_memcmp 6 (sub frame 0 6) (sub B 4 6) v2 ltac:(lia) ltac:(lia) Hv2) as [[V2a V2b] V2r].
  assert (V20 : v2 = 0) by (apply V2b; rewrite HDESK; reflexivity).
  subst v2. clear V2a V2b V2r.
  carve_frame 32%nat ST.
  do 6 step.
  let mm := cur_mem in pose proof (csf_rd mm fp SB 0 4 HSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD0.
  step.
  rewrite wm_lw, SB0, Hcode. clear RD0.
  step.
  brf ltac:(reflexivity).
  do 2 step.
  let mm := cur_mem in pose proof (csf_rd mm fp SB 16 8 HSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD16.
  step.
  rewrite wm_ld, P16. clear RD16.
  do 4 step.
  (* bcmp (f->src, HOST, 6) *)
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := sub frame 6 6) (rs := HOST) (v := 0);
      [ rewrite unsigned_lit by lia; exact HF6
      | rewrite unsigned_lit by lia; exact HHB
      | rewrite unsigned_lit by lia; exact Hv1
      | assumption ]
    | wk_post_call rsegs mm ].
  step.
  brf ltac:(reflexivity).
  do 4 step.
  brf ltac:(rewrite csf_eqb0_s32 by lia; apply Z.eqb_neq; exact HDK).
  let mm := cur_mem in pose proof (csf_rd mm fp SB 8 8 HSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD8.
  step.
  rewrite wm_ld, P8. clear RD8.
  do 3 step.
  (* bcmp (f->dst, M.desk, 6) *)
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := sub frame 0 6) (rs := sub B 4 6) (v := 0);
      [ rewrite unsigned_lit by lia; exact HF0
      | rewrite unsigned_lit by lia; apply (wm_src rsegs W_BASE_PLAIN mm B 4 6); [exact WM | lia | lia | lia]
      | rewrite unsigned_lit by lia; exact Hv2
      | assumption ]
    | wk_post_call rsegs mm ].
  step.
  brf ltac:(reflexivity).
  (* ---- from here on the memory does not change: the rest of the walk, by its join points ---- *)
  assert (HN' : len = Z.max 60 (30 + blen)) by (rewrite HN; destruct (Z.ltb_spec (30 + blen) 60); lia).
  assert (HZ' : forall k, 30 + blen <= k < len -> u_at frame k 1 = 0).
  { intros k Hk. rewrite <- (Z2Nat.id k) by lia. apply (csf_zero frame (Z.to_nat (30 + blen)) HZ). lia. }
  pose proof (s32_range B 65044) as R65044.
  (* 0x15000: f->sum against the sum the code computed (both in a3, a2), then the epilogue *)
  let mm := cur_mem in
  assert (Kend : forall (q1 q5 q6 q7 q8 q9 q10 q11 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 : word),
    q13 = Z_to_bv 64 (sf_sum (rf frame)) ->
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp q5 q6 q7 q8 q9 q10 q11
                          (Z_to_bv 64 (sf_sum (rf frame))) q13 q14 q15 q16 q17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          q28 q29 q30 q31) F (Z_to_bv 64 86016) fc None mm (seg_rom rsegs))).
  { intros q1 q5 q6 q7 q8 q9 q10 q11 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 ->.
    step.
    brf ltac:(unfold bv_eqb; rewrite Z.eqb_refl; reflexivity).
    do 4 step.
    release_frame FR ST (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 15 eexists. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [reflexivity | eassumption]. }
  (* 0x14fe8: the body sum loop, j bytes added *)
  let mm := cur_mem in
  assert (SUM : forall k j (q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 : word),
    Z.of_nat k = blen - j -> 0 <= j < blen ->
    q10 = Z_to_bv 64 (fa + 30 + j) -> q11 = Z_to_bv 64 (fa + 30 + blen) ->
    q12 = Z_to_bv 64 (sf_sum (rf frame)) -> q13 = Z_to_bv 64 (csum frame 30 (Z.to_nat j)) ->
    sf_sum (rf frame) = csum frame 30 (Z.to_nat blen) mod 65536 ->
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
                          q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31) F (Z_to_bv 64 85992) fc None mm (seg_rom rsegs))).
  { induction k as [|k IH];
      intros j q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 Hk Hj -> -> -> -> HS; [lia|].
    pose proof (csum_range frame 30 (Z.to_nat j)) as CR.
    pose proof (csf_u1_range frame (30 + j)) as UR.
    let mm := cur_mem in pose proof (csf_rd mm fa frame (30 + j) 1 HFR ltac:(lia) ltac:(lia)) as RD.
    step. rewrite wm_lbu. clear RD.
    step. step.
    try rewrite (unsigned_lit (csum frame 30 (Z.to_nat j))) by lia.
    try rewrite (unsigned_lit (u_at frame (30 + j) 1)) by lia.
    step.
    rewrite csf_eqb_le by lia.
    destruct (Z.eqb_spec (fa + 30 + j + 1) (fa + 30 + blen)) as [E|E]; cbn [negb]; cbv iota.
    - step. step.
      apply Kend. f_equal. rewrite csf_shift by lia. rewrite HS. f_equal.
      replace (Z.to_nat blen) with (S (Z.to_nat j)) by lia. cbn [csum]. rewrite Z2Nat.id by lia. reflexivity.
    - apply (IH (j + 1));
        [ lia | lia | f_equal; lia | reflexivity | reflexivity
        | f_equal; replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia; cbn [csum]; rewrite Z2Nat.id by lia;
          reflexivity
        | exact HS ]. }
  (* 0x14fbc: len = n and the padding is zero; then the sum *)
  let mm := cur_mem in
  assert (Kbc : forall (q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 : word),
    q12 = Z_to_bv 64 len -> q13 = Z_to_bv 64 1 ->
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp q5 q6 q7 (Z_to_bv 64 fp) (Z_to_bv 64 len)
                          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 blen) q12 q13 q14 q15 q16 q17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          q28 q29 q30 q31) F (Z_to_bv 64 85948) fc None mm (seg_rom rsegs))).
  { intros q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 -> ->.
    step.
    brf ltac:(unfold bv_eqb; rewrite Z.eqb_refl; reflexivity).
    step.
    brf ltac:(reflexivity).
    let mm := cur_mem in pose proof (csf_rd mm fp SB 28 2 HSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD28.
    step. rewrite wm_lhu, SB28. clear RD28.
    step. step.
    rewrite csf_eqb by lia.
    destruct (Z.eqb_spec blen 0) as [E0|E0]; cbv iota.
    - apply Kend. f_equal. rewrite HSUM, E0. destruct (s32_at B 65044 =? 1); reflexivity.
    - do 4 step.
      rewrite csf_eqb_sgn by lia.
      destruct (Z.eqb_spec (s32_at B 65044) 1) as [E1|E1]; cbv iota.
      + apply Kend. f_equal. rewrite HSUM. try rewrite E1. reflexivity.
      + do 2 step.
        apply (SUM (Z.to_nat blen) 0); [lia | lia | weq | weq | reflexivity | reflexivity | ].
        rewrite HSUM. try (replace (s32_at B 65044 =? 1) with false by (symmetry; apply Z.eqb_neq; exact E1)).
        cbv iota. apply csf_sum_at; lia. }
  (* 0x14f98: the padding loop, i bytes checked *)
  let mm := cur_mem in
  assert (ZL : forall k i (q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 : word),
    Z.of_nat k = len - (30 + blen) - i -> 0 <= i < len - (30 + blen) ->
    q12 = Z_to_bv 64 len -> q13 = Z_to_bv 64 (fa + (blen + 30) + i) -> q14 = Z_to_bv 64 1 ->
    q18 = Z_to_bv 64 (fa + len) ->
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp q5 q6 q7 (Z_to_bv 64 fp) (Z_to_bv 64 len)
                          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 blen) q12 q13 q14 q15 q16 q17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          q28 q29 q30 q31) F (Z_to_bv 64 85912) fc None mm (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 Hk Hi -> -> -> ->; [lia|].
    let mm := cur_mem in pose proof (csf_rd mm fa frame (blen + 30 + i) 1 HFR ltac:(lia) ltac:(lia)) as RD.
    step. rewrite wm_lbu. clear RD. rewrite (HZ' (blen + 30 + i)) by lia.
    do 5 step.
    rewrite csf_eqb_le by lia.
    destruct (Z.eqb_spec (fa + (blen + 30) + i + 1) (fa + len)) as [E|E]; cbn [negb]; cbv iota.
    - do 2 step. apply Kbc; reflexivity.
    - apply (IH (i + 1)); [lia | lia | reflexivity | f_equal; lia | reflexivity | reflexivity]. }
  (* 0x14f88: n computed; padding or not *)
  let mm := cur_mem in
  assert (K88 : forall (q1 q5 q6 q7 q12 q14 q15 q16 q17 q28 q29 q30 q31 : word),
    q12 = Z_to_bv 64 len ->
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp q5 q6 q7 (Z_to_bv 64 fp) (Z_to_bv 64 len)
                          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 blen) q12 (Z_to_bv 64 (blen + 30)) q14 q15 q16 q17
                          (Z_to_bv 64 fa) s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 85896) fc None mm (seg_rom rsegs))).
  { intros q1 q5 q6 q7 q12 q14 q15 q16 q17 q28 q29 q30 q31 ->.
    step.
    rewrite csf_ltu by lia.
    destruct (Z.ltb_spec (blen + 30) len) as [L|L]; cbn [negb]; cbv iota.
    - do 3 step.
      apply (ZL (Z.to_nat (len - (30 + blen))) 0); [lia | lia | reflexivity | weq | reflexivity | weq].
    - step. apply Kbc; reflexivity. }
  (* 0x14f74: after the system-family scan *)
  let mm := cur_mem in
  assert (K74 : forall (q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp q5 q6 q7 (Z_to_bv 64 fp) (Z_to_bv 64 len)
                          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 blen) q12 q13 q14 q15 q16 q17
                          (Z_to_bv 64 fa) s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 85876) fc None mm (seg_rom rsegs))).
  { intros q1 q5 q6 q7 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31.
    do 4 step.
    rewrite csf_ltu by lia.
    destruct (Z.ltb_spec 60 (blen + 30)) as [L|L]; cbv iota.
    - apply K88. f_equal. lia.
    - step. apply K88. f_equal. lia. }
  (* 0x14f48: the system-family scan of the body (spec_system_at, inlined), at offset i *)
  let mm := cur_mem in
  assert (LOOP : forall k i (q1 q5 q6 q7 q12 q13 q14 q28 q29 q30 q31 : word),
    Z.of_nat k = blen - 3 - i -> 0 <= i < blen - 3 ->
    q12 = Z_to_bv 64 i -> q13 = Z_to_bv 64 (fa + 31 + i) -> q14 = Z_to_bv 64 (blen - 3) ->
    evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp q5 q6 q7 (Z_to_bv 64 fp) (Z_to_bv 64 len)
                          (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 blen) q12 q13 q14 (Z_to_bv 64 240) (Z_to_bv 64 19)
                          (Z_to_bv 64 112) (Z_to_bv 64 fa) s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                     F (Z_to_bv 64 85832) fc None mm (seg_rom rsegs))).
  { induction k as [|k IH]; intros i q1 q5 q6 q7 q12 q13 q14 q28 q29 q30 q31 Hk Hi -> -> ->; [lia|].
    let mm := cur_mem in
    assert (NEXT : forall q5' : word,
      evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp q5' q6 q7 (Z_to_bv 64 fp) (Z_to_bv 64 len)
                            (Z_to_bv 64 (fa + 30)) (Z_to_bv 64 blen) (Z_to_bv 64 i) (Z_to_bv 64 (fa + 31 + i))
                            (Z_to_bv 64 (blen - 3)) (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) (Z_to_bv 64 fa)
                            s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                       F (Z_to_bv 64 85856) fc None mm (seg_rom rsegs))).
    { intros q5'. do 3 step.
      rewrite csf_eqb by lia.
      destruct (Z.eqb_spec (blen - 3) (i + 1)) as [E|E]; cbn [negb]; cbv iota.
      - step. apply K74.
      - apply (IH (i + 1)); [lia | lia | reflexivity | f_equal; lia | reflexivity]. }
    pose proof (csf_u1_range frame (30 + i)) as U0.
    pose proof (csf_u1_range frame (30 + i + 1)) as U1.
    pose proof (csf_u1_range frame (30 + i + 3)) as U3.
    let mm := cur_mem in pose proof (csf_rd mm fa frame (30 + i) 1 HFR ltac:(lia) ltac:(lia)) as RD.
    step. rewrite wm_lbu. clear RD.
    step.
    rewrite csf_eqb by lia.
    destruct (Z.eqb_spec (u_at frame (30 + i) 1) 240) as [E1|E1]; cbn [negb]; cbv iota; [|apply NEXT].
    let mm := cur_mem in pose proof (csf_rd mm fa frame (30 + i + 1) 1 HFR ltac:(lia) ltac:(lia)) as RD.
    step. rewrite wm_lbu. clear RD.
    step.
    rewrite csf_eqb by lia.
    destruct (Z.eqb_spec (u_at frame (30 + i + 1) 1) 19) as [E2|E2]; cbn [negb]; cbv iota; [|apply NEXT].
    let mm := cur_mem in pose proof (csf_rd mm fa frame (30 + i + 3) 1 HFR ltac:(lia) ltac:(lia)) as RD.
    step. rewrite wm_lbu. clear RD.
    step.
    rewrite csf_eqb by lia.
    destruct (Z.eqb_spec (u_at frame (30 + i + 3) 1) 112) as [E3|E3]; cbv iota; [|apply NEXT].
    exfalso. apply (csf_sys frame blen i HSYS); lia. }
  (* f->body_len and f->body, then the scan or not *)
  let mm := cur_mem in pose proof (csf_rd mm fp SB 56 8 HSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD56.
  step.
  rewrite wm_ld, SB56. clear RD56.
  let mm := cur_mem in pose proof (csf_rd mm fp SB 48 8 HSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD48.
  step.
  rewrite wm_ld, P48. clear RD48.
  step. step.
  rewrite csf_ltu by lia.
  destruct (Z.ltb_spec blen 4) as [L4|L4]; cbv iota.
  - apply K74.
  - do 6 step.
    apply (LOOP (Z.to_nat (blen - 3)) 0); [lia | lia | reflexivity | weq | weq].
Qed.
