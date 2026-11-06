From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract check_latest_sent_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- machine words ---- *)

Lemma ls_eqb_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (E2 : (x - y) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in E2; [|lia]. destruct E2 as [c Ec]. nia.
Qed.

Lemma ls_eqb0u : forall v, 0 <= v < 2^64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ls_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma ls_s32_mod : forall B k, s32_at B k mod 2^32 = u_at B k 4.
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma ls_s32_small : forall B k, u_at B k 4 < 2^31 -> s32_at B k = u_at B k 4.
Proof.
  intros B k H. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ls_s32_eqb : forall B k v, 0 <= v < 2^31 -> (s32_at B k =? v) = (u_at B k 4 =? v).
Proof.
  intros B k v Hv. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  destruct (Z.eqb_spec (u_at B k 4) v) as [E|E].
  - rewrite ls_s32_small by lia. rewrite E. apply Z.eqb_refl.
  - apply Z.eqb_neq. intros C. apply E. rewrite <- ls_s32_mod, C. apply Z.mod_small. lia.
Qed.

Lemma ls_ltu_s32 : forall B k v, 0 <= v < 2^31 -> v < u_at B k 4 ->
  bv_ltu (Z_to_bv 64 v) (Z_to_bv 64 (s32_at B k)) = true.
Proof.
  intros B k v Hv Hlt. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold bv_ltu. rewrite !unsigned_lit_wrap. rewrite (Z.mod_small v) by lia. apply Z.ltb_lt.
  destruct (Z_lt_le_dec (u_at B k 4) (2^31)) as [L|L].
  - rewrite ls_s32_small by lia. rewrite Z.mod_small by lia. lia.
  - assert (S32 : s32_at B k = u_at B k 4 - 2^32).
    { unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
      Z.div_mod_to_equations. lia. }
    rewrite S32. rewrite <- (Z.mod_add (u_at B k 4 - 2^32) 1 (2^64)) by lia.
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma ls_mod64_32 : forall z, (z mod 2^64) mod 2^32 = z mod 2^32.
Proof.
  intros z. rewrite (Z.mod_eq z (2^64)) by lia.
  replace (z - 2^64 * (z / 2^64)) with (z + (- (2^32 * (z / 2^64))) * 2^32) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma ls_le4_mod : forall x y, x mod 2^32 = y mod 2^32 -> le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 y).
Proof.
  intros x y H. unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 (x mod 2^64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (y mod 2^64) 32) by (cbn; lia).
  rewrite !ls_mod64_32, H. reflexivity.
Qed.

Lemma ls_put_s32 : forall B k, put 4 (s32_at B k) = put 4 (u_at B k 4).
Proof.
  intros B k. pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold put. rewrite <- (Z_to_le_bytes_mod 4 (s32_at B k) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (u_at B k 4) 32) by (cbn; lia).
  rewrite ls_s32_mod, (Z.mod_small (u_at B k 4)) by lia. reflexivity.
Qed.

Lemma ls_lor_mod : forall a b c d, a mod 2^32 = b mod 2^32 -> c mod 2^32 = d mod 2^32 ->
  Z.lor a c mod 2^32 = Z.lor b d mod 2^32.
Proof.
  intros a b c d H1 H2. rewrite <- !(Z.land_ones _ 32) by lia. rewrite !Z.land_lor_distr_l.
  rewrite !(Z.land_ones _ 32) by lia. rewrite H1, H2. reflexivity.
Qed.

Lemma ls_swrap_mod : forall d, bv_swrap 32 d mod 2^32 = d mod 2^32.
Proof.
  intros d. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. lia.
Qed.

(* the display word the machine stores back has the model's low 32 bits *)
Lemma ls_disp_le4 : forall d cd,
  le4 (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 (Z_to_bv 64 d))) (bv_unsigned (Z_to_bv 64 cd))))
  = le4 (Z_to_bv 64 (Z.lor d cd)).
Proof.
  intros d cd. apply ls_le4_mod. unfold sx32. rewrite !unsigned_lit_wrap.
  apply ls_lor_mod.
  - rewrite ls_mod64_32, ls_swrap_mod. apply ls_mod64_32.
  - apply ls_mod64_32.
Qed.

Lemma ls_c4_swap : forall (mm : word -> option byte) A v v', le4 v = le4 v' ->
  rw_cells rsegs mm A [C4 v] -> rw_cells rsegs mm A [C4 v'].
Proof.
  intros mm A v v' H [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes] in *. rewrite <- H. exact Hb.
  - cbn [cells_size csize] in *. exact Hw.
Qed.

Lemma ls_shl32_shr30 : forall k, 0 <= k < 2^32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 32))) 30 = 4 * k.
Proof.
  intros k Hk. rewrite (unsigned_lit k) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by nia. rewrite Z.shiftr_div_pow2 by lia.
  replace (k * 2^32) with (4 * k * 2^30) by lia. apply Z.div_mul. lia.
Qed.

Lemma ls_addiw : forall k, 0 <= k < 2^30 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 k) + 1)) = Z_to_bv 64 (k + 1).
Proof.
  intros k Hk. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* ---- list bridges ---- *)

Lemma ls_firstn1 : forall (l : list byte) n,
  firstn 1 (skipn n l) = match nth_error l n with Some x => [x] | None => [] end.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH.
Qed.

Lemma ls_at8_ne : forall (l : list byte) n,
  at8 l n = match nth_error l n with Some x => bv_unsigned x | None => 0 end.
Proof.
  intros l n. revert l. unfold at8, bz. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH.
Qed.

Lemma ls_u_at8 : forall (l : list byte) k j, 0 <= k -> 0 <= j ->
  u_at l (k + j) 1 = at8 (skipn (Z.to_nat k) l) (Z.to_nat j).
Proof.
  intros l k j Hk Hj. unfold u_at, sub. rewrite ls_firstn1, ls_at8_ne.
  replace (Z.to_nat (k + j)) with (Z.to_nat k + Z.to_nat j)%nat by lia.
  rewrite <- nth_skipn.
  destruct (nth_error (skipn (Z.to_nat k) l) (Z.to_nat j)); cbn;
    [rewrite Z.shiftl_0_l, Z.lor_0_r; reflexivity | reflexivity].
Qed.

Lemma ls_bsub : forall mm a bs k n, bytes_at rsegs mm a bs -> 0 <= k -> (Z.to_nat k + n <= length bs)%nat ->
  bytes_at rsegs mm (a + k) (sub bs k n).
Proof.
  intros mm a bs k n (Ha & Hl & H) Hk Hn.
  assert (Ln : length (sub bs k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Ln; lia|].
  intros i Hi. rewrite Ln in Hi.
  rewrite ne_sub by lia. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

Lemma ls_rd : forall mm a bs k n, bytes_at rsegs mm a bs -> 0 <= k -> (Z.to_nat k + n <= length bs)%nat ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (a + k)) n = Some (sub bs k n).
Proof. intros. apply bytes_at_read; assumption. Qed.

Lemma ls_beq : forall l r, beq_bytes l r = true -> l = r.
Proof.
  intros l r H. unfold beq_bytes in H. destruct (list_eq_dec Z.eq_dec (zs l) (zs r)) as [E|E]; [|discriminate].
  clear H. unfold zs in E. revert r E. induction l as [|a l IH]; intros [|b r] E; cbn in E; try discriminate.
  - reflexivity.
  - injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma ls_memcmp_refl : forall l n, length l = n -> memcmp_model l l n = Some 0.
Proof.
  induction l as [|a l IH]; intros n H; cbn in H; subst n; [reflexivity|].
  cbn [memcmp_model]. rewrite Z.eqb_refl. apply IH. reflexivity.
Qed.

(* ---- the model ---- *)

Lemma ls_exit : forall fuel Bc body len pos dispc B' disp',
  latest_sent_loop fuel Bc body len pos dispc = Some (B', disp') -> len <= pos -> B' = Bc /\ disp' = dispc.
Proof.
  intros [|fuel] Bc body len pos dispc B' disp' H Hp; [discriminate|].
  cbn [latest_sent_loop] in H. rewrite (proj2 (Z.ltb_ge pos len) Hp) in H. injection H as <- <-. auto.
Qed.

Lemma ls_qrm : forall Bc s B2, q_remove_m Bc s = Some (B2, tt) ->
  exists B1 k, q_remove_loop (S (Z.to_nat CMDS_MAX)) Bc s (g_nq Bc) 0 0 = Some (B1, k) /\ B2 = set_g_nq B1 k.
Proof.
  intros Bc s B2 H. unfold q_remove_m in H.
  destruct (q_remove_loop (S (Z.to_nat CMDS_MAX)) Bc s (g_nq Bc) 0 0) as [[B1 k]|] eqn:E; [|discriminate].
  injection H as <-. exists B1, k. split; reflexivity.
Qed.

Lemma ls_q_step : forall fuel Bc s nq i k Bf kf,
  q_remove_loop fuel Bc s nq i k = Some (Bf, kf) -> i < nq ->
  exists fuel', fuel = S fuel' /\ i < CMDS_MAX /\
    (if Q_at Bc i =? s then q_remove_loop fuel' Bc s nq (i + 1) k = Some (Bf, kf)
     else q_remove_loop fuel' (set_Q_at Bc k (Q_at Bc i)) s nq (i + 1) (k + 1) = Some (Bf, kf)).
Proof.
  intros [|fuel] Bc s nq i k Bf kf H Hi; [discriminate|]. cbn [q_remove_loop] in H.
  rewrite (proj2 (Z.ltb_lt _ _) Hi) in H.
  destruct (CMDS_MAX <=? i) eqn:C; [discriminate|]. apply Z.leb_gt in C.
  exists fuel. split; [reflexivity|]. split; [exact C|]. destruct (Q_at Bc i =? s); exact H.
Qed.

Lemma ls_q_exit : forall fuel Bc s nq i k Bf kf,
  q_remove_loop fuel Bc s nq i k = Some (Bf, kf) -> nq <= i -> Bf = Bc /\ kf = k.
Proof.
  intros [|fuel] Bc s nq i k Bf kf H Hi; [discriminate|]. cbn [q_remove_loop] in H.
  rewrite (proj2 (Z.ltb_ge _ _) Hi) in H. injection H as <- <-. auto.
Qed.

Lemma ls_q_nqle : forall fuel Bc s nq i k Bf kf,
  q_remove_loop fuel Bc s nq i k = Some (Bf, kf) -> i <= CMDS_MAX -> nq <= CMDS_MAX.
Proof.
  induction fuel as [|fuel IH]; intros Bc s nq i k Bf kf H Hi; [discriminate|].
  cbn [q_remove_loop] in H.
  destruct (Z.ltb_spec i nq) as [L|L]; [|lia].
  destruct (CMDS_MAX <=? i) eqn:C; [discriminate|]. apply Z.leb_gt in C.
  destruct (Q_at Bc i =? s).
  - exact (IH Bc s nq (i + 1) k Bf kf H ltac:(lia)).
  - exact (IH (set_Q_at Bc k (Q_at Bc i)) s nq (i + 1) (k + 1) Bf kf H ltac:(lia)).
Qed.

Lemma ls_round : forall fuel Bc body len pos dispc B' disp',
  latest_sent_loop (S fuel) Bc body len pos dispc = Some (B', disp') ->
  0 <= pos < len -> Z.of_nat (length body) = len ->
  exists s B2,
    3 <= len - pos /\
    u_at body pos 1 = TAG /\
    s = Z.lor (Z.shiftl (u_at body (pos + 2) 1) 7) (u_at body (pos + 1) 1) /\
    0 <= s < CMDS_MAX /\ s < g_ncmd Bc /\
    Cmd_st Bc s = PENDING /\
    Cmd_len Bc s <= len - pos /\
    sub body pos (Z.to_nat (Cmd_len Bc s)) = sub Bc (A_Cmd_bytes s) (Z.to_nat (Cmd_len Bc s)) /\
    q_remove_m (set_Cmd_st Bc s SENT) s = Some (B2, tt) /\
    latest_sent_loop fuel B2 body len (pos + Cmd_len Bc s) (Z.lor dispc (Cmd_display B2 s)) = Some (B', disp').
Proof.
  intros fuel Bc body len pos dispc B' disp' H Hpos Hlen.
  cbn [latest_sent_loop] in H. rewrite (proj2 (Z.ltb_lt pos len) ltac:(lia)) in H.
  unfold tagged_of_m in H.
  destruct (Z.ltb_spec (len - pos) 3) as [H3|H3]; cbv beta iota in H; [discriminate|].
  destruct (Nat.ltb_spec (length (skipn (Z.to_nat pos) body)) 1) as [H1|H1]; cbv beta iota in H; [discriminate|].
  destruct (Z.eqb_spec (at8 (skipn (Z.to_nat pos) body) 0) TAG) as [HT|HT];
    cbn [negb] in H; cbv beta iota in H; [|discriminate].
  destruct (Nat.ltb_spec (length (skipn (Z.to_nat pos) body)) 3) as [H4|H4]; cbv beta iota in H; [discriminate|].
  set (sv := Z.lor (at8 (skipn (Z.to_nat pos) body) 1) (Z.shiftl (at8 (skipn (Z.to_nat pos) body) 2) 7)) in *.
  destruct (Z.ltb_spec sv (g_ncmd Bc)) as [Hs1|Hs1]; cbv beta iota in H; [|discriminate].
  destruct (Z.leb_spec CMDS_MAX sv) as [Hs2|Hs2]; cbv beta iota in H; [discriminate|].
  destruct (negb (Cmd_st Bc sv =? PENDING) || (len - pos <? Cmd_len Bc sv)
            || negb (beq_bytes (firstn (Z.to_nat (Cmd_len Bc sv)) (skipn (Z.to_nat pos) body))
                               (sub Bc (A_Cmd_bytes sv) (Z.to_nat (Cmd_len Bc sv))))) eqn:EC;
    cbv beta iota in H; [discriminate|].
  apply orb_false_iff in EC. destruct EC as [EC1 EC3]. apply orb_false_iff in EC1. destruct EC1 as [EC1 EC2].
  apply negb_false_iff in EC1. apply Z.eqb_eq in EC1.
  apply Z.ltb_ge in EC2. apply negb_false_iff in EC3. apply ls_beq in EC3.
  destruct (q_remove_m (set_Cmd_st Bc sv SENT) sv) as [[B2 []]|] eqn:EQ; cbv beta iota in H; [|discriminate].
  exists sv, B2.
  assert (A0 : u_at body pos 1 = at8 (skipn (Z.to_nat pos) body) 0).
  { replace pos with (pos + 0) at 1 by lia. apply ls_u_at8; lia. }
  assert (A1 : u_at body (pos + 1) 1 = at8 (skipn (Z.to_nat pos) body) 1).
  { rewrite (ls_u_at8 body pos 1) by lia. reflexivity. }
  assert (A2 : u_at body (pos + 2) 1 = at8 (skipn (Z.to_nat pos) body) 2).
  { rewrite (ls_u_at8 body pos 2) by lia. reflexivity. }
  assert (SN : 0 <= sv).
  { unfold sv. apply Z.lor_nonneg. split.
    - rewrite <- A1. unfold u_at. apply ble_range.
    - apply Z.shiftl_nonneg. rewrite <- A2. unfold u_at. apply ble_range. }
  split; [lia|]. split; [rewrite A0; exact HT|].
  split; [unfold sv; rewrite A1, A2; apply Z.lor_comm|].
  split; [lia|]. split; [exact Hs1|]. split; [exact EC1|]. split; [exact EC2|].
  split; [unfold sub; exact EC3|]. split; [exact EQ | exact H].
Qed.

Theorem check_latest_sent_holds : bcmp_contract -> check_latest_sent_contract.
Proof.
  intros BC. unfold bcmp_contract, BCMP in BC.
  unfold check_latest_sent_contract, check_latest_sent_ENTRY, check_latest_sent_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' bp len dp body junk disp
    Ea0 Ea1 Ea2 Hbp HB Hlen HBW HBwin Hdp4 HDP HDW HDwin HBD WM HM Hsp ST LO WOS MI.
  subst a0 a1 a2.
  pose proof (bytes_at_bound rsegs m bp body HB) as HBB. rewrite Hlen in HBB.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (dp, dp + 4);
                          (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold check_latest_sent_m in HM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  wk_facts. unfold w_off_stack in WOS. unfold off_window in HBwin, HDwin. unfold off_world in HDW.
  unfold OFF_g_cmd in HBW.
  carve_frame 112%nat ST.
  do 14 step.
  lazymatch goal with H : rw_cells rsegs ?mm (bv_unsigned sp + -112) ?cs |- _ => set (FRC := cs) in H end.
  assert (FRCSZ : cells_size FRC = 112%nat) by (unfold FRC; cbn [cells_size csize]; reflexivity).
  step.
  (* the epilogue, 0x15364 *)
  assert (EPI : forall (m2 : word -> option byte)
                  (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                   x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -112) FRC ->
    rw_cells rsegs m2 dp [C4 (Z_to_bv 64 disp)] ->
    stk rsegs m2 lo (bv_unsigned sp + -112) ->
    munch [(bv_unsigned sp + -112, bv_unsigned sp); (dp, dp + 4); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m2 ->
    wmono rsegs m m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B' ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x15364) fc None m2 (seg_rom rsegs))).
  { intros m2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31 FR2 DP2 ST2 MU2 WMo2 MI2 WM2.
    unfold FRC in FR2.
    do 13 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    step. step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WMo2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact DP2 | exact WM2]. }
  (* the command loop, 0x152a4 *)
  assert (OUTER : forall fuel pos dispc Bc (m2 : word -> option byte)
                    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x25 x28 x29 x30 x31 : word),
    latest_sent_loop fuel Bc body len pos dispc = Some (B', disp) ->
    0 <= pos < len ->
    x23 = Z_to_bv 64 (s32_at Bc 64980) ->
    u_at Bc 64984 4 = u_at B 64984 4 ->
    rw_cells rsegs m2 (bv_unsigned sp + -112) FRC ->
    rw_cells rsegs m2 dp [C4 (Z_to_bv 64 dispc)] ->
    stk rsegs m2 lo (bv_unsigned sp + -112) ->
    munch [(bv_unsigned sp + -112, bv_unsigned sp); (dp, dp + 4); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m2 ->
    wmono rsegs m m2 -> mem_inv rsegs m2 -> wmem rsegs m2 Bc -> bytes_at rsegs m2 bp body ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 bp) x19 (Z_to_bv 64 pos) x21 (Z_to_bv 64 267608) x23 (Z_to_bv 64 271704) x25
                          (Z_to_bv 64 (s32_at B 64984)) (Z_to_bv 64 226648) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x152a4) fc None m2 (seg_rom rsegs))).
  { induction fuel as [|fuel IH];
      intros pos dispc Bc m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x25 x28 x29 x30 x31
        HL Hpos -> HNC FR2 DP2 ST2 MU2 WMo2 MI2 WM2 HBY; [discriminate|].
    destruct (ls_round fuel Bc body len pos dispc B' disp HL Hpos Hlen) as
      (s & B2 & H3 & HTAG & Hsdef & Hsr & Hsnc & HST & HTL & HBYTES & HQR & HNEXT).
    unfold CMDS_MAX in Hsr.
    pose proof (wm_len rsegs W_BASE_PLAIN m2 Bc WM2) as LBc.
    assert (LBcZ : Z.of_nat (length Bc) = 65616) by (rewrite LBc; unfold W_LEN; lia).
    set (tl := Cmd_len Bc s) in *.
    assert (RTL : 0 <= tl < 256)
      by (unfold tl, Cmd_len; pose proof (u_at_range Bc (A_Cmd_len s) 1) as R; cbn in R; lia).
    pose proof (u_at_range body (pos + 1) 1) as R1. pose proof (u_at_range body (pos + 2) 1) as R2.
    change (8 * Z.of_nat 1) with 8 in R1, R2.
    destruct (ls_qrm _ _ _ HQR) as (B1q & kf & HQL & HB2). subst B2.
    set (nqv := g_nq Bc) in *.
    assert (HNQ : g_nq (set_Cmd_st Bc s SENT) = nqv).
    { unfold nqv, g_nq, set_Cmd_st. apply u_at_upd_out;
        [unfold A_Cmd_st, OFF_g_cmd; lia | unfold OFF_g_nq; lia
        | right; rewrite length_put; unfold A_Cmd_st, OFF_g_cmd, OFF_g_nq; lia
        | rewrite length_put; unfold A_Cmd_st, OFF_g_cmd; lia]. }
    rewrite HNQ in HQL.
    assert (HNQ1 : nqv <= CMDS_MAX) by (apply (ls_q_nqle _ _ _ _ _ _ _ _ HQL); unfold CMDS_MAX; lia).
    assert (RNQ : 0 <= nqv) by (unfold nqv, g_nq; apply u_at_range).
    assert (HS32NQ : s32_at Bc 64980 = nqv)
      by (unfold nqv, g_nq, OFF_g_nq; apply ls_s32_small; unfold CMDS_MAX in HNQ1; unfold g_nq, OFF_g_nq in *; lia).
    unfold CMDS_MAX in HNQ1.
    (* 0x15348: g_nq := k, then the display *)
    assert (TAIL : forall (m3 : word -> option byte) Bqf kfin
                     (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 : word),
      latest_sent_loop fuel (set_g_nq Bqf kfin) body len (pos + tl)
        (Z.lor dispc (Cmd_display (set_g_nq Bqf kfin) s)) = Some (B', disp) ->
      0 <= kfin <= 1024 ->
      u_at Bqf 64984 4 = u_at B 64984 4 ->
      rw_cells rsegs m3 (bv_unsigned sp + -112) FRC ->
      rw_cells rsegs m3 dp [C4 (Z_to_bv 64 dispc)] ->
      stk rsegs m3 lo (bv_unsigned sp + -112) ->
      munch [(bv_unsigned sp + -112, bv_unsigned sp); (dp, dp + 4); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m3 ->
      wmono rsegs m m3 -> mem_inv rsegs m3 -> wmem rsegs m3 Bqf -> bytes_at rsegs m3 bp body ->
      evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp y5 y6 y7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 bp) (Z_to_bv 64 tl) (Z_to_bv 64 pos) y21 (Z_to_bv 64 267608)
                            (Z_to_bv 64 kfin) (Z_to_bv 64 271704) (Z_to_bv 64 (226648 + s * 40))
                            (Z_to_bv 64 (s32_at B 64984)) (Z_to_bv 64 226648) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x15348) fc None m3 (seg_rom rsegs))).
    { intros m3 Bqf kfin y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31
        HLT HKF HNC3 FR3 DP3 ST3 MU3 WMo3 MI3 WM3 HBY3.
      pose proof (wm_len rsegs W_BASE_PLAIN m3 Bqf WM3) as LBq.
      assert (LBqZ : Z.of_nat (length Bqf) = 65616) by (rewrite LBq; unfold W_LEN; lia).
      (* sw s7,12(s8) *)
      step.
      lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ (upd Bqf 64980 (put 4 kfin))] |- _ =>
        replace (upd Bqf 64980 (put 4 kfin)) with (set_g_nq Bqf kfin) in H
          by (unfold set_g_nq, OFF_g_nq; reflexivity) end.
      (* lw a0,8(s9) *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (RDD : ov_read_bytes rsegs mm (Z_to_bv 64 (226648 + s * 40 + 8)) 4
                      = Some (sub (set_g_nq Bqf kfin) (A_Cmd_display s) 4))
        by (apply (wm_read rsegs W_BASE_PLAIN mm (set_g_nq Bqf kfin));
            [assumption | unfold A_Cmd_display, OFF_g_cmd; lia | unfold A_Cmd_display, OFF_g_cmd; lia
            | f_equal; unfold A_Cmd_display, OFF_g_cmd; lia]) end.
      step.
      rewrite ?wm_lw.
      change (s32_at (set_g_nq Bqf kfin) (A_Cmd_display s)) with (Cmd_display (set_g_nq Bqf kfin) s).
      (* lw a1,0(s0); or a0,a1,a0; add s4,s4,s3; sw a0,0(s0) *)
      do 4 step.
      lazymatch goal with H : rw_cells rsegs ?mm dp [C4 ?v] |- _ =>
        apply (ls_c4_swap mm dp v (Z_to_bv 64 (Z.lor dispc (Cmd_display (set_g_nq Bqf kfin) s)))) in H;
          [| apply ls_disp_le4] end.
      (* bltu s4,s1 *)
      step.
      rewrite ?(unsigned_lit pos), ?(unsigned_lit tl) by lia.
      rewrite ls_ltu_lit by lia.
      destruct (Z.ltb_spec (pos + tl) len) as [Lt|Ge]; cbv iota.
      - apply (IH (pos + tl) (Z.lor dispc (Cmd_display (set_g_nq Bqf kfin) s)) (set_g_nq Bqf kfin));
          [ exact HLT | lia | | | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption ].
        + assert (UU : u_at (set_g_nq Bqf kfin) 64980 4 = kfin).
          { unfold set_g_nq, OFF_g_nq. rewrite u_at_upd_put by lia.
            change (8 * Z.of_nat 4) with 32. apply Z.mod_small. lia. }
          f_equal. symmetry. rewrite (ls_s32_small (set_g_nq Bqf kfin) 64980) by (rewrite UU; lia). exact UU.
        + unfold set_g_nq. rewrite u_at_upd_out by
            (rewrite ?length_put; unfold OFF_g_nq; lia). exact HNC3.
      - destruct (ls_exit _ _ _ _ _ _ _ _ HLT ltac:(lia)) as [-> ->].
        apply EPI; assumption. }
    (* the g_q scan, 0x15324 *)
    assert (INNER : forall fuel2 i k Bq (m3 : word -> option byte)
                      (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      q_remove_loop fuel2 Bq s nqv i k = Some (B1q, kf) ->
      0 <= k <= i -> i < nqv -> i <= 1024 ->
      u_at Bq 64984 4 = u_at B 64984 4 ->
      rw_cells rsegs m3 (bv_unsigned sp + -112) FRC ->
      rw_cells rsegs m3 dp [C4 (Z_to_bv 64 dispc)] ->
      stk rsegs m3 lo (bv_unsigned sp + -112) ->
      munch [(bv_unsigned sp + -112, bv_unsigned sp); (dp, dp + 4); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m3 ->
      wmono rsegs m m3 -> mem_inv rsegs m3 -> wmem rsegs m3 Bq -> bytes_at rsegs m3 bp body ->
      evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp y5 y6 y7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                            (Z_to_bv 64 (267608 + 4 * nqv)) (Z_to_bv 64 (267608 + 4 * i)) y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 bp) (Z_to_bv 64 tl) (Z_to_bv 64 pos) (Z_to_bv 64 s) (Z_to_bv 64 267608)
                            (Z_to_bv 64 k) (Z_to_bv 64 271704) (Z_to_bv 64 (226648 + s * 40))
                            (Z_to_bv 64 (s32_at B 64984)) (Z_to_bv 64 226648) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x15324) fc None m3 (seg_rom rsegs))).
    { induction fuel2 as [|fuel2 IH2];
        intros i k Bq m3 y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31
          HQi Hki Hinq HiC HNC3 FR3 DP3 ST3 MU3 WMo3 MI3 WM3 HBY3; [discriminate|].
      destruct (ls_q_step (S fuel2) Bq s nqv i k B1q kf HQi Hinq) as (f2 & Ef2 & HiM & HQ2).
      injection Ef2 as <-. unfold CMDS_MAX in HiM.
      pose proof (wm_len rsegs W_BASE_PLAIN m3 Bq WM3) as LBq.
      assert (LBqZ : Z.of_nat (length Bq) = 65616) by (rewrite LBq; unfold W_LEN; lia).
      (* lw a2,0(a1) *)
      step.
      (* beq a2,s5 *)
      step.
      pose proof (s32_range Bq (60872 + 4 * i)) as RS1.
      rewrite ls_eqb_lit by lia.
      rewrite (ls_s32_eqb Bq (60872 + 4 * i) s) by lia.
      replace (u_at Bq (60872 + 4 * i) 4) with (Q_at Bq i) by (unfold Q_at, OFF_g_q; f_equal; lia).
      destruct (Z.eqb_spec (Q_at Bq i) s) as [EQS|EQS]; cbv iota; cbv beta iota in HQ2.
      - (* skip: 0x15340 *)
        step. step.
        rewrite ls_eqb_lit by lia.
        destruct (Z.eqb_spec (267608 + 4 * i + 4) (267608 + 4 * nqv)) as [EE|EE]; cbn [negb]; cbv iota.
        + destruct (ls_q_exit _ _ _ _ _ _ _ _ HQ2 ltac:(lia)) as [EB EK].
          rewrite EB, EK in HNEXT.
          apply (TAIL _ Bq k);
            [ exact HNEXT | lia | exact HNC3 | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption ].
        + replace (267608 + 4 * i + 4) with (267608 + 4 * (i + 1)) by lia.
          apply (IH2 (i + 1) k Bq);
            [ exact HQ2 | lia | lia | lia | exact HNC3 | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption ].
      - (* copy: 0x1532c *)
        do 4 step.
        rewrite ls_shl32_shr30 by lia.
        rewrite ?(unsigned_lit (4 * k)) by lia.
        rewrite ls_addiw by lia.
        (* sw a2,0(a3) *)
        step.
        lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ (upd Bq (60872 + 4 * k) ?v)] |- _ =>
          replace (upd Bq (60872 + 4 * k) v) with (set_Q_at Bq k (Q_at Bq i)) in H
            by (unfold set_Q_at, Q_at, OFF_g_q; rewrite ls_put_s32; f_equal; first [reflexivity | lia]) end.
        (* addi a1,a1,4; bne a1,a0 *)
        step. step.
        rewrite ls_eqb_lit by lia.
        destruct (Z.eqb_spec (267608 + 4 * i + 4) (267608 + 4 * nqv)) as [EE|EE]; cbn [negb]; cbv iota.
        + destruct (ls_q_exit _ _ _ _ _ _ _ _ HQ2 ltac:(lia)) as [EB EK].
          rewrite EB, EK in HNEXT.
          apply (TAIL _ (set_Q_at Bq k (Q_at Bq i)) (k + 1));
            [ exact HNEXT | lia | (unfold set_Q_at; rewrite u_at_upd_out by (rewrite ?length_put; unfold OFF_g_q; lia); exact HNC3) | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption ].
        + replace (267608 + 4 * i + 4) with (267608 + 4 * (i + 1)) by lia.
          apply (IH2 (i + 1) (k + 1) (set_Q_at Bq k (Q_at Bq i)));
            [ exact HQ2 | lia | lia | lia | (unfold set_Q_at; rewrite u_at_upd_out by (rewrite ?length_put; unfold OFF_g_q; lia); exact HNC3) | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption ]. }
    (* the round's walk, from 0x152a4 *)
    step.
    rewrite ?(unsigned_lit len), ?(unsigned_lit pos) by lia.
    step. step.
    rewrite ls_ltu_lit by lia.
    replace (len - pos <? 3) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
    step.
    assert (RB0 : ov_read_bytes rsegs m2 (Z_to_bv 64 (bp + pos)) 1 = Some (sub body pos 1))
      by (apply ls_rd; [exact HBY | lia | lia]).
    assert (RB1 : ov_read_bytes rsegs m2 (Z_to_bv 64 (bp + (pos + 1))) 1 = Some (sub body (pos + 1) 1))
      by (apply ls_rd; [exact HBY | lia | lia]).
    assert (RB2 : ov_read_bytes rsegs m2 (Z_to_bv 64 (bp + (pos + 2))) 1 = Some (sub body (pos + 2) 1))
      by (apply ls_rd; [exact HBY | lia | lia]).
    step. step. step.
    rewrite ?wm_lbu.
    rewrite HTAG. unfold TAG.
    rewrite ls_eqb_lit by lia. replace (160 =? 160) with true by reflexivity. cbn [negb]. cbv iota.
    step. step. step. step.
    rewrite ?wm_lbu.
    rewrite ?(unsigned_lit (u_at body (pos + 2) 1)) by lia.
    rewrite ?(unsigned_lit (Z.shiftl (u_at body (pos + 2) 1) 7)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite ?(unsigned_lit (u_at body (pos + 1) 1)) by lia.
    rewrite <- Hsdef.
    step.
    rewrite (ls_ltu_s32 B 64984 s ltac:(lia) ltac:(unfold g_ncmd, OFF_g_ncmd in Hsnc; lia)).
    cbn [negb]. cbv iota.
    do 3 step.
    rewrite ?(unsigned_lit s) by lia.
    step.
    replace (s32_at Bc (19912 + s * 40)) with (Cmd_st Bc s)
      by (unfold Cmd_st, A_Cmd_st, OFF_g_cmd; f_equal; lia).
    rewrite HST. unfold PENDING.
    step. step.
    rewrite ls_eqb_lit by lia. replace (1 =? 1) with true by reflexivity. cbn [negb]. cbv iota.
    assert (RDL : ov_read_bytes rsegs m2 (Z_to_bv 64 (226648 + s * 40 + 36)) 1 = Some (sub Bc (A_Cmd_len s) 1)).
    { apply (wm_read rsegs W_BASE_PLAIN m2 Bc);
        [exact WM2 | unfold A_Cmd_len, OFF_g_cmd; lia | unfold A_Cmd_len, OFF_g_cmd; lia
        | f_equal; unfold A_Cmd_len, OFF_g_cmd; lia]. }
    step.
    rewrite ?wm_lbu.
    change (u_at Bc (A_Cmd_len s) 1) with tl.
    step.
    rewrite ls_ltu_lit by lia. replace (len - pos <? tl) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [negb]. cbv iota.
    step. step.
    set (bs := sub Bc (A_Cmd_bytes s) (Z.to_nat tl)) in *.
    assert (LBS : length bs = Z.to_nat tl)
      by (unfold bs; apply length_sub; [unfold A_Cmd_bytes, OFF_g_cmd; lia | unfold A_Cmd_bytes, OFF_g_cmd; lia]).
    step.
    eapply evt_cut.
    { eapply BC with (ls := bs) (rs := bs) (v := 0).
      - rewrite unsigned_lit by lia. rewrite <- HBYTES.
        apply ls_bsub; [exact HBY | lia | lia].
      - rewrite unsigned_lit by lia. unfold bs.
        apply (wm_src rsegs W_BASE_PLAIN m2 Bc (A_Cmd_bytes s) (Z.to_nat tl));
          [exact WM2 | unfold A_Cmd_bytes, OFF_g_cmd; lia | unfold A_Cmd_bytes, OFF_g_cmd; lia
          | unfold A_Cmd_bytes, OFF_g_cmd; lia].
      - rewrite unsigned_lit by lia. apply ls_memcmp_refl. exact LBS.
      - exact MI2. }
    wk_post_call rsegs m2.
    step.
    replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbn [negb]. cbv iota.
    step. step.
    lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN [CB _ (upd Bc (19912 + s * 40) (put 4 2))] |- _ =>
      replace (upd Bc (19912 + s * 40) (put 4 2)) with (set_Cmd_st Bc s SENT) in H
        by (unfold set_Cmd_st, A_Cmd_st, OFF_g_cmd, SENT; f_equal; lia) end.
    step.
    rewrite HS32NQ.
    rewrite ls_eqb_lit by lia.
    destruct (Z.eqb_spec nqv 0) as [N0|N0]; cbv iota.
    - destruct (ls_q_exit _ _ _ _ _ _ _ _ HQL ltac:(lia)) as [EB EK].
      rewrite EB, EK in HNEXT. rewrite N0.
      apply (TAIL _ (set_Cmd_st Bc s SENT) 0);
        [ exact HNEXT | lia | (unfold set_Cmd_st; rewrite u_at_upd_out by (rewrite ?length_put; unfold A_Cmd_st, OFF_g_cmd; lia); exact HNC) | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption ].
    - do 5 step.
      rewrite ls_shl32_shr30 by lia.
      rewrite ?(unsigned_lit (4 * nqv)) by lia.
      apply (INNER (S (Z.to_nat CMDS_MAX)) 0 0 (set_Cmd_st Bc s SENT));
        [ exact HQL | lia | lia | lia | (unfold set_Cmd_st; rewrite u_at_upd_out by (rewrite ?length_put; unfold A_Cmd_st, OFF_g_cmd; lia); exact HNC) | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption ]. }
  (* beqz a1: len = 0 ? *)
  step.
  rewrite ls_eqb0u by lia.
  destruct (Z.eqb_spec len 0) as [L0|L0]; cbv iota.
  - destruct (ls_exit _ _ _ _ _ _ _ _ HM ltac:(lia)) as [-> ->].
    apply EPI; assumption.
  - do 12 step.
    apply (OUTER (S (Z.to_nat len)) 0 0 B);
      [ exact HM | lia | reflexivity | reflexivity | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption ].
Qed.
