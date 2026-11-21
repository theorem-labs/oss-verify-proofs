(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1 Z_tr_cb3 Z_tr_bt1 Z_tr_bt2 Z_tr_bt10 Z_tr_bt12 Z_tr_bt13 Z_tr_bt14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma gc2_model : forall s t FC DL HP HL HM DP BC OL SL MC f nc mc n R,
  R = gen_codes_loop2 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n -> n <= mc ->
  R = (if arr_get DL n =? 0 then gen_codes_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc (n + 1)
       else gen_codes_loop2 f (bt_upd s t (arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL HP HL HM DP BC OL SL MC) t
              (arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) mc (n + 1)).
Proof.
  intros until R. intros ER Hn.
  rewrite <- (bt_set_tree_fc s t FC DL HP HL HM DP BC OL SL MC FC) in ER. rewrite loop2_S in ER.
  rewrite (proj2 (Z.leb_le n mc) Hn) in ER. cbv zeta in ER. rewrite !bt_Len in ER. rewrite !bt_set_tree_fc in ER. exact ER.
Qed.

Lemma gc2_out : forall f X t nc mc n, mc < n -> gen_codes_loop2 f X t nc mc n = X.
Proof. intros. apply loop2_out. assumption. Qed.

Definition res_ok (r l : Z) : Prop := 0 <= r < 2 ^ (16 - l).
Lemma res_ok_0 : forall l, 1 <= l <= 15 -> res_ok 0 l.
Proof. intros l H. unfold res_ok. split; [lia|]. apply Z.pow_pos_nonneg; lia. Qed.
Lemma res_ok_lor : forall c r l, 1 <= l <= 15 -> res_ok r l -> 0 <= Z.lor (c mod 2 ^ 1) r < 2 ^ 31.
Proof.
  intros c r l Hl H. unfold res_ok in H.
  assert (B : 1 < 2 ^ (16 - l)) by (apply (Z.pow_gt_1 2); lia).
  pose proof (lor_bit_bound r c (16 - l) ltac:(lia) H B) as X.
  assert (2 ^ (16 - l) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma res_ok_step : forall c r l, 2 <= l <= 15 -> res_ok r l -> res_ok (Z.lor (c mod 2 ^ 1) r * 2 ^ 1) (l - 1).
Proof.
  intros c r l Hl H. unfold res_ok in *.
  assert (B : 1 < 2 ^ (16 - l)) by (apply (Z.pow_gt_1 2); lia).
  pose proof (lor_bit_bound r c (16 - l) ltac:(lia) H B) as X.
  replace (16 - (l - 1)) with (16 - l + 1) by lia. rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma res_ok_bound : forall r l, 1 <= l <= 15 -> res_ok r l -> 0 <= r < 65536.
Proof. intros r l Hl H. unfold res_ok in H. assert (2 ^ (16 - l) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia). lia. Qed.
Lemma srliw1 : forall c, 0 <= c < 65536 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 c) 1) = c / 2 ^ 1.
Proof.
  intros c Hc. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. apply bv_swrap32_id. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia.
Qed.

Definition gcR (T n mc1 : Z) (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n) (wz (bv_unsigned sp + 8)) (wz mc1) (wz 1) a4 a5 a6 a7
      (wz T) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition gc_brl_post (T n mc1 v : Z) (a4 : word)
    (ra sp gp tp t1 t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a5 a6 a7 m',
    ms' = MS (gcR T n mc1 ra sp gp tp (wz v) t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c288) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma gc_brl : forall (d : nat) (T n mc1 c r l : Z) (a4 t0 : word)
    (ra sp gp tp t1 t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv psegs m -> Z.of_nat d = l - 1 -> 1 <= l <= 15 -> 0 <= c < 65536 -> res_ok r l ->
  evt psegs (gc_brl_post T n mc1 (brl c r l) a4 ra sp gp tp t1 t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (gcR T n mc1 ra sp gp tp t0 t1 t2 s0 s1 a4 (wz c) (wz r) (wz (l + 1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c270) fc None m (seg_rom psegs)).
Proof.
  induction d as [|d IH]; intros until m; intros MI Ed Rl Rc RO.
  - assert (l = 1) by lia. subst l.
    pose proof (res_ok_lor c r 1 ltac:(lia) RO) as RB. pose proof (res_ok_bound r 1 ltac:(lia) RO) as Rr.
    unfold gcR. zs2. zs2. rewrite srliw1 by lia. zs2. zs2. zs2. zstep. br_cases K; [exfalso; lia|].
    rewrite land1_mod, Z.lor_comm. rewrite <- (brl_last c r) by lia.
    apply evt_done. unfold gc_brl_post, gcR. do 4 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
  - pose proof (res_ok_lor c r l ltac:(lia) RO) as RB. pose proof (res_ok_bound r l ltac:(lia) RO) as Rr. pose proof (res_ok_step c r l ltac:(lia) RO) as RO'.
    pose proof (brl_step c r l ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ES. change (2 ^ 1) with 2 in ES, RO'.
    unfold gcR. zs2. zs2. rewrite srliw1 by lia. zs2. zs2. zs2. shl_norm. zstep. br_cases K; [|exfalso; lia].
    rewrite land1_mod. change (2 ^ 1) with 2. rewrite (Z.lor_comm r). reg_as l (l - 1 + 1). rewrite ES.
    eapply evt_mono; [eapply (IH T n mc1 (c / 2) (Z.lor (c mod 2) r * 2) (l - 1)); [exact MI| lia| lia| Z.div_mod_to_equations; lia| exact RO']|].
    intros ms' H. exact H.
Qed.

Definition ncl (w0 : word) (nc : arr) : list word := upd (av16 nc 16) 0 w0.
Lemma ncl_length : forall w0 nc, length (ncl w0 nc) = 16%nat.
Proof. intros. unfold ncl. rewrite upd_length, av16_length. reflexivity. Qed.
Lemma ncl_zlength : forall w0 nc, Z.of_nat (length (u16s (ncl w0 nc))) = 32.
Proof. intros. rewrite u16s_length, ncl_length. reflexivity. Qed.
Lemma ncl_nth : forall w0 nc i, 1 <= i < 16 -> nth_error (ncl w0 nc) (Z.to_nat i) = Some (wz (arr_get nc i)).
Proof. intros w0 nc i Hi. unfold ncl. rewrite nth_error_upd_other by lia. apply av16_nth. lia. Qed.
Lemma upd_comm : forall {X} (l : list X) i j (x y : X), i <> j -> upd (upd l i x) j y = upd (upd l j y) i x.
Proof. intros X l. induction l as [|h l IH]; intros [|i] [|j] x y H; cbn [upd]; try reflexivity; [lia|]. f_equal. apply IH. lia. Qed.
Lemma ncl_write : forall m A w0 nc i (w : word) v,
  u8arr psegs m A (u16s (ncl w0 nc)) -> 1 <= i < 16 -> arr_len nc = 16 -> le2 w = le2 (wz v) ->
  u8arr psegs (write_to_mem m (wa (A + 2 * i)) (le2 w)) A (u16s (ncl w0 (arr_set nc i v))).
Proof.
  intros m A w0 nc i w v ARR Hi Hn E.
  assert (EQ : u16s (ncl w0 (arr_set nc i v)) = u16s (upd (ncl w0 nc) (Z.to_nat i) w)).
  { unfold ncl. rewrite <- av16_upd by lia. rewrite (upd_comm (av16 nc 16) (Z.to_nat i) 0%nat) by lia. apply u16s_upd_le2. symmetry. exact E. }
  rewrite EQ. apply (u16arr_write psegs); [exact ARR|]. rewrite ncl_length. lia.
Qed.

Ltac nc_store ARR w0 nc A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (ncl w0 nc) idx (wa (A + 2 * idx)) ARR ltac:(rewrite ncl_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (ncl_write m0 A w0 nc idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "LNC" in pose proof (ncl_zlength w0 (arr_set nc idx v)) as LN;
      let LA := fresh "LNB" in pose proof (arr_len_set nc idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Notation Wgc T N sp := [(T%Z, (T + 4 * N)%Z); (bv_unsigned sp + 8, bv_unsigned sp + 40)] (only parsing).

Definition gc_iter_post (T N n mc : Z) (w0 : word) (FC' DL nc' : arr)
    (ra sp gp tp t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a4 a5 a6 a7 pcx m',
    ms' = MS (gcR T (n + 1) (mc + 1) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wgc T N sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL N)) /\ u8arr psegs m' (bv_unsigned sp + 8) (u16s (ncl w0 nc'))
    /\ ((pcx = 0x1c244 /\ n + 1 <= mc) \/ (pcx = 0x1c290 /\ n = mc)).

Ltac gc_latch MU WM ARR NCA :=
  let K3 := fresh "K3" in
  zs2; zstep; br_cases K3;
  [ apply evt_done; unfold gc_iter_post, gcR; do 8 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
    split; [exact ARR|]; split; [exact NCA|]; right; split; [reflexivity| lia]
  | apply evt_done; unfold gc_iter_post, gcR; do 8 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
    split; [exact ARR|]; split; [exact NCA|]; left; split; [reflexivity| lia] ].

Lemma gc_iter : forall (T N n mc : Z) (w0 : word) (FC DL nc : arr)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u8arr psegs m (bv_unsigned sp + 8) (u16s (ncl w0 nc)) -> mem_inv psegs m ->
  0 < T -> T + 4 * N <= bv_unsigned sp -> bv_unsigned sp + 40 < 2^63 ->
  0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len nc = 16 ->
  0 <= n <= mc -> mc < N -> 0 <= arr_get DL n <= 15 -> (forall k, 1 <= k <= 15 -> 0 <= arr_get nc k < 65536) ->
  evt psegs (gc_iter_post T N n mc w0
               (if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL
               (if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1)))
               ra sp gp tp t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (gcR T n (mc + 1) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c244) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR NCA MI RT0 SEP RSP RN LFC LDL LNC Rn Rmc Rl RNC.
  pose proof (munch_refl (Wgc T N sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (ncl_zlength w0 nc) as LNCZ.
  pose proof (u16arr_read psegs m T (avct FC DL N) (2 * n + 1) _ (wa (T + n * 4 + 2)) ARR (avct_nth_dl FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
  unfold gcR. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K.
  -
    rewrite (proj2 (Z.eqb_eq _ 0) K).
    gc_latch MU WM ARR NCA.
  - rewrite (proj2 (Z.eqb_neq _ 0) K).
    set (len := arr_get DL n) in *.
    pose proof (RNC len ltac:(lia)) as Rc.
    pose proof (u16arr_read psegs m _ (ncl w0 nc) len _ (wa (bv_unsigned sp + 8 + len * 2)) NCA (ncl_nth w0 nc len ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDc.
    zs2. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zs2.
    nc_store NCA w0 nc (bv_unsigned sp + 8) len (wrap16 (arr_get nc len + 1)) ltac:(apply le2_wrap16; reflexivity).
    zs2.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (gc_brl (Z.to_nat (len - 1)) T n (mc + 1) (arr_get nc len) 0 len) end.
    1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ exact Rc. } 1:{ apply res_ok_0. lia. }
    rewrite <- bi_reverse_brl by lia.
    unfold gcR.
    ct_store_fc ARR FC DL N T n (wrap16 (bi_reverse (arr_get nc len) len)) ltac:(apply le2_wrap16; reflexivity).
    zs2.
    gc_latch MU WM ARR NCA.
Qed.

Lemma gc2_model' : forall s t FC DL HP HL HM DP BC OL SL MC f nc mc n R,
  R = gen_codes_loop2 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n -> n <= mc ->
  R = gen_codes_loop2 f (bt_upd s t (if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL HP HL HM DP BC OL SL MC) t
        (if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) mc (n + 1).
Proof. intros until R. intros ER Hn. pose proof (gc2_model _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ER Hn) as E. destruct (arr_get DL n =? 0); exact E. Qed.

Definition gc_loop_post (s : deflate_state) (t : tree_id) (T N mc : Z) (w0 : word) (DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a4 a5 a6 a7 FC' nc' m',
    ms' = MS (gcR T (mc + 1) (mc + 1) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c290) fc None m' (seg_rom psegs)
    /\ munch (Wgc T N sp) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL N)) /\ u8arr psegs m' (bv_unsigned sp + 8) (u16s (ncl w0 nc'))
    /\ R = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = N.

Lemma gc_loop : forall (f : nat) (s : deflate_state) (t : tree_id) (T N n mc : Z) (w0 : word) (FC DL nc HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u8arr psegs m (bv_unsigned sp + 8) (u16s (ncl w0 nc)) -> mem_inv psegs m ->
  munch (Wgc T N sp) m0 m -> wmono psegs m0 m ->
  0 < T -> T + 4 * N <= bv_unsigned sp -> bv_unsigned sp + 40 < 2^63 ->
  0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len nc = 16 ->
  Z.of_nat f = mc + 1 - n -> 0 <= n <= mc -> mc < N -> (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) -> (forall k, 1 <= k <= 15 -> 0 <= arr_get nc k < 65536) ->
  R = gen_codes_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n ->
  evt psegs (gc_loop_post s t T N mc w0 DL HP HL HM DP BC OL SL MC R ra sp gp tp t2 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (gcR T n (mc + 1) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c244) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR NCA MI MU WM RT0 SEP RSP RN LFC LDL LNC Ef Rn Rmc RDL RNC ER.
  { exfalso. lia. }
  pose proof (gc2_model' s t FC DL HP HL HM DP BC OL SL MC f nc mc n R ER ltac:(lia)) as ER'. clear ER.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (ncl_zlength w0 nc) as LNCZ.
  set (FC' := if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) in *.
  set (nc' := if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) in *.
  assert (LFC' : arr_len FC' = N) by (subst FC'; destruct (arr_get DL n =? 0); [exact LFC| rewrite arr_len_set; exact LFC]).
  assert (LNC' : arr_len nc' = 16) by (subst nc'; destruct (arr_get DL n =? 0); [exact LNC| rewrite arr_len_set; exact LNC]).
  assert (RNC' : forall k, 1 <= k <= 15 -> 0 <= arr_get nc' k < 65536).
  { intros k Hk. subst nc'. destruct (arr_get DL n =? 0); [apply RNC; exact Hk|].
    destruct (Z.eq_dec (arr_get DL n) k) as [<-|NE]; [rewrite arr_get_set_same by (pose proof (RDL n ltac:(lia)); lia); apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RNC; exact Hk]. }
  pose proof (avct_zlength FC' DL N ltac:(lia)) as LCT'. pose proof (ncl_zlength w0 nc') as LNCZ'.
  call (gc_iter T N n mc w0 FC DL nc).
  1:{ exact ARR. } 1:{ exact NCA. } 1:{ exact MI. } 1:{ exact RT0. } 1:{ exact SEP. } 1:{ exact RSP. } 1:{ exact RN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LNC. }
  1:{ exact Rn. } 1:{ exact Rmc. } 1:{ apply RDL. lia. } 1:{ exact RNC. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - eapply (IH s t T N (n + 1) mc w0 FC' DL nc' HP HL HM DP BC OL SL MC R m0);
      [eassumption| eassumption| eassumption| exact MU| exact WM| exact RT0| exact SEP| exact RSP| exact RN| exact LFC'| exact LDL| exact LNC'| lia| lia| exact Rmc| exact RDL| exact RNC'| exact ER'].
  - rewrite gc2_out in ER' by lia. subst n.
    apply evt_done. unfold gc_loop_post. do 6 eexists. exists FC', nc'. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER'| exact LFC'].
Qed.
