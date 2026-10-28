(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep Arr Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Str_cpy.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit I_pck D_kit I_ikit I_strncmpw I_memcpyw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation AMEMMOVE_DEPTH := 2224%Z (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mv_cur (off : nat) (bs : list byte) (i : nat) : list byte := firstn i (skipn off bs) ++ skipn i bs.

Lemma mv_cur_length : forall off bs i, (off + i <= length bs)%nat -> length (mv_cur off bs i) = length bs.
Proof. intros off bs i H. unfold mv_cur. rewrite length_app, firstn_length, !skipn_length. lia. Qed.

Lemma mv_cur_skipn : forall off bs i j, (off + i <= length bs)%nat -> (i <= j)%nat -> skipn j (mv_cur off bs i) = skipn j bs.
Proof.
  intros off bs i j H Hj. unfold mv_cur.
  assert (L : length (firstn i (skipn off bs)) = i) by (rewrite firstn_length, skipn_length; lia).
  rewrite skipn_app, L. rewrite (skipn_all2 (firstn i (skipn off bs))) by lia. cbn [app].
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma mv_cur_nth : forall off bs i j, (off + i <= length bs)%nat -> (i <= j)%nat -> nth_error (mv_cur off bs i) j = nth_error bs j.
Proof.
  intros off bs i j H Hj.
  rewrite <- (Nat.add_0_r j) at 1. rewrite <- nth_error_skipn, (mv_cur_skipn off bs i j H Hj), nth_error_skipn, Nat.add_0_r. reflexivity.
Qed.

Lemma mv_cur_upd : forall off bs i k, (off + i + k <= length bs)%nat ->
  upd_bytes (mv_cur off bs i) i (firstn k (skipn (off + i) bs)) = mv_cur off bs (i + k).
Proof.
  intros off bs i k H. unfold upd_bytes.
  assert (Lx : length (firstn k (skipn (off + i) bs)) = k) by (rewrite firstn_length, skipn_length; lia).
  rewrite Lx. rewrite (mv_cur_skipn off bs i (i + k)) by lia.
  unfold mv_cur.
  assert (L : length (firstn i (skipn off bs)) = i) by (rewrite firstn_length, skipn_length; lia).
  rewrite firstn_app, L, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. rewrite firstn_firstn, Nat.min_id.
  rewrite app_assoc. f_equal.
  rewrite firstn_add_split. f_equal. rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition imm_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (d off n : Z) (blk : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' a4' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' d [CB (length blk) (mv_cur (Z.to_nat off) blk (Z.to_nat n))].

Section IMM.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (blk : list byte) (d off n : Z).
  Notation N := (Z.of_nat (length blk)).
  Notation W := [(d, d + n)]%Z.
  Hypothesis AB : 0 <= off /\ off + n <= N /\ 0 <= d /\ d + N < 2^63 /\ 0 <= n.

  Notation POST := (imm_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d off n blk m).
  Notation ST pc mm x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation cur i := (mv_cur (Z.to_nat off) blk (Z.to_nat i)).

  Definition INV (mX : mem) (i : Z) : Prop :=
    u8arr asegs mX d (cur i) /\ mem_inv asegs mX /\ munch W m mX /\ wmono asegs m mX.

  Ltac open_inv H := destruct H as (DST & MI & MU & WM).

  Lemma cur_len : forall i, 0 <= i <= n -> length (cur i) = length blk.
  Proof. intros i Hi. apply mv_cur_length. lia. Qed.

  Lemma src_byte : forall i, 0 <= i < n -> exists b, nth_error (cur i) (Z.to_nat (off + i)) = Some b.
  Proof.
    intros i Hi. rewrite mv_cur_nth by lia.
    destruct (nth_error blk (Z.to_nat (off + i))) as [b|] eqn:E; [exists b; reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  Lemma cp_store_ok : forall mX i (k : nat) a,
    INV mX i -> 0 <= i -> i + Z.of_nat k <= n -> a = wa (d + i) -> store_ok asegs mX a k = true.
  Proof.
    intros mX i k a I Hi Hk Ha; open_inv I.
    eapply (u8arr_store_ok_n asegs mX d (cur i) i k a DST); [lia| rewrite cur_len by lia; lia | exact Ha].
  Qed.

  Lemma cp_store : forall mX i xs a,
    INV mX i -> 0 <= i -> i + Z.of_nat (length xs) <= n ->
    firstn (length xs) (skipn (Z.to_nat (off + i)) (cur i)) = xs -> a = wa (d + i) ->
    INV (write_to_mem mX a xs) (i + Z.of_nat (length xs)).
  Proof.
    intros mX i xs a I Hi Hk Hxs Ha. pose proof I as I'. open_inv I.
    pose proof (cp_store_ok mX i (length xs) a I' Hi Hk Ha) as SOK. subst a.
    split; [|split; [|split]].
    - replace (cur (i + Z.of_nat (length xs))) with (upd_bytes (cur i) (Z.to_nat i) xs).
      { apply (u8arr_write_bytes asegs mX d (cur i) i xs DST); [lia|]. rewrite cur_len by lia. lia. }
      rewrite <- Hxs at 1. rewrite (mv_cur_skipn (Z.to_nat off) blk (Z.to_nat i) (Z.to_nat (off + i))) by lia.
      replace (Z.to_nat (off + i)) with (Z.to_nat off + Z.to_nat i)%nat by lia.
      rewrite mv_cur_upd by lia. f_equal. lia.
    - apply mem_inv_store; assumption.
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma imm_ret : forall mX x11 x12 x13 x14, INV mX n -> evt asegs POST (ST 0x1d4e88 mX x11 x12 x13 x14).
  Proof.
    intros mX x11 x12 x13 x14 I; open_inv I.
    zstep. apply evt_done. exists x11, x12, x13, x14, mX.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply rw_cells_of_u8arr in DST. rewrite cur_len in DST by lia. exact DST.
  Qed.

  (* [comment removed for export] *)
  Lemma imm_bytes : forall (K : nat) mX i x14,
    INV mX i -> Z.to_nat (n - i) = K -> 0 <= i < n ->
    evt asegs POST (ST 0x1d4e44 mX (Z_to_bv 64 (d + off + i)) (Z_to_bv 64 (d + n)) (Z_to_bv 64 (d + i)) x14).
  Proof.
    induction K as [|K IH]; intros mX i x14 I HK Hi; [lia|].
    destruct (src_byte i Hi) as [b Hn].
    pose proof (u8arr_read asegs mX d _ (off + i) b (Z_to_bv 64 (d + off + i)) (proj1 I) Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    pose proof (cp_store_ok mX i 1 (Z_to_bv 64 (d + i)) I ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. clear SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bytes) _) =>
      replace bytes with [b] by first [reflexivity | symmetry; apply le1_zxb] end.
    pose proof (cp_store mX i [b] (Z_to_bv 64 (d + i)) I ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(apply nth_error_first1; exact Hn) ltac:(unfold wa; f_equal; lia)) as I2.
    cbn [length] in I2. change (Z.of_nat 1) with 1 in I2.
    remember (write_to_mem mX (Z_to_bv 64 (d + i)) [b]) as m2 eqn:Em. clear Em. clear I.
    do 2 zstep. zstep. if_cases Kc; zify_cond Kc.
    - replace (d + i + 1) with (d + (i + 1)) by lia. replace (d + off + i + 1) with (d + off + (i + 1)) by lia.
      eapply (IH _ (i + 1)); [exact I2| lia| lia].
    - zstep. eapply imm_ret. replace n with (i + 1) by lia. exact I2.
  Qed.

  Theorem imm_spec : forall x13 x14,
    rw_cells asegs m d [CB (length blk) blk] -> mem_inv asegs m ->
    evt asegs POST (ST 0x1d4e34 m (Z_to_bv 64 (d + off)) (Z_to_bv 64 n) x13 x14).
  Proof.
    intros x13 x14 BLK MI0.
    assert (I0 : INV m 0).
    { split; [| split; [exact MI0| split; [apply munch_refl| apply wmono_refl]]].
      change (cur 0) with (firstn 0 (skipn (Z.to_nat off) blk) ++ skipn 0 blk). cbn [firstn skipn app].
      apply (u8arr_of_rw_cells asegs m d (length blk) blk BLK). }
    assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (Z_to_bv 64 (d + off)) = d + off) by (apply unsigned_lit; lia).
    assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
    assert (FIN : forall mX, INV mX 0 -> (off = 0 \/ n = 0) -> INV mX n).
    { intros mX I [E|E]; [| rewrite E; exact I]. destruct I as (DST & REST). split; [| exact REST].
      rewrite E in *. unfold mv_cur in *. cbn [Z.to_nat skipn firstn app] in *. rewrite firstn_skipn. exact DST. }
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      eapply imm_ret. apply FIN; [exact I0| left; lia].
    - zstep. if_cases K3; zify_cond K3.
      + eapply imm_ret. apply FIN; [exact I0| right].
        apply andb_false_iff in K3. destruct K3 as [K3|K3]; apply Z.ltb_ge in K3; lia.
      + do 2 zstep.
        eapply evt_eq; [| eapply (imm_bytes (Z.to_nat (n - 0)) m 0); [exact I0| reflexivity| lia]].
        rewrite !Z.add_0_r. reflexivity.
  Qed.
End IMM.

(* [comment removed for export] *)
Lemma amm_loop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a5' a6' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 e) (Z_to_bv 64 e) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1c2254) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 c) (Z_to_bv 64 e) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c2244) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Lemma amm_loop2 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a5' a6' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 e) (Z_to_bv 64 e) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1c22f8) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 c) (Z_to_bv 64 e) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c22e8) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma amm_rip1 : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - AMEMMOVE_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= s -> 0 < n -> s + n < 2^63 ->
  acc asegs m s n -> rng_ok s n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                    s2' s3 s4 s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1c2090) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c225c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 6 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 4 lstep. lstep. if_true.
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma amm_chk1 : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - AMEMMOVE_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= s -> 0 <= n -> s + n < 2^63 ->
  chk_ok m s n -> m2s_cells m -> icells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                    s2' (Z_to_bv 64 (n + -65)) s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1c2090) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c2038) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN (AC & QW & RO) M2S (G2 & G1 & RM & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 s) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - s)) = 18446744073709551615 - s) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. if_false.
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    eapply evt_mono; [apply (amm_rip1 sp d s n) with (lo := lo); try assumption; unfold kHighShadowEnd; lia|].
    intros ms' (m' & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & -> & REST).
    do 19 eexists. split; [reflexivity| exact REST].
  - (* [comment removed for export] *)
    subst n. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + s ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((s / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (s + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((s + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (s + n + -1) with (s + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (s + n + -1) / 8) with ((s + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m s n AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
      destruct (SB ((s + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- eapply evt_mono; [apply (amm_rip1 sp d s n) with (lo := lo); try assumption; unfold kHighShadowEnd; lia|].
           intros ms' (m' & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & -> & REST).
           do 19 eexists. split; [reflexivity| exact REST].
      * zify_cond K2.
        eapply evt_cut.
        { eapply (amm_loop1 (Z.to_nat ((s + n + -1) / 8 + 2147450880 - (s / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a5' & a6' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- eapply evt_mono; [apply (amm_rip1 sp d s n) with (lo := lo); try assumption; unfold kHighShadowEnd; lia|].
           intros ms' (m' & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & -> & REST).
           do 19 eexists. split; [reflexivity| exact REST].
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* [comment removed for export] *)
Lemma amm_rip2 : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - AMEMMOVE_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 < n -> d + n < 2^63 ->
  acc asegs m d n -> rng_ok d n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s5' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                    s2' s3' s4 s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1c20dc) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c2300) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 5 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 4 lstep. lstep. if_true.
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma amm_chk2 : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - AMEMMOVE_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= d -> 0 <= n -> d + n < 2^63 ->
  chk_ok m d n -> m2s_cells m -> icells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s5' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                    s2' s3' s4 s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1c20dc) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (n + -65)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c2090) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN (AC & QW & RO) M2S (G2 & G1 & RM & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 d) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - d)) = 18446744073709551615 - d) by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (amm_rip2 sp d s n); try assumption; unfold kHighShadowEnd; lia.
  - subst n. if_true. lstep. if_false. lstep.
    apply evt_done. do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + d ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((d / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (d + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((d + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (d + n + -1) with (d + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (d + n + -1) / 8) with ((d + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m d n AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
      destruct (SB ((d + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (amm_rip2 sp d s n); try assumption; unfold kHighShadowEnd; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (amm_loop2 (Z.to_nat ((d + n + -1) / 8 + 2147450880 - (d / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a5' & a6' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (amm_rip2 sp d s n); try assumption; unfold kHighShadowEnd; lia.
    + apply evt_done. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* [comment removed for export] *)
Lemma imm_call : forall (d off n : Z) (blk : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  0 <= off /\ off + n <= Z.of_nat (length blk) /\ 0 <= d /\ d + Z.of_nat (length blk) < 2^63 /\ 0 <= n ->
  rw_cells asegs m d [CB (length blk) blk] -> mem_inv asegs m ->
  evt asegs (imm_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d off n blk m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (d + off)) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d4e34) fc None m (seg_rom asegs)).
Proof. intros. apply imm_spec; assumption. Qed.

Definition amemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d off n : Z) (blk : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + n); (bv_unsigned sp - AMEMMOVE_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' d [CB (length blk) (mv_cur (Z.to_nat off) blk (Z.to_nat n))].

(* [comment removed for export] *)
Theorem amemmove_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d off n : Z) (blk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (d + off) -> a2 = Z_to_bv 64 n ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - AMEMMOVE_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 <= d -> 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length blk) -> d + Z.of_nat (length blk) <= 2^47 ->
  rw_cells asegs m d [CB (length blk) blk] ->
  (d + Z.of_nat (length blk) <= lo \/ bv_unsigned sp <= d) ->
  chk_ok m (d + off) n -> chk_ok m d n -> m2s_cells m -> icells m -> mem_inv asegs m ->
  evt asegs (amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d off n blk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c1ffc) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> -> ST LO LOLO SPH D0 O0 N0 ON DH BLK SEPD CS CD M2S IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(d, d + n); (usp - 2224, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(usp - 2224, usp)] m) as MUf.
  pose proof IC as (G2 & G1 & RM & SHC & RI).
  assert (BLK0 : keep (rw_cells asegs m d [CB (length blk) blk])) by exact BLK. clear BLK.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  assert (OFF : forall mm, munch [(usp - 2224, usp)] m mm -> wmono asegs m mm ->
            rw_cells asegs mm d [CB (length blk) blk] /\ chk_ok mm (d + off) n /\ chk_ok mm d n /\ m2s_cells mm).
  { intros mm MU' WM'.
    assert (AGs : forall P : Z -> Prop, (forall x, P x -> x < usp - 2224 \/ usp <= x) -> agree_on P m mm).
    { intros P HP. apply (agree_of_munch _ _ _ _ MU'). intros y Hy. cbn [outside]. split; [specialize (HP y Hy); lia| exact I]. }
    split; [unfold keep in BLK0; apply (rw_cells_agree asegs m mm _ _ BLK0); [| exact WM']; apply AGs; intros x Hx;
            cbn [cells_size csize] in Hx; lia|].
    split; [apply (chk_ok_agree m mm (d + off) _ CS ltac:(lia) ltac:(lia)); apply AGs; intros x Hx; lia|].
    split; [apply (chk_ok_agree m mm d _ CD D0 ltac:(lia)); apply AGs; intros x Hx; lia|].
    apply (m2s_cells_agree m mm M2S); [apply AGs; intros x Hx; lia| exact WM']. }
  clear CS CD M2S.
  carve_frame 64%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  do 11 lstep. do 3 lstep. lstep. if_false.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MUf WM) as (_ & CS1 & _ & M2S1);
    assert (IC1 : icells mm) by (split; [exact G2| split; [exact G1| split; [exact RM| split; [exact SHC| exact RI]]]]) end.
  call (amm_chk1 usp d (d + off) n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS1| exact M2S1| exact IC1| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST2 end.
  clear CS1 M2S1 IC1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MUf WM) as (_ & _ & CD2 & M2S2);
    assert (IC2 : icells mm) by (split; [exact G2| split; [exact G1| split; [exact RM| split; [exact SHC| exact RI]]]]) end.
  call (amm_chk2 usp d (d + off) n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CD2| exact M2S2| exact IC2| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST3 end.
  clear CD2 M2S2 IC2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MUf WM) as (BLK & _ & _ & _) end.
  clear OFF BLK0 MUf.
  lstep.
  call (imm_call d off n blk); [lia| exact BLK| assumption|].
  do 10 lstep.
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST4 end.
  release_frame FR ST4 (usp + -64). release_frame FRs ST4 usp.
  lstep.
  unfold amemmove_post. sys_finish.
  - rewrite (unsigned_lit usp) by lia. exact MU.
  - rewrite (unsigned_lit usp) by lia. exact ST4.
Qed.

End WithRIP.
