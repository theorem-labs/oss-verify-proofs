(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import ScanInt ScanCount RespLine.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_scanner_get_token H_vfmatch_A H_vfmatch_F H_vfmatch_G1 H_match H_membuffer_assign
     Stdio_base F_shgetc_A F_shgetc_B F_strtol F_vfscanf_lib F_sscanf.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_presp_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Ltac sstep := step; fix_lit_store.

Lemma first_nulB : forall (l : list byte) z, In z l -> exists s r, l = s ++ z :: r /\ ~ In z s.
Proof.
  induction l as [|a l IH]; intros z H; [destruct H|].
  destruct (base.decide (a = z)) as [->|NE].
  - exists [], l. split; [reflexivity| intros []].
  - destruct H as [->|H]; [congruence|]. destruct (IH z H) as (s & r & -> & NI).
    exists (a :: s), r. split; [reflexivity|]. intros [E|X]; [exact (NE E)| exact (NI X)].
Qed.

Lemma nth_error_skipnZ : forall {X} (k t : nat) (l : list X), nth_error (skipn k l) t = nth_error l (k + t).
Proof. intros X k. induction k as [|k IH]; intros t l; cbn; [reflexivity|]. destruct l; cbn; [now destruct t| apply IH]. Qed.

Definition set_byte (bs : list byte) (k : nat) (b : byte) : list byte := firstn k bs ++ [b] ++ skipn (k + 1) bs.
Lemma set_byte_length : forall bs k b, (k < length bs)%nat -> length (set_byte bs k b) = length bs.
Proof. intros bs k b H. unfold set_byte. rewrite !length_app, firstn_length_le, length_skipn by lia. cbn. lia. Qed.
Lemma set_byte_same : forall bs k b, (k < length bs)%nat -> nth_error (set_byte bs k b) k = Some b.
Proof.
  intros bs k b H. unfold set_byte. rewrite nth_error_app2 by (rewrite firstn_length_le; lia). rewrite firstn_length_le, Nat.sub_diag by lia. reflexivity.
Qed.
Lemma set_byte_other : forall bs k b i, (k < length bs)%nat -> i <> k -> nth_error (set_byte bs k b) i = nth_error bs i.
Proof.
  intros bs k b i H NE. unfold set_byte. destruct (Nat.lt_ge_cases i k).
  - rewrite nth_error_app1 by (rewrite firstn_length_le; lia). rewrite nth_error_firstn. destruct (Nat.ltb_spec i k); [reflexivity| lia].
  - rewrite nth_error_app2 by (rewrite firstn_length_le; lia). rewrite firstn_length_le by lia.
    change ([b] ++ skipn (k + 1) bs) with (b :: skipn (k + 1) bs). destruct (i - k)%nat as [|d] eqn:E; [lia|]. cbn [nth_error].
    rewrite nth_error_skipnZ. f_equal. lia.
Qed.
Lemma set_byte_restore : forall bs k b b0, nth_error bs k = Some b0 -> set_byte (set_byte bs k b) k b0 = bs.
Proof.
  intros bs k b b0 H. pose proof (nth_error_Some_lt _ _ _ H) as LT.
  assert (LT1 : (k < length (set_byte bs k b))%nat) by (rewrite set_byte_length; lia).
  apply nth_error_ext. intros i. destruct (Nat.eq_dec i k) as [->|NE].
  - rewrite set_byte_same by lia. symmetry. exact H.
  - rewrite set_byte_other by lia. apply set_byte_other; lia.
Qed.

Definition s32v (v : word) : Z := let u := (bv_unsigned v mod 2^32)%Z in if (u <? 2^31)%Z then u else (u - 2^32)%Z.
Lemma s32v_range : forall v, (- 2^31 <= s32v v < 2^31)%Z.
Proof. intros v. unfold s32v. pose proof (Z.mod_pos_bound (bv_unsigned v) (2^32) ltac:(lia)). destruct (Z.ltb_spec0 (bv_unsigned v mod 2^32) (2^31)); lia. Qed.
Lemma mod64_mod32 : forall x, ((x mod 2^64) mod 2^32 = x mod 2^32)%Z.
Proof.
  intros x. change (2^64)%Z with (2^32 * 2^32)%Z. rewrite Z.rem_mul_r by lia.
  set (a := (x mod 2^32)%Z). set (c := ((x / 2^32) mod 2^32)%Z).
  replace (a + 2^32 * c)%Z with (a + c * 2^32)%Z by lia. rewrite Z.mod_add by lia. subst a. apply Z.mod_mod. lia.
Qed.
Lemma le4_s32v : forall v, le4 v = le4 (Z_to_bv 64 (s32v v)).
Proof.
  intros v. unfold le4. rewrite Z_to_bv_unsigned. change (bv_wrap 64 (s32v v)) with ((s32v v) mod 2^64)%Z.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 (s32v v mod 2^64) 32) by (cbn; lia).
  f_equal. rewrite mod64_mod32. unfold s32v. pose proof (Z.mod_pos_bound (bv_unsigned v) (2^32) ltac:(lia)) as B.
  set (u := (bv_unsigned v mod 2^32)%Z) in *.
  destruct (Z.ltb_spec0 u (2^31)).
  - symmetry. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add (u - 2^32) 1 (2^32)) by lia. replace (u - 2^32 + 1 * 2^32)%Z with u by lia. symmetry. apply Z.mod_small. lia.
Qed.
Lemma rw_cells_C4_s32v : forall m X v, rw_cells rsegs m X [C4 v] -> rw_cells rsegs m X [C4 (Z_to_bv 64 (s32v v))].
Proof.
  intros m X v [[W B] R]. split; [split; [exact W|]| exact R]. cbn [cells_bytes cbytes] in *. rewrite <- le4_s32v. exact B.
Qed.

Notation zb := (Z_to_bv 8 0).
Lemma map_nth_error : forall {X Y} (f : X -> Y) (l : list X) i, nth_error (map f l) i = option_map f (nth_error l i).
Proof. intros X Y f l. induction l as [|a l IH]; intros [|i]; cbn; try reflexivity. apply IH. Qed.

Lemma runs_bridge : forall (bs : list byte) (o l : Z) (s r : list byte) (bcr : byte) (j1 e1 j2 e2 j3 e3 : nat),
  (0 <= o)%Z -> (0 <= l)%Z -> (Z.to_nat (o + l) < length bs)%nat ->
  skipn (Z.to_nat o) (set_byte bs (Z.to_nat (o + l)) zb) = s ++ zb :: r -> ~ In zb s ->
  nth_error bs (Z.to_nat (o + l)) = Some bcr -> (bv_unsigned bcr = 13 \/ bv_unsigned bcr = 10)%Z ->
  resp_runs (map bv_unsigned s) j1 e1 j2 e2 j3 e3 ->
  runs3 bs o (o + Z.of_nat j1) (o + Z.of_nat e1) (o + Z.of_nat j2) (o + Z.of_nat e2) (o + Z.of_nat j3) (o + Z.of_nat e3)
  /\ (Z.of_nat e3 <= l)%Z.
Proof.
  intros bs o l s r bcr j1 e1 j2 e2 j3 e3 O0 L0 KLT SPLIT NIN Hbcr CRLF RR.
  set (k := Z.to_nat (o + l)) in *. set (bs1 := set_byte bs k zb) in *.
  assert (LB1 : length bs1 = length bs) by (subst bs1; apply set_byte_length; lia).

  assert (SB1 : forall t, (t < length s)%nat -> nth_error bs1 (Z.to_nat o + t) = nth_error s t).
  { intros t Ht. rewrite <- nth_error_skipnZ, SPLIT. rewrite nth_error_app1 by lia. reflexivity. }
  assert (SZ : nth_error bs1 (Z.to_nat o + length s) = Some zb).
  { rewrite <- nth_error_skipnZ, SPLIT. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }

  assert (K1 : nth_error bs1 k = Some zb) by (subst bs1; apply set_byte_same; lia).
  assert (SL : (Z.of_nat (length s) <= l)%Z).
  { destruct (Z.lt_ge_cases l (Z.of_nat (length s))) as [LT|GE]; [exfalso| exact GE].
    apply NIN. pose proof (SB1 (Z.to_nat l) ltac:(lia)) as E. replace (Z.to_nat o + Z.to_nat l)%nat with k in E by lia. rewrite K1 in E.
    symmetry in E. exact (nth_error_In _ _ E). }
  assert (SB : forall t, (t < length s)%nat -> nth_error bs (Z.to_nat (o + Z.of_nat t)) = nth_error s t).
  { intros t Ht. rewrite <- (SB1 t Ht). replace (Z.to_nat (o + Z.of_nat t)) with (Z.to_nat o + t)%nat by lia.
    subst bs1. symmetry. apply set_byte_other; lia. }
  assert (DG : forall t, zdig (map bv_unsigned s) t -> bdig bs (o + Z.of_nat t)).
  { intros t (c & Hc & D). rewrite map_nth_error in Hc. destruct (nth_error s t) as [bb|] eqn:E; cbn in Hc; [| discriminate]. injection Hc as <-.
    exists bb. rewrite (SB t (nth_error_Some_lt _ _ _ E)). split; [exact E|]. unfold is_digit in D. apply andb_true_iff in D. destruct D as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2. lia. }
  assert (ND : forall t, zndig (map bv_unsigned s) t -> bndig bs (o + Z.of_nat t)).
  { intros t (c & Hc & D). rewrite map_nth_error in Hc. destruct (nth_error s t) as [bb|] eqn:E; cbn in Hc; [| discriminate]. injection Hc as <-.
    exists bb. rewrite (SB t (nth_error_Some_lt _ _ _ E)). split; [exact E|]. unfold is_digit in D. apply Bool.andb_false_iff in D. destruct D as [D|D]; apply Z.leb_gt in D; lia. }

  assert (NDE : bndig bs (o + Z.of_nat (length s))).
  { destruct (Z.lt_ge_cases (Z.of_nat (length s)) l) as [LT|GE].
    - exists zb. split; [| left; apply Z.ltb_lt; vm_compute; reflexivity]. rewrite <- SZ. replace (Z.to_nat (o + Z.of_nat (length s))) with (Z.to_nat o + length s)%nat by lia.
      subst bs1. symmetry. apply set_byte_other; lia.
    - assert (E : Z.of_nat (length s) = l) by lia. rewrite E. exists bcr. split; [exact Hbcr| lia]. }
  destruct RR as (O1 & O2 & O3 & O4 & O5 & O6 & N1 & D1 & X1 & N2 & D2 & X2 & N3 & D3 & X3). rewrite ?length_map, ?map_length in O6, X3.
  split; [| lia]. unfold runs3. split; [lia|].
  assert (NR : forall a c : nat, (forall t, (a <= t < c)%nat -> zndig (map bv_unsigned s) t) -> forall t, (o + Z.of_nat a <= t < o + Z.of_nat c)%Z -> bndig bs t).
  { intros a c H t Ht. replace t with (o + Z.of_nat (Z.to_nat (t - o)))%Z by lia. apply ND. apply H. lia. }
  assert (DR : forall a c : nat, (forall t, (a <= t < c)%nat -> zdig (map bv_unsigned s) t) -> forall t, (o + Z.of_nat a <= t < o + Z.of_nat c)%Z -> bdig bs t).
  { intros a c H t Ht. replace t with (o + Z.of_nat (Z.to_nat (t - o)))%Z by lia. apply DG. apply H. lia. }
  split. { intros t Ht. replace t with (o + Z.of_nat (Z.to_nat (t - o)))%Z by lia. apply ND. apply N1. lia. }
  split; [apply DG; apply D1; lia|]. split; [apply (DR j1 e1); exact D1|]. split; [apply ND; exact X1|].
  split; [apply (NR e1 j2); exact N2|]. split; [apply DG; apply D2; lia|]. split; [apply (DR j2 e2); exact D2|]. split; [apply ND; exact X2|].
  split; [apply (NR e2 j3); exact N3|]. split; [apply DG; apply D3; lia|].
  split. { intros t Ht. apply (DR j3 e3); [exact D3| lia]. }
  destruct X3 as [->|X3]; [exact NDE| apply ND; exact X3].
Qed.

Section SEGS2.
Context {HCEIL : HasCeiling}.
  Variables (P q lo : Z).
  Notation S := (P + 480)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo + 1096 <= q)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis QP : (q + 80 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^62)%Z.

  Notation PRS pc x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
  #[using="QLO"] Lemma QLO1 : (lo <= q)%Z. Proof. lia. Qed.
  #[using="PHI"] Lemma PHI1 : (P + 504 < 2^63)%Z. Proof. lia. Qed.

  #[using="QLO LO0 QP PHI"] Lemma rl_loop : forall (k : nat) (A len cap cur : Z) (bs : list byte) (tb tl tyw : word)
      gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (len - cur < Z.of_nat k)%Z ->
    mem_inv rsegs m -> stk rsegs m lo q ->
    rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m MB (mbuf_cells A len cap) ->
    bytes_at rsegs m A bs -> (Z.of_nat (length bs) >= len)%Z -> (0 <= cur <= len)%Z -> (len <= cap)%Z -> (A + cap + 1 < 2^63)%Z ->
    rw_cells rsegs m (q + 16) [C8 tb; C8 tl] -> rw_cells rsegs m (q + 12) [C4 tyw] ->
    (A + Z.of_nat (length bs) <= lo)%Z -> (0 < A \/ (A = 0 /\ len = 0))%Z -> (P mod 8 = 0)%Z -> (q mod 8 = 0)%Z ->
    evt rsegs (fun ms' => exists m' (r cur' : Z) (tb' tl' tyw' : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        munch [(q - 96, q); (P + 488, P + 496); (q + 16, q + 32); (q + 12, q + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo q
        /\ rw_cells rsegs m' MB (mbuf_cells A len cap) /\ bytes_at rsegs m' A bs
        /\ rw_cells rsegs m' (q + 16) [C8 tb'; C8 tl'] /\ rw_cells rsegs m' (q + 12) [C4 tyw']
        /\ (cur <= cur' <= len)%Z /\ (0 <= r <= 5)%Z
        /\ ( (r <> 4 /\ rw_cells rsegs m' S (SCc S MB cur')
              /\ ms' = PRS 0x14bf0 (wz 0x1494c) t0' t1' t2' (wz S) (wz r) a1' a2' a3' a4' a5' a6' a7' (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' gp tp F fc m')
           \/ (exists (tlz ty : Z) a0', r = 4 /\ (1 <= tlz)%Z /\ (cur' + tlz <= len)%Z /\ tb' = wz (A + cur') /\ tl' = wz tlz
              /\ (0 <= ty <= 5)%Z /\ ty <> 1 /\ ty <> 2 /\ (ty = 0 -> cur' + tlz < len)%Z
              /\ rw_cells rsegs m' S (SCc S MB (cur' + tlz))
              /\ ms' = PRS 0x1495c (wz 0x1494c) t0' t1' t2' (wz S) a0' a1' a2' a3' a4' a5' a6' a7' (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' gp tp F fc m') ))
      (PRS 0x1493c x1 t0 t1 t2 (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    induction k as [|k IH]; intros until m; intros HK MI ST SC MBC BUF LBS CUR CAP AHI Q16 Q12 BLO ANZ PAL QAL; [lia|].
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    eapply evt_cut. { apply (rl_head P q). }
    cbv beta. intros ms1 ->.
    eapply evt_cut.
    { eapply (sgt_call q lo S (q + 16) (q + 12) MB A cur len cap bs tb tl tyw); try eassumption; try reflexivity; try lia. }
    intros ms2 PO. unfold sgt_qpost in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & cur2 & tb2 & tl2 & tyw2
                    & -> & MU2 & WM2 & MI2 & ST2 & SC2 & TC2 & TYC2 & CUR2 & RES).
    apply (munch_weaken _ [(q - 96, q); (P + 488, P + 496); (q + 16, q + 32); (q + 12, q + 16)]%Z) in MU2. 2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    pose proof (rw_cells_transport rsegs _ m m2 _ _ MBC MU2 WM2 ltac:(cbn; lia)) as MBC2.
    pose proof (bytes_at_transport rsegs _ m m2 _ _ BUF MU2 ltac:(cbn [disjoint_from]; lia)) as BUF2.
    replace (ret_pc (wz 0x1494c)) with (wz 0x1494c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE, TT_IDENTIFIER, TT_WHITESPACE, TT_CRLF in RES.
    destruct RES as [(tlz & ty & -> & -> & -> & -> & TL1 & -> & CLE & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    -
      eapply evt_cut. { eapply (rl_h2 P q 4 ty); try eassumption; try LiaTuning.alia. intros _; split; [reflexivity| lia]. }
      cbv beta. intros ms3 [[X _]|[(_ & TY12 & a0' & ->)|(_ & N1 & N2 & a0' & ->)]]; [exfalso; lia| |].
      +
        eapply evt_mono.
        { eapply (IH A len cap (cur + tlz)%Z bs); try eassumption; lia. }
        cbv beta. intros ms4 PO. destruct PO as (m4 & r4 & cur4 & tb4 & tl4 & tyw4 & PO). do 14 (let x := fresh "x" in destruct PO as [x PO]).
        destruct PO as (MU4 & WM4 & REST). exists m4, r4, cur4, tb4, tl4, tyw4. do 14 eexists.
        split. { eapply munch_trans; [exact MU2| exact MU4]. }
        split; [eapply wmono_trans; [exact WM2| exact WM4]|].
        destruct REST as (MI4 & ST4 & MBC4 & BUF4 & Q164 & Q124 & CUR4 & R4 & ALT).
        do 6 (split; [assumption|]). split; [lia|]. split; [lia|]. exact ALT.
      +
        apply evt_done. exists m2, 4, cur, (wz (A + cur)), (wz tlz), (wz ty). do 14 eexists.
        split; [exact MU2|]. split; [exact WM2|]. do 6 (split; [assumption|]). split; [lia|]. split; [lia|].
        right. exists tlz, ty, a0'. repeat (split; [first [reflexivity| assumption| lia]|]). reflexivity.
    -
      eapply evt_cut. { eapply (rl_h2 P q r 0); try eassumption; try LiaTuning.alia. }
      cbv beta. intros ms3 [[X ->]|[(X & _)|(X & _)]]; [| exfalso; lia| exfalso; lia].
      apply evt_done. exists m2, r, cur, tb2, tl2, tyw. do 14 eexists.
      split; [exact MU2|]. split; [exact WM2|]. do 6 (split; [assumption|]). split; [lia|]. split; [lia|].
      left. split; [lia|]. split; [exact SC2| reflexivity].
  Qed.

  #[using="QLO LO0 QP PHI"] Lemma rl_pre : forall (A len cap cur : Z) (bs : list byte) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> stk rsegs m lo (q + 80) ->
    rw_cells rsegs m S (SCc S MB cur) -> rw_cells rsegs m MB (mbuf_cells A len cap) ->
    bytes_at rsegs m A bs -> (Z.of_nat (length bs) >= len)%Z -> (0 <= cur <= len)%Z -> (len <= cap)%Z -> (A + cap + 1 < 2^63)%Z ->
    (A + Z.of_nat (length bs) <= lo)%Z -> (0 < A \/ (A = 0 /\ len = 0))%Z -> (P mod 8 = 0)%Z -> (q mod 8 = 0)%Z ->
    evt rsegs (fun ms' => exists m' (r cur' : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        munch [(lo, q + 80); (P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' MB (mbuf_cells A len cap) /\ bytes_at rsegs m' A bs
        /\ (cur <= cur' <= len)%Z /\ (0 <= r <= 5)%Z /\ rw_cells rsegs m' S (SCc S MB cur')
        /\ ( (r <> 4 /\ stk rsegs m' lo (q + 80)
              /\ ms' = MS (mkR ra (wz (q + 80)) gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom rsegs))
           \/ (exists (o l : Z) (bcr : byte) (j0 : list byte) (tyw : word), r = 4 /\ (cur <= o)%Z /\ (0 <= l)%Z /\ (o + l < cur')%Z
              /\ nth_error bs (Z.to_nat (o + l)) = Some bcr /\ (bv_unsigned bcr = 13 \/ bv_unsigned bcr = 10)%Z
              /\ stk rsegs m' lo q /\ rw_cells rsegs m' q [CB 12 j0] /\ rw_cells rsegs m' (q + 12) [C4 tyw]
              /\ rw_cells rsegs m' (q + 16) [C8 (wz (A + o)); C8 (wz l)] /\ rw_cells rsegs m' (q + 32) (rlFS ra s0 s1 s2 s3 s4)
              /\ ms' = PRS 0x14988 (wz 0x14980) t0' t1' t2' (wz S) (wz 4) (wz 4) a2' a3' a4' a5' a6' a7' (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' gp tp F fc m') ))
      (MS (mkR ra (wz (q + 80)) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parse_responseline_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until m; intros MI ST SC MBC BUF LBS CUR CAP AHI BLO ANZ PAL QAL. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.

    eapply evt_cut. { eapply (rl_entry P q lo QLO1 LO0 QP PHI1 cur); try eassumption; lia. }
    cbv beta. intros ms1 (m1 & j0 & tyw & a16 & b16 & a0e & -> & MU1 & WM1 & MI1 & ST1 & Q0 & Q12 & Q16 & FSH & SC1).
    pose proof (rw_cells_transport rsegs _ m m1 _ _ MBC MU1 WM1 ltac:(cbn; lia)) as MBC1.
    pose proof (bytes_at_transport rsegs _ m m1 _ _ BUF MU1 ltac:(cbn [disjoint_from]; lia)) as BUF1.

    eapply evt_cut. { eapply (rl_loop (Datatypes.S (Z.to_nat (len - cur))) A len cap cur bs); try eassumption; lia. }
    cbv beta. intros ms2 PO. destruct PO as (m2 & r & cur2 & tb2 & tl2 & tyw2 & PO). do 14 (let x := fresh "y" in destruct PO as [x PO]).
    destruct PO as (MU2 & WM2 & MI2 & ST2 & MBC2 & BUF2 & Q162 & Q122 & CUR2 & RR & ALT).
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ Q0 MU2 WM2 ltac:(cbn; lia)) as Q02.
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FSH MU2 WM2 ltac:(cbn; lia)) as FSH2.
    assert (MU02 : munch [(lo, q + 80); (P + 488, P + 496)]%Z m m2).
    { eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; intros; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM1 WM2) as WM02. clear MU1 WM1 MU2 WM2 MI1 ST1 SC1 MBC1 BUF1 Q0 Q12 Q16 FSH.
    destruct ALT as [(NR & SC2 & ->)|(tlz & ty & a0' & -> & TL1 & CLE & -> & -> & TY5 & N1 & N2 & STRICT & SC2 & ->)].
    {
      eapply evt_cut. { eapply (rl_epi P q lo QLO1); try eassumption. split; [eexists; exact Q02|]. split; [eexists; exact Q122| do 2 eexists; exact Q162]. }
      cbv beta. intros ms3 [-> ST3]. apply evt_done. exists m2, r, cur2. do 14 eexists.
      split; [exact MU02|]. split; [exact WM02|]. split; [exact MI2|]. split; [exact MBC2|]. split; [exact BUF2|]. split; [lia|]. split; [lia|]. split; [exact SC2|].
      left. split; [exact NR|]. split; [exact ST3| reflexivity]. }

    eapply evt_cut. { eapply (rl_pb P q QP PHI1 tlz (cur2 + tlz)%Z); try eassumption; lia. }
    cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & Q163 & SC3).
    replace (cur2 + tlz - tlz)%Z with cur2 in SC3 by lia. unfold rlFS in FSH2. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC2. clear SC2.
    transport_after_call rsegs m2 m3 MU3 WM3.
    assert (MOK : vf_ok (q + -64) lo S MB A len cap cur2 bs) by (unfold vf_ok; lia).
    eapply evt_cut.
    { eapply (match_resp q lo S MB A len cap cur2 bs MOK (q + 16)); unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc, mbuf_cells, MEMBUF_DEF_SIZE_INC; try eassumption. all: lia. }
    intros ms4 PO. unfold mpost in PO.
    destruct PO as (r4 & cur4 & t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m4
                    & -> & MU4 & WM4 & MI4 & ST4 & SC4 & MBC4 & BUF4 & R4 & CUR4 & MONO & SAME & XR).
    unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc, mbuf_cells, MEMBUF_DEF_SIZE_INC in SC4, MBC4, BUF4.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ Q02 MU4 WM4 ltac:(cbn; lia)) as Q04.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ Q122 MU4 WM4 ltac:(cbn; lia)) as Q124.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FSH2 MU4 WM4 ltac:(cbn; lia)) as FSH4.
    assert (MU04 : munch [(lo, q + 80); (P + 488, P + 496)]%Z m m4).
    { eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; intros; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM02 WM4) as WM04.
    replace (ret_pc (wz 0x14980)) with (wz 0x14980 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct XR as (pa & pb & PC4 & XOK).
    eapply evt_cut. { eapply (rl_m2 P q r4). lia. }
    cbv beta. intros ms5 [[NR ->]|[-> ->]].
    -
      eapply evt_cut. { eapply (rl_epi P q lo QLO1); try eassumption. split; [eexists; exact Q04|]. split; [eexists; exact Q124| do 2 eexists; exact PC4]. }
      cbv beta. intros ms6 [-> ST6]. apply evt_done. exists m4, r4, cur4. do 14 eexists.
      split; [exact MU04|]. split; [exact WM04|]. split; [exact MI4|]. split; [exact MBC4|]. split; [exact BUF4|].
      split; [specialize (SAME NR); lia|]. split; [lia|]. split; [exact SC4|].
      left. split; [exact NR|]. split; [exact ST6| reflexivity].
    -
      destruct (XOK eq_refl) as (o & l & -> & -> & O1 & L1 & OL & CL & bcr & Hbcr & CRLF).
      apply evt_done. exists m4, 4, cur4. do 14 eexists.
      split; [exact MU04|]. split; [exact WM04|]. split; [exact MI4|]. split; [exact MBC4|]. split; [exact BUF4|].
      split; [specialize (MONO eq_refl); lia|]. split; [lia|]. split; [exact SC4|].
      right. exists o, l, bcr, j0, tyw2. repeat (split; [first [reflexivity| eassumption| lia]|]). reflexivity.
    Unshelve. all: try exact (wz 0); try exact 0%Z.
  Qed.

  #[using="QLO LO0 QP PHI"] Lemma rl_mid : forall (A len cap o l cur3 : Z) (bs sl : list byte) (bcr : byte) (j0 : list byte) (tyw pad canary errv : word)
      (rm sc isreq maj min : Z) ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> stk rsegs m lo q ->
    rw_cells rsegs m q [CB 12 j0] -> rw_cells rsegs m (q + 12) [C4 tyw] -> rw_cells rsegs m (q + 16) [C8 (wz (A + o)); C8 (wz l)] ->
    rw_cells rsegs m (q + 32) (rlFS ra s0 s1 s2 s3 s4) ->
    rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs] -> bytes_at rsegs m (A + (cap + 1)) sl ->
    (0 <= o)%Z -> (0 <= l)%Z -> (o + l < cur3)%Z -> (cur3 <= len)%Z -> (len <= cap)%Z -> (cap + 1 <= 2^26 + 16)%Z -> (4096 <= A)%Z ->
    ((A + (cap + 1) + Z.of_nat (length sl)) mod 8 = 0)%Z -> (Z.of_nat (length sl) <= 8)%Z -> (A + (cap + 1) + Z.of_nat (length sl) <= lo)%Z ->
    (A + (cap + 1) + Z.of_nat (length sl) <= 0x2a000 \/ 0x5d000 <= A)%Z ->
    nth_error bs (Z.to_nat (o + l)) = Some bcr -> (bv_unsigned bcr = 13 \/ bv_unsigned bcr = 10)%Z ->
    rw_cells rsegs m (P + 224) [C4 (wz rm); C4 (wz sc)] -> rw_cells rsegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] ->
    (- 2^31 <= sc < 2^31)%Z -> (- 2^31 <= maj < 2^31)%Z -> (- 2^31 <= min < 2^31)%Z ->
    rw_cells rsegs m 0x2a150 [C8 (wz 0x5ba88)] -> rw_cells rsegs m 0x5ba88 [C8 canary] -> rw_cells rsegs m 0x3b77c [C4 errv] ->
    evt rsegs (fun ms' => exists m' (sc' maj' min' : Z) (errv' : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        munch [(lo, q); (A + (o + l), A + (o + l) + 1); (P + 228, P + 232); (P + 276, P + 284); (0x3b77c, 0x3b77c + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB (Z.to_nat (cap + 1)) bs] /\ bytes_at rsegs m' (A + (cap + 1)) sl
        /\ rw_cells rsegs m' (P + 224) [C4 (wz rm); C4 (wz sc')] /\ rw_cells rsegs m' (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj'); C4 (wz min'); C4 pad]
        /\ (- 2^31 <= sc' < 2^31)%Z /\ (- 2^31 <= maj' < 2^31)%Z /\ (- 2^31 <= min' < 2^31)%Z
        /\ rw_cells rsegs m' 0x2a150 [C8 (wz 0x5ba88)] /\ rw_cells rsegs m' 0x5ba88 [C8 canary] /\ rw_cells rsegs m' 0x3b77c [C4 errv']
        /\ ( (stk rsegs m' lo (q + 80)
              /\ ms' = MS (mkR ra (wz (q + 80)) gp (wz 0x3b820) t0' t1' t2' s0 s1 (wz 3) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' (seg_rom rsegs))
           \/ (exists (t' nv : Z) (sb : word), (o <= t' <= o + l)%Z /\ nv = (l - (t' - o))%Z /\ (0 <= sc')%Z /\ (0 <= maj')%Z /\ (0 <= min')%Z
              /\ stk rsegs m' lo q /\ rw_cells rsegs m' q [CB 12 j0] /\ rw_cells rsegs m' (q + 12) [C4 tyw]
              /\ rw_cells rsegs m' (q + 16) [C8 (wz (A + o)); C8 (wz l)] /\ rw_cells rsegs m' (q + 32) (rlFS ra s0 s1 s2 s3 s4)
              /\ ms' = MS (mkR (wz 0x14bd0) (wz q) gp (wz 0x3b820) t0' t1' t2' (wz P) (wz (P + 228)) (wz (P + 232)) (wz (A + t')) (wz nv) a3' a4' a5' a6' a7' (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (wz membuffer_assign_entry) fc None m' (seg_rom rsegs)) ))
      (PRS 0x14988 (wz 0x14980) t0 t1 t2 (wz S) (wz 4) (wz 4) a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp (wz 0x3b820) F fc m).
  Proof.
    intros until m; intros MI ST Q0 Q12 Q16 FSH BLK SLK O0 L0 OL CL LC CMX A0 AL8 SL8 ALO WIN Hbcr CRLF RS VER SCR MJR MNR SSP1 SSP2 ERR.
    unfold rlFS in FSH.
    pose proof (bytes_at_bound _ _ _ _ SLK) as BSL.
    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    set (k := (o + l)%Z) in *. assert (Hk : k = (o + l)%Z) by reflexivity.

    eapply evt_cut. { eapply (rl_nul P q lo QLO1 QP PHI1 A o l (Z.to_nat (cap + 1)) bs); try eassumption; lia. }
    cbv beta. intros ms1 (m1 & b & Hb & -> & MU1 & WM1 & MI1 & Q161 & BLK1).
    fold k in Hb, MU1, BLK1. rewrite Hbcr in Hb. injection Hb as <-.
    change (firstn (Z.to_nat k) bs ++ [zb] ++ skipn (Z.to_nat k + 1) bs) with (set_byte bs (Z.to_nat k) zb) in BLK1.

    split_chunk VER 2%nat VER0 VR1. split_chunk VR1 1%nat PMJ VR2. split_chunk VR2 1%nat PMN PPD.
    split_chunk RS 1%nat RS0 PSC.
    clear Q16 BLK. transport_after_call rsegs m m1 MU1 WM1.

    apply (munch_weaken _ [(lo, q); (A + k, A + k + 1); (P + 228, P + 232); (P + 276, P + 284); (0x3b77c, 0x3b77c + 4)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    rename MU1 into MUacc. rename WM1 into WMacc. stash MUacc. stash WMacc.

    set (bs1 := set_byte bs (Z.to_nat k) zb) in *.
    assert (LB1 : length bs1 = length bs) by (subst bs1; apply set_byte_length; lia).
    assert (INZ : In zb (skipn (Z.to_nat o) bs1)).
    { apply (nth_error_In _ (Z.to_nat l)). rewrite nth_error_skipnZ. replace (Z.to_nat o + Z.to_nat l)%nat with (Z.to_nat k) by lia. subst bs1. apply set_byte_same. lia. }
    destruct (first_nulB _ _ INZ) as (s & rr & SPLIT & NIN).
    set (txt := map bv_unsigned (skipn (Z.to_nat o) bs1 ++ sl)). set (pre := map bv_unsigned s). set (post := map bv_unsigned (rr ++ sl)).
    assert (LS : (length s <= Z.to_nat l)%nat).
    { destruct (Nat.le_gt_cases (length s) (Z.to_nat l)) as [LE|GT]; [exact LE| exfalso]. apply NIN.
      apply (nth_error_In _ (Z.to_nat l)). rewrite <- (nth_error_app1 s (zb :: rr)) by lia. rewrite <- SPLIT, nth_error_skipnZ.
      replace (Z.to_nat o + Z.to_nat l)%nat with (Z.to_nat k) by lia. subst bs1. apply set_byte_same. lia. }
    assert (LSK : length (skipn (Z.to_nat o) bs1) = (length s + 1 + length rr)%nat) by (rewrite SPLIT, length_app; cbn; lia).
    rewrite length_skipn in LSK.
    assert (TXT : rtext (A + o) txt pre post).
    { unfold rtext. split.
      { subst txt pre post. rewrite SPLIT, <- app_assoc. cbn [app]. rewrite map_app. cbn [map]. replace (bv_unsigned zb) with 0%Z by (vm_compute; reflexivity). reflexivity. }
      split.
      { subst pre. apply Forall_map. apply Forall_forall. intros bb Hbb. cbv beta. pose proof (byte_range bb) as R.
        assert (bb <> zb) by (intros ->; exact (NIN Hbb)). enough (bv_unsigned bb <> 0)%Z by lia.
        intros E. apply H. apply bv_eq. rewrite E. vm_compute. reflexivity. }
      split.
      { subst txt. apply Forall_map. apply Forall_forall. intros bb _. cbv beta. pose proof (byte_range bb). lia. }
      split.
      { subst pre post. unfold Prelim.zlength. rewrite ?length_map, ?map_length, ?length_app, ?app_length, ?length_map, ?map_length.
        enough (HH : ((- (A + o + Z.of_nat (length s) + 1)) mod 8 <= A + (cap + 1) + Z.of_nat (length sl) - (A + o + Z.of_nat (length s) + 1))%Z) by lia.
        set (N := (A + o + Z.of_nat (length s) + 1)%Z). set (E8 := (A + (cap + 1) + Z.of_nat (length sl))%Z) in *.
        assert (HN : (N <= E8)%Z) by (subst N E8; lia).
        rewrite <- (Z.mod_add (- N) (E8 / 8) 8) by lia.
        replace (- N + E8 / 8 * 8)%Z with (E8 - N)%Z by (Z.div_mod_to_equations; lia).
        apply Z.mod_le; lia. }
      subst txt. unfold Prelim.zlength. rewrite ?length_map, ?map_length, ?length_app, ?app_length, ?length_skipn, ?skipn_length. lia. }
    assert (BYT : bytes_at rsegs m1 (A + o) (zbytes txt)).
    { subst txt. rewrite zbytes_bytes. apply bytes_at_app. split.
      - pose proof (proj2 (proj1 BLK1)) as BB1. cbn [cells_bytes cbytes] in BB1. rewrite app_nil_r in BB1.
        rewrite <- (firstn_skipn (Z.to_nat o) bs1) in BB1. apply bytes_at_app in BB1. destruct BB1 as [_ BB1].
        rewrite firstn_length_le in BB1 by lia. replace (A + Z.of_nat (Z.to_nat o))%Z with (A + o)%Z in BB1 by lia. exact BB1.
      - rewrite length_skipn. replace (A + o + Z.of_nat (length bs1 - Z.to_nat o))%Z with (A + (cap + 1))%Z by lia. exact SLK. }

    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
    assert (LTXT : Prelim.zlength txt = (cap + 1 - o + Z.of_nat (length sl))%Z).
    { subst txt. unfold Prelim.zlength. rewrite ?length_map, ?map_length, ?length_app, ?app_length, ?length_skipn, ?skipn_length. lia. }
    pose proof sscanf_status_spec as SS. unfold sscanf_status_stmt, SSCANF_DEPTH, ERRNOA, SSCANF, FA_STATUS in SS.
    eapply evt_cut.
    { eapply SS with (sp := wz q) (txt := txt) (pre := pre) (post := post) (lo := lo) (canary := canary); rewrite ?EQ;
        first [ exact TXT | exact BYT | eassumption | unfold ssp_cells, got_ssp, ssp_guard; split; eassumption | apply unsigned_lit; lia | lia ]. }
    clear SS. intros ms2 PO. unfold sscanf3_post, ERRNOA in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ev & v1 & v2 & v3 & r
                    & -> & SM & RR & MU2 & WM2 & MI2 & ST2 & BYT2 & [SSP1' SSP2'] & ERR2 & PC1 & PC2 & PC3).
    unfold got_ssp, ssp_guard in SSP1', SSP2'. rewrite EQ in MU2, ST2.
    clear MI1 ST BYT PMJ PMN PSC SSP1 SSP2 ERR.
    transport_after_call rsegs m1 m2 MU2 WM2.
    unstash. apply (munch_trans _ _ _ m2) in MUacc. 2:{ eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    apply (wmono_trans rsegs _ _ m2) in WMacc; [| exact WM2]. clear MU2 WM2. stash MUacc. stash WMacc.
    apply rw_cells_C4_s32v in PC1. apply rw_cells_C4_s32v in PC2. apply rw_cells_C4_s32v in PC3.
    pose proof (s32v_range v1) as R1. pose proof (s32v_range v2) as R2. pose proof (s32v_range v3) as R3.
    replace (ret_pc (wz 0x149dc)) with (wz 0x149dc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    eapply evt_cut.
    { eapply (rl_chk P q lo QLO1 QP PHI1 r A o l (s32v v1) (s32v v2) (s32v v3) (Z.to_nat (cap + 1)) bs1 bcr); try eassumption; try LiaTuning.alia. }
    cbv beta. intros ms3 (m3 & a1'' & a2'' & a3'' & a4'' & MU3 & WM3 & MI3 & Q163 & BLK3 & PC13 & PC23 & PC33 & ALT). fold k in MU3, BLK3.
    change (firstn (Z.to_nat k) bs1 ++ [bcr] ++ skipn (Z.to_nat k + 1) bs1) with (set_byte bs1 (Z.to_nat k) bcr) in BLK3.
    assert (RESTORE : set_byte bs1 (Z.to_nat k) bcr = bs) by (subst bs1; apply set_byte_restore; exact Hbcr). rewrite RESTORE in BLK3. clear RESTORE.
    clear BYT2 BLK1 MI2 Q161. transport_after_call rsegs m2 m3 MU3 WM3.
    unstash. apply (munch_trans _ _ _ m3) in MUacc. 2:{ eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    apply (wmono_trans rsegs _ _ m3) in WMacc; [| exact WM3]. clear MU3 WM3.

    assert (VER3 : rw_cells rsegs m3 (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz (s32v v1)); C4 (wz (s32v v2)); C4 pad]).
    { apply (proj2 (rw_cells_app rsegs m3 (P + 264) [C8 (wz 0); C4 (wz isreq)] [C4 (wz (s32v v1)); C4 (wz (s32v v2)); C4 pad])). split; [exact VER0|].
      cbn [cells_size csize Nat.add]. replace (P + 264 + Z.of_nat 12)%Z with (P + 276)%Z by lia.
      apply (proj2 (rw_cells_app rsegs m3 (P + 276) [C4 (wz (s32v v1))] [C4 (wz (s32v v2)); C4 pad])). split; [exact PC13|].
      cbn [cells_size csize Nat.add]. replace (P + 276 + Z.of_nat 4)%Z with (P + 280)%Z by lia.
      apply (proj2 (rw_cells_app rsegs m3 (P + 280) [C4 (wz (s32v v2))] [C4 pad])). split; [exact PC23|].
      cbn [cells_size csize Nat.add]. replace (P + 280 + Z.of_nat 4)%Z with (P + 284)%Z by lia. exact PPD. }
    assert (RS3 : rw_cells rsegs m3 (P + 224) [C4 (wz rm); C4 (wz (s32v v3))]).
    { apply (proj2 (rw_cells_app rsegs m3 (P + 224) [C4 (wz rm)] [C4 (wz (s32v v3))])). split; [exact RS0|].
      cbn [cells_size csize Nat.add]. replace (P + 224 + Z.of_nat 4)%Z with (P + 228)%Z by lia. exact PC33. }
    clear VER0 PC13 PC23 PPD RS0 PC33.
    rename MUacc into MU03. rename WMacc into WM03.
    destruct ALT as [(WHY & ->)|((-> & MJ0 & MN0 & SC0) & ->)].
    {
      eapply evt_cut. { eapply (rl_epi P q lo QLO1); try eassumption. split; [eexists; exact Q0|]. split; [eexists; exact Q12| do 2 eexists; exact Q163]. }
      cbv beta. intros ms4 [-> ST4]. apply evt_done. exists m3, (s32v v3), (s32v v1), (s32v v2), ev. do 14 eexists.
      split; [exact MU03|]. split; [exact WM03|]. split; [exact MI3|]. split; [exact BLK3|]. split; [exact SLK|].
      split; [exact RS3|]. split; [exact VER3|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact SSP1'|]. split; [exact SSP2'|]. split; [exact ERR2|]. left. split; [exact ST4| reflexivity]. }

    pose proof TXT as (Htxt & NZ & _ & _ & _). rewrite Htxt in SM.
    destruct (sscanf_model_scan_count ScanInt.FMT_STATUSLINE pre post 3 NZ sd_ok_status SM) as [SC3|[X _]]; [| lia].
    symmetry in SC3. destruct (statusline_runs pre SC3) as (j1 & e1 & j2 & e2 & j3 & e3 & RRS).
    destruct (runs_bridge bs o l s rr bcr j1 e1 j2 e2 j3 e3 O0 L0 ltac:(lia) SPLIT NIN Hbcr CRLF RRS) as [RUNS E3L].
    pose proof (proj2 (proj1 BLK3)) as BUF3. cbn [cells_bytes cbytes] in BUF3. rewrite app_nil_r in BUF3.
    eapply evt_cut.
    { eapply (rl_walk P q A o l); try eassumption; try LiaTuning.alia. unfold bblank. lia. }
    cbv beta. intros ms4 [(b1' & b2' & b3' & b4' & b5' & b6' & b7' & ->)|(t' & nv & bt' & b3' & b4' & b5' & b6' & b7' & RT & Hbt' & NB & Hnv & ->)].
    -
      eapply evt_cut. { eapply (rl_epi P q lo QLO1); try eassumption. split; [eexists; exact Q0|]. split; [eexists; exact Q12| do 2 eexists; exact Q163]. }
      cbv beta. intros ms5 [-> ST5]. apply evt_done. exists m3, (s32v v3), (s32v v1), (s32v v2), ev. do 14 eexists.
      split; [exact MU03|]. split; [exact WM03|]. split; [exact MI3|]. split; [exact BLK3|]. split; [exact SLK|].
      split; [exact RS3|]. split; [exact VER3|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact SSP1'|]. split; [exact SSP2'|]. split; [exact ERR2|]. left. split; [exact ST5| reflexivity].
    -
      apply evt_done. exists m3, (s32v v3), (s32v v1), (s32v v2), ev. do 14 eexists.
      split; [exact MU03|]. split; [exact WM03|]. split; [exact MI3|]. split; [exact BLK3|]. split; [exact SLK|].
      split; [exact RS3|]. split; [exact VER3|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact SSP1'|]. split; [exact SSP2'|]. split; [exact ERR2|]. right.
      exists t', nv, (wz (bv_unsigned bcr)). split; [lia|]. split; [exact Hnv|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [assumption|]. split; [exact Q0|]. split; [exact Q12|]. split; [exact Q163|]. split; [exact FSH| reflexivity].
    Unshelve. all: try exact (wz 0); try exact 0%Z.
  Qed.
End SEGS2.
