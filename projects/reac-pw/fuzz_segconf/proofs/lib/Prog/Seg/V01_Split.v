(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): SPLIT, the inline m_split
   of turn i (fuzz_segconf.c:323-350 inside m_declared's loop): from LOOP (0x13d64) to JOIN
   (0x13d74, the `continue`) or to ADD (0x13e64).
   - 0x13d64 .. 0x13d70: s7 = m + 256 i (the name of seg[i]), `lw` seg[i].ignore (flag_enc), `beqz`: an ignored
     segment goes to JOIN.
   - 0x13d88 .. 0x13d90: strrchr(name, '.') (strrchr_contract; the name is the C string of the 16-byte field, the
     rest of the field is its slack; the stack below sp is main's stack window). SegModel.strrchr on the name is
     memrchr_c.rfind_byte 46 on its bytes ([V01SplitPure.v01s_strrchr]).
   - 0x13d94 .. 0x13da4: no dot, dot at 0 or dot[1] = NUL go to JOIN (m_split = None).
   - 0x13db0: the digit loop (v01_dig_stmt) from dot[1]; m_digits None goes to JOIN; 0x13dd4 `beqz s5`: vid = 0 goes
     to JOIN.
   - 0x13dd8 .. 0x13de8: pn = dot - name, then the parent loop (v01_par_stmt) over the pn bytes of the name; a
     character that is not a parent character goes to JOIN.
   - 0x13e40 .. 0x13e60: tab spilled at 8(sp), memcpy(v.parent, name, pn) (memcpy_contract), v.parent[pn] = 0,
     v.vid = vid: the 20 bytes at sp + 0x40 encode (firstn pn name, vid) (mvlan_enc), then ADD.
   Each JOIN exit keeps T and added and steps the model past segment i (m_decl_go at nth i :: skipn (S i)).
   [V01SplitPure] holds the build-independent lemmas (strrchr bridge, m_split decomposition, the name bytes and the
   ignore flag of seg[i] from mconf_enc, list and byte facts).
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_cuts memrchr_c strrchr_c
  memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import V01_Inv MainBPure.
Import ListNotations.
Open Scope Z_scope.

Module V01SplitPure.

(* ---- Lists ---- *)
Lemma v01s_firstn_snoc : forall {A} (l : list A) x r, firstn (S (length l)) (l ++ x :: r) = l ++ [x].
Proof. intros A l. induction l as [|y l IH]; intros x r; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma v01s_firstn1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d H.
  - cbn in H. exfalso. exact (Nat.nlt_0_r _ H).
  - destruct k as [|k].
    + reflexivity.
    + cbn [skipn nth]. apply IH. cbn [length] in H. apply (proj2 (Nat.succ_lt_mono k (length l))). exact H.
Qed.

Lemma v01s_skipn_nth : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d H.
  - cbn in H. exfalso. exact (Nat.nlt_0_r _ H).
  - destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in H.
    apply (proj2 (Nat.succ_lt_mono k (length l))). exact H.
Qed.

Lemma v01s_fld_fld : forall o1 n1 o2 n2 (l : list byte), (o2 + n2 <= n1)%nat ->
  fld o2 n2 (fld o1 n1 l) = fld (o1 + o2) n2 l.
Proof.
  intros o1 n1 o2 n2 l H. unfold fld.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n2 (n1 - o2)) with n2 by lia. replace (o2 + o1)%nat with (o1 + o2)%nat by lia. reflexivity.
Qed.

Lemma v01s_nin_skipn : forall (sx : list byte) k, ~ In ZERO sx -> ~ In ZERO (skipn k sx).
Proof. intros sx k N Hin. apply N. rewrite <- (firstn_skipn k sx). apply in_or_app. right. exact Hin. Qed.

Lemma v01s_nin_firstn : forall (sx : list byte) k, ~ In ZERO sx -> ~ In ZERO (firstn k sx).
Proof. intros sx k N Hin. apply N. rewrite <- (firstn_skipn k sx). apply in_or_app. left. exact Hin. Qed.

(* ---- Byte strings and their Z views ---- *)
Lemma v01s_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma v01s_zs_nul : forall l : list byte, ~ In ZERO l -> ~ In 0 (zs l).
Proof.
  intros l N Hin. unfold zs in Hin. apply in_map_iff in Hin as (b & Hb & Hi). apply N.
  replace ZERO with b; [exact Hi|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma v01s_firstn_zs : forall n (l : list byte), firstn n (zs l) = zs (firstn n l).
Proof. unfold zs. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma v01s_skipn_zs : forall n (l : list byte), skipn n (zs l) = zs (skipn n l).
Proof. unfold zs. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

(* A char[cap] field holding s: the bytes of s, the NUL, the slack. *)
Lemma v01s_cstr_split : forall cap s f, cstr_enc cap s f ->
  exists sx slack, f = sx ++ ZERO :: slack /\ zs sx = s /\ ~ In ZERO sx.
Proof.
  intros cap s f (Lf & Ls & N & E).
  pose proof (firstn_skipn (length s) f) as Ef.
  assert (Lsx : length (firstn (length s) f) = length s) by (rewrite length_firstn; lia).
  remember (firstn (length s) f) as sx eqn:Hsx. clear Hsx.
  revert Ef. destruct (skipn (length s) f) as [|b slack]; intros Ef.
  { exfalso. rewrite app_nil_r in Ef. rewrite <- Ef in Lf. lia. }
  subst f.
  unfold zs in E. rewrite map_app in E. cbn [map] in E.
  rewrite <- Lsx in E. rewrite <- (length_map (@bv_unsigned 8) sx) in E. rewrite v01s_firstn_snoc in E.
  apply app_inj_tail in E as [E1 E2].
  assert (Eb : b = ZERO) by (apply bv_eq; rewrite E2; reflexivity). subst b.
  exists sx, slack. split; [reflexivity|]. split; [exact E1|].
  intros Hin. apply N. rewrite <- E1. exact (in_map (@bv_unsigned 8) sx ZERO Hin).
Qed.

(* hd0 of the name from k on is the byte at k of the field (the NUL at k = length). *)
Lemma v01s_hd0 : forall (sx slack : list byte) k, (k <= length sx)%nat ->
  hd0 (skipn k (zs sx)) = bv_unsigned (nth k (sx ++ ZERO :: slack) ZERO).
Proof.
  unfold zs. induction sx as [|x sx IH]; intros slack k Hk.
  - cbn [length] in Hk. apply Nat.le_0_r in Hk. subst k. reflexivity.
  - destruct k as [|k]; [reflexivity|].
    cbn [map skipn app nth]. apply IH. cbn [length] in Hk. apply (proj2 (Nat.succ_le_mono k (length sx))). exact Hk.
Qed.

Lemma v01s_nz_lt : forall (sx slack : list byte) k, (k <= length sx)%nat ->
  bv_unsigned (nth k (sx ++ ZERO :: slack) ZERO) <> 0 -> (k < length sx)%nat.
Proof.
  intros sx slack k Hk Hn. destruct (Nat.eq_dec k (length sx)) as [E|Hne]; [|lia].
  exfalso. apply Hn. subst k. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma v01s_digits_in : forall (sx slack : list byte) k, (k < length sx)%nat ->
  skipn k (zs sx) = bv_unsigned (nth k (sx ++ ZERO :: slack) ZERO) :: zs (skipn (S k) sx).
Proof.
  intros sx slack k H. rewrite v01s_skipn_zs, (v01s_skipn_nth sx k ZERO H). rewrite app_nth1 by exact H.
  reflexivity.
Qed.

(* ---- SegModel.strrchr against memrchr_c.rfind_byte ---- *)
Lemma v01s_last_idx : forall c (l : list byte) i acc,
  last_idx c (zs l) i acc = match rfind_byte c l with Some k => Some (i + k)%nat | None => acc end.
Proof.
  intros c l. unfold zs. induction l as [|b l IH]; intros i acc; [reflexivity|].
  cbn [map last_idx rfind_byte]. rewrite IH.
  destruct (rfind_byte c l) as [k|]; cbn.
  - f_equal. symmetry. apply Nat.add_succ_r.
  - destruct (bv_unsigned b =? c); cbn; [f_equal; symmetry; apply Nat.add_0_r | reflexivity].
Qed.

Lemma v01s_strrchr : forall l : list byte, ~ In ZERO l -> strrchr (zs l) 46 = rfind_byte 46 l.
Proof.
  intros l N. unfold strrchr. rewrite cut_nul_id by exact (v01s_zs_nul l N). rewrite v01s_last_idx.
  destruct (rfind_byte 46 l); reflexivity.
Qed.

Lemma v01s_res_some : forall A c str j, rfind_byte 46 str = Some j -> c = 46 -> strrchr_res A c str = A + Z.of_nat j.
Proof. intros A c str j H ->. rewrite strrchr_res_nonnul by lia. rewrite H. reflexivity. Qed.

Lemma v01s_res_none : forall A c str, rfind_byte 46 str = None -> c = 46 -> strrchr_res A c str = 0.
Proof. intros A c str H ->. rewrite strrchr_res_nonnul by lia. rewrite H. reflexivity. Qed.

(* ---- m_split, case by case ---- *)
Lemma v01s_digits_rng : forall l vid v, 0 <= vid <= 4094 -> m_digits l vid = Some v -> 0 <= v <= 4094.
Proof.
  induction l as [|q r IH]; intros vid v Hv H.
  - cbn [m_digits] in H. injection H as <-. exact Hv.
  - revert H. cbn [m_digits].
    destruct (q <? 48) eqn:E1; [intros H; discriminate H|].
    destruct (57 <? q) eqn:E2; [intros H; discriminate H|].
    cbn [orb].
    match goal with |- context [if 4094 <? ?e then _ else _] => destruct (4094 <? e) eqn:E3 end;
      [intros H; discriminate H|].
    intros H. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. apply Z.ltb_ge in E3.
    eapply IH; [|exact H]. lia.
Qed.

Lemma v01s_split_none_rf : forall sx, ~ In ZERO sx -> rfind_byte 46 sx = None -> m_split (zs sx) = None.
Proof. intros sx N H. unfold m_split. rewrite v01s_strrchr by exact N. rewrite H. reflexivity. Qed.

Lemma v01s_split_none_j0 : forall sx, ~ In ZERO sx -> rfind_byte 46 sx = Some 0%nat -> m_split (zs sx) = None.
Proof. intros sx N H. unfold m_split. rewrite v01s_strrchr by exact N. rewrite H. reflexivity. Qed.

Lemma v01s_split_none_hd : forall sx j, ~ In ZERO sx -> rfind_byte 46 sx = Some j ->
  hd0 (skipn (S j) (zs sx)) = 0 -> m_split (zs sx) = None.
Proof.
  intros sx j N H Hh. unfold m_split. rewrite v01s_strrchr by exact N. rewrite H. cbv beta iota.
  rewrite Hh, Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma v01s_split_none_dig : forall sx j, ~ In ZERO sx -> rfind_byte 46 sx = Some j ->
  m_digits (skipn (S j) (zs sx)) 0 = None -> m_split (zs sx) = None.
Proof.
  intros sx j N H Hd. unfold m_split. rewrite v01s_strrchr by exact N. rewrite H. cbv beta iota.
  rewrite Hd. destruct ((j =? 0)%nat || (hd0 (skipn (S j) (zs sx)) =? 0)); reflexivity.
Qed.

Lemma v01s_split_none_v0 : forall sx j v, ~ In ZERO sx -> rfind_byte 46 sx = Some j ->
  m_digits (skipn (S j) (zs sx)) 0 = Some v -> v < 1 -> m_split (zs sx) = None.
Proof.
  intros sx j v N H Hd Hv. unfold m_split. rewrite v01s_strrchr by exact N. rewrite H. cbv beta iota.
  rewrite Hd. cbv beta iota. rewrite (proj2 (Z.ltb_lt v 1) Hv).
  destruct ((j =? 0)%nat || (hd0 (skipn (S j) (zs sx)) =? 0)); reflexivity.
Qed.

Lemma v01s_split_none_par : forall sx j v, ~ In ZERO sx -> rfind_byte 46 sx = Some j ->
  m_digits (skipn (S j) (zs sx)) 0 = Some v -> forallb h_parent_ok (firstn j (zs sx)) = false ->
  m_split (zs sx) = None.
Proof.
  intros sx j v N H Hd Hp. unfold m_split. rewrite v01s_strrchr by exact N. rewrite H. cbv beta iota.
  rewrite Hd. cbv beta iota. rewrite Hp.
  destruct ((j =? 0)%nat || (hd0 (skipn (S j) (zs sx)) =? 0)); [reflexivity|]. destruct (v <? 1); reflexivity.
Qed.

Lemma v01s_split_some : forall sx j v, ~ In ZERO sx -> rfind_byte 46 sx = Some j -> j <> 0%nat ->
  hd0 (skipn (S j) (zs sx)) <> 0 -> m_digits (skipn (S j) (zs sx)) 0 = Some v -> 1 <= v ->
  forallb h_parent_ok (firstn j (zs sx)) = true -> m_split (zs sx) = Some (firstn j (zs sx), v).
Proof.
  intros sx j v N H Hj Hh Hd Hv Hp. unfold m_split. rewrite v01s_strrchr by exact N. rewrite H. cbv beta iota.
  rewrite (proj2 (Nat.eqb_neq j 0) Hj), (proj2 (Z.eqb_neq _ 0) Hh). cbn [orb].
  rewrite Hd. cbv beta iota. rewrite (proj2 (Z.ltb_ge v 1) Hv), Hp. reflexivity.
Qed.

(* m_decl_go past a segment it skips. *)
Lemma v01s_model_skip : forall segs T cap added i res, (i < length segs)%nat ->
  m_decl_go (skipn i segs) T cap added = res ->
  (ms_ignore (nth i segs mseg_d) = true \/ m_split (ms_name (nth i segs mseg_d)) = None) ->
  m_decl_go (skipn (S i) segs) T cap added = res.
Proof.
  intros segs T cap added i res Hi H Hc. rewrite <- H. rewrite (v01s_skipn_nth segs i mseg_d Hi).
  cbn [m_decl_go]. destruct Hc as [E|E]; rewrite E; [reflexivity|].
  destruct (ms_ignore (nth i segs mseg_d)); reflexivity.
Qed.

(* The 20 bytes of v: parent, NUL, slack, vid. *)
Lemma v01s_mvlan : forall (src r : list byte) v n1 n2, ~ In ZERO src -> (length src + length r = 15)%nat ->
  0 <= v < 2 ^ 32 -> mvlan_enc (zs src, v) (cells_bytes [CB n1 src; C1 ZERO; CB n2 r; C4 (Z_to_bv 64 v)]).
Proof.
  intros src r v n1 n2 N L Hv.
  assert (EX : cells_bytes [CB n1 src; C1 ZERO; CB n2 r; C4 (Z_to_bv 64 v)] =
               (src ++ ZERO :: r) ++ le4 (Z_to_bv 64 v))
    by (cbn [cells_bytes cbytes]; rewrite app_nil_r, <- app_assoc; reflexivity).
  rewrite EX.
  assert (L16 : length (src ++ ZERO :: r) = 16%nat).
  { rewrite length_app. cbn [length]. rewrite Nat.add_succ_r, L. reflexivity. }
  assert (L4 : length (le4 (Z_to_bv 64 v)) = 4%nat) by apply length_le4.
  assert (F1 : firstn 16 ((src ++ ZERO :: r) ++ le4 (Z_to_bv 64 v)) = src ++ ZERO :: r)
    by (rewrite <- L16; apply firstn_app_exact).
  assert (F2 : skipn 16 ((src ++ ZERO :: r) ++ le4 (Z_to_bv 64 v)) = le4 (Z_to_bv 64 v))
    by (rewrite <- L16; apply skipn_app_exact).
  unfold mvlan_enc, fld. cbn [fst snd]. change (skipn 0 ((src ++ ZERO :: r) ++ le4 (Z_to_bv 64 v)))
    with ((src ++ ZERO :: r) ++ le4 (Z_to_bv 64 v)).
  rewrite F1, F2.
  split; [rewrite length_app, L16, L4; reflexivity|].
  split.
  - unfold cstr_enc. split; [exact L16|]. split; [unfold zs; rewrite length_map; lia|].
    split; [exact (v01s_zs_nul src N)|].
    unfold zs. rewrite map_app. cbn [map]. rewrite v01s_firstn_snoc. reflexivity.
  - unfold u32_enc. split; [exact Hv|]. apply firstn_all2. rewrite L4. lia.
Qed.

Section Mem.
Variable segs : list Segment.

Lemma v01s_ba_eq : forall m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

Lemma v01s_ba_win : forall m a bs k l, bytes_at segs m a bs -> (k + l <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn l (skipn k bs)).
Proof.
  intros m a bs k l H Hl.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn l (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma v01s_ba_pre : forall m a sx slack k, bytes_at segs m a (sx ++ ZERO :: slack) -> (k <= length sx)%nat ->
  bytes_at segs m a (firstn k sx).
Proof.
  intros m a sx slack k H Hk.
  rewrite <- (firstn_skipn k sx) in H. rewrite <- app_assoc in H.
  apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma v01s_ba_suf : forall m a sx slack k, bytes_at segs m a (sx ++ ZERO :: slack) -> (k <= length sx)%nat ->
  bytes_at segs m (a + Z.of_nat k) (skipn k sx ++ [ZERO]).
Proof.
  intros m a sx slack k H Hk.
  rewrite <- (firstn_skipn k sx) in H. rewrite <- app_assoc in H.
  apply bytes_at_app in H as [_ H]. rewrite length_firstn, Nat.min_l in H by exact Hk.
  replace (skipn k sx ++ ZERO :: slack) with ((skipn k sx ++ [ZERO]) ++ slack) in H
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma v01s_rd_field : forall m a sx slack k, bytes_at segs m a (sx ++ ZERO :: slack) -> (k <= length sx)%nat ->
  ov_read_bytes segs m (wa (a + Z.of_nat k)) 1 = Some [nth k (sx ++ ZERO :: slack) ZERO].
Proof.
  intros m a sx slack k H Hk.
  rewrite (bytes_at_ov_read segs m a (sx ++ ZERO :: slack) k 1 H).
  - f_equal. apply v01s_firstn1. rewrite length_app. cbn [length]. rewrite Nat.add_succ_r. apply le_n_S.
    apply Nat.le_trans with (length sx); [exact Hk | apply Nat.le_add_r].
  - rewrite length_app. cbn [length].
    apply Nat.le_trans with (length sx + 1)%nat; [apply Nat.add_le_mono_r; exact Hk|].
    apply Nat.add_le_mono_l. apply le_n_S. apply Nat.le_0_l.
Qed.

(* The name field and the ignore flag of seg[i] of a struct mconf. *)
Lemma v01s_name : forall m a bs mc i, bytes_at segs m a bs -> mconf_enc mc bs -> (i < length (mc_seg mc))%nat ->
  exists sx slack, bytes_at segs m (a + 256 * Z.of_nat i) (sx ++ ZERO :: slack) /\
    zs sx = ms_name (nth i (mc_seg mc) mseg_d) /\ ~ In ZERO sx /\ (length sx + length slack = 15)%nat /\
    ov_read_bytes segs m (wa (a + 256 * Z.of_nat i + 24)) 4 =
      Some (le4 (Z_to_bv 64 (if ms_ignore (nth i (mc_seg mc) mseg_d) then 1 else 0))).
Proof.
  intros m a bs mc i B (L & L32 & HS & _) Hi.
  destruct (HS i Hi) as (Lf & Hn & _ & _ & Hig & _).
  unfold SEG_M_SIZE in L.
  rewrite (v01s_fld_fld (256 * i) 256 0 16 bs) in Hn by lia.
  change (fldz MS_IGNORE 4 (fld (256 * i) 256 bs)) with (fld 24 4 (fld (256 * i) 256 bs)) in Hig.
  rewrite (v01s_fld_fld (256 * i) 256 24 4 bs) in Hig by lia.
  pose proof (proj1 Hn) as L16.
  destruct (v01s_cstr_split _ _ _ Hn) as (sx & slack & Ef & Ez & Nz).
  exists sx, slack. split; [|split; [exact Ez|split; [exact Nz|split]]].
  - rewrite <- Ef. unfold fld.
    apply (v01s_ba_eq m (a + Z.of_nat (256 * i + 0))); [apply v01s_ba_win; [exact B | lia] | lia].
  - rewrite Ef, length_app in L16. cbn [length] in L16. rewrite Nat.add_succ_r in L16.
    injection L16 as L16. exact L16.
  - unfold flag_enc in Hig. rewrite <- Hig. unfold fld.
    replace (a + 256 * Z.of_nat i + 24) with (a + Z.of_nat (256 * i + 24)) by lia.
    apply bytes_at_ov_read; [exact B | lia].
Qed.

(* rw_cells over a list of cells: the head cell and the rest, and back. *)
Lemma v01s_rwc_eq : forall m A A' cs, rw_cells segs m A cs -> A = A' -> rw_cells segs m A' cs.
Proof. intros; subst; assumption. Qed.

Lemma v01s_rwc_split : forall m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (Ha & Hn & Hw)].
  apply cells_wf_app in W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; [exact W1 | exact B1]|].
    split; [lia|]. split; [lia|]. intros k Hk. apply Hw. lia.
  - split; [split; [exact W2 | exact B2]|].
    split; [lia|]. split; [lia|]. intros k Hk.
    replace (A + Z.of_nat (cells_size cs1) + k) with (A + (Z.of_nat (cells_size cs1) + k)) by lia.
    apply Hw. lia.
Qed.

Lemma v01s_rwc_merge : forall m A cs1 cs2, rw_cells segs m A cs1 ->
  rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hn1 & H1)] [[W2 B2] (Ha2 & Hn2 & H2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros k Hk.
    destruct (Z.lt_ge_cases k (Z.of_nat (cells_size cs1))) as [Hlt|Hge].
    + apply H1. lia.
    + replace (A + k) with (A + Z.of_nat (cells_size cs1) + (k - Z.of_nat (cells_size cs1))) by lia.
      apply H2. lia.
Qed.

Lemma v01s_rwc_cons : forall m A c cs, rw_cells segs m A (c :: cs) ->
  rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs H. destruct (v01s_rwc_split m A [c] cs H) as [H1 H2].
  split; [exact H1|]. cbn [cells_size] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

(* v (20 bytes at A): parent [0, j), the NUL slot j, the rest of parent[16], vid at 16. *)
Lemma v01s_v4 : forall m A vb j, (j <= 15)%nat -> rw_cells segs m A [CB 20 vb] ->
  exists x1 x2 x3 x4, rw_cells segs m A [CB j x1] /\ rw_cells segs m (A + Z.of_nat j) [CB 1 x2] /\
    rw_cells segs m (A + Z.of_nat j + 1) [CB (15 - j) x3] /\ rw_cells segs m (A + 16) [CB 4 x4].
Proof.
  intros m A vb j Hj VB.
  pose proof (rw_cells_split_CB segs m A [] 20 vb [] [j; 1; 15 - j; 4]%nat VB) as H.
  specialize (H ltac:(cbn [sum_nat]; lia)).
  cbn [app mk_CB_cells] in H.
  destruct (v01s_rwc_cons _ _ _ _ H) as [P1 H1].
  destruct (v01s_rwc_cons _ _ _ _ H1) as [P2 H2].
  destruct (v01s_rwc_cons _ _ _ _ H2) as [P3 P4].
  cbn [csize] in P2, P3, P4.
  do 4 eexists. split; [exact P1|]. split; [exact P2|]. split.
  - eapply v01s_rwc_eq; [exact P3 | lia].
  - eapply v01s_rwc_eq; [exact P4 | lia].
Qed.

Lemma v01s_v4m : forall m A j src x3 w, rw_cells segs m A [CB j src] ->
  rw_cells segs m (A + Z.of_nat j) [C1 ZERO] -> rw_cells segs m (A + Z.of_nat j + 1) [CB (15 - j) x3] ->
  rw_cells segs m (A + 16) [C4 w] -> (j <= 15)%nat ->
  rw_cells segs m A [CB 20 (cells_bytes [CB j src; C1 ZERO; CB (15 - j) x3; C4 w])].
Proof.
  intros m A j src x3 w P1 P2 P3 P4 Hj.
  assert (H34 : rw_cells segs m (A + Z.of_nat j + 1) ([CB (15 - j) x3] ++ [C4 w])).
  { apply v01s_rwc_merge; [exact P3|]. eapply v01s_rwc_eq; [exact P4|]. cbn [cells_size csize]. lia. }
  assert (H234 : rw_cells segs m (A + Z.of_nat j) ([C1 ZERO] ++ [CB (15 - j) x3] ++ [C4 w])).
  { apply v01s_rwc_merge; [exact P2|]. eapply v01s_rwc_eq; [exact H34|]. cbn [cells_size csize]. lia. }
  assert (H1234 : rw_cells segs m A ([CB j src] ++ [C1 ZERO] ++ [CB (15 - j) x3] ++ [C4 w])).
  { apply v01s_rwc_merge; [exact P1|]. eapply v01s_rwc_eq; [exact H234|]. cbn [cells_size csize]. lia. }
  assert (E : cells_size [CB j src; C1 ZERO; CB (15 - j) x3; C4 w] = 20%nat) by (cbn [cells_size csize]; lia).
  pose proof (rw_cells_merge segs m A [] [CB j src; C1 ZERO; CB (15 - j) x3; C4 w] [] H1234) as H.
  rewrite E in H. exact H.
Qed.

(* The mask cell 0x28(sp) of main's frame. *)
Lemma v01s_frame_mask : forall m A w00 w08 w10 w18 w20 w28 w30 w38 w3c,
  rw_cells segs m A [C8 w00; C8 w08; C8 w10; C8 w18; C8 w20; C8 w28; C8 w30; C4 w38; C4 w3c] ->
  bytes_at segs m (A + 40) (le8 w28).
Proof.
  intros m A w00 w08 w10 w18 w20 w28 w30 w38 w3c [[_ H] _].
  cbn [cells_bytes cbytes] in H.
  apply bytes_at_app in H as [_ H]. apply bytes_at_app in H as [_ H]. apply bytes_at_app in H as [_ H].
  apply bytes_at_app in H as [_ H]. apply bytes_at_app in H as [_ H]. apply bytes_at_app in H as [H _].
  rewrite !length_le8 in H. eapply v01s_ba_eq; [exact H | lia].
Qed.

Lemma v01s_sub1 : forall lo hi lo' hi', lo' <= lo -> hi <= hi' -> sub_fp [(lo, hi)] [(lo', hi')].
Proof.
  intros lo hi lo' hi' H1 H2 x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [|exact I].
  intros [A B]. apply Hx. split; lia.
Qed.

End Mem.

Lemma v01s_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  assert (E1 : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
  assert (E2 : bv_modulus 32 = 2 ^ 32) by reflexivity.
  unfold bv_swrap, bv_wrap. rewrite E1, E2. rewrite Z.mod_small by lia. lia.
Qed.

End V01SplitPure.

Import V01SplitPure.

(* ---- The invariants at the exits ---- *)
(* tab, mt and the stack below main's frame across a run that writes only [lo, hi) of the stack window. *)
Lemma v01s_low : forall inp S c mm tab mt m0 m m' T lo hi,
  v01_geo inp S c mm tab mt -> v01_mem inp S tab mt m0 m -> v01_mt inp mt T m ->
  munch [(lo, hi)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 65536) (S - 208) ->
  S - 65536 <= lo -> hi <= S - 104 ->
  v01_mem inp S tab mt m0 m' /\ v01_mt inp mt T m'.
Proof.
  intros inp S c mm tab mt m0 m m' T lo hi GEO MEM MT MU WM MI ST Hlo Hhi.
  destruct MEM as (MU0 & WM0 & _ & _ & (bt & BT & ET) & (fr & FR) & GD).
  destruct MT as (LT & (bm & BM & EM) & (fm & FM)).
  pose proof GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & HtS & _ & _ & Hm & HmS & _).
  pose proof (mb_cap inp) as Hcap.
  pose proof (vlan_init_len (seg_pay inp) (proj1 Hcap)) as Hn0.
  pose proof (proj1 ET) as LBT. pose proof (proj1 EM) as LBM.
  assert (LG : length GUARD_BYTES = 18%nat) by reflexivity.
  assert (SUB : sub_fp [(lo, hi)] (v01_W inp S tab mt)).
  { intros x Hx. unfold v01_W in Hx. cbn [outside] in Hx |- *. destruct Hx as [Hx _]. split; [|exact I].
    intros [Hx1 Hx2]. apply Hx. split; lia. }
  unfold guard_at in GD.
  unfold TAB_N, MT_N, RVLAN_SIZE, MVLAN_SIZE in *. unfold v_cap, v_n0, v_tab0, seg_tab0, seg_cap in *.
  split.
  - split; [exact (munch_trans _ _ _ _ MU0 (munch_weaken _ _ _ _ SUB MU))|].
    split; [exact (wmono_trans rsegs _ _ _ WM0 WM)|].
    split; [exact MI|]. split; [exact ST|].
    split.
    { exists bt. split; [|exact ET].
      apply (bytes_at_transport rsegs [(lo, hi)] m m') in BT; [exact BT | exact MU |].
      cbn [disjoint_from]. split; [left; lia | exact I]. }
    split.
    { exists fr. apply (rw_cells_transport rsegs [(lo, hi)] m m') in FR; [exact FR | exact MU | exact WM |].
      cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [left; lia | exact I]. }
    apply (bytes_at_transport rsegs [(lo, hi)] m m') in GD; [exact GD | exact MU |].
    cbn [disjoint_from]. rewrite LG. split; [left; lia | exact I].
  - split; [exact LT|]. split.
    { exists bm. split; [|exact EM].
      apply (bytes_at_transport rsegs [(lo, hi)] m m') in BM; [exact BM | exact MU |].
      cbn [disjoint_from]. split; [left; lia | exact I]. }
    exists fm. apply (rw_cells_transport rsegs [(lo, hi)] m m') in FM; [exact FM | exact MU | exact WM |].
    cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [left; lia | exact I].
Qed.

(* JOIN: the memory of LOOP carried across a run that writes only [lo, hi) below main's frame. *)
Lemma v01s_join_mem : forall inp S c mm tab mt m0 i T added m m' lo hi,
  v01_geo inp S c mm tab mt -> v01_loop_mem inp S c tab mt m0 i i T added m ->
  v01_model inp (Nat.succ i) T added ->
  munch [(lo, hi)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 65536) (S - 208) ->
  S - 65536 <= lo -> hi <= S - 208 ->
  v01_loop_mem inp S c tab mt m0 i (Nat.succ i) T added m'.
Proof.
  intros inp S c mm tab mt m0 i T added m m' lo hi GEO (Hi & _ & MEM & MT & (w00 & w08 & w38 & FR) & (vb & VB))
    MOD MU WM MI ST Hlo Hhi.
  destruct (v01s_low inp S c mm tab mt m0 m m' T lo hi GEO MEM MT MU WM MI ST Hlo ltac:(lia)) as [MEM' MT'].
  unfold v01_frame in FR.
  split; [exact Hi|]. split; [exact MOD|]. split; [exact MEM'|]. split; [exact MT'|].
  split.
  - exists w00, w08, w38. unfold v01_frame.
    apply (rw_cells_transport rsegs [(lo, hi)] m m') in FR; [exact FR | exact MU | exact WM |].
    cbn [disjoint_from]. split; [right; lia | exact I].
  - exists vb. apply (rw_cells_transport rsegs [(lo, hi)] m m') in VB; [exact VB | exact MU | exact WM |].
    cbn [disjoint_from]. split; [right; lia | exact I].
Qed.

(* ADD: the memory of LOOP carried across the stack window, main's frame and v as SPLIT leaves them. *)
Lemma v01s_add_mem : forall inp S c mm tab mt m0 i T added p vid m m' w00 w38 vb,
  v01_geo inp S c mm tab mt -> v01_loop_mem inp S c tab mt m0 i i T added m ->
  ms_ignore (nth i (v_segs inp) mseg_d) = false -> m_split (ms_name (nth i (v_segs inp) mseg_d)) = Some (p, vid) ->
  munch [(S - 65536, S - 104)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 65536) (S - 208) ->
  v01_frame S w00 (Z_to_bv 64 tab) (Z_to_bv 64 (v_cap inp)) (Z_to_bv 64 added) (Z_to_bv 64 mt)
    (Z_to_bv 64 V01_MASK) (Z_to_bv 64 c) w38 (Z_to_bv 64 (v_n0 inp)) m' ->
  rw_cells rsegs m' (S - 208 + 64) [CB 20 vb] -> mvlan_enc (p, vid) vb ->
  v01_add_mem inp S c tab mt m0 i T added p vid m'.
Proof.
  intros inp S c mm tab mt m0 i T added p vid m m' w00 w38 vb GEO (Hi & MOD & MEM & MT & _ & _) Hig Hsp
    MU WM MI ST FR VB Henc.
  destruct (v01s_low inp S c mm tab mt m0 m m' T (S - 65536) (S - 104) GEO MEM MT MU WM MI ST
              ltac:(lia) ltac:(lia)) as [MEM' MT'].
  split; [exact Hi|]. split; [exact MOD|]. split; [exact Hig|]. split; [exact Hsp|].
  split; [exact MEM'|]. split; [exact MT'|]. split; [exists w00, w38; exact FR|].
  exists vb. split; assumption.
Qed.

Lemma v01s_model_step : forall inp i T added, (i < length (v_segs inp))%nat -> v01_model inp i T added ->
  (ms_ignore (nth i (v_segs inp) mseg_d) = true \/ m_split (ms_name (nth i (v_segs inp) mseg_d)) = None) ->
  v01_model inp (Nat.succ i) T added.
Proof.
  intros inp i T added Hi [H1 H2] Hc. split; [exact H1|].
  exact (v01s_model_skip _ _ _ _ i _ Hi H2 Hc).
Qed.

Ltac v01s_dead K := exfalso; zify_cond K; first [ discriminate K | lia ].

(* ---- SPLIT ---- *)
Lemma v01_split : strrchr_contract -> memcpy_contract -> v01_dig_stmt -> v01_par_stmt -> v01_split_stmt.
Proof.
  intros SR MC DIG PAR.
  unfold v01_split_stmt, K_loop_at.
  intros inp S c mm tab mt m0 gp tp F fc Q i GEO BASE KJ KA T added
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 m LM.
  unfold K_join_at in KJ. unfold K_add_at in KA.
  pose proof LM as (Hi & MOD & MEM & _ & FRM & VBX).
  pose proof MEM as (MU0 & _ & MI & ST & _).
  pose proof GEO as (HS16 & HSlo & HShi & _ & _ & _ & _ & _ & Hm4096 & HmS & Hm16 & _ & _ & _ & _ & _ & _ & _ &
                     _ & _ & _ & _ & _ & Atab & Amt & _).
  destruct BASE as (_ & (bsm & BM0 & EM) & _ & _).
  assert (BM : bytes_at rsegs m mm bsm).
  { apply (bytes_at_transport rsegs (v01_W inp S tab mt) m0 m) in BM0; [exact BM0 | exact MU0 |].
    pose proof (proj1 EM) as LB. unfold v01_W. cbn [disjoint_from]. rewrite LB.
    split; [left; unfold SEG_M_SIZE in *; lia|]. split; [exact Amt|]. split; [exact Atab | exact I]. }
  clear BM0 Atab Amt.
  unfold SEG_M_SIZE in HmS.
  pose proof (proj1 (proj2 EM)) as N32.
  change (length (mc_seg (v_mc inp)) <= 32)%nat with (length (v_segs inp) <= 32)%nat in N32.
  assert (Hi32 : Z.of_nat i < 32) by lia.
  destruct (v01s_name rsegs m mm bsm (v_mc inp) i BM EM Hi) as (sx & slack & NB & Hzs & NZ & Lss & RD).
  clear BM EM bsm.
  change (mc_seg (v_mc inp)) with (v_segs inp) in Hzs, RD.
  destruct FRM as (w00 & w08 & w38 & FR). unfold v01_frame in FR.
  destruct VBX as (vb & VB).
  unfold v01_loop_st, vst.
  (* 0x13d64 slli s7,s2,8 ; 0x13d68 add s7,s0,s7: s7 = m + 256 i *)
  zstep.
  match goal with |- context [Z_to_bv 64 (Z.shiftl ?x 8)] =>
    replace (Z_to_bv 64 (Z.shiftl x 8)) with (Z_to_bv 64 (256 * Z.of_nat i))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256;
          first [lia | rewrite Z.mod_small by lia; lia]) end.
  zstep.
  revert RD. destruct (ms_ignore (nth i (v_segs inp) mseg_d)) eqn:Hig; intros RD; cbv beta iota in RD.
  - (* ignored: 0x13d6c lw a0,0x18(s7) = 1 ; 0x13d70 beqz falls to JOIN *)
    zstep. rewrite (v01s_sx32 1) by lia.
    zstep. if_cases K1; [v01s_dead K1|]. clear K1.
    eapply (KJ T added).
    eapply v01s_join_mem; [exact GEO | exact LM | | exact (munch_refl [(S - 240, S - 208)] m) |
                           exact (wmono_refl rsegs m) | exact MI | exact ST | lia | lia].
    apply (v01s_model_step inp i T added Hi MOD). left. exact Hig.
  - (* 0x13d6c lw a0,0x18(s7) = 0 ; 0x13d70 beqz -> 0x13d88 *)
    zstep. rewrite (v01s_sx32 0) by lia.
    zstep. if_cases K1; [|v01s_dead K1]. clear K1.
    (* 0x13d88 li a1,0x2e ; 0x13d8c mv a0,s7 ; 0x13d90 jal strrchr *)
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SR with (str := sx) (slack := slack) (lo := S - 65536).
      - rewrite unsigned_lit by lia. exact NB.
      - exact NZ.
      - rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia.
      - exact MI.
      - rewrite unsigned_lit by lia. exact ST.
      - unfold STRRCHR_K. rewrite unsigned_lit by lia. lia.
      - left. unfold STRRCHR_K. rewrite !unsigned_lit by lia. lia. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
                MU1 & WM1 & MI1 & ST1 & NB1).
    rewrite (unsigned_lit (mm + 256 * Z.of_nat i)) in NB1 |- * by lia.
    rewrite (unsigned_lit (S - 208)) in MU1, ST1 by lia.
    unfold STRRCHR_K in MU1.
    rewrite ret_pc_even by (try lia; reflexivity).
    apply (rw_cells_transport rsegs [(S - 208 - 32, S - 208)] m m1) in FR;
      [| exact MU1 | exact WM1 | cbn [disjoint_from]; split; [right; lia | exact I]].
    apply (rw_cells_transport rsegs [(S - 208 - 32, S - 208)] m m1) in VB;
      [| exact MU1 | exact WM1 | cbn [disjoint_from]; split; [right; lia | exact I]].
    destruct (rfind_byte 46 sx) as [j|] eqn:Hrf.
    + (* the last dot at name + j *)
      rewrite (v01s_res_some _ _ _ _ Hrf) by reflexivity.
      destruct (rfind_byte_Some _ _ _ Hrf) as (Hj & _ & _).
      assert (Hj14 : (j <= 14)%nat) by lia.
      (* 0x13d94 beqz a0 *)
      zstep. if_cases K2; [v01s_dead K2|]. clear K2.
      (* 0x13d98 beq a0,s7 *)
      zstep. if_cases K3.
      * (* dot == name: JOIN *)
        zify_cond K3. assert (Ej : j = 0%nat) by lia. subst j.
        eapply (KJ T added).
        eapply v01s_join_mem; [exact GEO | exact LM | | exact MU1 | exact WM1 | exact MI1 | exact ST1 | lia | lia].
        apply (v01s_model_step inp i T added Hi MOD). right. rewrite <- Hzs. exact (v01s_split_none_j0 sx NZ Hrf).
      * zify_cond K3. assert (Hj0 : j <> 0%nat) by lia. clear K3.
        pose proof (v01s_rd_field rsegs m1 _ sx slack (Nat.succ j) NB1 Hj) as RD2.
        replace (mm + 256 * Z.of_nat i + Z.of_nat (Nat.succ j)) with (mm + 256 * Z.of_nat i + Z.of_nat j + 1)
          in RD2 by (rewrite Nat2Z.inj_succ; unfold Z.succ; lia).
        pose proof (v01s_hd0 sx slack (Nat.succ j) Hj) as Hh.
        remember (nth (Nat.succ j) (sx ++ ZERO :: slack) ZERO) as b1 eqn:Hb1.
        try rewrite <- Hb1 in Hh. try rewrite <- Hb1 in RD2.
        pose proof (v01s_byte_rng b1) as Rb1.
        (* 0x13d9c lbu a2,1(a0) ; 0x13da0 li a4,10 ; 0x13da4 beqz a2 *)
        zstep. clear RD2. zstep. zstep. if_cases K4.
        -- (* dot[1] = NUL: JOIN *)
           zify_cond K4.
           eapply (KJ T added).
           eapply v01s_join_mem; [exact GEO | exact LM | | exact MU1 | exact WM1 | exact MI1 | exact ST1 | lia | lia].
           apply (v01s_model_step inp i T added Hi MOD). right. rewrite <- Hzs.
           apply (v01s_split_none_hd sx j NZ Hrf). exact (eq_trans Hh K4).
        -- zify_cond K4.
           assert (Hj2 : (Nat.succ j < length sx)%nat).
           { apply (v01s_nz_lt sx slack (Nat.succ j) Hj). rewrite <- Hb1. exact K4. }
           assert (HD : skipn (Nat.succ j) (zs sx) = bv_unsigned b1 :: zs (skipn (Nat.succ (Nat.succ j)) sx)).
           { rewrite Hb1. apply v01s_digits_in. exact Hj2. }
           (* 0x13da8 li s5,0 ; 0x13dac addi a1,a0,2 *)
           zstep. zstep.
           (* 0x13db0: the digit loop *)
           eapply (DIG Q m1 (skipn (Nat.succ (Nat.succ j)) sx) (bv_unsigned b1) 0
                     (mm + 256 * Z.of_nat i + Z.of_nat j + 2)).
           ++ lia.
           ++ lia.
           ++ lia.
           ++ eapply v01s_ba_eq; [exact (v01s_ba_suf rsegs m1 _ sx slack (Nat.succ (Nat.succ j)) NB1 Hj2) |].
              rewrite !Nat2Z.inj_succ. unfold Z.succ. lia.
           ++ apply v01s_nin_skipn. exact NZ.
           ++ (* m_digits refuses: JOIN *)
              intros Hd a1x a2x a3x s5x.
              rewrite <- HD in Hd.
              eapply (KJ T added).
              eapply v01s_join_mem; [exact GEO | exact LM | | exact MU1 | exact WM1 | exact MI1 | exact ST1 |
                                     lia | lia].
              apply (v01s_model_step inp i T added Hi MOD). right. rewrite <- Hzs.
              apply (v01s_split_none_dig sx j NZ Hrf). exact Hd.
           ++ intros v Hd a1x a2x a3x.
              rewrite <- HD in Hd.
              pose proof (v01s_digits_rng _ 0 v ltac:(lia) Hd) as Hv.
              unfold vst.
              (* 0x13dd4 beqz s5 *)
              zstep. if_cases K5.
              ** (* vid = 0: JOIN *)
                 zify_cond K5.
                 eapply (KJ T added).
                 eapply v01s_join_mem; [exact GEO | exact LM | | exact MU1 | exact WM1 | exact MI1 | exact ST1 |
                                        lia | lia].
                 apply (v01s_model_step inp i T added Hi MOD). right. rewrite <- Hzs.
                 apply (v01s_split_none_v0 sx j v NZ Hrf Hd). lia.
              ** zify_cond K5. assert (Hv1 : 1 <= v) by lia. clear K5.
                 (* 0x13dd8 sub a2,a0,s7: pn = j *)
                 zstep.
                 match goal with |- context [Z_to_bv 64 (?x - (mm + 256 * Z.of_nat i))] =>
                   replace (Z_to_bv 64 (x - (mm + 256 * Z.of_nat i))) with (Z_to_bv 64 (Z.of_nat j))
                     by (f_equal; lia) end.
                 (* 0x13ddc add a0,a0,s9 *)
                 zstep.
                 match goal with |- context [Z_to_bv 64 (?x + - (mm + 256 * Z.of_nat i))] =>
                   replace (Z_to_bv 64 (x + - (mm + 256 * Z.of_nat i))) with (Z_to_bv 64 (Z.of_nat j))
                     by (f_equal; lia) end.
                 (* 0x13de0 seqz a1,a0 *)
                 zstep.
                 match goal with |- context [Z.b2z ?cnd] =>
                   replace cnd with false by (symmetry; apply Z.ltb_ge; lia) end.
                 (* 0x13de4 add a0,a0,a1 *)
                 zstep.
                 match goal with |- context [Z_to_bv 64 (Z.of_nat j + ?y)] =>
                   replace (Z_to_bv 64 (Z.of_nat j + y)) with (Z_to_bv 64 (Z.of_nat j))
                     by (f_equal; cbn [Z.b2z]; lia) end.
                 (* 0x13de8 mv a1,s1 *)
                 zstep.
                 (* 0x13dec: the parent loop *)
                 eapply (PAR Q m1 (firstn j sx) (Z.of_nat j) (mm + 256 * Z.of_nat i) (S - 208)).
                 --- rewrite length_firstn, Nat.min_l by lia. reflexivity.
                 --- lia.
                 --- lia.
                 --- lia.
                 --- exact (v01s_ba_pre rsegs m1 _ sx slack j NB1 (Nat.lt_le_incl _ _ Hj)).
                 --- exact (v01s_frame_mask rsegs m1 (S - 208) _ _ _ _ _ _ _ _ _ FR).
                 --- (* a character that is not a parent character: JOIN *)
                     intros Hp a0x a1y a3y a4y a5y.
                     eapply (KJ T added).
                     eapply v01s_join_mem; [exact GEO | exact LM | | exact MU1 | exact WM1 | exact MI1 |
                                            exact ST1 | lia | lia].
                     apply (v01s_model_step inp i T added Hi MOD). right. rewrite <- Hzs.
                     apply (v01s_split_none_par sx j v NZ Hrf Hd). rewrite v01s_firstn_zs. exact Hp.
                 --- intros Hp a0x a1y a3y a4y a5y.
                     unfold vst.
                     pose proof (munch_weaken _ _ m m1 (v01s_sub1 (S - 208 - 32) (S - 208) (S - 65536) (S - 104)
                                   ltac:(lia) ltac:(lia)) MU1) as MUl.
                     destruct (v01s_v4 rsegs m1 _ vb j ltac:(lia) VB) as (x1 & x2 & x3 & x4 & VBp & VBn & VBr & VBv).
                     apply (v01s_rwc_eq rsegs m1 _ (S - 208 + 80)) in VBv; [| lia].
                     pose proof (v01s_ba_pre rsegs m1 _ sx slack j NB1 (Nat.lt_le_incl _ _ Hj)) as SRC.
                     assert (Lsrc : length (firstn j sx) = j) by (rewrite length_firstn; lia).
                     clear MU1 VB NB1.
                     (* 0x13e40 sd s3,8(sp) *)
                     zstep.
                     lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) => rename M into M2 end.
                     (* 0x13e44 addi a0,sp,0x40 ; 0x13e48 mv a1,s7 ; 0x13e4c mv s3,a2 ; 0x13e50 jal memcpy *)
                     zstep. zstep. zstep. zstep.
                     eapply evt_cut.
                     { eapply MC with (src := firstn j sx) (junk := x1).
                       - rewrite unsigned_lit by lia. exact SRC.
                       - rewrite unsigned_lit by lia. rewrite Nat2Z.id. exact Lsrc.
                       - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact VBp.
                       - rewrite !unsigned_lit by lia. left. lia.
                       - assumption. }
                     intros ms' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & M3 & -> &
                                 MU3 & WM3 & MI3 & VP3 & SRC3).
                     rewrite !unsigned_lit in MU3, VP3 by lia. rewrite Nat2Z.id in VP3.
                     rewrite ret_pc_even by (try lia; reflexivity).
                     pose proof (munch_trans _ _ _ _ MUl (munch_weaken _ _ _ _
                                   (v01s_sub1 (S - 208 + 64) (S - 208 + 64 + Z.of_nat j) (S - 65536) (S - 104)
                                      ltac:(lia) ltac:(lia)) MU3)) as MUl3.
                     apply (rw_cells_transport rsegs [(S - 208 + 64, S - 208 + 64 + Z.of_nat j)] M2 M3) in FR;
                       [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; split; [left; lia | exact I]].
                     apply (rw_cells_transport rsegs [(S - 208 + 64, S - 208 + 64 + Z.of_nat j)] M2 M3) in VBn;
                       [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; split; [right; lia | exact I]].
                     apply (rw_cells_transport rsegs [(S - 208 + 64, S - 208 + 64 + Z.of_nat j)] M2 M3) in VBr;
                       [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; split; [right; lia | exact I]].
                     apply (rw_cells_transport rsegs [(S - 208 + 64, S - 208 + 64 + Z.of_nat j)] M2 M3) in VBv;
                       [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; split; [right; lia | exact I]].
                     apply (stk_transport_disjoint rsegs [(S - 208 + 64, S - 208 + 64 + Z.of_nat j)] M2 M3) in ST1;
                       [| exact MU3 | exact WM3 | cbn [disjoint_from]; split; [left; lia | exact I]].
                     pose proof (wmono_trans rsegs _ _ _ WM1 WM3) as WM13.
                     clear MUl WM1 MU3 WM3 MI1 VBp SRC SRC3.
                     rename MUl3 into MUl. rename WM13 into WM1. rename MI3 into MI1.
                     try clear M2.
                     (* 0x13e54 addi a0,sp,0x40 ; 0x13e58 add a0,a0,s3 *)
                     zstep. zstep.
                     (* 0x13e5c sb zero,0(a0): v.parent[pn] = 0 *)
                     assert (HS : store_ok rsegs M3 (wa (S - 208 + 64 + Z.of_nat j)) 1 = true).
                     { apply (rw_cells_store_ok_at rsegs M3 _ [CB 1 x2] 0%nat (CB 1 x2) 1%nat _ VBn);
                         [reflexivity | reflexivity | unfold wa; f_equal; lia]. }
                     zstep.
                     replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
                     pose proof (rw_cells_write rsegs M3 _ [CB 1 x2] 0%nat (CB 1 x2) (C1 ZERO) VBn eq_refl eq_refl I)
                       as NEW.
                     cbn [cbytes cell_upd Nat.eqb] in NEW. change (Z.of_nat 0) with 0 in NEW.
                     rewrite Z.add_0_r in NEW.
                     clear VBn.
                     store_done.
                     (* 0x13e60 sw s5,0x50(sp): v.vid = vid *)
                     zstep.
                     (* 0x13e64: ADD *)
                     assert (Lx3 : length x3 = (15 - j)%nat) by (pose proof VBr as [[[L3 _] _] _]; exact L3).
                     eapply (KA T added (firstn j (zs sx)) v).
                     eapply v01s_add_mem; [exact GEO | exact LM | exact Hig | | eassumption | eassumption |
                                           eassumption | eassumption | exact FR | | ].
                     +++ rewrite <- Hzs. apply v01s_split_some; [exact NZ | exact Hrf | exact Hj0 | | exact Hd |
                                                                 exact Hv1 | rewrite v01s_firstn_zs; exact Hp].
                         exact (fun E => K4 (eq_trans (eq_sym Hh) E)).
                     +++ eapply v01s_v4m; [exact VP3 | exact NEW | exact VBr | eapply v01s_rwc_eq; [exact VBv | lia] |
                                           lia].
                     +++ rewrite v01s_firstn_zs. apply v01s_mvlan; [apply v01s_nin_firstn; exact NZ |
                                                                    rewrite Lsrc, Lx3; lia | lia].
    + (* no dot: JOIN *)
      rewrite (v01s_res_none _ _ _ Hrf) by reflexivity.
      zstep. if_cases K2; [|v01s_dead K2]. clear K2.
      eapply (KJ T added).
      eapply v01s_join_mem; [exact GEO | exact LM | | exact MU1 | exact WM1 | exact MI1 | exact ST1 | lia | lia].
      apply (v01s_model_step inp i T added Hi MOD). right. rewrite <- Hzs. exact (v01s_split_none_rf sx NZ Hrf).
Qed.
