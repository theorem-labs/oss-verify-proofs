(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its addresses changed; 578 of its 650 lines of code are new or changed and 1157 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/relay_event_b.v, with its module paths, module names and numbers changed; 746 of its 838 lines of code are new or changed and 558 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import
  pthread_mutex_lock_c pthread_mutex_unlock_c memset_c wake_c relay_add_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c relay_event_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_add_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ra_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sgn64 : forall w : word, Z_to_bv 64 (bv_signed w) = w.
Proof.
  intros w. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus in *. change (bv_modulus 64) with (2 ^ 64) in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ret_pc_of_ok : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
  pose proof (bv_unsigned_in_range 64 k) as R. unfold bv_modulus in R.
  assert (T : Z.testbit (bv_unsigned k) 0 = false).
  { rewrite <- H at 1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec. apply Bool.andb_false_r. }
  assert (E : bv_unsigned k mod 2 = 0) by (rewrite Zmod_odd, <- Z.bit0_odd, T; reflexivity).
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [exact R | exact E].
Qed.

Lemma munch_mbyte : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  mbyte segs m' a = mbyte segs m a.
Proof.
  intros segs W m m' a H R O. unfold mbyte. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma munch_writable : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros segs W m m' a H R O. unfold writable_at, wview. rewrite (H (Z_to_bv 64 a)); [tauto|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma munch_present : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  present m a -> present m' a.
Proof.
  intros W m m' a H R O [b E]. exists b. rewrite (H (Z_to_bv 64 a)); [exact E|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); [right; lia | left; split; [lia|exact H] ..].
Qed.

Lemma not_outside_cons : forall lo hi W x, ~ outside ((lo, hi) :: W) x -> (lo <= x < hi) \/ ~ outside W x.
Proof.
  intros lo hi W x H. cbn [outside] in H.
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi);
    [left; lia | right; intros O; apply H; split; [lia | exact O] ..].
Qed.

Ltac nout O :=
  repeat match type of O with
  | ~ outside ((_, _) :: _) _ => apply not_outside_cons in O; destruct O as [O|O]
  | ~ outside [] _ => exfalso; apply O; exact I
  end.

Lemma find_segment_none_above : forall segs top a n,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true -> top <= a -> 0 < n ->
  find_segment segs a n = None.
Proof.
  induction segs as [|s segs IH]; intros top a n H Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - apply IH with top; assumption.
Qed.

Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. lia.
  - destruct (IH a n seg H) as (Hi & H1 & H2). split; [right; exact Hi|]. lia.
Qed.

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 20) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_res_top :
  forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 21) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma writable_hi_present : forall m a, 2 ^ 20 <= a < 2 ^ 64 -> writable_at rsegs m a -> present m a.
Proof.
  intros m a Ha. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite unsigned_lit by lia.
  rewrite (find_segment_none_above rsegs (2 ^ 20) a 1 rsegs_top) by lia.
  intros W. exfalso. apply W. reflexivity.
Qed.

Lemma ro_hi : forall a, 2 ^ 20 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
  rewrite (find_segment_none_above rsegs (2 ^ 20) a 1 rsegs_top) by lia. reflexivity.
Qed.

Lemma ro_glob : forall a, 0x318a0 <= a < 0x31920 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha.
  assert (C : forallb (fun i => negb (ro_addr rsegs (wa (0x318a0 + Z.of_nat i)))) (seq 0 128) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat (a - 0x318a0))).
  rewrite Z2Nat.id in C by lia. replace (0x318a0 + (a - 0x318a0)) with a in C by lia.
  apply negb_true_iff. apply C. apply in_seq. lia.
Qed.

Lemma present_writable : forall segs m a, present m a -> writable_at segs m a.
Proof. intros segs m a [b E]. unfold writable_at, wview. rewrite E. discriminate. Qed.

Lemma nth_error_seq_lt : forall s k i, (i < k)%nat -> nth_error (seq s k) i = Some (s + i)%nat.
Proof.
  intros s k. revert s. induction k as [|k IH]; intros s i Hi; [lia|].
  destruct i as [|i]; cbn; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma present_rw_cells : forall segs m a (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> present m (a + i)) ->
  exists junk, rw_cells segs m a [CB k junk].
Proof.
  intros segs m a k Ha Hk H.
  exists (map (fun i => match m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  assert (L : length (map (fun i => match m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
                         (seq 0 k)) = k) by (rewrite length_map, length_seq; reflexivity).
  split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact Ha|]. split; [rewrite L; exact Hk|].
    intros i Hi. rewrite L in Hi.
    destruct (H (Z.of_nat i) ltac:(lia)) as [b E].
    rewrite (map_nth_error _ _ _ (nth_error_seq_lt 0 k i Hi)). cbn [Nat.add].
    unfold mrd. unfold wa. rewrite E. reflexivity.
  - split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct (H i ltac:(lia)) as [b E]. unfold wview, wa. rewrite E. discriminate.
Qed.

Lemma bytes_at_transfer : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) E. split; [exact H1|]. split; [exact H2|].
  intros i Hi. change (mbyte segs m' (a + Z.of_nat i) = nth_error bs i).
  rewrite E by lia. exact (H i Hi).
Qed.

Lemma rw_cells_transfer : forall segs m m' a cs, rw_cells segs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte segs m' (a + i) = mbyte segs m (a + i) /\
     (writable_at segs m (a + i) -> writable_at segs m' (a + i))) ->
  rw_cells segs m' a cs.
Proof.
  intros segs m m' a cs [[Hwf Hb] (Ha & Hn & Hw)] E.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - apply (bytes_at_transfer segs m); [exact Hb|]. intros i Hi. apply E. rewrite <- L. exact Hi.
  - split; [exact Ha|]. split; [exact Hn|]. intros i Hi. apply (proj2 (E i Hi)). exact (Hw i Hi).
Qed.

Lemma rw_writable : forall segs m A cs x, rw_cells segs m A cs -> A <= x < A + Z.of_nat (cells_size cs) ->
  writable_at segs m x.
Proof.
  intros segs m A cs x [_ (H1 & H2 & H)] Hx. replace x with (A + (x - A)) by lia. apply H. lia.
Qed.

Lemma rw_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs RO [[W B] Wr] H. split; [split; [exact W|]|].
  - apply bytes_at_normalize; assumption.
  - eapply wr_at_norm; [apply mem_rel_normalize; exact RO | exact Wr | exact H].
Qed.

Lemma rw_back : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[W B] Wr]. split; [split; [exact W|]|].
  - apply (proj2 (bytes_at_rel rsegs m m0 A _ HR)). exact B.
  - exact (wr_at_rel rsegs m m0 A _ HR Wr).
Qed.

Lemma stk_norm : forall m lo hi, ro_agree rsegs m -> stk rsegs m lo hi -> 2 ^ 20 <= lo ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RO (H1 & H2 & H) Hlo. pose proof (mem_rel_normalize rsegs m RO) as HR.
  split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [W [b E]].
  split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ HR (ro_hi a ltac:(lia))). exact W.
  - exists b. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ HR). exact E.
Qed.

Lemma stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [W [b E]].
  split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ HR (ro_false_of_wview rsegs m m0 _ HR W)). exact W.
  - exists b. rewrite (mrd_rel rsegs m m0 _ HR). exact E.
Qed.

Lemma cb_split2 : forall m A n1 n2 b, rw_cells rsegs m A [CB (n1 + n2) b] ->
  rw_cells rsegs m A [CB n1 (firstn n1 b)] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 (skipn n1 b)].
Proof.
  intros m A n1 n2 b H.
  assert (LB : length b = (n1 + n2)%nat) by (destruct H as [[W _] _]; cbn in W; tauto).
  apply (rw_cells_split_CB rsegs m A [] (n1 + n2) b [] [n1; n2]) in H; [|cbn; lia].
  cbn [mk_CB_cells app] in H.
  destruct (ra_cut m A [_] [_] H) as [H1 H2].
  cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2.
  rewrite firstn_all2 in H2 by (rewrite length_skipn; lia).
  split; assumption.
Qed.

Lemma cb_join2 : forall m A n1 n2 b1 b2, rw_cells rsegs m A [CB n1 b1] ->
  rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2] -> rw_cells rsegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  assert (J : rw_cells rsegs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply (ra_join m A (A + Z.of_nat n1)); [exact H1 | exact H2 |].
    cbn [cells_size csize]. rewrite Nat.add_0_r. reflexivity. }
  apply (rw_cells_merge rsegs m A [] [CB n1 b1; CB n2 b2] []) in J.
  cbn [cells_size csize cells_bytes cbytes app] in J. rewrite Nat.add_0_r, app_nil_r in J. exact J.
Qed.

Section RA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis NODUP : blocks_nodup Bm API.

Lemma canon_mkst : forall regs pc mem rom,
  RegisterBridge.canonical_register_state (YK11.mkst regs pc mem rom) =
  MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem rom.
Proof using. reflexivity. Qed.

Lemma rel_eqv : forall R pc m0 ro can ms,
  ms_rel rsegs can (MS R fp_regs pc fp_csr None m0 ro) -> Regs6ss.ms_eqv can ms ->
  exists R' m', ms = YK11.mkst R' pc m' ro /\ Regs6ss.xregs_eqv R R' /\ mem_rel rsegs m' m0 /\ ms_mem can = m'.
Proof using.
  intros R pc m0 ro [r f p sv rv c mm o] [r2 f2 p2 sv2 rv2 c2 mm2 o2]
    (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8) (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. exists r2, mm2. split; [reflexivity|]. split; [exact H1|]. split; [exact E8 | reflexivity].
Qed.

Lemma getr_of_eqv : forall M R (r : bv 5), Regs6ss.xregs_eqv M R -> bv_eqb r 0 = false -> getr R r = reg_get M r.
Proof using. intros M R r H NZ. unfold getr. rewrite NZ. symmetry. apply H. exact NZ. Qed.

Ltac geteqv X := etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; reflexivity.

Lemma pres_canon : forall regs R x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  Regs6ss.xregs_eqv (mkR x1 (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2 (reg_get regs 8)
    (reg_get regs 9) a0 a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
    (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
    (reg_get regs 27) t3 t4 t5 t6) R ->
  regs_preserved regs R.
Proof using.
  intros regs R x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 X r Hr. unfold callee_saved in Hr.
  assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
  rewrite (getr_of_eqv _ _ _ X NZ). unfold getr. rewrite NZ.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity.
Qed.

Lemma img_not_owned : forall L A mem md a, aa_MR API L A mem md -> img_plain Bm a -> ~ owned Bm L A a.
Proof using AX.
  intros L A mem md a HM (Hi & Hs & Hc & He) [Ho|Ho];
    [exact (Hc (ax_img AX L A mem md a HM Hi Ho)) | exact (Hs Ho)].
Qed.

Lemma in_img_of_seg : ms_segs Bm = rsegs -> forall a seg, 0 <= a -> find_segment rsegs a 1 = Some seg -> in_img Bm a.
Proof using.
  intros SEG a seg Ha F. destruct (find_segment_in _ _ _ _ F) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) rsegs_top seg Hin) as T. apply Z.leb_le in T.
  unfold in_img. rewrite SEG. split; [intro E; rewrite E in Hin; destruct Hin|].
  exists (segment_reservation seg). split; [apply in_map; exact Hin|].
  unfold segment_reservation, page_round_down_Z, page_round_up_Z. cbn [fst snd].
  change page_size with 4096.
  pose proof (N2Z.is_nonneg (seg_base seg)) as P1. pose proof (N2Z.is_nonneg (seg_size seg)) as P2.
  set (bs := Z.of_N (seg_base seg)) in *. set (sz := Z.of_N (seg_size seg)) in *.
  pose proof (Z.mul_div_le bs 4096 ltac:(lia)) as D1.
  pose proof (Z.div_pos bs 4096 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (bs + sz + 4096 - 1) 4096 ltac:(lia)) as D3.
  pose proof (Z.mul_succ_div_gt (bs + sz + 4096 - 1) 4096 ltac:(lia)) as D4.
  rewrite !unsigned_lit by lia. lia.
Qed.

Lemma in_img_low : ms_segs Bm = rsegs -> forall a, in_img Bm a -> 0 <= a < 2 ^ 21.
Proof using.
  intros SEG a (_ & s & Hin & H1 & H2). rewrite SEG in Hin.
  pose proof (proj1 (forallb_forall _ _) rsegs_res_top s Hin) as T. apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma ro_out : ms_segs Bm = rsegs -> forall a, 0 <= a < 2 ^ 64 -> ~ in_img Bm a -> ro_addr rsegs (wa a) = false.
Proof using.
  intros SEG a Ha NI. unfold ro_addr. rewrite wa_unsigned by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|reflexivity].
  exfalso. apply NI. exact (in_img_of_seg SEG a seg ltac:(lia) F).
Qed.

Lemma present_of_writable_out : ms_segs Bm = rsegs -> forall m a, 0 <= a < 2 ^ 64 -> ~ in_img Bm a ->
  writable_at rsegs m a -> present m a.
Proof using.
  intros SEG m a Ha NI. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite unsigned_lit by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F.
  - exfalso. apply NI. exact (in_img_of_seg SEG a seg ltac:(lia) F).
  - intros W. exfalso. apply W. reflexivity.
Qed.

Lemma owned_low' : forall L A mem md a, aa_MR API L A mem md -> owned Bm L A a -> 0 <= a < alloc_ceiling.
Proof using. intros L A mem md a HM Ho. exact (mr_owned_low Bm _ (aa_laws API) L A mem md a HM Ho). Qed.

Lemma block_facts : forall L A mem md q k i, aa_MR API L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  present mem (q + i) /\ 4096 <= q /\ q + k <= alloc_ceiling /\ ~ owned Bm L A (q + i).
Proof using.
  intros L A mem md q k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn in E. injection E as <- <-. exact (mr_blocks Bm _ (aa_laws API) L A mem md p k' i HM Hp Hi).
Qed.

Lemma pairwise_app_mid' : forall {X} (R : X -> X -> Prop) b1 x b2 y,
  pairwise R (b1 ++ x :: b2) -> In y (b1 ++ b2) -> R x y \/ R y x.
Proof using.
  intros X R b1. induction b1 as [|z b1 IH]; intros x b2 y HP Hin; cbn in *.
  - left. apply (proj1 HP). exact Hin.
  - destruct HP as [H1 H2]. destruct Hin as [<-|Hin].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH x b2 y H2 Hin).
Qed.

Lemma blocks_mid_disjoint : forall L A mem md b1 b2 d n q k, aa_MR API L A mem md ->
  blocks L A = b1 ++ (d, n) :: b2 -> In (q, k) (b1 ++ b2) -> q + k <= d \/ d + n <= q.
Proof using.
  intros L A mem md b1 b2 d n q k HM E Hin.
  pose proof (mr_blocks_disjoint Bm _ (aa_laws API) L A mem md HM) as P. rewrite E in P.
  destruct (pairwise_app_mid' _ _ _ _ _ P Hin) as [D|D]; unfold ranges_disjoint in D; cbn in D; lia.
Qed.

Lemma mr_munch : forall L A mem md W mem', ms_segs Bm = rsegs -> aa_MR API L A mem md -> munch W mem mem' ->
  (forall a, owned Bm L A a -> outside W a) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ outside W (ptr_addr L p + i) ->
     writable_at rsegs mem' (ptr_addr L p + i)) ->
  aa_MR API L A mem' md.
Proof using AX.
  intros L A mem md W mem' SEG HM MU OW BW.
  pose proof alloc_ceiling_lt as AC.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
  eapply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
  - intros a Ho. destruct (owned_low' _ _ _ _ a HM Ho). eapply munch_mbyte; [exact MU | lia | exact (OW a Ho)].
  - intros a Ho Hp. destruct (owned_low' _ _ _ _ a HM Ho).
    eapply munch_present; [exact MU | lia | exact (OW a Ho) | exact Hp].
  - intros p n i Hin Hi. destruct (mr_blocks Bm _ (aa_laws API) L A mem md p n i HM Hin Hi) as (Hp & H4 & Hc & _).
    destruct (outside_dec W (ptr_addr L p + i)) as [O|O].
    + eapply munch_present; [exact MU | lia | exact O | exact Hp].
    + apply (present_of_writable_out SEG mem' (ptr_addr L p + i)); [lia | | exact (BW p n i Hin Hi O)].
      exact (ax_blocks_img AX L A mem md p n i HM Hin Hi).
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hmat.
Qed.

Lemma post_nocall : forall K E L A regs mem md W mem' R1,
  ms_segs Bm = rsegs ->
  call_pre_k Bm (aa_MR API) K L A regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> (spZ regs - K <= x < spZ regs) \/ E x) ->
  (forall a, owned Bm L A a -> outside W a) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ outside W (ptr_addr L p + i) ->
     writable_at rsegs mem' (ptr_addr L p + i)) ->
  regs_preserved regs R1 ->
  relay_post Bm API K E (fun _ => False) L A regs mem md L A R1 mem' md.
Proof using AX.
  intros K E L A regs mem md W mem' R1 SEG PRE MU WM WS OW BW RP.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  pose proof alloc_ceiling_lt as AC.
  unfold relay_post. rewrite SEG in *.
  split; [exact (mr_munch L A mem md W mem' SEG HM MU OW BW)|].
  split; [exact HWF|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [lia|].
  split; [intros; reflexivity|].
  split; [intros p n Hp _ _; exact Hp|].
  split; [intros p Hp; split; [exact Hp | reflexivity]|].
  split; [intros a _ Ho; exact Ho|].
  split; [exact RP|].
  split; [exists (m_vmmaps md); apply YI04.with_vmmaps_self|].
  split.
  { intros a Hr Ho1 Ho2 Hs He.
    pose proof alloc_ceiling_val as ACV.
    assert (Ra : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low SEG a Hr); lia]).
    destruct (outside_dec W a) as [O|O].
    - split; [exact (munch_mbyte _ W mem mem' a MU Ra O) | exact (munch_writable _ W mem mem' a MU Ra O)].
    - exfalso. destruct (WS a Ra O) as [S|S]; [apply Hs; left; exact S | exact (He S)]. }
  split.
  { intros p n i Hp1 Hp2 _ Hi He.
    destruct (mr_blocks Bm _ (aa_laws API) _ _ _ _ p n i HM Hp1 Hi) as (_ & R1' & R2' & _).
    destruct (outside_dec W (ptr_addr L p + i)) as [O|O].
    - apply (munch_mbyte _ W); [exact MU | lia | exact O].
    - exfalso. destruct (WS (ptr_addr L p + i) ltac:(lia) O) as [S|S]; [lia | exact (He S)]. }
  intros a [Hs|Hs]; apply WM; [apply HWs | apply HWe]; exact Hs.
Qed.

Lemma fresh_disj : forall G lo hi, fresh_block Bm G 896 -> (forall a, lo <= a < hi -> img_plain Bm a) -> lo < hi ->
  G + 896 <= lo \/ hi <= G.
Proof using.
  intros G lo hi (F1 & F2 & F3) P Hlh.
  destruct (Z_le_gt_dec (G + 896) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi G) as [D'|D']; [right; exact D'|]. exfalso.
  apply (F3 (Z.max G lo - G)); [lia|]. replace (G + (Z.max G lo - G)) with (Z.max G lo) by lia.
  apply (P (Z.max G lo)). lia.
Qed.

Lemma block_aligned : forall L A mem md q k, aa_MR API L A mem md -> In (q, k) (blocks L A) -> q mod 8 = 0.
Proof using.
  intros L A mem md q k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn [fst snd] in E. injection E as <- <-.
  pose proof (mr_blocks_aligned Bm _ (aa_laws API) L A mem md p k' HM Hp) as H16.
  Z.div_mod_to_equations. lia.
Qed.

Theorem relay_add_holds (RF : ResFormT) : pthread_mutex_lock_contract -> pthread_mutex_unlock_contract ->
  memset_contract -> wake_contract -> realloc_null_contract_rt Bm API RF 0x178f8 -> ms_malloc Bm = 0x1608c ->
  relay_add_contract Bm API RF.
Proof using AX CTX NODUP.
  intros SPL SPU MSET WAKEC REAL MPC. unfold relay_add_contract.
  intros L A regs mem md bnd N C G ents tail. cbv zeta.
  intros SEG PRE INIT RO ERRI PL1 PL2 GL WK NS GS FDR NR CASES RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (EK : RELAY_ADD_K = 8320) by reflexivity.
  rewrite EK in *.
  unfold G_LOCK, G_LOCK_HI, G_RELAY_LO, G_NSRC, G_SRC, G_WAKE1, SRC_TABLE, SRC_ENTRY, RELAY_ADD in *.
  set (sp := reg_get regs 2) in *.
  assert (SPE : spZ regs = bv_unsigned sp) by reflexivity. rewrite SPE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  rewrite SEG in RO, GL, WK, NS, GS, HWS, HERR, CASES.
  rewrite SEG.
  assert (EL : 0 <= errno_addr Bm /\ errno_addr Bm + 4 <= 2 ^ 21).
  { pose proof (in_img_low SEG _ (ERRI (errno_addr Bm) ltac:(lia))).
    pose proof (in_img_low SEG _ (ERRI (errno_addr Bm + 3) ltac:(lia))). lia. }
  assert (G1 : forall a, 0x318a0 <= a < 0x31920 -> in_img Bm a) by (intros a Ha; exact (proj1 (PL1 a Ha))).
  assert (G2 : forall a, 0x2162c <= a < 0x21630 -> in_img Bm a) by (intros a Ha; exact (proj1 (PL2 a Ha))).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8320) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha. assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (mem_rel_normalize rsegs mem RO) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as MI0.
  pose proof (stk_norm mem _ _ RO ST ltac:(lia)) as ST0.
  pose proof (rw_norm mem _ _ RO GL ltac:(intros i Hi; apply ro_glob; cbn in Hi; lia)) as GL0.
  pose proof (rw_norm mem _ _ RO NS ltac:(intros i Hi; apply ro_glob; cbn in Hi; lia)) as NS0.
  pose proof (rw_norm mem _ _ RO GS ltac:(intros i Hi; apply ro_glob; cbn in Hi; lia)) as GS0.
  pose proof (bytes_at_normalize rsegs mem _ _ RO WK) as WK0.
  assert (OWG : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> 0x318a0 <= a < 0x31920 -> ~ owned Bm L0 A0 a)
    by (intros L0 A0 m0 md0 a HM Ha; exact (img_not_owned _ _ _ _ a HM (PL1 a Ha))).
  match type of FDR with - 2 ^ 31 <= ?f < 2 ^ 31 => destruct (Z_lt_le_dec f 0) as [NEG|POS] end.
  - eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply (evt_normalize rsegs); [exact ra_wx | exact RO |].
      eapply (ra_neg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                (normalize rsegs mem) (bv_unsigned sp - 8320)); [exact ST0 | lia | exact NEG]. }
    intros ms1 (can & (s0 & HQ & REL & ROS) & EQV).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' &
      -> & MU & WM & _).
    destruct (rel_eqv _ _ _ _ _ _ REL EQV) as (R1 & m1 & -> & X1 & HR1 & EM). rewrite EM in ROS.
    pose proof (munch_rel rsegs _ mem _ m1 m1' HR0 HR1 ROS MU) as MUr.
    pose proof (wmono_rel rsegs mem _ m1 m1' HR0 HR1 ROS WM) as WMr.
    pose proof (ro_agree_same rsegs mem m1 RO ROS) as RO1.
    apply SR_ret. exists L, A, R1, m1, md, G, (@nil byte).
    split; [f_equal; f_equal; exact (ret_pc_of_ok _ HRA)|].
    split.
    { apply (post_nocall _ _ L A regs mem md [(bv_unsigned sp - 64, bv_unsigned sp)] m1 R1 SEG PRE MUr WMr).
      - intros x Hx O. nout O. left. lia.
      - intros a Ho. destruct (owned_low' _ _ _ _ a HMR Ho). cbn [outside]. split; [lia | exact I].
      - intros p n i Hp Hi O. exfalso.
        destruct (mr_blocks Bm _ LAWS L A mem md p n i HMR Hp Hi) as (_ & B1 & B2 & _). nout O. lia.
      - eapply pres_canon. exact X1. }
    split; [exact INIT|].
    split; [exists []; unfold relay_add_tr; rewrite (proj2 (Z.ltb_lt _ _) NEG);
            split; [reflexivity|]; split; [exact RES | intros H; lia]|].
    split; [exact RO1|].
    split.
    { apply (rw_cells_transport rsegs _ mem m1 _ _ GL MUr WMr). cbn. lia. }
    split.
    { apply (bytes_at_transport rsegs _ mem m1 _ _ WK MUr). cbn. lia. }
    split; [|intros H; lia].
    intros _. split; [geteqv X1|].
    split; [reflexivity|].
    split; [apply (rw_cells_transport rsegs _ mem m1 _ _ NS MUr WMr); cbn; lia|].
    apply (rw_cells_transport rsegs _ mem m1 _ _ GS MUr WMr); cbn; lia.
  - specialize (NR POS).
    destruct CASES as [(EC & EG & EN & EE) | (EC & INB & FRESH & LE & LT & TBL)].
    + subst C G N ents.
      eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
        eapply (evt_normalize rsegs); [exact ra_wx | exact RO |].
        eapply (ra_g1 SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (normalize rsegs mem) (bv_unsigned sp - 8320));
          first [exact ST0 | exact MI0 | exact GL0 | exact WK0 | exact NS0 | exact GS0 | exact POS | lia]. }
      intros ms1 (can & (s0 & HQ & REL & ROS) & EQV).
      unfold ra_g1_post in HQ.
      destruct HQ as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' &
        -> & MU1 & WM1 & MI1 & FR1 & ST1 & GL1 & WK1 & NS1 & GS1).
      destruct (rel_eqv _ _ _ _ _ _ REL EQV) as (R1 & m1 & -> & X1 & HR1 & EM). rewrite EM in ROS.
      pose proof (munch_rel rsegs _ mem _ m1 m1' HR0 HR1 ROS MU1) as MU1r.
      pose proof (wmono_rel rsegs mem _ m1 m1' HR0 HR1 ROS WM1) as WM1r.
      pose proof (ro_agree_same rsegs mem m1 RO ROS) as RO1.
      apply (rw_back m1) in FR1, GL1, NS1, GS1; [|exact HR1 ..].
      apply (bytes_at_rel rsegs m1 m1' _ _ HR1) in WK1.
      assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1358c) by geteqv X1.
      assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -64)) by geteqv X1.
      assert (E1_3 : getr R1 3 = reg_get regs 3) by geteqv X1.
      assert (E1_4 : getr R1 4 = reg_get regs 4) by geteqv X1.
      assert (E1_8 : getr R1 8 = reg_get regs 10) by geteqv X1.
      assert (E1_9 : getr R1 9 = Z_to_bv 64 0x318f8) by geteqv X1.
      assert (E1_10 : getr R1 10 = Z_to_bv 64 0) by geteqv X1.
      assert (E1_11 : getr R1 11 = Z_to_bv 64 896) by geteqv X1.
      assert (E1_18 : getr R1 18 = Z_to_bv 64 (-1)) by geteqv X1.
      assert (E1_19 : getr R1 19 = reg_get regs 19) by geteqv X1.
      assert (E1_20 : getr R1 20 = Z_to_bv 64 0x318a0) by geteqv X1.
      assert (E1_21 : getr R1 21 = Z_to_bv 64 0) by geteqv X1.
      assert (E1_22 : getr R1 22 = Z_to_bv 64 16) by geteqv X1.
      assert (E1_23 : getr R1 23 = reg_get regs 23) by geteqv X1.
      assert (E1_24 : getr R1 24 = reg_get regs 24) by geteqv X1.
      assert (E1_25 : getr R1 25 = reg_get regs 25) by geteqv X1.
      assert (E1_26 : getr R1 26 = reg_get regs 26) by geteqv X1.
      assert (E1_27 : getr R1 27 = reg_get regs 27) by geteqv X1.
      assert (SP1 : spZ R1 = bv_unsigned sp - 64).
      { unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))); [f_equal; exact E1_2|].
        apply unsigned_lit. lia. }
      assert (MR1 : aa_MR API L A m1 md).
      { apply (mr_munch L A mem md _ m1 SEG HMR MU1r).
        - intros a Ho. destruct (owned_low' _ _ _ _ a HMR Ho). cbn [outside].
          split; [lia|]. split; [intros Ha; exact (OWG _ _ _ _ a HMR ltac:(lia) Ho) | exact I].
        - intros p n i Hp Hi O. exfalso.
          destruct (mr_blocks Bm _ LAWS L A mem md p n i HMR Hp Hi) as (_ & B1 & B2 & _).
          pose proof (ax_blocks_img AX L A mem md p n i HMR Hp Hi) as NI.
          nout O; [lia | exact (NI (G1 (ptr_addr L p + i) ltac:(lia)))]. }
      pose proof REAL as RE. unfold realloc_null_contract_rt in RE. rewrite SEG in RE.
      assert (ROOM0 : rt_room RF bnd 896).
      { pose proof (ROOM [SP 0 0]) as R. unfold relay_add_tr in R. rewrite (proj2 (Z.ltb_ge _ _) POS) in R.
        exact (proj1 (R eq_refl)). }
      assert (RA1 : YK0s.ret_ok (getr R1 1)) by (rewrite E1_1; apply ret_ok_even; vm_compute; reflexivity).
      eapply SR_bind.
      { apply (RE L A R1 m1 md 896 bnd).
        - split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
          split; [exact RA1|].
          split; [rewrite SP1; Z.div_mod_to_equations; lia|].
          split; [rewrite SP1; unfold REALLOC_STACK, ALLOC_STACK; lia|].
          split; [rewrite SP1; lia|].
          split; [intros a Ha; rewrite SP1 in Ha; unfold REALLOC_STACK, ALLOC_STACK in Ha; rewrite SEG;
                  apply WM1r; apply HWS; lia|].
          split; [rewrite E1_4; exact HTP|].
          split; [intros a Ha; rewrite SEG; apply WM1r; apply HERR; exact Ha|].
          intros H. rewrite INIT in H. discriminate.
        - exact RO1.
        - exact E1_10.
        - exact E1_11.
        - exact (ra_ne_malloc Bm R1 0x1358c 0x1608c E1_1 MPC ltac:(vm_compute; reflexivity)).
        - exact RES.
        - exact ROOM0. }
      intros c2 RET. unfold malloc_ret_rt in RET.
      destruct RET as (L' & A' & R2 & m2 & md2 & res & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RO2 & GK &
        SURV & INIT2 & REG & RES').
      rewrite SEG in RO2.
      pose proof POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
      rewrite SEG in HFRAME, HBLKS, HSCR.
      destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
      destruct BLK as (b1 & b2 & BLK1 & BLK2).
      pose proof FRESH as (F1 & F2 & F3).
      assert (INB : In (res, 896) (blocks L' A')) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
      assert (KF : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) -> ~ owned Bm L A a -> ~ owned Bm L' A' a ->
                 ~ (bv_unsigned sp - 8320 <= a < bv_unsigned sp - 64) -> ~ (errno_addr Bm <= a < errno_addr Bm + 4) ->
                 mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
      { intros a Hr N1 N2 S1 S2. apply HFRAME; [exact Hr | exact N1 | exact N2 | | intros F; exact F].
        unfold scratch_k, REALLOC_STACK, ALLOC_STACK. rewrite SP1. intros [S|S]; [apply S1; lia | exact (S2 S)]. }
      assert (KG : forall a, img_plain Bm a ->
                 mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a -> writable_at rsegs m2 a)).
      { intros a P. pose proof P as (Pi & _ & _ & Pe). pose proof (in_img_low SEG a Pi).
        destruct (KF a (or_intror Pi) (img_not_owned _ _ _ _ a MR1 P) (img_not_owned _ _ _ _ a HMR' P)
                    ltac:(lia) Pe) as [K1 K2].
        split; [exact K1 | apply K2]. }
      assert (KS : forall a, bv_unsigned sp - 64 <= a < bv_unsigned sp ->
                 mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
      { intros a Ha. apply KF; [left; lia | intros Ho; destruct (owned_low' _ _ _ _ a MR1 Ho); lia
                               | intros Ho; destruct (owned_low' _ _ _ _ a HMR' Ho); lia | lia | lia]. }
      pose proof (rw_cells_transfer rsegs m1 m2 _ _ GL1
                    ltac:(intros i Hi; cbn in Hi; apply KG; apply PL1; lia)) as GL2.
      pose proof (rw_cells_transfer rsegs m1 m2 _ _ NS1
                    ltac:(intros i Hi; cbn in Hi; apply KG; apply PL1; lia)) as NS2.
      pose proof (rw_cells_transfer rsegs m1 m2 _ _ GS1
                    ltac:(intros i Hi; cbn in Hi; apply KG; apply PL1; lia)) as GS2.
      pose proof (bytes_at_transfer rsegs m1 m2 _ _ WK1
                    ltac:(intros i Hi; rewrite length_le4 in Hi; apply KG; apply PL2; lia)) as WK2.
      pose proof (rw_cells_transfer rsegs m1 m2 _ _ FR1
                    ltac:(intros i Hi; cbn [cells_size csize Nat.add] in Hi;
                          destruct (KS (bv_unsigned sp + -64 + i) ltac:(lia)) as [K1 K2];
                          split; [exact K1 | apply K2])) as FR2.
      assert (ST2 : stk rsegs m2 (bv_unsigned sp - 8320) (bv_unsigned sp + -64)).
      { split; [lia|]. split; [lia|]. intros a Ha.
        assert (W : writable_at rsegs m2 a).
        { apply HSCR. unfold scratch_k, REALLOC_STACK, ALLOC_STACK. rewrite SP1. left. lia. }
        split; [exact W|]. destruct (writable_hi_present m2 a ltac:(lia) W) as [bb E]. exists bb.
        unfold mrd, wa. rewrite E. reflexivity. }
      assert (PR : forall i, 0 <= i < Z.of_nat 896 -> present m2 (res + i))
        by (intros i Hi; exact (proj1 (block_facts _ _ _ _ _ _ i HMR' INB ltac:(lia)))).
      destruct (present_rw_cells rsegs m2 res 896 ltac:(lia) ltac:(lia) PR) as [jt0 TB2].
      assert (LJ : length jt0 = 896%nat) by (destruct TB2 as [[W _] _]; cbn in W; tauto).
      apply (cb_split2 m2 res 56 840) in TB2. destruct TB2 as [TE2 TQ2]. change (Z.of_nat 56) with 56 in TQ2.
      pose proof (mem_rel_normalize rsegs m2 RO2) as HR2.
      assert (ROT2 : forall x, res <= x < res + 896 -> ro_addr rsegs (wa x) = false).
      { intros x Hx. apply (ro_out SEG); [lia|]. replace x with (res + (x - res)) by lia. apply F3. lia. }
      pose proof (rw_norm m2 _ _ RO2 FR2 ltac:(intros i Hi; cbn [cells_size csize Nat.add] in Hi; apply ro_hi; lia))
        as FR2n.
      pose proof (stk_norm m2 _ _ RO2 ST2 ltac:(lia)) as ST2n.
      pose proof (rw_norm m2 _ _ RO2 GL2 ltac:(intros i Hi; apply ro_glob; cbn in Hi; lia)) as GL2n.
      pose proof (rw_norm m2 _ _ RO2 NS2 ltac:(intros i Hi; apply ro_glob; cbn in Hi; lia)) as NS2n.
      pose proof (rw_norm m2 _ _ RO2 GS2 ltac:(intros i Hi; apply ro_glob; cbn in Hi; lia)) as GS2n.
      pose proof (bytes_at_normalize rsegs m2 _ _ RO2 WK2) as WK2n.
      pose proof (rw_norm m2 _ _ RO2 TE2 ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply ROT2; lia)) as TE2n.
      pose proof (rw_norm m2 _ _ RO2 TQ2 ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply ROT2; lia)) as TQ2n.
      pose proof (mem_inv_normalize rsegs m2) as MI2n.
      assert (D1 := fresh_disj res _ _ FRESH PL2 ltac:(lia)).
      assert (D2 := fresh_disj res _ _ FRESH PL1 ltac:(lia)).
      assert (RA8 : res mod 8 = 0) by (Z.div_mod_to_equations; lia).
      assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -64))
        by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
      assert (E2_3 : reg_get R2 3 = reg_get regs 3) by exact (eq_trans (HPRES 3 ltac:(unfold callee_saved; lia)) E1_3).
      assert (E2_4 : reg_get R2 4 = reg_get regs 4) by exact (eq_trans (HPRES 4 ltac:(unfold callee_saved; lia)) E1_4).
      assert (E2_8 : reg_get R2 8 = reg_get regs 10) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
      assert (E2_9 : reg_get R2 9 = Z_to_bv 64 0x318f8)
        by exact (eq_trans (HPRES 9 ltac:(unfold callee_saved; lia)) E1_9).
      assert (E2_10 : reg_get R2 10 = Z_to_bv 64 res) by exact A0'.
      assert (E2_18 : reg_get R2 18 = Z_to_bv 64 (-1))
        by exact (eq_trans (HPRES 18 ltac:(unfold callee_saved; lia)) E1_18).
      assert (E2_19 : reg_get R2 19 = reg_get regs 19)
        by exact (eq_trans (HPRES 19 ltac:(unfold callee_saved; lia)) E1_19).
      assert (E2_20 : reg_get R2 20 = Z_to_bv 64 0x318a0)
        by exact (eq_trans (HPRES 20 ltac:(unfold callee_saved; lia)) E1_20).
      assert (E2_21 : reg_get R2 21 = Z_to_bv 64 0)
        by exact (eq_trans (HPRES 21 ltac:(unfold callee_saved; lia)) E1_21).
      assert (E2_22 : reg_get R2 22 = Z_to_bv 64 16)
        by exact (eq_trans (HPRES 22 ltac:(unfold callee_saved; lia)) E1_22).
      assert (E2_23 : reg_get R2 23 = reg_get regs 23)
        by exact (eq_trans (HPRES 23 ltac:(unfold callee_saved; lia)) E1_23).
      assert (E2_24 : reg_get R2 24 = reg_get regs 24)
        by exact (eq_trans (HPRES 24 ltac:(unfold callee_saved; lia)) E1_24).
      assert (E2_25 : reg_get R2 25 = reg_get regs 25)
        by exact (eq_trans (HPRES 25 ltac:(unfold callee_saved; lia)) E1_25).
      assert (E2_26 : reg_get R2 26 = reg_get regs 26)
        by exact (eq_trans (HPRES 26 ltac:(unfold callee_saved; lia)) E1_26).
      assert (E2_27 : reg_get R2 27 = reg_get regs 27)
        by exact (eq_trans (HPRES 27 ltac:(unfold callee_saved; lia)) E1_27).
      rewrite SEG. replace (getr R1 1) with (Z_to_bv 64 0x1358c) by (symmetry; exact E1_1).
      eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        rewrite E2_2, E2_3, E2_4, E2_8, E2_9, E2_10, E2_18, E2_19, E2_20, E2_21, E2_22, E2_23, E2_24, E2_25,
          E2_26, E2_27.
        eapply (evt_normalize rsegs); [exact ra_wx | exact RO2 |].
        eapply (ra_g2 SPU MSET WAKEC (reg_get regs 1) sp _ _ _ _ _ (reg_get regs 8) (reg_get regs 9) _ _ _ _ _ _ _
                  (reg_get regs 18) _ (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) _ _ _ _ _ _ _ _ _ _ _ _ _
                  (normalize rsegs m2) (bv_unsigned sp - 8320) res (firstn 56 jt0) (skipn 56 jt0));
          first [exact FR2n | exact ST2n | exact MI2n | exact GL2n | exact WK2n | exact NS2n | exact GS2n |
                 exact TE2n | exact TQ2n | exact POS | exact RA8 | exact D1 | exact D2 | lia]. }
      intros ms3 (can3 & (s3 & HQ3 & REL3 & ROS3) & EQV3).
      destruct HQ3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3' &
        -> & MU3 & WM3 & GL3 & WK3 & NS3 & GS3 & EN3 & PO3).
      destruct (rel_eqv _ _ _ _ _ _ REL3 EQV3) as (R3 & m3 & -> & X3 & HR3 & EM3). rewrite EM3 in ROS3.
      pose proof (munch_rel rsegs _ m2 _ m3 m3' HR2 HR3 ROS3 MU3) as MU3r.
      pose proof (wmono_rel rsegs m2 _ m3 m3' HR2 HR3 ROS3 WM3) as WM3r.
      pose proof (ro_agree_same rsegs m2 m3 RO2 ROS3) as RO3.
      apply (rw_back m3) in GL3, NS3, GS3, EN3, PO3; [|exact HR3 ..].
      apply (bytes_at_rel rsegs m3 m3' _ _ HR3) in WK3.
      apply SR_ret. exists L', A', R3, m3, md2, res, (skipn 56 jt0).
      split; [f_equal; f_equal; exact (ret_pc_of_ok _ HRA)|].
      split.
      { unfold relay_post. rewrite SEG.
        split.
        { apply (mr_munch L' A' m2 md2 _ m3 SEG HMR' MU3r).
          - intros a Ho. destruct (owned_low' _ _ _ _ a HMR' Ho). cbn [outside].
            split; [lia|].
            split; [intros Ha; exact (OWG _ _ _ _ a HMR' ltac:(lia) Ho)|].
            split; [intros Ha; exact (OWG _ _ _ _ a HMR' ltac:(lia) Ho)|].
            split; [intros Ha; exact (OWG _ _ _ _ a HMR' ltac:(lia) Ho)|].
            split; [|exact I]. intros Ha.
            apply (proj2 (proj2 (proj2 (block_facts _ _ _ _ _ _ (a - res) HMR' INB ltac:(lia))))).
            replace (res + (a - res)) with a by lia. exact Ho.
          - intros p n i Hp Hi O.
            destruct (mr_blocks Bm _ LAWS L' A' m2 md2 p n i HMR' Hp Hi) as (_ & B1 & B2 & _).
            pose proof (ax_blocks_img AX L' A' m2 md2 p n i HMR' Hp Hi) as NI.
            nout O; [lia | exfalso; exact (NI (G1 (ptr_addr L' p + i) ltac:(lia)))
                         | exfalso; exact (NI (G1 (ptr_addr L' p + i) ltac:(lia)))
                         | exfalso; exact (NI (G1 (ptr_addr L' p + i) ltac:(lia))) |].
            apply (rw_writable rsegs m3 _ _ _ EN3). cbn [cells_size csize Nat.add]. lia. }
        split; [exact HWF'|]. split; [exact HBD'|]. split; [exact HLE|]. split; [exact REG|].
        split; [intros p n H1 H2 _; exact (HSTAB p n H1 H2)|].
        split; [intros p n H _ _; exact (SURV p n H)|].
        split; [intros p H; split; [exact (SURV p 0 H) | exact (HSTAB p 0 H (SURV p 0 H))]|].
        split; [intros a Hi [Ho|Ho];
                [exact (CTX L A m1 md a MR1 (ax_img AX L' A' m2 md2 a HMR' Hi Ho)) | right; exact Ho]|].
        split; [eapply pres_canon; exact X3|].
        split; [exact HVM|].
        split.
        { intros a Hr Ho1 Ho2 Hs He. unfold scratch_k in Hs. rewrite SPE in Hs.
          assert (Ra : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low SEG a Hr); lia]).
          assert (O1 : outside [(bv_unsigned sp - 64, bv_unsigned sp); (0x318fc, 0x31900)] a).
          { cbn [outside]. split; [intros H; apply Hs; left; lia|].
            split; [intros H; apply He; cbv beta; left; lia | exact I]. }
          assert (O3 : outside [(bv_unsigned sp - 160, bv_unsigned sp); (0x318fc, 0x31900); (0x318b8, 0x318c0);
                                (0x318d0, 0x318d8); (res, res + 56)] a).
          { cbn [outside]. split; [intros H; apply Hs; left; lia|].
            split; [intros H; apply He; cbv beta; left; lia|].
            split; [intros H; apply He; cbv beta; right; left; lia|].
            split; [intros H; apply He; cbv beta; right; right; left; lia|].
            split; [|exact I]. intros H. destruct Hr as [Hr|Hr]; [lia|].
            apply (F3 (a - res)); [lia|]. replace (res + (a - res)) with a by lia. exact Hr. }
          destruct (KF a Hr Ho1 Ho2 ltac:(intros H; apply Hs; left; lia) ltac:(intros H; apply Hs; right; exact H))
            as [K1 K2].
          pose proof (munch_mbyte rsegs _ mem m1 a MU1r Ra O1) as E01.
          pose proof (munch_writable rsegs _ mem m1 a MU1r Ra O1) as W01.
          pose proof (munch_mbyte rsegs _ m2 m3 a MU3r Ra O3) as E23.
          pose proof (munch_writable rsegs _ m2 m3 a MU3r Ra O3) as W23.
          split; [rewrite E23, K1, E01; reflexivity | tauto]. }
        split.
        { intros p n i Hp1 Hp2 _ Hi He.
          destruct (mr_blocks Bm _ LAWS L A mem md p n i HMR Hp1 Hi) as (_ & B1 & B2 & _).
          pose proof (ax_blocks_img AX L A mem md p n i HMR Hp1 Hi) as NI.
          assert (INA : In (ptr_addr L p, n) (b1 ++ b2)).
          { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hp1). }
          pose proof (blocks_mid_disjoint _ _ _ _ _ _ _ _ _ _ HMR' BLK1 INA) as Dj.
          rewrite (munch_mbyte rsegs _ m2 m3 (ptr_addr L p + i) MU3r ltac:(lia)).
          2: { cbn [outside]. split; [lia|].
               split; [intros H; exact (NI (G1 (ptr_addr L p + i) ltac:(lia)))|].
               split; [intros H; exact (NI (G1 (ptr_addr L p + i) ltac:(lia)))|].
               split; [intros H; exact (NI (G1 (ptr_addr L p + i) ltac:(lia)))|].
               split; [lia | exact I]. }
          rewrite (HBLKS p n i Hp1 Hp2 Hi).
          apply (munch_mbyte rsegs _ mem m1 _ MU1r); [lia|].
          cbn [outside]. split; [lia|]. split; [intros H; exact (NI (G1 (ptr_addr L p + i) ltac:(lia))) | exact I]. }
        intros a Hs. unfold scratch_k in Hs. rewrite SPE in Hs. apply WM3r.
        destruct Hs as [Hs|Hs].
        - destruct (Z_lt_ge_dec a (bv_unsigned sp - 64)) as [D|D].
          + apply HSCR. unfold scratch_k, REALLOC_STACK, ALLOC_STACK. rewrite SP1. left. lia.
          + apply (proj1 (proj2 (KS a ltac:(lia)))). apply WM1r. apply HWS. lia.
        - apply HSCR. unfold scratch_k. right. exact Hs. }
      split; [exact INIT2|].
      split.
      { pose proof (NODUP L' A' m2 md2 HMR') as ND'.
        exists [sptr_of L' A' res]. unfold relay_add_tr, relay_add_tbl. rewrite (proj2 (Z.ltb_ge _ _) POS).
        split; [reflexivity|]. split; [exact RES'|].
        intros _. exact (sptr_of_spec L' A' res 896 ND' INB). }
      split; [exact RO3|]. split; [exact GL3|]. split; [exact WK3|].
      split; [intros H; lia|].
      intros _. split; [geteqv X3|].
      split; [exact NS3|]. split; [exact GS3|]. split; [exact INB|]. split; [exact FRESH|].
      split; [rewrite length_skipn, LJ; reflexivity|].
      split.
      { pose proof (rw_cells_merge rsegs m3 res [] [C4 (reg_get regs 10); CB 52 (repeat (Z_to_bv 8 0) 52)] [])
          as M.
        cbn [app] in M. specialize (M EN3). cbn [cells_size cells_bytes csize cbytes Nat.add] in M.
        rewrite app_nil_r in M.
        unfold new_entry. rewrite sgn64.
        pose proof (cb_join2 _ _ _ _ _ _ M PO3) as J.
        cbn [app]. exact J. }
      left. split; [reflexivity|]. exists b1, b2. split; [exact BLK1 | symmetry; exact BLK2].
    + subst C.
      pose proof FRESH as (F1 & F2 & F3).
      assert (LEn : length ents = Z.to_nat (56 * N)) by lia.
      change (Z.to_nat (16 * 56)) with 896%nat in TBL.
      replace 896%nat with (length ents + (896 - length ents))%nat in TBL by lia.
      destruct (cb_split2 _ _ _ _ _ TBL) as [TP TR]. clear TBL.
      rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r in TP.
      rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O in TR. cbn [app] in TR.
      replace (896 - length ents)%nat with (56 + (840 - length ents))%nat in TR by lia.
      destruct (cb_split2 _ _ _ _ _ TR) as [TE TQ]. clear TR.
      rewrite LEn in TP, TE, TQ.
      rewrite Z2Nat.id in TE, TQ by lia. change (Z.of_nat 56) with 56 in TQ.
      replace (840 - Z.to_nat (56 * N))%nat with (Z.to_nat (840 - 56 * N)) in TQ by lia.
      assert (D1 := fresh_disj G _ _ FRESH PL2 ltac:(lia)).
      assert (D2 := fresh_disj G _ _ FRESH PL1 ltac:(lia)).
      assert (GA8 : G mod 8 = 0) by exact (block_aligned _ _ _ _ _ _ HMR INB).
      assert (ROT : forall x, G <= x < G + 896 -> ro_addr rsegs (wa x) = false).
      { intros x Hx. apply (ro_out SEG); [lia|]. replace x with (G + (x - G)) by lia. apply F3. lia. }
      pose proof (rw_norm mem _ _ RO TP ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply ROT; lia)) as TP0.
      pose proof (rw_norm mem _ _ RO TE ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply ROT; lia)) as TE0.
      pose proof (rw_norm mem _ _ RO TQ ltac:(intros i Hi; cbn [cells_size csize] in Hi; apply ROT; lia)) as TQ0.
      eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
        eapply (evt_normalize rsegs); [exact ra_wx | exact RO |].
        eapply (ra_c16 SPL SPU MSET WAKEC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (normalize rsegs mem) (bv_unsigned sp - 8320) N G ents (firstn 56 tail) (skipn 56 tail));
          first [exact ST0 | exact MI0 | exact GL0 | exact WK0 | exact NS0 | exact GS0 | exact TP0 | exact TE0 |
                 exact TQ0 | exact POS | exact GA8 | exact D1 | exact D2 | lia]. }
      intros ms1 (can & (s0 & HQ & REL & ROS) & EQV).
      destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' &
        -> & MU & WM & GL1 & WK1 & NS1 & GS1 & TP1 & TE1 & TQ1).
      destruct (rel_eqv _ _ _ _ _ _ REL EQV) as (R1 & m1 & -> & X1 & HR1 & EM). rewrite EM in ROS.
      pose proof (munch_rel rsegs _ mem _ m1 m1' HR0 HR1 ROS MU) as MUr.
      pose proof (wmono_rel rsegs mem _ m1 m1' HR0 HR1 ROS WM) as WMr.
      pose proof (ro_agree_same rsegs mem m1 RO ROS) as RO1.
      apply (rw_back m1) in GL1, NS1, GS1, TP1, TE1, TQ1; [|exact HR1 ..].
      apply (bytes_at_rel rsegs m1 m1' _ _ HR1) in WK1.
      apply SR_ret. exists L, A, R1, m1, md, G, (skipn 56 tail).
      split; [f_equal; f_equal; exact (ret_pc_of_ok _ HRA)|].
      split.
      { apply (post_nocall _ _ L A regs mem md _ m1 R1 SEG PRE MUr WMr).
        - intros x Hx O. nout O; [left; lia | right; cbv beta; lia | right; cbv beta; lia | right; cbv beta; lia].
        - intros a Ho. destruct (owned_low' _ _ _ _ a HMR Ho). cbn [outside].
          split; [lia|]. split; [intros Ha; exact (OWG _ _ _ _ a HMR ltac:(lia) Ho)|].
          split; [intros Ha; exact (OWG _ _ _ _ a HMR ltac:(lia) Ho)|].
          split; [|exact I]. intros Ha.
          apply (proj2 (proj2 (proj2 (block_facts _ _ _ _ _ _ (a - G) HMR INB ltac:(lia))))).
          replace (G + (a - G)) with a by lia. exact Ho.
        - intros p n i Hp Hi O.
          destruct (mr_blocks Bm _ LAWS L A mem md p n i HMR Hp Hi) as (_ & B1 & B2 & _).
          pose proof (ax_blocks_img AX L A mem md p n i HMR Hp Hi) as NI.
          nout O; [lia | exfalso; exact (NI (G1 (ptr_addr L p + i) ltac:(lia)))
                       | exfalso; exact (NI (G1 (ptr_addr L p + i) ltac:(lia))) |].
          apply (rw_writable rsegs m1 _ _ _ TE1). cbn [cells_size csize Nat.add]. lia.
        - eapply pres_canon. exact X1. }
      split; [exact INIT|].
      split.
      { exists []. unfold relay_add_tr, relay_add_tbl.
        rewrite (proj2 (Z.ltb_ge _ _) POS), (proj2 (Z.eqb_neq N 16)) by lia.
        split; [reflexivity|]. split; [exact RES|].
        intros _. exact (sptr_of_spec L A G _ (NODUP L A mem md HMR) INB). }
      split; [exact RO1|].
      split; [exact GL1|]. split; [exact WK1|].
      split; [intros H; lia|].
      intros _. split; [geteqv X1|].
      split; [exact NS1|]. split; [exact GS1|]. split; [exact INB|]. split; [exact FRESH|].
      split; [rewrite length_skipn; lia|].
      split.
      { pose proof (rw_cells_merge rsegs m1 (G + 56 * N) [] [C4 (reg_get regs 10); CB 52 (repeat (Z_to_bv 8 0) 52)] [])
          as M.
        cbn [app] in M. specialize (M TE1). cbn [cells_size cells_bytes csize cbytes Nat.add] in M.
        rewrite app_nil_r in M.
        unfold new_entry. rewrite sgn64.
        assert (M' : rw_cells rsegs m1 (G + Z.of_nat (Z.to_nat (56 * N)))
                       [CB 56 (le4 (reg_get regs 10) ++ repeat (Z_to_bv 8 0) 52)])
          by (replace (G + Z.of_nat (Z.to_nat (56 * N))) with (G + 56 * N) by lia; exact M).
        pose proof (cb_join2 _ _ _ _ _ _ TP1 M') as J1.
        assert (Q' : rw_cells rsegs m1 (G + Z.of_nat (Z.to_nat (56 * N) + 56))
                       [CB (Z.to_nat (840 - 56 * N)) (skipn 56 tail)])
          by (replace (G + Z.of_nat (Z.to_nat (56 * N) + 56)) with (G + 56 * N + 56) by lia; exact TQ1).
        pose proof (cb_join2 _ _ _ _ _ _ J1 Q') as J2.
        rewrite <- app_assoc in J2.
        replace (Z.to_nat (16 * 56)) with (Z.to_nat (56 * N) + 56 + Z.to_nat (840 - 56 * N))%nat by lia.
        exact J2. }
      right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
Qed.

End RA.
