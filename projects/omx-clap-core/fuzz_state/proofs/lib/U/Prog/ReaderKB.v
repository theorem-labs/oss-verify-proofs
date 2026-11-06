(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths and module names changed; 702 of its 749 lines of code are new or changed and 692 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/pj_write.v, with its module paths and module names changed; 523 of its 563 lines of code are new or changed and 709 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjIn PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import ReaderRes.
Import ListNotations.
Open Scope Z_scope.

Lemma rk_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rk_mask : forall c : byte, bv_unsigned c <= 32 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (bv_unsigned (zxb c) mod 64)))) 1 =
    if ws (bv_unsigned c) then 1 else 0.
Proof.
  intros c Hc. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. cbn in R.
  unfold zxb, ws. rewrite (unsigned_lit (bv_unsigned c)) by lia.
  revert Hc R. generalize (bv_unsigned c) as x. intros x Hc R.
  assert (A : forallb (fun y => Z.eqb (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (y mod 64)))) 1)
                                      (if (y =? 32) || (y =? 9) || (y =? 10) || (y =? 13) then 1 else 0))
                      (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A x). cbv beta in A.
  apply Z.eqb_eq, A. apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia].
Qed.

Definition rk_suf (r x : list Z) : Prop := exists u, x = u ++ r.

Lemma rk_suf_refl : forall x, rk_suf x x.
Proof. intros x. exists []. reflexivity. Qed.

Lemma rk_suf_trans : forall r y x, rk_suf r y -> rk_suf y x -> rk_suf r x.
Proof. intros r y x (u & Hu) (v & Hv). exists (v ++ u). rewrite Hv, Hu. apply app_assoc. Qed.

Lemma rk_suf_skipn : forall n x, rk_suf (skipn n x) x.
Proof. intros n x. exists (firstn n x). symmetry. apply firstn_skipn. Qed.

Lemma rk_suf_skip : forall x, rk_suf (skip x) x.
Proof.
  induction x as [|b r IH]; [apply rk_suf_refl|]. cbn [skip]. destruct (ws b).
  - destruct IH as (u & Hu). exists (b :: u). cbn [app]. f_equal. exact Hu.
  - apply rk_suf_refl.
Qed.

Lemma rk_suf_tl : forall x, rk_suf (tl x) x.
Proof. intros [|b r]; [apply rk_suf_refl|]. exists [b]. reflexivity. Qed.

Lemma rk_suf_cons : forall b r y, rk_suf (b :: r) y -> rk_suf r y.
Proof. intros b r y (u & Hu). exists (u ++ [b]). rewrite Hu, <- app_assoc. reflexivity. Qed.

Lemma rk_suf_string : forall z ok s r t ok', jr_string z ok = (Some (s, r), t, ok') -> rk_suf r z.
Proof.
  intros z ok s r t ok' H. pose proof (jr_string_spec z ok) as S. rewrite H in S.
  destruct S as (q & Hq & Hd & _). destruct (G1_4 z s r Hd) as (q' & _ & Hr & _). rewrite Hr. apply rk_suf_skipn.
Qed.

Lemma rk_suf_lit : forall w v x ok u r t ok', lit w v x ok = (Some (u, r), t, ok') -> rk_suf r x.
Proof.
  intros w v x ok u r t ok' H. unfold lit in H.
  destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as E1 E2 E3 E4. rewrite <- E2. apply rk_suf_skipn.
Qed.

Lemma rk_suf_number : forall x ok u r t ok', jr_number jr_strtod x ok = (Some (u, r), t, ok') -> rk_suf r x.
Proof.
  intros x ok u r t ok' H. unfold jr_number in H. cbv zeta in H.
  destruct (skipn _ x) as [|c z] eqn:E; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct ((c =? 48) && _); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r'] eqn:SP. cbv beta iota in H.
  apply jbind_some in H as (a0 & t1 & ok1 & t2 & _ & H & _).
  destruct (whole _ _); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as E1 E2 E3 E4. subst r.
  apply (rk_suf_trans r' (c :: z) x).
  - apply span_app in SP. exists (c :: a). rewrite SP. reflexivity.
  - rewrite <- E. apply rk_suf_skipn.
Qed.

Lemma rk_suf_name : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) -> rk_suf y1 y.
Proof.
  intros o y ok nm y1 tn ok2 H. unfold jr_name in H. destruct o.
  - destruct (skip y) as [|b z] eqn:E; [unfold jrefuse in H; discriminate|].
    destruct (b =? 34); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([name r] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
    destruct (skip r) as [|c r1] eqn:E2; [unfold jbind, jfree, jrefuse in H; cbn in H; discriminate H|].
    destruct (c =? 58); [|unfold jbind, jfree, jrefuse in H; cbn in H; discriminate H].
    unfold jret in H. injection H as F1 F2 F3 F4. subst y1.
    apply (rk_suf_trans r1 r y); [apply (rk_suf_cons c); rewrite <- E2; apply rk_suf_skip|].
    apply (rk_suf_trans r z y); [exact (rk_suf_string z ok name r t1 ok1 Hs)|].
    apply (rk_suf_cons b). rewrite <- E. apply rk_suf_skip.
  - unfold jret in H. injection H as F1 F2 F3 F4. subst y1. apply rk_suf_refl.
Qed.

Lemma rk_suf_cont : forall loop d o x ok t r tr ok',
  (forall o' n cap acc y ok1 t1 r1 tr1 ok2, loop (S d) o' n cap acc y ok1 = (Some (t1, r1), tr1, ok2) -> rk_suf r1 y) ->
  jr_cont loop d o x ok = (Some (t, r), tr, ok') -> rk_suf r x.
Proof.
  intros loop d o x ok t r tr ok' HL H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbv zeta in H.
  destruct (skip (tl x)) as [|c r0] eqn:E; cbv beta iota in H.
  - pose proof (rk_suf_trans _ _ _ (rk_suf_skip (tl x)) (rk_suf_tl x)) as SY. rewrite E in SY.
    exact (rk_suf_trans _ _ _ (HL _ _ _ _ _ _ _ _ _ _ H) SY).
  - pose proof (rk_suf_trans _ _ _ (rk_suf_skip (tl x)) (rk_suf_tl x)) as SY. rewrite E in SY.
    destruct (c =? closer o); cbv beta iota in H.
    + unfold jret in H. injection H as F1 F2 F3 F4. subst r. exact (rk_suf_cons c _ _ SY).
    + exact (rk_suf_trans _ _ _ (HL _ _ _ _ _ _ _ _ _ _ H) SY).
Qed.

Lemma rk_suf_fuel : forall f,
  (forall d x ok t r tr ok', jrv jr_strtod f d x ok = (Some (t, r), tr, ok') -> rk_suf r x) /\
  (forall d o n cap acc y ok t r tr ok', jrl jr_strtod f d o n cap acc y ok = (Some (t, r), tr, ok') -> rk_suf r y).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y] eqn:SX; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (SY : rk_suf (b :: y) x) by (rewrite <- SX; apply rk_suf_skip).
      apply (rk_suf_trans r (b :: y) x); [|exact SY].
      destruct (b =? 123); cbv beta iota in H.
      { exact (rk_suf_cont _ _ _ _ _ _ _ _ _ (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H). }
      destruct (b =? 91); cbv beta iota in H.
      { exact (rk_suf_cont _ _ _ _ _ _ _ _ _ (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H). }
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
        unfold jret in H. injection H as F1 F2 F3 F4. subst r.
        apply (rk_suf_trans r1 y); [exact (rk_suf_string y ok s r1 t1 ok1 Hs)|]. exists [b]. reflexivity. }
      destruct (b =? 116); cbv beta iota in H; [exact (rk_suf_lit _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 102); cbv beta iota in H; [exact (rk_suf_lit _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 110); cbv beta iota in H; [exact (rk_suf_lit _ _ _ _ _ _ _ _ H)|].
      exact (rk_suf_number _ _ _ _ _ _ H).
    + intros d o n cap acc y ok t r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & Hn & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      pose proof (rk_suf_trans _ _ _ (IHv d y1 ok2 v r0 tv ok3 Ev) (rk_suf_name o y ok1 nm y1 tn ok2 Hn)) as S0.
      destruct (skip r0) as [|c r1] eqn:E; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (S1 : rk_suf r1 y).
      { apply (rk_suf_trans r1 r0 y); [apply (rk_suf_cons c); rewrite <- E; apply rk_suf_skip | exact S0]. }
      destruct (c =? 44); cbv beta iota in H.
      { exact (rk_suf_trans _ _ _ (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 t r t4 ok' H) S1). }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as F1 F2 F3 F4. subst r. exact S1.
Qed.

Lemma rk_wview_nofs : forall m x, find_segment rsegs (bv_unsigned x) 1 = None -> wview rsegs m x = m x.
Proof. intros m x H. unfold wview. destruct (m x); [reflexivity|]. rewrite H. reflexivity. Qed.

Lemma rk_mrd_nofs : forall m x, find_segment rsegs (bv_unsigned x) 1 = None -> mrd rsegs m x = m x.
Proof.
  intros m x H. unfold mrd. destruct (m x); [reflexivity|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite H. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YK14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
Local Open Scope Z_scope.

Lemma rk_wx : U.MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rk_fs_some : forall segs a n s, find_segment segs a n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= a /\ a + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 segs IH]; intros a n s H; cbn in H; [discriminate|].
  destruct (Z.of_N (seg_base s0) <=? a) eqn:E1; destruct (a + n <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) eqn:E2;
    cbn in H;
    try (destruct (IH _ _ _ H) as (I1 & I2 & I3); split; [right; exact I1 | split; assumption]).
  inversion H; subst. apply Z.leb_le in E1. apply Z.leb_le in E2. split; [left; reflexivity | split; assumption].
Qed.

Lemma rk_rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 33) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rk_seg_top : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 2 ^ 33.
Proof. intros s H. pose proof rk_rsegs_top as T. rewrite forallb_forall in T. apply Z.leb_le. exact (T s H). Qed.

Lemma rk_vm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma rk_vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma rk_pairwise_in : forall {T : Type} (R : T -> T -> Prop) (l : list T) x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros T R l. induction l as [|h l IH]; intros x y Hp Hx Hy Hne; cbn in *; [contradiction|].
  destruct Hp as [H1 H2]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - left. apply H1. exact Hy.
  - right. apply H1. exact Hx.
  - apply IH; assumption.
Qed.

Lemma rk_writable_munch : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros segs W m m' a H Ha Ho. unfold writable_at, wview. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit by lia. exact Ho.
Qed.

Lemma rk_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; destruct (Z.le_gt_cases lo x) as [Q1|Q1]; destruct (Z.lt_ge_cases x hi) as [Q2|Q2];
    first [left; split; [lia | exact H] | right; intros [Q3 Q4]; first [lia | contradiction]].
Qed.

Lemma rk_rw_cells_keep : forall m m' A cs, rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     mbyte rsegs m' (A + i) = mbyte rsegs m (A + i) /\ (writable_at rsegs m (A + i) -> writable_at rsegs m' (A + i))) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (H1 & H2 & H3)] (W1 & W2 & W3)] K.
  rewrite cells_bytes_length in H2 by exact Hwf.
  split; [split; [exact Hwf|]|].
  - split; [exact H1|]. split; [rewrite cells_bytes_length by exact Hwf; exact H2|].
    intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf.
    destruct (K (Z.of_nat i) ltac:(lia)) as [E _].
    transitivity (mbyte rsegs m' (A + Z.of_nat i)); [reflexivity|]. rewrite E.
    transitivity (mrd rsegs m (wa (A + Z.of_nat i))); [reflexivity|].
    apply H3. rewrite cells_bytes_length by exact Hwf. exact Hi.
  - split; [exact W1|]. split; [exact W2|]. intros i Hi.
    destruct (K i Hi) as [_ E]. apply E. apply W3. exact Hi.
Qed.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {B : malloc_syms} {API : AllocAPI B}.
Hypothesis SEG : ms_segs B = rsegs.

Lemma rk_ceil : 2 ^ 46 <= alloc_ceiling < 2 ^ 47.
Proof. pose proof (@YM05.alloc_ceiling_val rc) as H. lia. Qed.

Lemma rk_seg_img : forall s a, In s rsegs ->
  Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> in_img B a.
Proof.
  intros s a Hin Ha. pose proof (rk_seg_top s Hin) as T. unfold in_img. rewrite SEG.
  split; [intros E; rewrite E in Hin; exact Hin|].
  exists (segment_reservation s). split; [apply in_map; exact Hin|].
  unfold segment_reservation. cbn [fst snd]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). unfold page_round_down_Z, page_round_up_Z, page_size.
  rewrite (Z.mod_small (Z.of_N (seg_base s) / 4096 * 4096)) by (Z.div_mod_to_equations; lia).
  rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma rk_noimg_fs : forall a, ~ in_img B a -> find_segment rsegs a 1 = None.
Proof.
  intros a H. destruct (find_segment rsegs a 1) as [s|] eqn:E; [|reflexivity]. exfalso. apply H.
  destruct (rk_fs_some _ _ _ _ E) as (Hin & H1 & H2). apply (rk_seg_img s); [exact Hin | lia].
Qed.

Lemma rk_img_bound : forall a, in_img B a -> 0 <= a < 2 ^ 33.
Proof.
  intros a (_ & s & Hs & H1 & H2). rewrite SEG in Hs. unfold segments_reserved in Hs.
  apply in_map_iff in Hs as (s0 & <- & Hin). pose proof (rk_seg_top s0 Hin) as T.
  unfold segment_reservation in H1, H2. cbn [fst snd] in H1, H2.
  rewrite !Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
  unfold page_round_down_Z, page_round_up_Z, page_size in H1, H2.
  assert (0 <= Z.of_N (seg_base s0)) by lia. assert (0 <= Z.of_N (seg_size s0)) by lia.
  split; [pose proof (Z.mod_pos_bound (Z.of_N (seg_base s0) / 4096 * 4096) (2 ^ 64)); lia|].
  rewrite Z_to_bv_unsigned in H2. unfold bv_wrap in H2. change (bv_modulus 64) with (2 ^ 64) in H2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rk_high_nofs : forall a, 2 ^ 33 <= a -> find_segment rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [s|] eqn:E; [|reflexivity].
  destruct (rk_fs_some _ _ _ _ E) as (Hin & H1 & H2). pose proof (rk_seg_top s Hin). lia.
Qed.

Lemma rk_blk_of_user : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply (in_map (fun b => (ptr_addr L (fst b), snd b))) in H. exact H. Qed.

Lemma rk_blk_user : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn [fst snd] in E.
  injection E as E1 E2. subst k'. exists p. split; assumption.
Qed.

Lemma rk_blk_facts : forall L A mem md a k, aa_MR API L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= alloc_ceiling /\
  (forall i, 0 <= i < k -> present mem (a + i) /\ ~ owned B L A (a + i)).
Proof.
  intros L A mem md a k HM Hin. destruct (rk_blk_user L A a k Hin) as (p & Hp & <-).
  destruct (mr_blocks_range B _ (aa_laws API) L A mem md p k HM Hp) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (mr_blocks B _ (aa_laws API) L A mem md p k i HM Hp Hi) as (P & _ & _ & N). split; assumption.
Qed.

Lemma rk_D_facts : forall L A mem md Lam peak cnt fail D Lam0 a k,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> Permutation Lam (D ++ Lam0) -> In (a, k) D ->
  In (a - 16, k + 16) (blocks L A) /\ 4112 <= a /\ a + k <= alloc_ceiling /\ 0 <= k /\
  (forall i, -16 <= i < k -> ~ in_img B (a + i)).
Proof.
  intros L A mem md Lam peak cnt fail D Lam0 a k HM HL HP HD.
  assert (HI : In (a, k) Lam) by (apply (Permutation_in (a, k) (Permutation_sym HP)); apply in_or_app; left; exact HD).
  pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL HI) as (R1 & R2 & _).
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. specialize (HF _ HI).
  destruct HF as (Hk & Hin & _ & _). cbn [fst snd] in *.
  split; [exact Hin|]. split; [exact R1|]. split; [exact R2|]. split; [exact Hk|].
  intros i Hi. exact (ledger_block_not_img B L A mem Lam peak cnt fail a k i HL HI Hi).
Qed.

Lemma rk_fresh : forall L A L1 A1 mem1 md1 D p n i a k,
  aa_MR API L1 A1 mem1 md1 -> new_blks L A D -> In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) ->
  ptr_addr L1 p = ptr_addr L p -> In (a, k) D -> In (a - 16, k + 16) (blocks L1 A1) -> 0 <= i < n ->
  ~ (a - 16 <= ptr_addr L p + i < a + k).
Proof.
  intros L A L1 A1 mem1 md1 D p n i a k HM NB Hp Hp1 Ep HD HB Hi Hx.
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem1 md1 HM) as PW.
  pose proof (rk_blk_of_user L1 A1 p n Hp1) as Hq. rewrite Ep in Hq.
  destruct (Z.eq_dec (ptr_addr L p) (a - 16)) as [E1|E1]; [destruct (Z.eq_dec n (k + 16)) as [E2|E2]|].
  - apply (NB a k HD). rewrite <- E1, <- E2. exact (rk_blk_of_user L A p n Hp).
  - destruct (rk_pairwise_in _ _ _ _ PW Hq HB ltac:(intros E; injection E as E3 E4; lia)) as [R|R];
      unfold ranges_disjoint in R; cbn [fst snd] in R; lia.
  - destruct (rk_pairwise_in _ _ _ _ PW Hq HB ltac:(intros E; injection E as E3 E4; lia)) as [R|R];
      unfold ranges_disjoint in R; cbn [fst snd] in R; lia.
Qed.

Lemma rk_MR_A : forall L A mem mem1 md W, aa_MR API L A mem md -> munch W mem mem1 -> wmono (ms_segs B) mem mem1 ->
  (forall x, owned B L A x -> outside W x) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> ~ in_img B x) ->
  aa_MR API L A mem1 md.
Proof.
  intros L A mem mem1 md W HM MU WM HO HI. destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hm).
  pose proof rk_ceil as HC.
  eapply (mr_frame B _ (aa_laws API) L A mem mem1 md md HM).
  - intros a Ha. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ha).
    apply (U.MemNorm.mbyte_munch _ W); [exact MU | lia | apply HO; exact Ha].
  - intros a Ha (b0 & Hb0). pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ha).
    exists b0. rewrite (MU (Z_to_bv 64 a)); [exact Hb0|]. rewrite unsigned_lit by lia. apply HO. exact Ha.
  - intros p n i Hp Hi. destruct (mr_blocks B _ (aa_laws API) L A mem md p n i HM Hp Hi) as ((b0 & Hb0) & H1 & H2 & _).
    assert (Hr : 0 <= ptr_addr L p + i < 2 ^ 64) by lia.
    destruct (rk_outside_dec W (ptr_addr L p + i)) as [Ho|Ho].
    + exists b0. rewrite (MU (Z_to_bv 64 (ptr_addr L p + i))); [exact Hb0|]. rewrite unsigned_lit by lia. exact Ho.
    + pose proof (rk_noimg_fs _ (HI _ Hr Ho)) as NF.
      assert (W0 : wview (ms_segs B) mem (Z_to_bv 64 (ptr_addr L p + i)) <> None) by (unfold wview; rewrite Hb0; discriminate).
      pose proof (WM _ W0) as W1. rewrite SEG in W1. rewrite rk_wview_nofs in W1 by (rewrite unsigned_lit by lia; exact NF).
      destruct (mem1 (Z_to_bv 64 (ptr_addr L p + i))) as [b1|] eqn:E1; [exists b1; exact E1 | contradiction].
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hm.
Qed.

Lemma rk_word_keep : forall m m' a v, word_mem (ms_segs B) m a v ->
  (forall k, 0 <= k < 8 -> mbyte (ms_segs B) m' (a + k) = mbyte (ms_segs B) m (a + k)) -> word_mem (ms_segs B) m' a v.
Proof. intros m m' a v H K k Hk. rewrite K by lia. apply H. exact Hk. Qed.

Lemma rk_ledger_keep : forall L A m m' Lam peak cnt fail, ledger B L A m Lam peak cnt fail ->
  (forall a, alloc_statics a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 -> mbyte (ms_segs B) m' (a - 16 + i) = mbyte (ms_segs B) m (a - 16 + i)) ->
  ledger B L A m' Lam peak cnt fail.
Proof.
  intros L A m m' Lam peak cnt fail (AW & R1 & R2 & R3 & ND & FA) HS HH.
  destruct AW as (W1 & W2 & W3 & W4).
  split; [|split; [exact R1|split; [exact R2|split; [exact R3|split; [exact ND|]]]]].
  - split; [|split; [|split]]; eapply rk_word_keep; try eassumption; intros k Hk; apply HS;
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia.
  - rewrite Forall_forall in FA |- *. intros [a k] Hin. specialize (FA _ Hin). destruct FA as (Hk & Hb & Hw & Hn).
    cbn [fst snd] in *. split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hn].
    eapply rk_word_keep; [exact Hw|]. intros j Hj. apply (HH a k j Hin Hj).
Qed.

Lemma rk_auxv_keep : forall sec lo mem mem', auxv_pre B sec lo mem ->
  (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem' (ms_libc B + 8 + i) = mbyte (ms_segs B) mem (ms_libc B + 8 + i)) ->
  (forall a, lo <= a < 2 ^ 63 -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  auxv_pre B sec lo mem'.
Proof.
  intros sec lo mem mem' (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) KL KH.
  exists av, ar.
  split; [eapply rk_word_keep; [exact H1|]; intros k Hk; replace (ms_libc B + 8 + k) with (ms_libc B + 8 + k) by lia;
          apply KL; exact Hk|].
  split; [intros k Hk; eapply rk_word_keep; [apply H2; exact Hk|]; intros j Hj; apply KH; lia|].
  split; [eapply rk_word_keep; [exact H3|]; intros j Hj; apply KH; lia|].
  split; [eapply rk_word_keep; [exact H4|]; intros j Hj; apply KH; lia|].
  repeat split; lia.
Qed.

Lemma rk_layout_trans : forall A L L1 A1 L2, layout_le A L L1 -> layout_le A1 L1 L2 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> layout_le A L L2.
Proof.
  intros A L L1 A1 L2 (C1 & S1 & B1 & R1) (C2 & S2 & B2 & R2) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite R2 by lia. apply R1. exact Hr.
Qed.

Lemma rk_of_A : forall K L A regs mem md E mem1 W regsF,
  aa_MR API L A mem1 md -> WF A -> bounded A -> regs_preserved regs regsF ->
  munch W mem mem1 -> wmono (ms_segs B) mem mem1 ->
  (forall a, scratch_k B K regs a -> writable_at (ms_segs B) mem a) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ scratch_k B K regs x -> ~ E x -> outside W x) ->
  (forall i, 0 <= i < 8 -> outside W (ms_libc B + 8 + i)) -> 0 <= ms_libc B + 8 -> ms_libc B + 16 <= 2 ^ 64 ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ E (ptr_addr L p + i) ->
     0 <= ptr_addr L p + i < 2 ^ 64 /\ outside W (ptr_addr L p + i)) ->
  rpost B API K L A regs mem md E (fun _ _ => False) L A regsF mem1 md.
Proof.
  intros K L A regs mem md E mem1 W regsF HM HWF HB RP MU WM HSW HE HL HL1 HL2 HP.
  pose proof rk_ceil as HC.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [tauto|].
  split; [intros _ i Hi; apply (U.MemNorm.mbyte_munch _ W); [exact MU | lia | apply HL; exact Hi]|].
  split; [lia|].
  split; [intros p n Hp _; exact Hp|].
  split; [reflexivity|].
  split; [exact RP|].
  split; [exists (m_vmmaps md); apply rk_vm_self|].
  split.
  { intros a Ha Hs He. assert (Ho : outside W a) by (apply HE; [lia | exact Hs | exact He]).
    split; [apply (U.MemNorm.mbyte_munch _ W); [exact MU | lia | exact Ho] | apply (rk_writable_munch _ W); [exact MU | lia | exact Ho]]. }
  split.
  { intros a Ha _ Hs He. pose proof (rk_img_bound a Ha) as Hr.
    assert (Ho : outside W a) by (apply HE; [lia | exact Hs | exact He]).
    split; [apply (U.MemNorm.mbyte_munch _ W); [exact MU | lia | exact Ho] | apply (rk_writable_munch _ W); [exact MU | lia | exact Ho]]. }
  split.
  { intros p n i Hp _ Hi He. destruct (HP p n i Hp Hi He) as [Hr Ho].
    apply (U.MemNorm.mbyte_munch _ W); [exact MU | exact Hr | exact Ho]. }
  intros a Ha. unfold writable_at. apply WM. exact (HSW a Ha).
Qed.

Lemma rk_seq : forall K L A regs mem md E L1 A1 regsX mem1 md1 K2 regs2 E2 gone2 L2 A2 regs3 mem2 md2 regsF,
  rpost B API K L A regs mem md E (fun _ _ => False) L1 A1 regsX mem1 md1 ->
  rpost B API K2 L1 A1 regs2 mem1 md1 E2 gone2 L2 A2 regs3 mem2 md2 ->
  regs_preserved regs regsF ->
  spZ regs - K <= spZ regs2 - K2 -> spZ regs2 <= spZ regs -> alloc_ceiling + K <= spZ regs -> 0 <= K2 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B K regs a -> ~ E a -> ~ E2 a) ->
  (forall a, in_img B a -> ~ scratch_k B K regs a -> ~ E a -> ~ E2 a) ->
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) -> ~ E2 (ptr_addr L p + i)) ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ~ gone2 (ptr_addr L p) n) ->
  (forall a, scratch_k B K regs a -> ~ scratch_k B K2 regs2 a -> ~ E2 a \/ writable_at (ms_segs B) mem2 a) ->
  rpost B API K L A regs mem md E (fun _ _ => False) L2 A2 regsF mem2 md2.
Proof.
  intros K L A regs mem md E L1 A1 regsX mem1 md1 K2 regs2 E2 gone2 L2 A2 regs3 mem2 md2 regsF R1 R2 RPF
    W1 W2 HC HK2 HE12 HI12 HB12 HG12 HW12.
  destruct R1 as (M1 & WF1 & B1 & Y1 & I1 & X1 & G1 & S1 & P1 & _ & D1 & H1 & IM1 & K1 & C1).
  destruct R2 as (M2 & WF2 & B2 & Y2 & I2 & X2 & G2 & S2 & P2 & _ & D2 & H2 & IM2 & K2' & C2).
  assert (NS : forall a, ~ scratch_k B K regs a -> ~ scratch_k B K2 regs2 a).
  { intros a Hn Hs. apply Hn. unfold scratch_k in *. destruct Hs as [Hs|Hs]; [left; lia | right; exact Hs]. }
  split; [exact M2|]. split; [exact WF2|]. split; [exact B2|].
  split; [exact (rk_layout_trans A L L1 A1 L2 Y1 Y2 G1)|].
  split; [intros H; apply I2, I1, H|].
  split.
  { intros HN i Hi. assert (HN1 : st_init_done A1 = false).
    { case_eq (st_init_done A1); intros E1; [rewrite (I2 E1) in HN; discriminate HN | reflexivity]. }
    rewrite (X2 HN i Hi). exact (X1 HN1 i Hi). }
  split; [lia|].
  split.
  { intros p n Hp _. assert (Hp1 : In (p, n) (user_blocks A1)) by (apply S1; [exact Hp | tauto]).
    apply S2; [exact Hp1|]. rewrite (P1 p n Hp Hp1). exact (HG12 p n Hp Hp1). }
  split.
  { intros p n Hp Hp2. assert (Hp1 : In (p, n) (user_blocks A1)) by (apply S1; [exact Hp | tauto]).
    rewrite (P2 p n Hp1 Hp2). exact (P1 p n Hp Hp1). }
  split; [exact RPF|].
  split.
  { destruct D1 as (v1 & E1). destruct D2 as (v2 & E2'). exists v2. rewrite E2', E1. apply rk_vm_twice. }
  split.
  { intros a Ha Hs He. destruct (H1 a Ha Hs He) as [Ea Wa].
    destruct (H2 a Ha (NS a Hs) (HE12 a Ha Hs He)) as [Eb Wb]. split; [congruence | tauto]. }
  split.
  { intros a Ha Hn Hs He. destruct (IM1 a Ha Hn Hs He) as [Ea Wa].
    destruct (IM2 a Ha Hn (NS a Hs) (HI12 a Ha Hs He)) as [Eb Wb]. split; [congruence | tauto]. }
  split.
  { intros p n i Hp Hp2 Hi He. assert (Hp1 : In (p, n) (user_blocks A1)) by (apply S1; [exact Hp | tauto]).
    pose proof (K2' p n i Hp1 Hp2 Hi) as Kb. rewrite (P1 p n Hp Hp1) in Kb.
    rewrite (Kb (HB12 p n i Hp Hp1 Hi He)). exact (K1 p n i Hp Hp1 Hi He). }
  intros a Ha.
  assert (Hd : scratch_k B K2 regs2 a \/ ~ scratch_k B K2 regs2 a) by (unfold scratch_k; lia).
  destruct Hd as [Hd|Hd]; [exact (C2 a Hd)|].
  destruct (HW12 a Ha Hd) as [He|Hw]; [|exact Hw].
  assert (Hst : spZ regs - K <= a < spZ regs).
  { unfold scratch_k in Ha, Hd. destruct Ha as [Ha|Ha]; [exact Ha | exfalso; apply Hd; right; exact Ha]. }
  pose proof (C1 a Ha) as Hw1.
  assert (Hr : alloc_ceiling <= a < 2 ^ 64).
  { pose proof (zr_word (getr regs 2)) as R. unfold inr64 in R. unfold spZ in Hst, HC. lia. }
  destruct (H2 a Hr Hd He) as [_ Wb]. apply Wb. exact Hw1.
Qed.

Lemma rk_getr_eqv : forall R R', xregs_eqv R R' -> forall r, getr R' r = getr R r.
Proof.
  intros R R' H r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. rewrite <- bv_eqb0_is_x0. exact E.
Qed.

Lemma rk_canon : forall (f : FPState) regs pc m ro,
  RegisterBridge.canonical_register_state (@mkst f regs pc m ro) = MS (mkR_of regs) (@fp_regs f) pc (@fp_csr f) None m ro.
Proof. reflexivity. Qed.

Lemma rk_eqv_shape : forall (f : FPState) R pc m ro ms',
  ms_eqv (MS R (@fp_regs f) pc (@fp_csr f) None m ro) ms' ->
  ms' = @mkst f (ms_regs ms') pc m ro /\ xregs_eqv R (ms_regs ms').
Proof.
  intros f R pc m ro [R' F' pc' svc' rv' fc' m' ro'] (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  cbn in *. subst. split; [reflexivity | exact HR].
Qed.

Lemma rk_rel_shape : forall R pc m0 ro can ms',
  U.MemNorm.ms_rel rsegs can (MS R (@fp_regs fx) pc (@fp_csr fx) None m0 ro) -> ms_eqv can ms' ->
  ms' = @mkst fx (ms_regs ms') pc (ms_mem can) ro /\ xregs_eqv R (ms_regs ms') /\ U.MemNorm.mem_rel rsegs (ms_mem can) m0.
Proof.
  intros R pc m0 ro [cr cf cp cs cv cc cm co] [R' F' pc' svc' rv' fc' m' ro'] (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8)
    (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  cbn in *. subst. split; [reflexivity|]. split; [exact HR | exact E8].
Qed.

Lemma rk_stk_of_wr : forall m lo hi, 2 ^ 33 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. unfold writable_at in W. change (wview rsegs m (wa a) <> None) in W.
  assert (NF : find_segment rsegs (bv_unsigned (wa a)) 1 = None) by (rewrite wa_unsigned by lia; apply rk_high_nofs; lia).
  split; [exact W|].
  rewrite rk_mrd_nofs by exact NF. rewrite rk_wview_nofs in W by exact NF.
  destruct (m (wa a)) as [b0|]; [exists b0; reflexivity | contradiction].
Qed.

Lemma rk_stk_norm : forall m lo hi, (forall a, lo <= a < hi -> find_segment rsegs a 1 = None) ->
  stk rsegs m lo hi -> stk rsegs (U.MemNorm.normalize rsegs m) lo hi.
Proof.
  intros m lo hi NF (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (E : U.MemNorm.normalize rsegs m (wa a) = m (wa a)).
  { unfold U.MemNorm.normalize. cbv beta. unfold OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.ro_addr.
    rewrite wa_unsigned by lia. rewrite (NF a Ha). reflexivity. }
  destruct (H a Ha) as [W (b0 & Hb)]. unfold wview in *. unfold mrd in *. rewrite E. split; [exact W | exists b0; exact Hb].
Qed.

Lemma rk_rw_cells_rel : forall m m0 A cs, U.MemNorm.mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (U.MemNorm.bytes_at_rel rsegs m m0 A _ HR) Hb).
  - exact (U.MemNorm.wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

Definition rk_cs (regs regs' : bvmap 5 word) : Prop :=
  forall r, r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).

Lemma rk_cs_rp : forall r0 r1 r2, rk_cs r0 r1 -> regs_preserved r1 r2 -> rk_cs r0 r2.
Proof. intros r0 r1 r2 H1 H2 r Hr. rewrite (H2 r) by (unfold callee_saved; lia). exact (H1 r Hr). Qed.

Lemma rk_cs_mkR : forall R R' x1 x2 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  xregs_eqv (mkR x1 x2 (reg_get R 3) (reg_get R 4) x5 x6 x7 x8 (reg_get R 9) x10 x11 x12 x13 x14 x15 x16 x17
     (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21) (reg_get R 22) (reg_get R 23) (reg_get R 24)
     (reg_get R 25) (reg_get R 26) (reg_get R 27) x28 x29 x30 x31) R' -> rk_cs R R'.
Proof.
  intros R R' x1 x2 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 XR r Hr.
  rewrite (rk_getr_eqv _ _ XR).
  assert (Hc : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
               r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]; reflexivity.
Qed.

Lemma rk_ret_pc : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof. intros k H. exact (KindBGlue.kb_ret_pc k H). Qed.

Lemma rk_regs : forall K L A regs mem md E gone L' A' regs' mem' md' regsF,
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' -> regs_preserved regs regsF ->
  rpost B API K L A regs mem md E gone L' A' regsF mem' md'.
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' regsF
    (M & W & Bd & Y & I & X & G & S & P & _ & D & H & IM & Kb & C) RP.
  exact (conj M (conj W (conj Bd (conj Y (conj I (conj X (conj G (conj S (conj P (conj RP (conj D (conj H (conj IM (conj Kb C)))))))))))))).
Qed.

Lemma rk_scr : forall K L A regs mem md E gone L' A' regs' mem' md' mem'' W,
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  aa_MR API L' A' mem'' md' -> munch W mem' mem'' -> wmono (ms_segs B) mem' mem'' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> spZ regs - K <= x < spZ regs) ->
  alloc_ceiling <= spZ regs - K ->
  rpost B API K L A regs mem md E gone L' A' regs' mem'' md'.
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' mem'' W
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) M MU WM HW HK.
  pose proof rk_ceil as HC.
  assert (OUT : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - K <= x < spZ regs) -> outside W x).
  { intros x Hx Hn. destruct (rk_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. exact (Hn (HW x Hx Ho)). }
  assert (KB : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - K <= x < spZ regs) ->
             mbyte (ms_segs B) mem'' x = mbyte (ms_segs B) mem' x /\
             (writable_at (ms_segs B) mem' x <-> writable_at (ms_segs B) mem'' x)).
  { intros x Hx Hn. split.
    - apply (U.MemNorm.mbyte_munch _ W); [exact MU | exact Hx | exact (OUT x Hx Hn)].
    - apply (rk_writable_munch _ W); [exact MU | exact Hx | exact (OUT x Hx Hn)]. }
  split; [exact M|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split.
  { intros HI i Hi. rewrite <- (H6 HI i Hi).
    assert (Ho : owned B L' A' (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
    pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M Ho). apply KB; lia. }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|].
  split.
  { intros a Ha Hs He. destruct (H12 a Ha Hs He) as (E1 & E2).
    destruct (KB a ltac:(lia) ltac:(unfold scratch_k in Hs; tauto)) as (E3 & E4).
    split; [rewrite E3; exact E1 | rewrite <- E4; exact E2]. }
  split.
  { intros a Ha HO Hs He. destruct (H13 a Ha HO Hs He) as (E1 & E2). pose proof (rk_img_bound a Ha) as Hr.
    destruct (KB a ltac:(lia) ltac:(lia)) as (E3 & E4).
    split; [rewrite E3; exact E1 | rewrite <- E4; exact E2]. }
  split.
  { intros p n i Hp Hp' Hi He. rewrite <- (H14 p n i Hp Hp' Hi He).
    destruct (mr_blocks B _ (aa_laws API) L' A' mem'' md' p n i M Hp' Hi) as (_ & R1 & R2 & _).
    rewrite (H9 p n Hp Hp') in R1, R2. apply KB; lia. }
  intros a Ha. unfold writable_at. apply WM. exact (H15 a Ha).
Qed.

Lemma rk_kA : forall (f : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MS (mkR_of regs) (@fp_regs f) pc (@fp_csr f) None mem (seg_rom rsegs)) ->
  (forall ms', (exists can, Q can /\ ms_eqv can ms') -> SR rsegs (mkCfg ms' md) P) ->
  SR rsegs (mkCfg (@mkst f regs pc mem (seg_rom rsegs)) md) P.
Proof. intros f regs pc mem md Q P Hh Hl HE HK. eapply evt_SR_canon; [rewrite rk_canon; exact HE | exact Hh | exact Hl | exact HK]. Qed.

Lemma rk_cs_trans : forall r0 r1 r2, rk_cs r0 r1 -> rk_cs r1 r2 -> rk_cs r0 r2.
Proof. intros r0 r1 r2 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

End KB.
