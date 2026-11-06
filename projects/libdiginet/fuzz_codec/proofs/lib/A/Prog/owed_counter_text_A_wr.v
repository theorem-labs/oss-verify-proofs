(* owed_counter_text at image A: facts on the bytes the call writes (seg[8] and *dots, twr_ok of the contract) at
   the walk's later states, for the second loop and the release (owed_counter_text_A_base.v has the vocabulary). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Lemma oc_awr_move : forall STK sp0 FP bl0 blc blc' ly ly' own own' a,
  awr_byte STK sp0 FP bl0 blc ly own a ->
  (forall b n, In (b, n) blc -> In (b, n) blc') ->
  (forall c p, frame_addr ly c p = frame_addr ly' c p) -> incl own own' ->
  awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own own' a [H | [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | (cid & pos & Hin & Hz)]]]
  Hbl Hfa Hown.
- left; exact H.
- right; left. split; [exact Hf|]. exists b, n. split; [apply Hbl; exact Hin | exact Hr].
- right; right; left. exists b, n. split; [apply Hbl; exact Hin|]. split; [exact Hn0 | exact Hr].
- right; right; right. exists cid, pos. split; [apply Hown; exact Hin|]. rewrite <- !Hfa. exact Hz.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variable MT : ameter_ops.
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
(* where a byte the call may write (twr_ok of the call state) lies: the caller's stack allowance, a heap block of the
   call state, or a side-stack frame of it (the frame's shadow is not app memory) *)
Lemma oc_twr_cases : forall cx q n x,
  oc_pre B GLYPHA ROSTRS cx ->
  twr_ok tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_lyc cx) (o_Sc cx) (o_own cx) (o_W cx) (o_memc cx)
    (spZ (o_regs cx)) q n ->
  amem_range q n -> q <= x < q + n ->
  (o_sp0 cx - o_STK cx <= x < o_sp0 cx) \/
  (exists b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) /\ b <= x < b + req_size m) \/
  (exists cid pos, In (cid, pos) (frames (o_Sc cx)) /\ in_zr x (frame_rng (o_lyc cx) (cid, pos))).
Proof.
intros cx q n x Hpre Htw Ham Hx.
pose proof Hpre as ((HJ0 & _) & _).
pose proof HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct (Htw x Hx) as (Haw & _ & _ & _).
destruct Haw as [H | [(Hf & b & m & Hin & Hr) | [(b & m & Hin & _ & Hr) | (cid & pos & Hin & Hz)]]].
- left; exact H.
- right; left. exists b, m. auto.
- right; left. exists b, m. auto.
- right; right. exists cid, pos. split; [rewrite Hfrs; apply in_or_app; left; exact Hin|].
  destruct Hz as [Hz | Hz]; [exact Hz|]. exfalso.
  assert (Hin2 : In (cid, pos) (frames (o_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos HAR Hin2) as (Hf4 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold in_zr, shadow_addr, SHADOW_OFF in Hz. cbn [fst snd] in Hz.
  assert (D1 : frame_addr (o_lyc cx) cid pos / 8 + fs_frame_bytes cid / 8 <= alloc_ceiling / 8).
  { set (f := frame_addr (o_lyc cx) cid pos) in *. set (b := fs_frame_bytes cid) in *.
    pose proof (Z.div_mod f 8 ltac:(lia)). pose proof (Z.mod_pos_bound f 8 ltac:(lia)).
    pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)). pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(lia)).
    nia. }
  assert (D2 : 512 <= frame_addr (o_lyc cx) cid pos / 8) by (apply Z.div_le_lower_bound; lia).
  assert (D3 : alloc_ceiling / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  unfold amem_range in Ham. rewrite C3, C4, C5 in Ham. lia.
Qed.
Lemma oc_twr_fresh : forall cx q n x,
  oc_pre B GLYPHA ROSTRS cx ->
  twr_ok tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_lyc cx) (o_Sc cx) (o_own cx) (o_W cx) (o_memc cx)
    (spZ (o_regs cx)) q n ->
  amem_range q n -> q <= x < q + n -> cw_fresh B (o_lyc cx) (o_Sc cx) x -> False.
Proof.
intros cx q n x Hpre Htw Ham Hx (Hlo & _ & Hbl & Hfr).
pose proof Hpre as ((HJ0 & _) & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hlo2 & _).
destruct (oc_twr_cases cx q n x Hpre Htw Ham Hx) as [H | [(b & m & Hin & Hr) | (cid & pos & Hin & Hz)]].
- lia.
- exact (Hbl b m (x - b) Hin ltac:(lia) ltac:(lia)).
- exact (proj1 (Hfr cid pos Hin) Hz).
Qed.
Lemma oc_twr_not_img : forall cx q n x,
  oc_pre B GLYPHA ROSTRS cx ->
  twr_ok tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_lyc cx) (o_Sc cx) (o_own cx) (o_W cx) (o_memc cx)
    (spZ (o_regs cx)) q n ->
  amem_range q n -> q <= x < q + n -> ~ in_img tfibsegs x.
Proof.
intros cx q n x Hpre Htw Ham Hx Himg.
pose proof Hpre as ((HJ0 & _) & _).
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hlo2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (tfib_segs_low x Himg) as Hlow. unfold kLowMemEnd in Hlow.
destruct (oc_twr_cases cx q n x Hpre Htw Ham Hx) as [H | [(b & m & Hin & Hr) | (cid & pos & Hin & Hz)]].
- lia.
- eapply (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low (o_lyc cx) (o_Sc cx) _ _ _ x 1 x HAR); [| lia | exact Himg].
  intros a Ha. left. exists b, m. split; [exact Hin | lia].
- eapply (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low (o_lyc cx) (o_Sc cx) _ _ _ x 1 x HAR); [| lia | exact Himg].
  intros a Ha. right. exists cid, pos. split; [exact Hin|]. replace a with x by lia. exact Hz.
Qed.
End w.

Section w2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variable MT : ameter_ops.
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
(* the bytes the call writes stay present at the walk's later states (tcj_kept: off the call's window) *)
Lemma oc_pres_at : forall cx ly3 S3 W3 m3 md3 q n a,
  oc_pre B GLYPHA ROSTRS cx -> oc_st B MT cx ly3 S3 W3 m3 md3 ->
  twr_ok tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_lyc cx) (o_Sc cx) (o_own cx) (o_W cx) (o_memc cx)
    (spZ (o_regs cx)) q n ->
  amem_range q n -> coff_win (spZ (o_regs cx)) T_owed_counter_text q n -> 0 <= q -> q <= a < q + n ->
  apresent (w_H W3) m3 a.
Proof.
intros cx ly3 S3 W3 m3 md3 q n a Hpre Hst Htw Ham Hcw Hq Ha.
pose proof Hst as (HJ3 & Hfrs3 & _ & HPm & _ & _ & (_ & _ & _ & _ & K5 & _)).
pose proof (proj1 HJ3) as HAR3.
pose proof Hpre as ((HJ0 & _) & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTK & Hceil & Hlo2 & Hshi & H47 & _).
destruct (Htw a Ha) as (_ & Hp & _ & _).
destruct (oc_twr_cases B LAWS GLYPHA ROSTRS cx q n a Hpre Htw Ham Ha) as [Hs | [(b & m & Hin & Hr) | (cid & pos & Hin & Hz)]].
- apply K5; [lia | unfold coff_win in Hcw; lia | exact Hp].
- assert (Hin3 : In (b, m) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym HPm) Hin).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 m3 md3 b m HAR3 Hin3) as (_ & _ & _ & _ & Hpr & _).
  exact (proj1 (Hpr a ltac:(lia))).
- assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR3 Hin3) as (_ & _ & Hpr & _).
  destruct (oc_fa_eq B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx) (o_own cx)
    (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) (o_mdc cx) (o_k cx) _ _ _ _ _ _ _ HJ0 HJ3) as (EFA & _).
  unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
  exact (proj1 (Hpr a ltac:(rewrite EFA; lia))).
Qed.
(* their shadow marks too: the caller's stack allowance (its shadow is zero in every state), a heap block of the call
   state (its shadow law at the later state), or a side-stack frame of it (its shadow kept, tcj_kept) *)
Lemma oc_ra_at : forall cx ly3 S3 W3 m3 md3 q n,
  oc_pre B GLYPHA ROSTRS cx -> oc_st B MT cx ly3 S3 W3 m3 md3 ->
  twr_ok tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_lyc cx) (o_Sc cx) (o_own cx) (o_W cx) (o_memc cx)
    (spZ (o_regs cx)) q n ->
  amem_range q n ->
  range_addressable (aview tfibsegs (w_H (o_W cx)) (o_memc cx)) SHADOW_OFF q n ->
  range_addressable (aview tfibsegs (w_H W3) m3) SHADOW_OFF q n.
Proof.
intros cx ly3 S3 W3 m3 md3 q n Hpre Hst Htw Ham Hra x Hx.
pose proof Hst as (HJ3 & Hfrs3 & _ & HPm & _ & _ & (_ & _ & _ & K4 & _)).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpre as (HE & _ & _ & _ & _ & _ & Hdsg & _ & _ & _ & Hdt & _).
destruct (oc_twr_cases B LAWS GLYPHA ROSTRS cx q n x Hpre Htw Ham Hx) as [Hs | [(b & m & Hin & Hr) | (cid & pos & Hin & Hz)]].
- (* the caller's stack allowance: zero shadow (AR_zshadow_law's stack row) *)
  pose proof Hstk as (_ & _ & _ & Hslo & Hshi & _).
  pose proof (al_zshadow _ _ LAWS ly3 S3 W3 m3 md3 _ HAR3 (or_introl eq_refl)) as Hz. cbn [fst snd] in Hz.
  pose proof HAR3 as (M & _). pose proof (lo_top _ (am_layout _ _ _ _ M)) as (_ & _ & _ & _ & Tlo & Thi & _).
  unfold page_aligned in Tlo, Thi.
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  rewrite Eslo in Tlo, Hz. rewrite Eshi in Thi, Hz.
  set (lo := ly_stk_lo (o_ly cx)) in *. set (hi := ly_stk_hi (o_ly cx)) in *.
  assert (Dlo : lo = 4096 * (lo / 4096)) by (pose proof (Z.div_mod lo 4096 ltac:(lia)); lia).
  assert (Dhi : hi = 4096 * (hi / 4096)) by (pose proof (Z.div_mod hi 4096 ltac:(lia)); lia).
  assert (L8 : lo / 8 = 512 * (lo / 4096)).
  { transitivity (((512 * (lo / 4096)) * 8) / 8); [f_equal; lia | apply Z.div_mul; lia]. }
  assert (E8 : (hi - lo) / 8 = 512 * (hi / 4096 - lo / 4096)).
  { transitivity (((512 * (hi / 4096 - lo / 4096)) * 8) / 8); [f_equal; lia | apply Z.div_mul; lia]. }
  assert (Hlx : lo <= x) by (clear - Hs Hslo; lia).
  assert (Hxh : x < hi) by (clear - Hs Hshi; lia).
  exists 0. split; [|left; reflexivity].
  assert (Y1 : 512 * (lo / 4096) <= x / 8) by (apply Z.div_le_lower_bound; [lia | clear - Dlo Hlx; lia]).
  assert (Y2 : x / 8 < 512 * (hi / 4096)) by (apply Z.div_lt_upper_bound; [lia | clear - Dhi Hxh; lia]).
  assert (Hi : 0 <= x / 8 - lo / 8 < (hi - lo) / 8) by (clear - Y1 Y2 L8 E8; lia).
  pose proof (Hz _ Hi) as H0. unfold shadow_of_addr in H0 |- *.
  replace (SHADOW_OFF + lo / 8 + (x / 8 - lo / 8)) with (SHADOW_OFF + x / 8) in H0 by ring. exact H0.
- (* a heap block of the call state *)
  assert (Hin3 : In (b, m) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym HPm) Hin).
  exact (range_addressable_of_block tfibsegs B LAWS ly3 S3 W3 m3 md3 b m x 1 HAR3 Hin3 ltac:(lia) ltac:(lia) x ltac:(lia)).
- (* a side-stack frame of the call state: its shadow kept *)
  destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  pose proof (proj1 HE) as HJ0. pose proof (proj1 HJ0) as HAR.
  destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf4096 & Hfceil & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (Hfal & _).
  pose proof HAR as (Me & _).
  assert (Hcid : 0 <= cid) by (first [ destruct (YG0s.frame_facts _ _ _ _ _ _ Me Hin) as (Hc & _); lia
                                     | destruct (YG0s.frame_facts _ _ _ _ _ _ _ Me Hin) as (Hc & _); lia
                                     | destruct (YG0s.frame_facts _ _ _ _ _ _ _ _ Me Hin) as (Hc & _); lia ]).
  assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
  { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
    replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z_mod_mult. }
  assert (Hf8 : frame_addr (o_lyc cx) cid pos mod 8 = 0).
  { pose proof (Z.div_mod (frame_addr (o_lyc cx) cid pos) 32 ltac:(lia)) as D. rewrite Hfal, Z.add_0_r in D.
    rewrite D. replace (32 * (frame_addr (o_lyc cx) cid pos / 32)) with ((4 * (frame_addr (o_lyc cx) cid pos / 32)) * 8) by lia.
    apply Z_mod_mult. }
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
  set (f := frame_addr (o_lyc cx) cid pos) in *. set (bs := fs_frame_bytes cid) in *.
  pose proof (Z.div_mod f 8 ltac:(lia)) as Df. pose proof (Z.div_mod bs 8 ltac:(lia)) as Db.
  assert (Hq : f / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (Hq2 : x / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia).
  assert (Hx47 : 0 <= x / 8 < 2 ^ 44).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | unfold amem_range in Ham; rewrite C3, C4, C5 in Ham; lia]]. }
  (* the shadow byte is not a byte the call writes (those are application memory) *)
  assert (HnE : ~ oc_E cx (shadow_of_addr SHADOW_OFF x)).
  { pose proof Hdsg as (_ & _ & _ & _ & _ & _ & Hamg & _).
    assert (Hamd : amem_range (o_dt cx) 1)
      by (destruct Hdt as [((_ & _ & _ & _ & _ & _ & Hm & _) & _) | (_ & _ & _ & _ & _ & _ & _ & Hm & _)]; exact Hm).
    unfold oc_E, shadow_of_addr, amem_range in *. rewrite C3, C4, C5 in *.
    change SHADOW_OFF with 2147450880 in *. lia. }
  rewrite <- Hsv. unfold aview in *.
  pose proof (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin) as K. unfold aview in K. apply K; [|exact HnE].
  right. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. subst f bs. lia.
Qed.
End w2.
