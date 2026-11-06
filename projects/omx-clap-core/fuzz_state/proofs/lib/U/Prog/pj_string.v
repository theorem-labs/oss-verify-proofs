From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memset_c fuzz_strdup_c pj_string_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
Module YK11 := YK11.
Module YM05 := YM05.
Module strtod_c := U.Prog.strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition SD_RET : Z := 0x14cb0.
Lemma str_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Definition EMPTY_STR : Z := 0x102f5.
Definition sarg (s : Z) : Z := if s =? 0 then EMPTY_STR else s.
Lemma rw_cells_stk : forall m A cs, rw_cells rsegs m A cs -> stk rsegs m A (A + Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [[Hwf (H0 & H1 & HB)] (W0 & W1 & HW)].
  rewrite cells_bytes_length in HB by exact Hwf.
  split; [lia|]. split; [lia|]. intros a Ha. split.
  - replace a with (A + (a - A)) by lia. apply HW. lia.
  - pose proof (HB (Z.to_nat (a - A)) ltac:(lia)) as E.
    replace (A + Z.of_nat (Z.to_nat (a - A))) with a in E by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) as [b|] eqn:N; [exists b; exact E|].
    apply nth_error_None in N. rewrite cells_bytes_length in N by exact Hwf. lia.
Qed.


Definition seg1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo v s : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte) (junk : list byte),
    ms = MS (mkR (Z_to_bv 64 SD_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 v)
               (Z_to_bv 64 (sarg s)) (Z_to_bv 64 (sarg s)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6) F (Z_to_bv 64 FUZZ_STRDUP) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -32, bv_unsigned sp); (v, v + 56)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -32) /\
    rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] /\
    stk rsegs m1 v (v + 56) /\
    bytes_at rsegs m1 v (le4 (Z_to_bv 64 4) ++ repeat (Z_to_bv 8 0) 52).

Lemma seg1 : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo v s : Z),
    a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 s -> v <> 0 -> v mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    stk rsegs m v (v + 56) -> (v + 56 <= lo \/ bv_unsigned sp <= v) ->
    mem_inv rsegs m -> 0 <= s < 2 ^ 64 ->
    evt rsegs (seg1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo v s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PJ_STRING) fc None m (seg_rom rsegs)).
Proof.
  intros HMS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v s
    A0 A1 VNZ V8 ST LO VS VD MI SR. subst a0 a1.
  unfold PJ_STRING.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (v, v + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof VS as (VS1 & VS2 & _).
  destruct (stk_carve rsegs m v (v + 56) 56 VS ltac:(lia)) as [_ [jv FV]].
  replace (v + 56 - Z.of_nat 56) with v in FV by lia.
  carve_frame 32%nat ST.
  do 9 step.
  assert (FV' : rw_cells rsegs m0 (bv_unsigned (Z_to_bv 64 v)) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) jv])
    by (rewrite !unsigned_lit by lia; exact FV).
  eapply evt_cut; [apply (HMS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jv FV' MI)|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & E & MU1 & WM1 & MI1 & RW1).
  subst ms'. rewrite !unsigned_lit in MU1, RW1 by lia.
  change (Z.to_nat 56) with 56%nat in RW1. change (0 mod 256) with 0 in RW1.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR1.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST MU1 WM1 ltac:(cbn [disjoint_from]; lia)) as ST1.
  assert (MU2 : munch [(bv_unsigned sp + -32, bv_unsigned sp); (v, v + 56)] m m1)
    by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU1]; unfold sub_fp; cbn [outside]; intros; lia).
  pose proof (wmono_trans rsegs _ _ _ WM WM1) as WM2.
  clear FR ST MU WM MU1 WM1 FV FV' MI VS.
  replace (ret_pc (Z_to_bv 64 0x14c88)) with (Z_to_bv 64 0x14c88) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. if_cases HB0; [zify_cond HB0; rewrite ?(unsigned_lit v) in HB0 by lia; lia|].
  step. step. if_cases HB1.
  { zify_cond HB1. rewrite ?(unsigned_lit v) in HB1 by lia. rewrite ?str_land7 in HB1.
    rewrite ?unsigned_lit in HB1 by (pose proof (Z.mod_pos_bound v 8 ltac:(lia)); lia). first [contradiction | lia]. }
  do 3 step.
  assert (Z0 : skipn 4 (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) 56) = repeat (Z_to_bv 8 0) 52)
    by (vm_compute; reflexivity).
  rewrite Z0 in RW1.
  pose proof (rw_cells_stk _ _ _ RW1) as VS3. cbn [cells_size csize Nat.add] in VS3.
  pose proof (proj2 (proj1 RW1)) as VB3. cbn [cells_bytes cbytes] in VB3. rewrite app_nil_r in VB3.
  replace (v + Z.of_nat 56) with (v + 56) in VS3 by lia.
  if_cases HC; zify_cond HC.
  - assert (SA : sarg s = s) by (unfold sarg; destruct (Z.eqb_spec s 0); [exfalso; lia | reflexivity]).
    do 2 step. apply evt_done. unfold seg1_post. rewrite SA.
    do 16 eexists. split; [reflexivity|].
    exact (conj MU2 (conj WM2 (conj MI1 (conj ST1 (conj FR1 (conj VS3 VB3)))))).
  - assert (S0 : s = 0) by lia. subst s.
    do 4 step. apply evt_done. unfold seg1_post.
    do 16 eexists. split; [reflexivity|].
    exact (conj MU2 (conj WM2 (conj MI1 (conj ST1 (conj FR1 (conj VS3 VB3)))))).
Qed.

Definition sres (res : Z) : Z := if res =? 0 then -1 else 0.

Lemma sres_lit : forall res, 0 <= res < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 res)) + -1) = Z_to_bv 64 (sres res).
Proof.
  intros res R. rewrite v_sltu_b2z. rewrite !(unsigned_lit 0), (unsigned_lit res) by lia. unfold sres.
  destruct (Z.ltb_spec 0 res); destruct (Z.eqb_spec res 0); try lia; cbn [Z.b2z];
    rewrite unsigned_lit by lia; reflexivity.
Qed.

Definition seg2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v res : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sres res)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
    munch [(v + 16, v + 24)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
    bytes_at rsegs m1 (v + 16) (le8 (Z_to_bv 64 res)).

Lemma seg2 :
  forall (ra1 spr sp gp tp t0 t1 t2 s0r s1x a0r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v res : Z) (ra s0 s1 : word) (junk : list byte),
    spr = Z_to_bv 64 (bv_unsigned sp + -32) -> s0r = Z_to_bv 64 v -> a0r = Z_to_bv 64 res ->
    rw_cells rsegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m (v + 16) (v + 24) -> (v + 24 <= bv_unsigned sp + -32 \/ bv_unsigned sp <= v + 16) ->
    32 <= bv_unsigned sp ->
    mem_inv rsegs m -> 0 <= res < 2 ^ 64 ->
    evt rsegs (seg2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v res m)
      (MS (mkR ra1 spr gp tp t0 t1 t2 s0r s1x a0r a1 a2 a3 a4
               a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SD_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 spr sp gp tp t0 t1 t2 s0r s1x a0r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v res
    ra s0 s1 junk ESP ES0 EA0 FR VS VD SP MI RR. subst spr s0r a0r.
  unfold SD_RET.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof VS as (VS1 & VS2 & _).
  destruct (stk_carve rsegs m (v + 16) (v + 24) 8 VS ltac:(lia)) as [_ [jv FV]].
  replace (v + 24 - Z.of_nat 8) with (v + 16) in FV by lia.
  pose proof (munch_refl [(v + 16, v + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HS : store_ok rsegs m (wa (v + 16)) 8 = true).
  { rewrite <- (Z.add_0_r (v + 16)) at 1. apply (wr_at_store_ok rsegs m (v + 16) 8 0 8); [|lia|cbn; lia].
    exact (proj2 FV). }
  clear VS.
  do 3 step.
  rewrite (sres_lit res RR).
  do 6 step.
  pose proof (proj2 (proj1 FV)) as BV. cbn [cells_bytes cbytes] in BV. rewrite app_nil_r in BV.
  apply evt_done. unfold seg2_post. do 15 eexists. split; [reflexivity|].
  exact (conj MU (conj WM (conj MI BV))).
Qed.

Section Tr.
Variable sg : list Segment.

Lemma mbyte_mrd : forall m a, mbyte sg m a = mrd sg m (wa a).
Proof. reflexivity. Qed.

Lemma bytes_frame : forall m m' a bs, bytes_at sg m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte sg m' (a + i) = mbyte sg m (a + i)) -> bytes_at sg m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (E (Z.of_nat i) ltac:(lia)) as Ei. rewrite !mbyte_mrd in Ei. rewrite Ei. exact (H i Hi).
Qed.

Lemma wr_frame : forall m m' a n, wr_at sg m a n ->
  (forall i, 0 <= i < n -> writable_at sg m (a + i) -> writable_at sg m' (a + i)) -> wr_at sg m' a n.
Proof.
  intros m m' a n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (E i Hi (H i Hi)).
Qed.

Lemma stk_frame : forall m m' lo hi, stk sg m lo hi ->
  (forall a, lo <= a < hi -> mbyte sg m' a = mbyte sg m a /\ (writable_at sg m a -> writable_at sg m' a)) ->
  stk sg m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W [b R]]. destruct (E a Ha) as [Eb Ew]. split; [exact (Ew W)|].
  exists b. rewrite <- mbyte_mrd in R |- *. rewrite Eb. exact R.
Qed.

Lemma rw_frame : forall m m' A cs, rw_cells sg m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     mbyte sg m' (A + i) = mbyte sg m (A + i) /\ (writable_at sg m (A + i) -> writable_at sg m' (A + i))) ->
  rw_cells sg m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] E. split; [split; [exact Hwf|]|].
  - apply (bytes_frame m); [exact HB|]. intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf. exact (proj1 (E i Hi)).
  - apply (wr_frame m); [exact HW|]. intros i Hi. exact (proj2 (E i Hi)).
Qed.

Lemma stk_rel : forall m m0 lo hi, mem_rel sg m m0 -> stk sg m0 lo hi -> stk sg m lo hi.
Proof.
  intros m m0 lo hi HR (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W [b R]]. split.
  - rewrite <- (wview_rel_rw sg m m0 _ HR (ro_false_of_wview sg m m0 _ HR W)). exact W.
  - exists b. rewrite (mrd_rel sg m m0 _ HR). exact R.
Qed.

Lemma rw_rel : forall m m0 A cs, mem_rel sg m m0 -> rw_cells sg m0 A cs -> rw_cells sg m A cs.
Proof.
  intros m m0 A cs HR [[Hwf HB] HW].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel sg m m0 A _ HR) HB)] | exact (wr_at_rel sg m m0 A _ HR HW)].
Qed.

Lemma stk_norm : forall m lo hi, ro_agree sg m -> (forall a, lo <= a < hi -> ro_addr sg (wa a) = false) ->
  stk sg m lo hi -> stk sg (normalize sg m) lo hi.
Proof.
  intros m lo hi Hro Hf (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W [b R]]. pose proof (mem_rel_normalize sg m Hro) as HR. split.
  - rewrite (wview_rel_rw sg m (normalize sg m) _ HR (Hf a Ha)). exact W.
  - exists b. rewrite <- (mrd_rel sg m (normalize sg m) _ HR). exact R.
Qed.

Lemma rw_norm : forall m A cs, ro_agree sg m ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr sg (wa (A + i)) = false) ->
  rw_cells sg m A cs -> rw_cells sg (normalize sg m) A cs.
Proof.
  intros m A cs Hro Hf [[Hwf HB] HW].
  split; [split; [exact Hwf | exact (bytes_at_normalize sg m A _ Hro HB)] |].
  exact (wr_at_norm sg m (normalize sg m) A _ (mem_rel_normalize sg m Hro) HW Hf).
Qed.

Lemma stk_patch : forall m m' lo hi W, stk sg m lo hi -> munch W m m' -> wmono sg m m' ->
  (forall a, lo <= a < hi -> ~ outside W a -> exists b, mrd sg m' (wa a) = Some b) -> stk sg m' lo hi.
Proof.
  intros m m' lo hi W (H0 & H1 & H) MU WM P. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Wv [b R]]. split; [exact (WM _ Wv)|].
  destruct (kb_outside_dec W a) as [O|O].
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact R|]. rewrite wa_unsigned by lia. exact O.
  - exact (P a Ha O).
Qed.

Lemma present_of_wview : forall m x, 0 <= x < 2 ^ 64 -> find_segment sg x 1 = None ->
  wview sg m (Z_to_bv 64 x) <> None -> present m x.
Proof.
  intros m x Hx F W. unfold present. revert W. unfold wview.
  destruct (m (Z_to_bv 64 x)) as [b|]; intros W; [exists b; reflexivity|].
  rewrite unsigned_lit in W by lia. rewrite F in W. contradiction.
Qed.

Lemma ro_false_of_noseg : forall x, 0 <= x < 2 ^ 64 -> find_segment sg x 1 = None -> ro_addr sg (wa x) = false.
Proof. intros x Hx F. unfold ro_addr, wa. rewrite unsigned_lit by lia. rewrite F. reflexivity. Qed.

End Tr.

Lemma pw_app : forall (R : Z * Z -> Z * Z -> Prop) b1 y b2 x, pairwise R (b1 ++ y :: b2) -> In x (b1 ++ b2) ->
  R x y \/ R y x.
Proof.
  induction b1 as [|z b1 IH]; intros y b2 x H Hx; cbn in H, Hx.
  - destruct H as [H _]. right. apply H. exact Hx.
  - destruct H as [Hz H]. destruct Hx as [<- | Hx].
    + left. apply Hz. apply in_or_app. right. left. reflexivity.
    + exact (IH y b2 x H Hx).
Qed.

Lemma pw_in2 : forall (R : Z * Z -> Z * Z -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  induction l as [|z l IH]; intros x y H Hx Hy Hne; cbn in *; [contradiction|].
  destruct H as [Hz H]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - left. exact (Hz y Hy).
  - right. exact (Hz x Hx).
  - exact (IH x y H Hx Hy Hne).
Qed.

Definition seg_cover (sl : list Segment) : bool :=
  forallb (fun g => existsb (fun r => (bv_unsigned (fst r) <=? Z.of_N (seg_base g)) &&
    (Z.of_N (seg_base g) + Z.of_N (seg_size g) <=? bv_unsigned (fst r) + bv_unsigned (snd r))) (segments_reserved sl)) sl.

Lemma seg_cover_rsegs : seg_cover rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_reserved : forall x, find_segment rsegs x 1 <> None ->
  rsegs <> [] /\ exists r, In r (segments_reserved rsegs) /\ bv_unsigned (fst r) <= x < bv_unsigned (fst r) + bv_unsigned (snd r).
Proof.
  intros x H. destruct (find_segment rsegs x 1) as [g|] eqn:F; [|contradiction].
  destruct (kb_find_segment rsegs x 1 g F) as (Hin & H1 & H2).
  pose proof seg_cover_rsegs as C. unfold seg_cover in C. rewrite forallb_forall in C. specialize (C g Hin).
  apply existsb_exists in C as (r & Hr & Hc). apply andb_prop in Hc as [Ha Hb]. apply Z.leb_le in Ha, Hb.
  split; [|exists r; split; [exact Hr | lia]].
  intros E. rewrite E in Hin. destruct Hin.
Qed.

Lemma empty_str_ro : forall i, (i < 8)%nat -> ro_addr rsegs (wa (EMPTY_STR + Z.of_nat i)) = true.
Proof. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.

Definition EMPTY_SLACK : list byte :=
  [Z_to_bv 8 0x2e; Z_to_bv 8 0; Z_to_bv 8 0x73; Z_to_bv 8 0x74; Z_to_bv 8 0x61; Z_to_bv 8 0x74; Z_to_bv 8 0x65].

Lemma empty_str_bytes : forall m, ro_agree rsegs m -> bytes_at rsegs m EMPTY_STR (Z_to_bv 8 0 :: EMPTY_SLACK).
Proof.
  intros m H. unfold EMPTY_SLACK. split; [unfold EMPTY_STR; lia|]. split; [cbn [length]; unfold EMPTY_STR; lia|].
  intros i Hi. cbn [length] in Hi. rewrite (H _ (empty_str_ro i Hi)).
  do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma stk_sub : forall sg m lo hi lo' hi', stk sg m lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo' -> stk sg m lo' hi'.
Proof.
  intros sg m lo hi lo' hi' (H0 & H1 & H) L1 L2 L3. split; [exact L3|]. split; [lia|]. intros a Ha. apply H. lia.
Qed.

Lemma z8_id : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma zb_map : forall cs, map (Z_to_bv 8) (zb cs) = cs.
Proof. intros cs. unfold zb. rewrite map_map. rewrite (map_ext _ (fun b => b)) by exact z8_id. apply map_id. Qed.

Lemma zb_pos : forall cs, ~ In (Z_to_bv 8 0) cs -> Forall (fun c => 0 < c < 256) (zb cs).
Proof.
  intros cs H. unfold zb. rewrite Forall_forall. intros c Hc. apply in_map_iff in Hc as (bt & <- & Hbt).
  pose proof (bv_unsigned_in_range 8 bt) as R. unfold bv_modulus in R. cbn in R.
  destruct (Z.eq_dec (bv_unsigned bt) 0) as [E|E]; [|lia].
  exfalso. apply H. assert (EB : bt = Z_to_bv 8 0) by (rewrite <- (z8_id bt), E; reflexivity). rewrite <- EB. exact Hbt.
Qed.

Definition HDR_SPLIT : list byte :=
  le4 (Z_to_bv 64 4) ++ repeat (Z_to_bv 8 0) 4 ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++
  le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0).

Lemma hdr_split_eq : le4 (Z_to_bv 64 4) ++ repeat (Z_to_bv 8 0) 52 = HDR_SPLIT.
Proof. vm_compute. reflexivity. Qed.

Lemma hdr_split : forall sg m v w, bytes_at sg m v (le4 (Z_to_bv 64 4) ++ repeat (Z_to_bv 8 0) 52) ->
  bytes_at sg m v (le4 (Z_to_bv 64 4)) /\ bytes_at sg m (v + 4) (repeat (Z_to_bv 8 0) 4) /\
  bytes_at sg m (v + 8) (le8 (Z_to_bv 64 0)) /\ (w = 0 -> bytes_at sg m (v + 16) (le8 (Z_to_bv 64 w))) /\
  bytes_at sg m (v + 24) (le8 (Z_to_bv 64 0)) /\ bytes_at sg m (v + 32) (le8 (Z_to_bv 64 0)) /\
  bytes_at sg m (v + 40) (le8 (Z_to_bv 64 0)) /\ bytes_at sg m (v + 48) (le8 (Z_to_bv 64 0)).
Proof.
  intros sg m v w H. rewrite hdr_split_eq in H. unfold HDR_SPLIT in H.
  apply bytes_at_app in H as [H1 H]. rewrite length_le4 in H.
  apply bytes_at_app in H as [H2 H]. rewrite repeat_length in H.
  apply bytes_at_app in H as [H3 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H4 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H5 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H6 H]. rewrite length_le8 in H.
  apply bytes_at_app in H as [H7 H8]. rewrite length_le8 in H8.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
  split; [exact H1|]. split; [exact H2|].
  split; [replace (v + 8) with (v + 4 + 4) by lia; exact H3|].
  split; [intros ->; replace (v + 16) with (v + 4 + 4 + 8) by lia; exact H4|].
  split; [replace (v + 24) with (v + 4 + 4 + 8 + 8) by lia; exact H5|].
  split; [replace (v + 32) with (v + 4 + 4 + 8 + 8 + 8) by lia; exact H6|].
  split; [replace (v + 40) with (v + 4 + 4 + 8 + 8 + 8 + 8) by lia; exact H7|].
  replace (v + 48) with (v + 4 + 4 + 8 + 8 + 8 + 8 + 8) by lia; exact H8.
Qed.

Lemma hdr_join : forall sg m v,
  bytes_at sg m v (le4 (Z_to_bv 64 4)) -> bytes_at sg m (v + 4) (repeat (Z_to_bv 8 0) 4) ->
  bytes_at sg m (v + 8) (le8 (Z_to_bv 64 0)) -> bytes_at sg m (v + 16) (le8 (Z_to_bv 64 0)) ->
  bytes_at sg m (v + 24) (le8 (Z_to_bv 64 0)) -> bytes_at sg m (v + 32) (le8 (Z_to_bv 64 0)) ->
  bytes_at sg m (v + 40) (le8 (Z_to_bv 64 0)) -> bytes_at sg m (v + 48) (le8 (Z_to_bv 64 0)) ->
  bytes_at sg m v (le4 (Z_to_bv 64 4) ++ repeat (Z_to_bv 8 0) 52).
Proof.
  intros sg m v H1 H2 H3 H4 H5 H6 H7 H8. rewrite hdr_split_eq. unfold HDR_SPLIT.
  apply bytes_at_app. split; [exact H1|]. rewrite length_le4.
  apply bytes_at_app. split; [exact H2|]. rewrite repeat_length.
  apply bytes_at_app. split; [replace (v + Z.of_nat 4 + Z.of_nat 4) with (v + 8) by lia; exact H3|]. rewrite length_le8.
  apply bytes_at_app. split; [replace (v + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8) with (v + 16) by lia; exact H4|].
  rewrite length_le8.
  apply bytes_at_app. split; [replace (v + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + Z.of_nat 8) with (v + 24) by lia; exact H5|].
  rewrite length_le8.
  apply bytes_at_app.
  split; [replace (v + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (v + 32) by lia; exact H6|].
  rewrite length_le8.
  apply bytes_at_app.
  split; [replace (v + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (v + 40) by lia;
          exact H7|].
  rewrite length_le8.
  replace (v + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (v + 48)
    by lia. exact H8.
Qed.

Ltac psv HRP Hg1 rp r :=
  transitivity (YK11.getr rp (Z_to_bv 5 r)); [reflexivity|];
  rewrite (HRP r ltac:(unfold callee_saved; lia)), Hg1; reflexivity.

Ltac trb P MU :=
  apply (bytes_at_transport rsegs _ _ _ _ _ P MU); cbn [Frame.disjoint_from];
  rewrite ?length_le4, ?length_le8, ?repeat_length; lia.

Section Main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HMS : memset_contract.
Hypothesis HSD : fuzz_strdup_contract B API RF.

Lemma blk_user : forall L A a k, In (a, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = a.
Proof.
  intros L A a k H. unfold blocks in H. apply in_map_iff in H as ([q n] & E & Hq). cbn [fst snd] in E.
  injection E as E1 E2. subst. exists q. split; [exact Hq | reflexivity].
Qed.

Lemma blk_range : forall L A m md a k, aa_MR API L A m md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= YM05.alloc_ceiling.
Proof.
  intros L A m md a k HM H. destruct (blk_user L A a k H) as (q & Hq & <-).
  exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq).
Qed.

Definition K1 (regs : bvmap 5 word) (mem : word -> option byte) (v s : Z) (R : bvmap 5 word) (pc : word)
    (m1 : word -> option byte) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
    R = mkR (Z_to_bv 64 SD_RET) (Z_to_bv 64 (spZ regs + -32)) (YK11.getr regs 3) (YK11.getr regs 4) t0 t1 t2 (Z_to_bv 64 v)
          (Z_to_bv 64 (sarg s)) (Z_to_bv 64 (sarg s)) a1 a2 a3 a4 a5 a6 a7 (YK11.getr regs 18) (YK11.getr regs 19) (YK11.getr regs 20)
          (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27)
          t3 t4 t5 t6 /\
    pc = Z_to_bv 64 FUZZ_STRDUP /\
    munch [(spZ regs + -32, spZ regs); (v, v + 56)] mem m1 /\ wmono rsegs mem m1 /\ ro_same rsegs mem m1 /\
    stk rsegs m1 (spZ regs - PJ_STRING_K) (spZ regs + -32) /\
    rw_cells rsegs m1 (spZ regs + -32) [CB 8 junk; C8 (YK11.getr regs 9); C8 (YK11.getr regs 8); C8 (YK11.getr regs 1)] /\
    stk rsegs m1 v (v + 56) /\
    bytes_at rsegs m1 v (le4 (Z_to_bv 64 4) ++ repeat (Z_to_bv 8 0) 52).

Lemma wx_rsegs : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma run1 : forall regs mem v s,
  ms_segs B = rsegs -> ro_agree rsegs mem ->
  YK11.getr regs 10 = Z_to_bv 64 v -> YK11.getr regs 11 = Z_to_bv 64 s -> v <> 0 -> v mod 8 = 0 ->
  stk rsegs (normalize rsegs mem) (spZ regs - PJ_STRING_K) (spZ regs) ->
  stk rsegs (normalize rsegs mem) v (v + 56) ->
  (v + 56 <= spZ regs - PJ_STRING_K \/ spZ regs <= v) -> 0 <= s < 2 ^ 64 ->
  Exec.evt (ms_segs B) (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom (ms_segs B)) /\
      K1 regs mem v s R pc' mem')
    (MState.MS (rmk regs) fp_regs (Z_to_bv 64 PJ_STRING) fp_csr None mem (seg_rom (ms_segs B))).
Proof.
  intros regs mem v s HSEG ROA R10 R11 VNZ V8 ST VS VD SR. rewrite HSEG.
  unfold PJ_STRING_K, PJ_STRING_F, STRDUP_K, ALLOC_STACK in *.
  eapply evt_mono.
  { eapply (evt_normalize rsegs); [exact wx_rsegs | exact ROA |].
    unfold rmk.
    apply (seg1 HMS); [exact R10 | exact R11 | exact VNZ | exact V8 | exact ST | unfold spZ in *; lia | exact VS |
      unfold spZ in *; lia | apply mem_inv_normalize | exact SR]. }
  intros ms (s0 & Q0 & Hrel & Hsame).
    destruct Q0 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & junk & -> & MU & WM & MI & ST1 &
                    FR & VS1 & VB).
    destruct ms as [r1 f1 p1 sv1 rv1 fc1 mm1 ro1].
    destruct Hrel as (Hr & Hf & Hp & Hsv & Hrs & Hfc & Hro & Hm). cbn in Hr, Hf, Hp, Hsv, Hrs, Hfc, Hro, Hm, Hsame. subst.
    pose proof (mem_rel_normalize rsegs mem ROA) as HR0.
    exists (mkR (Z_to_bv 64 SD_RET) (Z_to_bv 64 (bv_unsigned (YK11.getr regs 2) + -32)) (YK11.getr regs 3) (YK11.getr regs 4) t0 t1 t2
              (Z_to_bv 64 v) (Z_to_bv 64 (sarg s)) (Z_to_bv 64 (sarg s)) a1 a2 a3 a4 a5 a6 a7 (YK11.getr regs 18) (YK11.getr regs 19)
              (YK11.getr regs 20) (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25) (YK11.getr regs 26)
              (YK11.getr regs 27) t3 t4 t5 t6), (Z_to_bv 64 FUZZ_STRDUP), mm1.
    split; [reflexivity|].
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, junk.
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) mm1 m1 HR0 Hm Hsame MU)|].
    split; [exact (wmono_rel rsegs mem (normalize rsegs mem) mm1 m1 HR0 Hm Hsame WM)|].
    split; [exact Hsame|].
    split; [exact (stk_rel rsegs mm1 m1 _ _ Hm ST1)|].
    split; [exact (rw_rel rsegs mm1 m1 _ _ Hm FR)|].
    split; [exact (stk_rel rsegs mm1 m1 _ _ Hm VS1)|].
    exact (proj2 (bytes_at_rel rsegs mm1 m1 _ _ Hm) VB).
Qed.

Definition K2 (regs' : bvmap 5 word) (mem' : word -> option byte) (v res : Z) (sp ra s0 s1 : word)
    (R : bvmap 5 word) (pc : word) (m : word -> option byte) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    R = mkR ra sp (YK11.getr regs' 3) (YK11.getr regs' 4) t0 t1 t2 s0 s1 (Z_to_bv 64 (sres res)) a1 a2 a3 a4 a5 a6 a7
          (YK11.getr regs' 18) (YK11.getr regs' 19) (YK11.getr regs' 20) (YK11.getr regs' 21) (YK11.getr regs' 22) (YK11.getr regs' 23)
          (YK11.getr regs' 24) (YK11.getr regs' 25) (YK11.getr regs' 26) (YK11.getr regs' 27) t3 t4 t5 t6 /\
    pc = ret_pc ra /\
    munch [(v + 16, v + 24)] mem' m /\ wmono rsegs mem' m /\ ro_same rsegs mem' m /\
    bytes_at rsegs m (v + 16) (le8 (Z_to_bv 64 res)).

Lemma run2 : forall regs' mem' v res (sp ra s0 s1 : word) junk,
  ms_segs B = rsegs -> ro_agree rsegs mem' ->
  YK11.getr regs' 2 = Z_to_bv 64 (bv_unsigned sp + -32) -> YK11.getr regs' 8 = Z_to_bv 64 v -> YK11.getr regs' 10 = Z_to_bv 64 res ->
  rw_cells rsegs (normalize rsegs mem') (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
  stk rsegs (normalize rsegs mem') (v + 16) (v + 24) ->
  (v + 24 <= bv_unsigned sp + -32 \/ bv_unsigned sp <= v + 16) -> 32 <= bv_unsigned sp -> 0 <= res < 2 ^ 64 ->
  Exec.evt (ms_segs B) (fun ms => exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom (ms_segs B)) /\
      K2 regs' mem' v res sp ra s0 s1 R pc' m')
    (MState.MS (rmk regs') fp_regs (Z_to_bv 64 SD_RET) fp_csr None mem' (seg_rom (ms_segs B))).
Proof.
  intros regs' mem' v res sp ra s0 s1 junk HSEG ROA G2 G8 G10 FR VS VD SP RR. rewrite HSEG.
  eapply evt_mono.
  { eapply (evt_normalize rsegs); [exact wx_rsegs | exact ROA |].
    unfold rmk.
    eapply (seg2 _ _ sp); [exact G2 | exact G8 | exact G10 | exact FR | exact VS | exact VD | exact SP |
                          apply mem_inv_normalize | exact RR]. }
  intros ms (s0' & Q0 & Hrel & Hsame).
  destruct Q0 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & -> & MU & WM & MI & BV).
  destruct ms as [r1 f1 p1 sv1 rv1 fc1 mm1 ro1].
  destruct Hrel as (Hr & Hf & Hp & Hsv & Hrs & Hfc & Hro & Hm). cbn in Hr, Hf, Hp, Hsv, Hrs, Hfc, Hro, Hm, Hsame. subst.
  pose proof (mem_rel_normalize rsegs mem' ROA) as HR0.
  eexists _, _, mm1. split; [reflexivity|].
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6.
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ mem' (normalize rsegs mem') mm1 m1 HR0 Hm Hsame MU)|].
  split; [exact (wmono_rel rsegs mem' (normalize rsegs mem') mm1 m1 HR0 Hm Hsame WM)|].
  split; [exact Hsame|].
  exact (proj2 (bytes_at_rel rsegs mm1 m1 _ _ Hm) BV).
Qed.

Theorem pj_string_holds : pj_string_contract B API RF.
Proof.
  unfold pj_string_contract.
  intros L A regs mem md Lam peak cnt fail b v s cs slack ENV LED RES R10 R11 VNZ PRW RPL VDJ STXT CSZ ROOM.
  destruct ENV as (HSEG & HTP & HERR & HGOT & HGRD & PRE & SPHI & GTOP & FRM & ROA & GOTW & GW).
  pose proof PRE as (HM & HWF & HBD & HRA & HAL & HCEIL & HSP63 & HSTK & HTPR & HERRW & HAUX).
  destruct RPL as (RPP & RPA & RPN).
  destruct PRW as (VAL & VSTK).
  pose proof YM05.alloc_ceiling_value as CV.
  pose proof (bv_unsigned_in_range 64 (YK11.getr regs 2)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold PJ_STRING_K, PJ_STRING_F, STRDUP_K, ALLOC_STACK in *.
  cbn [Frame.disjoint_from] in VDJ.
  assert (IL : img_low B).
  { apply (img_low_of_check B (2 ^ 20)); [unfold img_check; rewrite HSEG; vm_compute; reflexivity | lia]. }
  pose proof IL as (ILa & ILb).
  assert (NOSEG : forall x, YM05.alloc_ceiling <= x -> find_segment rsegs x 1 = None).
  { intros x Hx. destruct (find_segment rsegs x 1) as [g|] eqn:F; [|reflexivity].
    rewrite <- HSEG in F. apply ILb in F. lia. }
  assert (NOSEGV : forall i, 0 <= i < 56 -> find_segment rsegs (v + i) 1 = None).
  { intros i Hi. destruct (find_segment rsegs (v + i) 1) as [g|] eqn:F; [|reflexivity]. exfalso.
    destruct (RPN i Hi) as (_ & _ & _ & NI). apply NI.
    destruct (seg_reserved (v + i) ltac:(rewrite F; discriminate)) as [NE (r & Hr & Hb)].
    unfold in_img. rewrite HSEG. split; [exact NE | exists r; split; [exact Hr | exact Hb]]. }
  pose proof (kb_stk B API IL _ L A regs mem md PRE ltac:(lia)) as SSTK.
  rewrite HSEG in SSTK, VSTK, ROA.
  pose proof VSTK as (VS0 & VS56 & _).
  assert (NST : stk rsegs (normalize rsegs mem) (spZ regs - (32 + (8192 + 64))) (spZ regs)).
  { apply stk_norm; [exact ROA | | exact SSTK]. intros a Ha.
    apply ro_false_of_noseg; [unfold spZ in *; lia | apply NOSEG; unfold spZ in *; lia]. }
  assert (NVS : stk rsegs (normalize rsegs mem) v (v + 56)).
  { apply stk_norm; [exact ROA | | exact VSTK]. intros a Ha.
    apply ro_false_of_noseg; [lia|]. replace a with (v + (a - v)) by lia. apply NOSEGV. lia. }
  assert (VB : spZ regs <= v \/ exists a0 k0, In (a0, k0) (blocks L A) /\ a0 <= v /\ v + 56 <= a0 + k0).
  { destruct RPP as [(H1 & H2) | [(a0 & k0 & H1 & _ & H2 & H3) | (a1 & k1 & H1 & H2 & H3)]].
    - left. exact H1.
    - right. exists a0, k0. auto.
    - right. pose proof LED as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ H1) as (LK & LIn & _). cbn [fst snd] in LK, LIn.
      exists (a1 - 16), (k1 + 16). split; [exact LIn | lia]. }
  assert (HEADS : forall a k, In (a, k) Lam -> forall j, 0 <= j < 16 -> ~ (v <= a - 16 + j < v + 56)).
  { intros a k Hin j Hj.
    pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM LED Hin) as LR.
    pose proof LED as (_ & _ & _ & _ & LND & LF). rewrite Forall_forall in LF.
    destruct (LF _ Hin) as (LK & LIn & _). cbn [fst snd] in LK, LIn.
    pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A mem md HM) as PW.
    destruct RPP as [(H1 & H2) | [(a0 & k0 & H1 & H0 & H2 & H3) | (a1 & k1 & H1 & H2 & H3)]].
    - unfold spZ in *. lia.
    - destruct (Z.eq_dec a0 (a - 16)) as [Ea|Ea]; [destruct (Z.eq_dec k0 (k + 16)) as [Ek|Ek]|].
      + subst a0 k0. exfalso. apply H0. unfold lin.
        replace (a - 16 + 16) with a by lia. replace (k + 16 - 16) with k by lia. exact Hin.
      + destruct (pw_in2 _ _ _ _ PW H1 LIn ltac:(intros E; injection E; lia)) as [D|D];
          unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
      + destruct (pw_in2 _ _ _ _ PW H1 LIn ltac:(intros E; injection E; lia)) as [D|D];
          unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
    - destruct (Z.eq_dec a1 a) as [E1|E1]; [subst a1; lia|].
      destruct (LF _ H1) as (LK1 & LIn1 & _). cbn [fst snd] in LK1, LIn1.
      destruct (pw_in2 _ _ _ _ PW LIn1 LIn ltac:(intros E; injection E; lia)) as [D|D];
        unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (SRANGE : 0 <= s < 2 ^ 64).
  { destruct STXT as [(-> & _) | (_ & (SB0 & SB1 & _) & _)]; [lia|].
    rewrite length_app in SB1. cbn [length] in SB1. lia. }
  eapply (kb_run B regs (Z_to_bv 64 PJ_STRING) mem md (K1 regs mem v s)).
  { exact (proj1 (kb_md B API _ _ _ _ HM)). }
  { exact (proj2 (kb_md B API _ _ _ _ HM)). }
  { apply run1; [exact HSEG | exact ROA | exact R10 | exact R11 | exact VNZ | exact VAL | exact NST | exact NVS |
           unfold PJ_STRING_K, PJ_STRING_F, STRDUP_K, ALLOC_STACK; unfold spZ in *; lia | exact SRANGE]. }
  intros R pc' m1 regs1 HK Hg1.
  destruct HK as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & junk & -> & -> &
                  MU1 & WM1 & RS1 & ST1 & FR1 & VS1 & VB1).
  assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 SD_RET) by (rewrite Hg1; reflexivity).
  assert (G2 : YK11.getr regs1 2 = Z_to_bv 64 (spZ regs + -32)) by (rewrite Hg1; reflexivity).
  assert (G4 : YK11.getr regs1 4 = YK11.getr regs 4) by (rewrite Hg1; reflexivity).
  assert (G10 : YK11.getr regs1 10 = Z_to_bv 64 (sarg s)) by (rewrite Hg1; reflexivity).
  assert (SP1 : spZ regs1 = spZ regs - 32).
  { unfold spZ at 1. rewrite G2. rewrite unsigned_lit by (unfold spZ in *; lia). lia. }
  assert (OUTV : forall x, owned B L A x -> ~ (v <= x < v + 56)).
  { intros x Ho Hv. destruct (RPN (x - v) ltac:(lia)) as (NO & _). apply NO. replace (v + (x - v)) with x by lia. exact Ho. }
  assert (STAT : forall x, alloc_statics x -> ~ (v <= x < v + 56) /\ 0 <= x < 2 ^ 20).
  { intros x Hx. split.
    - intros Hv. destruct (RPN (x - v) ltac:(lia)) as (_ & NS & _). apply NS. replace (v + (x - v)) with x by lia. exact Hx.
    - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. lia. }
  assert (MR1 : aa_MR API L A m1 md).
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (MH & ML & MT).
    apply (mr_frame _ _ (aa_laws API) L A mem m1 md md HM).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) as Hlo. pose proof (OUTV a Ho).
      rewrite HSEG. apply (KindBGlue.mbyte_munch rsegs _ mem m1 a MU1); [lia|].
      cbn [outside]. unfold spZ in *. lia.
    - intros a Ho Hp. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) as Hlo. pose proof (OUTV a Ho).
      apply (present_munch _ mem m1 a MU1); [lia | cbn [outside]; unfold spZ in *; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as (Pr & Lo & Hi2 & _).
      destruct (kb_outside_dec [(spZ regs + -32, spZ regs); (v, v + 56)] (ptr_addr L p + i)) as [O|O].
      + exact (present_munch _ mem m1 (ptr_addr L p + i) MU1 ltac:(lia) O Pr).
      + assert (Hv : v <= ptr_addr L p + i < v + 56) by (cbn [outside] in O; unfold spZ in *; lia).
        pose proof VS1 as (_ & _ & VS1'). destruct (VS1' _ Hv) as (W & _).
        apply (present_of_wview rsegs); [lia | | exact W].
        replace (ptr_addr L p + i) with (v + (ptr_addr L p + i - v)) by lia. apply NOSEGV. lia.
    - reflexivity.
    - exact MH.
    - exact ML.
    - exact MT. }
  assert (P1 : call_pre_k B (aa_MR API) (ALLOC_STACK + 64) L A regs1 m1 md).
  { unfold call_pre_k.
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite G1; vm_compute; reflexivity|].
    split; [rewrite SP1; replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact HAL|].
    split; [rewrite SP1; unfold ALLOC_STACK; lia|].
    split; [rewrite SP1; lia|].
    split.
    { intros a Ha. rewrite SP1 in Ha. unfold ALLOC_STACK in Ha. rewrite HSEG.
      apply (proj1 (writable_munch rsegs _ mem m1 a MU1 ltac:(unfold spZ in *; lia) ltac:(cbn [outside]; unfold spZ in *; lia))).
      rewrite <- HSEG. apply HSTK. lia. }
    split; [rewrite G4; exact HTPR|].
    split.
    { intros a Ha. pose proof Ha as Ha'. rewrite HERR in Ha'. unfold strtod_c.STRTOD_ERRNO in Ha'. rewrite HSEG.
      assert (NV : ~ (v <= a < v + 56)).
      { intros Hv. destruct (RPN (a - v) ltac:(lia)) as (_ & _ & NE & _). apply NE. replace (v + (a - v)) with a by lia. exact Ha. }
      apply (proj1 (writable_munch rsegs _ mem m1 a MU1 ltac:(lia) ltac:(cbn [outside]; unfold spZ in *; lia))).
      rewrite <- HSEG. apply HERRW. exact Ha. }
    intros HI. rewrite SP1. destruct (Z_le_gt_dec (spZ regs) v) as [Hv|Hv].
    - apply (auxv_pre_mono B _ (v + 56)); [lia|].
      apply (kb_auxv B API _ (v + 56) mem m1 _ L A md HM (RPA Hv HI) MU1).
      + intros x Hx Hl. cbn [outside]. unfold spZ in *. lia.
      + intros x Hx Ho. cbn [outside]. unfold spZ in *. lia.
    - apply (auxv_pre_mono B _ (spZ regs)); [lia|].
      apply (kb_auxv B API _ (spZ regs) mem m1 _ L A md HM (HAUX HI) MU1).
      + intros x Hx Hl. cbn [outside]. unfold spZ in *. lia.
      + intros x Hx Ho. pose proof (OUTV x Ho). cbn [outside]. unfold spZ in *. lia. }
  assert (STR : exists slack', Mem.bytes_at (ms_segs B) m1 (sarg s) (cs ++ Z_to_bv 8 0 :: slack') /\
      ~ In (Z_to_bv 8 0) cs /\ (- (sarg s + Z.of_nat (length cs) + 1)) mod 8 <= Z.of_nat (length slack') /\
      (forall a, sarg s <= a < sarg s + Z.of_nat (length cs) + 1 -> ~ (spZ regs - 32 - (ALLOC_STACK + 64) <= a < spZ regs - 32)) /\
      (forall a, sarg s <= a < sarg s + Z.of_nat (length cs) + 1 ->
         spZ regs - 32 <= a \/ Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true \/
         exists p k, In (p, k) (blocks L A) /\ p <= a < p + k)).
  { destruct STXT as [(S0 & CS0) | (SNZ & SB & SNI & SSL & SOK & SVD & SSD)].
    - subst s cs. exists EMPTY_SLACK. change (sarg 0) with EMPTY_STR. cbn [length app Z.of_nat].
      split; [rewrite HSEG; apply empty_str_bytes; exact (ro_agree_same rsegs mem m1 ROA RS1)|].
      split; [intros []|].
      split; [unfold EMPTY_STR, EMPTY_SLACK; cbn [length Z.of_nat]; lia|].
      split; [intros a Ha; unfold EMPTY_STR, ALLOC_STACK, spZ in *; lia|].
      intros a Ha. right. left. assert (a = EMPTY_STR + Z.of_nat 0) by (unfold EMPTY_STR in *; lia). subst a.
      rewrite HSEG. exact (empty_str_ro 0 ltac:(lia)).
    - assert (SA : sarg s = s) by (unfold sarg; destruct (Z.eqb_spec s 0); [contradiction | reflexivity]).
      rewrite SA.
      cbn [Frame.disjoint_from] in SVD, SSD.
      remember ((- (s + Z.of_nat (length cs) + 1)) mod 8) as n0 eqn:EN0.
      assert (N0 : 0 <= n0 < 8) by (subst n0; apply Z.mod_pos_bound; lia).
      exists (firstn (Z.to_nat n0) slack).
      assert (LF0 : length (firstn (Z.to_nat n0) slack) = Z.to_nat n0) by (rewrite length_firstn; lia).
      split.
      { rewrite HSEG in SB |- *. rewrite <- (firstn_skipn (Z.to_nat n0) slack) in SB.
        replace (cs ++ Z_to_bv 8 0 :: firstn (Z.to_nat n0) slack ++ skipn (Z.to_nat n0) slack)
          with ((cs ++ Z_to_bv 8 0 :: firstn (Z.to_nat n0) slack) ++ skipn (Z.to_nat n0) slack) in SB
          by (rewrite <- app_assoc; reflexivity).
        apply bytes_at_app in SB. destruct SB as [SB _].
        apply (bytes_at_transport rsegs _ mem m1 _ _ SB MU1).
        cbn [Frame.disjoint_from]. rewrite length_app. cbn [length]. rewrite LF0.
        unfold spZ in *. Z.div_mod_to_equations. lia. }
      split; [exact SNI|].
      split; [rewrite LF0; lia|].
      split; [intros a Ha; unfold ALLOC_STACK, spZ in *; lia|].
      intros a Ha. destruct SOK as [RO | (c1 & d1 & L1 & B1 & B2)].
      + right. left. replace a with (s + (a - s)) by lia. apply RO. lia.
      + right. right. pose proof LED as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
        destruct (LF _ L1) as (LK & LIn & _). cbn [fst snd] in LK, LIn.
        exists (c1 - 16), (d1 + 16). split; [exact LIn | lia]. }
  destruct STR as (slack' & SB1 & SNI1 & SSL1 & SWIN1 & SLOC1).
  assert (LED1 : ledger B L A m1 Lam peak cnt fail).
  { pose proof LED as (AW & LB & CB0 & FB & ND & LF).
    unfold ledger. split; [|split; [exact LB | split; [exact CB0 | split; [exact FB | split; [exact ND |]]]]].
    - destruct AW as (W1 & W2 & W3 & W4). unfold alloc_words.
      rewrite HSEG in W1, W2, W3, W4 |- *.
      split; [|split; [|split]]; (eapply (kb_word_munch rsegs mem m1); [eassumption | exact MU1 |]); intros k Hk.
      + destruct (STAT (G_LIVE + k) ltac:(unfold alloc_statics; lia)) as (NV & LT).
        split; [lia|]. cbn [outside]. unfold spZ in *. lia.
      + destruct (STAT (G_PEAK + k) ltac:(unfold alloc_statics; lia)) as (NV & LT).
        split; [lia|]. cbn [outside]. unfold spZ in *. lia.
      + destruct (STAT (G_COUNT + k) ltac:(unfold alloc_statics; lia)) as (NV & LT).
        split; [lia|]. cbn [outside]. unfold spZ in *. lia.
      + destruct (STAT (G_FAIL + k) ltac:(unfold alloc_statics; lia)) as (NV & LT).
        split; [lia|]. cbn [outside]. unfold spZ in *. lia.
    - rewrite Forall_forall in LF |- *. intros [a k] Hin. destruct (LF _ Hin) as (H0 & H1 & H2 & H3). cbn [fst snd] in *.
      split; [exact H0|]. split; [exact H1|]. split; [|exact H3].
      pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM LED Hin) as LR.
      rewrite HSEG in H2 |- *. eapply (kb_word_munch rsegs mem m1); [exact H2 | exact MU1 |].
      intros j Hj. pose proof (HEADS a k Hin j ltac:(lia)). split; [lia|]. cbn [outside]. unfold spZ in *. lia. }
  eapply SR_bind.
  { apply (HSD L A regs1 m1 md (sarg s) cs slack' b Lam peak cnt fail).
    - exact P1.
    - exact G10.
    - exact SB1.
    - exact SNI1.
    - exact SSL1.
    - intros a Ha. change (bv_unsigned (YK11.getr regs1 2)) with (spZ regs1). rewrite SP1. exact (SWIN1 a Ha).
    - intros a Ha. change (bv_unsigned (YK11.getr regs1 2)) with (spZ regs1). rewrite SP1. exact (SLOC1 a Ha).
    - exact LED1.
    - rewrite HSEG. exact (ro_agree_same rsegs mem m1 ROA RS1).
    - exact RES.
    - exact ROOM.
    - lia. }
  intros c' (L' & A' & regs' & mem' & md' & res & -> & ROA' & GK & INIT & AUXK & CPOST & NREG & GA0 & KEEPS &
             UKEPT & ARMS).
  destruct CPOST as (HM' & HWF' & HBD' & HLY & HPA & HRP & HMD & HFR & HUB & HSCR).
  assert (RESB : res = 0 \/ (4096 <= res - 16 /\ res - 16 + (Z.of_nat (length cs) + 17) <= YM05.alloc_ceiling /\
                 (forall i, 0 <= i < Z.of_nat (length cs) + 17 -> ~ in_img B (res - 16 + i)))).
  { destruct ARMS as [(_ & R0 & _) | (_ & _ & _ & _ & _ & RNI & _ & _ & (bb1 & bb2 & EB' & _) & _)]; [left; exact R0|].
    right. assert (Hin : In (res - 16, Z.of_nat (length cs) + 17) (blocks L' A'))
      by (rewrite EB'; apply in_or_app; right; left; reflexivity).
    destruct (blk_range _ _ _ _ _ _ HM' Hin) as (Lo & Hi). split; [lia|]. split; [lia|]. intros i Hi'. apply RNI. lia. }
  assert (RR : 0 <= res < 2 ^ 64) by (destruct RESB as [->|(Lo & Hi & _)]; lia).
  assert (BLK' : forall a0 k0, In (a0, k0) (blocks L A) -> exists q, In (q, k0) (user_blocks A) /\
            In (q, k0) (user_blocks A') /\ ptr_addr L q = a0 /\ ptr_addr L' q = a0 /\ 4096 <= a0 /\
            a0 + k0 <= YM05.alloc_ceiling).
  { intros a0 k0 Hin. destruct (blk_user L A a0 k0 Hin) as (q & Hq & Eq).
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k0 HM Hq) as BR. rewrite Eq in BR.
    assert (Hq' : In (q, k0) (user_blocks A')) by (apply UKEPT; [exact Hq | intros E; injection E; lia]).
    exists q. split; [exact Hq|]. split; [exact Hq'|]. split; [exact Eq|].
    split; [rewrite (HPA q k0 Hq Hq'); exact Eq | lia]. }
  assert (OWN3 : forall x, owned B L' A' x -> ~ (v <= x < v + 56)).
  { intros x Ho Hv. destruct VB as [Hs | (a0 & k0 & Hin & Ha0 & Hk0)].
    - pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho). unfold spZ in *. lia.
    - destruct (BLK' a0 k0 Hin) as (q & Hq & Hq' & Eq & Eq' & BR1 & BR2).
      destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k0 (x - a0) HM' Hq' ltac:(lia)) as (_ & _ & _ & NO).
      apply NO. rewrite Eq'. replace (a0 + (x - a0)) with x by lia. exact Ho. }
  assert (VADDR : forall x, v <= x < v + 56 ->
            mbyte rsegs mem' x = mbyte rsegs m1 x /\ (writable_at rsegs m1 x -> writable_at rsegs mem' x)).
  { intros x Hx. rewrite <- HSEG. destruct VB as [Hs | (a0 & k0 & Hin & Ha0 & Hk0)].
    - pose proof (HFR x ltac:(left; unfold spZ in *; lia)
        ltac:(intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); unfold spZ in *; lia)
        ltac:(intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho); unfold spZ in *; lia)
        ltac:(unfold scratch_k; rewrite SP1, HERR; unfold strtod_c.STRTOD_ERRNO, ALLOC_STACK, spZ in *; lia)
        ltac:(unfold strdup_writes; intros [Hs'|(Hr & Hr')]; [destruct (STAT x Hs'); unfold spZ in *; lia|
               destruct RESB as [R0|(Lo & Hi & _)]; [contradiction|unfold spZ in *; lia]])) as [E1 E2].
      split; [exact E1 | apply E2].
    - destruct (BLK' a0 k0 Hin) as (q & Hq & Hq' & Eq & Eq' & BR1 & BR2).
      split.
      + replace x with (a0 + (x - a0)) by lia. apply (KEEPS a0 k0 (x - a0) Hin); lia.
      + intros _. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k0 (x - a0) HM' Hq' ltac:(lia)) as (Pr & _).
        rewrite Eq' in Pr. replace (a0 + (x - a0)) with x in Pr by lia. exact (present_writable B mem' x Pr). }
  assert (VS2 : stk rsegs mem' v (v + 56)).
  { apply (stk_frame rsegs m1 mem' v (v + 56) VS1). intros a Ha. exact (VADDR a Ha). }
  assert (VB2 : bytes_at rsegs mem' v (le4 (Z_to_bv 64 4) ++ repeat (Z_to_bv 8 0) 52)).
  { apply (bytes_frame rsegs m1 mem' v _ VB1). intros i Hi. rewrite length_app, length_le4, repeat_length in Hi.
    exact (proj1 (VADDR (v + i) ltac:(lia))). }
  assert (FRADDR : forall x, spZ regs + -32 <= x < spZ regs ->
            mbyte rsegs mem' x = mbyte rsegs m1 x /\ (writable_at rsegs m1 x -> writable_at rsegs mem' x)).
  { intros x Hx. rewrite <- HSEG.
    pose proof (HFR x ltac:(left; unfold spZ in *; lia)
      ltac:(intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); unfold spZ in *; lia)
      ltac:(intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho); unfold spZ in *; lia)
      ltac:(unfold scratch_k; rewrite SP1, HERR; unfold strtod_c.STRTOD_ERRNO, ALLOC_STACK, spZ in *; lia)
      ltac:(unfold strdup_writes; intros [Hs'|(Hr & Hr')]; [destruct (STAT x Hs'); unfold spZ in *; lia|
             destruct RESB as [R0|(Lo & Hi & _)]; [contradiction|unfold spZ in *; lia]])) as [E1 E2].
    split; [exact E1 | apply E2]. }
  assert (FRR : rw_cells rsegs mem' (spZ regs + -32)
                  [CB 8 junk; C8 (YK11.getr regs 9); C8 (YK11.getr regs 8); C8 (YK11.getr regs 1)]).
  { apply (rw_frame rsegs m1 mem' _ _ FR1). intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply FRADDR. lia. }
  rewrite HSEG in ROA'.
  rewrite G1.
  eapply (kb_run B regs' (Z_to_bv 64 SD_RET) mem' md'
            (K2 regs' mem' v res (YK11.getr regs 2) (YK11.getr regs 1) (YK11.getr regs 8) (YK11.getr regs 9))).
  { exact (proj1 (kb_md B API _ _ _ _ HM')). }
  { exact (proj2 (kb_md B API _ _ _ _ HM')). }
  { apply (run2 regs' mem' v res (YK11.getr regs 2) (YK11.getr regs 1) (YK11.getr regs 8) (YK11.getr regs 9) junk HSEG ROA').
    - etransitivity; [exact (HRP 2 ltac:(unfold callee_saved; lia))|]. rewrite Hg1. reflexivity.
    - etransitivity; [exact (HRP 8 ltac:(unfold callee_saved; lia))|]. rewrite Hg1. reflexivity.
    - exact GA0.
    - apply rw_norm; [exact ROA' | | exact FRR]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      apply ro_false_of_noseg; [unfold spZ in *; lia | apply NOSEG; unfold spZ in *; lia].
    - apply stk_norm; [exact ROA' | | exact (stk_sub rsegs mem' v (v + 56) (v + 16) (v + 24) VS2 ltac:(lia) ltac:(lia) ltac:(lia))].
      intros a Ha. apply ro_false_of_noseg; [lia|]. replace a with (v + (a - v)) by lia. apply NOSEGV. lia.
    - unfold spZ in *. lia.
    - unfold spZ in *. lia.
    - exact RR. }
  intros R3 pc3 m3 regs3 HK2 Hg3.
  destruct HK2 as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & -> & -> & MU3 & WM3 & RS3 & BV3).
  rewrite (kb_ret_pc _ HRA).
  apply SR_ret.
  cbv beta.
  assert (VS3 : stk rsegs m3 v (v + 56)).
  { apply (stk_patch rsegs mem' m3 v (v + 56) [(v + 16, v + 24)] VS2 MU3 WM3). intros a Ha O.
    assert (Hin : v + 16 <= a < v + 24) by (cbn [outside] in O; lia).
    destruct BV3 as (_ & _ & BB). pose proof (BB (Z.to_nat (a - (v + 16))) ltac:(rewrite length_le8; lia)) as E.
    replace (v + 16 + Z.of_nat (Z.to_nat (a - (v + 16)))) with a in E by lia.
    destruct (nth_error (le8 (Z_to_bv 64 res)) (Z.to_nat (a - (v + 16)))) as [bt|] eqn:N; [exists bt; exact E|].
    apply nth_error_None in N. rewrite length_le8 in N. lia. }
  assert (MR3 : aa_MR API L' A' m3 md').
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM') as (MH' & ML' & MT').
    apply (mr_frame _ _ (aa_laws API) L' A' mem' m3 md' md' HM').
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho). pose proof (OWN3 a Ho).
      apply (KindBGlue.mbyte_munch _ _ mem' m3 a MU3); [lia | cbn [outside]; lia].
    - intros a Ho Hp. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho). pose proof (OWN3 a Ho).
      apply (present_munch _ mem' m3 a MU3); [lia | cbn [outside]; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM' Hin Hi) as (Pr & Lo & Hi2 & _).
      destruct (kb_outside_dec [(v + 16, v + 24)] (ptr_addr L' p + i)) as [O|O].
      + exact (present_munch _ mem' m3 (ptr_addr L' p + i) MU3 ltac:(lia) O Pr).
      + assert (Hv : v <= ptr_addr L' p + i < v + 56) by (cbn [outside] in O; lia).
        pose proof VS3 as (_ & _ & VS3'). destruct (VS3' _ Hv) as (W & _).
        apply (present_of_wview rsegs); [lia | | exact W].
        replace (ptr_addr L' p + i) with (v + (ptr_addr L' p + i - v)) by lia. apply NOSEGV. lia.
    - reflexivity.
    - exact MH'.
    - exact ML'.
    - exact MT'. }
  assert (RPOST : rpost B API PJ_STRING_K L A regs mem md (pj_string_writes v) (fun _ _ => False)
                    L' A' regs3 m3 md').
  { unfold rpost, PJ_STRING_K, PJ_STRING_F, STRDUP_K, ALLOC_STACK.
    split; [exact MR3|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact HLY|]. split; [exact INIT|].
    split.
    { intros NI i Hi.
      assert (SO : forall L0 A0, owned B L0 A0 (ms_libc B + 8 + i)) by (intros; right; unfold static_owned; right; right; left; lia).
      pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM (SO L A)) as LO1.
      pose proof (OUTV _ (SO L A)) as NV1. pose proof (OWN3 _ (SO L' A')) as NV3.
      rewrite (KindBGlue.mbyte_munch _ _ mem' m3 (ms_libc B + 8 + i) MU3 ltac:(lia) ltac:(cbn [outside]; lia)).
      rewrite (AUXK NI i Hi).
      apply (KindBGlue.mbyte_munch _ _ mem m1 (ms_libc B + 8 + i) MU1 ltac:(lia) ltac:(cbn [outside]; unfold spZ in *; lia)). }
    split; [exact NREG|].
    split.
    { intros p n Hin _. apply UKEPT; [exact Hin|]. intros E. injection E as E1 _.
      pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hin). lia. }
    split; [exact HPA|].
    split.
    { intros r Hr. rewrite Hg3. unfold callee_saved in Hr.
      destruct Hr as [->|[->|[->|[->|[->|Hr]]]]];
        [reflexivity | psv HRP Hg1 regs' 3 | psv HRP Hg1 regs' 4 | reflexivity | reflexivity |].
      assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
      - psv HRP Hg1 regs' 18. - psv HRP Hg1 regs' 19. - psv HRP Hg1 regs' 20. - psv HRP Hg1 regs' 21.
      - psv HRP Hg1 regs' 22. - psv HRP Hg1 regs' 23. - psv HRP Hg1 regs' 24. - psv HRP Hg1 regs' 25.
      - psv HRP Hg1 regs' 26. - psv HRP Hg1 regs' 27. }
    split; [exact HMD|].
    split.
    { intros a Ha NS NE. unfold scratch_k in NS. unfold pj_string_writes in NE.
      assert (O1 : outside [(spZ regs + -32, spZ regs); (v, v + 56)] a) by (cbn [outside]; unfold spZ in *; lia).
      pose proof (KindBGlue.mbyte_munch (ms_segs B) _ mem m1 a MU1 ltac:(lia) O1) as E1.
      pose proof (writable_munch (ms_segs B) _ mem m1 a MU1 ltac:(lia) O1) as W1.
      pose proof (HFR a ltac:(left; lia)
        ltac:(intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); lia)
        ltac:(intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho); lia)
        ltac:(unfold scratch_k; rewrite SP1; unfold ALLOC_STACK, spZ in *; lia)
        ltac:(unfold strdup_writes; intros [Hs'|(Hr & Hr')]; [destruct (STAT a Hs'); lia|
               destruct RESB as [R0|(Lo & Hi & _)]; [contradiction|lia]])) as [E2 W2].
      assert (O3 : outside [(v + 16, v + 24)] a) by (cbn [outside]; lia).
      pose proof (KindBGlue.mbyte_munch (ms_segs B) _ mem' m3 a MU3 ltac:(lia) O3) as E3.
      pose proof (writable_munch (ms_segs B) _ mem' m3 a MU3 ltac:(lia) O3) as W3.
      split; [rewrite E3, E2, E1; reflexivity | tauto]. }
    split.
    { intros a Ha NOWN NS NE. unfold scratch_k in NS. unfold pj_string_writes in NE. pose proof (ILa a Ha) as Hlo.
      assert (O1 : outside [(spZ regs + -32, spZ regs); (v, v + 56)] a) by (cbn [outside]; unfold spZ in *; lia).
      pose proof (KindBGlue.mbyte_munch (ms_segs B) _ mem m1 a MU1 ltac:(lia) O1) as E1.
      pose proof (writable_munch (ms_segs B) _ mem m1 a MU1 ltac:(lia) O1) as W1.
      pose proof (HFR a ltac:(right; exact Ha) (NOWN _ _ _ _ MR1) (NOWN _ _ _ _ HM')
        ltac:(unfold scratch_k; rewrite SP1; unfold ALLOC_STACK, spZ in *; lia)
        ltac:(unfold strdup_writes; intros [Hs'|(Hr & Hr')]; [tauto|
               destruct RESB as [R0|(Lo & Hi & NI)]; [contradiction|]];
              apply (NI (a - (res - 16))); [lia|]; replace (res - 16 + (a - (res - 16))) with a by lia; exact Ha))
        as [E2 W2].
      assert (O3 : outside [(v + 16, v + 24)] a) by (cbn [outside]; lia).
      pose proof (KindBGlue.mbyte_munch (ms_segs B) _ mem' m3 a MU3 ltac:(lia) O3) as E3.
      pose proof (writable_munch (ms_segs B) _ mem' m3 a MU3 ltac:(lia) O3) as W3.
      split; [rewrite E3, E2, E1; reflexivity | tauto]. }
    split.
    { intros p n i Hin Hin' Hi NE. unfold pj_string_writes in NE.
      destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as (_ & Lo & Hi2 & _).
      assert (O1 : outside [(spZ regs + -32, spZ regs); (v, v + 56)] (ptr_addr L p + i))
        by (cbn [outside]; unfold spZ in *; lia).
      assert (O3 : outside [(v + 16, v + 24)] (ptr_addr L p + i)) by (cbn [outside]; lia).
      rewrite (KindBGlue.mbyte_munch _ _ mem' m3 (ptr_addr L p + i) MU3 ltac:(lia) O3).
      rewrite (KEEPS (ptr_addr L p) n i ltac:(unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hin])
                 ltac:(lia) Hi).
      exact (KindBGlue.mbyte_munch _ _ mem m1 (ptr_addr L p + i) MU1 ltac:(lia) O1). }
    intros a Ha. unfold scratch_k in Ha. rewrite HSEG. unfold writable_at. apply WM3. fold (writable_at rsegs mem' a). rewrite <- HSEG.
    destruct Ha as [Ha|Ha]; [destruct (Z_lt_ge_dec a (spZ regs - 32)) as [Hl|Hl]|].
    - apply HSCR. unfold scratch_k. rewrite SP1. unfold ALLOC_STACK. lia.
    - destruct (proj2 FRR) as (_ & _ & WW). cbn [cells_size csize Nat.add] in WW.
      pose proof (WW (a - (spZ regs + -32)) ltac:(lia)) as WA.
      replace (spZ regs + -32 + (a - (spZ regs + -32))) with a in WA by lia. rewrite <- HSEG in WA. exact WA.
    - apply HSCR. unfold scratch_k. right. exact Ha. }
  assert (RDC : rd_cells B m3).
  { unfold rd_cells. split; [rewrite HSEG; exact (ro_agree_same rsegs mem' m3 ROA' RS3)|].
    destruct (ax_statics AX L' A' m3 md' MR3) as (GOT & (g & _ & GG) & _). split; [exact GOT | exists g; exact GG]. }
  assert (LEDT : forall Lam0 pk c f, ledger B L' A' mem' Lam0 pk c f ->
            (forall a k, In (a, k) Lam0 -> forall j, 0 <= j < 8 -> ~ (v + 16 <= a - 16 + j < v + 24)) ->
            ledger B L' A' m3 Lam0 pk c f).
  { intros Lam0 pk c f (AW & LB & CB0 & FB & ND & LF) HH. unfold ledger.
    split; [|split; [exact LB | split; [exact CB0 | split; [exact FB | split; [exact ND |]]]]].
    - destruct AW as (W1 & W2 & W3 & W4). unfold alloc_words.
      split; [|split; [|split]]; (eapply (kb_word_munch (ms_segs B) mem' m3); [eassumption | exact MU3 |]); intros k Hk.
      + destruct (STAT (G_LIVE + k) ltac:(unfold alloc_statics; lia)) as (NV & LT). split; [lia|]. cbn [outside]. lia.
      + destruct (STAT (G_PEAK + k) ltac:(unfold alloc_statics; lia)) as (NV & LT). split; [lia|]. cbn [outside]. lia.
      + destruct (STAT (G_COUNT + k) ltac:(unfold alloc_statics; lia)) as (NV & LT). split; [lia|]. cbn [outside]. lia.
      + destruct (STAT (G_FAIL + k) ltac:(unfold alloc_statics; lia)) as (NV & LT). split; [lia|]. cbn [outside]. lia.
    - rewrite Forall_forall in LF |- *. intros [a k] Hin. destruct (LF _ Hin) as (H0 & H1 & H2 & H3). cbn [fst snd] in *.
      split; [exact H0|]. split; [exact H1|]. split; [|exact H3].
      eapply (kb_word_munch (ms_segs B) mem' m3); [exact H2 | exact MU3 |].
      intros j Hj. pose proof (HH a k Hin j ltac:(lia)). pose proof (blk_range _ _ _ _ _ _ HM' H1).
      split; [lia|]. cbn [outside]. lia. }
  destruct (hdr_split rsegs mem' v 0 VB2) as (Q0 & Q4 & Q8 & _ & Q24 & Q32 & Q40 & Q48).
  assert (P0 : bytes_at rsegs m3 v (le4 (Z_to_bv 64 4))) by trb Q0 MU3.
  assert (P4 : bytes_at rsegs m3 (v + 4) (repeat (Z_to_bv 8 0) 4)) by trb Q4 MU3.
  assert (P8 : bytes_at rsegs m3 (v + 8) (le8 (Z_to_bv 64 0))) by trb Q8 MU3.
  assert (P24 : bytes_at rsegs m3 (v + 24) (le8 (Z_to_bv 64 0))) by trb Q24 MU3.
  assert (P32 : bytes_at rsegs m3 (v + 32) (le8 (Z_to_bv 64 0))) by trb Q32 MU3.
  assert (P40 : bytes_at rsegs m3 (v + 40) (le8 (Z_to_bv 64 0))) by trb Q40 MU3.
  assert (P48 : bytes_at rsegs m3 (v + 48) (le8 (Z_to_bv 64 0))) by trb Q48 MU3.
  destruct ARMS as [(CF & R0 & _ & _ & _ & RESF & LEDF) | (CNF & RNZ & RM16 & RES' & RNS & RNI & RNL & RBY & (bb1 & bb2 & EB' & EB) & LEDS)].
  - subst res.
    repeat match type of LEDF with _ /\ _ => destruct LEDF as [_ LEDF] end.
    exists L', A', regs3, m3, md', Lam, peak, (2 ^ 64 - 1), (-1).
    split; [reflexivity|]. split; [exact RPOST|]. split; [exact RDC|].
    split; [rewrite Hg3; reflexivity|].
    split.
    { apply LEDT; [exact LEDF|]. intros a k Hin j Hj Hv. apply (HEADS a k Hin j); lia. }
    right. split; [exact CF|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact RESF|].
    rewrite HSEG.
    split; [split; [exact VAL | exact VS3]|].
    split; [exact (hdr_join rsegs m3 v P0 P4 P8 BV3 P24 P32 P40 P48)|].
    cbn [pj_fd]. unfold pj_fshape. split; [constructor|]. split; [intros b0 x Hb; destruct Hb|].
    exists 4, 0, 0, 0, 0, 0, 0, false, [], [], [], [].
    split.
    { unfold pj_hdr. split; [split; [exact VAL | exact VS3]|].
      split; [split; [lia | exact P0]|]. split; [split; [lia | exact P8]|]. split; [split; [lia | exact BV3]|].
      split; [split; [lia | exact P24]|]. split; [split; [lia | exact P32]|]. split; [split; [lia | exact P40]|].
      split; [lia | exact P48]. }
    split; [left; auto|]. split; [left; auto|]. split; [left; auto|]. split; [apply Permutation.Permutation_refl|].
    split; reflexivity.
  - assert (NEWD : res - 16 + (Z.of_nat (length cs) + 17) <= v \/ v + 56 <= res - 16).
    { destruct VB as [Hs | (a0 & k0 & Hin & Ha0 & Hk0)].
      - destruct RESB as [R0|(Lo & Hi & _)]; [contradiction|]. unfold spZ in *. lia.
      - pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') as PW. rewrite EB' in PW. rewrite EB in Hin.
        destruct (pw_app _ bb1 _ bb2 _ PW Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    exists L', A', regs3, m3, md', ((res, Z.of_nat (length cs) + 1) :: Lam),
      (Z.max peak (lsum Lam + Z.of_nat (length cs) + 1)), fail, 0.
    split; [reflexivity|]. split; [exact RPOST|]. split; [exact RDC|].
    split.
    { rewrite Hg3. transitivity (Z_to_bv 64 (sres res)); [reflexivity|].
      unfold sres. destruct (Z.eqb_spec res 0); [contradiction | reflexivity]. }
    split.
    { apply LEDT; [exact LEDS|]. intros a k [E|Hin] j Hj Hv.
      - injection E as <- <-. lia.
      - apply (HEADS a k Hin j); lia. }
    left. split; [exact CNF|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RES'|].
    exists res. split; [reflexivity|].
    split.
    { intros a k [E|[]]. injection E as <- <-. intros Hin. rewrite EB in Hin.
      pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') as PW. rewrite EB' in PW.
      destruct (pw_app _ bb1 _ bb2 _ PW Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    split; [cbn [lsum]; f_equal; lia|].
    rewrite HSEG. cbn [pj_node tag].
    split; [constructor; [intros Hn; inversion Hn | constructor]|].
    split; [intros b0 x Hb Hx; destruct Hb as [<-|[]]; unfold pj_holds in Hx; cbn [fst snd] in Hx; lia|].
    exists 0, res, 0, 0, 0, 0.
    split.
    { unfold pj_hdr. split; [split; [exact VAL | exact VS3]|].
      split; [split; [lia | exact P0]|]. split; [split; [lia | exact P8]|]. split; [split; [exact RR | exact BV3]|].
      split; [split; [lia | exact P24]|]. split; [split; [lia | exact P32]|]. split; [split; [lia | exact P40]|].
      split; [lia | exact P48]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists (Z.of_nat (length cs) + 1). split; [|reflexivity].
    split; [left; reflexivity|]. split; [unfold zb; rewrite length_map; lia|].
    split; [exact (zb_pos cs SNI1)|]. rewrite map_app, zb_map. cbn [map].
    rewrite HSEG in RBY.
    apply (bytes_at_transport rsegs _ mem' m3 res _ RBY MU3).
    cbn [Frame.disjoint_from]. rewrite length_app. cbn [length]. lia.
Qed.

End Main.
