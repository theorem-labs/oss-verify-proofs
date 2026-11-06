(* The slot's mark step glue (ARM 2 op_mark, ARM 5 op_refused), plain image: the bookkeeping of the slot's
   heap blocks across a mark_quietly step, the payload as an entry block, and the uniqueness of the views
   the step's premises and its Post read (so the Post's tab / kbs / nm are the arm's own). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs LFr LFrEn LFrLo
  LFrMqDefs LGlue.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Uniqueness of the views
   ========================================================================== *)

Lemma lgmq_bytes_inj : forall m a l1 l2,
  bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) HL.
  apply lo_list_ext; [exact HL|].
  intros i Hi. rewrite <- (H1 i Hi). apply H2. rewrite <- HL. exact Hi.
Qed.

Lemma lgmq_cstr_len : forall m a s1 s2, cstr_at m a s1 -> cstr_at m a s2 -> (length s1 <= length s2)%nat.
Proof.
  intros m a s1 s2 [(_ & _ & H1) N1] [(_ & _ & H2) _].
  destruct (Nat.le_gt_cases (length s1) (length s2)) as [Hle | Hlt]; [exact Hle | exfalso].
  assert (Hi1 : (length s2 < length (s1 ++ [zb 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  assert (Hi2 : (length s2 < length (s2 ++ [zb 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (H1 _ Hi1) as R1. pose proof (H2 _ Hi2) as R2.
  rewrite nth_error_app1 in R1 by exact Hlt.
  rewrite nth_error_app2, Nat.sub_diag in R2 by lia. cbn [nth_error] in R2.
  rewrite R2 in R1.
  apply N1. apply (nth_error_In s1 (length s2)). symmetry. exact R1.
Qed.

Lemma lgmq_cstr_inj : forall m a s1 s2, cstr_at m a s1 -> cstr_at m a s2 -> s1 = s2.
Proof.
  intros m a s1 s2 H1 H2.
  pose proof (lgmq_cstr_len m a s1 s2 H1 H2) as L1. pose proof (lgmq_cstr_len m a s2 s1 H2 H1) as L2.
  destruct H1 as [B1 _]. destruct H2 as [B2 _].
  apply (app_inv_tail [zb 0]).
  apply (lgmq_bytes_inj m a); [exact B1 | exact B2 | rewrite !length_app; lia].
Qed.

Lemma lgmq_str_arg_inj : forall m a o1 o2, str_arg m a o1 -> str_arg m a o2 -> o1 = o2.
Proof.
  intros m a [s1|] [s2|] H1 H2; unfold str_arg in H1, H2.
  - destruct H1 as [_ C1]. destruct H2 as [_ C2]. rewrite (lgmq_cstr_inj m a s1 s2 C1 C2). reflexivity.
  - destruct H1 as [Ha _]. exfalso. exact (Ha H2).
  - destruct H2 as [Ha _]. exfalso. exact (Ha H1).
  - reflexivity.
Qed.

Lemma lgmq_nlk_inj : forall m k1 k2, nlk_at m k1 -> nlk_at m k2 -> k1 = k2.
Proof.
  intros m k1 k2 [[B1 _] L1] [[B2 _] L2].
  apply (lgmq_bytes_inj m A_G_NL); [exact B1 | exact B2 | lia].
Qed.

Lemma lgmq_list_ext : forall (X : Type) (l l' : list X), length l = length l' ->
  (forall i, (i < length l)%nat -> nth_error l i = nth_error l' i) -> l = l'.
Proof.
  intros X. induction l as [|b l IH]; intros [|b' l'] HL H.
  - reflexivity.
  - cbn in HL. discriminate.
  - cbn in HL. discriminate.
  - cbn in HL. f_equal.
    + specialize (H 0%nat ltac:(cbn; lia)). cbn in H. injection H as Hb. exact Hb.
    + apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

Lemma lgmq_iftab_inj : forall m kbs t1 t2, iftab_at m kbs t1 -> iftab_at m kbs t2 -> t1 = t2.
Proof.
  intros m kbs t1 t2 (N1 & _ & H1) (N2 & _ & H2).
  pose proof (Nat2Z.inj _ _ (eq_trans (eq_sym N1) N2)) as HL. clear N1 N2.
  pose proof (eq_refl : 2 ^ 64 = 18446744073709551616) as P64.
  pose proof (eq_refl : 2 ^ 32 = 4294967296) as P32.
  pose proof (eq_refl : 2 ^ 31 = 2147483648) as P31.
  apply lgmq_list_ext; [exact HL|]. intros i Hi.
  destruct (nth_error t1 i) as [[nm1 ix1]|] eqn:E1; [|exfalso; apply nth_error_None in E1; lia].
  destruct (nth_error t2 i) as [[nm2 ix2]|] eqn:E2; [|exfalso; apply nth_error_None in E2; lia].
  destruct (H1 i nm1 ix1 E1) as (R1 & p1 & U1 & _ & C1 & I1).
  destruct (H2 i nm2 ix2 E2) as (R2 & p2 & U2 & _ & C2 & I2).
  assert (Ep : p1 = p2).
  { apply (lo_u64_inj m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i)); [exact U1 | exact U2 | |].
    - destruct C1 as [(Z0 & Z1 & _) _]. rewrite length_app in Z1. cbn [length] in Z1. lia.
    - destruct C2 as [(Z0 & Z1 & _) _]. rewrite length_app in Z1. cbn [length] in Z1. lia. }
  subst p2. rewrite (lgmq_cstr_inj m p1 nm1 nm2 C1 C2).
  assert (E4 : le4 (wz ix1) = le4 (wz ix2)).
  { apply (lgmq_bytes_inj m (A_G_NL + NK_IF_INDEX + 4 * Z.of_nat i)); [exact I1 | exact I2 |].
    rewrite !length_le4. reflexivity. }
  pose proof (f_equal (fun l => bv_unsigned (le_bytes_to_word l)) E4) as E5. cbn beta in E5.
  rewrite !le_bytes_to_word_le4 in E5. unfold wz in E5.
  rewrite (MState.unsigned_lit ix1), (MState.unsigned_lit ix2) in E5 by lia.
  rewrite !Z.mod_small in E5 by lia. subst ix2. reflexivity.
Qed.

(* ==========================================================================
   2. Registers, the selector's pointer, the two ends of a last segment
   ========================================================================== *)

Section Get.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Lemma lgmq_g10 :
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 10 = a0.
Proof. reflexivity. Qed.
Lemma lgmq_g11 :
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 11 = a1.
Proof. reflexivity. Qed.
End Get.

Lemma lgmq_reg10 : forall r : bvmap 5 word, getr r 10 = reg_get r 10.
Proof. intros. reflexivity. Qed.

Lemma lgmq_sel_ptr_rng : forall s, 0 <= s <= 255 -> 0 <= sel_ptr s < 2 ^ 64.
Proof.
  intros s Hs. unfold sel_ptr.
  destruct (s =? 255); [lia|]. destruct (s <? 64); [unfold A_G_NAMES; lia|].
  assert (H : forall n, 0 <= nth n odd_ptrs 0 < 2 ^ 64)
    by (intros [|[|[|[|[|[|n]]]]]]; cbn; [lia..| destruct n; cbn; lia]).
  apply H.
Qed.

(* the two ends of segment B *)
Lemma lgmq_lh_pc : forall E i gp ms, lh_ms E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_LH) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
                    & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma lgmq_ex_pc : forall E gp ms, ex_ms E gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_EXIT) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6 & s8
                  & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & j & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma lgmq_uw : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (wz a) = a.
Proof. intros a H. unfold wz. exact (MState.unsigned_lit a H). Qed.

(* ==========================================================================
   3. The slot's heap blocks across the mark step
   ========================================================================== *)

Section LM.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

(* the kept set of a cut (LFR's lkept) *)
Lemma lgmq_kept : forall g pc hb T P c, CUT B API g pc hb T P c -> lkept g hb T.
Proof using.
  intros g pc hb T P c (fx' & L & A & regs & mem & md & _ & _ & HL & _).
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK & _).
  exact HK.
Qed.

(* md and mk are among the slot's blocks *)
Lemma lgmq_hb_in : forall g E hb T, hb_inv g E hb T -> In (e_md E, MD_SIZE) hb /\ In (e_mk E, MK_SIZE) hb.
Proof using.
  intros g E hb T HI. unfold hb_inv in HI.
  split; apply (Permutation_in _ (Permutation_sym HI)); [left; reflexivity | right; left; reflexivity].
Qed.

Lemma lgmq_hb_bytes_perm : forall h h', Permutation h h' -> hb_bytes h = hb_bytes h'.
Proof.
  intros h h' HP.
  induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; rewrite ?hb_bytes_cons.
  - reflexivity.
  - rewrite IH. reflexivity.
  - ring.
  - rewrite IH1, IH2. reflexivity.
Qed.

(* the room lfr_mark asks: at most md, mk and the FILE *)
Lemma lgmq_room : forall g E hb T, hb_inv g E hb T -> (T = [] \/ exists f, T = [(f, MF_BLOCK)]) -> lroom_hb hb.
Proof using.
  intros g E hb T HI HT. unfold hb_inv in HI. unfold lroom_hb.
  pose proof (eq_refl : 2 ^ 20 = 1048576) as P20.
  rewrite (Permutation_length HI), (lgmq_hb_bytes_perm _ _ HI), !hb_bytes_cons. cbn [length snd].
  assert (HX : hx g T = [] \/ exists f, hx g T = [(f, MF_BLOCK)]).
  { unfold hx. destruct (lg_T g); [exact HT | left; reflexivity]. }
  destruct HX as [-> | (f & ->)]; unfold hb_bytes; cbn [length map fold_right snd];
    unfold MD_SIZE, MK_SIZE, MF_BLOCK; lia.
Qed.

(* after the mark: the FILE f is the kept block; it joins hb when this driver call opened it *)
Lemma lgmq_hb_next : forall g E hb T f,
  hb_inv g E hb T -> lkept g hb T -> lkept g (lmq_hb T f hb) [(f, MF_BLOCK)] ->
  hb_inv g E (lmq_hb T f hb) [(f, MF_BLOCK)].
Proof using.
  intros g E hb T f HI HK HK2. unfold hb_inv in *.
  destruct HK as [(Hne & ->) | (Hnil & HT)].
  - assert (Hx : forall X, hx g X = [])
      by (intros X; unfold hx; destruct (lg_T g) eqn:E0; [congruence | reflexivity]).
    assert (Hl : lmq_hb (lg_T g) f hb = hb)
      by (unfold lmq_hb; destruct (lg_T g) eqn:E0; [congruence | reflexivity]).
    rewrite Hl, Hx. rewrite Hx in HI. exact HI.
  - assert (Hx : forall X, hx g X = X) by (intros X; unfold hx; rewrite Hnil; reflexivity).
    rewrite Hx. rewrite Hx in HI.
    destruct HT as [-> | (f0 & -> & Hin0)].
    + cbn [lmq_hb]. eapply Permutation_trans; [apply perm_skip; exact HI|].
      exact (Permutation_cons_append [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)] (f, MF_BLOCK)).
    + cbn [lmq_hb] in HK2 |- *.
      destruct HK2 as [(Hne & _) | (_ & [Hc | (f' & Ef & Hin)])];
        [exfalso; exact (Hne Hnil) | discriminate Hc |].
      injection Ef; intros; subst f'.
      apply (Permutation_in _ HI) in Hin.
      destruct Hin as [Hm | [Hm | [Hm | []]]].
      * injection Hm as _ Hs. unfold MF_BLOCK, MD_SIZE in Hs. exfalso. lia.
      * injection Hm as _ Hs. unfold MF_BLOCK, MK_SIZE in Hs. exfalso. lia.
      * injection Hm; intros; subst f0. exact HI.
Qed.

(* the payload is an entry block, and not a kept one *)
Lemma lgmq_pl : forall g md mk, LGV B API g -> lenv_ok (lg_E g md mk) ->
  In (e_p0 (lg_E g md mk), Z.of_nat (length (e_pl (lg_E g md mk)))) (blocks (lg_L g) (lg_A g)) /\
  ~ In (e_p0 (lg_E g md mk), Z.of_nat (length (e_pl (lg_E g md mk)))) (lg_T g).
Proof using FF.
  intros g md mk HV HE.
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & Hl & _).
  change (e_p0 (lg_E g md mk)) with (len_p0 g).
  change (e_pl (lg_E g md mk)) with (lg_pl g) in Hl |- *.
  destruct (len_ghost_ok B API FF g HV) as (_ & _ & _ & Hn & _ & Hpos).
  rewrite <- Hn in Hl |- *.
  assert (Hn0 : 0 < lg_n g) by lia.
  destruct (Hpos Hn0) as [Hp0 _]. rewrite Hp0.
  pose proof HV as ((Hpre & _) & _ & _ & Hnk & _).
  split; [|exact (Hnk Hn0)].
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcase & _).
  destruct Hcase as [(Hz & _) | (_ & q & Hq & Hp)]; [exfalso; lia|].
  unfold blocks. apply in_map_iff. exists (q, lg_n g). cbn [fst snd]. rewrite Hp.
  split; [reflexivity | exact Hq].
Qed.

End LM.

Print Assumptions lgmq_bytes_inj.
Print Assumptions lgmq_cstr_inj.
Print Assumptions lgmq_str_arg_inj.
Print Assumptions lgmq_nlk_inj.
Print Assumptions lgmq_iftab_inj.
Print Assumptions lgmq_kept.
Print Assumptions lgmq_hb_in.
Print Assumptions lgmq_room.
Print Assumptions lgmq_hb_next.
Print Assumptions lgmq_pl.
