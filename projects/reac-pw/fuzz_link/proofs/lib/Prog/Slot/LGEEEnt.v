(* LGlue's ENTRY_OK: from the entry cut (LFrEn.cut_entry) to the loop head of operation 0, the exit, or the
   end. The chain, each step a lemma below:
     E0  0x1384c -> calloc (1, 8856) at 0x1729c, or the early return at 0x1414c  (LE0.le_E0, cut_evt_or)
     C1  calloc (1, 8856), ra 0x13998: the model block md joins hb                (LFrAl.lfr_calloc)
     E1  0x13998 -> calloc (1, 516)                                                (LE2.le_E1, cut_evt)
     C2  calloc (1, 516), ra 0x139a8: the marks block mk joins hb                 (LFrAl.lfr_calloc)
     E2  0x139a8 -> the loop head 0x13a1c, or the exit 0x1413c (size 0)           (LE2.le_E2, cut_evt_or)
   and the early return runs LEX.le_EXc to the caller's ra (LGEELib.ee_fin). hb ends as [mk; md], a
   permutation of md :: mk :: hx g (lg_T g) = md :: mk :: []. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom CallocSite.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memset_c snprintf_img_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrRun LFrAl LFrLo LFrEn
  LGlue LEDefs LE0 LE2 LEX LGEEOp LGEELib.
Import ListNotations.
Local Open Scope Z_scope.

Section GEE.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Hypothesis MEMSET : memset_contract.
Hypothesis SNP : snprintf_img_contract.

(* E0: the prologue, memset of g_nl, the two interface loops, up to the first calloc; or the early return *)
Lemma ee_E0 : forall g c, CUT B API g L_ENTRY [] (lg_T g) (lentry_ms g) c ->
  SR (ms_segs B) c (fun c' => CUT B API g CALLOC_PC [] (lg_T g) (le_cut1 (lg_G g)) c' \/
                              CUT B API g L_FREE2_RA [] (lg_T g) (le_free2r (lg_S g) (lg_gp g) (lg_R g)) c').
Proof.
  intros g c HE.
  apply (cut_evt_or B API FF g L_ENTRY [] (lg_T g) [] (lentry_ms g) CALLOC_PC (le_cut1 (lg_G g))
           L_FREE2_RA (le_free2r (lg_S g) (lg_gp g) (lg_R g)) c HE).
  - intros t [].
  - intros ms (F & fc & m & -> & FC & HGh & HM).
    pose proof (ee_place g HGh) as HPL.
    destruct HGh as (_ & _ & _ & Hn & _).
    rewrite Hn.
    eapply evt_mono.
    + exact (le_E0 MEMSET SNP (lg_G g) (getr (lg_regs g) 5) (getr (lg_regs g) 6) (getr (lg_regs g) 7)
               (getr (lg_regs g) 12) (getr (lg_regs g) 13) (getr (lg_regs g) 14) (getr (lg_regs g) 15)
               (getr (lg_regs g) 16) (getr (lg_regs g) 17)
               (getr (lg_regs g) 28) (getr (lg_regs g) 29) (getr (lg_regs g) 30) (getr (lg_regs g) 31)
               F fc m HPL FC HM).
    + intros ms' H. exact (ee_eqv_intro _ _ H).
  - intros ms' H. exact (ee_cut1_pc _ _ H).
  - intros ms' H. exact (ee_free2r_pc _ _ _ _ H).
Qed.

(* C1: calloc (1, 8856) *)
Lemma ee_C1 : forall g c, CUT B API g CALLOC_PC [] (lg_T g) (le_cut1 (lg_G g)) c ->
  SR (ms_segs B) c (fun c' => exists md, CUT B API g L_CALLOC1_RA [(md, MD_SIZE)] (lg_T g)
                                 (fun ms => le_cut1r (lg_G g) md ms /\ ee_far g md MD_SIZE) c').
Proof.
  intros g c HC.
  pose proof (cut_lgv B API g _ _ _ _ c HC) as HV.
  pose proof (len_ghost_ok B API FF g HV) as HGh.
  eapply SR_mono.
  - apply (lfr_calloc B API FF g [] (lg_T g) MD_SIZE L_CALLOC1_RA (le_cut1 (lg_G g))
             (fun r => eqv_cl (fun ms => le_cut1r (lg_G g) r ms /\ ee_far g r MD_SIZE)) c).
    + unfold MD_SIZE. lia.
    + exact ee_room_nil.
    + unfold L_CALLOC1_RA. lia.
    + reflexivity.
    + exact HC.
    + intros ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & _).
      repeat split.
    + intros R F fc m regs' m' r HP RP H10 C PM FR H16 HZ. cbv beta.
      destruct HP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F0 & fc0 & m0 & EQ
                      & FC & H26 & BS & KN & FRm & ST).
      destruct (ee_MS_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ) as (ER & EF & Efc & Em). subst R F0 fc0 m0.
      eapply ee_canon; [exact RP|].
      change (reg_get regs' 10 = Z_to_bv 64 r) in H10. rewrite H10.
      pose proof (ee_fresh_blk B API FF g [] r MD_SIZE m' HGh FR H16 ltac:(unfold MD_SIZE; lia) HZ) as BZ.
      pose proof PM as (_ & _ & ST' & _).
      split.
      * do 15 eexists. exists F, fc, m'. split; [reflexivity|].
        split; [exact FC|]. split; [exact H26|].
        split; [exact (ee_base_carry B API FF g [] m m' HV HGh BS C PM)|].
        split; [exact (ee_kern_carry B API FF g [] m m' KN C)|].
        split; [exact (ee_frame_carry B g [] m m' FRm C)|].
        split; [exact BZ | exact ST'].
      * exact (ee_far_fresh B API g [] r MD_SIZE HV FR).
  - intros c' (r & H). exists r. exact (ee_cut_collapse B API g _ _ _ _ c' H).
Qed.

(* E1: 0x13998 -> calloc (1, 516) *)
Lemma ee_E1 : forall g md c,
  CUT B API g L_CALLOC1_RA [(md, MD_SIZE)] (lg_T g)
    (fun ms => le_cut1r (lg_G g) md ms /\ ee_far g md MD_SIZE) c ->
  SR (ms_segs B) c (CUT B API g CALLOC_PC [(md, MD_SIZE)] (lg_T g)
    (fun ms => le_cut2 (lg_G g) md ms /\ ee_far g md MD_SIZE)).
Proof.
  intros g md c HC.
  apply (cut_evt B API FF g L_CALLOC1_RA [(md, MD_SIZE)] (lg_T g) [] _ CALLOC_PC _ c HC).
  - intros t [].
  - intros ms (H1 & Hf). eapply evt_mono; [exact (le_E1 (lg_G g) md ms H1)|].
    intros ms' (H2 & Hfp). apply ee_eqv_intro. split; [split; [exact H2 | exact Hf] | exact (Hfp [])].
  - intros ms' (H & _). exact (ee_cut2_pc _ _ _ H).
Qed.

(* C2: calloc (1, 516) *)
Lemma ee_C2 : forall g md c,
  CUT B API g CALLOC_PC [(md, MD_SIZE)] (lg_T g)
    (fun ms => le_cut2 (lg_G g) md ms /\ ee_far g md MD_SIZE) c ->
  SR (ms_segs B) c (fun c' => exists mk, CUT B API g L_CALLOC2_RA [(mk, MK_SIZE); (md, MD_SIZE)] (lg_T g)
    (fun ms => le_cut2r (lg_G g) md mk ms /\ ee_far g md MD_SIZE /\ ee_far g mk MK_SIZE /\
               (mk + MK_SIZE <= md \/ md + MD_SIZE <= mk)) c').
Proof.
  intros g md c HC.
  pose proof (cut_lgv B API g _ _ _ _ c HC) as HV.
  pose proof (len_ghost_ok B API FF g HV) as HGh.
  eapply SR_mono.
  - apply (lfr_calloc B API FF g [(md, MD_SIZE)] (lg_T g) MK_SIZE L_CALLOC2_RA
             (fun ms => le_cut2 (lg_G g) md ms /\ ee_far g md MD_SIZE)
             (fun r => eqv_cl (fun ms => le_cut2r (lg_G g) md r ms /\ ee_far g md MD_SIZE /\
                                          ee_far g r MK_SIZE /\ (r + MK_SIZE <= md \/ md + MD_SIZE <= r))) c).
    + unfold MK_SIZE. lia.
    + exact (ee_room_md md).
    + unfold L_CALLOC2_RA. lia.
    + reflexivity.
    + exact HC.
    + intros ms ((t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & _) & _).
      repeat split.
    + intros R F fc m regs' m' r (HP & Hfd) RP H10 C PM FR H16 HZ. cbv beta.
      destruct HP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F0 & fc0 & m0 & EQ
                      & FC & H26 & BS & KN & FRm & BZd & ST).
      destruct (ee_MS_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ) as (ER & EF & Efc & Em). subst R F0 fc0 m0.
      eapply ee_canon; [exact RP|].
      change (reg_get regs' 10 = Z_to_bv 64 r) in H10. rewrite H10.
      pose proof (ee_fresh_blk B API FF g _ r MK_SIZE m' HGh FR H16 ltac:(unfold MK_SIZE; lia) HZ) as BZk.
      pose proof PM as (_ & _ & ST' & _).
      pose proof FR as (_ & _ & _ & _ & Hdk & _).
      split.
      * do 15 eexists. exists F, fc, m'. split; [reflexivity|].
        split; [exact FC|]. split; [exact H26|].
        split; [exact (ee_base_carry B API FF g _ m m' HV HGh BS C PM)|].
        split; [exact (ee_kern_carry B API FF g _ m m' KN C)|].
        split; [exact (ee_frame_carry B g _ m m' FRm C)|].
        split; [exact (ee_blk_carry B g [(md, MD_SIZE)] _ md MD_SIZE m m' ltac:(unfold MD_SIZE; lia)
                         (or_introl eq_refl) BZd C)|].
        split; [exact BZk | exact ST'].
      * split; [exact Hfd|]. split; [exact (ee_far_fresh B API g _ r MK_SIZE HV FR)|].
        exact (Hdk md MD_SIZE (or_introl eq_refl)).
  - intros c' (r & H). exists r. exact (ee_cut_collapse B API g _ _ _ _ c' H).
Qed.

(* the loop head's environment from the facts the entry carries *)
Lemma ee_env_ok : forall g md mk m, len_ghost g -> le_place (lg_G g) ->
  1 <= n_len (lg_G g) -> n_len (lg_G g) < 2 ^ 26 ->
  blk_zero (n_S (lg_G g)) md MD_SIZE m -> blk_zero (n_S (lg_G g)) mk MK_SIZE m ->
  ee_far g md MD_SIZE -> ee_far g mk MK_SIZE -> (mk + MK_SIZE <= md \/ md + MD_SIZE <= mk) ->
  lenv_ok (lg_E g md mk).
Proof.
  intros g md mk m (_ & _ & _ & Hn & _ & Hp) HPL H1 H26 BZd BZk Hfd Hfk Hdk.
  refine (le_env_ok (lg_G g) md mk m HPL (conj H1 H26) BZd BZk _ _ _ (lr_bytes_length _)).
  - lia.
  - change (n_len (lg_G g)) with (Z.of_nat (length (lg_pl g))) in *. change (n_p0 (lg_G g)) with (len_p0 g).
    rewrite <- Hn in *. destruct (Hp ltac:(lia)) as (E & _). rewrite E. destruct (Hfd ltac:(lia)); lia.
  - change (n_len (lg_G g)) with (Z.of_nat (length (lg_pl g))) in *. change (n_p0 (lg_G g)) with (len_p0 g).
    rewrite <- Hn in *. destruct (Hp ltac:(lia)) as (E & _). rewrite E. destruct (Hfk ltac:(lia)); lia.
Qed.

(* E2: 0x139a8 -> the loop head of operation 0, or the exit when the input is empty *)
Lemma ee_E2 : forall g md mk c,
  CUT B API g L_CALLOC2_RA [(mk, MK_SIZE); (md, MD_SIZE)] (lg_T g)
    (fun ms => le_cut2r (lg_G g) md mk ms /\ ee_far g md MD_SIZE /\ ee_far g mk MK_SIZE /\
               (mk + MK_SIZE <= md \/ md + MD_SIZE <= mk)) c ->
  SR (ms_segs B) c (fun c' => LH B API g 0 c' \/ EX B API g c').
Proof.
  intros g md mk c HC.
  pose proof (cut_lgv B API g _ _ _ _ c HC) as HV.
  pose proof (len_ghost_ok B API FF g HV) as HGh.
  pose proof (ee_place g HGh) as HPL.
  pose proof (cut_T B API g _ _ _ _ c HC) as HT.
  assert (HI : hb_inv g (lg_E g md mk) [(mk, MK_SIZE); (md, MD_SIZE)] (lg_T g)).
  { unfold hb_inv. rewrite (ee_hx_T g). apply perm_swap. }
  eapply SR_mono.
  - apply (cut_evt_or B API FF g L_CALLOC2_RA _ (lg_T g)
             [(e_md (lg_E g md mk), MD_SIZE); (e_mk (lg_E g md mk), MK_SIZE)] _ L_LH
             (fun ms => lenv_ok (lg_E g md mk) /\ lh_ms (lg_E g md mk) 0 (lg_gp g) ms)
             L_EXIT (ex_ms (lg_E g md mk) (lg_gp g)) c HC (hp_md_mk g (lg_E g md mk) _ (lg_T g) HI HT)).
    + intros ms (H2 & Hfd & Hfk & Hdk).
      pose proof H2 as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m
                        & _ & _ & H26 & _ & _ & _ & BZd & BZk & _).
      eapply evt_mono; [exact (le_E2 (lg_G g) md mk ms HPL H2)|].
      intros ms' ([[Hn1 HL] | [_ HX]] & Hfp); apply ee_eqv_intro; (split; [|exact Hfp]).
      * left. split; [exact (ee_env_ok g md mk m HGh HPL Hn1 H26 BZd BZk Hfd Hfk Hdk) | exact HL].
      * right. exact HX.
    + intros ms' (_ & H). exact (ee_lh_pc _ _ _ _ H).
    + intros ms' H. exact (ee_ex_pc _ _ _ H).
  - intros c' [H1 | H2].
    + left. exists md, mk, [(mk, MK_SIZE); (md, MD_SIZE)], (lg_T g).
      split; [exact (ee_cut_pure B API g _ _ _ _ _ c' H1)|]. split; [exact HI|].
      exact (cut_mono B API g _ _ _ _ _ c' (fun ms H => proj2 H) H1).
    + right. exists md, mk, [(mk, MK_SIZE); (md, MD_SIZE)], (lg_T g). split; [exact HI | exact H2].
Qed.

Theorem glue_entry : ENTRY_OK B API.
Proof.
  intros g c HE. unfold ENT in HE.
  pose proof (cut_T B API g _ _ _ _ c HE) as HT.
  eapply SR_bind; [exact (ee_E0 g c HE)|].
  intros c1 [H1 | H1].
  2: { eapply SR_mono.
       - refine (ee_fin B API FF g [] (lg_T g) c1 (ee_case g [] (lg_T g) HT _) H1).
         rewrite (ee_hx_T g). constructor.
       - intros c' Hf. right. right. exact Hf. }
  eapply SR_bind; [exact (ee_C1 g c1 H1)|].
  intros c2 (md & H2).
  eapply SR_bind; [exact (ee_E1 g md c2 H2)|].
  intros c3 H3.
  eapply SR_bind; [exact (ee_C2 g md c3 H3)|].
  intros c4 (mk & H4).
  eapply SR_mono; [exact (ee_E2 g md mk c4 H4)|].
  intros c' [H | H]; [left; exact H | right; left; exact H].
Qed.

End GEE.

Print Assumptions glue_entry.
About glue_entry.
