(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 467 of its 509 lines of code are new or changed and 422 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/Slot/LC0Chk.v, with its module paths and module names changed; 187 of its 199 lines of code are new or changed and 497 lines of the source are left out. *)
(* ARM 0 (op_read) at the SR level: LGlue's ARM 0 from LC0's five segments and the arm's four
   allocator calls.

     loop head (lh_ms /\ lh_op 0)  --c0_s1-->  c0_cut_kc  --text_buf (kc)-->  c0_ret_kc
       --c0_s2-->  c0_cut_ac  --text_buf (ac)-->  c0_ret_ac  --c0_s3a-->  c0_mid  --c0_s3b-->  c0_cut_fk
       --free (kind) / free (NULL)-->  c0_ret_fk  --c0_s4-->  c0_cut_fa  --free (alias) / free (NULL)-->
       c0_ret_fa  --c0_s5-->  the next loop head or the exit

   Each segment is one LFrRun.cut_evt (the last one cut_evt_or); each call is an LFrAl / LFrTx step with an
   LG0Ad adapter at its return address. The slot's blocks go hb -> opt_hb K (kc + 1) hb ->
   opt_hb A (ac + 1) (opt_hb K (kc + 1) hb) -> opt_hb A (ac + 1) hb -> hb, so the arm ends with the hb and
   T it started with. The callee contracts are the Section hypotheses of the LC0 files, with their names, and
   LFrTx's TBUF for text_buf. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem text_buf_c
  kernel_c memset_c model_read_c reac_link_alias_read_c check_socket_c index_of_c check_refused_c check_bounds_c
  check_read_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrRun LFrAl LFrTx LGlue
  LC0Defs LC0Head LC0Buf LC0Rd LC0Chk LC0Tail LG0Lib LG0Ad.
Import ListNotations.
Local Open Scope Z_scope.

(* the cut after S1: the head chose the selector and the two caps *)
Definition g0_kcP (E : lenv) (i : Z) (gp : word) (ms : machine_state) : Prop :=
  exists sel kc ac P N kbs mbs gbs, c0_cut_kc E i gp P N sel kc ac kbs mbs gbs ms.

(* one existential of a cut predicate out of the CUT *)
Tactic Notation "g0_open" constr(L) hyp(H) ident(x) := apply L in H; destruct H as [x H]; cbv beta in H.

Section G0.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Hypothesis KERN : kernel_contract.
Hypothesis MEMSET_C : memset_contract.
Hypothesis MR : model_read_contract.
Hypothesis AR : reac_link_alias_read_contract.
Hypothesis CSOCK : check_socket_contract.
Hypothesis IDXOF : index_of_contract_P.
Hypothesis CREF : check_refused_contract.
Hypothesis CBND : check_bounds_contract.
Hypothesis CREAD : check_read_contract.
Hypothesis CREQ : check_requests_contract.

Hypothesis TBUF : forall fx' : YK11.FPState, @text_buf_contract fx' rc B API.

(* S1 with the head's choices inside the cut predicate *)
Lemma g0_s1 : forall E i gp ms, lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 0 ->
  evt rsegs (eqv_cl (fun ms' => g0_kcP E i gp ms' /\ seg_fp (e_S E) (c0_hp2 E) (ms_mem ms) (ms_mem ms'))) ms.
Proof using KERN.
  intros E i gp ms HE HL HO. destruct (c0_s1 KERN E i gp ms HE HL HO) as (sel & kc & ac & H).
  eapply evt_mono; [exact H|]. intros ms' (c & ((P & N & kbs & mbs & gbs & Hc) & Hf) & Heq).
  exists c. split; [split; [exists sel, kc, ac, P, N, kbs, mbs, gbs; exact Hc | exact Hf] | exact Heq].
Qed.

Theorem glue_arm0 : ARM B API 0.
Proof.
  intros g md mk hb T i c OK HI Hi HC.
  pose proof (cut_T B API g L_LH hb T _ c HC) as HT.
  pose proof (cut_lgv B API g L_LH hb T _ c HC) as HV.
  pose proof (hp_md_mk g (lg_E g md mk) hb T HI HT) as HP2.
  assert (Hmd : In (md, MD_SIZE) hb) by exact (proj1 (HP2 _ (or_introl eq_refl))).
  assert (Hmk : In (mk, MK_SIZE) hb) by exact (proj1 (HP2 _ (or_intror (or_introl eq_refl)))).
  destruct (g0_room0 g (lg_E g md mk) hb T HI HT) as [HL3 HB3].
  (* S1: the loop head to the call of text_buf (kc) *)
  eapply SR_bind.
  { apply (cut_evt B API FF g L_LH hb T (c0_hp2 (lg_E g md mk)) _ TEXT_BUF (g0_kcP (lg_E g md mk) i (lg_gp g))
             c HC HP2).
    - intros ms (HL & HO). exact (g0_s1 (lg_E g md mk) i (lg_gp g) ms OK HL HO).
    - intros ms' H. unfold g0_kcP in H. g0_ex H. exact (g0_pc_kc _ _ _ _ _ _ _ _ _ _ _ _ H). }
  intros c1 HC1. unfold g0_kcP in HC1.
  g0_open (g0_cut_ex B API FF) HC1 sel. g0_open (g0_cut_ex B API FF) HC1 kc.
  g0_open (g0_cut_ex B API FF) HC1 ac. g0_open (g0_cut_ex B API FF) HC1 P.
  g0_open (g0_cut_ex B API FF) HC1 N. g0_open (g0_cut_ex B API FF) HC1 kbs.
  g0_open (g0_cut_ex B API FF) HC1 mbs. g0_open (g0_cut_ex B API FF) HC1 gbs.
  destruct (g0_cut_pure B API FF g TEXT_BUF hb T _ _ c1 HC1 (fun ms H => g0_kc_caps _ _ _ _ _ _ _ _ _ _ _ _ H))
    as [Hkc Hac].
  (* text_buf (kc) *)
  eapply SR_bind.
  { apply (lfr_text_buf B API FF TBUF g hb T kc C0_RA_KC (c0_cut_kc (lg_E g md mk) i (lg_gp g) P N sel kc ac kbs mbs gbs)
             (fun r => eqv_cl (c0_ret_kc (lg_E g md mk) i (lg_gp g) P N sel kc ac r kbs mbs gbs)) c1
             Hkc (g0_room hb HL3 HB3) ltac:(unfold C0_RA_KC; lia) ltac:(reflexivity) HC1).
    - intros ms H. exact (g0_rg_kc _ _ _ _ _ _ _ _ _ _ _ _ H).
    - intros R F fc m regs' m' r H RP H10 CR PM Z0 Z1.
      exact (g0_ad_kc B API FF g md mk hb i (lg_gp g) P N sel kc ac kbs mbs gbs R F fc m regs' m' r
               HV OK Hmd Hmk H RP H10 CR PM Z0 Z1). }
  intros c2 (K & HC2). apply (g0_cut_cl B API FF) in HC2.
  destruct (g0_cut_pure B API FF g C0_RA_KC _ T _ _ c2 HC2 (fun ms H => g0_rkc_K _ _ _ _ _ _ _ _ _ _ _ _ _ H))
    as [HK0 HKnz].
  (* S2: to the call of text_buf (ac) *)
  eapply SR_bind.
  { apply (cut_evt B API FF g C0_RA_KC (opt_hb K (kc + 1) hb) T (c0_hpK (lg_E g md mk) kc K) _ TEXT_BUF
             (c0_cut_ac (lg_E g md mk) i (lg_gp g) P N sel kc ac K kbs mbs gbs) c2 HC2
             (g0_hp_opt (c0_hp2 (lg_E g md mk)) hb T kc K HP2 HT Hkc HKnz)).
    - intros ms H. exact (c0_s2 (lg_E g md mk) i (lg_gp g) P N sel kc ac K kbs mbs gbs ms OK H).
    - intros ms' H. exact (g0_pc_ac _ _ _ _ _ _ _ _ _ _ _ _ _ H). }
  intros c3 HC3.
  (* text_buf (ac) *)
  eapply SR_bind.
  { apply (lfr_text_buf B API FF TBUF g (opt_hb K (kc + 1) hb) T ac C0_RA_AC
             (c0_cut_ac (lg_E g md mk) i (lg_gp g) P N sel kc ac K kbs mbs gbs)
             (fun r => eqv_cl (c0_ret_ac (lg_E g md mk) i (lg_gp g) P N sel kc ac K r kbs mbs gbs)) c3
             Hac (g0_room_opt hb K (kc + 1) HL3 HB3 ltac:(lia)) ltac:(unfold C0_RA_AC; lia) ltac:(reflexivity) HC3).
    - intros ms H. exact (g0_rg_ac _ _ _ _ _ _ _ _ _ _ _ _ _ H).
    - intros R F fc m regs' m' r H RP H10 CR PM Z0 Z1.
      exact (g0_ad_ac B API FF g md mk (opt_hb K (kc + 1) hb) i (lg_gp g) P N sel kc ac K kbs mbs gbs
               R F fc m regs' m' r HV OK (g0_in_opt _ _ _ _ Hmd) (g0_in_opt _ _ _ _ Hmk)
               (fun Hk => g0_in_opt_self K (kc + 1) hb (HKnz Hk)) H RP H10 CR PM Z0 Z1). }
  intros c4 (A & HC4). apply (g0_cut_cl B API FF) in HC4.
  destruct (g0_cut_pure B API FF g C0_RA_AC _ T _ _ c4 HC4 (fun ms H => g0_rac_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ H))
    as [HA0 HAnz].
  assert (HPKA : forall t, In t (c0_hpKA (lg_E g md mk) kc K ac A) ->
                   In t (opt_hb A (ac + 1) (opt_hb K (kc + 1) hb)) /\ ~ In t T).
  { intros t Ht. unfold c0_hpKA in Ht. rewrite app_assoc in Ht.
    exact (g0_hp_opt (c0_hp2 (lg_E g md mk) ++ c0_opt kc K) (opt_hb K (kc + 1) hb) T ac A
             (g0_hp_opt (c0_hp2 (lg_E g md mk)) hb T kc K HP2 HT Hkc HKnz) HT Hac HAnz t Ht). }
  (* S3a: to the return of reac_link_alias_read *)
  eapply SR_bind.
  { apply (cut_evt B API FF g C0_RA_AC (opt_hb A (ac + 1) (opt_hb K (kc + 1) hb)) T
             (c0_hpKA (lg_E g md mk) kc K ac A) _ C0_MID
             (fun ms => exists kbs' mbs' op0 want rcv,
                c0_mid (lg_E g md mk) i (lg_gp g) P N sel kc ac K A op0 want rcv kbs' mbs' gbs ms) c4 HC4 HPKA).
    - intros ms H. exact (c0_s3a MEMSET_C MR AR (lg_E g md mk) i (lg_gp g) P N sel kc ac K A kbs mbs gbs ms OK H).
    - intros ms' (kbs' & mbs' & op0 & want & rcv & H). exact (g0_pc_mid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H). }
  intros c5 HC5.
  g0_open (g0_cut_ex B API FF) HC5 kbs'. g0_open (g0_cut_ex B API FF) HC5 mbs'.
  g0_open (g0_cut_ex B API FF) HC5 op0. g0_open (g0_cut_ex B API FF) HC5 want.
  g0_open (g0_cut_ex B API FF) HC5 rcv.
  (* S3b: the six checks, to the call of free (kind) *)
  eapply SR_bind.
  { apply (cut_evt B API FF g C0_MID (opt_hb A (ac + 1) (opt_hb K (kc + 1) hb)) T
             (c0_hpKA (lg_E g md mk) kc K ac A) _ LLVM_FREE
             (c0_cut_fk (lg_E g md mk) i (lg_gp g) P N sel kc ac K A kbs' mbs' gbs) c5 HC5 HPKA).
    - intros ms H. exact (c0_s3b CSOCK IDXOF CREF CBND CREAD CREQ (lg_E g md mk) i (lg_gp g) P N sel kc ac K A
                            op0 want rcv kbs' mbs' gbs ms OK H).
    - intros ms' H. exact (g0_pc_fk _ _ _ _ _ _ _ _ _ _ _ _ _ _ H). }
  intros c6 HC6.
  (* free (kind): the block K leaves hb, or free (NULL) *)
  assert (SFK : SR (ms_segs B) c6 (CUT B API g C0_RA_FK (opt_hb A (ac + 1) hb) T
                                     (c0_ret_fk (lg_E g md mk) i (lg_gp g) P N ac A kbs' mbs' gbs))).
  { destruct (Z.eq_dec kc 0) as [Hk0 | Hk0].
    - replace (opt_hb K (kc + 1) hb) with hb in HC6 by (rewrite (HK0 Hk0); reflexivity).
      eapply SR_mono.
      + apply (lfr_free_null B API FF g (opt_hb A (ac + 1) hb) T C0_RA_FK
                 (c0_cut_fk (lg_E g md mk) i (lg_gp g) P N sel kc ac K A kbs' mbs' gbs)
                 (eqv_cl (c0_ret_fk (lg_E g md mk) i (lg_gp g) P N ac A kbs' mbs' gbs)) c6
                 ltac:(unfold C0_RA_FK; lia) ltac:(reflexivity) HC6).
        * intros ms H. destruct (g0_rg_fk _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (G1 & _ & _ & G10).
          split; [exact G1 | exact (eq_trans G10 (f_equal (Z_to_bv 64) (HK0 Hk0)))].
        * intros R F fc m H. exact (g0_ad_fk0 _ _ _ _ _ _ _ _ _ _ _ _ _ R F fc m H).
      + intros c' H. exact (g0_cut_cl B API FF _ _ _ _ _ c' H).
    - assert (HKz : K <> 0) by exact (HKnz Hk0).
      rewrite (g0_opt_nz K (kc + 1) hb HKz), g0_opt_cons in HC6.
      eapply SR_mono.
      + apply (lfr_free B API FF g (opt_hb A (ac + 1) []) K (kc + 1) hb T C0_RA_FK
                 (c0_cut_fk (lg_E g md mk) i (lg_gp g) P N sel kc ac K A kbs' mbs' gbs)
                 (eqv_cl (c0_ret_fk (lg_E g md mk) i (lg_gp g) P N ac A kbs' mbs' gbs)) c6
                 (g0_notT T K (kc + 1) HT ltac:(unfold MF_BLOCK; lia)) ltac:(unfold C0_RA_FK; lia) ltac:(reflexivity)
                 HC6).
        * intros ms H. exact (g0_rg_fk _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
        * intros R F fc m regs' m' H RP CR PM.
          exact (g0_ad_fk B API FF g md mk (opt_hb A (ac + 1) [] ++ hb) i (lg_gp g) P N sel kc ac K A kbs' mbs' gbs
                   R F fc m regs' m' HV OK (g0_in_app _ _ _ Hmd) (g0_in_app _ _ _ Hmk) H RP CR PM).
      + intros c' H. rewrite g0_opt_app in H. exact (g0_cut_cl B API FF _ _ _ _ _ c' H). }
  eapply SR_bind; [exact SFK|]. intros c7 HC7.
  (* S4: to the call of free (alias) *)
  eapply SR_bind.
  { apply (cut_evt B API FF g C0_RA_FK (opt_hb A (ac + 1) hb) T (c0_hpA (lg_E g md mk) ac A) _ LLVM_FREE
             (c0_cut_fa (lg_E g md mk) i (lg_gp g) P N ac A kbs' mbs' gbs) c7 HC7
             (g0_hp_opt (c0_hp2 (lg_E g md mk)) hb T ac A HP2 HT Hac HAnz)).
    - intros ms H. exact (c0_s4 (lg_E g md mk) i (lg_gp g) P N ac A kbs' mbs' gbs ms OK H).
    - intros ms' H. exact (g0_pc_fa _ _ _ _ _ _ _ _ _ _ _ H). }
  intros c8 HC8.
  (* free (alias): the block A leaves hb, or free (NULL) *)
  assert (SFA : SR (ms_segs B) c8 (CUT B API g C0_RA_FA hb T
                                     (c0_ret_fa (lg_E g md mk) i (lg_gp g) P N kbs' mbs' gbs))).
  { destruct (Z.eq_dec ac 0) as [Ha0 | Ha0].
    - replace (opt_hb A (ac + 1) hb) with hb in HC8 by (rewrite (HA0 Ha0); reflexivity).
      eapply SR_mono.
      + apply (lfr_free_null B API FF g hb T C0_RA_FA
                 (c0_cut_fa (lg_E g md mk) i (lg_gp g) P N ac A kbs' mbs' gbs)
                 (eqv_cl (c0_ret_fa (lg_E g md mk) i (lg_gp g) P N kbs' mbs' gbs)) c8
                 ltac:(unfold C0_RA_FA; lia) ltac:(reflexivity) HC8).
        * intros ms H. destruct (g0_rg_fa _ _ _ _ _ _ _ _ _ _ _ H) as (G1 & _ & _ & G10).
          split; [exact G1 | exact (eq_trans G10 (f_equal (Z_to_bv 64) (HA0 Ha0)))].
        * intros R F fc m H. exact (g0_ad_fa0 _ _ _ _ _ _ _ _ _ _ R F fc m H).
      + intros c' H. exact (g0_cut_cl B API FF _ _ _ _ _ c' H).
    - assert (HAz : A <> 0) by exact (HAnz Ha0).
      rewrite (g0_opt_nz A (ac + 1) hb HAz) in HC8.
      change ((A, ac + 1) :: hb) with ([] ++ (A, ac + 1) :: hb) in HC8.
      eapply SR_mono.
      + apply (lfr_free B API FF g [] A (ac + 1) hb T C0_RA_FA
                 (c0_cut_fa (lg_E g md mk) i (lg_gp g) P N ac A kbs' mbs' gbs)
                 (eqv_cl (c0_ret_fa (lg_E g md mk) i (lg_gp g) P N kbs' mbs' gbs)) c8
                 (g0_notT T A (ac + 1) HT ltac:(unfold MF_BLOCK; lia)) ltac:(unfold C0_RA_FA; lia) ltac:(reflexivity)
                 HC8).
        * intros ms H. exact (g0_rg_fa _ _ _ _ _ _ _ _ _ _ _ H).
        * intros R F fc m regs' m' H RP CR PM.
          exact (g0_ad_fa B API FF g md mk ([] ++ hb) i (lg_gp g) P N ac A kbs' mbs' gbs
                   R F fc m regs' m' HV OK Hmd Hmk H RP CR PM).
      + intros c' H. exact (g0_cut_cl B API FF _ _ _ _ _ c' H). }
  eapply SR_bind; [exact SFA|]. intros c9 HC9.
  (* S5: to the next loop head or the exit *)
  eapply SR_mono.
  - apply (cut_evt_or B API FF g C0_RA_FA hb T (c0_hp2 (lg_E g md mk)) _ L_LH
             (fun ms => i < 47 /\ lh_ms (lg_E g md mk) (i + 1) (lg_gp g) ms) L_EXIT
             (ex_ms (lg_E g md mk) (lg_gp g)) c9 HC9 HP2).
    + intros ms H. exact (c0_s5 (lg_E g md mk) i (lg_gp g) P N kbs' mbs' gbs ms OK H).
    + intros ms' (_ & H). exact (g0_pc_lh _ _ _ _ H).
    + intros ms' H. exact (g0_pc_ex _ _ _ H).
  - intros c' [H1 | H2]; unfold arm_post; exists hb, T; split; try exact HI.
    + left. split.
      * destruct H1 as (fx1 & L1 & A1 & regs1 & mem1 & md1 & _ & _ & _ & (c10 & (Hlt & _) & _)). exact Hlt.
      * exact (cut_mono B API g L_LH hb T _ _ c' (fun ms H => proj2 H) H1).
    + right. exact H2.
Qed.

End G0.

About glue_arm0.
Print Assumptions glue_arm0.
