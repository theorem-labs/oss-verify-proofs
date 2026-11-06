(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:358-361
   [Apache-2.0]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* The main path of the walk of reac_identity_ingest (fuzz_identity.asan 0x838fc): the prologue, the two
   refusals (id = 0 at 0x83910; p = 0 and len <> 0 at 0x83924), the address dispatch, the five return-0 exits,
   and the hand-over to the three arms (stated in lib/A/Prog/IngestSeg.v, proved in lib/A/Prog/IngestSegVer.v,
   IngestSegFw.v and IngestSegName.v). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentCJ YC4b YC1h YC85
reac_identity_ingest IngestSeg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel RcIdentLib reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require IngestSegVer IngestSegFw IngestSegName.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
(* The three arms. *)
Let SEGVER : ting_seg_ver B := IngestSegVer.pb_ting_seg_ver B LAWS.
Let SEGFW : ting_seg_fw B := IngestSegFw.pb_ing_seg_fw B LAWS.
Let SEGNAME : ting_seg_name B := IngestSegName.pb_ting_seg_name B LAWS.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).
(* After a run whose only writable window is the frame: carry "memory = call-time memory outside the
   frame" and the growth of presence to the new memory. *)
Ltac ing_keep :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HG : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    KEEPM : forall a, 0 <= a < 2 ^ 64 -> ~ (?lo <= a < ?hi) -> aview ?sg (w_H ?W) ?m1 a = aview ?sg (w_H ?W) ?m0 a,
    GROW : forall a, apresent (w_H ?W) ?m0 a -> apresent (w_H ?W) ?m1 a,
    Usp : bv_unsigned (ew _ 2) = _ |- _ =>
    let K2 := fresh "K2" in let G2 := fresh "G2" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview sg (w_H W) m2 a = aview sg (w_H W) m0 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
      intros a Ha Hw; transitivity (aview sg (w_H W) m1 a); [| exact (KEEPM a Ha Hw)];
      apply (kept_of_frame Ex rs (w_H W) m1 m2 (fun x => lo <= x < hi) HFr); [| exact Ha | exact Hw];
      let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
      let Hin := fresh "Hin" in let Hr := fresh "Hr" in
      intros bb wl wh aa Hin Hr;
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin;
      repeat (destruct Hin as [Hin | Hin];
              [ injection Hin as <- <- <-; cbn [base_val] in Hr;
                cbn [ew ewset havoc Nat.eqb Nat.ltb extK] in Hr; rewrite ?Usp in Hr; lia | ]);
      destruct Hin
    | assert (G2 : forall a, apresent (w_H W) m0 a -> apresent (w_H W) m2 a)
        by (let a := fresh "a" in let Hp := fresh "Hp" in
            intros a Hp; exact (apresent_grows _ _ _ a HG (GROW a Hp)));
      clear KEEPM GROW HFr HG; rename K2 into KEEPM; rename G2 into GROW ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
(* At the ret: the post up to the result, the kept clause and the record clause. *)
Ltac ing_fin :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?W) ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HAE : env_agree 32 (Ereg ?regs ?extra) _, E1 : ew _ 1 = getr _ 1, Hra : YK0s.ret_ok _,
    Hsegs : forall a, in_img _ a -> 0 <= a < kLowMemEnd |- _ =>
    let R1 := fresh "R1" in let R10 := fresh "R10" in
    prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat' := fresh "mat" in intros mat';
    unfold treac_identity_ingest_post; split; [reflexivity|];
    exists (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
    split; [unfold EV_INGEST; rewrite Z.add_0_r; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs extra HS);
            [ split; [ intros nn Hnn; repeat first [ rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia ];
                       exact (proj1 HAE nn Hnn)
                     | cbn [ed ewset havoc]; exact (proj2 HAE) ]
            | vm_compute; reflexivity ]|];
    split
  end.
(* The kept clause at the ret, from KEEPM, GROW and the final journal; leaves the image premise. *)
Ltac ing_kept :=
  lazymatch goal with
  | HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HARc : AR _ _ _ _ _ _ _,
    KEEPM : forall a, 0 <= a < 2 ^ 64 -> ~ (_ <= a < _) -> _ = _,
    GROW : forall a, apresent _ _ a -> apresent _ _ a,
    Hceil : alloc_ceiling + INGEST_STK <= spZ ?regs, Hsp : _ <= spZ ?regs <= 2 ^ 47,
    Hlo : _ <= spZ ?regs - INGEST_STK, Hhi : spZ ?regs <= _ |- _ =>
    let HpF := fresh "HpF" in
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpF & _);
    eapply (ing_kept_of B LAWS _ _ _ _ _ _ (spZ regs) _ HARc Hceil ltac:(lia));
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
      intros a Ha Hw _; apply KEEPM; [exact Ha | exact Hw]
    | exact GROW
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HpF; unfold INGEST_STK, ESTACK in *; lia
    | ]
  end.
(* A branch condition on the arguments, as a Prop on id, ad, p, len. *)
Ltac ing_hc :=
  lazymatch goal with
  | Hc : branch_taken _ _ _ = _, E10 : ew ?Ex 10 = Z_to_bv 64 ?id, E11 : ew ?Ex 11 = Z_to_bv 64 ?ad,
    E12 : ew ?Ex 12 = Z_to_bv 64 ?p, E13 : ew ?Ex 13 = Z_to_bv 64 ?len,
    Hid : 0 <= ?id < 2 ^ 64, Had : 0 <= ?ad < 65536, Hp : 0 <= ?p < 2 ^ 64, Hlen : 0 <= ?len < 2 ^ 64 |- _ =>
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc;
    rewrite ?(U_atom Ex 10 id E10 Hid), ?(U_atom Ex 11 ad E11 ltac:(lia)),
      ?(U_atom Ex 12 p E12 Hp), ?(U_atom Ex 13 len E13 Hlen) in Hc;
    rewrite ?U_lit in Hc by lia;
    first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc
          | apply negb_true_iff, Z.eqb_neq in Hc | apply negb_false_iff, Z.eqb_eq in Hc
          | apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ]
  end.
(* One run of the main segment: the only writable window is the frame. *)
Ltac ing_run :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ ?STK ?sp0 _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
    paj_run_tok RUN HS HJ SHOK Bspan_ING;
      [ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
        [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; unfold INGEST_STK, ESTACK in *; lia
        | cbn [YP09.r_whi stack_region]; lia | awr_ok_tac] |];
    ing_keep
  end.
(* The return-0 exits of the main segment: the call is accepted, ING returns (0, idb), nothing was written. *)
Ltac ing_fin0 HNR HREC HING :=
  ing_fin;
  [ lazymatch goal with R10 : getr _ 10 = _ |- _ => rewrite R10 end;
    unfold reac_identity_ingest_c.ingest_ret; rewrite HNR, HING; reflexivity
  | split;
    [ ing_kept;
      let a := fresh "a" in let Hi := fresh "Hi" in let Ha := fresh "Ha" in
      intros a Hi (_ & Ha);
      lazymatch goal with HARc : AR _ _ _ _ _ _ _, Hceil : alloc_ceiling + INGEST_STK <= _,
                          Hslo : alloc_ceiling <= ly_stk_lo _, Hshi : ly_stk_hi _ <= 2 ^ 47 |- _ =>
        exact (proj1 (ting_rec_apart B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HARc Hceil Hslo Hshi HREC Ha) Hi) end
    | intros _; rewrite HING; cbn [snd];
      lazymatch goal with HARc : AR _ _ _ _ _ _ _, Hceil : alloc_ceiling + INGEST_STK <= _,
                          Hslo : alloc_ceiling <= ly_stk_lo _, Hshi : ly_stk_hi _ <= 2 ^ 47,
                          KEEPM : forall a, 0 <= a < 2 ^ 64 -> ~ (_ <= a < _) -> _ = _ |- _ =>
        exact (ting_rec_kept B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc Hceil Hslo Hshi HREC KEEPM)
      end ] ].
(* Run the main path to an arm's entry `stop` (a listing offset). *)
Ltac ing_to stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ ?STK ?sp0 _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK Bspan_ING stop;
      [ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
        [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; unfold INGEST_STK, ESTACK in *; lia
        | cbn [YP09.r_whi stack_region]; lia | awr_ok_tac] |];
    ing_keep
  end.
(* The callee-saved registers the main path does not touch (all but sp). *)
Definition ING_KEPT2 : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma in_kept2_of : forall q, 0 <= q < 32 ->
  existsb (fun r : bv 5 => Z.eqb (bv_unsigned r) q) ING_KEPT2 = true -> In (Z_to_bv 5 q) ING_KEPT2.
Proof.
  intros q Hq H. apply existsb_exists in H as (r & Hin & Hr). apply Z.eqb_eq in Hr.
  replace (Z_to_bv 5 q) with r; [exact Hin|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* An 8-byte save of the frame, from the symbolic state at a hand-over. *)
Ltac ing_frame_val k :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?W) ?msc), Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
    replace (spZ regs - k) with (bv_unsigned (ew Ex 2) + - k) by (rewrite Usp; lia);
    eapply (val8_of_st_ok_pi Ex ss (restrict (w_H W) msc) _ 2%nat (- k) _ _ HS);
    [ cbn [ss_mem]; left; reflexivity
    | reflexivity
    | cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])
    | cbn [sv_denot]; rewrite ?Z.add_0_r;
      first [ match goal with E : ew Ex ?n = getr regs _ |- context [ew Ex ?n] => rewrite E end | idtac ];
      rewrite ?Z_to_bv_bv_unsigned; reflexivity
    | apply bv_unsigned_in_range ]
  end.
(* The hand-over facts of ing_arm_at, at an arm's entry. *)
Ltac ing_arm_at_tac HJc0 Hra Hra4 Hid Hp Hlen Hal16 Hlo Hhi Hpl HNR HREC HPAY Hev Hlive HJ
    E1 E10 E12 E13 E32 Usp HAE KEEPM GROW :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?W) ?msc) |- _ =>
    let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in let Q10 := fresh "Q10" in
    let Q12 := fresh "Q12" in let Q13 := fresh "Q13" in let Q16 := fresh "Q16" in
    prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10;
    prreg HS (12%bv : bv 5) Q12; prreg HS (13%bv : bv 5) Q13; prreg HS (16%bv : bv 5) Q16;
    unfold ing_arm_at;
    split; [exact HJc0|]; split; [exact Hra|]; split; [exact Hra4|]; split; [exact Hid|];
    split; [lia|]; split; [exact Hp|]; split; [exact Hlen|]; split; [exact Hal16|];
    split; [exact Hlo|]; split; [exact Hhi|]; split; [exact Hpl|]; split; [exact HNR|];
    split; [exact HREC|]; split; [exact HPAY|]; split; [exact Hev|]; split; [exact Hlive|];
    split; [exact HJ|];
    split; [rewrite Q10, E10; reflexivity|];
    split; [rewrite Q12, E12; reflexivity|];
    split; [rewrite Q13, E13; reflexivity|];
    split; [rewrite Q16, E32; reflexivity|];
    split; [rewrite Q2; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned, Usp; reflexivity|];
    split; [rewrite Q1, E1; reflexivity|];
    split;
    [ let q := fresh "q" in let Hq := fresh "Hq" in let Hq2 := fresh "Hq2" in let Hc := fresh "Hc" in
      intros q Hq Hq2;
      eapply (regs_kept_of_st_ok_pi _ _ _ _ _ ING_KEPT2 HS HAE ltac:(vm_compute; reflexivity));
      apply in_kept2_of; [unfold acallee_saved in Hq; lia|];
      assert (Hc : q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22
                   \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27)
        by (unfold acallee_saved in Hq; lia);
      clear - Hc;
      repeat (destruct Hc as [Hc | Hc]; [try subst q; vm_compute; reflexivity |]);
      try subst q; vm_compute; reflexivity
    |];
    split; [ing_frame_val 8|]; split; [ing_frame_val 16|]; split; [ing_frame_val 24|];
    split; [exact KEEPM | exact GROW]
  end.
(* ---- the main walk ----------------------------------------------------------------------------- *)
Theorem pb_reac_identity_ingest : treac_identity_ingest_spec B.
Proof.
  unfold treac_identity_ingest_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb
    HJ Hra Hra4 H10 H11 H12 H13 Hid Had Hp Hlen Hal16 Hlo Hhi Hpl HPRE Hev Hlive.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  pose proof (ing_sp B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi) as Hsp.
  pose proof (ing_sp_ceil B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi) as Hceil.
  destruct (ing_entry B LAWS TL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pb HJ Hal16 Hlo Hhi)
    as [HS SHOK].
  pose proof HJ as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & Hstatc & _).
  pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  pose proof Hstatc as (Hsp0al & Hstk0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
  assert (Hslo : alloc_ceiling <= ly_stk_lo lyc) by (rewrite Elo; exact Hceil0).
  assert (Hshi : ly_stk_hi lyc <= 2 ^ 47) by (rewrite Ehi; exact H470).
  remember (EI regs pb) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ing_extra pb)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 id) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 ad) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_ING)
    by (rewrite EL by (unfold A_TEXT; lia); replace 32%nat with (32 + 0)%nat by lia; rewrite ew_Ereg_extra; reflexivity).
  pose proof HJ as HJc0.
  assert (EP : forall j, (j < 17)%nat -> ew E (33 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j)))
    by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia;
        rewrite ew_Ereg_extra; exact (ing_extra_pay pb j Hj)).
  assert (HAE : env_agree 32 (Ereg regs (ing_extra pb)) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  clear HE EL.
  assert (KEEPM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
                    aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by (intros; reflexivity).
  assert (GROW : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros a Ha; exact Ha).
  unfold cfg_at. change (w64 A_reac_identity_ingest) with (Z_to_bv 64 A_reac_identity_ingest).
  (* the prologue: the frame, the saves, a4 := -1; then the test of id at 0x83910 *)
  paj_run_tok RUN HS HJ SHOK Bspan_ING;
    [ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
      [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; unfold INGEST_STK, ESTACK in *; lia
      | cbn [YP09.r_whi stack_region]; lia | awr_ok_tac] |].
  ing_keep.
  (* 0x83910 beqz a0: the call is refused when id = 0 *)
  psrr_branch_tok RUN BR HS SHOK Bspan_ING.
  { rewrite branch_eq_U, (U_atom E 10 id E10 Hid), U_lit in Hc by lia. apply Z.eqb_eq in Hc. subst id.
    assert (HREF : reac_identity_ingest_c.ingest_refused 0 p len = true) by reflexivity.
    paj_run_tok RUN HS HJ SHOK Bspan_ING;
      [ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
        [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; unfold INGEST_STK, ESTACK in *; lia
        | cbn [YP09.r_whi stack_region]; lia | awr_ok_tac] |].
    ing_keep.
    ing_fin.
    { rewrite R10. unfold reac_identity_ingest_c.ingest_ret. rewrite HREF.
      unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
    split.
    { ing_kept. intros a _ (Hr & _). rewrite HREF in Hr. discriminate. }
    intros Hr. rewrite HREF in Hr. discriminate. }
  ing_hc. rename Hc into Hid0.
  (* 0x83914..0x8391c the shadow base; 0x83920 bnez a2 *)
  ing_run.
  let disp arm := idtac;
    destruct (HPRE HNR) as [HREC HPAY];
    (* 0x83928 lui a4,1; 0x8392c beq a1,a4: the model-name arm *)
    ing_run; psrr_branch_tok RUN BR HS SHOK Bspan_ING; ing_hc;
    [ (* ad = 4096; 0x83b40 li a1,2; 0x83b44 bgeu a3,a1 *)
      subst ad; ing_run; psrr_branch_tok RUN BR HS SHOK Bspan_ING; ing_hc;
      [ (* 2 <= len: the name loop at 0x83b50 *) arm
      | (* len < 2: 0x83b48 li a4,0; the tail *)
        assert (HING : RcIdentModel.ING idb 4096 pb = (0, idb))
          by (apply RcIdentLib.ING_name_zero; left; rewrite Hpl; lia);
        ing_run; ing_fin0 HNR HREC HING ]
    | (* 0x83930 li a4,1536; 0x83934 beq a1,a4: the version arm *)
      ing_run; psrr_branch_tok RUN BR HS SHOK Bspan_ING; ing_hc;
      [ (* ad = 1536; 0x8398c li a1,8; 0x83990 bltu a3,a1 *)
        subst ad; ing_run; psrr_branch_tok RUN BR HS SHOK Bspan_ING; ing_hc;
        [ (* len < 8 *)
          assert (HING : RcIdentModel.ING idb 1536 pb = (0, idb))
            by (apply RcIdentLib.ING_ver_short; rewrite Hpl; lia);
          ing_run; ing_fin0 HNR HREC HING
        | (* 8 <= len: the version arm at 0x83994 *) arm ]
      | (* 0x83938 bnez a1 *)
        ing_run; psrr_branch_tok RUN BR HS SHOK Bspan_ING; ing_hc;
        [ (* ad not 0, 4096, 1536 *)
          assert (HING : RcIdentModel.ING idb ad pb = (0, idb))
            by (apply RcIdentLib.ING_other; lia);
          ing_run; ing_fin0 HNR HREC HING
        | (* ad = 0; 0x8393c li a4,4; 0x83940 bltu a3,a4 *)
          subst ad; ing_run; psrr_branch_tok RUN BR HS SHOK Bspan_ING; ing_hc;
          [ (* len < 4 *)
            assert (HING : RcIdentModel.ING idb 0 pb = (0, idb))
              by (apply RcIdentLib.ING_fw_short; rewrite Hpl; lia);
            ing_run; ing_fin0 HNR HREC HING
          | (* 4 <= len: the firmware loop at 0x83944 *) arm ] ] ] ]
  in
  psrr_branch_tok RUN BR HS SHOK Bspan_ING; ing_hc;
  [ (* p <> 0: accepted *)
    assert (HNR : reac_identity_ingest_c.ingest_refused id p len = false)
      by (unfold reac_identity_ingest_c.ingest_refused;
          rewrite (proj2 (Z.eqb_neq id 0) Hid0), (proj2 (Z.eqb_neq p 0) Hc), andb_false_r; reflexivity);
    disp idtac
  | (* p = 0; 0x83924 bnez a3 *)
    subst p; ing_run; psrr_branch_tok RUN BR HS SHOK Bspan_ING; ing_hc;
    [ (* len <> 0: refused *)
      assert (HREF : reac_identity_ingest_c.ingest_refused id 0 len = true)
        by (unfold reac_identity_ingest_c.ingest_refused; rewrite (proj2 (Z.eqb_neq len 0) Hc); apply orb_true_r);
      ing_run; ing_fin;
      [ lazymatch goal with R10 : getr _ 10 = _ |- _ => rewrite R10 end;
        unfold reac_identity_ingest_c.ingest_ret; rewrite HREF;
        unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity
      | split;
        [ ing_kept; let a := fresh "a" in let Hr := fresh "Hr" in
          intros a _ (Hr & _); rewrite HREF in Hr; discriminate
        | let Hr := fresh "Hr" in intros Hr; rewrite HREF in Hr; discriminate ] ]
    | (* len = 0: accepted *)
      subst len;
      assert (HNR : reac_identity_ingest_c.ingest_refused id 0 0 = false)
        by (unfold reac_identity_ingest_c.ingest_refused; rewrite (proj2 (Z.eqb_neq id 0) Hid0); reflexivity);
      disp ltac:(exfalso; lia) ] ].
  - (* the model-name arm: run to 0x83b50 and hand over *)
    ing_to 13380%Z.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H W) _) |- _ => pmkst HS end.
    change (BASE + 13380) with (BASE + AF_ing_name).
    eapply SEGNAME;
      [ ing_arm_at_tac HJc0 Hra Hra4 Hid Hp Hlen Hal16 Hlo Hhi Hpl HNR HREC HPAY Hev Hlive HJ
          E1 E10 E12 E13 E32 Usp HAE KEEPM GROW
      | reflexivity | lia].
  - (* the version arm: run to 0x83994 and hand over *)
    ing_to 12936%Z.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H W) _) |- _ => pmkst HS end.
    change (BASE + 12936) with (BASE + AF_ing_ver).
    eapply SEGVER;
      [ ing_arm_at_tac HJc0 Hra Hra4 Hid Hp Hlen Hal16 Hlo Hhi Hpl HNR HREC HPAY Hev Hlive HJ
          E1 E10 E12 E13 E32 Usp HAE KEEPM GROW
      | reflexivity | lia].
  - (* the firmware arm: run to 0x83944 and hand over; a4 = 4 *)
    ing_to 12856%Z.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H W) _) |- _ => pmkst HS end.
    change (BASE + 12856) with (BASE + AF_ing_fw).
    eapply SEGFW;
      [ ing_arm_at_tac HJc0 Hra Hra4 Hid Hp Hlen Hal16 Hlo Hhi Hpl HNR HREC HPAY Hev Hlive HJ
          E1 E10 E12 E13 E32 Usp HAE KEEPM GROW
      | reflexivity | lia |].
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H W) _) |- _ =>
      let Q14 := fresh "Q14" in prreg HS (14%bv : bv 5) Q14; rewrite Q14; reflexivity
    end.
Qed.
End h.
End f.
End d.
