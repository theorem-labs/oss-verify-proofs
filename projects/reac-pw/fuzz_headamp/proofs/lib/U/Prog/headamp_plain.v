(** headamp_plain_contract (U/Prog/LLVMFuzzerTestOneInput_c.v), [0x147fc, 0x1482c) of the UBSan image: the plain
    parse and check_plain (fuzz_headamp.c:351-353). 0x147fc `addi a1,zero,0xa5; mv a0,s3; mv a2,s4` and
    memset(out, 0xa5, 3 cap + 3) at 0x14808 (ra 0x1480c, U/Prog/memset_c.v); `mv a0,s5; mv a1,s3; mv a2,s2` and
    reac_headamp_prop_parse(null ? 0 : pod, out, cap) at 0x14818 (ra 0x1481c, U/Prog/reac_headamp_prop_parse_c.v,
    res = NULL): its parse_args hold on the memory after the memset (the pod bytes, out writable, errno and the SSP
    cells kept, as U/Prog/HeadSites.v says for this site); it answers parse_props (parse_arg null (buf r)) cap, the
    rc in s6; `mv a1,s6; mv a2,s3; mv a3,s7` and check_plain(plain, rc, out, first) at 0x14828 (ra 0x1482c,
    U/Prog/check_plain_c.v): a0 = a1, and for rc > 0 out and first hold the same 3 rc bytes (HeadSites.site_plain:
    the parse wrote the cells to out; first keeps the first parse's cells, apart from every write since). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require memset_c reac_headamp_prop_parse_c check_plain_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c HeadSites
  SlotInv LLVMFuzzerTestOneInput_c EvtFacts.
Import ListNotations.
Open Scope Z_scope.

Theorem headamp_plain_holds : memset_c.memset_contract ->
  reac_headamp_prop_parse_c.reac_headamp_prop_parse_contract -> check_plain_c.check_plain_contract ->
  headamp_plain_contract.
Proof.
  intros MSET PARSE CKP. unfold headamp_plain_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    inp junk nl cap pod out first lo ev can -> -> -> -> -> -> Hnl Hcap Hpod0 HpodA HPB Hout0 HOC HOROM HFB HSOP
    HSOF HOLO HPLO HFLO HST HLO HSPA HROM HEV HED HG1 HG2 HGD1 HGD2 HF HMI.
  apply or_hide in HSOP, HSOF.
  unfold head_ans, head_len, OUT_LEN, HEAD_PLAIN, HEAD_FREE, FRAME_LOCALS, MID_STACK, PARSE_STACK in *.
  set (r := head_rec inp) in *.
  assert (HB : pod_build inp = (r, snd (pod_build inp))) by (unfold r, head_rec; apply surjective_pairing).
  pose proof (pod_build_wf inp r _ HB) as HWF.
  destruct (buf_header r HWF) as (_ & _ & HU & HL).
  destruct (parse_answer (nl =? 1) (buf r) cap ltac:(lia) ltac:(lia)) as [HOK _].
  destruct (cells_len cap _ ltac:(lia) HOK) as (HCL & Hrc & HNL).
  destruct (bytes_at_bound rsegs m first _ HFB) as [HF0 _].
  pose proof HST as (HLO0 & HSPT & _).
  cbn [disjoint_from] in HED, HGD1, HGD2.
  destruct HED as (D1 & D2 & D3 & D4 & _).
  destruct HGD1 as (G1 & G2 & G3 & _). destruct HGD2 as (G4 & G5 & G6 & _).
  apply or_hide in D1, D2, D3, D4, G1, G2, G3, G4, G5, G6.
  (* 0x147fc addi a1,zero,0xa5; mv a0,s3; mv a2,s4; jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := junk); [rewrite !unsigned_lit by lia; exact HOC | exact HMI]. }
  intros ms' Hpost. unfold memset_c.memset_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                     E & MU1 & WM1 & MI1 & CB1).
  subst ms'. rewrite !unsigned_lit in MU1, CB1 by lia. ret_even.
  pose proof (rw_cells_CB_wr m1 out _ _ CB1) as HOW1. rewrite Z2Nat.id in HOW1 by lia.
  assert (HPB1 : bytes_at rsegs m1 pod (buf r)).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HPB MU1). cbn [disjoint_from].
    split; [unfold or_h in HSOP; lia | exact I]. }
  assert (HFB1 : bytes_at rsegs m1 first (ha_cells_bytes (ans_cells (parse_props (parse_arg (nl =? 1) (buf r)) cap)))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HFB MU1). cbn [disjoint_from]. rewrite HCL.
    split; [unfold or_h in HSOF; lia | exact I]. }
  assert (HEV1 : rw_cells rsegs m1 (PARSE_ERRNO tp) [C4 ev]).
  { apply (rw_cells_transport rsegs _ m m1 _ _ HEV MU1 WM1). cbn [disjoint_from cells_size csize].
    split; [unfold or_h in D3; lia | exact I]. }
  assert (HG1' : bytes_at rsegs m1 PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HG1 MU1). cbn [disjoint_from]. rewrite length_le8.
    split; [unfold or_h in G2; lia | exact I]. }
  assert (HG2' : bytes_at rsegs m1 PARSE_SSP_GUARD (le8 can)).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HG2 MU1). cbn [disjoint_from]. rewrite length_le8.
    split; [unfold or_h in G5; lia | exact I]. }
  assert (HST1 : stk rsegs m1 lo (bv_unsigned sp + 472)).
  { apply (stk_transport_disjoint rsegs _ m m1 _ _ HST MU1 WM1). cbn [disjoint_from]. split; [lia | exact I]. }
  (* 0x1480c mv a0,s5; mv a1,s3; mv a2,s2; jal reac_headamp_prop_parse *)
  step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (null := nl =? 1) (lo := lo) (P := pod) (O := out) (cap := cap) (bs := buf r) (ev := ev)
                      (can := can).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold parse_args.
      split; [exact HPB1|]. split; [exact Hpod0|]. split; [exact HpodA|]. split; [lia|]. split; [exact HU|].
      split; [lia|]. split; [lia|]. split; [exact Hout0|]. split; [exact HOW1|]. split; [lia|].
      split; [unfold or_h in HSOP; lia|].
      split; [left; reflexivity|]. split; [exact HEV1|].
      split; [cbn [disjoint_from]; unfold or_h in D1, D2, D3; repeat split; lia|].
      split; [left; reflexivity|]. split; [exact HG1'|]. split; [exact HG2'|].
      unfold parse_space. cbn [Z.eqb app disjoint_from].
      split; [unfold or_h in G1, G2, G3; repeat split; lia | unfold or_h in G4, G5, G6; repeat split; lia].
    - exact (proj1 (stk_split rsegs m1 lo (bv_unsigned sp) (bv_unsigned sp + 472) HST1 ltac:(lia))).
    - unfold PARSE_STACK. lia.
    - intros a Ha. apply HROM. lia.
    - exact HF.
    - exact MI1. }
  intros ms' Hpost. unfold parse_post in Hpost.
  destruct Hpost as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' &
                     t6'' & F' & fc' & m2 & ev' & E & HF' & MU2 & HO2 & _ & HEV2 & WM2 & MI2 & ST2).
  subst ms'. ret_even.
  unfold parse_writes, PARSE_STACK in MU2. cbn [Z.eqb app] in MU2.
  assert (HFB2 : bytes_at rsegs m2 first (ha_cells_bytes (ans_cells (parse_props (parse_arg (nl =? 1) (buf r)) cap)))).
  { apply (bytes_at_transport rsegs _ m1 m2 _ _ HFB1 MU2). cbn [disjoint_from]. rewrite HCL.
    split; [lia|]. split; [unfold or_h in HSOF; lia|]. split; [unfold or_h in D4; lia | exact I]. }
  (* 0x1481c mv a1,s6; mv a2,s3; mv a3,s7; jal check_plain *)
  step. step. step. step.
  eapply evt_cut.
  { eapply CKP with (lo := lo) (rc := ans_rc (parse_props (parse_arg (nl =? 1) (buf r)) cap))
                    (w := ha_cells_bytes (ans_cells (parse_props (parse_arg (nl =? 1) (buf r)) cap))).
    - reflexivity.
    - reflexivity.
    - lia.
    - intros Hp.
      destruct (site_plain m2 out first lo cap _ ltac:(lia) HOK ltac:(lia) ltac:(lia) HO2 HFB2) as [_ HS].
      rewrite !unsigned_lit by lia. exact (HS Hp).
    - exact ST2.
    - unfold check_plain_c.CHECK_PLAIN_FRAME. lia.
    - intros a Ha. apply HROM. lia.
    - exact MI2. }
  intros ms' (a0' & a1''' & a2''' & a3''' & a4''' & a5''' & a6''' & a7''' & m3 & E & MU3 & WM3 & MI3 & ST3).
  subst ms'. ret_even. unfold check_plain_c.CHECK_PLAIN_FRAME in MU3.
  set (W := [(bv_unsigned sp - 512, bv_unsigned sp); (out, out + 3 * (cap + 1));
             (PARSE_ERRNO tp, PARSE_ERRNO tp + 4)]).
  assert (MUW : munch W m m3).
  { apply (munch_trans W m m2 m3).
    - apply (munch_trans W m m1 m2).
      + refine (munch_weaken _ W m m1 _ MU1).
        unfold sub_fp, W. cbn [outside]. intros x (X1 & X2 & X3 & _). split; [lia | exact I].
      + refine (munch_weaken _ W m1 m2 _ MU2).
        unfold sub_fp, W. cbn [outside]. intros x (X1 & X2 & X3 & _). repeat split; try exact I; lia.
    - refine (munch_weaken _ W m2 m3 _ MU3).
      unfold sub_fp, W. cbn [outside]. intros x (X1 & X2 & X3 & _). split; [lia | exact I]. }
  assert (WMW : wmono rsegs m m3) by exact (wmono_trans rsegs m m1 m3 WM1 (wmono_trans rsegs m1 m2 m3 WM2 WM3)).
  apply evt_done. do 16 eexists. exists F', fc', m3, ev'. split; [reflexivity|].
  split; [exact HF'|].
  split.
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ HEV2 MU3 WM3). cbn [disjoint_from cells_size csize].
    split; [unfold or_h in D1; lia | exact I]. }
  split; [exact MUW|]. split; [exact WMW|]. split; [exact MI3|].
  apply (stk_merge rsegs m3 lo (bv_unsigned sp) (bv_unsigned sp + 472)); [exact ST3 | | lia].
  destruct (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + 472) HST ltac:(lia)) as [_ HS].
  apply (stk_transport_disjoint rsegs W m m3 _ _ HS MUW WMW). unfold W. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [unfold or_h in D1; lia | exact I].
Qed.
