(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image-B walk segment; lines 192-198 follow the shape of cgif_file_fuzzer lib/A/ACgb.v:547 (licscan run). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/LLVMFEntryRawRd0.v, with its module names changed; 186 of its 232 lines of code are new or changed and 153 lines of the source are left out. *)
(* Ported from lib/A/Prog/GrantEntryRawBs2.v of a working branch 7c8c67da870 (blob bfa4ac4115f). *)
(* The hand-built allocation phase of LLVMFuzzerTestOneInput on image B, segment Bs2: the
   slots 0x81918 .. 0x81934 (GR_bs2 .. GR_bs3 of LLVMFEntryRawDefs.v).

   0x81918  jal reac_grant_build_sweep   (NULL, 1, &raw, t)
   0x8191c  mv  a3,s4                    t, for the next call
   0x81920  li  s4,-1
   0x81924  bne a0,s4,0x81d98            the abort, not taken: the answer is -1
   0x81928  li  a1,128
   0x8192c  mv  a0,s2
   0x81930  li  a2,0
   0x81934  jal reac_grant_build_sweep   (the next cut, GR_bs3)

   The call is made through `gcall` with reac_grant_build_sweep's contract. The sweep pointer
   is NULL, so `bsw_ok` is false: the callee owns no bytes of the caller (its FP is empty),
   answers -1, and keeps the blocks, the frames and the state up to its fs part. Its journal
   keeps every byte the phase's facts read (call_keep). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib YC1g YC1h YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat LLVMFEntrySetDefs LLVMFEntryRawDefs LLVMFEntryRawLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel BuildSweepLink.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section b. Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis BSW : tb_reac_grant_build_sweep_spec B.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the symbolic states of the two runs: no region, every register its own atom ---- *)
Definition ss_bs2 : sstate := mkSS 0xedc sr_atoms [] None (mkFacts [] [] []).
Definition ss_ret : sstate := mkSS 0xee0 sr_atoms [] None (mkFacts [] [] []).

Ltac bs_reg HS EE r n X := prreg HS r X; rewrite (EE n r eq_refl) in X.

Theorem seg_raw_bs2 : forall POST, ge_from B MT POST (GR_bs3I B MT) -> ge_from B MT POST (GR_bs2I B MT).
Proof.
  intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
  destruct HGI as (t & s & HRC & Hk & Hacc & Hbl & Htab & Hs4 & R20 & R18 & R10 & R11 & R12 & R13).
  pose proof HRC as (HBD & Hn & R19 & R21 & R22 & R23 & H48 & HSL & HFB0 & HFB1 & HWS & HST & HREL & HI1).
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSH & HFL & Hlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  (* the geometry *)
  pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFoff & HSHeq).
  pose proof (ge_sp_facts B MT cx HB) as (Hal & Hlo & Hhi & Hsp1).
  pose proof (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EFA.
  pose proof (proj1 alloc_ceiling_val) as AC.
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hg8 : gF cx fp mod 8 = 0).
  { pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp (proj1 HJ) Hfin) as (H64 & _).
    rewrite EFA in H64. lia. }
  destruct (g_ly B cx fp k ly3 S3 W3 (ms_mem ms3) md3 HJ) as [Etop _].
  pose proof HB as (HPRE0 & _).
  pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & _ & _ & _ & _ & _ & Htop0 & _).
  pose proof Htab as (Hint & Ht0 & HTl & _).
  assert (Hbl0 : forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3))
    by (intros p n Hpn; unfold gblk2 in Hbl; rewrite Hbl; apply in_or_app; left; exact Hpn).
  assert (Hok : bsw_ok 0 (gF cx fp + GO_RAW) 1 (raw_b cx) (raw_w cx) = false) by reflexivity.
  (* ---- 0x81918: the jal ---- *)
  assert (HMA : gmach cx ms3 0xedc) by exact (conj Hpc (conj Hrv (conj Hsvc (conj Hrom (conj Hfrg (conj Hfc HG)))))).
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros nn r Hnn; subst E; apply ew_Eimg_Ereg_nat; exact Hnn).
  assert (HS : st_ok_pi SEGS VAL E ss_bs2 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0xedc)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_bs2. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) mem)) by constructor.
  subst mem.
  paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_nil |].
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- SRr _ _ (mkCfg ?m ?md) _ =>
    rename HSx into HSc; rename m into msc; set (mdc := md) in * end.
  assert (K0 : forall a, aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a. match goal with H1 : frame_of _ _ (ms_mem ms3) (ms_mem msc) |- _ =>
      exact (frame_nil_eq _ _ _ _ _ eq_refl H1 a) end. }
  prreg HSc (1%bv : bv 5) C1.
  bs_reg HSc EE (2%bv : bv 5) 2%nat C2. bs_reg HSc EE (3%bv : bv 5) 3%nat C3.
  bs_reg HSc EE (4%bv : bv 5) 4%nat C4. bs_reg HSc EE (8%bv : bv 5) 8%nat C8.
  bs_reg HSc EE (9%bv : bv 5) 9%nat C9. bs_reg HSc EE (10%bv : bv 5) 10%nat C10.
  bs_reg HSc EE (11%bv : bv 5) 11%nat C11. bs_reg HSc EE (12%bv : bv 5) 12%nat C12.
  bs_reg HSc EE (13%bv : bv 5) 13%nat C13. bs_reg HSc EE (18%bv : bv 5) 18%nat C18.
  bs_reg HSc EE (19%bv : bv 5) 19%nat C19. bs_reg HSc EE (20%bv : bv 5) 20%nat C20.
  bs_reg HSc EE (21%bv : bv 5) 21%nat C21. bs_reg HSc EE (22%bv : bv 5) 22%nat C22.
  bs_reg HSc EE (23%bv : bv 5) 23%nat C23.
  rewrite (st_ok_restrict_mkst _ _ _ _ _ HSc eq_refl). cbn [ss_pc setpc].
  rewrite pa_sigma_reac_grant_build_sweep.
  subst regs.
  assert (C2' : getr (ms_regs msc) 2 = w64 (c_sp1 cx)) by (rewrite C2; exact G2).
  assert (C8' : getr (ms_regs msc) 8 = w64 (spZ (c_regs cx))) by (rewrite C8; exact G8).
  assert (C3' : getr (ms_regs msc) 3 = getr (c_regs cx) 3) by (rewrite C3; exact G3).
  assert (C4' : getr (ms_regs msc) 4 = getr (c_regs cx) 4) by (rewrite C4; exact G4).
  assert (C10' : getr (ms_regs msc) 10 = w64 0) by (rewrite C10; exact R10).
  assert (C11' : getr (ms_regs msc) 11 = w64 1) by (rewrite C11; exact R11).
  assert (C12' : getr (ms_regs msc) 12 = w64 (gF cx fp + GO_RAW)) by (rewrite C12; exact R12).
  assert (C13' : getr (ms_regs msc) 13 = w64 t) by (rewrite C13; exact R13).
  assert (C1' : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + 0xee0)) by (rewrite C1; reflexivity).
  (* the facts at the callee's entry *)
  assert (H8c : rdword (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 8)
      (fun j _ => K0 _)). exact (proj1 HSV). }
  assert (H16c' : rdword (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 16)
      (fun j _ => K0 _)).
    pose proof (proj2 HSV 0 ltac:(lia)) as S0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in S0 by lia.
    rewrite S0. reflexivity. }
  assert (B0c : aview SEGS (w_H W3) (ms_mem msc) (gF cx fp + GO_RAW) = Some (raw_b cx)) by (rewrite K0; exact HFB0).
  assert (B1c : aview SEGS (w_H W3) (ms_mem msc) (gF cx fp + (GO_RAW + 1)) = Some (raw_w cx)) by (rewrite K0; exact HFB1).
  assert (HTABc : gtab B cx ly3 S3 W3 msc t (GrantSlotPlan.T_end (c_pl cx)))
    by exact (rm_gtab B cx ly3 S3 ly3 S3 W3 ms3 W3 msc t _ Htab Hint (fun a _ => K0 a)).
  assert (Uspc : spZ (ms_regs msc) = c_sp1 cx) by (unfold spZ; rewrite C2'; unfold w64; apply unsigned_lit_small; lia).
  assert (HTOP : spZ (ms_regs msc) + 32 <= ly_top ly3) by (rewrite Uspc, Etop; lia).
  assert (HF7 : Z.of_nat (length (frames S3)) <= 7) by (rewrite HFR; cbn [length Z.of_nat]; lia).
  (* `raw` is a usable object of this frame: its granule's shadow byte is 0x02 *)
  assert (HAL : gF cx fp + GO_RAW <> 0 -> afobj SEGS B ly3 S3 W3 (ms_mem msc) (gF cx fp + GO_RAW) 2 /\
                 garr8 SEGS (mrestrict (w_H W3) (ms_mem msc)) (gF cx fp + GO_RAW) [raw_b cx; raw_w cx]).
  { intros _. split.
    - split; [|split].
      + exists GE_CID, fp. rewrite EFA. split; [exact Hfin|].
        assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity). rewrite Hfb.
        unfold GE_CID, GO_RAW. repeat split; lia.
      + unfold GO_RAW. lia.
      + apply range_addressable_partial; [| unfold GO_RAW; lia | lia].
        unfold shadow_of_addr.
        replace (SHADOW_OFF + (gF cx fp + GO_RAW) / 8) with (gSH cx fp + Z.of_nat 70)
          by (rewrite HSHeq; unfold GO_RAW; cbn [Z.of_nat]; lia).
        rewrite K0, (HSH 70%nat ltac:(rewrite Hlen; unfold GE_NSH; lia)). vm_compute. reflexivity.
    - intros j Hj. cbn [length] in Hj. destruct j as [|[|j]]; [| |lia]; cbn [nth Z.of_nat].
      + rewrite Z.add_0_r. exact (val_mem1_of_aview SEGS _ _ _ _ B0c).
      + replace (gF cx fp + GO_RAW + Z.of_nat 1) with (gF cx fp + (GO_RAW + 1)) by lia.
        exact (val_mem1_of_aview SEGS _ _ _ _ B1c). }
  assert (HOBJ : obj_at SEGS (mrestrict (w_H W3) (ms_mem msc)) t ATx.LAY_TX (ATx.tx_vals (GrantSlotPlan.T_end (c_pl cx))))
    by exact (gtab_obj B cx ly3 S3 W3 msc t _ HTABc).
  assert (HIN : In (t, ATx.TX_SIZE) (ablocks B ly3 S3)) by exact Hint.
  pose proof (fun HPRE => BSW ly3 S3 W3 (ms_regs msc) (ms_mem msc) mdc (gch cx) 0 1 (gF cx fp + GO_RAW) t
    (raw_b cx) (raw_w cx) (GrantSlotPlan.T_end (c_pl cx)) HPRE HF7 HTOP (garo B MT cx fp k ly3 S3 W3 (ms_mem msc) mdc HB HJ)
    C10' C11' C12' C13' ltac:(lia) ltac:(lia) ltac:(unfold GO_RAW; lia) HAL HIN HTl HOBJ
    (BuildSweepLink.I1_set01 _ HI1) (BuildSweepLink.I1_legal _ HI1)
    ltac:(intros Hc; rewrite Hok in Hc; discriminate Hc)) as HCALL.
  refine (gcall B MT LAWS STK_reac_grant_build_sweep [] _ _ 0xee0 POST cx fp k ly3 S3 W3 (ms_regs msc) (ms_mem msc) mdc HB HJ
    C2' C8' C3' C4' C1' ltac:(lia) eq_refl H8c H16c'
    ltac:(unfold STK_reac_grant_build_sweep, ESTACK; lia)
    (fun a Ha => False_ind _ (inFP_nil a Ha))
    HCALL _).
  (* ---- the return, 0x8191c ---- *)
  intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP2 HQ.
  destruct HQ as (QF & QA & (f & QS) & Q10 & _).
  assert (Q10' : getr regs2 10 = w64 (-1)) by (rewrite Q10, Hok; reflexivity).
  assert (KC : forall a, rm_at cx fp t a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem msc) a).
  { apply (call_keep B MT cx fp t ly3 S3 W3 (ms_mem msc) mdc STK_reac_grant_build_sweep [] ly2 S2 W2 mem2 md2 0 HB HFR EFA HSHeq);
      [lia | exact Hbl0 | exact Hint | exact QA | exact inFP_nil | exact HJc]. }
  assert (P18 : getr regs2 18%bv = getr (ms_regs msc) 18%bv) by (apply (HP2 18); unfold acallee_saved; lia).
  assert (P2 : getr regs2 2%bv = getr (ms_regs msc) 2%bv) by (apply (HP2 2); unfold acallee_saved; lia).
  assert (P3 : getr regs2 3%bv = getr (ms_regs msc) 3%bv) by (apply (HP2 3); unfold acallee_saved; lia).
  assert (P4 : getr regs2 4%bv = getr (ms_regs msc) 4%bv) by (apply (HP2 4); unfold acallee_saved; lia).
  assert (P8 : getr regs2 8%bv = getr (ms_regs msc) 8%bv) by (apply (HP2 8); unfold acallee_saved; lia).
  assert (P9 : getr regs2 9%bv = getr (ms_regs msc) 9%bv) by (apply (HP2 9); unfold acallee_saved; lia).
  assert (P19 : getr regs2 19%bv = getr (ms_regs msc) 19%bv) by (apply (HP2 19); unfold acallee_saved; lia).
  assert (P20 : getr regs2 20%bv = getr (ms_regs msc) 20%bv) by (apply (HP2 20); unfold acallee_saved; lia).
  assert (P21 : getr regs2 21%bv = getr (ms_regs msc) 21%bv) by (apply (HP2 21); unfold acallee_saved; lia).
  assert (P22 : getr regs2 22%bv = getr (ms_regs msc) 22%bv) by (apply (HP2 22); unfold acallee_saved; lia).
  assert (P23 : getr regs2 23%bv = getr (ms_regs msc) 23%bv) by (apply (HP2 23); unfold acallee_saved; lia).
  remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
    by (intros nn r Hnn; subst E2; apply ew_Eimg_Ereg_nat; exact Hnn).
  assert (HS2 : st_ok_pi SEGS VAL E2 ss_ret (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0xee0)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_ret. apply pa_entry_st_ok_full.
    - rewrite HE2. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK2 : sh_ok SEGS GBx [] E2 (mrestrict (w_H W2) mem2)) by constructor.
  (* 0x8191c .. 0x81924: a3 := t, s4 := -1, `bne a0,s4` with a0 = -1 *)
  paj_run_tok RUN HS2 HJ2 SHOK2 GBspan; [apply awr_ok_nil |].
  psrr_branch_tok RUN BR HS2 SHOK2 GBspan.
  { exfalso. prreg_norm Hc. rewrite (EE2 10%nat (10%bv : bv 5) eq_refl), Q10' in Hc.
    vm_compute in Hc. discriminate Hc. }
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 GBspan GR_bs3; [apply awr_ok_nil |].
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
  assert (K2 : forall a, aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem2 a).
  { intros a. match goal with H1 : frame_of _ _ mem2 (ms_mem ?m1), H2 : frame_of _ _ (ms_mem ?m1) (ms_mem msF) |- _ =>
      rewrite (frame_nil_eq _ _ _ _ _ eq_refl H2 a), (frame_nil_eq _ _ _ _ _ eq_refl H1 a); reflexivity end. }
  destruct (gst_ok_mach _ _ _ _ HS2 eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
  bs_reg HS2 EE2 (2%bv : bv 5) 2%nat F2. bs_reg HS2 EE2 (3%bv : bv 5) 3%nat F3.
  bs_reg HS2 EE2 (4%bv : bv 5) 4%nat F4. bs_reg HS2 EE2 (8%bv : bv 5) 8%nat F8.
  bs_reg HS2 EE2 (9%bv : bv 5) 9%nat F9. bs_reg HS2 EE2 (18%bv : bv 5) 18%nat F18.
  bs_reg HS2 EE2 (19%bv : bv 5) 19%nat F19. bs_reg HS2 EE2 (21%bv : bv 5) 21%nat F21.
  bs_reg HS2 EE2 (22%bv : bv 5) 22%nat F22. bs_reg HS2 EE2 (23%bv : bv 5) 23%nat F23.
  prreg HS2 (10%bv : bv 5) F10. rewrite (EE2 18%nat (18%bv : bv 5) eq_refl) in F10.
  prreg HS2 (13%bv : bv 5) F13. rewrite (EE2 20%nat (20%bv : bv 5) eq_refl) in F13.
  prreg HS2 (20%bv : bv 5) F20. prreg HS2 (11%bv : bv 5) F11. prreg HS2 (12%bv : bv 5) F12.
  rewrite P2, C2 in F2. rewrite P3, C3 in F3. rewrite P4, C4 in F4. rewrite P8, C8 in F8. rewrite P9, C9 in F9.
  rewrite P18, C18 in F18. rewrite P19, C19 in F19. rewrite P21, C21 in F21. rewrite P22, C22 in F22.
  rewrite P23, C23 in F23. rewrite P18, C18 in F10. rewrite P20, C20 in F13.
  assert (KF : forall a, rm_at cx fp t a -> aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; rewrite K2, (KC a Ha); apply K0).
  assert (RCF : rcore cx fp GR_bs3 t W2 msF)
    by exact (rm_rcore cx fp GR_bs2 GR_bs3 t W3 ms3 W2 msF HRC Hhi ltac:(lia) KF Pc Prv Psv Pro Pfr Pfc
                F2 F3 F4 F8 F9 F19 F21 F22 F23).
  assert (GTF : gtab B cx ly2 S2 W2 msF t (GrantSlotPlan.T_end (c_pl cx))).
  { apply (rm_gtab B cx ly3 S3 ly2 S2 W3 ms3 W2 msF t _ Htab); [rewrite QA; exact Hint|].
    intros a Ha. apply KF. right; right; right; right. exact Ha. }
  apply (HN cx fp k acc ly2 S2 W2 msF _ HB HJ2 (eq_trans QF HFR)).
  { rewrite QS. exact (mo_le_set_fs_r MT MTF _ _ f acc HMO). }
  exists t, s.
  split; [exact RCF|].
  split; [exact Hk|]. split; [exact Hacc|].
  split; [unfold gblk2 in *; rewrite QA; exact Hbl|].
  split; [exact GTF|].
  split; [exact Hs4|]. split; [rewrite F18; exact R18|].
  split; [rewrite F20; apply bv_eq; vm_compute; reflexivity|].
  split; [rewrite F10; exact R18|].
  split; [rewrite F11; reflexivity|].
  split; [rewrite F12; reflexivity|].
  rewrite F13; exact R20.
Qed.

End c.
End b.
End a.
