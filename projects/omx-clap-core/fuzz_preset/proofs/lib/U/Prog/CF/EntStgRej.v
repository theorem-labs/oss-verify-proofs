From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c EntSegA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_reject_clean_starved_c EntryDefs EntrySR EntBase EntGlue EntStg EntStgCno.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The check_reject_clean_starved stage on the rc != 0 arm of the #102 ubsan entry (check_reject_clean_starved 0x13c3c
   called at 0x13834 with doc = NULL, ra 0x13838), then j 0x137e4 and the epilogue (EntSegA.ent_segC2): the entry
   returns 0 without pj_free, as before #102. CF/check_reject_clean_starved_c.v takes the two flag bytes 0. *)

Lemma ents1_growth0 : forall x took, 0 <= took -> 0 <= crcs_growth x took 0 JNull <= took.
Proof.
  intros x took Ht. unfold crcs_growth, pick.
  assert (E0 : (0 =? 0) = true) by reflexivity. rewrite E0.
  destruct (took =? 0) eqn:E; cbv beta iota; [lia|].
  apply Z.eqb_neq in E. pose proof (Z.mod_pos_bound (djb2 5381 x) took ltac:(lia)). lia.
Qed.

Section R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Variable KW : Z.
Hypothesis HKW : 0 <= KW /\ 112 + CRCS_K KW <= SLOT_K.
Hypothesis CRS : forall fx' : YK11.FPState, @check_reject_clean_starved_contract fx' rc B API F KW.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Theorem stg_crs0_holds : stg_crs0_st (fx := fx) B API F.
Proof.
  unfold stg_crs0_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md peak E1 E2 E3 D Dp
    ENT INV R1 RK R8 R9 R10 R11 R12 R13 FL HEMP HE0 ROOM HN CNOW HJR HPD HTD.
  destruct HKW as (HKW0 & HKW1).
  pose proof RK as (R2 & R3 & R4 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof FL as (FLR & FLO).
  pose proof ENT as (PREW & SYMS & SINKS & RAE & SLK & RO0 & TS & FRM0 & LED0 & CNT & HJ & RES0).
  pose proof PREW as (PRE & HNL & BLK & _).
  pose proof PRE as (MR0 & WF0 & BD0 & INIT0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & R10' & R11' & PAY & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & PAY0 & _).
  pose proof RS as (MRc & WFc & BDc & INc & KBc & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof alloc_ceiling_lt as HCL.
  pose proof (ent_errno B SYMS) as ERRB.
  pose proof (ent_ret_ok B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT) as RET0.
  assert (HK : SLOT_K = 14704) by reflexivity.
  assert (HCK0 : 0 <= CRCS_K KW) by (unfold CRCS_K, CRCS_F; lia).
  assert (HSP : spZ regs = spZ regs0 - 112) by (unfold spZ at 1; rewrite R2; apply ents1_uns; lia).
  assert (RET : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  pose proof (ent_env_mid B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    fx1 L A mem md [] peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 Dp) regs (CRCS_K KW) ENT INV HSP R4 RET HCK0
    ltac:(lia)) as REN.
  assert (PR : 0 < p /\ p + n < 2 ^ 62 /\ (0 < n -> In (p, n) (blocks L0 A0))).
  { destruct PAY as [(Hn0 & ->) | (Hn0 & q & Hq & Eq)].
    - split; [lia|]. split; [lia | intros; lia].
    - pose proof (rg_blk_of B API HSEG AX FG L0 A0 q n Hq) as Hb. rewrite Eq in Hb.
      destruct (rg_blk B API HSEG AX FG L0 A0 mem0 md0 p n 0 MR0 Hb ltac:(lia)) as (_ & H1 & H2 & _).
      split; [lia|]. split; [lia | intros; exact Hb]. }
  destruct PR as (HP0 & HP1 & HPB).
  assert (PB : EMem.bytes_at (ms_segs B) mem p pl).
  { split; [lia|]. split; [lia|]. intros i Hi.
    change (EMem.mrd (ms_segs B) mem (EMem.wa (p + Z.of_nat i))) with (mbyte (ms_segs B) mem (p + Z.of_nat i)).
    rewrite (PAY0 (Z.of_nat i)) by lia. rewrite (BLK (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity. }
  assert (HCN : Z.of_nat j <= 3) by lia.
  assert (HBA : 0 < n -> In (p, n) (blocks L A)) by (intros Hn0; apply KBc; [apply HPB, Hn0 | exact Hn0 | intros []]).
  assert (NIMG : forall i, 0 <= i < n -> ~ in_img B (p + i)).
  { intros i Hi Himg. destruct (rg_blk_in B API HSEG AX FG L A p n (HBA ltac:(lia))) as (q & Hq & Eq).
    apply (ax_blocks_img AX L A mem md q n i MRc Hq Hi). rewrite Eq. exact Himg. }
  assert (NC : (ncalls jr_strtod (zb pl) <= 2 * length (zb pl) + 2)%nat) by apply G7_4.
  assert (EL : length (zb pl) = length pl) by (unfold zb; apply length_map).
  assert (HNZ : n <= 0x300000) by (unfold ent_n in HN; lia).
  assert (HT : 0 <= ent_took pl <= 2 * n + 2) by (unfold ent_took; rewrite EL in NC; lia).
  destruct CNOW as (C1 & C2 & C3).
  destruct (ROOM HN) as (_ & RM).
  destruct (RM E1 E2 E3 C1 C2 C3) as (_ & RM2).
  assert (CRR : crs_rooms F (ent_b3 F b0 pl E1 E2 E3 Dp) (ent_c3 cnt0 pl) pl 0 JNull).
  { rewrite HJR in RM2. exact (proj2 (RM2 D Dp HPD HTD)). }
  destruct CRR as (CR1 & _ & _).
  eapply SR_bind.
  { apply (CRS fx1 L A regs mem md [] peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 Dp) p n (ent_took pl) 0 pl
      JNull [] REN R10 R11 R12 R13 HKW0 HNZ HP0 HP1 (eq_sym HNL) PB);
      [ | | reflexivity | left; reflexivity | exact LED | unfold ent_c3; lia | exact RES | exact CR1
      | intros _ H; exfalso; apply H; reflexivity | intros _ H; exfalso; apply H; reflexivity | exact FLR | exact FLO ].
    - intros Hn0. exists p, n. split; [exact (HBA Hn0)|]. split; [intros []|]. lia.
    - intros i Hi. destruct (rg_blk B API HSEG AX FG L A mem md p n i MRc (HBA ltac:(lia)) Hi) as (_ & _ & _ & HO).
      split; [exact HO|]. split.
      + intros Hs. apply (NIMG i Hi). exact (proj1 (statics_img B API HSEG AX FG _ Hs)).
      + intros He. apply (NIMG i Hi).
        pose proof (errno_img B API HSEG AX FG ERRB (p + i - errno_addr B) ltac:(lia)) as H.
        replace (errno_addr B + (p + i - errno_addr B)) with (p + i) in H by lia. exact H. }
  intros c' (fx' & L' & A' & regs' & mem' & md' & Lam' & peak' & -> & FRM' & RP & RD' & LED' & PERM & PK & _ & T0 & T1).
  rewrite R1.
  apply Permutation_sym, Permutation_nil in PERM. subst Lam'.
  pose proof RP as (MR' & WF' & BD' & _ & _ & _ & _ & UB' & PA' & RR' & _).
  pose proof (rstep_of_rpost B API HSEG AX FG (CRCS_K KW) L A regs mem md alloc_statics (fun _ _ => False)
    L' A' regs' mem' md' RP) as ST.
  rewrite HSP in ST.
  set (cnt2 := ent_c3 cnt0 pl + crcs_growth (zb pl) (ent_took pl) 0 JNull) in *.
  assert (HB : exists trs Ds, (ent_took pl <> 0 -> crs_parse_left (ent_c3 cnt0 pl) (zb pl) (ent_took pl) trs Ds) /\
                             rf_ok F A' (ent_brej F b0 pl E1 E2 E3 Dp trs Ds)).
  { destruct (Z.eq_dec (ent_took pl) 0) as [Ht|Ht].
    - exists [], []. split; [intros H; contradiction|]. unfold ent_brej. rewrite (proj2 (Z.eqb_eq _ _) Ht).
      exact (T0 Ht).
    - destruct (T1 Ht) as (tr & D' & PL & RB). exists tr, D'. split; [intros _; exact PL|].
      unfold ent_brej. rewrite (proj2 (Z.eqb_neq _ _) Ht). exact RB. }
  destruct HB as (trs & Ds & HPL & RESB).
  assert (INV1 : ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx' L' A' mem' md' [] peak' cnt2
                   (ent_brej F b0 pl E1 E2 E3 Dp trs Ds)).
  { apply (ent_after B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md [] peak
      (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 Dp) (CRCS_K KW) _ _ fx' L' A' mem' md' [] peak' cnt2
      (ent_brej F b0 pl E1 E2 E3 Dp trs Ds) ENT INV ST HCK0 ltac:(lia));
      [| | | | exact (proj1 RD') | exact FRM' | exact LED' | exact RESB].
    - intros a H. left. left. exact H.
    - intros a Ha H. pose proof (ent_statics_lo a H). lia.
    - intros a k _ _ (k' & []).
    - intros a k Hin _. destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
      assert (Hq1 : In (q0, k) (user_blocks A')) by (apply UB'; [exact Hq0 | intros []]).
      rewrite <- (PA' q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L' A' q0 k Hq1). }
  assert (GR : 0 <= crcs_growth (zb pl) (ent_took pl) 0 JNull <= ent_took pl) by (apply ents1_growth0; lia).
  assert (CNT2 : cnt2 <= Z.of_nat (S j) * 2 ^ 60) by (unfold cnt2, ent_c3; rewrite Nat2Z.inj_succ; lia).
  assert (EF : entry_fold F b0 cnt0 pl E1 E2 E3 Dp 0 b0 trs Ds [] = ent_brej F b0 pl E1 E2 E3 Dp trs Ds).
  { unfold entry_fold. rewrite (proj2 (Z.ltb_ge _ _) HN), HJR. reflexivity. }
  assert (EW : entry_wit F b0 cnt0 pl E1 E2 E3 Dp 0 b0 trs Ds []).
  { intros _. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    rewrite HJR. split; [exists D; split; [exact HPD | exact HTD] | exact HPL]. }
  pose proof INV1 as (RS1 & Z1 & INIT1 & RD1 & FRM1 & LED1 & RES1 & _ &
                      SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & _).
  pose proof RS1 as (MR1 & _).
  assert (G2 : getr regs' 2 = Z_to_bv 64 (spZ regs0 - 112))
    by (etransitivity; [apply (RR' 2); unfold callee_saved; lia | exact R2]).
  assert (G3 : getr regs' 3 = getr regs0 3) by (etransitivity; [apply (RR' 3); unfold callee_saved; lia | exact R3]).
  assert (G4 : getr regs' 4 = getr regs0 4) by (etransitivity; [apply (RR' 4); unfold callee_saved; lia | exact R4]).
  assert (G22 : getr regs' 22 = getr regs0 22)
    by (etransitivity; [apply (RR' 22); unfold callee_saved; lia | exact R22]).
  assert (G23 : getr regs' 23 = getr regs0 23)
    by (etransitivity; [apply (RR' 23); unfold callee_saved; lia | exact R23]).
  assert (G24 : getr regs' 24 = getr regs0 24)
    by (etransitivity; [apply (RR' 24); unfold callee_saved; lia | exact R24]).
  assert (G25 : getr regs' 25 = getr regs0 25)
    by (etransitivity; [apply (RR' 25); unfold callee_saved; lia | exact R25]).
  assert (G26 : getr regs' 26 = getr regs0 26)
    by (etransitivity; [apply (RR' 26); unfold callee_saved; lia | exact R26]).
  assert (G27 : getr regs' 27 = getr regs0 27)
    by (etransitivity; [apply (RR' 27); unfold callee_saved; lia | exact R27]).
  destruct (kb_md B API L' A' mem' md' MR1) as (Hh & Hz).
  eapply (ent_kA B HSEG fx' regs' _ mem' md' _ _ Hh Hz).
  { unfold rmk. rewrite G2.
    apply (ent_segC2 (getr regs' 1) (getr regs' 3) (getr regs' 4) (getr regs' 5) (getr regs' 6) (getr regs' 7)
      (getr regs' 8) (getr regs' 9) (getr regs' 10) (getr regs' 11) (getr regs' 12) (getr regs' 13) (getr regs' 14)
      (getr regs' 15) (getr regs' 16) (getr regs' 17) (getr regs' 18) (getr regs' 19) (getr regs' 20) (getr regs' 21)
      (getr regs' 22) (getr regs' 23) (getr regs' 24) (getr regs' 25) (getr regs' 26) (getr regs' 27) (getr regs' 28)
      (getr regs' 29) (getr regs' 30) (getr regs' 31) (@fp_regs fx') (@fp_csr fx') mem' (spZ regs0 - 112)
      (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20)
      (getr regs0 21)); [lia | lia | | | | | | |].
    - apply (ent_slot _ _ (spZ regs0 - 8)); [lia | rewrite <- HSEG; exact SL8].
    - apply (ent_slot _ _ (spZ regs0 - 16)); [lia | rewrite <- HSEG; exact SL16].
    - apply (ent_slot _ _ (spZ regs0 - 24)); [lia | rewrite <- HSEG; exact SL24].
    - apply (ent_slot _ _ (spZ regs0 - 32)); [lia | rewrite <- HSEG; exact SL32].
    - apply (ent_slot _ _ (spZ regs0 - 40)); [lia | rewrite <- HSEG; exact SL40].
    - apply (ent_slot _ _ (spZ regs0 - 48)); [lia | rewrite <- HSEG; exact SL48].
    - apply (ent_slot _ _ (spZ regs0 - 56)); [lia | rewrite <- HSEG; exact SL56]. }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  ent_inj HQ R pc' mem1.
  apply SR_ret. rewrite (kb_ret_pc _ RET0), RA0.
  apply (ent_sr_of_cpost B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0 E1 E2 E3 Dp 0 b0 trs Ds []); [exact EW|].
  rewrite EF.
  apply (ent_post_intro B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A' regs1 mem'
    md' peak' cnt2 (ent_brej F b0 pl E1 E2 E3 Dp trs Ds) ENT RS1 Z1 INIT1 (proj1 RD1) FRM1 LED1 CNT2 RES1).
  - intros r Hr. unfold callee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    rewrite HGr.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    + transitivity (Z_to_bv 64 (spZ regs0 - 112 + 112)); [reflexivity|].
      replace (spZ regs0 - 112 + 112) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
    + transitivity (getr regs' 3); [reflexivity | exact G3].
    + transitivity (getr regs' 4); [reflexivity | exact G4].
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + transitivity (getr regs' 22); [reflexivity | exact G22].
    + transitivity (getr regs' 23); [reflexivity | exact G23].
    + transitivity (getr regs' 24); [reflexivity | exact G24].
    + transitivity (getr regs' 25); [reflexivity | exact G25].
    + transitivity (getr regs' 26); [reflexivity | exact G26].
    + transitivity (getr regs' 27); [reflexivity | exact G27].
  - rewrite HGr. reflexivity.
Qed.

End R.
