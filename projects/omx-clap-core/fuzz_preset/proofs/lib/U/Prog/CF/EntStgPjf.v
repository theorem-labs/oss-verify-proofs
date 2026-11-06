From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import WriterRet pj_parse_c check_no_overread_c check_reject_clean_starved_c check_round_trip_c pj_free_c EntryDefs EntrySR EntBase EntGlue EntStg EntSQ_Cnt EntSQ_Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The pj_free stage of the #102 ubsan entry (pj_free 0x16340 called at 0x137e0, ra 0x137e4; doc at sp) and the
   epilogue (EntGlue.ent_fin at 0x137e4). *)

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis PJF : forall fx' : YK11.FPState, @pj_free_contract fx' rc B API F.
Hypothesis HWL1 : esq_wl1.
Hypothesis HWL2 : esq_wl2.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Theorem stg_pjf_holds : stg_pjf_st (fx := fx) B API F.
Proof.
  unfold stg_pjf_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md Lam peak E1 E2 E3 t D cset b4
    trs Ds ENT INV R1 RK R10 HEMP HEMP2 ROOMS HN CNOW JR TREE HCS CFIN CPL.
  set (cnt := ent_c4 cnt0 pl t cset + crcs_growth (zb pl) (ent_took pl) 1 t) in INV.
  set (bnd := ent_b5 F b4 (ent_c4 cnt0 pl t cset) pl t trs Ds) in INV.
  pose proof RK as (G2 & G3 & G4 & _).
  pose proof ENT as ((PRE & _) & SYMS & _ & _ & SLK & _ & _ & _ & LED0 & CNT0 & HJ & _).
  pose proof PRE as (MR0 & _ & _ & _ & _ & SP16 & SPC & SP63 & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & _).
  pose proof RS as (MRc & _ & _ & _ & PSc & _).
  destruct TREE as (PL & NODE & TDL & NEW).
  pose proof alloc_ceiling_val as HCV. pose proof alloc_ceiling_lt as HCL.
  assert (HK : SLOT_K = 14704) by reflexivity.
  pose proof (ent_errno B SYMS) as ERRB.
  assert (SPr : spZ regs = spZ regs0 - 112) by (apply (esq_sp regs0 regs G2); lia).
  pose proof (json_read_depth jr_strtod (zb pl) t JR) as DEP. unfold MAXD in DEP.
  assert (HPK : 0 <= PJ_FREE_K (depth t) /\ 112 + PJ_FREE_K (depth t) <= 14704).
  { unfold PJ_FREE_K, PJ_FREE_F, FREE_K, ALLOC_STACK. lia. }
  assert (RET : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  pose proof (ent_env_mid B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md
    Lam peak cnt bnd regs (PJ_FREE_K (depth t)) ENT INV SPr G4 RET ltac:(lia) ltac:(lia)) as REN.
  pose proof (pj_node_fd (ms_segs B) t mem (lin Lam) (spZ regs0 - 112) D NODE) as HFD.
  assert (RPL : rplace B L A Lam regs mem (spZ regs0 - 112)).
  { split; [left; rewrite SPr; lia|].
    split; [intros _ Hf; rewrite INIT in Hf; discriminate|].
    intros i Hi. split; [|split; [|split]].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ MRc Ho). lia.
    - intros Hs. pose proof (ent_statics_lo _ Hs). lia.
    - rewrite ERRB. unfold U.Prog.strtod_c.STRTOD_ERRNO. lia.
    - intros Hi'. pose proof (proj1 (ent_img_low B HSEG) _ Hi'). lia. }
  eapply SR_bind.
  { apply (PJF fx1 L A regs mem md Lam peak cnt (2 ^ 64 - 1) bnd (spZ regs0 - 112) (depth t) D REN LED RES R10).
    right. split; [lia|]. split; [exact HFD|]. split; [exact RPL|].
    rewrite SPr. cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  intros c' (L' & A' & regs2 & mem2 & md2 & Lam' & -> & RP2 & RD2 & PERMF & LED2 & (Df & PDf & RES2) & _ & HZR).
  rewrite R1.
  assert (EL : Lam' = []).
  { assert (P1 : Permutation (D ++ Lam') (D ++ []))
      by (rewrite app_nil_r; exact (Permutation_trans (Permutation_sym PERMF) PL)).
    apply Permutation_app_inv_l in P1. apply Permutation_nil. exact (Permutation_sym P1). }
  subst Lam'.
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & RR2 & _).
  pose proof (rstep_of_rpost B API HSEG AX FG (PJ_FREE_K (depth t)) L A regs mem md
    (pj_free_writes (spZ regs0 - 112) D) (freed D) L' A' regs2 mem2 md2 RP2) as STEP.
  rewrite SPr in STEP.
  destruct (HZR ltac:(lia)) as ((_ & ZSTK) & _).
  assert (DL : forall a k, In (a, k) D -> In (a, k) Lam)
    by (intros a k H; exact (Permutation_in _ (Permutation_sym PL) H)).
  assert (INV2 : ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L' A' mem2 md2 [] peak cnt (rf_frees F bnd Df)).
  { apply (ent_after B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak
      cnt bnd (PJ_FREE_K (depth t)) (pj_free_writes (spZ regs0 - 112) D) (fun a => exists n0, freed D a n0)
      fx1 L' A' mem2 md2 [] peak cnt (rf_frees F bnd Df) ENT INV STEP); try lia.
    - intros a (_ & [Ha|[Ha|Ha]]).
      + right. left. lia.
      + right. right. destruct Ha as (a' & k' & Hin' & Hr).
        destruct (esq_lblk B API L A mem md Lam peak cnt (2 ^ 64 - 1) a' k' MRc LED (DL _ _ Hin'))
          as (Hk' & Hb' & H1' & H2' & NI').
        split; [lia|]. split.
        * intros Hi. apply (NI' (a - a') ltac:(lia)). replace (a' + (a - a')) with a by lia. exact Hi.
        * intros b k Hb Hg. destruct (Z.eq_dec b (a' - 16)) as [->|Hne].
          -- exfalso. apply Hg. exists (k' + 16). unfold freed.
             replace (a' - 16 + 16) with a' by lia. replace (k' + 16 - 16) with k' by lia. exact Hin'.
          -- exact (blocks_apart B API HSEG AX FG L A mem md (a' - 16) (k' + 16) b k a MRc Hb' Hb
               (fun E => Hne (eq_sym E)) ltac:(lia)).
      + left. left. exact Ha.
    - intros a Ha (_ & [Hw|[(a' & k' & Hin' & Hr)|Hs]]).
      + destruct ZSTK as (_ & _ & ZS). exact (proj1 (ZS a ltac:(lia))).
      + destruct (esq_lblk B API L A mem md Lam peak cnt (2 ^ 64 - 1) a' k' MRc LED (DL _ _ Hin'))
          as (_ & _ & _ & H2' & _).
        lia.
      + pose proof (ent_statics_lo _ Hs). lia.
    - intros a k Hin Hk (n0 & Hn0). unfold freed in Hn0.
      pose proof (PSc a k Hin Hk (fun h => h)) as HinL.
      destruct (esq_lblk B API L A mem md Lam peak cnt (2 ^ 64 - 1) (a + 16) (n0 - 16) MRc LED (DL _ _ Hn0))
        as (Hn1 & Hbn & _).
      replace (a + 16 - 16) with a in Hbn by lia. replace (n0 - 16 + 16) with n0 in Hbn by lia.
      pose proof (blocks_same_addr B API HSEG AX FG L A mem md a k n0 MRc HinL Hbn Hk ltac:(lia)) as Ek. subst n0.
      apply (NEW (a + 16) (k - 16) Hn0). replace (a + 16 - 16) with a by lia. replace (k - 16 + 16) with k by lia.
      exact Hin.
    - intros a k Hin Hk. apply (esq_rpost_blocks B API HSEG FA _ _ _ _ _ _ _ _ _ _ _ _ _ RP2 a k Hin).
      intros Hf. unfold freed in Hf.
      destruct (esq_lblk B API L A mem md Lam peak cnt (2 ^ 64 - 1) (a + 16) (k - 16) MRc LED (DL _ _ Hf))
        as (Hk0 & _).
      lia.
    - exact (proj1 RD2).
    - exact FRM.
    - exact LED2.
    - exact RES2. }
  assert (CNTB : cnt <= Z.of_nat (S j) * 2 ^ 60).
  { pose proof LED0 as (_ & _ & HC0 & _).
    destruct (esq_cnt HWL1 HWL2 cnt0 pl t cset j ltac:(lia) HJ JR HN HCS) as (_ & H). exact H. }
  pose proof (esq_rk regs0 regs regs2 RR2 RK) as (G2' & G3' & G4' & G22' & G23' & G24' & G25' & G26' & G27').
  eapply SR_mono; [exact (ent_fin B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L' A'
    regs2 mem2 md2 peak cnt (rf_frees F bnd Df) ENT INV2 CNTB G2' G3' G4' G22' G23' G24' G25' G26' G27')|].
  intros c' Hc.
  apply (ent_sr_of_cpost B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0 E1 E2 E3 [] cset b4 trs Ds Df c').
  - intros _. destruct CNOW as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    rewrite JR. split; [exact CFIN|]. split; [exact CPL|]. exists D. split; [exact PDf | exact TDL].
  - unfold entry_fold. rewrite (proj2 (Z.ltb_ge _ _) HN). rewrite JR. exact Hc.
Qed.

End S.
