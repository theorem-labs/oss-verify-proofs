From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger PjStruct PjIn ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PvDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import PvMain0 PvPaths.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import
  memcpy_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import
  parse_value_c parse_items_c parse_string_c fuzz_malloc_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PvDisp literal_c strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require PvItems PvLit PvStr PvNumB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Exec := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Exec.

Lemma disp_shape : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo ms,
  pv_disp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo ms ->
  exists R pc' m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d tb v lo ms H.
  destruct H as (P & m' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
    _ & _ & _ & _ & H).
  destruct H as [(_ & _ & _ & _ & ->)|[(o & y & _ & _ & _ & _ & ->)|[(b0 & y & wa & ty & _ & _ & _ & _ & _ & ->)|
    [(y & _ & _ & _ & _ & _ & _ & _ & ->)|(b0 & y & txt & r & _ & _ & _ & _ & _ & _ & _ & ->)]]]];
    do 3 eexists; reflexivity.
Qed.

Section V.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

Theorem parse_value_step : forall d,
  AllocExtra B (aa_MR API) -> ctx_owned B API -> errno_unowned B API ->
  parse_items_contract B API RF d -> parse_string_contract B API RF -> literal_c.literal_contract ->
  fuzz_malloc_contract B API RF -> memcpy_contract -> strtod_c.strtod_contract ->
  parse_value_contract B API RF d.
Proof.
  intros d AX CO ERR PI PS LIT FM MC SC. unfold parse_value_contract.
  intros L A regs mem md Lam peak cnt fail b q text len p tb v ENV LED RES Q10 V11 PJ0 Hq QA MX TX V0 VZ VP D1 D2 CN RR.
  assert (PRE0 : pv_pre B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v)
    by exact (conj ENV (conj LED (conj RES (conj Q10 (conj V11 (conj PJ0 (conj Hq (conj QA (conj MX (conj TX
      (conj V0 (conj VZ (conj VP (conj D1 (conj D2 (conj CN RR)))))))))))))))).
  pose proof ENV as (SEG & TP & EA & GG & GD & PRE & H47 & GT & FRM & RC).
  pose proof (pj_in_ok_bounds segs _ _ _ _ _ _ _ PJ0) as (_ & _ & _ & _ & _ & _ & _ & _ & Bd).
  assert (Hd : (d <= MAXD)%nat) by (unfold MAXD; lia).
  pose proof PRE as (HM & HWF & HB & HRA & Hal16 & Hlo & Hhi & HWs & Htp & Her & Haux).
  pose proof (pvk_bounds d Hd) as (K1 & K2 & K3).
  pose proof ceil_big as Cb.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (ST0 : Frame.stk rsegs mem (spZ regs - PARSE_VALUE_K d) (spZ regs)).
  { rewrite <- SEG. exact (kb_stk B API (pv_img_low B SEG) (PARSE_VALUE_K d) L A regs mem md PRE ltac:(lia)). }
  set (lo := spZ regs - PARSE_VALUE_K d).
  apply (kb_run B regs (Z_to_bv 64 PARSE_VALUE) mem md
    (fun R pc' mem' => pv_disp_post (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8)
       (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
       (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr mem q text len p (Z.of_nat d) tb v lo
       (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh Hl).
  { rewrite SEG. unfold rmk. eapply Exec.evt_mono.
    { eapply PvDisp.pv_disp with (q := q) (text := text) (len := len) (p := p) (d := Z.of_nat d) (tb := tb) (v := v) (lo := lo).
      - exact Q10.
      - exact V11.
      - rewrite <- SEG. exact PJ0.
      - rewrite <- SEG. exact VZ.
      - exact ST0.
      - change (bv_unsigned (getr regs 2)) with (spZ regs). unfold lo. lia.
      - change (bv_unsigned (getr regs 2)) with (spZ regs).
        apply (disjoint_from_sub _ (spZ regs - PARSE_VALUE_K d) (PARSE_VALUE_K d)); [exact D2 | lia | lia].
      - exact D1. }
    intros ms Hpost. destruct (disp_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as (R & pc' & m' & ->).
    exists R, pc', m'. split; [reflexivity | exact Hpost]. }
  intros R pc' mem' regs' HK Hg.
  destruct HK as (P & m'' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
    HP & HR & PJ & WM & HK).
  assert (RPx : forall R0, (forall r, getr regs' r = getr R0 r) ->
    (forall k, k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ 18 <= k <= 27 -> getr R0 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)) ->
    regs_preserved regs regs').
  { intros R0 HR0 HK0 k Hk. rewrite HR0. apply HK0. unfold callee_saved in Hk. lia. }
  destruct HK as [(Hc & MU & ST & PZ & EQ)|[(o & y & HO & MU & ST & PZ & EQ)|[(b0 & y & wa & ty & HO & LS & MU & ST & PZ & EQ)|
    [(y & HO & MU & ST & FR & PRW & B4 & BZ & EQ)|(b0 & y & txt & r & HO & OB & NT & MU & ST & FR & PZ & EQ)]]]];
    destruct (PvNumB.MS_inj _ _ _ _ _ _ _ _ _ _ _ _ EQ) as (ER & _ & EP & _ & EM); subst R pc' mem'.
  - apply (pv_path_ret B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m'' regs' HP HR PJ WM Hc MU PZ).
    + apply (RPx _ Hg). intros k Hk.
      assert (Hk' : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/
        k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
      destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
        reflexivity.
    + rewrite Hg. reflexivity.
  - apply (PvItems.pv_items_ok B API RF d PI L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m'' regs' o y
      HP HR PJ WM HO MU ST PZ).
    + rewrite Hg. reflexivity.
    + apply (RPx _ Hg). intros k Hk.
      assert (Hk' : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/
        k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
      destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
        reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
  - apply (PvLit.pv_lit_ok B API RF d LIT L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m'' regs' b0 y wa ty
      HP HR PJ WM HO LS MU ST PZ).
    + rewrite Hg. reflexivity.
    + apply (RPx _ Hg). intros k Hk.
      assert (Hk' : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/
        k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
      destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
        reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
  - apply (PvStr.pv_str_ok B API RF d PS L A regs mem md Lam peak cnt fail b q text len p tb v PRE0 P m'' regs' y
      HP HR PJ WM HO MU ST FR PRW B4 BZ).
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + intros k Hk. rewrite Hg.
      assert (Hk' : k = 3 \/ k = 4 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/
        k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
      destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]; reflexivity.
  - apply (PvNumB.pv_num_ok B API RF d AX CO ERR FM MC SC L A regs mem md Lam peak cnt fail b q text len p tb v PRE0
      P m'' regs' b0 y txt r HP HR PJ WM HO OB NT MU ST FR PZ).
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + rewrite Hg. reflexivity.
    + intros k Hk. rewrite Hg.
      assert (Hk' : k = 3 \/ k = 4 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
      destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; reflexivity.
Qed.

End V.
