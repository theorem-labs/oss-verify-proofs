From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterSpecFacts WriterValue WriterApp WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import put_c put_kb write_value_c pj_write_c PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pjwa_bytes : forall segs t m lblk p D, pj_node segs m lblk p t D -> jv_bytes_ok t.
Proof.
  intros segs t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
    intros m lblk p D H; cbn [pj_node] in H; cbn [jv_bytes_ok]; try exact I.
  - destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & _ & k & (_ & _ & HF & _) & _).
    destruct (chars_ok txt HF) as [Hz Hb]. split; assumption.
  - destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & k & (_ & _ & HF & _) & _).
    destruct (chars_ok s HF) as [Hz Hb]. split; assumption.
  - destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & _ & Di & _ & HI).
    clear - IH HI. revert kids Di HI.
    induction IH as [|x r Hx Hr IHr]; intros a Di HI; [exact I|].
    cbn [pj_items] in HI. destruct HI as (D1 & D2 & _ & H1 & H2).
    split; [exact (Hx _ _ _ _ H1) | exact (IHr _ _ H2)].
  - destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & Di & _ & HI).
    clear - IH HI. revert kids keys Di HI.
    induction IH as [|[nm u] r Hx Hr IHr]; intros a ka Di HI; [exact I|].
    cbn [pj_mems] in HI. destruct HI as (x & k & D1 & D2 & _ & _ & (_ & _ & HF & _) & H1 & H2).
    destruct (chars_ok nm HF) as [Hz Hb].
    split; [exact Hb|]. split; [exact Hz|]. split; [exact (Hx _ _ _ _ H1) | exact (IHr _ _ _ H2)].
Qed.

Lemma pjwa_ok : forall P cnt fail, 0 <= cnt ->
  cnt + Z.of_nat (length (grow_calls 0 0 (piece_lens P))) < 2 ^ 64 ->
  fail < cnt \/ cnt + Z.of_nat (length (grow_calls 0 0 (piece_lens P))) <= fail ->
  putN (w0 cnt fail) P =
  mkW 0 (concat P) (grow_cap 0 0 (piece_lens P)) (cnt + Z.of_nat (length (grow_calls 0 0 (piece_lens P)))) fail
    (grow_calls 0 0 (piece_lens P)).
Proof.
  intros P cnt fail H0 H1 H2. exact (putN_ok P (w0 cnt fail) eq_refl H0 H1 H2).
Qed.

Lemma pjwa_starve : forall P cnt fail, 0 <= cnt ->
  cnt <= fail < cnt + Z.of_nat (length (grow_calls 0 0 (piece_lens P))) ->
  cnt + Z.of_nat (length (grow_calls 0 0 (piece_lens P))) < 2 ^ 64 ->
  w_failed (putN (w0 cnt fail) P) = 1 /\ w_cnt (putN (w0 cnt fail) P) = fail + 1 /\
  w_fail (putN (w0 cnt fail) P) = 2 ^ 64 - 1.
Proof.
  intros P cnt fail H0 H1 H2.
  destruct (putN_starved P cnt fail (Z.to_nat (fail - cnt)) H0 ltac:(lia) ltac:(lia) ltac:(lia))
    as (E1 & E2 & E3 & _).
  split; [exact E1|]. split; [rewrite E2; lia | exact E3].
Qed.

Section A.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis AX : AllocExtra B (aa_MR API).

Lemma pj_write_adapt : (forall fx' : YK11.FPState, @pj_write_contract fx' rc B API F) ->
  @pj_write_hyp fx rc B API F PJW_K.
Proof.
  intros PJC. unfold pj_write_hyp.
  intros L A regs mem md v pretty t D Lam peak cnt fail b. cbv zeta.
  intros REN INIT LG RFOK R10 R11 HPR PN DIN WH WL DEP RM CW.
  pose proof REN as (SEG & TP & ERR & GG & GD & PRE & SPT & GT & FRM & RDC).
  pose proof RDC as (RO & _ & _).
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  pose proof LG as (_ & _ & Hc & Hf & _).
  assert (CK : 0 <= cnt) by lia.
  assert (KP : 48 <= PJW_K t) by (unfold PJW_K, PJW_FR, ALLOC_STACK; lia).
  assert (DEPZ : Z.of_nat (depth t) <= 2 ^ 31 - 1).
  { assert (E : Z.of_nat (2 ^ 31)%nat = 2 ^ 31) by (rewrite Nat2Z.inj_pow; reflexivity). lia. }
  assert (BYT : Forall (fun c => 0 < c < 256) (wdoc t (negb (pretty =? 0)))).
  { destruct (wdoc_no_zero t (negb (pretty =? 0)) (pjwa_bytes _ _ _ _ _ _ PN)) as [Z1 B1].
    exact (str_chr _ B1 Z1). }
  assert (TS : spZ regs <= TASK_SIZE) by (assert (T : TASK_SIZE = 2 ^ 47) by reflexivity; lia).
  assert (OFFK : off_errno B (spZ regs - PJW_K t) (PJW_K t)).
  { unfold off_errno. right. rewrite ERR. unfold strtod_c.STRTOD_ERRNO, strtod_c.STRTOD_GLOBALS_TOP in *. lia. }
  assert (PW : pjw_where B regs Lam v).
  { destruct WH as [W|(a & k & W)]; [left; split; [exact W|] | right; exists a, k; exact W].
    unfold off_errno. right. rewrite ERR. unfold strtod_c.STRTOD_ERRNO, strtod_c.STRTOD_GLOBALS_TOP in *. lia. }
  assert (SRC : SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PJ_WRITE_PC) mem (seg_rom (ms_segs B))) md)
      (@pj_write_ret fx rc B API F (PJW_K t) L A regs mem md v t D (negb (pretty =? 0)) Lam peak cnt fail b)).
  { refine (PJC fx L A regs mem md b v pretty t D Lam peak cnt fail SEG _ _ _ INIT RO FRM R10 R11 HPR LG OFFK _ PW _
      DEPZ _ RFOK RM).
    - rewrite GG. reflexivity.
    - rewrite GD. reflexivity.
    - split; assumption.
    - rewrite <- SEG. exact PN.
    - intros a k H. exact (DIN _ H).
    - exact WL. }
  change PJ_WRITE with PJ_WRITE_PC.
  eapply SR_mono; [exact SRC|].
  intros c' RET. unfold pj_write_ret in RET. cbv zeta in RET.
  set (st' := putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))) in RET.
  destruct RET as (fx' & L' & A' & regs' & mem' & md' & Lam' & peak' & b' & EC & FRG & FRM' & RP & HM' & HWF' & HB'
    & RO' & GK & LG' & RF' & LLE & LEN' & INI' & VM & UB & KP0 & PN' & FR1 & FR2 & ARMS).
  assert (FK : fregs_kept fx fx').
  { intros r Hr. apply FRG. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). lia. }
  assert (RPO : rpost B API (PJW_K t) L A regs mem md alloc_statics (fun _ _ => False) L' A' regs' mem' md').
  { unfold rpost.
    split; [exact HM'|]. split; [exact HWF'|]. split; [exact HB'|]. split; [exact LLE|]. split; [exact INI'|].
    split; [intros H0; rewrite (INI' INIT) in H0; discriminate|].
    split; [exact LEN'|].
    split; [intros q0 n Hq _; exact (proj1 (UB q0 n Hq))|].
    split; [intros q0 n Hq _; exact (proj2 (UB q0 n Hq))|].
    split; [exact RP|]. split; [exact VM|].
    split.
    { intros a Ha Hs He. apply FR1; [left; exact Ha | | | | | exact He].
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho). lia.
      - intros Hk. apply Hs. left. exact Hk.
      - intros Hk. apply Hs. right. exact Hk. }
    split.
    { intros a Ha Hno Hs He. apply FR1; [right; exact Ha | exact (Hno _ _ _ _ HM) | exact (Hno _ _ _ _ HM')
        | intros Hk; apply Hs; left; exact Hk | intros Hk; apply Hs; right; exact Hk | exact He]. }
    split.
    { intros q0 n i Hq Hq' Hi He.
      destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ _ _ HM Hq) as [Hlo _].
      apply (KP0 (ptr_addr L q0) n i); [|lia | exact Hi].
      unfold blocks. apply in_map_iff. exists (q0, n). split; [reflexivity | exact Hq]. }
    intros a Hs. apply FR2; [exact Hs|]. destruct Hs as [Hs|Hs]; [apply HWs; exact Hs | apply HWe; exact Hs]. }
  assert (RDC' : rd_cells B mem').
  { destruct (ax_statics AX _ _ _ _ HM') as (G1 & (g & _ & G2) & _).
    split; [exact RO'|]. split; [exact G1 | exists g; exact G2]. }
  assert (PK0 : peak <= peak').
  { destruct ARMS as [(_ & q & _ & _ & _ & _ & EPk & _)|(_ & _ & _ & [(_ & EPk & _)|(_ & EPk & _)])]; lia. }
  assert (NODE : forall Lx, (forall a k, In (a, k) Lam -> In (a, k) Lx) -> pj_node (ms_segs B) mem' (lin Lx) v t D).
  { intros Lx HX. rewrite SEG. apply (pj_node_frame rsegs t mem' (wv_lblk Lam) mem' (lin Lx) v D PN').
    - intros a k H. unfold lin. apply HX. exact (DIN _ H).
    - intros x _. reflexivity. }
  assert (STA : fail < cnt \/ cnt + wcalls t (negb (pretty =? 0)) <= fail ->
    st' = mkW 0 (wdoc t (negb (pretty =? 0))) (wcap t (negb (pretty =? 0))) (cnt + wcalls t (negb (pretty =? 0)))
      fail (grow_calls 0 0 (piece_lens (wdpieces t (negb (pretty =? 0)))))).
  { intros C. exact (pjwa_ok _ cnt fail CK CW C). }
  assert (STB : cnt <= fail < cnt + wcalls t (negb (pretty =? 0)) ->
    w_failed st' = 1 /\ w_cnt st' = fail + 1 /\ w_fail st' = 2 ^ 64 - 1).
  { intros C. exact (pjwa_starve _ cnt fail CK C CW). }
  destruct ARMS as [(WF0 & q & Q10 & Qnz & QNB & ELam & EPk & Eb & ZB)|(WF1 & Q10 & ELam & PKB)].
  - exists fx', L', A', regs', mem', md', Lam', peak', (w_cnt st'), (w_fail st'), q, b'.
    split; [exact EC|]. split; [exact FRM'|]. split; [exact FK|]. split; [exact RPO|]. split; [exact RDC'|].
    split; [exact LG'|]. split; [exact PK0|]. split; [exact RF'|]. split; [exact Q10|].
    split; [apply NODE; intros a k H; rewrite ELam; right; exact H|].
    split.
    + intros C. pose proof (STA C) as E. rewrite E in QNB, ELam. cbn [w_cap] in QNB, ELam.
      rewrite E. cbn [w_cnt w_fail].
      split; [exact Qnz|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Eb|].
      split; [rewrite ELam; apply Permutation_refl|].
      split; [intros a k [Ek|[]]; injection Ek as <- <-; exact QNB|].
      split; [exact BYT|].
      assert (HIN : In (q, wcap t (negb (pretty =? 0))) Lam') by (rewrite ELam; left; reflexivity).
      destruct (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM' LG' HIN) as (Hq1 & Hq2 & Hq3).
      pose proof LG' as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
      destruct (FB _ HIN) as (Hk & _). cbn [fst snd] in Hk.
      rewrite SEG. unfold zbytes_at in ZB. rewrite SEG in ZB.
      apply (proj1 (zbytes_core mem' q (wdoc t (negb (pretty =? 0)) ++ [0]) ltac:(lia)
        ltac:(rewrite length_app; cbn [length]; unfold wlen in WL; lia))).
      exact ZB.
    + intros C. destruct (STB C) as (E1 & _). lia.
  - exists fx', L', A', regs', mem', md', Lam', peak', (w_cnt st'), (w_fail st'), 0, b'.
    split; [exact EC|]. split; [exact FRM'|]. split; [exact FK|]. split; [exact RPO|]. split; [exact RDC'|].
    split; [exact LG'|]. split; [exact PK0|]. split; [exact RF'|]. split; [exact Q10|].
    split; [apply NODE; intros a k H; rewrite ELam; exact H|].
    split.
    + intros C. exfalso. apply WF1. rewrite (STA C). reflexivity.
    + intros C. destruct (STB C) as (_ & E2 & E3).
      split; [reflexivity|]. split; [exact E2|]. split; [exact E3|]. rewrite ELam. apply Permutation_refl.
Qed.

End A.
