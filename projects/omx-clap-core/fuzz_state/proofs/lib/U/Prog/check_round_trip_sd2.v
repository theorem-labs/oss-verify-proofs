(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1786 lines of code are new or changed and 723 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread.v, with its module paths, module names and numbers changed; 1318 of its 1476 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_round_trip_calls.v; 243 of its 433 lines of code are new or changed and 1286 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_round_trip_sd7.v, with its addresses and numbers changed; 308 of its 417 lines of code are new or changed and 324 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger LedgerFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import HStateRoom ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import check_round_trip_c check_round_trip_glue
  check_round_trip_runs check_round_trip_calls check_round_trip_stages_a check_round_trip_st8 check_round_trip_stdefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB check_reject_clean_starved past_nul.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c
  pj_get_c pj_get_str_c.


Lemma sd2_zs_bz : forall l, bytes_ok l -> map bv_unsigned (bz l) = l.
Proof.
  intros l H. unfold bz. rewrite map_map. transitivity (map (fun x : Z => x) l); [|apply map_id].
  apply map_ext_in. intros z Hz. cbv beta. unfold bytes_ok in H.
  pose proof (proj1 (Forall_forall _ _) H z Hz) as Hr. cbv beta in Hr.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma sd2_pad_le : forall x y p, x <= y -> p mod 16 = 0 -> y <= p -> x + (- x) mod 8 <= p.
Proof. intros x y p H1 H2 H3. Z.div_mod_to_equations. lia. Qed.

Lemma sd2_pad_lt : forall x, x + (- x) mod 8 < x + 8.
Proof. intros x. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)). lia. Qed.

Lemma sd2_ivl : forall lo hi x : Z, (lo <= x < hi) \/ ~ (lo <= x < hi).
Proof.
  intros lo hi x. destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); [left; lia | right; lia ..].
Qed.

Lemma sd2_stk_norm : forall m lo hi, ro_agree rsegs m -> stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> ro_addr rsegs (wa a) = false) -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RA (H0 & H1 & H) HRO. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W R].
  pose proof (mem_rel_normalize rsegs m RA) as HR.
  split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ HR (HRO a Ha)). exact W.
  - rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ HR). exact R.
Qed.

#[local] Set Default Proof Using "All".

Section ST.
Context {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis MAL : ms_malloc B = 0x16c7c.
Hypothesis FRE : ms_free B = 0x16b3c.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : lib.U.Reusable.YL01.AllocExtra B (aa_MR API).
Hypothesis CO : ctx_owned B API.
Hypothesis BSP : block_slack_present B API.
Hypothesis RTP : ms_tp B = U.Prog.strtod_c.STRTOD_TP.
Hypothesis RER : errno_addr B = U.Prog.strtod_c.STRTOD_ERRNO.
Hypothesis RGG : ms_got_guard B = U.Prog.strtod_c.STRTOD_GOT_GUARD.
Hypothesis RGD : ms_guard B = U.Prog.strtod_c.STRTOD_GUARD.
Hypothesis STRLEN : strlen_contract.
Hypothesis STRCMP : strcmp_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis PJO : pj_object_contract.
Hypothesis PJG : pj_get_contract.
Hypothesis PJGS : pj_get_str_contract.
Hypothesis MALLOC : forall fx' : lib.Reusable.YK11.FPState, malloc_contract (fx := fx') B API.
Hypothesis FREE : forall fx' : lib.Reusable.YK11.FPState, free_contract (fx := fx') B API.
Hypothesis FFREE : forall fx' : lib.Reusable.YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form.
Hypothesis ENC : forall fx' : lib.Reusable.YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form.
Hypothesis DEC : forall fx' : lib.Reusable.YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form.
Hypothesis PJS : forall fx' : lib.Reusable.YK11.FPState, pj_string_contract (fx := fx') B API sb_form.
Hypothesis PJSET : forall fx' : lib.Reusable.YK11.FPState, pj_set_contract (fx := fx') B API sb_form.
Hypothesis PJF : forall fx' : lib.Reusable.YK11.FPState, pj_free_contract (fx := fx') B API sb_form.
Hypothesis PJW : forall fx' : lib.Reusable.YK11.FPState, pj_write_contract_sb (fx := fx') B API.
Hypothesis PJP : forall fx' : lib.Reusable.YK11.FPState, pj_parse_contract (fx := fx') B API sb_form.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : call_pre_k B (aa_MR API) CRT_STK L A regs mem md.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound).
Hypothesis LG0 : ledger B L A mem Lam peak cnt (2 ^ 64 - 1).
Hypothesis HCNT : cnt + CRT_ALLOCS < 2 ^ 63.
Hypothesis RSP : spZ regs <= 2 ^ 47.
Hypothesis RGT : U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK.
Variable fx0 : lib.Reusable.YK11.FPState.

Local Notation CRs := (CR B API L A regs mem md Lam peak cnt bnd).
Local Notation post := (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
Local Notation PFX f := (f B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC
  FREE FFREE ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0) (only parsing).

Ltac retok R1 := rewrite R1; vm_compute; reflexivity.
Ltac kbr HM := first [ exact (proj1 (kb_md B API _ _ _ _ HM)) | exact (proj2 (kb_md B API _ _ _ _ HM)) ].
Ltac sv RP R' H E n :=
  lazymatch type of H with getr _ ?k = ?v =>
    assert (E : getr R' k = v) by (rewrite <- H; exact (RP n ltac:(unfold callee_saved; lia))) end.

Lemma sd2_frame_stk : forall Lc Ac memc mdc lo hi, GI B API L A regs mem md Lc Ac memc mdc ->
  spZ regs - CRT_STK <= lo -> lo <= hi -> hi <= spZ regs -> stk rsegs (normalize rsegs memc) lo hi.
Proof.
  intros Lc Ac memc mdc lo hi GIc H1 H2 H3.
  pose proof GIc as ((_ & _ & _ & _ & _ & _ & _ & _ & HSW) & _ & _ & _ & RA & _).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp1 & Hsp2 & _). pose proof alloc_ceiling_val as Hacv.
  unfold CRT_STK, ALLOC_STACK in *.
  apply sd2_stk_norm; [exact RA | |].
  - split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at (ms_segs B) memc a) by (apply HSW; left; lia).
    rewrite SEG in W. unfold writable_at in W. split; [exact W | exact (past_nul.pn_rd memc _ W)].
  - intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
    rewrite (crt_fs_none B SEG a); [reflexivity | left; lia].
Qed.

Lemma sd2_blk_stk : forall Lc Ac memc mdc p n, GI B API L A regs mem md Lc Ac memc mdc -> In (p, n) (blocks Lc Ac) ->
  stk rsegs (normalize rsegs memc) p (p + n) /\ 4096 <= p /\ p + n <= alloc_ceiling /\ p mod 16 = 0.
Proof.
  intros Lc Ac memc mdc p n GIc Hin.
  pose proof GIc as ((HMc & _) & _ & _ & _ & RA & _).
  pose proof alloc_ceiling_val as Hacv.
  destruct (HsKindB.in_blocks Lc Ac p n Hin) as (q & Hq & Ep).
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HMc Hq) as [R1 R2].
  pose proof (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ q n HMc Hq) as AL.
  rewrite <- Ep in R1, R2, AL.
  split; [|split; [exact R1|split; [exact R2 | exact AL]]].
  apply sd2_stk_norm; [exact RA | |].
  - split; [lia|]. split; [lia|]. intros a Ha.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n (a - p) HMc Hq ltac:(lia)) as ((bb & Hb) & _).
    rewrite <- Ep in Hb. replace (p + (a - p)) with a in Hb by lia.
    assert (W : wview rsegs memc (Z_to_bv 64 a) <> None) by (unfold wview; rewrite Hb; discriminate).
    split; [exact W | exact (past_nul.pn_rd memc _ W)].
  - intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
    destruct (crt_blk B API GF AX Lc Ac memc mdc p n (a - p) HMc Hin ltac:(lia)) as (Hr & NI & _).
    replace (p + (a - p)) with a in Hr, NI by lia.
    rewrite (crt_fs_none B SEG a); [reflexivity | right; split; [lia | exact NI]].
Qed.

Lemma sd2_blk_sep : forall Lc Ac memc mdc p n p' n', GI B API L A regs mem md Lc Ac memc mdc ->
  In (p, n) (blocks Lc Ac) -> In (p', n') (blocks Lc Ac) -> (p, n) <> (p', n') -> p + n <= p' \/ p' + n' <= p.
Proof.
  intros Lc Ac memc mdc p n p' n' GIc H1 H2 Hne. pose proof GIc as ((HMc & _) & _).
  destruct (crt_pw_two _ _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HMc) H1 H2 Hne) as [D|D];
    red in D; cbn [fst snd] in D; lia.
Qed.

Lemma sd2_cr_munch : forall X P Lc Ac memc mdc Lamc pk cn Nc W m',
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> munch W memc m' -> wmono rsegs memc m' -> ro_agree rsegs m' ->
  (forall x, ~ outside W x -> (spZ regs - CRT_STK <= x < spZ regs - 104) \/
     exists w n, In (w, n) P /\ w <= x < w + n) ->
  CRs X P Lc Ac m' mdc Lamc pk cn Nc.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc W m' CRc MU WM RA HW.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _).
  pose proof NBc as (INC & _ & NE).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp1 & _). pose proof alloc_ceiling_val as Hacv.
  split.
  { apply (gi_munch B API SEG GF AX L A regs mem md PRE Lc Ac memc mdc W m' GIc MU WM RA).
    intros x Hx. destruct (HW x Hx) as [Hf | (w & n & Hw & Hwx)]; [left; exact Hf|].
    right. exists w, n. split; [apply INC; apply in_or_app; left; exact Hw|].
    split; [apply NE; apply in_or_app; left; exact Hw | exact Hwx]. }
  split; [exact NBc|]. split.
  { apply (put_kb.ledger_munch B API Lc Ac memc mdc Lamc pk cn _ W m' HMc LGc MU).
    - intros a Ha. destruct (kb_outside_dec W a) as [Ho|Ho]; [exact Ho|]. exfalso.
      destruct (crt_GS B API GF a Ha) as [Hi Hr].
      destruct (HW a Ho) as [Hf | (w & n & Hw & Hwx)]; [unfold CRT_STK, ALLOC_STACK in Hf; lia|].
      destruct (crt_blk B API GF AX Lc Ac memc mdc w n (a - w) HMc (INC _ (in_or_app _ _ _ (or_introl Hw)))
        ltac:(lia)) as (_ & NI & _).
      replace (w + (a - w)) with a in NI by lia. exact (NI Hi).
    - intros x k i Hin Hi. destruct (kb_outside_dec W (x - 16 + i)) as [Ho|Ho]; [exact Ho|]. exfalso.
      destruct (crt_lam_blk B Lc Ac memc Lamc pk cn _ x k LGc Hin) as (_ & Hk0 & _).
      apply (Permutation_in _ PMc) in Hin. apply in_app_or in Hin as [Hin|Hin].
      + destruct ((PFX cr_xin) X P Lc Ac memc mdc Lamc pk cn Nc x k (x - 16 + i) CRc Hin ltac:(lia))
          as (_ & Hr & _ & _ & _ & HP).
        destruct (HW _ Ho) as [Hf | (w & n & Hw & Hwx)];
          [unfold CRT_STK, ALLOC_STACK in Hf; lia | exact (HP w n Hw Hwx)].
      + destruct ((PFX cr_lam_x) X P Lc Ac memc mdc Lamc pk cn Nc x k (x - 16 + i) CRc Hin ltac:(lia))
          as (_ & Hr & _ & _ & HP).
        destruct (HW _ Ho) as [Hf | (w & n & Hw & Hwx)];
          [unfold CRT_STK, ALLOC_STACK in Hf; lia | exact (HP w n Hw Hwx)]. }
  repeat (split; [assumption|]). assumption.
Qed.

Section F2.
Context {fx : lib.Reusable.YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

Lemma st2s : St3 ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc want wn q kq bs b kb t tb,
  CRs [(q, kq)] [(want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 66 <= cnt + CRT_ALLOCS -> (158 <= Nc)%nat ->
  wn = (Z.of_nat (length bs) + 2) / 3 * 4 + 1 ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) tb -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13a34 -> getr regsc 10 = Z_to_bv 64 (Z.of_nat (length tb) + 1) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t -> getr regsc 22 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4) ->
  getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 0x16c7c) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros H3 Lc Ac regsc memc mdc Lamc peakc cntc Nc want wn q kq bs b kb t tb CRc HC HN HWN CSQ BOK HL BB Hbin
    Hbk TB TNZ HTL (pt & kt & Hpt & Ht1 & Ht2) HDEC RFc R1 R10 R19 R20 R21 R22 R8 R9.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp0 & Hsp63 & Hsp16).
  pose proof alloc_ceiling_val as Hacv. pose proof PRE as (HM0 & _).
  assert (HE0 : 0 <= (Z.of_nat (length bs) + 2) / 3) by (apply Z.div_pos; lia).
  assert (HEL : Z.of_nat (length (b64_enc bs)) = (Z.of_nat (length bs) + 2) / 3 * 4)
    by exact (check_round_trip_loops.enc_len_Z bs).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ b kb HM0 LG0 Hbin) as (Hb1 & Hb2 & _).
  destruct ((PFX cr_x_lo) [(q, kq)] _ _ _ _ _ _ _ _ _ q kq CRc (or_introl eq_refl)) as (Hq1 & Hq2 & Hq16).
  destruct CSQ as (CL & CK & CF & CB).
  pose proof CRc as (GIc & (INC & _ & _) & _).
  assert (HBq : In (q - 16, kq + 16) (blocks Lc Ac)) by (apply INC; right; left; reflexivity).
  assert (HBb : In (b - 16, kb + 16) (blocks Lc Ac))
    by exact (cr_entry_sub B API L A regs mem md PRE Lam peak cnt bnd _ _ _ _ _ _ _ _ _ _ CRc _
      (LG0_blk B L A mem Lam peak cnt LG0 b kb Hbin)).
  assert (HBt : In (pt, kt) (blocks Lc Ac))
    by exact (cr_entry_sub B API L A regs mem md PRE Lam peak cnt bnd _ _ _ _ _ _ _ _ _ _ CRc _ Hpt).
  destruct (sd2_blk_stk Lc Ac memc mdc pt kt GIc HBt) as (_ & Hpt1 & Hpt2 & _).
  assert (CRc' : CRs [(q, kq)] [(want, wn)] Lc Ac memc mdc Lamc peakc cntc (S (Nc - 1)%nat)).
  { replace (S (Nc - 1)%nat) with Nc by lia. exact CRc. }
  apply (w_malloc B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (MALLOC fx) MAL
    [(q, kq)] [(want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc (Nc - 1)%nat (Z.of_nat (length tb) + 1) post
    CRc' R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10).
  { unfold CRT_SIZE. lia. }
  intros Lc' Ac' regs' memc' mdc' w RP R10' Hw0 Hw1 Hw16 Hwb CR' CS.
  assert (CB' : Mem.bytes_at rsegs memc' q (map (Z_to_bv 8) (b64_enc bs ++ [0]))).
  { apply (cs_bytes_blk B API SEG _ _ _ _ Lc Ac memc mdc Lc' Ac' memc' mdc' (q - 16) (kq + 16) q _ CS HBq).
    - intros E. cbv beta in E. injection E as E1 _. lia.
    - exact CB.
    - lia.
    - rewrite length_map, length_app. cbn [length]. lia.
    - intros i _ []. }
  assert (BB' : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply (cs_bytes_blk B API SEG _ _ _ _ Lc Ac memc mdc Lc' Ac' memc' mdc' (b - 16) (kb + 16) b _ CS HBb).
    - intros E. cbv beta in E. injection E as E1 _. lia.
    - exact BB.
    - lia.
    - unfold bz. rewrite length_map. lia.
    - intros i _ []. }
  assert (TB' : Mem.bytes_at rsegs memc' t (tb ++ [Z_to_bv 8 0])).
  { apply (cs_bytes_blk B API SEG _ _ _ _ Lc Ac memc mdc Lc' Ac' memc' mdc' pt kt t _ CS HBt).
    - intros E. cbv beta in E. injection E as E1 _. lia.
    - exact TB.
    - lia.
    - rewrite length_app. cbn [length]. lia.
    - intros i _ []. }
  pose proof CR' as (GI' & (INC' & ND' & NE') & _).
  pose proof GI' as ((HM' & _) & _ & _ & _ & RA' & _).
  assert (Hin_w : In (want, wn) (blocks Lc' Ac')) by (apply INC'; right; left; reflexivity).
  assert (Hin_q : In (q - 16, kq + 16) (blocks Lc' Ac')) by (apply INC'; right; right; left; reflexivity).
  assert (Hin_b : In (b - 16, kb + 16) (blocks Lc' Ac'))
    by exact (cr_entry_sub B API L A regs mem md PRE Lam peak cnt bnd _ _ _ _ _ _ _ _ _ _ CR' _
      (LG0_blk B L A mem Lam peak cnt LG0 b kb Hbin)).
  assert (Hin_t : In (pt, kt) (blocks Lc' Ac'))
    by exact (cr_entry_sub B API L A regs mem md PRE Lam peak cnt bnd _ _ _ _ _ _ _ _ _ _ CR' _ Hpt).
  assert (NEs : ~ In (w, Z.of_nat (length tb) + 1) (blocks L A))
    by exact (NE' (w, Z.of_nat (length tb) + 1) (or_introl eq_refl)).
  assert (NEw : ~ In (want, wn) (blocks L A)) by exact (NE' (want, wn) (or_intror (or_introl eq_refl))).
  pose proof (LG0_blk B L A mem Lam peak cnt LG0 b kb Hbin) as Hb0.
  apply NoDup_ListNoDup in ND'. cbn [app map xblk fst snd] in ND'.
  apply NoDup_cons_iff in ND' as [N1 ND2]. apply NoDup_cons_iff in ND2 as [N2 _].
  assert (SEPwb : want + wn <= b - 16 \/ b - 16 + (kb + 16) <= want).
  { apply (sd2_blk_sep Lc' Ac' memc' mdc' want wn (b - 16) (kb + 16) GI' Hin_w Hin_b).
    intros E. apply NEw. rewrite E. exact Hb0. }
  assert (SEPwq : want + wn <= q - 16 \/ q - 16 + (kq + 16) <= want).
  { apply (sd2_blk_sep Lc' Ac' memc' mdc' want wn (q - 16) (kq + 16) GI' Hin_w Hin_q).
    intros E. apply N2. left. symmetry. exact E. }
  assert (SEPst : w + (Z.of_nat (length tb) + 1) <= pt \/ pt + kt <= w).
  { apply (sd2_blk_sep Lc' Ac' memc' mdc' w (Z.of_nat (length tb) + 1) pt kt GI' Hwb Hin_t).
    intros E. apply NEs. rewrite E. exact Hpt. }
  assert (SEPsq : w + (Z.of_nat (length tb) + 1) <= q - 16 \/ q - 16 + (kq + 16) <= w).
  { apply (sd2_blk_sep Lc' Ac' memc' mdc' w (Z.of_nat (length tb) + 1) (q - 16) (kq + 16) GI' Hwb Hin_q).
    intros E. apply N1. right. left. symmetry. exact E. }
  assert (SEPsw : w + (Z.of_nat (length tb) + 1) <= want \/ want + wn <= w).
  { apply (sd2_blk_sep Lc' Ac' memc' mdc' w (Z.of_nat (length tb) + 1) want wn GI' Hwb Hin_w).
    intros E. apply N1. left. symmetry. exact E. }
  assert (SEPwt : want + wn <= pt \/ pt + kt <= want).
  { apply (sd2_blk_sep Lc' Ac' memc' mdc' want wn pt kt GI' Hin_w Hin_t).
    intros E. apply NEw. rewrite E. exact Hpt. }
  destruct (sd2_blk_stk Lc' Ac' memc' mdc' want wn GI' Hin_w) as (SW & Hwa1 & Hwa2 & Hwa16).
  destruct (sd2_blk_stk Lc' Ac' memc' mdc' w (Z.of_nat (length tb) + 1) GI' Hwb) as (SS & _ & _ & _).
  pose proof (sd2_frame_stk Lc' Ac' memc' mdc' (spZ regs - 352 + 8) (spZ regs - 352 + 16) GI'
    ltac:(unfold CRT_STK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia)) as SF.
  destruct (stk_carve rsegs _ (spZ regs - 352 + 8) (spZ regs - 352 + 16) 8 SF ltac:(lia)) as [_ (j8 & RW8)].
  replace (spZ regs - 352 + 16 - Z.of_nat 8) with (spZ regs - 352 + 8) in RW8 by lia.
  destruct (stk_carve rsegs _ want (want + wn) (Z.to_nat wn) SW ltac:(rewrite Z2Nat.id by lia; lia))
    as [_ (jw & RWW)].
  rewrite Z2Nat.id in RWW by lia. replace (want + wn - wn) with want in RWW by lia.
  destruct (stk_carve rsegs _ w (w + (Z.of_nat (length tb) + 1)) (S (length tb)) SS ltac:(lia)) as [_ (js & RWS)].
  replace (w + (Z.of_nat (length tb) + 1) - Z.of_nat (S (length tb))) with w in RWS by lia.
  destruct ((PFX crt_slack) [(q, kq)] _ Lc' Ac' memc' mdc' Lamc peakc cntc _ q kq (b64_enc bs) CR' CL CK CB')
    as (slack & TQ & SLL).
  rewrite map_app in TQ. rewrite <- app_assoc in TQ. cbn [map app] in TQ.
  rewrite HEL in SLL.
  assert (PAD : forall p, p mod 16 = 0 -> q + kq <= p ->
    q + ((Z.of_nat (length bs) + 2) / 3 * 4 + 1) + Z.of_nat (length slack) <= p).
  { intros p Hp1 Hp2. rewrite SLL.
    pose proof (sd2_pad_le (q + (Z.of_nat (length bs) + 2) / 3 * 4 + 1) (q + kq) p ltac:(lia) Hp1 Hp2). lia. }
  assert (PADT : q + ((Z.of_nat (length bs) + 2) / 3 * 4 + 1) + Z.of_nat (length slack) < q + kq + 8).
  { rewrite SLL. pose proof (sd2_pad_lt (q + (Z.of_nat (length bs) + 2) / 3 * 4 + 1)). lia. }
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21. sv RP regs' R22 S22 22.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9.
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13a34) memc' mdc'
    (fun R pc' m' => exists m0, (RF regs R /\ getr R 1 = Z_to_bv 64 0x13cc4 /\ getr R 10 = Z_to_bv 64 q /\
       getr R 11 = Z_to_bv 64 (spZ regs - 352 + 8) /\ getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\
       getr R 20 = Z_to_bv 64 b /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 w /\ pc' = Z_to_bv 64 0x15410 /\
       munch [(spZ regs - 352 + 8, spZ regs - 352 + 16);
              (want, want + ((Z.of_nat (length bs) + 2) / 3 * 4 + 1));
              (w, w + Z.of_nat (length tb) + 1)] (normalize rsegs memc') m0 /\
       wmono rsegs (normalize rsegs memc') m0) /\
       mem_rel rsegs m' m0 /\ ro_same rsegs memc' m'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S22, S8, S9.
    apply (PFX crt_evn); [exact RA'|].
    eapply Exec.evt_mono.
    - eapply (crt_r3 STRLEN STRCMP) with (q := q) (want := want) (same := w) (b := b) (t := t)
        (l := Z.of_nat (length bs)) (db := bz bs) (tb := tb) (slq := slack) (j8 := j8) (jw := jw) (js := js).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia. exact RW8.
      + rewrite (sd2_zs_bz bs BOK). apply bytes_at_normalize; [exact RA' | exact TQ].
      + lia.
      + rewrite <- HWN. exact RWW.
      + exact RWS.
      + apply bytes_at_normalize; [exact RA' | exact BB'].
      + unfold bz. rewrite length_map. reflexivity.
      + lia.
      + apply bytes_at_normalize; [exact RA' | exact TB'].
      + exact TNZ.
      + rewrite (sd2_zs_bz bs BOK). exact HDEC.
      + destruct SEPwb as [H|H]; [left | right]; lia.
      + destruct SEPwq as [H|H]; [left; lia | right; apply PAD; [exact Hwa16 | lia]].
      + destruct SEPst as [H|H]; [left | right]; lia.
      + destruct SEPsq as [H|H]; [left; lia | right; apply PAD; [exact Hw16 | lia]].
      + destruct SEPsw as [H|H]; [left | right]; lia.
      + destruct SEPwt as [H|H]; [left | right]; lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + apply mem_inv_normalize.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 &
        u18 & m1 & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|].
      split; [apply ((PFX RF_mk) regs'); [exact RF' | reflexivity ..]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply (PFX crt_spo); lia|].
      do 6 (split; [reflexivity|]).
      rewrite MState.unsigned_lit in MU by lia.
      split; [exact MU | exact WM]. }
  intros RR pc2 mem2 regs2 (m0 & (RF2 & Q1 & Q10 & Q11 & Q19 & Q20 & Q8 & Q9 & Q18 & -> & MU & WM) & HR & ROS) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q19, Q20, Q8, Q9, Q18.
  pose proof (mem_rel_normalize rsegs memc' RA') as HR0.
  pose proof (munch_rel rsegs _ memc' (normalize rsegs memc') mem2 m0 HR0 HR ROS MU) as MU2.
  pose proof (wmono_rel rsegs memc' (normalize rsegs memc') mem2 m0 HR0 HR ROS WM) as WM2.
  pose proof (ro_agree_same rsegs memc' mem2 RA' ROS) as RA2.
  assert (CR2 : CRs [(q, kq)] [(w, Z.of_nat (length tb) + 1); (want, wn)] Lc' Ac' mem2 mdc' Lamc peakc cntc
    (Nc - 1)%nat).
  { apply (sd2_cr_munch _ _ _ _ _ _ _ _ _ _ _ mem2 CR' MU2 WM2 RA2).
    intros x Hx.
    destruct (sd2_ivl (spZ regs - 352 + 8) (spZ regs - 352 + 16) x) as [I1|I1];
      [left; unfold CRT_STK, ALLOC_STACK; lia|].
    destruct (sd2_ivl want (want + ((Z.of_nat (length bs) + 2) / 3 * 4 + 1)) x) as [I2|I2];
      [right; exists want, wn; split; [right; left; reflexivity | lia]|].
    destruct (sd2_ivl w (w + Z.of_nat (length tb) + 1) x) as [I3|I3];
      [right; exists w, (Z.of_nat (length tb) + 1); split; [left; reflexivity | lia]|].
    exfalso. apply Hx. cbn [outside]. split; [exact I1|]. split; [exact I2|]. split; [exact I3 | exact I]. }
  assert (OUT : forall x, 0 <= x < alloc_ceiling -> ~ (want <= x < want + wn) ->
    ~ (w <= x < w + (Z.of_nat (length tb) + 1)) -> mbyte rsegs mem2 x = mbyte rsegs memc' x).
  { intros x H1 H2 H3'. apply (mbyte_munch rsegs _ memc' mem2 x MU2); [lia|]. cbn [outside].
    split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (CB2 : Mem.bytes_at rsegs mem2 q (map (Z_to_bv 8) (b64_enc bs ++ [0]))).
  { apply (crt_bytes_keep memc' mem2 q _ CB'). intros i Hi.
    rewrite length_map, length_app in Hi. cbn [length] in Hi.
    destruct ((PFX cr_xin) [(q, kq)] _ _ _ _ _ _ _ _ _ q kq i CR' (or_introl eq_refl) ltac:(lia))
      as (_ & Hr & _ & _ & _ & HP).
    apply OUT; [lia | exact (HP want wn (or_intror (or_introl eq_refl))) | exact (HP w _ (or_introl eq_refl))]. }
  assert (BB2 : Mem.bytes_at rsegs mem2 b (bz bs)).
  { apply (crt_bytes_keep memc' mem2 b _ BB'). intros i Hi. unfold bz in Hi. rewrite length_map in Hi.
    destruct ((PFX cr_lam_x) [(q, kq)] _ _ _ _ _ _ _ _ _ b kb i CR' Hbin ltac:(lia)) as (_ & Hr & _ & _ & HP).
    apply OUT; [lia | exact (HP want wn (or_intror (or_introl eq_refl))) | exact (HP w _ (or_introl eq_refl))]. }
  exact (H3 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE ENC
    DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM Lc' Ac' regs2 mem2
    mdc' Lamc peakc cntc (Nc - 1)%nat w (Z.of_nat (length tb) + 1) want wn q kq bs b kb CR2 ltac:(lia) ltac:(lia)
    (conj CL (conj CK (conj CF CB2))) BOK HL BB2 Hbin Hbk RF2 Q1 Q10 Q11 Q19 Q20 Q8 Q9 Q18 ltac:(lia) ltac:(lia)).
Qed.

End F2.
End ST.

Lemma st2 : St3 -> St2.
Proof.
  intros H3 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM.
  exact (@st2s rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM H3).
Qed.
