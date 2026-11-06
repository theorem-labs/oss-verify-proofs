(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 556 of its 631 lines of code are new or changed and 671 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/past_nul.v, with its module names changed; 711 of its 786 lines of code are new or changed and 556 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_as_written.v, with its module names, addresses and numbers changed; 1716 of its 1784 lines of code are new or changed and 718 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_no_overread.v, with its module paths, module names and numbers changed; 1316 of its 1472 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_calls.v; 223 of its 404 lines of code are new or changed and 1291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_sd5.v, with its addresses and numbers changed; 121 of its 224 lines of code are new or changed and 301 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger LedgerFacts HState ReaderRes WriterSpec PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import KindBGlue HStateRoom fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import check_round_trip_runs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls check_round_trip_stages_a check_round_trip_st8 check_round_trip_stdefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.

(* check_round_trip (check_4, plain, 0x138ac): stage 1, st1 : St2 -> St1. From the entry of c1 = malloc((len + 2) / 3
   * 4 + 1), the malloc wrapper, then crt_r2 (strlen(input)) to the entry of c2 = malloc(strlen(input) + 1), then St2.
   malloc keeps the input's string (in a block of the caller); the slack strlen reads after its NUL is read again in
   malloc's memory: inside the caller's block from the bytes malloc kept, past it from block_slack_present. *)

#[local] Set Default Proof Using "All".

(* The slack after a NUL at y - 1 up to the next 8-byte boundary stays below the 8-byte boundary after z >= y. *)
Lemma crt_sl_room : forall y z i, y <= z -> 0 <= i < (- y) mod 8 -> y + i < 8 * ((z + 7) / 8).
Proof. intros y z i Hyz Hi. Z.div_mod_to_equations. lia. Qed.

Section ST1.
Hypothesis H2 : St2.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis MAL : ms_malloc B = 0x16594.
Hypothesis FRE : ms_free B = 0x16454.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis CO : ctx_owned B API.
Hypothesis BSP : block_slack_present B API.
Hypothesis RTP : ms_tp B = strtod_c.STRTOD_TP.
Hypothesis RER : errno_addr B = strtod_c.STRTOD_ERRNO.
Hypothesis RGG : ms_got_guard B = strtod_c.STRTOD_GOT_GUARD.
Hypothesis RGD : ms_guard B = strtod_c.STRTOD_GUARD.
Hypothesis STRLEN : strlen_contract.
Hypothesis STRCMP : strcmp_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis PJO : pj_object_contract.
Hypothesis PJG : pj_get_contract.
Hypothesis PJGS : pj_get_str_contract.
Hypothesis MALLOC : forall fx' : YK11.FPState, malloc_contract (fx := fx') B API.
Hypothesis FREE : forall fx' : YK11.FPState, free_contract (fx := fx') B API.
Hypothesis FFREE : forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form.
Hypothesis ENC : forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form.
Hypothesis DEC : forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form.
Hypothesis PJS : forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form.
Hypothesis PJSET : forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form.
Hypothesis PJF : forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form.
Hypothesis PJW : forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API.
Hypothesis PJP : forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : call_pre_k B MR CRT_STK L A regs mem md.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound).
Hypothesis LG0 : ledger B L A mem Lam peak cnt (2 ^ 64 - 1).
Hypothesis HCNT : cnt + CRT_ALLOCS < 2 ^ 63.
Hypothesis RSP : spZ regs <= 2 ^ 47.
Hypothesis RGT : strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK.
Variable fx0 : YK11.FPState.

Local Notation CRs := (CR B API L A regs mem md Lam peak cnt bnd).
Local Notation post := (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
Local Notation RFs := (RF regs).
(* A lemma of check_round_trip_stages_a.v at this section's variables. *)
Local Notation PFX f := (f B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC
  FREE FFREE ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0) (only parsing).

Ltac retok R1 := rewrite R1; vm_compute; reflexivity.
Ltac kbr HM := first [ exact (proj1 (kb_md B API _ _ _ _ HM)) | exact (proj2 (kb_md B API _ _ _ _ HM)) ].
Ltac sv RP R' H E n :=
  lazymatch type of H with getr _ ?k = ?v =>
    assert (E : getr R' k = v) by (rewrite <- H; exact (RP n ltac:(unfold callee_saved; lia))) end.

Section F1.
Context {fx : YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

(* c1: malloc((len + 2) / 3 * 4 + 1), then crt_r2 (strlen(input)) to malloc(strlen(input) + 1) *)
Lemma st1_sec : forall Lc Ac regsc memc mdc Lamc peakc cntc Nc q kq bs b kb t tb slack,
  CRs [(q, kq)] [] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 67 <= cnt + CRT_ALLOCS -> (159 <= Nc)%nat ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13918 ->
  getr regsc 10 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4 + 1) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t -> getr regsc 22 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4) ->
  getr regsc 8 = Z_to_bv 64 q ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 0x16594) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros Lc Ac regsc memc mdc Lamc peakc cntc Nc q kq bs b kb t tb slack CRc HC HN CSQ Hbo Hbl BB Hbin Hbk
    TB NZ SL Htl EX HD RFc R1 R10 R19 R20 R21 R22 R8.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof PRE as (HM0 & _).
  pose proof CRc as (GIc & _).
  destruct EX as (pt & kt & Hpt & Hpt1 & Hpt2).
  pose proof (crt_blk B API GF AX L A mem md pt kt 0 HM0 Hpt ltac:(lia)) as (Hp0 & _).
  pose proof (crt_blk B API GF AX L A mem md pt kt (t - pt) HM0 Hpt ltac:(lia)) as (Ht0 & _).
  pose proof (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc pt kt GIc Hpt) as Hptc.
  assert (G1 : (pt, kt) <> (0, 0)) by (intros E; injection E as E1 _; lia).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ b kb HM0 LG0 Hbin) as (Hb1 & Hb2 & _).
  destruct ((PFX cr_x_lo) _ _ _ _ _ _ _ _ _ _ q kq CRc (or_introl eq_refl)) as (Hq1 & Hq2 & _).
  (* the input's string and the slack after it, in the caller's memory *)
  assert (TB0 : Mem.bytes_at rsegs memc t (tb ++ [Z_to_bv 8 0]) /\
                Mem.bytes_at rsegs memc (t + Z.of_nat (length tb) + 1) slack).
  { replace (tb ++ Z_to_bv 8 0 :: slack) with ((tb ++ [Z_to_bv 8 0]) ++ slack) in TB
      by (rewrite <- app_assoc; reflexivity).
    apply Mem.bytes_at_app in TB as [T1 T2]. split; [exact T1|].
    rewrite length_app in T2. cbn [length] in T2.
    replace (t + Z.of_nat (length tb + 1)) with (t + Z.of_nat (length tb) + 1) in T2 by lia. exact T2. }
  destruct TB0 as [TB1 TBS].
  assert (Hn : 0 <= (Z.of_nat (length bs) + 2) / 3 <= 2 ^ 20).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  replace Nc with (S (Nc - 1)) in CRc by lia.
  apply (w_malloc B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (MALLOC fx) MAL
    [(q, kq)] [] Lc Ac regsc memc mdc Lamc peakc cntc (Nc - 1) ((Z.of_nat (length bs) + 2) / 3 * 4 + 1) post
    CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10).
  { unfold CRT_SIZE. lia. }
  intros Lc' Ac' regs' memc' mdc' w RP R10' Hw0 Hwc Hw16 HWB CR' CS.
  pose proof CS as (HM' & _).
  destruct (cs_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ pt kt CS Hptc G1) as [Hptc' KB].
  (* malloc kept the input's string *)
  assert (TB1' : Mem.bytes_at rsegs memc' t (tb ++ [Z_to_bv 8 0])).
  { apply (cs_bytes_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ pt kt t _ CS Hptc G1 TB1).
    - lia.
    - rewrite length_app. cbn [length]. lia.
    - intros i _ []. }
  (* the slack strlen reads after the NUL, in malloc's memory *)
  pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length tb) + 1)) 8 ltac:(lia)) as Hr.
  destruct ((PFX crt_mk_bytes) rsegs memc' (t + Z.of_nat (length tb) + 1)
    (Z.to_nat ((- (t + Z.of_nat (length tb) + 1)) mod 8)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia))
    as (sl & Hsl & BSL).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia.
    destruct (Z_lt_le_dec (t + Z.of_nat (length tb) + 1 + i) (pt + kt)) as [Hx|Hx].
    - pose proof (crt_bytes_some memc (t + Z.of_nat (length tb) + 1) slack i TBS ltac:(lia)) as NN.
      rewrite <- (KB (t + Z.of_nat (length tb) + 1 + i) ltac:(lia) (fun H => H)) in NN.
      destruct (mbyte rsegs memc' (t + Z.of_nat (length tb) + 1 + i)) as [v|] eqn:Ev;
        [|exfalso; exact (NN eq_refl)].
      exists v. exact Ev.
    - destruct (BSP Lc' Ac' memc' mdc' pt kt (t + Z.of_nat (length tb) + 1 + i) HM' Hptc') as [v Hv].
      { split; [lia|]. apply crt_sl_room; lia. }
      exists v. unfold Mem.mrd, Mem.wa. rewrite Hv. reflexivity. }
  assert (TB' : Mem.bytes_at rsegs memc' t (tb ++ Z_to_bv 8 0 :: sl)).
  { replace (tb ++ Z_to_bv 8 0 :: sl) with ((tb ++ [Z_to_bv 8 0]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply Mem.bytes_at_app. split; [exact TB1'|]. rewrite length_app. cbn [length].
    replace (t + Z.of_nat (length tb + 1)) with (t + Z.of_nat (length tb) + 1) by lia. exact BSL. }
  assert (SL' : (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length sl))
    by (rewrite Hsl, Z2Nat.id by lia; lia).
  (* the text and the body across malloc *)
  assert (CSQ' : pj_cstr rsegs memc' (lin Lamc) q kq (b64_enc bs)).
  { destruct CSQ as (Cq1 & Cq2 & Cq3 & Cq4).
    split; [exact Cq1|]. split; [exact Cq2|]. split; [exact Cq3|].
    apply ((PFX cr_keep_bytes) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 q kq q _ CRc CR' CS
      (or_introl eq_refl) (or_introl eq_refl)).
    - intros x [].
    - intros E. cbv beta in E. injection E as E1 _. lia.
    - exact Cq4.
    - lia.
    - rewrite length_map, length_app. cbn [length]. lia. }
  assert (BB' : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply ((PFX cr_keep_lam) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 [] b kb b (bz bs) CRc CR' CS).
    - intros x [].
    - intros E. cbv beta in E. injection E as E1 _. lia.
    - exact Hbin.
    - exact BB.
    - lia.
    - unfold bz. rewrite length_map. lia. }
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21. sv RP regs' R22 S22 22.
  sv RP regs' R8 S8 8.
  pose proof CR' as ((MID' & _ & _ & _ & RA' & _) & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13918) memc' mdc'
    (fun R pc' m' => exists m0, (RFs R /\ getr R 1 = Z_to_bv 64 0x1392c /\
       getr R 10 = Z_to_bv 64 (Z.of_nat (length tb) + 1) /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\
       getr R 21 = Z_to_bv 64 t /\ getr R 22 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4) /\
       getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 w /\ pc' = Z_to_bv 64 0x16594 /\
       munch [] (normalize rsegs memc') m0) /\ mem_rel rsegs m' m0 /\ ro_same rsegs memc' m'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S22, S8.
    apply (PFX crt_evn); [exact RA'|].
    eapply Exec.evt_mono.
    - eapply (crt_r2 STRLEN) with (t := t) (tb := tb) (slack := sl).
      + reflexivity.
      + lia.
      + apply bytes_at_normalize; [exact RA' | exact TB'].
      + exact NZ.
      + exact SL'.
      + apply mem_inv_normalize.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU & _ & _).
      rewrite (MState.unsigned_lit (Z.of_nat (length tb))) by lia.
      do 3 eexists. split; [reflexivity|].
      split; [apply ((PFX RF_mk) regs'); [exact RF' | reflexivity ..]|].
      do 9 (split; [reflexivity|]). exact MU. }
  intros RR pc2 mem2 regs2 (m0 & (RF2 & Q1 & Q10 & Q19 & Q20 & Q21 & Q22 & Q8 & Q9 & -> & MU) & HR & ROS) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q19, Q20, Q21, Q22, Q8, Q9.
  (* crt_r2 wrote no memory *)
  assert (EQ : forall x, mem2 x = memc' x).
  { apply (mem_unchanged_rel rsegs memc' (normalize rsegs memc') mem2 m0 (mem_rel_normalize rsegs memc' RA') HR ROS).
    intros x. apply MU. exact I. }
  assert (KEEP : forall y bs0, Mem.bytes_at rsegs memc' y bs0 -> Mem.bytes_at rsegs mem2 y bs0).
  { intros y bs0 H. apply (crt_bytes_keep memc' mem2 y bs0 H). intros i _. unfold mbyte. rewrite EQ. reflexivity. }
  pose proof ((PFX cr_eqm) _ _ _ _ _ _ _ _ _ _ mem2 CR' EQ) as CR2.
  assert (CSQ2 : pj_cstr rsegs mem2 (lin Lamc) q kq (b64_enc bs)).
  { destruct CSQ' as (C1 & C2 & C3 & C4). exact (conj C1 (conj C2 (conj C3 (KEEP _ _ C4)))). }
  exact (H2 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM
    Lc' Ac' regs2 mem2 mdc' Lamc peakc cntc (Nc - 1)%nat w ((Z.of_nat (length bs) + 2) / 3 * 4 + 1) q kq bs b kb t tb
    CR2 ltac:(unfold CRT_ALLOCS; lia) ltac:(lia) eq_refl CSQ2 Hbo Hbl (KEEP _ _ BB') Hbin Hbk (KEEP _ _ TB1') NZ Htl
    (ex_intro _ pt (ex_intro _ kt (conj Hpt (conj Hpt1 Hpt2)))) HD
    RF2 Q1 Q10 Q19 Q20 Q21 Q22 Q8 Q9).
Qed.

End F1.
End ST1.

Lemma st1 : St2 -> St1.
Proof. intros H2 rc. exact (@st1_sec H2 rc). Qed.
