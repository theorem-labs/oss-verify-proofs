(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 583 of its 659 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/past_nul.v, with its module paths and module names changed; 715 of its 794 lines of code are new or changed and 580 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1788 lines of code are new or changed and 724 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_no_overread.v, with its module paths, module names and numbers changed; 1320 of its 1479 lines of code are new or changed and 1629 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_round_trip_calls.v; 224 of its 413 lines of code are new or changed and 1290 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/check_round_trip_sd5.v, with its addresses and numbers changed; 83 of its 234 lines of code are new or changed and 262 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import HStateRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import check_round_trip_runs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls check_round_trip_stages_a check_round_trip_st8 check_round_trip_stdefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require check_reject_clean_starved past_nul.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.


#[local] Set Default Proof Using "All".

Definition crt_sl4 : list byte :=
  map (fun i => match seg_rom rsegs (Mem.wa (0x10391 + i)) with Some x => x | None => Z_to_bv 8 0 end)
    [0; 1; 2; 3; 4; 5; 6].

Lemma crt_sl4_len : length crt_sl4 = 7%nat.
Proof. reflexivity. Qed.

Lemma crt_klen4 : Z.of_nat (length (map (Z_to_bv 8) CRT_FMT2)) = 22.
Proof. reflexivity. Qed.

Lemma crt_key4_ro : forall i, 0 <= i < 30 -> Mem.ro_addr rsegs (Mem.wa (0x1037a + i)) = true.
Proof.
  intros i Hi. rewrite <- (Z2Nat.id i) by lia.
  assert (Hn : (Z.to_nat i < 30)%nat) by lia.
  revert Hn. generalize (Z.to_nat i) as n. intros n Hn.
  do 30 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma crt_key4 : forall m, ro_agree rsegs m ->
  Mem.bytes_at rsegs m 0x1037a (map (Z_to_bv 8) CRT_FMT2 ++ Z_to_bv 8 0 :: crt_sl4).
Proof.
  intros m RA. unfold ro_agree in RA. unfold Mem.bytes_at.
  change (length (map (Z_to_bv 8) CRT_FMT2 ++ Z_to_bv 8 0 :: crt_sl4)) with 30%nat.
  split; [lia|]. split; [lia|]. intros i Hi.
  transitivity (seg_rom rsegs (Mem.wa (0x1037a + Z.of_nat i))); [apply RA; apply crt_key4_ro; lia|].
  do 30 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma crt_kz4 : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) CRT_FMT2).
Proof.
  intros H. apply in_map_iff in H as (c & E & Hc). apply (f_equal bv_unsigned) in E.
  unfold CRT_FMT2 in Hc.
  repeat (destruct Hc as [Ec|Hc]; [subst c; vm_compute in E; discriminate E|]). destruct Hc.
Qed.

Lemma crt_ks4 :
  (- (0x1037a + Z.of_nat (length (map (Z_to_bv 8) CRT_FMT2)) + 1)) mod 8 <= Z.of_nat (length crt_sl4).
Proof. rewrite crt_klen4, crt_sl4_len. vm_compute. intros H. discriminate H. Qed.

Lemma crt_zb4 : zb (map (Z_to_bv 8) CRT_FMT2) = CRT_FMT2.
Proof. vm_compute. reflexivity. Qed.

Section ST4.
Hypothesis H5 : St5.
Context {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis MAL : ms_malloc B = 0x16c7c.
Hypothesis FRE : ms_free B = 0x16b3c.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : lib.U.Reusable.YL01.AllocExtra B MR.
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
Hypothesis PRE : call_pre_k B MR CRT_STK L A regs mem md.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound).
Hypothesis LG0 : ledger B L A mem Lam peak cnt (2 ^ 64 - 1).
Hypothesis HCNT : cnt + CRT_ALLOCS < 2 ^ 63.
Hypothesis RSP : spZ regs <= 2 ^ 47.
Hypothesis RGT : U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK.
Variable fx0 : lib.Reusable.YK11.FPState.

Local Notation CRs := (CR B API L A regs mem md Lam peak cnt bnd).
Local Notation post := (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
Local Notation RFs := (RF regs).
Local Notation PFX f := (f B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC
  FREE FFREE ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0) (only parsing).

Ltac retok R1 := rewrite R1; vm_compute; reflexivity.
Ltac kbr HM := first [ exact (proj1 (kb_md B API _ _ _ _ HM)) | exact (proj2 (kb_md B API _ _ _ _ HM)) ].
Ltac sv RP R' H E n :=
  lazymatch type of H with getr _ ?k = ?v =>
    assert (E : getr R' k = v) by (rewrite <- H; exact (RP n ltac:(unfold callee_saved; lia))) end.
Ltac kfin R' RF' :=
  do 3 eexists; split; [reflexivity|];
  split; [apply ((PFX RF_mk) R'); [exact RF' | reflexivity ..]|];
  repeat (split; [first [reflexivity | apply (PFX crt_spo); lia]|]); first [reflexivity | apply (PFX crt_spo); lia].

Section F4.
Context {fx : lib.Reusable.YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

Lemma st4_sec : forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 bs b kb,
  CRs [(b1, k1); (q, kq)] [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 64 <= cnt + CRT_ALLOCS -> (156 <= Nc)%nat ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 192) (JObj []) [] ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13d10 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 352 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x1037a ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 bs b kb CRc HC HN ND NS CSQ
    Hbo Hbl BB Hbin Hbk RFc R1 R10 R11 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (_ & _ & H16).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof crt_klen4 as HK4.
  assert (HKs : PJ_STRING_K = 8288) by reflexivity.
  pose proof CRc as ((_ & _ & _ & _ & RAc & _) & _).
  replace Nc with (S (Nc - 1)) in CRc by lia.
  apply (w_string B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJS fx)
    [(b1, k1); (q, kq)] [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc (Nc - 1)
    (spZ regs - 352 + 80) 0x1037a (map (Z_to_bv 8) CRT_FMT2) crt_sl4 post FRM CRc R2 (RG 4 ltac:(lia))
    ltac:(retok R1) R10 R11).
  { lia. }
  { lia. }
  { lia. }
  { lia. }
  { rewrite SEG. exact (crt_key4 memc RAc). }
  { exact crt_kz4. }
  { exact crt_ks4. }
  { unfold cstr_ok. left. intros i Hi. rewrite SEG. apply crt_key4_ro. lia. }
  { cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  { cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  { unfold CRT_SIZE. lia. }
  { lia. }
  intros Lc' Ac' regs' memc' mdc' a RP R10' CR' CS RDC NODE.
  rewrite crt_zb4 in NODE.
  set (k4 := Z.of_nat (length (map (Z_to_bv 8) CRT_FMT2)) + 1) in *.
  assert (HqX : In (q, kq) [(b1, k1); (q, kq)]) by (right; left; reflexivity).
  assert (HqX' : In (q, kq) ((a, k4) :: [(b1, k1); (q, kq)])) by (right; right; left; reflexivity).
  assert (EO : forall p D, spZ regs - 352 + 136 <= p ->
     Eok regs [(b1, k1); (q, kq)] [(same, sn); (want, wn)] ((a, k4) :: [(b1, k1); (q, kq)])
       [(same, sn); (want, wn)] p D (pj_string_writes (spZ regs - 352 + 80))).
  { intros p D Hp x [Hx|Hx]; [right; left; split; lia | left; exact Hx]. }
  assert (KN : forall p, spZ regs - 352 + 136 <= p -> pj_node rsegs memc (lin Lamc) p (JObj []) [] ->
     pj_node rsegs memc' (lin ((a, k4) :: Lamc)) p (JObj []) []).
  { intros p Hp Hn.
    apply ((PFX cr_keep_node) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p (JObj []) [] CRc CR' CS Hn
      (incl_nil_l _) (incl_nil_l _)).
    - lia.
    - exact (EO p [] Hp).
    - intros a0 k0 []. }
  assert (CSQ' : pj_cstr rsegs memc' (lin ((a, k4) :: Lamc)) q kq (b64_enc bs)).
  { destruct CSQ as (Cq1 & Cq2 & Cq3 & Cq4).
    split; [exact (cr_in_lam B API L A regs mem md Lam peak cnt bnd _ _ _ _ _ _ _ _ _ _ q kq CR' HqX')|].
    split; [exact Cq2|]. split; [exact Cq3|].
    apply ((PFX cr_keep_bytes) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - 352 + 136) q kq q _
      CRc CR' CS HqX HqX').
    - apply EO. lia.
    - exact (fun H => H).
    - exact Cq4.
    - lia.
    - rewrite length_map, length_app. cbn [length]. lia. }
  assert (BB' : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply ((PFX cr_keep_lam) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - 352 + 136) [] b kb b (bz bs)
      CRc CR' CS).
    - apply EO. lia.
    - exact (fun H => H).
    - exact Hbin.
    - exact BB.
    - lia.
    - unfold bz. rewrite length_map. lia. }
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d10) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13d28 /\ getr R 10 = Z_to_bv 64 (spZ regs - 352 + 192) /\
       getr R 11 = Z_to_bv 64 0x1036e /\ getr R 12 = Z_to_bv 64 (spZ regs - 352 + 80) /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\
       getr R 20 = Z_to_bv 64 b /\ getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\
       getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14a74 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r5; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q12 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q12, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (H5 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM
    ((a, k4) :: [(b1, k1); (q, kq)]) Lc' Ac' regs2 memc' mdc' ((a, k4) :: Lamc) _ (cntc + 1) (Nc - 1)%nat
    same sn want wn q kq b1 k1 [(a, k4)] bs b kb CR' ltac:(unfold CRT_ALLOCS; lia) ltac:(lia) (Permutation_refl _)
    (KN (spZ regs - 352 + 192) ltac:(lia) ND) NODE (KN (spZ regs - 352 + 136) ltac:(lia) NS) CSQ' Hbo Hbl BB'
    Hbin Hbk RF2 Q1 Q10 Q11 Q12 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

End F4.
End ST4.

Lemma st4 : St5 -> St4.
Proof. intros H5 rc. exact (@st4_sec H5 rc). Qed.
