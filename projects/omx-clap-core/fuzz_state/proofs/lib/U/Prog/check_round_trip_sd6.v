(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1786 lines of code are new or changed and 723 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread.v, with its module paths, module names and numbers changed; 1318 of its 1476 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_round_trip_calls.v; 224 of its 410 lines of code are new or changed and 1290 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_round_trip_sd5.v, with its addresses and numbers changed; 120 of its 234 lines of code are new or changed and 296 lines of the source are left out. *)
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


Definition crt_sl6 : list byte :=
  [match seg_rom rsegs (Mem.wa 0x102fe) with Some c => c | None => Z_to_bv 8 0 end;
   match seg_rom rsegs (Mem.wa 0x102ff) with Some c => c | None => Z_to_bv 8 0 end].

Lemma crt_lit6 : forall m, ro_agree rsegs m ->
  Mem.bytes_at rsegs m 0x102f8 (map (Z_to_bv 8) CRT_STATE ++ Z_to_bv 8 0 :: crt_sl6) /\
  forall i, 0 <= i < 6 -> Mem.ro_addr rsegs (Z_to_bv 64 (0x102f8 + i)) = true.
Proof.
  intros m RA.
  assert (H : forall i, (i < 8)%nat -> Mem.ro_addr rsegs (Mem.wa (0x102f8 + Z.of_nat i)) = true /\
    seg_rom rsegs (Mem.wa (0x102f8 + Z.of_nat i)) =
      nth_error (map (Z_to_bv 8) CRT_STATE ++ Z_to_bv 8 0 :: crt_sl6) i).
  { intros i Hi. do 8 (destruct i as [|i]; [split; vm_compute; reflexivity|]). lia. }
  assert (HL : length (map (Z_to_bv 8) CRT_STATE ++ Z_to_bv 8 0 :: crt_sl6) = 8%nat) by reflexivity.
  split.
  - split; [lia|]. split; [rewrite HL; change (Z.of_nat 8) with 8; lia|].
    intros i Hi. rewrite HL in Hi. destruct (H i Hi) as [Hro Hr].
    etransitivity; [exact (RA _ Hro) | exact Hr].
  - intros i Hi. destruct (H (Z.to_nat i) ltac:(lia)) as [Hro _]. rewrite Z2Nat.id in Hro by lia. exact Hro.
Qed.

Lemma crt_state_nz : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) CRT_STATE).
Proof.
  intros H. apply in_map_iff in H as (c & E & Hc).
  assert (F : Forall (fun c => 0 < c < 256) CRT_STATE) by (unfold CRT_STATE; repeat constructor; lia).
  pose proof (proj1 (Forall_forall _ _) F c Hc) as Hr. cbv beta in Hr.
  assert (U : bv_unsigned (Z_to_bv 8 c) = c).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
  rewrite E in U. change (bv_unsigned (Z_to_bv 8 0)) with 0 in U. lia.
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
Local Notation KV := (Z.of_nat (length (map (Z_to_bv 8) CRT_STATE)) + 1) (only parsing).

Ltac retok R1 := rewrite R1; vm_compute; reflexivity.
Ltac kbr HM := first [ exact (proj1 (kb_md B API _ _ _ _ HM)) | exact (proj2 (kb_md B API _ _ _ _ HM)) ].
Ltac sv RP R' H E n :=
  lazymatch type of H with getr _ ?k = ?v =>
    assert (E : getr R' k = v) by (rewrite <- H; exact (RP n ltac:(unfold callee_saved; lia))) end.
Ltac kfin R' RF' :=
  do 3 eexists; split; [reflexivity|];
  split; [apply ((PFX RF_mk) R'); [exact RF' | reflexivity ..]|];
  repeat (split; [first [reflexivity | apply (PFX crt_spo); lia]|]); first [reflexivity | apply (PFX crt_spo); lia].

Section F6.
Context {fx : lib.Reusable.YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

Lemma st6s : St7 ->
  forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 60 <= cnt + CRT_ALLOCS -> (152 <= Nc)%nat ->
  Permutation X (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 192) (JObj [(CRT_FORMAT, JStr CRT_FMT2)]) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13d3c -> getr regsc 10 = Z_to_bv 64 (spZ regs - 352 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x102f8 ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros H7 X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd bs b kb CRc HC HN PX ND NS CSQ
    BOK HL BB Hbin Hbk RFc R1 R10 R11 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp0 & Hsp63 & Hsp16).
  pose proof alloc_ceiling_val as Hacv.
  assert (HKs : PJ_STRING_K = 8288) by reflexivity.
  assert (E5 : Z.of_nat (length (map (Z_to_bv 8) CRT_STATE)) = 5) by reflexivity.
  assert (CRc' : CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc (S (Nc - 1))).
  { replace (S (Nc - 1)) with Nc by lia. exact CRc. }
  pose proof CRc as (GIc & _). pose proof GIc as ((HMc & _) & _ & _ & _ & RAc & _).
  assert (Hv3 : (spZ regs - 352 + 80) mod 8 = 0).
  { replace (spZ regs - 352 + 80) with ((2 * (spZ regs / 16) - 34) * 8)
      by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia).
    apply Z.mod_mul. lia. }
  apply (w_string B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJS fx)
    X [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc (Nc - 1) (spZ regs - 352 + 80) 0x102f8
    (map (Z_to_bv 8) CRT_STATE) crt_sl6 post FRM CRc' R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11).
  { lia. }
  { lia. }
  { exact Hv3. }
  { lia. }
  { rewrite SEG. exact (proj1 (crt_lit6 memc RAc)). }
  { exact crt_state_nz. }
  { apply Z.leb_le. vm_compute. reflexivity. }
  { unfold cstr_ok. left. intros i Hi. rewrite SEG. apply (proj2 (crt_lit6 memc RAc)). lia. }
  { cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  { cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  { unfold CRT_SIZE. lia. }
  { lia. }
  intros Lc' Ac' regs' memc' mdc' a RP R10' CR' CS RDC NODE.
  match type of NODE with pj_node _ _ _ _ (JStr ?z) _ =>
    assert (EZ : z = CRT_STATE) by (vm_compute; reflexivity); rewrite EZ in NODE end.
  pose proof ((PFX incl_perm_l) X Dd _ PX) as ID.
  assert (HXq : In (q, kq) X).
  { assert (H : In (q, kq) [(b1, k1); (q, kq)]) by (cbn [In]; right; left; reflexivity).
    exact ((PFX incl_perm_r) X Dd _ PX (q, kq) H). }
  assert (I0 : forall l : list (Z * Z), incl [] l) by (intros l y []).
  assert (EO : forall p D, spZ regs - 352 + 136 <= p ->
    Eok regs X [(same, sn); (want, wn)] ((a, KV) :: X) [(same, sn); (want, wn)] p D
      (pj_string_writes (spZ regs - 352 + 80))).
  { intros p D Hp x [Hx|Hx]; [right; left; split; lia | left; exact Hx]. }
  assert (ND' : pj_node rsegs memc' (lin ((a, KV) :: Lamc)) (spZ regs - 352 + 192)
    (JObj [(CRT_FORMAT, JStr CRT_FMT2)]) Dd).
  { apply ((PFX cr_keep_node) X _ Lc Ac memc mdc Lamc peakc cntc _ ((a, KV) :: X) _ Lc' Ac' memc' mdc'
      _ _ _ _ _ _ _ _ _ Dd CRc' CR' CS ND ID (fun y Hy => in_cons (a, KV) y X (ID y Hy))).
    - lia.
    - exact (EO (spZ regs - 352 + 192) Dd ltac:(lia)).
    - intros ak kk _ Hg. exact Hg. }
  assert (NS' : pj_node rsegs memc' (lin ((a, KV) :: Lamc)) (spZ regs - 352 + 136) (JObj []) []).
  { apply ((PFX cr_keep_node) X _ Lc Ac memc mdc Lamc peakc cntc _ ((a, KV) :: X) _ Lc' Ac' memc' mdc'
      _ _ _ _ _ _ _ _ _ [] CRc' CR' CS NS (I0 _) (I0 _)).
    - lia.
    - exact (EO (spZ regs - 352 + 136) [] ltac:(lia)).
    - intros ak kk []. }
  destruct CSQ as (CL & CK & CF & CB).
  assert (CSQ' : pj_cstr rsegs memc' (lin ((a, KV) :: Lamc)) q kq (b64_enc bs)).
  { split; [exact (in_cons (a, KV) (q, kq) Lamc CL)|]. split; [exact CK|]. split; [exact CF|].
    apply ((PFX cr_keep_bytes) X _ Lc Ac memc mdc Lamc peakc cntc _ ((a, KV) :: X) _ Lc' Ac' memc' mdc'
      _ _ _ _ _ _ _ (spZ regs - 352 + 192) q kq q _ CRc' CR' CS HXq (in_cons (a, KV) (q, kq) X HXq)
      (EO (spZ regs - 352 + 192) [(q, kq)] ltac:(lia)) (fun Hg => Hg) CB).
    - lia.
    - rewrite length_map, length_app. cbn [length]. lia. }
  assert (BB' : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply ((PFX cr_keep_lam) X _ Lc Ac memc mdc Lamc peakc cntc _ ((a, KV) :: X) _ Lc' Ac' memc' mdc'
      _ _ _ _ _ _ _ (spZ regs - 352 + 192) [] b kb b (bz bs) CRc' CR' CS (EO (spZ regs - 352 + 192) [] ltac:(lia))
      (fun Hg => Hg) Hbin BB ltac:(lia)).
    unfold bz. rewrite length_map. lia. }
  assert (PX' : Permutation ((a, KV) :: X) (Dd ++ [(a, KV)] ++ [(b1, k1); (q, kq)])).
  { eapply perm_trans; [apply perm_skip; exact PX|]. exact (Permutation_middle Dd _ (a, KV)). }
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as (((HM' & _) & _) & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d3c) memc' mdc'
    (fun R pc' m' => RF regs R /\ getr R 1 = Z_to_bv 64 0x13d54 /\ getr R 10 = Z_to_bv 64 (spZ regs - 352 + 192) /\
       getr R 11 = Z_to_bv 64 0x102ba /\ getr R 12 = Z_to_bv 64 (spZ regs - 352 + 80) /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\ getr R 21 = Z_to_bv 64 b1 /\
       getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\
       pc' = Z_to_bv 64 0x14a74 /\ m' = memc')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r7; [exact R10' | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q12 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q12, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (H7 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE ENC
    DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM ((a, KV) :: X) Lc' Ac'
    regs2 memc' mdc' ((a, KV) :: Lamc) _ (cntc + 1) (Nc - 1)%nat same sn want wn q kq b1 k1 Dd [(a, KV)] bs b kb CR'
    ltac:(lia) ltac:(lia) PX' ND' NODE NS' CSQ' BOK HL BB' Hbin Hbk RF2 Q1 Q10 Q11 Q12 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

End F6.
End ST.

Lemma st6 : St7 -> St6.
Proof.
  intros H7 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM.
  exact (@st6s rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM H7).
Qed.
