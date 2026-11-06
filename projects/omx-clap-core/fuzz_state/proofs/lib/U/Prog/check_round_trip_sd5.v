(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1786 lines of code are new or changed and 723 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread.v, with its module paths, module names and numbers changed; 1318 of its 1476 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_round_trip_calls.v; 224 of its 410 lines of code are new or changed and 1290 lines of the source are left out. *)
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


#[local] Set Default Proof Using "All".

Definition crt_sl5 : list byte :=
  map (fun i => match seg_rom rsegs (Mem.wa (0x10375 + i)) with Some x => x | None => Z_to_bv 8 0 end) [0; 1; 2].

Lemma crt_sl5_len : length crt_sl5 = 3%nat.
Proof. reflexivity. Qed.

Lemma crt_klen5 : Z.of_nat (length (map (Z_to_bv 8) CRT_FORMAT)) = 6.
Proof. reflexivity. Qed.

Lemma crt_key5_ro : forall i, 0 <= i < 10 -> Mem.ro_addr rsegs (Mem.wa (0x1036e + i)) = true.
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma crt_key5 : forall m, ro_agree rsegs m ->
  Mem.bytes_at rsegs m 0x1036e (map (Z_to_bv 8) CRT_FORMAT ++ Z_to_bv 8 0 :: crt_sl5).
Proof.
  intros m RA. unfold ro_agree in RA. unfold Mem.bytes_at.
  change (length (map (Z_to_bv 8) CRT_FORMAT ++ Z_to_bv 8 0 :: crt_sl5)) with 10%nat.
  split; [lia|]. split; [lia|]. intros i Hi.
  transitivity (seg_rom rsegs (Mem.wa (0x1036e + Z.of_nat i))); [apply RA; apply crt_key5_ro; lia|].
  do 10 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma crt_kz5 : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) CRT_FORMAT).
Proof.
  intros H. apply in_map_iff in H as (c & E & Hc). apply (f_equal bv_unsigned) in E.
  unfold CRT_FORMAT in Hc.
  repeat (destruct Hc as [Ec|Hc]; [subst c; vm_compute in E; discriminate E|]). destruct Hc.
Qed.

Lemma crt_ks5 :
  (- (0x1036e + Z.of_nat (length (map (Z_to_bv 8) CRT_FORMAT)) + 1)) mod 8 <= Z.of_nat (length crt_sl5).
Proof. rewrite crt_klen5, crt_sl5_len. vm_compute. intros H. discriminate H. Qed.

Lemma crt_zb5 : zb (map (Z_to_bv 8) CRT_FORMAT) = CRT_FORMAT.
Proof. vm_compute. reflexivity. Qed.

Section ST5.
Hypothesis H6 : St6.
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

Section F5.
Context {fx : lib.Reusable.YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

Lemma w_set5 : pj_set_contract (fx := fx) B API sb_form ->
  forall X P Lc Ac regsc memc mdc Lamc peakc cntc Nc o w k ms tv D Dw Y kname slack (Q : config -> Prop),
  frm_zero (@fp_csr fx) ->
  CRs X P Lc Ac memc mdc Lamc peakc cntc (Datatypes.S (Datatypes.S (Datatypes.S Nc))) ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 352) -> getr regsc 4 = getr regs 4 -> lib.Reusable.YK0s.ret_ok (getr regsc 1) ->
  getr regsc 10 = Z_to_bv 64 o -> getr regsc 11 = Z_to_bv 64 k -> getr regsc 12 = Z_to_bv 64 w ->
  spZ regs - 352 <= o -> o + 56 <= spZ regs - 104 ->
  spZ regs - 352 <= w -> w + 56 <= spZ regs - 104 -> o + 56 <= w \/ w + 56 <= o ->
  pj_node rsegs memc (lin Lamc) o (JObj ms) D -> pj_node rsegs memc (lin Lamc) w tv Dw ->
  Permutation X (D ++ Dw ++ Y) ->
  (depth (JObj ms) <= 2)%nat -> (depth tv <= 1)%nat -> (length ms <= 2)%nat -> ~ In (zb kname) (map fst ms) ->
  Mem.bytes_at (ms_segs B) memc k (kname ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) kname ->
  (- (k + Z.of_nat (length kname) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (forall i, 0 <= i < Z.of_nat (length kname) + 1 + Z.of_nat (length slack) ->
     Mem.ro_addr rsegs (Z_to_bv 64 (k + i)) = true) ->
  Z.of_nat (length kname) + 17 <= CRT_SIZE -> cntc < 2 ^ 63 ->
  (forall Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' Do,
     regs_preserved regsc regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     CRs (Do ++ Y) P Lc' Ac' memc' mdc' Lamc' peakc' cntc' Nc -> cntc' <= cntc + 3 ->
     cs B API (spZ regs - 352) (PJ_SET_K 1) (pj_set_writes o w D Dw) (freed (D ++ Dw))
       Lc Ac memc mdc Lc' Ac' memc' mdc' ->
     rd_cells B memc' ->
     pj_node rsegs memc' (lin Lamc') o (JObj (pj_set_model ms (zb kname) tv)) Do -> pj_zero rsegs memc' w ->
     SR (ms_segs B) (mkCfg (@mkst fx regs' (getr regsc 1) memc' (seg_rom (ms_segs B))) mdc') Q) ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc) Q.
Proof.
  intros PJC X P Lc Ac regsc memc mdc Lamc peakc cntc Nc o w k ms tv D Dw Y kname slack Q FRM0 CRc R2 R4 R1 R10 R11
    R12 Ho1 Ho2 Hw1 Hw2 HOW NO NW PX Hd1 Hd2 Hlen HK KB KZ KS KRO Hksz Hc K.
  pose proof CRc as (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  pose proof GIc as ((HMc & _) & _ & _ & INIc & RAc & _).
  pose proof crt_sp B API L A regs mem md PRE as (Hsp1 & Hsp2 & _).
  pose proof alloc_ceiling_val as Hacv. pose proof lib.Reusable.YM05.alloc_ceiling_lt as Hacl. pose proof LGc as (_ & _ & Hc00 & _).
  assert (HKs : PJ_SET_K 1 = 8400) by reflexivity.
  destruct (crt_renv B API SEG AX L A regs mem md PRE RTP RER RGG RGD RSP RGT Lc Ac memc mdc regsc (PJ_SET_K 1) GIc
    R2 R4 R1 ltac:(lia) ltac:(unfold CRT_STK, ALLOC_STACK; lia) FRM0) as [SPc ENV].
  pose proof NO as NO'. cbn [pj_node] in NO'.
  destruct NO' as (_ & _ & num & str & kids & keys & n & cap & HH & _ & En & Hncap & Hcap & _).
  assert (Hcap54 : cap <= 2 ^ 54).
  { destruct Hcap as [(-> & _)|(Hc0 & Hk & _)]; [lia|].
    pose proof (ledger_block_range B API Lc Ac memc mdc Lamc peakc cntc _ kids (56 * cap) HMc LGc Hk) as (Rk & R & _).
    lia. }
  pose proof (cr_nodup B API L A regs mem md Lam peak cnt bnd X P Lc Ac memc mdc Lamc peakc cntc _ CRc) as NDX.
  assert (NDl : List.NoDup (D ++ Dw ++ Y)).
  { apply (NoDup_map_inv fst). exact (Permutation_NoDup (Permutation_map fst PX) NDX). }
  assert (LO : forall a kk, In (a, kk) (D ++ Dw ++ Y) ->
     4112 <= a /\ a + kk <= alloc_ceiling /\ 0 <= kk /\ forall i, -16 <= i < kk -> ~ in_img B (a + i)).
  { intros a kk H.
    destruct (cr_X_lam B API L A regs mem md Lam peak cnt bnd X P Lc Ac memc mdc Lamc peakc cntc _ _ CRc PX a kk H)
      as (_ & H1 & H2 & H3 & H4).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
  assert (KI : forall x, k <= x < k + Z.of_nat (length kname) + 1 -> in_img B x /\ x < alloc_ceiling).
  { intros x Hx. destruct KB as (Hk0 & Hkl & _). rewrite length_app in Hkl. cbn [length] in Hkl.
    assert (HI : in_img B x).
    { apply (crt_ro_img B SEG); [lia|]. replace x with (k + (x - k)) by lia. apply KRO. lia. }
    split; [exact HI|]. destruct (crt_IL B SEG) as [IL _]. pose proof (IL x HI). lia. }
  assert (Hn2 : 0 <= n <= 2) by lia.
  destruct (set_trace_ok n cap (Z.of_nat (length kname)) Hn2 ltac:(lia) Hksz Hncap) as [TF TL].
  destruct (room_cap _ (bat bnd X P) (Datatypes.S (Datatypes.S (Datatypes.S Nc))) TF ltac:(lia) HCc) as [ROOM HCr].
  assert (HGX : forall a0 n0, freed (D ++ Dw) a0 n0 -> In (a0, n0) (map xblk X)).
  { intros a0 n0 Hg. unfold freed in Hg. apply in_map_iff. exists (a0 + 16, n0 - 16).
    split; [unfold xblk; cbn [fst snd]; f_equal; lia|].
    apply (Permutation_in _ (Permutation_sym PX)). rewrite app_assoc. apply in_or_app. left. exact Hg. }
  eapply SR_bind.
  { apply (PJC Lc Ac regsc memc mdc Lamc peakc cntc (2 ^ 64 - 1) (bat bnd X P) o k w ms tv D Dw num str kids keys n
      cap kname slack 1%nat ENV LGc RSc R10 R11 R12).
    - lia.
    - rewrite SEG. exact NO.
    - rewrite SEG. exact HH.
    - exact Hcap54.
    - exact (crt_rplace_frame B API SEG ERR GF L A regs mem md PRE RSP Lc Ac memc mdc Lamc regsc o HMc INIc SPc Ho1
        ltac:(lia)).
    - lia.
    - rewrite SEG. exact NW.
    - exact (crt_rplace_frame B API SEG ERR GF L A regs mem md PRE RSP Lc Ac memc mdc Lamc regsc w HMc INIc SPc Hw1
        ltac:(lia)).
    - intros bk H1 H2. exact (crt_nd_app_not D (Dw ++ Y) bk NDl H2 (in_or_app _ _ _ (or_introl H1))).
    - intros x Hx [Hx'|([a kk] & Hb & Hbx)]; [lia|]. unfold pj_holds in Hbx. cbn [fst snd] in Hbx.
      destruct (LO a kk (in_or_app _ _ _ (or_introl Hb))) as (_ & R & _). lia.
    - intros [a kk] x Hb Hbx Hx. unfold pj_holds in Hbx. cbn [fst snd] in Hbx.
      destruct (LO a kk ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (_ & R & _). lia.
    - exact Hd1.
    - exact Hd2.
    - exact KB.
    - exact KZ.
    - exact KS.
    - unfold cstr_ok. left. intros i Hi. rewrite SEG. exact (KRO i Hi).
    - intros x Hx. destruct (KI x Hx) as [HI Hxa]. split.
      + intros [Hx'|([a kk] & Hb & Hbx)]; [lia|]. unfold pj_holds in Hbx. cbn [fst snd] in Hbx.
        destruct (LO a kk (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & NI).
        apply (NI (x - a)); [lia|]. replace (a + (x - a)) with x by lia. exact HI.
      + intros [Hx'|([a kk] & Hb & Hbx)]; [lia|]. unfold pj_holds in Hbx. cbn [fst snd] in Hbx.
        destruct (LO a kk ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (_ & _ & _ & NI).
        apply (NI (x - a)); [lia|]. replace (a + (x - a)) with x by lia. exact HI.
    - rewrite SPc. pose proof (KI (k + Z.of_nat (length kname)) ltac:(lia)) as (_ & Hke).
      cbn [Frame.disjoint_from]. unfold CRT_STK, ALLOC_STACK in *. lia.
    - lia.
    - exact ROOM. }
  intros c1 (L' & A' & regs' & mem' & md' & Lam' & peak' & fail' & res & c & Lr & Do & -> & RP & RDC & R10' & LG' & FA &
    PL & PL' & ZW & _ & BR).
  destruct BR as [(HIn & _) | [(_ & Hrng & Hcl & Hres & Hpk & RES' & HLD & HLS &
    (Dold & Dnew & Dr & a & PD & PDo & FRESH & _) & NODE) | (_ & Hrng & _)]];
    [exact (False_rect _ (HK HIn)) | | lia].
  subst res.
  rewrite (proj2 FA) in LG' by lia.
  destruct (cs_of_rpost B API AX CO (PJ_SET_K 1) Lc Ac regsc memc mdc _ _ L' A' regs' mem' md' HMc RP) as [CS RP'].
  rewrite SPc in CS. pose proof CS as (HM' & _).
  rewrite SEG in NODE, ZW.
  assert (PLr : Permutation Lr (Y ++ Lam)).
  { apply (Permutation_app_inv_l (D ++ Dw)). rewrite <- !app_assoc.
    eapply Permutation_trans; [exact (Permutation_sym PL)|]. eapply Permutation_trans; [exact PMc|].
    rewrite !app_assoc. apply Permutation_app_tail. rewrite <- !app_assoc. exact PX. }
  assert (PX' : Permutation Lam' ((Do ++ Y) ++ Lam)).
  { rewrite <- app_assoc. eapply Permutation_trans; [exact PL'|]. apply Permutation_app_head. exact PLr. }
  assert (HL1 : length X = (length D + length Dw + length Y)%nat) by (rewrite (Permutation_length PX), !length_app; lia).
  assert (HS1 : lsum X = lsum D + lsum Dw + lsum Y) by (rewrite (lsum_perm _ _ PX), !lsum_app; lia).
  rewrite length_app in HLD. rewrite lsum_app in HLS.
  assert (BAT : rf_run sb_form (bat bnd X P) (set_trace n cap (Z.of_nat (length kname))) = bat bnd (Do ++ Y) P).
  { apply bat_run; rewrite ?length_app, ?lsum_app; lia. }
  apply (K L' A' regs' mem' md' Lam' peak' (cntc + Z.of_nat c) Do RP' R10');
    [| lia | exact CS | exact RDC | exact NODE | exact ZW].
  apply (cr_mk B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd X P Lc Ac memc mdc Lamc peakc cntc _
    (Do ++ Y) P L' A' mem' md' Lam' peak' (cntc + Z.of_nat c) Nc (PJ_SET_K 1) _ _ CRc CS).
  - pose proof RDC as (RA' & _). rewrite <- SEG. exact RA'.
  - exact (crt_gk B memc mem' (crt_rdc B API SEG AX Lc Ac memc mdc HMc RAc) RDC).
  - lia.
  - unfold CRT_STK, ALLOC_STACK. lia.
  - intros p nn Hp Hg. pose proof NBc as (_ & _ & NE). apply (NE (p, nn)); [|exact Hp].
    apply in_or_app. right. exact (HGX p nn Hg).
  - intros x Hx. unfold pj_set_writes in Hx.
    destruct Hx as [Hx|[Hx|[(aa & kk & Hb & Hbx)|Hx]]].
    + right. left. split; [lia | exact (crt_node_present mem' _ o _ _ x NODE Hx)].
    + right. left. split; [lia | exact (crt_rw_present mem' w x (proj1 ZW) Hx)].
    + right. right. left. exists (xblk (aa, kk)). split; [|unfold xblk; cbn [fst snd]; lia].
      apply in_or_app. right. apply in_map. apply (Permutation_in _ (Permutation_sym PX)). rewrite app_assoc.
      apply in_or_app. left. exact Hb.
    + left. exact Hx.
  - intros x Hx. unfold pj_set_writes.
    assert (NB : ~ blk_set (D ++ Dw) x).
    { intros (aa & kk & Hb & Hbx). destruct (LO aa kk ltac:(rewrite app_assoc; apply in_or_app; left; exact Hb))
        as (_ & R & _). unfold CRT_STK, ALLOC_STACK in *. lia. }
    assert (NS : ~ alloc_statics x).
    { intros Hs. destruct (crt_GS B API GF x Hs) as [_ Hr]. unfold CRT_STK, ALLOC_STACK in *. lia. }
    assert (DC : (o <= x < o + 56 \/ w <= x < w + 56) \/ ~ (o <= x < o + 56 \/ w <= x < w + 56)) by lia.
    destruct DC as [DC|DC]; [left; destruct DC as [DC|DC]; [left | right; left]; exact DC|].
    right. intros [H|[H|[H|H]]]; [exact (DC (or_introl H)) | exact (DC (or_intror H)) | exact (NB H) | exact (NS H)].
  - exact LG'.
  - rewrite Hpk. lia.
  - lia.
  - exact PX'.
  - apply (nb_relist B L A Lam X P (Do ++ Y) Lc Ac L' A' mem' Lam' peak' (cntc + Z.of_nat c) (2 ^ 64 - 1) NBc
      (cr_entry_sub B API L A regs mem md PRE Lam peak cnt bnd X P Lc Ac memc mdc Lamc peakc cntc _ CRc) LG' PX').
    + exact (nb_P_kept B API SEG L A _ _ _ _ X P Lc Ac memc mdc L' A' mem' md' CS NBc HGX).
    + assert (INX : forall y, In y (D ++ Dw ++ Y) -> In y X)
        by (intros y Hy; exact (Permutation_in _ (Permutation_sym PX) Hy)).
      assert (IND : forall y, In y D -> In y X) by (intros y Hy; apply INX; apply in_or_app; left; exact Hy).
      assert (INO : forall y, In y Dold -> In y X).
      { intros y Hy. apply IND. apply (Permutation_in _ (Permutation_sym PD)). apply in_or_app. left. exact Hy. }
      intros d Hd. apply in_app_or in Hd as [Hd|Hd].
      * apply (Permutation_in _ PDo) in Hd. apply in_app_or in Hd as [Hd|[Hd|Hd]].
        -- destruct d as [a' k']. destruct (FRESH a' k' (in_or_app _ _ _ (or_introl Hd))) as [Hold|Hnew];
             [left; exact (INO _ Hold) | right; exact Hnew].
        -- subst d. destruct (FRESH a (Z.of_nat (length kname) + 1) ltac:(apply in_or_app; right; left; reflexivity))
             as [Hold|Hnew]; [left; exact (INO _ Hold) | right; exact Hnew].
        -- left. apply in_app_or in Hd as [Hd|Hd].
           ++ apply IND. apply (Permutation_in _ (Permutation_sym PD)). apply in_or_app. right. exact Hd.
           ++ apply INX. apply in_or_app. right. apply in_or_app. left. exact Hd.
      * left. apply INX. apply in_or_app. right. apply in_or_app. right. exact Hd.
  - rewrite <- BAT. exact RES'.
  - rewrite <- BAT. exact (hs_cap_le _ (Datatypes.S (Datatypes.S (Datatypes.S Nc)) -
      length (set_trace n cap (Z.of_nat (length kname)))) Nc CRT_SIZE ltac:(lia) ltac:(unfold CRT_SIZE; lia) HCr).
Qed.

Lemma st5_sec : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dv bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 63 <= cnt + CRT_ALLOCS -> (155 <= Nc)%nat ->
  Permutation X (Dv ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 192) (JObj []) [] ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 80) (JStr CRT_FMT2) Dv ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 352 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13d28 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 352 + 192) ->
  getr regsc 11 = Z_to_bv 64 0x1036e -> getr regsc 12 = Z_to_bv 64 (spZ regs - 352 + 80) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dv bs b kb CRc HC HN PX NO NV NS CSQ
    Hbo Hbl BB Hbin Hbk RFc R1 R10 R11 R12 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof ((PFX crt_nd) _ _ _ _ _ _ _ _ _ _ CRc) as NDX.
  pose proof CRc as ((_ & _ & _ & _ & RAc & _) & _).
  replace Nc with (S (S (S (Nc - 3)))) in CRc by lia.
  apply (w_set5 (PJSET fx) X [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc (Nc - 3)
    (spZ regs - 352 + 192) (spZ regs - 352 + 80) 0x1036e [] (JStr CRT_FMT2) [] Dv [(b1, k1); (q, kq)]
    (map (Z_to_bv 8) CRT_FORMAT) crt_sl5 post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11 R12).
  { lia. }
  { lia. }
  { lia. }
  { lia. }
  { right. lia. }
  { exact NO. }
  { exact NV. }
  { exact PX. }
  { cbn. lia. }
  { cbn. lia. }
  { cbn. lia. }
  { cbn. tauto. }
  { rewrite SEG. exact (crt_key5 memc RAc). }
  { exact crt_kz5. }
  { exact crt_ks5. }
  { intros i Hi. apply crt_key5_ro. rewrite crt_klen5, crt_sl5_len in Hi. lia. }
  { rewrite crt_klen5. unfold CRT_SIZE. lia. }
  { lia. }
  intros Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' Do RP R10' CR' HCN CS RDC NODE ZW.
  rewrite crt_zb5 in NODE. cbn [pj_set_model] in NODE.
  assert (HqX : In (q, kq) X) by exact ((PFX incl_perm_r) X Dv _ PX (q, kq) (or_intror (or_introl eq_refl))).
  assert (HqX' : In (q, kq) (Do ++ [(b1, k1); (q, kq)])) by (apply in_or_app; right; right; left; reflexivity).
  assert (HqD : ~ In (q, kq) Dv).
  { intros H. exact ((PFX perm_disj) X Dv _ (q, kq) (q, kq) NDX PX H (or_intror (or_introl eq_refl)) eq_refl). }
  assert (EO : forall D, (forall y, In y D -> ~ In y Dv) ->
     Eok regs X [(same, sn); (want, wn)] (Do ++ [(b1, k1); (q, kq)]) [(same, sn); (want, wn)]
       (spZ regs - 352 + 136) D (pj_set_writes (spZ regs - 352 + 192) (spZ regs - 352 + 80) [] Dv)).
  { intros D HD x [Hx|[Hx|[(a & k & Ha & Hax)|Hx]]].
    - right. left. split; lia.
    - right. left. split; lia.
    - right. right. left. exists a, k. split; [left; exact ((PFX incl_perm_l) X Dv _ PX _ Ha)|].
      split; [intros H; exact (HD _ H Ha) | exact Hax].
    - left. exact Hx. }
  assert (NS' : pj_node rsegs memc' (lin Lamc') (spZ regs - 352 + 136) (JObj []) []).
  { apply ((PFX cr_keep_node) X _ Lc Ac memc mdc Lamc peakc cntc _ (Do ++ [(b1, k1); (q, kq)]) _ Lc' Ac' memc' mdc'
      Lamc' peakc' cntc' (Nc - 3) _ _ _ _ (JObj []) [] CRc CR' CS NS (incl_nil_l _) (incl_nil_l _)).
    - lia.
    - exact (EO [] (fun y (H : In y []) => match H with end)).
    - intros a k []. }
  assert (CSQ' : pj_cstr rsegs memc' (lin Lamc') q kq (b64_enc bs)).
  { destruct CSQ as (Cq1 & Cq2 & Cq3 & Cq4).
    split; [exact (cr_in_lam B API L A regs mem md Lam peak cnt bnd _ _ _ _ _ _ _ _ _ _ q kq CR' HqX')|].
    split; [exact Cq2|]. split; [exact Cq3|].
    apply ((PFX cr_keep_bytes) X _ Lc Ac memc mdc Lamc peakc cntc _ (Do ++ [(b1, k1); (q, kq)]) _ Lc' Ac' memc' mdc'
      Lamc' peakc' cntc' (Nc - 3) _ _ _ (spZ regs - 352 + 136) q kq q _ CRc CR' CS HqX HqX').
    - apply EO. intros y [<-|[]]. exact HqD.
    - unfold freed. replace (q - 16 + 16) with q by lia. replace (kq + 16 - 16) with kq by lia. exact HqD.
    - exact Cq4.
    - lia.
    - rewrite length_map, length_app. cbn [length]. lia. }
  assert (BB' : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply ((PFX cr_keep_lam) X _ Lc Ac memc mdc Lamc peakc cntc _ (Do ++ [(b1, k1); (q, kq)]) _ Lc' Ac' memc' mdc'
      Lamc' peakc' cntc' (Nc - 3) _ _ _ (spZ regs - 352 + 136) [] b kb b (bz bs) CRc CR' CS).
    - exact (EO [] (fun y (H : In y []) => match H with end)).
    - unfold freed. replace (b - 16 + 16) with b by lia. replace (kb + 16 - 16) with kb by lia. intros Hb.
      destruct ((PFX cr_lam_x) X _ Lc Ac memc mdc Lamc peakc cntc _ b kb (b - 16) CRc Hbin ltac:(lia))
        as (_ & _ & _ & HX & _).
      exact (HX b kb ((PFX incl_perm_l) X Dv _ PX _ Hb) ltac:(lia)).
    - exact Hbin.
    - exact BB.
    - lia.
    - unfold bz. rewrite length_map. lia. }
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d28) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13d3c /\ getr R 10 = Z_to_bv 64 (spZ regs - 352 + 80) /\
       getr R 11 = Z_to_bv 64 0x102f8 /\ getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\
       getr R 20 = Z_to_bv 64 b /\ getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\
       getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14c64 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r6; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (H6 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM
    (Do ++ [(b1, k1); (q, kq)]) Lc' Ac' regs2 memc' mdc' Lamc' peakc' cntc' (Nc - 3)%nat same sn want wn q kq b1 k1 Do
    bs b kb CR' ltac:(unfold CRT_ALLOCS; lia) ltac:(lia) (Permutation_refl _) NODE NS' CSQ' Hbo Hbl BB' Hbin Hbk RF2
    Q1 Q10 Q11 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

End F5.
End ST5.

Lemma st5 : St6 -> St5.
Proof. intros H6 rc. exact (@st5_sec H6 rc). Qed.
