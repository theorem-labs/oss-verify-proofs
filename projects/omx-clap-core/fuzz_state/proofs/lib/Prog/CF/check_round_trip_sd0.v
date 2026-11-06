(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 556 of its 631 lines of code are new or changed and 671 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/past_nul.v, with its module names changed; 711 of its 786 lines of code are new or changed and 556 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_as_written.v, with its module names, addresses and numbers changed; 1716 of its 1784 lines of code are new or changed and 718 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_no_overread.v, with its module paths, module names and numbers changed; 1316 of its 1472 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_calls.v; 223 of its 404 lines of code are new or changed and 1291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_sd5.v, with its addresses and numbers changed; 160 of its 257 lines of code are new or changed and 307 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB check_round_trip_loops WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.

(* check_round_trip (check_4, plain, 0x138ac): stage 0, st0 : St1 -> St0 (check_round_trip_stdefs.v). From the entry
   of c0 = preset_base64_encode(body, len): the encoder through its wrapper w_enc (its text q holds b64_enc bs and
   becomes the one entry of X), the stretch crt_r1 (s0 = text, then the size (len + 2) / 3 * 4 + 1 of want) to the
   entry of c1 = malloc, then St1. The body and the input string are in blocks the encoder neither wrote nor freed;
   the slack after the input's NUL is read again in the encoder's memory (block_slack_present past the block). *)

(* The slack after a NUL at y - 1 up to the next 8-byte boundary stays below the 8-byte boundary after z >= y. *)
Lemma c0_sl_room : forall y z i, y <= z -> 0 <= i < (- y) mod 8 -> y + i < 8 * ((z + 7) / 8).
Proof. intros y z i Hyz Hi. Z.div_mod_to_equations. lia. Qed.

Lemma c0_bat_eqm : forall (m m' : word -> option byte) a bs, (forall x, m' x = m x) ->
  Mem.bytes_at rsegs m a bs -> Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs E (H0 & Hl & H). split; [exact H0|]. split; [exact Hl|].
  intros i Hi. unfold Mem.mrd. rewrite E. exact (H i Hi).
Qed.

#[local] Set Default Proof Using "All".

Section ST0.
Hypothesis HS1 : St1.
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

Section F0.
Context {fx : YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

(* c0: preset_base64_encode(body, len), then crt_r1 to malloc((len + 2) / 3 * 4 + 1) *)
Lemma st0_sec : forall Lc Ac regsc memc mdc Lamc peakc cntc Nc bs b kb t tb slack,
  CRs [] [] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 68 <= cnt + CRT_ALLOCS -> (160 <= Nc)%nat ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  Mem.bytes_at rsegs memc t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  b64_dec (zs tb) = Some bs ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x138f4 -> getr regsc 10 = Z_to_bv 64 b ->
  getr regsc 11 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 t ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PRESET_BASE64_ENCODE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros Lc Ac regsc memc mdc Lamc peakc cntc Nc bs b kb t tb slack CRc HC HN BOK HL BB Hbin Hbk TB NZ SLL HTB EX
    HDEC RFc R1 R10 R11 R19 R20 R21.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp0 & Hsp63 & Hsp16).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof PRE as (HM0 & _).
  pose proof CRc as (GIc & _).
  destruct EX as (pt & kt & Hpt & Hpt1 & Hpt2).
  destruct (crt_blk B API GF AX L A mem md pt kt 0 HM0 Hpt ltac:(lia)) as (Hp0 & _).
  destruct (crt_blk B API GF AX L A mem md pt kt (kt - 1) HM0 Hpt ltac:(lia)) as (Hpk & _).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ b kb HM0 LG0 Hbin) as (Hb1 & Hb2 & _).
  pose proof (LG0_blk B L A mem Lam peak cnt LG0 b kb Hbin) as Hbblk.
  assert (Hek : 0 <= enc_size (Z.of_nat (length bs))) by (unfold enc_size; Z.div_mod_to_equations; lia).
  replace Nc with (S (Nc - 1)) in CRc by lia.
  apply (w_enc B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (ENC fx) [] [] Lc Ac regsc memc mdc
    Lamc peakc cntc (Nc - 1) b (Z.of_nat (length bs)) bs post CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11).
  { lia. }
  { lia. }
  { exact BOK. }
  { reflexivity. }
  { lia. }
  { intros i Hi. pose proof BB as (_ & _ & HB).
    rewrite SEG. replace (b + i) with (b + Z.of_nat (Z.to_nat i)) by lia.
    change (mbyte rsegs memc (b + Z.of_nat (Z.to_nat i)))
      with (Mem.mrd rsegs memc (Mem.wa (b + Z.of_nat (Z.to_nat i)))).
    rewrite (HB (Z.to_nat i) ltac:(unfold bz; rewrite length_map; lia)).
    unfold bz. rewrite nth_error_map, (nth_error_nth' bs 0) by lia. reflexivity. }
  { right. left. exists (b - 16), (kb + 16).
    split; [exact (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc _ _ GIc Hbblk) | lia]. }
  { lia. }
  { unfold enc_size, CRT_SIZE. Z.div_mod_to_equations. lia. }
  intros Lc' Ac' regs' memc' mdc' q RP R10' Hq0 Hq16 HQ CR' CS TX.
  rewrite SEG in TX.
  pose proof CS as (HM' & _).
  pose proof CR' as (GI' & (_ & _ & NE') & _).
  pose proof GI' as (_ & _ & _ & _ & RA' & _).
  assert (NQ : ~ In (q - 16, enc_size (Z.of_nat (length bs)) + 16) (blocks L A)).
  { apply NE'. left. reflexivity. }
  destruct ((PFX cr_x_lo) _ _ _ _ _ _ _ _ _ _ q (enc_size (Z.of_nat (length bs))) CR' (or_introl eq_refl))
    as (Hq1 & Hq2 & _).
  (* the encoder wrote no byte of a block of the caller *)
  assert (NOE : forall p n x, In (p, n) (blocks L A) -> p <= x < p + n ->
    ~ enc_writes q (enc_size (Z.of_nat (length bs))) x).
  { intros p n x Hp Hx Ex.
    destruct (crt_blk B API GF AX L A mem md p n (x - p) HM0 Hp ltac:(lia)) as (_ & _ & _ & NS).
    replace (p + (x - p)) with x in NS by lia.
    destruct (crt_blk B API GF AX L A mem md p n 0 HM0 Hp ltac:(lia)) as (Hpz & _).
    pose proof (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc p n GIc Hp) as Hpc.
    assert (G1 : (p, n) <> (0, 0)) by (intros E; injection E as E1 _; lia).
    destruct (cs_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ p n CS Hpc G1) as [Hpc' _].
    assert (HNE : (p, n) <> (q - 16, enc_size (Z.of_nat (length bs)) + 16))
      by (intros E; apply NQ; rewrite <- E; exact Hp).
    unfold enc_writes, alloc_writes in Ex.
    destruct Ex as [[Ex|(_ & Ex)]|(_ & Ex)]; [exact (NS Ex)| |];
      exact (crt_blk_disj B API Lc' Ac' memc' mdc' p n (q - 16) (enc_size (Z.of_nat (length bs)) + 16) x HM' Hpc'
        HQ HNE Hx ltac:(lia)). }
  assert (KEEP : forall p n y l, In (p, n) (blocks L A) -> 0 < n -> Mem.bytes_at rsegs memc y l -> p <= y ->
    y + Z.of_nat (length l) <= p + n -> Mem.bytes_at rsegs memc' y l).
  { intros p n y l Hp Hn BS Hy1 Hy2.
    pose proof (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc p n GIc Hp) as Hpc.
    destruct (crt_blk B API GF AX L A mem md p n 0 HM0 Hp ltac:(lia)) as (Hpz & _).
    assert (G1 : (p, n) <> (0, 0)) by (intros E; injection E as E1 _; lia).
    apply (cs_bytes_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ p n y l CS Hpc G1 BS Hy1 Hy2).
    intros i Hi. apply (NOE p n i Hp). lia. }
  (* the body across the encoder *)
  assert (BB' : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply (KEEP (b - 16) (kb + 16) b (bz bs) Hbblk ltac:(lia) BB ltac:(lia)). unfold bz. rewrite length_map. lia. }
  (* the input's string across the encoder, then its slack read again in the encoder's memory *)
  pose proof TB as TB0.
  replace (tb ++ Z_to_bv 8 0 :: slack) with ((tb ++ [Z_to_bv 8 0]) ++ slack) in TB0
    by (rewrite <- app_assoc; reflexivity).
  apply Mem.bytes_at_app in TB0 as [TB1 _].
  assert (TB1' : Mem.bytes_at rsegs memc' t (tb ++ [Z_to_bv 8 0])).
  { apply (KEEP pt kt t _ Hpt ltac:(lia) TB1 Hpt1). rewrite length_app. cbn [length]. lia. }
  pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length tb) + 1)) 8 ltac:(lia)) as Hr.
  pose proof (gi_entry_blk B API L A regs mem md PRE Lc Ac memc mdc pt kt GIc Hpt) as Hptc.
  assert (G1 : (pt, kt) <> (0, 0)) by (intros E; injection E as E1 _; lia).
  destruct (cs_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ pt kt CS Hptc G1) as [Hptc' KB].
  destruct ((PFX crt_mk_bytes) rsegs memc' (t + Z.of_nat (length tb) + 1)
    (Z.to_nat ((- (t + Z.of_nat (length tb) + 1)) mod 8)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia))
    as (sl & Hsl & BS2).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia.
    destruct (Z_lt_le_dec (t + Z.of_nat (length tb) + 1 + i) (pt + kt)) as [Hx|Hx].
    - assert (Hs : mbyte rsegs memc' (t + Z.of_nat (length tb) + 1 + i) <> None).
      { rewrite (KB (t + Z.of_nat (length tb) + 1 + i) ltac:(lia)
          (NOE pt kt (t + Z.of_nat (length tb) + 1 + i) Hpt ltac:(lia))).
        replace (t + Z.of_nat (length tb) + 1 + i) with (t + (Z.of_nat (length tb) + 1 + i)) by lia.
        exact (crt_bytes_some memc t _ (Z.of_nat (length tb) + 1 + i) TB
          ltac:(rewrite length_app; cbn [length]; lia)). }
      destruct (mbyte rsegs memc' (t + Z.of_nat (length tb) + 1 + i)) as [v|] eqn:Ev; [|contradiction].
      exists v. exact Ev.
    - destruct (BSP Lc' Ac' memc' mdc' pt kt (t + Z.of_nat (length tb) + 1 + i) HM' Hptc') as [v Hv].
      { split; [lia|]. apply c0_sl_room; lia. }
      exists v. unfold Mem.mrd, Mem.wa. rewrite Hv. reflexivity. }
  assert (TB' : Mem.bytes_at rsegs memc' t (tb ++ Z_to_bv 8 0 :: sl)).
  { replace (tb ++ Z_to_bv 8 0 :: sl) with ((tb ++ [Z_to_bv 8 0]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply Mem.bytes_at_app. split; [exact TB1'|]. rewrite length_app. cbn [length].
    replace (t + Z.of_nat (length tb + 1)) with (t + Z.of_nat (length tb) + 1) by lia. exact BS2. }
  (* the encoder's text *)
  assert (CSQ : pj_cstr rsegs memc' (lin ((q, enc_size (Z.of_nat (length bs))) :: Lamc)) q
      (enc_size (Z.of_nat (length bs))) (b64_enc bs)).
  { pose proof (check_round_trip_loops.enc_len_Z bs) as EL.
    split; [exact (or_introl eq_refl)|].
    split; [unfold enc_size; lia|].
    split.
    - eapply Forall_impl; [|exact (WriterSpecFacts.b64_enc_chars bs BOK)]. intros c Hc. cbv beta in *. lia.
    - split; [lia|]. split; [rewrite length_map, length_app; cbn [length]; unfold enc_size in *; lia|].
      intros i Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi.
      pose proof (TX (Z.of_nat i) ltac:(unfold enc_size; lia)) as E. rewrite Nat2Z.id in E. exact E. }
  (* crt_r1: s0 = text, a0 = (len + 2) / 3 * 4 + 1, s6 = (len + 2) / 3 * 4, then malloc *)
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x138f4) memc' mdc'
    (fun R pc' m' => exists m0, (RFs R /\ getr R 1 = Z_to_bv 64 0x13918 /\
       getr R 10 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4 + 1) /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\ getr R 21 = Z_to_bv 64 t /\
       getr R 22 = Z_to_bv 64 ((Z.of_nat (length bs) + 2) / 3 * 4) /\ getr R 8 = Z_to_bv 64 q /\
       pc' = Z_to_bv 64 0x16594 /\ munch [] (normalize rsegs memc') m0) /\
       mem_rel rsegs m' m0 /\ ro_same rsegs memc' m')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21.
    apply (PFX crt_evn); [exact RA'|].
    eapply Exec.evt_mono.
    - eapply crt_r1 with (l := Z.of_nat (length bs)).
      + reflexivity.
      + lia.
      + apply mem_inv_normalize.
    - intros ms' (a1' & ->).
      do 3 eexists. split; [reflexivity|].
      split; [apply ((PFX RF_mk) regs'); [exact RF' | reflexivity ..]|].
      repeat (split; [first [reflexivity | apply (PFX crt_spo); lia]|]).
      apply munch_refl. }
  intros RR pc2 mem2 regs2 (m0 & (RF2 & Q1 & Q10 & Q19 & Q20 & Q21 & Q22 & Q8 & -> & MU) & HR & ROS) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q19, Q20, Q21, Q22, Q8.
  assert (EQ : forall x, mem2 x = memc' x).
  { apply (mem_unchanged_rel rsegs memc' (normalize rsegs memc') mem2 m0 (mem_rel_normalize rsegs memc' RA') HR ROS).
    intros x. apply MU. exact I. }
  pose proof ((PFX cr_eqm) _ _ _ _ _ _ _ _ _ _ mem2 CR' EQ) as CR2.
  assert (CSQ2 : pj_cstr rsegs mem2 (lin ((q, enc_size (Z.of_nat (length bs))) :: Lamc)) q
      (enc_size (Z.of_nat (length bs))) (b64_enc bs)).
  { destruct CSQ as (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    exact (c0_bat_eqm memc' mem2 q _ EQ C4). }
  pose proof (c0_bat_eqm memc' mem2 b _ EQ BB') as BB2.
  pose proof (c0_bat_eqm memc' mem2 t _ EQ TB') as TB2.
  exact (HS1 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM Lc' Ac' regs2 mem2
    mdc' ((q, enc_size (Z.of_nat (length bs))) :: Lamc) _ (cntc + 1) (Nc - 1)%nat q (enc_size (Z.of_nat (length bs)))
    bs b kb t tb sl CR2 ltac:(unfold CRT_ALLOCS; lia) ltac:(lia) CSQ2 BOK HL BB2 Hbin Hbk TB2 NZ
    ltac:(rewrite Hsl, Z2Nat.id by lia; lia) HTB (ex_intro _ pt (ex_intro _ kt (conj Hpt (conj Hpt1 Hpt2)))) HDEC
    RF2 Q1 Q10 Q19 Q20 Q21 Q22 Q8).
Qed.

End F0.
End ST0.

Lemma st0 : St1 -> St0.
Proof. intros HS1 rc. exact (@st0_sec HS1 rc). Qed.
