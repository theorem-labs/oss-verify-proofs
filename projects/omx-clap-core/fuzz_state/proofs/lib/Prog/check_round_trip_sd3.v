(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths, module names, addresses and numbers changed; 1718 of its 1786 lines of code are new or changed and 723 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread.v, with its module paths, module names and numbers changed; 1312 of its 1471 lines of code are new or changed and 1627 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_calls.v; 242 of its 427 lines of code are new or changed and 1286 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_sd7.v, with its addresses and numbers changed; 215 of its 320 lines of code are new or changed and 322 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger LedgerFacts KindBGlue HState HStateRoom
  ReaderRes WriterSpec fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c
  PjStruct pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue
  put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import check_round_trip_c check_round_trip_glue
  check_round_trip_runs check_round_trip_calls check_round_trip_stages_a check_round_trip_stages_b
  check_round_trip_st8 check_round_trip_stdefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB past_nul check_round_trip_loops
  WriterSpecFacts.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c
  pj_get_c pj_get_str_c.

(* check_round_trip (check_4, plain, 0x138ac): stage 3, st3 : St4 -> St3 (check_round_trip_stdefs.v). From the entry
   of c3 = preset_base64_decode(text, &n) (text = q, n at sp+8): the decoder through its wrapper w_dec (the text is
   b64_enc bs, so the decoded bytes are bs), the stretch crt_r4 (the comparison of back with the body, then
   pj_object(&doc) and pj_object(&state)) to the entry of c4 = pj_string(&v, PRESET_FORMAT_STATE), then St4. *)

(* Bounds on the encoder's text and the decoder's block for a body of at most 9 * 2 ^ 18 bytes. *)
Lemma c3_enc_len : forall bs : list Z, Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Z.of_nat (length (b64_enc bs)) <= 3 * 2 ^ 20 + 4.
Proof. intros bs H. rewrite check_round_trip_loops.enc_len_Z. Z.div_mod_to_equations. lia. Qed.

Lemma c3_dec_sz : forall tb : list Z, Z.of_nat (length tb) <= 3 * 2 ^ 20 + 4 -> dec_size tb + 16 <= CRT_SIZE.
Proof. intros tb H. unfold dec_size, CRT_SIZE. Z.div_mod_to_equations. lia. Qed.

Lemma c3_stk_sub : forall m lo hi lo' hi', Frame.stk rsegs m lo hi -> lo <= lo' -> hi' <= hi ->
  Frame.stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H0 & H1 & H) Hl Hh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma c3_stk_wr : forall m lo hi a n, Frame.stk rsegs m lo hi -> lo <= a -> a + n <= hi -> Mem.wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Hl Hh. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (H (a + i)) as [Hw _]; [lia | exact Hw].
Qed.

(* The node pj_object writes (crt_obj: type 6, every other field zero) is the empty object. *)
Lemma c3_obj_u64 : forall m p off, Mem.bytes_at rsegs m p crt_obj -> 8 <= off <= 48 -> pj_u64 rsegs m (p + off) 0.
Proof.
  intros m p off (H1 & H2 & H) Ho.
  assert (LC : length crt_obj = 56%nat)
    by (unfold crt_obj; rewrite length_app, Mem.length_le4, repeat_length; reflexivity).
  assert (NC : forall i, (4 <= i < 56)%nat -> nth_error crt_obj i = Some (Z_to_bv 8 0)).
  { intros i Hi. unfold crt_obj. rewrite nth_error_app2 by (rewrite Mem.length_le4; lia).
    rewrite Mem.length_le4. apply pj_nth_repeat. lia. }
  rewrite LC in H2, H.
  split; [lia|]. rewrite pj_le8_0.
  split; [lia|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi.
  replace (p + off + Z.of_nat i) with (p + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite H by lia. rewrite NC by lia. rewrite pj_nth_repeat by lia. reflexivity.
Qed.

Lemma c3_obj_node : forall m lblk p, pj_rw rsegs m p -> Mem.bytes_at rsegs m p crt_obj ->
  pj_node rsegs m lblk p (JObj []) [].
Proof.
  intros m lblk p Hrw HB.
  assert (H4 : Mem.bytes_at rsegs m p (Mem.le4 (Z_to_bv 64 6))).
  { pose proof HB as HB'. unfold crt_obj in HB'. apply Mem.bytes_at_app in HB'. exact (proj1 HB'). }
  cbn [pj_node].
  split; [constructor|]. split; [intros b x Hb; destruct Hb|].
  exists 0, 0, 0, 0, 0, 0. split.
  - cbn [tag]. split; [exact Hrw|].
    split; [split; [lia | exact H4]|].
    split; [apply c3_obj_u64; [exact HB | lia]|].
    split; [apply c3_obj_u64; [exact HB | lia]|].
    split; [apply c3_obj_u64; [exact HB | lia]|].
    split; [apply c3_obj_u64; [exact HB | lia]|].
    split; [apply c3_obj_u64; [exact HB | lia]|].
    apply c3_obj_u64; [exact HB | lia].
  - split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    split; [left; split; [reflexivity | split; reflexivity]|].
    exists []. split; [reflexivity | exact eq_refl].
Qed.

#[local] Set Default Proof Using "All".

Section ST.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis MAL : ms_malloc B = 0x16594.
Hypothesis FRE : ms_free B = 0x16454.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
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
Hypothesis PRE : call_pre_k B (aa_MR API) CRT_STK L A regs mem md.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound).
Hypothesis LG0 : ledger B L A mem Lam peak cnt (2 ^ 64 - 1).
Hypothesis HCNT : cnt + CRT_ALLOCS < 2 ^ 63.
Hypothesis RSP : spZ regs <= 2 ^ 47.
Hypothesis RGT : strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK.
Variable fx0 : YK11.FPState.

Local Notation CRs := (CR B API L A regs mem md Lam peak cnt bnd).
Local Notation post := (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
(* A lemma of check_round_trip_stages_a.v or check_round_trip_stages_b.v at this section's variables. *)
Local Notation PFX f := (f B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC
  FREE FFREE ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0) (only parsing).
(* The frame bytes crt_r4 writes: bcmp's and pj_object's stack below sp, the word at sp+16, the state and the doc. *)
Local Notation W4 := [(spZ regs - 336 - 16, spZ regs - 336); (spZ regs - 336 + 16, spZ regs - 336 + 24);
  (spZ regs - 336 + 136, spZ regs - 336 + 248)] (only parsing).

Ltac retok R1 := rewrite R1; vm_compute; reflexivity.
Ltac kbr HM := first [ exact (proj1 (kb_md B API _ _ _ _ HM)) | exact (proj2 (kb_md B API _ _ _ _ HM)) ].
Ltac sv RP R' H E n :=
  lazymatch type of H with getr _ ?k = ?v =>
    assert (E : getr R' k = v) by (rewrite <- H; exact (RP n ltac:(unfold callee_saved; lia))) end.

(* The whole frame is readable and writable at a call or return point. *)
Lemma c3_fstk : forall X P Lc Ac memc mdc Lamc pk cn Nc, CRs X P Lc Ac memc mdc Lamc pk cn Nc ->
  Frame.stk rsegs memc (spZ regs - CRT_STK) (spZ regs).
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc (((_ & _ & _ & _ & _ & _ & _ & _ & S) & _) & _).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp1 & Hsp2 & _). pose proof alloc_ceiling_val as Hacv.
  split; [unfold CRT_STK, ALLOC_STACK; lia|]. split; [lia|]. intros a Ha.
  assert (W : writable_at (ms_segs B) memc a) by (apply S; left; lia).
  rewrite SEG in W. unfold writable_at in W. split; [exact W | exact (past_nul.pn_rd memc _ W)].
Qed.

Lemma c3_w : forall x, ~ outside W4 x -> spZ regs - CRT_STK <= x < spZ regs - 88.
Proof.
  intros x Hx. cbn [outside] in Hx. unfold CRT_STK, ALLOC_STACK.
  destruct (Z_lt_le_dec x (spZ regs - 336 - 16)) as [H1|H1].
  { exfalso. apply Hx. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  destruct (Z_lt_le_dec x (spZ regs - 336 + 248)) as [H2|H2]; [lia|].
  exfalso. apply Hx. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* Bytes below the allocation ceiling across crt_r4. *)
Lemma c3_keep_lo : forall m m' y bs, Mem.bytes_at rsegs m y bs -> y + Z.of_nat (length bs) <= alloc_ceiling ->
  munch W4 m m' -> Mem.bytes_at rsegs m' y bs.
Proof.
  intros m m' y bs BS Hy MU.
  pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3). pose proof alloc_ceiling_val as Hacv.
  pose proof BS as (H0 & _).
  apply (crt_bytes_keep m m' y bs BS). intros i Hi.
  apply (mbyte_munch rsegs _ m m' i MU); [lia|]. cbn [outside].
  split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Section F3.
Context {fx : YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

(* c3: preset_base64_decode(text, &n), then crt_r4 to pj_string(&v, PRESET_FORMAT_STATE) *)
Lemma st3s : St4 ->
  forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq bs b kb,
  CRs [(q, kq)] [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 65 <= cnt + CRT_ALLOCS -> (157 <= Nc)%nat ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13b64 -> getr regsc 10 = Z_to_bv 64 q ->
  getr regsc 11 = Z_to_bv 64 (spZ regs - 336 + 8) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same ->
  0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PRESET_BASE64_DECODE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros H4 Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq bs b kb CRc HC HN CSQ BOK HL BB Hbin Hbk
    RFc R1 R10 R11 R19 R20 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp0 & Hsp63 & Hsp16).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt.
  assert (HK : CRT_STK = 14336) by reflexivity.
  pose proof (c3_enc_len bs HL) as ELB.
  assert (CRc' : CRs [(q, kq)] [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc (S (Nc - 1))).
  { replace (S (Nc - 1)) with Nc by lia. exact CRc. }
  pose proof CSQ as (Hqin & Hqk & HF & HQB).
  pose proof PRE as (HM0 & _).
  destruct ((PFX crt_slack) _ _ _ _ _ _ _ _ _ _ q kq (b64_enc bs) CRc Hqin Hqk HQB) as (slack & TB & SLL).
  destruct ((PFX cr_x_lo) _ _ _ _ _ _ _ _ _ _ q kq CRc (or_introl eq_refl)) as (Hq1 & Hq2 & _).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ b kb HM0 LG0 Hbin) as (Hb1 & Hb2 & _).
  apply (w_dec B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (DEC fx) [(q, kq)]
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc (Nc - 1) q (spZ regs - 336 + 8) (b64_enc bs) slack
    bs post CRc' R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11).
  { unfold no_zero. eapply Forall_impl; [|exact HF]. intros c Hc. cbv beta in *. lia. }
  { unfold bytes_ok. eapply Forall_impl; [|exact HF]. intros c Hc. cbv beta in *. lia. }
  { lia. }
  { rewrite SEG. exact TB. }
  { lia. }
  { right. right. left. exists q, kq. split; [exact Hqin | lia]. }
  { lia. }
  { lia. }
  { lia. }
  { right. lia. }
  { exact (WriterSpecFacts.b64_dec_enc bs BOK). }
  { lia. }
  { exact (c3_dec_sz _ ELB). }
  intros Lc' Ac' regs' memc' mdc' g RP RG10 Hg0 Hg16 Hgb CR' CS BG BL.
  rewrite SEG in BG, BL.
  assert (Hds : 0 <= dec_size (b64_enc bs)) by (unfold dec_size; lia).
  pose proof ((PFX crt_nd) _ _ _ _ _ _ _ _ _ _ CR') as NDg. apply NoDup_cons_iff in NDg as [NG _].
  assert (EO : forall p D, incl D [(q, kq)] -> spZ regs - 336 + 16 <= p ->
    Eok regs [(q, kq)] [(same, sn); (want, wn)] ((g, dec_size (b64_enc bs)) :: [(q, kq)]) [(same, sn); (want, wn)]
      p D (dec_writes g (dec_size (b64_enc bs)) (spZ regs - 336 + 8))).
  { intros p D HI Hp x [Hx|[(_ & Hx)|Hx]].
    - left. exact Hx.
    - right. right. left. exists g, (dec_size (b64_enc bs)). split; [right; left; reflexivity|].
      split; [|exact Hx]. intros H. exact (NG (HI _ H)).
    - right. left. split; lia. }
  assert (GQ : ~ ((q - 16, kq + 16) = (0, 0))) by (intros E; injection E as E1 _; lia).
  assert (GB : ~ ((b - 16, kb + 16) = (0, 0))) by (intros E; injection E as E1 _; lia).
  (* the text and the body across the decoder *)
  assert (CSQ' : pj_cstr rsegs memc' (lin ((g, dec_size (b64_enc bs)) :: Lamc)) q kq (b64_enc bs)).
  { split; [exact (in_cons (g, dec_size (b64_enc bs)) (q, kq) Lamc Hqin)|]. split; [exact Hqk|]. split; [exact HF|].
    apply ((PFX cr_keep_bytes) [(q, kq)] _ Lc Ac memc mdc Lamc peakc cntc _ ((g, dec_size (b64_enc bs)) :: [(q, kq)])
      _ Lc' Ac' memc' mdc' _ _ _ _ _ _ _ (spZ regs - 336 + 192) q kq q _ CRc' CR' CS (or_introl eq_refl)
      (or_intror (or_introl eq_refl)) (EO (spZ regs - 336 + 192) [(q, kq)] (incl_refl _) ltac:(lia)) GQ HQB).
    - lia.
    - rewrite length_map, length_app. cbn [length]. lia. }
  assert (BB1 : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply ((PFX cr_keep_lam) [(q, kq)] _ Lc Ac memc mdc Lamc peakc cntc _ ((g, dec_size (b64_enc bs)) :: [(q, kq)]) _
      Lc' Ac' memc' mdc' _ _ _ _ _ _ _ (spZ regs - 336 + 192) [] b kb b (bz bs) CRc' CR' CS
      (EO (spZ regs - 336 + 192) [] (fun y (H : In y []) => match H with end) ltac:(lia)) GB Hbin BB ltac:(lia)).
    unfold bz. rewrite length_map. lia. }
  (* crt_r4: bcmp(back, body, len), pj_object(&doc), pj_object(&state), then a0 = &v, a1 = "format", pj_string *)
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as (GI' & _). pose proof GI' as ((HM' & _) & _ & _ & _ & RA' & _).
  destruct ((PFX cr_x_lo) _ _ _ _ _ _ _ _ _ _ g (dec_size (b64_enc bs)) CR' (or_introl eq_refl)) as (Hg1 & Hg2 & _).
  pose proof (c3_fstk _ _ _ _ _ _ _ _ _ _ CR') as STK'.
  pose proof ((PFX stk_normalize) memc' (spZ regs - CRT_STK) (spZ regs) RA' STK' ltac:(lia)) as STKN.
  assert (HJ : exists j16 : list byte, length j16 = 8%nat /\
    Mem.bytes_at rsegs (normalize rsegs memc') (spZ regs - 336 + 16) j16).
  { apply (PFX crt_mk_bytes); [lia | lia |]. intros i Hi. destruct STKN as (_ & _ & SK).
    destruct (SK (spZ regs - 336 + 16 + i)) as [_ Hr]; [lia | exact Hr]. }
  destruct HJ as (j16 & Hj16 & BJ).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13b64) memc' mdc'
    (fun R pc' m' => exists m0, (RF regs R /\ getr R 1 = Z_to_bv 64 0x13bb0 /\
       getr R 10 = Z_to_bv 64 (spZ regs - 336 + 80) /\ getr R 11 = Z_to_bv 64 0x1037a /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\ getr R 21 = Z_to_bv 64 g /\
       getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\
       pc' = Z_to_bv 64 0x14890 /\ munch W4 (normalize rsegs memc') m0 /\ wmono rsegs (normalize rsegs memc') m0 /\
       Mem.bytes_at rsegs m0 (spZ regs - 336 + 136) crt_obj /\ Mem.bytes_at rsegs m0 (spZ regs - 336 + 192) crt_obj) /\
       mem_rel rsegs m' m0 /\ ro_same rsegs memc' m')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, RG10, S19, S20, S8, S9, S18.
    apply (PFX crt_evn); [exact RA'|].
    eapply Exec.evt_mono.
    - eapply (crt_r4 BCMP PJO) with (back := g) (b := b) (l := Z.of_nat (length bs)) (lo := spZ regs - CRT_STK)
        (db := bz bs) (j16 := j16).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + lia.
      + lia.
      + lia.
      + unfold bz. rewrite length_map. reflexivity.
      + apply bytes_at_normalize; [exact RA' | exact BG].
      + apply bytes_at_normalize; [exact RA' | exact BB1].
      + rewrite MState.unsigned_lit by lia. split.
        * split; [cbn [cells_wf cell_wf]; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
          apply Mem.bytes_at_app. split.
          -- apply bytes_at_normalize; [exact RA' | exact BL].
          -- rewrite Mem.length_le8. replace (spZ regs - 336 + 8 + Z.of_nat 8) with (spZ regs - 336 + 16) by lia.
             exact BJ.
        * apply (c3_stk_wr _ _ _ _ _ STKN); cbn [cells_size csize]; lia.
      + rewrite MState.unsigned_lit by lia. apply (c3_stk_wr _ _ _ _ _ STKN); lia.
      + rewrite MState.unsigned_lit by lia. apply (c3_stk_wr _ _ _ _ _ STKN); lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia. apply (c3_stk_sub _ _ _ _ _ STKN); lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + apply mem_inv_normalize.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & m1 & -> & MU & WM & _ & _ &
        OB1 & OB2).
      rewrite MState.unsigned_lit in MU, OB1, OB2 by lia.
      do 3 eexists. split; [reflexivity|].
      split; [apply ((PFX RF_mk) regs'); [exact RF' | reflexivity ..]|].
      repeat (split; [first [reflexivity | apply (PFX crt_spo); lia]|]).
      split; [exact MU|]. split; [exact WM|]. split; [exact OB1 | exact OB2]. }
  intros RR pc2 mem2 regs2 (m0 & (RF2 & Q1 & Q10 & Q11 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & MU & WM & OB1 & OB2) &
    HR & ROS) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q19, Q20, Q21, Q8, Q9, Q18.
  pose proof (mem_rel_normalize rsegs memc' RA') as HR0.
  pose proof (munch_rel rsegs _ memc' (normalize rsegs memc') mem2 m0 HR0 HR ROS MU) as MU2.
  pose proof (wmono_rel rsegs memc' (normalize rsegs memc') mem2 m0 HR0 HR ROS WM) as WM2.
  pose proof (ro_agree_same rsegs memc' mem2 RA' ROS) as RA2.
  pose proof ((PFX cr_munch) _ _ _ _ _ _ _ _ _ _ _ mem2 CR' MU2 WM2 RA2 c3_w) as CR2.
  (* the text, the body and the two empty objects in the memory after crt_r4 *)
  assert (CSQ2 : pj_cstr rsegs mem2 (lin ((g, dec_size (b64_enc bs)) :: Lamc)) q kq (b64_enc bs)).
  { destruct CSQ' as (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    apply (c3_keep_lo memc' mem2 q _ C4); [|exact MU2]. rewrite length_map, length_app. cbn [length]. lia. }
  assert (BB2 : Mem.bytes_at rsegs mem2 b (bz bs)).
  { apply (c3_keep_lo memc' mem2 b _ BB1); [|exact MU2]. unfold bz. rewrite length_map. lia. }
  pose proof (c3_fstk _ _ _ _ _ _ _ _ _ _ CR2) as STK2.
  assert (NS2 : pj_node rsegs mem2 (lin ((g, dec_size (b64_enc bs)) :: Lamc)) (spZ regs - 336 + 136) (JObj []) []).
  { apply c3_obj_node; [split; [lia | apply (c3_stk_sub _ _ _ _ _ STK2); lia] |].
    exact (proj2 (bytes_at_rel rsegs mem2 m0 _ _ HR) OB1). }
  assert (ND2 : pj_node rsegs mem2 (lin ((g, dec_size (b64_enc bs)) :: Lamc)) (spZ regs - 336 + 192) (JObj []) []).
  { apply c3_obj_node; [split; [lia | apply (c3_stk_sub _ _ _ _ _ STK2); lia] |].
    exact (proj2 (bytes_at_rel rsegs mem2 m0 _ _ HR) OB2). }
  exact (H4 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE ENC
    DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM Lc' Ac' regs2 mem2 mdc'
    ((g, dec_size (b64_enc bs)) :: Lamc) _ (cntc + 1) (Nc - 1)%nat same sn want wn q kq g (dec_size (b64_enc bs)) bs b
    kb CR2 ltac:(lia) ltac:(lia) ND2 NS2 CSQ2 BOK HL BB2 Hbin Hbk RF2 Q1 Q10 Q11 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

End F3.
End ST.

Lemma st3 : St4 -> St3.
Proof.
  intros H4 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM.
  exact (@st3s rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM H4).
Qed.
