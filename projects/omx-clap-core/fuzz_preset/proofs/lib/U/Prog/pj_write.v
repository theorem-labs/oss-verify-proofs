(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module names changed; 701 of its 749 lines of code are new or changed and 691 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract AllocSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require PropExec Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import MState Mem Exec Frame Cells Regs6ss RegisterBridge FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger put_c put_kb WriterRet WriterCall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import snprintf_c write_value_c fuzz_free_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import put_blocks pj_write_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require put_string_c indent_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pjw_resume : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {x : machine_state} {regs1 : bvmap 5 word},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31) F pc fc rv m ro) x ->
  regs_preserved (ms_regs x) regs1 ->
  mkR_of regs1 = mkR (reg_get regs1 1) x2 x3 x4 (reg_get regs1 5) (reg_get regs1 6) (reg_get regs1 7) x8 x9
    (reg_get regs1 10) (reg_get regs1 11) (reg_get regs1 12) (reg_get regs1 13) (reg_get regs1 14) (reg_get regs1 15)
    (reg_get regs1 16) (reg_get regs1 17) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    (reg_get regs1 28) (reg_get regs1 29) (reg_get regs1 30) (reg_get regs1 31).
Proof. intros * HE RP. rewrite (resume_regs _ _ _ _ _ _ _ _ _ HE RP). reflexivity. Qed.

Lemma pjw_put1_text : forall st bs, w_failed (put1 st bs) = 0 -> w_text (put1 st bs) = w_text st ++ bs.
Proof.
  intros [f tx c n fl cs] bs. unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls].
  destruct (Z.eqb_spec f 0) as [->|Hf]; cbn [negb].
  - destruct (Z.of_nat (length tx) + Z.of_nat (length bs) + 1 <=? c); [intros _; reflexivity|].
    destruct (n =? fl); [intros H; cbn in H; discriminate H | intros _; reflexivity].
  - intros H. cbn in H. exfalso. exact (Hf H).
Qed.

Lemma pjw_text_ok : forall P st, w_failed (putN st P) = 0 -> w_text (putN st P) = w_text st ++ concat P.
Proof.
  induction P as [|bs P IH]; intros st H.
  - rewrite putN_nil. cbn [concat]. rewrite app_nil_r. reflexivity.
  - rewrite putN_cons in *.
    destruct (Z.eq_dec (w_failed (put1 st bs)) 0) as [H0|H0].
    + rewrite (IH _ H), (pjw_put1_text _ _ H0). cbn [concat]. rewrite app_assoc. reflexivity.
    + rewrite putN_failed in H by exact H0. contradiction.
Qed.

Lemma pjw_w0_cap : forall P cnt fail, w_failed (putN (w0 cnt fail) P) = 0 -> P <> [] ->
  w_cap (putN (w0 cnt fail) P) <> 0.
Proof.
  intros [|bs P] cnt fail HF HP; [exfalso; exact (HP eq_refl)|].
  rewrite putN_cons in *. unfold w0 in *.
  destruct (Z.eq_dec cnt fail) as [E|E].
  - rewrite put1_starve in HF by (cbn [length]; lia). rewrite putN_failed in HF by (cbn [w_failed]; lia).
    cbn [w_failed] in HF. lia.
  - assert (C1 : 4096 <= w_cap (put1 (mkW 0 [] 0 cnt fail []) bs)).
    { rewrite put1_grow by (cbn [length]; lia). cbn [w_cap]. unfold newcap. cbn [Z.eqb].
      apply dbl_ge. lia. }
    pose proof (putN_cap P (put1 (mkW 0 [] 0 cnt fail []) bs) ltac:(lia)) as C2. lia.
Qed.

Lemma pjw_dpieces_ne : forall t p, wdpieces t p <> [].
Proof. intros t p. unfold wdpieces. destruct t; cbn [wvpieces]; try unfold spieces; cbn [app]; discriminate. Qed.

Lemma pjw_bytes_nl : bytes_ok [10].
Proof. unfold bytes_ok. repeat constructor; lia. Qed.

Lemma pjw_img_nl : img_ok STR_NL [10] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pjw_seg_nl : existsb (fun sg => (bv_unsigned (fst sg) <=? STR_NL) && (STR_NL <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
  (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis WVC : write_value_contract B API RF.
Hypothesis PUTC : forall fx' : YK11.FPState, @put_contract fx' rc B API RF.
Hypothesis FFC : forall fx' : YK11.FPState, @fuzz_free_contract fx' rc B API RF.

Lemma pjw_word4_iff : forall m a v, 0 <= a -> a + 4 <= 2 ^ 64 ->
  (word4_mem B m a v <-> bytes_at rsegs m a (le4 (Z_to_bv 64 v))).
Proof using SEGS.
  intros m a v Ha Hb. unfold word4_mem. rewrite SEGS. split.
  - intros H. split; [lia|]. split; [rewrite length_le4; lia|].
    intros i Hi. rewrite length_le4 in Hi. rewrite <- mbyte_mrd, H by exact Hi.
    unfold le4. rewrite nth_Z_to_le by exact Hi. rewrite le_byte_bv, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite le4_byte by exact Hi. reflexivity.
  - intros (_ & _ & H) k Hk. rewrite mbyte_mrd, H by (rewrite length_le4; exact Hk).
    unfold le4. rewrite nth_Z_to_le by exact Hk. rewrite le_byte_bv, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite le4_byte by exact Hk. reflexivity.
Qed.

Lemma pjw_rec_of : forall m Lam o buf len cap failed text, pj_out_ok B m Lam o buf len cap failed text ->
  exists pad, pj_rec m o buf len cap failed pad.
Proof using SEGS.
  intros m Lam o buf len cap failed text PJ.
  destruct PJ as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & _).
  rewrite SEGS in HRW, Wb, Wl, Wc.
  assert (STK : stk rsegs m (o + 28) (o + 32)).
  { split; [lia|]. split; [lia|]. intros a Ha. destruct (HRW (a - o) ltac:(lia)) as [W (v & Hv)].
    replace (o + (a - o)) with a in W, Hv by lia. split; [exact W|]. exists v. exact Hv. }
  destruct (stk_bytes rsegs m (o + 28) (o + 32) STK ltac:(lia)) as (pad & Lp & Bp).
  replace (Z.to_nat (o + 32 - (o + 28))) with 4%nat in Lp by lia.
  exists pad. unfold pj_rec. split; [split|].
  - cbn [cells_wf cell_wf]. repeat split. exact Lp.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [apply word_mem_iff; [lia | lia | exact Wb]|]. rewrite length_le8.
    apply bytes_at_app. split; [apply word_mem_iff; [lia | lia | exact Wl]|]. rewrite length_le8.
    replace (o + Z.of_nat 8 + Z.of_nat 8) with (o + 16) by lia.
    apply bytes_at_app. split; [apply word_mem_iff; [lia | lia | exact Wc]|]. rewrite length_le8.
    replace (o + 16 + Z.of_nat 8) with (o + 24) by lia.
    apply bytes_at_app. split; [apply pjw_word4_iff; [lia | lia | exact Wf]|]. rewrite length_le4.
    replace (o + 24 + Z.of_nat 4) with (o + 28) by lia. exact Bp.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (HRW i Hi)).
Qed.

Lemma pjw_out_zero : forall m Lam o pad, pj_rec m o 0 0 0 0 pad -> o mod 8 = 0 ->
  pj_out_ok B m Lam o 0 0 0 0 [].
Proof using SEGS.
  intros m Lam o pad REC H8.
  pose proof (Step.rw_cells_bound _ _ _ _ REC) as RB. cbn [cells_size csize] in RB.
  destruct REC as [[Hwf BY] (_ & _ & HW)]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (_ & _ & _ & _ & Lp & _).
  cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. cbn [cells_size csize] in HW.
  pose proof BY as BY0.
  apply bytes_at_app in BY as [Bb BY]. rewrite length_le8 in BY.
  apply bytes_at_app in BY as [Bl BY]. rewrite length_le8 in BY.
  apply bytes_at_app in BY as [Bc BY]. rewrite length_le8 in BY.
  apply bytes_at_app in BY as [Bf _].
  unfold pj_out_ok. rewrite SEGS.
  split; [exact H8|]. split; [lia|]. split; [lia|].
  split.
  { intros i Hi. split; [exact (HW i ltac:(cbn; lia))|].
    destruct BY0 as (_ & _ & HB). rewrite mbyte_mrd. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite HB by (rewrite !length_app, !length_le8, length_le4, Lp; lia).
    destruct (nth_error _ _) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E.
    rewrite !length_app, !length_le8, length_le4, Lp in E. lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply word_mem_iff; [lia | lia | exact Bb]|].
  split; [apply word_mem_iff; [lia | lia | replace (o + 8) with (o + Z.of_nat 8) by lia; exact Bl]|].
  split; [apply word_mem_iff; [lia | lia | replace (o + 16) with (o + Z.of_nat 8 + Z.of_nat 8) by lia; exact Bc]|].
  split; [apply pjw_word4_iff; [lia | lia |
    replace (o + 24) with (o + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia; exact Bf]|].
  split; [left; reflexivity|]. split; [constructor|]. split; [reflexivity|].
  left. repeat split.
Qed.

Lemma pjw_noimg_fs : forall a, ~ in_img B a -> find_segment rsegs a 1 = None.
Proof using SEGS.
  intros a H. destruct (find_segment rsegs a 1) as [s|] eqn:F; [|reflexivity]. exfalso. apply H.
  destruct (fs_some _ _ _ _ F) as (Hin & H1 & H2). pose proof (rsegs_seg_top s Hin) as T. unfold IMG_TOP in T.
  unfold in_img. rewrite SEGS.
  split; [intros E; rewrite E in Hin; exact Hin|].
  exists (segment_reservation s). split; [apply in_map; exact Hin|].
  unfold segment_reservation. cbn [fst snd]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). unfold page_round_down_Z, page_round_up_Z, page_size.
  rewrite (Z.mod_small (Z.of_N (seg_base s) / 4096 * 4096)) by (Z.div_mod_to_equations; lia).
  rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma pjw_mbyte_noimg : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> mbyte (ms_segs B) m a = m (Z_to_bv 64 a).
Proof using SEGS.
  intros m a Ha H. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b0|]; [reflexivity|].
  rewrite SEGS. apply seg_rom_unmapped. rewrite unsigned_lit by lia. exact (pjw_noimg_fs a H).
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (b : rf_R RF)
  (v pretty : Z) (t : jv) (D Lam : list (Z * Z)) (peak cnt fail : Z).
Hypothesis GG : ms_got_guard B = GOT_GUARD.
Hypothesis GD : ms_guard B = GUARD.
Hypothesis PRE : call_pre_k B (aa_MR API) (PJW_K t) L A regs mem md.
Hypothesis TS : spZ regs <= TASK_SIZE.
Hypothesis INIT : st_init_done A = true.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm0 (@fp_csr fx).
Hypothesis R10 : getr regs 10 = Z_to_bv 64 v.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 pretty.
Hypothesis HPR : 0 <= pretty < 2 ^ 64.
Hypothesis LG : ledger B L A mem Lam peak cnt fail.
Hypothesis OE : off_errno B (spZ regs - PJW_K t) (PJW_K t).
Hypothesis PN : pj_node rsegs mem (wv_lblk Lam) v t D.
Hypothesis PW : pjw_where B regs Lam v.
Hypothesis DL : forall a k, In (a, k) D -> In (a, k) Lam.
Hypothesis DEP : Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1.
Hypothesis LEN : Z.of_nat (length (wdoc t (negb (pretty =? 0)))) + 1 <= WMAX.
Hypothesis RS : rf_ok RF A b.
Hypothesis ROOMS : wr_rooms RF b (w0 cnt fail) (wdpieces t (negb (pretty =? 0))).

Lemma pjw_k : PJW_K t = 48 + WV_K t /\ 8608 <= WV_K t /\ PUT_K = 8352.
Proof.
  unfold PJW_K, PJW_FR, WV_K, WV_FR, WV_KMAX, put_string_c.PS_K, indent_c.IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK.
  pose proof (Zle_0_nat (PjTree.depth t)). lia.
Qed.

Lemma pjw_foot_cases : forall z, pj_foot v D z ->
  (spZ regs <= z /\ off_errno B v 56 /\ v <= z < v + 56) \/ (exists x y, In (x, y) Lam /\ x <= z < x + y).
Proof.
  intros z [Hz|([x y] & Hb & Hh)].
  - destruct PW as [(H1 & H2)|(x & y & Hin & H1 & H2)].
    + left. split; [lia|]. split; [exact H2 | lia].
    + right. exists x, y. split; [exact Hin | lia].
  - right. exists x, y. split; [exact (DL x y Hb)|]. unfold pj_holds in Hh. cbn [fst snd] in Hh. lia.
Qed.

Lemma pjw_node_final : forall m',
  keeps B L A mem m' 0 ->
  (forall a, spZ regs <= a < 2 ^ 64 -> ~ errno_at B a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) mem a) ->
  pj_node rsegs m' (wv_lblk Lam) v t D.
Proof.
  intros m' KP FS. pose proof PRE as (HM & _ & _ & _ & _ & Hceil & _).
  pose proof ceil_big as CEB. unfold IMG_TOP in CEB. pose proof pjw_k as (KE & KW & _).
  apply (pj_node_frame rsegs t mem (wv_lblk Lam) m' (wv_lblk Lam) v D PN); [intros a k H; exact (DL a k H)|].
  intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
  assert (KEY : ~ in_img B (bv_unsigned x) /\
                mbyte (ms_segs B) m' (bv_unsigned x) = mbyte (ms_segs B) mem (bv_unsigned x)).
  { destruct (pjw_foot_cases _ Hx) as [(H1 & H2 & H3)|(x0 & y0 & Hin & H1)].
    - split.
      + intros HI. pose proof (in_img_low B SEGS _ HI). unfold IMG_TOP in *. lia.
      + apply FS; [lia|]. unfold errno_at, off_errno in *. lia.
    - destruct (lblock_in B _ _ _ _ _ _ _ _ _ LG Hin) as [Hy Hb].
      pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin) as RR.
      split.
      + replace (bv_unsigned x) with (x0 + (bv_unsigned x - x0)) by lia.
        apply (ledger_block_not_img B _ _ _ _ _ _ _ x0 y0 _ LG Hin). lia.
      + pose proof (KP (x0 - 16) (y0 + 16) (bv_unsigned x - x0 + 16) Hb) as K.
        replace (x0 - 16 + (bv_unsigned x - x0 + 16)) with (bv_unsigned x) in K by lia.
        apply K; lia. }
  destruct KEY as [NI E].
  rewrite <- (Z_to_bv_bv_unsigned x).
  rewrite <- (pjw_mbyte_noimg m' _ Rx NI), <- (pjw_mbyte_noimg mem _ Rx NI). exact E.
Qed.

Lemma pjw_fs_of : forall m' L' A' md', aa_MR API L' A' m' md' ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
     ~ (spZ regs - PJW_K t <= a < spZ regs) -> ~ errno_at B a -> ~ alloc_statics a ->
     mbyte (ms_segs B) m' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m' a)) ->
  forall a, spZ regs <= a < 2 ^ 64 -> ~ errno_at B a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) mem a.
Proof.
  intros m' L' A' md' HM' F a Ha He.
  pose proof PRE as (HM & _ & _ & _ & _ & Hceil & _).
  pose proof pjw_k as (KE & KW & _).
  assert (NS : ~ alloc_statics a) by (intros Hs0; pose proof (statics_low a Hs0); lia).
  assert (Hd : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
  assert (W0 : ~ (spZ regs - PJW_K t <= a < spZ regs)) by lia.
  exact (proj1 (F a Hd (not_owned_hi B API _ _ _ _ a HM ltac:(lia)) (not_owned_hi B API _ _ _ _ a HM' ltac:(lia))
    W0 He NS)).
Qed.

Lemma pjw_tail : forall (fx' : YK11.FPState) m1 regsT memT mdT L2 A2 buf2 Lam2 peak2 b2 (g8 : word),
  (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) ->
  frm0 (@fp_csr fx') ->
  munch [(spZ regs - 48, spZ regs)] mem m1 -> wmono rsegs mem m1 -> aa_MR API L A m1 md ->
  wr_rel B API RF (spZ regs - PJW_K t) (spZ regs) L A m1 md (spZ regs - 48) 0 (w0 cnt fail) Lam peak b
    (wdpieces t (negb (pretty =? 0))) L2 A2 memT mdT buf2 Lam2 peak2 b2 ->
  Step.rw_cells rsegs memT (spZ regs - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  mkR_of regsT = mkR (reg_get regsT 1) (Z_to_bv 64 (bv_unsigned (reg_get regs 2) - PJW_FRAME)) (reg_get regs 3)
    (reg_get regs 4) (reg_get regsT 5) (reg_get regsT 6) (reg_get regsT 7) g8 (reg_get regs 9)
    (reg_get regsT 10) (reg_get regsT 11) (reg_get regsT 12) (reg_get regsT 13) (reg_get regsT 14)
    (reg_get regsT 15) (reg_get regsT 16) (reg_get regsT 17) (reg_get regs 18) (reg_get regs 19)
    (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
    (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regsT 28) (reg_get regsT 29)
    (reg_get regsT 30) (reg_get regsT 31) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regsT (Z_to_bv 64 PJW_PUT_RET) memT (YK11.seg_rom rsegs)) mdT)
    (@pj_write_ret fx rc B API RF (PJW_K t) L A regs mem md v t D (negb (pretty =? 0)) Lam peak cnt fail b).
Proof.
  intros fx' m1 regsT memT mdT L2 A2 buf2 Lam2 peak2 b2 g8 FRG FC MU1 WM1 HM1 REL FRC RT.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  pose proof REL as (HM2 & HWF2 & HB2 & [RO2 GK2] & PJ2 & LG2 & RS2 & EB2 & LM2 & LL2 & RG2 & IN2 & MD2 & PT2 & KP2
    & FM2 & FR2 & WR2).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  pose proof ceil_big as CEB. unfold IMG_TOP in CEB.
  pose proof pjw_k as (KE & KW & KP).
  assert (SP2 : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite getr_reg by reflexivity; reflexivity).
  assert (PC : ret_pc (reg_get regs 1) = getr regs 1)
    by (rewrite <- getr_reg by reflexivity; apply ret_pc_ok; exact Hra).
  assert (WS : forall a, spZ regs - PJW_K t <= a < spZ regs -> writable_at (ms_segs B) memT a).
  { intros a Ha. apply WR2; [left; exact Ha|]. rewrite <- SEGS in WM1. apply WM1. apply HWs. exact Ha. }
  assert (STKT : stk rsegs memT (spZ regs - PJW_K t) (bv_unsigned (reg_get regs 2) - PJW_FRAME)).
  { rewrite SP2. unfold PJW_FRAME. apply stk_hi; [unfold IMG_TOP; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply WS. lia. }
  assert (FRC' : Step.rw_cells rsegs memT (bv_unsigned (reg_get regs 2) - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)])
    by (rewrite SP2; exact FRC).
  assert (KEEPT : keeps B L A mem memT 0).
  { intros a k i Hin Hne Hi. pose proof (block_range B API _ _ _ _ _ _ HM Hin) as [R1 R2].
    rewrite (KP2 a k i Hin ltac:(lia) Hi).
    exact (proj1 (raw_mbyte (ms_segs B) mem m1 (a + i)
      (munch_raw _ mem m1 (a + i) MU1 ltac:(lia) ltac:(cbn [outside]; split; [lia | exact I])))). }
  assert (FRT : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L2 A2 a ->
       ~ (spZ regs - PJW_K t <= a < spZ regs) -> ~ errno_at B a -> ~ alloc_statics a ->
       mbyte (ms_segs B) memT a = mbyte (ms_segs B) mem a /\
       (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) memT a)).
  { intros a Hd Ho0 Ho2 Hs He Hst.
    destruct (FR2 a Hd Ho0 Ho2 Hs He ltac:(lia) Hst) as [E1 W1].
    destruct (raw_mbyte (ms_segs B) mem m1 a (munch_raw _ mem m1 a MU1 (dom_range B SEGS a Hd)
      ltac:(cbn [outside]; split; [lia | exact I]))) as [E0 W0].
    split; [congruence | tauto]. }
  assert (WRT : forall a, (spZ regs - PJW_K t <= a < spZ regs \/ errno_at B a) -> writable_at (ms_segs B) mem a ->
       writable_at (ms_segs B) memT a).
  { intros a Ha W. apply WR2; [exact Ha|]. rewrite <- SEGS in WM1. apply WM1. exact W. }
  assert (PTT : forall q n, In (q, n) (user_blocks A) ->
       In (q, n) (user_blocks A2) /\ ptr_addr L2 q = ptr_addr L q).
  { intros q n Hq. apply (PT2 q n Hq). intros E. injection E as E _.
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq). lia. }
  assert (GKT : guard_kept B mem memT).
  { apply (guard_trans B mem m1 memT); [|exact GK2].
    apply (guard_munch B API L A mem md _ mem m1 HM MU1). intros i Hi.
    destruct (got_low B API L A mem md i HM Hi) as [_ G]. cbn [outside]. split; [lia | exact I]. }
  destruct (pjw_rec_of _ _ _ _ _ _ _ _ PJ2) as [pad REC].
  assert (REC' : pj_rec memT (bv_unsigned (reg_get regs 2) - PJW_FRAME) buf2
      (Z.of_nat (length (w_text (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))))))
      (w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))))
      (w_failed (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0))))) pad)
    by (rewrite SP2; exact REC).
  pose proof PJ2 as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & BOt & LT & CAP).
  destruct Hf as [F0|F1].
  - assert (CAPNZ : w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))) <> 0)
      by (apply pjw_w0_cap; [exact F0 | apply pjw_dpieces_ne]).
    destruct CAP as [(C0 & _ & _)|(Hj & Hin & Hst & Hlt & Hz)]; [exfalso; exact (CAPNZ C0)|].
    destruct LM2 as [(Ec & _ & _ & _)|(Gc & l1 & l2 & Hl & El & Ep)]; [exfalso; exact (CAPNZ Ec)|].
    destruct Hl as [(_ & -> & ->)|(Hc0 & _)]; [|exfalso; exact (Hc0 eq_refl)].
    cbn [app] in El, Ep.
    rewrite F0 in REC'.
    eapply (@kA_lift fx'); [exact Hh2 | exact Hl2 | |].
    { rewrite RT.
      eapply (pjw_ret_text (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
        (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
        (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) _ _ _
        (spZ regs - PJW_K t)); [exact STKT | rewrite SP2; unfold PJW_FRAME; lia | exact REC' | exact FRC']. }
    intros x y HQ HEQ HRM.
    destruct HQ as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & Ey & _). subst y.
    destruct (post_shape B SEGS regs _ memT x mdT HEQ PC) as [CF _].
    apply SR_ret. unfold pj_write_ret. cbv zeta.
    exists fx', L2, A2, (ms_regs x), memT, mdT, Lam2, peak2, b2.
    split; [exact CF|]. split; [exact FRG|]. split; [exact FC|].
    split; [eapply regs_kept; [exact HEQ|]; callee_cases|].
    split; [exact HM2|]. split; [exact HWF2|]. split; [exact HB2|]. split; [exact RO2|]. split; [exact GKT|].
    split; [exact LG2|].
    split; [exact RS2|].
    split; [exact LL2|]. split; [exact RG2|]. split; [exact IN2|].
    split; [exact MD2|]. split; [exact PTT|]. split; [exact KEEPT|].
    split; [apply pjw_node_final; [exact KEEPT | exact (pjw_fs_of memT L2 A2 mdT HM2 FRT)]|].
    split; [exact FRT|]. split; [exact WRT|].
    left. split; [exact F0|]. exists buf2.
    split; [rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity|].
    split; [pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM2 LG2 Hin); lia|].
    split.
    { intros HBk. pose proof (block_range B API _ _ _ _ _ _ HM HBk) as [RB1 _].
      exact (FM2 _ _ HBk ltac:(lia) ltac:(intros E; injection E as E _; lia) eq_refl). }
    split; [exact El|]. split; [exact Ep|].
    split; [rewrite EB2; reflexivity|].
    assert (ET : w_text (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))) = wdoc t (negb (pretty =? 0)))
      by exact (pjw_text_ok _ _ F0).
    rewrite <- ET. exact Hz.
  - rewrite F1 in REC'.
    assert (CAPA : buf2 = 0 /\ w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))) = 0 \/
                   In (buf2, w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0))))) Lam2).
    { destruct CAP as [(C0 & B0 & _)|(_ & Hin & _)]; [left; split; assumption | right; exact Hin]. }
    assert (EL : forall a, free_writes buf2 (w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0))))) a ->
                   a < alloc_ceiling).
    { intros a [Ha|(Hb0 & Ha)]; [unfold G_LIVE in Ha; lia|].
      destruct CAPA as [(B0 & _)|Hin]; [exfalso; exact (Hb0 B0)|].
      pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM2 LG2 Hin). lia. }
    eapply (@kA_lift fx'); [exact Hh2 | exact Hl2 | |].
    { rewrite RT.
      eapply (pjw_to_free (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
        (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
        (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) _ _ _
        (spZ regs - PJW_K t)); [rewrite SP2; unfold PJW_FRAME; lia | exact REC' | lia]. }
    intros x4 y4 HQ4 HEQ4 HRM4. destruct HQ4 as [a1' Ey4]. subst y4.
    rewrite (eqv_shape _ _ _ _ HEQ4).
    assert (G1 : getr (ms_regs x4) 1 = Z_to_bv 64 PJW_FREE_RET)
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ4); reflexivity).
    assert (G2 : getr (ms_regs x4) 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - PJW_FRAME))
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ4); reflexivity).
    assert (G4 : getr (ms_regs x4) 4 = Z_to_bv 64 (ms_tp B))
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ4), <- Htp; reflexivity).
    assert (G10 : getr (ms_regs x4) 10 = Z_to_bv 64 buf2)
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ4); reflexivity).
    assert (SP5 : spZ (ms_regs x4) = spZ regs - 48)
      by (unfold spZ at 1; rewrite G2, SP2; unfold PJW_FRAME; apply unsigned_lit; lia).
    assert (CPRE5 : call_pre_k B (aa_MR API) ALLOC_STACK L2 A2 (ms_regs x4) memT mdT).
    { unfold call_pre_k. rewrite SP5.
      split; [exact HM2|]. split; [exact HWF2|]. split; [exact HB2|].
      split; [rewrite G1; exact (ret_ok_lit PJW_FREE_RET ltac:(unfold PJW_FREE_RET; lia) eq_refl)|].
      split; [Z.div_mod_to_equations; lia|].
      split; [unfold ALLOC_STACK; lia|]. split; [lia|].
      split; [intros a Ha; apply WS; unfold ALLOC_STACK in Ha; lia|].
      split; [exact G4|].
      split; [intros a Ha; apply WRT; [right; exact Ha | apply HWe; exact Ha]|].
      intros Hi. rewrite (IN2 INIT) in Hi. discriminate. }
    eapply SR_bind.
    { rewrite <- SEGS.
      exact (FFC fx' L2 A2 (ms_regs x4) memT mdT buf2 (w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))))
        b2 Lam2 peak2 _ _ CPRE5 G10 LG2 RO2 CAPA RS2). }
    intros c' (L' & A' & regs6 & mem' & md' & Ec & RO' & GK' & INI' & LIB' & CPK & RG' & KP' & UK' & ARMS).
    subst c'. rewrite G1, SEGS.
    pose proof CPK as (HM3 & HWF3 & HB3 & HLL3 & HPT3 & RP6 & HMD3 & HFR3 & HBK3 & HSW3).
    destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM3) as (Hh3 & Hl3 & _).
    assert (XH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B ALLOC_STACK (ms_regs x4) a ->
       mbyte (ms_segs B) mem' a = mbyte (ms_segs B) memT a /\
       (writable_at (ms_segs B) memT a <-> writable_at (ms_segs B) mem' a)).
    { intros a Ha Hs. apply (HFR3 a (or_introl Ha)).
      - exact (not_owned_hi B API _ _ _ _ a HM2 ltac:(lia)).
      - exact (not_owned_hi B API _ _ _ _ a HM3 ltac:(lia)).
      - exact Hs.
      - intros HE. pose proof (EL a HE). lia. }
    assert (NSc : forall a, spZ regs - 48 <= a < spZ regs -> ~ scratch_k B ALLOC_STACK (ms_regs x4) a).
    { intros a Ha [Hs|Hs]; [rewrite SP5 in Hs; lia | unfold off_errno in OE; lia]. }
    assert (WSF : forall a, spZ regs - PJW_K t <= a < spZ regs -> writable_at (ms_segs B) mem' a).
    { intros a Ha. destruct (scratch_dec B ALLOC_STACK (ms_regs x4) a) as [Sc|Sc]; [exact (HSW3 a Sc)|].
      apply (proj1 (proj2 (XH a ltac:(lia) Sc))). apply WS. exact Ha. }
    assert (STK6 : stk rsegs mem' (spZ regs - PJW_K t) (bv_unsigned (reg_get regs 2) - PJW_FRAME)).
    { rewrite SP2. unfold PJW_FRAME. apply stk_hi; [unfold IMG_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply WSF. lia. }
    assert (CEQ : forall A0 cs, spZ regs - 48 <= A0 -> A0 + Z.of_nat (cells_size cs) <= spZ regs ->
       Step.rw_cells rsegs memT A0 cs -> Step.rw_cells rsegs mem' A0 cs).
    { intros A0 cs H1 H2 RC. pose proof (Step.rw_cells_bound _ _ _ _ RC) as RB.
      apply (rw_cells_eqm memT mem' A0 cs RC). intros i Hi. rewrite <- SEGS.
      destruct (XH (A0 + i) ltac:(lia) (NSc (A0 + i) ltac:(lia))) as [E W]. split; [exact E | tauto]. }
    assert (REC6 : pj_rec mem' (bv_unsigned (reg_get regs 2) - PJW_FRAME) buf2
        (Z.of_nat (length (w_text (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))))))
        (w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0))))) 1 pad).
    { unfold pj_rec in *. rewrite SP2 in REC' |- *. unfold PJW_FRAME in *.
      apply CEQ; [lia | cbn [cells_size csize]; lia | exact REC']. }
    assert (FRC6 : Step.rw_cells rsegs mem' (bv_unsigned (reg_get regs 2) - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { rewrite SP2. apply CEQ; [lia | cbn [cells_size csize]; lia | exact FRC]. }
    assert (KEEPF : keeps B L A mem mem' 0).
    { intros a k i Hin Hne Hi.
      destruct (blocks_user L A a k Hin) as (q & Hq & Eq).
      destruct (PTT q k Hq) as [Hq2 Ep2].
      assert (Hin2 : In (a, k) (blocks L2 A2)).
      { unfold blocks. apply in_map_iff. exists (q, k). cbn [fst snd]. rewrite Ep2, Eq. split; [reflexivity | exact Hq2]. }
      pose proof (block_range B API _ _ _ _ _ _ HM Hin) as [R1 R2].
      rewrite (KP' a k i Hin2 (FM2 a k Hin ltac:(lia) ltac:(intros E; injection E as E _; lia)) Hi).
      exact (KEEPT a k i Hin Hne Hi). }
    assert (FRF : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
       ~ (spZ regs - PJW_K t <= a < spZ regs) -> ~ errno_at B a -> ~ alloc_statics a ->
       mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
       (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
    { intros a Hd Ho0 Ho' Hs He Hst.
      pose proof (owned_mid B API AX CTX L A mem md L2 A2 memT mdT a HM HM2 Hd Ho0) as Ho2.
      destruct (FRT a Hd Ho0 Ho2 Hs He Hst) as [E1 W1].
      assert (NS : ~ scratch_k B ALLOC_STACK (ms_regs x4) a).
      { intros [Sc|Sc]; [rewrite SP5 in Sc; unfold ALLOC_STACK in Sc; lia | exact (He Sc)]. }
      assert (NE : ~ free_writes buf2 (w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0))))) a).
      { intros [HE|(Hb0 & HE)]; [apply Hst; left; exact HE|].
        destruct CAPA as [(B0 & _)|Hin]; [exact (Hb0 B0)|].
        destruct (lblock_in B _ _ _ _ _ _ _ _ _ LG2 Hin) as [_ Hb].
        exact (blk_out B API AX L2 A2 memT mdT _ _ a HM2 Hb ltac:(lia) Hd). }
      destruct (HFR3 a Hd Ho2 Ho' NS NE) as [E2 W2].
      split; [congruence | tauto]. }
    assert (WRF : forall a, (spZ regs - PJW_K t <= a < spZ regs \/ errno_at B a) -> writable_at (ms_segs B) mem a ->
       writable_at (ms_segs B) mem' a).
    { intros a Ha W. pose proof (WRT a Ha W) as WT.
      destruct (scratch_dec B ALLOC_STACK (ms_regs x4) a) as [Sc|Sc]; [exact (HSW3 a Sc)|].
      destruct Ha as [Ha|Ha]; [|exfalso; apply Sc; right; exact Ha].
      exact (proj1 (proj2 (XH a ltac:(lia) Sc)) WT). }
    assert (PTF : forall q n, In (q, n) (user_blocks A) ->
       In (q, n) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q).
    { intros q n Hq. destruct (PTT q n Hq) as [Hq2 E2].
      pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq) as RQ.
      assert (Hne : (ptr_addr L2 q, n) <> (buf2 - 16, w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))) + 16)).
      { rewrite E2. intros E0. injection E0 as Ea En.
        apply (FM2 (ptr_addr L q) n);
          [unfold blocks; apply in_map_iff; exists (q, n); split; [reflexivity | exact Hq] | lia
          | intros E1; injection E1 as E1 _; lia | exact Ea]. }
      pose proof (UK' q n Hq2 Hne) as Hq'.
      split; [exact Hq'|]. rewrite (HPT3 q n Hq2 Hq'). exact E2. }
    assert (GKF : guard_kept B mem mem') by exact (guard_trans B mem memT mem' GKT GK').
    assert (LLF : layout_le A L L') by exact (layout_le_trans A A2 L L2 L' LL2 HLL3 RG2).
    assert (RGF : (length (st_regions A) <= length (st_regions A'))%nat) by lia.
    assert (INF : st_init_done A = true -> st_init_done A' = true) by (intros H; exact (INI' (IN2 H))).
    assert (MDF : exists vm', md' = with_vmmaps vm' md).
    { destruct MD2 as [vm1 E1]. destruct HMD3 as [vm2 E2]. exists vm2. rewrite E2, E1. apply with_vmmaps_twice. }
    assert (PNF : pj_node rsegs mem' (wv_lblk Lam) v t D)
      by (apply pjw_node_final; [exact KEEPF | exact (pjw_fs_of mem' L' A' md' HM3 FRF)]).
    eapply (@kA_lift fx'); [exact Hh3 | exact Hl3 | |].
    { rewrite (pjw_resume HEQ4 RP6).
      eapply (pjw_ret_failed (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
        (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
        (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) _ _ _
        (spZ regs - PJW_K t)); [exact STK6 | rewrite SP2; unfold PJW_FRAME; lia | exact REC6 | exact FRC6]. }
    intros x6 y6 HQ6 HEQ6 HRM6.
    destruct HQ6 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & Ey6 & _). subst y6.
    destruct (post_shape B SEGS regs _ mem' x6 md' HEQ6 PC) as [CF _].
    assert (RPF : regs_preserved regs (ms_regs x6)) by (eapply regs_kept; [exact HEQ6|]; callee_cases).
    assert (A0F : getr (ms_regs x6) 10 = Z_to_bv 64 0) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ6); reflexivity).
    apply SR_ret. unfold pj_write_ret. cbv zeta.
    destruct LM2 as [(Ec & Eb & El & Ep)|(Gc & l1 & l2 & Hl & El & Ep)].
    + destruct ARMS as [(_ & _ & _ & _ & _ & _ & _ & LGF & RSF)|(Hb0 & _)]; [|exfalso; exact (Hb0 Eb)].
      rewrite El, Ep in LGF.
      exists fx', L', A', (ms_regs x6), mem', md', Lam, peak, b2.
      split; [exact CF|]. split; [exact FRG|]. split; [exact FC|]. split; [exact RPF|].
      split; [exact HM3|]. split; [exact HWF3|]. split; [exact HB3|]. split; [exact RO'|]. split; [exact GKF|].
      split; [exact LGF|]. split; [exact RSF|]. split; [exact LLF|]. split; [exact RGF|].
      split; [exact INF|].
      split; [exact MDF|]. split; [exact PTF|]. split; [exact KEEPF|]. split; [exact PNF|].
      split; [exact FRF|]. split; [exact WRF|].
      right. split; [rewrite F1; discriminate|]. split; [exact A0F|]. split; [reflexivity|].
      left. split; [exact Ec|]. split; [reflexivity|]. rewrite EB2. reflexivity.
    + destruct Hl as [(_ & -> & ->)|(Hc0 & _)]; [|exfalso; exact (Hc0 eq_refl)].
      cbn [app] in El, Ep. change (w_cap (w0 cnt fail)) with 0 in Gc.
      assert (Hin : In (buf2, w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0))))) Lam2)
        by (rewrite El; left; reflexivity).
      pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM2 LG2 Hin) as RB.
      destruct ARMS as [(Hb0 & _)|(_ & _ & (l1' & l2' & EL' & LGF) & RSF)]; [lia|].
      assert (ELam : Lam = l1' ++ l2').
      { pose proof LG2 as (_ & _ & _ & _ & ND & _). rewrite El in ND, EL'. exact (nodup_head _ _ _ _ ND EL'). }
      rewrite <- ELam, Ep in LGF.
      exists fx', L', A', (ms_regs x6), mem', md', Lam,
        (Z.max peak (lsum Lam + w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))))),
        (rf_free RF b2 (w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))) + 16)).
      split; [exact CF|]. split; [exact FRG|]. split; [exact FC|]. split; [exact RPF|].
      split; [exact HM3|]. split; [exact HWF3|]. split; [exact HB3|]. split; [exact RO'|]. split; [exact GKF|].
      split; [exact LGF|].
      split; [exact RSF|].
      split; [exact LLF|]. split; [exact RGF|]. split; [exact INF|].
      split; [exact MDF|]. split; [exact PTF|]. split; [exact KEEPF|]. split; [exact PNF|].
      split; [exact FRF|]. split; [exact WRF|].
      right. split; [rewrite F1; discriminate|]. split; [exact A0F|]. split; [reflexivity|].
      right. split; [lia|]. split; [reflexivity|]. rewrite EB2. reflexivity.
Qed.

Lemma pjw_body : SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PJ_WRITE_PC) mem (seg_rom (ms_segs B))) md)
  (@pj_write_ret fx rc B API RF (PJW_K t) L A regs mem md v t D (negb (pretty =? 0)) Lam peak cnt fail b).
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof ceil_big as CEB. unfold IMG_TOP in CEB.
  pose proof pjw_k as (KE & KW & KP).
  assert (SP2 : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite getr_reg by reflexivity; reflexivity).
  assert (Q10 : reg_get regs 10 = Z_to_bv 64 v) by (rewrite <- getr_reg by reflexivity; exact R10).
  assert (Q11 : reg_get regs 11 = Z_to_bv 64 pretty) by (rewrite <- getr_reg by reflexivity; exact R11).
  assert (STK : stk rsegs mem (spZ regs - PJW_K t) (bv_unsigned (reg_get regs 2))).
  { rewrite SP2. apply stk_hi; [unfold IMG_TOP; lia | lia |]. intros a Ha. rewrite <- SEGS. apply HWs. exact Ha. }
  rewrite SEGS. eapply kA_lift; [exact Hh | exact Hl | |].
  { unfold mkR_of. rewrite Q10, Q11.
    eapply pjw_to_write_value with (lo := spZ regs - PJW_K t); [exact STK | rewrite SP2; unfold PJW_FRAME; lia]. }
  intros x y HQ HEQ HRM.
  destruct HQ as (m1 & Ey & MU1 & WM1 & ST1 & REC1 & FR1). subst y.
  rewrite SP2 in MU1, REC1, FR1. unfold PJW_FRAME in MU1, REC1.
  assert (XM : ms_mem x = m1) by (destruct HEQ as (_ & _ & _ & _ & _ & _ & HMx & _); cbn in HMx; congruence).
  rewrite XM in HRM.
  rewrite (eqv_shape _ _ _ _ HEQ).
  assert (G1 : getr (ms_regs x) 1 = Z_to_bv 64 PJW_WV_RET) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (G2 : getr (ms_regs x) 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - PJW_FRAME))
    by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (G4 : getr (ms_regs x) 4 = Z_to_bv 64 (ms_tp B))
    by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ), <- Htp; reflexivity).
  assert (G10 : getr (ms_regs x) 10 = Z_to_bv 64 (spZ regs - 48)).
  { rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). rewrite <- SP2. reflexivity. }
  assert (G11 : getr (ms_regs x) 11 = Z_to_bv 64 v) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (G12 : getr (ms_regs x) 12 = Z_to_bv 64 pretty) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (G13 : getr (ms_regs x) 13 = Z_to_bv 64 0) by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ); reflexivity).
  assert (SPx : spZ (ms_regs x) = spZ regs - 48)
    by (unfold spZ at 1; rewrite G2, SP2; unfold PJW_FRAME; apply unsigned_lit; lia).
  assert (OW : forall a, owned B L A a -> outside [(spZ regs - 48, spZ regs)] a)
    by (intros a Ha; pose proof (owned_low B API _ _ _ _ _ HM Ha); cbn [outside]; split; [lia | exact I]).
  assert (HM1 : aa_MR API L A m1 md) by exact (mr_munch B API _ _ _ _ _ _ HM MU1 HRM OW).
  assert (WM1' : wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM1).
  assert (CPRE1k : call_pre_k B (aa_MR API) (WV_K t) L A (ms_regs x) m1 md).
  { unfold call_pre_k. rewrite SPx.
    split; [exact HM1|]. split; [exact HWF|]. split; [exact HB|].
    split; [rewrite G1; exact (ret_ok_lit PJW_WV_RET ltac:(unfold PJW_WV_RET; lia) eq_refl)|].
    split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|].
    split; [intros a Ha; apply WM1'; apply HWs; lia|].
    split; [exact G4|].
    split; [intros a Ha; apply WM1'; apply HWe; exact Ha|].
    intros Hi. rewrite INIT in Hi. discriminate. }
  assert (CPRE1 : call_pre_t B API (WV_K t) L A (ms_regs x) m1 md) by (split; [exact CPRE1k | rewrite SPx; lia]).
  assert (RO1 : ro_agree (ms_segs B) m1).
  { rewrite SEGS. apply (ro_munch_hi (spZ regs - 48) (spZ regs) mem m1); [rewrite <- SEGS; exact RO | exact MU1 |].
    unfold IMG_TOP. lia. }
  assert (PJ0 : pj_out_ok B m1 Lam (spZ regs - 48) 0 0 0 0 [])
    by (apply (pjw_out_zero m1 Lam (spZ regs - 48) (le4 (Z_to_bv 64 0)) REC1); Z.div_mod_to_equations; lia).
  assert (LG1 : ledger B L A m1 Lam peak cnt fail).
  { eapply (ledger_munch B API); [exact HM | exact LG | exact MU1 | |].
    - intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. cbn [outside]. split; [lia | exact I].
    - intros x0 k i Hin Hi. pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin).
      pose proof (lblock_in B _ _ _ _ _ _ _ _ _ LG Hin) as [Hk0 _]. cbn [outside]. split; [lia | exact I]. }
  assert (OEo : off_errno B (spZ regs - 48) 32) by (eapply off_errno_sub; [exact OE | lia | lia]).
  assert (OEw : off_errno B (spZ (ms_regs x) - WV_K t) (WV_K t))
    by (rewrite SPx; eapply off_errno_sub; [exact OE | lia | lia]).
  assert (FOOT : forall z, pj_foot v D z ->
                   outside [(spZ regs - 48, spZ regs)] z /\ ~ (spZ regs - 48 <= z < spZ regs - 48 + 32)).
  { intros z Hz. destruct (pjw_foot_cases z Hz) as [(H1 & _)|(x0 & y0 & Hin & H1)].
    - cbn [outside]. split; [split; [lia | exact I] | lia].
    - pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin).
      cbn [outside]. split; [split; [lia | exact I] | lia]. }
  assert (PN1 : pj_node rsegs m1 (wv_lblk Lam) v t D)
    by exact (pj_node_munch rsegs _ mem (wv_lblk Lam) m1 (wv_lblk Lam) v t D PN (fun a k H => DL a k H) MU1
      (fun z Hz => proj1 (FOOT z Hz))).
  assert (WW : wv_where B (ms_regs x) Lam v 0).
  { unfold wv_where. rewrite SPx. destruct PW as [(H1 & H2)|(x0 & y0 & Hin & H1 & H2)].
    - left. split; [lia | exact H2].
    - right. exists x0, y0. pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin).
      split; [exact Hin|]. split; [lia|]. split; lia. }
  assert (DL0 : forall a k, In (a, k) D -> In (a, k) Lam /\ a <> 0).
  { intros a k H. pose proof (DL a k H) as H'. split; [exact H'|].
    pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG H'). lia. }
  assert (NF : forall z, spZ regs - 48 <= z < spZ regs - 48 + 32 -> ~ pj_foot v D z)
    by (intros z Hz Hf; exact (proj2 (FOOT z Hf) Hz)).
  assert (LEN0 : Z.of_nat (length (w_text (w0 cnt fail))) +
                 Z.of_nat (length (concat (wvpieces t (negb (pretty =? 0)) 0))) + 1 <= WMAX).
  { pose proof LEN as LN. unfold wdoc, wdpieces in LN. rewrite concat_app, length_app in LN.
    change (Z.of_nat (length (w_text (w0 cnt fail)))) with 0. lia. }
  assert (ROOM0 : wr_rooms RF b (w0 cnt fail) (wvpieces t (negb (pretty =? 0)) 0)).
  { pose proof ROOMS as RM. unfold wdpieces in RM. apply wr_rooms_app in RM. exact (proj1 RM). }
  eapply SR_bind.
  { rewrite <- SEGS.
    exact (WVC L A (ms_regs x) m1 md b (spZ regs - 48) v pretty 0 t D 0 (w0 cnt fail) Lam peak SEGS GG GD CPRE1 INIT
      RO1 FRM G10 G11 G12 G13 HPR ltac:(lia) ltac:(lia) PJ0 LG1 ltac:(rewrite SPx; lia) OEo OEw PN1 WW DL0 NF LEN0 RS
      ROOM0). }
  intros c' (fx' & FRG & FC & _ & _ & L1 & A1 & regs2 & mem2 & md1 & buf1 & Lam1 & peak1 & b1 & Ec & RP2 & REL1).
  subst c'. rewrite G1, SEGS.
  rewrite SPx in REL1.
  pose proof REL1 as (HM2 & HWF2 & HB2 & [RO2 _] & PJ2 & LG2 & RS2 & EB2 & _ & _ & _ & IN2 & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  assert (FRC1 : Step.rw_cells rsegs mem2 (spZ regs - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { eapply (wr_cells B API RF SEGS); [exact HM1 | exact REL1 | exact FR1 | lia | lia | right; lia |].
    eapply off_errno_sub; [exact OE | lia | cbn [cells_size csize]; lia]. }
  assert (REL1W : wr_rel B API RF (spZ regs - PJW_K t) (spZ regs) L A m1 md (spZ regs - 48) 0 (w0 cnt fail) Lam peak b
     (wvpieces t (negb (pretty =? 0)) 0) L1 A1 mem2 md1 buf1 Lam1 peak1 b1).
  { apply (wr_rel_widen B API RF (spZ regs - 48 - WV_K t) (spZ regs - 48)); [exact HM1 | lia | lia | lia | lia | exact REL1]. }
  destruct (Z.eq_dec pretty 0) as [P0|P1].
  - assert (EP : negb (pretty =? 0) = false) by (rewrite P0; reflexivity).
    assert (EW : wdpieces t (negb (pretty =? 0)) = wvpieces t (negb (pretty =? 0)) 0)
      by (unfold wdpieces; rewrite EP; apply app_nil_r).
    eapply (@kA_lift fx'); [exact Hh2 | exact Hl2 | |].
    { rewrite (pjw_resume HEQ RP2). apply pjw_skip_nl. rewrite unsigned_lit by lia. exact P0. }
    intros x3 y3 HQ3 HEQ3 HRM3. cbv beta in HQ3. subst y3.
    rewrite (eqv_shape _ _ _ _ HEQ3).
    rewrite <- EW in REL1W.
    exact (pjw_tail fx' m1 (ms_regs x3) mem2 md1 L1 A1 buf1 Lam1 peak1 b1 (Z_to_bv 64 pretty) FRG FC MU1 WM1 HM1
      REL1W FRC1 (pjw_resume HEQ3 (fun r _ => eq_refl))).
  - assert (EP : negb (pretty =? 0) = true) by (destruct (Z.eqb_spec pretty 0); [contradiction | reflexivity]).
    assert (EW : wdpieces t (negb (pretty =? 0)) = wvpieces t (negb (pretty =? 0)) 0 ++ [[10]])
      by (unfold wdpieces; rewrite EP; reflexivity).
    eapply (@kA_lift fx'); [exact Hh2 | exact Hl2 | |].
    { rewrite (pjw_resume HEQ RP2). apply pjw_to_put_nl. rewrite unsigned_lit by lia. exact P1. }
    intros x3 y3 HQ3 HEQ3 HRM3. cbv beta in HQ3. subst y3.
    rewrite (eqv_shape _ _ _ _ HEQ3).
    assert (G31 : getr (ms_regs x3) 1 = Z_to_bv 64 PJW_PUT_RET)
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ3); reflexivity).
    assert (G32 : getr (ms_regs x3) 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - PJW_FRAME))
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ3); reflexivity).
    assert (G34 : getr (ms_regs x3) 4 = Z_to_bv 64 (ms_tp B))
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ3), <- Htp; reflexivity).
    assert (G310 : getr (ms_regs x3) 10 = Z_to_bv 64 (spZ regs - 48)).
    { rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ3). rewrite <- SP2. reflexivity. }
    assert (G311 : getr (ms_regs x3) 11 = Z_to_bv 64 STR_NL)
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ3); reflexivity).
    assert (G312 : getr (ms_regs x3) 12 = Z_to_bv 64 1)
      by (rewrite (eqv_getr _ _ _ _ _ _ _ _ _ HEQ3); reflexivity).
    assert (SP3 : spZ (ms_regs x3) = spZ regs - 48)
      by (unfold spZ at 1; rewrite G32, SP2; unfold PJW_FRAME; apply unsigned_lit; lia).
    destruct (wr_writable B API RF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - PJW_K t) (spZ regs) REL1W
      ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply WM1'; apply HWs; exact Ha)
      ltac:(intros a Ha; apply WM1'; apply HWe; exact Ha)) as [WS2 WE2].
    assert (ROr : ro_agree rsegs mem2) by (rewrite <- SEGS; exact RO2).
    assert (NEEDNL : Z.of_nat (length (w_text (putN (w0 cnt fail) (wvpieces t (negb (pretty =? 0)) 0)))) + 1 + 1 <= WMAX).
    { pose proof (putN_text (wvpieces t (negb (pretty =? 0)) 0) (w0 cnt fail)) as T. pose proof LEN as LN.
      unfold wdoc in LN. rewrite EW, concat_app, length_app in LN.
      change (length (concat [[10]])) with 1%nat in LN.
      change (Z.of_nat (length (w_text (w0 cnt fail)))) with 0 in T. lia. }
    rewrite <- SEGS.
    apply (@put_call fx' rc B API RF SEGS AX (PUTC fx') (PJW_K t - 48) (spZ regs - 48) L1 A1 (ms_regs x3) mem2 md1
      (spZ regs - 48) STR_NL 1 [10] buf1 (putN (w0 cnt fail) (wvpieces t (negb (pretty =? 0)) 0)) Lam1 peak1 b1).
    + rewrite SP3. lia.
    + rewrite SP3. lia.
    + lia.
    + lia.
    + rewrite SP3. Z.div_mod_to_equations. lia.
    + intros a Ha. apply WS2. lia.
    + exact WE2.
    + exact G34.
    + rewrite G31. exact (ret_ok_lit PJW_PUT_RET ltac:(unfold PJW_PUT_RET; lia) eq_refl).
    + exact HM2.
    + exact HWF2.
    + exact HB2.
    + exact (IN2 INIT).
    + exact RO2.
    + exact G310.
    + exact G311.
    + exact G312.
    + exact PJ2.
    + exact LG2.
    + exact RS2.
    + lia.
    + exact OEo.
    + eapply off_errno_sub; [exact OE | lia | lia].
    + exact (img_zbytes B SEGS mem2 STR_NL [10] ROr pjw_img_nl).
    + reflexivity.
    + exact pjw_bytes_nl.
    + unfold STR_NL. lia.
    + unfold STR_NL. lia.
    + exact (img_where B SEGS (ms_regs x3) Lam1 STR_NL 1 buf1 [10] pjw_seg_nl pjw_img_nl eq_refl).
    + left. unfold STR_NL. lia.
    + exact NEEDNL.
    + rewrite EB2. pose proof ROOMS as RM. rewrite EW in RM. apply wr_rooms_app in RM. destruct RM as [_ RM].
      cbn [wr_rooms] in RM. exact (proj1 RM).
    + intros regs4 L2 A2 mem3 md2 buf2 Lam2 peak2 b2 RP4 REL2.
      rewrite G31, SEGS.
      rewrite SP3 in REL2.
      assert (FRC3 : Step.rw_cells rsegs mem3 (spZ regs - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { eapply (wr_cells B API RF SEGS); [exact HM2 | exact REL2 | exact FRC1 | lia | lia | right; lia |].
        eapply off_errno_sub; [exact OE | lia | cbn [cells_size csize]; lia]. }
      assert (REL2W : wr_rel B API RF (spZ regs - PJW_K t) (spZ regs) L1 A1 mem2 md1 (spZ regs - 48) buf1
        (putN (w0 cnt fail) (wvpieces t (negb (pretty =? 0)) 0)) Lam1 peak1 b1 [[10]] L2 A2 mem3 md2 buf2 Lam2 peak2 b2).
      { apply (wr_rel_widen B API RF (spZ regs - 48 - PUT_K) (spZ regs - 48)); [exact HM2 | lia | lia | lia | lia | exact REL2]. }
      pose proof (wr_rel_app B API RF SEGS AX CTX _ _ L A m1 md (spZ regs - 48) 0 (w0 cnt fail) Lam peak b _ L1 A1 mem2 md1
        buf1 Lam1 peak1 b1 [[10]] L2 A2 mem3 md2 buf2 Lam2 peak2 b2 HM1 (Z.le_refl 0) REL1W REL2W) as REL.
      rewrite <- EW in REL.
      exact (pjw_tail fx' m1 regs4 mem3 md2 L2 A2 buf2 Lam2 peak2 b2 (Z_to_bv 64 pretty) FRG FC MU1 WM1 HM1 REL FRC3
        (pjw_resume HEQ3 RP4)).
Qed.

End Body.

Theorem pj_write_holds : pj_write_contract B API RF.
Proof.
  unfold pj_write_contract.
  intros L A regs mem md b v pretty t D Lam peak cnt fail _ GG GD [PRE TS] INIT RO FRM R10 R11 HPR LG OE PN PW DL DEP
    LEN RS ROOMS.
  eapply pjw_body; eassumption.
Qed.

End W.

Section SB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem pj_write_sb : forall (B : malloc_syms) (API : AllocAPI B),
  pj_write_contract B API sb_form -> pj_write_contract_sb B API.
Proof.
  intros B API PJ. unfold pj_write_contract_sb.
  intros L A regs mem md b v pretty t D Lam peak cnt fail SG GG GD PRE INIT RO FRM R10 R11 HPR LG OE PN PW DL DEP LEN
    RS RM.
  assert (RMS : wr_rooms sb_form b (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))).
  { apply (wr_rooms_sb (wdpieces t (negb (pretty =? 0))) b (w0 cnt fail) RM (or_introl eq_refl)).
    change (Z.of_nat (length (w_text (w0 cnt fail)))) with 0. unfold wdoc in LEN. lia. }
  assert (BW : wfold sb_form b (w0 cnt fail) (wdpieces t (negb (pretty =? 0))) =
               wbc b (w_cap (putN (w0 cnt fail) (wdpieces t (negb (pretty =? 0)))))).
  { exact (wfold_sb (wdpieces t (negb (pretty =? 0))) b (w0 cnt fail) ltac:(cbn; lia)). }
  eapply SR_mono; [exact (PJ L A regs mem md b v pretty t D Lam peak cnt fail SG GG GD PRE INIT RO FRM R10 R11 HPR LG OE
    PN PW DL DEP LEN RS RMS) |].
  intros c' (fx' & L' & A' & regs' & mem' & md' & Lam' & peak' & b' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10
    & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & ARMS).
  unfold pj_write_ret_sb. cbv zeta.
  exists fx', L', A', regs', mem', md', Lam', peak', b'.
  do 20 (split; [first [assumption | exact H11]|]).
  destruct ARMS as [(F0 & q & Q1 & Q2 & Q3 & Q4 & Q5 & Eb & Q6)|(F1 & Q1 & Q2 & [(C0 & Q3 & Eb)|(Cn & Q3 & Eb)])].
  - left. split; [exact F0|]. exists q. do 5 (split; [assumption|]). split; [|exact Q6].
    rewrite Eb, BW. apply wbc_nz. apply pjw_w0_cap; [exact F0 | apply pjw_dpieces_ne].
  - right. split; [exact F1|]. split; [exact Q1|]. split; [exact Q2|]. left. split; [exact C0|]. split; [exact Q3|].
    rewrite Eb, BW, C0. reflexivity.
  - right. split; [exact F1|]. split; [exact Q1|]. split; [exact Q2|]. right. split; [exact Cn|]. split; [exact Q3|].
    rewrite Eb, BW, (wbc_nz b _ Cn). cbn [rf_free sb_form]. apply sb_free_malloc.
Qed.

End SB.
