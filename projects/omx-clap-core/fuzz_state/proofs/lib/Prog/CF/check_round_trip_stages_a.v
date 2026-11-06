(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 556 of its 631 lines of code are new or changed and 671 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/past_nul.v, with its module names changed; 711 of its 786 lines of code are new or changed and 556 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_as_written.v, with its module names, addresses and numbers changed; 1716 of its 1784 lines of code are new or changed and 718 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_no_overread.v, with its module paths, module names and numbers changed; 1316 of its 1472 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_calls.v; 223 of its 404 lines of code are new or changed and 1291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_sd5.v, with its addresses changed; 827 of its 929 lines of code are new or changed and 302 lines of the source are left out. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require check_reject_clean_starved past_nul.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.

(* check_round_trip (check_4, plain, 0x138ac): the stages from each call to the function's return. A stage starts
   at a callee's entry with the frame invariant CR, runs the callee through its wrapper, the machine stretch after
   the callee's return, and the next stage. The stages are written from the last call back. *)

#[local] Set Default Proof Using "All".

(* The function's post (check_round_trip_contract), for an entry FP state fx0. *)
Definition crt_post {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (L : layout) (A : astate)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (Lam : list (Z * Z)) (peak cnt : Z)
    (bnd : sbound) (fx0 : YK11.FPState) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' peak' cnt',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    fregs_kept fx0 fx' /\ frm_zero (@fp_csr fx') /\
    ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
    call_post_k B (aa_MR API) CRT_STK L A regs mem md alloc_statics L' A' regs' mem' md' /\
    (st_init_done A = true -> st_init_done A' = true) /\
    keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
    peak <= peak' /\ cnt <= cnt' <= cnt + CRT_ALLOCS /\
    ledger B L' A' mem' Lam peak' cnt' (2 ^ 64 - 1) /\
    res_ok_slots A' bnd.

Lemma fk_trans : forall f1 f2 f3, fregs_kept f1 f2 -> fregs_kept f2 f3 -> fregs_kept f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma fk_refl : forall f, fregs_kept f f.
Proof. intros f r _. reflexivity. Qed.

Lemma bat_nil : forall b, bat b [] [] = b.
Proof. intros [l y c]. unfold bat. cbn [sb_live sb_bytes sb_cap lsum length]. f_equal; lia. Qed.

Section ST.
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

(* The frame's stack pointer and the callee-saved registers the function does not touch. *)
Definition RF (R : bvmap 5 word) : Prop :=
  getr R 2 = Z_to_bv 64 (spZ regs - 336) /\
  forall k, k = 3 \/ k = 4 \/ k = 26 \/ k = 27 -> getr R (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k).

Lemma RF_pres : forall R R', regs_preserved R R' -> RF R -> RF R'.
Proof.
  intros R R' HP (Q2 & QG). split; [rewrite <- Q2; exact (HP 2 ltac:(unfold callee_saved; lia))|].
  intros k Hk. rewrite <- (QG k Hk). exact (HP k ltac:(unfold callee_saved; lia)).
Qed.

Lemma RF_getr : forall R R', (forall r, getr R' r = getr R r) -> RF R -> RF R'.
Proof. intros R R' HG. apply RF_pres. intros r _. apply HG. Qed.

Lemma RF_mk : forall R0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  RF R0 -> sp = Z_to_bv 64 (spZ regs - 336) -> gp = getr R0 3 -> tp = getr R0 4 -> s10 = getr R0 26 ->
  s11 = getr R0 27 ->
  RF (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Proof.
  intros R0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (Q2 & QG) E2 E3 E4 E26 E27. subst sp gp tp s10 s11.
  split; [reflexivity|]. intros k Hk. rewrite <- (QG k Hk).
  destruct Hk as [->|[->|[->| ->]]]; reflexivity.
Qed.

Lemma crt_HRA : YK0s.ret_ok (getr regs 1).
Proof. pose proof PRE as (_ & _ & _ & HRA & _). exact HRA. Qed.

Lemma crt_spr : 0 <= spZ regs - 336 /\ spZ regs - 336 + 336 <= 2 ^ 64 /\ alloc_ceiling + 14000 <= spZ regs - 336.
Proof. pose proof (crt_sp B API L A regs mem md PRE) as (H1 & H2 & _). pose proof alloc_ceiling_val. lia. Qed.

(* The post from the frame invariant with nothing left allocated. *)
Lemma crt_fin : forall Lc Ac memc mdc Lamc peakc cntc Nc (fx' : YK11.FPState) regs',
  CRs [] [] Lc Ac memc mdc Lamc peakc cntc Nc -> cntc <= cnt + CRT_ALLOCS ->
  fregs_kept fx0 fx' -> frm_zero (@fp_csr fx') -> regs_preserved regs regs' ->
  post (mkCfg (@mkst fx' regs' (getr regs 1) memc (seg_rom (ms_segs B))) mdc).
Proof.
  intros Lc Ac memc mdc Lamc peakc cntc Nc fx' regs' CRc HC FK FRM RP.
  pose proof CRc as ((MID & _ & UB & INI & RA & GK & _) & _ & LG & PK & CN & PM & RS & _).
  exists fx', Lc, Ac, regs', memc, mdc, peakc, cntc.
  split; [reflexivity|]. split; [exact FK|]. split; [exact FRM|].
  split; [rewrite SEG; exact RA|]. split; [exact GK|].
  split; [exact (kb_post B API _ _ _ _ _ _ _ _ _ _ _ _ MID RP)|].
  split; [intros _; exact INI|].
  split; [exact (check_reject_clean_starved.crs_keep_of_mid B API _ _ _ _ _ _ _ _ _ _ _ MID UB)|].
  split; [exact UB|]. split; [exact PK|]. split; [lia|].
  split; [exact (ledger_perm B Lc Ac memc Lamc Lam peakc cntc _ PM LG)|].
  rewrite <- (bat_nil bnd). exact RS.
Qed.


Lemma crt_nd : forall X P Lc Ac memc mdc Lamc pk cn Nc, CRs X P Lc Ac memc mdc Lamc pk cn Nc -> List.NoDup X.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc CRc.
  exact (NoDup_map_inv _ _ (cr_nodup B API L A regs mem md Lam peak cnt bnd X P Lc Ac memc mdc Lamc pk cn Nc CRc)).
Qed.

Lemma perm_disj : forall {T : Type} (X D Y : list T) y y', List.NoDup X -> Permutation X (D ++ Y) ->
  In y D -> In y' Y -> y <> y'.
Proof.
  intros T X D Y y y' ND PX Hy Hy' ->.
  pose proof (Permutation_NoDup PX ND) as ND'.
  exact (crt_nd_app_not D Y y' ND' Hy Hy').
Qed.

Lemma perm_in : forall {T : Type} (X Z1 : list T) y, Permutation X Z1 -> In y Z1 -> In y X.
Proof. intros T X Z1 y PX H. exact (Permutation_in _ (Permutation_sym PX) H). Qed.

(* A byte of an entry of X: below the frame, not a static, and in no other entry's block. *)
Lemma cr_xin : forall X P Lc Ac memc mdc Lamc pk cn Nc a k x,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> In (a, k) X -> a - 16 <= x < a + k ->
  ~ alloc_statics x /\ 4096 <= x < alloc_ceiling /\ ~ in_img B x /\
  In (a - 16, k + 16) (blocks Lc Ac) /\
  (forall a' k', In (a', k') X -> (a', k') <> (a, k) -> ~ (a' - 16 <= x < a' + k')) /\
  (forall w n, In (w, n) P -> ~ (w <= x < w + n)).
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc a k x CRc Hin Hx.
  pose proof CRc as (((HMc & _) & _) & (INC & ND & _) & _).
  assert (Hb : forall a' k', In (a', k') X -> In (a' - 16, k' + 16) (blocks Lc Ac)).
  { intros a' k' H. apply INC. apply in_or_app. right. change (a' - 16, k' + 16) with (xblk (a', k')).
    apply in_map. exact H. }
  destruct (crt_blk B API GF AX Lc Ac memc mdc (a - 16) (k + 16) (x - (a - 16)) HMc (Hb a k Hin) ltac:(lia))
    as (R & NI & _ & NS).
  replace (a - 16 + (x - (a - 16))) with x in R, NI, NS by lia.
  split; [exact NS|]. split; [lia|]. split; [exact NI|]. split; [exact (Hb a k Hin)|]. split.
  - intros a' k' H' Hne Hx'.
    apply (crt_blk_disj B API Lc Ac memc mdc (a - 16) (k + 16) (a' - 16) (k' + 16) x HMc (Hb a k Hin) (Hb a' k' H'));
      [|lia|lia].
    intros E. injection E as E1 E2. apply Hne. f_equal; lia.
  - intros w n H' Hx'.
    assert (Hw : In (w, n) (blocks Lc Ac)) by (apply INC; apply in_or_app; left; exact H').
    apply (crt_blk_disj B API Lc Ac memc mdc (a - 16) (k + 16) w n x HMc (Hb a k Hin) Hw); [|lia|lia].
    intros E. assert (Hm : In (w, n) (map xblk X)) by (rewrite <- E; change (a - 16, k + 16) with (xblk (a, k));
      apply in_map; exact Hin).
    apply NoDup_ListNoDup in ND. exact (crt_nd_app_not P (map xblk X) (w, n) ND H' Hm).
Qed.

Lemma cr_blkset : forall X P Lc Ac memc mdc Lamc pk cn Nc D x,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> incl D X -> blk_set D x ->
  exists a k, In (a, k) D /\ a - 16 <= x < a + k /\ 4096 <= x < alloc_ceiling.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc D x CRc HI (a & k & Ha & Hx).
  destruct (cr_xin X P Lc Ac memc mdc Lamc pk cn Nc a k x CRc (HI _ Ha) Hx) as (_ & R & _).
  exists a, k. split; [exact Ha|]. split; [exact Hx | exact R].
Qed.

Lemma crt_stat_lt : forall x, alloc_statics x -> 0 <= x < alloc_ceiling.
Proof. intros x Hx. exact (proj1 (proj2 (crt_GS2 B API GF x Hx))). Qed.

(* Raw bytes of an entry of X across a callee that neither freed nor wrote it. *)
Lemma cr_x_raw : forall X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' a k (w : word),
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> cs B API (spZ regs - 336) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  In (a, k) X -> ~ G (a - 16) (k + 16) -> a - 16 <= bv_unsigned w < a + k -> ~ E (bv_unsigned w) ->
  memc' w = memc w.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' a k w CRc CS Hin HG Hx HE.
  destruct (cr_xin X P Lc Ac memc mdc Lamc pk cn Nc a k _ CRc Hin Hx) as (_ & R & NI & Hb & _).
  destruct (cs_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ _ _ CS Hb HG) as [_ H].
  apply crt_raw; [apply (crt_fs_none B SEG); right; split; [lia | exact NI]|]. apply H; [lia | exact HE].
Qed.

(* Raw bytes of the frame above a callee's window across the callee. *)
Lemma cr_f_raw : forall X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' (w : word),
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> cs B API (spZ regs - 336) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  spZ regs - 336 <= bv_unsigned w -> ~ E (bv_unsigned w) -> memc' w = memc w.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' w CRc CS Hx HE.
  pose proof CRc as (((HMc & _) & _) & _). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rw.
  apply crt_raw; [apply (crt_fs_none B SEG); left; lia|].
  destruct (cs_hi B API SEG ERR _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned w) CS HMc) as [H _]; [lia | lia | exact HE |].
  exact H.
Qed.

(* A tree in the frame across a callee that neither freed nor wrote its node or its blocks. *)
Lemma cr_node_keep : forall X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' Lamc' p t D,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> cs B API (spZ regs - 336) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  pj_node rsegs memc (lin Lamc) p t D -> incl D X -> spZ regs - 336 <= p ->
  (forall x, p <= x < p + 56 -> ~ E x) ->
  (forall a k, In (a, k) D -> ~ G (a - 16) (k + 16) /\ forall x, a <= x < a + k -> ~ E x) ->
  (forall a k, In (a, k) D -> lin Lamc' a k) ->
  pj_node rsegs memc' (lin Lamc') p t D.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' Lamc' p t D CRc CS ND HI Hp HEf HD HL.
  apply (pj_node_frame rsegs t memc (lin Lamc) memc' (lin Lamc') p D ND HL).
  intros w [Hw|([a k] & Hb & Hh)].
  2: unfold pj_holds in Hh; cbn [fst snd] in Hh.
  - apply (cr_f_raw X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' w CRc CS ltac:(lia) (HEf _ Hw)).
  - destruct (HD a k Hb) as (HG & HE).
    exact (cr_x_raw X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' a k w CRc CS (HI _ Hb) HG
      ltac:(lia) (HE _ Hh)).
Qed.

Lemma crt_spo : forall o, 0 <= o <= 336 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (spZ regs - 336)) + o) = Z_to_bv 64 (spZ regs - 336 + o).
Proof. intros o Ho. pose proof crt_spr as (Hs1 & Hs2 & Hs3). rewrite MState.unsigned_lit by lia. reflexivity. Qed.

Lemma crt_lin_perm : forall Lamc Y Z1 a k, Permutation Lamc (Y ++ Lam) -> incl Z1 Y -> In (a, k) Z1 -> lin Lamc a k.
Proof.
  intros Lamc Y Z1 a k PM HI H. unfold lin. apply (perm_in Lamc (Y ++ Lam)); [exact PM|].
  apply in_or_app. left. exact (HI _ H).
Qed.

Lemma incl_perm_l : forall {T : Type} (X D Y : list T), Permutation X (D ++ Y) -> incl D X.
Proof. intros T X D Y PX y Hy. apply (perm_in X (D ++ Y)); [exact PX | apply in_or_app; left; exact Hy]. Qed.

Lemma incl_perm_r : forall {T : Type} (X D Y : list T), Permutation X (D ++ Y) -> incl Y X.
Proof. intros T X D Y PX y Hy. apply (perm_in X (D ++ Y)); [exact PX | apply in_or_app; right; exact Hy]. Qed.

Lemma cr_pin : forall X P Lc Ac memc mdc Lamc pk cn Nc w n x,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> In (w, n) P -> w <= x < w + n ->
  ~ alloc_statics x /\ 4096 <= x < alloc_ceiling /\ ~ in_img B x /\
  (forall a k, In (a, k) X -> ~ (a - 16 <= x < a + k)).
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc w n x CRc Hin Hx.
  pose proof CRc as (((HMc & _) & _) & (INC & _) & _).
  assert (Hw : In (w, n) (blocks Lc Ac)) by (apply INC; apply in_or_app; left; exact Hin).
  destruct (crt_blk B API GF AX Lc Ac memc mdc w n (x - w) HMc Hw ltac:(lia)) as (R & NI & _ & NS).
  replace (w + (x - w)) with x in R, NI, NS by lia.
  split; [exact NS|]. split; [lia|]. split; [exact NI|].
  intros a k Ha Hx'. destruct (cr_xin X P Lc Ac memc mdc Lamc pk cn Nc a k x CRc Ha Hx') as (_ & _ & _ & _ & _ & HP).
  exact (HP w n Hin Hx).
Qed.

(* What a callee wrote, relative to a tree with node p and blocks D (or an entry's bytes, D = [it]): statics, the
   frame outside the node, blocks of other entries before or after the call, blocks of malloc'd buffers. *)
Definition Eok (X P X' P' : list (Z * Z)) (p : Z) (D : list (Z * Z)) (E : Z -> Prop) : Prop :=
  forall x, E x -> alloc_statics x \/ (spZ regs - 336 <= x /\ ~ (p <= x < p + 56)) \/
    (exists a k, (In (a, k) X \/ In (a, k) X') /\ ~ In (a, k) D /\ a - 16 <= x < a + k) \/
    (exists w n, (In (w, n) P \/ In (w, n) P') /\ w <= x < w + n).

Lemma eok_x : forall X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E a k x,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  Eok X P X' P' p D E -> In (a, k) D -> In (a, k) X -> In (a, k) X' -> a - 16 <= x < a + k -> ~ E x.
Proof.
  intros X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E a k x CRc CR' HE Hak HX HX'
    Hx Ex.
  destruct (cr_xin X P Lc Ac memc mdc Lamc pk cn Nc a k x CRc HX Hx) as (NS & R & _ & _ & HO & HPn).
  destruct (cr_xin X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' a k x CR' HX' Hx) as (_ & _ & _ & _ & HO' & HPn').
  pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  destruct (HE x Ex) as [Hs|[(Hf & _)|[(a' & k' & Ha' & Hn & Hax)|(w & n & Hw & Hwx)]]].
  - exact (NS Hs).
  - lia.
  - assert (Hne : (a', k') <> (a, k)) by (intros E'; injection E' as -> ->; exact (Hn Hak)).
    destruct Ha' as [Ha'|Ha']; [exact (HO a' k' Ha' Hne Hax) | exact (HO' a' k' Ha' Hne Hax)].
  - destruct Hw as [Hw|Hw]; [exact (HPn w n Hw Hwx) | exact (HPn' w n Hw Hwx)].
Qed.

Lemma eok_f : forall X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E x,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  Eok X P X' P' p D E -> spZ regs - 336 <= p -> p <= x < p + 56 -> ~ E x.
Proof.
  intros X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E x CRc CR' HE Hp Hx Ex.
  pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  destruct (HE x Ex) as [Hs|[(_ & Hf)|[(a & k & Ha & _ & Hax)|(w & n & Hw & Hwx)]]].
  - pose proof (crt_stat_lt x Hs). lia.
  - exact (Hf Hx).
  - destruct Ha as [Ha|Ha].
    + destruct (cr_xin X P Lc Ac memc mdc Lamc pk cn Nc a k x CRc Ha Hax) as (_ & R & _). lia.
    + destruct (cr_xin X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' a k x CR' Ha Hax) as (_ & R & _). lia.
  - destruct Hw as [Hw|Hw].
    + destruct (cr_pin X P Lc Ac memc mdc Lamc pk cn Nc w n x CRc Hw Hwx) as (_ & R & _). lia.
    + destruct (cr_pin X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' w n x CR' Hw Hwx) as (_ & R & _). lia.
Qed.

(* A tree in the frame across a callee, from its write set. *)
Lemma cr_keep_node : forall X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p t D,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  cs B API (spZ regs - 336) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  pj_node rsegs memc (lin Lamc) p t D -> incl D X -> incl D X' -> spZ regs - 336 <= p ->
  Eok X P X' P' p D E -> (forall a k, In (a, k) D -> ~ G (a - 16) (k + 16)) ->
  pj_node rsegs memc' (lin Lamc') p t D.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p t D CRc CR' CS ND HI HI'
    Hp HE HG.
  apply (cr_node_keep X P Lc Ac memc mdc Lamc pk cn Nc K E G Lc' Ac' memc' mdc' Lamc' p t D CRc CS ND HI Hp).
  - intros x Hx. exact (eok_f X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E x
      CRc CR' HE Hp Hx).
  - intros a k Hak. split; [exact (HG a k Hak)|]. intros x Hx.
    exact (eok_x X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E a k x CRc CR' HE
      Hak (HI _ Hak) (HI' _ Hak) ltac:(lia)).
  - intros a k Hak. unfold lin.
    exact (cr_in_lam B API L A regs mem md Lam peak cnt bnd X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' a k CR'
      (HI' _ Hak)).
Qed.

(* The bytes of an entry across a callee, from its write set. *)
Lemma cr_keep_mb : forall X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p a k x,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  cs B API (spZ regs - 336) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  In (a, k) X -> In (a, k) X' -> Eok X P X' P' p [(a, k)] E -> ~ G (a - 16) (k + 16) -> a - 16 <= x < a + k ->
  mbyte rsegs memc' x = mbyte rsegs memc x.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p a k x CRc CR' CS HX HX'
    HE HG Hx.
  destruct (cr_xin X P Lc Ac memc mdc Lamc pk cn Nc a k x CRc HX Hx) as (_ & _ & _ & Hb & _).
  destruct (cs_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ _ _ CS Hb HG) as [_ H]. apply H; [lia|].
  exact (eok_x X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p [(a, k)] E a k x CRc CR'
    HE (or_introl eq_refl) HX HX' Hx).
Qed.

Lemma cr_keep_bytes : forall X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p a k
    y bs,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  cs B API (spZ regs - 336) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  In (a, k) X -> In (a, k) X' -> Eok X P X' P' p [(a, k)] E -> ~ G (a - 16) (k + 16) ->
  Mem.bytes_at rsegs memc y bs -> a <= y -> y + Z.of_nat (length bs) <= a + k ->
  Mem.bytes_at rsegs memc' y bs.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p a k y bs CRc CR' CS HX
    HX' HE HG BS H1 H2.
  apply (crt_bytes_keep memc memc' y bs BS). intros i Hi.
  exact (cr_keep_mb X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p a k i CRc CR'
    CS HX HX' HE HG ltac:(lia)).
Qed.

Lemma cr_perm : forall X X' P Lc Ac memc mdc Lamc pk cn Nc, Permutation X X' ->
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P Lc Ac memc mdc Lamc pk cn Nc.
Proof.
  intros X X' P Lc Ac memc mdc Lamc pk cn Nc HP (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc).
  split; [exact GIc|]. split.
  { eapply nb_perm; [exact NBc|]. apply Permutation_app_head. apply Permutation_map. exact HP. }
  split; [exact LGc|]. split; [exact PKc|]. split; [exact CNc|]. split.
  { eapply perm_trans; [exact PMc|]. apply Permutation_app_tail. exact HP. }
  rewrite <- (bat_perm bnd X X' P HP). split; assumption.
Qed.

(* fuzz_free of an entry: its write set misses every tree and entry that does not hold it. *)
Lemma eok_ff : forall X P p D f kf, ~ In (f, kf) D -> Eok ((f, kf) :: X) P X P p D (free_writes f kf).
Proof.
  intros X P p D f kf HD x [Hx|(_ & Hx)].
  - left. unfold alloc_statics. left. exact Hx.
  - right. right. left. exists f, kf. split; [left; left; reflexivity|]. split; [exact HD | exact Hx].
Qed.

Lemma keep_ff : forall X P Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K p t D f kf,
  CRs ((f, kf) :: X) P Lc Ac memc mdc Lamc pk cn Nc -> CRs X P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  cs B API (spZ regs - 336) K (free_writes f kf) (fun a n => (a, n) = (f - 16, kf + 16))
    Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  pj_node rsegs memc (lin Lamc) p t D -> incl D X -> spZ regs - 336 <= p ->
  pj_node rsegs memc' (lin Lamc') p t D.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K p t D f kf CRc CR' CS ND HI Hp.
  pose proof (crt_nd _ _ _ _ _ _ _ _ _ _ CRc) as NDX. apply NoDup_cons_iff in NDX as [NF _].
  assert (HD : ~ In (f, kf) D) by (intros H; exact (NF (HI _ H))).
  apply (cr_keep_node ((f, kf) :: X) P Lc Ac memc mdc Lamc pk cn Nc X P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K _ _ p t
    D CRc CR' CS ND (fun y Hy => or_intror (HI y Hy)) HI Hp (eok_ff X P p D f kf HD)).
  intros a k Hak E. cbv beta in E. injection E as E1 E2.
  assert (a = f) by lia. assert (k = kf) by lia. subst a k. exact (HD Hak).
Qed.

(* A machine stretch run on the normalized memory, read back on the real one. *)
Lemma crt_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_rel_shape : forall s R F pc fc m0 ro, ms_rel rsegs s (MS R F pc fc None m0 ro) ->
  s = MS R F pc fc None (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [R' F' pc' svc' rv' fc' m' ro'] R F pc fc m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma crt_evn : forall (R : bvmap 5 word) F pc fc m (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop),
  ro_agree rsegs m ->
  Exec.evt rsegs (fun ms => exists R' pc' m0, ms = MS R' F pc' fc None m0 (seg_rom rsegs) /\ Q R' pc' m0)
    (MS R F pc fc None (normalize rsegs m) (seg_rom rsegs)) ->
  Exec.evt rsegs (fun ms => exists R' pc' m', ms = MS R' F pc' fc None m' (seg_rom rsegs) /\
    exists m0, Q R' pc' m0 /\ mem_rel rsegs m' m0 /\ ro_same rsegs m m')
    (MS R F pc fc None m (seg_rom rsegs)).
Proof.
  intros R F pc fc m Q RA H.
  eapply Exec.evt_mono; [exact (evt_normalize rsegs _ R F pc fc None m (seg_rom rsegs) crt_wx RA H)|].
  intros s (s0 & (R' & pc' & m0 & -> & HQ) & REL & ROS).
  destruct (crt_rel_shape s _ _ _ _ _ _ REL) as [Es HR].
  exists R', pc', (ms_mem s). split; [exact Es|]. exists m0. split; [exact HQ|]. split; [exact HR | exact ROS].
Qed.

(* CR across a machine stretch that writes only the frame below the saved registers. *)
Lemma cr_munch : forall X P Lc Ac memc mdc Lamc pk cn Nc W m',
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> munch W memc m' -> wmono rsegs memc m' -> ro_agree rsegs m' ->
  (forall x, ~ outside W x -> spZ regs - CRT_STK <= x < spZ regs - 88) ->
  CRs X P Lc Ac m' mdc Lamc pk cn Nc.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc W m' (GIc & NBc & LGc & PKc & CNc & PMc & RSc & HCc) MU WM RA HW.
  pose proof GIc as ((HMc & _) & _).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp1 & _). pose proof alloc_ceiling_val as Hacv.
  split; [exact (gi_munch B API SEG GF AX L A regs mem md PRE Lc Ac memc mdc W m' GIc MU WM RA
    (fun x Hx => or_introl (HW x Hx)))|].
  split; [exact NBc|]. split.
  { apply (HsKindB.ledger_munch B API Lc Ac memc mdc m' W Lamc pk cn _ HMc LGc MU).
    intros x Hx. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. pose proof (HW x Ho).
    unfold CRT_STK, ALLOC_STACK in *. lia. }
  repeat (split; [assumption|]). assumption.
Qed.

Lemma cr_eqm : forall X P Lc Ac memc mdc Lamc pk cn Nc m',
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> (forall x, m' x = memc x) -> CRs X P Lc Ac m' mdc Lamc pk cn Nc.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc m' CRc E.
  pose proof CRc as ((_ & _ & _ & _ & RA & _) & _).
  apply (cr_munch X P Lc Ac memc mdc Lamc pk cn Nc [] m' CRc).
  - intros x _. exact (E x).
  - intros x Hx. unfold wview. rewrite E. exact Hx.
  - intros a Ha. unfold mrd. rewrite E. exact (RA a Ha).
  - intros x Hx. exfalso. apply Hx. exact I.
Qed.

Lemma node_eqm : forall m m' lblk p t D, pj_node rsegs m lblk p t D -> (forall a k, In (a, k) D -> lblk a k) ->
  (forall x, m' x = m x) -> pj_node rsegs m' lblk p t D.
Proof.
  intros m m' lblk p t D ND HL E. apply (pj_node_frame rsegs t m lblk m' lblk p D ND HL). intros x _. exact (E x).
Qed.

Lemma cr_lin : forall X P Lc Ac memc mdc Lamc pk cn Nc D, CRs X P Lc Ac memc mdc Lamc pk cn Nc -> incl D X ->
  forall a k, In (a, k) D -> lin Lamc a k.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc D CRc HI a k H.
  exact (cr_in_lam B API L A regs mem md Lam peak cnt bnd X P Lc Ac memc mdc Lamc pk cn Nc a k CRc (HI _ H)).
Qed.

Lemma cr_x_lo : forall X P Lc Ac memc mdc Lamc pk cn Nc a k, CRs X P Lc Ac memc mdc Lamc pk cn Nc -> In (a, k) X ->
  4112 <= a /\ a + k <= alloc_ceiling /\ a mod 16 = 0.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc a k CRc Hin. pose proof CRc as (((HMc & _) & _) & _ & LGc & _).
  pose proof (cr_in_lam B API L A regs mem md Lam peak cnt bnd X P Lc Ac memc mdc Lamc pk cn Nc a k CRc Hin) as Hl.
  destruct (ledger_block_range B API Lc Ac memc mdc Lamc pk cn _ a k HMc LGc Hl) as (H1 & H2 & _).
  split; [lia|]. split; [lia|]. exact (ledger_block_aligned B API Lc Ac memc mdc Lamc pk cn _ a k HMc LGc Hl).
Qed.

Lemma crt_mk_bytes : forall segs m a r, 0 <= a -> a + Z.of_nat r <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat r -> exists b, Mem.mrd segs m (Mem.wa (a + i)) = Some b) ->
  exists bs, length bs = r /\ Mem.bytes_at segs m a bs.
Proof.
  intros segs m a r. revert a. induction r as [|r IH]; intros a H0 H1 H.
  - exists []. split; [reflexivity|]. apply Mem.bytes_at_nil. lia.
  - destruct (H 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & Hbs).
    { intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn [length]; rewrite Hl; reflexivity|].
    change (b :: bs) with ([b] ++ bs). apply Mem.bytes_at_app. split.
    + split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. exact Hb.
    + cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact Hbs.
Qed.

(* The slack after a string in a ledger entry: the entry's bytes, then the block's slack. *)
Lemma crt_slack : forall X P Lc Ac memc mdc Lamc pk cn Nc z kz (s : list Z),
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> In (z, kz) Lamc -> Z.of_nat (length s) + 1 <= kz ->
  Mem.bytes_at rsegs memc z (map (Z_to_bv 8) (s ++ [0])) ->
  exists slack, Mem.bytes_at rsegs memc z (map (Z_to_bv 8) (s ++ [0]) ++ slack) /\
    Z.of_nat (length slack) = (- (z + Z.of_nat (length s) + 1)) mod 8.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc z kz s CRc Hin Hk BS.
  pose proof CRc as (((HMc & _) & _) & _ & LGc & _).
  destruct (crt_lam_blk B Lc Ac memc Lamc pk cn (2 ^ 64 - 1) z kz LGc Hin) as (Hb & Hk0 & _).
  destruct (ledger_block_range B API Lc Ac memc mdc Lamc pk cn _ z kz HMc LGc Hin) as (Hz1 & Hz2 & Hz3).
  pose proof alloc_ceiling_val as Hacv.
  pose proof (Z.mod_pos_bound (- (z + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hr.
  destruct (crt_mk_bytes rsegs memc (z + Z.of_nat (length s) + 1)
    (Z.to_nat ((- (z + Z.of_nat (length s) + 1)) mod 8)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia))
    as (sl & Hl & BS2).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia.
    assert (Hp : present memc (z + Z.of_nat (length s) + 1 + i)).
    { destruct (Z_lt_le_dec (z + Z.of_nat (length s) + 1 + i) (z + kz)) as [Hx|Hx].
      - replace (z + Z.of_nat (length s) + 1 + i) with (z + (Z.of_nat (length s) + 1 + i)) by lia.
        exact (ledger_block_present B API Lc Ac memc mdc Lamc pk cn _ z kz (Z.of_nat (length s) + 1 + i) HMc LGc Hin
          ltac:(lia)).
      - apply (BSP Lc Ac memc mdc (z - 16) (kz + 16) _ HMc Hb).
        replace (z - 16 + (kz + 16)) with (z + kz) by lia. Z.div_mod_to_equations. lia. }
    destruct Hp as [b Hb']. exists b. unfold Mem.mrd, Mem.wa. rewrite Hb'. reflexivity. }
  exists sl. split.
  - apply Mem.bytes_at_app. split; [exact BS|]. rewrite length_map, length_app. cbn [length].
    replace (z + Z.of_nat (length s + 1)) with (z + Z.of_nat (length s) + 1) by lia. exact BS2.
  - rewrite Hl, Z2Nat.id by lia. reflexivity.
Qed.

(* A byte of an entry block of the function's caller: no static, below the frame, in no block the function holds. *)
Lemma cr_lam_x : forall X P Lc Ac memc mdc Lamc pk cn Nc a k x,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> In (a, k) Lam -> a - 16 <= x < a + k ->
  ~ alloc_statics x /\ x < alloc_ceiling /\ In (a - 16, k + 16) (blocks Lc Ac) /\
  (forall a' k', In (a', k') X -> ~ (a' - 16 <= x < a' + k')) /\ (forall w n, In (w, n) P -> ~ (w <= x < w + n)).
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc a k x CRc Hin Hx.
  pose proof CRc as (((HMc & _) & _) & (INC & _ & NE) & _).
  pose proof (LG0_blk B L A mem Lam peak cnt LG0 a k Hin) as Hb0.
  pose proof (cr_entry_sub B API L A regs mem md PRE Lam peak cnt bnd X P Lc Ac memc mdc Lamc pk cn Nc CRc _ Hb0) as Hb.
  destruct (crt_blk B API GF AX Lc Ac memc mdc (a - 16) (k + 16) (x - (a - 16)) HMc Hb ltac:(lia)) as (R & _ & _ & NS).
  replace (a - 16 + (x - (a - 16))) with x in R, NS by lia.
  split; [exact NS|]. split; [lia|]. split; [exact Hb|]. split.
  - intros a' k' H' Hx'.
    assert (Hm : In (a' - 16, k' + 16) (P ++ map xblk X)).
    { apply in_or_app. right. change (a' - 16, k' + 16) with (xblk (a', k')). apply in_map. exact H'. }
    apply (crt_blk_disj B API Lc Ac memc mdc (a - 16) (k + 16) (a' - 16) (k' + 16) x HMc Hb (INC _ Hm)); [|lia|lia].
    intros E. apply (NE _ Hm). rewrite <- E. exact Hb0.
  - intros w n H' Hx'.
    assert (Hm : In (w, n) (P ++ map xblk X)) by (apply in_or_app; left; exact H').
    apply (crt_blk_disj B API Lc Ac memc mdc (a - 16) (k + 16) w n x HMc Hb (INC _ Hm)); [|lia|lia].
    intros E. apply (NE _ Hm). rewrite <- E. exact Hb0.
Qed.

Lemma eok_lam : forall X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E a k x,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  Eok X P X' P' p D E -> In (a, k) Lam -> a - 16 <= x < a + k -> ~ E x.
Proof.
  intros X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E a k x CRc CR' HE Hin Hx Ex.
  destruct (cr_lam_x X P Lc Ac memc mdc Lamc pk cn Nc a k x CRc Hin Hx) as (NS & R & _ & HX & HP).
  destruct (cr_lam_x X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' a k x CR' Hin Hx) as (_ & _ & _ & HX' & HP').
  pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  destruct (HE x Ex) as [Hs|[(Hf & _)|[(a' & k' & Ha' & _ & Hax)|(w & n & Hw & Hwx)]]].
  - exact (NS Hs).
  - lia.
  - destruct Ha' as [Ha'|Ha']; [exact (HX a' k' Ha' Hax) | exact (HX' a' k' Ha' Hax)].
  - destruct Hw as [Hw|Hw]; [exact (HP w n Hw Hwx) | exact (HP' w n Hw Hwx)].
Qed.

(* The bytes of a caller's entry block across a callee, from its write set. *)
Lemma cr_keep_lam : forall X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p D a k
    y bs,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  cs B API (spZ regs - 336) K E G Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  Eok X P X' P' p D E -> ~ G (a - 16) (k + 16) -> In (a, k) Lam ->
  Mem.bytes_at rsegs memc y bs -> a <= y -> y + Z.of_nat (length bs) <= a + k -> Mem.bytes_at rsegs memc' y bs.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc X' P' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K E G p D a k y bs CRc CR' CS HE
    HG Hin BS H1 H2.
  apply (crt_bytes_keep memc memc' y bs BS). intros i Hi.
  destruct (cr_lam_x X P Lc Ac memc mdc Lamc pk cn Nc a k i CRc Hin ltac:(lia)) as (_ & _ & Hb & _).
  destruct (cs_blk B API SEG _ _ _ _ _ _ _ _ _ _ _ _ _ _ CS Hb HG) as [_ H]. apply H; [lia|].
  exact (eok_lam X P X' P' Lc Ac memc mdc Lamc pk cn Nc Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' p D E a k i CRc CR' HE Hin
    ltac:(lia)).
Qed.

Ltac wfree := apply (w_free B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd LG0 (FREE _) FRE).
Ltac wffree := apply (w_ffree B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (FFREE _)).
Ltac wpfree := apply (w_pfree B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJF _)).
Ltac retok R1 := rewrite R1; vm_compute; reflexivity.
Ltac kbr HM := first [ exact (proj1 (kb_md B API _ _ _ _ HM)) | exact (proj2 (kb_md B API _ _ _ _ HM)) ].
(* getr R' k = v from getr R k = v across a callee that kept the callee-saved registers *)
Ltac sv RP R' H E n :=
  lazymatch type of H with getr _ ?k = ?v =>
    assert (E : getr R' k = v) by (rewrite <- H; exact (RP n ltac:(unfold callee_saved; lia))) end.
(* the K of a machine stretch: the frame registers, then register facts and the pc, memory unchanged *)
Ltac kfin R' RF' :=
  do 3 eexists; split; [reflexivity|];
  split; [apply (RF_mk R'); [exact RF' | reflexivity ..]|];
  repeat (split; [first [reflexivity | apply crt_spo; lia]|]); first [reflexivity | apply crt_spo; lia].

Section F.
Context {fx : YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

(* c25: free(same), then the epilogue *)
Lemma st25 : forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn,
  CRs [] [(same, sn)] Lc Ac memc mdc Lamc peakc cntc Nc -> cntc <= cnt + CRT_ALLOCS ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13d4c -> getr regsc 10 = Z_to_bv 64 same -> 0 < sn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 0x16454) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn CRc HC RFc R1 R10 Hn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  apply (w_free B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd LG0 (FREE fx) FRE [] [] [] Lc Ac regsc memc mdc
    Lamc peakc cntc Nc same sn post CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 Hn).
  intros Lc' Ac' regs' memc' mdc' RP CR' CS.
  pose proof (RF_pres _ _ RP RFc) as RF'.
  pose proof CR' as ((MID' & _ & _ & _ & _ & _ & FR') & _).
  pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d4c) memc' mdc'
    (fun R pc' m' => regs_preserved regs R /\ pc' = ret_pc (getr regs 1) /\ m' = memc')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. destruct RF' as (P2 & PG). rewrite P2.
    eapply Exec.evt_mono.
    - eapply crt_r26 with (xra := getr regs 1) (xs0 := getr regs 8) (xs1 := getr regs 9) (xs2 := getr regs 18)
        (xs3 := getr regs 19) (xs4 := getr regs 20) (xs5 := getr regs 21) (xs6 := getr regs 22)
        (xs7 := getr regs 23) (xs8 := getr regs 24) (xs9 := getr regs 25).
      + rewrite MState.unsigned_lit by lia. replace (spZ regs - 336 + 248) with (spZ regs - 88) by lia. exact FR'.
      + rewrite MState.unsigned_lit by lia. lia.
    - intros ms' ->. do 3 eexists. split; [reflexivity|]. split; [|split; reflexivity].
      apply check_reject_clean_starved.crs_rp;
        [ rewrite MState.unsigned_lit by lia; replace (spZ regs - 336 + 336) with (spZ regs) by lia; unfold spZ;
          apply Z_to_bv_bv_unsigned
        | exact (PG 3 ltac:(lia)) | exact (PG 4 ltac:(lia)) | reflexivity .. | exact (PG 26 ltac:(lia))
        | exact (PG 27 ltac:(lia)) ]. }
  intros RR pc2 mem2 regs2 (RPR & -> & ->) HG.
  apply SR_ret. rewrite (kb_ret_pc _ crt_HRA).
  exact (crt_fin Lc' Ac' memc' mdc' Lamc peakc cntc Nc fx regs2 CR' HC FK FRM (kb_preserved_getr _ _ _ RPR HG)).
Qed.

(* c24: free(want), then free(same) *)
Lemma st24 : forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn,
  CRs [] [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> cntc <= cnt + CRT_ALLOCS ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13d44 -> getr regsc 10 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 0x16454) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn CRc HC RFc R1 R10 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  apply (w_free B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd LG0 (FREE fx) FRE [] [(same, sn)] []
    Lc Ac regsc memc mdc Lamc peakc cntc Nc want wn post CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 Hwn).
  intros Lc' Ac' regs' memc' mdc' RP CR' CS.
  pose proof (RF_pres _ _ RP RFc) as RF'. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d44) memc' mdc'
    (fun R pc' m' => RF R /\ getr R 1 = Z_to_bv 64 0x13d4c /\ getr R 10 = Z_to_bv 64 same /\
       pc' = Z_to_bv 64 0x16454 /\ m' = memc')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, S18.
    eapply Exec.evt_mono; [apply crt_r25|]. intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & -> & ->) HG.
  apply (RF_getr _ _ HG) in RF2. rewrite <- HG in Q1, Q10.
  exact (st25 Lc' Ac' regs2 memc' mdc' Lamc peakc cntc Nc same sn CR' HC RF2 Q1 Q10 Hsn).
Qed.

(* c23: fuzz_free(text), then free(want) *)
Lemma st23 : forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq,
  CRs [(q, kq)] [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> cntc <= cnt + CRT_ALLOCS ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13d3c -> getr regsc 10 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq CRc HC RFc R1 R10 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  apply (w_ffree B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (FFREE fx) [] []
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc q kq post CRc R2 (RG 4 ltac:(lia))
    ltac:(retok R1) R10).
  intros Lc' Ac' regs' memc' mdc' Lamc' RP CR' CS.
  pose proof (RF_pres _ _ RP RFc) as RF'. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d3c) memc' mdc'
    (fun R pc' m' => RF R /\ getr R 1 = Z_to_bv 64 0x13d44 /\ getr R 10 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x16454 /\ m' = memc')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, S9, S18.
    eapply Exec.evt_mono; [apply crt_r24|]. intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q18 & -> & ->) HG.
  apply (RF_getr _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q18.
  exact (st24 Lc' Ac' regs2 memc' mdc' Lamc' peakc cntc Nc same sn want wn CR' HC RF2 Q1 Q10 Q18 Hsn Hwn).
Qed.

(* c22: fuzz_free(back), then fuzz_free(text) *)
Lemma st22 : forall Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1,
  CRs [(b1, k1); (q, kq)] [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> cntc <= cnt + CRT_ALLOCS ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13d34 -> getr regsc 10 = Z_to_bv 64 b1 ->
  getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same ->
  0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 CRc HC RFc R1 R10 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  apply (w_ffree B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (FFREE fx) [] [(q, kq)]
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc b1 k1 post CRc R2 (RG 4 ltac:(lia))
    ltac:(retok R1) R10).
  intros Lc' Ac' regs' memc' mdc' Lamc' RP CR' CS.
  pose proof (RF_pres _ _ RP RFc) as RF'. sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d34) memc' mdc'
    (fun R pc' m' => RF R /\ getr R 1 = Z_to_bv 64 0x13d3c /\ getr R 10 = Z_to_bv 64 q /\
       getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x141c4 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r23|]. intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q9 & Q18 & -> & ->) HG.
  apply (RF_getr _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q9, Q18.
  exact (st23 Lc' Ac' regs2 memc' mdc' Lamc' peakc cntc Nc same sn want wn q kq CR' HC RF2 Q1 Q10 Q9 Q18 Hsn Hwn).
Qed.

(* c21: pj_free(&doc), then fuzz_free(back) *)
Lemma st21 : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> cntc <= cnt + CRT_ALLOCS ->
  Permutation X (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) td Dd -> (depth td <= 2)%nat ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13d2c -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 192) ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_FREE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd CRc HC PX ND Hd RFc R1 R10
    R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  apply (w_pfree B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJF fx)
    X _ Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 192) td Dd [(b1, k1); (q, kq)] post FRM CRc R2
    (RG 4 ltac:(lia)) ltac:(retok R1) R10 ltac:(lia) ltac:(lia) ND Hd PX).
  intros Lc' Ac' regs' memc' mdc' Lamc' RP CR' CS _ _.
  pose proof (RF_pres _ _ RP RFc) as RF'.
  sv RP regs' R21 S21 21. sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d2c) memc' mdc'
    (fun R pc' m' => RF R /\ getr R 1 = Z_to_bv 64 0x13d34 /\ getr R 10 = Z_to_bv 64 b1 /\
       getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\
       pc' = Z_to_bv 64 0x141c4 /\ m' = memc')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r22|]. intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply (RF_getr _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q8, Q9, Q18.
  exact (st22 Lc' Ac' regs2 memc' mdc' Lamc' peakc cntc Nc same sn want wn q kq b1 k1 CR' HC RF2 Q1 Q10 Q8 Q9 Q18
    Hsn Hwn).
Qed.

(* c20: pj_free(&back), then pj_free(&doc) *)
Lemma st20 : forall X Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> cntc <= cnt + CRT_ALLOCS ->
  Permutation X (Db ++ Y) -> Permutation Y (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 24) tb Db -> (depth tb <= 2)%nat ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) td Dd -> (depth td <= 2)%nat ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13d24 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 24) ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_FREE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db CRc HC PX PY NB Hdb ND
    Hdd RFc R1 R10 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  pose proof (crt_nd _ _ _ _ _ _ _ _ _ _ CRc) as NDX.
  apply (w_pfree B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJF fx)
    X _ Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 24) tb Db Y post FRM CRc R2 (RG 4 ltac:(lia))
    ltac:(retok R1) R10 ltac:(lia) ltac:(lia) NB Hdb PX).
  intros Lc' Ac' regs' memc' mdc' Lamc' RP CR' CS _ _.
  assert (ND' : pj_node rsegs memc' (lin Lamc') (spZ regs - 336 + 192) td Dd).
  { apply (cr_keep_node X _ Lc Ac memc mdc Lamc peakc cntc Nc Y _ Lc' Ac' memc' mdc' Lamc' peakc cntc Nc _ _ _ _ td Dd
      CRc CR' CS ND).
    - intros y Hy. apply (incl_perm_r X Db Y PX). exact (incl_perm_l Y Dd _ PY _ Hy).
    - exact (incl_perm_l Y Dd _ PY).
    - lia.
    - intros x (_ & [Hx|[(a & k & Ha & Hax)|Hs]]).
      + right. left. split; lia.
      + right. right. left. exists a, k. split; [left; exact (incl_perm_l X Db Y PX _ Ha)|]. split; [|exact Hax].
        intros Hd'. exact (perm_disj X Db Y (a, k) (a, k) NDX PX Ha (incl_perm_l Y Dd _ PY _ Hd') eq_refl).
      + left. exact Hs.
    - intros a k Hak Hf. unfold freed in Hf. replace (a - 16 + 16) with a in Hf by lia.
      replace (k + 16 - 16) with k in Hf by lia.
      exact (perm_disj X Db Y (a, k) (a, k) NDX PX Hf (incl_perm_l Y Dd _ PY _ Hak) eq_refl). }
  pose proof (RF_pres _ _ RP RFc) as RF'.
  sv RP regs' R21 S21 21. sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d24) memc' mdc'
    (fun R pc' m' => RF R /\ getr R 1 = Z_to_bv 64 0x13d2c /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 192) /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x145a4 /\ m' = memc')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r21; rewrite MState.unsigned_lit by lia; lia|]. intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply (RF_getr _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q21, Q8, Q9, Q18.
  exact (st21 Y Lc' Ac' regs2 memc' mdc' Lamc' peakc cntc Nc same sn want wn q kq b1 k1 td Dd CR' HC PY ND' Hdd RF2
    Q1 Q10 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c19: fuzz_free(file), then pj_free(&back) *)
Lemma st19 : forall X Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db f kf,
  CRs ((f, kf) :: X) [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> cntc <= cnt + CRT_ALLOCS ->
  Permutation X (Db ++ Y) -> Permutation Y (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 24) tb Db -> (depth tb <= 2)%nat ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) td Dd -> (depth td <= 2)%nat ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13d1c -> getr regsc 10 = Z_to_bv 64 f ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db f kf CRc HC PX PY NB Hdb
    ND Hdd RFc R1 R10 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  apply (w_ffree B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (FFREE fx) [] X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc f kf post CRc R2 (RG 4 ltac:(lia))
    ltac:(retok R1) R10).
  intros Lc' Ac' regs' memc' mdc' Lamc' RP CR' CS.
  assert (IB : incl Db X) by exact (incl_perm_l X Db Y PX).
  assert (ID : incl Dd X) by (intros y Hy; apply (incl_perm_r X Db Y PX); exact (incl_perm_l Y Dd _ PY _ Hy)).
  pose proof (keep_ff X _ Lc Ac memc mdc Lamc peakc cntc Nc Lc' Ac' memc' mdc' Lamc' peakc cntc Nc _ _ tb Db f kf
    CRc CR' CS NB IB ltac:(lia)) as NB'.
  pose proof (keep_ff X _ Lc Ac memc mdc Lamc peakc cntc Nc Lc' Ac' memc' mdc' Lamc' peakc cntc Nc _ _ td Dd f kf
    CRc CR' CS ND ID ltac:(lia)) as ND'.
  pose proof (RF_pres _ _ RP RFc) as RF'.
  sv RP regs' R21 S21 21. sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d1c) memc' mdc'
    (fun R pc' m' => RF R /\ getr R 1 = Z_to_bv 64 0x13d24 /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 24) /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x145a4 /\ m' = memc')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r20; rewrite MState.unsigned_lit by lia; lia|]. intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply (RF_getr _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q21, Q8, Q9, Q18.
  exact (st20 X Y Lc' Ac' regs2 memc' mdc' Lamc' peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db CR' HC PX PY NB'
    Hdb ND' Hdd RF2 Q1 Q10 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c18: fuzz_free(got), then fuzz_free(file) *)
Lemma st18 : forall X Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db f kf g kg,
  CRs ((g, kg) :: (f, kf) :: X) [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc <= cnt + CRT_ALLOCS ->
  Permutation X (Db ++ Y) -> Permutation Y (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 24) tb Db -> (depth tb <= 2)%nat ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) td Dd -> (depth td <= 2)%nat ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13d14 -> getr regsc 10 = Z_to_bv 64 g -> getr regsc 22 = Z_to_bv 64 f ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db f kf g kg CRc HC PX PY NB
    Hdb ND Hdd RFc R1 R10 R22 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  apply (w_ffree B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (FFREE fx) [] ((f, kf) :: X)
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc g kg post CRc R2 (RG 4 ltac:(lia))
    ltac:(retok R1) R10).
  intros Lc' Ac' regs' memc' mdc' Lamc' RP CR' CS.
  assert (IB : incl Db ((f, kf) :: X)) by (intros y Hy; right; exact (incl_perm_l X Db Y PX _ Hy)).
  assert (ID : incl Dd ((f, kf) :: X))
    by (intros y Hy; right; apply (incl_perm_r X Db Y PX); exact (incl_perm_l Y Dd _ PY _ Hy)).
  pose proof (keep_ff ((f, kf) :: X) _ Lc Ac memc mdc Lamc peakc cntc Nc Lc' Ac' memc' mdc' Lamc' peakc cntc Nc _ _
    tb Db g kg CRc CR' CS NB IB ltac:(lia)) as NB'.
  pose proof (keep_ff ((f, kf) :: X) _ Lc Ac memc mdc Lamc peakc cntc Nc Lc' Ac' memc' mdc' Lamc' peakc cntc Nc _ _
    td Dd g kg CRc CR' CS ND ID ltac:(lia)) as ND'.
  pose proof (RF_pres _ _ RP RFc) as RF'.
  sv RP regs' R22 S22 22. sv RP regs' R21 S21 21. sv RP regs' R8 S8 8. sv RP regs' R9 S9 9.
  sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13d14) memc' mdc'
    (fun R pc' m' => RF R /\ getr R 1 = Z_to_bv 64 0x13d1c /\ getr R 10 = Z_to_bv 64 f /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x141c4 /\ m' = memc')); [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, S22, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r19|]. intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply (RF_getr _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q21, Q8, Q9, Q18.
  exact (st19 X Y Lc' Ac' regs2 memc' mdc' Lamc' peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db f kf CR' HC PX
    PY NB' Hdb ND' Hdd RF2 Q1 Q10 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c17: preset_base64_decode(bytes, &n), the comparison with the body, then fuzz_free(got) *)
Lemma st17 : forall X Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db f kf z kz s
    bs b kb,
  CRs ((f, kf) :: X) [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc (S Nc) ->
  cntc + 1 <= cnt + CRT_ALLOCS ->
  Permutation X (Db ++ Y) -> Permutation Y (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 24) tb Db -> (depth tb <= 2)%nat ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) td Dd -> (depth td <= 2)%nat ->
  pj_cstr rsegs memc (lin Lamc) z kz s -> Z.of_nat (length s) <= 2 ^ 28 -> dec_size s + 16 <= CRT_SIZE ->
  b64_dec s = Some bs -> Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regsc -> getr regsc 1 = Z_to_bv 64 0x13ce4 -> getr regsc 10 = Z_to_bv 64 z ->
  getr regsc 11 = Z_to_bv 64 (spZ regs - 336 + 16) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 22 = Z_to_bv 64 f -> getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PRESET_BASE64_DECODE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 td Dd tb Db f kf z kz s bs b kb CRc HC
    PX PY NB Hdb ND Hdd CSZ Hsl Hsz HD BB Hbin Hbk RFc R1 R10 R11 R19 R20 R22 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof crt_spr as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (_ & _ & Hsp16).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof CSZ as (Hzin & Hzk & HF & HZB).
  pose proof CRc as (((HMc & _) & _) & _ & LGc & _). pose proof PRE as (HM0 & _).
  destruct (crt_slack _ _ _ _ _ _ _ _ _ _ z kz s CRc Hzin Hzk HZB) as (slack & TB & SLL).
  destruct (ledger_block_range B API Lc Ac memc mdc Lamc peakc cntc _ z kz HMc LGc Hzin) as (Hz1 & Hz2 & _).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ b kb HM0 LG0 Hbin) as (Hb1 & Hb2 & _).
  apply (w_dec B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd (DEC fx) ((f, kf) :: X)
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc z (spZ regs - 336 + 16) s slack bs post
    CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11).
  { unfold no_zero. eapply Forall_impl; [|exact HF]. intros c Hc. cbv beta in *. lia. }
  { unfold bytes_ok. eapply Forall_impl; [|exact HF]. intros c Hc. cbv beta in *. lia. }
  { exact Hsl. }
  { rewrite SEG. exact TB. }
  { lia. }
  { right. right. left. exists z, kz. split; [exact Hzin | lia]. }
  { lia. }
  { lia. }
  { lia. }
  { right. lia. }
  { exact HD. }
  { lia. }
  { exact Hsz. }
  intros Lc' Ac' regs' memc' mdc' g RP RG10 Hg0 Hg16 Hgb CR' CS BG BL.
  assert (IB : incl Db ((f, kf) :: X)) by (intros y Hy; right; exact (incl_perm_l X Db Y PX _ Hy)).
  assert (ID : incl Dd ((f, kf) :: X))
    by (intros y Hy; right; apply (incl_perm_r X Db Y PX); exact (incl_perm_l Y Dd _ PY _ Hy)).
  pose proof (crt_nd _ _ _ _ _ _ _ _ _ _ CR') as NDg. apply NoDup_cons_iff in NDg as [NG _].
  assert (EO : forall p D, incl D ((f, kf) :: X) -> spZ regs - 336 + 24 <= p ->
     Eok ((f, kf) :: X) [(same, sn); (want, wn)] ((g, dec_size s) :: (f, kf) :: X) [(same, sn); (want, wn)] p D
       (dec_writes g (dec_size s) (spZ regs - 336 + 16))).
  { intros p D HI Hp x [Hx|[(_ & Hx)|Hx]].
    - left. exact Hx.
    - right. right. left. exists g, (dec_size s). split; [right; left; reflexivity|]. split; [|exact Hx].
      intros H. exact (NG (HI _ H)).
    - right. left. split; lia. }
  assert (G0 : forall D, incl D ((f, kf) :: X) -> forall a k, In (a, k) D -> (a - 16, k + 16) <> (0, 0)).
  { intros D HI a k Hak E. injection E as E1 _.
    destruct (cr_x_lo _ _ _ _ _ _ _ _ _ _ a k CRc (HI _ Hak)) as (H1 & _). lia. }
  assert (NB1 : pj_node rsegs memc' (lin ((g, dec_size s) :: Lamc)) (spZ regs - 336 + 24) tb Db).
  { apply (cr_keep_node ((f, kf) :: X) _ Lc Ac memc mdc Lamc peakc cntc (S Nc) ((g, dec_size s) :: (f, kf) :: X) _
      Lc' Ac' memc' mdc' _ _ _ Nc _ _ _ _ tb Db CRc CR' CS NB IB (fun y Hy => or_intror (IB y Hy))).
    - lia.
    - exact (EO (spZ regs - 336 + 24) Db IB ltac:(lia)).
    - exact (G0 Db IB). }
  assert (ND1 : pj_node rsegs memc' (lin ((g, dec_size s) :: Lamc)) (spZ regs - 336 + 192) td Dd).
  { apply (cr_keep_node ((f, kf) :: X) _ Lc Ac memc mdc Lamc peakc cntc (S Nc) ((g, dec_size s) :: (f, kf) :: X) _
      Lc' Ac' memc' mdc' _ _ _ Nc _ _ _ _ td Dd CRc CR' CS ND ID (fun y Hy => or_intror (ID y Hy))).
    - lia.
    - exact (EO (spZ regs - 336 + 192) Dd ID ltac:(lia)).
    - exact (G0 Dd ID). }
  assert (BB1 : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply (cr_keep_lam ((f, kf) :: X) _ Lc Ac memc mdc Lamc peakc cntc (S Nc) ((g, dec_size s) :: (f, kf) :: X) _
      Lc' Ac' memc' mdc' _ _ _ Nc _ _ _ (spZ regs - 336 + 24) [] b kb b (bz bs) CRc CR' CS).
    - exact (EO (spZ regs - 336 + 24) [] (fun y (H : In y []) => match H with end) ltac:(lia)).
    - intros E. cbv beta in E. injection E as E1 _. lia.
    - exact Hbin.
    - exact BB.
    - lia.
    - unfold bz. rewrite length_map. lia. }
  pose proof (RF_pres _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R22 S22 22. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _ & _ & _ & RA' & _) & _). pose proof MID' as (HM' & _).
  destruct (cr_x_lo _ _ _ _ _ _ _ _ _ _ g (dec_size s) CR' (or_introl eq_refl)) as (Hg1 & Hg2 & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13ce4) memc' mdc'
    (fun R pc' m' => exists m0, (RF R /\ getr R 1 = Z_to_bv 64 0x13d14 /\ getr R 10 = Z_to_bv 64 g /\
       getr R 22 = Z_to_bv 64 f /\ getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\
       getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x141c4 /\
       munch [] (normalize rsegs memc') m0) /\ mem_rel rsegs m' m0 /\ ro_same rsegs memc' m'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, RG10, S19, S20, S22, S21, S8, S9, S18.
    apply crt_evn; [exact RA'|].
    eapply Exec.evt_mono.
    - eapply (crt_r18 BCMP) with (db := bz bs).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + assert (0 <= dec_size s) by (unfold dec_size; lia). lia.
      + lia.
      + lia.
      + unfold bz. rewrite length_map. reflexivity.
      + apply bytes_at_normalize; [exact RA'|]. rewrite SEG in BG. exact BG.
      + apply bytes_at_normalize; [exact RA' | exact BB1].
      + rewrite MState.unsigned_lit by lia. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_normalize; [exact RA'|]. rewrite SEG in BL. exact BL.
      + rewrite MState.unsigned_lit by lia. lia.
      + apply mem_inv_normalize.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU & _ & _).
      do 3 eexists. split; [reflexivity|].
      split; [apply (RF_mk regs'); [exact RF' | reflexivity ..]|].
      do 8 (split; [reflexivity|]). exact MU. }
  intros RR pc2 mem2 regs2 (m0 & (RF2 & Q1 & Q10 & Q22 & Q21 & Q8 & Q9 & Q18 & -> & MU) & HR & ROS) HG.
  apply (RF_getr _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q22, Q21, Q8, Q9, Q18.
  assert (EQ : forall x, mem2 x = memc' x).
  { apply (mem_unchanged_rel rsegs memc' (normalize rsegs memc') mem2 m0 (mem_rel_normalize rsegs memc' RA') HR ROS).
    intros x. apply MU. exact I. }
  pose proof (cr_eqm _ _ _ _ _ _ _ _ _ _ mem2 CR' EQ) as CR2.
  assert (IB' : incl Db ((g, dec_size s) :: (f, kf) :: X)) by (intros y Hy; right; exact (IB y Hy)).
  assert (ID' : incl Dd ((g, dec_size s) :: (f, kf) :: X)) by (intros y Hy; right; exact (ID y Hy)).
  pose proof (node_eqm _ mem2 _ _ _ _ NB1 (cr_lin _ _ _ _ _ _ _ _ _ _ Db CR' IB') EQ) as NB2.
  pose proof (node_eqm _ mem2 _ _ _ _ ND1 (cr_lin _ _ _ _ _ _ _ _ _ _ Dd CR' ID') EQ) as ND2.
  exact (st18 X Y Lc' Ac' regs2 mem2 mdc' _ _ (cntc + 1) Nc same sn want wn q kq b1 k1 td Dd tb Db f kf g (dec_size s)
    CR2 ltac:(unfold CRT_ALLOCS; lia) PX PY NB2 Hdb ND2 Hdd RF2 Q1 Q10 Q22 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

End F.
End ST.
