(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan+UBSan walk (image B) of fuzz_reply's LLVMFuzzerTestOneInput
   over the GENERIC allocator relation ARx, its FIRST stage: the ARx twin of lib/B/W_LLVMFuzzerTestOneInput_drain_entry.v
   (a Theorem Labs lane's, a working branch af5c712458a; NOT edited): dr_stage_entry, from the arm's entry
   0x8489c through the relay_source call to the latch (both skips) or to DLK (lib/B/..._drain_defs_x.v).
   Proves no function (kind: segment walk): relay_source is cut_x's named contract RSRC_x (:348), declared below
   verbatim in place of the AR file's RSRC.
   The method (W8Entry-2's add_x method, as in AddX's lib/A/W_LLVMFuzzerTestOneInput_drain_x.v): this file Requires the
   AR file and CITES its items that read no AR and no Section variable (the pure byte / list lemmas before its Section,
   the stage's run definitions de_span / de1_regions / ss_de1 / ..., the run lemma de3n_entry); the items that read a
   Section variable but no AR are restated verbatim (de_ctx, de_regs, de_regs_kept, ...); the AR-reading items are
   CONVERTED, keeping their names: AR -> ARx with the state's ghost list (Hp beside S, Hp3 beside S3, Hpe at the entry
   beside cx), al_* -> alx_* (alx_shadow with hp_off_block_hp0 at HP0), the journal lemmas -> W_journal_x's _x twins,
   paj_run(_to)_tok -> paj_run(_to)_tok_x, frames_bounds -> frames_bounds_x, azs_range_addressable ->
   azs_range_addressable_x; the de_ transport kit (B latch's lt_ kit) after A's lib/A/W_LLVMFuzzerTestOneInput_latch_x.v
   lt_*_x.  The stage's states DE1 / DE2 take Hpe beside cx and Hp3 beside S3.
   The Section header is cut_x's Section w header (B .. RINV), the arm's MMAX, the room round's RP / dr_cnl_pk and the
   interface record EV : dr_env_x.  The room round (an internal work row, image A's b5892edd1cb): the cut's NP S3 (lcut_x,
   after LSx) is threaded from dr_stage_entry's INV_A_x to de_mk_K's INV_K_x and to DLK. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_contract_x W_sites_x W_frame_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs_x.
(* LAST, so the names this file cites from the AR file are not shadowed by a kit file's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_entry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the cut's own Local Notation, which does not leave its file *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section drex.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- cut_x's Section w (W_LLVMFuzzerTestOneInput_cut_x.v:199-244), verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* ---- the arm's own parameter ---- *)
Variable MMAX : Z.                                   (* W7's request bound, dr_spec_x's parameter *)
(* the room round's two parameters of the interface record (lib/B/W_LLVMFuzzerTestOneInput_drain_defs_x.v) *)
Variable RP : roomp.
Variable dr_cnl_pk : hsrc -> (Z -> bool) -> nat.
(* the arm's interface record over ARx (lib/B/W_LLVMFuzzerTestOneInput_drain_defs_x.v dr_env_x) *)
Variable EV : dr_env_x B MT NP G_fr PST ARx LSx RINV MMAX RP dr_cnl_pk.
(* the engine's seats, over the generic journal *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
(* the cut_x's relay_source contract (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:583 RSRC_x), verbatim *)
Hypothesis RSRC_x : forall W ly S Hp (regs : bvmap 5 word) mem md ch T es fd,
  afn_pre_x segs B ARx RSRC_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
    (aleafx_post_x B PST ARx RSRC_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
            a0 = w64 (T + AENT * Z.of_nat j)) \/
         ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0))).

Ltac de_low :=
  cbn [fst snd gfp]; unfold DE_CEIL8, fr_RG in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof de_ceil_lo; lia.

Lemma de_blk : forall ly S Hp (W : world segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S Hp W mem md p n HAR Hin Hn.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H1 & H2 & _).
  pose proof (req_size_pos n Hn) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.

(* :108 struct list *)

Lemma de_alist : forall ly S Hp (W : world segs) mem md LA l lines,
  ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= DE_CEIL8 ->
  de_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : de_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite de_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (de_blk ly S Hp W mem md _ _ HAR K1 ltac:(lia)) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite de_bzs_len, length_app. cbn [length].
      unfold DE_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply de_fp_low_cons; [cbn; lia | cbn; lia|]. apply de_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply de_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (de_blk ly S Hp W mem md _ _ HAR Hin ltac:(unfold AREC; lia)) as (P1 & P2 & P3).
    apply de_fp_low_cons; [cbn; lia | | apply de_fp_low_nil].
    cbn [gfp fst snd]. rewrite de_bzs_len, length_app, de_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold DE_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

Lemma de_asrc : forall ly S Hp (W : world segs) mem md HA h,
  ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= DE_CEIL8 ->
  de_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (de_alist ly S Hp W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (de_alist ly S Hp W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (de_alist ly S Hp W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (de_blk ly S Hp W mem md _ _ HAR Hpb ltac:(unfold APARTIAL; lia)) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply de_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply de_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite de_bzs_len, Hpj. unfold APARTIAL, DE_CEIL8 in *. lia.
    + apply de_fp_low_app; [exact A1|]. apply de_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

Lemma de_aentry : forall ly S Hp (W : world segs) mem md e,
  ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
  de_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : de_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k) (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k, Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite de_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (de_blk ly S Hp W mem md _ _ HAR M1 ltac:(lia)) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite de_bzs_len, length_app. cbn [length].
      unfold DE_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply de_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply de_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (de_blk ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
      apply de_fp_low_cons; [cbn; lia | | apply de_fp_low_nil].
      cbn [gfp snd]. rewrite de_bzs_len, length_app. unfold DE_CEIL8 in *. lia.
    + apply de_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _ & Hk8 & _)]; [lia|].
        destruct (de_blk ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite de_bzs_len, de_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold DE_CEIL8. pose proof de_ceil_lo. lia. }
        destruct (de_blk ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold DE_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

Lemma de_arelay : forall ly S Hp (W : world segs) mem md G es,
  ARx ly S Hp W mem md -> arelay_at B fr_RG ly S W mem G es ->
  de_fp_low (arelay_fp fr_RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (de_blk ly S Hp W mem md _ _ HAR R8 ltac:(unfold ATABLE; lia)) as (P1 & P2 & P3).
  assert (HE : de_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite de_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (de_aentry ly S Hp W mem md e HAR (R10 e He)) as [F1 _].
      rewrite de_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (de_aentry ly S Hp W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply de_fp_low_cons; [de_low | de_low|].
    apply de_fp_low_cons; [de_low | de_low|].
    apply de_fp_low_cons; [de_low | de_low|].
    apply de_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, DE_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

Lemma de_aout : forall ly S Hp (W : world segs) mem md c O mx no cap out,
  ARx ly S Hp W mem md -> aout_at B fr_RG ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= DE_CEIL8 ->
  de_fp_low (aout_fp B fr_RG cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply de_fp_low_cons; [de_low | de_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply de_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (de_blk ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
    apply de_fp_low_cons; [cbn; lia | cbn; unfold DE_CEIL8 in *; lia | apply de_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* :329 the model *)

Lemma de_errno : 0 <= as_errno B /\ as_errno B + 4 <= DE_CEIL8.
Proof.
  pose proof (pal_env B (dre_TL _ _ _ _ _ _ _ _ _ _ _ EV)) as ((HE0 & HE1) & _).
  pose proof de_ceil_lo. unfold DE_CEIL8, kLowMemEnd in *. lia.
Qed.

(* ---- the model ---- *)

Lemma de_amodel_kept : forall ly S Hp (W : world segs) mem md (W' : world segs) mem' m,
  ARx ly S Hp W mem md -> amodel_at B ly S W mem m ->
  (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S Hp W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) KEEP.
  destruct de_errno as [HE0 HE1].
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= DE_CEIL8)
      by (unfold fr_RG, DE_CEIL8; cbn; unfold ASRC; pose proof de_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (de_asrc ly S Hp W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (de_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (de_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (de_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (de_arelay ly S Hp W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (de_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (de_aout ly S Hp W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (de_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, DE_CEIL8 in *. pose proof de_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, DE_CEIL8 in *. pose proof de_ceil_lo. lia.
Qed.

(* :445 the input block *)

Ltac de_outt := unfold de_out, DR_N, DR_AT; repeat split; lia.

Lemma de_ainput_kept : forall cx ly S Hp (W : world segs) mem md (W' : world segs) mem',
  ARx ly S Hp W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S Hp W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hpe) | (Hn & Hin)]; [lia|].
  destruct (de_blk ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
  unfold DE_CEIL8. lia.
Qed.

(* :538 reading one entry's used and cap out of the relay's table (check_bounded's pre); the relation is not read *)

Lemma de_spF : forall cx Hpe, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\ lf_F cx mod 32 = 0 /\
  Z.of_nat (length (c_pl cx)) = c_n cx /\ 0 <= c_n cx < 2 ^ 26.
Proof.
  intros cx Hpe (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold YCfn.LLVMF_STK in Hslo.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hm.
  split; [lia|]. split; [unfold lf_F; lia|].
  split; [unfold lf_F; rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. destruct Hnrng as [(Hz & _) | (Hz & _)]; lia.
Qed.
(* the walk's own fake frame is a live frame of its journal *)

Lemma de_fin : forall cx Hpe fpos ly S Hp (W : world segs) mem md k,
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k ->
  In (1, fpos) (frames S).
Proof.
  intros cx Hpe fpos ly S Hp W mem md k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity.
Qed.

(* ---- everything lcut states of memory, as one bundle, and its transport across a run or a call that keeps every
   byte outside this stage's three windows ---- *)

Definition de_ctx (cx : lfcx) (m : lmod) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
  (mem : word -> option byte) : Prop :=
  aframe_at cx (frame_addr ly 1 fpos) W mem /\ sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  amodel_at B ly S W mem m /\ ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem.

Lemma de_ctx_kept : forall cx Hpe m fpos ly S Hp (W W' : world segs) mem mem' md,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ARx ly S Hp W mem md -> In (1, fpos) (frames S) ->
  (forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  de_ctx cx m fpos ly S W mem -> de_ctx cx m fpos ly S W' mem'.
Proof.
  intros cx Hpe m fpos ly S Hp W W' mem mem' md HB HAR Hfin HK WK (HFR & HFL & HMOD & HIN & HRV & HJT).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil_lo as HCL. pose proof de_ceil_hi as HC64.
  destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly 1 fpos / 8 /\ 8 * (frame_addr ly 1 fpos / 8) <= frame_addr ly 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply HK; [lia | unfold DE_CEIL8 in *; de_outt]).
  split; [apply (de_aframe_kept cx _ W W' mem mem' HFR HK WK); unfold DE_CEIL8, SB in *; lia|].
  split; [apply (de_sv8_kept W W' mem mem'); [intros x Hx; apply KL; unfold DE_CEIL8 in *; lia | exact HFL]|].
  split; [exact (de_amodel_kept ly S Hp W mem md W' mem' m HAR HMOD KL)|].
  split; [exact (de_ainput_kept cx ly S Hp W mem md W' mem' HAR HIN Hlen KL)|].
  split; [exact (de_rom_kept W W' mem mem' HRV KL)|].
  exact (de_jt_kept W W' mem mem' HJT KL).
Qed.
(* the registers every state of this stage keeps: lregs_common, s9 = t, s4 = the new cursor, s5 = the source *)

Definition de_regs (cx : lfcx) (t : Z) (m : lmod) (si : nat) (FF : Z) (regs : bvmap 5 word) : Prop :=
  lregs_common B cx FF regs /\ getr regs 25 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 20 = w64 (c_p cx + dr_k' cx m) /\ getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si).

Ltac de_in := cbn [In jt_kept DE_KR DE_KD]; repeat (first [left; reflexivity | right]).

Lemma de_regs_kept : forall cx t m si FF (regs regs' : bvmap 5 word),
  (forall r, In r DE_KR -> getr regs' r = getr regs r) ->
  de_regs cx t m si FF regs -> de_regs cx t m si FF regs'.
Proof.
  intros cx t m si FF regs regs' HK ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  unfold de_regs, lregs_common.
  rewrite (HK 2%bv ltac:(de_in)), (HK 8%bv ltac:(de_in)), (HK 9%bv ltac:(de_in)), (HK 18%bv ltac:(de_in)),
    (HK 19%bv ltac:(de_in)), (HK 23%bv ltac:(de_in)), (HK 24%bv ltac:(de_in)), (HK 26%bv ltac:(de_in)),
    (HK 27%bv ltac:(de_in)), (HK 3%bv ltac:(de_in)), (HK 4%bv ltac:(de_in)), (HK 25%bv ltac:(de_in)),
    (HK 20%bv ltac:(de_in)), (HK 21%bv ltac:(de_in)).
  repeat split; first [assumption | lia].
Qed.
(* a callee-saved register across a call (lib/B SEG_LATCH's lt_pres) *)

Ltac de_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

Lemma de_regs_pres : forall cx t m si FF (regs regs' : bvmap 5 word),
  aregs_preserved regs regs' -> de_regs cx t m si FF regs -> de_regs cx t m si FF regs'.
Proof.
  intros cx t m si FF regs regs' HP HR. apply (de_regs_kept cx t m si FF regs regs'); [|exact HR].
  intros r Hr. apply (de_pres regs regs' r HP). unfold DE_KR in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [de_cs|]). destruct Hr.
Qed.
(* a byte present before a run that only grows the memory is present after it *)

Lemma de_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|].
  split; [exact H8|]. split; lia.
Qed.

(* ---- relay_source's afn_pre at sp = F (lib/B SEG_LATCH's lt_afn_pre_at, verbatim but for the name) ---- *)

Lemma de_afn_pre_at : forall cx Hp ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hp ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  (* sp0 is 16-aligned (astk_ok), so 8-aligned (this file's lia does not convert mod, as _drain_defs.v sets) *)
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | exact Hsp8 | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* ---- the relay's table in memory: entry i's eof field (image A's dr_tbl_eof) ---- *)

Lemma de_pads_of_relay : forall ly S W mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  rewrite Forall_forall in HE |- *. intros e He.
  destruct (HE e He) as (_ & _ & H3 & H4 & _). split; assumption.
Qed.
(* the shadow entry of a range INSIDE a live block (image A's dc_shent_block, from Reusable/YCbq.v
   shent_ok_of_block) *)

Lemma de_shent_block : forall ly S Hp (W : world segs) mem md E Bx (mm : nat) p n q lo hi,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  U E Bx = SHADOW_OFF -> U E (SOff mm 0) = q -> p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
  shent_ok segs Bx E (mrestrict (w_H W) mem) (mkSHE mm lo hi).
Proof.
  intros ly S Hp W mem md E Bx mm p n q lo hi HAR Hin HB Hm Hlo Hle Hhi.
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of segs).
  destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md p n HAR Hin (hp_off_block_hp0 _ _ HP0 _ _ _ _ _ _ _ _ HAR)) as [Hbs _].
  split.
  - destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
    eapply block_shadow_range; [exact Hbs | lia | lia].
  - destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* ------------------------------------------------------------------ the engine's seats *)

Ltac de_awr U9 :=
  cbn [ss_mem add_cond];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold YCfn.LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.

(* (1) 0x8489c: s5 = g_s + 96 si (atom 21, seat R1), s1 = F (atom 9), s11 = SB (atom 27); the in.n cell F+144
   (written) and s->fd (atom 32, read) *)

Lemma de1_entry : forall ly S Hp (W : world segs) regs mem md F HA fd,
  ARx ly S Hp W mem md ->
  getr regs 9 = w64 F -> getr regs 21 = w64 HA -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  4096 <= HA -> HA + ASRC <= SB -> HA mod 8 = 0 -> 0 <= fd < 2 ^ 31 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  val_mem segs (arm W mem) HA 4 fd -> azs B HA ASRC ->
  st_ok_pi segs VAL (Eimg (Ereg regs (de1_extra fd))) ss_de1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_arm)) mem (seg_rom segs)))
  /\ sh_ok segs de_Bx de_SH1 (Eimg (Ereg regs (de1_extra fd))) (mrestrict (w_H W) mem).
Proof.
  intros ly S Hp W regs mem md F HA fd HAR H9 H21 H27 HF1 HF2 HH0 HH1 HH2 Hfd HW1 Mfd HZ.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (de1_extra fd))).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E21 : ew E 21 = w64 HA) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
  assert (E27 : ew E 27 = w64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 fd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  split.
  - unfold ss_de1. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold de1_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW1; lia | apply Forall_nil].
      * rewrite E21, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ HA 0 4 (SOff 32 0) fd);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mfd.
    + apply pairwise_disjoint_of_extents. unfold de1_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E21, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [de1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E21, E27, E32, !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r. try change (2 ^ 5) with 32. try change (2 ^ 3) with 8.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, de_SH1. constructor; [|constructor].
    eapply shent_ok_of_range.
    + exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md HA ASRC HAR HZ).
    + unfold de_Bx. rewrite (U_atom E 27 SB E27) by lia. reflexivity.
    + rewrite (U_atom E 21 HA E21) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. assert (Hm1 : Z.min 0 ASRC = 0) by reflexivity. assert (Hm2 : Z.max 0 ASRC = ASRC) by reflexivity.
      rewrite Hm1, Hm2 in Hx. unfold ASRC in *. lia.
Qed.

(* (3n) 0x848c4 with a0 = 0: the at cell F+192 (written); a0 is the plain atom 10 (the walk splits `beqz a0` and
   refutes its fall-through edge from a0 = 0) *)

Lemma de3f_entry : forall ly S Hp (W : world segs) regs mem md F G (j : nat) ef,
  ARx ly S Hp W mem md ->
  getr regs 9 = w64 F -> getr regs 10 = w64 (G + AENT * Z.of_nat j) -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  (forall a, F + 192 <= a < F + 200 -> writable_at segs (arm W mem) a) ->
  In (G, ATABLE) (ablocks B ly S) ->
  4096 <= G -> (G + AENT * Z.of_nat j) mod 8 = 0 -> G + ATABLE <= 140737479966720 -> G + ATABLE <= F ->
  (j < 16)%nat ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat j + 4) 4 ef -> 0 <= ef <= 1 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (de3_extra ef))) ss_de3f
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)))
  /\ sh_ok segs de_Bx de_SH3 (Eimg (Ereg regs (de3_extra ef))) (mrestrict (w_H W) mem).
Proof.
  intros ly S Hp W regs mem md F G j ef HAR H9 H10 H27 HF1 HF2 HWA Hin HG0 HG8 HGc HGF Hj Mef Hef.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (de3_extra ef))).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E10 : ew E 10 = w64 (G + AENT * Z.of_nat j)) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
  assert (E27 : ew E 27 = w64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 ef)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HAT : ATABLE = 896) by reflexivity. assert (HAE : AENT = 56) by reflexivity.
  split.
  - unfold ss_de3f. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, de_rA, de_rE;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply HWA; lia | apply Forall_nil].
      * rewrite E10, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (G + AENT * Z.of_nat j) 4 4 (SOff 32 0) ef);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mef].
    + apply pairwise_disjoint_of_extents. unfold de_rA, de_rE, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E10, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [de3f_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E10, E27, E32, !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r. try change (2 ^ 5) with 32. try change (2 ^ 3) with 8.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, de_SH3. constructor; [|constructor].
    apply (de_shent_block ly S Hp W mem md E de_Bx 10 G ATABLE (G + AENT * Z.of_nat j) 0 AENT HAR Hin).
    + unfold de_Bx. rewrite (U_atom E 27 SB E27) by lia. reflexivity.
    + rewrite (U_atom E 10 _ E10) by lia. reflexivity.
    + lia.
    + lia.
    + replace (req_size ATABLE) with 896 by reflexivity. lia.
Qed.

(* ------------------------------------------------------------------ the stage's intermediate states *)
(* at `jal relay_source` (0x848c0, the callee's entry): in.n stored, a0 = s->fd, ra = 0x848c4 *)

Definition DE1 (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fr_relay_source)) mem (seg_rom segs)) md /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k /\
    de_ctx cx m fpos ly3 S3 W mem /\ sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
    getr regs 1 = Z_to_bv 64 (BASE + A_dr_ret) /\ getr regs 10 = w64 (hs_fd h) /\
    de_regs cx t m si (frame_addr ly3 1 fpos) regs.
(* back from relay_source (0x848c4): a0 = the entry of the source's fd, or 0 *)

Definition DE2 (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k /\
    de_ctx cx m fpos ly3 S3 W mem /\ sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
    de_regs cx t m si (frame_addr ly3 1 fpos) regs /\
    ((exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
        getr regs 10 = w64 (lm_G m + AENT * Z.of_nat j)) \/
     (dr_nomatch m h (Z.of_nat (length (lm_es m))) /\ getr regs 10 = w64 0)).

(* the registers run (1) does not write (it writes a0, a1 and ra) *)

Lemma de_stage1 : forall cx Hpe t m si h fpos ly3 S3 Hp3 k (W : world segs) regs mem md,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  getr regs 6 = w64 (c_n cx - dr_k' cx m) -> dr_at_op cx m -> dr_pick cx m si h ->
  SRr segs W (cfg_at segs (fr_B0 + A_dr_arm) regs mem md) (DE1 cx Hpe t m si h fpos ly3 S3 Hp3 k).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HB HJ HCTX HRG R6 Hatop Hpick.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  pose proof Hpick as (Hpk & Hsi & Hh).
  pose proof HMOD as (Hlen4 & HSL & _).
  pose proof (HSL si Hsi) as HSRC. unfold aslot in HSRC. rewrite Hh in HSRC.
  pose proof HSRC as (Mfd & _ & _ & _ & _ & _ & _ & _ & Rfd & _).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin cx Hpe fpos ly3 S3 Hp3 W mem md k HJ).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof Hatop as (Hk0 & _ & _).
  pose proof (dr_k'_rng cx m Hk0) as Hk'.
  destruct (de_slot si Hsi) as (HA0 & HA1 & HA8 & HA2).
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HRS : rg_s fr_RG = 0x5d8e60) by reflexivity. assert (HAS : ASRC = 96) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (HZ : azs B HA ASRC)
    by (apply (de_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact (dre_HZS _ _ _ _ _ _ _ _ _ _ _ EV) | unfold HA; lia | lia]).
  pose proof HFR as (_ & HAWR & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de1_entry ly3 S3 Hp3 W regs mem md (lf_F cx) HA (hs_fd h) HAR C9 R21 C27 ltac:(lia) HF32 HA0
              ltac:(lia) HA8 Rfd HW1 Mfd HZ) as [HS SHOK].
  remember (Eimg (Ereg regs (de1_extra (hs_fd h)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de1_extra (hs_fd h))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E6 : ew E 6 = w64 (c_n cx - dr_k' cx m)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6).
  assert (E9 : ew E 9 = w64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact C9).
  assert (E32 : ew E 32 = Z_to_bv 64 (hs_fd h))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  clear HE EEo.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_arm)) with (Z_to_bv 64 (BASE + A_dr_arm)).
  (* 0x8489c `beqz s5,850fc` (TRAP NONNULL) and 0x848a4 `bnez a0,850fc` (TRAP ALIGN8): both decided by the runner
     from atom 21's fact mkAF 4096 140737479966720 3 (seat R1), no W_traps.v lemma; the shadow check 0x848b8 is
     decided by mkSHE 21 0 96.  The run stores in.n, loads s->fd and stops at relay_source's entry. *)
  paj_run_to_tok_x RUNTO HS HJ SHOK de_span AF_fr_relay_source.
  { de_awr U9. }
  (* what the run kept: every byte outside the in.n cell, the registers but a0, a1, ra *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms) a).
  { intros a Ha (_ & Hna & _). split.
    - apply (aview_kept_out _ _ _ _ _ HFr a Ha). intros (r & Hin & Hr). cbn [ss_mem ss_de1 de1_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; unfold DR_N in Hna; lia | ]).
      destruct Hin.
    - intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 Hp). }
  assert (WK : forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a ->
      writable_at segs (arm W (ms_mem ms)) a).
  { intros a _ Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (de_pres_grows W _ _ a HG0 Hp). }
  pose proof (de_ctx_kept cx Hpe m fpos ly3 S3 Hp3 W W mem (ms_mem ms) md HB HAR Hfin KEEP WK HCTX) as HCTX2.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : sv8 W (ms_mem ms) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { unfold sv8, DR_N.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 6 0) (c_n cx - dr_k' cx m) RG0) end.
    - rewrite ?ew_ewset_other by lia. exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zside.
    - zside. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (de1_extra (hs_fd h))) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite ?E32 in Q10.
  pmkst HS.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|].
  split; [exact HJ|].
  split; [exact HCTX2|].
  split; [exact SVN|].
  split; [exact Q1|].
  split; [exact Q10|].
  exact (de_regs_kept cx t m si _ regs _ KR HRG).
Qed.

(* ------------------------------------------------------------------ (2) the call at 0x848c0: RSRC *)

Lemma de_stage2 : forall cx Hpe t m si h fpos ly3 S3 Hp3 k W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe -> 0 <= hs_fd h < 2 ^ 31 ->
  DE1 cx Hpe t m si h fpos ly3 S3 Hp3 k W c ->
  SRr segs W c (DE2 cx Hpe t m si h fpos ly3 S3 Hp3 k).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W c HB Hfd (regs & mem & md & -> & HJ & HCTX & SVN & Q1 & Q10 & HRG).
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin cx Hpe fpos ly3 S3 Hp3 W mem md k HJ).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL. pose proof de_ceil_hi as HC64.
  assert (Hsp1 : spZ regs = lf_F cx).
  { unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
  (* relay_source's afn_pre at sp = F; ra = 0x848c4 = BASE + 9600 *)
  assert (HRET : A_dr_ret = 9600) by reflexivity. rewrite HRET in Q1.
  destruct (de_afn_pre_at cx Hpe ly3 S3 Hp3 fpos k W mem md regs RSRC_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { exact C3. }
  { exact C4. }
  { exact C8. }
  { unfold RSRC_STK. lia. }
  { unfold RSRC_STK, YCfn.LLVMF_STK. lia. }
  pose proof HMOD as (_ & _ & HREL & _).
  change (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fr_relay_source)) mem (seg_rom segs)) md)
    with (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md).
  eapply SRr_bind.
  { exact (RSRC_x W ly3 S3 Hp3 regs mem md ch (lm_G m) (lm_es m) (hs_fd h) HPREc Q10 ltac:(lia) HREL HRV). }
  intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HKEEP & HA0).
  rewrite Hsp1 in HJc, HKEEP. unfold RSRC_STK in HKEEP.
  (* relay_source's journal inside this function's: ajournal_gx_sub_x at G_fr, the callee's lifted from G = [] *)
  assert (HJc' : ajournal_gx_x segs B PST ARx G_fr 0 [] RSRC_STK (lf_F cx) [] ly3 S3 Hp3 W mem md [] ly3 S3 Hp3 W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] RSRC_STK (lf_F cx) [] ly3 S3 Hp3 W mem md [] ly3 S3 Hp3 W2 mem2 md2 0 _ HJc).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k
     RSRC_STK (lf_F cx) 0 [] [] [] ly3 S3 Hp3 W2 mem2 md2 0 HJ HJc'
     ltac:(unfold RSRC_STK, YCfn.LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  (* every fact of the cut, kept across the call: relay_source keeps every byte outside [F - 16, F) *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W2 mem2 a)
    by (intros a Ha (Ho & _ & _); exact (HKEEP a Ha Ho)).
  assert (WK : forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a ->
      writable_at segs (arm W2 mem2) a)
    by (intros a Ha Hw; exact (proj2 (HKEEP a ltac:(lia) ltac:(lia)) Hw)).
  pose proof (de_ctx_kept cx Hpe m fpos ly3 S3 Hp3 W W2 mem mem2 md HB HAR Hfin KEEP WK HCTX) as HCTX2.
  assert (SVN2 : sv8 W2 mem2 (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { apply (de_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply HKEEP; unfold DR_N in Hx; lia. }
  apply SRr_ret.
  exists regs2, mem2, md2.
  split; [rewrite Q1; reflexivity|].
  split; [exact HJ2|].
  split; [exact HCTX2|].
  split; [exact SVN2|].
  split; [exact (de_regs_pres cx t m si _ regs regs2 HP2 HRG)|].
  destruct HA0 as [(j & e & Hnth & Hfde & _ & Ha0) | (Hnone & Ha0)].
  - left. exists j.
    assert (Hjl : (j < length (lm_es m))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
    split; [exact Hjl|].
    rewrite (nth_error_nth (lm_es m) j dr_e0 Hnth). split; [exact Hfde | exact Ha0].
  - right. split; [exact (dr_nomatch_all m h Hnone) | exact Ha0].
Qed.

(* ------------------------------------------------------------------ (3) 0x848c4-0x84900 *)
(* the latch's state from what every skip path holds: the model dr_skip m k' (only the cursor moves) *)

Lemma de_mk_K : forall cx Hpe t m si h fpos ly3 S3 Hp3 k (W : world segs) regs mem md,
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_latch)) mem (seg_rom segs)) md).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HJ (HFR & HFL & HMOD & HIN & HRV & HJT) SVN
    ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21)
    HSEP HLS HNP HRI Hatop Hpick Hor.
  exists regs, mem, md. split; [reflexivity|]. split; [exact HJT|].
  exists [(1, fpos)], ly3, S3, Hp3, k, (dr_skip m (dr_k' cx m)), fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
  split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
  split; [exact (dre_LS_drain_skip _ _ _ _ _ _ _ _ _ _ _ EV cx t m ly3 S3 HLS)|]. split; [exact HNP|].
  split; [exact (dre_RI_drain_skip _ _ _ _ _ _ _ _ _ _ _ EV cx t m si h HRI Hatop Hpick Hor)|].
  split; [repeat split; assumption|].
  split; [exact R25|]. split; [exact Ht|]. split; [exact R20|]. split; [exact SVN|].
  exact (dr_k'_rng cx m (proj1 Hatop)).
Qed.

(* (3n) a0 = 0: `sd zero,192(s1); beqz a0,84804` *)

Lemma de_none : forall cx Hpe t m si h fpos ly3 S3 Hp3 k (W : world segs) regs mem md,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  dr_nomatch m h (Z.of_nat (length (lm_es m))) -> getr regs 10 = w64 0 ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md)
    (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HB HSEP HLS HNP HRI Hatop Hpick HJ HCTX SVN HRG Hnom R10.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin cx Hpe fpos ly3 S3 Hp3 W mem md k HJ).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof HFR as (_ & HAWR & _).
  assert (HWA : forall a, lf_F cx + 192 <= a < lf_F cx + 200 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de3n_entry W regs mem (lf_F cx) C9 C27 ltac:(lia) HF32 HWA) as [HS SHOK].
  remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), C9.
    apply unsigned_lit_small. lia. }
  assert (E10 : ew E 10 = w64 0).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact R10. }
  clear HE.
  (* 0x848c4 `sd zero,192(s1)`; the run stops at 0x848c8 `beqz a0,84804` (not a trap) *)
  paj_run_tok_x RUN HS HJ SHOK de_span.
  { unfold ss_de3n, de_rA. de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem ss_de3n In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
    destruct Hin. }
  psrr_branch_tok RUN BR HS SHOK de_span.
  - (* a0 = 0: to the latch *)
    paj_run_to_tok_x RUNTO HS HJ SHOK de_span AF_LLVM_latch.
    { unfold ss_de3n, de_rA. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3n In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept cx Hpe m fpos ly3 S3 Hp3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret.
    eapply de_mk_K; [exact HJ | exact HCTX2 | exact SVN2 | exact (de_regs_kept cx t m si _ regs _ KR HRG)
                    | exact HSEP | exact HLS | exact HNP | exact HRI | exact Hatop | exact Hpick | left; exact Hnom].
  - (* a0 <> 0: refuted by a0 = 0 *)
    exfalso.
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U10 : U Ev (SOff 10 0) = 0) by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E10 | lia]) end.
    rewrite W_traps.trap_br_eq, U10, U_lit in Hc by lia. cbn in Hc. discriminate Hc.
Qed.

(* the value of the image object g_lock (B: 0x5d9040), the auipc / addi pair at 0x848f4 *)

Lemma de_found : forall cx Hpe t m si h fpos ly3 S3 Hp3 k (W : world segs) regs mem md j,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  getr regs 10 = w64 (lm_G m + AENT * Z.of_nat j) ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md)
    (fun W' c' => INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t W' c' \/
       DLK B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t m j si h fpos ly3 S3 Hp3 k W' c').
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md j HB HSEP HLS HNP HRI Hatop Hpick HJ HCTX SVN HRG Hj Hfdj R10.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin cx Hpe fpos ly3 S3 Hp3 W mem md k HJ).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof HMOD as (_ & _ & HREL & _).
  pose proof HREL as (_ & _ & _ & _ & _ & _ & Hle16 & HGin & (tl & HTAB) & HENT & _).
  pose proof (de_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as HPAD.
  set (e := nth j (lm_es m) dr_e0) in *.
  assert (HEOK : aentry_ok B ly3 S3 W mem e) by (rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  pose proof HEOK as (Heof01 & _).
  assert (Hef2 : 0 <= re_eof (nth j (lm_es m) dr_e0) < 2 ^ 32) by (change (nth j (lm_es m) dr_e0) with e; lia).
  assert (Mef : val_mem segs (arm W mem) (lm_G m + AENT * Z.of_nat j + 4) 4 (re_eof e))
    by (exact (de_tbl_eof W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj Hef2)).
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hj16 : (j < 16)%nat) by lia.
  assert (HAT : ATABLE = 896) by reflexivity. assert (HAEN : AENT = 56) by reflexivity.
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { unfold AENT. pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
    rewrite D. replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  pose proof HFR as (_ & HAWR & _).
  assert (HWA : forall a, lf_F cx + 192 <= a < lf_F cx + 200 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de3f_entry ly3 S3 Hp3 W regs mem md (lf_F cx) (lm_G m) j (re_eof e) HAR C9 R10 C27
              ltac:(lia) HF32 HWA HGin HG4096 HSA8 ltac:(lia) ltac:(lia) Hj16 Mef ltac:(lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (de3_extra (re_eof e)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de3_extra (re_eof e))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = w64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact C9).
  assert (E10 : ew E 10 = w64 (lm_G m + AENT * Z.of_nat j)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_eof e))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  (* atom 244 = A_OBJ 3 = g_lock: the listing's auipc / addi pair at 0x848f4 resolves to it *)
  assert (ELK : ew E 244 = Z_to_bv 64 (rg_lock fr_RG)).
  { change 244%nat with (A_OBJ 3). subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite de_lock_val. reflexivity. }
  clear HE EEo.
  (* 0x848c4 `sd zero,192(s1)`; 0x848c8 `beqz a0,84804` (not a trap) decided by atom 10's lo = 4096;
     0x848d4 `bnez a0,850fc` (TRAP ALIGN8) decided by the runner from atom 10's fact mkAF 4096 140737479966720 3
     (seat R1/R2: T + 56 j is its own atom), no W_traps.v lemma; the shadow check 0x848e8 decided by
     mkSHE 10 0 56.  The run loads r->eof (atom 32) and stops at the eof test 0x848f0. *)
  paj_run_tok_x RUN HS HJ SHOK de_span.
  { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem ss_de3f In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?U9 in Hr;
        unfold DR_AT in Hna; lia | ]).
    destruct Hin. }
  (* 0x848f0 `bnez a0,84804`: the eof test (not a trap) *)
  psrr_branch_tok RUN BR HS SHOK de_span.
  - (* r->eof <> 0: end of file, the operation is a skip - to the latch *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e)
        by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hef1 : re_eof e = 1) by lia.
    paj_run_to_tok_x RUNTO HS HJ SHOK de_span AF_LLVM_latch.
    { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3f In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept cx Hpe m fpos ly3 S3 Hp3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. left.
    eapply de_mk_K; [exact HJ | exact HCTX2 | exact SVN2 | exact (de_regs_kept cx t m si _ regs _ KR HRG)
                    | exact HSEP | exact HLS | exact HNP | exact HRI | exact Hatop | exact Hpick |].
    right. exists j. split; [exact Hj|]. split; [exact Hfdj | exact Hef1].
  - (* r->eof = 0: the relay still reads the source - a0 = s7 = &g_lock, `jal pthread_mutex_lock` *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e)
        by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    rename Hc into Hef0.
    paj_run_tok_x RUN HS HJ SHOK de_span.
    { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3f In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept cx Hpe m fpos ly3 S3 Hp3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    first [ pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0
          | pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0 ].
    cbn [ms_mem restrict] in RG0.
    assert (S192 : sv8 W (ms_mem ms0) (lf_F cx + DR_AT) 0).
    { unfold sv8, DR_AT.
      lazymatch type of RG0 with region_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 192 8%N (SLit 0) 0 RG0) end.
      - rewrite ?ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - reflexivity.
      - lia.
      - lia. }
    first [ lazymatch type of HS with st_ok _ ?Ev _ _ =>
              assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
                by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                           | rewrite ?ed_ewset; exact (proj2 HAE)]) end
          | lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
              assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
                by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                           | rewrite ?ed_ewset; exact (proj2 HAE)]) end ].
    first [ pose proof (regs_kept_of_st_ok segs _ _ _ regs _ DE_KD HS HAE2 ltac:(vm_compute; reflexivity)) as KR
          | pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KD HS HAE2
                          ltac:(vm_compute; reflexivity)) as KR ].
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23.
    rewrite ?ELK in Q10, Q23. rewrite ?E10 in Q22.
    pmkst HS.
    apply SRr_ret. right.
    destruct HCTX2 as (HFR2 & HFL2 & HMOD2 & HIN2 & HRV2 & HROM2).
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|].
    split; [exact HJ|].
    split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HROM2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|].
    split; [exact HRI|]. split; [exact Hatop|]. split; [exact Hpick|]. split; [exact Hj|].
    split; [exact Hfdj|]. split; [exact Hef0|].
    split; [exact SVN2|]. split; [exact S192|].
    split; [exact Q1|]. split; [exact Q10|]. split; [exact Q23|].
    (* dr_regs_call: lregs_common but s7, s9 = t, s4 = the new cursor, s5 = the source, s6 = the entry *)
    unfold dr_regs_call.
    rewrite (KR 2%bv ltac:(de_in)), (KR 8%bv ltac:(de_in)), (KR 9%bv ltac:(de_in)), (KR 18%bv ltac:(de_in)),
      (KR 19%bv ltac:(de_in)), (KR 24%bv ltac:(de_in)), (KR 26%bv ltac:(de_in)), (KR 27%bv ltac:(de_in)),
      (KR 3%bv ltac:(de_in)), (KR 4%bv ltac:(de_in)), (KR 25%bv ltac:(de_in)), (KR 20%bv ltac:(de_in)),
      (KR 21%bv ltac:(de_in)), Q22.
    repeat split; first [assumption | lia].
Qed.

(* ------------------------------------------------------------------ (3) the three paths after the call *)

Lemma de_stage3 : forall cx Hpe t m si h fpos ly3 S3 Hp3 k W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  DE2 cx Hpe t m si h fpos ly3 S3 Hp3 k W c ->
  SRr segs W c (fun W' c' => INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t W' c' \/
    (exists m j si h fpos ly3 S3 Hp3 k, DLK B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t m j si h fpos ly3 S3 Hp3 k W' c')).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W c HB HSEP HLS HNP HRI Hatop Hpick
    (regs & mem & md & -> & HJ & HCTX & SVN & HRG & [(j & Hj & Hfdj & R10) | (Hnom & R10)]).
  - eapply SRr_mono.
    { exact (de_found cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md j HB HSEP HLS HNP HRI Hatop Hpick HJ HCTX SVN HRG
               Hj Hfdj R10). }
    intros W' c' _ [HK | HD]; [left; exact HK | right; exists m, j, si, h, fpos, ly3, S3, Hp3, k; exact HD].
  - eapply SRr_mono.
    { exact (de_none cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HB HSEP HLS HNP HRI Hatop Hpick HJ HCTX SVN HRG
               Hnom R10). }
    intros W' c' _ HK. left. exact HK.
Qed.

(* ------------------------------------------------------------------ the stage *)

Theorem dr_stage_entry : forall cx Hpe t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 2 cx Hpe t W c ->
  SRr segs W c (fun W' c' => INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t W' c' \/
    (exists m j si h fpos ly3 S3 Hp3 k, DLK B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t m j si h fpos ly3 S3 Hp3 k W' c')).
Proof.
  intros cx Hpe t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI
    & HR).
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & Hk & HO & R11 & HPK).
  (* the operation is 2 (regsD's a1), so pick() ran: slot si holds h *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 2).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 2) with true in HPK.
  destruct HPK as (R20 & R6 & [(si & Hpk & R21) | (Hf & _)]); [|lia].
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (dr_k' cx m) in R20, R6.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (dr_kb cx m) in Hpk.
  pose proof HMOD as (Hlen4 & _).
  destruct (dr_pick_some (lm_hs m) (dr_kb cx m) si Hpk) as [Hsi [h Hh]].
  rewrite Hlen4 in Hsi.
  assert (HPICK : dr_pick cx m si h) by (split; [exact Hpk | split; [exact Hsi | exact Hh]]).
  assert (Hatop : dr_at_op cx m) by exact (conj Hk (conj HO Hop)).
  destruct (dre_RI_src _ _ _ _ _ _ _ _ _ _ _ EV cx t m si h HRI HPICK) as (_ & _ & Hfd).
  (* the arm's registers are the dispatch's but for a0 and a1 *)
  assert (HRG : de_regs cx t m si (frame_addr ly3 1 fpos) regs).
  { unfold de_regs, lregs_common.
    rewrite (KR0 2%bv ltac:(de_in)), (KR0 8%bv ltac:(de_in)), (KR0 9%bv ltac:(de_in)), (KR0 18%bv ltac:(de_in)),
      (KR0 19%bv ltac:(de_in)), (KR0 23%bv ltac:(de_in)), (KR0 24%bv ltac:(de_in)), (KR0 26%bv ltac:(de_in)),
      (KR0 27%bv ltac:(de_in)), (KR0 3%bv ltac:(de_in)), (KR0 4%bv ltac:(de_in)), (KR0 25%bv ltac:(de_in)),
      (KR0 20%bv ltac:(de_in)), (KR0 21%bv ltac:(de_in)).
    repeat split; first [assumption | lia]. }
  assert (R6' : getr regs 6 = w64 (c_n cx - dr_k' cx m)) by (rewrite (KR0 6%bv ltac:(de_in)); exact R6).
  assert (HCTX : de_ctx cx m fpos ly3 S3 W mem) by exact (conj HFR (conj HFL (conj HMOD (conj HIN (conj HRV HROM))))).
  eapply SRr_bind; [exact (de_stage1 cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HB HJ HCTX HRG R6' Hatop HPICK)|].
  intros W1 c1 _ H1.
  eapply SRr_bind; [exact (de_stage2 cx Hpe t m si h fpos ly3 S3 Hp3 k W1 c1 HB Hfd H1)|].
  intros W2 c2 _ H2.
  exact (de_stage3 cx Hpe t m si h fpos ly3 S3 Hp3 k W2 c2 HB HSEP HLS HNP HRI Hatop HPICK H2).
Qed.


(* ---- route R: the R twins of the entry stage over the R journal (no world move; strict run tactics with RUNR, SRr kept; dr_stage_entry_xR lifts once with SRr_SRrG).  Strict text above unchanged. ---- *)
Section drexR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable EV_R : dr_env_xR B MT NP G_fr PST ARx LSx RINV MMAX RP dr_cnl_pk R.
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].

Lemma de_errno_xR : 0 <= as_errno B /\ as_errno B + 4 <= DE_CEIL8.
Proof.
  pose proof (pal_env B (dreR_TL _ _ _ _ _ _ _ _ _ _ _ _ EV_R)) as ((HE0 & HE1) & _).
  pose proof de_ceil_lo. unfold DE_CEIL8, kLowMemEnd in *. lia.
Qed.
Lemma de_amodel_kept_xR : forall ly S Hp (W : world segs) mem md (W' : world segs) mem' m,
  ARx ly S Hp W mem md -> amodel_at B ly S W mem m ->
  (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S Hp W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) KEEP.
  destruct de_errno_xR as [HE0 HE1].
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= DE_CEIL8)
      by (unfold fr_RG, DE_CEIL8; cbn; unfold ASRC; pose proof de_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (de_asrc ly S Hp W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (de_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (de_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (de_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (de_arelay ly S Hp W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (de_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (de_aout ly S Hp W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (de_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, DE_CEIL8 in *. pose proof de_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, DE_CEIL8 in *. pose proof de_ceil_lo. lia.
Qed.
Lemma de_ctx_kept_xR : forall cx Hpe m fpos ly S Hp (W W' : world segs) mem mem' md,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ARx ly S Hp W mem md -> In (1, fpos) (frames S) ->
  (forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  de_ctx cx m fpos ly S W mem -> de_ctx cx m fpos ly S W' mem'.
Proof.
  intros cx Hpe m fpos ly S Hp W W' mem mem' md HB HAR Hfin HK WK (HFR & HFL & HMOD & HIN & HRV & HJT).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil_lo as HCL. pose proof de_ceil_hi as HC64.
  destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly 1 fpos / 8 /\ 8 * (frame_addr ly 1 fpos / 8) <= frame_addr ly 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply HK; [lia | unfold DE_CEIL8 in *; de_outt]).
  split; [apply (de_aframe_kept cx _ W W' mem mem' HFR HK WK); unfold DE_CEIL8, SB in *; lia|].
  split; [apply (de_sv8_kept W W' mem mem'); [intros x Hx; apply KL; unfold DE_CEIL8 in *; lia | exact HFL]|].
  split; [exact (de_amodel_kept_xR ly S Hp W mem md W' mem' m HAR HMOD KL)|].
  split; [exact (de_ainput_kept cx ly S Hp W mem md W' mem' HAR HIN Hlen KL)|].
  split; [exact (de_rom_kept W W' mem mem' HRV KL)|].
  exact (de_jt_kept W W' mem mem' HJT KL).
Qed.

Lemma de_fin_xR : forall cx Hpe fpos ly S Hp (W : world segs) mem md k,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k ->
  In (1, fpos) (frames S).
Proof.
  intros cx Hpe fpos ly S Hp W mem md k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity.
Qed.

Lemma de_afn_pre_at_xR : forall cx Hp ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hp ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  (* sp0 is 16-aligned (astk_ok), so 8-aligned (this file's lia does not convert mod, as _drain_defs.v sets) *)
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | exact Hsp8 | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

Definition DE1_xR (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fr_relay_source)) mem (seg_rom segs)) md /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k /\
    de_ctx cx m fpos ly3 S3 W mem /\ sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
    getr regs 1 = Z_to_bv 64 (BASE + A_dr_ret) /\ getr regs 10 = w64 (hs_fd h) /\
    de_regs cx t m si (frame_addr ly3 1 fpos) regs.

Definition DE2_xR (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k /\
    de_ctx cx m fpos ly3 S3 W mem /\ sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
    de_regs cx t m si (frame_addr ly3 1 fpos) regs /\
    ((exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
        getr regs 10 = w64 (lm_G m + AENT * Z.of_nat j)) \/
     (dr_nomatch m h (Z.of_nat (length (lm_es m))) /\ getr regs 10 = w64 0)).

Lemma de_stage1_xR : forall cx Hpe t m si h fpos ly3 S3 Hp3 k (W : world segs) regs mem md,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  getr regs 6 = w64 (c_n cx - dr_k' cx m) -> dr_at_op cx m -> dr_pick cx m si h ->
  SRr segs W (cfg_at segs (fr_B0 + A_dr_arm) regs mem md) (DE1_xR cx Hpe t m si h fpos ly3 S3 Hp3 k).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HB HJ HCTX HRG R6 Hatop Hpick.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  pose proof Hpick as (Hpk & Hsi & Hh).
  pose proof HMOD as (Hlen4 & HSL & _).
  pose proof (HSL si Hsi) as HSRC. unfold aslot in HSRC. rewrite Hh in HSRC.
  pose proof HSRC as (Mfd & _ & _ & _ & _ & _ & _ & _ & Rfd & _).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin_xR cx Hpe fpos ly3 S3 Hp3 W mem md k HJ).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof Hatop as (Hk0 & _ & _).
  pose proof (dr_k'_rng cx m Hk0) as Hk'.
  destruct (de_slot si Hsi) as (HA0 & HA1 & HA8 & HA2).
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HRS : rg_s fr_RG = 0x5d8e60) by reflexivity. assert (HAS : ASRC = 96) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (HZ : azs B HA ASRC)
    by (apply (de_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact (dreR_HZS _ _ _ _ _ _ _ _ _ _ _ _ EV_R) | unfold HA; lia | lia]).
  pose proof HFR as (_ & HAWR & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de1_entry ly3 S3 Hp3 W regs mem md (lf_F cx) HA (hs_fd h) HAR C9 R21 C27 ltac:(lia) HF32 HA0
              ltac:(lia) HA8 Rfd HW1 Mfd HZ) as [HS SHOK].
  remember (Eimg (Ereg regs (de1_extra (hs_fd h)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de1_extra (hs_fd h))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E6 : ew E 6 = w64 (c_n cx - dr_k' cx m)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6).
  assert (E9 : ew E 9 = w64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact C9).
  assert (E32 : ew E 32 = Z_to_bv 64 (hs_fd h))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  clear HE EEo.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_arm)) with (Z_to_bv 64 (BASE + A_dr_arm)).
  (* 0x8489c `beqz s5,850fc` (TRAP NONNULL) and 0x848a4 `bnez a0,850fc` (TRAP ALIGN8): both decided by the runner
     from atom 21's fact mkAF 4096 140737479966720 3 (seat R1), no W_traps.v lemma; the shadow check 0x848b8 is
     decided by mkSHE 21 0 96.  The run stores in.n, loads s->fd and stops at relay_source's entry. *)
  paj_run_to_tok_x RUNTOR HS HJ SHOK de_span AF_fr_relay_source.
  { de_awr U9. }
  (* what the run kept: every byte outside the in.n cell, the registers but a0, a1, ra *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms) a).
  { intros a Ha (_ & Hna & _). split.
    - apply (aview_kept_out _ _ _ _ _ HFr a Ha). intros (r & Hin & Hr). cbn [ss_mem ss_de1 de1_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; unfold DR_N in Hna; lia | ]).
      destruct Hin.
    - intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 Hp). }
  assert (WK : forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a ->
      writable_at segs (arm W (ms_mem ms)) a).
  { intros a _ Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (de_pres_grows W _ _ a HG0 Hp). }
  pose proof (de_ctx_kept_xR cx Hpe m fpos ly3 S3 Hp3 W W mem (ms_mem ms) md HB HAR Hfin KEEP WK HCTX) as HCTX2.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : sv8 W (ms_mem ms) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { unfold sv8, DR_N.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 6 0) (c_n cx - dr_k' cx m) RG0) end.
    - rewrite ?ew_ewset_other by lia. exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zside.
    - zside. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (de1_extra (hs_fd h))) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite ?E32 in Q10.
  pmkst HS.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|].
  split; [exact HJ|].
  split; [exact HCTX2|].
  split; [exact SVN|].
  split; [exact Q1|].
  split; [exact Q10|].
  exact (de_regs_kept cx t m si _ regs _ KR HRG).
Qed.

Lemma de_stage2_xR : forall cx Hpe t m si h fpos ly3 S3 Hp3 k W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe -> 0 <= hs_fd h < 2 ^ 31 ->
  DE1_xR cx Hpe t m si h fpos ly3 S3 Hp3 k W c ->
  SRr segs W c (DE2_xR cx Hpe t m si h fpos ly3 S3 Hp3 k).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W c HB Hfd (regs & mem & md & -> & HJ & HCTX & SVN & Q1 & Q10 & HRG).
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin_xR cx Hpe fpos ly3 S3 Hp3 W mem md k HJ).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL. pose proof de_ceil_hi as HC64.
  assert (Hsp1 : spZ regs = lf_F cx).
  { unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
  (* relay_source's afn_pre at sp = F; ra = 0x848c4 = BASE + 9600 *)
  assert (HRET : A_dr_ret = 9600) by reflexivity. rewrite HRET in Q1.
  destruct (de_afn_pre_at_xR cx Hpe ly3 S3 Hp3 fpos k W mem md regs RSRC_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { exact C3. }
  { exact C4. }
  { exact C8. }
  { unfold RSRC_STK. lia. }
  { unfold RSRC_STK, YCfn.LLVMF_STK. lia. }
  pose proof HMOD as (_ & _ & HREL & _).
  change (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fr_relay_source)) mem (seg_rom segs)) md)
    with (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md).
  eapply SRr_bind.
  { exact (RSRC_x W ly3 S3 Hp3 regs mem md ch (lm_G m) (lm_es m) (hs_fd h) HPREc Q10 ltac:(lia) HREL HRV). }
  intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HKEEP & HA0).
  rewrite Hsp1 in HJc, HKEEP. unfold RSRC_STK in HKEEP.
  (* relay_source's journal inside this function's: ajournal_gx_sub_x at G_fr, the callee's lifted from G = [] *)
  assert (HJc' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] RSRC_STK (lf_F cx) [] ly3 S3 Hp3 W mem md [] ly3 S3 Hp3 W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono_xR segs B PST ARx [] G_fr 0 [] RSRC_STK (lf_F cx) [] ly3 S3 Hp3 W mem md [] ly3 S3 Hp3 W2 mem2 md2 0 _ (ajournal_gx_xR_mono segs B PST ARx (@wle segs) R WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc)).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k
     RSRC_STK (lf_F cx) 0 [] [] [] ly3 S3 Hp3 W2 mem2 md2 0 HJ HJc'
     ltac:(unfold RSRC_STK, YCfn.LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  (* every fact of the cut, kept across the call: relay_source keeps every byte outside [F - 16, F) *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W2 mem2 a)
    by (intros a Ha (Ho & _ & _); exact (HKEEP a Ha Ho)).
  assert (WK : forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a ->
      writable_at segs (arm W2 mem2) a)
    by (intros a Ha Hw; exact (proj2 (HKEEP a ltac:(lia) ltac:(lia)) Hw)).
  pose proof (de_ctx_kept_xR cx Hpe m fpos ly3 S3 Hp3 W W2 mem mem2 md HB HAR Hfin KEEP WK HCTX) as HCTX2.
  assert (SVN2 : sv8 W2 mem2 (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { apply (de_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply HKEEP; unfold DR_N in Hx; lia. }
  apply SRr_ret.
  exists regs2, mem2, md2.
  split; [rewrite Q1; reflexivity|].
  split; [exact HJ2|].
  split; [exact HCTX2|].
  split; [exact SVN2|].
  split; [exact (de_regs_pres cx t m si _ regs regs2 HP2 HRG)|].
  destruct HA0 as [(j & e & Hnth & Hfde & _ & Ha0) | (Hnone & Ha0)].
  - left. exists j.
    assert (Hjl : (j < length (lm_es m))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
    split; [exact Hjl|].
    rewrite (nth_error_nth (lm_es m) j dr_e0 Hnth). split; [exact Hfde | exact Ha0].
  - right. split; [exact (dr_nomatch_all m h Hnone) | exact Ha0].
Qed.

Lemma de_mk_K_xR : forall cx Hpe t m si h fpos ly3 S3 Hp3 k (W : world segs) regs mem md,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_latch)) mem (seg_rom segs)) md).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HJ (HFR & HFL & HMOD & HIN & HRV & HJT) SVN
    ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21)
    HSEP HLS HNP HRI Hatop Hpick Hor.
  exists regs, mem, md. split; [reflexivity|]. split; [exact HJT|].
  exists [(1, fpos)], ly3, S3, Hp3, k, (dr_skip m (dr_k' cx m)), fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
  split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
  split; [exact (dreR_LS_drain_skip _ _ _ _ _ _ _ _ _ _ _ _ EV_R cx t m ly3 S3 HLS)|]. split; [exact HNP|].
  split; [exact (dreR_RI_drain_skip _ _ _ _ _ _ _ _ _ _ _ _ EV_R cx t m si h HRI Hatop Hpick Hor)|].
  split; [repeat split; assumption|].
  split; [exact R25|]. split; [exact Ht|]. split; [exact R20|]. split; [exact SVN|].
  exact (dr_k'_rng cx m (proj1 Hatop)).
Qed.

Lemma de_none_xR : forall cx Hpe t m si h fpos ly3 S3 Hp3 k (W : world segs) regs mem md,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  dr_nomatch m h (Z.of_nat (length (lm_es m))) -> getr regs 10 = w64 0 ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md)
    (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HB HSEP HLS HNP HRI Hatop Hpick HJ HCTX SVN HRG Hnom R10.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin_xR cx Hpe fpos ly3 S3 Hp3 W mem md k HJ).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof HFR as (_ & HAWR & _).
  assert (HWA : forall a, lf_F cx + 192 <= a < lf_F cx + 200 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de3n_entry W regs mem (lf_F cx) C9 C27 ltac:(lia) HF32 HWA) as [HS SHOK].
  remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), C9.
    apply unsigned_lit_small. lia. }
  assert (E10 : ew E 10 = w64 0).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact R10. }
  clear HE.
  (* 0x848c4 `sd zero,192(s1)`; the run stops at 0x848c8 `beqz a0,84804` (not a trap) *)
  paj_run_tok_x RUNR HS HJ SHOK de_span.
  { unfold ss_de3n, de_rA. de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem ss_de3n In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
    destruct Hin. }
  psrr_branch_tok RUNR BR HS SHOK de_span.
  - (* a0 = 0: to the latch *)
    paj_run_to_tok_x RUNTOR HS HJ SHOK de_span AF_LLVM_latch.
    { unfold ss_de3n, de_rA. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3n In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept_xR cx Hpe m fpos ly3 S3 Hp3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret.
    eapply de_mk_K_xR; [exact HJ | exact HCTX2 | exact SVN2 | exact (de_regs_kept cx t m si _ regs _ KR HRG)
                    | exact HSEP | exact HLS | exact HNP | exact HRI | exact Hatop | exact Hpick | left; exact Hnom].
  - (* a0 <> 0: refuted by a0 = 0 *)
    exfalso.
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U10 : U Ev (SOff 10 0) = 0) by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E10 | lia]) end.
    rewrite W_traps.trap_br_eq, U10, U_lit in Hc by lia. cbn in Hc. discriminate Hc.
Qed.

Lemma de_found_xR : forall cx Hpe t m si h fpos ly3 S3 Hp3 k (W : world segs) regs mem md j,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  getr regs 10 = w64 (lm_G m + AENT * Z.of_nat j) ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md)
    (fun W' c' => INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t W' c' \/
       DLK_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t m j si h fpos ly3 S3 Hp3 k W' c').
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md j HB HSEP HLS HNP HRI Hatop Hpick HJ HCTX SVN HRG Hj Hfdj R10.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin_xR cx Hpe fpos ly3 S3 Hp3 W mem md k HJ).
  destruct (de_spF cx Hpe HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof HMOD as (_ & _ & HREL & _).
  pose proof HREL as (_ & _ & _ & _ & _ & _ & Hle16 & HGin & (tl & HTAB) & HENT & _).
  pose proof (de_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as HPAD.
  set (e := nth j (lm_es m) dr_e0) in *.
  assert (HEOK : aentry_ok B ly3 S3 W mem e) by (rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  pose proof HEOK as (Heof01 & _).
  assert (Hef2 : 0 <= re_eof (nth j (lm_es m) dr_e0) < 2 ^ 32) by (change (nth j (lm_es m) dr_e0) with e; lia).
  assert (Mef : val_mem segs (arm W mem) (lm_G m + AENT * Z.of_nat j + 4) 4 (re_eof e))
    by (exact (de_tbl_eof W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj Hef2)).
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hj16 : (j < 16)%nat) by lia.
  assert (HAT : ATABLE = 896) by reflexivity. assert (HAEN : AENT = 56) by reflexivity.
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { unfold AENT. pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
    rewrite D. replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  pose proof HFR as (_ & HAWR & _).
  assert (HWA : forall a, lf_F cx + 192 <= a < lf_F cx + 200 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de3f_entry ly3 S3 Hp3 W regs mem md (lf_F cx) (lm_G m) j (re_eof e) HAR C9 R10 C27
              ltac:(lia) HF32 HWA HGin HG4096 HSA8 ltac:(lia) ltac:(lia) Hj16 Mef ltac:(lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (de3_extra (re_eof e)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de3_extra (re_eof e))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = w64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact C9).
  assert (E10 : ew E 10 = w64 (lm_G m + AENT * Z.of_nat j)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_eof e))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  (* atom 244 = A_OBJ 3 = g_lock: the listing's auipc / addi pair at 0x848f4 resolves to it *)
  assert (ELK : ew E 244 = Z_to_bv 64 (rg_lock fr_RG)).
  { change 244%nat with (A_OBJ 3). subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite de_lock_val. reflexivity. }
  clear HE EEo.
  (* 0x848c4 `sd zero,192(s1)`; 0x848c8 `beqz a0,84804` (not a trap) decided by atom 10's lo = 4096;
     0x848d4 `bnez a0,850fc` (TRAP ALIGN8) decided by the runner from atom 10's fact mkAF 4096 140737479966720 3
     (seat R1/R2: T + 56 j is its own atom), no W_traps.v lemma; the shadow check 0x848e8 decided by
     mkSHE 10 0 56.  The run loads r->eof (atom 32) and stops at the eof test 0x848f0. *)
  paj_run_tok_x RUNR HS HJ SHOK de_span.
  { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem ss_de3f In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?U9 in Hr;
        unfold DR_AT in Hna; lia | ]).
    destruct Hin. }
  (* 0x848f0 `bnez a0,84804`: the eof test (not a trap) *)
  psrr_branch_tok RUNR BR HS SHOK de_span.
  - (* r->eof <> 0: end of file, the operation is a skip - to the latch *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e)
        by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hef1 : re_eof e = 1) by lia.
    paj_run_to_tok_x RUNTOR HS HJ SHOK de_span AF_LLVM_latch.
    { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3f In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept_xR cx Hpe m fpos ly3 S3 Hp3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. left.
    eapply de_mk_K_xR; [exact HJ | exact HCTX2 | exact SVN2 | exact (de_regs_kept cx t m si _ regs _ KR HRG)
                    | exact HSEP | exact HLS | exact HNP | exact HRI | exact Hatop | exact Hpick |].
    right. exists j. split; [exact Hj|]. split; [exact Hfdj | exact Hef1].
  - (* r->eof = 0: the relay still reads the source - a0 = s7 = &g_lock, `jal pthread_mutex_lock` *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e)
        by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    rename Hc into Hef0.
    paj_run_tok_x RUNR HS HJ SHOK de_span.
    { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3f In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept_xR cx Hpe m fpos ly3 S3 Hp3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    first [ pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0
          | pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0 ].
    cbn [ms_mem restrict] in RG0.
    assert (S192 : sv8 W (ms_mem ms0) (lf_F cx + DR_AT) 0).
    { unfold sv8, DR_AT.
      lazymatch type of RG0 with region_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 192 8%N (SLit 0) 0 RG0) end.
      - rewrite ?ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - reflexivity.
      - lia.
      - lia. }
    first [ lazymatch type of HS with st_ok _ ?Ev _ _ =>
              assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
                by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                           | rewrite ?ed_ewset; exact (proj2 HAE)]) end
          | lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
              assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
                by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                           | rewrite ?ed_ewset; exact (proj2 HAE)]) end ].
    first [ pose proof (regs_kept_of_st_ok segs _ _ _ regs _ DE_KD HS HAE2 ltac:(vm_compute; reflexivity)) as KR
          | pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KD HS HAE2
                          ltac:(vm_compute; reflexivity)) as KR ].
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23.
    rewrite ?ELK in Q10, Q23. rewrite ?E10 in Q22.
    pmkst HS.
    apply SRr_ret. right.
    destruct HCTX2 as (HFR2 & HFL2 & HMOD2 & HIN2 & HRV2 & HROM2).
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|].
    split; [exact HJ|].
    split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HROM2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|].
    split; [exact HRI|]. split; [exact Hatop|]. split; [exact Hpick|]. split; [exact Hj|].
    split; [exact Hfdj|]. split; [exact Hef0|].
    split; [exact SVN2|]. split; [exact S192|].
    split; [exact Q1|]. split; [exact Q10|]. split; [exact Q23|].
    (* dr_regs_call: lregs_common but s7, s9 = t, s4 = the new cursor, s5 = the source, s6 = the entry *)
    unfold dr_regs_call.
    rewrite (KR 2%bv ltac:(de_in)), (KR 8%bv ltac:(de_in)), (KR 9%bv ltac:(de_in)), (KR 18%bv ltac:(de_in)),
      (KR 19%bv ltac:(de_in)), (KR 24%bv ltac:(de_in)), (KR 26%bv ltac:(de_in)), (KR 27%bv ltac:(de_in)),
      (KR 3%bv ltac:(de_in)), (KR 4%bv ltac:(de_in)), (KR 25%bv ltac:(de_in)), (KR 20%bv ltac:(de_in)),
      (KR 21%bv ltac:(de_in)), Q22.
    repeat split; first [assumption | lia].
Qed.

Lemma de_stage3_xR : forall cx Hpe t m si h fpos ly3 S3 Hp3 k W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  DE2_xR cx Hpe t m si h fpos ly3 S3 Hp3 k W c ->
  SRr segs W c (fun W' c' => INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t W' c' \/
    (exists m j si h fpos ly3 S3 Hp3 k, DLK_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t m j si h fpos ly3 S3 Hp3 k W' c')).
Proof.
  intros cx Hpe t m si h fpos ly3 S3 Hp3 k W c HB HSEP HLS HNP HRI Hatop Hpick
    (regs & mem & md & -> & HJ & HCTX & SVN & HRG & [(j & Hj & Hfdj & R10) | (Hnom & R10)]).
  - eapply SRr_mono.
    { exact (de_found_xR cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md j HB HSEP HLS HNP HRI Hatop Hpick HJ HCTX SVN HRG
               Hj Hfdj R10). }
    intros W' c' _ [HK | HD]; [left; exact HK | right; exists m, j, si, h, fpos, ly3, S3, Hp3, k; exact HD].
  - eapply SRr_mono.
    { exact (de_none_xR cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HB HSEP HLS HNP HRI Hatop Hpick HJ HCTX SVN HRG
               Hnom R10). }
    intros W' c' _ HK. left. exact HK.
Qed.

Theorem dr_stage_entry_xR : forall cx Hpe t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 2 cx Hpe t W c ->
  SRr segs W c (fun W' c' => INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t W' c' \/
    (exists m j si h fpos ly3 S3 Hp3 k, DLK_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t m j si h fpos ly3 S3 Hp3 k W' c')).
Proof.
  intros cx Hpe t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI
    & HR).
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & Hk & HO & R11 & HPK).
  (* the operation is 2 (regsD's a1), so pick() ran: slot si holds h *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 2).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 2) with true in HPK.
  destruct HPK as (R20 & R6 & [(si & Hpk & R21) | (Hf & _)]); [|lia].
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (dr_k' cx m) in R20, R6.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (dr_kb cx m) in Hpk.
  pose proof HMOD as (Hlen4 & _).
  destruct (dr_pick_some (lm_hs m) (dr_kb cx m) si Hpk) as [Hsi [h Hh]].
  rewrite Hlen4 in Hsi.
  assert (HPICK : dr_pick cx m si h) by (split; [exact Hpk | split; [exact Hsi | exact Hh]]).
  assert (Hatop : dr_at_op cx m) by exact (conj Hk (conj HO Hop)).
  destruct (dreR_RI_src _ _ _ _ _ _ _ _ _ _ _ _ EV_R cx t m si h HRI HPICK) as (_ & _ & Hfd).
  (* the arm's registers are the dispatch's but for a0 and a1 *)
  assert (HRG : de_regs cx t m si (frame_addr ly3 1 fpos) regs).
  { unfold de_regs, lregs_common.
    rewrite (KR0 2%bv ltac:(de_in)), (KR0 8%bv ltac:(de_in)), (KR0 9%bv ltac:(de_in)), (KR0 18%bv ltac:(de_in)),
      (KR0 19%bv ltac:(de_in)), (KR0 23%bv ltac:(de_in)), (KR0 24%bv ltac:(de_in)), (KR0 26%bv ltac:(de_in)),
      (KR0 27%bv ltac:(de_in)), (KR0 3%bv ltac:(de_in)), (KR0 4%bv ltac:(de_in)), (KR0 25%bv ltac:(de_in)),
      (KR0 20%bv ltac:(de_in)), (KR0 21%bv ltac:(de_in)).
    repeat split; first [assumption | lia]. }
  assert (R6' : getr regs 6 = w64 (c_n cx - dr_k' cx m)) by (rewrite (KR0 6%bv ltac:(de_in)); exact R6).
  assert (HCTX : de_ctx cx m fpos ly3 S3 W mem) by exact (conj HFR (conj HFL (conj HMOD (conj HIN (conj HRV HROM))))).
  eapply SRr_bind; [exact (de_stage1_xR cx Hpe t m si h fpos ly3 S3 Hp3 k W regs mem md HB HJ HCTX HRG R6' Hatop HPICK)|].
  intros W1 c1 _ H1.
  eapply SRr_bind; [exact (de_stage2_xR cx Hpe t m si h fpos ly3 S3 Hp3 k W1 c1 HB Hfd H1)|].
  intros W2 c2 _ H2.
  exact (de_stage3_xR cx Hpe t m si h fpos ly3 S3 Hp3 k W2 c2 HB HSEP HLS HNP HRI Hatop HPICK H2).
Qed.

End drexR.

End drex.
