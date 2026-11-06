(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: SEG_PRO of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput (image B,
   fuzz_reply.asan-ubsan) OVER ARx (a Theorem Labs lane's route (b)): the ARx conversion of lib/B/W_LLVMFuzzerTestOneInput_pro.v's
   lf_seg_pro (a Theorem Labs lane's, Qed at a working branch 4bd2015c065, LS_pro at the proposed fr_LS_pro text),
   stated as B cut_x Section w's hypothesis SEG_PRO.  Neither _pro.v nor cut_x is edited.  The template is image A's
   lib/A/W_LLVMFuzzerTestOneInput_pro_x.v (SmallX); every conversion step below is that file's.
   - The Section header is B cut_x's Section w header (B .. RINV, with PST / ARx / hl / LAWS / HP0 / HG / LSx).
   - _pro.v's own hypotheses, in its order: the AR-free ones verbatim (TL, TLF, GWL, HEV, HZS, HGOBJ, HRO); OA at W2's
     W_op_add.oa_spec_g_x; ERRL at cut_x's errno_law_x; ASM1 / FFL at W_frame_x's astack_malloc_pres_x
     / frame_flag_lawP_x; GSHV over ARx; HFP_pro, LS_pro_oa, RI_pro, LS_pro with lf_base -> lf_base_x at the entry's
     ghost list Hp (bound after cx) and LS -> LSx, the rest of their text verbatim; LS_pro at B top_x's text
     (W_LLVMFuzzerTestOneInput_top_x.v:326, the room round's: xcnt_ok and HFH0 inside its existential).
   - KF-COUNT F2 (A f937a8adaa8, B top_x e1c3324bb6d): LS_pro_oa and LS_pro take mo_le MT (c_S cx) S2 0, which the
     seat gives from MO_FR (B top_x's text, W_LLVMFuzzerTestOneInput_top_x.v:287): the seat's set_fs costs nothing.
   - OA is op_add's contract at the kit's form at the room record RP: a Theorem Labs lane's room-form lib/B/W_op_add.v:2896
     oa_spec_g_x .. RP (24341ca6749).
   - The room round (A 7c2c4577649): Variable RP, RP_NP, NPF and LS_cnt; NP is carried from the entry through the
     seat (NPF) into op_add and from op_add's rp_RM post (RP_NP) to the first cut; prx_cells reads the pre's XCNT.
   - ML and SMP (cgif's model_laws / stack_malloc_progressP) are not hypotheses here: the generic stack_malloc seat
     W_frame_x.aj_stack_malloc_pres_at_x takes in their place its Section fsp hypotheses OWNLOW, WFx / WFL and
     SMALLOC, stated here in B's W_frame_x.v:744-755 text.
   - OWED (kit has no twin): BLKN, add_x's text (AR's al_blocks has 0 <= n, AR_laws_x's alx_blocks does not).
     Forced by the generic placement, add_x's text: HPST (the image is off PST; at the instance's PST := [] it holds
     trivially), which the ROM-view lemma W_journal_x.ajournal_gx_rom_view_x and the journal's image clause ask.
   - HP0 makes every ghost list of the walk empty, so the converted helpers are stated at Hp = []: AR0 is _pro.v's AR at
     [], AJ0 its journal at G, AJi0 the plain journal, AFN0 its afn_pre, LFB0 its lf_base.  The AR-free lemmas and
     definitions of _pro.v are CITED from it (with their section arguments, through local abbreviations); each one
     that reads AR is converted here under its name + _x with _pro.v's proof: AR's laws -> AR_laws_x's fields, the
     journal lemmas -> W_journal_x's, the runs -> paj_run_x_x / paj_run_to_x_x (the first run at G = [], W1Verify's
     template) and W_frame_x's SRr_run_pi_AJ_x; W_op_add.v's oa_call_keep / _blk / _hi over the generic journal
     (oa_call_keep_x / _blk_x / _hi_x, A's pro_call_img_x / _blk_x / _hi_x); the transport kit (lt_blk_x ..
     lt_ainput_kept_x) is lib/B/W_LLVMFuzzerTestOneInput_latch_x.v's, restated as _pro.v restates lib/B/W_LLVMFuzzerTestOneInput_latch.v's.
   - pro_afn_pre_B (_pro.v's bridge from Reusable's afn_pre to lib/B's YCbq copy, for W_op_add's AR contract) has no
     use here: the ARx contract above is stated over YCbqG's afn_pre_x, which the walk builds. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_img_x W_LLVMFuzzerTestOneInput_cut_x.
(* _pro.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
(* YG0s: frame_facts / client_byte_not_img, for the frame-vs-image bound at image B's top (pro_frm_img_hi) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
(* the same YCbq as lib/B/W_journal.v and the cut (Reusable's) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G.
(* the key-text helpers the relay entry's footprint names (lib/B/W_rep.v's) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_pro.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* the program interface's stack bound (_pro.v's local notation) *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------------------------------------
   The transport kit's block bounds over ARx: lib/B/W_LLVMFuzzerTestOneInput_latch_x.v's Section kit_x (lt_blk_x ..
   lt_ainput_kept_x), restated as _pro.v restates lib/B/W_LLVMFuzzerTestOneInput_latch.v's kit.  Its proofs take the zify flag latch_x gives them. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section kit_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* _latch.v:60 lt_low, a Section-local Ltac of the AR file (dropped at its End kit), restated *)
Ltac lt_low :=
  cbn [fst snd gfp]; unfold CEIL8 in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lt_ceil_lo; lia.

(* :83 lt_blk: a live block's bytes, and the 7 bytes of alignment slack a key's text may carry past them.  The size
   bound 0 <= n is a premise: alx_blocks does not carry it. *)
Lemma lt_blk_x : forall ly S Hp (W : world segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S Hp W mem md p n HAR Hin Hn.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H1 & H2 & _).
  pose proof (req_size_pos n Hn) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.

(* :108 struct list *)
Lemma lt_alist_x : forall ly S Hp (W : world segs) mem md LA l lines,
  ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= CEIL8 ->
  lt_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lt_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (lt_blk_x ly S Hp W mem md _ _ HAR K1 ltac:(lia)) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; lia|]. apply lt_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(unfold AREC; lia)) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
    cbn [gfp fst snd]. rewrite lt_bzs_len, length_app, lt_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* :138 struct source *)
Lemma lt_asrc_x : forall ly S Hp (W : world segs) mem md HA h,
  ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= CEIL8 ->
  lt_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (lt_alist_x ly S Hp W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (lt_alist_x ly S Hp W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (lt_alist_x ly S Hp W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hpb ltac:(unfold APARTIAL; lia)) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply lt_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite lt_bzs_len, Hpj. unfold APARTIAL, CEIL8 in *. lia.
    + apply lt_fp_low_app; [exact A1|]. apply lt_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* :164 one source_t of the relay's table *)
Lemma lt_aentry_x : forall ly S Hp (W : world segs) mem md e,
  ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
  lt_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : lt_fp_low (map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (lt_blk_x ly S Hp W mem md _ _ HAR M1 ltac:(lia)) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lt_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
      apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
      cbn [gfp snd]. rewrite lt_bzs_len, length_app. unfold CEIL8 in *. lia.
    + apply lt_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _ & Hk8 & _)]; [lia|].
        destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lt_bzs_len, lt_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold CEIL8. pose proof lt_ceil_lo. lia. }
        destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* :203 the relay's table, at fuzz_reply.asan-ubsan's globals *)
Lemma lt_arelay_x : forall ly S Hp (W : world segs) mem md G es,
  ARx ly S Hp W mem md -> arelay_at B fr_globals_b ly S W mem G es ->
  lt_fp_low (arelay_fp fr_globals_b G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR R8 ltac:(unfold ATABLE; lia)) as (P1 & P2 & P3).
  assert (HE : lt_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry_x ly S Hp W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lt_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry_x ly S Hp W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* :227 the controller's stream *)
Lemma lt_aout_x : forall ly S Hp (W : world segs) mem md c O mx no cap out,
  ARx ly S Hp W mem md -> aout_at B fr_globals_b ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  lt_fp_low (aout_fp B fr_globals_b cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply lt_fp_low_cons; [lt_low | lt_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | cbn; unfold CEIL8 in *; lia | apply lt_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* :329 the model *)
Lemma lt_amodel_kept_x : forall ly S Hp (W : world segs) mem md (W' : world segs) mem' m,
  ARx ly S Hp W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S Hp W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= CEIL8)
      by (unfold fr_RG, CEIL8; cbn; unfold ASRC; pose proof lt_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (lt_asrc_x ly S Hp W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lt_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (lt_arelay_x ly S Hp W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (lt_aout_x ly S Hp W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. lia.
Qed.

(* :445 the input block *)
Lemma lt_ainput_kept_x : forall cx ly S Hp (W : world segs) mem md (W' : world segs) mem',
  ARx ly S Hp W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S Hp W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hpe) | (Hn & Hin)]; [lia|].
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
  unfold CEIL8. lia.
Qed.
End kit_x.

(* the zify flag _pro.v's proofs (converted here) expect *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section prx.
(* ---- B cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:200-244) ---- *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
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
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2 / 0.4; A 7c2c4577649 pro_x :98-103): the allocator rules' room
   record RP (lib/B/W_journal_x.v roomp), whose room invariant is the cut's NP (the walk's RM := fun S _ => NP S; at
   top_x rp_RM RP := fun S _ => room_live_cf S = NP), and NPF: the fake frame's seat (a set_fs) keeps NP (top_x:
   room_live_set_fs) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis NPF : forall S f, NP S -> NP (set_fs f S).
(* ---- KF-COUNT F2: the meter law of the same seat, a set_fs costs nothing at MT (B top_x's MO_FR verbatim,
   lib/B/W_LLVMFuzzerTestOneInput_top_x.v:287): it gives LS_pro_oa's / LS_pro's premise mo_le MT (c_S cx) S2 0 ---- *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.

(* ---------------------------------------------------------------- SEG_PRO's own hypotheses, in _pro.v's order *)
(* op_add: _pro.v:624's OA over ARx, at the kit's form at the room record RP: a Theorem Labs lane's room-form lib/B/W_op_add.v:2896
   oa_spec_g_x .. RP (a working branch 24341ca6749, the B twin of A's 327fa3d3616; its post carries
   rp_RM RP S' kr, its pre rp_RM RP S (oa_rk + kr) and cnt_ok_pk RP oa_peak) *)
Hypothesis OA : W_op_add.oa_spec_g_x (PI := PB_fr) B PST ARx MT RP (BASE + AF_fr_op_add).
Hypothesis TL : PALib B.                            (* the allocator instance (lib/B/W_kit.v) *)
Hypothesis TLF : PALibF B.                          (* its fake-stack fields (lib/B/W_frame.v) *)
(* the stack_malloc seat's Section fsp hypotheses (B's W_frame_x.v:744-755, verbatim), in place of _pro.v's ML / SMP *)
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
(* _pro.v:631-632 over ARx: W_frame_x.v astack_malloc_pres_x at class 1 and frame_flag_lawP_x *)
Hypothesis ASM1 : astack_malloc_pres_x segs B ARx 1.
Hypothesis FFL : frame_flag_lawP_x segs B ARx.
(* _cut's two shared facts: glob_wr_law verbatim, errno_law at cut_x's errno_law_x *)
Hypothesis GWL : glob_wr_law G_fr.
Hypothesis ERRL : errno_law_x B ARx.
(* ---- the instance facts, verbatim (_pro.v:642-650) ---- *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_B.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis HGOBJ : forall a, inG G_fr_obj a -> inG G_fr a.
Hypothesis HRO : rom_out segs B G_fr.
(* _pro.v:651 GSHV over ARx (gx_prog_x's last conjunct at pro_G) *)
Hypothesis GSHV : forall ly S Hp (W : world segs) mem md a n, ARx ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG pro_G x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
(* ---- _pro.v:662-697 with lf_base -> lf_base_x at the entry's ghost list Hp and LS -> LSx ---- *)
Hypothesis HFP_pro : forall cx Hp T c O mx cap out,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ra_rel B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) T [] ->
  aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c O mx (Z.of_nat (length O)) cap out ->
  (exists rest, Permutation (ablocks B (c_ly cx) (c_S cx))
     (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest)) /\
  (T <> 0 -> forall a, T <= a < T + req_size ATABLE -> inFP (lf_FP fr_FP cx) a) /\
  (forall b, In b (aout_blks cap out) -> forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a).
Hypothesis LS_pro_oa : forall cx Hp (S2 : astate) pos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  mo_le MT (c_S cx) S2 0 ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S2 (oa_cost MT).
Hypothesis RI_pro : forall cx Hp q T' pj c O cap out,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  RINV cx 0 (pro_m q T' pj c O cap out).
(* LS_pro at the PROPOSED text (W8Add's fr_LS_pro, a working branch f57b3e2d0ca lib/A/ReplyLS.v:571;
   _pro.v:687): the blocks after op_add with the entry's split at its table T0 and relay_add's two cases.  The room
   round (ruling (a)): the entry's xcnt_ok and HFH0 (fr_hblks is the entry's table and g_out buffer, the three harness
   reads SEG_PRO makes) sit inside the existential.  B top_x's text (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:326-339,
   with KF-COUNT F2's `mo_le MT (c_S cx) S2 0 ->`) at this Section's names; inline, since s5-r1d's
   lib/B/ReplyBTxPro.v TX_LS_pro_xok has no F2 premise *)
Hypothesis LS_pro : forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
  mo_le MT S2 S (W_op_add.oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  LSx cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S.
(* the room round's count row for SEG_PRO (A 7c2c4577649 lib/A/W_LLVMFuzzerTestOneInput_pro_x.v:116-119, B names;
   discharged at the top by s5-r1d's fr_cnt_pro, A ba8e99b5bd2 lib/A/ReplyLScnt.v:300): op_add's count premise at the
   seat's state S2, whose blocks are the entry's.  The counts come from the entry's xcnt_ok (fr_lib_pre_cf_x's XCNT,
   at the entry's table T0 and g_out), not from LS *)
Hypothesis LS_cnt : forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) ->
  cnt_ok_pk RP W_op_add.oa_peak (ablocks B (c_ly cx) S2).
(* ---- forced by the generic relation and the placement PST (add_x's texts) ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX; ARx_blocks_law has no size conjunct).
   The text is W_kit_x.v's BLKN (add_x's). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the ROM-view lemma's premise and the journal's image clause; trivial at
   PST = [] *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* ---- _pro.v's AR-free items that take section arguments, cited with them ---- *)
Local Notation pro_cov := (W_LLVMFuzzerTestOneInput_pro.pro_cov G_fr HGOBJ).
Local Notation pro_rom_out := (W_LLVMFuzzerTestOneInput_pro.pro_rom_out B G_fr HRO).
Local Notation pro_rom_out_fr := (W_LLVMFuzzerTestOneInput_pro.pro_rom_out_fr B G_fr HRO).
Local Notation G_oa_fr := (W_LLVMFuzzerTestOneInput_pro.G_oa_fr G_fr HGOBJ).
Local Notation G_oa_rt := (W_LLVMFuzzerTestOneInput_pro.G_oa_rt B HEV).
Local Notation G_obj_err := (W_LLVMFuzzerTestOneInput_pro.G_obj_err B HEV).
Local Notation pro_extra := (W_LLVMFuzzerTestOneInput_pro.pro_extra B).
Local Notation pro_regs := (W_LLVMFuzzerTestOneInput_pro.pro_regs B).
Local Notation pro_ks := (W_LLVMFuzzerTestOneInput_pro.pro_ks B).

(* ---------------------------------------------------------------- the walk at the empty ghost list
   HP0: every ARx state's ghost list is [], so the walk runs at Hp = []: AR0 is _pro.v's AR, AJ0 its journal at G,
   AJi0 the plain journal, AFN0 its afn_pre, LFB0 its lf_base *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* the AR laws _pro.v cites, at AR0 (cgif's al_* -> AR_laws_x's alx_*, YCbq.v's lemmas -> their _x twins) *)
Local Notation al0_const ly S W mem md := (alx_const _ _ _ LAWS ly S [] W mem md).
Local Notation al0_frames ly S W mem md := (alx_frames _ _ _ LAWS ly S [] W mem md).
Local Notation al0_sep ly S W mem md := (alx_sep _ _ _ LAWS ly S [] W mem md).
Local Notation frames_bounds0 ly S W mem md := (frames_bounds_x _ _ _ LAWS ly S [] W mem md).
Local Notation blk_img0 ly S W mem md := (blk_img_x _ _ _ LAWS ly S [] W mem md).
(* cgif's al_blocks at AR0: ARx_blocks_law's six conjuncts and BLKN's size *)
Lemma al0_blocks : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
(* W_frame_x's IMGC: B's W_img_x.fr_img_cover_x, from the image law *)
Let IMGCx := W_img_x.fr_img_cover_x B ARx LAWS.
(* W_journal.v ajournal_gx_rom_view at AJ0: W_journal_x's, whose ROM-off-PST premise HPST gives *)
Lemma ajournal_gx_rom_view0 : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs)
    mem' md' k,
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  rom_out segs B G -> rom_view segs W mem -> rom_view segs W' mem'.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR Hrv.
  apply (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low G XO OUT STK sp0 FP ly S [] W mem md own ly' S' []
    W' mem' md' k HJ HR); [|exact Hrv].
  intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr].
Qed.
(* YCbq.v:2602 region_kept_stack_aj over ajournal_x (its proof: the journal's presence and stack clauses) *)
Lemma region_kept_stack_aj_x : forall E lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (Er : Z -> Prop)
    n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
  acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
  region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
    (K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
  pose proof asan_consts as (C1 & _).
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview segs). apply K1; lia.
  - intros _. apply (apresent_writable segs). apply Hpres. lia.
Qed.
(* _pro.v:702-708 and :846-851, restated (the runs over the generic chain: the first one at G = [], W1Verify's
   template; the plain one W_frame_x's SRr_run_pi_AJ_x) *)
Let HG_client := pro_cov (rg_client fr_RG) 4 ltac:(vm_compute; reflexivity).
Let HG_cbroken := pro_cov (rg_client_broken fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_nfd := pro_cov AG_NFD 4 ltac:(vm_compute; reflexivity).
Let HG_smax := pro_cov (rg_send_max fr_RG) 8 ltac:(vm_compute; reflexivity).
Let HG_gone := pro_cov (rg_gone fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_sdead := pro_cov (rg_send_dead fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_seintr := pro_cov (rg_send_eintr fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let HG0 : gx_ok segs B [] := gx_ok_nil segs B.
Let RUN0 := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS [] HG0 0 [].
Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS.
Let RUNX := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTOX := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* ---------------------------------------------------------------- what a callee taken at its own G keeps
   (lib/B/W_op_add.v's oa_call_keep / _blk / _hi over the generic journal; A's pro_x pro_call_img_x / _blk_x / _hi_x) *)
Lemma oa_call_keep_x : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  AJ0 G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
  forall a, in_img segs a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Him Hno He (HPST a Him) ltac:(apply fp_spares_closed; exact Hsk)).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
Lemma oa_call_keep_blk_x : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  AJ0 G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
  ~ inFP FP (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n j H0 H1 Hj Hfp).
  destruct (al0_blocks ly1 S1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
  apply (aview_gagree segs G' (w_H W0) m0 memS (p + j) HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  exact (blk_img0 ly1 S1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
Lemma oa_call_keep_hi_x : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  AJ0 G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx a Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (F1 a Ha Hno).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.

(* the live blocks are pairwise distinct *)
Lemma ad_nodup_x : forall ly S W mem md, AR0 ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al0_blocks ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al0_sep ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* a byte of a live block other than the relay table is outside a footprint inside that table *)
Lemma ad_fp_avoid_x : forall ly S W mem md p n T FP j,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) -> In (T, ATABLE) (ablocks B ly S) -> (p, n) <> (T, ATABLE) ->
  (forall a, inFP FP a -> T <= a < T + ATABLE) -> 0 <= j < req_size n -> ~ inFP FP (p + j).
Proof.
  intros ly S W mem md p n T FP j HAR Hp HT Hne HFP Hj Hf. apply HFP in Hf.
  pose proof (sep_blocks_x segs B ARx LAWS ly S [] W mem md p n T ATABLE HAR Hp HT Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. unfold ATABLE in Hf. lia.
Qed.

(* what a callee taken at its own G' keeps of a frame of the caller's state: the journal's frame clause, read
   through the overlay of ajournal_gx (an off-image byte is not one of G') *)
Lemma ad_call_keep_frm_x : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k
    cid pos a,
  gx_ok segs B G' ->
  AJ0 G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k cid pos a HGok HJx Hin Hr Hnf Ha Hni.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hnf).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa. exact (Hni (proj1 (HGok a HGa))).
Qed.

(* A fake frame is apart from the IMAGE OBJECT, at image B's top.  lib/B/W_frame.v frm_off_imgP proves exactly this
   but states it as the SHARED `off_img`, which cites IMG_TOP_A = 0x5fb000 (Reusable/YImgTop.v); image B's own top
   is IMG_TOP_B = 0x5fc000, and lib/B's kit bounds its objects by that (W_kit.v pa_obj_img, W_frame.v palf_uar_img).
   So the shared statement leaves a 4 KiB gap between a frame and an object, and this walk's region disjointness
   needs the B number.  Same proof as frm_off_imgP, with its own 0x5fc000 kept in the conclusion. *)
Lemma pro_frm_img_hi_x : forall ly S (W : world segs) mem md cid pos,
  AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
  (* over ARx: the image law alx_img puts a live fake frame at or above the image's top, which W_img_x's
     fr_img_cover_x (B's segments) puts at or above 0x5fc000 *)
  intros ly S W mem md cid pos HAR Hin. right.
  destruct (IMGCx ly S [] W mem md HAR) as [_ C2].
  pose proof (proj2 (alx_img _ _ _ LAWS ly S [] W mem md HAR) cid pos Hin) as Hf. lia.
Qed.

(* a byte of a live block is none of the seven globals the prologue stores (the blocks are off the image) *)
Lemma pro_blk_gst_x : forall ly S (W : world segs) mem md p n a, AR0 ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> pro_gst_out a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha. pose proof (blk_img0 ly S W mem md p n a HAR Hin Ha) as Hni.
  assert (HI : forall lo w, rng_inb lo w G_fr_obj = true -> ~ (lo <= a < lo + w))
    by (intros lo w Hr Hx; apply Hni; exact (proj1 (HG a (HGOBJ a (rng_cover lo w G_fr_obj Hr a Hx))))).
  split; [intros Hx; refine (HI 0xa2560 4 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8d60 1 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8da0 4 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8dc0 8 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8de0 1 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8e00 1 _ _); [vm_compute; reflexivity | lia]|].
  intros Hx; refine (HI 0x5d8e20 1 _ _); [vm_compute; reflexivity | lia].
Qed.

Lemma G_oa_prog_x : gx_prog_x (PI := PB_fr) B ARx pro_G.
Proof.
  split; [exact (gx_ok_sub segs B pro_G G_fr G_oa_fr HG)|].
  split; [exact G_oa_rt|].
  split; [exact (pro_rom_out pro_G G_oa_fr)|].
  split.
  { intros a Ha.
    pose proof (rng_all_in (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end)
      pro_G a ltac:(vm_compute; reflexivity) Ha) as H.
    cbv beta in H. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate H]. }
  split; [intros a Ha m; apply pro_wr_any; apply (segwb_ok segs);
          exact (rng_all_in (segwb segs) pro_G a ltac:(vm_compute; reflexivity) Ha)|].
  exact GSHV.
Qed.

Lemma pro_entry_x : forall W ly S regs mem md ch n,
  AFN0 LLVMF_STK ly S W regs mem md ch -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 26 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (pro_extra regs))) ss_pro0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_pro)) mem (seg_rom segs)))
  /\ sh_ok segs Bx [] (Eimg (Ereg regs (pro_extra regs))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S regs mem md ch n HPRE H11 Rn.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  destruct (al0_const ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
  pose proof (palf_uar_img B TLF) as HuR. pose proof (palf_uar_al B TLF) as HuA. pose proof (palf_sep B TLF) as HSEP.
  cbn [zseps zseps_from fst snd] in HSEP.
  set (F := pro_F regs).
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (pro_extra regs))). pose proof pa_B_ok as HBASE.
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E11 : ew E 11 = getr regs 11) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E247 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E271 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 6 ltac:(lia)) as HguR.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
  { intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
  split.
  - unfold ss_pro0, A_pro. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold pro_regions0, pr_zero, pr_save, pr_F, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * cbn [base_val]. rewrite UF. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
          [cbn [sv_denot]; rewrite E271, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 30)) 0 8 (SOff 33 0) SB);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
      * rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 6)) 0 8 (SOff 32 0) (as_uar_cell B));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
      * rewrite (VB 32%nat (as_uar_cell B) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
    + apply pairwise_disjoint_of_extents.
      unfold pro_regions0, pr_zero, pr_save, pr_F, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia).
      rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
      rewrite (VB 32%nat (as_uar_cell B) E32) by lia. cbn [base_val]. rewrite Usp, UF.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert HFv HspR Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HguR HuR HSEP. clear.
      unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [pro_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, UF, E11, H11, E32, E33, !unsigned_lit_small by (unfold SB; lia).
        change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
        revert HFv HFal HspR Hal16 Rn HuR HuA. clear. unfold SB. intros.
        repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [pro_facts0 f_alias alias_ok pro_alias]. split; [|exact I].
        assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
        apply U_inj. rewrite U_SAlu, (U_atom_off E 2 (spZ regs) (-320) E2'), (U_atom E 34 F E34) by lia.
        rewrite U_SLit. cbn [zalu_raw].
        assert (Hlo : 0 <= spZ regs + -320 < 2 ^ 64) by (destruct HspR as [HspR1 HspR2]; destruct HFv as [HFv | HFv]; rewrite HFv in HspR1; lia).
        change (zcanon (-32)) with (2 ^ 64 - 2 ^ 5). rewrite (land_neg_pow2_u64 (spZ regs + -320) 5 Hlo ltac:(lia)).
        assert (EF : spZ regs + -320 - (spZ regs + -320) mod 2 ^ 5 = F) by reflexivity.
        rewrite EF. apply zcanon_id. unfold M64. destruct HspR as [HspR1 HspR2]. destruct HFv as [HFv | HFv]; lia.
  - unfold sh_ok. constructor.
Qed.

(* keep the regions idxs of HS's state *)
Ltac pro_keep HS idxs :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (YP03.pick (ss_mem ssx) idxs) in
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_submem (PI := PB_fr) Ex ssx msx rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.

(* make region i read-only *)
Ltac pro_ro HS i :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  let HSk := fresh "HSk" in
  pose proof (ast_ok_pi_set_region (PI := PB_fr) Ex ssx msx i r (set_window r 0 0) HS eq_refl eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow sg Ex _ r 0 0 (st_ok_pi_region_nth (PI := PB_fr) Ex ssx msx i r HS eq_refl) ltac:(intros o Ho; lia)))
    as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.

(* rewrite every image atom's value in the goal, then compute each named image value *)
Ltac pro_val :=
  repeat match goal with |- context [VAL ?a] =>
    let a' := eval vm_compute in a in
    let v := eval vm_compute in (VAL a') in
    let Hv := fresh "Hval" in
    assert (Hv : VAL a = v) by (vm_compute; reflexivity); rewrite Hv; clear Hv end.

Ltac pro_img HEI :=
  repeat match goal with |- context [bv_unsigned (ew ?E ?a)] =>
    let a' := eval vm_compute in a in
    lazymatch eval vm_compute in ((A_TEXT <=? a') && (a' <? A_LIM))%nat with
    | true => rewrite (HEI a ltac:(unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia))
    end end;
  pro_val.

Ltac pro_imgh HEI H :=
  repeat match type of H with context [bv_unsigned (ew ?E ?a)] =>
    let a' := eval vm_compute in a in
    lazymatch eval vm_compute in ((A_TEXT <=? a') && (a' <? A_LIM))%nat with
    | true => rewrite (HEI a ltac:(unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia)) in H
    end end;
  repeat match type of H with context [VAL ?a] =>
    let a' := eval vm_compute in a in
    let v := eval vm_compute in (VAL a') in
    let Hv := fresh "Hval" in
    assert (Hv : VAL a = v) by (vm_compute; reflexivity); rewrite Hv in H; clear Hv end.

(* add the store region of global hi slot j, offset off, width w, whose bytes HGx puts in G_fr *)
Ltac pro_addg HS HEI j off w HGx :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_add_region Ex ssx msx (pr_g j off w) HS eq_refl
    ltac:(unfold region_ok, pr_g; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          pro_img HEI; split; [lia|]; split; [lia|]; split; [|constructor];
          intros o Ho; cbn [ms_mem restrict mkst]; apply GWL; apply HGx; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, pr_g; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          repeat match goal with H : bv_unsigned (ew ?E ?a) = _ |- context [bv_unsigned (ew ?E ?a)] => rewrite H end;
          pro_img HEI;
          unfold SB, off_img in *; repeat split; lia)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.

(* pin image atom n to its value in HS's facts (the token run's static check reads a store region's base off them) *)
Ltac pro_addf HS HEI n :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let v := eval vm_compute in (VAL n) in
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_add_fact Ex ssx msx n (mkAF v v 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia)); pro_val;
          rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.

(* region i of HS's state, as region_ok *)
Ltac pro_rgn HS i HR :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_pi_region_nth (PI := PB_fr) Ex ssx msx i r HS eq_refl) as HR end.

(* a register op_add's post keeps *)
Ltac pro_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* ------------------------------------------------------------------ the frame's numbers *)
Lemma pro_Fb_x : forall cx, LFB0 cx ->
  CEIL8 + 32000 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\ spZ (c_regs cx) - 352 <= lf_F cx /\
  spZ (c_regs cx) <= 2 ^ 47 /\ lf_F cx mod 32 = 0 /\ spZ (c_regs cx) mod 16 = 0.
Proof.
  intros cx (_ & HPRE0).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  pose proof (pro_F_al (spZ (c_regs cx) - 320)) as Hal32. rewrite <- HF32 in Hal32.
  assert (HFlo : CEIL8 + 32000 <= lf_F cx) by (unfold CEIL8, YCfn.LLVMF_STK in *; lia).
  split; [exact HFlo|]. split; [lia|]. split; [lia|]. split; [unfold YCfn.LLVMF_STK in *; lia|].
  split; [exact Hal32 | exact Hal16].
Qed.

(* the frame's bytes are present wherever the journal from the entry holds *)
Lemma pro_frame_wr_x : forall cx own ly3 S3 k (W : world segs) mem md,
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a.
Proof.
  intros cx own ly3 S3 k W mem md (_ & _ & (memS & HJi & _) & _) a Ha. rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply (apresent_writable segs). apply Hpres. lia.
Qed.

(* B has NO empty-input branch here: the `in.n != 0` test IS the head (0x845e0), so this run lands on INV_H alone
   (the cut's difference (2)); A's pro_fin had to split and could land on INV_X. *)
Lemma pro_fin_x : forall cx (W : world segs) regs mem md ly3 S3 k m fpos,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  pro_fr cx (frame_addr ly3 1 fpos) (flag_addr ly3 1 fpos) W mem ->
  pro_regs cx (frame_addr ly3 1 fpos) regs ->
  amodel_at B ly3 S3 W mem m -> lm_k m = 0 -> ainput_at B cx ly3 S3 W mem -> rom_view segs W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx 0 m ly3 S3 -> NP S3 -> RINV cx 0 m ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_pro_ret)) mem (seg_rom segs)) md)
    (INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] 0).
Proof.
  intros cx W regs mem md ly3 S3 k m fpos HB HJ HFR HRG HMOD Hk0 HIN HRV HSEP HLS HNP HRI.
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : YCfn.LLVMF_STK = 32768) by reflexivity.
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hn26 : 0 <= c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf_x in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  set (FF := frame_addr ly3 1 fpos) in *. set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds0 ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  destruct (al0_frames ly3 S3 W mem md 1 fpos HAR Hin1) as (HFFal & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1, HFFal.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  pose proof HFR as (HSV & H32 & H40 & H56 & H64 & H72 & H80 & H104 & H184 & HH0 & HH8 & HH16 & HFL & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R19 & R21 & R22 & R24 & R27 & R3 & R4).
  assert (HDIV : val_mem segs (arm W mem) 0x10320 8 DIV10)
    by (apply (rom_vmb_ok W mem _ _ _ HRV); vm_compute; reflexivity).
  assert (HWRF : forall a, sp0 - YCfn.LLVMF_STK <= a < sp0 -> writable_at segs (arm W mem) a)
    by (exact (pro_frame_wr_x cx _ _ _ _ W mem md HJ)).
  assert (HWR : forall a, F + 48 <= a < F + 160 -> writable_at segs (arm W mem) a)
    by (intros a Ha; apply HWRF; unfold sp0 in *; lia).
  destruct (pro_entry2 W regs mem F R9 R27 ltac:(unfold CEIL8 in *; lia) ltac:(unfold sp0 in *; lia) HFal HDIV HWR)
    as [HS SHOK].
  remember (Eimg (Ereg regs pro2_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs pro2_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  assert (E24 : ew E 24 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E27 : ew E 27 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  clear HE.
  pose proof pro_vals as (PV60 & PV61 & PV62 & PV63 & PV64 & PV65 & PV66 & PV69 & PV70 & PVO19 & PVO22 & PVO23 &
    PVO0 & PVO6 & PVO30 & PVLF).
  assert (VI : forall j v, VAL (A_HI j) = v -> (A_HI j < A_LIM)%nat -> 0 <= v < 2 ^ 64 -> ew E (A_HI j) = Z_to_bv 64 v).
  { intros j v Hv Hj Hr. apply bv_eq. rewrite (HEI (A_HI j) ltac:(unfold A_HI, A_TEXT in *; lia)).
    rewrite unsigned_lit_small by exact Hr. exact Hv. }
  assert (Hgs : rg_s fr_RG = 0x5d8e60) by (vm_compute; reflexivity).
  assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s fr_RG))
    by (apply bv_eq; rewrite (HEI (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
        rewrite unsigned_lit_small by (rewrite Hgs; lia); rewrite PVO19; reflexivity).
  change (A_OBJ 19) with 260%nat in E260.
  (* every fact of the cut but the slots the set-up stores, for any memory that keeps the bytes outside them *)
  assert (Herr : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8)
    by (rewrite HEV; unfold TFIB_ERRNO_B, CEIL8; pose proof lt_ceil_lo; lia).
  assert (KEEPF : forall mf, (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 48 <= a < F + 56) -> ~ (F + 96 <= a < F + 104) ->
      ~ (F + 120 <= a < F + 160) -> abyte_kept W mem W mf a) ->
    amodel_at B ly3 S3 W mf m /\ ainput_at B cx ly3 S3 W mf /\ rom_view segs W mf /\ jt_rom W mf /\
    pro_fr cx FF (flag_addr ly3 1 fpos) W mf).
  { intros mf KO.
    assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mf a)
      by (intros a Ha; apply KO; unfold CEIL8 in *; lia).
    assert (HRVf : rom_view segs W mf) by exact (lt_rom_kept W W mem mf HRV KL).
    split; [exact (lt_amodel_kept_x B ARx LAWS ly3 S3 [] W mem md W mf m HAR HMOD (proj1 Herr) (proj2 Herr) KL)|].
    split; [exact (lt_ainput_kept_x B ARx LAWS cx ly3 S3 [] W mem md W mf HAR HIN (eq_sym HlenP) KL)|].
    split; [exact HRVf|]. split; [exact (lt_jt_kept W W mem mf (pro_jt W mem HRV) KL)|].
    assert (KH : forall a v, (forall x, a <= x < a + 8 -> abyte_kept W mem W mf x) -> sv8 W mem a v -> sv8 W mf a v)
      by (intros a v Hk Hv; exact (lt_sv8_kept W W mem mf a v Hk Hv)).
    split; [intros o r Hor; apply KH; [|exact (HSV o r Hor)]; intros x Hx;
            unfold saved_regs in Hor; cbn [In] in Hor;
            repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; apply KO; unfold sp0 in *; lia|]);
            destruct Hor|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H32]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H40]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H56]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H64]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H72]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H80]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H104]|].
    split; [apply KH; [intros x Hx; apply KO; unfold sp0 in *; lia | exact H184]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH0]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH8]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH16]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFL]|].
    split; [apply (akept_awr W mem W mf); [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFW]|].
    split; [apply (akept_garr8 W mem W mf); [intros x Hx; apply KL; cbn [length fake_shadow] in Hx;
            pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia
            | exact HSH]|].
    apply (akept_awr W mem W mf); [intros x Hx; apply KL;
      pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia | exact HSW]. }
  paj_run_to_tok_x RUNTOX HS HJ SHOK Bspan AF_LLVM_head.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
        first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
    destruct Hin'. }
  clear HF.
  lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
    assert (KO1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 48 <= a < F + 56) -> ~ (F + 96 <= a < F + 104) ->
      ~ (F + 120 <= a < F + 160) -> abyte_kept W m1 W m2 a) end.
  { intros a Ha H1 H2 H3. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
    destruct Hin'. }
  clear HFr.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs pro2_extra pro_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  pro_rgn HS 0%nat HR48. pro_rgn HS 1%nat HR96. pro_rgn HS 2%nat HR120.
  pose proof (pro_sh_den E 27 260 SB (rg_s fr_RG) 0 E27 E260 ltac:(unfold SB; lia) ltac:(rewrite Hgs; lia)
    ltac:(rewrite Hgs; lia)) as D120.
  pose proof (pro_sh_den E 27 260 SB (rg_s fr_RG) 4 E27 E260 ltac:(unfold SB; lia) ltac:(rewrite Hgs; lia)
    ltac:(rewrite Hgs; lia)) as D152.
  rewrite Z.add_0_r in D120.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
    apply SRr_ret; exists rf, mf, df end.
  split; [reflexivity|].
  lazymatch type of KO1 with forall a, _ -> _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
    destruct (KEEPF m2 KO1) as (HMODf & HINf & HRVf & HJTf & HFRf) end.
  pose proof HFRf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFLf & _).
  split; [exact HJTf|].
  exists [(1, fpos)], ly3, S3, [], k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|].
  split.
  { apply (pro_aframe cx FF (flag_addr ly3 1 fpos) W _ HFRf).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 48 56 48 56 48 8 (SOff 260 0) (rg_s fr_RG) HR48 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E260, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(rewrite Hgs; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 104 96 104 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(unfold SB in *; cbn [Z.of_N Z.mul]; lia) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 120 8
        (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 260 0) (SLit 3))) (SB + rg_s fr_RG / 8) HR120 U9
        ltac:(cbn [In]; tauto) D120
        ltac:(rewrite Hgs; unfold SB; split; [vm_compute; discriminate | vm_compute; reflexivity])
        ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 128 8 (SOff 260 4) (rg_s fr_RG + 4) HR120 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E260, unsigned_lit_small by (rewrite Hgs; lia); reflexivity)
        ltac:(rewrite Hgs; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 136 8 (SLit DIV10) DIV10 HR120 U9
        ltac:(cbn [In]; tauto) eq_refl
        ltac:(unfold DIV10; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 152 8
        (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 260 4) (SLit 3))) (SB + (rg_s fr_RG + 4) / 8) HR120 U9
        ltac:(cbn [In]; tauto) D152
        ltac:(rewrite Hgs; unfold SB; split; [vm_compute; discriminate | vm_compute; reflexivity])
        ltac:(zside)).
    - exact (pro_frame_wr_x cx _ _ _ _ W _ _ HJ).
    - lia.
    - lia. }
  split; [exact HFLf|].
  split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
  split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
  unfold lregs_H, lregs_common.
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite Q18; change 350%nat with (A_HI 70); apply VI; [exact PV70 | cbv; lia | unfold HI_G_SRC; lia]|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite Q26; change 349%nat with (A_HI 69); apply VI; [exact PV69 | cbv; lia | unfold HI_G_NOUT; lia]|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite Q25; reflexivity|].
  split; [rewrite (KR 21%bv ltac:(cbv; tauto)), Hk0, Z.sub_0_r; exact R21|].
  split; [rewrite (KR 22%bv ltac:(cbv; tauto)), Hk0, Z.add_0_r; exact R22|].
  split; [unfold OPS_MAX; lia|].
  rewrite Hk0. lia.
Qed.

(* the fake frame keeps its place across a journal (frame_addr / flag_addr read only ly_F, which layout_le keeps) *)
Lemma pro_ff_eq_x : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k cid pos,
  AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.

(* op_add's afn_pre at sp = F: the donor's afn_pre_at, whose achain is the entry's chain with this frame pushed
   (the prologue saved ra at sp0-8 and s0 at sp0-16: achain_push) -- or, when sp0 is within 16 bytes of the stack
   top, the empty chain (lib/B/W_LLVMFuzzerTestOneInput_add.v lt_afn_pre_at, from the saved registers alone) *)
Lemma pro_afn_pre_at_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
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
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
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
      | unfold raZ in Hra40; lia | lia
      | rewrite (Znumtheory.Zmod_div_mod 8 16 sp0) by (try lia; exists 2; reflexivity); rewrite Hal16; reflexivity
      | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* ---- the room round: the entry's three harness cells (g_src, g_capout, g_out) read back as the relay's table and
   the stream's buffer; SEG_PRO's HFH0 and the identification of the pre's XCNT witnesses with fr_gi's (A 7c2c4577649
   prx_cells) ---- *)
Lemma prx_cells : forall ly S Hp (W : world segs) mem md T c O mx cap out,
  ARx ly S Hp W mem md ->
  ra_rel B fr_RG ly S W mem T [] ->
  aout_at B fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out ->
  rdword (aview segs (w_H W) mem) (rg_src fr_RG) = Some T /\
  rdword (aview segs (w_H W) mem) (rg_capout fr_RG) = Some cap /\
  rdword (aview segs (w_H W) mem) (rg_out fr_RG) = Some out.
Proof.
  intros ly S Hp W mem md T c O mx cap out HAR HRA HAO.
  pose proof asan_consts as (C1 & _).
  assert (BLK : forall p n, In (p, n) (ablocks B ly S) -> 0 <= p /\ 0 <= n /\ p + n < 2 ^ 64).
  { intros p0 n0 Hin.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p0 n0 HAR Hin) as (_ & H4096 & Hce & _).
    pose proof (BLKN ly S Hp W mem md p0 n0 HAR Hin) as Hn0.
    assert (Hrq : n0 <= req_size n0) by (unfold req_size; destruct (Z.eqb_spec n0 0); lia).
    lia. }
  assert (HT : rdword (aview segs (w_H W) mem) (rg_src fr_RG) = Some T).
  { destruct HRA as [(-> & _ & Hv & _) | (Hv & _ & _ & _ & _ & _ & _ & Hin & _)].
    - apply (W_frame.rdword_of_val_mem segs (w_H W) mem); [exact Hv | lia].
    - destruct (BLK T ATABLE Hin) as (H0 & H1 & H2).
      apply (W_frame.rdword_of_val_mem segs (w_H W) mem); [exact Hv | unfold ATABLE in *; lia]. }
  destruct HAO as (_ & _ & _ & _ & Hcap & _ & Hout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & Hco).
  split; [exact HT|].
  destruct Hco as [(-> & -> & _) | (Hc & _ & Hin & _)].
  - split; (apply (W_frame.rdword_of_val_mem segs (w_H W) mem); [assumption | lia]).
  - destruct (BLK out cap Hin) as (H0 & H1 & H2).
    split; (apply (W_frame.rdword_of_val_mem segs (w_H W) mem); [assumption | lia]).
Qed.

(* ------------------------------------------------------------------ 0x84590 `jal op_add` *)
Lemma pro_mid_x : forall cx regs mem md S2 k fpos,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) mem md k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 -> NP S2 ->
  pro_fr cx (frame_addr (c_ly cx) 1 fpos) (flag_addr (c_ly cx) 1 fpos) (c_W cx) mem ->
  getr regs 1 = w64 (BASE + A_pro_ret) -> pro_regs cx (frame_addr (c_ly cx) 1 fpos) regs ->
  pro_glob (c_W cx) mem ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) mem a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRr segs (c_W cx) (cfg_at segs (BASE + AF_fr_op_add) regs mem md) (INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] 0).
Proof.
  intros cx regs mem md S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HFR Hra HRG HGL KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & _ & _ & Hgi & Hrom & _).
  destruct Hgi as (HGP0 & HCL & (T & HRR) & (c0 & O & mx0 & cap & out & HAO) & (gn0 & HGN) & HLK & HWK & HTU &
    (lst & HLS0) & HLW).
  (* the room round: the pre's XCNT (its 22nd conjunct) at fr_gi's table T and g_out (cap, out), read off the same three
     cells (prx_cells), and HFH0 *)
  pose proof HPRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HXC0 & _).
  destruct HXC0 as (Tx & cx0 & Ox & mxx & capx & outx & HRRx & HAOx & HXC).
  pose proof (proj1 HPREE) as HARe.
  destruct (prx_cells _ _ _ _ _ _ T c0 O mx0 cap out HARe HRR HAO) as (CT & CC & CO).
  destruct (prx_cells _ _ _ _ _ _ Tx cx0 Ox mxx capx outx HARe HRRx HAOx) as (CTx & CCx & COx).
  rewrite CT in CTx. rewrite CC in CCx. rewrite CO in COx.
  injection CTx as <-. injection CCx as <-. injection COx as <-. clear HRRx HAOx.
  change (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) with (input_blks cx) in HXC.
  assert (HFH0 : fr_hblks (c_W cx) (c_mem cx) = (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out).
  { unfold fr_hblks. cbv zeta. change tfibsegs with segs. rewrite CT, CO, CC. unfold aout_blks. reflexivity. }
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL8.
  pose proof (HFP_pro cx [] T c0 O mx0 cap out HB HRR HAO) as ((rest0 & HPERM0) & HFPT & HFPO).
  set (W := c_W cx) in *. set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
  assert (Hgs : rg_s fr_RG = 0x5d8e60) by (vm_compute; reflexivity).
  assert (Hgs' : rg_s fr_globals = 0x5d8e60) by (vm_compute; reflexivity).
  (* ---- kept from the entry to the call ---- *)
  assert (KG : forall a, inG G_keep a -> aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros a Ha; apply KEEP; left; exact Ha).
  assert (KBk : forall p n a, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> p <= a < p + req_size n ->
      aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros p0 n0 a Hp Ha; apply KEEP; right; exists p0, n0; split; [exact Hp | exact Ha]).
  assert (KGv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W mem) a n v).
  { intros a n0 v Hr Hv. apply (ad_vm_view W W (c_mem cx) mem); [|exact Hv].
    intros x Hx. exact (KG x (rng_cover a (Z.of_nat n0) G_keep Hr x Hx)). }
  assert (AW : forall a n, rng_inb a n G_fr_obj = true -> forall (W' : world segs) m', awr W' m' a n).
  { intros a n0 Hr W' m' i Hi. apply (G_obj_wr (a + i) (rng_cover a n0 G_fr_obj Hr (a + i) ltac:(lia))). }
  (* ---- the call's facts ---- *)
  assert (HCLc : forall i, (i < 4)%nat -> asrc_closed W mem (oa_HA i)).
  { intros i Hi. destruct (HCL i Hi) as [HZ _]. split.
    - apply (pro_garr8_view W W (c_mem cx) mem); [|exact HZ].
      intros x Hx. apply KG. rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply (rng_cover (rg_s fr_globals) (4 * ASRC) G_keep ltac:(vm_compute; reflexivity)).
      unfold oa_HA, ASRC in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->|[->| ->]]]; vm_compute; reflexivity. }
  assert (Hos : forall i, nth i [0; 0; 0; 0] 0 = 0) by (intros i; destruct i as [|[|[|[|[|i]]]]]; reflexivity).
  assert (HRRc : ra_rel B fr_RG (c_ly cx) S2 W mem T []).
  { destruct HRR as [(HT0 & _ & (E1 & E2 & E3 & E4 & E5 & E6)) | HAT].
    - left. split; [exact HT0|]. split; [reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E1]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E3]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E5] | apply AW; vm_compute; reflexivity].
    - right. pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _).
      apply (arelay_at_kept B fr_RG (c_ly cx) (c_S cx) W (c_mem cx) (c_ly cx) S2 W mem T [] HAT).
      + intros r Hr a Ha. split.
        * unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- apply KG. refine (rng_cover (rg_src fr_RG) 8 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_nsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_capsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply (KBk T ATABLE a HTin). change (req_size ATABLE) with 896. unfold ATABLE in Ha. lia.
        * intros _. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- refine (G_obj_wr a (rng_cover (rg_src fr_RG) 8 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_nsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_capsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- rewrite <- Eab2 in HTin.
             destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & _ & Hpr & _).
             apply (apresent_writable segs). apply (proj1 (Hpr a ltac:(change (req_size ATABLE) with 896;
               unfold ATABLE in Ha; lia))).
      + intros b Hb. rewrite Eab2. cbn [arelay_blks map concat app] in Hb. destruct Hb as [<- | []]. exact HTin. }
  assert (HLKc : alock_at fr_RG W mem false).
  { destruct HLK as (L1 & L2 & L3 & L4).
    split; [apply KGv; [vm_compute; reflexivity | exact L1]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L2]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L3] | apply AW; vm_compute; reflexivity]. }
  assert (HWKc : awake_at fr_RG W mem) by (apply KGv; [vm_compute; reflexivity | exact HWK]).
  assert (HRVc : rom_view segs W mem)
    by (eapply ajournal_gx_rom_view0; first [exact Hsegs | exact LAWS | exact HJ | exact pro_rom_out_fr | exact Hrom]).
  (* ---- op_add's afn_pre, its room and its meter ---- *)
  pose proof HFR as (HSV & H32 & H40 & H56 & H64 & H72 & H80 & H104 & H184 & HH0 & HH8 & HH16 & HFLw & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R19 & R21 & R22 & R24 & R27 & R3 & R4).
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  destruct (pro_afn_pre_at_x cx (c_ly cx) S2 fpos k W mem md regs OA_STK HB HJ HSV Hsp) as (ch & HPREc).
  { rewrite Hra. apply ret_ok_codeptr_v; [unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite Hra, unsigned_lit_small by (unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia).
    unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput. lia. }
  { exact R3. } { exact R4. } { exact R8. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK. lia. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK. lia. }
  destruct (LS_pro_oa cx [] S2 fpos HB Eab2 Hfrs2 Hnev2 Hbb2 HMO2) as (Hroom & Hmok).
  (* the entry's T: when the table exists it is a live block of the entry, above 4096 *)
  assert (HT4096 : T <> 0 -> 4096 <= T /\ In (T, ATABLE) (ablocks B (c_ly cx) (c_S cx))).
  { intros HT0. destruct HRR as [(HT0' & _) | HAT]; [contradiction|].
    pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _). split; [|exact HTin]. rewrite <- Eab2 in HTin.
    destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & H4096 & _). exact H4096. }
  (* ---- op_add, at its own G ---- *)
  assert (HGcov1 : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG pro_G a)
    by (intros a Ha; exact (pro_inG_rng pro_G (rg_s fr_globals) (4 * ASRC) a ltac:(cbn [In pro_G app RA_G];
          repeat (first [left; reflexivity | right])) Ha)).
  assert (HGcov2 : forall a, A_NFD <= a < A_NFD + 4 -> inG pro_G a)
    by (intros a Ha; exact (pro_inG_rng pro_G A_NFD 4 a ltac:(cbn [In pro_G app RA_G];
          repeat (first [left; reflexivity | right])) Ha)).
  assert (HGcov3 : forall a, inG (RA_G fr_globals) a -> inG pro_G a)
    by (intros a Ha; unfold pro_G; apply inG_app; right; exact Ha).
  destruct HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eapply SRr_bind.
  { exact (OA pro_G G_oa_prog_x W (c_ly cx) S2 [] regs mem md ch [0; 0; 0; 0] 0 T []
      HPREc
      ltac:(rewrite Hsp; exact HFal) ltac:(rewrite Hfrs2; vm_compute; reflexivity) eq_refl
      ltac:(intros i _; rewrite Hos; lia)
      ltac:(intros i Hi; rewrite Hos; exact (oa_zero_vm _ _ _ 4 4 (proj1 (HCLc i Hi)) ltac:(lia)
              ltac:(unfold ASRC; cbn; lia)))
      ltac:(intros i Hi _; exact (HCLc i Hi))
      G3 ltac:(lia) HZS HGcov1 HGcov2 HGcov3 HRRc HLKc HWKc HRVc
      ltac:(intros _; split; [cbn; lia | intros []]) Hroom Hmok
      (* the room round: the room from the seat's NP (kr := 0), the counts from the entry's xcnt_ok (LS_cnt) *)
      0%nat (proj2 (RP_NP S2 _) HNP2) (LS_cnt cx T cap out S2 HXC Eab2)). }
  cbv beta. intros W3 c3 Hwle3
    (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & kk & -> & HJo & HP4 & HAPK & HOK & Hfrs4 & HRM4 & HSome).
  (* the room after op_add: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S4 0%nat) HRM4) as HNP4.
  (* oa_post_x's ghost list is [] (HP0 at the post's journal) *)
  hp0g HJo.
  assert (Hof : oa_first [0; 0; 0; 0] = Some 0%nat) by reflexivity.
  rewrite Hof in HSome. cbv beta iota in HSome.
  destruct HSome as (q & T' & pj & HSRC & HNFD & HREL & HLK4 & HPERM & HMLE).
  cbn [app] in HREL. change (100 + 0) with 100 in HSRC, HREL. change (0 + 1) with 1 in HNFD.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo) as HAR4.
  pose proof (proj1 G_oa_prog_x) as HGoa.
  assert (Hsk : ~ YI16.sink_open_fp (oa_FP [0; 0; 0; 0] T [])).
  { unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
    intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & _). lia. }
  (* the journal from the entry, through op_add (lifted from pro_G to G_fr) *)
  pose proof (ajournal_gx_G_mono_x segs B PST ARx pro_G G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G_oa_fr HJo) as HJo'.
  assert (HFP1 : forall a, inFP (oa_FP [0; 0; 0; 0] T []) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B (c_ly cx) S2) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B (c_ly cx) S2) a).
  { intros a Ha. left. unfold oa_FP in Ha. rewrite Hof in Ha. unfold ra_FP in Ha.
    destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [destruct Ha as (r & [] & _)|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & HTin).
    split; [apply (HFPT HT0); change (req_size ATABLE) with 896; unfold ATABLE in *; lia|].
    exists T, ATABLE. split; [rewrite Eab2; exact HTin | change (req_size ATABLE) with 896; lia]. }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 [] W mem md k
     OA_STK (spZ regs) 0 [] (oa_FP [0; 0; 0; 0] T []) [] ly4 S4 [] W3 mem4 md4 kk HJ HJo'
     ltac:(rewrite Hsp; unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK; lia)
     ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP1) as HJ4.
  cbn [app] in HJ4.
  destruct (pro_ff_eq_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos HJo) as [EFF EFL]. fold FF in EFF.
  (* ---- what op_add keeps ---- *)
  assert (KP : forall a, inG G_pst a -> aview segs (w_H W3) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. pose proof (G_pst_obj a Ha) as Ho. destruct (HG a (HGOBJ a Ho)) as (Him & Hno & _).
    exact (oa_call_keep_x pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo Hsk a Him
      (G_pst_oa a Ha) Hno (G_obj_err a Ho)). }
  assert (KPv : forall a n v, rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W3 mem4) a n v).
  { intros a n0 v Hr Hv. apply (ad_vm_view W W3 mem mem4); [|exact Hv].
    intros x Hx. exact (KP x (rng_cover a (Z.of_nat n0) G_pst Hr x Hx)). }
  assert (KGPv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true -> rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W3 mem4) a n v)
    by (intros a n0 v H1 H2 Hv; exact (KPv a n0 v H2 (KGv a n0 v H1 Hv))).
  assert (KS3 : forall i, (1 <= i < 4)%nat -> asrc_closed W3 mem4 (oa_HA i)).
  { intros i Hi. destruct (HCLc i ltac:(lia)) as [HZ _]. split.
    - apply (pro_garr8_view W W3 mem mem4); [|exact HZ]. intros x Hx.
      rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply HOK.
      + apply HGcov1. unfold oa_HA, ASRC in *. lia.
      + unfold oa_wr. rewrite Hof. intros [Hx1 | [Hx2 | Hx3]].
        * unfold oa_HA, ASRC in *. cbn [Z.of_nat] in Hx1. lia.
        * unfold oa_HA, ASRC, A_NFD in *. rewrite Hgs' in *. lia.
        * pose proof (pro_ra_g x Hx3). unfold oa_HA, ASRC in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[-> | ->]]; vm_compute; reflexivity. }
  (* the entry's blocks the call keeps: all but the relay's table, whose new entry relay_add writes *)
  assert (KBo : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) mem (p + j)).
  { intros p n j Hp Hne Hj. assert (Hp2 : In (p, n) (ablocks B (c_ly cx) S2)) by (rewrite Eab2; exact Hp).
    apply (oa_call_keep_blk_x pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HGoa HJo p n j Hp2).
    - destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)).
      + right. right. exact Hp2.
      + right. exact Hp2.
    - exact Hj.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      pose proof (sep_blocks_x segs B ARx LAWS (c_ly cx) S2 [] W mem md p n T ATABLE HAR2 Hp2 HTin (Hne HT0)) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
      unfold ATABLE in *. lia. }
  (* the input block and the controller's buffer are not the relay's table (the entry's blocks are distinct) *)
  assert (ND0 : List.NoDup (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest0)).
  { pose proof HPREE as (HAR0 & _). exact (Permutation_NoDup HPERM0 (ad_nodup_x _ _ _ _ _ HAR0)). }
  assert (HinpT : forall p n, In (p, n) (input_blks cx) -> T <> 0 -> (p, n) <> (T, ATABLE)).
  { intros p n Hp HT0 Heq. rewrite Heq in Hp. apply (pro_nd_app _ _ _ (T, ATABLE) ND0 Hp).
    rewrite (proj2 (Z.eqb_neq T 0) HT0). apply in_or_app. left. left. reflexivity. }
  assert (HoutT : forall b, In b (aout_blks cap out) -> T <> 0 -> b <> (T, ATABLE)).
  { intros b Hb HT0 Heq. rewrite Heq in Hb. pose proof (pro_nd_appr _ _ _ ND0) as ND1.
    rewrite (proj2 (Z.eqb_neq T 0) HT0) in ND1. cbn [app] in ND1. inversion ND1 as [|x l Hx _]; subst.
    apply Hx. apply in_or_app. left. exact Hb. }
  assert (KBt : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) (c_mem cx) (p + j))
    by (intros p n j Hp Hne Hj; rewrite (KBo p n j Hp Hne Hj); exact (KBk p n (p + j) Hp ltac:(lia))).
  (* ---- the cut after op_add: the controller's stream ---- *)
  destruct (ERRL ly4 S4 [] W3 mem4 md4 HAR4) as ((v & Hv & Hvr) & Hvw).
  pose proof HAO as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 &
    A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26).
  assert (HAOp : aout_at B fr_RG ly4 S4 W3 mem4 (W_rep.CTL 3 0 0 0 v) O 0 (Z.of_nat (length O)) cap out).
  { split; [apply KPv; [vm_compute; reflexivity | exact G4]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A3]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A5]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A7]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G1]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G2]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G6]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G7]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [exact Hv|]. split; [exact Hvw|]. split; [exact Hvr|].
    split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|].
    destruct A26 as [A26 | (Hc & Hnc & Hio & junk & Hjl & Hjg)]; [left; exact A26|].
    right. split; [exact Hc|]. split; [exact Hnc|].
    assert (Hio2 : In (out, cap) (ablocks B ly4 S4)).
    { destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hio. }
    split; [exact Hio2|]. exists junk. split; [exact Hjl|].
    apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hjg].
    intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx.
    replace x with (out + (x - out)) by lia.
    apply (KBt out cap (x - out)); [exact Hio | intros HT0; apply (HoutT (out, cap));
      [unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)); left; reflexivity | exact HT0] |].
    pose proof (req_size_pos cap ltac:(lia)) as [_ Hrc]. lia. }
  (* the input *)
  assert (HINp : ainput_at B cx ly4 S4 W3 mem4).
  { split.
    - destruct Hin as [Hin | (Hn & Hpin)]; [left; exact Hin|]. right. split; [exact Hn|].
      destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hpin.
    - destruct Hin as [(Hn0 & _) | (Hn & Hpin)].
      + rewrite Hnl in Hn0. assert (Hpl : c_pl cx = []) by (apply length_zero_iff_nil; lia).
        rewrite Hpl. intros j Hj. cbn in Hj. lia.
      + apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hgarr].
        intros x Hx. rewrite length_map in Hx. rewrite <- Hnl in Hx. replace x with (c_p cx + (x - c_p cx)) by lia.
        apply (KBt (c_p cx) (c_n cx) (x - c_p cx)); [exact Hpin | intros HT0; apply (HinpT (c_p cx) (c_n cx));
          [unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); left; reflexivity | exact HT0] |].
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrc]. lia. }
  (* the model *)
  assert (HMOD4 : amodel_at B ly4 S4 W3 mem4 (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out)).
  { unfold amodel_at, pro_m. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [reflexivity|].
    split.
    { intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth aslot].
      - exact HSRC.
      - exact (KS3 1%nat ltac:(lia)).
      - exact (KS3 2%nat ltac:(lia)).
      - exact (KS3 3%nat ltac:(lia)).
      - lia. }
    split; [exact HREL|]. split; [exact HAOp|].
    split; [split; [apply KPv; [vm_compute; reflexivity | exact G5]
                  | split; [apply AW; vm_compute; reflexivity | left; reflexivity]]|].
    split; [exact HLK4|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HWK]|].
    split; [exact HNFD|]. split; [apply AW; vm_compute; reflexivity|]. split; [unfold OPS_MAX; lia|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HTU]|].
    split; [exists lst; apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HLS0]|].
    apply AW; vm_compute; reflexivity. }
  (* the frame and the fake frame *)
  assert (HIV : forall x, F <= x < 2 ^ 47 -> aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (oa_call_keep_hi_x pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HGoa HJo x);
      [unfold CEIL8 in *; lia | rewrite Hsp; lia]. }
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof (frm_off_imgP_x B ARx LAWS IMGCx _ _ [] _ _ _ 1 fpos HAR2 Hin1) as HFimg.
  change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg. unfold off_img in HFimg.
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HAR2 Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (FRV : forall x, (FF <= x < FF + 128) \/ (SB + FF / 8 <= x < SB + FF / 8 + 16) ->
      aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx.
    assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold SB in *; lia).
    assert (Hni : ~ in_img segs x).
    { intros Hi. destruct Hx as [Hx | Hx].
      - exact (frm_img_x segs B ARx LAWS (c_ly cx) S2 [] W mem md 1 fpos x HAR2 Hin1
          ltac:(change (fs_frame_bytes 1) with 128; unfold FF in Hx; lia) Hi).
      - pose proof (pa_segs_low x Hi). unfold SB, kLowMemEnd in *. lia. }
    apply (ad_call_keep_frm_x pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk 1 fpos x HGoa HJo Hin1);
      [| | exact Hx64 | exact Hni].
    - unfold frame_rng, in_zr, shadow_addr. rewrite <- SB_SHADOW_OFF. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. fold FF.
      destruct Hx as [Hx | Hx]; [left | right]; lia.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & Happ & _).
      change (req_size ATABLE) with 896 in Happ.
      destruct Hx as [Hx | Hx].
      + pose proof (sep_block_frame_x segs B ARx LAWS (c_ly cx) S2 [] W mem md T ATABLE 1 fpos HAR2 HTin Hin1) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
        change (fs_frame_bytes 1) with 128 in Hd. fold FF in Hd. unfold ATABLE in *. lia.
      + apply (fshadow_not_app FF 16 T 896 x ltac:(lia) ltac:(lia) Happ); [unfold SB in Hx; lia | unfold ATABLE in *; lia]. }
  assert (Hin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4, Hfrs2; left; reflexivity).
  destruct (al0_frames ly4 S4 W3 mem4 md4 1 fpos HAR4 Hin4) as (_ & _ & HFp & HFs).
  rewrite EFF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFR4 : pro_fr cx FF (flag_addr (c_ly cx) 1 fpos) W3 mem4).
  { split.
    { intros o r Hor. apply (ad_vm_view W W3 mem mem4); [|exact (HSV o r Hor)].
      intros x Hx. apply HIV. unfold saved_regs in Hor. cbn [In] in Hor.
      repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; unfold sp0 in *; lia|]). destruct Hor. }
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H32]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H40]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H56]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H64]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H72]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H80]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H104]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H184]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH0]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH8]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH16]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HFLw]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split; [apply (pro_garr8_view W W3 mem mem4); [intros x Hx; apply FRV; right; cbn [length fake_shadow] in Hx; lia
            | exact HSH]|].
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers op_add keeps *)
  assert (HRG4 : pro_regs cx FF regs4).
  { split; [rewrite (pro_pres regs regs4 2%bv HP4 ltac:(pro_cs)); exact R2|].
    split; [rewrite (pro_pres regs regs4 8%bv HP4 ltac:(pro_cs)); exact R8|].
    split; [rewrite (pro_pres regs regs4 9%bv HP4 ltac:(pro_cs)); exact R9|].
    split; [rewrite (pro_pres regs regs4 19%bv HP4 ltac:(pro_cs)); exact R19|].
    split; [rewrite (pro_pres regs regs4 21%bv HP4 ltac:(pro_cs)); exact R21|].
    split; [rewrite (pro_pres regs regs4 22%bv HP4 ltac:(pro_cs)); exact R22|].
    split; [rewrite (pro_pres regs regs4 24%bv HP4 ltac:(pro_cs)); exact R24|].
    split; [rewrite (pro_pres regs regs4 27%bv HP4 ltac:(pro_cs)); exact R27|].
    split; [rewrite (pro_pres regs regs4 3%bv HP4 ltac:(pro_cs)); exact R3|].
    rewrite (pro_pres regs regs4 4%bv HP4 ltac:(pro_cs)); exact R4. }
  (* the blocks, as ablocks_sep lists them *)
  assert (Em : model_blks (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) =
    (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
  assert (ND4 : List.NoDup (ablocks B ly4 S4)) by exact (ad_nodup_x _ _ _ _ _ HAR4).
  assert (HSEP4 : ablocks_sep B fr_FP cx (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) ly4 S4).
  { split.
    - exists rest0. rewrite Em. rewrite Eab2 in HPERM. exact (pro_sep_perm _ _ _ _ _ T T' q HPERM0 HPERM).
    - intros b Hb. rewrite Em in Hb. destruct Hb as [<- | [<- | Hb]].
      + destruct HPERM as [(HT0 & HP) | (HT0 & -> & HP)].
        * left. intros Hb'. pose proof (Permutation_NoDup HP ND4) as ND. inversion ND as [|x l Hx ND']; subst.
          apply Hx. right. rewrite Eab2. exact Hb'.
        * right. intros a Ha. cbn [fst snd] in Ha. exact (HFPT HT0 a Ha).
      + left. intros Hb'. destruct HPERM as [(_ & HP) | (_ & _ & HP)]; pose proof (Permutation_NoDup HP ND4) as ND.
        * inversion ND as [|x l _ ND']; subst. inversion ND' as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
        * inversion ND as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
      + right. exact (HFPO b Hb). }
  (* the cut's two Variables, and the ROM view after op_add *)
  assert (Hc0ex : exists c1 mx1, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c1 O mx1
    (Z.of_nat (length O)) cap out) by (exists c0, mx0; exact HAO).
  assert (HPERM' : exists T0 rest, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly4 S4) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly4 S4) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx)))))
    by (exists T, rest0; split; [exact HPERM0|]; split; [exact HXC|]; split; [exact HFH0|];
        rewrite <- Eab2; exact HPERM).
  pose proof (LS_pro cx [] q T' pj (W_rep.CTL 3 0 0 0 v) O cap out S2 fpos ly4 S4 HB Hc0ex eq_refl eq_refl eq_refl
    eq_refl Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HMLE HPERM') as HLS4.
  pose proof (RI_pro cx [] q T' pj (W_rep.CTL 3 0 0 0 v) O cap out HB Hc0ex eq_refl eq_refl eq_refl eq_refl) as HRI4.
  assert (HRV4 : rom_view segs W3 mem4)
    by (eapply ajournal_gx_rom_view0;
        first [exact Hsegs | exact LAWS | exact HJo | exact (proj1 (proj2 (proj2 G_oa_prog_x))) | exact HRVc]).
  (* the loop's set-up *)
  rewrite Hra. rewrite <- EFF in HFR4, HRG4. rewrite <- EFL in HFR4.
  exact (pro_fin_x cx W3 regs4 mem4 md4 ly4 S4 (k + kk) _ fpos HB HJ4 HFR4 HRG4 HMOD4 eq_refl HINp HRV4 HSEP4
    HLS4 HNP4 HRI4).
Qed.

(* an image atom's value, by computation *)
Ltac pro_rwimg HEI n :=
  let v := eval vm_compute in (VAL n) in
  rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia));
  replace (VAL n) with v by (vm_compute; reflexivity).

Lemma pro_at_call_x : forall cx S2 k fpos E regs4 m4 md4,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) m4 md4 k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 -> NP S2 ->
  img_env VAL A_LIM E ->
  bv_unsigned (ew E 2) = spZ (c_regs cx) -> bv_unsigned (ew E 34) = lf_F cx ->
  bv_unsigned (ew E 39) = frame_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 512) = flag_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 513) = SB + frame_addr (c_ly cx) 1 fpos / 8 -> ew E 33 = Z_to_bv 64 SB ->
  (forall r, (r < 32)%nat -> ew E r = getr (c_regs cx) (Z_to_bv 5 (Z.of_nat r))) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 346 (-1868) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 345 (-1892) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 344 (-1916) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 343 (-1936) 8 8 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 342 (-1964) 4 4 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 341 (-2024) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 340 32 4 4 3) ->
  region_ok segs E (arm (c_W cx) m4) pc_sh -> region_ok segs E (arm (c_W cx) m4) pc_ff ->
  region_ok segs E (arm (c_W cx) m4) pc_save -> region_ok segs E (arm (c_W cx) m4) pc_F ->
  getr regs4 1 = Z_to_bv 64 (BASE + A_pro_ret) -> getr regs4 2 = ew E 34 -> getr regs4 3 = ew E 3 ->
  getr regs4 4 = ew E 4 -> getr regs4 8 = ew E 2 -> getr regs4 9 = ew E 34 ->
  getr regs4 19 = Z_to_bv 64 (bv_unsigned (ew E 39) + 32) ->
  getr regs4 21 = ew E 11 -> getr regs4 22 = ew E 10 -> getr regs4 24 = ew E 513 -> getr regs4 27 = ew E 33 ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) m4 a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRr segs (c_W cx) (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + AF_fr_op_add)) m4 (seg_rom segs)) md4)
    (INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] 0).
Proof.
  intros cx S2 k fpos E regs4 m4 md4 HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HEI U2 U34 U39 U512 U513 E33 EA
    RG7 RG6 RG5 RG4 RG3 RG2 RG1 RSH RFF RSV RF Q1 Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q24 Q27 KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & _).
  pose proof HPREE as (_ & _ & _ & Hgp & Htp & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof lt_ceil_lo as HCL8.
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  destruct (al0_frames _ _ _ _ _ 1 fpos HAR Hin1) as (_ & _ & HFp & HFs).
  fold FF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (ER : forall (r : nat) (b : bv 5), (r < 32)%nat -> Z.of_nat r = bv_unsigned b -> ew E r = getr (c_regs cx) b).
  { intros r b Hr Hb. rewrite (EA r Hr). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hb.
    apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  (* the frame and the fake frame *)
  assert (HFR : pro_fr cx FF (flag_addr (c_ly cx) 1 fpos) (c_W cx) m4).
  { unfold pro_fr. cbv zeta. fold F.
    split.
    { apply (pro_saved_of_region E _ _ _ _ _ _ _ (c_regs cx) RSV U2 EA).
      unfold saved_regs.
      repeat (apply Forall_cons; [cbn [fst snd In]; repeat (first [left; reflexivity | right]) |]).
      apply Forall_nil. }
    assert (FS : forall off (nv : nat) v, In (YP09.mkChunk off (CVal 8 (SOff nv 0))) (YP09.r_chunks pc_F) ->
        bv_unsigned (ew E nv) = v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (F + off) v).
    { intros off nv v Hc Hv Hr. unfold sv8.
      refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 34 F _ 32 192 32 192 off 8 (SOff nv 0) v RF U34 Hc _ Hr
        ltac:(cbn; lia)) eq_refl eq_refl).
      cbn [sv_denot]. rewrite Hv, Z.add_0_r. reflexivity. }
    split; [apply (FS 32 340%nat); [cbn; tauto | pro_rwimg HEI 340%nat; reflexivity | unfold HI_G_CLIENT; lia]|].
    split; [apply (FS 40 345%nat); [cbn; tauto | pro_rwimg HEI 345%nat; reflexivity | unfold HI_G_SDEAD; lia]|].
    split; [apply (FS 56 346%nat); [cbn; tauto | pro_rwimg HEI 346%nat; reflexivity | unfold HI_G_SEINTR; lia]|].
    split; [apply (FS 64 344%nat); [cbn; tauto | pro_rwimg HEI 344%nat; reflexivity | unfold HI_G_GONE; lia]|].
    split; [apply (FS 72 343%nat); [cbn; tauto | pro_rwimg HEI 343%nat; reflexivity | unfold HI_G_SMAX; lia]|].
    split; [apply (FS 80 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 104 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 184 39%nat); [cbn; tauto | exact U39 | lia]|].
    assert (FH : forall off e v, In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks pc_ff) ->
        sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (FF + off) v).
    { intros off e v Hc Hv Hr. unfold sv8.
      exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 off 8 e v RFF U39 Hc Hv Hr
        ltac:(cbn; lia)) eq_refl eq_refl). }
    split; [rewrite <- (Z.add_0_r FF); apply (FH 0 (SLit 1102416563)); [cbn; tauto | reflexivity | lia]|].
    split; [apply (FH 8 (SOff 263 0)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 263%nat; reflexivity|].
    split; [apply (FH 16 (SOff 240 8388)); [cbn; tauto | | unfold YCfn.A_LLVMF; lia];
            cbn [sv_denot]; pro_rwimg HEI 240%nat; reflexivity|].
    split; [apply (FH 120 (SOff 512 0)); [cbn; tauto | | ];
            [cbn [sv_denot]; rewrite U512, Z.add_0_r; reflexivity
            | destruct (FFL _ _ [] _ _ _ 1 fpos HAR Hin1) as (_ & _ & _ & (HFL4096 & _ & HFLc)); lia]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split.
    { apply (pro_shadow_garr8 E _ 513 _ _ 0 16 0 0 RSH U513).
      intros j Hj. do 16 (destruct j as [|j]; [cbn; repeat (first [left; reflexivity | right]) |]). lia. }
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers *)
  assert (HRG : pro_regs cx FF regs4).
  { unfold pro_regs, w64. fold F.
    split; [rewrite Q2, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q8, (ER 2%nat 2%bv ltac:(lia) eq_refl); reflexivity|].
    split; [rewrite Q9, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q19, U39; reflexivity|].
    split; [rewrite Q21, (ER 11%nat 11%bv ltac:(lia) eq_refl), H11; reflexivity|].
    split; [rewrite Q22, (ER 10%nat 10%bv ltac:(lia) eq_refl), H10; reflexivity|].
    split; [rewrite Q24, <- U513, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q27; exact E33|].
    split; [rewrite Q3, (ER 3%nat 3%bv ltac:(lia) eq_refl), Hgp; reflexivity|].
    rewrite Q4, (ER 4%nat 4%bv ltac:(lia) eq_refl), Htp; reflexivity. }
  (* the globals *)
  assert (GV : forall n off w (sz : N) v a, region_ok segs E (arm (c_W cx) m4) (pc_g n off w sz v) ->
      (A_TEXT <= n < A_LIM)%nat -> VAL n + off = a -> N.to_nat sz = Z.to_nat w -> 0 <= v < 2 ^ (8 * Z.of_N sz) ->
      (Z.of_N sz <= 8) -> val_mem segs (arm (c_W cx) m4) a (Z.to_nat w) v).
  { intros n0 off w sz v a HR Hn Ha Hw Hv Hs.
    refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ n0 (VAL n0) _ off (off + w) off (off + w) off sz
      (SLit v) v HR (HEI n0 Hn) ltac:(cbn; tauto) _ Hv Hs) Ha Hw).
    reflexivity. }
  assert (HGL : pro_glob (c_W cx) m4).
  { unfold pro_glob.
    split; [exact (GV 340%nat 32 4 4%N 3 (rg_client fr_RG) RG1 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 341%nat (-2024) 1 1%N 0 (rg_client_broken fr_RG) RG2 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 342%nat (-1964) 4 4%N 0 AG_NFD RG3 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 343%nat (-1936) 8 8%N 0 (rg_send_max fr_RG) RG4 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 344%nat (-1916) 1 1%N 0 (rg_gone fr_RG) RG5 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 345%nat (-1892) 1 1%N 0 (rg_send_dead fr_RG) RG6 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    exact (GV 346%nat (-1868) 1 1%N 0 (rg_send_eintr fr_RG) RG7 ltac:(unfold A_TEXT, A_LIM; lia)
      ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* the return address *)
  assert (Hra : getr regs4 1 = w64 (BASE + A_pro_ret)) by (rewrite Q1; reflexivity).
  exact (pro_mid_x cx regs4 m4 md4 S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HFR Hra HRG HGL KEEP).
Qed.

(* ~ in_wrange E rs a, region by region: each window is read off (its base by the U facts in context, an image base
   by HEIx) and refuted by a lia over few facts: an empty window; a stack window above F (Ha, HFlo, HFsp); a window
   the one fact Hk about a misses *)
Ltac pro_nwr_k HEIx Ha HFlo HFsp :=
  let r := fresh "r" in let Hin' := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin' & Hr);
  lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end;
  cbn [In] in Hin';
  repeat (destruct Hin' as [<- | Hin'];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      repeat match goal with Hu : bv_unsigned (ew ?E ?x) = _ |- _ =>
        match type of Hr with context [bv_unsigned (ew E x)] => rewrite Hu in Hr end end;
      pro_imgh HEIx Hr; unfold SB in Hr;
      first [ clear - Hr; lia
            | clear - Hr Ha HFlo HFsp; lia
            | match goal with Hk : ~ (_ <= _ < _) |- _ => clear - Hr Hk; lia end
            | match goal with Hk : (_ \/ _) |- _ => clear - Hr Hk; lia end ] | ]);
  destruct Hin'.

Theorem lf_seg_pro_x : forall cx Hp, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  SRr segs (c_W cx) (lf_entry cx) (INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp 0).
Proof.
  intros [ly S W regs mem md p n pl M] Hp HB.
  (* the entry's ghost list is empty (HP0 on the pre's ARx): the walk runs at [] *)
  pose proof HB as (_ & HPRE_). hp0a (proj1 (proj1 HPRE_)). clear HPRE_.
  pose proof HB as (HAI & HPRE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & Hroom & Hnp & Hgi & Hrom & Hrod & Hsink & Hfd & Hsrt & Hmeta & Hmo & Hstkr & Hhb & _).
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_M lf_entry] in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL8.
  assert (Rn : 0 <= n < 2 ^ 26) by (destruct Hin as [(-> & _) | (Hn & _)]; lia).
  destruct (pro_entry_x W ly S regs mem md [] n HPRE H11 Rn) as [HS SHOK].
  (* the journal at G = [] (W1Verify's template: ajournal_gx_nil_x of ajournal_x_init) *)
  pose proof (proj2 (ajournal_gx_nil_x segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (ajournal_x_init segs B PST ARx LLVMF_STK (lf_FP fr_FP (LFCX ly S W regs mem md p n pl M)) ly S [] W regs mem md [] HPRE)) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  remember (Eimg (Ereg regs (pro_extra regs))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n0 r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  set (F := pro_F regs) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (HAE : env_agree 32 (Ereg regs (pro_extra regs)) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  unfold cfg_at. change (w64 YCfn.A_LLVMF) with (Z_to_bv 64 (BASE + A_pro)).
  (* run 1: the frame, the saved registers, the fake-stack test; stops at __asan_stack_malloc_1 (0x84478) *)
  paj_run_tok_x RUN0 HS HJ SHOK Bspan.
  { apply awr_ok_x_of0. intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?UF in Hr;
        first [ lia | left; lia ] | ]).
    destruct Hin'. }
  (* the call to __asan_stack_malloc_1 (128): the fake frame FF; the journal at G = [] is the plain ajournal_x *)
  apply ajournal_gx_nil_x in HJ.
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  rewrite (palf_sm1 B TLF).
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
      eapply (aj_stack_malloc_pres_at_x segs B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 1 ASM1 ltac:(lia)
        W rg mm LLVMF_STK (spZ regs) _ ly S [] W mem md [] ly S [] _ 0 (F - spZ regs) _ HJ) end.
    - unfold spZ at 1. rewrite R2, UF. lia.
    - destruct HFv as [HFe | HFe]; rewrite HFe;
        [replace (spZ regs - 320 - spZ regs) with ((-20) * 16) by lia | replace (spZ regs - 336 - spZ regs) with ((-21) * 16) by lia];
        apply Z_mod_mult.
    - lia.
    - rewrite WS, Hes. lia.
    - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Hfrs. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPg & Hsf).
  (* the room round: the seat is a set_fs of the entry's state, so NP holds there (NPF) *)
  assert (HNP2 : NP S2) by (destruct Hsf as (fs & ->); exact (NPF _ fs Hnp)).
  (* KF-COUNT F2: and it costs nothing at the meter (MO_FR), LS_pro_oa's / LS_pro's premise *)
  assert (HMO2 : mo_le MT S S2 0) by (destruct Hsf as (fs & ->); exact (MO_FR S fs)).
  set (FF := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
  pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
  destruct (al0_const _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
  destruct (al0_const _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
  rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
  pose proof (palf_uar_img B TLF) as HuR.
  jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact UF | lia | lia | lia | cbn; lia | cbn; lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 30)));
        [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kg1) | exact (val_mem_of_rdword segs _ _ _ _ Kg2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 30) (VAL (A_OBJ 30)) 8 SHADOW_OFF);
        [exact (HEI (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kc1) | exact (val_mem_of_rdword segs _ _ _ _ Kc2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 6) (VAL (A_OBJ 6)) 8 (as_uar_cell B));
        [exact (HEI (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kgu1) | exact (val_mem_of_rdword segs _ _ _ _ Kgu2) | lia].
    - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
        [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 segs _ _ _ _ Ku1) | exact (val_mem_of_rd32 segs _ _ _ _ Ku2) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (HAEa : env_agree 32 (Ereg regs (pro_extra regs)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
  clear HEa.
  prreg HS (10%bv : bv 5) RF.
  (* seat the fake frame: FF in atom 39 (a0), its flag FL in 512, the frame's shadow SB + FF / 8 in 513 *)
  assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
  destruct (al0_frames _ _ _ _ _ 1 fpos HARb Hfin2) as (HFal2 & HFapp & HFpres & HFSpres).
  destruct (FFL _ _ [] _ _ _ 1 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  fold FF FL in HFal2, HFapp, HFpres, HFSpres, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
  assert (RF' : ew Ea 39 = Z_to_bv 64 FF) by (rewrite <- RF, Ha0; reflexivity).
  assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
  assert (U2a : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
  assert (U34a : bv_unsigned (ew Ea 34) = F) by (rewrite OLDa by lia; exact UF).
  assert (U32a : bv_unsigned (ew Ea 32) = as_uar_cell B) by (rewrite OLDa, E32 by lia; apply unsigned_lit_small; lia).
  assert (U241 : bv_unsigned (ew Ea 241) = VAL (A_OBJ 0)) by exact (HEIa (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U247 : bv_unsigned (ew Ea 247) = VAL (A_OBJ 6)) by exact (HEIa (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U271 : bv_unsigned (ew Ea 271) = VAL (A_OBJ 30)) by exact (HEIa (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (HFF8 : FF / 8 = 4 * (FF / 32)).
  { pose proof (Z.div_mod FF 32 ltac:(lia)) as D. rewrite HFal2, Z.add_0_r in D. rewrite D at 1.
    replace (32 * (FF / 32)) with (4 * (FF / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  assert (HFF8lo : 512 <= FF / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HFF8hi : FF / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 6 ltac:(lia)) as HguR.
  pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
  pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 6)). pose proof (pa_val_range (A_OBJ 30)).
  pose proof (ff_seat_ok Ea _ _ (w_H W) mem2 39 33 512 1 FF FL HS eq_refl ltac:(vm_compute; reflexivity)
    RF' E33a ltac:(lia) ltac:(lia) ltac:(right; reflexivity) HFal2 ltac:(lia) ltac:(change (fs_frame_bytes 1) with 128; lia)
    ltac:(lia)
    ltac:(change (fs_frame_bytes 1) with 128; intros a Ha; exact (proj1 (HFpres a Ha)))
    ltac:(change (fs_frame_bytes 1 / 8) with 16; intros i Hi; exact (proj1 (HFSpres i Hi)))
    ltac:(change (fs_frame_bytes 1) with 128; exact Hflag) ltac:(change (fs_frame_bytes 1) with 128; exact Hz)) as HS3.
  pose proof (pro_frm_img_hi_x _ _ _ _ _ 1 fpos HARb Hfin2) as HFimg. change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg.
  set (Eb := havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)]) in HS3.
  assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; subst Eb; apply YN3v.ew_havoc_old; exact Hm).
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
  assert (U512 : bv_unsigned (ew Eb 512) = FL).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. lia. }
  assert (U513 : bv_unsigned (ew Eb 513) = SB + FF / 8).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. unfold SB. lia. }
  assert (U39b : bv_unsigned (ew Eb 39) = FF) by (rewrite OLDb, RF' by lia; apply unsigned_lit_small; lia).
  assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact U2a).
  assert (U34b : bv_unsigned (ew Eb 34) = F) by (rewrite OLDb by lia; exact U34a).
  assert (U32b : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb by lia; exact U32a).
  assert (U241b : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U241).
  assert (U247b : bv_unsigned (ew Eb 247) = VAL (A_OBJ 6)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U247).
  assert (U271b : bv_unsigned (ew Eb 271) = VAL (A_OBJ 30)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U271).
  match type of HS3 with ?A1 -> ?A2 -> _ => assert (HD1 : A1); [|assert (HD2 : A2); [|specialize (HS3 HD1 HD2)]] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_fregion, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1) with 128. rewrite U39b, U2b, U34b, U241b, U247b, U271b, U32b.
    unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_sregion, ff_fregion, fshadow_region, fframe_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1 / 8) with 16. change (fs_frame_bytes 1) with 128.
    rewrite U513, U39b, U2b, U34b, U241b, U247b, U271b, U32b.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd8a. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as Hd8b.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as Hd8c.
    unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  clear HS. rename HS3 into HS. norm_ss HS.
  (* run 2 (plain): the frame's slots F+184 and F+104, the fake frame's header and its shadow's poison *)
  paj_run_sh_x RUNP HS HJ2.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U247b, ?U271b, ?U32b in Hr;
        first [ lia
        | left; lia
        | right; right; right; exists 1, fpos; split; [left; reflexivity|];
          change (frame_addr ly 1 fpos) with FF; change (fs_frame_bytes 1) with 128;
          first [ left; unfold in_zr; cbn [fst snd]; lia
          | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hin'. }
  (* the size refusal: n >> 26 <> 0 goes to 0x85014; refuted by the contract's n < 2^26 *)
  assert (E11b : ew Eb 11 = Z_to_bv 64 n) by (rewrite OLDb, OLDa, (EE 11%nat 11%bv eq_refl), H11 by lia; reflexivity).
  psrr_branch_pi_x RUNP BR HS.
  { exfalso. rewrite branch_ne_U, U_SAlu, (U_atom Eb 11 n E11b), !U_SLit in Hc by lia. cbn [zalu_raw] in Hc.
    change (Z.land (zcanon 26) 63) with 26 in Hc. rewrite Z.shiftr_div_pow2, Z.div_small in Hc by lia.
    vm_compute in Hc. discriminate Hc. }
  (* the fake frame and its shadow become read-only (the token run keeps its windows off the shadow span);
     the runtime's GOT and uar regions are dropped *)
  pro_keep HS [0; 1; 2; 3; 4]%nat.
  pro_ro HS 0%nat. pro_ro HS 1%nat.
  pose proof pro_vals as (PV60 & PV61 & PV62 & PV63 & PV64 & PV65 & PV66 & PV69 & PV70 & PVO19 & PVO22 & PVO23 &
    PVO0 & PVO6 & PVO30 & PVLF).
  assert (RGv : rg_client fr_RG = 0xa2560 /\ rg_client_broken fr_RG = 0x5d8d60 /\ rg_send_max fr_RG = 0x5d8dc0 /\
    rg_gone fr_RG = 0x5d8de0 /\ rg_send_dead fr_RG = 0x5d8e00 /\ rg_send_eintr fr_RG = 0x5d8e20 /\
    rg_s fr_RG = 0x5d8e60 /\ rg_nout fr_RG = 0x5d8e40 /\ rg_nsrc fr_RG = 0x5d8d20 /\ rg_src fr_RG = 0x5d8d40)
    by (vm_compute; repeat split; reflexivity).
  destruct RGv as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9 & RG10).
  assert (HNFDv : AG_NFD = 0x5d8da0) by reflexivity.
  (* the seven global stores' regions (pr_g 60 .. 66), all in G_fr *)
  pro_addg HS HEIb 60%nat 32 4 HG_client.
  pro_addg HS HEIb 61%nat (-2024) 1 HG_cbroken.
  pro_addg HS HEIb 62%nat (-1964) 4 HG_nfd.
  pro_addg HS HEIb 63%nat (-1936) 8 HG_smax.
  pro_addg HS HEIb 64%nat (-1916) 1 HG_gone.
  pro_addg HS HEIb 65%nat (-1892) 1 HG_sdead.
  pro_addg HS HEIb 66%nat (-1868) 1 HG_seintr.
  pro_addf HS HEIb 340%nat. pro_addf HS HEIb 341%nat. pro_addf HS HEIb 342%nat. pro_addf HS HEIb 343%nat.
  pro_addf HS HEIb 344%nat. pro_addf HS HEIb 345%nat. pro_addf HS HEIb 346%nat.
  (* the journal, from here at G_fr (the donor's journal is ajournal_gx at G = [], lifted) *)
  pose proof (ajournal_gx_G_mono_x segs B PST ARx [] G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a Ha => False_ind _ (inG_nil a Ha)) (proj2 (ajournal_gx_nil_x segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJ2)) as HJ3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (SHOKb : sh_ok segs Bx [] Eb (mrestrict (w_H W) (ms_mem msx))) by (unfold sh_ok; constructor) end.
  pose proof (pro_Fb_x (LFCX ly S W regs mem md p n pl M) HB) as (HFlo & HFsp & HFsp2 & _ & _ & _).
  change (lf_F (LFCX ly S W regs mem md p n pl M)) with F in HFlo, HFsp, HFsp2. unfold CEIL8 in HFlo.
  cbn [c_regs] in HFsp, HFsp2.
  (* run 3: the frame's slots and the seven globals, to `jal op_add` *)
  paj_run_to_tok_x RUNTOX HS HJ3 SHOKb Bspan AF_fr_op_add.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U247b, ?U271b, ?U32b in Hr;
        pro_imgh HEIb Hr;
        first [ clear - Hr; lia
        | left; split; [left; clear - Hr WS HFsp HFsp2; lia | clear - Hr; lia]
        | right; left; first [ apply HG_client; clear - Hr RG1; lia | apply HG_cbroken; clear - Hr RG2; lia
                             | apply HG_nfd; clear - Hr HNFDv; lia | apply HG_smax; clear - Hr RG3; lia
                             | apply HG_gone; clear - Hr RG4; lia | apply HG_sdead; clear - Hr RG5; lia
                             | apply HG_seintr; clear - Hr RG6; lia ]
        ]
      | ]).
    destruct Hin'. }
  (* ---- the bytes the prologue keeps from the entry to the call (pro_mid's KEEP) ---- *)
  pose proof HK as (HK1 & HK2 & HK3 & _ & _ & _).
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    rename Hx into HFr3;
    assert (K3 : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= FF \/ FF + 128 <= a) ->
        (a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a) -> pro_gst_out a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem2 a) end.
  { clear - HFr3 HFr0 HEIb U2b U34b U39b U512 U513 U241b U247b U271b U32b HFlo HFsp.
    intros a Ha Hff Hsh Hgst. pose proof Hgst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & Hg7). clear Hgst.
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    rewrite (proj1 (pro_kept_frame _ _ W _ _ a HFr3 ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEIb Ha HFlo HFsp))).
    pose proof (proj1 (pro_kept_frame _ _ W _ _ a HFr0 ltac:(clear - Ha D1; lia)
      ltac:(pro_nwr_k HEIb Ha HFlo HFsp))) as K2.
    cbn [ms_mem mkst] in K2. exact K2. }
  assert (K1 : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { clear - HFr HEI Usp UF HFlo HFsp.
    intros a Ha. pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    exact (proj1 (pro_kept_frame _ _ W _ _ a HFr ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEI Ha HFlo HFsp))). }
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    assert (KEEP : forall a, pro_ks (LFCX ly S W regs mem md p n pl M) a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem a) end.
  { pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    intros a [Ha | (p0 & n0 & Hp & Hpa)]; [|cbn [c_ly c_S] in Hp].
    - pose proof (G_obj_rng a (G_keep_obj a Ha)) as Hr. pose proof (G_keep_gst a Ha) as Hg.
      destruct (HG a (HGOBJ a (G_keep_obj a Ha))) as (Him & Hno & _).
      rewrite (K3 a ltac:(clear - Hr D1; lia) ltac:(clear - Hr HFimg; lia) ltac:(clear - Hr HF4096; lia) Hg),
        (HK3 a Him Hno (G_obj_err a (G_keep_obj a Ha))).
      exact (K1 a ltac:(clear - Hr D1; lia)).
    - destruct (al0_blocks _ _ _ _ _ p0 n0 HARa Hp) as (_ & H4096 & Hbc & Happ & _).
      assert (Hp2 : In (p0, n0) (ablocks B ly S2)) by (rewrite Eab; exact Hp).
      pose proof (sep_block_frame_x segs B ARx LAWS ly S2 [] W mem2 md2 p0 n0 1 fpos HARb Hp2 Hfin2) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      change (frame_addr ly 1 fpos) with FF in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      assert (Hsh : a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a).
      { destruct (Z_lt_le_dec a (2147450880 + FF / 8)) as [Hl | Hl]; [left; exact Hl | right].
        destruct (Z_lt_le_dec a (2147450880 + FF / 8 + 16)) as [Hl2 | Hl2]; [|exact Hl2].
        exfalso. exact (fshadow_not_app FF 16 p0 (req_size n0) a ltac:(clear - HF4096; lia)
          ltac:(clear - HFceil D1; lia) Happ ltac:(clear - Hl Hl2; lia) Hpa). }
      rewrite (K3 a ltac:(clear - H4096 Hbc Hpa; lia) ltac:(clear - Hd Hpa; lia) Hsh
        (pro_blk_gst_x _ _ _ _ _ p0 n0 a HARa Hp Hpa)).
      replace a with (p0 + (a - p0)) by ring.
      rewrite (HK2 p0 n0 (a - p0) Hp ltac:(clear - Hpa; lia) (fun Hf => Hf)).
      exact (K1 (p0 + (a - p0)) ltac:(clear - H4096 Hbc Hpa D1; lia)). }
  (* ---- op_add's entry ---- *)
  pmkst HS.
  pro_rgn HS 0%nat RQ7. pro_rgn HS 1%nat RQ6. pro_rgn HS 2%nat RQ5. pro_rgn HS 3%nat RQ4.
  pro_rgn HS 4%nat RQ3. pro_rgn HS 5%nat RQ2. pro_rgn HS 6%nat RQ1. pro_rgn HS 7%nat RQS.
  pro_rgn HS 8%nat RQF. pro_rgn HS 10%nat RQV. pro_rgn HS 11%nat RQP.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
  prreg HS (27%bv : bv 5) Q27.
  assert (EAb : forall r, (r < 32)%nat -> ew Eb r = getr regs (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. rewrite OLDb, OLDa by (clear - Hr; lia). apply EE. rewrite Z_to_bv_unsigned. symmetry.
    apply bv_wrap_small. change (bv_modulus 5) with 32. clear - Hr; lia. }
  assert (Hfrs2' : frames S2 = [(1, fpos)]) by (rewrite Hfrs2, Hfrs; reflexivity).
  exact (pro_at_call_x (LFCX ly S W regs mem md p n pl M) S2 0 fpos Eb _ _ _ HB HJ3 Eab Hfrs2' Hnev2 Hbb2 HMO2 HNP2 HEIb
    U2b U34b U39b U512 U513 (eq_trans (OLDb 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33a) EAb
    RQ7 RQ6 RQ5 RQ4 RQ3 RQ2 RQ1 RQS RQF RQV RQP Q1 Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q24 Q27 KEEP).
Qed.

(* ---- THE CHECK: B cut_x Section w's SEG_PRO (W_LLVMFuzzerTestOneInput_cut_x.v:621), restated in its text at
   cut_x's names (the forms B lib/B/W_LLVMFuzzerTestOneInput_top_x.v uses) and closed by `exact` from lf_seg_pro_x ---- *)
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IH := (INV_H_x B NP G_fr fr_FP PST ARx LSx RINV).
Lemma lf_seg_pro_x_check : forall cx Hp, BASEx cx Hp -> SRr segs (c_W cx) (lf_entry cx) (IH cx Hp 0).
Proof. exact lf_seg_pro_x. Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the prologue at a world relation R.  Up to op_add's entry the walk is the
   strict one (it starts the journal, takes the stack_malloc seat and the plain run, and moves no world), so
   lf_seg_pro_xR runs the strict text there, lifted by YA0nH.SRr_SRrG WLE_R, and lifts the journal at the call to R
   by ajournal_gx_xR_mono WLE_R.  From op_add's entry on, every text of Section prx that names the journal (AJ0 /
   AJi0 -> AJ0R / AJi0R), a cut_x carrier or the step relation is restated at R: SRr segs -> SRrG segs R, the run
   -> W_journal_x.v paj_run_to_x_xG, the op_add call -> its R contract OA_R (W_op_add.v oa_spec_g_xR: op_add can
   free, so its post journal is at R).  lf_seg_pro_xR concludes B cut_x Section wR's SEG_PRO_R.  The strict text
   above is unchanged. ---- *)
Section prxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
Hypothesis OA_R : W_op_add.oa_spec_g_xR (PI := PB_fr) B PST ARx R MT RP (BASE + AF_fr_op_add).
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (R := R) (PI := PB_fr).

(* R twin of ajournal_gx_rom_view0 *)
Lemma ajournal_gx_rom_view0R : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs)
    mem' md' k,
  AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  rom_out segs B G -> rom_view segs W mem -> rom_view segs W' mem'.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR Hrv.
  apply (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low G XO OUT STK sp0 FP ly S [] W mem md own ly' S' []
    W' mem' md' k HJ HR); [|exact Hrv].
  intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr].
Qed.
(* R twin of region_kept_stack_aj_x *)
Lemma region_kept_stack_aj_xR : forall E lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (Er : Z -> Prop)
    n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
  acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
  region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
    (K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
  pose proof asan_consts as (C1 & _).
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview segs). apply K1; lia.
  - intros _. apply (apresent_writable segs). apply Hpres. lia.
Qed.
(* R twin of oa_call_keep_x *)
Lemma oa_call_keep_xR : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  AJ0R G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
  forall a, in_img segs a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Him Hno He (HPST a Him) ltac:(apply fp_spares_closed; exact Hsk)).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* R twin of oa_call_keep_blk_x *)
Lemma oa_call_keep_blk_xR : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  AJ0R G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
  ~ inFP FP (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n j H0 H1 Hj Hfp).
  destruct (al0_blocks ly1 S1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
  apply (aview_gagree segs G' (w_H W0) m0 memS (p + j) HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  exact (blk_img0 ly1 S1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
(* R twin of oa_call_keep_hi_x *)
Lemma oa_call_keep_hi_xR : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  AJ0R G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx a Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (F1 a Ha Hno).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
(* R twin of ad_call_keep_frm_x *)
Lemma ad_call_keep_frm_xR : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k
    cid pos a,
  gx_ok segs B G' ->
  AJ0R G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k cid pos a HGok HJx Hin Hr Hnf Ha Hni.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hnf).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa. exact (Hni (proj1 (HGok a HGa))).
Qed.
(* R twin of pro_frame_wr_x *)
Lemma pro_frame_wr_xR : forall cx own ly3 S3 k (W : world segs) mem md,
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a.
Proof.
  intros cx own ly3 S3 k W mem md (_ & _ & (memS & HJi & _) & _) a Ha. rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply (apresent_writable segs). apply Hpres. lia.
Qed.
(* R twin of pro_fin_x *)
Lemma pro_fin_xR : forall cx (W : world segs) regs mem md ly3 S3 k m fpos,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  pro_fr cx (frame_addr ly3 1 fpos) (flag_addr ly3 1 fpos) W mem ->
  pro_regs cx (frame_addr ly3 1 fpos) regs ->
  amodel_at B ly3 S3 W mem m -> lm_k m = 0 -> ainput_at B cx ly3 S3 W mem -> rom_view segs W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx 0 m ly3 S3 -> NP S3 -> RINV cx 0 m ->
  YA0nH.SRrG segs R W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_pro_ret)) mem (seg_rom segs)) md)
    (INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] 0).
Proof.
  intros cx W regs mem md ly3 S3 k m fpos HB HJ HFR HRG HMOD Hk0 HIN HRV HSEP HLS HNP HRI.
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : YCfn.LLVMF_STK = 32768) by reflexivity.
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hn26 : 0 <= c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf_x in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  set (FF := frame_addr ly3 1 fpos) in *. set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds0 ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  destruct (al0_frames ly3 S3 W mem md 1 fpos HAR Hin1) as (HFFal & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1, HFFal.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  pose proof HFR as (HSV & H32 & H40 & H56 & H64 & H72 & H80 & H104 & H184 & HH0 & HH8 & HH16 & HFL & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R19 & R21 & R22 & R24 & R27 & R3 & R4).
  assert (HDIV : val_mem segs (arm W mem) 0x10320 8 DIV10)
    by (apply (rom_vmb_ok W mem _ _ _ HRV); vm_compute; reflexivity).
  assert (HWRF : forall a, sp0 - YCfn.LLVMF_STK <= a < sp0 -> writable_at segs (arm W mem) a)
    by (exact (pro_frame_wr_xR cx _ _ _ _ W mem md HJ)).
  assert (HWR : forall a, F + 48 <= a < F + 160 -> writable_at segs (arm W mem) a)
    by (intros a Ha; apply HWRF; unfold sp0 in *; lia).
  destruct (pro_entry2 W regs mem F R9 R27 ltac:(unfold CEIL8 in *; lia) ltac:(unfold sp0 in *; lia) HFal HDIV HWR)
    as [HS SHOK].
  remember (Eimg (Ereg regs pro2_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs pro2_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  assert (E24 : ew E 24 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E27 : ew E 27 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  clear HE.
  pose proof pro_vals as (PV60 & PV61 & PV62 & PV63 & PV64 & PV65 & PV66 & PV69 & PV70 & PVO19 & PVO22 & PVO23 &
    PVO0 & PVO6 & PVO30 & PVLF).
  assert (VI : forall j v, VAL (A_HI j) = v -> (A_HI j < A_LIM)%nat -> 0 <= v < 2 ^ 64 -> ew E (A_HI j) = Z_to_bv 64 v).
  { intros j v Hv Hj Hr. apply bv_eq. rewrite (HEI (A_HI j) ltac:(unfold A_HI, A_TEXT in *; lia)).
    rewrite unsigned_lit_small by exact Hr. exact Hv. }
  assert (Hgs : rg_s fr_RG = 0x5d8e60) by (vm_compute; reflexivity).
  assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s fr_RG))
    by (apply bv_eq; rewrite (HEI (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
        rewrite unsigned_lit_small by (rewrite Hgs; lia); rewrite PVO19; reflexivity).
  change (A_OBJ 19) with 260%nat in E260.
  (* every fact of the cut but the slots the set-up stores, for any memory that keeps the bytes outside them *)
  assert (Herr : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8)
    by (rewrite HEV; unfold TFIB_ERRNO_B, CEIL8; pose proof lt_ceil_lo; lia).
  assert (KEEPF : forall mf, (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 48 <= a < F + 56) -> ~ (F + 96 <= a < F + 104) ->
      ~ (F + 120 <= a < F + 160) -> abyte_kept W mem W mf a) ->
    amodel_at B ly3 S3 W mf m /\ ainput_at B cx ly3 S3 W mf /\ rom_view segs W mf /\ jt_rom W mf /\
    pro_fr cx FF (flag_addr ly3 1 fpos) W mf).
  { intros mf KO.
    assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mf a)
      by (intros a Ha; apply KO; unfold CEIL8 in *; lia).
    assert (HRVf : rom_view segs W mf) by exact (lt_rom_kept W W mem mf HRV KL).
    split; [exact (lt_amodel_kept_x B ARx LAWS ly3 S3 [] W mem md W mf m HAR HMOD (proj1 Herr) (proj2 Herr) KL)|].
    split; [exact (lt_ainput_kept_x B ARx LAWS cx ly3 S3 [] W mem md W mf HAR HIN (eq_sym HlenP) KL)|].
    split; [exact HRVf|]. split; [exact (lt_jt_kept W W mem mf (pro_jt W mem HRV) KL)|].
    assert (KH : forall a v, (forall x, a <= x < a + 8 -> abyte_kept W mem W mf x) -> sv8 W mem a v -> sv8 W mf a v)
      by (intros a v Hk Hv; exact (lt_sv8_kept W W mem mf a v Hk Hv)).
    split; [intros o r Hor; apply KH; [|exact (HSV o r Hor)]; intros x Hx;
            unfold saved_regs in Hor; cbn [In] in Hor;
            repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; apply KO; unfold sp0 in *; lia|]);
            destruct Hor|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H32]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H40]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H56]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H64]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H72]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H80]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H104]|].
    split; [apply KH; [intros x Hx; apply KO; unfold sp0 in *; lia | exact H184]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH0]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH8]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH16]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFL]|].
    split; [apply (akept_awr W mem W mf); [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFW]|].
    split; [apply (akept_garr8 W mem W mf); [intros x Hx; apply KL; cbn [length fake_shadow] in Hx;
            pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia
            | exact HSH]|].
    apply (akept_awr W mem W mf); [intros x Hx; apply KL;
      pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia | exact HSW]. }
  paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan AF_LLVM_head.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
        first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
    destruct Hin'. }
  clear HF.
  lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
    assert (KO1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 48 <= a < F + 56) -> ~ (F + 96 <= a < F + 104) ->
      ~ (F + 120 <= a < F + 160) -> abyte_kept W m1 W m2 a) end.
  { intros a Ha H1 H2 H3. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
    destruct Hin'. }
  clear HFr.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs pro2_extra pro_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  pro_rgn HS 0%nat HR48. pro_rgn HS 1%nat HR96. pro_rgn HS 2%nat HR120.
  pose proof (pro_sh_den E 27 260 SB (rg_s fr_RG) 0 E27 E260 ltac:(unfold SB; lia) ltac:(rewrite Hgs; lia)
    ltac:(rewrite Hgs; lia)) as D120.
  pose proof (pro_sh_den E 27 260 SB (rg_s fr_RG) 4 E27 E260 ltac:(unfold SB; lia) ltac:(rewrite Hgs; lia)
    ltac:(rewrite Hgs; lia)) as D152.
  rewrite Z.add_0_r in D120.
  pmkst HS.
  lazymatch goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
    apply (YA0nH.SRrG_ret segs R R_refl); exists rf, mf, df end.
  split; [reflexivity|].
  lazymatch type of KO1 with forall a, _ -> _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
    destruct (KEEPF m2 KO1) as (HMODf & HINf & HRVf & HJTf & HFRf) end.
  pose proof HFRf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFLf & _).
  split; [exact HJTf|].
  exists [(1, fpos)], ly3, S3, [], k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|].
  split.
  { apply (pro_aframe cx FF (flag_addr ly3 1 fpos) W _ HFRf).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 48 56 48 56 48 8 (SOff 260 0) (rg_s fr_RG) HR48 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E260, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(rewrite Hgs; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 104 96 104 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(unfold SB in *; cbn [Z.of_N Z.mul]; lia) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 120 8
        (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 260 0) (SLit 3))) (SB + rg_s fr_RG / 8) HR120 U9
        ltac:(cbn [In]; tauto) D120
        ltac:(rewrite Hgs; unfold SB; split; [vm_compute; discriminate | vm_compute; reflexivity])
        ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 128 8 (SOff 260 4) (rg_s fr_RG + 4) HR120 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E260, unsigned_lit_small by (rewrite Hgs; lia); reflexivity)
        ltac:(rewrite Hgs; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 136 8 (SLit DIV10) DIV10 HR120 U9
        ltac:(cbn [In]; tauto) eq_refl
        ltac:(unfold DIV10; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 152 8
        (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 260 4) (SLit 3))) (SB + (rg_s fr_RG + 4) / 8) HR120 U9
        ltac:(cbn [In]; tauto) D152
        ltac:(rewrite Hgs; unfold SB; split; [vm_compute; discriminate | vm_compute; reflexivity])
        ltac:(zside)).
    - exact (pro_frame_wr_xR cx _ _ _ _ W _ _ HJ).
    - lia.
    - lia. }
  split; [exact HFLf|].
  split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
  split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
  unfold lregs_H, lregs_common.
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite Q18; change 350%nat with (A_HI 70); apply VI; [exact PV70 | cbv; lia | unfold HI_G_SRC; lia]|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite Q26; change 349%nat with (A_HI 69); apply VI; [exact PV69 | cbv; lia | unfold HI_G_NOUT; lia]|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite Q25; reflexivity|].
  split; [rewrite (KR 21%bv ltac:(cbv; tauto)), Hk0, Z.sub_0_r; exact R21|].
  split; [rewrite (KR 22%bv ltac:(cbv; tauto)), Hk0, Z.add_0_r; exact R22|].
  split; [unfold OPS_MAX; lia|].
  rewrite Hk0. lia.
Qed.
(* R twin of pro_ff_eq_x *)
Lemma pro_ff_eq_xR : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k cid pos,
  AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.
(* R twin of pro_afn_pre_at_x *)
Lemma pro_afn_pre_at_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
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
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
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
      | unfold raZ in Hra40; lia | lia
      | rewrite (Znumtheory.Zmod_div_mod 8 16 sp0) by (try lia; exists 2; reflexivity); rewrite Hal16; reflexivity
      | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.
(* R twin of pro_mid_x *)
Lemma pro_mid_xR : forall cx regs mem md S2 k fpos,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) mem md k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 -> NP S2 ->
  pro_fr cx (frame_addr (c_ly cx) 1 fpos) (flag_addr (c_ly cx) 1 fpos) (c_W cx) mem ->
  getr regs 1 = w64 (BASE + A_pro_ret) -> pro_regs cx (frame_addr (c_ly cx) 1 fpos) regs ->
  pro_glob (c_W cx) mem ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) mem a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  YA0nH.SRrG segs R (c_W cx) (cfg_at segs (BASE + AF_fr_op_add) regs mem md) (INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] 0).
Proof.
  intros cx regs mem md S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HFR Hra HRG HGL KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & _ & _ & Hgi & Hrom & _).
  destruct Hgi as (HGP0 & HCL & (T & HRR) & (c0 & O & mx0 & cap & out & HAO) & (gn0 & HGN) & HLK & HWK & HTU &
    (lst & HLS0) & HLW).
  (* the room round: the pre's XCNT (its 22nd conjunct) at fr_gi's table T and g_out (cap, out), read off the same three
     cells (prx_cells), and HFH0 *)
  pose proof HPRE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HXC0 & _).
  destruct HXC0 as (Tx & cx0 & Ox & mxx & capx & outx & HRRx & HAOx & HXC).
  pose proof (proj1 HPREE) as HARe.
  destruct (prx_cells _ _ _ _ _ _ T c0 O mx0 cap out HARe HRR HAO) as (CT & CC & CO).
  destruct (prx_cells _ _ _ _ _ _ Tx cx0 Ox mxx capx outx HARe HRRx HAOx) as (CTx & CCx & COx).
  rewrite CT in CTx. rewrite CC in CCx. rewrite CO in COx.
  injection CTx as <-. injection CCx as <-. injection COx as <-. clear HRRx HAOx.
  change (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) with (input_blks cx) in HXC.
  assert (HFH0 : fr_hblks (c_W cx) (c_mem cx) = (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out).
  { unfold fr_hblks. cbv zeta. change tfibsegs with segs. rewrite CT, CO, CC. unfold aout_blks. reflexivity. }
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL8.
  pose proof (HFP_pro cx [] T c0 O mx0 cap out HB HRR HAO) as ((rest0 & HPERM0) & HFPT & HFPO).
  set (W := c_W cx) in *. set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
  assert (Hgs : rg_s fr_RG = 0x5d8e60) by (vm_compute; reflexivity).
  assert (Hgs' : rg_s fr_globals = 0x5d8e60) by (vm_compute; reflexivity).
  (* ---- kept from the entry to the call ---- *)
  assert (KG : forall a, inG G_keep a -> aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros a Ha; apply KEEP; left; exact Ha).
  assert (KBk : forall p n a, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> p <= a < p + req_size n ->
      aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros p0 n0 a Hp Ha; apply KEEP; right; exists p0, n0; split; [exact Hp | exact Ha]).
  assert (KGv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W mem) a n v).
  { intros a n0 v Hr Hv. apply (ad_vm_view W W (c_mem cx) mem); [|exact Hv].
    intros x Hx. exact (KG x (rng_cover a (Z.of_nat n0) G_keep Hr x Hx)). }
  assert (AW : forall a n, rng_inb a n G_fr_obj = true -> forall (W' : world segs) m', awr W' m' a n).
  { intros a n0 Hr W' m' i Hi. apply (G_obj_wr (a + i) (rng_cover a n0 G_fr_obj Hr (a + i) ltac:(lia))). }
  (* ---- the call's facts ---- *)
  assert (HCLc : forall i, (i < 4)%nat -> asrc_closed W mem (oa_HA i)).
  { intros i Hi. destruct (HCL i Hi) as [HZ _]. split.
    - apply (pro_garr8_view W W (c_mem cx) mem); [|exact HZ].
      intros x Hx. apply KG. rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply (rng_cover (rg_s fr_globals) (4 * ASRC) G_keep ltac:(vm_compute; reflexivity)).
      unfold oa_HA, ASRC in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->|[->| ->]]]; vm_compute; reflexivity. }
  assert (Hos : forall i, nth i [0; 0; 0; 0] 0 = 0) by (intros i; destruct i as [|[|[|[|[|i]]]]]; reflexivity).
  assert (HRRc : ra_rel B fr_RG (c_ly cx) S2 W mem T []).
  { destruct HRR as [(HT0 & _ & (E1 & E2 & E3 & E4 & E5 & E6)) | HAT].
    - left. split; [exact HT0|]. split; [reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E1]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E3]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E5] | apply AW; vm_compute; reflexivity].
    - right. pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _).
      apply (arelay_at_kept B fr_RG (c_ly cx) (c_S cx) W (c_mem cx) (c_ly cx) S2 W mem T [] HAT).
      + intros r Hr a Ha. split.
        * unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- apply KG. refine (rng_cover (rg_src fr_RG) 8 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_nsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_capsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply (KBk T ATABLE a HTin). change (req_size ATABLE) with 896. unfold ATABLE in Ha. lia.
        * intros _. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- refine (G_obj_wr a (rng_cover (rg_src fr_RG) 8 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_nsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_capsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- rewrite <- Eab2 in HTin.
             destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & _ & Hpr & _).
             apply (apresent_writable segs). apply (proj1 (Hpr a ltac:(change (req_size ATABLE) with 896;
               unfold ATABLE in Ha; lia))).
      + intros b Hb. rewrite Eab2. cbn [arelay_blks map concat app] in Hb. destruct Hb as [<- | []]. exact HTin. }
  assert (HLKc : alock_at fr_RG W mem false).
  { destruct HLK as (L1 & L2 & L3 & L4).
    split; [apply KGv; [vm_compute; reflexivity | exact L1]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L2]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L3] | apply AW; vm_compute; reflexivity]. }
  assert (HWKc : awake_at fr_RG W mem) by (apply KGv; [vm_compute; reflexivity | exact HWK]).
  assert (HRVc : rom_view segs W mem)
    by (eapply ajournal_gx_rom_view0R; first [exact Hsegs | exact LAWS | exact HJ | exact pro_rom_out_fr | exact Hrom]).
  (* ---- op_add's afn_pre, its room and its meter ---- *)
  pose proof HFR as (HSV & H32 & H40 & H56 & H64 & H72 & H80 & H104 & H184 & HH0 & HH8 & HH16 & HFLw & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R19 & R21 & R22 & R24 & R27 & R3 & R4).
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  destruct (pro_afn_pre_at_xR cx (c_ly cx) S2 fpos k W mem md regs OA_STK HB HJ HSV Hsp) as (ch & HPREc).
  { rewrite Hra. apply ret_ok_codeptr_v; [unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite Hra, unsigned_lit_small by (unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia).
    unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput. lia. }
  { exact R3. } { exact R4. } { exact R8. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK. lia. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK. lia. }
  destruct (LS_pro_oa cx [] S2 fpos HB Eab2 Hfrs2 Hnev2 Hbb2 HMO2) as (Hroom & Hmok).
  (* the entry's T: when the table exists it is a live block of the entry, above 4096 *)
  assert (HT4096 : T <> 0 -> 4096 <= T /\ In (T, ATABLE) (ablocks B (c_ly cx) (c_S cx))).
  { intros HT0. destruct HRR as [(HT0' & _) | HAT]; [contradiction|].
    pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _). split; [|exact HTin]. rewrite <- Eab2 in HTin.
    destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & H4096 & _). exact H4096. }
  (* ---- op_add, at its own G ---- *)
  assert (HGcov1 : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG pro_G a)
    by (intros a Ha; exact (pro_inG_rng pro_G (rg_s fr_globals) (4 * ASRC) a ltac:(cbn [In pro_G app RA_G];
          repeat (first [left; reflexivity | right])) Ha)).
  assert (HGcov2 : forall a, A_NFD <= a < A_NFD + 4 -> inG pro_G a)
    by (intros a Ha; exact (pro_inG_rng pro_G A_NFD 4 a ltac:(cbn [In pro_G app RA_G];
          repeat (first [left; reflexivity | right])) Ha)).
  assert (HGcov3 : forall a, inG (RA_G fr_globals) a -> inG pro_G a)
    by (intros a Ha; unfold pro_G; apply inG_app; right; exact Ha).
  destruct HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eapply (YA0nH.SRrG_bind segs R R_trans).
  { exact (OA_R pro_G G_oa_prog_x W (c_ly cx) S2 [] regs mem md ch [0; 0; 0; 0] 0 T []
      HPREc
      ltac:(rewrite Hsp; exact HFal) ltac:(rewrite Hfrs2; vm_compute; reflexivity) eq_refl
      ltac:(intros i _; rewrite Hos; lia)
      ltac:(intros i Hi; rewrite Hos; exact (oa_zero_vm _ _ _ 4 4 (proj1 (HCLc i Hi)) ltac:(lia)
              ltac:(unfold ASRC; cbn; lia)))
      ltac:(intros i Hi _; exact (HCLc i Hi))
      G3 ltac:(lia) HZS HGcov1 HGcov2 HGcov3 HRRc HLKc HWKc HRVc
      ltac:(intros _; split; [cbn; lia | intros []]) Hroom Hmok
      (* the room round: the room from the seat's NP (kr := 0), the counts from the entry's xcnt_ok (LS_cnt) *)
      0%nat (proj2 (RP_NP S2 _) HNP2) (LS_cnt cx T cap out S2 HXC Eab2)). }
  cbv beta. intros W3 c3 Hwle3
    (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & kk & -> & HJo & HP4 & HAPK & HOK & Hfrs4 & HRM4 & HSome).
  (* the room after op_add: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S4 0%nat) HRM4) as HNP4.
  (* oa_post_x's ghost list is [] (HP0 at the post's journal) *)
  hp0gR HJo.
  assert (Hof : oa_first [0; 0; 0; 0] = Some 0%nat) by reflexivity.
  rewrite Hof in HSome. cbv beta iota in HSome.
  destruct HSome as (q & T' & pj & HSRC & HNFD & HREL & HLK4 & HPERM & HMLE).
  cbn [app] in HREL. change (100 + 0) with 100 in HSRC, HREL. change (0 + 1) with 1 in HNFD.
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo) as HAR4.
  pose proof (proj1 G_oa_prog_x) as HGoa.
  assert (Hsk : ~ YI16.sink_open_fp (oa_FP [0; 0; 0; 0] T [])).
  { unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
    intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & _). lia. }
  (* the journal from the entry, through op_add (lifted from pro_G to G_fr) *)
  pose proof (ajournal_gx_G_mono_xR segs B PST ARx pro_G G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G_oa_fr HJo) as HJo'.
  assert (HFP1 : forall a, inFP (oa_FP [0; 0; 0; 0] T []) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B (c_ly cx) S2) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B (c_ly cx) S2) a).
  { intros a Ha. left. unfold oa_FP in Ha. rewrite Hof in Ha. unfold ra_FP in Ha.
    destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [destruct Ha as (r & [] & _)|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & HTin).
    split; [apply (HFPT HT0); change (req_size ATABLE) with 896; unfold ATABLE in *; lia|].
    exists T, ATABLE. split; [rewrite Eab2; exact HTin | change (req_size ATABLE) with 896; lia]. }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 [] W mem md k
     OA_STK (spZ regs) 0 [] (oa_FP [0; 0; 0; 0] T []) [] ly4 S4 [] W3 mem4 md4 kk HJ HJo'
     ltac:(rewrite Hsp; unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK; lia)
     ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP1) as HJ4.
  cbn [app] in HJ4.
  destruct (pro_ff_eq_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos HJo) as [EFF EFL]. fold FF in EFF.
  (* ---- what op_add keeps ---- *)
  assert (KP : forall a, inG G_pst a -> aview segs (w_H W3) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. pose proof (G_pst_obj a Ha) as Ho. destruct (HG a (HGOBJ a Ho)) as (Him & Hno & _).
    exact (oa_call_keep_xR pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo Hsk a Him
      (G_pst_oa a Ha) Hno (G_obj_err a Ho)). }
  assert (KPv : forall a n v, rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W3 mem4) a n v).
  { intros a n0 v Hr Hv. apply (ad_vm_view W W3 mem mem4); [|exact Hv].
    intros x Hx. exact (KP x (rng_cover a (Z.of_nat n0) G_pst Hr x Hx)). }
  assert (KGPv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true -> rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W3 mem4) a n v)
    by (intros a n0 v H1 H2 Hv; exact (KPv a n0 v H2 (KGv a n0 v H1 Hv))).
  assert (KS3 : forall i, (1 <= i < 4)%nat -> asrc_closed W3 mem4 (oa_HA i)).
  { intros i Hi. destruct (HCLc i ltac:(lia)) as [HZ _]. split.
    - apply (pro_garr8_view W W3 mem mem4); [|exact HZ]. intros x Hx.
      rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply HOK.
      + apply HGcov1. unfold oa_HA, ASRC in *. lia.
      + unfold oa_wr. rewrite Hof. intros [Hx1 | [Hx2 | Hx3]].
        * unfold oa_HA, ASRC in *. cbn [Z.of_nat] in Hx1. lia.
        * unfold oa_HA, ASRC, A_NFD in *. rewrite Hgs' in *. lia.
        * pose proof (pro_ra_g x Hx3). unfold oa_HA, ASRC in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[-> | ->]]; vm_compute; reflexivity. }
  (* the entry's blocks the call keeps: all but the relay's table, whose new entry relay_add writes *)
  assert (KBo : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) mem (p + j)).
  { intros p n j Hp Hne Hj. assert (Hp2 : In (p, n) (ablocks B (c_ly cx) S2)) by (rewrite Eab2; exact Hp).
    apply (oa_call_keep_blk_xR pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HGoa HJo p n j Hp2).
    - destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)).
      + right. right. exact Hp2.
      + right. exact Hp2.
    - exact Hj.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      pose proof (sep_blocks_x segs B ARx LAWS (c_ly cx) S2 [] W mem md p n T ATABLE HAR2 Hp2 HTin (Hne HT0)) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
      unfold ATABLE in *. lia. }
  (* the input block and the controller's buffer are not the relay's table (the entry's blocks are distinct) *)
  assert (ND0 : List.NoDup (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest0)).
  { pose proof HPREE as (HAR0 & _). exact (Permutation_NoDup HPERM0 (ad_nodup_x _ _ _ _ _ HAR0)). }
  assert (HinpT : forall p n, In (p, n) (input_blks cx) -> T <> 0 -> (p, n) <> (T, ATABLE)).
  { intros p n Hp HT0 Heq. rewrite Heq in Hp. apply (pro_nd_app _ _ _ (T, ATABLE) ND0 Hp).
    rewrite (proj2 (Z.eqb_neq T 0) HT0). apply in_or_app. left. left. reflexivity. }
  assert (HoutT : forall b, In b (aout_blks cap out) -> T <> 0 -> b <> (T, ATABLE)).
  { intros b Hb HT0 Heq. rewrite Heq in Hb. pose proof (pro_nd_appr _ _ _ ND0) as ND1.
    rewrite (proj2 (Z.eqb_neq T 0) HT0) in ND1. cbn [app] in ND1. inversion ND1 as [|x l Hx _]; subst.
    apply Hx. apply in_or_app. left. exact Hb. }
  assert (KBt : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) (c_mem cx) (p + j))
    by (intros p n j Hp Hne Hj; rewrite (KBo p n j Hp Hne Hj); exact (KBk p n (p + j) Hp ltac:(lia))).
  (* ---- the cut after op_add: the controller's stream ---- *)
  destruct (ERRL ly4 S4 [] W3 mem4 md4 HAR4) as ((v & Hv & Hvr) & Hvw).
  pose proof HAO as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 &
    A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26).
  assert (HAOp : aout_at B fr_RG ly4 S4 W3 mem4 (W_rep.CTL 3 0 0 0 v) O 0 (Z.of_nat (length O)) cap out).
  { split; [apply KPv; [vm_compute; reflexivity | exact G4]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A3]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A5]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A7]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G1]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G2]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G6]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G7]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [exact Hv|]. split; [exact Hvw|]. split; [exact Hvr|].
    split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|].
    destruct A26 as [A26 | (Hc & Hnc & Hio & junk & Hjl & Hjg)]; [left; exact A26|].
    right. split; [exact Hc|]. split; [exact Hnc|].
    assert (Hio2 : In (out, cap) (ablocks B ly4 S4)).
    { destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hio. }
    split; [exact Hio2|]. exists junk. split; [exact Hjl|].
    apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hjg].
    intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx.
    replace x with (out + (x - out)) by lia.
    apply (KBt out cap (x - out)); [exact Hio | intros HT0; apply (HoutT (out, cap));
      [unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)); left; reflexivity | exact HT0] |].
    pose proof (req_size_pos cap ltac:(lia)) as [_ Hrc]. lia. }
  (* the input *)
  assert (HINp : ainput_at B cx ly4 S4 W3 mem4).
  { split.
    - destruct Hin as [Hin | (Hn & Hpin)]; [left; exact Hin|]. right. split; [exact Hn|].
      destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hpin.
    - destruct Hin as [(Hn0 & _) | (Hn & Hpin)].
      + rewrite Hnl in Hn0. assert (Hpl : c_pl cx = []) by (apply length_zero_iff_nil; lia).
        rewrite Hpl. intros j Hj. cbn in Hj. lia.
      + apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hgarr].
        intros x Hx. rewrite length_map in Hx. rewrite <- Hnl in Hx. replace x with (c_p cx + (x - c_p cx)) by lia.
        apply (KBt (c_p cx) (c_n cx) (x - c_p cx)); [exact Hpin | intros HT0; apply (HinpT (c_p cx) (c_n cx));
          [unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); left; reflexivity | exact HT0] |].
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrc]. lia. }
  (* the model *)
  assert (HMOD4 : amodel_at B ly4 S4 W3 mem4 (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out)).
  { unfold amodel_at, pro_m. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [reflexivity|].
    split.
    { intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth aslot].
      - exact HSRC.
      - exact (KS3 1%nat ltac:(lia)).
      - exact (KS3 2%nat ltac:(lia)).
      - exact (KS3 3%nat ltac:(lia)).
      - lia. }
    split; [exact HREL|]. split; [exact HAOp|].
    split; [split; [apply KPv; [vm_compute; reflexivity | exact G5]
                  | split; [apply AW; vm_compute; reflexivity | left; reflexivity]]|].
    split; [exact HLK4|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HWK]|].
    split; [exact HNFD|]. split; [apply AW; vm_compute; reflexivity|]. split; [unfold OPS_MAX; lia|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HTU]|].
    split; [exists lst; apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HLS0]|].
    apply AW; vm_compute; reflexivity. }
  (* the frame and the fake frame *)
  assert (HIV : forall x, F <= x < 2 ^ 47 -> aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (oa_call_keep_hi_xR pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HGoa HJo x);
      [unfold CEIL8 in *; lia | rewrite Hsp; lia]. }
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof (frm_off_imgP_x B ARx LAWS IMGCx _ _ [] _ _ _ 1 fpos HAR2 Hin1) as HFimg.
  change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg. unfold off_img in HFimg.
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HAR2 Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (FRV : forall x, (FF <= x < FF + 128) \/ (SB + FF / 8 <= x < SB + FF / 8 + 16) ->
      aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx.
    assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold SB in *; lia).
    assert (Hni : ~ in_img segs x).
    { intros Hi. destruct Hx as [Hx | Hx].
      - exact (frm_img_x segs B ARx LAWS (c_ly cx) S2 [] W mem md 1 fpos x HAR2 Hin1
          ltac:(change (fs_frame_bytes 1) with 128; unfold FF in Hx; lia) Hi).
      - pose proof (pa_segs_low x Hi). unfold SB, kLowMemEnd in *. lia. }
    apply (ad_call_keep_frm_xR pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk 1 fpos x HGoa HJo Hin1);
      [| | exact Hx64 | exact Hni].
    - unfold frame_rng, in_zr, shadow_addr. rewrite <- SB_SHADOW_OFF. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. fold FF.
      destruct Hx as [Hx | Hx]; [left | right]; lia.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (al0_blocks _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & Happ & _).
      change (req_size ATABLE) with 896 in Happ.
      destruct Hx as [Hx | Hx].
      + pose proof (sep_block_frame_x segs B ARx LAWS (c_ly cx) S2 [] W mem md T ATABLE 1 fpos HAR2 HTin Hin1) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
        change (fs_frame_bytes 1) with 128 in Hd. fold FF in Hd. unfold ATABLE in *. lia.
      + apply (fshadow_not_app FF 16 T 896 x ltac:(lia) ltac:(lia) Happ); [unfold SB in Hx; lia | unfold ATABLE in *; lia]. }
  assert (Hin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4, Hfrs2; left; reflexivity).
  destruct (al0_frames ly4 S4 W3 mem4 md4 1 fpos HAR4 Hin4) as (_ & _ & HFp & HFs).
  rewrite EFF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFR4 : pro_fr cx FF (flag_addr (c_ly cx) 1 fpos) W3 mem4).
  { split.
    { intros o r Hor. apply (ad_vm_view W W3 mem mem4); [|exact (HSV o r Hor)].
      intros x Hx. apply HIV. unfold saved_regs in Hor. cbn [In] in Hor.
      repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; unfold sp0 in *; lia|]). destruct Hor. }
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H32]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H40]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H56]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H64]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H72]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H80]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H104]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H184]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH0]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH8]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH16]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HFLw]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split; [apply (pro_garr8_view W W3 mem mem4); [intros x Hx; apply FRV; right; cbn [length fake_shadow] in Hx; lia
            | exact HSH]|].
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers op_add keeps *)
  assert (HRG4 : pro_regs cx FF regs4).
  { split; [rewrite (pro_pres regs regs4 2%bv HP4 ltac:(pro_cs)); exact R2|].
    split; [rewrite (pro_pres regs regs4 8%bv HP4 ltac:(pro_cs)); exact R8|].
    split; [rewrite (pro_pres regs regs4 9%bv HP4 ltac:(pro_cs)); exact R9|].
    split; [rewrite (pro_pres regs regs4 19%bv HP4 ltac:(pro_cs)); exact R19|].
    split; [rewrite (pro_pres regs regs4 21%bv HP4 ltac:(pro_cs)); exact R21|].
    split; [rewrite (pro_pres regs regs4 22%bv HP4 ltac:(pro_cs)); exact R22|].
    split; [rewrite (pro_pres regs regs4 24%bv HP4 ltac:(pro_cs)); exact R24|].
    split; [rewrite (pro_pres regs regs4 27%bv HP4 ltac:(pro_cs)); exact R27|].
    split; [rewrite (pro_pres regs regs4 3%bv HP4 ltac:(pro_cs)); exact R3|].
    rewrite (pro_pres regs regs4 4%bv HP4 ltac:(pro_cs)); exact R4. }
  (* the blocks, as ablocks_sep lists them *)
  assert (Em : model_blks (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) =
    (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
  assert (ND4 : List.NoDup (ablocks B ly4 S4)) by exact (ad_nodup_x _ _ _ _ _ HAR4).
  assert (HSEP4 : ablocks_sep B fr_FP cx (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) ly4 S4).
  { split.
    - exists rest0. rewrite Em. rewrite Eab2 in HPERM. exact (pro_sep_perm _ _ _ _ _ T T' q HPERM0 HPERM).
    - intros b Hb. rewrite Em in Hb. destruct Hb as [<- | [<- | Hb]].
      + destruct HPERM as [(HT0 & HP) | (HT0 & -> & HP)].
        * left. intros Hb'. pose proof (Permutation_NoDup HP ND4) as ND. inversion ND as [|x l Hx ND']; subst.
          apply Hx. right. rewrite Eab2. exact Hb'.
        * right. intros a Ha. cbn [fst snd] in Ha. exact (HFPT HT0 a Ha).
      + left. intros Hb'. destruct HPERM as [(_ & HP) | (_ & _ & HP)]; pose proof (Permutation_NoDup HP ND4) as ND.
        * inversion ND as [|x l _ ND']; subst. inversion ND' as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
        * inversion ND as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
      + right. exact (HFPO b Hb). }
  (* the cut's two Variables, and the ROM view after op_add *)
  assert (Hc0ex : exists c1 mx1, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c1 O mx1
    (Z.of_nat (length O)) cap out) by (exists c0, mx0; exact HAO).
  assert (HPERM' : exists T0 rest, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly4 S4) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly4 S4) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx)))))
    by (exists T, rest0; split; [exact HPERM0|]; split; [exact HXC|]; split; [exact HFH0|];
        rewrite <- Eab2; exact HPERM).
  pose proof (LS_pro cx [] q T' pj (W_rep.CTL 3 0 0 0 v) O cap out S2 fpos ly4 S4 HB Hc0ex eq_refl eq_refl eq_refl
    eq_refl Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HMLE HPERM') as HLS4.
  pose proof (RI_pro cx [] q T' pj (W_rep.CTL 3 0 0 0 v) O cap out HB Hc0ex eq_refl eq_refl eq_refl eq_refl) as HRI4.
  assert (HRV4 : rom_view segs W3 mem4)
    by (eapply ajournal_gx_rom_view0R;
        first [exact Hsegs | exact LAWS | exact HJo | exact (proj1 (proj2 (proj2 G_oa_prog_x))) | exact HRVc]).
  (* the loop's set-up *)
  rewrite Hra. rewrite <- EFF in HFR4, HRG4. rewrite <- EFL in HFR4.
  exact (pro_fin_xR cx W3 regs4 mem4 md4 ly4 S4 (k + kk) _ fpos HB HJ4 HFR4 HRG4 HMOD4 eq_refl HINp HRV4 HSEP4
    HLS4 HNP4 HRI4).
Qed.
(* R twin of pro_at_call_x *)
Lemma pro_at_call_xR : forall cx S2 k fpos E regs4 m4 md4,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) m4 md4 k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 -> NP S2 ->
  img_env VAL A_LIM E ->
  bv_unsigned (ew E 2) = spZ (c_regs cx) -> bv_unsigned (ew E 34) = lf_F cx ->
  bv_unsigned (ew E 39) = frame_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 512) = flag_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 513) = SB + frame_addr (c_ly cx) 1 fpos / 8 -> ew E 33 = Z_to_bv 64 SB ->
  (forall r, (r < 32)%nat -> ew E r = getr (c_regs cx) (Z_to_bv 5 (Z.of_nat r))) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 346 (-1868) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 345 (-1892) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 344 (-1916) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 343 (-1936) 8 8 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 342 (-1964) 4 4 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 341 (-2024) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 340 32 4 4 3) ->
  region_ok segs E (arm (c_W cx) m4) pc_sh -> region_ok segs E (arm (c_W cx) m4) pc_ff ->
  region_ok segs E (arm (c_W cx) m4) pc_save -> region_ok segs E (arm (c_W cx) m4) pc_F ->
  getr regs4 1 = Z_to_bv 64 (BASE + A_pro_ret) -> getr regs4 2 = ew E 34 -> getr regs4 3 = ew E 3 ->
  getr regs4 4 = ew E 4 -> getr regs4 8 = ew E 2 -> getr regs4 9 = ew E 34 ->
  getr regs4 19 = Z_to_bv 64 (bv_unsigned (ew E 39) + 32) ->
  getr regs4 21 = ew E 11 -> getr regs4 22 = ew E 10 -> getr regs4 24 = ew E 513 -> getr regs4 27 = ew E 33 ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) m4 a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  YA0nH.SRrG segs R (c_W cx) (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + AF_fr_op_add)) m4 (seg_rom segs)) md4)
    (INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] 0).
Proof.
  intros cx S2 k fpos E regs4 m4 md4 HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HEI U2 U34 U39 U512 U513 E33 EA
    RG7 RG6 RG5 RG4 RG3 RG2 RG1 RSH RFF RSV RF Q1 Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q24 Q27 KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & _).
  pose proof HPREE as (_ & _ & _ & Hgp & Htp & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof lt_ceil_lo as HCL8.
  pose proof (pro_Fb_x cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  destruct (al0_frames _ _ _ _ _ 1 fpos HAR Hin1) as (_ & _ & HFp & HFs).
  fold FF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (ER : forall (r : nat) (b : bv 5), (r < 32)%nat -> Z.of_nat r = bv_unsigned b -> ew E r = getr (c_regs cx) b).
  { intros r b Hr Hb. rewrite (EA r Hr). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hb.
    apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  (* the frame and the fake frame *)
  assert (HFR : pro_fr cx FF (flag_addr (c_ly cx) 1 fpos) (c_W cx) m4).
  { unfold pro_fr. cbv zeta. fold F.
    split.
    { apply (pro_saved_of_region E _ _ _ _ _ _ _ (c_regs cx) RSV U2 EA).
      unfold saved_regs.
      repeat (apply Forall_cons; [cbn [fst snd In]; repeat (first [left; reflexivity | right]) |]).
      apply Forall_nil. }
    assert (FS : forall off (nv : nat) v, In (YP09.mkChunk off (CVal 8 (SOff nv 0))) (YP09.r_chunks pc_F) ->
        bv_unsigned (ew E nv) = v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (F + off) v).
    { intros off nv v Hc Hv Hr. unfold sv8.
      refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 34 F _ 32 192 32 192 off 8 (SOff nv 0) v RF U34 Hc _ Hr
        ltac:(cbn; lia)) eq_refl eq_refl).
      cbn [sv_denot]. rewrite Hv, Z.add_0_r. reflexivity. }
    split; [apply (FS 32 340%nat); [cbn; tauto | pro_rwimg HEI 340%nat; reflexivity | unfold HI_G_CLIENT; lia]|].
    split; [apply (FS 40 345%nat); [cbn; tauto | pro_rwimg HEI 345%nat; reflexivity | unfold HI_G_SDEAD; lia]|].
    split; [apply (FS 56 346%nat); [cbn; tauto | pro_rwimg HEI 346%nat; reflexivity | unfold HI_G_SEINTR; lia]|].
    split; [apply (FS 64 344%nat); [cbn; tauto | pro_rwimg HEI 344%nat; reflexivity | unfold HI_G_GONE; lia]|].
    split; [apply (FS 72 343%nat); [cbn; tauto | pro_rwimg HEI 343%nat; reflexivity | unfold HI_G_SMAX; lia]|].
    split; [apply (FS 80 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 104 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 184 39%nat); [cbn; tauto | exact U39 | lia]|].
    assert (FH : forall off e v, In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks pc_ff) ->
        sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (FF + off) v).
    { intros off e v Hc Hv Hr. unfold sv8.
      exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 off 8 e v RFF U39 Hc Hv Hr
        ltac:(cbn; lia)) eq_refl eq_refl). }
    split; [rewrite <- (Z.add_0_r FF); apply (FH 0 (SLit 1102416563)); [cbn; tauto | reflexivity | lia]|].
    split; [apply (FH 8 (SOff 263 0)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 263%nat; reflexivity|].
    split; [apply (FH 16 (SOff 240 8388)); [cbn; tauto | | unfold YCfn.A_LLVMF; lia];
            cbn [sv_denot]; pro_rwimg HEI 240%nat; reflexivity|].
    split; [apply (FH 120 (SOff 512 0)); [cbn; tauto | | ];
            [cbn [sv_denot]; rewrite U512, Z.add_0_r; reflexivity
            | destruct (FFL _ _ [] _ _ _ 1 fpos HAR Hin1) as (_ & _ & _ & (HFL4096 & _ & HFLc)); lia]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split.
    { apply (pro_shadow_garr8 E _ 513 _ _ 0 16 0 0 RSH U513).
      intros j Hj. do 16 (destruct j as [|j]; [cbn; repeat (first [left; reflexivity | right]) |]). lia. }
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers *)
  assert (HRG : pro_regs cx FF regs4).
  { unfold pro_regs, w64. fold F.
    split; [rewrite Q2, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q8, (ER 2%nat 2%bv ltac:(lia) eq_refl); reflexivity|].
    split; [rewrite Q9, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q19, U39; reflexivity|].
    split; [rewrite Q21, (ER 11%nat 11%bv ltac:(lia) eq_refl), H11; reflexivity|].
    split; [rewrite Q22, (ER 10%nat 10%bv ltac:(lia) eq_refl), H10; reflexivity|].
    split; [rewrite Q24, <- U513, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q27; exact E33|].
    split; [rewrite Q3, (ER 3%nat 3%bv ltac:(lia) eq_refl), Hgp; reflexivity|].
    rewrite Q4, (ER 4%nat 4%bv ltac:(lia) eq_refl), Htp; reflexivity. }
  (* the globals *)
  assert (GV : forall n off w (sz : N) v a, region_ok segs E (arm (c_W cx) m4) (pc_g n off w sz v) ->
      (A_TEXT <= n < A_LIM)%nat -> VAL n + off = a -> N.to_nat sz = Z.to_nat w -> 0 <= v < 2 ^ (8 * Z.of_N sz) ->
      (Z.of_N sz <= 8) -> val_mem segs (arm (c_W cx) m4) a (Z.to_nat w) v).
  { intros n0 off w sz v a HR Hn Ha Hw Hv Hs.
    refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ n0 (VAL n0) _ off (off + w) off (off + w) off sz
      (SLit v) v HR (HEI n0 Hn) ltac:(cbn; tauto) _ Hv Hs) Ha Hw).
    reflexivity. }
  assert (HGL : pro_glob (c_W cx) m4).
  { unfold pro_glob.
    split; [exact (GV 340%nat 32 4 4%N 3 (rg_client fr_RG) RG1 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 341%nat (-2024) 1 1%N 0 (rg_client_broken fr_RG) RG2 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 342%nat (-1964) 4 4%N 0 AG_NFD RG3 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 343%nat (-1936) 8 8%N 0 (rg_send_max fr_RG) RG4 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 344%nat (-1916) 1 1%N 0 (rg_gone fr_RG) RG5 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 345%nat (-1892) 1 1%N 0 (rg_send_dead fr_RG) RG6 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    exact (GV 346%nat (-1868) 1 1%N 0 (rg_send_eintr fr_RG) RG7 ltac:(unfold A_TEXT, A_LIM; lia)
      ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* the return address *)
  assert (Hra : getr regs4 1 = w64 (BASE + A_pro_ret)) by (rewrite Q1; reflexivity).
  exact (pro_mid_xR cx regs4 m4 md4 S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HMO2 HNP2 HFR Hra HRG HGL KEEP).
Qed.
(* R twin of lf_seg_pro_x: B cut_x Section wR's SEG_PRO_R *)
Theorem lf_seg_pro_xR : forall cx Hp, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  YA0nH.SRrG segs R (c_W cx) (lf_entry cx) (INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp 0).
Proof.
  pose proof R_refl as _. pose proof R_trans as _. pose proof WLE_R as _.
  intros [ly S W regs mem md p n pl M] Hp HB.
  (* the strict walk up to op_add's entry (the start, the stack_malloc seat and the plain run take the strict journal,
     the walk moves no world before the call); there its journal is lifted to R and pro_at_call_xR takes over *)
  apply (YA0nH.SRrG_bind segs R R_trans _ _ (fun W' c' => YA0nH.SRrG segs R W' c'
      (INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R (LFCX ly S W regs mem md p n pl M) Hp 0)));
    [apply (YA0nH.SRr_SRrG segs R WLE_R) | intros W' c' _ HQ; exact HQ].
  (* the entry's ghost list is empty (HP0 on the pre's ARx): the walk runs at [] *)
  pose proof HB as (_ & HPRE_). hp0a (proj1 (proj1 HPRE_)). clear HPRE_.
  pose proof HB as (HAI & HPRE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & Hroom & Hnp & Hgi & Hrom & Hrod & Hsink & Hfd & Hsrt & Hmeta & Hmo & Hstkr & Hhb & _).
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_M lf_entry] in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL8.
  assert (Rn : 0 <= n < 2 ^ 26) by (destruct Hin as [(-> & _) | (Hn & _)]; lia).
  destruct (pro_entry_x W ly S regs mem md [] n HPRE H11 Rn) as [HS SHOK].
  (* the journal at G = [] (W1Verify's template: ajournal_gx_nil_x of ajournal_x_init) *)
  pose proof (proj2 (ajournal_gx_nil_x segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (ajournal_x_init segs B PST ARx LLVMF_STK (lf_FP fr_FP (LFCX ly S W regs mem md p n pl M)) ly S [] W regs mem md [] HPRE)) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  remember (Eimg (Ereg regs (pro_extra regs))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n0 r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  set (F := pro_F regs) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (HAE : env_agree 32 (Ereg regs (pro_extra regs)) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  unfold cfg_at. change (w64 YCfn.A_LLVMF) with (Z_to_bv 64 (BASE + A_pro)).
  (* run 1: the frame, the saved registers, the fake-stack test; stops at __asan_stack_malloc_1 (0x84478) *)
  paj_run_tok_x RUN0 HS HJ SHOK Bspan.
  { apply awr_ok_x_of0. intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?UF in Hr;
        first [ lia | left; lia ] | ]).
    destruct Hin'. }
  (* the call to __asan_stack_malloc_1 (128): the fake frame FF; the journal at G = [] is the plain ajournal_x *)
  apply ajournal_gx_nil_x in HJ.
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  rewrite (palf_sm1 B TLF).
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
      eapply (aj_stack_malloc_pres_at_x segs B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 1 ASM1 ltac:(lia)
        W rg mm LLVMF_STK (spZ regs) _ ly S [] W mem md [] ly S [] _ 0 (F - spZ regs) _ HJ) end.
    - unfold spZ at 1. rewrite R2, UF. lia.
    - destruct HFv as [HFe | HFe]; rewrite HFe;
        [replace (spZ regs - 320 - spZ regs) with ((-20) * 16) by lia | replace (spZ regs - 336 - spZ regs) with ((-21) * 16) by lia];
        apply Z_mod_mult.
    - lia.
    - rewrite WS, Hes. lia.
    - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Hfrs. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPg & Hsf).
  (* the room round: the seat is a set_fs of the entry's state, so NP holds there (NPF) *)
  assert (HNP2 : NP S2) by (destruct Hsf as (fs & ->); exact (NPF _ fs Hnp)).
  (* KF-COUNT F2: and it costs nothing at the meter (MO_FR), LS_pro_oa's / LS_pro's premise *)
  assert (HMO2 : mo_le MT S S2 0) by (destruct Hsf as (fs & ->); exact (MO_FR S fs)).
  set (FF := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
  pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
  destruct (al0_const _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
  destruct (al0_const _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
  rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
  pose proof (palf_uar_img B TLF) as HuR.
  jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply region_kept_stack_aj_x; [exact HK | exact HJ2 | exact UF | lia | lia | lia | cbn; lia | cbn; lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 30)));
        [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kg1) | exact (val_mem_of_rdword segs _ _ _ _ Kg2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 30) (VAL (A_OBJ 30)) 8 SHADOW_OFF);
        [exact (HEI (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kc1) | exact (val_mem_of_rdword segs _ _ _ _ Kc2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 6) (VAL (A_OBJ 6)) 8 (as_uar_cell B));
        [exact (HEI (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kgu1) | exact (val_mem_of_rdword segs _ _ _ _ Kgu2) | lia].
    - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
        [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 segs _ _ _ _ Ku1) | exact (val_mem_of_rd32 segs _ _ _ _ Ku2) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (HAEa : env_agree 32 (Ereg regs (pro_extra regs)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
  clear HEa.
  prreg HS (10%bv : bv 5) RF.
  (* seat the fake frame: FF in atom 39 (a0), its flag FL in 512, the frame's shadow SB + FF / 8 in 513 *)
  assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds0 _ _ _ _ _ 1 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
  destruct (al0_frames _ _ _ _ _ 1 fpos HARb Hfin2) as (HFal2 & HFapp & HFpres & HFSpres).
  destruct (FFL _ _ [] _ _ _ 1 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  fold FF FL in HFal2, HFapp, HFpres, HFSpres, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
  assert (RF' : ew Ea 39 = Z_to_bv 64 FF) by (rewrite <- RF, Ha0; reflexivity).
  assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
  assert (U2a : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
  assert (U34a : bv_unsigned (ew Ea 34) = F) by (rewrite OLDa by lia; exact UF).
  assert (U32a : bv_unsigned (ew Ea 32) = as_uar_cell B) by (rewrite OLDa, E32 by lia; apply unsigned_lit_small; lia).
  assert (U241 : bv_unsigned (ew Ea 241) = VAL (A_OBJ 0)) by exact (HEIa (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U247 : bv_unsigned (ew Ea 247) = VAL (A_OBJ 6)) by exact (HEIa (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U271 : bv_unsigned (ew Ea 271) = VAL (A_OBJ 30)) by exact (HEIa (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (HFF8 : FF / 8 = 4 * (FF / 32)).
  { pose proof (Z.div_mod FF 32 ltac:(lia)) as D. rewrite HFal2, Z.add_0_r in D. rewrite D at 1.
    replace (32 * (FF / 32)) with (4 * (FF / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  assert (HFF8lo : 512 <= FF / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HFF8hi : FF / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 6 ltac:(lia)) as HguR.
  pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
  pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 6)). pose proof (pa_val_range (A_OBJ 30)).
  pose proof (ff_seat_ok Ea _ _ (w_H W) mem2 39 33 512 1 FF FL HS eq_refl ltac:(vm_compute; reflexivity)
    RF' E33a ltac:(lia) ltac:(lia) ltac:(right; reflexivity) HFal2 ltac:(lia) ltac:(change (fs_frame_bytes 1) with 128; lia)
    ltac:(lia)
    ltac:(change (fs_frame_bytes 1) with 128; intros a Ha; exact (proj1 (HFpres a Ha)))
    ltac:(change (fs_frame_bytes 1 / 8) with 16; intros i Hi; exact (proj1 (HFSpres i Hi)))
    ltac:(change (fs_frame_bytes 1) with 128; exact Hflag) ltac:(change (fs_frame_bytes 1) with 128; exact Hz)) as HS3.
  pose proof (pro_frm_img_hi_x _ _ _ _ _ 1 fpos HARb Hfin2) as HFimg. change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg.
  set (Eb := havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)]) in HS3.
  assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; subst Eb; apply YN3v.ew_havoc_old; exact Hm).
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
  assert (U512 : bv_unsigned (ew Eb 512) = FL).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. lia. }
  assert (U513 : bv_unsigned (ew Eb 513) = SB + FF / 8).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. unfold SB. lia. }
  assert (U39b : bv_unsigned (ew Eb 39) = FF) by (rewrite OLDb, RF' by lia; apply unsigned_lit_small; lia).
  assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact U2a).
  assert (U34b : bv_unsigned (ew Eb 34) = F) by (rewrite OLDb by lia; exact U34a).
  assert (U32b : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb by lia; exact U32a).
  assert (U241b : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U241).
  assert (U247b : bv_unsigned (ew Eb 247) = VAL (A_OBJ 6)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U247).
  assert (U271b : bv_unsigned (ew Eb 271) = VAL (A_OBJ 30)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U271).
  match type of HS3 with ?A1 -> ?A2 -> _ => assert (HD1 : A1); [|assert (HD2 : A2); [|specialize (HS3 HD1 HD2)]] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_fregion, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1) with 128. rewrite U39b, U2b, U34b, U241b, U247b, U271b, U32b.
    unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_sregion, ff_fregion, fshadow_region, fframe_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1 / 8) with 16. change (fs_frame_bytes 1) with 128.
    rewrite U513, U39b, U2b, U34b, U241b, U247b, U271b, U32b.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd8a. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as Hd8b.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as Hd8c.
    unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  clear HS. rename HS3 into HS. norm_ss HS.
  (* run 2 (plain): the frame's slots F+184 and F+104, the fake frame's header and its shadow's poison *)
  paj_run_sh_x RUNP HS HJ2.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U247b, ?U271b, ?U32b in Hr;
        first [ lia
        | left; lia
        | right; right; right; exists 1, fpos; split; [left; reflexivity|];
          change (frame_addr ly 1 fpos) with FF; change (fs_frame_bytes 1) with 128;
          first [ left; unfold in_zr; cbn [fst snd]; lia
          | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hin'. }
  (* the size refusal: n >> 26 <> 0 goes to 0x85014; refuted by the contract's n < 2^26 *)
  assert (E11b : ew Eb 11 = Z_to_bv 64 n) by (rewrite OLDb, OLDa, (EE 11%nat 11%bv eq_refl), H11 by lia; reflexivity).
  psrr_branch_pi_x RUNP BR HS.
  { exfalso. rewrite branch_ne_U, U_SAlu, (U_atom Eb 11 n E11b), !U_SLit in Hc by lia. cbn [zalu_raw] in Hc.
    change (Z.land (zcanon 26) 63) with 26 in Hc. rewrite Z.shiftr_div_pow2, Z.div_small in Hc by lia.
    vm_compute in Hc. discriminate Hc. }
  (* the fake frame and its shadow become read-only (the token run keeps its windows off the shadow span);
     the runtime's GOT and uar regions are dropped *)
  pro_keep HS [0; 1; 2; 3; 4]%nat.
  pro_ro HS 0%nat. pro_ro HS 1%nat.
  pose proof pro_vals as (PV60 & PV61 & PV62 & PV63 & PV64 & PV65 & PV66 & PV69 & PV70 & PVO19 & PVO22 & PVO23 &
    PVO0 & PVO6 & PVO30 & PVLF).
  assert (RGv : rg_client fr_RG = 0xa2560 /\ rg_client_broken fr_RG = 0x5d8d60 /\ rg_send_max fr_RG = 0x5d8dc0 /\
    rg_gone fr_RG = 0x5d8de0 /\ rg_send_dead fr_RG = 0x5d8e00 /\ rg_send_eintr fr_RG = 0x5d8e20 /\
    rg_s fr_RG = 0x5d8e60 /\ rg_nout fr_RG = 0x5d8e40 /\ rg_nsrc fr_RG = 0x5d8d20 /\ rg_src fr_RG = 0x5d8d40)
    by (vm_compute; repeat split; reflexivity).
  destruct RGv as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9 & RG10).
  assert (HNFDv : AG_NFD = 0x5d8da0) by reflexivity.
  (* the seven global stores' regions (pr_g 60 .. 66), all in G_fr *)
  pro_addg HS HEIb 60%nat 32 4 HG_client.
  pro_addg HS HEIb 61%nat (-2024) 1 HG_cbroken.
  pro_addg HS HEIb 62%nat (-1964) 4 HG_nfd.
  pro_addg HS HEIb 63%nat (-1936) 8 HG_smax.
  pro_addg HS HEIb 64%nat (-1916) 1 HG_gone.
  pro_addg HS HEIb 65%nat (-1892) 1 HG_sdead.
  pro_addg HS HEIb 66%nat (-1868) 1 HG_seintr.
  pro_addf HS HEIb 340%nat. pro_addf HS HEIb 341%nat. pro_addf HS HEIb 342%nat. pro_addf HS HEIb 343%nat.
  pro_addf HS HEIb 344%nat. pro_addf HS HEIb 345%nat. pro_addf HS HEIb 346%nat.
  (* the journal, from here at G_fr (the donor's journal is ajournal_gx at G = [], lifted) *)
  pose proof (ajournal_gx_G_mono_x segs B PST ARx [] G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a Ha => False_ind _ (inG_nil a Ha)) (proj2 (ajournal_gx_nil_x segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJ2)) as HJ3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (SHOKb : sh_ok segs Bx [] Eb (mrestrict (w_H W) (ms_mem msx))) by (unfold sh_ok; constructor) end.
  pose proof (pro_Fb_x (LFCX ly S W regs mem md p n pl M) HB) as (HFlo & HFsp & HFsp2 & _ & _ & _).
  change (lf_F (LFCX ly S W regs mem md p n pl M)) with F in HFlo, HFsp, HFsp2. unfold CEIL8 in HFlo.
  cbn [c_regs] in HFsp, HFsp2.
  (* run 3: the frame's slots and the seven globals, to `jal op_add` *)
  paj_run_to_tok_x RUNTOX HS HJ3 SHOKb Bspan AF_fr_op_add.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U247b, ?U271b, ?U32b in Hr;
        pro_imgh HEIb Hr;
        first [ clear - Hr; lia
        | left; split; [left; clear - Hr WS HFsp HFsp2; lia | clear - Hr; lia]
        | right; left; first [ apply HG_client; clear - Hr RG1; lia | apply HG_cbroken; clear - Hr RG2; lia
                             | apply HG_nfd; clear - Hr HNFDv; lia | apply HG_smax; clear - Hr RG3; lia
                             | apply HG_gone; clear - Hr RG4; lia | apply HG_sdead; clear - Hr RG5; lia
                             | apply HG_seintr; clear - Hr RG6; lia ]
        ]
      | ]).
    destruct Hin'. }
  (* ---- the bytes the prologue keeps from the entry to the call (pro_mid's KEEP) ---- *)
  pose proof HK as (HK1 & HK2 & HK3 & _ & _ & _).
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    rename Hx into HFr3;
    assert (K3 : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= FF \/ FF + 128 <= a) ->
        (a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a) -> pro_gst_out a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem2 a) end.
  { clear - HFr3 HFr0 HEIb U2b U34b U39b U512 U513 U241b U247b U271b U32b HFlo HFsp.
    intros a Ha Hff Hsh Hgst. pose proof Hgst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & Hg7). clear Hgst.
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    rewrite (proj1 (pro_kept_frame _ _ W _ _ a HFr3 ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEIb Ha HFlo HFsp))).
    pose proof (proj1 (pro_kept_frame _ _ W _ _ a HFr0 ltac:(clear - Ha D1; lia)
      ltac:(pro_nwr_k HEIb Ha HFlo HFsp))) as K2.
    cbn [ms_mem mkst] in K2. exact K2. }
  assert (K1 : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { clear - HFr HEI Usp UF HFlo HFsp.
    intros a Ha. pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    exact (proj1 (pro_kept_frame _ _ W _ _ a HFr ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEI Ha HFlo HFsp))). }
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    assert (KEEP : forall a, pro_ks (LFCX ly S W regs mem md p n pl M) a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem a) end.
  { pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    intros a [Ha | (p0 & n0 & Hp & Hpa)]; [|cbn [c_ly c_S] in Hp].
    - pose proof (G_obj_rng a (G_keep_obj a Ha)) as Hr. pose proof (G_keep_gst a Ha) as Hg.
      destruct (HG a (HGOBJ a (G_keep_obj a Ha))) as (Him & Hno & _).
      rewrite (K3 a ltac:(clear - Hr D1; lia) ltac:(clear - Hr HFimg; lia) ltac:(clear - Hr HF4096; lia) Hg),
        (HK3 a Him Hno (G_obj_err a (G_keep_obj a Ha))).
      exact (K1 a ltac:(clear - Hr D1; lia)).
    - destruct (al0_blocks _ _ _ _ _ p0 n0 HARa Hp) as (_ & H4096 & Hbc & Happ & _).
      assert (Hp2 : In (p0, n0) (ablocks B ly S2)) by (rewrite Eab; exact Hp).
      pose proof (sep_block_frame_x segs B ARx LAWS ly S2 [] W mem2 md2 p0 n0 1 fpos HARb Hp2 Hfin2) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      change (frame_addr ly 1 fpos) with FF in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      assert (Hsh : a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a).
      { destruct (Z_lt_le_dec a (2147450880 + FF / 8)) as [Hl | Hl]; [left; exact Hl | right].
        destruct (Z_lt_le_dec a (2147450880 + FF / 8 + 16)) as [Hl2 | Hl2]; [|exact Hl2].
        exfalso. exact (fshadow_not_app FF 16 p0 (req_size n0) a ltac:(clear - HF4096; lia)
          ltac:(clear - HFceil D1; lia) Happ ltac:(clear - Hl Hl2; lia) Hpa). }
      rewrite (K3 a ltac:(clear - H4096 Hbc Hpa; lia) ltac:(clear - Hd Hpa; lia) Hsh
        (pro_blk_gst_x _ _ _ _ _ p0 n0 a HARa Hp Hpa)).
      replace a with (p0 + (a - p0)) by ring.
      rewrite (HK2 p0 n0 (a - p0) Hp ltac:(clear - Hpa; lia) (fun Hf => Hf)).
      exact (K1 (p0 + (a - p0)) ltac:(clear - H4096 Hbc Hpa D1; lia)). }
  (* ---- op_add's entry ---- *)
  pmkst HS.
  pro_rgn HS 0%nat RQ7. pro_rgn HS 1%nat RQ6. pro_rgn HS 2%nat RQ5. pro_rgn HS 3%nat RQ4.
  pro_rgn HS 4%nat RQ3. pro_rgn HS 5%nat RQ2. pro_rgn HS 6%nat RQ1. pro_rgn HS 7%nat RQS.
  pro_rgn HS 8%nat RQF. pro_rgn HS 10%nat RQV. pro_rgn HS 11%nat RQP.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
  prreg HS (27%bv : bv 5) Q27.
  assert (EAb : forall r, (r < 32)%nat -> ew Eb r = getr regs (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. rewrite OLDb, OLDa by (clear - Hr; lia). apply EE. rewrite Z_to_bv_unsigned. symmetry.
    apply bv_wrap_small. change (bv_modulus 5) with 32. clear - Hr; lia. }
  assert (Hfrs2' : frames S2 = [(1, fpos)]) by (rewrite Hfrs2, Hfrs; reflexivity).
  apply SRr_ret.
  exact (pro_at_call_xR (LFCX ly S W regs mem md p n pl M) S2 0 fpos Eb _ _ _ HB
    (ajournal_gx_xR_mono segs B PST ARx (@wle segs) R WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) Eab Hfrs2' Hnev2 Hbb2 HMO2 HNP2 HEIb
    U2b U34b U39b U512 U513 (eq_trans (OLDb 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33a) EAb
    RQ7 RQ6 RQ5 RQ4 RQ3 RQ2 RQ1 RQS RQF RQV RQP Q1 Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q24 Q27 KEEP).
Qed.
End prxR.

End prx.
