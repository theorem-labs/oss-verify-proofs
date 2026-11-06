(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEG_LATCH of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput
   (lib/A/W_LLVMFuzzerTestOneInput_cut.v), in the form of that file's worked dispatch lf_seg_jt and of the
   internal call sites of lib/A/W_check_shape_event.v.  It walks 0x84490-0x844b0: the call to check_bounded
   (fuzz_reply.c:740) and the loop test `ops < 512 && in.n` (fuzz_reply.c:685), from the cut point K to the
   loop head H of operation t + 1, or to the shutdown block X. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------
   The transport kit.  check_bounded's only store is `sd ra,8(sp)` into its own 16-byte frame, so the
   caller's state is kept at every byte outside [sp - 16, sp); that window lies above alloc_ceiling + 8
   (the frame F of LLVMFuzzerTestOneInput is 32768 - 351 bytes above ly_stk_lo >= alloc_ceiling), while
   every byte the cut invariant reads outside the caller's own frame -- the globals, the relay's table,
   the harness's sources, the heap blocks and their 8-byte alignment slack, the input and the fake frame
   with its shadow -- lies below it.  These lemmas turn "kept below alloc_ceiling + 8" into the `akept`
   footprints that lib/A/W_rep.v's frame lemmas take. *)
Section kit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Definition CEIL8 : Z := alloc_ceiling + 8.
Definition lt_fp_low (fp : list (Z * Z)) : Prop := Forall (fun r => 0 <= fst r /\ snd r <= CEIL8) fp.
Lemma lt_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
(* a bound on a range of fuzz_reply.asan's globals, or on errno from the premises *)
Ltac lt_low :=
  cbn [fst snd gfp]; unfold CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lt_ceil_lo; lia.

Lemma lt_fp_low_nil : lt_fp_low []. Proof. constructor. Qed.
Lemma lt_fp_low_cons : forall r fp, 0 <= fst r -> snd r <= CEIL8 -> lt_fp_low fp -> lt_fp_low (r :: fp).
Proof. intros r fp H1 H2 H3. constructor; [split; assumption | exact H3]. Qed.
Lemma lt_fp_low_app : forall f1 f2, lt_fp_low f1 -> lt_fp_low f2 -> lt_fp_low (f1 ++ f2).
Proof. intros f1 f2 H1 H2. apply Forall_app. split; assumption. Qed.
Lemma lt_fp_low_forall : forall fp, lt_fp_low fp <-> (forall r, In r fp -> 0 <= fst r /\ snd r <= CEIL8).
Proof. intros fp. unfold lt_fp_low. apply Forall_forall. Qed.
Lemma lt_fp_low_sub : forall f1 f2, lt_fp_low f2 -> (forall r, In r f1 -> In r f2) -> lt_fp_low f1.
Proof. intros f1 f2 H Hs. rewrite lt_fp_low_forall in *. intros r Hr. exact (H r (Hs r Hr)). Qed.
Lemma lt_akept_of_low : forall (W : world segs) mem (W' : world segs) mem' fp,
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) -> lt_fp_low fp -> akept W mem W' mem' fp.
Proof.
  intros W mem W' mem' fp HK Hl r Hr a Ha. rewrite lt_fp_low_forall in Hl.
  destruct (Hl r Hr) as [H1 H2]. apply HK. lia.
Qed.

(* a live block: its bytes, and the 7 bytes of alignment slack a key's text may carry past them *)
Lemma lt_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma lt_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma lt_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma lt_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, lt_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma lt_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.

(* ---- struct list ---- *)
Lemma lt_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= CEIL8 ->
  lt_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lt_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (lt_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; lia|]. apply lt_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
    cbn [gfp fst snd]. rewrite lt_bzs_len, length_app, lt_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
Lemma lt_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= CEIL8 ->
  lt_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (lt_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (lt_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (lt_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (lt_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
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

(* ---- one source_t of the relay's table ---- *)
Lemma lt_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  lt_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : lt_fp_low (map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (lt_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lt_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
      cbn [gfp snd]. rewrite lt_bzs_len, length_app. unfold CEIL8 in *. lia.
    + apply lt_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lt_bzs_len, lt_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold CEIL8. pose proof lt_ceil_lo. lia. }
        destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan's globals ---- *)
Lemma lt_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_globals ly S W mem G es ->
  lt_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (lt_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : lt_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lt_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
Lemma lt_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  lt_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply lt_fp_low_cons; [lt_low | lt_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | cbn; unfold CEIL8 in *; lia | apply lt_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
End kit.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.

(* ------------------------------------------------------------------------------------------------
   check_bounded's contract, with the one conjunct this call site needs that this base's lib/A/W_contract.v
   cb_spec does not carry: the caller's memory is kept at every byte outside check_bounded's own 16-byte
   frame (a working branch 817ce9dd54a adds it to aleafx_post and proves it in pb_check_bounded).
   check_bounded (0x85304) stores exactly once, `sd ra,8(sp)`, and its only call site in the image is
   0x84490, this latch. *)
Section cbk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Variable B : asyms.
Definition cbk_post (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal_gx segs B [] 0 [] CB_STK (spZ regs) [] ly S W mem md [] ly S W' mem' md' 0 /\
    aregs_preserved regs regs' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CB_STK <= a < spZ regs) -> abyte_kept W mem W' mem' a).
Definition cbk_spec (pc : Z) : Prop :=
  forall (W : world segs) ly S regs mem md ch n P N,
  afn_pre segs B CB_STK ly S W regs mem md ch ->
  - 2 ^ 31 <= n < 2 ^ 31 ->
  val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nsrc) 4 (n mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) mem) (VAL A_g_src) 8 P -> 0 <= P < 2 ^ 64 ->
  (0 < n -> In (P, N) (ablocks B ly S) /\ 56 * n <= req_size N) ->
  (forall j, 0 <= j < n -> cb_entry_ok W mem P j) ->
  SRr segs W (cfg_at segs pc regs mem md) (cbk_post ly S W regs mem md).
End cbk.

Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* check_bounded's contract: cb_spec with the kept conjunct above.  A Section hypothesis until this base's
   W_contract.v aleafx_post carries the kept clause of a working branch 817ce9dd54a; with it, cbk_spec is
   pb_check_bounded's post minus two conjuncts. *)
Hypothesis W1_check_bounded : cbk_spec B (BASE + AF_fr_check_bounded).
(* errno's place: an instance fact, as _cut's errno_law is.  The instance's api_env (Reusable/YCbq.v:809,
   carried as pal_env by the allocator instance PALib, W_kit.v:367) gives 0 <= as_errno B and
   as_errno B + 4 <= kLowMemEnd = 0x7fff8000 < CEIL8. *)
Hypothesis ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8.


(* ---- the window: check_bounded's frame is between the cut's low bytes and the caller's frame ---- *)
Lemma lt_ceil_hi : CEIL8 < 2 ^ 64.
Proof. unfold CEIL8. pose proof asan_consts as (C1 & _). lia. Qed.
Lemma lt_keep_lo : forall (W W' : world segs) mem mem' F,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F - 16 <= a < F) -> abyte_kept W mem W' mem' a) ->
  CEIL8 <= F - 16 -> forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a.
Proof. intros W W' mem mem' F HK HF a Ha. pose proof lt_ceil_hi. apply HK; lia. Qed.
Lemma lt_keep_hi : forall (W W' : world segs) mem mem' F,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F - 16 <= a < F) -> abyte_kept W mem W' mem' a) ->
  0 <= F -> forall a, F <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a.
Proof. intros W W' mem mem' F HK HF a Ha. apply HK; lia. Qed.
Lemma lt_akept_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= CEIL8 ->
  akept W mem W' mem' [(lo, hi)].
Proof.
  intros W W' mem mem' lo hi HK H1 H2. apply lt_akept_of_low; [exact HK|].
  apply lt_fp_low_cons; [cbn; lia | cbn; lia | apply lt_fp_low_nil].
Qed.
Lemma lt_akept_of_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= CEIL8 ->
  forall x, lo <= x < hi -> abyte_kept W mem W' mem' x.
Proof. intros W W' mem mem' lo hi HK H1 H2 x Hx. apply HK. lia. Qed.

(* ---- the model ---- *)
Lemma lt_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= CEIL8)
      by (unfold fr_RG, CEIL8; cbn; unfold ASRC; pose proof lt_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (lt_asrc B LAWS ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lt_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (lt_arelay B LAWS ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (lt_aout B LAWS ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
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

(* ---- the frame, the fake frame and its shadow ---- *)
Lemma lt_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
Lemma lt_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - 16 <= a < lf_F cx) -> abyte_kept W mem W' mem' a) ->
  CEIL8 <= lf_F cx - 16 -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= CEIL8 ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    HK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof lt_ceil_hi as HC64. pose proof lt_ceil_lo as HCL.
  assert (HFpos : 0 <= lf_F cx) by lia.
  assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a)
    by (apply (lt_keep_lo W W' mem mem' (lf_F cx) HK HLO)).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (apply (lt_keep_hi W W' mem mem' (lf_F cx) HK HFpos)).
  split.
  { intros o r Hin. apply (lt_sv8_kept W W' mem mem'); [|exact (A1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  split.
  { apply (akept_awr W mem); [|exact A2]. intros x Hx. apply KH. lia. }
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A3]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A4]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A5]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A6]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A7]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A8]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A9]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A10]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact A11]|].
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B1]|].
    split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B2]|].
    split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B3]|].
    split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B4]|].
    split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B5]|].
    split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B6]|].
    apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B7]. }
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A13]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A14]|].
  split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact A16]|].
  split.
  { apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros x Hx.
    unfold fake_shadow in Hx. cbn [length] in Hx. apply KL. lia. }
  apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact (proj2 A17)].
Qed.

(* ---- the input block, the read-only image, the jump table ---- *)
Lemma lt_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (lt_blk B LAWS ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold CEIL8. lia.
Qed.
Lemma lt_rom_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  rom_view segs W' mem'.
Proof.
  intros W W' mem mem' HR KEEP a Ha. rewrite <- (HR a Ha).
  assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
  pose proof (pa_segs_low a Hin) as Hlow. pose proof lt_ceil_lo.
  exact (proj1 (KEEP a ltac:(unfold CEIL8, kLowMemEnd in *; lia))).
Qed.
Lemma lt_jt_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJ KEEP i Hi. apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. apply KEEP. unfold fr_jtab, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia.
Qed.

(* ---- reading one entry's used and cap out of the relay's table (check_bounded's pre) ---- *)
Definition RE0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].
Lemma lt_nth_bzs : forall l n, (n < length l)%nat -> nth n (bzs l) 0 = bz (nth n l (Z_to_bv 8 0)).
Proof.
  intros l n Hn. unfold bzs.
  rewrite (nth_indep (map bz l) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hn).
  apply map_nth.
Qed.
Lemma lt_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, H1, H2, !Mem.length_le4, !Mem.length_le8. reflexivity.
Qed.
Lemma lt_nth_concat : forall (es : list rentry) j k d,
  (forall e, In e es -> length (entry_bytes e) = 56%nat) -> (j < length es)%nat -> (k < 56)%nat ->
  nth (56 * j + k) (concat (map entry_bytes es)) d = nth k (entry_bytes (nth j es RE0)) d.
Proof.
  induction es as [|e es IH]; intros j k d HL Hj Hk; [cbn in Hj; lia|].
  cbn [map concat]. destruct j as [|j].
  - cbn [nth]. rewrite Nat.mul_0_r, Nat.add_0_l.
    apply app_nth1. rewrite (HL e ltac:(left; reflexivity)). lia.
  - cbn [nth] in *. cbn [length] in Hj.
    rewrite app_nth2 by (rewrite (HL e ltac:(left; reflexivity)); lia).
    rewrite (HL e ltac:(left; reflexivity)).
    replace (56 * S j + k - 56)%nat with (56 * j + k)%nat by lia.
    apply IH; [intros x Hx; apply HL; right; exact Hx | lia | lia].
Qed.
Lemma lt_nth_used : forall e k d, (k < 8)%nat -> length (re_pad1 e) = 4%nat ->
  nth (24 + k) (entry_bytes e) d = nth k (Mem.le8 (Z_to_bv 64 (re_used e))) d.
Proof.
  intros e k d Hk Hp. unfold entry_bytes.
  rewrite app_nth2 by (rewrite Mem.length_le4; lia). rewrite Mem.length_le4.
  rewrite app_nth2 by (rewrite Mem.length_le4; lia). rewrite Mem.length_le4.
  rewrite app_nth2 by (rewrite Mem.length_le4; lia). rewrite Mem.length_le4.
  rewrite app_nth2 by (rewrite Hp; lia). rewrite Hp.
  rewrite app_nth2 by (rewrite Mem.length_le8; lia). rewrite Mem.length_le8.
  replace (24 + k - 4 - 4 - 4 - 4 - 8)%nat with k by lia.
  apply app_nth1. rewrite Mem.length_le8. lia.
Qed.
Lemma lt_nth_cap : forall e k d, (k < 8)%nat -> length (re_pad1 e) = 4%nat ->
  nth (32 + k) (entry_bytes e) d = nth k (Mem.le8 (Z_to_bv 64 (re_cap e))) d.
Proof.
  intros e k d Hk Hp. unfold entry_bytes.
  rewrite app_nth2 by (rewrite Mem.length_le4; lia). rewrite Mem.length_le4.
  rewrite app_nth2 by (rewrite Mem.length_le4; lia). rewrite Mem.length_le4.
  rewrite app_nth2 by (rewrite Mem.length_le4; lia). rewrite Mem.length_le4.
  rewrite app_nth2 by (rewrite Hp; lia). rewrite Hp.
  rewrite app_nth2 by (rewrite Mem.length_le8; lia). rewrite Mem.length_le8.
  rewrite app_nth2 by (rewrite Mem.length_le8; lia). rewrite Mem.length_le8.
  replace (32 + k - 4 - 4 - 4 - 4 - 8 - 8)%nat with k by lia.
  apply app_nth1. rewrite Mem.length_le8. lia.
Qed.
(* the byte a little-endian 8-byte field holds, as val_mem reads it *)
Lemma lt_le8_byte : forall v k, (k < 8)%nat -> 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (bz (nth k (Mem.le8 (Z_to_bv 64 v)) (Z_to_bv 8 0))) = Z_to_bv 8 (YO0f.le_byte v 8 k).
Proof.
  intros v k Hk Hv. unfold Mem.le8, word_to_le_bytes.
  rewrite unsigned_lit_small by lia.
  pose proof (YN01.nth_error_Z_to_le_bytes 8 v k Hk) as HN.
  rewrite (nth_error_nth _ _ (Z_to_bv 8 0) HN).
  unfold bz. rewrite Z_to_bv_bv_unsigned.
  rewrite (le_byte_small v 8 k ltac:(cbn; lia) Hk). reflexivity.
Qed.
Lemma lt_cb_entry : forall ly S (W : world segs) mem md G es j,
  AR segs B ly S W mem md -> arelay_at B fr_globals ly S W mem G es ->
  0 <= j < Z.of_nat (length es) -> cb_entry_ok W mem G j.
Proof.
  intros ly S W mem md G es j HAR HR Hj.
  pose proof HR as (_ & _ & _ & _ & _ & _ & Hlen16 & Hblk & (tail & T1 & T2 & T3) & HF & _).
  set (jn := Z.to_nat j).
  assert (Hjn : (jn < length es)%nat) by (unfold jn; lia).
  set (e := nth jn es RE0).
  assert (He : In e es) by (unfold e; apply nth_In; exact Hjn).
  rewrite Forall_forall in HF.
  pose proof (HF e He) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HLall : forall x, In x es -> length (entry_bytes x) = 56%nat).
  { intros x Hx. destruct (HF x Hx) as (_ & _ & P1 & P2 & _). exact (lt_eb_len x P1 P2). }
  assert (Hcl : length (concat (map entry_bytes es)) = (56 * length es)%nat).
  { clear - HLall. induction es as [|x xs IH]; [reflexivity|].
    cbn [map concat]. rewrite length_app, (HLall x ltac:(left; reflexivity)).
    rewrite IH by (intros y Hy; apply HLall; right; exact Hy). cbn [length]. lia. }
  (* the byte at index 56*jn + o of the table is the entry's byte at o *)
  assert (HB : forall o, (o < 56)%nat ->
    mbyte segs (arm W mem) (G + Z.of_nat (56 * jn + o)) =
    Some (Z_to_bv 8 (bz (nth o (entry_bytes e) (Z_to_bv 8 0))))).
  { intros o Ho.
    assert (Hlt : (56 * jn + o < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
    { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
    rewrite (garr8_mbyte segs (arm W mem) G _ (56 * jn + o)%nat T3 Hlt). f_equal.
    rewrite (lt_nth_bzs _ (56 * jn + o)%nat ltac:(rewrite length_app, Hcl; lia)).
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite (lt_nth_concat es jn o (Z_to_bv 8 0) HLall Hjn Ho). reflexivity. }
  exists (re_used e), (re_cap e).
  assert (Hused : val_mem segs (arm W mem) (G + 56 * j + 24) 8 (re_used e)).
  { intros k Hk.
    replace (G + 56 * j + 24 + Z.of_nat k) with (G + Z.of_nat (56 * jn + (24 + k))) by (unfold jn; lia).
    rewrite (HB (24 + k)%nat ltac:(lia)). f_equal.
    rewrite (lt_nth_used e k (Z_to_bv 8 0) Hk K3).
    apply lt_le8_byte; [exact Hk | lia]. }
  assert (Hcap : val_mem segs (arm W mem) (G + 56 * j + 32) 8 (re_cap e)).
  { intros k Hk.
    replace (G + 56 * j + 32 + Z.of_nat k) with (G + Z.of_nat (56 * jn + (32 + k))) by (unfold jn; lia).
    rewrite (HB (32 + k)%nat ltac:(lia)). f_equal.
    rewrite (lt_nth_cap e k (Z_to_bv 8 0) Hk K3).
    apply lt_le8_byte; [exact Hk | lia]. }
  split; [exact Hused|]. split; [exact Hcap|].
  assert (Hle : re_used e <= re_cap e).
  { destruct K10 as [(Hc & _ & Hu) | (Hc & _ & Hjk & _)]; lia. }
  unfold APARTIAL in K8. split; [lia|]. split; [lia | lia].
Qed.

(* ---- the walk ---- *)
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
Definition lt_extra : list word := map (Z_to_bv 64) [SB].
Definition lt_facts : facts := mkFacts [ (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_lt : sstate := mkSS AF_LLVM_latch sr_atoms [] None lt_facts.
Definition LBx : sv := SOff 32 0.
(* a run over read-only regions leaves the memory as it was (_cut's jt_mem) *)
Ltac lt_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
(* a concrete register is callee-saved / one of a list *)
Ltac lt_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac lt_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* every register but ra, which the jal sets *)
Definition lt_kept : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* 0x84490 `jal check_bounded`: the state the run starts from needs no region (the call reads no memory). *)
Lemma lt_entry : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (Ereg regs lt_extra)) ss_lt
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_latch)) mem (seg_rom segs)))
  /\ sh_ok segs LBx [] (Eimg (Ereg regs lt_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs lt_extra)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold ss_lt. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [lt_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.

(* check_bounded's afn_pre at sp = F: the donor's afn_pre_at (Reusable/YCbq.v:1811), whose achain is the entry's
   chain with this frame pushed (the prologue saved ra at sp0-8 and s0 at sp0-16, `saved_regs` of aframe_at:
   achain_push, YCbq.v:297) -- or, when sp0 is within 16 bytes of the stack top, the empty chain. *)
Lemma lt_afn_pre_at : forall cx full ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx full ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
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
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
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
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
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
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* a callee-saved register across the call *)
Lemma lt_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* 0x84494, back from check_bounded: `ld s5,144(s1)` reads in.n from the frame slot F+144 *)
Definition AF_LLVM_latch4 : Z := AF_LLVM_latch + 4.
Definition lt2_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 32 0))].
Definition lt2_facts : facts := mkFacts [ (32%nat, mkAF 0 (2 ^ 26) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_lt2 : sstate := mkSS AF_LLVM_latch4 sr_atoms [lt2_region] None lt2_facts.
Definition LBx2 : sv := SOff 33 0.
Definition lt2_extra (nl : Z) : list word := map (Z_to_bv 64) [nl; SB].
Lemma lt_entry2 : forall (W : world segs) regs mem F nl,
  getr regs 9 = w64 F -> 0 <= F -> F + 152 <= 2 ^ 64 ->
  0 <= nl <= 2 ^ 26 -> val_mem segs (mrestrict (w_H W) mem) (F + 144) 8 nl ->
  st_ok_pi segs VAL (Eimg (Ereg regs (lt2_extra nl))) ss_lt2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_latch4)) mem (seg_rom segs)))
  /\ sh_ok segs LBx2 [] (Eimg (Ereg regs (lt2_extra nl))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F nl H9 HF0 HF1 Hnl HV. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (lt2_extra nl))).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E32 : ew E 32 = Z_to_bv 64 nl)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (VB9 : base_val E (Some 9%nat) = F) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  split.
  - unfold ss_lt2. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, lt2_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite VB9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ F 144 8 (SOff 32 0) nl);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact HV].
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [lt2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, E33, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.

(* 0x84494-0x844b0 after the call: `ld s5,144(s1); li t1,4; li t2,1; li a0,510; bltu a0,s11 -> X;
   addiw s11,s11,1; bnez s5 -> H; j X`.  The walk writes t1, t2, a0, s5 and s11 only. *)
Definition lt2_kept : list (bv 5) :=
  [1; 2; 3; 4; 5; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 28; 29; 30; 31]%bv.
(* the callee-saved registers the next cut point names *)
Definition lt_saved : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26]%bv.
Lemma lt_fin_regs : forall (regs regs2 rf : bvmap 5 word),
  (forall r, In r lt2_kept -> getr rf r = getr regs2 r) ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> In r lt_kept -> getr regs2 r = getr regs r) ->
  forall r, In r lt_saved -> getr rf r = getr regs r.
Proof.
  intros regs regs2 rf K2 RR r Hr. unfold lt_saved in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [rewrite K2 by (unfold lt2_kept; lt_in); apply RR; [lt_cs | unfold lt_kept; lt_in] |]).
  destruct Hr.
Qed.
(* `addiw s11,s11,1` with s11 = t <= 510: the 32-bit sum, sign-extended, is t + 1 *)
Definition lt_envb (E : env) (b : Z) : env := {| ew := fun _ => Z_to_bv 64 b; ed := ed E |}.
Lemma lt_addiw_U : forall E t, ew E 27 = Z_to_bv 64 t -> 0 <= t <= 510 ->
  U E (SAluw ALU_ADD (SOff 27 0) (SLit 1)) = t + 1.
Proof.
  intros E t H27 Ht.
  assert (Hd : U E (SAluw ALU_ADD (SOff 27 0) (SLit 1)) = U (lt_envb E t) (SAluw ALU_ADD (SOff 27 0) (SLit 1)))
    by (unfold U; cbn [sv_denot]; rewrite H27; reflexivity).
  rewrite Hd. clear Hd H27.
  assert (K : forallb (fun t => U (lt_envb E t) (SAluw ALU_ADD (SOff 27 0) (SLit 1)) =? t + 1)
      (map Z.of_nat (seq 0 511)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. apply Z.eqb_eq. apply K. apply in_map_iff. exists (Z.to_nat t). split; [lia|].
  apply in_seq. lia.
Qed.
Lemma lt_sv_of_U : forall E v z, U E v = z -> 0 <= z < 2 ^ 64 -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H Hz. apply bv_eq. rewrite unsigned_lit_small by exact Hz. exact H. Qed.
(* the exit X reads no slot stored after the empty-input exit *)
Lemma lt_aframe_false : forall cx FF W mem, aframe_at cx true FF W mem -> aframe_at cx false FF W mem.
Proof.
  intros cx FF W mem H. unfold aframe_at in *. cbv zeta in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _ & H13).
  do 11 (split; [assumption|]). split; [intros Hf; discriminate Hf | exact H13].
Qed.
(* a register of the symbolic state, its value left as the symbolic expression *)
Ltac lt_prreg_raw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.

Theorem lf_seg_latch : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_K B G_fr fr_FP LS RINV cx t W c ->
  SRr segs W c (fun W' c' =>
    INV_H B G_fr fr_FP LS RINV cx (t + 1) W' c' \/ INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros cx t W c HB HK.
  destruct HK as (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR).
  destruct (lt_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs lt_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs lt_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_latch)) with (Z_to_bv 64 (BASE + AF_LLVM_latch)).
  paj_run_to_tok RUNTO HS HJ SHOK LBspan AF_fr_check_bounded.
  { apply awr_ok_x_nil. }
  pmkst HS.
  lt_mem HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs lt_extra lt_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof HR as ((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Rt & R22 & R144 & Rk).
  (* the frame's numbers: F is 320..351 below the entry sp, which is 32768 above ly_stk_lo >= alloc_ceiling *)
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (Hn26 : c_n cx < 2 ^ 26) by (unfold fr_lib_pre_cf in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : CEIL8 + 32000 <= lf_F cx) by (unfold CEIL8, LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= sp0) by lia.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold CEIL8 in *. lia. }
  (* check_bounded's afn_pre *)
  destruct (lt_afn_pre_at cx true ly3 S3 fpos k W mem mdc (ms_regs ms) CB_STK HB HJ HFR Hsp1)
    as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CB_STK. lia. }
  { unfold CB_STK, LLVMF_STK. lia. }
  (* its functional premises, from the relay's table *)
  pose proof HJ as (_ & _ & (memS & HJi & Hag) & _).
  pose proof (proj1 HJi) as HAR.
  pose proof HMOD as (_ & _ & HREL & _).
  pose proof HREL as (Rs1 & _ & Rs3 & _ & _ & _ & Rs7 & Rs8 & _).
  destruct (lt_blk B LAWS ly3 S3 W mem mdc _ _ HAR Rs8) as (PG1 & PG2 & PG3).
  set (n := Z.of_nat (length (lm_es m))).
  assert (Pn : - 2 ^ 31 <= n < 2 ^ 31) by (unfold n; lia).
  assert (Pns : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nsrc) 4 (n mod 2 ^ 32)).
  { replace (VAL A_g_nsrc) with (rg_nsrc fr_RG) by (vm_compute; reflexivity).
    rewrite Z.mod_small by (unfold n; lia). exact Rs3. }
  assert (Psr : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_src) 8 (lm_G m)).
  { replace (VAL A_g_src) with (rg_src fr_RG) by (vm_compute; reflexivity). exact Rs1. }
  assert (PP : 0 <= lm_G m < 2 ^ 64) by lia.
  assert (Pblk : 0 < n -> In (lm_G m, ATABLE) (ablocks B ly3 S3) /\ 56 * n <= req_size ATABLE).
  { intros _. split; [exact Rs8|]. unfold req_size, ATABLE, n. cbn. lia. }
  assert (Pent : forall j, 0 <= j < n -> cb_entry_ok W mem (lm_G m) j)
    by (intros j Hj; exact (lt_cb_entry ly3 S3 W mem mdc (lm_G m) (lm_es m) j HAR HREL Hj)).
  eapply SRr_bind.
  { exact (W1_check_bounded W ly3 S3 (ms_regs ms) mem mdc ch n (lm_G m) ATABLE HPREc Pn Pns Psr PP Pblk Pent). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HKEEP).
  rewrite Hsp1 in HJc, HKEEP. unfold CB_STK in HKEEP.
  clear HS SHOK HF HFr.
  (* check_bounded's journal inside this function's: W2's ajournal_gx_sub at G_fr, the callee's lifted from G = [] *)
  assert (HJc' : ajournal_gx segs B G_fr 0 [] CB_STK (lf_F cx) [] ly3 S3 W mem mdc [] ly3 S3 W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono segs B [] G_fr 0 [] CB_STK (lf_F cx) [] ly3 S3 W mem mdc [] ly3 S3 W2 mem2 md2 0 _ HJc).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc k
     CB_STK (lf_F cx) 0 [] [] [] ly3 S3 W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CB_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  (* every fact of the cut, kept across the call *)
  assert (HLO : CEIL8 <= lf_F cx - 16) by lia.
  pose proof (lt_keep_lo W W2 mem mem2 (lf_F cx) HKEEP HLO) as KL.
  pose proof (lt_keep_hi W W2 mem mem2 (lf_F cx) HKEEP ltac:(unfold CEIL8 in *; lia)) as KH.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem mdc 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  replace (fs_frame_bytes 1) with 128 in HFF1 by reflexivity.
  pose proof (lt_aframe_kept cx true (frame_addr ly3 1 fpos) W W2 mem mem2 HFR HKEEP HLO HFhi
     ltac:(lia) ltac:(lia) ltac:(unfold CEIL8; lia) ltac:(unfold SB; lia) ltac:(unfold SB, CEIL8; lia)) as HFR2.
  (* the fake frame's flag word (lcut's conjunct after aframe_at), kept like the fake frame's other words *)
  pose proof (lt_sv8_kept W W2 mem mem2 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)
     (fun x Hx => KL x ltac:(unfold CEIL8 in *; lia)) HFL) as HFL2.
  pose proof (lt_amodel_kept ly3 S3 W mem mdc W2 mem2 m HAR HMOD (proj1 ERRNO_LOW) (proj2 ERRNO_LOW) KL) as HMOD2.
  pose proof (lt_ainput_kept cx ly3 S3 W mem mdc W2 mem2 HAR HIN (eq_sym HlenP) KL) as HIN2.
  pose proof (lt_rom_kept W W2 mem mem2 HRV KL) as HRV2.
  pose proof (lt_jt_kept W W2 mem mem2 HROM KL) as HROM2.
  set (nl := c_n cx - lm_k m) in *.
  assert (R144b : sv8 W2 mem2 (lf_F cx + 144) nl).
  { apply (lt_sv8_kept W W2 mem mem2); [|exact R144]. intros x Hx. apply KH. lia. }
  (* the registers check_bounded keeps *)
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r lt_kept -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (lt_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  assert (H9b : getr regs2 9 = w64 (lf_F cx))
    by (rewrite (RR 9%bv ltac:(lt_cs) ltac:(unfold lt_kept; lt_in)); exact R9).
  assert (Hnl : 0 <= nl <= 2 ^ 26) by (unfold nl; lia).
  destruct (lt_entry2 W2 regs2 mem2 (lf_F cx) nl H9b ltac:(lia) ltac:(lia) Hnl R144b) as [HSb SHOKb].
  (* the two cut points the walk ends at, from the facts kept across the call: the shutdown block X after
     t + 1 operations, and the loop head H of operation t + 1 *)
  assert (XFIN : forall c, (exists rf mdf, c = cfg_at segs (fr_B0 + AF_LLVM_exit) rf mem2 mdf /\
      (forall r, In r lt_saved -> getr rf r = getr regs r) /\
      ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W2 mem2 mdf k) ->
      INV_X B G_fr fr_FP LS RINV cx W2 c).
  { intros c (rf & mdf & -> & KX & HJf).
    exists rf, mem2, mdf, (t + 1). split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly3, S3, k, m, fpos.
    split; [exact HJf|]. split; [reflexivity|]. split; [exact (lt_aframe_false _ _ _ _ HFR2)|]. split; [exact HFL2|].
    split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HRI|].
    unfold lregs_X.
    repeat split;
      first [ match goal with |- getr rf ?r = _ => rewrite (KX r ltac:(unfold lt_saved; lt_in)) end; assumption
            | lia ]. }
  assert (HFIN : forall c, (exists rf mdf, c = cfg_at segs (fr_B0 + AF_LLVM_head) rf mem2 mdf /\
      (forall r, In r lt_saved -> getr rf r = getr regs r) /\
      getr rf 6 = w64 4 /\ getr rf 7 = w64 1 /\ getr rf 21 = w64 nl /\ getr rf 27 = w64 (t + 1) /\
      ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W2 mem2 mdf k) ->
      t <= 510 -> nl <> 0 -> INV_H B G_fr fr_FP LS RINV cx (t + 1) W2 c).
  { intros c (rf & mdf & -> & KX & Q6 & Q7 & Q21 & Q27 & HJf) Ht Hn.
    assert (Hk1 : lm_k m < c_n cx) by (unfold nl in Hn; lia).
    exists rf, mem2, mdf. split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly3, S3, k, m, fpos.
    split; [exact HJf|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|].
    split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HRI|].
    unfold lregs_H, lregs_common.
    repeat split;
      first [ exact Q6 | exact Q7 | exact Q21 | exact Q27
            | match goal with |- getr rf ?r = _ => rewrite (KX r ltac:(unfold lt_saved; lt_in)) end; assumption
            | unfold OPS_MAX in *; lia ]. }
  rewrite Q1.
  change (Z_to_bv 64 (BASE + 8616)) with (Z_to_bv 64 (BASE + AF_LLVM_latch4)).
  remember (Eimg (Ereg regs2 (lt2_extra nl))) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 (lt2_extra nl)) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E27 : ew Eb 27 = Z_to_bv 64 t).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl).
    rewrite (RR 27%bv ltac:(lt_cs) ltac:(unfold lt_kept; lt_in)). exact R27. }
  assert (E32 : ew Eb 32 = Z_to_bv 64 nl)
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  clear HEb.
  paj_run_tok RUN HSb HJ2 SHOKb LBspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lt_mem HF Em2. clear HF HFr.
  assert (Rt' : 0 <= t < 512) by (unfold OPS_MAX in Rt; exact Rt).
  (* bltu a0(510), s11(t): after operation 511 the loop is left *)
  psrr_branch_tok RUN BR HSb SHOKb LBspan.
  - assert (Ht511 : t = 511).
    { rewrite branch_ltu_U, (U_lit Eb 510), (U_atom Eb 27 t E27) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
    paj_run_to_tok RUNTO HSb HJ2 SHOKb LBspan AF_LLVM_exit.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    lt_mem HF Em3.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply SRr_ret. right. apply XFIN.
    lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
    split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|]. exact HJ2.
  - assert (Ht510 : t <= 510).
    { rewrite branch_ltu_U, (U_lit Eb 510), (U_atom Eb 27 t E27) in Hc by lia. apply Z.ltb_ge in Hc. lia. }
    (* addiw s11,s11,1 *)
    paj_run_tok RUN HSb HJ2 SHOKb LBspan.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    lt_mem HF Em3. clear HF HFr Hc.
    (* bnez s5(in.n): the next operation, or the shutdown *)
    psrr_branch_tok RUN BR HSb SHOKb LBspan.
    + assert (Hn0 : nl <> 0).
      { rewrite branch_ne_U, (U_atom Eb 32 nl E32), U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
        exact Hc. }
      paj_run_to_tok RUNTO HSb HJ2 SHOKb LBspan AF_LLVM_head.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      lt_mem HF Em4.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
        ltac:(vm_compute; reflexivity)) as KR2.
      cbn [ms_regs restrict] in KR2.
      prreg HSb (6%bv : bv 5) Q6. prreg HSb (7%bv : bv 5) Q7. prreg HSb (21%bv : bv 5) Q21.
      lt_prreg_raw HSb (27%bv : bv 5) Q27.
      rewrite ?E32 in Q21.
      rewrite (lt_sv_of_U Eb _ (t + 1) (lt_addiw_U Eb t E27 ltac:(lia)) ltac:(lia)) in Q27.
      pmkst HSb.
      rewrite Em4 in *. rewrite Em3 in *. rewrite Em2 in *.
      apply SRr_ret. left. apply HFIN; [|exact Ht510|exact Hn0].
      lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
      split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|].
      split; [exact Q6|]. split; [exact Q7|]. split; [exact Q21|]. split; [exact Q27|]. exact HJ2.
    + (* j 0x84bf8 *)
      paj_run_to_tok RUNTO HSb HJ2 SHOKb LBspan AF_LLVM_exit.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      lt_mem HF Em4.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
        ltac:(vm_compute; reflexivity)) as KR2.
      cbn [ms_regs restrict] in KR2.
      pmkst HSb.
      rewrite Em4 in *. rewrite Em3 in *. rewrite Em2 in *.
      apply SRr_ret. right. apply XFIN.
      lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
      split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|]. exact HJ2.
Qed.
End w.
