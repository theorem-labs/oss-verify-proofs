(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the four small arms of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput
   -- arm 3 (s->closed = 1, 0x84588), arm 6 (s->eintr = 1, 0x84614), arm 8 (g_send_max = fuzz_u8(&in);
   g_send_eintr = 1, 0x84638) and the default arm 9 (the controller goes away, 0x84660) -- in the form of the cgif
   segment walks (proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v rt_from: a segment is an SRr from one cut point's
   invariant to the next), over the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut.v.
   Each theorem is exactly one of that file's Section hypotheses: ARM_close, ARM_eintr, ARM_sendmax, ARM_default.
   What it takes beyond _cut's own Section variables (B, MT, XM_LIB, XN_LIB, RLO, RHI, fr_live_pre, fr_live_post,
   fr_surv, G_fr, fr_FP, LAWS, HG, LS, RINV):
     TL              - the allocator instance (W_kit.v PALib): its api_env puts errno's cell below kLowMemEnd;
     HERRHI          - errno's cell lies above g_out, the highest of the program's globals (G_fr contains errno's
                       four bytes; W_LLVMFuzzerTestOneInput_G.v c_HERRHI proves this at G_fr_c's instance);
     HGs .. HGlk     - that each global these arms store to is covered by G_fr (inG), one per object;
     HZS             - g_s's 384 bytes are in the instance's zero-shadow ranges (azs), which is what the arms'
                       ASan checks of g_s[i] read;
     ALOCK / AUNLOCK - W_sites.v's pthread_mutex_lock / _unlock site contracts, the default arm's two calls, as
                       _drain.v states them (proved by R5: a working branch b1c048a98a5, RT_pthread_mutex_lock.v
                       rt_pthread_mutex_lock and RT_pthread_mutex_unlock.v rt_pthread_mutex_unlock);
     RI_* / LS_*     - the model step of each arm: the loop's relational invariant and the allocator-state
                       invariant after it.  These are the open model obligations of this file. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section sm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
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
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* ---------------------------------------------------------------- the image, by computation *)
(* fuzz_reply.asan's four loaded segments: [0x10000, 0x30000) and [0x30000, 0x9d000) read-only,
   [0x9d000, 0x9f000) and [0x9f000, 0x5fb000) writable (vm_compute over pa_segs PB_fr). *)
Definition sm_segmap : list (Z * Z) := [(65536, 131072); (196608, 446464); (643072, 8192); (651264, 5619712)].
Lemma sm_segs : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs = sm_segmap.
Proof. vm_compute. reflexivity. Qed.
Lemma sm_rom_range : forall a, in_rom segs a -> 0x10000 <= a < 0x9d000.
Proof.
  intros a (sg & Hin & Hw & Hr).
  assert (Hf : In sg (List.filter (fun s => negb (seg_writable s)) segs))
    by (apply (proj2 (filter_In _ sg segs)); split; [exact Hin | rewrite Hw; reflexivity]).
  assert (HL1 : map (fun s => Z.of_N (seg_base s))
      (List.filter (fun s => negb (seg_writable s)) segs) = [65536; 196608])
    by (vm_compute; reflexivity).
  assert (HL2 : map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s))
      (List.filter (fun s => negb (seg_writable s)) segs) = [196608; 643072])
    by (vm_compute; reflexivity).
  assert (Hb1 : In (Z.of_N (seg_base sg)) [65536; 196608])
    by (rewrite <- HL1; apply (in_map (fun s => Z.of_N (seg_base s))); exact Hf).
  assert (Hb2 : In (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) [196608; 643072])
    by (rewrite <- HL2; apply (in_map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s))); exact Hf).
  destruct Hb1 as [E1|[E1|[]]]; destruct Hb2 as [E2|[E2|[]]]; lia.
Qed.
Lemma sm_img_of : forall a, 0x9d000 <= a < 0x5fb000 -> in_img segs a.
Proof.
  intros a Ha. pose proof sm_segs as HL.
  destruct (Z_lt_le_dec a 651264) as [H|H].
  - assert (Hin : In (643072, 8192) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs))
      by (rewrite HL; unfold sm_segmap; cbn; tauto).
    apply in_map_iff in Hin as (sg & E & Hsg). exists sg. split; [exact Hsg|]. injection E as E1 E2. lia.
  - assert (Hin : In (651264, 5619712) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs))
      by (rewrite HL; unfold sm_segmap; cbn; tauto).
    apply in_map_iff in Hin as (sg & E & Hsg). exists sg. split; [exact Hsg|]. injection E as E1 E2. lia.
Qed.

(* ---------------------------------------------------------------- what a run keeps *)
(* X is the list of ranges the arm stores to: each is either a program global (inside the image's writable
   segments) or high in this frame's stack window. *)
Definition CEIL8 : Z := alloc_ceiling + 8.
Definition XOK (X : list (Z * Z)) : Prop :=
  forall a, inFP X a -> (0x9d000 <= a < 0x5fb000) \/ alloc_ceiling + 1024 <= a.
Definition KEPT (W : world segs) (m m' : word -> option byte) (X : list (Z * Z)) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ inFP X a -> abyte_kept W m W m' a.
Lemma sm_ceil_lo : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact (proj1 alloc_ceiling_val). Qed.

Lemma sm_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
Lemma sm_wkeep : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  writable_at segs (arm W m) a -> writable_at segs (arm W m') a.
Proof.
  intros W m m' a HGr Hw. apply (writable_kept (w_H W) m m' a); [|exact Hw].
  intros Hp. exact (sm_pres_grows W m m' a HGr Hp).
Qed.
Lemma sm_awr : forall (W : world segs) m m' a n,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> awr W m a n -> awr W m' a n.
Proof. intros W m m' a n HGr Hw i Hi. exact (sm_wkeep W m m' (a + i) HGr (Hw i Hi)). Qed.

(* a byte of a live block, with the seven bytes of slack a key's NUL padding may add past it, is never in X *)
Lemma sm_blk_kept : forall ly S (W : world segs) mem md mem' X b n a,
  AR segs B ly S W mem md -> XOK X -> KEPT W mem mem' X ->
  In (b, n) (ablocks B ly S) -> b <= a < b + req_size n + 8 -> abyte_kept W mem W mem' a.
Proof.
  intros ly S W mem md mem' X b n a HAR HX HK Hin Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hin) as (_ & H4096 & Hceil & _).
  pose proof (blk_off_imgP B ly S W mem md b n HAR Hin) as Hoff.
  pose proof sm_ceil_lo as Hac.
  apply HK; [unfold off_img in Hoff; lia|].
  intros HinX. destruct (HX a HinX) as [Hc | Hc]; unfold off_img in Hoff; lia.
Qed.
(* a byte of the fake frame, or of its shadow, is never in X either *)
Lemma sm_frm_kept : forall ly S (W : world segs) mem md mem' X cid pos a,
  AR segs B ly S W mem md -> XOK X -> KEPT W mem mem' X -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> abyte_kept W mem W mem' a.
Proof.
  intros ly S W mem md mem' X cid pos a HAR HX HK Hin Ha.
  destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (H1 & H2 & _).
  pose proof sm_ceil_lo as Hac.
  apply HK; [lia|]. intros HinX. destruct (HX a HinX) as [Hc | Hc]; [|lia].
  destruct (al_client_img _ _ LAWS ly S W mem md a HAR
    (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha)))))) as [_ Hni].
  exact (Hni (sm_img_of a Hc)).
Qed.
(* a read-only image byte is never in X, so the .rodata view and the jump table carry *)
Lemma sm_rom_kept : forall (W : world segs) mem mem' X,
  XOK X -> KEPT W mem mem' X -> rom_view segs W mem -> rom_view segs W mem'.
Proof.
  intros W mem mem' X HX HK HR a Ha. rewrite <- (HR a Ha).
  pose proof (sm_rom_range a Ha) as Hlt. pose proof sm_ceil_lo as Hac.
  destruct (HK a ltac:(lia) ltac:(intros HinX; destruct (HX a HinX) as [Hc | Hc]; lia)) as [Hv _]. exact Hv.
Qed.
Lemma sm_jt_kept : forall (W : world segs) mem mem' X,
  XOK X -> KEPT W mem mem' X ->
  jt_rom W mem -> jt_rom W mem'.
Proof.
  intros W mem mem' X HX HK HJ i Hi.
  apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. cbn [Z.of_nat] in Hx. pose proof sm_ceil_lo as Hac.
  apply HK; [unfold fr_jtab in *; lia|].
  intros HinX. destruct (HX x HinX) as [Hc | Hc]; unfold fr_jtab in *; lia.
Qed.
(* keeping over a concrete range of the image's globals *)
Lemma sm_glob_kept : forall (W : world segs) mem mem' X a n,
  KEPT W mem mem' X -> 0x9d000 <= a -> a + n <= 0x5fb000 -> (forall x, a <= x < a + n -> ~ inFP X x) ->
  forall x, a <= x < a + n -> abyte_kept W mem W mem' x.
Proof. intros W mem mem' X a n HK H1 H2 Hd x Hx. apply HK; [lia | exact (Hd x Hx)]. Qed.

(* ---------------------------------------------------------------- the cut facts' footprints
   Ported from W8SegHead's store-frame kit (lib/A/W_LLVMFuzzerTestOneInput_head.v:240-373, hd_len_text,
   hd_len_kptrs, hd_alist_fp_off, hd_asrc_fp_off, hd_aentry_fp_off, hd_arelay_fp_off and the *_blks_in
   companions), with its single stored range [lo, hi) generalised to the list X these arms store to and its
   `offw lo hi` replaced by `abyte_kept` through sm_blk_kept. *)
Definition sm_koff (W : world segs) (mem mem' : word -> option byte) (r : Z * Z) : Prop :=
  forall a, fst r <= a < snd r -> abyte_kept W mem W mem' a.
Lemma sm_koff_sub : forall (W : world segs) mem mem' a n a' n',
  sm_koff W mem mem' (a, a + n) -> a <= a' -> a' + n' <= a + n -> sm_koff W mem mem' (a', a' + n').
Proof. intros W mem mem' a n a' n' H H1 H2 x Hx. apply H. cbn in *. lia. Qed.
Lemma sm_len_text : forall recs, length (concat (map text_rec recs)) = (16 * length recs)%nat.
Proof.
  induction recs as [|r recs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
  assert (Hx : length (text_rec r) = 16%nat) by reflexivity. rewrite Hx. cbn [length]. lia.
Qed.
Lemma sm_len_kptrs : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
  match goal with |- (length ?x + _)%nat = _ => assert (Hx : length x = 8%nat) by reflexivity; rewrite Hx end.
  cbn [length]. lia.
Qed.

Lemma sm_alist_fp_kept : forall X (W : world segs) (mem mem' : word -> option byte), XOK X -> KEPT W mem mem' X -> forall ly S md LA l lines, AR segs B ly S W mem md ->
  alist_at B ly S W mem LA l lines -> sm_koff W mem mem' (LA, LA + 16) ->
  forall r, In r (alist_fp LA l) -> sm_koff W mem mem' r.
Proof.
  intros X W mem mem' HX HK ly S md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, sm_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (sm_blk_kept ly S W mem md mem' X (hl_v l) (AREC * hl_cap l) a HAR HX HK Hin).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (sm_blk_kept ly S W mem md mem' X (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR HX HK Hb).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma sm_alist_blks_in : forall (W : world segs) (mem : word -> option byte), forall ly S LA l lines, alist_at B ly S W mem LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros W mem ly S LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (rr & <- & Hrr). rewrite Forall_forall in H9. exact (proj1 (H9 rr Hrr)).
Qed.
Lemma sm_asrc_fp_kept : forall X (W : world segs) (mem mem' : word -> option byte), XOK X -> KEPT W mem mem' X -> forall ly S md HA h, AR segs B ly S W mem md -> asrc_at B ly S W mem HA h ->
  sm_koff W mem mem' (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> sm_koff W mem mem' r.
Proof.
  intros X W mem mem' HX HK ly S md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (sm_blk_kept ly S W mem md mem' X (hs_partial h) APARTIAL a HAR HX HK H18).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (sm_alist_fp_kept X W mem mem' HX HK ly S md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (sm_koff_sub W mem mem' HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (sm_alist_fp_kept X W mem mem' HX HK ly S md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (sm_koff_sub W mem mem' HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (sm_alist_fp_kept X W mem mem' HX HK ly S md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (sm_koff_sub W mem mem' HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.
Lemma sm_asrc_blks_in : forall (W : world segs) (mem : word -> option byte), forall ly S HA h, asrc_at B ly S W mem HA h ->
  forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros W mem ly S HA h Hs b Hb.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - exact (sm_alist_blks_in W mem ly S _ _ _ H10 b Hb).
  - exact (sm_alist_blks_in W mem ly S _ _ _ H22 b Hb).
  - exact (sm_alist_blks_in W mem ly S _ _ _ H23 b Hb).
Qed.
Lemma sm_aentry_fp_kept : forall X (W : world segs) (mem mem' : word -> option byte), XOK X -> KEPT W mem mem' X -> forall ly S md e, AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> sm_koff W mem mem' r.
Proof.
  intros X W mem mem' HX HK ly S md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (sm_blk_kept ly S W mem md mem' X (re_buf e) (re_cap e) a HAR HX HK Hin).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, sm_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (sm_blk_kept ly S W mem md mem' X (re_hp e) (re_kh e) a HAR HX HK Hin).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15.
      destruct (H15 k Hk) as (K1 & K2 & K3 & K4).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (sm_blk_kept ly S W mem md mem' X (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR HX HK K1).
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma sm_aentry_blks_in : forall (W : world segs) (mem : word -> option byte), forall ly S e, aentry_ok B ly S W mem e ->
  forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros W mem ly S e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & _)]; [lia | exact Hin].
  - destruct (re_hp e =? 0) eqn:Ez; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ez.
    destruct H12 as [(Hz & _) | (Hz & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
Lemma sm_arelay_fp_kept : forall X (W : world segs) (mem mem' : word -> option byte), XOK X -> KEPT W mem mem' X -> forall RG ly S md G es, AR segs B ly S W mem md -> arelay_at B RG ly S W mem G es ->
  sm_koff W mem mem' (rg_src RG, rg_src RG + 8) -> sm_koff W mem mem' (rg_nsrc RG, rg_nsrc RG + 4) ->
  sm_koff W mem mem' (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> sm_koff W mem mem' r.
Proof.
  intros X W mem mem' HX HK RG ly S md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (sm_blk_kept ly S W mem md mem' X G ATABLE a HAR HX HK H8).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (sm_aentry_fp_kept X W mem mem' HX HK ly S md e HAR (H10 e He) r Hr).
Qed.
Lemma sm_arelay_blks_in : forall (W : world segs) (mem : word -> option byte), forall RG ly S G es, arelay_at B RG ly S W mem G es ->
  forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros W mem RG ly S G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) b Hb.
  unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  rewrite Forall_forall in H10. exact (sm_aentry_blks_in W mem ly S e (H10 e He) b Hb).
Qed.
(* akept over a footprint whose every range is kept *)
Lemma sm_akept_of : forall (W : world segs) (mem mem' : word -> option byte) fp, (forall r, In r fp -> sm_koff W mem mem' r) -> akept W mem W mem' fp.
Proof. intros W mem mem' fp H r Hr a Ha. exact (H r Hr a Ha). Qed.

Lemma azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|].
  split; [exact H8|]. split; lia.
Qed.

(* ---------------------------------------------------------------- pick() returns an open slot *)
Lemma sm_pick_from : forall hs j k i, pick_from hs j k = Some i ->
  (j <= i < j + length hs)%nat /\ exists h, nth (i - j) hs None = Some h.
Proof.
  induction hs as [|o hs IH]; intros j k i Hp; [discriminate Hp|].
  destruct o as [h|]; cbn in Hp.
  - destruct (k =? 0) eqn:Hk.
    + injection Hp as <-. rewrite Nat.sub_diag. split; [cbn; lia | exists h; reflexivity].
    + destruct (IH (S j) (k - 1) i Hp) as [Hr [h' Hh']]. split; [cbn; lia|].
      exists h'. replace (i - j)%nat with (S (i - S j)) by lia. exact Hh'.
  - destruct (IH (S j) k i Hp) as [Hr [h' Hh']]. split; [cbn; lia|].
    exists h'. replace (i - j)%nat with (S (i - S j)) by lia. exact Hh'.
Qed.
Lemma sm_pick : forall hs kb i, pick hs kb = Some i -> (i < length hs)%nat /\ exists h, nth i hs None = Some h.
Proof.
  intros hs kb i Hp. unfold pick in Hp. destruct (nopen hs =? 0); [discriminate Hp|].
  destruct (sm_pick_from hs 0 (kb mod nopen hs) i Hp) as [Hr [h Hh]].
  rewrite Nat.sub_0_r in Hh. split; [lia | exists h; exact Hh].
Qed.

(* ---------------------------------------------------------------- the model step of the four arms *)
Definition upd_closed (h : hsrc) : hsrc :=
  HS (hs_fd h) (hs_open h) 1 (hs_eintr h) (hs_pending h) (hs_off h) (hs_partial h) (hs_pjunk h)
     (hs_npartial h) (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).
Definition upd_eintr (h : hsrc) : hsrc :=
  HS (hs_fd h) (hs_open h) (hs_closed h) 1 (hs_pending h) (hs_off h) (hs_partial h) (hs_pjunk h)
     (hs_npartial h) (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).
Fixpoint upd_hs (i : nat) (f : hsrc -> hsrc) (l : list (option hsrc)) : list (option hsrc) :=
  match i, l with
  | _, [] => []
  | O, Some h :: l' => Some (f h) :: l'
  | O, None :: l' => None :: l'
  | S i', x :: l' => x :: upd_hs i' f l'
  end.
Lemma upd_hs_length : forall i f l, length (upd_hs i f l) = length l.
Proof.
  induction i as [|i IH]; intros f l.
  - destruct l as [|[h|] l']; reflexivity.
  - destruct l as [|x l']; [reflexivity|]. cbn [upd_hs length]. rewrite IH. reflexivity.
Qed.
Lemma upd_hs_nth_same : forall i f l h, nth i l None = Some h -> nth i (upd_hs i f l) None = Some (f h).
Proof.
  induction i as [|i IH]; intros f l h Hn.
  - destruct l as [|[h'|] l']; cbn in Hn; try discriminate Hn.
    injection Hn as <-. reflexivity.
  - destruct l as [|x l']; cbn in Hn; [discriminate Hn|].
    cbn [upd_hs nth]. apply IH. exact Hn.
Qed.
Lemma upd_hs_nth_other : forall i f l j, j <> i -> nth j (upd_hs i f l) None = nth j l None.
Proof.
  induction i as [|i IH]; intros f l j Hj.
  - destruct l as [|[h|] l']; [reflexivity | | reflexivity].
    destruct j as [|j]; [exfalso; apply Hj; reflexivity | reflexivity].
  - destruct l as [|x l']; [reflexivity|].
    destruct j as [|j]; [reflexivity|]. cbn [upd_hs nth]. apply IH. lia.
Qed.
Lemma upd_hs_blks : forall i f l, (forall h, asrc_blks (f h) = asrc_blks h) ->
  map slot_blks (upd_hs i f l) = map slot_blks l.
Proof.
  induction i as [|i IH]; intros f l Hf.
  - destruct l as [|[h|] l']; [reflexivity | | reflexivity].
    cbn [upd_hs map slot_blks]. rewrite Hf. reflexivity.
  - destruct l as [|x l']; [reflexivity|].
    cbn [upd_hs map]. rewrite (IH f l' Hf). reflexivity.
Qed.
Lemma upd_closed_blks : forall h, asrc_blks (upd_closed h) = asrc_blks h.
Proof. intros h. reflexivity. Qed.
Lemma upd_eintr_blks : forall h, asrc_blks (upd_eintr h) = asrc_blks h.
Proof. intros h. reflexivity. Qed.

(* the cursor after one operation: the op byte, and the second byte when the input still had one *)
Definition sm_kn (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1.
Definition sm_close (cx : lfcx) (m : lmod) (i : nat) : lmod :=
  LM (sm_kn cx m) (upd_hs i upd_closed (lm_hs m)) (lm_G m) (lm_es m)
     (lm_c m) [] (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition sm_eintr (cx : lfcx) (m : lmod) (i : nat) : lmod :=
  LM (sm_kn cx m) (upd_hs i upd_eintr (lm_hs m)) (lm_G m) (lm_es m)
     (lm_c m) [] (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition sm_sendmax (cx : lfcx) (m : lmod) (u : Z) : lmod :=
  LM (sm_kn cx m) (lm_hs m) (lm_G m) (lm_es m)
     (CTL (ct_cl (lm_c m)) (ct_br (lm_c m)) (ct_dd (lm_c m)) 1 (ct_ev (lm_c m))) []
     u (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition sm_default (cx : lfcx) (m : lmod) (gone : bool) : lmod :=
  LM (sm_kn cx m) (lm_hs m) (lm_G m) (lm_es m)
     (CTL (if gone then -1 else ct_cl (lm_c m)) (ct_br (lm_c m))
          (if gone then ct_dd (lm_c m) else 1) (ct_ei (lm_c m)) (ct_ev (lm_c m))) []
     (lm_mx m) (lm_cap m) (lm_out m) 1 (lm_nfd m).
(* the default arm's branch: the controller is gone (g_client := -1) when the input had a second byte and its low
   bit is 1 *)
Definition sm_dg (cx : lfcx) (m : lmod) : bool := (lm_k m + 1 <? c_n cx) && Z.odd (in_byte cx (lm_k m + 1)).

(* ---------------------------------------------------------------- what this file takes *)
(* the globals these arms store to are covered by G_fr *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HGmx : forall a, rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 -> inG G_fr a.
Hypothesis HGei : forall a, rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1 -> inG G_fr a.
Hypothesis HGdd : forall a, rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1 -> inG G_fr a.
Hypothesis HGgn : forall a, rg_gone fr_RG <= a < rg_gone fr_RG + 1 -> inG G_fr a.
Hypothesis HGcl : forall a, rg_client fr_RG <= a < rg_client fr_RG + 4 -> inG G_fr a.
Hypothesis HGlk : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
(* g_s's four sources are in the instance's zero-shadow ranges: the arms' checks of g_s[i] pass *)
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* the allocator instance (W_kit.v): its api_env puts errno's cell in the image, below kLowMemEnd *)
Hypothesis TL : PALib B.
(* errno's cell lies above g_out, the highest of the program's globals (errno = TFIB_ERRNO = 0x5d93cc, musl's
   static-TLS cell; proved for G_fr_c's instance as W_LLVMFuzzerTestOneInput_G.v c_HERRHI) *)
Hypothesis HERRHI : rg_out fr_RG + 8 <= as_errno B.
(* the default arm's two libc calls: W_sites.v's site contracts, stated as _drain.v states them; proved by R5
   (a working branch b1c048a98a5: RT_pthread_mutex_lock.v rt_pthread_mutex_lock, RT_pthread_mutex_unlock.v
   rt_pthread_mutex_unlock) *)
Hypothesis ALOCK : alock_realizes B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock).
(* the model step of each arm (the open obligations of this file), each at the choice the walk makes: the source
   pick() returns for the second byte (or 0), the second byte (or 0), the default arm's branch *)
Hypothesis RI_close : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_close cx m i).
Hypothesis RI_eintr : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_eintr cx m i).
Hypothesis RI_sendmax : forall cx t m, RINV cx t m ->
  RINV cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
Hypothesis RI_default : forall cx t m, RINV cx t m -> RINV cx (t + 1) (sm_default cx m (sm_dg cx m)).
Hypothesis LS_close : forall cx t m i ly S, LS cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LS cx (t + 1) (sm_close cx m i) ly S.
Hypothesis LS_eintr : forall cx t m i ly S, LS cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LS cx (t + 1) (sm_eintr cx m i) ly S.
Hypothesis LS_sendmax : forall cx t m ly S, LS cx t m ly S ->
  LS cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Hypothesis LS_default : forall cx t m ly S, LS cx t m ly S -> LS cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.


(* ---------------------------------------------------------------- arms 3 and 6: one flag word *)
(* 0x84588 (close) / 0x84614 (eintr): `sd t4,144(s1); mv s6,t3; addi a0,s5,fo; <shadow check>; sw t2,0(a0);
   j 0x84490`, with fo = 8 (s->closed) or 12 (s->eintr) and t2 = 1 throughout the loop. *)
Definition sm_fl_sr : list sv := sr_set sr_atoms 7 (SLit 1).
Definition sm_fl_regions (fo : Z) : smem :=
  [ YP09.mkRegion (Some 9%nat) 144 152 144 152 []; YP09.mkRegion (Some 21%nat) fo (fo + 4) fo (fo + 4) [] ].
Definition sm_fl_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, mkAF (rg_s fr_RG) (rg_s fr_RG + 4 * ASRC) 5);
            (26%nat, mkAF SB SB 0) ] [] [].
Definition sm_Bx : sv := SOff 26 0.
Definition sm_fl_SH : list shent := [ mkSHE 21 0 ASRC ].

Lemma sm_fl_entry : forall (W : world segs) regs mem ly S md F HA fo pc,
  AR segs B ly S W mem md ->
  getr regs 7 = w64 1 -> getr regs 9 = w64 F -> getr regs 21 = w64 HA -> getr regs 26 = w64 SB ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  rg_s fr_RG <= HA <= rg_s fr_RG + 4 * ASRC -> HA mod 32 = 0 ->
  (fo = 8 \/ fo = 12) ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  (forall a, HA + fo <= a < HA + fo + 4 -> writable_at segs (arm W mem) a) ->
  azs B HA ASRC ->
  st_ok_pi segs VAL (Eimg (Ereg regs (@nil word))) (mkSS pc sm_fl_sr (sm_fl_regions fo) None sm_fl_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs sm_Bx sm_fl_SH (Eimg (Ereg regs (@nil word))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem ly S md F HA fo pc HAR H7 H9 H21 H26 HF1 HF2 HH1 HH2 Hfo HW1 HW2 HZ.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (@nil word))).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E7 : ew E 7 = w64 1) by (rewrite (EE 7%nat 7%bv eq_refl); exact H7).
  assert (E9 : ew E 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E21 : ew E 21 = w64 HA) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
  assert (E26 : ew E 26 = w64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
  assert (HRS : rg_s fr_RG = 6129888) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  destruct Hfo as [-> | ->];
  (split;
   [ apply pa_entry_st_ok_full;
     [ unfold sm_fl_sr; apply regs_ok_pin;
       [ apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H7 ]
     | vm_compute; reflexivity
     | unfold sm_fl_regions; repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
       cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
       [ rewrite E9, unsigned_lit_small by lia;
         split; [lia|]; split; [lia|]; split; [intros o Ho; apply HW1; lia | apply Forall_nil]
       | rewrite E21, unsigned_lit_small by lia;
         split; [lia|]; split; [lia|]; split; [intros o Ho; apply HW2; lia | apply Forall_nil] ]
     | apply pairwise_disjoint_of_extents; unfold sm_fl_regions, extent_of_region;
       cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val];
       rewrite E9, E21, !unsigned_lit_small by lia;
       cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia
     | split; [|split; [exact I | exact I]];
       cbn [sm_fl_facts f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
       rewrite E9, E21, E26, !unsigned_lit_small by lia;
       rewrite !Z.pow_0_r, !Z.mod_1_r;
       repeat match goal with |- _ /\ _ => split end; try change (2 ^ 5) with 32; lia ]
   | unfold sh_ok, sm_fl_SH; constructor; [|constructor];
     eapply shent_ok_of_range;
     [ exact (azs_range_addressable B LAWS ly S W mem md HA ASRC HAR HZ)
     | unfold sm_Bx; rewrite (U_atom E 26 SB E26) by lia; reflexivity
     | rewrite (U_atom E 21 HA E21) by lia; reflexivity
     | lia
     | lia
     | intros x Hx; cbn [Z.min Z.max] in Hx; lia ] ]).
Qed.


(* the stored source after the arm: every field but the one flag word is the one it was *)
Definition same_but_flags (h h' : hsrc) : Prop :=
  hs_fd h' = hs_fd h /\ hs_open h' = hs_open h /\ hs_pending h' = hs_pending h /\ hs_off h' = hs_off h /\
  hs_partial h' = hs_partial h /\ hs_pjunk h' = hs_pjunk h /\ hs_npartial h' = hs_npartial h /\
  hs_overlong h' = hs_overlong h /\ hs_pad h' = hs_pad h /\ hs_expected h' = hs_expected h /\
  hs_held h' = hs_held h.
Lemma same_but_flags_closed : forall h, same_but_flags h (upd_closed h).
Proof. intros h. repeat split. Qed.
Lemma same_but_flags_eintr : forall h, same_but_flags h (upd_eintr h).
Proof. intros h. repeat split. Qed.

Lemma sm_slot_store : forall ly S (W : world segs) mem md mem' X HA h h' fo,
  AR segs B ly S W mem md -> XOK X -> KEPT W mem mem' X ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  asrc_at B ly S W mem HA h -> same_but_flags h h' ->
  ((fo = 8 /\ hs_closed h' = 1 /\ hs_eintr h' = hs_eintr h) \/
   (fo = 12 /\ hs_eintr h' = 1 /\ hs_closed h' = hs_closed h)) ->
  (forall a, HA <= a < HA + ASRC -> ~ (HA + fo <= a < HA + fo + 4) -> ~ inFP X a) ->
  0 <= HA -> HA + ASRC < 2 ^ 64 ->
  val_mem segs (arm W mem') (HA + fo) 4 1 ->
  asrc_at B ly S W mem' HA h'.
Proof.
  intros ly S W mem md mem' X HA h h' fo HAR HX HK HGr Hs Hsame Hfo Hdis HA0 HA1 Hnew.
  destruct Hsame as (Efd & Eopen & Epend & Eoff & Epart & Epjunk & Enp & Eov & Epad & Eexp & Eheld).
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  assert (HAS : ASRC = 96) by reflexivity.
  assert (KH : forall a, HA <= a < HA + ASRC -> ~ (HA + fo <= a < HA + fo + 4) -> abyte_kept W mem W mem' a)
    by (intros a Ha Hn; apply HK; [lia | exact (Hdis a Ha Hn)]).
  assert (KV : forall a n v, HA <= a -> a + Z.of_nat n <= HA + ASRC ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (HA + fo <= x < HA + fo + 4)) ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v)
    by (intros a n v Ha Hn Hd Hv; apply (akept_vm W mem); [intros x Hx; apply KH; [lia | exact (Hd x Hx)] | exact Hv]).
  assert (KL : forall LA, HA <= LA -> LA + 16 <= HA + ASRC ->
      (forall x, LA <= x < LA + 16 -> ~ (HA + fo <= x < HA + fo + 4)) -> sm_koff W mem mem' (LA, LA + 16))
    by (intros LA Ha Hn Hd x Hx; cbn [fst snd] in Hx; apply KH; [lia | exact (Hd x Hx)]).
  assert (KAL : forall LA l lines, HA <= LA -> LA + 16 <= HA + ASRC ->
      (forall x, LA <= x < LA + 16 -> ~ (HA + fo <= x < HA + fo + 4)) ->
      alist_at B ly S W mem LA l lines -> alist_at B ly S W mem' LA l lines).
  { intros LA l lines Ha Hn Hd Hl.
    apply (alist_at_kept B ly S W mem ly S W mem' LA l lines Hl).
    - apply (sm_akept_of W mem mem'). intros r Hr.
      exact (sm_alist_fp_kept X W mem mem' HX HK ly S md LA l lines HAR Hl (KL LA Ha Hn Hd) r Hr).
    - exact (sm_alist_blks_in W mem ly S LA l lines Hl). }
  assert (HBW : forall a, hs_partial h <= a < hs_partial h + req_size APARTIAL + 8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; exact (sm_blk_kept ly S W mem md mem' X (hs_partial h) APARTIAL a HAR HX HK H18 Ha)).
  assert (HFO : fo = 8 \/ fo = 12) by (destruct Hfo as [(-> & _) | (-> & _)]; [left | right]; reflexivity).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]]]]]]]]]]].
  - rewrite Efd. apply (KV HA 4%nat (hs_fd h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H1].
  - rewrite Eopen. apply (KV (HA + 4) 4%nat (hs_open h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H2].
  - destruct Hfo as [(-> & Hc & _) | (-> & _ & Hc)].
    + rewrite Hc. exact Hnew.
    + rewrite Hc. apply (KV (HA + 8) 4%nat (hs_closed h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H3].
  - destruct Hfo as [(-> & _ & He) | (-> & He & _)].
    + rewrite He. apply (KV (HA + 12) 4%nat (hs_eintr h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H4].
    + rewrite He. exact Hnew.
  - exact (sm_awr W mem mem' HA ASRC HGr H5).
  - destruct Hfo as [(_ & Hc & _) | (_ & _ & Hc)]; [rewrite Hc; right; reflexivity | rewrite Hc; exact H6].
  - destruct Hfo as [(_ & _ & He) | (_ & He & _)]; [rewrite He; exact H7 | rewrite He; right; reflexivity].
  - rewrite Eopen. exact H8.
  - rewrite Efd. exact H9.
  - rewrite Epend. apply (KAL (HA + 16)); [lia | cbn; lia | intros x Hx; lia | exact H10].
  - rewrite Eoff. apply (KV (HA + 32) 8%nat (hs_off h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H11].
  - rewrite Epart. apply (KV (HA + 40) 8%nat (hs_partial h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H12].
  - rewrite Enp. apply (KV (HA + 48) 8%nat (hs_npartial h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H13].
  - rewrite Eov. apply (KV (HA + 56) 4%nat (hs_overlong h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H14].
  - rewrite Epend, Eoff. exact H15.
  - rewrite Enp. exact H16.
  - rewrite Eov. exact H17.
  - rewrite Epart. exact H18.
  - rewrite Epjunk. exact H19.
  - rewrite Epart, Epjunk. apply (akept_garr8 W mem); [|exact H20].
    intros x Hx. unfold bzs in Hx. rewrite length_map, H19 in Hx. apply HBW.
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - unfold hs_W. rewrite Enp, Epjunk. exact H21.
  - rewrite Eexp. apply (KAL (HA + 64)); [lia | cbn; lia | intros x Hx; lia | exact H22].
  - rewrite Eheld. apply (KAL (HA + 80)); [lia | cbn; lia | intros x Hx; lia | exact H23].
  - unfold hs_blocks. rewrite Epend, Epart, Eexp, Eheld. exact H24.
Qed.

(* ---------------------------------------------------------------- the cut's facts across an arm's stores
   An arm stores to this frame's in.n cell [F+144, F+152) and to a list XG of program-global cells; a libc entry
   it calls with sp = F (the default arm's pthread_mutex_lock / _unlock, W_sites.v) may also change the ESTACK
   bytes of scratch below sp.  X = XS F XG. *)
Definition XS (F : Z) (XG : list (Z * Z)) : list (Z * Z) := (F - ESTACK, F) :: (F + 144, F + 152) :: XG.
Definition XGOK (XG : list (Z * Z)) : Prop := forall a, inFP XG a -> 0x9d000 <= a < 0x5fb000.
Lemma sm_rgv : rg_s fr_RG = 0x5d88e0 /\ rg_src fr_RG = 0x5d87c0 /\ rg_nsrc fr_RG = 0x5d87a0 /\
  rg_capsrc fr_RG = 0x5d8800 /\ rg_out fr_RG = 0x5d8b40 /\ rg_nout fr_RG = 0x5d88c0 /\ rg_capout fr_RG = 0x5d8b20 /\
  rg_send_max fr_RG = 0x5d8840 /\ rg_send_eintr fr_RG = 0x5d88a0 /\ rg_send_dead fr_RG = 0x5d8880 /\
  rg_gone fr_RG = 0x5d8860 /\ rg_client fr_RG = 0xa1fe0 /\ rg_client_broken fr_RG = 0x5d87e0 /\
  rg_lock fr_RG = 0x5d8ac0 /\ rg_wake fr_RG = 0xa1fa0.
Proof. repeat split. Qed.
(* arithmetic over fuzz_reply.asan's globals *)
Ltac sm_rgl :=
  let R := fresh "RV" in pose proof sm_rgv as R;
  unfold ASRC, AG_NFD, AG_THREAD_UP, AG_LISTEN in *;
  destruct R as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); lia.
Lemma sm_errno : 0 <= as_errno B /\ as_errno B + 4 <= alloc_ceiling.
Proof.
  pose proof (pal_env B TL) as ((HE0 & HE1) & _). pose proof sm_ceil_lo as Hac.
  unfold kLowMemEnd in HE1. lia.
Qed.
Lemma sm_xok : forall F XG, alloc_ceiling + 1024 + ESTACK <= F -> XGOK XG -> XOK (XS F XG).
Proof.
  intros F XG HF HXG a Ha. unfold XS in Ha. assert (HES : ESTACK = 4096) by reflexivity.
  apply inFP_cons in Ha as [Ha | Ha]; [right; lia|].
  apply inFP_cons in Ha as [Ha | Ha]; [right; lia | left; exact (HXG a Ha)].
Qed.
(* a byte outside the scratch, the in.n cell and the image's writable band is kept *)
Lemma sm_kept_off : forall (W : world segs) mem mem' F XG, XGOK XG -> KEPT W mem mem' (XS F XG) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (F - ESTACK <= a < F) -> ~ (F + 144 <= a < F + 152) ->
  ~ (0x9d000 <= a < 0x5fb000) -> abyte_kept W mem W mem' a.
Proof.
  intros W mem mem' F XG HXG HK a Ha H0 H1 H2. apply HK; [exact Ha|].
  intros Hin. unfold XS in Hin. apply inFP_cons in Hin as [Hin | Hin]; [exact (H0 Hin)|].
  apply inFP_cons in Hin as [Hin | Hin]; [exact (H1 Hin) | exact (H2 (HXG a Hin))].
Qed.
(* a byte outside the scratch, the in.n cell and the stored globals is kept *)
Lemma sm_kept_ng : forall (W : world segs) mem mem' F XG, KEPT W mem mem' (XS F XG) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (F - ESTACK <= a < F) -> ~ (F + 144 <= a < F + 152) -> ~ inFP XG a ->
  abyte_kept W mem W mem' a.
Proof.
  intros W mem mem' F XG HK a Ha H0 H1 H2. apply HK; [exact Ha|].
  intros Hin. unfold XS in Hin. apply inFP_cons in Hin as [Hin | Hin]; [exact (H0 Hin)|].
  apply inFP_cons in Hin as [Hin | Hin]; [exact (H1 Hin) | exact (H2 Hin)].
Qed.
(* a cell below the allocator's ceiling and apart from the stored globals is kept *)
Lemma sm_cell_kept : forall (W : world segs) mem mem' F XG lo n,
  KEPT W mem mem' (XS F XG) -> alloc_ceiling + ESTACK <= F -> 0 <= lo -> lo + n <= alloc_ceiling ->
  (forall a, lo <= a < lo + n -> ~ inFP XG a) ->
  forall a, lo <= a < lo + n -> abyte_kept W mem W mem' a.
Proof.
  intros W mem mem' F XG lo n HK HF H0 H1 Hd a Ha. pose proof sm_ceil_lo as Hac.
  assert (HES : ESTACK = 4096) by reflexivity.
  apply (sm_kept_ng W mem mem' F XG HK); [lia | lia | lia | exact (Hd a Ha)].
Qed.

(* the frame and the fake frame: no cell of them is the scratch, the in.n cell or in the image *)
Lemma sm_aframe_kept : forall cx full ly S (W : world segs) mem md mem' fpos XG,
  AR segs B ly S W mem md -> In (1, fpos) (frames S) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  XGOK XG -> KEPT W mem mem' (XS (lf_F cx) XG) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aframe_at cx full (frame_addr ly 1 fpos) W mem -> aframe_at cx full (frame_addr ly 1 fpos) W mem'.
Proof.
  intros cx full ly S W mem md mem' fpos XG HAR Hfin Hsp HXG HK HGr
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HXOK : XOK (XS (lf_F cx) XG)) by (apply sm_xok; [lia | exact HXG]).
  destruct (frames_bounds segs B LAWS ly S W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly 1 fpos / 8 /\ 8 * (frame_addr ly 1 fpos / 8) <= frame_addr ly 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KS : forall a, 0x5fb000 <= a < 2 ^ 64 -> ~ (lf_F cx - ESTACK <= a < lf_F cx) ->
      ~ (lf_F cx + 144 <= a < lf_F cx + 152) -> abyte_kept W mem W mem' a)
    by (intros a Ha H0 Hn; apply (sm_kept_off W mem mem' (lf_F cx) XG HXG HK); lia).
  assert (KF : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 -> abyte_kept W mem W mem' a)
    by (intros a Ha; exact (sm_frm_kept ly S W mem md mem' _ _ _ a HAR HXOK HK Hfin
          ltac:(change (fs_frame_bytes 1) with 128; lia))).
  assert (KV : forall a v, 0x5fb000 <= a -> a + 8 <= 2 ^ 64 ->
      ((lf_F cx <= a /\ a + 8 <= lf_F cx + 144) \/ lf_F cx + 152 <= a) ->
      sv8 W mem a v -> sv8 W mem' a v).
  { intros a v H0 H1 H2 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. apply KS; cbn in Hx; lia. }
  assert (KFV : forall o v, 0 <= o -> o + 8 <= 128 -> sv8 W mem (frame_addr ly 1 fpos + o) v ->
      sv8 W mem' (frame_addr ly 1 fpos + o) v).
  { intros o v H0 H1 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. apply KF. cbn in Hx. lia. }
  assert (KW : forall a n, awr W mem a n -> awr W mem' a n) by (intros a n Hw; exact (sm_awr W mem mem' a n HGr Hw)).
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  do 9 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | lia | assumption]|]).
    apply KV; [lia | lia | lia | assumption]. }
  split; [rewrite <- (Z.add_0_r (frame_addr ly 1 fpos)); apply KFV; [lia | lia | rewrite Z.add_0_r; exact A13]|].
  split; [apply KFV; [lia | lia | exact A14]|].
  split; [apply KFV; [lia | lia | exact A15]|].
  split; [exact (KW _ _ A16)|].
  split; [|exact (KW _ _ (proj2 A17))].
  apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply KS; unfold SB in *; lia.
Qed.
(* the fake frame's flag word (lcut's conjunct after aframe_at), kept like the fake frame's other bytes *)
Lemma sm_flag_kept : forall cx ly S (W : world segs) mem md mem' fpos XG,
  AR segs B ly S W mem md -> In (1, fpos) (frames S) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  XGOK XG -> KEPT W mem mem' (XS (lf_F cx) XG) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) -> sv8 W mem' (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos).
Proof.
  intros cx ly S W mem md mem' fpos XG HAR Hfin Hsp HXG HK HGr Hv.
  pose proof sm_ceil_lo as Hac.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (HXOK : XOK (XS (lf_F cx) XG)) by (apply sm_xok; [lia | exact HXG]).
  unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx.
  exact (sm_frm_kept ly S W mem md mem' _ _ _ x HAR HXOK HK Hfin ltac:(change (fs_frame_bytes 1) with 128; lia)).
Qed.

(* the input block *)
Lemma sm_ainput_kept : forall cx ly S (W : world segs) mem md mem' X,
  AR segs B ly S W mem md -> XOK X -> KEPT W mem mem' X ->
  Z.of_nat (length (c_pl cx)) = c_n cx -> ainput_at B cx ly S W mem -> ainput_at B cx ly S W mem'.
Proof.
  intros cx ly S W mem md mem' X HAR HX HK Hlen (I1 & I2). split; [exact I1|].
  apply (akept_garr8 W mem); [|exact I2]. intros x Hx. rewrite length_map, Hlen in Hx.
  destruct I1 as [(Hn & _) | (Hn & Hin)]; [lia|].
  apply (sm_blk_kept ly S W mem md mem' X (c_p cx) (c_n cx) x HAR HX HK Hin).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
Qed.

(* one of g_s[0..3] none of whose 96 bytes the arm stores to *)
Lemma sm_aslot_kept : forall ly S (W : world segs) mem md mem' F XG j o,
  AR segs B ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> XGOK XG -> KEPT W mem mem' (XS F XG) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') -> (j < 4)%nat ->
  (forall a, rg_s fr_RG + ASRC * Z.of_nat j <= a < rg_s fr_RG + ASRC * Z.of_nat j + ASRC -> ~ inFP XG a) ->
  aslot B ly S W mem j o -> aslot B ly S W mem' j o.
Proof.
  intros ly S W mem md mem' F XG j o HAR HF HXG HK HGr Hj Hd Hs.
  assert (HXOK : XOK (XS F XG)) by (apply sm_xok; [exact HF | exact HXG]).
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (KJ : forall a, rg_s fr_RG + ASRC * Z.of_nat j <= a < rg_s fr_RG + ASRC * Z.of_nat j + ASRC ->
      abyte_kept W mem W mem' a)
    by (intros a Ha; apply (sm_cell_kept W mem mem' F XG (rg_s fr_RG + ASRC * Z.of_nat j) ASRC HK);
        [lia | sm_rgl | sm_rgl | exact Hd | exact Ha]).
  unfold aslot in *. destruct o as [h|].
  - apply (asrc_at_kept B ly S W mem ly S W mem' _ h Hs).
    + apply (sm_akept_of W mem mem'). intros r Hr.
      exact (sm_asrc_fp_kept _ W mem mem' HXOK HK ly S md _ h HAR Hs (fun a Ha => KJ a Ha) r Hr).
    + exact (sm_asrc_blks_in W mem ly S _ h Hs).
  - destruct Hs as [G1 G2]. split.
    + apply (akept_garr8 W mem); [|exact G1]. intros x Hx.
      rewrite repeat_length, Z2Nat.id in Hx by (unfold ASRC; lia). exact (KJ x Hx).
    + apply (akept_awr W mem); [|exact G2]. exact KJ.
Qed.

(* the relay's globals and table *)
Lemma sm_arelay_kept : forall ly S (W : world segs) mem md mem' F XG G es,
  AR segs B ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> XGOK XG -> KEPT W mem mem' (XS F XG) ->
  (forall a, rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
     rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 -> ~ inFP XG a) ->
  arelay_at B fr_RG ly S W mem G es -> arelay_at B fr_RG ly S W mem' G es.
Proof.
  intros ly S W mem md mem' F XG G es HAR HF HXG HK Hd Hr.
  assert (HXOK : XOK (XS F XG)) by (apply sm_xok; [exact HF | exact HXG]).
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  apply (arelay_at_kept B fr_RG ly S W mem ly S W mem' G es Hr).
  - apply (sm_akept_of W mem mem'). intros r Hr'.
    assert (CK : forall lo n, 0 <= lo -> lo + n <= alloc_ceiling -> (forall a, lo <= a < lo + n -> ~ inFP XG a) ->
        sm_koff W mem mem' (lo, lo + n))
      by (intros lo n H0 H1 Hn a Ha; cbn [fst snd] in Ha;
          exact (sm_cell_kept W mem mem' F XG lo n HK ltac:(lia) H0 H1 Hn a Ha)).
    apply (sm_arelay_fp_kept _ W mem mem' HXOK HK fr_RG ly S md G es HAR Hr); [| | | exact Hr'];
      (apply CK; [sm_rgl | sm_rgl | intros y Hy; apply Hd; lia]).
  - exact (sm_arelay_blks_in W mem fr_RG ly S G es Hr).
Qed.

(* the controller's stream: its eight globals, errno's cell and the g_out block *)
Definition aout_glob (a : Z) : Prop :=
  (rg_send_max fr_RG <= a < rg_send_max fr_RG + 8) \/ (rg_nout fr_RG <= a < rg_nout fr_RG + 8) \/
  (rg_capout fr_RG <= a < rg_capout fr_RG + 8) \/ (rg_out fr_RG <= a < rg_out fr_RG + 8) \/
  (rg_client fr_RG <= a < rg_client fr_RG + 4) \/ (rg_client_broken fr_RG <= a < rg_client_broken fr_RG + 1) \/
  (rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1) \/ (rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1) \/
  (as_errno B <= a < as_errno B + 4).
Lemma sm_aout_kept : forall ly S (W : world segs) mem md mem' F XG c O mx no cap out,
  AR segs B ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> XGOK XG -> KEPT W mem mem' (XS F XG) ->
  (forall a, aout_glob a -> ~ inFP XG a) ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> aout_at B fr_RG ly S W mem' c O mx no cap out.
Proof.
  intros ly S W mem md mem' F XG c O mx no cap out HAR HF HXG HK Hd Ho.
  assert (HXOK : XOK (XS F XG)) by (apply sm_xok; [exact HF | exact HXG]).
  pose proof sm_ceil_lo as Hac. pose proof sm_errno as (HE0 & HE1). assert (HES : ESTACK = 4096) by reflexivity.
  assert (CK : forall a, aout_glob a -> abyte_kept W mem W mem' a).
  { intros a Ha. pose proof (Hd a Ha) as Hn. apply (sm_kept_ng W mem mem' F XG HK); [| | | exact Hn];
      unfold aout_glob in Ha; sm_rgl. }
  pose proof Ho as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hblk).
  apply (aout_at_kept B fr_RG ly S W mem ly S W mem' c O mx no cap out Ho).
  - intros r Hr a Ha. unfold aout_fp in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Ha;
      try (apply CK; unfold aout_glob; lia).
    destruct (cap =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    cbn [fst snd] in Ha.
    destruct Hblk as [(Hc & _) | (Hcp & Hno & Hin & _)]; [lia|].
    apply (sm_blk_kept ly S W mem md mem' (XS F XG) out cap a HAR HXOK HK Hin).
    pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
  - intros b Hb. unfold aout_blks in Hb. destruct (cap =? 0) eqn:Ec; [destruct Hb|].
    apply Z.eqb_neq in Ec. destruct Hb as [<- | []].
    destruct Hblk as [(Hc & _) | (Hcp & Hno & Hin & _)]; [lia | exact Hin].
Qed.

(* the model after arm 3 / 6: slot i's flag word is 1, everything else as it was *)
Lemma sm_amodel_fl : forall ly S (W : world segs) mem md mem' F m i h (upd : hsrc -> hsrc) fo kx,
  AR segs B ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F ->
  KEPT W mem mem' (XS F [(rg_s fr_RG + ASRC * Z.of_nat i + fo, rg_s fr_RG + ASRC * Z.of_nat i + fo + 4)]) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  amodel_at B ly S W mem m -> (i < 4)%nat -> nth i (lm_hs m) None = Some h ->
  same_but_flags h (upd h) ->
  ((fo = 8 /\ hs_closed (upd h) = 1 /\ hs_eintr (upd h) = hs_eintr h) \/
   (fo = 12 /\ hs_eintr (upd h) = 1 /\ hs_closed (upd h) = hs_closed h)) ->
  val_mem segs (arm W mem') (rg_s fr_RG + ASRC * Z.of_nat i + fo) 4 1 ->
  amodel_at B ly S W mem' (LM kx (upd_hs i upd (lm_hs m)) (lm_G m) (lm_es m) (lm_c m) (lm_O m)
    (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m)).
Proof.
  intros ly S W mem md mem' F m i h upd fo kx HAR HF HK HGr HM Hi Hnth Hsf Hfl Hnew.
  assert (Hfo : fo = 8 \/ fo = 12) by (destruct Hfl as [(-> & _) | (-> & _)]; [left | right]; reflexivity).
  pose proof sm_ceil_lo as Hac. pose proof sm_errno as (HE0 & HE1). assert (HES : ESTACK = 4096) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat i) in *.
  set (XG := [(HA + fo, HA + fo + 4)]) in *.
  assert (NX : forall a, ~ (HA + fo <= a < HA + fo + 4) -> ~ inFP XG a).
  { intros a Hn Ha. unfold XG in Ha. apply inFP_cons in Ha as [Ha | Ha]; [exact (Hn Ha) | exact (inFP_nil a Ha)]. }
  assert (HXG : XGOK XG).
  { intros a Ha. unfold XG in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold HA in Ha; sm_rgl | destruct (inFP_nil a Ha)]. }
  assert (HXOK : XOK (XS F XG)) by (apply sm_xok; [exact HF | exact HXG]).
  assert (CK : forall lo n, 0 <= lo -> lo + n <= alloc_ceiling ->
      (forall a, lo <= a < lo + n -> ~ (HA + fo <= a < HA + fo + 4)) ->
      forall a, lo <= a < lo + n -> abyte_kept W mem W mem' a).
  { intros lo n H0 H1 Hd. apply (sm_cell_kept W mem mem' F XG lo n HK); [lia | lia | lia |].
    intros a Ha. exact (NX a (Hd a Ha)). }
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite upd_hs_length; exact M1|].
  split.
  { intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hne].
    - rewrite (upd_hs_nth_same i upd (lm_hs m) h Hnth). unfold aslot.
      pose proof (M2 i Hi) as Hs. unfold aslot in Hs. rewrite Hnth in Hs.
      apply (sm_slot_store ly S W mem md mem' (XS F XG) HA h (upd h) fo HAR HXOK HK HGr Hs Hsf Hfl).
      + intros a Ha Hn Hin. unfold XS in Hin. apply inFP_cons in Hin as [Hin | Hin]; [unfold HA in Ha; sm_rgl|].
        apply inFP_cons in Hin as [Hin | Hin]; [unfold HA in Ha; sm_rgl|].
        exact (NX a Hn Hin).
      + unfold HA; sm_rgl.
      + unfold HA; sm_rgl.
      + exact Hnew.
    - rewrite (upd_hs_nth_other i upd (lm_hs m) j Hne).
      apply (sm_aslot_kept ly S W mem md mem' F XG j _ HAR HF HXG HK HGr Hj); [|exact (M2 j Hj)].
      intros a Ha. apply NX. unfold HA. sm_rgl. }
  split.
  { apply (sm_arelay_kept ly S W mem md mem' F XG (lm_G m) (lm_es m) HAR HF HXG HK); [|exact M3].
    intros a Ha. apply NX. unfold HA. sm_rgl. }
  split.
  { apply (sm_aout_kept ly S W mem md mem' F XG _ _ _ _ _ _ HAR HF HXG HK); [|exact M4].
    intros a Ha Hin. unfold XG in Hin. apply inFP_cons in Hin as [Hin | Hin]; [|exact (inFP_nil a Hin)].
    pose proof HERRHI as He.
    unfold aout_glob in Ha. unfold HA in Hin. sm_rgl. }
  split.
  { apply (agone_at_kept fr_RG W mem W mem' _ M5). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_gone fr_RG) 1); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | exact Ha]. }
  split.
  { apply (alock_at_kept fr_RG W mem W mem' _ M6). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_lock fr_RG) 12); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | exact Ha]. }
  split.
  { apply (awake_at_kept fr_RG W mem W mem' M7). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_wake fr_RG + 4) 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply (CK AG_THREAD_UP 1); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  split.
  { destruct M12 as (lst & M12). exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx.
    apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia].
Qed.

(* the model's blocks do not change when only a source's flags do *)
Lemma sm_sep_fl : forall cx m ly S i (upd : hsrc -> hsrc) kx O,
  (forall h, asrc_blks (upd h) = asrc_blks h) -> ablocks_sep B fr_FP cx m ly S ->
  ablocks_sep B fr_FP cx (LM kx (upd_hs i upd (lm_hs m)) (lm_G m) (lm_es m) (lm_c m) O
    (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m)) ly S.
Proof.
  intros cx m ly S i upd kx O Hb Hs. unfold ablocks_sep, model_blks in *.
  cbn [lm_hs lm_G lm_es lm_cap lm_out]. rewrite (upd_hs_blks i upd (lm_hs m) Hb). exact Hs.
Qed.

Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
Definition SMspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* ---------------------------------------------------------------- arms 3 and 6: the run to the latch *)
(* the registers the run does not write *)
Definition sm_fl_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29]%bv.
(* the registers arm 8's run does not write (it writes a0, a1, s6 and t4) *)
Definition sm_mx_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28]%bv.
(* the registers arm 9's runs and calls keep (the calls clobber t3 / t4; s4 is reloaded with 10) *)
Definition sm_df_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 23; 24; 25; 26; 27]%bv.
(* a concrete register is in a concrete list (no normalisation of the bv literals' proofs) *)
Ltac sm_in := cbn [In jt_kept sm_fl_kept sm_mx_kept sm_df_kept]; repeat (first [left; reflexivity | right]).
(* what the run gives: the latch's state, the journal, the two stores (in.n := t4, the flag word := 1), every
   other byte kept, the registers the run does not write, and s6 = t3 *)
Definition sm_fl_post (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (kk F HA fo N29 : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem' md' kk /\
    KEPT W mem mem' (XS F [(HA + fo, HA + fo + 4)]) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 N29 /\ val_mem segs (arm W mem') (HA + fo) 4 1 /\
    (forall r, In r sm_fl_kept -> getr regs' r = getr regs r) /\ getr regs' 22 = getr regs 28.
Lemma sm_fl_run : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 (W0 : world segs) mem0 md0 own ly S kk
    F HA fo N29 pc,
  (fo = 8 /\ pc = AF_arm_close) \/ (fo = 12 /\ pc = AF_arm_eintr) ->
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md kk ->
  getr regs 7 = w64 1 -> getr regs 9 = w64 F -> getr regs 21 = w64 HA -> getr regs 26 = w64 SB ->
  getr regs 29 = w64 N29 -> 0 <= N29 < 2 ^ 64 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  rg_s fr_RG <= HA <= rg_s fr_RG + 3 * ASRC -> HA mod 32 = 0 ->
  sp0 - STK <= F + 144 -> F + 152 <= sp0 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  (forall a, HA + fo <= a < HA + fo + 4 -> writable_at segs (arm W mem) a) ->
  azs B HA ASRC ->
  SRr segs W (cfg_at segs (fr_B0 + pc) regs mem md)
    (sm_fl_post W regs mem STK sp0 FP ly0 S0 W0 mem0 md0 own ly S kk F HA fo N29).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 W0 mem0 md0 own ly S kk F HA fo N29 pc Hcase HJ H7 H9 H21 H26 H29 HN29
    HF1 HF2 HH1 HH2 Hs1 Hs2 HW1 HW2 HZ.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HAR : AR segs B ly S W mem md)
    by (exact (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
  assert (HRS : rg_s fr_RG = 6129888) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (Hfo : fo = 8 \/ fo = 12) by (destruct Hcase as [(-> & _) | (-> & _)]; [left | right]; reflexivity).
  destruct (sm_fl_entry W regs mem ly S md F HA fo pc HAR H7 H9 H21 H26 HF1 HF2 ltac:(lia) HH2 Hfo HW1 HW2 HZ)
    as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (@nil word)))) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) (Eimg (Ereg regs (@nil word))))
    by (split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs (@nil word))) m = getr regs rr)
    by (intros m rr Hm; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E9 : ew (Eimg (Ereg regs (@nil word))) 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E21 : ew (Eimg (Ereg regs (@nil word))) 21 = w64 HA) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
  assert (E28 : ew (Eimg (Ereg regs (@nil word))) 28 = getr regs 28) by exact (EE 28%nat 28%bv eq_refl).
  assert (E29 : ew (Eimg (Ereg regs (@nil word))) 29 = w64 N29) by (rewrite (EE 29%nat 29%bv eq_refl); exact H29).
  assert (E9b : base_val (Eimg (Ereg regs (@nil word))) (Some 9%nat) = F)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  assert (E21b : base_val (Eimg (Ereg regs (@nil word))) (Some 21%nat) = HA)
    by (cbn [base_val]; rewrite E21; apply unsigned_lit_small; rewrite HRS, HAS in HH1; lia).
  clear EE.
  set (E := Eimg (Ereg regs (@nil word))) in *. clearbody E.
  unfold cfg_at. change (w64 (fr_B0 + pc)) with (Z_to_bv 64 (BASE + pc)).
  destruct Hcase as [(-> & ->) | (-> & ->)].
  all: paj_run_to_tok RUNTO HS HJ SHOK SMspan AF_LLVM_latch.
  1,3: apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha; rewrite E9b in Ha;
      left; split; [left; lia | lia]
    | apply awr_ok_x_cons_g;
      [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha; rewrite E21b in Ha;
        apply HGs; rewrite HAS; lia
      | apply awr_ok_x_nil ] ].
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  all: pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (@nil word) sm_fl_kept HS HAE2
    ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: prreg HS (22%bv : bv 5) Q22.
  all: rewrite ?ew_ewset_other in Q22 by lia.
  all: rewrite E28 in Q22.
  all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
  all: pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
  all: cbn [ms_mem restrict] in RG0, RG1.
  all: assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 N29)
    by (apply (field_of_region E _ 9%nat F _ _ _ _ _ 144 8%N (SOff 29 0) N29 RG0);
        [ rewrite E9; apply unsigned_lit_small; lia
        | left; reflexivity
        | cbn [sv_denot]; rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | zside | zside ]).
  all: lazymatch type of RG1 with region_ok _ _ _ (YP09.mkRegion _ ?o _ _ _ _) =>
    assert (VHA : val_mem segs (arm W (ms_mem ms)) (HA + o) 4 1)
      by (apply (field_of_region E _ 21%nat HA _ _ _ _ _ o 4%N (SLit 1) 1 RG1);
          [ rewrite E21; apply unsigned_lit_small; rewrite HRS, HAS in HH1; lia
          | left; reflexivity | reflexivity | zside | zside ]) end.
  all: pmkst HS.
  all: apply SRr_ret.
  all: split; [reflexivity|].
  all: exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
  all: split; [reflexivity|].
  all: split; [exact HJ|].
  all: split; [intros a Ha Hn; split;
    [ apply (aview_kept_out _ _ _ _ _ HFr a Ha); intros (r & Hin & Hr); cbn [ss_mem sm_fl_regions In] in Hin;
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
      [ rewrite E9b in Hr; apply Hn; unfold XS; apply inFP_cons; right; apply inFP_cons; left; lia
      | rewrite E21b in Hr; apply Hn; unfold XS; apply inFP_cons; right; apply inFP_cons; right;
        apply inFP_cons; left; lia ]
    | exact (sm_wkeep W mem (ms_mem ms) a HG0) ] |].
  all: split; [exact HG0|].
  all: split; [exact V144|].
  all: split; [exact VHA|].
  all: split; [exact KR|].
  all: exact Q22.
Qed.

(* ---------------------------------------------------------------- the shared close/eintr walk *)
Lemma sm_fl_walk : forall (ii fo : Z) (upd : hsrc -> hsrc) (mk : lfcx -> lmod -> nat -> lmod) cx t W c,
  (ii = 3 /\ fo = 8) \/ (ii = 6 /\ fo = 12) ->
  (forall h, same_but_flags h (upd h)) ->
  (forall h, (fo = 8 /\ hs_closed (upd h) = 1 /\ hs_eintr (upd h) = hs_eintr h) \/
             (fo = 12 /\ hs_eintr (upd h) = 1 /\ hs_closed (upd h) = hs_closed h)) ->
  (forall m0 i0, mk cx m0 i0 = LM (sm_kn cx m0) (upd_hs i0 upd (lm_hs m0)) (lm_G m0) (lm_es m0)
      (lm_c m0) [] (lm_mx m0) (lm_cap m0) (lm_out m0) (lm_gn m0) (lm_nfd m0)) ->
  (forall m0 i0, RINV cx t m0 ->
     pick (lm_hs m0) (if lm_k m0 + 1 <? c_n cx then in_byte cx (lm_k m0 + 1) else 0) = Some i0 ->
     RINV cx (t + 1) (mk cx m0 i0)) ->
  (forall m0 i0 ly0 S0, LS cx t m0 ly0 S0 ->
     pick (lm_hs m0) (if lm_k m0 + 1 <? c_n cx then in_byte cx (lm_k m0 + 1) else 0) = Some i0 ->
     LS cx (t + 1) (mk cx m0 i0) ly0 S0) ->
  (forall h, asrc_blks (upd h) = asrc_blks h) ->
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_A B G_fr fr_FP LS RINV ii cx t W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros ii fo upd mk cx t W c Hcase Hsf Hfl Hmk Hri Hls Hblks HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep & HLS & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD6 & HD7 & HD27 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hiirange : 0 <= ii <= 9) by (destruct Hcase as [[-> _]|[-> _]]; lia).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = ii).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk3 : picks ii = true) by (destruct Hcase as [[-> _]|[-> _]]; reflexivity).
  rewrite Hpk3 in Hpick. cbv zeta in Hpick. destruct Hpick as (HD28 & HD29 & Hpk).
  destruct Hpk as [(i & Hpicki & HD21) | (Hbad & _)];
    [| exfalso; destruct Hcase as [[Hii _]|[Hii _]]; rewrite Hii in Hbad; discriminate Hbad].
  destruct (sm_pick (lm_hs m) _ i Hpicki) as (Hilen & hsome & Hnthi).
  pose proof Hmodel as (Hlen4 & Hslots & _).
  rewrite Hlen4 in Hilen.
  pose proof (Hslots i Hilen) as Haslot. unfold aslot in Haslot. rewrite Hnthi in Haslot.
  assert (HAR : AR segs B ly3 S3 W mem md)
    by (exact (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (HAc := rg_s fr_RG + ASRC * Z.of_nat i) in *.
  assert (HRS : rg_s fr_RG = 6129888) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (Hi4 : (i < 4)%nat) by lia.
  assert (HHbound : rg_s fr_RG <= HAc <= rg_s fr_RG + 3 * ASRC) by (unfold HAc; rewrite HAS; lia).
  assert (HHmod : HAc mod 32 = 0)
    by (unfold HAc; rewrite HRS, HAS; replace (6129888 + 96 * Z.of_nat i) with ((191559 + 3 * Z.of_nat i) * 32) by lia; apply Z_mod_mult).
  assert (Hfo : fo = 8 \/ fo = 12) by (destruct Hcase as [[_ ->]|[_ ->]]; [left|right]; reflexivity).
  (* the registers: regs agrees with regsD outside a0 / a1 *)
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  assert (Hr7 : getr regs 7 = w64 1) by (rewrite (KD 7%bv ltac:(sm_in)); exact HD7).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr26 : getr regs 26 = w64 SB) by (rewrite (KD 26%bv ltac:(sm_in)); exact C26).
  assert (Hr21 : getr regs 21 = w64 HAc) by (rewrite (KD 21%bv ltac:(sm_in)); exact HD21).
  set (k1 := if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) in *.
  assert (Hk1 : lm_k m + 1 <= k1 <= c_n cx)
    by (unfold k1; destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek]; lia).
  assert (Hn26 : c_n cx < 2 ^ 26)
    by (pose proof Hpre as (_ & _ & _ & _ & Hpn & _); destruct Hpn as [(H0 & _) | (H0 & _)]; lia).
  assert (Hr29 : getr regs 29 = w64 (c_n cx - k1)) by (rewrite (KD 29%bv ltac:(sm_in)); exact HD29).
  assert (Hr28 : getr regs 28 = w64 (c_p cx + k1)) by (rewrite (KD 28%bv ltac:(sm_in)); exact HD28).
  pose proof Hframe as (_ & Hawr & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Haslot as (_ & _ & _ & _ & Hs5 & _).
  assert (HW2 : forall a, HAc + fo <= a < HAc + fo + 4 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (HAc + (a - HAc)) by lia. apply Hs5. unfold ASRC; lia. }
  assert (HZslot : azs B HAc ASRC) by (apply (azs_sub (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | unfold HAc; lia]).
  assert (Hpcs : (fo = 8 /\ fr_arm ii = AF_arm_close) \/ (fo = 12 /\ fr_arm ii = AF_arm_eintr))
    by (destruct Hcase as [(-> & ->) | (-> & ->)]; [left | right]; split; reflexivity).
  rewrite Hc.
  eapply SRr_mono.
  { exact (sm_fl_run W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 kk (lf_F cx) HAc fo (c_n cx - k1) (fr_arm ii) Hpcs HJ Hr7 Hr9 Hr21 Hr26 Hr29
      ltac:(lia) HFbound HFmod HHbound HHmod ltac:(lia) ltac:(lia) HW1 HW2 HZslot). }
  intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & KP & HGr & V144 & VHA & KR & Q22).
  set (XG := [(HAc + fo, HAc + fo + 4)]) in *.
  assert (HXG : XGOK XG).
  { intros a Ha. unfold XG in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold HAc in Ha; sm_rgl | destruct (inFP_nil a Ha)]. }
  assert (HXOK : XOK (XS (lf_F cx) XG)) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_fl_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, kk, (mk cx m i), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept cx true ly3 S3 W mem md mem' fpos XG HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept cx ly3 S3 W mem md mem' fpos XG HAR Hfin Hsp0 HXG KP HGr Hflag)|].
  split.
  { rewrite Hmk.
    pose proof (sm_amodel_fl ly3 S3 W mem md mem' (lf_F cx) m i hsome upd fo (sm_kn cx m) HAR ltac:(lia) KP HGr
      Hmodel Hi4 Hnthi (Hsf hsome) (Hfl hsome) VHA) as HM2.
    rewrite HO in HM2. exact HM2. }
  split; [exact (sm_ainput_kept cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [rewrite Hmk; apply sm_sep_fl; [exact Hblks | exact Hsep]|].
  split; [exact (Hls m i ly3 S3 HLS Hpicki)|].
  split; [exact (Hri m i HRINV Hpicki)|].
  unfold lregs_K, lregs_common. rewrite Hmk. cbn [lm_k].
  assert (Hkn : sm_kn cx m = k1) by reflexivity. rewrite Hkn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [rewrite (KK 20%bv ltac:(sm_in) ltac:(sm_in)); exact C20|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact C25|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact HD27|].
  split; [exact Htb|].
  split; [rewrite Q22, Hr28; reflexivity|].
  split; [unfold sv8; exact V144|].
  lia.
Qed.

(* ---------------------------------------------------------------- ARM_close and ARM_eintr (_cut.v :578 / :581) *)
Theorem lf_arm_close : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_A B G_fr fr_FP LS RINV 3 cx t W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB HA.
  exact (sm_fl_walk 3 8 upd_closed sm_close cx t W c (or_introl (conj eq_refl eq_refl)) same_but_flags_closed
    (fun h => or_introl (conj eq_refl (conj eq_refl eq_refl))) (fun m0 i0 => eq_refl)
    (fun m0 i0 H Hp => RI_close cx t m0 i0 H Hp) (fun m0 i0 ly0 S0 H Hp => LS_close cx t m0 i0 ly0 S0 H Hp)
    upd_closed_blks HB HA).
Qed.
Theorem lf_arm_eintr : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_A B G_fr fr_FP LS RINV 6 cx t W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB HA.
  exact (sm_fl_walk 6 12 upd_eintr sm_eintr cx t W c (or_intror (conj eq_refl eq_refl)) same_but_flags_eintr
    (fun h => or_intror (conj eq_refl (conj eq_refl eq_refl))) (fun m0 i0 => eq_refl)
    (fun m0 i0 H Hp => RI_eintr cx t m0 i0 H Hp) (fun m0 i0 ly0 S0 H Hp => LS_eintr cx t m0 i0 ly0 S0 H Hp)
    upd_eintr_blks HB HA).
Qed.

(* ---------------------------------------------------------------- arm 8: g_send_max := in.p[0], g_send_eintr := 1 *)
(* 0x84638 `beqz t4,0x84984`.  Input left: the shadow check of in.p[0] (t3), `lbu a0,0(t3); addi s6,t3,1;
   addi t4,t4,-1; sd t4,144(s1); j 0x84990`.  None: 0x84984 `mv s6,t3; sd zero,144(s1); li a0,0`.  Then 0x84990
   `ld a1,72(s1); sd a0,1616(a1)` (g_send_max, through the frame's copy 0x5d81f0 of the auipc value A_HI 70) and
   `ld a0,56(s1); sb t2,1684(a0)` (g_send_eintr, through 0x5d820c = A_HI 73), `j 0x84490`. *)
Lemma sm_inFP2 : forall lo1 hi1 lo2 hi2 a, inFP [(lo1, hi1); (lo2, hi2)] a -> lo1 <= a < hi1 \/ lo2 <= a < hi2.
Proof.
  intros lo1 hi1 lo2 hi2 a H. apply inFP_cons in H as [H | H]; [left; exact H|].
  apply inFP_cons in H as [H | H]; [right; exact H | destruct (inFP_nil a H)].
Qed.
Definition sm_mx_XG : list (Z * Z) :=
  [(rg_send_max fr_RG, rg_send_max fr_RG + 8); (rg_send_eintr fr_RG, rg_send_eintr fr_RG + 1)].
Lemma sm_mx_xgok : XGOK sm_mx_XG.
Proof. intros a Ha. apply sm_inFP2 in Ha. sm_rgl. Qed.
Lemma sm_in_byte : forall (cx : lfcx) (m : word -> option byte) i,
  garr8 segs m (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  0 <= i < Z.of_nat (length (c_pl cx)) ->
  val_mem segs m (c_p cx + i) 1 (in_byte cx i) /\ 0 <= in_byte cx i < 256.
Proof.
  intros cx m i Hg Hi. unfold in_byte.
  destruct (Hg (Z.to_nat i) ltac:(rewrite length_map; lia)) as [Hv Hr].
  rewrite Z2Nat.id in Hv by lia.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv, Hr by (rewrite length_map; lia).
  rewrite map_nth in Hv, Hr. split; [exact Hv | exact Hr].
Qed.
Lemma sm_in_byte_rng : forall cx i, 0 <= in_byte cx i < 256.
Proof.
  intros cx i. unfold in_byte.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) (c_pl cx) (Z_to_bv 8 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.

(* the controller's stream after the arm: g_send_max = u, g_send_eintr = 1, everything else as it was *)
Ltac sm_kv KV H :=
  apply KV; [intros x Hx; cbn in Hx; unfold aout_glob; sm_rgl | intros x Hx; cbn in Hx; sm_rgl
            | intros x Hx; cbn in Hx; sm_rgl | exact H].
Lemma sm_aout_mx : forall ly S (W : world segs) mem md mem' F c O mx no cap out u,
  AR segs B ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> KEPT W mem mem' (XS F sm_mx_XG) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> 0 <= u <= 255 ->
  val_mem segs (arm W mem') (rg_send_max fr_RG) 8 u -> val_mem segs (arm W mem') (rg_send_eintr fr_RG) 1 1 ->
  aout_at B fr_RG ly S W mem' (CTL (ct_cl c) (ct_br c) (ct_dd c) 1 (ct_ev c)) O u no cap out.
Proof.
  intros ly S W mem md mem' F c O mx no cap out u HAR HF HK HGr Ho Hu Vmx Vei.
  assert (HXOK : XOK (XS F sm_mx_XG)) by (apply sm_xok; [exact HF | exact sm_mx_xgok]).
  pose proof sm_ceil_lo as Hac. pose proof sm_errno as (HE0 & HE1). pose proof HERRHI as HEH.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (CK : forall a, aout_glob a -> ~ (rg_send_max fr_RG <= a < rg_send_max fr_RG + 8) ->
      ~ (rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1) -> abyte_kept W mem W mem' a).
  { intros a Ha H1 H2. apply (sm_kept_ng W mem mem' F sm_mx_XG HK);
      [unfold aout_glob in Ha; sm_rgl | unfold aout_glob in Ha; sm_rgl | unfold aout_glob in Ha; sm_rgl |].
    intros Hin. apply sm_inFP2 in Hin. destruct Hin as [Hin | Hin]; [exact (H1 Hin) | exact (H2 Hin)]. }
  assert (KV : forall a n v, (forall x, a <= x < a + Z.of_nat n -> aout_glob x) ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (rg_send_max fr_RG <= x < rg_send_max fr_RG + 8)) ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (rg_send_eintr fr_RG <= x < rg_send_eintr fr_RG + 1)) ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v).
  { intros a n v H1 H2 H3 Hv. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. apply CK; [exact (H1 x Hx) | exact (H2 x Hx) | exact (H3 x Hx)]. }
  destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 &
    O19 & O20 & O21 & O22 & O23 & O24 & O25 & O26).
  unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [exact Vmx|]. split; [exact (sm_awr W mem mem' _ _ HGr O2)|].
  split; [sm_kv KV O3|]. split; [exact (sm_awr W mem mem' _ _ HGr O4)|].
  split; [sm_kv KV O5|]. split; [exact (sm_awr W mem mem' _ _ HGr O6)|].
  split; [sm_kv KV O7|]. split; [exact (sm_awr W mem mem' _ _ HGr O8)|].
  split; [sm_kv KV O9|]. split; [exact (sm_awr W mem mem' _ _ HGr O10)|].
  split; [sm_kv KV O11|]. split; [exact (sm_awr W mem mem' _ _ HGr O12)|].
  split; [sm_kv KV O13|]. split; [exact (sm_awr W mem mem' _ _ HGr O14)|].
  split; [exact Vei|]. split; [exact (sm_awr W mem mem' _ _ HGr O16)|].
  split; [sm_kv KV O17|]. split; [exact (sm_awr W mem mem' _ _ HGr O18)|].
  split; [exact O19|]. split; [exact O20|]. split; [exact O21|]. split; [exact O22|].
  split; [right; reflexivity|]. split; [lia|]. split; [exact O25|].
  destruct O26 as [O26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact O26 | right].
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|]. exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply (sm_blk_kept ly S W mem md mem' (XS F sm_mx_XG) out cap x HAR HXOK HK Hin).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

(* the model after arm 8: the stream's g_send_max and g_send_eintr, the cursor; everything else as it was *)
Lemma sm_amodel_mx : forall ly S (W : world segs) mem md mem' F cx m u,
  AR segs B ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F ->
  KEPT W mem mem' (XS F sm_mx_XG) -> mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  amodel_at B ly S W mem m -> lm_O m = [] -> 0 <= u <= 255 ->
  val_mem segs (arm W mem') (rg_send_max fr_RG) 8 u -> val_mem segs (arm W mem') (rg_send_eintr fr_RG) 1 1 ->
  amodel_at B ly S W mem' (sm_sendmax cx m u).
Proof.
  intros ly S W mem md mem' F cx m u HAR HF HK HGr HM HO Hu Vmx Vei.
  pose proof sm_ceil_lo as Hac. pose proof sm_mx_xgok as HXG.
  assert (NX : forall lo n, (forall a, lo <= a < lo + n -> ~ (rg_send_max fr_RG <= a < rg_send_max fr_RG + 8) /\
      ~ (rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1)) -> forall a, lo <= a < lo + n -> ~ inFP sm_mx_XG a).
  { intros lo n Hd a Ha Hin. apply sm_inFP2 in Hin. destruct (Hd a Ha) as [N1 N2].
    destruct Hin as [Hin | Hin]; [exact (N1 Hin) | exact (N2 Hin)]. }
  assert (CK : forall lo n, 0 <= lo -> lo + n <= alloc_ceiling ->
      (forall a, lo <= a < lo + n -> ~ (rg_send_max fr_RG <= a < rg_send_max fr_RG + 8) /\
        ~ (rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1)) ->
      forall a, lo <= a < lo + n -> abyte_kept W mem W mem' a).
  { intros lo n H0 H1 Hd. apply (sm_cell_kept W mem mem' F sm_mx_XG lo n HK); [lia | lia | lia | exact (NX lo n Hd)]. }
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  unfold amodel_at, sm_sendmax. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [exact M1|].
  split.
  { intros j Hj. apply (sm_aslot_kept ly S W mem md mem' F sm_mx_XG j _ HAR HF HXG HK HGr Hj); [|exact (M2 j Hj)].
    apply NX. intros a Ha. split; sm_rgl. }
  split.
  { apply (sm_arelay_kept ly S W mem md mem' F sm_mx_XG (lm_G m) (lm_es m) HAR HF HXG HK); [|exact M3].
    intros a Ha Hin. apply sm_inFP2 in Hin. sm_rgl. }
  split.
  { rewrite HO in M4. exact (sm_aout_mx ly S W mem md mem' F _ _ _ _ _ _ u HAR HF HK HGr M4 Hu Vmx Vei). }
  split.
  { apply (agone_at_kept fr_RG W mem W mem' _ M5). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_gone fr_RG) 1); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | exact Ha]. }
  split.
  { apply (alock_at_kept fr_RG W mem W mem' _ M6). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_lock fr_RG) 12); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | exact Ha]. }
  split.
  { apply (awake_at_kept fr_RG W mem W mem' M7). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_wake fr_RG + 4) 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply (CK AG_THREAD_UP 1); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  split.
  { destruct M12 as (lst & M12). exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx.
    apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia].
Qed.

(* the entry state: the in.n cell (written), the frame's two address copies, g_send_max and g_send_eintr through
   them (written), and, with input left, the byte in.p[0] = atom 32 with its shadow entry *)
Lemma sm_mx_vals : VAL (A_HI 70) = 0x5d81f0 /\ VAL (A_HI 73) = 0x5d820c.
Proof. vm_compute. split; reflexivity. Qed.
Definition sm_mx_rfr : YP09.region := YP09.mkRegion (Some 9%nat) 56 80 0 0
  [YP09.mkChunk 56 (CVal 8 (SOff (A_HI 73) 0)); YP09.mkChunk 72 (CVal 8 (SOff (A_HI 70) 0))].
Definition sm_mx_rb : YP09.region := YP09.mkRegion (Some 28%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition sm_mx_regions (more : bool) : smem :=
  [ YP09.mkRegion (Some 9%nat) 144 152 144 152 []; sm_mx_rfr;
    YP09.mkRegion (Some (A_HI 70)) 1616 1624 1616 1624 []; YP09.mkRegion (Some (A_HI 73)) 1684 1685 1684 1685 [] ]
  ++ (if more then [sm_mx_rb] else []).
(* the two image atoms the stores go through carry their values as facts (the window check needs a range) *)
Definition sm_mx_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (26%nat, mkAF SB SB 0); (28%nat, mkAF 4096 (2 ^ 47 - 16) 0);
            (32%nat, mkAF 0 255 0); (A_HI 70, mkAF 0x5d81f0 0x5d81f0 0); (A_HI 73, mkAF 0x5d820c 0x5d820c 0) ] [] [].
Definition sm_mx_SH (more : bool) : list shent := if more then [mkSHE 28 0 1] else [].
Definition sm_x1 (b : Z) : list word := map (Z_to_bv 64) [b].

Lemma sm_mx_entry : forall (W : world segs) regs mem (more : bool) F P1 kb,
  getr regs 7 = w64 1 -> getr regs 9 = w64 F -> getr regs 26 = w64 SB -> getr regs 28 = w64 P1 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 ->
  (more = true -> P1 + 1 <= 0x10000 \/ 0x5fb000 <= P1) ->
  (more = true -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (more = true -> P1 + 1 <= F) ->
  (more = true -> val_mem segs (arm W mem) P1 1 kb) ->
  (more = true -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 56) 0x5d820c -> sv8 W mem (F + 72) 0x5d81f0 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  awr W mem (rg_send_max fr_RG) 8 -> awr W mem (rg_send_eintr fr_RG) 1 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (sm_x1 kb))) (mkSS AF_arm_sendmax sm_fl_sr (sm_mx_regions more) None sm_mx_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_sendmax)) mem (seg_rom segs)))
  /\ sh_ok segs sm_Bx (sm_mx_SH more) (Eimg (Ereg regs (sm_x1 kb))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem more F P1 kb H7 H9 H26 H28 HF1 HF2 HP Hkb HPi HPa HPc MB RA M56 M72 HW1 HWmx HWei.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (sm_x1 kb))).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E26 : ew E 26 = w64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
  assert (E28 : ew E 28 = w64 P1) by (rewrite (EE 28%nat 28%bv eq_refl); exact H28).
  assert (E32 : ew E 32 = Z_to_bv 64 kb)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = SB) by (rewrite E26; apply unsigned_lit_small; unfold SB; lia).
  assert (U28 : bv_unsigned (ew E 28) = P1) by (rewrite E28; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = kb) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U70 : bv_unsigned (ew E (A_HI 70)) = 0x5d81f0)
    by (subst E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); rewrite (proj1 sm_mx_vals);
        apply unsigned_lit_small; lia).
  assert (U73 : bv_unsigned (ew E (A_HI 73)) = 0x5d820c)
    by (subst E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); rewrite (proj2 sm_mx_vals);
        apply unsigned_lit_small; lia).
  assert (HRmx : rg_send_max fr_RG = 0x5d8840) by reflexivity.
  assert (HRei : rg_send_eintr fr_RG = 0x5d88a0) by reflexivity.
  assert (R0 : region_ok segs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 9%nat) 144 152 144 152 [])).
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW1; lia | apply Forall_nil]. }
  assert (R1 : region_ok segs E (mrestrict (w_H W) mem) sm_mx_rfr).
  { unfold region_ok, sm_mx_rfr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    - apply (chunk_ok_val segs E _ F 56 8 (SOff (A_HI 73) 0) 0x5d820c);
        [cbn [sv_denot]; rewrite U73; reflexivity | zside | zside |]. exact M56.
    - apply (chunk_ok_val segs E _ F 72 8 (SOff (A_HI 70) 0) 0x5d81f0);
        [cbn [sv_denot]; rewrite U70; reflexivity | zside | zside |]. exact M72. }
  assert (R2 : region_ok segs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some (A_HI 70)) 1616 1624 1616 1624 [])).
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U70. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (0x5d81f0 + o) with (rg_send_max fr_RG + (o - 1616)) by lia. apply HWmx. lia. }
  assert (R3 : region_ok segs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some (A_HI 73)) 1684 1685 1684 1685 [])).
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U73. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (0x5d820c + o) with (rg_send_eintr fr_RG + (o - 1684)) by lia. apply HWei. lia. }
  split.
  - apply pa_entry_st_ok_full.
    + unfold sm_fl_sr; apply regs_ok_pin;
        [ apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H7 ].
    + destruct more; vm_compute; reflexivity.
    + destruct more; cbn [sm_mx_regions app]; repeat apply Forall_cons; try apply Forall_nil; try assumption.
      unfold region_ok, sm_mx_rb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U28. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ P1 0 1 (SOff 32 0) kb);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (MB eq_refl).
    + destruct more; cbn [sm_mx_regions app];
        [pose proof (HPi eq_refl); pose proof (HPc eq_refl) |];
        apply pairwise_disjoint_of_extents; unfold sm_mx_rfr, sm_mx_rb, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U28, ?U70, ?U73;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [sm_mx_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U26, U28, U32, U70, U73. rewrite !Z.pow_0_r, !Z.mod_1_r. try change (2 ^ 5) with 32.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - destruct more; unfold sh_ok, sm_mx_SH; [constructor; [|constructor] | constructor].
    pose proof (HPa eq_refl) as HPa'.
    eapply shent_ok_of_range.
    + exact (RA eq_refl).
    + unfold sm_Bx. rewrite (U_atom E 26 SB E26) by (unfold SB; lia). reflexivity.
    + rewrite (U_atom E 28 P1 E28) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* what the run gives: the latch's state, the journal, the three stores (in.n, g_send_max, g_send_eintr), every
   other byte kept, the registers the run does not write, and s6 = t3 (+ 1 with input left) *)
Definition sm_mx_post (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (kk F P1 N1 u : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem' md' kk /\
    KEPT W mem mem' (XS F sm_mx_XG) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1) /\
    val_mem segs (arm W mem') (rg_send_max fr_RG) 8 u /\ val_mem segs (arm W mem') (rg_send_eintr fr_RG) 1 1 /\
    (forall r, In r sm_mx_kept -> getr regs' r = getr regs r) /\
    getr regs' 22 = w64 (if N1 =? 0 then P1 else P1 + 1).
Lemma sm_mx_run : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 (W0 : world segs) mem0 md0 own ly S kk
    F P1 N1 kb,
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md kk ->
  getr regs 7 = w64 1 -> getr regs 9 = w64 F -> getr regs 26 = w64 SB -> getr regs 28 = w64 P1 ->
  getr regs 29 = w64 N1 -> 0 <= N1 < 2 ^ 26 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 ->
  sp0 - STK <= F + 144 -> F + 152 <= sp0 ->
  (N1 <> 0 -> P1 + 1 <= 0x10000 \/ 0x5fb000 <= P1) ->
  (N1 <> 0 -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (N1 <> 0 -> P1 + 1 <= F) ->
  (N1 <> 0 -> val_mem segs (arm W mem) P1 1 kb) ->
  (N1 <> 0 -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 56) 0x5d820c -> sv8 W mem (F + 72) 0x5d81f0 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  awr W mem (rg_send_max fr_RG) 8 -> awr W mem (rg_send_eintr fr_RG) 1 ->
  SRr segs W (cfg_at segs (fr_B0 + AF_arm_sendmax) regs mem md)
    (sm_mx_post W regs mem STK sp0 FP ly0 S0 W0 mem0 md0 own ly S kk F P1 N1 (if N1 =? 0 then 0 else kb)).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 W0 mem0 md0 own ly S kk F P1 N1 kb HJ H7 H9 H26 H28 H29 HN1
    HF1 HF2 HP Hkb Hs1 Hs2 HPi HPa HPc MB RA M56 M72 HW1 HWmx HWei.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HRmx : rg_send_max fr_RG = 0x5d8840) by reflexivity.
  assert (HRei : rg_send_eintr fr_RG = 0x5d88a0) by reflexivity.
  assert (Hmo : negb (N1 =? 0) = true -> N1 <> 0) by (intros Hb; apply negb_true_iff, Z.eqb_neq in Hb; exact Hb).
  destruct (sm_mx_entry W regs mem (negb (N1 =? 0)) F P1 kb H7 H9 H26 H28 HF1 HF2 HP Hkb
    (fun Hb => HPi (Hmo Hb)) (fun Hb => HPa (Hmo Hb)) (fun Hb => HPc (Hmo Hb)) (fun Hb => MB (Hmo Hb))
    (fun Hb => RA (Hmo Hb)) M56 M72 HW1 HWmx HWei) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (sm_x1 kb)))) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg regs (sm_x1 kb)) (Eimg (Ereg regs (sm_x1 kb))))
    by (split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs (sm_x1 kb))) m = getr regs rr)
    by (intros m rr Hm; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E28 : ew (Eimg (Ereg regs (sm_x1 kb))) 28 = w64 P1) by (rewrite (EE 28%nat 28%bv eq_refl); exact H28).
  assert (E29 : ew (Eimg (Ereg regs (sm_x1 kb))) 29 = w64 N1) by (rewrite (EE 29%nat 29%bv eq_refl); exact H29).
  assert (E32 : ew (Eimg (Ereg regs (sm_x1 kb))) 32 = Z_to_bv 64 kb)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 9) = F)
    by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (U350 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 350) = 0x5d81f0)
    by (rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 350%nat with (A_HI 70);
        rewrite (proj1 sm_mx_vals); apply unsigned_lit_small; lia).
  assert (U353 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 353) = 0x5d820c)
    by (rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 353%nat with (A_HI 73);
        rewrite (proj2 sm_mx_vals); apply unsigned_lit_small; lia).
  clear EE.
  set (E := Eimg (Ereg regs (sm_x1 kb))) in *. clearbody E.
  assert (E9b : base_val E (Some 9%nat) = F) by exact U9.
  assert (E350b : base_val E (Some 350%nat) = 0x5d81f0) by exact U350.
  assert (E353b : base_val E (Some 353%nat) = 0x5d820c) by exact U353.
  unfold cfg_at. change (w64 (fr_B0 + AF_arm_sendmax)) with (Z_to_bv 64 (BASE + AF_arm_sendmax)).
  revert HS SHOK. destruct (N1 =? 0) eqn:EN; intros HS SHOK; cbn [negb] in HS, SHOK.
  all: pose proof EN as EN'; first [apply Z.eqb_eq in EN' | apply Z.eqb_neq in EN'].
  all: psrr_branch_tok RUN BR HS SHOK SMspan.
  all: rewrite branch_eq_U, (U_atom E 29 N1 E29), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc]; lia).
  all: clear Hc.
  all: paj_run_to_tok RUNTO HS HJ SHOK SMspan AF_LLVM_latch.
  1,3: lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
    repeat first
     [ apply awr_ok_x_nil
     | apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?E9b in Ha;
         first [exfalso; lia | left; split; [left; lia | lia]] |]
     | apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
         rewrite ?E350b, ?E353b in Ha; first [apply HGmx; lia | apply HGei; lia] |] ].
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]);
    assert (EV9 : bv_unsigned (ew Ev 9) = F) by (rewrite ?ew_ewset_other by lia; exact U9);
    assert (EV29 : bv_unsigned (ew Ev 29) = N1)
      by (rewrite ?ew_ewset_other by lia; rewrite E29; apply unsigned_lit_small; lia);
    assert (EV32 : bv_unsigned (ew Ev 32) = kb)
      by (rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia);
    assert (EV350 : bv_unsigned (ew Ev 350) = 0x5d81f0) by (rewrite ?ew_ewset_other by lia; exact U350);
    assert (EV353 : bv_unsigned (ew Ev 353) = 0x5d820c) by (rewrite ?ew_ewset_other by lia; exact U353)
  end.
  all: pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_mx_kept HS HAE2
    ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: prreg HS (22%bv : bv 5) Q22.
  all: rewrite ?ew_ewset_other in Q22 by lia.
  all: assert (Q22' : getr (ms_regs ms) 22 = w64 (if N1 =? 0 then P1 else P1 + 1))
    by (rewrite Q22, EN; cbv iota; rewrite ?E28; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
  all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
  all: pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
  all: pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
  all: cbn [ms_mem restrict] in RG0, RG2, RG3.
  all: assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1))
    by (rewrite EN; cbv iota; eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
        [ exact EV9 | left; reflexivity
        | cbn [sv_denot]; rewrite ?EV29; first [reflexivity | f_equal; lia]
        | zside | zside ]).
  all: assert (Vmx : val_mem segs (arm W (ms_mem ms)) (rg_send_max fr_RG) 8 (if N1 =? 0 then 0 else kb))
    by (rewrite EN; cbv iota; replace (rg_send_max fr_RG) with (0x5d81f0 + 1616) by reflexivity;
        eapply (field_of_region _ _ 350%nat 0x5d81f0 _ _ _ _ _ 1616 8%N _ _ RG2);
        [ exact EV350 | left; reflexivity
        | cbn [sv_denot]; rewrite ?EV32, ?Z.add_0_r; reflexivity | zside | zside ]).
  all: assert (Vei : val_mem segs (arm W (ms_mem ms)) (rg_send_eintr fr_RG) 1 1)
    by (replace (rg_send_eintr fr_RG) with (0x5d820c + 1684) by reflexivity;
        eapply (field_of_region _ _ 353%nat 0x5d820c _ _ _ _ _ 1684 1%N _ _ RG3);
        [ exact EV353 | left; reflexivity | reflexivity | zside | zside ]).
  all: assert (KP : KEPT W mem (ms_mem ms) (XS F sm_mx_XG))
    by (intros a Ha Hn; split;
        [ apply (aview_kept_out _ _ _ _ _ HFr a Ha); intros (r & Hin & Hr); vm_compute in Hin;
          repeat (destruct Hin as [<- | Hin];
            [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?E9b, ?E350b, ?E353b in Hr;
              first [ lia | apply Hn; unfold XS, sm_mx_XG; apply inFP_cons; right; apply inFP_cons;
                first [ left; lia | right; apply inFP_cons; left; lia
                      | right; apply inFP_cons; right; apply inFP_cons; left; lia ] ]
            | ]);
          destruct Hin
        | exact (sm_wkeep W mem (ms_mem ms) a HG0) ]).
  all: pmkst HS.
  all: apply SRr_ret.
  all: unfold sm_mx_post; cbv beta.
  all: split; [reflexivity|].
  all: exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
  all: split; [reflexivity|].
  all: split; [exact HJ|].
  all: split; [exact KP|].
  all: split; [exact HG0|].
  all: split; [exact V144|].
  all: split; [rewrite EN in Vmx; exact Vmx|].
  all: split; [exact Vei|].
  all: split; [exact KR|].
  all: exact Q22'.
Qed.

(* ---------------------------------------------------------------- ARM_sendmax (_cut.v :583) *)
Theorem lf_arm_sendmax : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_A B G_fr fr_FP LS RINV 8 cx t W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep & HLS & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD6 & HD7 & HD27 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = 8).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk8 : picks 8 = false) by reflexivity.
  rewrite Hpk8 in Hpick. destruct Hpick as (HD28 & HD29 & _).
  assert (HAR : AR segs B ly3 S3 W mem md)
    by (exact (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  assert (Hr7 : getr regs 7 = w64 1) by (rewrite (KD 7%bv ltac:(sm_in)); exact HD7).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr26 : getr regs 26 = w64 SB) by (rewrite (KD 26%bv ltac:(sm_in)); exact C26).
  assert (Hr28 : getr regs 28 = w64 (c_p cx + lm_k m + 1)) by (rewrite (KD 28%bv ltac:(sm_in)); exact HD28).
  assert (Hr29 : getr regs 29 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KD 29%bv ltac:(sm_in)); exact HD29).
  (* the input block and the byte in.p[0] *)
  pose proof Hinput as [[[Hn0 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hblk) as Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (sm_in_byte_rng cx (lm_k m + 1)) as Hkb8.
  (* the frame and the stream's two cells *)
  pose proof Hframe as (_ & Hawr & _ & _ & F56 & _ & F72 & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Hmodel as (_ & _ & _ & Hout & _).
  pose proof Hout as (_ & Omx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Oei & _).
  rewrite Hc.
  eapply SRr_mono.
  { exact (sm_mx_run W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 kk (lf_F cx) (c_p cx + lm_k m + 1) (c_n cx - lm_k m - 1) (in_byte cx (lm_k m + 1))
      HJ Hr7 Hr9 Hr26 Hr28 Hr29 ltac:(lia) HFbound HFmod ltac:(lia) Hkb8 ltac:(lia) ltac:(lia)
      ltac:(intros HN; unfold off_img in Hpimg; lia)
      ltac:(intros HN; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; rewrite <- Z.add_assoc; exact (proj1 (sm_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))))
      ltac:(intros HN; apply (range_addressable_of_block segs B LAWS ly3 S3 W mem md (c_p cx) (c_n cx));
            [exact HAR | exact Hblk | lia | lia])
      F56 F72 HW1 Omx Oei). }
  intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & KP & HGr & V144 & Vmx & Vei & KR & Q22).
  pose proof sm_mx_xgok as HXG.
  assert (HXOK : XOK (XS (lf_F cx) sm_mx_XG)) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_mx_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  set (u := if c_n cx - lm_k m - 1 =? 0 then 0 else in_byte cx (lm_k m + 1)) in *.
  assert (Hu : 0 <= u <= 255) by (unfold u; destruct (_ =? 0); lia).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, kk, (sm_sendmax cx m u), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept cx true ly3 S3 W mem md mem' fpos sm_mx_XG HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept cx ly3 S3 W mem md mem' fpos sm_mx_XG HAR Hfin Hsp0 HXG KP HGr Hflag)|].
  split; [exact (sm_amodel_mx ly3 S3 W mem md mem' (lf_F cx) cx m u HAR ltac:(lia) KP HGr Hmodel HO Hu Vmx Vei)|].
  split; [exact (sm_ainput_kept cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [exact Hsep|].
  assert (Hud : u = (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
  { unfold u. destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
    - replace (c_n cx - lm_k m - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - replace (c_n cx - lm_k m - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
  split; [rewrite Hud; exact (LS_sendmax cx t m ly3 S3 HLS)|].
  split; [rewrite Hud; exact (RI_sendmax cx t m HRINV)|].
  unfold lregs_K, lregs_common, sm_sendmax. cbn [lm_k]. unfold sm_kn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [rewrite (KK 20%bv ltac:(sm_in) ltac:(sm_in)); exact C20|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact C25|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact HD27|].
  split; [exact Htb|].
  unfold sv8.
  destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite EN in Q22, V144. cbv iota in Q22, V144.
    split; [rewrite Q22; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 2)) with (c_n cx - lm_k m - 1 - 1) by lia; exact V144|]. lia.
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = true) by (apply Z.eqb_eq; lia).
    rewrite EN in Q22, V144. cbv iota in Q22, V144.
    split; [rewrite Q22; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 1)) with 0 by lia; exact V144|]. lia.
Qed.

(* ---------------------------------------------------------------- arm 9: the controller goes away *)
(* 0x84660 `beqz t4,0x849a4`.  Input left: the shadow check of in.p[0] (t3), `lbu a0,0(t3); addi t4,t4,-1;
   andi a0,a0,1; addi s6,t3,1; sd t4,144(s1); beqz a0,0x849ac`.  An odd byte: `auipc a0,0x554; addi s4,a0,1076`
   (s4 = &g_lock = VAL (A_OBJ 6)), `mv a0,s4; jal pthread_mutex_lock; ld a0,24(s1); li a1,-1; sw a1,-512(a0)`
   (g_client := -1, through the frame's copy 0xa21e0 of A_HI 67), `mv a0,s4; li s4,10; jal pthread_mutex_unlock;
   li t2,1; j 0x849b4`.  None left: 0x849a4 `sd zero,144(s1); mv s6,t3`.  Then 0x849ac `ld a0,48(s1);
   sb t2,1660(a0)` (g_send_dead := 1, through 0x5d8204 = A_HI 72; the odd byte skips it) and 0x849b4
   `ld a0,64(s1); sb t2,1636(a0)` (g_gone := 1, through 0x5d81fc = A_HI 71), `j 0x84490`. *)
Lemma sm_df_vals : VAL (A_HI 67) = 0xa21e0 /\ VAL (A_HI 71) = 0x5d81fc /\ VAL (A_HI 72) = 0x5d8204.
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.
(* g_lock is the listing's object 6: a computation at PB_fr, not a hypothesis *)
Lemma sm_hv6 : VAL (A_OBJ 6) = rg_lock fr_RG.
Proof. vm_compute. reflexivity. Qed.
(* The frame's three address copies, the in.n cell, and the three globals the arm may store to.  g_send_dead and
   g_client carry their entry values dd / cl as chunks: the path that does not store to one of them still reads
   its value off the state at the latch. *)
Definition sm_df_rfr : YP09.region := YP09.mkRegion (Some 9%nat) 24 72 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff (A_HI 67) 0)); YP09.mkChunk 48 (CVal 8 (SOff (A_HI 72) 0));
   YP09.mkChunk 64 (CVal 8 (SOff (A_HI 71) 0))].
Definition sm_df_rdd (dd : Z) : YP09.region :=
  YP09.mkRegion (Some (A_HI 72)) 1660 1661 1660 1661 [YP09.mkChunk 1660 (CVal 1 (SLit dd))].
Definition sm_df_rgn : YP09.region := YP09.mkRegion (Some (A_HI 71)) 1636 1637 1636 1637 [].
Definition sm_df_rcl (cl : Z) : YP09.region :=
  YP09.mkRegion (Some (A_HI 67)) (-512) (-508) (-512) (-508) [YP09.mkChunk (-512) (CVal 4 (SLit cl))].
Definition sm_df_regions (more : bool) (dd cl : Z) : smem :=
  [ YP09.mkRegion (Some 9%nat) 144 152 144 152 []; sm_df_rfr; sm_df_rdd dd; sm_df_rgn; sm_df_rcl cl ]
  ++ (if more then [sm_mx_rb] else []).
Definition sm_df_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (26%nat, mkAF SB SB 0); (28%nat, mkAF 4096 (2 ^ 47 - 16) 0);
            (32%nat, mkAF 0 255 0); (A_HI 67, mkAF 0xa21e0 0xa21e0 0); (A_HI 71, mkAF 0x5d81fc 0x5d81fc 0);
            (A_HI 72, mkAF 0x5d8204 0x5d8204 0) ] [] [].

Lemma sm_df_entry : forall (W : world segs) regs mem (more : bool) F P1 kb dd cl,
  getr regs 7 = w64 1 -> getr regs 9 = w64 F -> getr regs 26 = w64 SB -> getr regs 28 = w64 P1 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 ->
  0 <= dd < 256 -> 0 <= cl < 2 ^ 32 ->
  (more = true -> P1 + 1 <= 0x10000 \/ 0x5fb000 <= P1) ->
  (more = true -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (more = true -> P1 + 1 <= F) ->
  (more = true -> val_mem segs (arm W mem) P1 1 kb) ->
  (more = true -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 24) 0xa21e0 -> sv8 W mem (F + 48) 0x5d8204 -> sv8 W mem (F + 64) 0x5d81fc ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  val_mem segs (arm W mem) (rg_send_dead fr_RG) 1 dd -> awr W mem (rg_send_dead fr_RG) 1 ->
  awr W mem (rg_gone fr_RG) 1 ->
  val_mem segs (arm W mem) (rg_client fr_RG) 4 cl -> awr W mem (rg_client fr_RG) 4 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (sm_x1 kb)))
    (mkSS AF_arm_default sm_fl_sr (sm_df_regions more dd cl) None sm_df_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_default)) mem (seg_rom segs)))
  /\ sh_ok segs sm_Bx (sm_mx_SH more) (Eimg (Ereg regs (sm_x1 kb))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem more F P1 kb dd cl H7 H9 H26 H28 HF1 HF2 HP Hkb Hdd Hcl HPi HPa HPc MB RA M24 M48 M64 HW1
    Vdd HWdd HWgn Vcl HWcl.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (sm_x1 kb))).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E26 : ew E 26 = w64 SB) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
  assert (E28 : ew E 28 = w64 P1) by (rewrite (EE 28%nat 28%bv eq_refl); exact H28).
  assert (E32 : ew E 32 = Z_to_bv 64 kb)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = SB) by (rewrite E26; apply unsigned_lit_small; unfold SB; lia).
  assert (U28 : bv_unsigned (ew E 28) = P1) by (rewrite E28; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = kb) by (rewrite E32; apply unsigned_lit_small; lia).
  pose proof sm_df_vals as (V67 & V71 & V72).
  assert (U67 : bv_unsigned (ew E (A_HI 67)) = 0xa21e0)
    by (subst E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); rewrite V67; apply unsigned_lit_small; lia).
  assert (U71 : bv_unsigned (ew E (A_HI 71)) = 0x5d81fc)
    by (subst E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); rewrite V71; apply unsigned_lit_small; lia).
  assert (U72 : bv_unsigned (ew E (A_HI 72)) = 0x5d8204)
    by (subst E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); rewrite V72; apply unsigned_lit_small; lia).
  pose proof sm_rgv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRdd & HRgn & HRcl & _).
  assert (R0 : region_ok segs E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 9%nat) 144 152 144 152 [])).
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW1; lia | apply Forall_nil]. }
  assert (R1 : region_ok segs E (mrestrict (w_H W) mem) sm_df_rfr).
  { unfold region_ok, sm_df_rfr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (chunk_ok_val segs E _ F 24 8 (SOff (A_HI 67) 0) 0xa21e0);
        [cbn [sv_denot]; rewrite U67; reflexivity | zside | zside |]. exact M24.
    - apply (chunk_ok_val segs E _ F 48 8 (SOff (A_HI 72) 0) 0x5d8204);
        [cbn [sv_denot]; rewrite U72; reflexivity | zside | zside |]. exact M48.
    - apply (chunk_ok_val segs E _ F 64 8 (SOff (A_HI 71) 0) 0x5d81fc);
        [cbn [sv_denot]; rewrite U71; reflexivity | zside | zside |]. exact M64. }
  assert (R2 : region_ok segs E (mrestrict (w_H W) mem) (sm_df_rdd dd)).
  { unfold region_ok, sm_df_rdd. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U72. split; [lia|]. split; [lia|]. split.
    - intros o Ho. replace (0x5d8204 + o) with (rg_send_dead fr_RG + (o - 1660)) by lia. apply HWdd. lia.
    - constructor; [|constructor].
      apply (chunk_ok_val segs E _ 0x5d8204 1660 1 (SLit dd) dd); [reflexivity | zside | zside |].
      replace (0x5d8204 + 1660) with (rg_send_dead fr_RG) by lia. exact Vdd. }
  assert (R3 : region_ok segs E (mrestrict (w_H W) mem) sm_df_rgn).
  { unfold region_ok, sm_df_rgn. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U71. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (0x5d81fc + o) with (rg_gone fr_RG + (o - 1636)) by lia. apply HWgn. lia. }
  assert (R4 : region_ok segs E (mrestrict (w_H W) mem) (sm_df_rcl cl)).
  { unfold region_ok, sm_df_rcl. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U67. split; [lia|]. split; [lia|]. split.
    - intros o Ho. replace (0xa21e0 + o) with (rg_client fr_RG + (o + 512)) by lia. apply HWcl. lia.
    - constructor; [|constructor].
      apply (chunk_ok_val segs E _ 0xa21e0 (-512) 4 (SLit cl) cl); [reflexivity | zside | zside |].
      replace (0xa21e0 + -512) with (rg_client fr_RG) by lia. exact Vcl. }
  split.
  - apply pa_entry_st_ok_full.
    + unfold sm_fl_sr; apply regs_ok_pin;
        [ apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H7 ].
    + destruct more; vm_compute; reflexivity.
    + destruct more; cbn [sm_df_regions app]; repeat apply Forall_cons; try apply Forall_nil; try assumption.
      unfold region_ok, sm_mx_rb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U28. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ P1 0 1 (SOff 32 0) kb);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (MB eq_refl).
    + destruct more; cbn [sm_df_regions app];
        [pose proof (HPi eq_refl); pose proof (HPc eq_refl) |];
        apply pairwise_disjoint_of_extents;
        unfold sm_df_rfr, sm_df_rdd, sm_df_rgn, sm_df_rcl, sm_mx_rb, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U28, ?U67, ?U71, ?U72;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [sm_df_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U26, U28, U32, U67, U71, U72. rewrite !Z.pow_0_r, !Z.mod_1_r. try change (2 ^ 5) with 32.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - destruct more; unfold sh_ok, sm_mx_SH; [constructor; [|constructor] | constructor].
    pose proof (HPa eq_refl) as HPa'.
    eapply shent_ok_of_range.
    + exact (RA eq_refl).
    + unfold sm_Bx. rewrite (U_atom E 26 SB E26) by (unfold SB; lia). reflexivity.
    + rewrite (U_atom E 28 P1 E28) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ---- what a segment of arm 9 keeps: a run changes only its regions' write windows, a libc call only its
   written bytes and its scratch *)
Lemma sm_kept_trans : forall (W : world segs) m1 m2 m3 X, KEPT W m1 m2 X -> KEPT W m2 m3 X -> KEPT W m1 m3 X.
Proof.
  intros W m1 m2 m3 X H12 H23 a Ha Hn. destruct (H12 a Ha Hn) as [V12 W12]. destruct (H23 a Ha Hn) as [V23 W23].
  split; [rewrite V23; exact V12 | intros Hw; exact (W23 (W12 Hw))].
Qed.
Lemma sm_kept_run : forall (W : world segs) E rs m m' X,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E rs a -> inFP X a) -> KEPT W m m' X.
Proof.
  intros W E rs m m' X HFr HGr HX a Ha Hn. split.
  - apply (aview_kept_out E rs (w_H W) m m' HFr a Ha). intros Hw. exact (Hn (HX a Hw)).
  - exact (sm_wkeep W m m' a HGr).
Qed.
Lemma sm_kept_call : forall (W : world segs) m m' X (Wr : Z -> Prop) lo hi,
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (lo <= a < hi) -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  (forall a, Wr a -> inFP X a) -> (forall a, lo <= a < hi -> inFP X a) -> KEPT W m m' X.
Proof.
  intros W m m' X Wr lo hi HV HP HW HS a Ha Hn. split.
  - apply HV; [exact Ha | intros Hw; exact (Hn (HW a Hw)) | intros Hs; exact (Hn (HS a Hs))].
  - exact (writable_kept (w_H W) m m' a (HP a)).
Qed.
Lemma sm_grows_of_pres : forall (W : world segs) m m',
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m').
Proof.
  intros W m m' HP x Hx. unfold mrestrict in *. destruct (w_H W x) eqn:Eh; [exact Hx|].
  destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
  assert (Hp : apresent (w_H W) m (bv_unsigned x))
    by (split; rewrite Z_to_bv_bv_unsigned; [exact Eh | exists b; exact Em]).
  destruct (HP _ Hp) as [_ [b2 Hb2]]. rewrite Z_to_bv_bv_unsigned in Hb2. rewrite Hb2. discriminate.
Qed.
(* the four bytes a 4-byte store of the word -1 leaves *)
Lemma sm_val_m1 : forall E m n b cs lo hi wlo whi od e,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 (-1) ->
  val_mem segs m (b + od) 4 (2 ^ 32 - 1).
Proof.
  intros E m n b cs lo hi wlo whi od e (_ & _ & _ & Hcs) Hn Hc He k Hk.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
  destruct (Hck (Z.of_nat k) ltac:(unfold c_len; cbn; lia)) as (bb & Hb1 & Hb2).
  cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2.
  rewrite He in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
  apply bv_eq. destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity .. | lia].
Qed.

(* ---- the run of arm 9 to the latch, on its three paths *)
(* the stored set: the in.n cell, the scratch, g_send_dead, g_gone, g_client, and on the odd byte the lock word *)
Definition sm_df_XG (g : bool) : list (Z * Z) :=
  [(rg_send_dead fr_RG, rg_send_dead fr_RG + 1); (rg_gone fr_RG, rg_gone fr_RG + 1);
   (rg_client fr_RG, rg_client fr_RG + 4)] ++ (if g then [(rg_lock fr_RG + 4, rg_lock fr_RG + 8)] else []).
(* the low bit of a byte, as `andi a0,a0,1; beqz a0` tests it *)
Lemma sm_odd_land : forall z, Z.odd z = negb (Z.land z 1 =? 0).
Proof.
  intros z. replace (Z.land z 1) with (z mod 2) by (symmetry; exact (Z.land_ones z 1 ltac:(lia))).
  rewrite Zmod_odd. destruct (Z.odd z); reflexivity.
Qed.
(* what the run gives: g is the branch taken -- input left and its byte kb odd (the controller is gone: g_client := -1
   under the lock) *)
Definition sm_df_post (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (kk F P1 N1 kb dd cl : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists (g : bool) regs' mem' md',
    g = negb (N1 =? 0) && Z.odd kb /\
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem' md' kk /\
    KEPT W mem mem' (XS F (sm_df_XG g)) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1) /\
    val_mem segs (arm W mem') (rg_send_dead fr_RG) 1 (if g then dd else 1) /\
    val_mem segs (arm W mem') (rg_gone fr_RG) 1 1 /\
    val_mem segs (arm W mem') (rg_client fr_RG) 4 (if g then 2 ^ 32 - 1 else cl) /\
    (g = true -> val_mem segs (arm W mem') (rg_lock fr_RG + 4) 4 0) /\
    (forall r, In r sm_df_kept -> getr regs' r = getr regs r) /\
    getr regs' 20 = w64 10 /\
    getr regs' 22 = w64 (if N1 =? 0 then P1 else P1 + 1).
(* a region's write window, with its base atom's value (any env the runs and calls extend E to) *)
Ltac sm_dfb H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in H;
  repeat (first [rewrite ew_ewset_other in H by (cbv; lia) | rewrite ew_havoc_old in H by (cbv; lia)]);
  repeat match goal with U : bv_unsigned (ew _ _) = _ |- _ => rewrite U in H end.
(* every region the runs of arm 9 write is the in.n cell (the frame's window) or a global of G_fr *)
Ltac sm_df_awr :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [intros a Ha; sm_dfb Ha; first [exfalso; lia | left; split; [left; lia | lia]] |]
   | apply awr_ok_x_cons_g; [intros a Ha; sm_dfb Ha; first [apply HGdd; lia | apply HGgn; lia | apply HGcl; lia] |] ].
(* a byte of a region's write window is in a concrete stored list *)
Ltac sm_inFP := repeat (first [apply inFP_cons; left; lia | apply inFP_cons; right]).
(* every write window of a run's regions lies in XS F (sm_df_XG g), g concrete *)
Ltac sm_inX :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [sm_dfb Hr; unfold XS, sm_df_XG; cbn [app]; sm_inFP | ]);
  destruct Hin.
(* a byte apart from every write window of a run's regions *)
Ltac sm_notw :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [sm_dfb Hr; lia | ]); destruct Hin.
(* the value of a region's base atom, in any env the runs and calls extend E to *)
Ltac sm_base :=
  repeat (first [rewrite ew_ewset_other by (cbv; lia) | rewrite ew_havoc_old by (cbv; lia)]);
  match goal with U : bv_unsigned (ew _ ?n) = _ |- bv_unsigned (ew _ ?n) = _ => exact U end.
Lemma sm_av_ne : forall (W : world segs) (m : word -> option byte) a (n : nat) v x,
  val_mem segs (mrestrict (w_H W) m) a n v -> a <= x < a + Z.of_nat n -> aview segs (w_H W) m x <> None.
Proof.
  intros W m a n v x Hv Hx. unfold aview.
  pose proof (Hv (Z.to_nat (x - a)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  replace (a + (x - a)) with x in Hb by lia. rewrite Hb. discriminate.
Qed.
Lemma sm_av0 : forall (W : world segs) (m : word -> option byte) a,
  val_mem segs (mrestrict (w_H W) m) a 4 0 -> aview segs (w_H W) m a = Some 0.
Proof.
  intros W m a Hv. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as Hb. cbn [Z.of_nat] in Hb.
  rewrite Z.add_0_r in Hb. rewrite Hb. cbn [option_map]. f_equal; vm_compute; reflexivity.
Qed.
Lemma sm_df_run : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 (W0 : world segs) mem0 md0 own ly S kk
    F P1 N1 kb dd cl,
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md kk ->
  getr regs 2 = w64 F -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 7 = w64 1 -> getr regs 9 = w64 F -> getr regs 20 = w64 10 -> getr regs 26 = w64 SB ->
  getr regs 28 = w64 P1 -> getr regs 29 = w64 N1 -> 0 <= N1 < 2 ^ 26 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 ->
  F + 152 <= sp0 -> (F - sp0) mod 16 = 0 -> ESTACK + (sp0 - F) <= STK ->
  (N1 <> 0 -> P1 + 1 <= 0x10000 \/ 0x5fb000 <= P1) ->
  (N1 <> 0 -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (N1 <> 0 -> P1 + 1 <= F) ->
  (N1 <> 0 -> val_mem segs (arm W mem) P1 1 kb) ->
  (N1 <> 0 -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 24) 0xa21e0 -> sv8 W mem (F + 48) 0x5d8204 -> sv8 W mem (F + 64) 0x5d81fc ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  val_mem segs (arm W mem) (rg_send_dead fr_RG) 1 dd -> 0 <= dd < 256 -> awr W mem (rg_send_dead fr_RG) 1 ->
  awr W mem (rg_gone fr_RG) 1 ->
  val_mem segs (arm W mem) (rg_client fr_RG) 4 cl -> 0 <= cl < 2 ^ 32 -> awr W mem (rg_client fr_RG) 4 ->
  alock_at fr_RG W mem false ->
  SRr segs W (cfg_at segs (fr_B0 + AF_arm_default) regs mem md)
    (sm_df_post W regs mem STK sp0 FP ly0 S0 W0 mem0 md0 own ly S kk F P1 N1 kb dd cl).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 W0 mem0 md0 own ly S kk F P1 N1 kb dd cl HJ H2 H3 H4 H7 H9 H20 H26
    H28 H29 HN1 HF1 HF2 HP Hkb Hs1 Hs16 Hs2 HPi HPa HPc MB RA M24 M48 M64 HW1 Vdd Hdd HWdd HWgn Vcl Hcl HWcl HLK.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  pose proof sm_rgv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRdd & HRgn & HRcl & _ & HRlk & _).
  assert (Hmo : negb (N1 =? 0) = true -> N1 <> 0) by (intros Hb; apply negb_true_iff, Z.eqb_neq in Hb; exact Hb).
  destruct (sm_df_entry W regs mem (negb (N1 =? 0)) F P1 kb dd cl H7 H9 H26 H28 HF1 HF2 HP Hkb Hdd Hcl
    (fun Hb => HPi (Hmo Hb)) (fun Hb => HPa (Hmo Hb)) (fun Hb => HPc (Hmo Hb)) (fun Hb => MB (Hmo Hb))
    (fun Hb => RA (Hmo Hb)) M24 M48 M64 HW1 Vdd HWdd HWgn Vcl HWcl) as [HS SHOK].
  set (E := Eimg (Ereg regs (sm_x1 kb))) in *.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (sm_x1 kb)) E)
    by (subst E; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E2 : ew E 2 = w64 F) by (rewrite (EE 2%nat 2%bv eq_refl); exact H2).
  assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact H3).
  assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact H4).
  assert (E20 : ew E 20 = w64 10) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
  assert (E28 : ew E 28 = w64 P1) by (rewrite (EE 28%nat 28%bv eq_refl); exact H28).
  assert (E29 : ew E 29 = w64 N1) by (rewrite (EE 29%nat 29%bv eq_refl); exact H29).
  assert (E32 : ew E 32 = Z_to_bv 64 kb)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (U28 : bv_unsigned (ew E 28) = P1) by (rewrite E28; apply unsigned_lit_small; lia).
  pose proof sm_df_vals as (V67 & V71 & V72).
  assert (U347 : bv_unsigned (ew E 347) = 0xa21e0)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 347%nat with (A_HI 67);
        rewrite V67; apply unsigned_lit_small; lia).
  assert (U351 : bv_unsigned (ew E 351) = 0x5d81fc)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 351%nat with (A_HI 71);
        rewrite V71; apply unsigned_lit_small; lia).
  assert (U352 : bv_unsigned (ew E 352) = 0x5d8204)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 352%nat with (A_HI 72);
        rewrite V72; apply unsigned_lit_small; lia).
  assert (E247 : ew E 247 = Z_to_bv 64 (rg_lock fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 247%nat with (A_OBJ 6);
        rewrite sm_hv6; reflexivity).
  clear EE.
  clearbody E.
  unfold cfg_at. change (w64 (fr_B0 + AF_arm_default)) with (Z_to_bv 64 (BASE + AF_arm_default)).
  revert HS SHOK. destruct (N1 =? 0) eqn:EN; intros HS SHOK; cbn [negb] in HS, SHOK.
  all: pose proof EN as EN'; first [apply Z.eqb_eq in EN' | apply Z.eqb_neq in EN'].
  all: psrr_branch_tok RUN BR HS SHOK SMspan.
  all: rewrite branch_eq_U, (U_atom E 29 N1 E29), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc]; lia).
  all: clear Hc.
  - (* no input left: in.n := 0, g_send_dead := 1, g_gone := 1 *)
    paj_run_to_tok RUNTO HS HJ SHOK SMspan AF_LLVM_latch.
    + sm_df_awr.
    + assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) E) by exact HAE.
      assert (EV9 : bv_unsigned (ew E 9) = F) by sm_base.
      assert (EV351 : bv_unsigned (ew E 351) = 0x5d81fc) by sm_base.
      assert (EV352 : bv_unsigned (ew E 352) = 0x5d8204) by sm_base.
      assert (EV347 : bv_unsigned (ew E 347) = 0xa21e0) by sm_base.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
        ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
      rewrite E20 in Q20. rewrite E28 in Q22.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
      pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
      pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
      cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
      assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 0)
        by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
            [exact EV9 | left; reflexivity | reflexivity | zside | zside]).
      assert (Vdd' : val_mem segs (arm W (ms_mem ms)) (rg_send_dead fr_RG) 1 1)
        by (replace (rg_send_dead fr_RG) with (0x5d8204 + 1660) by lia;
            eapply (field_of_region _ _ 352%nat 0x5d8204 _ _ _ _ _ 1660 1%N _ _ RG2);
            [exact EV352 | left; reflexivity | reflexivity | zside | zside]).
      assert (Vgn' : val_mem segs (arm W (ms_mem ms)) (rg_gone fr_RG) 1 1)
        by (replace (rg_gone fr_RG) with (0x5d81fc + 1636) by lia;
            eapply (field_of_region _ _ 351%nat 0x5d81fc _ _ _ _ _ 1636 1%N _ _ RG3);
            [exact EV351 | left; reflexivity | reflexivity | zside | zside]).
      assert (Vcl' : val_mem segs (arm W (ms_mem ms)) (rg_client fr_RG) 4 cl)
        by (replace (rg_client fr_RG) with (0xa21e0 + -512) by lia;
            eapply (field_of_region _ _ 347%nat 0xa21e0 _ _ _ _ _ (-512) 4%N _ _ RG4);
            [exact EV347 | left; reflexivity | reflexivity | zside | zside]).
      pmkst HS. apply SRr_ret. unfold sm_df_post; cbv beta. split; [reflexivity|].
      exists false. do 3 eexists. split; [rewrite EN; reflexivity|].
      split; [reflexivity|]. split; [exact HJ|].
      split; [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFr HG0); sm_inX|].
      split; [exact HG0|].
      split; [rewrite EN; exact V144|].
      split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
      split; [intros Hf; discriminate Hf|].
      split; [exact KR|]. split; [exact Q20|]. rewrite EN; exact Q22.
  - (* input left: the byte, in.n := t4 - 1, then its low bit *)
    paj_run_tok RUN HS HJ SHOK SMspan.
    + sm_df_awr.
    + rename HF into HFa, HFr into HFra, HG0 into HGa.
      psrr_branch_tok RUN BR HS SHOK SMspan.
      all: assert (EV32 : ew (ewset (ewset E 512 w) 513 w0) 32 = Z_to_bv 64 kb)
             by (rewrite ?ew_ewset_other by lia; exact E32).
      all: rewrite branch_eq_U, U_and_lit, (U_atom _ 32 kb EV32), U_lit in Hc by lia.
      all: pose proof (sm_odd_land kb) as Hodd; rewrite Hc in Hodd; cbn [negb] in Hodd; clear Hc.
      * (* even: g_send_dead := 1, g_gone := 1 *)
        paj_run_to_tok RUNTO HS HJ SHOK SMspan AF_LLVM_latch.
        -- sm_df_awr.
        -- assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) (ewset (ewset E 512 w) 513 w0))
             by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                        | rewrite ?ed_ewset; exact (proj2 HAE)]).
           assert (EV9 : bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 9) = F) by sm_base.
           assert (EV351 : bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 351) = 0x5d81fc) by sm_base.
           assert (EV352 : bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 352) = 0x5d8204) by sm_base.
           assert (EV347 : bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 347) = 0xa21e0) by sm_base.
           assert (EV29 : bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 29) = N1)
             by (rewrite !ew_ewset_other by lia; rewrite E29; apply unsigned_lit_small; lia).
           pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
             ltac:(vm_compute; reflexivity)) as KR.
           cbn [ms_regs restrict] in KR.
           prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
           rewrite ?ew_ewset_other in Q20, Q22 by lia. rewrite E20 in Q20. rewrite U28 in Q22.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
           pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
           pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
           pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
           cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
           assert (V144 : val_mem segs (arm W (ms_mem ms0)) (F + 144) 8 (N1 - 1))
             by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
                 [exact EV9 | left; reflexivity | cbn [sv_denot]; rewrite EV29; f_equal; lia | zside | zside]).
           assert (Vdd' : val_mem segs (arm W (ms_mem ms0)) (rg_send_dead fr_RG) 1 1)
             by (replace (rg_send_dead fr_RG) with (0x5d8204 + 1660) by lia;
                 eapply (field_of_region _ _ 352%nat 0x5d8204 _ _ _ _ _ 1660 1%N _ _ RG2);
                 [exact EV352 | left; reflexivity | reflexivity | zside | zside]).
           assert (Vgn' : val_mem segs (arm W (ms_mem ms0)) (rg_gone fr_RG) 1 1)
             by (replace (rg_gone fr_RG) with (0x5d81fc + 1636) by lia;
                 eapply (field_of_region _ _ 351%nat 0x5d81fc _ _ _ _ _ 1636 1%N _ _ RG3);
                 [exact EV351 | left; reflexivity | reflexivity | zside | zside]).
           assert (Vcl' : val_mem segs (arm W (ms_mem ms0)) (rg_client fr_RG) 4 cl)
             by (replace (rg_client fr_RG) with (0xa21e0 + -512) by lia;
                 eapply (field_of_region _ _ 347%nat 0xa21e0 _ _ _ _ _ (-512) 4%N _ _ RG4);
                 [exact EV347 | left; reflexivity | reflexivity | zside | zside]).
           pmkst HS. apply SRr_ret. unfold sm_df_post; cbv beta. split; [reflexivity|].
           exists false. do 3 eexists. split; [rewrite EN, Hodd; reflexivity|].
           split; [reflexivity|]. split; [exact HJ|].
           split; [apply (sm_kept_trans W mem (ms_mem ms) (ms_mem ms0));
                   [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFra HGa); sm_inX
                   | apply (sm_kept_run W _ _ (ms_mem ms) (ms_mem ms0) _ HFr HG0); sm_inX]|].
           split; [exact (mem_grows_trans _ _ _ HGa HG0)|].
           split; [rewrite EN; exact V144|].
           split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
           split; [intros Hf; discriminate Hf|].
           split; [exact KR|]. split; [exact Q20|]. rewrite EN; exact Q22.
      * (* odd: to pthread_mutex_lock *)
        paj_run_tok RUN HS HJ SHOK SMspan.
        -- sm_df_awr.
        -- rename HF into HFb, HFr into HFrb, HG0 into HGb.
           (* pthread_mutex_lock (&g_lock): a0 = s4 = A_OBJ 6 *)
           pmkst HS.
           prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
           prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
           rewrite ?ew_ewset_other in Q2, Q3, Q4, Q10 by lia.
           rewrite E2 in Q2. rewrite E3 in Q3. rewrite E4 in Q4. rewrite E247 in Q10.
           assert (Usp : spZ (ms_regs ms0) = F) by (unfold spZ; rewrite Q2; apply unsigned_lit_small; lia).
           pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
           assert (KL1 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
               aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
           { intros a Ha. transitivity (aview segs (w_H W) (ms_mem ms) a).
             - apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)). sm_notw.
             - apply (aview_kept_out _ _ _ _ _ HFra a ltac:(lia)). sm_notw. }
           pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
           assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly S a).
           { intros a Ha Ho. destruct (HG a (HGlk a Ha)) as (Hi & Hno & _). apply Hno.
             exact (proj1 (al_owned_image _ _ LAWS ly S W (ms_mem ms0) _ a HARc Hi) Ho). }
           assert (LKV : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
               aview segs (w_H W) (ms_mem ms0) a <> None).
           { intros a Ha. rewrite (KL1 a Ha).
             destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [h1 | h1];
               [exact (sm_av_ne W mem _ 4 0 a LK0 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) |].
             destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [h2 | h2];
               [ exact (sm_av_ne W mem _ 4 0 a LK4 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
               | exact (sm_av_ne W mem _ 4 0 a LK8 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) ]. }
           assert (AVL : aview segs (w_H W) (ms_mem ms0) (rg_lock fr_RG) = Some 0)
             by (rewrite (KL1 (rg_lock fr_RG) ltac:(lia)); exact (sm_av0 W mem _ LK0)).
           assert (LK4m : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (rg_lock fr_RG + 4) 4 0).
           { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms0) (rg_lock fr_RG + 4) (rg_lock fr_RG + 4) 4 0);
               [intros j Hj; apply KL1; cbn in Hj; lia | exact LK4]. }
           eapply SRr_bind.
           { eapply (aj_gx_entry_at B LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
               (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
               (fun (_ : bvmap 5 word) (mem' : word -> option byte) =>
                  val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 16)
               W (ms_regs ms0) (ms_mem ms0) STK sp0 FP ly0 S0 W0 mem0 md0 own ly S _ kk (F - sp0) _ HG eq_refl HJ
               ltac:(rewrite Usp; lia) Hs16 ltac:(lia) ltac:(lia) ltac:(lia) Q3 Q4 Q1
               (ret_ok_codeptr_v 9136 ltac:(lia) eq_refl)).
             - intros a. lia.
             - intros a Ha _. exact (LKV a ltac:(lia)).
             - intros a Ha HnG. exfalso. apply HnG. apply HGlk. lia.
             - intros HPRE2 HSC2.
               exact (ALOCK ly S W (ms_regs ms0) (ms_mem ms0) _ (rg_lock fr_RG) 0 HPRE2 Q10
                 ltac:(lia) ltac:(rewrite HRlk; reflexivity) ltac:(lia) AVL eq_refl LK4m
                 ltac:(intros a Ha; split; [exact (LKV a ltac:(lia)) | rewrite Usp; lia])
                 ltac:(intros a Ha; split;
                       [ apply (sm_wkeep W (ms_mem ms) (ms_mem ms0) a HGb);
                         apply (sm_wkeep W mem (ms_mem ms) a HGa);
                         replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; apply LKW; lia
                       | split; [apply HNOWN; lia | rewrite Usp; lia] ])). }
           cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HLK2 & Hfr2 & Hpres2).
           jafter_call_keep_hi HS 514%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
           match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
           { cbn [ms_mem restrict].
             repeat apply Forall_cons; [| | | | | apply Forall_nil];
               (eapply region_kept_aview; [sm_base | intros a Ha; apply Hfr2; lia | exact Hpres2]). }
           clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
           (* back from the lock: ld a0,24(s1); li a1,-1; sw a1,-512(a0) (g_client := -1); to the unlock *)
           assert (HEIl : img_env VAL A_LIM (havoc (ewset (ewset E 512 w) 513 w0) 514 (map (getr regs2) CLOB)))
             by (apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
           assert (SHOK2 : sh_ok segs sm_Bx []
               (havoc (ewset (ewset E 512 w) 513 w0) 514 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
             by (unfold sh_ok; constructor).
           paj_run_tok RUN HS HJ2 SHOK2 SMspan.
           ++ sm_df_awr.
           ++ rename HF into HFc, HFr into HFrc, HG0 into HGc.
              (* pthread_mutex_unlock (&g_lock): a0 = s4 = A_OBJ 6, kept by the lock *)
              pmkst HS.
              prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
              prreg HS (4%bv : bv 5) R4. prreg HS (10%bv : bv 5) R10.
              rewrite ?ew_ewset_other in R2, R3, R4, R10 by lia.
              rewrite E2 in R2. rewrite E3 in R3. rewrite E4 in R4. rewrite E247 in R10.
              assert (Usp3 : spZ (ms_regs ms1) = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
              assert (KL3 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem2 a).
              { intros a Ha. apply (aview_kept_out _ _ _ _ _ HFrc a ltac:(lia)). sm_notw. }
              assert (KL13 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
                  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a).
              { intros a Ha Hn. rewrite (KL3 a Ha), (Hfr2 a ltac:(lia) Hn ltac:(lia)), (KL1 a Ha). reflexivity. }
              assert (V0u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG) 4 0).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms1) (rg_lock fr_RG) (rg_lock fr_RG) 4 0); [|exact LK0].
                intros j Hj. cbn in Hj. apply KL13; lia. }
              assert (V8u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG + 8) 4 0).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms1) (rg_lock fr_RG + 8) (rg_lock fr_RG + 8) 4 0);
                  [|exact LK8].
                intros j Hj. cbn in Hj. apply KL13; lia. }
              assert (V4u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG + 4) 4 16).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem2 (ms_mem ms1) (rg_lock fr_RG + 4) (rg_lock fr_RG + 4) 4 16);
                  [|exact HLK2].
                intros j Hj. cbn in Hj. apply KL3; lia. }
              assert (AV13 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  aview segs (w_H W) (ms_mem ms1) a <> None).
              { intros a Ha.
                destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [h1 | h1];
                  [exact (sm_av_ne W (ms_mem ms1) _ 4 0 a V0u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) |].
                destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [h2 | h2];
                  [ exact (sm_av_ne W (ms_mem ms1) _ 4 16 a V4u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
                  | exact (sm_av_ne W (ms_mem ms1) _ 4 0 a V8u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) ]. }
              eapply SRr_bind.
              { eapply (aj_gx_entry_at B LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
                  (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
                  (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
                     getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 0)
                  W (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly0 S0 W0 mem0 md0 own ly S _ kk (F - sp0) _ HG eq_refl HJ2
                  ltac:(rewrite Usp3; lia) Hs16 ltac:(lia) ltac:(lia) ltac:(lia) R3 R4 R1
                  (ret_ok_codeptr_v 9160 ltac:(lia) eq_refl)).
                - intros a. lia.
                - intros a Ha _. exact (AV13 a ltac:(lia)).
                - intros a Ha HnG. exfalso. apply HnG. apply HGlk. lia.
                - intros HPRE3 HSC3.
                  exact (AUNLOCK ly S W (ms_regs ms1) (ms_mem ms1) _ (rg_lock fr_RG) HPRE3 R10
                    ltac:(lia) ltac:(rewrite HRlk; reflexivity) ltac:(lia) V0u V4u V8u
                    ltac:(intros a Ha; split; [exact (AV13 a ltac:(lia)) | rewrite Usp3; lia])
                    ltac:(intros a Ha; split;
                          [ apply (sm_wkeep W mem2 (ms_mem ms1) a HGc);
                            apply (writable_kept (w_H W) (ms_mem ms0) mem2 a (Hpres2 a));
                            apply (sm_wkeep W (ms_mem ms) (ms_mem ms0) a HGb);
                            apply (sm_wkeep W mem (ms_mem ms) a HGa);
                            replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; apply LKW; lia
                          | split; [apply HNOWN; lia | rewrite Usp3; lia] ])). }
              cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & [HR10 HLK3] & Hfr3 & Hpres3).
              jafter_call_keep_hi HS 530%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
              match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
              { cbn [ms_mem restrict].
                repeat apply Forall_cons; [| | | | | apply Forall_nil];
                  (eapply region_kept_aview; [sm_base | intros a Ha; apply Hfr3; lia | exact Hpres3]). }
              clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
              (* back from the unlock: li t2,1; then g_gone := 1 and the latch *)
              assert (HEIu : img_env VAL A_LIM (havoc (havoc (ewset (ewset E 512 w) 513 w0) 514
                  (map (getr regs2) CLOB)) 530 (map (getr regs3) CLOB)))
                by (apply img_env_havoc_hi; [exact HEIl | cbv; lia]).
              assert (SHOK3 : sh_ok segs sm_Bx [] (havoc (havoc (ewset (ewset E 512 w) 513 w0) 514
                  (map (getr regs2) CLOB)) 530 (map (getr regs3) CLOB)) (mrestrict (w_H W) mem3))
                by (unfold sh_ok; constructor).
              paj_run_to_tok RUNTO HS HJ3 SHOK3 SMspan AF_LLVM_latch.
              ** sm_df_awr.
              ** lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
                   assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
                     by (apply env_agree_havoc_ge; [cbv; lia|]; apply env_agree_havoc_ge; [cbv; lia|];
                         split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                                | rewrite ?ed_ewset; exact (proj2 HAE)]);
                   assert (EV9 : bv_unsigned (ew Ev 9) = F) by sm_base;
                   assert (EV351 : bv_unsigned (ew Ev 351) = 0x5d81fc) by sm_base;
                   assert (EV352 : bv_unsigned (ew Ev 352) = 0x5d8204) by sm_base;
                   assert (EV347 : bv_unsigned (ew Ev 347) = 0xa21e0) by sm_base;
                   assert (EV29 : bv_unsigned (ew Ev 29) = N1)
                     by (repeat (first [rewrite ew_ewset_other by (cbv; lia) | rewrite ew_havoc_old by (cbv; lia)]);
                         rewrite E29; apply unsigned_lit_small; lia)
                 end.
                 pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
                   ltac:(vm_compute; reflexivity)) as KR.
                 cbn [ms_regs restrict] in KR.
                 prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
                 rewrite ?ew_ewset_other in Q22 by lia. rewrite U28 in Q22.
                 pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
                 pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
                 pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
                 pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
                 cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
                 assert (V144 : val_mem segs (arm W (ms_mem ms2)) (F + 144) 8 (N1 - 1))
                   by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
                       [exact EV9 | left; reflexivity | cbn [sv_denot]; rewrite EV29; f_equal; lia | zside | zside]).
                 assert (Vdd' : val_mem segs (arm W (ms_mem ms2)) (rg_send_dead fr_RG) 1 dd)
                   by (replace (rg_send_dead fr_RG) with (0x5d8204 + 1660) by lia;
                       eapply (field_of_region _ _ 352%nat 0x5d8204 _ _ _ _ _ 1660 1%N _ _ RG2);
                       [exact EV352 | left; reflexivity | reflexivity | zside | zside]).
                 assert (Vgn' : val_mem segs (arm W (ms_mem ms2)) (rg_gone fr_RG) 1 1)
                   by (replace (rg_gone fr_RG) with (0x5d81fc + 1636) by lia;
                       eapply (field_of_region _ _ 351%nat 0x5d81fc _ _ _ _ _ 1636 1%N _ _ RG3);
                       [exact EV351 | left; reflexivity | reflexivity | zside | zside]).
                 assert (Vcl' : val_mem segs (arm W (ms_mem ms2)) (rg_client fr_RG) 4 (2 ^ 32 - 1))
                   by (replace (rg_client fr_RG) with (0xa21e0 + -512) by lia;
                       eapply (sm_val_m1 _ _ 347%nat 0xa21e0 _ _ _ _ _ (-512) _ RG4);
                       [ exact EV347 | left; reflexivity
                       | cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity ]).
                 assert (VLK : val_mem segs (arm W (ms_mem ms2)) (rg_lock fr_RG + 4) 4 0).
                 { apply (val_mem_moved segs (w_H W) (w_H W) mem3 (ms_mem ms2) (rg_lock fr_RG + 4)
                     (rg_lock fr_RG + 4) 4 0); [|exact HLK3].
                   intros j Hj. cbn in Hj.
                   apply (aview_kept_out _ _ _ _ _ HFr (rg_lock fr_RG + 4 + j) ltac:(lia)). sm_notw. }
                 pmkst HS. apply SRr_ret. unfold sm_df_post; cbv beta. split; [reflexivity|].
                 exists true. do 3 eexists. split; [rewrite EN, Hodd; reflexivity|].
                 split; [reflexivity|]. split; [exact HJ3|].
                 split.
                 { apply (sm_kept_trans W mem (ms_mem ms) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFra HGa); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms) (ms_mem ms0) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ (ms_mem ms) (ms_mem ms0) _ HFrb HGb); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms0) mem2 (ms_mem ms2));
                     [ apply (sm_kept_call W (ms_mem ms0) mem2 _ _ _ _ Hfr2 Hpres2); intros a Ha; cbv beta in Ha;
                       unfold XS, sm_df_XG; cbn [app]; sm_inFP |].
                   apply (sm_kept_trans W mem2 (ms_mem ms1) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ mem2 (ms_mem ms1) _ HFrc HGc); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms1) mem3 (ms_mem ms2));
                     [ apply (sm_kept_call W (ms_mem ms1) mem3 _ _ _ _ Hfr3 Hpres3); intros a Ha; cbv beta in Ha;
                       unfold XS, sm_df_XG; cbn [app]; sm_inFP |].
                   apply (sm_kept_run W _ _ mem3 (ms_mem ms2) _ HFr HG0); sm_inX. }
                 split.
                 { apply (mem_grows_trans _ _ _ HGa). apply (mem_grows_trans _ _ _ HGb).
                   apply (mem_grows_trans _ _ _ (sm_grows_of_pres W _ _ Hpres2)). apply (mem_grows_trans _ _ _ HGc).
                   apply (mem_grows_trans _ _ _ (sm_grows_of_pres W _ _ Hpres3)). exact HG0. }
                 split; [rewrite EN; exact V144|].
                 split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
                 split; [intros _; exact VLK|].
                 split; [exact KR|]. split; [exact Q20|]. rewrite EN; exact Q22.
Qed.

(* ---- the cut's facts after arm 9 *)
Lemma sm_df_xgok : forall g, XGOK (sm_df_XG g).
Proof.
  intros g a Ha. unfold sm_df_XG in Ha. destruct g; cbn [app] in Ha;
    repeat (apply inFP_cons in Ha as [Ha | Ha]; [sm_rgl|]); destruct (inFP_nil a Ha).
Qed.
(* a byte that is in none of the stored globals (g concrete) *)
Ltac sm_nXG Hin :=
  unfold sm_df_XG in Hin; cbn [app] in Hin;
  repeat (apply inFP_cons in Hin as [Hin | Hin]; [sm_rgl|]); exact (inFP_nil _ Hin).
(* the controller's stream: on an odd byte (g) g_client = -1 and g_send_dead as it was, else g_send_dead = 1 and
   g_client as it was; every other cell as it was *)
Lemma sm_aout_df : forall ly S (W : world segs) mem md mem' F c O mx no cap out (g : bool),
  AR segs B ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> KEPT W mem mem' (XS F (sm_df_XG g)) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  val_mem segs (arm W mem') (rg_send_dead fr_RG) 1 (if g then ct_dd c else 1) ->
  val_mem segs (arm W mem') (rg_client fr_RG) 4 (if g then 2 ^ 32 - 1 else ct_cl c mod 2 ^ 32) ->
  aout_at B fr_RG ly S W mem'
    (CTL (if g then -1 else ct_cl c) (ct_br c) (if g then ct_dd c else 1) (ct_ei c) (ct_ev c)) O mx no cap out.
Proof.
  intros ly S W mem md mem' F c O mx no cap out g HAR HF HK HGr Ho Vdd Vcl.
  pose proof (sm_df_xgok g) as HXG.
  assert (HXOK : XOK (XS F (sm_df_XG g))) by (apply sm_xok; [exact HF | exact HXG]).
  pose proof sm_ceil_lo as Hac. pose proof sm_errno as (HE0 & HE1). pose proof HERRHI as HEH.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (CK : forall a, aout_glob a -> ~ (rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1) ->
      ~ (rg_client fr_RG <= a < rg_client fr_RG + 4) -> abyte_kept W mem W mem' a).
  { intros a Ha H1 H2. apply (sm_kept_ng W mem mem' F (sm_df_XG g) HK);
      [unfold aout_glob in Ha; sm_rgl | unfold aout_glob in Ha; sm_rgl | unfold aout_glob in Ha; sm_rgl |].
    intros Hin. unfold aout_glob in Ha. destruct g; sm_nXG Hin. }
  assert (KV : forall a n v, (forall x, a <= x < a + Z.of_nat n -> aout_glob x) ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (rg_send_dead fr_RG <= x < rg_send_dead fr_RG + 1)) ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (rg_client fr_RG <= x < rg_client fr_RG + 4)) ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v).
  { intros a n v H1 H2 H3 Hv. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. apply CK; [exact (H1 x Hx) | exact (H2 x Hx) | exact (H3 x Hx)]. }
  destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 &
    O19 & O20 & O21 & O22 & O23 & O24 & O25 & O26).
  unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [sm_kv KV O1|]. split; [exact (sm_awr W mem mem' _ _ HGr O2)|].
  split; [sm_kv KV O3|]. split; [exact (sm_awr W mem mem' _ _ HGr O4)|].
  split; [sm_kv KV O5|]. split; [exact (sm_awr W mem mem' _ _ HGr O6)|].
  split; [sm_kv KV O7|]. split; [exact (sm_awr W mem mem' _ _ HGr O8)|].
  split; [destruct g; exact Vcl|]. split; [exact (sm_awr W mem mem' _ _ HGr O10)|].
  split; [sm_kv KV O11|]. split; [exact (sm_awr W mem mem' _ _ HGr O12)|].
  split; [destruct g; exact Vdd|]. split; [exact (sm_awr W mem mem' _ _ HGr O14)|].
  split; [sm_kv KV O15|]. split; [exact (sm_awr W mem mem' _ _ HGr O16)|].
  split; [sm_kv KV O17|]. split; [exact (sm_awr W mem mem' _ _ HGr O18)|].
  split; [exact O19|]. split; [destruct g; [right; reflexivity | exact O20]|].
  split; [exact O21|]. split; [destruct g; [exact O22 | right; reflexivity]|].
  split; [exact O23|]. split; [exact O24|]. split; [exact O25|].
  destruct O26 as [O26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact O26 | right].
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|]. exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply (sm_blk_kept ly S W mem md mem' (XS F (sm_df_XG g)) out cap x HAR HXOK HK Hin).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

(* the model after arm 9: the stream's flags, g_gone = 1, the lock free again, the cursor; the rest as it was *)
Lemma sm_amodel_df : forall ly S (W : world segs) mem md mem' F cx m (g : bool),
  AR segs B ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F ->
  KEPT W mem mem' (XS F (sm_df_XG g)) -> mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  amodel_at B ly S W mem m -> lm_O m = [] ->
  val_mem segs (arm W mem') (rg_send_dead fr_RG) 1 (if g then ct_dd (lm_c m) else 1) ->
  val_mem segs (arm W mem') (rg_gone fr_RG) 1 1 ->
  val_mem segs (arm W mem') (rg_client fr_RG) 4 (if g then 2 ^ 32 - 1 else ct_cl (lm_c m) mod 2 ^ 32) ->
  (g = true -> val_mem segs (arm W mem') (rg_lock fr_RG + 4) 4 0) ->
  amodel_at B ly S W mem' (sm_default cx m g).
Proof.
  intros ly S W mem md mem' F cx m g HAR HF HK HGr HM HO Vdd Vgn Vcl Vlk.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  pose proof (sm_df_xgok g) as HXG.
  assert (CK : forall lo n, 0 <= lo -> lo + n <= alloc_ceiling -> (forall a, lo <= a < lo + n -> ~ inFP (sm_df_XG g) a) ->
      forall a, lo <= a < lo + n -> abyte_kept W mem W mem' a).
  { intros lo n H0 H1 Hd. apply (sm_cell_kept W mem mem' F (sm_df_XG g) lo n HK); [lia | lia | lia | exact Hd]. }
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  unfold amodel_at, sm_default. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [exact M1|].
  split.
  { intros j Hj. apply (sm_aslot_kept ly S W mem md mem' F (sm_df_XG g) j _ HAR HF HXG HK HGr Hj); [|exact (M2 j Hj)].
    intros a Ha Hin. destruct g; sm_nXG Hin. }
  split.
  { apply (sm_arelay_kept ly S W mem md mem' F (sm_df_XG g) (lm_G m) (lm_es m) HAR HF HXG HK); [|exact M3].
    intros a Ha Hin. destruct g; sm_nXG Hin. }
  split.
  { rewrite HO in M4. exact (sm_aout_df ly S W mem md mem' F _ _ _ _ _ _ g HAR HF HK HGr M4 Vdd Vcl). }
  split.
  { split; [exact Vgn|]. split; [exact (sm_awr W mem mem' _ _ HGr (proj1 (proj2 M5)))|]. right; reflexivity. }
  split.
  { pose proof M6 as (L0 & L4 & L8 & LW). destruct g.
    - split; [|split; [|split]].
      + apply (akept_vm W mem); [|exact L0]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
        apply (CK (rg_lock fr_RG) 4); [sm_rgl | sm_rgl | intros y Hy Hin; sm_nXG Hin | lia].
      + exact (Vlk eq_refl).
      + apply (akept_vm W mem); [|exact L8]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
        apply (CK (rg_lock fr_RG + 8) 4); [sm_rgl | sm_rgl | intros y Hy Hin; sm_nXG Hin | lia].
      + exact (sm_awr W mem mem' _ _ HGr LW).
    - apply (alock_at_kept fr_RG W mem W mem' _ M6). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      apply (CK (rg_lock fr_RG) 12); [sm_rgl | sm_rgl | intros y Hy Hin; sm_nXG Hin | exact Ha]. }
  split.
  { apply (awake_at_kept fr_RG W mem W mem' M7). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_wake fr_RG + 4) 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply (CK AG_THREAD_UP 1); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  split.
  { destruct M12 as (lst & M12). exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx.
    apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia].
Qed.

(* ---------------------------------------------------------------- ARM_default (_cut.v :584) *)
Theorem lf_arm_default : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_A B G_fr fr_FP LS RINV 9 cx t W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep & HLS & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD6 & HD7 & HD27 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = 9).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk9 : picks 9 = false) by reflexivity.
  rewrite Hpk9 in Hpick. destruct Hpick as (HD28 & HD29 & _).
  assert (HAR : AR segs B ly3 S3 W mem md)
    by (exact (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (HF16 : (lf_F cx - sp0) mod 16 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite HFmod in D1. rewrite Hsp16 in D2.
    replace (lf_F cx - sp0) with ((2 * (lf_F cx / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  assert (Hr2 : getr regs 2 = w64 (lf_F cx)) by (rewrite (KD 2%bv ltac:(sm_in)); exact C2).
  assert (Hr3 : getr regs 3 = w64 (as_gp B)) by (rewrite (KD 3%bv ltac:(sm_in)); exact C3).
  assert (Hr4 : getr regs 4 = w64 (as_tp B)) by (rewrite (KD 4%bv ltac:(sm_in)); exact C4).
  assert (Hr7 : getr regs 7 = w64 1) by (rewrite (KD 7%bv ltac:(sm_in)); exact HD7).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr20 : getr regs 20 = w64 10) by (rewrite (KD 20%bv ltac:(sm_in)); exact C20).
  assert (Hr26 : getr regs 26 = w64 SB) by (rewrite (KD 26%bv ltac:(sm_in)); exact C26).
  assert (Hr28 : getr regs 28 = w64 (c_p cx + lm_k m + 1)) by (rewrite (KD 28%bv ltac:(sm_in)); exact HD28).
  assert (Hr29 : getr regs 29 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KD 29%bv ltac:(sm_in)); exact HD29).
  (* the input block and the byte in.p[0] *)
  pose proof Hinput as [[[Hn0 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hblk) as Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (sm_in_byte_rng cx (lm_k m + 1)) as Hkb8.
  (* the frame's three address copies, the stream's two flags, g_gone and the lock *)
  pose proof Hframe as (_ & Hawr & F24 & F48 & _ & F64 & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Hmodel as (_ & _ & _ & Hout & Hgone & Hlock & _).
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & Ocl & Owcl & _ & _ & Odd & Owdd & _ & _ & _ & _ & _ & _ & _ &
    Odd01 & _).
  pose proof Hgone as (_ & Owgn & _).
  rewrite Hc.
  eapply SRr_mono.
  { exact (sm_df_run W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 kk (lf_F cx) (c_p cx + lm_k m + 1) (c_n cx - lm_k m - 1) (in_byte cx (lm_k m + 1))
      (ct_dd (lm_c m)) (ct_cl (lm_c m) mod 2 ^ 32)
      HJ Hr2 Hr3 Hr4 Hr7 Hr9 Hr20 Hr26 Hr28 Hr29 ltac:(lia) HFbound HFmod ltac:(lia) Hkb8 ltac:(lia) HF16
      ltac:(lia)
      ltac:(intros HN; unfold off_img in Hpimg; lia)
      ltac:(intros HN; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; rewrite <- Z.add_assoc; exact (proj1 (sm_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))))
      ltac:(intros HN; apply (range_addressable_of_block segs B LAWS ly3 S3 W mem md (c_p cx) (c_n cx));
            [exact HAR | exact Hblk | lia | lia])
      F24 F48 F64 HW1 Odd ltac:(lia) Owdd Owgn Ocl ltac:(apply Z.mod_pos_bound; lia) Owcl Hlock). }
  intros W' c' _ (-> & g & regs' & mem' & md' & Hg & -> & HJ' & KP & HGr & V144 & Vdd & Vgn & Vcl & Vlk & KR & Q20 &
    Q22).
  assert (Hgd : g = sm_dg cx m).
  { rewrite Hg. unfold sm_dg. destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
    - replace (c_n cx - lm_k m - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - replace (c_n cx - lm_k m - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
  pose proof (sm_df_xgok g) as HXG.
  assert (HXOK : XOK (XS (lf_F cx) (sm_df_XG g))) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_df_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, kk, (sm_default cx m g), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept cx true ly3 S3 W mem md mem' fpos (sm_df_XG g) HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept cx ly3 S3 W mem md mem' fpos (sm_df_XG g) HAR Hfin Hsp0 HXG KP HGr Hflag)|].
  split; [exact (sm_amodel_df ly3 S3 W mem md mem' (lf_F cx) cx m g HAR ltac:(lia) KP HGr Hmodel HO Vdd Vgn Vcl Vlk)|].
  split; [exact (sm_ainput_kept cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [exact Hsep|].
  split; [rewrite Hgd; exact (LS_default cx t m ly3 S3 HLS)|].
  split; [rewrite Hgd; exact (RI_default cx t m HRINV)|].
  unfold lregs_K, lregs_common, sm_default. cbn [lm_k]. unfold sm_kn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [exact Q20|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact C25|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact HD27|].
  split; [exact Htb|].
  unfold sv8.
  destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite EN in Q22, V144. cbv iota in Q22, V144.
    split; [rewrite Q22; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 2)) with (c_n cx - lm_k m - 1 - 1) by lia; exact V144|]. lia.
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = true) by (apply Z.eqb_eq; lia).
    rewrite EN in Q22, V144. cbv iota in Q22, V144.
    split; [rewrite Q22; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 1)) with 0 by lia; exact V144|]. lia.
Qed.

End sm.
