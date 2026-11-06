(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Shared helpers for the segment lemmas of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B): the run lemma
   sl_run (an evt run into SR Post, via PContract.evt_SR_canon; the asan evt already runs on the real memory, so
   there is no normalize step as in the ubsan twin), the ADDR-KEEP lemma sl_addr_keep (addressable survives a run
   that writes only app memory), and the frame-and-shadow transport of FRA. The side-stack package lemmas
   (FSFREE, fra_fp, fsfree_post, tls_fra, fra_rbe_tls) live in Seg/Tac_fsfree.v, exported from here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFP asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Export Tac_fsfree.
Import ListNotations.
(* A later import shadows YK11.getr (used by FRA); restore it as the default so register equalities match FRA. *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
(* The lib/Lib Frame / Mem modules used by ckv_fra's statement (a Theorem Labs lane, lib/B/Prog/Seg/F20.v). *)
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
(* The UL engine's copy of the write-set predicate (lib/B/Tk/UL/Frame.v, exported by lib/B/Tk/UL/Tac.v), next to
   LFr above, which is the lib/Lib copy the callee contracts use: see fr_outside_lib / fr_munch_ul below. *)
Module ULFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Frame.
(* The side-stack frame package of the callee contracts and the interval-apartness predicate it is built on
   (fra_callee_fp below). *)
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module ASM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module RLay := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.

(* ADDR-KEEP (plan 7): a buffer that is addressable in m is still addressable after a run whose writes W are all in
   app memory (so the shadow bytes it reads are kept): addressable_kept composed with munch_meta. *)
Lemma sl_addr_keep : forall m m' W p n,
  addressable m p n -> Frame.munch W m m' -> all_app W -> addressable m' p n.
Proof.
  intros m m' W p n H MU AW. exact (addressable_kept m m' p n H (munch_meta W m m' MU AW)).
Qed.

(* One addressable byte: its app-memory range and its shadow byte. *)
Lemma addr1_app : forall m a, addressable m a 1 -> app_mem a.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m a (_ & _ & _ & H). destruct (H 0 ltac:(lia)) as (Ha & _).
  rewrite Z.add_0_r in Ha. exact Ha.
Qed.

(* and so one addressable byte survives a run that leaves its shadow byte alone (the finer form of sl_addr_keep,
   for a run that does write some shadow bytes). *)
Lemma addr1_munch : forall W m m' a, Frame.munch W m m' ->
  Frame.outside W (shadow_addr a) -> addressable m a 1 -> addressable m' a 1.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros W m m' a MU Ho (H1 & H2 & H3 & H).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. assert (Ei : i = 0) by lia. subst i.
  destruct (H 0 ltac:(lia)) as (Happ & b & Hb & Hok).
  pose proof (shadow_of_app (a + 0) Happ) as His.
  destruct (in_shadow_range (shadow_addr (a + 0)) His) as (R1 & R2).
  assert (Hmb : mbyte rsegs m' (shadow_addr (a + 0)) = mbyte rsegs m (shadow_addr (a + 0))).
  { apply (mbyte_munch rsegs W m m' (shadow_addr (a + 0)) MU ltac:(lia)).
    rewrite Z.add_0_r. exact Ho. }
  split; [exact Happ|]. exists b. split; [|exact Hok]. exact (eq_trans Hmb Hb).
Qed.

(* OUTA (SlotInv.v, out[]'s 1492 bytes addressable) across a run whose writes are all app memory (no shadow byte
   changes): sl_addr_keep. *)
Lemma outa_munch : forall W fr m m', OUTA fr m -> Frame.munch W m m' -> all_app W -> OUTA fr m'.
Proof. intros W fr m m' H MU AW. unfold OUTA in *. exact (sl_addr_keep m m' W (fr + 544) 1492 H MU AW). Qed.

(* and across a run that writes shadow bytes, none of them out[]'s (the round-trip loop's own shadow stores are at
   296..323(s3), out[]'s shadow is S(fr) + 68 .. S(fr) + 254): addr1_munch byte by byte. *)
Lemma outa_run : forall W fr m m', OUTA fr m -> Frame.munch W m m' ->
  (forall i, 0 <= i < 1492 -> Frame.outside W (shadow_addr (fr + 544 + i))) -> OUTA fr m'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros W fr m m' HO MU HW. unfold OUTA in *.
  pose proof HO as (H1 & H2 & H3 & _).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi.
  pose proof (addressable_sub m (fr + 544) 1492 i 1 HO ltac:(lia) ltac:(lia) ltac:(lia)) as Hi1.
  destruct (addr1_munch W m m' (fr + 544 + i) MU (HW i Hi) Hi1) as (_ & _ & _ & Hb).
  specialize (Hb 0 ltac:(lia)). rewrite Z.add_0_r in Hb. exact Hb.
Qed.

(* The copy window of turn b (R8's checked_memcpy source): a prefix of out[]. The premise is the count's bound,
   which SlotModel's rt_n = 52 + 36 * rt_uw does not give by itself. *)
Lemma outa_rnb : forall g b fr m, OUTA fr m -> 0 <= rnb g b <= 1492 -> addressable m (fr + 544) (rnb g b).
Proof. intros g b fr m H Hb. unfold OUTA in H. exact (addressable_prefix m (fr + 544) 1492 (rnb g b) H Hb). Qed.

(* An addressable range survives a run that leaves the shadow byte of each of its bytes alone (outa_run's
   argument, for any range). *)
Lemma addr_run : forall W m m' p n, addressable m p n -> Frame.munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros W m m' p n HO MU HW.
  pose proof HO as (H1 & H2 & H3 & _).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi.
  pose proof (addressable_sub m p n i 1 HO ltac:(lia) ltac:(lia) ltac:(lia)) as Hi1.
  destruct (addr1_munch W m m' (p + i) MU (HW i Hi) Hi1) as (_ & _ & _ & Hb).
  specialize (Hb 0 ltac:(lia)). rewrite Z.add_0_r in Hb. exact Hb.
Qed.

(* FRA's input facts (SlotInv.v: the input bytes at p and, for n > 0, the block (p, n) live and addressable)
   survive a run whose writes miss the input block: the bytes by fl_bytes, the addressability by sl_addr_keep when
   every write is app memory (fra_in_keep), or by addr_run when the run also misses the block's shadow bytes
   (fra_in_keep_sh). *)
Lemma fra_in_keep : forall g m m' W,
  bytes_at rsegs m (g_p g) (g_in g) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable m (g_p g) (g_n g)) ->
  Frame.munch W m m' -> all_app W ->
  (forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x) ->
  bytes_at rsegs m' (g_p g) (g_in g) /\
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable m' (g_p g) (g_n g)).
Proof.
  intros g m m' W Hb Hblk MU AW HW. split.
  - eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply HW. unfold g_n, nlen. exact Hx.
  - intros Hn. destruct (Hblk Hn) as (Hin & Had). split; [exact Hin|].
    exact (sl_addr_keep m m' W (g_p g) (g_n g) Had MU AW).
Qed.

Lemma fra_in_keep_sh : forall g m m' W,
  bytes_at rsegs m (g_p g) (g_in g) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable m (g_p g) (g_n g)) ->
  Frame.munch W m m' ->
  (forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  bytes_at rsegs m' (g_p g) (g_in g) /\
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable m' (g_p g) (g_n g)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g m m' W Hb Hblk MU HW. split.
  - eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply (proj1 (HW x ltac:(unfold g_n, nlen; lia))).
  - intros Hn. destruct (Hblk Hn) as (Hin & Had). split; [exact Hin|].
    apply (addr_run W m m' (g_p g) (g_n g) Had MU). intros i Hi. exact (proj2 (HW (g_p g + i) ltac:(lia))).
Qed.

Section R.
Context {fx : FPState}.

(* The asan run lemma: an evt from the real config at pc that ends at some pc' with the register/memory predicate K
   lifts to SR Post. The asan model carries lazy pages (a_call_post may add backing), so the bridge is the lazy
   AsanLift.evt_SR_canon_lazy (no m_vm_lazy = [] premise); the end model is some md' with mat_le md md', which the
   continuation receives (FRA is moved to md' by sl_fra_mat). The asan evt runs on the real memory (no normalize);
   SmLib.ul_entry carries the UL engine's evt into Lib.Exec.evt. *)
Lemma sl_run : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  Exec.evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  apply ul_entry in HE.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* The same lift for a run stated in the Lib engine (a Theorem Labs lane, lib/B/Prog/Seg/F7.v): the callee contracts
   reac_ctrl_kind_name_c / bcmp_wrap_c speak Lib.Exec.evt, so this is sl_run without its ul_entry step. *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

End R.

(* Lazy-page materialization keeps the fd table (the file-descriptor state frame of mat_le), so it keeps a model's
   sink_none third clause. *)
Lemma sl_mat_fds : forall md md', AsanLift.mat_le md md' -> m_fds md' = m_fds md.
Proof.
  intros md md' H. destruct (AsanLift.mat_le_frame md md' H) as (Hfd & _). unfold m_fds. rewrite Hfd. reflexivity.
Qed.

(* The wrapper_bcmp stack-scratch size (lib/B/Prog/bcmp_wrap_c.v BCMP_WRAP_K = 4560), so bcmp_fra matches the F18
   cuts. *)
Local Definition BCMP_WRAP_K := 4560.

(* Every runtime cell of rt_disjoint lies in the image, below HIGHMEM_BEG: a write above HIGHMEM_BEG misses them
   (a Theorem Labs lane, lib/B/Prog/Seg/F20.v). *)
Lemma rt_disjoint_hi : forall lo hi, HIGHMEM_BEG <= lo -> rt_disjoint [(lo, hi)].
Proof.
  intros lo hi H. unfold rt_disjoint. simpl.
  repeat match goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- _ \/ _ => left; apply (Z.le_trans _ HIGHMEM_BEG _); [apply Z.leb_le; vm_compute; reflexivity | exact H]
  end.
Qed.

(* A cell A' + d (0 <= d < 448) of the spill base A' = s1 is outside the wrapper's stack scratch [sp - K, sp) when
   s1 = A >= sp; the two spill bases agree (a Theorem Labs lane, lib/B/Prog/Seg/F18.v). *)
Lemma spill_outW : forall regs A A' sp x,
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> sp <= A -> rg regs 9 A' ->
  BCMP_WRAP_K + 448 <= sp -> sp <= 2 ^ 64 ->
  A' <= x < A' + 448 -> Frame.outside [(sp - BCMP_WRAP_K, sp)] x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros regs A A' sp x Hs1 HAb HspA HA' Hk Hsp Hx.
  cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
  unfold BCMP_WRAP_K in *.
  assert (Hb' : 0 <= A' < 2 ^ 64) by lia.
  assert (EA' : A' = A).
  { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in *; rewrite <- HA'; exact Hs1).
    apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
  subst A'. lia.
Qed.

(* x < lo or hi <= x puts x outside one interval (a Theorem Labs lane, lib/B/Prog/Seg/F18.v). *)
Lemma out1 : forall lo hi x, (x < lo \/ hi <= x) -> Frame.outside [(lo, hi)] x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv. intros lo hi x H. cbn [Frame.outside]. split; [lia | exact I]. Qed.

(* Two copies of the write-set predicate are in scope in a segment file: the one the callee contracts and the
   runtime lemmas are stated with (lib/Lib/Frame.v, LFr) and the one the UL step engine brings in
   (lib/B/Tk/UL/Frame.v, ULFr, exported by lib/B/Tk/UL/Tac.v). They have the same body, so each implies the
   other by induction on the interval list; munch follows because it reads outside contravariantly. A segment
   that holds a callee's `munch` in one flavour and needs the other uses these instead of its own copy. *)
Lemma fr_outside_lib : forall W x, ULFr.outside W x <-> LFr.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [ULFr.outside LFr.outside]; [tauto|].
  split; intros [H1 H2]; (split; [exact H1 | apply (IH x); exact H2]).
Qed.

Lemma fr_munch_ul : forall W m m', LFr.munch W m m' <-> ULFr.munch W m m'.
Proof.
  intros W m m'. unfold LFr.munch, ULFr.munch. split; intros H x Hx; apply H; apply (fr_outside_lib W); exact Hx.
Qed.

(* fp for a callee's window [lo', hi') inside [lo, hi), with writes W' and data ranges D' that W and D cover,
   and the last range of an apart list shrunk: the two fp lemmas fra_callee_fp needs. Image A keeps both in
   lib/A/Prog/RcAsanFPLib.v (391-411); image B's RcAsanFPLib.v has neither, and B's copies sit inside
   lib/B/Prog/reac_ctrl_classify_box_frame.v (356-375), a 1500-line segment proof that a shared helper file must
   not depend on, so the two proofs are repeated here over lib/B/Prog/RcAsanFP.v's fp / fp_dj. *)
Lemma fl_fp_sub : forall cs m TP FS lo hi W D lo' hi' W' D',
  FP.fp cs m TP FS lo hi W D -> lo <= lo' -> hi' <= hi ->
  (forall X, FP.fp_dj W X -> FP.fp_dj W' X) -> (forall X, FP.fp_dj D X -> FP.fp_dj D' X) ->
  FP.fp cs m TP FS lo' hi' W' D'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros cs m TP FS lo hi W D lo' hi' W' D' (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA &
    HWd & HDd) H1 H2 HW HD.
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
  split; [exact HCL|]. split; [lia|]. split; [intros a Ha; apply HA; lia|].
  split; [apply HW; exact HWd | apply HD; exact HDd].
Qed.

Lemma fl_dj_last : forall L X a b a' b', FP.fp_dj L (X ++ [(a, b)]) -> a <= a' -> b' <= b ->
  FP.fp_dj L (X ++ [(a', b')]).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros L X a b a' b' H H1 H2. unfold FP.fp_dj in *. eapply Forall_impl; [|exact H]. intros w Hw. cbn beta in Hw.
  apply Forall_app in Hw as [Hx Hy]. apply Forall_app. split; [exact Hx|].
  apply Forall_cons_iff in Hy as [Hy _]. constructor; [|constructor]. unfold RLay.ly_dj in *.
  cbn [fst snd] in *. lia.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* FSREC (the side-arm FakeStack frame record of SlotInv.v) moves across a run that writes no app byte outside
   the frame body [fr + 24, fr + 3136): the tp word, the class-6 flag byte and the slot's last word are all app
   bytes outside that range. The flag byte is below the frames (fs_flag FS 6 j < FS + 36864, and class 6 starts
   at FS + 6328320) and the slot's last word is at fr + 4088, above the frame body; the tp word is in the low
   image. a_laws_fs_place gives the FakeStack's app-memory range, which covers the flag and the slot word.
   The premise is the app-memory form, so it also serves the runs that rewrite the frame's own shadow bytes
   (sl_fr_meta): a shadow byte is never app memory. *)
Lemma fsrec_munch : forall hb mem mem' md W fr,
  FSREC fr mem ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) hb mem md ->
  Frame.munch W mem mem' ->
  (forall x, app_mem x -> ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x) ->
  FSREC fr mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros hb mem mem' md W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH MU HW.
  destruct (lw_fs_place (APIf rc) hb mem md FS HAH Htp HFSr) as [HGTb _ _ Happ].
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HB6 : ASM.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : ASM.fs_M 6 = 256) by reflexivity.
  assert (Hfl : ASM.fs_flag FS 6 j = FS + 36352 + j) by (unfold ASM.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold ASM.fs_frame, ASM.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hap : app_mem (AC.as_tp AC.ASYMS + Z.of_nat k))
      by (unfold app_mem, LOWMEM_END, AC.as_tp, AC.ASYMS; cbn; left; lia).
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64)
      by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by exact Hx.
      apply HW; [exact Hap | unfold AC.as_tp, AC.ASYMS; cbn; lia]. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HW; [|lia].
    replace x with (ASM.fs_flag FS 6 j) by lia. apply Happ. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply HW; [|rewrite HB6 in *; lia].
    apply Happ. rewrite HB6 in *. lia. }
Qed.

(* The same transport for a run that MAY write app bytes outside the frame body, as long as it writes nothing
   below the real stack's low bound stklo: the callee-window runs (bcmp_fra, ckv_fra, sl_callee_keep), whose write
   set lies in [sp - K, sp) with stklo <= sp - FN_STACK <= sp - K (fra_win). The three
   FSREC byte groups are all below stklo: a_laws_fs_place puts the whole FakeStack there (FS + FS_SIZE <= stklo),
   the tp word is in the image below GT <= FS, the flag byte is FS + 36352 + j, and the slot's last word is
   fr + 4088 = FS + 6328320 + j * 4096 + 4088 with j < 256, so below FS + FS_SIZE. Image A states it as fsrec_stklo
   (lib/A/Prog/Seg/Tac_slot.v:276) and fra_fsrec_stklo (:319) for its callee-window helpers (the gap once reported to a Theorem Labs lane is closed). *)
Lemma fsrec_munch_lo : forall hb mem mem' md W fr,
  FSREC fr mem ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) hb mem md ->
  Frame.munch W mem mem' ->
  (forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x) ->
  FSREC fr mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros hb mem mem' md W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH MU HW.
  destruct (lw_fs_place (APIf rc) hb mem md FS HAH Htp HFSr) as [HGTb Hend _ _].
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HB6 : ASM.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : ASM.fs_M 6 = 256) by reflexivity.
  assert (Hfl : ASM.fs_flag FS 6 j = FS + 36352 + j) by (unfold ASM.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold ASM.fs_frame, ASM.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64)
      by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by exact Hx.
      apply HW; unfold AC.as_tp, AC.ASYMS in *; cbn in *; lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HW; lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply HW; rewrite HB6 in *; lia. }
Qed.

(* fsrec_munch_lo in the form of the FSREC premise of sl_fr_cl, sl_win_run and sl_stk_run (image A's premise
   `FSREC fr mem -> FSREC fr mem'`): a caller whose write set misses everything below stklo outside the frame body
   gets it here. *)
Lemma fsrec_stklo : forall hb mem mem' md W fr,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) hb mem md -> Frame.munch W mem mem' ->
  (forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md -> ~ (fr + 24 <= x < fr + FRAME_BYTES) ->
     Frame.outside W x) ->
  (FSREC fr mem -> FSREC fr mem').
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros hb mem mem' md W fr HAH MU HW Hrec. exact (fsrec_munch_lo hb mem mem' md W fr Hrec HAH MU HW).
Qed.

(* The transport for a run that writes spills AND the frame's own shadow bytes (prover a Theorem Labs lane's A3 / A4 segments):
   its write set may hold app bytes outside the frame [fr, fr + 3136) only at or above stklo, and any non-app
   byte (a shadow byte). Each of the three FSREC byte groups is app memory below stklo and outside the frame:
   the tp word is in the low image (below GT <= FS <= fr), the flag byte FS + 36352 + j is below
   fr = FS + 6328320 + j * 4096, and the slot's last word [fr + 4088, fr + 4096) is above the frame and below
   FS + FS_SIZE <= stklo (a_laws_fs_place, which also gives the FakeStack's app-memory range). *)
Lemma fsrec_keep_app_lo : forall hb mem mem' md W fr,
  FSREC fr mem ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) hb mem md ->
  Frame.munch W mem mem' ->
  (forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr <= x < fr + FRAME_BYTES) -> Frame.outside W x) ->
  FSREC fr mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros hb mem mem' md W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH MU HW.
  destruct (lw_fs_place (APIf rc) hb mem md FS HAH Htp HFSr) as [HGTb Hend _ Happ].
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HB6 : ASM.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : ASM.fs_M 6 = 256) by reflexivity.
  assert (Hfl : ASM.fs_flag FS 6 j = FS + 36352 + j) by (unfold ASM.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold ASM.fs_frame, ASM.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hap : app_mem (AC.as_tp AC.ASYMS + Z.of_nat k))
      by (unfold app_mem, LOWMEM_END, AC.as_tp, AC.ASYMS; cbn; left; lia).
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64)
      by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by exact Hx.
      apply HW; [exact Hap | |]; unfold AC.as_tp, AC.ASYMS in *; cbn in *; lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HW; [| lia | lia].
    replace x with (ASM.fs_flag FS 6 j) by lia. apply Happ. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply HW; [| rewrite HB6 in *; lia | rewrite HB6 in *; lia].
    apply Happ. rewrite HB6 in *. lia. }
Qed.

(* FRA moves across a register change that keeps the FRA registers (sp 2, gp 3, tp 4, s0 8, s1 9, s3 19) and across
   lazy-page materialization (mat_le md md'): the only md-dependent conjuncts are RT (RT_any), AH and stklo
   (a_laws_mat_le), m_halted (mat_le_halted) and sink_none (sl_mat_fds); the rest read mem / regs / ghost only.
   Push 5c's conjuncts (the fr reload spill [A + 40], the window's addressability, the three ENTRY stack-top
   facts) read mem or the ghost alone, so they move unchanged. *)
Lemma sl_fra_move : forall g fr hb regs regs' mem md md',
  FRA B APIf ra g fr hb regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem md'.
Proof.
  intros g fr hb regs regs' mem md md' HFRA E2 E3 E4 E8 E9 E19 E26 Hmat.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct (lw_mat_le (APIf rc) (hb ++ g_H g) mem md md' Hmat) as [HAHm _ Hstklo_eq _].
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_any sp sp mem md md' HRT)|].
  split; [exact (HAHm HAH)|].
  split; [exact Hro|].
  split; [destruct Hsn as (He & Hh & Hf); split; [exact He|];
          split; [exact Hh|]; rewrite (sl_mat_fds md md' Hmat); exact Hf|].
  split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
  split; [exact Hgimg|].
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite Hstklo_eq; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split; [exact Hspill|].
  split; [exact Hsel|].
  split; [exact Hfr56|].
  split; [destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]];
          [left; split; [exact H0|]; split; [exact Hspfr|];
             intros a Ha; rewrite Hstklo_eq; exact (Hreal a Ha)
          |right; split; [exact Hfr0|]; split; [exact Hfsb | split; [exact Hfs | exact Hrec]]]|].
  split; [exact Hhdr1|].
  split; [exact Hhdr2|].
  split; [exact Hsh|].
  split; [exact Hwin|].
  split; [exact Hsaved|].
  split; [exact Herrno|].
  split; [exact HAG|].
  split; [exact HWA|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. exact (conj Hinb Hinblk).
Qed.

(* FRA moves across a run that writes only the frame body (app bytes inside [fr, fr + 3136), never the frame
   header [fr, fr + 24), never the spill slot [s1 + 336, s1 + 344), never the saved registers [S - 104, S), never
   the 392 shadow bytes): RT via RT_store (all_app W, rt_disjoint W, no shadow write); AH / stklo kept by the
   caller's a_laws_store (real arm) or a_laws_fs_store (side arm); the app/image memory facts (header q64 words,
   G_img_c, the 3 sink words, the spill, the saved registers, the shadow existential) kept with fl_bytes, since
   their addresses are outside W; the window and errno writable cells kept by wmono. The frame location disjunction
   is kept by the stklo equality (real arm) and the tp word (side arm, read by a_in_fs, which is below the frame).
   Push 5c: the window's addressability survives because W is all_app, so no shadow byte changes (sl_addr_keep);
   the fr reload spill at [A + 40] is kept by the spill premise, which now covers [A + 40, A + 56) (the fr reload
   slot and the selector slot); the three ENTRY stack-top facts read the ghost only. *)
Lemma sl_fr_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> AC.GT <= fr ->
  (forall x, 0 <= x < 2 ^ 64 -> (x < fr + 24 \/ fr + FRAME_BYTES <= x) -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 336 <= x < A + 344 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 40 <= x < A + 56 -> Frame.outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> Frame.outside W x \/ exists b, mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK Happ Hgt
    HWout HWspill HWsaved HWsh HWsel HWwin E2 E3 E4 E8 E9 E19 E26.
  unfold AC.GT in Hgt.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (Hub : fr + FRAME_BYTES <= 140737488355328).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. destruct Ha as [Ha|Ha]; lia. }
  assert (KB : forall (sg : list Segment) x, 0 <= x < 2 ^ 64 -> (x < fr + 24 \/ fr + FRAME_BYTES <= x) ->
                 mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hx Hd. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by exact Hx. exact (HWout x Hx Hd). }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. apply KB; [lia | left; lia]. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md W HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * refine (fsrec_munch (hb ++ g_H g) mem mem' md W fr Hrec HAH MU _).
          intros x Hap Hd. apply HWout.
          -- unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap. lia.
          -- destruct (Z_lt_le_dec x (fr + 24)) as [L|R]; [left; exact L | right; lia]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWout; [lia | left; lia]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWout; [lia | left; lia]. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split.
  { eapply (Frame.stk_transport rsegs W mem mem' (g_S g - AF.SLOT_STACK) (g_S g));
      [exact Hwin | exact MU | exact WM |].
    intros x Hx. exact (HWwin x Hx). }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' W a 1 (HAG a Hin) MU HAW)|].
  split; [intros a H1 H2; exact (sl_addr_keep mem mem' W a 1 (HWA a H1 H2) MU HAW)|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* the input block: app memory outside the frame (fra_in_apart), so outside W *)
  apply (fra_in_keep g mem mem' W Hinb Hinblk MU HAW).
  intros x Hx. destruct (Hinap x Hx) as (Hxa & _ & Hxf & _). apply HWout.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa. lia.
  - lia.
Qed.

(* FRA moves across a run that writes the frame body AND its 392 shadow bytes [Sfr fr, Sfr fr + 392) (the poisoning /
   set_shadow runs): RT via RT_meta_write (rt_disjoint W, every shadow byte readable afterwards: the frame shadow from
   the caller's new 392-byte list, the rest kept by munch over RT's shadow_rw); AH / stklo from the caller's
   a_laws_store / a_laws_fs_store; the shadow existential is the caller's new list; the other app/image facts kept as
   in sl_fr_run (their addresses are app and outside the body, so neither body nor frame shadow).
   Push 5c: the fr reload spill at [A + 40] is outside W by the widened spill premise; the window's
   addressability survives one byte at a time, since a window byte outside the frame has its shadow byte outside
   the frame's 392 (the frame covers whole granules, fr mod 32 = 0 and 3136 mod 8 = 0). *)
Lemma sl_fr_meta : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> AC.GT <= fr ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (fr + 24 <= x < fr + FRAME_BYTES) -> ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) ->
     Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 336 <= x < A + 344 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 40 <= x < A + 56 -> Frame.outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> Frame.outside W x \/ exists b, mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK Happ Hgt Hshnew
    HWkept HWspill HWsaved HWsel HWwin HAG' E2 E3 E4 E8 E9 E19 E26.
  unfold AC.GT in Hgt.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (Hub : fr + FRAME_BYTES <= 140737488355328).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. destruct Ha as [Ha|Ha]; lia. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (KBout : forall x, app_mem x -> ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x).
  { intros x Hap Hnb. apply HWkept.
    - unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; destruct Hap; lia.
    - exact Hnb.
    - intro Hin380. exact (app_not_shadow x Hap (HshIS x Hin380)). }
  assert (KBmb : forall (sg : list Segment) x, app_mem x -> ~ (fr + 24 <= x < fr + FRAME_BYTES) ->
                   mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hap Hnb.
    assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap; destruct Hap; lia).
    assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by exact Hx64. exact (KBout x Hap Hnb). }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. apply KBmb; [unfold app_mem, LOWMEM_END; left; lia | lia]. }
  assert (ShRo : forall a, in_shadow a -> ~ (Sfr fr <= a < Sfr fr + FRAME_SHADOW) ->
                   exists b, mrd rsegs mem' (wa a) = Some b).
  { intros a Hin Hnf.
    assert (Hnb : ~ (fr + 24 <= a < fr + FRAME_BYTES)) by
      (intro Hb; exact (app_not_shadow a (Happ a ltac:(lia)) Hin)).
    assert (Hx64 : 0 <= a < 2 ^ 64) by (pose proof (in_shadow_range a Hin); lia).
    assert (Ho : Frame.outside W a) by (apply HWkept; [exact Hx64 | exact Hnb | exact Hnf]).
    destruct (AsanRTInv.RT_shadow_rw sp mem md HRT a Hin) as (_ & b & Hmr).
    assert (Hmem : mem' (wa a) = mem (wa a)) by (apply MU; rewrite Mem.wa_unsigned by exact Hx64; exact Ho).
    exists b. unfold mrd in *. rewrite Hmem. exact Hmr. }
  assert (HshR : forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b).
  { intros a Hin.
    destruct (Z_le_gt_dec (Sfr fr) a) as [Hge|Hlt];
      [destruct (Z_lt_ge_dec a (Sfr fr + FRAME_SHADOW)) as [Hlt2|Hge2]|].
    - destruct Hshnew as (sh & (Hb0 & Hb1 & Hb2) & Hl).
      assert (Hj : (Z.to_nat (a - Sfr fr) < length sh)%nat) by (rewrite Hl; lia).
      pose proof (Hb2 (Z.to_nat (a - Sfr fr)) Hj) as HmE.
      rewrite Z2Nat.id in HmE by lia. replace (Sfr fr + (a - Sfr fr)) with a in HmE by lia.
      destruct (nth_error sh (Z.to_nat (a - Sfr fr))) as [b|] eqn:E; [exists b; exact HmE|].
      exfalso. apply nth_error_None in E. rewrite Hl in E. lia.
    - apply (ShRo a Hin). lia.
    - apply (ShRo a Hin). lia. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * exact (fsrec_munch (hb ++ g_H g) mem mem' md W fr Hrec HAH MU KBout). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply KBout; [apply Happ; lia | lia]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply KBout; [apply Happ; lia | lia]. }
  split; [exact Hshnew|].
  split.
  { eapply (Frame.stk_transport rsegs W mem mem' (g_S g - AF.SLOT_STACK) (g_S g));
      [exact Hwin | exact MU | exact WM |].
    intros x Hx. exact (HWwin x Hx). }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split.
  { intros a H1 H2.
    pose proof (HWA a H1 H2) as HadA.
    pose proof (addr1_app mem a HadA) as Happa.
    assert (Hfr0 : 0 <= fr).
    { pose proof (Happ fr ltac:(lia)) as X.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X. lia. }
    assert (Ha0 : 0 <= a) by (destruct HadA as (H0 & _); exact H0).
    apply (addr1_munch W mem mem' a MU); [|exact HadA].
    apply HWkept.
    - destruct (in_shadow_range (shadow_addr a) (shadow_of_app a Happa)) as (R1 & R2). lia.
    - intro Hb. exact (app_not_shadow (shadow_addr a) (Happ (shadow_addr a) ltac:(lia))
                         (shadow_of_app a Happa)).
    - intro Hb. apply H2. unfold Sfr, shadow_addr in Hb.
      revert Hb Hfrm Ha0 Hfr0 HFBv HFSv. clear. intros. Z.div_mod_to_equations. lia. }
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* the input block: app memory outside the frame (fra_in_apart), so outside the frame body and, the frame
     covering whole granules (fr mod 32 = 0), with its shadow bytes outside the frame's 392 *)
  apply (fra_in_keep_sh g mem mem' W Hinb Hinblk MU).
  intros x Hx. destruct (Hinap x Hx) as (Hxa & _ & Hxf & _).
  assert (Hfr0 : 0 <= fr).
  { pose proof (Happ fr ltac:(lia)) as X.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X. lia. }
  assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
  split; [apply KBout; [exact Hxa | lia]|].
  apply HWkept.
  - destruct (in_shadow_range (shadow_addr x) (shadow_of_app x Hxa)) as (R1 & R2). lia.
  - intro Hb. exact (app_not_shadow (shadow_addr x) (Happ (shadow_addr x) ltac:(lia)) (shadow_of_app x Hxa)).
  - intro Hb. apply Hxf. unfold Sfr, shadow_addr in Hb.
    revert Hb Hfrm Hx0 Hfr0 HFBv HFSv. clear. intros. Z.div_mod_to_equations. lia.
Qed.

(* FRA moves across a callee run (plan 4): the callee's a_call_post carries RT, AH for the new heap H' = hb' ++ g_H g,
   the callee-saved registers, the lazy-materialised model md', stklo = stklo, and the tp word (16 bytes).  The app /
   image memory facts (header, spill, the 392 shadow bytes, saved registers, the window, sink_none, G_img_c) are kept
   by the caller from a_call_post's frame clause (ADDR-KEEP, the frame-window / touched disjointness); errno survives
   by a_call_post's errno-writable iff.  The frame location disjunction is kept by stklo (real arm) and the tp word
   (side arm, read by a_in_fs) and, push 5b, by the caller's FSREC premise (a callee that writes only its own
   window keeps the record: fsrec_munch_lo). Push 5c: the fr reload spill at [A + 40] and the window's
   addressability after the call are the caller's (a_call_post leaves the window's shadow to the callee's own
   epilogue); the three ENTRY stack-top facts read the ghost only. FRA's input facts: a_call_post does not keep
   the input block (it is a live block of the heap, which the callee may own), so the caller gives its bytes and,
   for n > 0, its addressability after the call; its membership in g_H g reads the ghost only. *)
Lemma sl_mid : forall g fr hb hb' regs mem md regs' mem' md' touched K,
  FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    K (hb ++ g_H g) regs mem md touched (hb' ++ g_H g) regs' mem' md' ->
  (length hb' <= 1)%nat ->
  sink_none B mem' md' -> G_img_c B AF.frame_RELRO mem' ->
  q64 mem' fr 0x41b58ab3 -> q64 mem' (fr + 16) AF.ENTRY ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> q64 mem' (A + 336) fr) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall v, q64 mem (A + 48) v -> q64 mem' (A + 48) v) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> q64 mem' (A + 40) fr) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  bytes_at rsegs mem' (g_S g - 104) (saved_bytes ra g) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  bytes_at rsegs mem' (g_p g) (g_in g) ->
  (0 < g_n g -> addressable mem' (g_p g) (g_n g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb' regs' mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb hb' regs mem md regs' mem' md' touched K HFRA Hcp Hhb' Hsn' Hgimg'
    Hhdr1' Hhdr2' Hspill' Hselp Hfr56' Hsh' Hsaved' Hwin' HAG' HWA' HrecK Hinb' Hinad' E2 E3 E4 E8 E9 E19 E26.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  pose proof Hcp as Hrt; apply AC.a_call_post_rt in Hrt.
  pose proof Hcp as Hah; apply AC.a_call_post_ah in Hah.
  pose proof Hcp as Hroc; apply AC.a_call_post_ro in Hroc.
  pose proof Hcp as Hlv; apply AC.a_call_post_live in Hlv.
  pose proof Hcp as Hsk; apply AC.a_call_post_stklo in Hsk.
  assert (Htp : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (Hew : forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 ->
            (writable_at rsegs mem a <-> writable_at rsegs mem' a))
    by (eapply AC.a_call_post_errno_writable; exact Hcp).
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_any (AC.aspZ regs) sp mem' md' md' Hrt)|].
  split; [exact Hah|].
  split; [exact Hroc|].
  split; [exact Hsn'|].
  split; [exact Hlv|].
  split; [exact Hgimg'|].
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite Hsk; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split; [exact (Hspill' A Hr9 HA64)|].
  split; [exact (Hselp A Hr9 HA64 s5 Hsel)|].
  split; [exact (Hfr56' A Hr9 HA64)|].
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite Hsk. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- (Htp (Z.of_nat k) ltac:(lia)). exact (Hw k Hk).
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite (Htp (Z.of_nat k) ltac:(lia)). exact (Hw k Hk).
        * exact (HrecK Hrec). }
  split; [exact Hhdr1'|].
  split; [exact Hhdr2'|].
  split; [exact Hsh'|].
  split; [exact Hwin'|].
  split; [exact Hsaved'|].
  split.
  { intros a Ha. apply (Hew a Ha). exact (Herrno a Ha). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb'|]. split; [exact Hlive|]. split; [exact Hinb'|].
  intros Hn. split; [exact (proj1 (Hinblk Hn)) | exact (Hinad' Hn)].
Qed.

(* sl_mid for a callee whose a_call_post states the post heap H' in another order than FRA's hb' ++ g_H g (the
   allocator appends: g_H ++ [(q, n)]). FRA reads aa_AH only (never aa_owned), so the AH conjunct is rebuilt with
   a_laws_perm from the post's AH H' and the permutation; every other premise and conjunct is sl_mid's (the input
   facts after the call included). *)
Lemma sl_mid_perm : forall g fr hb hb' H' regs mem md regs' mem' md' touched K,
  FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    K (hb ++ g_H g) regs mem md touched H' regs' mem' md' ->
  Permutation (hb' ++ g_H g) H' ->
  (length hb' <= 1)%nat ->
  sink_none B mem' md' -> G_img_c B AF.frame_RELRO mem' ->
  q64 mem' fr 0x41b58ab3 -> q64 mem' (fr + 16) AF.ENTRY ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> q64 mem' (A + 336) fr) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall v, q64 mem (A + 48) v -> q64 mem' (A + 48) v) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> q64 mem' (A + 40) fr) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  bytes_at rsegs mem' (g_S g - 104) (saved_bytes ra g) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  bytes_at rsegs mem' (g_p g) (g_in g) ->
  (0 < g_n g -> addressable mem' (g_p g) (g_n g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb' regs' mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb hb' H' regs mem md regs' mem' md' touched K HFRA Hcp Hperm Hhb' Hsn' Hgimg'
    Hhdr1' Hhdr2' Hspill' Hselp Hfr56' Hsh' Hsaved' Hwin' HAG' HWA' HrecK Hinb' Hinad' E2 E3 E4 E8 E9 E19 E26.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  pose proof Hcp as Hrt; apply AC.a_call_post_rt in Hrt.
  pose proof Hcp as Hah; apply AC.a_call_post_ah in Hah.
  pose proof Hcp as Hroc; apply AC.a_call_post_ro in Hroc.
  pose proof Hcp as Hlv; apply AC.a_call_post_live in Hlv.
  pose proof Hcp as Hsk; apply AC.a_call_post_stklo in Hsk.
  assert (Htp : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (Hew : forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 ->
            (writable_at rsegs mem a <-> writable_at rsegs mem' a))
    by (eapply AC.a_call_post_errno_writable; exact Hcp).
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_any (AC.aspZ regs) sp mem' md' md' Hrt)|].
  split; [exact (AC.a_laws_perm _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H' (hb' ++ g_H g) mem' md'
                   Hah (Permutation_sym Hperm))|].
  split; [exact Hroc|].
  split; [exact Hsn'|].
  split; [exact Hlv|].
  split; [exact Hgimg'|].
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite Hsk; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split; [exact (Hspill' A Hr9 HA64)|].
  split; [exact (Hselp A Hr9 HA64 s5 Hsel)|].
  split; [exact (Hfr56' A Hr9 HA64)|].
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite Hsk. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- (Htp (Z.of_nat k) ltac:(lia)). exact (Hw k Hk).
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite (Htp (Z.of_nat k) ltac:(lia)). exact (Hw k Hk).
        * exact (HrecK Hrec). }
  split; [exact Hhdr1'|].
  split; [exact Hhdr2'|].
  split; [exact Hsh'|].
  split; [exact Hwin'|].
  split; [exact Hsaved'|].
  split.
  { intros a Ha. apply (Hew a Ha). exact (Herrno a Ha). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb'|]. split; [exact Hlive|]. split; [exact Hinb'|].
  intros Hn. split; [exact (proj1 (Hinblk Hn)) | exact (Hinad' Hn)].
Qed.

(* FRA is assembled from scratch (plan 3.1, for A1 / A4 at or just after the frame request): the asan runtime, heap,
   ro_agree, m_halted, sp alignment and tp register come from the frame request's a_call_pre projections
   (Contract.v a_call_pre_rt / _ah / _ro / _live / _sp_align / _tp); the stack facts are the entry-anchored ones of
   PREF (stklo at or below S - SLOT_STACK, the window [S - SLOT_STACK, S), S - 4096 < sp, S < APPMEM_END), which the
   entry pre gives at sp = S with
   K = SLOT_STACK and which hold at every sp of the function; the frame base fr, the s0/s1/s3 registers, the header,
   the 392 shadow bytes, the frame-location disjunction (real arm sp = fr and the a_store_ok range, side arm the FS
   base below the frame and a_in_fs), the spill, the saved registers, errno, sink_none, G_img_c and the ROOM bounds
   are supplied by the caller (the request's post / the real-stack arm and the A3 header+shadow writes), and so are
   FRA's input facts (PREF's, which no A-region run changes). *)
Lemma sl_fr_of : forall g fr hb s5 A sp regs mem md K,
  AC.a_call_pre AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    K (hb ++ g_H g) regs mem md ->
  AC.aspZ regs = sp ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AF.SLOT_STACK ->
  g_S g - 4096 < sp -> g_S g < APPMEM_END ->
  sink_none B mem md -> G_img_c B AF.frame_RELRO mem ->
  getr regs 2 = Z_to_bv 64 sp -> rg regs 8 (g_S g) -> rg regs 9 A ->
  getr regs 3 = getr (g_regs g) 3 -> rg regs 19 (Sfr fr) -> rg regs 26 ASAN_K ->
  fr mod 32 = 0 -> (s5 = 0 \/ s5 = fr) -> A mod 32 = 0 -> A <= g_S g -> sp <= A -> fr + FRAME_BYTES <= A ->
  A + 448 <= g_S g ->
  q64 mem (A + 336) fr ->
  q64 mem (A + 48) s5 ->
  q64 mem (A + 40) fr ->
  ((s5 = 0 /\ sp = fr /\ (forall a, fr <= a < fr + FRAME_BYTES ->
       AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END)) \/
   (s5 = fr /\
      (forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + 6328320 <= fr) /\
      (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC fr mem)) ->
  q64 mem fr 0x41b58ab3 -> q64 mem (fr + 16) AF.ENTRY ->
  (exists sh, bytes_at rsegs mem (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g) ->
  bytes_at rsegs mem (g_S g - 104) (saved_bytes ra g) ->
  (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at rsegs mem a) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem a 1) ->
  g_S g <= AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) (g_mem g) (g_md g) ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) (g_mem g) (g_md g) <= APPMEM_END ->
  (forall a, g_S g <= a < AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) (g_mem g) (g_md g) ->
     exists b, mbyte rsegs (g_mem g) a = Some b) ->
  (length hb <= 1)%nat -> AC.a_live_bytes (g_H g) <= 5 * 2 ^ 30 ->
  bytes_at rsegs mem (g_p g) (g_in g) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)) ->
  FRA B APIf ra g fr hb regs mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb s5 A sp regs mem md K Hpre Haspz Hstklo HS4 HAPP Hsn Hgimg Hr2 Hr8 Hr9 Hr3 Hr19 Hr26
    Hfrm Hs5 HAm HAS Hspa Hfa HA416 Hspill Hsel Hfr56 Hloc Hhdr1 Hhdr2 Hsh Hwin Hsaved Herrno HAG
    HWA HSHI1 HSHI2 HSHI3 Hhb Hlive Hinb Hinblk.
  pose proof Hpre as Hrt; apply AC.a_call_pre_rt in Hrt.
  pose proof Hpre as Hah; apply AC.a_call_pre_ah in Hah.
  pose proof Hpre as Hro; apply AC.a_call_pre_ro in Hro.
  pose proof Hpre as Hlv; apply AC.a_call_pre_live in Hlv.
  pose proof Hpre as Hal; apply AC.a_call_pre_sp_align in Hal.
  pose proof Hpre as Htp; apply AC.a_call_pre_tp in Htp.
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_any (AC.aspZ regs) sp mem md md Hrt)|].
  split; [exact Hah|].
  split; [exact Hro|].
  split; [exact Hsn|].
  split; [exact Hlv|].
  split; [exact Hgimg|].
  split; [exact Hr2|].
  split; [rewrite <- Haspz; exact Hal|].
  split; [exact Haspz|].
  split; [exact Hstklo|].
  split; [exact Htp|].
  split; [unfold rg in *; exact Hr8|].
  split; [unfold rg in *; exact Hr9|].
  split; [exact Hr3|].
  split; [unfold rg in *; exact Hr19|].
  split; [unfold rg in *; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split; [exact Hspill|].
  split; [exact Hsel|].
  split; [exact Hfr56|].
  split; [exact Hloc|].
  split; [exact Hhdr1|].
  split; [exact Hhdr2|].
  split; [exact Hsh|].
  split; [exact Hwin|].
  split; [exact Hsaved|].
  split; [exact Herrno|].
  split; [exact HAG|].
  split; [exact HWA|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. exact (conj Hinb Hinblk).
Qed.

(* The 3136-byte frame is apart from the allocator's own stack window [sp - 4096, sp): on the real arm the frame
   base IS sp (FRA's real-arm conjunct sp = fr), so no frame byte is below sp; on the side arm the frame is in the
   FakeStack, which a_laws_fs_place puts wholly below stklo, and fra_win puts stklo at or below sp - FN_STACK,
   with FN_STACK = SLOT_STACK - 4096 >= 4096. *)
Lemma sl_frame_apart_win : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  forall a, fr <= a < fr + FRAME_BYTES -> ~ (AC.aspZ regs - 4096 <= a < AC.aspZ regs).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA a Ha.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold FN_STACK in Hlo.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs _]]]].
  - rewrite Haspz. lia.
  - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
    destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md FSb HAH Hw HFSr) as [_ Hend _].
    rewrite Haspz in Hlo. lia.
Qed.

(* ---- Callee-window transports (the canonical copies for the segments that call a program callee or a wrapper
   whose post is a munch over its own stack window, not a_call_post). ---- *)

(* The entry-anchored stack window of FRA survives a callee's write of its own window [sp - K, sp), for any
   window K the callee contracts use (0 <= K <= FN_STACK): the parts below and above it are kept
   (stk_transport_disjoint) and the window itself is the callee's own post. Every sp of the function is above
   S - 4096 and at or below A <= S, so [sp - K, sp) lies inside [S - SLOT_STACK, S). *)
Lemma sl_win_stk : forall g fr hb regs mem md mem' K,
  FRA B APIf ra g fr hb regs mem md -> 0 <= K <= FN_STACK ->
  Frame.munch [(AC.aspZ regs - K, AC.aspZ regs)] mem mem' -> Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (AC.aspZ regs - K) (AC.aspZ regs) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md mem' K HFRA HK MU WM HST.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  rewrite Haspz in HST, MU.
  destruct (Frame.stk_split rsegs mem (g_S g - AF.SLOT_STACK) (sp - K) (g_S g) Hwin ltac:(lia)) as (Hlo & Hhi).
  destruct (Frame.stk_split rsegs mem (sp - K) sp (g_S g) Hhi ltac:(lia)) as (_ & Htop).
  assert (Lo' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (sp - K)).
  { eapply Frame.stk_transport_disjoint; [exact Hlo | exact MU | exact WM |].
    cbn [Frame.disjoint_from]. split; [left; lia | exact I]. }
  assert (Top' : stk rsegs mem' sp (g_S g)).
  { eapply Frame.stk_transport_disjoint; [exact Htop | exact MU | exact WM |].
    cbn [Frame.disjoint_from]. split; [right; lia | exact I]. }
  apply (Frame.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) sp (g_S g));
    [apply (Frame.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) (sp - K) sp Lo' HST ltac:(lia)) | exact Top' | lia].
Qed.

(* The heap invariant and the stack-low bound move across a callee's write of its own window [sp - K, sp): every
   byte of that window is a_store_ok (the window is at or above stklo by fra_win and below APPMEM_END, since
   sp <= A <= S < APPMEM_END), so a_laws_store applies on either frame arm. The AH' / stklo premises of sl_fr_cl
   come from here. *)
Lemma sl_ah_stk : forall g fr hb regs mem mem' md K,
  FRA B APIf ra g fr hb regs mem md -> 0 <= K <= FN_STACK ->
  Frame.munch [(AC.aspZ regs - K, AC.aspZ regs)] mem mem' -> Frame.wmono rsegs mem mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md K HFRA HK MU WM.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP & _).
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (Hsp : AC.aspZ regs = sp) by exact Haspz.
  assert (P1 : forall a, 0 <= a < 2 ^ 64 ->
            ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
            mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn. apply MU. rewrite MState.unsigned_lit by exact Ha.
    cbn [Frame.outside]. split; [|exact I]. intros Hin. apply Hn.
    unfold AC.a_store_ok. right. left. rewrite Hsp in Hin. lia. }
  assert (P2 : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md
    HAH P1 P2) as [HAH' _ Hstkeq _].
  split; [exact HAH' | exact Hstkeq].
Qed.

(* THE callee / stack transport of FRA (push 5c): FRA moves across any run whose write set W is app memory and
   rt_disjoint and which keeps the cells FRA reads outside itself -- the low image [0, 6283264) (the runtime's
   sink cells and the RELRO image bytes), the frame header [fr, fr + 24), the frame-base spill [s1 + 336,
   s1 + 344), the fr reload and selector spills [s1 + 56, s1 + 72), the saved caller registers [S - 104, S) and
   the 392 frame shadow bytes -- but which MAY write the frame body [fr + 24, fr + 3136) and the callee's own
   stack window [sp - K, sp). RT via RT_store; AH / stklo from the caller (sl_ah_stk for a callee window, or
   a_laws_store / a_laws_fs_store for a frame write); the entry-anchored window of mem' from the caller
   (sl_win_stk or the callee's post); frame_AG and the window stay addressable because W is app memory, so no
   shadow byte changes (sl_addr_keep); the rest kept by fl_bytes (their addresses are outside W) and wmono
   (errno). It is the one copy of the rebuild: sl_win_run and sl_stk_run below are its siblings. A caller
   holding the "outside W or readable" form of the window gets it with Frame.stk_transport.
   Image B has no mem_inv conjunct in FRA, so image A's `mem_inv rsegs mem'` premise is dropped. The side-arm
   FakeStack record is image A's premise `FSREC fr mem -> FSREC fr mem'` (a caller whose writes miss everything
   below stklo outside the frame body gets it from fsrec_stklo). FRA's input facts: W misses the input block (a
   caller gets it from fra_in_apart: the block is below stklo and apart from the frame), so its bytes stay, and its
   addressability stays because W is app memory (fra_in_keep). *)
Lemma sl_fr_cl : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, 0 <= x < 6283264 -> Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 336 <= x < A + 344 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 40 <= x < A + 56 -> Frame.outside W x) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HWlo HWhdr HWspill HWsaved HWsh
    HWsel Hrec' HWin HWwin E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md W HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * exact (Hrec' Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split; [exact HWwin|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' W a 1 (HAG a Hin) MU HAW)|].
  split; [intros a H1 H2; exact (sl_addr_keep mem mem' W a 1 (HWA a H1 H2) MU HAW)|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. exact (fra_in_keep g mem mem' W Hinb Hinblk MU HAW HWin).
Qed.

(* The side-stack premises of a call, for any class list cs and any window 0 <= K <= FN_STACK: the caller's own
   frame package fp at a window [lo, hi) that covers the callee's [sp - K, sp) gives the callee's fp (fl_fp_sub:
   the cells fp names do not move, only the window shrinks) and its tls premise (the thread cells stay apart from
   fp_w cs FS and from the shadow of the smaller window, fl_dj_last). The window facts the same contracts ask for
   next to fp -- the window at or above HIGHMEM_BEG and below APPMEM_END, sp 16-aligned, the window's bytes
   readable and writable (stk), every window byte app memory and addressable -- are FRA's: fra_win for the
   window, a_laws_stack_high for HIGHMEM_BEG <= stklo, sp <= A <= S < APPMEM_END for the top, and FRA's own
   window-addressability conjunct with fra_frame's frame/window apartness for `addressable`.
   (lib/B/Prog/reac_ctrl_parse_c.v and reac_ctrl_classify_box_frame_c.v ask for exactly these.) *)
Lemma fra_callee_fp : forall g fr hb regs mem md K cs FS lo hi W D,
  FRA B APIf ra g fr hb regs mem md -> 0 <= K <= FN_STACK ->
  FP.fp cs mem (AC.as_tp AC.ASYMS) FS lo hi W D ->
  (forall DT TS C T DB k, ASM.asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k ->
     FP.fp_dj (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k)
       (FP.fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)])) ->
  lo <= AC.aspZ regs - K -> AC.aspZ regs <= hi ->
  HIGHMEM_BEG <= AC.aspZ regs - K /\ AC.aspZ regs <= APPMEM_END /\ AC.aspZ regs mod 16 = 0 /\
  stk rsegs mem (AC.aspZ regs - K) (AC.aspZ regs) /\
  (forall a, AC.aspZ regs - K <= a < AC.aspZ regs -> app_mem a) /\
  addressable mem (AC.aspZ regs - K) K /\
  FP.fp cs mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - K) (AC.aspZ regs) W D /\
  (forall DT TS C T DB k, ASM.asan_tls_cells mem (AC.as_tp AC.ASYMS) DT TS C T DB k ->
     FP.fp_dj (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k)
       (FP.fp_w cs FS ++ [(shadow_addr (AC.aspZ regs - K), shadow_addr (AC.aspZ regs))])).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md K cs FS lo hi W D HFRA HK Hfp Htls Hlo Hhi.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & _ & _ & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HK1 : HIGHMEM_BEG <= AC.aspZ regs - K) by lia.
  assert (HK2 : AC.aspZ regs <= APPMEM_END) by lia.
  assert (Hstk : stk rsegs mem (AC.aspZ regs - K) (AC.aspZ regs)).
  { destruct (Frame.stk_split rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs - K) (AC.aspZ regs) Hwstk
                ltac:(lia)) as (_ & Hs). exact Hs. }
  split; [exact HK1|].
  split; [exact HK2|].
  split; [rewrite Haspz; exact Hspm|].
  split; [exact Hstk|].
  split; [intros a Ha; unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END in *; lia|].
  split.
  { unfold addressable.
    assert (HHB : HIGHMEM_BEG = 17594333495296) by reflexivity.
    assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros i Hi.
    pose proof (HWA (AC.aspZ regs - K + i) ltac:(lia)
                  ltac:(destruct (Hapart K HK) as [Hd|Hd]; lia)) as Had.
    destruct Had as (_ & _ & _ & Hb). pose proof (Hb 0 ltac:(lia)) as Hb0.
    rewrite Z.add_0_r in Hb0. exact Hb0. }
  split.
  { apply (fl_fp_sub cs mem (AC.as_tp AC.ASYMS) FS lo hi W D); [exact Hfp | lia | lia | | ];
      intros X HX; exact HX. }
  { intros DT TS C T DB k HT.
    apply (fl_dj_last _ (FP.fp_w cs FS) (shadow_addr lo) (shadow_addr hi));
      [exact (Htls DT TS C T DB k HT) | |];
      unfold shadow_addr; apply Z.add_le_mono_r, Z.div_le_mono; lia. }
Qed.

(* FRA moves across a callee run whose writes W lie in [HIGHMEM_BEG, sp) and miss the frame header [fr, fr + 24)
   (a Theorem Labs lane, lib/B/Prog/Seg/F7.v: the reac_ctrl_kind_name window [sp - 16, sp)): the low image / runtime words
   (below HIGHMEM_BEG), the shadow bytes (in_shadow, below HIGHMEM_BEG), the spills [A+336,A+344) / [A+56,A+72) and
   the saved registers [S-104,S) (all at or above A >= sp) are outside W. RT via RT_store; AH / stklo from the
   caller's a_laws_store; the AG cells by sl_addr_keep. The window [S - SLOT_STACK, S) is the callee's stk post
   below sp (the contract called with lo = S - SLOT_STACK, which FRA's window gives the pre by stk_split) joined
   with FRA's window above sp, which W misses. sl_fr_run / sl_fr_meta need W inside the frame body, and sl_mid
   needs a_call_post; a callee window is inside the slot window and its contract gives munch / wmono / stk. The
   FakeStack record and FRA's input facts as in sl_fr_cl: image A's premise `FSREC fr mem -> FSREC fr mem'`
   (fsrec_stklo) and W missing the input block (fra_in_apart, fra_in_keep). *)
Lemma sl_win_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, x < HIGHMEM_BEG \/ AC.aspZ regs <= x -> Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x) ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HWout HWhdr Hrec' HWin Happ HWIN
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  rewrite Haspz in HWout, HWIN.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold HIGHMEM_BEG; lia).
      apply HWout. left. unfold HIGHMEM_BEG; lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (HWhi : forall x, sp <= x -> Frame.outside W x) by (intros x Hx; apply HWout; right; exact Hx).
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md W HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhi. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * exact (Hrec' Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. apply HWout. left.
    change (Z.of_nat (Z.to_nat FRAME_SHADOW)) with FRAME_SHADOW in Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hinfr)) as His.
    unfold shadow_addr in His. rewrite Hdiv in His. unfold Sfr, shadow_addr in *.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  split.
  { destruct (Frame.stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)) as (_ & Hup).
    apply (Frame.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) sp (g_S g)); [exact HWIN | | lia].
    eapply (Frame.stk_transport rsegs W mem mem' sp (g_S g)); [exact Hup | exact MU | exact WM |].
    intros x Hx. left. apply HWhi. lia. }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx. apply HWhi.
    unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' W a 1 (HAG a Hin) MU HAW)|].
  split; [intros a H1 H2; exact (sl_addr_keep mem mem' W a 1 (HWA a H1 H2) MU HAW)|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. exact (fra_in_keep g mem mem' W Hinb Hinblk MU HAW HWin).
Qed.

(* FRA moves across a run that writes only a region W disjoint from the frame / spill / saved / shadow / low
   image (the wrapper_bcmp main-stack scratch [sp-K,sp); a Theorem Labs lane, lib/B/Prog/Seg/F18.v). The complement of
   sl_fr_run (writes INSIDE the frame body); the entry-anchored slot window on mem' is the caller's. The FakeStack
   record and FRA's input facts as in sl_fr_cl: image A's premise `FSREC fr mem -> FSREC fr mem'` (fsrec_stklo)
   and W missing the input block (fra_in_apart, fra_in_keep). *)
Lemma sl_stk_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  all_app W -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  (forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> forall x, A + 336 <= x < A + 344 -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> forall x, A + 40 <= x < A + 56 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HAW HD HAH' HSTK HSTKW HWframe HWimg HWspill HWsel
    HWsaved HWsh Hrec' HWin E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold HIGHMEM_BEG in *; lia).
      apply HWimg. unfold HIGHMEM_BEG in *; lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md W HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill A Hr9 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * exact (Hrec' Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWframe. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWframe. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split; [exact HSTKW|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' W a 1 (HAG a Hin) MU HAW)|].
  split; [intros a H1 H2; exact (sl_addr_keep mem mem' W a 1 (HWA a H1 H2) MU HAW)|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. exact (fra_in_keep g mem mem' W Hinb Hinblk MU HAW HWin).
Qed.

(* FRA across one wrapper_bcmp call from a FRA cut: the call writes only its main-stack scratch W = [sp - K, sp)
   (disjoint from the frame by fra_frame, below the spill base A, above the low image and the shadow); keeps the FRA
   registers and the entry-anchored slot window, and materializes pages (a Theorem Labs lane, lib/B/Prog/Seg/F18.v). *)
Lemma bcmp_fra : forall g fr hb regs regs' mem mem' md md' A,
  FRA B APIf ra g fr hb regs mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> AC.aspZ regs <= A ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  Frame.munch [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)] mem mem' ->
  Frame.wmono rsegs mem mem' -> LMem.mem_inv rsegs mem' ->
  stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' A HFRA Hs1 HAb HspA Hfrapp MU WM MI' HSTKW
    Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat.
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hfrw & _ & _ & _).
  assert (Hdisjfr : fr + FRAME_BYTES <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr)
    by (apply Hfrw; unfold FN_STACK, BCMP_WRAP_K, AF.SLOT_STACK; lia).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HSTKS : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { destruct (Frame.stk_split rsegs mem (g_S g - AF.SLOT_STACK) (AC.aspZ regs - BCMP_WRAP_K) (g_S g) Hwin
                ltac:(rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia)) as (Hw1 & Hw2).
    destruct (Frame.stk_split rsegs mem (AC.aspZ regs - BCMP_WRAP_K) (AC.aspZ regs) (g_S g) Hw2
                ltac:(rewrite Haspz; unfold BCMP_WRAP_K; lia)) as (_ & Hw3).
    destruct (Frame.stk_split rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs - BCMP_WRAP_K) (AC.aspZ regs) HSTKW
                ltac:(unfold BCMP_WRAP_K, FN_STACK, AF.SLOT_STACK; lia)) as (_ & HwW).
    assert (Hw1' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs - BCMP_WRAP_K)).
    { eapply (Frame.stk_transport rsegs _ mem mem'); [exact Hw1 | exact MU | exact WM |].
      intros x Hx. left. apply out1. lia. }
    assert (Hw3' : stk rsegs mem' (AC.aspZ regs) (g_S g)).
    { eapply (Frame.stk_transport rsegs _ mem mem'); [exact Hw3 | exact MU | exact WM |].
      intros x Hx. left. apply out1. lia. }
    apply (Frame.stk_merge rsegs mem' _ (AC.aspZ regs) _); [| exact Hw3' | rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia].
    apply (Frame.stk_merge rsegs mem' _ (AC.aspZ regs - BCMP_WRAP_K) _); [exact Hw1' | exact HwW |].
    rewrite Haspz; unfold BCMP_WRAP_K, AF.SLOT_STACK in *; lia. }
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  assert (HroM : ro_agree rsegs mem').
  { intros a Ha. unfold LMem.mrd. destruct (mem' a) as [b|] eqn:Em; [|reflexivity].
    exfalso. pose proof (MI' a b Em) as Hf. rewrite Hf in Ha. discriminate. }
  assert (Hallapp : all_app W).
  { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  assert (Hwlo : AC.GT <= AC.aspZ regs - BCMP_WRAP_K)
    by (rewrite Haspz in *; unfold AC.GT, BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
  assert (Hrtdj : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN, AC.GT, BCMP_WRAP_K in *.
    rewrite Haspz in *. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
    unfold AC.a_store_ok. right; left. rewrite Haspz in *.
    unfold BCMP_WRAP_K, AF.SLOT_STACK in *. split; lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as [HAH' _ HSTKeq _].
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside W x).
  { intros A' HA' x Hx. subst W.
    apply (spill_outW regs A A' (AC.aspZ regs) x Hs1 HAb HspA HA'); [| unfold APPMEM_END in *; lia | exact Hx].
    rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run g fr hb regs regs' mem mem' md W HFRA MU WM HroM Hallapp Hrtdj HAH' HSTKeq HSTKS).
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. destruct Hdisjfr as [Hd|Hd]; unfold BCMP_WRAP_K in *; lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - intros A' HA' x Hx. apply (HA9 A' HA' x). lia.
    - intros A' HA' x Hx. apply (HA9 A' HA' x). lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K in *. lia.
    - intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      assert (Hin : in_shadow x).
      { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
        { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
        pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hinfr)) as His.
        replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
        unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
      rewrite Haspz in *. unfold BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - apply (fsrec_stklo (hb ++ g_H g) mem mem' md W fr HAH MU).
      intros x Hxlo _. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia.
    - intros x Hx. destruct (fra_in_apart B APIf ra g fr hb regs mem md HFRA x Hx) as (_ & Hxlo & _ & _).
      subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. unfold BCMP_WRAP_K, AF.SLOT_STACK in *. lia.
    - exact Fr2.
    - exact Fr3.
    - exact Fr4.
    - exact Fr8.
    - exact Fr9.
    - exact Fr19.
    - exact Fr26. }
  apply (sl_fra_move g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
Qed.

(* FRA across the reac_ctrl_checksum_verify call: the callee writes only its stack scratch W = [sp - 16, sp),
   keeps the FRA registers and the entry-anchored slot window, and materializes pages (a Theorem Labs lane,
   lib/B/Prog/Seg/F20.v). *)
Lemma ckv_fra : forall g fr hb regs regs' mem mem' md md',
  FRA B APIf ra g fr hb regs mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  (fr + FRAME_BYTES <= AC.aspZ regs - 16 \/ AC.aspZ regs <= fr) ->
  AC.aspZ regs <= APPMEM_END ->
  LFr.munch [(AC.aspZ regs - 16, AC.aspZ regs)] mem mem' ->
  LFr.wmono rsegs mem mem' -> LMem.mem_inv rsegs mem' ->
  LFr.stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' HFRA Hfrapp Hdisjfr HaspB MU WM MI' HSTKW
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  rewrite Haspz in Hdisjfr, HaspB, MU, HSTKW.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HOW : forall x, (x < sp - 16 \/ sp <= x) -> LFr.outside [(sp - 16, sp)] x)
    by (intros x Hx; simpl; split; [lia | exact I]).
  assert (HroM : ro_agree rsegs mem').
  { intros a Ha. unfold LMem.mrd. destruct (mem' a) as [b|] eqn:Em; [|reflexivity].
    exfalso. pose proof (MI' a b Em) as Hf. rewrite Hf in Ha. discriminate. }
  assert (Hallapp : all_app [(sp - 16, sp)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  assert (Hrtdj : rt_disjoint [(sp - 16, sp)]) by (apply rt_disjoint_hi; unfold AF.SLOT_STACK in *; lia).
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. apply HOW.
    destruct (Z_lt_le_dec a (sp - 16)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec a sp) as [H2|H2]; [|right; exact H2].
    exfalso. apply Hns. unfold AC.a_store_ok. right; left. unfold AF.SLOT_STACK in *. split; lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as [HAH' _ HSTKeq _].
  assert (HSTKS : LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { destruct (LFr.stk_split rsegs mem (g_S g - AF.SLOT_STACK) (sp - 16) (g_S g) Hwin ltac:(lia)) as (Hw1 & Hw2).
    destruct (LFr.stk_split rsegs mem (sp - 16) sp (g_S g) Hw2 ltac:(lia)) as (_ & Hw3).
    destruct (LFr.stk_split rsegs mem' (sp - FN_STACK) (sp - 16) sp HSTKW
                ltac:(unfold FN_STACK; lia)) as (_ & HwW).
    assert (Hw1' : LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) (sp - 16)).
    { eapply (LFr.stk_transport rsegs _ mem mem'); [exact Hw1 | exact MU | exact WM |].
      intros x Hx. left. apply HOW. lia. }
    assert (Hw3' : LFr.stk rsegs mem' sp (g_S g)).
    { eapply (LFr.stk_transport rsegs _ mem mem'); [exact Hw3 | exact MU | exact WM |].
      intros x Hx. left. apply HOW. lia. }
    apply (LFr.stk_merge rsegs mem' _ sp _); [| exact Hw3' | lia].
    apply (LFr.stk_merge rsegs mem' _ (sp - 16) _); [exact Hw1' | exact HwW | lia]. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. apply (KindBGlue.mbyte_munch sg [(sp - 16, sp)] mem mem' x MU).
    - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - apply HOW. left. unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { exists A, sp, s5.
    split; [exact (AsanRTInv.RT_store sp sp mem mem' md md _ HRT MU WM Hallapp Hrtdj)|].
    split; [exact HAH'|].
    split; [exact HroM|].
    split.
    { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
      - destruct Hcse as (Hthrm & Hlockm). split.
        + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
          * lia.
          * rewrite Hthr in Hx. cbn in Hx. lia.
        + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
          * lia.
          * rewrite Hlock in Hx. cbn in Hx. lia.
      - intros k Hk. rewrite KBlo.
        + exact (Hohd k Hk).
        + rewrite Hhead. lia.
        + rewrite Hhead. lia. }
    split; [exact Hhalt|].
    split.
    { intros a Hin. rewrite KBlo.
      - exact (Hgimg a Hin).
      - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        destruct Hil as [E|[]]; injection E as <- <-; lia.
      - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        destruct Hil as [E|[]]; injection E as <- <-; lia. }
    split; [rewrite E2; exact Hr2|].
    split; [exact Hspm|].
    split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
    split; [rewrite HSTKeq; exact Hstklo|].
    split; [rewrite E4; exact Hr4|].
    split; [unfold rg in *; rewrite E8; exact Hr8|].
    split; [unfold rg in *; rewrite E9; exact Hr9|].
    split; [rewrite E3; exact Hr3|].
    split; [unfold rg in *; rewrite E19; exact Hr19|].
    split; [unfold rg in *; rewrite E26; exact Hr26|].
    split; [exact Hfrm|].
    split; [exact Hs5|].
    split; [exact HAm|].
    split; [exact HAS|].
    split; [exact Hspa|].
    split; [exact Hfa|].
    split; [exact HA416|].
    split; [exact HS4|].
    split; [exact HAPP|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
      - left. split; [exact H0|]. split; [exact Hspfr|].
        intros a Ha. rewrite HSTKeq. exact (Hreal a Ha).
      - right. split; [exact Hfr0|]. split.
        + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
          intros k Hk. rewrite <- KBlo.
          * exact (Hw k Hk).
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        + split.
          * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
            exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
            intros k Hk. rewrite KBlo.
            -- exact (Hw k Hk).
            -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
            -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          * refine (fsrec_munch_lo (hb ++ g_H g) mem mem' md _ fr Hrec HAH
                      (proj1 (fr_munch_ul _ _ _) MU) _).
            intros x Hxlo _. apply (proj2 (fr_outside_lib _ _)). apply HOW. left.
            unfold AF.SLOT_STACK in *. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. lia. }
    split.
    { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
      eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. apply HOW. left.
      assert (Hin : in_shadow x).
      { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
        { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
        pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hinfr)) as His.
        replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
        unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
      unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
    split; [exact HSTKS|].
    split.
    { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx. apply HOW. right.
      unfold saved_bytes in Hx. rewrite !length_app, !LMem.length_le8 in Hx. cbn in Hx. lia. }
    split.
    { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
    split; [intros a Hin; exact (sl_addr_keep mem mem' [(sp - 16, sp)] a 1 (HAG a Hin) MU Hallapp)|].
    split; [intros a H1 H2;
            exact (sl_addr_keep mem mem' [(sp - 16, sp)] a 1 (HWA a H1 H2) MU Hallapp)|].
    split; [exact HSHI1|].
    split; [exact HSHI2|].
    split; [exact HSHI3|].
    split; [exact Hhb|]. split; [exact Hlive|]. split.
    (* the input block is below stklo <= S - SLOT_STACK < sp - 16 (fra_in_apart), so outside the window *)
    { eapply fl_bytes; [exact Hinb | exact MU |]. intros x Hx.
      destruct (Hinap x ltac:(unfold g_n, nlen; lia)) as (_ & Hxlo & _ & _). apply HOW. left. lia. }
    { intros Hn. destruct (Hinblk Hn) as (Hin & Had). split; [exact Hin|].
      exact (sl_addr_keep mem mem' [(sp - 16, sp)] (g_p g) (g_n g) Had MU Hallapp). } }
  apply (sl_fra_move g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
Qed.

(* ---- The S-anchored callee transport (image-A push 6b, a Theorem Labs lane's statement 3ef2305c85, a Theorem Labs lane ruling
   2026-10-27), with the image-B values: the 448-byte save area [A, A + 448), the frame-base spill
   [A + 336, A + 344), the fr reload and selector spills [A + 40, A + 56). ---- *)

(* Every loaded segment that holds an address range of n >= 1 bytes ends at or below top when all of them do
   (the image-A twin is lib/A/Prog/Seg/Tac_b5.v's b5_find_below; prover a Theorem Labs lane's copy is Seg/F13.v find_segment_below). *)
Lemma sl_find_below : forall sgs top x n s,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sgs = true ->
  find_segment sgs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  induction sgs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* ro_agree survives a run that writes nothing below GT: every read-only image byte is below GT (every loaded
   segment ends at or below GT, checked by computation). *)
Lemma sl_ro_keep : forall W mem mem',
  ro_agree rsegs mem -> Frame.munch W mem mem' -> (forall x, 0 <= x < AC.GT -> Frame.outside W x) ->
  ro_agree rsegs mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros W mem mem' Hro MU Hlo. apply (ro_agree_same rsegs mem mem' Hro).
  intros a Ha. apply MU. apply Hlo.
  pose proof (bv_unsigned_in_range 64 a) as Hr.
  unfold LMem.ro_addr in Ha.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate Ha].
  destruct (sl_find_below rsegs AC.GT (bv_unsigned a) 1 s ltac:(vm_compute; reflexivity) E ltac:(lia))
    as [L|L]; [lia | discriminate L].
Qed.

(* FRA moves across a program callee whose contract gives the bespoke post (munch over its own stack window
   [sp - K, sp), wmono) instead of a_call_post, and across the lazy-page materialization md -> md' of the run:
   sl_fr_cl with W = [(sp - K, sp)], then sl_fra_move. The caller gives the S-anchored window of mem' itself
   (FRA's own conjunct, kept through the callee), any K <= FN_STACK (a K < 0 window is empty; it is read as
   K = 0), the window top below APPMEM_END, the frame header apart from the window and the frame below
   APPMEM_END. The rest comes from FRA: the window is above HIGHMEM_BEG (stklo <= sp - FN_STACK by fra_win,
   HIGHMEM_BEG <= stklo by a_laws_stack_high), so it is app memory and a_store_ok (AH / stklo by sl_ah_stk), and
   misses the image, RT and the frame shadow (fr + 3136 <= APPMEM_END, so Sfr fr + 392 <= HIGHMEM_BEG); the
   spills [A + 40, A + 56), [A + 336, A + 344) and the saved registers [S - 104, S) are at or above sp
   (sp <= A, A + 448 <= S). The side-arm FakeStack record and the input block: the window is at or above stklo
   (fsrec_stklo; fra_in_apart puts the input block below stklo). mem_inv is not involved (FRA does not carry it). *)
Lemma sl_callee_keep : forall g fr hb regs regs' mem mem' md md' K,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch [(AC.aspZ regs - K, AC.aspZ regs)] mem mem' -> Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  K <= FN_STACK -> AC.aspZ regs <= APPMEM_END ->
  (AC.aspZ regs <= fr \/ fr + 24 <= AC.aspZ regs - K) -> fr + FRAME_BYTES <= APPMEM_END ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' K HFRA MU WM Hwin' HK Hsp Hhdr Hfrapp E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & _).
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  (* the window as run: K0 = max 0 K (the same bytes; empty for K <= 0) *)
  remember (Z.max 0 K) as K0 eqn:HK0e.
  assert (HK0 : 0 <= K0 <= FN_STACK) by lia.
  assert (MU0 : Frame.munch [(AC.aspZ regs - K0, AC.aspZ regs)] mem mem').
  { intros x Hx. apply MU. cbn [Frame.outside] in *. destruct Hx as (Hx & _). split; [lia | exact I]. }
  destruct (sl_ah_stk g fr hb regs mem mem' md K0 HFRA HK0 MU0 WM) as (HAH' & Hstkeq).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    _ & _ & _ & _ & _ & _ & _ & Hwin & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold AC.GT in Hgt.
  assert (Hlo : HIGHMEM_BEG <= AC.aspZ regs - K0) by lia.
  assert (Hout : forall x, x < AC.aspZ regs - K0 \/ AC.aspZ regs <= x ->
                   Frame.outside [(AC.aspZ regs - K0, AC.aspZ regs)] x).
  { intros x Hx. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
    assert (HA64 : 0 <= A < 2 ^ 64).
    { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  apply (sl_fra_move g fr hb regs' regs' mem' md md');
    [| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hmat].
  apply (sl_fr_cl g fr hb regs regs' mem mem' md [(AC.aspZ regs - K0, AC.aspZ regs)] HFRA MU0 WM).
  - apply (sl_ro_keep _ mem mem' Hro MU0). intros x Hx. apply Hout. left.
    unfold AC.GT, HIGHMEM_BEG in *. lia.
  - cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, APPMEM_END in *. lia.
  - apply rt_disjoint_hi. exact Hlo.
  - exact HAH'.
  - exact Hstkeq.
  - intros x Hx. apply Hout. left. unfold HIGHMEM_BEG in *. lia.
  - intros x Hx. apply Hout. destruct Hhdr as [Hd|Hd]; lia.
  - intros A' HA' HA'r x Hx. apply Hout. right. rewrite (HA9 A' HA' HA'r) in Hx. lia.
  - intros x Hx. apply Hout. right. lia.
  - intros x Hx. apply Hout. left. unfold Sfr, shadow_addr, ASAN_K in Hx.
    pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.mod_pos_bound fr 8 ltac:(lia)).
    unfold APPMEM_END, HIGHMEM_BEG in *. lia.
  - intros A' HA' HA'r x Hx. apply Hout. right. rewrite (HA9 A' HA' HA'r) in Hx. lia.
  - apply (fsrec_stklo (hb ++ g_H g) mem mem' md _ fr HAH MU0).
    intros x Hx _. apply Hout. left. lia.
  - intros x Hx. destruct (fra_in_apart B APIf ra g fr hb regs mem md HFRA x Hx) as (_ & Hxlo & _ & _).
    apply Hout. left. lia.
  - exact Hwin'.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

(* ==== Push 5c: the transports of the entry-state relation ENT (SlotInv.v).
   ent_mat moves ENT across lazy-page materialization (the model step of sl_run), ent_munch / ent_store across a
   store of the segment's own run, ent_call across a callee's a_call_post, ent_entry gives ENT at the entry cut,
   and ent_post turns ENT at 0x82f5c into the slot post. *)

(* Every byte of the image lies below GT, the top of the image's writable data rounded to a page
   (struct.asan.runtime RT4.3): the loaded segments' tops, checked by computation. *)
Definition img_tops_ok : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? AC.GT) rsegs.

Lemma img_tops_true : img_tops_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img_below_GT : forall a, AC.a_in_img a -> 0 <= a < AC.GT.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros a (s & Hs & Hr).
  pose proof (proj1 (forallb_forall _ _) img_tops_true s Hs) as H. apply Z.leb_le in H.
  pose proof (N2Z.is_nonneg (seg_base s)) as Hb. lia.
Qed.

(* An address of a loaded segment: the errno word and the runtime's out-of-memory flag, which the slot post and
   a_call_post's frame clause name. *)
Definition in_img_b (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma in_img_b_sound : forall a, in_img_b a = true -> AC.a_in_img a.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros a H. apply existsb_exists in H. destruct H as (s & Hs & He).
  apply andb_prop in He as (H1 & H2). apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists s. split; [exact Hs | lia].
Qed.

Lemma errno_in_img : forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> AC.a_in_img a.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros a Ha.
  assert (E : a = AC.a_errno AC.ASYMS \/ a = AC.a_errno AC.ASYMS + 1 \/ a = AC.a_errno AC.ASYMS + 2 \/
              a = AC.a_errno AC.ASYMS + 3) by lia.
  destruct E as [ -> | [ -> | [ -> | -> ] ] ]; apply in_img_b_sound; vm_compute; reflexivity.
Qed.

Lemma oom_in_img : AC.a_in_img (AC.as_oom AC.ASYMS).
Proof. apply in_img_b_sound. vm_compute. reflexivity. Qed.

(* An image byte lies on a page the image maps. *)
Lemma img_on_page : forall a, AC.a_in_img a -> AC.a_on_img_page a.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros a (s & Hs & Hr). exists s. split; [exact Hs|].
  pose proof (N2Z.is_nonneg (seg_base s)) as Hb. pose proof (N2Z.is_nonneg (seg_size s)) as Hn.
  revert Hr Hb Hn. generalize (Z.of_N (seg_base s)). generalize (Z.of_N (seg_size s)).
  intros n b Hr Hb Hn. Z.div_mod_to_equations. lia.
Qed.

(* Two addresses in one 8-byte granule whose base is a multiple of 8 lie on the same image page: a segment's
   page-rounded bounds are multiples of 4096, hence of 8. *)
Lemma gran_img_page : forall G x a, G mod 8 = 0 -> G <= x < G + 8 -> G <= a < G + 8 ->
  AC.a_on_img_page a -> AC.a_on_img_page x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros G x a HG Hx Ha (s & Hs & Hr). exists s. split; [exact Hs|].
  assert (HLO : (Z.of_N (seg_base s) / 4096 * 4096) mod 8 = 0).
  { replace (Z.of_N (seg_base s) / 4096 * 4096)
      with ((Z.of_N (seg_base s) / 4096 * 512) * 8) by lia. apply Z_mod_mult. }
  assert (HHI : ((Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096) mod 8 = 0).
  { replace ((Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096)
      with (((Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 512) * 8) by lia.
    apply Z_mod_mult. }
  revert Hr HLO HHI. generalize (Z.of_N (seg_base s) / 4096 * 4096).
  generalize ((Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096).
  intros HI LO Hr HLO HHI. revert HG Hx Ha Hr HLO HHI HFBv HFSv. clear. intros.
  Z.div_mod_to_equations. lia.
Qed.

(* No image byte is a live block's byte, its word slack or the shadow of one of those: a block's bytes lie off
   the image's pages (a_laws_blocks), its slack lies in the same 8-byte granule as its last byte (the base is
   16-aligned, so the slack reaches the next multiple of 8), and every shadow byte is at or above ASAN_K, which
   is above GT. *)
Lemma img_not_blk_ext : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.a_in_img a -> ~ AC.in_blk_ext H a.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md a HAH Himg Hx.
  pose proof (img_below_GT a Himg) as HaGT. unfold AC.GT in HaGT.
  destruct Hx as [Hb | [Hsl | (b & Hb & Heq)]].
  - destruct Hb as (p & n & Hin & Hr).
    destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ _ _ Hall].
    destruct (Hall a ltac:(lia)) as (_ & _ & Hni & _ & _). exact (Hni Himg).
  - destruct Hsl as (p & n & Hin & Hr).
    destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [Hal Hp4 _ _ Hall].
    pose proof (AC.a_laws_block_size _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md p n HAH Hin)
      as Hn0.
    assert (Hm : 0 <= n mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eq_dec (n mod 8) 0) as [E|E].
    { rewrite E in Hr. change ((8 - 0) mod 8) with 0 in Hr. lia. }
    rewrite (Z.mod_small (8 - n mod 8) 8) in Hr by lia.
    pose proof (Z.mod_eq p 16 ltac:(lia)) as Ep16. rewrite Hal in Ep16.
    pose proof (Z.mod_eq n 8 ltac:(lia)) as En8.
    destruct (Hall (p + n - 1) ltac:(lia)) as (_ & _ & _ & Hnp & _).
    apply Hnp. apply (gran_img_page (p + n - n mod 8) (p + n - 1) a).
    + replace (p + n - n mod 8) with ((2 * (p / 16) + n / 8) * 8) by lia. apply Z_mod_mult.
    + lia.
    + lia.
    + exact (img_on_page a Himg).
  - subst a. unfold shadow_addr, ASAN_K in HaGT.
    assert (Hb0 : 0 <= b).
    { destruct Hb as [(p & n & Hin & Hr) | (p & n & Hin & Hr)];
        destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ Hp4 _ _ _];
        pose proof (AC.a_laws_block_size _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                      H mem md p n HAH Hin); lia. }
    assert (Hd : 0 <= b / 8) by (apply Z.div_pos; lia).
    lia.
Qed.

(* On an image byte the runtime's ownership is the same in two states that both satisfy the heap invariant and
   agree on the stack bottom and the 16 bytes at tp (a_laws_owned_run, whose block-extent premises every image
   byte meets). *)
Lemma ent_owned_img : forall H H' mem md mem' md' a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall i, 0 <= i < 16 ->
     mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i)) ->
  AC.a_in_img a ->
  (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a <->
   AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a).
Proof.
  intros H H' mem md mem' md' a HAH HAH' Hsk Htp Himg.
  exact (AC.a_laws_owned_run _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
           H H' mem md mem' md' a HAH HAH' Hsk Htp
           (img_not_blk_ext H mem md a HAH Himg) (img_not_blk_ext H' mem' md' a HAH' Himg)).
Qed.

(* The addresses ENT speaks of: the bytes of the entry blocks the target does not keep, the image's bytes, the
   stack at or above the entry sp S, the shadow bytes of the image and of that stack, and (ENT append #1) the shadow
   bytes of those entry blocks. *)
Definition ent_kept (g : ghost) (x : Z) : Prop :=
  (exists q k i, In (q, k) (g_H g) /\ ~ In (q, k) (g_T g) /\ 0 <= i < k /\ x = q + i) \/
  AC.a_in_img x \/ (g_S g <= x < APPMEM_END) \/
  (exists b, (AC.a_in_img b \/ g_S g <= b < APPMEM_END) /\ x = shadow_addr b) \/
  (exists q k i, In (q, k) (g_H g) /\ ~ In (q, k) (g_T g) /\ 0 <= i < k /\ x = shadow_addr (q + i)).

(* ENT moves across a run that writes none of those addresses, keeps the stack bounds, and makes the runtime own
   no image byte it did not own. This is the general form; ent_store specialises it to the frame, the frame's
   shadow and the slot window. ENT append #1 (the entry blocks' shadow) comes from ent_kept's fifth case. *)
Lemma ent_munch : forall g hb mem mem' md W,
  ENT APIf g hb mem md ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md ->
  Frame.munch W mem mem' ->
  (forall x, ent_kept g x -> Frame.outside W x) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, AC.a_in_img a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) ->
  ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g hb mem mem' md W HENT HAH MU HW Hlo Hhi Hown.
  destruct HENT as (Hasp & Htp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hkshd & Hcls).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (Hkeep : forall x, ent_kept g x -> 0 <= x < 2 ^ 64 ->
            mbyte rsegs mem' x = mbyte rsegs mem x /\ (writable_at rsegs mem x <-> writable_at rsegs mem' x)).
  { intros x Hk Hx. split.
    - exact (mbyte_munch rsegs W mem mem' x MU Hx (HW x Hk)).
    - exact (writable_munch rsegs W mem mem' x MU Hx (HW x Hk)). }
  split; [exact Hasp|]. split; [exact Htp|]. split; [exact HTH|]. split; [exact Hfs|]. split; [exact Hfz|]. split; [exact Hmdl|].
  split; [rewrite Hlo; exact Hslo|].
  split; [rewrite Hhi; exact Hshi|].
  split.
  { intros q k i Hin Hni Hi.
    assert (Hr : 0 <= q + i < 2 ^ 64).
    { destruct (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as [_ Hq _ _ Hall].
      destruct (Hall (q + i) ltac:(lia)) as (Happ & _).
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ. lia. }
    assert (Hk : ent_kept g (q + i))
      by (left; exists q, k, i; split; [exact Hin | split; [exact Hni | split; [exact Hi | reflexivity]]]).
    rewrite (proj1 (Hkeep (q + i) Hk Hr)). exact (Hblk q k i Hin Hni Hi). }
  split.
  { intros a Hia Ho1 Ho2 Hg He.
    assert (Hr : 0 <= a < 2 ^ 64) by (pose proof (img_below_GT a Hia) as X; unfold AC.GT in X; lia).
    destruct (Hkeep a (or_intror (or_introl Hia)) Hr) as (Hm & Hw).
    destruct (Himg a Hia Ho1 (fun X => Ho2 (Hown a Hia X)) Hg He) as (Hm0 & Hw0).
    split; [rewrite Hm; exact Hm0|].
    split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Ha.
    assert (Hr : 0 <= a < 2 ^ 64) by lia.
    destruct (Hkeep a (or_intror (or_intror (or_introl Ha))) Hr) as (Hm & Hw).
    destruct (Habv a Ha) as (Hm0 & Hw0).
    split; [rewrite Hm; exact Hm0|].
    split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Hor.
    assert (Hb0 : 0 <= a)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT a Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hdiv : 0 <= a / 8 <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Hrs : 0 <= shadow_addr a < 2 ^ 64).
    { unfold shadow_addr, ASAN_K.
      destruct Hor as [Hi|Hr]; [pose proof (img_below_GT a Hi) as X; unfold AC.GT in X|]; lia. }
    assert (Hk : ent_kept g (shadow_addr a))
      by (right; right; right; left; exists a; split; [exact Hor | reflexivity]).
    rewrite (proj1 (Hkeep (shadow_addr a) Hk Hrs)). exact (Hshd a Hor). }
  split.
  { (* ENT append #1: the run leaves the entry blocks' shadow bytes alone, by ent_kept's fifth case. *)
    intros q k i Hin Hni Hi.
    destruct (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as [_ Hq _ _ Hall].
    destruct (Hall (q + i) ltac:(lia)) as (Happ & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ.
    assert (Hdiv : 0 <= (q + i) / 8 <= q + i)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Hrs : 0 <= shadow_addr (q + i) < 2 ^ 64) by (unfold shadow_addr, ASAN_K; lia).
    assert (Hk : ent_kept g (shadow_addr (q + i)))
      by (right; right; right; right; exists q, k, i;
          split; [exact Hin | split; [exact Hni | split; [exact Hi | reflexivity]]]).
    rewrite (proj1 (Hkeep (shadow_addr (q + i)) Hk Hrs)). exact (Hkshd q k i Hin Hni Hi). }
  (* #14 names only the ghost: the same witness. *)
  exact Hcls.
Qed.

(* The model shape ENT carries: a change of the page maps over an os_upd image of the entry model is again an
   os_upd image of it, with the same fd table, file system and pins. *)
Lemma with_vmmaps_os : forall vm vm0 fds0 fs0 pins0 (m : Model),
  with_vmmaps vm (os_upd vm0 fds0 fs0 pins0 m) = os_upd vm fds0 fs0 pins0 m.
Proof.
  intros vm vm0 fds0 fs0 pins0 [[t p] [v l z] io [fs] [h ti c ss sm ch u sa k sp at_ pins] li tm].
  reflexivity.
Qed.

Lemma md_shape_step : forall (m md1 md2 : Model) lz mt vm0 fds0 fs0 pins0 lz1 mt1 vm1,
  md1 = with_vm_backing lz mt (os_upd vm0 fds0 fs0 pins0 m) ->
  md2 = with_vm_backing lz1 mt1 (with_vmmaps vm1 md1) ->
  md2 = with_vm_backing lz1 mt1 (os_upd vm1 fds0 fs0 pins0 m).
Proof.
  intros m md1 md2 lz mt vm0 fds0 fs0 pins0 lz1 mt1 vm1 -> ->.
  destruct m as [[t p] [v l z] io [fs] [h ti c ss sm ch u sa k sp at_ pins] li tm]. reflexivity.
Qed.

(* ENT moves across lazy-page materialization: a_laws_mat_le keeps the heap invariant, ownership, stklo and
   stkhi, and mat_le_shape keeps the model's shape over the entry model. *)
Lemma ent_mat : forall g hb mem md md',
  ENT APIf g hb mem md -> AsanLift.mat_le md md' -> ENT APIf g hb mem md'.
Proof.
  intros g hb mem md md' HENT Hmat.
  destruct (lw_mat_le (APIf rc) (hb ++ g_H g) mem md md' Hmat) as [_ Hown Hlo Hhi].
  destruct HENT as (Hasp & Htp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hkshd & Hcls).
  split; [exact Hasp|]. split; [exact Htp|]. split; [exact HTH|]. split; [exact Hfs|]. split; [exact Hfz|].
  split.
  { destruct Hmdl as (lz & mt & vm0 & fds0 & pins0 & Hmd & Hfd).
    destruct (AC.mat_le_shape (os_upd vm0 fds0 (m_fs (g_md g)) pins0 (g_md g)) md md' lz mt
                (m_vmmaps (os_upd vm0 fds0 (m_fs (g_md g)) pins0 (g_md g)))
                ltac:(rewrite with_vmmaps_os, os_upd_vmmaps; exact Hmd) Hmat)
      as (lz2 & mt2 & vm2 & Hmd').
    exists lz2, mt2, vm2, fds0, pins0. split; [|exact Hfd].
    rewrite Hmd', with_vmmaps_os. reflexivity. }
  split; [rewrite Hlo; exact Hslo|].
  split; [rewrite Hhi; exact Hshi|].
  split; [exact Hblk|].
  split.
  { intros a Hia Ho1 Ho2 Hg He. exact (Himg a Hia Ho1 (fun X => Ho2 (proj2 (Hown a) X)) Hg He). }
  split; [exact Habv|]. split; [exact Hshd|].
  split; [exact Hkshd | exact Hcls].
Qed.

(* ENT moves across a store of the segment's own run, when the run writes only inside the slot window below the
   entry sp, the frame, or the frame's shadow: no byte of an entry block, of the image, of the stack at or above
   S, or of the shadow of those, is written. The frame is below S on both arms (FRA's fr + 3136 <= A <= S), the
   image is below GT <= fr (fra_app), and a shadow byte is never app memory. *)
Lemma ent_store : forall g fr hb regs mem mem' md W,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
     (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, AC.a_in_img a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) ->
  ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md W HENT HFRA MU HWin Hlo Hhi Hown.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Happfr).
  pose proof HENT as HE0. destruct HE0 as (Hasp & _).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & _ & _).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  unfold AC.GT in HGTfr. unfold HIGHMEM_BEG in Hhigh.
  assert (Hfr8 : fr mod 8 = 0) by (pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
                                   replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
  assert (Hfr0 : 0 <= fr) by (pose proof (Happfr fr ltac:(lia)) as X;
                              unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
  assert (Hfrd : 0 <= fr / 8) by (apply Z.div_pos; lia).
  assert (Hfrd8 : 8 * (fr / 8) <= fr) by (apply Z.mul_div_le; lia).
  (* every byte of the frame's 392 shadow bytes is the shadow byte of a frame byte *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happfr _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  (* an address that is neither in the window, nor in the frame, nor in the frame's shadow is outside W *)
  assert (Hreg : forall x, 0 <= x < 2 ^ 64 -> ~ (g_S g - AF.SLOT_STACK <= x < g_S g) ->
            ~ (fr <= x < fr + FRAME_BYTES) -> ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> Frame.outside W x).
  { intros x Hx H1 H2 H3. destruct (HWin x Hx) as [Ho|[Hw|[Hf|Hs]]];
      [exact Ho | contradiction | contradiction | contradiction]. }
  (* a byte of the frame's shadow is the shadow of a frame byte, so it is not the shadow of an image byte or of
     a byte at or above S *)
  assert (Hshfr : forall b, 0 <= b -> ~ (fr <= b < fr + FRAME_BYTES) ->
            ~ (Sfr fr <= shadow_addr b < Sfr fr + FRAME_SHADOW)).
  { intros b Hb0 Hnb Hin. apply Hnb. unfold Sfr, shadow_addr in Hin.
    revert Hin Hfr8 Hb0 Hfr0 HFBv HFSv. clear. intros. Z.div_mod_to_equations. lia. }
  apply (ent_munch g hb mem mem' md W HENT HAH MU); [| exact Hlo | exact Hhi | exact Hown].
  intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
  - destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
    destruct (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as [_ Hq4 Hend _ Hall].
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    apply Hreg; [exact Hqr | lia | | ].
    + intro Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs _]]]].
      * destruct (Hreal (q + i) Hf) as (Hr1 & _). lia.
      * exact (Hnfs (Hfs (q + i) Hf)).
    + intro Hs. exact (app_not_shadow (q + i) Happq (HshIS (q + i) Hs)).
  - pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
    assert (Happx : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
    apply Hreg; [lia | lia | lia |].
    intro Hs. exact (app_not_shadow x Happx (HshIS x Hs)).
  - assert (Happx : app_mem x) by (unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia).
    apply Hreg; [lia | lia | lia |].
    intro Hs. exact (app_not_shadow x Happx (HshIS x Hs)).
  - assert (Hb0 : 0 <= b)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hnb : ~ (fr <= b < fr + FRAME_BYTES))
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
    assert (Happb : app_mem b).
    { destruct Hor as [Hi|Hr];
        [pose proof (img_below_GT b Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
        |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
    pose proof (shadow_of_app b Happb) as Hsb.
    destruct (in_shadow_range (shadow_addr b) Hsb) as (R1 & R2).
    pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
    apply Hreg.
    + lia.
    + lia.
    + intro Hf. exact (app_not_shadow (shadow_addr b) (Happfr _ Hf) Hsb).
    + exact (Hshfr b Hb0 Hnb).
  - destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
    destruct (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as [_ Hq4 Hend _ Hall].
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
    assert (Hb0 : 0 <= q + i) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    assert (Hnb : ~ (fr <= q + i < fr + FRAME_BYTES)).
    { intro Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs _]]]].
      - destruct (Hreal (q + i) Hf) as (Hr1 & _). lia.
      - exact (Hnfs (Hfs (q + i) Hf)). }
    pose proof (shadow_of_app (q + i) Happq) as Hsb.
    destruct (in_shadow_range (shadow_addr (q + i)) Hsb) as (R1 & R2).
    pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
    apply Hreg.
    + lia.
    + lia.
    + intro Hf. exact (app_not_shadow (shadow_addr (q + i)) (Happfr _ Hf) Hsb).
    + exact (Hshfr (q + i) Hb0 Hnb).
Qed.

(* ENT moves across a callee's a_call_post: the callee changes memory only in its own window [sp - K, sp), in the
   bytes of `touched` (the block it gives or takes back), in errno, in the out-of-memory flag and in its own
   bytes. None of those is an address ENT speaks of: the window lies below the entry sp S, `touched` is below S,
   off the image and off the entry blocks, errno and the flag are image bytes that the allocator contracts keep,
   and the entry blocks and the image bytes stay unowned (ent_owned_img). *)
Lemma ent_call : forall g fr hb hb' regs mem md regs' mem' md' touched K,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    K (hb ++ g_H g) regs mem md touched (hb' ++ g_H g) regs' mem' md' ->
  0 <= K <= FN_STACK ->
  (forall a, touched a -> app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a) ->
  AC.a_errno_kept AC.ASYMS mem mem' ->
  ENT APIf g hb' mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb hb' regs mem md regs' mem' md' touched K HENT HFRA Hcp HK Hto Hek.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HENT as HE0. destruct HE0 as (Hasp & Hgtp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hkshd & Hcls).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & _ & _).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  unfold HIGHMEM_BEG in Hhigh.
  pose proof Hcp as Hah'; apply AC.a_call_post_ah in Hah'.
  pose proof Hcp as Hsk; apply AC.a_call_post_stklo in Hsk.
  pose proof Hcp as Hskh; apply AC.a_call_post_stkhi in Hskh.
  pose proof Hcp as Hoom; apply AC.a_call_post_oom in Hoom.
  assert (Htp : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (Hfr : forall a, 0 <= a < 2 ^ 64 ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md' a ->
            ~ AC.a_window K regs a -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
            a <> AC.as_oom AC.ASYMS -> ~ touched a ->
            mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a))
    by (eapply AC.a_call_post_frame; exact Hcp).
  (* the callee's window is inside the slot window, so it is below S *)
  assert (Hwin2 : forall a, AC.a_window K regs a ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < g_S g).
  { intros a Ha. unfold AC.a_window in Ha. unfold FN_STACK in Hwlo.
    rewrite Haspz in Ha. rewrite Haspz in Hwlo. lia. }
  assert (Hoomimg : AC.a_in_img (AC.as_oom AC.ASYMS)) by exact oom_in_img.
  split; [exact Hasp|]. split; [exact Hgtp|]. split; [exact HTH|]. split; [exact Hfs|]. split; [exact Hfz|].
  split.
  { destruct Hmdl as (lz & mt & vm0 & fds0 & pins0 & Hmd & Hfd).
    pose proof Hcp as Hmd1; apply AC.a_call_post_model in Hmd1. destruct Hmd1 as (lz1 & mt1 & vm1 & Hmd1).
    exists lz1, mt1, vm1, fds0, pins0. split; [|exact Hfd].
    exact (md_shape_step (g_md g) md md' lz mt vm0 fds0 (m_fs (g_md g)) pins0 lz1 mt1 vm1 Hmd Hmd1). }
  split; [rewrite Hsk; exact Hslo|].
  split; [rewrite Hskh; exact Hshi|].
  split.
  { intros q k i Hin Hni Hi.
    destruct (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as [_ Hq4 Hend _ Hall].
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & Hnimg & _ & _).
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    assert (Hinb : AC.in_blocks (g_H g) (q + i)) by (exists q, k; split; [exact Hin | lia]).
    assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (Hinb2 : AC.in_blocks (hb' ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (Hn1 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md (q + i))
      by exact (lwn_byte (lw_not_owned (APIf rc) (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
    assert (Hn2 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md' (q + i))
      by exact (lwn_byte (lw_not_owned (APIf rc) (hb' ++ g_H g) mem' md' (q + i) Hah' (or_introl Hinb2))).
    assert (Hnw : ~ AC.a_window K regs (q + i)) by (intro Hw; pose proof (Hwin2 _ Hw); lia).
    assert (Hne : ~ (AC.a_errno AC.ASYMS <= q + i < AC.a_errno AC.ASYMS + 4))
      by (intro He; exact (Hnimg (errno_in_img (q + i) He))).
    assert (Hno : q + i <> AC.as_oom AC.ASYMS) by (intro He; apply Hnimg; rewrite He; exact Hoomimg).
    assert (Hnt : ~ touched (q + i)) by (intro Ht; exact (proj2 (proj2 (proj2 (Hto (q + i) Ht))) Hinb)).
    rewrite (proj1 (Hfr (q + i) Hqr Hn1 Hn2 Hnw Hne Hno Hnt)).
    exact (Hblk q k i Hin Hni Hi). }
  split.
  { intros a Hia Ho1 Ho2 Hg He.
    pose proof (img_below_GT a Hia) as Hag. unfold AC.GT in Hag.
    assert (Ho2' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a)
      by (intro X; apply Ho2;
          exact (proj1 (ent_owned_img (hb ++ g_H g) (hb' ++ g_H g) mem md mem' md' a HAH Hah' Hsk Htp Hia) X)).
    destruct (Himg a Hia Ho1 Ho2' Hg He) as (Hm0 & Hw0).
    destruct (Z.eq_dec a (AC.as_oom AC.ASYMS)) as [Eo|Eo].
    - subst a. destruct Hek as (_ & Hoomb).
      split; [rewrite Hoomb; exact Hm0|].
      split; intro X; [exact (proj1 Hoom (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hoom X))].
    - destruct (Hfr a ltac:(lia) Ho2' Ho2 ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia) He Eo
                  ltac:(intro Ht; exact (proj1 (proj2 (proj2 (Hto a Ht))) Hia))) as (Hm & Hw).
      split; [rewrite Hm; exact Hm0|].
      split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Ha.
    assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) by lia.
    assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md' <= a < APPMEM_END)
      by (rewrite Hsk; lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a)
      by exact (lwn_byte (lw_not_owned (APIf rc) (hb ++ g_H g) mem md a HAH (or_intror (or_intror (or_intror Hst))))).
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md' a)
      by exact (lwn_byte (lw_not_owned (APIf rc) (hb' ++ g_H g) mem' md' a Hah' (or_intror (or_intror (or_intror Hst'))))).
    destruct (Hfr a ltac:(lia) Hno Hno' ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img a He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X; lia)
                ltac:(intro Ht; pose proof (proj1 (proj2 (Hto a Ht))); lia)) as (Hm & Hw).
    destruct (Habv a Ha) as (Hm0 & Hw0).
    split; [rewrite Hm; exact Hm0|].
    split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Hor.
    assert (Hb0 : 0 <= a)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT a Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hdiv : 0 <= a / 8 <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Hsh1 : in_shadow (shadow_addr a)).
    { apply shadow_of_app. destruct Hor as [Hi|Hr];
        [pose proof (img_below_GT a Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
        |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
    assert (Hsr : 0 <= shadow_addr a < 2 ^ 64)
      by (destruct (in_shadow_range (shadow_addr a) Hsh1) as (R1 & R2); lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact (lw_client_img_shadow (APIf rc) (hb ++ g_H g) mem md a HAH Hi).
      - assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) by lia.
        exact (lwn_shadow (lw_not_owned (APIf rc) (hb ++ g_H g) mem md a HAH (or_intror (or_intror (or_intror Hst))))). }
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md' (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact (lw_client_img_shadow (APIf rc) (hb' ++ g_H g) mem' md' a Hah' Hi).
      - assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md' <= a < APPMEM_END)
          by (rewrite Hsk; lia).
        exact (lwn_shadow (lw_not_owned (APIf rc) (hb' ++ g_H g) mem' md' a Hah' (or_intror (or_intror (or_intror Hst'))))). }
    destruct (in_shadow_range (shadow_addr a) Hsh1) as (R1 & R2).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1.
    destruct (Hfr (shadow_addr a) ltac:(lia) Hno Hno'
                ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                      rewrite <- He in X; lia)
                ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
    rewrite Hm. exact (Hshd a Hor). }
  split.
  { intros q k i Hin Hni Hi.
  destruct (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as [_ Hq4 Hend _ Hall].
  destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & _).
  assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
    by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
  assert (Hinb2 : AC.in_blocks (hb' ++ g_H g) (q + i))
    by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
  assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md (shadow_addr (q + i)))
    by exact (lwn_shadow (lw_not_owned (APIf rc) (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
  assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md' (shadow_addr (q + i)))
    by exact (lwn_shadow (lw_not_owned (APIf rc) (hb' ++ g_H g) mem' md' (q + i) Hah' (or_introl Hinb2))).
  pose proof (shadow_of_app (q + i) Happq) as Hsh1.
  destruct (in_shadow_range (shadow_addr (q + i)) Hsh1) as (R1 & R2).
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1.
  destruct (Hfr (shadow_addr (q + i)) ltac:(lia) Hno Hno'
              ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
              ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
              ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                    rewrite <- He in X; lia)
              ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
  rewrite Hm. exact (Hkshd q k i Hin Hni Hi). }
  (* #14: g_H g is the ENTRY heap, which a call does not change, so the same witness; the call's own block is
     accounted at the call site by Seg/Tac_cls.v's sl_malloc_cls / sl_free_cls. *)
  exact Hcls.
Qed.

(* The model of the entry state is its own os_upd / with_vm_backing image. *)
Lemma md_self : forall m : Model, m = with_vm_backing (m_vm_lazy m) (m_vm_materialized m)
  (os_upd (m_vmmaps m) (m_fds m) (m_fs m) (m_statpins m) m).
Proof. intros [[t p] [v l z] io [fs] [h ti c ss sm ch u sa k sp at_ pins] li tm]. reflexivity. Qed.

(* ENT #14, the per-class fact, as a predicate (names agreed with the image-A lane, 0b6b7fff89f). *)
Definition ent_class_fact (g : ghost) : Prop :=
  exists BE : Z -> Z,
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES -> ClassConsDef.a_class_bytes (g_H g) c <= BE c) /\
    (forall c, 0 <= c < AsanCtrl.K_NUM_CLASSES -> BE c + BC_ctrl c <= 2 ^ 22).

(* ENT at the entry cut: every conjunct is a fact of the entry state about itself, except #14, which is the slot's
   named premise ENTRY_CLASS: the entry heap's per-class bound, owed by the driver (a Theorem Labs lane's
   drv_slot_class_entry_stmt) until a Theorem Labs lane puts it in alib_pre (48004cf7bfc's alib_pre has no class premise; it
   gives only a_live_bytes H <= 5 * 2 ^ 30). It lives in this one-lemma section so that no other lemma (in
   particular no tauto proof) can capture it: only ent_entry and ent_class_entry take it. *)
Section EntryClass.
Hypothesis ENTRY_CLASS : forall g c, Inv_ENTRY B APIf ra empty g c ->
  exists BE : Z -> Z,
    (forall cl, 0 <= cl < AsanCtrl.K_NUM_CLASSES -> ClassConsDef.a_class_bytes (g_H g) cl <= BE cl) /\
    (forall cl, 0 <= cl < AsanCtrl.K_NUM_CLASSES -> BE cl + BC_ctrl cl <= 2 ^ 22).

Lemma ent_entry : forall g c, Inv_ENTRY B APIf ra empty g c -> ENT APIf g [] (g_mem g) (g_md g).
Proof.
  intros g c HI. pose proof (ENTRY_CLASS g c HI) as Hcls.
  destruct HI as (Hc & Hpre & HTH & Hnp & Hgimg & Hasp & Hfz).
  destruct Hpre as (Hcp & Hra & Hp & Hn & Hbuf & Hlen & Hnmax & Hbd & Hag & Hlv & Herrno & Hsn & Hfd & Hfs & Himg).
  split; [exact Hasp|]. split; [eapply AC.a_call_pre_tp; exact Hcp|]. split; [exact HTH|]. split; [exact Hfs|]. split; [exact Hfz|].
  split.
  { exists (m_vm_lazy (g_md g)), (m_vm_materialized (g_md g)), (m_vmmaps (g_md g)),
           (m_fds (g_md g)), (m_statpins (g_md g)).
    split; [apply md_self | reflexivity]. }
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros q k i _ _ _; reflexivity|].
  split; [intros a _ _ _ _ _; split; [reflexivity | split; intro X; exact X]|].
  split; [intros a _; split; [reflexivity | split; intro X; exact X]|].
  split; [intros a _; reflexivity|].
  split; [intros q k i _ _ _; reflexivity | exact Hcls].
Qed.

(* ENT #14 at the entry cut: ENTRY_CLASS itself. *)
Lemma ent_class_entry : forall g c, Inv_ENTRY B APIf ra empty g c -> ent_class_fact g.
Proof. intros g c HI. exact (ENTRY_CLASS g c HI). Qed.
End EntryClass.

(* ==== ENT append #1 (ent_shd: the shadow bytes of the entry blocks the target does not keep; SlotInv.v ENT's 13th
   conjunct, verbatim from FrameAPI.v alib_post). Each lemma is that conjunct of the ENT its transport builds, so a
   segment can cite the one fact it needs without unpacking ENT (names and statements shared with image A). *)
Lemma ent_shadow_of : forall g hb mem md, ENT APIf g hb mem md -> ent_shd g mem.
Proof.
  intros g hb mem md HENT.
  destruct HENT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblks & _). exact Hblks.
Qed.

(* At the entry cut it is a fact of the entry state about itself: the shadow bytes are the entry ones. *)
Lemma ent_shadow_entry : forall g c, Inv_ENTRY B APIf ra empty g c -> ent_shd g (g_mem g).
Proof. intros g c _ q k i _ _ _. reflexivity. Qed.

(* Across a store of the segment's own run (ent_store's premises): the run writes only the slot window, the frame
   and the frame's shadow, and a block's shadow byte is none of those. *)
Lemma ent_shadow_store : forall g fr hb regs mem mem' md W,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
     (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, AC.a_in_img a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) ->
  ent_shd g mem'.
Proof.
  intros g fr hb regs mem mem' md W HENT HFRA MU HWin Hlo Hhi Hown.
  exact (ent_shadow_of g hb mem' md (ent_store g fr hb regs mem mem' md W HENT HFRA MU HWin Hlo Hhi Hown)).
Qed.

(* Across a callee's a_call_post (ent_call's premises): a live block's byte AND its shadow byte are unowned before
   and after (a_laws_not_owned), the shadow byte is not app memory, so it is neither touched nor in the window. *)
Lemma ent_shadow_call : forall g fr hb hb' regs mem md regs' mem' md' touched K,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    K (hb ++ g_H g) regs mem md touched (hb' ++ g_H g) regs' mem' md' ->
  0 <= K <= FN_STACK ->
  (forall a, touched a -> app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a) ->
  AC.a_errno_kept AC.ASYMS mem mem' ->
  ent_shd g mem'.
Proof.
  intros g fr hb hb' regs mem md regs' mem' md' touched K HENT HFRA Hcp HK Hto Hek.
  exact (ent_shadow_of g hb' mem' md'
           (ent_call g fr hb hb' regs mem md regs' mem' md' touched K HENT HFRA Hcp HK Hto Hek)).
Qed.

(* Across lazy-page materialization: memory does not change at all. *)
Lemma ent_shadow_mat : forall g hb mem md md',
  ENT APIf g hb mem md -> AsanLift.mat_le md md' -> ent_shd g mem.
Proof. intros g hb mem md md' HENT _. exact (ent_shadow_of g hb mem md HENT). Qed.

(* ENT #14 names only the ghost: every transport keeps the SAME witness BE. *)
Lemma ent_class_of : forall g hb mem md, ENT APIf g hb mem md -> ent_class_fact g.
Proof.
  intros g hb mem md HENT.
  destruct HENT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcls). exact Hcls.
Qed.

Lemma ent_class_store : forall g fr hb regs mem mem' md W,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md -> Frame.munch W mem mem' -> ent_class_fact g.
Proof. intros g fr hb regs mem mem' md W HENT _ _. exact (ent_class_of g hb mem md HENT). Qed.

Lemma ent_class_call : forall g fr hb hb' regs mem md regs' mem' md' touched K,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    K (hb ++ g_H g) regs mem md touched (hb' ++ g_H g) regs' mem' md' ->
  ent_class_fact g.
Proof. intros g fr hb hb' regs mem md regs' mem' md' touched K HENT _ _. exact (ent_class_of g hb mem md HENT). Qed.

Lemma ent_class_mat : forall g hb mem md md',
  ENT APIf g hb mem md -> AsanLift.mat_le md md' -> ent_class_fact g.
Proof. intros g hb mem md md' HENT _. exact (ent_class_of g hb mem md HENT). Qed.

(* ENT at the post-release epilogue head gives the slot post: every clause of alib_post that compares the return
   state with the entry state is a conjunct of ENT, and the rest are the facts Y3's cut carries. The caller
   supplies a0 = 0 and a_regs_kept, which the 13 reloads 0x82f64-0x82f94 and `addi sp,s0,-448` give. *)
Lemma ent_post : forall g regs' mem' md',
  ENT APIf g [] mem' md' ->
  AsanRTInv.RT (AC.aspZ (g_regs g)) mem' md' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem' md' ->
  ro_agree rsegs mem' -> sink_none B mem' md' -> m_halted md' = None ->
  getr regs' 10 = Z_to_bv 64 0 -> AC.a_regs_kept (g_regs g) regs' ->
  (forall a, AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4 -> writable_at rsegs mem' a) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> writable_at rsegs mem' a /\ addressable mem' a 1) ->
  Post B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom rsegs)) md').
Proof.
  intros g regs' mem' md' HENT HRT HAH Hro Hsn Hhalt Ha0 Hkept Herrno Hwin.
  pose proof FF as (SEGS & _).
  destruct HENT as (Hasp & Htp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hkshd & Hcls).
  exists fx, (LL 0 (m_fs (g_md g)) []), (g_H g), regs', mem', md', (g_T g).
  split; [rewrite SEGS; reflexivity|].
  split; [exact Hfz|].
  split; [reflexivity|].
  split; [reflexivity|].
  unfold AF.alib_post. rewrite SEGS.
  split; [exact HRT|].
  split; [exact HAH|].
  split; [exact Ha0|].
  split; [exact Hkept|].
  split; [exact Hmdl|].
  split; [exact Hhalt|].
  split; [exact Hslo|].
  split; [exact Hshi|].
  split; [intros q k Hin _; exact Hin|].
  split; [exact Hblk|].
  split; [exact Hkshd|].
  split; [intros a Hia Ho1 Ho2 Hg He; exact (Himg a Hia Ho1 Ho2 Hg He)|].
  split; [intros a (lo & len & HF & _); destruct HF|].
  split; [exact Herrno|].
  split; [intros a Ha; rewrite Hasp in Ha; exact (Habv a Ha)|].
  split; [intros a Hor; rewrite Hasp in Hor; exact (Hshd a Hor)|].
  split; [intros a Ha; rewrite Hasp in Ha; exact (Hwin a Ha)|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hfs|].
  split; [exact Hsn|].
  split; [exact Hro|].
  split; [exact HTH|].
  split; [intros t Ht _; exact Ht|].
  intros t Ht. left. exact Ht.
Qed.

End S.

(* ==== Worked examples: how a segment threads ENT (push 5c). One per kind; copy the three lines.

   A straight call segment (a cut with CUTST, one callee call, a cut at the return). The cut gives
   `FRA ... regs mem md` and `ENT APIf g hb mem md`; the segment already builds FRA' with sl_mid (a callee whose
   post is a_call_post) or with sl_fr_run (a program callee whose post is a munch). Next to that, ENT moves with
   the matching transport, and sl_run's model step with ent_mat:

     (* the allocator calls: wrapper_malloc at R7, wrapper_free at R20, with K = AC.AK_MALLOC / AC.AK_FREE *)
     pose proof (ent_call g fr hb hb' regs mem md regs' mem' md' touched AC.AK_FREE
                   HENT HFRA Hcp ltac:(cbv; lia) Htouched Herrkept) as HENT'.
     (* a program callee (its post is a munch of its window and its output cells) *)
     pose proof (ent_store g fr hb regs mem mem' md W HENT HFRA MU HWcases
                   HstkloEq HstkhiEq HownKept) as HENT'.
     (* after sl_run's continuation, which hands you Hmat : AsanLift.mat_le md md' *)
     pose proof (ent_mat g hb mem' md md' HENT' Hmat) as HENT''.

   The call's premise Htouched is `forall a, touched a -> app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\
   ~ AC.in_blocks (g_H g) a`: for wrapper_malloc, `touched` is the new block, which a_new_block puts below
   stklo (so below S), off the image and off every block of H; for wrapper_free, it is the harness buffer of hb,
   which a_laws_disjoint keeps apart from the entry blocks. Herrkept is the `a_errno_kept` the allocator
   contract returns next to its a_call_post.

   The store's premise HWcases is `forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/ the slot window \/ the
   frame \/ the frame's FRAME_SHADOW shadow bytes`: the same case split the segment already makes for sl_fr_run's
   HWout premise, with the window arm added for a callee that writes below sp. HownKept is the "owned" half of
   the a_laws_store / a_laws_fs_store the segment runs for AH, read left to right.

   A loop segment (a cut at the loop head, a body that returns to the head). ENT is a conjunct of the head's
   CUTST, so the loop invariant carries it with no extra index; the body threads it exactly as the straight
   segment does, and the induction closes with the same three lines:

     (* at the head, after `destruct Hcut as (regs & mem & md & fr & -> & HFRA & HENT & HP)` *)
     ... body ...
     pose proof (ent_store g fr hb regs mem mem1 md W HENT HFRA MU HWcases Hlo Hhi Hown) as HENT1.
     pose proof (ent_mat g hb mem1 md md1 HENT1 Hmat) as HENT2.
     apply IH; exists regs1, mem1, md1, fr; split; [reflexivity | split; [exact HFRA1 | split; [exact HENT2 |
       ... ]]].

   At the return the owner of the Y3 segment calls ent_post, whose premises are Inv_B82f5c's (v1.9 pc 0x82f5c) own
   conjuncts plus a0 = 0 and AC.a_regs_kept, which the 13 reloads 0x82f64-0x82f94 and 0x82f60 `addi sp,s0,-448` give. *)
