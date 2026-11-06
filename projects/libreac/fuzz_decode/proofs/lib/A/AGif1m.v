(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif1m.v (commit 95e6f1d72b6, file sha256 a8ba029fc832; written for cgif_file_fuzzer.asan-ubsan 1c29845fe605) onto libreac/fuzz_decode's asan image (pin 5973b76807d8, unstripped twin 4cb0a852e826); module paths changed, names TfibSyms -> GrantSyms; its 6 image addresses moved by code-verified function pairs (3 port_addr_check 0767e70e074a MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 3 hand maps (agreloc-resolve.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); 4 model labels (YG00 mcheck / spin tags) kept; no other numeral changed; later the model labels became the model's tags (202260 -> 3, 449860 -> 12). *)
(* The cgif_file instance of the miss-arm interface AGif0n.AIfaceM (iface_cgif_m), next to AGif1's instance of
   AIface: ARX = ARX_cgif, AOX = aowned, rpre = aregime /\ qmeter, mt = malloc, lpost = qtight, dpost = dpost_cgif,
   rtree = AFl1.refill_tree.  Ported from cgif_file's released miss arm (YFim / YFiw / YFkv / YFl1 / YFj1 / YFiv /
   YG0s) as cgif's instance of AIfaceM:
   - if_mview: the miss seed's cells (YFiw: SEEDM_ok's constant cells, count0, unwinding_valM) from ARm;
   - if_shape_miss: AFi3.malloc_primary_eq;
   - if_refill: CLrefillR.tfib_refill_okR (YFkv.tfib_refill_ok with a raw frame) at the post-tick state, entered as
     YFim.REFILL_PRE enters it (AR at the call-time memory by AR_frame_law_ok, YFim.AR1), with AFkq.refill_tree_apost
     for regs_only (qtight of the post state); errno, which the released aview frame excludes, from the raw frame
     (errno is in the image, never hidden);
   - if_post_miss: AGj1.AR_final (YFj1) at the pop state, Wf / qtight of the final state from YG07.malloc_ok at the
     entry state along the granted path (as AGif1.post_cgif; the entry ARX is read only for Wf, at its own layout);
   - if_post_miss_k: the k twin, AGif1k.AR_final_kw (AGjf.AR_transport over at_RETkw) at the pop state;
   - if_depot_miss: AGif1.depot_cgif at the pop state (cgif's U does not read the state; the entry ARX is not read);
   - if_oom: AFi5.AR_oom (the released miss arm's OOM leaf, YFim TAILN), own_area for the OOM byte and own_core for
     the thread object's unwinding byte;
   - if_stack: YG0s.AR_stack_law_ok;
   - if_view_m / if_owned_m / if_owned_m_k: AGif1's view / owned proofs and AGif1k's owned_k proof, which never read
     rpre;
   - if_mono_join: the join keeps every owned byte outside the new block (st_final only adds the popped chunk). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0m YG08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AFhy AGhy AGis AFi3.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YGAlloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AllocGcgif AGif0cgif AGiy AGix AGj1.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import CLrefill0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AB13 AFkq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YFfk.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AFi5 CLrefillR.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require ImgBaseAG.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AGj6 AGjc AGjb AGif1k.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AGif2cgif AGif1.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order. *)
Set Default Proof Using "All".
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Machine helpers (as in the released miss arm YFim).                                                              *)
Lemma apresent_aview_some : forall (H : word -> bool) m a, apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a Hp. destruct (apresent_mbyte H m a Hp) as [b Hb]. unfold aview. rewrite Hb. cbn. discriminate. Qed.
Lemma aview_rw_some : forall (Hh : word -> bool) m a, 0x98000 <= a < 0x5f6000 -> aview tfibsegs Hh m a <> None.
Proof.
intros Hh m a Ha. unfold aview, mbyte. destruct (mrestrict Hh m (Z_to_bv 64 a)); cbn; [discriminate|].
pose proof (AB13.tfib_rw_rom a Ha) as X. destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | exfalso; exact (X eq_refl)].
Qed.
(* A byte of the image's read-write window is never hidden. *)
Lemma rw_not_hidden : forall (W : world tfibsegs) a, 0x98000 <= a < 0x5f6000 -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [|reflexivity]. exfalso. apply (AB13.tfib_rw_rom a Ha).
unfold seg_rom. rewrite (memory_read1_hidden tfibsegs (w_H W) (w_Hoff W) _ Eh). reflexivity.
Qed.
Lemma In_upd_chunk : forall l k0 k, In k (upd_chunk l k0) -> In k l \/ k = k0.
Proof.
induction l as [|k' t IH]; intros k0 k H; cbn [upd_chunk] in H.
- destruct H as [<-|[]]. right. reflexivity.
- match type of H with context [if ?b then _ else _] => destruct b end.
  + destruct H as [<-|H]; [right; reflexivity | left; right; exact H].
  + destruct H as [<-|H]; [left; left; reflexivity|]. destruct (IH k0 k H) as [X|X]; [left; right; exact X | right; exact X].
Qed.
(* A primary chunk put by upd_chunk adds no section extent (it replaces at most a chunk at the same primary offset). *)
Lemma flat_map_upd_prim : forall (g : chunk -> list (Z * Z)) l k,
(forall k' o, ck_beg k' = PPrim o -> g k' = []) -> (exists p, ck_beg k = PPrim p) ->
flat_map g (upd_chunk l k) = flat_map g l.
Proof.
intros g l k Hg [p Hp]. induction l as [|k' t IH]; cbn [upd_chunk].
- cbn [flat_map]. rewrite (Hg k p Hp). reflexivity.
- rewrite Hp. destruct (ck_beg k') as [|o|r o|c q] eqn:Eb; cbn [sptr_eqb]; try (cbn [flat_map]; rewrite IH; reflexivity).
  destruct (o =? p); cbn [flat_map]; [|rewrite IH; reflexivity].
  rewrite (Hg k p Hp), (Hg k' o Eb). reflexivity.
Qed.
Lemma sec_extents_upd_prim : forall ly S S' k, st_chunks S' = upd_chunk (st_chunks S) k -> (exists p, ck_beg k = PPrim p) ->
sec_extents ly S' = sec_extents ly S.
Proof.
intros ly S S' k E Pk. unfold sec_extents. rewrite E. apply flat_map_upd_prim; [|exact Pk].
intros k' o Eo. cbv beta. rewrite Eo. reflexivity.
Qed.
(* The thread object lies in a zone apart from the shadow (AGiy.T_zone). *)
Lemma T_zone_of : forall ly, layout_ok ly -> img_cover ly -> zone3 (ly_T ly) kThreadObjSize.
Proof.
intros ly LY IMG. pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
exact (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) IT (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl)).
Qed.

Section b.
Variable B : asyms.
Hypothesis TS : GrantSyms B.

(* errno is never owned (YFim.errno_not_owned). *)
Lemma errno_not_owned_cgif : forall ly S W mem md a, AR tfibsegs B ly S W mem md ->
TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
intros ly S W mem md a HAR Ha O.
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. rewrite AB13.tfib_segs_eq. eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. lia. }
apply (proj1 (AR_owned_image_law_ok tfibsegs B ly S W mem md a HAR IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_mview: the miss seed's cells (YFiw.SEEDM_ok over ARm: the constant cells, the instance fields, the class count
   0, the unwinding byte). *)
Lemma mview_cgif : forall inst ly S W mem md n,
ARX_cgif B inst ly S W mem md -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S (chunk_class n)) = [] -> mview B W ly inst mem (chunk_class n).
Proof.
intros inst ly S W mem md n [-> HAR] Hn0 FP Hc.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
pose proof (primary_geometry n Hn0 FP) as (Gc & _).
pose proof (proj1 (Forall_forall _ _) (am_cells B ly S _ HARm)) as AC.
constructor.
- exact LY.
- exact IMG.
- rewrite (am_tsd _ _ _ _ HARm). exact (ts_tsd B TS).
- exact (am_const B ly S _ HARm).
- split; [|split].
  + replace (TFIB_INST + 0x20) with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TS); reflexivity).
    replace (ly_space ly) with (aeval B ly (ASp 0)) by (cbn; lia).
    exact (tfib_const_lookup_sym B TS ly S (w_H W) mem (AInst o_space) 8 (ASp 0) HARm ltac:(clear; vm_compute; reflexivity)).
  + exact (tfib_const_lookup B TS ly S (w_H W) mem (TFIB_INST + 0xe20) 8 0x10000000000 HARm ltac:(clear; vm_compute; reflexivity)).
  + exact (tfib_const_lookup B TS ly S (w_H W) mem (TFIB_INST + 0xe28) 8 0x108000010 HARm ltac:(clear; vm_compute; reflexivity)).
- assert (E : ImgBaseAG.Pv ly (chunk_class n) = aeval B ly (AT (t_cache + 80 * chunk_class n))) by (cbn; unfold ImgBaseAG.Pv; lia).
  rewrite E. refine (cell_holds_val_mem B ly (w_H W) mem (AT (t_cache + 80 * chunk_class n)) 4 (ANum 0) _).
  apply AC. unfold acells. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists (chunk_class n).
  split; [apply In_zseq; lia|]. unfold cache_cells. rewrite Hc. destruct (st_cache_inited S); left; reflexivity.
- refine (cell_holds_val_mem B ly (w_H W) mem (AT t_unwinding) 1 (ANum 0) _).
  apply AC. unfold acells. do 8 (apply in_or_app; right). left. reflexivity.
Qed.

(* if_shape_miss: malloc's primary arm (AFi3.malloc_primary_eq); the join with the spin tag 12 is malloc_join. *)
Lemma shape_miss_cgif : forall n tr S, 0 <= n -> from_primary n = true -> pc_chunks (cache S (chunk_class n)) = [] ->
malloc n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 3 ;; refill_tree (chunk_class n) ;;
                 malloc_join_t 12 n tr (chunk_class n)) S.
Proof. intros n tr S _ FP _. rewrite (malloc_primary_eq n tr S FP). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_refill: the refill callee at the post-tick state (YFim.REFILL_PRE / AR1, then CLrefillR.tfib_refill_okR). *)
Lemma refill_cgif : forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
ARX_cgif B inst ly S0 W mem0 md0 -> rpre_cgif S0 n -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 A_REFILL_RET -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 TFIB_TP ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal tfibsegs (refill_tree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at tfibsegs A_Refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf (ARX_cgif B) (aowned B) qtight inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).
Proof.
intros inst ly S0 W mem0 md0 n sp0 regs mem mat [Ei HAR0] [Hev HQ] Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1 RAW1 PRES1
SP R1 R3 R4 R10 R11 R12 R13.
pose proof (proj1 HAR0) as HARm0. pose proof (am_layout _ _ _ _ HARm0) as LY.
pose proof (img_cover_of_ledger ly S0 md0 (proj1 (proj2 HAR0))) as IMG.
pose proof (lo_top ly LY) as (_ & _ & _ & K2 & _ & _ & K1).
pose proof (T_zone_of ly LY IMG) as ZT.
pose proof (primary_geometry n Hn0 FP) as (Gc & _).
set (cl := chunk_class n) in *. assert (Hcl : 1 <= cl <= 31) by lia.
set (S1 := set_nev (st_nev S0 + 1) S0).
set (md1 := with_vm_backing (m_vm_lazy md0) mat md0).
pose proof (AR_tick B ly S0 W mem0 md0 HAR0 Hev) as HAR1. fold S1 in HAR1.
pose proof (WfP_tick _ S0 (am_wf _ _ _ _ HARm0) Hev) as WfP1. fold S1 in WfP1.
(* AR at the call-time memory (YFim.AR1) *)
assert (HARc : AR tfibsegs B ly S1 W mem md1).
{ apply (AR_frame_law_ok tfibsegs B ly S1 W mem0 md0 mem md1 HAR1).
  - intros a Ha Ho. apply AG1; [exact Ha|]. intros Hst. apply (AR_stack_law_ok tfibsegs B ly S1 W mem0 md0 a HAR1); [lia | exact Ho].
  - intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
    assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
    assert (AV : forall m, aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
    rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
    destruct (Z_lt_le_dec a' (sp0 - AFSTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a' sp0) as [H2|H2]].
    2:{ apply apresent_aview_some. apply PRES1. lia. }
    all: rewrite (AG1 a' Ha' ltac:(lia)); exact Hv.
  - apply m_vmmaps_wvb.
  - apply m_vm_lazy_wvb.
  - apply eager_used_wvb.
  - intros a Ha Hx.
    assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
    assert (HB : kLowShadowBeg <= a < kHighMemBeg) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
    pose proof (zone3_apart_hsh _ _ a ZT HB) as TH.
    unfold YG0d.w64, YG0n.w64 in *. apply RAW1; rewrite unsigned_lit_small by exact Ha'.
    + clear - HB K1 Hlo. unfold kHighMemBeg, AFSTACK in *. lia.
    + clear - TH. unfold t_unwinding, kThreadObjSize in *. lia. }
assert (PRE : refill_pre B ly S1 W regs mem md1 cl).
{ pose proof HAR0 as (_ & _ & [BUD _] & _).
  unfold refill_pre. rewrite SP. unfold raZ. rewrite R1, R3, R4, R10, R11, R12, R13, (ts_tp B TS).
  split; [exact HARc|].
  split; [unfold abudget in *; unfold S1; change (sec_live_bytes (set_nev (st_nev S0 + 1) S0)) with (sec_live_bytes S0);
    change (sec_hulls (set_nev (st_nev S0 + 1) S0)) with (sec_hulls S0); cbn [st_nev set_nev]; unfold EV_A in *; lia|].
  split; [split; [pose proof (wf_prim_ev _ _ _ _ _ WfP1) as PE; lia|];
    split; [exact (aregime_preg_tick S0 cl Hev Hcl) | exact (aregime_mid_tick S0 Hev)]|].
  split; [split; [apply qtight_qloose; exact (qmeter_tight _ HQ) | apply (rroom_tick S0); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact (qmeter_room _ HQ)]]|].
  split; [apply ret_ok_even; reflexivity|]. split; [unfold w64, YG0d.w64, YG0n.w64, A_REFILL_RET; rewrite unsigned_lit_small by lia; lia|].
  split; [clear - Hal; replace (sp0 - 176) with (sp0 + (-11) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
  split; [clear - Hlo; unfold AFSTACK, RSTACK in *; lia|]. split; [lia|].
  split; [intros a Ha; apply PRES1; clear - Ha; unfold AFSTACK, RSTACK in *; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite Ei; reflexivity|]. split; [reflexivity|]. split; [exact Hcl | exact Hmiss]. }
pose proof (CLrefillR.tfib_refill_okR B TS ly S1 W regs mem md1 cl PRE) as RR.
pose proof (AFkq.refill_tree_apost (as_universe B) 1 1 1 S1 cl WfP1 Hcl ltac:(lia) (aregime_preg_tick S0 cl Hev Hcl)) as APOST.
pose proof (YFfk.amreal_apost tfibsegs _ _ W _ _ APOST RR) as RR2.
eapply amreal_mono; [|exact RR2].
intros r W' c' [(_ & RO & CI) [(regs' & mem' & md' & Ec & (AR' & _ & WLE & RP & IO & FR & PR) & A0) (regs'' & mem'' & md'' & Ec' & RAWF)]].
assert (Em : mem'' = mem').
{ rewrite Ec in Ec'. apply (f_equal (fun c => ms_mem (cfg_ms c))) in Ec'. unfold cfg_at, mkst in Ec'. cbn in Ec'. symmetry. exact Ec'. }
subst mem''.
destruct RO as (Rck & _ & _ & _ & Rqt & Rqg & _).
assert (ENO : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> 0x98000 <= a < 0x5f6000) by (unfold TFIB_ERRNO; lia).
unfold rleaf. exists ly, regs', mem', md'.
split; [exact Ec|].
split; [exact (conj Ei AR')|].
split; [exact (qtight_ext S0 (snd r) Rck Rqt Rqg (qmeter_tight _ HQ))|].
split; [exact CI|].
split; [unfold blocks_bytes; rewrite Rck; reflexivity|].
split; [apply layout_le_refl|].
split; [exact WLE|].
split; [exact RP|].
split; [exact IO|].
split.
{ intros a Ra NO NO' NS. unfold ImgBaseAG.RSTACK, AFl1.RSTACK in *.
  destruct (Z_le_gt_dec TFIB_ERRNO a) as [E1|E1]; [destruct (Z_lt_ge_dec a (TFIB_ERRNO + 4)) as [E2|E2]|].
  - (* errno: never hidden, so the raw frame gives the view *)
    pose proof (rw_not_hidden W a (ENO a (conj E1 E2))) as Hh.
    assert (Hh' : w_H W' (Z_to_bv 64 a) = false) by (destruct (w_H W' (Z_to_bv 64 a)) eqn:E; [rewrite (WLE _ E) in Hh; discriminate | reflexivity]).
    assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ra).
    change (aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
    unfold aview, mbyte, mrestrict. rewrite Hh, Hh'.
    rewrite (RAWF (Z_to_bv 64 a)); [reflexivity | rewrite Ex; exact NO | rewrite Ex; exact NO' | rewrite Ex; unfold AFl1.RSTACK; exact NS].
  - apply (FR a Ra NO NO'); [|intros []]. unfold ascratch. intros [X|X]; [unfold AFl1.RSTACK in X; exact (NS X)|]. rewrite (ts_errno B TS) in X. lia.
  - apply (FR a Ra NO NO'); [|intros []]. unfold ascratch. intros [X|X]; [unfold AFl1.RSTACK in X; exact (NS X)|]. rewrite (ts_errno B TS) in X. lia. }
split; [intros x NO NO' NS; exact (RAWF x NO NO' NS)|].
split; [exact PR|].
exact A0.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_post_miss: AR of the final state (AGj1.AR_final at the pop state Sp), Wf / qtight of the final state from
   malloc's contract at the entry state S0 along the granted path (AGif1.post_cgif).  The entry ARX is at its own
   layout ly0 (the join runs at the refill's grown layout ly); only its Wf is read. *)
Lemma post_miss_cgif : forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
ARX_cgif B inst ly0 S0 W0 mem00 md00 -> rpre_cgif S0 n -> blocks_bytes S0 + n <= LIVE_MAX ->
ARX_cgif B inst ly Sp W mem0 md0 -> n < MALLOC_MAX -> blocks_bytes Sp + n <= LIVE_MAX -> In tr (as_universe B) ->
49 <= n <= 64512 -> st_cache_inited Sp = true -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv ly (chunk_class n) (off / 16) + RZ (rz_log n) - 15) 1 jb ->
at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
  (fun z m => dpost_cgif B inst ly Sp W tr z m) odd z W
  (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> n mod 8 <> 0) ->
(exists trc, apath (malloc n tr S0) trc (ck_user (new_chunk (chunk_class n) off n), st_final Sp (chunk_class n) l off n tr z) /\
  gflag trc = true) ->
ARX_cgif B inst ly (st_final Sp (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
qtight (st_final Sp (chunk_class n) l off n tr z).
Proof.
intros inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat [_ HAR00] [Hev HQ] Hlive0 [Ei HARp]
Hmax _ Htr Nrange0 Hinited Hcache WFR Hjb Hjb_def HR Hodd [trc [HP HG]].
(* Wf and qtight of the final state, from malloc's contract at the entry state along the granted path. *)
pose proof (malloc_ok (as_universe B) S0 n tr (ts_universe B TS) (am_wf _ _ _ _ (proj1 HAR00)) Hev ltac:(lia) Hlive0 Htr) as AT.
pose proof (atok_apath_flag _ _ _ trc _ AT HP) as MPo. unfold malloc_post in MPo.
destruct MPo as (WF' & _ & _ & _ & _ & QT). pose proof (QT (qmeter_tight _ HQ)) as QT'. clear QT.
pose proof (proj1 HARp) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly Sp md0 (proj1 (proj2 HARp))) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS)).
destruct (rz_log_range n Nrange0) as [Hkz Nrange].
assert (Hn0 : 0 <= n) by lia.
pose proof (@AGis.casek_sizes n (rz_log n) Hkz Nrange) as (_ & _ & _ & _ & FP & _).
destruct (off_split B ly Sp _ n l off HARm Hn0 FP Hcache) as [_ Hoff].
pose proof (AGiy.Hcl' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff) as Hcl.
pose proof (AGiy.Hv' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff) as Hv.
pose proof (AGiy.Hcnt' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff) as Hcnt.
pose proof (AGiy.Hv2' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff) as Hv2.
pose proof (AGix.SKPRES B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) (rz_log n) Sp l off tr TS LY IMG HARm Hinited Hcache eq_refl eq_refl Hoff Hkz Nrange) as HSKpres.
destruct WFR as (Hsp & Htrlen & _ & Hbp & _).
split; [|exact QT'].
split; [exact Ei|].
exact (AGj1.AR_final W ly regs0 mem0 md0 n tr (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp Htrlen Hbp (fun z0 m => dpost_cgif B inst ly Sp W tr z0 m) HSKpres Hkz Nrange
B Sp l off TS HTSD HARm Hinited Hcache eq_refl eq_refl Hoff (fun z0 m H => H) odd z regs' mem' mat HR Hodd (conj WF' QT') HARp).
Qed.

(* if_post_miss_k: the k twin of post_miss_cgif (0 <= n <= 48): AR of the final state from AGif1k.AR_final_kw at the
   pop state Sp (AGif1k.post_cgif_k's body with Sp for the post-tick state), Wf / qtight from malloc's contract at
   the entry state S0 along the granted path. *)
Lemma post_miss_k_cgif : forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
ARX_cgif B inst ly0 S0 W0 mem00 md00 -> rpre_cgif S0 n -> blocks_bytes S0 + n <= LIVE_MAX ->
ARX_cgif B inst ly Sp W mem0 md0 -> n < MALLOC_MAX -> blocks_bytes Sp + n <= LIVE_MAX -> In tr (as_universe B) ->
0 <= n <= 48 -> st_cache_inited Sp = true -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (AGj6.Kv ly (chunk_class n) (off / 16) + AGj6.RZ - 15) 1 jb ->
at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
  (fun z m => dpost_cgif B inst ly Sp W tr z m) odd z W
  (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
(odd = true <-> AGj6.NPv n mod 8 <> 0) ->
(exists trc, apath (malloc n tr S0) trc (ck_user (new_chunk (chunk_class n) off n), st_final Sp (chunk_class n) l off n tr z) /\
  gflag trc = true) ->
ARX_cgif B inst ly (st_final Sp (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
qtight (st_final Sp (chunk_class n) l off n tr z).
Proof.
intros inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat [_ HAR00] [Hev HQ] Hlive0 [Ei HARp]
Hmax _ Htr Nrange Hinited Hcache WFR Hjb Hjb_def HR Hodd [trc [HP HG]].
(* Wf and qtight of the final state, from malloc's contract at the entry state along the granted path. *)
pose proof (malloc_ok (as_universe B) S0 n tr (ts_universe B TS) (am_wf _ _ _ _ (proj1 HAR00)) Hev ltac:(lia) Hlive0 Htr) as AT.
pose proof (atok_apath_flag _ _ _ trc _ AT HP) as MPo. unfold malloc_post in MPo.
destruct MPo as (WF' & _ & _ & _ & _ & QT). pose proof (QT (qmeter_tight _ HQ)) as QT'. clear QT.
pose proof (proj1 HARp) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly Sp md0 (proj1 (proj2 HARp))) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS)).
assert (Hn0 : 0 <= n) by lia.
pose proof (@AGj6.case0_sizes n Nrange) as (_ & _ & _ & _ & FP & _).
destruct (off_split B ly Sp _ n l off HARm Hn0 FP Hcache) as [_ Hoff].
pose proof (AGjc.Hcl' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff) as Hcl.
pose proof (AGjc.Hv' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff) as Hv.
pose proof (AGjc.Hcnt' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff) as Hcnt.
pose proof (AGjc.Hv2' B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff) as Hv2.
pose proof (AGjb.SKPRES B W ly mem0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) Sp l off tr TS LY IMG HARm Hinited Hcache eq_refl eq_refl Hoff Nrange) as HSKpres.
destruct WFR as (Hsp & Htrlen & _ & Hbp & _).
split; [|exact QT'].
split; [exact Ei|].
exact (AGif1k.AR_final_kw W ly regs0 mem0 md0 n tr (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp Htrlen Hbp (fun z0 m => dpost_cgif B inst ly Sp W tr z0 m) HSKpres Nrange
B Sp l off TS HTSD HARm Hinited Hcache eq_refl eq_refl Hoff (fun z0 m H => H) odd z regs' mem' mat HR Hodd (conj WF' QT') HARp).
Qed.

(* if_depot_miss: the depot callee at the pop state Sp is AGif1.depot_cgif there; cgif's U (In tr (as_universe B))
   does not read the state, so the entry's U is the one depot_cgif asks for, and the entry ARX is not read. *)
Lemma depot_miss_cgif : tfib_depot_spec B ->
forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
ARX_cgif B inst ly0 S0 W0 mem00 md00 -> In tr (as_universe B) ->
ARX_cgif B inst ly Sp W mem0 md0 ->
(forall x : word, DZONE ly (bv_unsigned x) \/ CZONE ly (bv_unsigned x) -> mem x = mem0 x) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
~ DZONE ly (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
dpost_cgif B inst ly Sp W tr z mem').
Proof.
intros HD1 inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr regs mem md buf _ Htr HARp.
exact (AGif1.depot_cgif B TS HD1 inst ly Sp W mem0 md0 tr regs mem md buf HARp Htr).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* if_oom: AR after Allocate's OOM tail (AFi5.AR_oom, as the released miss arm's TAILN), the OOM byte owned
   (own_area) and the thread's unwinding byte owned (own_core). *)
Lemma oom_cgif : forall inst ly S0 Sp W mem md n tr (sp0 : Z) mem' md',
ARX_cgif B inst ly Sp W mem md -> qtight Sp -> pc_chunks (cache Sp (chunk_class n)) = [] ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
   aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> bv_unsigned x <> TFIB_OOM -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) ->
   mem' x = mem x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) -> (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem' a) ->
ly_stk_lo ly + AFSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
val_mem tfibsegs (mrestrict (w_H W) mem') TFIB_OOM 1 1 -> same_io md md' -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
(exists trc, apath (malloc n tr S0) trc (PNull, Sp) /\ gflag trc = true) ->
ARX_cgif B inst ly Sp W mem' md' /\ qtight Sp /\ aowned B ly Sp TFIB_OOM /\ aowned B ly Sp (ly_T ly + t_unwinding).
Proof.
intros inst ly S0 Sp W mem md n tr sp0 mem' md' [Ei HAR] HQ _ AGV RAWV _ P1 Hlo Hhi _ _ Hvm Hlz _.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (lo_top ly LY) as (_ & _ & _ & K2 & _ & _ & K1).
assert (OOMo : aowned B ly Sp TFIB_OOM).
{ apply (own_area B ly Sp _ (as_oom_byte B, 1) TFIB_OOM HARm); [unfold asyms_areas; cbn; tauto|]. cbn [fst snd]. rewrite (ts_oom B TS). lia. }
assert (UNWo : aowned B ly Sp (ly_T ly + t_unwinding)).
{ apply (own_core B ly Sp _ (ly_T ly, kThreadObjSize) (ly_T ly + t_unwinding) HARm); [unfold core_extents; cbn; tauto|].
  cbn [fst snd]. unfold t_unwinding, kThreadObjSize. lia. }
split; [|split; [exact HQ | split; [exact OOMo | exact UNWo]]].
split; [exact Ei|].
apply (AFi5.AR_oom B ly Sp W mem mem' md md' TS HAR).
- intros a Ra Ho NX. apply AGV; [exact Ra | | intros ->; apply NX; unfold AFi5.XJ; lia | intros ER; exact (errno_not_owned_cgif ly Sp W mem md a HAR ER Ho)].
  intros ST. exact (AR_stack_law_ok tfibsegs B ly Sp W mem md a HAR ltac:(lia) Ho).
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (AV : forall m, aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
  rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  destruct (Z_le_gt_dec (sp0 - AFSTACK) a') as [G1|G1]; [destruct (Z_lt_ge_dec a' sp0) as [G2|G2]|].
  { apply apresent_aview_some. apply P1. lia. }
  all: destruct (Z.eq_dec a' TFIB_OOM) as [->|NO]; [apply aview_rw_some; unfold TFIB_OOM; lia|].
  all: destruct (Z_le_gt_dec TFIB_ERRNO a') as [G3|G3]; [destruct (Z_lt_ge_dec a' (TFIB_ERRNO + 4)) as [G4|G4]; [apply aview_rw_some; unfold TFIB_ERRNO in *; lia|]|].
  all: rewrite (AGV a' Ha' ltac:(lia) NO ltac:(lia)); exact Hv.
- exact Hvm.
- exact Hlz.
- unfold eager_used. rewrite Hvm, Hlz. reflexivity.
- intros a Ha Hx. unfold YG0n.w64.
  assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
  apply RAWV; rewrite unsigned_lit_small by exact Ra.
  + clear - Ha K1 Hlo. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, AFSTACK in *. lia.
  + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *. lia.
  + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. lia.
Qed.

(* if_stack: the stack is never owned (YG0s.AR_stack_law_ok). *)
Lemma stack_cgif : forall inst ly S W mem md a, ARX_cgif B inst ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.
Proof. intros inst ly S W mem md a [_ HAR] Ha. exact (AR_stack_law_ok tfibsegs B ly S W mem md a HAR Ha). Qed.

(* if_view_m: AGif1.view_cgif's proof (it never reads rpre). *)
Lemma view_m_cgif : forall inst ly S W mem md n l off,
ARX_cgif B inst ly S W mem md -> 0 <= n -> from_primary n = true ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
off mod 32 = 0 /\ hview B W ly inst mem (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16).
Proof.
intros inst ly S W mem md n l off [Ei HAR] Hn0 FP Hinited Hcache. subst inst.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
destruct (off_split B ly S _ n l off HARm Hn0 FP Hcache) as [A32 Hoff].
split; [exact A32|].
exact (hview_of_ARm B W ly mem n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S l off TS LY IMG HARm Hn0 FP Hinited Hcache eq_refl eq_refl Hoff).
Qed.

(* if_owned_m: AGif1.owned_cgif's proof (AGix.hit_owned; it never reads rpre). *)
Lemma owned_m_cgif : forall inst ly S W mem md n l off odd a,
ARX_cgif B inst ly S W mem md -> 49 <= n <= 64512 ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
0 <= a < 2 ^ 64 -> (odd = true -> n mod 8 <> 0) ->
hit_writes ly n (chunk_class n) (off / 16) (rz_log n) odd a -> aowned B ly S a.
Proof.
intros inst ly S W mem md n l off odd a [_ HAR] Nrange0 Hinited Hcache Ra Hodd Hw.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
destruct (rz_log_range n Nrange0) as [Hkz Nrange].
pose proof (@AGis.casek_sizes n (rz_log n) Hkz Nrange) as (_ & _ & _ & _ & FP & _).
destruct (off_split B ly S _ n l off HARm ltac:(lia) FP Hcache) as [_ Hoff].
exact (AGix.hit_owned B W ly mem n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) (rz_log n) S l off [] TS LY IMG HARm
Hinited Hcache eq_refl eq_refl Hoff Hkz Nrange odd a Ra Hodd Hw).
Qed.

(* if_owned_m_k: AGif1k.owned_cgif_k's proof (AGjb.hit_owned_k; it never reads rpre). *)
Lemma owned_m_k_cgif : forall inst ly S W mem md n l off odd a,
ARX_cgif B inst ly S W mem md -> 0 <= n <= 48 ->
st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
0 <= a < 2 ^ 64 -> (odd = true -> AGj6.NPv n mod 8 <> 0) ->
hit_writes_k ly n (chunk_class n) (off / 16) odd a -> aowned B ly S a.
Proof.
intros inst ly S W mem md n l off odd a [_ HAR] Nrange Hinited Hcache Ra Hodd Hw.
pose proof (proj1 HAR) as HARm. pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
pose proof (@AGj6.case0_sizes n Nrange) as (_ & _ & _ & _ & FP & _).
destruct (off_split B ly S _ n l off HARm ltac:(lia) FP Hcache) as [_ Hoff].
exact (AGjb.hit_owned_k B W ly mem n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) S l off [] TS LY IMG HARm
Hinited Hcache eq_refl eq_refl Hoff Nrange odd a Ra Hodd Hw).
Qed.

(* if_mono_join: st_final only adds the popped chunk (upd_chunk), keeps the sections and the fake frames, so an owned
   byte outside the new block stays owned. *)
Lemma mono_join_cgif : forall inst ly Sp W mem md n l off tr z a,
ARX_cgif B inst ly Sp W mem md -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
~ (sptr_addr B ly (ck_user (new_chunk (chunk_class n) off n)) <= a <
   sptr_addr B ly (ck_user (new_chunk (chunk_class n) off n)) + req_size n) ->
aowned B ly Sp a -> aowned B ly (st_final Sp (chunk_class n) l off n tr z) a.
Proof.
intros inst ly Sp W mem md n l off tr z a _ _ NB [Hpart NC].
assert (Pnc : exists p, ck_beg (new_chunk (chunk_class n) off n) = PPrim p) by (eexists; reflexivity).
assert (CK : st_chunks (st_final Sp (chunk_class n) l off n tr z) = upd_chunk (st_chunks Sp) (new_chunk (chunk_class n) off n)).
{ cbv [AFi3.st_final ImgBaseAG.st_final AFl0.depot_after ImgBaseAG.depot_after]. destruct (z =? 0); reflexivity. }
assert (FS : frames (st_final Sp (chunk_class n) l off n tr z) = frames Sp).
{ cbv [AFi3.st_final ImgBaseAG.st_final AFl0.depot_after ImgBaseAG.depot_after]. destruct (z =? 0); reflexivity. }
pose proof (sec_extents_upd_prim ly Sp _ _ CK Pnc) as SE.
unfold aowned. rewrite SE. split; [exact Hpart|].
intros [(k & Hk & Hst & Hr) | (cp & Hcp & Hfr)].
- rewrite CK in Hk. apply In_upd_chunk in Hk as [Hk| ->].
  + apply NC. left. exists k. split; [exact Hk|]. split; [exact Hst | exact Hr].
  + apply NB. exact Hr.
- rewrite FS in Hcp. apply NC. right. exists cp. split; [exact Hcp | exact Hfr].
Qed.
End b.

Theorem iface_cgif_m (B : asyms) : GrantSyms B -> tfib_depot_spec B ->
AIfaceM B (fun tr _ => In tr (as_universe B)) malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX LIVE_MAX qtight (dpost_cgif B)
  3 12 refill_tree.
Proof.
intros TS HD1. constructor.
- exact (mview_cgif B TS).
- exact (shape_miss_cgif B TS).
- exact (refill_cgif B TS).
- exact (post_miss_cgif B TS).
- exact (post_miss_k_cgif B TS).
- exact (depot_miss_cgif B TS HD1).
- exact (oom_cgif B TS).
- exact (stack_cgif B TS).
- exact (view_m_cgif B TS).
- exact (owned_m_cgif B TS).
- exact (owned_m_k_cgif B TS).
- exact (mono_join_cgif B TS).
Qed.
End a.
