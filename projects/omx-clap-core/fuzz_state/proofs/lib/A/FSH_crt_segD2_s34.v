(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names and addresses changed; 1881 of its 1980 lines of code are new or changed and 485 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segB2.v, with its module names changed; 283 of its 407 lines of code are new or changed and 1856 lines of the source are left out. *)
(* check_round_trip (fs.asan 0x81a9c, build A), WALK LANE D2, SEGMENT 34: from the boundary crt_INV_822ac (0x822ac,
   the return of fuzz_free (file)) over `mv a0, s2` and `jal pj_free` (0x822b0, a0 = s2 = F + 0x140 = &back) to the
   boundary crtD2_INV_35 (0x822b4, the return of pj_free (&back)).

   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd19.v .. sd24.v)
   The function-level lookup is the one quoted in the lane head (internal path)
   (checker a Theorem Labs lane, role check, CONFIRM). This file ports the CONTENT of d25a984c903's St19 step
   (check_round_trip_sd19.v: pj_free frees back's tree D19, the holdings lose D19, the document's node and its tree are
   carried across the call untouched) into S0's ajournal / ARU / U form; it builds no bridge to the donor framework.

   What the call does, in S0's terms (FSH_Fn_reader.pj_free_spec at level 0, v = F + 0x140, D = Dback):
   - it frees Dback's blocks: Permutation (ablocks ly3 S3) (rd_hblocks Dback ++ ablocks ly' S'), and each free disowns
     its block's head, U' = udrop U3 (rd_heads Dback). crtD2_udrop_perm turns that into the next boundary's head list:
     U3 is pairwise disjoint, so no head of the kept part of U3 is one of Dback's heads.
   - its footprint is the back object (v, v + 56), Dback's blocks and fs's statics. The doc object (F + 0x20), the
     document's tree Ddoc, text's and back's blocks are off it (crtD2pf_off_fp / crtD2pf_frm_off_fp, ported from a Theorem Labs lane's
     lib/A/FSH_crt_segB2.v (a working branch): crtB2_off_fp / crtB2_frm_off_fp / crtB2_fp_noshadow), so FSW_rd's
     call keeps carry rtree / pobj / fs_rblock over; the footprint is a sub-footprint of crt's (fsw_fp_sub: the object
     is crt's own frame, the freed blocks are blocks that crt allocated, the statics are image bytes), and the flag word
     at F + 504 is off it (the object ends at F + 0x178, a block is apart from every frame, a frame byte is no image).
   - g_live goes down by rd_sum Dback; rom_view is read afresh at the new boundary (the site's crt_rom).
   The budget: pj_free ticks EV_pj_free Dback; crtD2_INV_35 carries the REMAINING allowance. It comes from the entry
   boundary itself: crt_INV_822ac (FSH_crt_base.v, base v20) carries
   `k + EV_pj_free Dback + EV_pj_free Ddoc + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip` over its own
   lists, so no room premise is taken here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret
FSW_frame FSW_frame3 FSW_rd FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site
FSH_crt_segD FSH_crt_segD2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct check_round_trip_stages_b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the run (MEASURED by the engine over crt_tbl) =================
   From the store-free boundary state at 0x822ac: `mv a0, s2` and `jal pj_free` reach pj_free (A 0x83570) with
   a0 = s2 (atom 18 = &back), ra = 0x822b4, and every other register still its boundary atom. *)
Definition crtD2_sc34 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_free (crt_ss2 0x822ac)).
Lemma crtD2_run34 : sym_run_toN tfibsegs crt_tbl FUEL A_pj_free (crt_ss2 0x822ac) = (crtD2_sc34, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD2_site34 : crt_csite crtD2_sc34 A_pj_free 0x822b4 /\ sr_get (ss_regs crtD2_sc34) 10%bv = SOff 18 0.
Proof. unfold crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD2_ssave34 : crt_ssave crtD2_sc34.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

(* ================= list facts: the reader trees' block and head lists, and U after a tree's frees ================= *)
Lemma crtD2pf_hb_app : forall D1 D2, rd_hblocks (D1 ++ D2) = rd_hblocks D1 ++ rd_hblocks D2.
Proof. intros D1 D2. unfold rd_hblocks. apply map_app. Qed.
Lemma crtD2pf_rh_app : forall D1 D2, rd_heads (D1 ++ D2) = rd_heads D1 ++ rd_heads D2.
Proof. intros D1 D2. unfold rd_heads. apply map_app. Qed.
Lemma crtD2pf_filter_perm : forall (f : Z * Z -> bool) l l',
  Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
intros f l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2]; simpl.
- apply perm_nil.
- destruct (f x); [apply perm_skip; exact IH | exact IH].
- destruct (f x), (f y); simpl; first [apply perm_swap | apply Permutation_refl].
- eapply Permutation_trans; [exact IH1 | exact IH2].
Qed.
(* hd_in H h is membership of h in H (both components compared) *)
Lemma crtD2pf_hd_in_true : forall H h, In h H -> hd_in H h = true.
Proof.
intros H h Hin. unfold hd_in. apply existsb_exists. exists h. split; [exact Hin|].
cbv beta. rewrite !Z.eqb_refl. reflexivity.
Qed.
Lemma crtD2pf_hd_in_in : forall H h, hd_in H h = true -> In h H.
Proof.
intros H h E. unfold hd_in in E. apply existsb_exists in E as (g & Hg & E). cbv beta in E.
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
destruct g as [g1 g2], h as [h1 h2]. cbn [fst snd] in E1, E2. subst. exact Hg.
Qed.
(* udrop is stdpp's filter at a boolean test; it is Stdlib's List.filter at the same test *)
Lemma crtD2pf_udrop_eq : forall U H, udrop U H = List.filter (fun h => negb (hd_in H h)) U.
Proof.
intros U H. unfold udrop. induction U as [|x U IH]; [reflexivity|].
rewrite list_basics.list.filter_cons. cbn [List.filter].
destruct (hd_in H x); cbn [negb]; destruct (decide _) as [Hd|Hd]; cbv iota.
- destruct Hd.
- exact IH.
- f_equal. exact IH.
- exfalso. exact (Hd I).
Qed.
(* ---- U after the frees of a tree: U is a permutation of the kept heads A and the tree's heads Hd, and U is pairwise
   disjoint (upoison_ok), so no head of A is one of Hd's (crtD2_perm_not_in) and dropping Hd leaves A ---- *)
Lemma crtD2_udrop_perm : forall (U A Hd : list (Z * Z)),
  pairwise zdisjoint U -> Permutation U (A ++ Hd) -> Forall (fun x => 0 < snd x) Hd ->
  Permutation (udrop U Hd) A.
Proof.
intros U A Hd PW HP HF. rewrite crtD2pf_udrop_eq.
eapply Permutation_trans; [exact (crtD2pf_filter_perm _ U (A ++ Hd) HP)|].
rewrite filter_app.
assert (E2 : forall l, incl l Hd -> List.filter (fun h => negb (hd_in Hd h)) l = []).
{ intros l. induction l as [|x l IH]; intros Hi; [reflexivity|]. simpl.
  rewrite (crtD2pf_hd_in_true Hd x (Hi x (or_introl eq_refl))). simpl.
  apply IH. intros y Hy. apply Hi. right. exact Hy. }
assert (E1 : forall l, (forall x, In x l -> ~ In x Hd) -> List.filter (fun h => negb (hd_in Hd h)) l = l).
{ intros l. induction l as [|x l IH]; intros Hn; [reflexivity|]. simpl.
  destruct (hd_in Hd x) eqn:E.
  - exfalso. exact (Hn x (or_introl eq_refl) (crtD2pf_hd_in_in Hd x E)).
  - simpl. f_equal. apply IH. intros y Hy. apply Hn. right. exact Hy. }
rewrite (E2 Hd (incl_refl Hd)), app_nil_r, (E1 A); [apply Permutation_refl|].
intros x HxA HxH. rewrite Forall_forall in HF.
exact (crtD2_perm_not_in U A Hd x PW HP (HF x HxH) HxH HxA).
Qed.
(* a callee-saved register of the return env is the boundary atom the call site held (s2 .. s11 kept by the call) *)
Lemma crtD2pf_reg : forall E ssC (regsC regs' : bvmap 5 word) extra n,
  crt_ssave ssC -> (18 <= n <= 27)%nat ->
  (forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr)) ->
  aregs_preserved regsC regs' -> ew (Ereg regs' extra) n = ew E n.
Proof.
intros E ssC regsC regs' extra n HSV Hn RG HP.
rewrite (ew_Ereg_lt regs' extra n ltac:(lia)).
rewrite (HP (Z.of_nat n) ltac:(unfold acallee_saved; lia)).
rewrite RG, (HSV n Hn). apply fsw_SOff0.
Qed.

(* ================= a freeing call's footprint against crt's frame and the live blocks =================
   The footprint of a call that frees the blocks Dh is FR ++ ablocks_fp Dh ++ FS_PSTAT_FP, FR inside crt's class-3
   frame. A byte of another live block, a frame byte outside FR, and every shadow byte are off it. PORTED from a Theorem Labs lane's
   lib/A/FSH_crt_segB2.v:644-705 on a working branch (crtB2_pstat_range, crtB2_off_fp, crtB2_frm_off_fp,
   crtB2_fp_noshadow), renamed; the keeps below are its :742-814 in explicit-argument form. ---- *)
Section kp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* a block of one part of a split of the live list is not in the other part (crtD2_once) *)
Lemma crtD2pf_not_in_r : forall ly S (W : world tfibsegs) mem md K1 K2 x,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (K1 ++ K2) -> In x K1 -> ~ In x K2.
Proof.
intros ly S W mem md K1 K2 x HAR HP Hx Hx2.
apply in_split in Hx as (l1 & l2 & ->).
apply (crtD2_once B ly S W mem md l1 (l2 ++ K2) x HAR).
- eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. apply Permutation_refl.
- apply in_or_app. right. apply in_or_app. right. exact Hx2.
Qed.
Lemma crtD2pf_not_in_l : forall ly S (W : world tfibsegs) mem md K1 K2 x,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (K1 ++ K2) -> In x K2 -> ~ In x K1.
Proof.
intros ly S W mem md K1 K2 x HAR HP Hx Hx1.
apply (crtD2pf_not_in_r ly S W mem md K2 K1 x HAR); [| exact Hx | exact Hx1].
eapply Permutation_trans; [exact HP | apply Permutation_app_comm].
Qed.

Lemma crtD2pf_pstat_range : forall a, inFP FS_PSTAT_FP a -> 0x10000 <= a < FS_IMG_END.
Proof.
intros a (r & Hr & Hra). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hra; unfold FS_IMG_END; lia|]). destruct Hr.
Qed.
(* a byte of a live heap block other than those of Dh *)
Lemma crtD2pf_off_fp : forall lyc Sc (W : world tfibsegs) mem md pos FR Dh p n x,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall a, inFP FR a -> frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) Dh -> p <= x < p + req_size n ->
  ~ inFP (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) x.
Proof.
intros lyc Sc W mem md pos FR Dh p n x HAR Hin HFR HDh Hpn Hnd Hx Hf.
apply inFP_app in Hf as [Hf|Hf].
- pose proof (HFR x Hf) as Hfr.
  pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W mem md p n 3 pos HAR Hpn Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite crt_frame3 in Hd. lia.
- apply inFP_app in Hf as [Hf|Hf].
  + destruct Hf as (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm).
    cbn [fst snd] in Hra.
    assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hbm; exact (Hnd Hbm)).
    pose proof (sep_blocks tfibsegs B LAWS lyc Sc W mem md b m p n HAR (HDh _ Hbm) Hpn Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  + pose proof (fsw_ablock_off_img B lyc Sc W mem md p n HAR Hpn) as Ho.
    pose proof (crtD2pf_pstat_range x Hf) as Hs. lia.
Qed.
(* a byte of crt's frame outside FR *)
Lemma crtD2pf_frm_off_fp : forall lyc Sc (W : world tfibsegs) mem md pos FR Dh a,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512 -> ~ inFP FR a ->
  ~ inFP (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) a.
Proof.
intros lyc Sc W mem md pos FR Dh a HAR Hin HDh Ha HnFR Hf.
apply inFP_app in Hf as [Hf|Hf]; [exact (HnFR Hf)|].
apply inFP_app in Hf as [Hf|Hf].
- destruct Hf as (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm).
  cbn [fst snd] in Hra.
  pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W mem md b m 3 pos HAR (HDh _ Hbm) Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite crt_frame3 in Hd. lia.
- exact (frm_img tfibsegs B LAWS lyc Sc W mem md 3 pos a HAR Hin ltac:(rewrite crt_frame3; lia) (crt_pstat_img a Hf)).
Qed.
(* no byte of such a footprint is a shadow byte *)
Lemma crtD2pf_fp_noshadow : forall lyc Sc (W : world tfibsegs) mem md pos FR Dh a,
  AR tfibsegs B lyc Sc W mem md -> In (3, pos) (frames Sc) ->
  (forall a, inFP FR a -> frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  inFP (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros lyc Sc W mem md pos FR Dh a HAR Hin HFR HDh Hf.
apply inFP_app in Hf as [Hf|Hf].
- destruct (frames_bounds tfibsegs B LAWS lyc Sc W mem md 3 pos HAR Hin) as (_ & _ & Happ).
  pose proof (HFR a Hf) as Hr. rewrite crt_frame3 in Happ.
  pose proof (in_app_addr _ _ a Happ Hr) as AP.
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in AP |- *. lia.
- apply inFP_app in Hf as [Hf|Hf].
  + destruct Hf as (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hbm).
    cbn [fst snd] in Hra.
    exact (fsw_ablock_off_shadow B lyc Sc W mem md b m HAR (HDh _ Hbm) a Hra).
  + pose proof (crtD2pf_pstat_range a Hf) as Hs. unfold FS_IMG_END, SHADOW_OFF in *. lia.
Qed.

(* ---- what such a call keeps (FSW_rd's call keeps at this footprint) ---- *)
(* a reader block that the call does not free *)
Lemma crtD2pf_rblock_kept : forall STK1 sp1 kc pos FR Dh lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U'
    (W' : world tfibsegs) mem' md' p k,
  @ajournal rc SK tfibsegs B STK1 sp1 (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) lyc Sc W (unpoison Uc memc) mdc []
    ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (3, pos) (frames Sc) ->
  (forall a, inFP FR a -> frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  ~ In (p - HEAD, k + HEAD) Dh ->
  fs_rblock tfibsegs B lyc Sc W memc p k -> fs_rblock tfibsegs B ly' S' W' mem' p k.
Proof.
intros STK1 sp1 kc pos FR Dh lyc Sc Uc W memc mdc ly' S' U' W' mem' md' p k HJ HU HO' HP' Hin3 HFR HDh Hnd Hb.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HU) as HAR.
pose proof Hb as (Hin & _ & Hk & _).
apply (fs_rblock_kept_call B STK1 sp1 _ lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc p k HJ HU HO' HP'); [|exact Hb].
intros x Hx. apply (crtD2pf_off_fp lyc Sc W _ mdc pos FR Dh (p - HEAD) (k + HEAD) x HAR Hin3 HFR HDh Hin Hnd).
pose proof (req_size_pos (k + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr). unfold HEAD in *. lia.
Qed.
(* a tree whose node is a frame object outside FR and whose blocks are not Dh's *)
Lemma crtD2pf_rtree_kept : forall STK1 sp1 kc pos FR Dh lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U'
    (W' : world tfibsegs) mem' md' v t D,
  @ajournal rc SK tfibsegs B STK1 sp1 (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) lyc Sc W (unpoison Uc memc) mdc []
    ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (3, pos) (frames Sc) ->
  (forall a, inFP FR a -> frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  frame_addr lyc 3 pos <= v -> v + 56 <= frame_addr lyc 3 pos + 512 ->
  (forall x, v <= x < v + 56 -> ~ inFP FR x) -> (forall bk, In bk (rd_hblocks D) -> ~ In bk Dh) ->
  pobj tfibsegs B lyc Sc W memc v -> rtree tfibsegs B lyc Sc W memc v t D -> rtree tfibsegs B ly' S' W' mem' v t D.
Proof.
intros STK1 sp1 kc pos FR Dh lyc Sc Uc W memc mdc ly' S' U' W' mem' md' v t D HJ HU HO' HP' Hin3 HFR HDh
  Hv0 Hv1 HvFR HDD HPv HT.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HU) as HAR.
apply (rtree_kept_call B STK1 sp1 _ lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc v t D HJ HU HO' HP');
  [| | exact HPv | exact HT].
- intros x Hx. apply (crtD2pf_frm_off_fp lyc Sc W _ mdc pos FR Dh x HAR Hin3 HDh); [lia | exact (HvFR x Hx)].
- intros a k x Hak Hx. pose proof HT as (_ & HBk & _). destruct (HBk a k Hak) as (Hin & _ & Hk & _).
  apply (crtD2pf_off_fp lyc Sc W _ mdc pos FR Dh (a - HEAD) (k + HEAD) x HAR Hin3 HFR HDh Hin).
  + apply HDD. unfold rd_hblocks. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hak].
  + pose proof (req_size_pos (k + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr). unfold HEAD in *. lia.
Qed.
(* a frame object outside FR stays a placed object *)
Lemma crtD2pf_pobj_kept : forall STK1 sp1 kc pos FR Dh lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U'
    (W' : world tfibsegs) mem' md' v,
  @ajournal rc SK tfibsegs B STK1 sp1 (FR ++ ablocks_fp Dh ++ FS_PSTAT_FP) lyc Sc W (unpoison Uc memc) mdc []
    ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (3, pos) (frames Sc) ->
  (forall a, inFP FR a -> frame_addr lyc 3 pos <= a < frame_addr lyc 3 pos + 512) ->
  (forall bk, In bk Dh -> In bk (ablocks B lyc Sc)) ->
  frame_addr lyc 3 pos <= v -> v + 56 <= frame_addr lyc 3 pos + 512 ->
  (forall x, v <= x < v + 56 -> ~ inFP FR x) -> FSupoisonU.fs_heads B ly' S' U' ->
  pobj tfibsegs B lyc Sc W memc v -> pobj tfibsegs B ly' S' W' mem' v.
Proof.
intros STK1 sp1 kc pos FR Dh lyc Sc Uc W memc mdc ly' S' U' W' mem' md' v HJ HU HO' HP' Hin3 HFR HDh
  Hv0 Hv1 HvFR HH HPv.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HU) as HAR.
apply (pobj_kept_call B STK1 sp1 _ lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc v HJ HU HO' HP');
  [| | exact HH | exact HPv].
- intros x Hx. apply (crtD2pf_frm_off_fp lyc Sc W _ mdc pos FR Dh x HAR Hin3 HDh); [lia | exact (HvFR x Hx)].
- intros a Ha. exact (crtD2pf_fp_noshadow lyc Sc W _ mdc pos FR Dh a HAR Hin3 HFR HDh Ha).
Qed.
End kp.

(* ================= segment 34 ================= *)
Section s34. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJ_FREE : @pj_free_spec fx rc SK tfibsegs B 0.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* the call's own part: from crt_INV_822ac at the call, pj_free (&back) into crtD2_INV_35 *)
Lemma crtD2_hcall34 :
  crt_hcall SK B crtD2_sc34 A_pj_free 0x822b4 (STK_pj_free 2) (crt_INV_822ac B) (crtD2_INV_35 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJ HARU Hfr HSB RG HPRE HFRL HTOP.
destruct crtD2_site34 as ((_ & _ & _ & _ & G2 & _ & _ & _ & _ & _) & G10).
pose proof crtD2_ssave34 as HSV.
pose proof HE as (E2 & _).
destruct HINV as (E18 & E20 & E21 & E26 & _ & (same & nsame & back & Dback & Ddoc & tback & live & peak & cnt &
  E24 & E25 & HPB & HPU & HFH & HTX & HBK & HRT & HRN & Hdep & HPO1 & HPO2 & HG & HL & _ & HC & Hk & HR1)).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
pose proof HARU as (_ & (_ & PWU) & _).
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJ HARU Hfr) as (_ & HF4096 & HFceil & _ & _ & _).
pose proof (crtD2_F_at SK B cx ly3 S3 W3 (unpoison U3 memC) mdC k HJ) as EFa.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (@alloc_ceiling_value rc) as (HCr & _).
(* the registers at the call *)
assert (Esp : spZ regsC = crt_sp1 cx) by (unfold spZ; rewrite RG, G2, fsw_SOff0; exact E2).
assert (R10 : YK11.getr regsC 10%bv = w64 (crt_F cx + 0x140)) by (rewrite RG, G10, fsw_SOff0; exact E18).
(* the boundary's data facts, from the boundary memory to the call's (same below alloc_ceiling) *)
assert (KIMG : forall a, in_img tfibsegs a -> aview tfibsegs (w_H W3) memC a = aview tfibsegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. pose proof (crt_img_range a Ha). apply (aview_below (w_H W3) (ms_mem ms3) memC alloc_ceiling a HSB). lia. }
pose proof (crt_glob_keep W3 (ms_mem ms3) memC live peak cnt SIZE_MAXZ KIMG HG) as HG'.
pose proof (rnode_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (Ddoc ++ Dback) (crt_F cx + 0x140) tback Dback HAR HSB
  ltac:(lia) ltac:(lia) HRN) as HRN'.
pose proof (rnode_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC Ddoc (crt_F cx + 0x20) _ Ddoc HAR HSB
  ltac:(lia) ltac:(lia) HRT) as HRT'.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HAR HSB HPO1) as HPO1'.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HAR HSB HPO2) as HPO2'.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ _ HAR HSB HTX) as HTX'.
pose proof (fs_rblock_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ _ HAR HSB HBK) as HBK'.
(* the live list at the call: crt's entry blocks, the four kept blocks and Ddoc's (K), then Dback's *)
assert (HPK : Permutation (ablocks B ly3 S3)
  ((ablocks B (c_ly cx) (c_S cx) ++ crtD2_L4 cx same nsame back ++ rd_hblocks Ddoc) ++ rd_hblocks Dback)).
{ eapply Permutation_trans; [exact HPB|]. rewrite crtD2pf_hb_app, <- !app_assoc. apply Permutation_refl. }
assert (HPK2 : Permutation (ablocks B ly3 S3)
  (ablocks B (c_ly cx) (c_S cx) ++ (crtD2_L4 cx same nsame back ++ rd_hblocks Ddoc ++ rd_hblocks Dback))).
{ eapply Permutation_trans; [exact HPK|]. rewrite <- !app_assoc. apply Permutation_refl. }
assert (HDh : forall bk, In bk (rd_hblocks Dback) -> In bk (ablocks B ly3 S3)).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPK)). apply in_or_app. right. exact Hbk. }
assert (HKin : forall bk,
  In bk (ablocks B (c_ly cx) (c_S cx) ++ crtD2_L4 cx same nsame back ++ rd_hblocks Ddoc) -> ~ In bk (rd_hblocks Dback)).
{ intros bk Hbk. exact (crtD2pf_not_in_r B ly3 S3 W3 _ mdC _ _ bk HAR HPK Hbk). }
(* U at the call: the kept heads, then Dback's *)
assert (HPU2 : Permutation U3
  ((c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD)] ++ rd_heads Ddoc) ++ rd_heads Dback)).
{ eapply Permutation_trans; [exact HPU|]. rewrite crtD2pf_rh_app, <- !app_assoc. apply Permutation_refl. }
assert (HF16 : Forall (fun x => 0 < snd x) (rd_heads Dback)).
{ apply Forall_forall. intros x Hx. unfold rd_heads in Hx. apply in_map_iff in Hx as (b & <- & _). cbn [snd].
  unfold HEAD. lia. }
pose proof (crtD2_udrop_perm U3 _ (rd_heads Dback) PWU HPU2 HF16) as HUD.
(* pj_free's premises: back's tree is freeable at depth 2 over its own blocks *)
destruct HRN' as (HN & HBk & HI).
assert (HN2 : PjStruct.pj_node tfibsegs (mrestrict (w_H W3) memC) (fun a n => In (a, n) Dback) (crt_F cx + 0x140)
  tback Dback).
{ apply (PjStruct.pj_node_frame tfibsegs tback _ _ _ _ _ Dback HN); [intros a n Han; exact Han | intros x _; reflexivity]. }
pose proof (PjStruct.pj_fd_mono tfibsegs _ _ (PjTree.depth tback) 2 _ Dback Hdep
  (PjStruct.pj_node_fd tfibsegs tback _ _ _ Dback HN2)) as HFD.
destruct (crt_rbo_app B ly3 S3 W3 memC Ddoc Dback HBk) as (HBdoc & HBback).
assert (HINC : incl (rd_heads Dback) U3).
{ intros h Hh. apply (Permutation_in _ (Permutation_sym HPU2)). apply in_or_app. right. exact Hh. }
assert (HSUM : rd_sum Dback <= live).
{ pose proof (crt_live0 B cx HB). pose proof (crt_rd_sum_pos B ly3 S3 W3 memC Ddoc HBdoc).
  pose proof HTX as (_ & _ & Ht & _). pose proof HBK as (_ & _ & Hb & _).
  rewrite crt_rd_sum_app in HL. lia. }
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNEV & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & HNJ & _).
assert (HEVd : 0 <= EV_pj_free Ddoc) by (unfold EV_pj_free, EV_fuzz_free; lia).
assert (HNEVD : st_nev S3 + EV_pj_free Dback <= EV_MAX) by (unfold CRT_EV_WRAP, EV_fuzz_free in HR1; lia).
pose proof (crtD2_window SK B cx ly3 S3 U3 W3 memC mdC k regsC 0x140 (STK_pj_free 2) HB HJ HARU Hfr Esp
  ltac:(lia) ltac:(lia) crtD2_stk_pj_free) as HWIN.
assert (HV : crt_F cx + 0x140 = 0 /\ Dback = [] \/
  crt_F cx + 0x140 <> 0 /\
  PjStruct.pj_fd tfibsegs (mrestrict (w_H W3) memC) (fun a n => In (a, n) Dback) (2 - 0) (crt_F cx + 0x140) Dback /\
  pobj tfibsegs B ly3 S3 W3 memC (crt_F cx + 0x140) /\
  (crt_F cx + 0x140 + 56 <= spZ regsC - STK_pj_free (2 - 0) \/ spZ regsC <= crt_F cx + 0x140)).
{ right. split; [lia|]. split; [exact HFD|]. split; [exact HPO1'|]. left. exact HWIN. }
(* the call *)
pose proof (PJ_FREE ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (crt_F cx + 0x140) Dback live peak cnt SIZE_MAXZ
  ltac:(lia) HPRE HFH R10 HV HBback HINC HG' HSUM HNEVD) as HSRr.
exists ((crt_F cx + 0x140, crt_F cx + 0x140 + 56) :: ablocks_fp (rd_hblocks Dback) ++ FS_PSTAT_FP), (EV_pj_free Dback).
eexists. split; [exact HSRr|].
(* the footprint is crt's: the object is crt's own frame, the freed blocks crt's temporaries, the statics image *)
split.
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
  - right. right. right. left. exists 3, (c_pos cx). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFa, crt_frame3. lia.
  - apply inFP_app in Ha as [Ha | Ha].
    + right. left. destruct Ha as (r & Hr & Hra). unfold ablocks_fp in Hr.
      apply in_map_iff in Hr as ([b n] & <- & Hbn). cbn [fst snd] in Hra.
      exists b, n. split; [exact (HDh _ Hbn)|]. split; [|lia].
      apply (crtD2pf_not_in_l B ly3 S3 W3 _ mdC _ _ (b, n) HAR HPK2).
      apply in_or_app. right. apply in_or_app. right. exact Hbn.
    + right. right. left. split; [exact Ha | exact (crt_pstat_img a Ha)]. }
(* the flag word is off the footprint *)
split.
{ intros a Ha Hf. rewrite crt_frame3 in Ha. apply inFP_cons in Hf as [Hf | Hf]; [lia|].
  apply (crtD2pf_frm_off_fp B ly3 S3 W3 _ mdC (c_pos cx) [] (rd_hblocks Dback) a HAR Hin3 HDh);
    [rewrite EFa; lia | exact (inFP_nil a) | exact Hf]. }
(* the next boundary *)
intros W' c' HPc. destruct HPc as (ly' & S' & regs' & mem' & md' & Hc' & HJc & OK' & PO' & HPR & HQ).
destruct HQ as (HPerm & _ & HG2).
exists ly', S', (udrop U3 (rd_heads Dback)), regs', mem', md'.
split; [exact Hc'|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HPR|].
intros HJ' HARU'.
assert (ER : forall n, (18 <= n <= 27)%nat -> ew (Ereg regs' (crt_extra cx)) n = ew E n)
  by (intros n Hn; exact (crtD2pf_reg E crtD2_sc34 regsC regs' (crt_extra cx) n HSV Hn RG HPR)).
(* the heads after the call: each one's block is still live (it is no head of Dback) *)
assert (HFH' : FSupoisonU.fs_heads B ly' S' (udrop U3 (rd_heads Dback))).
{ intros r Hr. rewrite crtD2pf_udrop_eq in Hr. apply filter_In in Hr as (HrU & Hnd). cbv beta in Hnd.
  destruct (HFH r HrU) as (E16 & m & Hm & Hm16). split; [exact E16|]. exists m. split; [|exact Hm16].
  apply (Permutation_in _ HPerm) in Hm. apply in_app_or in Hm as [Hm | Hm]; [exfalso | exact Hm].
  unfold rd_hblocks in Hm. apply in_map_iff in Hm as ([a kk] & Ea & Hak). cbn [fst snd] in Ea.
  assert (Hr' : In r (rd_heads Dback)).
  { destruct r as [r1 r2]. cbn [fst snd] in E16, Ea. subst r2. injection Ea as Ea1 Ea2.
    unfold rd_heads. apply in_map_iff. exists (a, kk). cbn [fst snd]. rewrite Ea1. split; [reflexivity | exact Hak]. }
  rewrite (crtD2pf_hd_in_true _ _ Hr') in Hnd. cbn in Hnd. discriminate. }
(* the footprint's object part and what lies off it *)
assert (HFR : forall a, inFP [(crt_F cx + 0x140, crt_F cx + 0x140 + 56)] a ->
  frame_addr ly3 3 (c_pos cx) <= a < frame_addr ly3 3 (c_pos cx) + 512).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [rewrite EFa; lia | destruct (inFP_nil a Ha)]. }
assert (HvFR : forall x, crt_F cx + 0x20 <= x < crt_F cx + 0x20 + 56 ->
  ~ inFP [(crt_F cx + 0x140, crt_F cx + 0x140 + 56)] x).
{ intros x Hx Hf. apply inFP_cons in Hf as [Hf | Hf]; [lia | exact (inFP_nil x Hf)]. }
assert (Hv0 : frame_addr ly3 3 (c_pos cx) <= crt_F cx + 0x20) by (rewrite EFa; lia).
assert (Hv1 : crt_F cx + 0x20 + 56 <= frame_addr ly3 3 (c_pos cx) + 512) by (rewrite EFa; lia).
assert (HDD : forall bk, In bk (rd_hblocks Ddoc) -> ~ In bk (rd_hblocks Dback)).
{ intros bk Hbk. apply HKin. apply in_or_app. right. apply in_or_app. right. exact Hbk. }
assert (HKt : ~ In (c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD) (rd_hblocks Dback)).
{ apply HKin. apply in_or_app. right. apply in_or_app. left. unfold crtD2_L4. cbv zeta. cbn [In]. left. reflexivity. }
assert (HKb : ~ In (back - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) (rd_hblocks Dback)).
{ apply HKin. apply in_or_app. right. apply in_or_app. left. unfold crtD2_L4. cbv zeta. cbn [In].
  right. right. right. left. reflexivity. }
unfold crtD2_INV_35. cbv zeta.
change (ms_mem (mkst regs' (Z_to_bv 64 0x822b4) mem' (seg_rom tfibsegs))) with mem'.
split; [rewrite (ER 20%nat ltac:(lia)); exact E20|].
split; [rewrite (ER 21%nat ltac:(lia)); exact E21|].
split; [rewrite (ER 26%nat ltac:(lia)); exact E26|].
exists same, nsame, back, Ddoc, (live - rd_sum Dback), peak, cnt.
split; [rewrite (ER 24%nat ltac:(lia)); exact E24|].
split; [rewrite (ER 25%nat ltac:(lia)); exact E25|].
(* the blocks: Dback's are gone *)
split.
{ unfold crtD2_blocks. apply (Permutation_app_inv_l (rd_hblocks Dback)).
  eapply Permutation_trans; [apply Permutation_sym; exact HPerm|].
  eapply Permutation_trans; [exact HPK | apply Permutation_app_comm]. }
split; [exact HUD|].
split; [exact HFH'|].
split.
{ exact (crtD2pf_rblock_kept SK B (STK_pj_free 2) (spZ regsC) (EV_pj_free Dback) (c_pos cx)
    [(crt_F cx + 0x140, crt_F cx + 0x140 + 56)] (rd_hblocks Dback) ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _ _
    HJc HARU OK' PO' Hin3 HFR HDh HKt HTX'). }
split.
{ exact (crtD2pf_rblock_kept SK B (STK_pj_free 2) (spZ regsC) (EV_pj_free Dback) (c_pos cx)
    [(crt_F cx + 0x140, crt_F cx + 0x140 + 56)] (rd_hblocks Dback) ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _ _
    HJc HARU OK' PO' Hin3 HFR HDh HKb HBK'). }
split.
{ exact (crtD2pf_rtree_kept SK B (STK_pj_free 2) (spZ regsC) (EV_pj_free Dback) (c_pos cx)
    [(crt_F cx + 0x140, crt_F cx + 0x140 + 56)] (rd_hblocks Dback) ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md'
    (crt_F cx + 0x20) _ Ddoc HJc HARU OK' PO' Hin3 HFR HDh Hv0 Hv1 HvFR HDD HPO2' HRT'). }
split.
{ exact (crtD2pf_pobj_kept SK B (STK_pj_free 2) (spZ regsC) (EV_pj_free Dback) (c_pos cx)
    [(crt_F cx + 0x140, crt_F cx + 0x140 + 56)] (rd_hblocks Dback) ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md'
    (crt_F cx + 0x20) HJc HARU OK' PO' Hin3 HFR HDh Hv0 Hv1 HvFR HFH' HPO2'). }
split; [exact HG2|].
split; [exact (crt_rom SK B IMG cx (k + EV_pj_free Dback) ly' S' _ W' mem' md' HB HJ' HARU')|].
split; [rewrite crt_rd_sum_app in HL; lia|].
split; [exact HC|].
unfold CRT_EV_WRAP, EV_fuzz_free in HR1 |- *. lia.
Qed.

Lemma crtD2_seg34 : crt_from SK B crt_ss35 (crtD2_INV_35 B) -> crt_from SK B crt_ss34 (crt_INV_822ac B).
Proof.
intros NEXT.
destruct crtD2_site34 as (HCS & _).
exact (crt_seg_call SK B 0x822ac A_pj_free 0x822b4 crtD2_sc34 (crt_INV_822ac B) (crtD2_INV_35 B) (STK_pj_free 2)
  crtD2_run34 HCS ltac:(lia) eq_refl (proj1 crtD2_stk_pos) crtD2_stk_pj_free crtD2_hcall34 NEXT).
Qed.
End s34.
