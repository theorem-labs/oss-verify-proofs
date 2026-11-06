(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1540 of its 1601 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_string.v; 2571 of its 2712 lines of code are new or changed and 1460 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_free.v, with its addresses changed; 800 of its 941 lines of code are new or changed and 2571 lines of the source are left out. *)
(* pj_free 0x83570 (pf.c:334-350) on fs.asan (sha256 64b53ff86172...), the TAIL SEGMENT 0x83654 .. 0x836a0: the three
   exit calls fuzz_free (kids) 0x83668, fuzz_free (keys) 0x83680, fuzz_free (str) 0x8369c, each with its inline ASan
   shadow check decided UNTAKEN by the kit's token run, ending at 0x836a0 where lib/A/FSW_pj_free.v's pjf_end_memset
   closes the goal.  0x83654 is reached from the loop exit (bltu 0x83650) and from the entry when n = 0 (beqz 0x835d8).
   rule 24: the function's released plain proof exists (lib/Prog/pj_free.v @ c8557374ad2e); no released ASan-image proof
   of any fs function exists (ossv proof index v5; a Theorem Labs lane's (internal path)).
   The Section shape, pjf_inv / pjf_regs / pjf_reseat / pjf_end_memset and the data lemmas belong to
   lib/A/FSW_pj_free.v and lib/A/FSW_pj_free_dat.v (the pj_free walk lane); this file adds the tail segment only, and
   re-declares Sections W and N with the same variables, hypotheses and Lets so that its GOAL is the same term. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_reader
FSW_K FSW_ret FSW_rd FSW_pj FSW_K3 FSW_pj_free_tbl FSW_pj_free_dat FSW_pj_free.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= image facts: fuzz/alloc.c's statics are no read-only bytes ================= *)
(* a concrete byte range that no non-writable segment covers and that misses the relro window is no read-only byte *)
Lemma pjt_roP_out : forall lo hi,
  forallb (fun s => (seg_writable s || (hi <=? Z.of_N (seg_base s)) ||
                     (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? lo))%bool) tfibsegs = true ->
  ((hi <=? FS_RLO) || (FS_RHI <=? lo))%bool = true ->
  forall a, lo <= a < hi -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros lo hi Hsegs Hrel a Ha [(s & Hs & Hw & Hr) | Hr].
- rewrite forallb_forall in Hsegs. pose proof (Hsegs s Hs) as E. rewrite Hw in E. cbn [orb] in E.
  apply orb_true_iff in E as [E|E]; apply Z.leb_le in E; lia.
- apply orb_true_iff in Hrel as [E|E]; apply Z.leb_le in E; lia.
Qed.
Lemma pjt_pstat_notro : forall a, inFP FS_PSTAT_FP a -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha;
  [ exact (pjt_roP_out 0xa3ca0 0xa3ca8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) a Ha)
  | exact (pjt_roP_out 0x5da5c0 0x5da5c8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) a Ha)
  | exact (pjt_roP_out 0x5da5e0 0x5da5e8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) a Ha)
  | exact (pjt_roP_out 0x5da600 0x5da608 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) a Ha)].
Qed.
(* the statics lie far below the shadow *)
Lemma pjt_pstat_low : forall a, inFP FS_PSTAT_FP a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; unfold SHADOW_OFF; lia.
Qed.
Lemma pjt_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn [fst]; lia. Qed.
(* the GOT word of the shadow base and the shadow-base cell are image bytes, and a byte window of an object that holds
   no image byte is apart from them (FSW_pj_free.v's pjf_got_img / pjf_cell_img / pjf_disj_img are discharged over its
   Section N, so this file states its own, Section-free) *)
Lemma pjt_got_img : forall y, tfib_D_GOT_asan_shadow_memory_dynamic_address <= y <
  tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 -> in_img tfibsegs y.
Proof.
intros y Hy. exact (pjf_img_cover tfib_D_GOT_asan_shadow_memory_dynamic_address
  (tfib_D_GOT_asan_shadow_memory_dynamic_address + 8) ltac:(vm_compute; reflexivity) y Hy).
Qed.
Lemma pjt_cell_img : forall y, tfib_D_asan_shadow_memory_dynamic_address <= y <
  tfib_D_asan_shadow_memory_dynamic_address + 8 -> in_img tfibsegs y.
Proof.
intros y Hy. exact (pjf_img_cover tfib_D_asan_shadow_memory_dynamic_address
  (tfib_D_asan_shadow_memory_dynamic_address + 8) ltac:(vm_compute; reflexivity) y Hy).
Qed.
Lemma pjt_disj_img : forall v0 lo hi c len, 0 <= lo -> lo < hi -> hi <= 56 -> 0 < len ->
  (forall x, v0 <= x < v0 + 56 -> ~ in_img tfibsegs x) -> (forall y, c <= y < c + len -> in_img tfibsegs y) ->
  v0 + hi <= c \/ c + len <= v0 + lo.
Proof.
intros v0 lo hi c len H0 H1 H2 H3 Hv Hc.
destruct (Z_le_gt_dec (v0 + hi) c) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (c + len) (v0 + lo)) as [R|R]; [right; exact R|].
exfalso. apply (Hv (Z.max c (v0 + lo))); [lia|]. apply Hc. lia.
Qed.

(* ================= list algebra the tail needs on top of FSW_pj_free_dat.v ================= *)
Lemma pjt_rd_sum_nonneg : forall (A : list (Z * Z)), (forall a k, In (a, k) A -> 0 <= k) -> 0 <= rd_sum A.
Proof.
induction A as [|[a k] A IH]; intros H.
- cbn. lia.
- rewrite pjf_rd_sum_cons. cbn [snd].
  assert (Hk : 0 <= k) by (apply (H a k); left; reflexivity).
  assert (HA : 0 <= rd_sum A) by (apply IH; intros a0 k0 Hin; apply (H a0 k0); right; exact Hin).
  lia.
Qed.
Lemma pjt_inFP_nil : forall a, ~ inFP ([] : list (Z * Z)) a.
Proof. intros a (r & Hr & _). exact Hr. Qed.
Lemma pjt_rd_sum_one : forall a kb, rd_sum [(a, kb)] = kb.
Proof. intros a kb. rewrite pjf_rd_sum_cons. cbn [snd rd_sum fold_right]. lia. Qed.
Lemma pjt_nodup_app_disj : forall {X} (l1 l2 : list X) x,
  List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x HN H1 H2; [destruct H1|].
cbn [app] in HN. apply NoDup_cons_iff in HN as [Hy HN'].
destruct H1 as [<-|H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH l2 x HN' H1 H2)].
Qed.
(* two (start, requested size) pairs of blocks of size >= 2 differ when the blocks do *)
Lemma pjt_rq_ne : forall b m q n : Z, 2 <= n -> ~ (b = q /\ m = n) -> (b, req_size m) <> (q, req_size n).
Proof.
intros b m q n Hn HNE E. injection E as E1 E2. apply HNE. split; [exact E1|].
unfold req_size in E2. destruct (Z.eqb_spec m 0) as [->|Hm]; destruct (Z.eqb_spec n 0) as [->|Hn0]; lia.
Qed.

Section Q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* AR_blocks_law's pairwise zdisjoint, pointwise *)
Lemma pjt_blocks_disj : forall ly S (W : world tfibsegs) mx md p1 n1 p2 n2 x,
  AR tfibsegs B ly S W mx md -> In (p1, n1) (ablocks B ly S) -> In (p2, n2) (ablocks B ly S) ->
  (p1, req_size n1) <> (p2, req_size n2) ->
  ~ (p1 <= x < p1 + req_size n1 /\ p2 <= x < p2 + req_size n2).
Proof.
intros ly S W mx md p1 n1 p2 n2 x HAR H1 H2 HNE [Hx1 Hx2].
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks tfibsegs B LAWS ly S W mx md p1 n1 HAR H1) as (_ & _ & _ & _ & _ & PW & _).
assert (I1 : In (p1, req_size n1) (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (change (p1, req_size n1) with ((fun b : Z * Z => (fst b, req_size (snd b))) (p1, n1));
      apply in_map; exact H1).
assert (I2 : In (p2, req_size n2) (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (change (p2, req_size n2) with ((fun b : Z * Z => (fst b, req_size (snd b))) (p2, n2));
      apply in_map; exact H2).
destruct (FSupoisonU.pairwise_In2 zdisjoint _ _ _ PW I1 I2 HNE) as [Hd|Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.
(* AR_sep_law: a live block and a live fake frame never share a byte *)
Lemma pjt_block_frame_disj : forall ly S (W : world tfibsegs) mx md p n cid pos x,
  AR tfibsegs B ly S W mx md -> In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  ~ (p <= x < p + req_size n /\ frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid).
Proof.
intros ly S W mx md p n cid pos x HAR Hb Hf [Hx1 Hx2].
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_sep tfibsegs B LAWS ly S W mx md HAR) as (PS & _).
destruct (YG0s.pairwise_app_inv zdisjoint _ _ PS) as (_ & _ & PX).
pose proof (PX (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid)
  ltac:(change (p, req_size n) with ((fun b : Z * Z => (fst b, req_size (snd b))) (p, n));
        apply in_map; exact Hb)
  ltac:(change (frame_addr ly cid pos, fs_frame_bytes cid)
          with ((fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (cid, pos));
        apply in_map; exact Hf)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* an 8-byte window of application bytes is an in_app range *)
Lemma pjt_in_app8 : forall a, app_addr a -> app_addr (a + 7) -> in_app a 8.
Proof.
intros a (H0 & Ha) (H1 & Hb). pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
End Q.

(* ================= the tail's one new resumed state: 0x83654 ================= *)
(* s3 = v + 24 (atom 19) is the shadow-checked word; 24(s0) is the same cell (an alias); kids is atom 45 *)
Definition ss_T0 : sstate := pjss 0x83654 [fld 19 0 45] [(19%nat, mkAF 4096 PJF_CEIL 3)] [(SOff 8 24, SOff 19 0)].
Definition SH_T0 : list shent := [mkSHE 19 0 8].
(* a register after a token run: the run's env is the start env, extended (ewset) only at fresh atoms past every atom
   the state names (YCbn extK), so a register the state holds as an atom reads that atom of the start env *)
Ltac pjt_rd HS r :=
  rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ r HS);
  lazymatch type of HS with st_ok _ _ ?sC _ =>
    let e := eval vm_compute in (sr_get (ss_regs sC) r) in
    change (sr_get (ss_regs sC) r) with e end;
  rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis fs_fuzz_free_spec : @fuzz_free_spec fx rc SK tfibsegs B.
Hypothesis fs_memset_realizesU : aintrin_realizesU tfibsegs B OSet PC_memset.
Section N.
Variable k : nat.
Variables (ly : alayout) (S0 : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (v : Z) (D : list (Z * Z)) (live peak cnt fail : Z).
Hypothesis Hk : (k <= 2)%nat.
Hypothesis HPRE : fpreU tfibsegs B (STK_pj_free (2 - k)) ly S0 U W regs mem md ch.
Hypothesis HHD0 : FSupoisonU.fs_heads B ly S0 U.
Hypothesis H10 : YK11.getr regs 10 = w64 v.
Hypothesis HV : v <> 0.
Hypothesis HPO : pobj tfibsegs B ly S0 W mem v.
Hypothesis HVS : v + 56 <= spZ regs - STK_pj_free (2 - k) \/ spZ regs <= v.
Hypothesis HBK : rd_blocks_ok tfibsegs B ly S0 W mem D.
Hypothesis HUI : incl (rd_heads D) U.
Hypothesis HG : fs_glob tfibsegs W mem live peak cnt fail.
Hypothesis HSUM : rd_sum D <= live.
Hypothesis HEV : st_nev S0 + EV_pj_free D <= EV_MAX.
Variables (ty num str kids keys n cap : Z) (ks : bool) (Ds Dk Dy Di : list (Z * Z)).
Hypothesis HND : NoDup D.
Hypothesis HAP : PjStruct.pj_apart D v.
Hypothesis HHDR : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) v ty num str kids keys n cap.
Hypothesis HSTR : str = 0 /\ Ds = [] \/ exists k0, In (str, k0) D /\ Ds = [(str, k0)].
Hypothesis HKIDS : kids = 0 /\ n = 0 /\ Dk = [] \/ exists k0, In (kids, k0) D /\ 56 * n <= k0 /\ Dk = [(kids, k0)].
Hypothesis HKEYS : keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k0, In (keys, k0) D /\ 8 * n <= k0 /\ Dy = [(keys, k0)].
Hypothesis HPERM : Permutation D (Ds ++ Dk ++ Dy ++ Di).
Hypothesis HITEMS : PjStruct.pf_items tfibsegs (mrestrict (w_H W) mem) (fun a n0 => In (a, n0) D)
  (pjf_Pd tfibsegs (mrestrict (w_H W) mem) (fun a n0 => In (a, n0) D) (2 - k)) ks kids keys (Z.to_nat n) Di.

Let STK : Z := STK_pj_free (2 - k).
Let sp0 : Z := spZ regs.
Let FP : list (Z * Z) := (v, v + 56) :: ablocks_fp (rd_hblocks D) ++ FS_PSTAT_FP.
Let m0 : word -> option byte := mrestrict (w_H W) mem.
Let Qf : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' _ mem' _ =>
    Permutation (ablocks B ly S0) (rd_hblocks D ++ ablocks B ly' S') /\
    (v <> 0 -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W') mem') v /\ pobj tfibsegs B ly' S' W' mem' v) /\
    fs_glob tfibsegs W' mem' (live - rd_sum D) peak cnt fail.
Let GOAL : world tfibsegs -> config -> Prop :=
  fpostU tfibsegs B STK sp0 FP regs ly S0 U W mem md (EV_pj_free D) (udrop U (rd_heads D)) Qf.

(* the tail reads only v's 56 bytes of the entry memory *)
Let Fv : Z -> Prop := fun x => v <= x < v + 56.
Let TINV (Dfr Rem : list (Z * Z)) lyc Sc Uc (Wc : world tfibsegs) memc mdc : Prop :=
  pjf_inv B k ly S0 U W regs mem md v D live peak cnt fail Fv Dfr Rem lyc Sc Uc Wc memc mdc.
(* lib/A/FSW_pj_free.v's lemmas, discharged over its Sections, at this Section's variables and hypotheses *)
Let ENTRY := pjf_entry_facts B k ly S0 U W regs mem md ch v HPRE HPO.
Let STKF := pjf_STK k regs Hk.
Let FRMREG := pjf_frm_of_region B k ly S0 U W regs mem md v D live peak cnt fail Hk HVS str kids keys n ks Ds Dk Dy
  HSTR HKIDS HKEYS.

(* ---- D is a function of the block address (the entry blocks are pairwise disjoint) ---- *)
Lemma pjt_D_fun : forall a k1 k2, In (a, k1) D -> In (a, k2) D -> k1 = k2.
Proof.
intros a k1 k2 H1 H2.
pose proof (proj1 (proj1 HPRE)) as HAPf. destruct HAPf as (HARe & _).
destruct (HBK a k1 H1) as (Hin1 & _ & Hn1 & _).
destruct (HBK a k2 H2) as (Hin2 & _ & Hn2 & _).
destruct (Z.eq_dec k1 k2) as [E|NE]; [exact E|exfalso].
apply (pjt_blocks_disj B ly S0 W (unpoison U mem) md (a - HEAD) (k1 + HEAD) (a - HEAD) (k2 + HEAD) (a - HEAD)
  HARe Hin1 Hin2 (pjt_rq_ne (a - HEAD) (k1 + HEAD) (a - HEAD) (k2 + HEAD) ltac:(cbv [HEAD]; lia)
    ltac:(intros (_ & Eq); apply NE; cbv [HEAD] in Eq; lia))).
assert (R1 : req_size (k1 + HEAD) = k1 + HEAD) by (unfold req_size; destruct (Z.eqb_spec (k1 + HEAD) 0); cbv [HEAD] in *; lia).
assert (R2 : req_size (k2 + HEAD) = k2 + HEAD) by (unfold req_size; destruct (Z.eqb_spec (k2 + HEAD) 0); cbv [HEAD] in *; lia).
rewrite R1, R2. cbv [HEAD]. lia.
Qed.
(* no block already freed shares its head with a block still to free *)
Lemma pjt_head_fresh : forall Dfr Rem p kk, Permutation D (Dfr ++ Rem) -> In (p, kk) Rem ->
  hd_in (rd_heads Dfr) (p - HEAD, HEAD) = false.
Proof.
intros Dfr Rem p kk HP Hin.
destruct (hd_in (rd_heads Dfr) (p - HEAD, HEAD)) eqn:E; [exfalso|reflexivity].
apply pjf_hd_in_iff in E. unfold rd_heads in E. apply in_map_iff in E as (b & Eb & Hb).
destruct b as (q, m). cbn [fst] in Eb. injection Eb as Eb1.
assert (Hqp : q = p) by lia. subst q.
assert (HinD1 : In (p, m) D) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hb).
assert (HinD2 : In (p, kk) D) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
pose proof (pjt_D_fun p m kk HinD1 HinD2) as Em. subst m.
assert (HNDl : List.NoDup D) by (apply NoDup_ListNoDup; exact HND).
exact (pjt_nodup_app_disj Dfr Rem (p, kk) (Permutation_NoDup HP HNDl) Hb Hin).
Qed.

(* ---- the resumed states' disjointness goal, with no extra region and with one field region ---- *)
Lemma pjt_pd0 : forall E, bv_unsigned (ew E 2) = sp0 - 96 ->
  pairwise_disjoint E (fsT_ret_regions 96 pjf_cs []).
Proof.
intros E E2.
pose proof ENTRY as (_ & Hceil & _).
pose proof STKF as (HSTK1 & _).
pose proof asan_consts as (C1 & _).
apply pairwise_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold STK, sp0 in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Lemma pjt_pd1 : forall E nn b o lo, bv_unsigned (ew E 2) = sp0 - 96 -> bv_unsigned (ew E nn) = b -> b + o = v + lo ->
  0 <= lo -> lo + 8 <= 56 ->
  (forall x, v <= x < v + 56 -> ~ in_img tfibsegs x) ->
  pairwise_disjoint E (fsT_ret_regions 96 pjf_cs [fld nn o 45]).
Proof.
intros E nn b o lo E2 En Ebo Hlo Hhi HNI.
pose proof ENTRY as (_ & Hceil & _ & Hv0 & Hv1 & _).
pose proof STKF as (HSTK1 & _).
pose proof asan_consts as (C1 & _).
pose proof (pjt_disj_img v lo (lo + 8) tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) HNI pjt_got_img) as HdG.
pose proof (pjt_disj_img v lo (lo + 8) tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) HNI pjt_cell_img) as HdC.
apply pairwise_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, fld, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, En.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold STK, sp0 in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ================= one fuzz_free call: the journal, the data and the registers across it ================= *)
Lemma pjt_cross : forall (FP1 : list (Z * Z)) (kc : Z) (Dfr UL : list (Z * Z))
    lyc Sc Uc (Wc : world tfibsegs) regsC memC mdc ly' S' U' (Wr : world tfibsegs) regs' mem' md',
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memC) mdc (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memC mdc ->
  pjf_frm regs Wc memC ->
  rd_blocks_ok tfibsegs B lyc Sc Wc memC UL ->
  pobj tfibsegs B lyc Sc Wc memC v ->
  (forall x : word, v <= bv_unsigned x < v + 56 -> mrestrict (w_H Wc) memC x = m0 x) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memC) ->
  pjf_regs regs v regsC ->
  ajournal tfibsegs B STK_fuzz_free (spZ regsC) FP1 lyc Sc Wc (unpoison Uc memC) mdc []
    ly' S' Wr (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs Wr mem' U' ->
  aregs_preserved regsC regs' ->
  FSupoisonU.fs_heads B ly' S' U' ->
  fsw_fp_sub B ly S0 lyc Sc [] FP FP1 ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  (forall a kb x, In (a, kb) UL -> a - HEAD <= x < a + kb -> ~ inFP FP1 x) ->
  (forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP1 a) ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] ly' S' Wr (unpoison U' mem') md'
    (EV_pj_free Dfr + kc) /\
  ARU tfibsegs B ly' S' U' Wr mem' md' /\
  pjf_frm regs Wr mem' /\
  rd_blocks_ok tfibsegs B ly' S' Wr mem' UL /\
  pobj tfibsegs B ly' S' Wr mem' v /\
  (forall x : word, v <= bv_unsigned x < v + 56 -> mrestrict (w_H Wr) mem' x = m0 x) /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wr) mem') /\
  pjf_regs regs v regs'.
Proof.
intros FP1 kc Dfr UL lyc Sc Uc Wc regsC memC mdc ly' S' U' Wr regs' mem' md'
  HJ HARU Hfrm HBKc Hpo HKEEP HRO HR HJc OK' PO' HP HH' HFsub HFv HFul HFsh HFcl HFro.
pose proof STKF as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof HSS as [Hgot Hcell].
pose proof HR as (Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21).
assert (Hsp' : spZ regs' = sp0 - 96)
  by (unfold spZ in *; rewrite (fsw_pres regsC regs' 2%bv HP ltac:(pjf_cs_reg)); exact Hsp).
assert (E2' : bv_unsigned (ew (pjf_env regs regs' []) 2) = spZ regs - 96)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); unfold spZ in Hsp'; unfold sp0 in Hsp'; exact Hsp').
assert (He' : forall j, (j < 12)%nat ->
  sv_denot (pjf_env regs regs' []) (SOff (33 + j) 0) = nth j (pjf_saved regs) (Z_to_bv 64 0))
  by (intros j Hj; exact (pjf_ew_sav k regs Hk regs' [] (33 + j) j eq_refl Hj)).
destruct (fsw_after_callFPU_args B STK sp0 FP [] ly S0 U Wc mem md W lyc Sc Uc memC mdc (EV_pj_free Dfr)
   STK_fuzz_free FP1 96 regsC ly' S' U' Wr regs' mem' md' kc (pjf_saved regs ++ []) pjf_cs [] [] 0
   Hgot Hcell HJ HARU HJc HFsub OK' PO' HP Hsp ltac:(lia)
   ltac:(vm_compute; intros Hc; discriminate Hc) ltac:(unfold STK in *; lia) ltac:(reflexivity)
   ltac:(vm_compute; reflexivity) ltac:(unfold pjf_cs; repeat constructor; cbn; lia)
   ltac:(exact (pjf_cs_ok k regs Hk (pjf_env regs regs' []) (mrestrict (w_H Wc) memC) E2' He' Hfrm))
   (Forall_nil _) ltac:(apply pjt_pd0; exact E2') I) as (HJ2 & HARU2 & HS2).
(* the frame's twelve saved words, read back from the resumed state's frame region *)
assert (Hfrm2 : pjf_frm regs Wr mem').
{ intros j Hj.
  pose proof (fsw_region_nth _ _ _ 0 _ HS2 ltac:(reflexivity)) as HR0. cbn [ms_mem restrict] in HR0.
  exact (FRMREG (pjf_env regs regs' []) (mrestrict (w_H Wr) mem') HR0 E2' He' j Hj). }
assert (HBK2 : rd_blocks_ok tfibsegs B ly' S' Wr mem' UL)
  by exact (rd_blocks_ok_kept_call B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdc ly' S' U' Wr mem' md' kc UL
       HJc HARU OK' PO' HFul HBKc).
assert (Hpo2 : pobj tfibsegs B ly' S' Wr mem' v)
  by exact (pobj_kept_call B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdc ly' S' U' Wr mem' md' kc v
       HJc HARU OK' PO' HFv HFsh HH' Hpo).
assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wr) mem'))
  by exact (arodata_kept B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdc ly' S' U' Wr mem' md' kc
       HJc HARU OK' PO' HFcl HFro HRO).
assert (KB : forall a, v <= a < v + 56 ->
  mrestrict (w_H Wr) mem' (Z_to_bv 64 a) = mrestrict (w_H Wc) memC (Z_to_bv 64 a)).
{ intros a Ha.
  refine (proj2 (fsw_journal_kept_byte B STK_fuzz_free (spZ regsC) FP1 lyc Sc Uc Wc memC mdc ly' S' U' Wr mem' md' kc
    a HJc HARU OK' PO' _ (HFv a Ha))).
  destruct Hpo as [[((cid & pos & Hin & _ & _ & Hf1 & Hf2) & _)|((bb & nn & Hin & Hb1 & Hb2) & _)] _].
  - right. exists cid, pos. split; [exact Hin | lia].
  - left. exists bb, nn. split; [exact Hin | cbv [HEAD] in Hb1; lia]. }
assert (HKEEP2 : forall x : word, v <= bv_unsigned x < v + 56 -> mrestrict (w_H Wr) mem' x = m0 x).
{ intros x Hx. pose proof (KB (bv_unsigned x) Hx) as E. rewrite Z_to_bv_bv_unsigned in E.
  rewrite E. exact (HKEEP x Hx). }
assert (HR2 : pjf_regs regs v regs').
{ unfold pjf_regs. split; [unfold sp0 in Hsp'; exact Hsp'|].
  split; [rewrite (fsw_pres regsC regs' 3%bv HP ltac:(pjf_cs_reg)); exact H3|].
  split; [rewrite (fsw_pres regsC regs' 4%bv HP ltac:(pjf_cs_reg)); exact H4|].
  split; [rewrite (fsw_pres regsC regs' 27%bv HP ltac:(pjf_cs_reg)); exact H27|].
  split; [rewrite (fsw_pres regsC regs' 8%bv HP ltac:(pjf_cs_reg)); exact H8|].
  split; [rewrite (fsw_pres regsC regs' 9%bv HP ltac:(pjf_cs_reg)); exact H9|].
  split; [rewrite (fsw_pres regsC regs' 18%bv HP ltac:(pjf_cs_reg)); exact H18|].
  split; [rewrite (fsw_pres regsC regs' 19%bv HP ltac:(pjf_cs_reg)); exact H19|].
  split; [rewrite (fsw_pres regsC regs' 20%bv HP ltac:(pjf_cs_reg)); exact H20|].
  rewrite (fsw_pres regsC regs' 21%bv HP ltac:(pjf_cs_reg)); exact H21. }
split; [exact HJ2|]. split; [exact HARU2|]. split; [exact Hfrm2|]. split; [exact HBK2|].
split; [exact Hpo2|]. split; [exact HKEEP2|]. split; [exact HRO2 | exact HR2].
Qed.

(* ================= one exit call of fuzz_free, entry to resume ================= *)
Lemma pjt_call : forall (Dfr Dx Rem' : list (Z * Z)) (p pcr : Z)
    lyc Sc Uc (Wc : world tfibsegs) regsC memC mdc,
  ((Dx = [] /\ p = 0) \/ (exists kk, Dx = [(p, kk)])) ->
  TINV Dfr (Dx ++ Rem') lyc Sc Uc Wc memC mdc ->
  pjf_regs regs v regsC ->
  YK11.getr regsC 1 = Z_to_bv 64 pcr ->
  YK11.getr regsC 10 = w64 p ->
  4096 <= pcr -> pcr < 2 ^ 64 -> pcr mod 2 = 0 ->
  (forall lyr Sr Ur (Wr : world tfibsegs) regsr memr mdr,
     TINV (Dfr ++ Dx) Rem' lyr Sr Ur Wr memr mdr -> pjf_regs regs v regsr ->
     SRr tfibsegs Wr (mkCfg (YK11.mkst regsr (Z_to_bv 64 pcr) memr (YK11.seg_rom tfibsegs)) mdr) GOAL) ->
  SRr tfibsegs Wc (cfg_at tfibsegs A_fuzz_free regsC memC mdc) GOAL.
Proof.
intros Dfr Dx Rem' p pcr lyc Sc Uc Wc regsC memC mdc HDx HINV HR R1 R10 Hpc0 Hpc1 Hpc2 HK.
pose proof ENTRY as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & _ & _).
pose proof STKF as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HR as (Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21).
pose proof (proj1 (proj1 HPRE)) as HAPf.
destruct HAPf as (HARe & _ & _ & Hgpe & Htpe & _).
unfold TINV, pjf_inv in HINV.
destruct HINV as (HJ & HARU & HH & Hfrm & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
assert (HPREc : fpreU tfibsegs B STK_fuzz_free lyc Sc Uc Wc regsC memC mdc []).
{ apply (fsw_fpreU_atFP B STK sp0 FP ly S0 Uc W (unpoison U mem) md [] lyc Sc Wc memC mdc (EV_pj_free Dfr)
    regsC STK_fuzz_free (-96) [] HJ HARU HRO).
  - unfold sp0 in *; lia.
  - reflexivity.
  - lia.
  - vm_compute; intros Hc; discriminate Hc.
  - unfold STK in *; lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. exact Hpc2.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite H3. exact Hgpe.
  - rewrite H4. exact Htpe.
  - apply achain_low. unfold s0Z. rewrite H8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HBKr : rd_blocks_ok tfibsegs B lyc Sc Wc memC Rem')
  by (intros a kb Hin; apply HBKc; apply in_or_app; right; exact Hin).
destruct HDx as [(-> & ->) | (kk & ->)].
- (* the field is NULL: fuzz_free returns at once, no event, no block leaves *)
  cbn [app] in HPD, HBKc.
  eapply SRr_bind.
  { apply (fs_fuzz_free_spec lyc Sc Uc Wc regsC memC mdc [] 0 0 (live - rd_sum Dfr) peak cnt fail);
      [ exact R10 | exact Hglob | exact HH
      | left; split; [reflexivity | exact HPREc]
      | intros Hc; exfalso; exact (Hc eq_refl) ]. }
  intros Wr cr Hwle [(_ & Hpost) | (Hne & _)]; [|exfalso; exact (Hne eq_refl)].
  unfold apost_baseU, fpostU in Hpost.
  destruct Hpost as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP' & Eab & HH2 & HG2).
  subst cr. rewrite R1.
  destruct (pjt_cross [] 0 Dfr Rem' lyc Sc Uc Wc regsC memC mdc ly' S' Uc Wr regs' mem' md'
      HJ HARU Hfrm HBKr Hpo HKEEP HRO HR HJc OK' PO' HP' HH2
      ltac:(intros a Ha; destruct (pjt_inFP_nil a Ha))
      ltac:(intros a _ Ha; exact (pjt_inFP_nil a Ha))
      ltac:(intros a kb x _ _ Hf; exact (pjt_inFP_nil x Hf))
      ltac:(intros a Ha; destruct (pjt_inFP_nil a Ha))
      sink_closed_nil
      ltac:(intros a _ Hf; exact (pjt_inFP_nil a Hf)))
    as (HJ2 & HARU2 & Hfrm2 & HBK2 & Hpo2 & HKEEP2 & HRO2 & HR2).
  apply (HK ly' S' Uc Wr regs' mem' md'); [|exact HR2].
  unfold TINV, pjf_inv. rewrite app_nil_r.
  replace (EV_pj_free Dfr + 0) with (EV_pj_free Dfr) in HJ2 by lia.
  split; [exact HJ2|]. split; [exact HARU2|]. split; [exact HH2|]. split; [exact Hfrm2|].
  split; [rewrite Eab; exact HBP|]. split; [exact HUc|]. split; [exact HG2|].
  split; [exact HPD|]. split; [exact HBK2|]. split; [exact Hpo2|].
  split; [exact HKEEP2 | exact HRO2].
- (* the field is a live block: one event, the block and its head leave *)
  assert (HinRem : In (p, kk) ([(p, kk)] ++ Rem')) by (left; reflexivity).
  pose proof (HBKc p kk HinRem) as HRB.
  pose proof HRB as (Hinb & Hp16 & Hkk & Hvm).
  destruct (fsw_rblock_low B lyc Sc Wc (unpoison Uc memC) mdc memC p kk (proj1 HARU) HRB) as (Hp0 & Hp1).
  assert (Hpne : p <> 0) by (cbv [HEAD] in Hp0; lia).
  assert (HinD : In (p, kk) D)
    by (apply (Permutation_in _ (Permutation_sym HPD)); apply in_or_app; right; exact HinRem).
  assert (HinU : In (p - HEAD, HEAD) U).
  { apply HUI. unfold rd_heads.
    change (p - HEAD, HEAD) with ((fun b : Z * Z => (fst b - HEAD, HEAD)) (p, kk)). apply in_map. exact HinD. }
  assert (HinUc : In (p - HEAD, HEAD) Uc).
  { rewrite HUc, pjf_udrop_eq. apply filter_In. split; [exact HinU|].
    rewrite (pjt_head_fresh Dfr ([(p, kk)] ++ Rem') p kk HPD HinRem). reflexivity. }
  destruct (in_split _ _ HinUc) as (U1 & U2 & EUc).
  assert (Hlive : kk <= live - rd_sum Dfr).
  { pose proof (pjf_rd_sum_perm D (Dfr ++ ([(p, kk)] ++ Rem')) HPD) as ES.
    rewrite !pjf_rd_sum_app, pjt_rd_sum_one in ES.
    assert (HR' : 0 <= rd_sum Rem')
      by (apply pjt_rd_sum_nonneg; intros a0 k0 Hin0;
          destruct (HBKr a0 k0 Hin0) as (_ & _ & Hk0 & _); lia).
    lia. }
  assert (HEVc : st_nev Sc + 1 <= EV_MAX).
  { pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
    pose proof (pjf_EV_perm D (Dfr ++ ([(p, kk)] ++ Rem')) HPD) as EE.
    rewrite !pjf_EV_app in EE.
    assert (E1 : EV_pj_free [(p, kk)] = 1) by (unfold EV_pj_free, EV_fuzz_free; cbn [length]; lia).
    assert (E2 : 0 <= EV_pj_free Rem') by (unfold EV_pj_free, EV_fuzz_free; lia).
    lia. }
  eapply SRr_bind.
  { apply (fs_fuzz_free_spec lyc Sc Uc Wc regsC memC mdc [] p kk (live - rd_sum Dfr) peak cnt fail);
      [ exact R10 | exact Hglob | exact HH
      | right; split; [exact Hpne|]; exists U1, U2;
        split; [exact EUc|]; split; [exact HPREc|]; split; [exact HRB | exact Hlive]
      | intros _; exact HEVc ]. }
  intros Wr cr Hwle [(Hc0 & _) | (_ & U1' & U2' & EUc' & Hpost)]; [exfalso; exact (Hpne Hc0)|].
  unfold apost_baseU, fpostU in Hpost.
  destruct Hpost as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP' &
    (l1 & l2 & Eab1 & Eab2) & HH2 & HG2).
  subst cr. rewrite R1.
  (* the freed block's footprint avoids v, the surviving blocks, the shadow and the read-only image *)
  destruct (pjf_place B lyc Sc Wc (unpoison Uc memC) mdc memC v (proj1 HARU) Hpo) as (HPL & HAMR & HHULL).
  assert (HFPb : forall a, inFP (ablocks_fp [(p - HEAD, kk + HEAD)]) a <->
    p - HEAD <= a < p - HEAD + req_size (kk + HEAD)).
  { intros a. rewrite pjf_inFP_ablocks. split.
    - intros (q & m & [E|[]] & Hr). injection E as E1 E2. rewrite <- E1, <- E2 in Hr. exact Hr.
    - intros Hr. exists (p - HEAD), (kk + HEAD). split; [left; reflexivity | exact Hr]. }
  assert (Hrq : req_size (kk + HEAD) = kk + HEAD)
    by (unfold req_size; destruct (Z.eqb_spec (kk + HEAD) 0); cbv [HEAD] in *; lia).
  assert (HFv : forall a, v <= a < v + 56 -> ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) a).
  { intros a Ha Hf. apply pjf_inFP_app in Hf as [Hf|Hf].
    - exact (proj1 (proj2 (proj2 (HPL a Ha))) (pjf_pstat_img a Hf)).
    - apply HFPb in Hf.
      destruct Hpo as [[((cid & pos & Hinf & _ & _ & Hf1 & Hf2) & _)|((bb & nn & Hinbb & Hb1 & Hb2) & _)] _].
      + apply (pjt_block_frame_disj B lyc Sc Wc (unpoison Uc memC) mdc (p - HEAD) (kk + HEAD) cid pos a
          (proj1 HARU) Hinb Hinf). split; [exact Hf | lia].
      + destruct (Z.eq_dec bb (p - HEAD)) as [Eb|Nb].
        * destruct (Z.eq_dec nn (kk + HEAD)) as [En|Nn].
          -- apply (HAP (p, kk) v HinD); [unfold PjStruct.pj_holds; cbn [fst snd]; cbv [HEAD] in *; lia | lia].
          -- apply (pjt_blocks_disj B lyc Sc Wc (unpoison Uc memC) mdc bb nn (p - HEAD) (kk + HEAD) a
               (proj1 HARU) Hinbb Hinb
               (pjt_rq_ne bb nn (p - HEAD) (kk + HEAD) ltac:(cbv [HEAD] in *; lia)
                  ltac:(intros (_ & Hc); exact (Nn Hc)))).
             cbv [HEAD] in *. split; [lia | lia].
        * apply (pjt_blocks_disj B lyc Sc Wc (unpoison Uc memC) mdc bb nn (p - HEAD) (kk + HEAD) a
            (proj1 HARU) Hinbb Hinb
            (pjt_rq_ne bb nn (p - HEAD) (kk + HEAD) ltac:(cbv [HEAD] in *; lia)
               ltac:(intros (Hc & _); exact (Nb Hc)))).
          cbv [HEAD] in *. split; [lia | lia]. }
  assert (HFul : forall a kb x, In (a, kb) Rem' -> a - HEAD <= x < a + kb ->
    ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) x).
  { intros a kb x Hin Hx Hf.
    pose proof (HBKr a kb Hin) as HRBa. pose proof HRBa as (Hina & _ & Hka & _).
    assert (Hrqa : req_size (kb + HEAD) = kb + HEAD)
      by (unfold req_size; destruct (Z.eqb_spec (kb + HEAD) 0); cbv [HEAD] in *; lia).
    apply pjf_inFP_app in Hf as [Hf|Hf].
    - refine (proj2 (al_client_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memC) mdc x (proj1 HARU) _)
        (pjf_pstat_img x Hf)).
      left. exists (a - HEAD), (kb + HEAD). split; [exact Hina | cbv [HEAD] in *; lia].
    - apply HFPb in Hf.
      assert (HNE : ~ (a - HEAD = p - HEAD /\ kb + HEAD = kk + HEAD)).
      { intros (E1 & E2).
        assert (Ea : a = p) by lia. assert (Ek : kb = kk) by lia. subst a kb.
        assert (HNDl : List.NoDup D) by (apply NoDup_ListNoDup; exact HND).
        assert (HNDr : List.NoDup (Dfr ++ ([(p, kk)] ++ Rem')))
          by exact (Permutation_NoDup HPD HNDl).
        rewrite app_assoc in HNDr.
        exact (pjt_nodup_app_disj (Dfr ++ [(p, kk)]) Rem' (p, kk) HNDr
          ltac:(apply in_or_app; right; left; reflexivity) Hin). }
      apply (pjt_blocks_disj B lyc Sc Wc (unpoison Uc memC) mdc (a - HEAD) (kb + HEAD) (p - HEAD) (kk + HEAD) x
        (proj1 HARU) Hina Hinb
        (pjt_rq_ne (a - HEAD) (kb + HEAD) (p - HEAD) (kk + HEAD) ltac:(cbv [HEAD] in *; lia) HNE)).
      cbv [HEAD] in *. split; [lia | lia]. }
  assert (HFsh : forall a, inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) a ->
    ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
  { intros a Hf. apply pjf_inFP_app in Hf as [Hf|Hf]; [exact (pjt_pstat_low a Hf)|].
    apply HFPb in Hf.
    destruct (al_blocks tfibsegs B LAWS lyc Sc Wc (unpoison Uc memC) mdc (p - HEAD) (kk + HEAD)
      (proj1 HARU) Hinb) as (_ & _ & _ & Happ & _).
    pose proof (in_app_addr _ _ a Happ ltac:(lia)) as Haa.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
  assert (HFcl : ~ YI16.sink_open_fp (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)])).
  { apply sink_closed_app; [exact pjt_pstat_closed|].
    apply sink_closed_ablocks_fp. repeat constructor. cbn [fst]. cbv [HEAD] in *. lia. }
  assert (HFro : forall a, in_roP tfibsegs FS_RLO FS_RHI a ->
    ~ inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) a).
  { intros a Hro Hf. apply pjf_inFP_app in Hf as [Hf|Hf]; [exact (pjt_pstat_notro a Hf Hro)|].
    apply HFPb in Hf.
    refine (proj2 (al_client_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memC) mdc a (proj1 HARU) _)
      (fsw_roP_img a Hro)).
    left. exists (p - HEAD), (kk + HEAD). split; [exact Hinb | lia]. }
  assert (HFsub : fsw_fp_sub B ly S0 lyc Sc [] FP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)])).
  { intros a Hf. apply pjf_inFP_app in Hf as [Hf|Hf].
    - right. right. left. split; [|exact (pjf_pstat_img a Hf)].
      unfold FP. apply pjf_inFP_cons. right. apply pjf_inFP_app. right. exact Hf.
    - apply HFPb in Hf. left. split.
      + unfold FP. apply pjf_inFP_cons. right. apply pjf_inFP_app. left.
        apply pjf_inFP_hblocks. exists p, kk. split; [exact HinD | exact Hf].
      + exists (p - HEAD), (kk + HEAD). split; [exact Hinb | exact Hf]. }
  destruct (pjt_cross (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, kk + HEAD)]) 1 Dfr Rem'
      lyc Sc Uc Wc regsC memC mdc ly' S' (U1' ++ U2') Wr regs' mem' md'
      HJ HARU Hfrm HBKr Hpo HKEEP HRO HR HJc OK' PO' HP' HH2 HFsub HFv HFul HFsh HFcl HFro)
    as (HJ2 & HARU2 & Hfrm2 & HBK2 & Hpo2 & HKEEP2 & HRO2 & HR2).
  apply (HK ly' S' (U1' ++ U2') Wr regs' mem' md'); [|exact HR2].
  unfold TINV, pjf_inv.
  assert (EEV : EV_pj_free (Dfr ++ [(p, kk)]) = EV_pj_free Dfr + 1)
    by (rewrite pjf_EV_app; unfold EV_pj_free, EV_fuzz_free; cbn [length]; lia).
  assert (EHB : rd_hblocks (Dfr ++ [(p, kk)]) = rd_hblocks Dfr ++ [(p - HEAD, kk + HEAD)])
    by (rewrite pjf_rd_hblocks_app; cbn [rd_hblocks map fst snd]; reflexivity).
  assert (EHD : rd_heads (Dfr ++ [(p, kk)]) = rd_heads Dfr ++ [(p - HEAD, HEAD)])
    by (rewrite pjf_rd_heads_app; cbn [rd_heads map fst snd]; reflexivity).
  assert (ESM : rd_sum (Dfr ++ [(p, kk)]) = rd_sum Dfr + kk)
    by (rewrite pjf_rd_sum_app, pjt_rd_sum_one; reflexivity).
  rewrite EEV. split; [exact HJ2|]. split; [exact HARU2|]. split; [exact HH2|]. split; [exact Hfrm2|].
  split.
  { rewrite EHB, Eab2. apply pjf_perm_free1. rewrite <- Eab1. exact HBP. }
  split.
  { rewrite EHD, <- pjf_udrop_app, <- HUc, EUc'.
    symmetry. apply pjf_udrop_one.
    exact (pjf_head_once B lyc Sc U1' (p - HEAD, HEAD) U2' ltac:(rewrite <- EUc'; exact (proj1 (proj2 HARU)))
      ltac:(cbn [snd]; cbv [HEAD]; lia)). }
  split; [rewrite ESM; replace (live - (rd_sum Dfr + kk)) with (live - rd_sum Dfr - kk) by lia; exact HG2|].
  split; [rewrite <- app_assoc; exact HPD|].
  split; [exact HBK2|]. split; [exact Hpo2|]. split; [exact HKEEP2 | exact HRO2].
Qed.

(* ================= the three segments ================= *)
Lemma pjt_inv_perm : forall Dfr Rem Rem2 lyc Sc Uc (Wc : world tfibsegs) memc mdc,
  Permutation Rem Rem2 -> TINV Dfr Rem lyc Sc Uc Wc memc mdc -> TINV Dfr Rem2 lyc Sc Uc Wc memc mdc.
Proof.
intros Dfr Rem Rem2 lyc Sc Uc Wc memc mdc HPm HINV.
unfold TINV, pjf_inv in HINV |- *.
destruct HINV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & HPD & HBKc & I10 & I11 & I12).
split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
split; [exact I6|]. split; [exact I7|].
split; [exact (Permutation_trans HPD (Permutation_app_head Dfr HPm))|].
split; [intros a kb Hin; apply HBKc; exact (Permutation_in _ (Permutation_sym HPm) Hin)|].
split; [exact I10|]. split; [exact I11 | exact I12].
Qed.
(* a run that writes only the frame keeps every invariant fact; the journal, ARU and the frame come back from the run *)
Lemma pjt_inv_below : forall Dfr Rem lyc Sc Uc (Wc : world tfibsegs) memc memR mdc mdR,
  TINV Dfr Rem lyc Sc Uc Wc memc mdc ->
  ajournal tfibsegs B STK sp0 FP ly S0 W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memR) mdR (EV_pj_free Dfr) ->
  ARU tfibsegs B lyc Sc Uc Wc memR mdR ->
  pjf_frm regs Wc memR ->
  same_below memc memR alloc_ceiling ->
  TINV Dfr Rem lyc Sc Uc Wc memR mdR.
Proof.
intros Dfr Rem lyc Sc Uc Wc memc memR mdc mdR HINV HJ' HARU' Hfrm' SB.
pose proof ENTRY as (_ & _ & _ & _ & Hv1 & _).
unfold TINV, pjf_inv in HINV |- *.
destruct HINV as (_ & _ & HH & _ & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
split; [exact HJ'|]. split; [exact HARU'|]. split; [exact HH|]. split; [exact Hfrm'|].
split; [exact HBP|]. split; [exact HUc|].
split; [exact (fs_glob_below Wc memc memR _ peak cnt fail SB Hglob)|].
split; [exact HPD|].
split; [exact (rd_blocks_ok_below B lyc Sc Wc (unpoison Uc memR) mdR memc memR Rem (proj1 HARU') SB HBKc)|].
split; [exact (pobj_below B lyc Sc Wc (unpoison Uc memR) mdR memc memR v (proj1 HARU') SB Hpo)|].
split.
- intros x Hx. rewrite (fsw_mrestrict_below (w_H Wc) memc memR x SB); [exact (HKEEP x Hx)|].
  unfold Fv in Hx. lia.
- exact (arodata_below B Wc memc memR SB HRO).
Qed.
(* the registers of pjf_regs, each kept *)
Lemma pjt_regs_of : forall regsc regsm, pjf_regs regs v regsc ->
  YK11.getr regsm 2 = YK11.getr regsc 2 -> YK11.getr regsm 3 = YK11.getr regsc 3 ->
  YK11.getr regsm 4 = YK11.getr regsc 4 -> YK11.getr regsm 27 = YK11.getr regsc 27 ->
  YK11.getr regsm 8 = YK11.getr regsc 8 -> YK11.getr regsm 9 = YK11.getr regsc 9 ->
  YK11.getr regsm 18 = YK11.getr regsc 18 -> YK11.getr regsm 19 = YK11.getr regsc 19 ->
  YK11.getr regsm 20 = YK11.getr regsc 20 -> YK11.getr regsm 21 = YK11.getr regsc 21 ->
  pjf_regs regs v regsm.
Proof.
intros regsc regsm (Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21) E2 E3 E4 E27 E8 E9 E18 E19 E20 E21.
unfold pjf_regs. unfold spZ in *. rewrite E2, E3, E4, E27, E8, E9, E18, E19, E20, E21.
split; [exact Hsp|]. split; [exact H3|]. split; [exact H4|]. split; [exact H27|]. split; [exact H8|].
split; [exact H9|]. split; [exact H18|]. split; [exact H19|]. split; [exact H20 | exact H21].
Qed.
(* the frame's presence, from the journal *)
Lemma pjt_pres : forall Dfr Rem lyc Sc Uc (Wc : world tfibsegs) memc mdc,
  TINV Dfr Rem lyc Sc Uc Wc memc mdc -> forall a, sp0 - 96 <= a < sp0 -> apresent (w_H Wc) memc a.
Proof.
intros Dfr Rem lyc Sc Uc Wc memc mdc HINV a Ha.
pose proof ENTRY as (_ & Hceil & H47 & _).
pose proof STKF as (HSTK1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TINV, pjf_inv in HINV. destruct HINV as (HJ & HARU & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold sp0, STK in *; lia|].
apply Hpres0. unfold STK in *. lia.
Qed.
(* the header of v, read at the current memory *)
Lemma pjt_hdr : forall Dfr Rem lyc Sc Uc (Wc : world tfibsegs) memc mdc,
  TINV Dfr Rem lyc Sc Uc Wc memc mdc ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H Wc) memc) v ty num str kids keys n cap.
Proof.
intros Dfr Rem lyc Sc Uc Wc memc mdc HINV.
unfold TINV, pjf_inv in HINV. destruct HINV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HKEEP & _).
apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W) mem)); [exact HHDR|].
intros x Hx. exact (HKEEP x Hx).
Qed.

(* ---- 0x83684 .. fuzz_free (str) 0x8369c, back at 0x836a0, then pjf_end_memset ---- *)
Lemma pjt_seg_str : forall Dfr lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  TINV Dfr Ds lyc Sc Uc Wc memc mdc -> pjf_regs regs v regsc ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x83684) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros Dfr lyc Sc Uc Wc regsc memc mdc HINV HR.
pose proof ENTRY as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & _ & _).
pose proof STKF as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21).
pose proof (pjt_pres _ _ _ _ _ _ _ _ HINV) as Hpres.
pose proof (pjt_hdr _ _ _ _ _ _ _ _ HINV) as (_ & _ & _ & Hstr & _ & _ & _ & _).
pose proof HINV as HINV0.
unfold TINV, pjf_inv in HINV.
destruct HINV as (HJ & HARU & HH & Hfrm & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v (proj1 HARU) Hpo) as (HPL & _ & _).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct Hpo as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
set (xs := [w64 str]).
assert (E2m : bv_unsigned (ew (pjf_env regs regsc xs) 2) = sp0 - 96)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E2 : bv_unsigned (ew (pjf_env regs regsc xs) 2) = sp0 + (-96)) by (rewrite E2m; lia).
assert (E8 : bv_unsigned (ew (pjf_env regs regsc xs) 8) = v)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl), H8; unfold w64; apply wz; lia).
assert (E45 : ew (pjf_env regs regsc xs) 45 = Z_to_bv 64 str)
  by exact (pjf_ew_x k regs Hk regsc xs 45 0 eq_refl).
assert (HS : st_ok tfibsegs (pjf_env regs regsc xs) ss_X2
  (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x83684) memc (YK11.seg_rom tfibsegs)))).
{ pose proof E2m as E2u. pose proof E8 as E8u. unfold pjf_env in E2u, E8u. unfold ss_X2, pjf_env.
  apply (pjf_reseat B HSS k ly S0 U W regs mem md ch v Hk HPRE HV HPO lyc Sc Uc Wc regsc memc mdc 0x83684
    [fld 8 16 45] [(8%nat, mkAF 4096 PJF_CEIL 3)] [] xs HARU Hsp H20 Hpres Hfrm ltac:(vm_compute; reflexivity)).
  - constructor; [|constructor].
    exact (pjf_fld_ok k regs Hk regsc xs 8%bv 8 16 45 Wc memc v str ltac:(reflexivity) H8 ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(rewrite fsw_SOff0; exact E45) (proj1 Hstr) (fsw_pj_u64_val tfibsegs _ _ _ Hstr)).
  - exact (pjt_pd1 _ 8 v 16 16 E2u E8u ltac:(lia) ltac:(lia) ltac:(lia) HNI).
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8u.
    change (2 ^ 3) with 8. split; [|exact I]. split; [unfold PJF_CEIL in *; lia|]. split; [exact Hv8 | lia].
  - exact I. }
assert (SHOK : sh_ok tfibsegs pBx SH_X2 (pjf_env regs regsc xs) (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor].
  apply (pjf_shent (pjf_env regs regsc xs) (mrestrict (w_H Wc) memc) 8 v 16 24).
  - unfold pjf_env. apply pjf_U_bx. exact H20.
  - unfold pjf_env. apply (pjf_U_atom regsc _ 8%bv 8 v); [reflexivity | exact H8 | lia].
  - lia.
  - intros x Hx. exact (HRA x ltac:(lia)).
  - replace (24 - 16) with 8 by lia. apply pjt_in_app8.
    + exact (proj2 (proj2 (proj2 (HPL (v + 16) ltac:(lia))))).
    + replace (v + 16 + 7) with (v + 23) by lia. exact (proj2 (proj2 (proj2 (HPL (v + 23) ltac:(lia))))). }
(* run 0x83684 .. the `jal fuzz_free` 0x8369c, stopping at the callee's entry 0x82d40 *)
fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ HARU SHOK fs_Bspan 535872.
{ cbn [ss_mem ss_X2 pjss fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
match goal with |- SRr _ _ (mkCfg ?mC _) _ => rename mC into msC end.
pose proof (fsw_reg_lit _ _ _ msC 1%bv 0x836a0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
assert (R10 : YK11.getr (ms_regs msC) 10 = w64 str) by (pjt_rd HS (10%bv : bv 5); exact E45).
assert (HRm : pjf_regs regs v (ms_regs msC)).
{ apply (pjt_regs_of regsc (ms_regs msC) HR).
  - pjt_rd HS (2%bv : bv 5). exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl).
  - pjt_rd HS (3%bv : bv 5). exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl).
  - pjt_rd HS (4%bv : bv 5). exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl).
  - pjt_rd HS (27%bv : bv 5). exact (ew_Ereg_nat regsc _ 27 27%bv eq_refl).
  - pjt_rd HS (8%bv : bv 5). exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl).
  - pjt_rd HS (9%bv : bv 5). exact (ew_Ereg_nat regsc _ 9 9%bv eq_refl).
  - pjt_rd HS (18%bv : bv 5). exact (ew_Ereg_nat regsc _ 18 18%bv eq_refl).
  - pjt_rd HS (19%bv : bv 5). exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl).
  - pjt_rd HS (20%bv : bv 5). exact (ew_Ereg_nat regsc _ 20 20%bv eq_refl).
  - pjt_rd HS (21%bv : bv 5). exact (ew_Ereg_nat regsc _ 21 21%bv eq_refl). }
assert (SB : same_below memc (ms_mem msC) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regs regsc xs) (ss_mem ss_X2) memc (ms_mem msC) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regs regsc xs) pjf_cs [fld 8 16 45] a (sp0 - 96)
    ltac:(constructor; [cbn; lia | constructor]) E2m Ha). unfold STK, sp0 in *. lia. }
assert (Hfrm1 : pjf_frm regs Wc (ms_mem msC)).
{ intros j Hj.
  pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  apply (FRMREG _ _ HR0); [| |exact Hj].
  - repeat (rewrite ew_ewset_other by lia). exact E2m.
  - intros i Hi. rewrite fsw_SOff0. repeat (rewrite ew_ewset_other by lia). rewrite <- fsw_SOff0.
    exact (pjf_ew_sav k regs Hk regsc xs (33 + i) i eq_refl Hi). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdR) _ =>
  pose proof (pjt_inv_below Dfr Ds lyc Sc Uc Wc memc (ms_mem msC) mdc mdR HINV0 HJ HARU Hfrm1 SB) as HINVm end.
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ msC HS eq_refl).
refine (pjt_call Dfr Ds [] str 0x836a0 lyc Sc Uc Wc (ms_regs msC) (ms_mem msC) _ _ _ HRm R1 R10
  ltac:(lia) ltac:(lia) ltac:(reflexivity) _).
- pose proof HSTR as HSTR'.
  destruct HSTR' as [(E1 & E3)|(k0 & _ & E3)]; [left; split; assumption | right; exists k0; exact E3].
- rewrite app_nil_r. exact HINVm.
- intros lyr Sr Ur Wr regsr memr mdr HINVr HRr.
  pose proof HRr as (Hspr & _ & _ & _ & _ & _ & _ & _ & H20r & _).
  pose proof (pjt_pres _ _ _ _ _ _ _ _ HINVr) as Hpresr.
  unfold TINV, pjf_inv in HINVr.
  destruct HINVr as (HJr & HARUr & HHr & Hfrmr & HBPr & HUcr & Hglobr & HPDr & _ & Hpor & _ & _).
  assert (HS3 : st_ok tfibsegs (pjf_env regs regsr []) ss_X3
    (restrict (w_H Wr) (YK11.mkst regsr (Z_to_bv 64 0x836a0) memr (YK11.seg_rom tfibsegs)))).
  { unfold ss_X3, pjf_env.
    apply (pjf_reseat B HSS k ly S0 U W regs mem md ch v Hk HPRE HV HPO lyr Sr Ur Wr regsr memr mdr 0x836a0
      [] [] [] [] HARUr Hspr H20r Hpresr Hfrmr ltac:(vm_compute; reflexivity) (Forall_nil _)).
    - apply pjt_pd0. rewrite (ew_Ereg_nat regsr _ 2 2%bv eq_refl). exact Hspr.
    - exact I.
    - exact I. }
  rewrite app_nil_r in HPDr.
  exact (pjf_end_memset B HSS fs_memset_realizesU k ly S0 U W regs mem md ch v D live peak cnt fail Hk HPRE HV HPO
    HVS str kids keys n ks Ds Dk Dy HSTR HKIDS HKEYS lyr Sr Ur Wr regsr memr mdr (Dfr ++ Ds)
    HS3 HJr HARUr HRr HPDr HBPr HUcr Hglobr Hpor).
Qed.

(* ---- 0x8366c .. fuzz_free (keys) 0x83680, back at 0x83684 ---- *)
Lemma pjt_seg_keys : forall Dfr lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  TINV Dfr (Ds ++ Dy) lyc Sc Uc Wc memc mdc -> pjf_regs regs v regsc ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x8366c) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros Dfr lyc Sc Uc Wc regsc memc mdc HINV HR.
pose proof ENTRY as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & _ & _).
pose proof STKF as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21).
pose proof (pjt_pres _ _ _ _ _ _ _ _ HINV) as Hpres.
pose proof (pjt_hdr _ _ _ _ _ _ _ _ HINV) as (_ & _ & _ & _ & _ & Hkeys & _ & _).
pose proof HINV as HINV0.
unfold TINV, pjf_inv in HINV.
destruct HINV as (HJ & HARU & HH & Hfrm & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v (proj1 HARU) Hpo) as (HPL & _ & _).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct Hpo as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
set (xs := [w64 keys]).
assert (E2m : bv_unsigned (ew (pjf_env regs regsc xs) 2) = sp0 - 96)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E2 : bv_unsigned (ew (pjf_env regs regsc xs) 2) = sp0 + (-96)) by (rewrite E2m; lia).
assert (E8 : bv_unsigned (ew (pjf_env regs regsc xs) 8) = v)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl), H8; unfold w64; apply wz; lia).
assert (E9 : bv_unsigned (ew (pjf_env regs regsc xs) 9) = v + 32)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), H9; unfold w64; apply wz; lia).
assert (E45 : ew (pjf_env regs regsc xs) 45 = Z_to_bv 64 keys)
  by exact (pjf_ew_x k regs Hk regsc xs 45 0 eq_refl).
assert (HS : st_ok tfibsegs (pjf_env regs regsc xs) ss_X1
  (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x8366c) memc (YK11.seg_rom tfibsegs)))).
{ pose proof E2m as E2u. pose proof E8 as E8u. pose proof E9 as E9u. unfold pjf_env in E2u, E8u, E9u.
  unfold ss_X1, pjf_env.
  apply (pjf_reseat B HSS k ly S0 U W regs mem md ch v Hk HPRE HV HPO lyc Sc Uc Wc regsc memc mdc 0x8366c
    [fld 9 0 45] [(9%nat, mkAF 4096 PJF_CEIL 3)] [(SOff 8 32, SOff 9 0)] xs HARU Hsp H20 Hpres Hfrm
    ltac:(vm_compute; reflexivity)).
  - constructor; [|constructor].
    exact (pjf_fld_ok k regs Hk regsc xs 9%bv 9 0 45 Wc memc (v + 32) keys ltac:(reflexivity) H9 ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(rewrite fsw_SOff0; exact E45) (proj1 Hkeys)
      ltac:(rewrite Z.add_0_r; exact (fsw_pj_u64_val tfibsegs _ _ _ Hkeys))).
  - exact (pjt_pd1 _ 9 (v + 32) 0 32 E2u E9u ltac:(lia) ltac:(lia) ltac:(lia) HNI).
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9u.
    change (2 ^ 3) with 8. split; [|exact I]. split; [unfold PJF_CEIL in *; lia|].
    split; [rewrite Zplus_mod, Hv8; reflexivity | lia].
  - cbn [alias_ok]. split; [|exact I]. cbn [sv_denot]. rewrite E8u, E9u. f_equal. lia. }
assert (SHOK : sh_ok tfibsegs pBx SH_X1 (pjf_env regs regsc xs) (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor].
  apply (pjf_shent (pjf_env regs regsc xs) (mrestrict (w_H Wc) memc) 9 (v + 32) 0 8).
  - unfold pjf_env. apply pjf_U_bx. exact H20.
  - unfold pjf_env. apply (pjf_U_atom regsc _ 9%bv 9 (v + 32)); [reflexivity | exact H9 | lia].
  - lia.
  - intros x Hx. exact (HRA x ltac:(lia)).
  - replace (v + 32 + 0) with (v + 32) by lia. replace (8 - 0) with 8 by lia. apply pjt_in_app8.
    + exact (proj2 (proj2 (proj2 (HPL (v + 32) ltac:(lia))))).
    + replace (v + 32 + 7) with (v + 39) by lia. exact (proj2 (proj2 (proj2 (HPL (v + 39) ltac:(lia))))). }
(* run 0x8366c .. the `jal fuzz_free` 0x83680, stopping at the callee's entry 0x82d40 *)
fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ HARU SHOK fs_Bspan 535872.
{ cbn [ss_mem ss_X1 pjss fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
match goal with |- SRr _ _ (mkCfg ?mC _) _ => rename mC into msC end.
pose proof (fsw_reg_lit _ _ _ msC 1%bv 0x83684 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
assert (R10 : YK11.getr (ms_regs msC) 10 = w64 keys) by (pjt_rd HS (10%bv : bv 5); exact E45).
assert (HRm : pjf_regs regs v (ms_regs msC)).
{ apply (pjt_regs_of regsc (ms_regs msC) HR).
  - pjt_rd HS (2%bv : bv 5). exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl).
  - pjt_rd HS (3%bv : bv 5). exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl).
  - pjt_rd HS (4%bv : bv 5). exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl).
  - pjt_rd HS (27%bv : bv 5). exact (ew_Ereg_nat regsc _ 27 27%bv eq_refl).
  - pjt_rd HS (8%bv : bv 5). exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl).
  - pjt_rd HS (9%bv : bv 5). exact (ew_Ereg_nat regsc _ 9 9%bv eq_refl).
  - pjt_rd HS (18%bv : bv 5). exact (ew_Ereg_nat regsc _ 18 18%bv eq_refl).
  - pjt_rd HS (19%bv : bv 5). exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl).
  - pjt_rd HS (20%bv : bv 5). exact (ew_Ereg_nat regsc _ 20 20%bv eq_refl).
  - pjt_rd HS (21%bv : bv 5). exact (ew_Ereg_nat regsc _ 21 21%bv eq_refl). }
assert (SB : same_below memc (ms_mem msC) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regs regsc xs) (ss_mem ss_X1) memc (ms_mem msC) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regs regsc xs) pjf_cs [fld 9 0 45] a (sp0 - 96)
    ltac:(constructor; [cbn; lia | constructor]) E2m Ha). unfold STK, sp0 in *. lia. }
assert (Hfrm1 : pjf_frm regs Wc (ms_mem msC)).
{ intros j Hj.
  pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  apply (FRMREG _ _ HR0); [| |exact Hj].
  - repeat (rewrite ew_ewset_other by lia). exact E2m.
  - intros i Hi. rewrite fsw_SOff0. repeat (rewrite ew_ewset_other by lia). rewrite <- fsw_SOff0.
    exact (pjf_ew_sav k regs Hk regsc xs (33 + i) i eq_refl Hi). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdR) _ =>
  pose proof (pjt_inv_below Dfr (Ds ++ Dy) lyc Sc Uc Wc memc (ms_mem msC) mdc mdR HINV0 HJ HARU Hfrm1 SB) as HINVm end.
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ msC HS eq_refl).
refine (pjt_call Dfr Dy Ds keys 0x83684 lyc Sc Uc Wc (ms_regs msC) (ms_mem msC) _ _ _ HRm R1 R10
  ltac:(lia) ltac:(lia) ltac:(reflexivity) _).
- pose proof HKEYS as HKEYS'.
  destruct HKEYS' as [(E1 & _ & E3)|(_ & k0 & _ & _ & E3)]; [left; split; assumption | right; exists k0; exact E3].
- exact (pjt_inv_perm _ _ _ _ _ _ _ _ _ (Permutation_app_comm Ds Dy) HINVm).
- intros lyr Sr Ur Wr regsr memr mdr HINVr HRr.
  exact (pjt_seg_str (Dfr ++ Dy) lyr Sr Ur Wr regsr memr mdr HINVr HRr).
Qed.

(* ---- 0x83654 .. fuzz_free (kids) 0x83668, back at 0x8366c ---- *)
Lemma pjt_seg_kids : forall Dfr lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  TINV Dfr (Ds ++ Dk ++ Dy) lyc Sc Uc Wc memc mdc -> pjf_regs regs v regsc ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x83654) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros Dfr lyc Sc Uc Wc regsc memc mdc HINV HR.
pose proof ENTRY as (Hal16 & Hceil & H47 & Hv0 & Hv1 & Hv8 & _ & _).
pose proof STKF as (HSTK1 & HSTK2 & _ & HSTK4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & H3 & H4 & H27 & H8 & H9 & H18 & H19 & H20 & H21).
pose proof (pjt_pres _ _ _ _ _ _ _ _ HINV) as Hpres.
pose proof (pjt_hdr _ _ _ _ _ _ _ _ HINV) as (_ & _ & _ & _ & Hkids & _ & _ & _).
pose proof HINV as HINV0.
unfold TINV, pjf_inv in HINV.
destruct HINV as (HJ & HARU & HH & Hfrm & HBP & HUc & Hglob & HPD & HBKc & Hpo & HKEEP & HRO).
destruct (pjf_place B lyc Sc Wc (unpoison Uc memc) mdc memc v (proj1 HARU) Hpo) as (HPL & _ & _).
assert (HRA : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56)
  by (destruct Hpo as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr).
assert (HNI : forall x, v <= x < v + 56 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (proj1 (proj2 (proj2 (HPL x Hx))))).
set (xs := [w64 kids]).
assert (E2m : bv_unsigned (ew (pjf_env regs regsc xs) 2) = sp0 - 96)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E2 : bv_unsigned (ew (pjf_env regs regsc xs) 2) = sp0 + (-96)) by (rewrite E2m; lia).
assert (E8 : bv_unsigned (ew (pjf_env regs regsc xs) 8) = v)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl), H8; unfold w64; apply wz; lia).
assert (E19 : bv_unsigned (ew (pjf_env regs regsc xs) 19) = v + 24)
  by (unfold pjf_env; rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl), H19; unfold w64; apply wz; lia).
assert (E45 : ew (pjf_env regs regsc xs) 45 = Z_to_bv 64 kids)
  by exact (pjf_ew_x k regs Hk regsc xs 45 0 eq_refl).
assert (HS : st_ok tfibsegs (pjf_env regs regsc xs) ss_T0
  (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 0x83654) memc (YK11.seg_rom tfibsegs)))).
{ pose proof E2m as E2u. pose proof E8 as E8u. pose proof E19 as E19u. unfold pjf_env in E2u, E8u, E19u.
  unfold ss_T0, pjf_env.
  apply (pjf_reseat B HSS k ly S0 U W regs mem md ch v Hk HPRE HV HPO lyc Sc Uc Wc regsc memc mdc 0x83654
    [fld 19 0 45] [(19%nat, mkAF 4096 PJF_CEIL 3)] [(SOff 8 24, SOff 19 0)] xs HARU Hsp H20 Hpres Hfrm
    ltac:(vm_compute; reflexivity)).
  - constructor; [|constructor].
    exact (pjf_fld_ok k regs Hk regsc xs 19%bv 19 0 45 Wc memc (v + 24) kids ltac:(reflexivity) H19 ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(rewrite fsw_SOff0; exact E45) (proj1 Hkids)
      ltac:(rewrite Z.add_0_r; exact (fsw_pj_u64_val tfibsegs _ _ _ Hkids))).
  - exact (pjt_pd1 _ 19 (v + 24) 0 24 E2u E19u ltac:(lia) ltac:(lia) ltac:(lia) HNI).
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E19u.
    change (2 ^ 3) with 8. split; [|exact I]. split; [unfold PJF_CEIL in *; lia|].
    split; [rewrite Zplus_mod, Hv8; reflexivity | lia].
  - cbn [alias_ok]. split; [|exact I]. cbn [sv_denot]. rewrite E8u, E19u. f_equal. lia. }
assert (SHOK : sh_ok tfibsegs pBx SH_T0 (pjf_env regs regsc xs) (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor].
  apply (pjf_shent (pjf_env regs regsc xs) (mrestrict (w_H Wc) memc) 19 (v + 24) 0 8).
  - unfold pjf_env. apply pjf_U_bx. exact H20.
  - unfold pjf_env. apply (pjf_U_atom regsc _ 19%bv 19 (v + 24)); [reflexivity | exact H19 | lia].
  - lia.
  - intros x Hx. exact (HRA x ltac:(lia)).
  - replace (v + 24 + 0) with (v + 24) by lia. replace (8 - 0) with 8 by lia. apply pjt_in_app8.
    + exact (proj2 (proj2 (proj2 (HPL (v + 24) ltac:(lia))))).
    + replace (v + 24 + 7) with (v + 31) by lia. exact (proj2 (proj2 (proj2 (HPL (v + 31) ltac:(lia))))). }
(* run 0x83654 .. the `jal fuzz_free` 0x83668, stopping at the callee's entry 0x82d40 *)
fsw_aj_run_to_tokU pj_free_tbl_ok HS HJ HARU SHOK fs_Bspan 535872.
{ cbn [ss_mem ss_T0 pjss fsT_ret_regions app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -96);
    first [ reflexivity | exact E2 | solve [cbn; unfold STK in *; lia] | solve [cbn; lia]
          | solve [repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil] ]. }
match goal with |- SRr _ _ (mkCfg ?mC _) _ => rename mC into msC end.
pose proof (fsw_reg_lit _ _ _ msC 1%bv 0x8366c HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
assert (R10 : YK11.getr (ms_regs msC) 10 = w64 kids) by (pjt_rd HS (10%bv : bv 5); exact E45).
assert (HRm : pjf_regs regs v (ms_regs msC)).
{ apply (pjt_regs_of regsc (ms_regs msC) HR).
  - pjt_rd HS (2%bv : bv 5). exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl).
  - pjt_rd HS (3%bv : bv 5). exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl).
  - pjt_rd HS (4%bv : bv 5). exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl).
  - pjt_rd HS (27%bv : bv 5). exact (ew_Ereg_nat regsc _ 27 27%bv eq_refl).
  - pjt_rd HS (8%bv : bv 5). exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl).
  - pjt_rd HS (9%bv : bv 5). exact (ew_Ereg_nat regsc _ 9 9%bv eq_refl).
  - pjt_rd HS (18%bv : bv 5). exact (ew_Ereg_nat regsc _ 18 18%bv eq_refl).
  - pjt_rd HS (19%bv : bv 5). exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl).
  - pjt_rd HS (20%bv : bv 5). exact (ew_Ereg_nat regsc _ 20 20%bv eq_refl).
  - pjt_rd HS (21%bv : bv 5). exact (ew_Ereg_nat regsc _ 21 21%bv eq_refl). }
assert (SB : same_below memc (ms_mem msC) alloc_ceiling).
{ apply (pjf_same_below_wr (pjf_env regs regsc xs) (ss_mem ss_T0) memc (ms_mem msC) alloc_ceiling HF); [|lia].
  intros a Ha. pose proof (pjf_wrange_ret (pjf_env regs regsc xs) pjf_cs [fld 19 0 45] a (sp0 - 96)
    ltac:(constructor; [cbn; lia | constructor]) E2m Ha). unfold STK, sp0 in *. lia. }
assert (Hfrm1 : pjf_frm regs Wc (ms_mem msC)).
{ intros j Hj.
  pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  apply (FRMREG _ _ HR0); [| |exact Hj].
  - repeat (rewrite ew_ewset_other by lia). exact E2m.
  - intros i Hi. rewrite fsw_SOff0. repeat (rewrite ew_ewset_other by lia). rewrite <- fsw_SOff0.
    exact (pjf_ew_sav k regs Hk regsc xs (33 + i) i eq_refl Hi). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdR) _ =>
  pose proof (pjt_inv_below Dfr (Ds ++ Dk ++ Dy) lyc Sc Uc Wc memc (ms_mem msC) mdc mdR HINV0 HJ HARU Hfrm1 SB)
    as HINVm end.
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ msC HS eq_refl).
refine (pjt_call Dfr Dk (Ds ++ Dy) kids 0x8366c lyc Sc Uc Wc (ms_regs msC) (ms_mem msC) _ _ _ HRm R1 R10
  ltac:(lia) ltac:(lia) ltac:(reflexivity) _).
- pose proof HKIDS as HKIDS'.
  destruct HKIDS' as [(E1 & _ & E3)|(k0 & _ & _ & E3)]; [left; split; assumption | right; exists k0; exact E3].
- assert (HPm : Permutation (Ds ++ Dk ++ Dy) (Dk ++ Ds ++ Dy))
    by (rewrite !app_assoc; apply Permutation_app_tail; apply Permutation_app_comm).
  exact (pjt_inv_perm _ _ _ _ _ _ _ _ _ HPm HINVm).
- intros lyr Sr Ur Wr regsr memr mdr HINVr HRr.
  exact (pjt_seg_keys (Dfr ++ Dk) lyr Sr Ur Wr regsr memr mdr HINVr HRr).
Qed.

(* ================= the tail: 0x83654 .. the ret, the goal pjf_end_memset closes ================= *)
(* statement agreed with the pj_free walk lane (internal path): reached from the loop exit
   (bltu 0x83650) and from the entry's n = 0 arm (beqz 0x835d8); Rem is Ds ++ Dk ++ Dy, the kids' subtree blocks are
   in Dfr; F keeps v's 56 bytes *)
Lemma pjf_tail : forall F Dfr lyc Sc Uc (Wc : world tfibsegs) regsc memc mdc,
  (forall x : Z, v <= x < v + 56 -> F x) ->
  pjf_inv B k ly S0 U W regs mem md v D live peak cnt fail F Dfr (Ds ++ Dk ++ Dy) lyc Sc Uc Wc memc mdc ->
  pjf_regs regs v regsc ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 0x83654) memc (YK11.seg_rom tfibsegs)) mdc) GOAL.
Proof.
intros F Dfr lyc Sc Uc Wc regsc memc mdc HF HINV HR.
apply (pjt_seg_kids Dfr lyc Sc Uc Wc regsc memc mdc); [|exact HR].
unfold TINV. unfold pjf_inv in HINV |- *.
destruct HINV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
split; [exact I6|]. split; [exact I7|]. split; [exact I8|]. split; [exact I9|]. split; [exact I10|].
split; [intros x Hx; apply I11; apply HF; exact Hx | exact I12].
Qed.
End N.
End W.
