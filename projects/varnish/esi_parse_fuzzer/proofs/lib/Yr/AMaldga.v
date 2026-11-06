(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 AMTac AMallocA AMallocH AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).

(* [comment removed for export] *)
Definition ref_ws (sb c : Z) (fr : list Z) (k : Z) : list word :=
  map (fun i => Z_to_bv 64 (i * class_size c / kCompactPtrScale)) (skipn (length fr - Z.to_nat k) fr).

(* [comment removed for export] *)
Lemma nth_error_skipn' : forall {X} (l : list X) i j, nth_error (skipn i l) j = nth_error l (i + j).
Proof. intros X l. induction l as [|x l IH]; intros [|i] j; cbn; try reflexivity; [destruct j; reflexivity| apply IH]. Qed.
Lemma last_nth_error : forall (l : list Z), l <> [] -> nth_error l (length l - 1) = Some (nth (length l - 1) l 0).
Proof. intros l NE. apply nth_error_nth'. destruct l; [congruence| cbn; lia]. Qed.

Section Refill.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (n : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Let v := aview_of (pa_hull A) m.
  Let P := a_pl A.
  Local Notation c := (class_of n).
  Local Notation R := (a_reg A (class_of n)).
  Local Notation fr := (rg_free (a_reg A (class_of n))).
  Local Notation nf := (Z.of_nat (length (rg_free (a_reg A (class_of n))))).
  Local Notation k := (refill_count (class_of n)).
  Local Notation kidx := (nth (length (rg_free (a_reg A (class_of n))) - 1) (rg_free (a_reg A (class_of n))) 0).
  Local Notation sb := (a_sb A).
  Local Notation ri := (a_ri A).
  (* [comment removed for export] *)
  Hypothesis CI : a_cache_inited A = true.
  Hypothesis EMP : pk_chunks (a_cache A (class_of n)) = [].
  Hypothesis ENOUGH : refill_count (class_of n) <= Z.of_nat (length (rg_free (a_reg A (class_of n)))).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.

  #[using="NR"] Lemma ref_CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.
  #[using="NR A"] Lemma ref_k : max_count c = 2 * k /\ 1 <= k <= 8 /\ Z.shiftr (max_count c) 1 = k /\ 2 <= max_count c <= 16.
  Proof.
    (first [ pose proof ((max_count_range _ ref_CR)) as dR_1; dand3 dR_1 as M1 M2 M3 | pose proof (max_count_range _ ref_CR) as (M1 & M2 & M3) ]). rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.
  #[using="W ENOUGH NR AI md m DR Clg"] Lemma ref_kidx : In kidx fr /\ 0 <= kidx < carved_count A c /\ nth_error fr (length fr - 1) = Some kidx /\ fr <> [].
  Proof.
    (first [ pose proof (ref_k) as dR_2; dand3 dR_2 as _ KR _ | pose proof ref_k as (_ & KR & _) ]).
    assert (NE : fr <> []) by (intros E; rewrite E in ENOUGH; cbn in ENOUGH; lia).
    pose proof (last_nth_error fr NE) as L. pose proof (nth_error_In _ _ L) as IN.
    (first [ pose proof ((wfR A W)) as dR_3; dand3 dR_3 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c ref_CR)) as dR_4; dand10 dR_4 as _ _ _ _ _ _ _ _ B _ | destruct (WR c ref_CR) as (_ & _ & _ & _ & _ & _ & _ & _ & B & _) ]).
    split; [exact IN|]. split; [| exact (conj L NE)]. unfold carved_count, carved_count_. exact (B _ IN).
  Qed.
  #[using="W ENOUGH NR AI md m DR Clg"] Lemma ref_nf : k <= nf < 2^27 /\ 4 * nf <= rg_mapped_fa R.
  Proof.
    (first [ pose proof ((wfR A W)) as dR_5; dand3 dR_5 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c ref_CR)) as dR_6; dand12 dR_6 as B1 _ _ _ _ _ B7 _ _ _ _ B12 | destruct (WR c ref_CR) as (B1 & _ & _ & _ & _ & _ & B7 & _ & _ & _ & _ & B12) ]).
    (* [comment removed for export] *)
    pose proof (wf_au_cap A c W ref_CR) as [AU _]. pose proof (class_size_range c ref_CR) as CSR.
    assert (Q1 : rg_allocated_user R / class_size c <= rg_allocated_user R / 32) by (apply Z.div_le_compat_l; lia).
    assert (Q2 : 32 * (rg_allocated_user R / 32) <= rg_allocated_user R) by (apply Z.mul_div_le; lia).
    unfold kAuCap, kFreeArrayMapSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="W AI md m DR"] Lemma ref_ri : ri = sb + kSpaceSize /\ kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling /\ ri mod 128 = 0 /\ sb mod 4096 = 0 /\
                 region_info_addr sb c = ri + 128 * c /\ free_array_beg sb c = free_array_of sb c.
  Proof.
    (first [ pose proof ((sb_facts A W)) as dR_7; dand5 dR_7 as _ SBM HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBM & HB6 & RSB & SCE) ]). unfold a_ri, p_ri, a_sb in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (unfold kSpaceSize, kHighMemBeg in *; lia).
    all: try (apply (mod0_down _ 0x10000 128); [exists 512; reflexivity|]; unfold kSpaceSize; rewrite <- Zplus_mod_idemp_l, SBM; reflexivity).
    all: try (apply (mod0_down _ 0x10000 4096); [exists 16; reflexivity| exact SBM]).
    all: unfold region_info_addr, kRegionInfoSize, free_array_beg, free_array_of, region_beg, kRegionSize, kFreeArrayOffset, kSpaceSize in *; lia.
  Qed.
  #[using="W AI n md m DR Clg"] Lemma ref_sep : apart (p_thr P) 4096 ri 4096 /\ apart ri 4096 sb (2^37) /\ apart (p_ctx P) 0x10000 ri 4096 /\
                  apart (p_nodes0 P) kDepotNodesBlock ri 4096 /\ apart (p_frames0 P) kStackStoreBlockBytes ri 4096.
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_8; dand10 dR_8 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    (first [ pose proof ((sb_facts A W)) as dR_9; dand5 dR_9 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). destruct ref_ri as (RI & _).
    unfold a_thr, a_ctx, a_nodes0, a_frames0, a_b6, a_sb, a_ri in *. subst P. rewrite RI.
    assert (B6 : forall i b s, i <> 0%nat -> nth_error (big_maps A) i = Some (b, s) -> apart b s (p_sb (a_pl A) + kSpaceSize) 4096).
    { intros i b s Hi Hn. destruct (bm_sep A i 0 _ _ _ _ W Hn E0 Hi); unfold apart, kSpaceReserve, kSpaceSize in *; lia. }
    split; [exact (B6 4%nat _ _ ltac:(lia) E4)|]. split; [unfold apart, kSpaceSize; lia|].
    split; [exact (B6 5%nat _ _ ltac:(lia) E5)|]. split; [exact (B6 7%nat _ _ ltac:(lia) E7)| exact (B6 8%nat _ _ ltac:(lia) E8)].
  Qed.
  (* [comment removed for export] *)
  #[using="NR AI n md DR"] Lemma ref_CRI : ro_cells rsegs v 0xb1d88 [C8 (Z_to_bv 64 ri)].
  Proof.
    pose proof (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_RegionInfo_ptr) (p_ri (a_pl A))) by tauto. apply u64_ro. exact X.
  Qed.

  (* [comment removed for export] *)
  #[using="W EMP CI NR AI md DR"] Lemma ref_PC : exists ks, length ks = 16%nat /\
    rw_cells rsegs v (p_thr P + 208 + 80 * c) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Proof.
    pose proof ref_CR as CR.
    pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. (first [ dand5 C as C _ _ TM _ | destruct C as (C & _ & _ & TM & _) ]).
    (first [ pose proof ((C c ltac:(lia))) as dR_11; dand5 dR_11 as L16 Hcnt Hmax Hent Hjunk | destruct (C c ltac:(lia)) as (L16 & Hcnt & Hmax & Hent & Hjunk) ]). rewrite CI in Hmax. cbn [andb negb] in Hmax.
    destruct (Z.eqb_spec c 0); [lia|]. destruct Hmax as [Hmax Hsz]. rewrite EMP in Hcnt, Hjunk. cbn [length Z.of_nat] in Hcnt, Hjunk.
    (first [ dex1 Hjunk as jb; destruct Hjunk as [Ljb Bjb] | dand3 Hjunk as jb Ljb Bjb | destruct Hjunk as (jb & Ljb & Bjb) ]).
    pose proof (place_facts A W) as (Pthr & _). cbv zeta in Pthr. pose proof alloc_ceiling_val as CE.
    (first [ dand3 Pthr as Pthr PthrC PthrM | destruct Pthr as (Pthr & PthrC & PthrM) ]). apply app_facts in Pthr.
    unfold off_th_per_class, off_th_alloc_cache, off_pc_count, off_pc_max_count, off_pc_class_size, off_pc_chunk, kPerClassSize in *.
    set (e := p_thr P + 208 + 80 * c). replace (p_thr (a_pl A) + (208 + 80 * c)) with e in * by (subst e P; lia).
    exists (words4 jb 16). split; [apply words4_length|].
    apply ro_rw.
    - split; [cbn -[words4 u32s]; rewrite ?u32s_length, ?words4_length; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact I | reflexivity | lia]|].
      cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_app. split; [rewrite Z.add_0_r in Hcnt; exact Hcnt|]. rewrite length_le4.
      apply bytes_at_app. split; [replace (e + Z.of_nat 4) with (e + 4) by lia; exact Hmax|]. rewrite length_le4.
      apply bytes_at_app. split; [replace (e + Z.of_nat 4 + Z.of_nat 4) with (e + 8) by lia; exact Hsz|]. rewrite length_le8.
      replace (e + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8) with (e + 16) by lia.
      rewrite u32s_words4 by lia. replace (e + 16) with (e + (16 + 4 * 0)) by lia. exact Bjb.
    - cbn [cells_size csize Nat.add]. intros i Hi. subst e P. replace (p_thr (a_pl A) + 208 + 80 * c + i) with (p_thr (a_pl A) + (208 + 80 * c + i)) by lia.
      apply TM. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ENOUGH NR"] Lemma ref_ws_len : length (ref_ws sb c fr k) = Z.to_nat k.
  Proof. (first [ pose proof (ref_k) as dR_14; dand3 dR_14 as _ KR _ | pose proof ref_k as (_ & KR & _) ]). unfold ref_ws. rewrite map_length, length_skipn. lia. Qed.
  #[using="W ENOUGH NR AI md m DR Clg"] Lemma ref_ws_last : nth_error (ref_ws sb c fr k) (Z.to_nat (k - 1)) = Some (Z_to_bv 64 (kidx * class_size c / kCompactPtrScale)).
  Proof.
    (first [ pose proof (ref_k) as dR_15; dand3 dR_15 as _ KR _ | pose proof ref_k as (_ & KR & _) ]). (first [ dand4 ref_kidx as _ _ L NE | destruct ref_kidx as (_ & _ & L & NE) ]). unfold ref_ws. rewrite nth_error_map, nth_error_skipn'.
    replace (length fr - Z.to_nat k + Z.to_nat (k - 1))%nat with (length fr - 1)%nat by lia. rewrite L. reflexivity.
  Qed.
  #[using="W ENOUGH NR AI md DR"] Lemma ref_region : exists na : word,
    rw_cells rsegs v (ri + 128 * c) [C8 (Z_to_bv 64 0)] /\
    rw_cells rsegs v (ri + 128 * c + 16) [C8 (Z_to_bv 64 nf)] /\
    rw_cells rsegs v (ri + 128 * c + 72) [C8 na] /\
    u32arr rsegs v (free_array_of sb c + 4 * (nf - k)) (ref_ws sb c fr k).
  Proof.
    pose proof ref_CR as CR. (first [ pose proof (ref_k) as dR_17; dand4 dR_17 as _ KR _ _ | pose proof ref_k as (_ & KR & _ & _) ]). pose proof ref_nf as (NF & FA4). pose proof alloc_ceiling_val as CE.
    (first [ dand7 ref_ri as RI RLO RHI RAL SBAL RIA FAE | destruct ref_ri as (RI & RLO & RHI & RAL & SBAL & RIA & FAE) ]).
    pose proof (ar_regions _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) c CR) as RR. unfold region_repr_ in RR. cbv zeta in RR.
    rewrite RIA, FAE in RR. (first [ dand13 RR as Hnf Hfa Hal Ham Hmu Hmm Hex J64 Jna Jrt ENT MFA MUS | destruct RR as (Hnf & Hfa & Hal & Ham & Hmu & Hmm & Hex & J64 & Jna & Jrt & ENT & MFA & MUS) ]).
    pose proof (ar_locks _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as LK. unfold locks_repr_ in LK. cbv zeta in LK. destruct LK as (LK & _).
    destruct (LK c ltac:(lia)) as [MX0 _]. change (p_ri (a_pl A)) with ri in MX0. unfold kRegionInfoSize in MX0. rewrite Z.add_0_r in MX0.
    (first [ pose proof ((ar_maps _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_20; dand3 dR_20 as _ MRI _ | pose proof (ar_maps _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & MRI & _) ]). change (p_ri (a_pl A)) with ri in MRI.
    pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in RB.
    unfold off_ri_num_freed, off_ri_n_allocated in *.
    assert (TMi : forall a j, ri <= a -> a + j <= ri + 4096 -> mapped v a j).
    { intros a j H1 H2 i Hi. replace (a + i) with (ri + (a - ri + i)) by lia. apply MRI. lia. }
    (first [ dex1 Jna as bna; destruct Jna as [Lna Bna] | dand3 Jna as bna Lna Bna | destruct Jna as (bna & Lna & Bna) ]).
    assert (FAR : free_array_of sb c = region_beg sb c + kFreeArrayOffset) by (unfold free_array_of, region_beg, kRegionSize, kFreeArrayOffset; lia).
    exists (le_bytes_to_word (firstn 8 bna)).
    split; [|split; [|split]].
    - apply ro_rw; [apply u64_ro; exact MX0| apply TMi; cbn; lia].
    - apply ro_rw; [apply u64_ro; exact Hnf| apply TMi; cbn; lia].
    - apply ro_rw; [| apply TMi; cbn; lia]. apply bytes_ro_C8. rewrite le8_of_bytes by (rewrite firstn_length; lia).
      replace (ri + 128 * c + 72) with (ri + 128 * c + 72 + Z.of_nat 0) by lia. apply (bytes_at_mid v _ bna 0 8 Bna). lia.
    - split.
      + unfold ref_ws. apply (u32s_of_entries v (fun i => i * class_size c / kCompactPtrScale)).
        * intros i x E. rewrite nth_error_skipn' in E. pose proof (ENT _ _ E) as U.
          replace (free_array_of sb c + 4 * (nf - k) + 4 * Z.of_nat i) with (free_array_of sb c + 4 * Z.of_nat (length fr - Z.to_nat k + i)) by lia. exact U.
        * rewrite FAR. unfold kFreeArrayOffset, kHighMemBeg in *. lia.
        * rewrite length_skipn, FAR. unfold kRegionSize, kFreeArrayOffset, kSpaceSize in *. lia.
      + rewrite ref_ws_len. apply mapped_wr_at; [| rewrite FAR; unfold kFreeArrayOffset, kHighMemBeg in *; lia| rewrite FAR; unfold kRegionSize, kFreeArrayOffset, kSpaceSize in *; lia].
        intros i Hi. replace (free_array_of sb c + 4 * (nf - k) + i) with (free_array_of sb c + (4 * (nf - k) + i)) by lia. apply MFA. lia.
  Qed.
End Refill.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ChunkF.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (n kidx : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Let v := aview_of (pa_hull A) m.
  Local Notation c := (class_of n).
  Hypothesis KIN : In kidx (rg_free (a_reg A (class_of n))).
  Local Notation AB := (chunk_addr (a_sb A) (class_of n) kidx).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Ltac glia := unfold region_beg, kRegionSize, kHighMemBeg, kMaxSize, kShadowOffset in *; change (2^32)%Z with 4294967296%Z in *;
               change (2^37)%Z with 137438953472%Z in *; lia.
  #[using="W KIN NR AI md m DR Clg"] Lemma free_KB : 0 <= kidx < carved_count A c.
  Proof.
    (first [ pose proof ((wfR A W)) as dR_22; dand3 dR_22 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c (proj1 (hit_class n NR)))) as dR_23; dand10 dR_23 as _ _ _ _ _ _ _ _ B _ | destruct (WR c (proj1 (hit_class n NR))) as (_ & _ & _ & _ & _ & _ & _ & _ & B & _) ]).
    unfold carved_count, carved_count_. exact (B _ KIN).
  Qed.

  #[using="W KIN NR AI md m DR"] Lemma free_geom :
    AB = a_sb A + c * 2^32 + 16 * (kidx * class_size c / kCompactPtrScale) /\ AB mod 32 = 0 /\ AB = 8 * (AB / 8) /\
    a_sb A <= AB /\ AB + class_size c <= a_sb A + 2^37 /\ rz_size n = 8 * (rz_size n / 8) /\
    kHighMemBeg <= a_sb A /\ a_sb A + 2^37 <= alloc_ceiling /\
    region_beg (a_sb A) c <= AB /\ AB + class_size c <= region_beg (a_sb A) c + rg_mapped_user (a_reg A c) /\
    rz_size n + n <= class_size c /\ needed_size n <= class_size c /\ 1 <= c <= 30 /\ 0 <= kidx < carved_count A c /\
    0 <= kidx * class_size c / kCompactPtrScale < 2^32 /\ AB + class_size c <= a_sb A + c * 2^32 + 3758096384.
  Proof.
    (first [ pose proof ((hit_class n NR)) as dR_24; dand5 dR_24 as CR HC FIT CSR M32 | destruct (hit_class n NR) as (CR & HC & FIT & CSR & M32) ]). pose proof free_KB as KB.
    (first [ pose proof ((carved_chunk_bounds A c kidx W CR KB)) as dR_25; dand4 dR_25 as B1 B2 B3 _ | pose proof (carved_chunk_bounds A c kidx W CR KB) as (B1 & B2 & B3 & _) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
    (first [ pose proof ((sb_facts A W)) as dR_26; dand5 dR_26 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]). pose proof alloc_ceiling_val as CE.
    pose proof (rz_size_range n) as RZR. pose proof (rounded_size_ge n) as RG.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (SM : 0 <= kidx * class_size c / kCompactPtrScale < 2^32).
    { unfold chunk_addr, kCompactPtrScale, kFreeArrayOffset in *. split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. clear - KB B1 B2 B3 RB CR; nia. }
    assert (M16 : (kidx * class_size c) mod 16 = 0).
    { apply (mod0_down _ 32 16); [exists 2; reflexivity|]. rewrite Z.mul_mod, M32, Z.mul_0_r by lia. reflexivity. }
    pose proof (Z_div_exact_full_2 (kidx * class_size c) 16 ltac:(lia) M16) as E16.
    pose proof (Z_div_mod_eq_full AB 8). pose proof (mod0_down AB 32 8 ltac:(exists 4; reflexivity) B3).
    pose proof (Z_div_mod_eq_full (rz_size n) 8). pose proof (mod0_down (rz_size n) 16 8 ltac:(exists 2; reflexivity) (rz_size_mod16 n)).
    unfold chunk_addr, region_beg, kCompactPtrScale, kRegionSize, kSpaceSize, kFreeArrayOffset, kHighMemBeg in *.
    change (2^32)%Z with 4294967296%Z in *. change (2^37)%Z with 137438953472%Z in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try assumption.
  Qed.
  Let RM : mapped v (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c)).
  Proof. (first [ dand14 free_geom as _ _ _ _ _ _ _ _ _ _ _ _ CR _ | destruct free_geom as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _) ]). pose proof (ar_regions _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) c CR) as R. unfold region_repr_ in R. cbv zeta in R. tauto. Qed.
  Let CM : forall a j, region_beg (a_sb A) c <= a -> a + j <= region_beg (a_sb A) c + rg_mapped_user (a_reg A c) -> mapped v a j.
  Proof. intros a j H1 H2 i Hi. replace (a + i) with (region_beg (a_sb A) c + (a - region_beg (a_sb A) c + i)) by lia. apply RM. lia. Qed.

  #[using="CM RM W KIN NR AI md DR"] Lemma free_HDR : exists (b0 b1 : byte) (h2 w4 d8 : word), rw_cells rsegs v (AB + rz_size n + -16) [C1 b0; C1 b1; C2 h2; C4 w4; C8 d8].
  Proof.
    (first [ dand14 free_geom as _ _ _ _ U1 _ HB U2 R1 R2 FIT _ CR _ | destruct free_geom as (_ & _ & _ & _ & U1 & _ & HB & U2 & R1 & R2 & FIT & _ & CR & _) ]). pose proof alloc_ceiling_val as CE. pose proof (rz_size_range n).
    set (a := AB + rz_size n + -16).
    assert (M16 : mapped v a 16) by (apply CM; subst a; glia).
    pose proof (rdbytes_bytes_at v a 16 M16 ltac:(subst a; glia) ltac:(subst a; glia)) as B.
    set (bs := rdbytes v a 16) in B.
    assert (L : length bs = 16%nat) by (subst bs; apply rdbytes_length).
    exists (nth 0 bs (Z_to_bv 8 0)), (nth 1 bs (Z_to_bv 8 0)), (le_bytes_to_word (firstn 2 (skipn 2 bs))), (le_bytes_to_word (firstn 4 (skipn 4 bs))),
           (le_bytes_to_word (skipn 8 bs)).
    apply ro_rw; [| exact M16]. split; [exact (conj I (conj I (conj I (conj I (conj I I)))))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite le2_of_bytes by (rewrite firstn_length, skipn_length; lia). rewrite le4_of_bytes by (rewrite firstn_length, skipn_length; lia).
    rewrite le8_of_bytes by (rewrite skipn_length; lia).
    apply (bytes_at_as v _ _ _ B). destruct bs as [|x0 [|x1 bs']]; cbn in L; try lia. cbn [nth skipn app].
    f_equal. f_equal. rewrite <- (firstn_skipn 2 bs') at 1. f_equal. rewrite <- (firstn_skipn 4 (skipn 2 bs')) at 1. rewrite skipn_skipn. f_equal.
  Qed.
  #[using="CM RM W KIN NR AI md DR"] Lemma free_ABH : exists (j0 j1 : word), rw_cells rsegs v AB [C8 j0; C8 j1].
  Proof.
    (first [ dand14 free_geom as _ _ _ _ U1 _ HB U2 R1 R2 FIT _ CR _ | destruct free_geom as (_ & _ & _ & _ & U1 & _ & HB & U2 & R1 & R2 & FIT & _ & CR & _) ]). pose proof alloc_ceiling_val as CE. (first [ pose proof ((hit_class n NR)) as dR_30; dand5 dR_30 as _ _ _ CSR _ | destruct (hit_class n NR) as (_ & _ & _ & CSR & _) ]).
    assert (M16 : mapped v AB 16) by (apply CM; glia).
    pose proof (rdbytes_bytes_at v AB 16 M16 ltac:(glia) ltac:(glia)) as B.
    set (bs := rdbytes v AB 16) in B. assert (L : length bs = 16%nat) by (subst bs; apply rdbytes_length).
    exists (le_bytes_to_word (firstn 8 bs)), (le_bytes_to_word (skipn 8 bs)).
    apply ro_rw; [| exact M16]. split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite !le8_of_bytes by (rewrite ?firstn_length, ?skipn_length; lia). rewrite firstn_skipn. exact B.
  Qed.
  #[using="CM RM W KIN NR AI md DR"] Lemma free_USR : exists uj, rw_cells rsegs v (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj].
  Proof.
    (first [ dand14 free_geom as _ _ _ _ U1 _ HB U2 R1 R2 FIT _ CR _ | destruct free_geom as (_ & _ & _ & _ & U1 & _ & HB & U2 & R1 & R2 & FIT & _ & CR & _) ]). pose proof alloc_ceiling_val as CE. pose proof (rz_size_range n).
    assert (MU : mapped v (AB + rz_size n) (Z.min n 4096)) by (apply CM; lia).
    exists (rdbytes v (AB + rz_size n) (Z.to_nat (Z.min n 4096))).
    apply ro_rw; [| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact MU].
    split; [cbn; rewrite rdbytes_length; exact (conj eq_refl I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply rdbytes_bytes_at; [rewrite Z2Nat.id by lia; exact MU| glia|].
    rewrite Z2Nat.id by lia. glia.
  Qed.
  (* [comment removed for export] *)
  #[using="W KIN NR AI md DR"] Lemma free_shadow : bytes_at rsegs v (sh AB) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (class_size c / 8))).
  Proof.
    (first [ dand14 free_geom as _ _ _ _ _ _ _ _ _ _ _ _ CR _ | destruct free_geom as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _) ]).
    pose proof (ar_shadow _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as S. destruct S as (S1 & _).
    exact (S1 c kidx CR (or_introl KIN)).
  Qed.
  #[using="W KIN NR AI md DR"] Lemma free_SH : forall d e, n = 8 * d + e -> 0 <= e < 8 -> exists olds oldp,
    ro_cells rsegs v (AB / 8 + kShadowOffset) [C1 (Z_to_bv 8 kAsanHeapLeftRedzoneMagic)] /\
    u8arr rsegs v (AB / 8 + rz_size n / 8 + kShadowOffset) olds /\ length olds = Z.to_nat d /\
    (e <> 0 -> rw_cells rsegs v (AB / 8 + rz_size n / 8 + d + kShadowOffset) [C1 oldp]).
  Proof.
    intros d e NDE ER. pose proof free_shadow as S. pose proof alloc_ceiling_val as CE. (first [ dand14 free_geom as _ _ Q8 _ U1 R8 HB U2 R1 R2 FIT _ CR _ | destruct free_geom as (_ & _ & Q8 & _ & U1 & R8 & HB & U2 & R1 & R2 & FIT & _ & CR & _) ]).
    (first [ pose proof ((hit_class n NR)) as dR_34; dand5 dR_34 as _ _ _ CSR M32 | destruct (hit_class n NR) as (_ & _ & _ & CSR & M32) ]). pose proof (rz_size_range n) as RZR.
    pose proof (Z_div_mod_eq_full (class_size c) 8) as C8E. pose proof (mod0_down (class_size c) 32 8 ltac:(exists 4; reflexivity) M32) as C8M.
    assert (SHB : sh AB = AB / 8 + kShadowOffset) by reflexivity.
    assert (HI : 0x60a000 <= sh AB).
    { rewrite SHB. unfold kShadowOffset. pose proof (Z.div_le_mono 0x10007fff8000 AB 8 ltac:(lia) ltac:(glia)) as DL.
      change (0x10007fff8000 / 8) with 0x2000ffff000 in DL. lia. }
    pose proof (bytes_at_mapped_high v (sh AB) _ S HI) as SM. rewrite repeat_length, Z2Nat.id in SM by lia.
    set (fa := Z_to_bv 8 kAsanHeapLeftRedzoneMagic) in *.
    assert (PIECE : forall i j, 0 <= i -> 0 <= j -> i + j <= class_size c / 8 -> bytes_at rsegs v (sh AB + i) (repeat fa (Z.to_nat j))).
    { intros i j Hi Hj Hij. replace (sh AB + i) with (sh AB + Z.of_nat (Z.to_nat i)) by lia.
      rewrite <- (repeat_mid fa (Z.to_nat (class_size c / 8)) (Z.to_nat i) (Z.to_nat j)) by lia.
      apply bytes_at_mid; [exact S| rewrite repeat_length; lia]. }
    exists (repeat fa (Z.to_nat d)), fa. split; [|split; [|split]].
    - rewrite <- SHB. apply bytes_ro_C1. replace (sh AB) with (sh AB + 0) by lia. apply (PIECE 0 1); lia.
    - split.
      + replace (AB / 8 + rz_size n / 8 + kShadowOffset) with (sh AB + rz_size n / 8) by (rewrite SHB; lia). apply PIECE; lia.
      + rewrite repeat_length, Z2Nat.id by lia. apply mapped_wr_at; [| rewrite SHB in HI; lia| glia].
        intros i Hi. replace (AB / 8 + rz_size n / 8 + kShadowOffset + i) with (sh AB + (rz_size n / 8 + i)) by (rewrite SHB; lia). apply SM. lia.
    - apply repeat_length.
    - intros NE0. apply ro_rw.
      + apply bytes_ro_C1. replace (AB / 8 + rz_size n / 8 + d + kShadowOffset) with (sh AB + (rz_size n / 8 + d)) by (rewrite SHB; lia).
        apply (PIECE (rz_size n / 8 + d) 1); lia.
      + cbn. intros i Hi. replace (AB / 8 + rz_size n / 8 + d + kShadowOffset + i) with (sh AB + (rz_size n / 8 + d + i)) by (rewrite SHB; lia). apply SM. lia.
  Qed.
End ChunkF.
