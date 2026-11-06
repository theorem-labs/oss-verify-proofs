(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS ITree Nodes Decode SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio Malloc Prog MEX_defs MEX_iface MEX_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_SiteM0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Sites.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocBlocks Malloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree F_pad Exit Printf_model F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_syscalls F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_base Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_hdr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_hdr.Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_die.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac lia ::= first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma firstn_add_skipn : forall {X} (l : list X) n k, firstn (n + k) l = firstn n l ++ firstn k (skipn n l).
Proof.
  intros X l n. revert l. induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma firstn_app_read : forall {X} (data : list X) (len n want : nat),
  n = length (firstn want (skipn len data)) ->
  firstn len data ++ firstn want (skipn len data) = firstn (len + n) data.
Proof.
  intros X data len n want ->. rewrite firstn_add_skipn. f_equal.
  rewrite length_firstn. rewrite Nat.min_comm. symmetry.
  destruct (Nat.le_gt_cases want (length (skipn len data))).
  - rewrite Nat.min_r by lia. reflexivity.
  - rewrite Nat.min_l by lia. rewrite !firstn_all2 by lia. reflexivity.
Qed.

Lemma pow2_ge1 : forall k : nat, 1 <= 2 ^ Z.of_nat k.
Proof. intros k. pose proof (Z.pow_le_mono_r 2 0 (Z.of_nat k) ltac:(lia) ltac:(lia)) as H. change (2 ^ 0) with 1 in H. exact H. Qed.

Section S.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_OOM : so_diag_oom_stmt.
  Hypothesis SO_REFUSED : so_diag_refused_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.

  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid ra0 : word)
            (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (q8 q9 q10 q11 : word).
  Hypothesis TP : tp = wz PTP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis GT : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 0x800000000000.
  Hypothesis SPBE : SPB = bv_unsigned sp + 128.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.
  Hypothesis FRM : frm0 fc.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) path.
  Hypothesis SLK : (- (P1 + zlength path + 1)) mod 8 <= zlength slack.
  Hypothesis LEN : zlength path <= 131071.
  Hypothesis PUS : bv_unsigned sp + 128 <= P1.

  Notation INV := (loop_inv sp fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7).
  Notation REGS := (loop_regs sp gp tp F fc P1 q8 q9 q10 q11).

  (* [comment removed for export] *)
  Definition HEAD_OK (bound : Z) : Prop :=
    forall len cap A cs p d junk m mo ms,
      INV len cap A cs p d junk m mo -> len < cap -> REGS len cap A m 0x12218 ms -> zlength data - len < bound ->
      realizes psegs (mkCfg ms mo) (Kloop data fs cap).

  Hypothesis POST : post_stmt sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.

  Lemma head_ok_mono : forall b b', HEAD_OK b -> b' <= b -> HEAD_OK b'.
  Proof. intros b b' H LE len cap A cs p d junk m mo ms IV LT RG LT'. apply (H len cap A cs p d junk m mo ms IV LT RG). lia. Qed.

  Lemma cap_next : forall (cap : Z) (k : nat), cap = 65536 * 2 ^ Z.of_nat k -> cap < 2 ^ 26 -> cap * 2 <= 2 ^ 26 /\ cap * 2 = 65536 * 2 ^ Z.of_nat (S k).
  Proof.
    intros cap k -> LT. split.
    - destruct (Z_lt_dec (Z.of_nat k) 10).
      + pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 9 ltac:(lia) ltac:(lia)). cbn in *. lia.
      + pose proof (Z.pow_le_mono_r 2 10 (Z.of_nat k) ltac:(lia) ltac:(lia)). cbn in *. lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_grow : forall (cap A : Z) cs p d junk m mo (b : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      INV cap cap A cs p d junk m mo -> HEAD_OK b -> zlength data - cap < b ->
      realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz cap) (wz 3) (wz cap) (wz PRS) (wz A) q8 q9 q10 q11 t3 t4 t5 t6)
                                F (wz 0x121e0) fc None m (seg_rom psegs)) mo)
               (Kloop data fs cap).
  Proof.
    intros until t6. intros IV IH IHb.
    (nelim IV 21%nat; intros ST MI FR DS CJ [e ER] IFL SOF SEF BY DH RP PD DM FL BLK [stj RSC] [k CAP] LEN1 LEN2 CAP2).
    pose proof RSN_Z as HRSN. pose proof PRS_eq as HPRS.
    pose proof DM as [MOK' MFDS HFS].
    pose proof (dheap_block_range _ _ _ _ _ (p, A, cap) DH ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    (nelimp BR 5%nat; intros BR1 BR2 BR3 BR4 BR5). unfold alloc_ceiling in BR4.
    pose proof (pow2_ge1 k) as K2.   (* [comment removed for export] *)
    assert (BR6 : 0x55000 <= A) by (destruct BR5; lia). clear BR5.   (* [comment removed for export] *)
    unfold wz in *. unfold PERRNO in ER. unfold PINITFLAG in IFL.
    eapply rz_step_evt; [exact MOK'|].
    do 2 step. if_cases K; zify_cond K; rewrite Z.shiftr_div_pow2 in K by lia.
    - (* [comment removed for export] *)
      assert (CAPB : 2 ^ 26 <= cap) by (apply Z.nlt_ge; intros Hlt; apply K; apply Z.div_small; lia).
      apply evt_done.
      replace (Kloop data fs cap) with (t_die msg_refused fs).
      2:{ unfold Kloop.
          unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT, zlength in *; lia). reflexivity. }
      (nelim (dheap_libc_cells _ _ _ _ _ DH) 5%nat; intros cdt thr sec tm1 LC).
      eapply die_refused with (lo := lo) (tid := tid) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1) (guard := ssp_guard_val);
        first [exact SO_EXIT| exact SO_REFUSED| exact DM| right; eexists; reflexivity| exact TP| exact TID| exact FRM
              | split; [exact ST| split; [exact MI| split; [exact DS| split; [exact LC| split; [eapply dheap_ssp0; exact DH| split; [exact SOF| exact SEF]]]]]]
              | unfold GLOBALS_TOP; lia ].
    - (* [comment removed for export] *)
      assert (CAPB : cap < 2 ^ 26) by (destruct (Z_lt_dec cap (2 ^ 26)) as [Hl|Hl]; [exact Hl|]; exfalso; pose proof (Z.div_str_pos cap (2 ^ 26) ltac:(lia)); lia).
      destruct (cap_next cap k CAP CAPB) as [CAP2' CAPS].
      do 3 step. apply evt_done.
      rewrite (unsigned_lit cap) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      (nelim (rp1_RP _ _ RP) 3%nat; intros fl lo1 HRP).
      pose proof (big_site _ _ _ _ (cap * 2) HRP ltac:(unfold MMAP_THRESHOLD; lia)) as SITE. unfold MEX_iface.big_site in SITE.
      pose proof (rp_bounds_small rp_bounds _ _ _ _ HRP) as SMALL.
      (* [comment removed for export] *)
      change (Kloop data fs cap) with (Kloop data fs (cap * 2)).
      eapply (drv_malloc_site _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo cs [(p, A, cap)] SPB (cap * 2) lo (cap * 2 + 20) (cap * 2 + 20) e);
        first [exact DH| exact SITE| exact SMALL| exact ST| exact ER| exact MI| exact TP| reflexivity
              | unfold CJ_iface.RMALLOC_STACK; lia | idtac].
      + (* [comment removed for export] *)
        intros ms2 mo2 m2 errv2 cs' c' off' A' junk' RPO VO MI2 ST2 ER2 PR BR' NIN BLK' DH2 LEAF.
        (nelim RPO 15%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ->).
        replace (ret_pc (Z_to_bv 64 0x121f4)) with (Z_to_bv 64 0x121f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (dheap_mok _ _ _ _ _ DH2) as MOK2. (nelimp BR' 5%nat; intros BQ1 BQ2 BQ3 BQ4 BQ5). unfold alloc_ceiling in BQ4.
        assert (BQ6 : 0x55000 <= A') by (destruct BQ5; lia). clear BQ5.   (* [comment removed for export] *)
        cbn [map bview blk_addr blk_size fst snd] in PR. cbn [map blk_addr fst snd] in NIN.
        assert (NE : A' <> A) by (intros E; apply NIN; left; symmetry; exact E). clear NIN.
        destruct LEAF as [ans LEAF].
        pose proof (big_follow cs d (cap * 2) ans cs' (Some c') RP ltac:(unfold MMAP_THRESHOLD; lia) LEAF) as BF.
        cbv beta iota in BF. (nelim BF 4%nat; intros dnew RP2' Ec' _). clear LEAF ans.
        (* [comment removed for export] *)
        assert (BLKo : rw_cells psegs m2 A [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)]).
        { pose proof (proj1 (proj1 (rw_cells_app psegs m A [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)] _) BLK)) as B1.
          eapply cj_pres_rw_cells; [exact PR| exact B1| right; right; exists A, cap; split; [left; reflexivity| cbn; lia]]. }
        pose proof BLK' as BLKn.
        eapply (rw_cells_split_CB psegs m2 A' [] (Z.to_nat (cap * 2)) junk' [] [Z.to_nat cap; Z.to_nat cap]) in BLKn; [| cbn; lia]. cbn [mk_CB_cells app] in BLKn.
        pose proof (proj1 (rw_cells_app psegs m2 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk')] _) BLKn) as [BLKn1 BLKn2].
        replace (A' + Z.of_nat (cells_size [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk')])) with (A' + cap) in BLKn2 by (cbn; lia). clear BLKn.
        pose proof (dheap_blocks_disjoint _ _ _ _ _ A' (cap * 2) A cap DH2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) NE) as DISJ.
        (* [comment removed for export] *)
        eapply rz_step_evt; [exact MOK2|]. unfold wz.
        step. if_cases K'; zify_cond K'; [exfalso; lia|]. clear K'.
        step. step. if_cases K'; zify_cond K'; [exfalso; lia|]. clear K'.
        do 4 step.
        assert (LSRC : length (firstn (Z.to_nat cap) data) = Z.to_nat cap) by (rewrite length_firstn; unfold zlength in *; lia).
        eapply evt_cut.
        { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (firstn (Z.to_nat cap) data) (firstn (Z.to_nat cap) junk'));
            rewrite ?unsigned_lit by lia; [| exact LSRC| exact BLKn1| lia| exact MI2].
          exact (proj1 (rw_cells_CB_bytes _ _ _ _ BLKo)). }
        intros ms3 nelH_; (nelim nelH_ 21%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m3 -> MU3 WM3 MI3 DST3 SRC3).
        rewrite ?unsigned_lit in MU3 by lia. rewrite ?unsigned_lit in DST3 by lia. rewrite ?unsigned_lit in SRC3 by lia.
        replace (ret_pc (Z_to_bv 64 0x12210)) with (Z_to_bv 64 0x12210) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold zlength in *. rewrite ?unsigned_lit in MU3 by lia. rewrite ?unsigned_lit in DST3 by lia.
        (* [comment removed for export] *)
        pose proof (stk_transport_disjoint psegs _ _ _ _ _ ST2 MU3 WM3 ltac:(cbn; lia)) as ST3.
        xport ER2 MU3 WM3 ER3. xport BLKn2 MU3 WM3 BLKn3.
        assert (DH3 : DHEAP cs' [(c', off', A', cap * 2); (p, A, cap)] SPB m3 mo2).
        { eapply dheap_frame_ext; [exact DH2| exact MU3| exact WM3|].
          solve_Forall ltac:(right; right; right; right; exists A', (cap * 2); split; [left; reflexivity| cbn [fst snd]; lia]). }
        (* [comment removed for export] *)
        do 2 step. apply evt_done.
        eapply (drv_free _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mo2 cs' [(c', off', A', cap * 2); (p, A, cap)] SPB p A cap lo errv2);
          first [exact DH3| right; left; reflexivity| exact ST3| exact ER3| exact MI3| exact TP| reflexivity
                | unfold CJ_iface.RMALLOC_STACK; lia | idtac].
        intros ms4 mo4 m4 cs4 a04 RPO4 VO4 MI4 ST4 ER4 PR4 DH4 FL4.
        rewrite (dheap_remove_old _ _ _ _ _ _ _ _ _ _ DH3) in PR4, DH4.
        (nelim RPO4 15%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 ->).
        replace (ret_pc (Z_to_bv 64 0x12218)) with (Z_to_bv 64 0x12218) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (dheap_mok _ _ _ _ _ DH4) as MOK4.
        cbn [map bview blk_addr blk_size fst snd] in PR4.
        (* [comment removed for export] *)
        destruct FL4 as [ans4 FL4]. rewrite PD in FL4.
        pose proof (free_follow cs' d dnew ans4 cs4 RP2' FL4) as RP4.
        (* [comment removed for export] *)
        assert (FR4 : rw_cells psegs m4 (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)).
        { assert (FR2 : rw_cells psegs m2 (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0))
            by (eapply cj_pres_rw_cells; [exact PR| exact FR| left; unfold mframe; cbn; lia]).
          xport FR2 MU3 WM3 FR3. eapply cj_pres_rw_cells; [exact PR4| exact FR3| left; unfold mframe; cbn; lia]. }
        assert (RSC4 : rw_cells psegs m4 PRS [CB RSN stj]).
        { assert (RSC2 : rw_cells psegs m2 PRS [CB RSN stj])
            by (eapply cj_pres_rw_cells; [exact PR| exact RSC| right; left; unfold PRS, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; pose proof RSN_Z; cbn; lia]).
          xport RSC2 MU3 WM3 RSC3.
          eapply cj_pres_rw_cells; [exact PR4| exact RSC3| right; left; unfold PRS, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; pose proof RSN_Z; cbn; lia]. }
        assert (DS4 : DSTAT false tid m4).
        { pose proof (DSTAT_cj_pres _ _ _ _ _ _ DS PR) as DS2. xport DS2 MU3 WM3 DS3. eapply DSTAT_cj_pres; [exact DS3| exact PR4]. }
        assert (CJ4 : CJST m4).
        { pose proof (CJST_pres _ _ _ _ PR CJ) as CJ2. xport CJ2 MU3 WM3 CJ3. eapply CJST_pres; [exact PR4| exact CJ3]. }
        assert (IFL4 : rw_cells psegs m4 PINITFLAG [C1 (Z_to_bv 8 0)]).
        { assert (IFL2 : rw_cells psegs m2 PINITFLAG [C1 (Z_to_bv 8 0)])
            by (unfold PINITFLAG; eapply cj_pres_rw_cells; [exact PR| exact IFL| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia]).
          xport IFL2 MU3 WM3 IFL3. unfold PINITFLAG in *.
          eapply cj_pres_rw_cells; [exact PR4| exact IFL3| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia]. }
        assert (SOF4 : stdout_file m4 stdout_init).
        { pose proof (stdout_file_cj_pres _ _ _ _ _ SOF PR) as SOF2. xport SOF2 MU3 WM3 SOF3. eapply stdout_file_cj_pres; [exact SOF3| exact PR4]. }
        assert (SEF4 : stderr_wfile0 m4).
        { pose proof (stderr_wfile0_cj_pres _ _ _ _ SEF PR) as SEF2. xport SEF2 MU3 WM3 SEF3. eapply stderr_wfile0_cj_pres; [exact SEF3| exact PR4]. }
        assert (BY4 : bytes_at psegs m4 P1 (path ++ Z_to_bv 8 0 :: slack)).
        { pose proof (cj_pres_bytes_at _ _ _ _ _ _ PR BY ltac:(left; lia)) as BY2. xport BY2 MU3 WM3 BY3.
          eapply cj_pres_bytes_at; [exact PR4| exact BY3| left; lia]. }
        assert (BLK4 : rw_cells psegs m4 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat (cap * 2 - cap)) (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk'))]).
        { eapply cj_pres_rw_cells; [exact PR4| | right; right; exists A', (cap * 2); split; [left; reflexivity| cbn; lia]].
          apply (proj2 (rw_cells_app psegs m3 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)] _)). split; [exact DST3|].
          cbn [cells_size csize Nat.add]. replace (A' + Z.of_nat (Z.to_nat cap + 0)) with (A' + cap) by lia.
          replace (Z.to_nat (cap * 2 - cap)) with (Z.to_nat cap) by lia. exact BLKn3. }
        assert (DM4 : DMOD fs (FDS3 (FdFile path (Z_to_bv 64 cap))) mo4).
        { eapply DMOD_vm_only; [| exact VO4| exact MOK4]. eapply DMOD_vm_only; [exact DM| exact VO| exact MOK2]. }
        assert (IV4 : INV cap (cap * 2) A' cs4 (c', off') dnew (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk')) m4 mo4).
        { split; [exact ST4|]. split; [exact MI4|]. split; [exact FR4|]. split; [exact DS4|]. split; [exact CJ4|]. split; [exists errv2; exact ER4|]. split; [exact IFL4|].
          split; [exact SOF4|]. split; [exact SEF4|]. split; [exact BY4|]. split; [exact DH4|]. split; [exact RP4|]. split; [cbn [fst]; exact Ec'|]. split; [exact DM4|]. split; [exact FL|].
          split; [exact BLK4|]. split; [exists stj; exact RSC4|]. split; [exists (S k); exact CAPS|]. unfold zlength in *. lia. }
        clear FR4 DS4 CJ4 IFL4 SOF4 SEF4 BY4 BLK4 RSC4 DH3 PR4 PR.
        (* [comment removed for export] *)
        eapply (IH cap (cap * 2) A' cs4 (c', off') dnew _ m4 mo4 _ IV4); [lia| | unfold zlength in *; lia].
        unfold loop_regs. unfold wz. nexists 17%nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_read : forall (len cap A : Z) cs p d junk m mo (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (want : Z),
      INV len cap A cs p d junk m mo -> HEAD_OK (zlength data - len) ->
      len < cap -> want = Z.min (cap - len) 65536 ->
      realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 (wz want) a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz PRS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
                                F (wz 0x12228) fc None m (seg_rom psegs)) mo)
               (Kloop data fs cap).
  Proof.
    intros until want. intros IV IH LT WANT.
    (nelim IV 21%nat; intros ST MI FR DS CJ [e ER] IFL SOF SEF BY DH RP PD DM FL BLK [stj RSC] [k CAP] LEN1 LEN2 CAP2).
    pose proof RSN_Z as HRSN. pose proof PRS_eq as HPRS.
    pose proof DM as [MOK' MFDS HFS].
    pose proof (dheap_block_range _ _ _ _ _ (p, A, cap) DH ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    (nelimp BR 5%nat; intros BR1 BR2 BR3 BR4 BR5). unfold alloc_ceiling in BR4.
    pose proof (pow2_ge1 k) as K2.   (* [comment removed for export] *)
    assert (BR6 : 0x55000 <= A) by (destruct BR5; lia). clear BR5.   (* [comment removed for export] *)
    unfold wz in *. unfold PERRNO in ER. unfold PINITFLAG in IFL.
    (* [comment removed for export] *)
    assert (RSCs : rw_cells psegs m PRS [CB (Z.to_nat want) (firstn (Z.to_nat want) stj); CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))]).
    { eapply (rw_cells_split_CB psegs m PRS [] RSN stj [] [Z.to_nat want; Z.to_nat (65536 - want)]) in RSC; [| pose proof RSN_Z; cbn [sum_nat]; lia].
      cbn [mk_CB_cells app] in RSC. exact RSC. }
    pose proof (proj1 (rw_cells_app psegs m PRS [CB (Z.to_nat want) (firstn (Z.to_nat want) stj)] _) RSCs) as [RSCa RSCb].
    replace (PRS + Z.of_nat (cells_size [CB (Z.to_nat want) (firstn (Z.to_nat want) stj)])) with (PRS + want) in RSCb by (pose proof RSN_Z; cbn; lia).
    clear RSCs.
    eapply rz_step_evt; [exact MOK'|].
    do 3 step. apply evt_done.
    eapply (rz_impl_read_file psegs _ _ mo 3 (bv_unsigned (Z_to_bv 64 PRS)) want path (Z_to_bv 64 len) data);
      [exact MOK'| | rewrite MFDS; reflexivity| rewrite HFS; exact FL| rewrite rw_bytes_max_val; lia| rewrite unsigned_lit by lia; rewrite TASK_SIZE_val; unfold PRS; lia|].
    { eapply read_spec with (lo := lo) (junk := firstn (Z.to_nat want) stj) (errv := e);
      first [ exact ST | exact MI
            | lazymatch goal with |- _ = _ => reflexivity end
            | rewrite ?(errno_addr_tp tp TP); rewrite ?TP; unfold PERRNO, PTP, PRS; rewrite ?unsigned_lit by lia; first [exact RSCa| exact ER| lia] ]. }
    cbv zeta. intros ms2 PO.
    (nelim PO 23%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 RSC2 ER2 Hn).
    cbn [read_ret] in *. rewrite (errno_addr_tp tp TP) in MU2, ER2. rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in RSC2 by lia.
    set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)) in *.
    replace (ret_pc (Z_to_bv 64 0x12234)) with (Z_to_bv 64 0x12234) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite MFDS, FDS3_insert.
    assert (LBS : Z.of_nat (length bs) = Z.min want (zlength data - len)).
    { subst bs. rewrite length_file_read. unfold word_to_nat. unfold zlength in *. rewrite !unsigned_lit by lia. lia. }
    set (n := Z.of_nat (length bs)) in *.
    assert (Hn' : 0 <= n <= want) by lia.
    assert (BS : firstn (Z.to_nat len) data ++ bs = firstn (Z.to_nat (len + n)) data).
    { subst bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia.
      replace (Z.to_nat (len + n)) with (Z.to_nat len + Z.to_nat n)%nat by lia. apply firstn_app_read.
      subst n. rewrite Nat2Z.id. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    xport FR MU2 WM2 FR2. xport DS MU2 WM2 DS2. xport CJ MU2 WM2 CJ2. xport IFL MU2 WM2 IFL2. xport SOF MU2 WM2 SOF2. xport SEF MU2 WM2 SEF2. xport BY MU2 WM2 BY2.
    xport BLK MU2 WM2 BLK2. xport RSCb MU2 WM2 RSCb2.
    assert (DH2 : DHEAP cs [(p, A, cap)] SPB m2 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
    { apply (dheap_model cs _ SPB m2 mo); [| reflexivity| destruct MOK' as [Hh _]; exact Hh].
      eapply dheap_frame_ext; [exact DH| exact MU2| exact WM2|].
      solve_Forall ltac:(first [drv_write_ok_tac| unfold PRS; drv_write_ok_tac]). }
    assert (DM2 : DMOD fs (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
    { eapply DMOD_with_fds. exact DM. }
    pose proof (dheap_mok _ _ _ _ _ DH2) as MOK2.
    (* [comment removed for export] *)
    eapply rz_step_evt; [exact MOK2|].
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 2 step.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NPOS : 0 < n) by (rewrite ?unsigned_lit in K by lia; lia). clear K.
      (* [comment removed for export] *)
      pose proof BLK2 as BLK0.
      eapply (rw_cells_split_CB psegs m2 A [CB (Z.to_nat len) (firstn (Z.to_nat len) data)] (Z.to_nat (cap - len)) junk [] [Z.to_nat n; Z.to_nat (cap - len - n)]) in BLK2; [| cbn; lia].
      cbn [mk_CB_cells app] in BLK2.
      pose proof (proj1 (rw_cells_app psegs m2 A [CB (Z.to_nat len) (firstn (Z.to_nat len) data)] _) BLK2) as [BLKa BLKbc].
      pose proof (proj1 (rw_cells_app psegs m2 _ [CB (Z.to_nat n) (firstn (Z.to_nat n) junk)] _) BLKbc) as [BLKb BLKc].
      replace (A + Z.of_nat (cells_size [CB (Z.to_nat len) (firstn (Z.to_nat len) data)])) with (A + len) in BLKb, BLKc by (cbn; lia).
      replace (A + len + Z.of_nat (cells_size [CB (Z.to_nat n) (firstn (Z.to_nat n) junk)])) with (A + len + n) in BLKc by (cbn; lia).
      clear BLK2 BLKbc.
      (* [comment removed for export] *)
      pose proof (proj1 (rw_cells_app psegs m2 PRS [CB (length bs) bs] _) RSC2) as [RSC2a RSC2b].
      replace (PRS + Z.of_nat (cells_size [CB (length bs) bs])) with (PRS + n) in RSC2b by (pose proof RSN_Z; cbn; lia).
      do 4 step.   (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 bs (firstn (Z.to_nat n) junk));
          rewrite ?unsigned_lit by lia; [| lia| exact BLKb| lia| exact MI2].
        exact (proj1 (rw_cells_CB_bytes _ _ _ _ RSC2a)). }
      intros ms3 nelH_; (nelim nelH_ 21%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m3 -> MU3 WM3 MI3 DST3 SRC3).
      rewrite ?unsigned_lit in MU3 by lia. rewrite ?unsigned_lit in DST3 by lia. rewrite ?unsigned_lit in SRC3 by lia.
      replace (ret_pc (Z_to_bv 64 0x121cc)) with (Z_to_bv 64 0x121cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      pose proof (stk_transport_disjoint psegs _ _ _ _ _ ST2 MU3 WM3 ltac:(cbn; lia)) as ST3.
      xport FR2 MU3 WM3 FR3. xport DS2 MU3 WM3 DS3. xport CJ2 MU3 WM3 CJ3. xport IFL2 MU3 WM3 IFL3. xport SOF2 MU3 WM3 SOF3. xport SEF2 MU3 WM3 SEF3.
      xport BY2 MU3 WM3 BY3. xport ER2 MU3 WM3 ER3. xport BLKa MU3 WM3 BLKa3. xport BLKc MU3 WM3 BLKc3.
      xport RSC2b MU3 WM3 RSC2b3. xport RSCb2 MU3 WM3 RSCb3.
      pose proof (rw_cells_transport _ _ _ _ _ _ RSC2a MU3 WM3 ltac:(cbn; lia)) as RSC2a3.
      assert (DH3 : DHEAP cs [(p, A, cap)] SPB m3 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
      { eapply dheap_frame_ext; [exact DH2| exact MU3| exact WM3|].
        solve_Forall ltac:(right; right; right; right; exists A, cap; split; [left; reflexivity| cbn [fst snd]; lia]). }
      (* [comment removed for export] *)
      assert (BLK3 : rw_cells psegs m3 A [CB (Z.to_nat (len + n)) (firstn (Z.to_nat (len + n)) data); CB (Z.to_nat (cap - (len + n))) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))]).
      { assert (J1 : rw_cells psegs m3 A ([CB (Z.to_nat len) (firstn (Z.to_nat len) data)] ++ ([CB (length bs) bs] ++ [CB (Z.to_nat (cap - len - n)) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))]))).
        { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact BLKa3|]. cbn [cells_size csize Nat.add].
          replace (A + Z.of_nat (Z.to_nat len + 0)) with (A + len) by lia.
          apply (proj2 (rw_cells_app _ _ _ _ _)). split.
          - replace (length bs) with (Z.to_nat n) by lia. exact DST3.
          - cbn [cells_size csize Nat.add]. replace (A + len + Z.of_nat (length bs + 0)) with (A + len + n) by lia. exact BLKc3. }
        cbn [app] in J1.
        pose proof (rw_cells_merge psegs m3 A [] [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (length bs) bs] _ J1) as J2.
        cbn [app cells_size cells_bytes csize cbytes] in J2. rewrite app_nil_r, BS in J2.
        replace (Z.to_nat len + (length bs + 0))%nat with (Z.to_nat (len + n)) in J2 by lia.
        replace (Z.to_nat (cap - (len + n))) with (Z.to_nat (cap - len - n)) by lia. exact J2. }
      (* [comment removed for export] *)
      assert (RSC3 : exists stj', rw_cells psegs m3 PRS [CB RSN stj']).
      { assert (J1 : rw_cells psegs m3 PRS ([CB (length bs) bs] ++ ([CB (Z.to_nat want - length bs) (skipn (length bs) (firstn (Z.to_nat want) stj))] ++ [CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))]))).
        { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact RSC2a3|]. cbn [cells_size csize Nat.add].
          replace (PRS + Z.of_nat (length bs + 0)) with (PRS + n) by lia.
          apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact RSC2b3|].
          cbn [cells_size csize Nat.add]. replace (PRS + n + Z.of_nat (Z.to_nat want - length bs + 0)) with (PRS + want) by lia. exact RSCb3. }
        cbn [app] in J1.
        pose proof (rw_cells_merge psegs m3 PRS [] [_; _; _] [] J1) as J2. cbn [app cells_size cells_bytes csize cbytes] in J2. rewrite ?app_nil_r in J2.
        eexists. replace RSN with (length bs + (Z.to_nat want - length bs + (Z.to_nat (65536 - want) + 0)))%nat by (pose proof RSN_Z; lia). exact J2. }
      assert (IV3 : INV (len + n) cap A cs p d (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk)) m3 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
      { split; [exact ST3|]. split; [exact MI3|]. split; [exact FR3|]. split; [exact DS3|]. split; [exact CJ3|]. split; [exists e; exact ER3|]. split; [exact IFL3|].
        split; [exact SOF3|]. split; [exact SEF3|]. split; [exact BY3|]. split; [exact DH3|]. split; [exact RP|]. split; [exact PD|]. split; [exact DM2|]. split; [exact FL|].
        split; [exact BLK3|]. split; [exact RSC3|]. split; [exists k; exact CAP|]. unfold zlength in *. lia. }
      clear FR3 DS3 CJ3 IFL3 SOF3 SEF3 BY3 BLK3 RSC3 DH3.
      (* [comment removed for export] *)
      unfold wz.
      do 3 step. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        apply evt_done. assert (E : len + n = cap) by (rewrite ?unsigned_lit in K by lia; lia).
        rewrite E in IV3 |- *. replace (n + len) with cap by lia.
        eapply (loop_grow cap A cs p d _ m3 _ (zlength data - len) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IV3 IH); unfold zlength in *; lia.
      + (* [comment removed for export] *)
        do 2 step. apply evt_done.
        eapply (IH (len + n) cap A cs p d _ m3 _ _ IV3); [rewrite ?unsigned_lit in K by lia; lia| | lia].
        unfold loop_regs. unfold wz. nexists 17%nat. replace (n + len) with (len + n) by lia. reflexivity.
    - (* [comment removed for export] *)
      apply evt_done.
      assert (EOFL : len = zlength data) by (rewrite ?unsigned_lit in K by lia; unfold zlength in *; lia).
      assert (N0 : n = 0) by (rewrite ?unsigned_lit in K by lia; lia).
      assert (RSC3 : exists stj', rw_cells psegs m2 PRS [CB RSN stj']).
      { assert (BS0 : length bs = 0%nat) by (clear - N0; subst n; lia).
        apply length_zero_iff_nil in BS0. rewrite BS0 in RSC2.
        cbn [length cells_size] in RSC2.
        assert (J1 : rw_cells psegs m2 PRS ([CB (Z.to_nat want - 0) (skipn 0 (firstn (Z.to_nat want) stj))] ++ [CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))])).
        { apply (proj2 (rw_cells_app _ _ _ _ _)). split.
          - pose proof (proj2 (proj1 (rw_cells_app psegs m2 PRS [CB 0 []] _) RSC2)) as R. cbn [cells_size csize Nat.add] in R. rewrite Z.add_0_r in R. exact R.
          - cbn [cells_size csize Nat.add]. replace (PRS + Z.of_nat (Z.to_nat want - 0 + 0)) with (PRS + want) by lia. exact RSCb2. }
        pose proof (rw_cells_merge psegs m2 PRS [] [_; _] [] J1) as J2. cbn [app cells_size cells_bytes csize cbytes] in J2. rewrite ?app_nil_r in J2.
        eexists. replace RSN with (Z.to_nat want - 0 + (Z.to_nat (65536 - want) + 0))%nat by (pose proof RSN_Z; lia). exact J2. }
      assert (IV2 : INV len cap A cs p d junk m2 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
      { split; [exact ST2|]. split; [exact MI2|]. split; [exact FR2|]. split; [exact DS2|]. split; [exact CJ2|]. split; [exists e; exact ER2|]. split; [exact IFL2|].
        split; [exact SOF2|]. split; [exact SEF2|]. split; [exact BY2|]. split; [rewrite N0, Z.add_0_r in DH2; rewrite N0, Z.add_0_r; exact DH2|]. split; [exact RP|]. split; [exact PD|].
        split; [rewrite N0, Z.add_0_r in DM2 |- *; exact DM2|]. split; [exact FL|].
        split; [exact BLK2|]. split; [exact RSC3|]. split; [exists k; exact CAP|]. unfold zlength in *. lia. }
      rewrite N0, Z.add_0_r in IV2 |- *. subst len.
      unfold Kloop.
      rewrite ?unsigned_lit by lia.
      eapply POST; [exact IV2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_want : forall (len cap A : Z) cs p d junk m mo (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      INV len cap A cs p d junk m mo -> HEAD_OK (zlength data - len) -> len < cap ->
      realizes psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz PRS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
                                F (wz 0x12218) fc None m (seg_rom psegs)) mo)
               (Kloop data fs cap).
  Proof.
    intros until t6. intros IV IH LT.
    (nelimp IV 21%nat; intros _ _ _ _ _ _ _ _ _ _ DH _ _ DM _ _ _ [k CAP] LEN1 LEN2 CAP2).
    pose proof DM as [MOK' _ _].
    unfold wz.
    eapply rz_step_evt; [exact MOK'|].
    step. rewrite (unsigned_lit len) by lia. do 2 step. if_cases K; zify_cond K.
    - apply evt_done. apply (loop_read len cap A cs p d junk m mo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cap - len) IV IH LT); lia.
    - step. apply evt_done. apply (loop_read len cap A cs p d junk m mo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 65536 IV IH LT); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma head_ok : forall n : nat, HEAD_OK (Z.of_nat n).
  Proof.
    induction n as [|n IHn]; intros len cap A cs p d junk m mo ms IV LT RG LT'.
    - exfalso. (nelim IV 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LEN1 LEN2 _). unfold zlength in *. lia.
    - pose proof (head_ok_mono _ (zlength data - len) IHn ltac:(lia)) as IH.
      (nelim RG 18%nat; intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 ->).
      apply (loop_want len cap A cs p d junk m mo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IV IH LT).
  Qed.

  Theorem loop_ok : loop_stmt sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
  Proof.
    intros len cap A cs p d junk m mo ms IV LT RG.
    (nelimp IV 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LEN1 LEN2 _).
    apply (head_ok (S (Z.to_nat (zlength data))) len cap A cs p d junk m mo ms IV LT RG). unfold zlength in *. lia.
  Qed.
End S.

(* [comment removed for export] *)
Theorem loop_proof :
  so_exit_stmt -> so_diag_oom_stmt -> so_diag_refused_stmt -> so_diag_read_error_stmt ->
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid ra0 : word)
         (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11 : word),
    loop_side sp tp fc lo SPB P1 tid path slack ->
    post_stmt sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11 ->
    loop_stmt sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
Proof.
  intros SE SO SR SRD. intros until q11. intros (TP & LO & GT & SPH & SPBE & TID & FRM & NONUL & SLK & LEN & PUS & SPAL) POST.
  eapply loop_ok; eassumption.
Qed.


End CeilWrap.
