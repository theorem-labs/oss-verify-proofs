(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer ZdFrame ZdFrameThm ZdHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdDctxRep ZdWalkKit ZdSepKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_facts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RF_fse_iface_m RF_fse_h_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_frame_iface RZ_block_iface RZ_dframe_iface RZ_dctx_iface RZ_dctx_iface_m RZ_prod_iface RZ_harness_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.
Section FuzzOne.
  Hypothesis CREATE : prod_create_stmt.
  Hypothesis RESERVE : zd_reserve_stmt.
  Hypothesis CREATEDCTX : zd_createdctx_stmt.
  Hypothesis U32R : zd_u32r_stmt.
  Hypothesis FMALLOC : fuzz_malloc_stmt.
  Hypothesis DDCTX : zd_ddctx_stmt.
  Hypothesis ISERR : zd_iserror_stmt.
  Hypothesis FINDDSIZE : zd_finddsize_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FREENULL : rfree_null_stmt.
  Hypothesis PFREE : prod_free_stmt.
  Hypothesis FREEDCTX : zd_freedctx_stmt.

  Theorem fuzz_one_proof : fuzz_one_stmt.
  Proof.
    unfold fuzz_one_stmt. intros until errv. intros HP PAY PAYB PAYR D16 D0 DTOP SZ DSEP HC SE AUX SPB ABB ST LOA LOS ERR MI FC TP SP16 A0 A1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold HARNESS_STACK in LOS. atop_facts.
    unfold wz in *. subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    unfold zlength in *.
    assert (LENP : zlen (map (Z_to_bv 8) payload) = zlen payload) by (rewrite length_map; reflexivity).
    destruct HC as (_ & _ & DCELL & GOTT).
    unfold Prog.fuzz_one, Harness.fuzz_one.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 64%nat ST.
    subst a0 a1. unfold PFUZZ_ENTRY.
    zstep. do 7 zstep. zstep. zstep.
    apply evt_done.
    assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
    assert (AUX1 : rauxv_ok m0 AB) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
    assert (HPR0 : hpres LB (bv_unsigned sp) m m0).
    { eapply hpres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|].
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
    assert (PAYR' : forall SP', SP' <= bv_unsigned sp -> rclient_range LB SP' D (zlen payload)).
    { intros SP' HS. unfold rclient_range in PAYR |- *. destruct PAYR as [R|[R|R]]; [left; lia| right; left; exact R| right; right; exact R]. }
    assert (DCR : forall LBq SP', rclient_range LBq SP' 295200 8).
    { intros. right; left. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
    assert (GTR : forall LBq SP', rclient_range LBq SP' 224832 16).
    { intros. right; left. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
    clear SE HP AUX MU WM.
    eapply implM_bind.
    { unfold prod_create_stmt in CREATE.
      eapply CREATE with (lo := lo) (B := AB); try reflexivity; unfold RATP, PROD_CREATE_STACK, FUZZ_MALLOC_STACK, RMALLOC_STACK; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (295416 + -164) with 295252; exact ERR]. }
    cbv beta. intros r sA ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & p & P & -> & -> & BR & HP2 & PRC & HEXP).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    replace (ret_pc (Z_to_bv 64 84080)) with (Z_to_bv 64 84080) by (symmetry; rpc).
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold PRODUCER_SIZE in BR3, BR4, BR5.
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64)
                    [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    assert (PAY2 : bytes_at usegs m2 D (map (Z_to_bv 8) payload))
      by (eapply rheap_pres_bytes_at; [exact HPR| exact PAY| rewrite length_map; apply PAYR'; lia]).
    assert (DCELL2 : rw_cells usegs m2 295200 [C8 (Z_to_bv 64 0)]) by (eapply rheap_pres_rw_cells; [exact HPR| exact DCELL| apply DCR]).
    assert (GOTT2 : rw_cells usegs m2 224832 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (eapply rheap_pres_rw_cells; [exact HPR| exact GOTT| apply GTR]).
    assert (DP : D + zlen payload <= P \/ P + 16 <= D).
    { unfold rclient_range in PAYR. destruct PAYR as [R|[R|(b & Hb & R1 & R2)]]; [lia| lia|].
      pose proof (RHEAP_disjoint_head _ _ _ _ _ _ b HP2 Hb) as DJ. unfold PRODUCER_SIZE in DJ. lia. }
    assert (HPRA : hpres LB (bv_unsigned sp) m m2).
    { eapply hpres_trans; [exact HPR0|]. eapply hpres_of_rheap_pres; [exact HPR| lia| intros b Hb; exact Hb]. }
    clear FR PAY DCELL GOTT HPR HPR0 ST MI ERR HP1 AUX1.
    assert (AB8 : all_bytes payload) by (apply Forall_all_bytes; exact PAYB).
    apply implM_from_evt.
    zstep. zstep.
    pose proof (munch_refl [(P, P + 16); (lo, bv_unsigned sp)] m2) as MUA. pose proof (wmono_refl usegs m2) as WMA.
    assert (P8 : P mod 8 = 0) by (clear - BR2; Z.div_mod_to_equations; lia).
    unfold zd_reserve_stmt in RESERVE.
    call (RESERVE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -64) P D payload (zlen payload) lo);
      [ exact PRC | split; [exact PAY2| exact PAYB] | lia | change (2^31) with 2147483648; change (2^26) with 67108864 in SZ; lia | lia | exact P8 | exact D0 | lia
      | exact ST2 | lia | lia | lia | lia | exact DP | exact MI2 | reflexivity | ].
    rename MI into MI3. rename PC into ST3. rename POST into PR3.
    pose proof (reserve_data_prefix_range payload (zlen payload) ltac:(change (2^32) with 4294967296; change (2^26) with 67108864 in SZ; lia)) as RDP.
    destruct (reserve_data_prefix payload (zlen payload)) as [rem eff] eqn:ERDP. cbn [fst snd] in *. destruct RDP as (RDP1 & RDP2 & RDP3).
    zstep. zstep. zstep. zstep. if_false.
    zstep.
    apply evt_done.
    destruct (fh_transport sA [(p, P, PRODUCER_SIZE)] LB m2 x13 _ AB (bv_unsigned sp) HP2 MUA WMA
                ltac:(constructor; [right; exists (p, P, PRODUCER_SIZE); split; [left; reflexivity| unfold PRODUCER_SIZE; cbn; lia]
                      | constructor; [left; cbn; atop_facts; lia| constructor]]) ltac:(atop_facts; lia))
      as (HP3 & AUX3 & _ & HPR23).
    specialize (AUX3 AUX2). cbn [app] in HP3.
    assert (HPRB : hpres LB (bv_unsigned sp) m x13).
    { eapply hpres_trans; [exact HPRA|]. eapply hpres_of_rheap_pres; [exact HPR23| lia| intros b Hb; exact Hb]. }
    clear HPRA HPR23 MUA WMA HP2 AUX2.
    unfold Harness.fuzz_malloc at 1. change (0 <? DCTX_SIZE) with true. cbv iota.
    apply implM_bind_assoc.
    eapply implM_bind.
    { unfold zd_createdctx_stmt, PZD_CREATEDCTX in CREATEDCTX.
      eapply CREATEDCTX with (lo := lo) (B := AB); try reflexivity; unfold RATP, CREATEDCTX_STACK, RMALLOC_STACK; rewrite ?unsigned_lit by lia;
        first [exact HP3 | exact AUX3 | exact ST3 | exact MI3 | lia | change (295416 + -164) with 295252; exact ERR2]. }
    cbv beta. intros r sB ms2 PO.
    destruct PO as (v0 & v1 & v2 & ra1 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv2 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & FAE4 & SOE4 & RR).
    rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia. rewrite errno_lit in ERR4. unfold RERRNO in ERR4.
    replace (ret_pc (Z_to_bv 64 84108)) with (Z_to_bv 64 84108) by (symmetry; rpc).
    destruct r as [pd|].
    2: { destruct RR as (_ & _). unfold new_handler. apply implM_bind_assoc. apply implM_unr. }
    destruct RR as (DC & -> & BRD & HP5 & DA5 & HEXD). pose proof BRD as (BD1 & BD2 & BD3 & BD4 & BD5). unfold DCTX_SIZE in BD3, BD4, BD5.
    assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -64)
                    [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR4| exact FR2| left; cbn; lia]).
    assert (PAY4 : bytes_at usegs m4 D (map (Z_to_bv 8) payload)).
    { eapply rheap_pres_bytes_at; [exact HPR4| exact PAY2|]. rewrite length_map.
      pose proof (PAYR' (bv_unsigned sp + -64) ltac:(lia)) as R. unfold rclient_range in R |- *.
      destruct R as [R|[R|(b & Hb & R)]]; [left; exact R| right; left; exact R| right; right; exists b; split; [right; exact Hb| exact R]]. }
    assert (DCELL4 : rw_cells usegs m4 295200 [C8 (Z_to_bv 64 0)]) by (eapply rheap_pres_rw_cells; [exact HPR4| exact DCELL2| apply DCR]).
    assert (GOTT4 : rw_cells usegs m4 224832 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (eapply rheap_pres_rw_cells; [exact HPR4| exact GOTT2| apply GTR]).
    assert (PR4 : prod_at m4 P (D + rem) eff).
    { unfold prod_at in *. eapply rheap_pres_rw_cells; [exact HPR4| exact PR3|]. right; right. exists (p, P, PRODUCER_SIZE).
      split; [left; reflexivity| cbn; unfold PRODUCER_SIZE; lia]. }
    assert (HPRC : hpres LB (bv_unsigned sp) m m4).
    { eapply hpres_trans; [exact HPRB|]. eapply hpres_of_rheap_pres; [exact HPR4| lia| intros b Hb; right; exact Hb]. }
    clear FR2 PAY2 DCELL2 GOTT2 PR3 HPRB HPR4 HP3 AUX3 ST3 MI3 ERR2.
    unfold prod_at in PR4.
    apply implM_retb.
    apply implM_from_evt.
    pose proof (munch_refl [(295200, 295208); (P, P + 16); (lo, bv_unsigned sp)] m4) as MUB. pose proof (wmono_refl usegs m4) as WMB.
    zstep. zstep. if_cases KN; zify_cond KN; [exfalso; lia|].
    zstep. zstep. rewrite swrap32_small by (change (2^26) with 67108864 in SZ; lia).
    zstep. zstep. zstep.
    set (pl2 := skipn (Z.to_nat rem) payload).
    assert (PL2 : bytes_at usegs m1 (D + rem) (map (Z_to_bv 8) pl2)) by (apply zd_src_skipn; [exact PAY4| lia]).
    assert (PL2B : Forall (fun c => 0 <= c < 256) pl2).
    { apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) PAYB). unfold pl2 in Hc.
      rewrite <- (firstn_skipn (Z.to_nat rem) payload). apply in_or_app. right. exact Hc. }
    assert (PL2L : zlen pl2 = zlen payload - rem) by (unfold pl2; rewrite length_skipn; lia).
    unfold zd_u32r_stmt in U32R.
    call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -64) P (D + rem) pl2 eff 0 (rem * 10) lo);
      [ exact PR4 | split; [exact PL2| exact PL2B] | lia | lia | exact P8 | lia | exact ST4 | lia | lia | lia | lia | lia | exact MI4
      | lia | change (2^31) with 2147483648; change (2^26) with 67108864 in SZ; lia | reflexivity | reflexivity | reflexivity | ].
    rename MI into MI6. rename PC into ST6. rename POST into PR6.
    assert (EBS : fst (uint32Range pl2 eff 0 (rem * 10)) = buff_size payload).
    { unfold buff_size, sd_buf_size, sd_draws, FseNCount.Zlength. rewrite ERDP. fold pl2. rewrite (Z.mul_comm 10 rem).
      destruct (uint32Range pl2 eff 0 (rem * 10)) as [bb ee]. reflexivity. }
    pose proof (uint32Range_range pl2 eff 0 (rem * 10) ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; change (2^26) with 67108864 in SZ; lia)
                  ltac:(change (2^32) with 4294967296; change (2^26) with 67108864 in SZ; lia)) as URR.
    destruct (uint32Range pl2 eff 0 (rem * 10)) as [bsz eff2] eqn:EUR. cbn [fst snd] in *. destruct URR as (RB1 & RB2).
    zstep. zstep.
    replace (Z.land bsz 4294967295) with bsz
      by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2^32) with 4294967296; change (2^26) with 67108864 in SZ; lia).
    zstep. zstep.
    apply evt_done.
    pose proof (RHEAP_disjoint_head _ _ _ _ _ _ (p, P, PRODUCER_SIZE) HP5 ltac:(left; reflexivity)) as DJ_DP. cbn [blk_addr blk_size fst snd] in DJ_DP.
    unfold DCTX_SIZE, PRODUCER_SIZE in DJ_DP.
    assert (DA6 : dctx_any x28 DC).
    { eapply (dctx_any_transport DC _ m4 x28); [exact DA5 | exact MUB | exact WMB |]. cbn [disjoint_from]. atop_facts. lia. }
    destruct (fh_transport_d sB [(pd, DC, DCTX_SIZE); (p, P, PRODUCER_SIZE)] LB m4 x28 _ AB (bv_unsigned sp) HP5 MUB WMB
                ltac:(constructor; [right; reflexivity
                      | constructor; [left; right; exists (p, P, PRODUCER_SIZE); split; [right; left; reflexivity| unfold PRODUCER_SIZE; cbn; lia]
                      | constructor; [left; left; cbn; atop_facts; lia| constructor]]]) ltac:(atop_facts; lia))
      as (HP6 & AUX6 & HPR46).
    specialize (AUX6 AUX4). cbn [app] in HP6.
    assert (HPRD : hpres LB (bv_unsigned sp) m x28) by (eapply hpres_trans; [exact HPRC| exact HPR46]).
    clear HPRC HPR46 MUB WMB HP5 AUX4 DA5.
    eapply implM_bind.
    { unfold fuzz_malloc_stmt, PFUZZ_MALLOC in FMALLOC.
      eapply FMALLOC with (lo := lo) (B := AB) (n := buff_size payload); try reflexivity; unfold RATP, FUZZ_MALLOC_STACK, RMALLOC_STACK; rewrite ?unsigned_lit by lia;
        first [exact HP6 | exact AUX6 | exact ST6 | exact MI6 | rewrite <- EBS; reflexivity | rewrite <- EBS; change (2^32) with 4294967296; change (2^26) with 67108864 in SZ; lia
              | lia | change (295416 + -164) with 295252; exact ERR4]. }
    cbv beta. intros rb sC ms3 PO.
    destruct PO as (w0 & w1 & w2 & ra2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m7 & errv3 & -> & MI7 & ST7 & ERR7 & AUX7 & HPR7 & FAE7 & SOE7 & RR).
    rewrite ?unsigned_lit in ST7 by lia. rewrite ?unsigned_lit in HPR7 by lia. rewrite errno_lit in ERR7. unfold RERRNO in ERR7.
    replace (ret_pc (Z_to_bv 64 84152)) with (Z_to_bv 64 84152) by (symmetry; rpc).
    assert (FR7 : rw_cells usegs m7 (bv_unsigned sp + -64)
                    [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rheap_pres_rw_cells; [exact HPR7| exact FR4| left; cbn; lia]).
    assert (PAY7 : bytes_at usegs m7 D (map (Z_to_bv 8) payload)).
    { eapply rheap_pres_bytes_at; [exact HPR7| exact PAY4|]. rewrite length_map.
      pose proof (PAYR' (bv_unsigned sp + -64) ltac:(lia)) as R. unfold rclient_range in R |- *.
      destruct R as [R|[R|(b & Hb & R)]]; [left; exact R| right; left; exact R| right; right; exists b; split; [right; right; exact Hb| exact R]]. }
    assert (DCELL7 : rw_cells usegs m7 295200 [C8 (Z_to_bv 64 DC)]) by (eapply rheap_pres_rw_cells; [exact HPR7| exact DCELL4| apply DCR]).
    assert (GOTT7 : rw_cells usegs m7 224832 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (eapply rheap_pres_rw_cells; [exact HPR7| exact GOTT4| apply GTR]).
    assert (DA7 : dctx_any m7 DC).
    { eapply (dctx_any_rheap_pres _ _ x28 m7 DC (pd, DC, DCTX_SIZE)); [exact HPR7 | exact DA6 | left; reflexivity | reflexivity | reflexivity]. }
    assert (HPRE : hpres LB (bv_unsigned sp) m m7).
    { eapply hpres_trans; [exact HPRD|]. eapply hpres_of_rheap_pres; [exact HPR7| lia| intros b Hb; right; right; exact Hb]. }
    assert (D_DC : zsep D (D + zlen payload) DC (DC + 95992)).
    { unfold zsep. pose proof (PAYR' (bv_unsigned sp) ltac:(lia)) as R. unfold rclient_range in R.
      destruct R as [R|[R|(b & Hb & R1 & R2)]]; [lia| lia|].
      pose proof (RHEAP_disjoint_head _ _ _ _ _ _ b HP6 ltac:(right; exact Hb)) as DJ. unfold DCTX_SIZE in DJ. lia. }
    clear FR4 PAY4 DCELL4 GOTT4 DA6 HPRD HP6 AUX6 ST6 MI6 ERR4 PR6.
    assert (D4096 : 4096 <= D).
    { pose proof (PAYR' (bv_unsigned sp) ltac:(lia)) as R. unfold rclient_range in R.
      destruct R as [R|[R|(b & Hb & R1 & R2)]]; [atop_facts; lia| lia|].
      assert (HPx : exists sx LBx, RHEAP sx (LBx ++ LB) m7).
      { destruct rb as [pb|]; [destruct RR as (Ab & jb & _ & _ & HPx & _); exists sC, [(pb, Ab, buff_size payload); (pd, DC, DCTX_SIZE); (p, P, PRODUCER_SIZE)]; exact HPx
                              | destruct RR as (_ & _ & HPx); exists sC, [(pd, DC, DCTX_SIZE); (p, P, PRODUCER_SIZE)]; exact HPx]. }
      destruct HPx as (sx & LBx & HPx).
      pose proof (RHEAP_block_low _ _ _ _ HPx ltac:(apply in_app_iff; right; exact Hb)). lia. }
    assert (DC4096 : 4096 <= DC) by (clear - BD1 BD5; lia).
    (* [comment removed for export] *)
    assert (PHASEC : forall DST (y0 : word),
      stk usegs m7 DST (DST + bsz) -> 0 <= DST -> (DST = 0 -> bsz = 0) -> (DST <> 0 -> 4096 <= DST) -> DST + bsz <= ATOP ->
      zsep DST (DST + bsz) DC (DC + 95992) -> zsep DST (DST + bsz) D (D + zlen payload) -> zsep DST (DST + bsz) 65536 430080 ->
      y0 = Z_to_bv 64 DST ->
      evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' : word) (m8 : mem),
                  ms' = MS (mkR (Z_to_bv 64 84236) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 D)
                                (Z_to_bv 64 DST) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 rem) (Z_to_bv 64 DST) s4' (Z_to_bv 64 297080)
                                 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (Z_to_bv 64 RFREE_SYM) fc None m8 (seg_rom usegs)
                   /\ munch [(DC, DC + 95992); (DST, DST + bsz); (lo, bv_unsigned sp)] m7 m8 /\ wmono usegs m7 m8 /\ mem_inv usegs m8
                   /\ stk usegs m8 lo (bv_unsigned sp + -64)
                   /\ rw_cells usegs m8 (bv_unsigned sp + -64)
                        [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                   /\ rw_cells usegs m8 295200 [C8 (Z_to_bv 64 DC)]
                   /\ rw_cells usegs m8 295252 [C4 errv3]
                   /\ dctx_any m8 DC)
         (MS (mkR (Z_to_bv 64 84152) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) w0 w1 w2 (Z_to_bv 64 P) (Z_to_bv 64 D) y0 d1 d2 d3 d4 d5 d6 d7
                  (Z_to_bv 64 rem) s3 (Z_to_bv 64 bsz) (Z_to_bv 64 297080) s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
             F (Z_to_bv 64 84152) fc None m7 (seg_rom usegs))).
    { intros DST y0 DSK DST0 DNULLF DNNF DTOPF Z_DC Z_D Z_IMG ->.
      assert (Z_IDC : zsep DC (DC + 95992) 65536 430080) by exact BD5.
      assert (SPM : id ((bv_unsigned sp + -64) mod 16 = 0)) by (unfold id; clear - SP16; Z.div_mod_to_equations; lia).
      clear - ISERR DDCTX FINDDSIZE DSK DST0 DNULLF DNNF DTOPF Z_DC Z_D Z_IMG Z_IDC D_DC ST7 MI7 ERR7 FR7 PAY7 DCELL7 GOTT7 DA7 AB8 RDP1 RDP2 RDP3 RB1 RB2 SZ
              LOA LOS RSP BD1 BD2 BD3 BD4 D0 DTOP LENP KN SPB ABB D4096 DC4096 SPM.
      pose proof (munch_refl [(DC, DC + 95992); (DST, DST + bsz); (lo, bv_unsigned sp)] m7) as MUC. pose proof (wmono_refl usegs m7) as WMC.
      atop_facts. change (2^26) with 67108864 in SZ. change (2^47) with 140737488355328 in ABB.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      assert (DA' : id (dctx_any m7 DC)) by exact DA7. clear DA7.
      assert (DSK' : id (stk usegs m7 DST (DST + bsz))) by exact DSK. clear DSK.
      assert (ST' : id (stk usegs m7 lo (bv_unsigned sp + -64))) by exact ST7. clear ST7.
      assert (DC8 : DC mod 8 = 0) by (clear - BD2; Z.div_mod_to_equations; lia).
      assert (SUBFP : sub_fp [(DC, DC + 95992); (DST, DST + bsz); (bv_unsigned sp + -64 - 2368, bv_unsigned sp + -64)]
                             [(DC, DC + 95992); (DST, DST + bsz); (lo, bv_unsigned sp)]).
      { clear - LOS. unfold sub_fp. cbn [outside]. intros x Hx. repeat split; try lia; exact I. }
      unfold zd_ddctx_stmt, PZD_DDCTX in DDCTX.
      callk (DDCTX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -64) lo DC DST bsz D payload rem);
        [ exact DA' | exact DC4096 | lia | exact DC8 | exact GOTT7 | exact PAY7 | exact AB8 | lia | lia | change (2^40) with 1099511627776; lia
        | exact D4096 | lia | exact DSK' | lia | change (2^40) with 1099511627776; lia | exact DNULLF | exact DNNF | lia
        | exact ST' | lia | lia | lia | exact SPM
        | left; lia | left; lia | left; lia | left; lia
        | exact Z_DC | exact Z_D | exact D_DC | unfold zsep in Z_IDC; lia | unfold zsep in Z_IMG; lia
        | exact MI7 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
      rename MI into MI8. rename PC into ST8. rename PC0 into DA8. rename PC1 into DSK8. rename PC2 into RR8. rename POST into ROK.
      clear SUBFP DA' DSK' ST'. change (2^64) with 18446744073709551616 in RR8.
      zstep. zstep.
      unfold zd_iserror_stmt, PZD_ISERROR in ISERR.
      call_pure (ISERR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x14); [lia | reflexivity |].
      assert (FIN : forall mm (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' : word),
        munch [(DC, DC + 95992); (DST, DST + bsz); (lo, bv_unsigned sp)] m7 mm -> wmono usegs m7 mm -> mem_inv usegs mm ->
        stk usegs mm lo (bv_unsigned sp + -64) ->
        rw_cells usegs mm (bv_unsigned sp + -64)
          [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells usegs mm 295200 [C8 (Z_to_bv 64 DC)] -> rw_cells usegs mm 295252 [C4 errv3] -> dctx_any mm DC ->
        evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' : word) (m8 : mem),
                  ms' = MS (mkR (Z_to_bv 64 84236) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 D)
                                (Z_to_bv 64 DST) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 rem) (Z_to_bv 64 DST) s4' (Z_to_bv 64 297080)
                                 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (Z_to_bv 64 RFREE_SYM) fc None m8 (seg_rom usegs)
                   /\ munch [(DC, DC + 95992); (DST, DST + bsz); (lo, bv_unsigned sp)] m7 m8 /\ wmono usegs m7 m8 /\ mem_inv usegs m8
                   /\ stk usegs m8 lo (bv_unsigned sp + -64)
                   /\ rw_cells usegs m8 (bv_unsigned sp + -64)
                        [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                   /\ rw_cells usegs m8 295200 [C8 (Z_to_bv 64 DC)]
                   /\ rw_cells usegs m8 295252 [C4 errv3]
                   /\ dctx_any m8 DC)
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 D)
                  a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 rem) (Z_to_bv 64 DST) s4' (Z_to_bv 64 297080) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 84228) fc None mm (seg_rom usegs))).
      { intros mm ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' A1 A2 A3 A4 A5 A6 A7 A8.
        zstep. zstep. apply evt_done.
        do 15 eexists. exists mm. split; [reflexivity|].
        split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7| exact A8]. }
      zstep. destruct (zd_is_error x14) eqn:EERR; cbn [Z.b2z].
      - (* [comment removed for export] *)
        if_true. eapply FIN; eassumption.
      - if_false.
        specialize (ROK eq_refl).
        pose proof (decompress_ok_finder payload AB8 rem bsz x14 ltac:(change (2^64) with 18446744073709551616; lia)
                      ltac:(unfold ZD_CONTENTSIZE_ERROR; change (2^64) with 18446744073709551616; lia) ROK) as (FNE & FEQ & FRG).
        zstep. zstep. zstep.
        unfold zd_finddsize_stmt, PZD_FINDDSIZE in FINDDSIZE.
        assert (SUBFP : sub_fp [(bv_unsigned sp + -64 - 320, bv_unsigned sp + -64)] [(DC, DC + 95992); (DST, DST + bsz); (lo, bv_unsigned sp)]).
        { clear - LOS. unfold sub_fp. cbn [outside]. intros x Hx. repeat split; try lia; exact I. }
        pose proof (munch_refl [(bv_unsigned sp + -64 - 320, bv_unsigned sp + -64)] x13) as MUF. pose proof (wmono_refl usegs x13) as WMF.
        callk (FINDDSIZE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -64) D payload rem lo);
          [ exact PAY7 | exact AB8 | lia | change (2^40) with 1099511627776; lia | lia | lia | lia | exact ST8 | lia | lia | exact SPM | left; lia | exact MI8
          | reflexivity | reflexivity | ].
        assert (DA9 : dctx_any x25 DC).
        { eapply (dctx_any_transport DC _ x13 x25); [exact DA8 | exact MUF | exact WMF |]. cbn [disjoint_from]. lia. }
        clear DA8 MUF WMF SUBFP. rename MI into MI9. rename POST into ST9.
        destruct FEQ as [FU|FR].
        + rewrite FU. replace (Z_to_bv 64 ZD_CONTENTSIZE_UNKNOWN) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
          zstep. zstep. if_true. eapply FIN; eassumption.
        + rewrite FR.
          zstep. zstep. if_cases KA; zify_cond KA; [exfalso; lia|].
          zstep. zstep. if_cases KB; zify_cond KB; [exfalso; lia|].
          zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
          eapply FIN; eassumption. }
    (* [comment removed for export] *)
    assert (TAIL : forall sX mX (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' z1 z2 z3 z4 t3' t4' t5' t6' : word),
      RHEAP sX ((pd, DC, DCTX_SIZE) :: (p, P, PRODUCER_SIZE) :: LB) mX -> rauxv_ok mX AB -> mem_inv usegs mX ->
      stk usegs mX lo (bv_unsigned sp + -64) ->
      rw_cells usegs mX (bv_unsigned sp + -64)
        [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs mX 295200 [C8 (Z_to_bv 64 DC)] -> rw_cells usegs mX 295252 [C4 errv3] -> dctx_any mX DC ->
      hpres LB (bv_unsigned sp) m mX -> ps_so sX = ps_so s ->
      implM usegs (free_opt raw_free (Some p);;; free_opt raw_free (Some pd);;; mret 0) sX
        (fuzz_one_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
        (MS (mkR (Z_to_bv 64 84236) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 P) z1
                 a0' a1' a2' a3' a4' a5' a6' a7' z2 z3 z4 (Z_to_bv 64 297080) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 84236) fc None mX (seg_rom usegs))).
    { intros sX mX t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' z1 z2 z3 z4 t3' t4' t5' t6' HPX AUXX MIX STX FRX DCX ERRX DAX HPRX SOX.
      clear PHASEC RR.
      cbn [free_opt].
      apply implM_from_evt. zstep. zstep. apply evt_done.
      pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HPX) as ND1.
      pose proof (lb_remove_second p (pd, DC, DCTX_SIZE) (p, P, PRODUCER_SIZE) _ eq_refl ND1) as LBR1.
      eapply implM_bind.
      { unfold prod_free_stmt, RF_fse_iface_m.PPROD_FREE in PFREE.
        eapply PFREE with (lo := lo) (B := AB) (A := P) (n := PRODUCER_SIZE); try reflexivity; unfold RATP, RFREE_STACK; rewrite ?unsigned_lit by lia;
          first [exact HPX | right; left; reflexivity | exact AUXX | exact STX | exact MIX | lia | change (295416 + -164) with 295252; exact ERRX]. }
      cbv beta. intros [] sY ms4 PO.
      destruct PO as (v0' & v1' & v2' & ra3 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3' & v4' & v5' & v6' & mY & -> & MIY & STY & ERRY & AUXY & HPRY & FAEY & SOEY & HPY).
      rewrite LBR1 in HPRY, HPY.
      rewrite ?unsigned_lit in STY by lia. rewrite ?unsigned_lit in HPRY by lia. rewrite errno_lit in ERRY. unfold RERRNO in ERRY.
      replace (ret_pc (Z_to_bv 64 84244)) with (Z_to_bv 64 84244) by (symmetry; rpc).
      assert (FRY : rw_cells usegs mY (bv_unsigned sp + -64)
                      [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rheap_pres_rw_cells; [exact HPRY| exact FRX| left; cbn; lia]).
      assert (DCY : rw_cells usegs mY 295200 [C8 (Z_to_bv 64 DC)]) by (eapply rheap_pres_rw_cells; [exact HPRY| exact DCX| apply DCR]).
      assert (DAY : dctx_any mY DC).
      { eapply (dctx_any_rheap_pres _ _ mX mY DC (pd, DC, DCTX_SIZE)); [exact HPRY | exact DAX | left; reflexivity | reflexivity | reflexivity]. }
      assert (HPRXY : hpres LB (bv_unsigned sp) m mY).
      { eapply hpres_trans; [exact HPRX|]. eapply hpres_of_rheap_pres; [exact HPRY| lia| intros b Hb; right; exact Hb]. }
      clear FRX DCX DAX HPRX HPRY HPX AUXX MIX STX ERRX.
      apply implM_from_evt. zstep. zstep. apply evt_done.
      eapply implM_bind.
      { unfold zd_freedctx_stmt, PZD_FREEDCTX in FREEDCTX.
        eapply FREEDCTX with (lo := lo) (B := AB) (A := DC); try reflexivity; unfold RATP, FREEDCTX_STACK, RFREE_STACK; rewrite ?unsigned_lit by lia;
          first [exact HPY | exact DAY | exact AUXY | exact STY | exact MIY | lia | change (295416 + -164) with 295252; exact ERRY]. }
      cbv beta. intros [] sZ ms5 PO.
      destruct PO as (v0'' & v1'' & v2'' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & v3'' & v4'' & v5'' & v6'' & mZ & -> & MIZ & STZ & ERRZ & AUXZ & HPRZ & FAEZ & SOEZ & HPZ).
      rewrite ?unsigned_lit in STZ by lia. rewrite ?unsigned_lit in HPRZ by lia. rewrite errno_lit in ERRZ. unfold RERRNO in ERRZ.
      replace (ret_pc (Z_to_bv 64 84252)) with (Z_to_bv 64 84252) by (symmetry; rpc).
      assert (FRZ : rw_cells usegs mZ (bv_unsigned sp + -64)
                      [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rheap_pres_rw_cells; [exact HPRZ| exact FRY| left; cbn; lia]).
      assert (DCZ : rw_cells usegs mZ 295200 [C8 (Z_to_bv 64 DC)]) by (eapply rheap_pres_rw_cells; [exact HPRZ| exact DCY| apply DCR]).
      assert (HPRXZ : hpres LB (bv_unsigned sp) m mZ).
      { eapply hpres_trans; [exact HPRXY|]. eapply hpres_of_rheap_pres; [exact HPRZ| lia| intros b Hb; exact Hb]. }
      clear FRY DCY DAY HPRXY HPRZ HPY AUXY MIY STY ERRY.
      apply implM_ret.
      pose proof (munch_refl [(295200, 295208); (lo, bv_unsigned sp)] mZ) as MUZ. pose proof (wmono_refl usegs mZ) as WMZ.
      zstep. zstep.
      do 7 zstep. zstep. zstep.
      lazymatch type of MUZ with munch _ _ ?mW =>
        destruct (fh_transport_d sZ [] LB mZ mW _ AB (bv_unsigned sp) HPZ MUZ WMZ
                    ltac:(constructor; [right; reflexivity | constructor; [left; left; cbn; atop_facts; lia| constructor]]) ltac:(atop_facts; lia))
          as (HPW & AUXW & HPRZW)
      end.
      specialize (AUXW AUXZ). cbn [app] in HPW.
      apply evt_done. unfold fuzz_one_post.
      do 14 eexists. exists F, fc. eexists. exists errv3. split; [reflexivity|].
      split; [lia|]. split; [exact MIZ|]. split; [exact FC|].
      split.
      { apply stk_of_rw_cells in FRZ. cbn [cells_size csize Nat.add] in FRZ.
        replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in FRZ by lia. eapply stk_merge; [exact STZ | exact FRZ | lia]. }
      split; [rewrite errno_lit; exact ERRZ|]. split; [exact AUXW|].
      split.
      { apply harness_pres_intro.
        - exact (hpres_trans _ _ _ _ _ HPRXZ HPRZW).
        - intros a Ha. destruct DCZ as [_ (W0 & W1 & WV)]. cbn [cells_size csize Nat.add] in WV.
          replace a with (295200 + (a - 295200)) by lia. apply WV. lia. }
      split; [exact DCZ|]. split; [exact HPW|].
      rewrite SOEZ, SOEY. exact SOX. }
    destruct rb as [pb|].
    - (* [comment removed for export] *)
      destruct RR as (BUFF & junkb & -> & BRB & HP7 & BLKB & HEXB). pose proof BRB as (BB1 & BB2 & BB3 & BB4 & BB5).
      rewrite <- EBS in BRB, HP7, BLKB, BB3, BB4, BB5.
      pose proof (RHEAP_block_low _ _ _ _ HP7 ltac:(left; reflexivity)) as BLOW. cbn [blk_addr fst snd] in BLOW.
      pose proof (RHEAP_disjoint_head _ _ _ _ _ _ (pd, DC, DCTX_SIZE) HP7 ltac:(left; reflexivity)) as DJ_BD. cbn [blk_addr blk_size fst snd] in DJ_BD. unfold DCTX_SIZE in DJ_BD.
      assert (DJ_BPAY : zsep BUFF (BUFF + bsz) D (D + zlen payload)).
      { unfold zsep. pose proof (PAYR' (bv_unsigned sp) ltac:(lia)) as R. unfold rclient_range in R.
        destruct R as [R|[R|(b & Hb & R1 & R2)]]; [atop_facts; lia| lia|].
        pose proof (RHEAP_disjoint_head _ _ _ _ _ _ b HP7 ltac:(right; right; exact Hb)) as DJ. lia. }
      apply stk_of_rw_cells in BLKB. cbn [cells_size csize Nat.add] in BLKB. rewrite Nat.add_0_r, Z2Nat.id in BLKB by lia.
      cbn [free_opt].
      apply implM_from_evt.
      eapply evt_cut.
      { eapply (PHASEC BUFF); [exact BLKB | lia | intros E0; exfalso; lia | intros _; exact BLOW | lia | exact DJ_BD | exact DJ_BPAY | exact BB5 | reflexivity]. }
      cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & t3' & t4' & t5' & t6' & m8 & -> & MU8 & WM8 & MI8 & ST8 & FR8 & DC8 & ERR8 & DA8).
      apply evt_done.
      destruct (fh_transport sC [(pb, BUFF, bsz); (pd, DC, DCTX_SIZE); (p, P, PRODUCER_SIZE)] LB m7 m8 _ AB (bv_unsigned sp) HP7 MU8 WM8
                  ltac:(constructor; [right; exists (pd, DC, DCTX_SIZE); split; [right; left; reflexivity| unfold DCTX_SIZE; cbn; lia]
                        | constructor; [right; exists (pb, BUFF, bsz); split; [left; reflexivity| cbn; lia]
                        | constructor; [left; cbn; atop_facts; lia| constructor]]]) ltac:(atop_facts; lia))
        as (HP8 & AUX8 & _ & HPR78).
      specialize (AUX8 AUX7). cbn [app] in HP8.
      pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP8) as ND8.
      pose proof (lb_remove_hd pb (pb, BUFF, bsz) _ eq_refl ND8) as LBR8.
      eapply implM_bind.
      { unfold rfree_stmt in FREE.
        eapply FREE with (lo := lo) (B := AB) (A := BUFF) (n := bsz); try reflexivity; unfold RATP, RFREE_STACK; rewrite ?unsigned_lit by lia;
          first [exact HP8 | left; reflexivity | exact AUX8 | exact ST8 | exact MI8 | lia | change (295416 + -164) with 295252; exact ERR8]. }
      cbv beta. intros [] sD ms6 PO.
      destruct PO as (k0 & k1 & k2 & ra4 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & k3 & k4 & k5 & k6 & m9 & -> & MI9 & ST9 & ERR9 & AUX9 & HPR9 & FAE9 & SOE9 & HP9).
      rewrite LBR8 in HPR9, HP9.
      rewrite ?unsigned_lit in ST9 by lia. rewrite ?unsigned_lit in HPR9 by lia. rewrite errno_lit in ERR9. unfold RERRNO in ERR9.
      replace (ret_pc (Z_to_bv 64 84236)) with (Z_to_bv 64 84236) by (symmetry; rpc).
      eapply TAIL; [exact HP9 | exact AUX9 | exact MI9 | exact ST9 | | | exact ERR9 | | | ].
      + eapply rheap_pres_rw_cells; [exact HPR9| exact FR8| left; cbn; lia].
      + eapply rheap_pres_rw_cells; [exact HPR9| exact DC8| apply DCR].
      + eapply (dctx_any_rheap_pres _ _ m8 m9 DC (pd, DC, DCTX_SIZE)); [exact HPR9 | exact DA8 | left; reflexivity | reflexivity | reflexivity].
      + eapply hpres_trans; [exact HPRE|]. eapply hpres_trans; [eapply hpres_of_rheap_pres; [exact HPR78| lia| intros b Hb; exact Hb]|].
        eapply hpres_of_rheap_pres; [exact HPR9| lia| intros b Hb; right; right; exact Hb].
      + rewrite SOE9, SOE7, SOE4. exact SOE.
    - (* [comment removed for export] *)
      destruct RR as (BS0 & -> & HP7). rewrite BS0 in EBS. subst bsz.
      cbn [free_opt]. apply implM_retb.
      apply implM_from_evt.
      eapply evt_cut.
      { eapply (PHASEC 0); [apply stk_empty; lia | lia | intros _; reflexivity | intros E0; exfalso; apply E0; reflexivity | atop_facts; lia
                            | unfold zsep; lia | unfold zsep; lia | unfold zsep; lia | reflexivity]. }
      cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & t3' & t4' & t5' & t6' & m8 & -> & MU8 & WM8 & MI8 & ST8 & FR8 & DC8 & ERR8 & DA8).
      eapply evt_cut.
      { eapply FREENULL. reflexivity. }
      cbv beta. intros ms' ->.
      replace (ret_pc (Z_to_bv 64 84236)) with (Z_to_bv 64 84236) by (symmetry; rpc).
      apply evt_done.
      assert (MU8' : munch [(DC, DC + 95992); (lo, bv_unsigned sp)] m7 m8).
      { eapply munch_weaken; [| exact MU8]. unfold sub_fp. cbn [outside]. intros xq (X1 & X2 & _). repeat split; try assumption; lia. }
      destruct (fh_transport sC [(pd, DC, DCTX_SIZE); (p, P, PRODUCER_SIZE)] LB m7 m8 _ AB (bv_unsigned sp) HP7 MU8' WM8
                  ltac:(constructor; [right; exists (pd, DC, DCTX_SIZE); split; [left; reflexivity| unfold DCTX_SIZE; cbn; lia]
                        | constructor; [left; cbn; atop_facts; lia| constructor]]) ltac:(atop_facts; lia))
        as (HP8 & AUX8 & _ & HPR78).
      specialize (AUX8 AUX7). cbn [app] in HP8.
      eapply TAIL; [exact HP8 | exact AUX8 | exact MI8 | exact ST8 | exact FR8 | exact DC8 | exact ERR8 | exact DA8 | | ].
      + eapply hpres_trans; [exact HPRE|]. eapply hpres_of_rheap_pres; [exact HPR78| lia| intros b Hb; exact Hb].
      + rewrite SOE7, SOE4. exact SOE.
  Qed.
End FuzzOne.
End CANSEC1.
