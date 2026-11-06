(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem EatLeaf EatAllocG EatPoison EatRzLog EatAllocA EatInitCache EatPopulate1 ArtRuns ArtRunsMem EatCls EatFp EatClsRep EatClsGfa2 EatCellEx EatByteCell EatCARSpec EatAlloc3Pure EatDepotA EatDepot EatUnwind ArtBridge EatAllocate3 EatMallocTop3 EatMallocTop3S EarInv EatInvMallocPure EatInvMallocFp EarInvMalloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EarTopMalloc3 EarTopMalloc3S EarUkey.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Entry.
Variable FSG : Type.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_wm_entry :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
         (Sp n rl rz qz rs qr qn m8 km top bot : Z) (kb : nat),
    let c := AsanTab.class_id (rs + rz) in
    let cl := g_cls FSG G c in
    let w := art_ca_cptr c cl in
    let ab := rn_spb rn + c * 2 ^ 32 + w * 16 in
    art_alloc_rep FSG rn G LB Mr ->
    getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 n ->
    8 <= n -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 -> rs + rz <= 65536 ->
    rn_HI rn + 4096 <= Sp - 4096 -> Sp <= 2 ^ 47 -> Sp mod 16 = 0 ->
    top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    wrA Mr (Sp - 4096) 4096 -> readable8 Mr Sp top ->
    g_depot FSG G = Datatypes.S kb -> cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
    art_evok_list EVOK log (art_ca_events (rn_spb rn) c cl) ->
    (forall regs' (Mr' : word -> option byte) (b1 : Z),
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
        art_malloc_out rn Mr Mr' Sp n rz qz rs qr qn m8 km kb cl b1 ->
        Q (log ++ art_ca_events (rn_spb rn) c cl) (mkst regs' raw0 Mr' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst R (0x7a378 : word) Mr rom).
Proof.
  intros Q log R Mr rom raw0 rn G LB Sp n rl rz qz rs qr qn m8 km top bot kb c cl w ab
         REP H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W RD0 Edep Emu Room EV K.
  pose proof (AsanTab.class_id_ok (rs + rz) ltac:(lia)) as (Hc & _). fold c in Hc.
  destruct REP as (ROK & ST & TH & (PH & PRIM & Wsh) & CH & _ & _ & DEP & _).
  rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & _ & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & T7). rewrite <- Etop in T3. rewrite <- Ebot in T4.
  destruct (PRIM c Hc) as (RC & OK & Hin & _). fold cl in RC, OK, Hin.
  specialize (CH c Hc). cbv zeta in CH. destruct CH as (I & II & _ & III). fold cl in I, II, III.
  unfold art_rt_depot in DEP. rewrite Edep in DEP.
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & _ & _ & Hfor & _).
  assert (ES : forall y, HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * rn_qs rn + c * 2 ^ 29 + y). { intros y. rewrite Espb. apply art_S_lin. }
  apply (art_malloc3N EVOK GR Q log R Mr rom raw0 Sp (rn_HI rn) n (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_loff rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km
           (rn_l2 rn) (rn_blk rn) top bot rl rz qz rs qr qn m8 kb (rn_keys rn) (g_inited FSG G) cl
           H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
           Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs W RD0 Wt Wsh RO RZ L T PC C1 C2 C3 C4 C5 C6 C8 C10 C11 C12 T7 T1 T2 C13 C14 T6 T5 T3 T4
           PH RC OK Hin Emu Room EV).
  -
    intros y Hy. pose proof (I (8 * y) Hy ltac:(replace (8 * y) with (y * 8) by lia; apply Z_mod_mult)) as B. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  -
    intros v Hv. pose proof (proj1 (Forall_forall _ _) Hfor v Hv) as V. specialize (III v V). rewrite (II v Hv) in III. destruct III as (_ & B).
    replace (rn_spb rn + c * 2 ^ 32 + 16 * v) with (rn_spb rn + c * 2 ^ 32 + 8 * (2 * v)) in B by lia. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  - exact DEP.
  - exact DR.
  - intros regs' Mr' b1 P10 P2 P1 PK GRW FR DI' PH' RC' OK' CP' Hb1 Hty CL1 CL3 CL4 CL2 SAB SHZ SHP PSH LCH.
    apply (K regs' Mr' b1 P10 P2 P1 PK). unfold art_malloc_out. fold c. fold cl. fold w. fold ab.
    split; [exact GRW|]. split; [intros x N; apply FR; intros F; apply N; [left|right]; exact F|]. split; [exact DI'|]. split; [exact PH'|]. split; [exact RC'|]. split; [exact OK'|]. split; [exact CP'|].
    split; [exact Hb1|]. split; [exact Hty|]. split; [exact CL1|]. split; [exact CL3|]. split; [exact CL4|]. split; [exact CL2|]. split; [exact SAB|].
    split; [exact SHZ|]. split; [exact SHP|]. split; [exact PSH|exact LCH].
Qed.

#[using="Type"] Lemma art_wm_entryU :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
         (Sp n rl rz qz rs qr qn m8 km top bot : Z) (kb : nat) (Lz : HeapIfaceA.asan_layout) (Kz : list Z) (k0 : nat),
    let c := AsanTab.class_id (rs + rz) in
    let cl := g_cls FSG G c in
    let w := art_ca_cptr c cl in
    let ab := rn_spb rn + c * 2 ^ 32 + w * 16 in
    art_alloc_rep FSG rn G LB Mr ->
    getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 n ->
    8 <= n -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 -> rs + rz <= 65536 ->
    rn_HI rn + 4096 <= Sp - 4096 -> Sp <= 2 ^ 47 -> Sp mod 16 = 0 ->
    top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    wrA Mr (Sp - 4096) 4096 -> HeapIfaceA.hl_segs Lz = ASEGS -> ukeyG Lz (rn_ar rn) 0x7a440 Mr Sp (U raw0) (U (getr R 8)) Kz ->
    g_depot FSG G = k0 -> (In Kz (rn_keys rn) \/ (1 <= k0)%nat) -> (kb <= if HeapIfaceAEr.HAR.kin Kz (rn_keys rn) then k0 else pred k0)%nat ->
    cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
    art_evok_list EVOK log (art_ca_events (rn_spb rn) c cl) ->
    (forall regs' (Mr' : word -> option byte) (b1 : Z),
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
        art_malloc_out rn Mr Mr' Sp n rz qz rs qr qn m8 km kb cl b1 ->
        DInvK (rn_l2 rn) (rn_blk rn) kb (Kz :: rn_keys rn) Mr' ->
        Q (log ++ art_ca_events (rn_spb rn) c cl) (mkst regs' raw0 Mr' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst R (0x7a378 : word) Mr rom).
Proof.
  intros Q log R Mr rom raw0 rn G LB Sp n rl rz qz rs qr qn m8 km top bot kb Lz Kz k0 c cl w ab
         REP H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W HSEGz UKz Edep HKin Hkb Emu Room EV K.
  pose proof (AsanTab.class_id_ok (rs + rz) ltac:(lia)) as (Hc & _). fold c in Hc.
  destruct REP as (ROK & ST & TH & (PH & PRIM & Wsh) & CH & _ & _ & DEP & _).
  rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & _ & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & T7). rewrite <- Etop in T3. rewrite <- Ebot in T4.
  destruct (PRIM c Hc) as (RC & OK & Hin & _). fold cl in RC, OK, Hin.
  specialize (CH c Hc). cbv zeta in CH. destruct CH as (I & II & _ & III). fold cl in I, II, III.
  unfold art_rt_depot in DEP. rewrite Edep in DEP.
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & _ & _ & Hfor & _).
  assert (ES : forall y, HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * rn_qs rn + c * 2 ^ 29 + y). { intros y. rewrite Espb. apply art_S_lin. }
  apply (art_malloc3K EVOK GR Lz (rn_ar rn) Q log R Mr rom raw0 Sp (rn_HI rn) n (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_loff rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km
           (rn_l2 rn) (rn_blk rn) top bot rl rz qz rs qr qn m8 k0 (rn_keys rn) Kz (g_inited FSG G) cl
           H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
           Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs W HSEGz (eq_sym Etop) (eq_sym Ebot) UKz Wt Wsh RO RZ L T PC C1 C2 C3 C4 C5 C6 C8 C10 C11 C12 T7 T1 T2 C13 C14 T6 T5 T3 T4
           PH RC OK Hin Emu Room EV).
  -
    intros y Hy. pose proof (I (8 * y) Hy ltac:(replace (8 * y) with (y * 8) by lia; apply Z_mod_mult)) as B. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  -
    intros v Hv. pose proof (proj1 (Forall_forall _ _) Hfor v Hv) as V. specialize (III v V). rewrite (II v Hv) in III. destruct III as (_ & B).
    replace (rn_spb rn + c * 2 ^ 32 + 16 * v) with (rn_spb rn + c * 2 ^ 32 + 8 * (2 * v)) in B by lia. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  - exact DEP.
  - exact HKin.
  - exact DR.
  - intros regs' Mr' b1 P10 P2 P1 PK GRW FR DI' PH' RC' OK' CP' Hb1 Hty CL1 CL3 CL4 CL2 SAB SHZ SHP PSH LCH.
    pose proof (DInvK_le _ _ _ _ _ _ DI' Hkb) as DIk. clear DI'.
    assert (DI' : DInvK (rn_l2 rn) (rn_blk rn) kb (rn_keys rn) Mr') by (apply (DInvK_incl _ _ _ _ _ _ DIk); intros x Hx; right; exact Hx).
    refine (K regs' Mr' b1 P10 P2 P1 PK _ DIk). unfold art_malloc_out. fold c. fold cl. fold w. fold ab.
    split; [exact GRW|]. split; [intros x N; apply FR; intros F; apply N; [left|right]; exact F|]. split; [exact DI'|]. split; [exact PH'|]. split; [exact RC'|]. split; [exact OK'|]. split; [exact CP'|].
    split; [exact Hb1|]. split; [exact Hty|]. split; [exact CL1|]. split; [exact CL3|]. split; [exact CL4|]. split; [exact CL2|]. split; [exact SAB|].
    split; [exact SHZ|]. split; [exact SHP|]. split; [exact PSH|exact LCH].
Qed.

#[using="Type"] Lemma art_wm_entry_small :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
         (Sp n rl rz qz rs qr qn m8 km top bot : Z) (kb : nat),
    let c := AsanTab.class_id (rs + rz) in
    let cl := g_cls FSG G c in
    let w := art_ca_cptr c cl in
    let ab := rn_spb rn + c * 2 ^ 32 + w * 16 in
    art_alloc_rep FSG rn G LB Mr ->
    getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 n ->
    1 <= n < 8 -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 -> rs + rz <= 65536 ->
    rn_HI rn + 4096 <= Sp - 4096 -> Sp <= 2 ^ 47 -> Sp mod 16 = 0 ->
    top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    wrA Mr (Sp - 4096) 4096 -> readable8 Mr Sp top ->
    g_depot FSG G = Datatypes.S kb -> cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
    art_evok_list EVOK log (art_ca_events (rn_spb rn) c cl) ->
    (forall regs' (Mr' : word -> option byte) (b1 : Z),
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
        art_malloc_out rn Mr Mr' Sp n rz qz rs qr qn m8 km kb cl b1 ->
        Q (log ++ art_ca_events (rn_spb rn) c cl) (mkst regs' raw0 Mr' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst R (0x7a378 : word) Mr rom).
Proof.
  intros Q log R Mr rom raw0 rn G LB Sp n rl rz qz rs qr qn m8 km top bot kb c cl w ab
         REP H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W RD0 Edep Emu Room EV K.
  pose proof (AsanTab.class_id_ok (rs + rz) ltac:(lia)) as (Hc & _). fold c in Hc.
  destruct REP as (ROK & ST & TH & (PH & PRIM & Wsh) & CH & _ & _ & DEP & _).
  rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & _ & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & T7). rewrite <- Etop in T3. rewrite <- Ebot in T4.
  destruct (PRIM c Hc) as (RC & OK & Hin & _). fold cl in RC, OK, Hin.
  specialize (CH c Hc). cbv zeta in CH. destruct CH as (I & II & _ & III). fold cl in I, II, III.
  unfold art_rt_depot in DEP. rewrite Edep in DEP.
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & _ & _ & Hfor & _).
  assert (ES : forall y, HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * rn_qs rn + c * 2 ^ 29 + y). { intros y. rewrite Espb. apply art_S_lin. }
  apply (art_malloc3_smallN EVOK GR Q log R Mr rom raw0 Sp (rn_HI rn) n (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_loff rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km
           (rn_l2 rn) (rn_blk rn) top bot rl rz qz rs qr qn m8 kb (rn_keys rn) (g_inited FSG G) cl
           H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
           Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs W RD0 Wt Wsh RO RZ L T PC C1 C2 C3 C4 C5 C6 C8 C10 C11 C12 T7 T1 T2 C13 C14 T6 T5 T3 T4
           PH RC OK Hin Emu Room EV).
  -
    intros y Hy. pose proof (I (8 * y) Hy ltac:(replace (8 * y) with (y * 8) by lia; apply Z_mod_mult)) as B. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  -
    intros v Hv. pose proof (proj1 (Forall_forall _ _) Hfor v Hv) as V. specialize (III v V). rewrite (II v Hv) in III. destruct III as (_ & B).
    replace (rn_spb rn + c * 2 ^ 32 + 16 * v) with (rn_spb rn + c * 2 ^ 32 + 8 * (2 * v)) in B by lia. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  - exact DEP.
  - exact DR.
  - intros regs' Mr' b1 P10 P2 P1 PK GRW FR DI' PH' RC' OK' CP' Hb1 Hty CL1 CL3 CL4 CL2 SAB SHZ SHP PSH LCH.
    apply (K regs' Mr' b1 P10 P2 P1 PK). unfold art_malloc_out. fold c. fold cl. fold w. fold ab.
    split; [exact GRW|]. split; [intros x N; apply FR; intros F; apply N; [left|right]; exact F|]. split; [exact DI'|]. split; [exact PH'|]. split; [exact RC'|]. split; [exact OK'|]. split; [exact CP'|].
    split; [exact Hb1|]. split; [exact Hty|]. split; [exact CL1|]. split; [exact CL3|]. split; [exact CL4|]. split; [exact CL2|]. split; [exact SAB|].
    split; [exact SHZ|]. split; [exact SHP|]. split; [exact PSH|exact LCH].
Qed.

#[using="Type"] Lemma art_wm_entry_smallU :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
         (Sp n rl rz qz rs qr qn m8 km top bot : Z) (kb : nat) (Lz : HeapIfaceA.asan_layout) (Kz : list Z) (k0 : nat),
    let c := AsanTab.class_id (rs + rz) in
    let cl := g_cls FSG G c in
    let w := art_ca_cptr c cl in
    let ab := rn_spb rn + c * 2 ^ 32 + w * 16 in
    art_alloc_rep FSG rn G LB Mr ->
    getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 n ->
    1 <= n < 8 -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 -> rs + rz <= 65536 ->
    rn_HI rn + 4096 <= Sp - 4096 -> Sp <= 2 ^ 47 -> Sp mod 16 = 0 ->
    top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    wrA Mr (Sp - 4096) 4096 -> HeapIfaceA.hl_segs Lz = ASEGS -> ukeyG Lz (rn_ar rn) 0x7a440 Mr Sp (U raw0) (U (getr R 8)) Kz ->
    g_depot FSG G = k0 -> (In Kz (rn_keys rn) \/ (1 <= k0)%nat) -> (kb <= if HeapIfaceAEr.HAR.kin Kz (rn_keys rn) then k0 else pred k0)%nat ->
    cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
    art_evok_list EVOK log (art_ca_events (rn_spb rn) c cl) ->
    (forall regs' (Mr' : word -> option byte) (b1 : Z),
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
        art_malloc_out rn Mr Mr' Sp n rz qz rs qr qn m8 km kb cl b1 ->
        DInvK (rn_l2 rn) (rn_blk rn) kb (Kz :: rn_keys rn) Mr' ->
        Q (log ++ art_ca_events (rn_spb rn) c cl) (mkst regs' raw0 Mr' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst R (0x7a378 : word) Mr rom).
Proof.
  intros Q log R Mr rom raw0 rn G LB Sp n rl rz qz rs qr qn m8 km top bot kb Lz Kz k0 c cl w ab
         REP H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W HSEGz UKz Edep HKin Hkb Emu Room EV K.
  pose proof (AsanTab.class_id_ok (rs + rz) ltac:(lia)) as (Hc & _). fold c in Hc.
  destruct REP as (ROK & ST & TH & (PH & PRIM & Wsh) & CH & _ & _ & DEP & _).
  rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & _ & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & T7). rewrite <- Etop in T3. rewrite <- Ebot in T4.
  destruct (PRIM c Hc) as (RC & OK & Hin & _). fold cl in RC, OK, Hin.
  specialize (CH c Hc). cbv zeta in CH. destruct CH as (I & II & _ & III). fold cl in I, II, III.
  unfold art_rt_depot in DEP. rewrite Edep in DEP.
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & _ & _ & Hfor & _).
  assert (ES : forall y, HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * rn_qs rn + c * 2 ^ 29 + y). { intros y. rewrite Espb. apply art_S_lin. }
  apply (art_malloc3_smallK EVOK GR Lz (rn_ar rn) Q log R Mr rom raw0 Sp (rn_HI rn) n (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_loff rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km
           (rn_l2 rn) (rn_blk rn) top bot rl rz qz rs qr qn m8 k0 (rn_keys rn) Kz (g_inited FSG G) cl
           H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
           Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs W HSEGz (eq_sym Etop) (eq_sym Ebot) UKz Wt Wsh RO RZ L T PC C1 C2 C3 C4 C5 C6 C8 C10 C11 C12 T7 T1 T2 C13 C14 T6 T5 T3 T4
           PH RC OK Hin Emu Room EV).
  -
    intros y Hy. pose proof (I (8 * y) Hy ltac:(replace (8 * y) with (y * 8) by lia; apply Z_mod_mult)) as B. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  -
    intros v Hv. pose proof (proj1 (Forall_forall _ _) Hfor v Hv) as V. specialize (III v V). rewrite (II v Hv) in III. destruct III as (_ & B).
    replace (rn_spb rn + c * 2 ^ 32 + 16 * v) with (rn_spb rn + c * 2 ^ 32 + 8 * (2 * v)) in B by lia. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  - exact DEP.
  - exact HKin.
  - exact DR.
  - intros regs' Mr' b1 P10 P2 P1 PK GRW FR DI' PH' RC' OK' CP' Hb1 Hty CL1 CL3 CL4 CL2 SAB SHZ SHP PSH LCH.
    pose proof (DInvK_le _ _ _ _ _ _ DI' Hkb) as DIk. clear DI'.
    assert (DI' : DInvK (rn_l2 rn) (rn_blk rn) kb (rn_keys rn) Mr') by (apply (DInvK_incl _ _ _ _ _ _ DIk); intros x Hx; right; exact Hx).
    refine (K regs' Mr' b1 P10 P2 P1 PK _ DIk). unfold art_malloc_out. fold c. fold cl. fold w. fold ab.
    split; [exact GRW|]. split; [intros x N; apply FR; intros F; apply N; [left|right]; exact F|]. split; [exact DI'|]. split; [exact PH'|]. split; [exact RC'|]. split; [exact OK'|]. split; [exact CP'|].
    split; [exact Hb1|]. split; [exact Hty|]. split; [exact CL1|]. split; [exact CL3|]. split; [exact CL4|]. split; [exact CL2|]. split; [exact SAB|].
    split; [exact SHZ|]. split; [exact SHP|]. split; [exact PSH|exact LCH].
Qed.

End Entry.
