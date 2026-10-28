(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatRzLog_b BatAllocA_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatCellEx_b BatByteCell_b
     BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b BatUnwind_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatSecAllocPost_b BatSecRSpec_b BatAllocate3L_b BatMallocTop3L_b
     BatInv_b BatInvMallocPure_b BatInvMallocFp_b BatInvMalloc_b BatInvMallocL_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Entry.
Variable FSG : Type.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_wm_entry_sec :
  forall (Q : list aev -> machine_state -> Prop) (P : Z -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
         (Sp n rl rz qz rs qr qn m8 nd q msz top bot : Z) (kb : nat),
    let nch := Z.of_nat (length (g_sec FSG G)) in
    let cm := g_sec_committed FSG G in
    art_alloc_rep FSG rn G LB Mr ->
    getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 n ->
    8 <= n < 2 ^ 32 -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 2 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 -> 65536 < rs + rz ->
    nd = rs + rz + rz -> 4096 * (q - 1) < nd <= 4096 * q -> msz = 4096 * q + 4096 ->
    rn_HI rn + 4096 <= Sp - 4096 -> Sp <= 2 ^ 47 -> Sp mod 16 = 0 ->
    top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    wrA Mr (Sp - 4096) 4096 -> readable8 Mr Sp top ->
    g_depot FSG G = Datatypes.S kb -> nch + 1 <= 16384 ->
    (forall Mx r, GR log Mx msz r -> P r) ->
    (forall r, P r -> art_sec_grant3 (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) (rn_spb rn) (rn_l2 rn) (rn_blk rn) msz r) ->
    EVOK log (AMmapNull msz 0) ->
    (cm = false -> forall r, P r -> EVOK (log ++ [AMmapNull msz r]) (AMmapFixed (rn_parr rn + 8 * nch) 131072)) ->
    (forall r regs' (Mr' : word -> option byte) (b1 : Z), P r ->
        getr regs' 10 = Z_to_bv 64 (4096 + r + rz) -> getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr R x) ->
        art_malloc_out_sec rn Mr Mr' Sp n rz qz qn m8 nd msz r nch cm kb b1 ->
        Q (log ++ art_sec_events msz r (rn_parr rn) nch cm) (mkst regs' raw0 Mr' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst R (0x799f4 : word) Mr rom).
Proof.
  intros Q P log R Mr rom raw0 rn G LB Sp n rl rz qz rs qr qn m8 nd q msz top bot kb nch cm
         REP H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W RD0 Edep Hroom HGR HP EV1 EV2 K.
  destruct REP as (ROK & ST & TH & (PH & PRIM & Wsh) & CH & SEC & _ & DEP & _).
  pose proof (art_run_ok_tail rn ROK) as (Il2 & Iblk & _).
  rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & _ & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & Cnm1 & Cnm2 & _).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & T7). rewrite <- Etop in T3. rewrite <- Ebot in T4.
  destruct SEC as (S0 & S8 & S56 & S48 & S616 & S16 & CMT & WPA & _).
  unfold art_rt_depot in DEP. rewrite Edep in DEP.
  assert (APp : appmem (rn_parr rn) (2 ^ 23)). { destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap. unfold appmem, BatPoison_b.SB, BatPoison_b.kHighMemBeg. lia. }
  assert (Hnch0 : cm = false -> nch = 0).
  { intros E. unfold nch. destruct (g_sec FSG G) as [|s0 l0] eqn:Eg; [reflexivity|]. exfalso. unfold cm in E. rewrite CMT in E by discriminate. discriminate E. }
  apply (art_malloc3_sec EVOK GR Q P log R Mr rom raw0 Sp (rn_HI rn) n (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_loff rn) (rn_spb rn) (rn_ris rn) (rn_qs rn)
           (rn_l2 rn) (rn_blk rn) top bot rl rz qz rs qr qn m8 nd q msz 0x1a476 (rn_parr rn) nch kb cm
           H1 Hret H2 H4 H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
           Dl2 Dblk Al2t Al2c Al2s Il2 Abt Abc Abs Iblk Plo Pal Phi APp Apt Apc Apl Apb ltac:(unfold nch in *; lia) Hnch0 ltac:(lia)
           W RD0 Wt WPA RO RZ L T PC C1 C2 C3 C4 C5 C6 C8 C10 C11 C12 T7 T1 T2 C13 C14 T6 T5 T3 T4 Cnm1 Cnm2
           S0 S8 S16 S56 S48 S616 HGR HP EV1 EV2 DEP DR).
  intros r regs' Mr' b1 Pr ab P10 P2 P1 PK GRW AG WIN DI' WSr WSs Cr0 Cr8 Cr16 Cr24 Hb1 Hty CL1 CL3 CL4 CL2 SHZ SHP SS0 SS8 SS16 SS56 SS48 SS616 Sslot WSp.
  subst ab.
  apply (K r regs' Mr' b1 Pr P10 P2 P1 PK). unfold art_malloc_out_sec.
  repeat (split; [assumption|]). assumption.
Qed.
End Entry.
