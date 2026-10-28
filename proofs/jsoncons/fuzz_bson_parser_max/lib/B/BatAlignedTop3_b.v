(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatPoison_b BatAllocA_b BatAllocB_b BatAllocG_b BatAllocV_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatCellEx_b BatByteCell_b BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b BatUnwind_b BatUnwindG_b BatMalloc_b BatAllocate3_b BatMallocTop3_b BatAllocA16_b BatAllocB16_b BatAllocate3A16_b BatAligned16_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Theorem art_aligned16_3 :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M0 rom : word -> option byte) (raw0 : word)
         (S HI n tp key tsd ctx t loff spb ris qs km l2 blk top bot rl rz qz rs qr qn m8 q16 : Z) (kb : nat) (inited : bool) (cl : art_cls),
    let c := AsanTab.class_id (rs + 16 + rz) in
    let w := art_ca_cptr c cl in
    let ab := spb + c * 2 ^ 32 + w * 16 in
    let shb := 2147450880 + 8192 * qs + c * 2 ^ 29 in
    getr regs 1 = raw0 -> ret_ok raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 16 -> getr regs 11 = Z_to_bv 64 n ->
    (* [comment removed for export] *)
    8 <= n -> n mod 16 = 0 -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> rs = 16 * q16 -> n <= rs <= n + 7 -> rs + 16 + rz <= 65536 ->
    (* [comment removed for export] *)
    art_geo HI t ctx tp tsd spb ris qs -> HI + 4096 <= S - 4096 -> S <= 2 ^ 47 -> S mod 16 = 0 ->
    0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    0 <= loff -> 0x10000 <= tp + loff -> tp + loff + 4 <= 0x696000 -> 0x661b28 <= tp - 88 -> 0x661b28 <= tsd ->
    l2 + 2 ^ 20 <= HI -> blk + 2 ^ 23 <= HI ->
    apart l2 (2 ^ 20) t 4096 -> apart l2 (2 ^ 20) ctx 4096 -> apart l2 (2 ^ 20) spb (2 ^ 37 + 4096) -> apart l2 (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
    apart blk (2 ^ 23) t 4096 -> apart blk (2 ^ 23) ctx 4096 -> apart blk (2 ^ 23) spb (2 ^ 37 + 4096) -> apart blk (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
    (* [comment removed for export] *)
    wrA M0 (S - 4096) 4096 -> readable8 M0 S top -> wrA M0 t 4096 -> wrA M0 (2147450880 + 8192 * qs) (2 ^ 34) ->
    art_alloc_rodata M0 -> cellA M0 0x104c0 1 4 -> art_rz_rodata M0 -> art_layout M0 -> art_tsd M0 tp key tsd ctx t -> art_prim_consts spb ris M0 ->
    cellA M0 0x140918 1 1 -> cellA M0 0x1c1ea2 1 0 -> cellA M0 (1295832 + 3616) 8 (2 ^ 40) -> cellA M0 (1295832 + 3624) 2 16 -> cellA M0 (1295832 + 3626) 2 2048 ->
    cellA M0 0x1d1700 8 0 -> cellA M0 (0x13d438 + 44) 4 4096 -> cellA M0 (0x13d438 + 52) 4 190 -> cellA M0 (0x13d438 + 85) 1 1 ->
    cellA M0 0x138120 8 loff -> cellA M0 (tp + loff) 4 0 -> cellA M0 t 8 ctx -> cellA M0 (ctx + 8) 4 0 ->
    cellA M0 0x14093c 4 30 -> cellA M0 (0x1d1768 + 34) 1 1 -> cellA M0 (t + 3168) 1 0 -> cellA M0 (t + 40) 1 0 -> cellA M0 (t + 8) 8 top -> cellA M0 (t + 16) 8 bot ->
    (* [comment removed for export] *)
    art_pc_hdr (t + 208) inited M0 -> art_cls_rep (t + 208) spb ris c cl M0 -> art_cls_ok c cl -> (cl_cache cl <> [] -> inited = true) -> cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
    art_evok_list EVOK log (art_ca_events spb c cl) ->
    (forall y, cl_au cl <= 8 * y < cl_mu cl -> cellA M0 (shb + y) 1 250) ->
    (forall v, In v (cl_cache cl ++ cl_free cl) -> cellA M0 (shb + 2 * v) 1 250) ->
    (* [comment removed for export] *)
    DInvD l2 blk (Datatypes.S kb) M0 -> DRoD M0 ->
    (forall regs' (M' : word -> option byte) (b1 : Z),
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 S -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M0 M' ->
        (forall x : word, ~ (S - 4096 <= U x < S) -> ~ art_alloc3_fp (S - 2144) t spb ris qs c km ab rz n rs l2 blk (U x) -> M' x = M0 x) ->
        DInvD l2 blk kb M' ->
        art_pc_hdr (t + 208) true M' -> art_cls_rep (t + 208) spb ris c (art_cls_pop (art_ca_pre c cl)) M' -> art_cls_ok c (art_cls_pop (art_ca_pre c cl)) ->
        art_cptr_ok (AsanTab.class_size c) (cl_au (art_ca_pre c cl)) w ->
        0 <= b1 < 256 -> b1 mod 4 = 1 ->
        cellA M' (ab + rz - 16) 1 2 -> cellA M' (ab + rz - 15) 1 b1 -> cellA M' (ab + rz - 14) 2 0 -> cellA M' (ab + rz - 12) 4 n ->
        cellA M' (shb + 2 * w) 1 250 ->
        (forall j, 0 <= j < qn -> cellA M' (shb + 2 * w + 2 * qz + j) 1 0) -> (m8 <> 0 -> cellA M' (shb + 2 * w + 2 * qz + qn) 1 m8) ->
        (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
           forall j, 0 <= j < 32768 -> ~ (2 * w + 2 * qz <= 32768 * km + j < 2 * w + 2 * qz + qr) -> cellA M' (shb + 32768 * km + j) 1 250) ->
        (rz <> 16 -> cellA M' ab 8 0xcc6e96b9cc6e96b9 /\ cellA M' (ab + 8) 8 (ab + rz - 16)) ->          (* [comment removed for export] *)
        Q (log ++ art_ca_events spb c cl) (mkst regs' raw0 M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x79f60 : word) M0 rom).
Proof.
  intros Q log regs M0 rom raw0 S HI n tp key tsd ctx t loff spb ris qs km l2 blk top bot rl rz qz rs qr qn m8 q16 kb inited cl c w ab shb
         H1 Hret H2 H4 H10 H11
         Hn Hn16 Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim
         GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
         Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
         W RD0 Wt Wsh RO C1046 RZRO L TSD PC Ci Cr Cmax Cmin16 Cmax2048 Chook Cmfs Cfb Cpp Cg Clsan Ctctx Ctid Cctx30 Cfast Cunw C40 Ctop Cbot
         PH RC OK Hin Emu Room EV PZ1 PZ2 DI DR K.
  assert (Eab : ab = spb + c * 2 ^ 32 + w * 16) by reflexivity.
  assert (Eshb : shb = 2147450880 + 8192 * qs + c * 2 ^ 29) by reflexivity.
  clearbody ab shb.
  pose proof (AsanTab.class_id_ok (rs + 16 + rz) ltac:(lia)) as (Hc & Hfit & _). fold c in Hc, Hfit.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G15; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
  change (hid (t + 4096 <= 0x10000 \/ 0x696000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx)) in G15.
  clear G10 G16.
  pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
  assert (Hkm : 0 <= km) by lia. assert (Hkm' : 262144 * km <= 3758096384) by lia.
  pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
  pose proof TSD as (_ & _ & _ & _ & _ & TR).
  pose proof PC as (_ & _ & _ & _ & _ & Cpg1 & Cpg2 & _).
  (* [comment removed for export] *)
  destruct (art_icu1_16 regs M0 rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 H11 ltac:(lia) HS47 ltac:(lia) G7 ltac:(lia) G9 ltac:(unfold apart; lia)
              ltac:(unfold apart; lia) G15 G18 G19 G20 G21 G22 ltac:(lia) Htop W Wt TSD Ci Cctx30 ltac:(pose proof L as L'; unfold art_layout in L'; tauto) Cfast Cunw C40 Ctop Cbot)
    as (r1 & M1 & RUN1 & Q1_1 & Q1_2 & Q1_10 & Q1_11 & Q1_12 & Q1_13 & Q1_14 & Q1_15 & Q1_24 & Q1_4 & K1 & G01 & A1
        & F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & E36 & E44 & E52 & E60 & E68 & E76 & E84 & E92 & E00 & E08 & E28 & E20 & E16' & W1).
  eapply ar_steps; [exact RUN1|].
  assert (T1 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= S - 2288 \/ S <= a) -> (a + Z.of_nat k <= t + 3168 \/ t + 3169 <= a) ->
            cellA M0 a k v -> cellA M1 a k v).
  { intros a k v Ha Hak O1 O2 C. apply (cell_agree M0 M1); [|lia|lia|exact C]. intros x Hx. apply A1; lia. }
  (* [comment removed for export] *)
  assert (HS8 : S mod 8 = 0). { clear - HS16. rewrite <- (Z.div_exact S 16) in HS16 by lia. rewrite HS16. replace (16 * (S / 16)) with ((2 * (S / 16)) * 8) by lia. apply Z_mod_mult. }
  assert (RD1 : readable8 M1 (S - 16) top).
  { intros a Ha1 Ha2 Ha8. destruct (Z.lt_ge_cases a S) as [Lo|Hi].
    - assert (a = S - 16 \/ a = S - 8) as [->| ->].
      { clear - Ha1 Lo Ha8 HS8. rewrite <- (Z.div_exact a 8) in Ha8 by lia. rewrite <- (Z.div_exact S 8) in HS8 by lia. lia. }
      + eexists. exact F16.
      + eexists. exact F8.
    - destruct (RD0 a ltac:(lia) ltac:(lia) Ha8) as [w' Cw]. exists w'. apply T1; [lia|cbn; lia|cbn; lia| clear - Hi G8 HHI; cbn; lia | exact Cw]. }
  destruct (art_unwind_fast_any r1 M1 rom (0x81f98 : bv 64)%bv (S - 2224) (S - 2136) 0x79ff8 S top bot
              Q1_1 ltac:(unfold ret_ok; bveq) Q1_2 Q1_10 Q1_11 Q1_12 Q1_13 Q1_14 Q1_15
              ltac:(lia) ltac:(lia) ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) HS8 ltac:(lia) ltac:(lia)
              ltac:(eapply wr_sub; [exact W1|lia|lia]) ltac:(eapply wr_sub; [exact W1|lia|lia]) (fun _ _ => RD1)
              ltac:(apply T1; [lia|cbn; lia|cbn; lia|clear - At_i; unfold apart in At_i; cbn; lia|exact Cpg1]) ltac:(apply T1; [lia|cbn; lia|cbn; lia|clear - At_i; unfold apart in At_i; cbn; lia|exact Cpg2]))
    as (r2 & M2 & RUN2 & Q2_2 & Q2_1 & K2 & G12 & A2 & (sz & Hsz & Csz & TRC)).
  eapply ar_steps; [exact RUN2|].
  assert (T2 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= S - 2288 \/ S - 2224 <= a) -> (a + Z.of_nat k <= S - 2128 \/ S - 2124 <= a) ->
            (a + Z.of_nat k <= S - 2120 \/ S - 1880 <= a) -> cellA M1 a k v -> cellA M2 a k v).
  { intros a k v Ha Hak O1 O2 O3 C. apply (cell_agree M1 M2); [|lia|lia|exact C]. intros x Hx. apply A2; lia. }
  (* [comment removed for export] *)
  pose proof (art_icu2_16_fn r2 M2 rom S n t (U (getr regs 23)) (U (getr regs 24)) Q2_2 ltac:(rewrite K2 by inl; exact Q1_24)
               ltac:(lia) HS47 ltac:(lia) Hn16 G7 ltac:(lia) ltac:(unfold apart; lia) (u64_range _) (u64_range _)
               ltac:(eapply wr_grows; [exact G12|exact W1]) ltac:(eapply wr_grows; [exact G12|]; eapply wr_grows; [exact G01|exact Wt])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E36]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E44])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E52]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E60])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E68]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E76])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E84]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E92])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E00]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E08])) as RUN3.
  match type of RUN3 with msteps _ _ (mkst ?R _ ?X _) => set (r3 := R) in RUN3; set (M3 := X) in RUN3 end.
  eapply ar_steps; [exact RUN3|].
  assert (A03 : art_agree [(S - 2288, 2288); (t + 3168, 1)] M0 M3).
  { intros x Hx. cbn [art_out fst snd] in Hx. unfold M3. rewrite 5 Wn_outside by (cbn; clear - Hx G7 G8 G2 HHI G1 HS47; lia). rewrite A2 by (clear - Hx; lia). apply A1; clear - Hx; lia. }
  assert (G03 : mem_grows M0 M3). { eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G12|]. unfold M3. zgrows. }
  (* [comment removed for export] *)
  assert (T_img3 : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x696000 -> cellA M0 a k v -> cellA M3 a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr1 _ M0 M3 a k v A03); [|exact C]. revert Ha Hk. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Ha Hk. zarith_f. }
  assert (RO3 : art_alloc_rodata M3).
  { unfold art_alloc_rodata in *. destruct RO as (a1 & a2 & a3). repeat split; apply T_img3; first [exact a1|exact a2|exact a3|clear; lia|clear; cbn; lia]. }
  assert (RZRO3 : art_rz_rodata M3).
  { unfold art_rz_rodata in *. destruct RZRO as (a1 & a2 & a3). repeat split; apply T_img3; first [exact a1|exact a2|exact a3|clear; lia|clear; cbn; lia]. }
  assert (L3 : art_layout M3).
  { eapply art_layout_fp; [exact A03| |exact L]. intros z Hz. apply (art_gap_out _ 0x10000 (0x211b08 - 0x10000)); [|clear - Hz; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
  assert (T3 : art_tsd M3 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M3 tp key tsd ctx t A03); [| | | |exact TSD]; clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
  assert (PC3 : art_prim_consts spb ris M3).
  { eapply art_prim_consts_fp; [exact A03| |exact PC]. intros z Hz. apply (art_gap_out _ 0x10000 (0x696000 - 0x10000)); [|clear - Hz; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
  assert (W3 : wrA M3 (S - 2176 - 1920) 1920) by (eapply wr_grows; [exact G03|]; eapply wr_sub; [exact W|lia|lia]).
  assert (Wt3 : wrA M3 t 4096) by (eapply wr_grows; [exact G03|exact Wt]).
  assert (Wsh3 : wrA M3 (2147450880 + 8192 * qs) (2 ^ 34)) by (eapply wr_grows; [exact G03|exact Wsh]).
  assert (Clsan3 : cellA M3 (tp + loff) 4 0) by (apply T_img3; [clear - Hloff'; lia|clear - Hloff''; cbn; lia|exact Clsan]).
  assert (Ctctx3 : cellA M3 t 8 ctx). { apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Ctctx]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
  assert (Ctid3 : cellA M3 (ctx + 8) 4 0). { apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Ctid]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
  assert (PH3 : art_pc_hdr (t + 208) inited M3).
  { apply (art_pc_hdr_tr _ (t + 208) inited M0 M3 ltac:(clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; lia) ltac:(clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; lia) A03); [|exact PH]. intros c' Hc'. revert Hc'. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Hc'. zarith_f. }
  assert (RC3 : art_cls_rep (t + 208) spb ris c cl M3).
  { apply (art_cls_rep_tr [(S - 2288, 2288); (t + 3168, 1)] (t + 208) spb ris c cl M0 M3); first [ exact RC | exact G03 | exact A03 | exact Hl16 | idtac ];
      first [ clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; lia | clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f ]. }
  assert (PZ1_3 : forall y, cl_au cl <= 8 * y < cl_mu cl -> cellA M3 (shb + y) 1 250).
  { intros y Hy. apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|apply PZ1; exact Hy]. revert Hy. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Hy. zarith_f. }
  pose proof (art_class_size_facts c Hc) as (Hcsz & _).
  assert (PZ2_3 : forall v, In v (cl_cache cl ++ cl_free cl) -> cellA M3 (shb + 2 * v) 1 250).
  { intros v Hv. apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|apply PZ2; exact Hv].
    pose proof (proj1 (Forall_forall _ _) Hfor v Hv) as (Hv0 & Hv1 & _). revert Hv0 Hv1 Hcsz. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Hv0 Hv1 Hcsz. zarith_f. }
  assert (DI3 : DInvD l2 blk (Datatypes.S kb) M3).
  { apply (DInvD_frame l2 blk (Datatypes.S kb) M0 M3 DI). intros x Dx. apply A03. revert Dx. apply art_dpriv_out; clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
  assert (DR3 : DRoD M3).
  { apply (DRoD_frame M0 M3 DR). intros x Hx. apply A03. apply (art_gap_out _ 0x10000 (0x211b08 - 0x10000)); [|clear - Hx; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
  assert (Cstk3 : cellA M3 (S - 2136) 8 (S - 2120)).
  { unfold M3. do 5 (apply cell_Wn_other; [clear - G7 HHI G1; lia|clear - G8 G2 HS47; cbn; lia|clear - HHI G1; lia|clear - HS47; cbn; lia|unfold apart; clear - G8 HHI; cbn; lia|]).
    apply T2; [clear - HHI G1; lia|clear - HS47; cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E28]. }
  assert (Cszt3 : cellA M3 (S - 2136 + 8) 8 sz).
  { replace (S - 2136 + 8) with (S - 2128) by lia. unfold M3.
    do 5 (apply cell_Wn_other; [clear - G7 HHI G1; lia|clear - G8 G2 HS47; cbn; lia|clear - HHI G1; lia|clear - HS47; cbn; lia|unfold apart; clear - G8 HHI; cbn; lia|]).
    replace sz with (sz + 0 * 2 ^ 32) by lia. replace (S - 2136 + 8) with (S - 2128) in Csz by lia.
    apply cell8_of_cells4; [clear - HHI G1; lia|clear - HS47; lia|clear - Hsz; lia|lia|exact Csz|].
    replace (S - 2128 + 4) with (S - 2124) by lia. apply T2; [clear - HHI G1; lia|clear - HS47; cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E16']. }
  assert (DP3 : DPreD blk M3 (S - 2120) sz).
  { unfold DPreD. split; [exact Hsz|]. split.
    { clear - HS8. rewrite <- (Z.div_exact S 8) in HS8 by lia. rewrite HS8. replace (8 * (S / 8) - 2120) with ((S / 8 - 265) * 8) by lia. apply Z_mod_mult. }
    split; [clear - HHI G1; lia|]. split; [clear - HS47 Hsz; lia|]. split; [unfold apart; clear - Dblk HHI Hsz; lia|].
    intros i Hi. destruct (TRC i Hi) as [w' Cw]. unfold rcell. eexists.
    assert (C3' : cellA M3 (S - 2120 + 8 * i) 8 (U w')).
    { unfold M3. do 5 (apply cell_Wn_other; [clear - G7 HHI G1 Hi; lia|clear - G8 G2 HS47 Hi Hsz; cbn; lia|clear - HHI G1 Hi; lia|clear - HS47 Hi Hsz; cbn; lia|unfold apart; clear - G8 HHI Hi Hsz; cbn; lia|]).
      replace (S - 2120 + 8 * i) with (S - 2136 + 16 + 8 * i) by lia. exact Cw. }
    exact C3'. }
  (* [comment removed for export] *)
  rewrite Eshb in PZ1_3, PZ2_3.
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
  assert (C1046_3 : cellA M3 0x104c0 1 4) by (apply T_img3; [clear; lia|clear; cbn; lia|exact C1046]).
  apply (art_allocate3_16 EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r3 M3 rom (0x531c4 : bv 64)%bv (S - 2176) HI n (S - 2136) tp key tsd ctx t loff spb ris qs km l2 blk
           (S - 2120) sz rl rz qz rs qr qn m8 q16 kb inited cl
           ltac:(unfold r3; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; rewrite K2 by inl; exact Q1_4)
           ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
           ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
           Hn Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim
           GEO ltac:(clear - HHI; lia) ltac:(clear - HHI; lia) ltac:(clear - HS47; lia) ltac:(clear; lia) ltac:(clear; lia)
           ltac:(clear - HHI G1 HS47; lia) ltac:(clear - Hsz; lia) ltac:(clear; lia) ltac:(clear - Hsz; lia)
           Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
           W3 Wt3 Wsh3 RO3 C1046_3 RZRO3 L3 T3 PC3
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Ci]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cr])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmax]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmin16])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmax2048]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Chook])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmfs]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cfb])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cpp]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cg])
           Clsan3 Ctctx3 Ctid3 Cstk3 Cszt3
           PH3 RC3 OK Hin Emu Room EV PZ1_3 PZ2_3 DI3 DP3 DR3).
  intros r4 M4 b1 P4_10 P4_2 P4_1 K4 G34 AG34 DI4 PH4 RC4 OK4 CP4 Hb1 Hty CL1 CL3 CL4 CL2 SAB4 SHZ SHP PSH LCH.
  fold c in P4_10, AG34, RC4, OK4, CP4, CL1, CL2, CL3, CL4, SAB4, SHZ, SHP, PSH, LCH. fold w in P4_10, AG34, CP4, CL1, CL2, CL3, CL4, SAB4, SHZ, SHP, PSH, LCH.
  rewrite <- ?Eab in P4_10, AG34, CL1, CL2, CL3, CL4, LCH. rewrite <- ?Eshb in SAB4, SHZ, SHP, PSH.
  (* [comment removed for export] *)
  pose proof CP4 as (Hw0 & Hwsz & _).
  pose proof OK4 as OK'. unfold art_cls_ok in OK'. cbn [art_cls_pop cl_cache cl_free cl_au cl_mu cl_mfa] in OK'.
  destruct OK' as (_ & (_ & Haumu') & _ & _ & _ & Hmu3' & _).
  assert (Hub8 : (ab + rz) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz).
  { rewrite Eab, Espb, Erz16. replace (65536 * qs + c * 2 ^ 32 + w * 16 + 16 * qz) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hqr8 : rs / 8 = qr). { rewrite Ers, Z.mul_comm. apply Z.div_mul. lia. }
  assert (ABOVE : forall x, S - 2176 <= x -> ~ art_alloc3_fp16 (S - 2176) t spb ris qs c km ab rz n rs l2 blk x).
  { intros x Hx FX. apply art_alloc3_fp16_sub in FX. revert FX. apply (art_alloc3_fp_above (S - 2176) HI t spb ris qs c km ab rz n rs l2 blk _ _ x Hc Hkm Hkm' ltac:(clear - HHI; lia) G1 Espb G4 Eris G6 G8 Dl2 Dblk
             ltac:(clear - Eab Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hrs; lia) Hub8 Hqr8 ltac:(clear - Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hrs Hqz Ers Erz16 Espb Eris G6 G2 Hcsz; lia) Hx). }
  assert (T34 : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> S - 2176 <= a -> cellA M3 a k v -> cellA M4 a k v).
  { intros a k v Ha Hak O1 C. apply (art_cell_agree _ M3 M4); [|exact Ha|exact Hak|exact C]. intros x Hx. apply AG34. apply ABOVE. clear - Hx O1. lia. }
  assert (TF : forall a v, S - 64 <= a -> a + 8 <= S -> cellA M1 a 8 v -> cellA M4 a 8 v).
  { intros a v Ha Ha' C. apply T34; [clear - Ha HHI G1; lia|clear - Ha' HS47; cbn; lia|clear - Ha; lia|]. unfold M3.
    do 5 (apply cell_Wn_other; [clear - G7 HHI G1 Ha; lia|clear - G8 G2 HS47 Ha'; cbn; lia|clear - HHI G1 Ha; lia|clear - HS47 Ha'; cbn; lia|unfold apart; clear - G8 HHI Ha Ha'; cbn; lia|]).
    apply T2; [clear - HHI G1 Ha; lia|clear - HS47 Ha'; cbn; lia|clear - Ha; cbn; lia|clear - Ha; cbn; lia|clear - Ha; cbn; lia|exact C]. }
  pose proof (art_ic3_16_fn r4 M4 rom raw0 S n (ab + rz) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)) (U (getr regs 22))
               P4_2 P4_10 ltac:(clear - Eab Espb G4 Hc Hw0 Hwsz Haumu' Hmu3' Hqz Erz16 Eris G6 G2 Hcsz; lia) ltac:(clear - HHI G1; lia) HS47 Hret ltac:(clear - Hn Hrs Hprim Hqz Erz16; lia)
               (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
               ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
               ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
               ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
               ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
               ltac:(apply TF; [clear; lia|clear; lia|exact F8]) ltac:(apply TF; [clear; lia|clear; lia|exact F16]) ltac:(apply TF; [clear; lia|clear; lia|exact F24])
               ltac:(apply TF; [clear; lia|clear; lia|exact F32]) ltac:(apply TF; [clear; lia|clear; lia|exact F40]) ltac:(apply TF; [clear; lia|clear; lia|exact F48])
               ltac:(apply TF; [clear; lia|clear; lia|exact F56]) ltac:(apply TF; [clear; lia|clear; lia|exact F64])) as RUN5.
  eapply ar_steps; [exact RUN5|]. apply ar_done.
  apply (K _ M4 b1).
  - gres. exact P4_10.
  - gres. reflexivity.
  - gres. reflexivity.
  - intros r Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; try apply Z_to_bv_bv_unsigned;
      rewrite K4 by inl; unfold r3; gres; try apply Z_to_bv_bv_unsigned; rewrite K2 by inl; first [ rewrite K1 by inl; reflexivity | rewrite Q1_4; symmetry; exact H4 ].
  - eapply mem_grows_trans; [exact G03|exact G34].
  - intros x N1 N2.
    rewrite (AG34 x ltac:(intros FX; apply art_alloc3_fp16_window in FX; destruct FX as [FX|FX]; [exact (N1 FX)|exact (N2 FX)])).
    destruct (Z.eq_dec (U x) (t + 3168)) as [e|ne].
    + assert (Ex : x = Z_to_bv 64 (t + 3168)) by (rewrite <- e; symmetry; apply Z_to_bv_bv_unsigned). rewrite Ex.
      rewrite (art_byte_of_cell1 M0 (t + 3168) 0 ltac:(clear - At_i; unfold apart in At_i; lia) ltac:(clear - G7 G8 G2; lia) ltac:(clear; lia) Cunw).
      apply art_byte_of_cell1; [clear - At_i; unfold apart in At_i; lia|clear - G7 G8 G2; lia|clear; lia|]. unfold M3. clear - G7 G8 G2 HHI G1 HS47. zcell.
    + apply A03. cbn [art_out fst snd]. clear - N1 ne. repeat split; lia.
  - exact DI4.
  - exact PH4.
  - exact RC4.
  - exact OK4.
  - exact CP4.
  - exact Hb1.
  - exact Hty.
  - exact CL1.
  - exact CL3.
  - exact CL4.
  - exact CL2.
  - exact SAB4.
  - exact SHZ.
  - exact SHP.
  - exact PSH.
  - exact LCH.
Qed.
End Spec.
