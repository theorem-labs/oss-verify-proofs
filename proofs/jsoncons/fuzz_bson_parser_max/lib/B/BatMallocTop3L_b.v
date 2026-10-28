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
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatPoison_b BatAllocA_b BatAllocB_b BatAllocG_b BatAllocV_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatCellEx_b BatByteCell_b BatDepotA_b BatDepot_b BatUnwind_b BatUnwindG_b BatMalloc_b BatAllocate3_b BatSecAllocPost_b BatSecRSpec_b BatAllocate3L_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_malloc3L_fp (S t parr nch r msz l2 blk : Z) (committed : bool) : list (Z * Z) :=
  [ (S - 4096, 4096); (0x13c618, 624); (0x13c888 + 16, 16); (t + 2800, 112); (r, msz); (art_shlo r, art_shhi r msz - art_shlo r);
    (parr + 8 * nch, if committed then 8 else 131072); (0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23) ].

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Theorem art_malloc3_sec :
  forall (Q : list aev -> machine_state -> Prop) (P : Z -> Prop) (log : list aev) regs (M0 rom : word -> option byte) (raw0 : word)
         (S HI n tp key tsd ctx t loff spb ris qs l2 blk top bot rl rz qz rs qr qn m8 nd q msz nm parr nch : Z) (kb : nat) (committed : bool),
    getr regs 1 = raw0 -> ret_ok raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 n ->
    8 <= n < 2 ^ 32 -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 2 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 -> 65536 < rs + rz ->
    nd = rs + rz + rz -> 4096 * (q - 1) < nd <= 4096 * q -> msz = 4096 * q + 4096 ->
    art_geo HI t ctx tp tsd spb ris qs -> HI + 4096 <= S - 4096 -> S <= 2 ^ 47 -> S mod 16 = 0 ->
    0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    0 <= loff -> 0x10000 <= tp + loff -> tp + loff + 4 <= 0x696000 -> 0x661b28 <= tp - 88 -> 0x661b28 <= tsd ->
    l2 + 2 ^ 20 <= HI -> blk + 2 ^ 23 <= HI ->
    apart l2 (2 ^ 20) t 4096 -> apart l2 (2 ^ 20) ctx 4096 -> apart l2 (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> 0x696000 <= l2 ->
    apart blk (2 ^ 23) t 4096 -> apart blk (2 ^ 23) ctx 4096 -> apart blk (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> 0x696000 <= blk ->
    0x696000 <= parr -> parr mod 4096 = 0 -> parr + 2 ^ 23 <= HI -> appmem parr (2 ^ 23) -> apart parr (2 ^ 23) t 4096 ->
    apart parr (2 ^ 23) ctx 4096 -> apart parr (2 ^ 23) l2 (2 ^ 20) -> apart parr (2 ^ 23) blk (2 ^ 23) ->
    0 <= nch < 16384 -> (committed = false -> nch = 0) -> 0x10000 <= nm < 2 ^ 47 ->
    (* [comment removed for export] *)
    wrA M0 (S - 4096) 4096 -> readable8 M0 S top -> wrA M0 t 4096 -> (committed = true -> wrA M0 parr 131072) ->
    art_alloc_rodata M0 -> art_rz_rodata M0 -> art_layout M0 -> art_tsd M0 tp key tsd ctx t -> art_prim_consts spb ris M0 ->
    cellA M0 0x140918 1 1 -> cellA M0 0x1c1ea2 1 0 -> cellA M0 (1295832 + 3616) 8 (2 ^ 40) -> cellA M0 (1295832 + 3624) 2 16 -> cellA M0 (1295832 + 3626) 2 2048 ->
    cellA M0 0x1d1700 8 0 -> cellA M0 (0x13d438 + 44) 4 4096 -> cellA M0 (0x13d438 + 52) 4 190 -> cellA M0 (0x13d438 + 85) 1 1 ->
    cellA M0 0x138120 8 loff -> cellA M0 (tp + loff) 4 0 -> cellA M0 t 8 ctx -> cellA M0 (ctx + 8) 4 0 ->
    cellA M0 0x14093c 4 30 -> cellA M0 (0x1d1768 + 34) 1 1 -> cellA M0 (t + 3168) 1 0 -> cellA M0 (t + 40) 1 0 -> cellA M0 (t + 8) 8 top -> cellA M0 (t + 16) 8 bot ->
    cellA M0 0x1374a8 8 0x139508 -> cellA M0 0x139508 8 nm ->
    cellA M0 0x13c618 8 4096 -> cellA M0 (0x13c618 + 8) 8 parr -> cellA M0 (0x13c618 + 16) 8 parr -> cellA M0 (0x13c618 + 56) 8 nch ->
    cellA M0 (0x13c618 + 48) 8 (if committed then 16384 else 0) -> cellA M0 (0x13c618 + 616) 4 0 ->
    (forall Mx r, GR log Mx msz r -> P r) -> (forall r, P r -> art_sec_grant3 HI t ctx parr spb l2 blk msz r) ->
    EVOK log (AMmapNull msz 0) ->
    (committed = false -> forall r, P r -> EVOK (log ++ [AMmapNull msz r]) (AMmapFixed (parr + 8 * nch) 131072)) ->
    DInvD l2 blk (Datatypes.S kb) M0 -> DRoD M0 ->
    (forall r regs' (M' : word -> option byte) (b1 : Z), P r ->
        let ab := 4096 + r in
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 S -> getr regs' 1 = raw0 ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M0 M' -> art_agree (art_malloc3L_fp S t parr nch r msz l2 blk committed) M0 M' ->
        (forall (x : word) b, art_shlo r <= U x < art_shhi r msz -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> M0 x = Some b -> M' x = Some b) ->
        DInvD l2 blk kb M' ->
        wrA M' r msz -> wrA M' (SB + r / 8) (msz / 8) ->
        cellA M' r 8 r -> cellA M' (r + 8) 8 msz -> cellA M' (r + 16) 8 nd -> cellA M' (r + 24) 8 nch ->
        0 <= b1 < 256 -> b1 mod 4 = 1 ->
        cellA M' (ab + rz - 16) 1 2 -> cellA M' (ab + rz - 15) 1 b1 -> cellA M' (ab + rz - 14) 2 0 -> cellA M' (ab + rz - 12) 4 n ->
        (forall j, 0 <= j < qn -> cellA M' (2147450880 + ab / 8 + 2 * qz + j) 1 0) -> (m8 <> 0 -> cellA M' (2147450880 + ab / 8 + 2 * qz + qn) 1 m8) ->
        cellA M' 0x13c618 8 4096 -> cellA M' (0x13c618 + 8) 8 parr -> cellA M' (0x13c618 + 16) 8 parr -> cellA M' (0x13c618 + 56) 8 (nch + 1) ->
        cellA M' (0x13c618 + 48) 8 16384 -> cellA M' (0x13c618 + 616) 4 0 ->
        cellA M' (parr + 8 * nch) 8 r -> wrA M' parr 131072 ->
        Q (log ++ art_sec_events msz r parr nch committed) (mkst regs' raw0 M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x799f4 : word) M0 rom).
Proof.
  intros Q P log regs M0 rom raw0 S HI n tp key tsd ctx t loff spb ris qs l2 blk top bot rl rz qz rs qr qn m8 nd q msz nm parr nch kb committed
         H1 Hret H2 H4 H10
         Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz
         GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
         Dl2 Dblk Al2t Al2c Al2s Il2 Abt Abc Abs Iblk Hparr Hparr4 Hparr' APp Apt Apc Apl2 Apblk Hnch Hnch0 Hnm
         W RD0 Wt Wparr RO RZRO L TSD PC Ci Cr Cmax Cmin16 Cmax2048 Chook Cmfs Cfb Cpp Cg Clsan Ctctx Ctid Cctx30 Cfast Cunw C40 Ctop Cbot Cnm1 Cnm2
         S0 S8 S16 S56 S48 S616 HGR HP EV1 EV2 DI DR K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G15; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
  change (hid (t + 4096 <= 0x10000 \/ 0x696000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx)) in G15.
  clear G10 G16.
  pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
  pose proof TSD as (_ & _ & _ & _ & _ & TR).
  pose proof PC as (_ & _ & _ & _ & _ & Cpg1 & Cpg2 & _).
  (* [comment removed for export] *)
  destruct (art_icu1 regs M0 rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 ltac:(lia) HS47 ltac:(lia) G7 ltac:(lia) G9 ltac:(unfold apart; lia)
              ltac:(unfold apart; lia) G15 G18 G19 G20 G21 G22 ltac:(lia) Htop W Wt TSD Ci Cctx30 ltac:(pose proof L as L'; unfold art_layout in L'; tauto) Cfast Cunw C40 Ctop Cbot)
    as (r1 & M1 & RUN1 & Q1_1 & Q1_2 & Q1_10 & Q1_11 & Q1_12 & Q1_13 & Q1_14 & Q1_15 & Q1_24 & Q1_4 & K1 & G01 & A1
        & F8 & F16 & F24 & F32 & F40 & F48 & F56 & E36 & E44 & E52 & E60 & E68 & E76 & E84 & E92 & E00 & E08 & E28 & E20 & E16' & W1).
  eapply ar_steps; [exact RUN1|].
  assert (T1 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= S - 2272 \/ S <= a) -> (a + Z.of_nat k <= t + 3168 \/ t + 3169 <= a) ->
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
  destruct (art_unwind_fast_any r1 M1 rom (0x81f98 : bv 64)%bv (S - 2208) (S - 2128) 0x79abc S top bot
              Q1_1 ltac:(unfold ret_ok; bveq) Q1_2 Q1_10 Q1_11 Q1_12 Q1_13 Q1_14 Q1_15
              ltac:(lia) ltac:(lia) ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) HS8 ltac:(lia) ltac:(lia)
              ltac:(eapply wr_sub; [exact W1|lia|lia]) ltac:(eapply wr_sub; [exact W1|lia|lia]) (fun _ _ => RD1)
              ltac:(apply T1; [lia|cbn; lia|cbn; lia|clear - At_i; unfold apart in At_i; cbn; lia|exact Cpg1]) ltac:(apply T1; [lia|cbn; lia|cbn; lia|clear - At_i; unfold apart in At_i; cbn; lia|exact Cpg2]))
    as (r2 & M2 & RUN2 & Q2_2 & Q2_1 & K2 & G12 & A2 & (sz & Hsz & Csz & TRC)).
  eapply ar_steps; [exact RUN2|].
  assert (T2 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= S - 2272 \/ S - 2208 <= a) -> (a + Z.of_nat k <= S - 2120 \/ S - 2116 <= a) ->
            (a + Z.of_nat k <= S - 2112 \/ S - 1872 <= a) -> cellA M1 a k v -> cellA M2 a k v).
  { intros a k v Ha Hak O1 O2 O3 C. apply (cell_agree M1 M2); [|lia|lia|exact C]. intros x Hx. apply A2; lia. }
  (* [comment removed for export] *)
  pose proof (art_icu2_fn r2 M2 rom S n t (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) Q2_2 ltac:(rewrite K2 by inl; exact Q1_24)
               ltac:(lia) HS47 ltac:(lia) G7 ltac:(lia) ltac:(unfold apart; lia) (u64_range _) (u64_range _) (u64_range _)
               ltac:(eapply wr_grows; [exact G12|exact W1]) ltac:(eapply wr_grows; [exact G12|]; eapply wr_grows; [exact G01|exact Wt])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E36]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E44])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E52]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E60])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E68]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E76])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E84]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E92])
               ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E00]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E08])) as RUN3.
  match type of RUN3 with msteps _ _ (mkst ?R _ ?X _) => set (r3 := R) in RUN3; set (M3 := X) in RUN3 end.
  eapply ar_steps; [exact RUN3|].
  assert (A03 : art_agree [(S - 2272, 2272); (t + 3168, 1)] M0 M3).
  { intros x Hx. cbn [art_out fst snd] in Hx. unfold M3. rewrite 3 Wn_outside by (cbn; clear - Hx G7 G8 G2 HHI G1 HS47; lia). rewrite A2 by (clear - Hx; lia). apply A1; clear - Hx; lia. }
  assert (G03 : mem_grows M0 M3). { eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G12|]. unfold M3. zgrows. }
  (* [comment removed for export] *)
  assert (T_img3 : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x696000 -> cellA M0 a k v -> cellA M3 a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr1 _ M0 M3 a k v A03); [|exact C]. revert Ha Hk. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Abt Abc Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop. intros Ha Hk. zarith_f. }
  assert (RO3 : art_alloc_rodata M3).
  { unfold art_alloc_rodata in *. destruct RO as (a1 & a2 & a3). repeat split; apply T_img3; first [exact a1|exact a2|exact a3|clear; lia|clear; cbn; lia]. }
  assert (RZRO3 : art_rz_rodata M3).
  { unfold art_rz_rodata in *. destruct RZRO as (a1 & a2 & a3). repeat split; apply T_img3; first [exact a1|exact a2|exact a3|clear; lia|clear; cbn; lia]. }
  assert (L3 : art_layout M3).
  { eapply art_layout_fp; [exact A03| |exact L]. intros z Hz. apply (art_gap_out _ 0x10000 (0x211b08 - 0x10000)); [|clear - Hz; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Abt Abc Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; zarith_f. }
  assert (T3 : art_tsd M3 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M3 tp key tsd ctx t A03); [| | | |exact TSD]; clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Abt Abc Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; zarith_f. }
  assert (PC3 : art_prim_consts spb ris M3).
  { eapply art_prim_consts_fp; [exact A03| |exact PC]. intros z Hz. apply (art_gap_out _ 0x10000 (0x696000 - 0x10000)); [|clear - Hz; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Abt Abc Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; zarith_f. }
  assert (W3 : wrA M3 (S - 2144 - 1952) 1952) by (eapply wr_grows; [exact G03|]; eapply wr_sub; [exact W|lia|lia]).
  assert (Wt3 : wrA M3 t 4096) by (eapply wr_grows; [exact G03|exact Wt]).
  assert (Clsan3 : cellA M3 (tp + loff) 4 0) by (apply T_img3; [clear - Hloff'; lia|clear - Hloff''; cbn; lia|exact Clsan]).
  assert (Ctctx3 : cellA M3 t 8 ctx). { apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Ctctx]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Abt Abc Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; zarith_f. }
  assert (Ctid3 : cellA M3 (ctx + 8) 4 0). { apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Ctid]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Abt Abc Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; zarith_f. }
  assert (DI3 : DInvD l2 blk (Datatypes.S kb) M3).
  { apply (DInvD_frame l2 blk (Datatypes.S kb) M0 M3 DI). intros x Dx. apply A03. revert Dx. apply art_dpriv_out; clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Abt Abc Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; zarith_f. }
  assert (DR3 : DRoD M3).
  { apply (DRoD_frame M0 M3 DR). intros x Hx. apply A03. apply (art_gap_out _ 0x10000 (0x211b08 - 0x10000)); [|clear - Hx; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Abt Abc Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; zarith_f. }
  assert (Cstk3 : cellA M3 (S - 2128) 8 (S - 2112)).
  { unfold M3. do 3 (apply cell_Wn_other; [clear - G7 HHI G1; lia|clear - G8 G2 HS47; cbn; lia|clear - HHI G1; lia|clear - HS47; cbn; lia|unfold apart; clear - G8 HHI; cbn; lia|]).
    apply T2; [clear - HHI G1; lia|clear - HS47; cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E28]. }
  assert (Cszt3 : cellA M3 (S - 2128 + 8) 8 sz).
  { replace (S - 2128 + 8) with (S - 2120) by lia. unfold M3.
    do 3 (apply cell_Wn_other; [clear - G7 HHI G1; lia|clear - G8 G2 HS47; cbn; lia|clear - HHI G1; lia|clear - HS47; cbn; lia|unfold apart; clear - G8 HHI; cbn; lia|]).
    replace sz with (sz + 0 * 2 ^ 32) by lia. replace (S - 2128 + 8) with (S - 2120) in Csz by lia.
    apply cell8_of_cells4; [clear - HHI G1; lia|clear - HS47; lia|clear - Hsz; lia|lia|exact Csz|].
    replace (S - 2120 + 4) with (S - 2116) by lia. apply T2; [clear - HHI G1; lia|clear - HS47; cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E16']. }
  assert (DP3 : DPreD blk M3 (S - 2112) sz).
  { unfold DPreD. split; [exact Hsz|]. split.
    { clear - HS8. rewrite <- (Z.div_exact S 8) in HS8 by lia. rewrite HS8. replace (8 * (S / 8) - 2112) with ((S / 8 - 264) * 8) by lia. apply Z_mod_mult. }
    split; [clear - HHI G1; lia|]. split; [clear - HS47 Hsz; lia|]. split; [unfold apart; clear - Dblk HHI Hsz; lia|].
    intros i Hi. destruct (TRC i Hi) as [w' Cw]. unfold rcell. eexists.
    assert (C3' : cellA M3 (S - 2112 + 8 * i) 8 (U w')).
    { unfold M3. do 3 (apply cell_Wn_other; [clear - G7 HHI G1 Hi; lia|clear - G8 G2 HS47 Hi Hsz; cbn; lia|clear - HHI G1 Hi; lia|clear - HS47 Hi Hsz; cbn; lia|unfold apart; clear - G8 HHI Hi Hsz; cbn; lia|]).
      replace (S - 2112 + 8 * i) with (S - 2128 + 16 + 8 * i) by lia. exact Cw. }
    exact C3'. }
  (* [comment removed for export] *)
  assert (Wparr3 : committed = true -> wrA M3 parr 131072) by (intros E; eapply wr_grows; [exact G03|exact (Wparr E)]).
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
  apply (art_allocate3_sec EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) P log r3 M3 rom (0x525b4 : bv 64)%bv (S - 2144) HI n (S - 2128) tp key tsd ctx t loff spb ris qs l2 blk
           (S - 2112) sz rl rz qz rs qr qn m8 nd q msz nm parr nch kb committed
           ltac:(unfold r3; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; rewrite K2 by inl; exact Q1_4)
           ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
           ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
           Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz
           GEO ltac:(clear - HHI; lia) ltac:(clear - HHI; lia) ltac:(clear - HS47; lia) ltac:(clear; lia) ltac:(clear; lia)
           ltac:(clear - HHI G1 HS47; lia) ltac:(clear - Hsz; lia) ltac:(clear; lia) ltac:(clear - Hsz; lia)
           Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2s Il2 Abt Abc Abs Iblk Hparr Hparr4 Hparr' APp Apt Apc Apl2 Apblk Hnch Hnch0 Hnm
           W3 Wt3 Wparr3 RO3 RZRO3 L3 T3 PC3
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Ci]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cr])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmax]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmin16])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmax2048]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Chook])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmfs]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cfb])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cpp]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cg])
           Clsan3 Ctctx3 Ctid3 Cstk3 Cszt3
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cnm1]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cnm2])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact S0]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact S8])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact S16]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact S56])
           ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact S48]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact S616])
           HGR HP EV1 EV2 DI3 DP3 DR3).
  intros r r4 M4 b1 Pr ab P4_10 P4_2 P4_1 K4 G34 A34 WIN4 DI4 WSr WSs Cr0 Cr8 Cr16 Cr24 Hb1 Hty CL1 CL3 CL4 CL2 SHZ SHP SS0 SS8 SS16 SS56 SS48 SS616 Sslot WSp.
  subst ab.
  destruct (HP r Pr) as ((Hr4 & Hr & Hri & Hrm & APr & Art & Arc & Arp) & Ark & Arl2 & Arblk).
  assert (Hm4 : msz mod 4096 = 0). { rewrite Emsz. replace (4096 * q + 4096) with ((q + 1) * 4096) by lia. apply Z_mod_mult. }
  assert (Hq1 : 17 <= q) by (clear - Hq Hsec End Hqz Erz16; lia).
  destruct (art_sh_bounds r msz Hr4 Hm4 ltac:(lia) ltac:(lia) ltac:(clear - Hrm G2; lia)) as (SH1 & SH2 & SH3 & SH4 & _).
  unfold SB, kHighMemBeg in SH1, SH2, SH3, SH4.
  (* [comment removed for export] *)
  assert (ZA : forall a n0, 0 <= n0 -> S - 2144 <= a -> art_gap (art_alloc3L_fp (S - 2144) t parr nch r msz l2 blk committed) a n0).
  { intros a n0 Hn0 Ha. unfold art_alloc3L_fp. clear - Hn0 Ha HHI G1 G8 Hrm SH4 Hparr' Hnch Dl2 Dblk.
    cbn [art_gap app fst snd]. unfold apart. destruct committed; repeat split; try exact I; lia. }
  assert (T34 : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> S - 2144 <= a -> cellA M3 a k v -> cellA M4 a k v).
  { intros a k v Ha Hak O1 C. apply (art_cell_tr _ M3 M4 a k v A34); [apply ZA; [lia|exact O1]|exact Ha|exact Hak|exact C]. }
  assert (TF : forall a v, S - 56 <= a -> a + 8 <= S -> cellA M1 a 8 v -> cellA M4 a 8 v).
  { intros a v Ha Ha' C. apply T34; [clear - Ha HHI G1; lia|clear - Ha' HS47; cbn; lia|clear - Ha; lia|]. unfold M3.
    do 3 (apply cell_Wn_other; [clear - G7 HHI G1 Ha; lia|clear - G8 G2 HS47 Ha'; cbn; lia|clear - HHI G1 Ha; lia|clear - HS47 Ha'; cbn; lia|unfold apart; clear - G8 HHI Ha Ha'; cbn; lia|]).
    apply T2; [clear - HHI G1 Ha; lia|clear - HS47 Ha'; cbn; lia|clear - Ha; cbn; lia|clear - Ha; cbn; lia|clear - Ha; cbn; lia|exact C]. }
  pose proof (art_ic3_fn r4 M4 rom raw0 S (4096 + r + rz) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
               P4_2 P4_10 ltac:(clear - Hr Hrm G2 Hqz Erz16 Hq1 Emsz; lia) ltac:(clear - HHI G1; lia) HS47 Hret
               (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
               ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
               ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
               ltac:(apply TF; [clear; lia|clear; lia|exact F8]) ltac:(apply TF; [clear; lia|clear; lia|exact F16]) ltac:(apply TF; [clear; lia|clear; lia|exact F24])
               ltac:(apply TF; [clear; lia|clear; lia|exact F32]) ltac:(apply TF; [clear; lia|clear; lia|exact F40]) ltac:(apply TF; [clear; lia|clear; lia|exact F48])
               ltac:(apply TF; [clear; lia|clear; lia|exact F56])) as RUN5.
  eapply ar_steps; [exact RUN5|]. apply ar_done.
  apply (K r _ M4 b1 Pr).
  - gres. exact P4_10.
  - gres. reflexivity.
  - gres. reflexivity.
  - intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; try apply Z_to_bv_bv_unsigned;
      rewrite K4 by inl; unfold r3; gres; try apply Z_to_bv_bv_unsigned; rewrite K2 by inl; first [ rewrite K1 by inl; reflexivity | rewrite Q1_4; symmetry; exact H4 ].
  - eapply mem_grows_trans; [exact G03|exact G34].
  - intros x Ox. unfold art_malloc3L_fp in Ox. 
    assert (O34 : art_out (art_alloc3L_fp (S - 2144) t parr nch r msz l2 blk committed) (U x)).
    { unfold art_alloc3L_fp. clear - Ox. cbn [art_out fst snd] in Ox |- *. destruct committed; repeat split; try exact I; lia. }
    rewrite (A34 x O34).
    destruct (Z.eq_dec (U x) (t + 3168)) as [e|ne].
    + assert (Ex : x = Z_to_bv 64 (t + 3168)) by (rewrite <- e; symmetry; apply Z_to_bv_bv_unsigned). rewrite Ex.
      rewrite (art_byte_of_cell1 M0 (t + 3168) 0 ltac:(clear - At_i; unfold apart in At_i; lia) ltac:(clear - G7 G8 G2; lia) ltac:(clear; lia) Cunw).
      apply art_byte_of_cell1; [clear - At_i; unfold apart in At_i; lia|clear - G7 G8 G2; lia|clear; lia|]. unfold M3. clear - G7 G8 G2 HHI G1 HS47. zcell.
    + apply A03. cbn [art_out fst snd] in Ox |- *. clear - Ox ne. repeat split; try exact I; lia.
  - intros x b Hx Nx Mx. apply (WIN4 x b Hx Nx). rewrite (art_agree_pt _ _ _ x A03); [exact Mx|].
    clear - Hx SH1 SH4 HHI G1 At_s. unfold apart in At_s. cbn [art_out fst snd]. repeat split; try exact I; lia.
  - exact DI4.
  - exact WSr. - exact WSs. - exact Cr0. - exact Cr8. - exact Cr16. - exact Cr24.
  - exact Hb1. - exact Hty. - exact CL1. - exact CL3. - exact CL4. - exact CL2. - exact SHZ. - exact SHP.
  - exact SS0. - exact SS8. - exact SS16. - exact SS56. - exact SS48. - exact SS616. - exact Sslot. - exact WSp.
Qed.
End Spec.
