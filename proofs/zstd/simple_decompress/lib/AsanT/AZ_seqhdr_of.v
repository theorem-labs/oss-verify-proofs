(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdTbl ZdDctxRep SepHide DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSafe.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_tbl AZ_kx
     AZ_fkit AZ_blk_iface AZ_blk_iface2 AZ_blk_iface3 AZ_bst_stk AZ_seqhdr_kit AZ_seqhdr_env.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation zlen l := (Z.of_nat (length l)).

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.
Section SHS.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Ltac open_shhA HY := pose proof HY as (DCL & DCH & NBL & NBH & SLEN & SRCL & SRCH & LO0 & LOS & SPH & OFFD & OFFNB & OFFSRC & DNB & DSRC & NBSRC
                                        & DCA & NBA & KLO & D8 & ASH & AST & RFS & BOT & SPT & SP16 & RSTKT & LBH
                                        & RD & RDS & IBD & RNB & RNBS & IBN & SRCF & DCB & NBB & ABD & ABN);
                    hide_all_disj.
Ltac open_shbA I := destruct I as (P0 & P1 & P2 & P3 & ELL & EOF & EML & EWK & H3 & COLD & NB & SRCB & STK & (fa & fb & FR) & MI & MU & WM
                                   & AH & FFR & UD & UNB & USRC & HSRC & ROC).
Notation FOOTA L DCTX NBP SPV := ([(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (NBP, NBP + 4); (SPV - 5248, SPV)] ++ fake_area L) (only parsing).
Notation W4 DCTX NBP := [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (NBP, NBP + 4)] (only parsing).
Section SH.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis HBST : zd_buildseq_stmtA AI rng_fs.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
            (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DCTX NBP SRC : Z) (src : list Z) (llt mlt oft huf pcs dsz bt stg le fe cold : word).
  Hypothesis HY : sh_hypsA rng_fs L RNG LB SPV lo DCTX NBP SRC (zlen src).
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) src.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Notation POST := (zd_seqhdr_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX NBP (zlen src) llt mlt oft huf lo m).
  Notation SHB := (SHBA AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m SPV lo DCTX NBP SRC src huf pcs dsz bt stg le fe cold).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SH_RET := (sh_retA AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX NBP SRC src llt mlt oft huf pcs dsz bt stg le fe cold HY).
  Notation SH_ML := (sh_mlA AI fflag rng_fs FHL HBST L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX NBP SRC src llt mlt oft huf pcs dsz bt stg le fe cold HY FBY TP).

  (* [comment removed for export] *)
  Lemma sh_ofA : forall m1 p0 p1 p2 nbSeq i1 r1 tb T0 bs0 TO bsO TM bsM xra x5 x6 x7 xs4v xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    SHB p0 p1 p2 (Z_to_bv 64 nbSeq) m1 ->
    1 <= nbSeq <= 98047 -> 0 <= tb < 256 -> 1 <= i1 -> 0 <= r1 -> i1 + r1 <= zlen src ->
    tab_infoA DCTX K_LL 32 APZD_LL_DEFAULT LL_defaultDTable p0 T0 bs0 -> bytes_at bsegs m1 T0 bs0 ->
    bytes_at bsegs m1 TO bsO -> zlen bsO <= 2056 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_OF 4136 APZD_OF_DEFAULT OF_defaultDTable p2 TO bsO) ->
    (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) -> (TO + 2056 <= lo \/ SPV <= TO) -> (TO = DCTX + 4136 \/ TO + 2056 <= 0x30000) ->
    bytes_at bsegs m1 TM bsM -> zlen bsM <= 4104 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_ML 6192 APZD_ML_DEFAULT ML_defaultDTable p1 TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) -> (TM = DCTX + 6192 \/ TM + 4104 <= 0x30000) ->
    xs4v = Z_to_bv 64 nbSeq ->
    evtF bsegs RNG POST (ST 0x889d8 m1 xra x5 x6 x7 (Z_to_bv 64 (DCTX + 30204)) (Z_to_bv 64 (DCTX + 30004))
                       (Z_to_bv 64 r1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + zlen src)) xs4v (Z_to_bv 64 SRC) (Z_to_bv 64 tb) (Z_to_bv 64 (DCTX + 27324))
                       (Z_to_bv 64 (2147450880 + (DCTX + 30004) / 8)) (Z_to_bv 64 (2147450880 + (DCTX + 30204) / 8)) (Z_to_bv 64 DCTX)
                       x28 x29 x30 x31).
  Proof.
    intros until x31. intros I NBR TBR I1 R1 IR TI0 TB0 OLDBO OLDLO OLDVO LOCO OFFO IMGO OLDB OLDL OLDV LOCM OFFM IMGM ->. open_shbA I. open_shhA HY.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (tab_infoA_len _ _ _ _ _ _ _ _ TI0) as LEN0.
    cbn [kind_maxLog] in LEN0. change (2^9) with 512 in LEN0.
    (* [comment removed for export] *)
    hide MU. hide TB0. hide OLDBO. hide OLDB. hide FFR.
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
    assert (MUr : munch [(SPV - 112, SPV - 96)] m1 m1) by apply munch_refl.
    assert (WMr : wmono bsegs m1 m1) by apply wmono_refl.
    kx_autoFLAx [KAUnp DCTX 95992; KAShp (2147450880 + (DCTX + 30004) / 8) (DCTX + 30004); KAShp (2147450880 + (DCTX + 30204) / 8) (DCTX + 30204);
               KAApp (SPV - 112) 16]
      [0x88bb8] 60%nat
      [KZRange SPV (17594333495296 + 5248) (2^47); KZRange DCTX 0x625000 (2^47 - 95992); KZRange SRC 4096 (2^47); KZRange NBP 0x625000 (2^47 - 4);
       KZRange i1 0 1048576; KZRange r1 0 1048576; KZRange (zlen src) 0 1048576; KZRange tb 0 255; KZRange nbSeq 1 98047; KZAlign DCTX 8;
       KZWr (SPV - 112) 16; KZDisj (SPV - 112) 16 DCTX 95992; KZDisj (SPV - 112) 16 NBP 4; KZDisj (SPV - 112) 16 SRC (zlen src)]
      [(SPV - 112, 112); (DCTX + 29976, 32); (DCTX + 30204, 4)] [(SPV - 112, 112); (DCTX, 95992)].
    all: try kx_cell_lit. all: try kx_z. all: try (kx_acc RSTKT).
    all: match goal with |- evtF _ _ _ _ => idtac | |- _ => repeat split; try lia; unfold off_stack, apart in *; sep_solve end.
    all: kx_mem.
    (* [comment removed for export] *)
    all: lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned (edenot ?E (EExt true 0 4 (EVar ?j))))] =>
           let H := fresh "T5E" in
           assert (H : Z_to_bv 64 (bv_unsigned (edenot E (EExt true 0 4 (EVar j)))) = Mem.sx32 fe)
             by (rewrite Z_to_bv_bv_unsigned; cbn [edenot]; rewrite (KXA j) by (cbn; lia); cbn [znth nth Z.to_nat Pos.to_nat];
                 unfold ext_val, ext_Z, Mem.sx32; rewrite Z_to_bv_bv_unsigned; apply Zbv_eq_mod;
                 unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                 change (2 ^ Z.of_N (32 - 1)) with 2147483648; change (2 ^ (8 * Z.of_nat 0)) with 1; change (2 ^ (8 * Z.of_nat 4)) with 4294967296;
                 rewrite Z.div_1_r; pose proof (bv_unsigned_in_range 64 fe); Z.div_mod_to_equations; lia);
           rewrite H
         end.
    all: kx_abs.
    (* [comment removed for export] *)
    set (i2 := i1 + r1) in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mq end.
    replace (r1 + (SRC + i1)) with (SRC + i2) by lia.
    replace (-1 * r1 + (-1 * i1 + zlen src)) with (zlen (skipn (Z.to_nat i2) src)) by (rewrite length_skipn; lia).
    assert (LSK : zlen (skipn (Z.to_nat i2) src) = zlen src - i2) by (rewrite length_skipn; lia).
    assert (FSK : Forall (fun c => 0 <= c < 256) (skipn (Z.to_nat i2) src)).
    { pose proof FBY as FB. rewrite <- (firstn_skipn (Z.to_nat i2) src) in FB. apply Forall_app in FB. exact (proj2 FB). }
    pose proof (abytes_at_skipn _ _ _ i2 SRCB ltac:(lia)) as SRC3.
    assert (TYR : 0 <= (288230376151711744 * tb) mod 2 ^ 64 / 4611686018427387904 <= 3).
    { pose proof (Z.mod_pos_bound (288230376151711744 * tb) (2^64) ltac:(lia)) as MB.
      split; [apply Z.div_pos; lia|].
      assert (X4 : (288230376151711744 * tb) mod 2 ^ 64 / 4611686018427387904 < 4) by (apply Z.div_lt_upper_bound; lia). lia. }
    assert (AH1 : AHEAP AI L RNG st LB mq).
    { eapply (AI_frame AI); [exact AH| exact MUr| exact WMr|]. constructor; [| constructor]. left; left. cbn. lia. }
    assert (ART1 : art mq) by (apply sh_artcells_art; exact (AI_rtcells AI _ _ _ _ _ AH1)).
    assert (DSH : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 112, SPV - 96)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *. clear - X0 Hn Hb KLO LOS. Z.div_mod_to_equations. lia. }
    assert (UD1 : unpoisoned mq DCTX (DCTX + 95992)) by (eapply unpoisoned_munch; [exact UD| exact MUr| apply DSH; lia]).
    assert (UNB1 : unpoisoned mq NBP (NBP + 4)) by (eapply unpoisoned_munch; [exact UNB| exact MUr| apply DSH; lia]).
    assert (ROC1 : aro_client RNG mq).
    { eapply aro_client_transport; [exact ROC| exact MUr| exact WMr|]. constructor; [| constructor]. right. cbn. unfold KHIGH. lia. }
    pose proof (aro_tables _ _ ROC1) as (_ & _ & _ & OBASE & OBITS & ODFLT & _ & _ & _).
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) => change (c1 :: c2 :: rest) with ([c1; c2] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [ARGS FRR]. cbn [cells_size csize Nat.add] in FRR.
    replace (SPV + -112 + Z.of_nat 16) with (SPV + -96) in FRR by lia.
    destruct AST as (KLO' & RSTK & RIMG).
    assert (AFP : afpre AI rng_fs L RNG st LB mq lo (SPV + -112) 3).
    { split; [exact AH1|]. split; [exact ASH|]. split; [exact ART1|]. split; [split; [exact KLO'| split; [eapply rng_sub'; [exact RSTK| lia]| exact RIMG]]|].
      split; [exact RFS|]. split; [exact BOT|]. split; [lia|]. split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH]. }
    (* [comment removed for export] *)
    pose proof (zd_buildseq_stkA AI rng_fs HBST) as BS. change (Z_to_bv 64 562804) with (Z_to_bv 64 APZD_BUILDSEQ).
    eapply evtF_cut; [ eapply BS with (SPV := SPV + -112) (lo := lo) (DTS := DCTX + 4136) (DTP := DCTX + 16) (SRC := SRC + i2) (W := DCTX + 27324)
        (DFLT := APZD_OF_DEFAULT) (BASE := APOF_BASE) (BITS := APOF_BITS) (ty := (288230376151711744 * tb) mod 2 ^ 64 / 4611686018427387904)
        (wlen := 2560) (k := K_OF) (srcb := skipn (Z.to_nat i2) src) (oldp := p2) (nbw := Z_to_bv 64 nbSeq) (L := L) (st := st) (LB := LB);
      first [ eassumption | reflexivity
            | replace (DCTX + 4136 + (8 + 8 * 2 ^ kind_maxLog K_OF)) with (DCTX + 6192) by (cbn [kind_maxLog]; lia); exact EOF
            | replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK
            | apply apof_base_at; assumption | apply apof_bits_at; assumption
            | intros Hfz; destruct (OLDVO Hfz) as (tq & -> & _ & _ & [-> | [-> _]]); rewrite unsigned_lit by (unfold APZD_OF_DEFAULT; lia); unfold APZD_OF_DEFAULT; lia   (* [comment removed for export] *)
            | idtac ] | ].
    all: cbn [kind_maxLog].
    all: try lazymatch goal with
         | |- aregU _ _ ?A ?n =>
                 destruct (SRCF ltac:(lia)) as (Q1 & Q2 & Q3 & Q4);
                     split; [eapply ablk_sub; [exact Q4| lia| lia]|];
                     split; [eapply unpoisoned_sub; [eapply unpoisoned_munch; [eapply USRC; lia| exact MUr| apply DSH; lia]| lia| lia]|];
                     split; [eapply rng_sub'; [exact Q1| lia]|];
                     pose proof (shspan_sub SRC (zlen src) A n ltac:(lia) ltac:(lia) ltac:(lia)) as SS; eapply rng_sub'; [exact Q2| lia]
         | |- areg _ _ ?A ?n =>
             first [ (* [comment removed for export] *)
                     intros _; split; [eapply ablk_sub; [exact ABD| lia| lia]|];
                     split; [eapply unpoisoned_sub; [exact UD1| lia| lia]|];
                     split; [eapply rng_sub'; [exact RD| lia]|];
                     pose proof (shspan_sub DCTX 95992 A n ltac:(lia) ltac:(lia) ltac:(lia)) as SS; eapply rng_sub'; [exact RDS| lia]
                   | (* [comment removed for export] *)
                     intros Hn; destruct (SRCF ltac:(lia)) as (Q1 & Q2 & Q3 & Q4);
                     split; [eapply ablk_sub; [exact Q4| lia| lia]|];
                     split; [eapply unpoisoned_sub; [eapply unpoisoned_munch; [eapply USRC; lia| exact MUr| apply DSH; lia]| lia| lia]|];
                     split; [eapply rng_sub'; [exact Q1| lia]|];
                     pose proof (shspan_sub SRC (zlen src) A n ltac:(lia) ltac:(lia) ltac:(lia)) as SS; eapply rng_sub'; [exact Q2| lia] ]
         | |- ainblk _ ?A ?n => eapply ainblk_sub; [exact IBD| lia| lia]
         | |- 0 < _ -> ainimg _ _ _ => intros Hn; destruct (SRCF ltac:(lia)) as (Q1 & Q2 & Q3 & Q4); eapply ainimg_sub; [exact Q3| lia| lia]
         | |- ahull _ _ _ _ => eapply ahull_sub; [eapply ahull_wmono; [exact WMr| eapply HSRC; lia]| lia| lia]
         | |- 0 < _ -> ahull _ _ _ _ => intros Hn; eapply ahull_sub; [eapply ahull_wmono; [exact WMr| eapply HSRC; lia]| lia| lia]
         | |- ainimg _ _ _ => first [ destruct (SRCF ltac:(lia)) as (Q1 & Q2 & Q3 & Q4); eapply ainimg_sub; [exact Q3| lia| lia] | right; cbn; unfold APOF_BASE, APOF_BITS, AIMG_HI; lia ]
         | |- _ <= AIMG_HI => cbn; unfold APOF_BASE, APOF_BITS, AIMG_HI; lia
         | |- forall _, _ => idtac
         | |- _ => unfold APOF_BASE, APOF_BITS, APZD_OF_DEFAULT, off_stack, apart; first [lia | sep_solve | unhide; lia]
         end.
    (* [comment removed for export] *)
    cbv beta. intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mc & rr & pv & -> & MUc & WMc & MIc & STKc & FFRc & AHc & DTSc & WKc & DTPc & FRAMEc & RR & RESc).
    replace (ret_pc (Z_to_bv 64 559692)) with (Z_to_bv 64 559692) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [kind_maxLog] in MUc, FFRc, DTSc, FRAMEc, RESc.
    replace (DCTX + 4136 + (8 + 8 * 2 ^ 8)) with (DCTX + 6192) in * by lia.
    replace (DCTX + 16 + 8) with (DCTX + 24) in * by lia.
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in * by lia.
    pose proof (AI_layout AI _ _ _ _ _ AHc) as (_ & _ & _ & _ & _ & _ & FKLO & FKHI).
    assert (FFRc4 : ffr_pres [(DCTX + 4136, DCTX + 6192); (DCTX + 16, DCTX + 24); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)] LB mq mc).
    { eapply ffr_pres_weaken; [exact FFRc|]. unfold sub_fp. cbn [outside]. intros x Hx. tauto. }
    (* [comment removed for export] *)
    assert (DJ : forall X n, 0 <= n -> DCTX <= X -> (X + n <= DCTX + 16 \/ DCTX + 24 <= X) -> (X + n <= DCTX + 4136 \/ DCTX + 6192 <= X) ->
                 (X + n <= DCTX + 27324 \/ DCTX + 29884 <= X) -> X + n <= DCTX + 95992 ->
                 disjoint_from [(DCTX + 4136, DCTX + 6192); (DCTX + 16, DCTX + 24); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)] X n).
    { intros X n Hn G0 G1 G2 G3 G4. cbn [disjoint_from]. pose proof OFFD as OFFD'; unfold hidden in OFFD'. repeat split; lia. }
    assert (P0c : rw_cells bsegs mc DCTX [C8 p0]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact P0]. }
    assert (P1c : rw_cells bsegs mc (DCTX + 8) [C8 p1]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact P1]. }
    assert (P3c : rw_cells bsegs mc (DCTX + 24) [C8 huf]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact P3]. }
    assert (H3c : rw_cells bsegs mc (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact H3]. }
    assert (COLDc : rw_cells bsegs mc (DCTX + 30204) [C4 cold]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact COLD]. }
    assert (ELLc : stk bsegs mc (DCTX + 32) (DCTX + 4136)).
    { eapply (shc_stk_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| lia| lia]| apply DJ; lia| exact MUc| exact WMc| exact FFRc4| exact ELL]. }
    assert (EMLc : stk bsegs mc (DCTX + 6192) (DCTX + 10296)).
    { eapply (shc_stk_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| lia| lia]| apply DJ; lia| exact MUc| exact WMc| exact FFRc4| exact EML]. }
    assert (DJN : disjoint_from [(DCTX + 4136, DCTX + 6192); (DCTX + 16, DCTX + 24); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)] NBP 4).
    { cbn [disjoint_from]. pose proof OFFNB as X1; unfold hidden in X1. pose proof DNB as X2; unfold hidden in X2. repeat split; lia. }
    assert (NBc : rw_cells bsegs mc NBP [C4 (Z_to_bv 64 nbSeq)]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBN| cbn; lia| cbn; lia]| exact DJN| exact MUc| exact WMc| exact FFRc4| exact NB]. }
    (* [comment removed for export] *)
    assert (DJF : disjoint_from ([(DCTX + 4136, DCTX + 6192); (DCTX + 16, DCTX + 24); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)] ++ fake_area L) (SPV + -112) 112).
    { pose proof OFFD as X1; unfold hidden in X1. unfold fake_area, FAKESZ. cbn [disjoint_from app]. rewrite !shad_div. unfold ASHOFF.
      repeat split; first [lia | clear - FKHI BOT LOS KLO ATR; Z.div_mod_to_equations; lia]. }
    assert (FRc : rw_cells bsegs mc (SPV + -112) ([C8 (Z_to_bv 64 nbSeq); C8 (Z_to_bv 64 (DCTX + 27324))] ++ [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { eapply rw_cells_transport; [| exact MUc| exact WMc| exact DJF]. apply rw_cells_app. split; [exact ARGS|]. cbn [cells_size csize Nat.add].
      replace (SPV + -112 + Z.of_nat 16) with (SPV + -96) by lia. exact FRR. }
    cbn [app] in FRc.
    (* [comment removed for export] *)
    assert (SRCc : bytes_at bsegs mc SRC (map (Z_to_bv 8) src)).
    { destruct (Z.eq_dec (zlen src) 0) as [Z0|Zp].
      - destruct SRCB as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite length_map in Hi. lia.
      - destruct (SRCF ltac:(lia)) as (Q1 & Q2 & [Q3|Q3] & Q4).
        + eapply (shc_bytes_pres AI FHL); [exact AH1| rewrite length_map; exact Q3| | exact MUc| exact FFRc4| exact SRCB].
          rewrite length_map. cbn [disjoint_from]. pose proof OFFSRC as X1; unfold hidden in X1. pose proof DSRC as X2; unfold hidden in X2. repeat split; lia.
        + eapply bytes_at_transport; [exact SRCB| exact MUc|]. rewrite length_map. unfold fake_area, FAKESZ, AIMG_HI in *. cbn [disjoint_from app].
          rewrite !shad_div. unfold ASHOFF. repeat split; first [lia | clear - Q3 FKLO SRCL; Z.div_mod_to_equations; lia]. }
    (* [comment removed for export] *)
    assert (AAW : aappW [(DCTX + 4136, DCTX + 6192); (DCTX + 16, DCTX + 24); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)]).
    { pose proof DCB as X1; unfold hidden in X1. unfold aappW, KLOW, KHIGH. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (UDc : unpoisoned mc DCTX (DCTX + 95992)).
    { eapply (shc_unp_pres AI FHL); [exact AH1| exact IBD| lia| unfold KEND; lia| exact AAW| exact MUc| exact FFRc4| exact UD1]. }
    assert (UNBc : unpoisoned mc NBP (NBP + 4)).
    { eapply (shc_unp_pres AI FHL); [exact AH1| exact IBN| lia| unfold KEND; lia| exact AAW| exact MUc| exact FFRc4| exact UNB1]. }
    assert (USRCc : 0 < zlen src -> unpoisoned mc SRC (SRC + zlen src)).
    { intros Zp. destruct (SRCF ltac:(lia)) as (Q1 & Q2 & [Q3|Q3] & Q4).
      - eapply (shc_unp_pres AI FHL); [exact AH1| exact Q3| lia| unfold KEND; lia| exact AAW| exact MUc| exact FFRc4|].
        eapply unpoisoned_munch; [eapply USRC; lia| exact MUr| apply DSH; lia].
      - eapply unpoisoned_munch; [eapply unpoisoned_munch; [eapply USRC; lia| exact MUr| apply DSH; lia]| exact MUc|].
        pose proof (proj1 (FHL _ _ _ _ _ AHc)) as AFB. unfold ablk, AIMG_HI, KLS in AFB.
        unfold fake_area, FAKESZ, AIMG_HI in *. cbn [disjoint_from app]. rewrite !shad_div. unfold ASHOFF. pose proof DCB as X1; unfold hidden in X1.
        repeat split; (clear - Q3 FKLO SRCL Zp X1 DCA KLO LOS AFB ATR; Z.div_mod_to_equations; lia). }
    assert (HSRCc : 0 < zlen src -> ahull RNG mc SRC (zlen src)) by (intros Zp; eapply ahull_wmono; [exact WMc| eapply ahull_wmono; [exact WMr| exact (HSRC Zp)]]).
    assert (ROCc : aro_client RNG mc) by (eapply aro_client_transport_F; [exact ROC1| exact MUc| exact WMc| exact AAW| exact (proj1 (FHL _ _ _ _ _ AHc))]).
    (* [comment removed for export] *)
    unfold hidden in MU. unfold hidden in FFR.
    assert (MUq : munch (FOOTA L DCTX NBP SPV) m mq).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUr]. unfold sub_fp. cbn [outside app]. intros x Hx. repeat split; lia. }
    assert (MUt : munch (FOOTA L DCTX NBP SPV) m mc).
    { eapply munch_trans; [exact MUq|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp, fake_area. cbn [outside app]. intros x Hx. repeat split; try lia; tauto. }
    first [assert (WMt : wmono bsegs m mc) by (eapply wmono_trans; [exact WM| exact WMc]) | assert (WMt : wmono bsegs m mc) by (eapply wmono_trans; [eapply wmono_trans; [exact WM| exact WMr]| exact WMc])].
    assert (FFRq : ffr_pres [] LB m1 mq).
    { eapply (fk_ffr_stack AI); [exact AH| exact MUr| exact WMr|]. constructor; [cbn; lia| constructor]. }
    assert (FFRt : ffr_pres (W4 DCTX NBP) LB m mc).
    { eapply ffr_pres_trans; [exact FFR|]. eapply ffr_pres_trans; [eapply ffr_pres_weaken; [exact FFRq| unfold sub_fp; cbn; intros; exact I]|].
      eapply ffr_pres_weaken; [exact FFRc|]. unfold sub_fp. cbn [outside]. intros x Hx. repeat split; lia. }
    (* [comment removed for export] *)
    unfold hidden in TB0. unfold hidden in OLDBO. unfold hidden in OLDB.
    pose proof OFFD as OFFD1. unfold hidden in OFFD1.
    assert (TB0c : bytes_at bsegs mc T0 bs0).
    { destruct TI0 as (tL & EpL & EbL & OKL & [TL0 | [TL0 EtL]]).
      - assert (B1 : bytes_at bsegs mq T0 bs0).
        { eapply bytes_at_transport; [exact TB0| exact MUr|]. cbn [disjoint_from]. split; [|exact I]. clear - TL0 LEN0 OFFD1 LOS DCL. lia. }
        eapply (shc_bytes_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| lia| lia]| apply DJ; lia| exact MUc| exact FFRc4| exact B1].
      - rewrite TL0, EbL, EtL. exact (all_default_at mc MIc). }
    assert (SHI : SHB p0 p1 pv (Z_to_bv 64 nbSeq) mc).
    { split; [exact P0c|]. split; [exact P1c|]. split; [exact DTPc|]. split; [exact P3c|]. split; [exact ELLc|]. split; [exact DTSc|]. split; [exact EMLc|].
      split; [exact WKc|]. split; [exact H3c|]. split; [exact COLDc|]. split; [exact NBc|]. split; [exact SRCc|]. split; [exact STKc|].
      split; [eexists; eexists; exact FRc|]. split; [exact MIc|]. split; [exact MUt|]. split; [exact WMt|].
      split; [exact AHc|]. split; [exact FFRt|]. split; [exact UDc|]. split; [exact UNBc|]. split; [exact USRCc|]. split; [exact HSRCc| exact ROCc]. }
    destruct RESc as [ER | (RL & RES3)].
    - (* [comment removed for export] *)
      assert (RRE : 2^64 - 119 <= rr) by (unfold zd_is_error, ZE_maxCode in ER; apply Z.ltb_lt in ER; lia).
      kx_autoFLAx [] [0x88bb8] 12%nat [KZRange rr (2^64 - 119) (2^64 - 1)] [] [].
      all: try kx_z.
      all: kx_mem.
      eapply (SH_RET mc p0 p1 pv (Z_to_bv 64 nbSeq) 18446744073709551596); [exact SHI| lia| left; reflexivity].
    - (* [comment removed for export] *)
      assert (OFI : exists TO' bsO', tab_infoA DCTX K_OF 4136 APZD_OF_DEFAULT OF_defaultDTable pv TO' bsO' /\ bytes_at bsegs mc TO' bsO').
      { destruct RES3 as [(T0' & ->) | [(T3 & FRN & -> & SAME) | (T12 & -> & t & TOK & TB)]].
        - exists APZD_OF_DEFAULT, (map (Z_to_bv 8) (seq_table_bytes OF_defaultDTable)). split; [| exact (aof_default_at mc MIc)].
          exists OF_defaultDTable. split; [reflexivity|]. split; [reflexivity|]. split; [exact OF_default_ok| right; split; reflexivity].
        - destruct (OLDVO FRN) as (tO & EpO & EbO & OKO & TPO). exists TO, bsO. split; [exists tO; split; [exact EpO| split; [exact EbO| split; [exact OKO| exact TPO]]]|].
          destruct TPO as [TO0 | [TO0 EtO]].
          + rewrite TO0. apply SAME; [| lia]. rewrite <- TO0. eapply bytes_at_transport; [exact OLDBO| exact MUr|]. cbn [disjoint_from]. split; [|exact I].
            clear - TO0 OLDLO OFFD1 LOS DCL. lia.
          + rewrite TO0, EbO, EtO. exact (aof_default_at mc MIc).
        - exists (DCTX + 4136), (map (Z_to_bv 8) (seq_table_bytes t)). split; [| exact TB]. exists t. split; [reflexivity|]. split; [reflexivity|].
          split; [exact TOK| left; reflexivity]. }
      destruct OFI as (TO' & bsO' & TIO & TBO).
      (* [comment removed for export] *)
      assert (MLI : exists TM' bsM', bytes_at bsegs mc TM' bsM' /\ zlen bsM' <= 4104 /\
                (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_ML 6192 APZD_ML_DEFAULT ML_defaultDTable p1 TM' bsM') /\
                (TM' = DCTX + 6192 \/ (TM' + 4104 <= DCTX \/ DCTX + 30372 <= TM')) /\ (TM' + 4104 <= lo \/ SPV <= TM') /\ (TM' = DCTX + 6192 \/ TM' + 4104 <= 0x30000)).
      { destruct (decide (Mem.sx32 fe = Z_to_bv 64 0)) as [FZ | FNZ].
        - exists APZD_ML_DEFAULT, (map (Z_to_bv 8) (seq_table_bytes ML_defaultDTable)). split; [exact (aml_default_at mc MIc)|].
          split; [vm_compute; discriminate|]. split; [intros X; exfalso; exact (X FZ)|]. unfold APZD_ML_DEFAULT. clear - DCA KLO. repeat split; lia.
        - destruct (OLDV FNZ) as (tM & EpM & EbM & OKM & TPM). exists TM, bsM. split.
          + destruct TPM as [TM0 | [TM0 EtM]].
            * assert (B1 : bytes_at bsegs mq TM bsM).
              { eapply bytes_at_transport; [exact OLDB| exact MUr|]. cbn [disjoint_from]. split; [|exact I]. clear - TM0 OLDL OFFD1 LOS DCL. lia. }
              eapply (shc_bytes_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| lia| lia]| apply DJ; lia| exact MUc| exact FFRc4| exact B1].
            * rewrite TM0, EbM, EtM. exact (aml_default_at mc MIc).
          + split; [exact OLDL|]. split; [intros X; exists tM; split; [exact EpM| split; [exact EbM| split; [exact OKM| exact TPM]]]|].
            split; [exact LOCM|]. split; [exact OFFM| exact IMGM]. }
      destruct MLI as (TM' & bsM' & TBM & TLM & TIM & LOCM' & OFFM' & IMGM').
      eapply (SH_ML mc p0 p1 pv nbSeq i2 rr tb T0 bs0 TO' bsO' TM' bsM'); first [exact SHI | exact TIO | exact TBO | exact TBM | exact TLM | exact TIM
        | exact LOCM' | exact OFFM' | exact IMGM' | reflexivity | lia
        | destruct TI0 as (tL & EpL & EbL & OKL & TPL); exists tL; split; [exact EpL| split; [exact EbL| split; [exact OKL| exact TPL]]]
        | exact TB0c ].
  Qed.
End SH.
End SHS.
End CANSEC1.
