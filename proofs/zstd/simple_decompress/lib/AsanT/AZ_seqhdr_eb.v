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
     AZ_fkit AZ_blk_iface AZ_blk_iface2 AZ_blk_iface3 AZ_bst_stk AZ_seqhdr_kit AZ_seqhdr_env AZ_seqhdr_of AZ_seqhdr_ll AZ_seqhdr_ea.
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
  Hypothesis NB4 : NBP mod 4 = 0.   (* [comment removed for export] *)
  Notation POST := (zd_seqhdr_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX NBP (zlen src) llt mlt oft huf lo m).
  Notation SHB := (SHBA AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m SPV lo DCTX NBP SRC src huf pcs dsz bt stg le fe cold).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SH_RET := (sh_retA AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX NBP SRC src llt mlt oft huf pcs dsz bt stg le fe cold HY).
  Notation SH_LL := (sh_llA AI fflag rng_fs FHL HBST L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX NBP SRC src llt mlt oft huf pcs dsz bt stg le fe cold HY FBY TP).
  Notation SH_OF := (sh_ofA AI fflag rng_fs FHL HBST L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX NBP SRC src llt mlt oft huf pcs dsz bt stg le fe cold HY FBY TP).

  Lemma sh_ent1 : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nb0 : word) TL bsL TO bsO TM bsM,
    rw_cells bsegs m DCTX [C8 llt] -> rw_cells bsegs m (DCTX + 8) [C8 mlt] -> rw_cells bsegs m (DCTX + 16) [C8 oft] -> rw_cells bsegs m (DCTX + 24) [C8 huf] ->
    stk bsegs m (DCTX + 32) (DCTX + 4136) -> stk bsegs m (DCTX + 4136) (DCTX + 6192) -> stk bsegs m (DCTX + 6192) (DCTX + 10296) ->
    stk bsegs m (DCTX + 27324) (DCTX + 29884) ->
    rw_cells bsegs m (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] -> rw_cells bsegs m (DCTX + 30204) [C4 cold] ->
    rw_cells bsegs m NBP [C4 nb0] -> bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> stk bsegs m lo SPV -> mem_inv bsegs m ->
    AHEAP AI L RNG st LB m -> art m -> unpoisoned m DCTX (DCTX + 95992) -> unpoisoned m NBP (NBP + 4) ->
    (0 < zlen src -> unpoisoned m SRC (SRC + zlen src)) -> (0 < zlen src -> ahull RNG m SRC (zlen src)) -> aro_client RNG m ->
    bytes_at bsegs m TL bsL -> zlen bsL <= 4104 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_LL 32 APZD_LL_DEFAULT LL_defaultDTable llt TL bsL) ->
    (TL = DCTX + 32 \/ (TL + 4104 <= DCTX \/ DCTX + 30372 <= TL)) -> (TL + 4104 <= lo \/ SPV <= TL) -> (TL = DCTX + 32 \/ TL + 4104 <= 0x30000) ->
    (TL + 4104 <= NBP \/ NBP + 4 <= TL) ->
    bytes_at bsegs m TO bsO -> zlen bsO <= 2056 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_OF 4136 APZD_OF_DEFAULT OF_defaultDTable oft TO bsO) ->
    (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) -> (TO + 2056 <= lo \/ SPV <= TO) -> (TO = DCTX + 4136 \/ TO + 2056 <= 0x30000) ->
    (TO + 2056 <= NBP \/ NBP + 4 <= TO) ->
    bytes_at bsegs m TM bsM -> zlen bsM <= 4104 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_ML 6192 APZD_ML_DEFAULT ML_defaultDTable mlt TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) -> (TM = DCTX + 6192 \/ TM + 4104 <= 0x30000) ->
    (TM + 4104 <= NBP \/ NBP + 4 <= TM) ->
    zlen src = 1 ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) (Z_to_bv 64 NBP) (Z_to_bv 64 SRC) (Z_to_bv 64 (zlen src))
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8889c) fc None m (seg_rom bsegs)).
  Proof.
    intros until bsM. intros P0 P1 P2 P3 ELL EOF EML EWK H3 COLD NB SRCB STK MI AH ART UD UNB USRC HSRC ROC
           OLDBL OLDLL OLDVL LOCL OFFL IMGL SNL OLDBO OLDLO OLDVO LOCO OFFO IMGO SNO OLDB OLDL OLDV LOCM OFFM IMGM SNM CLS. open_shhA HY.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct ART as (GOT & RIC & SHB0 & INI & LAY & REAL). destruct AST as (KLO' & RSTK & RIMG).
    pose proof NBB as NBB1. unfold hidden in NBB1. pose proof OFFSRC as OFFSRC1. unfold hidden in OFFSRC1. pose proof NBSRC as NBSRC1. unfold hidden in NBSRC1.
    hide OLDBL. hide OLDBO. hide OLDB. pose proof SRCB as SRCB0. hide SRCB0.
    assert (MUr : munch [(NBP, NBP + 4); (SPV - 5248, SPV)] m m) by apply munch_refl.
    assert (WMr : wmono bsegs m m) by apply wmono_refl.
    assert (DSH : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(NBP, NBP + 4); (SPV - 5248, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear - X0 Hn Hb KLO LOS NBB1.
      split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
    assert (AAW : aappW [(NBP, NBP + 4); (SPV - 5248, SPV)]).
    { unfold aappW, KLOW, KHIGH. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
    (* [comment removed for export] *)
    carve_frame 112%nat STK.
    apply (rw_cells_split_CB bsegs m (SPV + -112) [] 112 junk [] [8; 8; 96]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (cb8_as_c8 bsegs m (SPV + -112) [] _ _ FR) as [fa FR1]. cbn [app] in FR1.
    destruct (cb8_as_c8 bsegs m (SPV + -112) [C8 fa] _ _ FR1) as [fb FR2]. cbn [app] in FR2. clear FR FR1. rename FR2 into FR.
    pose proof (USRC ltac:(lia)) as USRC1. destruct (SRCF ltac:(lia)) as (QS1 & QS2 & QS3 & QS4).
    assert (NTH1 : forall (l : list Z) (n : nat) (d : Z), (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l d]).
    { clear. induction l as [|c l IH]; intros [|n] d Hn; cbn in *; try lia; [reflexivity | apply IH; lia]. }
    set (b0 := nth (Z.to_nat 0) src 0).
    assert (B0R : 0 <= b0 < 256) by (subst b0; pose proof (proj1 (Forall_nth _ src) FBY (Z.to_nat 0) 0) as X; apply X; lia).
    assert (TB0 : bytes_at bsegs m (SRC + 0) [Z_to_bv 8 b0]).
    { pose proof (abytes_at_firstn _ _ _ 1 (abytes_at_skipn _ _ _ 0 SRCB ltac:(lia))) as B. rewrite firstn_map, (NTH1 src (Z.to_nat 0) 0) in B by lia. exact B. }
    replace (SRC + 0) with SRC in TB0 by lia.
    kx_autoFLAx [KAUnp DCTX 95992; KAUnp NBP 4; KAUnp SRC (zlen src); KAApp (SPV - 112) 112; KAApp NBP 4]
      [0x88928; 0x88bb8] 120%nat
      [KZRange SPV (17594333495296 + 5248) (2^47); KZRange DCTX 0x625000 (2^47 - 95992); KZRange SRC 4096 (2^47 - 2); KZRange NBP 0x625000 (2^47 - 4);
       KZRange (zlen src) 1 1; KZRange b0 0 255; KZAlign DCTX 8; KZAlign NBP 4;
       KZWr (SPV - 112) 112; KZWr NBP 4; KZDisj (SPV - 112) 112 DCTX 95992; KZDisj (SPV - 112) 112 NBP 4; KZDisj NBP 4 DCTX 95992; KZDisj (SPV - 112) 112 SRC (zlen src); KZDisj NBP 4 SRC (zlen src);
       KZRange (SRC + zlen src) 4096 (2^47)]
      [(SPV - 112, 112); (NBP, 4); (SRC, 1)] [(SPV - 112, 112); (NBP, 4)].
    all: try kx_cell_lit. all: try kx_z. all: try (kx_acc RSTKT). all: try (kx_acc QS1). all: try (kx_acc RIMG).
    all: try match goal with |- _ /\ _ <= KXKEND /\ _ => unfold KXKEND, KXSHLO, KXSHHI, KEND in *; repeat split; lia end.
    all: match goal with |- evtF _ _ _ _ => idtac | |- _ => repeat split; try lia; unfold off_stack, apart in *; sep_solve end.
    all: kx_read_ranges.
    all: clear SRCB TB0.
    all: kx_mem.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mq end.
    (* [comment removed for export] *)
    all: unfold hidden in SRCB0.
    all: assert (SRCBq : bytes_at bsegs mq SRC (map (Z_to_bv 8) src))
      by (eapply bytes_at_transport; [exact SRCB0| exact MUr|]; rewrite length_map; cbn [disjoint_from]; clear - OFFSRC1 NBSRC1 LOS; repeat split; lia).
    all: assert (AH1 : AHEAP AI L RNG st LB mq)
      by (eapply (AI_frame AI); [exact AH| exact MUr| exact WMr|]; constructor; [right; left; destruct IBN as (b & Hb & Hb1 & Hb2); exists b; cbn [fst snd]; split; [exact Hb| lia]| constructor; [left; left; cbn; lia| constructor]]).
    all: assert (UD1 : unpoisoned mq DCTX (DCTX + 95992)) by (eapply unpoisoned_munch; [exact UD| exact MUr| apply DSH; lia]).
    all: assert (UNB1 : unpoisoned mq NBP (NBP + 4)) by (eapply unpoisoned_munch; [exact UNB| exact MUr| apply DSH; lia]).
    all: assert (USRCq : 0 < zlen src -> unpoisoned mq SRC (SRC + zlen src)) by (intros Zp; eapply unpoisoned_munch; [exact (USRC Zp)| exact MUr| apply DSH; lia]).
    all: assert (HSRCq : 0 < zlen src -> ahull RNG mq SRC (zlen src)) by (intros Zp; eapply ahull_wmono; [exact WMr| exact (HSRC Zp)]).
    all: assert (ROC1 : aro_client RNG mq) by (eapply aro_client_transport; [exact ROC| exact MUr| exact WMr| exact AAW]).
    all: assert (MUq : munch (FOOTA L DCTX NBP SPV) m mq) by (eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside app]; intros x Hx; repeat split; lia).
    all: assert (FFRq : ffr_pres (W4 DCTX NBP) LB m mq) by (eapply ffr_pres_weaken; [eapply (sh_ffr_nbp AI); [exact AH| exact MUr| exact WMr| lia| exact NBB1]| unfold sub_fp; cbn [outside]; intros x Hx; tauto]).
    all: unfold hidden in OLDBL. all: unfold hidden in OLDBO. all: unfold hidden in OLDB.
    all: assert (OLDBLq : bytes_at bsegs mq TL bsL) by (eapply bytes_at_transport; [exact OLDBL| exact MUr|]; cbn [disjoint_from]; pose proof OFFL as X1; unfold hidden in X1; pose proof SNL as X2; unfold hidden in X2; clear - X1 X2 OLDLL LOS; repeat split; lia).
    all: assert (OLDBOq : bytes_at bsegs mq TO bsO) by (eapply bytes_at_transport; [exact OLDBO| exact MUr|]; cbn [disjoint_from]; pose proof OFFO as X1; unfold hidden in X1; pose proof SNO as X2; unfold hidden in X2; clear - X1 X2 OLDLO LOS; repeat split; lia).
    all: assert (OLDBq : bytes_at bsegs mq TM bsM) by (eapply bytes_at_transport; [exact OLDB| exact MUr|]; cbn [disjoint_from]; pose proof OFFM as X1; unfold hidden in X1; pose proof SNM as X2; unfold hidden in X2; clear - X1 X2 OLDL LOS; repeat split; lia).
    all: pose proof LOCL as LOCL1; unfold hidden in LOCL1; pose proof OFFL as OFFL1; unfold hidden in OFFL1; pose proof IMGL as IMGL1; unfold hidden in IMGL1.
    all: pose proof LOCO as LOCO1; unfold hidden in LOCO1; pose proof OFFO as OFFO1; unfold hidden in OFFO1; pose proof IMGO as IMGO1; unfold hidden in IMGO1.
    all: pose proof LOCM as LOCM1; unfold hidden in LOCM1; pose proof OFFM as OFFM1; unfold hidden in OFFM1; pose proof IMGM as IMGM1; unfold hidden in IMGM1.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 560056) _ _ _ _) => replace (ev KXE 47) with (Z_to_bv 64 0) in NB by (apply bv_eq; rewrite KXBR0; reflexivity)
         | |- _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 560056) _ _ _ _) =>
             eapply (SH_RET mq llt mlt oft _ _);
             [ split; [exact P0|]; split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact ELL|]; split; [exact EOF|]; split; [exact EML|];
               split; [exact EWK|]; split; [exact H3|]; split; [exact COLD|]; split; [exact NB|]; split; [exact SRCBq|]; split; [exact STK|];
               split; [eexists; eexists; exact FR|]; split; [exact KXMI|]; split; [exact MUq|]; split; [exact WMr|];
               split; [exact AH1|]; split; [exact FFRq|]; split; [exact UD1|]; split; [exact UNB1|]; split; [exact USRCq|]; split; [exact HSRCq| exact ROC1]
             | clear; lia
             | first [ left; reflexivity
                     | right; split; [clear - CLS; lia|]; exists 0; split; [reflexivity|]; split; [clear; lia|]; left;
                       split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact MUr] ] ]
         | |- _ => idtac end.
  Qed.

  Lemma sh_ent3 : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nb0 : word) TL bsL TO bsO TM bsM,
    rw_cells bsegs m DCTX [C8 llt] -> rw_cells bsegs m (DCTX + 8) [C8 mlt] -> rw_cells bsegs m (DCTX + 16) [C8 oft] -> rw_cells bsegs m (DCTX + 24) [C8 huf] ->
    stk bsegs m (DCTX + 32) (DCTX + 4136) -> stk bsegs m (DCTX + 4136) (DCTX + 6192) -> stk bsegs m (DCTX + 6192) (DCTX + 10296) ->
    stk bsegs m (DCTX + 27324) (DCTX + 29884) ->
    rw_cells bsegs m (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] -> rw_cells bsegs m (DCTX + 30204) [C4 cold] ->
    rw_cells bsegs m NBP [C4 nb0] -> bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> stk bsegs m lo SPV -> mem_inv bsegs m ->
    AHEAP AI L RNG st LB m -> art m -> unpoisoned m DCTX (DCTX + 95992) -> unpoisoned m NBP (NBP + 4) ->
    (0 < zlen src -> unpoisoned m SRC (SRC + zlen src)) -> (0 < zlen src -> ahull RNG m SRC (zlen src)) -> aro_client RNG m ->
    bytes_at bsegs m TL bsL -> zlen bsL <= 4104 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_LL 32 APZD_LL_DEFAULT LL_defaultDTable llt TL bsL) ->
    (TL = DCTX + 32 \/ (TL + 4104 <= DCTX \/ DCTX + 30372 <= TL)) -> (TL + 4104 <= lo \/ SPV <= TL) -> (TL = DCTX + 32 \/ TL + 4104 <= 0x30000) ->
    (TL + 4104 <= NBP \/ NBP + 4 <= TL) ->
    bytes_at bsegs m TO bsO -> zlen bsO <= 2056 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_OF 4136 APZD_OF_DEFAULT OF_defaultDTable oft TO bsO) ->
    (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) -> (TO + 2056 <= lo \/ SPV <= TO) -> (TO = DCTX + 4136 \/ TO + 2056 <= 0x30000) ->
    (TO + 2056 <= NBP \/ NBP + 4 <= TO) ->
    bytes_at bsegs m TM bsM -> zlen bsM <= 4104 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_ML 6192 APZD_ML_DEFAULT ML_defaultDTable mlt TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) -> (TM = DCTX + 6192 \/ TM + 4104 <= 0x30000) ->
    (TM + 4104 <= NBP \/ NBP + 4 <= TM) ->
    zlen src = 3 ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) (Z_to_bv 64 NBP) (Z_to_bv 64 SRC) (Z_to_bv 64 (zlen src))
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8889c) fc None m (seg_rom bsegs)).
  Proof.
    intros until bsM. intros P0 P1 P2 P3 ELL EOF EML EWK H3 COLD NB SRCB STK MI AH ART UD UNB USRC HSRC ROC
           OLDBL OLDLL OLDVL LOCL OFFL IMGL SNL OLDBO OLDLO OLDVO LOCO OFFO IMGO SNO OLDB OLDL OLDV LOCM OFFM IMGM SNM CLS. open_shhA HY.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct ART as (GOT & RIC & SHB0 & INI & LAY & REAL). destruct AST as (KLO' & RSTK & RIMG).
    pose proof NBB as NBB1. unfold hidden in NBB1. pose proof OFFSRC as OFFSRC1. unfold hidden in OFFSRC1. pose proof NBSRC as NBSRC1. unfold hidden in NBSRC1.
    hide OLDBL. hide OLDBO. hide OLDB. pose proof SRCB as SRCB0. hide SRCB0.
    assert (MUr : munch [(NBP, NBP + 4); (SPV - 5248, SPV)] m m) by apply munch_refl.
    assert (WMr : wmono bsegs m m) by apply wmono_refl.
    assert (DSH : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(NBP, NBP + 4); (SPV - 5248, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear - X0 Hn Hb KLO LOS NBB1.
      split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
    assert (AAW : aappW [(NBP, NBP + 4); (SPV - 5248, SPV)]).
    { unfold aappW, KLOW, KHIGH. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
    (* [comment removed for export] *)
    carve_frame 112%nat STK.
    apply (rw_cells_split_CB bsegs m (SPV + -112) [] 112 junk [] [8; 8; 96]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (cb8_as_c8 bsegs m (SPV + -112) [] _ _ FR) as [fa FR1]. cbn [app] in FR1.
    destruct (cb8_as_c8 bsegs m (SPV + -112) [C8 fa] _ _ FR1) as [fb FR2]. cbn [app] in FR2. clear FR FR1. rename FR2 into FR.
    pose proof (USRC ltac:(lia)) as USRC1. destruct (SRCF ltac:(lia)) as (QS1 & QS2 & QS3 & QS4).
    assert (NTH1 : forall (l : list Z) (n : nat) (d : Z), (n < length l)%nat -> firstn 1 (skipn n l) = [nth n l d]).
    { clear. induction l as [|c l IH]; intros [|n] d Hn; cbn in *; try lia; [reflexivity | apply IH; lia]. }
    set (b0 := nth (Z.to_nat 0) src 0).
    assert (B0R : 0 <= b0 < 256) by (subst b0; pose proof (proj1 (Forall_nth _ src) FBY (Z.to_nat 0) 0) as X; apply X; lia).
    assert (TB0 : bytes_at bsegs m (SRC + 0) [Z_to_bv 8 b0]).
    { pose proof (abytes_at_firstn _ _ _ 1 (abytes_at_skipn _ _ _ 0 SRCB ltac:(lia))) as B. rewrite firstn_map, (NTH1 src (Z.to_nat 0) 0) in B by lia. exact B. }
    set (b1 := nth (Z.to_nat 1) src 0).
    assert (B1R : 0 <= b1 < 256) by (subst b1; pose proof (proj1 (Forall_nth _ src) FBY (Z.to_nat 1) 0) as X; apply X; lia).
    assert (TB1 : bytes_at bsegs m (SRC + 1) [Z_to_bv 8 b1]).
    { pose proof (abytes_at_firstn _ _ _ 1 (abytes_at_skipn _ _ _ 1 SRCB ltac:(lia))) as B. rewrite firstn_map, (NTH1 src (Z.to_nat 1) 0) in B by lia. exact B. }
    set (b2 := nth (Z.to_nat 2) src 0).
    assert (B2R : 0 <= b2 < 256) by (subst b2; pose proof (proj1 (Forall_nth _ src) FBY (Z.to_nat 2) 0) as X; apply X; lia).
    assert (TB2 : bytes_at bsegs m (SRC + 2) [Z_to_bv 8 b2]).
    { pose proof (abytes_at_firstn _ _ _ 1 (abytes_at_skipn _ _ _ 2 SRCB ltac:(lia))) as B. rewrite firstn_map, (NTH1 src (Z.to_nat 2) 0) in B by lia. exact B. }
    replace (SRC + 0) with SRC in TB0 by lia.
    kx_autoFLAx [KAUnp DCTX 95992; KAUnp NBP 4; KAUnp SRC (zlen src); KAApp (SPV - 112) 112; KAApp NBP 4]
      [0x88928; 0x88bb8] 120%nat
      [KZRange SPV (17594333495296 + 5248) (2^47); KZRange DCTX 0x625000 (2^47 - 95992); KZRange SRC 4096 (2^47 - 4); KZRange NBP 0x625000 (2^47 - 4);
       KZRange (zlen src) 3 3; KZRange b0 0 255; KZRange b1 0 255; KZRange b2 0 255; KZAlign DCTX 8; KZAlign NBP 4;
       KZWr (SPV - 112) 112; KZWr NBP 4; KZDisj (SPV - 112) 112 DCTX 95992; KZDisj (SPV - 112) 112 NBP 4; KZDisj NBP 4 DCTX 95992; KZDisj (SPV - 112) 112 SRC (zlen src); KZDisj NBP 4 SRC (zlen src);
       KZRange (SRC + zlen src) 4096 (2^47)]
      [(SPV - 112, 112); (NBP, 4); (SRC, 1); (SRC + 1, 1); (SRC + 2, 1)] [(SPV - 112, 112); (NBP, 4)].
    all: try kx_cell_lit. all: try kx_z. all: try (kx_acc RSTKT). all: try (kx_acc QS1). all: try (kx_acc RIMG).
    all: try match goal with |- _ /\ _ <= KXKEND /\ _ => unfold KXKEND, KXSHLO, KXSHHI, KEND in *; repeat split; lia end.
    all: match goal with |- evtF _ _ _ _ => idtac | |- _ => repeat split; try lia; unfold off_stack, apart in *; sep_solve end.
    all: kx_read_ranges.
    all: clear SRCB TB0 TB1 TB2.
    all: kx_mem.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mq end.
    (* [comment removed for export] *)
    all: unfold hidden in SRCB0.
    all: assert (SRCBq : bytes_at bsegs mq SRC (map (Z_to_bv 8) src))
      by (eapply bytes_at_transport; [exact SRCB0| exact MUr|]; rewrite length_map; cbn [disjoint_from]; clear - OFFSRC1 NBSRC1 LOS; repeat split; lia).
    all: assert (AH1 : AHEAP AI L RNG st LB mq)
      by (eapply (AI_frame AI); [exact AH| exact MUr| exact WMr|]; constructor; [right; left; destruct IBN as (b & Hb & Hb1 & Hb2); exists b; cbn [fst snd]; split; [exact Hb| lia]| constructor; [left; left; cbn; lia| constructor]]).
    all: assert (UD1 : unpoisoned mq DCTX (DCTX + 95992)) by (eapply unpoisoned_munch; [exact UD| exact MUr| apply DSH; lia]).
    all: assert (UNB1 : unpoisoned mq NBP (NBP + 4)) by (eapply unpoisoned_munch; [exact UNB| exact MUr| apply DSH; lia]).
    all: assert (USRCq : 0 < zlen src -> unpoisoned mq SRC (SRC + zlen src)) by (intros Zp; eapply unpoisoned_munch; [exact (USRC Zp)| exact MUr| apply DSH; lia]).
    all: assert (HSRCq : 0 < zlen src -> ahull RNG mq SRC (zlen src)) by (intros Zp; eapply ahull_wmono; [exact WMr| exact (HSRC Zp)]).
    all: assert (ROC1 : aro_client RNG mq) by (eapply aro_client_transport; [exact ROC| exact MUr| exact WMr| exact AAW]).
    all: assert (MUq : munch (FOOTA L DCTX NBP SPV) m mq) by (eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside app]; intros x Hx; repeat split; lia).
    all: assert (FFRq : ffr_pres (W4 DCTX NBP) LB m mq) by (eapply ffr_pres_weaken; [eapply (sh_ffr_nbp AI); [exact AH| exact MUr| exact WMr| lia| exact NBB1]| unfold sub_fp; cbn [outside]; intros x Hx; tauto]).
    all: unfold hidden in OLDBL. all: unfold hidden in OLDBO. all: unfold hidden in OLDB.
    all: assert (OLDBLq : bytes_at bsegs mq TL bsL) by (eapply bytes_at_transport; [exact OLDBL| exact MUr|]; cbn [disjoint_from]; pose proof OFFL as X1; unfold hidden in X1; pose proof SNL as X2; unfold hidden in X2; clear - X1 X2 OLDLL LOS; repeat split; lia).
    all: assert (OLDBOq : bytes_at bsegs mq TO bsO) by (eapply bytes_at_transport; [exact OLDBO| exact MUr|]; cbn [disjoint_from]; pose proof OFFO as X1; unfold hidden in X1; pose proof SNO as X2; unfold hidden in X2; clear - X1 X2 OLDLO LOS; repeat split; lia).
    all: assert (OLDBq : bytes_at bsegs mq TM bsM) by (eapply bytes_at_transport; [exact OLDB| exact MUr|]; cbn [disjoint_from]; pose proof OFFM as X1; unfold hidden in X1; pose proof SNM as X2; unfold hidden in X2; clear - X1 X2 OLDL LOS; repeat split; lia).
    all: pose proof LOCL as LOCL1; unfold hidden in LOCL1; pose proof OFFL as OFFL1; unfold hidden in OFFL1; pose proof IMGL as IMGL1; unfold hidden in IMGL1.
    all: pose proof LOCO as LOCO1; unfold hidden in LOCO1; pose proof OFFO as OFFO1; unfold hidden in OFFO1; pose proof IMGO as IMGO1; unfold hidden in IMGO1.
    all: pose proof LOCM as LOCM1; unfold hidden in LOCM1; pose proof OFFM as OFFM1; unfold hidden in OFFM1; pose proof IMGM as IMGM1; unfold hidden in IMGM1.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 560056) _ _ _ _) =>
             eapply (SH_RET mq llt mlt oft _ _);
             [ split; [exact P0|]; split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact ELL|]; split; [exact EOF|]; split; [exact EML|];
               split; [exact EWK|]; split; [exact H3|]; split; [exact COLD|]; split; [exact NB|]; split; [exact SRCBq|]; split; [exact STK|];
               split; [eexists; eexists; exact FR|]; split; [exact KXMI|]; split; [exact MUq|]; split; [exact WMr|];
               split; [exact AH1|]; split; [exact FFRq|]; split; [exact UD1|]; split; [exact UNB1|]; split; [exact USRCq|]; split; [exact HSRCq| exact ROC1]
             | clear; lia
             | first [ left; reflexivity
                     | right; split; [clear - CLS; lia|]; exists 0; split; [reflexivity|]; split; [clear; lia|]; left;
                       split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact MUr] ] ]
         | |- _ => idtac end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (SRC + 2)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 559400) _ _ _ _) =>
             rewrite Z.mod_small in KXBR by (clear - KXRR; lia); rewrite Z.mod_small in KXBR1 by (clear - KXRR KXBR KXRR2; lia);
             assert (NBRg : 1 <= 256 * bv_unsigned (ev KXE 49) + bv_unsigned (ev KXE 56) + -32768 <= 98047) by (clear - KXRR KXRR2 KXBR KXBR1; lia);
             replace (SRC + 3) with (SRC + 2 + 1) by (clear; lia);
             eapply (SH_LL mq llt mlt oft (256 * bv_unsigned (ev KXE 49) + bv_unsigned (ev KXE 56) + -32768) 2 TL bsL TO bsO TM bsM);
             first [ exact OLDBLq | exact OLDBOq | exact OLDBq | exact OLDVL | exact OLDVO | exact OLDV | exact LOCL1 | exact OFFL1 | exact IMGL1
                   | exact LOCO1 | exact OFFO1 | exact IMGO1 | exact LOCM1 | exact OFFM1 | exact IMGM1 | exact OLDLL | exact OLDLO | exact OLDL | exact NBRg | reflexivity
                   | split; [exact P0|]; split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact ELL|]; split; [exact EOF|]; split; [exact EML|];
               split; [exact EWK|]; split; [exact H3|]; split; [exact COLD|]; split; [exact NB|]; split; [exact SRCBq|]; split; [exact STK|];
               split; [eexists; eexists; exact FR|]; split; [exact KXMI|]; split; [exact MUq|]; split; [exact WMr|];
               split; [exact AH1|]; split; [exact FFRq|]; split; [exact UD1|]; split; [exact UNB1|]; split; [exact USRCq|]; split; [exact HSRCq| exact ROC1]
                   | clear - CLS; lia ]
         | |- _ => idtac end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (SRC + 1)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 559400) _ _ _ _) =>
             rewrite Z.mod_small in KXBR by (clear - KXRR; lia); rewrite <- (Z_to_bv_bv_unsigned (ev KXE 49)) in NB; rewrite <- (Z_to_bv_bv_unsigned (ev KXE 49));
             assert (NBRg : 1 <= bv_unsigned (ev KXE 49) <= 98047) by (clear - KXRR KXBR KXBR0; lia);
             replace (SRC + 2) with (SRC + 1 + 1) by (clear; lia);
             eapply (SH_LL mq llt mlt oft (bv_unsigned (ev KXE 49)) 1 TL bsL TO bsO TM bsM);
             first [ exact OLDBLq | exact OLDBOq | exact OLDBq | exact OLDVL | exact OLDVO | exact OLDV | exact LOCL1 | exact OFFL1 | exact IMGL1
                   | exact LOCO1 | exact OFFO1 | exact IMGO1 | exact LOCM1 | exact OFFM1 | exact IMGM1 | exact OLDLL | exact OLDLO | exact OLDL | exact NBRg | reflexivity
                   | split; [exact P0|]; split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact ELL|]; split; [exact EOF|]; split; [exact EML|];
               split; [exact EWK|]; split; [exact H3|]; split; [exact COLD|]; split; [exact NB|]; split; [exact SRCBq|]; split; [exact STK|];
               split; [eexists; eexists; exact FR|]; split; [exact KXMI|]; split; [exact MUq|]; split; [exact WMr|];
               split; [exact AH1|]; split; [exact FFRq|]; split; [exact UD1|]; split; [exact UNB1|]; split; [exact USRCq|]; split; [exact HSRCq| exact ROC1]
                   | clear - CLS; lia ]
         | |- _ => idtac end.
  Qed.

End SH.
End SHS.
End CANSEC1.
