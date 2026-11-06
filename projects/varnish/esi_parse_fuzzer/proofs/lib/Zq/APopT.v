(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMTac AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalmys AMaldga AMalrrv ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopP.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_3ti ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_png AMalnrk ARtSscs ARtSoqz ANodeA6 APopSA APopSB APopSC APopSD APopTE APopCtx APopE.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalnrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopSA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopSB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopSC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopSD OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopTE OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopCtx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@Q2; @Q5; @B5; @B1; @B3; @L1; @CE; @R1; @H5; @B4; @H3; @B2; @Q4; @Hi; @Q6; @CSR; @Q3; @R6; @F0; @RANGE; @Q1; @PU1; @Lt4; @Hal; @X; @U0; @H1; @H2; @Lt1; @SEP_ts; @NEEDMAP; @PN2; @Hz; @EF; @L; @Ha; @R10; @NU; @FEB; @SEP_tr; @PU; @FEQ; @SHGEO; @U21; @CLO; @Hu; @Hf; @X0; @NS; @CEIL; @G4; @PF1; @Q9; @NOFIT; @PU4; @D1; @PU5; @A1; @A5; @L2; @S1; @S2; @D0; @R8; @G3; @Z64; @Hx; @LO; @K0'; @NP; @NRQ; @LOSA; @SAHI; @HI47; @G; @R2; @NTL; @PN3; @CAP0; @PF3; @NF; @NFS; @NE0; @ROOM; @G1; @G2; @E1; @M1; @E2; @E3; @M3; @SPH; @S3; @S4; @NFx; @NFSx; @FAST; @PN1; @RIR; @SBR; @FIT])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.


(* [comment removed for export] *)
Lemma inside_pos : forall (W : list (Z * Z)) (k : nat) (lo hi a n : Z), nth_error W k = Some (lo, hi) -> lo <= a /\ a + n <= hi -> inside W a n.
Proof.
  induction W as [|[l h] W IH]; intros [|k] lo hi a n E H; cbn [nth_error] in E; try discriminate.
  - injection E as -> ->. left. exact H.
  - right. exact (IH k lo hi a n E H).
Qed.
Ltac inside_at k :=
  lazymatch goal with |- inside ?WW ?a ?n =>
    let e := eval cbv [nth_error WW] in (nth_error WW k) in
    lazymatch e with Some (?lo, ?hi) => refine (inside_pos WW k lo hi a n eq_refl _) end
  end.
Section Arm.
Context {Clg : Ceiling}.
  Variables (rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z).
  Hypothesis PRE : alloc_core_pre rac spa (cl_tp LPA) m md A n canfill stkobj lo hi key.
  Hypothesis NP : n <= kMaxPrimaryUser.
  Hypothesis EMP : pk_chunks (a_cache A (class_of n)) = [].
  Hypothesis SHORT : Z.of_nat (length (rg_free (a_reg A (class_of n)))) < refill_count (class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation c := (class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation tp := (cl_tp LPA).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation ctx := (p_ctx (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (p_thr (a_pl A) + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (bv_unsigned spa + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation rbs := (a_sb A + class_of n * 4294967296).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) (class_of n) + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A (class_of n))))).
  #[warnings="-notation-for-abbreviation"] Local Notation kk := (refill_count (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation U := (pop_ums A (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation N := (pop_nc A (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation Fm := (pop_fam A (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation CY := (carry rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A n canfill stkobj).
  #[warnings="-notation-for-abbreviation"] Local Notation RW := (regw A n).
  #[warnings="-notation-for-abbreviation"] Local Notation Wi := (pk_Wi spa A n).

  Let AI : @pa_ainv _ DepotRepL A m md. Proof. exact (proj1 PRE). Qed.
  Let NR : 1 <= n <= kMaxPrimaryUser. Proof. destruct PRE as (_ & _ & NRQ & _). lia. Qed.
  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let CEIL : alloc_ceiling <= sa - 1024. Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CLO & LOSA & _). lia. Qed.
  Let MIv : mem_inv rsegs v. Proof. exact (proj1 (proj2 PRE)). Qed.
  Let PREF : 0 <= canfill <= 1 /\ alloc_ceiling <= lo /\ lo <= sa - 4096 /\ sa <= hi /\ hi <= 2^47 /\ sa mod 16 = 0 /\ bv_unsigned rac mod 2 = 0 /\
             stk rsegs v lo sa /\ sa <= stkobj /\ stkobj + 2064 <= hi.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CF & _ & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & _ & SOLO & SOHI & _). cbn [cl_segs LPA] in ST. exact (conj CF (conj CLO (conj LOSA (conj SAHI (conj HI47 (conj SPA (conj RAC2 (conj ST (conj SOLO SOHI))))))))). Qed.
  Let KS : Z.shiftr (max_count c) 1 = kk. Proof. exact (proj1 (proj2 (proj2 (ar_k A c CR)))). Qed.
  #[warnings="-notation-for-abbreviation"] Local Notation LIN := (pk_lin spa m md A n AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation Wle := (pk_Wi_le spa A n).
  #[warnings="-notation-for-abbreviation"] Local Notation Wmono := (pk_Wi_mono spa A n).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_step := (carry_step rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A n canfill stkobj NR).
  #[warnings="-notation-for-abbreviation"] Local Notation rw_step := (regw_step A n).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_statics := (carry_statics rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A n canfill stkobj AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_ro_hi := (carry_ro_hi rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A n canfill stkobj AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_bytes_hi := (carry_bytes_hi rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A n canfill stkobj AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_oom := (carry_oom rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A n canfill stkobj AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_na := (carry_na rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A n canfill stkobj AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_thr_mapped := (carry_thr_mapped rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A n canfill stkobj AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_tst := (carry_tst rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A n canfill stkobj AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_stm := (carry_stm rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A n canfill stkobj AI NR EMP SHORT CEIL).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_mapped := (carry_mapped rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A n canfill stkobj).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_NN := (carry_NN rac spa s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A n canfill stkobj).

  Variable (T1 : TSet).
  Hypothesis K1 : alloc_core_K1v rac spa gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1.

  #[warnings="-notation-for-abbreviation"] Local Notation e_par := (par_facts rac spa m md A n canfill stkobj lo hi key PRE NP EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation e_seg := (seg_pre rac spa m md A n canfill stkobj lo hi key PRE NP EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation HU := (pa_hull (popg A (class_of n) (pop_ums A (class_of n)) 0 0)).
  #[warnings="-notation-for-abbreviation"] Local Notation HF := (pa_hull (popg A (class_of n) (pop_ums A (class_of n)) (pop_fam A (class_of n)) 0)).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation AgU := (popg A (class_of n) (pop_ums A (class_of n)) 0 0).
  #[warnings="-notation-for-abbreviation"] Local Notation AgF := (popg A (class_of n) (pop_ums A (class_of n)) (pop_fam A (class_of n)) 0).
  #[warnings="-notation-for-abbreviation"] Local Notation HLU := (pa_lhull (popg A (class_of n) (pop_ums A (class_of n)) 0 0)).
  #[warnings="-notation-for-abbreviation"] Local Notation HLF := (pa_lhull (popg A (class_of n) (pop_ums A (class_of n)) (pop_fam A (class_of n)) 0)).
  #[warnings="-notation-for-abbreviation"] Local Notation GPp := (gp_post rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A n canfill stkobj lo key).

  (* [comment removed for export] *)
  Ltac lin_open :=
    let L := fresh "L" in pose proof LIN as L;
    destruct L as (L1 & L2 & (Lt1 & Lt2 & Lt3 & Lt4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)).
  Tactic Notation "cv" constr(k) := split; [right; (let kn := lazymatch type of k with Z => eval cbv in (Z.to_nat k) | _ => k end in inside_at kn); lia|].
  Ltac sub_open := apply sub_fp_all_inside; unfold pk_Wi, pop_Wi, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [app]; destruct (a_cache_inited A); (lazymatch goal with |- all_inside ?W' _ => let WW := fresh "WW" in set (WW := W') end); cbn [all_inside app].
  Ltac dj_tac := unfold pk_Wi, pop_Wi, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [disjoint_from app]; try (destruct (a_cache_inited A));
                 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; lia.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CEIL CE PRE key stkobj canfill n md spa rac"] Lemma t_SMW : mapped v lo (hi - lo).
  Proof.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CLO & LOSA & SAHI & HI47 & _ & _ & ST & SM & _). cbn [cl_segs LPA] in ST.
    intros i Hi. destruct (Z_lt_le_dec (lo + i) sa) as [L|G].
    - (first [ dand3 ST as _ _ ST3 | destruct ST as (_ & _ & ST3) ]). destruct (ST3 (lo + i) ltac:(lia)) as [X _]. unfold wview, wa in X.
      intros E0. apply X. rewrite E0. rewrite unsigned_lit by lia. rewrite (pa_find_segment_none (lo + i) 1); [reflexivity| lia| right; lia].
    - replace (lo + i) with (sa + (lo + i - sa)) by lia. apply SM. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md spa rac"] Lemma t_VNEW : forall ums, mu + ums <= kFreeArrayOffset -> forall a, rb + mu <= a < rb + mu + ums -> v (wz a) = None.
  Proof.
    intros ums Hu a Ha. lin_open. unfold aview_of, mrestrict, hidc.
    rewrite unsigned_lit by (unfold region_beg, kRegionSize, kFreeArrayOffset in *; lia).
    assert (DEADB : forall dlo dhi, In (dlo, dhi) (a_deadsh A) -> dhi <= kHighMemBeg).
    { intros dlo dhi Hd. (first [ pose proof ((wfE A W0)) as dR_2; dand3 dR_2 as _ DF0 _ | destruct (wfE A W0) as (_ & DF0 & _) ]). pose proof (proj1 (Forall_forall _ _) DF0 _ Hd) as (D1 & _). cbn [fst snd] in D1. kung_all. unfold kShadowGapBeg in *. lia. }
    rewrite (prim_unmapped_hidden A (WFT_of_WF A W0) (ai_extra _ _ _ _ _ _ _ AI) DEADB c a CR); [reflexivity|]. left. lia.
  Qed.
  #[using="CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md spa rac"] Lemma t_VNEWF : forall fam, mfa + fam <= kFreeArraySize -> forall a, fa + mfa <= a < fa + mfa + fam -> v (wz a) = None.
  Proof.
    intros fam Hf a Ha. lin_open. unfold aview_of, mrestrict, hidc.
    rewrite unsigned_lit by (unfold region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in *; lia).
    assert (DEADB : forall dlo dhi, In (dlo, dhi) (a_deadsh A) -> dhi <= kHighMemBeg).
    { intros dlo dhi Hd. (first [ pose proof ((wfE A W0)) as dR_3; dand3 dR_3 as _ DF0 _ | destruct (wfE A W0) as (_ & DF0 & _) ]). pose proof (proj1 (Forall_forall _ _) DF0 _ Hd) as (D1 & _). cbn [fst snd] in D1. kung_all. unfold kShadowGapBeg in *. lia. }
    rewrite (prim_unmapped_hidden A (WFT_of_WF A W0) (ai_extra _ _ _ _ _ _ _ AI) DEADB c a CR); [reflexivity|]. right.
    unfold region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac Clg"] Lemma t_UMS0 : 0 <= 0 /\ 0 mod kUserMapSize = 0 /\ mu + 0 < au + 9 * size + kUserMapSize /\ au <= size * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.   (* [comment removed for export] *)
  Proof. pose proof (ar_reg A c W0 CR) as ((R1 & R2) & _). pose proof (ar_cap A c W0 CR EMP SHORT) as CAP. unfold kUserMapSize in *. split; [clear; hot_lia_full|]. split; [reflexivity|]. split; [clear - R2; hot_lia_full| exact CAP]. Qed.
  #[using="NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac Clg"] Lemma t_UMS : 0 <= U /\ U mod kUserMapSize = 0 /\ mu + U < au + 9 * size + kUserMapSize /\ au <= size * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c. Proof. exact (pk_UMS m md A n AI NR EMP SHORT). Qed.
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac Clg"] Lemma t_FAM0 : 0 <= 0 /\ 0 mod kFreeArrayMapSize = 0 /\ mfa + 0 <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + 0 <= kFreeArraySize.   (* [comment removed for export] *)
  Proof. pose proof (ar_reg A c W0 CR) as (_ & _ & _ & _ & R5 & _ & _ & _ & R10 & _). unfold kFreeArrayMapSize in *. split; [clear; hot_lia_full|]. split; [reflexivity|]. split; [clear - R10; hot_lia_full| clear - R5; hot_lia_full]. Qed.
  #[using="NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac Clg"] Lemma t_FAM : 0 <= Fm /\ Fm mod kFreeArrayMapSize = 0 /\ mfa + Fm <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + Fm <= kFreeArraySize. Proof. exact (pk_FAM m md A n AI NR EMP SHORT). Qed.
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac Clg"] Lemma t_TAIL0 : forall ums, ums = 0 \/ ums = U -> mu + ums < au + 0 * size + 9 * size + kUserMapSize.
  Proof.
    intros ums Hu. (first [ pose proof (e_par) as dR_6; dand8 dR_6 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    pose proof (ar_reg A c W0 CR) as ((_ & R2) & _). unfold kUserMapSize. destruct Hu as [->| ->]; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="K1 PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE hi"] Lemma grant_tail : forall (Rg : bvmap 5 word) (pc : word) (Mk : mem) (mdk : Model),
    (forall a, hidc HF a = true -> Mk a = m a) ->
    pop_mod AgF md mdk -> MInv HF HLF (pa_eager A + U + Fm) mdk ->   (* [comment removed for export] *)
    evt rsegs (fun st => exists junk0 pad scr ksc, GPp junk0 pad scr ksc st) (MS Rg F pc fc None (aview_of HF Mk) (seg_rom rsegs)) ->
    srealizes rsegs (mkCfg (MS Rg F pc fc None Mk (seg_rom rsegs)) mdk) T1.
  Proof.
    (intros Rg pc Mk mdk MSH; (first [ intro dR_41; dand6 dR_41 as V LED COV TOP AMD HH | intros (V & LED & COV & TOP & AMD & HH) ]); intros HI EV).
    rewrite (popg_hull_nc A c U Fm 0 N) in MSH, HI, EV. rewrite (popg_lhull_nc A c U Fm 0 N) in HI.
    pose proof (aledger_reg _ _ _ (a_reg (popg A c U Fm N)) _ _ (fun c' _ => popg_mapped_nc A c U Fm N 0 c') LED) as LEDN.
    (first [ pose proof (e_par) as dR_10; dand8 dR_10 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof ((ar_nc A c W0 CR EMP SHORT)) as dR_11; dand4 dR_11 as _ _ NTL _ | pose proof (ar_nc A c W0 CR EMP SHORT) as (_ & _ & NTL & _) ]).
    eapply (srz_evt_restrict rsegs (pa_hull (popg A c U Fm N)) (hull_segsR _) pa_wxR _ (pa_eager A + U + Fm) _ _ mdk T1 HI HH).
    { rewrite restrict_MS. exact EV. }
    intros msr' md' Q HI' SB CL.
    (first [ dex21 Q as junk0 pad scr ksc tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na v5; destruct Q as [-> GPK] | dand23 Q as junk0 pad scr ksc tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na v5 -> GPK | destruct Q as (junk0 & pad & scr & ksc & tq0 & tq1 & tq2 & aq1 & aq2 & aq3 & aq4 & aq5 & aq6 & aq7 & tq3 & tq4 & tq5 & tq6 & a0g & na & v5 & -> & GPK) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in CL |- *.
    (first [ dand25 GPK as MU5 NN5 ST5 MI5 LKS P_mxL P_nf P_mfa P_au P_mu P_ex P_na P_fa P_newU P_newF P_shU P_shF P_line P_lines P_s1a P_comb P_ref P_gfa TRC5 TRB5 | destruct GPK as (MU5 & NN5 & ST5 & MI5 & LKS & P_mxL & P_nf & P_mfa & P_au & P_mu & P_ex & P_na & P_fa & P_newU & P_newF & P_shU & P_shF & P_line & P_lines
                     & P_s1a & P_comb & P_ref & P_gfa & TRC5 & TRB5) ]).
    destruct PREF as (CF & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SOLO & SOHI).
    destruct PRE as (_ & _ & _ & _ & LIM & NLV & TINY & _ & PCRED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEYU & KR).
    assert (HI'' : MInv (pa_hull (popg A c U Fm N)) (pa_lhull (popg A c U Fm N)) (pa_eager (popg A c U Fm N)) md') by (rewrite (popg_eager A c U Fm N CR t_UMS t_FAM); exact HI').
    exact (pop_finishG rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key T1 U Fm N
             AI NR EMP TINY PCRED LIM NLV CF CLO LOSA SAHI HI47 SPA RAC2 t_SMW SOLO SOHI KEYU KR t_UMS t_FAM (pk_NC m md A n AI NR EMP SHORT) (pk_POS m md A n AI NR EMP SHORT)
             ltac:(unfold kUserMapSize; lia) ltac:(lia)
             (t_VNEW U ltac:(unfold kFreeArrayOffset; lia)) (t_VNEWF Fm ltac:(unfold kFreeArraySize; lia)) K1
             Mk mdk md' v5 a0g (wz thr) (wz 1) ksc junk0 pad scr MSH V LEDN HH AMD HI'' SB CL MU5 NN5 ST5 MI5 LKS
             P_mxL P_nf P_mfa P_au P_mu P_ex P_fa P_newU P_newF P_shU P_shF P_line P_lines P_s1a P_comb P_ref P_gfa TRC5 TRB5
             tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="spa rac"] Lemma tRBE : rbs = rb. Proof. unfold region_beg, kRegionSize. lia. Qed.
  Lemma hull_000 : pa_hull (popg A c 0 0 0) = pa_hull A. Proof. rewrite popg_zero. reflexivity. Qed.
  Lemma lhull_000 : pa_lhull (popg A c 0 0 0) = pa_lhull A. Proof. rewrite popg_zero. reflexivity. Qed.   (* [comment removed for export] *)

  #[using="CEIL CE CR W0 NR AI NP PRE key hi lo stkobj canfill md m spa rac"] Lemma hull_le_gen : forall u f x u' f' x', 0 <= u <= u' -> 0 <= f <= f' -> hull_le (pa_hull (popg A c u f x)) (pa_hull (popg A c u' f' x')).
  Proof.
    intros u f x u' f' x' Hu Hf.
    unfold pa_hull, ahull_of, ahull_of_, aregions_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh].
    rewrite !hull_of_app.
    apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply classes_regions_le. intros c'. unfold reg_upd. (first [ pose proof ((wfR A W0)) as dR_14; dand3 dR_14 as WR WZ _ | destruct (wfR A W0) as (WR & WZ & _) ]).
    destruct (Z.eqb_spec c' c) as [->|NE].
    - cbn [grow rg_mapped_user rg_mapped_fa]. (first [ pose proof ((WR c CR)) as dR_15; dand6 dR_15 as A1 _ _ _ A5 _ | destruct (WR c CR) as (A1 & _ & _ & _ & A5 & _) ]). lia.
    - destruct (Z_le_dec 1 c') as [L|L]; [destruct (Z_le_dec c' 30) as [L2|L2]|].
      + (first [ pose proof ((WR c' ltac:(lia))) as dR_16; dand6 dR_16 as A1 _ _ _ A5 _ | destruct (WR c' ltac:(lia)) as (A1 & _ & _ & _ & A5 & _) ]). lia.
      + rewrite (WZ c') by lia. cbn. lia.
      + rewrite (WZ c') by lia. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CEIL CE CR W0 NR AI NP PRE key hi lo stkobj canfill md m spa rac"] Lemma lhull_le_gen : forall u f x u' f' x', 0 <= u <= u' -> 0 <= f <= f' -> hull_le (pa_lhull (popg A c u f x)) (pa_lhull (popg A c u' f' x')).
  Proof.
    intros u f x u' f' x' Hu Hf.
    unfold pa_lhull, alhull_of, alhull_of_, alregions_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh].
    rewrite !hull_of_app.
    apply hull_le_app2; [| apply hull_le_refl]. apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply lclasses_regions_le. intros c'. unfold reg_upd. (first [ pose proof ((wfR A W0)) as dR_14; dand3 dR_14 as WR WZ _ | destruct (wfR A W0) as (WR & WZ & _) ]).
    destruct (Z.eqb_spec c' c) as [->|NE].
    - cbn [grow rg_mapped_user rg_mapped_fa]. (first [ pose proof ((WR c CR)) as dR_15; dand6 dR_15 as A1 _ _ _ A5 _ | destruct (WR c CR) as (A1 & _ & _ & _ & A5 & _) ]). lia.
    - destruct (Z_le_dec 1 c') as [L|L]; [destruct (Z_le_dec c' 30) as [L2|L2]|].
      + (first [ pose proof ((WR c' ltac:(lia))) as dR_16; dand6 dR_16 as A1 _ _ _ A5 _ | destruct (WR c' ltac:(lia)) as (A1 & _ & _ & _ & A5 & _) ]). lia.
      + rewrite (WZ c') by lia. cbn. lia.
      + rewrite (WZ c') by lia. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac"] Lemma newh_U : forall x, in_hullb HU x = true -> in_hullb (pa_hull A) x = false ->
    (rbs + mu <= x < rbs + mu + U) \/ (sh (rbs + mu) <= x < sh (rbs + mu) + U / 8).
  Proof.
    intros x X1 X0. rewrite tRBE.
    destruct (pop_hull_cases A c U 0 0 W0 CR t_UMS t_FAM0 x X1) as [OLD|[NU|[NS|[NF|NFS]]]].
    - rewrite OLD in X0. discriminate.
    - left. exact NU.
    - right. exact NS.
    - exfalso. lia.
    - exfalso. change (0 / 8) with 0 in NFS. lia.
  Qed.
  #[using="CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac"] Lemma newh_F : forall x, in_hullb HF x = true -> in_hullb HU x = false ->
    (rbs + kFreeArrayOffset + mfa <= x < rbs + kFreeArrayOffset + mfa + Fm) \/ (sh (rbs + kFreeArrayOffset + mfa) <= x < sh (rbs + kFreeArrayOffset + mfa) + Fm / 8).
  Proof.
    intros x X1 X0. rewrite tRBE.
    (first [ pose proof (e_par) as dR_17; dand7 dR_17 as (PU1 & _) _ _ _ _ ((R1 & _) & _) _ | pose proof e_par as ((PU1 & _) & _ & _ & _ & _ & ((R1 & _) & _) & _) ]). (first [ pose proof ((pk_SHG spa m md A n AI NR EMP SHORT CEIL)) as dR_18; dand3 dR_18 as S1 S2 _ | pose proof (pk_SHG spa m md A n AI NR EMP SHORT CEIL) as (S1 & S2 & _) ]).
    destruct (pop_hull_cases A c U Fm 0 W0 CR t_UMS t_FAM x X1) as [OLD|[NU|[NS|[NF|NFS]]]].
    - exfalso. rewrite (in_hullb_mono _ _ x (hull_le_gen 0 0 0 U 0 0 ltac:(lia) ltac:(lia)) ltac:(rewrite hull_000; exact OLD)) in X0. discriminate.
    - exfalso. rewrite (pop_vis_user A c U 0 0 CR ltac:(lia) x ltac:(lia)) in X0. discriminate.
    - exfalso. assert (D0 : 0 <= mu / 8) by (apply Z.div_pos; lia).
      destruct (Z.eq_dec U 0) as [E0|NE0]; [rewrite E0 in NS; change (0 / 8) with 0 in NS; lia|].
      rewrite (pop_vis_ush A c U 0 0 W0 CR t_UMS t_FAM0 ltac:(lia) x ltac:(lia)) in X0. discriminate.
    - left. exact NF.
    - right. exact NFS.
  Qed.

  (* [comment removed for export] *)
  #[using="CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac"] Lemma WF_gen : forall u f, (u = 0 /\ f = 0) \/ (u = U /\ (f = 0 \/ f = Fm)) -> WF (popg A c u f 0).
  Proof.
    intros u f Huf.
    (first [ pose proof (e_par) as dR_19; dand8 dR_19 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (Hu : u = 0 \/ u = U) by (destruct Huf as [[X _]|[X _]]; [left| right]; exact X).
    assert (Hf : f = 0 \/ f = Fm) by (destruct Huf as [[_ X]|[_ X]]; [left; exact X| exact X]).
    assert (UMSx : 0 <= u /\ u mod kUserMapSize = 0 /\ mu + u < au + 9 * size + kUserMapSize /\ au <= size * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c) by (destruct Hu as [->| ->]; [exact t_UMS0| exact t_UMS]).
    assert (FAMx : 0 <= f /\ f mod kFreeArrayMapSize = 0 /\ mfa + f <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + f <= kFreeArraySize) by (destruct Hf as [->| ->]; [exact t_FAM0| exact t_FAM]).
    assert (NCx : 0 <= 0 /\ au + 0 * size <= mu + u /\ 4 * (nf + 0) <= mfa + f) by (destruct UMSx as (U0 & _); destruct FAMx as (F0 & _); lia).
    assert (POSx : mu + u = 0 -> f = 0 /\ 0 = 0).
    { intros Z0. split; [| reflexivity]. destruct Huf as [[_ X]|[X1 X2]]; [exact X|]. subst u. destruct X2 as [X|X]; [exact X|].
      pose proof (pk_POS m md A n AI NR EMP SHORT Z0) as [Y _]. rewrite X. exact Y. }
    exact (pop_WF A c u f 0 W0 CR UMSx FAMx NCx POSx ltac:(destruct Hu as [->| ->]; [exact (t_TAIL0 0 (or_introl eq_refl))| exact (t_TAIL0 U (or_intror eq_refl))])).
  Qed.
  (* [comment removed for export] *)
  #[using="CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac"] Lemma cover_gen : forall u f mdx, (u = 0 /\ f = 0) \/ (u = U /\ (f = 0 \/ f = Fm)) ->
    pop_mod (popg A c u f 0) md mdx ->
    forall (H0x : hull) l0 h0, In (l0, h0) (pa_hull (popg A c u f 0)) ->
      iv_sub H0x l0 h0 \/ iv_sub (pa_lhull (popg A c u f 0)) l0 h0 \/ lazy_free (m_vm_lazy mdx) l0 h0.
  Proof.
    intros u f mdx Huf (_ & LED & _) H0x l0 h0 Hin. right. exact (ahull_cover (popg A c u f 0) mdx (WF_gen u f Huf) LED l0 h0 Hin).
  Qed.
  #[using="CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac"] Lemma room_gen : forall u f, (u = 0 /\ f = 0) \/ (u = U /\ (f = 0 \/ f = Fm)) -> pa_eager A + u + f + hull_bytes (pa_lhull (popg A c u f 0)) + (2^30 + 2^28) <= p_tlim (a_pl A).   (* [comment removed for export] *)
  Proof.
    intros u f Huf. pose proof (WF_gen u f Huf) as WFx.
    (first [ pose proof (e_par) as dR_19; dand8 dR_19 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (Hu : u = 0 \/ u = U) by (destruct Huf as [[X _]|[X _]]; [left| right]; exact X).
    assert (Hf : f = 0 \/ f = Fm) by (destruct Huf as [[_ X]|[_ X]]; [left; exact X| exact X]).
    assert (UMSx : 0 <= u /\ u mod kUserMapSize = 0 /\ mu + u < au + 9 * size + kUserMapSize /\ au <= size * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c) by (destruct Hu as [->| ->]; [exact t_UMS0| exact t_UMS]).
    assert (FAMx : 0 <= f /\ f mod kFreeArrayMapSize = 0 /\ mfa + f <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + f <= kFreeArraySize) by (destruct Hf as [->| ->]; [exact t_FAM0| exact t_FAM]).
    assert (NCx : 0 <= 0 /\ au + 0 * size <= mu + u /\ 4 * (nf + 0) <= mfa + f) by (destruct UMSx as (U0 & _); destruct FAMx as (F0 & _); lia).
    pose proof (wf_budget_room (popg A c u f 0) WFx (ai_extra _ _ _ _ _ _ _ AI)) as ROOM. unfold kBudgetRoom in ROOM. change (p_tlim (a_pl (popg A c u f 0))) with (p_tlim (a_pl A)) in ROOM.
    change (aeager_of (popg A c u f 0)) with (pa_eager (popg A c u f 0)) in ROOM. rewrite (popg_eager A c u f 0 CR UMSx FAMx) in ROOM. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CEIL CE W0 AI PRE key hi lo md"] Lemma shadow_present : forall (H0x H1x : hull) (beg len : Z) (Mk w : mem) (junk0 pad scr : list byte) (ksc : list word) (u f x : Z),
    hull_le (pa_hull A) H0x -> (forall a, hidc H0x a = true -> Mk a = m a) -> CY junk0 pad scr ksc u f x w ->
    kHighMemBeg <= beg /\ beg + len <= 2^47 /\ 0 < len ->
    sh sb <= sh beg /\ sh beg + len / 8 <= sh sb + kSpaceSize / 8 /\ kLowShadowMapBeg <= sh beg /\ sh beg + len / 8 <= kHighMemBeg ->
    (forall z, sh beg <= z < sh beg + len / 8 -> in_hullb H1x z = true) ->
    (forall z, sh beg <= z < sh beg + len / 8 -> in_hullb H0x z = true -> in_hullb (pa_hull A) z = true) ->
    mapped (mrestrict (hidc H1x) (apply_zeros (munrestrict (hidc H0x) Mk w) [(wz beg, wz len)])) (sh beg) (len / 8).
  Proof.
    (intros H0x H1x beg len Mk w junk0 pad scr ksc u f x HLE MSH CYw FEB; (first [ intro dR_42; dand4 dR_42 as G1 G2 G3 G4 | intros (G1 & G2 & G3 & G4) ]); intros VIS1 OLDV i Hi).
    set (z := sh beg + i). assert (Hz : sh beg <= z < sh beg + len / 8) by (unfold z; lia).
    assert (Z64 : 0 <= z < 2^64) by (unfold kLowShadowMapBeg, kHighMemBeg in *; lia).
    assert (GH : m (wz z) <> None).
    { destruct (ai_hidden _ _ _ _ _ _ _ AI) as [HH1 _]. exact (proj1 (HH1 z (prim_shadow_ghost A W0 z ltac:(lia)))). }
    unfold mrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite (VIS1 z Hz). cbn [negb].
    destruct (in_hullb (pa_hull A) z) eqn:VA.
    - (* [comment removed for export] *)
      rewrite (sw_zspec H0x beg len Mk w FEB). unfold in_range. rewrite unsigned_lit by exact Z64.
      replace ((beg <=? z) && (z <? beg + len)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; unfold kHighMemBeg in *; lia).
      unfold munrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite (in_hullb_mono _ _ z HLE VA). cbn [negb].
      apply (cy_NN _ _ _ _ _ _ _ w CYw z); [lia| right; unfold kLowShadowMapBeg in *; lia| lia|].
      unfold aview_of, mrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite VA. exact GH.
    - (* [comment removed for export] *)
      destruct (in_hullb H0x z) eqn:V0; [rewrite (OLDV z Hz V0) in VA; discriminate|].
      rewrite (sw_zspec H0x beg len Mk w FEB). unfold in_range. rewrite unsigned_lit by exact Z64.
      replace ((beg <=? z) && (z <? beg + len)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; unfold kHighMemBeg in *; lia).
      unfold munrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite V0. cbn [negb].
      rewrite (MSH (wz z)); [exact GH|]. unfold hidc. rewrite unsigned_lit by exact Z64. rewrite V0. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mod4096_of : forall x, x mod 262144 = 0 -> x mod 4096 = 0.
  Proof. intros x Hx. apply (mod0_down _ 262144 4096); [exists 64; reflexivity| exact Hx]. Qed.
  #[using="SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac Clg"] Lemma rbs_mod : rbs mod 4096 = 0.
  Proof.
    (first [ pose proof (e_seg) as dR_20; dand11 dR_20 as _ _ _ _ _ _ _ _ _ SBAL _ | pose proof e_seg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SBAL & _) ]).
    rewrite Z.add_mod, SBAL by lia. replace (c * 4294967296) with (c * 1048576 * 4096) by lia. rewrite Z_mod_mult. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CEIL CE PRE key hi lo stkobj canfill n md m spa rac Clg"] Lemma sh_prim_range : forall x l, sb <= x -> x + l <= sb + kSpaceSize -> 0 <= l -> sh sb <= sh x /\ sh x + l / 8 <= sh sb + kSpaceSize / 8.
  Proof.
    intros x l H1 H2 H3. unfold sh, kSpaceSize in *. change (2^37 / 8) with 17179869184.
    pose proof (Z_div_mod_eq_full x 8) as E1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
    pose proof (Z_div_mod_eq_full l 8) as E2. pose proof (Z.mod_pos_bound l 8 ltac:(lia)) as M2.
    pose proof (Z_div_mod_eq_full sb 8) as E3. pose proof (Z.mod_pos_bound sb 8 ltac:(lia)) as M3.
    lia.
  Qed.

  Definition pk_Wg1 : list (Z * Z) := [(rb + mu, rb + mu + U); (sh (rb + mu), sh (rb + mu) + U / 8)].
  Definition pk_Wg2 : list (Z * Z) := [(fa + mfa, fa + mfa + Fm); (sh (fa + mfa), sh (fa + mfa) + Fm / 8)].
  #[using="CEIL CE NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac"] Lemma pk_WG1 : sub_fp pk_Wg1 (Wi U 0 0) /\ disjoint_from pk_Wg1 (sa - 336) 336 /\ disjoint_from pk_Wg1 R 8 /\ disjoint_from pk_Wg1 (thr + 288) 2480 /\
    disjoint_from pk_Wg1 (R + 16) 64 /\ (forall a l, alloc_ceiling <= a -> disjoint_from pk_Wg1 a l).
  Proof.
    (first [ pose proof (e_seg) as dR_21; dand14 dR_21 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof e_seg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    lin_open. unfold pk_Wg1.
    split; [sub_open; (cv 8; cv 9; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. intros a l Hal. dj_tac.
  Qed.
  #[using="CEIL CE NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac"] Lemma pk_WG2 : sub_fp pk_Wg2 (Wi U Fm 0) /\ disjoint_from pk_Wg2 (sa - 336) 336 /\ disjoint_from pk_Wg2 R 8 /\ disjoint_from pk_Wg2 (thr + 288) 2480 /\
    disjoint_from pk_Wg2 (R + 16) 64 /\ (forall a l, alloc_ceiling <= a -> disjoint_from pk_Wg2 a l) /\ disjoint_from pk_Wg2 (sh (rb + mu)) (U / 8).
  Proof.
    (first [ pose proof (e_seg) as dR_22; dand14 dR_22 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof e_seg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    lin_open. unfold pk_Wg2.
    split; [sub_open; (cv 10; cv 11; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. split; [intros a l Hal; dj_tac| dj_tac].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation nmv := (round_up (4 * (nf + N)) kFaMap).
  #[warnings="-notation-for-abbreviation"] Local Notation fev := (rbs + kFreeArrayOffset + mfa).
  #[warnings="-notation-for-abbreviation"] Local Notation FRPc a0h := (pop_frame (wz kk) (wz (E + 16)) (wz (free_array_of sb c)) (wz 2305843009213693952) a0h (wz 0xb1558) (wz R) (wz gfa_popret)).
  #[warnings="-notation-for-abbreviation"] Local Notation FREc scr2 := (efas_frame scr2 (wz N) (wz rbs) (wz (nf + N)) (wz R) (wz pop_efasret)).
  #[warnings="-notation-for-abbreviation"] Local Notation FRM2c scrM := (mapcb_frame scrM (wz (mu + U - au)) (wz R) (wz (nmv - mfa)) fev (nmv - mfa) (wz fev) (wz nmv) (wz efas_mapret)).
  #[warnings="-notation-for-abbreviation"] Local Notation e_D := (pop_D rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key PRE NP EMP SHORT).

  #[using="K1 PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi"] Lemma node2 : forall (junk0 pad scr scr2 scrM : list byte) (ksc : list word) (a0h s6v t0' t1' t2' a6' t3' t4' t5' t6' : word) (Mk w : mem) (mdk : Model),
    mfa < 4 * (nf + N) ->
    (forall a, hidc HU a = true -> Mk a = m a) -> pop_mod AgU md mdk -> MInv HU HLU (pa_eager A + U) mdk ->   (* [comment removed for export] *)
    (forall a, hidc HU a = true -> w a = None) ->
    CY junk0 pad scr ksc U 0 0 w -> RW nf mfa au (mu + U) w -> stk rsegs w lo (uG + -64 + -48 + -128) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) -> rw_cells rsegs w (uG + -64 + -48) (FREc scr2) -> rw_cells rsegs w (uG + -64 + -48 + -128) (FRM2c scrM) ->
    mapped w (rb + mu) U -> bytes_at rsegs w (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    srealizes rsegs
      (mkCfg (MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -48 + -128)) gp tp t0' t1' t2' (wz (nmv - mfa)) (wz 1) (wz fev) (wz (nmv - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                        (wz fev) (wz efas_name) (wz PSC) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3' t4' t5' t6')
                   F (wz mmap_ecall_pc) (wz 222) fc None (munrestrict (hidc HU) Mk w) (seg_rom rsegs)) mdk)
      T1.
  Proof.
    intros junk0 pad scr scr2 scrM ksc a0h s6v t0' t1' t2' a6' t3' t4' t5' t6' Mk w mdk NEEDMAP MSH PM HI CL CYw RWw STw FRP FRE FRM NEWU SHU.
    (first [ pose proof (e_par) as dR_23; dand8 dR_23 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof (e_seg) as dR_24; dand16 dR_24 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof e_seg as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    assert (EF : Fm = nmv - mfa) by (destruct (ar_fam_cases A c) as [[_ X]|[X _]]; [lia| exact X]).
    assert (F0 : 0 < Fm) by ((first [ pose proof ((ar_fam A c W0 CR EMP SHORT)) as dR_25; dand3 dR_25 as _ X _ | pose proof (ar_fam A c W0 CR EMP SHORT) as (_ & X & _) ]); lia).
    pose proof tRBE as RBEq. lin_open.
    assert (FEQ : fev = fa + mfa) by (rewrite RBEq; reflexivity).
    assert (RANGE : a_sb A <= fev /\ fev + (nmv - mfa) <= a_sb A + kSpaceSize + 4096 /\ fev mod 4096 = 0 /\ (nmv - mfa) mod 4096 = 0 /\ 0 < nmv - mfa).
    { rewrite <- EF. split; [unfold kFreeArrayOffset; lia|]. split; [unfold kFreeArrayOffset, kSpaceSize; lia|].
      split; [| split; [apply mod4096_of; exact PF2| exact F0]].
      rewrite Z.add_mod, (mod4096_of mfa R7), Z.add_0_r, Z.mod_mod by lia. rewrite Z.add_mod, rbs_mod by lia. reflexivity. }
    assert (BR : pa_eager A + U + (nmv - mfa) + hull_bytes HLU <= p_tlim (a_pl A)).
    { pose proof (room_gen U 0 (or_intror (conj eq_refl (or_introl eq_refl)))) as X. rewrite <- EF. unfold kFreeArraySize in *. lia. }
    pose proof (hull_le_gen U 0 0 U Fm 0 ltac:(lia) ltac:(lia)) as HLE. pose proof (lhull_le_gen U 0 0 U Fm 0 ltac:(lia) ltac:(lia)) as LHLE.
    assert (FEB : kHighMemBeg <= fev /\ fev + (nmv - mfa) <= 2^47 /\ 0 < nmv - mfa) by (rewrite <- EF; unfold kHighMemBeg, kFreeArrayOffset; lia).
    assert (VISN : forall x, fev <= x < fev + (nmv - mfa) -> in_hullb HF x = true).
    { intros x Hx. rewrite <- EF in Hx. apply (pop_vis_fa A c U Fm 0 CR ltac:(lia)). rewrite FEQ in Hx. lia. }
    eapply (pop_node A m md AI mdk HU HLU (pa_eager A + U) fev (nmv - mfa) AgU eq_refl eq_refl PM HI RANGE BR).
    - (* [comment removed for export] *)
      cbv zeta. intros HI2 PM2 LZ2.
      set (md2 := commit_model (wz 50) (wz fev) (wz (nmv - mfa)) false mdk) in *.
      (* [comment removed for export] *)
      assert (PMF2 : pop_mod AgF md md2).
      { apply (pop_mod_grow AgU AgF md md2 fev (nmv - mfa) eq_refl eq_refl ltac:(lia)); [| exact PM2| exact LZ2].
        intros c' Hc'. cbn [popg set_cache_inited set_reg a_reg a_pl]. unfold reg_upd.
        destruct (Z.eqb_spec c' c) as [->|NE]; cbn [grow rg_mapped_user rg_mapped_fa]; [| split; left; reflexivity].
        split; [left; reflexivity| right]. split; [| clear - EF; lia].
        clear - RBEq. unfold region_beg, a_sb, kRegionSize in *. cbn [a_pl popg set_cache_inited set_reg] in *. lia. }
      (first [ pose proof (CYw) as dR_26; dand4 dR_26 as _ _ MIw _ | pose proof CYw as (_ & _ & MIw & _) ]).
      assert (SHGEO : sh sb <= sh fev /\ sh fev + (nmv - mfa) / 8 <= sh sb + kSpaceSize / 8 /\ kLowShadowMapBeg <= sh fev /\ sh fev + (nmv - mfa) / 8 <= kHighMemBeg).
      { destruct (sh_prim_range fev (nmv - mfa) ltac:(unfold kFreeArrayOffset; lia) ltac:(rewrite <- EF; unfold kFreeArrayOffset, kSpaceSize; lia) ltac:(lia)) as [G1 G2].
        split; [exact G1|]. split; [exact G2|]. rewrite <- EF, FEQ. unfold kLowShadowMapBeg, kHighMemBeg, kFreeArrayOffset in *. lia. }
      pose proof (sw_munch HU HF fev (nmv - mfa) Mk w HLE ltac:(rewrite <- EF; exact newh_F) FEB CL) as MU2.
      pose proof (sw_wmono HU HF fev (nmv - mfa) Mk w HLE FEB CL) as WM2.
      pose proof (sw_mem_inv HU HF fev (nmv - mfa) Mk w ltac:(rewrite <- EF; exact newh_F) FEB (conj (proj1 (proj2 (proj2 SHGEO))) (proj2 (proj2 (proj2 SHGEO)))) MIw) as MI2.
      assert (MSF : mapped (mrestrict (hidc HF) (apply_zeros (munrestrict (hidc HU) Mk w) [(wz fev, wz (nmv - mfa))])) (sh fev) ((nmv - mfa) / 8)).
      { apply (shadow_present HU HF fev (nmv - mfa) Mk w junk0 pad scr ksc U 0 0 (popg_hull_le A c U 0 0 W0 CR t_UMS t_FAM0) MSH CYw FEB SHGEO).
        - intros z Hz. rewrite <- EF, FEQ in Hz. (first [ pose proof ((pk_SHG spa m md A n AI NR EMP SHORT CEIL)) as dR_27; dand5 dR_27 as _ _ S3 S4 _ | pose proof (pk_SHG spa m md A n AI NR EMP SHORT CEIL) as (_ & _ & S3 & S4 & _) ]).
          assert (D0 : 0 <= mfa / 8) by (apply Z.div_pos; lia).
          apply (pop_vis_fsh A c U Fm 0 W0 CR t_UMS t_FAM ltac:(lia)). lia.
        - intros z Hz V0. rewrite <- EF, FEQ in Hz.
          destruct (pop_hull_cases A c U 0 0 W0 CR t_UMS t_FAM0 z V0) as [OLD|[NU|[NS|[NFx|NFSx]]]]; [exact OLD| exfalso; unfold kFreeArrayOffset in *; lia| exfalso; unfold kFreeArrayOffset in *; lia| exfalso; lia| exfalso; change (0 / 8) with 0 in NFSx; lia]. }
      assert (ZNF : mapped (mrestrict (hidc HF) (apply_zeros (munrestrict (hidc HU) Mk w) [(wz fev, wz (nmv - mfa))])) (fa + mfa) Fm).
      { intros i Hi. rewrite <- FEQ. rewrite (sw_zero HU HF fev (nmv - mfa) Mk w FEB VISN (fev + i) ltac:(lia)). discriminate. }
      set (M2 := apply_zeros (munrestrict (hidc HU) Mk w) [(wz fev, wz (nmv - mfa))]) in *.
      set (w2 := mrestrict (hidc HF) M2) in *.
      rewrite <- EF in MU2. rewrite FEQ in MU2. change (munch pk_Wg2 w w2) in MU2.
      (first [ dand7 pk_WG2 as SUB DF DR DL DRW DHI DSH | destruct pk_WG2 as (SUB & DF & DR & DL & DRW & DHI & DSH) ]).
      apply (grant_tail _ _ M2 md2).
      + intros a Ha. unfold M2. rewrite (sw_hidden HU HF fev (nmv - mfa) Mk w HLE FEB VISN a Ha). apply MSH. exact (hidc_grow_le HU HF HLE a Ha).
      + exact PMF2.
      + apply (MInv_hull_mono HU HLU HF HLF (pa_eager A + U + (nmv - mfa)) _ md2 HI2 LHLE (cover_gen U Fm md2 (or_intror (conj eq_refl (or_intror eq_refl))) PMF2 HU)); [lia|].
        destruct PM2 as ((_ & _ & VL & _) & _). rewrite VL. (first [ pose proof ((ai_ledger _ _ _ _ _ _ _ AI)) as dR_29; dand6 dR_29 as _ _ _ _ L5 _ | destruct (ai_ledger _ _ _ _ _ _ _ AI) as (_ & _ & _ & _ & L5 & _) ]). rewrite L5.
        pose proof (room_gen U Fm (or_intror (conj eq_refl (or_intror eq_refl)))) as X. lia.
      + change (aview_of HF M2) with w2.
        eapply evt_mono; [| intros st' PO; exists junk0, pad, scr, ksc; exact PO].
        apply (e_D t0' t1' t2' a6' s6v t3' t4' t5' t6' a0h junk0 pad scr scr2 scrM (rdbytes w2 (sh fev) (Z.to_nat ((nmv - mfa) / 8))) ksc w2 NEEDMAP).
        * exact (cy_step _ _ _ _ U 0 0 U Fm 0 _ w w2 CYw MU2 WM2 MI2 (Wmono U 0 0 U Fm 0 ltac:(lia) ltac:(lia) ltac:(lia)) SUB DF DR DL).
        * exact (rw_step _ _ _ _ _ w w2 RWw MU2 WM2 DRW).
        * apply (stk_transport_disjoint rsegs _ w w2 _ _ STw MU2 WM2). apply DHI. lia.
        * eapply rw_cells_transport; [exact FRP| exact MU2| exact WM2| apply DHI; lia].
        * eapply rw_cells_transport; [exact FRE| exact MU2| exact WM2| apply DHI; lia].
        * eapply rw_cells_transport; [exact FRM| exact MU2| exact WM2| apply DHI; lia].
        * apply (pk_mapped_wm w w2 _ _ WM2); [lia| right; lia| lia| exact NEWU].
        * eapply bytes_at_transport; [exact SHU| exact MU2|]. rewrite repeat_length, Z2Nat.id by lia. exact DSH.
        * assert (K0' : 0 <= (nmv - mfa) / 8) by (apply Z.div_pos; lia).
          apply mapped_CB; [rewrite Z2Nat.id by lia; exact MSF| unfold kLowShadowMapBeg in *; lia| rewrite Z2Nat.id by lia; unfold kHighMemBeg in *; lia].
        * exact ZNF.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation EPp := (ep_post rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A n canfill stkobj lo).
  #[warnings="-notation-for-abbreviation"] Local Notation PM2p := (pm2_post rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A n canfill stkobj lo).
  #[warnings="-notation-for-abbreviation"] Local Notation e_Cfast := (pop_C_fast rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key PRE NP EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation e_Cmap := (pop_C_map rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key PRE NP EMP SHORT).

  #[using="K1 PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi"] Lemma c_stage : forall (Rg : bvmap 5 word) (pc : word) (Mk : mem) (mdk : Model),
    (forall a, hidc HU a = true -> Mk a = m a) -> pop_mod AgU md mdk -> MInv HU HLU (pa_eager A + U) mdk ->   (* [comment removed for export] *)
    evt rsegs (fun st => exists junk0 pad scr ksc a0h, EPp junk0 pad scr ksc a0h st) (MS Rg F pc fc None (aview_of HU Mk) (seg_rom rsegs)) ->
    srealizes rsegs (mkCfg (MS Rg F pc fc None Mk (seg_rom rsegs)) mdk) T1.
  Proof.
    intros Rg pc Mk mdk MSH PM HI EV.
    destruct (Z.leb_spec (4 * (nf + N)) mfa) as [FAST|NEED].
    - (* [comment removed for export] *)
      assert (F0 : Fm = 0) by (destruct (ar_fam_cases A c) as [[X _]|[_ X]]; [exact X| lia]).
      pose proof (grant_tail Rg pc Mk mdk) as GT. rewrite F0, Z.add_0_r in GT. apply GT; [exact MSH| exact PM| exact HI|].
      eapply evt_cut; [exact EV|].
      (intros st; (first [ intro dR_43; dex18 dR_43 as junk0 pad scr ksc a0h t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' w'; dand7 dR_43 as -> CYw RWw STw FRP NEWU SHU | intro dR_43; dand25 dR_43 as junk0 pad scr ksc a0h t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' w' -> CYw RWw STw FRP NEWU SHU | intros (junk0 & pad & scr & ksc & a0h & t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & t3' & t4' & t5' & t6' & w' & -> & CYw & RWw & STw & FRP & NEWU & SHU) ])).
      eapply evt_mono; [exact (e_Cfast t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' a0h junk0 pad scr ksc w' FAST CYw RWw STw FRP NEWU SHU)|].
      intros st' PO. exists junk0, pad, scr, ksc. exact PO.
    - (* [comment removed for export] *)
      (first [ pose proof (PM) as dR_30; dand6 dR_30 as _ _ _ _ _ HH | pose proof PM as (_ & _ & _ & _ & _ & HH) ]).
      eapply (srz_evt_restrict rsegs HU (hull_segsR _) pa_wxR _ (pa_eager A + U) (fun st => exists junk0 pad scr ksc a0h s6v, PM2p junk0 pad scr ksc a0h s6v st) _ mdk _ HI HH).
      { rewrite restrict_MS. eapply evt_cut; [exact EV|].
        (intros st; (first [ intro dR_44; dex18 dR_44 as junk0 pad scr ksc a0h t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' w'; dand7 dR_44 as -> CYw RWw STw FRP NEWU SHU | intro dR_44; dand25 dR_44 as junk0 pad scr ksc a0h t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' w' -> CYw RWw STw FRP NEWU SHU | intros (junk0 & pad & scr & ksc & a0h & t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & t3' & t4' & t5' & t6' & w' & -> & CYw & RWw & STw & FRP & NEWU & SHU) ])).
        eapply evt_mono; [exact (e_Cmap t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' a0h junk0 pad scr ksc w' NEED CYw RWw STw FRP NEWU SHU)|].
        intros st' PO. exists junk0, pad, scr, ksc, a0h, s6'. exact PO. }
      (intros msr' md'; (first [ intro dR_45; dex6 dR_45 as junk0 pad scr ksc a0h s6v; rename dR_45 into Q | intro dR_45; dand7 dR_45 as junk0 pad scr ksc a0h s6v Q | intros (junk0 & pad & scr & ksc & a0h & s6v & Q) ]); intros HI' SB CL).
      (first [ dex11 Q as t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w'; dand9 Q as -> CYw RWw STw FRP FRE FRM NEWU SHU | dand20 Q as t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w' -> CYw RWw STw FRP FRE FRM NEWU SHU | destruct Q as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & scr2 & scrM & w' & -> & CYw & RWw & STw & FRP & FRE & FRM & NEWU & SHU) ]).
      rewrite unrestrict_MSsvc. cbn [ms_mem] in CL |- *.
      exact (node2 junk0 pad scr scr2 scrM ksc a0h s6v t0' t1' t2' a6' t3' t4' t5' t6' Mk w' md' NEED MSH (pop_mod_sbm_any _ md mdk md' PM SB) HI' CL CYw RWw STw FRP FRE FRM NEWU SHU).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation e_B := (pop_B rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key PRE NP EMP SHORT).

  #[using="K1 PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi"] Lemma node1 : forall (junk0 pad scr scrM : list byte) (ksc : list word) (a0h t0' t1' t2' a6' t3' t4' t5' t6' : word) (w : mem) (mdk : Model),
    mu < au + (kk - nf) * size ->
    pop_mod A md mdk -> MInv (pa_hull A) (pa_lhull A) (pa_eager A) mdk ->
    (forall a, hidc (pa_hull A) a = true -> w a = None) ->
    CY junk0 pad scr ksc 0 0 0 w -> RW nf mfa au mu w -> stk rsegs w lo (uG + -64 + -128) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) ->
    rw_cells rsegs w (uG + -64 + -128) (mapcb_frame scrM (wz (rbs + mu)) (wz U) (wz rbs) (rbs + mu) U (wz (C + 2560)) (wz R) (wz pop_mapret)) ->
    srealizes rsegs
      (mkCfg (MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -128)) gp tp t0' t1' t2' (wz U) (wz 1) (wz (rbs + mu)) (wz U) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                        (wz (rbs + mu)) (wz pop_name) (wz PSC) (wz size) (wz 0xb1558) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3' t4' t5' t6')
                   F (wz mmap_ecall_pc) (wz 222) fc None (munrestrict (hidc (pa_hull A)) m w) (seg_rom rsegs)) mdk)
      T1.
  Proof.
    intros junk0 pad scr scrM ksc a0h t0' t1' t2' a6' t3' t4' t5' t6' w mdk NOFIT PM HI CL CYw RWw STw FRP FRM.
    (first [ pose proof (e_par) as dR_32; dand8 dR_32 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof (e_seg) as dR_33; dand16 dR_33 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof e_seg as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    assert (U0 : 0 < U) by lia.
    (first [ pose proof ((ar_ums A c W0 CR EMP SHORT)) as dR_34; dand5 dR_34 as _ _ _ _ U21 | pose proof (ar_ums A c W0 CR EMP SHORT) as (_ & _ & _ & _ & U21) ]).
    pose proof tRBE as RBEq. lin_open.
    assert (BEQ : rbs + mu = rb + mu) by (rewrite RBEq; reflexivity).
    assert (RANGE : a_sb A <= rbs + mu /\ rbs + mu + U <= a_sb A + kSpaceSize + 4096 /\ (rbs + mu) mod 4096 = 0 /\ U mod 4096 = 0 /\ 0 < U).
    { split; [lia|]. split; [unfold kSpaceSize; lia|]. split; [| split; [apply mod4096_of; tauto| exact U0]].
      rewrite Z.add_mod, rbs_mod, (mod4096_of mu R4) by lia. reflexivity. }
    assert (BR : pa_eager A + U + hull_bytes (pa_lhull A) <= p_tlim (a_pl A)).
    { pose proof (room_gen 0 0 (or_introl (conj eq_refl eq_refl))) as X. rewrite lhull_000 in X. lia. }
    pose proof (popg_hull_le A c U 0 0 W0 CR t_UMS t_FAM0) as HLE. pose proof (popg_lhull_le A c U 0 0 W0 CR t_UMS t_FAM0) as LHLE.
    assert (FEB : kHighMemBeg <= rbs + mu /\ rbs + mu + U <= 2^47 /\ 0 < U) by (unfold kHighMemBeg; lia).
    assert (VISN : forall x, rbs + mu <= x < rbs + mu + U -> in_hullb HU x = true).
    { intros x Hx. apply (pop_vis_user A c U 0 0 CR ltac:(lia)). rewrite BEQ in Hx. lia. }
    eapply (pop_node A m md AI mdk (pa_hull A) (pa_lhull A) (pa_eager A) (rbs + mu) U A eq_refl eq_refl PM HI RANGE BR).
    - (* [comment removed for export] *)
      cbv zeta. intros HI2 PM2 LZ2.
      set (md2 := commit_model (wz 50) (wz (rbs + mu)) (wz U) false mdk) in *.
      (* [comment removed for export] *)
      assert (PMU2 : pop_mod AgU md md2).
      { apply (pop_mod_grow A AgU md md2 (rbs + mu) U eq_refl eq_refl ltac:(lia)); [| exact PM2| exact LZ2].
        intros c' Hc'. cbn [popg set_cache_inited set_reg a_reg a_pl]. unfold reg_upd.
        destruct (Z.eqb_spec c' c) as [->|NE]; cbn [grow rg_mapped_user rg_mapped_fa]; [| split; left; reflexivity].
        split; [right| left; clear; lia]. split; [| clear; lia].
        clear - RBEq. unfold region_beg, a_sb, kRegionSize in *. lia. }
      (first [ pose proof (CYw) as dR_35; dand4 dR_35 as _ _ MIw _ | pose proof CYw as (_ & _ & MIw & _) ]).
      assert (SHGEO : sh sb <= sh (rbs + mu) /\ sh (rbs + mu) + U / 8 <= sh sb + kSpaceSize / 8 /\ kLowShadowMapBeg <= sh (rbs + mu) /\ sh (rbs + mu) + U / 8 <= kHighMemBeg).
      { destruct (sh_prim_range (rbs + mu) U ltac:(lia) ltac:(unfold kSpaceSize; lia) ltac:(lia)) as [G1 G2].
        split; [exact G1|]. split; [exact G2|]. rewrite BEQ. unfold kLowShadowMapBeg, kHighMemBeg in *. lia. }
      pose proof (sw_munch (pa_hull A) HU (rbs + mu) U m w HLE newh_U FEB CL) as MU2.
      pose proof (sw_wmono (pa_hull A) HU (rbs + mu) U m w HLE FEB CL) as WM2.
      pose proof (sw_mem_inv (pa_hull A) HU (rbs + mu) U m w newh_U FEB (conj (proj1 (proj2 (proj2 SHGEO))) (proj2 (proj2 (proj2 SHGEO)))) MIw) as MI2.
      assert (MSF : mapped (mrestrict (hidc HU) (apply_zeros (munrestrict (hidc (pa_hull A)) m w) [(wz (rbs + mu), wz U)])) (sh (rbs + mu)) (U / 8)).
      { apply (shadow_present (pa_hull A) HU (rbs + mu) U m w junk0 pad scr ksc 0 0 0 (hull_le_refl _) (fun a _ => eq_refl) CYw FEB SHGEO).
        - intros z Hz. rewrite BEQ in Hz. (first [ pose proof ((pk_SHG spa m md A n AI NR EMP SHORT CEIL)) as dR_36; dand3 dR_36 as S1 S2 _ | pose proof (pk_SHG spa m md A n AI NR EMP SHORT CEIL) as (S1 & S2 & _) ]).
          assert (D0 : 0 <= mu / 8) by (apply Z.div_pos; lia).
          apply (pop_vis_ush A c U 0 0 W0 CR t_UMS t_FAM0 ltac:(lia)). lia.
        - intros z Hz V0. exact V0. }
      assert (ZNU : mapped (mrestrict (hidc HU) (apply_zeros (munrestrict (hidc (pa_hull A)) m w) [(wz (rbs + mu), wz U)])) (rb + mu) U).
      { intros i Hi. rewrite <- BEQ. rewrite (sw_zero (pa_hull A) HU (rbs + mu) U m w FEB VISN (rbs + mu + i) ltac:(lia)). discriminate. }
      set (M2 := apply_zeros (munrestrict (hidc (pa_hull A)) m w) [(wz (rbs + mu), wz U)]) in *.
      set (w2 := mrestrict (hidc HU) M2) in *.
      rewrite BEQ in MU2. change (munch pk_Wg1 w w2) in MU2.
      (first [ dand6 pk_WG1 as SUB DF DR DL DRW DHI | destruct pk_WG1 as (SUB & DF & DR & DL & DRW & DHI) ]).
      apply (c_stage _ _ M2 md2).
      + intros a Ha. unfold M2. exact (sw_hidden (pa_hull A) HU (rbs + mu) U m w HLE FEB VISN a Ha).
      + exact PMU2.
      + apply (MInv_hull_mono (pa_hull A) (pa_lhull A) HU HLU (pa_eager A + U) _ md2 HI2 LHLE (cover_gen U 0 md2 (or_intror (conj eq_refl (or_introl eq_refl))) PMU2 (pa_hull A))); [lia|].
        destruct PM2 as ((_ & _ & VL & _) & _). rewrite VL. (first [ pose proof ((ai_ledger _ _ _ _ _ _ _ AI)) as dR_38; dand6 dR_38 as _ _ _ _ L5 _ | destruct (ai_ledger _ _ _ _ _ _ _ AI) as (_ & _ & _ & _ & L5 & _) ]). rewrite L5.
        pose proof (room_gen U 0 (or_intror (conj eq_refl (or_introl eq_refl)))) as X. lia.
      + change (aview_of HU M2) with w2.
        eapply evt_mono; [| intros st' PO; exists junk0, pad, scr, ksc, a0h; exact PO].
        apply (e_B t0' t1' t2' a6' t3' t4' t5' t6' a0h junk0 pad scr scrM (rdbytes w2 (sh (rbs + mu)) (Z.to_nat (U / 8))) ksc w2 NOFIT).
        * exact (cy_step _ _ _ _ 0 0 0 U 0 0 _ w w2 CYw MU2 WM2 MI2 (Wmono 0 0 0 U 0 0 ltac:(lia) ltac:(lia) ltac:(lia)) SUB DF DR DL).
        * exact (rw_step _ _ _ _ _ w w2 RWw MU2 WM2 DRW).
        * apply (stk_transport_disjoint rsegs _ w w2 _ _ STw MU2 WM2). apply DHI. lia.
        * eapply rw_cells_transport; [exact FRP| exact MU2| exact WM2| apply DHI; lia].
        * eapply rw_cells_transport; [exact FRM| exact MU2| exact WM2| apply DHI; lia].
        * assert (K0' : 0 <= U / 8) by (apply Z.div_pos; lia).
          apply mapped_CB; [rewrite Z2Nat.id by lia; exact MSF| unfold kLowShadowMapBeg in *; lia| rewrite Z2Nat.id by lia; unfold kHighMemBeg in *; lia].
        * exact ZNU.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pop_shape : TSet := T1.

  #[warnings="-notation-for-abbreviation"] Local Notation HPp := (hp_post rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A n canfill stkobj lo).
  #[warnings="-notation-for-abbreviation"] Local Notation PM1p := (pm1_post rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A n canfill stkobj lo).
  #[warnings="-notation-for-abbreviation"] Local Notation e_head := (pop_head rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key PRE NP EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation e_Afit := (pop_A_fit rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key PRE NP EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation e_Amap := (pop_A_map rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill stkobj lo hi key PRE NP EMP SHORT).

  #[using="K1 PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo Clg"] Theorem pop_core_gen : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
    srealizes rsegs
      (mkCfg (MS (mkR rac spa gp tp t0 t1 t2 s0 s1 (wz 0xb1558) (wz n) (wz 8) (wz stkobj) (wz 1) (wz canfill) a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3707c) fc None m (seg_rom rsegs)) md)
      pop_shape.
  Proof.
    intros t0 t1 t2 a6 a7 t3 t4 t5 t6. unfold pop_shape.
    destruct (asI_minv A m md AI) as [HMI HH]. pose proof (pop_mod_entry A m md AI) as PM0.
    destruct (Z.leb_spec (au + (kk - nf) * size) mu) as [FIT|NOFIT].
    - (* [comment removed for export] *)
      assert (U0 : U = 0) by (destruct (ar_ums_cases A c) as [[X _]|[_ X]]; [exact X| lia]).
      pose proof c_stage as CS. rewrite U0 in CS. rewrite hull_000 in CS. rewrite lhull_000 in CS. rewrite popg_zero in CS.   (* [comment removed for export] *)
      eapply (CS _ _ m md (fun a _ => eq_refl) PM0 ltac:(rewrite Z.add_0_r; exact HMI)).
      eapply evt_cut; [exact (e_head t0 t1 t2 a6 a7 t3 t4 t5 t6)|].
      (intros st; (first [ intro dR_46; dex16 dR_46 as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w; dand4 dR_46 as -> CYw RWw STw | intro dR_46; dand20 dR_46 as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w -> CYw RWw STw | intros (t0' & t1' & t2' & a0' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk0 & pad & scr & ksc & w & -> & CYw & RWw & STw) ])).
      eapply evt_mono; [exact (e_Afit t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w FIT CYw RWw STw)|].
      intros st' PO. exists junk0, pad, scr, ksc, a0'. exact PO.
    - (* [comment removed for export] *)
      eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR _) pa_wxR _ (pa_eager A)
                (fun st => exists junk0 pad scr ksc a0h, PM1p junk0 pad scr ksc a0h st) _ md _ HMI HH).
      { rewrite restrict_MS. eapply evt_cut; [exact (e_head t0 t1 t2 a6 a7 t3 t4 t5 t6)|].
        (intros st; (first [ intro dR_47; dex16 dR_47 as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w; dand4 dR_47 as -> CYw RWw STw | intro dR_47; dand20 dR_47 as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w -> CYw RWw STw | intros (t0' & t1' & t2' & a0' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk0 & pad & scr & ksc & w & -> & CYw & RWw & STw) ])).
        eapply evt_mono; [exact (e_Amap t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w NOFIT CYw RWw STw)|].
        intros st' PO. exists junk0, pad, scr, ksc, a0'. exact PO. }
      (intros msr' md'; (first [ intro dR_48; dex5 dR_48 as junk0 pad scr ksc a0h; rename dR_48 into Q | intro dR_48; dand6 dR_48 as junk0 pad scr ksc a0h Q | intros (junk0 & pad & scr & ksc & a0h & Q) ]); intros HI' SB CL).
      (first [ dex10 Q as t0' t1' t2' a6' t3' t4' t5' t6' scrM w'; dand6 Q as -> CYw RWw STw FRP FRM | dand16 Q as t0' t1' t2' a6' t3' t4' t5' t6' scrM w' -> CYw RWw STw FRP FRM | destruct Q as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & scrM & w' & -> & CYw & RWw & STw & FRP & FRM) ]).
      rewrite unrestrict_MSsvc. cbn [ms_mem] in CL |- *.
      exact (node1 junk0 pad scr scrM ksc a0h t0' t1' t2' a6' t3' t4' t5' t6' w' md' NOFIT (pop_mod_sbm A m md AI md md' PM0 SB) HI' CL CYw RWw STw FRP FRM).
  Qed.
End Arm.
