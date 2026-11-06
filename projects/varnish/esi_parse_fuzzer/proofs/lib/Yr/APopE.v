(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMTac AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalmys AMaldga AMalrrv ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_3ti ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_png AMalnrk ARtSscs ARtSoqz ANodeA6 APopSA APopSB APopSC APopSD.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalnrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSD.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
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
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@Q2; @Q5; @B5; @B3; @B1; @L1; @Q4; @CE; @B2; @T4; @R1; @H5; @SEP_ts; @H3; @CSR; @T1; @SEP_tr; @LJ; @B4; @T2; @Q6; @Q7; @Q10; @Hi; @Q1; @R6; @PU; @Hal; @Ha; @H1; @PN; @NEEDMAP; @LOSA; @U1; @F1; @Hx; @X; @Q9; @PF; @SPR; @Hb; @CAP0; @P1; @P3; @P2; @Q3; @LK5; @FAST; @HI47; @SOLO; @LO; @LK; @H; @RBEq; @CEIL; @H2; @CLO; @SOHI; @LKS; @CR; @MR; @NOFIT; @R10; @R8; @OLD; @NP; @NRQ; @SAHI; @NR; @R9; @FIT; @U0; @Hj; @KS; @MXR; @PU4; @NEW; @EF])).
Ltac hot_lia_full := tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).
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



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hp_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
      st = MS (mkR (wz refill_ret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) a0' (wz (C + 2560)) (wz c) (wz (E + 16)) (wz kk) a5' a6' a7'
                   (wz 8) (wz 2305843009213693952) (wz (free_array_of sb c)) (wz 1099511627776) (wz 1152921504607895551)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3' t4' t5' t6')
               F (wz gfa_locked) fc None w (seg_rom rsegs)
      /\ CY junk0 pad scr ksc 0 0 0 w /\ RW nf mfa au mu w /\ stk rsegs w lo uG.

  #[using="KS PREF MIv CEIL CR NR AI SHORT EMP NP PRE key hi md"] Lemma pop_head : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
    evt rsegs hp_post
        (MS (mkR rac spa gp tp t0 t1 t2 s0 s1 (wz 0xb1d58) (wz n) (wz 8) (wz stkobj) (wz 1) (wz canfill) a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3719c) fc None v (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a6 a7 t3 t4 t5 t6.
    destruct PREF as (CF & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SOLO & SOHI).
    pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    (first [ pose proof ((hit_class n NR)) as dR_1; dand3 dR_1 as _ HC _ | pose proof (hit_class n NR) as (_ & HC & _) ]).
    (first [ pose proof ((ar_k A c CR)) as dR_2; dand4 dR_2 as MK2 KR2 _ MR | pose proof (ar_k A c CR) as (MK2 & KR2 & _ & MR) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_3; dand6 dR_3 as TH1 TH2 THRA CT1 CT2 _ | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & _) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_4; dand4 dR_4 as SEP_thr SEP_ctx SEP_tc _ | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & _) ]).
    (first [ pose proof ((ref_sep A m md n AI)) as dR_5; dand4 dR_5 as SEP_tr SEP_rs SEP_cri _ | pose proof (ref_sep A m md n AI) as (SEP_tr & SEP_rs & SEP_cri & _) ]).
    (first [ pose proof ((ref_ri A m md n AI)) as dR_6; dand7 dR_6 as RIE RIL RIH RIAL SBAL _ _ | pose proof (ref_ri A m md n AI) as (RIE & RIL & RIH & RIAL & SBAL & _ & _) ]).
    pose proof (pk_region A m md n AI NR) as (MX & _).
    (first [ pose proof (LIN) as dR_7; dand6 dR_7 as L1 L2 (T1 & T2 & T3 & T4) (B1 & B2 & B3 & B4 & B5) (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) (H1 & H2 & H3 & H4 & H5) | pose proof LIN as (L1 & L2 & (T1 & T2 & T3 & T4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)) ]).
    assert (LO : alloc_ceiling <= lo /\ lo <= sa - 1024) by lia.
    assert (SPR' : sa + 65536 < 2^64) by lia.
    assert (NR64 : 1 <= n <= 64512) by (clear - NR; unfold kMaxPrimaryUser in NR; lia).
    assert (SOA : sa <= stkobj /\ stkobj + 2064 <= 2^47) by lia.
    assert (TSDL : 0x5e8328 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    assert (TPL : bv_unsigned tp = 0x5e83d8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    assert (SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling) by (unfold kHighMemBeg; lia).
    (* [comment removed for export] *)
    assert (HSUB : forall LW, (LW = [] \/ (a_cache_inited A = false /\ LW = [(C + 80, C + 2560)])) ->
              sub_fp ([(sa - 1024, sa); (R, R + 8)] ++ LW) (Wi 0 0 0) /\ disjoint_from ([(sa - 1024, sa); (R, R + 8)] ++ LW) (R + 16) 64).
    { intros LW [->|[CI ->]]; unfold sub_fp, pk_Wi, pop_Wi; cbn [app outside disjoint_from]; rewrite ?CI; unfold apart in SEP_tr; (split; [intros x Hx; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; first [ solve [clear - Hx; lia] | lia ] | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; first [ solve [clear - RIH SEP_tr; lia] | lia ]]). }   (* [comment removed for export] *)
    destruct (a_cache_inited A) eqn:CI.
    - (* [comment removed for export] *)
      (first [ pose proof ((ref_PC A m md n AI NR CI EMP)) as dR_8; dex1 dR_8 as ks; destruct dR_8 as [LKS PC] | pose proof ((ref_PC A m md n AI NR CI EMP)) as dR_8; dand3 dR_8 as ks LKS PC | destruct (ref_PC A m md n AI NR CI EMP) as (ks & LKS & PC) ]).
      pose proof (alloc_head_ok rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v
                    lo n stkobj canfill pa_tsd ctx thr c (max_count c) sb ri ks
                    MIv ST LO SPA SPR' NR64 CF SOA rzlog_ok get_thread_ok classid_blk_ok
                    (hit_INI A m md AI) (hit_RSS A m md AI) (hit_RZm A m md AI) (hit_MUM A m md AI) (hit_SBc A m md AI) (ref_CRI A m md n AI NR)
                    (hit_TC A m md AI) (hit_TH0 A m md AI) (hit_CT8 A m md AI) (conj TH1 TH2) THRA (conj CT1 CT2) TSDL TPL SBR SEP_thr SEP_ctx SEP_tc
                    HC PC LKS MR (conj RIL RIH) RIAL SBAL SEP_tr SEP_rs SEP_cri MX) as EV.
      eapply evt_mono; [exact EV|]. intros st PO. unfold alloc_head_post in PO. cbv zeta in PO. rewrite KS in PO.
      (first [ dex15 PO as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr w; dand11 PO as -> MU WM MI' ST' FA FC FR FG MX' _ | dand26 PO as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr w -> MU WM MI' ST' FA FC FR FG MX' _ | destruct PO as (t0' & t1' & t2' & a0' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk0 & pad & scr & w & -> & MU & WM & MI' & ST' & FA & FC & FR & FG & MX' & _) ]).
      destruct (HSUB [] (or_introl eq_refl)) as (HS1 & HS2).
      first [ hotw_ex16 t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ks w | exists t0', t1', t2', a0', a5', a6', a7', t3', t4', t5', t6', junk0, pad, scr, ks, w ]. split; [reflexivity|].
      split; [| split; [exact (rw_step _ _ _ _ _ v w (regw_entry m md A n AI NR) MU WM HS2)| exact ST']].
      unfold carry. split; [exact (munch_weaken _ _ _ _ HS1 MU)|]. split; [exact WM|]. split; [exact MI'|].
      split; [exact FA|]. split; [exact FC|]. split; [exact FR|]. split; [exact FG|]. split; [exact MX'|]. split; [exact LKS|].
      split; [| intros X; rewrite CI in X; discriminate X].
      eapply rw_cells_transport; [exact PC| exact MU| exact WM|]. cbn [app disjoint_from cells_size csize Nat.add]. unfold apart in SEP_tr. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.
    - (* [comment removed for export] *)
      pose proof (alloc_head0_ok rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v
                    lo n stkobj canfill pa_tsd ctx thr c sb ri (fun _ => 0) (fun _ => 0) (fun _ => 0) (pk_ks0 A m)
                    MIv ST LO SPA SPR' NR64 CF SOA rzlog_ok get_thread_ok classid_blk_ok
                    (hit_INI A m md AI) (hit_RSS A m md AI) (hit_RZm A m md AI) (hit_MUM A m md AI) (hit_SBc A m md AI) (ref_CRI A m md n AI NR)
                    (hit_TC A m md AI) (hit_TH0 A m md AI) (hit_CT8 A m md AI) (conj TH1 TH2) THRA (conj CT1 CT2) TSDL TPL SBR SEP_thr SEP_ctx SEP_tc
                    HC) as EV.
      cbv zeta in EV.
      specialize (EV ltac:(intros i Hi; destruct (pk_lines0 A m md AI CI i Hi) as (LK & RWi); cbv beta; split; [lia|]; split; [lia|]; split; [lia|]; split; [exact LK| exact RWi]) eq_refl eq_refl
                     (conj RIL RIH) RIAL SBAL SEP_tr SEP_rs SEP_cri MX).
      eapply evt_mono; [exact EV|]. intros st PO. unfold alloc_head_post in PO. cbv zeta in PO. rewrite KS in PO.
      (first [ dex15 PO as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr w; dand11 PO as -> MU WM MI' ST' FA FC FR FG MX' LP | dand26 PO as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr w -> MU WM MI' ST' FA FC FR FG MX' LP | destruct PO as (t0' & t1' & t2' & a0' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk0 & pad & scr & w & -> & MU & WM & MI' & ST' & FA & FC & FR & FG & MX' & LP) ]).
      destruct (HSUB [(C + 80, C + 2560)] (or_intror (conj eq_refl eq_refl))) as (HS1 & HS2).
      first [ hotw_ex16 t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr (pk_ks0 A m c) w | exists t0', t1', t2', a0', a5', a6', a7', t3', t4', t5', t6', junk0, pad, scr, (pk_ks0 A m c), w ]. split; [reflexivity|].
      split; [| split; [exact (rw_step _ _ _ _ _ v w (regw_entry m md A n AI NR) MU WM HS2)| exact ST']].
      unfold carry. split; [exact (munch_weaken _ _ _ _ HS1 MU)|]. split; [exact WM|]. split; [exact MI'|].
      split; [exact FA|]. split; [exact FC|]. split; [exact FR|]. split; [exact FG|]. split; [exact MX'|].
      split; [exact (proj1 (pk_lines0 A m md AI CI c ltac:(lia)))|].
      split; [exact (LP c ltac:(lia))|].
      intros _ i Hi NE. exists (pk_ks0 A m i). split; [exact (proj1 (pk_lines0 A m md AI CI i Hi))| exact (LP i Hi)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac lin_open :=
    let L := fresh "L" in pose proof LIN as L;
    destruct L as (L1 & L2 & (T1 & T2 & T3 & T4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)).
  Tactic Notation "cv" constr(k) := split; [right; (let kn := lazymatch type of k with Z => eval cbv in (Z.to_nat k) | _ => k end in inside_at kn); lia|].
  Ltac sub_open := apply sub_fp_all_inside; unfold pk_Wi, pop_Wi, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [app]; destruct (a_cache_inited A); (lazymatch goal with |- all_inside ?W' _ => let WW := fresh "WW" in set (WW := W') end); cbn [all_inside app].
  Ltac dj_tac := unfold pk_Wi, pop_Wi, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [disjoint_from app]; try (destruct (a_cache_inited A));
                 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; lia.

  (* [comment removed for export] *)
  #[using="PREF CEIL CE NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac Clg"] Lemma pk_stackW : forall a b ums fam nc, sa - 1024 <= a -> b <= uG ->
    sub_fp [(a, b)] (Wi ums fam nc) /\ disjoint_from [(a, b)] (sa - 336) 336 /\ disjoint_from [(a, b)] R 8 /\
    disjoint_from [(a, b)] (thr + 288) 2480 /\ disjoint_from [(a, b)] (R + 16) 64.
  Proof. intros a b ums fam nc Ha Hb. lin_open. split; [sub_open; (cv 0; exact I)|]. split; [dj_tac|]. split; [dj_tac|]. split; dj_tac. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation FRPc a0h := (pop_frame (wz kk) (wz (E + 16)) (wz (free_array_of sb c)) (wz 2305843009213693952) a0h (wz 0xb1d58) (wz R) (wz gfa_popret)).

  Definition pm1_post (junk0 pad scr : list byte) (ksc : list word) (a0h : word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scrM : list byte) (w' : mem),
      st = MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -128)) gp tp t0' t1' t2' (wz U) (wz 1) (wz (rbs + mu)) (wz U) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz (rbs + mu)) (wz pop_name) (wz PSC) (wz size) (wz 0xb1d58) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None w' (seg_rom rsegs)
      /\ CY junk0 pad scr ksc 0 0 0 w' /\ RW nf mfa au mu w' /\ stk rsegs w' lo (uG + -64 + -128)
      /\ rw_cells rsegs w' (uG + -64) (FRPc a0h)
      /\ rw_cells rsegs w' (uG + -64 + -128) (mapcb_frame scrM (wz (rbs + mu)) (wz U) (wz rbs) (rbs + mu) U (wz (C + 2560)) (wz R) (wz pop_mapret)).

  (* [comment removed for export] *)
  #[using="PREF CEIL CR NR AI SHORT EMP NP PRE key hi stkobj canfill md m rac"] Lemma seg_pre :
    (alloc_ceiling <= lo /\ lo <= sa - 1024) /\ sa mod 16 = 0 /\ sa <= 2^47 /\
    (2 <= max_count c <= 16 /\ max_count c = 2 * kk) /\ (aobj thr 4096 /\ thr + 4096 <= alloc_ceiling) /\ thr mod 16 = 0 /\
    (kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling) /\ ri mod 128 = 0 /\ (kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling) /\ sb mod 4096 = 0 /\
    (thr + 4096 <= ri \/ ri + 4096 <= thr) /\ (ri + 4096 <= sb \/ sb + 2^37 <= ri) /\ (thr + 4096 <= sb \/ sb + 2^37 <= thr) /\
    0 <= nf < kk /\ bv_unsigned tp = 0x5e83d8 /\ (0x5e8328 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000).
  Proof.
    destruct PREF as (CF & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SOLO & SOHI).
    (first [ pose proof ((ar_k A c CR)) as dR_11; dand4 dR_11 as MK2 KR2 _ MR | pose proof (ar_k A c CR) as (MK2 & KR2 & _ & MR) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_12; dand4 dR_12 as TH1 TH2 THRA _ | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & _) ]).
    pose proof (hit_sep A m md AI) as (SEP_thr & _).
    (first [ pose proof ((ref_sep A m md n AI)) as dR_13; dand3 dR_13 as SEP_tr SEP_rs _ | pose proof (ref_sep A m md n AI) as (SEP_tr & SEP_rs & _) ]).
    (first [ pose proof ((ref_ri A m md n AI)) as dR_14; dand7 dR_14 as RIE RIL RIH RIAL SBAL _ _ | pose proof (ref_ri A m md n AI) as (RIE & RIL & RIH & RIAL & SBAL & _ & _) ]).
    lin_open. unfold apart in *. unfold kHighMemBeg.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try lia.
    - cbn [cl_tp LPA]. rewrite unsigned_lit by lia. reflexivity.
    - unfold pa_tsd. lia.
    - unfold pa_tsd. lia.
  Qed.

  #[using="KS PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi md"] Lemma pop_A_map : forall (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
    mu < au + (kk - nf) * size ->
    CY junk0 pad scr ksc 0 0 0 w -> RW nf mfa au mu w -> stk rsegs w lo uG ->
    evt rsegs (pm1_post junk0 pad scr ksc a0)
        (MS (mkR (wz refill_ret) (wz uG) gp tp t0 t1 t2 (wz R) (wz 0xb1d58) a0 (wz (C + 2560)) (wz c) (wz (E + 16)) (wz kk) a5 a6 a7
                 (wz 8) (wz 2305843009213693952) (wz (free_array_of sb c)) (wz 1099511627776) (wz 1152921504607895551)
                 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3 t4 t5 t6)
            F (wz gfa_locked) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 junk0 pad scr ksc w NOFIT CYw RWw STw.
    (first [ pose proof (seg_pre) as dR_15; dand16 dR_15 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof ((ar_reg A c W0 CR)) as dR_16; dand10 dR_16 as (R1 & R2) R3 R4 R5 R6 R7 R8 R9 R10 R11 | pose proof (ar_reg A c W0 CR) as ((R1 & R2) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) ]). (* [comment removed for export] *)
    assert (CAP0 : mu <= 3682891136 /\ au <= 3615782272 /\ mfa <= 469762048).
    { pose proof (ar_csr c CR) as CSR0. pose proof (Z.div_le_compat_l au 32 size ltac:(hot_lia_full) ltac:(hot_lia_full)) as Q1. pose proof (Z.mul_div_le au 32 ltac:(hot_lia_full)) as Q2.
      clear - R1 R2 R9 R10 CSR0 Q1 Q2. unfold kAuCap, kMaxSize in *. hot_lia_full. }
    assert (EU : U = round_up (au + (kk - nf) * size - mu) kUserMap) by (destruct (ar_ums_cases A c) as [[_ X]|[X _]]; [lia| exact X]).
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw (Wle 0 0 0 ltac:(pose proof (pk_UMS m md A n AI NR EMP SHORT); lia) ltac:(pose proof (pk_FAM m md A n AI NR EMP SHORT); lia) ltac:(pose proof (pk_NC m md A n AI NR EMP SHORT); lia)))) as dR_17; dand8 dR_17 as PCo TC CSB CREL CPMH CCF2 CCF144 MRN | pose proof (cy_statics _ _ _ _ _ _ _ w CYw (Wle 0 0 0 ltac:(pose proof (pk_UMS m md A n AI NR EMP SHORT); lia) ltac:(pose proof (pk_FAM m md A n AI NR EMP SHORT); lia) ltac:(pose proof (pk_NC m md A n AI NR EMP SHORT); lia)))
      as (PCo & TC & CSB & CREL & CPMH & CCF2 & CCF144 & MRN) ]).
    (first [ dand13 PCo as _ CCF1 _ _ _ _ _ _ _ _ _ CPSC1 CPSC2 | destruct PCo as (_ & CCF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CPSC1 & CPSC2) ]).
    (first [ pose proof (CYw) as dR_19; dand4 dR_19 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ dand7 RWw as RNF RMFA RAU R40 RMU RMM REX | destruct RWw as (RNF & RMFA & RAU & R40 & RMU & RMM & REX) ]).
    pose proof (pop_sA_map gp tp t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 F fc w (wz 8) (wz thr) (wz 1) sa lo thr c (max_count c) sb ri nf au mu) as EV.
    unfold pop_sA_map_post in EV. cbv zeta in EV. rewrite !KS in EV. rewrite <- !EU in EV.
    specialize (EV MIw STw LO SPH CR MXR THR RIR SBR SBAL NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(lia)
                   CSB CREL CPMH CPSC1 CPSC2 CCF1 CCF2 RNF RAU RMU RMM NOFIT).
    eapply evt_mono; [exact EV|]. (intros st; (first [ intro dR_87; dex10 dR_87 as t0' t1' t2' a6' t3' t4' t5' t6' scrM w'; dand7 dR_87 as -> MU WM MI' ST' FRP FRM | intro dR_87; dand17 dR_87 as t0' t1' t2' a6' t3' t4' t5' t6' scrM w' -> MU WM MI' ST' FRP FRM | intros (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & scrM & w' & -> & MU & WM & MI' & ST' & FRP & FRM) ])).
    (first [ pose proof ((pk_stackW (uG - 464) uG 0 0 0 ltac:(lia) ltac:(lia))) as dR_21; dand5 dR_21 as S1 S2 S3 S4 S5 | destruct (pk_stackW (uG - 464) uG 0 0 0 ltac:(lia) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5) ]).
    first [ hotw_ex10 t0' t1' t2' a6' t3' t4' t5' t6' scrM w' | exists t0', t1', t2', a6', t3', t4', t5', t6', scrM, w' ]. split; [reflexivity|].
    split; [exact (cy_step _ _ _ _ _ _ _ _ _ _ _ w w' CYw MU WM MI' (fun x H => H) S1 S2 S3 S4)|].
    split; [exact (rw_step _ _ _ _ _ w w' (conj RNF (conj RMFA (conj RAU (conj R40 (conj RMU (conj RMM REX)))))) MU WM S5)|].
    split; [exact ST'|]. split; [exact FRP| exact FRM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m spa rac Clg"] Lemma par_facts :
    (0 <= U /\ U mod 262144 = 0 /\ mu + U <= 3750000000) /\ au + (kk - nf) * size <= mu + U /\ mu + U - au < 9 * size + 262144 /\
    (0 <= N /\ au + N * size <= mu + U /\ kk - nf <= N /\ N < 9 + 8192) /\
    (0 <= Fm /\ Fm mod 262144 = 0 /\ mfa + Fm <= 536870912 /\ 4 * (nf + N) <= mfa + Fm) /\
    ((0 <= au <= mu /\ mu mod 262144 = 0 /\ au mod size = 0) /\ 0 <= mfa <= 469762048 /\ mfa mod 262144 = 0 /\ 4 * nf <= mfa /\ au <= 3615782272 /\ mu <= 3682891136) /\
    32 <= size <= 65536 /\ (mu + U) mod 262144 = 0.   (* [comment removed for export] *)
  Proof.
    (first [ pose proof ((ar_ums A c W0 CR EMP SHORT)) as dR_22; dand4 dR_22 as (U1 & U2 & U3) U4 U5 _ | pose proof (ar_ums A c W0 CR EMP SHORT) as ((U1 & U2 & U3) & U4 & U5 & _) ]). (first [ pose proof ((ar_nc A c W0 CR EMP SHORT)) as dR_23; dand5 dR_23 as N1 N2 _ N4 N5 | pose proof (ar_nc A c W0 CR EMP SHORT) as (N1 & N2 & _ & N4 & N5) ]).
    pose proof (ar_fam A c W0 CR EMP SHORT) as ((F1 & F2 & F3 & F3') & F4 & _).
    (first [ pose proof ((ar_reg A c W0 CR)) as dR_25; dand10 dR_25 as (R1 & R2) R3 R4 R5 R6 R7 R8 R9 R10 R11 | pose proof (ar_reg A c W0 CR) as ((R1 & R2) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) ]). pose proof (ar_cap A c W0 CR EMP SHORT) as CAP0.
    pose proof (ar_csr c CR) as CSR. unfold kUserMapSize, kFreeArrayMapSize, kFreeArraySize, kAuCap in *. change (2^18) with 262144 in *.
    assert (Q1 : au / size <= au / 32) by (apply Z.div_le_compat_l; hot_lia_full). assert (Q2 : 32 * (au / 32) <= au) by (apply Z.mul_div_le; hot_lia_full).
    assert (MUM : (mu + U) mod 262144 = 0) by (rewrite Z.add_mod, R4, U2 by lia; reflexivity).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try hot_lia_full.   (* [comment removed for export] *)
  Qed.
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac Clg"] Lemma Wle000 : sub_fp (Wi 0 0 0) (Wi U Fm N). Proof. (first [ pose proof (par_facts) as dR_26; dand6 dR_26 as (P1 & _) _ _ (P2 & _) (P3 & _) _ | pose proof par_facts as ((P1 & _) & _ & _ & (P2 & _) & (P3 & _) & _) ]). apply Wle; lia. Qed.
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac Clg"] Lemma WleU00 : sub_fp (Wi U 0 0) (Wi U Fm N). Proof. (first [ pose proof (par_facts) as dR_27; dand6 dR_27 as (P1 & _) _ _ (P2 & _) (P3 & _) _ | pose proof par_facts as ((P1 & _) & _ & _ & (P2 & _) & (P3 & _) & _) ]). apply Wle; lia. Qed.
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac Clg"] Lemma WleU0N : sub_fp (Wi U 0 N) (Wi U Fm N). Proof. (first [ pose proof (par_facts) as dR_28; dand6 dR_28 as (P1 & _) _ _ (P2 & _) (P3 & _) _ | pose proof par_facts as ((P1 & _) & _ & _ & (P2 & _) & (P3 & _) & _) ]). apply Wle; lia. Qed.
  #[using="CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac Clg"] Lemma WleUF0 : sub_fp (Wi U Fm 0) (Wi U Fm N). Proof. (first [ pose proof (par_facts) as dR_29; dand6 dR_29 as (P1 & _) _ _ (P2 & _) (P3 & _) _ | pose proof par_facts as ((P1 & _) & _ & _ & (P2 & _) & (P3 & _) & _) ]). apply Wle; lia. Qed.
  #[using="spa rac"] Lemma FAE : free_array_of sb c = fa. Proof. unfold free_array_of, region_beg, kRegionSize, kFreeArrayOffset. lia. Qed.
  #[using="spa rac"] Lemma RBE : rbs = rb. Proof. unfold region_beg, kRegionSize. lia. Qed.

  (* [comment removed for export] *)
  Definition ep_post (junk0 pad scr : list byte) (ksc : list word) (a0h : word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word) (w' : mem),
      st = MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0' t1' t2' (wz R) (wz (nf + N)) (wz 0xb1d58) (wz R) (wz rbs) (wz (nf + N)) a4' a5' a6' a7'
                   (wz rbs) (wz N) (wz (mu + U - au)) (wz size) s6' (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3' t4' t5' t6')
              F (wz efas_entry) fc None w' (seg_rom rsegs)
      /\ CY junk0 pad scr ksc U 0 0 w' /\ RW nf mfa au (mu + U) w' /\ stk rsegs w' lo (uG - 64)
      /\ rw_cells rsegs w' (uG + -64) (FRPc a0h)
      /\ mapped w' (rb + mu) U /\ bytes_at rsegs w' (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))).

  #[using="KS PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi md"] Lemma pop_A_fit : forall (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
    au + (kk - nf) * size <= mu ->
    CY junk0 pad scr ksc 0 0 0 w -> RW nf mfa au mu w -> stk rsegs w lo uG ->
    evt rsegs (ep_post junk0 pad scr ksc a0)
        (MS (mkR (wz refill_ret) (wz uG) gp tp t0 t1 t2 (wz R) (wz 0xb1d58) a0 (wz (C + 2560)) (wz c) (wz (E + 16)) (wz kk) a5 a6 a7
                 (wz 8) (wz 2305843009213693952) (wz (free_array_of sb c)) (wz 1099511627776) (wz 1152921504607895551)
                 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3 t4 t5 t6)
            F (wz gfa_locked) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 junk0 pad scr ksc w FIT CYw RWw STw.
    (first [ pose proof (seg_pre) as dR_30; dand16 dR_30 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_31; dand8 dR_31 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (U0 : U = 0) by (destruct (ar_ums_cases A c) as [[X _]|[_ X]]; [exact X| lia]).
    assert (EN : (mu - au) / size = N) by (unfold pop_nc; rewrite U0, Z.add_0_r; reflexivity).
    assert (EM : mu - au = mu + U - au) by lia.
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw Wle000)) as dR_32; dand4 dR_32 as PCo TC CSB _ | pose proof (cy_statics _ _ _ _ _ _ _ w CYw Wle000) as (PCo & TC & CSB & _) ]).
    (first [ pose proof (CYw) as dR_33; dand4 dR_33 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_34; dand7 dR_34 as RNF RMFA RAU R40 RMU RMM REX | pose proof RWw as (RNF & RMFA & RAU & R40 & RMU & RMM & REX) ]).
    pose proof (pop_sA_fit gp tp t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 F fc w (wz 8) (wz thr) (wz 1) sa lo thr c (max_count c) sb ri nf au mu) as EV.
    unfold pop_sA_fit_post in EV. cbv zeta in EV. rewrite !KS in EV. rewrite !EN in EV. rewrite EM in EV.
    specialize (EV MIw STw LO SPH CR MXR THR RIR SBR NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(lia) CSB RNF RAU RMU FIT).
    eapply evt_mono; [exact EV|]. (intros st; (first [ intro dR_88; dex3 dR_88 as a5' a6' w'; dand6 dR_88 as -> MU WM MI' ST' FRP | intro dR_88; dand9 dR_88 as a5' a6' w' -> MU WM MI' ST' FRP | intros (a5' & a6' & w' & -> & MU & WM & MI' & ST' & FRP) ])).
    (first [ pose proof ((pk_stackW (uG - 64) uG U 0 0 ltac:(lia) ltac:(lia))) as dR_35; dand5 dR_35 as S1 S2 S3 S4 S5 | destruct (pk_stackW (uG - 64) uG U 0 0 ltac:(lia) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5) ]).
    lin_open.
    first [ hotw_ex13 t0 t1 t2 (wz (kk - nf)) a5' a6' a7 (wz kk) t3 t4 t5 t6 w' | exists t0, t1, t2, (wz (kk - nf)), a5', a6', a7, (wz kk), t3, t4, t5, t6, w' ]. split; [reflexivity|].
    split; [exact (cy_step _ _ _ _ _ _ _ _ _ _ _ w w' CYw MU WM MI' (Wmono 0 0 0 U 0 0 ltac:(lia) ltac:(lia) ltac:(lia)) S1 S2 S3 S4)|].
    split; [rewrite U0, Z.add_0_r; exact (rw_step _ _ _ _ _ w w' RWw MU WM S5)|].
    split; [exact ST'|]. split; [exact FRP|].
    rewrite U0. split; [intros i Hi; lia|]. change (0 / 8) with 0. apply bytes_at_nil. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pk_Wb : list (Z * Z) :=
    [(uG - 192, uG - 64); (sh (rbs + mu), sh (rbs + mu) + U / 8); (thr + off_th_stats + 72, thr + off_th_stats + 88);
     (C + 2560 + 24, C + 2560 + 32); (R + 48, R + 56)].
  #[using="PREF CEIL CE CR NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac Clg"] Lemma pk_WB : sub_fp pk_Wb (Wi U 0 0) /\ disjoint_from pk_Wb (sa - 336) 336 /\ disjoint_from pk_Wb R 8 /\ disjoint_from pk_Wb (thr + 288) 2480 /\
    (forall a l, (R + 8 <= a /\ a + l <= R + 48) \/ (R + 56 <= a /\ a + l <= R + 128) -> disjoint_from pk_Wb a l).
  Proof.
    (first [ pose proof (seg_pre) as dR_36; dand14 dR_36 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof seg_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    lin_open. unfold pk_Wb. rewrite RBE.
    split; [sub_open; (cv 0; cv 9; cv 6; cv 6; cv 3; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. intros a l Hal. dj_tac.
  Qed.

  #[using="KS PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi md"] Lemma pop_B : forall (t0 t1 t2 a6 t3 t4 t5 t6 a0h : word) (junk0 pad scr scrM old : list byte) (ksc : list word) (w : mem),
    mu < au + (kk - nf) * size ->
    CY junk0 pad scr ksc U 0 0 w -> RW nf mfa au mu w -> stk rsegs w lo (uG + -64 + -128) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) ->
    rw_cells rsegs w (uG + -64 + -128) (mapcb_frame scrM (wz (rbs + mu)) (wz U) (wz rbs) (rbs + mu) U (wz (C + 2560)) (wz R) (wz pop_mapret)) ->
    rw_cells rsegs w (sh (rbs + mu)) [CB (Z.to_nat (U / 8)) old] -> mapped w (rb + mu) U ->
    evt rsegs (ep_post junk0 pad scr ksc a0h)
        (MS (mkR (wz mapfixed_resume) (wz (uG + -64 + -128)) gp tp t0 t1 t2 (wz U) (wz 1) (wz (rbs + mu)) (wz U) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                 (wz (rbs + mu)) (wz pop_name) (wz PSC) (wz size) (wz 0xb1d58) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3 t4 t5 t6)
            F (wz mmap_after_pc) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a6 t3 t4 t5 t6 a0h junk0 pad scr scrM old ksc w NOFIT CYw RWw STw FRP FRM SHB NEWU.
    (first [ pose proof (seg_pre) as dR_37; dand16 dR_37 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_38; dand8 dR_38 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (EU : U = round_up (au + (kk - nf) * size - mu) kUserMap) by (destruct (ar_ums_cases A c) as [[_ X]|[X _]]; [lia| exact X]).
    assert (EN : (mu + U - au) / size = N) by reflexivity.
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw WleU00)) as dR_39; dand8 dR_39 as PCo TC CSB CREL CPMH CCF2 CCF144 MRN | pose proof (cy_statics _ _ _ _ _ _ _ w CYw WleU00) as (PCo & TC & CSB & CREL & CPMH & CCF2 & CCF144 & MRN) ]).
    (first [ pose proof ((cy_tst _ _ _ _ _ _ _ w CYw)) as dR_40; dex2 dR_40 as mm72 mm80; rename dR_40 into TST | pose proof ((cy_tst _ _ _ _ _ _ _ w CYw)) as dR_40; dand3 dR_40 as mm72 mm80 TST | destruct (cy_tst _ _ _ _ _ _ _ w CYw) as (mm72 & mm80 & TST) ]). destruct (cy_stm _ _ _ _ _ _ _ w CYw) as (statm & STM).
    (first [ pose proof (CYw) as dR_41; dand4 dR_41 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_42; dand7 dR_42 as RNF RMFA RAU R40 RMU RMM REX | pose proof RWw as (RNF & RMFA & RAU & R40 & RMU & RMM & REX) ]).
    pose proof (pop_sB gp tp t0 t1 t2 a6 t3 t4 t5 t6 a0h F fc w (wz thr) (wz 1) sa lo thr c (max_count c) sb ri nf au mu pa_tsd ctx scrM old mm72 mm80 statm) as EV.
    unfold pop_sB_post in EV. cbv zeta in EV. rewrite !KS in EV. rewrite <- !EU in EV. rewrite !EN in EV.
    specialize (EV poison_ok thread_stats_ok MIw STw LO SPA SPH CR MXR THR THRA RIR SBR SBAL SEP_tr NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) NOFIT ltac:(lia)
                   TPL TSDL PCo TC CCF144 RNF RAU RMU FRP FRM SHB TST STM).
    eapply evt_mono; [exact EV|].
    (intros st; (first [ intro dR_89; dex13 dR_89 as t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' statm' w'; dand12 dR_89 as -> MU WM MI' ST' FRP' RNF' RAU' RMU' SHU' TST' STM' | intro dR_89; dand25 dR_89 as t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' statm' w' -> MU WM MI' ST' FRP' RNF' RAU' RMU' SHU' TST' STM' | intros (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statm' & w' & -> & MU & WM & MI' & ST' & FRP' & RNF' & RAU' & RMU' & SHU' & TST' & STM') ])).
    lin_open. pose proof RBE as RBEq.
    fold pk_Wb in MU. (first [ dand5 pk_WB as SUB DF DR DL DW | destruct pk_WB as (SUB & DF & DR & DL & DW) ]).
    first [ hotw_ex13 t0' t1' t2' a4' a5' a6' a7' (wz 0xb1d58) t3' t4' t5' t6' w' | exists t0', t1', t2', a4', a5', a6', a7', (wz 0xb1d58), t3', t4', t5', t6', w' ]. split; [reflexivity|].
    split; [exact (cy_step _ _ _ _ _ _ _ _ _ _ _ w w' CYw MU WM MI' (fun x H => H) SUB DF DR DL)|].
    split.
    { unfold regw. split; [exact RNF'|].
      split; [eapply rw_cells_transport; [exact RMFA| exact MU| exact WM| apply DW; cbn; lia]|].
      split; [exact RAU'|].
      split; [eapply rw_cells_transport; [exact R40| exact MU| exact WM| apply DW; cbn; lia]|].
      split; [exact RMU'|].
      split; [eapply rw_cells_transport; [exact RMM| exact MU| exact WM| apply DW; cbn; lia]|].
      eapply rw_cells_transport; [exact REX| exact MU| exact WM| apply DW; cbn; lia]. }
    split; [exact ST'|]. split; [exact FRP'|].
    split; [apply (pk_mapped_wm w w' _ _ WM); [lia| right; lia| lia| exact NEWU]|].
    rewrite <- RBEq. exact SHU'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition gpk (junk0 pad scr : list byte) (ksc : list word) (na : word) (v5 : mem) : Prop :=
    munch (pop_W (sa - 1024) sa thr E R fa nf N rb mu U mfa Fm (a_cache_inited A)) v v5 /\
    (forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> v5 (wz a) <> None) /\
    stk rsegs v5 lo (sa + -128 + -48 + -32 - 128) /\ mem_inv rsegs v5 /\ length ksc = 16%nat /\
    rw_cells rsegs v5 R [C8 (wz kMutexWriter)] /\ rw_cells rsegs v5 (R + 16) [C8 (wz (nf + N))] /\ rw_cells rsegs v5 (R + 24) [C8 (wz (mfa + Fm))] /\
    rw_cells rsegs v5 (R + 32) [C8 (wz (au + N * size))] /\ rw_cells rsegs v5 (R + 48) [C8 (wz (mu + U))] /\ rw_cells rsegs v5 (R + 68) [C1 (Z_to_bv 8 0)] /\
    rw_cells rsegs v5 (R + 72) [C8 na] /\
    u32arr rsegs v5 (fa + 4 * nf) (map (fun k => wz (k * size / kCompactPtrScale)) (newfree (au / size) N)) /\
    mapped v5 (rb + mu) U /\ mapped v5 (fa + mfa) Fm /\
    bytes_at rsegs v5 (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) /\
    bytes_at rsegs v5 (sh (fa + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (Fm / 8))) /\
    rw_cells rsegs v5 E [C4 (wz 0); C4 (wz (max_count c)); C8 (wz size); CB 64 (u32s ksc)] /\
    (a_cache_inited A = false -> forall i, 1 <= i <= 31 -> i <> c ->
       exists ks, length ks = 16%nat /\ rw_cells rsegs v5 (thr + 208 + 80 * i) [C4 (wz 0); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s ks)]) /\
    rw_cells rsegs v5 (sa + -128) (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0) /\
    rw_cells rsegs v5 (sa + -128 + -48) (comb_frameR n) /\
    rw_cells rsegs v5 (sa + -128 + -48 + -32) (refill_frame pad (wz E) (wz c) (wz comb_refill_ret)) /\
    rw_cells rsegs v5 (sa + -128 + -48 + -32 + -128) (gfa_frameR scr thr stkobj n (thr + 208) kk E) /\
    ro_cells rsegs v5 stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))] /\
    bytes_at rsegs v5 (stkobj + 16) (u64s (map (Z_to_bv 64) key)).

  Definition gp_post (junk0 pad scr : list byte) (ksc : list word) : machine_state -> Prop := fun st =>
    exists (tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na : word) (v5 : mem),
      st = MS (mkR (wz gfa_popret) (wz uG) gp tp tq0 tq1 tq2 (wz R) (wz 0xb1d58) (wz 1) aq1 aq2 aq3 aq4 aq5 aq6 aq7
                   a0g (wz 2305843009213693952) (wz (free_array_of sb c)) (wz (E + 16)) (wz kk)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) tq3 tq4 tq5 tq6)
              F (wz gfa_popret) fc None v5 (seg_rom rsegs)
      /\ gpk junk0 pad scr ksc na v5.

  (* [comment removed for export] *)
  #[using="PREF CEIL CR W0 NR AI SHORT EMP NP PRE hi md"] Lemma gpk_intro : forall (junk0 pad scr : list byte) (ksc : list word) (u f x : Z) (v5 : mem),
    CY junk0 pad scr ksc u f x v5 -> sub_fp (Wi u f x) (Wi U Fm N) -> stk rsegs v5 lo uG ->
    rw_cells rsegs v5 (R + 16) [C8 (wz (nf + N))] -> rw_cells rsegs v5 (R + 24) [C8 (wz (mfa + Fm))] ->
    rw_cells rsegs v5 (R + 32) [C8 (wz (au + N * size)); C8 (wz 0); C8 (wz (mu + U)); C8 (wz 0)] -> rw_cells rsegs v5 (R + 68) [C1 (Z_to_bv 8 0)] ->
    u32arr rsegs v5 (free_array_of sb c + 4 * nf) (ARtSb8o.carved au size N) ->
    mapped v5 (rb + mu) U -> mapped v5 (fa + mfa) Fm ->
    bytes_at rsegs v5 (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    bytes_at rsegs v5 (sh (fa + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (Fm / 8))) ->
    exists na, gpk junk0 pad scr ksc na v5.
  Proof.
    intros junk0 pad scr ksc u f x v5 CY5 LE ST5 PNF PMFA RAU4 PEX PFA PNU PNF' PSU PSF.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SOLO & _ & TRC & TRB & _). cbn [cl_segs LPA] in TRC, TRB.
    destruct (cy_na _ _ _ _ _ _ _ v5 CY5) as (na & PNA). exists na.
    (first [ pose proof (par_facts) as dR_44; dand8 dR_44 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof (CY5) as dR_45; dand11 dR_45 as MU5 WM5 MI5 FA5 FC5 FR5 FG5 MX5 LK5 LN5 LNS5 | pose proof CY5 as (MU5 & WM5 & MI5 & FA5 & FC5 & FR5 & FG5 & MX5 & LK5 & LN5 & LNS5) ]).
    change [C8 (wz (au + N * size)); C8 (wz 0); C8 (wz (mu + U)); C8 (wz 0)] with ([C8 (wz (au + N * size))] ++ [C8 (wz 0)] ++ [C8 (wz (mu + U))] ++ [C8 (wz 0)]) in RAU4.
    apply rw_cells_app_iff in RAU4. destruct RAU4 as [PAU RAU4]. apply rw_cells_app_iff in RAU4. destruct RAU4 as [_ RAU4]. apply rw_cells_app_iff in RAU4. destruct RAU4 as [PMU _].
    cbn [cells_size csize Nat.add] in PMU. replace (R + 32 + Z.of_nat 8 + Z.of_nat 8) with (R + 48) in PMU by lia.
    unfold gpk.
    split; [exact (munch_weaken _ _ _ _ (pop_Wi_sub_W _ _ _ _ _ _ _ _ _ _ _ _ _ _) (munch_weaken _ _ _ _ LE MU5))|].
    split; [exact (cy_NN _ _ _ _ _ _ _ v5 CY5)|].
    split; [exact ST5|]. split; [exact MI5|]. split; [exact LK5|]. split; [exact MX5|]. split; [exact PNF|]. split; [exact PMFA|].
    split; [exact PAU|]. split; [exact PMU|]. split; [exact PEX|]. split; [exact PNA|].
    split; [rewrite <- FAE, <- (carved_newfree au size N ltac:(lia) R5); exact PFA|].
    split; [exact PNU|]. split; [exact PNF'|]. split; [exact PSU|]. split; [exact PSF|]. split; [exact LN5|]. split; [exact LNS5|].
    split; [exact FA5|]. split; [exact FC5|]. split; [exact FR5|]. split; [exact FG5|].
    split; [exact (cy_ro_hi _ _ _ _ _ _ _ v5 CY5 LE _ _ TRC SOLO)| exact (cy_bytes_hi _ _ _ _ _ _ _ v5 CY5 LE _ _ TRB ltac:(lia))].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pk_Wc : list (Z * Z) :=
    [(uG - 112, uG); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69); (free_array_of sb c + 4 * nf, free_array_of sb c + 4 * nf + 4 * N)].
  #[using="PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac Clg"] Lemma pk_WC : sub_fp pk_Wc (Wi U 0 N) /\ disjoint_from pk_Wc (sa - 336) 336 /\ disjoint_from pk_Wc R 8 /\ disjoint_from pk_Wc (thr + 288) 2480 /\
    disjoint_from pk_Wc (sh (rb + mu)) (U / 8).
  Proof.
    (first [ pose proof (seg_pre) as dR_46; dand14 dR_46 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof seg_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    (first [ pose proof (par_facts) as dR_47; dand6 dR_47 as PU PU4 PU5 PN PF _ | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & _) ]).
    lin_open. unfold pk_Wc.
    split; [sub_open; (cv 0; cv 2; cv 2; cv 4; cv 5; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. dj_tac.
  Qed.

  #[using="spa rac"] Lemma merge_RAU4 : forall (w : mem) auv muv, RW nf mfa auv muv w -> rw_cells rsegs w (R + 32) [C8 (wz auv); C8 (wz 0); C8 (wz muv); C8 (wz 0)].
  Proof.
    (intros w auv muv; (first [ intro dR_90; dand7 dR_90 as _ _ RAU R40 RMU RMM _ | intros (_ & _ & RAU & R40 & RMU & RMM & _) ])).
    change [C8 (wz auv); C8 (wz 0); C8 (wz muv); C8 (wz 0)] with ([C8 (wz auv)] ++ [C8 (wz 0)] ++ [C8 (wz muv)] ++ [C8 (wz 0)]).
    apply rw_cells_app_iff. split; [exact RAU|]. cbn [cells_size csize Nat.add]. replace (R + 32 + Z.of_nat 8) with (R + 40) by lia.
    apply rw_cells_app_iff. split; [exact R40|]. cbn [cells_size csize Nat.add]. replace (R + 40 + Z.of_nat 8) with (R + 48) by lia.
    apply rw_cells_app_iff. split; [exact RMU|]. cbn [cells_size csize Nat.add]. replace (R + 48 + Z.of_nat 8) with (R + 56) by lia. exact RMM.
  Qed.

  (* [comment removed for export] *)
  #[using="CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo md"] Lemma faj_old : forall (junk0 pad scr : list byte) (ksc : list word) (u f x : Z) (w : mem), CY junk0 pad scr ksc u f x w -> 4 * (nf + N) <= mfa ->
    exists junk, length junk = Z.to_nat N /\ u32arr rsegs w (free_array_of sb c + 4 * nf) junk.
  Proof.
    intros junk0 pad scr ksc u f x w CYw FAST. (first [ pose proof (par_facts) as dR_48; dand5 dR_48 as _ _ _ (N0 & _) _ | pose proof par_facts as (_ & _ & _ & (N0 & _) & _) ]). lin_open.
    (first [ pose proof ((pk_region A m md n AI NR)) as dR_49; dand11 dR_49 as _ _ _ _ _ _ _ _ _ MFA _ | pose proof (pk_region A m md n AI NR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MFA & _) ]).
    apply mapped_u32arr; [| rewrite FAE; unfold kFreeArrayOffset; lia| rewrite FAE; unfold kFreeArrayOffset; lia].
    rewrite FAE. apply (cy_mapped _ _ _ _ _ _ _ w CYw); [| unfold kFreeArrayOffset; lia| right; unfold kFreeArrayOffset; lia| unfold kFreeArrayOffset; lia].
    intros i Hi. replace (fa + 4 * nf + i) with (fa + (4 * nf + i)) by lia. apply MFA. lia.
  Qed.

  #[using="KS PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE hi md"] Lemma pop_C_fast : forall (t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
    4 * (nf + N) <= mfa ->
    CY junk0 pad scr ksc U 0 0 w -> RW nf mfa au (mu + U) w -> stk rsegs w lo (uG - 64) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) ->
    mapped w (rb + mu) U -> bytes_at rsegs w (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    evt rsegs (gp_post junk0 pad scr ksc)
        (MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + N)) (wz 0xb1d58) (wz R) (wz rbs) (wz (nf + N)) a4 a5 a6 a7
                 (wz rbs) (wz N) (wz (mu + U - au)) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3 t4 t5 t6)
            F (wz efas_entry) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h junk0 pad scr ksc w FAST CYw RWw STw FRP NEWU SHU.
    (first [ pose proof (seg_pre) as dR_50; dand16 dR_50 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_51; dand8 dR_51 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (F0 : Fm = 0) by (destruct (ar_fam_cases A c) as [[X _]|[_ X]]; [exact X| lia]).
    (first [ pose proof ((faj_old _ _ _ _ _ _ _ w CYw FAST)) as dR_52; dex1 dR_52 as junk; destruct dR_52 as [LJ FAJ] | pose proof ((faj_old _ _ _ _ _ _ _ w CYw FAST)) as dR_52; dand3 dR_52 as junk LJ FAJ | destruct (faj_old _ _ _ _ _ _ _ w CYw FAST) as (junk & LJ & FAJ) ]).
    (first [ pose proof (CYw) as dR_53; dand4 dR_53 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_54; dand7 dR_54 as RNF RMFA _ _ _ _ REX | pose proof RWw as (RNF & RMFA & _ & _ & _ & _ & REX) ]).
    pose proof (pop_sC_fast gp tp t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h F fc w (wz thr) (wz 1) sa lo thr c (max_count c) sb ri nf au (mu + U) mfa junk) as EV.
    unfold pop_grow_post in EV. cbv zeta in EV. rewrite !KS in EV. change ((mu + U - au) / size) with N in EV.
    change (pop_sC_W sa c sb ri nf au (mu + U)) with pk_Wc in EV.
    replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) in EV by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
    specialize (EV MIw STw LO SPA SPH CR MXR THR RIR SBR SBAL SEP_rs NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(lia)
                   ltac:(unfold kFreeArrayMapSize; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) LJ RNF RMFA (merge_RAU4 w _ _ RWw) (ex_intro (fun ex => rw_cells rsegs w (R + 68) [C1 ex]) _ REX) FRP FAJ FAST).
    eapply evt_mono; [exact EV|].
    (intros st; (first [ intro dR_91; dex15 dR_91 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w'; dand11 dR_91 as -> MU WM MI' ST' RNF' RMFA' RAU4' REX' FA' _ | intro dR_91; dand26 dR_91 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w' -> MU WM MI' ST' RNF' RMFA' RAU4' REX' FA' _ | intros (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & w' & -> & MU & WM & MI' & ST' & RNF' & RMFA' & RAU4' & REX' & FA' & _) ])).
    (first [ dand5 pk_WC as SUB DF DR DL DS | destruct pk_WC as (SUB & DF & DR & DL & DS) ]). lin_open.
    pose proof (cy_step _ _ _ _ U 0 0 U 0 N _ w w' CYw MU WM MI' (Wmono U 0 0 U 0 N ltac:(lia) ltac:(lia) ltac:(lia)) SUB DF DR DL) as CY'.
    destruct (gpk_intro junk0 pad scr ksc U 0 N w' CY' WleU0N ST' RNF' ltac:(rewrite F0, Z.add_0_r; exact RMFA') RAU4' REX' FA') as (na & GP).
    - apply (pk_mapped_wm w w' _ _ WM); [lia| right; lia| lia| exact NEWU].
    - rewrite F0. intros i Hi. lia.
    - eapply bytes_at_transport; [exact SHU| exact MU|]. rewrite repeat_length, Z2Nat.id by lia. exact DS.
    - rewrite F0. change (0 / 8) with 0. apply bytes_at_nil. lia.
    - exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', a0h, na, w'. split; [reflexivity| exact GP].
  Qed.

  #[warnings="-notation-for-abbreviation"] Local Notation nmv := (round_up (4 * (nf + N)) kFaMap).
  #[warnings="-notation-for-abbreviation"] Local Notation fev := (rbs + kFreeArrayOffset + mfa).
  #[warnings="-notation-for-abbreviation"] Local Notation FREc scr2 := (efas_frame scr2 (wz N) (wz rbs) (wz (nf + N)) (wz R) (wz pop_efasret)).
  #[warnings="-notation-for-abbreviation"] Local Notation FRM2c scrM := (mapcb_frame scrM (wz (mu + U - au)) (wz R) (wz (nmv - mfa)) fev (nmv - mfa) (wz fev) (wz nmv) (wz efas_mapret)).

  Definition pm2_post (junk0 pad scr : list byte) (ksc : list word) (a0h s6v : word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr2 scrM : list byte) (w' : mem),
      st = MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -48 + -128)) gp tp t0' t1' t2' (wz (nmv - mfa)) (wz 1) (wz fev) (wz (nmv - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz fev) (wz efas_name) (wz PSC) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None w' (seg_rom rsegs)
      /\ CY junk0 pad scr ksc U 0 0 w' /\ RW nf mfa au (mu + U) w' /\ stk rsegs w' lo (uG + -64 + -48 + -128)
      /\ rw_cells rsegs w' (uG + -64) (FRPc a0h) /\ rw_cells rsegs w' (uG + -64 + -48) (FREc scr2) /\ rw_cells rsegs w' (uG + -64 + -48 + -128) (FRM2c scrM)
      /\ mapped w' (rb + mu) U /\ bytes_at rsegs w' (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))).


  #[using="KS PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi md"] Lemma pop_C_map : forall (t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
    mfa < 4 * (nf + N) ->
    CY junk0 pad scr ksc U 0 0 w -> RW nf mfa au (mu + U) w -> stk rsegs w lo (uG - 64) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) ->
    mapped w (rb + mu) U -> bytes_at rsegs w (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    evt rsegs (pm2_post junk0 pad scr ksc a0h s6v)
        (MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + N)) (wz 0xb1d58) (wz R) (wz rbs) (wz (nf + N)) a4 a5 a6 a7
                 (wz rbs) (wz N) (wz (mu + U - au)) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3 t4 t5 t6)
            F (wz efas_entry) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h junk0 pad scr ksc w NEEDMAP CYw RWw STw FRP NEWU SHU.
    (first [ pose proof (seg_pre) as dR_56; dand16 dR_56 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_57; dand8 dR_57 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw WleU00)) as dR_58; dand8 dR_58 as PCo TC CSB CREL CPMH CCF2 CCF144 MRN | pose proof (cy_statics _ _ _ _ _ _ _ w CYw WleU00) as (PCo & TC & CSB & CREL & CPMH & CCF2 & CCF144 & MRN) ]).
    (first [ dand13 PCo as _ CCF1 _ _ _ _ _ _ _ _ _ CPSC1 CPSC2 | destruct PCo as (_ & CCF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CPSC1 & CPSC2) ]).
    (first [ pose proof (CYw) as dR_60; dand4 dR_60 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_61; dand3 dR_61 as RNF RMFA _ | pose proof RWw as (RNF & RMFA & _) ]).
    pose proof (pop_sC_map gp tp t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 F fc w (wz thr) (wz 1) sa lo thr c (max_count c) sb ri nf au (mu + U) mfa (repeat (wz 0) (Z.to_nat N))) as EV.
    unfold pop_sC_map_post in EV. cbv zeta in EV. rewrite ?KS in EV. change ((mu + U - au) / size) with N in EV.
    specialize (EV MIw STw LO SPH CR MXR THR RIR SBR SBAL NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia)
                   ltac:(unfold kFreeArrayMapSize; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(apply repeat_length) CPMH CPSC1 CPSC2 CCF1 CCF2 RMFA NEEDMAP).
    eapply evt_mono; [exact EV|].
    (intros st; (first [ intro dR_92; dex11 dR_92 as t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w'; dand7 dR_92 as -> MU WM MI' ST' FRE FRM | intro dR_92; dand18 dR_92 as t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w' -> MU WM MI' ST' FRE FRM | intros (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & scr2 & scrM & w' & -> & MU & WM & MI' & ST' & FRE & FRM) ])).
    (first [ pose proof ((pk_stackW (uG - 512) (uG + -64) U 0 0 ltac:(lia) ltac:(lia))) as dR_62; dand5 dR_62 as S1 S2 S3 S4 S5 | destruct (pk_stackW (uG - 512) (uG + -64) U 0 0 ltac:(lia) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5) ]). lin_open.
    first [ hotw_ex11 t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w' | exists t0', t1', t2', a6', t3', t4', t5', t6', scr2, scrM, w' ]. split; [reflexivity|].
    split; [exact (cy_step _ _ _ _ _ _ _ _ _ _ _ w w' CYw MU WM MI' (fun x H => H) S1 S2 S3 S4)|].
    split; [exact (rw_step _ _ _ _ _ w w' RWw MU WM S5)|].
    split; [exact ST'|].
    split; [eapply rw_cells_transport; [exact FRP| exact MU| exact WM| cbn [disjoint_from cells_size csize pop_frame Nat.add]; split; [lia| exact I]]|].
    split; [exact FRE|]. split; [exact FRM|].
    split; [apply (pk_mapped_wm w w' _ _ WM); [lia| right; lia| lia| exact NEWU]|].
    eapply bytes_at_transport; [exact SHU| exact MU|]. rewrite repeat_length, Z2Nat.id by lia. cbn [disjoint_from]. split; [lia| exact I].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pk_Wd : list (Z * Z) :=
    [(uG - 240, uG); (sh (fa + mfa), sh (fa + mfa) + Fm / 8); (thr + off_th_stats + 72, thr + off_th_stats + 88);
     (R + 16, R + 32); (R + 32, R + 40); (R + 68, R + 69); (free_array_of sb c + 4 * nf, free_array_of sb c + 4 * nf + 4 * N)].
  #[using="PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE key hi lo stkobj canfill md m rac Clg"] Lemma pk_WD : sub_fp pk_Wd (Wi U Fm N) /\ disjoint_from pk_Wd (sa - 336) 336 /\ disjoint_from pk_Wd R 8 /\ disjoint_from pk_Wd (thr + 288) 2480 /\
    disjoint_from pk_Wd (sh (rb + mu)) (U / 8).
  Proof.
    (first [ pose proof (seg_pre) as dR_63; dand14 dR_63 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof seg_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    (first [ pose proof (par_facts) as dR_64; dand6 dR_64 as PU PU4 PU5 PN PF _ | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & _) ]).
    lin_open. unfold pk_Wd.
    split; [sub_open; (cv 0; cv 11; cv 6; cv 2; cv 2; cv 4; cv 5; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. dj_tac.
  Qed.

  #[using="KS PREF CEIL CE CR W0 NR AI SHORT EMP NP PRE hi md"] Lemma pop_D : forall (t0 t1 t2 a6 s6v t3 t4 t5 t6 a0h : word) (junk0 pad scr scr2 scrM old : list byte) (ksc : list word) (w : mem),
    mfa < 4 * (nf + N) ->
    CY junk0 pad scr ksc U Fm 0 w -> RW nf mfa au (mu + U) w -> stk rsegs w lo (uG + -64 + -48 + -128) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) -> rw_cells rsegs w (uG + -64 + -48) (FREc scr2) -> rw_cells rsegs w (uG + -64 + -48 + -128) (FRM2c scrM) ->
    mapped w (rb + mu) U -> bytes_at rsegs w (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    rw_cells rsegs w (sh fev) [CB (Z.to_nat ((nmv - mfa) / 8)) old] -> mapped w (fa + mfa) Fm ->
    evt rsegs (gp_post junk0 pad scr ksc)
        (MS (mkR (wz mapfixed_resume) (wz (uG + -64 + -48 + -128)) gp tp t0 t1 t2 (wz (nmv - mfa)) (wz 1) (wz fev) (wz (nmv - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                 (wz fev) (wz efas_name) (wz PSC) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3 t4 t5 t6)
            F (wz mmap_after_pc) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a6 s6v t3 t4 t5 t6 a0h junk0 pad scr scr2 scrM old ksc w NEEDMAP CYw RWw STw FRP FRE FRM NEWU SHU SHF NEWF.
    (first [ pose proof (seg_pre) as dR_65; dand16 dR_65 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_66; dand8 dR_66 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (EF : Fm = nmv - mfa) by (destruct (ar_fam_cases A c) as [[_ X]|[X _]]; [lia| exact X]).
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw WleUF0)) as dR_67; dand8 dR_67 as PCo TC CSB CREL CPMH CCF2 CCF144 MRN | pose proof (cy_statics _ _ _ _ _ _ _ w CYw WleUF0) as (PCo & TC & CSB & CREL & CPMH & CCF2 & CCF144 & MRN) ]).
    (first [ pose proof ((cy_tst _ _ _ _ _ _ _ w CYw)) as dR_68; dex2 dR_68 as mm72 mm80; rename dR_68 into TST | pose proof ((cy_tst _ _ _ _ _ _ _ w CYw)) as dR_68; dand3 dR_68 as mm72 mm80 TST | destruct (cy_tst _ _ _ _ _ _ _ w CYw) as (mm72 & mm80 & TST) ]).
    (first [ pose proof (CYw) as dR_69; dand4 dR_69 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_70; dand7 dR_70 as RNF RMFA _ _ _ _ REX | pose proof RWw as (RNF & RMFA & _ & _ & _ & _ & REX) ]).
    (* [comment removed for export] *)
    assert (FAJx : exists junk, length junk = Z.to_nat N /\ u32arr rsegs w (free_array_of sb c + 4 * nf) junk).
    { (first [ pose proof ((pk_region A m md n AI NR)) as dR_71; dand11 dR_71 as _ _ _ _ _ _ _ _ _ MFAv _ | pose proof (pk_region A m md n AI NR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MFAv & _) ]). lin_open.
      apply mapped_u32arr; [| rewrite FAE; unfold kFreeArrayOffset; lia| rewrite FAE; unfold kFreeArrayOffset; lia].
      rewrite FAE. intros i Hi. destruct (Z_lt_le_dec (4 * nf + i) mfa) as [OLD|NEW].
      - assert (X : mapped w (fa + 4 * nf + i) 1).
        { apply (cy_mapped _ _ _ _ _ _ _ w CYw (fa + 4 * nf + i) 1); [| unfold kFreeArrayOffset; lia| right; unfold kFreeArrayOffset; lia| unfold kFreeArrayOffset; lia].
          intros j Hj. replace (fa + 4 * nf + i + j) with (fa + (4 * nf + i)) by lia. apply MFAv. lia. }
        specialize (X 0 ltac:(lia)). rewrite Z.add_0_r in X. exact X.
      - replace (fa + 4 * nf + i) with (fa + mfa + (4 * nf + i - mfa)) by lia. apply NEWF. lia. }
    (first [ dex1 FAJx as junk; destruct FAJx as [LJ FAJ] | dand3 FAJx as junk LJ FAJ | destruct FAJx as (junk & LJ & FAJ) ]).
    pose proof (pop_sD gp tp t0 t1 t2 a6 s6v t3 t4 t5 t6 a0h F fc w (wz thr) (wz 1) sa lo thr c (max_count c) sb ri nf au (mu + U) mfa pa_tsd ctx scr2 scrM old junk mm72 mm80) as EV.
    unfold pop_grow_post in EV. cbv zeta in EV. rewrite ?KS in EV. change ((mu + U - au) / size) with N in EV.
    replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) in EV by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
    specialize (EV poison_ok thread_stats_ok MIw STw LO SPA SPH CR MXR THR RIR SBR SBAL SEP_tr SEP_rs SEP_ts NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(lia)
                   ltac:(unfold kFreeArrayMapSize; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) LJ TPL TSDL PCo TC CCF144 RNF RMFA (merge_RAU4 w _ _ RWw)
                   (ex_intro (fun ex => rw_cells rsegs w (R + 68) [C1 ex]) _ REX) FRP FRE FRM FAJ SHF TST).
    eapply evt_mono; [exact EV|].
    (intros st; (first [ intro dR_93; dex15 dR_93 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w'; dand12 dR_93 as -> MU WM MI' ST' RNF' RMFA' RAU4' REX' FA' SHF' _ | intro dR_93; dand27 dR_93 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w' -> MU WM MI' ST' RNF' RMFA' RAU4' REX' FA' SHF' _ | intros (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & w' & -> & MU & WM & MI' & ST' & RNF' & RMFA' & RAU4' & REX' & FA' & SHF' & _) ])).
    unfold pop_sD_W in MU. change ((mu + U - au) / size) with N in MU. rewrite <- EF in MU, SHF'. rewrite RBE in MU, SHF'. change (munch pk_Wd w w') in MU.
    (first [ dand5 pk_WD as SUB DF DR DL DS | destruct pk_WD as (SUB & DF & DR & DL & DS) ]). lin_open.
    pose proof (cy_step _ _ _ _ U Fm 0 U Fm N _ w w' CYw MU WM MI' (Wmono U Fm 0 U Fm N ltac:(lia) ltac:(lia) ltac:(lia)) SUB DF DR DL) as CY'.
    destruct (gpk_intro junk0 pad scr ksc U Fm N w' CY' (fun x H => H) ST' RNF' ltac:(replace (mfa + Fm) with nmv by lia; exact RMFA') RAU4' REX' FA') as (na & GP).
    - apply (pk_mapped_wm w w' _ _ WM); [lia| right; lia| lia| exact NEWU].
    - apply (pk_mapped_wm w w' _ _ WM); [unfold kFreeArrayOffset; lia| right; unfold kFreeArrayOffset; lia| unfold kFreeArrayOffset; lia| exact NEWF].
    - eapply bytes_at_transport; [exact SHU| exact MU|]. rewrite repeat_length, Z2Nat.id by lia. exact DS.
    - exact SHF'.
    - exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', a0h, na, w'. split; [reflexivity| exact GP].
  Qed.

  (* [comment removed for export] *)
End Arm.
