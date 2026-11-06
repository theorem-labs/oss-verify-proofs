(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AMalq4j AMalrrv.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j ARtStmts ARtS4t2 AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA.AMalrao OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3dl2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
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
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @SOA; @CV; @H; @LKS; @RIR; @SBR; @CR1; @RSR; @RGE; @NS; @NR; @NSB; @MXR; @SEP_tr; @SEP_thr; @THR; @ATHR; @Hi; @CSR; @Str])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I | lia
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided1 x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided1 x y
          end ].

Section AllocHead.
Context {Clg : Ceiling}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr c maxc sb ri : Z) (ks : list word).
  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (thr + 208 + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (Z.shiftr maxc 1).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo usp.
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= usp - 1024.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis SPR : usp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis SOA : usp <= stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis INI : ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x136e22 [C1 (Z_to_bv 8 0)].
  Hypothesis RZm : ro_cells rsegs m 0xb2380 [C2 (wz 16); C2 (wz 2048)].
  Hypothesis MUM : ro_cells rsegs m 0xb2378 [C8 (wz (2^40))].
  Hypothesis SBc : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m 0xb1588 [C8 (wz ri)].
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (wz ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (wz 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e7bd8.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SEP_thr : apart thr 4096 sb (2^37).
  Hypothesis SEP_ctx : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis RIR : kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_cri : apart ctx 0x10000 ri 4096.
  Hypothesis MX : rw_cells rsegs m R [C8 (wz 0)].

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section Inited.
  Hypothesis PC : rw_cells rsegs m E [C4 (wz 0); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)].
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis MXR : 2 <= maxc <= 16.

  #[using="MXR LKS PC MX SEP_cri SEP_tr RIAL RIR HC SEP_thr SBR TPL TSDL CTR THRA THR CT8 TH0 TC CRI SBc MUM RZm RSS INI BLK GT RZL SOA NR SPR SPA LO ST MI ks ctx tsd Clg"] Lemma alloc_head : evt rsegs (alloc_head_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo n stkobj canfill thr c maxc sb ri [] (fun _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xb1558) (wz n) (wz 8) (wz stkobj) (wz 1) (wz canfill) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3707c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CV. aobjL THR. aobjL CTR.
    pose proof (zr_word sp) as SPRg; unfold inr64 in SPRg.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (class_size_range c CR1) as CSR. unfold kMaxSize in CSR.
    pose proof (needed_size_mod8 n) as NS8.
    assert (KR : 1 <= k <= 8) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SO : 0 < stkobj < 2^64) by lia.
    assert (CAL : C mod 16 = 0) by (rewrite Z.add_mod, THRA by lia; reflexivity).
    assert (SEP_cr : apart C 3888 ri 4096) by (generalize SEP_tr; unfold apart; clear; intros; lia).
    assert (SEP_cs : apart C 3888 sb (2^37)) by (generalize SEP_thr; unfold apart; clear; intros; lia).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    unfold kHighMemBeg in *.
    pose proof (munch_refl [(usp - 1024, usp); (R, R + 8)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    callx alloc_seg1a_spec.
    match goal with H : ?x = rz_log n |- _ => subst x end.
    callx alloc_seg1b_spec.
    callx alloc_seg1c_spec.
    (* [comment removed for export] *)
    amz.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (comb_to_gfa (wz 0x3731c) (wz (usp + -128)) gp tp _ _ _ (wz 1) (wz n) _ _ _ _ (wz 8) (wz (needed_size n)) (wz (rz_size n)) (wz n)
                 (wz 0xb1558) (wz stkobj) (wz (-8)) (wz 7) (wz thr) (wz 1) _ _ _ _ F fc mc lo C c maxc (class_size c) sb ri (needed_size n) ks)
    end.
    all: rewrite ?unsigned_lit by lia.
    all: try (first [fside CV | kcellz | zmod]).
    intros t0' t1' a5' a6' a7' pad m1 MI1 ST1 CF1 RF1 MU1 WM1.
    rewrite ?unsigned_lit in ST1, CF1, RF1, MU1 by lia. kpost MU1 WM1.
    (* [comment removed for export] *)
    eapply (gfa_lock_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz thr) (wz 1) _ _ _ _ F fc m1 lo ri sb c);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr m2 MX2 GF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in GF2, MU2, ST2 by lia. kpost MU2 WM2. rewrite ?unsigned_lit by lia.
    apply evt_done. unfold alloc_head_post, gfa_locked, comb_frameR, gfa_frameR, comb_refill_ret. cbv zeta.
    hot_eexists_all.
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside app]. clear. intros; lia. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcellz | eassumption | exact I].
  Qed.
  End Inited.

  (* [comment removed for export] *)
  Section Init0.
  Variables (cnt mc0 cs0 : Z -> Z) (kss : Z -> list word).
  Hypothesis LINES : forall i, 1 <= i <= 31 ->
      0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (kss i) = 16%nat /\
      rw_cells rsegs m (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (kss i))].
  Hypothesis MC0 : mc0 c = 0.
  Hypothesis CNT0 : cnt c = 0.

  #[using="CNT0 MC0 LINES cs0 mc0 MX SEP_cri SEP_tr RIAL RIR HC SEP_tc SEP_thr SBR TPL TSDL CTR THRA THR CT8 TH0 TC CRI SBc MUM RZm RSS INI BLK GT RZL SOA NR SPR LO ST MI ctx tsd Clg"] Lemma alloc_head0 : evt rsegs (alloc_head_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo n stkobj canfill thr c (max_count c) sb ri
                                 [(C + 80, C + 2560)]
                                 (fun m' => forall i, 1 <= i <= 31 ->
                                    rw_cells rsegs m' (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (kss i))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xb1558) (wz n) (wz 8) (wz stkobj) (wz 1) (wz canfill) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3707c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CV. aobjL THR. aobjL CTR.
    pose proof (zr_word sp) as SPRg; unfold inr64 in SPRg.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (class_size_range c CR1) as CSR. unfold kMaxSize in CSR.
    pose proof (needed_size_mod8 n) as NS8.
    (first [ pose proof ((max_count_facts c ltac:(lia))) as dR_2; dand3 dR_2 as MCR MCH RCR | pose proof (max_count_facts c ltac:(lia)) as (MCR & MCH & RCR) ]).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SO : 0 < stkobj < 2^64) by lia.
    assert (CAL : C mod 16 = 0) by (rewrite Z.add_mod, THRA by lia; reflexivity).
    assert (SEP_cr : apart C 3888 ri 4096) by (generalize SEP_tr; unfold apart; clear; intros; lia).
    assert (SEP_cs : apart C 3888 sb (2^37)) by (generalize SEP_thr; unfold apart; clear; intros; lia).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    unfold kHighMemBeg in *.
    pose proof (munch_refl [(usp - 1024, usp); (R, R + 8); (C + 80, C + 2560)] m) as MU.
    pose proof (munch_refl [(usp - 1024, usp)] m) as MUS.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    callx alloc_seg1a_spec.
    match goal with H : ?x = rz_log n |- _ => subst x end.
    callx alloc_seg1b_spec.
    callx alloc_seg1c_spec.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (LINES1 : forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (kss i) = 16%nat /\
                rw_cells rsegs mc (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (kss i))])
        by (intros i Hi; (first [ pose proof ((LINES i Hi)) as dR_4; dand5 dR_4 as X1 X2 X3 X4 X5 | destruct (LINES i Hi) as (X1 & X2 & X3 & X4 & X5) ]); refine (conj X1 (conj X2 (conj X3 (conj X4 _))));
            eapply (rw_cells_transport rsegs _ m mc); [exact X5 | exact MUS | exact WM | cbn [disjoint_from]; simpl_sizes; clear - Hi ATHR CV LO SPRg; lia])
    end.
    clear MUS.
    (* [comment removed for export] *)
    amz.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (comb_to_gfa0 (wz 0x3731c) (wz (usp + -128)) gp tp _ _ _ (wz 1) (wz n) _ _ _ _ (wz 8) (wz (needed_size n)) (wz (rz_size n)) (wz n)
                 (wz 0xb1558) (wz stkobj) (wz (-8)) (wz 7) (wz thr) (wz 1) _ _ _ _ F fc mc lo C c sb ri (needed_size n) cnt mc0 cs0 kss);
      [> try (fside CV) .. | idtac]
    end.
    all: rewrite ?unsigned_lit by lia.
    all: try (first [exact LINES1 | fside CV | kcellz | zmod]).
    intros a5' a6' a7' t0' t1' t2' t3' t4' t5' pad m1 MI1 ST1 CF1 RF1 LINES2 MU1 WM1.
    clear LINES1. rewrite ?unsigned_lit in ST1, CF1, RF1, MU1 by lia. kpost MU1 WM1.
    (* [comment removed for export] *)
    eapply (gfa_lock_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz thr) (wz 1) _ _ _ _ F fc m1 lo ri sb c);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | kcellz | zmod]).
    intros t0b t1b t2b a0b a5b a6b a7b t3b t4b t5b t6b scr m2 MX2 GF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in GF2, MU2, ST2 by lia.
    assert (LINES3 : forall i, 1 <= i <= 31 -> rw_cells rsegs m2 (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (kss i))]).
    { intros i Hi. pose proof (proj1 (proj2 (proj2 (proj2 (LINES i Hi))))) as X4.
      eapply (rw_cells_transport rsegs _ m1 m2); [exact (LINES2 i Hi) | exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes].
      pose proof SEP_tr as Str. unfold apart in Str. clear - Hi ATHR CV LO SPRg Str CR1 RIR. lia. }
    clear LINES2. kpost MU2 WM2. rewrite ?unsigned_lit by lia. rewrite <- MCH. rewrite <- MCH in GF2.
    apply evt_done. unfold alloc_head_post, gfa_locked, comb_frameR, gfa_frameR, comb_refill_ret. cbv zeta.
    hot_eexists_all.
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside app]. clear. intros; lia. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcellz | eassumption | exact I].
  Qed.
  End Init0.

End AllocHead.

(* [comment removed for export] *)
Section Closed.
Context {Clg : Ceiling}.
  Theorem alloc_head_ok : alloc_head_stmt.
  Proof.
    unfold alloc_head_stmt. intros until ks. cbv zeta. intros. eapply alloc_head; eassumption.
  Qed.
  Theorem alloc_head0_ok : alloc_head0_stmt.
  Proof.
    unfold alloc_head0_stmt. intros until ks. cbv zeta. intros. eapply alloc_head0; eassumption.
  Qed.
End Closed.
