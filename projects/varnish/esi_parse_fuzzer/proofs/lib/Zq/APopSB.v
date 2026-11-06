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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtS4t2 ARtSoqz ARtSb8o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AMTac ANodeA7 ANodeA6 ANodl61.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt34mx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt34mx ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalrrv ASecqib.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt34mx.ARt3_pop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt34mx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3dl2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecqib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegB.
Context {Clg : Ceiling}.
  Variables (gp tp t0 t1 t2 a6 t3 t4 t5 t6 : word) (a0g : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (s2v s10v s11v : word).   (* [comment removed for export] *)
  Variables (usp lo thr c maxc sb ri nf au mu mfa tsd ctx : Z) (scrM old : list byte) (mm72 mm80 statm : word).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (thr + 208 + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (Z.shiftr maxc 1).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (usp + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (sb + c * 4294967296).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size c).
  #[warnings="-notation-for-abbreviation"] Local Notation ums := (round_up (au + (k - nf) * class_size c - mu) kUserMap).
  #[warnings="-notation-for-abbreviation"] Local Notation beg := (sb + c * 4294967296 + mu).
  Hypothesis PS : poison_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (uG + -64 + -128).   (* [comment removed for export] *)
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= usp - 1024.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis MXR : 2 <= maxc <= 16 /\ maxc = 2 * k.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis RIR : kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis SEP_tr : thr + 4096 <= ri \/ ri + 4096 <= thr.
  Hypothesis NF : 0 <= nf < k.
  Hypothesis AU : 0 <= au <= mu /\ mu mod kUserMap = 0 /\ au mod class_size c = 0.
  Hypothesis NOFIT : mu < au + (k - nf) * class_size c.
  Hypothesis CAP : mu <= 3682891136 /\ au <= 3615782272.   (* [comment removed for export] *)
  Hypothesis TPL : bv_unsigned tp = 0x5e7bd8.
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis PCo : poison_consts m.
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis CCF144 : ro_cells rsegs m (CF + 144) [C8 (wz 0)].
  Hypothesis RNF : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis RAU : rw_cells rsegs m (R + 32) [C8 (wz au)].
  Hypothesis RMU : rw_cells rsegs m (R + 48) [C8 (wz mu)].
  Hypothesis FRP : rw_cells rsegs m (uG + -64) (pop_frame (wz k) (wz (E + 16)) (wz (free_array_of sb c)) (wz 2305843009213693952) a0g (wz 0xb1558) (wz R) (wz gfa_popret)).
  Hypothesis FRM : rw_cells rsegs m (uG + -64 + -128) (mapcb_frame scrM (wz beg) (wz ums) (wz rb) beg ums (wz (C + 2560)) (wz R) (wz pop_mapret)).   (* [comment removed for export] *)
  Hypothesis SHB : rw_cells rsegs m (sh beg) [CB (Z.to_nat (ums / 8)) old].
  Hypothesis TST : rw_cells rsegs m (thr + off_th_stats + 72) [C8 mm72; C8 mm80].
  Hypothesis STM : rw_cells rsegs m (C + 2560 + 24) [C8 statm].

  Definition pop_sB_post : machine_state -> Prop := fun st =>
    let mu' := mu + ums in let nc := (mu' - au) / size in
    exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' statm' : word) (m' : word -> option byte),
      st = MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0' t1' t2' (wz R) (wz (nf + nc)) (wz 0xb1558) (wz R) (wz rb) (wz (nf + nc)) a4' a5' a6' a7'
                   (wz rb) (wz nc) (wz (mu' - au)) (wz size) (wz 0xb1558) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3' t4' t5' t6')
              F (wz efas_entry) fc None m' (seg_rom rsegs)
      /\ munch [(uG - 192, uG - 64); (sh beg, sh beg + ums / 8); (thr + off_th_stats + 72, thr + off_th_stats + 88); (C + 2560 + 24, C + 2560 + 32); (R + 48, R + 56)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (uG - 64)
      /\ rw_cells rsegs m' (uG + -64) (pop_frame (wz k) (wz (E + 16)) (wz (free_array_of sb c)) (wz 2305843009213693952) a0g (wz 0xb1558) (wz R) (wz gfa_popret))
      /\ rw_cells rsegs m' (R + 16) [C8 (wz nf)] /\ rw_cells rsegs m' (R + 32) [C8 (wz au)] /\ rw_cells rsegs m' (R + 48) [C8 (wz mu')]
      /\ bytes_at rsegs m' (sh beg) (repeat (Z_to_bv 8 250) (Z.to_nat (ums / 8)))
      /\ rw_cells rsegs m' (thr + off_th_stats + 72) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + ums))]
      /\ rw_cells rsegs m' (C + 2560 + 24) [C8 statm'].

  #[using="STM TST SHB FRM FRP RMU RAU RNF CCF144 TC PCo TSDL TPL CAP NOFIT AU NF SEP_tr SBAL SBR RIR THRA THR MXR CR SPH SPA LO ST MI TSS PS statm old scrM ctx tsd Clg"] Lemma pop_sB :
    evt rsegs pop_sB_post
        (MS (mkR (wz mapfixed_resume) (wz (uG + -64 + -128)) gp tp t0 t1 t2 (wz ums) (wz 1) (wz beg) (wz ums) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                 (wz beg) (wz pop_name) (wz PSC) (wz size) (wz 0xb1558) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3 t4 t5 t6)
            F (wz mmap_after_pc) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CV. pose proof (class_size_range c CR) as CSR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof THR as [THRo THRc]. pose proof (aobj_facts _ _ THRo) as THF.
    unfold PSC, CF in *.
    assert (UMS : au + (k - nf) * class_size c - mu <= ums < au + (k - nf) * class_size c - mu + 262144 /\ ums mod 262144 = 0).
    { unfold kUserMap. apply roundup_famap_range. clear - NOFIT; lia. }
    assert (KS : (k - nf) * class_size c <= 8 * 65536) by (clear - CSR NF MXR; unfold kMaxSize in CSR; nia).
    eapply evt_cut; [eapply (map_post_ok gp tp t0 t1 t2 _ _ _ _ _ _ a6 _ _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 F fc m (uG + -64) lo ums beg beg scrM _ _ _ _ _ _
      (fun s => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         s = MS (mkR (wz pop_mapret) (wz (uG + -64)) gp tp t0' t1' t2' (wz R) (wz (C + 2560)) (wz beg) a1' a2' a3' a4' a5' a6' a7'
                     (wz rb) (wz ums) (wz beg) (wz size) (wz 0xb1558) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3' t4' t5' t6')
                F (wz pop_mapret) fc None m' (seg_rom rsegs)
         /\ munch [(uG + -64 - 128, uG + -64)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (uG + -64)))|].
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF AU CAP UMS KS NOFIT; unfold kHighMemBeg in *; first [lia | kcellz]).
    1: { unfold CF. destruct PCo as (_ & X & _). exact X. }
    1: { rewrite unsigned_lit by (clear - CV SBR CR AU CAP; unfold kHighMemBeg in *; lia). clear - CV SBR CR AU CAP; unfold kHighMemBeg in *; lia. }
    { intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m1 MU1 WM1 MI1 ST1. rewrite ?unsigned_lit in MU1, ST1 by (clear - CV LO LO0 SPH; lia).
      replace (ret_pc (wz pop_mapret)) with (wz pop_mapret : word) by (symmetry; apply ret_pc_even; [unfold pop_mapret; lia| reflexivity]).
      hot_eexists_all. split; [reflexivity|]. exact (conj MU1 (conj WM1 (conj MI1 ST1))). }
    intros ms1 PO. destruct_exs PO. (first [ dand5 PO as -> MU1 WM1 MI1 ST1 | destruct PO as (-> & MU1 & WM1 & MI1 & ST1) ]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    xfer RNF MU1 WM1. xfer RAU MU1 WM1. xfer RMU MU1 WM1. xfer FRP MU1 WM1.
    unfold off_th_stats in *. xfer TST MU1 WM1. xfer STM MU1 WM1. xfer CCF144 MU1 WM1.
    assert (SHB1 : rw_cells rsegs m1 (sh beg) [CB (Z.to_nat (ums / 8)) old]).
    { eapply (rw_cells_transport rsegs _ m m1 _ _ SHB MU1 WM1). cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I]. left.
      unfold sh. clear - CV LO SBR CR AU CAP UMS KS. unfold kHighMemBeg, kShadowOffset in *. Z.div_mod_to_equations. lia. }
    assert (PCo1 : poison_consts m1).
    { destruct PCo as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13). unfold poison_consts.
      xfer P1 MU1 WM1. xfer P2 MU1 WM1. xfer P3 MU1 WM1. xfer P4 MU1 WM1. xfer P5 MU1 WM1. xfer P6 MU1 WM1. xfer P7 MU1 WM1.
      xfer P8 MU1 WM1. xfer P9 MU1 WM1. xfer P10 MU1 WM1. xfer P11 MU1 WM1. xfer P12 MU1 WM1. xfer P13 MU1 WM1.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    assert (TC1 : thread_cells m1 tp tsd ctx thr).
    { destruct TC as (T1 & T2 & T3 & T4 & T5 & Bnds). (first [ pose proof (Bnds) as dR_2; dand8 dR_2 as B1 B2 B3 B4 B5 B6 B7 B8 | pose proof Bnds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) ]). unfold thread_cells. rewrite TPL in *.
      xfer T1 MU1 WM1. xfer T2 MU1 WM1. xfer T3 MU1 WM1. xfer T4 MU1 WM1. xfer T5 MU1 WM1.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; clear - CV; lia. }
    pose proof TC as TC0. (first [ dand6 TC0 as _ _ _ _ _ Bnds | destruct TC0 as (_ & _ & _ & _ & _ & Bnds) ]). (first [ pose proof (Bnds) as dR_4; dand8 dR_4 as B1 B2 B3 B4 B5 B6 B7 B8 | pose proof Bnds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) ]). pose proof (aobj_facts _ _ B8) as CTF.
    eapply (pop_mapped_ok PS TSS gp tp x x0 x1 _ _ _ _ _ _ _ _ _ _ _ _ x9 x10 x11 x12 F fc m1 (uG) lo R sb c (k - nf) (C + 2560) nf au mu ums tsd ctx thr old statm mm72 mm80).
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF AU CAP UMS KS NOFIT TPL TSDL SEP_tr; unfold kHighMemBeg, kShadowOffset, off_th_stats in *; first [lia | kcellz]).
    1: (clear - SPA; Z.div_mod_to_equations; lia).
    1: (apply (aobj_sub _ _ _ _ THRo); clear; lia).
    1: (clear - THRA; Z.div_mod_to_equations; lia).
    1: { destruct AU as (_ & MUM & _). unfold kUserMap in MUM. apply mod_add_lit; [lia| apply mod_add_lit; [lia| apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact SBAL]| apply Znumtheory.Zdivide_mod; exists (c * 536870912); lia]| apply (mod0_down _ 262144 8); [exists 32768; reflexivity| exact MUM]]. }
    1: (clear - UMS NOFIT; destruct UMS as [U1 U2]; unfold kUserMap in *; Z.div_mod_to_equations; lia).
    1: (destruct UMS as [_ U2]; apply (mod0_down _ 262144 8); [exists 32768; reflexivity| exact U2]).
    intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m2 FRP2 RNF2 RAU2 RMU2 SHB2 TST2 STM2 MU2 WM2 MI2 ST2. rewrite ?unsigned_lit in FRP2, MU2, ST2 by (clear - CV LO LO0 SPH; lia).
    destruct STM2 as [statm' STM2].
    apply evt_done. unfold pop_sB_post. cbv zeta. first [ hotw_ex13 t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c statm' m2 | exists t0c, t1c, t2c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, statm', m2 ].
    split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact FRP2|]. split; [exact RNF2|]. split; [exact RAU2|]. split; [exact RMU2|]. split; [exact SHB2|]. split; [exact TST2| exact STM2].
  Qed.
End SegB.

