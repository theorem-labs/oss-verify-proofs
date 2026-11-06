(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocI ANodeA7 ASecComb ASechs3 ASecqib ABudget.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
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
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @SPH; @CE0; @USP2; @NR; @USP3; @H; @NS2; @RGE; @RLT; @PN0; @PN1; @RUF])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].

Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac kung := cbv delta [kHighMemBeg kDepotNodesBlock kStackStoreBlockBytes kShadowOffset kStackStoreBlockFrames kMaxSize
                        kAsanHeapLeftRedzoneMagic kMaxPrimaryUser kMallocFillByte kAllocBegMagic CHUNK_ALLOCATED].
Ltac eqrefl := lazymatch goal with |- _ = _ => reflexivity end.
Ltac sides1c := first [ eassumption | eqrefl | lia | modtac ].
Ltac sidesc := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sidesc
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sidesc
  | |- _ /\ _ => first [eassumption | split; sidesc]
  | |- _ => sides1c end.
Ltac sides1 ::= first [ eassumption | eqrefl | lia | kung; lia | modtac
                      | rewrite ?unsigned_lit by lia; first [eassumption | eqrefl | lia | modtac] ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sides
  | |- _ /\ _ => first [eassumption | split; sides]
  | |- _ => sides1 end.
Tactic Notation "callx" uconstr(SPEC) "cleaning" tactic(CLEAN) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | CLEAN; post_call_z segs m ]
  end.
Tactic Notation "callx" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | post_call_z segs m ]
  end.

(* [comment removed for export] *)
Ltac unfa := unfold ASecComb.LMA, ASecComb.LSTAT, ASecComb.lma_entry, ASecComb.comb_entry, ASecComb.comb_sec_ret,
                    ARtSf1m.LMA, ARtSf1m.LSTAT, ARtSf1m.lma_entry, ARtSf1m.lma_mapret, ARtSf1m.lma_name, ARtSf1m.lma_estest,
                    ARtSf1m.mmapordie_entry, ANodeA7.mmapordie_entry, ANodeA7.CF, ANodeA7.PSC, ANodeA7.mmap_ecall_pc, ANodeA7.mmap_after_pc,
                    ANodeA7.mmapordie_resume, AMallocI.TP, AMallocI.alloc_entry, AMallocI.malloc_icpt_entry, off_th_unwinding in *.

(* [comment removed for export] *)
Definition lma_consts (m : word -> option byte) (pn : Z) : Prop :=
     ro_cells rsegs m LMA [C8 (wz 4096)]                                   (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa9178 [C8 (wz pn)] /\ ro_cells rsegs m pn [C8 (wz lma_name)] /\ 0x10000 <= pn /\ pn + 8 <= 0x60a000   (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa9180 [C8 (wz CF)] /\ ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ ro_cells rsegs m (CF + 144) [C8 (wz 0)].                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dep_w8 (top bot fp : Z) : Z := if unwind_depth2 top bot fp then 2 else 1.
Definition dep_b16 (top bot fp : Z) (ra : word) (jb1 : list byte) : list byte := if unwind_depth2 top bot fp then le8 ra else jb1.
(* [comment removed for export] *)

Section A1.
Context {Clg : Ceiling}.
  Variables (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr pn : Z).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned spa).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned spa - 1024.
  Hypothesis SPA : bv_unsigned spa mod 16 = 0.
  Hypothesis SPH : bv_unsigned spa <= 2^47.
  Hypothesis NR : kMaxPrimaryUser < n < 2^30 + 1.
  Hypothesis SO : 0 < stkobj < 2^64.
  Hypothesis CF : 0 <= canfill <= 1.
  (* [comment removed for export] *)
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis LPRE : lma_pre_stmt.
  (* [comment removed for export] *)
  Hypothesis INI : ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x137622 [C1 (Z_to_bv 8 0)].
  Hypothesis RZm : ro_cells rsegs m 0xb2b80 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Hypothesis MUM : ro_cells rsegs m 0xb2b78 [C8 (Z_to_bv 64 (2^40))].
  Hypothesis PCo : poison_consts m.
  Hypothesis LC : lma_consts m pn.
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis TPL : bv_unsigned tp = 0x5e83d8.
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.

  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation ms := (map_size n).

  (* [comment removed for export] *)
  Definition sec_a1_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (junk0 scrL scrM : list byte) (m1 : word -> option byte),
    st = MSsvc (mkR (wz mmapordie_resume) (wz (sa + -128 + -48 + -96 + -48)) gp tp t0' t1' t2' (wz lma_name) (wz ms)
                    (wz 0) (wz ms) (wz 3) (wz 34) (wz (-1)) (wz 0) a6' (wz 222)
                    (wz PSC) (wz (needed_size2 n)) (wz (rz_size n)) (wz 8) (wz 0xb1d58) (wz stkobj) (wz 7) (wz 7) (wz thr) (wz 1)
                    t3' t4' t5' t6')
               F (wz mmap_ecall_pc) (wz 222) fc None m1 (seg_rom rsegs)
    /\ munch [(lo, sa)] m m1
    /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ stk rsegs m1 lo (sa + -128 + -48 + -96 + -48)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (sa + -128) (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (sa + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3743c))
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (sa + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1d58) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret))
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (sa + -128 + -48 + -96 + -48) [CB 12 scrM; C4 (wz 34); C8 (wz ms); C8 (wz LMA); C8 (wz LSTAT); C8 (wz lma_mapret)].

  #[using="CTR TSDL TPL THR TC LC PCo MUM RZm RSS INI LPRE GT RZL SO NR SPH LO ST MI pn ctx tsd Clg"] Lemma sec_a1 : evt rsegs sec_a1_post
    (MS (mkR rac spa gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 stkobj) (Z_to_bv 64 1) (Z_to_bv 64 canfill) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3719c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. pose proof alloc_ceiling_val as CV. pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]). pose proof Bnds as Bnds_; (first [ dand8 Bnds_ as Btsd0 Btsd1 Bctx0 Bctx1 Bthr Bthr1 Btp Bctx | destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx) ]). aobj_lin1 Bthr. aobj_lin1 Bctx.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof LC as LC'. (first [ dand8 LC' as Lpg Lgotn Lname PN0 PN1 Lgotcf Ldpm Lmlim | destruct LC' as (Lpg & Lgotn & Lname & PN0 & PN1 & Lgotcf & Ldpm & Lmlim) ]).
    unfold kMaxPrimaryUser in NR. unfa.
    (* [comment removed for export] *)
    pose proof (rz_log_large n ltac:(lia)) as RZ7. pose proof (rz_size_large n ltac:(lia)) as RSL.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT. pose proof (rounded_size_mod8 n) as RM8.
    assert (MSE : ms = round_up (needed_size2 n) 4096 + 4096) by reflexivity.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as RUF.
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kMaxSize in *.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, sa)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    assert (USP2 : bv_unsigned (Z_to_bv 64 (sa + -128)) = sa + -128) by (rewrite unsigned_lit; lia).
    assert (USP3 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (sa + -128)) + -48)) = sa + -128 + -48) by (rewrite unsigned_lit; lia).
    assert (USP4 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (sa + -128)) + -48)) + -96)) = sa + -128 + -48 + -96) by (rewrite unsigned_lit; lia).
    callx (sec_seg1a_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo n stkobj canfill).
    match goal with H : ?x = rz_log n |- _ => subst x end.
    callx (sec_seg1b_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo n stkobj canfill).
    callx (sec_seg1c_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo n stkobj tsd ctx thr).
    (* [comment removed for export] *)
    Ltac kpost MUc WMc :=
      lazymatch type of MUc with munch _ ?mo ?mn =>
        rewrite ?unsigned_lit in MUc by lia;
        transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
        try match goal with H : mem_inv rsegs mo |- _ => clear H end; try clear mo end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (comb_sec_pre_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc lo (thr + 208) (needed_size2 n));
      unfa; [eassumption| rewrite ?unsigned_lit by lia; eassumption| rewrite ?unsigned_lit by lia; lia| lia| reflexivity| reflexivity| reflexivity| reflexivity| kung; lia|] end.
    intros mC FRC MUC WMC MIC STC. unfa. rewrite ?unsigned_lit in FRC, STC by lia. kpost MUC WMC.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (LPRE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc lo (needed_size2 n) pn);
      unfa; [eassumption| rewrite ?unsigned_lit by lia; eassumption| rewrite ?unsigned_lit by lia; lia| lia| reflexivity| reflexivity| reflexivity
            | lia| apply needed_size2_mod8
            | eassumption| eassumption| eassumption| lia| kung; lia|] end.
    intros a2L scrL mL FRL MUL WML MIL STL. unfa. cbv zeta. rewrite ?unsigned_lit in FRL, STL by lia. kpost MUL WML.
    change (round_up (needed_size2 n) 4096 + 4096) with ms.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (mmapordie_pre_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc lo ms lma_name);
      unfa; [eassumption| rewrite ?unsigned_lit by lia; eassumption| rewrite ?unsigned_lit by lia; lia| lia| rewrite ?unsigned_lit by lia; lia
            | reflexivity| reflexivity| | apply map_size_page| lia| eassumption| eassumption| eassumption| eassumption|] end.
    { unfold map_size, kPageSize. lia. }
    intros t0M t1M t2M a6M t3M t4M t5M t6M scrM mM FRM MUM_ WMM MIM STM. unfa. rewrite ?unsigned_lit in FRM, STM by lia. kpost MUM_ WMM.
    (* [comment removed for export] *)
    unfold sec_a1_post. unfa. rewrite ?unsigned_lit by lia.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; eassumption.
  Qed.
End A1.
