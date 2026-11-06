(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARtStmts ARtSscs ARtSf1m ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j AInv AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocI AMallocA AMallocH ANodeA7 ANodeA6 ASecComb ASechs3 ASech8k ASecqib ABudget ASecr83 ASecO1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecFinB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecFinB.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASech8k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecr83 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecO1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecFinB.ASecFin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecFinB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ASecs86.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SplitAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @CE0; @SOA; @ABQ; @AMBR; @NR; @NS2; @ER; @KSO; @MSE; @H; @NDE; @Ha; @RGE; @RU8; @DCM; @E0; @NCH; @RUF; @RS8; @LK; @NCH0; @APAR; @PAK; @ADN0; @PC0; @e0; @n; @RLT; @NM8; @H0; @N28; @MSP; @RUB; @PAR; @ADF0; @DF0; @SHMB; @OL])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac simpl_sizes ::=
  rewrite ?app_length, ?repeat_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?repeat_length, ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
  try rewrite ?Z2Nat.id by lia.
Ltac thin := repeat match goal with
  | H : boxed _ |- _ => clear H | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : wr_at _ _ _ _ |- _ => clear H | H : _ -> rw_cells _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
  | H : poison_consts _ |- _ => clear H | H : thread_cells _ _ _ _ _ |- _ => clear H | H : NoDup _ |- _ => clear H end.
Ltac stk_fix := lazymatch goal with |- stk _ ?mm ?l ?hi => match goal with H : stk _ mm l ?hi' |- _ => replace hi with hi' by (thin; lia); exact H end end.
(* [comment removed for export] *)
Ltac cell_exact := lazymatch goal with
  | |- rw_cells _ ?mm ?a _ => match goal with H : rw_cells _ mm a _ |- _ => exact H end
  | |- ro_cells _ ?mm ?a _ => match goal with H : ro_cells _ mm a _ |- _ => exact H | H : rw_cells _ mm a _ |- _ => exact (proj1 H) end
  | |- bytes_at _ ?mm ?a _ => match goal with H : bytes_at _ mm a _ |- _ => exact H end
  | |- u8arr _ ?mm ?a _ => match goal with H : u8arr _ mm a _ |- _ => exact H end
  | |- stk _ ?mm ?lo _ => match goal with H : stk _ mm lo _ |- _ => exact H end
  | |- _ -> rw_cells _ ?mm ?a _ => match goal with H : _ -> rw_cells _ mm a _ |- _ => exact H end
  end.
Ltac sides1c := first [ cell_exact | eassumption | eqrefl | thin; kung; lia | modtac ].
Ltac sidesc := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sidesc
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sidesc
  | |- _ /\ _ => first [eassumption | split; sidesc]
  | |- _ => sides1c end.
Ltac sides1 ::= first [ cell_exact | eassumption | eqrefl | stk_fix | lia | kung; lia | modtac
                      | rewrite ?unsigned_lit by lia; first [eassumption | eqrefl | stk_fix | lia | modtac]
                      | multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ].
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
(* [comment removed for export] *)
Ltac slia_neg a lo hi :=
      repeat match goal with H : ?A /\ _ |- _ => lazymatch A with ~ (_ <= a < _) => destruct H as [? H] end end;
      first [ assumption
            | multimatch goal with H : ~ (?lo' <= a < ?hi') |- _ =>
                apply (notin_mono a lo hi lo' hi' H); repeat match goal with H' : ~ _ |- _ => clear H' end; lia end
            | repeat match goal with H' : ~ _ |- _ => clear H' end; lia ].
Ltac slia1 :=
  lazymatch goal with
  | |- True => exact I
  | |- ~ (?lo <= ?a < ?hi) => slia_neg a lo hi
  | |- _ => first [ lia
                  | multimatch goal with H : apart _ _ _ _ |- _ =>
                      (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ]
  end.
(* [comment removed for export] *)
Ltac clear_negs := repeat match goal with
  | H' : ~ (_ <= _ < _) |- _ => clear H' | H' : outside _ _ |- _ => clear H'
  | H' : ?T |- _ => lazymatch T with (~ (_ <= _ < _)) /\ _ => clear H' end end.
Ltac slia ::= thin;
  lazymatch goal with
  | |- ~ (_ <= _ < _) => slia1
  | |- (~ (_ <= _ < _)) /\ _ => split_all; slia1
  | |- outside _ _ => fail "slia: a folded footprint in an [outside] goal (unfold it first)"
  | |- disjoint_from _ _ _ => fail "slia: a folded footprint in a [disjoint_from] goal (unfold it first)"
  | |- _ => clear_negs; first [ lia | split_all; slia1 ]
  end.
Ltac unfa := unfold ASecComb.LMA, ASecComb.LSTAT, ASecComb.lma_entry, ASecComb.comb_entry, ASecComb.comb_sec_ret,
                    ARtSf1m.LMA, ARtSf1m.LSTAT, ARtSf1m.lma_entry, ARtSf1m.lma_mapret, ARtSf1m.lma_name, ARtSf1m.lma_estest,
                    ARtSf1m.lma_tail, ARtSf1m.lma_espost, ARtSf1m.mapordie_entry,
                    ARtSf1m.mmapordie_entry, ANodeA7.mmapordie_entry, ANodeA7.CF, ANodeA7.PSC, ANodeA7.mmap_ecall_pc, ANodeA7.mmap_after_pc,
                    ANodeA7.mmapordie_resume, ANodeA6.mapfixed_resume, ANodeA6.mapordie_entry, ANodeA6.mapcb_entry, ANodeA6.mapfixed_body, AMallocI.TP, AMallocI.alloc_entry, AMallocI.malloc_icpt_entry, AMallocI.malloc_epi_entry,
                    off_th_unwinding, off_th_stats in *.
(* [comment removed for export] *)
Definition lastm (P : Prop) : Prop := P.   (* [comment removed for export] *)
Ltac clear_lastm := repeat match goal with H : lastm _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac tf_thin ::= thin; clear_negs.
Local Ltac tf_slow ::= slia1.
Local Ltac tf_slow_all ::= first [ lia | split_all; slia1 ].
Local Ltac tf_apart B lo ::= multimatch goal with
  | H : apart B _ ?b _ |- _ => lazymatch lo with context [b] => idtac end; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ B _ |- _ => lazymatch lo with context [a] => idtac end; eapply (apart_gr _ _ _ _ H) end.
Local Ltac tf_skip a ::= lazymatch a with context [kShadowOffset] => idtac | context [sh _] => idtac end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TPL : bv_unsigned ?tp = ?V |- _ => tf_closed V; pose proof (I : regn (bv_unsigned tp) 65536 6266880) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
Ltac post_call_zu segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  clear_lastm;
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  rewrite ?unsigned_lit in MUc by lia;
  try rewrite ?unsigned_lit in PO by lia;
  unfold sec_fin_W, sec_fin_W2, sec_finA_W, sec_finB_W in *; unfa;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      lazymatch type of MUc with ?T => change T with (lastm T) in MUc end;
      lazymatch type of WMc with ?T => change T with (lastm T) in WMc end;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "callx" uconstr(SPEC) "cleaning" tactic(CLEAN) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | CLEAN; post_call_zu segs m ]
  end.
Tactic Notation "callx" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | post_call_zu segs m ]
  end.
Ltac kpost MUc WMc :=
  lazymatch type of MUc with munch _ ?mo ?mn =>
    clear_lastm;
    rewrite ?unsigned_lit in MUc by lia;
    transport_after_call rsegs mo mn MUc WMc;
    lazymatch type of MUc with ?T => change T with (lastm T) in MUc end;
    lazymatch type of WMc with ?T => change T with (lastm T) in WMc end;
    try match goal with H : mem_inv rsegs mo |- _ => clear H end; try clear mo end.
(* [comment removed for export] *)
Ltac hand_impl H :=
  match goal with MU : lastm (munch ?W ?mo ?mn), WM : lastm (wmono _ ?mo ?mn) |- _ =>
  lazymatch type of H with ?P -> rw_cells _ _ ?A ?cs =>
    let H2 := fresh "HI" in
    assert (H2 : P -> rw_cells rsegs mn A cs) by
      (intros HP; pose proof (H HP) as X; apply (rw_cells_transport rsegs W mo mn A cs) in X;
       [exact X| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; slia]);
    clear H; rename H2 into H end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cell_fix := lazymatch goal with
  | |- ro_cells _ ?mm ?a _ => match goal with H : ro_cells _ mm ?a' _ |- _ => replace a with a' by (thin; lia); exact H
                                             | H : rw_cells _ mm ?a' _ |- _ => replace a with a' by (thin; lia); exact (proj1 H) end
  | |- rw_cells _ ?mm ?a _ => match goal with H : rw_cells _ mm ?a' _ |- _ => replace a with a' by (thin; lia); exact H end
  | |- bytes_at _ ?mm ?a _ => match goal with H : bytes_at _ mm ?a' _ |- _ => replace a with a' by (thin; lia); exact H end
  | |- u8arr _ ?mm ?a _ => match goal with H : u8arr _ mm ?a' _ |- _ => replace a with a' by (thin; lia); exact H end
  end.
Ltac thinc := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : wr_at _ _ _ _ |- _ => clear H | H : _ -> rw_cells _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
  | H : poison_consts _ |- _ => clear H | H : thread_cells _ _ _ _ _ |- _ => clear H | H : NoDup _ |- _ => clear H end.
Ltac sides1 ::= first [ cell_exact | eassumption | eqrefl | stk_fix | cell_fix | thin; kung; lia | unfold boxed in *; thinc; kung; lia | unfold boxed in *; thinc; modtac
                      | rewrite ?unsigned_lit by (thin; lia); first [cell_exact | eassumption | eqrefl | stk_fix | cell_fix | thin; kung; lia | unfold boxed in *; thinc; kung; lia | unfold boxed in *; thinc; modtac]
                      | thin; multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ].



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Ltac is_kept H K1 K2 K3 := first [constr_eq H K1 | constr_eq H K2 | constr_eq H K3].
Ltac clear_cells_but K1 K2 K3 := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => tryif is_kept H K1 K2 K3 then fail else clear H
  | H : ro_cells _ _ _ _ |- _ => tryif is_kept H K1 K2 K3 then fail else clear H
  | H : bytes_at _ _ _ _ |- _ => tryif is_kept H K1 K2 K3 then fail else clear H
  | H : u8arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : wr_at _ _ _ _ |- _ => clear H
  | H : _ -> rw_cells _ _ _ _ |- _ => clear H | H : thread_cells _ _ _ _ _ |- _ => clear H | H : poison_consts _ |- _ => clear H end.
Ltac clear_cells := clear_cells_but O O O.

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@CE0; @CTR; @LO; @MBR; @MSE; @RUB; @THR])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hot_slow_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@LO; @ABQ; @CE0; @AMBR; @KSO; @SOA; @SHMB; @NR; @NDE; @MSE; @DCM])).
Ltac hot_slow_full := slia1.
Ltac hot_slow_all_full := first [ lia | split_all; slia1 ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_slow ::= first [ solve [ hot_slow_cut; hot_slow_full ] | hot_slow_full ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_slow_all ::= first [ solve [ hot_slow_cut; hot_slow_all_full ] | hot_slow_all_full ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.simpl_arr_sizes ::= rewrite ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.u32s_length, ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.u64s_length, ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.upd_length.
(* [comment removed for export] *)
Section O3bA8c.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (rac spa gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (s1x a0w : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr sb mb q d e dc ru pa nch nres n0 f0 : Z).
  Variables (junk0 scrL scrM old1 : list byte) (key : list Z) (lk1 lk2 : Z) (cs : byte)
            (na nf ca mx cidx pan sta stm v0 v1 v2 vl mm72 mm80 h2 w4 d8 j0 j1 j2 k0 k1 : word) (b0w b1w : byte) (bsl : list word)
            (D : list (list Z)) (olds oll uj : list byte) (oldp : byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.

  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation ms := (map_size n).
  #[warnings="-notation-for-abbreviation"] Local Notation AB := (mb + 4096).
  #[warnings="-notation-for-abbreviation"] Local Notation KEY := (key).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (sa + -128 + -48 + -96 + -48).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= sa - 1024.
  Hypothesis SPA : sa mod 16 = 0.
  Hypothesis SPH : sa + 65536 < 2^64.
  Hypothesis NR : kMaxPrimaryUser < n < 2^31.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis DC : dc = d + (if e =? 0 then 0 else 1).
  Hypothesis MB : bv_unsigned a0w = mb.
  (* [comment removed for export] *)
  Hypothesis LMID : lma_mid_stmt.
  Hypothesis LTAIL : lma_tail_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis P0 : poison0_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb2be4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa9df0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146e80 [C8 (Z_to_bv 64 0)].
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m LMA [C8 (Z_to_bv 64 4096)].
  Hypothesis LPA8 : ro_cells rsegs m (LMA + 8) [C8 (wz pa)].
  Hypothesis Lgotcf : ro_cells rsegs m 0xa9180 [C8 (wz CF)].
  Hypothesis Lmlim : ro_cells rsegs m (CF + 144) [C8 (wz 0)].
  Hypothesis CF260 : ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)].
  Hypothesis LPA16 : ro_cells rsegs m (LMA + 16) [C8 (wz pa)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e83d8.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STM : rw_cells rsegs m (thr + 2872) [C8 mm72; C8 mm80].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  (* [comment removed for export] *)
  Hypothesis MBR : aobj mb ms /\ mb + ms <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis MBA : mb mod 4096 = 0.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SEP_sb : apart mb ms sb (2^37).
  Hypothesis SEP_thr : apart mb ms thr 4096.
  Hypothesis SEP_ctx : apart mb ms ctx 0x10000.
  Hypothesis SEP_n0 : apart mb ms n0 kDepotNodesBlock.
  Hypothesis SEP_f0 : apart mb ms f0 kStackStoreBlockBytes.
  Hypothesis SEP_pa : apart mb ms pa (8 * nres).
  Hypothesis SEP_pat : apart pa (8 * nres) thr 4096.
  Hypothesis SEP_pac : apart pa (8 * nres) ctx 0x10000.
  Hypothesis SEP_pan : apart pa (8 * nres) n0 kDepotNodesBlock.
  Hypothesis SEP_paf : apart pa (8 * nres) f0 kStackStoreBlockBytes.
  Hypothesis J012 : rw_cells rsegs m mb [C8 j0; C8 j1; C8 j2].
  Hypothesis CIDX : rw_cells rsegs m (mb + 24) [C8 cidx].
  Hypothesis ABH : rw_cells rsegs m AB [C8 k0; C8 k1].
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis USR : rw_cells rsegs m (AB + 2048) [CB 4096%nat uj].
  Hypothesis SH512 : rw_cells rsegs m (sh mb) [CB 512 old1].
  Hypothesis SHL : rw_cells rsegs m (q + kShadowOffset) [CB 256 oll].
  Hypothesis SHU : u8arr rsegs m (q + 256 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
  Hypothesis SHT : stk rsegs m (q + 256 + dc + kShadowOffset) (q + ru + kShadowOffset).
  (* [comment removed for export] *)
  Hypothesis NCH : 0 <= nch <= nres /\ nres <= kChunksBlockCount.
  Hypothesis PAR : aobj pa (8 * nres) /\ pa + 8 * nres <= alloc_ceiling /\ pa mod 8 = 0.   (* [comment removed for export] *)
  Hypothesis LBSL : length bsl = 64%nat.
  Hypothesis LK : 0 <= lk1 < 256 /\ 0 <= lk2 < 2^15.
  Hypothesis LREG : rw_cells rsegs m (LMA + 48) [C8 (wz nres); C8 (wz nch)].
  Hypothesis LCS : rw_cells rsegs m (LMA + 64) [C1 cs].
  Hypothesis LSTA : rw_cells rsegs m (LMA + 72) [C8 na; C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)].
  Hypothesis LMTX : rw_cells rsegs m (LMA + 616) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 lk1); C2 (wz lk2)].
  Hypothesis PAN : rw_cells rsegs m (pa + 8 * nch) [C8 pan].
  Hypothesis GST : rw_cells rsegs m (LSTAT + 16) [C8 sta; C8 stm].
  (* [comment removed for export] *)
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length key) < kStackStoreBlockFrames.
  Hypothesis CFL : 0 <= canfill <= 1.
  (* [comment removed for export] *)
  Hypothesis SOA : sa <= stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis KL : (1 <= length key <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis DRF : forall D' (m1 m2 : word -> option byte), dr AL_pasan rsegs D' n0 f0 m1 ->
      (forall a, depot_foot AL_pasan n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pasan rsegs D' n0 f0 m2.
  (* [comment removed for export] *)
  Hypothesis FRA : rw_cells rsegs m (sa + -128)
         (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0).
  Hypothesis FRC : rw_cells rsegs m (sa + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3743c)).
  Hypothesis FRL : rw_cells rsegs m (sa + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1d58) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)).
  Hypothesis FRM : rw_cells rsegs m (sa + -128 + -48 + -96 + -48) [CB 12 scrM; C4 (wz 34); C8 (wz ms); C8 (wz LMA); C8 (wz LSTAT); C8 (wz lma_mapret)].

  (* [comment removed for export] *)
  Hypothesis NCH0 : nch = 0 /\ nres = 0.
  Hypothesis PAK : pa mod 4096 = 0 /\ pa + 0x20000 <= alloc_ceiling.
  Hypothesis LESP : lma_esp_stmt.
  Hypothesis MFP : mapfixed_pre_stmt.

  (* [comment removed for export] *)
  Definition sec_o3b_a8_postc : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr olt : list byte) (m' : word -> option byte),
    st = MSsvc (mkR (wz mapfixed_resume) (wz (sa + -128 + -48 + -96 + -96)) gp tp t0' t1' t2' (wz 0x20000) (wz 0)
                    (wz pa) (wz 0x20000) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                    (wz pa) (wz 0) (wz PSC) (wz mb) (wz (mb + ms)) (wz (AB + needed_size2 n)) (wz 7) (wz AB) (wz thr) (wz 1) t3' t4' t5' t6')
               F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs)
    /\ munch ([(sa + -128 + -48 + -96 - 48, sa + -128 + -48 + -96); (sa + -128 + -48 - 96 - 64, sa + -128 + -48 - 96);
               (sh mb, sh mb + 512); (sh (mb + 4096 + needed_size2 n), sh (mb + 4096 + needed_size2 n) + (ms - 4096 - needed_size2 n) / 8);
               (mb, mb + 24); (thr + 2800 + 72, thr + 2800 + 88); (LMA + 616, LMA + 620)]
              ++ [(sa + -128 + -48 + -96 - 368, sa + -128 + -48 + -96)]) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (sa + -128 + -48 + -96 + -96)
    /\ 0 <= lma_lz ms < 64
    /\ rw_cells rsegs m' (sa + -128 + -48 + -96 + -96) (mapfixed_frame scr (wz AB) (wz (lma_lz ms)) (wz ms) (wz LMA) (wz LSTAT) (wz lma_espost))
    /\ poison_consts m' /\ thread_cells m' tp tsd ctx thr
    /\ ro_cells rsegs m' 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)]
    /\ ro_cells rsegs m' 0xb2c0d [C1 (Z_to_bv 8 1)]
    /\ ro_cells rsegs m' 0xb2be4 [C4 (Z_to_bv 64 4096)]
    /\ ro_cells rsegs m' 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)]
    /\ ro_cells rsegs m' 0xa9df0 [C8 (Z_to_bv 64 0x10)]
    /\ ro_cells rsegs m' (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)]
    /\ ro_cells rsegs m' 0x146e80 [C8 (Z_to_bv 64 0)]
    /\ ro_cells rsegs m' 0xb1d78 [C8 (Z_to_bv 64 sb)]
    /\ ro_cells rsegs m' LMA [C8 (Z_to_bv 64 4096)]
    /\ ro_cells rsegs m' (LMA + 8) [C8 (wz pa)]
    /\ ro_cells rsegs m' (LMA + 16) [C8 (wz pa)]
    /\ ro_cells rsegs m' 0xa9180 [C8 (wz CF)]
    /\ ro_cells rsegs m' (CF + 144) [C8 (wz 0)]
    /\ ro_cells rsegs m' (CF + 260) [C1 (Z_to_bv 8 0)]
    /\ ro_cells rsegs m' thr [C8 (Z_to_bv 64 ctx)]
    /\ ro_cells rsegs m' (ctx + 8) [C4 (Z_to_bv 64 0)]
    /\ rw_cells rsegs m' (thr + 2800) [C8 v0; C8 v1; C8 v2]
    /\ rw_cells rsegs m' (thr + off_th_stats + 72) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + ms))]
    /\ rw_cells rsegs m' (thr + 2904) [C8 vl]
    /\ rw_cells rsegs m' mb [C8 (wz mb); C8 (wz ms); C8 (wz (needed_size2 n))]
    /\ rw_cells rsegs m' (mb + 24) [C8 cidx]
    /\ rw_cells rsegs m' AB [C8 k0; C8 k1]
    /\ rw_cells rsegs m' (AB + 2032) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8]
    /\ rw_cells rsegs m' (AB + 2048) [CB 4096%nat uj]
    /\ bytes_at rsegs m' (sh mb) (repeat (Z_to_bv 8 250) 512)
    /\ rw_cells rsegs m' (q + kShadowOffset) [CB 256 oll]
    /\ u8arr rsegs m' (q + 256 + kShadowOffset) olds
    /\ (e <> 0 -> rw_cells rsegs m' (q + 256 + d + kShadowOffset) [C1 oldp])
    /\ rw_cells rsegs m' (q + 256 + dc + kShadowOffset) [CB (Z.to_nat (ru - 256 - dc)) olt]
    /\ rw_cells rsegs m' (LMA + 48) [C8 (wz nres); C8 (wz nch); C1 cs]
    /\ rw_cells rsegs m' (LMA + 72) [C8 na; C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)]
    /\ rw_cells rsegs m' (LMA + 616) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 lk1); C2 (wz lk2)]
    /\ rw_cells rsegs m' (LSTAT + 16) [C8 sta; C8 stm]
    /\ dr AL_pasan rsegs D n0 f0 m'
    /\ ro_cells rsegs m' stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))]
    /\ bytes_at rsegs m' (stkobj + 16) (u64s (map (Z_to_bv 64) key))
    /\ rw_cells rsegs m' (sa + -128)
         (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0)
    /\ rw_cells rsegs m' (sa + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3743c))
    /\ rw_cells rsegs m' (sa + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1d58) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)).

  #[using="MFP LESP PAK NCH0 FRM FRL FRC FRA DRF SEP_f0t SEP_n0t DF0 DN0 KL TRB TRC SOA DR GST LMTX LSTA LCS LREG LK LBSL PAR NCH SHT SHP OL SHU SHL SH512 USR HDR ABH CIDX J012 SEP_f0 SEP_n0 SEP_ctx SEP_thr RU8 ABQ MBA MBR STL STM STS SEP_tc TPL TSDL CTR THR CT8 TH0 TC LPA16 CF260 Lmlim Lgotcf LPA8 PGS SBc HK LS2 LS1 AF52 AF44 AF2 AF1 PCo P0 PS TSS LMID MB DC ER NDE NR SPA LO ST MI j2 j1 j0 old1 scrM"] Lemma sec_o3b_a8 : evt rsegs sec_o3b_a8_postc
    (MS (mkR (wz mmapordie_resume) (wz (sa + -128 + -48 + -96 + -48)) gp tp t0 t1 t2 (wz lma_name) s1x
             a0w a1 a2 a3 a4 a5 a6 a7
             (wz PSC) (wz (needed_size2 n)) (wz (rz_size n)) (wz 8) (wz 0xb1d58) (wz stkobj) (wz 7) (wz 7) (wz thr) (wz 1)
             t3 t4 t5 t6)
        F (wz mmap_after_pc) fc None m (seg_rom rsegs)).
  Proof. try clear LTAIL. try clear DPS. try clear SBR. try clear SEP_sb. try clear SEP_pa. try clear SEP_pat. try clear SEP_pac. try clear SEP_pan. try clear SEP_paf. try clear CFL. try clear KR. try clear SEP_n0c. try clear SEP_f0c.   (* [comment removed for export] *) (* [comment removed for export] *) box KL. box LBSL.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof alloc_ceiling_val as CV. pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]). pose proof Bnds as Bnds_; (first [ dand8 Bnds_ as Btsd0 Btsd1 Bctx0 Bctx1 Bthr Bthr1 Btp Bctx | destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx) ]). aobj_lin1 Bthr. aobj_lin1 Bctx.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    unfold kMaxPrimaryUser in NR. unfa.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (needed_size2_mod8 n) as NM8.
    pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as RUF.
    assert (MSE : ms = 8 * ru + 4096) by (unfold map_size, kPageSize; lia).
    pose proof (map_size_page n) as MSP. unfold kPageSize in MSP.
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kMaxSize, kStackStoreBlockFrames, kChunksBlockCount in *.
    assert (KSO : kShadowOffset = 2147450880) by reflexivity.
    assert (USP : sa = sa) by reflexivity.
    assert (DCM : dc = d + Z.min e 1) by (try (generalize alloc_ceiling_val); clear - DC ER; rewrite DC; destruct (Z.eqb_spec e 0); lia).
    assert (QR : 1024 <= q /\ q + ru <= 17592184995840) by (try (generalize alloc_ceiling_val); clear - AMBR MSE ABQ; lia).   (* [comment removed for export] *)
    assert (RUB : 65536 <= 8 * ru <= 2^31 + 8192) by (try (generalize alloc_ceiling_val); clear - RU8 RUF NS2 RGE RLT NR; lia).
    assert (N28 : 65536 <= needed_size2 n <= 8 * ru /\ needed_size2 n mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - RUF RU8 NS2 RGE RLT NR NM8; lia).
    (* [comment removed for export] *)
    assert (SHMB : sh mb = q - 512 + kShadowOffset).
    { clear - ABQ MBA KSO. unfold sh. rewrite KSO. pose proof (Z.div_mod mb 8 ltac:(lia)).
      assert (mb mod 8 = 0) by (rewrite <- (Z.mod_mod _ _) ; [| lia]; Z.div_mod_to_equations; nia). lia. }
    assert (SHUE : sh (mb + 4096 + needed_size2 n) = q + needed_size2 n / 8 + kShadowOffset).
    { clear - ABQ MBA KSO N28. unfold sh. rewrite KSO. destruct N28 as [_ M8].
      pose proof (Z.div_mod (needed_size2 n) 8 ltac:(lia)). rewrite M8 in H.
      replace (mb + 4096 + needed_size2 n) with (8 * (q + needed_size2 n / 8)) by lia. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    assert (RS8 : rounded_size n = 8 * dc).
    { clear - NDE ER DCM NR. unfold rounded_size, round_up. replace (Z.max n 8) with n by lia.
      replace (n + 8 - 1) with ((e + 7) + d * 8) by lia. rewrite Z.div_add by lia.
      destruct (Z.eq_dec e 0) as [E0|E0].
      - rewrite E0. change ((0 + 7) / 8) with 0. lia.
      - rewrite <- (Z.div_unique (e + 7) 8 1 (e - 1)); [lia| left; lia| lia]. }
    assert (N8R : 8192 <= needed_size2 n / 8 <= ru /\ 256 + dc <= needed_size2 n / 8 /\ needed_size2 n = 8 * (dc + 512)).
    { clear - N28 RS8 NS2 NR NDE ER DCM. assert (E8 : needed_size2 n = 8 * (dc + 512)) by lia.
      rewrite E8 at 1 2. rewrite E8. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    assert (TL8 : (ms - 4096 - needed_size2 n) / 8 = ru - needed_size2 n / 8).
    { clear - MSE N28. destruct N28 as [_ M8]. pose proof (Z.div_mod (needed_size2 n) 8 ltac:(lia)). rewrite M8 in H.
      replace (ms - 4096 - needed_size2 n) with (8 * (ru - needed_size2 n / 8)) by lia. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    (* [comment removed for export] *)
    assert (SEPthrM : mb + ms <= thr \/ thr + 4096 <= mb) by (clear - SEP_thr; exact SEP_thr).
    assert (K2 : 2 <= ms / 4096 <= 2^19 + 16 /\ ms = 4096 * (ms / 4096)) by (try (generalize alloc_ceiling_val); clear - MSE RUB MSP; Z.div_mod_to_equations; lia).
    set (k := ms / 4096) in K2.
    assert (TL8k : (4096 * k - 4096 - needed_size2 n) / 8 = ru - needed_size2 n / 8) by (destruct K2 as [_ E]; rewrite <- E; exact TL8).
    (* [comment removed for export] *)
    box SPA. box SPH. box RU8. box RUF. box RGE. box RLT. box NS2. box NM8. box MSP. box DC.
    box Btsd0. box Btsd1. box Bctx0. box Bctx1. box Bthr. box Bthr1. box Btp. box Bctx. box THRA. box MBA. box LBSL. box LK. box DLEN. box DND. box DTOT.
    assert (LK1 : 0 <= lk1 < 256) by (try (generalize alloc_ceiling_val); clear - LK; unfold boxed in LK; lia). assert (LK2 : 0 <= lk2 < 2^15) by (try (generalize alloc_ceiling_val); clear - LK; unfold boxed in LK; lia).
    box SEPthrM. box N28. box LK1. box LK2.
    try clear Cini Ckey Ctsd Cctx Cthr2. try clear Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps. clear PAN.
    pose proof (munch_refl ([(sa + -128 + -48 + -96 - 48, sa + -128 + -48 + -96); (sa + -128 + -48 - 96 - 64, sa + -128 + -48 - 96);
               (sh mb, sh mb + 512); (sh (mb + 4096 + needed_size2 n), sh (mb + 4096 + needed_size2 n) + (ms - 4096 - needed_size2 n) / 8);
               (mb, mb + 24); (thr + 2800 + 72, thr + 2800 + 88); (LMA + 616, LMA + 620)]
              ++ [(sa + -128 + -48 + -96 - 368, sa + -128 + -48 + -96)]) m) as MU.
    cbn [app] in MU. unfa.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    callx sec_o3mid_a8 cleaning (unfa; clear_cells).
    all: idtac "Q1done".
    destruct NCH0 as [NC0 NR0].
    replace (Z_to_bv 64 nres) with (Z_to_bv 64 nch) by (f_equal; lia).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (LESP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc (sa + -128 + -48) nch pa (mb + 4096)) end; unfa.
    all: lazymatch goal with |- evt _ _ _ => idtac | _ => sides end.
    all: idtac "Q2done".
    replace (pa + 8 * nch) with pa by lia.
    change (Z_to_bv 64 477996) with (Z_to_bv 64 (mapfixed_thunk 0)).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      match goal with H : poison_consts mc |- _ =>
        (first [ dand13 H as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct H as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]) end;
      match goal with H : thread_cells mc _ _ _ _ |- _ => (first [ dand6 H as Cini Ckey Ctsd Cctx Cthr2 Bnds2 | destruct H as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds2) ]) end;
      unfa;
      eapply (MFP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc lo 0 pa 0x20000 0) end; unfa.
    all: lazymatch goal with |- forall _, _ => idtac | _ => sides end.
    all: idtac "Q3done".
    intros t0X t1X t2X a6X t3X t4X t5X t6X scr mX FRX MUX WMX MIX STX.
    unfa. rewrite ?unsigned_lit in FRX by lia. rewrite ?unsigned_lit in STX by lia. rewrite ?unsigned_lit in MUX by lia.
    rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    match goal with H : e <> 0 -> rw_cells rsegs ?mo ?A ?cs |- _ =>
      assert (SHPX : e <> 0 -> rw_cells rsegs mX A cs) by
        (intros E0; pose proof (H E0) as X;
         lazymatch type of MUX with munch ?W _ _ => apply (rw_cells_transport rsegs W mo mX A cs) in X;
           [exact X| exact MUX| exact WMX| cbn [disjoint_from]; simpl_sizes; slia] end); clear H end.
    match goal with DRc : dr _ _ D n0 f0 ?mo |- _ =>
      assert (DRX : dr AL_pasan rsegs D n0 f0 mX) by
          (eapply (DRF D mo mX DRc); intros a Ha; apply (MUX (Z_to_bv 64 a));
           unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha;
           rewrite unsigned_lit by lia; cbn [outside]; destruct Ha as [Ha|[Ha|Ha]]; rsplit; apply outside_of_disj; slia); clear DRc end.
    kpost MUX WMX.
    assert (TCX : thread_cells mX tp tsd ctx thr) by (unfold thread_cells; repeat (split; [assumption|]); first [assumption | apply aobjK_e; assumption | unfold boxed in *; kung; lia]).
    assert (PCX : poison_consts mX) by (unfold poison_consts; repeat (split; [assumption|]); assumption).
    all: idtac "Q4done".
    unfold sec_o3b_a8_postc. unfa.
    hot_eexists_all.
    split; [reflexivity|].
    split_all; try (first [cell_exact | eassumption]).
    all: try (thin; lia).
    all: match goal with |- ?g => idtac "REM" g end.
  Qed.
End O3bA8c.

