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
Section SegC.
Context {Clg : Ceiling}.
  Variables (gp tp t0 t1 t2 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word) (a0g : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (s2v s10v s11v : word).   (* [comment removed for export] *)
  Variables (usp lo thr c maxc sb ri nf au mu mfa : Z) (junk : list word).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (thr + 208 + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (Z.shiftr maxc 1).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (usp + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (sb + c * 4294967296).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size c).
  #[warnings="-notation-for-abbreviation"] Local Notation nc := ((mu - au) / class_size c).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (uG - 64).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= usp - 1024.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis MXR : 2 <= maxc <= 16 /\ maxc = 2 * k.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis RIR : kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis SEP_rs : ri + 4096 <= sb \/ sb + 2^37 <= ri.
  Hypothesis NF : 0 <= nf < k.
  (* [comment removed for export] *)
  Hypothesis AU : 0 <= au <= mu /\ mu mod kUserMap = 0 /\ au mod class_size c = 0 /\ au + (k - nf) * class_size c <= mu /\ mu - au < 9 * class_size c + kUserMap.
  Hypothesis CAP : mu <= 3750000000.   (* [comment removed for export] *)
  Hypothesis MFA : 0 <= mfa <= 469762048 (* [comment removed for export] *) /\ mfa mod kFreeArrayMapSize = 0.
  Hypothesis LJ : length junk = Z.to_nat nc.
  (* [comment removed for export] *)
  Hypothesis CPMH : ro_cells rsegs m 0xb1590 [C1 (Z_to_bv 8 0)].
  Hypothesis CPSC1 : ro_cells rsegs m 0xa8b50 [C8 (wz PSC)].
  Hypothesis CPSC2 : ro_cells rsegs m PSC [C8 (wz 4096)].
  Hypothesis CCF1 : ro_cells rsegs m 0xa8b60 [C8 (wz CF)].
  Hypothesis CCF2 : ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)].
  (* [comment removed for export] *)
  Hypothesis RNF : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis RMFA : rw_cells rsegs m (R + 24) [C8 (wz mfa)].
  Hypothesis RAU4 : rw_cells rsegs m (R + 32) [C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis REX : exists ex, rw_cells rsegs m (R + 68) [C1 ex].
  Hypothesis FRP : rw_cells rsegs m (uG + -64) (pop_frame (wz k) (wz (E + 16)) (wz (free_array_of sb c)) (wz 2305843009213693952) a0g (wz 0xb1558) (wz R) (wz gfa_popret)).
  Hypothesis FAJ : u32arr rsegs m (free_array_of sb c + 4 * nf) junk.

  (* [comment removed for export] *)
  Definition pop_grow_post (mfa' : Z) (W : list (Z * Z)) (X : (word -> option byte) -> Prop) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      st = MS (mkR (wz gfa_popret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1558) (wz 1) a1' a2' a3' a4' a5' a6' a7'
                   a0g (wz 2305843009213693952) (wz (free_array_of sb c)) (wz (E + 16)) (wz k)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3' t4' t5' t6')
              F (ret_pc (wz gfa_popret)) fc None m' (seg_rom rsegs)
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo uG
      /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf + nc))]
      /\ rw_cells rsegs m' (R + 24) [C8 (wz mfa')]
      /\ rw_cells rsegs m' (R + 32) [C8 (wz (au + nc * size)); C8 (wz 0); C8 (wz mu); C8 (wz 0)]
      /\ rw_cells rsegs m' (R + 68) [C1 (Z_to_bv 8 0)]
      /\ u32arr rsegs m' (free_array_of sb c + 4 * nf) (carved au size nc)
      /\ X m'.

  Definition pop_sC_W : list (Z * Z) :=
    [(uG - 112, uG); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69); (free_array_of sb c + 4 * nf, free_array_of sb c + 4 * nf + 4 * nc)].

  #[using="FAJ FRP REX RAU4 RMFA RNF LJ MFA CAP AU NF SEP_rs SBAL SBR RIR THR MXR CR SPH SPA LO ST MI junk Clg"] Lemma pop_sC_fast : 4 * (nf + nc) <= mfa ->
    evt rsegs (pop_grow_post mfa pop_sC_W (fun _ => True))
        (MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + nc)) (wz 0xb1558) (wz R) (wz rb) (wz (nf + nc)) a4 a5 a6 a7
                 (wz rb) (wz nc) (wz (mu - au)) (wz size) s6 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3 t4 t5 t6)
            F (wz efas_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros FAST.
    pose proof alloc_ceiling_val as CV. pose proof (class_size_range c CR) as CSR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof THR as [THRo THRc]. pose proof (aobj_facts _ _ THRo) as THF.
    unfold PSC, CF in *.
    assert (NCR : k - nf <= nc < 9 + 8192).
    { destruct AU as (A1 & A2 & A3 & A4 & A5). unfold kUserMap in A5. unfold kMaxSize in CSR.
      split; [apply Z.div_le_lower_bound; clear - A1 A4 CSR; lia| apply Z.div_lt_upper_bound; [clear - CSR; lia|]].
      clear - A5 CSR. nia. }
    (* [comment removed for export] *)
      eapply evt_cut; [eapply (efas_fast_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ a4 a5 a6 a7 _ _ _ _ s6 _ _ _ _ _ t3 t4 t5 t6 F fc m lo R (nf + nc) mfa)|].
      all: try eassumption. all: try reflexivity.
      all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
      all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF NCR MFA ST; unfold kHighMemBeg in *; first [lia | kcellz]).
      intros ms1 PO. destruct_exs PO. (first [ dand5 PO as -> MU1 WM1 MI1 ST1 | destruct PO as (-> & MU1 & WM1 & MI1 & ST1) ]). rewrite ?unsigned_lit in MU1, ST1 by (clear - CV LO LO0 SPH; lia).
      replace (ret_pc (wz pop_efasret)) with (wz pop_efasret : word) by (symmetry; apply ret_pc_even; [unfold pop_efasret; lia| reflexivity]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      destruct REX as [ex REX0]. xfer RNF MU1 WM1. xfer RAU4 MU1 WM1. xfer REX0 MU1 WM1. xfer FRP MU1 WM1.
      assert (FAJ1 : u32arr rsegs m1 (free_array_of sb c + 4 * nf) junk).
      { apply (u32arr_transport rsegs _ m m1 _ _ FAJ MU1 WM1). cbn [disjoint_from]. rewrite LJ. unfold free_array_of.
        split; [| exact I]. clear - CV LO SBR CR NF NCR MXR. unfold kHighMemBeg in *. lia. }
      eapply evt_cut; [eapply (pop_carve_ok _ gp tp x x0 x1 _ _ _ _ _ _ _ s6 _ _ _ _ _ x9 x10 x11 x12 F fc m1 (uG) lo R sb c nf au (mu - au) 1 junk ex)|].
      all: try eassumption. all: try reflexivity.
      all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
      all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF NCR MFA AU CAP; unfold kHighMemBeg, kUserMap in *; lia).
      1: (clear - SPA; Z.div_mod_to_equations; lia).
      1: { destruct AU as (_ & _ & AM & _). apply (mod0_down _ (class_size c) 16); [| exact AM]. apply (Z.divide_trans _ 32); [exists 2; reflexivity|]. apply Znumtheory.Zmod_divide; [clear - CSR; lia| exact (class_size_mod32 c CR)]. }
      1: (clear - SEP_rs CR; lia).
      1: (replace (au + (mu - au)) with mu by lia; exact RAU4).
      intros ms2 PO. destruct_exs PO. (first [ dand9 PO as -> MU2 WM2 MI2 ST2 RNF2 RAU2 REX2 FA2 | destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & RNF2 & RAU2 & REX2 & FA2) ]). rewrite ?unsigned_lit in MU2, ST2 by (clear - CV LO LO0 SPH; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
      xfer RMFA MU1 WM1.
      apply (rw_cells_transport rsegs _ m1 _ _ _ RMFA) in MU2 as RMFA2; [| exact WM2| cbn [disjoint_from]; simpl_sizes; unfold free_array_of; clear - CV LO SBR RIR CR NF NCR SEP_rs MXR; unfold kHighMemBeg in *; lia].
      lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ ?r0 ?r1 ?r2 _ _ _ ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 _ _ _ _ _ _ _ _ _ _ ?u3 ?u4 ?u5 ?u6) _ _ _ _ ?mm _) =>
        apply evt_done; unfold pop_grow_post; exists r0, r1, r2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, mm end.
      split; [reflexivity|].
      split. { unfold pop_sC_W. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
      split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2|].
      split; [exact RNF2|]. split; [exact RMFA2|]. split; [replace mu with (au + (mu - au)) at 2 by lia; exact RAU2|]. split; [exact REX2|]. split; [exact FA2| exact I].
  Qed.

  (* [comment removed for export] *)
  Definition pop_sC_map_post : machine_state -> Prop := fun st =>
    let nm := round_up (4 * (nf + nc)) kFaMap in let fe := rb + kFreeArrayOffset + mfa in
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr scrM : list byte) (m' : word -> option byte),
      st = MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -48 + -128)) gp tp t0' t1' t2' (wz (nm - mfa)) (wz 1) (wz fe) (wz (nm - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz fe) (wz efas_name) (wz PSC) (wz size) s6 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs)
      /\ munch [(uG - 512, uG + -64)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (uG + -64 + -48 + -128)
      /\ rw_cells rsegs m' (uG + -64 + -48) (efas_frame scr (wz nc) (wz rb) (wz (nf + nc)) (wz R) (wz pop_efasret))
      /\ rw_cells rsegs m' (uG + -64 + -48 + -128) (mapcb_frame scrM (wz (mu - au)) (wz R) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)).

  #[using="RMFA CCF2 CCF1 CPSC2 CPSC1 CPMH LJ MFA AU NF SBAL SBR RIR THR MXR CR SPH LO ST MI junk maxc thr Clg"] Lemma pop_sC_map : mfa < 4 * (nf + nc) ->
    evt rsegs pop_sC_map_post
        (MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + nc)) (wz 0xb1558) (wz R) (wz rb) (wz (nf + nc)) a4 a5 a6 a7
                 (wz rb) (wz nc) (wz (mu - au)) (wz size) s6 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3 t4 t5 t6)
            F (wz efas_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros NEEDMAP.
    pose proof alloc_ceiling_val as CV. pose proof (class_size_range c CR) as CSR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof THR as [THRo THRc]. pose proof (aobj_facts _ _ THRo) as THF.
    unfold PSC, CF in *.
    assert (NCR : k - nf <= nc < 9 + 8192).
    { destruct AU as (A1 & A2 & A3 & A4 & A5). unfold kUserMap in A5. unfold kMaxSize in CSR.
      split; [apply Z.div_le_lower_bound; clear - A1 A4 CSR; lia| apply Z.div_lt_upper_bound; [clear - CSR; lia|]].
      clear - A5 CSR. nia. }
    eapply (efas_map_pre_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ a4 a5 a6 a7 _ _ _ _ s6 _ _ _ _ _ t3 t4 t5 t6 F fc m lo R rb (nf + nc) mfa).
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF NCR MFA ST; unfold kHighMemBeg, kFreeArrayOffset in *; first [lia | kcellz]).
    intros m1 scr FRE MU1 WM1 MI1 ST1. rewrite ?unsigned_lit in FRE, MU1, ST1 by (clear - CV LO LO0 SPH; lia).
    set (nm := round_up (4 * (nf + nc)) kFaMap) in *.
    assert (NM : 4 * (nf + nc) <= nm < 4 * (nf + nc) + 262144 /\ nm mod 262144 = 0) by (subst nm; unfold kFaMap; apply roundup_famap_range; clear - NF NCR MXR; lia).
    xfer CPSC1 MU1 WM1. xfer CPSC2 MU1 WM1. xfer CCF1 MU1 WM1. xfer CCF2 MU1 WM1.
    eapply (map_pre_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ _ _ a6 a7 _ _ _ _ s6 _ _ _ _ _ t3 t4 t5 t6 F fc m1 lo (rb + kFreeArrayOffset + mfa) (nm - mfa) efas_name).
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF NCR MFA ST1 NM NEEDMAP; unfold kHighMemBeg, kFreeArrayOffset, efas_name in *; first [lia | kcellz]).
    1: { destruct NM as [_ N2]. destruct MFA as [_ M2]. unfold kFreeArrayMapSize in M2.
         replace (nm - mfa) with (nm + (-1) * mfa) by lia. apply mod_add_lit; [lia| apply (mod0_down _ 262144 4096); [exists 64; reflexivity| exact N2]|].
         apply Znumtheory.Zdivide_mod. apply Z.divide_mul_r. apply (Z.divide_trans _ 262144); [exists 64; reflexivity| apply Znumtheory.Zmod_divide; [lia| exact M2]]. }
    1: { destruct MFA as [_ M2]. unfold kFreeArrayMapSize in M2. unfold kFreeArrayOffset.
         apply mod_add_lit; [lia| apply mod_add_lit; [lia| apply mod_add_lit; [lia| exact SBAL| apply Znumtheory.Zdivide_mod; exists (c * 1048576); lia]| reflexivity]| apply (mod0_down _ 262144 4096); [exists 64; reflexivity| exact M2]]. }
    intros t0c t1c t2c a6c t3c t4c t5c t6c scrM m2 FRM MU2 WM2 MI2 ST2. rewrite ?unsigned_lit in FRM, MU2, ST2 by (clear - CV LO LO0 SPH; lia). xfer FRE MU2 WM2.
    unfold pop_sC_map_post. cbv zeta. fold nm. exists t0c, t1c, t2c, a6c, t3c, t4c, t5c, t6c, scr, scrM, m2.
    split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FRE| exact FRM].
  Qed.
End SegC.

