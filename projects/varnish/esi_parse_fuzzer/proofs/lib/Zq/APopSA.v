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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
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

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section SegA.
Context {Clg : Ceiling}.
  Variables (gp tp t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (s2v s10v s11v : word).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (usp lo thr c maxc sb ri nf au mu mfa : Z).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (thr + 208 + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation k := (Z.shiftr maxc 1).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (usp + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (sb + c * 4294967296).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (usp + -128 + -48 + -32 - 128).
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
  Hypothesis NF : 0 <= nf < k.
  Hypothesis AU : 0 <= au <= mu /\ mu mod kUserMap = 0 /\ au mod class_size c = 0.
  Hypothesis CAP : mu <= 3682891136 /\ au <= 3615782272.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
  Hypothesis CREL : ro_cells rsegs m 0xb1580 [C4 (wz 4294967295)].
  Hypothesis CPMH : ro_cells rsegs m 0xb1590 [C1 (Z_to_bv 8 0)].
  Hypothesis CPSC1 : ro_cells rsegs m 0xa8b50 [C8 (wz PSC)].
  Hypothesis CPSC2 : ro_cells rsegs m PSC [C8 (wz 4096)].
  Hypothesis CCF1 : ro_cells rsegs m 0xa8b60 [C8 (wz CF)].
  Hypothesis CCF2 : ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)].
  (* [comment removed for export] *)
  Hypothesis RNF : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis RMFA : rw_cells rsegs m (R + 24) [C8 (wz mfa)].
  Hypothesis RAU : rw_cells rsegs m (R + 32) [C8 (wz au)].
  Hypothesis RMU : rw_cells rsegs m (R + 48) [C8 (wz mu)].
  Hypothesis RMM : rw_cells rsegs m (R + 56) [C8 (wz 0)].

  (* [comment removed for export] *)
  Definition pop_sA_map_post : machine_state -> Prop := fun st =>
    let ums := round_up (au + (k - nf) * class_size c - mu) kUserMap in
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr : list byte) (m' : word -> option byte),
      st = MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -128)) gp tp t0' t1' t2' (wz ums) (wz 1) (wz (rb + mu)) (wz ums) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz (rb + mu)) (wz pop_name) (wz PSC) (wz (class_size c)) (wz 0xb1558) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs)
      /\ munch [(uG - 464, uG)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (uG + -64 + -128)
      /\ rw_cells rsegs m' (uG + -64) (pop_frame (wz k) (wz (E + 16)) (wz (free_array_of sb c)) (wz 2305843009213693952) a0 (wz 0xb1558) (wz R) (wz gfa_popret))
      /\ rw_cells rsegs m' (uG + -64 + -128) (mapcb_frame scr (wz (rb + mu)) (wz ums) (wz rb) (rb + mu) ums (wz (C + 2560)) (wz R) (wz pop_mapret)).

  Lemma pop_sA_map : mu < au + (k - nf) * class_size c ->
    evt rsegs pop_sA_map_post
        (MS (mkR (wz refill_ret) (wz uG) gp tp t0 t1 t2 (wz R) (wz 0xb1558) a0 (wz (C + 2560)) (wz c) (wz (E + 16)) (wz k) a5 a6 a7
                 s2v (wz 2305843009213693952) (wz (free_array_of sb c)) (wz 1099511627776) (wz 1152921504607895551)
                 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3 t4 t5 t6)
            F (wz gfa_locked) fc None m (seg_rom rsegs)).
  Proof.
    intros NOFIT.
    pose proof alloc_ceiling_val as CV. pose proof (class_size_range c CR) as CSR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof THR as [THRo THRc]. pose proof (aobj_facts _ _ THRo) as THF.
    unfold PSC, CF in *.
    (* [comment removed for export] *)
    eapply (gfa_popcall_ok _ gp tp t0 t1 t2 a0 _ a5 a6 a7 _ _ _ t3 t4 t5 t6 _ _ _ _ _ _ _ F fc m (usp + -128 + -48 + -32) R 0xb1558 c nf k (E + 16)).
    all: try eassumption.
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF; unfold kHighMemBeg in *; lia).
    intros a5'.
    (* [comment removed for export] *)
    eapply (pop_map_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ _ a6 a7 _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 F fc m lo R sb c (k - nf) (C + 2560) nf au mu).
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF AU ST; unfold kHighMemBeg in *; first [lia | kcellz]).
    1: { unfold kUserMap. pose proof (roundup_famap_range (au + (k - nf) * class_size c - mu) ltac:(clear - NOFIT; lia)) as [U _].
         assert (KS : (k - nf) * class_size c <= 8 * 65536) by (clear - CSR NF MXR; unfold kMaxSize in CSR; nia).
         clear - U CAP KS AU NOFIT. lia. }
    intros a5b a6b m1 FRP MU1 WM1 MI1 ST1.
    set (ums := round_up (au + (k - nf) * class_size c - mu) kUserMap) in *.
    assert (UMS : au + (k - nf) * class_size c - mu <= ums < au + (k - nf) * class_size c - mu + 262144 /\ ums mod 262144 = 0).
    { subst ums. unfold kUserMap. apply roundup_famap_range. clear - NOFIT; lia. }
    assert (KS : (k - nf) * class_size c <= 8 * 65536) by (clear - CSR NF MXR; unfold kMaxSize in CSR; nia).
    xfer CPSC1 MU1 WM1. xfer CPSC2 MU1 WM1. xfer CCF1 MU1 WM1. xfer CCF2 MU1 WM1.
    change ARtSb8o.mapcb_entry with ANodeA6.mapcb_entry.
    eapply (map_pre_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ _ _ a6b a7 _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 F fc m1 lo (rb + mu) ums pop_name).
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF AU ST1 UMS KS CAP NOFIT; unfold kHighMemBeg, pop_name in *; first [lia | kcellz]).
    1: { destruct UMS as [_ U2]. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 262144); [exists 64; reflexivity| apply Znumtheory.Zmod_divide; [lia| exact U2]]. }
    1: { destruct AU as (_ & MUM & _). unfold kUserMap in MUM. apply mod_add_lit; [lia| apply mod_add_lit; [lia| exact SBAL| apply Znumtheory.Zdivide_mod; exists (c * 1048576); lia]| apply (mod0_down _ 262144 4096); [exists 64; reflexivity| exact MUM]]. }
    intros t0c t1c t2c a6c t3c t4c t5c t6c scr m2 FRM MU2 WM2 MI2 ST2.
    xfer FRP MU2 WM2.
    unfold pop_sA_map_post. cbv zeta. fold ums. first [ hotw_ex10 t0c t1c t2c a6c t3c t4c t5c t6c scr m2 | exists t0c, t1c, t2c, a6c, t3c, t4c, t5c, t6c, scr, m2 ].
    split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FRP| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Definition pop_sA_fit_post : machine_state -> Prop := fun st =>
    let nc := (mu - au) / class_size c in
    exists (a5' a6' : word) (m' : word -> option byte),
      st = MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + nc)) (wz 0xb1558) (wz R) (wz rb) (wz (nf + nc)) (wz (k - nf)) a5' a6' a7
                   (wz rb) (wz nc) (wz (mu - au)) (wz (class_size c)) (wz k) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3 t4 t5 t6)
              F (wz efas_entry) fc None m' (seg_rom rsegs)
      /\ munch [(uG - 64, uG)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (uG - 64)
      /\ rw_cells rsegs m' (uG + -64) (pop_frame (wz k) (wz (E + 16)) (wz (free_array_of sb c)) (wz 2305843009213693952) a0 (wz 0xb1558) (wz R) (wz gfa_popret)).

  Lemma pop_sA_fit : au + (k - nf) * class_size c <= mu ->
    evt rsegs pop_sA_fit_post
        (MS (mkR (wz refill_ret) (wz uG) gp tp t0 t1 t2 (wz R) (wz 0xb1558) a0 (wz (C + 2560)) (wz c) (wz (E + 16)) (wz k) a5 a6 a7
                 s2v (wz 2305843009213693952) (wz (free_array_of sb c)) (wz 1099511627776) (wz 1152921504607895551)
                 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v t3 t4 t5 t6)
            F (wz gfa_locked) fc None m (seg_rom rsegs)).
  Proof.
    intros FIT.
    pose proof alloc_ceiling_val as CV. pose proof (class_size_range c CR) as CSR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof THR as [THRo THRc]. pose proof (aobj_facts _ _ THRo) as THF.
    unfold PSC, CF in *.
    eapply (gfa_popcall_ok _ gp tp t0 t1 t2 a0 _ a5 a6 a7 _ _ _ t3 t4 t5 t6 _ _ _ _ _ _ _ F fc m (usp + -128 + -48 + -32) R 0xb1558 c nf k (E + 16)).
    all: try eassumption.
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF; unfold kHighMemBeg in *; lia).
    intros a5'.
    eapply (pop_fit_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ _ a6 a7 _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 F fc m lo R sb c (k - nf) (C + 2560) nf au mu).
    all: try eassumption. all: try reflexivity.
    all: rewrite ?unsigned_lit by (clear - CV LO LO0 SPH; lia).
    all: try (clear - CV CSR LO0 LO SPH CR MXR THF RIR SBR NF AU ST CAP FIT; unfold kHighMemBeg in *; first [lia | kcellz]).
    intros a5b a6b m1 FRP MU1 WM1 MI1 ST1. rewrite ?unsigned_lit in FRP, MU1, ST1 by (clear - CV LO LO0 SPH; lia).
    apply evt_done. unfold pop_sA_fit_post. first [ hotw_ex3 a5b a6b m1 | exists a5b, a6b, m1 ].
    split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact FRP].
  Qed.
End SegA.
