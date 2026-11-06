(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr ZBridge SysStep ITree.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RBand.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition OPNEW : Z := 0x78ff8.
Definition OPNEW_RA : Z := 0x79014.       (* [comment removed for export] *)
Definition OPNEW_FAIL : Z := 0x79018.     (* [comment removed for export] *)
Definition OPNEW_ARR : Z := 0x79068.      (* [comment removed for export] *)
Definition OPDEL : Z := 0x58f84.          (* [comment removed for export] *)
Definition OPDEL_SZ : Z := 0x58f88.       (* [comment removed for export] *)

Definition opnew_size (n : Z) : Z := if n =? 0 then 1 else n.

(* [comment removed for export] *)
Lemma impl_mono_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R)
    (Q Q' : R -> machine_state -> Prop) ms,
  impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> impl segs atn t Q' ms.
Proof. try hcb. try hsb.
  intros node segs atn R t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; [apply Hk| exact HQ].
Qed.

Lemma implM_mono_evt : forall {A} (c : M PState A) s (Q Q' : A -> PState -> machine_state -> Prop) ms,
  implM rsegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt rsegs (Q' a s') ms') -> implM rsegs c s Q' ms.
Proof. try hcb. try hsb.
  intros A c s Q Q' ms H HQ. unfold implM in *. eapply impl_mono_evt; [exact H|].
  intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I|]. apply HQ.
Qed.

Section OpNew.
  Context (RHEAP : PState -> list block -> mem -> Prop)
          (rauxv_ok : mem -> Z -> Prop)
          (raddr_exposed : PState -> Z -> Prop)
          (lb_remove : bptr -> list block -> list block).
  Hypothesis HM : rmalloc_stmt RHEAP rauxv_ok raddr_exposed.
  Hypothesis HF : rfree_stmt RHEAP rauxv_ok lb_remove.
  Hypothesis RHEAP_frame : RHEAP_frame_stmt RHEAP.
  Hypothesis rauxv_frame : rauxv_ok_frame_stmt rauxv_ok.
  Hypothesis RHEAP_blocks : RHEAP_block_range_stmt RHEAP.

  Definition opnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (n1 lo B : Z) (m : mem)
      (r : option bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' =>
      match r with
      | Some p => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) A junk,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom rsegs)
          /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
          /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
          /\ rauxv_ok m' B
          /\ rheap_pres LB (bv_unsigned sp) m m'
          /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
          /\ rblock_range A n1
          /\ RHEAP s' ((p, A, n1) :: LB) m'
          /\ rw_cells rsegs m' A [CB (Z.to_nat n1) junk]
          /\ (raddr_exposed s n1 -> A = ptr_addr s' p)
      | None => (* [comment removed for export] *)
          exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
          ms' = MS (mkR (Z_to_bv 64 OPNEW_RA) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 n1) s1
                        (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 OPNEW_FAIL) fc None m' (seg_rom rsegs)
          /\ mem_inv rsegs m' /\ RHEAP s' LB m'
          /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
          /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      end.

  Definition opnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (n lo B : Z) (errv : word),
    RHEAP s LB m ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 - RMALLOC_STACK ->
    rw_cells rsegs m (errno_addr tp) [C4 errv] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
    implM rsegs (raw_malloc (opnew_size n)) s
          (opnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (opnew_size n) lo B m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 OPNEW) fc None m (seg_rom rsegs)).

  Lemma opnew_spec : opnew_stmt.
  Proof. try hcb. try hsb.
    intros until errv. intros HP AUX SPB ST CEIL LO ERR MI TP A0 HN.
    unfold RMALLOC_STACK in LO. pose proof CEIL as CEIL'. hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CEIL.
    subst tp. replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO in ERR by (unfold RATP, RERRNO; rewrite unsigned_lit; lia).
    unfold RERRNO in ERR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold implM. iprefix. unfold OPNEW. subst a0.
    carve_frame 16%nat ST.
    step. step. step. zstep. zstep. zstep. step.
    replace (n + Z.b2z (n <? 1)) with (opnew_size n) by (unfold opnew_size; destruct (Z.eqb_spec n 0); destruct (Z.ltb_spec n 1); cbn; lia).
    apply evt_done.
    set (sp1 := Z_to_bv 64 (bv_unsigned sp + -16)).
    assert (SP1 : bv_unsigned sp1 = bv_unsigned sp + -16) by (subst sp1; apply unsigned_lit; lia).
    eapply implM_mono_evt.
    { unfold rmalloc_stmt in HM.
      eapply HM with (s := s) (LB := LB) (n := opnew_size n) (lo := lo) (B := B); rewrite ?SP1.
      all: try solve [ unfold RMALLOC_STACK; lia | reflexivity | exact MI | exact ST | exact ERR
                     | unfold opnew_size; destruct (Z.eqb_spec n 0); lia ].
      - eapply RHEAP_frame; [exact HP| exact MU| exact WM|]. constructor; [|constructor]. left. cbn. lia.
      - eapply rauxv_frame; [exact AUX| exact MU| exact WM|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL. lia. }
    cbv beta. intros r s_2 ms2 PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HPRES & EFA & ESO & RES).
    rewrite SP1 in ST2, HPRES. subst sp1.
    replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with 0x925ac in ERR2 by (unfold RATP; rewrite unsigned_lit; lia).
    replace (ret_pc (Z_to_bv 64 0x79014)) with (Z_to_bv 64 0x79014) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    apply (rheap_pres_rw_cells _ _ _ _ _ _ HPRES) in FR; [| left; lia].
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= hceil).
    { intros b Hb. destruct (RHEAP_blocks _ _ _ b HP Hb) as (_ & _ & _ & H4 & _). exact H4. }
    assert (PRES : rheap_pres LB (bv_unsigned sp) m m2).
    { eapply rheap_pres_trans.
      - eapply rheap_pres_of_munch; [exact MU| exact WM| | exact HB]. constructor; [|constructor]. cbn. lia.
      - eapply rheap_pres_weaken; [exact HPRES| lia| auto]. }
    clear MU WM MI HPRES.
    destruct r as [p|].
    - (* [comment removed for export] *)
      destruct RES as (A & bj & -> & BR & HEAP2 & BLK & EXP).
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by (hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in BR4; lia). lia. }
      clear K. step. step. step. step.
      release_frame FR ST2 (bv_unsigned sp).
      apply evt_done. cbn [opnew_post].
      do 15 eexists. exists errv2, A, bj.
      split; [reflexivity|].
      repeat match goal with |- _ /\ _ => split end; try assumption.
    - (* [comment removed for export] *)
      destruct RES as [-> HEAP2].
      step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. }
      clear K. apply evt_done. cbn [opnew_post].
      do 15 eexists. exists errv2.
      split; [reflexivity|].
      repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma opnew_spec_pos :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (n lo B : Z) (errv : word),
    RHEAP s LB m ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 - RMALLOC_STACK ->
    rw_cells rsegs m (errno_addr tp) [C4 errv] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 n -> 1 <= n < 2^32 ->
    implM rsegs (raw_malloc n) s
          (opnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 OPNEW) fc None m (seg_rom rsegs)).
  Proof. try hcb. try hsb.
    intros until errv. intros HP AUX SPB ST CEIL LO ERR MI TP A0 HN.
    pose proof (opnew_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc m s LB n lo B errv HP AUX SPB ST CEIL LO ERR MI TP A0 ltac:(lia)) as H.
    unfold opnew_size in H. replace (n =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia). exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma opnew_arr_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (n lo B : Z) (errv : word),
    RHEAP s LB m ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 - RMALLOC_STACK ->
    rw_cells rsegs m (errno_addr tp) [C4 errv] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
    implM rsegs (raw_malloc (opnew_size n)) s
          (opnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (opnew_size n) lo B m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 OPNEW_ARR) fc None m (seg_rom rsegs)).
  Proof. try hcb. try hsb.
    intros until errv. intros HP AUX SPB ST CEIL LO ERR MI TP A0 HN.
    unfold implM. iprefix. unfold OPNEW_ARR. step. apply evt_done.
    pose proof (opnew_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc m s LB n lo B errv HP AUX SPB ST CEIL LO ERR MI TP A0 HN) as H.
    unfold implM, OPNEW in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Definition opdel_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
    RHEAP s LB m -> In (p, A, n) LB ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
    rw_cells rsegs m (errno_addr tp) [C4 errv] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 A ->
    implM rsegs (raw_free p) s
          (rfree_post RHEAP rauxv_ok lb_remove ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

  Lemma opdel_spec : opdel_stmt_at OPDEL.
  Proof. try hcb. try hsb.
    intros until errv. intros HP IN AUX SPB ST CEIL LO ERR MI TP A0.
    unfold implM. iprefix. unfold OPDEL. step. apply evt_done.
    unfold rfree_stmt, implM in HF. eapply HF; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma opdel_sz_spec : opdel_stmt_at OPDEL_SZ.
  Proof. ltac2:(KReplay.runc [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.PState); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr); constr:(@Corelib.Numbers.BinNums.Z); constr:(RHEAP); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(rauxv_ok); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.stk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RFREE_STACK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RATP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.SysStep.impl_from_evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Nodes.node); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Nodes.at_node); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.ITree.Exc.exc); constr:(@Corelib.Init.Datatypes.unit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.raw_free); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.ITree.epost); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.rfree_post); constr:(lb_remove); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.mkR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.F_opnew.HCW.OPDEL_SZ); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_evt_step); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.ITree.impl); constr:(@stdpp.bitvector.definitions.BV); constr:(@stdpp.bitvector.definitions.Z_to_bv_obligation_1); constr:(@LinuxProcessSemantics.Riscv.Instr.Jal); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.Some); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall); constr:(@LinuxProcessSemantics.Riscv.Instr.instr); constr:(@LinuxProcessSemantics.Riscv.DecodeC.decode_any); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_cong1); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@LinuxProcessSemantics.Riscv.Prelude.sext); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.StepFast.sf_btgt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt_done); constr:(HF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Monad.implM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.F_opnew.HCW.OpNew.opdel_stmt_at)|] [|@p; @ms'; @y; @A0; @TP; @MI; @ERR; @LO; @CEIL; @ST; @SPB; @AUX; @IN; @HP; @errv; @B; @lo; @n; @A; @LB; @s; @m; @fc; @F; @t6; @t5; @t4; @t3; @s11; @s10; @s9; @s8; @s7; @s6; @s5; @s4; @s3; @s2; @a7; @a6; @a5; @a4; @a3; @a2; @a1; @a0; @s1; @s0; @t2; @t1; @t0; @tp; @gp; @sp; @ra; @HCANB; @HSECB; @HCEILB|] "#(L#Z$V#~#v#8#6#7#Q#P#5#W#V#F#E#D#C#B#A#@#?#^#*#O#3#R#r###U#G#>#9#g#h#w#)#{#N#/#1#M$4#4#0#T#H#=#:#+#u#'#2$5$7$8#X#S#L#K#J#I#<#;$J$K$M#d#j#n#(#-#&$)$6$<$=$1$A$E$G$I$L$N$R$Q$S$O#.$@#]#e#f#i#k#l#m#p#s#t#x#}$#$$$'$&$*$+$($%$,$/$2$3$9$:$>$?#Y$B$P$U#,#%#$$T$V$0$W#q$X#b#c#a$-#`$F$.$D$C#o#y#z#|$;$H#_3$F$$G$$H$$I&$J%$K%$L%$M%$N&$O$$P%$Q'$R%$S*$T%$U%USiS%$SR$#$#$#$#$#$#$#$#$#$#$#$#$###$#$#$#$#$#$#$#$###############################################%#USjS%'$#$s#&$#$#$#$#$#$#$#$###############################################%#'s#%#2s#%#m#s#W#USkS0USlS0'S1##SR%##$########%#VSm)#VSS-#2-#m#0#USnS0USoS0'S1#VSS$)2$#m#'#,.UST#$6,#VSp#%,4UST#USqSrWS2S&S3S@-SAD-#D.SADS3SU.%D#SBWSs%#S&VS4SVSW/1S5'#SB/3S'XStCS6S3#'s#PS&/6HVSu#Sv'S@#/9I#8##$#####USw#VSx)#USyS&USzSXWS{SX$#XS|CSC&#VS}CS()s#&S~&s#&S)#)s#(S7&s#(S8#UT#C-S9S*UT$#WSDS%S(JWT%S9S*S+WT&S9S*S+i#ASES2S4SFSGKLS,HIS-MNOPQRS#S$S.S/EFJS:S7S;S6G$#j#$(#VSY)#i#BSZKLS,S<SHS)HIS'S5S8SISJSKSLS=S-MNOPQRS#S$S.S>SMSNS?S/)s#4S[UT's#4UT(C0&E%G$F#WSDS%S:Fi#ASES2S4SFT)SGKLS)HS=S-MNOPQRS#S$S?S/GFJSCS7S;E-,j#$1#VSY2#[T*S\C42&#S+j#%S]#$s#<####$#######$#####$###########%##SR$#$#######$#$#$#$#$#######$#######%##($#####%#$SR####$#$#$#$#$#$###$#$###$#$#######%#)s#z;#s%%$#$#$#$#$#$#$#$#$###########$#$###$#$#$#$#%#*s$1#+s$2$#%-*s$6#+s$7S1#$s$#,##s$s##%#*&#+'$#VS^*#%s$S#s#[$#$#$#####%#)s$Ks#C0s#wE#Gs#uFs#tUS_s$G1s$H9($#VS`Cs#4&&#%m$%#(SOSPUSa?&SO#SPm$%#-SQDUS_#.SQD981%#(%#USbs#'&'#%m$%#i#BSZSGKLS,S<SHS)HIS'S5S8SISJSKSLS=S-MNOPQRS#S$S.S>SMSNS?0#S/S+Es$-Gs$,VT+S]#j#&s$a#WScs#)s$cs#$WSds$ds#H#(Ds#]YSes#cs#^s#,s#'#XSf'%>##s%u$#$#########$#########$#$#$#############$#$###$#$#$#$#%#$SR$###$###$###$###$#########$#$#$#############$#$###$#$#$#$#%#%+$?$#$###$###$###$#####%#*s%P0+s%Q1#%s#9*s%U2+s%VS1#$s#N$###$#$###########%#*s$+3+s$,4#VS^0##s&v$#################$#$#$#$#$#####%#)s%zs$_0s%JE#Gs%HFs%G1s%vs#((s$2#VS`Cs$5&s$4#%m$%#USas#-&SO#SPm$s$2#.SQD?s$C1s$0#(s$0#USbs#3&s$2#%m$%#WScs$Ps&.s#&WSds&/s$B#(Ds$qYSes%)s$rs$Ss#)#XSfs$.%6#i#XT,KLS,S<SHS)HIS'S5S8SISJSKSLS=S-MNOPQRS#S$S.S>SMSNS?S/EGFJS:S(SCS7S;S6SgSVT-S@S&S3SUSBSWT.T/S+XT0Cs%U7#fShCs%Vs%`Es$HGs%^Fs%]s#=s#,s$P830*%#fShCs%Ws%aEs$vGs%_Fs%^s$]s$Rs$Qs$Hs$Bs$>s$6s$-#WT1Cs%Xs%^m#$#\T2S\Cs%ms%ks%js%es%`#VSDS%S(i#?SES2S4SFKLS,S<IS'MNOPQRS#S$S.S>EGJS:S(S;S6SgF[T3S*CS9$J#s%cm#&#j#'s%s#j#(s%v#j#)s%y#j#*s%{#j#+s&,#j#,s&0#j#-s&2#j#.s&5#j#/s&8#j#0s&:#j#1s&@#j#2s&H#j#3D#j#4D#j#5D#j#6D#j#$SA#j#7s&H#j#8S*#j#9T4#j#:s&L#j#;s&O#j#<s&S#j#=s&T#j#>s&U#j#?s&V#j#@s&W#j#As&X#j#Bs&Y#j#Cs&Z#j#Ds&[#j#Es&\#j#Fs&]#j#Gs&^#j#Hs&_#j#Is&`#j#Js&a#j#Ks&b#j#Ls&c#j#Ms&d#j#Ns&e#j#Os&f#j#Ps&g#j#Qs&h#j#Rs&i#j#Ss&j#j#Ts&k#j#Us&l#j#Vs&m#j#Ws&n#j#Xs&o#j#Ys&p#j#Zs&q#UT5S[m#$#l#[s&vs&w#l#\s&}s&~#l#]s'1s'2##"). Qed.

  (* [comment removed for export] *)
  Definition opdel_null_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
    a0 = Z_to_bv 64 0 ->
    evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

  Lemma opdel_null_spec : opdel_null_stmt_at OPDEL.
  Proof. try hcb. try hsb. intros until m. intros ->. unfold OPDEL. step. step. step. if_true. step. apply evt_done. reflexivity. Qed.

  Lemma opdel_sz_null_spec : opdel_null_stmt_at OPDEL_SZ.
  Proof. try hcb. try hsb. intros until m. intros ->. unfold OPDEL_SZ. step. step. step. step. if_true. step. apply evt_done. reflexivity. Qed.
End OpNew.

End HCW.

