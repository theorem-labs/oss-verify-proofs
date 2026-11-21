(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require PropExec StdModel ShapeAlg Spec S9TargetPre S9World S9StdioDefs S9ExitBase S9Exit
  RefMemcpyLib Frame Hoare SymRun ZlibStmtBase S9LibStmt S9Atexit DrawDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PlainS9 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP F_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift2 MrRoom MrRulesS9.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.MrP9 Require Import S9HeapPre S9HBase S9HConv S9SoDefs S9PrintfFirst S9PrintfNext S9TrTail S9TrInv S9U2Seg S9U2Lib.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.MrP9 Require Export S9SoOk.
From Ltac2 Require Ltac2.
Module TrrKeep.
Import Ltac2.Ltac2.
Ltac2 is_section_hyp (h : ident) : bool :=
  match Env.get [h] with
  | Some r => match r with Std.VarRef _ => true | _ => false end
  | None => false
  end.
Ltac2 keep_section () : unit :=
  Control.enter (fun () =>
    let sec := List.filter (fun (p : ident * constr option * constr) => let (h, _, _) := p in is_section_hyp h) (Control.hyps ()) in
    Std.keep (List.map (fun (p : ident * constr option * constr) => let (h, _, _) := p in h) sec)).
End TrrKeep.
Ltac trr_keep_section := idtac; ltac2:(TrrKeep.keep_section ()).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module OAX := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.S9Atexit.

Lemma bptr_eqb_refl' : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true -> p = q.
Proof.
  intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
  rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
  - rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
  - exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
    + apply H. left. apply bptr_eqb_eq in E. exact E.
    + apply N. cbn [negb]. exact I.
Qed.

Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
  intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons, bptr_eqb_refl'. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
  apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.


Lemma keeps_cs_kept : forall R R' : bvmap 5 word, RefMemcpyLib.keeps_cs R R' ->
  forall k, In k kept_regs -> reg_get R' (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k).
Proof.
  intros R R' H k Hk. unfold kept_regs in Hk. cbn [In] in Hk.
  assert (IN : forall r, In r RefMemcpyLib.callee_saved -> PropExec.getr R' r = PropExec.getr R r) by exact H.
  repeat (destruct Hk as [<-|Hk];
    [ lazymatch goal with |- reg_get _ (Z_to_bv 5 ?kk) = _ =>
        refine (IN (Z_to_bv 5 kk) _); unfold RefMemcpyLib.callee_saved; cbn [In];
        repeat (first [left; apply bv_eq; reflexivity | right]) end |]).
  destruct Hk.
Qed.

Definition memcpy_postv {RCa1 : RunCtx}  (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m' Src src.

Lemma memcpy_callv {RCa1 : RunCtx}  : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m Src src -> length src = Z.to_nat N -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N)%Z -> (Src + N < 2^64)%Z -> (Dst + N < 2^64)%Z -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20168) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  pose proof (bytes_at_bound _ _ _ _ BA) as B1. pose proof (rw_cells_bound _ _ _ _ DC) as B2. cbn [cells_size csize] in B2.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.

Lemma rdn_of_cells {RCa1 : RunCtx}  : forall (M : word -> option byte) A cs (k n : nat) a bs,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A cs -> (k + n <= length (cells_bytes cs))%nat -> a = wa (A + Z.of_nat k) ->
  map bv_unsigned (firstn n (skipn k (cells_bytes cs))) = map bv_unsigned bs ->
  PropExec.rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M a n = Some bs.
Proof.
  intros M A cs k n a bs RW LE -> E.
  rewrite (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M A (cells_bytes cs) k n (rw_cells_bytes_at _ _ _ _ RW) LE).
  f_equal. apply bytes_eq_unsigned. exact E.
Qed.

Ltac atx_rc m H k := eapply (rdn_of_cells m _ _ k _ _ _ H); [cbn; lia | apply bv_eq; reflexivity | vm_compute; reflexivity].
Lemma atx_R_of_cells {RCa1 : RunCtx}  : forall M : word -> option byte,
  OAX.atx_cellsA M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e64 [C1 (Z_to_bv 8 0)] -> OSD.atx_R M.
Proof.
  intros M [A B] C. unfold OAX.PATX, OAX.PATX_CALL, OAX.PAEF_GUARD in A, B.
  unfold OSD.atx_R.
  split; [atx_rc M A 16%nat|]. split; [atx_rc M A 8%nat|]. split; [atx_rc M A 4%nat|]. split; [atx_rc M A 24%nat|]. split; [atx_rc M A 32%nat|].
  split; [atx_rc M B 0%nat|]. atx_rc M C 0%nat.
Qed.

Section RUN.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis SP16 : sp0 mod 16 = 0.
Hypothesis ATOPE : ATOP = sp0 - 8388608.

Abbreviation T_end fs k code :=
  (ShapeAlg.t_emit (Spec.W 1 (Spec.zero_lines k)) (ShapeAlg.t_exit (Spec.exit_code code) fs)).

Lemma needlk_of_RHEAP : forall s LB M, RHEAP s LB M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M OAX.PNEEDLK [C1 (Z_to_bv 8 0)].
Proof. intros s LB M (st & LB0 & _ & _ & (_ & _ & (_ & NL & _) & _) & _). exact NL. Qed.

Lemma trun_epi_rz : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (M : word -> option byte) (mo : Model) (s : PState) (pb : bptr) (buf cap : Z) (fs : Fs.Fs) (k : nat) (rcv b1 tid lo : Z)
    (jt : list byte) (t7 t6 t4 t3 t2 t0 : word) (errv : word),
  x2 = Z_to_bv 64 (sp0 - 208) -> x4 = Z_to_bv 64 RATP -> x10 = Z_to_bv 64 rcv -> 0 <= b1 < 256 -> rcv = 0 \/ rcv = 2 ->
  RHEAP s [(pb, buf, cap)] M -> OWN [pb] (G_std fs) s mo ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208) -> ATOP <= lo -> lo <= sp0 - 208 - 8192 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 208) [CB 8 jt; C8 t7; C8 t6; C8 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)); C8 t4; C8 t3; C8 t2;
                                C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x14a40)] ->
  cli_inv sp0 M tid -> 1 <= tid <= 4194303 -> so_ok M k ->
  OAX.atx_cellsA M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e64 [C1 (Z_to_bv 8 0)] ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14ca0) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (T_end fs k (if b1 <? 128 then rcv else 0)).
Proof.
  intros until errv. intros -> -> -> B1 RCV HH HOWN ST ALO LO ERR MI FRT [AUX PR TIDC (junk & m7 & m6 & m5 & m4 & m3 & m2 & m1 & m0 & FRM)] TID SO AXA ICB.
  pose proof HOWN as [(L & _ & HKL & _) _].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  apply rz_evt; [exact Hh | exact Hl |].
  do 11 step. apply evt_done.
  release_frame FRT ST (sp0 - 128).
  eapply (main_tail_rz sp0 SP0 so_ok so_ok_exit so_ok_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            M mo s pb buf cap fs k rcv b1 tid lo junk m7 m6 m5 m4 m3 m2 m1 m0 errv);
    try eassumption; try reflexivity; try lia.
  - f_equal; lia.
  - apply atx_R_of_cells; assumption.
Qed.

Variables (pb : bptr) (buf cap : Z) (fs : Fs.Fs) (payl b1 tid lo : Z).
Hypothesis B1 : 0 <= b1 < 256.
Hypothesis TID : 1 <= tid <= 4194303.
Hypothesis ALO : ATOP <= lo.
Hypothesis LO : lo <= sp0 - 208 - 65536.
Hypothesis PAYL : 0 <= payl < 2 ^ 26.
Variable C7 : S9LibStmt.zlib_u2_contract_S9.

Definition LBT (own : option (bptr * Z)) : list block :=
  match own with None => [(pb, buf, cap)] | Some (q, D) => [(q, D, payl); (pb, buf, cap)] end.
Definition XT (own : option (bptr * Z)) : list bptr := match own with None => [pb] | Some (q, _) => [q; pb] end.
Definition dptr (own : option (bptr * Z)) : Z := match own with None => 0x32e70 | Some (_, D) => D end.
Definition oreg (own : option (bptr * Z)) : Z := match own with None => 0 | Some (_, D) => D end.

Record run_inv (cb : Z) (own : option (bptr * Z)) (M : word -> option byte) (s : PState) (mo : Model) : Prop := RUN_INV {
  ri_heap : RHEAP s (LBT own) M;
  ri_own  : OWN (XT own) (G_std fs) s mo;
  ri_data : match own with None => payl = 0 | Some (_, D) => exists src, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M D [CB (Z.to_nat payl) src] end;
  ri_stk  : stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208);
  ri_err  : exists errv : word, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv];
  ri_mi   : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M;
  ri_frt  : exists (jt : list byte) (t7 t6 t4 t3 t2 t0 : word),
            rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 208) [CB 8 jt; C8 t7; C8 t6; C8 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)); C8 t4; C8 t3; C8 t2;
                                          C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x14a40)];
  ri_cli  : cli_inv sp0 M tid;
  ri_atx  : OAX.atx_cellsA M;
  ri_icb  : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e64 [C1 (Z_to_bv 8 cb)]
}.

Lemma own_range : forall cb own M s mo, run_inv cb own M s mo ->
  match own with None => True | Some (_, D) => 0 < D /\ D mod 16 = 0 /\ D + payl <= ATOP /\ (D + payl <= 0x10000 \/ 0x94000 <= D) end.
Proof.
  intros cb [[q D]|] M s mo RI; [|exact I].
  pose proof (RHEAP_block_range_proof _ _ _ (q, D, payl) (ri_heap _ _ _ _ _ RI) ltac:(left; reflexivity)) as (H1 & H2 & H3 & H4 & H5).
  cbn in *. auto.
Qed.

Record run_invX (LBx : list block) (cb : Z) (own : option (bptr * Z)) (M : word -> option byte) (s : PState) (mo : Model) : Prop := RUN_INVX {
  rx_heap : RHEAP s (LBx ++ LBT own) M;
  rx_own  : OWN (map blk_id LBx ++ XT own) (G_std fs) s mo;
  rx_wr   : Forall (fun b : block => wr_at (run_segments psegs rc_inp rc_sp rc_mb) M (blk_addr b) (blk_size b)) LBx;
  rx_data : match own with None => payl = 0 | Some (_, D) => exists src, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M D [CB (Z.to_nat payl) src] end;
  rx_stk  : stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208);
  rx_err  : exists errv : word, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv];
  rx_mi   : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M;
  rx_frt  : exists (jt : list byte) (t7 t6 t4 t3 t2 t0 : word),
            rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 208) [CB 8 jt; C8 t7; C8 t6; C8 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)); C8 t4; C8 t3; C8 t2;
                                          C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x14a40)];
  rx_cli  : cli_inv sp0 M tid;
  rx_atx  : OAX.atx_cellsA M;
  rx_icb  : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e64 [C1 (Z_to_bv 8 cb)]
}.

Lemma run_invX_nil : forall cb own M s mo, run_inv cb own M s mo -> run_invX [] cb own M s mo.
Proof. intros cb own M s mo [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]. constructor; try assumption. constructor. Qed.

Lemma run_inv_nil : forall cb own M s mo, run_invX [] cb own M s mo -> run_inv cb own M s mo.
Proof. intros cb own M s mo [H1 H2 _ H3 H4 H5 H6 H7 H8 H9 H10]. constructor; assumption. Qed.

Lemma own_live : forall X G s mo, OWN X G s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
Proof.
  intros X G s mo [(L & _ & HKL & _) _]. split; [exact (kl_halt _ _ _ HKL)|].
  exact (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)).
Qed.

Lemma nodup_app_ne : forall (L1 L2 : list block) (c1 c2 : block),
  List.NoDup (map blk_id (L1 ++ L2)) -> In c1 L1 -> In c2 L2 -> blk_id c1 <> blk_id c2.
Proof.
  induction L1 as [|a L1 IH]; intros L2 c1 c2 ND I1 I2; [destruct I1|].
  cbn [app map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct I1 as [->|I1]; [|eapply IH; eassumption].
  intros E. apply NI. rewrite E. apply in_map. apply in_or_app. right. exact I2.
Qed.

Lemma blkX_facts : forall LBx cb own M s mo (c : block), run_invX LBx cb own M s mo -> In c LBx ->
  rblock_range (blk_addr c) (blk_size c) /\
  match own with None => True | Some (_, D) => blk_addr c + blk_size c <= D \/ D + payl <= blk_addr c end.
Proof.
  intros LBx cb own M s mo c RI IN. pose proof (rx_heap _ _ _ _ _ _ RI) as HH.
  split; [apply (RHEAP_block_range_proof _ _ _ c HH); apply in_or_app; left; exact IN|].
  destruct own as [[q D]|]; [|exact I].
  pose proof (RHEAP_blocks_disjoint_proof _ _ _ c (q, D, payl) HH ltac:(apply in_or_app; left; exact IN)
                ltac:(apply in_or_app; right; left; reflexivity)) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. apply DJ.
  apply (nodup_app_ne LBx (LBT (Some (q, D))) c (q, D, payl)); [exact (RHEAP_blocks_nodup_proof _ _ _ HH) | exact IN | left; reflexivity].
Qed.

Lemma own_rangeX : forall LBx cb own M s mo, run_invX LBx cb own M s mo ->
  match own with None => True | Some (_, D) => 0 < D /\ D mod 16 = 0 /\ D + payl <= ATOP /\ (D + payl <= 0x10000 \/ 0x94000 <= D) end.
Proof.
  intros LBx cb [[q D]|] M s mo RI; [|exact I].
  pose proof (RHEAP_block_range_proof _ _ _ (q, D, payl) (rx_heap _ _ _ _ _ _ RI) ltac:(apply in_or_app; right; left; reflexivity))
    as (H1 & H2 & H3 & H4 & H5).
  cbn in *. auto.
Qed.

Definition fp_u (LBx : list block) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= sp0 - 208)   (* rx_stk's window *)
  \/ (0x32e90 <= fst iv /\ snd iv <= 0x72e90)
  \/ (exists c : block, In c LBx /\ blk_addr c <= fst iv /\ snd iv <= blk_addr c + blk_size c).
Definition fp_x (LBx : list block) (iv : Z * Z) : Prop := fp_u LBx iv \/ fp_so iv.

Definition fp_cls (own : option (bptr * Z)) (iv : Z * Z) : Prop :=
  (ATOP <= fst iv /\ snd iv <= sp0 - 208)
  \/ (0x22d18 <= fst iv /\ snd iv <= 0x93a30 /\ (snd iv <= 0x72e90 \/ 0x93628 <= fst iv))
  \/ (snd iv <= ATOP /\ (snd iv <= 0x10000 \/ 0x94000 <= fst iv)
      /\ match own with None => True | Some (_, D) => snd iv <= D \/ D + payl <= fst iv end).

Lemma fp_x_cls : forall LBx cb own M s mo iv, run_invX LBx cb own M s mo -> fp_x LBx iv -> fp_cls own iv.
Proof.
  intros LBx cb own M s mo [a b] RI [[H|[H|(c & IN & H1 & H2)]]|H]; unfold fp_cls; cbn [fst snd] in *.
  - left. lia.   (* ATOP <= lo (ALO) *)
  - right; left. lia.
  - right; right. destruct (blkX_facts _ _ _ _ _ _ c RI IN) as [(R1 & R2 & R3 & R4 & R5) DJ].
    split; [lia|]. split; [lia|]. destruct own as [[q D]|]; [lia | exact I].
  - right; left. unfold fp_so in H. cbn [fst snd] in H. lia.
Qed.

Lemma fp_x_ok : forall LBx cb own M s mo iv, run_invX LBx cb own M s mo -> fp_x LBx iv -> fp_ok sp0 iv.
Proof.
  intros LBx cb own M s mo [a b] RI [[H|[H|(c & IN & H1 & H2)]]|H]; unfold fp_ok, fp_cli; cbn [fst snd] in *.
  - left; left. lia.
  - left; right; right; right; right. exact H.
  - left; right; left. destruct (blkX_facts _ _ _ _ _ _ c RI IN) as [(R1 & R2 & R3 & R4 & R5) _]. lia.
  - right. exact H.
Qed.

Definition zone_x (A n : Z) : Prop :=
  sp0 - 208 <= A \/ (0x10000 <= A /\ A + n <= 0x22d18) \/ (0x72e90 <= A /\ A + n <= 0x93628).

Lemma fp_cls_zone : forall own W A n, Forall (fp_cls own) W -> zone_x A n -> 0 <= n -> disjoint_from W A n.
Proof.
  intros own W A n FC Z Hn. induction FC as [|[a b] W H _ IH]; cbn; [exact I|]. split; [|exact IH].
  unfold fp_cls, zone_x in *. cbn [fst snd] in H. clear IH. destruct own as [[? ?]|]; lia.
Qed.

Lemma fp_cls_data : forall q D W, Forall (fp_cls (Some (q, D))) W ->
  D + payl <= ATOP -> (D + payl <= 0x10000 \/ 0x94000 <= D) -> disjoint_from W D payl.
Proof.
  intros q D W FC D1 D2. induction FC as [|[a b] W H _ IH]; cbn; [exact I|]. split; [|exact IH].
  unfold fp_cls in H. cbn [fst snd] in H. clear IH. lia.
Qed.

Lemma fp_x_icb : forall LBx cb own M s mo W, run_invX LBx cb own M s mo -> Forall (fp_x LBx) W -> disjoint_from W 0x32e64 1.
Proof.
  intros LBx cb own M s mo W RI FW. induction FW as [|[a b] W H _ IH]; cbn; [exact I|]. split; [|exact IH].
  destruct H as [[H|[H|(c & IN & H1 & H2)]]|H]; unfold fp_so in *; cbn [fst snd] in *; try lia.
  destruct (blkX_facts _ _ _ _ _ _ c RI IN) as [(R1 & R2 & R3 & R4 & R5) _]. lia.
Qed.

Lemma run_invX_mu : forall LBx cb own M M' s mo W,
  run_invX LBx cb own M s mo -> munch W M M' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' -> Forall (fp_x LBx) W -> run_invX LBx cb own M' s mo.
Proof.
  intros LBx cb own M M' s mo W RI MU WM FW. pose proof (own_rangeX _ _ _ _ _ _ RI) as OR.
  assert (FC : Forall (fp_cls own) W) by (eapply Forall_impl; [|exact FW]; intros iv; apply (fp_x_cls _ _ _ _ _ _ _ RI)).
  assert (FOK : Forall (fp_ok sp0) W) by (eapply Forall_impl; [|exact FW]; intros iv; apply (fp_x_ok _ _ _ _ _ _ _ RI)).
  pose proof (fp_x_icb _ _ _ _ _ _ _ RI FW) as DI.
  destruct RI as [HH HOWN WR DATA ST ERR MI FRT CLI AXA ICB].
  constructor.
  - eapply RHEAP_frame_proof; [exact HH | exact MU | exact WM |].
    eapply Forall_impl; [|exact FW]. intros [a b] [[H|[H|(c & IN & H1 & H2)]]|H]; unfold rclient_write_ok; cbn [fst snd] in *.
    + left. lia.
    + right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
    + right; right. exists c. split; [apply in_or_app; left; exact IN | lia].
    + right; left. unfold fp_so in H. cbn [fst snd] in H. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
  - exact HOWN.
  - eapply Forall_impl; [|exact WR]. intros c H. eapply wr_at_transport; [exact H | exact WM].
  - destruct own as [[q D]|]; [|exact DATA]. destruct DATA as [src DATA]. exists src.
    eapply rw_cells_transport; [exact DATA | exact MU | exact WM |].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    apply (fp_cls_data q D W FC); lia.
  - apply (stk_wmono M M'); [exact ST | lia | exact WM].
  - destruct ERR as [errv ERR]. exists errv. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |].
    cbn [cells_size csize]. apply (fp_cls_zone own); [exact FC | unfold zone_x, RERRNO; lia | lia].
  - eapply mem_inv_munch; [exact MI | exact MU | |].
    + intros a Ha. apply (disjoint_outside W a 1); [|lia]. apply (fp_cls_zone own); [exact FC | unfold zone_x; lia | lia].
    + (* the stack class is in rx_stk's window, the blocks are rx_wr's; the rest is the image *)
      rewrite Forall_forall in FW, WR |- *. intros [l0 h0] IN a Ha Hout. cbn [fst snd] in Ha.
      destruct (FW _ IN) as [[H|[H|(c & INc & H1 & H2)]]|H]; unfold fp_so in *; cbn [fst snd] in *.
      * pose proof ST as (_ & _ & STK). exact (proj1 (STK a ltac:(lia))).
      * lia.
      * pose proof (WR c INc) as (_ & _ & WA). replace a with (blk_addr c + (a - blk_addr c)) by lia. apply WA. lia.
      * lia.
  - destruct FRT as (jt & t7 & t6 & t4 & t3 & t2 & t0 & FRT). exists jt, t7, t6, t4, t3, t2, t0.
    eapply rw_cells_transport; [exact FRT | exact MU | exact WM |]. cbn [cells_size csize].
    apply (fp_cls_zone own); [exact FC | unfold zone_x; lia | lia].
  - eapply cli_inv_munch; [exact ATOPE | exact CLI | exact MU | exact WM | exact FOK].
  - eapply OAX.atx_cellsA_munch; [exact MU | exact WM | | exact AXA]. unfold OAX.PATX, OAX.PATX_N.
    apply (fp_cls_zone own); [exact FC | unfold zone_x; lia | lia].
  - eapply rw_cells_transport; [exact ICB | exact MU | exact WM | exact DI].
Qed.

Lemma run_inv_fm : forall cb own M M' s mo rs,
  run_inv cb own M s mo -> OF.frame_mod M M' rs ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp0 - 208) \/ fp_so iv) (fm_ivs rs) ->  (* fp_u's stack class *)
  run_inv cb own M' s mo.
Proof.
  intros cb own M M' s mo rs RI FM FW. destruct (munch_of_frame_mod _ _ _ FM) as [MU WM].
  apply run_inv_nil. eapply run_invX_mu; [apply run_invX_nil; exact RI | exact MU | exact WM |].
  eapply Forall_impl; [|exact FW]. intros iv [H|H]; [left; left; exact H | right; exact H].
Qed.

Lemma run_inv_icb : forall cb cb' own M M' s mo,
  run_inv cb own M s mo -> munch [(0x32e64, 0x32e65)] M M' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' 0x32e64 [C1 (Z_to_bv 8 cb')] -> run_inv cb' own M' s mo.
Proof.
  intros cb cb' own M M' s mo RI MU WM MI' ICB'. pose proof (own_range _ _ _ _ _ RI) as OR.
  destruct RI as [HH HOWN DATA ST ERR MI FRT CLI AXA ICB].
  constructor.
  - eapply RHEAP_frame_proof; [exact HH | exact MU | exact WM |].
    constructor; [|constructor]. unfold rclient_write_ok; cbn [fst snd]. right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
  - exact HOWN.
  - destruct own as [[q D]|]; [|exact DATA]. destruct DATA as [src DATA]. exists src.
    eapply rw_cells_transport; [exact DATA | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. lia.
  - apply (stk_wmono M M'); [exact ST | lia | exact WM].
  - destruct ERR as [errv ERR]. exists errv. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold RERRNO. cbn. lia.
  - exact MI'.
  - destruct FRT as (jt & t7 & t6 & t4 & t3 & t2 & t0 & FRT). exists jt, t7, t6, t4, t3, t2, t0.
    eapply rw_cells_transport; [exact FRT | exact MU | exact WM |]. cbn. lia.
  - eapply cli_inv_munch; [exact ATOPE | exact CLI | exact MU | exact WM |]. constructor; [|constructor]. left. right; right; left. cbn [fst snd]. lia.
  - eapply OAX.atx_cellsA_munch; [exact MU | exact WM | | exact AXA]. unfold OAX.PATX, OAX.PATX_N. cbn. lia.
  - exact ICB'.
Qed.

Lemma so_agree_munch_icb : forall M M', munch [(0x32e64, 0x32e65)] M M' -> so_agree M M'.
Proof. intros M M' MU i Hi. apply MU. unfold so_dom in Hi. rewrite unsigned_lit by lia. cbn [outside]. lia. Qed.

Lemma fp_u_outside_so : forall LBx cb own M s mo W i, run_invX LBx cb own M s mo -> Forall (fp_u LBx) W -> so_dom i -> outside W i.
Proof.
  intros LBx cb own M s mo W i RI FW Hi. unfold so_dom in Hi.
  induction FW as [|[a b] W H _ IH]; cbn; [exact I|]. split; [|exact IH].
  destruct H as [H|[H|(c & IN & H1 & H2)]]; cbn [fst snd] in *; [lia | lia |].
  destruct (blkX_facts _ _ _ _ _ _ c RI IN) as [(R1 & R2 & R3 & R4 & R5) _]. lia.
Qed.

Lemma so_agree_mu : forall LBx cb own M M' s mo W,
  run_invX LBx cb own M s mo -> munch W M M' -> Forall (fp_u LBx) W -> so_agree M M'.
Proof.
  intros LBx cb own M M' s mo W RI MU FW i Hi. apply MU. rewrite unsigned_lit by (unfold so_dom in Hi; lia).
  eapply fp_u_outside_so; eassumption.
Qed.

Lemma so_agree_heap : forall LB SP M M', rheap_pres LB SP M M' -> so_agree M M'.
Proof.
  intros LB SP M M' HP i Hi. unfold so_dom in Hi. destruct (HP i ltac:(lia)) as [E _]; [| exact E].
  unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia.
Qed.

Ltac rcl_static HP H := apply (rheap_pres_rw_cells _ _ _ _ _ _ HP H); right; left; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RERRNO; cbn; lia.

Lemma run_invX_heap : forall LBx LBx' cb own M M' s s' mo mo' SP LBk (errv' : word),
  run_invX LBx cb own M s mo -> lo <= SP -> SP <= sp0 - 208 ->
  rheap_pres LBk SP M M' -> (forall c, In c (LBT own) -> In c LBk) ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo SP -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' RERRNO [C4 errv'] -> rauxv_ok M' sp0 ->
  RHEAP s' (LBx' ++ LBT own) M' -> OWN (map blk_id LBx' ++ XT own) (G_std fs) s' mo' ->
  Forall (fun c : block => wr_at (run_segments psegs rc_inp rc_sp rc_mb) M' (blk_addr c) (blk_size c)) LBx' ->
  run_invX LBx' cb own M' s' mo'.
Proof.
  intros LBx LBx' cb own M M' s s' mo mo' SP LBk errv' RI L1 L2 HP INK MI' ST' ERR' AUX' HH' HOWN' WR'.
  pose proof (own_rangeX _ _ _ _ _ _ RI) as OR.
  destruct RI as [HH HOWN WR DATA ST ERR MI FRT CLI AXA ICB].
  constructor; try assumption.
  - destruct own as [[q D]|]; [|exact DATA]. destruct DATA as [src DATA]. exists src.
    refine (rheap_pres_rw_cells _ _ _ _ _ _ HP DATA _). right; right. exists (q, D, payl).
    split; [apply INK; left; reflexivity|].
    cbn [blk_addr blk_size fst snd cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
  - destruct (stk_split (run_segments psegs rc_inp rc_sp rc_mb) M lo SP (sp0 - 208) ST ltac:(lia)) as [_ STh].
    eapply stk_merge; [exact ST' | eapply rheap_pres_stk; [exact HP | exact STh | lia] | lia].
  - exists errv'. exact ERR'.
  - destruct FRT as (jt & t7 & t6 & t4 & t3 & t2 & t0 & FRT). exists jt, t7, t6, t4, t3, t2, t0.
    refine (rheap_pres_rw_cells _ _ _ _ _ _ HP FRT _). left. lia.
  - exact (cli_inv_heap sp0 _ _ _ _ _ CLI HP ltac:(lia) AUX').
  - destruct AXA as [A1 A2]. unfold OAX.atx_cellsA, OAX.PATX in *. split; [rcl_static HP A1 | rcl_static HP A2].
  - rcl_static HP ICB.
Qed.

Lemma wrX_kept : forall LBx LBk SP M M',
  Forall (fun c : block => wr_at (run_segments psegs rc_inp rc_sp rc_mb) M (blk_addr c) (blk_size c)) LBx ->
  rheap_pres LBk SP M M' -> (forall c, In c LBx -> In c LBk) ->
  Forall (fun c : block => wr_at (run_segments psegs rc_inp rc_sp rc_mb) M' (blk_addr c) (blk_size c)) LBx.
Proof.
  intros LBx LBk SP M M' WR HP INK. apply Forall_forall. intros c IN.
  pose proof (proj1 (Forall_forall _ _) WR c IN) as W.
  refine (rheap_pres_wr_at _ _ _ _ _ _ HP W _). right; right. exists c. split; [apply INK; exact IN | lia].
Qed.

Lemma run_invX_malloc : forall LBx cb own M M' s s' mo mo' SP (pn : bptr) (A n : Z) (junk : list byte) (errv' : word),
  run_invX LBx cb own M s mo -> lo <= SP -> SP <= sp0 - 208 ->
  rheap_pres (LBx ++ LBT own) SP M M' ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo SP -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' RERRNO [C4 errv'] -> rauxv_ok M' sp0 ->
  RHEAP s' ((pn, A, n) :: LBx ++ LBT own) M' -> OWN (pn :: map blk_id LBx ++ XT own) (G_std fs) s' mo' ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' A [CB (Z.to_nat n) junk] -> 0 <= n ->
  run_invX ((pn, A, n) :: LBx) cb own M' s' mo'.
Proof.
  intros LBx cb own M M' s s' mo mo' SP pn A n junk errv' RI L1 L2 HP MI' ST' ERR' AUX' HH' HOWN' NB Hn.
  eapply (run_invX_heap LBx ((pn, A, n) :: LBx)); try eassumption.
  - intros c IN. apply in_or_app. right. exact IN.
  - constructor.
    + cbn [blk_addr blk_size fst snd]. eapply rw_cells_wr_at; [exact NB|]. cbn [cells_size csize]. lia.
    + eapply wrX_kept; [exact (rx_wr _ _ _ _ _ _ RI) | exact HP |]. intros c IN. apply in_or_app. left. exact IN.
Qed.

Lemma run_invX_null : forall LBx cb own M M' s s' mo mo' SP (errv' : word),
  run_invX LBx cb own M s mo -> lo <= SP -> SP <= sp0 - 208 ->
  rheap_pres (LBx ++ LBT own) SP M M' ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo SP -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' RERRNO [C4 errv'] -> rauxv_ok M' sp0 ->
  RHEAP s' (LBx ++ LBT own) M' -> OWN (map blk_id LBx ++ XT own) (G_std fs) s' mo' ->
  run_invX LBx cb own M' s' mo'.
Proof.
  intros LBx cb own M M' s s' mo mo' SP errv' RI L1 L2 HP MI' ST' ERR' AUX' HH' HOWN'.
  eapply (run_invX_heap LBx LBx); try eassumption.
  - intros c IN. apply in_or_app. right. exact IN.
  - eapply wrX_kept; [exact (rx_wr _ _ _ _ _ _ RI) | exact HP |]. intros c IN. apply in_or_app. left. exact IN.
Qed.

Lemma run_invX_free : forall (c0 : block) LBx cb own M M' s s' mo mo' SP (errv' : word),
  run_invX (c0 :: LBx) cb own M s mo -> lo <= SP -> SP <= sp0 - 208 ->
  rheap_pres (lb_remove (blk_id c0) ((c0 :: LBx) ++ LBT own)) SP M M' ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' lo SP -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' RERRNO [C4 errv'] -> rauxv_ok M' sp0 ->
  RHEAP s' (lb_remove (blk_id c0) ((c0 :: LBx) ++ LBT own)) M' -> OWN (map blk_id LBx ++ XT own) (G_std fs) s' mo' ->
  run_invX LBx cb own M' s' mo'.
Proof.
  intros c0 LBx cb own M M' s s' mo mo' SP errv' RI L1 L2 HP MI' ST' ERR' AUX' HH' HOWN'.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ (rx_heap _ _ _ _ _ _ RI)) as ND.
  cbn [app] in ND, HP, HH'. rewrite (lb_remove_head c0 (LBx ++ LBT own) ND) in HP, HH'.
  eapply (run_invX_heap (c0 :: LBx) LBx); try eassumption.
  - intros c IN. apply in_or_app. right. exact IN.
  - pose proof (rx_wr _ _ _ _ _ _ RI) as WR. inversion WR as [|? ? _ WRt]; subst.
    eapply wrX_kept; [exact WRt | exact HP |]. intros c IN. apply in_or_app. left. exact IN.
Qed.

Lemma pf_pre_of_inv : forall cb own M s mo, run_inv cb own M s mo -> pf_pre M (Z_to_bv 64 (sp0 - 208)) (bv_unsigned CAN).
Proof.
  intros cb own M s mo [HH _ _ ST _ MI _ [_ PR _ _] _ _].
  pose proof (ssp_of_RHEAP _ _ _ HH) as [G1 G2].
  assert (U : bv_unsigned (Z_to_bv 64 (sp0 - 208)) = sp0 - 208) by (apply unsigned_lit; lia).
  constructor.
  - rewrite U. replace (sp0 - 208) with (sp0 + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact SP16.
  - rewrite U. unfold PF1_FR. lia.
  - rewrite U. lia.
  - intros a n H1 H2. rewrite U in H1, H2. unfold PF1_FR in H1.
    rewrite <- (Z_to_bv_bv_unsigned a). apply (store_ok_of_stk M lo (sp0 - 208)); [exact ST | lia | lia].
  - intros i Hi. destruct (Z_lt_le_dec i 0x21000) as [L|L]; [apply mem_inv_none; [exact MI | lia]|].
    destruct (Z_lt_le_dec i 0x21be8) as [L2|L2].
    + apply (PR 0x21000 0x21be8); [cbn; tauto | lia].
    + apply (PR 0x21bf0 0x22d18); [cbn; tauto | lia].
  - exact G1.
  - rewrite Z_to_bv_bv_unsigned. exact G2.
  - pose proof (bv_unsigned_in_range 64 CAN) as R. unfold bv_modulus in R. lia.
Qed.

Abbreviation UU := (sp0 - 416).

Lemma dptr_range : forall LBx cb own M s mo, run_invX LBx cb own M s mo -> 1 <= dptr own /\ dptr own + payl <= ATOP.
Proof.
  intros LBx cb own M s mo RI. pose proof (own_rangeX _ _ _ _ _ _ RI) as OR.
  destruct own as [[q D]|]; cbn [dptr]; [lia|]. pose proof (rx_data _ _ _ _ _ _ RI) as E. cbn in E. lia.
Qed.

Lemma lib_layout_of_inv : forall LBx cb own M s mo (pp : bptr) (p : Z),
  run_invX LBx cb own M s mo -> In (pp, p, OL.S9_INFL_N) LBx -> OL.lib_layout_S9 ATOP M UU p (dptr own) payl.
Proof.
  intros LBx cb own M s mo pp p RI IN. pose proof (own_rangeX _ _ _ _ _ _ RI) as OR. pose proof (dptr_range _ _ _ _ _ _ RI) as DR.
  destruct (blkX_facts _ _ _ _ _ _ (pp, p, OL.S9_INFL_N) RI IN) as [PR DJ]. cbn [blk_addr blk_size fst snd] in PR, DJ.
  pose proof PR as (P1 & P2 & P3 & P4 & P5).
  apply (lib_layout_intro sp0 SP0 SP16 ATOPE M p (dptr own) payl lo PR PAYL); try lia.
  - destruct own as [[q D]|]; cbn [dptr] in *; [lia|]. pose proof (rx_data _ _ _ _ _ _ RI) as E. cbn in E. lia.
  - destruct own as [[q D]|]; cbn [dptr] in *; unfold OL.S9_BUF, OL.S9_BUF_N; [lia|].
    pose proof (rx_data _ _ _ _ _ _ RI) as E. cbn in E. lia.
  - destruct own as [[q D]|]; cbn [dptr] in *; unfold OL.S9_INFL_N in *; [lia|].
    pose proof (rx_data _ _ _ _ _ _ RI) as E. cbn in E. lia.
  - intros i Hi. destruct own as [[q D]|]; [|pose proof (rx_data _ _ _ _ _ _ RI) as E; cbn in E; lia].
    destruct (rx_data _ _ _ _ _ _ RI) as [src [[[LEN _] B] _]]. cbn [cells_bytes cbytes dptr] in *. rewrite app_nil_r in B.
    cbn [cell_wf] in LEN.
    assert (LI : (Z.to_nat i + 1 <= length src)%nat) by lia.
    pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M D src (Z.to_nat i) 1%nat B LI) as X.
    rewrite Z2Nat.id in X by lia.
    destruct (skipn (Z.to_nat i) src) as [|b rest] eqn:SK.
    { exfalso. pose proof (f_equal (@length _) SK) as SL. rewrite length_skipn in SL. cbn in SL. lia. }
    exists b. exact X.
  - exact (rx_mi _ _ _ _ _ _ RI).
  - exact (rx_stk _ _ _ _ _ _ RI).
  - unfold OL.S9_FRA. lia.
  - exact (proj1 (Forall_forall _ _) (rx_wr _ _ _ _ _ _ RI) (pp, p, OL.S9_INFL_N) IN).
Qed.

(* the cells the library writes stay off the caller frames UF reads: uncompress2_z's saves (UU+112 ..
   UU+160), uncompress's s0 and ra (UU+176 .. UU+192) and LLVMFuzzerTestOneInput's ra (UU+200 .. UU+208). *)
Lemma u2_fm_transport : forall LBx cb own M M' s mo rs q v2 v3 v4 v5,
  run_invX LBx cb own M s mo -> OF.frame_mod M M' rs ->
  Forall (fp_u LBx) (fm_ivs rs) ->
  (forall x, UU + 112 <= x < UU + 160 \/ UU + 176 <= x < UU + 192 \/ UU + 200 <= x < UU + 208 -> outside (fm_ivs rs) x) ->
  u2_frames sp0 M q payl v2 v3 v4 v5 ->
  run_invX LBx cb own M' s mo /\ so_agree M M' /\ u2_frames sp0 M' q payl v2 v3 v4 v5.
Proof.
  intros LBx cb own M M' s mo rs q v2 v3 v4 v5 RI FM FW OUT UF. destruct (munch_of_frame_mod _ _ _ FM) as [MU WM].
  split; [|split].
  - eapply run_invX_mu; [exact RI | exact MU | exact WM |]. eapply Forall_impl; [|exact FW]. intros iv H. left. exact H.
  - eapply so_agree_mu; eassumption.
  - exact (u2_frames_same_on sp0 SP0 _ _ _ _ _ _ _ _ _ UF (same_on_munch _ _ _ MU WM) OUT).
Qed.

(* WA_S9 = inflate's frame down to u - 1024 (up to u + 112), the sourceLen / got copies (u+160, u+168),
   the state block and the output buffer. *)
Lemma wa_fp : forall (pp : bptr) (p : Z) LBx, In (pp, p, OL.S9_INFL_N) LBx -> 0 <= p < 2 ^ 64 ->
  Forall (fp_u LBx) (fm_ivs (OL.WA_S9 UU p)) /\
  (forall x, p + OL.S9_INFL_N <= ATOP -> UU + 112 <= x < UU + 160 \/ UU + 176 <= x < UU + 192 \/ UU + 200 <= x < UU + 208 -> outside (fm_ivs (OL.WA_S9 UU p)) x).
Proof.
  intros pp p LBx IN PR.
  unfold OL.WA_S9, fm_ivs, OL.S9_FRA, OL.S9_INFL_N, OL.S9_BUF, OL.S9_BUF_N in *. cbn [map fst snd].
  rewrite (unsigned_lit (sp0 - 416 - 1024)), (unsigned_lit (sp0 - 416 + 160)), (unsigned_lit (sp0 - 416 + 168)), (unsigned_lit p), (unsigned_lit 0x32e90) by lia.
  split.
  - constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia|].
    constructor; [right; right; exists (pp, p, 7176); split; [exact IN | cbn [blk_addr blk_size fst snd]; lia]|].
    constructor; [right; left; cbn [fst snd]; lia | constructor].
  - intros x PA Hx. cbn [outside]. lia.
Qed.

Lemma wab_fp : forall (pp pw : bptr) (p w : Z) LBx, In (pp, p, OL.S9_INFL_N) LBx -> In (pw, w, OL.S9_WIN_N) LBx ->
  0 <= p < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  Forall (fp_u LBx) (fm_ivs (OL.WA_S9 UU p ++ [(Z_to_bv 64 w, OL.S9_WIN_N)])) /\
  (forall x, p + OL.S9_INFL_N <= ATOP -> w + OL.S9_WIN_N <= ATOP -> UU + 112 <= x < UU + 160 \/ UU + 176 <= x < UU + 192 \/ UU + 200 <= x < UU + 208 ->
             outside (fm_ivs (OL.WA_S9 UU p ++ [(Z_to_bv 64 w, OL.S9_WIN_N)])) x).
Proof.
  intros pp pw p w LBx IN INW PR WR.
  unfold OL.WA_S9, fm_ivs, OL.S9_FRA, OL.S9_INFL_N, OL.S9_WIN_N, OL.S9_BUF, OL.S9_BUF_N in *. cbn [map fst snd app].
  rewrite (unsigned_lit (sp0 - 416 - 1024)), (unsigned_lit (sp0 - 416 + 160)), (unsigned_lit (sp0 - 416 + 168)), (unsigned_lit p), (unsigned_lit 0x32e90), (unsigned_lit w) by lia.
  split.
  - constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia|].
    constructor; [right; right; exists (pp, p, 7176); split; [exact IN | cbn [blk_addr blk_size fst snd]; lia]|].
    constructor; [right; left; cbn [fst snd]; lia |].
    constructor; [right; right; exists (pw, w, 32768); split; [exact INW | cbn [blk_addr blk_size fst snd]; lia] | constructor].
  - intros x PA WA Hx. cbn [outside]. lia.
Qed.

(* uncompress's tail (0x14ef4 ..) reads and writes the harness's frames, so its segment takes them as
   rw_cells. These lemmas carve them from the stack and give the saved cells the values UF reads there. *)
Lemma rw_cells_peel8 : forall (M : word -> option byte) A pre (n : nat) j post,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A (pre ++ CB (8 + n) j :: post) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A (pre ++ C8 (le_bytes_to_word (firstn 8 j)) :: CB n (skipn 8 j) :: post).
Proof.
  intros M A pre n j post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn [cell_wf] in H2.
  assert (E8 : le8 (le_bytes_to_word (firstn 8 j)) = firstn 8 j)
    by (apply DrawDefs.le8_roundtrip; rewrite firstn_length; lia).
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. cbn [cells_wf cell_wf]. split; [exact I|]. split; [rewrite skipn_length; lia | exact H3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite E8, (app_assoc (firstn 8 j)), firstn_skipn. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *.
    replace (8 + (n + cells_size post))%nat with (8 + n + cells_size post)%nat by lia. exact Hw.
Qed.

Lemma rw_cells_last8 : forall (M : word -> option byte) A pre j,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A (pre ++ [CB 8 j]) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A (pre ++ [C8 (le_bytes_to_word j)]).
Proof.
  intros M A pre j [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 _]]. cbn [cell_wf] in H2.
  assert (E8 : le8 (le_bytes_to_word j) = j) by (apply DrawDefs.le8_roundtrip; exact H2).
  split; [split|].
  - apply cells_wf_app. split; [exact H1 | cbn [cells_wf cell_wf]; tauto].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite E8. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

Lemma rw_cells_C8_eq : forall (M : word -> option byte) A pre (w v : word) post (a : Z),
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A (pre ++ C8 w :: post) ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> a = A + Z.of_nat (cells_size pre) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A (pre ++ C8 v :: post).
Proof.
  intros M A pre w v post a RW RD Ea.
  assert (E : w = v).
  { destruct RW as [[Hwf Hb] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 _].
    rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
    assert (LE : (length (cells_bytes pre) + 8 <= length (cells_bytes pre ++ le8 w ++ cells_bytes post))%nat)
      by (rewrite !app_length, length_le8; lia).
    pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M A _ _ 8 Hb LE) as X.
    rewrite skipn_app_exact in X.
    assert (F8 : firstn 8 (le8 w ++ cells_bytes post) = le8 w)
      by (rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r; apply firstn_all2; rewrite length_le8; lia).
    rewrite F8, (cells_bytes_length pre H1) in X. unfold wa in X. rewrite <- Ea in X.
    assert (SV : Some (le8 w) = Some (word_to_le_bytes 8 v)) by (rewrite <- X; exact RD).
    apply (f_equal (fun o : option (list byte) => match o with Some x => x | None => [] end)) in SV. cbv beta iota in SV.
    assert (E2 : le_bytes_to_word (le8 w) = le_bytes_to_word (le8 v)) by (f_equal; exact SV).
    rewrite !le_bytes_to_word_le8 in E2. exact E2. }
  rewrite <- E. exact RW.
Qed.

Lemma u2_ret_cells : forall (M : word -> option byte) q v2 v3 v4 v5,
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208) -> u2_frames sp0 M q payl v2 v3 v4 v5 ->
  exists sl g bl : word,
    rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 256) [C8 sl; C8 g; C8 (Z_to_bv 64 payl); C8 (Z_to_bv 64 S9U2Seg.S9_UNC_RA)] /\
    rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 224) [C8 bl; C8 (Z_to_bv 64 S9U2Seg.T_RET)].
Proof.
  intros M q v2 v3 v4 v5 ST [F_hra F_wra F_us0 F_ura _ _ _ _ _].
  rewrite <- (le8_lit S9U2Seg.T_RET) in F_hra by (unfold S9U2Seg.T_RET; lia).
  rewrite <- (le8_lit S9U2Seg.S9_UNC_RA) in F_wra by (unfold S9U2Seg.S9_UNC_RA; lia).
  destruct (stk_carve (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208) 16%nat ST ltac:(lia)) as [ST1 [j1 C1]].
  destruct (stk_carve (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208 - Z.of_nat 16) 32%nat ST1 ltac:(lia)) as [_ [j0 C0]].
  change (Z.of_nat 16) with 16 in C1, C0. change (Z.of_nat 32) with 32 in C0.
  replace (sp0 - 208 - 16 - 32) with (sp0 - 256) in C0 by lia.
  replace (sp0 - 208 - 16) with (sp0 - 224) in C1 by lia.
  (* the harness's frame: buffer_length, then LLVMFuzzerTestOneInput's ra *)
  pose proof (rw_cells_peel8 M (sp0 - 224) [] 8 j1 [] C1) as C1a. cbn [app] in C1a.
  pose proof (rw_cells_last8 M (sp0 - 224) [_] _ C1a) as C1b. cbn [app] in C1b.
  pose proof (rw_cells_C8_eq M (sp0 - 224) [_] _ (Z_to_bv 64 S9U2Seg.T_RET) [] _ C1b F_hra ltac:(cbn; lia)) as C1c.
  cbn [app] in C1c.
  (* uncompress's frame: the sourceLen copy, got, its saved s0 (payl), its ra *)
  pose proof (rw_cells_peel8 M (sp0 - 256) [] 24 j0 [] C0) as C0a. cbn [app] in C0a.
  pose proof (rw_cells_peel8 M (sp0 - 256) [_] 16 _ [] C0a) as C0b. cbn [app] in C0b.
  pose proof (rw_cells_peel8 M (sp0 - 256) [_; _] 8 _ [] C0b) as C0c. cbn [app] in C0c.
  pose proof (rw_cells_last8 M (sp0 - 256) [_; _; _] _ C0c) as C0d. cbn [app] in C0d.
  pose proof (rw_cells_C8_eq M (sp0 - 256) [_; _] _ (Z_to_bv 64 payl) [_] _ C0d F_us0 ltac:(cbn; lia)) as C0e.
  cbn [app] in C0e.
  pose proof (rw_cells_C8_eq M (sp0 - 256) [_; _; _] _ (Z_to_bv 64 S9U2Seg.S9_UNC_RA) [] _ C0e F_wra ltac:(cbn; lia)) as C0f.
  cbn [app] in C0f.
  eexists _, _, _. split; [exact C0f | exact C1c].
Qed.

Section CALL.
Variables (own : option (bptr * Z)) (T : ShapeAlg.TSet) (r : Z) (M0 : word -> option byte) (x3 x19 x22 x23 x24 x25 x26 x27 : word).
Hypothesis HK : forall (M' : word -> option byte) (s' : PState) (mo' : Model) (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
  run_inv 0 own M' s' mo' -> so_agree M0 M' ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR (Z_to_bv 64 0x14c78) (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) y5 y6 y7
                                 (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) (Z_to_bv 64 0) (Z_to_bv 64 0) y12 y13 y14 y15 y16 y17
                                 (Z_to_bv 64 (oreg own)) (Z_to_bv 64 0) (Z_to_bv 64 0x32e60) (Z_to_bv 64 r)
                                 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                            bvmap_empty (Z_to_bv 64 0x14d24) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') T.

(* UF = the caller frames; SE = the entry registers the library returns: s5 (target_run's r, which
   uncompress2_z does not save at 1.4) and s6 .. s11. *)
Abbreviation UF M := (u2_frames sp0 M (dptr own) payl (Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 0x32e60) (Z_to_bv 64 r)).
Abbreviation SE := [bv_unsigned (Z_to_bv 64 r); bv_unsigned x22; bv_unsigned x23; bv_unsigned x24; bv_unsigned x25; bv_unsigned x26; bv_unsigned x27].

(* from uncompress's return point (0x14ef4, sp0-256) through uncompress's and LLVMFuzzerTestOneInput's
   tails to target_run's emit_printf call (HK). *)
Lemma u2_ret_rz : forall (M : word -> option byte) (s : PState) (mo : Model)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
  run_inv 1 own M s mo -> UF M -> so_agree M0 M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (sp0 - 256)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (sp0 + -224)) (Z_to_bv 64 (dptr own))
                                 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 0x32e60) (Z_to_bv 64 r)
                                 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                            bvmap_empty (Z_to_bv 64 0x14f54) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros M s mo y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI UFM AG.
  destruct (own_live _ _ _ _ (ri_own _ _ _ _ _ RI)) as [Hh Hl].
  destruct (u2_ret_cells M _ _ _ _ _ (ri_stk _ _ _ _ _ RI) UFM) as (sl & g & bl & FR0 & FR).
  replace (sp0 + -224) with (sp0 - 224) by lia.
  apply rz_evt; [exact Hh | exact Hl |].
  eapply (u2_seg_ret_evt sp0); [exact FR0 | exact FR |].
  intros M1 MU1 WM1. unfold S9U2Seg.T_RET.
  pose proof (run_invX_nil _ _ _ _ _ RI) as RX.
  assert (FW : Forall (fp_u []) [(sp0 - 224, sp0 - 216)]) by (constructor; [left; cbn [fst snd]; lia | constructor]).
  pose proof (run_inv_nil _ _ _ _ _ (run_invX_mu [] 1 own M M1 s mo _ RX MU1 WM1
                ltac:(eapply Forall_impl; [|exact FW]; intros iv H; left; exact H))) as RI1.
  pose proof (so_agree_trans _ _ _ AG (so_agree_mu [] 1 own M M1 s mo _ RX MU1 FW)) as AG1.
  clear MU1 WM1 FR0 FR UFM RX RI AG.
  pose proof (ri_icb _ _ _ _ _ RI1) as ICB. pose proof (ri_mi _ _ _ _ _ RI1) as MI.
  pose proof (munch_refl [(0x32e64, 0x32e65)] M1) as MU. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) M1) as WM.
  apply rz_evt; [exact Hh | exact Hl |].
  (* target_run after the call: mv s3,a0; sb zero,4(s4); mv a1,a0; jal emit_printf *)
  do 4 step. apply evt_done.
  lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into M2 end.
  assert (RI2 : run_inv 0 own M2 s mo) by (eapply run_inv_icb; [exact RI1 | exact MU | exact WM | exact MI | exact ICB]).
  eapply HK; [exact RI2 | eapply so_agree_trans; [exact AG1 | apply so_agree_munch_icb; exact MU]].
Qed.

(* inflateEnd's tail and uncompress2_z's epilogue (zc) back to uncompress; s5 rides through. *)
Lemma u2_zc_rz : forall (R' : bvmap 5 word) (M : word -> option byte) (s : PState) (mo : Model),
  reg_get R' (Z_to_bv 5 2) = Z_to_bv 64 (UU - 16) -> reg_get R' (Z_to_bv 5 8) = Z_to_bv 64 (UU) ->
  reg_get R' (Z_to_bv 5 3) = x3 -> reg_get R' (Z_to_bv 5 4) = Z_to_bv 64 RATP ->
  reg_get R' (Z_to_bv 5 21) = Z_to_bv 64 r ->
  reg_get R' (Z_to_bv 5 22) = x22 -> reg_get R' (Z_to_bv 5 23) = x23 -> reg_get R' (Z_to_bv 5 24) = x24 ->
  reg_get R' (Z_to_bv 5 25) = x25 -> reg_get R' (Z_to_bv 5 26) = x26 -> reg_get R' (Z_to_bv 5 27) = x27 ->
  run_inv 1 own M s mo -> UF M -> so_agree M0 M ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.S9_RA2) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' (Z_to_bv 64 OL.S9_ZC) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R' M s mo G2 G8 G3 G4 G21 G22 G23 G24 G25 G26 G27 RI UFM AG RA2.
  destruct (own_live _ _ _ _ (ri_own _ _ _ _ _ RI)) as [Hh Hl].
  pose proof UFM as [F_hra F_wra F_us0 F_ura F_s0 F_s1 F_s2 F_s3 F_s4].
  destruct (OL.run_zc_S9 C7 R' M UU (Z_to_bv 64 (sp0 + -224)) (Z_to_bv 64 (dptr own)) (Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 0x32e60) (Z_to_bv 64 r))
    as (R3 & M3 & HMS & FM & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & ZK).
  1: exact G2. 1: exact G8.
  1: replace (sp0 - 416) with (sp0 + (-26) * 16) by lia; rewrite Z_mod_plus_full; exact SP16.
  1: unfold OL.S9_IMG_TOP; lia. 1: lia.
  1: change (Z.to_nat 224) with 224%nat; apply (store_ok_of_stk M lo (sp0 - 208)); [exact (ri_stk _ _ _ _ _ RI) | lia | lia].
  1: exact RA2. 1: exact F_ura. 1: exact F_s0. 1: exact F_s1. 1: exact F_s2. 1: exact F_s3. 1: exact F_s4.
  eapply rz_ours; [exact Hh | exact Hl | exact HMS |].
  assert (FW : Forall (fp_u []) (fm_ivs [(Z_to_bv 64 (UU + 56), 8)]) /\
               (forall x, UU + 112 <= x < UU + 160 \/ UU + 176 <= x < UU + 192 \/ UU + 200 <= x < UU + 208 -> outside (fm_ivs [(Z_to_bv 64 (UU + 56), 8)]) x)).
  { unfold fm_ivs. cbn [map fst snd]. rewrite unsigned_lit by lia. split.
    - constructor; [left; cbn [fst snd]; lia | constructor].
    - intros x Hx. cbn [outside]. lia. }
  destruct (u2_fm_transport [] 1 own M M3 s mo _ _ _ _ _ _ (run_invX_nil _ _ _ _ _ RI) FM (proj1 FW) (proj2 FW) UFM) as (RI3 & AG3 & UF3).
  eapply (rz_zc_regs R' R3 _ M3 mo T (sp0 - 256) _ _ _ _ _ _ x3 (Z_to_bv 64 RATP) x22 x23 x24 x25 x26 x27);
    [ rewrite (Z2 : reg_get R3 (Z_to_bv 5 2) = _); f_equal; lia
    | exact Z8 | exact Z9 | exact Z18 | exact Z19 | exact Z20
    | rewrite (Z21 : reg_get R3 (Z_to_bv 5 21) = _); exact G21 | exact ZK
    | exact G3 | exact G4 | exact G22 | exact G23 | exact G24 | exact G25 | exact G26 | exact G27 | ].
  intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31.
  eapply u2_ret_rz; [apply run_inv_nil; exact RI3 | exact UF3 | eapply so_agree_trans; eassumption].
Qed.

Lemma u2_ze2_rz : forall (pp : bptr) (p : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (y1 y5 y6 y7 y9 y12 y13 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 : word),
  run_invX [(pp, p, OL.S9_INFL_N)] 1 own M s mo -> UF M -> so_agree M0 M ->
  OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.S9_RA2) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (UU - 16)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (UU)) y9 (Z_to_bv 64 0) (Z_to_bv 64 p)
                                 y12 y13 (Z_to_bv 64 0x1720c) y15 y16 y17 y18 y19 y20 (Z_to_bv 64 r) x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                            bvmap_empty (Z_to_bv 64 0x171e0) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros pp p M s mo y1 y5 y6 y7 y9 y12 y13 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 RI UFM AG RA2.
  destruct (own_live _ _ _ _ (rx_own _ _ _ _ _ _ RI)) as [Hh Hl].
  destruct (rx_err _ _ _ _ _ _ RI) as [errv ERR].
  destruct (stk_split (run_segments psegs rc_inp rc_sp rc_mb) M lo (UU - 16) (sp0 - 208) (rx_stk _ _ _ _ _ _ RI) ltac:(lia)) as [STl _].
  apply rz_evt; [exact Hh | exact Hl |].
  eapply u2_seg_ze2_evt.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (free_rz_any RR M mo s ([(pp, p, OL.S9_INFL_N)] ++ LBT own) (XT own) (G_std fs) pp p OL.S9_INFL_N lo sp0 errv) end.
  1: exact (rx_heap _ _ _ _ _ _ RI). 1: left; reflexivity. 1: exact (rx_own _ _ _ _ _ _ RI). 1: apply frame_ok_G_std.
  1: exact (ci_aux _ _ _ (rx_cli _ _ _ _ _ _ RI)).
  1: simp_regs; rewrite unsigned_lit by lia; lia.
  1: simp_regs; rewrite unsigned_lit by lia; exact STl.
  1: exact ALO.
  1: simp_regs; rewrite unsigned_lit by lia; unfold RFREE_STACK; lia.
  1: simp_regs; rewrite rerrno_lit'; exact ERR.
  1: exact (rx_mi _ _ _ _ _ _ RI). 1: simp_regs; reflexivity. 1: simp_regs; reflexivity.
  intros R' M' mo' s' KEPT MI' ST' ERR' AUX' HP _ _ HH' HOWN'.
  revert HP ST' ERR'. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP ST' ERR'.
  pose proof (run_invX_free (pp, p, OL.S9_INFL_N) [] 1 own M M' s s' mo mo' (UU - 16) errv RI ltac:(lia) ltac:(lia) HP MI' ST' ERR' AUX' HH' HOWN') as RI'.
  pose proof (same_on_rheap_pres _ _ _ _ HP) as SO.
  assert (UF' : UF M') by (apply (u2_frames_same_on sp0 SP0 _ _ _ _ _ _ _ _ _ UFM SO); intros x Hx; left; lia).
  assert (RA2' : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M' (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.S9_RA2)).
  { rewrite <- RA2. apply (rdn_same_on _ M M' _ _ SO); [intros x Hx; left; cbn in Hx; lia | lia | cbn; lia]. }
  rewrite ret_pc_even by (first [lia | reflexivity]).
  eapply (u2_zc_rz R' M' s' mo');
    [ rewrite (KEPT 2) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 8) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 3) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 4) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 21) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 22) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 23) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 24) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 25) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 26) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | rewrite (KEPT 27) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
    | apply run_inv_nil; exact RI' | exact UF' | eapply so_agree_trans; [exact AG | eapply so_agree_heap; exact HP] | exact RA2' ].
Qed.

Lemma u2_ze1_rz : forall (pp pw : bptr) (p w : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (y1 y5 y6 y7 y9 y12 y13 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 : word),
  run_invX [(pw, w, OL.S9_WIN_N); (pp, p, OL.S9_INFL_N)] 1 own M s mo -> UF M -> so_agree M0 M ->
  OL.end_cells_S9 M UU p ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (UU - 16)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (UU)) y9 (Z_to_bv 64 0) (Z_to_bv 64 w)
                                 y12 y13 (Z_to_bv 64 0x1720c) y15 y16 y17 y18 y19 y20 (Z_to_bv 64 r) x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                            bvmap_empty (Z_to_bv 64 0x171c8) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros pp pw p w M s mo y1 y5 y6 y7 y9 y12 y13 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 RI UFM AG EC.
  destruct (own_live _ _ _ _ (rx_own _ _ _ _ _ _ RI)) as [Hh Hl].
  destruct (rx_err _ _ _ _ _ _ RI) as [errv ERR].
  destruct (stk_split (run_segments psegs rc_inp rc_sp rc_mb) M lo (UU - 16) (sp0 - 208) (rx_stk _ _ _ _ _ _ RI) ltac:(lia)) as [STl _].
  destruct (blkX_facts _ _ _ _ _ _ (pp, p, OL.S9_INFL_N) RI ltac:(right; left; reflexivity)) as [(P1 & P2 & P3 & P4 & P5) _].
  cbn [blk_addr blk_size fst snd] in P1, P3, P4.
  apply rz_evt; [exact Hh | exact Hl |].
  eapply u2_seg_ze1_evt.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (free_rz_any RR M mo s ([(pw, w, OL.S9_WIN_N); (pp, p, OL.S9_INFL_N)] ++ LBT own) (map blk_id [(pp, p, OL.S9_INFL_N)] ++ XT own)
              (G_std fs) pw w OL.S9_WIN_N lo sp0 errv) end.
  1: exact (rx_heap _ _ _ _ _ _ RI). 1: left; reflexivity. 1: exact (rx_own _ _ _ _ _ _ RI). 1: apply frame_ok_G_std.
  1: exact (ci_aux _ _ _ (rx_cli _ _ _ _ _ _ RI)).
  1: simp_regs; rewrite unsigned_lit by lia; lia.
  1: simp_regs; rewrite unsigned_lit by lia; exact STl.
  1: exact ALO.
  1: simp_regs; rewrite unsigned_lit by lia; unfold RFREE_STACK; lia.
  1: simp_regs; rewrite rerrno_lit'; exact ERR.
  1: exact (rx_mi _ _ _ _ _ _ RI). 1: simp_regs; reflexivity. 1: simp_regs; reflexivity.
  intros R' M' mo' s' KEPT MI' ST' ERR' AUX' HP _ _ HH' HOWN'.
  revert HP ST' ERR'. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP ST' ERR'.
  pose proof (run_invX_free (pw, w, OL.S9_WIN_N) [(pp, p, OL.S9_INFL_N)] 1 own M M' s s' mo mo' (UU - 16) errv RI ltac:(lia) ltac:(lia)
                HP MI' ST' ERR' AUX' HH' HOWN') as RI'.
  pose proof (same_on_rheap_pres _ _ _ _ HP) as SO.
  assert (UF' : UF M') by (apply (u2_frames_same_on sp0 SP0 _ _ _ _ _ _ _ _ _ UFM SO); intros x Hx; left; lia).
  assert (EC' : OL.end_cells_S9 M' UU p) by (apply (end_cells_same_on sp0 SP0 _ _ _ _ EC SO); intros x Hx; left; lia).
  assert (AG' : so_agree M0 M') by (eapply so_agree_trans; [exact AG | eapply so_agree_heap; exact HP]).
  destruct (own_live _ _ _ _ (rx_own _ _ _ _ _ _ RI')) as [Hh' Hl'].
  clear HP SO RI UFM EC AG STl ERR HH' HOWN' ST' ERR' MI' AUX'.
  use_kept KEPT. forget_regs R'. clear KEPT.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  apply rz_evt; [exact Hh' | exact Hl' |].
  eapply (u2_seg_ze1b_evt sp0); [exact EC' | lia |].
  eapply u2_ze2_rz; [exact RI' | exact UF' | exact AG' | exact (proj1 EC')].
Qed.

Lemma u2_zw_rz : forall (R2 : bvmap 5 word) (pp : bptr) (p : Z) (M : word -> option byte) (s : PState) (mo : Model),
  reg_get R2 (Z_to_bv 5 13) = Z_to_bv 64 OL.S9_ZCALLOC -> reg_get R2 (Z_to_bv 5 10) = Z_to_bv 64 0 ->
  reg_get R2 (Z_to_bv 5 11) = Z_to_bv 64 OL.S9_WIN_N -> reg_get R2 (Z_to_bv 5 12) = Z_to_bv 64 1 ->
  reg_get R2 (Z_to_bv 5 2) = Z_to_bv 64 (UU - OL.S9_ZWD) -> reg_get R2 (Z_to_bv 5 3) = x3 -> reg_get R2 (Z_to_bv 5 4) = Z_to_bv 64 RATP ->
  OL.zw_inv_S9 C7 UU p (dptr own) payl ATOP SE (OZ.sregs R2 OZ.S_ALL) M ->
  run_invX [(pp, p, OL.S9_INFL_N)] 1 own M s mo -> UF M -> so_agree M0 M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R2 (Z_to_bv 64 OL.S9_T_ZW) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R2 pp p M s mo W13 W10 W11 W12 W2 W3 W4 ZW RI UFM AG.
  destruct (own_live _ _ _ _ (rx_own _ _ _ _ _ _ RI)) as [Hh Hl].
  destruct (rx_err _ _ _ _ _ _ RI) as [errv ERR].
  pose proof (dptr_range _ _ _ _ _ _ RI) as DR.
  destruct (blkX_facts _ _ _ _ _ _ (pp, p, OL.S9_INFL_N) RI ltac:(left; reflexivity)) as [(P1 & P2 & P3 & P4 & P5) PDJ].
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5, PDJ.
  unfold OL.S9_ZWD, OL.S9_T_ZW, OL.S9_ZCALLOC, OL.S9_WIN_N in *.
  destruct (stk_split (run_segments psegs rc_inp rc_sp rc_mb) M lo (UU - 272) (sp0 - 208) (rx_stk _ _ _ _ _ _ RI) ltac:(lia)) as [STl _].
  eapply (rz_zw_regs R2 _ M mo T _ _ _ _ _ _ _ W2 W3 W4 W10 W11 W12 W13). cbv beta zeta.
  apply rz_evt; [exact Hh | exact Hl |].
  eapply u2_seg_zw_evt.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (malloc_rz_any RR M mo s ([(pp, p, OL.S9_INFL_N)] ++ LBT own) (map blk_id [(pp, p, OL.S9_INFL_N)] ++ XT own)
              (G_std fs) 32768 lo sp0 errv) end.
  1: exact (rx_heap _ _ _ _ _ _ RI). 1: exact (rx_own _ _ _ _ _ _ RI). 1: apply frame_ok_G_std.
  1: exact (ci_aux _ _ _ (rx_cli _ _ _ _ _ _ RI)).
  1: simp_regs; rewrite unsigned_lit by lia; lia.
  1: simp_regs; rewrite unsigned_lit by lia; exact STl.
  1: exact ALO.
  1: simp_regs; rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia.
  1: simp_regs; rewrite rerrno_lit'; exact ERR.
  1: exact (rx_mi _ _ _ _ _ _ RI). 1: simp_regs; reflexivity. 1: simp_regs; reflexivity. 1: lia.
  intros R3 M3 mo3 s3 rr MR OR.
  destruct MR as (KEPT & MI3 & ST3 & [errv3 ERR3] & AUX3 & HP & _ & _ & HR).
  revert HP ST3 ERR3. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP ST3 ERR3.
  pose proof (same_on_rheap_pres _ _ _ _ HP) as SO.
  assert (UF3 : UF M3) by (apply (u2_frames_same_on sp0 SP0 _ _ _ _ _ _ _ _ _ UFM SO); intros x Hx; left; lia).
  assert (AG3 : so_agree M0 M3) by (eapply so_agree_trans; [exact AG | eapply so_agree_heap; exact HP]).
  assert (ZW3 : OL.zw_inv_S9 C7 UU p (dptr own) payl ATOP SE (OZ.sregs R3 OZ.S_ALL) M3).
  { rewrite (sregs_all_kept _ _ KEPT).
    lazymatch goal with |- OL.zw_inv_S9 _ _ _ _ _ _ _ ?sw _ => replace sw with (OZ.sregs R2 OZ.S_ALL) by reflexivity end.
    apply (zw_inv_same_on _ _ M M3 _ _ _ _ _ _ _ (OL.zw_local_S9 C7) ZW SO).
    unfold OL.S9_ZWD, OL.S9_INFL_N, OL.S9_BUF, OL.S9_BUF_N. intros x Rx [Hx|[Hx|[Hx|Hx]]].
    - left. lia.
    - right; right. exists (pp, p, OL.S9_INFL_N). split; [left; reflexivity | cbn [blk_addr blk_size fst snd]; unfold OL.S9_INFL_N; lia].
    - right; left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia.
    - right; right. destruct own as [[q D]|]; cbn [dptr] in Hx.
      + exists (q, D, payl). split; [right; left; reflexivity | cbn [blk_addr blk_size fst snd]; lia].
      + exfalso. pose proof (rx_data _ _ _ _ _ _ RI) as E. cbn in E. lia. }
  assert (G3 : reg_get R3 (Z_to_bv 5 3) = x3) by (rewrite (KEPT 3) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity).
  assert (G4 : reg_get R3 (Z_to_bv 5 4) = Z_to_bv 64 RATP) by (rewrite (KEPT 4) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity).
  assert (G2 : reg_get R3 (Z_to_bv 5 2) = Z_to_bv 64 (UU - 272)) by (rewrite (KEPT 2) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity).
  assert (EP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 (dptr own)) = dptr own) by (apply unsigned_lit; lia).
  rewrite ret_pc_even by (first [lia | reflexivity]).
  destruct rr as [pw|]; cbn [own_ret] in OR.
  -
    destruct HR as (w & junk & Ha0 & WR & HH3 & WBLK & _).
    pose proof (run_invX_malloc [(pp, p, OL.S9_INFL_N)] 1 own M M3 s s3 mo mo3 (UU - 272) pw w 32768 junk errv3 RI ltac:(lia) ltac:(lia)
                  HP MI3 ST3 ERR3 AUX3 HH3 OR WBLK ltac:(lia)) as RI3.
    destruct (own_live _ _ _ _ (rx_own _ _ _ _ _ _ RI3)) as [Hh3 Hl3].
    pose proof WR as (W1 & W2' & W3' & W4' & W5).
    destruct (blkX_facts _ _ _ _ _ _ (pw, w, 32768) RI3 ltac:(left; reflexivity)) as [_ WDJ]. cbn [blk_addr blk_size fst snd] in WDJ.
    assert (PW : p + 7176 <= w \/ w + 32768 <= p).
    { pose proof (RHEAP_blocks_nodup_proof _ _ _ HH3) as ND. cbn [map app blk_id fst] in ND.
      pose proof (RHEAP_blocks_disjoint_proof _ _ _ (pp, p, OL.S9_INFL_N) (pw, w, 32768) HH3 ltac:(right; left; reflexivity) ltac:(left; reflexivity)) as DJ.
      cbn [blk_id blk_addr blk_size fst snd] in DJ. unfold OL.S9_INFL_N in DJ. apply DJ.
      apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. left. exact E. }
    assert (EW : bv_unsigned (Z_to_bv 64 w) = w) by (apply unsigned_lit; lia).
    pose proof (lib_layout_of_inv _ _ _ _ _ _ pp p RI3 ltac:(right; left; reflexivity)) as LL.
    pose proof (OL.run_zb_S9 C7 R3 M3 UU (Z_to_bv 64 p) (Z_to_bv 64 (dptr own)) (Z_to_bv 64 w) payl ATOP SE (OZ.sregs R3 OZ.S_ALL)) as ZB.
    cbv zeta in ZB. rewrite EP, EQ, EW in ZB. unfold OL.S9_ZWD, OL.S9_WIN_N, OL.S9_INFL_N, OL.S9_BUF, OL.S9_BUF_N, OL.S9_IMG_TOP in ZB.
    destruct ZB as (R4 & M4 & HMS & FM & ER & EC).
    1: exact G2. 1: exact Ha0. 1: reflexivity. 1: exact ZW3. 1: exact LL.
    1: exact W2'. 1: lia. 1: lia. 1: lia. 1: lia.
    1: destruct own as [[q D]|]; cbn [dptr] in *; [lia | pose proof (rx_data _ _ _ _ _ _ RI) as E; cbn in E; lia].
    1: lia.
    1: { pose proof (wr_at_store_ok (run_segments psegs rc_inp rc_sp rc_mb) M3 w 32768 0 (Z.to_nat 32768) (rw_cells_wr_at _ _ _ _ 32768 WBLK ltac:(cbn [cells_size csize]; lia))
                       ltac:(lia) ltac:(lia)) as X.
         rewrite Z.add_0_r in X. exact X. }
    eapply rz_ours; [exact Hh3 | exact Hl3 | exact HMS |].
    destruct (wab_fp pp pw p w [(pw, w, 32768); (pp, p, OL.S9_INFL_N)] ltac:(right; left; reflexivity) ltac:(left; reflexivity) ltac:(lia) ltac:(lia))
      as [FW OUT].
    destruct (u2_fm_transport _ 1 own M3 M4 s3 mo3 _ _ _ _ _ _ RI3 FM FW (fun x => OUT x P4 W4') UF3)
      as (RI4 & AG4 & UF4).
    eapply (rz_end_regs R3 R4 _ M4 mo3 T UU w SE x3 (Z_to_bv 64 RATP) (Z_to_bv 64 r) x22 x23 x24 x25 x26 x27 ER G3 G4 eq_refl).
    intros z1 z5 z6 z7 z9 z12 z13 z15 z16 z17 z18 z19 z20 z28 z29 z30 z31.
    eapply (u2_ze1_rz pp pw p w M4 s3 mo3); [exact RI4 | exact UF4 | eapply so_agree_trans; eassumption | exact EC].
  -
    destruct HR as (Ha0 & HH3).
    pose proof (run_invX_null [(pp, p, OL.S9_INFL_N)] 1 own M M3 s s3 mo mo3 (UU - 272) errv3 RI ltac:(lia) ltac:(lia)
                  HP MI3 ST3 ERR3 AUX3 HH3 OR) as RI3.
    destruct (own_live _ _ _ _ (rx_own _ _ _ _ _ _ RI3)) as [Hh3 Hl3].
    pose proof (lib_layout_of_inv _ _ _ _ _ _ pp p RI3 ltac:(left; reflexivity)) as LL.
    pose proof (OL.run_zb0_S9 C7 R3 M3 UU (Z_to_bv 64 p) (Z_to_bv 64 (dptr own)) payl ATOP SE (OZ.sregs R3 OZ.S_ALL)) as ZB.
    cbv zeta in ZB. rewrite EP, EQ in ZB. unfold OL.S9_ZWD in ZB.
    destruct ZB as (R4 & M4 & HMS & FM & ER & EC).
    1: exact G2. 1: exact Ha0. 1: reflexivity. 1: exact ZW3. 1: exact LL.
    eapply rz_ours; [exact Hh3 | exact Hl3 | exact HMS |].
    destruct (wa_fp pp p [(pp, p, OL.S9_INFL_N)] ltac:(left; reflexivity) ltac:(lia)) as [FW OUT].
    destruct (u2_fm_transport _ 1 own M3 M4 s3 mo3 _ _ _ _ _ _ RI3 FM FW (fun x => OUT x P4) UF3) as (RI4 & AG4 & UF4).
    eapply (rz_end_regs R3 R4 _ M4 mo3 T UU p SE x3 (Z_to_bv 64 RATP) (Z_to_bv 64 r) x22 x23 x24 x25 x26 x27 ER G3 G4 eq_refl).
    intros z1 z5 z6 z7 z9 z12 z13 z15 z16 z17 z18 z19 z20 z28 z29 z30 z31.
    eapply (u2_ze2_rz pp p M4 s3 mo3); [exact RI4 | exact UF4 | eapply so_agree_trans; eassumption | exact (proj1 EC)].
Qed.

(* the za walk's entry (inflateInit_ after zalloc returned p): s1 = strm = UU, s3 = sourceLen, s4 = left,
   s5 = target_run's r. *)
Lemma u2_za_rz : forall (R' : bvmap 5 word) (pp : bptr) (p : Z) (M : word -> option byte) (s : PState) (mo : Model),
  reg_get R' (Z_to_bv 5 2) = Z_to_bv 64 (UU - 32) -> reg_get R' (Z_to_bv 5 9) = Z_to_bv 64 (UU) ->
  reg_get R' (Z_to_bv 5 10) = Z_to_bv 64 p -> reg_get R' (Z_to_bv 5 19) = Z_to_bv 64 payl ->
  reg_get R' (Z_to_bv 5 20) = Z_to_bv 64 OL.S9_BUF_N ->
  reg_get R' (Z_to_bv 5 3) = x3 -> reg_get R' (Z_to_bv 5 4) = Z_to_bv 64 RATP ->
  reg_get R' (Z_to_bv 5 21) = Z_to_bv 64 r ->
  reg_get R' (Z_to_bv 5 22) = x22 -> reg_get R' (Z_to_bv 5 23) = x23 -> reg_get R' (Z_to_bv 5 24) = x24 ->
  reg_get R' (Z_to_bv 5 25) = x25 -> reg_get R' (Z_to_bv 5 26) = x26 -> reg_get R' (Z_to_bv 5 27) = x27 ->
  run_invX [(pp, p, OL.S9_INFL_N)] 1 own M s mo -> UF M -> u2_za_cells sp0 M (dptr own) -> so_agree M0 M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' (Z_to_bv 64 OL.S9_ZA) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R' pp p M s mo G2 G9 G10 G19 G20 G3 G4 G21 G22 G23 G24 G25 G26 G27 RI UFM UZ AG.
  destruct (own_live _ _ _ _ (rx_own _ _ _ _ _ _ RI)) as [Hh Hl].
  pose proof (dptr_range _ _ _ _ _ _ RI) as DR.
  destruct (blkX_facts _ _ _ _ _ _ (pp, p, OL.S9_INFL_N) RI ltac:(left; reflexivity)) as [(P1 & P2 & P3 & P4 & P5) _].
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5. unfold OL.S9_INFL_N in P3, P4, P5.
  assert (EP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 (dptr own)) = dptr own) by (apply unsigned_lit; lia).
  pose proof (lib_layout_of_inv _ _ _ _ _ _ pp p RI ltac:(left; reflexivity)) as LL.
  destruct UZ as [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9].
  pose proof (OL.run_za_S9 C7 R' M UU (Z_to_bv 64 p) (Z_to_bv 64 (dptr own)) payl ATOP) as ZA.
  cbv zeta in ZA. rewrite EP, EQ in ZA.
  destruct ZA as (R2 & M2 & pc2 & HMS & FM & EX).
  1: exact G2. 1: exact G9. 1: exact G10. 1: exact G19. 1: exact G20. 1: exact LL.
  1: exact Z1. 1: exact Z2. 1: exact Z3. 1: exact Z4. 1: exact Z5. 1: exact Z6. 1: exact Z7. 1: exact Z8. 1: exact Z9.
  destruct (wa_fp pp p [(pp, p, OL.S9_INFL_N)] ltac:(left; reflexivity) ltac:(lia)) as [FW OUT].
  destruct (u2_fm_transport _ 1 own M M2 s mo _ _ _ _ _ _ RI FM FW (fun x => OUT x P4) UFM) as (RI2 & AG2 & UF2).
  assert (SEQ : OZ.sregs R' OL.S_ENTRY5 = SE) by (apply sregs_entry_of; assumption).
  rewrite SEQ in EX.
  destruct EX as [(-> & ER & EC) | (-> & W13 & W10 & W11 & W12 & W2 & W3 & W4 & ZW)];
    (eapply rz_ours; [exact Hh | exact Hl | exact HMS |]).
  - eapply (rz_end_regs R' R2 _ M2 mo T UU p SE x3 (Z_to_bv 64 RATP) (Z_to_bv 64 r) x22 x23 x24 x25 x26 x27 ER G3 G4 eq_refl).
    intros z1 z5 z6 z7 z9 z12 z13 z15 z16 z17 z18 z19 z20 z28 z29 z30 z31.
    eapply (u2_ze2_rz pp p M2 s mo); [exact RI2 | exact UF2 | eapply so_agree_trans; eassumption | exact (proj1 EC)].
  - eapply (u2_zw_rz R2 pp p M2 s mo); try eassumption.
    + rewrite (W3 : reg_get R2 (Z_to_bv 5 3) = _). exact G3.
    + rewrite (W4 : reg_get R2 (Z_to_bv 5 4) = _). exact G4.
    + eapply so_agree_trans; eassumption.
Qed.

End CALL.

Lemma u2_call_rz : forall own (M : word -> option byte) (s : PState) (mo : Model) (T : ShapeAlg.TSet) (r : Z)
    (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  run_inv 0 own M s mo ->
  (forall (M' : word -> option byte) (s' : PState) (mo' : Model) (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     run_inv 0 own M' s' mo' -> so_agree M M' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR (Z_to_bv 64 0x14c78) (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) y5 y6 y7
                                    (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) (Z_to_bv 64 0) (Z_to_bv 64 0) y12 y13 y14 y15 y16 y17
                                    (Z_to_bv 64 (oreg own)) (Z_to_bv 64 0) (Z_to_bv 64 0x32e60) (Z_to_bv 64 r)
                                    x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x14d24) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) x5 x6 x7
                                 (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) x10 x11 x12 x13 x14 x15 x16 x17
                                 (Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 0x32e60) (Z_to_bv 64 r)
                                 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14c54) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros own M s mo T r x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 RI HK.
  destruct (own_live _ _ _ _ (ri_own _ _ _ _ _ RI)) as [Hh Hl].
  (* no GOT cells here: inflateInit_ forms zcalloc / zcfree with auipc + addi *)
  (* (1.3.1 read them from the GOT at 0x21af0) *)
  pose proof (ri_icb _ _ _ _ _ RI) as ICB. pose proof (ri_mi _ _ _ _ _ RI) as MI.
  pose proof (munch_refl [(0x32e64, 0x32e65)] M) as MU0. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) M) as WM0.
  apply rz_evt; [exact Hh | exact Hl |].
  do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into Mc end.
  assert (RIc : run_inv 1 own Mc s mo) by (eapply run_inv_icb; [exact RI | exact MU0 | exact WM0 | exact MI | exact ICB]).
  assert (AGc : so_agree M Mc) by (apply so_agree_munch_icb; exact MU0).
  clear MU0 WM0 ICB MI.
  pose proof (run_invX_nil _ _ _ _ _ RIc) as RX.
  pose proof (dptr_range _ _ _ _ _ _ RX) as DR.
  eapply (u2_seg1_evt sp0 SP0 _ (dptr own) payl lo Mc);
    [lia | exact PAYL | lia | lia | exact (ri_stk _ _ _ _ _ RIc) | exact (ri_mi _ _ _ _ _ RIc) |].
  intros M1 MU WM MI1 UF1 UZ1.
  assert (FW : Forall (fp_u []) [(sp0 - 448, sp0 - 208)]) by (constructor; [left; cbn [fst snd]; lia | constructor]).
  pose proof (run_invX_mu [] 1 own Mc M1 s mo _ RX MU WM ltac:(eapply Forall_impl; [|exact FW]; intros iv H; left; exact H)) as RX1.
  pose proof (so_agree_trans _ _ _ AGc (so_agree_mu [] 1 own Mc M1 s mo _ RX MU FW)) as AG1.
  destruct (rx_err _ _ _ _ _ _ RX1) as [errv ERR].
  destruct (stk_split (run_segments psegs rc_inp rc_sp rc_mb) M1 lo (sp0 - 448) (sp0 - 208) (rx_stk _ _ _ _ _ _ RX1) ltac:(lia)) as [STl _].
  (* zalloc(7176): the 1.4 inflate_state *)
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (malloc_rz_any RR M1 mo s ([] ++ LBT own) (map blk_id [] ++ XT own) (G_std fs) 7176 lo sp0 errv) end.
  1: exact (rx_heap _ _ _ _ _ _ RX1). 1: exact (rx_own _ _ _ _ _ _ RX1). 1: apply frame_ok_G_std.
  1: exact (ci_aux _ _ _ (rx_cli _ _ _ _ _ _ RX1)).
  1: simp_regs; rewrite unsigned_lit by lia; lia.
  1: simp_regs; rewrite unsigned_lit by lia; exact STl.
  1: exact ALO.
  1: simp_regs; rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia.
  1: simp_regs; rewrite rerrno_lit'; exact ERR.
  1: exact (rx_mi _ _ _ _ _ _ RX1). 1: simp_regs; reflexivity. 1: simp_regs; reflexivity. 1: lia.
  intros R' M' mo' s' rr MR OR.
  destruct MR as (KEPT & MI' & ST' & [errv' ERR'] & AUX' & HP & _ & _ & HR).
  revert HP ST' ERR'. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP ST' ERR'.
  pose proof (same_on_rheap_pres _ _ _ _ HP) as SO.
  assert (UF' : u2_frames sp0 M' (dptr own) payl (Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 0x32e60) (Z_to_bv 64 r))
    by (apply (u2_frames_same_on sp0 SP0 _ _ _ _ _ _ _ _ _ UF1 SO); intros x Hx; left; lia).
  assert (UZ' : u2_za_cells sp0 M' (dptr own)) by (apply (u2_za_cells_same_on sp0 SP0 _ _ _ _ UZ1 SO); intros x Hx; left; lia).
  assert (AG' : so_agree M M') by (eapply so_agree_trans; [exact AG1 | eapply so_agree_heap; exact HP]).
  rewrite ret_pc_even by (first [lia | reflexivity]).
  destruct rr as [pp|]; cbn [own_ret] in OR.
  -
    destruct HR as (p & junk & Ha0 & PR & HH' & PBLK & _).
    pose proof (run_invX_malloc [] 1 own M1 M' s s' mo mo' (sp0 - 448) pp p 7176 junk errv' RX1 ltac:(lia) ltac:(lia)
                  HP MI' ST' ERR' AUX' HH' OR PBLK ltac:(lia)) as RI'.
    eapply (u2_za_rz own T r M x3 x19 x22 x23 x24 x25 x26 x27 HK R' pp p M' s' mo');
      [ rewrite (KEPT 2) by (cbn; trr_keep_section; tauto); simp_regs; f_equal; lia
      | rewrite (KEPT 9) by (cbn; trr_keep_section; tauto); simp_regs; f_equal; lia
      | exact Ha0
      | rewrite (KEPT 19) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 20) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 3) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 4) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 21) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 22) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 23) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 24) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 25) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 26) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | rewrite (KEPT 27) by (cbn; trr_keep_section; tauto); simp_regs; reflexivity
      | exact RI' | exact UF' | exact UZ' | exact AG' ].
  -
    destruct HR as (Ha0 & HH').
    pose proof (run_invX_null [] 1 own M1 M' s s' mo mo' (sp0 - 448) errv' RX1 ltac:(lia) ltac:(lia) HP MI' ST' ERR' AUX' HH' OR) as RI'.
    destruct (own_live _ _ _ _ (rx_own _ _ _ _ _ _ RI')) as [Hh' Hl'].
    use_kept KEPT. rewrite Ha0. forget_regs R'. clear KEPT.
    apply rz_evt; [exact Hh' | exact Hl' |].
    eapply (u2_seg_null_evt sp0 SP0 _ (dptr own) payl); [lia | exact UF' | exact UZ' |].
    intros z10 z13.
    eapply (u2_ret_rz own T r M x3 x19 x22 x23 x24 x25 x26 x27 HK M' s' mo'); [apply run_inv_nil; exact RI' | exact UF' | exact AG'].
Qed.

Lemma so_regions_fp : Forall (fun iv => (lo <= fst iv /\ snd iv <= sp0 - 208) \/ fp_so iv)
                             (fm_ivs (so_regions (Z_to_bv 64 (sp0 - 208)))).
Proof.
  unfold so_regions, fm_ivs, PF1_FR, fp_so. cbn [map fst snd].
  rewrite (unsigned_lit (sp0 - 208)) by lia. rewrite !unsigned_lit by lia.
  repeat constructor; cbn [fst snd]; lia.
Qed.

Abbreviation AFTER_LINE x3 r own y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 M :=
  (MS (mkR (Z_to_bv 64 0x14c78) (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) y5 y6 y7
           (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) y10 y11 y12 y13 y14 y15 y16 y17
           (Z_to_bv 64 (oreg own)) (Z_to_bv 64 0) (Z_to_bv 64 0x32e60) (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
           x24 x25 x26 x27 y28 y29 y30 y31)
      bvmap_empty (Z_to_bv 64 0x14c78) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Abbreviation LOOP_HEAD x1 x3 r own x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 M :=
  (MS (mkR x1 (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) x5 x6 x7
           (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 0x32e60) (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
           x24 x25 x26 x27 x28 x29 x30 x31)
      bvmap_empty (Z_to_bv 64 0x14c54) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Lemma line_first_rz : forall own (M : word -> option byte) (s : PState) (mo : Model) (T : ShapeAlg.TSet) (r : Z)
    (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  run_inv 0 own M s mo -> so_pristine M -> T [] ->
  (forall (M' : word -> option byte) (s' : PState) (mo' : Model) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     run_inv 0 own M' s' mo' -> so_wmode M' 0 ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (AFTER_LINE x3 r own y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 M') mo') T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (LOOP_HEAD x1 x3 r own x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 M) mo)
           (ShapeAlg.t_emit (Spec.W 1 [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]) T).
Proof.
  intros own M s mo T r x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 RI SOP T0 HK.
  eapply u2_call_rz; [exact RI|]. intros M1 s1 mo1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI1 AG1.
  pose proof (ri_own _ _ _ _ _ RI1) as [(L & _ & HKL & _) [_ HG]].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo1 (kl_minv _ _ _ HKL)) as Hl.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (printf0_first RR M1 mo1 (Z_to_bv 64 (sp0 - 208)) (bv_unsigned CAN) T) end.
  1: exact (pf_pre_of_inv _ _ _ _ _ RI1).
  1: exact (so_pristine_frame _ _ SOP AG1).
  1: reflexivity. 1: reflexivity. 1: reflexivity.
  1: exact (fd1_of_G_std _ _ _ HG).
  1: exact (minv_reader _ (kl_minv _ _ _ HKL)).   (* the stdio call's far-end reader *)
  1: exact Hh. 1: exact Hl. 1: exact T0.
  intros regs' M2 KCS FM SOW.
  assert (RI2 : run_inv 0 own M2 s1 mo1) by (eapply run_inv_fm; [exact RI1 | exact FM | exact so_regions_fp]).
  pose proof (keeps_cs_kept _ _ KCS) as KEPT.
  use_kept KEPT. forget_regs regs'.
  eapply HK; eassumption.
Qed.

Lemma line_next_rz : forall own (M : word -> option byte) (s : PState) (mo : Model) (T : ShapeAlg.TSet) (r : Z) (j : nat)
    (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  run_inv 0 own M s mo -> so_wmode M j -> (j < 512)%nat ->
  (forall (M' : word -> option byte) (s' : PState) (mo' : Model) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     run_inv 0 own M' s' mo' -> so_wmode M' (S j) ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (AFTER_LINE x3 r own y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 M') mo') T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (LOOP_HEAD x1 x3 r own x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 M) mo) T.
Proof.
  intros own M s mo T r j x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 RI SOW J HK.
  eapply u2_call_rz; [exact RI|]. intros M1 s1 mo1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI1 AG1.
  pose proof (ri_own _ _ _ _ _ RI1) as [(L & _ & HKL & _) [_ HG]].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo1 (kl_minv _ _ _ HKL)) as Hl.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (printf0_next_rz RR M1 mo1 (Z_to_bv 64 (sp0 - 208)) (bv_unsigned CAN) j T) end.
  1: exact (pf_pre_of_inv _ _ _ _ _ RI1).
  1: exact (so_wmode_frame _ _ _ SOW AG1).
  1: exact J.
  1: reflexivity. 1: reflexivity. 1: reflexivity.
  1: exact Hh. 1: exact Hl.
  intros regs' M2 KCS FM SOW2.
  assert (RI2 : run_inv 0 own M2 s1 mo1) by (eapply run_inv_fm; [exact RI1 | exact FM | exact so_regions_fp]).
  pose proof (keeps_cs_kept _ _ KCS) as KEPT.
  use_kept KEPT. forget_regs regs'.
  eapply HK; eassumption.
Qed.

Lemma trun_free_rz : forall own (M : word -> option byte) (s : PState) (mo : Model) (k : nat)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x2 = Z_to_bv 64 (sp0 - 208) -> x4 = Z_to_bv 64 RATP -> x18 = Z_to_bv 64 (oreg own) -> x22 = Z_to_bv 64 0 ->
  run_inv 0 own M s mo -> so_ok M k ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14c8c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (T_end fs k 0).
Proof.
  intros until x31. intros -> -> -> -> RI SO.
  pose proof (own_range _ _ _ _ _ RI) as OR.
  destruct RI as [HH HOWN DATA ST [errv ERR] MI (jt & t7 & t6 & t4 & t3 & t2 & t0 & FRT) CLI AXA ICB].
  pose proof HOWN as [(L & _ & HKL & _) _].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  assert (ET : T_end fs k 0 = T_end fs k (if b1 <? 128 then 0 else 0)) by (destruct (b1 <? 128); reflexivity).
  rewrite ET. clear ET.
  apply rz_evt; [exact Hh | exact Hl |].
  do 2 step.
  destruct own as [[q D]|]; cbn [oreg LBT XT] in *.
  -
    apply evt_done.
    lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
      eapply (free_rz_any RR M mo s [(q, D, payl); (pb, buf, cap)] [pb] (G_std fs) q D payl lo sp0 errv) end.
    1: exact HH. 1: left; reflexivity. 1: exact HOWN. 1: apply frame_ok_G_std. 1: exact (ci_aux _ _ _ CLI).
    1: simp_regs; rewrite unsigned_lit by lia; lia.
    1: simp_regs; rewrite unsigned_lit by lia; exact ST.
    1: exact ALO.
    1: simp_regs; rewrite unsigned_lit by lia; unfold RFREE_STACK; lia.
    1: simp_regs; rewrite rerrno_lit'; exact ERR.
    1: exact MI. 1: simp_regs; reflexivity. 1: simp_regs; reflexivity.
    intros R' M' mo' s' KEPT MI' ST' ERR' AUX' HP _ _ HH' HOWN'.
    use_kept KEPT. forget_regs R'. clear KEPT.
    revert HP ST' ERR'. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP ST' ERR'.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HH) as ND.
    rewrite (lb_remove_head (q, D, payl) [(pb, buf, cap)] ND) in HP, HH'.
    pose proof (rheap_pres_rw_cells _ _ _ _ _ _ HP FRT ltac:(left; lia)) as FRT'.
    pose proof (cli_inv_heap sp0 _ _ _ _ _ CLI HP ltac:(lia) AUX') as CLI'.
    pose proof (so_ok_heap so_ok so_ok_frame _ _ _ _ _ SO HP) as SO'.
    assert (AXA' : OAX.atx_cellsA M').
    { destruct AXA as [A1 A2]. unfold OAX.atx_cellsA, OAX.PATX in *. split; [rcl_static HP A1 | rcl_static HP A2]. }
    assert (ICB' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' 0x32e64 [C1 (Z_to_bv 8 0)]) by rcl_static HP ICB.
    pose proof HOWN' as [(L' & _ & HKL' & _) _].
    pose proof (kl_halt _ _ _ HKL') as Hh'.
    pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo' (kl_minv _ _ _ HKL')) as Hl'.
    clear HP FRT CLI SO ST MI ERR HH HOWN HKL Hh Hl DATA AXA ICB.
    apply rz_evt; [exact Hh' | exact Hl' |].
    do 3 step. apply evt_done.
    eapply (trun_epi_rz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M' mo' s' pb buf cap fs k 0 b1 tid lo jt t7 t6 t4 t3 t2 t0 errv);
      try eassumption; try reflexivity; try lia.
  -
    do 2 step. if_true. do 4 step. apply evt_done.
    eapply (trun_epi_rz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M mo s pb buf cap fs k 0 b1 tid lo jt t7 t6 t4 t3 t2 t0 errv);
      try eassumption; try reflexivity; try lia.
Qed.

Lemma swrap32_small : forall z, -2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

Lemma loop_next_rz : forall (n : nat) own (j : nat) (M : word -> option byte) (s : PState) (mo : Model)
    (x3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 : word),
  (S n <= 4)%nat -> (j + n < 512)%nat ->
  run_inv 0 own M s mo -> so_wmode M j ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (AFTER_LINE x3 (Z.of_nat (S n)) own y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 M) mo)
           (T_end fs (j + n) 0).
Proof.
  induction n as [|n IH]; intros own j M s mo x3 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 N4 JN RI SOW;
    pose proof (ri_own _ _ _ _ _ RI) as [(L & _ & HKL & _) _];
    pose proof (kl_halt _ _ _ HKL) as Hh;
    pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl;
    (apply rz_evt; [exact Hh | exact Hl |]).
  -
    zstep. step.
    replace (negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2)))) with true by (vm_compute; reflexivity). cbv iota.
    change (Z.of_nat 1) with 1. zstep. step.
    if_false. apply evt_done.
    rewrite Nat.add_0_r.
    eapply (trun_free_rz own M s mo j); try reflexivity; [exact RI | right; exact SOW].
  - zstep. step.
    replace (negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2)))) with true by (vm_compute; reflexivity). cbv iota.
    zstep. rewrite swrap32_small by lia.
    replace (Z.of_nat (S (S n)) + -1) with (Z.of_nat (S n)) by lia.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let C := fresh "C" in assert (C : c = true);
      [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply negb_true_iff, Z.eqb_neq; lia | rewrite C; cbv iota ] end.
    apply evt_done.
    eapply line_next_rz; [exact RI | exact SOW | lia |].
    intros M' s' mo' z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RI' SOW'.
    replace (j + S n)%nat with (S j + n)%nat by lia.
    eapply IH; [lia | lia | exact RI' | exact SOW'].
Qed.

Abbreviation T_succ n := (ShapeAlg.t_emit (Spec.W 1 [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]) (T_end fs n 0)).

Lemma T_end_nil : forall k code, T_end fs k code [].
Proof. intros. left. apply is_prefix_nil. Qed.

Lemma loop_rz : forall (n : nat) own (M : word -> option byte) (s : PState) (mo : Model)
    (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  (S n <= 4)%nat -> run_inv 0 own M s mo -> so_pristine M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (LOOP_HEAD x1 x3 (Z.of_nat (S n)) own x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 M) mo)
           (T_succ n).
Proof.
  intros n own M s mo x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 N4 RI SOP.
  eapply line_first_rz; [exact RI | exact SOP | apply T_end_nil |].
  intros M' s' mo' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI' SOW.
  eapply (loop_next_rz n own 0); [exact N4 | lia | exact RI' | exact SOW].
Qed.

Lemma trun_copy_rz : forall (n : nat) (q : bptr) (A payp : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (src junk jt : list byte) (t7 t6 t4 t3 t2 t0 errv : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x2 = Z_to_bv 64 (sp0 - 208) -> x4 = Z_to_bv 64 RATP -> x8 = Z_to_bv 64 payl -> x9 = Z_to_bv 64 payp -> x10 = Z_to_bv 64 A ->
  x21 = Z_to_bv 64 (Z.of_nat (S n)) -> x20 = Z_to_bv 64 0x32e60 ->
  (S n <= 4)%nat -> 1 <= payl ->
  RHEAP s [(q, A, payl); (pb, buf, cap)] M -> OWN [q; pb] (G_std fs) s mo ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A [CB (Z.to_nat payl) junk] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M payp src -> length src = Z.to_nat payl -> buf <= payp -> payp + payl <= buf + cap ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 208) [CB 8 jt; C8 t7; C8 t6; C8 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)); C8 t4; C8 t3; C8 t2;
                                C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x14a40)] ->
  cli_inv sp0 M tid -> so_pristine M ->
  OAX.atx_cellsA M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e64 [C1 (Z_to_bv 8 0)] ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14c00) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (T_succ n).
Proof.
  intros until x31. intros -> -> -> -> -> -> -> N4 P1 HH HOWN NBLK PB LEN PLO PHI ST ERR MI FRT CLI SOP [AXA AXB] ICB.
  pose proof (RHEAP_block_range_proof _ _ _ (q, A, payl) HH ltac:(left; reflexivity)) as (A1 & A2 & A3 & A4 & A5).
  pose proof (RHEAP_block_range_proof _ _ _ (pb, buf, cap) HH ltac:(right; left; reflexivity)) as (C1 & C2 & C3 & C4 & C5).
  cbn [blk_addr blk_size fst snd] in *.
  assert (DISJ : A + payl <= buf \/ buf + cap <= A).
  { pose proof (RHEAP_blocks_nodup_proof _ _ _ HH) as ND.
    pose proof (RHEAP_blocks_disjoint_proof _ _ _ (q, A, payl) (pb, buf, cap) HH ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
    cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
    intros E. apply NI. left. symmetry. exact E. }
  pose proof HOWN as [(L & _ & HKL & _) _].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  unfold OAX.PATX, OAX.PATX_CALL, OAX.PAEF_GUARD in AXA, AXB. change (602016 + 288) with 602304 in AXB.
  apply rz_evt; [exact Hh | exact Hl |].
  step.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia | rewrite C; cbv iota; clear C ] end.
  do 4 step.
  eapply evt_cut.
  { eapply memcpy_callv with (src := src) (junk := junk);
      [exact PB | exact LEN | exact NBLK | lia | lia | lia | lia | exact MI]. }
  cbv beta. intros ms' PO.
  destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB2 & _).
  assert (HH2 : RHEAP s [(q, A, payl); (pb, buf, cap)] m2).
  { eapply RHEAP_frame_proof; [exact HH | exact MUc | exact WMc |].
    constructor; [| constructor]. right; right. exists (q, A, payl). split; [left; reflexivity|]. cbn. lia. }
  assert (CLI2 : cli_inv sp0 m2 tid).
  { eapply cli_inv_munch; [exact ATOPE | exact CLI | exact MUc | exact WMc |].
    constructor; [| constructor]. left. right; left. cbn [fst snd]. lia. }
  assert (SOP2 : so_pristine m2).
  { eapply so_pristine_frame; [exact SOP|]. intros i Hi. apply MUc. rewrite unsigned_lit by (unfold so_dom in Hi; lia).
    cbn [outside]. unfold so_dom in Hi. split; [lia | exact I]. }
  clear NBLK PB. unfold RERRNO in ERR. transport_after_call (run_segments psegs rc_inp rc_sp rc_mb) M m2 MUc WMc.
  replace (ret_pc (Z_to_bv 64 0x14c14)) with (Z_to_bv 64 0x14c14) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 4 step. apply evt_done.
  eapply (loop_rz n (Some (q, A)) m2 s mo); [exact N4 | | exact SOP2].
  constructor; cbn [LBT XT]; try assumption.
  - exists src. exact NB2.
  - exists errv. assumption.
  - exists jt, t7, t6, t4, t3, t2, t0. assumption.
  - split; assumption.
Qed.

Lemma trun_null_rz : forall (M : word -> option byte) (s : PState) (mo : Model) (jt : list byte) (t7 t6 t4 t3 t2 t0 errv : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x2 = Z_to_bv 64 (sp0 - 208) -> x4 = Z_to_bv 64 RATP -> x10 = Z_to_bv 64 0 ->
  RHEAP s [(pb, buf, cap)] M -> OWN [pb] (G_std fs) s mo ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 208) [CB 8 jt; C8 t7; C8 t6; C8 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)); C8 t4; C8 t3; C8 t2;
                                C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x14a40)] ->
  cli_inv sp0 M tid -> so_pristine M ->
  OAX.atx_cellsA M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e64 [C1 (Z_to_bv 8 0)] ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14c00) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (T_end fs 0 (if b1 <? 128 then 2 else 0)).
Proof.
  intros until x31. intros -> -> -> HH HOWN ST ERR MI FRT CLI SOP AXA ICB.
  pose proof HOWN as [(L & _ & HKL & _) _].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  apply rz_evt; [exact Hh | exact Hl |].
  step. if_true. do 2 step. apply evt_done.
  eapply (trun_epi_rz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M mo s pb buf cap fs 0%nat 2 b1 tid lo jt t7 t6 t4 t3 t2 t0 errv);
    try eassumption; try reflexivity; try lia.
  left. split; [reflexivity | exact SOP].
Qed.

Definition calls_n (cfgl c2 : Z) : nat := if cfgl =? 0 then 0%nat else Z.to_nat (Z.land c2 3).

Lemma land3_range : forall c, 0 <= c -> 0 <= Z.land c 3 <= 3.
Proof.
  intros c Hc. split; [apply Z.land_nonneg; lia|].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3.
  pose proof (Z.mod_pos_bound c 4 ltac:(lia)). change (2^2) with 4. lia.
Qed.

Lemma trun_entry_evt : forall (Q : machine_state -> Prop) (cfgl c2 payp : Z) (M : word -> option byte) (src : list byte)
    (x3 x5 x6 x7 x8 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= cfgl < 32768 -> 0 <= c2 < 256 -> 0 <= payp -> payp + payl <= ATOP -> buf + 2 + 1 <= ATOP -> 0 <= buf ->
  (buf + cap <= 0x10000 \/ 0x94000 <= buf) -> buf + 6 <= payp -> payp + payl <= buf + cap ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 128) -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e60 [C1 (Z_to_bv 8 0)] -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x21bb0 [C8 (Z_to_bv 64 0)] ->
  OAX.atx_cells0 M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M OAX.PNEEDLK [C1 (Z_to_bv 8 0)] -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e64 [C1 (Z_to_bv 8 0)] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M (buf + 2) [Z_to_bv 8 c2] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M payp src -> length src = Z.to_nat payl ->
  (forall (M1 : word -> option byte) (jt : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     munch [(sp0 - 256, sp0 - 128); (0x32e60, 0x32e61); (0x92fa0, 0x931c0)] M M1 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M1 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M1 ->
     stk (run_segments psegs rc_inp rc_sp rc_mb) M1 lo (sp0 - 208) ->
     rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M1 (sp0 - 208) [CB 8 jt; C8 x23; C8 x22; C8 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)); C8 x20; C8 x19; C8 x18;
                                    C8 (Z_to_bv 64 buf); C8 x8; C8 (Z_to_bv 64 0x14a40)] ->
     bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M1 payp src ->
     OAX.atx_cellsA M1 -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M1 0x32e64 [C1 (Z_to_bv 8 0)] ->
     Q (MS (mkR y1 (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 payl) (Z_to_bv 64 payp)
                y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 cfgl) (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 0x32e60) (Z_to_bv 64 (Z.of_nat (S (calls_n cfgl c2))))
                x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
           bvmap_empty (Z_to_bv 64 (if payl =? 0 then 0x14c44 else 0x14bf8)) fc0 None M1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR (Z_to_bv 64 0x14a40) (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 buf)
                       (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 cfgl) (Z_to_bv 64 payp) (Z_to_bv 64 payl) x14 x15 x16 x17
                       x18 x19 x20 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x14b9c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q cfgl c2 payp M src x3 x5 x6 x7 x8 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         CFG C2 PP0 PPA BA B0 BIMG PLO PHI ST MI FL GOT [AX0 AX0B] NL ICB CB PB LEN HK.
  pose proof (munch_refl [(sp0 - 256, sp0 - 128); (0x32e60, 0x32e61); (0x92fa0, 0x931c0)] M) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) M) as WM.
  unfold OAX.PATX, OAX.PNEEDLK in AX0, AX0B, NL. change (602016 + 288) with 602304 in AX0B.
  step; carve_frame 80%nat ST.
  replace (sp0 + -128 + -80) with (sp0 + -208) in * by lia.
  do 9 step. do 8 step. if_true.
  do 5 step.
  assert (USP : bv_unsigned (Z_to_bv 64 (sp0 + -208)) = sp0 + -208) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply OAX.atexit_guard_spec; [rewrite USP; exact ST | split; [exact AX0 | exact AX0B] | exact NL | exact MI | reflexivity | rewrite USP; lia | lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (v0 & v1 & v2 & c1 & c2' & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & STc & [AXA AXB]).
  rewrite USP in MUc, STc. unfold OAX.PATX, OAX.PATX_N, OAX.PATX_CALL, OAX.PAEF_GUARD in MUc, AXA, AXB.
  change (602016 + 544) with 602560 in MUc. change (602016 + 288) with 602304 in AXB.
  clear AX0 AX0B NL ST. transport_after_call (run_segments psegs rc_inp rc_sp rc_mb) m0 m2 MUc WMc.
  replace (ret_pc (Z_to_bv 64 0x14c30)) with (Z_to_bv 64 0x14c30) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. if_true. do 3 step. if_true.
  destruct (Z.eq_dec cfgl 0) as [-> | NZ].
  -
    step. if_true. step. step.
    change (calls_n 0 c2) with 0%nat in HK. change (Z.of_nat 1) with 1 in HK.
    destruct (Z.eqb_spec payl 0) as [EP|NP].
    + lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let C := fresh "C" in assert (C : c = false);
        [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply negb_false_iff, Z.eqb_eq; lia | rewrite C; cbv iota; clear C ] end.
      apply evt_done.
      lazymatch goal with |- Q (MS _ _ _ _ _ ?mx _) => eapply (HK mx) end; try eassumption. split; assumption.
    + lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let C := fresh "C" in assert (C : c = true);
        [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply negb_true_iff, Z.eqb_neq; lia | rewrite C; cbv iota; clear C ] end.
      apply evt_done.
      lazymatch goal with |- Q (MS _ _ _ _ _ ?mx _) => eapply (HK mx) end; try eassumption. split; assumption.
  - step.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let C := fresh "C" in assert (C : c = false);
      [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia | rewrite C; cbv iota; clear C ] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) mx (buf + 2) [Z_to_bv 8 c2] 0 1%nat ltac:(eassumption) ltac:(lia) ltac:(cbn; lia)) as HR end.  (* the run's instance is still an evar inside the term, so `assumption` cannot match CB *)
    cbn [firstn skipn Z.to_nat] in HR.
    zstep. zstep. zstep. zstep.
    pose proof (land3_range c2 ltac:(lia)) as L3.
    assert (ES4 : Z.of_nat (S (calls_n cfgl c2)) = Z.land c2 3 + 1).
    { unfold calls_n. destruct (Z.eqb_spec cfgl 0); [contradiction|]. lia. }
    rewrite ES4 in HK.
    replace (bv_unsigned (Z_to_bv 8 c2)) with c2
      by (symmetry; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    destruct (Z.eqb_spec payl 0) as [EP|NP].
    + lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let C := fresh "C" in assert (C : c = true);
        [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_eq; lia | rewrite C; cbv iota; clear C ] end.
      apply evt_done.
      lazymatch goal with |- Q (MS _ _ _ _ _ ?mx _) => eapply (HK mx) end; try eassumption. split; assumption.
    + lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let C := fresh "C" in assert (C : c = false);
        [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia | rewrite C; cbv iota; clear C ] end.
      apply evt_done.
      lazymatch goal with |- Q (MS _ _ _ _ _ ?mx _) => eapply (HK mx) end; try eassumption. split; assumption.
Qed.

Definition T_run (n : nat) : ShapeAlg.TSet :=
  if payl =? 0 then T_succ n else ShapeAlg.t_alt2 (T_end fs 0 (if b1 <? 128 then 2 else 0)) (T_succ n).

Theorem trun_rz : forall (cfgl c2 payp : Z) (M : word -> option byte) (s : PState) (mo : Model) (src : list byte) (errv : word)
    (x3 x5 x6 x7 x8 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= cfgl < 32768 -> 0 <= c2 < 256 -> buf + 6 <= payp -> payp + payl <= buf + cap ->
  RHEAP s [(pb, buf, cap)] M -> OWN [pb] (G_std fs) s mo -> drv_state s -> room (2 ^ 27) mo ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 128) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e60 [C1 (Z_to_bv 8 0)] -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x21bb0 [C8 (Z_to_bv 64 0)] ->
  OAX.atx_cells0 M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x32e64 [C1 (Z_to_bv 8 0)] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M (buf + 2) [Z_to_bv 8 c2] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M payp src -> length src = Z.to_nat payl ->
  cli_inv sp0 M tid -> so_pristine M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR (Z_to_bv 64 0x14a40) (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 buf)
                                 (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 cfgl) (Z_to_bv 64 payp) (Z_to_bv 64 payl) x14 x15 x16 x17
                                 x18 x19 x20 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14b9c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (T_run (calls_n cfgl c2)).
Proof.
  intros cfgl c2 payp M s mo src errv x3 x5 x6 x7 x8 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         CFG C2 PLO PHI HH HOWN [HACT HMETA] HROOM ST ERR MI FL GOT AX0 ICB CB PB LEN CLI SOP.
  pose proof (RHEAP_block_range_proof _ _ _ (pb, buf, cap) HH ltac:(left; reflexivity)) as (BR1 & BR2 & BR3 & BR4 & BR5).
  cbn [blk_addr blk_size fst snd] in *.
  pose proof HOWN as [(L & _ & HKL & _) _].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  assert (N4 : (S (calls_n cfgl c2) <= 4)%nat).
  { unfold calls_n. destruct (cfgl =? 0); [lia|]. pose proof (land3_range c2 ltac:(lia)). lia. }
  apply rz_evt; [exact Hh | exact Hl |].
  eapply (trun_entry_evt _ cfgl c2 payp M src); try eassumption; try lia.
  1: exact (needlk_of_RHEAP _ _ _ HH).
  intros M1 jt y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU WM MI1 ST1 FRT PB1 AXA1 ICB1.
  assert (FW : Forall (fp_ok sp0) [(sp0 - 256, sp0 - 128); (0x32e60, 0x32e61); (0x92fa0, 0x931c0)]).
  { constructor; [left; left; cbn [fst snd]; lia | constructor; [left; right; right; left; cbn [fst snd]; lia |
    constructor; [left; right; right; right; cbn [fst snd]; lia | constructor]]]. }
  assert (HH1 : RHEAP s [(pb, buf, cap)] M1).
  { eapply RHEAP_frame_proof; [exact HH | exact MU | exact WM |].
    constructor; [left; cbn [fst snd]; lia | constructor; [| constructor; [|constructor]]];
      right; left; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; cbn [fst snd]; lia. }
  assert (CLI1 : cli_inv sp0 M1 tid) by (eapply cli_inv_munch; eassumption).
  assert (SOP1 : so_pristine M1).
  { eapply so_pristine_frame; [exact SOP|]. intros i Hi. apply MU. unfold so_dom in Hi. rewrite unsigned_lit by lia.
    cbn [outside]. lia. }
  assert (ERR1 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M1 RERRNO [C4 errv]).
  { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold RERRNO. cbn. lia. }
  unfold T_run. destruct (Z.eqb_spec payl 0) as [EP|NP].
  -
    apply rz_evt; [exact Hh | exact Hl |].
    do 4 step. apply evt_done.
    eapply (loop_rz (calls_n cfgl c2) None M1 s mo); [exact N4 | | exact SOP1].
    constructor; cbn [LBT XT]; try assumption.
    + exists errv. exact ERR1.
    + do 7 eexists. exact FRT.
  -
    apply rz_evt; [exact Hh | exact Hl |].
    do 2 step. apply evt_done.
    lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
      eapply (malloc_rz_driver RR M1 mo s [(pb, buf, cap)] [pb] (G_std fs) payl lo sp0 errv) with (Bd := 2 ^ 27) end.
    1: exact HH1. 1: exact HOWN. 1: apply frame_ok_G_std. 1: exact (ci_aux _ _ _ CLI1).
    1: simp_regs; rewrite unsigned_lit by lia; lia.
    1: simp_regs; rewrite unsigned_lit by lia; exact ST1.
    1: exact ALO.
    1: simp_regs; rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia.
    1: simp_regs; rewrite rerrno_lit'; exact ERR1.
    1: exact MI1. 1: simp_regs; reflexivity. 1: simp_regs; reflexivity. 1: lia.
    1: exact HACT. 1: exact HMETA. 1: exact HROOM. 1: lia. 1: lia. 1: lia.
    1: apply T_end_nil. 1: left; apply is_prefix_nil.
    intros R' M' mo' s' r MR OR.
    destruct MR as (KEPT & MI' & ST' & [errv' ERR'] & AUX' & HP & _ & _ & HR).
    revert HP ST' ERR'. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP ST' ERR'.
    pose proof (rheap_pres_rw_cells _ _ _ _ _ _ HP FRT ltac:(left; lia)) as FRT'.
    pose proof (cli_inv_heap sp0 _ _ _ _ _ CLI1 HP ltac:(lia) AUX') as CLI'.
    assert (SOP' : so_pristine M').
    { eapply so_pristine_frame; [exact SOP1|]. intros i Hi. unfold so_dom in Hi.
      destruct (HP i ltac:(lia)) as [E _]; [| exact E].
      unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia. }
    assert (AXA' : OAX.atx_cellsA M').
    { destruct AXA1 as [A1 A2]. unfold OAX.atx_cellsA, OAX.PATX in *. split; [rcl_static HP A1 | rcl_static HP A2]. }
    assert (ICB' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' 0x32e64 [C1 (Z_to_bv 8 0)]) by rcl_static HP ICB1.
    destruct r as [q|]; cbn [own_ret] in OR.
    + destruct HR as (A & junk & Ha0 & _ & HH' & NBLK & _).
      assert (PB' : bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M' payp src).
      { eapply rheap_pres_bytes_at; [exact HP | exact PB1 |]. right; right. exists (pb, buf, cap).
        split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
      use_kept KEPT. rewrite Ha0. forget_regs R'.
      rewrite ret_pc_even by (first [lia | reflexivity]).
      eapply (trun_copy_rz (calls_n cfgl c2) q A payp M' s' mo' src junk jt _ _ _ _ _ _ errv');
        try eassumption; try reflexivity; try lia.
    + destruct HR as (Ha0 & HH').
      use_kept KEPT. rewrite Ha0. forget_regs R'.
      rewrite ret_pc_even by (first [lia | reflexivity]).
      eapply (trun_null_rz M' s' mo' jt _ _ _ _ _ _ errv'); try eassumption; try reflexivity.
Qed.

End RUN.
