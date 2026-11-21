(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx. (* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require PropExec StdModel ShapeAlg Spec U0TargetPre U0World U0StdioDefs U0ExitBase U0Exit
  RefMemcpyLib Frame Hoare SymRun U0FuzzStmt U0Fuzz U0Atexit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KLink. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP F_memcpy.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift2 MrRoom MrRulesU0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.MrP0 Require Import U0HeapPre U0HBase U0HConv U0SoDefs U0PrintfFirst U0PrintfNext U0TrTail U0TrInv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.MrP0 Require Export U0SoOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module OAX := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.U0Atexit.

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
        F (Z_to_bv 64 0x1cf88) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
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
  OAX.atx_cellsA M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc84 [C1 (Z_to_bv 8 0)] -> OSD.atx_R M.
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
                                C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x13ee4)] ->
  cli_inv sp0 M tid -> 1 <= tid <= 4194303 -> so_ok M k ->
  OAX.atx_cellsA M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc84 [C1 (Z_to_bv 8 0)] ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14144) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
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
Hypothesis LO : lo <= sp0 - 208 - 8192.
Hypothesis PAYL : 0 <= payl < 2 ^ 26.

Definition LBT (own : option (bptr * Z)) : list block :=
  match own with None => [(pb, buf, cap)] | Some (q, D) => [(q, D, payl); (pb, buf, cap)] end.
Definition XT (own : option (bptr * Z)) : list bptr := match own with None => [pb] | Some (q, _) => [q; pb] end.
Definition dptr (own : option (bptr * Z)) : Z := match own with None => 0x2fc90 | Some (_, D) => D end.
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
                                          C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x13ee4)];
  ri_cli  : cli_inv sp0 M tid;
  ri_atx  : OAX.atx_cellsA M;
  ri_icb  : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc84 [C1 (Z_to_bv 8 cb)]
}.

Lemma own_range : forall cb own M s mo, run_inv cb own M s mo ->
  match own with None => True | Some (_, D) => 0 < D /\ D mod 16 = 0 /\ D + payl <= ATOP /\ (D + payl <= 0x10000 \/ 0x51000 <= D) end.
Proof.
  intros cb [[q D]|] M s mo RI; [|exact I].
  pose proof (RHEAP_block_range_proof _ _ _ (q, D, payl) (ri_heap _ _ _ _ _ RI) ltac:(left; reflexivity)) as (H1 & H2 & H3 & H4 & H5).
  cbn in *. auto.
Qed.

Lemma run_inv_fm : forall cb own M M' s mo rs,
  run_inv cb own M s mo -> OF.frame_mod M M' rs ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp0 - 208) \/ fp_so iv) (fm_ivs rs) ->  (* ri_stk's window *)
  run_inv cb own M' s mo.
Proof.
  intros cb own M M' s mo rs RI FM FW. pose proof (own_range _ _ _ _ _ RI) as OR.
  destruct RI as [HH HOWN DATA ST ERR MI FRT CLI AXA ICB].
  destruct (munch_of_frame_mod _ _ _ FM) as [MU WM].
  assert (FOK : Forall (fp_ok sp0) (fm_ivs rs)).
  { eapply Forall_impl; [|exact FW]. intros iv [H|H]; [left; left; lia | right; exact H]. }
  assert (DJ : forall A n, 0 <= n -> (A + n <= ATOP \/ sp0 - 208 <= A) -> (A + n <= 0x1fb38 \/ 0x1fc20 <= A) -> (A + n <= 0x50450 \/ 0x50858 <= A) ->
               disjoint_from (fm_ivs rs) A n).
  { intros A n Hn HA HB HC. clear - FW SP0 ATOPE ALO Hn HA HB HC. induction FW as [|[a b] W H _ IH]; cbn; [exact I|]. split; [|exact IH].
    unfold fp_so in H. cbn [fst snd] in H. lia. }
  constructor.
  - eapply RHEAP_frame_proof; [exact HH | exact MU | exact WM |].
    eapply Forall_impl; [|exact FW]. intros [a b] [H|[H|H]]; unfold rclient_write_ok; cbn [fst snd] in *.
    + left. lia.
    + right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
    + right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
  - exact HOWN.
  - destruct own as [[q D]|]; [|exact DATA]. destruct DATA as [src DATA]. exists src.
    eapply rw_cells_transport; [exact DATA | exact MU | exact WM |].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply DJ; lia.
  - apply (stk_wmono M M'); [exact ST | lia | exact WM].
  - destruct ERR as [errv ERR]. exists errv. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |].
    cbn [cells_size csize]. unfold RERRNO. apply DJ; lia.
  - eapply mem_inv_munch; [exact MI | exact MU | |].
    + intros a Ha.
      clear - FW SP0 ATOPE ALO Ha. induction FW as [|[a' b'] W H _ IH]; cbn; [exact I|]. split; [|exact IH].
      unfold fp_so in H. cbn [fst snd] in H. lia.
    + (* the stack class is in ri_stk's window; fp_so's ranges
         lie in the image *)
      rewrite Forall_forall in FW |- *. intros [l0 h0] IN a Ha Hout. cbn [fst snd] in Ha.
      destruct (FW _ IN) as [H|H]; unfold fp_so in *; cbn [fst snd] in *.
      * pose proof ST as (_ & _ & STK). exact (proj1 (STK a ltac:(lia))).
      * lia.
  - destruct FRT as (jt & t7 & t6 & t4 & t3 & t2 & t0 & FRT). exists jt, t7, t6, t4, t3, t2, t0.
    eapply rw_cells_transport; [exact FRT | exact MU | exact WM |]. cbn [cells_size csize]. apply DJ; lia.
  - eapply cli_inv_munch; eassumption.
  - eapply OAX.atx_cellsA_munch; [exact MU | exact WM | | exact AXA]. unfold OAX.PATX, OAX.PATX_N. apply DJ; lia.
  - eapply rw_cells_transport; [exact ICB | exact MU | exact WM |]. cbn [cells_size csize]. apply DJ; lia.
Qed.

Lemma run_inv_icb : forall cb cb' own M M' s mo,
  run_inv cb own M s mo -> munch [(0x2fc84, 0x2fc85)] M M' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' 0x2fc84 [C1 (Z_to_bv 8 cb')] -> run_inv cb' own M' s mo.
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

Lemma so_agree_munch_icb : forall M M', munch [(0x2fc84, 0x2fc85)] M M' -> so_agree M M'.
Proof. intros M M' MU i Hi. apply MU. unfold so_dom in Hi. rewrite unsigned_lit by lia. cbn [outside]. lia. Qed.

Lemma so_agree_trans : forall M1 M2 M3, so_agree M1 M2 -> so_agree M2 M3 -> so_agree M1 M3.
Proof. intros M1 M2 M3 A B i Hi. rewrite (B i Hi). apply A. exact Hi. Qed.

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
  - intros i Hi. destruct (Z_lt_le_dec i 0x1e000) as [L|L]; [apply mem_inv_none; [exact MI | lia]|].
    destruct (Z_lt_le_dec i 0x1ea08) as [L2|L2].
    + apply (PR 0x1e000 0x1ea08); [cbn; tauto | lia].
    + apply (PR 0x1ea10 0x1fb38); [cbn; tauto | lia].
  - exact G1.
  - rewrite Z_to_bv_bv_unsigned. exact G2.
  - pose proof (bv_unsigned_in_range 64 CAN) as R. unfold bv_modulus in R. lia.
Qed.

Lemma fuzz_call_rz : forall own (M : word -> option byte) (s : PState) (mo : Model) (T : ShapeAlg.TSet) (r : Z)
    (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  run_inv 0 own M s mo ->
  (forall (M' : word -> option byte) (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     run_inv 0 own M' s mo -> so_agree M M' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR (Z_to_bv 64 0x1411c) (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) y5 y6 y7
                                    (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) (Z_to_bv 64 0) (Z_to_bv 64 0) y12 y13 y14 y15 y16 y17
                                    (Z_to_bv 64 (oreg own)) (Z_to_bv 64 0) (Z_to_bv 64 0x2fc80) (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
                                    x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x141c8) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) x5 x6 x7
                                 (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) x10 x11 x12 x13 x14 x15 x16 x17
                                 (Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 0x2fc80) (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
                                 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x140f8) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros own M s mo T r x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 RI HK.
  pose proof (own_range _ _ _ _ _ RI) as OR.
  pose proof (ri_own _ _ _ _ _ RI) as [(L & _ & HKL & _) _].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  pose proof (ri_icb _ _ _ _ _ RI) as ICB. pose proof (ri_mi _ _ _ _ _ RI) as MI.
  pose proof (munch_refl [(0x2fc84, 0x2fc85)] M) as MU. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) M) as WM.
  apply rz_evt; [exact Hh | exact Hl |].
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into M1 end.
  assert (RI1 : run_inv 1 own M1 s mo) by (eapply run_inv_icb; [exact RI | exact MU | exact WM | exact MI | exact ICB]).
  assert (AG1 : so_agree M M1) by (apply so_agree_munch_icb; exact MU).
  clear MU WM ICB MI.
  do 3 step. apply evt_done.
  assert (USP : bv_unsigned (Z_to_bv 64 (sp0 - 208)) = sp0 - 208) by (apply unsigned_lit; lia).
  assert (DR : 1 <= dptr own /\ dptr own + payl < 2 ^ 64 /\ (1 <= payl -> dptr own + payl <= sp0 - 208 - 240)).
  { destruct own as [[q D]|]; cbn [dptr]; [lia|]. pose proof (ri_data _ _ _ _ _ RI1) as E. cbn in E. lia. }
  assert (UD : bv_unsigned (Z_to_bv 64 (dptr own)) = dptr own) by (apply unsigned_lit; lia).
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    destruct (U0Fuzz.u0_fuzz RR M1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)) (Z_to_bv 64 0x1410c) (Z_to_bv 64 (sp0 - 208)) (Z_to_bv 64 (dptr own)) payl)
      as (regs' & M' & HMS & KCS & A0 & FM) end.
  1: reflexivity.
  1: apply Hoare.ret_ok_even; reflexivity.
  1: reflexivity. 1: reflexivity. 1: reflexivity.
  1: lia. 1: rewrite UD; lia. 1: rewrite UD; lia. 1: rewrite USP; lia.
  {
    intros Hn i Hi. rewrite UD. destruct own as [[q D]|]; [|pose proof (ri_data _ _ _ _ _ RI1) as E; cbn in E; lia].
    destruct (ri_data _ _ _ _ _ RI1) as [src [[[LEN _] B] _]]. cbn [cells_bytes cbytes dptr] in *. rewrite app_nil_r in B.
    cbn [cell_wf] in LEN.
    assert (LI : (Z.to_nat i + 1 <= length src)%nat) by lia.
    pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M1 D src (Z.to_nat i) 1%nat B LI) as X.
    rewrite Z2Nat.id in X by lia.
    destruct (skipn (Z.to_nat i) src) as [|b rest] eqn:SK.
    { exfalso. pose proof (f_equal (@length _) SK) as SL. rewrite length_skipn in SL. cbn in SL. lia. }
    exists b. exact X. }
  1: rewrite USP; apply (store_ok_of_stk M1 lo (sp0 - 208)); [exact (ri_stk _ _ _ _ _ RI1) | lia | lia].
  1: rewrite UD, USP; lia.
  1: intros j Hj; apply mem_inv_none; [exact (ri_mi _ _ _ _ _ RI1) | lia].
  replace (Z_to_bv 64 82448) with (0x14210%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_ours; [exact Hh | exact Hl | exact HMS |].
  rewrite USP in FM.
  assert (RI' : run_inv 1 own M' s mo).
  { eapply run_inv_fm; [exact RI1 | exact FM |]. unfold fm_ivs. cbn [map fst snd]. rewrite unsigned_lit by lia.
    constructor; [|constructor]. left. cbn [fst snd]. lia. }
  assert (AG : so_agree M M').
  { eapply so_agree_trans; [exact AG1|]. eapply so_agree_of_frame; [exact FM|]. intros i Hi. cbn [OF.outside]. split; [|exact I].
    unfold OF.in_rng, so_dom in *. rewrite !unsigned_lit by lia. lia. }
  pose proof (keeps_cs_kept _ _ KCS) as KEPT.
  use_kept KEPT. rewrite (A0 : reg_get regs' (Z_to_bv 5 10) = _). forget_regs regs'.
  clear RI RI1 AG1 KEPT FM HMS KCS A0.
  pose proof (ri_icb _ _ _ _ _ RI') as ICB. pose proof (ri_mi _ _ _ _ _ RI') as MI.
  pose proof (munch_refl [(0x2fc84, 0x2fc85)] M') as MU. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) M') as WM.
  apply rz_evt; [exact Hh | exact Hl |].
  do 4 step. apply evt_done.
  lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into M2 end.
  assert (RI2 : run_inv 0 own M2 s mo) by (eapply run_inv_icb; [exact RI' | exact MU | exact WM | exact MI | exact ICB]).
  assert (AG2 : so_agree M M2) by (eapply so_agree_trans; [exact AG | apply so_agree_munch_icb; exact MU]).
  apply HK; assumption.
Qed.
Lemma so_regions_fp : Forall (fun iv => (lo <= fst iv /\ snd iv <= sp0 - 208) \/ fp_so iv)
                             (fm_ivs (so_regions (Z_to_bv 64 (sp0 - 208)))).
Proof.
  unfold so_regions, fm_ivs, PF1_FR, fp_so. cbn [map fst snd].
  rewrite (unsigned_lit (sp0 - 208)) by lia. rewrite !unsigned_lit by lia.
  repeat constructor; cbn [fst snd]; lia.
Qed.

Abbreviation AFTER_LINE x3 r own y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 M :=
  (MS (mkR (Z_to_bv 64 0x1411c) (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) y5 y6 y7
           (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) y10 y11 y12 y13 y14 y15 y16 y17
           (Z_to_bv 64 (oreg own)) (Z_to_bv 64 0) (Z_to_bv 64 0x2fc80) (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
           x24 x25 x26 x27 y28 y29 y30 y31)
      bvmap_empty (Z_to_bv 64 0x1411c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Abbreviation LOOP_HEAD x1 x3 r own x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 M :=
  (MS (mkR x1 (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) x5 x6 x7
           (Z_to_bv 64 payl) (Z_to_bv 64 (dptr own)) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (oreg own)) x19 (Z_to_bv 64 0x2fc80) (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
           x24 x25 x26 x27 x28 x29 x30 x31)
      bvmap_empty (Z_to_bv 64 0x140f8) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Lemma line_first_rz : forall own (M : word -> option byte) (s : PState) (mo : Model) (T : ShapeAlg.TSet) (r : Z)
    (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  run_inv 0 own M s mo -> so_pristine M -> T [] ->
  (forall (M' : word -> option byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     run_inv 0 own M' s mo -> so_wmode M' 0 ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (AFTER_LINE x3 r own y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 M') mo) T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (LOOP_HEAD x1 x3 r own x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 M) mo)
           (ShapeAlg.t_emit (Spec.W 1 [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]) T).
Proof.
  intros own M s mo T r x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 RI SOP T0 HK.
  eapply fuzz_call_rz; [exact RI|]. intros M1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI1 AG1.
  pose proof (ri_own _ _ _ _ _ RI1) as [(L & _ & HKL & _) [_ HG]].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (printf0_first RR M1 mo (Z_to_bv 64 (sp0 - 208)) (bv_unsigned CAN) T) end.
  1: exact (pf_pre_of_inv _ _ _ _ _ RI1).
  1: exact (so_pristine_frame _ _ SOP AG1).
  1: reflexivity. 1: reflexivity. 1: reflexivity.
  1: exact (fd1_of_G_std _ _ _ HG).
  1: exact (minv_reader _ (kl_minv _ _ _ HKL)).   (* port727: the stdio call's far-end reader *)
  1: exact Hh. 1: exact Hl. 1: exact T0.
  intros regs' M2 KCS FM SOW.
  assert (RI2 : run_inv 0 own M2 s mo) by (eapply run_inv_fm; [exact RI1 | exact FM | exact so_regions_fp]).
  pose proof (keeps_cs_kept _ _ KCS) as KEPT.
  use_kept KEPT. forget_regs regs'.
  apply HK; assumption.
Qed.

Lemma line_next_rz : forall own (M : word -> option byte) (s : PState) (mo : Model) (T : ShapeAlg.TSet) (r : Z) (j : nat)
    (x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  run_inv 0 own M s mo -> so_wmode M j -> (j < 512)%nat ->
  (forall (M' : word -> option byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     run_inv 0 own M' s mo -> so_wmode M' (S j) ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (AFTER_LINE x3 r own y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x24 x25 x26 x27 y28 y29 y30 y31 M') mo) T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (LOOP_HEAD x1 x3 r own x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 M) mo) T.
Proof.
  intros own M s mo T r j x1 x3 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 RI SOW J HK.
  eapply fuzz_call_rz; [exact RI|]. intros M1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI1 AG1.
  pose proof (ri_own _ _ _ _ _ RI1) as [(L & _ & HKL & _) [_ HG]].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (printf0_next_rz RR M1 mo (Z_to_bv 64 (sp0 - 208)) (bv_unsigned CAN) j T) end.
  1: exact (pf_pre_of_inv _ _ _ _ _ RI1).
  1: exact (so_wmode_frame _ _ _ SOW AG1).
  1: exact J.
  1: reflexivity. 1: reflexivity. 1: reflexivity.
  1: exact Hh. 1: exact Hl.
  intros regs' M2 KCS FM SOW2.
  assert (RI2 : run_inv 0 own M2 s mo) by (eapply run_inv_fm; [exact RI1 | exact FM | exact so_regions_fp]).
  pose proof (keeps_cs_kept _ _ KCS) as KEPT.
  use_kept KEPT. forget_regs regs'.
  apply HK; assumption.
Qed.

Ltac rcl_static HP H := apply (rheap_pres_rw_cells _ _ _ _ _ _ HP H); right; left; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RERRNO; cbn; lia.

Lemma trun_free_rz : forall own (M : word -> option byte) (s : PState) (mo : Model) (k : nat)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x2 = Z_to_bv 64 (sp0 - 208) -> x4 = Z_to_bv 64 RATP -> x18 = Z_to_bv 64 (oreg own) -> x22 = Z_to_bv 64 0 ->
  run_inv 0 own M s mo -> so_ok M k ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14130) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
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
    assert (ICB' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' 0x2fc84 [C1 (Z_to_bv 8 0)]) by rcl_static HP ICB.
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
    intros M' z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RI' SOW'.
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
  intros M' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI' SOW.
  eapply (loop_next_rz n own 0); [exact N4 | lia | exact RI' | exact SOW].
Qed.

Lemma trun_copy_rz : forall (n : nat) (q : bptr) (A payp : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (src junk jt : list byte) (t7 t6 t4 t3 t2 t0 errv : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x2 = Z_to_bv 64 (sp0 - 208) -> x4 = Z_to_bv 64 RATP -> x8 = Z_to_bv 64 payl -> x9 = Z_to_bv 64 payp -> x10 = Z_to_bv 64 A ->
  x21 = Z_to_bv 64 (Z.of_nat (S n)) -> x20 = Z_to_bv 64 0x2fc80 ->
  (S n <= 4)%nat -> 1 <= payl ->
  RHEAP s [(q, A, payl); (pb, buf, cap)] M -> OWN [q; pb] (G_std fs) s mo ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A [CB (Z.to_nat payl) junk] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M payp src -> length src = Z.to_nat payl -> buf <= payp -> payp + payl <= buf + cap ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 208) [CB 8 jt; C8 t7; C8 t6; C8 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)); C8 t4; C8 t3; C8 t2;
                                C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x13ee4)] ->
  cli_inv sp0 M tid -> so_pristine M ->
  OAX.atx_cellsA M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc84 [C1 (Z_to_bv 8 0)] ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x140a4) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
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
  unfold OAX.PATX, OAX.PATX_CALL, OAX.PAEF_GUARD in AXA, AXB. change (327112 + 288) with 327400 in AXB.
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
  replace (ret_pc (Z_to_bv 64 0x140b8)) with (Z_to_bv 64 0x140b8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
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
                                C8 (Z_to_bv 64 buf); C8 t0; C8 (Z_to_bv 64 0x13ee4)] ->
  cli_inv sp0 M tid -> so_pristine M ->
  OAX.atx_cellsA M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc84 [C1 (Z_to_bv 8 0)] ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x140a4) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
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
  (buf + cap <= 0x10000 \/ 0x51000 <= buf) -> buf + 6 <= payp -> payp + payl <= buf + cap ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 128) -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc80 [C1 (Z_to_bv 8 0)] -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x1e9d0 [C8 (Z_to_bv 64 0)] ->
  OAX.atx_cells0 M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M OAX.PNEEDLK [C1 (Z_to_bv 8 0)] -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc84 [C1 (Z_to_bv 8 0)] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M (buf + 2) [Z_to_bv 8 c2] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M payp src -> length src = Z.to_nat payl ->
  (forall (M1 : word -> option byte) (jt : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     munch [(sp0 - 256, sp0 - 128); (0x2fc80, 0x2fc81); (0x4fdc8, 0x4ffe8)] M M1 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M1 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M1 ->
     stk (run_segments psegs rc_inp rc_sp rc_mb) M1 lo (sp0 - 208) ->
     rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M1 (sp0 - 208) [CB 8 jt; C8 x23; C8 x22; C8 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)); C8 x20; C8 x19; C8 x18;
                                    C8 (Z_to_bv 64 buf); C8 x8; C8 (Z_to_bv 64 0x13ee4)] ->
     bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M1 payp src ->
     OAX.atx_cellsA M1 -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M1 0x2fc84 [C1 (Z_to_bv 8 0)] ->
     Q (MS (mkR y1 (Z_to_bv 64 (sp0 - 208)) x3 (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 payl) (Z_to_bv 64 payp)
                y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 cfgl) (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 0x2fc80) (Z_to_bv 64 (Z.of_nat (S (calls_n cfgl c2))))
                x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
           bvmap_empty (Z_to_bv 64 (if payl =? 0 then 0x140e8 else 0x1409c)) fc0 None M1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) Q (MS (mkR (Z_to_bv 64 0x13ee4) (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 buf)
                       (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 cfgl) (Z_to_bv 64 payp) (Z_to_bv 64 payl) x14 x15 x16 x17
                       x18 x19 x20 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  bvmap_empty (Z_to_bv 64 0x14040) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros Q cfgl c2 payp M src x3 x5 x6 x7 x8 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         CFG C2 PP0 PPA BA B0 BIMG PLO PHI ST MI FL GOT [AX0 AX0B] NL ICB CB PB LEN HK.
  pose proof (munch_refl [(sp0 - 256, sp0 - 128); (0x2fc80, 0x2fc81); (0x4fdc8, 0x4ffe8)] M) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) M) as WM.
  unfold OAX.PATX, OAX.PNEEDLK in AX0, AX0B, NL. change (327112 + 288) with 327400 in AX0B.
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
  change (327112 + 544) with 327656 in MUc. change (327112 + 288) with 327400 in AXB.
  clear AX0 AX0B NL ST. transport_after_call (run_segments psegs rc_inp rc_sp rc_mb) m0 m2 MUc WMc.
  replace (ret_pc (Z_to_bv 64 0x140d4)) with (Z_to_bv 64 0x140d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
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
      pose proof (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) mx (buf + 2) [Z_to_bv 8 c2] 0 1%nat ltac:(eassumption) ltac:(lia) ltac:(cbn; lia)) as HR end.  (* the run's instance is still an evar inside the term *)
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

(* Tier-2b port: the payload copy's malloc is always served, so its NULL exit is not an execution of the
   filtered run. *)
Definition T_run (n : nat) : ShapeAlg.TSet := T_succ n.

Theorem trun_rz : forall (cfgl c2 payp : Z) (M : word -> option byte) (s : PState) (mo : Model) (src : list byte) (errv : word)
    (x3 x5 x6 x7 x8 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= cfgl < 32768 -> 0 <= c2 < 256 -> buf + 6 <= payp -> payp + payl <= buf + cap ->
  RHEAP s [(pb, buf, cap)] M -> OWN [pb] (G_std fs) s mo -> drv_state s -> room (2 ^ 27) mo ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 128) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc80 [C1 (Z_to_bv 8 0)] -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x1e9d0 [C8 (Z_to_bv 64 0)] ->
  OAX.atx_cells0 M -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M 0x2fc84 [C1 (Z_to_bv 8 0)] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M (buf + 2) [Z_to_bv 8 c2] ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M payp src -> length src = Z.to_nat payl ->
  cli_inv sp0 M tid -> so_pristine M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR (Z_to_bv 64 0x13ee4) (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 buf)
                                 (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 cfgl) (Z_to_bv 64 payp) (Z_to_bv 64 payl) x14 x15 x16 x17
                                 x18 x19 x20 (Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14040) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
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
  assert (FW : Forall (fp_ok sp0) [(sp0 - 256, sp0 - 128); (0x2fc80, 0x2fc81); (0x4fdc8, 0x4ffe8)]).
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
      eapply (malloc_rz_driver RR M1 mo s [(pb, buf, cap)] [pb] (G_std fs) payl lo sp0 errv)
        with (Bd := 2 ^ 27) (A := T_end fs 0 (if b1 <? 128 then 2 else 0)) end.
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
    assert (ICB' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' 0x2fc84 [C1 (Z_to_bv 8 0)]) by rcl_static HP ICB1.
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
