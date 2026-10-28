(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatExec CatSim StoreOk Frame Hoare ShapeAlg Spec AgentLib RefMemcpyLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0StdioDefs U.S0ExitBase U.S0Exit U.S0Printf0 U.S0PrintfBufBase U.S0PrintfBuf.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocCover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0HarnStmt U.S0TRDefs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocIface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TRWalk U.S0TargetPre.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0HarnStmt OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocIface.GlueEqv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRWalk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0TRInv.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.

Notation F0 := (bvmap_empty : bvmap 5 word) (only parsing).
Notation FC0 := (Z_to_bv 32 0) (only parsing).

(* [comment removed for export] *)

Lemma final_status_range : forall s5v v, 0 <= v < 256 -> 0 <= final_status s5v v < 256.
Proof. intros. unfold final_status. destruct (2 ^ 63 <=? bv_unsigned s5v); lia. Qed.

Lemma ret_pc_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros. apply ret_pc_even; assumption. Qed.

Section TargetRun.
  Context (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI).
  Hypothesis HARN : harn_spec AI AC S0I.
  Hypothesis PF0 : printf0_first_stmt PF0_S0.

  Local Notation L := S0_layout.

  (* [comment removed for export] *)
  Definition fds_ok (MD : Model) : Prop := fd_lookup (m_fds MD) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

  Lemma fds_ok_stdout : forall MD, fds_ok MD -> fd_lookup (m_fds MD) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
  Proof. intros MD E. exact E. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fin_cps :
    forall (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 ms2 ms3 ms4 ms5 ms6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : word -> option byte) (MD : Model) (s : ai_AS AI) (LB : list ablock) (pb : bid)
           (sp0 tid lo B bufA bufN v : Z) (errv : word) (pending : list byte),
      0x7fff80000000 <= sp0 <= 0x800000000000 ->
      ai_inv AI s LB m MD -> In (pb, bufA, bufN) LB -> ai_aux AI m B -> sp0 <= B ->
      stk s0segs m lo (sp0 - 128) -> alloc_ceiling <= lo -> lo <= sp0 - 128 - 8192 ->
      rw_cells s0segs m (errno_cell L) [C4 errv] -> mem_inv s0segs m ->
      statics1 sp0 tid m -> rw_cells s0segs m 0x440e4 [C1 (Z_to_bv 8 0)] -> 0 < tid < 2 ^ 22 ->
      fds_ok MD ->
      0 <= v < 256 ->
      ((stdout_untouched m /\ pending = []) \/ stdout_used m pending) ->
      realizes s0segs
        (mkCfg (MS (mkR (Z_to_bv 64 0x1377c) (Z_to_bv 64 (sp0 - 128)) gp (Z_to_bv 64 0x441e0) t0 t1 t2
                        (Z_to_bv 64 (final_status ms5 v)) (Z_to_bv 64 bufA) (Z_to_bv 64 bufA) a1 a2 a3 a4 a5 a6 a7
                        ms2 ms3 ms4 ms5 ms6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F0 (Z_to_bv 64 0x293c4) FC0 None m (seg_rom s0segs)) MD)
        (t_emit (W 1 pending) (t_exit (exit_code (final_status ms5 v)) (m_fs MD))).
  Proof.
    intros until pending. intros SP0 INV IN AUX HB ST LOC LO ERR MI STAT FLG TID FDS Hv SO.
    eapply (ai_free AI) with (s := s) (LB := LB) (p := pb) (A := bufA) (n := bufN) (lo := lo) (B := B) (errv := errv);
      [exact INV | exact IN | exact AUX | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; exact ST | exact LOC
      | rewrite u64_lit by lia; cbn [al_stack L S0_layout]; lia | exact ERR | exact MI | reflexivity | reflexivity |].
    intros s' m' MD' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV' VMO' MI' ST' ERR' AUX' HP.
    rewrite u64_lit in ST', HP by lia.
    pose proof (proj1 (ai_inv_model AI INV')) as Hh'. pose proof (proj2 (ai_inv_model AI INV')) as Hl'.
    assert (STAT' : statics1 sp0 tid m').
    { eapply statics1_pres; [apply pres_of_heap_pres; exact HP | | exact SP0 | exact STAT].
      intros a Ha. apply (statics1_client sp0); [lia | exact Ha]. }
    assert (FLG' : rw_cells s0segs m' 0x440e4 [C1 (Z_to_bv 8 0)]).
    { eapply pres_rw_cells; [apply pres_of_heap_pres; exact HP | exact FLG |].
      intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; left.
      unfold L, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia. }
    rewrite ret_pc_lit by lia.
    destruct (s1_mf _ _ _ STAT') as [junk8 MF'].
    eapply (evt_realizes s0segs); [exact Hh' | exact Hl' | |].
    { eapply L7; [| exact MI']. rewrite u64_lit by lia. exact MF'. }
    (intros ms'; cps_intros (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & ->)).
    rewrite u64_lit by lia. replace (sp0 - 128 + 80) with (sp0 - 48) by lia.
    rewrite <- (vm_only_fs _ _ VMO').
    eapply exit_cps; try eassumption.
    - (* [comment removed for export] *)
      pose proof (stk_release s0segs m' lo (sp0 - 128) _ ST' MF' ltac:(lia)) as R.
      cbn [cells_size csize Nat.add] in R. replace (sp0 - 128 + Z.of_nat 80) with (sp0 - 48) in R by lia. exact R.
    - lia.
    - apply final_status_range. exact Hv.
    - destruct SO as [SU | SU]; [left | right].
      + destruct SU as [SU E]. split; [|exact E].
        eapply stdout_untouched_pres; [apply pres_of_heap_pres; exact HP | | exact SU].
        intros a Ha. unfold stdout_addr, SO_FILE, SO_BUF in Ha. right; left.
        unfold L, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
      + split.
        * eapply stdout_used_pres; [apply pres_of_heap_pres; exact HP | | exact SU].
          intros a Ha. unfold stdout_addr, SO_FILE, SO_BUF in Ha. right; left.
          unfold L, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
        * rewrite (vm_only_fds _ _ VMO'). apply fds_ok_stdout. exact FDS.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rw_cells_bytes_at : forall m A cs, rw_cells s0segs m A cs -> bytes_at s0segs m A (cells_bytes cs).
  Proof. intros m A cs [[_ H] _]. exact H. Qed.

  Lemma zero_lines_snoc : forall n, zero_lines n ++ ZL = zero_lines (S n).
  Proof. induction n as [|n IH]; [reflexivity|]. change (zero_lines (S n)) with (ZL ++ zero_lines n). rewrite <- app_assoc, IH. reflexivity. Qed.

  Lemma zero_lines_length : forall n, Z.of_nat (length (zero_lines n)) = 2 * Z.of_nat n.
  Proof. induction n as [|n IH]; [reflexivity|]. cbn [zero_lines length]. lia. Qed.

  Lemma W_app : forall ch a b, W ch (a ++ b) = W ch a ++ W ch b.
  Proof. intros. unfold W. apply map_app. Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_cons : forall m A c cs,
    rw_cells s0segs m A [c] -> rw_cells s0segs m (A + Z.of_nat (csize c)) cs -> rw_cells s0segs m A (c :: cs).
  Proof.
    intros m A c cs H1 H2. change (c :: cs) with ([c] ++ cs). apply rw_cells_app; [exact H1|].
    cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
  Qed.

  Ltac c8p PR := eapply rw_C8_pristine; [apply PR; lia | lia | lia | solve_img | vm_compute; reflexivity].
  Ltac cells8 PR :=
    first [ apply rw_cells_cons; [c8p PR | cbn [csize]; match goal with |- rw_cells _ _ ?A _ => let a := eval cbv in A in change A with a end; cells8 PR]
          | c8p PR ].

  Lemma harn_mem_of_pr : forall m,
    (forall lo hi, 0x32000 <= lo -> hi <= 0x33f90 -> img_pristine m lo hi) -> img_pristine m 0x64471 (0x64471 + 1) ->
    harn_mem s0segs S0I m.
  Proof.
    intros m PR PL.
    cps_pose harn_img_s0 as (IC & IR & _).
    unfold harn_mem. cbn [hi_got hi_relro hi_crc hi_crcx hi_rnums hi_stderrF hi_libc S0I].
    replace (205032 + 16) with 205048 by reflexivity. replace (205032 + 8) with 205040 by reflexivity.
    replace (410736 + 1) with 410737 by reflexivity.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - cells8 PR.
    - cells8 PR.
    - cells8 PR.
    - cells8 PR.
    - apply rw_cells_cons; [apply rw_cells_pristine; [ | lia | | exact IC]; change (Z.of_nat 1024) with 1024%Z; [apply PR|]; lia | cbn [csize]; match goal with |- rw_cells _ _ ?A _ => let a := eval cbv in A in change A with a end; apply rw_cells_pristine; [change (Z.of_nat 56) with 56%Z; apply PR; lia | lia | change (Z.of_nat 56) with 56%Z; lia | vm_compute; reflexivity]].
    - apply rw_cells_pristine; [ | lia | | exact IR]; change (Z.of_nat 2048) with 2048%Z; [apply PR|]; lia.
    - eapply rw_C1_pristine; [exact PL | lia | lia | solve_img | vm_compute; reflexivity].
  Qed.

  Lemma harn_mem_of_statics : forall sp0 tid m, statics sp0 tid m -> harn_mem s0segs S0I m.
  Proof.
    intros sp0 tid m ST. pose proof (st_img _ _ _ ST) as HP. apply harn_mem_of_pr.
    - intros l h Hl Hh a Ha. apply HP. cbn. lia.
    - intros a Ha. apply HP. cbn. lia.
  Qed.

  Lemma harn_mem_of_statics1 : forall sp0 tid m, statics1 sp0 tid m -> harn_mem s0segs S0I m.
  Proof.
    intros sp0 tid m ST. pose proof (s1_img _ _ _ ST) as HP. apply harn_mem_of_pr.
    - intros l h Hl Hh a Ha. apply HP. cbn [in_ivs S_IVS1]. lia.
    - intros a Ha. apply HP. cbn [in_ivs S_IVS1]. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma cwo_stack : forall LB l h, alloc_ceiling <= l -> client_write_ok L LB (l, h).
  Proof. intros. left. cbn. assumption. Qed.

  Lemma cwo_data : forall LB l h, 0x32000 <= l -> h <= 0x66000 ->
    (h <= 0x32138 \/ (0x32140 <= l /\ h <= 0x64450) \/ (0x64458 <= l /\ h <= 0x64470) \/ 0x64890 <= l) ->
    client_write_ok L LB (l, h).
  Proof.
    intros. right; left. cbn [fst snd al_rw_lo al_img_hi al_static S0_layout]. split; [lia|]. split; [lia|].
    intros a Ha. unfold S0_static. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac aux_fp := repeat (apply Forall_cons; [cbn [fst snd al_static S0_layout]; split; [lia | unfold S0_static; intros; lia] |]); apply Forall_nil.

  Section Run.
    Variables (sp0 tid B bufA bufN len alA : Z) (pa pb : bid) (payload : list byte) (calls : nat).
    Variables (gp s0v s2v s3v s5v s6v s7v s8v s9v s10v s11v : word).
    Local Notation lo := (sp0 - 8388608).
    Local Notation spT := (sp0 - 208).
    Local Notation spL := (sp0 - 256).
    Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
    Hypothesis alloc_ceiling_val : alloc_ceiling = sp0 - 8388608.   (* [comment removed for export] *)
    Hypothesis TID : 0 < tid < 2 ^ 22.
    Hypothesis HB : sp0 <= B.
    Hypothesis LEN : Z.of_nat (length payload) = len /\ len < 2 ^ 26.
    Hypothesis AL : (len = 0 /\ alA = 0x440f0) \/ (0 < len /\ block_ok L alA len).
    Hypothesis CALLS : (1 <= calls <= 4)%nat.

    Definition owA : Z := if len =? 0 then 0 else alA.
    Definition frame_cells (junk8 : list byte) : list cell :=
      [CB 8 junk8; C8 s7v; C8 s6v; C8 s5v; C8 (Z_to_bv 64 len); C8 s3v; C8 s2v; C8 (Z_to_bv 64 bufA); C8 s0v; C8 (Z_to_bv 64 0x136f4)].

    Definition stdout_state (m : word -> option byte) (i : nat) : Prop :=
      match i with O => stdout_untouched m | S i' => stdout_used m (zero_lines i') end.

    (* [comment removed for export] *)
    Record cfacts (m : word -> option byte) (i : nat) : Prop := CFACTS {
      cf_stat  : statics1 sp0 tid m;
      cf_frame : exists junk8, rw_cells s0segs m spT (frame_cells junk8);
      cf_src   : bytes_at s0segs m alA payload;
      cf_out   : stdout_state m i }.

    Definition cfacts_addr (a : Z) : Prop :=
      statics1_addr sp0 a \/ (spT <= a < spT + 80) \/ (alA <= a < alA + len) \/ stdout_addr a.

    Lemma lo_facts : alloc_ceiling <= lo /\ 0x7fff7f000000 <= lo.
    Proof. rewrite alloc_ceiling_val. lia. Qed.

    Lemma alA_facts : 0 <= alA /\ alA + len <= 2 ^ 64 /\ (alA + len <= 0x10000 \/ 0x440f0 <= alA) /\ alA + len <= alloc_ceiling /\
                      (0 < len -> alA + len <= 0x10000 \/ 0x66000 <= alA).
    Proof.
      rewrite alloc_ceiling_val. destruct AL as [[E1 E2]|[E1 (B1 & B2 & B3 & B4 & B5)]].
      - subst. lia.
      - rewrite alloc_ceiling_val in B4. unfold L, S0_layout in B5; cbn [al_img_lo al_img_hi] in B5. lia.
    Qed.

    Lemma stdout_state_pres : forall P m m' i,
      pres P m m' -> (forall a, stdout_addr a -> P a) -> stdout_state m i -> stdout_state m' i.
    Proof.
      intros P m m' [|i'] HP HS; cbn; [apply (stdout_untouched_pres P) | apply (stdout_used_pres P)]; assumption.
    Qed.

    Lemma cfacts_pres : forall P m m' i,
      pres P m m' -> (forall a, cfacts_addr a -> P a) -> cfacts m i -> cfacts m' i.
    Proof.
      intros P m m' i HP HS [ST [junk8 FR] SRC OUT]. pose proof alA_facts as AF. constructor.
      - eapply statics1_pres; [exact HP | | exact (proj1 SP0) | exact ST]. intros a Ha; apply HS; left; exact Ha.
      - exists junk8. eapply pres_rw_cells; [exact HP | exact FR |]. cbn. intros a Ha; apply HS; right; left. lia.
      - eapply pres_bytes_at; [exact HP | exact SRC |]. intros a Ha; apply HS; right; right; left. lia.
      - eapply stdout_state_pres; [exact HP | | exact OUT]. intros a Ha; apply HS; right; right; right; exact Ha.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma cfacts_heap : forall LB SP m m' i,
      heap_pres s0segs L LB SP m m' -> SP <= spT ->
      (0 < len -> In (pa, alA, len) LB) ->
      cfacts m i -> cfacts m' i.
    Proof.
      intros LB SP m m' i HP HSP HAL CF. pose proof alA_facts as AF.
      eapply cfacts_pres; [apply pres_of_heap_pres; exact HP | | exact CF].
      intros a [Ha|[Ha|[Ha|Ha]]].
      - apply (statics1_client sp0); [lia | exact Ha].
      - left. lia.
      - destruct AL as [[E1 E2]|[E1 _]]; [lia|]. right; right. exists (pa, alA, len). split; [apply HAL; lia|]. cbn. lia.
      - right; left. unfold stdout_addr, SO_FILE, SO_BUF in Ha.
        unfold L, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
    Qed.


    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition KX (n : nat) (fs' : Fs.Fs) : TSet := t_emit (W 1 (zero_lines n)) (t_exit (exit_code 0) fs').
    (* [comment removed for export] *)
    Definition REM (i j : nat) (f : Fs.Fs) : TSet := KX (match i with O => calls | S _ => (calls - 1)%nat end) f.

    Lemma REM_S : forall i j f, REM (S i) j f = KX (calls - 1) f.
    Proof. reflexivity. Qed.
    Lemma REM_step : forall i j f, REM i (S j) f = REM i j f.
    Proof. reflexivity. Qed.

    (* [comment removed for export] *)
    Definition credit (j : nat) : nat := (j * HARN_VM_NEED)%nat.

    Record head_inv (m : word -> option byte) (MD : Model) (LB : list ablock) (i j : nat) : Prop := HEAD_INV {
      hi_inv : exists s : ai_AS AI, ai_inv AI s LB m MD /\ ac_vm AC (credit j) s MD;   (* [comment removed for export] *)
      hi_aux : ai_aux AI m B;
      hi_mi  : mem_inv s0segs m;
      hi_stk : stk s0segs m lo spT;
      hi_err : exists e, rw_cells s0segs m (errno_cell L) [C4 e];
      hi_cf  : cfacts m i;
      hi_al  : 0 < len -> In (pa, alA, len) LB;
      hi_ne  : 0 < len -> pa <> pb;
      hi_buf : In (pb, bufA, bufN) LB;
      hi_fds : fds_ok MD;   (* [comment removed for export] *)
      hi_flg : rw_cells s0segs m 0x440e4 [C1 (Z_to_bv 8 0)] }.

    Lemma model_of_inv : forall s LB m MD, ai_inv AI s LB m MD -> m_halted MD = None /\ m_vm_lazy MD = [].
    Proof. intros. exact (ai_inv_model AI H). Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma tail_cps : forall (i : nat) (m : word -> option byte) (MD : Model) (LB : list ablock)
        (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      (S i = calls)%nat -> head_inv m MD LB (S i) 0 ->
      realizes s0segs
        (mkCfg (MS (mkR (Z_to_bv 64 0x1392c) (Z_to_bv 64 spT) gp (Z_to_bv 64 0x441e0) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 alA)
                        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owA) (Z_to_bv 64 0) (Z_to_bv 64 0x440e0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8v s9v s10v s11v t3 t4 t5 t6)
                   F0 (Z_to_bv 64 0x1392c) FC0 None m (seg_rom s0segs)) MD)
        (REM (S i) 0 (m_fs MD)).
    Proof.
      intros i m MD LB t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi [[s (INV & VM)] AUX MI ST [e ERR] CF ALB NE BUFB FDS FLG].
      pose proof (proj1 SP0) as SP. pose proof lo_facts as [LOC LOLO]. pose proof alA_facts as AF.
      destruct (model_of_inv _ _ _ _ INV) as [Hh Hl].
      eapply (evt_realizes s0segs); [exact Hh | exact Hl | apply L5last; exact MI |].
      intros ms' ->.
      (* [comment removed for export] *)
      assert (K : forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model) (LB' : list ablock)
                         (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ai_inv AI s' LB' m' MD' -> In (pb, bufA, bufN) LB' -> vm_only MD MD' -> mem_inv s0segs m' -> stk s0segs m' lo spT ->
        rw_cells s0segs m' (errno_cell L) [C4 e] -> ai_aux AI m' B ->
        statics1 sp0 tid m' -> (exists junk8, rw_cells s0segs m' spT (frame_cells junk8)) -> stdout_used m' (zero_lines i) ->
        rw_cells s0segs m' 0x440e4 [C1 (Z_to_bv 8 0)] ->
        realizes s0segs
          (mkCfg (MS (mkR (Z_to_bv 64 0x13948) (Z_to_bv 64 spT) gp (Z_to_bv 64 0x441e0) t0' t1' t2' (Z_to_bv 64 len) (Z_to_bv 64 alA)
                          a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 owA) (Z_to_bv 64 (-1)) (Z_to_bv 64 0x440e0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8v s9v s10v s11v t3' t4' t5' t6')
                     F0 (ret_pc (Z_to_bv 64 0x13948)) FC0 None m' (seg_rom s0segs)) MD')
          (REM (S i) 0 (m_fs MD))).
      { intros s' m' MD' LB' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV' BUFB' VMO' MI' ST' ERR' AUX' STAT' [junk8 FR'] OUT' FLG'.
        destruct (model_of_inv _ _ _ _ INV') as [Hh' Hl'].
        rewrite ret_pc_lit by lia.
        replace (Z_to_bv 64 spT) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (sp0 - 128)) + -80)) by (rewrite u64_lit by lia; f_equal; lia).
        eapply (evt_realizes s0segs); [exact Hh' | exact Hl' | |].
        { eapply L6; [| reflexivity | exact MI']. rewrite u64_lit by lia. replace (sp0 - 128 + -80) with spT by lia. exact FR'. }
        (intros ms'; cps_intros (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & ->)).
        rewrite REM_S. unfold KX. rewrite <- Hi, Nat.sub_succ, Nat.sub_0_r.
        rewrite <- (vm_only_fs _ _ VMO').
        replace (exit_code 0) with (exit_code (final_status s5v 0)) by (unfold final_status; destruct (2 ^ 63 <=? bv_unsigned s5v); reflexivity).
        eapply fin_cps; try eassumption.
        - pose proof (stk_release s0segs m' lo spT _ ST' FR' ltac:(lia)) as R.
          unfold frame_cells in R. cbn [cells_size csize Nat.add] in R. replace (spT + Z.of_nat 80) with (sp0 - 128) in R by lia. exact R.
        - lia.
        - unfold fds_ok. rewrite (vm_only_fds _ _ VMO'). exact FDS.
        - lia.
        - right. exact OUT'. }
      (* [comment removed for export] *)
      destruct AL as [[L0 EA]|[LP BO]].
      - (* [comment removed for export] *)
        unfold owA in *. rewrite (proj2 (Z.eqb_eq len 0) L0) in *.
        apply (ai_free_null AI); [exact Hh | exact Hl | reflexivity |].
        destruct CF as [STc FRc SRCc OUTc].
        eapply K; try eassumption. apply vm_only_refl.
      - (* [comment removed for export] *)
        unfold owA in *. replace (len =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia).
        eapply (ai_free AI) with (s := s) (LB := LB) (p := pa) (A := alA) (n := len) (lo := lo) (B := B) (errv := e);
          [exact INV | apply ALB; exact LP | exact AUX | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; exact ST | exact LOC
          | rewrite u64_lit by lia; cbn [al_stack S0_layout]; lia | exact ERR | exact MI | reflexivity | reflexivity |].
        intros s' m' MD' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV' VMO' MI' ST' ERR' AUX' HP.
        rewrite u64_lit in ST', HP by lia.
        destruct CF as [STc [junk8 FRc] SRCc OUTc].
        pose proof (pres_of_heap_pres _ _ _ _ _ HP) as PR.
        eapply K.
        + exact INV'.
        + apply lb_remove_keep; [exact BUFB|]. cbn. intros E. apply (NE LP). symmetry. exact E.
        + exact VMO'.
        + exact MI'.
        + exact ST'.
        + exact ERR'.
        + exact AUX'.
        + eapply statics1_pres; [exact PR | | exact SP | exact STc]. intros a Ha. apply (statics1_client sp0); [lia| exact Ha].
        + exists junk8. eapply pres_rw_cells; [exact PR | exact FRc |]. intros a Ha. left. unfold frame_cells in Ha. cbn in Ha. lia.
        + eapply stdout_used_pres; [exact PR | | exact OUTc]. intros a Ha. unfold stdout_addr, SO_FILE, SO_BUF in Ha.
          right; left. unfold S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
        + eapply pres_rw_cells; [exact PR | exact FLG |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
          right; left. unfold S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma head_inv_after_printf : forall W m m' MD LB i i' j,
      head_inv m MD LB i j ->
      munch W m m' -> wmono s0segs m m' -> mem_inv s0segs m' -> stk s0segs m' lo spT -> statics1 sp0 tid m' ->
      stdout_state m' i' ->
      Forall (client_write_ok L LB) W -> Forall (fun iv => snd iv <= B /\ (forall a, fst iv <= a < snd iv -> ~ al_static L a)) W ->
      disjoint_from W spT 80 -> disjoint_from W alA len -> disjoint_from W (errno_cell L) 4 -> disjoint_from W 0x440e4 1 ->
      head_inv m' MD LB i' j.
    Proof.
      intros W m m' MD LB i i' j [[s (INV & VM)] AUX MI ST [e ERR] [STc [junk8 FR] SRC OUT] ALB NE BUFB FDS FLG] MU WM MI' ST' STAT' OUT' CW LEB D1 D2 D3 D4.
      constructor; try assumption.
      - exists s. split; [| exact VM]. eapply (ai_inv_frame AI); eassumption.
      - eapply (ai_aux_frame AI); eassumption.
      - exists e. eapply rw_cells_transport; [exact ERR | exact MU | exact WM | exact D3].
      - constructor.
        + exact STAT'.
        + exists junk8. eapply rw_cells_transport; [exact FR | exact MU | exact WM | exact D1].
        + eapply bytes_at_transport; [exact SRC | exact MU |]. rewrite (proj1 LEN). exact D2.
        + exact OUT'.
      - eapply rw_cells_transport; [exact FLG | exact MU | exact WM | exact D4].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    (* [comment removed for export] *)

    Lemma printf_step : forall (i j : nat) (m : word -> option byte) (MD : Model) (LB : list ablock) (jw : word)
        (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      (S i <= calls)%nat -> head_inv m MD LB i j ->
      (forall (m' : word -> option byte) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          head_inv m' MD LB (S i) j ->
          realizes s0segs
            (mkCfg (MS (mkR (Z_to_bv 64 0x1392c) (Z_to_bv 64 spT) gp (Z_to_bv 64 0x441e0) t0' t1' t2' (Z_to_bv 64 len) (Z_to_bv 64 alA)
                            a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 owA) (Z_to_bv 64 0) (Z_to_bv 64 0x440e0) jw (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8v s9v s10v s11v t3' t4' t5' t6')
                       F0 (Z_to_bv 64 0x1392c) FC0 None m' (seg_rom s0segs)) MD)
            (REM (S i) j (m_fs MD))) ->
      realizes s0segs
        (mkCfg (MS (mkR (Z_to_bv 64 0x1392c) (Z_to_bv 64 spT) gp (Z_to_bv 64 0x441e0) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 alA)
                        a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owA) (Z_to_bv 64 0) (Z_to_bv 64 0x440e0) jw (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8v s9v s10v s11v t3 t4 t5 t6)
                   F0 (Z_to_bv 64 0x139d8) FC0 None m (seg_rom s0segs)) MD)
        (REM i j (m_fs MD)).
    Proof.
      intros i j m MD LB jw t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi HI HK.
      pose proof HI as [[s (INV & VM)] AUX MI ST [e ERR] [STc [junk8 FR] SRC OUT] ALB NE BUFB FDS FLG].
      pose proof (proj1 SP0) as SP. pose proof lo_facts as [LOC LOLO]. pose proof alA_facts as AF.
      destruct (model_of_inv _ _ _ _ INV) as [Hh Hl].
      assert (SPT : bv_unsigned (Z_to_bv 64 spT) = spT) by (apply u64_lit; lia).
      destruct i as [|i'].
      - (* [comment removed for export] *)
        apply (rz_eq s0segs _ (REM 0 j (m_fs MD)) (t_emit (W 1 ZL) (REM 1 j (m_fs MD)))).
        { unfold REM, KX. cbn iota.
          replace (zero_lines calls) with (ZL ++ zero_lines (calls - 1))
            by (clear - Hi; destruct calls as [|c]; [lia| cbn [Nat.sub]; rewrite Nat.sub_0_r; reflexivity]).
          rewrite W_app. apply t_eq_sym. apply t_emit_app. }
        eapply (printf0_cps PF0) with (sp0 := sp0) (tid := tid) (lo := lo); rewrite ?SPT;
          [lia | exact SP | lia | exact ST | lia | lia | exact MI | exact STc | exact OUT | apply fds_ok_stdout; exact FDS | exact Hh | exact Hl
          | apply t_emit_has_nil |].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST' STAT' OUT'.
        apply HK. eapply (head_inv_after_printf (pf0_W spT)); try eassumption.
        + unfold pf0_W, SO_FILE, SO_BUF.
          apply Forall_cons; [apply cwo_stack; lia|]. apply Forall_cons; [apply cwo_data; lia|].
          apply Forall_cons; [apply cwo_data; lia|]. apply Forall_nil.
        + unfold pf0_W, SO_FILE, SO_BUF. aux_fp.
        + unfold pf0_W, SO_FILE, SO_BUF. cbn. lia.
        + unfold pf0_W, SO_FILE, SO_BUF. cbn. lia.
        + unfold pf0_W, SO_FILE, SO_BUF, errno_cell, S0_layout. cbn. lia.
        + unfold pf0_W, SO_FILE, SO_BUF. cbn. lia.
      - (* [comment removed for export] *)
        change (REM (S i') j (m_fs MD)) with (REM (S (S i')) j (m_fs MD)).
        eapply printfN_cps with (sp0 := sp0) (tid := tid) (lo := lo) (pending := zero_lines i'); rewrite ?SPT;
          [lia | exact SP | lia | exact ST | lia | lia | exact MI | exact STc | exact OUT | rewrite zero_lines_length; lia | exact Hh | exact Hl |].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST' STAT' OUT'.
        rewrite zero_lines_snoc in OUT'.
        pose proof (zero_lines_length i') as ZLL.
        apply HK. eapply (head_inv_after_printf (pfN_W spT (SO_BUF + Z.of_nat (length (zero_lines i'))))); try eassumption.
        + unfold pfN_W, SO_FILE, SO_BUF.
          apply Forall_cons; [apply cwo_stack; lia|]. apply Forall_cons; [apply cwo_data; lia|].
          apply Forall_cons; [apply cwo_data; lia|]. apply Forall_cons; [apply cwo_data; lia|]. apply Forall_nil.
        + unfold pfN_W, SO_FILE, SO_BUF. aux_fp.
        + unfold pfN_W, SO_FILE, SO_BUF. cbn. lia.
        + unfold pfN_W, SO_FILE, SO_BUF. cbn. lia.
        + unfold pfN_W, SO_FILE, SO_BUF, errno_cell, S0_layout. cbn. lia.
        + unfold pfN_W, SO_FILE, SO_BUF. cbn. lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma spT_lit : bv_unsigned (Z_to_bv 64 spT) = spT. Proof. apply u64_lit. lia. Qed.
    (* [comment removed for export] *)

    Lemma fuzz_step : forall (i j : nat) (m : word -> option byte) (MD : Model) (LB : list ablock)
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word),
      head_inv m MD LB i (S j) ->
      (forall (m' : word -> option byte) (MD' : Model) (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          head_inv m' MD' LB i j ->
          realizes s0segs
            (mkCfg (MS (mkR (Z_to_bv 64 0x1392c) (Z_to_bv 64 spT) gp (Z_to_bv 64 0x441e0) t0' t1' t2' (Z_to_bv 64 len) (Z_to_bv 64 alA)
                            (Z_to_bv 64 0) (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 owA) (Z_to_bv 64 0) (Z_to_bv 64 0x440e0) (Z_to_bv 64 (Z.of_nat (S j)))
                            (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8v s9v s10v s11v t3' t4' t5' t6')
                       F0 (Z_to_bv 64 0x139d8) FC0 None m' (seg_rom s0segs)) MD')
            (REM i j (m_fs MD'))) ->
      realizes s0segs
        (mkCfg (MS (mkR ra (Z_to_bv 64 spT) gp (Z_to_bv 64 0x441e0) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 alA)
                        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owA) s3 (Z_to_bv 64 0x440e0) (Z_to_bv 64 (Z.of_nat (S j)))
                        (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8v s9v s10v s11v t3 t4 t5 t6)
                   F0 (Z_to_bv 64 0x13908) FC0 None m (seg_rom s0segs)) MD)
        (REM i (S j) (m_fs MD)).
    Proof.
      intros i j m MD LB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 HI HK.
      pose proof HI as [[s (INV & VM)] AUX MI ST [e ERR] CF ALB NE BUFB FDS FLG].
      pose proof (proj1 SP0) as SP. pose proof lo_facts as [LOC LOLO]. pose proof alA_facts as AF.
      destruct (model_of_inv _ _ _ _ INV) as [Hh Hl].
      (* [comment removed for export] *)
      eapply (evt_realizes s0segs); [exact Hh | exact Hl | eapply L1; [exact MI | exact FLG] |].
      (intros ms1; cps_intros (m1 & -> & MU1 & WM1 & MI1 & FLG1)).
      assert (PR1 := pres_of_munch _ _ _ MU1 WM1).
      assert (INV1 : ai_inv AI s LB m1 MD).
      { eapply (ai_inv_frame AI); [exact INV | exact MU1 | exact WM1 |].
        apply Forall_cons; [apply cwo_data; lia | apply Forall_nil]. }
      assert (AUX1 : ai_aux AI m1 B) by (eapply (ai_aux_frame AI); [exact AUX | exact MU1 | exact WM1 | aux_fp]).
      assert (ST1 : stk s0segs m1 lo spT) by (eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 | cbn; lia]).
      assert (ERR1 : rw_cells s0segs m1 (errno_cell L) [C4 e])
        by (eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | unfold errno_cell, S0_layout; cbn; lia]).
      assert (CF1 : cfacts m1 i).
      { eapply cfacts_pres; [exact PR1 | | exact CF]. intros a [Ha|[Ha|[Ha|Ha]]].
        - unfold statics1_addr, core1_addr, ax_addr, OFL in Ha. cbn [in_ivs S_IVS1] in Ha. cbn. first [ solve [clear - SP0 Ha; lia] | lia ].
        - cbn. lia.
        - cbn. destruct AL as [[E1 E2]|[E1 _]]; lia.
        - unfold stdout_addr, SO_FILE, SO_BUF in Ha. cbn. lia. }
      clear INV AUX ST ERR CF MI.
      rewrite REM_step.
      eapply (HARN (Z_to_bv 64 0x1391c) (Z_to_bv 64 spT) gp (Z_to_bv 64 0x441e0) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 alA)
                 (Z_to_bv 64 alA) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owA) s3 (Z_to_bv 64 0x440e0) (Z_to_bv 64 (Z.of_nat (S j)))
                 (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8v s9v s10v s11v t3 t4 t5 t6 F0 FC0 m1 MD s LB alA len lo B payload e (credit j)
                 (REM i j (m_fs MD)));
        rewrite ?spT_lit; try reflexivity.
      - lia.
      - exact INV1.
      - exact VM.
      - exact AUX1.
      - lia.
      - exact (cf_src _ _ CF1).
      - lia.
      - destruct AL as [[L0 EA]|[LP _]].
        + right; left. unfold errno_cell, S0_layout, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp].
          split; [lia|]. split; [lia|]. split; [intros; lia| lia].
        + right; right. exists (pa, alA, len). split; [apply ALB; exact LP|]. cbn. lia.
      - lia.
      - destruct AL as [[_ ->]|[_ (_ & B2 & _)]]; [reflexivity | exact B2].
      - destruct AL as [[L0 _]|[LP _]]; [left; exact L0 | right; exists (pa, alA, len); split; [apply ALB; exact LP | cbn; lia]].
      - exact ST1.
      - exact LOC.
      - unfold HARN_STACK. lia.
      - destruct (proj1 (Z.mod_divide sp0 16 ltac:(lia)) (proj2 SP0)) as [q Hq]. rewrite Hq.
        replace (q * 16 - 208) with ((q - 13) * 16) by lia. apply Z_mod_mult.   (* [comment removed for export] *)
      - lia.
      - exact ERR1.
      - exact MI1.
      - exact (harn_mem_of_statics1 _ _ _ (cf_stat _ _ CF1)).
      - (* [comment removed for export] *)
        (intros ms' MD'; cps_intros (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & errv' & m' & s' &
                          -> & INV' & VM' & VMO' & MI' & ST' & ERR' & AUX' & HP & HM')).
        rewrite !spT_lit in *. rewrite ret_pc_lit by lia.
        destruct (model_of_inv _ _ _ _ INV') as [Hh' Hl'].
        assert (CF' : cfacts m' i) by (eapply cfacts_heap; [exact HP | lia | exact ALB | exact CF1]).
        assert (FLG' : rw_cells s0segs m' 0x440e4 [C1 (Z_to_bv 8 1)]).
        { eapply pres_rw_cells; [apply pres_of_heap_pres; exact HP | exact FLG1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
          right; left. unfold S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia. }
        eapply (evt_realizes s0segs); [exact Hh' | exact Hl' | eapply L4; [exact MI' | exact FLG'] |].
        (intros ms2; cps_intros (m2 & -> & MU2 & WM2 & MI2 & FLG2)).
        assert (PR2 := pres_of_munch _ _ _ MU2 WM2).
        rewrite <- (vm_only_fs _ _ VMO').
        apply HK. constructor.
        + exists s'. split; [| exact VM']. eapply (ai_inv_frame AI); [exact INV' | exact MU2 | exact WM2 |].
          apply Forall_cons; [apply cwo_data; lia | apply Forall_nil].
        + eapply (ai_aux_frame AI); [exact AUX' | exact MU2 | exact WM2 | aux_fp].
        + exact MI2.
        + eapply stk_transport_disjoint; [exact ST' | exact MU2 | exact WM2 | cbn; lia].
        + exists errv'. eapply rw_cells_transport; [exact ERR' | exact MU2 | exact WM2 | unfold errno_cell, S0_layout; cbn; lia].
        + eapply cfacts_pres; [exact PR2 | | exact CF']. intros a [Ha|[Ha|[Ha|Ha]]].
          * unfold statics1_addr, core1_addr, ax_addr, OFL in Ha. cbn [in_ivs S_IVS1] in Ha. cbn. first [ solve [clear - SP0 Ha; lia] | lia ].
          * cbn. lia.
          * cbn. destruct AL as [[E1 E2]|[E1 _]]; lia.
          * unfold stdout_addr, SO_FILE, SO_BUF in Ha. cbn. lia.
        + exact ALB.
        + exact NE.
        + exact BUFB.
        + unfold fds_ok. rewrite (vm_only_fds _ _ VMO'). exact FDS.
        + exact FLG2.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Lemma loop_cps : forall (j i : nat) (m : word -> option byte) (MD : Model) (LB : list ablock)
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word),
      (1 <= j)%nat -> (i + j = calls)%nat -> head_inv m MD LB i j ->
      realizes s0segs
        (mkCfg (MS (mkR ra (Z_to_bv 64 spT) gp (Z_to_bv 64 0x441e0) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 alA)
                        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owA) s3 (Z_to_bv 64 0x440e0) (Z_to_bv 64 (Z.of_nat j))
                        (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8v s9v s10v s11v t3 t4 t5 t6)
                   F0 (Z_to_bv 64 0x13908) FC0 None m (seg_rom s0segs)) MD)
        (REM i j (m_fs MD)).
    Proof.
      induction j as [|j IH]; intros i m MD LB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 Hj Hij HI; [lia|].
      eapply fuzz_step; [exact HI|].
      intros m1 MD1 y0 y1 y2 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 HI1.
      eapply printf_step; [lia | exact HI1 |].
      intros m2 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 HI2.
      destruct (hi_inv _ _ _ _ _ HI2) as [s2 (INV2 & _)]. pose proof (hi_mi _ _ _ _ _ HI2) as MI2.
      destruct (model_of_inv _ _ _ _ INV2) as [Hh2 Hl2].
      destruct j as [|j'].
      - (* [comment removed for export] *)
        change (Z.of_nat 1) with 1. eapply tail_cps; [lia| exact HI2].
      - (* [comment removed for export] *)
        eapply (evt_realizes s0segs); [exact Hh2 | exact Hl2 | apply L5loop; [lia | exact MI2] |].
        intros ms' ->. replace (Z.of_nat (S (S j')) - 1) with (Z.of_nat (S j')) by lia.
        eapply IH; [lia | lia | exact HI2].
    Qed.
  End Run.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition callsN (content : list byte) : nat :=
    match Z.to_nat (hdr_cfglen content) with
    | O => 1%nat
    | S _ => S (Z.to_nat (bv_unsigned (nth 2 content (Z_to_bv 8 0)) mod 4))
    end.

  Lemma callsN_range : forall content, (1 <= callsN content <= 4)%nat.
  Proof.
    intros content. unfold callsN. destruct (Z.to_nat (hdr_cfglen content)); [lia|].
    pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)). lia.
  Qed.

  Lemma callsN_calls_of : forall content,
    Z.of_nat (callsN content) = calls_of (hdr_cfglen content) (bv_unsigned (nth 2 content (Z_to_bv 8 0))).
  Proof.
    intros content. unfold callsN, calls_of.
    pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)) as HC. unfold hdr_cfglen in *.
    pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)).
    change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
    destruct (Z.to_nat (hdr_cfg content mod 32768)) eqn:E.
    - replace (hdr_cfg content mod 32768 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
    - replace (hdr_cfg content mod 32768 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma t_target_unfold : forall content fs,
    t_target content fs = t_emit (W 1 (zero_lines (callsN content))) (t_exit (exit_code 0) fs).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rw_CB1_C1 : forall m A b, rw_cells s0segs m A [CB 1 [b]] -> rw_cells s0segs m A [C1 b].
  Proof.
    intros m A b [[W B] R]. split; [split; [exact (conj I I)|]|]; cbn [cells_bytes cbytes cells_size csize app Nat.add] in *; assumption.
  Qed.

  Lemma firstn1_skipn : forall (bs : list byte) k, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs (Z_to_bv 8 0)].
  Proof.
    intros bs; induction bs as [|b bs IH]; intros [|k] H; cbn in *; try lia; [reflexivity|]. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_byte : forall m A n bs k,
    rw_cells s0segs m A [CB n bs] -> (k < n)%nat ->
    rw_cells s0segs m (A + Z.of_nat k) [C1 (nth k bs (Z_to_bv 8 0))].
  Proof.
    intros m A n bs k RW Hk.
    pose proof (rw_cells_split_CB s0segs m A [] n bs [] [k; 1; n - k - 1]%nat RW ltac:(cbn; lia)) as S1.
    cbn [app mk_CB_cells] in S1.
    destruct (rw_cells_split m A [CB k (firstn k bs)] _ S1) as [_ X2]. cbn [cells_size csize Nat.add] in X2.
    destruct (rw_cells_split m _ [CB 1 (firstn 1 (skipn k bs))] _ X2) as [X3 _].
    apply rw_CB1_C1. destruct RW as [[[WF _] _] _]. cbn in WF.
    rewrite Nat.add_0_r in X3. rewrite firstn1_skipn in X3 by lia. exact X3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma got_of_statics : forall sp0 tid m, statics sp0 tid m ->
    rw_cells s0segs m 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)].
  Proof.
    intros sp0 tid m ST. pose proof (st_img _ _ _ ST) as HP.
    assert (PR : forall lo hi, 0x32000 <= lo -> hi <= 0x33f90 -> img_pristine m lo hi).
    { intros l h Hl Hh a Ha. apply HP. cbn. lia. }
    cells8 PR.
  Qed.

  Ltac c4p PR := eapply rw_C4_pristine; [apply PR; lia | lia | lia | solve_img | vm_compute; reflexivity].
  Ltac nxt := cbn [csize]; match goal with |- rw_cells _ _ ?A _ => let a := eval cbv in A in change A with a end.
  Ltac nrm H := match type of H with rw_cells _ _ ?A _ => let a := eval vm_compute in A in change A with a in H end.

  Lemma atx_init_of_statics : forall sp0 tid m, statics sp0 tid m ->
    exists p1 p2, rw_cells s0segs m 0x64228 (ax_list p1 p2 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0))
      /\ rw_cells s0segs m 0x64348 [C8 (Z_to_bv 64 0)] /\ rw_cells s0segs m 0x64473 [C1 (Z_to_bv 8 0)].
  Proof.
    intros sp0 tid m ST. pose proof (st_img _ _ _ ST) as HP.
    assert (PR : forall lo hi, 0x64220 <= lo -> hi <= 0x64450 -> img_pristine m lo hi).
    { intros l h Hl Hh a Ha. apply HP. cbn. lia. }
    assert (PL : img_pristine m 0x64473 (0x64473 + 1)).
    { intros a Ha. apply HP. cbn. lia. }
    eexists ?[p1], ?[p2]. unfold ax_list. split; [|split].
    - apply rw_cells_cons; [eapply rw_C1_pristine; [apply PR; lia | lia | lia | solve_img | vm_compute; reflexivity] | nxt].
      apply rw_cells_cons; [apply rw_cells_pristine; [change (Z.of_nat 3) with 3; apply PR; lia | lia | change (Z.of_nat 3) with 3; lia | solve_img] | nxt].
      apply rw_cells_cons; [c4p PR | nxt].
      apply rw_cells_cons; [c4p PR | nxt].
      apply rw_cells_cons; [apply rw_cells_pristine; [change (Z.of_nat 4) with 4; apply PR; lia | lia | change (Z.of_nat 4) with 4; lia | solve_img] | nxt].
      apply rw_cells_cons; [c8p PR | nxt].
      apply rw_cells_cons; [c8p PR | nxt].
      c8p PR.
    - c8p PR.
    - eapply rw_C1_pristine; [exact PL | lia | lia | solve_img | vm_compute; reflexivity].
  Qed.

  Lemma flag_of_statics : forall sp0 tid m, statics sp0 tid m -> rw_cells s0segs m 0x440e4 [C1 (Z_to_bv 8 0)].
  Proof.
    intros sp0 tid m ST. pose proof (st_img _ _ _ ST) as HP.
    eapply rw_C1_pristine; [intros a Ha; apply HP; cbn; lia | lia | lia | solve_img | vm_compute; reflexivity].
  Qed.

  Lemma ax_cells_of : forall m p1 p2 nx,
    rw_cells s0segs m 0x64228 (ax_list p1 p2 1 0x64240 nx (Z_to_bv 64 0x2916c)) ->
    rw_cells s0segs m 0x64348 [C8 (Z_to_bv 64 0x139a8)] -> ax_cells m.
  Proof.
    intros m p1 p2 nx H A0. unfold ax_list in H.
    change (C1 (Z_to_bv 8 0) :: CB 3 p1 :: C4 (Z_to_bv 64 0) :: C4 (Z_to_bv 64 1) :: CB 4 p2 :: C8 (Z_to_bv 64 0x64240) :: C8 nx :: [C8 (Z_to_bv 64 0x2916c)])
      with ([C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 1)] ++ [CB 4 p2] ++ [C8 (Z_to_bv 64 0x64240)] ++ [C8 nx] ++ [C8 (Z_to_bv 64 0x2916c)]) in H.
    apply rw_cells_split in H as [_ H]. apply rw_cells_split in H as [H1 H]. apply rw_cells_split in H as [_ H].
    apply rw_cells_split in H as [H2 H]. apply rw_cells_split in H as [_ H3].
    cbn [cells_size csize Nat.add] in H1, H2, H3. nrm H1. nrm H2. nrm H3.
    unfold ax_cells. split; [exact H1 | split; [exact H2 | split; [exact H3 | exact A0]]].
  Qed.

  Lemma run_cps : forall (sp0 tid B bufA bufN : Z) (content : list byte) (MD0 : Model)
      (R : bvmap 5 word) (M : word -> option byte) (s : ai_AS AI) (LB0 : list ablock) (pb : bid) (e : word) (K0 : nat),
    let Lc := Z.of_nat (length content) in
    let cfglen := hdr_cfglen content in
    let paylen := Lc - 6 - cfglen in
    getr R 1 = Z_to_bv 64 0x136f4 -> getr R 2 = Z_to_bv 64 (sp0 - 128) -> getr R 4 = Z_to_bv 64 0x441e0 ->
    getr R 10 = Z_to_bv 64 (bufA + 2) -> getr R 11 = Z_to_bv 64 cfglen -> getr R 12 = Z_to_bv 64 (bufA + 6 + cfglen) ->
    getr R 13 = Z_to_bv 64 paylen -> getr R 9 = Z_to_bv 64 bufA -> getr R 18 = Z_to_bv 64 cfglen -> getr R 20 = Z_to_bv 64 paylen ->
    getr R 21 = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64) ->
    getr R 22 = Z_to_bv 64 0x340d9 ->                                  (* [comment removed for export] *)
    0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0 -> alloc_ceiling = sp0 - 8388608 -> 0 < tid < 2 ^ 22 ->
    6 + cfglen <= Lc -> Lc < 2 ^ 26 -> 0x66000 <= bufA ->
    stk s0segs M (sp0 - 8388608) (sp0 - 128) -> mem_inv s0segs M -> statics sp0 tid M -> stdout_untouched M ->
    rw_cells s0segs M 0x440e0 [C1 (Z_to_bv 8 0)] ->
    rw_cells s0segs M bufA [CB (length content) content] ->
    rw_cells s0segs M (errno_cell L) [C4 e] ->
    ai_inv AI s LB0 M MD0 -> In (pb, bufA, bufN) LB0 -> Lc <= bufN ->
    ai_aux AI M B -> sp0 <= B -> (forall n, 0 < n < 2 ^ 26 -> ai_sys_ok AI s LB0 n MD0) ->
    ac_c21 AC C21_none s LB0 -> ac_vm AC K0 s MD0 -> (80 <= K0)%nat ->
    fds_ok MD0 ->
    realizes s0segs (mkCfg (mkst R (Z_to_bv 64 0x13850) M (seg_rom s0segs)) MD0) (t_target content (m_fs MD0)).
  Proof.
    intros until K0. intros Lc cfglen paylen R1 R2 R4 R10 R11 R12 R13 R9 R18 R20 R21 R22 SP0 alloc_ceiling_val TID HL1 HL2 BUFLO ST MI STAT SU INI CONT ERR
           INV BUFB BUFN AUX HB SYS C21 VM K0LE FDS.
    pose proof (callsN_range content) as CR4.
    assert (VM' : ac_vm AC (ac_cost paylen + credit (callsN content)) s MD0).
    { eapply (ac_vm_le _ _ _ AC); [exact VM|]. unfold ac_cost, credit, HARN_VM_NEED. destruct (paylen <? 1024); lia. }
    pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)) as HC.
    assert (CF : 0 <= cfglen < 32768) by (subst cfglen; unfold hdr_cfglen; lia).
    destruct (ai_inv_model AI INV) as [Hh Hl].
    pose proof (ai_inv_blocks AI INV BUFB) as BOK. cbn [blk_addr blk_size fst snd] in BOK.
    cps_destruct BOK as (BK1 & BK2 & BK3 & BK4 & BK5). cbn [al_img_lo al_img_hi S0_layout] in BK5. rewrite alloc_ceiling_val in BK4.
    set (b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))).
    assert (Hb2 : 0 <= b2 < 256) by (subst b2; pose proof (bv_unsigned_in_range 8 (nth 2 content (Z_to_bv 8 0))) as X; change (bv_modulus 8) with 256 in X; lia).
    assert (CFG : rw_cells s0segs M (bufA + 2) [C1 (Z_to_bv 8 b2)]).
    { replace (Z_to_bv 8 b2) with (nth 2 content (Z_to_bv 8 0)) by (subst b2; apply bv_eq; symmetry; apply Z_to_bv_small; change (bv_modulus 8) with 256; lia).
      apply (rw_cells_byte M bufA (length content) content 2 CONT). lia. }
    pose proof (got_of_statics _ _ M STAT) as GOT.
    destruct (atx_init_of_statics _ _ _ STAT) as (p1 & p2 & AX0 & A00 & NL0).
    pose proof (flag_of_statics _ _ _ STAT) as FLG0.
    apply realizes_to_mkR. unfold mkR_of. rewrite R1, R2, R4, R9, R10, R11, R12, R13, R18, R20, R21, R22.
    rewrite t_target_unfold.
    assert (SPM : bv_unsigned (Z_to_bv 64 (sp0 - 128)) = sp0 - 128) by (apply u64_lit; lia).
    eapply (evt_realizes s0segs); [exact Hh | exact Hl | |].
    { eapply trP with (lo := sp0 - 8388608); rewrite ?SPM;
        [exact ST | lia | lia | exact MI | exact INI | exact GOT | exact AX0 | exact A00 | exact NL0]. }
    (intros ms1; cps_intros (x0 & x1 & x2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x3 & x4 & x5 & x6 & m1 & junk8 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & INI1 & AX1 & A01)).
    rewrite !SPM in *. replace (sp0 - 128 + -80) with (sp0 - 208) in * by lia.
    assert (PR1 := pres_of_munch _ _ _ MU1 WM1).
    assert (INV1 : ai_inv AI s LB0 m1 MD0).
    { eapply (ai_inv_frame AI); [exact INV | exact MU1 | exact WM1 |].
      apply Forall_cons; [apply cwo_stack; rewrite alloc_ceiling_val; lia|].
      repeat (apply Forall_cons; [apply cwo_data; lia|]). apply Forall_nil. }
    assert (AUX1 : ai_aux AI m1 B).
    { eapply (ai_aux_frame AI); [exact AUX | exact MU1 | exact WM1 |].
      aux_fp. }
    assert (ERR1 : rw_cells s0segs m1 (errno_cell L) [C4 e]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | unfold errno_cell, S0_layout; cbn; lia]. }
    assert (STAT1 : statics1 sp0 tid m1).
    { eapply statics1_of; [exact PR1 | | exact (proj1 SP0) | exact STAT | eapply ax_cells_of; [exact AX1 | exact A01]].
      intros a Ha. unfold core1_addr, OFL in Ha. cbn [in_ivs S_IVS1] in Ha. cbn. first [ solve [clear - SP0 Ha; lia] | lia ]. }
    assert (SU1 : stdout_untouched m1).
    { eapply stdout_untouched_pres; [exact PR1 | | exact SU]. intros a Ha. unfold stdout_addr, SO_FILE, SO_BUF in Ha. cbn. lia. }
    assert (CONT1 : rw_cells s0segs m1 bufA [CB (length content) content]).
    { eapply rw_cells_transport; [exact CONT | exact MU1 | exact WM1 | cbn; lia]. }
    assert (CFG1 : rw_cells s0segs m1 (bufA + 2) [C1 (Z_to_bv 8 b2)]).
    { eapply rw_cells_transport; [exact CFG | exact MU1 | exact WM1 | cbn; lia]. }
    assert (FLG1 : rw_cells s0segs m1 0x440e4 [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_transport; [exact FLG0 | exact MU1 | exact WM1 | cbn; lia]. }
    destruct (length content - 6 - Z.to_nat (hdr_cfglen content))%nat eqn:EP.
    - (* [comment removed for export] *)
      assert (P0 : paylen = 0) by (subst paylen Lc cfglen; lia).
      eapply (evt_realizes s0segs); [exact Hh | exact Hl | |].
      { eapply trA0 with (b2 := b2); rewrite ?u64_lit by lia; [exact MI1 | exact CFG1 | exact Hb2 | exact P0]. }
      (intros ms2; cps_intros (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & ->)).
      rewrite (u64_lit cfglen) by lia.
      replace (calls_of cfglen b2) with (Z.of_nat (callsN content)) by (subst b2 cfglen; apply callsN_calls_of).
      rewrite P0.
      change (t_emit (W 1 (zero_lines (callsN content))) (t_exit (exit_code 0) (m_fs MD0)))
        with (REM (callsN content) 0 (callsN content) (m_fs MD0)).
      eapply (loop_cps sp0 tid B bufA bufN 0 0x440f0 pb pb (skipn (6 + Z.to_nat (hdr_cfglen content)) content) (callsN content)) with (i := 0%nat);
        [exact SP0 | exact alloc_ceiling_val | exact TID | exact HB | rewrite skipn_length; cbn; lia | left; split; reflexivity | apply callsN_range | lia | lia |].
      constructor.
      + exists s. split; [exact INV1 | eapply (ac_vm_le _ _ _ AC); [exact VM| unfold credit, HARN_VM_NEED; lia]].
      + exact AUX1.
      + exact MI1.
      + exact ST1.
      + exists e. exact ERR1.
      + constructor.
        * exact STAT1.
        * exists junk8. rewrite P0 in FR1. exact FR1.
        * replace (skipn (6 + Z.to_nat (hdr_cfglen content)) content) with (@nil byte)
            by (symmetry; apply skipn_all2; subst paylen Lc cfglen; lia).
          apply bytes_at_nil. lia.
        * cbn. exact SU1.
      + intros; lia.
      + intros; lia.
      + exact BUFB.
      + exact FDS.
      + exact FLG1.
    - (* [comment removed for export] *)
      assert (PP : 0 < paylen < 2 ^ 26) by (subst paylen Lc cfglen; lia).
      assert (PLU : bv_unsigned (Z_to_bv 64 paylen) = paylen) by (apply u64_lit; lia).
      eapply (evt_realizes s0segs); [exact Hh | exact Hl | |].
      { eapply trA with (b2 := b2); rewrite ?u64_lit by lia; [exact MI1 | exact CFG1 | exact Hb2 | lia]. }
      (intros ms2; cps_intros (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & ->)).
      rewrite (u64_lit cfglen) by lia.
      replace (calls_of cfglen b2) with (Z.of_nat (callsN content)) by (subst b2 cfglen; apply callsN_calls_of).
      (* [comment removed for export] *)
      eapply (ac_malloc_sys AC) with (s := s) (LB := LB0) (k := credit (callsN content)) (n := paylen) (lo := sp0 - 8388608) (B := B) (errv := e);
        rewrite ?u64_lit by lia;
        [exact INV1 | apply SYS; lia | exact VM' | exact C21 | exact AUX1 | lia | exact ST1 | rewrite alloc_ceiling_val; lia | cbn [al_stack S0_layout]; lia
        | exact ERR1 | exact MI1 | reflexivity | reflexivity | unfold MAX_REQ_C; lia |].   (* [comment removed for export] *)
      + (* [comment removed for export] *)
        intros s2 m2 MD2 r p y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 errv2 junk INV2 VMO2 VM2 C212 MI2 ST2 ERR2 AUX2 HP2 Hr BO NIP DST.
        rewrite ?u64_lit in ST2 by lia. rewrite ?u64_lit in HP2 by lia. rewrite ret_pc_lit by lia.
        destruct (ai_inv_model AI INV2) as [Hh2 Hl2].
        cps_pose BO as (BO1 & BO2 & BO3 & BO4 & BO5). cbn [al_img_lo al_img_hi S0_layout] in BO5. rewrite alloc_ceiling_val in BO4.
        pose proof (pres_of_heap_pres _ _ _ _ _ HP2) as PR2.
        assert (CONT2 : rw_cells s0segs m2 bufA [CB (length content) content]).
        { eapply pres_rw_cells; [exact PR2 | exact CONT1 |]. cbn. intros a Ha. right; right. exists (pb, bufA, bufN). split; [exact BUFB|]. cbn. lia. }
        assert (SEP : bufA + bufN <= r \/ r + paylen <= bufA).
        { pose proof (ai_inv_disjoint AI (b1 := (pb, bufA, bufN)) (b2 := (p, r, paylen)) INV2
                        ltac:(right; exact BUFB) ltac:(left; reflexivity)) as D.
          cbn [blk_addr blk_size fst snd] in D. apply D. intros E. injection E as E0 E1 E2.
          apply NIP. rewrite <- E0. apply in_map_iff. exists (pb, bufA, bufN). split; [reflexivity| exact BUFB]. }
        (* [comment removed for export] *)
        assert (PAY : bytes_at s0segs m2 (bufA + 6 + cfglen) (skipn (6 + Z.to_nat cfglen) content)).
        { pose proof (rw_cells_bytes_at m2 bufA _ CONT2) as BA. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
          rewrite <- (firstn_skipn (6 + Z.to_nat cfglen) content) in BA.
          apply (proj1 (bytes_at_app s0segs m2 bufA _ _)) in BA. destruct BA as [_ BA].
          rewrite firstn_length in BA. replace (bufA + Z.of_nat (Nat.min (6 + Z.to_nat cfglen) (length content))) with (bufA + 6 + cfglen) in BA by lia.
          exact BA. }
        assert (PAYL : Z.of_nat (length (skipn (6 + Z.to_nat cfglen) content)) = paylen) by (rewrite skipn_length; subst paylen Lc; lia).
        eapply (evt_realizes s0segs); [exact Hh2 | exact Hl2 | apply trB; [rewrite u64_lit by lia; lia | exact MI2] |].
        (intros ms3; cps_intros (z0 & z1 & z2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & ->)).
        eapply memcpy_cps with (dst := r) (src := bufA + 6 + cfglen) (n := paylen) (bs := skipn (6 + Z.to_nat cfglen) content) (junk := junk);
          [reflexivity | reflexivity | reflexivity | exists 0x138c8; split; [reflexivity| lia] | exact DST | exact PAY | exact PAYL
          | lia | lia | lia | exact Hh2 | exact Hl2 | exact MI2 |].
        intros w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 m3 MU3 WM3 MI3 DST3 SRC3.
        rewrite ret_pc_lit by lia.
        pose proof (pres_of_munch _ _ _ MU3 WM3) as PR3.
        eapply (evt_realizes s0segs); [exact Hh2 | exact Hl2 | apply trC; exact MI3 |].
        intros ms4 ->.
        (* [comment removed for export] *)
        replace (Z_to_bv 64 r) with (Z_to_bv 64 (owA paylen r)) at 3 by (unfold owA; replace (paylen =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        rewrite <- (vm_only_fs _ _ VMO2).
        change (t_emit (W 1 (zero_lines (callsN content))) (t_exit (exit_code 0) (m_fs MD2)))
          with (REM (callsN content) 0 (callsN content) (m_fs MD2)).
        eapply (loop_cps sp0 tid B bufA bufN paylen r p pb (skipn (6 + Z.to_nat cfglen) content) (callsN content)) with (i := 0%nat);
          [exact SP0 | exact alloc_ceiling_val | exact TID | exact HB | lia | right; split; [lia| exact BO] | apply callsN_range | lia | lia |].
        constructor.
        * exists s2. split; [| exact VM2]. eapply (ai_inv_frame AI); [exact INV2 | exact MU3 | exact WM3 |].
          apply Forall_cons; [| apply Forall_nil]. right; right. exists (p, r, paylen). split; [left; reflexivity|]. cbn. lia.
        * eapply (ai_aux_frame AI); [exact AUX2 | exact MU3 | exact WM3 |].
          aux_fp.
        * exact MI3.
        * eapply stk_transport_disjoint; [exact ST2 | exact MU3 | exact WM3 | cbn; lia].
        * exists errv2. eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 | unfold errno_cell, S0_layout; cbn; lia].
        * constructor.
          -- eapply statics1_pres; [exact PR3 | | exact (proj1 SP0) |].
             ++ intros a Ha. unfold statics1_addr, core1_addr, ax_addr, OFL in Ha. cbn [in_ivs S_IVS1] in Ha. cbn. first [ solve [clear - BO4 BO5 Ha; lia] | lia ].
             ++ eapply statics1_pres; [exact PR2 | | exact (proj1 SP0) | exact STAT1]. intros a Ha. apply (statics1_client sp0); [lia| exact Ha].
          -- exists junk8. eapply rw_cells_transport; [| exact MU3 | exact WM3 | cbn; lia].
             eapply pres_rw_cells; [exact PR2 | exact FR1 |]. cbn. intros a Ha. left. lia.
          -- pose proof (rw_cells_bytes_at m3 r _ DST3) as BA. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA.
          -- cbn. eapply stdout_untouched_pres; [exact PR3 | |].
             ++ intros a Ha. unfold stdout_addr, SO_FILE, SO_BUF in Ha. cbn. first [ solve [clear - BO5 Ha; lia] | lia ].
             ++ eapply stdout_untouched_pres; [exact PR2 | | exact SU1]. intros a Ha. unfold stdout_addr, SO_FILE, SO_BUF in Ha. right; left.
                unfold errno_cell, S0_layout, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
        * intros _. left. reflexivity.
        * intros _ E. apply NIP. rewrite E. apply in_map_iff. exists (pb, bufA, bufN). split; [reflexivity| exact BUFB].
        * right. exact BUFB.
        * unfold fds_ok. rewrite (vm_only_fds _ _ VMO2). exact FDS.
        * eapply rw_cells_transport; [| exact MU3 | exact WM3 | cbn; lia].
          eapply pres_rw_cells; [exact PR2 | exact FLG1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; left.
          unfold S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
  Qed.
End TargetRun.

End ACeilS1.
