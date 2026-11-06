(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep ITree ITreeCfg Nodes NodesCfg Decode Arr FP InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg TrzLeafCfg ImplSplitCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc Monad StdioBase Stdio FmtFp Driver RawAlloc MSafe MLive.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface R_StartupLib R_Startup R_Exit RF_pad RF_stdio_lib Stdio_iface RF_printf_iface Stdio_init RF_syscalls RF_memcpy RF_fwritex_gen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RDrv_iface RDrv_ctx RDrv_kio RDrv_A RDrv_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shiftr26_zero_iff : forall a, 0 <= a -> (Z.shiftr a 26 = 0 <-> a < 67108864).
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  split; intros H; [| apply Z.div_small; lia].
  destruct (Z.lt_ge_cases a 67108864) as [L|G]; [exact L|]. exfalso.
  pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) G) as M. rewrite Z.div_same in M by lia. lia.
Qed.

Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
  rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells rsegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  assert (H : rw_cells rsegs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2. }
  destruct H as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  split; [split|].
  - cbn. rewrite length_app. split; [lia| exact I].
  - cbn [cells_bytes cbytes app] in HB |- *. rewrite !app_nil_r in HB |- *. exact HB.
  - replace (Z.of_nat (cells_size [CB (n1 + n2)%nat (b1 ++ b2)])) with (Z.of_nat (cells_size ([CB n1 b1] ++ [CB n2 b2]))) by (cbn; lia). exact HW.
Qed.

(* [comment removed for export] *)
Lemma bptr_eqb_refl : forall p, bptr_eqb p p = true.
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
  unfold lb_remove. rewrite filter_cons, bptr_eqb_refl. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
  apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.
Lemma lb_remove_second : forall p b0 b LB,
  blk_id b = p -> List.NoDup (map blk_id (b0 :: b :: LB)) -> lb_remove p (b0 :: b :: LB) = b0 :: LB.
Proof.
  intros p b0 b LB <- ND. unfold lb_remove. rewrite filter_cons.
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct (decide _) as [Y|N].
  - f_equal. apply (lb_remove_head b LB). exact ND.
  - exfalso. apply N. destruct (bptr_eqb (blk_id b0) (blk_id b)) eqn:E; [| exact I].
    apply bptr_eqb_eq in E. apply NI. left. symmetry. exact E.
Qed.

Lemma firstn_app_skipn_firstn : forall {A} (l : list A) n k,
  firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof.
  intros A l n k. revert l. induction n as [|n IH]; intros l; cbn; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.

Section C.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Variable HKG : HKG_T.
  Hypothesis DI : drv_iface HKG.
  Variable FS0 : Fs.Fs.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation HK := (HKG (G_fs FS0)).

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).

  Notation RDCORE' := (RDCORE sp0 argv envp uid hw rnd TID PAD S4 S5 S6 S7 HKG FS0).
  Notation RDINV' := (RDINV sp0 argv envp uid hw rnd TID PAD S4 S5 S6 S7 S8 S9 S10 S11 HKG FS0).
  Notation RDBRK' := (RDBRK sp0 argv envp uid hw rnd TID PAD S4 S5 S6 S7 S8 S9 S10 S11 HKG FS0).

  Let DIR := di_run HKG DI.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (P1v : Z) (pathb FILE : list byte).
  (* [comment removed for export] *)
  Variable KDONE : TSet.
  Hypothesis KDONE_nil : KDONE [].
  Hypothesis HBRK : forall cap s mo ms, RDBRK' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length FILE)))) cap FILE s mo ms ->
                    Z.of_nat (length FILE) < cap -> realizes_cfg acfg rsegs (mkCfg ms mo) KDONE.

  Definition TREF : TSet := TDIE pieces_too_big stdout_init FS0.
  (* [comment removed for export] *)
  Definition TFIN : TSet := if MAX_INPUT <=? Z.of_nat (length FILE) then TREF else KDONE.

  Lemma TFIN_nil : TFIN []. Proof. unfold TFIN. destruct (MAX_INPUT <=? _); [apply TDIE_nil | apply KDONE_nil]. Qed.

  (* [comment removed for export] *)
  Definition rmeas (cap : Z) (DATA : list byte) : Z := 2 * MAX_INPUT - Z.of_nat (length DATA) - cap.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rz_grow : forall (cap : Z) (DATA : list byte) (s : PState) mo
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z),
    RDCORE' 3 (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap DATA s mo mm fc A ->
    fs_lookup (m_fs mo) pathb = Some FILE -> DATA = firstn (length DATA) FILE ->
    Z.of_nat (length DATA) = cap ->
    (forall cap' s' mo' ms', rmeas cap' DATA < rmeas cap DATA ->
        fs_lookup (m_fs mo') pathb = Some FILE ->
        RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap' DATA s' mo' ms' ->
        realizes_cfg acfg rsegs (mkCfg ms' mo') TFIN) ->
    realizes_cfg acfg rsegs
      (mkCfg (RST 0x13568 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (Z.of_nat (length DATA)) 3 cap (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm) mo)
      TFIN.
  Proof.
    intros until A. intros RC FSL PRE FULL IH.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof STAGE_val as SV.
    destruct RC as (junk & stg & errv & bufp & BU & HKx & FD & FS & FR & BA & ERR & RSG & FRM).
    destruct BU as (BLK & [CAPR [k [Kk0 CAPK]]] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4. unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST. unfold MFRAME in FR. unfold RERRNO in ERR.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    pose proof (f_equal (@length byte) PRE) as LD. rewrite length_firstn in LD.
    set (LEN := Z.of_nat (length DATA)) in *.
    rz_seg Hh Hl.
    zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (GE : 67108864 <= cap).
      { destruct (Z.lt_ge_cases cap 67108864) as [L|G]; [| exact G]. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff LEN ltac:(lia))). lia. }
      pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G78 & GD0).
      zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      assert (TLE : TFIN = TREF).
      { unfold TFIN. replace (MAX_INPUT <=? Z.of_nat (length FILE)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia). reflexivity. }
      rewrite TLE. unfold TREF. rewrite <- FS.
      eapply (rz_fprintf_exit sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP RCSP HT HKG DI DTooBig _ s [(bufp, A, cap)]);
        [| | exact BA | exact HKx | exact FRM].
      - cbn [diag_args]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity.
      - cbn [diag_pieces pieces_too_big]. unfold INTERNAL_BUFSIZ, WRITEV_MAX, zlength.
        repeat constructor; cbn [length str list_ascii_of_string map app]; lia. }
    (* [comment removed for export] *)
    assert (LTM : cap < 67108864).
    { rewrite <- FULL. apply (proj1 (shiftr26_zero_iff LEN ltac:(lia))). exact K0. }
    assert (CAP2 : cap * 2 <= 67108864).
    { pose proof LTM as LTM'. rewrite CAPK in LTM' |- *. change 67108864 with (2 ^ 26) in LTM' |- *. apply Z.pow_lt_mono_r_iff in LTM'; [| lia| lia].
      replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    zstep. zstep. zstep. apply evt_done.
    replace (Z.shiftl LEN 1) with (cap * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    eapply (di_mallocX HKG DI (G_fdfs (m_fds mo) FS0) (frame_ok_G_fdfs _ _)) with (lo := usp0 - 8388608) (B := usp0) (s := s) (LB := [(bufp, A, cap)]) (n := cap * 2);
      try reflexivity.
    all: unfold RATP; rewrite ?(unsigned_lit 0x34d40) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia.
    - apply TFIN_nil.
    - apply (di_pin_fds HKG DI). exact HKx.
    - exact AUX.
    - lia.
    - exact ST.
    - lia.
    - unfold RMALLOC_STACK. lia.
    - exact ERR.
    - exact MI.
    - unfold NUSERc. lia.
    - (* [comment removed for export] *)
      intros v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 m2 mo2 s2 errv2 p A' MI2 ST2 ERR2 AUX2 HPR EA0 BR' HK2 [junk' NBLK].
      subst c0.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0x1357c)) with (Z_to_bv 64 0x1357c) by (symmetry; rpc).
      destruct (di_fdfs HKG DI _ _ _ _ _ _ HK2) as [FDS2 FS2].
      assert (BA2 : BASE' m2) by (eapply (BASE_heap_pres sp0 argv envp uid hw rnd TID); [exact BA| exact HPR| exact MI2| unfold LO; exact ST2| exact AUX2]).
      assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
      assert (BLK2 : rw_cells rsegs m2 A [CB (length DATA) DATA; CB (Z.to_nat (cap - LEN)) junk]).
      { eapply rheap_pres_rw_cells; [exact HPR| exact BLK|]. right; right. exists (bufp, A, cap). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
      assert (RSG2 : RSTG m2 stg).
      { unfold RSTG in *. eapply rheap_pres_rw_cells; [exact HPR| exact RSG|]. right; left.
        cbn [cells_size csize Nat.add]. unfold RSTAGE, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
      clear FR BLK ST MI AUX IMG RS SE SOF YSx TRx ERR RSG.
      pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). unfold alloc_ceiling in BQ4.
      destruct (di_blocks HKG DI _ _ _ _ _ HK2) as (_ & DISJ0 & ND).
      assert (DISJ : A' + cap * 2 <= A \/ A + cap <= A').
      { pose proof (DISJ0 (p, A', cap * 2) (bufp, A, cap) ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
        cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E. left. reflexivity. }
      pose proof BA2 as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST.
      destruct (DIR _ _ _ _ _ HK2) as (Hmi2 & Hh2 & Hl2).
      rz_seg Hh2 Hl2.
      unfold wz. zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      zstep. zstep. if_cases K2; zify_cond K2; try (exfalso; rewrite ?unsigned_lit in K2 by lia; lia). clear K2.
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB _ _ _ [] _ _ [] [length DATA; Z.to_nat (cap * 2) - length DATA]%nat) in NBLK; [| cbn; lia]. cbn [mk_CB_cells app] in NBLK.
      apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) (firstn (length DATA) junk')] _)) in NBLK. destruct NBLK as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
      pose proof BLK2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
      pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
      eapply evt_cut.
      { eapply memcpy_callw with (src := DATA) (junk := firstn (length DATA) junk');
          [exact SRCB| lia| replace (Z.to_nat LEN) with (length DATA) by lia; exact NB1| lia| lia| lia| lia| exact MI]. }
      cbv beta. intros ms' PO.
      destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MUc & WMc & MI3 & NB1' & _).
      transport_after_call rsegs m2 m3 MUc WMc.
      replace (ret_pc (Z_to_bv 64 0x13598)) with (Z_to_bv 64 0x13598) by (symmetry; rpc).
      assert (WOKW : Forall (WOK sp0) [(A', A' + LEN)]).
      { unfold WOK, alloc_ceiling. constructor; [cbn [fst snd]; lia| constructor]. }
      assert (HK3 : HKG (G_fdfs (m_fds mo) FS0) s2 [(p, A', cap * 2); (bufp, A, cap)] m3 mo2).
      { eapply (di_frame HKG DI); [exact HK2| exact MUc| exact WMc|].
        constructor; [| constructor]. right; right. exists (p, A', cap * 2). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
      assert (BA3 : BASE' m3) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP RCSP VARGV VENVP); [exact BA2| exact WOKW| exact MUc| exact WMc| exact MI3| unfold LO; exact ST]).
      assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc|exact WMc] | exact FR2 | intros ax Ha; cbn in Ha |- *; lia]).
      assert (RSG3 : RSTG m3 stg).
      { unfold RSTG in *. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc|exact WMc] | exact RSG2 |].
        intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; unfold RSTAGE in *; lia. }
      clear MUc WMc BA2 ST MI RS AUX IMG SE SOF YSx TRx WOKW RSG2.
      pose proof BA3 as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST.
      (* [comment removed for export] *)
      zstep. zstep. apply evt_done.
      eapply (di_freeX HKG DI (G_fdfs (m_fds mo) FS0) (frame_ok_G_fdfs _ _)) with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap);
        try reflexivity.
      all: unfold RATP; rewrite ?(unsigned_lit 0x34d40) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia.
      + apply TFIN_nil.
      + exact HK3.
      + right; left; reflexivity.
      + exact AUX.
      + lia.
      + exact ST.
      + lia.
      + unfold RFREE_STACK. lia.
      + exact ERR2.
      + exact MI.
      + intros w0' w1' w2' rb0 e1 e2 e3 e4 e5 e6 e7 w3' w4' w5' w6' m4 mo4 s4 MI4 ST4 ERR4 AUX4 HPR4 HK4.
        rewrite ?(unsigned_lit (usp0 + -128)) in ST4 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR4 by lia.
        replace (ret_pc (Z_to_bv 64 0x135a0)) with (Z_to_bv 64 0x135a0) by (symmetry; rpc).
        rewrite (lb_remove_second bufp (p, A', cap * 2) (bufp, A, cap) [] eq_refl ND) in HPR4, HK4.
        destruct (di_fdfs HKG DI _ _ _ _ _ _ HK4) as [FDS4 FS4].
        apply (di_unpin_fds HKG DI) in HK4.
        assert (BA4 : BASE' m4) by (eapply (BASE_heap_pres sp0 argv envp uid hw rnd TID); [exact BA3| exact HPR4| exact MI4| unfold LO; exact ST4| exact AUX4]).
        assert (FR4 : FRAME' m4) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR4| exact FR3| left; cbn; lia]).
        assert (RSG4 : RSTG m4 stg).
        { unfold RSTG in *. eapply rheap_pres_rw_cells; [exact HPR4| exact RSG3|]. right; left.
          cbn [cells_size csize Nat.add]. unfold RSTAGE, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
        assert (NB4 : rw_cells rsegs m4 A' [CB (length DATA) DATA; CB (Z.to_nat (cap * 2 - LEN)) (firstn (Z.to_nat (cap * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
        { eapply rheap_pres_rw_cells; [exact HPR4| |].
          - apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split; [replace (length DATA) with (Z.to_nat LEN) at 1 by lia; exact NB1'|].
            cbn [cells_size csize Nat.add]. replace (Z.to_nat (cap * 2 - LEN)) with (Z.to_nat (cap * 2) - length DATA)%nat by lia.
            first [exact NB2 | replace (A' + Z.of_nat (length DATA + 0)) with (A' + Z.of_nat (Z.to_nat LEN + 0)) by lia; exact NB2
                   | replace (A' + Z.of_nat (Z.to_nat LEN + 0)) with (A' + Z.of_nat (length DATA + 0)) by lia; exact NB2].
          - right; right. exists (p, A', cap * 2). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
        (* [comment removed for export] *)
        apply (IH (cap * 2) s4 mo4); [unfold rmeas; lia | rewrite FS4; rewrite <- FS; exact FSL |].
        unfold RDINV. do 17 eexists. exists F, fc, m4, A'. split; [reflexivity|]. split; [| lia].
        unfold RDCORE. exists (firstn (Z.to_nat (cap * 2) - length DATA)%nat (skipn (length DATA) junk')), stg, errv2, p.
        split. { unfold BUFC. split; [exact NB4|]. unfold MAX_INPUT. split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|]. split; [lia| exact BR']. }
        split; [exact HK4|]. split; [first [rewrite FDS4; exact FD | rewrite FDS4, <- FDS2; exact FD | rewrite FDS4, FDS2; exact FD]|]. split; [exact FS4|].
        split; [exact FR4|]. split; [exact BA4|]. split; [unfold RERRNO; exact ERR4|]. split; [exact RSG4| exact FRM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rz_read_part : forall (cap : Z) (DATA : list byte) (s : PState) mo
      x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A CNT : Z),
    RDCORE' 3 (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap DATA s mo mm fc A ->
    fs_lookup (m_fs mo) pathb = Some FILE -> DATA = firstn (length DATA) FILE ->
    Z.of_nat (length DATA) < cap -> 0 < CNT <= 65536 -> CNT <= cap - Z.of_nat (length DATA) ->
    (forall cap' DATA' s' mo' ms', rmeas cap' DATA' < rmeas cap DATA -> fs_lookup (m_fs mo') pathb = Some FILE -> DATA' = firstn (length DATA') FILE ->
        RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA')))) cap' DATA' s' mo' ms' -> realizes_cfg acfg rsegs (mkCfg ms' mo') TFIN) ->
    realizes_cfg acfg rsegs
      (mkCfg (GST 0x135b0 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 (Z_to_bv 64 CNT) a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (Z.of_nat (length DATA))) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm) mo)
      TFIN.
  Proof.
    intros until CNT. intros RC FSL PRE LT CNTR CNTC IH.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof STAGE_val as SV.
    pose proof RC as RC0.
    destruct RC as (junk & stg & errv & bufp & BU & HKx & FD & FS & FR & BA & ERR & RSG & FRM).
    destruct BU as (BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4. unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST. unfold MFRAME in FR. unfold RERRNO in ERR.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    set (LEN := Z.of_nat (length DATA)) in *.
    (* [comment removed for export] *)
    pose proof RSG as DST0. unfold RSTG in DST0. pose proof (rw_cells_bound _ _ _ _ DST0) as STGB. cbn [cells_size csize Nat.add] in STGB.
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat CNT; Z.to_nat STAGE - Z.to_nat CNT]%nat) in DST0; [| cbn; lia]. cbn [mk_CB_cells app] in DST0.
    apply (proj1 (rw_cells_app _ _ _ [CB (Z.to_nat CNT) (firstn (Z.to_nat CNT) stg)] _)) in DST0. destruct DST0 as [DST REST]. cbn [cells_size csize Nat.add] in REST.
    rz_seg Hh Hl. zstep. zstep. zstep. apply evt_done.
    (* [comment removed for export] *)
    pose proof (read_spec (Z_to_bv 64 0x135bc) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A)
                  (Z_to_bv 64 3) (Z_to_bv 64 RSTAGE) (Z_to_bv 64 CNT) a3 a4 a5 a6 a7
                  (Z_to_bv 64 P1v) (Z_to_bv 64 LEN) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6 F fc mm
                  3 CNT (firstn (Z.to_nat CNT) stg) errv (usp0 - 8388608)) as IMR.
    rewrite !(unsigned_lit RSTAGE) in IMR by (unfold RSTAGE; lia).
    specialize (IMR ltac:(rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST) DST
                    ltac:(unfold RATP; rewrite (unsigned_lit 0x34d40) by lia; exact ERR) MI eq_refl eq_refl ltac:(lia) ltac:(lia)
                    ltac:(unfold RSTAGE, TASK_SIZE; lia)).
    do 4 (specialize (IMR ltac:(unfold RATP, RSTAGE; rewrite ?(unsigned_lit 0x34d40) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; lia))).
    specialize (IMR ltac:(unfold RATP; rewrite ?(unsigned_lit 0x34d40) by lia; lia)).
    set (bs := firstn (Z.to_nat CNT) (skipn (length DATA) FILE)).
    set (mo2 := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 3) (FdFile pathb (Z_to_bv 64 (LEN + Z.of_nat (length bs))))) mo).
    assert (RO : read_out 3 RSTAGE CNT mo = Some (RdData bs, mo2)).
    { unfold read_out. rewrite FD, FSL. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia.
      replace (Z.to_nat LEN) with (length DATA) by lia. subst bs mo2. unfold len_word. rewrite lit_add_lit. reflexivity. }
    eapply (rz_read 3 RSTAGE CNT _ _ mo); [exact IMR | exact Hmi | exact Hh | lia | apply TFIN_nil | exact RO |].
    intros ms' rsp evs Hst PO Hmi2 Hh2.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
    cbn [read_ret] in *. destruct RES as (STG2 & ERR2 & Hbs).
    unfold RATP in MUc, ERR2. rewrite ?(unsigned_lit 0x34d40) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit 0x34d40) in ERR2 by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. change (0x34d40 + -164) with RERRNO in MUc, ERR2.
    replace (ret_pc (Z_to_bv 64 0x135bc)) with (Z_to_bv 64 0x135bc) by (symmetry; rpc).
    (* [comment removed for export] *)
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 16, usp0 + -128); (RSTAGE, RSTAGE + Z.of_nat (Z.to_nat CNT)); (RERRNO, RERRNO + 4)]).
    { unfold WOK, LO, RERRNO, alloc_ceiling. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2]).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (FR2 : FRAME' m2).
    { unfold MFRAME. eapply rw_cells_agree; [exact AG | exact FR | intros ax Ha; cbn in Ha |- *; unfold RERRNO, RSTAGE; lia]. }
    assert (BLK2 : rw_cells rsegs m2 A [CB (length DATA) DATA; CB (Z.to_nat (cap - LEN)) junk]).
    { eapply rw_cells_agree; [exact AG | exact BLK | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; unfold RERRNO, RSTAGE; lia]. }
    assert (REST' : rw_cells rsegs m2 (RSTAGE + Z.of_nat (Z.to_nat CNT + 0)) [CB (Z.to_nat STAGE - Z.to_nat CNT) (firstn (Z.to_nat STAGE - Z.to_nat CNT) (skipn (Z.to_nat CNT) stg))]).
    { eapply rw_cells_agree; [exact AG | exact REST | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; unfold RERRNO, RSTAGE in *; lia]. }
    (* [comment removed for export] *)
    assert (HK2 : HK s [(bufp, A, cap)] m2 mo2).
    { eapply (di_mo HKG DI) with (n := NRead 3 RSTAGE CNT); [| exact I | exact Hst | subst mo2; apply m_vmmaps_with_fds | unfold G_fs; subst mo2; rewrite m_fs_with_fds; exact FS].
      eapply (di_frame HKG DI); [exact HKx | exact MUc | exact WMc |].
      constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RSTAGE, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
      constructor; [| constructor]. right; left. cbn [fst snd]. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
    assert (LBS : (length bs <= Z.to_nat CNT)%nat) by (subst bs; rewrite length_firstn; lia).
    assert (PRE' : DATA ++ bs = firstn (length DATA + length bs) FILE).
    { subst bs. rewrite PRE at 1. rewrite firstn_app_skipn_firstn. rewrite length_firstn, length_skipn.
      pose proof (f_equal (@length byte) PRE) as LD. rewrite length_firstn in LD.
      replace (length DATA + Nat.min (Z.to_nat CNT) (length FILE - length DATA))%nat with (Nat.min (length DATA + Z.to_nat CNT) (length FILE)) by lia.
      destruct (Nat.le_ge_cases (length DATA + Z.to_nat CNT) (length FILE)) as [Hle|Hge].
      - rewrite Nat.min_l by lia. reflexivity.
      - rewrite Nat.min_r by lia. rewrite firstn_all. rewrite firstn_all2 by lia. reflexivity. }
    (* [comment removed for export] *)
    pose proof STG2 as STGa. apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in STGa. destruct STGa as [STGa STGb]. cbn [cells_size csize Nat.add] in STGb.
    assert (RSG2 : RSTG m2 (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) stg) ++ firstn (Z.to_nat STAGE - Z.to_nat CNT) (skipn (Z.to_nat CNT) stg)))).
    { unfold RSTG. replace (Z.to_nat STAGE) with (length bs + ((Z.to_nat CNT - length bs) + (Z.to_nat STAGE - Z.to_nat CNT)))%nat at 1 by lia.
      apply rw_cells_CB_join; [exact STGa|]. rewrite <- (Nat.add_0_r (length bs)) at 1. apply rw_cells_CB_join; [exact STGb|].
      match goal with |- rw_cells _ _ ?a _ => replace a with (RSTAGE + Z.of_nat (Z.to_nat CNT + 0)) by lia end. exact REST'. }
    pose proof (rw_cells_bytes_at _ _ _ _ STGa) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
    clear MUc WMc WOKW AG BA ST MI RS AUX IMG SE SOF YSx TRx FR BLK DST REST IMR RO REST' STG2 STGb RSG.
    pose proof BA2 as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST.
    destruct (DIR _ _ _ _ _ HK2) as (_ & Hh' & Hl').
    rz_seg Hh' Hl'.
    zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 LBS CNTR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
    zstep. zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (NZ : length bs <> 0%nat) by (intros E; rewrite E in K1; apply K1; reflexivity).
      (* [comment removed for export] *)
      pose proof BLK2 as BLKx. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKx. destruct BLKx as [BLK1 BLKr].
      cbn [cells_size csize Nat.add] in BLKr. replace (length DATA + 0)%nat with (length DATA) in BLKr by lia.
      apply (rw_cells_split_CB _ _ _ [] _ _ [] [length bs; Z.to_nat (cap - LEN) - length bs]%nat) in BLKr; [| cbn; lia]. cbn [mk_CB_cells app] in BLKr.
      apply (proj1 (rw_cells_app _ _ _ [CB (length bs) (firstn (length bs) junk)] _)) in BLKr. destruct BLKr as [DSTB RESTB]. cbn [cells_size csize Nat.add] in RESTB.
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply memcpy_callw with (src := bs) (junk := firstn (length bs) junk);
          [exact SRCB| lia| replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; first [exact DSTB | replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; exact DSTB]
          | unfold RSTAGE; lia| lia| unfold RSTAGE; lia| lia| exact MI]. }
      cbv beta. intros ms' PO.
      destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MUc & WMc & MI3 & DSTB' & _).
      replace (ret_pc (Z_to_bv 64 0x13554)) with (Z_to_bv 64 0x13554) by (symmetry; rpc).
      assert (WOKW : Forall (WOK sp0) [(A + LEN, A + LEN + Z.of_nat (length bs))]).
      { unfold WOK, alloc_ceiling. constructor; [cbn [fst snd]; lia| constructor]. }
      assert (HK3 : HK s [(bufp, A, cap)] m3 mo2).
      { eapply (di_frame HKG DI); [exact HK2| exact MUc| exact WMc|].
        constructor; [| constructor]. right; right. exists (bufp, A, cap). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
      assert (ST3 : stk rsegs m3 (usp0 - 8388608) (usp0 + -128)).
      { eapply stk_transport_disjoint; [exact ST | exact MUc | exact WMc | cbn [disjoint_from]; lia]. }
      assert (BA3 : BASE' m3) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP RCSP VARGV VENVP); [exact BA2| exact WOKW| exact MUc| exact WMc| exact MI3| unfold LO; exact ST3]).
      pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG3.
      assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rw_cells_agree; [exact AG3 | exact FR2 | intros ax Ha; cbn in Ha |- *; lia]).
      assert (RSG3 : RSTG m3 (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) stg) ++ firstn (Z.to_nat STAGE - Z.to_nat CNT) (skipn (Z.to_nat CNT) stg)))).
      { unfold RSTG in *. eapply rw_cells_agree; [exact AG3 | exact RSG2 | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; unfold RSTAGE in *; lia]. }
      assert (ERR3 : rw_cells rsegs m3 RERRNO [C4 errv]).
      { eapply rw_cells_agree; [exact AG3 | unfold RERRNO; exact ERR2 | intros ax Ha; cbn in Ha |- *; unfold RERRNO in *; lia]. }
      assert (BLK1' : rw_cells rsegs m3 A [CB (length DATA) DATA]).
      { eapply rw_cells_agree; [exact AG3 | exact BLK1 | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; lia]. }
      assert (RESTB' : rw_cells rsegs m3 (A + LEN + Z.of_nat (length bs + 0)) [CB (Z.to_nat (cap - LEN) - length bs) (firstn (Z.to_nat (cap - LEN) - length bs) (skipn (length bs) junk))]).
      { eapply rw_cells_agree; [exact AG3 | exact RESTB | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; lia]. }
      (* [comment removed for export] *)
      assert (BLK' : rw_cells rsegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (cap - Z.of_nat (length (DATA ++ bs)))) (firstn (Z.to_nat (cap - LEN) - length bs) (skipn (length bs) junk))]).
      { pose proof (rw_cells_CB_join m3 A (length DATA) (length bs) DATA bs BLK1'
                      ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia;
                            replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) at 1 by lia; exact DSTB')) as J.
        apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split; [exact J|]. cbn [cells_size csize Nat.add].
        replace (Z.to_nat (cap - Z.of_nat (length DATA + length bs))) with (Z.to_nat (cap - LEN) - length bs)%nat by lia.
        replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + LEN + Z.of_nat (length bs + 0)) by lia. exact RESTB'. }
      clear MUc WMc WOKW AG3 BA2 ST MI RS AUX IMG SE SOF YSx TRx FR2 BLK2 BLK1 DSTB RESTB SRCB RSG2 ERR2 BLK1' RESTB' DSTB'.
      pose proof BA3 as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        apply evt_done.
        replace (Z.of_nat (length bs) + LEN) with (Z.of_nat (length (DATA ++ bs))) by (rewrite length_app; lia).
        eapply (rz_grow cap (DATA ++ bs) s mo2); [| subst mo2; rewrite m_fs_with_fds; exact FSL | rewrite length_app; exact PRE' | rewrite length_app; lia |].
        * unfold RDCORE. exists (firstn (Z.to_nat (cap - LEN) - length bs) (skipn (length bs) junk)), (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) stg) ++ firstn (Z.to_nat STAGE - Z.to_nat CNT) (skipn (Z.to_nat CNT) stg))), errv, bufp.
          split. { unfold BUFC. split; [exact BLK' | unfold MAX_INPUT; split; [split; [lia| exact CAPK]|]; split; [rewrite length_app; lia| exact BR]]. }
          split; [exact HK3|].
          split. { subst mo2. rewrite m_fds_with_fds, fd_lookup_insert_same. rewrite length_app. do 3 f_equal. lia. }
          split; [subst mo2; rewrite m_fs_with_fds; exact FS|].
          split; [exact FR3|]. split; [exact BA3|]. split; [exact ERR3|]. split; [exact RSG3| exact FRM].
        * intros cap' s' mo' ms' HM FSL' RI'. apply (IH cap' (DATA ++ bs) s' mo' ms'); [unfold rmeas in *; rewrite length_app in *; lia | exact FSL' | rewrite length_app; exact PRE' | exact RI'].
      + (* [comment removed for export] *)
        zstep. zstep. apply evt_done.
        apply (IH cap (DATA ++ bs) s mo2); [unfold rmeas; rewrite length_app; lia | subst mo2; rewrite m_fs_with_fds; exact FSL | rewrite length_app; exact PRE' |].
        unfold RDINV. do 17 eexists. exists F, fc, m3, A.
        split. { rewrite length_app. replace (Z.of_nat (length bs) + LEN) with (Z.of_nat (length DATA + length bs)%nat) by lia. reflexivity. }
        split; [| rewrite length_app; lia].
        unfold RDCORE. exists (firstn (Z.to_nat (cap - LEN) - length bs) (skipn (length bs) junk)), (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) stg) ++ firstn (Z.to_nat STAGE - Z.to_nat CNT) (skipn (Z.to_nat CNT) stg))), errv, bufp.
        split. { unfold BUFC. split; [exact BLK' | unfold MAX_INPUT; split; [split; [lia| exact CAPK]|]; split; [rewrite length_app; lia| exact BR]]. }
        split; [exact HK3|].
        split. { subst mo2. rewrite m_fds_with_fds, fd_lookup_insert_same. rewrite length_app. do 3 f_equal. lia. }
        split; [subst mo2; rewrite m_fs_with_fds; exact FS|].
        split; [exact FR3|]. split; [exact BA3|]. split; [exact ERR3|]. split; [exact RSG3| exact FRM].
    - (* [comment removed for export] *)
      assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]).
      assert (LENF : length DATA = length FILE).
      { pose proof (f_equal (@length byte) PRE) as L1. rewrite length_firstn in L1.
        assert (L2 : length bs = 0%nat) by (rewrite Ebs; reflexivity).
        unfold bs in L2. rewrite length_firstn, length_skipn in L2. lia. }
      assert (EDF : DATA = FILE) by (rewrite PRE, LENF, firstn_all; reflexivity).
      apply evt_done.
      assert (TLF : TFIN = KDONE).
      { unfold TFIN. replace (MAX_INPUT <=? Z.of_nat (length FILE)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia). reflexivity. }
      rewrite TLF. apply (HBRK cap s mo2); [| lia].
      rewrite EDF in BLK2.
      unfold RDBRK. do 17 eexists. exists F, fc, m2, A. split; [rewrite <- LENF; reflexivity|].
      unfold RDCORE. exists junk, (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) stg) ++ firstn (Z.to_nat STAGE - Z.to_nat CNT) (skipn (Z.to_nat CNT) stg))), errv, bufp.
      split. { unfold BUFC. split; [replace (Z.of_nat (length FILE)) with LEN by lia; exact BLK2 | unfold MAX_INPUT; split; [split; [lia| exact CAPK]|]; split; [lia| exact BR]]. }
      split; [exact HK2|].
      split. { subst mo2. rewrite m_fds_with_fds, fd_lookup_insert_same. do 3 f_equal. rewrite Ebs. cbn [length]. lia. }
      split; [subst mo2; rewrite m_fs_with_fds; exact FS|].
      split; [exact FR2|]. split; [exact BA2|]. split; [unfold RERRNO in ERR2; exact ERR2|]. split; [exact RSG2| exact FRM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rz_round : forall (cap : Z) (DATA : list byte) (s : PState) mo ms,
    RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap DATA s mo ms ->
    fs_lookup (m_fs mo) pathb = Some FILE -> DATA = firstn (length DATA) FILE ->
    (forall cap' DATA' s' mo' ms', rmeas cap' DATA' < rmeas cap DATA ->
        fs_lookup (m_fs mo') pathb = Some FILE -> DATA' = firstn (length DATA') FILE ->
        RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA')))) cap' DATA' s' mo' ms' ->
        realizes_cfg acfg rsegs (mkCfg ms' mo') TFIN) ->
    realizes_cfg acfg rsegs (mkCfg ms mo) TFIN.
  Proof.
    intros cap DATA s mo ms RI FSL PRE IH.
    destruct RI as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & -> & RC & LT).
    pose proof RC as RC0.
    destruct RC as (junk & stg & errv & bufp & BU & HKx & FD & FS & FR & BA & ERR & RSG & FRM).
    destruct BU as (BLK & [CAPR CAPK] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    set (LEN := Z.of_nat (length DATA)) in *.
    rz_seg Hh Hl.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K01; zify_cond K01.
    - (* [comment removed for export] *)
      apply evt_done.
      eapply (rz_read_part cap DATA s mo); [exact RC0 | exact FSL | exact PRE | lia | lia | lia | exact IH].
    - zstep. apply evt_done.
      eapply (rz_read_part cap DATA s mo); [exact RC0 | exact FSL | exact PRE | lia | lia | lia | exact IH].
  Qed.

  Lemma rz_loop : forall (fuel : nat) (cap : Z) (DATA : list byte) (s : PState) mo ms,
    rmeas cap DATA < Z.of_nat fuel ->
    RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap DATA s mo ms ->
    fs_lookup (m_fs mo) pathb = Some FILE -> DATA = firstn (length DATA) FILE ->
    realizes_cfg acfg rsegs (mkCfg ms mo) TFIN.
  Proof.
    induction fuel as [|fuel IH]; intros cap DATA s mo ms HM RI FSL PRE.
    - exfalso. destruct RI as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & _ & RC & LT).
      destruct RC as (junk & stg & errv & bufp & BU & _). destruct BU as (_ & [CAPR _] & LENR & _). unfold rmeas, MAX_INPUT in *. cbn in HM. lia.
    - eapply rz_round; [exact RI | exact FSL | exact PRE |].
      intros cap' DATA' s' mo' ms' HM' FSL' PRE' RI'. apply (IH cap' DATA' s' mo' ms'); [lia | exact RI' | exact FSL' | exact PRE'].
  Qed.

  (* [comment removed for export] *)
  Lemma rz_loop0 : forall (s : PState) mo ms,
    RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 0)) 65536 [] s mo ms ->
    fs_lookup (m_fs mo) pathb = Some FILE ->
    realizes_cfg acfg rsegs (mkCfg ms mo) TFIN.
  Proof.
    intros s mo ms RI FSL. apply (rz_loop (Z.to_nat (rmeas 65536 []) + 1) 65536 [] s mo ms); [unfold rmeas, MAX_INPUT; cbn; lia | exact RI | exact FSL | reflexivity].
  Qed.
End C.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CDir.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Variable HKG : HKG_T.
  Hypothesis DI : drv_iface HKG.
  Variable FS0 : Fs.Fs.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation HK := (HKG (G_fs FS0)).
  Notation RDINV' := (RDINV sp0 argv envp uid hw rnd TID PAD S4 S5 S6 S7 S8 S9 S10 S11 HKG FS0).
  Let DIR := di_run HKG DI.

  Variables (P1v : Z).
  Hypothesis HP1 : nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v).
  Hypothesis P1R : 0 <= P1v < 2^64.

  Lemma rz_loop_dir : forall (s : PState) mo ms,
    RDINV' 3 P1v FdDir 65536 [] s mo ms ->
    realizes_cfg acfg rsegs (mkCfg ms mo) (TDIE (pieces_read_error (map bv_unsigned arg1)) stdout_init FS0).
  Proof.
    intros s mo ms RI.
    destruct RI as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & -> & RC & _).
    destruct RC as (junk & stg & errv & bufp & BU & HKx & FD & FS & FR & BA & ERR & RSG & FRM).
    destruct BU as (BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4. unfold MAX_INPUT in CAPR.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof (IMGB_ts sp0 argv envp uid hw rnd EFIT) as ITS. pose proof STAGE_val as SV.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST. unfold MFRAME in FR. unfold RERRNO in ERR.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    cbn [length Z.of_nat] in *.
    pose proof RSG as DST. unfold RSTG in DST.
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat 65536; Z.to_nat STAGE - Z.to_nat 65536]%nat) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
    apply (proj1 (rw_cells_app _ _ _ [CB (Z.to_nat 65536) (firstn (Z.to_nat 65536) stg)] _)) in DST. destruct DST as [DST _].
    rz_seg Hh Hl.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K01; zify_cond K01; [exfalso; lia|].
    zstep. zstep. zstep. zstep. rewrite ?Z.sub_0_r. apply evt_done.
    (* [comment removed for export] *)
    pose proof (read_spec (Z_to_bv 64 0x135bc) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A)
                  (Z_to_bv 64 3) (Z_to_bv 64 RSTAGE) (Z_to_bv 64 65536) a3 a4 a5 a6 a7
                  (Z_to_bv 64 P1v) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6 F fc mm
                  3 65536 (firstn (Z.to_nat 65536) stg) errv (usp0 - 8388608)) as IMR.
    rewrite !(unsigned_lit RSTAGE) in IMR by (unfold RSTAGE; lia).
    specialize (IMR ltac:(rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST) DST
                    ltac:(unfold RATP; rewrite (unsigned_lit 0x34d40) by lia; exact ERR) MI eq_refl eq_refl ltac:(lia) ltac:(lia)
                    ltac:(unfold RSTAGE, TASK_SIZE; lia)).
    do 4 (specialize (IMR ltac:(unfold RATP, RSTAGE; rewrite ?(unsigned_lit 0x34d40) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; lia))).
    specialize (IMR ltac:(unfold RATP; rewrite ?(unsigned_lit 0x34d40) by lia; lia)).
    assert (RO : read_out 3 RSTAGE 65536 mo = Some (RdErr EISDIR, mo)) by (unfold read_out; rewrite FD; reflexivity).
    eapply (rz_read 3 RSTAGE 65536 _ _ mo); [exact IMR | exact Hmi | exact Hh | lia | apply TDIE_nil | exact RO |].
    intros ms' rsp evs Hst PO _ _.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
    cbn [read_ret] in *. destruct RES as (STG2 & ERR2 & He).
    unfold RATP in MUc, ERR2. rewrite ?(unsigned_lit 0x34d40) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit 0x34d40) in ERR2 by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. change (0x34d40 + -164) with RERRNO in MUc, ERR2.
    replace (ret_pc (Z_to_bv 64 0x135bc)) with (Z_to_bv 64 0x135bc) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 16, usp0 + -128); (RSTAGE, RSTAGE + Z.of_nat (Z.to_nat 65536)); (RERRNO, RERRNO + 4)]).
    { unfold WOK, LO, RERRNO, alloc_ceiling. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2]).
    assert (HK2 : HK s [(bufp, A, 65536)] m2 mo).
    { eapply (di_frame HKG DI); [exact HKx | exact MUc | exact WMc |].
      constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RSTAGE, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
      constructor; [| constructor]. right; left. cbn [fst snd]. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
    clear MUc WMc WOKW BA ST MI RS AUX IMG SE SOF YSx TRx.
    pose proof BA2 as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST.
    pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G78 & GD0).
    (* [comment removed for export] *)
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
    destruct (argv_cstring sp0 argv envp uid hw rnd m2 IMG 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IMGBD.
    assert (EP : p1 = P1v).
    { rewrite HP1 in HP1'. assert (E : bv_unsigned (Z_to_bv 64 P1v) = bv_unsigned (Z_to_bv 64 p1)) by congruence.
      rewrite !unsigned_lit in E by lia. lia. }
    subst p1.
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    rz_seg Hh Hl.
    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
    zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    rewrite <- FS.
    eapply (rz_fprintf_exit sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP RCSP HT HKG DI (DReadError (map bv_unsigned arg1)) _ s [(bufp, A, 65536)]);
      [| | exact BA2 | exact HK2 | exact FRM].
    - cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      unfold zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [unfold FmtFp.INT_MAX; lia|]. split; [right; lia| unfold GLOBALS_TOP; lia].
    - cbn [diag_pieces pieces_read_error]. unfold INTERNAL_BUFSIZ, WRITEV_MAX, zlength.
      repeat constructor; rewrite ?length_map, ?length_app; cbn [length str list_ascii_of_string map app]; lia.
  Qed.
End CDir.
