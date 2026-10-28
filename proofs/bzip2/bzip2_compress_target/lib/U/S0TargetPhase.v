(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatExec CatSim StoreOk Frame Hoare ShapeAlg Spec AgentLib RefMemcpyLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0StdioDefs U.S0ExitBase U.S0Exit U.S0Printf0 U.S0PrintfBufBase U.S0PrintfBuf.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocCover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0HarnStmt U.S0TRDefs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocIface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TRWalk U.S0TRInv U.S0TargetRun.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TargetPre.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0HarnStmt OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocIface.GlueEqv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRWalk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre.S0WorldVM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0World U.S0TargetPre U.S0SymPlanSoundA U.S0GrowStmt.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mem_inv_of_pristine : forall m, img_pristine m 0x10000 0x32000 -> mem_inv s0segs m.
Proof.
  intros m HP x b Hx. destruct (ro_addr s0segs x) eqn:E; [|reflexivity]. exfalso.
  pose proof (ro_addr_range x E) as R. pose proof (HP (bv_unsigned x) R) as N.
  unfold wa in N. rewrite Z_to_bv_bv_unsigned in N. congruence.
Qed.

(* [comment removed for export] *)
Lemma wr_at_img : forall m A (n : nat) bs,
  image_bytes s0segs A n = Some bs -> 0x32000 <= A -> A + Z.of_nat n <= 0x66000 -> wr_at s0segs m A (Z.of_nat n).
Proof.
  intros m A n bs HI H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (m (wa (A + i))) as [b|] eqn:E.
  - unfold wview. rewrite E. discriminate.
  - rewrite wview_rw_data_pristine; [| unfold rw_data; lia | exact E].
    replace (A + i) with (A + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (image_bytes_nth n A bs (Z.to_nat i) HI) by lia.
    destruct (nth_error bs (Z.to_nat i)) eqn:N; [discriminate|].
    apply nth_error_None in N. pose proof (image_bytes_length s0segs n A bs HI). lia.
Qed.

(* [comment removed for export] *)
Lemma wr_at_def : forall m A n,
  (forall a, A <= a < A + n -> m (wa a) <> None) -> 0x66000 <= A -> A + n <= 2 ^ 64 -> 0 <= n -> wr_at s0segs m A n.
Proof.
  intros m A n H H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite wview_off; [apply H; lia|]. unfold off_image. rewrite wa_unsigned by lia. lia.
Qed.

Lemma stk_of_stack_writableZ : forall M sp0,
  stack_writableZ M sp0 -> 0x7fff80000000 <= sp0 <= 0x800000000000 ->
  stk s0segs M (sp0 - 8388608) (sp0 - 128).
Proof.
  intros M sp0 SW Hsp.
  pose proof (SW 0 (Z.to_nat (8388608 - 128)) ltac:(lia) ltac:(lia)) as S. rewrite Z.add_0_r in S.
  pose proof (stk_of_store_ok_off M (sp0 - 8388608) (Z.to_nat (8388608 - 128)) ltac:(lia) ltac:(lia) ltac:(lia) S) as K.
  replace (sp0 - 8388608 + Z.of_nat (Z.to_nat (8388608 - 128))) with (sp0 - 128) in K by lia. exact K.
Qed.

Lemma img_clear_In : forall M lo hi,
  Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs -> In (lo, hi) img_clear_ivs -> img_pristine M lo hi.
Proof.
  intros M lo hi H HIn a Ha. pose proof (proj1 (Forall_forall _ _) H _ HIn) as C. cbn in C. apply C. exact Ha.
Qed.
End ACeilS1.


Ltac img_of W lo hi := apply (img_clear_In _ lo hi W); cbv; tauto.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma statics_of_world : forall M sp0 tid g,
  0x7fff80000000 <= sp0 <= 0x800000000000 ->
  stack_writableZ M sp0 -> main_frame sp0 M ->
  Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs ->
  cell M 0x44138 4 tid -> cell M 0x64450 8 g ->
  statics sp0 tid M.
Proof.
  intros M sp0 tid g Hsp SW MF W CT CC.
  pose proof (stk_of_stack_writableZ M sp0 SW Hsp) as ST0.
  assert (STF : stk s0segs M (sp0 - 8388608) (sp0 - 48)).
  { pose proof (SW 0 (Z.to_nat (8388608 - 48)) ltac:(lia) ltac:(lia)) as S. rewrite Z.add_0_r in S.
    pose proof (stk_of_store_ok_off M (sp0 - 8388608) (Z.to_nat (8388608 - 48)) ltac:(lia) ltac:(lia) ltac:(lia) S) as K.
    replace (sp0 - 8388608 + Z.of_nat (Z.to_nat (8388608 - 48))) with (sp0 - 48) in K by lia. exact K. }
  constructor.
  - intros a Ha. cbn [in_ivs S_IVS] in Ha.
    assert (P1 : img_pristine M 0x10000 0x34090) by img_of W 0x10000 0x34090.
    assert (P2 : img_pristine M 0x34091 0x340d9) by img_of W 0x34091 0x340d9.
    assert (P2' : img_pristine M 0x440d9 0x44110) by img_of W 0x440d9 0x44110.
    assert (P3 : img_pristine M 0x441f8 0x641e8) by img_of W 0x441f8 0x641e8.
    assert (P3' : img_pristine M 0x64220 0x64450) by img_of W 0x64220 0x64450.
    assert (P4 : img_pristine M 0x64471 0x64478) by img_of W 0x64471 0x64478.
    destruct Ha as [?|[?|[?|[?|[?|[?|[?|[?|[]]]]]]]]];
      first [apply P1; lia | apply P2; lia | apply P2'; lia | apply P3; lia | apply P3'; lia | apply P4; lia].
  - apply rw_cells_C4_of_rdn; [exact CT|]. change 4 with (Z.of_nat 4). eapply wr_at_img; [solve_img | lia | lia].
  - exists (Z_to_bv 64 g). apply rw_cells_C8_of_rdn; [exact CC|]. change 8 with (Z.of_nat 8). eapply wr_at_img; [solve_img | lia | lia].
  - (* [comment removed for export] *)
    assert (P5 : img_pristine M 0x64890 0x66000) by img_of W 0x64890 0x66000.
    unfold OFL.
    apply rw_cells_cons; [eapply rw_C4_pristine; [intros a Ha; apply P5; lia | lia | lia | solve_img | vm_compute; reflexivity] | cbn [csize]].
    replace (411792 + Z.of_nat 4) with 411796 by reflexivity.
    apply rw_cells_cons; [eapply rw_C4_pristine; [intros a Ha; apply P5; lia | lia | lia | solve_img | vm_compute; reflexivity] | cbn [csize]].
    replace (411796 + Z.of_nat 4) with 411800 by reflexivity.
    eapply rw_C8_pristine; [intros a Ha; apply P5; lia | lia | lia | solve_img | vm_compute; reflexivity].
  - destruct MF as [Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7]. unfold cell in *.
    assert (WR : forall A, sp0 - 128 <= A -> A + 8 <= sp0 - 48 -> wr_at s0segs M A 8).
    { intros A HA HB. eapply wr_at_of_stk; [exact STF | lia | lia | lia]. }
    (* [comment removed for export] *)
    destruct (stk_carve s0segs M (sp0 - 8388608) (sp0 - 120) 8 (proj1 (stk_split s0segs M (sp0 - 8388608) (sp0 - 120) (sp0 - 48) STF ltac:(lia))) ltac:(lia))
      as [_ [junk8 JK]].
    replace (sp0 - 120 - Z.of_nat 8) with (sp0 - 128) in JK by lia.
    exists junk8.
    repeat match goal with
    | |- rw_cells _ _ ?A (?c :: ?rest) =>
        lazymatch rest with
        | [] => idtac
        | _ => change (c :: rest) with ([c] ++ rest); apply rw_cells_app; cbn [cells_size csize Nat.add]
        end
    end.
    1: exact JK.
    all: try (apply rw_cells_C8_of_rdn; [| apply WR; lia]).
    all: unfold wa.
    + replace (sp0 - 128 + Z.of_nat 8) with (sp0 - 120) by lia. exact Ms7.
    + replace (sp0 - 128 + Z.of_nat 8 + Z.of_nat 8) with (sp0 - 112) by lia. exact Ms6.
    + replace (sp0 - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (sp0 - 104) by lia. exact Ms5.
    + replace (sp0 - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (sp0 - 96) by lia. exact Ms4.
    + replace (sp0 - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (sp0 - 88) by lia. exact Ms3.
    + replace (sp0 - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (sp0 - 80) by lia. exact Ms2.
    + replace (sp0 - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (sp0 - 72) by lia. exact Ms1.
    + replace (sp0 - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (sp0 - 64) by lia. exact Ms0.
    + replace (sp0 - 128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (sp0 - 56) by lia. exact Mra.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition target_phase_stmt : Prop :=
  forall (sp0 gm area brkv mas tid hw : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid hw content R M -> target_vm gm area VM ->
    target_vmx sp0 gm area brkv mas VM -> auxv0 sp0 M -> SPSA.std_model VM model ->
    realizes s0segs (mkCfg (mkst R (Z_to_bv 64 0x13850) M (seg_rom s0segs)) model) (t_target content (m_fs model)).

Section Phase.
  Context (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI).
  Hypothesis HARN : harn_spec AI AC S0I.
  Hypothesis PF0 : printf0_first_stmt PF0_S0.

  (* [comment removed for export] *)
  Definition entry_facts (bufA L sp0 : Z) (M : word -> option byte) (MD : Model) : Prop :=
    exists (s : ai_AS AI) (LB0 : list ablock) (pb : bid) (bufN B : Z),
      ai_inv AI s LB0 M MD /\ In (pb, bufA, bufN) LB0 /\ L <= bufN /\ ai_aux AI M B /\ sp0 <= B /\
      (forall n, 0 < n < 2 ^ 26 -> ai_sys_ok AI s LB0 n MD) /\
      ac_c21 AC C21_none s LB0 /\ (exists K0, ac_vm AC K0 s MD /\ (80 <= K0)%nat).

  (* [comment removed for export] *)
  Definition entry_facts_0 : Prop :=
    forall (sp0 gm area brkv mas tid hw : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (MD : Model),
      target_pre sp0 gm area brkv mas tid hw content R M -> target_vm gm area VM -> target_vmx sp0 gm area brkv mas VM ->
      auxv0 sp0 M -> atop_ok VM ->
      m_vmmaps MD = VM -> m_halted MD = None -> m_vm_lazy MD = [] -> m_vm_materialized MD = [] ->
      entry_facts (gm + 32) (Z.of_nat (length content)) sp0 M MD.

  (* [comment removed for export] *)

  Hypothesis HE0 : entry_facts_0.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma phase_common : forall (sp0 tid bufA gLo gN : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte) (MD : Model),
    let Lc := Z.of_nat (length content) in
    let cfglen := hdr_cfglen content in
    let paylen := hdr_paylen content in
    getr R 1 = Z_to_bv 64 0x136f4 -> getr R 2 = Z_to_bv 64 (sp0 - 128) -> getr R 4 = Z_to_bv 64 0x441e0 ->
    getr R 10 = Z_to_bv 64 (bufA + 2) -> getr R 11 = Z_to_bv 64 cfglen -> getr R 12 = Z_to_bv 64 (bufA + 6 + cfglen) ->
    getr R 13 = Z_to_bv 64 paylen -> getr R 9 = Z_to_bv 64 bufA -> getr R 18 = Z_to_bv 64 cfglen -> getr R 20 = Z_to_bv 64 paylen ->
    getr R 21 = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64) ->
    getr R 22 = Z_to_bv 64 0x340d9 ->                                   (* [comment removed for export] *)
    0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0 -> alloc_ceiling = sp0 - 8388608 -> 0 < tid < 2 ^ 22 ->
    6 + cfglen <= Lc -> Lc < 2 ^ 26 ->
    (* [comment removed for export] *)
    (forall i, 0 <= i < gN -> M (Z_to_bv 64 (gLo + i)) <> None) -> 0x66000 <= gLo -> gLo <= bufA -> bufA + Lc <= gLo + gN -> gLo + gN <= 2 ^ 64 ->
    rdn s0segs M (Z_to_bv 64 bufA) (length content) = Some content ->
    stack_writableZ M sp0 -> main_frame sp0 M ->
    Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs ->
    cell M 0x44138 4 tid -> (exists e, 0 <= e < 2 ^ 32 /\ cell M 0x4413c 4 e) -> cell M 0x64450 8 run_guard ->
    entry_facts bufA Lc sp0 M MD -> m_fds MD = SPSA.fds_std ->
    realizes s0segs (mkCfg (mkst R (Z_to_bv 64 0x13850) M (seg_rom s0segs)) MD) (t_target content (m_fs MD)).
  Proof.
    intros until MD. (intros Lc cfglen paylen R1 R2 R4 R10 R11 R12 R13 R9 R18 R20 R21 R22 SP0 ACV TID HL1 HL2 GD GLO GA GB GN CONT SW MF W CT [e [He CE]] CC; cps_intros (s & LB0 & pb & bufN & B & INV & BUFB & BUFN & AUX & HB & SYS & C21 & K0 & VM & K0LE); intros FDS).
    assert (P1 : img_pristine M 0x10000 0x34090) by img_of W 0x10000 0x34090.
    assert (P2 : img_pristine M 0x440d9 0x44110) by img_of W 0x440d9 0x44110.   (* [comment removed for export] *)
    eapply (run_cps AI AC HARN PF0 sp0 tid B bufA bufN content MD R M s LB0 pb (Z_to_bv 64 e) K0); try eassumption; try lia.
    all: lazymatch goal with
      | |- stk _ _ _ _ => apply stk_of_stack_writableZ; [exact SW | exact (proj1 SP0)]
      | |- mem_inv _ _ => apply mem_inv_of_pristine; intros a Ha; apply P1; lia
      | |- statics _ _ _ => eapply statics_of_world; try eassumption; exact (proj1 SP0)
      | |- stdout_untouched _ => intros a Ha; apply P1; unfold SO_FILE in Ha; lia
      | |- rw_cells _ _ _ [C1 _] => eapply rw_C1_pristine; [intros a Ha; apply P2; lia | lia | lia | solve_img | vm_compute; reflexivity]
      | |- rw_cells _ _ _ [CB _ _] =>
          split; [split; [cbn; split; [reflexivity| exact I] |]|];
          [ cbn [cells_bytes cbytes app]; rewrite app_nil_r; apply (bytes_at_of_rdn (length content)); [exact CONT | lia | lia]
          | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; apply wr_at_def; [| lia | lia | lia];
            intros a Ha; unfold wa; replace a with (gLo + (a - gLo)) by lia; apply GD; lia ]
      | |- rw_cells _ _ _ [C4 _] =>
          apply rw_cells_C4_of_rdn; [| change 4 with (Z.of_nat 4); eapply wr_at_img; [solve_img | unfold errno_cell, S0_layout; cbn [al_tp]; lia | unfold errno_cell, S0_layout; cbn [al_tp]; lia]];
          unfold cell in CE; unfold errno_cell, S0_layout; cbn [al_tp]; unfold wa; exact CE
      | |- fds_ok _ _ => unfold fds_ok; rewrite FDS; reflexivity
      | |- fds_ok _ => unfold fds_ok; rewrite FDS; reflexivity
      end.
  Qed.

  Theorem target_phase : target_phase_stmt.
  Proof.
    intros sp0 gm area brkv mas tid hw content R M VM model TP TV TX AX SM.
    destruct SM as [Sfds Svm Shalt Slazy Smat].
    pose proof (HE0 _ _ _ _ _ _ _ _ _ _ _ _ TP TV TX AX
                  (atop_of_vmx _ _ _ _ _ _ TX (tp_ceil _ _ _ _ _ _ _ _ _ _ TP) ltac:(pose proof (tp_sp0 _ _ _ _ _ _ _ _ _ _ TP); lia))
                  Svm Shalt Slazy Smat) as EF.
    destruct TP as [Rra Rsp Rgp Rtp Ra0 Ra1 Ra2 Ra3 Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Gsp Gceil Glen Mstack Mframe Wd Mcontent].
    pose proof (w_grp_def _ _ _ _ _ _ _ Wd) as GD. pose proof (w_gm_rng _ _ _ _ _ _ _ Wd) as GR.
    pose proof (w_tid _ _ _ _ _ _ _ Wd) as CT. pose proof (w_tidr _ _ _ _ _ _ _ Wd) as TR.
    pose proof (w_errno _ _ _ _ _ _ _ Wd) as CE. pose proof (w_canary _ _ _ _ _ _ _ Wd) as CC. pose proof (w_img _ _ _ _ _ _ _ Wd) as WI.
    eapply (phase_common sp0 tid (gm + 32) gm 69632 content R M model); try eassumption; try lia.
    - rewrite Ra0. f_equal. lia.
    - rewrite Ra2. f_equal. lia.
  Qed.

End Phase.

End ACeilS2.
