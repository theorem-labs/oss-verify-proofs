(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 582 of its 596 lines of code are new or changed and 234 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c_on.
Import ListNotations.
Open Scope Z_scope.

(* The footprint hook this file's stores use (Step's footprint_after_store), Local. lib/A/Prog/MemMono.v:207's copy
   is GLOBAL on this tree (a Theorem Labs lane's declared exception 3; a Theorem Labs lane's 8bac67328ab was not taken) and reaches this file
   through the Require Export above; this copy, defined after it, is the one in force here. Byte-for-byte
   MemMono.v:207-217's body. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* reac_box_model_block, image A (asan, entry 0x85b44): reac_box_model_block_holds (the contract of
   reac_box_model_block_c.v) from the contracts of __asan_stack_malloc_0, __asan_memset, __asan_memcpy and
   build_dt1_single. The plain proof (lib/Prog/reac_box_model_block.v) with the ASan frame of this build: the class-0
   frame request, the frame words and their shadow, the shadow check before each instrumented load and store (each
   passes from the addressable-range premises, so __asan_report_* is not reached), and the frame exit. *)

Section Main.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis HSM : asan_stack_malloc_0_contract.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).

  Lemma STW0 : forall a, bv_unsigned sp - 4272 <= a < bv_unsigned sp -> wview rsegs m (wa a) <> None.
  Proof. intros a Ha. exact (stk_wv m _ _ _ ST0 Ha). Qed.

  Lemma HA1 : A mod 32 = 0 /\ bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160.
  Proof. rewrite HA. Z.div_mod_to_equations. lia. Qed.

  Definition SAVES : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* The writes of the run outside o: the window, the class-0 hint word, flag j, the frame and its shadow. *)
  Definition Wf (fr j n : Z) : list ivl :=
    [(bv_unsigned sp - 4272, bv_unsigned sp); (FS, FS + 8); (fs_flag FS 0 j, fs_flag FS 0 j + n);
     (fr, fr + 64); (shadow_addr fr, shadow_addr fr + 8)].

  (* The frame: real (f = 0, fr = A - 64 = sp) or fake (fr = f, the class-0 frame j, sp = A, the flag-byte address
     w56 at fr + 56). *)
  Definition FK (fr f spc j n : Z) (w56 : word) : Prop :=
    (f = 0 /\ fr = A - 64 /\ spc = A - 64 /\ j = 0 /\ n = 0) \/
    (0 <= j < fs_M 0 /\ fr = fs_frame FS 0 j /\ f = fr /\ spc = A /\ w56 = Z_to_bv 64 (fs_flag FS 0 j) /\ n = 1).

  Definition BI (W : list ivl) (fr : Z) (w56 : word) (mc : word -> option byte) : Prop :=
    munch W m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (bv_unsigned sp + -104) SAVES /\
    (exists h, bytes_at rsegs mc FS (le8 h)) /\
    bytes_at rsegs mc (fr + 56) (le8 w56).

  Definition KB (Q : machine_state -> Prop) : Prop :=
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc ->
      evt rsegs Q (MS (mkR (Z_to_bv 64 0x85bbc) (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                         a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                         (Z_to_bv 64 b) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                         t3' t4' t5' t6') F (Z_to_bv 64 0x85c48) fc None mc (seg_rom rsegs)).

  Lemma app_range : forall X n, 0 < n -> (forall i, 0 <= i < n -> app_mem (X + i)) ->
    X + n <= 2147450880 \/ 17594333495296 <= X.
  Proof.
    intros X n Hn H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H (n - 1) ltac:(lia)) as H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H0, H1.
    destruct (Z.le_gt_cases (X + n) 2147450880) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases 17594333495296 X) as [G|G]; [right; exact G|].
    exfalso. pose proof (H (2147450880 - X) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H2. lia.
  Qed.

  (* What every frame gives: alignment, place, writable and AppMem bytes, writable shadow bytes. *)
  Lemma fk_facts : forall fr f spc j n w56, FK fr f spc j n w56 ->
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 64 -> app_mem (fr + i)) /\
    (fr + 64 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 8 -> wview rsegs m (wa (fr / 8 + off + i)) <> None) /\
    2147450880 <= fr / 8 + off /\ fr / 8 + off + 8 <= 17594333495296.
  Proof.
    intros fr f spc j n w56 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    assert (B : fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
                (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
                (forall i, 0 <= i < 64 -> app_mem (fr + i))).
    { destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
      - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. destruct AW0 as (_ & _ & _ & AW).
        pose proof (proj1 (AW (A - 64 + i - (bv_unsigned sp - 4272)) ltac:(lia))) as AP.
        replace (bv_unsigned sp - 4272 + (A - 64 + i - (bv_unsigned sp - 4272))) with (A - 64 + i) in AP by lia.
        exact AP.
      - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat] in *. change (2 ^ (14 - 0)) with 16384 in Hj.
        change (2 ^ 0) with 1 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range fr 64 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 8 -> fr / 8 + off + i = shadow_addr (fr + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. rewrite Hoff. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. rewrite B8 by exact Hi. apply (proj1 (SR0 _ (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - rewrite Hoff. unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  Ltac bi_intro H :=
    let MU := fresh "MU" in let WM := fresh "WM" in let RM := fresh "RM" in let MI := fresh "MI" in
    let SV := fresh "SV" in let HH := fresh "HH" in let hh := fresh "h" in let F56 := fresh "F56" in
    destruct H as (MU & WM & RM & MI & SV & (hh & HH) & F56).

  (* The byte x is writable in m: in the window (ST0), in the frame (FW) or a shadow byte of the frame (SW). *)
  Ltac wv_tac :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    first [ match goal with
            | STW : forall a, bv_unsigned sp - 4272 <= a < bv_unsigned sp -> wview rsegs m (wa a) <> None |- _ =>
                apply STW; lia
            end
          | apply STW0; lia
          | match goal with
            | FW : forall i, 0 <= i < 64 -> wview rsegs m (wa (?fr + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (fr + (x - fr)) by lia; apply FW; lia
            end
          | match goal with
            | SW : forall i, 0 <= i < 8 -> wview rsegs m (wa (?s + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (s + (x - s)) by lia; apply SW; lia
            end ].

  (* store_ok of n bytes at a in the current memory. *)
  Ltac wst a n :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) n = true)
          by (eapply wv_store_ok; [ wv_tac | eassumption | lia | lia ])
    end.

  (* +0xa8 .. +0x100: the frame words and the frame's shadow. *)
  Lemma fwords : forall fr f spc j n w56 mc (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Q,
    FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc -> KB Q ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x85bbc) (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                       a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                       (Z_to_bv 64 b) (Z_to_bv 64 fr) s8 (wa off) s10 s11
                       t3' t4' t5' t6') F (Z_to_bv 64 0x85bec) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Q HK HB K.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'. pose proof HP as (P1 & P2 & P3 & P4 & P5).
    unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    pose proof (app_range FS 8 ltac:(lia) ltac:(intros i Hi; apply P4; lia)) as FSA.
    pose proof HB as HB'. bi_intro HB'. unfold Wf, shadow_addr in MU.
    assert (Hspc : 0 <= spc < 2 ^ 64) by lia.
    assert (HS1 : store_ok rsegs mc (wa (A + 8)) 8 = true)
      by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia | exact WM | lia | lia]).
    step. store_done.
    do 8 step.
    wst fr 8%nat. step. store_done.
    wst (fr + 8) 8%nat. step. store_done.
    wst (fr + 16) 8%nat. step. store_done.
    step. step.
    rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
    wst (fr / 8 + off + 4) 1%nat. step. store_done.
    wst (fr / 8 + off + 5) 1%nat. step. store_done.
    wst (fr / 8 + off + 6) 1%nat. step. store_done.
    wst (fr / 8 + off + 7) 1%nat. step. store_done.
    step.
    wst (fr / 8 + off) 1%nat. step. store_done.
    wst (fr / 8 + off + 1) 1%nat. step. store_done.
    wst (fr / 8 + off + 2) 1%nat. step. store_done.
    wst (fr / 8 + off + 3) 1%nat. step. store_done.
    eapply K; [exact HK|].
    split; [unfold Wf, shadow_addr; exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [eexists; eassumption | assumption].
  Qed.

  Lemma entry : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m -> KB Q ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 K.
    pose proof FP0 as FPm. unfold reac_box_model_block_W in FPm. pose proof STW0 as STW.
    unfold REAC_BOX_MODEL_BLOCK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (MU : munch [(bv_unsigned sp - 4272, bv_unsigned sp)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    rewrite <- Hoff in CK.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (bv_unsigned sp - 160) _ ST0c ltac:(lia)) as [STa STb].
    clear ST0c.
    carve_frame 104%nat STb.
    step.
    assert (HS0 : store_ok rsegs m0 (wa (bv_unsigned sp + -160)) 8 = true).
    { eapply wv_store_ok; [ | apply wmono_refl | lia | lia]. intros i Hi.
      apply (stk_wv m0 (bv_unsigned sp - 160) (bv_unsigned sp + -104)); [exact STb | lia]. }
    step. store_done.
    do 13 step.
    step. step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; rewrite HA; f_equal; f_equal; lia).
    rewrite EA.
    do 11 step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* the side-stack state at m1 *)
    pose proof (fl_fp [0%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0. destruct HCL0 as [(_ & h & flags & HH & HF & HFl & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STa STb ltac:(lia)) as STc.
    destruct (stk_split rsegs m1 _ A _ STc ltac:(lia)) as [STA _].
    pose proof HSM as HM. unfold asan_stack_malloc_0_contract, asan_stack_malloc_contract in HM. cbv zeta in HM.
    eapply evt_cut.
    { eapply HM with (lo := bv_unsigned sp - 4272) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit A) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC0 MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (shadow_rw_mono m m1 SR0 WM RM).
      - exact MI.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HF.
      - exact HFl.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 547772)) with (Z_to_bv 64 547772) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit A) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2. rewrite Z.add_0_r in HH2.
    pose proof FPm as (DT' & TS' & C' & T' & DB' & k' & _ & _ & HPm & _).
    pose proof HPm as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [A - 64, A) *)
      subst x0. rewrite (unsigned_lit A) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      rewrite Z.add_0_r in MU2.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf (A - 64) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      destruct (rd8_le8 m2 (A - 8) ltac:(lia) ltac:(lia) ltac:(intros y Hy; apply (rd_of_stk _ _ _ ST2); lia))
        as (w56 & F56).
      clear MU MU2 WM WM2 RM RM2 FR STA STa STb STc MI.
      unfold Wf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (A - 64)
          by (rewrite ?(unsigned_lit A), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step. step.
      rewrite (unsigned_lit A) by lia.
      wst (A - 4096) 8%nat. step. store_done.
      step.
      rewrite (rc_lts_signed (A - 64) (A - 4096)) by lia.
      replace (A - 64 <? A - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      eapply (fwords (A - 64) 0 (A - 64) 0 0 w56); [left; repeat split; lia | | exact K].
      split; [unfold Wf, shadow_addr; exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
      replace (A - 64 + 56) with (A - 8) by lia. assumption.
    - (* the side-stack frame fs_frame FS 0 jj *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit A), (unsigned_lit 64) in FRM by lia.
      replace (fs_B 0) with 64 in FRM by reflexivity.
      replace (fs_shadow_n 0 64) with 8 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFL & H24 & H56 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 0) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 0) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 0 jj) as fr eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2. rewrite Z.add_0_r in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EFl : fs_flag FS 0 jj = FS + 4096 + jj) by (unfold fs_flag; cbn; lia).
      assert (EM0 : fs_M 0 = 16384) by reflexivity.
      rewrite EM0 in Hjj.
      assert (SHb : shadow_addr fr + 8 <= bv_unsigned sp - 4272)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HFL). cbn. lia.
        - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ H56). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf fr jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(rewrite EFl; cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR STA STa STb STc MI.
      step. step. step. step.
      rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
      eapply (fwords fr fr A jj 1 (Z_to_bv 64 (fs_flag FS 0 jj))); [right; repeat split; lia | | exact K].
      split; [exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
      replace (fr + 56) with (fr + 64 - 8) by lia. assumption.
  Qed.

  (* ---- Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; form of a Theorem Labs lane 09:38Z, ruling 09:58Z): the section premise SR0 narrowed.
     fk_facts, fwords and entry above stay byte-identical; fk_facts_on, fwords_on and entry_on are NEW, with the
     section premises SR0_on (in place of SR0) and HSM_on (__asan_stack_malloc_0's _on contract, a Theorem Labs lane's
     STATEMENT asan_stack_malloc_c_on.v, cited only as this Section Hypothesis, as HSM is).  Both new hypotheses come
     after entry, so no old proof can see them.
     SR0_shadow_R is the set of shadow bytes these runs need present through the premise, the bytes they read or store:
       - the 8 shadow bytes [shadow_addr fr, shadow_addr fr + 8) of the 64-byte frame, read and stored by fwords
         (the frame's shadow words at +0xa8 .. +0x100, wv_tac's SW case, from fk_facts' last conjuncts): for the
         real-stack frame fr = A - 64 they are [shadow_addr (A - 64), shadow_addr (A - 64) + 8); for the side-stack
         frame fr = fs_frame FS 0 j they lie in the class-0 block's shadow;
       - __asan_stack_malloc_0's region at its call, asan_stack_malloc_shadow_R FS 0 (the class-0 block's shadow), carried
         from m to the call's memory m1 by ShadowRwOnT.shadow_rw_on_mem_mono (wmono + rd_mono, as MemMono's
         shadow_rw_mono carries SR0).
     No other shadow byte is read or stored by these runs. *)
  Hypothesis HSM_on : asan_stack_malloc_0_contract_on.
  Definition SR0_shadow_R (a : Z) : Prop :=
    shadow_addr (A - 64) <= a < shadow_addr (A - 64) + 8 \/ asan_stack_malloc_shadow_R FS 0%nat a.
  Hypothesis SR0_on : shadow_rw_on SR0_shadow_R m.

  Lemma fk_facts_on : forall fr f spc j n w56, FK fr f spc j n w56 ->
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 64 -> app_mem (fr + i)) /\
    (fr + 64 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 8 -> wview rsegs m (wa (fr / 8 + off + i)) <> None) /\
    2147450880 <= fr / 8 + off /\ fr / 8 + off + 8 <= 17594333495296.
  Proof.
    intros fr f spc j n w56 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    assert (B : fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
                (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
                (forall i, 0 <= i < 64 -> app_mem (fr + i))).
    { destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
      - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. destruct AW0 as (_ & _ & _ & AW).
        pose proof (proj1 (AW (A - 64 + i - (bv_unsigned sp - 4272)) ltac:(lia))) as AP.
        replace (bv_unsigned sp - 4272 + (A - 64 + i - (bv_unsigned sp - 4272))) with (A - 64 + i) in AP by lia.
        exact AP.
      - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat] in *. change (2 ^ (14 - 0)) with 16384 in Hj.
        change (2 ^ 0) with 1 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range fr 64 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 8 -> fr / 8 + off + i = shadow_addr (fr + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. rewrite Hoff. lia. }
    assert (HRs : forall i, 0 <= i < 8 -> SR0_shadow_R (shadow_addr (fr + 8 * i))).
    { intros i Hi. unfold SR0_shadow_R, asan_stack_malloc_shadow_R, shadow_addr.
      destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
      - left. Z.div_mod_to_equations. lia.
      - right. unfold fs_frame, fs_M, fs_B, FS_SIZE in *. cbn [Z.of_nat] in *.
        change (2 ^ (14 - 0)) with 16384 in Hj. change (2 ^ 0) with 1 in *. Z.div_mod_to_equations. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. rewrite B8 by exact Hi. apply (proj1 (SR0_on _ (HRs i Hi) (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - rewrite Hoff. unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  Lemma fwords_on : forall fr f spc j n w56 mc (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Q,
    FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc -> KB Q ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x85bbc) (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                       a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                       (Z_to_bv 64 b) (Z_to_bv 64 fr) s8 (wa off) s10 s11
                       t3' t4' t5' t6') F (Z_to_bv 64 0x85bec) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Q HK HB K.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts_on fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'. pose proof HP as (P1 & P2 & P3 & P4 & P5).
    unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    pose proof (app_range FS 8 ltac:(lia) ltac:(intros i Hi; apply P4; lia)) as FSA.
    pose proof HB as HB'. bi_intro HB'. unfold Wf, shadow_addr in MU.
    assert (Hspc : 0 <= spc < 2 ^ 64) by lia.
    assert (HS1 : store_ok rsegs mc (wa (A + 8)) 8 = true)
      by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia | exact WM | lia | lia]).
    step. store_done.
    do 8 step.
    wst fr 8%nat. step. store_done.
    wst (fr + 8) 8%nat. step. store_done.
    wst (fr + 16) 8%nat. step. store_done.
    step. step.
    rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
    wst (fr / 8 + off + 4) 1%nat. step. store_done.
    wst (fr / 8 + off + 5) 1%nat. step. store_done.
    wst (fr / 8 + off + 6) 1%nat. step. store_done.
    wst (fr / 8 + off + 7) 1%nat. step. store_done.
    step.
    wst (fr / 8 + off) 1%nat. step. store_done.
    wst (fr / 8 + off + 1) 1%nat. step. store_done.
    wst (fr / 8 + off + 2) 1%nat. step. store_done.
    wst (fr / 8 + off + 3) 1%nat. step. store_done.
    eapply K; [exact HK|].
    split; [unfold Wf, shadow_addr; exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [eexists; eassumption | assumption].
  Qed.

  Lemma entry_on : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m -> KB Q ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 K.
    pose proof FP0 as FPm. unfold reac_box_model_block_W in FPm. pose proof STW0 as STW.
    unfold REAC_BOX_MODEL_BLOCK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (MU : munch [(bv_unsigned sp - 4272, bv_unsigned sp)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    rewrite <- Hoff in CK.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (bv_unsigned sp - 160) _ ST0c ltac:(lia)) as [STa STb].
    clear ST0c.
    carve_frame 104%nat STb.
    step.
    assert (HS0 : store_ok rsegs m0 (wa (bv_unsigned sp + -160)) 8 = true).
    { eapply wv_store_ok; [ | apply wmono_refl | lia | lia]. intros i Hi.
      apply (stk_wv m0 (bv_unsigned sp - 160) (bv_unsigned sp + -104)); [exact STb | lia]. }
    step. store_done.
    do 13 step.
    step. step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; rewrite HA; f_equal; f_equal; lia).
    rewrite EA.
    do 11 step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* the side-stack state at m1 *)
    pose proof (fl_fp [0%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0. destruct HCL0 as [(_ & h & flags & HH & HF & HFl & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STa STb ltac:(lia)) as STc.
    destruct (stk_split rsegs m1 _ A _ STc ltac:(lia)) as [STA _].
    pose proof HSM_on as HM. unfold asan_stack_malloc_0_contract_on, asan_stack_malloc_contract_on in HM. cbv zeta in HM.
    eapply evt_cut.
    { eapply HM with (lo := bv_unsigned sp - 4272) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit A) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC0 MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (A.ShadowRwOnT.shadow_rw_on_mem_mono _ m m1
               (shadow_rw_on_mono SR0_shadow_R (asan_stack_malloc_shadow_R FS 0%nat) m (fun a Ha => or_intror Ha) SR0_on)
               WM RM).
      - exact MI.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HF.
      - exact HFl.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 547772)) with (Z_to_bv 64 547772) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit A) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2. rewrite Z.add_0_r in HH2.
    pose proof FPm as (DT' & TS' & C' & T' & DB' & k' & _ & _ & HPm & _).
    pose proof HPm as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [A - 64, A) *)
      subst x0. rewrite (unsigned_lit A) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      rewrite Z.add_0_r in MU2.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf (A - 64) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      destruct (rd8_le8 m2 (A - 8) ltac:(lia) ltac:(lia) ltac:(intros y Hy; apply (rd_of_stk _ _ _ ST2); lia))
        as (w56 & F56).
      clear MU MU2 WM WM2 RM RM2 FR STA STa STb STc MI.
      unfold Wf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (A - 64)
          by (rewrite ?(unsigned_lit A), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step. step.
      rewrite (unsigned_lit A) by lia.
      wst (A - 4096) 8%nat. step. store_done.
      step.
      rewrite (rc_lts_signed (A - 64) (A - 4096)) by lia.
      replace (A - 64 <? A - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      eapply (fwords_on (A - 64) 0 (A - 64) 0 0 w56); [left; repeat split; lia | | exact K].
      split; [unfold Wf, shadow_addr; exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
      replace (A - 64 + 56) with (A - 8) by lia. assumption.
    - (* the side-stack frame fs_frame FS 0 jj *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit A), (unsigned_lit 64) in FRM by lia.
      replace (fs_B 0) with 64 in FRM by reflexivity.
      replace (fs_shadow_n 0 64) with 8 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFL & H24 & H56 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 0) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 0) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 0 jj) as fr eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2. rewrite Z.add_0_r in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EFl : fs_flag FS 0 jj = FS + 4096 + jj) by (unfold fs_flag; cbn; lia).
      assert (EM0 : fs_M 0 = 16384) by reflexivity.
      rewrite EM0 in Hjj.
      assert (SHb : shadow_addr fr + 8 <= bv_unsigned sp - 4272)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HFL). cbn. lia.
        - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ H56). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf fr jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(rewrite EFl; cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR STA STa STb STc MI.
      step. step. step. step.
      rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
      eapply (fwords_on fr fr A jj 1 (Z_to_bv 64 (fs_flag FS 0 jj))); [right; repeat split; lia | | exact K].
      split; [exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
      replace (fr + 56) with (fr + 64 - 8) by lia. assumption.
  Qed.
End Main.

Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block.fk_facts_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block.fk_facts_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block.fwords_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block.fwords_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block.entry_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block.entry_on.
