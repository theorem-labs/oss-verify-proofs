(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_model_block_glue.v, with its module paths and module names changed; 694 of its 807 lines of code are new or changed and 2299 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/ctrl_lay_block_gctx.v, with its module paths and module names changed; 225 of its 254 lines of code are new or changed and 778 lines of the source are left out. *)
(* ctrl_lay_block (0x86104), fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): region R3 of pb_ctrl_lay_block's glue,
   from the return of reac_box_model_block (pc 0x86370 = 549744, descriptor D3) to the class-1 flag store (pc 0x86440 =
   549952, descriptor D4).  rule 24: no function proved.

   PLAN OF RECORD: ctrl_lay_block-B-glue-plan.md section 3 (a working note, not in this delivery) (R2 box arm,
   R3).  lay_R3: lay_D3 (ctrl_lay_block_gD3.v) and a continuation over lay_D4 (ctrl_lay_block_gD4.v) give the walk from
   the box-return state.
     1. the run: ctrl_lay_block_cutsF.ly_box_k on m := B.MemNorm.normalize rsegs mem4 (its section memory, mc' := m),
        through EPI_C := ly_epi_c REAL STORE (REAL: the real-stack frame, dead in cgif form, post trivially true;
        STORE: the store state with ly_epi_side_pre's continuation facts, D3's lay_stores), with the Section CUTS facts
        of lay_cut_ctx at m and the post Qd sfr := sfr <> 0 -> lay_stores ... sfr; lifted by ctrl_lay_block_gbase's
        lay_SRr_norm at RNG := B.ProgBridge.RNG_W (w_H W4);
     2. the journal: lay_journal_lwf (write list lay_LWF S p fr1);
     3. D4 at the real store memory: the store state's registers, ly_store_tail's premises moved back through mem_rel,
        the output block carried from LC across the epilogue's three writes (all in the class-1 frame, its shadow and
        its flag byte, apart from the block by FP0's fp_dj), acall_kept across the LWF writes.
   The Section CUTS instantiation is by name (gsinst): the proof context names every Section variable / hypothesis
   the closed cut lemmas take as Section CUTS does.

   CLOSURE: the _F files are Required QUALIFIED; lib.Lib is named lib.Lib.X; every B module is named B.X in full. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YK04R YA0nR YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_ctrl_lay_block.
(* the _F closure and the bridges, QUALIFIED only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Img0 AsanRT MemNorm MemNormF MemNormTr ProgBridge
  ProgWorld.
(* the proved B ProgWorld statements this file reads, by their lemmas (a Theorem Labs lane) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldShadow ProgWorld_Fs ProgWorldTlsApart
  ProgWorldTlsOwned ProgWorldVisWin ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlBase asan_stack_malloc_c RcAsanFP
  asan_memcpy_cF_on ctrl_lay_block_c ctrl_lay_blockF_on ctrl_lay_block_cutsF ctrl_lay_block_gbase
  ctrl_lay_block_gD3 ctrl_lay_block_gctx ctrl_lay_block_gD4 ctrl_lay_block_gR4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rget := lib.Reusable.YK11.getr.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.

(* Instantiate the leading binders of a closed Section-CUTS lemma by the hypotheses / let-variables of the same name
   (ctrl_lay_block_cutsF.v's sinst, which stops at the first binder with no such name). *)
Ltac gsinst t :=
  lazymatch type of t with
  | forall (x : _), _ => first [ let v := constr:(x) in let t' := constr:(t v) in gsinst t' | exact t ]
  | _ => exact t
  end.

Section R3.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
(* core rules *)
Hypothesis LAWS : AR_laws SEGS B.
(* the bundle's symbols; the B ProgWorld statements are PROVED (a Theorem Labs lane), cited by their lemmas *)
Hypothesis CTS : lib.Reusable.YF0m.CtrlTSyms B.
Let ctl_stack_shadow_of_AR : B.ProgWorld.ctl_stack_shadow_of_AR_stmt B := B.ProgWorldShadow.ctl_stack_shadow_of_AR B.
Let ctl_fp_of_AR : B.ProgWorld.ctl_fp_of_AR_stmt B := B.ProgWorld_Fs.ctl_fp_of_AR B.
Let fp_tls_apart : B.ProgWorld.fp_tls_apart_stmt B := B.ProgWorldTlsApart.fp_tls_apart B.
Let fp_tls_owned : B.ProgWorld.fp_tls_owned_stmt B := B.ProgWorldTlsOwned.fp_tls_owned B.
Let win_sh_vis : B.ProgWorld.win_sh_vis_stmt B := B.ProgWorldVisWin.win_sh_vis B.
Let ctl_block_apart_fs : B.ProgWorld.ctl_block_apart_fs_stmt B := B.ProgWorldBlkApart.ctl_block_apart_fs B.
(* a Theorem Labs lane's footprint contract of __asan_memcpy in its route (C) _on form, applied inside the stretch (exactly its
   type; ly_box_k's copy arm) *)
Hypothesis MEMC : B.Prog.asan_memcpy_cF_on.asan_memcpy_contract_F_on.

(* The main lemma of region R3. *)
Lemma lay_R3 : forall RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k (regs : bvmap 5 word)
    (p f md g : Z) (fr tb mb nb gb : list byte) (pos : Z) ly4 S4 (W4 : world SEGS) (regs4 : bvmap 5 word)
    (mem4 : word -> option byte) (md4 : Model) (Q : world SEGS -> config -> Prop),
  B.Prog.ctrl_lay_block_gD3.lay_D3 (SK := SK) B RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p f md g
    fr tb mb nb gb pos ly4 S4 W4 regs4 mem4 md4 ->
  (forall ly3 S3 (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model),
     B.Prog.ctrl_lay_block_gD4.lay_D4 (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md g
       fr tb mb nb gb pos ly3 S3 W3 regs3 mem3 md3 ->
     SRr SEGS W3 (mkCfg (lib.Reusable.YK11.mkst regs3 (Z_to_bv 64 549952) mem3 (lib.Reusable.YK11.seg_rom SEGS)) md3)
       Q) ->
  SRr SEGS W4 (mkCfg (lib.Reusable.YK11.mkst regs4 (Z_to_bv 64 549744) mem4 (lib.Reusable.YK11.seg_rom SEGS)) md4) Q.
Proof.
  intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p f md g fr tb mb nb gb pos ly4 S4 W4 regs4 mem4
    md4 Q D3 KD4.
  destruct D3 as (HJ & Hwle & Hfrs & Hnin & Hab & HlyF & Hpos & HGT & Hwlo & Hwhi & Hret & Hgp & Htp & Hhome & Hf0 &
    Hf24 & Hawr & Hk39 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 &
    (r & E10 & Hr & Hr1 & Hr0) & Haro & (gj & HSV) & H120 & HA32 & Hpure & Hdata & HIR & HK).
  pose proof HJ as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & Hstk & _ & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & _).
  assert (EK : B.Prog.ctrl_lay_block_c.CTRL_LAY_BLOCK_K = 4512) by reflexivity.
  assert (ES : CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (rget regs 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  assert (HSz : spZ regs = bv_unsigned (rget regs 2)) by reflexivity.
  (* the real memory's read-only agreement (gbase lay_rt_facts) and the side stack's visibility *)
  destruct (B.Prog.ctrl_lay_block_gbase.lay_rt_facts B LAWS CTS
              RLO RHI ly4 S4 W4 mem4 md4 HAR4 (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Haro
                                                 (Z.le_refl _) (Z.le_refl _))) as (Hro4 & _ & _).
  pose proof (B.Prog.ctrl_lay_block_gctx.lay_F_vis B ly4 S4 W4 mem4 md4 HAR4) as HVF. rewrite HlyF in HVF.
  (* the Section CUTS facts at the normalized box-return memory *)
  pose proof (B.Prog.ctrl_lay_block_gctx.lay_cut_ctx B LAWS CTS
                RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly4 S4 W4 mem4 md4 k regs p f md g fr
                ly_zero tb mb nb gb pos HJ Hfrs Hab HlyF Hwlo Hwhi Htp Haro Hhome Hawr Hf0 Hf24 Hpure Hdata HIR) as CTX.
  destruct (B.Prog.ctrl_lay_block_gctx.lay_cut_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly4 S4 W4 mem4 md4
              k regs p pos HJ Hfrs Hab HlyF Hwlo Hwhi Hawr) as (HNI & Hceil4 & _).
  pose proof Hdata as (_ & _ & _ & _ & _ & _ & _ & HVB & _).
  (* the box-return configuration in ctrl's MS form *)
  change (lib.Reusable.YK11.mkst regs4 (Z_to_bv 64 549744) mem4 (lib.Reusable.YK11.seg_rom SEGS)) with
    (lib.Lib.MState.MS regs4 lib.Reusable.YK11.fp_regs (Z_to_bv 64 549744) lib.Reusable.YK11.fp_csr None mem4
       (lib.Lib.PropExec.seg_rom B.Img0.rsegs)).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv SEGS W4 (lib.Lib.Regs6ss.mkR_of regs4) regs4);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs4))].
  unfold lib.Lib.Regs6ss.mkR_of.
  assert (G2 : reg_get regs4 2 = Z_to_bv 64 ((bv_unsigned (rget regs 2) - 128) / 32 * 32)) by exact E2.
  assert (G3 : reg_get regs4 3 = rget regs 3) by exact E3.
  assert (G4 : reg_get regs4 4 = rget regs 4) by exact E4.
  assert (G8 : reg_get regs4 8 = rget regs 2) by exact E8.
  assert (G9 : reg_get regs4 9 = Z_to_bv 64 ((bv_unsigned (rget regs 2) - 128) / 32 * 32)) by exact E9.
  assert (G10 : reg_get regs4 10 = Z_to_bv 64 r) by exact E10.
  assert (G18 : reg_get regs4 18 = Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) by exact E18.
  assert (G19 : reg_get regs4 19 = Z_to_bv 64 g) by exact E19.
  assert (G20 : reg_get regs4 20 = Z_to_bv 64 f) by exact E20.
  assert (G21 : reg_get regs4 21 = Z_to_bv 64 (p + 18)) by exact E21.
  assert (G22 : reg_get regs4 22 = Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 32))
    by exact E22.
  assert (G23 : reg_get regs4 23 = Z_to_bv 64 md) by exact E23.
  assert (G24 : reg_get regs4 24 =
                Z_to_bv 64 (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)))
    by exact E24.
  assert (G25 : reg_get regs4 25 = Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) by exact E25.
  assert (G26 : reg_get regs4 26 = Z_to_bv 64 B.AsanRT.ASAN_K) by exact E26.
  assert (G27 : reg_get regs4 27 = rget regs 27) by exact E27.
  rewrite G2, G3, G4, G8, G9, G10, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27.
  clear G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27.
  (* Section CUTS's variables, by name *)
  set (ra := rget regs 1) in *. set (sp := rget regs 2) in *. set (gp := rget regs 3) in *.
  set (tp := rget regs 4) in *. set (s0 := rget regs 8) in *. set (s1 := rget regs 9) in *.
  set (s2 := rget regs 18) in *. set (s3 := rget regs 19) in *. set (s4 := rget regs 20) in *.
  set (s5 := rget regs 21) in *. set (s6 := rget regs 22) in *. set (s7 := rget regs 23) in *.
  set (s8 := rget regs 24) in *. set (s9 := rget regs 25) in *. set (s10 := rget regs 26) in *.
  set (s11 := rget regs 27) in *.
  set (F := lib.Reusable.YK11.fp_regs) in *. set (fc := lib.Reusable.YK11.fp_csr) in *.
  set (FS := ly_F lyc) in *. set (m := B.MemNorm.normalize B.Img0.rsegs mem4) in *.
  set (RNG := B.ProgBridge.RNG_W (w_H W4)) in *. set (ob := ly_zero) in CTX.
  set (fr1 := B.Prog.asan_stack_malloc_c.fs_frame FS 1 pos) in *.
  set (SP2 := (bv_unsigned sp - 128) / 32 * 32) in *.
  B.Prog.ctrl_lay_block_gD3.lay_ctx_names CTX.
  pose (Qd := fun (sfr : Z) (ms : machine_state) => sfr <> 0 ->
          B.Prog.ctrl_lay_block_gD3.lay_stores ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS
            fr tb mb nb gb sfr ms).
  (* the epilogue stage: REAL is dead (post trivially true), STORE hands the store state over *)
  pose proof (ltac:(gsinst B.Prog.ctrl_lay_block_cutsF.ly_epi_c)) as EPIc.
  assert (EPI := EPIc
    ltac:(intros; apply lib.Lib.ExecF.evtF_done; intros H00; exfalso; apply H00; reflexivity)
    ltac:(intros mc' gj' frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30
            x31 HFI Hsfr HLC HMf m0 fb H1 H2 H3 H4 H5 H6 H7 H8 H9;
          apply lib.Lib.ExecF.evtF_done; intros _;
          exists mc', gj', frb, spc, j, w120, m0, fb, xra, x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x19, x20, x21,
            x22, x23, x28, x29, x30, x31;
          exact (conj eq_refl (conj HFI (conj Hsfr (conj HLC (conj HMf (conj H1 (conj H2 (conj H3 (conj H4 (conj H5
                   (conj H6 (conj H7 (conj H8 H9))))))))))))))).
  clear EPIc.
  pose proof (ltac:(gsinst B.Prog.ctrl_lay_block_cutsF.ly_box_k)) as BOXK.
  (* ---- the side stack's geometry and FP0's apartness of the output block from the class-1 area ---- *)
  pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (FSpos & FSal & FSGT & FSApp & _) & _ & _ & _ & HFSlo & _ & _
    & HdD).
  assert (EfM1 : B.Prog.asan_stack_malloc_c.fs_M 1 = 8192) by reflexivity.
  assert (EFS : B.Prog.asan_stack_malloc_c.FS_SIZE = 11571200) by reflexivity.
  assert (EAK : B.AsanRT.ASAN_K = 2147450880) by reflexivity.
  assert (Efr : forall jj, B.Prog.asan_stack_malloc_c.fs_frame FS 1 jj = FS + 1085440 + jj * 128)
    by (intros jj; unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B; cbn; lia).
  assert (Efl : forall jj, B.Prog.asan_stack_malloc_c.fs_flag FS 1 jj = FS + 20480 + jj)
    by (intros jj; unfold B.Prog.asan_stack_malloc_c.fs_flag; cbn; lia).
  assert (Efr1 : fr1 = FS + 1085440 + pos * 128) by (unfold fr1; apply Efr).
  rewrite EfM1 in Hpos. rewrite EFS in HFSlo, FSApp. unfold B.Prog.asan_stack_malloc_c.ASAN_GT in FSGT.
  assert (DJB : forall a b, In (a, b) (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS) -> ly_dj (p + 18) (p + 50) a b).
  { intros a b Hin. unfold B.Prog.RcAsanFP.fp_dj, B.Prog.ctrl_lay_block_c.ctrl_lay_block_D in HdD.
    apply Forall_cons_iff in HdD as [_ HdD]. apply Forall_cons_iff in HdD as [Hp _].
    rewrite Forall_forall in Hp. exact (Hp (a, b) Hin). }
  assert (DJfr : ly_dj (p + 18) (p + 50) (B.Prog.asan_stack_malloc_c.fs_frame FS 1 0)
                   (B.Prog.asan_stack_malloc_c.fs_frame FS 1 (B.Prog.asan_stack_malloc_c.fs_M 1)))
    by (apply DJB; unfold B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1; cbn [flat_map app In];
        do 6 right; left; reflexivity).
  assert (DJfl : ly_dj (p + 18) (p + 50) (B.Prog.asan_stack_malloc_c.fs_flag FS 1 0)
                   (B.Prog.asan_stack_malloc_c.fs_flag FS 1 0 + B.Prog.asan_stack_malloc_c.fs_M 1))
    by (apply DJB; unfold B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1; cbn [flat_map app In];
        do 5 right; left; reflexivity).
  assert (DJsh : ly_dj (p + 18) (p + 50) (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame FS 1 0))
                   (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame FS 1 (B.Prog.asan_stack_malloc_c.fs_M 1))))
    by (apply DJB; unfold B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1; cbn [flat_map app In];
        do 7 right; left; reflexivity).
  rewrite EfM1, !Efr in DJfr. rewrite EfM1, !Efl in DJfl. rewrite EfM1, !Efr in DJsh.
  unfold ly_dj in DJfr, DJfl, DJsh.
  rewrite EK in HFSlo.
  (* ---- the stretch's premises at the normalized box-return memory ---- *)
  assert (HFI : B.Prog.ctrl_lay_blockF_on.FI sp tp p f md g FS fr mb nb m fr1 fr1 SP2 pos
                  (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag FS 1 pos))).
  { unfold B.Prog.ctrl_lay_blockF_on.FI. split; [right; rewrite EfM1; exact (conj Hpos (conj eq_refl (conj eq_refl
      (conj eq_refl eq_refl))))|].
    split; [intros _; apply B.MemNorm.bytes_at_normalize; [exact Hro4 | exact H120]|].
    split; [exact AC0|]. split; [exact SR0|]. split; [exact FP0|]. split; [exact TLS0|].
    intros x Hx _. pose proof AW0 as (A0 & A1 & A2 & A3). rewrite EK in A0, A1, A2, A3, Hx.
    split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i.
    specialize (A3 (x - (bv_unsigned sp - 4512)) ltac:(lia)).
    replace (bv_unsigned sp - 4512 + (x - (bv_unsigned sp - 4512))) with (x + 0) in A3 by lia. exact A3. }
  assert (HLC : B.Prog.ctrl_lay_blockF_on.LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr m gj ly_zero).
  { unfold B.Prog.ctrl_lay_blockF_on.LC. split.
    { apply B.MemNormTr.rw_cells_normalize; [exact Hro4 | | exact HSV].
      intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add B.Prog.ctrl_lay_blockF_on.SAVES] in Hi.
      apply B.MemNormTr.ro_addr_above_img. pose proof C1 as C1'. unfold B.Prog.ImgBounds.IMG_HI. lia. }
    split.
    { pose proof ST0 as (T0 & T1 & TH). split; [lia|]. split; [lia|]. intros a Ha. apply TH. rewrite EK in Ha |- *.
      lia. }
    split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|].
    split; [exact MI0|]. split; [exact BLK | exact FB]. }
  assert (HA32n : B.AsanRT.addressable m (fr1 + 32) 32)
    by exact (B.MemNormTr.addressable_normalize mem4 _ _ Hro4 HA32).
  assert (Hr1n : r = 1 -> lib.Lib.Mem.bytes_at B.Img0.rsegs m (fr1 + 32) (B.Prog.ctrl_lay_blockF_on.BASE md fr tb mb nb) /\
                 length (B.Prog.ctrl_lay_blockF_on.BASE md fr tb mb nb) = 32%nat).
  { intros E1. destruct (Hr1 E1) as (Hb & Hl). split; [apply B.MemNorm.bytes_at_normalize; assumption | exact Hl]. }
  assert (H0b : 0 <= fr1 + 32 < 2 ^ 64) by lia.
  assert (Happ : B.AsanRT.app_mem (fr1 + 64)) by (apply FSApp; lia).
  assert (Hdjp : fr1 + 64 <= p + 18 \/ p + 50 <= fr1 + 32) by lia.
  assert (Hdjw : fr1 + 64 <= bv_unsigned sp - B.Prog.ctrl_lay_block_c.CTRL_LAY_BLOCK_K \/ SP2 <= fr1 + 32)
    by (rewrite EK; left; lia).
  pose proof (BOXK EPI fr1 fr1 SP2 pos (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag FS 1 pos)) m gj r
                (reg_get regs4 1) (reg_get regs4 5) (reg_get regs4 6) (reg_get regs4 7) (reg_get regs4 11)
                (reg_get regs4 12) (reg_get regs4 13) (reg_get regs4 14) (reg_get regs4 15) (reg_get regs4 16)
                (reg_get regs4 17) (reg_get regs4 28) (reg_get regs4 29) (reg_get regs4 30) (reg_get regs4 31)
                HFI HLC HA32n Hr Hr1n Hr0 H0b Happ Hdjp Hdjw (lib.Lib.Frame.munch_refl _ m)) as RUN.
  clear BOXK EPI.
  (* ---- the lift ---- *)
  eapply (B.Prog.ctrl_lay_block_gbase.lay_SRr_norm B.Prog.ctrl_lay_block_gR4.lay_R4_wx W4 RNG md4 _ F
            (Z_to_bv 64 549744) fc mem4 _ Q (B.ProgBridge.fp_avoids_RNG_W _) Hro4 RUN).
  intros ms' model' Hrun (sE & HQ & HREL & HROS) Hhid Hsame.
  specialize (HQ ltac:(lia)).
  destruct HQ as (mc & gj' & frb & spc & j & w120 & m0 & fb & xra & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 &
    x17 & x19 & x20 & x21 & x22 & x23 & x28 & x29 & x30 & x31 & EsE & HFIc & Hsfr & HLCc & HMUc & HMU0 & HWM0 & HRM0 &
    HFC & HSf & HMI & HMUf & HSV0 & HDJ).
  subst sE.
  destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems' HMR].
  pose proof HFIc as ([(E0 & _) | (Hj & Efrb & Esfr & Espc & Ew)] & _); [exfalso; lia|].
  assert (Ej : j = pos) by (rewrite Efrb, Efr in Esfr; lia).
  subst j. rewrite <- Esfr in *. clear Efrb.
  (* the journal across the stretch *)
  assert (HJ3 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly4 S4 W4 (ms_mem ms') model' k).
  { lazymatch type of Hrun with lib.Reusable.YK04R.fsteps _ _ ?ms1 _ =>
      exact (B.Prog.ctrl_lay_block_gctx.lay_journal_lwf B LAWS B.Prog.ctrl_lay_block_gR4.lay_R4_wx
               STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly4 S4 W4 mem4 md4 k regs p pos ms1 ms' _
               model' RNG HJ Hab HlyF ltac:(rewrite EfM1; exact Hpos) Hwlo Hwhi Hawr Hro4 eq_refl Hrun
               (B.ProgBridge.fp_avoids_RNG_W _) HREL HROS HMUf Hsame) end. }
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  pose proof (B.MemNorm.munch_rel B.Img0.rsegs _ mem4 m (ms_mem ms') m0
                (B.MemNorm.mem_rel_normalize B.Img0.rsegs mem4 Hro4) HMR HROS HMUf) as HMUr.
  (* the output block at the store memory: LC's, across the epilogue's three writes in the class-1 area *)
  pose proof HLCc as (_ & _ & _ & _ & _ & HBLKc & _).
  assert (HBLK0 : lib.Lib.Step.rw_cells B.Img0.rsegs m0 (p + 18)
                    [lib.Lib.Cells.CB 32 (B.Prog.ctrl_lay_blockF_on.LAY md g fr tb mb nb gb)]).
  { apply (lib.Lib.Frame.rw_cells_transport B.Img0.rsegs _ mc m0 _ _ HBLKc HMU0 HWM0).
    cbn [lib.Lib.Frame.disjoint_from lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add Z.of_nat Pos.of_succ_nat].
    rewrite Efl. rewrite Efr1. unfold B.AsanRT.shadow_addr in DJsh |- *. rewrite EAK in DJsh |- *.
    split; [|split; [|split; [|exact I]]]; Z.div_mod_to_equations; lia. }
  (* ---- D4 at the store state ---- *)
  rewrite Ems'.
  change (lib.Lib.MState.MS ?R F (Z_to_bv 64 549952) fc None (ms_mem ms') (lib.Lib.PropExec.seg_rom B.Img0.rsegs))
    with (lib.Reusable.YK11.mkst R (Z_to_bv 64 549952) (ms_mem ms') (lib.Reusable.YK11.seg_rom SEGS)).
  apply (KD4 ly4 S4 W4 _ (ms_mem ms') model').
  unfold B.Prog.ctrl_lay_block_gD4.lay_D4.
  split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hab|]. split; [exact HlyF|].
  split; [rewrite EfM1; exact Hpos|]. split; [unfold B.Prog.asan_stack_malloc_c.ASAN_GT; exact HGT|].
  split; [exact Hhome|]. split; [exact Hwlo|]. split; [exact Hwhi|]. split; [exact Hret|].
  do 9 (split; [reflexivity|]).
  split; [exact (B.MemNorm.ro_agree_of_mem_rel B.Img0.rsegs _ _ HMR)|].
  split; [exists fb; exact (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR HFC)|].
  split; [exact (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR HSV0)|].
  split; [exact HDJ|].
  split; [exact (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR HBLK0)|].
  split; [exact HVB|]. split; [exact HVF|].
  eapply acall_kept_mono_E;
    [ exact (B.Prog.ctrl_lay_block_gctx.lay_kept_lwf B LAWS lyc Sc ly4 S4 W W4 memc mem4
               (ms_mem ms') md4 regs p pos (tctrl_lay_block_out p)
               HAR4 Hfrs Hab HlyF ltac:(rewrite EfM1; exact Hpos) Hceil4 Hhome HNI HK HMUr
               (fun a Ha => Hpres3 a ltac:(unfold CTRL_LAY_BLOCK_STK in Ha; lia)))
    | intros a [Ha | Ha]; exact Ha ].
Qed.

End R3.
