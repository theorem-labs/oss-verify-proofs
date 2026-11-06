(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_8a5a8_8a63c.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8a5c0 : bv 32 := @BV 32 0x0007c597%Z I.
Lemma F_8a5c0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8a5c0%Z I : word) = Some W_8a5c0.
Proof. vm_refl. Qed.
Lemma D_8a5c0 : decode_any W_8a5c0 = Some (Auipc (@BV 5 11%Z I) (@BV 20 124%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a5c4 : bv 32 := @BV 32 0x9385b903%Z I.
Lemma F_8a5c4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x8a5c4%Z I : word) = Some W_8a5c4.
Proof. vm_refl. Qed.
Lemma D_8a5c4 : decode_any W_8a5c4 = Some (Load SZ8 true (@BV 5 18%Z I) (@BV 5 11%Z I) (@BV 12 2360%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_8a5a8_8a63c.
Module Bo_code_811d0_811fc.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- @eq (option (bv 32)) (fetch_word ?s ?a) ?r =>
      apply (@bool_decide_eq_true_1 _ (@decide_rel (option (bv 32)) (option (bv 32)) (@eq (option (bv 32))) (@option_eq_dec (bv 32) (bv_eq_dec 32)) (fetch_word s a) r));
      vm_cast_no_check (@eq_refl bool true)
  | |- @eq (option (prod instr Z)) (decode_any ?w) ?r =>
      (* [comment removed for export] *)
      apply (@InstrEnc.enc_opt_inj (decode_any w) r);
      vm_cast_no_check (@eq_refl (list Z) (InstrEnc.enc_opt r))
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_811d0 : bv 32 := @BV 32 0x00085697%Z I.
Lemma F_811d0 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811d0%Z I : word) = Some W_811d0.
Proof. vm_refl. Qed.
Lemma D_811d0 : decode_any W_811d0 = Some (Auipc (@BV 5 13%Z I) (@BV 20 133%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811d4 : bv 32 := @BV 32 0xd886b683%Z I.
Lemma F_811d4 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x811d4%Z I : word) = Some W_811d4.
Proof. vm_refl. Qed.
Lemma D_811d4 : decode_any W_811d4 = Some (Load SZ8 true (@BV 5 13%Z I) (@BV 5 13%Z I) (@BV 12 3464%Z I), 4%Z).
Proof. vm_refl. Qed.
End Bo_code_811d0_811fc.
Require Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtFlushI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtXStrlenI.AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_flush_tab : flush_tab :=
  {| ft_base := 0x6dff8; ft_mt := asan_m2s_tab_6e03c; ft_g_pgsz := 0xff250; ft_p_pgsz := 0x197020; ft_g_seal := 0xff2b0; ft_sv := 1 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_flush_tab_ok : flush_tab_ok ASEGS asan_flush_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold flush_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ft_base ft_mt ft_g_pgsz ft_p_pgsz ft_g_seal ft_sv asan_flush_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold flush_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold rel_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold imadv_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_m2s_tab_ok_6e03c.
  - apply bv_eq. vm_compute. reflexivity.
  - gload_tac F_89b48 D_89b48 F_89b4c D_89b4c.
  - gload_tac F_80758 D_80758 F_8075c D_8075c.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma asan_flush_cells : flush_cells asan_flush_tab = ltac:(let x := eval cbv in (flush_cells asan_flush_tab) in exact x).
Proof using. reflexivity. Qed.
End FPGen1.
End AsRtFlushI.
Require Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtFlushK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.

Lemma fk_munrestrict_same : forall (Hd : word -> bool) (M M' : word -> option byte),
  (forall a, Hd a = true -> M' a = M a) -> munrestrict Hd M (mrestrict Hd M') = M'.
Proof using.
  intros Hd M M' E. apply functional_extensionality. intros a. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict, mrestrict in G in change_no_check G' end).
  destruct (Hd a) eqn:Ha; [symmetry; apply E; exact Ha | reflexivity].
Qed.
Lemma fk_unrestrict_mkst : forall (Hd : word -> bool) (M : word -> option byte) regs pc m rom,
  unrestrict Hd M (mkst regs pc m rom) = mkst regs pc (munrestrict Hd M m) rom.
Proof using. intros. reflexivity. Qed.
Lemma fk_restrict_mkst : forall (Hd : word -> bool) regs pc m rom,
  restrict Hd (mkst regs pc m rom) = mkst regs pc (mrestrict Hd m) rom.
Proof using. intros. reflexivity. Qed.
Lemma fk_pru_id : forall z, 0 <= z -> z mod 4096 = 0 -> page_round_up_Z z = z.
Proof using. intros z Hz Hm. apply page_round_up_Z_aligned; [exact Hz|]. (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end). exact Hm. Qed.

Section FLK.
  Variable segs : list Segment.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments segs Hd.
  Hypothesis WX : wx_segs_nowrap segs.
  Variable t : flush_tab.
  Hypothesis TOK : flush_tab_ok segs t.


  Theorem flush_katD2 :
    forall (Hd' : word -> bool) (HOFF' : H_off_segments segs Hd') (A A' : list (Z * Z)) regs (mem rom : word -> option byte) (model : Model)
           (p size ra sp midend : word) (Q : config -> Prop),
    let pb := fl_pb p in let pe := fl_pe p size in
    let MF := fl_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) in
    flushH segs t mem p size sp midend -> ret_ok ra ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = p -> getr regs 11 = size ->
    (* [comment removed for export] *)
    Forall (fun c => hid_off Hd c 8) (flush_cells t) -> hid_off Hd (U sp - 32) 32 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (pb < pe -> forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        madvise_dontneed_ok (m_vmmaps mdlm) (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb)) = true) ->
    (* [comment removed for export] *)
    A_wf A' -> lazy_cover Hd' (m_vm_lazy model) A' ->
    (pb < pe -> forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        MInv A' (madvise_dontneed_next mdlm (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb)))) ->
    (* [comment removed for export] *)
    (pb < pe -> forall (r' : bvmap 5 word) mdlm mdl4,
        same_but_materialized model mdlm -> MInv A mdlm ->
        same_but_materialized (madvise_dontneed_next mdlm (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb))) mdl4 -> MInv A' mdl4 ->
        getr r' 1 = ra -> getr r' 2 = sp -> getr r' 10 = Z_to_bv 64 0 ->
        regs_agree (fun x => In x m2s_clob) regs r' ->
        katD segs (mkCfg (mkst r' ra (zfill (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb)) MF) rom) mdl4) Q) ->
    (* [comment removed for export] *)
    (pe <= pb -> forall (r' : bvmap 5 word) mdlm,
        same_but_materialized model mdlm -> MInv A mdlm ->
        getr r' 1 = ra -> getr r' 2 = sp ->
        regs_agree (fun x => In x m2s_clob) regs r' ->
        katD segs (mkCfg (mkst r' ra MF rom) mdlm) Q) ->
    katD segs (mkCfg (mkst regs (ft_base t) mem rom) model) Q.
  Proof using TOK WX HOFFSEG.
    intros Hd' HOFF' A A' regs mem rom model p size ra sp midend Q pb pe MF PRE Hret R1 R2 R10 R11 HCELLS HSCR HALT LC AWF MI GATE AWF' LC' REL CONT CONT0.
    pose proof (u64_range sp) as Hspr.
    pose proof PRE as [P1 P2 P3 P4 P5 P6 P7 P8].
    pose proof (fl_geom_t p size P2) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10). fold pb pe in G4, G5, G6, G7, G8, G9, G10.
    pose proof (flushH_mrestrict segs t Hd mem p size sp midend PRE HCELLS HSCR) as PRE'.
    assert (MFhid : forall a : word, Hd a = true -> MF a = mem a).
    { intros a Ha. destruct (decide (MF a = mem a)) as [E|N]; [exact E|]. exfalso.
      destruct (fl_frame_mod mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) a P7 N) as [X _].
      rewrite (HSCR a) in Ha by lia. discriminate Ha. }
    destruct (Z_lt_le_dec pb pe) as [HLT | HGE].
    - (* [comment removed for export] *)
      destruct (flush_pre_t segs t TOK (mrestrict Hd mem) rom ra sp p size midend regs PRE' R1 R2 R10 R11 HLT)
        as (r1 & RUN1 & B17 & B10 & B11 & B12 & B1 & B2 & AG1).
      rewrite (fl_frame_mrestrict Hd mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) P7 HSCR) in RUN1. fold MF in RUN1.
      apply (katD_msteps_acct segs Hd HOFFSEG WX A (mkst regs (ft_base t) mem rom)
               (mkst r1 (at_ (ft_base t) 75656) (mrestrict Hd MF) rom) model Q LC AWF MI HALT).
      { rewrite fk_restrict_mkst. exact RUN1. }
      intros mdlm MIm SBMm HC1. rewrite fk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst regs (ft_base t) mem rom)) with mem by reflexivity.
      rewrite (fk_munrestrict_same Hd mem MF MFhid).
      pose proof (same_but_materialized_frame model mdlm SBMm) as FRm.
      assert (HALTm : m_halted mdlm = None) by (destruct FRm as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_); rewrite Hh; exact HALT).
      assert (LZm : m_vm_lazy mdlm = m_vm_lazy model) by (destruct FRm as (_&_&Hl&_); exact Hl).
      (* [comment removed for export] *)
      apply (katD_ecall segs r1 (at_ (ft_base t) 75656) MF rom mdlm W_80778 Q HALTm (flush_ecall_fetch_t segs t TOK) E_80778).
      rewrite B17.
      (* [comment removed for export] *)
      assert (Upb : U (Z_to_bv 64 pb) = pb) by (rewrite u_Z2bv; lia).
      assert (Un : U (Z_to_bv 64 (pe - pb)) = pe - pb) by (rewrite u_Z2bv; lia).
      assert (PRUZ : page_round_up_Z (pe - pb) = pe - pb) by (apply fk_pru_id; [lia | rewrite Zminus_mod, G8, G9; reflexivity]).
      set (ms := epend r1 (at_ (ft_base t) 75656) MF rom (Z_to_bv 64 233)).
      assert (E0 : ms_gpr ms 0 = Z_to_bv 64 pb) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend0; exact B10).
      assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (pe - pb)) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend1; exact B11).
      assert (E2 : ms_gpr ms 2 = Z_to_bv 64 4) by ((lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end); rewrite AsKSys6.MhKSys.ms_gpr_epend2; exact B12).
      assert (RU : MmapSim.page_round_up (ms_gpr ms 1) = Z_to_bv 64 (pe - pb)).
      { (lazymatch goal with |- ?G => let G' := eval unfold MmapSim.page_round_up in G in change_no_check G' end). rewrite E1, Un, PRUZ. reflexivity. }
      apply (katD_madvise segs ms mdlm (Z_to_bv 64 233) Q HALTm eq_refl).
      { rewrite u_Z2bv by lia. reflexivity. }
      { (lazymatch goal with |- ?G => let G' := eval unfold madvise_args_ok in G in change_no_check G' end). rewrite RU, E0, E1, E2, Upb, Un, PRUZ.
        split. { (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end). exact G8. }
        split. { reflexivity. }
        split. { intros X. apply (f_equal bv_unsigned) in X. rewrite Un in X. rewrite u_Z2bv in X by lia. lia. }
        split. { (lazymatch goal with |- ?G => let G' := eval unfold two_pow_64 in G in change_no_check G' end). lia. }
        exact (GATE HLT mdlm SBMm MIm). }
      (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold madvise_eff, madvise_model in G in change_no_check G' end). rewrite RU, E0. (lazymatch goal with |- ?G => let G' := eval unfold ms in G in change_no_check G' end).
      rewrite AsKSys6.MhKSys.adv_zerosr_epend. rewrite at_addi. zlit_at.
      set (mdl2 := madvise_dontneed_next mdlm (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb))).
      set (MZ := zfill (Z_to_bv 64 pb) (Z_to_bv 64 (pe - pb)) MF).
      assert (EM2 : mdl2 = madvise_model ms mdlm) by ((lazymatch goal with |- ?G => let G' := eval unfold mdl2, madvise_model in G in change_no_check G' end); rewrite RU, E0; reflexivity).
      assert (MI2 : MInv A' mdl2) by exact (REL HLT mdlm SBMm MIm).
      assert (HALT2 : m_halted mdl2 = None) by (rewrite EM2, madvise_model_halted; exact HALTm).
      assert (LC2 : lazy_cover Hd' (m_vm_lazy mdl2) A') by (rewrite EM2, madvise_model_lazy, LZm; exact LC').
      (* [comment removed for export] *)
      assert (Q1 : getr (regupd r1 10 (Z_to_bv 64 0)) 1 = ra) by (rewrite getr_other by (intros E; discriminate E); exact B1).
      assert (Q10 : getr (regupd r1 10 (Z_to_bv 64 0)) 10 = Z_to_bv 64 0) by (rewrite getr_same by (intros E; discriminate E); reflexivity).
      destruct (flush_post_t segs t TOK (mrestrict Hd' MZ) rom ra (regupd r1 10 (Z_to_bv 64 0)) Hret Q1 Q10) as (r2 & RUN2 & C10 & AG2).
      apply (katD_msteps_acct segs Hd' HOFF' WX A' (mkst (regupd r1 10 (Z_to_bv 64 0)) (at_ (ft_base t) 75660) MZ rom)
               (mkst r2 ra (mrestrict Hd' MZ) rom) mdl2 Q LC2 AWF' MI2 HALT2).
      { rewrite fk_restrict_mkst. exact RUN2. }
      intros mdl4 MI4 SBM4 HC4. rewrite fk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst (regupd r1 10 (Z_to_bv 64 0)) (at_ (ft_base t) 75660) MZ rom)) with MZ by reflexivity.
      rewrite (fk_munrestrict_same Hd' MZ MZ (fun a _ => eq_refl)).
      apply (CONT HLT r2 mdlm mdl4 SBMm MIm SBM4 MI4).
      + rewrite (AG2 1%bv ltac:(notin)). exact Q1.
      + rewrite (AG2 2%bv ltac:(notin)). rewrite getr_other by (intros E; discriminate E). exact B2.
      + exact C10.
      + intros x Hx. destruct (decide (x = 10%bv)) as [->|NE10]; [exfalso; apply Hx; (lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto|].
        rewrite (AG2 x). 2:{ (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros [E|[]]. apply NE10. symmetry. exact E. }
        rewrite getr_other by (intros E; apply NE10; exact E). apply AG1. exact Hx.
    - (* [comment removed for export] *)
      destruct (flush_nocall_t segs t TOK (mrestrict Hd mem) rom ra sp p size midend regs PRE' Hret R1 R2 R10 R11 HGE)
        as (r1 & RUN1 & B1 & B2 & AG1).
      rewrite (fl_frame_mrestrict Hd mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) P7 HSCR) in RUN1. fold MF in RUN1.
      apply (katD_msteps_acct segs Hd HOFFSEG WX A (mkst regs (ft_base t) mem rom)
               (mkst r1 ra (mrestrict Hd MF) rom) model Q LC AWF MI HALT).
      { rewrite fk_restrict_mkst. exact RUN1. }
      intros mdlm MIm SBMm HC1. rewrite fk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst regs (ft_base t) mem rom)) with mem by reflexivity.
      rewrite (fk_munrestrict_same Hd mem MF MFhid).
      exact (CONT0 HGE r1 mdlm SBMm MIm B1 B2 AG1).
  Qed.

End FLK.
End FPGen1.
End AsRtFlushK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoRtFlushI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtXStrlenI.BoRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 Bo_code_8a5a8_8a63c Bo_code_811d0_811fc.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition both_flush_tab : flush_tab :=
  {| ft_base := 0x6ea68; ft_mt := both_m2s_tab_6dffc; ft_g_pgsz := 0x105ef8; ft_p_pgsz := 0x19dc60; ft_g_seal := 0x105f58; ft_sv := 1 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma both_flush_tab_ok : flush_tab_ok BSEGS both_flush_tab.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold flush_tab_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ft_base ft_mt ft_g_pgsz ft_p_pgsz ft_g_seal ft_sv both_flush_tab] in G in change_no_check G' end).
  repeat match goal with |- _ /\ _ => split end.
  - (lazymatch goal with |- ?G => let G' := eval unfold flush_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold rel_words in G in change_no_check G' end). code_ato_vm.
  - (lazymatch goal with |- ?G => let G' := eval unfold imadv_words in G in change_no_check G' end). code_ato_vm.
  - exact both_m2s_tab_ok_6dffc.
  - apply bv_eq. vm_compute. reflexivity.
  - gload_tac F_8a5c0 D_8a5c0 F_8a5c4 D_8a5c4.
  - gload_tac F_811d0 D_811d0 F_811d4 D_811d4.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma both_flush_cells : flush_cells both_flush_tab = ltac:(let x := eval cbv in (flush_cells both_flush_tab) in exact x).
Proof using. reflexivity. Qed.
End FPGen1.
End BoRtFlushI.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush AsRtFlushK AsRtFlushI BoRtFlushI.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section FPGen1.
Context {fx : FPState}.


(* [comment removed for export] *)
Definition asan_flush_katD2 (Hd : word -> bool) (HOFF : H_off_segments AsRtFlushI.ASEGS Hd) (WX : wx_segs_nowrap AsRtFlushI.ASEGS) :=
  flush_katD2 AsRtFlushI.ASEGS Hd HOFF WX asan_flush_tab asan_flush_tab_ok.
Definition both_flush_katD2 (Hd : word -> bool) (HOFF : H_off_segments BoRtFlushI.BSEGS Hd) (WX : wx_segs_nowrap BoRtFlushI.BSEGS) :=
  flush_katD2 BoRtFlushI.BSEGS Hd HOFF WX both_flush_tab both_flush_tab_ok.
End FPGen1.
