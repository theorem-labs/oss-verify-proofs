(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAllocM0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Section FPGen0.
Context {fx : FPState}.
Definition gauipc_addi (segs : list Segment) (base : word) (off1 off2 : Z) (rt rd : reg) (v : word) : Prop :=
  exists x : word,
    (forall regs mem rom,
        msteps segs (mkst regs (at_ base off1) mem rom) (mkst (regupd regs rt x) (at_ base (off1 + 4)) mem rom))
    /\ (forall regs mem rom,
           getr regs rt = x ->
           msteps segs (mkst regs (at_ base off2) mem rom) (mkst (regupd regs rd v) (at_ base (off2 + 4)) mem rom)).
End FPGen0.
Ltac gauipc_addi_tac Fa Da Fb Db :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  let Hx := fresh "Hx" in
  wd_eexists; split;
  [ intros regs mem rom; lit_pc;
    (chain_step; [ reflexivity | eapply step_auipc; [exact Fa | reflexivity | exact Da] | step_simpl ]);
    gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc in G in change_no_check G' end); vals_lit; close_eq
  | intros regs mem rom Hx; lit_pc;
    (chain_step; [ reflexivity | eapply step_addi; [exact Fb | reflexivity | exact Db] | step_simpl ]);
    gres; rewrite Hx; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); vals_lit; close_eq ].

Section FPGen1.
Context {fx : FPState}.

Definition rzl_words : list (option (bv 32)) :=
  [Some W_5113c; Some W_51140; Some W_51144; Some W_51148; Some W_5114c; Some W_51150; Some W_51154; Some W_51158;
   Some W_5115c; Some W_51160; Some W_51164; Some W_51168; Some W_5116c; None; None; None; Some W_5117c; None;
   Some W_51184; Some W_51188; Some W_5118c; Some W_51190; Some W_51194; Some W_51198; Some W_5119c; Some W_511a0;
   Some W_511a4; Some W_511a8; Some W_511ac; Some W_511b0; Some W_511b4; Some W_511b8]%list.

Definition rss_words : list (option (bv 32)) := [None; None; Some W_7a974; Some W_7a978]%list.
Definition cpm_words : list (option (bv 32)) := [None; None; Some W_6f5fc; Some W_6f600; Some W_6f604]%list.
Definition gts_words : list (option (bv 32)) :=
  [Some W_77580; Some W_77584; Some W_77588; Some W_7758c; Some W_77590; Some W_77594; Some W_77598; Some W_7759c;
   Some W_775a0]%list.
Definition rmh_words : list (option (bv 32)) :=
  [Some W_7cb88; Some W_7cb8c; Some W_7cb90; Some W_7cb94; Some W_7cb98; Some W_7cb9c; Some W_7cba0; Some W_7cba4;
   None; None; Some W_7cbb0; Some W_7cbb4; Some W_7cbb8; Some W_7cbbc; Some W_7cbc0; Some W_7cbc4; Some W_7cbc8;
   Some W_7cbcc; Some W_7cbd0; Some W_7cbd4; Some W_7cbd8; Some W_7cbdc; Some W_7cbe0; Some W_7cbe4; Some W_7cbe8;
   Some W_7cbec; Some W_7cbf0; Some W_7cbf4; Some W_7cbf8; Some W_7cbfc; Some W_7cc00; Some W_7cc04; Some W_7cc08;
   Some W_7cc0c; Some W_7cc10; Some W_7cc14; Some W_7cc18; Some W_7cc1c; Some W_7cc20; Some W_7cc24; Some W_7cc28;
   Some W_7cc2c; Some W_7cc30; Some W_7cc34; Some W_7cc38; Some W_7cc3c]%list.
Definition lsn_words : list (option (bv 32)) :=
  [None; None; Some W_9bf80; Some W_9bf84; Some W_9bf88; Some W_9bf8c]%list.


Section LEAVES.
  Variable segs : list Segment.
  Variable rb : word.
  Variables (g_rss g_cpm g_lsan : Z) (hooks : word).
  Hypothesis HRSS : code_ato segs rb 0x7a974 rss_words.
  Hypothesis GRSS : gloadb segs rb 0x7a974 10 g_rss.
  Hypothesis HCPM : code_ato segs rb 0x6f5fc cpm_words.
  Hypothesis GCPM : gloadb segs rb 0x6f5fc 10 g_cpm.
  Hypothesis HGTS : code_ato segs rb 0x77588 gts_words.
  Hypothesis HRMH : code_ato segs rb 0x7cb90 rmh_words.
  Hypothesis GRMH : gaddr2 segs rb 0x7cbb0 10 18 hooks.
  Hypothesis HHK : code_ato segs rb 0x7cc48 [Some W_7cc40].         (* [comment removed for export] *)
  Hypothesis HLSN : code_ato segs rb 0x9bf80 lsn_words.
  Hypothesis GLSN : gload segs rb 0x9bf80 10 g_lsan.
  Hypothesis RBE : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variables (g_magic : Z) (TBL : word).                                (* [comment removed for export] *)
  Hypothesis HRZL : code_ato segs rb 0x51144 rzl_words.
  Hypothesis GRZM : gload segs rb 0x51178 12 g_magic.
  Hypothesis GRZT : gauipc_addi segs rb 0x51180 0x51188 14 14 TBL.

  Lemma Ro8 : fetch_word segs (at_ rb 0x7a97c) = Some W_7a974.  Proof using HRSS. exact (code_ato_get segs rb 0x7a974 rss_words 2 _ HRSS eq_refl). Qed.
  Lemma Ro12 : fetch_word segs (at_ rb 0x7a980) = Some W_7a978.  Proof using HRSS. exact (code_ato_get segs rb 0x7a974 rss_words 3 _ HRSS eq_refl). Qed.
  Lemma Co8 : fetch_word segs (at_ rb 0x6f604) = Some W_6f5fc.  Proof using HCPM. exact (code_ato_get segs rb 0x6f5fc cpm_words 2 _ HCPM eq_refl). Qed.
  Lemma Co12 : fetch_word segs (at_ rb 0x6f608) = Some W_6f600.  Proof using HCPM. exact (code_ato_get segs rb 0x6f5fc cpm_words 3 _ HCPM eq_refl). Qed.
  Lemma Co16 : fetch_word segs (at_ rb 0x6f60c) = Some W_6f604.  Proof using HCPM. exact (code_ato_get segs rb 0x6f5fc cpm_words 4 _ HCPM eq_refl). Qed.
  Lemma If1cb8 : fetch_word segs (at_ rb 0x77588) = Some W_77580.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 0 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1cbc : fetch_word segs (at_ rb 0x7758c) = Some W_77584.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 1 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1cc0 : fetch_word segs (at_ rb 0x77590) = Some W_77588.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 2 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1cc4 : fetch_word segs (at_ rb 0x77594) = Some W_7758c.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 3 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1cc8 : fetch_word segs (at_ rb 0x77598) = Some W_77590.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 4 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1ccc : fetch_word segs (at_ rb 0x7759c) = Some W_77594.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 5 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1cd0 : fetch_word segs (at_ rb 0x775a0) = Some W_77598.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 6 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1cd4 : fetch_word segs (at_ rb 0x775a4) = Some W_7759c.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 7 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If1cd8 : fetch_word segs (at_ rb 0x775a8) = Some W_775a0.  Proof using HGTS. exact (code_ato_get segs rb 0x77588 gts_words 8 _ HGTS eq_refl). Qed.   (* [comment removed for export] *)

  Lemma If949c : fetch_word segs (at_ rb 0x7cb90) = Some W_7cb88.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 0 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94a0 : fetch_word segs (at_ rb 0x7cb94) = Some W_7cb8c.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 1 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94a4 : fetch_word segs (at_ rb 0x7cb98) = Some W_7cb90.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 2 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94a8 : fetch_word segs (at_ rb 0x7cb9c) = Some W_7cb94.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 3 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94ac : fetch_word segs (at_ rb 0x7cba0) = Some W_7cb98.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 4 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94b0 : fetch_word segs (at_ rb 0x7cba4) = Some W_7cb9c.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 5 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94b4 : fetch_word segs (at_ rb 0x7cba8) = Some W_7cba0.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 6 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94b8 : fetch_word segs (at_ rb 0x7cbac) = Some W_7cba4.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 7 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94c4 : fetch_word segs (at_ rb 0x7cbb8) = Some W_7cbb0.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 10 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If94c8 : fetch_word segs (at_ rb 0x7cbbc) = Some W_7cbb4.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 11 _ HRMH eq_refl). Qed.



























   (* [comment removed for export] *)
  Lemma If953c : fetch_word segs (at_ rb 0x7cc30) = Some W_7cc28.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 40 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If9540 : fetch_word segs (at_ rb 0x7cc34) = Some W_7cc2c.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 41 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If9544 : fetch_word segs (at_ rb 0x7cc38) = Some W_7cc30.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 42 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If9548 : fetch_word segs (at_ rb 0x7cc3c) = Some W_7cc34.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 43 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If954c : fetch_word segs (at_ rb 0x7cc40) = Some W_7cc38.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 44 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If9550 : fetch_word segs (at_ rb 0x7cc44) = Some W_7cc3c.  Proof using HRMH. exact (code_ato_get segs rb 0x7cb90 rmh_words 45 _ HRMH eq_refl). Qed.   (* [comment removed for export] *)

  Lemma I11a72c : fetch_word segs (at_ rb 0x9bf88) = Some W_9bf80.  Proof using HLSN. exact (code_ato_get segs rb 0x9bf80 lsn_words 2 _ HLSN eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I11a730 : fetch_word segs (at_ rb 0x9bf8c) = Some W_9bf84.  Proof using HLSN. exact (code_ato_get segs rb 0x9bf80 lsn_words 3 _ HLSN eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I11a734 : fetch_word segs (at_ rb 0x9bf90) = Some W_9bf88.  Proof using HLSN. exact (code_ato_get segs rb 0x9bf80 lsn_words 4 _ HLSN eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I11a738 : fetch_word segs (at_ rb 0x9bf94) = Some W_9bf8c.  Proof using HLSN. exact (code_ato_get segs rb 0x9bf80 lsn_words 5 _ HLSN eq_refl). Qed.   (* [comment removed for export] *)


  Lemma If9554 : fetch_word segs (at_ rb 0x7cc48) = Some W_7cc40.  Proof using HHK. exact (code_ato_get segs rb 0x7cc48 [Some W_7cc40] 0 _ HHK eq_refl). Qed.
  Lemma RETrb : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d).
  Proof using RBE. intros d Hd Hdr. destruct RBE as [E1 E2]. pose proof (u64_range rb). apply ret_ok_at; [exact E1 | exact Hd | lia]. Qed.

  (* [comment removed for export] *)
  Theorem rss_run : forall mem rom regs (ra : word),
    rdn segs mem (Z_to_bv 64 g_rss) 1 = Some [Z_to_bv 8 0] -> ret_ok ra -> getr regs 1 = ra ->
    exists r, msteps segs (mkst regs (at_ rb 0x7a974) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ regs_agree (fun x => In x [10]) regs r.
  Proof using GRSS HRSS.
    intros mem rom regs ra Rf Hret H1. wd_eexists. split; [|split].
    - eapply msteps_trans; [eapply GRSS; exact Rf|]. zlit_at.
      an Ro8 D_7a974.                                      (* [comment removed for export] *)
      aret Ro12 D_7a978 ra.
      wd_refl.
    - gres. reflexivity.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Theorem cpm_run : forall mem rom regs (ra : word),
    rdn segs mem (Z_to_bv 64 g_cpm) 1 = Some [Z_to_bv 8 1] -> ret_ok ra -> getr regs 1 = ra ->
    exists r, msteps segs (mkst regs (at_ rb 0x6f5fc) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 1 /\ regs_agree (fun x => In x [10]) regs r.
  Proof using GCPM HCPM.
    intros mem rom regs ra Rf Hret H1. wd_eexists. split; [|split].
    - eapply msteps_trans; [eapply GCPM; exact Rf|]. zlit_at.
      afence Co8 D_6f5fc.
      an Co12 D_6f600.                                     (* [comment removed for export] *)
      aret Co16 D_6f604 ra.
      wd_refl.
    - gres. reflexivity.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Theorem lsan_run : forall mem rom regs (ra tp : word) (off : Z),
    rdn segs mem (Z_to_bv 64 g_lsan) 8 = Some (LE8 (Z_to_bv 64 off)) -> (0 <= off)%Z -> (U tp + off + 4 <= 2 ^ 64)%Z ->
    rdn segs mem (at_ tp off) 4 = Some (LE4 0) ->
    ret_ok ra -> getr regs 1 = ra -> getr regs 4 = tp ->
    exists r, msteps segs (mkst regs (at_ rb 0x9bf80) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ regs_agree (fun x => In x [10]) regs r.
  Proof using GLSN HLSN.
    intros mem rom regs ra tp off Rg Hoff Hnw Rc Hret H1 H4. pose proof (u64_range tp). wd_eexists. split; [|split].
    - eapply msteps_trans; [eapply GLSN; exact Rg|]. zlit_at.
      av I11a72c D_9bf80 (at_ tp off) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 0) (v := Z_to_bv 64 0);
          [exact I11a730 | reflexivity | exact D_9bf84 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rc | apply bytes4_small; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an I11a734 D_9bf88.                                 (* [comment removed for export] *)
      aret I11a738 D_9bf8c ra.
      wd_refl.
    - gres. reflexivity.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  Theorem gts_run : forall t mem rom regs (ra sp tp tsdp tctx thr : word),
    gct_tab_ok segs t -> gt_rb t = rb ->
    gctH segs t mem (at_ sp (-16)) tp tsdp tctx thr ->
    store_ok segs mem (at_ sp (-8)) 8 = true -> (2 ^ 32 + 32 <= U sp)%Z -> (4096 <= U thr)%Z -> (U thr + 4096 <= 2 ^ 64)%Z ->
    ret_ok ra -> getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp ->
    exists r, msteps segs (mkst regs (at_ rb 0x77588) mem rom)
                         (mkst r ra (wbytes (wbytes mem (at_ sp (-8)) (LE8 ra)) (at_ sp (-24)) (LE8 (at_ rb 0x77594))) rom)
      /\ getr r 10 = at_ thr 2800 /\ regs_agree (fun x => In x [10; 11]) regs r.
  Proof using RBE HGTS.
    intros t mem rom regs ra sp tp tsdp tctx thr TOK TRB GH SOK Gsp Gthr0 Gthr Hret H1 H2 H4.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range thr).
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 ra)).
    assert (GH1 : gctH segs t M1 (at_ sp (-16)) tp tsdp tctx thr).
    { apply (gctH_keep segs t mem M1 _ _ _ _ _ GH); [| (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply wbytes_grows].
      intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (W1 : exists r1, msteps segs (mkst regs (at_ rb 0x77588) mem rom) (mkst r1 (at_ rb 0x783bc) M1 rom)
                 /\ getr r1 1 = at_ rb 0x77594 /\ getr r1 2 = at_ sp (-16) /\ getr r1 4 = tp /\ regs_agree (fun x => In x [1; 2; 10; 11]) regs r1).
    { wd_eexists. split.
      { an If1cb8 D_77580.                                 (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ sp (-8));
            [exact If1cbc | reflexivity | exact D_77584 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | exact SOK]
          | step_simpl]; vn.                                (* [comment removed for export] *)
        change (wbytes _ _ _) with M1.
        an If1cc0 D_77588.                                 (* [comment removed for export] *)
        wd_refl. }
      post. ra_solve. }
    destruct W1 as (r1 & RUN1 & A1 & A2 & A4 & AG1).
    destruct (gct_run segs t TOK M1 rom r1 (at_ rb 0x77594) (at_ sp (-16)) tp tsdp tctx thr GH1 (RETrb 0x77594 eq_refl ltac:(lia))
                A1 A2 A4) as (r2 & RUN2 & B10 & B11 & AG2).
    rewrite TRB, at_at in RUN2. cbn [Z.add] in RUN2.
    pose proof (gh_tctx_nz _ _ _ _ _ _ _ _ GH) as NZ.
    wd_eexists. split; [|split].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      ab_ft If1cc4 D_7758c ltac:(condz).                 (* [comment removed for export] *)
      an If1cc8 D_77590. an If1ccc D_77594.              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ra) (v := ra);
          [exact If1cd0 | reflexivity | exact D_77598
          | gres; rwH; rewrite (AG2 2) by notin_list; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                  (* [comment removed for export] *)
      an If1cd4 D_7759c.                                    (* [comment removed for export] *)
      aret If1cd8 D_775a0 ra.
      wd_refl.
    - gres. rewrite ?B10, ?at_at. first [reflexivity | f_equal; lia].
    - apply (regs_agree_strengthen [10; 11] [1; 2; 10; 11] regs).
      + eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2|]. ra_solve.
      + intros i Hi Hni. cbn [In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rewrite ?(AG2 2) by notin_list; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Theorem rmh_run : forall mem rom regs (ra sp : word),
    rdn segs mem hooks 8 = Some (LE8 (Z_to_bv 64 0)) -> (U hooks + 8 <= 2 ^ 32)%Z ->
    store_ok segs mem (at_ sp (-32)) 32 = true -> (2 ^ 32 + 32 <= U sp)%Z ->
    ret_ok ra -> getr regs 1 = ra -> getr regs 2 = sp ->
    exists r, msteps segs (mkst regs (at_ rb 0x7cb90) mem rom)
                         (mkst r ra (wbytes (wbytes (wbytes (wbytes mem (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8)))
                                               (at_ sp (-24)) (LE8 (getr regs 9))) (at_ sp (-32)) (LE8 (getr regs 18))) rom)
      /\ regs_agree (fun x => In x [10; 11; 12]) regs r.
  Proof using RBE HHK GRMH HRMH.
    intros mem rom regs ra sp Rh Hh SOK Gsp Hret H1 H2. pose proof (u64_range sp) as Hspr. pose proof (u64_range hooks).
    destruct GRMH as [gx GA].
    Ltac fsdh F D aa Hs lo :=
      chain_step; [reflexivity
        | eapply step_sd_at with (a := aa);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia] | gres; rwH; reflexivity
          | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
            eapply (store_ok_sub segs _ lo _ 32); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
        | step_simpl]; vn.
    wd_eexists. split.
    - an If949c D_7cb88.                                    (* [comment removed for export] *)
      fsdh If94a0 D_7cb8c (at_ sp (-8)) SOK (at_ sp (-32)).
      fsdh If94a4 D_7cb90 (at_ sp (-16)) SOK (at_ sp (-32)).
      fsdh If94a8 D_7cb94 (at_ sp (-24)) SOK (at_ sp (-32)).
      fsdh If94ac D_7cb98 (at_ sp (-32)) SOK (at_ sp (-32)).
      an If94b0 D_7cb9c. an If94b4 D_7cba0.               (* [comment removed for export] *)
      an If94b8 D_7cba4.                                    (* [comment removed for export] *)
      pose proof (RETrb 0x7cbb0 eq_refl ltac:(lia)) as RT1.
      aret If9554 D_7cc40 (at_ rb 0x7cbb0).                 (* [comment removed for export] *)
      eapply msteps_trans; [apply GA|]. zlit_at.             (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact If94c4 | reflexivity | exact D_7cbb0
          | gres; rwH; imm_norm; rewrite ?v_addi_0; rewrite <- Rh; apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; cbn in Hx;
              rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia; reflexivity]
          | apply bytes_le_to_Z_8 ]
        | step_simpl]; vn.                                  (* [comment removed for export] *)
      ab_tk If94c8 D_7cbb4 ltac:(condz).                   (* [comment removed for export] *)
      Ltac rl F D vv := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; rd8_chain | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      rl If953c D_7cc28 ra. rl If9540 D_7cc2c (getr regs 8). rl If9544 D_7cc30 (getr regs 9). rl If9548 D_7cc34 (getr regs 18).
      an If954c D_7cc38.                                    (* [comment removed for export] *)
      aret If9550 D_7cc3c ra.
      wd_refl.
    - apply (regs_agree_strengthen [10; 11; 12] [1; 2; 8; 9; 18; 10; 11; 12] regs).
      + ra_solve.
      + intros i Hi Hni. cbn [In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]).
        destruct Hi.
  Qed.
  Lemma I6c9b8 : fetch_word segs (at_ rb 0x51144) = Some W_5113c.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 0 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9bc : fetch_word segs (at_ rb 0x51148) = Some W_51140.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 1 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9c0 : fetch_word segs (at_ rb 0x5114c) = Some W_51144.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 2 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9c4 : fetch_word segs (at_ rb 0x51150) = Some W_51148.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 3 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9c8 : fetch_word segs (at_ rb 0x51154) = Some W_5114c.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 4 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9cc : fetch_word segs (at_ rb 0x51158) = Some W_51150.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 5 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9d0 : fetch_word segs (at_ rb 0x5115c) = Some W_51154.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 6 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9d4 : fetch_word segs (at_ rb 0x51160) = Some W_51158.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 7 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9d8 : fetch_word segs (at_ rb 0x51164) = Some W_5115c.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 8 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9dc : fetch_word segs (at_ rb 0x51168) = Some W_51160.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 9 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9e0 : fetch_word segs (at_ rb 0x5116c) = Some W_51164.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 10 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9e4 : fetch_word segs (at_ rb 0x51170) = Some W_51168.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 11 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9e8 : fetch_word segs (at_ rb 0x51174) = Some W_5116c.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 12 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c9f8 : fetch_word segs (at_ rb 0x51184) = Some W_5117c.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 16 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca00 : fetch_word segs (at_ rb 0x5118c) = Some W_51184.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 18 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca04 : fetch_word segs (at_ rb 0x51190) = Some W_51188.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 19 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca08 : fetch_word segs (at_ rb 0x51194) = Some W_5118c.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 20 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca0c : fetch_word segs (at_ rb 0x51198) = Some W_51190.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 21 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca10 : fetch_word segs (at_ rb 0x5119c) = Some W_51194.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 22 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca14 : fetch_word segs (at_ rb 0x511a0) = Some W_51198.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 23 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca18 : fetch_word segs (at_ rb 0x511a4) = Some W_5119c.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 24 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca1c : fetch_word segs (at_ rb 0x511a8) = Some W_511a0.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 25 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca20 : fetch_word segs (at_ rb 0x511ac) = Some W_511a4.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 26 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca24 : fetch_word segs (at_ rb 0x511b0) = Some W_511a8.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 27 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca28 : fetch_word segs (at_ rb 0x511b4) = Some W_511ac.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 28 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca2c : fetch_word segs (at_ rb 0x511b8) = Some W_511b0.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 29 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca30 : fetch_word segs (at_ rb 0x511bc) = Some W_511b4.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 30 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6ca34 : fetch_word segs (at_ rb 0x511c0) = Some W_511b8.  Proof using HRZL. exact (code_ato_get segs rb 0x51144 rzl_words 31 _ HRZL eq_refl). Qed.   (* [comment removed for export] *)


  Definition MAGICw : word := Z_to_bv 64 0x0218a392cd3d5dbf.

  (* [comment removed for export] *)
  Section RZL.
    Variables (mem rom : word -> option byte) (regs : bvmap 5 word) (ra sp : word).
    Hypothesis Rm : rdn segs mem (Z_to_bv 64 g_magic) 8 = Some (LE8 MAGICw).
    Hypothesis GT : (U TBL + 64 <= 2 ^ 64)%Z.
    Hypothesis SOK : store_ok segs mem (at_ sp (-8)) 8 = true.
    Hypothesis Gsp : (8 <= U sp)%Z.
    Hypothesis Gsep : (U sp <= U TBL \/ U TBL + 64 <= U sp - 8)%Z.
    Hypothesis Gm : (0 <= g_magic /\ g_magic + 8 <= U sp - 8)%Z.
    Hypothesis Hret : ret_ok ra.
    Hypothesis H1 : getr regs 1 = ra.
    Hypothesis H2 : getr regs 2 = sp.
    Definition rzM1 := wbytes mem (at_ sp (-8)) (LE8 ra).
    Lemma rzM1_out : forall y : word, (U y < U sp - 8 \/ U sp <= U y)%Z -> rzM1 y = mem y.
    Proof using Gsp rb.
      intros y Hy. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold rzM1 in G in change_no_check G' end).
      rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    Qed.
    Lemma rzRm1 : rdn segs rzM1 (Z_to_bv 64 g_magic) 8 = Some (LE8 MAGICw).
    Proof using Gm Gsp GT Rm TBL rb. pose proof (u64_range sp). rewrite <- Rm. apply rdn_ext; [wd_ulia_c | intros y Hy; apply rzM1_out; revert Hy; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hy; lia]. Qed.
    Lemma rzRt1 : forall idx L, (0 <= idx < 63)%Z -> rdn segs mem (at_ TBL idx) 1 = Some [Z_to_bv 8 L] -> rdn segs rzM1 (at_ TBL idx) 1 = Some [Z_to_bv 8 L].
    Proof using Gm Gsep Gsp GT g_magic rb.
      intros idx L Hidx Rt. pose proof (u64_range sp). pose proof (u64_range TBL).
      rewrite <- Rt. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros y Hy; apply rzM1_out; rewrite at_u in Hy by lia; cbn in Hy; lia].
    Qed.

    Ltac rzl_walk Rt1 GA GB :=
      an I6c9b8 D_5113c;                                     (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ sp (-8));
          [exact I6c9bc | reflexivity | exact D_51140 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | exact SOK]
        | step_simpl]); vn;                                 (* [comment removed for export] *)
      change (wbytes _ _ _) with rzM1;
      an I6c9c0 D_51144; an I6c9c4 D_51148; an I6c9c8 D_5114c;   (* [comment removed for export] *)
      ab_ft I6c9cc D_51150 ltac:(condz);                    (* [comment removed for export] *)
      an I6c9d0 D_51154; an I6c9d4 D_51158;
      ab_ft I6c9d8 D_5115c ltac:(condz);                    (* [comment removed for export] *)
      an I6c9dc D_51160; an I6c9e0 D_51164;
      ab_ft I6c9e4 D_51168 ltac:(condz);                    (* [comment removed for export] *)
      an I6c9e8 D_5116c;                                     (* [comment removed for export] *)
      (eapply msteps_trans; [eapply GRZM; exact rzRm1|]); zlit_at;   (* [comment removed for export] *)
      (eapply msteps_trans; [apply GA|]); zlit_at;           (* [comment removed for export] *)
      an I6c9f8 D_5117c;                                     (* [comment removed for export] *)
      (eapply msteps_trans; [apply GB; gres; reflexivity|]); zlit_at;   (* [comment removed for export] *)
      rewrite ?regupd_regupd_same;
      an I6ca00 D_51184;                                     (* [comment removed for export] *)
      an I6ca04 D_51188;                                     (* [comment removed for export] *)
      match goal with |- context [regupd _ 11 (Z_to_bv 64 ?i)] =>
        av I6ca08 D_5118c (at_ TBL i) ltac:(apply v_add_at; lia) end;   (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_lbu; [exact I6ca0c | reflexivity | exact D_51190 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rt1]
        | step_simpl]); vn;                                 (* [comment removed for export] *)
      an I6ca10 D_51194; an I6ca14 D_51198;                 (* [comment removed for export] *)
      ab_ft I6ca18 D_5119c ltac:(condz);                    (* [comment removed for export] *)
      an I6ca1c D_511a0; an I6ca20 D_511a4;                 (* [comment removed for export] *)
      ab_ft I6ca24 D_511a8 ltac:(condz);                    (* [comment removed for export] *)
      an I6ca28 D_511ac;                                     (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ra) (v := ra);
          [exact I6ca2c | reflexivity | exact D_511b0 | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold rzM1 in G in change_no_check G' end); apply rdn_wbytes_hit8; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | apply bytes_le_to_Z_8]
        | step_simpl]); vn;                                 (* [comment removed for export] *)
      an I6ca30 D_511b4;                                     (* [comment removed for export] *)
      aret I6ca34 D_511b8 ra;
      wd_refl.
    Ltac rzl_post :=
      apply (regs_agree_strengthen [10; 11; 12; 13; 14] [1; 2; 10; 11; 12; 13; 14] regs); [ra_solve|];
      intros i Hi Hni; cbn [In] in Hi;
      repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto] |]);
      destruct Hi.

    Theorem rzl16_run : rdn segs mem (at_ TBL 8) 1 = Some [Z_to_bv 8 4] -> getr regs 10 = Z_to_bv 64 16 ->
      exists r, msteps segs (mkst regs (at_ rb 0x51144) mem rom) (mkst r ra rzM1 rom)
        /\ getr r 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]) regs r.
    Proof using H2 H1 Hret Gm Gsep Gsp SOK GT Rm GRZT GRZM HRZL g_magic RBE.
      intros Rt H10. pose proof (u64_range sp) as Hspr. pose proof (u64_range TBL) as HT.
      pose proof (rzRt1 8 4 ltac:(lia) Rt) as Rt1. destruct GRZT as [gx [GA GB]].
      wd_eexists. split; [|split]; [rzl_walk Rt1 GA GB | gres; reflexivity | rzl_post].
    Qed.
    Theorem rzl2048_run : rdn segs mem (at_ TBL 49) 1 = Some [Z_to_bv 8 11] -> getr regs 10 = Z_to_bv 64 2048 ->
      exists r, msteps segs (mkst regs (at_ rb 0x51144) mem rom) (mkst r ra rzM1 rom)
        /\ getr r 10 = Z_to_bv 64 7 /\ regs_agree (fun r => In r [10; 11; 12; 13; 14]) regs r.
    Proof using H2 H1 Hret Gm Gsep Gsp SOK GT Rm GRZT GRZM HRZL g_magic RBE.
      intros Rt H10. pose proof (u64_range sp) as Hspr. pose proof (u64_range TBL) as HT.
      pose proof (rzRt1 49 11 ltac:(lia) Rt) as Rt1. destruct GRZT as [gx [GA GB]].
      wd_eexists. split; [|split]; [rzl_walk Rt1 GA GB | gres; reflexivity | rzl_post].
    Qed.
  End RZL.
End LEAVES.
End FPGen1.
End AsAllocM0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition am_words : list (option (bv 32)) :=
  [Some W_4bac0; Some W_4bac4; Some W_4bac8; Some W_4bacc; Some W_4bad0; None; Some W_4bad8; Some W_4badc; None;
   Some W_4bae4; Some W_4bae8; Some W_4baec; Some W_4baf0; Some W_4baf4; Some W_4baf8; Some W_4bafc; Some W_4bb00;
   Some W_4bb04; Some W_4bb08; Some W_4bb0c; Some W_4bb10; Some W_4bb14; Some W_4bb18]%list.
Definition al_words : list (option (bv 32)) :=
  [Some W_4bb1c; Some W_4bb20; Some W_4bb24; Some W_4bb28; Some W_4bb2c; Some W_4bb30; Some W_4bb34; Some W_4bb38;
   Some W_4bb3c; Some W_4bb40; Some W_4bb44; Some W_4bb48; Some W_4bb4c; Some W_4bb50; Some W_4bb54; Some W_4bb58;
   Some W_4bb5c; Some W_4bb60; Some W_4bb64; Some W_4bb68; Some W_4bb6c; Some W_4bb70; Some W_4bb74; Some W_4bb78;
   Some W_4bb7c; Some W_4bb80; Some W_4bb84; Some W_4bb88; Some W_4bb8c; Some W_4bb90; Some W_4bb94; Some W_4bb98;
   Some W_4bb9c; Some W_4bba0; Some W_4bba4; Some W_4bba8; Some W_4bbac; Some W_4bbb0; Some W_4bbb4; Some W_4bbb8;
   Some W_4bbbc; Some W_4bbc0; Some W_4bbc4; Some W_4bbc8; Some W_4bbcc; Some W_4bbd0; Some W_4bbd4; Some W_4bbd8;
   None; None; Some W_4bbe4; Some W_4bbe8; Some W_4bbec; None; Some W_4bbf4; None; Some W_4bbfc; Some W_4bc00;
   Some W_4bc04; Some W_4bc08; Some W_4bc0c; Some W_4bc10; Some W_4bc14; Some W_4bc18; Some W_4bc1c; Some W_4bc20;
   Some W_4bc24; Some W_4bc28; Some W_4bc2c; Some W_4bc30; Some W_4bc34; Some W_4bc38; Some W_4bc3c; Some W_4bc40;
   Some W_4bc44; Some W_4bc48; Some W_4bc4c; Some W_4bc50; Some W_4bc54; Some W_4bc58; Some W_4bc5c; Some W_4bc60;
   Some W_4bc64; Some W_4bc68; Some W_4bc6c; Some W_4bc70; Some W_4bc74; Some W_4bc78; Some W_4bc7c; Some W_4bc80;
   Some W_4bc84; Some W_4bc88; Some W_4bc8c; Some W_4bc90; Some W_4bc94; Some W_4bc98; Some W_4bc9c; Some W_4bca0;
   Some W_4bca4; Some W_4bca8; Some W_4bcac; Some W_4bcb0; Some W_4bcb4; Some W_4bcb8; Some W_4bcbc; Some W_4bcc0;
   Some W_4bcc4; Some W_4bcc8; Some W_4bccc; Some W_4bcd0; Some W_4bcd4; Some W_4bcd8; Some W_4bcdc; Some W_4bce0;
   Some W_4bce4; Some W_4bce8; Some W_4bcec; Some W_4bcf0; Some W_4bcf4; Some W_4bcf8; Some W_4bcfc; Some W_4bd00;
   Some W_4bd04; Some W_4bd08; Some W_4bd0c; Some W_4bd10; Some W_4bd14; Some W_4bd18; Some W_4bd1c; Some W_4bd20;
   Some W_4bd24; Some W_4bd28; Some W_4bd2c; Some W_4bd30; Some W_4bd34; Some W_4bd38; Some W_4bd3c; Some W_4bd40;
   Some W_4bd44; None; None; Some W_4bd50; Some W_4bd54; Some W_4bd58; Some W_4bd5c; Some W_4bd60;
   Some W_4bd64; Some W_4bd68; Some W_4bd6c; Some W_4bd70; Some W_4bd74; Some W_4bd78; Some W_4bd7c; Some W_4bd80;
   Some W_4bd84; Some W_4bd88; Some W_4bd8c; Some W_4bd90; Some W_4bd94; Some W_4bd98; Some W_4bd9c; Some W_4bda0;
   Some W_4bda4; Some W_4bda8; Some W_4bdac; Some W_4bdb0; Some W_4bdb4; Some W_4bdb8]%list.

(* [comment removed for export] *)
Lemma rz_log_cases : forall n, (1 <= n)%Z ->
  (n <= 48 /\ rz_log n = 0 \/ 49 <= n <= 96 /\ rz_log n = 1 \/ 97 <= n <= 448 /\ rz_log n = 2 \/ 449 <= n <= 3968 /\ rz_log n = 3
   \/ 3969 <= n <= 16128 /\ rz_log n = 4 \/ 16129 <= n <= 32256 /\ rz_log n = 5 \/ 32257 <= n <= 64512 /\ rz_log n = 6 \/ 64513 <= n /\ rz_log n = 7)%Z.
Proof using.
  intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold rz_log in G in change_no_check G' end).
  repeat match goal with |- context [Z.leb n ?k] => destruct (Z.leb_spec n k) end; lia.
Qed.
Lemma rz_log_range : forall n, (0 <= rz_log n <= 7)%Z.
Proof using. intros n. (lazymatch goal with |- ?G => let G' := eval unfold rz_log in G in change_no_check G' end). repeat match goal with |- context [Z.leb n ?k] => destruct (Z.leb n k) end; lia. Qed.


(* [comment removed for export] *)
Record am_tab := AMT { am_rb : word; am_inst : word; am_g_magic : Z; am_tbl2 : word; am_tbl : word; am_g_inited : Z; am_g_rss : Z }.
Record am_tab_ok (segs : list Segment) (t : am_tab) : Prop := AMTOK {
  ato_am : code_ato segs (am_rb t) 0x4bac8 am_words;
  ato_al : code_ato segs (am_rb t) 0x4bb24 al_words;
  ato_inst : gauipc_addi segs (am_rb t) 0x4badc 0x4bae8 10 10 (am_inst t);
  ato_mag : gload segs (am_rb t) 0x4bbe4 12 (am_g_magic t);
  ato_tbl2 : gauipc_addi segs (am_rb t) 0x4bbf8 0x4bc00 12 12 (am_tbl2 t);
  ato_ain : code_ato segs (am_rb t) 0x74cac ain_words;
  ato_ainb : gloadb segs (am_rb t) 0x74cac 10 (am_g_inited t);
  ato_rss : code_ato segs (am_rb t) 0x7a974 rss_words;
  ato_rssb : gloadb segs (am_rb t) 0x7a974 10 (am_g_rss t);
  ato_rzl : code_ato segs (am_rb t) 0x51144 rzl_words;
  ato_rzm : gload segs (am_rb t) 0x51178 12 (am_g_magic t);
  ato_rzt : gauipc_addi segs (am_rb t) 0x51180 0x51188 14 14 (am_tbl t);
  ato_rb : (U (am_rb t) mod 2 = 0)%Z /\ (U (am_rb t) + 2 ^ 24 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition am_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Section AM.
  Variable segs : list Segment.
  Variable t : am_tab.
  Hypothesis TOK : am_tab_ok segs t.
  #[local] Abbreviation rb := (am_rb t).
  #[local] Abbreviation INST := (am_inst t).
  Let HAM : code_ato segs rb 0x4bac8 am_words := ato_am _ _ TOK.
  Let HAL : code_ato segs rb 0x4bb24 al_words := ato_al _ _ TOK.

  Lemma I669fc : fetch_word segs (at_ rb 0x4bac8) = Some W_4bac0.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 0 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a00 : fetch_word segs (at_ rb 0x4bacc) = Some W_4bac4.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 1 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a04 : fetch_word segs (at_ rb 0x4bad0) = Some W_4bac8.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 2 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a08 : fetch_word segs (at_ rb 0x4bad4) = Some W_4bacc.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 3 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a0c : fetch_word segs (at_ rb 0x4bad8) = Some W_4bad0.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 4 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a14 : fetch_word segs (at_ rb 0x4bae0) = Some W_4bad8.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 6 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a18 : fetch_word segs (at_ rb 0x4bae4) = Some W_4badc.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 7 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a20 : fetch_word segs (at_ rb 0x4baec) = Some W_4bae4.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 9 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a24 : fetch_word segs (at_ rb 0x4baf0) = Some W_4bae8.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4bac8 am_words 10 _ HAM eq_refl). Qed.











   (* [comment removed for export] *)

  Lemma I66a58 : fetch_word segs (at_ rb 0x4bb24) = Some W_4bb1c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 0 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a5c : fetch_word segs (at_ rb 0x4bb28) = Some W_4bb20.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 1 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a60 : fetch_word segs (at_ rb 0x4bb2c) = Some W_4bb24.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 2 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a64 : fetch_word segs (at_ rb 0x4bb30) = Some W_4bb28.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 3 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a68 : fetch_word segs (at_ rb 0x4bb34) = Some W_4bb2c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 4 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a6c : fetch_word segs (at_ rb 0x4bb38) = Some W_4bb30.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 5 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a70 : fetch_word segs (at_ rb 0x4bb3c) = Some W_4bb34.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 6 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a74 : fetch_word segs (at_ rb 0x4bb40) = Some W_4bb38.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 7 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a78 : fetch_word segs (at_ rb 0x4bb44) = Some W_4bb3c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 8 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a7c : fetch_word segs (at_ rb 0x4bb48) = Some W_4bb40.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 9 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a80 : fetch_word segs (at_ rb 0x4bb4c) = Some W_4bb44.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 10 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a84 : fetch_word segs (at_ rb 0x4bb50) = Some W_4bb48.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 11 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a88 : fetch_word segs (at_ rb 0x4bb54) = Some W_4bb4c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 12 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a8c : fetch_word segs (at_ rb 0x4bb58) = Some W_4bb50.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 13 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a90 : fetch_word segs (at_ rb 0x4bb5c) = Some W_4bb54.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 14 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a94 : fetch_word segs (at_ rb 0x4bb60) = Some W_4bb58.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 15 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a98 : fetch_word segs (at_ rb 0x4bb64) = Some W_4bb5c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 16 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66a9c : fetch_word segs (at_ rb 0x4bb68) = Some W_4bb60.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 17 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66aa0 : fetch_word segs (at_ rb 0x4bb6c) = Some W_4bb64.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 18 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66aa4 : fetch_word segs (at_ rb 0x4bb70) = Some W_4bb68.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 19 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66aa8 : fetch_word segs (at_ rb 0x4bb74) = Some W_4bb6c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 20 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66aac : fetch_word segs (at_ rb 0x4bb78) = Some W_4bb70.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 21 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ab0 : fetch_word segs (at_ rb 0x4bb7c) = Some W_4bb74.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 22 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ab4 : fetch_word segs (at_ rb 0x4bb80) = Some W_4bb78.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 23 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ab8 : fetch_word segs (at_ rb 0x4bb84) = Some W_4bb7c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 24 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66abc : fetch_word segs (at_ rb 0x4bb88) = Some W_4bb80.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 25 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ac0 : fetch_word segs (at_ rb 0x4bb8c) = Some W_4bb84.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 26 _ HAL eq_refl). Qed.


   (* [comment removed for export] *)
  Lemma I66ad0 : fetch_word segs (at_ rb 0x4bb9c) = Some W_4bb94.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 30 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ad4 : fetch_word segs (at_ rb 0x4bba0) = Some W_4bb98.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 31 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ad8 : fetch_word segs (at_ rb 0x4bba4) = Some W_4bb9c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 32 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66adc : fetch_word segs (at_ rb 0x4bba8) = Some W_4bba0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 33 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ae0 : fetch_word segs (at_ rb 0x4bbac) = Some W_4bba4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 34 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ae4 : fetch_word segs (at_ rb 0x4bbb0) = Some W_4bba8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 35 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ae8 : fetch_word segs (at_ rb 0x4bbb4) = Some W_4bbac.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 36 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66aec : fetch_word segs (at_ rb 0x4bbb8) = Some W_4bbb0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 37 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66af0 : fetch_word segs (at_ rb 0x4bbbc) = Some W_4bbb4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 38 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66af4 : fetch_word segs (at_ rb 0x4bbc0) = Some W_4bbb8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 39 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66af8 : fetch_word segs (at_ rb 0x4bbc4) = Some W_4bbbc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 40 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66afc : fetch_word segs (at_ rb 0x4bbc8) = Some W_4bbc0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 41 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b00 : fetch_word segs (at_ rb 0x4bbcc) = Some W_4bbc4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 42 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b04 : fetch_word segs (at_ rb 0x4bbd0) = Some W_4bbc8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 43 _ HAL eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma I66b0c : fetch_word segs (at_ rb 0x4bbd8) = Some W_4bbd0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 45 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b10 : fetch_word segs (at_ rb 0x4bbdc) = Some W_4bbd4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 46 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b14 : fetch_word segs (at_ rb 0x4bbe0) = Some W_4bbd8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 47 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b20 : fetch_word segs (at_ rb 0x4bbec) = Some W_4bbe4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 50 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b24 : fetch_word segs (at_ rb 0x4bbf0) = Some W_4bbe8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 51 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b28 : fetch_word segs (at_ rb 0x4bbf4) = Some W_4bbec.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 52 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b30 : fetch_word segs (at_ rb 0x4bbfc) = Some W_4bbf4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 54 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b38 : fetch_word segs (at_ rb 0x4bc04) = Some W_4bbfc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 56 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b3c : fetch_word segs (at_ rb 0x4bc08) = Some W_4bc00.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 57 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b40 : fetch_word segs (at_ rb 0x4bc0c) = Some W_4bc04.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 58 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b44 : fetch_word segs (at_ rb 0x4bc10) = Some W_4bc08.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 59 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b48 : fetch_word segs (at_ rb 0x4bc14) = Some W_4bc0c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 60 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b4c : fetch_word segs (at_ rb 0x4bc18) = Some W_4bc10.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 61 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b50 : fetch_word segs (at_ rb 0x4bc1c) = Some W_4bc14.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 62 _ HAL eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma I66b58 : fetch_word segs (at_ rb 0x4bc24) = Some W_4bc1c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 64 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b5c : fetch_word segs (at_ rb 0x4bc28) = Some W_4bc20.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 65 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b60 : fetch_word segs (at_ rb 0x4bc2c) = Some W_4bc24.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 66 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b64 : fetch_word segs (at_ rb 0x4bc30) = Some W_4bc28.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 67 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b68 : fetch_word segs (at_ rb 0x4bc34) = Some W_4bc2c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 68 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b6c : fetch_word segs (at_ rb 0x4bc38) = Some W_4bc30.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 69 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b70 : fetch_word segs (at_ rb 0x4bc3c) = Some W_4bc34.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 70 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b74 : fetch_word segs (at_ rb 0x4bc40) = Some W_4bc38.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 71 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b78 : fetch_word segs (at_ rb 0x4bc44) = Some W_4bc3c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 72 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b7c : fetch_word segs (at_ rb 0x4bc48) = Some W_4bc40.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 73 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b80 : fetch_word segs (at_ rb 0x4bc4c) = Some W_4bc44.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 74 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b84 : fetch_word segs (at_ rb 0x4bc50) = Some W_4bc48.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 75 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b88 : fetch_word segs (at_ rb 0x4bc54) = Some W_4bc4c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 76 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b8c : fetch_word segs (at_ rb 0x4bc58) = Some W_4bc50.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 77 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b90 : fetch_word segs (at_ rb 0x4bc5c) = Some W_4bc54.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 78 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b94 : fetch_word segs (at_ rb 0x4bc60) = Some W_4bc58.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 79 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b98 : fetch_word segs (at_ rb 0x4bc64) = Some W_4bc5c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 80 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66b9c : fetch_word segs (at_ rb 0x4bc68) = Some W_4bc60.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 81 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ba0 : fetch_word segs (at_ rb 0x4bc6c) = Some W_4bc64.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 82 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ba4 : fetch_word segs (at_ rb 0x4bc70) = Some W_4bc68.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 83 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ba8 : fetch_word segs (at_ rb 0x4bc74) = Some W_4bc6c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 84 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bac : fetch_word segs (at_ rb 0x4bc78) = Some W_4bc70.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 85 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bb0 : fetch_word segs (at_ rb 0x4bc7c) = Some W_4bc74.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 86 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bb4 : fetch_word segs (at_ rb 0x4bc80) = Some W_4bc78.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 87 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bb8 : fetch_word segs (at_ rb 0x4bc84) = Some W_4bc7c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 88 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bbc : fetch_word segs (at_ rb 0x4bc88) = Some W_4bc80.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 89 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bc0 : fetch_word segs (at_ rb 0x4bc8c) = Some W_4bc84.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 90 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bc4 : fetch_word segs (at_ rb 0x4bc90) = Some W_4bc88.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 91 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bc8 : fetch_word segs (at_ rb 0x4bc94) = Some W_4bc8c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 92 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bcc : fetch_word segs (at_ rb 0x4bc98) = Some W_4bc90.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 93 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bd0 : fetch_word segs (at_ rb 0x4bc9c) = Some W_4bc94.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 94 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bd4 : fetch_word segs (at_ rb 0x4bca0) = Some W_4bc98.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 95 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bd8 : fetch_word segs (at_ rb 0x4bca4) = Some W_4bc9c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 96 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bdc : fetch_word segs (at_ rb 0x4bca8) = Some W_4bca0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 97 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66be0 : fetch_word segs (at_ rb 0x4bcac) = Some W_4bca4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 98 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66be4 : fetch_word segs (at_ rb 0x4bcb0) = Some W_4bca8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 99 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66be8 : fetch_word segs (at_ rb 0x4bcb4) = Some W_4bcac.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 100 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bec : fetch_word segs (at_ rb 0x4bcb8) = Some W_4bcb0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 101 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bf0 : fetch_word segs (at_ rb 0x4bcbc) = Some W_4bcb4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 102 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bf4 : fetch_word segs (at_ rb 0x4bcc0) = Some W_4bcb8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 103 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bf8 : fetch_word segs (at_ rb 0x4bcc4) = Some W_4bcbc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 104 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66bfc : fetch_word segs (at_ rb 0x4bcc8) = Some W_4bcc0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 105 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c00 : fetch_word segs (at_ rb 0x4bccc) = Some W_4bcc4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 106 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c04 : fetch_word segs (at_ rb 0x4bcd0) = Some W_4bcc8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 107 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c08 : fetch_word segs (at_ rb 0x4bcd4) = Some W_4bccc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 108 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c0c : fetch_word segs (at_ rb 0x4bcd8) = Some W_4bcd0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 109 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c10 : fetch_word segs (at_ rb 0x4bcdc) = Some W_4bcd4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 110 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c14 : fetch_word segs (at_ rb 0x4bce0) = Some W_4bcd8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 111 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c18 : fetch_word segs (at_ rb 0x4bce4) = Some W_4bcdc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 112 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c1c : fetch_word segs (at_ rb 0x4bce8) = Some W_4bce0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 113 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c20 : fetch_word segs (at_ rb 0x4bcec) = Some W_4bce4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 114 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c24 : fetch_word segs (at_ rb 0x4bcf0) = Some W_4bce8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 115 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c28 : fetch_word segs (at_ rb 0x4bcf4) = Some W_4bcec.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 116 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c2c : fetch_word segs (at_ rb 0x4bcf8) = Some W_4bcf0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 117 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c30 : fetch_word segs (at_ rb 0x4bcfc) = Some W_4bcf4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 118 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c34 : fetch_word segs (at_ rb 0x4bd00) = Some W_4bcf8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 119 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c38 : fetch_word segs (at_ rb 0x4bd04) = Some W_4bcfc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 120 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c3c : fetch_word segs (at_ rb 0x4bd08) = Some W_4bd00.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 121 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c40 : fetch_word segs (at_ rb 0x4bd0c) = Some W_4bd04.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 122 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c44 : fetch_word segs (at_ rb 0x4bd10) = Some W_4bd08.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 123 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c48 : fetch_word segs (at_ rb 0x4bd14) = Some W_4bd0c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 124 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c4c : fetch_word segs (at_ rb 0x4bd18) = Some W_4bd10.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 125 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c50 : fetch_word segs (at_ rb 0x4bd1c) = Some W_4bd14.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 126 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c54 : fetch_word segs (at_ rb 0x4bd20) = Some W_4bd18.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 127 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c58 : fetch_word segs (at_ rb 0x4bd24) = Some W_4bd1c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 128 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c5c : fetch_word segs (at_ rb 0x4bd28) = Some W_4bd20.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 129 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c60 : fetch_word segs (at_ rb 0x4bd2c) = Some W_4bd24.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 130 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c64 : fetch_word segs (at_ rb 0x4bd30) = Some W_4bd28.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 131 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c68 : fetch_word segs (at_ rb 0x4bd34) = Some W_4bd2c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 132 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c6c : fetch_word segs (at_ rb 0x4bd38) = Some W_4bd30.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 133 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c70 : fetch_word segs (at_ rb 0x4bd3c) = Some W_4bd34.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 134 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c74 : fetch_word segs (at_ rb 0x4bd40) = Some W_4bd38.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 135 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66c78 : fetch_word segs (at_ rb 0x4bd44) = Some W_4bd3c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 136 _ HAL eq_refl). Qed.





   (* [comment removed for export] *)
  Lemma I66c9c : fetch_word segs (at_ rb 0x4bd68) = Some W_4bd60.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 145 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ca0 : fetch_word segs (at_ rb 0x4bd6c) = Some W_4bd64.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 146 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ca4 : fetch_word segs (at_ rb 0x4bd70) = Some W_4bd68.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 147 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66ca8 : fetch_word segs (at_ rb 0x4bd74) = Some W_4bd6c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 148 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66cac : fetch_word segs (at_ rb 0x4bd78) = Some W_4bd70.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 149 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I66cb0 : fetch_word segs (at_ rb 0x4bd7c) = Some W_4bd74.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4bb24 al_words 150 _ HAL eq_refl). Qed.
















   (* [comment removed for export] *)


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp stk : word) (n : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 n.
  Hypothesis H11 : getr regs 11 = stk.
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  (* [comment removed for export] *)
  Variable MAG : word.
  Hypothesis Rinited : rdn segs mem (Z_to_bv 64 (am_g_inited t)) 1 = Some [Z_to_bv 8 1].
  Hypothesis Rrss : rdn segs mem (Z_to_bv 64 (am_g_rss t)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rmag : rdn segs mem (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw).
  Hypothesis Rtbl2 : rdn segs mem (at_ (am_tbl2 t) 4) 1 = Some [Z_to_bv 8 3].     (* [comment removed for export] *)
  Hypothesis Rt16 : rdn segs mem (at_ (am_tbl t) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis Rt2048 : rdn segs mem (at_ (am_tbl t) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis Rminrz : rdn segs mem (at_ INST 3624) 2 = Some (LE2 16).
  Hypothesis Rmaxrz : rdn segs mem (at_ INST 3626) 2 = Some (LE2 2048).
  Hypothesis Rmaxsz : rdn segs mem (at_ INST 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-160)) 160 = true.
  (* [comment removed for export] *)
  Hypothesis G0 : (0 <= am_g_inited t < 2 ^ 32)%Z /\ (0 <= am_g_rss t < 2 ^ 32)%Z /\ (0 <= am_g_magic t /\ am_g_magic t + 8 <= 2 ^ 32)%Z
            /\ (U (am_tbl2 t) + 64 <= 2 ^ 32)%Z /\ (U (am_tbl t) + 64 <= 2 ^ 32)%Z /\ (U INST + 4096 <= 2 ^ 32)%Z /\ (U stk <> 0)%Z.
  Hypothesis G1 : (2 ^ 32 + 160 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  #[local] Abbreviation CLX := (fun r => In r am_clobx).

  Lemma RETa : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d).
  Proof using TOK segs fx. intros d Hd Hdr. pose proof (ato_rb _ _ TOK) as [E1 E2]. pose proof (u64_range rb). apply ret_ok_at; [exact E1 | exact Hd | lia]. Qed.

  (* [comment removed for export] *)
  Definition am_m1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8)))
      (at_ sp (-24)) (LE8 (at_ rb 0x4baf4))) (at_ sp (-32)) (LE8 (getr regs 8))) (at_ sp (-40)) (LE8 (getr regs 9)))
      (at_ sp (-48)) (LE8 (getr regs 18))) (at_ sp (-56)) (LE8 (getr regs 19))) (at_ sp (-64)) (LE8 (getr regs 20)))
      (at_ sp (-72)) (LE8 (getr regs 21))) (at_ sp (-80)) (LE8 (getr regs 22))) (at_ sp (-88)) (LE8 (getr regs 23)))
      (at_ sp (-96)) (LE8 (getr regs 24))) (at_ sp (-104)) (LE8 (getr regs 25))) (at_ sp (-112)) (LE8 (getr regs 26)))
      (at_ sp (-120)) (LE8 (getr regs 27)).
  Lemma am_m1_outside : forall x : word, (U x < U sp - 120 \/ U sp <= U x)%Z -> am_m1 x = mem x.
  Proof using G1.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold am_m1 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.

  Ltac sokS Hs lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hstk (at_ sp (-160)) 160%nat ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma amA1a :
    exists r,
      msteps segs (mkst regs (at_ rb 0x4bac8) mem rom) (mkst r (at_ rb 0x74cac) am_m1 rom)
      /\ getr r 1 = at_ rb 0x4bb78 /\ getr r 2 = at_ sp (-144) /\ getr r 9 = Z_to_bv 64 1 /\ getr r 27 = Z_to_bv 64 1 /\ getr r 23 = stk
      /\ getr r 18 = Z_to_bv 64 8 /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = INST
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Hstk H11 H10 H2 H1 HAL HAM TOK.
    destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range stk) as Hstk'. pose proof (u64_range INST) as HI.
    destruct (ato_inst _ _ TOK) as [ix [IA IB]].
    wd_eexists. split.
    - an I669fc D_4bac0.                                   (* [comment removed for export] *)
      fsd8 I66a00 D_4bac4 (at_ sp (-8)).                   (* [comment removed for export] *)
      fsd8 I66a04 D_4bac8 (at_ sp (-16)).                  (* [comment removed for export] *)
      an I66a08 D_4bacc. an I66a0c D_4bad0.               (* [comment removed for export] *)
      eapply msteps_trans; [apply IA|]. zlit_at.            (* [comment removed for export] *)
      an I66a14 D_4bad8. an I66a18 D_4badc.               (* [comment removed for export] *)
      eapply msteps_trans; [apply IB; gres; reflexivity|]. zlit_at. rewrite ?regupd_regupd_same.   (* [comment removed for export] *)
      an I66a20 D_4bae4.                                   (* [comment removed for export] *)
      an I66a24 D_4bae8.                                   (* [comment removed for export] *)
      an I66a58 D_4bb1c.                                   (* [comment removed for export] *)
      fsd8 I66a5c D_4bb20 (at_ sp (-24)). fsd8 I66a60 D_4bb24 (at_ sp (-32)). fsd8 I66a64 D_4bb28 (at_ sp (-40)). fsd8 I66a68 D_4bb2c (at_ sp (-48)).
      fsd8 I66a6c D_4bb30 (at_ sp (-56)). fsd8 I66a70 D_4bb34 (at_ sp (-64)). fsd8 I66a74 D_4bb38 (at_ sp (-72)). fsd8 I66a78 D_4bb3c (at_ sp (-80)).
      fsd8 I66a7c D_4bb40 (at_ sp (-88)). fsd8 I66a80 D_4bb44 (at_ sp (-96)). fsd8 I66a84 D_4bb48 (at_ sp (-104)). fsd8 I66a88 D_4bb4c (at_ sp (-112)).
      fsd8 I66a8c D_4bb50 (at_ sp (-120)).
      change (wbytes _ _ _) with am_m1.
      an I66a90 D_4bb54. an I66a94 D_4bb58. an I66a98 D_4bb5c. an I66a9c D_4bb60. an I66aa0 D_4bb64. an I66aa4 D_4bb68.   (* [comment removed for export] *)
      an I66aa8 D_4bb6c.                                   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma v_sltu_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
    v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if (a <? b)%Z then 1 else 0).
  Proof using. intros a b Ha Hb. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end). unorm. destruct (a <? b)%Z; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition am_m2 : word -> option byte := wbytes (wbytes am_m1 (at_ sp (-136)) (LE8 (Z_to_bv 64 1))) (at_ sp (-128)) (LE8 (Z_to_bv 64 16)).
  Definition am_m3 : word -> option byte := wbytes (wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4bca8))) (at_ sp (-152)) (LE8 (at_ rb 0x4bcbc)).
  #[local] Hint Unfold am_m1 am_m2 am_m3 : asfr.
  Lemma am_m2_outside : forall x : word, (U x < U sp - 136 \/ U sp <= U x)%Z -> am_m2 x = mem x.
  Proof using G1.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold am_m2 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. apply am_m1_outside. lia.
  Qed.
  Lemma am_m3_outside : forall x : word, (U x < U sp - 152 \/ U sp <= U x)%Z -> am_m3 x = mem x.
  Proof using G1.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold am_m3 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. apply am_m2_outside. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma amA1b : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 1 -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bb78) M rom) (mkst r (at_ rb 0x7a974) M rom)
      /\ getr r 1 = at_ rb 0x4bb80 /\ (forall i : reg, In i [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HAL TOK.
    intros M r0 R10 AG0. wd_eexists. split.
    - ab_ft I66aac D_4bb70 ltac:(condz).                  (* [comment removed for export] *)
      an I66ab0 D_4bb74.                                   (* [comment removed for export] *)
      wd_refl.
    - post. 2: ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma amA1c : forall r0,
    getr r0 10 = Z_to_bv 64 0 -> getr r0 2 = at_ sp (-144) -> getr r0 23 = stk -> getr r0 18 = Z_to_bv 64 8 -> getr r0 22 = INST -> getr r0 9 = Z_to_bv 64 1 ->
    regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bb80) am_m1 rom) (mkst r (at_ rb 0x4bbbc) am_m2 rom)
      /\ getr r 10 = Z_to_bv 64 49 /\ getr r 8 = Z_to_bv 64 8 /\ getr r 25 = Z_to_bv 64 7 /\ getr r 26 = at_ INST 2047
      /\ (forall i : reg, In i [2; 9; 18; 19; 20; 21; 22; 23; 24; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Hstk Rtbl2 Rmag HAL TOK.
    intros r0 R10 R2 R23 R18 R22 R9 AG0.
    destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range stk) as Hstk'. pose proof (u64_range INST) as HI. pose proof (u64_range (am_tbl2 t)) as HT2.
    pose proof (ato_mag _ _ TOK) as GM. destruct (ato_tbl2 _ _ TOK) as [tx [TA TB]].
    assert (Rmag1 : rdn segs am_m1 (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rtb1 : rdn segs am_m1 (at_ (am_tbl2 t) 4) 1 = Some [Z_to_bv 8 3]).
    { rewrite <- Rtbl2. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply am_m1_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    wd_eexists. split.
    - ab_ft I66ab4 D_4bb78 ltac:(condz).                  (* [comment removed for export] *)
      ab_ft I66ab8 D_4bb7c ltac:(condz).                  (* [comment removed for export] *)
      an I66abc D_4bb80.                                   (* [comment removed for export] *)
      ab_tk I66ac0 D_4bb84 ltac:(condz).                  (* [comment removed for export] *)
      an I66afc D_4bbc0. an I66b00 D_4bbc4.               (* [comment removed for export] *)
      ab_tk I66b04 D_4bbc8 ltac:(condz).                  (* [comment removed for export] *)
      an I66b0c D_4bbd0. an I66b10 D_4bbd4.               (* [comment removed for export] *)
      ab_ft I66b14 D_4bbd8 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [eapply GM; exact Rmag1|]. zlit_at.   (* [comment removed for export] *)
      an I66b20 D_4bbe4. an I66b24 D_4bbe8.               (* [comment removed for export] *)
      an I66b28 D_4bbec.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply TA|]. zlit_at.            (* [comment removed for export] *)
      an I66b30 D_4bbf4.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply TB; gres; reflexivity|]. zlit_at. rewrite ?regupd_regupd_same.   (* [comment removed for export] *)
      av I66b38 D_4bbfc (at_ (am_tbl2 t) 4) ltac:(apply v_add_at; lia).   (* [comment removed for export] *)
      clbu I66b3c D_4bc00 (Z_to_bv 8 3) Rtbl2.            (* [comment removed for export] *)
      an I66b40 D_4bc04. an I66b44 D_4bc08. an I66b48 D_4bc0c.   (* [comment removed for export] *)
      an I66b4c D_4bc10.                                   (* [comment removed for export] *)
      ab_tk I66b50 D_4bc14 ltac:(condz).                  (* [comment removed for export] *)
      an I66ad0 D_4bb94. an I66ad4 D_4bb98. an I66ad8 D_4bb9c.   (* [comment removed for export] *)
      ab_ft I66adc D_4bba0 ltac:(condz).                  (* [comment removed for export] *)
      an I66ae0 D_4bba4.                                   (* [comment removed for export] *)
      an I66ae4 D_4bba8.                                   (* [comment removed for export] *)
      fsd I66ae8 D_4bbac (at_ sp (-136)).                  (* [comment removed for export] *)
      fsd I66aec D_4bbb0 (at_ sp (-128)).                  (* [comment removed for export] *)
      wd_refl.
    - post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA2 : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 49 -> getr r0 21 = Z_to_bv 64 n -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bbbc) M rom) (mkst r (at_ rb 0x4bc90) M rom)
      /\ getr r 19 = Z_to_bv 64 (rz_log n)
      /\ (forall i : reg, In i [2; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using Hn HAL TOK.
    intros M r0 R10 R21 AG0.
    Ltac fin := post; first [ (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
                            | intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi
                            | idtac ].
    destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E.
    - wd_eexists. split.
      { ab_ft I66af0 D_4bbb4 ltac:(condz). an I66af4 D_4bbb8. an I66af8 D_4bbbc. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I66af0 D_4bbb4 ltac:(condz). an I66b58 D_4bc1c. ab_ft I66b5c D_4bc20 ltac:(condz). an I66b60 D_4bc24. an I66b64 D_4bc28. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I66af0 D_4bbb4 ltac:(condz). an I66b58 D_4bc1c. ab_tk I66b5c D_4bc20 ltac:(condz).
      an I66b68 D_4bc2c. ab_ft I66b6c D_4bc30 ltac:(condz). an I66b70 D_4bc34. an I66b74 D_4bc38. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I66af0 D_4bbb4 ltac:(condz). an I66b58 D_4bc1c. ab_tk I66b5c D_4bc20 ltac:(condz).
      an I66b68 D_4bc2c. ab_tk I66b6c D_4bc30 ltac:(condz).
      an I66b78 D_4bc3c. an I66b7c D_4bc40. ab_ft I66b80 D_4bc44 ltac:(condz). an I66b84 D_4bc48. an I66b88 D_4bc4c. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I66af0 D_4bbb4 ltac:(condz). an I66b58 D_4bc1c. ab_tk I66b5c D_4bc20 ltac:(condz).
      an I66b68 D_4bc2c. ab_tk I66b6c D_4bc30 ltac:(condz).
      an I66b78 D_4bc3c. an I66b7c D_4bc40. ab_tk I66b80 D_4bc44 ltac:(condz).
      an I66b8c D_4bc50. an I66b90 D_4bc54. ab_ft I66b94 D_4bc58 ltac:(condz). an I66b98 D_4bc5c. an I66b9c D_4bc60. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I66af0 D_4bbb4 ltac:(condz). an I66b58 D_4bc1c. ab_tk I66b5c D_4bc20 ltac:(condz).
      an I66b68 D_4bc2c. ab_tk I66b6c D_4bc30 ltac:(condz).
      an I66b78 D_4bc3c. an I66b7c D_4bc40. ab_tk I66b80 D_4bc44 ltac:(condz).
      an I66b8c D_4bc50. an I66b90 D_4bc54. ab_tk I66b94 D_4bc58 ltac:(condz).
      an I66ba0 D_4bc64. an I66ba4 D_4bc68. ab_ft I66ba8 D_4bc6c ltac:(condz). an I66bac D_4bc70. an I66bb0 D_4bc74. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I66af0 D_4bbb4 ltac:(condz). an I66b58 D_4bc1c. ab_tk I66b5c D_4bc20 ltac:(condz).
      an I66b68 D_4bc2c. ab_tk I66b6c D_4bc30 ltac:(condz).
      an I66b78 D_4bc3c. an I66b7c D_4bc40. ab_tk I66b80 D_4bc44 ltac:(condz).
      an I66b8c D_4bc50. an I66b90 D_4bc54. ab_tk I66b94 D_4bc58 ltac:(condz).
      an I66ba0 D_4bc64. an I66ba4 D_4bc68. ab_tk I66ba8 D_4bc6c ltac:(condz).
      an I66bb4 D_4bc78. an I66bb8 D_4bc7c. an I66bbc D_4bc80. rewrite v_sltu_lit by lia. replace (n <? 64513)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      an I66bc0 D_4bc84. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I66af0 D_4bbb4 ltac:(condz). an I66b58 D_4bc1c. ab_tk I66b5c D_4bc20 ltac:(condz).
      an I66b68 D_4bc2c. ab_tk I66b6c D_4bc30 ltac:(condz).
      an I66b78 D_4bc3c. an I66b7c D_4bc40. ab_tk I66b80 D_4bc44 ltac:(condz).
      an I66b8c D_4bc50. an I66b90 D_4bc54. ab_tk I66b94 D_4bc58 ltac:(condz).
      an I66ba0 D_4bc64. an I66ba4 D_4bc68. ab_tk I66ba8 D_4bc6c ltac:(condz).
      an I66bb4 D_4bc78. an I66bb8 D_4bc7c. an I66bbc D_4bc80. rewrite v_sltu_lit by lia. replace (n <? 64513)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      an I66bc0 D_4bc84. wd_refl. }
      fin.
  Qed.

  (* [comment removed for export] *)
  Lemma v_sllw_16 : forall k, (0 <= k <= 7)%Z -> v_sllw (Z_to_bv 64 16) (Z_to_bv 64 k) = Z_to_bv 64 (16 * 2 ^ k).
  Proof using.
    intros k Hk. (lazymatch goal with |- ?G => let G' := eval unfold v_sllw in G in change_no_check G' end). f_equal. unorm. rewrite (Z.mod_small k 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    assert (2 ^ k <= 2 ^ 7)%Z by (apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ k)%Z by (apply Z.pow_pos_nonneg; lia).
    apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. cbn in H. lia.
  Qed.
  Lemma land_m8 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x (2 ^ 64 - 8) = (x - x mod 8)%Z.
  Proof using.
    intros x Hx. apply Z.bits_inj'. intros k Hk.
    rewrite Z.land_spec.
    assert (Em : (2 ^ 64 - 8)%Z = Z.shiftl (2 ^ 61 - 1) 3) by reflexivity. rewrite Em.
    assert (Ex : (x - x mod 8)%Z = Z.shiftl (x / 2 ^ 3) 3).
    { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z. pose proof (Z.div_mod x 8). lia. }
    rewrite Ex.
    destruct (Z.lt_ge_cases k 3) as [Hl|Hg].
    - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite !Z.shiftl_spec_high by lia.
      destruct (Z.lt_ge_cases k 64) as [Hl2|Hg2].
      + assert (Ht : Z.testbit (2 ^ 61 - 1) (k - 3) = true).
        { replace (2 ^ 61 - 1)%Z with (Z.ones 61) by reflexivity. apply Z.ones_spec_low. lia. }
        rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
      + rewrite (testbit_high 64 x k) by lia.
        rewrite (testbit_high 61 (x / 2 ^ 3) (k - 3)); [reflexivity | lia | | lia].
        change (2 ^ 3)%Z with 8%Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma rounded_val : forall m, (8 <= m < 2 ^ 62)%Z -> Z.land (m + 7) (2 ^ 64 - 8) = RoundUp m 8.
  Proof using.
    intros m Hm. rewrite land_m8 by lia. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (m + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (m + 8 - 1) 8 ltac:(lia)).
    replace (m + 7)%Z with (m + 8 - 1)%Z by lia. lia.
  Qed.

  Ltac clh F D z Hr :=
    chain_step; [reflexivity
      | eapply step_lh with (bs := LE2 z) (v := Z_to_bv 64 z);
        [exact F | reflexivity | exact D | rd_addr Hr | vm_compute; reflexivity]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma amA3a : forall r0,
    getr r0 26 = at_ INST 2047 -> getr r0 2 = at_ sp (-144) -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bc90) am_m2 rom) (mkst r (at_ rb 0x51144) am_m2 rom)
      /\ getr r 1 = at_ rb 0x4bca8 /\ getr r 10 = Z_to_bv 64 16 /\ getr r 20 = Z_to_bv 64 65536 /\ getr r 24 = Z_to_bv 64 65535
      /\ (forall i : reg, In i [2; 8; 9; 18; 19; 21; 22; 23; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Rminrz stk HAL TOK.
    intros r0 R26 R2 AG0. destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI.
    wd_eexists. split.
    { clh I66bc4 D_4bc88 16%Z Rminrz.                      (* [comment removed for export] *)
      afence I66bc8 D_4bc8c.
      an I66bcc D_4bc90. an I66bd0 D_4bc94.               (* [comment removed for export] *)
      an I66bd4 D_4bc98.                                   (* [comment removed for export] *)
      an I66bd8 D_4bc9c.                                   (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA3b : forall r0,
    getr r0 10 = Z_to_bv 64 0 -> getr r0 26 = at_ INST 2047 -> getr r0 2 = at_ sp (-144) -> getr r0 24 = Z_to_bv 64 65535 -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bca8) (wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4bca8))) rom)
                         (mkst r (at_ rb 0x51144) (wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4bca8))) rom)
      /\ getr r 1 = at_ rb 0x4bcbc /\ getr r 10 = Z_to_bv 64 2048 /\ getr r 9 = Z_to_bv 64 0
      /\ (forall i : reg, In i [2; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Rmaxrz stk HAL TOK.
    intros r0 R10 R26 R2 R24 AG0. destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI.
    wd_eexists. split.
    { an I66bdc D_4bca0.                                     (* [comment removed for export] *)
      clh I66be0 D_4bca4 2048%Z Rmaxrz.                     (* [comment removed for export] *)
      afence I66be4 D_4bca8.
      an I66be8 D_4bcac.                                     (* [comment removed for export] *)
      an I66bec D_4bcb0.                                     (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA3c : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 7 -> getr r0 9 = Z_to_bv 64 0 -> getr r0 19 = Z_to_bv 64 (rz_log n) -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bcbc) M rom) (mkst r (at_ rb 0x4bcc8) M rom)
      /\ getr r 19 = Z_to_bv 64 (rz_log n) /\ getr r 10 = Z_to_bv 64 7 /\ getr r 9 = Z_to_bv 64 0
      /\ (forall i : reg, In i [2; 8; 18; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using Hn HAL TOK.
    intros M r0 R10 R9 R19 AG0.
    destruct (rz_log_cases n ltac:(lia)) as [[C E]|REST].
    - rewrite E in *. wd_eexists. split.
      { ab_ft I66bf0 D_4bcb4 ltac:(condz).                 (* [comment removed for export] *)
        an I66bf4 D_4bcb8.                                  (* [comment removed for export] *)
        ab_ft I66bf8 D_4bcbc ltac:(condz).                 (* [comment removed for export] *)
        wd_refl. }
      post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac
           end.
    - assert (HR : (1 <= rz_log n <= 6)%Z) by lia.
      wd_eexists. split.
      { ab_tk I66bf0 D_4bcb4 ltac:(condz).                 (* [comment removed for export] *)
        ab_tk I66c9c D_4bd60 ltac:(condz).                 (* [comment removed for export] *)
        wd_refl. }
      post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA4 : forall r0,
    getr r0 19 = Z_to_bv 64 (rz_log n) -> getr r0 21 = Z_to_bv 64 n -> getr r0 8 = Z_to_bv 64 8 -> getr r0 18 = Z_to_bv 64 8 ->
    getr r0 20 = Z_to_bv 64 65536 -> getr r0 26 = at_ INST 2047 -> getr r0 2 = at_ sp (-144) -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bcc8) am_m3 rom) (mkst r (at_ rb 0x4bda4) am_m3 rom)
      /\ getr r 8 = Z_to_bv 64 1 /\ getr r 9 = Z_to_bv 64 n /\ getr r 19 = Z_to_bv 64 (needed n) /\ getr r 20 = Z_to_bv 64 (rz n)
      /\ getr r 24 = Z_to_bv 64 18446744073709551608
      /\ (forall i : reg, In i [2; 18; 21; 22; 23; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Rmaxsz Hn stk HAL TOK.
    intros r0 R19 R21 R8 R18 R20 R26 R2 AG0. destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI. pose proof (rz_log_range n) as HRL.
    assert (HP : (1 <= rz_log n <= 7 \/ rz_log n = 0)%Z) by lia.
    assert (Hrz : (rz n = 16 * 2 ^ rz_log n)%Z) by reflexivity.
    assert (Hrz2 : (16 <= rz n <= 1024)%Z).
    { rewrite Hrz. destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (Hrd : (rounded n = RoundUp (Z.max n 8) 8)%Z) by reflexivity.
    assert (Hrd2 : (Z.max n 8 <= rounded n <= Z.max n 8 + 7 /\ rounded n mod 8 = 0)%Z).
    { rewrite Hrd. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
    assert (Hprim : (needed n <= 65536)%Z).
    { pose proof (AsArith3.is_primary_iff n ltac:(lia)) as X. destruct X as [_ X]. specialize (X ltac:(lia)). unfold is_primary in X. apply Z.leb_le. exact X. }
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps segs (mkst r0 (at_ rb 0x4bcc8) am_m3 rom) (mkst r1 (at_ rb 0x4bcd8) am_m3 rom)
                 /\ getr r1 10 = Z_to_bv 64 (Z.max n 8) /\ (forall i : reg, In i [2; 8; 18; 19; 20; 21; 22; 23; 25; 26; 27] -> getr r1 i = getr r0 i)
                 /\ regs_agree CLX regs r1).
    { destruct (Z.lt_ge_cases 8 n) as [Hn8|Hn8].
      - rewrite Z.max_l by lia. wd_eexists. split.
        { an I66bfc D_4bcc0. an I66c00 D_4bcc4. ab_tk I66c04 D_4bcc8 ltac:(condz). wd_refl. }
        post. all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac end.
      - rewrite Z.max_r by lia. wd_eexists. split.
        { an I66bfc D_4bcc0. an I66c00 D_4bcc4. ab_ft I66c04 D_4bcc8 ltac:(condz). an I66c08 D_4bccc. wd_refl. }
        post. all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac end. }
    destruct W1 as (r1 & RUN1 & A10 & AK & AG1).
    assert (A8 : getr r1 8 = Z_to_bv 64 8) by (rewrite (AK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R8).
    assert (A18 : getr r1 18 = Z_to_bv 64 8) by (rewrite (AK 18) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R18).
    assert (A19 : getr r1 19 = Z_to_bv 64 (rz_log n)) by (rewrite (AK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R19).
    assert (A20 : getr r1 20 = Z_to_bv 64 65536) by (rewrite (AK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R20).
    assert (A21 : getr r1 21 = Z_to_bv 64 n) by (rewrite (AK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R21).
    assert (A26 : getr r1 26 = at_ INST 2047) by (rewrite (AK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R26).
    set (m := Z.max n 8) in *.
    eapply (runs_trans segs _ (fun r => mkst r (at_ rb 0x4bcd8) am_m3 rom) (fun r => r = r1)); [exists r1; split; [exact RUN1 | reflexivity] |].
    intros r1' ->.
    wd_eexists. split.
    { av I66c0c D_4bcd0 (Z_to_bv 64 (m + 8)) ltac:(valz).   (* [comment removed for export] *)
      an I66c10 D_4bcd4.                                      (* [comment removed for export] *)
      an I66c14 D_4bcd8.                                      (* [comment removed for export] *)
      av I66c18 D_4bcdc (Z_to_bv 64 (m + 7)) ltac:(valz).    (* [comment removed for export] *)
      an I66c1c D_4bce0.                                      (* [comment removed for export] *)
      an I66c20 D_4bce4.                                      (* [comment removed for export] *)
      match goal with |- context [v_and ?x ?y] => replace (v_and x y) with (Z_to_bv 64 (rounded n)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; rewrite Hrd; symmetry; apply rounded_val; lia) end.
      an I66c24 D_4bce8.                                      (* [comment removed for export] *)
      av I66c28 D_4bcec (Z_to_bv 64 (rounded n)) ltac:(valz).   (* [comment removed for export] *)
      av I66c2c D_4bcf0 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; replace (rounded n mod 8)%Z with 0%Z by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft I66c30 D_4bcf4 ltac:(condz).                    (* [comment removed for export] *)
      an I66c34 D_4bcf8.                                      (* [comment removed for export] *)
      av I66c38 D_4bcfc (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sltiu in G in change_no_check G' end); unorm; change (bv_wrap 64 1) with 1%Z; replace (n <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).   (* [comment removed for export] *)
      an I66c3c D_4bd00.                                      (* [comment removed for export] *)
      an I66c40 D_4bd04. rewrite (v_sllw_16 (rz_log n)) by lia. rewrite <- Hrz.   (* [comment removed for export] *)
      an I66c44 D_4bd08.                                      (* [comment removed for export] *)
      av I66c48 D_4bd0c (Z_to_bv 64 n) ltac:(valz).           (* [comment removed for export] *)
      an I66c4c D_4bd10.                                      (* [comment removed for export] *)
      av I66c50 D_4bd14 (Z_to_bv 64 (needed n)) ltac:(rewrite Hnd; valz).   (* [comment removed for export] *)
      an I66c54 D_4bd18. rewrite (v_sltu_lit (needed n) 65537) by lia. replace (needed n <? 65537)%Z with true by (symmetry; apply Z.ltb_lt; lia).   (* [comment removed for export] *)
      an I66c58 D_4bd1c.                                      (* [comment removed for export] *)
      an I66c5c D_4bd20.                                      (* [comment removed for export] *)
      an I66c60 D_4bd24.                                      (* [comment removed for export] *)
      all: try (match goal with |- context [v_and (Z_to_bv 64 0) ?y] => replace (v_and (Z_to_bv 64 0) y) with (Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; rewrite Z.land_0_l; reflexivity) end).
      an I66c64 D_4bd28.                                      (* [comment removed for export] *)
      av I66c68 D_4bd2c (Z_to_bv 64 (needed n)) ltac:(valz).   (* [comment removed for export] *)
      ab_ft I66c6c D_4bd30 ltac:(condz).                    (* [comment removed for export] *)
      ab_ft I66c70 D_4bd34 ltac:(condz).                    (* [comment removed for export] *)
      cld8 I66c74 D_4bd38 (Z_to_bv 64 (2 ^ 40)) Rmaxsz.      (* [comment removed for export] *)
      ab_tk I66c78 D_4bd3c ltac:(condz).                    (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; apply AK; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.

  (* [comment removed for export] *)
  Theorem amA_run :
    exists r,
      msteps segs (mkst regs (at_ rb 0x4bac8) mem rom) (mkst r (at_ rb 0x4bda4) am_m3 rom)
      /\ getr r 2 = at_ sp (-144) /\ getr r 8 = Z_to_bv 64 1 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = Z_to_bv 64 8
      /\ getr r 19 = Z_to_bv 64 (needed n) /\ getr r 20 = Z_to_bv 64 (rz n) /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = INST
      /\ getr r 23 = stk /\ getr r 24 = Z_to_bv 64 18446744073709551608 /\ getr r 25 = Z_to_bv 64 7 /\ getr r 26 = at_ INST 2047
      /\ getr r 27 = Z_to_bv 64 1
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Hstk Rmaxsz Rmaxrz Rminrz Rt2048 Rt16 Rtbl2 Rmag Rrss Rinited Hn H11 H10 H2 H1 HAL HAM TOK.
    pose proof G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). pose proof G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI. pose proof (u64_range (am_tbl t)) as HT.
    pose proof TOK as TOK'. destruct TOK' as [_ _ _ _ _ AIN AINB RSS RSSB RZL RZM RZT RB].
    Ltac via AG r H := let T := fresh in pose proof (AG r ltac:(notin_list)) as T; rewrite H in T; exact T.
    Ltac viaK K AG r H := rewrite (K r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); via AG r H.
    (* [comment removed for export] *)
    destruct amA1a as (r1 & RUN1 & A1 & A2 & A9 & A27 & A23 & A18 & A21 & A22 & AG1).
    (* [comment removed for export] *)
    destruct (ain_run segs rb (am_g_inited t) AIN AINB am_m1 rom r1 (at_ rb 0x4bb78)) as (r2 & RUN2 & B10 & AG2).
    { rewrite <- Rinited. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    { apply RETa; [reflexivity | lia]. }
    { exact A1. }
    (* [comment removed for export] *)
    destruct (amA1b am_m1 r2 B10 ltac:(eapply regs_agree_trans; [exact AG1 | regs_agree_weaken AG2])) as (r3 & RUN3 & C1 & CK & AG3).
    (* [comment removed for export] *)
    destruct (rss_run segs rb (am_g_rss t) RSS RSSB am_m1 rom r3 (at_ rb 0x4bb80)) as (r4 & RUN4 & D10 & AG4).
    { rewrite <- Rrss. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    { apply RETa; [reflexivity | lia]. }
    { exact C1. }
    (* [comment removed for export] *)
    destruct (amA1c r4 D10) as (r5 & RUN5 & E10 & E8 & E25 & E26 & EK & AG5).
    { rewrite (AG4 2) by notin_list. viaK CK AG2 (2:reg) A2. }
    { rewrite (AG4 23) by notin_list. viaK CK AG2 (23:reg) A23. }
    { rewrite (AG4 18) by notin_list. viaK CK AG2 (18:reg) A18. }
    { rewrite (AG4 22) by notin_list. viaK CK AG2 (22:reg) A22. }
    { rewrite (AG4 9) by notin_list. viaK CK AG2 (9:reg) A9. }
    { eapply regs_agree_trans; [exact AG3 | regs_agree_weaken AG4]. }
    assert (E21 : getr r5 21 = Z_to_bv 64 n). { rewrite (EK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG4 21) by notin_list. viaK CK AG2 (21:reg) A21. }
    Ltac thr5 EK AG4 CK AG2 r A := rewrite (EK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG4 r) by notin_list; rewrite (CK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); let T := fresh in pose proof (AG2 r ltac:(notin_list)) as T; rewrite A in T; exact T.
    assert (E2 : getr r5 2 = at_ sp (-144)) by (thr5 EK AG4 CK AG2 (2:reg) A2).
    assert (E9 : getr r5 9 = Z_to_bv 64 1) by (thr5 EK AG4 CK AG2 (9:reg) A9).
    assert (E18 : getr r5 18 = Z_to_bv 64 8) by (thr5 EK AG4 CK AG2 (18:reg) A18).
    assert (E22 : getr r5 22 = INST) by (thr5 EK AG4 CK AG2 (22:reg) A22).
    assert (E23 : getr r5 23 = stk) by (thr5 EK AG4 CK AG2 (23:reg) A23).
    assert (E27 : getr r5 27 = Z_to_bv 64 1) by (thr5 EK AG4 CK AG2 (27:reg) A27).
    (* [comment removed for export] *)
    destruct (amA2 am_m2 r5 E10 E21 AG5) as (r6 & RUN6 & F19 & FK & AG6).
    (* [comment removed for export] *)
    destruct (amA3a r6 ltac:(rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E26) ltac:(rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) AG6) as (r7 & RUN7 & G1' & G10 & G20 & G24 & GK & AG7).
    (* [comment removed for export] *)
    assert (Rm2 : rdn segs am_m2 (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m2_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rt2 : rdn segs am_m2 (at_ (am_tbl t) 8) 1 = Some [Z_to_bv 8 4]).
    { rewrite <- Rt16. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply am_m2_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOK2 : store_ok segs am_m2 (at_ (at_ sp (-144)) (-8)) 8 = true).
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval unfold am_m2, am_m1 in G in change_no_check G' end). repeat (eapply store_ok_mono; [apply wbytes_grows|]).
      eapply (store_ok_sub segs mem (at_ sp (-160)) _ 160); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (rzl16_run segs rb RB (am_g_magic t) (am_tbl t) RZL RZM RZT am_m2 rom r7 (at_ rb 0x4bca8) (at_ sp (-144)) Rm2 ltac:(lia) SOK2
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(right; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ])
                (RETa 0x4bca8 eq_refl ltac:(lia)) G1' ltac:(rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) Rt2 G10)
      as (r8 & RUN8 & H10' & AG8).
    unfold rzM1 in RUN8. rewrite at_at in RUN8. cbn [Z.add] in RUN8.
    (* [comment removed for export] *)
    destruct (amA3b r8 H10') as (r9 & RUN9 & I1 & I10 & I9 & IK & AG9).
    { rewrite (AG8 26) by notin_list. rewrite (GK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E26. }
    { rewrite (AG8 2) by notin_list. rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E2. }
    { rewrite (AG8 24) by notin_list. exact G24. }
    { eapply regs_agree_trans; [exact AG7 | regs_agree_weaken AG8]. }
    (* [comment removed for export] *)
    set (M3a := wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4bca8))) in *.
    assert (HM3a : forall x : word, (U x < U sp - 152 \/ U sp <= U x)%Z -> M3a x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M3a in G in change_no_check G' end). rewrite wbytes_outside; [apply am_m2_outside; lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rm3 : rdn segs M3a (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply HM3a; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rt3 : rdn segs M3a (at_ (am_tbl t) 49) 1 = Some [Z_to_bv 8 11]).
    { rewrite <- Rt2048. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM3a; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOK3 : store_ok segs M3a (at_ (at_ sp (-144)) (-8)) 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold M3a in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOK2]. }
    destruct (rzl2048_run segs rb RB (am_g_magic t) (am_tbl t) RZL RZM RZT M3a rom r9 (at_ rb 0x4bcbc) (at_ sp (-144)) Rm3 ltac:(lia) SOK3
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(right; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ])
                (RETa 0x4bcbc eq_refl ltac:(lia)) I1 ltac:(rewrite (IK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG8 2) by notin_list; rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) Rt3 I10)
      as (r10 & RUN10 & J10 & AG10).
    unfold rzM1 in RUN10. rewrite at_at in RUN10. cbn [Z.add] in RUN10.
    change (wbytes M3a (at_ sp (-152)) (LE8 (at_ rb 0x4bcbc))) with am_m3 in RUN10.
    (* [comment removed for export] *)
    destruct (amA3c am_m3 r10 J10) as (r11 & RUN11 & K19 & K10 & K9 & KK & AG11).
    { rewrite (AG10 9) by notin_list. exact I9. }
    { rewrite (AG10 19) by notin_list. rewrite (IK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 19) by notin_list. rewrite (GK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact F19. }
    { eapply regs_agree_trans; [exact AG9 | regs_agree_weaken AG10]. }
    (* [comment removed for export] *)
    Ltac thrB KK AG10 IK AG8 GK FK r H := rewrite (KK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 r) by notin_list; rewrite (IK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]);
                                        rewrite (AG8 r) by notin_list; rewrite (GK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H.
    destruct (amA4 r11 K19) as (r12 & RUN12 & L8 & L9 & L19 & L20 & L24 & LK & AG12).
    { thrB KK AG10 IK AG8 GK FK (21:reg) E21. }
    { rewrite (KK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 8) by notin_list. rewrite (IK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 8) by notin_list. rewrite (GK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E8. }
    { thrB KK AG10 IK AG8 GK FK (18:reg) E18. }
    { rewrite (KK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 20) by notin_list. rewrite (IK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 20) by notin_list. exact G20. }
    { rewrite (KK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 26) by notin_list. rewrite (IK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 26) by notin_list. rewrite (GK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E26. }
    { thrB KK AG10 IK AG8 GK FK (2:reg) E2. }
    { eapply regs_agree_trans; [exact AG11 | idtac]. apply regs_agree_refl. }
    exists r12. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
      eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11 | exact RUN12]. }
    Ltac thrC LK KK AG10 IK AG8 GK FK r H := rewrite (LK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (KK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 r) by notin_list; rewrite (IK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]);
                                        rewrite (AG8 r) by notin_list; rewrite (GK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H.
    split; [thrC LK KK AG10 IK AG8 GK FK (2:reg) E2|]. split; [exact L8|]. split; [exact L9|]. split; [thrC LK KK AG10 IK AG8 GK FK (18:reg) E18|].
    split; [exact L19|]. split; [exact L20|]. split; [thrC LK KK AG10 IK AG8 GK FK (21:reg) E21|]. split; [thrC LK KK AG10 IK AG8 GK FK (22:reg) E22|].
    split; [thrC LK KK AG10 IK AG8 GK FK (23:reg) E23|]. split; [exact L24|].
    split; [rewrite (LK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (KK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 25) by notin_list; rewrite (IK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG8 25) by notin_list; rewrite (GK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E25|].
    split; [thrC LK KK AG10 IK AG8 GK FK (26:reg) E26|].
    split; [thrC LK KK AG10 IK AG8 GK FK (27:reg) E27|].
    exact AG12.
  Qed.
End AM.
End FPGen1.
