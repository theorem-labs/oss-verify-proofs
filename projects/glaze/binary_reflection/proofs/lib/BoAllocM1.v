(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.InstrEnc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Bo_code_75eb4_76b0c.
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
Definition W_7662c : bv 32 := @BV 32 0xff010113%Z I.

Lemma D_7662c : decode_any W_7662c = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 4080%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76630 : bv 32 := @BV 32 0x00113423%Z I.

Lemma D_76630 : decode_any W_76630 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 1%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76634 : bv 32 := @BV 32 0x00813023%Z I.

Lemma D_76634 : decode_any W_76634 = Some (Store SZ8 (@BV 5 2%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76638 : bv 32 := @BV 32 0x00099517%Z I.
Lemma F_76638 : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x76638%Z I : word) = Some W_76638.
Proof. vm_refl. Qed.
Lemma D_76638 : decode_any W_76638 = Some (Auipc (@BV 5 10%Z I) (@BV 20 153%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7663c : bv 32 := @BV 32 0x86050413%Z I.
Lemma F_7663c : fetch_word AsanUbsan.M.loaded_segments (@BV 64 0x7663c%Z I : word) = Some W_7663c.
Proof. vm_refl. Qed.
Lemma D_7663c : decode_any W_7663c = Some (OpImm ALU_ADD (@BV 5 8%Z I) (@BV 5 10%Z I) (@BV 12 2144%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76640 : bv 32 := @BV 32 0x00040583%Z I.

Lemma D_76640 : decode_any W_76640 = Some (Load SZ1 true (@BV 5 11%Z I) (@BV 5 8%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76644 : bv 32 := @BV 32 0x00100513%Z I.

Lemma D_76644 : decode_any W_76644 = Some (OpImm ALU_ADD (@BV 5 10%Z I) (@BV 5 0%Z I) (@BV 12 1%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76648 : bv 32 := @BV 32 0x0230000f%Z I.

Lemma D_76648 : decode_any W_76648 = Some (Fence (@BV 4 0%Z I) (@BV 4 2%Z I) (@BV 4 3%Z I) (@BV 5 0%Z I) (@BV 5 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7664c : bv 32 := @BV 32 0x00a59a63%Z I.

Lemma D_7664c : decode_any W_7664c = Some (Branch BC_NE (@BV 5 11%Z I) (@BV 5 10%Z I) (@BV 13 20%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76650 : bv 32 := @BV 32 0x00813083%Z I.

Lemma D_76650 : decode_any W_76650 = Some (Load SZ8 true (@BV 5 1%Z I) (@BV 5 2%Z I) (@BV 12 8%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76654 : bv 32 := @BV 32 0x00013403%Z I.

Lemma D_76654 : decode_any W_76654 = Some (Load SZ8 true (@BV 5 8%Z I) (@BV 5 2%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_76658 : bv 32 := @BV 32 0x01010113%Z I.

Lemma D_76658 : decode_any W_76658 = Some (OpImm ALU_ADD (@BV 5 2%Z I) (@BV 5 2%Z I) (@BV 12 16%Z I), 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7665c : bv 32 := @BV 32 0x00008067%Z I.

Lemma D_7665c : decode_any W_7665c = Some (Jalr (@BV 5 0%Z I) (@BV 5 1%Z I) (@BV 12 0%Z I), 4%Z).
Proof. vm_refl. Qed.








































































































































































































































































End Bo_code_75eb4_76b0c.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 Bo_code_75eb4_76b0c OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_76b0c_77514 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_8fc84_905f0.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Section FPGen0.
Context {fx : FPState}.
Definition gloadw (segs : list Segment) (base : word) (off : Z) (rd : reg) (g : Z) : Prop :=
  forall regs mem rom (z : Z), (0 <= z < 2 ^ 31)%Z ->
    rdn segs mem (Z_to_bv 64 g) 4 = Some (LE4 z) ->
    msteps segs (mkst regs (at_ base off) mem rom)
                (mkst (regupd regs rd (Z_to_bv 64 z)) (at_ base (off + 8)) mem rom).
End FPGen0.
Ltac gloadw_tac Fa Da Fl Dl :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  let z := fresh "z" in let Hz := fresh "Hz" in let Hrd := fresh "Hrd" in
  intros regs mem rom z Hz Hrd;
  lit_pc;
  (chain_step; [ reflexivity | eapply step_auipc; [exact Fa | reflexivity | exact Da] | step_simpl ]);
  gres; imm_norm; vals_lit;
  (chain_step;
   [ reflexivity
   | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 z)) (v := Z_to_bv 64 z);
     [exact Fl | reflexivity | exact Dl | gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact Hrd | apply bytes4_small; lia]
   | step_simpl ]);
  rewrite (v_lw_small z) by lia;
  close_refl.

Section FPGen1.
Context {fx : FPState}.

Definition mp_words : list (option (bv 32)) :=
  [Some W_6ef3c; Some W_6ef40; Some W_6ef44; Some W_6ef48; Some W_6ef4c; Some W_6ef50; Some W_6ef54; Some W_6ef58;
   Some W_6ef5c; Some W_6ef60; Some W_6ef64; Some W_6ef68; Some W_6ef6c; Some W_6ef70; Some W_6ef74; Some W_6ef78;
   Some W_6ef7c; Some W_6ef80; Some W_6ef84; Some W_6ef88; Some W_6ef8c; Some W_6ef90; Some W_6ef94; Some W_6ef98;
   Some W_6ef9c; Some W_6efa0; Some W_6efa4; Some W_6efa8; Some W_6efac; Some W_6efb0; Some W_6efb4; Some W_6efb8;
   Some W_6efbc; Some W_6efc0; Some W_6efc4; Some W_6efc8; Some W_6efcc; Some W_6efd0; Some W_6efd4; Some W_6efd8;
   Some W_6efdc; Some W_6efe0; Some W_6efe4; Some W_6efe8; Some W_6efec; Some W_6eff0; Some W_6eff4; Some W_6eff8;
   Some W_6effc; Some W_6f000; None; None; Some W_6f00c; Some W_6f010; Some W_6f014; Some W_6f018; Some W_6f01c;
   Some W_6f020; Some W_6f024; Some W_6f028; Some W_6f02c; Some W_6f030; Some W_6f034; Some W_6f038; Some W_6f03c;
   Some W_6f040; Some W_6f044; Some W_6f048; Some W_6f04c; Some W_6f050; Some W_6f054; Some W_6f058; Some W_6f05c;
   Some W_6f060; Some W_6f064; Some W_6f068; Some W_6f06c; Some W_6f070; Some W_6f074; Some W_6f078; Some W_6f07c;
   Some W_6f080; Some W_6f084; Some W_6f088; Some W_6f08c; Some W_6f090; Some W_6f094]%list.
Definition tai_words : list (option (bv 32)) :=
  [Some W_7662c; Some W_76630; Some W_76634; None; None; Some W_76640; Some W_76644; Some W_76648; Some W_7664c;
   Some W_76650; Some W_76654; Some W_76658; Some W_7665c]%list.
Definition gmc_words : list (option (bv 32)) :=
  [None; None; Some W_773bc; Some W_773c0]%list.
Definition gpc_words : list (option (bv 32)) :=
  [Some W_8fe74; Some W_8fe78]%list.

(* [comment removed for export] *)
Record mp_tab := MPT { mt_rb : word; mt_ui : ui_tab; mt_g_cf : Z; mt_a_inited : word; mt_g_mcs : Z }.
Record mp_tab_ok (segs : list Segment) (t : mp_tab) : Prop := MPTOK {
  mto_mp : code_ato segs (mt_rb t) 0x6ef3c mp_words;
  mto_tai : code_ato segs (mt_rb t) 0x7662c tai_words;
  mto_gmc : code_ato segs (mt_rb t) 0x773b4 gmc_words;
  mto_gpc : code_ato segs (mt_rb t) 0x8fe74 gpc_words;
  mto_gcf : gload segs (mt_rb t) 0x6f004 11 (mt_g_cf t);                 (* [comment removed for export] *)
  mto_ain : gaddr2 segs (mt_rb t) 0x76638 10 8 (mt_a_inited t);          (* [comment removed for export] *)
  mto_mcs : gloadw segs (mt_rb t) 0x773b4 10 (mt_g_mcs t);               (* [comment removed for export] *)
  mto_ui : ui_tab_ok segs (mt_ui t);
  mto_ui_rb : ut_rb (mt_ui t) = mt_rb t;
  mto_rb : (U (mt_rb t) mod 2 = 0)%Z /\ (U (mt_rb t) + 2 ^ 24 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition mp_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17].


(* [comment removed for export] *)
Record mpH (segs : list Segment) (t : mp_tab) (mem : word -> option byte) (S CF thr : word) (fb : byte) : Prop := MPH {
  mh_inited : rdn segs mem (mt_a_inited t) 1 = Some [Z_to_bv 8 1];
  mh_gcf : rdn segs mem (Z_to_bv 64 (mt_g_cf t)) 8 = Some (LE8 CF);
  mh_fast : rdn segs mem (at_ CF 34) 1 = Some [fb];
  mh_fast_nz : U fb <> 0%Z;
  mh_mcs : rdn segs mem (Z_to_bv 64 (mt_g_mcs t)) 4 = Some (LE4 30);
  mh_stk : store_ok segs mem (at_ S (-2272)) 2272 = true;
  (* [comment removed for export] *)
  mh_g0 : (U (mt_a_inited t) + 8 <= 2 ^ 32)%Z /\ (0 <= mt_g_cf t /\ mt_g_cf t + 8 <= 2 ^ 32)%Z /\ (U CF + 40 <= 2 ^ 32)%Z
          /\ (0 <= mt_g_mcs t /\ mt_g_mcs t + 8 <= 2 ^ 32)%Z;
  mh_g1 : (2 ^ 32 + 2272 <= U S)%Z /\ (U S + 16 <= 2 ^ 47)%Z /\ (U S mod 16 = 0)%Z;
  mh_g2 : (4096 <= U thr)%Z /\ (U thr + 4096 <= U S - 2272)%Z   (* [comment removed for export] *) }.

Section MP.
  Variable segs : list Segment.
  Variable t : mp_tab.
  Hypothesis TOK : mp_tab_ok segs t.
  #[local] Abbreviation rb := (mt_rb t).
  Let HMP : code_ato segs rb 0x6ef3c mp_words := mto_mp _ _ TOK.
  Let HTAI : code_ato segs rb 0x7662c tai_words := mto_tai _ _ TOK.
  Let HGMC : code_ato segs rb 0x773b4 gmc_words := mto_gmc _ _ TOK.
  Let HGPC : code_ato segs rb 0x8fe74 gpc_words := mto_gpc _ _ TOK.

  Lemma Iec260 : fetch_word segs (at_ rb 0x6ef3c) = Some W_6ef3c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 0 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec264 : fetch_word segs (at_ rb 0x6ef40) = Some W_6ef40.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 1 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec268 : fetch_word segs (at_ rb 0x6ef44) = Some W_6ef44.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 2 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec26c : fetch_word segs (at_ rb 0x6ef48) = Some W_6ef48.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 3 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec270 : fetch_word segs (at_ rb 0x6ef4c) = Some W_6ef4c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 4 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec274 : fetch_word segs (at_ rb 0x6ef50) = Some W_6ef50.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 5 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec278 : fetch_word segs (at_ rb 0x6ef54) = Some W_6ef54.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 6 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec27c : fetch_word segs (at_ rb 0x6ef58) = Some W_6ef58.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 7 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec280 : fetch_word segs (at_ rb 0x6ef5c) = Some W_6ef5c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 8 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec284 : fetch_word segs (at_ rb 0x6ef60) = Some W_6ef60.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 9 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec288 : fetch_word segs (at_ rb 0x6ef64) = Some W_6ef64.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 10 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec28c : fetch_word segs (at_ rb 0x6ef68) = Some W_6ef68.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 11 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec290 : fetch_word segs (at_ rb 0x6ef6c) = Some W_6ef6c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 12 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec294 : fetch_word segs (at_ rb 0x6ef70) = Some W_6ef70.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 13 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec298 : fetch_word segs (at_ rb 0x6ef74) = Some W_6ef74.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 14 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec29c : fetch_word segs (at_ rb 0x6ef78) = Some W_6ef78.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 15 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2a0 : fetch_word segs (at_ rb 0x6ef7c) = Some W_6ef7c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 16 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2a4 : fetch_word segs (at_ rb 0x6ef80) = Some W_6ef80.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 17 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2a8 : fetch_word segs (at_ rb 0x6ef84) = Some W_6ef84.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 18 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2ac : fetch_word segs (at_ rb 0x6ef88) = Some W_6ef88.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 19 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2b0 : fetch_word segs (at_ rb 0x6ef8c) = Some W_6ef8c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 20 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2b4 : fetch_word segs (at_ rb 0x6ef90) = Some W_6ef90.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 21 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2b8 : fetch_word segs (at_ rb 0x6ef94) = Some W_6ef94.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 22 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2bc : fetch_word segs (at_ rb 0x6ef98) = Some W_6ef98.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 23 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec2c0 : fetch_word segs (at_ rb 0x6ef9c) = Some W_6ef9c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 24 _ HMP eq_refl). Qed.























   (* [comment removed for export] *)
  Lemma Iec324 : fetch_word segs (at_ rb 0x6f000) = Some W_6f000.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 49 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec330 : fetch_word segs (at_ rb 0x6f00c) = Some W_6f00c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 52 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec334 : fetch_word segs (at_ rb 0x6f010) = Some W_6f010.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 53 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec338 : fetch_word segs (at_ rb 0x6f014) = Some W_6f014.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 54 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec33c : fetch_word segs (at_ rb 0x6f018) = Some W_6f018.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 55 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec340 : fetch_word segs (at_ rb 0x6f01c) = Some W_6f01c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 56 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec344 : fetch_word segs (at_ rb 0x6f020) = Some W_6f020.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 57 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec348 : fetch_word segs (at_ rb 0x6f024) = Some W_6f024.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 58 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec34c : fetch_word segs (at_ rb 0x6f028) = Some W_6f028.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 59 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec350 : fetch_word segs (at_ rb 0x6f02c) = Some W_6f02c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 60 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec354 : fetch_word segs (at_ rb 0x6f030) = Some W_6f030.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 61 _ HMP eq_refl). Qed.



   (* [comment removed for export] *)
  Lemma Iec368 : fetch_word segs (at_ rb 0x6f044) = Some W_6f044.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 66 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec36c : fetch_word segs (at_ rb 0x6f048) = Some W_6f048.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 67 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec370 : fetch_word segs (at_ rb 0x6f04c) = Some W_6f04c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 68 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec374 : fetch_word segs (at_ rb 0x6f050) = Some W_6f050.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 69 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec378 : fetch_word segs (at_ rb 0x6f054) = Some W_6f054.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 70 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec37c : fetch_word segs (at_ rb 0x6f058) = Some W_6f058.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 71 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec380 : fetch_word segs (at_ rb 0x6f05c) = Some W_6f05c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 72 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec384 : fetch_word segs (at_ rb 0x6f060) = Some W_6f060.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 73 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec388 : fetch_word segs (at_ rb 0x6f064) = Some W_6f064.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 74 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec38c : fetch_word segs (at_ rb 0x6f068) = Some W_6f068.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 75 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec390 : fetch_word segs (at_ rb 0x6f06c) = Some W_6f06c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 76 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec394 : fetch_word segs (at_ rb 0x6f070) = Some W_6f070.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 77 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec398 : fetch_word segs (at_ rb 0x6f074) = Some W_6f074.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 78 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec39c : fetch_word segs (at_ rb 0x6f078) = Some W_6f078.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 79 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec3a0 : fetch_word segs (at_ rb 0x6f07c) = Some W_6f07c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 80 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec3a4 : fetch_word segs (at_ rb 0x6f080) = Some W_6f080.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 81 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec3a8 : fetch_word segs (at_ rb 0x6f084) = Some W_6f084.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 82 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec3ac : fetch_word segs (at_ rb 0x6f088) = Some W_6f088.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 83 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec3b0 : fetch_word segs (at_ rb 0x6f08c) = Some W_6f08c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 84 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec3b4 : fetch_word segs (at_ rb 0x6f090) = Some W_6f090.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 85 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Iec3b8 : fetch_word segs (at_ rb 0x6f094) = Some W_6f094.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6ef3c mp_words 86 _ HMP eq_refl). Qed.   (* [comment removed for export] *)

  Lemma If7044 : fetch_word segs (at_ rb 0x7662c) = Some W_7662c.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 0 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7048 : fetch_word segs (at_ rb 0x76630) = Some W_76630.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 1 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If704c : fetch_word segs (at_ rb 0x76634) = Some W_76634.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 2 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7058 : fetch_word segs (at_ rb 0x76640) = Some W_76640.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 5 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If705c : fetch_word segs (at_ rb 0x76644) = Some W_76644.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 6 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7060 : fetch_word segs (at_ rb 0x76648) = Some W_76648.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 7 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7064 : fetch_word segs (at_ rb 0x7664c) = Some W_7664c.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 8 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7068 : fetch_word segs (at_ rb 0x76650) = Some W_76650.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 9 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If706c : fetch_word segs (at_ rb 0x76654) = Some W_76654.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 10 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7070 : fetch_word segs (at_ rb 0x76658) = Some W_76658.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 11 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7074 : fetch_word segs (at_ rb 0x7665c) = Some W_7665c.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x7662c tai_words 12 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)

  Lemma If7ca0 : fetch_word segs (at_ rb 0x773bc) = Some W_773bc.  Proof using HGMC TOK fx. exact (code_ato_get segs rb 0x773b4 gmc_words 2 _ HGMC eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If7ca4 : fetch_word segs (at_ rb 0x773c0) = Some W_773c0.  Proof using HGMC TOK fx. exact (code_ato_get segs rb 0x773b4 gmc_words 3 _ HGMC eq_refl). Qed.   (* [comment removed for export] *)

  Lemma I113e20 : fetch_word segs (at_ rb 0x8fe74) = Some W_8fe74.  Proof using HGPC TOK fx. exact (code_ato_get segs rb 0x8fe74 gpc_words 0 _ HGPC eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I113e24 : fetch_word segs (at_ rb 0x8fe78) = Some W_8fe78.  Proof using HGPC TOK fx. exact (code_ato_get segs rb 0x8fe74 gpc_words 1 _ HGPC eq_refl). Qed.   (* [comment removed for export] *)


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra S tp n CF thr top bot tsdp tctx P : word) (fb : byte).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = S.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H10 : getr regs 10 = n.
  Hypothesis MH : mpH segs t mem S CF thr fb.
  Hypothesis UH : uiH segs (mt_ui t) mem (at_ S (-2128)) (at_ S (-2128)) S thr P.
  Hypothesis GH : gctH segs (ut_gct (mt_ui t)) mem (at_ S (-2208)) tp tsdp tctx thr.
  Hypothesis SH : stkH segs mem thr top bot.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.

  #[local] Abbreviation CLX := (fun r => In r mp_clobx).

  Lemma RET : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d).
  Proof using TOK segs fx. intros d Hd Hdr. pose proof (mto_rb _ _ TOK) as [E1 E2]. pose proof (u64_range rb). apply ret_ok_at; [exact E1 | exact Hd | lia]. Qed.

  (* [comment removed for export] *)
  Definition mp_m1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ S (-8)) (LE8 ra)) (at_ S (-16)) (LE8 (getr regs 8))) (at_ S (-24)) (LE8 (getr regs 9)))
      (at_ S (-32)) (LE8 (getr regs 18))) (at_ S (-40)) (LE8 (getr regs 19))) (at_ S (-48)) (LE8 (getr regs 20)))
      (at_ S (-56)) (LE8 (getr regs 21)))
      (at_ S (-2136)) (LE8 (at_ rb 0x6ef70))) (at_ S (-2144)) (LE8 S))               (* [comment removed for export] *)
      (at_ S (-72)) (LE8 (Z_to_bv 64 0)))                                            (* [comment removed for export] *)
      (at_ S (-2128)) (LE8 (at_ S (-2112))))                                         (* [comment removed for export] *)
      (at_ S (-2120)) (LE8 (Z_to_bv 64 0)).                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mp_m2 : word -> option byte := wbytes mp_m1 (at_ S (-72)) (LE8 S).

  Lemma mp_m1_outside : forall x : word,
    (U x < U S - 2144)%Z \/ (U S - 2112 <= U x < U S - 72)%Z \/ (U S - 64 <= U x < U S - 56)%Z \/ (U S <= U x)%Z -> mp_m1 x = mem x.
  Proof using MH fb thr CF segs.
    intros x Hx. destruct MH as [_ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold mp_m1 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma mp_m2_outside : forall x : word,
    (U x < U S - 2144)%Z \/ (U S - 2112 <= U x < U S - 72)%Z \/ (U S - 64 <= U x < U S - 56)%Z \/ (U S <= U x)%Z -> mp_m2 x = mem x.
  Proof using MH fb thr CF segs.
    intros x Hx. destruct MH as [_ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold mp_m2 in G in change_no_check G' end).
    rewrite wbytes_outside; [apply mp_m1_outside; exact Hx | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.
  Lemma mp_m2_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21);
               (-72, S); (-2128, at_ S (-2112)); (-2120, Z_to_bv 64 0)]%Z ->
    rdn segs mp_m2 (at_ S k) 8 = Some (LE8 v).
  Proof using MH fb thr CF.
    intros k v Hin. destruct MH as [_ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold mp_m2, mp_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  Ltac sokS Hs lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa Hs lo N :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hs lo N ]
      | step_simpl]; vn.
  Ltac cldg F D bs0 vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := bs0) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; Hr | first [apply bytes_le_to_Z_8 | unorm; reflexivity] ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma mpA :
    exists r,
      msteps segs (mkst regs (at_ rb 0x6ef3c) mem rom) (mkst r (at_ rb 0x773c4) mp_m2 rom)
      /\ getr r 1 = at_ rb 0x6f060 /\ getr r 2 = at_ S (-2128) /\ getr r 4 = tp
      /\ getr r 10 = at_ S (-2128) /\ getr r 11 = at_ rb 0x6f004 /\ getr r 12 = S /\ getr r 13 = Z_to_bv 64 0
      /\ getr r 14 = Z_to_bv 64 (U fb) /\ getr r 15 = Z_to_bv 64 30
      /\ getr r 8 = S /\ getr r 9 = n /\ getr r 18 = at_ rb 0x6f004 /\ getr r 20 = at_ S (-2128) /\ getr r 21 = at_ S (-81)
      /\ regs_agree CLX regs r.
  Proof using MH H10 H4 H2 H1 thr CF HGPC HGMC HTAI HMP TOK.
    destruct MH as [Rin Rcf Rfb NZ Rmcs Hstk G0 G1 G2]. pose proof (u64_range S) as HS. pose proof (u64_range CF) as HCF. pose proof (u8_range fb) as Hfb.
    destruct (mto_ain _ _ TOK) as [gx GA]. pose proof (mto_gcf _ _ TOK) as GCF. pose proof (mto_mcs _ _ TOK) as GMC.
    wd_eexists. split.
    - an Iec260 D_6ef3c.                                   (* [comment removed for export] *)
      fsd8 Iec264 D_6ef40 (at_ S (-8)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Iec268 D_6ef44 (at_ S (-16)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Iec26c D_6ef48 (at_ S (-24)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Iec270 D_6ef4c (at_ S (-32)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Iec274 D_6ef50 (at_ S (-40)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Iec278 D_6ef54 (at_ S (-48)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Iec27c D_6ef58 (at_ S (-56)) Hstk (at_ S (-2272)) 2272%nat.
      av Iec280 D_6ef5c S ltac:(rewrite at_addi; replace (-2032 + 2032)%Z with 0%Z by lia; apply at_0).   (* [comment removed for export] *)
      an Iec284 D_6ef60.                                   (* [comment removed for export] *)
      an Iec288 D_6ef64.                                   (* [comment removed for export] *)
      an Iec28c D_6ef68.                                   (* [comment removed for export] *)
      an Iec290 D_6ef6c.                                   (* [comment removed for export] *)
      an If7044 D_7662c.                                   (* [comment removed for export] *)
      fsd8 If7048 D_76630 (at_ S (-2136)) Hstk (at_ S (-2272)) 2272%nat.   (* [comment removed for export] *)
      fsd8 If704c D_76634 (at_ S (-2144)) Hstk (at_ S (-2272)) 2272%nat.   (* [comment removed for export] *)
      eapply msteps_trans; [apply GA|]. zlit_at.              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 1); [exact If7058 | reflexivity | exact D_76640
          | gres; rwH; imm_norm; rewrite ?v_addi_0; rewrite <- Rin; apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; cbn in Hx;
            rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia; reflexivity] ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an If705c D_76644.                                   (* [comment removed for export] *)
      afence If7060 D_76648.
      ab_ft If7064 D_7664c ltac:(condz).                  (* [comment removed for export] *)
      cldg If7068 D_76650 (LE8 (at_ rb 0x6ef70)) (at_ rb 0x6ef70) ltac:(rd8_chain).   (* [comment removed for export] *)
      cldg If706c D_76654 (LE8 S) S ltac:(rd8_chain).      (* [comment removed for export] *)
      an If7070 D_76658.                                   (* [comment removed for export] *)
      pose proof (RET 0x6ef70 eq_refl ltac:(lia)) as RT1.
      aret If7074 D_7665c (at_ rb 0x6ef70).                (* [comment removed for export] *)
      ab_ft Iec294 D_6ef70 ltac:(condz).                  (* [comment removed for export] *)
      an Iec298 D_6ef74. an Iec29c D_6ef78.               (* [comment removed for export] *)
      an Iec2a0 D_6ef7c. an Iec2a4 D_6ef80.               (* [comment removed for export] *)
      an Iec2a8 D_6ef84.                                   (* [comment removed for export] *)
      fsd8 Iec2ac D_6ef88 (at_ S (-72)) Hstk (at_ S (-2272)) 2272%nat.     (* [comment removed for export] *)
      fsd8 Iec2b0 D_6ef8c (at_ S (-2128)) Hstk (at_ S (-2272)) 2272%nat.   (* [comment removed for export] *)
      fsd8 Iec2b4 D_6ef90 (at_ S (-2120)) Hstk (at_ S (-2272)) 2272%nat.   (* [comment removed for export] *)
      change (wbytes _ _ _) with mp_m1.
      an Iec2b8 D_6ef94.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply (GMC _ _ _ 30%Z); [lia|]; rewrite <- Rmcs; apply rdn_ext; [wd_ulia_c | intros x Hx; apply mp_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia] |]. zlit_at.
      afence If7ca0 D_773bc.
      pose proof (RET 0x6ef98 eq_refl ltac:(lia)) as RT2.
      aret If7ca4 D_773c0 (at_ rb 0x6ef98).                (* [comment removed for export] *)
      an Iec2bc D_6ef98.                                   (* [comment removed for export] *)
      ab_tk Iec2c0 D_6ef9c ltac:(condz).                  (* [comment removed for export] *)
      an Iec324 D_6f000.                                   (* [comment removed for export] *)
      an I113e20 D_8fe74.                                 (* [comment removed for export] *)
      pose proof (RET 0x6f004 eq_refl ltac:(lia)) as RT3.
      aret I113e24 D_8fe78 (at_ rb 0x6f004).              (* [comment removed for export] *)
      eapply msteps_trans; [eapply GCF; rewrite <- Rcf; apply rdn_ext; [wd_ulia_c | intros x Hx; apply mp_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia] |]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := fb); [exact Iec330 | reflexivity | exact D_6f00c
          | gres; rwH; imm_norm; change (v_addi CF 34) with (at_ CF 34); rewrite <- Rfb; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; apply mp_m1_outside; cbn in Hx; lia] ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an Iec334 D_6f010.                                   (* [comment removed for export] *)
      an Iec338 D_6f014.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply (GMC _ _ _ 30%Z); [lia|]; rewrite <- Rmcs; apply rdn_ext; [wd_ulia_c | intros x Hx; apply mp_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia] |]. zlit_at.
      afence If7ca0 D_773bc.
      pose proof (RET 0x6f018 eq_refl ltac:(lia)) as RT4.
      aret If7ca4 D_773c0 (at_ rb 0x6f018).                (* [comment removed for export] *)
      an Iec33c D_6f018.                                   (* [comment removed for export] *)
      an Iec340 D_6f01c.                                   (* [comment removed for export] *)
      an Iec344 D_6f020.                                   (* [comment removed for export] *)
      an Iec348 D_6f024.                                   (* [comment removed for export] *)
      match goal with |- context [v_and ?m S] => replace (v_and m S) with S by (symmetry; etransitivity; [|apply v_and_m1_l]; f_equal; apply bv_eq; reflexivity) end.
      an Iec34c D_6f028.                                   (* [comment removed for export] *)
      fsd8 Iec350 D_6f02c (at_ S (-72)) Hstk (at_ S (-2272)) 2272%nat.     (* [comment removed for export] *)
      change (wbytes _ _ _) with mp_m2.
      ab_tk Iec354 D_6f030 ltac:(condz).                  (* [comment removed for export] *)
      an Iec368 D_6f044. an Iec36c D_6f048.               (* [comment removed for export] *)
      an Iec370 D_6f04c. an Iec374 D_6f050. an Iec378 D_6f054. an Iec37c D_6f058.   (* [comment removed for export] *)
      an Iec380 D_6f05c.                                   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end). ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma uiH_keep : forall tU (M M' : word -> option byte) (sp0 this0 bp0 thr0 P0 : word),
    uiH segs tU M sp0 this0 bp0 thr0 P0 ->
    (forall x : word, (U x < 2 ^ 32)%Z \/ (U thr0 <= U x < U thr0 + 4096)%Z -> M' x = M x) -> mem_grows M M' ->
    uiH segs tU M' sp0 this0 bp0 thr0 P0.
  Proof using.
    intros tU M M' sp0 this0 bp0 thr0 P0 [Rin Ru SOKu Rg RP Hstk Hobj G0 G1 G2] HM GR.
    pose proof (u64_range thr0). pose proof (u64_range P0).
    split; try assumption.
    - rewrite <- Rin. apply rdn_ext; [wd_ulia_c | intros x Hx; apply HM; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia].
    - rewrite <- Ru. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM; rewrite at_u in Hx by lia; cbn in Hx; lia].
    - eapply store_ok_mono; [exact GR | exact SOKu].
    - rewrite <- Rg. apply rdn_ext; [wd_ulia_c | intros x Hx; apply HM; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia].
    - rewrite <- RP. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM; cbn in Hx; lia].
    - eapply store_ok_mono; [exact GR | exact Hstk].
    - eapply store_ok_mono; [exact GR | exact Hobj].
  Qed.

  (* [comment removed for export] *)
  Theorem mp_run : forall (D : nat),
    fpc mem (U (getr regs 8)) (U S) D ->
    exists r M' (s : Z),
      msteps segs (mkst regs (at_ rb 0x6ef3c) mem rom) (mkst r (at_ rb 0x4c538) M' rom)
      /\ getr r 1 = at_ rb 0x6f070 /\ getr r 2 = at_ S (-2128) /\ getr r 4 = tp
      /\ getr r 10 = n /\ getr r 11 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = n /\ getr r 20 = at_ S (-2128) /\ getr r 21 = at_ S (-81)
      /\ regs_agree CLX regs r
      /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ rdn segs M' (at_ S (-2120)) 4 = Some (LE4 s)                 (* [comment removed for export] *)
      /\ rdn segs M' (at_ S (-2116)) 4 = Some (LE4 0)                 (* [comment removed for export] *)
      /\ rdn segs M' (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))   (* [comment removed for export] *)
      /\ rdn segs M' (at_ S (-2112)) 8 = Some (LE8 (at_ rb 0x6f004))   (* [comment removed for export] *)
      /\ (forall (k : Z) (v : word),
            In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21)]%Z ->
            rdn segs M' (at_ S k) 8 = Some (LE8 v))
      /\ rdn segs M' (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ (forall x : word, M' x <> mem x -> (U S - 2272 <= U x < U S)%Z \/ U x = (U thr + 3168)%Z)
      /\ mem_grows mem M'.
  Proof using Gtop SH GH UH MH H10 H4 H2 H1 fb P tctx tsdp bot top CF HGPC HGMC HTAI HMP TOK.
    intros D FPC.
    pose proof MH as MH'. destruct MH' as [Rin Rcf Rfb NZ Rmcs Hstk G0 G1 G2].
    pose proof (u64_range S) as HS. pose proof (u64_range thr) as Hthr. pose proof (u8_range fb) as Hfb.
    destruct mpA as (r1 & RUN1 & A1 & A2 & A4 & A10 & A11 & A12 & A13 & A14 & A15 & A8 & A9 & A18 & A20 & A21 & AG1).
    assert (GR2 : mem_grows mem mp_m2).
    { (lazymatch goal with |- ?G => let G' := eval unfold mp_m2, mp_m1 in G in change_no_check G' end). do 13 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    assert (UH2 : uiH segs (mt_ui t) mp_m2 (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { apply (uiH_keep _ mem mp_m2 _ _ _ _ _ UH); [|exact GR2]. intros x Hx. apply mp_m2_outside. lia. }
    assert (GH2 : gctH segs (ut_gct (mt_ui t)) mp_m2 (at_ (at_ S (-2128)) (-80)) tp tsdp tctx thr).
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add] in G in change_no_check G' end). apply (gctH_keep segs _ mem mp_m2 _ _ _ _ _ GH); [|exact GR2]. intros x Hx. rewrite at_u in Hx by lia. apply mp_m2_outside. lia. }
    assert (SH2 : stkH segs mp_m2 thr top bot).
    { apply (stkH_keep segs mem mp_m2 _ _ _ SH). intros x Hx. apply mp_m2_outside. lia. }
    pose proof (mto_ui _ _ TOK) as UTOK. pose proof (mto_ui_rb _ _ TOK) as URB.
    destruct (ui_run_s segs (mt_ui t) UTOK r1 mp_m2 rom (at_ rb 0x6f060) (at_ S (-2128)) tp (at_ S (-2128)) (at_ rb 0x6f004) S (Z_to_bv 64 (U fb))
                thr top bot tsdp tctx P (RET 0x6f060 eq_refl ltac:(lia))
                A1 A2 A4 A10 A11 A12 A13 A14 A15 ltac:(unorm; exact NZ) UH2 GH2 SH2 Gtop
                D (LE8 ra) (LE8 (getr regs 8)))
      as (r2 & M3 & s & RUN2 & AG2 & S1 & S2 & SZ & PC & UNW & FR3 & GR3).
    { apply mp_m2_slots. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). tauto. }
    { apply length_N_to_le_bytes. }
    { apply mp_m2_slots. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). tauto. }
    { apply length_N_to_le_bytes. }
    { rewrite bytes_le_to_Z_8. apply (fpc_kept_gen mem _ _ _ FPC mp_m2).
      destruct (fpc_shape _ _ _ _ FPC) as [ST | FRM]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (getr regs 8)). rewrite <- (u_Z2bv a) in Ha by (unfold PTRHI in Ha; lia). apply mp_m2_outside. lia. }
    rewrite URB in RUN2.
    assert (HM3 : forall x : word, U x <> (U thr + 3168)%Z -> (U x < U S - 2272 \/ U S <= U x)%Z -> M3 x = mem x).
    { intros x Hx1 Hx2. destruct (decide (M3 x = mp_m2 x)) as [E|NE].
      - rewrite E. apply mp_m2_outside. lia.
      - exfalso. pose proof (FR3 x NE) as F. rewrite !at_u in F by lia. lia. }
    (* [comment removed for export] *)
    assert (W : exists r3, msteps segs (mkst r2 (at_ rb 0x6f060) M3 rom) (mkst r3 (at_ rb 0x4c538) M3 rom)
                 /\ getr r3 1 = at_ rb 0x6f070 /\ getr r3 10 = n /\ getr r3 11 = at_ S (-2128)
                 /\ (forall i : reg, In i [2; 4; 8; 9; 18; 20; 21] -> getr r3 i = getr r2 i)
                 /\ regs_agree CLX regs r3).
    { assert (K8 : getr r2 8 = S) by (rewrite (AG2 8) by notin_list; exact A8).
      assert (K9 : getr r2 9 = n) by (rewrite (AG2 9) by notin_list; exact A9).
      wd_eexists. split.
      { an Iec384 D_6f060. an Iec388 D_6f064.              (* [comment removed for export] *)
        an Iec38c D_6f068.                                 (* [comment removed for export] *)
        an Iec390 D_6f06c.                                 (* [comment removed for export] *)
        wd_refl. }
      post. 2: (eapply regs_agree_trans; [exact AG1|]; eapply regs_agree_trans; [regs_agree_weaken AG2|]; (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi. }
    destruct W as (r3 & RUN3 & C1 & C10 & C11 & CK & AG3).
    exists r3, M3, s.
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3] |].
    Ltac viaK CK AG2 r A := rewrite (CK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); rewrite (AG2 r) by notin_list; exact A.
    split; [exact C1|]. split; [viaK CK AG2 (2:reg) A2|]. split; [viaK CK AG2 (4:reg) A4|].
    split; [exact C10|]. split; [exact C11|]. split; [viaK CK AG2 (8:reg) A8|]. split; [viaK CK AG2 (9:reg) A9|].
    split; [viaK CK AG2 (20:reg) A20|]. split; [viaK CK AG2 (21:reg) A21|].
    split; [exact AG3|]. split; [exact S1|]. split; [exact S2|].
    split; [rewrite at_at in SZ; exact SZ|].
    split.
    { (* [comment removed for export] *)
      pose proof (mp_m2_slots (-2120) (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto)) as SL.
      assert (SL4 : rdn segs mp_m2 (at_ S (-2116)) 4 = Some (LE4 0)).
      { pose proof (MemsetLibF.RefMemcpyLib.rdn_skipn segs mp_m2 8 (at_ S (-2120)) _ 4 SL ltac:(lia)) as X.
        rewrite at_at in X. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Nat.sub] in X.
        replace (skipn 4 (LE8 (Z_to_bv 64 0))) with (LE4 0) in X by (vm_compute; reflexivity). exact X. }
      rewrite <- SL4. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia.
      destruct (decide (M3 x = mp_m2 x)) as [E|NE]; [exact E|]. exfalso. pose proof (FR3 x NE) as F. rewrite !at_u in F by lia. cbn in Hx. lia. }
    split.
    { pose proof (mp_m2_slots (-2128) (at_ S (-2112)) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto)) as SL.
      rewrite <- SL. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia.
      destruct (decide (M3 x = mp_m2 x)) as [E|NE]; [exact E|]. exfalso. pose proof (FR3 x NE) as F. rewrite !at_u in F by lia. cbn in Hx. lia. }
    split; [rewrite at_at in PC; exact PC|].
    split.
    { intros k v Hin. assert (Hk : (-56 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E; intros; lia|]); destruct Hin).
      rewrite <- (mp_m2_slots k v ltac:(cbn [In] in Hin |- *; tauto)). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia.
      destruct (decide (M3 x = mp_m2 x)) as [E|NE]; [exact E|]. exfalso. pose proof (FR3 x NE) as F. rewrite !at_u in F by lia. cbn in Hx. lia. }
    split; [exact UNW|].
    split.
    { intros x Hx. pose proof (u64_range x). destruct (Z.eq_dec (U x) (U thr + 3168)) as [E|NE]; [right; exact E | left].
      destruct (Z.lt_ge_cases (U x) (U S - 2272)); [exfalso; apply Hx; apply HM3; lia|].
      destruct (Z.lt_ge_cases (U x) (U S)); [lia|]. exfalso; apply Hx; apply HM3; lia. }
    eapply mem_grows_trans; [exact GR2 | exact GR3].
  Qed.

  (* [comment removed for export] *)
  Theorem mp_epi : forall (M : word -> option byte) r0,
    getr r0 2 = at_ S (-2128) ->
    (forall (k : Z) (v : word),
       In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21)]%Z ->
       rdn segs M (at_ S k) 8 = Some (LE8 v)) ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x6f070) M rom) (mkst r ra M rom)
      /\ getr r 10 = getr r0 10 /\ getr r 1 = ra /\ getr r 2 = S
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ (forall i : reg, ~ In i [1; 2; 8; 9; 18; 19; 20; 21] -> getr r i = getr r0 i).
  Proof using Gtop MH Hret fb top thr CF mem HMP TOK.
    intros M r0 R2 RD. destruct MH as [_ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range S) as HS.
    wd_eexists. split.
    - an Iec394 D_6f070.                                   (* [comment removed for export] *)
      cldg Iec398 D_6f074 (LE8 ra) ra ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Iec39c D_6f078 (LE8 (getr regs 8)) (getr regs 8) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Iec3a0 D_6f07c (LE8 (getr regs 9)) (getr regs 9) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Iec3a4 D_6f080 (LE8 (getr regs 18)) (getr regs 18) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Iec3a8 D_6f084 (LE8 (getr regs 19)) (getr regs 19) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Iec3ac D_6f088 (LE8 (getr regs 20)) (getr regs 20) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Iec3b0 D_6f08c (LE8 (getr regs 21)) (getr regs 21) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      av Iec3b4 D_6f090 S ltac:(rewrite at_addi; replace (-2128 + 96 + 2032)%Z with 0%Z by lia; apply at_0).   (* [comment removed for export] *)
      aret Iec3b8 D_6f094 ra.                              (* [comment removed for export] *)
      wd_refl.
    - repeat (split; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | f_equal; lia] |]).
      intros i Hni. gres.
      repeat (rewrite getr_other by (intros E; apply Hni; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto)). reflexivity.
  Qed.
End MP.
End FPGen1.
