(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
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
  [Some W_6e4c4; Some W_6e4c8; Some W_6e4cc; Some W_6e4d0; Some W_6e4d4; Some W_6e4d8; Some W_6e4dc; Some W_6e4e0;
   Some W_6e4e4; Some W_6e4e8; Some W_6e4ec; Some W_6e4f0; Some W_6e4f4; Some W_6e4f8; Some W_6e4fc; Some W_6e500;
   Some W_6e504; Some W_6e508; Some W_6e50c; Some W_6e510; Some W_6e514; Some W_6e518; Some W_6e51c; Some W_6e520;
   Some W_6e524; Some W_6e528; Some W_6e52c; Some W_6e530; Some W_6e534; Some W_6e538; Some W_6e53c; Some W_6e540;
   Some W_6e544; Some W_6e548; Some W_6e54c; Some W_6e550; Some W_6e554; Some W_6e558; Some W_6e55c; Some W_6e560;
   Some W_6e564; Some W_6e568; Some W_6e56c; Some W_6e570; Some W_6e574; Some W_6e578; Some W_6e57c; Some W_6e580;
   Some W_6e584; Some W_6e588; None; None; Some W_6e594; Some W_6e598; Some W_6e59c; Some W_6e5a0; Some W_6e5a4;
   Some W_6e5a8; Some W_6e5ac; Some W_6e5b0; Some W_6e5b4; Some W_6e5b8; Some W_6e5bc; Some W_6e5c0; Some W_6e5c4;
   Some W_6e5c8; Some W_6e5cc; Some W_6e5d0; Some W_6e5d4; Some W_6e5d8; Some W_6e5dc; Some W_6e5e0; Some W_6e5e4;
   Some W_6e5e8; Some W_6e5ec; Some W_6e5f0; Some W_6e5f4; Some W_6e5f8; Some W_6e5fc; Some W_6e600; Some W_6e604;
   Some W_6e608; Some W_6e60c; Some W_6e610; Some W_6e614; Some W_6e618; Some W_6e61c]%list.
Definition tai_words : list (option (bv 32)) :=
  [Some W_75bb4; Some W_75bb8; Some W_75bbc; None; None; Some W_75bc8; Some W_75bcc; Some W_75bd0; Some W_75bd4;
   Some W_75bd8; Some W_75bdc; Some W_75be0; Some W_75be4]%list.
Definition gmc_words : list (option (bv 32)) :=
  [None; None; Some W_76944; Some W_76948]%list.
Definition gpc_words : list (option (bv 32)) :=
  [Some W_8f3fc; Some W_8f400]%list.

(* [comment removed for export] *)
Record mp_tab := MPT { mt_rb : word; mt_ui : ui_tab; mt_g_cf : Z; mt_a_inited : word; mt_g_mcs : Z }.
Record mp_tab_ok (segs : list Segment) (t : mp_tab) : Prop := MPTOK {
  mto_mp : code_ato segs (mt_rb t) 0x6e4cc mp_words;
  mto_tai : code_ato segs (mt_rb t) 0x75bbc tai_words;
  mto_gmc : code_ato segs (mt_rb t) 0x76944 gmc_words;
  mto_gpc : code_ato segs (mt_rb t) 0x8f404 gpc_words;
  mto_gcf : gload segs (mt_rb t) 0x6e594 11 (mt_g_cf t);                 (* [comment removed for export] *)
  mto_ain : gaddr2 segs (mt_rb t) 0x75bc8 10 8 (mt_a_inited t);          (* [comment removed for export] *)
  mto_mcs : gloadw segs (mt_rb t) 0x76944 10 (mt_g_mcs t);               (* [comment removed for export] *)
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
  Let HMP : code_ato segs rb 0x6e4cc mp_words := mto_mp _ _ TOK.
  Let HTAI : code_ato segs rb 0x75bbc tai_words := mto_tai _ _ TOK.
  Let HGMC : code_ato segs rb 0x76944 gmc_words := mto_gmc _ _ TOK.
  Let HGPC : code_ato segs rb 0x8f404 gpc_words := mto_gpc _ _ TOK.

  Lemma Ie55b0 : fetch_word segs (at_ rb 0x6e4cc) = Some W_6e4c4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 0 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55b4 : fetch_word segs (at_ rb 0x6e4d0) = Some W_6e4c8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 1 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55b8 : fetch_word segs (at_ rb 0x6e4d4) = Some W_6e4cc.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 2 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55bc : fetch_word segs (at_ rb 0x6e4d8) = Some W_6e4d0.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 3 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55c0 : fetch_word segs (at_ rb 0x6e4dc) = Some W_6e4d4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 4 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55c4 : fetch_word segs (at_ rb 0x6e4e0) = Some W_6e4d8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 5 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55c8 : fetch_word segs (at_ rb 0x6e4e4) = Some W_6e4dc.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 6 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55cc : fetch_word segs (at_ rb 0x6e4e8) = Some W_6e4e0.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 7 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55d0 : fetch_word segs (at_ rb 0x6e4ec) = Some W_6e4e4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 8 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55d4 : fetch_word segs (at_ rb 0x6e4f0) = Some W_6e4e8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 9 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55d8 : fetch_word segs (at_ rb 0x6e4f4) = Some W_6e4ec.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 10 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55dc : fetch_word segs (at_ rb 0x6e4f8) = Some W_6e4f0.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 11 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55e0 : fetch_word segs (at_ rb 0x6e4fc) = Some W_6e4f4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 12 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55e4 : fetch_word segs (at_ rb 0x6e500) = Some W_6e4f8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 13 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55e8 : fetch_word segs (at_ rb 0x6e504) = Some W_6e4fc.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 14 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55ec : fetch_word segs (at_ rb 0x6e508) = Some W_6e500.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 15 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55f0 : fetch_word segs (at_ rb 0x6e50c) = Some W_6e504.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 16 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55f4 : fetch_word segs (at_ rb 0x6e510) = Some W_6e508.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 17 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55f8 : fetch_word segs (at_ rb 0x6e514) = Some W_6e50c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 18 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie55fc : fetch_word segs (at_ rb 0x6e518) = Some W_6e510.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 19 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5600 : fetch_word segs (at_ rb 0x6e51c) = Some W_6e514.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 20 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5604 : fetch_word segs (at_ rb 0x6e520) = Some W_6e518.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 21 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5608 : fetch_word segs (at_ rb 0x6e524) = Some W_6e51c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 22 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie560c : fetch_word segs (at_ rb 0x6e528) = Some W_6e520.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 23 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5610 : fetch_word segs (at_ rb 0x6e52c) = Some W_6e524.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 24 _ HMP eq_refl). Qed.























   (* [comment removed for export] *)
  Lemma Ie5674 : fetch_word segs (at_ rb 0x6e590) = Some W_6e588.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 49 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5680 : fetch_word segs (at_ rb 0x6e59c) = Some W_6e594.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 52 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5684 : fetch_word segs (at_ rb 0x6e5a0) = Some W_6e598.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 53 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5688 : fetch_word segs (at_ rb 0x6e5a4) = Some W_6e59c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 54 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie568c : fetch_word segs (at_ rb 0x6e5a8) = Some W_6e5a0.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 55 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5690 : fetch_word segs (at_ rb 0x6e5ac) = Some W_6e5a4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 56 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5694 : fetch_word segs (at_ rb 0x6e5b0) = Some W_6e5a8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 57 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5698 : fetch_word segs (at_ rb 0x6e5b4) = Some W_6e5ac.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 58 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie569c : fetch_word segs (at_ rb 0x6e5b8) = Some W_6e5b0.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 59 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56a0 : fetch_word segs (at_ rb 0x6e5bc) = Some W_6e5b4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 60 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56a4 : fetch_word segs (at_ rb 0x6e5c0) = Some W_6e5b8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 61 _ HMP eq_refl). Qed.



   (* [comment removed for export] *)
  Lemma Ie56b8 : fetch_word segs (at_ rb 0x6e5d4) = Some W_6e5cc.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 66 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56bc : fetch_word segs (at_ rb 0x6e5d8) = Some W_6e5d0.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 67 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56c0 : fetch_word segs (at_ rb 0x6e5dc) = Some W_6e5d4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 68 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56c4 : fetch_word segs (at_ rb 0x6e5e0) = Some W_6e5d8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 69 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56c8 : fetch_word segs (at_ rb 0x6e5e4) = Some W_6e5dc.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 70 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56cc : fetch_word segs (at_ rb 0x6e5e8) = Some W_6e5e0.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 71 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56d0 : fetch_word segs (at_ rb 0x6e5ec) = Some W_6e5e4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 72 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56d4 : fetch_word segs (at_ rb 0x6e5f0) = Some W_6e5e8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 73 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56d8 : fetch_word segs (at_ rb 0x6e5f4) = Some W_6e5ec.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 74 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56dc : fetch_word segs (at_ rb 0x6e5f8) = Some W_6e5f0.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 75 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56e0 : fetch_word segs (at_ rb 0x6e5fc) = Some W_6e5f4.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 76 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56e4 : fetch_word segs (at_ rb 0x6e600) = Some W_6e5f8.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 77 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56e8 : fetch_word segs (at_ rb 0x6e604) = Some W_6e5fc.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 78 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56ec : fetch_word segs (at_ rb 0x6e608) = Some W_6e600.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 79 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56f0 : fetch_word segs (at_ rb 0x6e60c) = Some W_6e604.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 80 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56f4 : fetch_word segs (at_ rb 0x6e610) = Some W_6e608.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 81 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56f8 : fetch_word segs (at_ rb 0x6e614) = Some W_6e60c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 82 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie56fc : fetch_word segs (at_ rb 0x6e618) = Some W_6e610.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 83 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5700 : fetch_word segs (at_ rb 0x6e61c) = Some W_6e614.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 84 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5704 : fetch_word segs (at_ rb 0x6e620) = Some W_6e618.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 85 _ HMP eq_refl). Qed.   (* [comment removed for export] *)
  Lemma Ie5708 : fetch_word segs (at_ rb 0x6e624) = Some W_6e61c.  Proof using HMP TOK fx. exact (code_ato_get segs rb 0x6e4cc mp_words 86 _ HMP eq_refl). Qed.   (* [comment removed for export] *)

  Lemma If0394 : fetch_word segs (at_ rb 0x75bbc) = Some W_75bb4.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 0 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If0398 : fetch_word segs (at_ rb 0x75bc0) = Some W_75bb8.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 1 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If039c : fetch_word segs (at_ rb 0x75bc4) = Some W_75bbc.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 2 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If03a8 : fetch_word segs (at_ rb 0x75bd0) = Some W_75bc8.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 5 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If03ac : fetch_word segs (at_ rb 0x75bd4) = Some W_75bcc.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 6 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If03b0 : fetch_word segs (at_ rb 0x75bd8) = Some W_75bd0.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 7 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If03b4 : fetch_word segs (at_ rb 0x75bdc) = Some W_75bd4.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 8 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If03b8 : fetch_word segs (at_ rb 0x75be0) = Some W_75bd8.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 9 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If03bc : fetch_word segs (at_ rb 0x75be4) = Some W_75bdc.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 10 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If03c0 : fetch_word segs (at_ rb 0x75be8) = Some W_75be0.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 11 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If03c4 : fetch_word segs (at_ rb 0x75bec) = Some W_75be4.  Proof using HTAI TOK fx. exact (code_ato_get segs rb 0x75bbc tai_words 12 _ HTAI eq_refl). Qed.   (* [comment removed for export] *)

  Lemma If0ff0 : fetch_word segs (at_ rb 0x7694c) = Some W_76944.  Proof using HGMC TOK fx. exact (code_ato_get segs rb 0x76944 gmc_words 2 _ HGMC eq_refl). Qed.   (* [comment removed for export] *)
  Lemma If0ff4 : fetch_word segs (at_ rb 0x76950) = Some W_76948.  Proof using HGMC TOK fx. exact (code_ato_get segs rb 0x76944 gmc_words 3 _ HGMC eq_refl). Qed.   (* [comment removed for export] *)

  Lemma I10d1a0 : fetch_word segs (at_ rb 0x8f404) = Some W_8f3fc.  Proof using HGPC TOK fx. exact (code_ato_get segs rb 0x8f404 gpc_words 0 _ HGPC eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I10d1a4 : fetch_word segs (at_ rb 0x8f408) = Some W_8f400.  Proof using HGPC TOK fx. exact (code_ato_get segs rb 0x8f404 gpc_words 1 _ HGPC eq_refl). Qed.   (* [comment removed for export] *)


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
      (at_ S (-2136)) (LE8 (at_ rb 0x6e500))) (at_ S (-2144)) (LE8 S))               (* [comment removed for export] *)
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
      msteps segs (mkst regs (at_ rb 0x6e4cc) mem rom) (mkst r (at_ rb 0x76954) mp_m2 rom)
      /\ getr r 1 = at_ rb 0x6e5f0 /\ getr r 2 = at_ S (-2128) /\ getr r 4 = tp
      /\ getr r 10 = at_ S (-2128) /\ getr r 11 = at_ rb 0x6e594 /\ getr r 12 = S /\ getr r 13 = Z_to_bv 64 0
      /\ getr r 14 = Z_to_bv 64 (U fb) /\ getr r 15 = Z_to_bv 64 30
      /\ getr r 8 = S /\ getr r 9 = n /\ getr r 18 = at_ rb 0x6e594 /\ getr r 20 = at_ S (-2128) /\ getr r 21 = at_ S (-81)
      /\ regs_agree CLX regs r.
  Proof using MH H10 H4 H2 H1 thr CF HGPC HGMC HTAI HMP TOK.
    destruct MH as [Rin Rcf Rfb NZ Rmcs Hstk G0 G1 G2]. pose proof (u64_range S) as HS. pose proof (u64_range CF) as HCF. pose proof (u8_range fb) as Hfb.
    destruct (mto_ain _ _ TOK) as [gx GA]. pose proof (mto_gcf _ _ TOK) as GCF. pose proof (mto_mcs _ _ TOK) as GMC.
    wd_eexists. split.
    - an Ie55b0 D_6e4c4.                                   (* [comment removed for export] *)
      fsd8 Ie55b4 D_6e4c8 (at_ S (-8)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Ie55b8 D_6e4cc (at_ S (-16)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Ie55bc D_6e4d0 (at_ S (-24)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Ie55c0 D_6e4d4 (at_ S (-32)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Ie55c4 D_6e4d8 (at_ S (-40)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Ie55c8 D_6e4dc (at_ S (-48)) Hstk (at_ S (-2272)) 2272%nat.
      fsd8 Ie55cc D_6e4e0 (at_ S (-56)) Hstk (at_ S (-2272)) 2272%nat.
      av Ie55d0 D_6e4e4 S ltac:(rewrite at_addi; replace (-2032 + 2032)%Z with 0%Z by lia; apply at_0).   (* [comment removed for export] *)
      an Ie55d4 D_6e4e8.                                   (* [comment removed for export] *)
      an Ie55d8 D_6e4ec.                                   (* [comment removed for export] *)
      an Ie55dc D_6e4f0.                                   (* [comment removed for export] *)
      an Ie55e0 D_6e4f4.                                   (* [comment removed for export] *)
      an If0394 D_75bb4.                                   (* [comment removed for export] *)
      fsd8 If0398 D_75bb8 (at_ S (-2136)) Hstk (at_ S (-2272)) 2272%nat.   (* [comment removed for export] *)
      fsd8 If039c D_75bbc (at_ S (-2144)) Hstk (at_ S (-2272)) 2272%nat.   (* [comment removed for export] *)
      eapply msteps_trans; [apply GA|]. zlit_at.              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 1); [exact If03a8 | reflexivity | exact D_75bc8
          | gres; rwH; imm_norm; rewrite ?v_addi_0; rewrite <- Rin; apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; cbn in Hx;
            rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia; reflexivity] ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an If03ac D_75bcc.                                   (* [comment removed for export] *)
      afence If03b0 D_75bd0.
      ab_ft If03b4 D_75bd4 ltac:(condz).                  (* [comment removed for export] *)
      cldg If03b8 D_75bd8 (LE8 (at_ rb 0x6e500)) (at_ rb 0x6e500) ltac:(rd8_chain).   (* [comment removed for export] *)
      cldg If03bc D_75bdc (LE8 S) S ltac:(rd8_chain).      (* [comment removed for export] *)
      an If03c0 D_75be0.                                   (* [comment removed for export] *)
      pose proof (RET 0x6e500 eq_refl ltac:(lia)) as RT1.
      aret If03c4 D_75be4 (at_ rb 0x6e500).                (* [comment removed for export] *)
      ab_ft Ie55e4 D_6e4f8 ltac:(condz).                  (* [comment removed for export] *)
      an Ie55e8 D_6e4fc. an Ie55ec D_6e500.               (* [comment removed for export] *)
      an Ie55f0 D_6e504. an Ie55f4 D_6e508.               (* [comment removed for export] *)
      an Ie55f8 D_6e50c.                                   (* [comment removed for export] *)
      fsd8 Ie55fc D_6e510 (at_ S (-72)) Hstk (at_ S (-2272)) 2272%nat.     (* [comment removed for export] *)
      fsd8 Ie5600 D_6e514 (at_ S (-2128)) Hstk (at_ S (-2272)) 2272%nat.   (* [comment removed for export] *)
      fsd8 Ie5604 D_6e518 (at_ S (-2120)) Hstk (at_ S (-2272)) 2272%nat.   (* [comment removed for export] *)
      change (wbytes _ _ _) with mp_m1.
      an Ie5608 D_6e51c.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply (GMC _ _ _ 30%Z); [lia|]; rewrite <- Rmcs; apply rdn_ext; [wd_ulia_c | intros x Hx; apply mp_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia] |]. zlit_at.
      afence If0ff0 D_76944.
      pose proof (RET 0x6e528 eq_refl ltac:(lia)) as RT2.
      aret If0ff4 D_76948 (at_ rb 0x6e528).                (* [comment removed for export] *)
      an Ie560c D_6e520.                                   (* [comment removed for export] *)
      ab_tk Ie5610 D_6e524 ltac:(condz).                  (* [comment removed for export] *)
      an Ie5674 D_6e588.                                   (* [comment removed for export] *)
      an I10d1a0 D_8f3fc.                                 (* [comment removed for export] *)
      pose proof (RET 0x6e594 eq_refl ltac:(lia)) as RT3.
      aret I10d1a4 D_8f400 (at_ rb 0x6e594).              (* [comment removed for export] *)
      eapply msteps_trans; [eapply GCF; rewrite <- Rcf; apply rdn_ext; [wd_ulia_c | intros x Hx; apply mp_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia] |]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := fb); [exact Ie5680 | reflexivity | exact D_6e594
          | gres; rwH; imm_norm; change (v_addi CF 34) with (at_ CF 34); rewrite <- Rfb; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; apply mp_m1_outside; cbn in Hx; lia] ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an Ie5684 D_6e598.                                   (* [comment removed for export] *)
      an Ie5688 D_6e59c.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply (GMC _ _ _ 30%Z); [lia|]; rewrite <- Rmcs; apply rdn_ext; [wd_ulia_c | intros x Hx; apply mp_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia] |]. zlit_at.
      afence If0ff0 D_76944.
      pose proof (RET 0x6e5a8 eq_refl ltac:(lia)) as RT4.
      aret If0ff4 D_76948 (at_ rb 0x6e5a8).                (* [comment removed for export] *)
      an Ie568c D_6e5a0.                                   (* [comment removed for export] *)
      an Ie5690 D_6e5a4.                                   (* [comment removed for export] *)
      an Ie5694 D_6e5a8.                                   (* [comment removed for export] *)
      an Ie5698 D_6e5ac.                                   (* [comment removed for export] *)
      match goal with |- context [v_and ?m S] => replace (v_and m S) with S by (symmetry; etransitivity; [|apply v_and_m1_l]; f_equal; apply bv_eq; reflexivity) end.
      an Ie569c D_6e5b0.                                   (* [comment removed for export] *)
      fsd8 Ie56a0 D_6e5b4 (at_ S (-72)) Hstk (at_ S (-2272)) 2272%nat.     (* [comment removed for export] *)
      change (wbytes _ _ _) with mp_m2.
      ab_tk Ie56a4 D_6e5b8 ltac:(condz).                  (* [comment removed for export] *)
      an Ie56b8 D_6e5cc. an Ie56bc D_6e5d0.               (* [comment removed for export] *)
      an Ie56c0 D_6e5d4. an Ie56c4 D_6e5d8. an Ie56c8 D_6e5dc. an Ie56cc D_6e5e0.   (* [comment removed for export] *)
      an Ie56d0 D_6e5e4.                                   (* [comment removed for export] *)
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
      msteps segs (mkst regs (at_ rb 0x6e4cc) mem rom) (mkst r (at_ rb 0x4bac8) M' rom)
      /\ getr r 1 = at_ rb 0x6e600 /\ getr r 2 = at_ S (-2128) /\ getr r 4 = tp
      /\ getr r 10 = n /\ getr r 11 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = n /\ getr r 20 = at_ S (-2128) /\ getr r 21 = at_ S (-81)
      /\ regs_agree CLX regs r
      /\ (1 <= s <= 30)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ rdn segs M' (at_ S (-2120)) 4 = Some (LE4 s)                 (* [comment removed for export] *)
      /\ rdn segs M' (at_ S (-2116)) 4 = Some (LE4 0)                 (* [comment removed for export] *)
      /\ rdn segs M' (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))   (* [comment removed for export] *)
      /\ rdn segs M' (at_ S (-2112)) 8 = Some (LE8 (at_ rb 0x6e594))   (* [comment removed for export] *)
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
    destruct (ui_run_s segs (mt_ui t) UTOK r1 mp_m2 rom (at_ rb 0x6e5f0) (at_ S (-2128)) tp (at_ S (-2128)) (at_ rb 0x6e594) S (Z_to_bv 64 (U fb))
                thr top bot tsdp tctx P (RET 0x6e5f0 eq_refl ltac:(lia))
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
    assert (W : exists r3, msteps segs (mkst r2 (at_ rb 0x6e5f0) M3 rom) (mkst r3 (at_ rb 0x4bac8) M3 rom)
                 /\ getr r3 1 = at_ rb 0x6e600 /\ getr r3 10 = n /\ getr r3 11 = at_ S (-2128)
                 /\ (forall i : reg, In i [2; 4; 8; 9; 18; 20; 21] -> getr r3 i = getr r2 i)
                 /\ regs_agree CLX regs r3).
    { assert (K8 : getr r2 8 = S) by (rewrite (AG2 8) by notin_list; exact A8).
      assert (K9 : getr r2 9 = n) by (rewrite (AG2 9) by notin_list; exact A9).
      wd_eexists. split.
      { an Ie56d4 D_6e5e8. an Ie56d8 D_6e5ec.              (* [comment removed for export] *)
        an Ie56dc D_6e5f0.                                 (* [comment removed for export] *)
        an Ie56e0 D_6e5f4.                                 (* [comment removed for export] *)
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
      msteps segs (mkst r0 (at_ rb 0x6e600) M rom) (mkst r ra M rom)
      /\ getr r 10 = getr r0 10 /\ getr r 1 = ra /\ getr r 2 = S
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ (forall i : reg, ~ In i [1; 2; 8; 9; 18; 19; 20; 21] -> getr r i = getr r0 i).
  Proof using Gtop MH Hret fb top thr CF mem HMP TOK.
    intros M r0 R2 RD. destruct MH as [_ _ _ _ _ _ G0 G1 G2]. pose proof (u64_range S) as HS.
    wd_eexists. split.
    - an Ie56e4 D_6e5f8.                                   (* [comment removed for export] *)
      cldg Ie56e8 D_6e5fc (LE8 ra) ra ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Ie56ec D_6e600 (LE8 (getr regs 8)) (getr regs 8) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Ie56f0 D_6e604 (LE8 (getr regs 9)) (getr regs 9) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Ie56f4 D_6e608 (LE8 (getr regs 18)) (getr regs 18) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Ie56f8 D_6e60c (LE8 (getr regs 19)) (getr regs 19) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Ie56fc D_6e610 (LE8 (getr regs 20)) (getr regs 20) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      cldg Ie5700 D_6e614 (LE8 (getr regs 21)) (getr regs 21) ltac:(apply RD; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto).
      av Ie5704 D_6e618 S ltac:(rewrite at_addi; replace (-2128 + 96 + 2032)%Z with 0%Z by lia; apply at_0).   (* [comment removed for export] *)
      aret Ie5708 D_6e61c ra.                              (* [comment removed for export] *)
      wd_refl.
    - repeat (split; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | f_equal; lia] |]).
      intros i Hni. gres.
      repeat (rewrite getr_other by (intros E; apply Hni; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto)). reflexivity.
  Qed.
End MP.
End FPGen1.
