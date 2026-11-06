(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs StepSoundBase.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step ValP StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module StepA.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma interp_EDone : forall c m, interp_eff segs (EDone c) m = MachineOk (c, m).
Proof. reflexivity. Qed.

Lemma Z_to_bv64_mod : forall z, Z_to_bv 64 (z mod two64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. apply Zmod_mod.
Qed.

Lemma wbv_Z2w : forall z, wbv (Z2w z) = Z_to_bv 64 z.
Proof. intros z. unfold wbv. rewrite Z2w_ok. apply Z_to_bv64_mod. Qed.

Lemma wbv_w_of_imm : forall n (b : bv n), wbv (w_of_imm b) = sext 64 b.
Proof.
  intros n b. unfold w_of_imm, sext. rewrite wbv_Z2w. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_sign_extend_unsigned. reflexivity.
Qed.

Lemma wbv_w_of_uimm : forall n (b : bv n), wbv (w_of_uimm b) = zext 64 b.
Proof.
  intros n b. unfold w_of_uimm, zext. rewrite wbv_Z2w. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_zero_extend_unsigned'. reflexivity.
Qed.

Lemma wbv_wlit : forall i, wbv (wlit i) = Z_to_bv 64 (to_Z i).
Proof. intros i. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Lemma low32_sext64 : forall n (b : bv n), low32 (sext 64 b) = sext 32 b.
Proof.
  intros n b. apply bv_eq. unfold low32, sext. rewrite bv_extract_unsigned, !bv_sign_extend_unsigned, Z.shiftr_0_r.
  apply (bv_wrap_bv_wrap 32 64). lia.
Qed.

Lemma low32_zext64 : forall n (b : bv n), low32 (zext 64 b) = zext 32 b.
Proof.
  intros n b. apply bv_eq. unfold low32, zext. rewrite bv_extract_unsigned, !bv_zero_extend_unsigned', Z.shiftr_0_r.
  apply (bv_wrap_bv_wrap 32 64). lia.
Qed.

Lemma lui_signed : forall imm : bv 20,
  bv_signed (bv_concat 32 imm (Z_to_bv 12 0)) = bv_signed imm * 4096.
Proof.
  intros imm. rewrite bv_concat_signed. rewrite Z_to_bv_unsigned. rewrite bv_wrap_0, Z.lor_0_r.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ Z.of_N 12) with 4096.
  unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (bv_half_modulus 20) with 524288. change (bv_modulus 20) with 1048576.
  pose proof (bv_unsigned_in_range _ imm) as Hr. change (bv_modulus 20) with 1048576 in Hr.
  rewrite (mod_cases2 (bv_unsigned imm * 4096 + 2147483648) 4294967296) by lia.
  rewrite (mod_cases2 (bv_unsigned imm + 524288) 1048576) by lia.
  destruct (Z.ltb_spec (bv_unsigned imm * 4096 + 2147483648) 4294967296);
  destruct (Z.ltb_spec (bv_unsigned imm + 524288) 1048576); lia.
Qed.

Lemma lui_imm : forall imm : bv 20,
  Z_to_bv 64 (bv_signed imm * 4096) = sext 64 (bv_concat 32 imm (Z_to_bv 12 0)).
Proof.
  intros imm. unfold sext. apply bv_eq. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned, lui_signed. reflexivity.
Qed.

Lemma jalr_mask : forall t, wt (wand t (wnot wone)) = false ->
  Z_to_bv 64 (to_Z (wl (wand t (wnot wone)))) = bv_and (wbv t) (bv_not w1).
Proof.
  intros t Ht.
  assert (Hw : to_Z (wl (wand t (wnot wone))) = w2Z (wand t (wnot wone))).
  { unfold w2Z. rewrite Ht. lia. }
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_and_unsigned, bv_not_unsigned, wbv_unsigned.
  rewrite Hw, wand_ok, wnot_ok, wone_ok.
  unfold w1. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1. change (bv_wrap 64 (Z.lnot 1)) with (two64 - 1 - 1).
  apply bv_wrap_small. rewrite bv_modulus_64.
  pose proof (w2Z_range t). pose proof (land_range_l (w2Z t) (two64 - 1 - 1) 64).
  rewrite <- two64_eq in *. lia.
Qed.

Ltac cbn_st := cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setpc setf setresv setregs addfact
                    ms_upd c_regs c_fregs c_pc c_fcsr c_resv
                    ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending
                    with_pc with_regs with_fregs with_resv with_fcsr core_of rget fget rset fset].

Lemma getr_den : forall E st ms model r, st_ok segs OPS E st ms model ->
  den E (getr st r) = rget (core_of ms) (reg_of_r5 r).
Proof. intros E st ms model r HS. unfold getr. symmetry. exact (so_regs _ _ _ _ _ _ HS r). Qed.

Lemma getf_den : forall E st ms model r, st_ok segs OPS E st ms model ->
  den E (getf st r) = fget (core_of ms) (reg_of_r5 r).
Proof. intros E st ms model r HS. unfold getf. symmetry. exact (so_fregs _ _ _ _ _ _ HS r). Qed.

Lemma pc_core : forall E st ms model, st_ok segs OPS E st ms model ->
  c_pc (core_of ms) = Z_to_bv 64 (to_Z (s_pc st)).
Proof. intros E st ms model HS. exact (so_pc _ _ _ _ _ _ HS). Qed.

Lemma pc4_core : forall E st ms model, st_ok segs OPS E st ms model ->
  PrimInt63.ltb (s_pc st) bit62i = true ->
  Z_to_bv 64 (to_Z (pc4 st)) = (c_pc (core_of ms) + Z_to_bv 64 4)%bv.
Proof.
  intros E st ms model HS Hpc. unfold pc4. rewrite (pc4_ok _ Hpc). rewrite (pc_core E st ms model HS). reflexivity.
Qed.

Lemma resolve_rm_core : forall E st ms model rm npc, st_ok segs OPS E st ms model ->
  resolve_rm rm (with_pc npc (core_of ms)) = resolve_rm_b rm.
Proof.
  intros E st ms model rm npc HS. unfold resolve_rm, resolve_rm_b, frm_of. cbn [c_fcsr with_pc core_of].
  pose proof (so_fcsr _ _ _ _ _ _ HS) as Hf. pose proof (bv_unsigned_in_range _ (ms_fcsr ms)) as Hr.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  rewrite Z.div_small by lia. rewrite Z.land_0_l. reflexivity.
Qed.

Lemma case_reg_gen : forall E st ms model rd (v : sv) (wv npc : word) (npci : int),
  st_ok segs OPS E st ms model ->
  den E v = wv ->
  Z_to_bv 64 (to_Z npci) = npc ->
  exists c m',
    interp_eff segs (EDone (rset (reg_of_r5 rd) wv (with_pc npc (core_of ms)))) (ms_mem ms) = MachineOk (c, m') /\
    st_ok segs OPS E (setpc (setr st rd v) npci) (ms_upd ms c m') model.
Proof.
  intros E st ms model rd v wv npc npci HS Hv Hn.
  eexists _, _. split; [apply interp_EDone|]. rewrite <- Hn. apply st_ok_reg_pc; assumption.
Qed.

Lemma case_reg : forall E st ms model rd (v : sv) (wv : word),
  st_ok segs OPS E st ms model ->
  PrimInt63.ltb (s_pc st) bit62i = true ->
  den E v = wv ->
  exists c m',
    interp_eff segs (EDone (rset (reg_of_r5 rd) wv (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))) (ms_mem ms) = MachineOk (c, m') /\
    st_ok segs OPS E (setpc (setr st rd v) (pc4 st)) (ms_upd ms c m') model.
Proof.
  intros E st ms model rd v wv HS Hpc Hv. apply case_reg_gen; [exact HS|exact Hv|exact (pc4_core E st ms model HS Hpc)].
Qed.

Lemma case_freg : forall E st ms model rd (v : sv) (wv : word),
  st_ok segs OPS E st ms model ->
  PrimInt63.ltb (s_pc st) bit62i = true ->
  den E v = wv ->
  exists c m',
    interp_eff segs (EDone (fset (reg_of_r5 rd) wv (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))) (ms_mem ms) = MachineOk (c, m') /\
    st_ok segs OPS E (setpc (setf st rd v) (pc4 st)) (ms_upd ms c m') model.
Proof.
  intros E st ms model rd v wv HS Hpc Hv.
  eexists _, _. split; [apply interp_EDone|]. rewrite <- (pc4_core E st ms model HS Hpc). apply st_ok_freg_pc; assumption.
Qed.

Lemma st_ok_freg_fcsr_pc : forall E st ms model rd (v : sv) (wv : word) (f : bv 32) (npci : int),
  st_ok segs OPS E st ms model ->
  den E v = wv ->
  bv_unsigned f < 32 ->
  st_ok segs OPS E (setpc (setf st rd v) npci)
        (ms_upd ms (fset (reg_of_r5 rd) wv (with_fcsr f (with_pc (Z_to_bv 64 (to_Z npci)) (core_of ms)))) (ms_mem ms)) model.
Proof.
  intros E st ms model rd v wv f npci HS Hv Hf.
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf].
  split; cbn_st; try assumption; try reflexivity.
  - intros r. rewrite reg_get_set. destruct (r5_eqb r rd) eqn:H1.
    + apply r5_eqb_spec in H1; subst r. rewrite rf_get_set_same. symmetry; exact Hv.
    + rewrite rf_get_set_other. 2:{ intro HH; subst r. rewrite r5_eqb_refl in H1. discriminate. }
      exact (Hfregs r).
Qed.

Lemma case_freg_fcsr : forall E st ms model rd (v : sv) (wv : word) (f : bv 32),
  st_ok segs OPS E st ms model ->
  PrimInt63.ltb (s_pc st) bit62i = true ->
  den E v = wv ->
  bv_unsigned f < 32 ->
  exists c m',
    interp_eff segs (EDone (fset (reg_of_r5 rd) wv (with_fcsr f (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))))) (ms_mem ms) = MachineOk (c, m') /\
    st_ok segs OPS E (setpc (setf st rd v) (pc4 st)) (ms_upd ms c m') model.
Proof.
  intros E st ms model rd v wv f HS Hpc Hv Hf.
  eexists _, _. split; [apply interp_EDone|]. rewrite <- (pc4_core E st ms model HS Hpc).
  apply st_ok_freg_fcsr_pc; assumption.
Qed.

Lemma fflags_bits_range : forall fl, 0 <= fflags_bits fl < 32.
Proof.
  intros [nv dz o uf nx]. unfold fflags_bits. cbn [fl_nx fl_uf fl_of fl_dz fl_nv].
  destruct nv, dz, o, uf, nx;
  match goal with |- 0 <= ?e < 32 => let v := eval vm_compute in e in change e with v end; lia.
Qed.

Lemma accrue_fcsr_range : forall (f : bv 32) fl, bv_unsigned f < 32 ->
  bv_unsigned (Z_to_bv 32 (Z.lor (bv_unsigned f) (fflags_bits fl))) < 32.
Proof.
  intros f fl Hf. pose proof (bv_unsigned_in_range _ f) as Hr. pose proof (fflags_bits_range fl) as Hl.
  pose proof (lor_range (bv_unsigned f) (fflags_bits fl) 5) as H5. change (2 ^ 5) with 32 in H5.
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [lia|].
  change (bv_modulus 32) with 4294967296. lia.
Qed.

Lemma case_pc_gen : forall E st ms model (npc : word) (npci : int),
  st_ok segs OPS E st ms model ->
  Z_to_bv 64 (to_Z npci) = npc ->
  exists c m',
    interp_eff segs (EDone (with_pc npc (core_of ms))) (ms_mem ms) = MachineOk (c, m') /\
    st_ok segs OPS E (setpc st npci) (ms_upd ms c m') model.
Proof.
  intros E st ms model npc npci HS Hn.
  eexists _, _. split; [apply interp_EDone|]. rewrite <- Hn. apply st_ok_pc; assumption.
Qed.

Lemma case_pc4 : forall E st ms model,
  st_ok segs OPS E st ms model ->
  PrimInt63.ltb (s_pc st) bit62i = true ->
  exists c m',
    interp_eff segs (EDone (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))) (ms_mem ms) = MachineOk (c, m') /\
    st_ok segs OPS E (setpc st (pc4 st)) (ms_upd ms c m') model.
Proof.
  intros E st ms model HS Hpc. apply case_pc_gen; [exact HS|exact (pc4_core E st ms model HS Hpc)].
Qed.

Ltac inv_of Hof :=
  repeat match type of Hof with
  | context [match r5_of_reg ?r with _ => _ end] =>
      let d := fresh "d" in let Hd := fresh "Hd" in
      destruct (r5_of_reg r) as [d|] eqn:Hd; [apply reg_of_r5_of_reg in Hd; subst r | discriminate Hof]
  | context [match ?x with _ => _ end] => is_var x; destruct x
  end;
  first [discriminate Hof | injection Hof; intros; subst | idtac].

Ltac open_case i Hof Hx :=
  destruct i; cbn [of_instr] in Hof; try discriminate Hof; inv_of Hof; cbn [exec] in Hx; try discriminate Hx.

Lemma sound_ILui : forall (i : instr) (rd : r5) (v : w64), case_stmt segs OPS i (ILui rd v).
Proof.
  intros i rd v E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  injection Hx as <-. cbn [Sem.exec].
  apply case_reg; [exact HS|exact Hpc|].
  cbn [den]. rewrite wbv_Z2w. apply lui_imm.
Qed.

Lemma sound_IAuipc : forall (i : instr) (rd : r5) (v : w64), case_stmt segs OPS i (IAuipc rd v).
Proof.
  intros i rd v E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  injection Hx as <-. cbn [Sem.exec].
  apply case_reg; [exact HS|exact Hpc|].
  cbn [den]. rewrite wbv_wadd, wbv_wlit, wbv_Z2w, lui_imm, <- (pc_core E st ms model HS). reflexivity.
Qed.

Lemma sound_IJal : forall (i : instr) (rd : r5) (off : w64), case_stmt segs OPS i (IJal rd off).
Proof.
  intros i rd off E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  destruct (pc_add (s_pc st) (w_of_imm imm)) as [t|] eqn:Ht; [|discriminate Hx].
  injection Hx as <-. cbn [Sem.exec].
  apply case_reg_gen; [exact HS| |].
  - cbn [den]. rewrite wbv_wlit. exact (pc4_core E st ms model HS Hpc).
  - rewrite (pc_add_ok _ _ _ Ht), wbv_w_of_imm, (pc_core E st ms model HS). reflexivity.
Qed.

Lemma sound_IJalr : forall (i : instr) (rd rs1 : r5) (off : w64), case_stmt segs OPS i (IJalr rd rs1 off).
Proof.
  intros i rd rs1 off E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  destruct (sv_alu ALU_ADD (getr st rs1) (VL (w_of_imm imm))) eqn:Ht; try discriminate Hx.
  match type of Hx with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate Hx] end.
  injection Hx as <-. cbn [Sem.exec].
  apply andb_prop in Hc as [Hwt _]. apply negb_true_iff in Hwt.
  apply case_reg_gen; [exact HS| |].
  - cbn [den]. rewrite wbv_wlit. exact (pc4_core E st ms model HS Hpc).
  - apply (f_equal (den E)) in Ht. rewrite den_sv_alu in Ht. cbn [alu64 alu den] in Ht.
    rewrite (getr_den E st ms model rs1 HS), wbv_w_of_imm in Ht. rewrite Ht.
    apply jalr_mask. exact Hwt.
Qed.

Lemma sound_IBranch : forall (i : instr) (c : branch_cond) (rs1 rs2 : r5) (off : w64), case_stmt segs OPS i (IBranch c rs1 rs2 off).
Proof.
  intros i c rs1 rs2 off E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  destruct (decide_branch_t (s_facts st) c (getr st rs1) (getr st rs2)) as [[|]|] eqn:Hdb; try discriminate Hx.
  - destruct (pc_add (s_pc st) (w_of_imm imm)) as [t|] eqn:Ht; [|discriminate Hx].
    injection Hx as <-. cbn [Sem.exec].
    apply (decide_branch_t_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS)) in Hdb.
    rewrite (getr_den E st ms model rs1 HS), (getr_den E st ms model rs2 HS) in Hdb. rewrite Hdb.
    apply case_pc_gen; [exact HS|].
    rewrite (pc_add_ok _ _ _ Ht), wbv_w_of_imm, (pc_core E st ms model HS). reflexivity.
  - injection Hx as <-. cbn [Sem.exec].
    apply (decide_branch_t_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS)) in Hdb.
    rewrite (getr_den E st ms model rs1 HS), (getr_den E st ms model rs2 HS) in Hdb. rewrite Hdb.
    apply case_pc4; [exact HS|exact Hpc].
Qed.

Lemma sound_IOpImm : forall (i : instr) (op : aluop) (rd rs1 : r5) (v : w64), case_stmt segs OPS i (IOpImm op rd rs1 v).
Proof.
  intros i op rd rs1 v E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  - injection Hx as <-. cbn [Sem.exec].
    apply case_reg; [exact HS|exact Hpc|].
    rewrite (den_sv_alu_f E (s_facts st) (so_facts _ _ _ _ _ _ HS)).
    rewrite (getr_den E st ms model rs1 HS). cbn [den]. rewrite wbv_w_of_imm. reflexivity.
  - injection Hx as <-. cbn [Sem.exec].
    apply case_reg; [exact HS|exact Hpc|].
    rewrite (den_sv_alu_f E (s_facts st) (so_facts _ _ _ _ _ _ HS)).
    rewrite (getr_den E st ms model rs1 HS). cbn [den]. rewrite wbv_w_of_uimm. reflexivity.
Qed.

Lemma sound_IOp : forall (i : instr) (op : aluop) (rd rs1 rs2 : r5), case_stmt segs OPS i (IOp op rd rs1 rs2).
Proof.
  intros i op rd rs1 rs2 E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  injection Hx as <-. cbn [Sem.exec].
  apply case_reg; [exact HS|exact Hpc|].
  rewrite (den_sv_alu_f E (s_facts st) (so_facts _ _ _ _ _ _ HS)).
  rewrite (getr_den E st ms model rs1 HS), (getr_den E st ms model rs2 HS). reflexivity.
Qed.

Lemma sound_IOpImm32 : forall (i : instr) (op : aluop) (rd rs1 : r5) (v : w64), case_stmt segs OPS i (IOpImm32 op rd rs1 v).
Proof.
  intros i op rd rs1 v E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  - injection Hx as <-. cbn [Sem.exec].
    apply case_reg; [exact HS|exact Hpc|].
    match goal with |- den E ?x = _ => change (den E x) with (den E (sv_aluw_f (s_facts st) ALU_ADD (getr st rs1) (VL (w_of_imm imm)))) end.
    rewrite (den_sv_aluw_f E (s_facts st) (so_facts _ _ _ _ _ _ HS)), (getr_den E st ms model rs1 HS). cbn [den]. rewrite wbv_w_of_imm, low32_sext64. reflexivity.
  - injection Hx as <-. cbn [Sem.exec].
    apply case_reg; [exact HS|exact Hpc|].
    match goal with |- den E ?x = _ => change (den E x) with (den E (sv_aluw_f (s_facts st) op (getr st rs1) (VL (w_of_uimm shamt)))) end.
    rewrite (den_sv_aluw_f E (s_facts st) (so_facts _ _ _ _ _ _ HS)), (getr_den E st ms model rs1 HS). cbn [den]. rewrite wbv_w_of_uimm, low32_zext64. reflexivity.
Qed.

Lemma sound_IOp32 : forall (i : instr) (op : aluop) (rd rs1 rs2 : r5), case_stmt segs OPS i (IOp32 op rd rs1 rs2).
Proof.
  intros i op rd rs1 rs2 E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  injection Hx as <-. cbn [Sem.exec].
  apply case_reg; [exact HS|exact Hpc|].
  rewrite (den_sv_aluw_f E (s_facts st) (so_facts _ _ _ _ _ _ HS)), (getr_den E st ms model rs1 HS), (getr_den E st ms model rs2 HS). reflexivity.
Qed.

Lemma sound_IMul : forall (i : instr) (op : mulop) (rd rs1 rs2 : r5), case_stmt segs OPS i (IMul op rd rs1 rs2).
Proof.
  intros i op rd rs1 rs2 E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  injection Hx as <-. cbn [Sem.exec].
  apply case_reg; [exact HS|exact Hpc|].
  rewrite den_sv_md, (getr_den E st ms model rs1 HS), (getr_den E st ms model rs2 HS). reflexivity.
Qed.

Lemma sound_IMul32 : forall (i : instr) (op : mulop) (rd rs1 rs2 : r5), case_stmt segs OPS i (IMul32 op rd rs1 rs2).
Proof.
  intros i op rd rs1 rs2 E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  injection Hx as <-. cbn [Sem.exec].
  apply case_reg; [exact HS|exact Hpc|].
  rewrite den_sv_mdw, (getr_den E st ms model rs1 HS), (getr_den E st ms model rs2 HS). reflexivity.
Qed.

Lemma sound_IFence : forall (i : instr) , case_stmt segs OPS i (IFence).
Proof.
  intros i E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  - injection Hx as <-. cbn [Sem.exec]. apply case_pc4; [exact HS|exact Hpc].
  - injection Hx as <-. cbn [Sem.exec]. apply case_pc4; [exact HS|exact Hpc].
Qed.

Lemma sound_IEcall : forall (i : instr) , case_stmt segs OPS i (IEcall).
Proof.
  intros i E st ms model st' HS Hpc Hof Hx. cbn [exec] in Hx. discriminate Hx.
Qed.

Lemma sound_IFmv : forall (i : instr) (dir : fmvdir) (fmt : ffmt) (rd rs1 : r5), case_stmt segs OPS i (IFmv dir fmt rd rs1).
Proof.
  intros i dir fmt rd rs1 E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  destruct dir, fmt; cbn [exec] in Hx; injection Hx as <-; cbn [Sem.exec].
  -
    apply case_reg; [exact HS|exact Hpc|].
    rewrite den_sv_ext.
    2:{ change (width_ok 0 4). unfold width_ok. lia. }
    change (ext_word true (to_Z 0%uint63) (to_Z 4%uint63)) with (ext_word true 0 4).
    rewrite ext_word_sext32, (getf_den E st ms model rs1 HS). reflexivity.
  -
    apply case_reg; [exact HS|exact Hpc|]. exact (getf_den E st ms model rs1 HS).
  -
    apply case_freg; [exact HS|exact Hpc|]. cbn [den fop1_sem]. rewrite (getr_den E st ms model rs1 HS). reflexivity.
  -
    apply case_freg; [exact HS|exact Hpc|]. exact (getr_den E st ms model rs1 HS).
Qed.

Lemma sound_IFcvtDS : forall (i : instr) (rd rs1 : r5) (rm : bv 3), case_stmt segs OPS i (IFcvtDS rd rs1 rm).
Proof.
  intros i rd rs1 rm E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  destruct (resolve_rm_b rm) as [md|] eqn:Hrm; [|discriminate Hx].
  injection Hx as <-. cbn [Sem.exec].
  rewrite (resolve_rm_core E st ms model rm _ HS), Hrm. cbn [fread fwrite accrue].
  destruct (fp_convert (fp_format FMT_S) (fp_format FMT_D) md _) as [v fl] eqn:Hcv.
  apply case_freg_fcsr; [exact HS|exact Hpc| |].
  - cbn [den fop1_sem]. rewrite (getf_den E st ms model rs1 HS), Hcv. reflexivity.
  - cbn [c_fcsr with_pc core_of]. apply accrue_fcsr_range. exact (so_fcsr _ _ _ _ _ _ HS).
Qed.

Lemma sound_IFcvtSD : forall (i : instr) (rd rs1 : r5) (rm : bv 3), case_stmt segs OPS i (IFcvtSD rd rs1 rm).
Proof.
  intros i rd rs1 rm E st ms model st' HS Hpc Hof Hx. open_case i Hof Hx.
  destruct (resolve_rm_b rm) as [md|] eqn:Hrm; [|discriminate Hx].
  injection Hx as <-. cbn [Sem.exec].
  rewrite (resolve_rm_core E st ms model rm _ HS), Hrm. cbn [fread fwrite accrue].
  destruct (fp_convert (fp_format FMT_D) (fp_format FMT_S) md _) as [v fl] eqn:Hcv.
  apply case_freg_fcsr; [exact HS|exact Hpc| |].
  - cbn [den fop1_sem]. rewrite (getf_den E st ms model rs1 HS), Hcv. reflexivity.
  - cbn [c_fcsr with_pc core_of]. apply accrue_fcsr_range. exact (so_fcsr _ _ _ _ _ _ HS).
Qed.

Lemma sound_IOther : forall (i : instr) (i0 : instr), case_stmt segs OPS i (IOther i0).
Proof.
  intros i i0 E st ms model st' HS Hpc Hof Hx. cbn [exec] in Hx. discriminate Hx.
Qed.

End WithSegs.
End StepA.
