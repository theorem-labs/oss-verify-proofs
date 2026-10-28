(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_ContStmt LbB_TablStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT1 LbB_TablPT2 LbB_TablPT4.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Inv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Record ptent : Type := PTEnt {
    p_ra : word; p_sp : word; p_gp : word; p_tp : word;
    p_s0 : word; p_s1 : word; p_s2 : word; p_s3 : word; p_s4 : word; p_s5 : word;
    p_s6 : word; p_s7 : word; p_s8 : word; p_s9 : word; p_s10 : word; p_s11 : word;
    p_F : bvmap 5 word; p_fc : bv 32; p_m : mem; p_mo : Model;
    p_s : as_St H; p_LB : list block; p_LF : list fframe;
    p_ps : Z; p_p : Z; p_v : Z; p_b : Z; p_cap : Z; p_l : list Z; p_xs : list Z; p_pid : bptr;
    p_lo : Z; p_B : Z; p_shi : Z; p_ff : Z; p_fp : Z }.

  Definition pSP (e : ptent) : Z := bv_unsigned (p_sp e).

  Definition pS1 (e : ptent) : Z := pSP e - 192 - pSP e mod 32.
  Definition pn (e : ptent) : Z := Zlen (p_l e).
  Definition pcapm (e : ptent) : Z := capmax (Zlen (p_xs e)) (p_cap e) (pn e).

  Definition pLF (e : ptent) : list fframe := (0, p_ff e, p_fp e) :: p_LF e.

  Definition pXS (e : ptent) : list (Z * Z) :=
    [(as_FSB H, as_FSB H + AFS_FLAGS); (p_fp e, p_fp e + 1); (p_ff e, p_ff e + 64); (sh (p_ff e), sh (p_ff e) + 8)].

  Definition pXE (e : ptent) : list (Z * Z) := (p_v e, p_v e + 24) :: v4_oldx (p_b e) (4 * p_cap e) ++ pXS e.

  Definition psaved (e : ptent) : list cell :=
    [C8 (p_s11 e); C8 (p_s10 e); C8 (p_s9 e); C8 (p_s8 e); C8 (p_s7 e); C8 (p_s6 e); C8 (p_s5 e); C8 (p_s4 e);
     C8 (p_s3 e); C8 (p_s2 e); C8 (p_s1 e); C8 (p_s0 e); C8 (p_ra e)].

  Definition pslots_lo (e : ptent) : list cell := [C8 (Z_to_bv 64 (p_ff e)); C8 (Z_to_bv 64 (p_ff e))].
  Definition pslots (e : ptent) : list cell :=
    [C8 (Z_to_bv 64 (sh (p_v e))); C8 (Z_to_bv 64 (sh (p_v e + 16))); C8 (Z_to_bv 64 (p_v e + 16));
     C8 (Z_to_bv 64 (p_v e)); C8 (Z_to_bv 64 (2 ^ 61)); C8 (Z_to_bv 64 (sh (p_ps e)))].
  Definition pslotsP (e : ptent) (mL : mem) : Prop :=
    rw_cells asegs mL (pS1 e) (pslots_lo e) /\ (pn e <> 0 -> rw_cells asegs mL (pS1 e + 16) (pslots e)).

  Definition pys (e : ptent) (i : Z) : list Z :=
    p_xs e ++ List.filter (fun t => negb (t =? 0)) (firstn (Z.to_nat i) (rev (p_l e))).

  Definition ppre (e : ptent) : Prop :=
    let SP := pSP e in let v := p_v e in let LB := p_LB e in let LF := p_LF e in let lo := p_lo e in
       fresh_frame H LF 0 (p_ff e) (p_fp e) /\ (length LF < AFS_MAXLIVE_BP)%nat
    /\ (forall f, In f LF -> aframe_range H (ff_class f) (ff_addr f) (ff_flag f))
    /\ SP mod 16 = 0 /\ SP <= 2 ^ 47 /\ SP <= p_B e /\ SP <= p_shi e /\ aceil <= lo /\ lo <= SP - PT_STACK
    /\ p_tp e = Z_to_bv 64 ATP /\ bv_unsigned (p_ra e) mod 2 = 0
    /\ span_keep H LB LF SP ((v, v + 24) :: v4_oldx (p_b e) (4 * p_cap e)) (p_m e) (p_ps e) (p_p e) (pn e)
    /\ p_ps e mod 8 = 0 /\ (p_ps e + 16 <= v \/ v + 24 <= p_ps e)
    /\ spanA (p_p e) (p_l e) /\ pn e <= 48 /\ Forall (fun t => 0 <= t < 2 ^ 31) (p_l e)
    /\ v mod 8 = 0 /\ ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47))
    /\ obj_win H LB LF SP lo v 24
    /\ v4_oldblk LB (p_b e) (p_cap e) (p_pid e) /\ List.NoDup (map blk_id LB) /\ as_RHEAP H (p_s e) LB (p_m e)
    /\ (4 * pcapm e <= 2 ^ 26 /\ closs (p_cap e) (pcapm e) <= as_AL H (p_s e)) /\ lb_small LB + 3 * 64512 <= RT_SMALL_MAX
    /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + 2 <= RT_LARGE_MAX
    /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] /\ 0 <= as_AL H (p_s e)
    /\ 0 <= Zlen (p_xs e) <= p_cap e /\ (p_b e = 0 -> p_cap e = 0)
    /\ ((0 <= p_b e /\ p_b e + 4 * p_cap e <= 0x7fff7000) \/ (0x10007fff8000 <= p_b e /\ p_b e + 4 * p_cap e <= 2 ^ 47))
    /\ (p_b e <> 0 -> v + 24 <= p_b e \/ p_b e + 4 * p_cap e <= v).

  Definition pgrown (e : ptent) (LBi : list block) (bi capi : Z) (pidi : bptr) : Prop :=
    (capi = p_cap e /\ bi = p_b e /\ LBi = p_LB e /\ pidi = p_pid e)
    \/ (p_cap e < capi <= pcapm e /\ LBi = v4_newLB H (p_LB e) (p_b e) (p_pid e) pidi bi (4 * capi)
        /\ ablock_range H bi (4 * capi)).

  Definition pframe (e : ptent) (k04 : Z) (mL : mem) (sL : as_St H) (LBi : list block) (eL : word) : Prop :=
    let SP := pSP e in let S1 := pS1 e in let ff := p_ff e in let fp := p_fp e in
       mem_inv asegs mL /\ ACONST mL /\ stk asegs mL (p_lo e) SP /\ stack0 mL (p_lo e) (p_shi e)
    /\ rw_cells asegs mL (errno_addr (p_tp e)) [C4 eL] /\ as_rauxv_ok H mL (p_B e)
    /\ rw_cells asegs mL (SP - 104) (psaved e) /\ pslotsP e mL
    /\ rw_cells asegs mL (ff + 56) [C8 (Z_to_bv 64 fp)] /\ wr_at asegs mL ff 8 /\ wr_at asegs mL (sh ff) 8
    /\ wr_at asegs mL fp 1 /\ wr_at asegs mL (ff + 32) 4 /\ rw_cells asegs mL (sh ff + 4) [C1 (b8 k04)]
    /\ as_RFS H (pLF e) mL /\ as_RHEAP H sL LBi mL /\ lb_own LBi mL.

  Definition pvec (e : ptent) (ys : list Z) (mL : mem) (LBi : list block) (bi capi : Z) (pidi : bptr) : Prop :=
    let v := p_v e in
       vec32A LBi mL v bi ys capi /\ (0 < capi -> SHAD mL bi (cc_gen (4 * capi) (4 * Zlen ys)))
    /\ addressable mL v 24 /\ wr_at asegs mL v 24
    /\ v4_oldblk LBi bi capi pidi /\ pgrown e LBi bi capi pidi.

  Definition pmem (e : ptent) (ys : list Z) (k04 : Z) (mL : mem) (sL : as_St H) (LBi : list block) (bi capi : Z)
      (pidi : bptr) (eL : word) : Prop :=
       pframe e k04 mL sL LBi eL /\ pvec e ys mL LBi bi capi pidi
    /\ xpres H (p_LB e) (pSP e) (pXE e) (p_m e) mL
    /\ as_AL H sL >= as_AL H (p_s e) - closs (p_cap e) capi.

  Definition pat (e : ptent) (pc : Z) (RP : bvmap 5 word -> Prop) (ys : list Z) (k04 : Z) (cf : config) : Prop :=
    exists R mL sL LBi bi capi pidi eL,
      as_VIS H sL (cfg_ms cf) = MS R (p_F e) (Z_to_bv 64 pc) (p_fc e) None mL (seg_rom asegs) /\ rfull R
      /\ getr R 3 = p_gp e /\ getr R 4 = p_tp e /\ RP R
      /\ as_AKREL H sL cf /\ as_MPRES H (p_mo e) (cfg_model cf)
      /\ pmem e ys k04 mL sL LBi bi capi pidi eL.

  Definition pt_head (e : ptent) (i : Z) : config -> Prop :=
    pat e PT_H2 (fun R => PTH R (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i) (pys e i) 4.
  Definition pt_skip (e : ptent) (i : Z) : config -> Prop :=
    pat e PT_SKIP (fun R => PTX R (pSP e) (pS1 e) (p_ff e) (p_ps e) (p_v e) (pn e) i /\ getr R 10 = Z_to_bv 64 (-8)) (pys e (i + 1)) 4.
  Definition pt_exit (e : ptent) (cf : config) : Prop :=
    exists k, pat e PT_EXIT (fun R => getr R 8 = Z_to_bv 64 (pSP e) /\ getr R 9 = Z_to_bv 64 (pS1 e)
                                        /\ getr R 26 = Z_to_bv 64 (sh (p_ff e))) (pys e (pn e)) k cf.
End Inv.
Arguments p_ra {H} _. Arguments p_sp {H} _. Arguments p_gp {H} _. Arguments p_tp {H} _.
Arguments p_s0 {H} _. Arguments p_s1 {H} _. Arguments p_s2 {H} _. Arguments p_s3 {H} _. Arguments p_s4 {H} _.
Arguments p_s5 {H} _. Arguments p_s6 {H} _. Arguments p_s7 {H} _. Arguments p_s8 {H} _. Arguments p_s9 {H} _.
Arguments p_s10 {H} _. Arguments p_s11 {H} _. Arguments p_F {H} _. Arguments p_fc {H} _. Arguments p_m {H} _.
Arguments p_mo {H} _. Arguments p_s {H} _. Arguments p_LB {H} _. Arguments p_LF {H} _. Arguments p_ps {H} _.
Arguments p_p {H} _. Arguments p_v {H} _. Arguments p_b {H} _. Arguments p_cap {H} _. Arguments p_l {H} _.
Arguments p_xs {H} _. Arguments p_pid {H} _. Arguments p_lo {H} _. Arguments p_B {H} _. Arguments p_shi {H} _.
Arguments p_ff {H} _. Arguments p_fp {H} _.
Arguments pSP {H} _. Arguments pS1 {H} _. Arguments pn {H} _. Arguments pcapm {H} _. Arguments pLF {H} _.
Arguments psaved {H} _. Arguments pslots {H} _. Arguments pslots_lo {H} _. Arguments pslotsP {H} _ _. Arguments pys {H} _ _.

Lemma pt_firstn_S : forall (A : Type) (l : list A) (k : nat) (x : A), nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof.
  intros A l. induction l as [|y l IH]; intros k x Hk; [destruct k; discriminate|].
  destruct k as [|k]; [cbn in Hk |- *; injection Hk as ->; reflexivity|].
  cbn in Hk. change (firstn (S (S k)) (y :: l)) with (y :: firstn (S k) l). rewrite (IH k x Hk). reflexivity.
Qed.

Lemma pys_0 {HCEIL : HeapCeil} : forall H (e : ptent H), pys e 0 = p_xs e.
Proof. intros H e. unfold pys. cbn [Z.to_nat firstn List.filter]. apply app_nil_r. Qed.

Lemma pys_step {HCEIL : HeapCeil} : forall H (e : ptent H) i, 0 <= i < pn e ->
  pys e (i + 1) = pys e i ++ (if Znth (pn e - 1 - i) (p_l e) =? 0 then [] else [Znth (pn e - 1 - i) (p_l e)]).
Proof.
  intros H e i Hi. unfold pys, pn in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  assert (NTH : nth_error (rev (p_l e)) (Z.to_nat i) = Some (Znth (Zlen (p_l e) - 1 - i) (p_l e))).
  { rewrite nth_error_rev.
    replace ((Z.to_nat i <? length (p_l e))%nat) with true by (symmetry; apply Nat.ltb_lt; unfold Zlen in Hi; lia).
    unfold Znth. rewrite nth_error_nth' with (d := 0) by (unfold Zlen in Hi; lia).
    f_equal. f_equal. unfold Zlen in *. lia. }
  rewrite (pt_firstn_S _ _ _ _ NTH).
  rewrite List.filter_app, app_assoc. f_equal. cbn [List.filter].
  destruct (Znth (Zlen (p_l e) - 1 - i) (p_l e) =? 0); reflexivity.
Qed.

Lemma pt_filter_eq : forall (l : list Z),
  List.filter (fun t => negb (t =? 0)) l = base.filter (fun t => Bool.Is_true (negb (t =? 0))) l.
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. rewrite IH.
  destruct (x =? 0) eqn:E; cbn; rewrite ?E; cbn; reflexivity.
Qed.

Lemma pys_n {HCEIL : HeapCeil} : forall H (e : ptent H), pys e (pn e) = PrsGrammar.push_types (p_l e) (p_xs e).
Proof.
  intros H e. unfold pys, pn, PrsGrammar.push_types, PrsGrammar.OT_NONE.
  rewrite firstn_all2; [rewrite pt_filter_eq; reflexivity|]. rewrite length_rev. unfold Zlen. lia.
Qed.

Lemma pys_len {HCEIL : HeapCeil} : forall H (e : ptent H) i, 0 <= i ->
  Zlen (p_xs e) <= Zlen (pys e i) <= Zlen (p_xs e) + i.
Proof.
  intros H e i Hi. unfold pys, Zlen. rewrite length_app.
  pose proof (List.filter_length_le (fun t => negb (t =? 0)) (firstn (Z.to_nat i) (rev (p_l e)))) as L1.
  pose proof (firstn_le_length (Z.to_nat i) (rev (p_l e))) as L2.
  unfold Zlen in *. lia.
Qed.
