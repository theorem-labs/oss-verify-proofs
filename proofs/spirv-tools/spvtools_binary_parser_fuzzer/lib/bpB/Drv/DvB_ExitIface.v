(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatSim BSeqExec BFrame BShapeAlg BAgentLib BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BSymAux.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BazyRestrict BazySR BazyFdNodes BsLazyRun BRefExitBase BsPrintfFirst.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsExitDefs DvB_ExitKit DvB_ExitPre DvB_ExitPreT DvB_ExitPreT1 DvB_ExitPreT2 DvB_ExitPreT3.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition shw (spz : Z) : Z := (8 * (((spz - 260) / 8 + 2147450880) / 8))%Z.

Lemma shx_denot : forall E (sp : word),
  ev E 0 = sp -> (ASP_LO <= bv_unsigned sp)%Z -> (bv_unsigned sp <= ASP_HI)%Z ->
  bv_unsigned (edenot E shx) = shw (bv_unsigned sp).
Proof.
  intros E sp E0 Hlo Hhi. unfold ASP_LO, ASP_HI in *. unfold shx, shw. cbn [edenot]. rewrite E0.
  cbn [alu64 alu].
  rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  change ((-260) mod 2 ^ 64)%Z with (2 ^ 64 - 260)%Z. change (3 mod 2 ^ 64)%Z with 3%Z. change (63 mod 2 ^ 64)%Z with 63%Z.
  change (Z.land 3 63) with 3%Z. change (2147450880 mod 2 ^ 64)%Z with 2147450880%Z.
  change ((-8) mod 2 ^ 64)%Z with 18446744073709551608%Z.
  replace ((bv_unsigned sp + (2 ^ 64 - 260)) mod 2 ^ 64)%Z with (bv_unsigned sp - 260)%Z by (Z.div_mod_to_equations; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
  rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
  rewrite land_m8' by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma shw_range : forall spz, (ASP_LO <= spz <= ASP_HI)%Z -> (SHX_LO <= shw spz <= SHX_HI)%Z
  /\ (2147450880 + (spz - 4096) / 8 <= shw spz)%Z /\ (shw spz + 8 <= 2147450880 + spz / 8)%Z.
Proof. intros spz H. unfold ASP_LO, ASP_HI, SHX_LO, SHX_HI, shw in *. Z.div_mod_to_equations. lia. Qed.

Record axA (mem : word -> option byte) (sp : word) (tid can TB : Z) : Prop := AXA {
  Xsp16 : (bv_unsigned sp mod 16 = 0)%Z;
  XspLo : (ASP_LO <= bv_unsigned sp)%Z;
  XspHi : (bv_unsigned sp <= ASP_HI)%Z;
  Xstk  : stk_ok RSEGS mem sp 2560;
  Xtid  : (0 < tid < 2147483648)%Z;
  Xtidc : rdn RSEGS mem (Z_to_bv 64 0x6c57b0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  Ximg  : forall i, (0x10000 <= i < 0x91000)%Z -> mem (Z_to_bv 64 i) = None;
  Xgot  : forall i, (0x17e000 <= i < 0x186000)%Z -> mem (Z_to_bv 64 i) = None;
  Xuse2 : forall i, (0x189a08 <= i < 0x189b00)%Z -> mem (Z_to_bv 64 i) = None;
  Xglb  : forall i, (0x189be8 <= i < 0x18d980)%Z -> mem (Z_to_bv 64 i) = None;
  Xcan  : rdn RSEGS mem (Z_to_bv 64 0x6e5898) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  Xcan64 : (0 <= can < 2 ^ 64)%Z;

  XTBc  : rdn RSEGS mem (Z_to_bv 64 0x190888) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TB));
  XTBal : (TB mod 4096 = 0)%Z;
  XTBr  : (ATB_LO <= TB <= ATB_HI)%Z;
  XTBimg : (TB + 0x38e000 <= AIMGR_LO \/ AIMGR_LO + AIMGR_N <= TB)%Z;
  XTBsh  : (TB + 0x38e000 <= ASHR_LO \/ ASHR_LO + ASHR_N <= TB)%Z;
  XTBsp  : (TB + 0x38e000 + 2560 <= bv_unsigned sp)%Z;
  XAHM  : forall i, (0 <= i < 96)%Z -> mem (Z_to_bv 64 (TB + 0x1e34f8 + i)) = Some (Z_to_bv 8 0)
                                      /\ mem (Z_to_bv 64 (TB + 0x2cf448 + i)) = Some (Z_to_bv 8 0);
  XAHMw : forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8)%Z ->
            store_ok RSEGS mem (Z_to_bv 64 (TB + 0x1e34f8 + d)) m = true /\ store_ok RSEGS mem (Z_to_bv 64 (TB + 0x2cf448 + d)) m = true;

  XshM  : rdn RSEGS mem (Z_to_bv 64 0x800d0720) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  XshS  : forall a, (2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8)%Z ->
            mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0);
  Xshw  : forall (a : word) (n : nat), (0x7fffa000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x7fffa000 + 0xdb000)%Z ->
            store_ok RSEGS mem a n = true;
  Xcells : cells_ok mem xk_common }.

Definition x_vals (regs : bvmap 5 word) (sp : word) (tid : Z) (code : word) (can TB : Z) : list word :=
  [sp; Z_to_bv 64 tid; code; Z_to_bv 64 can; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]
  ++ junk_vals regs ++ [Z_to_bv 64 TB].

Lemma x_vals_length : forall regs sp tid code can TB, length (x_vals regs sp tid code can TB) = XNV.
Proof. intros. unfold x_vals. rewrite !length_app, junk_vals_length. reflexivity. Qed.

Lemma x_ev_junk : forall regs sp tid code can TB i, (8 <= i < 40)%nat ->
  ev (XENV (x_vals regs sp tid code can TB)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 8))).
Proof.
  intros regs sp tid code can TB i Hi. unfold XENV, x_vals. cbn [ev]. unfold vals_ev.
  rewrite app_assoc.
  rewrite app_nth1 by (rewrite length_app, junk_vals_length; cbn; lia).
  replace i with (length [sp; Z_to_bv 64 tid; code; Z_to_bv 64 can; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] + (i - 8))%nat at 1
    by (cbn; lia).
  rewrite app_nth2_plus. unfold junk_vals.
  rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
Qed.

Lemma x_regs_ok : forall regs sp tid code can TB,
  getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 10 = code ->
  regs_ok (XENV (x_vals regs sp tid code can TB)) x_sr regs.
Proof.
  intros regs sp tid code can TB R2 R4 R10.
  apply regs_ok_by_idx. intros i Hi.
  destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
    cbn [nth x_sr allregs32 edenot].
  1: apply getr_zero.
  2: exact R2.
  3: exact R4.
  8: exact R10.
  all: rewrite x_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
Qed.

Lemma x_know_ok : forall regs mem sp tid code can TB xk,
  axA mem sp tid can TB -> forallb cell_wf_b xk = true -> cells_ok mem xk ->
  know_ok RSEGS (XENV (x_vals regs sp tid code can TB)) mem (kn_X xk).
Proof.
  intros regs mem sp tid code can TB xk XA WF CK. destruct XA. pose proof (u64_range sp) as Hsp.
  set (E := XENV (x_vals regs sp tid code can TB)).
  assert (E0 : ev E 0 = sp) by reflexivity.
  assert (E1 : ev E 1 = Z_to_bv 64 tid) by reflexivity.
  assert (E3 : ev E 3 = Z_to_bv 64 can) by reflexivity.
  assert (E40 : ev E 40 = Z_to_bv 64 TB) by reflexivity.
  assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
  assert (UTB : bv_unsigned (Z_to_bv 64 TB) = TB) by (apply u64_lit; unfold ATB_LO, ATB_HI in *; lia).
  pose proof (shx_denot E sp E0 XspLo0 XspHi0) as SHX.
  pose proof (shw_range (bv_unsigned sp) (conj XspLo0 XspHi0)) as (SR1 & SR2 & SR3).
  unfold ASP_LO, ASP_HI, SHX_LO, SHX_HI, ATB_LO, ATB_HI in *.
  unfold kn_X. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
  2:{ apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
      - change (kn_c xk_common) with (kn_cells xk_common). apply cells_know; [vm_compute; reflexivity | exact Xcells0].
      - change (kn_c xk) with (kn_cells xk). apply cells_know; [exact WF | exact CK]. }
  unfold kn_base. unfold ASP_LO, ASP_HI, SHX_LO, SHX_HI, ATB_LO, ATB_HI.
  repeat (apply Forall_cons); [ .. | apply Forall_nil ].
  - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
  - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
  - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp 2560); [exact E0 | assumption | lia].
  - apply krange_intro. cbn [edenot]. rewrite E1, u64_lit by lia. lia.
  - apply kimg_intro; [lia | lia | assumption].
  - apply kimg_intro; [lia | lia | assumption].
  - apply kimg_intro; [lia | lia | assumption].
  - apply kimg_intro; [lia | lia | assumption].
  - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E1 | lia | lia | rewrite Z0; lia
      | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
  - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E3 | lia | lia | rewrite Z0; lia
      | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
  - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E40 | lia | lia | rewrite Z0; lia
      | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
  - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E40, UTB. assumption.
  - apply krange_intro. cbn [edenot]. rewrite E40, UTB. lia.
  - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite E40, UTB, Z0. unfold AIMGR_LO, AIMGR_N in *. lia.
  - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite E40, UTB, Z0. unfold AIMGR_LO, AIMGR_N in *. lia.
  - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite E40, UTB, Z0. unfold ASHR_LO, ASHR_N in *. lia.
  - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite E40, UTB, Z0. unfold ASHR_LO, ASHR_N in *. lia.
  - cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. cbn [edenot]. rewrite E40, UTB, SHX. unfold ASHR_LO, ASHR_N in *. lia.
  - cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. cbn [edenot]. rewrite E40, UTB, SHX. unfold ASHR_LO, ASHR_N in *. lia.
  - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite E40, UTB, E0. lia.
  - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. rewrite E40, UTB, E0. lia.
  - eapply (kzero_intro RSEGS _ mem (EVar 40) (Z_to_bv 64 TB) 0x1e34f8 (ELit 96) 96);
      [exact E40 | reflexivity | rewrite UTB; lia | lia | rewrite UTB; lia |].
    intros i Hi. rewrite UTB. apply (XAHM0 i Hi).
  - eapply (kzero_intro RSEGS _ mem (EVar 40) (Z_to_bv 64 TB) 0x2cf448 (ELit 96) 96);
      [exact E40 | reflexivity | rewrite UTB; lia | lia | rewrite UTB; lia |].
    intros i Hi. rewrite UTB. apply (XAHM0 i Hi).
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite E40, UTB.
    split; [lia|]. intros d m Hd Hm. apply (XAHMw0 d m Hd Hm).
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite E40, UTB.
    split; [lia|]. intros d m Hd Hm. apply (XAHMw0 d m Hd Hm).
  - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia
      | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
  - eapply (kzero_intro RSEGS _ mem shx (edenot E shx) 0 (ELit 8) 8);
      [reflexivity | reflexivity | rewrite SHX; lia | lia | rewrite SHX; lia |].
    intros i Hi. rewrite SHX. apply XshS0. lia.
  - apply krange_intro. rewrite SHX. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
  - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
    split; [lia|]. intros d m Hd Hm. apply Xshw0; rewrite u64_lit by lia; lia.
Qed.

Theorem as_exit_U `{fx : DFP} : forall regs mem msF mo L S Zr (sp code : word) (tid can TB : Z),
  axA mem sp tid can TB -> cells_ok mem xk_U ->
  getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 10 = code ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem (seg_rom RSEGS) ->
  realizes RSEGS (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
Proof.
  intros regs mem msF mo L S Zr sp code tid can TB XA CK R2 R4 R10 OK RS.
  apply (ax_clean xk_U pre_U_ok (x_vals regs sp tid code can TB) regs mem msF mo L S Zr);
    [ apply x_vals_length | apply x_regs_ok; assumption | apply x_know_ok; [exact XA | vm_compute; reflexivity | exact CK]
    | exact OK | exact RS ].
Qed.

Theorem as_exit_U2 `{fx : DFP} : forall regs mem msF mo L S Zr (sp code : word) (tid can TB : Z),
  axA mem sp tid can TB -> cells_ok mem xk_U2 ->
  getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 10 = code ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem (seg_rom RSEGS) ->
  realizes RSEGS (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
Proof.
  intros regs mem msF mo L S Zr sp code tid can TB XA CK R2 R4 R10 OK RS.
  apply (ax_clean xk_U2 pre_U2_ok (x_vals regs sp tid code can TB) regs mem msF mo L S Zr);
    [ apply x_vals_length | apply x_regs_ok; assumption | apply x_know_ok; [exact XA | vm_compute; reflexivity | exact CK]
    | exact OK | exact RS ].
Qed.

Theorem as_exit_T0 `{fx : DFP} : forall regs mem msF mo L S Zr (sp code : word) (tid can TB : Z),
  axA mem sp tid can TB -> cells_ok mem xk_T0 ->
  getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 10 = code ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem (seg_rom RSEGS) ->
  realizes RSEGS (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
Proof.
  intros regs mem msF mo L S Zr sp code tid can TB XA CK R2 R4 R10 OK RS.
  apply (ax_clean xk_T0 pre_T0_ok (x_vals regs sp tid code can TB) regs mem msF mo L S Zr);
    [ apply x_vals_length | apply x_regs_ok; assumption | apply x_know_ok; [exact XA | vm_compute; reflexivity | exact CK]
    | exact OK | exact RS ].
Qed.

Theorem as_exit_T `{fx : DFP} : forall (j : Z) regs mem msF mo L S Zr (sp code : word) (tid can TB : Z) (pending : list byte),
  (1 <= j <= 3)%Z ->
  axA mem sp tid can TB -> cells_ok mem (xk_T j) ->
  length pending = Z.to_nat (2 * j) -> rdn RSEGS mem (Z_to_bv 64 ASTDOUT_BUF) (length pending) = Some pending ->
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 10 = code ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem (seg_rom RSEGS) ->
  realizes RSEGS (mkCfg msF mo) (t_emit (map (WriteEv (Z_to_bv 64 1)) pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo))).
Proof.
  intros j regs mem msF mo L S Zr sp code tid can TB pending Hj XA CK Hlen Hpend Hfd R2 R4 R10 OK RS.
  assert (Hv : vals_ev (x_vals regs sp tid code can TB) 2 = code) by reflexivity.
  rewrite <- Hv.
  assert (HJ : j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct HJ as [HJ|[HJ|HJ]]; subst j.
  - apply (ax_flush_1 (x_vals regs sp tid code can TB) regs mem msF mo L S Zr pending);
      [ apply x_vals_length | apply x_regs_ok; assumption | apply x_know_ok; [exact XA | vm_compute; reflexivity | exact CK]
      | exact Hlen | exact Hpend | exact Hfd | exact OK | exact RS ].
  - apply (ax_flush_2 (x_vals regs sp tid code can TB) regs mem msF mo L S Zr pending);
      [ apply x_vals_length | apply x_regs_ok; assumption | apply x_know_ok; [exact XA | vm_compute; reflexivity | exact CK]
      | exact Hlen | exact Hpend | exact Hfd | exact OK | exact RS ].
  - apply (ax_flush_3 (x_vals regs sp tid code can TB) regs mem msF mo L S Zr pending);
      [ apply x_vals_length | apply x_regs_ok; assumption | apply x_know_ok; [exact XA | vm_compute; reflexivity | exact CK]
      | exact Hlen | exact Hpend | exact Hfd | exact OK | exact RS ].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
