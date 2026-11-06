(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/CJ/RL/GX/G_vsnprintf.v, with its module paths, addresses and numbers changed; 361 of its 430 lines of code are new or changed and 229 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: vfprintf (plain 0x19ff4 = sym 0x7f000400, 432 bytes) on link's memory
   FILE, in CJ's vocabulary: `vfprintf_mf_proof : vfprintf_mf_stmt` (the statement is lib/Prog/mf_sink_c.v).

   The walk is the one of lib/CJ/RL/GX/G_vfprintf_snf.v `vfprintf_snf_proof` over the same 108-instruction
   list (`vfprintf_prog`, checked against link's image through `CODE_vfprintf`), on the other arm of +0xa0:
   - pass 1: printf_core with no FILE (`PC1`);
   - the lock is -1 (+0x70 skips __lockfile and +0x168 skips __unlockfile);
   - F_ERR is cleared in the stored flags word (+0x90..+0x9c);
   - buf_size = 1024, so +0xa0 does not swap in vfprintf's own 80-byte buffer and saved_buf = 0;
   - wend = 0: __towrite (+0xd8) sets the window and stores the orientation `mode | (mode - 1)`, which is -1
     for mode 0 or -1 (`towrite_mf`); wend <> 0: the window is already active;
   - pass 2: printf_core on f with the sink `SINK_mf` (`PC` at Fp = f, B = f + 280, BS = 1024,
     RC = sp - 360 (empty), RE = 1 (empty));
   - no flush (saved_buf = 0), the old F_ERR is put back (+0x14c..+0x164): the flags word is as it was;
   - the canary check and the return. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import SFModel Arr ITree Nodes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import G_towrite G_vfprintf_snf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import StoreCache.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mf_sink_c.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* the step tactics of G_vfprintf_snf.v :160-179 (they are Local there) *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* ==========================================================================
   The FILE as the sink reads it (lib/CJ/RL/G/G_fwritex.v FILE_cells: first byte, 31 bytes, wend, wpos,
   96 bytes, lbf) and as __towrite reads it (G_towrite.v towrite_file), from `mf_file`
   ========================================================================== *)

Definition mf_fl0 (fs : word) : byte := hd (Z_to_bv 8 0) (le4 fs).
Definition mf_j1 (fs : word) (jp jc : list byte) : list byte :=
  tl (le4 fs) ++ jp ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ jc.
Definition mf_j2 (j48 : list byte) (wb : word) (j64 : list byte) (buf : Z) (j104 : list byte) (md : word) : list byte :=
  j48 ++ le8 wb ++ j64 ++ le8 (Z_to_bv 64 buf) ++ le8 (Z_to_bv 64 1024) ++ j104 ++ le4 md ++ le4 (Z_to_bv 64 (-1)).
Definition mf_jt (lbf : word) (jx : list byte) : list byte := le4 (Z_to_bv 64 (-1)) ++ le4 lbf ++ jx.
(* the orientation vfprintf leaves *)
Definition mf_md (we mode : word) : word := if bv_unsigned we =? 0 then Z_to_bv 64 4294967295 else mode.

Ltac mrecast_bytes := cbn [cells_bytes cbytes]; repeat rewrite <- app_assoc; cbn [app]; reflexivity.

(* ==========================================================================
   Bits of the flags word: +0x98 stores (sx32 fl) & ~F_ERR, +0x150 ors the old F_ERR back
   ========================================================================== *)

Lemma le4_eq_mod : forall v w : word, bv_unsigned v mod 2^32 = bv_unsigned w mod 2^32 -> le4 v = le4 w.
Proof.
  intros v w E. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned w) 32) by lia.
  rewrite E. reflexivity.
Qed.

Lemma sx32_mod32 : forall w : word, bv_unsigned (sx32 w) mod 2^32 = bv_unsigned w mod 2^32.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
  change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lit_mod32 : forall e : Z, bv_unsigned (Z_to_bv 64 e) mod 2^32 = e mod 2^32.
Proof.
  intros e. rewrite unsigned_lit_wrap. change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land_low32 : forall a c, Z.land (Z.ones 32) c = c -> Z.land a c = Z.land (a mod 2^32) c.
Proof. intros a c H. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, H. reflexivity. Qed.

Lemma flags_restore_Z : forall a s : Z,
  s mod 2^32 = Z.land a 18446744073709551583 mod 2^32 ->
  Z.lor s (Z.land a 32) mod 2^32 = a mod 2^32.
Proof.
  intros a s H. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl | Hg].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.land_spec.
    assert (Ts : Z.testbit s i = Z.testbit (Z.land a 18446744073709551583) i).
    { rewrite <- (Z.mod_pow2_bits_low s 32 i) by lia. rewrite H. apply Z.mod_pow2_bits_low. lia. }
    rewrite Ts, Z.land_spec.
    assert (TN : Z.testbit 18446744073709551583 i = negb (5 =? i)).
    { replace 18446744073709551583 with (Z.lxor (Z.ones 64) (2^5)) by (vm_compute; reflexivity).
      rewrite Z.lxor_spec, Z.ones_spec_low by lia. rewrite Z.pow2_bits_eqb by lia. reflexivity. }
    assert (T32 : Z.testbit 32 i = (5 =? i)).
    { replace 32 with (2^5) by reflexivity. apply Z.pow2_bits_eqb. lia. }
    rewrite TN, T32. destruct (Z.testbit a i), (5 =? i); reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma hd_le4 : forall v : word, hd (Z_to_bv 8 0) (le4 v) = Z_to_bv 8 (bv_unsigned v).
Proof. intros v. reflexivity. Qed.

Lemma len_tl_le4 : forall v : word, length (tl (le4 v)) = 3%nat.
Proof. intros v. reflexivity. Qed.

Lemma fl0_clear : forall x : Z, Z.land (bv_unsigned (mf_fl0 (Z_to_bv 64 (Z.land x 18446744073709551583)))) 32 = 0.
Proof.
  intros x. unfold mf_fl0. rewrite hd_le4, Z_to_bv_unsigned. change (bv_wrap 8 ?y) with (y mod 2^8).
  rewrite unsigned_lit_wrap. rewrite <- !Z.land_ones by lia. rewrite <- !Z.land_assoc.
  match goal with |- Z.land x ?c = 0 => replace c with 0 by (vm_compute; reflexivity) end.
  apply Z.land_0_r.
Qed.

Lemma fsw_nowr : forall fl : word, Z.land (bv_unsigned fl) 8 = 0 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 fl)) 18446744073709551583))) 8 = 0.
Proof.
  intros fl H. rewrite unsigned_lit_wrap, <- Z.land_ones by lia. rewrite <- !Z.land_assoc.
  replace (Z.land 18446744073709551583 (Z.land (Z.ones 64) 8)) with 8 by (vm_compute; reflexivity).
  rewrite (land_low32 _ 8) by (vm_compute; reflexivity). rewrite sx32_mod32.
  rewrite <- land_low32 by (vm_compute; reflexivity). exact H.
Qed.

Lemma fsw_err_clear : forall x : Z,
  Z.land (bv_unsigned (sx32 (Z_to_bv 64 (Z.land x 18446744073709551583)))) 32 = 0.
Proof.
  intros x. rewrite (land_low32 _ 32) by (vm_compute; reflexivity). rewrite sx32_mod32, lit_mod32.
  rewrite <- land_low32 by (vm_compute; reflexivity). rewrite <- Z.land_assoc.
  replace (Z.land 18446744073709551583 32) with 0 by (vm_compute; reflexivity). apply Z.land_0_r.
Qed.

Section Img.
  Context {IMG : RImg}.

Lemma mf_file_eq : forall m f fl jp jc we wp j48 wb j64 buf j104 md lbf jx we' wp' wb' md',
  rw_cells img_segs m f (mf_file fl jp jc we wp j48 wb j64 buf j104 md lbf jx) ->
  we = we' -> wp = wp' -> wb = wb' -> md = md' ->
  rw_cells img_segs m f (mf_file fl jp jc we' wp' j48 wb' j64 buf j104 md' lbf jx).
Proof. intros. subst. assumption. Qed.

Lemma rw_cells_C4_head : forall m A v v' cs,
  rw_cells img_segs m A (C4 v :: cs) -> le4 v = le4 v' -> rw_cells img_segs m A (C4 v' :: cs).
Proof.
  intros m A v v' cs [[W B] R] E. split; [split|].
  - destruct W as [_ W]. split; [exact I | exact W].
  - cbn [cells_bytes cbytes] in *. rewrite <- E. exact B.
  - exact R.
Qed.

Lemma mf_to_tw : forall m f fl jp jc we wp j48 wb j64 buf j104 md lbf jx,
  rw_cells img_segs m f (mf_file fl jp jc we wp j48 wb j64 buf j104 md lbf jx) ->
  rw_cells img_segs m f (towrite_file fl jp (Z_to_bv 64 0) (Z_to_bv 64 0) jc we wp j48 wb j64 buf 1024 j104 md (mf_jt lbf jx)).
Proof.
  intros m f fl jp jc we wp j48 wb j64 buf j104 md lbf jx H.
  pose proof (proj1 (proj1 H)) as W. unfold mf_file in W. cbn [cells_wf cell_wf] in W.
  eapply rw_cells_recast; [exact H | |].
  - unfold towrite_file, mf_jt. cbn [cells_wf cell_wf]. rewrite !length_app, !length_le4. intuition lia.
  - unfold towrite_file, mf_file, mf_jt. mrecast_bytes.
Qed.

Lemma tw_to_mf : forall m f fl jp jc we wp j48 wb j64 buf j104 md lbf jx,
  rw_cells img_segs m f (towrite_file fl jp (Z_to_bv 64 0) (Z_to_bv 64 0) jc we wp j48 wb j64 buf 1024 j104 md (mf_jt lbf jx)) ->
  rw_cells img_segs m f (mf_file fl jp jc we wp j48 wb j64 buf j104 md lbf jx).
Proof.
  intros m f fl jp jc we wp j48 wb j64 buf j104 md lbf jx H.
  pose proof (proj1 (proj1 H)) as W. unfold towrite_file, mf_jt in W. cbn [cells_wf cell_wf] in W.
  rewrite !length_app, !length_le4 in W.
  eapply rw_cells_recast; [exact H | |].
  - unfold mf_file. cbn [cells_wf cell_wf]. intuition lia.
  - unfold towrite_file, mf_file, mf_jt. mrecast_bytes.
Qed.

Lemma mf_to_sink : forall m f fs jp jc WE WP j48 wb j64 buf j104 md lbf jx,
  rw_cells img_segs m f (mf_file fs jp jc (Z_to_bv 64 WE) (Z_to_bv 64 WP) j48 wb j64 buf j104 md lbf jx) ->
  rw_cells img_segs m f (FILE_cells (mf_fl0 fs) (mf_j1 fs jp jc) WE WP (mf_j2 j48 wb j64 buf j104 md) lbf)
  /\ rw_cells img_segs m (f + 148) [CB 84 jx].
Proof.
  intros m f fs jp jc WE WP j48 wb j64 buf j104 md lbf jx H.
  pose proof (proj1 (proj1 H)) as W. unfold mf_file in W. cbn [cells_wf cell_wf] in W.
  unfold mf_file in H.
  apply (proj1 (rw_cells_app img_segs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] _)) in H.
  destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2.
  split.
  - eapply rw_cells_recast; [exact H1 | |].
    + unfold FILE_cells, mf_j1, mf_j2. cbn [cells_wf cell_wf]. rewrite !length_app, ?length_le4, ?length_le8, len_tl_le4.
      intuition (try reflexivity; lia).
    + unfold FILE_cells, mf_fl0, mf_j1, mf_j2. mrecast_bytes.
  - eapply rwc_eq; [exact H2 | lia].
Qed.

Lemma sink_to_mf : forall m f fs jp jc WE WP j48 wb j64 buf j104 md lbf jx,
  rw_cells img_segs m f (FILE_cells (mf_fl0 fs) (mf_j1 fs jp jc) WE WP (mf_j2 j48 wb j64 buf j104 md) lbf) ->
  rw_cells img_segs m (f + 148) [CB 84 jx] ->
  length jp = 4%nat -> length jc = 8%nat -> length j48 = 8%nat -> length j64 = 24%nat -> length j104 = 32%nat ->
  rw_cells img_segs m f (mf_file fs jp jc (Z_to_bv 64 WE) (Z_to_bv 64 WP) j48 wb j64 buf j104 md lbf jx).
Proof.
  intros m f fs jp jc WE WP j48 wb j64 buf j104 md lbf jx H1 H2 L1 L2 L3 L4 L5.
  pose proof (G_printf_core_common.rw_CB_length _ _ _ _ H2) as LX.
  assert (H : rw_cells img_segs m f (FILE_cells (mf_fl0 fs) (mf_j1 fs jp jc) WE WP (mf_j2 j48 wb j64 buf j104 md) lbf ++ [CB 84 jx])).
  { apply (proj2 (rw_cells_app img_segs _ _ _ _)). split; [exact H1|]. eapply rwc_eq; [exact H2|]. unfold FILE_cells. cbn. lia. }
  eapply rw_cells_recast; [exact H | |].
  - unfold mf_file. cbn [cells_wf cell_wf]. intuition lia.
  - unfold mf_file, FILE_cells, mf_fl0, mf_j1, mf_j2. cbn [app]. mrecast_bytes.
Qed.

Lemma topok_mf : topok_stmt TOPOK_mf.
Proof. intros a b _ _. exact I. Qed.

  Context {CODE_vfprintf : CodeAtT img_segs (sym 0x7f000400) (PROGAT_CODE_vfprintf IMG)}.
  Context {RB_vfprintf : RelCode (sym 0x7f000400) 432}.
  Context {RN_printf_core : RelNear (sym 0x7f000400) (sym 0x18704)}.
  Context {RN_lockfile : RelNear (sym 0x7f000400) (sym 0x7f000700)}.
  Context {RN_towrite : RelNear (sym 0x7f000400) (sym 0x17f40)}.
  Context {RN_unlockfile : RelNear (sym 0x7f000400) (sym 0x7f000800)}.
  Context {RN_stack_chk_fail : RelNear (sym 0x7f000400) (sym 0x15f04)}.
  Context {CODE_towrite : CodeAtT img_segs (sym 0x17f40) (PROGAT_CODE_towrite IMG)}.
  Context {RB_towrite : RelCode (sym 0x17f40) 84}.
  Context {RS_got_ssp : RelSym (sym 0x22e18)}.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Context {RS_35000 : RelSym (sym 0x35000)}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)}.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)}.
  Context {RQ_22e18 : ZFact (0x14000 <= sym 0x22e18)}.
  Let rp_22e18 : 0 <= sym 0x22e18 < 2^30 := @rel_sym_pf _ RS_got_ssp.
  Let rp_34288 : 0 <= sym 0x34288 < 2^30 := @rel_sym_pf _ RS_34288.
  Let rp_35000 : 0 <= sym 0x35000 < 2^30 := @rel_sym_pf _ RS_35000.
  Let rl0_0 : sym 0x22e18 + 8 <= sym 0x34288 := @zfact_pf _ RL0_0.
  Let rl0_1 : sym 0x34288 + 8 <= sym 0x35000 := @zfact_pf _ RL0_1.
  Let rq_22e18 : 0x14000 <= sym 0x22e18 := @zfact_pf _ RQ_22e18.
  Context (PC : printf_core_heap_all).
  Context (PC1 : printf_core1_stmt).
  Context (MF_FRAME : forall f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES,
            sink_frame_stmt f (f + 280) 1024 RC RCS RE RES (SINK_mf f k OM pb fl0 j1 j2 lbfw jx)).
  Context (MF_FLAGS : forall f k OM pb fl0 j1 j2 lbfw jx, sink_flags_stmt f (SINK_mf f k OM pb fl0 j1 j2 lbfw jx)).
  Context (MF_OUT : forall f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES,
            out_stmt f (f + 280) 1024 RC RCS RE RES (SINK_mf f k OM pb fl0 j1 j2 lbfw jx) TOPOK_mf (OUT_snf OM)).

(* __towrite (plain 0x19950 = sym 0x17f40) as G_towrite.v `towrite_x_proof` walks it, with the orientation
   it stores: musl `f->mode |= f->mode - 1` is -1 (as 32 bits) when the mode was 0 or -1. *)
Definition towrite_mf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (flags : word) (jp : list byte) (rpos rend : word) (jc : list byte) (wend wpos : word)
         (jz : list byte) (wbase : word) (jf : list byte) (buf bufsize : Z) (jl : list byte) (mode : word) (jt : list byte),
    rw_cells img_segs m (bv_unsigned a0) (towrite_file flags jp rpos rend jc wend wpos jz wbase jf buf bufsize jl mode jt) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    0 <= buf -> buf + bufsize < 2^64 -> 0 <= bufsize ->
    (bv_unsigned mode = 0 \/ bv_unsigned mode = 4294967295) ->
    mem_inv img_segs m ->
    evt img_segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom img_segs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 232)] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
                 /\ rw_cells img_segs m' (bv_unsigned a0)
                      (towrite_file flags jp (Z_to_bv 64 0) (Z_to_bv 64 0) jc (Z_to_bv 64 (buf + bufsize)) (Z_to_bv 64 buf)
                                    jz (Z_to_bv 64 buf) jf buf bufsize jl (Z_to_bv 64 4294967295) jt))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (sym 0x17f40)) fc None m (seg_rom img_segs)).

Lemma towrite_mf : towrite_mf_stmt.
Proof.
  unfold towrite_mf_stmt. intros until jt. intros FC NOWR B0 BHI BS0 MD MI.
  destruct MD as [M0 | M1];
    [ replace mode with (Z_to_bv 64 0) in FC by (rewrite <- M0; apply Z_to_bv_bv_unsigned)
    | replace mode with (Z_to_bv 64 4294967295) in FC by (rewrite <- M1; apply Z_to_bv_bv_unsigned) ];
    clear dependent mode;
    pose proof (rw_cells_bound _ _ _ _ FC) as FB; cbn [cells_size towrite_file csize Nat.add] in FB;
    set (Fp := bv_unsigned a0) in *;
    replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity);
    pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU; pose proof (wmono_refl img_segs m) as WM;
    unfold towrite_file in FC;
    (assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z);
     [ unfold zx32; rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia);
       rewrite <- Z.land_ones by lia;
       rewrite <- Z.land_assoc; change (Z.land (Z.ones 32) 8) with 8%Z; exact NOWR | ]);
    do 5 zs; rewrite FL8; zs; zs; if_lit;
    do 10 zs;
    apply evt_done; repeat (lazymatch goal with |- ex _ => eexists end);
    (split; [cbv delta [mkR]; reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]);
    unfold towrite_file;
    (match goal with H : rw_cells _ _ Fp _ |- _ =>
       apply (proj1 (rw_cells_app img_segs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _] _)) in H;
       destruct H as [H1 H2];
       apply (proj2 (rw_cells_app img_segs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _] _)); split; [exact H1|];
       eapply rw_cells_C4_head; [exact H2|]; apply le4_eq_mod; vm_compute; reflexivity
     end).
Qed.

Theorem vfprintf_mf_proof : vfprintf_mf_stmt.
Proof.
  unfold vfprintf_mf_stmt. intros until o. cbv zeta.
  intros -> -> -> FH BUF LPB LTOT WST FL8 MODE LBF BY HF P1 VAA AOK MODEL HOM HKOM ST LO GLO QHI SSP MI FRM HA HA0
         QVA VAHI F0 FLO FIMG.
  unfold VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. unfold zb in AB. rewrite length_map in AB.
  pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in HA, VAHI.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof rp_22e18. pose proof rp_34288. pose proof rp_35000. pose proof rl0_0. pose proof rl0_1. pose proof rq_22e18.
  pose proof (proj1 (proj1 FH)) as FW. unfold mf_file in FW. cbn [cells_wf cell_wf] in FW.
  destruct FW as (_ & LJP & _ & _ & LJC & _ & _ & LJ48 & _ & LJ64 & _ & _ & LJ104 & _ & _ & _ & LJX & _).
  pose proof (munch_refl [(lo, bv_unsigned sp); (f, f + 232); (f + 280, f + 1304)] m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp); (f, f + 232)] m) as MU2.
  stash BY. stash VAA. stash AOK. stash MODEL. stash BUF. stash WST. stash MODE. stash LBF. stash FL8.
  unfold mf_file in FH.
  carve_frame 368%nat ST.
  do 25 zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BY0 : bytes_at img_segs mm A (zb fmt))
      by (unfold hideP in BY; eapply bytes_at_transport; [exact BY | exact MU2 |];
          cbn [disjoint_from]; unfold zb; rewrite length_map; lia)
  end.
  zs.
  eapply evt_cut.
  { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
      [ exact BY0 | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
      | split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
  cbv beta. intros ms' P. clear BY0. unfold printf_core1_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 21%nat; intros x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m1 -> MUc WMc MIc STc SSPc).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m1 MUc WMc; clear MUc WMc; try clear MI end.
  aret_pc.
  clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  (* +104 not taken; +108 lock; +112 taken (lock < 0) -> +140 s3 = 1; +144..+156 flags &= ~F_ERR;
     +160 buf_size <> 0; +164 wend; +168 s4 = 0 *)
  zs. if_lit. zs. zs. if_lit. zs. do 4 zs. zs. if_lit. zs. zs.
  lazymatch type of FH with rw_cells _ _ _ (C4 ?v :: _) => remember v as FSW eqn:EFSW end.
  lazymatch goal with
  | |- evt ?segs ?Q (MS (mkR _ ?sp0 ?gp0 ?tp0 _ _ _ ?s0_ ?s1_ _ _ _ _ _ _ _ _ ?s2_ ?s3_ ?s4_ ?s5_ ?s6_ ?s7_ ?s8_ ?s9_ ?s10_ ?s11_ _ _ _ _) ?F0 _ ?fc0 ?rv0 ?m2 ?ro0) =>
    assert (CORE : forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (mc : mem),
      munch [(f, f + 232)] m2 mc -> wmono segs m2 mc -> mem_inv segs mc ->
      rw_cells segs mc f (mf_file FSW jp jc (Z_to_bv 64 (f + 1304)) (Z_to_bv 64 (f + 280 + k)) j48 (Z_to_bv 64 (f + 280)) j64
                                  (f + 280) j104 (mf_md we mode) lbf jx) ->
      evt segs Q (MS (mkR xra sp0 gp0 tp0 xt0 xt1 xt2 s0_ s1_ xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ xt3 xt4 xt5 xt6)
                     F0 (Z_to_bv 64 (sym 0x7f000400 + 240)) fc0 rv0 mc ro0))
  end.
  { intros xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mc MUm WMm MIm FHm.
    clear FH.
    lazymatch type of MUm with munch _ ?mm _ =>
      repeat match goal with H : mem_inv _ ?mx |- _ => constr_eq mx mm; clear H end;
      transport_after_call img_segs mm mc MUm WMm end.
    clear MUm WMm.
    (* +240..+256 the arguments of pass 2; +260 jal printf_core *)
    do 5 zs. zs.
    apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    unfold hideP in BY, VAA, AOK, MODEL, BUF, LBF.
    assert (BY2 : bytes_at img_segs mc A (zb fmt)).
    { eapply bytes_at_transport; [exact BY | exact MU2 |]. cbn [disjoint_from]. unfold zb. rewrite length_map. lia. }
    assert (VAA2 : bytes_at img_segs mc VA (u64s slots)).
    { eapply bytes_at_transport; [exact VAA | exact MU2 |]. cbn [disjoint_from]. rewrite LU. lia. }
    assert (BUF2 : rw_cells img_segs mc (f + 280) [CB (length pb) pb; CB (length bjunk) bjunk]).
    { eapply rw_cells_transport; [exact BUF | exact MU2 | exact WM |]. cbn [disjoint_from cells_size csize]. lia. }
    assert (AOK2 : args_ok f (f + 280) 1024 (bv_unsigned sp + -360) 0 1 0 mc lo (bv_unsigned sp + -368) (bv_unsigned sp + -368) slots args).
    { eapply args_ok_rebase; [exact AOK | | lia | right; reflexivity | right; split; reflexivity | left; lia | left; lia].
      eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside] in *. tauto. }
    clear MU2 BY VAA AOK BUF.
    assert (SNK : SINK_mf f k OM pb (mf_fl0 FSW) (mf_j1 FSW jp jc)
                    (mf_j2 j48 (Z_to_bv 64 (f + 280)) j64 (f + 280) j104 (mf_md we mode)) lbf jx mc []).
    { assert (FC1 : rw_cells img_segs mc f (FILE_cells (mf_fl0 FSW) (mf_j1 FSW jp jc)
                      (f + 280 + Z.of_nat (length pb) + Z.of_nat (length bjunk)) (f + 280 + Z.of_nat (length pb))
                      (mf_j2 j48 (Z_to_bv 64 (f + 280)) j64 (f + 280) j104 (mf_md we mode)) lbf)
                    /\ rw_cells img_segs mc (f + 148) [CB 84 jx]).
      { apply mf_to_sink.
        replace (f + 280 + Z.of_nat (length pb) + Z.of_nat (length bjunk)) with (f + 1304) by lia.
        replace (f + 280 + Z.of_nat (length pb)) with (f + 280 + k) by lia. exact FHm. }
      destruct FC1 as [FC1 R148].
      unfold SINK_mf. exists bjunk. cbn [zb map]. rewrite !app_nil_r.
      split.
      { unfold wfile. split; [exact FC1|]. split; [exact BUF2|]. split; [rewrite EFSW; apply fl0_clear|].
        split; [exact LBF|]. lia. }
      split; [exact R148|]. unfold zlength, GLOBALS_TOP. cbn [length]. lia. }
    pose proof (PC (list Z) f (f + 280) 1024 (bv_unsigned sp + -360) 0 1 0
                   (SINK_mf f k OM pb (mf_fl0 FSW) (mf_j1 FSW jp jc)
                      (mf_j2 j48 (Z_to_bv 64 (f + 280)) j64 (f + 280) j104 (mf_md we mode)) lbf jx)
                   TOPOK_mf (OUT_snf OM) OUTFP_snf
                   (MF_FRAME _ _ _ _ _ _ _ _ _ _ _ _ _) (MF_FLAGS _ _ _ _ _ _ _ _ _) topok_mf
                   (MF_OUT _ _ _ _ _ _ _ _ _ _ _ _ _)) as PC2.
    unfold printf_core_stmt_heap in PC2.
    assert (PCALL : forall Q ms, implM img_segs (printf_model (OUT_snf OM) OUTFP_snf fmt args) [] Q ms -> evt img_segs (Q r o) ms).
    { intros Q ms HQ. unfold implM in HQ. rewrite MODEL in HQ. exact HQ. }
    clear MODEL.
    eapply evt_cut.
    { apply PCALL.
      eapply PC2 with (st := []) (VA := VA) (i := 0) (slots := slots) (args := args) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_mf, zlength;
        first [ exact SNK | exact BY2 | exact HF | reflexivity | (replace (VA + 8 * 0) with VA by lia; exact APC)
              | exact VAA2 | (cbn [Z.to_nat skipn]; exact AOK2) | apply fpcalls_snf | exact STc
              | (split; [exact SSP1 | exact SSP2]) | assumption | exact I | lia ]. }
    cbv beta. intros ms' P. clear PC2 PCALL BY2 VAA2 AOK2 BUF2 SNK APC.
    unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
    (nelim P 29%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' apv m3 -> MUc WMc MI3 FRM' FOK ST3 SNK3 SSP3 APC3 Hr).
    unfold SR in MUc. cbn [app] in MUc.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m3 MUc WMc; clear MUc WMc; try clear MIm end.
    aret_pc.
    (* +264 s1 = ret; +268 s5 &= F_ERR; +272 saved_buf = 0 -> +332 *)
    zs. zs. zs. if_lit.
    destruct SNK3 as (bj & WF3 & R148 & LPB3 & LEN3 & HO3 & HKO3 & _).
    destruct WF3 as (FC3 & BUF3 & _).
    assert (FH3 : rw_cells img_segs m3 f (mf_file FSW jp jc (Z_to_bv 64 (f + 1304)) (Z_to_bv 64 (f + 280 + k + zlength o)) j48
                       (Z_to_bv 64 (f + 280)) j64 (f + 280) j104 (mf_md we mode) lbf jx)).
    { pose proof (sink_to_mf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC3 R148 LJP LJC LJ48 LJ64 LJ104) as X.
      assert (LO3 : length (pb ++ zb o) = (length pb + length o)%nat) by (rewrite length_app; unfold zb; rewrite length_map; reflexivity).
      rewrite LO3 in X. unfold zlength in LEN3, HO3 |- *.
      replace (f + 280 + Z.of_nat (length pb + length o) + Z.of_nat (length bj)) with (f + 1304) in X by lia.
      replace (f + 280 + Z.of_nat (length pb + length o)) with (f + 280 + k + Z.of_nat (length o)) in X by lia.
      exact X. }
    clear FC3 R148.
    unfold mf_file in FH3.
    (* +332..+356: flags |= old F_ERR, a0 = (F_ERR ? -1 : 0) | ret *)
    do 7 zs.
    zs. if_lit.
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    replace (Z.land (bv_unsigned (sx32 FSW)) 32) with 0 by (rewrite EFSW; symmetry; apply fsw_err_clear).
    replace (Z.land (bv_swrap 32 (Z.b2z (0 <? 1) + -1)) 18446744073709551615) with 0 by (vm_compute; reflexivity).
    rewrite Z.lor_0_l.
    replace (Z.land r 18446744073709551615) with r
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small;
          unfold INT_MAX in Hr; lia).
    release_frame APC3 ST3 (bv_unsigned sp + -360).
    release_frame FR ST3 (bv_unsigned sp).
    apply evt_done. unfold vfprintf_mf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST3|]. split; [split; [exact SSP1 | exact SSP2]|].
    split.
    { unfold mf_file. eapply rw_cells_C4_head; [exact FH3|].
      apply le4_eq_mod. rewrite lit_mod32.
      rewrite flags_restore_Z by (rewrite sx32_mod32, EFSW, lit_mod32; reflexivity).
      apply sx32_mod32. }
    split; [exact BUF3 | exact Hr]. }
  unfold hideP in WST.
  zs. if_cases Kw; zify_cond Kw.
  { (* wend <> 0: the window is active *)
    destruct WST as [[W0 K0] | [WE [WP WB]]]; [exfalso; lia|].
    eapply CORE; [apply munch_refl | apply wmono_refl | eassumption |].
    eapply mf_file_eq; [exact FH | | | | ].
    - rewrite <- WE. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite <- WP. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite <- WB. symmetry. apply Z_to_bv_bv_unsigned.
    - unfold mf_md. rewrite WE. replace (f + 1304 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  { (* wend = 0: __towrite sets the window *)
    destruct WST as [[W0 K0] | [WE _]]; [| exfalso; lia]. subst k.
    zs. zs. zs.
    apply mf_to_tw in FH.
    eapply evt_cut.
    { eapply towrite_mf; rewrite ?unsigned_lit by lia;
        [ exact FH | unfold hideP in FL8; rewrite EFSW; apply fsw_nowr; exact FL8 | lia | lia | lia
        | unfold hideP in MODE; exact MODE | assumption ]. }
    cbv beta. intros ms' P. rewrite !unsigned_lit in P by lia.
    (nelim P 20%nat; intros x5' x6' x7' c1 c2 c3 c4 c5 c6 c7 x28' x29' x30' x31' m3 -> MUt WMt MIt FHt).
    apply tw_to_mf in FHt.
    aret_pc.
    zs. if_lit.
    eapply CORE; [exact MUt | exact WMt | exact MIt |].
    eapply mf_file_eq; [exact FHt | f_equal; lia | f_equal; lia | reflexivity | unfold mf_md; rewrite W0; reflexivity]. }
Qed.

End Img.
